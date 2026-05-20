import argparse
import base64
import hashlib
import html
import json
import re
import secrets
import sys
import threading
import time
import webbrowser
from collections import defaultdict
from decimal import Decimal, InvalidOperation
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.error import HTTPError, URLError
from urllib.parse import parse_qs, quote, unquote, urlencode, urlparse
from urllib.request import Request, urlopen

import pdfplumber


PROFILES_PATH = Path(__file__).with_name("profiles.json")
GLOBAL_SETTINGS_PATH = Path(__file__).with_name("globalsettings.json")
PREVIEW_TEMPLATE_PATH = Path(__file__).with_name("preview.html")
LOCAL_CONFIG_PATH = Path(__file__).with_name("localconfig.json")
LOCAL_TOKEN_PATH = Path(__file__).with_name("localtokens.json")
XERO_AUTHORIZE_URL = "https://login.xero.com/identity/connect/authorize"
XERO_TOKEN_URL = "https://identity.xero.com/connect/token"
XERO_CONNECTIONS_URL = "https://api.xero.com/connections"
DEFAULT_XERO_SCOPES = [
    "openid",
    "profile",
    "email",
    "offline_access",
    "accounting.invoices",
    "accounting.settings.read",
]
AMOUNT_RE = re.compile(r"^(?:\u00c2?\u00a3)?[0-9][0-9,]*\.[0-9]+$")
CID_ARTIFACT_RE = re.compile(r"\(cid:\d+\)")
DESCRIPTION_REPLACEMENTS = {
    "\ufb00": "ff",
    "\ufb01": "fi",
    "\ufb02": "fl",
    "\ufb03": "ffi",
    "\ufb04": "ffl",
    "\ufb05": "st",
    "\ufb06": "st",
    "(cid:415)": "ti",
}


def load_json_file(path):
    try:
        with path.open("r", encoding="utf-8") as f:
            return json.load(f)
    except json.JSONDecodeError as exc:
        raise ValueError(
            f"INVALID: {path}\n"
            f"  Line {exc.lineno}, column {exc.colno}: {exc.msg}"
        ) from exc


def load_profiles():
    return load_json_file(PROFILES_PATH)


def load_global_settings():
    return load_json_file(GLOBAL_SETTINGS_PATH)


def load_local_config():
    if not LOCAL_CONFIG_PATH.exists():
        return {}
    return load_json_file(LOCAL_CONFIG_PATH)


def load_local_tokens():
    if not LOCAL_TOKEN_PATH.exists():
        return {}
    return load_json_file(LOCAL_TOKEN_PATH)


def save_local_tokens(tokens):
    with LOCAL_TOKEN_PATH.open("w", encoding="utf-8") as f:
        json.dump(tokens, f, indent=2)
        f.write("\n")


def configured_port(local_config, requested_port):
    if requested_port:
        return requested_port

    redirect_uri = local_config.get("redirectUri")
    if not redirect_uri:
        return 0

    parsed = urlparse(redirect_uri)
    if parsed.hostname in {"127.0.0.1", "localhost"} and parsed.port:
        return parsed.port

    return 0


def configured_host(local_config):
    redirect_uri = local_config.get("redirectUri")
    if not redirect_uri:
        return "127.0.0.1"

    parsed = urlparse(redirect_uri)
    if parsed.hostname in {"127.0.0.1", "localhost"}:
        return parsed.hostname

    return "127.0.0.1"


def extract_pdf_words(pdf_path):
    words = []
    with pdfplumber.open(pdf_path) as pdf:
        for page in pdf.pages:
            words.extend(page.extract_words())
    return sorted(words, key=lambda word: (word["doctop"], word["x0"]))


def word_text(word):
    return word.get("text", "")


def grouped_rows(words):
    rows = defaultdict(list)
    for word in words:
        rows[word["doctop"]].append(word)
    return {
        doctop: sorted(row_words, key=lambda word: word["x0"])
        for doctop, row_words in rows.items()
    }


def row_text(row_words):
    return " ".join(word_text(word) for word in row_words)


def normalize_description(description):
    for source, replacement in DESCRIPTION_REPLACEMENTS.items():
        description = description.replace(source, replacement)
    return description


def description_artifacts(description):
    return CID_ARTIFACT_RE.findall(description)


def find_profile(words, profiles):
    texts = {word_text(word) for word in words}
    for profile in profiles:
        if any(match in texts for match in profile.get("matchStrings", [])):
            return profile
    raise ValueError("No matching profile found.")


def document_text(words):
    return " ".join(word_text(word) for word in words)


def find_property(words, profile):
    properties = profile.get("properties", [])
    if not properties:
        return None

    text = document_text(words)
    for property_info in properties:
        address = property_info.get("address")
        if address and address in text:
            return property_info

    addresses = ", ".join(
        property_info["address"]
        for property_info in properties
        if property_info.get("address")
    )
    raise ValueError(f"No matching property address found. Expected one of: {addresses}")


def find_lower_bound(words, profile):
    required = set(profile["finalRowContains"])
    for _doctop, row_words in grouped_rows(words).items():
        if required.issubset({word_text(word) for word in row_words}):
            return row_words[0]["doctop"]
    raise ValueError(
        "Could not find final row containing: "
        + ", ".join(profile["finalRowContains"])
    )


def parse_amount(text):
    cleaned = (
        text.replace("\u00c2", "")
        .replace("\u00a3", "")
        .replace(",", "")
    )
    try:
        return Decimal(cleaned)
    except InvalidOperation as exc:
        raise ValueError(f"Invalid amount: {text}") from exc


def is_amount_word(word, profile, upper_bound, lower_bound):
    text = word_text(word)
    return (
        AMOUNT_RE.fullmatch(text) is not None
        and word["doctop"] > upper_bound
        and word["doctop"] <= lower_bound
        and word["x0"] > profile["amountAfter"]
        and word["x1"] < profile["amountBefore"]
    )


def find_amounts(words, profile, upper_bound, lower_bound):
    return [
        {
            "raw": word_text(word),
            "amount": parse_amount(word_text(word)),
            "doctop": word["doctop"],
            "x0": word["x0"],
            "x1": word["x1"],
            "word": word,
        }
        for word in words
        if is_amount_word(word, profile, upper_bound, lower_bound)
    ]


def candidate_description_words(words, amount_line, profile):
    return [
        word
        for word in words
        if (
            word["x0"] > profile["descAfter"]
            and word["x1"] < profile["descBefore"]
            and word["doctop"] >= amount_line["doctop"]
        )
    ]


def description_for_amount(words, rows, amount_line, profile):
    selected = []
    last_doctop = None

    for word in candidate_description_words(words, amount_line, profile):
        doctop = word["doctop"]
        if doctop == amount_line["doctop"] or (
            last_doctop is not None
            and doctop < last_doctop + profile["descWrapMax"]
        ):
            selected.append(word)
            last_doctop = doctop
        elif selected:
            break

    if selected:
        return row_text(selected)

    row_words = [
        word
        for word in rows.get(amount_line["doctop"], [])
        if word is not amount_line["word"]
    ]
    fallback = row_text(row_words)
    if fallback in profile.get("descsOutsideRange", []):
        return fallback

    return None


def build_lines(words, profile, upper_bound, lower_bound):
    rows = grouped_rows(words)
    amounts = find_amounts(words, profile, upper_bound, lower_bound)
    lines = []

    for amount_line in amounts:
        description = description_for_amount(words, rows, amount_line, profile)
        if description is None:
            raise ValueError(
                "Could not find description for amount "
                f"{amount_line['raw']} at doctop {amount_line['doctop']}"
            )
        description = normalize_description(description)
        if description in profile.get("descIgnore", []):
            continue

        lines.append(
            {
                "description": description,
                "descriptionArtifacts": description_artifacts(description),
                "amount": amount_line["amount"],
                "doctop": amount_line["doctop"],
                "x0": amount_line["x0"],
                "x1": amount_line["x1"],
            }
        )

    return lines


def sign_multiplier(sign):
    if sign == "negative":
        return Decimal("-1")
    if sign == "positive":
        return Decimal("1")
    raise ValueError(f"Unknown sign: {sign}")


def apply_row_signing(words, lines, profile):
    amount_doctops = {line["doctop"] for line in lines}
    headers = []

    for doctop, row_words in grouped_rows(words).items():
        if doctop in amount_doctops:
            continue
        text = row_text(row_words)
        for header in profile.get("signHeaders", []):
            if text == header["text"]:
                headers.append(
                    {
                        "doctop": doctop,
                        "sign": header["sign"],
                    }
                )

    headers.sort(key=lambda header: header["doctop"])

    for line in lines:
        active_header = None
        for header in headers:
            if header["doctop"] < line["doctop"]:
                active_header = header
            else:
                break

        if active_header is not None:
            line["amount"] *= sign_multiplier(active_header["sign"])


def apply_column_signing(lines, profile):
    for line in lines:
        for column in profile.get("signCols", []):
            if (
                line["x0"] > column["amountAfter"]
                and line["x1"] < column["amountBefore"]
            ):
                line["amount"] *= sign_multiplier(column["sign"])
                break


def apply_signing(words, lines, profile):
    sign_by = profile.get("signBy")
    if sign_by == "rows":
        apply_row_signing(words, lines, profile)
    elif sign_by == "columns":
        apply_column_signing(lines, profile)
    else:
        raise ValueError(f"Unknown signBy value: {sign_by}")


def apply_transaction_types(lines, global_settings):
    desc_type_match = global_settings.get("descTypeMatch", {})

    for line in lines:
        description = line["description"].lower()
        line["type"] = "maintenance"

        for type_name, matches in desc_type_match.items():
            if any(match.lower() in description for match in matches):
                line["type"] = type_name
                break


def print_table(lines):
    desc_width = max(
        [len("Description")]
        + [min(len(line["description"]), 80) for line in lines]
    )
    type_width = max(
        [len("Type")]
        + [len(line.get("type", "")) for line in lines]
    )
    amount_width = max(
        [len("Amount")]
        + [len(format_amount(line["amount"])) for line in lines]
    )

    print(
        f"{'Description':<{desc_width}}  "
        f"{'Type':<{type_width}}  "
        f"{'Amount':>{amount_width}}"
    )
    print(f"{'-' * desc_width}  {'-' * type_width}  {'-' * amount_width}")
    for line in lines:
        description = line["description"]
        if len(description) > 80:
            description = description[:77] + "..."
        print(
            f"{description:<{desc_width}}  "
            f"{line.get('type', ''):<{type_width}}  "
            f"{format_amount(line['amount']):>{amount_width}}"
        )

    total = sum((line["amount"] for line in lines), Decimal("0"))
    print(f"{'-' * desc_width}  {'-' * type_width}  {'-' * amount_width}")
    print(
        f"{'TOTAL':<{desc_width}}  "
        f"{'':<{type_width}}  "
        f"{format_amount(total):>{amount_width}}"
    )

    artifacts = sorted(
        {
            artifact
            for line in lines
            for artifact in line.get("descriptionArtifacts", [])
        }
    )
    if artifacts:
        print()
        print(
            "WARNING: uncorrected description artifacts found: "
            + ", ".join(artifacts)
        )


def format_amount(amount):
    return f"{amount:.2f}"


def extract_document(pdf_path, profiles, global_settings):
    words = extract_pdf_words(pdf_path)
    profile = find_profile(words, profiles)
    property_info = find_property(words, profile)
    upper_bound = profile["ignoreBefore"]
    lower_bound = find_lower_bound(words, profile)
    lines = build_lines(words, profile, upper_bound, lower_bound)
    apply_signing(words, lines, profile)
    apply_transaction_types(lines, global_settings)

    return {
        "path": str(pdf_path.resolve()),
        "fileName": pdf_path.name,
        "profileName": profile["profileName"],
        "property": property_info or {},
        "accountTypes": list(profile.get("accountCodes", {}).keys()),
        "lines": lines,
        "total": sum((line["amount"] for line in lines), Decimal("0")),
    }


def print_document(document):
    print("=" * 80)
    print(f"FILE: {document['path']}")
    print("=" * 80)

    print(f"Profile: {document['profileName']}")
    if document["property"].get("address"):
        print(f"Property: {document['property']['address']}")
    print(f"Rows: {len(document['lines'])}")
    print()
    print_table(document["lines"])
    print()


def preview_json(documents):
    payload = {
        "documents": [
            {
                "fileName": document["fileName"],
                "profileName": document["profileName"],
                "property": document["property"],
                "accountTypes": document["accountTypes"],
                "total": format_amount(document["total"]),
                "lines": [
                    {
                        "description": line["description"],
                        "type": line["type"],
                        "amount": format_amount(line["amount"]),
                    }
                    for line in document["lines"]
                ],
            }
            for document in documents
        ]
    }
    return json.dumps(payload).encode("utf-8")


def public_xero_status(local_config):
    if not local_config.get("clientId") or not local_config.get("redirectUri"):
        return {
            "configured": False,
            "connected": False,
            "message": "Xero config missing",
        }

    tokens = load_local_tokens()
    connections = tokens.get("connections", [])
    selected_tenant_id = tokens.get("selectedTenantId")
    identity_connected = bool(tokens.get("refresh_token"))
    selected = None
    for connection in connections:
        if connection.get("tenantId") == selected_tenant_id:
            selected = connection
            break

    return {
        "configured": True,
        "identityConnected": identity_connected,
        "connected": bool(identity_connected and selected_tenant_id),
        "tenantCount": len(connections),
        "tenantId": selected_tenant_id,
        "tenantName": selected.get("tenantName") if selected else "",
        "scopes": tokens.get("scope", ""),
        "message": "Connected" if selected_tenant_id else (
            "Xero identity connected, no organisation access"
            if identity_connected
            else "Not connected"
        ),
    }


def pkce_verifier():
    return secrets.token_urlsafe(64)


def pkce_challenge(verifier):
    digest = hashlib.sha256(verifier.encode("ascii")).digest()
    return base64.urlsafe_b64encode(digest).decode("ascii").rstrip("=")


def xero_scopes(local_config):
    return local_config.get("scopes") or DEFAULT_XERO_SCOPES


def xero_authorize_url(local_config, auth_state):
    client_id = local_config.get("clientId")
    redirect_uri = local_config.get("redirectUri")
    if not client_id or not redirect_uri:
        raise ValueError("localconfig.json must include clientId and redirectUri.")

    state = secrets.token_urlsafe(32)
    verifier = pkce_verifier()
    auth_state.clear()
    auth_state.update(
        {
            "state": state,
            "verifier": verifier,
            "createdAt": time.time(),
        }
    )

    query = urlencode(
        {
            "client_id": client_id,
            "response_type": "code",
            "scope": " ".join(xero_scopes(local_config)),
            "redirect_uri": redirect_uri,
            "state": state,
            "code_challenge": pkce_challenge(verifier),
            "code_challenge_method": "S256",
        },
        quote_via=quote,
    )
    return f"{XERO_AUTHORIZE_URL}?{query}"


def xero_authorize_parts(local_config, auth_state):
    url = xero_authorize_url(local_config, auth_state)
    parsed = urlparse(url)
    return {
        "url": url,
        "baseUrl": f"{parsed.scheme}://{parsed.netloc}{parsed.path}",
        "params": {
            key: values[0]
            for key, values in parse_qs(parsed.query).items()
            if key != "client_id"
        },
        "clientIdTail": (local_config.get("clientId") or "")[-6:],
    }


def xero_debug_info(local_config, server_port):
    redirect_uri = local_config.get("redirectUri", "")
    parsed = urlparse(redirect_uri)
    configured_scopes = xero_scopes(local_config)
    return {
        "hasClientId": bool(local_config.get("clientId")),
        "clientIdTail": (local_config.get("clientId") or "")[-6:],
        "redirectUri": redirect_uri,
        "redirectHost": parsed.hostname or "",
        "redirectPort": parsed.port,
        "redirectPath": parsed.path,
        "serverPort": server_port,
        "redirectMatchesServer": parsed.port == server_port,
        "scopes": configured_scopes,
        "authorizeEndpoint": XERO_AUTHORIZE_URL,
        "checks": [
            "The redirect URI must be registered exactly in the Xero developer app.",
            "127.0.0.1 and localhost are different redirect URIs.",
            "The port and /xero/callback path must match exactly.",
            "For a desktop/local app, the Xero app should support PKCE and must not require a client secret.",
            "Apps created after 2 March 2026 should use granular scopes such as accounting.invoices, not accounting.transactions.",
            "Xero examples commonly include openid, profile and email alongside accounting scopes.",
        ],
    }


def read_http_error(exc):
    try:
        return exc.read().decode("utf-8", errors="replace")
    except Exception:
        return str(exc)


def xero_post_token(form):
    body = urlencode(form).encode("utf-8")
    request = Request(
        XERO_TOKEN_URL,
        data=body,
        headers={
            "Accept": "application/json",
            "Content-Type": "application/x-www-form-urlencoded",
        },
        method="POST",
    )

    try:
        with urlopen(request, timeout=30) as response:
            return json.loads(response.read().decode("utf-8"))
    except HTTPError as exc:
        raise ValueError(f"Xero token request failed: {read_http_error(exc)}") from exc
    except URLError as exc:
        raise ValueError(f"Xero token request failed: {exc.reason}") from exc


def xero_get_connections(access_token):
    request = Request(
        XERO_CONNECTIONS_URL,
        headers={
            "Accept": "application/json",
            "Authorization": f"Bearer {access_token}",
        },
    )

    try:
        with urlopen(request, timeout=30) as response:
            return json.loads(response.read().decode("utf-8"))
    except HTTPError as exc:
        raise ValueError(f"Xero connections request failed: {read_http_error(exc)}") from exc
    except URLError as exc:
        raise ValueError(f"Xero connections request failed: {exc.reason}") from exc


def exchange_xero_code(code, local_config, auth_state):
    verifier = auth_state.get("verifier")
    if not verifier:
        raise ValueError("No active Xero auth request found. Start the connection again.")

    token_set = xero_post_token(
        {
            "grant_type": "authorization_code",
            "code": code,
            "redirect_uri": local_config["redirectUri"],
            "client_id": local_config["clientId"],
            "code_verifier": verifier,
        }
    )
    connections = xero_get_connections(token_set["access_token"])
    selected_tenant_id = connections[0]["tenantId"] if len(connections) == 1 else ""

    save_local_tokens(
        {
            **token_set,
            "obtainedAt": int(time.time()),
            "connections": connections,
            "selectedTenantId": selected_tenant_id,
        }
    )

    return connections


def make_preview_handler(documents, local_config, server_port):
    pdf_paths = [Path(document["path"]) for document in documents]
    data = preview_json(documents)
    auth_state = {}

    class PreviewHandler(BaseHTTPRequestHandler):
        def do_GET(self):
            path = unquote(self.path.split("?", 1)[0])

            if path in ("/", "/index.html"):
                self.send_file(PREVIEW_TEMPLATE_PATH, "text/html; charset=utf-8")
                return

            if path == "/data.json":
                self.send_response(200)
                self.send_header("Content-Type", "application/json; charset=utf-8")
                self.send_header("Content-Length", str(len(data)))
                self.end_headers()
                self.wfile.write(data)
                return

            if path == "/xero/status":
                self.send_json(public_xero_status(local_config))
                return

            if path == "/xero/debug":
                self.send_json(xero_debug_info(local_config, server_port))
                return

            if path == "/xero/connect":
                self.redirect_to_xero(local_config, auth_state)
                return

            if path == "/xero/inspect-auth":
                self.inspect_xero_auth(local_config, auth_state)
                return

            if path == "/xero/callback":
                self.handle_xero_callback(local_config, auth_state)
                return

            if path.startswith("/pdf/"):
                self.send_pdf(path, pdf_paths)
                return

            self.send_error(404)

        def send_file(self, path, content_type):
            try:
                body = path.read_bytes()
            except OSError:
                self.send_error(404)
                return

            self.send_response(200)
            self.send_header("Content-Type", content_type)
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)

        def send_json(self, payload):
            body = json.dumps(payload).encode("utf-8")
            self.send_response(200)
            self.send_header("Content-Type", "application/json; charset=utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)

        def send_html_message(self, title, message):
            body = (
                "<!doctype html><html><head><meta charset=\"utf-8\">"
                f"<title>{html.escape(title)}</title></head><body>"
                f"<h1>{html.escape(title)}</h1><p>{html.escape(message)}</p>"
                "</body></html>"
            ).encode("utf-8")
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)

        def redirect_to_xero(self, config, state):
            try:
                url = xero_authorize_url(config, state)
            except ValueError as exc:
                self.send_error(400, str(exc))
                return

            self.send_response(302)
            self.send_header("Location", url)
            self.end_headers()

        def inspect_xero_auth(self, config, state):
            try:
                parts = xero_authorize_parts(config, state)
            except ValueError as exc:
                self.send_error(400, str(exc))
                return

            rows = "\n".join(
                "<tr>"
                f"<th>{html.escape(key)}</th>"
                f"<td>{html.escape(value)}</td>"
                "</tr>"
                for key, value in parts["params"].items()
            )
            body = (
                "<!doctype html><html><head><meta charset=\"utf-8\">"
                "<title>Xero auth inspector</title>"
                "<style>body{font-family:Arial,sans-serif;margin:24px;}"
                "table{border-collapse:collapse;}th,td{border:1px solid #ccc;"
                "padding:6px 8px;text-align:left;}code{word-break:break-all;}"
                "a{display:inline-block;margin:12px 0;}</style></head><body>"
                "<h1>Xero auth inspector</h1>"
                f"<p>Client ID tail: {html.escape(parts['clientIdTail'])}</p>"
                f"<p>Base URL: <code>{html.escape(parts['baseUrl'])}</code></p>"
                f"<table>{rows}</table>"
                f"<p><a href=\"{html.escape(parts['url'])}\">Open this Xero auth URL</a></p>"
                "</body></html>"
            ).encode("utf-8")

            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)

        def handle_xero_callback(self, config, state):
            query = parse_qs(urlparse(self.path).query)
            if query.get("error"):
                self.send_html_message("Xero connection failed", query["error"][0])
                return

            returned_state = query.get("state", [""])[0]
            if returned_state != state.get("state"):
                self.send_error(400, "Xero auth state did not match.")
                return

            code = query.get("code", [""])[0]
            if not code:
                self.send_error(400, "Xero callback did not include a code.")
                return

            try:
                connections = exchange_xero_code(code, config, state)
            except ValueError as exc:
                self.send_html_message("Xero connection failed", str(exc))
                return

            if len(connections) == 1:
                message = (
                    "Connected to "
                    f"{connections[0].get('tenantName', 'the selected organisation')}. "
                    "You can close this tab and return to ParseProp."
                )
            elif len(connections) == 0:
                message = (
                    "Xero identity connected, but no organisations were returned. "
                    "If you used OpenID-only scopes for testing, add an accounting "
                    "scope such as accounting.invoices and reconnect."
                )
            else:
                message = (
                    f"Connected to {len(connections)} organisations. "
                    "Tenant selection will be added before posting to Xero."
                )
            self.send_html_message("Xero connected", message)

        def send_pdf(self, request_path, paths):
            try:
                index = int(request_path.removeprefix("/pdf/"))
                pdf_path = paths[index]
            except (ValueError, IndexError):
                self.send_error(404)
                return

            try:
                body = pdf_path.read_bytes()
            except OSError:
                self.send_error(404)
                return

            self.send_response(200)
            self.send_header("Content-Type", "application/pdf")
            self.send_header("Content-Disposition", f'inline; filename="{pdf_path.name}"')
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)

        def log_message(self, _format, *_args):
            return

    return PreviewHandler


def start_preview_server(documents, host, port, open_browser, local_config):
    class DeferredPortServer(ThreadingHTTPServer):
        pass

    server = DeferredPortServer((host, port), BaseHTTPRequestHandler)
    server_port = server.server_port
    server.RequestHandlerClass = make_preview_handler(
        documents,
        local_config,
        server_port,
    )
    url = f"http://{host}:{server.server_port}/"
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()

    print(f"Preview: {url}")
    if open_browser:
        webbrowser.open(url)
    print("Press Ctrl+C to stop the preview server.")

    try:
        thread.join()
    except KeyboardInterrupt:
        print()
        print("Stopping preview server.")
        server.shutdown()
        server.server_close()


def parse_args():
    parser = argparse.ArgumentParser(
        description="Extract landlord statement transactions from PDFs."
    )
    parser.add_argument(
        "--no-preview",
        action="store_true",
        help="Print console output only; do not start the local preview page.",
    )
    parser.add_argument(
        "--no-browser",
        action="store_true",
        help="Start the local preview server without opening a browser window.",
    )
    parser.add_argument(
        "--port",
        type=int,
        default=0,
        help="Preview server port. Defaults to an available random port.",
    )
    parser.add_argument("input_files", nargs="*")
    return parser.parse_args()


def main():
    args = parse_args()
    input_files = args.input_files

    if not input_files:
        print("No files supplied.")
        return 1

    try:
        profiles = load_profiles()
        global_settings = load_global_settings()
        local_config = load_local_config()
    except Exception as exc:
        print(f"ERROR loading settings: {exc}")
        return 1

    args.port = configured_port(local_config, args.port)

    exit_code = 0
    documents = []
    for file_arg in input_files:
        path = Path(file_arg)

        if not path.exists():
            print(f"File not found: {path}")
            exit_code = 1
            continue

        if path.suffix.lower() != ".pdf":
            print(f"Skipping non-PDF file: {path}")
            continue

        try:
            document = extract_document(path, profiles, global_settings)
            documents.append(document)
            print_document(document)
        except Exception as exc:
            print(f"ERROR processing {path}")
            print(exc)
            print()
            exit_code = 1

    if documents and not args.no_preview:
        start_preview_server(
            documents,
            configured_host(local_config),
            args.port,
            not args.no_browser,
            local_config,
        )

    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
