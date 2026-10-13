import os
import re
import ipaddress
import logging
import json
import base64
import asyncio
import imaplib
import threading
from datetime import datetime, timezone
from email import policy
from email.parser import BytesParser
from email.utils import parseaddr, parsedate_to_datetime
from email.header import decode_header, make_header

import httpx

from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart

from html.parser import HTMLParser
from urllib.parse import urlparse

from google.oauth2.credentials import Credentials
from google.auth.transport.requests import Request
from googleapiclient.discovery import build


logger = logging.getLogger(__name__)

# Reuse one authenticated Zoho IMAP connection between polls.
_ZOHO_MAILBOX = None
_ZOHO_MAILBOX_LOCK = threading.Lock()


# ============================================================
# GMAIL API CONFIG
# ============================================================

GMAIL_TOKEN_JSON = os.environ.get("GMAIL_TOKEN_JSON")
GMAIL_CLIENT_ID = os.environ.get("GMAIL_CLIENT_ID")
GMAIL_CLIENT_SECRET = os.environ.get("GMAIL_CLIENT_SECRET")
GMAIL_REFRESH_TOKEN = os.environ.get("GMAIL_REFRESH_TOKEN")
GMAIL_TOKEN_URI = os.environ.get(
    "GMAIL_TOKEN_URI", "https://oauth2.googleapis.com/token"
)
GMAIL_ACCESS_TOKEN = os.environ.get("GMAIL_ACCESS_TOKEN")

EMAIL_FROM_NAME = os.environ.get(
    "EMAIL_FROM_NAME",
    "Talbros Security Awareness",
)

EMAIL_REPLY_TO = os.environ.get("EMAIL_REPLY_TO")

# Sending + reading replies requires BOTH scopes on the Google OAuth grant.
# Re-authorize the Gmail account with these scopes before deploying.
GMAIL_SCOPES = [
    "https://www.googleapis.com/auth/gmail.send",
    "https://www.googleapis.com/auth/gmail.readonly",
]


# ============================================================
# ZOHO IMAP INCOMING REPLY CONFIG
# ============================================================
# Legacy Zoho IMAP settings are retained for compatibility only.
# New outbound mail and reply scanning use the authenticated Gmail API.

ZOHO_IMAP_HOST = os.environ.get("ZOHO_IMAP_HOST", "imappro.zoho.in")
ZOHO_IMAP_PORT = int(os.environ.get("ZOHO_IMAP_PORT", "993"))
ZOHO_IMAP_EMAIL = os.environ.get("ZOHO_IMAP_EMAIL", "").strip()
ZOHO_IMAP_PASSWORD = os.environ.get("ZOHO_IMAP_PASSWORD", "")
ZOHO_IMAP_FOLDER = os.environ.get("ZOHO_IMAP_FOLDER", "INBOX")

# When Zoho IMAP is configured, force replies to the same Zoho mailbox.
# Replies are tracked in the authenticated Gmail inbox.
INBOUND_REPLY_EMAIL = (
    EMAIL_REPLY_TO
    or "chanchalchaudhary0101@gmail.com"
)


# Keep the MSAL cache in memory for the lifetime of the Render process.
# The initial serialized cache is supplied through Render Environment Variables.


# ============================================================
# EMAIL SAFETY VALIDATION
# ============================================================

_SHORTENERS = (
    "bit.ly",
    "tinyurl.com",
    "t.co",
    "is.gd",
    "cutt.ly",
    "goo.gl",
    "rebrand.ly",
)


_CRED_ASK = (
    "reply with your password",
    "reply with the code",
    "send your password",
    "cvv",
    "send us your password",
    "enter your password below",
    "confirm your card number",
    "your full card number",
    "seed phrase",
    "recovery phrase",
    "verify your card",
    "social security number",
    "confirm your bank details",
)


_HOSTISH = re.compile(
    r"\b(?:https?://)?((?:[a-z0-9-]+\.)+[a-z]{2,})",
    re.I,
)


def _host_ok(host: str) -> bool:
    if not host:
        return False

    if "xn--" in host:
        return False

    try:
        ipaddress.ip_address(host)
        return False
    except ValueError:
        pass

    return not any(
        host == shortener
        or host.endswith("." + shortener)
        for shortener in _SHORTENERS
    )


def _same_site(shown: str, real: str) -> bool:
    return (
        shown == real
        or real.endswith("." + shown)
        or shown.endswith("." + real)
    )


class _EmailScan(HTMLParser):

    def __init__(self):
        super().__init__()

        self.tags = set()
        self.urls = []
        self.anchors = []

        self._href = None
        self._text = []

    def handle_starttag(self, tag, attrs):

        tag_lower = tag.lower()

        self.tags.add(tag_lower)

        for key, value in attrs:

            if (
                key.lower() in ("href", "src")
                and value
            ):
                self.urls.append(value)

        if tag_lower == "a":

            attributes = {
                key.lower(): value
                for key, value in attrs
            }

            self._href = attributes.get("href")
            self._text = []

    def handle_data(self, data):

        if self._href is not None:
            self._text.append(data)

    def handle_endtag(self, tag):

        if (
            tag.lower() == "a"
            and self._href is not None
        ):

            self.anchors.append(
                (
                    self._href,
                    "".join(self._text),
                )
            )

            self._href = None
            self._text = []


def assert_safe_email(
    subject: str,
    html: str,
) -> None:

    scan = _EmailScan()

    scan.feed(html)

    forbidden_tags = {
        "form",
        "input",
        "textarea",
        "select",
    }

    if scan.tags & forbidden_tags:

        raise ValueError(
            "Email templates may not contain forms "
            "or input fields."
        )

    body = f"{subject}\n{html}".lower()

    for phrase in _CRED_ASK:

        if phrase in body:

            raise ValueError(
                "Email may not ask recipients for "
                "passwords or credentials."
            )

    for url in scan.urls:

        low = url.strip().lower()

        if low.startswith(
            (
                "mailto:",
                "tel:",
                "cid:",
                "#",
            )
        ):
            continue

        if not low.startswith(
            (
                "https://",
                "http://localhost:",
                "http://127.0.0.1:",
            )
        ):

            raise ValueError(
                "All email links and images must be "
                "absolute https URLs."
            )

        parsed = urlparse(low)

        host = parsed.hostname or ""

        if (
            not _host_ok(host)
            or parsed.username is not None
            or parsed.password is not None
        ):

            raise ValueError(
                "Shortened, numeric-host or "
                "credential-bearing URLs are not allowed."
            )

    for href, text in scan.anchors:

        real = (
            urlparse(
                href.strip().lower()
            ).hostname
            or ""
        )

        if not real:
            continue

        for match in _HOSTISH.finditer(text):

            shown = match.group(1).lower()

            if not _same_site(
                shown,
                real,
            ):

                raise ValueError(
                    "Link text must not reference a "
                    "different website than the link target."
                )


# ============================================================
# GMAIL SERVICE
# ============================================================

def _get_gmail_service():
    """Create a Gmail API client from JSON or separate Render env vars."""
    try:
        if GMAIL_CLIENT_ID and GMAIL_CLIENT_SECRET and GMAIL_REFRESH_TOKEN:
            credentials = Credentials(
                token=GMAIL_ACCESS_TOKEN,
                refresh_token=GMAIL_REFRESH_TOKEN,
                token_uri=GMAIL_TOKEN_URI,
                client_id=GMAIL_CLIENT_ID,
                client_secret=GMAIL_CLIENT_SECRET,
                scopes=GMAIL_SCOPES,
            )
        elif GMAIL_TOKEN_JSON:
            token_data = json.loads(GMAIL_TOKEN_JSON)
            credentials = Credentials.from_authorized_user_info(
                token_data,
                GMAIL_SCOPES,
            )
        else:
            raise RuntimeError(
                "Set GMAIL_CLIENT_ID, GMAIL_CLIENT_SECRET and GMAIL_REFRESH_TOKEN "
                "in Render Environment Variables (or provide GMAIL_TOKEN_JSON)."
            )
    except json.JSONDecodeError as exc:
        raise RuntimeError("GMAIL_TOKEN_JSON is not valid JSON.") from exc
    except Exception as exc:
        if isinstance(exc, RuntimeError):
            raise
        raise RuntimeError(f"Could not load Gmail credentials: {exc}") from exc

    if credentials.refresh_token and (
        not credentials.token or credentials.expired
    ):
        try:
            credentials.refresh(Request())
            logger.info("Gmail access token refreshed successfully.")
        except Exception as exc:
            logger.exception("Gmail token refresh failed.")
            raise RuntimeError(
                "Gmail token refresh failed. Check the new Client ID, Client Secret, "
                "Refresh Token and Gmail API scopes."
            ) from exc

    if not credentials.valid:
        raise RuntimeError(
            "Gmail credentials are invalid. Re-authorize with gmail.send and "
            "gmail.readonly scopes and update Render variables."
        )

    return build(
        "gmail",
        "v1",
        credentials=credentials,
        cache_discovery=False,
    )


# ============================================================
# GET AUTHENTICATED GMAIL ACCOUNT
# ============================================================

async def get_gmail_account_email() -> str:

    gmail_service = _get_gmail_service()

    profile = (
        gmail_service
        .users()
        .getProfile(userId="me")
        .execute()
    )

    email_address = profile.get("emailAddress")

    if not email_address:

        raise RuntimeError(
            "Could not determine authenticated Gmail account."
        )

    return email_address


# ============================================================
# SEND EMAIL WITH GMAIL API
# ============================================================

async def send_email(
    *,
    to: str,
    subject: str,
    html: str,
    reply_to: str | None = None,
) -> dict:
    """Send one authorized message using the configured Gmail account."""
    assert_safe_email(subject, html)
    final_reply_to = reply_to or EMAIL_REPLY_TO or "chanchalchaudhary0101@gmail.com"

    def _send_sync():
        gmail_service = _get_gmail_service()
        sender = (
            gmail_service.users()
            .getProfile(userId="me")
            .execute()
            .get("emailAddress", "")
        )
        if sender.lower() != "chanchalchaudhary0101@gmail.com":
            raise RuntimeError(
                "The connected Gmail account is not chanchalchaudhary0101@gmail.com. "
                "Authorize the correct Gmail account and update the OAuth credentials."
            )

        message = MIMEMultipart("alternative")
        message["To"] = to
        message["From"] = f"{EMAIL_FROM_NAME} <{sender}>" if EMAIL_FROM_NAME else sender
        message["Subject"] = subject
        if final_reply_to:
            message["Reply-To"] = final_reply_to
        message.attach(MIMEText(_html_to_text(html), "plain", "utf-8"))
        message.attach(MIMEText(html, "html", "utf-8"))
        raw = base64.urlsafe_b64encode(message.as_bytes()).decode("ascii")
        result = (
            gmail_service.users()
            .messages()
            .send(userId="me", body={"raw": raw})
            .execute()
        )
        message_id = result.get("id")
        thread_id = result.get("threadId")
        internet_message_id = None
        if message_id:
            try:
                metadata = (
                    gmail_service.users()
                    .messages()
                    .get(
                        userId="me",
                        id=message_id,
                        format="metadata",
                        metadataHeaders=["Message-ID"],
                    )
                    .execute()
                )
                headers = (metadata.get("payload") or {}).get("headers", [])
                internet_message_id = next(
                    (h.get("value") for h in headers if h.get("name", "").lower() == "message-id"),
                    None,
                )
            except Exception:
                logger.warning("Could not retrieve Gmail Message-ID for sent message %s", message_id)
        return {
            "id": message_id,
            "thread_id": thread_id,
            "internet_message_id": internet_message_id,
        }

    result = await asyncio.to_thread(_send_sync)
    logger.info("Gmail API accepted message to %s (message=%s)", to, result.get("id"))
    return result


class _HTMLTextParser(HTMLParser):
    """Convert HTML email content into readable plain text."""

    def __init__(self):
        super().__init__()
        self.parts = []

    def handle_data(self, data):
        text = data.strip()
        if text:
            self.parts.append(text)


def _html_to_text(value: str) -> str:
    if not value:
        return ""
    parser = _HTMLTextParser()
    parser.feed(value)
    parser.close()
    return "\n".join(parser.parts).strip()


def _graph_headers(access_token: str) -> dict:
    return {
        "Authorization": f"Bearer {access_token}",
        "Accept": "application/json",
    }


def _normalize_email_address(value: str) -> str:
    """Normalize email values coming from Graph/env, including escaped @."""
    value = (value or "").strip().strip("<>").strip()
    # Some Render/env copy-pastes can contain a literal backslash before @.
    value = value.replace("\\@", "@")
    return value.lower()


def _graph_address(item: dict) -> str:
    return (
        ((item or {}).get("emailAddress") or {}).get("address")
        or ""
    ).strip()


class _ReplyScan(list):
    """List-compatible reply scan result used by server.py."""

    def get(self, key, default=None):
        if key == "messages":
            return list(self)
        if key == "history_id":
            return None
        return default


def _zoho_ready() -> bool:
    return bool(ZOHO_IMAP_EMAIL and ZOHO_IMAP_PASSWORD)


def _decode_mime_header(value: str | None) -> str:
    if not value:
        return ""
    try:
        return str(make_header(decode_header(value)))
    except Exception:
        return value


def _iso_date(value: str | None) -> str:
    if not value:
        return ""
    try:
        dt = parsedate_to_datetime(value)
        if dt is None:
            return ""
        return dt.isoformat()
    except Exception:
        return value


def _zoho_open() -> imaplib.IMAP4_SSL:
    """Return a reusable Zoho IMAP connection, reconnecting when needed."""
    global _ZOHO_MAILBOX

    if not _zoho_ready():
        raise RuntimeError(
            "Zoho IMAP is not configured. Set ZOHO_IMAP_EMAIL and "
            "ZOHO_IMAP_PASSWORD in Render Environment Variables."
        )

    with _ZOHO_MAILBOX_LOCK:
        if _ZOHO_MAILBOX is not None:
            try:
                status, _ = _ZOHO_MAILBOX.noop()
                if status == "OK":
                    status, _ = _ZOHO_MAILBOX.select(
                        ZOHO_IMAP_FOLDER, readonly=True
                    )
                    if status == "OK":
                        return _ZOHO_MAILBOX
            except Exception:
                try:
                    _ZOHO_MAILBOX.logout()
                except Exception:
                    pass
                _ZOHO_MAILBOX = None

        mailbox = imaplib.IMAP4_SSL(
            ZOHO_IMAP_HOST,
            ZOHO_IMAP_PORT,
        )
    # Render copy/paste can accidentally leave a literal \@ in the email.
    # Zoho app passwords are shown grouped with spaces; IMAP expects the
    # actual password without those display spaces.
    login_email = _normalize_email_address(ZOHO_IMAP_EMAIL)
    login_password = re.sub(r"\s+", "", ZOHO_IMAP_PASSWORD or "")

    if not login_email or not login_password:
        raise RuntimeError(
            "ZOHO_IMAP_EMAIL or ZOHO_IMAP_PASSWORD is empty after normalization."
        )

    try:
        status, data = mailbox.login(
            login_email,
            login_password,
        )
    except Exception:
        try:
            mailbox.logout()
        except Exception:
            pass
        raise

    if status != "OK":
        try:
            mailbox.logout()
        except Exception:
            pass
        raise RuntimeError(f"Zoho IMAP login failed: {data!r}")

    status, _ = mailbox.select(
        ZOHO_IMAP_FOLDER,
        readonly=True,
    )
    if status != "OK":
        try:
            mailbox.logout()
        except Exception:
            pass
        raise RuntimeError(
            f"Could not select Zoho IMAP folder {ZOHO_IMAP_FOLDER!r}."
        )

    _ZOHO_MAILBOX = mailbox
    return mailbox


def _message_text_and_attachments(msg):
    """Extract readable body text and file attachments from an EmailMessage."""
    plain_parts: list[str] = []
    html_parts: list[str] = []
    attachments: list[dict] = []

    if msg.is_multipart():
        parts = msg.walk()
    else:
        parts = [msg]

    for part in parts:
        if part.is_multipart():
            continue

        filename = part.get_filename()
        disposition = (part.get_content_disposition() or "").lower()
        content_type = (part.get_content_type() or "").lower()

        # Any named attachment is a real file attachment.
        if filename or disposition == "attachment":
            if not filename:
                filename = "attachment"
            try:
                payload = part.get_payload(decode=True) or b""
            except Exception:
                payload = b""
            if payload:
                attachments.append({
                    "filename": _decode_mime_header(filename),
                    "mime_type": content_type or "application/octet-stream",
                    "data": payload,
                    "size": len(payload),
                })
            continue

        # Ignore inline images/binaries for the dashboard attachment count.
        if content_type.startswith("image/") and disposition == "inline":
            continue

        try:
            value = part.get_content()
        except Exception:
            raw = part.get_payload(decode=True) or b""
            charset = part.get_content_charset() or "utf-8"
            try:
                value = raw.decode(charset, errors="replace")
            except Exception:
                value = raw.decode("utf-8", errors="replace")

        if not isinstance(value, str):
            continue

        if content_type == "text/plain":
            plain_parts.append(value)
        elif content_type == "text/html":
            html_parts.append(value)

    if plain_parts:
        body = "\n\n".join(x.strip() for x in plain_parts if x.strip())
    elif html_parts:
        body = _html_to_text("\n\n".join(html_parts))
    else:
        body = ""

    return body, attachments


def _parse_zoho_message(uid_text: str, raw_message: bytes) -> dict:
    msg = BytesParser(policy=policy.default).parsebytes(raw_message)
    sender = parseaddr(msg.get("From", ""))[1].strip().lower()
    to_values = [
        parseaddr(x)[1].strip().lower()
        for x in msg.get_all("To", [])
        if parseaddr(x)[1]
    ]
    body, attachments = _message_text_and_attachments(msg)
    message_id = (msg.get("Message-ID") or "").strip()
    stable_id = f"zoho:{message_id}" if message_id else f"zoho-uid:{uid_text}"
    return {
        "id": stable_id,
        "uid": uid_text,
        "thread_id": None,
        "internet_message_id": message_id or None,
        "in_reply_to": (msg.get("In-Reply-To") or "").strip().lower(),
        "references": (msg.get("References") or "").strip().lower(),
        "from": sender,
        "to": ", ".join(x for x in to_values if x),
        "subject": _decode_mime_header(msg.get("Subject", "")),
        "date": _iso_date(msg.get("Date", "")),
        "body": body,
        "body_type": "text/plain",
        "reply_text": body,
        "has_attachments": bool(attachments),
        "parent_folder_id": ZOHO_IMAP_FOLDER,
        "attachments": attachments,
    }


def _zoho_fetch_uid_sync(mailbox, uid: bytes | str, *, headers_only: bool = False) -> dict:
    """Fetch one Zoho message. Header-only fetch is used during polling.

    Full BODY.PEEK[] is intentionally reserved for a message that the server
    has already matched to a sent simulation recipient. This avoids downloading
    attachments for unrelated inbox notifications and other mailbox noise.
    """
    uid_text = uid.decode() if isinstance(uid, bytes) else str(uid)
    fetch_spec = (
        "(BODY.PEEK[HEADER.FIELDS (FROM TO SUBJECT DATE MESSAGE-ID IN-REPLY-TO REFERENCES)])"
        if headers_only
        else "(BODY.PEEK[])"
    )
    status, data = mailbox.uid("fetch", uid_text, fetch_spec)
    if status != "OK":
        raise RuntimeError(f"Zoho IMAP fetch failed for UID {uid_text}: {data!r}")
    raw_message = None
    for item in data or []:
        if isinstance(item, tuple) and len(item) >= 2:
            raw_message = item[1]
            break
    if not raw_message:
        raise RuntimeError(f"Zoho IMAP returned no message data for UID {uid_text}.")

    msg = BytesParser(policy=policy.default).parsebytes(raw_message)
    sender = parseaddr(msg.get("From", ""))[1].strip().lower()
    to_values = [
        parseaddr(x)[1].strip().lower()
        for x in msg.get_all("To", [])
        if parseaddr(x)[1]
    ]
    message_id = (msg.get("Message-ID") or "").strip()
    stable_id = f"zoho:{message_id}" if message_id else f"zoho-uid:{uid_text}"

    if headers_only:
        return {
            "id": stable_id,
            "uid": uid_text,
            "thread_id": None,
            "internet_message_id": message_id or None,
            "in_reply_to": (msg.get("In-Reply-To") or "").strip().lower(),
            "references": (msg.get("References") or "").strip().lower(),
            "from": sender,
            "to": ", ".join(x for x in to_values if x),
            "subject": _decode_mime_header(msg.get("Subject", "")),
            "date": _iso_date(msg.get("Date", "")),
            "body": "",
            "body_type": "text/plain",
            "reply_text": "",
            "has_attachments": False,
            "parent_folder_id": ZOHO_IMAP_FOLDER,
            "attachments": [],
        }

    return _parse_zoho_message(uid_text, raw_message)


def _zoho_find_incoming_sync(limit: int, after_uid: int | None = None) -> _ReplyScan:
    """Fast incremental Zoho scan: search UIDs, then download headers only."""
    mailbox = _zoho_open()
    try:
        criteria = f"UID {int(after_uid) + 1}:*" if after_uid else "ALL"
        status, data = mailbox.uid("search", None, criteria)
        if status != "OK":
            raise RuntimeError(f"Zoho IMAP search failed: {data!r}")

        raw_uids = (data[0] or b"").split()
        max_scan = max(1, min(int(limit), 100))
        raw_uids = raw_uids[-max_scan:]
        results = _ReplyScan()
        scanned_last_uid = int(after_uid or 0)

        for uid in raw_uids:
            try:
                item = _zoho_fetch_uid_sync(mailbox, uid, headers_only=True)
                results.append(item)
                scanned_last_uid = max(scanned_last_uid, int(item["uid"]))
            except Exception:
                logger.exception(
                    "Could not read Zoho message UID %s",
                    uid.decode(errors="ignore") if isinstance(uid, bytes) else uid,
                )

        results.last_uid = scanned_last_uid
        return results
    finally:
        # Keep the authenticated IMAP connection alive between polls.
        # Closing/logging out here was the main source of the 1-2 second
        # delay because every poll had to reconnect to Zoho. _zoho_open()
        # validates the existing connection and reconnects automatically if
        # Zoho has dropped it.
        pass


async def find_incoming_replies(
    *,
    start_history_id: str | None = None,
    after_message_id: str | None = None,
    max_results: int = 100,
    after_uid: int | None = None,
) -> _ReplyScan:
    """List recent incoming Gmail inbox messages for reply matching."""
    del start_history_id, after_message_id, after_uid
    limit = max(1, min(int(max_results or 100), 100))

    def _scan_sync():
        service = _get_gmail_service()
        response = (
            service.users()
            .messages()
            .list(userId="me", q="in:inbox -from:me", maxResults=limit)
            .execute()
        )
        output = _ReplyScan()
        output.last_uid = 0
        for row in response.get("messages", []):
            message_id = row.get("id")
            if not message_id:
                continue
            msg = (
                service.users()
                .messages()
                .get(userId="me", id=message_id, format="metadata",
                     metadataHeaders=["From", "To", "Subject", "Date",
                                      "Message-ID", "In-Reply-To", "References"])
                .execute()
            )
            payload = msg.get("payload") or {}
            headers = {
                str(h.get("name", "")).lower(): h.get("value", "")
                for h in payload.get("headers", [])
            }
            output.append({
                "id": message_id,
                "thread_id": msg.get("threadId"),
                "from": headers.get("from", ""),
                "to": headers.get("to", ""),
                "subject": headers.get("subject", ""),
                "date": headers.get("date", ""),
                "in_reply_to": headers.get("in-reply-to", ""),
                "references": headers.get("references", ""),
                "internet_message_id": headers.get("message-id", ""),
            })
        return output

    result = await asyncio.to_thread(_scan_sync)
    logger.info("Gmail inbox reply scan found %d message(s).", len(result))
    return result


async def get_message_attachments(message_id: str) -> list[dict]:
    """Download file attachments from a Gmail message."""
    def _get_sync():
        service = _get_gmail_service()
        message = service.users().messages().get(
            userId="me", id=message_id, format="full"
        ).execute()
        results = []

        def walk(part):
            filename = part.get("filename") or ""
            body = part.get("body") or {}
            mime_type = part.get("mimeType") or "application/octet-stream"
            data = body.get("data")
            attachment_id = body.get("attachmentId")
            if filename:
                if data:
                    raw = base64.urlsafe_b64decode(data + "=" * (-len(data) % 4))
                elif attachment_id:
                    item = service.users().messages().attachments().get(
                        userId="me", messageId=message_id, id=attachment_id
                    ).execute()
                    encoded = item.get("data") or ""
                    raw = base64.urlsafe_b64decode(encoded + "=" * (-len(encoded) % 4))
                else:
                    raw = b""
                if raw:
                    results.append({
                        "filename": filename,
                        "mime_type": mime_type,
                        "data": raw,
                        "size": len(raw),
                    })
            for child in part.get("parts", []) or []:
                walk(child)

        walk(message.get("payload") or {})
        return results

    return await asyncio.to_thread(_get_sync)


async def get_incoming_message_details(
    message_id: str,
    zoho_uid: str | int | None = None,
) -> dict:
    """Get one reply's body and attachments from Zoho or Graph.

    When the incremental Zoho scan already knows the UID, use it directly.
    This avoids a second IMAP Message-ID search and makes reply+attachment
    processing noticeably faster.
    """
    if message_id.startswith("zoho:") or message_id.startswith("zoho-uid:"):
        uid_or_message_id = f"zoho-uid:{zoho_uid}" if zoho_uid is not None else message_id
        return await asyncio.to_thread(
            _zoho_get_message_details_sync,
            uid_or_message_id,
        )

    def _get_sync():
        service = _get_gmail_service()
        message = service.users().messages().get(
            userId="me", id=message_id, format="full"
        ).execute()
        payload = message.get("payload") or {}
        headers = {
            str(h.get("name", "")).lower(): h.get("value", "")
            for h in payload.get("headers", [])
        }
        text_parts = []
        html_parts = []

        def walk(part):
            mime_type = (part.get("mimeType") or "").lower()
            body = part.get("body") or {}
            data = body.get("data")
            if data and not part.get("filename"):
                try:
                    decoded = base64.urlsafe_b64decode(
                        data + "=" * (-len(data) % 4)
                    ).decode("utf-8", errors="replace")
                    if mime_type == "text/plain":
                        text_parts.append(decoded)
                    elif mime_type == "text/html":
                        html_parts.append(decoded)
                except Exception:
                    logger.exception("Could not decode Gmail message body.")
            for child in part.get("parts", []) or []:
                walk(child)

        walk(payload)
        body_content = "\\n".join(text_parts) or "\\n".join(html_parts)
        reply_text = _html_to_text(body_content) if html_parts and not text_parts else body_content.strip()
        received_ms = message.get("internalDate")
        received_date = (
            datetime.fromtimestamp(int(received_ms) / 1000, tz=timezone.utc).isoformat()
            if received_ms else headers.get("date", "")
        )
        return {
            "id": message.get("id") or message_id,
            "thread_id": message.get("threadId"),
            "internet_message_id": headers.get("message-id"),
            "from": headers.get("from", ""),
            "to": headers.get("to", ""),
            "subject": headers.get("subject", ""),
            "date": received_date,
            "body": body_content,
            "body_type": "html" if html_parts and not text_parts else "text",
            "reply_text": reply_text,
            "attachments": [],
        }

    details = await asyncio.to_thread(_get_sync)
    details["attachments"] = await get_message_attachments(message_id)
    return details


def _zoho_get_message_details_sync(message_id: str) -> dict:
    mailbox = _zoho_open()
    try:
        uid_text = None

        if message_id.startswith("zoho-uid:"):
            uid_text = message_id.split(":", 1)[1]
        elif message_id.startswith("zoho:"):
            # Resolve Message-ID back to its IMAP UID.
            wanted = message_id.split(":", 1)[1]
            status, data = mailbox.uid(
                "search",
                None,
                'HEADER', 'Message-ID', wanted.strip('<>'),
            )
            if status != "OK" or not data or not data[0]:
                raise RuntimeError(
                    f"Could not find Zoho message {wanted!r} in INBOX."
                )
            uid_text = data[0].split()[-1].decode()

        return _zoho_fetch_uid_sync(mailbox, uid_text)
    finally:
        try:
            mailbox.close()
        except Exception:
            pass
        try:
            mailbox.logout()
        except Exception:
            pass
