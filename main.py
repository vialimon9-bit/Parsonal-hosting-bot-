# Single-file build assembled from the supplied bot modules.

import asyncio
import html
import io
import json
import logging
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import uuid
import zipfile
from datetime import datetime, timedelta, timezone
from decimal import Decimal, InvalidOperation
from typing import Any, Awaitable, Callable

import psutil

from aiogram import BaseMiddleware, Bot, Dispatcher, F, Router
from aiogram.filters import CommandStart, StateFilter
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from aiogram.fsm.storage.memory import MemoryStorage
from aiogram.types import (
    BufferedInputFile,
    CallbackQuery,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    KeyboardButton,
    Message,
    ReplyKeyboardMarkup,
    TelegramObject,
)

# ── Shared UI styling (ported from main.py; behavior is unchanged) ───────────
#
# main.py uses Mathematical Bold labels and Telegram's button style field.
# Keep that presentation layer local to this file so none of the existing
# handlers, callback data, FSM states, or business logic need to change.
_UI_GLYPH_FALLBACKS = {
    "⏰": "⏱", "⏱": "⏱", "⏸": "❙❙", "⏹": "■", "▶": "▶",
    "♻": "↻", "⚙": "⚙", "⚠": "⚠", "⚡": "⚡", "✏": "•",
    "✅": "✓", "❌": "✘", "➕": "⊕", "➖": "⊖",
    "➡": "→", "⬅": "↲", "⬆": "▴",
    "🌿": "▸", "🎁": "✦", "🎟": "✿", "🎭": "★", "🎯": "→",
    "🏆": "★", "🏷": "▪", "👁": "◉", "👋": "▫", "👑": "♔",
    "👤": "◈", "👥": "◎", "💎": "◆", "💥": "⚠", "💰": "◆",
    "💱": "◆", "💲": "◆", "💳": "◆", "💸": "◆", "💾": "▾",
    "📁": "▸", "📂": "▸", "📄": "•", "📈": "▲", "📉": "▪",
    "📊": "▪", "📋": "•", "📜": "•", "📝": "•", "📡": "⚑",
    "📢": "⚑", "📣": "⚑", "📤": "▴", "📥": "▾", "📦": "▸",
    "📨": "▫", "📭": "▫", "🔄": "↻", "🔍": "◉", "🔐": "▣",
    "🔑": "❖", "🔒": "▣", "🔔": "⏱", "🔗": "→", "🔤": "•",
    "🔧": "⚙", "🔨": "⚙", "🔴": "✘", "🖥": "⚙", "🖼": "▸",
    "🗂": "▸", "🗄": "▸", "🗑": "✖", "😀": "✦", "🚫": "✘",
    "🛑": "■", "🛡": "◇", "🤖": "▸", "🥧": "▪", "🧪": "◈",
    "🧱": "■", "🧹": "✖", "🧾": "•",
}

_SC_MAP = str.maketrans(
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789",
    "𝐀𝐁𝐂𝐃𝐄𝐅𝐆𝐇𝐈𝐉𝐊𝐋𝐌𝐍𝐎𝐏𝐐𝐑𝐒𝐓𝐔𝐕𝐖𝐗𝐘𝐙"
    "𝐚𝐛𝐜𝐝𝐞𝐟𝐠𝐡𝐢𝐣𝐤𝐥𝐦𝐧𝐨𝐩𝐪𝐫𝐬𝐭𝐮𝐯𝐰𝐱𝐲𝐳"
    "𝟎𝟏𝟐𝟑𝟒𝟓𝟔𝟕𝟖𝟗",
)


def _sc(text: Any) -> str:
    """Render ordinary Latin letters/digits in main.py's bold style."""
    return str(text).translate(_SC_MAP)


def _glyphize_label(value: Any) -> str:
    text = str(value)
    for emoji, glyph in _UI_GLYPH_FALLBACKS.items():
        text = text.replace(f"{emoji}\ufe0f", glyph).replace(emoji, glyph)
    return text


def _button_style(text: Any, callback_data: Any = "") -> str:
    """Choose the same semantic color vocabulary used by main.py.

    Existing button behavior is determined by text/callback_data, so this only
    affects presentation. Explicit style= values still take precedence.
    """
    value = f"{text} {callback_data}".lower()
    if any(word in value for word in (
        "delete", "remove", "cancel", "back", "block", "ban", "revoke",
        "stop", "restart", "danger", "logout",
    )):
        return "danger"
    if any(word in value for word in (
        "upload", "done", "verify", "grant", "add", "download", "join",
        "unblock", "support", "success",
    )):
        return "success"
    return "primary"


_REPLY_BUTTON_ALIASES: dict[str, str] = {}


class _StyledInlineKeyboardButton(InlineKeyboardButton):
    """aiogram button that serializes Telegram's optional style field."""

    style: str = "primary"

    def __init__(self, *args, style: str = "", **kwargs):
        text = args[0] if args and isinstance(args[0], str) else kwargs.get("text", "")
        callback_data = kwargs.get("callback_data", "")
        styled_text = _sc(_glyphize_label(text))
        if args and isinstance(args[0], str):
            args = (styled_text,) + args[1:]
        elif "text" in kwargs:
            kwargs["text"] = styled_text
        super().__init__(*args, **kwargs)
        self.style = style or _button_style(text, callback_data)


class _StyledKeyboardButton(KeyboardButton):
    """aiogram reply-keyboard button with the same visual treatment."""

    style: str = "primary"

    def __init__(self, *args, style: str = "", **kwargs):
        text = args[0] if args and isinstance(args[0], str) else kwargs.get("text", "")
        canonical_text = str(text)
        # Keep the actual Telegram reply-keyboard text identical to the
        # handler text. Older keyboards may still contain the previously
        # rendered label, so retain an alias for those messages too.
        legacy_text = _sc(_glyphize_label(text))
        _REPLY_BUTTON_ALIASES[legacy_text] = canonical_text
        _REPLY_BUTTON_ALIASES[canonical_text] = canonical_text
        if args and isinstance(args[0], str):
            args = (canonical_text,) + args[1:]
        elif "text" in kwargs:
            kwargs["text"] = canonical_text
        super().__init__(*args, **kwargs)
        self.style = style or _button_style(text)


# All existing keyboard builders below keep their original names and callback
# data; only the concrete button class is swapped for the styled equivalent.
InlineKeyboardButton = _StyledInlineKeyboardButton
KeyboardButton = _StyledKeyboardButton


_QUOTE_OPEN = "<blockquote><b>"
_QUOTE_CLOSE = "</b></blockquote>"


def _style_html_text_nodes(text: Any) -> Any:
    """Apply Mathematical Bold outside HTML tags without changing markup."""
    if text is None:
        return text
    value = str(text)
    if not value:
        return value
    output = []
    index = 0
    while index < len(value):
        if value[index] == "<":
            end = value.find(">", index)
            if end == -1:
                output.append(value[index:])
                break
            output.append(value[index:end + 1])
            index = end + 1
        else:
            end = value.find("<", index)
            if end == -1:
                end = len(value)
            output.append(_sc(value[index:end]))
            index = end
    return "".join(output)


def _style_html_message(text: Any) -> Any:
    if text is None:
        return text
    value = str(text)
    if not value.strip():
        return value
    if value.startswith(_QUOTE_OPEN) and value.endswith(_QUOTE_CLOSE):
        return value
    return f"{_QUOTE_OPEN}{_style_html_text_nodes(value)}{_QUOTE_CLOSE}"


class _StyledBot(Bot):
    """Apply main.py's outgoing HTML presentation without changing handlers."""

    @staticmethod
    def _styled_text_kwargs(kwargs: dict) -> dict:
        parse_mode = kwargs.get("parse_mode")
        if parse_mode is None or str(parse_mode).strip().lower() == "html":
            kwargs["parse_mode"] = "HTML"
            if kwargs.get("text") is not None:
                kwargs["text"] = _style_html_message(kwargs["text"])
            if kwargs.get("caption") is not None:
                kwargs["caption"] = _style_html_message(kwargs["caption"])
        return kwargs

    async def send_message(self, chat_id, text, *args, **kwargs):
        kwargs = self._styled_text_kwargs(kwargs)
        return await super().send_message(chat_id, _style_html_message(text), *args, **kwargs)

    async def edit_message_text(self, text, *args, **kwargs):
        kwargs = self._styled_text_kwargs(kwargs)
        return await super().edit_message_text(_style_html_message(text), *args, **kwargs)

    async def send_document(self, chat_id, document, *args, **kwargs):
        kwargs = self._styled_text_kwargs(kwargs)
        return await super().send_document(chat_id, document, *args, **kwargs)

    async def send_photo(self, chat_id, photo, *args, **kwargs):
        kwargs = self._styled_text_kwargs(kwargs)
        return await super().send_photo(chat_id, photo, *args, **kwargs)

    async def send_video(self, chat_id, video, *args, **kwargs):
        kwargs = self._styled_text_kwargs(kwargs)
        return await super().send_video(chat_id, video, *args, **kwargs)

    async def send_animation(self, chat_id, animation, *args, **kwargs):
        kwargs = self._styled_text_kwargs(kwargs)
        return await super().send_animation(chat_id, animation, *args, **kwargs)

    async def edit_message_caption(self, *args, **kwargs):
        kwargs = self._styled_text_kwargs(kwargs)
        return await super().edit_message_caption(*args, **kwargs)


# ── Windows cp1252 fix ────────────────────────────────────────────────────────
# On Windows RDP, sys.stdout and sys.stderr default to the system code page
# (usually cp1252). Any emoji or non-ASCII character in a log message will
# raise UnicodeEncodeError and crash the bot immediately.
# Reconfigure both streams to UTF-8 before anything else runs.
if sys.stdout.encoding and sys.stdout.encoding.lower() != "utf-8":
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
if sys.stderr.encoding and sys.stderr.encoding.lower() != "utf-8":
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")
# ─────────────────────────────────────────────────────────────────────────────

# ── config.py ────────────────────────────────────────────────────────────────
ADMIN_ID         = 6013092363
BASE_DIR         = os.path.dirname(os.path.abspath(__file__))
BOT_TOKEN_FILE   = os.path.join(BASE_DIR, "botToken.txt")
BOTS_BASE_DIR    = os.path.join(BASE_DIR, "bots")
PYTHON_PATH      = sys.executable
os.makedirs(BOTS_BASE_DIR, exist_ok=True)


def _load_master_bot_token() -> str:
    """Load the master bot token from the local token file."""
    try:
        with open(BOT_TOKEN_FILE, "r", encoding="utf-8") as token_file:
            for line in token_file:
                value = line.strip()
                if value and not value.startswith("#"):
                    return value
    except OSError:
        pass
    return ""


MASTER_BOT_TOKEN = _load_master_bot_token()

# ── user_db.py ────────────────────────────────────────────────────────────────

# users.json lives alongside this script so the path is stable regardless
# of which working directory the process is launched from.
DB_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "users.json")
BOT_LIMIT_SETTINGS_PATH = os.path.join(
    os.path.dirname(os.path.abspath(__file__)),
    "bot_limit_settings.json",
)
DEPLOYMENT_SETTINGS_PATH = os.path.join(
    os.path.dirname(os.path.abspath(__file__)),
    "deployment_settings.json",
)
DEPLOYMENT_ACCESS_PATH = os.path.join(
    os.path.dirname(os.path.abspath(__file__)),
    "deployment_access.json",
)
REQUIRED_CHANNELS_PATH = os.path.join(
    os.path.dirname(os.path.abspath(__file__)),
    "required_channels.json",
)
ADMIN_IDS_PATH = os.path.join(
    os.path.dirname(os.path.abspath(__file__)),
    "admins.json",
)
WALLETS_PATH = os.path.join(
    os.path.dirname(os.path.abspath(__file__)),
    "wallets.json",
)
DEPOSITS_PATH = os.path.join(
    os.path.dirname(os.path.abspath(__file__)),
    "deposits.json",
)


def load_users() -> dict:
    """Return the full user dict from disk; empty dict on any error."""
    if not os.path.exists(DB_PATH):
        return {}
    try:
        with open(DB_PATH, "r", encoding="utf-8") as f:
            return json.load(f)
    except (json.JSONDecodeError, OSError):
        return {}


def save_users(users: dict) -> None:
    """Atomically persist the user dict to disk."""
    _atomic_json_save(DB_PATH, users)


def _atomic_json_save(path: str, value: Any) -> None:
    """Write JSON through a sibling temporary file so a stop cannot corrupt it."""
    directory = os.path.dirname(path) or "."
    os.makedirs(directory, exist_ok=True)
    temporary_path = f"{path}.{os.getpid()}.tmp"
    try:
        with open(temporary_path, "w", encoding="utf-8") as f:
            json.dump(value, f, ensure_ascii=False, indent=2)
            f.flush()
            os.fsync(f.fileno())
        os.replace(temporary_path, path)
    finally:
        try:
            if os.path.exists(temporary_path):
                os.remove(temporary_path)
        except OSError:
            pass


def _load_json_object(path: str, default: Any) -> Any:
    try:
        with open(path, "r", encoding="utf-8") as f:
            value = json.load(f)
        return value
    except (FileNotFoundError, json.JSONDecodeError, OSError, TypeError):
        return default


def _utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def load_wallets() -> dict[str, dict]:
    value = _load_json_object(WALLETS_PATH, {})
    return value if isinstance(value, dict) else {}


def save_wallets(wallets: dict[str, dict]) -> None:
    _atomic_json_save(WALLETS_PATH, wallets)


def load_deposits() -> dict[str, dict]:
    value = _load_json_object(DEPOSITS_PATH, {})
    return value if isinstance(value, dict) else {}


def save_deposits(deposits: dict[str, dict]) -> None:
    _atomic_json_save(DEPOSITS_PATH, deposits)


def _new_record_id(prefix: str) -> str:
    return f"{prefix}_{uuid.uuid4().hex[:12]}"


def _normalized_unique_value(value: Any) -> str:
    return " ".join(str(value or "").strip().casefold().split())


def get_active_wallets() -> list[dict]:
    return [
        wallet for wallet in load_wallets().values()
        if isinstance(wallet, dict) and wallet.get("active", False)
    ]


def get_pending_deposits() -> list[dict]:
    return sorted(
        [
            deposit for deposit in load_deposits().values()
            if isinstance(deposit, dict) and deposit.get("status") == "Pending"
        ],
        key=lambda item: item.get("created_at", ""),
        reverse=True,
    )


def load_admin_ids() -> set[int]:
    """Return persisted admin IDs, always including the master ADMIN_ID."""
    admin_ids = {ADMIN_ID}
    if not os.path.exists(ADMIN_IDS_PATH):
        return admin_ids
    try:
        with open(ADMIN_IDS_PATH, "r", encoding="utf-8") as f:
            saved_ids = json.load(f)
        if isinstance(saved_ids, list):
            admin_ids.update(
                int(user_id)
                for user_id in saved_ids
                if isinstance(user_id, int) or (
                    isinstance(user_id, str) and user_id.isdigit()
                )
            )
    except (json.JSONDecodeError, OSError, TypeError, ValueError):
        pass
    return admin_ids


def save_admin_ids(admin_ids: set[int]) -> None:
    """Persist admin IDs without ever removing the master admin."""
    with open(ADMIN_IDS_PATH, "w", encoding="utf-8") as f:
        json.dump(sorted({ADMIN_ID, *admin_ids}), f, ensure_ascii=False, indent=2)


def is_deployment_enabled() -> bool:
    """Return the global deployment switch; enabled by default."""
    if not os.path.exists(DEPLOYMENT_SETTINGS_PATH):
        return True
    try:
        with open(DEPLOYMENT_SETTINGS_PATH, "r", encoding="utf-8") as f:
            settings = json.load(f)
        return settings.get("deployment_enabled", True) is True
    except (json.JSONDecodeError, OSError, AttributeError):
        return True


def set_deployment_enabled(enabled: bool) -> None:
    """Persist the global deployment switch."""
    with open(DEPLOYMENT_SETTINGS_PATH, "w", encoding="utf-8") as f:
        json.dump({"deployment_enabled": enabled}, f, ensure_ascii=False, indent=2)


def load_deployment_access() -> dict[str, Any]:
    """Return users allowed to deploy while global deployment is disabled."""
    if not os.path.exists(DEPLOYMENT_ACCESS_PATH):
        return {}
    try:
        with open(DEPLOYMENT_ACCESS_PATH, "r", encoding="utf-8") as f:
            data = json.load(f)
        if not isinstance(data, dict):
            return {}
        return {
            str(user_id): record
            for user_id, record in data.items()
            if str(user_id).isdigit() and isinstance(record, (str, dict))
        }
    except (json.JSONDecodeError, OSError, TypeError):
        return {}


def save_deployment_access(access: dict[str, Any]) -> None:
    """Persist deployment exceptions atomically enough for this single-process bot."""
    with open(DEPLOYMENT_ACCESS_PATH, "w", encoding="utf-8") as f:
        json.dump(access, f, ensure_ascii=False, indent=2)


def grant_deployment_access(user_id: int, expires_at: str) -> bool:
    """Grant deployment access; return False if it already exists."""
    access = load_deployment_access()
    uid = str(user_id)
    if uid in access and has_deployment_access(user_id):
        return False
    access[uid] = {
        "granted_at": datetime.now().astimezone().isoformat(),
        "expires_at": expires_at,
    }
    save_deployment_access(access)
    return True


def revoke_deployment_access(user_id: int | str) -> bool:
    """Revoke deployment access; return False if it was not granted."""
    access = load_deployment_access()
    uid = str(user_id)
    if uid not in access:
        return False
    access.pop(uid)
    save_deployment_access(access)
    return True


def has_deployment_access(user_id: int | str) -> bool:
    record = load_deployment_access().get(str(user_id))
    if record is None:
        return False
    if isinstance(record, str):
        # Backward compatibility for access granted by the previous version.
        return True
    expires_at = record.get("expires_at")
    if not expires_at:
        return True
    try:
        expiry = datetime.fromisoformat(expires_at)
        if expiry.tzinfo is None:
            expiry = expiry.replace(tzinfo=datetime.now().astimezone().tzinfo)
        return datetime.now().astimezone() < expiry
    except (TypeError, ValueError):
        return False


def deployment_access_record_expired(record: Any) -> bool:
    """Return True when a temporary ADD Access record has reached its expiry."""
    if not isinstance(record, dict):
        # Legacy string records have no expiry and remain valid.
        return False
    expires_at = record.get("expires_at")
    if not expires_at:
        return False
    try:
        expiry = datetime.fromisoformat(str(expires_at))
        if expiry.tzinfo is None:
            expiry = expiry.replace(tzinfo=datetime.now().astimezone().tzinfo)
        return datetime.now().astimezone() >= expiry
    except (TypeError, ValueError):
        # Do not stop bots for a malformed record; leave it for Admin review.
        return False


def load_required_channels() -> dict[str, dict]:
    """Return required channel records keyed by Telegram chat ID."""
    if not os.path.exists(REQUIRED_CHANNELS_PATH):
        return {}
    try:
        with open(REQUIRED_CHANNELS_PATH, "r", encoding="utf-8") as f:
            data = json.load(f)
        return data if isinstance(data, dict) else {}
    except (json.JSONDecodeError, OSError, TypeError):
        return {}


def save_required_channels(channels: dict[str, dict]) -> None:
    with open(REQUIRED_CHANNELS_PATH, "w", encoding="utf-8") as f:
        json.dump(channels, f, ensure_ascii=False, indent=2)


def add_required_channel(chat_id: int | str, name: str, link: str) -> bool:
    channels = load_required_channels()
    key = str(chat_id)
    if key in channels:
        return False
    channels[key] = {
        "chat_id": int(chat_id),
        "name": name,
        "link": link,
        "added_at": datetime.now().astimezone().isoformat(),
    }
    save_required_channels(channels)
    return True


def remove_required_channel(chat_id: int | str) -> bool:
    channels = load_required_channels()
    key = str(chat_id)
    if key not in channels:
        return False
    channels.pop(key)
    save_required_channels(channels)
    return True


def add_admin(user_id: int) -> bool:
    """Add a user to the admin list; return False if already an admin."""
    admin_ids = load_admin_ids()
    if user_id in admin_ids:
        return False
    admin_ids.add(user_id)
    save_admin_ids(admin_ids)
    return True


def remove_admin(user_id: int) -> bool:
    """Remove a non-master admin; return False if removal is not allowed."""
    if user_id == ADMIN_ID:
        return False
    admin_ids = load_admin_ids()
    if user_id not in admin_ids:
        return False
    admin_ids.remove(user_id)
    save_admin_ids(admin_ids)
    return True


def load_bot_limit_settings() -> dict:
    """Return the persisted global bot-limit settings."""
    if not os.path.exists(BOT_LIMIT_SETTINGS_PATH):
        return {}
    try:
        with open(BOT_LIMIT_SETTINGS_PATH, "r", encoding="utf-8") as f:
            return json.load(f)
    except (json.JSONDecodeError, OSError):
        return {}


def get_default_bot_limit() -> int | None:
    """Return the global default bot limit; None means unlimited."""
    value = load_bot_limit_settings().get("default_bot_limit")
    if isinstance(value, int) and value >= 0:
        return value
    return None


def set_default_bot_limit(limit: int | None) -> None:
    """Persist the global default bot limit."""
    with open(BOT_LIMIT_SETTINGS_PATH, "w", encoding="utf-8") as f:
        json.dump({"default_bot_limit": limit}, f, ensure_ascii=False, indent=2)


def register_user(user_id: int, username: str) -> bool:
    """Insert a user and report whether this was their first registration."""
    users = load_users()
    uid = str(user_id)
    if uid not in users:
        users[uid] = {
            "user_id": user_id,
            "username": username or "",
            "is_blocked": False,
            "bot_limit": None,
            "hosting_expires_at": None,
            "registered_at": datetime.utcnow().isoformat(),
        }
        save_users(users)
        return True
    elif users[uid].get("username") != (username or ""):
        users[uid]["username"] = username or ""
        save_users(users)
    return False


def is_blocked(user_id: int) -> bool:
    users = load_users()
    return users.get(str(user_id), {}).get("is_blocked", False)


def get_user(user_id: int) -> dict | None:
    return load_users().get(str(user_id))


def get_all_users() -> dict:
    return load_users()


def get_bot_limit(user_id: int | str) -> int | None:
    """Return the user's limit, falling back to the global default."""
    value = load_users().get(str(user_id), {}).get("bot_limit")
    if isinstance(value, int) and value >= 0:
        return value
    return get_default_bot_limit()


def set_bot_limit(user_id: int | str, limit: int | None) -> bool:
    """Persist a bot limit for an existing user; None removes the limit."""
    users = load_users()
    uid = str(user_id)
    if uid not in users:
        return False
    users[uid]["bot_limit"] = limit
    save_users(users)
    return True


def add_user_hosting_limit(
    user_id: int | str,
    duration_seconds: int,
    bot_limit_add: int,
) -> tuple[bool, int | None, str]:
    """Extend a user's hosting time and add to their bot limit."""
    users = load_users()
    uid = str(user_id)
    if uid not in users:
        return False, None, ""

    user = users[uid]
    if bot_limit_add > 0:
        explicit_limit = user.get("bot_limit")
        if isinstance(explicit_limit, int) and explicit_limit >= 0:
            new_limit = explicit_limit + bot_limit_add
        else:
            default_limit = get_default_bot_limit()
            new_limit = (
                default_limit + bot_limit_add
                if default_limit is not None
                else bot_limit_add
            )
        user["bot_limit"] = new_limit
    else:
        new_limit = get_bot_limit(user_id)

    now = datetime.now().astimezone()
    current_expiry = user.get("hosting_expires_at")
    try:
        expiry = datetime.fromisoformat(current_expiry) if current_expiry else now
        if expiry.tzinfo is None:
            expiry = expiry.replace(tzinfo=now.tzinfo)
    except (TypeError, ValueError):
        expiry = now
    expiry = max(now, expiry) + timedelta(seconds=duration_seconds)
    user["hosting_expires_at"] = expiry.isoformat()
    save_users(users)
    return True, new_limit, user["hosting_expires_at"]


def parse_hosting_duration(raw: str) -> int | None:
    """Parse minutes, hours, days, or 30-day months into seconds."""
    match = re.fullmatch(
        r"\s*(\d+(?:\.\d+)?)\s*"
        r"(m|min|mins|minute|minutes|h|hr|hrs|hour|hours|"
        r"d|day|days|mo|mos|mon|month|months)\s*",
        raw,
        re.IGNORECASE,
    )
    if not match:
        return None

    value = float(match.group(1))
    unit = match.group(2).lower()
    if value <= 0:
        return None
    if unit == "m" or unit.startswith("min"):
        multiplier = 60
    elif unit.startswith("h"):
        multiplier = 3600
    elif unit.startswith("d"):
        multiplier = 86400
    else:
        # A month is intentionally treated as 30 days for predictable limits.
        multiplier = 30 * 86400
    return int(value * multiplier)


def hosting_expired(user_id: int | str) -> bool:
    expiry = (get_user(user_id) or {}).get("hosting_expires_at")
    if not expiry:
        return False
    try:
        expiry_dt = datetime.fromisoformat(expiry)
        if expiry_dt.tzinfo is None:
            expiry_dt = expiry_dt.replace(tzinfo=datetime.now().astimezone().tzinfo)
        return datetime.now().astimezone() >= expiry_dt
    except (TypeError, ValueError):
        return False


def block_user(user_id: int) -> bool:
    users = load_users()
    uid = str(user_id)
    if uid not in users:
        return False
    users[uid]["is_blocked"] = True
    save_users(users)
    return True


def unblock_user(user_id: int) -> bool:
    users = load_users()
    uid = str(user_id)
    if uid not in users:
        return False
    users[uid]["is_blocked"] = False
    save_users(users)
    return True

# ── process_manager.py ───────────────────────────────────────────────────────
"""
process_manager.py
------------------
Tracks running sub-bot processes in a JSON file (active_processes.json)
so the master bot remembers which bots are alive after it restarts.

Schema of active_processes.json:
{
  "bot_<uid>_<ts>": {
    "pid":     12345,
    "folder":  "C:\\bots\\<uid>_<ts>",
    "user_id": "123456789"
  },
  ...
}
"""



# Always store the JSON file next to this module (inside bot/)
_BASE = os.path.dirname(os.path.abspath(__file__))
PROCS_FILE = os.path.join(_BASE, "active_processes.json")


# ─── Internal I/O ─────────────────────────────────────────────────────────────

def _load() -> dict:
    if not os.path.exists(PROCS_FILE):
        return {}
    try:
        with open(PROCS_FILE, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return {}


def _save(data: dict) -> None:
    """Atomic write: write to .tmp then rename so we never corrupt the file."""
    tmp = PROCS_FILE + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)
    os.replace(tmp, PROCS_FILE)


# ─── Public helpers ────────────────────────────────────────────────────────────

def is_alive(pid: int) -> bool:
    """Return True if the process with the given PID is currently running."""
    try:
        p = psutil.Process(pid)
        return p.is_running() and p.status() != psutil.STATUS_ZOMBIE
    except (psutil.NoSuchProcess, psutil.AccessDenied, ValueError):
        return False


def register(bot_name: str, pid: int, folder: str, user_id: int | str, entry_file: str = "main.py") -> None:
    """Add or update a tracked bot process."""
    data = _load()
    data[bot_name] = {
        "pid":     pid,
        "folder":  folder,
        "user_id": str(user_id),
        "entry_file": entry_file,
    }
    _save(data)


def unregister(bot_name: str) -> None:
    """Remove a bot from the tracking file."""
    data = _load()
    data.pop(bot_name, None)
    _save(data)


def update_pid(bot_name: str, new_pid: int) -> None:
    """Update only the PID for an existing entry (used after restart)."""
    data = _load()
    if bot_name in data:
        data[bot_name]["pid"] = new_pid
        _save(data)


def get_user_procs(user_id: int | str) -> list[dict]:
    """
    Return all tracked bots belonging to user_id.
    Each dict: {name, pid, folder, alive}
    """
    data = _load()
    result = []
    for name, entry in data.items():
        if str(entry.get("user_id")) == str(user_id):
            pid = entry.get("pid", -1)
            result.append({
                "name":   name,
                "pid":    pid,
                "folder": entry.get("folder", ""),
                "entry_file": entry.get("entry_file", "main.py"),
                "alive":  is_alive(pid),
            })
    return result


def get_all_procs() -> list[dict]:
    """
    Return all tracked bots (admin view).
    Each dict: {name, pid, folder, user_id, alive}
    """
    data = _load()
    result = []
    for name, entry in data.items():
        pid = entry.get("pid", -1)
        result.append({
            "name":    name,
            "pid":     pid,
            "folder":  entry.get("folder", ""),
            "user_id": entry.get("user_id", "?"),
            "entry_file": entry.get("entry_file", "main.py"),
            "alive":   is_alive(pid),
        })
    return result


def load_raw() -> dict:
    """Return the raw JSON dict — used by System Restart."""
    return _load()

# Preserve the original process_manager alias used by the handlers.
pm = sys.modules[__name__]

# ── keyboards.py ─────────────────────────────────────────────────────────────


# ─── Reply Keyboards (persistent buttons at the bottom of the mobile app) ───

def main_reply_keyboard(is_admin: bool = False) -> ReplyKeyboardMarkup:
    """
    Main persistent keyboard.
    When is_admin=True an extra '🛡 Admin Panel' row is appended.
    """
    rows = [
        [
            KeyboardButton(text=BTN_UPLOAD),
            KeyboardButton(text=BTN_MYBOTS),
        ]
    ]
    rows.append([
        KeyboardButton(text=BTN_PROFILE),
        KeyboardButton(text=BTN_DEPOSIT),
    ])
    if is_admin:
        rows.append([
            KeyboardButton(text=BTN_SUPPORT),
            KeyboardButton(text=BTN_ADMIN_PANEL),
        ])
    else:
        rows.append([KeyboardButton(text=BTN_SUPPORT)])
    return ReplyKeyboardMarkup(
        keyboard=rows,
        resize_keyboard=True,
        persistent=True,
        input_field_placeholder="Choose an option from the menu...",
    )


def user_panel_inline_keyboard() -> InlineKeyboardMarkup:
    """Inline-only actions that must not become persistent mobile buttons."""
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text=BTN_DEPOSIT, callback_data="dep_open")],
        ]
    )


def deposit_wallet_type_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [
                InlineKeyboardButton(text="bKash", callback_data="dep_admin_type_bkash"),
                InlineKeyboardButton(text="Nagad", callback_data="dep_admin_type_nagad"),
            ],
            [
                InlineKeyboardButton(text="Binance", callback_data="dep_admin_type_binance"),
                InlineKeyboardButton(text="Other", callback_data="dep_admin_type_other"),
            ],
            [InlineKeyboardButton(text="❌ Cancel", callback_data="dep_admin_cancel")],
        ]
    )


def deposit_admin_menu_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [
                InlineKeyboardButton(text="➕ Add Wallet", callback_data="dep_admin_add_wallet"),
                InlineKeyboardButton(text="🗑 Remove Wallet", callback_data="dep_admin_remove_wallet"),
            ],
            [
                InlineKeyboardButton(text="📥 Deposit Pending", callback_data="dep_admin_notifications"),
                InlineKeyboardButton(text="⬅ Back", callback_data="dep_admin_back"),
            ],
        ]
    )


def _wallet_button_label(wallet: dict) -> str:
    return (
        f"{wallet.get('wallet_type', 'Wallet')} — "
        f"{wallet.get('name', 'Unnamed')}"
    )


def admin_panel_inline_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text=BTN_DEPOSIT_SYSTEM, callback_data="dep_admin_menu")],
        ]
    )


def deposit_cancel_keyboard(callback_data: str = "dep_user_cancel") -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="❌ Cancel", callback_data=callback_data)]
        ]
    )


def wallet_add_confirmation_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="✅ Confirm Add", callback_data="dep_admin_add_confirm")],
            [InlineKeyboardButton(text="✏️ Edit", callback_data="dep_admin_add_edit")],
            [InlineKeyboardButton(text="❌ Cancel", callback_data="dep_admin_cancel")],
        ]
    )


def wallet_remove_list_keyboard(wallets: list[dict]) -> InlineKeyboardMarkup:
    buttons = []
    for index in range(0, len(wallets), 2):
        buttons.append([
            InlineKeyboardButton(
                text=_wallet_button_label(wallet),
                callback_data=f"dep_admin_remove_select_{wallet.get('id', '')}",
            )
            for wallet in wallets[index:index + 2]
        ])
    buttons.append([InlineKeyboardButton(text="⬅ Back", callback_data="dep_admin_back")])
    return InlineKeyboardMarkup(inline_keyboard=buttons)


def wallet_remove_confirmation_keyboard(wallet_id: str) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="✅ Confirm Remove", callback_data=f"dep_admin_remove_confirm_{wallet_id}")],
            [InlineKeyboardButton(text="❌ Cancel", callback_data="dep_admin_remove_wallet")],
        ]
    )


def active_wallets_keyboard(wallets: list[dict]) -> InlineKeyboardMarkup:
    buttons = []
    for index in range(0, len(wallets), 2):
        buttons.append([
            InlineKeyboardButton(
                text=_wallet_button_label(wallet),
                callback_data=f"dep_user_wallet_{wallet.get('id', '')}",
            )
            for wallet in wallets[index:index + 2]
        ])
    buttons.append([InlineKeyboardButton(text="❌ Cancel", callback_data="dep_user_cancel")])
    return InlineKeyboardMarkup(inline_keyboard=buttons)


def wallet_details_keyboard(wallet_id: str) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="📤 Send Payment Proof", callback_data=f"dep_user_proof_{wallet_id}")],
            [InlineKeyboardButton(text="⬅ Choose Another Wallet", callback_data="dep_open")],
            [InlineKeyboardButton(text="❌ Cancel", callback_data="dep_user_cancel")],
        ]
    )


def deposit_transaction_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="⏭ Skip", callback_data="dep_user_tx_skip")],
            [InlineKeyboardButton(text="❌ Cancel", callback_data="dep_user_cancel")],
        ]
    )


def deposit_preview_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="✅ Submit Deposit", callback_data="dep_user_submit")],
            [InlineKeyboardButton(text="🔄 Send Again", callback_data="dep_user_proof_again")],
            [InlineKeyboardButton(text="❌ Cancel", callback_data="dep_user_cancel")],
        ]
    )


def admin_notification_keyboard(deposit_id: str) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [
                InlineKeyboardButton(text="✅ Approve", callback_data=f"dep_admin_approve_{deposit_id}"),
                InlineKeyboardButton(text="❌ Reject", callback_data=f"dep_admin_reject_{deposit_id}"),
            ],
            [InlineKeyboardButton(text="🔍 View Details", callback_data=f"dep_admin_details_{deposit_id}")],
        ]
    )


def admin_reject_reason_keyboard(deposit_id: str) -> InlineKeyboardMarkup:
    reasons = [
        ("Payment proof is unclear", "proof_unclear"),
        ("Amount does not match", "amount_mismatch"),
        ("Transaction could not be verified", "transaction_unverified"),
        ("Payment sent to the wrong wallet", "wrong_wallet"),
        ("Other", "other"),
    ]
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text=label, callback_data=f"dep_admin_reason_{key}_{deposit_id}")]
            for label, key in reasons
        ] + [
            [InlineKeyboardButton(text="❌ Cancel", callback_data=f"dep_admin_notification_back_{deposit_id}")]
        ]
    )


def admin_deposit_decision_keyboard(deposit_id: str, action: str) -> InlineKeyboardMarkup:
    confirmation_label = (
        "Confirm Approval" if action.casefold() == "approve"
        else "Confirm Rejection"
    )
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(
                text=f"✅ {confirmation_label}",
                callback_data=f"dep_admin_{action.casefold()}_confirm_{deposit_id}",
            )],
            [InlineKeyboardButton(text="❌ Cancel", callback_data=f"dep_admin_notification_back_{deposit_id}")],
        ]
    )


def blocked_user_keyboard() -> ReplyKeyboardMarkup:
    """The only reply keyboard available to a blocked user."""
    return ReplyKeyboardMarkup(
        keyboard=[[KeyboardButton(text=BTN_SUPPORT)]],
        resize_keyboard=True,
        persistent=True,
        input_field_placeholder="Contact Admin through Support...",
    )


def deployment_disabled_keyboard() -> InlineKeyboardMarkup:
    """Inline Support button shown when deployment is disabled."""
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [
                InlineKeyboardButton(
                    text=BTN_SUPPORT,
                    url="https://t.me/Limonff143",
                )
            ]
        ]
    )


def upload_reply_keyboard() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        keyboard=[
            [
                KeyboardButton(text=BTN_DONE),
                KeyboardButton(text=BTN_CANCEL),
            ]
        ],
        resize_keyboard=True,
        input_field_placeholder="Send a .zip, .py, or .js file...",
    )


def replace_reply_keyboard() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        keyboard=[
            [KeyboardButton(text=BTN_CANCEL_R)]
        ],
        resize_keyboard=True,
        input_field_placeholder="Send the replacement file...",
    )


# ─── Inline Keyboards (Dynamic Content) ──────────────────────────────────────

def mybots_keyboard(bots: list) -> InlineKeyboardMarkup:
    """
    bots: list of dicts from process_manager.get_user_procs()
          Each dict has: {name, pid, folder, alive}
    """
    buttons = []
    for bot in bots:
        name  = bot["name"]
        alive = bot.get("alive", False)
        emoji = "🟢" if alive else "🔴"
        label = "Running" if alive else "Stopped"
        buttons.append([
            InlineKeyboardButton(
                text=f"{emoji} {name} [{label}]",
                callback_data=f"bot_info_{name}",
            )
        ])
    return InlineKeyboardMarkup(inline_keyboard=buttons)


def bot_action_keyboard(bot_name: str) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="📋 𝐕ɪᴇᴡ 𝐋ᴏɢs",  callback_data=f"view_logs_{bot_name}")],
        [InlineKeyboardButton(text="📁 𝐕ɪᴇᴡ 𝐅ɪʟᴇs", callback_data=f"view_files_{bot_name}")],
        [InlineKeyboardButton(
            text="🔄 𝐑ᴇsᴛᴀʀᴛ 𝐁ᴏᴛ",
            callback_data=f"confirm_restart_bot_{bot_name}",
            style="success",
        )],
        [InlineKeyboardButton(
            text="🗑 𝐃ᴇʟᴇᴛᴇ 𝐁ᴏᴛ",
            callback_data=f"confirm_delete_bot_{bot_name}",
        )],
        [InlineKeyboardButton(text="⬅️ 𝐁ᴀᴄᴋ ᴛᴏ 𝐋ɪsᴛ", callback_data="back_bots")],
    ])


def user_restart_confirmation_keyboard(bot_name: str) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [
            InlineKeyboardButton(
                text="✅ 𝐂ᴏɴғɪʀᴍ 𝐑ᴇsᴛᴀʀᴛ",
                callback_data=f"restart_bot_{bot_name}",
                style="success",
            )
        ],
        [
            InlineKeyboardButton(
                text="🔙 𝐁ᴀᴄᴋ",
                callback_data=f"bot_info_{bot_name}",
            )
        ],
    ])


def user_delete_confirmation_keyboard(bot_name: str) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [
            InlineKeyboardButton(
                text="⚠️ 𝐂ᴏɴғɪʀᴍ 𝐃ᴇʟᴇᴛᴇ",
                callback_data=f"delete_bot_{bot_name}",
                style="danger",
            )
        ],
        [
            InlineKeyboardButton(
                text="🔙 𝐁ᴀᴄᴋ",
                callback_data=f"bot_info_{bot_name}",
            )
        ],
    ])


def files_keyboard(bot_name: str, filenames: list) -> InlineKeyboardMarkup:
    buttons = []
    for fname in filenames:
        cb = f"fi_{bot_name}|{fname}"
        if len(cb.encode()) <= 64:
            buttons.append([
                InlineKeyboardButton(text=f"📄 𝐕ɪᴇᴡ: {fname}", callback_data=cb)
            ])
    buttons.append([
        InlineKeyboardButton(text="⬅️ 𝐁ᴀᴄᴋ", callback_data=f"bot_info_{bot_name}")
    ])
    return InlineKeyboardMarkup(inline_keyboard=buttons)


def file_action_keyboard(bot_name: str, filename: str) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="📥 𝐃ᴏᴡɴʟᴏᴀᴅ",           callback_data=f"dl_{bot_name}|{filename}")],
        [InlineKeyboardButton(text="➕ 𝐔ᴘʟᴏᴀᴅ/𝐑ᴇᴘʟᴀᴄᴇ 𝐅ɪʟᴇ", callback_data=f"rp_{bot_name}|{filename}")],
        [InlineKeyboardButton(text="⬅️ 𝐁ᴀᴄᴋ ᴛᴏ 𝐅ɪʟᴇs",      callback_data=f"view_files_{bot_name}")],
    ])

# ── admin_keyboards.py ───────────────────────────────────────────────────────


# ─── Admin Panel — Persistent Reply Keyboard (mobile app) ───────────────────

def admin_reply_keyboard() -> ReplyKeyboardMarkup:
    """
    Shown at the bottom of the screen whenever the admin is in the Admin Panel.
    Replaces the main user keyboard while the admin is operating admin features.
    """
    return ReplyKeyboardMarkup(
        keyboard=[
            [KeyboardButton(text="📊 System Stats"),   KeyboardButton(text="🤖 Active Bots")],
            [KeyboardButton(text=BTN_USERS),           KeyboardButton(text=BTN_USER_SETTING)],
            [KeyboardButton(text="📢 Broadcast"),      KeyboardButton(text="🔄 System Restart")],
            [
                KeyboardButton(text=f"🚦 Deployment: {'ON' if is_deployment_enabled() else 'OFF'}"),
                KeyboardButton(text=BTN_DEPOSIT_SYSTEM),
            ],
        ],
        resize_keyboard=True,
        persistent=True,
        input_field_placeholder="Admin Panel — choose an option...",
    )


def admin_management_reply_keyboard() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        keyboard=[
            [
                KeyboardButton(text="➕ Add Admin"),
                KeyboardButton(text="➖ Remove Admin"),
            ],
            [
                KeyboardButton(text="📋 Admin List"),
                KeyboardButton(text=BTN_BACK_USER_SETTING),
            ],
        ],
        resize_keyboard=True,
        persistent=True,
        input_field_placeholder="ADD ADMIN — choose an option...",
    )


def admin_management_cancel_reply_keyboard() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        keyboard=[
            [KeyboardButton(text="❌ Cancel Admin Action")],
            [KeyboardButton(text="🔙 Back to ADD ADMIN")],
        ],
        resize_keyboard=True,
        persistent=True,
        input_field_placeholder="Enter a numeric Telegram User ID...",
    )


# ─── User Info — Block / Unblock Toggle (Inline) ─────────────────────────────

def admin_user_info_keyboard(user_id: int, blocked: bool) -> InlineKeyboardMarkup:
    if blocked:
        toggle_text = "✅ Unblock User"
        toggle_cb   = f"admin_unblock_{user_id}"
    else:
        toggle_text = "🚫 Block User"
        toggle_cb   = f"admin_block_{user_id}"
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text=toggle_text, callback_data=toggle_cb)],
    ])


# ─── FSM Reply Keyboards (while the Admin is in an FSM state) ───────────────

def broadcast_cancel_reply_keyboard() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        keyboard=[[KeyboardButton(text="❌ Cancel Broadcast")]],
        resize_keyboard=True,
        input_field_placeholder="Send the message to broadcast...",
    )


def user_lookup_cancel_reply_keyboard() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        keyboard=[[KeyboardButton(text="❌ Cancel Lookup")]],
        resize_keyboard=True,
        input_field_placeholder="Enter the numeric User ID...",
    )


def user_manager_reply_keyboard() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        keyboard=[
            [
                KeyboardButton(text="🚫 Ban / Unban User"),
                KeyboardButton(text="📋 All Users & Excel"),
            ],
            [
                KeyboardButton(text="🚫 Banned Users"),
                KeyboardButton(text=BTN_ADD_ADMIN_ENTRY),
            ],
            [KeyboardButton(text="🔙 Back to Admin Panel")],
        ],
        resize_keyboard=True,
        persistent=True,
        input_field_placeholder="Choose a User settings option...",
    )


def user_setting_reply_keyboard() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        keyboard=[
            [
                KeyboardButton(text="⚙️ Bot Limit"),
                KeyboardButton(text="📥 User ZIP Download"),
            ],
            [
                KeyboardButton(text="👤 Add User Limit"),
                KeyboardButton(text=BTN_DEPLOYMENT_ACCESS),
            ],
            [KeyboardButton(text="📢 Channel Verification")],
            [KeyboardButton(text="🔙 Back to Admin Panel")],
        ],
        resize_keyboard=True,
        persistent=True,
        input_field_placeholder="Choose a User Setting option...",
    )


def deployment_access_reply_keyboard() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        keyboard=[
            [
                KeyboardButton(text="➕ Add Access"),
                KeyboardButton(text="📋 Access List & Excel"),
            ],
            [
                KeyboardButton(text="🔙 Back"),
                KeyboardButton(text="🔙 Back to Admin Panel"),
            ],
        ],
        resize_keyboard=True,
        persistent=True,
        input_field_placeholder="Choose an ADD Access option...",
    )


def deployment_access_cancel_reply_keyboard() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        keyboard=[
            [
                KeyboardButton(text=BTN_CANCEL_DEPLOYMENT_ACCESS),
                KeyboardButton(text=BTN_BACK_DEPLOYMENT_ACCESS),
            ],
        ],
        resize_keyboard=True,
        persistent=True,
        input_field_placeholder="Enter the numeric Telegram User ID...",
    )


def channel_management_reply_keyboard() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        keyboard=[
            [
                KeyboardButton(text="➕ Add Required Channel"),
                KeyboardButton(text="📋 Channel List & Remove"),
            ],
            [
                KeyboardButton(text="🔙 Back"),
                KeyboardButton(text="🔙 Back to Admin Panel"),
            ],
        ],
        resize_keyboard=True,
        persistent=True,
        input_field_placeholder="Choose a Channel Verification option...",
    )


def channel_name_cancel_reply_keyboard() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        keyboard=[
            [
                KeyboardButton(text="❌ Cancel Channel Add"),
                KeyboardButton(text="🔙 Back to Channel Verification"),
            ],
        ],
        resize_keyboard=True,
        persistent=True,
        input_field_placeholder="Enter the Channel name...",
    )


def channel_link_cancel_reply_keyboard() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        keyboard=[
            [
                KeyboardButton(text="❌ Cancel Channel Add"),
                KeyboardButton(text="🔙 Back to Channel Verification"),
            ],
        ],
        resize_keyboard=True,
        persistent=True,
        input_field_placeholder="Enter the public Channel link...",
    )


def deployment_access_keyboard(user_ids: list[int]) -> InlineKeyboardMarkup:
    buttons = []
    for index in range(0, len(user_ids), 2):
        row = [
            InlineKeyboardButton(
                text=f"❌ Revoke {user_id}",
                callback_data=f"revoke_deploy_{user_id}",
            )
            for user_id in user_ids[index:index + 2]
        ]
        buttons.append(row)
    return InlineKeyboardMarkup(inline_keyboard=buttons)


def channel_verification_keyboard(channels: list[dict]) -> InlineKeyboardMarkup:
    buttons = []
    for channel in channels:
        link = channel.get("link", "")
        if link:
            buttons.append([
                InlineKeyboardButton(
                    text=f"📢 Join {channel.get('name', 'Channel')}",
                    url=link,
                )
            ])
    buttons.append([
        InlineKeyboardButton(
            text="✅ Verify Membership",
            callback_data="verify_required_channels",
        )
    ])
    return InlineKeyboardMarkup(inline_keyboard=buttons)


def required_channels_admin_keyboard(channel_ids: list[str]) -> InlineKeyboardMarkup:
    buttons = []
    for index in range(0, len(channel_ids), 2):
        buttons.append([
            InlineKeyboardButton(
                text=f"❌ Remove {channel_id}",
                callback_data=f"remove_required_channel_{channel_id}",
            )
            for channel_id in channel_ids[index:index + 2]
        ])
    return InlineKeyboardMarkup(inline_keyboard=buttons)


def settings_reply_keyboard() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        keyboard=[
            [KeyboardButton(text="🔙 Back to Admin Panel")],
        ],
        resize_keyboard=True,
        persistent=True,
        input_field_placeholder="Choose a Settings option...",
    )


def add_limit_cancel_reply_keyboard() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        keyboard=[
            [
                KeyboardButton(text="❌ Cancel Add Limit"),
                KeyboardButton(text="🔙 Back"),
            ],
        ],
        resize_keyboard=True,
        persistent=True,
        input_field_placeholder="Enter the User ID...",
    )


def bot_limit_cancel_reply_keyboard() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        keyboard=[[KeyboardButton(text="❌ Cancel Bot Limit")]],
        resize_keyboard=True,
        input_field_placeholder="Enter the default Bot limit...",
    )


def bot_limit_cancel_inline_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [
                InlineKeyboardButton(
                    text="❌ Cancel",
                    callback_data="cancel_default_bot_limit",
                )
            ]
        ]
    )


def zip_download_cancel_reply_keyboard() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        keyboard=[[KeyboardButton(text="❌ Cancel ZIP Download")]],
        resize_keyboard=True,
        input_field_placeholder="Enter the User ID...",
    )


def restart_cancel_reply_keyboard() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        keyboard=[[KeyboardButton(text=BTN_CANCEL_RESTART)]],
        resize_keyboard=True,
        input_field_placeholder="Enter the User ID...",
    )


def admin_zip_download_keyboard(bots: list[dict]) -> InlineKeyboardMarkup:
    buttons = []
    for bot in bots:
        name = bot["name"]
        source_status = "✅" if os.path.exists(original_zip_path_from_name(name)) else "⚠️"
        buttons.append([
            InlineKeyboardButton(
                text=f"{source_status} {name}",
                callback_data=f"admin_zip_download_{name}",
            )
        ])
    return InlineKeyboardMarkup(inline_keyboard=buttons)


def restart_options_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [
            InlineKeyboardButton(
                text="👤 Restart a User's Bot",
                callback_data="admin_restart_specific_user",
            )
        ],
        [
            InlineKeyboardButton(
                text="🌐 Restart All Users' Bots",
                callback_data="admin_restart_all_confirm",
            )
        ],
    ])


def restart_user_bots_keyboard(bots: list[dict]) -> InlineKeyboardMarkup:
    buttons = []
    for proc in bots:
        name = proc["name"]
        status = "🟢" if proc.get("alive") else "🔴"
        buttons.append([
            InlineKeyboardButton(
                text=f"{status} Restart {name}",
                callback_data=f"admin_restart_select_{name}",
            )
        ])
    buttons.append([
        InlineKeyboardButton(text="🔙 Back", callback_data="admin_restart_menu")
    ])
    return InlineKeyboardMarkup(inline_keyboard=buttons)


def restart_selected_bot_confirmation_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [
            InlineKeyboardButton(
                text="✅ Restart This Bot",
                callback_data="admin_restart_bot_confirm",
                style="success",
            ),
        ],
        [
            InlineKeyboardButton(
                text="🔙 Back",
                callback_data="admin_restart_user_bots_back",
            ),
        ],
    ])


def restart_all_confirmation_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [
            InlineKeyboardButton(
                text="⚠️ Yes, Restart All Bots",
                callback_data="admin_restart_all_execute",
                style="danger",
            )
        ],
        [
            InlineKeyboardButton(
                text="🔙 Back",
                callback_data="admin_restart_menu",
                style="primary",
            )
        ],
    ])


def build_users_excel(users: dict) -> bytes:
    """Create a dependency-free .xlsx file containing every stored user field."""
    rows = []
    headers = []
    for uid, user in users.items():
        row = {"user_id": user.get("user_id", uid), **user}
        rows.append(row)
        for key in row:
            if key not in headers:
                headers.append(key)

    def cell(column: int, row_number: int, value: Any) -> str:
        letters = ""
        number = column
        while number:
            number, remainder = divmod(number - 1, 26)
            letters = chr(65 + remainder) + letters
        text = html.escape("" if value is None else str(value), quote=True)
        return (
            f'<c r="{letters}{row_number}" t="inlineStr">'
            f"<is><t>{text}</t></is></c>"
        )

    sheet_rows = []
    all_rows = [headers] + [[row.get(header, "") for header in headers] for row in rows]
    for row_number, row in enumerate(all_rows, start=1):
        cells = "".join(cell(column, row_number, value) for column, value in enumerate(row, start=1))
        sheet_rows.append(f'<row r="{row_number}">{cells}</row>')

    sheet_xml = (
        '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
        '<worksheet xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main">'
        f"<sheetData>{''.join(sheet_rows)}</sheetData>"
        "</worksheet>"
    )
    content_types = (
        '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
        '<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">'
        '<Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/>'
        '<Default Extension="xml" ContentType="application/xml"/>'
        '<Override PartName="/xl/workbook.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet.main+xml"/>'
        '<Override PartName="/xl/worksheets/sheet1.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.worksheet+xml"/>'
        "</Types>"
    )
    root_rels = (
        '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
        '<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">'
        '<Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/officeDocument" Target="xl/workbook.xml"/>'
        "</Relationships>"
    )
    workbook = (
        '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
        '<workbook xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main" '
        'xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships">'
        '<sheets><sheet name="Users" sheetId="1" r:id="rId1"/></sheets></workbook>'
    )
    workbook_rels = (
        '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
        '<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">'
        '<Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/worksheet" Target="worksheets/sheet1.xml"/>'
        "</Relationships>"
    )

    output = io.BytesIO()
    with zipfile.ZipFile(output, "w", zipfile.ZIP_DEFLATED) as archive:
        archive.writestr("[Content_Types].xml", content_types)
        archive.writestr("_rels/.rels", root_rels)
        archive.writestr("xl/workbook.xml", workbook)
        archive.writestr("xl/_rels/workbook.xml.rels", workbook_rels)
        archive.writestr("xl/worksheets/sheet1.xml", sheet_xml)
    return output.getvalue()

# ── middleware.py ────────────────────────────────────────────────────────────


def _is_navigation_message(text: str | None) -> bool:
    """Return True for commands/buttons that should leave any active FSM flow."""
    if not text:
        return False
    if text.split(maxsplit=1)[0] == "/start":
        return True
    if text.startswith("🚦 Deployment:"):
        return True

    # These are menu destinations or actions that intentionally start a new
    # flow. Clearing the old state before routing prevents an earlier numeric
    # input handler from hijacking a newly selected menu button.
    return text in {
        BTN_UPLOAD,
        BTN_MYBOTS,
        BTN_PROFILE,
        BTN_SUPPORT,
        BTN_ADMIN_PANEL,
        BTN_STATS,
        BTN_BOTS,
        BTN_USERS,
        BTN_USER_SETTING,
        BTN_SETTINGS,
        BTN_BROADCAST,
        BTN_RESTART,
        BTN_BAN_UNBAN,
        BTN_ALL_USERS,
        BTN_BANNED_USERS,
        BTN_ADD_ADMIN_ENTRY,
        BTN_ADD_USER_LIMIT,
        BTN_BOT_LIMIT,
        BTN_ZIP_DOWNLOAD,
        BTN_DEPLOYMENT_ACCESS,
        BTN_GRANT_DEPLOYMENT_ACCESS,
        BTN_ACCESS_LIST,
        BTN_CHANNEL_VERIFICATION,
        BTN_ADD_REQUIRED_CHANNEL,
        BTN_CHANNEL_LIST_REMOVE,
        BTN_BACK_CHANNEL_VERIFICATION,
        BTN_BACK_USER_MENU,
        BTN_BACK_ADMIN_PANEL,
        BTN_BACK_USER_SETTING,
        BTN_BACK_DEPLOYMENT_ACCESS,
        BTN_DEPOSIT_SYSTEM,
        BTN_DEPOSIT_ADD_WALLET,
        BTN_DEPOSIT_REMOVE_WALLET,
        BTN_DEPOSIT_PENDING,
        BTN_DEPOSIT_BACK,
        "📋 Admin List",
        "➕ Add Admin",
        "➖ Remove Admin",
    }


class UserMiddleware(BaseMiddleware):
    """
    Global middleware that runs before every Message and CallbackQuery handler.

    Responsibilities
    ────────────────
    1. Register the user in users.json (first touch or username update).
    2. If the user is blocked, silently stop execution and notify them.
       The admin (ADMIN_ID) is always allowed through unconditionally.
    3. Clear stale FSM state when a top-level navigation command is selected.
    """

    async def __call__(
        self,
        handler: Callable[[TelegramObject, dict], Awaitable[Any]],
        event: TelegramObject,
        data: dict,
    ) -> Any:
        user = None
        if isinstance(event, Message):
            user = event.from_user
        elif isinstance(event, CallbackQuery):
            user = event.from_user

        if user:
            data["is_new_user"] = register_user(user.id, user.username or "")

            # Styled reply buttons send their rendered label back to Telegram.
            # Normalize it before the existing exact-text handlers run; this
            # preserves every existing feature and callback contract.
            if isinstance(event, Message) and event.text:
                canonical_text = _REPLY_BUTTON_ALIASES.get(event.text)
                if canonical_text and canonical_text != event.text:
                    # aiogram's Pydantic Message model is frozen. Create a
                    # validated copy instead of mutating event.text in place.
                    event = event.model_copy(update={"text": canonical_text})

            # A menu command is an explicit request to leave the current
            # workflow. Do this before routing so state-specific handlers
            # cannot interpret "System Stats", "/start", etc. as an ID.
            if (
                user
                and is_admin(user.id)
                and isinstance(event, Message)
                and _is_navigation_message(event.text)
            ):
                current_state = data.get("state")
                if current_state is not None:
                    await current_state.clear()

            # Admin is unconditionally allowed; everyone else is checked.
            if not is_admin(user.id) and is_blocked(user.id):
                # A blocked user may use only the Support button so they can
                # contact the Admin. Every other message and callback is halted.
                if isinstance(event, Message) and event.text == BTN_SUPPORT:
                    return await handler(event, data)
                if isinstance(event, Message):
                    await event.answer(
                        "⛔ <b>You are blocked from this Bot.</b>\n\n"
                        "You can only use the Support button to contact the Admin.",
                        reply_markup=blocked_user_keyboard(),
                        parse_mode="HTML",
                    )
                elif isinstance(event, CallbackQuery):
                    await event.answer(
                        "⛔ You are blocked. Only Support is available.",
                        show_alert=True,
                    )
                return  # Halt — do not call downstream handlers

        return await handler(event, data)

# ── handlers.py ──────────────────────────────────────────────────────────────




router = Router()

# ─── Button Text Constants ─────────────────────────────────────────────────────
BTN_UPLOAD   = "▴ 𝐔ᴘʟᴏᴀᴅ 𝐁ᴏᴛ"
BTN_MYBOTS   = "🤖 𝐌ʏ 𝐁ᴏᴛs"
BTN_PROFILE  = "👤 𝐌ʏ 𝐏ʀᴏғɪʟᴇ"
BTN_SUPPORT  = "🆘 𝐒ᴜᴘᴘᴏʀᴛ"
BTN_DONE     = "✅ 𝐔ᴘʟᴏᴀᴅ 𝐃ᴏɴᴇ"
BTN_CANCEL   = "❌ 𝐂ᴀɴᴄᴇʟ 𝐔ᴘʟᴏᴀᴅ"
BTN_CANCEL_R = "❌ 𝐂ᴀɴᴄᴇʟ 𝐑ᴇᴘʟᴀᴄᴇ"
BTN_DEPOSIT  = "💰 Deposit"

# ─── Cross-platform Temporary Directory ───────────────────────────────────────
# tempfile.gettempdir() returns:
#   Windows → C:\Users\<user>\AppData\Local\Temp
#   Linux   → /tmp
TMP_DIR = os.path.join(tempfile.gettempdir(), "master_bot_tmp")
ORIGINAL_ZIPS_DIR = os.path.join(BOTS_BASE_DIR, "_original_zips")


# ─── FSM States ──────────────────────────────────────────────────────────────

class BotStates(StatesGroup):
    waiting_for_zip          = State()
    waiting_for_replace_file = State()
    waiting_for_channel_name = State()
    waiting_for_channel_link = State()
    waiting_for_deposit_sender_number = State()
    waiting_for_deposit_amount = State()
    waiting_for_deposit_transaction = State()
    waiting_for_deposit_proof = State()


def deployment_is_allowed(user_id: int) -> bool:
    """Global ON allows deployment; when OFF only explicitly granted users may deploy."""
    return is_deployment_enabled() or has_deployment_access(user_id)


async def user_has_required_channel_membership(
    bot: Bot,
    user_id: int,
) -> tuple[bool, list[dict]]:
    """Check membership in every configured channel."""
    channels = list(load_required_channels().values())
    missing = []
    for channel in channels:
        try:
            member = await bot.get_chat_member(
                chat_id=int(channel["chat_id"]),
                user_id=user_id,
            )
            is_member = member.status in {"creator", "administrator", "member"}
            if member.status == "restricted":
                is_member = bool(getattr(member, "is_member", False))
            if not is_member:
                missing.append(channel)
        except Exception:
            # A channel that cannot be checked must not grant access.
            missing.append(channel)
    return not missing, missing


async def ensure_user_channel_verified(message: Message, bot: Bot) -> bool:
    """Show the verification panel and block user-panel access when needed."""
    if is_admin(message.from_user.id):
        return True
    verified, missing = await user_has_required_channel_membership(
        bot,
        message.from_user.id,
    )
    if verified:
        return True
    await message.answer(
        "🔒 <b>Channel Verification Required</b>\n\n"
        "Join every required channel below, then press "
        "<b>✅ Verify Membership</b> to use the User Panel.",
        reply_markup=channel_verification_keyboard(missing),
        parse_mode="HTML",
    )
    return False


# ─── Helpers ──────────────────────────────────────────────────────────────────

def is_admin(user_id: int) -> bool:
    return user_id in load_admin_ids()


def get_user_bots(user_id: int) -> list[dict]:
    """
    Return tracked bots for this user from active_processes.json.
    Each dict: {name, pid, folder, alive}
    """
    return pm.get_user_procs(user_id)


def get_tracked_bot(user_id: int, bot_name: str) -> dict | None:
    """Return the persisted process record for one user-owned bot."""
    return next(
        (
            proc for proc in pm.get_user_procs(user_id)
            if proc.get("name") == bot_name
        ),
        None,
    )


def get_tracked_bot_folder(user_id: int, bot_name: str) -> str:
    """Prefer the persisted absolute folder over reconstructing it from a name."""
    tracked = get_tracked_bot(user_id, bot_name)
    if tracked and tracked.get("folder"):
        return str(tracked["folder"])
    return bot_folder_from_name(bot_name)


def format_duration(seconds: float) -> str:
    """Format a duration for the user profile."""
    total_seconds = max(0, int(seconds))
    days, remainder = divmod(total_seconds, 86400)
    hours, remainder = divmod(remainder, 3600)
    minutes, _ = divmod(remainder, 60)

    parts = []
    if days:
        parts.append(f"{days} days")
    if hours:
        parts.append(f"{hours} hours")
    if minutes or not parts:
        parts.append(f"{minutes} minutes")
    return " ".join(parts)


def get_bot_runtime_seconds(bot_info: dict) -> float:
    """Return the current runtime for a running tracked bot."""
    if not bot_info.get("alive"):
        return 0
    try:
        process = psutil.Process(int(bot_info.get("pid", -1)))
        return max(0, time.time() - process.create_time())
    except (psutil.NoSuchProcess, psutil.AccessDenied, ValueError, TypeError):
        return 0


def bot_folder_from_name(bot_name: str) -> str:
    """
    bot_name format: bot_<uid>_<timestamp>
    folder  format: <uid>_<timestamp>  inside BOTS_BASE_DIR
    """
    parts = bot_name.split("_", 2)   # ["bot", "<uid>", "<ts>"]
    if len(parts) == 3:
        return os.path.join(BOTS_BASE_DIR, f"{parts[1]}_{parts[2]}")
    return ""


def original_zip_path_from_name(bot_name: str) -> str:
    return os.path.join(ORIGINAL_ZIPS_DIR, f"{bot_name}.zip")


def bot_python_path(bot_folder: str) -> str:
    """Return the platform-specific Python executable inside a bot venv."""
    if os.name == "nt":
        return os.path.join(bot_folder, ".venv", "Scripts", "python.exe")
    return os.path.join(bot_folder, ".venv", "bin", "python")


ENTRY_FILE_PRIORITY = ("bot.py", "main.py", "app.py", "index.js")


def detect_entry_file(bot_folder: str) -> str | None:
    """Return the first supported entry file found, using the documented priority."""
    candidates = []
    for root, dirs, files in os.walk(bot_folder):
        dirs[:] = [d for d in dirs if d not in {".venv", "__pycache__", "node_modules"}]
        for filename in files:
            if filename in ENTRY_FILE_PRIORITY:
                relative = os.path.relpath(os.path.join(root, filename), bot_folder)
                candidates.append(relative)
    for preferred_name in ENTRY_FILE_PRIORITY:
        matches = sorted(
            path for path in candidates
            if os.path.basename(path) == preferred_name
        )
        if matches:
            return matches[0]
    return None


def safe_extract_zip(zip_path: str, destination: str) -> None:
    """Extract a ZIP without allowing paths to escape the bot directory."""
    destination_root = os.path.realpath(destination)
    with zipfile.ZipFile(zip_path, "r") as archive:
        for member in archive.infolist():
            member_path = os.path.realpath(
                os.path.join(destination_root, member.filename)
            )
            if os.path.commonpath((destination_root, member_path)) != destination_root:
                raise ValueError("ZIP contains an unsafe path.")
        archive.extractall(destination_root)


def install_dependencies(bot_folder: str, entry_file: str) -> tuple[bool, str]:
    """Install Python or Node dependencies for the detected bot entrypoint."""
    try:
        entry_path = os.path.join(bot_folder, entry_file)
        if entry_file.lower().endswith(".js"):
            package_file = os.path.join(os.path.dirname(entry_path), "package.json")
            if not os.path.exists(package_file):
                return True, ""
            node = shutil.which("npm")
            if not node:
                return False, "Node.js/npm is not installed on the server."
            result = subprocess.run(
                [node, "install", "--omit=dev"],
                cwd=os.path.dirname(entry_path),
                capture_output=True, text=True, timeout=180,
            )
            if result.returncode != 0:
                return False, (result.stderr or result.stdout)[-1500:]
            return True, ""

        req_file = os.path.join(bot_folder, "requirements.txt")
        if not os.path.exists(req_file):
            req_file = os.path.join(os.path.dirname(entry_path), "requirements.txt")
        venv_dir = os.path.join(bot_folder, ".venv")
        venv_python = bot_python_path(bot_folder)
        if not os.path.exists(venv_python):
            create_venv = subprocess.run(
                [PYTHON_PATH, "-m", "venv", venv_dir],
                capture_output=True, text=True, timeout=120,
            )
            if create_venv.returncode != 0:
                error = create_venv.stderr or create_venv.stdout
                return False, (
                    "Could not create the bot virtual environment. "
                    "Install Python with the venv module and try again.\n"
                    f"{error[:1000]}"
                )
        if not os.path.exists(req_file):
            return True, ""
        result = subprocess.run(
            [venv_python, "-m", "pip", "install", "-r", req_file, "--quiet"],
            capture_output=True, text=True, timeout=180,
        )
        if result.returncode != 0:
            return False, result.stderr[-1500:]
        return True, ""
    except subprocess.TimeoutExpired:
        return False, "Dependency installation timed out."
    except Exception as e:
        return False, str(e)


def install_requirements(bot_folder: str) -> tuple[bool, str]:
    """Backward-compatible wrapper used by older admin restart records."""
    entry_file = detect_entry_file(bot_folder) or "main.py"
    return install_dependencies(bot_folder, entry_file)


def list_bot_files(bot_folder: str) -> list[str]:
    try:
        files = []
        for root, dirs, filenames in os.walk(bot_folder):
            dirs[:] = [
                d for d in dirs
                if d not in {".venv", "node_modules", "__pycache__"}
            ]
            for filename in filenames:
                relative = os.path.relpath(
                    os.path.join(root, filename),
                    bot_folder,
                )
                if relative != "bot.log":
                    files.append(relative)
        return sorted(files)
    except Exception:
        return []


def safe_bot_file_path(bot_folder: str, filename: str) -> str | None:
    """Resolve a displayed bot file while preventing path traversal."""
    try:
        root = os.path.realpath(bot_folder)
        path = os.path.realpath(os.path.join(root, filename))
        if os.path.commonpath((root, path)) != root:
            return None
        return path
    except (OSError, ValueError):
        return None


def spawn_bot(bot_folder: str, entry_file: str = "main.py") -> subprocess.Popen:
    """
    Launch a sub-bot in its own console window so it runs independently.
    stdout/stderr are redirected to bot.log for Telegram log viewing.

    On Windows: CREATE_NEW_CONSOLE opens a visible terminal window per bot.
    The file handle redirect (via STARTF_USESTDHANDLES inside Popen) takes
    precedence, so all print() / logging output lands in bot.log as well.

    The child process inherits the host process settings and writes all output
    to bot.log without changing the sub-bot's source code.
    """
    log_path = os.path.join(bot_folder, "bot.log")
    log_file = open(log_path, "a", encoding="utf-8", errors="replace")

    flags = 0
    # CREATE_NEW_CONSOLE is only valid on Windows; skip on Linux/Replit preview
    if os.name == "nt":
        flags = subprocess.CREATE_NEW_CONSOLE

    entry_path = os.path.join(bot_folder, entry_file)
    if entry_file.lower().endswith(".js"):
        node = shutil.which("node")
        if not node:
            log_file.close()
            raise FileNotFoundError("Node.js is not installed on the server.")
        command = [node, os.path.basename(entry_path)]
    else:
        command = [bot_python_path(bot_folder), os.path.basename(entry_path)]

    proc = subprocess.Popen(
        command,
        cwd=os.path.dirname(entry_path),
        stdout=log_file,
        stderr=subprocess.STDOUT,
        creationflags=flags,
    )
    return proc


BOT_STATUS_CHECK_INTERVAL = 10


def get_bot_stop_reason(proc_info: dict) -> str:
    """Return a useful reason from the bot log when a process is no longer alive."""
    bot_folder = proc_info.get("folder", "")
    log_path = os.path.join(bot_folder, "bot.log") if bot_folder else ""

    if log_path and os.path.exists(log_path):
        try:
            with open(log_path, "r", encoding="utf-8", errors="replace") as log_file:
                log_file.seek(0, os.SEEK_END)
                log_file.seek(max(0, log_file.tell() - 2000))
                lines = [line.strip() for line in log_file.read().splitlines() if line.strip()]
            if lines:
                return f"Last log: {lines[-1][:700]}"
        except OSError:
            pass

    return "The process stopped unexpectedly or is no longer running."


async def notify_bot_status_change(
    bot: Bot,
    proc_info: dict,
    was_alive: bool,
    is_alive_now: bool,
) -> None:
    """Notify the bot owner and Admin after a tracked bot changes state."""
    bot_name = html.escape(str(proc_info.get("name", "Unknown Bot")))
    bot_pid = html.escape(str(proc_info.get("pid", "—")))
    checked_at = datetime.now().astimezone().strftime("%Y-%m-%d %H:%M:%S %Z")

    if was_alive and not is_alive_now:
        reason = html.escape(get_bot_stop_reason(proc_info))
        text = (
            "🔴 <b>Bot has stopped</b>\n\n"
            f"🤖 Bot: <code>{bot_name}</code>\n"
            f"🕒 Time: <code>{checked_at}</code>\n"
            f"🆔 PID: <code>{bot_pid}</code>\n"
            f"📌 Reason: {reason}"
        )
    elif not was_alive and is_alive_now:
        text = (
            "🟢 <b>Bot has started again</b>\n\n"
            f"🤖 Bot: <code>{bot_name}</code>\n"
            f"🕒 Time: <code>{checked_at}</code>\n"
            f"🆔 New PID: <code>{bot_pid}</code>"
        )
    else:
        return

    recipient_ids = {ADMIN_ID}
    try:
        recipient_ids.add(int(proc_info.get("user_id")))
    except (TypeError, ValueError):
        pass

    for recipient_id in recipient_ids:
        try:
            await bot.send_message(recipient_id, text, parse_mode="HTML")
        except Exception as exc:
            logger.warning(
                "Could not send bot status notification to %s: %s",
                recipient_id,
                exc,
            )


def stop_tracked_process(proc_info: dict) -> bool:
    """Terminate one tracked bot process and confirm that it stopped."""
    pid = proc_info.get("pid")
    if not pm.is_alive(pid):
        return True

    try:
        process = psutil.Process(pid)
        process.terminate()
        try:
            process.wait(timeout=5)
        except psutil.TimeoutExpired:
            process.kill()
            process.wait(timeout=5)
    except psutil.NoSuchProcess:
        return True
    except (psutil.AccessDenied, psutil.TimeoutExpired, OSError) as exc:
        logger.warning(
            "Could not stop expired-access bot %s (PID %s): %s",
            proc_info.get("name", "Unknown Bot"),
            pid,
            exc,
        )
        return False

    return not pm.is_alive(pid)


async def notify_deployment_access_expired(
    bot: Bot,
    user_id: int,
    expires_at: str,
    stopped_bot_names: list[str],
) -> None:
    """Notify the user and Admins after temporary deployment access expires."""
    expires_display = html.escape(str(expires_at)[:19].replace("T", " "))
    if stopped_bot_names:
        bot_lines = "\n".join(
            f"• <code>{html.escape(name)}</code>"
            for name in stopped_bot_names[:20]
        )
        if len(stopped_bot_names) > 20:
            bot_lines += f"\n• …and {len(stopped_bot_names) - 20} more"
        stopped_details = (
            f"🛑 <b>Stopped Bots ({len(stopped_bot_names)}):</b>\n"
            f"{bot_lines}"
        )
    else:
        stopped_details = "🛑 <b>Stopped Bots:</b> No running Bots were found."

    user_text = (
        "⛔ <b>ADD Access Expired</b>\n\n"
        f"⏳ Access expired at: <code>{expires_display}</code>\n"
        f"{stopped_details}\n\n"
        "Contact the Admin through <b>Support</b> to deploy again."
    )
    admin_text = (
        "⛔ <b>User ADD Access Expired</b>\n\n"
        f"🆔 User ID: <code>{user_id}</code>\n"
        f"⏳ Access expired at: <code>{expires_display}</code>\n"
        f"{stopped_details}"
    )

    recipient_ids = {user_id}
    recipient_ids.update(load_admin_ids())
    for recipient_id in recipient_ids:
        try:
            await bot.send_message(
                chat_id=recipient_id,
                text=user_text if recipient_id == user_id else admin_text,
                reply_markup=(
                    main_reply_keyboard(is_admin=False)
                    if recipient_id == user_id
                    else None
                ),
                parse_mode="HTML",
            )
        except Exception as exc:
            logger.warning(
                "Could not send expired ADD Access notification to %s: %s",
                recipient_id,
                exc,
            )


async def enforce_expired_deployment_access(bot: Bot) -> None:
    """Stop every tracked Bot once its owner's temporary ADD Access expires."""
    for user_id, record in load_deployment_access().items():
        if not isinstance(record, dict):
            continue
        if record.get("expiry_action_at") or not deployment_access_record_expired(record):
            continue
        try:
            user_id_int = int(user_id)
        except (TypeError, ValueError):
            continue

        proc_infos = pm.get_user_procs(user_id_int)
        failed_bots = []
        stopped_bot_names = []
        for proc_info in proc_infos:
            if not stop_tracked_process(proc_info):
                failed_bots.append(str(proc_info.get("name", "Unknown Bot")))
            else:
                stopped_bot_names.append(str(proc_info.get("name", "Unknown Bot")))

        # Retry on the next monitor tick if any process could not be stopped.
        if failed_bots:
            logger.error(
                "ADD Access expired for user %s, but these Bots are still running: %s",
                user_id,
                ", ".join(failed_bots),
            )
            continue

        for proc_info in proc_infos:
            pm.unregister(str(proc_info.get("name", "")))

        # Persist the action so a master-bot restart cannot send duplicate
        # notifications or repeat the shutdown.
        access = load_deployment_access()
        current_record = access.get(str(user_id))
        if not isinstance(current_record, dict):
            continue
        current_record["expiry_action_at"] = datetime.now().astimezone().isoformat()
        current_record["stopped_bot_names"] = stopped_bot_names
        save_deployment_access(access)

        await notify_deployment_access_expired(
            bot,
            user_id_int,
            str(record.get("expires_at", "—")),
            stopped_bot_names,
        )


async def notify_admins_user_started(message: Message, bot: Bot) -> None:
    """Send a detailed /start event to every configured admin."""
    user = message.from_user
    if user is None:
        return

    user_id = user.id
    user_data = get_user(user_id) or {}
    user_bots = get_user_bots(user_id)
    running_bots = sum(1 for item in user_bots if item.get("alive"))
    username = f"@{user.username}" if user.username else "—"
    full_name = " ".join(
        part for part in (user.first_name, user.last_name) if part
    ) or "—"
    limit = get_bot_limit(user_id)
    limit_text = "Unlimited" if limit is None else str(limit)
    expiry = user_data.get("hosting_expires_at") or "Unlimited"
    if expiry != "Unlimited":
        expiry = str(expiry)[:19].replace("T", " ")

    details = (
        "🟢 <b>User Started the Bot</b>\n\n"
        f"🆔 User ID: <code>{user_id}</code>\n"
        f"👤 Name: <b>{html.escape(full_name)}</b>\n"
        f"📛 Username: {html.escape(username)}\n"
        f"🌐 Language: <code>{html.escape(str(getattr(user, 'language_code', None) or '—'))}</code>\n"
        "\n"
        f"📅 Registered: <code>{html.escape(str(user_data.get('registered_at', '—')))}</code>\n"
        f"🚦 Status: <code>{'Blocked' if user_data.get('is_blocked') else 'Active'}</code>\n"
        f"⏳ Hosting Until: <code>{html.escape(expiry)}</code>\n"
        f"🎯 Bot Limit: <code>{html.escape(limit_text)}</code>\n"
        f"📦 Deployed Bots: <code>{len(user_bots)}</code>\n"
        f"🟢 Running Bots: <code>{running_bots}</code>"
    )

    # Fetch the new user's latest profile photo once and reuse it for every
    # admin. The details remain the caption so the photo and notification are
    # delivered as one consistently styled message.
    profile_photo: BufferedInputFile | None = None
    try:
        profile_photos = await bot.get_user_profile_photos(user_id, limit=1)
        if profile_photos.total_count and profile_photos.photos:
            largest_photo = profile_photos.photos[0][-1]
            photo_file = await bot.get_file(largest_photo.file_id)
            photo_buffer = io.BytesIO()
            await bot.download_file(photo_file.file_path, destination=photo_buffer)
            profile_photo = BufferedInputFile(
                photo_buffer.getvalue(),
                filename=f"profile_{user_id}.jpg",
            )
    except Exception:
        # Photo access can fail for deleted/private photos. Keep the
        # notification reliable with its text-only fallback.
        logger.exception("Could not fetch profile photo for user %s", user_id)

    for admin_id in load_admin_ids():
        try:
            if profile_photo is not None:
                await bot.send_photo(
                    chat_id=int(admin_id),
                    photo=profile_photo,
                    caption=details,
                    reply_markup=admin_reply_keyboard(),
                    parse_mode="HTML",
                )
            else:
                await bot.send_message(
                    chat_id=int(admin_id),
                    text=details,
                    reply_markup=admin_reply_keyboard(),
                    parse_mode="HTML",
                )
        except Exception:
            # An admin may have blocked the bot or not started it yet. If the
            # photo send itself fails, preserve the notification as text.
            if profile_photo is not None:
                try:
                    await bot.send_message(
                        chat_id=int(admin_id),
                        text=details,
                        reply_markup=admin_reply_keyboard(),
                        parse_mode="HTML",
                    )
                    continue
                except Exception:
                    pass
            logger.exception("Could not send start details to admin %s", admin_id)


async def monitor_bot_status(bot: Bot) -> None:
    """Regularly check tracked bot processes and notify on state changes."""
    previous_status: dict[str, bool] = {}

    try:
        while True:
            try:
                await enforce_expired_deployment_access(bot)
                tracked_processes = pm.get_all_procs()
                current_names = set()

                for proc_info in tracked_processes:
                    bot_name = str(proc_info.get("name", ""))
                    if not bot_name:
                        continue

                    current_names.add(bot_name)
                    current_alive = bool(proc_info.get("alive", False))
                    previous_alive = previous_status.get(bot_name)

                    # The first observation establishes the baseline and avoids
                    # duplicate notifications after the master bot restarts.
                    if previous_alive is not None and previous_alive != current_alive:
                        await notify_bot_status_change(
                            bot,
                            proc_info,
                            previous_alive,
                            current_alive,
                        )

                    previous_status[bot_name] = current_alive

                # Explicitly unregistered bots should no longer be monitored.
                for bot_name in set(previous_status) - current_names:
                    previous_status.pop(bot_name, None)
            except Exception:
                logger.exception("Bot status check failed; retrying.")

            await asyncio.sleep(BOT_STATUS_CHECK_INTERVAL)
    except asyncio.CancelledError:
        raise


async def _restore_main_menu(target: Message, text: str) -> None:
    is_admin_user = is_admin(target.from_user.id)
    await target.answer(text, reply_markup=main_reply_keyboard(is_admin=is_admin_user), parse_mode="HTML")


# ════════════════════════════════════════════════════════════════════════════════
# /start
# ════════════════════════════════════════════════════════════════════════════════

@router.message(CommandStart())
async def cmd_start(
    message: Message,
    state: FSMContext,
    bot: Bot,
    is_new_user: bool = False,
):
    await state.clear()
    if is_new_user:
        await notify_admins_user_started(message, bot)
    if not await ensure_user_channel_verified(message, bot):
        return
    is_admin_user = is_admin(message.from_user.id)
    await message.answer(
        "🤖 <b>Master Bot Manager V2</b>\n\nChoose an option from the menu:",
        reply_markup=main_reply_keyboard(is_admin=is_admin_user),
        parse_mode="HTML",
    )


# ════════════════════════════════════════════════════════════════════════════════
# Main Menu Reply Keyboard Buttons
# ════════════════════════════════════════════════════════════════════════════════

@router.message(StateFilter("*"), F.text == BTN_UPLOAD)
async def btn_upload_new(message: Message, state: FSMContext, bot: Bot):
    if not await ensure_user_channel_verified(message, bot):
        return
    if not deployment_is_allowed(message.from_user.id):
        await state.clear()
        await message.answer(
            "⛔ <b>Bot deployment is temporarily disabled by Admin.</b>\n\n"
            "🆘 If you want to deploy a Bot, please contact the Admin "
            "through <b>Support</b>.",
            reply_markup=deployment_disabled_keyboard(),
            parse_mode="HTML",
        )
        return
    if hosting_expired(message.from_user.id):
        await message.answer(
            "⏳ Your hosting time has expired. Contact the Admin to add more time.",
        )
        return
    await state.clear()
    await state.set_state(BotStates.waiting_for_zip)
    await message.answer(
        "𝐒𝐞𝐧𝐝 𝐲𝐨𝐮𝐫 𝐛𝐨𝐭 𝐟𝐢𝐥𝐞 𝐚𝐬 𝐚 𝐝𝐨𝐜𝐮𝐦𝐞𝐧𝐭.\n\n"
        "𝐀𝐜𝐜𝐞𝐩𝐭𝐞𝐝: <code>.zip</code> <code>.py</code> <code>.js</code>\n\n"
        "𝐄𝐧𝐭𝐫𝐲 𝐝𝐞𝐭𝐞𝐜𝐭𝐢𝐨𝐧:\n"
        "<code>bot.py</code>\n<code>main.py</code>\n"
        "<code>app.py</code>\n<code>index.js</code>\n\n"
        f"After sending the file, press <b>{html.escape(BTN_DONE)}</b>.",
        reply_markup=upload_reply_keyboard(),
        parse_mode="HTML",
    )


@router.message(StateFilter("*"), F.text == BTN_MYBOTS)
async def btn_my_bots(message: Message, state: FSMContext, bot: Bot):
    if not await ensure_user_channel_verified(message, bot):
        return
    current = await state.get_state()
    if current is not None:
        await state.clear()
        await _restore_main_menu(message, "⚠️ The previous action was cancelled.")

    user_bots = get_user_bots(message.from_user.id)
    if not user_bots:
        await message.answer(
            f"You have no tracked Bots.\nPress <b>{html.escape(BTN_UPLOAD)}</b> to add one.",
            parse_mode="HTML",
        )
        return
    await message.answer(
        f"🤖 <b>Your Bot List ({len(user_bots)}):</b>\nTap one to manage it:",
        reply_markup=mybots_keyboard(user_bots),
        parse_mode="HTML",
    )


@router.message(StateFilter("*"), F.text == BTN_PROFILE)
async def btn_my_profile(message: Message, state: FSMContext, bot: Bot):
    if not await ensure_user_channel_verified(message, bot):
        return
    await state.clear()

    user_id = message.from_user.id
    user_data = get_user(user_id) or {}
    user_bots = get_user_bots(user_id)
    running_bots = [bot for bot in user_bots if bot.get("alive")]
    stopped_bots = len(user_bots) - len(running_bots)

    user_name = message.from_user.full_name or "—"
    username = user_data.get("username") or message.from_user.username or ""
    username_text = f"@{username}" if username else "—"
    registered_at = user_data.get("registered_at", "—")
    if registered_at != "—":
        registered_at = f"{registered_at[:19].replace('T', ' ')} UTC"

    bot_limit = get_bot_limit(user_id)
    if bot_limit is None:
        limit_text = "Unlimited"
        remaining_text = "Unlimited"
    else:
        remaining = max(0, bot_limit - len(user_bots))
        limit_text = str(bot_limit)
        remaining_text = str(remaining)

    total_runtime_seconds = sum(
        get_bot_runtime_seconds(bot) for bot in running_bots
    )
    if user_data.get("is_blocked", False):
        status_text = "🚫 Blocked"
    else:
        status_text = "✅ Active"
    hosting_until = user_data.get("hosting_expires_at")
    hosting_text = (
        "Unlimited" if not hosting_until
        else hosting_until[:19].replace("T", " ")
    )

    bot_lines = []
    for bot in user_bots:
        bot_name = html.escape(str(bot.get("name", "Unknown Bot")))
        if bot.get("alive"):
            runtime = format_duration(get_bot_runtime_seconds(bot))
            bot_lines.append(f"<b>🟢 <code>{bot_name}</code> — {html.escape(runtime)}</b>")
        else:
            bot_lines.append(f"<b>🔴 <code>{bot_name}</code> — Stopped</b>")

    bot_details = "\n".join(bot_lines) if bot_lines else "<b>No tracked Bots.</b>"
    profile_text = (
        f"<b>{html.escape(BTN_PROFILE)} — My Profile</b>\n\n"
        f"<b>🧑 Name: {html.escape(user_name)}</b>\n"
        f"<b>📛 Username: <code>{html.escape(username_text)}</code></b>\n"
        f"<b>🆔 Telegram ID: <code>{user_id}</code></b>\n"
        f"<b>📅 Registration: <code>{html.escape(str(registered_at))}</code></b>\n"
        f"<b>📌 Status: {html.escape(status_text)}</b>\n\n"
        "<b>🤖 Bot Information</b>\n"
        f"<b>📦 Total Bots: {len(user_bots)}</b>\n"
        f"<b>🟢 Running: {len(running_bots)}</b>\n"
        f"<b>🔴 Stopped: {stopped_bots}</b>\n"
        f"<b>🎯 Bot Limit: {html.escape(str(limit_text))}</b>\n"
        f"<b>📊 Remaining: {html.escape(str(remaining_text))}</b>\n"
        f"<b>⏳ Hosting Until: {html.escape(hosting_text)}</b>\n"
        f"<b>⏱ Total Runtime: {html.escape(format_duration(total_runtime_seconds))}</b>\n\n"
        "<b>📋 Bot Runtime</b>\n"
        f"{bot_details}"
    )

    # Send the user's latest Telegram profile photo with the profile details as
    # one styled caption. If the account has no photo or Telegram rejects the
    # lookup, the profile text still appears normally.
    profile_sent_with_photo = False
    try:
        profile_photos = await bot.get_user_profile_photos(user_id, limit=1)
        if profile_photos.total_count and profile_photos.photos:
            largest_photo = profile_photos.photos[0][-1]
            photo_file = await bot.get_file(largest_photo.file_id)
            photo_buffer = io.BytesIO()
            await bot.download_file(photo_file.file_path, destination=photo_buffer)
            await message.answer_photo(
                BufferedInputFile(
                    photo_buffer.getvalue(),
                    filename=f"profile_{user_id}.jpg",
                ),
                caption=profile_text,
                reply_markup=main_reply_keyboard(is_admin=is_admin(user_id)),
                parse_mode="HTML",
            )
            profile_sent_with_photo = True
    except Exception:
        logger.debug("Could not load Telegram profile photo for user %s.", user_id)

    if not profile_sent_with_photo:
        await message.answer(
            profile_text,
            reply_markup=main_reply_keyboard(is_admin=is_admin(user_id)),
            parse_mode="HTML",
        )


@router.message(StateFilter("*"), F.text == BTN_DEPOSIT)
async def btn_deposit_from_user_keyboard(message: Message, state: FSMContext, bot: Bot):
    if not await ensure_user_channel_verified(message, bot):
        return
    await state.clear()
    wallets = get_active_wallets()
    if not wallets:
        await message.answer(
            "No deposit wallet is currently available. Please try again later or contact Support.",
            parse_mode="HTML",
        )
        return
    await message.answer(
        "💰 <b>Deposit</b>\n\nPlease select an active wallet:",
        reply_markup=active_wallets_keyboard(wallets),
        parse_mode="HTML",
    )


@router.message(StateFilter("*"), F.text == "❌ Cancel Deposit")
async def cancel_deposit_from_reply_keyboard(message: Message, state: FSMContext):
    await state.clear()
    await message.answer(
        "Deposit action cancelled.",
        reply_markup=main_reply_keyboard(is_admin=is_admin(message.from_user.id)),
        parse_mode="HTML",
    )


@router.message(StateFilter("*"), F.text == BTN_SUPPORT)
async def btn_support(message: Message, state: FSMContext):
    await state.clear()
    await message.answer(
        "🆘 <b>Support</b>\n\nOpen the support chat using the button below.",
        reply_markup=InlineKeyboardMarkup(
            inline_keyboard=[
                [
                    InlineKeyboardButton(
                        text="🆘 Open Support Chat",
                        url="https://t.me/Limonff143",
                    )
                ]
            ]
        ),
        parse_mode="HTML",
    )


def _format_deposit_amount(value: Any) -> str:
    try:
        amount = Decimal(str(value))
        rendered = format(amount, "f").rstrip("0").rstrip(".")
        return rendered or "0"
    except (InvalidOperation, ValueError, TypeError):
        return str(value)


def _wallet_display(wallet: dict) -> str:
    return (
        f"{html.escape(str(wallet.get('wallet_type', '—')))} — "
        f"{html.escape(str(wallet.get('name', '—')))}"
    )


def _deposit_notification_text(deposit: dict, status: str | None = None) -> str:
    effective_status = status or str(deposit.get("status", "Pending"))
    username = deposit.get("username") or "—"
    proof_type = str(deposit.get("proof_type") or deposit.get("proof_file_type") or "—")
    payment_number = (
        f"Payment Number: <code>{html.escape(str(deposit.get('payment_number') or '—'))}</code>\n"
        if deposit.get("wallet_type") in {"bKash", "Nagad"}
        else ""
    )
    return (
        "📥 <b>New Deposit Request</b>\n\n"
        f"Deposit ID: <code>{html.escape(str(deposit.get('id', '—')))}</code>\n"
        f"User ID: <code>{html.escape(str(deposit.get('user_id', '—')))}</code>\n"
        f"Username: {html.escape(str(username))}\n"
        f"Full Name: {html.escape(str(deposit.get('full_name') or '—'))}\n"
        f"Amount: <code>{html.escape(_format_deposit_amount(deposit.get('amount', '—')))}</code>\n"
        f"Wallet Type: {html.escape(str(deposit.get('wallet_type') or '—'))}\n"
        f"Wallet Name: {html.escape(str(deposit.get('wallet_name') or '—'))}\n"
        f"Wallet Identifier: <code>{html.escape(str(deposit.get('wallet_identifier_snapshot') or '—'))}</code>\n"
        f"{payment_number}"
        f"Transaction ID: <code>{html.escape(str(deposit.get('transaction_id') or '—'))}</code>\n"
        f"Proof Type: {html.escape(proof_type)}\n"
        f"Submitted: <code>{html.escape(str(deposit.get('created_at', '—')))}</code>\n"
        f"Status: <b>{html.escape(effective_status)}</b>"
    )


async def _callback_channel_allowed(callback: CallbackQuery, bot: Bot) -> bool:
    if is_admin(callback.from_user.id):
        return True
    verified, _ = await user_has_required_channel_membership(bot, callback.from_user.id)
    if not verified:
        await callback.answer("🔒 Channel verification is required.", show_alert=True)
    return verified


async def _show_deposit_entry(callback: CallbackQuery) -> None:
    wallets = get_active_wallets()
    if not wallets:
        await callback.message.edit_text(
            "No deposit wallet is currently available. Please try again later or contact Support.",
            parse_mode="HTML",
        )
        return
    await callback.message.edit_text(
        "💰 <b>Deposit</b>\n\nPlease select an active wallet.",
        reply_markup=None,
        parse_mode="HTML",
    )
    await callback.message.answer(
        "Please select an active wallet:",
        reply_markup=active_wallets_keyboard(wallets),
    )


@router.callback_query(F.data == "dep_open")
async def callback_open_deposit(callback: CallbackQuery, bot: Bot, state: FSMContext):
    if not await _callback_channel_allowed(callback, bot):
        return
    await state.clear()
    await callback.answer()
    await _show_deposit_entry(callback)


@router.callback_query(F.data.startswith("dep_user_wallet_"))
async def callback_select_deposit_wallet(callback: CallbackQuery, state: FSMContext, bot: Bot):
    if not await _callback_channel_allowed(callback, bot):
        return
    wallet_id = callback.data.removeprefix("dep_user_wallet_")
    wallet = load_wallets().get(wallet_id)
    if not isinstance(wallet, dict) or not wallet.get("active"):
        await callback.answer("This wallet is no longer available.", show_alert=True)
        await _show_deposit_entry(callback)
        return
    await state.clear()
    await state.update_data(wallet_id=wallet_id)
    identifier = html.escape(str(wallet.get("identifier", "—")))
    await callback.answer()
    await callback.message.edit_text(
        "💰 <b>Deposit Wallet</b>\n\n"
        f"Wallet Type: {html.escape(str(wallet.get('wallet_type', '—')))}\n"
        f"Wallet Name: {html.escape(str(wallet.get('name', '—')))}\n"
        f"Wallet Identifier:\n<code>{identifier}</code>",
        reply_markup=wallet_details_keyboard(wallet_id),
        parse_mode="HTML",
    )


@router.callback_query(F.data.startswith("dep_user_proof_again"))
async def callback_deposit_proof_again(callback: CallbackQuery, state: FSMContext):
    data = await state.get_data()
    wallet = load_wallets().get(str(data.get("wallet_id")))
    await state.set_state(BotStates.waiting_for_deposit_proof)
    await callback.answer()
    proof_prompt = (
        "📤 Send your payment proof screenshot/photo again."
        if isinstance(wallet, dict) and wallet.get("wallet_type") in {"bKash", "Nagad"}
        else "📤 Send your payment proof as a photo, document, or text message again."
    )
    await callback.message.edit_text(
        proof_prompt,
        reply_markup=deposit_cancel_keyboard(),
        parse_mode="HTML",
    )


@router.callback_query(F.data.startswith("dep_user_proof_"))
async def callback_start_deposit_proof(
    callback: CallbackQuery,
    state: FSMContext,
    bot: Bot,
):
    if not await _callback_channel_allowed(callback, bot):
        return
    wallet_id = callback.data.removeprefix("dep_user_proof_")
    wallet = load_wallets().get(wallet_id)
    if not isinstance(wallet, dict) or not wallet.get("active"):
        await callback.answer("This wallet is no longer available.", show_alert=True)
        return
    await state.clear()
    await state.update_data(wallet_id=wallet_id)
    await state.set_state(BotStates.waiting_for_deposit_proof)
    await callback.answer()
    proof_prompt = (
        "Send your payment proof screenshot/photo."
        if wallet.get("wallet_type") in {"bKash", "Nagad"}
        else "Send your payment proof as a photo, document, or text message."
    )
    await callback.message.edit_text(
        proof_prompt,
        reply_markup=deposit_cancel_keyboard(),
        parse_mode="HTML",
    )


@router.message(BotStates.waiting_for_deposit_amount, F.text)
async def receive_deposit_amount(message: Message, state: FSMContext):
    raw = (message.text or "").strip().replace(",", "")
    try:
        amount = Decimal(raw)
    except (InvalidOperation, ValueError):
        amount = Decimal("0")
    if amount <= 0 or not amount.is_finite():
        await message.answer(
            "❌ Amount must be a valid positive number. Please try again:",
            reply_markup=deposit_cancel_keyboard(),
        )
        return
    await state.update_data(amount=_format_deposit_amount(amount))
    await state.set_state(BotStates.waiting_for_deposit_transaction)
    await message.answer(
        "Send the transaction ID or payment reference. Press Skip if unavailable.",
        reply_markup=deposit_transaction_keyboard(),
        parse_mode="HTML",
    )


async def _move_to_deposit_proof(message: Message, state: FSMContext, transaction_id: str):
    transaction_id = transaction_id.strip()
    if transaction_id:
        normalized = _normalized_unique_value(transaction_id)
        duplicate = any(
            _normalized_unique_value(item.get("transaction_id")) == normalized
            for item in load_deposits().values()
            if isinstance(item, dict) and item.get("transaction_id")
        )
        if duplicate:
            await message.answer(
                "This transaction ID has already been used. Please enter a different "
                "transaction ID or press Skip.",
                reply_markup=deposit_transaction_keyboard(),
            )
            return
    await state.update_data(transaction_id=transaction_id)
    data = await state.get_data()
    wallet = load_wallets().get(str(data.get("wallet_id")))
    if not isinstance(wallet, dict):
        await state.clear()
        await message.answer("❌ The selected wallet is no longer available. Please try again.")
        return
    payment_number = (
        f"Payment Number: <code>{html.escape(str(data.get('payment_number') or '—'))}</code>\n"
        if wallet.get("wallet_type") in {"bKash", "Nagad"}
        else ""
    )
    await message.answer(
        "📋 <b>Deposit Summary</b>\n\n"
        f"Wallet: {_wallet_display(wallet)}\n"
        f"Wallet Identifier: <code>{html.escape(str(wallet.get('identifier') or '—'))}</code>\n"
        f"{payment_number}"
        f"Amount: <code>{html.escape(str(data.get('amount') or '—'))}</code>\n"
        f"Transaction ID: <code>{html.escape(str(transaction_id or '—'))}</code>\n"
        f"Payment Proof: {html.escape(str(data.get('proof_type') or 'Text').title())}",
        reply_markup=deposit_preview_keyboard(),
        parse_mode="HTML",
    )


@router.callback_query(F.data == "dep_user_tx_skip")
async def callback_skip_deposit_transaction(callback: CallbackQuery, state: FSMContext):
    await callback.answer()
    await _move_to_deposit_proof(callback.message, state, "")


@router.message(BotStates.waiting_for_deposit_transaction, F.text)
async def receive_deposit_transaction(message: Message, state: FSMContext):
    transaction_id = (message.text or "").strip()
    if len(transaction_id) > 200:
        await message.answer("❌ Transaction ID is too long. Please try again or press Skip.")
        return
    await _move_to_deposit_proof(message, state, transaction_id)


async def _save_deposit_proof(
    message: Message,
    state: FSMContext,
    file_id: str = "",
    file_type: str = "text",
    proof_text: str = "",
):
    data = await state.get_data()
    wallet = load_wallets().get(str(data.get("wallet_id")))
    if not isinstance(wallet, dict) or not wallet.get("active"):
        await state.clear()
        await message.answer("❌ The selected wallet is no longer active. Please try again.")
        return
    if wallet.get("wallet_type") in {"bKash", "Nagad"} and file_type != "photo":
        await message.answer(
            "For bKash and Nagad, please send a payment proof screenshot/photo.",
            reply_markup=deposit_cancel_keyboard(),
        )
        return
    await state.update_data(
        proof_file_id=file_id,
        proof_file_type=file_type,
        proof_type=file_type,
        proof_text=proof_text,
        photo_file_id=file_id if file_type == "photo" else "",
        document_file_id=file_id if file_type == "document" else "",
        user_note="",
    )
    if wallet.get("wallet_type") in {"bKash", "Nagad"}:
        await state.set_state(BotStates.waiting_for_deposit_sender_number)
        await message.answer(
            "Enter the payment sender number:",
            reply_markup=deposit_cancel_keyboard(),
        )
        return
    await state.set_state(BotStates.waiting_for_deposit_amount)
    await message.answer(
        "Enter the deposit amount:\n\nOnly a positive number is accepted.",
        reply_markup=deposit_cancel_keyboard(),
        parse_mode="HTML",
    )


@router.message(BotStates.waiting_for_deposit_sender_number, F.text)
async def receive_deposit_sender_number(message: Message, state: FSMContext):
    sender_number = (message.text or "").strip()
    if not sender_number or len(sender_number) > 50:
        await message.answer(
            "❌ Enter a valid payment sender number:",
            reply_markup=deposit_cancel_keyboard(),
        )
        return
    await state.update_data(payment_number=sender_number)
    await state.set_state(BotStates.waiting_for_deposit_amount)
    await message.answer(
        "Enter the deposit amount:\n\nOnly a positive number is accepted.",
        reply_markup=deposit_cancel_keyboard(),
        parse_mode="HTML",
    )


@router.message(BotStates.waiting_for_deposit_proof, F.photo)
async def receive_deposit_photo(message: Message, state: FSMContext):
    if not message.photo:
        await message.answer("Please send a payment proof message, photo, or document.")
        return
    await _save_deposit_proof(message, state, message.photo[-1].file_id, "photo")


@router.message(BotStates.waiting_for_deposit_proof, F.document)
async def receive_deposit_document(message: Message, state: FSMContext):
    await _save_deposit_proof(message, state, message.document.file_id, "document")


@router.message(BotStates.waiting_for_deposit_proof, F.text)
async def receive_deposit_text_proof(message: Message, state: FSMContext):
    proof_text = (message.text or "").strip()
    if not proof_text:
        await message.answer("Please send a payment proof message, photo, or document.")
        return
    data = await state.get_data()
    wallet = load_wallets().get(str(data.get("wallet_id")))
    if isinstance(wallet, dict) and wallet.get("wallet_type") in {"bKash", "Nagad"}:
        await message.answer(
            "For bKash and Nagad, please send a payment proof screenshot/photo.",
            reply_markup=deposit_cancel_keyboard(),
        )
        return
    await _save_deposit_proof(message, state, proof_text=proof_text)


@router.message(BotStates.waiting_for_deposit_proof)
async def reject_invalid_deposit_proof(message: Message):
    await message.answer(
        "Please send a payment proof message, photo, or document.",
        reply_markup=deposit_cancel_keyboard(),
    )


async def _send_deposit_to_admins(bot: Bot, deposit: dict) -> None:
    caption = _deposit_notification_text(deposit)
    for admin_id in load_admin_ids():
        try:
            if deposit.get("proof_file_type") == "photo":
                await bot.send_photo(
                    chat_id=int(admin_id),
                    photo=deposit["proof_file_id"],
                    caption=caption,
                    reply_markup=admin_notification_keyboard(deposit["id"]),
                    parse_mode="HTML",
                )
            elif deposit.get("proof_file_type") == "document":
                await bot.send_document(
                    chat_id=int(admin_id),
                    document=deposit["proof_file_id"],
                    caption=caption,
                    reply_markup=admin_notification_keyboard(deposit["id"]),
                    parse_mode="HTML",
                )
            else:
                proof_text = html.escape(str(deposit.get("proof_text") or "—"))
                await bot.send_message(
                    chat_id=int(admin_id),
                    text=f"{caption}\n\n<b>Payment Proof:</b>\n{proof_text}",
                    reply_markup=admin_notification_keyboard(deposit["id"]),
                    parse_mode="HTML",
                )
        except Exception:
            logger.exception("Could not send deposit %s to admin %s", deposit.get("id"), admin_id)


@router.callback_query(F.data == "dep_user_submit")
async def callback_submit_deposit(callback: CallbackQuery, state: FSMContext, bot: Bot):
    data = await state.get_data()
    wallet = load_wallets().get(str(data.get("wallet_id")))
    if not isinstance(wallet, dict) or not wallet.get("active"):
        await state.clear()
        await callback.answer("This wallet is no longer active.", show_alert=True)
        return
    if not data.get("amount") or not (
        data.get("proof_file_id") or data.get("proof_text")
    ):
        await callback.answer("The deposit session is incomplete. Please try again.", show_alert=True)
        return
    deposit_id = _new_record_id("d")
    user = callback.from_user
    deposit = {
        "id": deposit_id,
        "user_id": user.id,
        "username": f"@{user.username}" if user.username else "",
        "full_name": user.full_name or "",
        "wallet_id": wallet["id"],
        "wallet_type": wallet.get("wallet_type", ""),
        "wallet_name": wallet.get("name", ""),
        "wallet_identifier_snapshot": wallet.get("identifier", ""),
        "amount": data["amount"],
        "payment_number": data.get("payment_number", ""),
        "transaction_id": data.get("transaction_id", ""),
        "proof_text": data.get("proof_text", ""),
        "photo_file_id": data.get("photo_file_id", ""),
        "document_file_id": data.get("document_file_id", ""),
        "proof_type": data.get("proof_type", data.get("proof_file_type", "text")),
        "proof_file_id": data["proof_file_id"],
        "proof_file_type": data.get("proof_file_type", "document"),
        "user_note": data.get("user_note", ""),
        "status": "Pending",
        "created_at": _utc_now(),
        "reviewed_at": None,
        "reviewed_by": None,
        "admin_review_note": "",
        "rejection_reason": "",
    }
    deposits = load_deposits()
    deposits[deposit_id] = deposit
    try:
        save_deposits(deposits)
    except (OSError, TypeError, ValueError):
        logger.exception("Could not save deposit %s", deposit_id)
        await callback.answer("Database save error. Please try again.", show_alert=True)
        return
    await state.clear()
    await callback.answer("Deposit submitted.")
    await callback.message.edit_text(
        "✅ <b>Deposit request submitted</b>\n\n"
        f"Deposit ID: <code>{html.escape(deposit_id)}</code>\n"
        "You will be notified after the admin reviews it.",
        parse_mode="HTML",
    )
    await _send_deposit_to_admins(bot, deposit)


@router.callback_query(F.data == "dep_user_cancel")
async def callback_cancel_user_deposit(callback: CallbackQuery, state: FSMContext):
    await state.clear()
    await callback.answer("Cancelled")
    await callback.message.edit_text(
        "Deposit action cancelled.",
        reply_markup=user_panel_inline_keyboard(),
        parse_mode="HTML",
    )


@router.callback_query(F.data == "verify_required_channels")
async def callback_verify_required_channels(callback: CallbackQuery, bot: Bot):
    if is_admin(callback.from_user.id):
        verified, missing = True, []
    else:
        verified, missing = await user_has_required_channel_membership(
            bot,
            callback.from_user.id,
        )

    if not verified:
        await callback.answer(
            "❌ You have not joined all required Channels yet.",
            show_alert=True,
        )
        if callback.message:
            await callback.message.edit_reply_markup(
                reply_markup=channel_verification_keyboard(missing),
            )
        return

    if callback.message:
        await callback.message.edit_text(
            "✅ <b>Membership verified successfully.</b>\n\n"
            "You can now use the User Panel.",
            parse_mode="HTML",
        )
        await callback.message.answer(
            "🏠 <b>User Panel</b>",
            reply_markup=main_reply_keyboard(is_admin=False),
            parse_mode="HTML",
        )
    await callback.answer("✅ Verified.")


# ════════════════════════════════════════════════════════════════════════════════
# Upload Flow  (waiting_for_zip state)
# ════════════════════════════════════════════════════════════════════════════════

@router.message(BotStates.waiting_for_zip, F.text == BTN_CANCEL)
async def btn_cancel_upload(message: Message, state: FSMContext):
    data = await state.get_data()
    upload_path = data.get("upload_path") or data.get("zip_path")
    if upload_path:
        try:
            os.remove(upload_path)
        except OSError:
            pass
    await state.clear()
    await _restore_main_menu(message, "❌ Upload was cancelled.")


@router.message(BotStates.waiting_for_zip, F.document)
async def handle_zip_upload(message: Message, state: FSMContext, bot: Bot):
    if not await ensure_user_channel_verified(message, bot):
        await state.clear()
        return
    if not deployment_is_allowed(message.from_user.id):
        await state.clear()
        await message.answer(
            "⛔ <b>Bot deployment is temporarily disabled by Admin.</b>\n\n"
            "🆘 If you want to deploy a Bot, please contact the Admin "
            "through <b>Support</b>.",
            reply_markup=deployment_disabled_keyboard(),
            parse_mode="HTML",
        )
        return
    document = message.document
    filename = os.path.basename(document.file_name or "")
    extension = os.path.splitext(filename)[1].lower()
    if extension not in {".zip", ".py", ".js"}:
        await message.answer(
            "❌ Only <b>.zip</b>, <b>.py</b>, or <b>.js</b> files are allowed.",
            parse_mode="HTML",
        )
        return

    try:
        os.makedirs(TMP_DIR, exist_ok=True)
    except Exception as e:
        await message.answer(
            f"❌ Could not create the temporary folder:\n<code>{html.escape(str(e))}</code>",
            parse_mode="HTML",
        )
        return

    tmp_path = os.path.join(
        TMP_DIR,
        f"{message.from_user.id}_{int(time.time())}{extension}",
    )

    try:
        file_info   = await bot.get_file(document.file_id)
        destination = open(tmp_path, "wb")
        try:
            await bot.download_file(file_info.file_path, destination=destination)
        finally:
            destination.flush()
            destination.close()
    except Exception as e:
        try:
            os.remove(tmp_path)
        except OSError:
            pass
        await message.answer(f"❌ File Download Error:\n<code>{html.escape(str(e))}</code>", parse_mode="HTML")
        return

    await state.update_data(upload_path=tmp_path, upload_filename=filename)
    await message.answer(
        f"📦 <b>{html.escape(filename)}</b> received ✅\n\n"
        f"Now press <b>{html.escape(BTN_DONE)}</b>.",
        parse_mode="HTML",
    )


@router.message(BotStates.waiting_for_zip, F.text == BTN_DONE)
async def btn_upload_done(message: Message, state: FSMContext, bot: Bot):
    if not await ensure_user_channel_verified(message, bot):
        await state.clear()
        return
    if not deployment_is_allowed(message.from_user.id):
        data = await state.get_data()
        upload_path = data.get("upload_path") or data.get("zip_path")
        if upload_path:
            try:
                os.remove(upload_path)
            except OSError:
                pass
        await state.clear()
        await message.answer(
            "⛔ <b>Bot deployment is temporarily disabled by Admin.</b>\n\n"
            "🆘 If you want to deploy a Bot, please contact the Admin "
            "through <b>Support</b>.",
            reply_markup=deployment_disabled_keyboard(),
            parse_mode="HTML",
        )
        return
    data     = await state.get_data()
    upload_path = data.get("upload_path") or data.get("zip_path")
    upload_filename = data.get("upload_filename", "uploaded file")
    if not upload_path or not os.path.exists(upload_path):
        await message.answer("❌ Send a bot file first!")
        return

    user_id    = message.from_user.id
    if hosting_expired(user_id):
        await message.answer(
            "⏳ Your hosting time has expired. Contact the Admin to add more time.",
        )
        return
    bot_limit  = get_bot_limit(user_id)
    current_bot_count = len(get_user_bots(user_id))
    if bot_limit is not None and current_bot_count >= bot_limit:
        await message.answer(
            f"⛔ Your Bot limit has been reached.\n"
            f"📊 Current: <b>{current_bot_count}</b> / <b>{bot_limit}</b>\n\n"
            "Contact the Admin to start a new Bot.",
            parse_mode="HTML",
        )
        return

    timestamp  = int(time.time())
    bot_name   = f"bot_{user_id}_{timestamp}"
    bot_folder = os.path.join(BOTS_BASE_DIR, f"{user_id}_{timestamp}")

    status_msg = await message.answer("⏳ Processing... Please wait.")

    # ── 1. Create bot folder ───────────────────────────────────────────────────
    try:
        os.makedirs(bot_folder, exist_ok=True)
    except Exception as e:
        await status_msg.edit_text(
            f"❌ Could not create the folder:\n<code>{html.escape(str(e))}</code>",
            parse_mode="HTML",
        )
        await state.clear()
        await _restore_main_menu(message, "❌ The operation failed.")
        return

    # ── 2. Extract the ZIP or place a single source file ───────────────────────
    try:
        upload_extension = os.path.splitext(upload_filename)[1].lower()
        if upload_extension == ".zip":
            safe_extract_zip(upload_path, bot_folder)
        else:
            shutil.copy2(
                upload_path,
                os.path.join(bot_folder, os.path.basename(upload_filename)),
            )
    except zipfile.BadZipFile:
        shutil.rmtree(bot_folder, ignore_errors=True)
        await status_msg.edit_text("❌ The ZIP file is corrupt or invalid.")
        await state.clear()
        await _restore_main_menu(message, "❌ The operation failed.")
        return
    except Exception as e:
        shutil.rmtree(bot_folder, ignore_errors=True)
        await status_msg.edit_text(
            f"❌ Extract Error:\n<code>{html.escape(str(e))}</code>",
            parse_mode="HTML",
        )
        await state.clear()
        await _restore_main_menu(message, "❌ The operation failed.")
        return

    # ── 3. Detect the supported entrypoint ─────────────────────────────────────
    entry_file = detect_entry_file(bot_folder)
    if not entry_file:
        shutil.rmtree(bot_folder, ignore_errors=True)
        await status_msg.edit_text(
            "❌ No supported entry file was found.\n\n"
            "Use one of: <code>bot.py</code>, <code>main.py</code>, "
            "<code>app.py</code>, or <code>index.js</code>.",
            parse_mode="HTML",
        )
        await state.clear()
        await _restore_main_menu(message, "❌ The operation failed.")
        return

    # ── 4. Preserve the original ZIP for Admin download ───────────────────────
    source_zip_path = original_zip_path_from_name(bot_name)
    try:
        os.makedirs(ORIGINAL_ZIPS_DIR, exist_ok=True)
        if upload_extension == ".zip":
            shutil.copy2(upload_path, source_zip_path)
        else:
            with zipfile.ZipFile(source_zip_path, "w", zipfile.ZIP_DEFLATED) as archive:
                archive.write(
                    os.path.join(bot_folder, entry_file),
                    arcname=entry_file,
                )
    except Exception as e:
        shutil.rmtree(bot_folder, ignore_errors=True)
        await status_msg.edit_text(
            f"❌ Could not save the original file:\n<code>{html.escape(str(e))}</code>",
            parse_mode="HTML",
        )
        await state.clear()
        await _restore_main_menu(message, "❌ The operation failed.")
        return

    # ── 5. Install requirements ────────────────────────────────────────────────
    await status_msg.edit_text("⏳ Installing dependencies...")
    ok, err = install_dependencies(bot_folder, entry_file)
    if not ok:
        shutil.rmtree(bot_folder, ignore_errors=True)
        try:
            os.remove(source_zip_path)
        except OSError:
            pass
        await status_msg.edit_text(
            f"❌ Dependency installation failed:\n<code>{html.escape(str(err))}</code>",
            parse_mode="HTML",
        )
        await state.clear()
        await _restore_main_menu(message, "❌ The operation failed.")
        return

    # ── 6. Spawn the sub-bot with subprocess.Popen ────────────────────────────
    await status_msg.edit_text("⏳ Starting the Bot...")
    try:
        proc = spawn_bot(bot_folder, entry_file)
    except Exception as e:
        shutil.rmtree(bot_folder, ignore_errors=True)
        try:
            os.remove(source_zip_path)
        except OSError:
            pass
        await status_msg.edit_text(
            f"❌ Bot start error:\n<code>{html.escape(str(e))}</code>",
            parse_mode="HTML",
        )
        await state.clear()
        await _restore_main_menu(message, "❌ The operation failed.")
        return

    # ── 7. Register PID in active_processes.json ──────────────────────────────
    pm.register(bot_name, proc.pid, bot_folder, user_id, entry_file)

    await state.clear()
    try:
        os.remove(upload_path)
    except OSError:
        pass

    await status_msg.edit_text(
        f"🚀 <b>Bot started!</b>\n\n"
        f"🤖 Name:   <code>{bot_name}</code>\n"
        f"🔢 PID:    <code>{proc.pid}</code>\n"
        f"📂 Folder: <code>{html.escape(bot_folder)}</code>\n"
        f"📄 Entry:  <code>{html.escape(entry_file)}</code>\n"
        f"📋 Logs:   <code>bot.log</code> (use the View Logs button)\n"
        f"✅ Running",
        parse_mode="HTML",
    )
    await message.answer(
        "Use the buttons below to manage your Bot:",
        reply_markup=main_reply_keyboard(is_admin=is_admin(user_id)),
    )


@router.message(BotStates.waiting_for_zip, ~F.document)
async def handle_wrong_zip_input(message: Message):
    if message.text and (
        message.text.startswith("/")
        or message.text in (BTN_UPLOAD, BTN_MYBOTS, BTN_PROFILE, BTN_SUPPORT, BTN_DONE, BTN_CANCEL)
    ):
        return
    await message.answer(
        "❌ Send only one bot document: <b>.zip</b>, <b>.py</b>, or <b>.js</b>.",
        parse_mode="HTML",
    )


# ════════════════════════════════════════════════════════════════════════════════
# Inline Callbacks — Bot List & Navigation
# ════════════════════════════════════════════════════════════════════════════════

@router.callback_query(F.data == "back_bots")
async def callback_back_bots(callback: CallbackQuery):
    user_bots = get_user_bots(callback.from_user.id)
    if not user_bots:
        await callback.message.edit_text("You have no tracked Bots.")
        await callback.answer()
        return
    await callback.message.edit_text(
        f"🤖 <b>Your Bot List ({len(user_bots)}):</b>",
        reply_markup=mybots_keyboard(user_bots),
        parse_mode="HTML",
    )
    await callback.answer()


@router.callback_query(F.data.startswith("bot_info_"))
async def callback_bot_info(callback: CallbackQuery):
    bot_name = callback.data[len("bot_info_"):]
    user_id  = str(callback.from_user.id)
    if not bot_name.startswith(f"bot_{user_id}_"):
        await callback.answer("❌ This is not your Bot!", show_alert=True)
        return

    # Live status via psutil
    entry = get_tracked_bot(callback.from_user.id, bot_name)
    if entry:
        status = "🟢 Running" if entry["alive"] else "🔴 Stopped"
        pid_txt = str(entry["pid"])
    else:
        fallback_folder = get_tracked_bot_folder(callback.from_user.id, bot_name)
        if os.path.isdir(fallback_folder):
            status = "🔴 Stopped"
            pid_txt = "—"
        else:
            await callback.answer(
                "⚠️ This Bot record is stale. Refreshing your Bot list.",
                show_alert=True,
            )
            await callback.message.edit_text(
                "🤖 <b>Your Bot List</b>\n\n"
                "⚠️ This Bot is no longer available.",
                reply_markup=mybots_keyboard(get_user_bots(callback.from_user.id)),
                parse_mode="HTML",
            )
            return

    await callback.message.edit_text(
        f"🤖 <b>{html.escape(bot_name)}</b>\n\n"
        f"📌 Status: {status}\n"
        f"🔢 PID:    <code>{pid_txt}</code>\n\n"
        f"What would you like to do?",
        reply_markup=bot_action_keyboard(bot_name),
        parse_mode="HTML",
    )
    await callback.answer()


@router.callback_query(F.data.startswith("confirm_restart_bot_"))
async def callback_confirm_restart_user_bot(callback: CallbackQuery):
    """Show a confirmation prompt before restarting the selected Bot."""
    bot_name = callback.data[len("confirm_restart_bot_"):]
    user_id = callback.from_user.id
    user_id_text = str(user_id)

    if not bot_name.startswith(f"bot_{user_id_text}_"):
        await callback.answer("❌ This is not your Bot!", show_alert=True)
        return

    access_record = load_deployment_access().get(user_id_text)
    if (
        isinstance(access_record, dict)
        and deployment_access_record_expired(access_record)
    ):
        await callback.answer(
            "❌ Your ADD Access has expired. This Bot cannot be restarted.",
            show_alert=True,
        )
        return

    if get_tracked_bot(user_id, bot_name) is None:
        await callback.answer("❌ This Bot is no longer available.", show_alert=True)
        return

    await callback.message.edit_text(
        f"⚠️ <b>Restart this Bot?</b>\n\n"
        f"🤖 Bot: <code>{html.escape(bot_name)}</code>\n\n"
        "The current process will stop and start again.",
        reply_markup=user_restart_confirmation_keyboard(bot_name),
        parse_mode="HTML",
    )
    await callback.answer()


@router.callback_query(F.data.startswith("restart_bot_"))
async def callback_restart_user_bot(callback: CallbackQuery):
    """Restart only the Bot selected by its owner from My Bots."""
    bot_name = callback.data[len("restart_bot_"):]
    user_id = callback.from_user.id
    user_id_text = str(user_id)

    if not bot_name.startswith(f"bot_{user_id_text}_"):
        await callback.answer("❌ This is not your Bot!", show_alert=True)
        return

    access_record = load_deployment_access().get(user_id_text)
    if (
        isinstance(access_record, dict)
        and deployment_access_record_expired(access_record)
    ):
        await callback.answer(
            "❌ Your ADD Access has expired. This Bot cannot be restarted.",
            show_alert=True,
        )
        return

    selected = get_tracked_bot(user_id, bot_name)
    if selected is None:
        await callback.answer(
            "❌ This Bot is no longer available.",
            show_alert=True,
        )
        return

    await callback.answer("⏳ Restarting selected Bot...")
    status_msg = await callback.message.answer(
        f"⏳ Restarting <code>{html.escape(bot_name)}</code>...",
        parse_mode="HTML",
    )
    try:
        ok_count, fail_count, result_lines = _restart_process_records([selected])
        await status_msg.edit_text(
            _restart_summary(
                f"Restart completed for {bot_name}",
                ok_count,
                fail_count,
                result_lines,
            ),
            parse_mode="HTML",
        )
    except Exception as exc:
        await status_msg.edit_text(
            f"❌ Could not restart <code>{html.escape(bot_name)}</code>:\n"
            f"<code>{html.escape(str(exc))}</code>",
            parse_mode="HTML",
        )


# ════════════════════════════════════════════════════════════════════════════════
# View Logs — reads bot.log from the bot's folder
# ════════════════════════════════════════════════════════════════════════════════

@router.callback_query(F.data.startswith("view_logs_"))
async def callback_view_logs(callback: CallbackQuery):
    bot_name = callback.data[len("view_logs_"):]
    user_id  = str(callback.from_user.id)
    if not bot_name.startswith(f"bot_{user_id}_"):
        await callback.answer("❌ This is not your Bot!", show_alert=True)
        return

    await callback.answer("⏳ Loading logs...")

    bot_folder = get_tracked_bot_folder(callback.from_user.id, bot_name)
    log_path   = os.path.join(bot_folder, "bot.log")

    if not bot_folder or not os.path.exists(bot_folder):
        await callback.message.answer("❌ The Bot folder was not found.")
        return

    if not os.path.exists(log_path):
        await callback.message.answer(
            f"📋 <b>Logs — {html.escape(bot_name)}:</b>\n\n"
            "<i>⚠️ bot.log has not been created yet. The Bot may have just started.</i>",
            parse_mode="HTML",
            reply_markup=bot_action_keyboard(bot_name),
        )
        return

    try:
        with open(log_path, "r", encoding="utf-8", errors="replace") as f:
            content = f.read()

        # Show last 3500 chars so it fits in a Telegram message
        if not content.strip():
            display = "<i>⚠️ The log file is still empty.</i>"
        else:
            tail    = content[-3500:]
            display = f"<pre>{html.escape(tail)}</pre>"

        await callback.message.answer(
            f"📋 <b>Logs — {html.escape(bot_name)}:</b>\n\n{display}",
            parse_mode="HTML",
            reply_markup=bot_action_keyboard(bot_name),
        )
    except Exception as e:
        await callback.message.answer(
            f"❌ Could not read the log:\n<code>{html.escape(str(e))}</code>",
            parse_mode="HTML",
        )


# ════════════════════════════════════════════════════════════════════════════════
# View Files
# ════════════════════════════════════════════════════════════════════════════════

@router.callback_query(F.data.startswith("view_files_"))
async def callback_view_files(callback: CallbackQuery):
    bot_name   = callback.data[len("view_files_"):]
    user_id    = str(callback.from_user.id)
    if not bot_name.startswith(f"bot_{user_id}_"):
        await callback.answer("❌ This is not your Bot!", show_alert=True)
        return
    bot_folder = get_tracked_bot_folder(callback.from_user.id, bot_name)
    if not bot_folder or not os.path.exists(bot_folder):
        await callback.answer("❌ The Bot folder was not found.", show_alert=True)
        return
    files = list_bot_files(bot_folder)
    if not files:
        await callback.answer("❌ The folder is empty.", show_alert=True)
        return
    await callback.message.edit_text(
        f"📁 <b>{html.escape(bot_name)}</b>\nFiles ({len(files)}) — tap one to manage it:",
        reply_markup=files_keyboard(bot_name, files),
        parse_mode="HTML",
    )
    await callback.answer()


# ════════════════════════════════════════════════════════════════════════════════
# File Actions (Download / Replace)
# ════════════════════════════════════════════════════════════════════════════════

@router.callback_query(F.data.startswith("fi_"))
async def callback_file_info(callback: CallbackQuery):
    raw = callback.data[3:]
    if "|" not in raw:
        await callback.answer("❌ Invalid data.", show_alert=True)
        return
    bot_name, filename = raw.split("|", 1)
    user_id = str(callback.from_user.id)
    if not bot_name.startswith(f"bot_{user_id}_"):
        await callback.answer("❌ This is not your Bot!", show_alert=True)
        return
    await callback.message.edit_text(
        f"📄 <b>{html.escape(filename)}</b>\n\nWhat would you like to do?",
        reply_markup=file_action_keyboard(bot_name, filename),
        parse_mode="HTML",
    )
    await callback.answer()


@router.callback_query(F.data.startswith("dl_"))
async def callback_download_file(callback: CallbackQuery, bot: Bot):
    raw = callback.data[3:]
    if "|" not in raw:
        await callback.answer("❌ Invalid data.", show_alert=True)
        return
    bot_name, filename = raw.split("|", 1)
    user_id = str(callback.from_user.id)
    if not bot_name.startswith(f"bot_{user_id}_"):
        await callback.answer("❌ This is not your Bot!", show_alert=True)
        return
    bot_folder = get_tracked_bot_folder(callback.from_user.id, bot_name)
    file_path = safe_bot_file_path(bot_folder, filename)
    if not file_path:
        await callback.answer("❌ Invalid path.", show_alert=True)
        return
    if not os.path.exists(file_path):
        await callback.answer("❌ The file was not found.", show_alert=True)
        return
    await callback.answer("⏳ Sending the file...")
    try:
        with open(file_path, "rb") as f:
            data = f.read()
        await bot.send_document(
            chat_id=callback.from_user.id,
            document=BufferedInputFile(data, filename=filename),
            caption=f"📄 <b>{html.escape(filename)}</b>\n📂 {html.escape(bot_name)}",
            parse_mode="HTML",
        )
    except Exception as e:
        await callback.message.answer(
            f"❌ Could not send the file:\n<code>{html.escape(str(e))}</code>",
            parse_mode="HTML",
        )


@router.callback_query(F.data.startswith("rp_"))
async def callback_replace_trigger(callback: CallbackQuery, state: FSMContext):
    raw = callback.data[3:]
    if "|" not in raw:
        await callback.answer("❌ Invalid data.", show_alert=True)
        return
    bot_name, filename = raw.split("|", 1)
    user_id = str(callback.from_user.id)
    if not bot_name.startswith(f"bot_{user_id}_"):
        await callback.answer("❌ This is not your Bot!", show_alert=True)
        return
    bot_folder = get_tracked_bot_folder(callback.from_user.id, bot_name)
    await state.set_state(BotStates.waiting_for_replace_file)
    await state.update_data(
        replace_bot_name=bot_name,
        replace_filename=filename,
        replace_folder=bot_folder,
    )
    await callback.message.answer(
        f"📤 Send a new file to replace <b>{html.escape(filename)}</b>:",
        reply_markup=replace_reply_keyboard(),
        parse_mode="HTML",
    )
    await callback.answer()


# ════════════════════════════════════════════════════════════════════════════════
# Replace File — FSM (waiting_for_replace_file)
# ════════════════════════════════════════════════════════════════════════════════

@router.message(BotStates.waiting_for_replace_file, F.text == BTN_CANCEL_R)
async def btn_cancel_replace(message: Message, state: FSMContext):
    await state.clear()
    await _restore_main_menu(message, "❌ Replace was cancelled.")


@router.message(BotStates.waiting_for_replace_file, F.document)
async def handle_replace_file(message: Message, state: FSMContext, bot: Bot):
    data       = await state.get_data()
    bot_name   = data.get("replace_bot_name")
    filename   = data.get("replace_filename")
    bot_folder = data.get("replace_folder")

    if not all([bot_name, filename, bot_folder]):
        await message.answer("❌ Session data was lost. Please try again.")
        await state.clear()
        await _restore_main_menu(message, "❌ The operation failed.")
        return

    if not os.path.exists(bot_folder):
        await message.answer("❌ The Bot folder was not found.")
        await state.clear()
        await _restore_main_menu(message, "❌ The operation failed.")
        return

    dest_path = safe_bot_file_path(bot_folder, filename)
    if not dest_path:
        await message.answer("❌ Invalid file path.")
        await state.clear()
        await _restore_main_menu(message, "❌ The operation failed.")
        return

    try:
        os.makedirs(TMP_DIR, exist_ok=True)
    except Exception as e:
        await message.answer(
            f"❌ Could not create the temporary folder:\n<code>{html.escape(str(e))}</code>",
            parse_mode="HTML",
        )
        return

    tmp_path = os.path.join(TMP_DIR, f"replace_{message.from_user.id}_{int(time.time())}")

    try:
        file_info   = await bot.get_file(message.document.file_id)
        destination = open(tmp_path, "wb")
        try:
            await bot.download_file(file_info.file_path, destination=destination)
        finally:
            destination.flush()
            destination.close()
    except Exception as e:
        try:
            os.remove(tmp_path)
        except OSError:
            pass
        await message.answer(
            f"❌ Download Error:\n<code>{html.escape(str(e))}</code>",
            parse_mode="HTML",
        )
        return

    try:
        os.makedirs(os.path.dirname(dest_path), exist_ok=True)
        shutil.move(tmp_path, dest_path)
    except Exception as e:
        await message.answer(
            f"❌ Could not save the file:\n<code>{html.escape(str(e))}</code>",
            parse_mode="HTML",
        )
        try:
            os.remove(tmp_path)
        except OSError:
            pass
        return

    await state.clear()
    await message.answer(
        f"✅ <b>{html.escape(filename)}</b> was replaced successfully!\n\n"
        f"♻️ Restart the Bot to apply the changes.",
        reply_markup=main_reply_keyboard(is_admin=is_admin(message.from_user.id)),
        parse_mode="HTML",
    )


@router.message(BotStates.waiting_for_replace_file, ~F.document)
async def handle_wrong_replace_input(message: Message):
    if message.text and (
        message.text.startswith("/")
        or message.text in (BTN_UPLOAD, BTN_MYBOTS, BTN_PROFILE, BTN_SUPPORT, BTN_CANCEL_R)
    ):
        return
    await message.answer("❌ Send only one <b>file</b>.", parse_mode="HTML")


# ════════════════════════════════════════════════════════════════════════════════
# Delete Bot — kill PID + unregister + delete folder
# ════════════════════════════════════════════════════════════════════════════════

@router.callback_query(F.data.startswith("confirm_delete_bot_"))
async def callback_confirm_delete_bot(callback: CallbackQuery):
    """Show a confirmation prompt before permanently deleting a Bot."""
    bot_name = callback.data[len("confirm_delete_bot_"):]
    user_id = callback.from_user.id
    user_id_text = str(user_id)

    if not bot_name.startswith(f"bot_{user_id_text}_"):
        await callback.answer("❌ This is not your Bot!", show_alert=True)
        return

    if get_tracked_bot(user_id, bot_name) is None:
        await callback.answer("❌ This Bot is no longer available.", show_alert=True)
        return

    await callback.message.edit_text(
        f"⚠️ <b>Delete this Bot permanently?</b>\n\n"
        f"🤖 Bot: <code>{html.escape(bot_name)}</code>\n\n"
        "The process, tracked record, Bot files, and original ZIP will be deleted.",
        reply_markup=user_delete_confirmation_keyboard(bot_name),
        parse_mode="HTML",
    )
    await callback.answer()


@router.callback_query(F.data.startswith("delete_bot_"))
async def callback_stop_bot(callback: CallbackQuery):
    bot_name = callback.data[len("delete_bot_"):]
    user_id  = str(callback.from_user.id)
    if not bot_name.startswith(f"bot_{user_id}_"):
        await callback.answer("❌ This is not your Bot!", show_alert=True)
        return

    errors: list[str] = []

    # ── 1. Kill the process if alive ──────────────────────────────────────────
    procs = pm.get_user_procs(callback.from_user.id)
    entry = next((p for p in procs if p["name"] == bot_name), None)
    if entry and entry["alive"]:
        try:
            proc = psutil.Process(entry["pid"])
            proc.terminate()
            try:
                proc.wait(timeout=5)
            except psutil.TimeoutExpired:
                proc.kill()
        except (psutil.NoSuchProcess, psutil.AccessDenied) as e:
            errors.append(f"kill: {e}")

    # ── 2. Remove from tracking JSON ──────────────────────────────────────────
    pm.unregister(bot_name)

    # ── 3. Delete bot folder from disk ────────────────────────────────────────
    bot_folder = get_tracked_bot_folder(callback.from_user.id, bot_name)
    if bot_folder and os.path.exists(bot_folder):
        try:
            shutil.rmtree(bot_folder)
        except Exception as e:
            errors.append(f"rmtree: {e}")

    source_zip_path = original_zip_path_from_name(bot_name)
    if os.path.exists(source_zip_path):
        try:
            os.remove(source_zip_path)
        except Exception as e:
            errors.append(f"source_zip: {e}")

    if errors:
        result_text = (
            f"⚠️ Partially Deleted <code>{html.escape(bot_name)}</code>\n"
            + "\n".join(f"• {html.escape(str(e))}" for e in errors)
        )
    else:
        result_text = f"🗑 Deleted ✅ <code>{html.escape(bot_name)}</code>"

    await callback.message.edit_text(result_text, parse_mode="HTML")
    await callback.message.answer(
        "🏠 Main Menu:",
        reply_markup=main_reply_keyboard(is_admin=is_admin(callback.from_user.id)),
    )
    await callback.answer()

# ── admin_handlers.py ────────────────────────────────────────────────────────




admin_router = Router()

# ─── Button Text Constants ────────────────────────────────────────────────────
BTN_ADMIN_PANEL      = "🛡 Admin Panel"
BTN_DEPOSIT_SYSTEM   = "💰 Deposit System"
BTN_STATS            = "📊 System Stats"
BTN_BROADCAST        = "📢 Broadcast"
BTN_USERS            = "👥 User settings"
BTN_ADD_ADMIN_ENTRY  = "➕ ADD ADMIN"
BTN_BAN_UNBAN        = "🚫 Ban / Unban User"
BTN_ALL_USERS        = "📋 All Users & Excel"
BTN_BOTS             = "🤖 Active Bots"
BTN_RESTART          = "🔄 System Restart"
BTN_BACK_USER_MENU   = "🔙 Back to User Menu"
BTN_BOT_LIMIT        = "⚙️ Bot Limit"
BTN_USER_SETTING     = "⚙️ User Setting"
BTN_ZIP_DOWNLOAD     = "📥 User ZIP Download"
BTN_BACK_ADMIN_PANEL = "🔙 Back to Admin Panel"
BTN_SETTINGS         = "⚙️ Settings"
BTN_ADD_USER_LIMIT   = "👤 Add User Limit"
BTN_BACK_USER_SETTING = "🔙 Back"
BTN_BANNED_USERS     = "🚫 Banned Users"
BTN_CANCEL_ADD_LIMIT = "❌ Cancel Add Limit"
BTN_CANCEL_BROADCAST = "❌ Cancel Broadcast"
BTN_CANCEL_LOOKUP    = "❌ Cancel Lookup"
BTN_CANCEL_BOT_LIMIT = "❌ Cancel Bot Limit"
BTN_CANCEL_ZIP       = "❌ Cancel ZIP Download"
BTN_CANCEL_RESTART   = "❌ Cancel Restart"
BTN_DEPLOYMENT_ACCESS = "➕ ADD Access"
BTN_GRANT_DEPLOYMENT_ACCESS = "➕ Add Access"
BTN_ACCESS_LIST = "📋 Access List & Excel"
BTN_CANCEL_DEPLOYMENT_ACCESS = "❌ Cancel ADD Access"
BTN_BACK_DEPLOYMENT_ACCESS = "🔙 Back to ADD Access"
BTN_DEPLOYMENT_ACCESS_DURATION = "❌ Cancel ADD Access Duration"
BTN_CHANNEL_VERIFICATION = "📢 Channel Verification"
BTN_ADD_REQUIRED_CHANNEL = "➕ Add Required Channel"
BTN_CHANNEL_LIST_REMOVE = "📋 Channel List & Remove"
BTN_CANCEL_CHANNEL_ADD = "❌ Cancel Channel Add"
BTN_BACK_CHANNEL_VERIFICATION = "🔙 Back to Channel Verification"
BTN_DEPOSIT_ADD_WALLET = "➕ Add Wallet"
BTN_DEPOSIT_REMOVE_WALLET = "🗑 Remove Wallet"
BTN_DEPOSIT_PENDING = "📥 Deposit Pending"
BTN_DEPOSIT_BACK = "⬅ Back"


# ─── Admin FSM States ─────────────────────────────────────────────────────────

class AdminStates(StatesGroup):
    waiting_for_broadcast    = State()
    waiting_for_user_id      = State()
    waiting_for_default_bot_limit = State()
    waiting_for_zip_download_user_id = State()
    waiting_for_restart_user_id = State()
    waiting_for_add_limit_user_id = State()
    waiting_for_add_limit_duration = State()
    waiting_for_add_limit_bot_count = State()
    waiting_for_add_admin_id = State()
    waiting_for_remove_admin_id = State()
    waiting_for_deployment_access_user_id = State()
    waiting_for_deployment_access_duration = State()
    waiting_for_channel_name = State()
    waiting_for_channel_link = State()
    waiting_for_wallet_name = State()
    waiting_for_wallet_identifier = State()
    waiting_for_deposit_reject_reason = State()


# ─── Guard helpers ────────────────────────────────────────────────────────────

def _is_admin(user_id: int) -> bool:
    return is_admin(user_id)


def _is_master_admin(user_id: int) -> bool:
    return user_id == ADMIN_ID


async def _admin_only_msg(message: Message) -> bool:
    if not _is_admin(message.from_user.id):
        await message.answer("❌ Only the Admin can perform this action.")
        return False
    return True


async def _admin_only_cb(callback: CallbackQuery) -> bool:
    if not _is_admin(callback.from_user.id):
        await callback.answer("❌ Admin access required.", show_alert=True)
        return False
    return True


async def _master_only_msg(message: Message) -> bool:
    if not _is_master_admin(message.from_user.id):
        await message.answer("❌ Only the Master Admin can manage admins.")
        return False
    return True


# ─── Restore admin panel keyboard ────────────────────────────────────────────

async def _restore_admin_kb(target: Message, text: str) -> None:
    await target.answer(
        text,
        reply_markup=admin_reply_keyboard(),
        parse_mode="HTML",
    )


# ════════════════════════════════════════════════════════════════════════════════
# 🛡 Admin Panel — Entry
# ════════════════════════════════════════════════════════════════════════════════

@admin_router.message(StateFilter("*"), F.text == BTN_ADMIN_PANEL)
async def btn_admin_panel(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    await state.clear()
    await message.answer(
        "🛡 <b>Admin Panel</b>\n\nChoose an option below:",
        reply_markup=admin_reply_keyboard(),
        parse_mode="HTML",
    )


@admin_router.message(StateFilter("*"), F.text == BTN_DEPOSIT_SYSTEM)
async def btn_admin_deposit_system(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    await state.clear()
    await message.answer(
        "💰 <b>Deposit System</b>\n\nChoose an option:",
        reply_markup=deposit_admin_menu_keyboard(),
        parse_mode="HTML",
    )


@admin_router.message(StateFilter("*"), F.text == BTN_DEPOSIT_ADD_WALLET)
async def btn_admin_deposit_add_wallet_reply(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    await state.clear()
    await state.set_state(AdminStates.waiting_for_wallet_name)
    await state.update_data(wallet_add_step="type")
    await message.answer(
        "➕ <b>Add Wallet</b>\n\nFirst, select the wallet type:",
        reply_markup=deposit_wallet_type_keyboard(),
        parse_mode="HTML",
    )


@admin_router.message(StateFilter("*"), F.text == BTN_DEPOSIT_REMOVE_WALLET)
async def btn_admin_deposit_remove_wallet_reply(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    await state.clear()
    wallets = get_active_wallets()
    if not wallets:
        await message.answer(
            "🗑 <b>Remove Wallet</b>\n\nThere are no active wallets.",
            reply_markup=deposit_admin_menu_keyboard(),
            parse_mode="HTML",
        )
        return
    await state.update_data(deposit_reply_view="remove")
    await message.answer(
        "🗑 <b>Remove Wallet</b>\n\nSelect the wallet you want to remove:",
        reply_markup=wallet_remove_list_keyboard(wallets),
        parse_mode="HTML",
    )


@admin_router.message(StateFilter("*"), F.text == BTN_DEPOSIT_PENDING)
async def btn_admin_deposit_pending_reply(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    await state.clear()
    await _show_pending_deposits(message)


@admin_router.message(StateFilter("*"), F.text == BTN_DEPOSIT_BACK)
async def btn_admin_deposit_back_reply(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    data = await state.get_data()
    await state.clear()
    if data.get("deposit_reply_view") == "remove":
        await message.answer(
            "💰 <b>Deposit System</b>\n\nChoose an option:",
            reply_markup=deposit_admin_menu_keyboard(),
            parse_mode="HTML",
        )
        return
    await _restore_admin_kb(message, "🛡 <b>Admin Panel</b>")


async def _show_admin_deposit_menu(callback: CallbackQuery):
    await callback.message.edit_text(
        "💰 <b>Deposit System</b>\n\nChoose an option:",
        reply_markup=deposit_admin_menu_keyboard(),
        parse_mode="HTML",
    )


@admin_router.callback_query(F.data == "dep_admin_menu")
async def callback_admin_deposit_menu(callback: CallbackQuery, state: FSMContext):
    if not await _admin_only_cb(callback):
        return
    await state.clear()
    await callback.answer()
    await _show_admin_deposit_menu(callback)


@admin_router.callback_query(F.data == "dep_admin_back")
async def callback_admin_deposit_back(callback: CallbackQuery, state: FSMContext):
    if not await _admin_only_cb(callback):
        return
    await state.clear()
    await callback.answer()
    await callback.message.edit_text(
        "🛡 <b>Admin Panel</b>\n\nDeposit System closed.",
        reply_markup=None,
        parse_mode="HTML",
    )
    await callback.message.answer(
        "🛡 <b>Admin Panel</b>",
        reply_markup=admin_reply_keyboard(),
        parse_mode="HTML",
    )


@admin_router.callback_query(F.data == "dep_admin_cancel")
async def callback_admin_deposit_cancel(callback: CallbackQuery, state: FSMContext):
    if not await _admin_only_cb(callback):
        return
    await state.clear()
    await callback.answer("Cancelled")
    await _show_admin_deposit_menu(callback)


@admin_router.callback_query(F.data == "dep_admin_add_wallet")
async def callback_admin_add_wallet(callback: CallbackQuery, state: FSMContext):
    if not await _admin_only_cb(callback):
        return
    await state.clear()
    await state.set_state(AdminStates.waiting_for_wallet_name)
    await state.update_data(wallet_add_step="type")
    await callback.answer()
    await callback.message.edit_text(
        "➕ <b>Add Wallet</b>\n\nFirst, select the wallet type:",
        reply_markup=deposit_wallet_type_keyboard(),
        parse_mode="HTML",
    )


@admin_router.callback_query(F.data.startswith("dep_admin_type_"))
async def callback_admin_wallet_type(callback: CallbackQuery, state: FSMContext):
    if not await _admin_only_cb(callback):
        return
    type_key = callback.data.removeprefix("dep_admin_type_")
    type_labels = {
        "bkash": "bKash",
        "nagad": "Nagad",
        "binance": "Binance",
        "other": "Other",
    }
    wallet_type = type_labels.get(type_key)
    if not wallet_type:
        await callback.answer("Invalid wallet type.", show_alert=True)
        return
    await state.update_data(wallet_type=wallet_type)
    await state.set_state(AdminStates.waiting_for_wallet_name)
    await callback.answer()
    await callback.message.edit_text(
        f"Wallet type: <b>{html.escape(wallet_type)}</b>\n\n"
        "Send the wallet name or display name:",
        reply_markup=None,
        parse_mode="HTML",
    )


@admin_router.message(AdminStates.waiting_for_wallet_name, F.text)
async def receive_admin_wallet_name(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    name = (message.text or "").strip()
    if name == "/cancel":
        await state.clear()
        await _restore_admin_kb(message, "Wallet setup was cancelled.")
        return
    data = await state.get_data()
    if not data.get("wallet_type"):
        await message.answer("Please select the wallet type first.", reply_markup=deposit_wallet_type_keyboard())
        return
    if not name or len(name) > 100:
        await message.answer("❌ Wallet name must be between 1 and 100 characters.")
        return
    await state.update_data(wallet_name=name)
    await state.set_state(AdminStates.waiting_for_wallet_identifier)
    await message.answer(
        "Enter the wallet number, UID, address, or payment identifier:\n"
        "A bKash/Nagad mobile number, Binance UID/address, or payment address.\n\n"
        "Send /cancel to stop.",
        reply_markup=None,
        parse_mode="HTML",
    )


@admin_router.message(AdminStates.waiting_for_wallet_identifier, F.text)
async def receive_admin_wallet_identifier(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    identifier = (message.text or "").strip()
    if identifier == "/cancel":
        await state.clear()
        await _restore_admin_kb(message, "Wallet setup was cancelled.")
        return
    if not identifier or len(identifier) > 250:
        await message.answer("❌ Wallet identifier must be between 1 and 250 characters.")
        return
    await state.update_data(wallet_identifier=identifier)
    await _show_wallet_add_confirmation(message, state)


async def _show_wallet_add_confirmation(target: Message, state: FSMContext):
    data = await state.get_data()
    await target.answer(
        "📋 <b>Confirm Wallet</b>\n\n"
        f"Wallet Type: {html.escape(str(data.get('wallet_type', '—')))}\n"
        f"Wallet Name: {html.escape(str(data.get('wallet_name', '—')))}\n"
        f"Wallet Identifier: <code>{html.escape(str(data.get('wallet_identifier', '—')))}</code>",
        reply_markup=wallet_add_confirmation_keyboard(),
        parse_mode="HTML",
    )


@admin_router.callback_query(F.data == "dep_admin_add_edit")
async def callback_admin_wallet_edit(callback: CallbackQuery, state: FSMContext):
    if not await _admin_only_cb(callback):
        return
    await state.clear()
    await state.set_state(AdminStates.waiting_for_wallet_name)
    await callback.answer()
    await callback.message.edit_text(
        "Select the wallet type again:",
        reply_markup=deposit_wallet_type_keyboard(),
        parse_mode="HTML",
    )


@admin_router.callback_query(F.data == "dep_admin_add_confirm")
async def callback_admin_wallet_add_confirm(callback: CallbackQuery, state: FSMContext):
    if not await _admin_only_cb(callback):
        return
    data = await state.get_data()
    name = str(data.get("wallet_name", "")).strip()
    identifier = str(data.get("wallet_identifier", "")).strip()
    wallets = load_wallets()
    duplicate = next(
        (
            wallet for wallet in wallets.values()
            if isinstance(wallet, dict)
            and (
                _normalized_unique_value(wallet.get("name")) == _normalized_unique_value(name)
                or _normalized_unique_value(wallet.get("identifier")) == _normalized_unique_value(identifier)
            )
        ),
        None,
    )
    if duplicate:
        await callback.answer("This wallet name or identifier already exists.", show_alert=True)
        await callback.message.answer(
            "❌ The same wallet name or identifier cannot be added more than once.",
            reply_markup=deposit_admin_menu_keyboard(),
        )
        await state.clear()
        return
    wallet_id = _new_record_id("w")
    wallets[wallet_id] = {
        "id": wallet_id,
        "wallet_type": data.get("wallet_type", "Other"),
        "name": name,
        "identifier": identifier,
        "active": True,
        "created_at": _utc_now(),
        "created_by": callback.from_user.id,
        "updated_at": _utc_now(),
    }
    try:
        save_wallets(wallets)
    except (OSError, TypeError, ValueError):
        logger.exception("Could not save wallet %s", wallet_id)
        await callback.answer("Wallet save error.", show_alert=True)
        return
    await state.clear()
    await callback.answer("Wallet added.")
    await callback.message.edit_text(
        "✅ <b>Wallet successfully added.</b>\n\n"
        f"Wallet ID: <code>{html.escape(wallet_id)}</code>",
        reply_markup=None,
        parse_mode="HTML",
    )
    await callback.message.answer(
        "💰 <b>Deposit System</b>\n\nChoose an option:",
        reply_markup=deposit_admin_menu_keyboard(),
        parse_mode="HTML",
    )


@admin_router.callback_query(F.data == "dep_admin_remove_wallet")
async def callback_admin_remove_wallet(callback: CallbackQuery, state: FSMContext):
    if not await _admin_only_cb(callback):
        return
    await state.clear()
    await state.update_data(deposit_reply_view="remove")
    wallets = get_active_wallets()
    await callback.answer()
    if not wallets:
        await callback.message.edit_text(
            "🗑 <b>Remove Wallet</b>\n\nThere are no active wallets.",
            reply_markup=None,
            parse_mode="HTML",
        )
        await callback.message.answer(
            "💰 <b>Deposit System</b>\n\nChoose an option:",
            reply_markup=deposit_admin_menu_keyboard(),
            parse_mode="HTML",
        )
        return
    await callback.message.edit_text(
        "🗑 <b>Remove Wallet</b>\n\nSelect the wallet you want to remove:",
        reply_markup=wallet_remove_list_keyboard(wallets),
        parse_mode="HTML",
    )


@admin_router.callback_query(F.data.startswith("dep_admin_remove_select_"))
async def callback_admin_remove_select(callback: CallbackQuery):
    if not await _admin_only_cb(callback):
        return
    wallet_id = callback.data.removeprefix("dep_admin_remove_select_")
    wallet = load_wallets().get(wallet_id)
    if not isinstance(wallet, dict) or not wallet.get("active"):
        await callback.answer("This wallet is no longer active.", show_alert=True)
        return
    await callback.answer()
    await callback.message.edit_text(
        "Do you want to remove this wallet?\n\n"
        f"Wallet Type: {html.escape(str(wallet.get('wallet_type', '—')))}\n"
        f"Wallet Name: {html.escape(str(wallet.get('name', '—')))}\n"
        f"Wallet Identifier: <code>{html.escape(str(wallet.get('identifier', '—')))}</code>",
        reply_markup=wallet_remove_confirmation_keyboard(wallet_id),
        parse_mode="HTML",
    )


@admin_router.callback_query(F.data.startswith("dep_admin_remove_confirm_"))
async def callback_admin_remove_confirm(callback: CallbackQuery):
    if not await _admin_only_cb(callback):
        return
    wallet_id = callback.data.removeprefix("dep_admin_remove_confirm_")
    wallets = load_wallets()
    wallet = wallets.get(wallet_id)
    if not isinstance(wallet, dict) or not wallet.get("active"):
        await callback.answer("Wallet already removed.", show_alert=True)
        return
    wallet["active"] = False
    wallet["updated_at"] = _utc_now()
    wallet["removed_at"] = _utc_now()
    wallet["removed_by"] = callback.from_user.id
    try:
        save_wallets(wallets)
    except (OSError, TypeError, ValueError):
        logger.exception("Could not remove wallet %s", wallet_id)
        await callback.answer("Wallet update error.", show_alert=True)
        return
    await callback.answer("Wallet removed.")
    await callback.message.edit_text(
        "✅ The wallet has been deactivated. Previous deposit history is preserved.",
        reply_markup=None,
        parse_mode="HTML",
    )
    await callback.message.answer(
        "💰 <b>Deposit System</b>\n\nChoose an option:",
        reply_markup=deposit_admin_menu_keyboard(),
        parse_mode="HTML",
    )


def _admin_notifications_keyboard(page: int, total_pages: int) -> InlineKeyboardMarkup:
    navigation = []
    if page > 0:
        navigation.append(InlineKeyboardButton(text="⬅ Previous", callback_data=f"dep_admin_notifications_page_{page - 1}"))
    if page + 1 < total_pages:
        navigation.append(InlineKeyboardButton(text="Next ➡", callback_data=f"dep_admin_notifications_page_{page + 1}"))
    rows = [navigation] if navigation else []
    rows.append([InlineKeyboardButton(text="⬅ Back", callback_data="dep_admin_back")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


async def _show_pending_deposits(source: CallbackQuery | Message, page: int = 0):
    callback = source if isinstance(source, CallbackQuery) else None
    message = callback.message if callback else source
    pending = get_pending_deposits()
    page_size = 5
    total_pages = max(1, (len(pending) + page_size - 1) // page_size)
    page = max(0, min(page, total_pages - 1))
    start = page * page_size
    current = pending[start:start + page_size]
    if not current:
        if callback:
            await message.edit_text(
                "There are currently no pending deposit requests.",
                reply_markup=None,
                parse_mode="HTML",
            )
            await message.answer(
                "💰 <b>Deposit System</b>\n\nChoose an option:",
                reply_markup=deposit_admin_menu_keyboard(),
                parse_mode="HTML",
            )
        else:
            await message.answer(
                "There are currently no pending deposit requests.",
                reply_markup=deposit_admin_menu_keyboard(),
                parse_mode="HTML",
            )
        return
    summary = (
        f"📥 <b>Pending Deposits</b> ({len(pending)})\n"
        f"Page {page + 1}/{total_pages}\n\n"
        "Review the proof and actions for each request below."
    )
    if callback:
        await message.edit_text(
            summary,
            reply_markup=_admin_notifications_keyboard(page, total_pages),
            parse_mode="HTML",
        )
    else:
        await message.answer(
            summary,
            reply_markup=_admin_notifications_keyboard(page, total_pages),
            parse_mode="HTML",
        )
    for deposit in current:
        caption = _deposit_notification_text(deposit)
        try:
            if deposit.get("proof_file_type") == "photo":
                await message.answer_photo(
                    deposit.get("proof_file_id"),
                    caption=caption,
                    reply_markup=admin_notification_keyboard(deposit["id"]),
                    parse_mode="HTML",
                )
            elif deposit.get("proof_file_type") == "document" and deposit.get("proof_file_id"):
                await message.answer_document(
                    deposit.get("proof_file_id"),
                    caption=caption,
                    reply_markup=admin_notification_keyboard(deposit["id"]),
                    parse_mode="HTML",
                )
            else:
                await message.answer(
                    caption
                    + "\n\n<b>Payment Proof:</b>\n"
                    + html.escape(str(deposit.get("proof_text") or "—")),
                    reply_markup=admin_notification_keyboard(deposit["id"]),
                    parse_mode="HTML",
                )
        except Exception:
            logger.exception("Could not display pending deposit %s", deposit.get("id"))


@admin_router.callback_query(F.data == "dep_admin_notifications")
async def callback_admin_notifications(callback: CallbackQuery):
    if not await _admin_only_cb(callback):
        return
    await callback.answer()
    await _show_pending_deposits(callback)


@admin_router.callback_query(F.data.startswith("dep_admin_notifications_page_"))
async def callback_admin_notifications_page(callback: CallbackQuery):
    if not await _admin_only_cb(callback):
        return
    try:
        page = int(callback.data.removeprefix("dep_admin_notifications_page_"))
    except ValueError:
        page = 0
    await callback.answer()
    await _show_pending_deposits(callback, page)


async def _edit_admin_deposit_message(message: Message, deposit: dict, status: str):
    text = _deposit_notification_text(deposit, status)
    try:
        if message.photo or message.document:
            await message.edit_caption(caption=text, reply_markup=None, parse_mode="HTML")
        else:
            await message.edit_text(text, reply_markup=None, parse_mode="HTML")
    except Exception:
        logger.exception("Could not update admin deposit message %s", deposit.get("id"))


@admin_router.callback_query(
    F.data.startswith("dep_admin_approve_")
    & ~F.data.startswith("dep_admin_approve_confirm_")
)
async def callback_admin_approve_deposit(callback: CallbackQuery):
    if not await _admin_only_cb(callback):
        return
    deposit_id = callback.data.removeprefix("dep_admin_approve_")
    deposit = load_deposits().get(deposit_id)
    if not isinstance(deposit, dict) or deposit.get("status") != "Pending":
        await callback.answer("This deposit is no longer pending.", show_alert=True)
        return
    await callback.answer()
    await callback.message.edit_reply_markup(reply_markup=admin_deposit_decision_keyboard(deposit_id, "Approve"))


@admin_router.callback_query(F.data.startswith("dep_admin_approve_confirm_"))
async def callback_admin_approve_confirm(callback: CallbackQuery, bot: Bot):
    if not await _admin_only_cb(callback):
        return
    deposit_id = callback.data.removeprefix("dep_admin_approve_confirm_")
    deposits = load_deposits()
    deposit = deposits.get(deposit_id)
    if not isinstance(deposit, dict) or deposit.get("status") != "Pending":
        await callback.answer("This deposit has already been reviewed.", show_alert=True)
        return
    deposit.update({
        "status": "Approved",
        "reviewed_at": _utc_now(),
        "reviewed_by": callback.from_user.id,
        "admin_review_note": "Approved",
    })
    try:
        save_deposits(deposits)
    except (OSError, TypeError, ValueError):
        logger.exception("Could not approve deposit %s", deposit_id)
        await callback.answer("Deposit update error.", show_alert=True)
        return
    await callback.answer("Approved.")
    await _edit_admin_deposit_message(callback.message, deposit, "Approved")
    try:
        await bot.send_message(
            chat_id=int(deposit["user_id"]),
            text=(
                "✅ Your deposit has been approved.\n\n"
                f"Deposit ID: <code>{html.escape(deposit_id)}</code>\n"
                f"Amount: <code>{html.escape(_format_deposit_amount(deposit.get('amount')))}</code>\n"
                f"Wallet: {_wallet_display(deposit)}\n"
                f"Wallet Identifier: <code>{html.escape(str(deposit.get('wallet_identifier_snapshot') or '—'))}</code>"
            ),
            parse_mode="HTML",
        )
    except Exception:
        logger.exception("Could not notify user %s about approved deposit %s", deposit.get("user_id"), deposit_id)


@admin_router.callback_query(
    F.data.startswith("dep_admin_reject_")
    & ~F.data.startswith("dep_admin_reject_confirm_")
)
async def callback_admin_reject_deposit(callback: CallbackQuery):
    if not await _admin_only_cb(callback):
        return
    deposit_id = callback.data.removeprefix("dep_admin_reject_")
    deposit = load_deposits().get(deposit_id)
    if not isinstance(deposit, dict) or deposit.get("status") != "Pending":
        await callback.answer("This deposit is no longer pending.", show_alert=True)
        return
    await callback.answer()
    await callback.message.edit_reply_markup(reply_markup=admin_reject_reason_keyboard(deposit_id))


@admin_router.callback_query(F.data.startswith("dep_admin_reason_"))
async def callback_admin_reject_reason(callback: CallbackQuery, state: FSMContext):
    if not await _admin_only_cb(callback):
        return
    payload = callback.data.removeprefix("dep_admin_reason_")
    id_marker = payload.find("_d_")
    if id_marker == -1:
        await callback.answer("Invalid deposit reference.", show_alert=True)
        return
    reason_key = payload[:id_marker]
    deposit_id = payload[id_marker + 1:]
    labels = {
        "proof_unclear": "Payment proof is unclear",
        "amount_mismatch": "Amount does not match",
        "transaction_unverified": "Transaction could not be verified",
        "wrong_wallet": "Payment sent to the wrong wallet",
    }
    if reason_key == "other":
        await state.set_state(AdminStates.waiting_for_deposit_reject_reason)
        await state.update_data(reject_deposit_id=deposit_id)
        await callback.answer()
        await callback.message.answer(
            "Enter the reason for rejecting this deposit:",
            reply_markup=deposit_cancel_keyboard(f"dep_admin_notification_back_{deposit_id}"),
        )
        return
    reason = labels.get(reason_key, "Other")
    await callback.answer()
    await callback.message.edit_reply_markup(
        reply_markup=admin_deposit_decision_keyboard(deposit_id, "Reject")
    )
    await state.update_data(reject_deposit_id=deposit_id, reject_reason=reason)


@admin_router.message(AdminStates.waiting_for_deposit_reject_reason, F.text)
async def receive_admin_reject_reason(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    reason = (message.text or "").strip()
    if not reason or len(reason) > 500:
        await message.answer("❌ Reason must be between 1 and 500 characters.")
        return
    data = await state.get_data()
    deposit_id = data.get("reject_deposit_id")
    await state.update_data(reject_reason=reason)
    await message.answer(
        f"Reject reason: <b>{html.escape(reason)}</b>\n\nDo you want to confirm?",
        reply_markup=admin_deposit_decision_keyboard(str(deposit_id), "Reject"),
        parse_mode="HTML",
    )


@admin_router.callback_query(F.data.startswith("dep_admin_reject_confirm_"))
async def callback_admin_reject_confirm(callback: CallbackQuery, state: FSMContext, bot: Bot):
    if not await _admin_only_cb(callback):
        return
    deposit_id = callback.data.removeprefix("dep_admin_reject_confirm_")
    data = await state.get_data()
    reason = str(data.get("reject_reason") or "Other")
    deposits = load_deposits()
    deposit = deposits.get(deposit_id)
    if not isinstance(deposit, dict) or deposit.get("status") != "Pending":
        await callback.answer("This deposit has already been reviewed.", show_alert=True)
        await state.clear()
        return
    deposit.update({
        "status": "Rejected",
        "reviewed_at": _utc_now(),
        "reviewed_by": callback.from_user.id,
        "admin_review_note": reason,
        "rejection_reason": reason,
    })
    try:
        save_deposits(deposits)
    except (OSError, TypeError, ValueError):
        logger.exception("Could not reject deposit %s", deposit_id)
        await callback.answer("Deposit update error.", show_alert=True)
        return
    await state.clear()
    await callback.answer("Rejected.")
    await _edit_admin_deposit_message(callback.message, deposit, "Rejected")
    try:
        await bot.send_message(
            chat_id=int(deposit["user_id"]),
            text=(
                "❌ Your deposit request has been rejected.\n\n"
                f"Deposit ID: <code>{html.escape(deposit_id)}</code>\n"
                f"Amount: <code>{html.escape(_format_deposit_amount(deposit.get('amount')))}</code>\n"
                f"Wallet: {_wallet_display(deposit)}\n"
                f"Reason: {html.escape(reason)}"
            ),
            parse_mode="HTML",
        )
    except Exception:
        logger.exception("Could not notify user %s about rejected deposit %s", deposit.get("user_id"), deposit_id)


@admin_router.callback_query(F.data.startswith("dep_admin_details_"))
async def callback_admin_deposit_details(callback: CallbackQuery):
    if not await _admin_only_cb(callback):
        return
    deposit_id = callback.data.removeprefix("dep_admin_details_")
    deposit = load_deposits().get(deposit_id)
    if not isinstance(deposit, dict):
        await callback.answer("Deposit ID was not found.", show_alert=True)
        return
    await callback.answer()
    await callback.message.answer(
        _deposit_notification_text(deposit)
        + f"\nWallet identifier snapshot: <code>{html.escape(str(deposit.get('wallet_identifier_snapshot', '—')))}</code>\n"
        + f"User note: {html.escape(str(deposit.get('user_note') or '—'))}",
        parse_mode="HTML",
    )


@admin_router.callback_query(F.data.startswith("dep_admin_notification_back_"))
async def callback_admin_deposit_notification_back(callback: CallbackQuery, state: FSMContext):
    if not await _admin_only_cb(callback):
        return
    deposit_id = callback.data.removeprefix("dep_admin_notification_back_")
    deposit = load_deposits().get(deposit_id)
    await state.clear()
    if not isinstance(deposit, dict):
        await callback.answer("Deposit ID was not found.", show_alert=True)
        return
    await callback.answer()
    await callback.message.edit_reply_markup(reply_markup=admin_notification_keyboard(deposit_id))


@admin_router.message(StateFilter("*"), F.text.startswith("🚦 Deployment:"))
async def btn_toggle_deployment(message: Message, state: FSMContext, bot: Bot):
    if not await _master_only_msg(message):
        return

    enabled = not is_deployment_enabled()
    set_deployment_enabled(enabled)
    status_text = "ON" if enabled else "OFF"
    await state.clear()

    await message.answer(
        f"✅ <b>Bot Deployment is now {status_text}</b>.",
        reply_markup=admin_reply_keyboard(),
        parse_mode="HTML",
    )

    notification = (
        "✅ <b>Bot deployment is available again.</b>\n\n"
        "You can deploy a new Bot normally."
        if enabled
        else
        "⛔ <b>Bot deployment is temporarily disabled by Admin.</b>\n\n"
        "If you want to deploy a Bot, please contact the Admin "
        "through <b>Support</b>."
    )

    success = 0
    failed = 0
    for user_id in get_all_users():
        try:
            await bot.send_message(int(user_id), notification, parse_mode="HTML")
            success += 1
        except Exception:
            failed += 1

    await message.answer(
        f"📢 User notification completed.\n"
        f"✅ Sent: {success}\n"
        f"❌ Failed: {failed}",
        reply_markup=admin_reply_keyboard(),
    )


@admin_router.message(StateFilter("*"), F.text == BTN_SETTINGS)
async def btn_admin_settings(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    await state.clear()
    await message.answer(
        "⚙️ <b>Settings</b>\n\nChoose a setting below:",
        reply_markup=settings_reply_keyboard(),
        parse_mode="HTML",
    )


@admin_router.message(
    StateFilter("*"),
    F.text == BTN_ADD_USER_LIMIT,
)
async def btn_add_user_limit(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    await state.clear()
    await state.set_state(AdminStates.waiting_for_add_limit_user_id)
    await message.answer(
        "👤 Enter the specific User ID:",
        reply_markup=add_limit_cancel_reply_keyboard(),
    )


@admin_router.message(
    AdminStates.waiting_for_add_limit_user_id,
    F.text == BTN_CANCEL_ADD_LIMIT,
)
async def btn_cancel_add_limit(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    await state.clear()
    await message.answer(
        "❌ Add Limit was cancelled.",
        reply_markup=user_setting_reply_keyboard(),
    )


@admin_router.message(
    AdminStates.waiting_for_add_limit_user_id,
    F.text == BTN_BACK_USER_SETTING,
)
async def btn_back_user_setting(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    await state.clear()
    await message.answer(
        "⚙️ <b>User Setting</b>\n\nChoose a setting below:",
        reply_markup=user_setting_reply_keyboard(),
        parse_mode="HTML",
    )


@admin_router.message(AdminStates.waiting_for_add_limit_user_id, F.text)
async def handle_add_limit_user_id(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    raw = message.text.strip()
    if not raw.isdigit():
        await message.answer("❌ Enter a numeric User ID.")
        return
    target_id = int(raw)
    if not get_user(target_id):
        await message.answer(
            f"❌ <code>{target_id}</code> — this User is not in the database.",
            parse_mode="HTML",
        )
        return
    await state.update_data(add_limit_user_id=target_id)
    await state.set_state(AdminStates.waiting_for_add_limit_duration)
    await message.answer(
        f"⏳ How long should User <code>{target_id}</code> be allowed "
        "to deploy Bots?\n\n"
        "Format: <code>30m</code>, <code>12h</code>, <code>7d</code>, "
        "or <code>1month</code>.",
        reply_markup=add_limit_cancel_reply_keyboard(),
        parse_mode="HTML",
    )


@admin_router.message(
    AdminStates.waiting_for_add_limit_duration,
    F.text.in_({BTN_CANCEL_ADD_LIMIT, BTN_BACK_USER_SETTING}),
)
async def btn_cancel_add_limit_duration(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    await state.clear()
    await message.answer(
        "⚙️ <b>User Setting</b>\n\nChoose a setting below:",
        reply_markup=user_setting_reply_keyboard(),
        parse_mode="HTML",
    )


@admin_router.message(AdminStates.waiting_for_add_limit_duration, F.text)
async def handle_add_limit_duration(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return

    duration_seconds = parse_hosting_duration(message.text)
    if duration_seconds is None:
        await message.answer(
            "❌ Invalid duration. Use <code>30m</code>, <code>12h</code>, "
            "<code>7d</code>, or <code>1month</code>.",
            parse_mode="HTML",
        )
        return

    await state.update_data(add_limit_duration_seconds=duration_seconds)
    await state.set_state(AdminStates.waiting_for_add_limit_bot_count)
    await message.answer(
        f"🤖 How many additional Bots should User <code>"
        f"{(await state.get_data()).get('add_limit_user_id')}</code> be allowed "
        "to deploy?\n\nEnter a positive whole number, for example: <code>3</code>.",
        reply_markup=add_limit_cancel_reply_keyboard(),
        parse_mode="HTML",
    )


@admin_router.message(
    AdminStates.waiting_for_add_limit_bot_count,
    F.text.in_({BTN_CANCEL_ADD_LIMIT, BTN_BACK_USER_SETTING}),
)
async def btn_cancel_add_limit_bot_count(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    await state.clear()
    await message.answer(
        "⚙️ <b>User Setting</b>\n\nChoose a setting below:",
        reply_markup=user_setting_reply_keyboard(),
        parse_mode="HTML",
    )


@admin_router.message(AdminStates.waiting_for_add_limit_bot_count, F.text)
async def handle_add_limit_bot_count(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return

    raw_count = message.text.strip()
    if not raw_count.isdigit() or int(raw_count) <= 0:
        await message.answer(
            "❌ Enter a positive whole number for the additional Bot count."
        )
        return

    bot_limit_add = int(raw_count)
    data = await state.get_data()
    target_id = data.get("add_limit_user_id")
    duration_seconds = data.get("add_limit_duration_seconds")
    if not target_id or not isinstance(duration_seconds, int) or duration_seconds <= 0:
        await state.clear()
        await _restore_admin_kb(message, "❌ This Add User Limit session expired.")
        return

    success, new_limit, expiry = add_user_hosting_limit(
        target_id, duration_seconds, bot_limit_add
    )
    if not success:
        await state.clear()
        await _restore_admin_kb(message, "❌ User was not found.")
        return

    await state.clear()
    limit_text = "Unlimited" if new_limit is None else str(new_limit)
    await _restore_admin_kb(
        message,
        f"✅ User <code>{target_id}</code> limit updated.\n\n"
        f"➕ Additional Bots: <b>{bot_limit_add}</b>\n"
        f"🎯 Total Bot Limit: <b>{limit_text}</b>\n"
        f"⏳ Hosting Until: <code>{html.escape(expiry[:19].replace('T', ' '))}</code>",
    )


@admin_router.message(StateFilter("*"), F.text == BTN_ADD_ADMIN_ENTRY)
async def btn_admin_management(message: Message, state: FSMContext):
    if not await _master_only_msg(message):
        return
    await state.clear()
    await message.answer(
        "➕ <b>ADD ADMIN</b>\n\nChoose an option below:",
        reply_markup=admin_management_reply_keyboard(),
        parse_mode="HTML",
    )


@admin_router.message(StateFilter("*"), F.text == "📋 Admin List")
async def btn_admin_list(message: Message, state: FSMContext):
    if not await _master_only_msg(message):
        return
    await state.clear()
    admin_ids = sorted(load_admin_ids())
    lines = ["👑 <b>Admin List</b>", ""]
    for number, user_id in enumerate(admin_ids, start=1):
        role = " — Master Admin" if user_id == ADMIN_ID else ""
        lines.append(f"{number}. <code>{user_id}</code>{role}")
    await message.answer(
        "\n".join(lines),
        reply_markup=admin_management_reply_keyboard(),
        parse_mode="HTML",
    )


@admin_router.message(StateFilter("*"), F.text == "➕ Add Admin")
async def btn_add_admin(message: Message, state: FSMContext):
    if not await _master_only_msg(message):
        return
    await state.clear()
    await state.set_state(AdminStates.waiting_for_add_admin_id)
    await message.answer(
        "➕ Enter the numeric Telegram User ID to add as an Admin:",
        reply_markup=admin_management_cancel_reply_keyboard(),
    )


@admin_router.message(StateFilter("*"), F.text == "➖ Remove Admin")
async def btn_remove_admin(message: Message, state: FSMContext):
    if not await _master_only_msg(message):
        return
    await state.clear()
    await state.set_state(AdminStates.waiting_for_remove_admin_id)
    await message.answer(
        "➖ Enter the numeric Telegram User ID to remove from Admins:",
        reply_markup=admin_management_cancel_reply_keyboard(),
    )


@admin_router.message(
    AdminStates.waiting_for_add_admin_id,
    F.text.in_({"❌ Cancel Admin Action", "🔙 Back to ADD ADMIN"}),
)
@admin_router.message(
    AdminStates.waiting_for_remove_admin_id,
    F.text.in_({"❌ Cancel Admin Action", "🔙 Back to ADD ADMIN"}),
)
async def btn_cancel_admin_action(message: Message, state: FSMContext):
    if not await _master_only_msg(message):
        return
    await state.clear()
    await message.answer(
        "➕ <b>ADD ADMIN</b>\n\nChoose an option below:",
        reply_markup=admin_management_reply_keyboard(),
        parse_mode="HTML",
    )


@admin_router.message(AdminStates.waiting_for_add_admin_id, F.text)
async def handle_add_admin_id(message: Message, state: FSMContext):
    if not await _master_only_msg(message):
        return
    raw = message.text.strip()
    if not raw.isdigit():
        await message.answer("❌ Enter a numeric Telegram User ID.")
        return
    target_id = int(raw)
    if not add_admin(target_id):
        await message.answer(
            f"ℹ️ <code>{target_id}</code> is already an Admin.",
            parse_mode="HTML",
        )
        return
    await state.clear()
    await message.answer(
        f"✅ <code>{target_id}</code> has been added as an Admin.",
        reply_markup=admin_management_reply_keyboard(),
        parse_mode="HTML",
    )


@admin_router.message(AdminStates.waiting_for_remove_admin_id, F.text)
async def handle_remove_admin_id(message: Message, state: FSMContext):
    if not await _master_only_msg(message):
        return
    raw = message.text.strip()
    if not raw.isdigit():
        await message.answer("❌ Enter a numeric Telegram User ID.")
        return
    target_id = int(raw)
    if target_id == ADMIN_ID:
        await message.answer("❌ The Master Admin cannot be removed.")
        return
    if not remove_admin(target_id):
        await message.answer(
            f"ℹ️ <code>{target_id}</code> is not in the Admin list.",
            parse_mode="HTML",
        )
        return
    await state.clear()
    await message.answer(
        f"✅ <code>{target_id}</code> has been removed from Admins.",
        reply_markup=admin_management_reply_keyboard(),
        parse_mode="HTML",
    )


# ════════════════════════════════════════════════════════════════════════════════
# ⚙️ User Bot Limit — FSM
# ════════════════════════════════════════════════════════════════════════════════

@admin_router.message(StateFilter("*"), F.text == BTN_USER_SETTING)
async def btn_admin_user_setting(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    await state.clear()
    await message.answer(
        "⚙️ <b>User Setting</b>\n\nChoose a setting below:",
        reply_markup=user_setting_reply_keyboard(),
        parse_mode="HTML",
    )


@admin_router.message(StateFilter("*"), F.text == BTN_CHANNEL_VERIFICATION)
async def btn_channel_verification(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    await state.clear()
    await message.answer(
        "📢 <b>Channel Verification</b>\n\n"
        "Users must join every Channel/Group listed here before using the User Panel.",
        reply_markup=channel_management_reply_keyboard(),
        parse_mode="HTML",
    )


@admin_router.message(StateFilter("*"), F.text == BTN_ADD_REQUIRED_CHANNEL)
async def btn_add_required_channel(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    await state.clear()
    await state.set_state(AdminStates.waiting_for_channel_name)
    await message.answer(
        "📢 Enter the Channel/Group name:",
        reply_markup=channel_name_cancel_reply_keyboard(),
    )


@admin_router.message(
    AdminStates.waiting_for_channel_name,
    F.text.in_({BTN_CANCEL_CHANNEL_ADD, BTN_BACK_CHANNEL_VERIFICATION}),
)
async def cancel_channel_name(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    await state.clear()
    await message.answer(
        "📢 <b>Channel Verification</b>\n\nChoose an option below:",
        reply_markup=channel_management_reply_keyboard(),
        parse_mode="HTML",
    )


@admin_router.message(AdminStates.waiting_for_channel_name, F.text)
async def handle_channel_name(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    channel_name = message.text.strip()
    if not channel_name:
        await message.answer("❌ Channel name cannot be empty.")
        return
    await state.update_data(channel_name=channel_name)
    await state.set_state(AdminStates.waiting_for_channel_link)
    await message.answer(
        "🔗 Now send the Channel/Group link.\n\n"
        "Use a public link such as <code>https://t.me/your_channel</code>.",
        reply_markup=channel_link_cancel_reply_keyboard(),
        parse_mode="HTML",
    )


@admin_router.message(
    AdminStates.waiting_for_channel_link,
    F.text.in_({BTN_CANCEL_CHANNEL_ADD, BTN_BACK_CHANNEL_VERIFICATION}),
)
async def cancel_channel_link(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    await state.clear()
    await message.answer(
        "📢 <b>Channel Verification</b>\n\nChoose an option below:",
        reply_markup=channel_management_reply_keyboard(),
        parse_mode="HTML",
    )


@admin_router.message(AdminStates.waiting_for_channel_link, F.text)
async def handle_channel_link(
    message: Message,
    state: FSMContext,
    bot: Bot,
):
    if not await _admin_only_msg(message):
        return

    link = message.text.strip()
    match = re.fullmatch(
        r"(?:https?://)?t\.me/([A-Za-z0-9_]{5,})/?",
        link,
        re.IGNORECASE,
    )
    if link.startswith("@") and re.fullmatch(r"@[A-Za-z0-9_]{5,}", link):
        lookup = link
        public_link = f"https://t.me/{link[1:]}"
    elif match:
        lookup = f"@{match.group(1)}"
        public_link = f"https://t.me/{match.group(1)}"
    else:
        await message.answer(
            "❌ Invalid Channel/Group link.\n"
            "Send a public link like <code>https://t.me/your_channel</code>.",
            parse_mode="HTML",
        )
        return

    try:
        chat = await bot.get_chat(chat_id=lookup)
    except Exception as exc:
        await message.answer(
            "❌ Could not find this Channel/Group. Make sure the link is public "
            "and the Bot is an Admin in that chat.\n\n"
            f"<code>{html.escape(str(exc))}</code>",
            parse_mode="HTML",
        )
        return

    chat_type = getattr(chat.type, "value", chat.type)
    if str(chat_type).lower() not in {"channel", "group", "supergroup"}:
        await message.answer(
            "❌ The provided link is not a Telegram Channel/Group.\n"
            f"Detected type: <code>{html.escape(str(chat_type))}</code>",
            parse_mode="HTML",
        )
        return

    data = await state.get_data()
    channel_name = data.get("channel_name", "").strip()
    if not add_required_channel(chat.id, channel_name, public_link):
        await message.answer(
            f"ℹ️ This Channel is already in the required list.\n"
            f"🆔 ID: <code>{chat.id}</code>",
            parse_mode="HTML",
        )
        return

    await state.clear()
    await message.answer(
        f"✅ <b>Required Channel added.</b>\n\n"
        f"📢 Name: <b>{html.escape(channel_name)}</b>\n"
        f"🔗 Link: <code>{html.escape(public_link)}</code>\n"
        f"🆔 Channel ID: <code>{chat.id}</code>",
        reply_markup=channel_management_reply_keyboard(),
        parse_mode="HTML",
    )


@admin_router.message(StateFilter("*"), F.text == BTN_CHANNEL_LIST_REMOVE)
async def btn_channel_list_remove(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    await state.clear()
    channels = load_required_channels()
    if not channels:
        await message.answer(
            "📢 <b>Required Channel List</b>\n\n"
            "<i>No required Channels have been added.</i>",
            reply_markup=channel_management_reply_keyboard(),
            parse_mode="HTML",
        )
        return

    lines = ["📢 <b>Required Channel List</b>", f"Total: <b>{len(channels)}</b>", ""]
    for number, channel in enumerate(channels.values(), start=1):
        lines.append(
            f"{number}. 📢 <b>{html.escape(str(channel.get('name', 'Channel')))}</b>\n"
            f"   🆔 ID: <code>{channel.get('chat_id', '—')}</code>\n"
            f"   🔗 {html.escape(str(channel.get('link', '—')))}"
        )
    await message.answer(
        "\n".join(lines),
        reply_markup=required_channels_admin_keyboard(list(channels)),
        parse_mode="HTML",
    )


@admin_router.callback_query(F.data.startswith("remove_required_channel_"))
async def callback_remove_required_channel(callback: CallbackQuery):
    if not await _admin_only_cb(callback):
        return
    chat_id = callback.data[len("remove_required_channel_"):]
    if not chat_id.lstrip("-").isdigit():
        await callback.answer("❌ Invalid Channel ID.", show_alert=True)
        return
    if not remove_required_channel(chat_id):
        await callback.answer("ℹ️ This Channel was already removed.", show_alert=True)
        return

    channels = load_required_channels()
    if not channels:
        await callback.message.edit_text(
            "📢 <b>Required Channel List</b>\n\n"
            "<i>No required Channels have been added.</i>",
            parse_mode="HTML",
        )
    else:
        lines = [
            "📢 <b>Required Channel List</b>",
            f"Total: <b>{len(channels)}</b>",
            "",
        ]
        for number, channel in enumerate(channels.values(), start=1):
            lines.append(
                f"{number}. 📢 <b>{html.escape(str(channel.get('name', 'Channel')))}</b>\n"
                f"   🆔 ID: <code>{channel.get('chat_id', '—')}</code>\n"
                f"   🔗 {html.escape(str(channel.get('link', '—')))}"
            )
        await callback.message.edit_text(
            "\n".join(lines),
            reply_markup=required_channels_admin_keyboard(list(channels)),
            parse_mode="HTML",
        )
    await callback.answer(f"✅ Channel {chat_id} removed.")


@admin_router.message(StateFilter("*"), F.text == BTN_DEPLOYMENT_ACCESS)
async def btn_admin_deployment_access(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    await state.clear()
    await message.answer(
        "➕ <b>ADD Access</b>\n\n"
        "When global Deployment is OFF, only users listed here can deploy new Bots.",
        reply_markup=deployment_access_reply_keyboard(),
        parse_mode="HTML",
    )


@admin_router.message(StateFilter("*"), F.text == BTN_BACK_USER_SETTING)
async def btn_back_to_user_setting(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    await state.clear()
    await message.answer(
        "⚙️ <b>User Setting</b>\n\nChoose a setting below:",
        reply_markup=user_setting_reply_keyboard(),
        parse_mode="HTML",
    )


@admin_router.message(StateFilter("*"), F.text == BTN_GRANT_DEPLOYMENT_ACCESS)
async def btn_grant_deployment_access(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    await state.clear()
    await state.set_state(AdminStates.waiting_for_deployment_access_user_id)
    await message.answer(
        "➕ Enter the numeric User ID to grant ADD Access:",
        reply_markup=deployment_access_cancel_reply_keyboard(),
    )


@admin_router.message(StateFilter("*"), F.text == BTN_BACK_DEPLOYMENT_ACCESS)
async def btn_back_deployment_access(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    await state.clear()
    await message.answer(
        "➕ <b>ADD Access</b>\n\nChoose an option below:",
        reply_markup=deployment_access_reply_keyboard(),
        parse_mode="HTML",
    )


@admin_router.message(
    AdminStates.waiting_for_deployment_access_user_id,
    F.text.in_({BTN_CANCEL_DEPLOYMENT_ACCESS, BTN_BACK_DEPLOYMENT_ACCESS}),
)
async def btn_cancel_deployment_access(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    await state.clear()
    await message.answer(
        "➕ <b>ADD Access</b>\n\nChoose an option below:",
        reply_markup=deployment_access_reply_keyboard(),
        parse_mode="HTML",
    )


@admin_router.message(AdminStates.waiting_for_deployment_access_user_id, F.text)
async def handle_deployment_access_user_id(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return

    raw = message.text.strip()
    if not raw.isdigit():
        await message.answer("❌ Enter a numeric User ID.")
        return

    target_id = int(raw)
    user_data = get_user(target_id)
    if not user_data:
        await message.answer(
            f"❌ <code>{target_id}</code> — this User is not in the database.",
            parse_mode="HTML",
        )
        return

    if has_deployment_access(target_id):
        await message.answer(
            f"ℹ️ <code>{target_id}</code> already has ADD Access.",
            parse_mode="HTML",
        )
        return

    await state.update_data(deployment_access_user_id=target_id)
    await state.set_state(AdminStates.waiting_for_deployment_access_duration)
    await message.answer(
        f"⏳ How long should User <code>{target_id}</code> have ADD Access "
        "to host Bots?\n\n"
        "Format: <code>30m</code>, <code>12h</code>, <code>7d</code>, "
        "or <code>1month</code>.",
        reply_markup=deployment_access_cancel_reply_keyboard(),
        parse_mode="HTML",
    )


@admin_router.message(
    AdminStates.waiting_for_deployment_access_duration,
    F.text.in_({BTN_CANCEL_DEPLOYMENT_ACCESS, BTN_BACK_DEPLOYMENT_ACCESS}),
)
async def cancel_deployment_access_duration(
    message: Message,
    state: FSMContext,
):
    if not await _admin_only_msg(message):
        return
    await state.clear()
    await message.answer(
        "➕ <b>ADD Access</b>\n\nChoose an option below:",
        reply_markup=deployment_access_reply_keyboard(),
        parse_mode="HTML",
    )


@admin_router.message(
    AdminStates.waiting_for_deployment_access_duration,
    F.text,
)
async def handle_deployment_access_duration(
    message: Message,
    state: FSMContext,
    bot: Bot,
):
    if not await _admin_only_msg(message):
        return

    duration_seconds = parse_hosting_duration(message.text)
    if duration_seconds is None:
        await message.answer(
            "❌ Invalid format. Use <code>30m</code>, <code>12h</code>, "
            "<code>7d</code>, or <code>1month</code>.",
            parse_mode="HTML",
        )
        return

    data = await state.get_data()
    target_id = data.get("deployment_access_user_id")
    if not target_id or has_deployment_access(target_id):
        await state.clear()
        await _restore_admin_kb(message, "❌ This ADD Access session is no longer valid.")
        return

    # The requested duration extends the user's actual hosting expiry as well
    # as the temporary deployment permission.
    success, _new_limit, expires_at = add_user_hosting_limit(
        target_id,
        duration_seconds,
        0,
    )
    if not success or not grant_deployment_access(target_id, expires_at):
        await state.clear()
        await _restore_admin_kb(message, "❌ Could not grant ADD Access.")
        return

    await state.clear()
    user_data = get_user(target_id) or {}
    username = html.escape(str(user_data.get("username") or "—"))
    expires_display = html.escape(expires_at[:19].replace("T", " "))
    notification_sent = True
    try:
        await bot.send_message(
            chat_id=target_id,
            text=(
                "🎉 <b>ADD Access Granted</b>\n\n"
                "You can now deploy your Bot from the User Panel.\n"
                f"⏳ Access valid until: <code>{expires_display}</code>"
            ),
            reply_markup=main_reply_keyboard(is_admin=False),
            parse_mode="HTML",
        )
    except Exception:
        notification_sent = False
        logger.warning("Could not notify User %s about ADD Access.", target_id)

    await message.answer(
        f"✅ <b>ADD Access granted.</b>\n\n"
        f"🆔 User ID: <code>{target_id}</code>\n"
        f"📛 Username: @{username}\n"
        f"⏳ Hosting Until: <code>{expires_display}</code>\n"
        f"📨 User notification: {'Sent' if notification_sent else 'Could not be sent'}",
        reply_markup=deployment_access_reply_keyboard(),
        parse_mode="HTML",
    )


def deployment_access_report() -> tuple[str, list[int], bytes]:
    access = load_deployment_access()
    users = get_all_users()
    user_ids = sorted(int(uid) for uid in access if uid.isdigit())

    lines = [
        "➕ <b>ADD Access List</b>",
        f"Total: <b>{len(user_ids)}</b>",
        "",
    ]
    report_users = {}
    for number, user_id in enumerate(user_ids, start=1):
        uid = str(user_id)
        user = users.get(uid, {})
        username = user.get("username") or "—"
        record = access.get(uid, "—")
        if isinstance(record, dict):
            granted_at = record.get("granted_at", "—")
            expires_at = record.get("expires_at", "—")
        else:
            granted_at = record
            expires_at = "Unlimited (legacy access)"
        access_active = has_deployment_access(user_id)
        status = "Blocked" if user.get("is_blocked") else "Active"
        lines.extend([
            f"{number}. 🆔 <code>{user_id}</code>",
            f"   📛 Username: @{html.escape(str(username).lstrip('@'))}",
            f"   📌 User Status: {status}",
            f"   🚦 Access Status: {'Active' if access_active else 'Expired'}",
            f"   ✅ Access Granted: <code>{html.escape(str(granted_at)[:19].replace('T', ' '))}</code>",
            f"   ⏳ Access Until: <code>{html.escape(str(expires_at)[:19].replace('T', ' '))}</code>",
            "",
        ])
        report_users[uid] = {
            "user_id": user_id,
            "username": username,
            "user_status": status,
            "deployment_access": "Granted",
            "access_granted_at": granted_at,
            "access_expires_at": expires_at,
            "access_status": "Active" if access_active else "Expired",
        }

    if not user_ids:
        lines.append("<i>No users currently have ADD Access.</i>")

    return "\n".join(lines), user_ids, build_users_excel(report_users)


async def send_deployment_access_report(message: Message, bot: Bot) -> None:
    report_text, user_ids, excel_data = deployment_access_report()
    chunks = []
    current = ""
    for line in report_text.splitlines():
        if current and len(current) + len(line) + 1 > 4000:
            chunks.append(current.rstrip())
            current = ""
        current += line + "\n"
    if current.strip():
        chunks.append(current.rstrip())

    for chunk in chunks:
        await message.answer(
            chunk,
            reply_markup=deployment_access_keyboard(user_ids) if chunk == chunks[-1] else None,
            parse_mode="HTML",
        )

    await bot.send_document(
        chat_id=message.from_user.id,
        document=BufferedInputFile(
            excel_data,
            filename="deployment_access_users.xlsx",
        ),
        caption="📊 Excel file with ADD Access users.",
    )
    await message.answer(
        "➕ ADD Access:",
        reply_markup=deployment_access_reply_keyboard(),
    )


@admin_router.message(StateFilter("*"), F.text == BTN_ACCESS_LIST)
async def btn_deployment_access_list(
    message: Message,
    state: FSMContext,
    bot: Bot,
):
    if not await _admin_only_msg(message):
        return
    await state.clear()
    await send_deployment_access_report(message, bot)


@admin_router.callback_query(F.data.startswith("revoke_deploy_"))
async def callback_revoke_deployment_access(callback: CallbackQuery):
    if not await _admin_only_cb(callback):
        return

    raw_user_id = callback.data[len("revoke_deploy_"):]
    if not raw_user_id.isdigit():
        await callback.answer("❌ Invalid User ID.", show_alert=True)
        return

    target_id = int(raw_user_id)
    if not revoke_deployment_access(target_id):
        await callback.answer("ℹ️ This access was already revoked.", show_alert=True)
        return

    report_text, user_ids, _ = deployment_access_report()
    await callback.message.edit_text(
        report_text,
        reply_markup=deployment_access_keyboard(user_ids),
        parse_mode="HTML",
    )
    await callback.answer(f"✅ ADD Access revoked for {target_id}.")


@admin_router.message(StateFilter("*"), F.text == BTN_BOT_LIMIT)
async def btn_admin_bot_limit(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    await state.clear()
    await state.set_state(AdminStates.waiting_for_default_bot_limit)
    current_limit = get_default_bot_limit()
    current_text = str(current_limit) if current_limit is not None else "Unlimited"
    await message.answer(
        "⚙️ <b>Default User Bot Limit</b>\n\n"
        f"Current default limit: <b>{current_text}</b>\n\n"
        "Enter the new maximum Bot count for all Users.\n"
        "<i>Enter -1 for Unlimited.</i>",
        reply_markup=bot_limit_cancel_inline_keyboard(),
        parse_mode="HTML",
    )


@admin_router.message(
    AdminStates.waiting_for_default_bot_limit,
    F.text == BTN_CANCEL_BOT_LIMIT,
)
async def btn_cancel_bot_limit(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    await state.clear()
    await _restore_admin_kb(message, "❌ Bot limit setup was cancelled.")


@admin_router.callback_query(
    AdminStates.waiting_for_default_bot_limit,
    F.data == "cancel_default_bot_limit",
)
async def callback_cancel_bot_limit(callback: CallbackQuery, state: FSMContext):
    if not await _admin_only_cb(callback):
        return
    await state.clear()
    await callback.message.edit_reply_markup(reply_markup=None)
    await callback.message.answer(
        "❌ Bot limit setup was cancelled.",
        reply_markup=admin_reply_keyboard(),
    )
    await callback.answer()


@admin_router.message(AdminStates.waiting_for_default_bot_limit, F.text)
async def handle_default_bot_limit_value(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return

    raw = message.text.strip()
    if raw == "-1":
        new_limit = None
    elif raw.isdigit():
        new_limit = int(raw)
    else:
        await message.answer(
            "❌ Enter a valid number: 0 or higher for a limit, or -1 for Unlimited."
        )
        return

    set_default_bot_limit(new_limit)
    limit_text = str(new_limit) if new_limit is not None else "Unlimited"
    total_users = len(get_all_users())
    await state.clear()
    await _restore_admin_kb(
        message,
        f"✅ Default Bot limit <b>{limit_text}</b> set for all Users.\n"
        f"👥 Total Users: <b>{total_users}</b>",
    )


# ════════════════════════════════════════════════════════════════════════════════
# 🔙 Back to User Menu
# ════════════════════════════════════════════════════════════════════════════════

@admin_router.message(StateFilter("*"), F.text == BTN_BACK_ADMIN_PANEL)
async def btn_back_admin_panel(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    await state.clear()
    await message.answer(
        "🛡 <b>Admin Panel</b>\n\nChoose an option below:",
        reply_markup=admin_reply_keyboard(),
        parse_mode="HTML",
    )


@admin_router.message(StateFilter("*"), F.text == BTN_BACK_USER_MENU)
async def btn_back_user_menu(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    await state.clear()
    await message.answer(
        "🤖 <b>Master Bot Manager V2</b>\n\nChoose an option from the menu:",
        reply_markup=main_reply_keyboard(is_admin=True),
        parse_mode="HTML",
    )


# ════════════════════════════════════════════════════════════════════════════════
# 📊 System Stats
# ════════════════════════════════════════════════════════════════════════════════

@admin_router.message(StateFilter("*"), F.text == BTN_STATS)
async def btn_admin_stats(message: Message):
    if not await _admin_only_msg(message):
        return
    try:
        cpu_pct = psutil.cpu_percent(interval=1)
        ram     = psutil.virtual_memory()
        disk    = psutil.disk_usage(os.path.abspath("/"))

        ram_used   = ram.used  / (1024 ** 3)
        ram_total  = ram.total / (1024 ** 3)
        disk_used  = disk.used  / (1024 ** 3)
        disk_total = disk.total / (1024 ** 3)
        disk_free  = disk.free  / (1024 ** 3)

        text = (
            "📊 <b>System Stats (Real-time)</b>\n\n"
            f"🖥  <b>CPU Usage:</b>  {cpu_pct:.1f}%\n\n"
            f"🧠 <b>RAM:</b>\n"
            f"   • Used:  {ram_used:.2f} GB\n"
            f"   • Total: {ram_total:.2f} GB\n"
            f"   • Usage: {ram.percent:.1f}%\n\n"
            f"💾 <b>Disk:</b>\n"
            f"   • Used:  {disk_used:.2f} GB\n"
            f"   • Free:  {disk_free:.2f} GB\n"
            f"   • Total: {disk_total:.2f} GB\n"
            f"   • Usage: {disk.percent:.1f}%"
        )
    except Exception as e:
        text = f"❌ Could not fetch stats:\n<code>{html.escape(str(e))}</code>"

    await message.answer(text, parse_mode="HTML")


# ════════════════════════════════════════════════════════════════════════════════
# 📢 Broadcast — FSM
# ════════════════════════════════════════════════════════════════════════════════

def _get_forward_source(message: Message) -> tuple[int, int] | None:
    """Return (source chat id, source message id) for a forwarded message."""
    origin = getattr(message, "forward_origin", None)
    if origin is not None:
        source_chat = (
            getattr(origin, "chat", None)
            or getattr(origin, "sender_chat", None)
        )
        source_message_id = getattr(origin, "message_id", None)
        source_chat_id = getattr(source_chat, "id", None)
        if source_chat_id is not None and source_message_id is not None:
            return int(source_chat_id), int(source_message_id)

    # Compatibility with older Bot API/aiogram message fields.
    legacy_chat = getattr(message, "forward_from_chat", None)
    legacy_message_id = getattr(message, "forward_from_message_id", None)
    legacy_chat_id = getattr(legacy_chat, "id", None)
    if legacy_chat_id is not None and legacy_message_id is not None:
        return int(legacy_chat_id), int(legacy_message_id)
    return None


def _is_forwarded_message(message: Message) -> bool:
    """Return True when the Admin sent a Telegram-forwarded message."""
    return bool(
        getattr(message, "forward_origin", None)
        or (
            getattr(message, "forward_from_chat", None) is not None
            and getattr(message, "forward_from_message_id", None) is not None
        )
    )


@admin_router.message(StateFilter("*"), F.text == BTN_BROADCAST)
async def btn_admin_broadcast(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    await state.set_state(AdminStates.waiting_for_broadcast)
    await message.answer(
        "📢 <b>Broadcast Message</b>\n\n"
        "Send the message you want to broadcast now.\n"
        "Text, photos, videos, and other content are supported.",
        reply_markup=broadcast_cancel_reply_keyboard(),
        parse_mode="HTML",
    )


@admin_router.message(AdminStates.waiting_for_broadcast, F.text == BTN_CANCEL_BROADCAST)
async def btn_cancel_broadcast(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    await state.clear()
    await _restore_admin_kb(message, "❌ Broadcast was cancelled.")


@admin_router.message(AdminStates.waiting_for_broadcast)
async def handle_broadcast_message(message: Message, state: FSMContext, bot: Bot):
    if not await _admin_only_msg(message):
        return

    await state.clear()
    users   = get_all_users()
    uids    = list(users.keys())
    total   = len(uids)
    success = 0
    failed  = 0
    forward_source = _get_forward_source(message)
    is_forwarded = _is_forwarded_message(message)

    status_msg = await message.answer(
        f"⏳ Broadcast is starting... ({total} Users)",
        reply_markup=admin_reply_keyboard(),
    )

    for uid in uids:
        try:
            if is_forwarded:
                forwarded = False
                try:
                    # Forward the message as received in the Admin chat first.
                    # This preserves Telegram's forwarded header even when the
                    # original source is private or inaccessible to the Bot.
                    await bot.forward_message(
                        chat_id=int(uid),
                        from_chat_id=message.chat.id,
                        message_id=message.message_id,
                    )
                    forwarded = True
                except Exception:
                    pass

                if not forwarded and forward_source is not None:
                    try:
                        # Fall back to the original source when it is
                        # accessible to the Bot.
                        await bot.forward_message(
                            chat_id=int(uid),
                            from_chat_id=forward_source[0],
                            message_id=forward_source[1],
                        )
                        forwarded = True
                    except Exception:
                        pass

                if not forwarded:
                    # Protected content may not be forwardable at all.
                    await bot.copy_message(
                        chat_id=int(uid),
                        from_chat_id=message.chat.id,
                        message_id=message.message_id,
                    )
            else:
                await bot.copy_message(
                    chat_id=int(uid),
                    from_chat_id=message.chat.id,
                    message_id=message.message_id,
                )
            success += 1
        except Exception:
            failed += 1

    await status_msg.edit_text(
        f"📢 <b>Broadcast completed!</b>\n\n"
        f"✅ Successful: {success}\n"
        f"❌ Failed: {failed}\n"
        f"👥 Total: {total}",
        parse_mode="HTML",
    )


# ════════════════════════════════════════════════════════════════════════════════
# 👥 User settings — FSM
# ════════════════════════════════════════════════════════════════════════════════

@admin_router.message(StateFilter("*"), F.text == BTN_USERS)
async def btn_admin_users(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return

    users   = get_all_users()
    total   = len(users)
    blocked = sum(1 for u in users.values() if u.get("is_blocked"))

    await state.clear()
    await message.answer(
        f"👥 <b>User settings</b>\n\n"
        f"📋 Registered: <b>{total}</b>\n"
        f"🚫 Blocked:    <b>{blocked}</b>\n\n"
        f"Choose an option:",
        reply_markup=user_manager_reply_keyboard(),
        parse_mode="HTML",
    )


@admin_router.message(StateFilter("*"), F.text == BTN_BAN_UNBAN)
async def btn_admin_user_lookup(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    await state.set_state(AdminStates.waiting_for_user_id)
    await message.answer(
        "Enter a User ID to view, ban, or unban:",
        reply_markup=user_lookup_cancel_reply_keyboard(),
    )


@admin_router.message(StateFilter("*"), F.text == BTN_ALL_USERS)
async def btn_admin_all_users(message: Message, state: FSMContext, bot: Bot):
    if not await _admin_only_msg(message):
        return
    await send_all_users_report(message, state, bot)


@admin_router.callback_query(F.data == "admin_all_users")
async def callback_admin_all_users(callback: CallbackQuery, state: FSMContext, bot: Bot):
    if not await _admin_only_cb(callback):
        return
    await send_all_users_report(callback.message, state, bot)
    await callback.answer()


async def send_all_users_report(message: Message, state: FSMContext, bot: Bot):
    users = get_all_users()
    await state.clear()

    if not users:
        await message.answer("❌ No users found.")
        return

    detail_lines = ["👥 <b>All Registered Users</b>", f"Total: <b>{len(users)}</b>", ""]
    for number, (uid, user) in enumerate(users.items(), start=1):
        username = user.get("username") or "—"
        status = "Blocked" if user.get("is_blocked") else "Active"
        limit = user.get("bot_limit")
        limit_text = "Unlimited" if limit is None else str(limit)
        registered = user.get("registered_at", "—")
        detail_lines.append(
            f"{number}. 🆔 <code>{html.escape(str(user.get('user_id', uid)))}</code> | "
            f"📛 @{html.escape(str(username).lstrip('@'))}\n"
            f"   📌 {status} | 🎯 Limit: {html.escape(limit_text)} | "
            f"📅 {html.escape(str(registered)[:19].replace('T', ' '))}"
        )

    detail_text = "\n".join(detail_lines)
    if len(detail_text) <= 4096:
        await message.answer(detail_text, parse_mode="HTML")
    else:
        # Telegram has a 4096-character message limit; keep the requested
        # single-message view usable by showing every user's core details.
        compact_lines = [
            "👥 <b>All Registered Users</b>",
            f"Total: <b>{len(users)}</b>",
            "",
        ]
        for number, (uid, user) in enumerate(users.items(), start=1):
            compact_lines.append(
                f"{number}. <code>{html.escape(str(user.get('user_id', uid)))}</code> "
                f"@{html.escape(str(user.get('username') or '—').lstrip('@'))} "
                f"({'Blocked' if user.get('is_blocked') else 'Active'})"
            )
        compact_text = "\n".join(compact_lines)
        await message.answer(compact_text[:4090], parse_mode="HTML")

    excel_data = build_users_excel(users)
    await bot.send_document(
        chat_id=message.from_user.id,
        document=BufferedInputFile(excel_data, filename="all_users.xlsx"),
        caption="📊 Excel file with all user details.",
    )
    await message.answer("✅ User details and Excel file sent.")


@admin_router.message(StateFilter("*"), F.text == BTN_BANNED_USERS)
async def btn_admin_banned_users(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return

    await state.clear()
    banned_users = [
        user for user in get_all_users().values()
        if user.get("is_blocked", False)
    ]
    if not banned_users:
        await message.answer(
            "🚫 <b>Banned Users</b>\n\n<i>No users are currently banned.</i>",
            reply_markup=admin_reply_keyboard(),
            parse_mode="HTML",
        )
        return

    lines = [
        "🚫 <b>Banned Users</b>",
        f"Total: <b>{len(banned_users)}</b>",
        "",
    ]
    for number, user in enumerate(banned_users, start=1):
        user_id = user.get("user_id", "—")
        username = user.get("username") or "—"
        registered = str(user.get("registered_at", "—"))
        hosting_until = user.get("hosting_expires_at") or "Unlimited"
        bot_limit = user.get("bot_limit")
        bot_limit_text = "Default" if bot_limit is None else str(bot_limit)
        managed_bots = len(get_user_bots(user_id)) if str(user_id).isdigit() else 0
        lines.extend([
            f"{number}. 🆔 User ID: <code>{html.escape(str(user_id))}</code>",
            f"   📛 Username: @{html.escape(str(username).lstrip('@'))}",
            f"   📅 Registered: <code>{html.escape(registered[:19].replace('T', ' '))}</code>",
            f"   ⏳ Hosting Until: <code>{html.escape(str(hosting_until)[:19].replace('T', ' '))}</code>",
            f"   🎯 Bot Limit: <b>{html.escape(bot_limit_text)}</b>",
            f"   🤖 Managed Bots: <b>{managed_bots}</b>",
            "",
        ])

    # Send the complete report in Telegram-safe chunks.
    chunks = []
    current = ""
    for line in lines:
        if current and len(current) + len(line) + 1 > 4000:
            chunks.append(current.rstrip())
            current = ""
        current += line + "\n"
    if current.strip():
        chunks.append(current.rstrip())

    for chunk in chunks:
        await message.answer(chunk, parse_mode="HTML")
    await message.answer("🛡 Admin Panel:", reply_markup=admin_reply_keyboard())


@admin_router.message(AdminStates.waiting_for_user_id, F.text == BTN_CANCEL_LOOKUP)
async def btn_cancel_lookup(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    await state.clear()
    await _restore_admin_kb(message, "❌ Lookup was cancelled.")


@admin_router.message(AdminStates.waiting_for_user_id, F.text)
async def handle_user_id_input(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return

    raw = message.text.strip()
    if not raw.lstrip("-").isdigit():
        await message.answer("❌ Enter a numeric User ID.")
        return

    target_id = int(raw)
    user_data = get_user(target_id)
    if not user_data:
        await message.answer(
            f"❌ <code>{target_id}</code> — this User is not in the database.",
            parse_mode="HTML",
        )
        return

    await state.clear()

    username   = user_data.get("username") or "—"
    blocked    = user_data.get("is_blocked", False)
    reg_at     = user_data.get("registered_at", "—")
    status_txt = "🚫 Blocked" if blocked else "✅ Active"

    await message.answer(
        f"👤 <b>User Info</b>\n\n"
        f"🆔 ID:         <code>{target_id}</code>\n"
        f"📛 Username:   @{html.escape(username)}\n"
        f"📌 Status:     {status_txt}\n"
        f"📅 Registered: {reg_at[:19].replace('T', ' ')}",
        reply_markup=admin_user_info_keyboard(target_id, blocked),
        parse_mode="HTML",
    )
    await _restore_admin_kb(message, "🛡 Admin Panel:")


# ════════════════════════════════════════════════════════════════════════════════
# 📥 User ZIP Download — FSM + Callback
# ════════════════════════════════════════════════════════════════════════════════

@admin_router.message(StateFilter("*"), F.text == BTN_ZIP_DOWNLOAD)
async def btn_admin_zip_download(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    await state.clear()
    await state.set_state(AdminStates.waiting_for_zip_download_user_id)
    await message.answer(
        "📥 <b>User ZIP Download</b>\n\n"
        "Enter the User ID whose Bot ZIP you want to download.",
        reply_markup=zip_download_cancel_reply_keyboard(),
        parse_mode="HTML",
    )


@admin_router.message(
    AdminStates.waiting_for_zip_download_user_id,
    F.text == BTN_CANCEL_ZIP,
)
async def btn_cancel_zip_download(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    await state.clear()
    await _restore_admin_kb(message, "❌ ZIP Download was cancelled.")


@admin_router.message(AdminStates.waiting_for_zip_download_user_id, F.text)
async def handle_zip_download_user_id(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return

    raw = message.text.strip()
    if not raw.isdigit():
        await message.answer("❌ Enter a numeric User ID.")
        return

    target_id = int(raw)
    if not get_user(target_id):
        await message.answer(
            f"❌ <code>{target_id}</code> — this User is not in the database.",
            parse_mode="HTML",
        )
        return

    bots = pm.get_user_procs(target_id)
    if not bots:
        await state.clear()
        await _restore_admin_kb(
            message,
            f"❌ User <code>{target_id}</code> has no managed Bots.",
        )
        return

    await state.update_data(zip_download_user_id=target_id)
    await message.answer(
        f"📥 Select a Bot for User <code>{target_id}</code>:\n"
        "✅ = original ZIP is available, ⚠️ = original ZIP is missing.",
        reply_markup=admin_zip_download_keyboard(bots),
        parse_mode="HTML",
    )


@admin_router.callback_query(F.data.startswith("admin_zip_download_"))
async def callback_admin_zip_download(
    callback: CallbackQuery,
    state: FSMContext,
    bot: Bot,
):
    if not await _admin_only_cb(callback):
        return

    bot_name = callback.data[len("admin_zip_download_"):]
    if not any(proc["name"] == bot_name for proc in pm.get_all_procs()):
        await callback.answer("❌ Bot not found.", show_alert=True)
        return

    source_zip_path = original_zip_path_from_name(bot_name)
    if not os.path.exists(source_zip_path):
        await callback.answer(
            "⚠️ The original ZIP for this Bot is not available.",
            show_alert=True,
        )
        return

    await callback.answer("⏳ Sending the original ZIP...")
    try:
        with open(source_zip_path, "rb") as source_file:
            data = source_file.read()
        await bot.send_document(
            chat_id=callback.from_user.id,
            document=BufferedInputFile(data, filename=f"{bot_name}.zip"),
            caption=(
                f"📥 <b>Original ZIP</b>\n"
                f"🤖 Bot: <code>{html.escape(bot_name)}</code>"
            ),
            parse_mode="HTML",
        )
        await state.clear()
        if callback.message:
            await callback.message.answer(
                "🛡 Admin Panel:",
                reply_markup=admin_reply_keyboard(),
            )
    except Exception as e:
        await callback.message.answer(
            f"❌ Could not send the ZIP:\n<code>{html.escape(str(e))}</code>",
            parse_mode="HTML",
        )


# ─── Block / Unblock Inline Callbacks ────────────────────────────────────────

@admin_router.callback_query(F.data.startswith("admin_block_"))
async def callback_block_user(callback: CallbackQuery, bot: Bot):
    if not await _admin_only_cb(callback):
        return
    target_id = int(callback.data[len("admin_block_"):])

    if target_id == ADMIN_ID:
        await callback.answer("❌ The Admin cannot be blocked.", show_alert=True)
        return

    ok = block_user(target_id)
    if not ok:
        await callback.answer("❌ User not found.", show_alert=True)
        return

    await callback.message.edit_reply_markup(
        reply_markup=admin_user_info_keyboard(target_id, blocked=True)
    )
    try:
        await bot.send_message(
            chat_id=target_id,
            text=(
                "⛔ <b>You are blocked from this Bot.</b>\n\n"
                "You can only use the Support button to contact the Admin."
            ),
            reply_markup=blocked_user_keyboard(),
            parse_mode="HTML",
        )
    except Exception:
        # The user may not have started the Bot or may have blocked it.
        pass
    await callback.answer(f"✅ {target_id} has been blocked.")


@admin_router.callback_query(F.data.startswith("admin_unblock_"))
async def callback_unblock_user(callback: CallbackQuery):
    if not await _admin_only_cb(callback):
        return
    target_id = int(callback.data[len("admin_unblock_"):])

    ok = unblock_user(target_id)
    if not ok:
        await callback.answer("❌ User not found.", show_alert=True)
        return

    await callback.message.edit_reply_markup(
        reply_markup=admin_user_info_keyboard(target_id, blocked=False)
    )
    await callback.answer(f"✅ {target_id} has been unblocked.")


# ════════════════════════════════════════════════════════════════════════════════
# 🤖 Active Bots Summary — reads active_processes.json via process_manager
# ════════════════════════════════════════════════════════════════════════════════

@admin_router.message(StateFilter("*"), F.text == BTN_BOTS)
async def btn_admin_bots(message: Message):
    if not await _admin_only_msg(message):
        return

    all_procs = pm.get_all_procs()

    if not all_procs:
        await message.answer(
            "🤖 <b>Active Bots Summary</b>\n\n<i>No managed Bots.</i>",
            parse_mode="HTML",
        )
        return

    running = sum(1 for p in all_procs if p["alive"])
    stopped = len(all_procs) - running

    # Group by user_id
    user_map: dict[str, list[str]] = {}
    for p in all_procs:
        emoji = "🟢" if p["alive"] else "🔴"
        label = "Running" if p["alive"] else "Stopped"
        uid   = p["user_id"]
        entry = f"{emoji} {p['name']} [PID:{p['pid']}] [{label}]"
        user_map.setdefault(uid, []).append(entry)

    lines = [
        "🤖 <b>Active Bots Summary</b>\n",
        f"📦 Total Tracked: <b>{len(all_procs)}</b>",
        f"🟢 Running:       <b>{running}</b>",
        f"🔴 Stopped:       <b>{stopped}</b>",
        "\n<b>── Per-User Breakdown ──</b>",
    ]
    for uid, bot_list in user_map.items():
        lines.append(f"\n👤 User <code>{uid}</code>:")
        for entry in bot_list:
            lines.append(f"   {entry}")

    await message.answer("\n".join(lines), parse_mode="HTML")


# ════════════════════════════════════════════════════════════════════════════════
# 🔄 System Restart — choose a scoped or all-bot restart
# ════════════════════════════════════════════════════════════════════════════════

@admin_router.message(StateFilter("*"), F.text == BTN_RESTART)
async def btn_admin_restart(message: Message):
    if not await _admin_only_msg(message):
        return

    all_procs = pm.get_all_procs()
    availability_note = (
        "\n\nℹ️ No tracked Bots are currently available. "
        "The restart options will work when a Bot is running."
        if not all_procs
        else ""
    )
    await message.answer(
        "🔄 <b>System Restart</b>\n\n"
        "Choose whether to restart one user's selected Bot or all managed "
        f"Bots from every User.{availability_note}",
        reply_markup=restart_options_keyboard(),
        parse_mode="HTML",
    )


def _restart_process_records(
    proc_records: list[dict],
) -> tuple[int, int, list[str]]:
    """Restart only the supplied tracked process records."""
    ok_count = 0
    fail_count = 0
    result_lines: list[str] = []

    for proc_info in proc_records:
        bot_name = proc_info["name"]
        old_pid = proc_info["pid"]
        bot_folder = proc_info["folder"]
        entry_file = (
            proc_info.get("entry_file")
            or detect_entry_file(bot_folder)
            or "main.py"
        )

        if proc_info["alive"]:
            try:
                old_proc = psutil.Process(old_pid)
                old_proc.terminate()
                try:
                    old_proc.wait(timeout=5)
                except psutil.TimeoutExpired:
                    old_proc.kill()
            except (psutil.NoSuchProcess, psutil.AccessDenied):
                pass

        if not bot_folder or not os.path.exists(bot_folder):
            result_lines.append(
                f"❌ {html.escape(bot_name)}: folder not found, skipped."
            )
            fail_count += 1
            pm.unregister(bot_name)
            continue

        try:
            ok, err = install_dependencies(bot_folder, entry_file)
            if not ok:
                result_lines.append(
                    f"❌ {html.escape(bot_name)}: setup failed — "
                    f"{html.escape(err[:500])}"
                )
                fail_count += 1
                continue

            new_proc = spawn_bot(bot_folder, entry_file)
            pm.update_pid(bot_name, new_proc.pid)
            result_lines.append(
                f"✅ {html.escape(bot_name)}: PID {old_pid} → {new_proc.pid}"
            )
            ok_count += 1
        except Exception as e:
            result_lines.append(
                f"❌ {html.escape(bot_name)}: {html.escape(str(e))}"
            )
            fail_count += 1

    return ok_count, fail_count, result_lines


def _restart_summary(
    title: str,
    ok_count: int,
    fail_count: int,
    result_lines: list[str],
) -> str:
    details = "\n".join(result_lines) if result_lines else "No result details."
    return (
        f"🔄 <b>{html.escape(title)}</b>\n\n"
        f"✅ Successful: {ok_count}\n"
        f"❌ Failed: {fail_count}\n\n"
        f"{details}"
    )


@admin_router.callback_query(F.data == "admin_restart_specific_user")
async def callback_restart_specific_user(
    callback: CallbackQuery,
    state: FSMContext,
):
    if not await _admin_only_cb(callback):
        return
    await state.clear()
    await state.set_state(AdminStates.waiting_for_restart_user_id)
    await callback.message.answer(
        "👤 Enter the User ID whose Bot you want to restart.",
        reply_markup=restart_cancel_reply_keyboard(),
    )
    await callback.answer()


@admin_router.message(
    AdminStates.waiting_for_restart_user_id,
    F.text == BTN_CANCEL_RESTART,
)
async def cancel_restart_user_lookup(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return
    await state.clear()
    await _restore_admin_kb(message, "❌ Restart selection was cancelled.")


@admin_router.message(AdminStates.waiting_for_restart_user_id, F.text)
async def handle_restart_user_id(message: Message, state: FSMContext):
    if not await _admin_only_msg(message):
        return

    raw = message.text.strip()
    if not raw.isdigit():
        await message.answer("❌ Enter a numeric User ID.")
        return

    target_id = int(raw)
    user_bots = pm.get_user_procs(target_id)
    if not user_bots:
        await state.clear()
        await _restore_admin_kb(
            message,
            f"❌ User <code>{target_id}</code> has no managed Bots.",
        )
        return

    await state.update_data(restart_user_id=target_id)
    await message.answer(
        f"👤 Select the Bot to restart for User <code>{target_id}</code>:",
        reply_markup=restart_user_bots_keyboard(user_bots),
        parse_mode="HTML",
    )


@admin_router.callback_query(F.data == "admin_restart_menu")
async def callback_restart_menu(callback: CallbackQuery, state: FSMContext):
    if not await _admin_only_cb(callback):
        return
    await state.clear()
    await callback.message.edit_text(
        "🔄 <b>System Restart</b>\n\nChoose a restart scope:",
        reply_markup=restart_options_keyboard(),
        parse_mode="HTML",
    )
    await callback.answer()


@admin_router.callback_query(F.data == "admin_restart_back")
async def callback_restart_back(callback: CallbackQuery, state: FSMContext):
    if not await _admin_only_cb(callback):
        return
    await state.clear()
    await callback.message.edit_reply_markup(reply_markup=None)
    await callback.message.answer(
        "🛡 <b>Admin Panel</b>",
        reply_markup=admin_reply_keyboard(),
        parse_mode="HTML",
    )
    await callback.answer()


@admin_router.callback_query(F.data.startswith("admin_restart_select_"))
async def callback_restart_selected_bot(
    callback: CallbackQuery,
    state: FSMContext,
):
    if not await _admin_only_cb(callback):
        return

    data = await state.get_data()
    target_id = data.get("restart_user_id")
    bot_name = callback.data[len("admin_restart_select_"):]
    if not target_id:
        await callback.answer(
            "❌ Restart session expired. Start again.",
            show_alert=True,
        )
        return

    selected = next(
        (
            proc for proc in pm.get_user_procs(target_id)
            if proc["name"] == bot_name
        ),
        None,
    )
    if selected is None:
        await callback.answer("❌ This Bot is no longer available.", show_alert=True)
        return

    await state.update_data(restart_bot_name=bot_name)
    await callback.message.edit_text(
        f"⚠️ <b>Restart permission required</b>\n\n"
        f"User: <code>{target_id}</code>\n"
        f"Bot: <code>{html.escape(bot_name)}</code>\n\n"
        "Do you want to restart this Bot?",
        reply_markup=restart_selected_bot_confirmation_keyboard(),
        parse_mode="HTML",
    )
    await callback.answer()


@admin_router.callback_query(F.data == "admin_restart_user_bots_back")
async def callback_restart_user_bots_back(
    callback: CallbackQuery,
    state: FSMContext,
):
    if not await _admin_only_cb(callback):
        return

    data = await state.get_data()
    target_id = data.get("restart_user_id")
    if not target_id:
        await state.clear()
        await callback.message.edit_text(
            "🔄 <b>System Restart</b>\n\nChoose a restart scope:",
            reply_markup=restart_options_keyboard(),
            parse_mode="HTML",
        )
        await callback.answer()
        return

    user_bots = pm.get_user_procs(target_id)
    if not user_bots:
        await state.clear()
        await callback.message.edit_text(
            f"❌ User <code>{target_id}</code> has no managed Bots.",
            parse_mode="HTML",
        )
        await callback.answer()
        return

    await state.update_data(restart_bot_name=None)
    await callback.message.edit_text(
        f"👤 Select the Bot to restart for User <code>{target_id}</code>:",
        reply_markup=restart_user_bots_keyboard(user_bots),
        parse_mode="HTML",
    )
    await callback.answer()


@admin_router.callback_query(F.data == "admin_restart_bot_confirm")
async def callback_restart_selected_bot_confirm(
    callback: CallbackQuery,
    state: FSMContext,
):
    if not await _admin_only_cb(callback):
        return

    data = await state.get_data()
    target_id = data.get("restart_user_id")
    bot_name = data.get("restart_bot_name")
    if not target_id or not bot_name:
        await callback.answer(
            "❌ Restart session expired. Start again.",
            show_alert=True,
        )
        return

    selected = next(
        (
            proc for proc in pm.get_user_procs(target_id)
            if proc["name"] == bot_name
        ),
        None,
    )
    if selected is None:
        await callback.answer("❌ This Bot is no longer available.", show_alert=True)
        return

    await callback.answer("⏳ Restarting selected Bot...")
    status_msg = await callback.message.answer(
        f"⏳ Restarting <code>{html.escape(bot_name)}</code>...",
        parse_mode="HTML",
    )
    ok_count, fail_count, result_lines = _restart_process_records([selected])
    await state.clear()
    await status_msg.edit_text(
        _restart_summary(
            f"Restart completed for User {target_id}",
            ok_count,
            fail_count,
            result_lines,
        ),
        parse_mode="HTML",
    )
    await callback.message.answer(
        "🛡 Admin Panel:",
        reply_markup=admin_reply_keyboard(),
    )


@admin_router.callback_query(F.data == "admin_restart_all_confirm")
async def callback_restart_all_confirm(callback: CallbackQuery):
    if not await _admin_only_cb(callback):
        return

    total = len(pm.get_all_procs())
    if not total:
        await callback.answer("ℹ️ No tracked Bots to restart.", show_alert=True)
        return

    await callback.message.edit_text(
        f"⚠️ <b>Permission required</b>\n\n"
        f"This will restart all <b>{total}</b> managed Bots belonging to "
        "all Users.\n\nContinue?",
        reply_markup=restart_all_confirmation_keyboard(),
        parse_mode="HTML",
    )
    await callback.answer()


@admin_router.callback_query(F.data == "admin_restart_all_execute")
async def callback_restart_all_execute(
    callback: CallbackQuery,
    state: FSMContext,
):
    if not await _admin_only_cb(callback):
        return

    all_procs = pm.get_all_procs()
    if not all_procs:
        await callback.answer("ℹ️ No tracked Bots to restart.", show_alert=True)
        return

    await callback.answer("⏳ Restarting all managed Bots...")
    status_msg = await callback.message.answer(
        f"⏳ Restarting {len(all_procs)} Bots...",
    )
    ok_count, fail_count, result_lines = _restart_process_records(all_procs)
    await state.clear()
    await status_msg.edit_text(
        _restart_summary(
            "System Restart completed for all Users",
            ok_count,
            fail_count,
            result_lines,
        ),
        parse_mode="HTML",
    )
    await callback.message.answer(
        "🛡 Admin Panel:",
        reply_markup=admin_reply_keyboard(),
    )


# ── main.py entrypoint ───────────────────────────────────────────────────────
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(name)s: %(message)s",
    handlers=[
        # Explicitly pass UTF-8 so logging never falls back to cp1252 on Windows
        logging.StreamHandler(stream=sys.stderr),
    ],
)
# Patch the handler's stream encoding just in case reconfigure() was not enough
for _h in logging.root.handlers:
    if hasattr(_h, "stream") and hasattr(_h.stream, "reconfigure"):
        try:
            _h.stream.reconfigure(encoding="utf-8", errors="replace")
        except Exception:
            pass

logger = logging.getLogger(__name__)


async def main():
    if not MASTER_BOT_TOKEN:
        raise RuntimeError(
            "Bot token is not configured. "
            "Put the token on a non-comment line in botToken.txt before starting the bot."
        )
    bot     = _StyledBot(token=MASTER_BOT_TOKEN)
    storage = MemoryStorage()
    dp      = Dispatcher(storage=storage)

    # Global middleware — registers every user and enforces block list.
    # Must be registered on the dispatcher so it runs for ALL updates.
    dp.message.outer_middleware(UserMiddleware())
    dp.callback_query.outer_middleware(UserMiddleware())

    # admin_router first so its StateFilter("*") handlers for BTN_ADMIN_PANEL
    # are matched before the user router's StateFilter("*") handlers.
    dp.include_router(admin_router)
    dp.include_router(router)

    logger.info("Master Bot Manager V2 starting...")
    status_monitor_task = asyncio.create_task(monitor_bot_status(bot))

    try:
        await dp.start_polling(bot, allowed_updates=dp.resolve_used_update_types())
    finally:
        status_monitor_task.cancel()
        try:
            await status_monitor_task
        except asyncio.CancelledError:
            pass
        await bot.session.close()
        logger.info("Bot stopped.")


if __name__ == "__main__":
    asyncio.run(main())
