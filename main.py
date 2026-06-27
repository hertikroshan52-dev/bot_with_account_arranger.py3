# -*- coding: utf-8 -*-
"""
Safe Link Distribution Bot

الوظائف:
- إضافة حسابات فحص scanner وحسابات توزيع distribution منفصلة.
- استيراد روابط Telegram من قناة/مجموعة تجميع.
- فحص الروابط بحسابات الفحص فقط، بدون انضمام جماعي تلقائي.
- تصنيف الروابط: مجموعة، قناة، مستخدم، بوت، منتهي، خاص غير مؤكد، فشل فحص.
- حساب عدد حسابات التوزيع المطلوبة.
- توزيع 1000 رابط صالح لكل حساب توزيع بدون تكرار.
- إرسال دفعة كل حساب إلى Saved Messages الخاصة بالحساب نفسه.
- تصدير ملفات TXT مضغوطة ZIP لكل حملة.

مهم:
هذا الكود لا ينفذ انضماماً جماعياً تلقائياً إلى الروابط.
زر Saved Messages يحفظ الدفعات فقط داخل الرسائل المحفوظة للحسابات، ولا ينضم للروابط.
"""

import asyncio
import math
import os
import re
import sqlite3
import zipfile
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

from telegram import InlineKeyboardButton, InlineKeyboardMarkup, InputFile, Update
from telegram.constants import ParseMode
from telegram.ext import Application, CallbackQueryHandler, CommandHandler, ContextTypes, MessageHandler, filters

from telethon import TelegramClient, types
from telethon.errors import FloodWaitError, UsernameInvalidError, UsernameNotOccupiedError, InviteHashExpiredError, InviteHashInvalidError
from telethon.sessions import StringSession
from telethon.tl.functions.channels import GetFullChannelRequest
from telethon.tl.functions.messages import CheckChatInviteRequest, GetFullChatRequest


# ============================
# Environment / إعدادات التشغيل
# ============================


def required_env(name: str) -> str:
    value = os.environ.get(name, "").strip()
    if not value:
        raise SystemExit(f"❌ المتغير {name} غير موجود. استخدم export {name}=... قبل تشغيل البوت.")
    return value


BOT_TOKEN = required_env("BOT_TOKEN")
OWNER_ID = int(required_env("OWNER_ID"))
API_ID = int(required_env("API_ID"))
API_HASH = required_env("API_HASH")

DATA_DIR = Path(os.environ.get("DATA_DIR", "safe_link_bot_data"))
EXPORTS_DIR = DATA_DIR / "exports"
DB_PATH = DATA_DIR / "safe_link_distribution.db"
DATA_DIR.mkdir(parents=True, exist_ok=True)
EXPORTS_DIR.mkdir(parents=True, exist_ok=True)

LINKS_PER_ACCOUNT = int(os.environ.get("LINKS_PER_ACCOUNT", "1000"))
SAVED_MESSAGE_CHUNK_SIZE = int(os.environ.get("SAVED_MESSAGE_CHUNK_SIZE", "100"))
DEFAULT_IMPORT_LIMIT = int(os.environ.get("DEFAULT_IMPORT_LIMIT", "0"))  # 0 = كل الرسائل المتاحة
DEFAULT_SCAN_LIMIT = int(os.environ.get("DEFAULT_SCAN_LIMIT", "5000"))


# ============================
# Utilities / أدوات مساعدة
# ============================


def now_iso() -> str:
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def safe_filename(value: str, fallback: str = "file") -> str:
    value = re.sub(r"[^A-Za-z0-9_\-\u0600-\u06FF]+", "_", value).strip("_")
    return value[:80] or fallback


def chunks(items: Sequence[str], size: int) -> Iterable[Sequence[str]]:
    for i in range(0, len(items), size):
        yield items[i:i + size]


def format_count(value: int) -> str:
    return f"{value:,}".replace(",", ",")


TELEGRAM_LINK_RE = re.compile(
    r'''(?:https?://)?(?:t\.me|telegram\.me)/[^\s<>"'\]\)\}،؛]+''',
    re.IGNORECASE,
)


def extract_telegram_links(text: str) -> List[str]:
    """استخراج روابط تليجرام فقط من النص."""
    if not text:
        return []
    results = []
    for raw in TELEGRAM_LINK_RE.findall(text):
        normalized = normalize_telegram_link(raw)
        if normalized:
            results.append(normalized)
    return list(dict.fromkeys(results))


def normalize_telegram_link(raw: str) -> Optional[str]:
    """توحيد رابط تليجرام ومنع روابط الرسائل والبوتات الواضحة."""
    if not raw:
        return None

    link = raw.strip().strip('.,;:!?)"]}،؛\n\r\t ')
    link = re.sub(r"^https?://", "", link, flags=re.IGNORECASE)
    link = link.replace("telegram.me/", "t.me/")
    link = link.split("?", 1)[0].split("#", 1)[0].strip("/")

    if not link.lower().startswith("t.me/"):
        return None

    path = link[5:].strip("/")
    if not path:
        return None

    parts = [p for p in path.split("/") if p]
    if not parts:
        return None

    first = parts[0]
    first_lower = first.lower()

    # استبعاد روابط رسائل القنوات والمشاهدات الداخلية
    if first_lower in {"c", "s"}:
        return None
    if len(parts) >= 2 and parts[1].isdigit():
        return None

    # استبعاد روابط البوتات العامة الواضحة
    if first_lower.endswith("bot"):
        return None

    return "https://t.me/" + "/".join(parts)


def invite_hash_from_link(link: str) -> Optional[str]:
    normalized = normalize_telegram_link(link)
    if not normalized:
        return None
    path = normalized.replace("https://t.me/", "", 1)
    if path.startswith("+"):
        return path[1:]
    if path.lower().startswith("joinchat/"):
        return path.split("/", 1)[1]
    return None


def public_entity_ref_from_link(link: str) -> Optional[str]:
    normalized = normalize_telegram_link(link)
    if not normalized:
        return None
    if invite_hash_from_link(normalized):
        return None
    path = normalized.replace("https://t.me/", "", 1).strip("/")
    if not path or "/" in path:
        # addlist أو روابط مركبة لا نعالجها ككيان عام
        return None
    return path


# ============================
# Database / قاعدة البيانات
# ============================


class Database:
    def __init__(self, path: Path):
        self.path = path
        self.init()

    def connect(self):
        conn = sqlite3.connect(self.path, timeout=30)
        conn.row_factory = sqlite3.Row
        conn.execute("PRAGMA journal_mode=WAL")
        conn.execute("PRAGMA synchronous=NORMAL")
        return conn

    def init(self):
        with self.connect() as conn:
            cur = conn.cursor()
            cur.execute(
                """
                CREATE TABLE IF NOT EXISTS accounts (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    admin_id INTEGER NOT NULL,
                    role TEXT NOT NULL CHECK(role IN ('scanner', 'distribution')),
                    session_string TEXT UNIQUE NOT NULL,
                    phone TEXT,
                    name TEXT,
                    username TEXT,
                    is_active INTEGER DEFAULT 1,
                    added_at TEXT DEFAULT CURRENT_TIMESTAMP
                )
                """
            )
            cur.execute(
                """
                CREATE TABLE IF NOT EXISTS links (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    admin_id INTEGER NOT NULL,
                    link TEXT NOT NULL,
                    normalized_link TEXT NOT NULL,
                    source TEXT,
                    source_message_id INTEGER,
                    status TEXT DEFAULT 'pending',
                    entity_type TEXT DEFAULT 'unknown',
                    entity_id TEXT,
                    title TEXT,
                    members_count INTEGER DEFAULT 0,
                    subscribers_count INTEGER DEFAULT 0,
                    reason TEXT,
                    scanned_by_account_id INTEGER,
                    imported_at TEXT DEFAULT CURRENT_TIMESTAMP,
                    scanned_at TEXT,
                    UNIQUE(admin_id, normalized_link)
                )
                """
            )
            cur.execute("CREATE INDEX IF NOT EXISTS idx_links_admin_status ON links(admin_id, status, id)")
            cur.execute("CREATE INDEX IF NOT EXISTS idx_links_admin_entity_type ON links(admin_id, entity_type, id)")

            cur.execute(
                """
                CREATE TABLE IF NOT EXISTS campaigns (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    admin_id INTEGER NOT NULL,
                    name TEXT NOT NULL,
                    links_per_account INTEGER DEFAULT 1000,
                    total_valid_links INTEGER DEFAULT 0,
                    required_accounts INTEGER DEFAULT 0,
                    provided_accounts INTEGER DEFAULT 0,
                    assigned_links INTEGER DEFAULT 0,
                    remaining_links INTEGER DEFAULT 0,
                    status TEXT DEFAULT 'created',
                    created_at TEXT DEFAULT CURRENT_TIMESTAMP
                )
                """
            )
            cur.execute(
                """
                CREATE TABLE IF NOT EXISTS campaign_accounts (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    campaign_id INTEGER NOT NULL,
                    account_id INTEGER NOT NULL,
                    account_order INTEGER NOT NULL,
                    assigned_count INTEGER DEFAULT 0,
                    saved_messages_status TEXT DEFAULT 'pending',
                    saved_messages_count INTEGER DEFAULT 0,
                    status TEXT DEFAULT 'ready',
                    UNIQUE(campaign_id, account_id),
                    UNIQUE(campaign_id, account_order)
                )
                """
            )
            cur.execute(
                """
                CREATE TABLE IF NOT EXISTS assignments (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    campaign_id INTEGER NOT NULL,
                    campaign_account_id INTEGER NOT NULL,
                    account_id INTEGER NOT NULL,
                    link_id INTEGER NOT NULL,
                    link TEXT NOT NULL,
                    order_index INTEGER NOT NULL,
                    saved_message_part INTEGER,
                    status TEXT DEFAULT 'assigned',
                    created_at TEXT DEFAULT CURRENT_TIMESTAMP,
                    UNIQUE(campaign_id, link_id),
                    UNIQUE(campaign_id, campaign_account_id, order_index)
                )
                """
            )
            cur.execute(
                """
                CREATE TABLE IF NOT EXISTS saved_message_exports (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    campaign_id INTEGER NOT NULL,
                    campaign_account_id INTEGER NOT NULL,
                    account_id INTEGER NOT NULL,
                    part_number INTEGER NOT NULL,
                    links_count INTEGER DEFAULT 0,
                    status TEXT DEFAULT 'pending',
                    sent_at TEXT,
                    error TEXT,
                    UNIQUE(campaign_id, campaign_account_id, part_number)
                )
                """
            )
            conn.commit()

    # ---------- Accounts ----------
    def add_account(self, admin_id: int, role: str, session_string: str, phone: str, name: str, username: str) -> Tuple[bool, str]:
        try:
            with self.connect() as conn:
                conn.execute(
                    """
                    INSERT INTO accounts(admin_id, role, session_string, phone, name, username)
                    VALUES (?, ?, ?, ?, ?, ?)
                    """,
                    (admin_id, role, session_string, phone, name, username),
                )
                conn.commit()
            return True, "تمت إضافة الحساب بنجاح."
        except sqlite3.IntegrityError:
            return False, "هذا الحساب مضاف مسبقاً."

    def get_accounts(self, admin_id: int, role: Optional[str] = None) -> List[sqlite3.Row]:
        with self.connect() as conn:
            if role:
                rows = conn.execute(
                    "SELECT * FROM accounts WHERE admin_id=? AND role=? AND is_active=1 ORDER BY id",
                    (admin_id, role),
                ).fetchall()
            else:
                rows = conn.execute(
                    "SELECT * FROM accounts WHERE admin_id=? AND is_active=1 ORDER BY role, id",
                    (admin_id,),
                ).fetchall()
        return rows

    def delete_account(self, admin_id: int, account_id: int) -> bool:
        with self.connect() as conn:
            cur = conn.execute("UPDATE accounts SET is_active=0 WHERE admin_id=? AND id=?", (admin_id, account_id))
            conn.commit()
            return cur.rowcount > 0

    # ---------- Links ----------
    def add_link(self, admin_id: int, link: str, source: str = None, source_message_id: int = None) -> bool:
        normalized = normalize_telegram_link(link)
        if not normalized:
            return False
        try:
            with self.connect() as conn:
                conn.execute(
                    """
                    INSERT INTO links(admin_id, link, normalized_link, source, source_message_id)
                    VALUES (?, ?, ?, ?, ?)
                    """,
                    (admin_id, link, normalized, source, source_message_id),
                )
                conn.commit()
            return True
        except sqlite3.IntegrityError:
            return False

    def get_links_for_scan(self, admin_id: int, limit: int) -> List[sqlite3.Row]:
        with self.connect() as conn:
            rows = conn.execute(
                """
                SELECT * FROM links
                WHERE admin_id=? AND status IN ('pending', 'scan_failed')
                ORDER BY id ASC
                LIMIT ?
                """,
                (admin_id, limit),
            ).fetchall()
        return rows

    def update_link_scan(self, link_id: int, status: str, entity_type: str, entity_id: str = None,
                         title: str = None, members_count: int = 0, subscribers_count: int = 0,
                         reason: str = None, scanned_by_account_id: int = None):
        with self.connect() as conn:
            conn.execute(
                """
                UPDATE links
                SET status=?, entity_type=?, entity_id=?, title=?, members_count=?, subscribers_count=?,
                    reason=?, scanned_by_account_id=?, scanned_at=?
                WHERE id=?
                """,
                (status, entity_type, entity_id, title, members_count or 0, subscribers_count or 0,
                 reason, scanned_by_account_id, now_iso(), link_id),
            )
            conn.commit()

    def count_links(self, admin_id: int) -> Dict[str, int]:
        with self.connect() as conn:
            rows = conn.execute(
                "SELECT status, COUNT(*) AS c FROM links WHERE admin_id=? GROUP BY status",
                (admin_id,),
            ).fetchall()
            by_status = {row["status"]: row["c"] for row in rows}
            total = conn.execute("SELECT COUNT(*) c FROM links WHERE admin_id=?", (admin_id,)).fetchone()["c"]
        by_status["total"] = total
        return by_status

    def count_valid_groups(self, admin_id: int) -> int:
        with self.connect() as conn:
            row = conn.execute(
                "SELECT COUNT(*) c FROM links WHERE admin_id=? AND status='valid_group'",
                (admin_id,),
            ).fetchone()
        return int(row["c"])

    def get_valid_group_links(self, admin_id: int) -> List[sqlite3.Row]:
        with self.connect() as conn:
            rows = conn.execute(
                """
                SELECT * FROM links
                WHERE admin_id=? AND status='valid_group'
                ORDER BY id ASC
                """,
                (admin_id,),
            ).fetchall()
        return rows

    def get_links_by_status(self, admin_id: int, statuses: Sequence[str]) -> List[sqlite3.Row]:
        placeholders = ",".join("?" for _ in statuses)
        with self.connect() as conn:
            rows = conn.execute(
                f"SELECT * FROM links WHERE admin_id=? AND status IN ({placeholders}) ORDER BY id ASC",
                (admin_id, *statuses),
            ).fetchall()
        return rows

    # ---------- Campaigns ----------
    def latest_campaign(self, admin_id: int) -> Optional[sqlite3.Row]:
        with self.connect() as conn:
            row = conn.execute(
                "SELECT * FROM campaigns WHERE admin_id=? ORDER BY id DESC LIMIT 1",
                (admin_id,),
            ).fetchone()
        return row

    def create_distribution_campaign(self, admin_id: int, name: str, links_per_account: int = LINKS_PER_ACCOUNT) -> Tuple[bool, str, Optional[int]]:
        valid_links = self.get_valid_group_links(admin_id)
        dist_accounts = self.get_accounts(admin_id, "distribution")
        total_valid = len(valid_links)
        required = math.ceil(total_valid / links_per_account) if total_valid else 0
        provided = len(dist_accounts)
        capacity = provided * links_per_account
        assign_count = min(total_valid, capacity)
        remaining = max(total_valid - assign_count, 0)

        if total_valid == 0:
            return False, "لا توجد روابط valid_group صالحة للتوزيع. شغّل الفحص أولاً.", None
        if provided == 0:
            return False, "لا توجد حسابات توزيع. أضف حسابات distribution أولاً.", None

        with self.connect() as conn:
            cur = conn.cursor()
            cur.execute(
                """
                INSERT INTO campaigns(admin_id, name, links_per_account, total_valid_links, required_accounts,
                                      provided_accounts, assigned_links, remaining_links, status)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, 'assigned')
                """,
                (admin_id, name, links_per_account, total_valid, required, provided, assign_count, remaining),
            )
            campaign_id = int(cur.lastrowid)

            campaign_account_ids = []
            for idx, acc in enumerate(dist_accounts, start=1):
                cur.execute(
                    """
                    INSERT INTO campaign_accounts(campaign_id, account_id, account_order)
                    VALUES (?, ?, ?)
                    """,
                    (campaign_id, acc["id"], idx),
                )
                campaign_account_ids.append((int(cur.lastrowid), int(acc["id"]), idx))

            for global_index, link_row in enumerate(valid_links[:assign_count]):
                account_slot = global_index // links_per_account
                order_index = (global_index % links_per_account) + 1
                campaign_account_id, account_id, _account_order = campaign_account_ids[account_slot]
                cur.execute(
                    """
                    INSERT INTO assignments(campaign_id, campaign_account_id, account_id, link_id, link, order_index)
                    VALUES (?, ?, ?, ?, ?, ?)
                    """,
                    (campaign_id, campaign_account_id, account_id, link_row["id"], link_row["normalized_link"], order_index),
                )

            # تحديث عدد المخصص لكل حساب
            cur.execute(
                """
                UPDATE campaign_accounts
                SET assigned_count = (
                    SELECT COUNT(*) FROM assignments
                    WHERE assignments.campaign_account_id = campaign_accounts.id
                )
                WHERE campaign_id=?
                """,
                (campaign_id,),
            )
            conn.commit()

        msg = (
            f"✅ تم إنشاء حملة التوزيع: {name}\n\n"
            f"الروابط الصالحة: {format_count(total_valid)}\n"
            f"كل حساب يأخذ: {format_count(links_per_account)}\n"
            f"الحسابات المطلوبة: {format_count(required)}\n"
            f"الحسابات المضافة: {format_count(provided)}\n"
            f"تم توزيع: {format_count(assign_count)}\n"
            f"المتبقي غير موزع: {format_count(remaining)}"
        )
        return True, msg, campaign_id

    def get_campaign_accounts(self, campaign_id: int) -> List[sqlite3.Row]:
        with self.connect() as conn:
            rows = conn.execute(
                """
                SELECT ca.*, a.session_string, a.name, a.username, a.phone
                FROM campaign_accounts ca
                JOIN accounts a ON a.id = ca.account_id
                WHERE ca.campaign_id=?
                ORDER BY ca.account_order ASC
                """,
                (campaign_id,),
            ).fetchall()
        return rows

    def get_assignments_for_campaign_account(self, campaign_account_id: int) -> List[sqlite3.Row]:
        with self.connect() as conn:
            rows = conn.execute(
                """
                SELECT * FROM assignments
                WHERE campaign_account_id=?
                ORDER BY order_index ASC
                """,
                (campaign_account_id,),
            ).fetchall()
        return rows

    def mark_saved_message_part(self, campaign_id: int, campaign_account_id: int, account_id: int,
                                part_number: int, links_count: int, status: str, error: str = None):
        with self.connect() as conn:
            conn.execute(
                """
                INSERT INTO saved_message_exports(campaign_id, campaign_account_id, account_id, part_number,
                                                  links_count, status, sent_at, error)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?)
                ON CONFLICT(campaign_id, campaign_account_id, part_number)
                DO UPDATE SET status=excluded.status, links_count=excluded.links_count,
                              sent_at=excluded.sent_at, error=excluded.error
                """,
                (campaign_id, campaign_account_id, account_id, part_number, links_count, status,
                 now_iso() if status == "sent" else None, error),
            )
            conn.execute(
                """
                UPDATE campaign_accounts
                SET saved_messages_count = (
                    SELECT COALESCE(SUM(links_count), 0)
                    FROM saved_message_exports
                    WHERE campaign_account_id=? AND status='sent'
                ),
                saved_messages_status = CASE
                    WHEN (
                        SELECT COALESCE(SUM(links_count), 0)
                        FROM saved_message_exports
                        WHERE campaign_account_id=? AND status='sent'
                    ) >= assigned_count THEN 'sent'
                    ELSE 'partial'
                END
                WHERE id=?
                """,
                (campaign_account_id, campaign_account_id, campaign_account_id),
            )
            conn.commit()


# ============================
# Telethon service / خدمة تليجرام
# ============================


@dataclass
class ScanResult:
    status: str
    entity_type: str
    entity_id: Optional[str] = None
    title: Optional[str] = None
    members_count: int = 0
    subscribers_count: int = 0
    reason: Optional[str] = None


class TelegramService:
    @staticmethod
    def client(session_string: str) -> TelegramClient:
        return TelegramClient(StringSession(session_string), API_ID, API_HASH)

    @staticmethod
    async def test_session(session_string: str):
        client = TelegramService.client(session_string)
        await client.connect()
        try:
            if not await client.is_user_authorized():
                return False, None
            me = await client.get_me()
            return True, me
        finally:
            await client.disconnect()

    @staticmethod
    async def import_links_from_dialog(session_string: str, dialog_ref: str, limit: int = 0) -> Tuple[int, int, List[Tuple[str, int]]]:
        """يرجع: عدد الرسائل المفحوصة، عدد الروابط المستخرجة، قائمة (link, message_id)."""
        client = TelegramService.client(session_string)
        await client.connect()
        found: List[Tuple[str, int]] = []
        scanned_messages = 0
        try:
            entity = await client.get_entity(dialog_ref)
            iter_limit = None if int(limit or 0) <= 0 else int(limit)
            async for message in client.iter_messages(entity, limit=iter_limit):
                scanned_messages += 1
                text = getattr(message, "message", None) or ""
                for link in extract_telegram_links(text):
                    found.append((link, int(getattr(message, "id", 0) or 0)))
            return scanned_messages, len(found), found
        finally:
            await client.disconnect()

    @staticmethod
    async def scan_link(session_string: str, link: str) -> ScanResult:
        normalized = normalize_telegram_link(link)
        if not normalized:
            return ScanResult("invalid", "invalid", reason="رابط غير صالح")

        client = TelegramService.client(session_string)
        await client.connect()
        try:
            invite_hash = invite_hash_from_link(normalized)
            if invite_hash:
                return await TelegramService._scan_private_invite(client, invite_hash)

            public_ref = public_entity_ref_from_link(normalized)
            if not public_ref:
                return ScanResult("private_unknown", "unknown", reason="رابط مركب أو غير قابل للفحص بدون دخول")

            try:
                entity = await client.get_entity(public_ref)
            except (UsernameInvalidError, UsernameNotOccupiedError):
                return ScanResult("expired", "unknown", reason="اسم مستخدم غير موجود أو غير صالح")

            return await TelegramService._classify_entity(client, entity)

        except FloodWaitError as e:
            return ScanResult("scan_failed", "unknown", reason=f"FloodWait {int(e.seconds)} seconds")
        except Exception as e:
            err = str(e)[:300]
            lowered = err.lower()
            if "not found" in lowered or "nobody is using" in lowered or "username" in lowered and "invalid" in lowered:
                return ScanResult("expired", "unknown", reason=err)
            return ScanResult("scan_failed", "unknown", reason=err)
        finally:
            await client.disconnect()

    @staticmethod
    async def _scan_private_invite(client: TelegramClient, invite_hash: str) -> ScanResult:
        try:
            result = await client(CheckChatInviteRequest(invite_hash))
        except (InviteHashExpiredError, InviteHashInvalidError):
            return ScanResult("expired", "unknown", reason="رابط دعوة منتهي أو غير صالح")
        except FloodWaitError as e:
            return ScanResult("scan_failed", "unknown", reason=f"FloodWait {int(e.seconds)} seconds")
        except Exception as e:
            return ScanResult("private_unknown", "unknown", reason=str(e)[:300])

        # إذا كان الحساب موجوداً مسبقاً داخل المجموعة، قد يرجع ChatInviteAlready وفيه chat
        if isinstance(result, types.ChatInviteAlready):
            return await TelegramService._classify_entity(client, result.chat)

        title = getattr(result, "title", None)
        participants = int(getattr(result, "participants_count", 0) or 0)
        broadcast = bool(getattr(result, "broadcast", False))
        megagroup = bool(getattr(result, "megagroup", False))
        channel = bool(getattr(result, "channel", False))

        if broadcast:
            return ScanResult("valid_channel", "channel", title=title, subscribers_count=participants, reason="رابط دعوة قناة / مشتركين")
        if megagroup or not channel:
            return ScanResult("valid_group", "group", title=title, members_count=participants, reason="رابط دعوة مجموعة / أعضاء")
        return ScanResult("private_unknown", "unknown", title=title, members_count=participants, reason="رابط دعوة خاص غير مؤكد النوع")

    @staticmethod
    async def _classify_entity(client: TelegramClient, entity) -> ScanResult:
        title = getattr(entity, "title", None) or getattr(entity, "first_name", None) or getattr(entity, "username", None)
        entity_id = str(getattr(entity, "id", ""))

        if isinstance(entity, types.User):
            if bool(getattr(entity, "bot", False)):
                return ScanResult("bot_link", "bot", entity_id=entity_id, title=title, reason="رابط بوت")
            return ScanResult("user_link", "user", entity_id=entity_id, title=title, reason="رابط مستخدم")

        if isinstance(entity, types.Chat):
            members = 0
            try:
                full = await client(GetFullChatRequest(entity.id))
                members = int(getattr(full.full_chat, "participants_count", 0) or 0)
            except Exception:
                pass
            return ScanResult("valid_group", "group", entity_id=entity_id, title=title, members_count=members, reason="مجموعة عادية")

        if isinstance(entity, types.Channel):
            participants = 0
            try:
                full = await client(GetFullChannelRequest(entity))
                participants = int(getattr(full.full_chat, "participants_count", 0) or 0)
            except Exception:
                pass

            if bool(getattr(entity, "megagroup", False)):
                return ScanResult("valid_group", "group", entity_id=entity_id, title=title, members_count=participants, reason="Supergroup / أعضاء")

            if bool(getattr(entity, "broadcast", False)):
                return ScanResult("valid_channel", "channel", entity_id=entity_id, title=title, subscribers_count=participants, reason="Channel / مشتركين")

            return ScanResult("valid_group", "group", entity_id=entity_id, title=title, members_count=participants, reason="Channel object غير broadcast")

        return ScanResult("private_unknown", "unknown", entity_id=entity_id, title=title, reason="نوع غير معروف")

    @staticmethod
    async def send_links_to_saved_messages(session_string: str, campaign_name: str, account_label: str,
                                           links: Sequence[str], chunk_size: int = SAVED_MESSAGE_CHUNK_SIZE,
                                           campaign_account_id: int = 0) -> int:
        client = TelegramService.client(session_string)
        await client.connect()
        sent_links = 0
        try:
            total = len(links)
            for part_number, part_links in enumerate(chunks(list(links), chunk_size), start=1):
                start_no = sent_links + 1
                end_no = sent_links + len(part_links)
                lines = [
                    f"📦 دفعة روابط محفوظة",
                    f"الحملة: {campaign_name}",
                    f"الحساب: {account_label}",
                    f"رقم حساب الحملة: {campaign_account_id}",
                    f"الجزء: {part_number}",
                    f"الروابط: {start_no} - {end_no} من أصل {total}",
                    "",
                ]
                for idx, link in enumerate(part_links, start=start_no):
                    lines.append(f"{idx}. {link}")
                await client.send_message("me", "\n".join(lines), link_preview=False)
                sent_links += len(part_links)
                await asyncio.sleep(1.0)
            return sent_links
        finally:
            await client.disconnect()


# ============================
# Exporter / التصدير
# ============================


class Exporter:
    def __init__(self, db: Database):
        self.db = db

    def export_campaign_zip(self, admin_id: int, campaign_id: int) -> Path:
        campaign = self._get_campaign(admin_id, campaign_id)
        if not campaign:
            raise ValueError("الحملة غير موجودة")

        folder = EXPORTS_DIR / f"campaign_{campaign_id}_{safe_filename(campaign['name'])}"
        folder.mkdir(parents=True, exist_ok=True)

        summary_path = folder / "summary.txt"
        summary_path.write_text(self._campaign_summary_text(campaign), encoding="utf-8")

        # ملفات كل حساب
        for ca in self.db.get_campaign_accounts(campaign_id):
            rows = self.db.get_assignments_for_campaign_account(ca["id"])
            label = ca["name"] or ca["username"] or f"account_{ca['account_order']:02d}"
            filename = f"account_{ca['account_order']:02d}_{safe_filename(label)}.txt"
            content = [
                f"Campaign: {campaign['name']}",
                f"Account order: {ca['account_order']}",
                f"Account name: {label}",
                f"Total assigned: {len(rows)}",
                "",
            ]
            for row in rows:
                content.append(f"{row['order_index']}. {row['link']}")
            (folder / filename).write_text("\n".join(content), encoding="utf-8")

        # ملفات التصنيف
        status_files = {
            "valid_channel": "channels_subscribers.txt",
            "expired": "expired_links.txt",
            "user_link": "user_links.txt",
            "bot_link": "bot_links.txt",
            "private_unknown": "private_unknown_links.txt",
            "scan_failed": "scan_failed_links.txt",
            "pending": "unchecked_pending_links.txt",
        }
        for status, filename in status_files.items():
            rows = self.db.get_links_by_status(admin_id, [status])
            lines = [f"Status: {status}", f"Count: {len(rows)}", ""]
            for row in rows:
                extra = f" | {row['title'] or ''} | {row['reason'] or ''}".strip()
                lines.append(f"{row['normalized_link']}{extra}")
            (folder / filename).write_text("\n".join(lines), encoding="utf-8")

        # روابط سليمة متبقية غير موزعة
        remaining_links = self._remaining_unassigned_valid_groups(admin_id, campaign_id)
        lines = [f"Remaining unassigned valid groups: {len(remaining_links)}", ""] + remaining_links
        (folder / "remaining_unassigned_links.txt").write_text("\n".join(lines), encoding="utf-8")

        zip_path = EXPORTS_DIR / f"campaign_{campaign_id}_{safe_filename(campaign['name'])}.zip"
        if zip_path.exists():
            zip_path.unlink()
        with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED) as zf:
            for file_path in sorted(folder.glob("*.txt")):
                zf.write(file_path, arcname=file_path.name)
        return zip_path

    def _get_campaign(self, admin_id: int, campaign_id: int) -> Optional[sqlite3.Row]:
        with self.db.connect() as conn:
            return conn.execute("SELECT * FROM campaigns WHERE admin_id=? AND id=?", (admin_id, campaign_id)).fetchone()

    def _campaign_summary_text(self, campaign: sqlite3.Row) -> str:
        return "\n".join([
            "تقرير توزيع الروابط",
            "====================",
            f"اسم الحملة: {campaign['name']}",
            f"رقم الحملة: {campaign['id']}",
            f"تاريخ الإنشاء: {campaign['created_at']}",
            "",
            f"الروابط السليمة valid_group: {campaign['total_valid_links']}",
            f"كل حساب يأخذ: {campaign['links_per_account']}",
            f"الحسابات المطلوبة: {campaign['required_accounts']}",
            f"الحسابات المضافة: {campaign['provided_accounts']}",
            f"تم توزيع: {campaign['assigned_links']}",
            f"المتبقي غير موزع: {campaign['remaining_links']}",
            f"الحالة: {campaign['status']}",
        ])

    def _remaining_unassigned_valid_groups(self, admin_id: int, campaign_id: int) -> List[str]:
        with self.db.connect() as conn:
            rows = conn.execute(
                """
                SELECT l.normalized_link
                FROM links l
                WHERE l.admin_id=? AND l.status='valid_group'
                  AND l.id NOT IN (SELECT link_id FROM assignments WHERE campaign_id=?)
                ORDER BY l.id ASC
                """,
                (admin_id, campaign_id),
            ).fetchall()
        return [row["normalized_link"] for row in rows]


# ============================
# Bot Handler / واجهة البوت
# ============================


class SafeLinkBot:
    def __init__(self):
        self.db = Database(DB_PATH)
        self.exporter = Exporter(self.db)
        self.app: Optional[Application] = None

    # ---------- Security ----------
    def is_owner(self, user_id: int) -> bool:
        return int(user_id) == OWNER_ID

    async def reject_if_not_owner(self, update: Update) -> bool:
        user = update.effective_user
        if not user or not self.is_owner(user.id):
            if update.message:
                await update.message.reply_text("❌ ليس لديك صلاحية لاستخدام هذا البوت.")
            elif update.callback_query:
                await update.callback_query.answer("❌ لا توجد صلاحية", show_alert=True)
            return True
        return False

    # ---------- Menus ----------
    async def start(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        if await self.reject_if_not_owner(update):
            return
        context.user_data.clear()
        await update.message.reply_text("🎮 لوحة إدارة الروابط", reply_markup=self.main_menu())

    def main_menu(self) -> InlineKeyboardMarkup:
        keyboard = [
            [InlineKeyboardButton("👥 حسابات الفحص والتوزيع", callback_data="menu_accounts")],
            [InlineKeyboardButton("📥 استيراد روابط من قناة التجميع", callback_data="menu_import")],
            [InlineKeyboardButton("🧪 فحص الروابط بحسابات الفحص", callback_data="scan_links")],
            [InlineKeyboardButton("📊 إحصائيات الفحص", callback_data="stats")],
            [InlineKeyboardButton("📦 إنشاء حملة توزيع", callback_data="create_campaign")],
            [InlineKeyboardButton("📌 إرسال الدفعات إلى Saved Messages", callback_data="send_saved")],
            [InlineKeyboardButton("📤 تصدير ملفات TXT/ZIP", callback_data="export_latest")],
        ]
        return InlineKeyboardMarkup(keyboard)

    def accounts_menu(self) -> InlineKeyboardMarkup:
        keyboard = [
            [InlineKeyboardButton("➕ إضافة حساب فحص scanner", callback_data="add_scanner")],
            [InlineKeyboardButton("➕ إضافة حساب توزيع distribution", callback_data="add_distribution")],
            [InlineKeyboardButton("📋 عرض الحسابات", callback_data="show_accounts")],
            [InlineKeyboardButton("🔙 رجوع", callback_data="back_main")],
        ]
        return InlineKeyboardMarkup(keyboard)

    # ---------- Callback ----------
    async def handle_callback(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        if await self.reject_if_not_owner(update):
            return
        query = update.callback_query
        await query.answer()
        data = query.data
        admin_id = query.from_user.id

        if data == "back_main":
            context.user_data.clear()
            await query.edit_message_text("🎮 لوحة إدارة الروابط", reply_markup=self.main_menu())
            return

        if data == "menu_accounts":
            await query.edit_message_text("👥 إدارة حسابات الفحص والتوزيع", reply_markup=self.accounts_menu())
            return

        if data in {"add_scanner", "add_distribution"}:
            role = "scanner" if data == "add_scanner" else "distribution"
            context.user_data["mode"] = "add_account"
            context.user_data["role"] = role
            await query.edit_message_text(
                f"أرسل StringSession للحساب الذي تريد إضافته كـ {role}.\n\n"
                "ملاحظة: حسابات scanner للفحص فقط، وحسابات distribution لاستلام الدفعات فقط."
            )
            return

        if data == "show_accounts":
            await self.show_accounts(query, admin_id)
            return

        if data == "menu_import":
            scanner_count = len(self.db.get_accounts(admin_id, "scanner"))
            if scanner_count == 0:
                await query.edit_message_text("❌ أضف حساب فحص scanner أولاً.", reply_markup=self.accounts_menu())
                return
            context.user_data["mode"] = "import_dialog"
            await query.edit_message_text(
                "أرسل رابط أو يوزر قناة التجميع التي تحتوي الروابط.\n\n"
                "مثال:\n"
                "@my_collect_channel\n"
                "أو\n"
                "https://t.me/my_collect_channel\n\n"
                "يمكنك اختيارياً كتابة limit بعد مسافة، مثال:\n"
                "@my_collect_channel 5000\n\n"
                "إذا لم تكتب limit سيتم استخدام DEFAULT_IMPORT_LIMIT."
            )
            return

        if data == "scan_links":
            await self.scan_links(query, admin_id)
            return

        if data == "stats":
            await self.send_stats(query, admin_id)
            return

        if data == "create_campaign":
            await self.create_campaign(query, admin_id)
            return

        if data == "send_saved":
            await self.send_saved_messages(query, admin_id)
            return

        if data == "export_latest":
            await self.export_latest(query, admin_id, context)
            return

    async def handle_text(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        if await self.reject_if_not_owner(update):
            return
        mode = context.user_data.get("mode")
        if not mode:
            await update.message.reply_text("استخدم الأزرار من /start")
            return

        if mode == "add_account":
            await self.handle_add_account_text(update, context)
            return

        if mode == "import_dialog":
            await self.handle_import_dialog_text(update, context)
            return

    # ---------- Accounts ----------
    async def handle_add_account_text(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        admin_id = update.effective_user.id
        role = context.user_data.get("role")
        session_string = update.message.text.strip()

        await update.message.reply_text("🔎 جاري اختبار الجلسة...")
        try:
            ok, me = await TelegramService.test_session(session_string)
        except Exception as e:
            await update.message.reply_text(f"❌ فشل اختبار الجلسة: {str(e)[:300]}")
            return

        if not ok or not me:
            await update.message.reply_text("❌ الجلسة غير صالحة أو الحساب غير مصرح.")
            return

        phone = getattr(me, "phone", None) or ""
        name = " ".join(x for x in [getattr(me, "first_name", None), getattr(me, "last_name", None)] if x) or "بدون اسم"
        username = getattr(me, "username", None) or ""

        success, msg = self.db.add_account(admin_id, role, session_string, phone, name, username)
        context.user_data.clear()
        await update.message.reply_text(
            f"{'✅' if success else '⚠️'} {msg}\n\n"
            f"الدور: {role}\n"
            f"الاسم: {name}\n"
            f"اليوزر: @{username if username else 'لا يوجد'}",
            reply_markup=self.main_menu(),
        )

    async def show_accounts(self, query, admin_id: int):
        rows = self.db.get_accounts(admin_id)
        if not rows:
            await query.edit_message_text("لا توجد حسابات مضافة.", reply_markup=self.accounts_menu())
            return
        lines = ["📋 الحسابات المضافة:", ""]
        for row in rows:
            lines.append(
                f"#{row['id']} | {row['role']} | {row['name'] or 'بدون اسم'} | "
                f"@{row['username'] or 'لا يوجد'} | {row['phone'] or 'لا يوجد رقم'}"
            )
        await query.edit_message_text("\n".join(lines), reply_markup=self.accounts_menu())

    # ---------- Import ----------
    async def handle_import_dialog_text(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        admin_id = update.effective_user.id
        text = update.message.text.strip()
        parts = text.split()
        dialog_ref = parts[0].strip()
        limit = DEFAULT_IMPORT_LIMIT
        if len(parts) >= 2 and parts[1].isdigit():
            limit = int(parts[1])

        scanners = self.db.get_accounts(admin_id, "scanner")
        if not scanners:
            await update.message.reply_text("❌ لا توجد حسابات فحص scanner.")
            return

        session = scanners[0]["session_string"]
        await update.message.reply_text("📥 جاري استيراد الروابط من قناة/مجموعة التجميع...")
        try:
            scanned_messages, extracted_count, found = await TelegramService.import_links_from_dialog(session, dialog_ref, limit)
        except Exception as e:
            await update.message.reply_text(f"❌ فشل الاستيراد: {str(e)[:500]}")
            return

        inserted = 0
        for link, message_id in found:
            if self.db.add_link(admin_id, link, source=dialog_ref, source_message_id=message_id):
                inserted += 1
        duplicates = extracted_count - inserted
        context.user_data.clear()
        await update.message.reply_text(
            "✅ انتهى الاستيراد.\n\n"
            f"الرسائل المفحوصة: {format_count(scanned_messages)}\n"
            f"الروابط المستخرجة: {format_count(extracted_count)}\n"
            f"الجديدة المحفوظة: {format_count(inserted)}\n"
            f"المكررة/المرفوضة: {format_count(max(duplicates, 0))}",
            reply_markup=self.main_menu(),
        )

    # ---------- Scan ----------
    async def scan_links(self, query, admin_id: int):
        scanners = self.db.get_accounts(admin_id, "scanner")
        if not scanners:
            await query.edit_message_text("❌ لا توجد حسابات فحص scanner.", reply_markup=self.accounts_menu())
            return

        links = self.db.get_links_for_scan(admin_id, DEFAULT_SCAN_LIMIT)
        if not links:
            await query.edit_message_text("✅ لا توجد روابط pending أو scan_failed للفحص.", reply_markup=self.main_menu())
            return

        await query.edit_message_text(
            f"🧪 بدأ فحص {format_count(len(links))} رابط بحسابات الفحص فقط.\n"
            "قد تستغرق العملية بعض الوقت حسب عدد الروابط وحالة الشبكة."
        )

        counts: Dict[str, int] = {}
        for idx, link_row in enumerate(links):
            scanner = scanners[idx % len(scanners)]
            result = await TelegramService.scan_link(scanner["session_string"], link_row["normalized_link"])
            self.db.update_link_scan(
                link_id=link_row["id"],
                status=result.status,
                entity_type=result.entity_type,
                entity_id=result.entity_id,
                title=result.title,
                members_count=result.members_count,
                subscribers_count=result.subscribers_count,
                reason=result.reason,
                scanned_by_account_id=scanner["id"],
            )
            counts[result.status] = counts.get(result.status, 0) + 1

            # تهدئة بسيطة حتى لا يضغط على API
            if (idx + 1) % 50 == 0:
                await asyncio.sleep(2)

        lines = ["✅ انتهى الفحص.", ""]
        for status, count in sorted(counts.items()):
            lines.append(f"{status}: {format_count(count)}")
        valid = self.db.count_valid_groups(admin_id)
        required = math.ceil(valid / LINKS_PER_ACCOUNT) if valid else 0
        lines += ["", f"المجموعات السليمة valid_group: {format_count(valid)}", f"الحسابات المطلوبة: {format_count(required)}"]
        await query.message.reply_text("\n".join(lines), reply_markup=self.main_menu())

    async def send_stats(self, query, admin_id: int):
        counts = self.db.count_links(admin_id)
        valid = counts.get("valid_group", 0)
        required = math.ceil(valid / LINKS_PER_ACCOUNT) if valid else 0
        scanners = len(self.db.get_accounts(admin_id, "scanner"))
        distributors = len(self.db.get_accounts(admin_id, "distribution"))
        capacity = distributors * LINKS_PER_ACCOUNT
        lines = [
            "📊 إحصائيات الروابط",
            "",
            f"إجمالي الروابط: {format_count(counts.get('total', 0))}",
            f"pending: {format_count(counts.get('pending', 0))}",
            f"valid_group / مجموعات: {format_count(counts.get('valid_group', 0))}",
            f"valid_channel / قنوات مشتركين: {format_count(counts.get('valid_channel', 0))}",
            f"user_link: {format_count(counts.get('user_link', 0))}",
            f"bot_link: {format_count(counts.get('bot_link', 0))}",
            f"expired: {format_count(counts.get('expired', 0))}",
            f"private_unknown: {format_count(counts.get('private_unknown', 0))}",
            f"scan_failed: {format_count(counts.get('scan_failed', 0))}",
            "",
            f"حسابات الفحص scanner: {format_count(scanners)}",
            f"حسابات التوزيع distribution: {format_count(distributors)}",
            f"كل حساب يأخذ: {format_count(LINKS_PER_ACCOUNT)}",
            f"الحسابات المطلوبة للمجموعات السليمة: {format_count(required)}",
            f"الطاقة المتاحة حالياً: {format_count(capacity)}",
            f"المتبقي عند التوزيع الحالي: {format_count(max(valid - capacity, 0))}",
        ]
        await query.edit_message_text("\n".join(lines), reply_markup=self.main_menu())

    # ---------- Campaign ----------
    async def create_campaign(self, query, admin_id: int):
        campaign_name = "campaign_" + datetime.now().strftime("%Y%m%d_%H%M%S")
        ok, msg, _campaign_id = self.db.create_distribution_campaign(admin_id, campaign_name, LINKS_PER_ACCOUNT)
        await query.edit_message_text(msg, reply_markup=self.main_menu())

    async def send_saved_messages(self, query, admin_id: int):
        campaign = self.db.latest_campaign(admin_id)
        if not campaign:
            await query.edit_message_text("❌ لا توجد حملة توزيع. أنشئ حملة أولاً.", reply_markup=self.main_menu())
            return

        accounts = self.db.get_campaign_accounts(campaign["id"])
        if not accounts:
            await query.edit_message_text("❌ لا توجد حسابات داخل الحملة.", reply_markup=self.main_menu())
            return

        await query.edit_message_text(
            f"📌 جاري إرسال دفعات الحملة {campaign['name']} إلى Saved Messages.\n"
            "سيتم حفظ الروابط فقط، بدون أي انضمام تلقائي."
        )

        total_sent = 0
        errors = []
        for ca in accounts:
            assigned = self.db.get_assignments_for_campaign_account(ca["id"])
            links = [row["link"] for row in assigned]
            if not links:
                continue
            label = ca["name"] or ca["username"] or f"account_{ca['account_order']:02d}"
            try:
                sent = await TelegramService.send_links_to_saved_messages(
                    session_string=ca["session_string"],
                    campaign_name=campaign["name"],
                    account_label=label,
                    links=links,
                    chunk_size=SAVED_MESSAGE_CHUNK_SIZE,
                    campaign_account_id=ca["id"],
                )
                total_sent += sent
                # سجل الأجزاء المرسلة
                parts_count = math.ceil(len(links) / SAVED_MESSAGE_CHUNK_SIZE)
                for part_number, part_links in enumerate(chunks(links, SAVED_MESSAGE_CHUNK_SIZE), start=1):
                    self.db.mark_saved_message_part(
                        campaign_id=campaign["id"],
                        campaign_account_id=ca["id"],
                        account_id=ca["account_id"],
                        part_number=part_number,
                        links_count=len(part_links),
                        status="sent",
                    )
            except FloodWaitError as e:
                errors.append(f"{label}: FloodWait {int(e.seconds)}s")
            except Exception as e:
                errors.append(f"{label}: {str(e)[:200]}")

        text = [
            "✅ انتهى إرسال الدفعات إلى Saved Messages.",
            f"إجمالي الروابط المحفوظة: {format_count(total_sent)}",
        ]
        if errors:
            text += ["", "⚠️ أخطاء:"] + errors[:15]
        await query.message.reply_text("\n".join(text), reply_markup=self.main_menu())

    async def export_latest(self, query, admin_id: int, context: ContextTypes.DEFAULT_TYPE):
        campaign = self.db.latest_campaign(admin_id)
        if not campaign:
            await query.edit_message_text("❌ لا توجد حملة للتصدير.", reply_markup=self.main_menu())
            return
        await query.edit_message_text("📤 جاري إنشاء ملف ZIP...")
        try:
            zip_path = self.exporter.export_campaign_zip(admin_id, campaign["id"])
        except Exception as e:
            await query.message.reply_text(f"❌ فشل التصدير: {str(e)[:500]}", reply_markup=self.main_menu())
            return

        with zip_path.open("rb") as f:
            await query.message.reply_document(
                document=InputFile(f, filename=zip_path.name),
                caption="✅ ملف التوزيع والتقارير TXT/ZIP جاهز."
            )
        await query.message.reply_text("🎮 رجوع للوحة", reply_markup=self.main_menu())

    # ---------- Run ----------
    def run(self):
        self.app = Application.builder().token(BOT_TOKEN).build()
        self.app.add_handler(CommandHandler("start", self.start))
        self.app.add_handler(CallbackQueryHandler(self.handle_callback))
        self.app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, self.handle_text))
        print("🤖 Safe Link Distribution Bot is running")
        print(f"📁 DATA_DIR: {DATA_DIR.resolve()}")
        print(f"🗄️ DB_PATH: {DB_PATH.resolve()}")
        print("✅ لا يوجد في هذا الكود أي انضمام جماعي تلقائي للروابط.")
        self.app.run_polling()


if __name__ == "__main__":
    SafeLinkBot().run()
