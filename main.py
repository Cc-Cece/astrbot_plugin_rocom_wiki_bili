from __future__ import annotations

import asyncio
import fnmatch
import inspect
import json
from typing import Any, Callable
from dataclasses import dataclass
from pathlib import Path
import re
from html import unescape
import sqlite3
import threading
import time
from urllib.parse import quote, unquote
from urllib.error import HTTPError, URLError
from urllib.parse import urlencode
from urllib.request import Request, urlopen

from astrbot.api import AstrBotConfig, logger
from astrbot.api.event import AstrMessageEvent, filter
from astrbot.api.message_components import Image, Node, Nodes, Plain
from astrbot.api.star import Context, Star, register


TYPE_EFFECT_CHART: dict[str, dict[str, list[str]]] = {
    "普通": {"strong": [], "resist": ["地", "幽", "机械"]},
    "草": {"strong": ["水", "光", "地"], "resist": ["火", "龙", "毒", "虫", "翼", "机械"]},
    "火": {"strong": ["草", "冰", "虫", "机械"], "resist": ["水", "地", "龙"]},
    "水": {"strong": ["火", "地", "机械"], "resist": ["草", "冰", "龙"]},
    "光": {"strong": ["幽", "恶"], "resist": ["草", "冰"]},
    "地": {"strong": ["火", "冰", "电", "毒"], "resist": ["草", "武"]},
    "冰": {"strong": ["草", "地", "龙", "翼"], "resist": ["火", "冰", "机械"]},
    "龙": {"strong": ["龙"], "resist": ["机械"]},
    "电": {"strong": ["水", "翼"], "resist": ["草", "地", "龙", "电"]},
    "毒": {"strong": ["草", "萌"], "resist": ["地", "毒", "幽", "机械"]},
    "虫": {"strong": ["草", "恶", "幻"], "resist": ["火", "毒", "武", "翼", "萌", "幽", "机械"]},
    "武": {"strong": ["普通", "地", "冰", "恶", "机械"], "resist": ["毒", "虫", "翼", "萌", "幽", "幻"]},
    "翼": {"strong": ["草", "虫", "武"], "resist": ["地", "龙", "电", "机械"]},
    "萌": {"strong": ["龙", "武", "恶"], "resist": ["火", "毒", "机械"]},
    "幽": {"strong": ["光", "幽", "幻"], "resist": ["普通", "恶"]},
    "恶": {"strong": ["毒", "萌", "幽"], "resist": ["光", "武", "恶"]},
    "机械": {"strong": ["地", "冰", "萌"], "resist": ["火", "水", "电", "机械"]},
    "幻": {"strong": ["毒", "武"], "resist": ["光", "机械", "幻"]},
}


def _split_csv(raw: str) -> list[str]:
    if not raw:
        return []
    return [part.strip() for part in re.split(r"[,，;；\n]+", raw) if part.strip()]


def _shorten(text: str, limit: int) -> str:
    text = (text or "").strip()
    if len(text) <= limit:
        return text
    return text[: max(0, limit - 3)] + "..."


def _dedupe_preserve_order(items: list[str]) -> list[str]:
    seen: set[str] = set()
    out: list[str] = []
    for item in items:
        if item in seen:
            continue
        seen.add(item)
        out.append(item)
    return out


def _join_items(items: list[str], fallback: str = "-") -> str:
    cleaned = [item for item in items if item]
    return "、".join(cleaned) if cleaned else fallback


def _limit_items(items: list[str], limit: int) -> str:
    if len(items) <= limit:
        return _join_items(items)
    head = _join_items(items[:limit])
    return f"{head}（其余 {len(items) - limit} 项略）"


def _safe_slug_segment(name: str) -> str:
    cleaned = name.replace("/", "_").replace("\\", "_")
    cleaned = re.sub(r"[\0-\x1f<>:\"|?*]+", "_", cleaned)
    cleaned = cleaned.strip().strip(".")
    return cleaned or "page"


def _direct_file_url(image_name: str) -> str:
    filename = str(image_name).replace(" ", "_")
    return f"https://wiki.biligame.com/rocom/Special:FilePath/{quote(filename, safe=':_-().')}"


def _wiki_page_url(title: str, url: str | None = None) -> str:
    if url:
        cleaned = url.strip()
        if cleaned:
            return cleaned
    return f"https://wiki.biligame.com/rocom/{quote(title, safe=':_-().')}"


def _clean_plain_text(text: str) -> str:
    cleaned = text or ""
    cleaned = cleaned.replace("\r", "")
    cleaned = re.sub(r"<br\s*/?>", "\n", cleaned, flags=re.IGNORECASE)
    cleaned = re.sub(r"\[\[([^\]|]+\|)?([^\]]+)\]\]", r"\2", cleaned)
    cleaned = re.sub(r"\[https?://[^\s\]]+\s+([^\]]+)\]", r"\1", cleaned)
    cleaned = re.sub(r"<[^>]+>", "", cleaned)
    cleaned = re.sub(r"[ \t]+\n", "\n", cleaned)
    cleaned = re.sub(r"\n{3,}", "\n\n", cleaned)
    cleaned = re.sub(r"[ \t]{2,}", " ", cleaned)
    return cleaned.strip()


def _clean_markdown_text(markdown_text: str) -> str:
    text = markdown_text or ""
    text = re.sub(r"<img[^>]+>", "", text, flags=re.IGNORECASE)
    text = re.sub(r"!\[([^\]]*)\]\([^)]+\)", r"\1", text)
    text = re.sub(r"\[([^\]]+)\]\([^)]+\)", r"\1", text)
    text = re.sub(r"^\s{0,3}#{1,6}\s*", "", text, flags=re.MULTILINE)
    text = re.sub(r"^\s*[-*+]\s+", "- ", text, flags=re.MULTILINE)
    text = re.sub(r"^\s*\d+\.\s+", "- ", text, flags=re.MULTILINE)
    text = re.sub(r"`{1,3}", "", text)
    text = re.sub(r"^\s*\|.*\|\s*$", "", text, flags=re.MULTILINE)
    return _clean_plain_text(text)


def _extract_template_block(wikitext: str) -> tuple[str, dict[str, str]]:
    text = (wikitext or "").replace("\r\n", "\n")
    start = text.find("{{")
    if start < 0:
        return "", {}

    lines = text[start:].splitlines()
    if not lines:
        return "", {}

    first = lines[0].strip()
    if not first.startswith("{{"):
        return "", {}

    header = first[2:].strip()
    params: dict[str, str] = {}
    current_key = ""

    for raw_line in lines[1:]:
        line = raw_line.rstrip()
        stripped = line.strip()
        if not stripped:
            continue
        if stripped == "}}":
            break
        if stripped.startswith("|"):
            content = stripped[1:]
            if "=" in content:
                key, value = content.split("=", 1)
                current_key = key.strip()
                params[current_key] = value.strip()
            else:
                current_key = ""
        elif current_key:
            params[current_key] = f"{params[current_key]}\n{stripped}".strip()

    return header, params


def _remove_template_block(wikitext: str) -> str:
    text = (wikitext or "").replace("\r\n", "\n")
    lines = text.splitlines()
    if not lines:
        return ""
    if not lines[0].lstrip().startswith("{{"):
        return text

    for idx, raw_line in enumerate(lines):
        if raw_line.strip() == "}}":
            return "\n".join(lines[idx + 1 :]).strip()
    return text


def _clean_wikitext_body(wikitext: str) -> str:
    text = _remove_template_block(wikitext or "")
    if not text:
        return ""

    text = re.sub(r"<!--.*?-->", " ", text, flags=re.DOTALL)
    text = re.sub(r"\{\|.*?\|\}", "\n", text, flags=re.DOTALL)
    text = re.sub(r"\[\[(?:文件|File|分类|Category):[^\]]+\]\]", " ", text, flags=re.IGNORECASE)
    text = re.sub(r"\{\{[^{}]*\}\}", " ", text)
    text = re.sub(r"\[\[([^\]|]+\|)?([^\]]+)\]\]", r"\2", text)
    text = re.sub(r"\[https?://[^\s\]]+\s+([^\]]+)\]", r"\1", text)
    text = re.sub(r"^\s*=+\s*(.*?)\s*=+\s*$", r"\1", text, flags=re.MULTILINE)
    text = re.sub(r"^\s*[*#:;]+\s*", "- ", text, flags=re.MULTILINE)
    text = re.sub(r"<br\s*/?>", "\n", text, flags=re.IGNORECASE)
    text = re.sub(r"<[^>]+>", " ", text)
    text = re.sub(r"[{}[\]]+", " ", text)
    return _clean_plain_text(text)


def _normalize_field_value(key: str, value: str) -> str:
    cleaned = _clean_plain_text(value)
    if not cleaned:
        return ""

    if key in {"技能", "血脉技能", "可学技能石", "分布地区"}:
        items = [item for item in re.split(r"[,，/、\n]+", cleaned) if item.strip()]
        cleaned = "、".join(dict.fromkeys(item.strip() for item in items))
    elif key == "图鉴课题":
        items = [item.strip() for item in cleaned.splitlines() if item.strip()]
        cleaned = "\n".join(f"- {item}" for item in items) if items else cleaned

    return cleaned.strip()


def _extract_spirit_types_from_params(params: dict[str, str]) -> list[str]:
    raw_types: list[str] = []
    for key in ("主属性", "2属性"):
        raw = params.get(key, "")
        cleaned = _clean_plain_text(raw)
        if not cleaned:
            continue
        for item in re.split(r"[、,/，\s]+", cleaned):
            name = item.strip().replace("系", "")
            if name and name in TYPE_EFFECT_CHART:
                raw_types.append(name)
    return _dedupe_preserve_order(raw_types)


def _compute_spirit_type_effectiveness(spirit_types: list[str]) -> dict[str, list[str]]:
    weak_4x: list[str] = []
    weak_2x: list[str] = []
    resist_half: list[str] = []
    resist_quarter: list[str] = []

    for attack_type, cfg in TYPE_EFFECT_CHART.items():
        multiplier = 1.0
        for defend_type in spirit_types:
            if defend_type in cfg.get("strong", []):
                multiplier *= 2.0
            if defend_type in cfg.get("resist", []):
                multiplier *= 0.5

        if multiplier >= 4.0:
            weak_4x.append(attack_type)
        elif multiplier > 1.0:
            weak_2x.append(attack_type)
        elif multiplier <= 0.25:
            resist_quarter.append(attack_type)
        elif multiplier < 1.0:
            resist_half.append(attack_type)

    return {
        "weak_4x": weak_4x,
        "weak_2x": weak_2x,
        "resist_half": resist_half,
        "resist_quarter": resist_quarter,
    }


def _first_non_empty_field(params: dict[str, str], keys: tuple[str, ...]) -> str:
    for key in keys:
        value = _normalize_field_value(key, params.get(key, ""))
        if value:
            return value
    return ""


def _summary_from_content(title: str, markdown_text: str, wikitext: str, params: dict[str, str], limit: int = 180) -> str:
    summary = _first_non_empty_field(
        params,
        ("精灵描述", "效果", "用途", "描述", "来源"),
    )
    if not summary and markdown_text:
        summary = _clean_markdown_text(markdown_text)
    if not summary:
        summary = _clean_wikitext_body(wikitext)
    if not summary:
        summary = title
    return _shorten(summary, limit)


def _config_str(config: dict[str, Any], key: str, default: str = "") -> str:
    value = config.get(key, default)
    if value is None:
        return default
    return str(value).strip()


def _config_int(config: dict[str, Any], key: str, default: int) -> int:
    value = config.get(key, default)
    try:
        return int(value)
    except (TypeError, ValueError):
        return default


def _config_bool(config: dict[str, Any], key: str, default: bool) -> bool:
    value = config.get(key, default)
    if isinstance(value, bool):
        return value
    if value is None:
        return default
    if isinstance(value, str):
        normalized = value.strip().lower()
        if normalized in {"1", "true", "yes", "on", "是", "启用", "开启"}:
            return True
        if normalized in {"0", "false", "no", "off", "否", "关闭"}:
            return False
    return bool(value)


def _normalize_source_mode(value: str) -> str:
    normalized = (value or "auto").strip().lower()
    if normalized in {"sqlite-only", "sqlite_only"}:
        return "sqlite_only"
    if normalized in {"jsonl-only", "jsonl_only"}:
        return "jsonl_only"
    if normalized in {"sqlite-jsonl-merge", "sqlite_jsonl_merge", "merge"}:
        return "sqlite_jsonl_merge"
    if normalized in {"crawler-only", "crawler_only"}:
        return "crawler_only"
    return "auto"


def _normalize_update_mode(value: str) -> str:
    normalized = (value or "after_send_compare_update").strip().lower()
    if normalized in {"before_send_compare_update", "before", "pre"}:
        return "before_send_compare_update"
    if normalized in {"disabled", "off", "none"}:
        return "disabled"
    return "after_send_compare_update"


class MediaWikiClient:
    def __init__(
        self,
        api_url: str = "https://wiki.biligame.com/rocom/api.php",
        user_agent: str = "astrbot-plugin-rocom-wiki-bili/1.0.2",
        timeout: int = 20,
        request_gate: Callable[[], None] | None = None,
    ) -> None:
        self.api_url = api_url
        self.user_agent = user_agent
        self.timeout = max(1, int(timeout))
        self.request_gate = request_gate

    def _headers(self, referer: str | None = None) -> dict[str, str]:
        headers = {
            "User-Agent": self.user_agent,
            "Accept": "application/json, text/javascript, */*; q=0.01",
            "Accept-Language": "zh-CN,zh;q=0.9,en;q=0.8",
            "Cache-Control": "no-cache",
            "Pragma": "no-cache",
        }
        if referer:
            headers["Referer"] = referer
        return headers

    def get_json(self, params: dict[str, Any]) -> dict[str, Any]:
        query = urlencode(params, doseq=True)
        request = Request(
            f"{self.api_url}?{query}",
            headers=self._headers("https://wiki.biligame.com/rocom/"),
        )
        retries = 3
        for attempt in range(retries):
            try:
                if self.request_gate:
                    self.request_gate()
                with urlopen(request, timeout=self.timeout) as response:
                    payload = response.read().decode("utf-8")
                data = json.loads(payload)
                return data if isinstance(data, dict) else {}
            except HTTPError as error:
                if error.code not in {429, 500, 502, 503, 504} or attempt >= retries - 1:
                    raise
                time.sleep(1.2 * (attempt + 1))
            except URLError:
                if attempt >= retries - 1:
                    raise
                time.sleep(1.2 * (attempt + 1))
        raise RuntimeError("Failed to fetch JSON from MediaWiki API")

    def get_text(self, url: str, referer: str | None = None) -> str:
        request = Request(url, headers=self._headers(referer))
        if self.request_gate:
            self.request_gate()
        with urlopen(request, timeout=self.timeout) as response:
            return response.read().decode("utf-8", errors="replace")

    @staticmethod
    def _strip_html_tags(text: str) -> str:
        text = re.sub(r"<script\b.*?</script>", " ", text, flags=re.IGNORECASE | re.DOTALL)
        text = re.sub(r"<style\b.*?</style>", " ", text, flags=re.IGNORECASE | re.DOTALL)
        text = re.sub(r"<[^>]+>", " ", text)
        text = unescape(text)
        text = re.sub(r"\s+", " ", text)
        return text.strip()

    def _search_titles_from_html(self, keyword: str, limit: int = 8) -> list[str]:
        search_url = "https://searchwiki.biligame.com/rocom/index.php?" + urlencode(
            {
                "search": keyword,
                "title": "Special:搜索",
            }
        )
        html = self.get_text(search_url, referer="https://searchwiki.biligame.com/rocom/")
        pattern = re.compile(
            r'<a[^>]+href="https://searchwiki\.biligame\.com/rocom/([^"#?]+)"[^>]*>(.*?)</a>',
            re.IGNORECASE | re.DOTALL,
        )
        titles: list[str] = []
        for href, anchor in pattern.findall(html):
            title = unquote(href).strip()
            if not title or title.lower().startswith("special:"):
                continue
            text = self._strip_html_tags(anchor)
            candidate = text or title
            candidate = candidate.split(" ", 1)[0].strip()
            if candidate and candidate not in titles:
                titles.append(candidate)
            if len(titles) >= limit:
                break
        if not titles:
            alt_pattern = re.compile(r'<a[^>]+href="/rocom/([^"#?]+)"[^>]*>(.*?)</a>', re.IGNORECASE | re.DOTALL)
            for href, anchor in alt_pattern.findall(html):
                title = unquote(href).strip()
                if not title or title.lower().startswith("special:"):
                    continue
                text = self._strip_html_tags(anchor)
                candidate = text or title
                candidate = candidate.split(" ", 1)[0].strip()
                if candidate and candidate not in titles:
                    titles.append(candidate)
                if len(titles) >= limit:
                    break
        return titles[:limit]

    def search_titles(self, keyword: str, limit: int = 8) -> list[str]:
        try:
            data = self.get_json(
                {
                    "action": "query",
                    "list": "search",
                    "srsearch": keyword,
                    "srlimit": max(1, min(20, limit)),
                    "srnamespace": 0,
                    "format": "json",
                    "formatversion": 2,
                }
            )
            results = data.get("query", {}).get("search", [])
            titles: list[str] = []
            for item in results:
                title = item.get("title")
                if title:
                    titles.append(str(title))
            if titles:
                return titles
        except Exception as exc:
            logger.warning(f"[rocom] API 搜索失败，切换 HTML 搜索页：{exc}")

        try:
            return self._search_titles_from_html(keyword, limit=max(1, min(20, limit)))
        except Exception as exc:
            logger.warning(f"[rocom] HTML 搜索失败：{exc}")
            return []

    def page(
        self,
        title: str,
        *,
        include_links: bool = True,
        include_images: bool = True,
        include_categories: bool = True,
    ) -> dict[str, Any]:
        data = self.get_json(
            {
                "action": "query",
                "titles": title,
                "prop": "info|revisions|extracts",
                "inprop": "url",
                "rvprop": "ids|timestamp|user|comment|content",
                "rvslots": "main",
                "explaintext": 1,
                "exintro": 1,
                "exsectionformat": "plain",
                "format": "json",
            }
        )
        pages = data.get("query", {}).get("pages", {})
        page_data = next(iter(pages.values()), {}) if isinstance(pages, dict) else {}
        revisions = page_data.get("revisions", []) if isinstance(page_data, dict) else []
        revision = revisions[0] if revisions else {}
        slots = revision.get("slots", {}) if isinstance(revision, dict) else {}
        main_slot = slots.get("main", {}) if isinstance(slots, dict) else {}
        revision_text = None
        if isinstance(main_slot, dict):
            revision_text = main_slot.get("*") or main_slot.get("content")

        result = {
            "title": page_data.get("title", title),
            "pageid": page_data.get("pageid"),
            "ns": page_data.get("ns"),
            "url": page_data.get("fullurl"),
            "touched": page_data.get("touched"),
            "lastrevid": page_data.get("lastrevid") or revision.get("revid"),
            "contentmodel": page_data.get("contentmodel"),
            "extract": page_data.get("extract"),
            "wikitext": revision_text,
            "categories": [],
            "links": [],
            "images": [],
        }

        if include_categories:
            result["categories"] = self._collect_titles(title, "categories", "title")
        if include_links:
            result["links"] = self._collect_titles(title, "links", "title", {"plnamespace": 0})
        if include_images:
            result["images"] = self._collect_titles(title, "images", "title")

        return result

    def _collect_titles(self, title: str, prop: str, item_key: str, extra_params: dict[str, Any] | None = None) -> list[str]:
        results: list[str] = []
        continue_params: dict[str, Any] | None = None

        while True:
            params: dict[str, Any] = {
                "action": "query",
                "titles": title,
                "prop": prop,
                "format": "json",
            }
            if extra_params:
                params.update(extra_params)
            if continue_params:
                params.update(continue_params)

            data = self.get_json(params)
            pages = data.get("query", {}).get("pages", {})
            page_data = next(iter(pages.values()), {}) if isinstance(pages, dict) else {}
            items = page_data.get(prop, []) if isinstance(page_data, dict) else []
            results.extend(item.get(item_key, "") for item in items if item.get(item_key))

            continue_params = data.get("continue")
            if not continue_params:
                break

        return results


@dataclass(slots=True)
class CacheEntry:
    value: str
    ts: float


@dataclass(slots=True)
class PendingSelection:
    keyword: str
    records: list[dict[str, Any]]
    ts: float


class RocomRepository:
    _SQLITE_COLUMN_TYPES: dict[str, str] = {
        "title": "TEXT",
        "pageid": "INTEGER",
        "ns": "INTEGER",
        "url": "TEXT",
        "touched": "TEXT",
        "lastrevid": "INTEGER",
        "contentmodel": "TEXT",
        "extract": "TEXT",
        "wikitext": "TEXT",
        "categories": "TEXT",
        "links": "TEXT",
        "images": "TEXT",
        "depth": "INTEGER",
    }

    def __init__(self, sqlite_path: Path, jsonl_path: Path, markdown_root: Path) -> None:
        self.sqlite_path = sqlite_path
        self.jsonl_path = jsonl_path
        self.markdown_root = markdown_root
        self._jsonl_records: list[dict[str, Any]] | None = None
        self._sqlite_lock = threading.RLock()
        self._jsonl_lock = threading.RLock()

    def is_ready(self) -> bool:
        return self.sqlite_path.exists() or self.jsonl_path.exists()

    def _connect(self) -> sqlite3.Connection:
        connection = sqlite3.connect(self.sqlite_path, timeout=30)
        connection.row_factory = sqlite3.Row
        connection.execute("PRAGMA busy_timeout = 30000")
        return connection

    @classmethod
    def _ensure_sqlite_schema(cls, conn: sqlite3.Connection) -> None:
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS pages (
                title TEXT PRIMARY KEY,
                pageid INTEGER,
                ns INTEGER,
                url TEXT,
                touched TEXT,
                lastrevid INTEGER,
                contentmodel TEXT,
                extract TEXT,
                wikitext TEXT,
                categories TEXT,
                links TEXT,
                images TEXT,
                depth INTEGER
            )
            """
        )
        existing_columns = {str(row["name"]) for row in conn.execute("PRAGMA table_info(pages)").fetchall()}
        for column_name, column_type in cls._SQLITE_COLUMN_TYPES.items():
            if column_name == "title":
                continue
            if column_name not in existing_columns:
                conn.execute(f"ALTER TABLE pages ADD COLUMN {column_name} {column_type}")
        conn.execute("CREATE UNIQUE INDEX IF NOT EXISTS idx_pages_title ON pages(title)")

    @staticmethod
    def _row_to_dict(row: sqlite3.Row | None) -> dict[str, Any] | None:
        if row is None:
            return None
        return {key: row[key] for key in row.keys()}

    def _fetch_one(self, query: str, params: tuple[object, ...]) -> dict[str, Any] | None:
        with self._sqlite_lock:
            try:
                with self._connect() as conn:
                    row = conn.execute(query, params).fetchone()
            except sqlite3.Error as exc:
                logger.warning(f"[rocom] SQLite 查询失败（fetch_one）：{exc}")
                return None
        return self._row_to_dict(row)

    def _fetch_many(
        self,
        query: str,
        params: tuple[object, ...],
        limit: int,
    ) -> list[dict[str, Any]]:
        with self._sqlite_lock:
            try:
                with self._connect() as conn:
                    rows = conn.execute(query, params).fetchall()
            except sqlite3.Error as exc:
                logger.warning(f"[rocom] SQLite 查询失败（fetch_many）：{exc}")
                return []
        return [self._row_to_dict(row) for row in list(rows)[:limit] if row is not None]

    def _load_jsonl_records(self) -> list[dict[str, Any]]:
        with self._jsonl_lock:
            if self._jsonl_records is None:
                self._jsonl_records = self._load_jsonl_records_from_disk_locked()
            return [dict(item) for item in self._jsonl_records]

    def _load_jsonl_records_from_disk_locked(self) -> list[dict[str, Any]]:
        if not self.jsonl_path.exists():
            return []

        records: list[dict[str, Any]] = []
        with self.jsonl_path.open("r", encoding="utf-8") as handle:
            for line in handle:
                line = line.strip()
                if not line:
                    continue
                try:
                    item = json.loads(line)
                except json.JSONDecodeError:
                    continue
                if isinstance(item, dict) and item.get("title"):
                    records.append(dict(item))
        return records

    @staticmethod
    def _sort_query_rows(rows: list[dict[str, Any]], keyword: str) -> list[dict[str, Any]]:
        unique: dict[str, dict[str, Any]] = {}
        for row in rows:
            title = str(row.get("title") or "")
            if title and title not in unique:
                unique[title] = row

        def sort_key(row: dict[str, Any]) -> tuple[int, int, str]:
            title = str(row.get("title") or "")
            if title == keyword:
                rank = 0
            elif title.startswith(keyword):
                rank = 1
            else:
                rank = 2
            return (rank, len(title), title)

        return sorted(unique.values(), key=sort_key)

    def query_sqlite_title_contains(self, keyword: str, limit: int = 8) -> list[dict[str, Any]]:
        if not self.sqlite_path.exists():
            return []
        return self._fetch_many(
            """
            SELECT title, pageid, ns, url, touched, lastrevid, contentmodel, extract, wikitext, categories, links, images, depth
            FROM pages
            WHERE title LIKE ?
            ORDER BY CASE WHEN title = ? THEN 0 WHEN title LIKE ? THEN 1 ELSE 2 END, LENGTH(title)
            LIMIT 20
            """,
            (f"%{keyword}%", keyword, f"{keyword}%"),
            limit,
        )

    def query_jsonl_title_contains(self, keyword: str, limit: int = 8) -> list[dict[str, Any]]:
        rows = [record for record in self._load_jsonl_records() if keyword.lower() in str(record.get("title") or "").lower()]
        return self._sort_query_rows(rows, keyword)[:limit]

    def get_sqlite_page_by_title(self, title: str) -> dict[str, Any] | None:
        if not self.sqlite_path.exists():
            return None
        return self._fetch_one(
            """
            SELECT title, pageid, ns, url, touched, lastrevid, contentmodel, extract, wikitext, categories, links, images, depth
            FROM pages
            WHERE title = ?
            LIMIT 1
            """,
            (title,),
        )

    def get_jsonl_page_by_title(self, title: str) -> dict[str, Any] | None:
        for record in self._load_jsonl_records():
            if str(record.get("title") or "") == title:
                return record
        return None

    def read_markdown_raw(self, title: str) -> str:
        for candidate in self._iter_markdown_paths(title):
            if candidate.exists():
                return candidate.read_text(encoding="utf-8")
        return ""

    def _iter_markdown_paths(self, title: str):
        seen: set[str] = set()
        for name in (title, _safe_slug_segment(title)):
            if not name or name in seen:
                continue
            seen.add(name)
            yield self.markdown_root / f"{name}.md"

    def _upsert_page_sqlite(self, record: dict[str, Any]) -> bool:
        self.sqlite_path.parent.mkdir(parents=True, exist_ok=True)
        categories = record.get("categories", [])
        links = record.get("links", [])
        images = record.get("images", [])
        if not isinstance(categories, str):
            categories = json.dumps(categories, ensure_ascii=False)
        if not isinstance(links, str):
            links = json.dumps(links, ensure_ascii=False)
        if not isinstance(images, str):
            images = json.dumps(images, ensure_ascii=False)

        try:
            with self._sqlite_lock:
                with self._connect() as conn:
                    self._ensure_sqlite_schema(conn)
                    conn.execute(
                        """
                        INSERT INTO pages (
                            title, pageid, ns, url, touched, lastrevid, contentmodel,
                            extract, wikitext, categories, links, images, depth
                        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                        ON CONFLICT(title) DO UPDATE SET
                            pageid=excluded.pageid,
                            ns=excluded.ns,
                            url=excluded.url,
                            touched=excluded.touched,
                            lastrevid=excluded.lastrevid,
                            contentmodel=excluded.contentmodel,
                            extract=excluded.extract,
                            wikitext=excluded.wikitext,
                            categories=excluded.categories,
                            links=excluded.links,
                            images=excluded.images,
                            depth=excluded.depth
                        """,
                        (
                            record.get("title"),
                            record.get("pageid"),
                            record.get("ns"),
                            record.get("url"),
                            record.get("touched"),
                            record.get("lastrevid"),
                            record.get("contentmodel"),
                            record.get("extract"),
                            record.get("wikitext"),
                            categories,
                            links,
                            images,
                            record.get("depth"),
                        ),
                    )
                    conn.commit()
            return True
        except sqlite3.Error as exc:
            logger.warning(f"[rocom] SQLite 写入失败：{exc}")
            return False

    def _upsert_page_jsonl(self, record: dict[str, Any]) -> bool:
        self.jsonl_path.parent.mkdir(parents=True, exist_ok=True)
        title = str(record.get("title") or "").strip()
        if not title:
            return False

        with self._jsonl_lock:
            if self._jsonl_records is None:
                self._jsonl_records = self._load_jsonl_records_from_disk_locked()

            records = [dict(item) for item in self._jsonl_records]
            replaced = False
            for idx, item in enumerate(records):
                if str(item.get("title") or "") == title:
                    records[idx] = dict(record)
                    replaced = True
                    break
            if not replaced:
                records.append(dict(record))

            with self.jsonl_path.open("w", encoding="utf-8") as handle:
                for item in records:
                    handle.write(json.dumps(item, ensure_ascii=False) + "\n")

            self._jsonl_records = records
            return True

    def upsert_page(
        self,
        record: dict[str, Any],
        *,
        write_sqlite: bool = True,
        write_jsonl: bool = True,
    ) -> bool:
        wrote_any = False
        if write_sqlite:
            wrote_any = self._upsert_page_sqlite(record) or wrote_any
        if write_jsonl:
            wrote_any = self._upsert_page_jsonl(record) or wrote_any
        return wrote_any


@register("astrbot_plugin_rocom_wiki_bili", "Kanbara", "洛克王国 Wiki 本地查询插件", "1.0.0")
class RocomWikiPlugin(Star):
    def __init__(self, context: Context, config: AstrBotConfig | None = None):
        super().__init__(context)
        self.context = context
        self.config = config or {}
        self._cache: dict[str, CacheEntry] = {}
        self._pending: dict[str, PendingSelection] = {}
        self._background_tasks: set[asyncio.Task[None]] = set()
        self._inflight_queries: set[str] = set()
        self._crawler_gate_lock = threading.Lock()
        self._last_crawler_request_ts = 0.0
        self.repo: RocomRepository | None = None

    async def initialize(self):
        self.repo = RocomRepository(
            sqlite_path=self._resolve_sqlite_path(),
            jsonl_path=self._resolve_jsonl_path(),
            markdown_root=self._resolve_markdown_root(),
        )
        logger.info(f"[rocom] 插件初始化完成，sqlite={self.repo.sqlite_path}, jsonl={self.repo.jsonl_path}")

    def _resolve_sqlite_path(self) -> Path:
        plugin_root = Path(__file__).resolve().parent
        configured = _config_str(self.config, "sqlite_path", "")
        candidates: list[Path] = []
        if configured:
            p = Path(configured)
            candidates.append(p if p.is_absolute() else (plugin_root / p).resolve())
        candidates.append((plugin_root / "data" / "pages.sqlite").resolve())
        candidates.append((plugin_root.parent / "data" / "pages.sqlite").resolve())
        for candidate in candidates:
            if candidate.exists():
                return candidate
        return candidates[0]

    def _resolve_jsonl_path(self) -> Path:
        plugin_root = Path(__file__).resolve().parent
        configured = _config_str(self.config, "jsonl_path", "")
        candidates: list[Path] = []
        if configured:
            p = Path(configured)
            candidates.append(p if p.is_absolute() else (plugin_root / p).resolve())
        candidates.append((plugin_root / "data" / "pages.jsonl").resolve())
        candidates.append((plugin_root.parent / "data" / "pages.jsonl").resolve())
        for candidate in candidates:
            if candidate.exists():
                return candidate
        return candidates[0]

    def _resolve_markdown_root(self) -> Path:
        plugin_root = Path(__file__).resolve().parent
        configured = _config_str(self.config, "markdown_root", "")
        candidates: list[Path] = []
        if configured:
            p = Path(configured)
            candidates.append(p if p.is_absolute() else (plugin_root / p).resolve())
        candidates.append((plugin_root / "data" / "markdown").resolve())
        candidates.append((plugin_root.parent / "data" / "markdown").resolve())
        for candidate in candidates:
            if candidate.exists():
                return candidate
        return candidates[0]

    def _cache_ttl(self) -> int:
        return _config_int(self.config, "cache_ttl_sec", 600)

    def _pending_ttl(self) -> int:
        return max(120, min(1800, self._cache_ttl()))

    def _cache_get(self, key: str) -> str | None:
        entry = self._cache.get(key)
        if not entry:
            return None
        if time.time() - entry.ts > self._cache_ttl():
            self._cache.pop(key, None)
            return None
        return entry.value

    def _cache_set(self, key: str, value: str) -> None:
        self._cache[key] = CacheEntry(value=value, ts=time.time())

    def _compact_mode(self) -> bool:
        return _config_str(self.config, "default_reply_mode", "compact").lower() != "full"

    def _query_limit(self) -> int:
        return max(1, min(20, _config_int(self.config, "query_max_results", 8)))

    def _source_mode(self) -> str:
        return _normalize_source_mode(_config_str(self.config, "source_mode", "auto"))

    def _update_mode(self) -> str:
        return _normalize_update_mode(_config_str(self.config, "update_mode", "after_send_compare_update"))

    def _crawler_enabled(self) -> bool:
        return _config_bool(self.config, "crawler_enabled", True)

    def _crawler_timeout(self) -> int:
        return max(1, _config_int(self.config, "crawler_timeout_sec", 20))

    def _crawler_min_interval(self) -> int:
        return max(0, _config_int(self.config, "crawler_min_interval_sec", 5))

    def _recall_on_update(self) -> bool:
        return _config_bool(self.config, "recall_on_update", True)

    def _forward_enabled(self) -> bool:
        return _config_bool(self.config, "merge_forward_enabled", True)

    def _forward_threshold(self) -> int:
        return max(0, _config_int(self.config, "merge_forward_threshold", 900))

    def _forward_platforms(self) -> set[str]:
        raw = _config_str(self.config, "merge_forward_platforms", "aiocqhttp,onebot")
        return {item.lower() for item in _split_csv(raw)}

    def _crawler_keyword_blocklist(self) -> list[str]:
        raw = _config_str(self.config, "crawler_keyword_blocklist", "Help:,Template:,Special:")
        return [item for item in _split_csv(raw) if item]

    def _keyword_is_blocked_for_crawler(self, keyword: str) -> bool:
        normalized = (keyword or "").strip().lower()
        if not normalized:
            return False
        for pattern in self._crawler_keyword_blocklist():
            p = pattern.strip().lower()
            if not p:
                continue
            if "*" in p or "?" in p:
                if fnmatch.fnmatch(normalized, p):
                    return True
            elif p in normalized:
                return True
        return False

    def _wait_for_crawler_slot(self) -> None:
        min_interval = float(self._crawler_min_interval())
        if min_interval <= 0:
            return

        while True:
            with self._crawler_gate_lock:
                now = time.monotonic()
                elapsed = now - self._last_crawler_request_ts
                if elapsed >= min_interval:
                    self._last_crawler_request_ts = now
                    return
                wait_for = min_interval - elapsed
            time.sleep(max(0.0, wait_for))

    def _new_mediawiki_client(self) -> MediaWikiClient:
        return MediaWikiClient(
            timeout=self._crawler_timeout(),
            request_gate=self._wait_for_crawler_slot,
        )

    def _query_local_records(self, keyword: str) -> list[dict[str, Any]]:
        if not self.repo:
            return []

        mode = self._source_mode()
        rows: list[dict[str, Any]] = []

        if mode == "auto":
            if self.repo.sqlite_path.exists():
                rows.extend(self.repo.query_sqlite_title_contains(keyword, limit=self._query_limit()))
            elif self.repo.jsonl_path.exists():
                rows.extend(self.repo.query_jsonl_title_contains(keyword, limit=self._query_limit()))
        elif mode in {"sqlite_only", "sqlite_jsonl_merge"} and self.repo.sqlite_path.exists():
            rows.extend(self.repo.query_sqlite_title_contains(keyword, limit=self._query_limit()))
        if mode in {"jsonl_only", "sqlite_jsonl_merge"} and self.repo.jsonl_path.exists():
            rows.extend(self.repo.query_jsonl_title_contains(keyword, limit=self._query_limit()))

        return self.repo._sort_query_rows(rows, keyword)[: self._query_limit()]

    def _parse_query_message(self, event: AstrMessageEvent, keyword: str) -> tuple[str, int | None]:
        raw_text = event.get_message_str().strip()
        extracted = keyword.strip()

        match = re.match(r"^(?:[#/]\s*)?(?:洛克查|洛克查询|查百科|查词条)\s+(.*)$", raw_text)
        if match:
            extracted = match.group(1).strip()

        selected_index: int | None = None
        if extracted:
            parts = extracted.rsplit(None, 1)
            if len(parts) == 2 and parts[1].isdigit():
                selected_index = int(parts[1])
                extracted = parts[0].strip()

        return extracted or keyword.strip(), selected_index

    def _query_remote_records(self, keyword: str) -> list[dict[str, Any]]:
        if not self._crawler_enabled() or self._source_mode() not in {"auto", "crawler_only"}:
            return []
        if self._keyword_is_blocked_for_crawler(keyword):
            logger.info(f"[rocom] 关键词命中在线抓取黑名单，已跳过远程查询：{keyword}")
            return []

        client = self._new_mediawiki_client()
        try:
            titles = client.search_titles(keyword, limit=self._query_limit())
        except Exception as exc:
            logger.warning(f"[rocom] 在线搜索失败：{exc}")
            return []

        records: list[dict[str, Any]] = []
        for title in titles:
            try:
                record = client.page(title)
            except Exception as exc:
                logger.warning(f"[rocom] 在线抓取失败：{title} -> {exc}")
                continue
            records.append(record)
            self._upsert_record_if_allowed(record)

        return RocomRepository._sort_query_rows(records, keyword)[: self._query_limit()]

    def _fetch_remote_page(self, title: str) -> dict[str, Any] | None:
        if not self._crawler_enabled():
            return None
        if self._keyword_is_blocked_for_crawler(title):
            logger.info(f"[rocom] 词条命中在线抓取黑名单，已跳过远程刷新：{title}")
            return None
        try:
            record = self._new_mediawiki_client().page(title)
        except Exception as exc:
            logger.warning(f"[rocom] 在线抓取详情失败：{title} -> {exc}")
            return None
        self._upsert_record_if_allowed(record)
        return record

    @staticmethod
    def _normalize_record_list_field(value: Any) -> list[str]:
        if isinstance(value, str):
            stripped = value.strip()
            if stripped:
                try:
                    parsed = json.loads(stripped)
                except json.JSONDecodeError:
                    parsed = None
                if isinstance(parsed, list):
                    return [str(item).strip() for item in parsed if str(item).strip()]
            return []
        if isinstance(value, (list, tuple, set)):
            return [str(item).strip() for item in value if str(item).strip()]
        return []

    @classmethod
    def _normalize_record_for_compare(cls, record: dict[str, Any] | None) -> dict[str, Any]:
        if not record:
            return {}
        normalized = dict(record)
        for list_key in ("categories", "links", "images"):
            normalized[list_key] = cls._normalize_record_list_field(normalized.get(list_key))
        return normalized

    @staticmethod
    def _record_revision(record: dict[str, Any] | None) -> str:
        if not record:
            return ""
        return str(record.get("lastrevid") or record.get("touched") or "")

    @classmethod
    def _record_payload(cls, record: dict[str, Any] | None) -> str:
        return json.dumps(cls._normalize_record_for_compare(record), ensure_ascii=False, sort_keys=True, default=str)

    def _record_needs_update(self, local_record: dict[str, Any], remote_record: dict[str, Any]) -> bool:
        local_rev = self._record_revision(local_record)
        remote_rev = self._record_revision(remote_record)
        if local_rev and remote_rev and local_rev != remote_rev:
            return True
        return self._record_payload(local_record) != self._record_payload(remote_record)

    def _allow_remote_search(self) -> bool:
        return self._crawler_enabled() and self._source_mode() in {"auto", "crawler_only"}

    def _allow_remote_update(self) -> bool:
        return self._crawler_enabled() and self._source_mode() != "crawler_only" and self._update_mode() != "disabled"

    def _should_touch_local_storage(self) -> bool:
        return self._source_mode() != "crawler_only"

    def _upsert_record_if_allowed(self, record: dict[str, Any]) -> None:
        if not self.repo or not self._should_touch_local_storage():
            return
        self.repo.upsert_page(record, write_sqlite=True, write_jsonl=True)

    def _refresh_record_if_needed(self, record: dict[str, Any]) -> tuple[dict[str, Any], bool]:
        if not self._allow_remote_update():
            return record, False

        title = str(record.get("title") or "")
        if not title:
            return record, False
        if self._keyword_is_blocked_for_crawler(title):
            return record, False

        remote_record = self._fetch_remote_page(title)
        if not remote_record:
            return record, False

        if self._record_needs_update(record, remote_record):
            return remote_record, True
        return record, False

    def _supports_forward(self, event: AstrMessageEvent, detail_text: str) -> bool:
        if not self._forward_enabled():
            return False
        threshold = self._forward_threshold()
        if threshold > 0 and len(detail_text) < threshold:
            return False
        platform = (event.get_platform_name() or "").lower()
        return platform in self._forward_platforms()

    def _build_help_text(self) -> str:
        return (
            "洛克百科插件命令\n"
            "- 洛克查 关键词\n"
            "- 洛克查询 关键词\n"
            "- 洛克状态\n"
            "管理员命令\n"
            "- 洛克重载\n"
            "- 洛克清缓存\n"
        )

    def _entry_kind(self, wikitext: str) -> str:
        if "{{精灵信息" in (wikitext or ""):
            return "精灵"
        if "{{技能信息" in (wikitext or ""):
            return "技能"
        if "{{物品信息" in (wikitext or ""):
            return "物品"
        return "词条"

    def _find_main_image_component(self, title: str, wikitext: str):
        if not self.repo:
            return None
        md_text = self.repo.read_markdown_raw(title)
        if md_text:
            src_match = re.search(r'<img[^>]+src="([^"]+)"', md_text)
            if src_match:
                src = src_match.group(1).strip()
                if src.startswith("http://") or src.startswith("https://"):
                    return Image.fromURL(src)
                local_path = (self.repo.markdown_root / src).resolve()
                if local_path.exists():
                    return Image.fromFileSystem(str(local_path))

        if "{{精灵信息" in (wikitext or ""):
            local_name = _safe_slug_segment(f"页面 宠物 立绘 {title} 1.png")
            candidate = self.repo.markdown_root / "assets" / "images" / local_name
            if candidate.exists():
                return Image.fromFileSystem(str(candidate.resolve()))
            return Image.fromURL(_direct_file_url(f"页面 宠物 立绘 {title} 1.png"))

        return None

    def _extract_detail_body(self, title: str, wikitext: str, params: dict[str, str]) -> str:
        markdown_text = self.repo.read_markdown_raw(title) if self.repo else ""
        if markdown_text:
            lines: list[str] = []
            for line in _clean_markdown_text(markdown_text).splitlines():
                stripped = line.strip()
                if not stripped:
                    continue
                if stripped == title or stripped == f"# {title}":
                    continue
                lines.append(stripped)
            body = "\n".join(lines).strip()
            if body:
                return body

        body = _clean_wikitext_body(wikitext)
        if body:
            return body

        return _first_non_empty_field(params, ("精灵描述", "效果", "用途", "描述", "来源"))

    def _summary_for_row(self, row: sqlite3.Row, limit: int = 160) -> str:
        title = str(row["title"] or "")
        wikitext = str(row["wikitext"] or "")
        _, params = _extract_template_block(wikitext)
        extract_raw = _clean_plain_text(str(row["extract"] or ""))
        markdown_text = self.repo.read_markdown_raw(title) if self.repo else ""
        return _shorten(
            extract_raw or _summary_from_content(title, markdown_text, wikitext, params, limit),
            limit,
        )

    def _format_selection_text(self, keyword: str, rows: list[sqlite3.Row]) -> str:
        lines = [f"找到 {len(rows)} 条与“{keyword}”相关的词条：", ""]
        for idx, row in enumerate(rows, start=1):
            title = str(row["title"] or "")
            kind = self._entry_kind(str(row["wikitext"] or ""))
            lines.append(f"{idx}. 【{kind}】{title}")
        lines.extend(
            [
                "",
                "请直接回复对应序号查看详情。",
                "回复 0 可以取消本次选择。",
            ]
        )
        return "\n".join(lines)

    def _format_detail_text(self, row: sqlite3.Row) -> str:
        title = str(row["title"] or "")
        touched = str(row["touched"] or "-")
        page_url = str(row["url"] or "")
        wikitext = str(row["wikitext"] or "")
        kind = self._entry_kind(wikitext)
        _, params = _extract_template_block(wikitext)

        if kind == "精灵":
            return self._format_spirit_detail_text(row, params)

        extract_raw = _clean_plain_text(str(row["extract"] or ""))
        body = self._extract_detail_body(title, wikitext, params)
        primary_description = _first_non_empty_field(
            params,
            ("精灵描述", "效果", "用途", "描述", "来源"),
        )
        summary = extract_raw or _summary_from_content(
            title,
            self.repo.read_markdown_raw(title) if self.repo else "",
            wikitext,
            params,
            220,
        )

        preferred_fields = {
            "精灵": [
                "精灵名称",
                "精灵形态",
                "精灵阶段",
                "精灵类型",
                "主属性",
                "2属性",
                "特性",
                "特性描述",
                "生命",
                "物攻",
                "魔攻",
                "物防",
                "魔防",
                "速度",
                "分布地区",
                "图鉴课题",
                "技能",
                "血脉技能",
                "可学技能石",
            ],
            "技能": [
                "技能名称",
                "属性",
                "技能类别",
                "耗能",
                "威力",
                "效果",
                "描述",
            ],
            "物品": [
                "物品名称",
                "稀有度",
                "主分类",
                "次分类",
                "用途",
                "来源",
                "描述",
            ],
        }

        lines = [f"【{kind}】{title}"]
        shown_keys: set[str] = set()

        for key in preferred_fields.get(kind, []):
            value = _normalize_field_value(key, params.get(key, ""))
            if not value:
                continue
            lines.append(f"{key}：{value}")
            shown_keys.add(key)

        if summary and summary not in {primary_description, body}:
            lines.append(f"摘要：{summary}")

        if body and body != primary_description:
            lines.append("详细内容：")
            lines.append(body)

        return "\n".join(lines)

    def _format_spirit_detail_text(self, row: sqlite3.Row, params: dict[str, str]) -> str:
        title = str(row["title"] or "")
        touched = str(row["touched"] or "-")
        page_url = str(row["url"] or "")
        wikitext = str(row["wikitext"] or "")

        spirit_name = _first_non_empty_field(params, ("精灵名称",)) or title
        attr_1 = _normalize_field_value("主属性", params.get("主属性", ""))
        attr_2 = _normalize_field_value("2属性", params.get("2属性", ""))
        feature = _normalize_field_value("特性", params.get("特性", ""))
        feature_desc = _normalize_field_value("特性描述", params.get("特性描述", ""))
        region = _normalize_field_value("分布地区", params.get("分布地区", ""))
        desc = _normalize_field_value("精灵描述", params.get("精灵描述", ""))

        spirit_types = _extract_spirit_types_from_params(params)
        type_calc = _compute_spirit_type_effectiveness(spirit_types) if spirit_types else {}

        stats_keys = ("生命", "物攻", "魔攻", "物防", "魔防", "速度")
        stats = [f"{k}{_normalize_field_value(k, params.get(k, ''))}" for k in stats_keys if _normalize_field_value(k, params.get(k, ""))]

        skills = _split_csv(_normalize_field_value("技能", params.get("技能", "")))
        blood_skills = _split_csv(_normalize_field_value("血脉技能", params.get("血脉技能", "")))
        stones = _split_csv(_normalize_field_value("可学技能石", params.get("可学技能石", "")))

        lines: list[str] = [f"【精灵】{spirit_name}"]
        if attr_1 or attr_2:
            lines.append(f"属性：{attr_1}{('/' + attr_2) if attr_2 else ''}")
        if feature:
            lines.append(f"特性：{feature}")
        if feature_desc:
            lines.append(f"特性描述：{_shorten(feature_desc, 120)}")
        if stats:
            lines.append(f"种族值：{' '.join(stats)}")

        if spirit_types and type_calc:
            lines.append("克制计算：")
            lines.append(f"- 4倍弱势：{_join_items(type_calc.get('weak_4x', []))}")
            lines.append(f"- 2倍弱势：{_join_items(type_calc.get('weak_2x', []))}")
            lines.append(f"- 0.5倍抗性：{_join_items(type_calc.get('resist_half', []))}")
            lines.append(f"- 0.25倍抗性：{_join_items(type_calc.get('resist_quarter', []))}")

        if skills:
            lines.append(f"技能：{_limit_items(skills, 8)}")
        if blood_skills:
            lines.append(f"血脉技能：{_limit_items(blood_skills, 6)}")
        if stones:
            lines.append(f"可学技能石：{_limit_items(stones, 6)}")
        if region:
            lines.append(f"分布地区：{region}")

        if not desc:
            desc = _summary_from_content(
                title,
                self.repo.read_markdown_raw(title) if self.repo else "",
                wikitext,
                params,
                220,
            )
        if desc:
            lines.append(f"精灵描述：{_shorten(desc, 220)}")

        if not self._compact_mode():
            extra_body = _clean_wikitext_body(wikitext)
            if extra_body and extra_body != desc:
                lines.append("详细内容：")
                lines.append(_shorten(extra_body, 1200))
        return "\n".join(lines)

    def _build_detail_chain(self, row: sqlite3.Row, detail_text: str | None = None):
        title = str(row["title"] or "")
        wikitext = str(row["wikitext"] or "")
        chain = []
        image_comp = self._find_main_image_component(title, wikitext)
        if image_comp is not None:
            chain.append(image_comp)
        chain.append(Plain(detail_text if detail_text is not None else self._format_detail_text(row)))
        return chain

    def _build_original_wiki_text(self, row: sqlite3.Row) -> str:
        title = str(row["title"] or "")
        page_url = str(row["url"] or "")
        return f"原 Wiki：{_wiki_page_url(title, page_url)}"

    def _build_original_wiki_result(self, event: AstrMessageEvent, row: sqlite3.Row):
        return event.plain_result(self._build_original_wiki_text(row))

    def _build_detail_result(self, event: AstrMessageEvent, row: sqlite3.Row, detail_text: str | None = None):
        result = event.make_result()
        result.chain.extend(self._build_detail_chain(row, detail_text=detail_text))
        return result

    def _build_detail_forward_result(
        self,
        event: AstrMessageEvent,
        row: sqlite3.Row,
        keyword: str = "",
        selected_index: int | None = None,
        total: int | None = None,
        detail_text: str | None = None,
    ):
        title = str(row["title"] or "")
        nodes: list[Node] = []

        if keyword and selected_index is not None and total is not None:
            nodes.append(
                Node(
                    uin=event.get_self_id(),
                    name="洛克百科",
                    content=[
                        Plain(
                            f"关键词：{keyword}\n"
                            f"已选择：{selected_index}/{total}\n"
                            f"词条：{title}"
                        )
                    ],
                )
            )

        nodes.append(
            Node(
                uin=event.get_self_id(),
                name="洛克百科",
                content=self._build_detail_chain(row, detail_text=detail_text),
            )
        )

        nodes.append(
            Node(
                uin=event.get_self_id(),
                name="洛克百科",
                content=[Plain(self._build_original_wiki_text(row))],
            )
        )

        result = event.make_result()
        result.chain.append(Nodes(nodes))
        return result

    def _ensure_repo(self, *, allow_remote_fallback: bool = False) -> str | None:
        if self._source_mode() == "crawler_only":
            return None
        if self.repo is None:
            self.repo = RocomRepository(
                sqlite_path=self._resolve_sqlite_path(),
                jsonl_path=self._resolve_jsonl_path(),
                markdown_root=self._resolve_markdown_root(),
            )
        if self.repo.is_ready():
            return None
        if allow_remote_fallback and self._allow_remote_search():
            return None
        return (
            "本地数据未就绪，请检查 sqlite_path/jsonl_path 配置。\n"
            f"SQLite：{self.repo.sqlite_path}\n"
            f"JSONL：{self.repo.jsonl_path}"
        )

    def _selection_key(self, event: AstrMessageEvent) -> str:
        return f"{event.get_session_id()}::{event.get_sender_id() or '-'}"

    def _pending_get(self, key: str) -> PendingSelection | None:
        pending = self._pending.get(key)
        if not pending:
            return None
        if time.time() - pending.ts > self._pending_ttl():
            self._pending.pop(key, None)
            return None
        return pending

    def _pending_set(self, key: str, keyword: str, records: list[dict[str, Any]]) -> None:
        self._pending[key] = PendingSelection(keyword=keyword, records=records, ts=time.time())

    def _pending_clear(self, key: str) -> None:
        self._pending.pop(key, None)

    def _track_background_task(self, task: asyncio.Task[None]) -> None:
        self._background_tasks.add(task)
        task.add_done_callback(self._background_tasks.discard)

    def _cancel_background_tasks(self) -> None:
        for task in list(self._background_tasks):
            task.cancel()
        self._background_tasks.clear()

    async def _send_result(self, event: AstrMessageEvent, result: Any) -> Any:
        return await event.send(result)

    async def _send_results(self, event: AstrMessageEvent, results: list[Any]) -> list[Any]:
        sent_messages: list[Any] = []
        for result in results:
            sent_messages.append(await self._send_result(event, result))
        return sent_messages

    async def _try_recall_sent_message(self, sent_message: Any) -> bool:
        candidates = list(sent_message) if isinstance(sent_message, (list, tuple, set)) else [sent_message]
        recall_methods = ("recall", "revoke", "withdraw", "delete", "retract")

        for candidate in candidates:
            if candidate is None:
                continue
            for method_name in recall_methods:
                method = getattr(candidate, method_name, None)
                if not callable(method):
                    continue
                try:
                    outcome = method()
                    if inspect.isawaitable(outcome):
                        await outcome
                    return True
                except Exception:
                    continue
        return False

    def _build_detail_delivery_result(
        self,
        event: AstrMessageEvent,
        row: sqlite3.Row | dict[str, Any],
        keyword: str = "",
        selected_index: int | None = None,
        total: int | None = None,
    ):
        detail_text = self._format_detail_text(row)
        if self._supports_forward(event, detail_text):
            return self._build_detail_forward_result(
                event,
                row,
                keyword=keyword,
                selected_index=selected_index,
                total=total,
                detail_text=detail_text,
            )

        result = self._build_detail_result(event, row, detail_text=detail_text)
        result.chain.append(Plain(f"\n{self._build_original_wiki_text(row)}"))
        return result

    async def _query_local_records_async(self, keyword: str) -> list[dict[str, Any]]:
        return await asyncio.to_thread(self._query_local_records, keyword)

    async def _query_remote_records_async(self, keyword: str) -> list[dict[str, Any]]:
        return await asyncio.to_thread(self._query_remote_records, keyword)

    async def _refresh_record_if_needed_async(self, record: dict[str, Any]) -> tuple[dict[str, Any], bool]:
        return await asyncio.to_thread(self._refresh_record_if_needed, record)

    async def _deliver_detail_async(
        self,
        event: AstrMessageEvent,
        row: sqlite3.Row | dict[str, Any],
        *,
        keyword: str = "",
        selected_index: int | None = None,
        total: int | None = None,
    ) -> None:
        record = dict(row)
        if self._update_mode() == "before_send_compare_update":
            record, _ = await self._refresh_record_if_needed_async(record)

        first_sent = await self._send_result(
            event,
            self._build_detail_delivery_result(
                event,
                record,
                keyword=keyword,
                selected_index=selected_index,
                total=total,
            ).stop_event(),
        )

        if self._update_mode() == "after_send_compare_update":
            refreshed_record, updated = await self._refresh_record_if_needed_async(record)
            if updated:
                recalled = False
                if self._recall_on_update():
                    recalled = await self._try_recall_sent_message(first_sent)
                if self._recall_on_update() and not recalled:
                    await self._send_result(event, event.plain_result("检测到词条已更新，以下为最新内容。"))
                await self._send_result(
                    event,
                    self._build_detail_delivery_result(
                        event,
                        refreshed_record,
                        keyword=keyword,
                        selected_index=selected_index,
                        total=total,
                    ).stop_event(),
                )

    async def _deliver_query_results_async(
        self,
        event: AstrMessageEvent,
        keyword: str,
        selected_index_hint: int | None,
    ) -> None:
        err = self._ensure_repo(allow_remote_fallback=True)
        if err:
            await self._send_result(event, event.plain_result(err))
            return

        try:
            rows = await self._query_local_records_async(keyword)
            if not rows and self._allow_remote_search():
                rows = await self._query_remote_records_async(keyword)

            if not rows:
                cache_key = f"miss:{keyword}:{self._query_limit()}"
                text = self._cache_get(cache_key) or f"未找到关键词“{keyword}”相关内容。"
                self._cache_set(cache_key, text)
                await self._send_result(event, event.plain_result(text))
                return

            selection_key = self._selection_key(event)
            if len(rows) == 1:
                self._pending_clear(selection_key)
                await self._deliver_detail_async(event, rows[0])
                return

            if selected_index_hint is not None and 1 <= selected_index_hint <= len(rows):
                self._pending_clear(selection_key)
                await self._deliver_detail_async(
                    event,
                    rows[selected_index_hint - 1],
                    keyword=keyword,
                    selected_index=selected_index_hint,
                    total=len(rows),
                )
                return

            self._pending_set(selection_key, keyword, rows)
            await self._send_result(event, event.plain_result(self._format_selection_text(keyword, rows)))
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            logger.warning(f"[rocom] 查询失败：{exc}")
            await self._send_result(event, event.plain_result(f"查询失败：{exc}"))

    async def _deliver_selected_index_async(
        self,
        event: AstrMessageEvent,
        pending: PendingSelection,
        index: int,
    ) -> None:
        selection_key = self._selection_key(event)
        if index == 0:
            self._pending_clear(selection_key)
            await self._send_result(event, event.plain_result("已取消本次词条选择。").stop_event())
            return

        if index < 1 or index > len(pending.records):
            await self._send_result(
                event,
                event.plain_result(f"请输入 1 到 {len(pending.records)} 之间的序号，或回复 0 取消。").stop_event(),
            )
            return

        self._pending_clear(selection_key)
        await self._deliver_detail_async(
            event,
            pending.records[index - 1],
            keyword=pending.keyword,
            selected_index=index,
            total=len(pending.records),
        )

    async def _query_request_async(
        self,
        event: AstrMessageEvent,
        keyword: str,
        selected_index_hint: int | None,
    ) -> None:
        key = self._selection_key(event)
        self._inflight_queries.add(key)
        try:
            await self._deliver_query_results_async(event, keyword, selected_index_hint)
        finally:
            self._inflight_queries.discard(key)

    async def _select_request_async(
        self,
        event: AstrMessageEvent,
        pending: PendingSelection,
        index: int,
    ) -> None:
        await self._deliver_selected_index_async(event, pending, index)

    @filter.command("洛克帮助", alias={"洛克help", "百科帮助"})
    async def rocom_help(self, event: AstrMessageEvent):
        yield event.plain_result(self._build_help_text())

    @filter.command("洛克查", alias={"洛克查询", "查百科", "查词条"})
    async def rocom_query(self, event: AstrMessageEvent, keyword: str = ""):
        event.should_call_llm(True)
        event.stop_event()

        raw_keyword = keyword.strip()
        if not raw_keyword:
            yield event.plain_result("请输入关键词，例如：洛克查 小独角兽").stop_event()
            return

        keyword, selected_index_hint = self._parse_query_message(event, raw_keyword)
        self._pending_clear(self._selection_key(event))
        task = asyncio.create_task(self._query_request_async(event, keyword, selected_index_hint))
        self._track_background_task(task)
        return

    @filter.regex(r"^\s*\d+\s*$")
    async def rocom_select_by_index(self, event: AstrMessageEvent):
        selection_key = self._selection_key(event)
        pending = self._pending_get(selection_key)
        if not pending:
            if selection_key in self._inflight_queries:
                event.should_call_llm(True)
                yield event.plain_result("查询仍在处理中，请稍后再回复序号。").stop_event()
            return

        event.should_call_llm(True)
        event.stop_event()

        err = self._ensure_repo(allow_remote_fallback=True)
        if err:
            yield event.plain_result(err).stop_event()
            return

        raw = event.get_message_str().strip()
        index = int(raw)
        task = asyncio.create_task(self._select_request_async(event, pending, index))
        self._track_background_task(task)
        return

    @filter.command("洛克状态", alias={"百科状态"})
    async def rocom_status(self, event: AstrMessageEvent):
        err = self._ensure_repo(allow_remote_fallback=True)
        if err:
            yield event.plain_result(err)
            return

        data_file = self.repo.sqlite_path if self.repo.sqlite_path.exists() else self.repo.jsonl_path
        if not data_file.exists():
            text = (
                "洛克百科插件状态\n"
                "当前数据文件：未就绪（将按配置尝试在线抓取）\n"
                f"缓存条目：{len(self._cache)}\n"
                f"待选择会话：{len(self._pending)}\n"
                f"回复模式：{'compact' if self._compact_mode() else 'full'}\n"
                f"数据源模式：{self._source_mode()}\n"
                f"更新模式：{self._update_mode()}\n"
                f"在线抓取：{'启用' if self._crawler_enabled() else '禁用'}"
            )
            yield event.plain_result(text)
            return

        st = data_file.stat()
        text = (
            "洛克百科插件状态\n"
            f"当前数据文件：{data_file.name}\n"
            f"文件大小：{st.st_size} 字节\n"
            f"缓存条目：{len(self._cache)}\n"
            f"待选择会话：{len(self._pending)}\n"
            f"回复模式：{'compact' if self._compact_mode() else 'full'}\n"
            f"数据源模式：{self._source_mode()}\n"
            f"更新模式：{self._update_mode()}\n"
            f"在线抓取：{'启用' if self._crawler_enabled() else '禁用'}"
        )
        yield event.plain_result(text)


    @filter.permission_type(filter.PermissionType.ADMIN)
    @filter.command("洛克重载", alias={"百科重载"})
    async def rocom_reload(self, event: AstrMessageEvent):
        self._cancel_background_tasks()
        self._inflight_queries.clear()
        self.repo = RocomRepository(
            sqlite_path=self._resolve_sqlite_path(),
            jsonl_path=self._resolve_jsonl_path(),
            markdown_root=self._resolve_markdown_root(),
        )
        self._cache.clear()
        self._pending.clear()
        yield event.plain_result(f"重载完成。当前 sqlite: {self.repo.sqlite_path}，jsonl: {self.repo.jsonl_path}")

    @filter.permission_type(filter.PermissionType.ADMIN)
    @filter.command("洛克清缓存", alias={"百科清缓存"})
    async def rocom_clear_cache(self, event: AstrMessageEvent):
        self._cancel_background_tasks()
        self._inflight_queries.clear()
        cache_size = len(self._cache)
        pending_size = len(self._pending)
        self._cache.clear()
        self._pending.clear()
        yield event.plain_result(
            f"缓存已清理，共清理缓存 {cache_size} 条，待选择会话 {pending_size} 条。"
        )

    async def terminate(self):
        self._cancel_background_tasks()
        self._inflight_queries.clear()
        self._cache.clear()
        self._pending.clear()
