from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import re
import sqlite3
import time
from urllib.parse import quote

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


@dataclass(slots=True)
class CacheEntry:
    value: str
    ts: float


@dataclass(slots=True)
class PendingSelection:
    keyword: str
    titles: list[str]
    ts: float


class RocomRepository:
    def __init__(self, sqlite_path: Path, markdown_root: Path) -> None:
        self.sqlite_path = sqlite_path
        self.markdown_root = markdown_root

    def is_ready(self) -> bool:
        return self.sqlite_path.exists()

    def _connect(self) -> sqlite3.Connection:
        connection = sqlite3.connect(self.sqlite_path)
        connection.row_factory = sqlite3.Row
        return connection

    def _fetch_one(self, query: str, params: tuple[object, ...]) -> sqlite3.Row | None:
        with self._connect() as conn:
            return conn.execute(query, params).fetchone()

    def _fetch_many(
        self,
        query: str,
        params: tuple[object, ...],
        limit: int,
    ) -> list[sqlite3.Row]:
        with self._connect() as conn:
            rows = conn.execute(query, params).fetchall()
        return list(rows)[:limit]

    def query_title_contains(self, keyword: str, limit: int = 8) -> list[sqlite3.Row]:
        return self._fetch_many(
            """
            SELECT title, extract, wikitext, touched
            FROM pages
            WHERE title LIKE ?
            ORDER BY CASE WHEN title = ? THEN 0 WHEN title LIKE ? THEN 1 ELSE 2 END, LENGTH(title)
            LIMIT 20
            """,
            (f"%{keyword}%", keyword, f"{keyword}%"),
            limit,
        )

    def get_page_by_title(self, title: str) -> sqlite3.Row | None:
        return self._fetch_one(
            """
            SELECT title, extract, wikitext, touched, url, images, categories, links
            FROM pages
            WHERE title = ?
            LIMIT 1
            """,
            (title,),
        )

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


@register("astrbot_plugin_rocom_wiki_bili", "Kanbara", "洛克王国 Wiki 本地查询插件", "1.0.0")
class RocomWikiPlugin(Star):
    def __init__(self, context: Context, config: AstrBotConfig | None = None):
        super().__init__(context)
        self.context = context
        self.config = config or {}
        self._cache: dict[str, CacheEntry] = {}
        self._pending: dict[str, PendingSelection] = {}
        self.repo: RocomRepository | None = None

    async def initialize(self):
        self.repo = RocomRepository(
            sqlite_path=self._resolve_sqlite_path(),
            markdown_root=self._resolve_markdown_root(),
        )
        logger.info(f"[rocom] 插件初始化完成，sqlite={self.repo.sqlite_path}")

    def _resolve_sqlite_path(self) -> Path:
        plugin_root = Path(__file__).resolve().parent
        configured = str(self.config.get("sqlite_path") or "").strip()
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

    def _resolve_markdown_root(self) -> Path:
        plugin_root = Path(__file__).resolve().parent
        configured = str(self.config.get("markdown_root") or "").strip()
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
        return int(self.config.get("cache_ttl_sec", 600) or 600)

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
        return str(self.config.get("default_reply_mode", "compact")) != "full"

    def _query_limit(self) -> int:
        return max(1, min(20, int(self.config.get("query_max_results", 8) or 8)))

    def _forward_enabled(self) -> bool:
        return bool(self.config.get("merge_forward_enabled", True))

    def _forward_platforms(self) -> set[str]:
        raw = str(self.config.get("merge_forward_platforms", "aiocqhttp,onebot")).strip()
        return {item.lower() for item in _split_csv(raw)}

    def _supports_forward(self, event: AstrMessageEvent) -> bool:
        if not self._forward_enabled():
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

    def _build_detail_chain(self, row: sqlite3.Row):
        title = str(row["title"] or "")
        wikitext = str(row["wikitext"] or "")
        chain = []
        image_comp = self._find_main_image_component(title, wikitext)
        if image_comp is not None:
            chain.append(image_comp)
        chain.append(Plain(self._format_detail_text(row)))
        return chain

    def _build_original_wiki_text(self, row: sqlite3.Row) -> str:
        title = str(row["title"] or "")
        page_url = str(row["url"] or "")
        return f"原 Wiki：{_wiki_page_url(title, page_url)}"

    def _build_original_wiki_result(self, event: AstrMessageEvent, row: sqlite3.Row):
        return event.plain_result(self._build_original_wiki_text(row))

    def _build_detail_result(self, event: AstrMessageEvent, row: sqlite3.Row):
        result = event.make_result()
        result.chain.extend(self._build_detail_chain(row))
        return result

    def _build_detail_forward_result(
        self,
        event: AstrMessageEvent,
        row: sqlite3.Row,
        keyword: str = "",
        selected_index: int | None = None,
        total: int | None = None,
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
                content=self._build_detail_chain(row),
            )
        )

        result = event.make_result()
        result.chain.append(Nodes(nodes))
        return result

    def _ensure_repo(self) -> str | None:
        if self.repo is None:
            self.repo = RocomRepository(
                sqlite_path=self._resolve_sqlite_path(),
                markdown_root=self._resolve_markdown_root(),
            )
        if not self.repo.is_ready():
            return (
                "本地数据未就绪，请检查 sqlite_path 配置。\n"
                f"当前路径：{self.repo.sqlite_path}"
            )
        return None

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

    def _pending_set(self, key: str, keyword: str, titles: list[str]) -> None:
        self._pending[key] = PendingSelection(keyword=keyword, titles=titles, ts=time.time())

    def _pending_clear(self, key: str) -> None:
        self._pending.pop(key, None)

    @filter.command("洛克帮助", alias={"洛克help", "百科帮助"})
    async def rocom_help(self, event: AstrMessageEvent):
        yield event.plain_result(self._build_help_text())

    @filter.command("洛克查", alias={"洛克查询", "查百科", "查词条"})
    async def rocom_query(self, event: AstrMessageEvent, keyword: str = ""):
        keyword = keyword.strip()
        if not keyword:
            yield event.plain_result("请输入关键词，例如：洛克查 小独角兽")
            return

        err = self._ensure_repo()
        if err:
            yield event.plain_result(err)
            return

        cache_key = f"miss:{keyword}:{self._query_limit()}"
        rows = self.repo.query_title_contains(keyword, limit=self._query_limit())
        if not rows:
            text = self._cache_get(cache_key) or f"未找到关键词“{keyword}”相关内容。"
            self._cache_set(cache_key, text)
            yield event.plain_result(text)
            return

        selection_key = self._selection_key(event)
        if len(rows) == 1:
            self._pending_clear(selection_key)
            yield self._build_detail_result(event, rows[0]).stop_event()
            yield self._build_original_wiki_result(event, rows[0]).stop_event()
            return

        self._pending_set(selection_key, keyword, [str(row["title"] or "") for row in rows])
        yield event.plain_result(self._format_selection_text(keyword, rows))

    @filter.regex(r"^\s*\d+\s*$")
    async def rocom_select_by_index(self, event: AstrMessageEvent):
        pending = self._pending_get(self._selection_key(event))
        if not pending:
            return

        err = self._ensure_repo()
        if err:
            yield event.plain_result(err).stop_event()
            return

        raw = event.get_message_str().strip()
        index = int(raw)

        if index == 0:
            self._pending_clear(self._selection_key(event))
            yield event.plain_result("已取消本次词条选择。").stop_event()
            return

        if index < 1 or index > len(pending.titles):
            yield event.plain_result(
                f"请输入 1 到 {len(pending.titles)} 之间的序号，或回复 0 取消。"
            ).stop_event()
            return

        title = pending.titles[index - 1]
        row = self.repo.get_page_by_title(title)
        if not row:
            self._pending_clear(self._selection_key(event))
            yield event.plain_result("词条详情读取失败，请重新查询一次。").stop_event()
            return

        self._pending_clear(self._selection_key(event))
        if self._supports_forward(event):
            yield self._build_detail_forward_result(
                event,
                row,
                keyword=pending.keyword,
                selected_index=index,
                total=len(pending.titles),
            ).stop_event()
            yield self._build_original_wiki_result(event, row).stop_event()
            return

        yield self._build_detail_result(event, row).stop_event()
        yield self._build_original_wiki_result(event, row).stop_event()

    @filter.command("洛克状态", alias={"百科状态"})
    async def rocom_status(self, event: AstrMessageEvent):
        err = self._ensure_repo()
        if err:
            yield event.plain_result(err)
            return

        st = self.repo.sqlite_path.stat()
        text = (
            "洛克百科插件状态\n"
            f"文件大小：{st.st_size} 字节\n"
            f"缓存条目：{len(self._cache)}\n"
            f"待选择会话：{len(self._pending)}\n"
            f"回复模式：{'compact' if self._compact_mode() else 'full'}"
        )
        yield event.plain_result(text)


    @filter.permission_type(filter.PermissionType.ADMIN)
    @filter.command("洛克重载", alias={"百科重载"})
    async def rocom_reload(self, event: AstrMessageEvent):
        self.repo = RocomRepository(
            sqlite_path=self._resolve_sqlite_path(),
            markdown_root=self._resolve_markdown_root(),
        )
        self._cache.clear()
        self._pending.clear()
        yield event.plain_result(f"重载完成。当前 sqlite: {self.repo.sqlite_path}")

    @filter.permission_type(filter.PermissionType.ADMIN)
    @filter.command("洛克清缓存", alias={"百科清缓存"})
    async def rocom_clear_cache(self, event: AstrMessageEvent):
        cache_size = len(self._cache)
        pending_size = len(self._pending)
        self._cache.clear()
        self._pending.clear()
        yield event.plain_result(
            f"缓存已清理，共清理缓存 {cache_size} 条，待选择会话 {pending_size} 条。"
        )

    async def terminate(self):
        self._cache.clear()
        self._pending.clear()
