"""
SEO Audit Tool — движок аудита (audit_engine.py)
=================================================
Вся "тяжёлая" логика вынесена сюда: краулер, разбор robots.txt и sitemap.xml,
набор технических SEO/performance-проверок для каждой страницы и подсчёт
итогового SEO Score. main.py отвечает только за HTTP API и управление job'ами.

Никаких платных внешних AI-API — только asyncio, aiohttp, BeautifulSoup4/lxml.
Ни одна SEO-проблема не определяется через LLM — только детерминированные
статические правила.

Версия 3.1: продолжение работы над версией 3 (race condition в краулере,
двойной подсчёт SEO Score, отключённая SSL-проверка, ошибочная HTTP/HTTPS
логика были исправлены раньше). В 3.1:

  * indexability matrix переписана на реальных сигналах (meta/X-Robots-Tag
    noindex, robots.txt, redirect, soft-404, HTTP-статус) с явным
    per-page списком "indexability_reasons";
  * sitemap.xml теперь реально участвует в indexability/consistency-проверках
    (передаётся настоящий набор URL, а не пустой set);
  * canonical- и hreflang-таргеты проверяются пост-обходом (canonical_to_error/
    canonical_to_redirect/canonical_to_noindex/canonical_chain,
    hreflang_self_missing, hreflang_to_error/noindex);
  * redirect chain хранит реальные статус-коды каждого хопа;
  * soft-404 использует несколько независимых сигналов и учитывает тип
    страницы, чтобы не путать короткие utility-страницы с ошибкой;
  * построен граф внутренних ссылок (incoming_internal_links) для поиска
    orphan / слабо связанных страниц;
  * добавлены sitemap consistency (duplicate/invalid/problem URLs), базовые
    accessibility-проверки, доп. mobile-проверки (viewport zoom), доп.
    security-проверки (http-ресурсы в canonical/hreflang/sitemap);
  * SEO Score теперь считается по 10 категориям с явными весами
    (SCORE_WEIGHTS) и агрегируется в overall score — вместо одной
    недифференцированной формулы;
  * у каждой issue появилось поле confidence (high/medium/low);
  * добавлены audit-level метаданные (crawl_started_at/finished_at,
    crawl_termination_reason, pages_discovered/skipped_limit и т.д.).

API и формат JSON-ответа остаются обратно совместимыми с main.py и текущим
UI: все старые ключи сохранены, добавлены только новые поля.
"""

from __future__ import annotations

import asyncio
import difflib
import gzip
import json
import logging
import re
import ssl as ssl_module
import time
import os
from datetime import date, datetime, timezone, timedelta
from urllib.parse import urljoin, urlparse, urlsplit, urldefrag, parse_qsl, urlunsplit
from collections import defaultdict
from dataclasses import dataclass, field
from typing import Any, Callable, Optional
from urllib.robotparser import RobotFileParser

import aiohttp
from bs4 import BeautifulSoup

logger = logging.getLogger("seo_audit.engine")

AUDIT_VERSION = "3.1"

# --------------------------------------------------------------------------
# Константы и пороговые значения
# --------------------------------------------------------------------------

REQUEST_TIMEOUT = 10            # секунд на один HTTP-запрос
CONCURRENT_REQUESTS = 8         # одновременных запросов к сайту
USER_AGENT = "SEO-Audit-Bot/2.0 (+local technical audit tool)"
MAX_JOB_DURATION = 300          # жёсткий потолок на весь аудит, секунд

TITLE_MIN_LEN, TITLE_MAX_LEN = 10, 60
DESC_MIN_LEN, DESC_MAX_LEN = 50, 160
THIN_CONTENT_WORDS = 200        # ниже этого — эвристика "тонкого" контента (не универсальное правило)
SLOW_RESPONSE_MS = 1000         # TTFB выше этого — предупреждение
LARGE_PAGE_BYTES = 2 * 1024 * 1024   # 2 МБ — тяжёлая страница
MAX_SITEMAP_URLS = 500
MAX_CHILD_SITEMAPS = 50
MAX_CRAWL_URLS_HARD = 5000
MAX_IMAGES_CHECKED_PER_PAGE = 25
MAX_EXTERNAL_LINKS_CHECKED_PER_PAGE = 20
MAX_TEXT_WORDS_FOR_ANALYSIS = 50000
PAGESPEED_TIMEOUT = 45
PAGESPEED_API_URL = "https://www.googleapis.com/pagespeedonline/v5/runPagespeed"
SCHEMA_VALIDATOR_URL = "https://validator.schema.org/"

# Защита от "crawler traps" (faceted-навигация, календари, бесконечные query-варианты)
MAX_VISITED_MULTIPLIER = 5          # верхний предел на len(visited) относительно max_pages
MAX_QUERY_VARIANTS_PER_PATH = 8     # сколько разных query-строк на один path мы готовы обойти
HERO_IMAGE_COUNT = 2                # первые N изображений считаются "above the fold" — для них не требуем lazy
SOFT_404_MIN_WORDS = 80

# Для near-duplicate title сравнение O(n^2) слишком дорого на больших сайтах —
# ограничиваем количество страниц, для которых делаем это сравнение.
NEAR_DUPLICATE_TITLE_MAX_PAGES = 400
NEAR_DUPLICATE_TITLE_RATIO = 0.92
REPEATED_CHAR_RE = re.compile(r"(.)\1{4,}")

WEAK_INTERNAL_LINKS_THRESHOLD = 2   # меньше этого входящих внутренних ссылок — "слабо связанная" страница

# Query-параметры, которые обычно не создают "другую" страницу с точки зрения canonical
TRACKING_PARAMS = {
    "utm_source", "utm_medium", "utm_campaign", "utm_term", "utm_content",
    "gclid", "fbclid", "yclid", "msclkid", "ref", "referrer", "_ga", "mc_cid", "mc_eid",
}
# Параметры пагинации/поиска, не считающиеся автоматически SEO-проблемой
BENIGN_QUERY_PARAMS = {"page", "p", "s", "q", "search", "sort", "order", "limit"}

ARTICLE_SCHEMA_TYPES = {"Article", "NewsArticle", "BlogPosting"}
UTILITY_PAGE_TYPES = {"login", "signup", "checkout", "cart", "search", "contact", "utility"}

PAGE_TYPE_URL_PATTERNS = (
    ("login", re.compile(r"/(login|signin|sign-in)(/|$)", re.I)),
    ("signup", re.compile(r"/(signup|sign-up|register)(/|$)", re.I)),
    ("checkout", re.compile(r"/(checkout|order)(/|$)", re.I)),
    ("cart", re.compile(r"/(cart|basket)(/|$)", re.I)),
    ("search", re.compile(r"/(search|find)(/|$)", re.I)),
    ("contact", re.compile(r"/(contact|contacts)(/|$)", re.I)),
    ("about", re.compile(r"/(about|about-us)(/|$)", re.I)),
    ("blog", re.compile(r"/(blog|news|articles?)(/|$)", re.I)),
    ("product", re.compile(r"/(product|item|goods)s?/", re.I)),
    ("category", re.compile(r"/(category|categories|catalog|collections?)/", re.I)),
)

SOFT_404_TITLE_MARKERS = re.compile(
    r"(page not found|404 error|404 not found|not found|страница не найдена|"
    r"страница не существует|ничего не найдено|error 404)",
    re.I,
)
SOFT_404_BODY_MARKERS = re.compile(
    r"(page not found|the page you.{0,15}looking for|does not exist|"
    r"страница не найдена|страница не существует|данная страница отсутствует|"
    r"запрашиваемая страница не найдена|ничего не найдено по вашему запросу)",
    re.I,
)

PAGINATION_QUERY_RE = re.compile(r"[?&](page|p)=\d+", re.I)
PAGINATION_PATH_RE = re.compile(r"/page/\d+/?$", re.I)

REDIRECT_STATUS_CODES = {301, 302, 303, 307, 308}
HREFLANG_LANG_RE = re.compile(r"^[a-z]{2,3}(?:-[a-z0-9]{2,8})?$")


# --------------------------------------------------------------------------
# Метаданные категорий проблем: серьёзность, вес для скоринга, группа, совет
# --------------------------------------------------------------------------

GROUP_LABELS = {
    "crawling": "Краулинг и доступность",
    "meta": "Meta-теги (Title / Description)",
    "indexing": "Индексация",
    "security": "Безопасность (HTTPS)",
    "content": "Контент и разметка",
    "social": "Соцсети и структурированные данные",
    "performance": "Производительность",
    "mobile": "Мобильная версия",
    "links": "Ссылки",
    "url": "Структура URL",
}

# Веса категорий для итогового SEO Score (сумма = 100). Это НЕ официальная
# формула Google, а внутренняя модель "Technical SEO Audit Score".
SCORE_WEIGHTS = {
    "crawling": 15,
    "indexing": 15,
    "meta": 10,
    "content": 15,
    "links": 10,
    "performance": 10,
    "security": 10,
    "mobile": 5,
    "social": 5,
    "url": 5,
}

# severity: critical / warning / info — влияет на цвет бэйджа в UI
# weight: вклад одного случая проблемы в штраф SEO Score
# confidence_default: базовая уверенность движка в проверке (может быть
# переопределена конкретным вызовом add_issue через параметр confidence)
CATEGORY_META = {
    "broken_link":          {"label": "Битые ссылки (4xx/5xx)",              "group": "crawling",   "severity": "critical", "weight": 8, "recommendation": "Исправьте ссылку или настройте 301-редирект на актуальную страницу.", "confidence_default": "high"},
    "timeout":              {"label": "Превышено время ожидания",             "group": "crawling",   "severity": "warning",  "weight": 4, "recommendation": "Проверьте нагрузку на сервер — страница не ответила за отведённое время.", "confidence_default": "medium"},
    "connection_error":     {"label": "Ошибки соединения",                    "group": "crawling",   "severity": "warning",  "weight": 4, "recommendation": "Проверьте доступность сервера и корректность DNS/SSL.", "confidence_default": "medium"},
    "blocked_by_robots":    {"label": "Заблокировано в robots.txt",           "group": "crawling",   "severity": "info",     "weight": 1, "recommendation": "Убедитесь, что страница закрыта от индексации намеренно.", "confidence_default": "high"},
    "no_sitemap":           {"label": "Не найден sitemap.xml",                "group": "crawling",   "severity": "warning",  "weight": 4, "recommendation": "Создайте sitemap.xml и укажите его в robots.txt (Sitemap: ...).", "confidence_default": "high"},
    "orphan_page":          {"label": "Страницы из sitemap не найдены при обходе", "group": "crawling", "severity": "info",    "weight": 1, "recommendation": "Добавьте внутренние ссылки на эти страницы — сейчас на них не ведут ссылки с сайта.", "confidence_default": "medium"},
    "ssl_error":             {"label": "Ошибка SSL-сертификата",               "group": "crawling",   "severity": "warning",  "weight": 5, "recommendation": "Проверьте валидность и цепочку SSL-сертификата (срок действия, промежуточные сертификаты).", "confidence_default": "high"},
    "redirect_loop":         {"label": "Цикл редиректов",                      "group": "crawling",   "severity": "critical", "weight": 6, "recommendation": "Устраните цикл редиректов — страница никогда не отдаёт финальный контент.", "confidence_default": "high"},

    "no_title":             {"label": "Отсутствует Title",                    "group": "meta",       "severity": "critical", "weight": 8, "recommendation": "Добавьте уникальный <title> длиной 50–60 символов, отражающий суть страницы.", "confidence_default": "high"},
    "duplicate_title":      {"label": "Дублирующиеся Title",                  "group": "meta",       "severity": "critical", "weight": 7, "recommendation": "Сделайте Title уникальным для каждой страницы — дубли путают поиск и пользователей.", "confidence_default": "high"},
    "similar_title":        {"label": "Очень похожие Title (near-duplicate)", "group": "meta",       "severity": "info",     "weight": 2, "recommendation": "Проверьте, действительно ли страницам нужны почти одинаковые Title.", "confidence_default": "medium"},
    "title_too_short":      {"label": "Слишком короткий Title",               "group": "meta",       "severity": "info",     "weight": 1, "recommendation": "Расширьте Title до 50–60 символов, добавив ключевые слова и бренд.", "confidence_default": "medium"},
    "title_too_long":       {"label": "Слишком длинный Title",                "group": "meta",       "severity": "info",     "weight": 1, "recommendation": "Сократите Title — часть текста обрежется в выдаче.", "confidence_default": "medium"},
    "repeated_char_title":  {"label": "Title содержит подозрительный повтор символов", "group": "meta", "severity": "info", "weight": 1, "recommendation": "Проверьте Title на технический мусор/повторы (например, следствие шаблона).", "confidence_default": "medium"},
    "no_meta_description":  {"label": "Отсутствует Meta Description",         "group": "meta",       "severity": "warning",  "weight": 4, "recommendation": "Добавьте описание 50–160 символов — оно влияет на CTR в выдаче.", "confidence_default": "high"},
    "duplicate_description":{"label": "Дублирующиеся Meta Description",       "group": "meta",       "severity": "warning",  "weight": 4, "recommendation": "Напишите уникальное описание для каждой страницы.", "confidence_default": "high"},
    "description_too_short":{"label": "Слишком короткий Meta Description",    "group": "meta",       "severity": "info",     "weight": 1, "recommendation": "Расширьте описание до 50–160 символов.", "confidence_default": "medium"},
    "description_too_long": {"label": "Слишком длинный Meta Description",     "group": "meta",       "severity": "info",     "weight": 1, "recommendation": "Сократите описание — оно обрежется в сниппете.", "confidence_default": "medium"},
    "repeated_char_description": {"label": "Description содержит подозрительный повтор символов", "group": "meta", "severity": "info", "weight": 1, "recommendation": "Проверьте описание на технический мусор/повторы.", "confidence_default": "medium"},

    "no_canonical":         {"label": "Отсутствует Canonical",                "group": "indexing",   "severity": "warning",  "weight": 3, "recommendation": "Добавьте <link rel=\"canonical\"> во избежание дублей в индексе.", "confidence_default": "high"},
    "noindex":               {"label": "Страница закрыта от индексации",       "group": "indexing",   "severity": "warning",  "weight": 3, "recommendation": "Проверьте, что noindex стоит намеренно — иначе страница не попадёт в поиск.", "confidence_default": "high"},

    "not_https":             {"label": "Страница отдаётся по HTTP",            "group": "security",   "severity": "critical", "weight": 8, "recommendation": "Настройте HTTPS и 301-редирект с HTTP — это прямой фактор ранжирования.", "confidence_default": "high"},
    "mixed_content":         {"label": "Смешанный контент (http-ресурсы на https-странице)", "group": "security", "severity": "warning", "weight": 4, "recommendation": "Замените http:// ссылки на https:// в ресурсах страницы (img/script/link).", "confidence_default": "high"},
    "https_downgrade":       {"label": "HTTPS редиректит на HTTP",             "group": "security",   "severity": "critical", "weight": 7, "recommendation": "Уберите редирект, понижающий защищённое соединение до HTTP.", "confidence_default": "high"},
    "http_internal_links":   {"label": "Внутренние ссылки указывают на HTTP-версию", "group": "security", "severity": "info", "weight": 2, "recommendation": "Замените внутренние ссылки на HTTP на их HTTPS-эквивалент.", "confidence_default": "medium"},

    "no_h1":                 {"label": "Отсутствует H1",                       "group": "content",    "severity": "critical", "weight": 7, "recommendation": "Добавьте единственный тег <h1>, описывающий главную тему страницы.", "confidence_default": "high"},
    "multiple_h1":           {"label": "Несколько H1 на странице",             "group": "content",    "severity": "warning",  "weight": 3, "recommendation": "Оставьте один <h1>, остальные замените на <h2>/<h3>.", "confidence_default": "high"},
    "empty_h1":               {"label": "Пустой H1",                            "group": "content",    "severity": "warning",  "weight": 2, "recommendation": "Заполните <h1> содержательным текстом, а не оставляйте его пустым.", "confidence_default": "high"},
    "h1_too_long":            {"label": "Очень длинный H1",                     "group": "content",    "severity": "info",     "weight": 1, "recommendation": "Рассмотрите более короткий и точный H1.", "confidence_default": "low"},
    "empty_heading":          {"label": "Пустой заголовок (H2–H6)",             "group": "content",    "severity": "info",     "weight": 1, "recommendation": "Уберите заголовок без текста или заполните его содержимым.", "confidence_default": "medium"},
    "heading_hierarchy_skip": {"label": "Пропуск уровня заголовков",            "group": "content",    "severity": "info",     "weight": 1, "recommendation": "Старайтесь не пропускать уровни заголовков (например, H2 сразу в H4) для лучшей структуры документа.", "confidence_default": "low"},
    "images_without_alt":    {"label": "Изображения без Alt",                  "group": "content",    "severity": "warning",  "weight": 2, "recommendation": "Добавьте атрибут alt с описанием изображения для доступности и Image Search.", "confidence_default": "high"},
    "broken_image":          {"label": "Битые изображения",                    "group": "content",    "severity": "warning",  "weight": 3, "recommendation": "Замените или удалите ссылку на изображение, которое не загружается.", "confidence_default": "high"},
    "thin_content":          {"label": "Малый объём текста (возможен тонкий контент)", "group": "content", "severity": "warning", "weight": 3, "recommendation": "Это эвристика, а не универсальное правило: для информационных/статейных страниц имеет смысл расширить содержательный текст.", "confidence_default": "medium"},
    "no_lang_attribute":     {"label": "Не указан атрибут lang у <html>",       "group": "content",    "severity": "info",     "weight": 1, "recommendation": "Добавьте lang=\"ru\" (или нужный код языка) в тег <html>.", "confidence_default": "high"},
    "soft_404":               {"label": "Похоже на soft 404 (200 OK, но контент — страница ошибки)", "group": "indexing", "severity": "warning", "weight": 5, "recommendation": "Отдавайте реальный статус 404/410 для отсутствующих страниц вместо 200 OK с текстом об ошибке.", "confidence_default": "medium"},
    "form_without_label":    {"label": "Поле формы без label",                 "group": "content",    "severity": "warning",  "weight": 2, "recommendation": "Добавьте связанный label или доступное имя для полей формы.", "confidence_default": "high"},
    "low_text_html_ratio":   {"label": "Низкая доля текста в HTML",            "group": "content",    "severity": "info",     "weight": 1, "recommendation": "Проверьте лишний HTML/JS/CSS и убедитесь, что основной контент доступен поисковому роботу.", "confidence_default": "low"},
    "no_author_signal":      {"label": "Не найден автор/организация",          "group": "content",    "severity": "info",     "weight": 1, "recommendation": "Для информационного контента явно укажите автора/организацию там, где это уместно.", "confidence_default": "medium"},
    "missing_publish_date":  {"label": "Не найдена дата публикации",           "group": "content",    "severity": "info",     "weight": 1, "recommendation": "Для новостей/статей укажите дату публикации и при необходимости дату обновления.", "confidence_default": "medium"},
    "duplicate_element_ids": {"label": "Повторяющиеся id-атрибуты",            "group": "content",    "severity": "info",     "weight": 1, "recommendation": "id должен быть уникален в пределах документа (важно для accessibility и JS).", "confidence_default": "high"},
    "empty_link":             {"label": "Пустая ссылка (без текста/aria-label)", "group": "content",   "severity": "info",     "weight": 1, "recommendation": "Добавьте текст, aria-label или доступное описание для ссылки.", "confidence_default": "medium"},
    "iframe_missing_title":  {"label": "iframe без атрибута title",            "group": "content",    "severity": "info",     "weight": 1, "recommendation": "Добавьте title для iframe — это важно для скринридеров.", "confidence_default": "medium"},

    "no_open_graph":         {"label": "Отсутствуют Open Graph теги",          "group": "social",     "severity": "info",     "weight": 2, "recommendation": "Добавьте og:title, og:description, og:image для красивых превью в соцсетях.", "confidence_default": "high"},
    "no_structured_data":    {"label": "Нет структурированных данных (JSON-LD)","group": "social",    "severity": "info",     "weight": 1, "recommendation": "Добавьте JSON-LD разметку (Schema.org) для расширенных сниппетов в поиске.", "confidence_default": "medium"},
    "schema_invalid_json":   {"label": "Некорректный JSON-LD",                 "group": "social",     "severity": "warning",  "weight": 3, "recommendation": "Исправьте синтаксис JSON-LD и проверьте Schema.org разметку валидатором.", "confidence_default": "high"},
    "schema_missing_type":   {"label": "JSON-LD блок без @type",               "group": "social",     "severity": "info",     "weight": 1, "recommendation": "Укажите @type для каждого объекта JSON-LD, иначе поисковик не поймёт тип разметки.", "confidence_default": "high"},

    "slow_response":         {"label": "Медленный ответ сервера (TTFB)",       "group": "performance","severity": "warning",  "weight": 3, "recommendation": "Оптимизируйте бэкенд/хостинг — время ответа выше 1 секунды снижает конверсию. Это эвристика по TTFB, не полноценный Core Web Vitals тест.", "confidence_default": "medium"},
    "large_page_size":       {"label": "Большой вес страницы",                 "group": "performance","severity": "info",     "weight": 2, "recommendation": "Сожмите изображения и минифицируйте CSS/JS — страница тяжелее 2 МБ.", "confidence_default": "high"},
    "redirect_chain":        {"label": "Цепочка редиректов",                   "group": "performance","severity": "warning",  "weight": 2, "recommendation": "Ведите ссылки сразу на финальный URL, избегая нескольких 3xx подряд.", "confidence_default": "high"},
    "images_missing_dimensions": {"label": "У изображений нет width/height", "group": "performance", "severity": "warning", "weight": 2, "recommendation": "Задайте width и height или корректное соотношение сторон, чтобы снизить layout shifts.", "confidence_default": "high"},
    "images_not_lazy": {"label": "Много изображений без lazy-loading", "group": "performance", "severity": "info", "weight": 1, "recommendation": "Для некритичных изображений (не в первом экране) используйте loading=\"lazy\".", "confidence_default": "medium"},
    "no_compression":        {"label": "Ответ сервера не сжат (gzip/br)",      "group": "performance","severity": "info",     "weight": 2, "recommendation": "Включите gzip или brotli сжатие для текстовых ответов.", "confidence_default": "medium"},
    "no_cache_headers":      {"label": "Нет кэширующих заголовков",            "group": "performance","severity": "info",     "weight": 1, "recommendation": "Добавьте Cache-Control/ETag/Last-Modified для статических ресурсов и HTML, где это уместно.", "confidence_default": "low"},

    "no_viewport":           {"label": "Отсутствует meta viewport",            "group": "mobile",     "severity": "warning",  "weight": 4, "recommendation": "Добавьте <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\"> для мобильной адаптивности.", "confidence_default": "high"},
    "no_favicon":            {"label": "Отсутствует favicon",                  "group": "mobile",     "severity": "info",     "weight": 1, "recommendation": "Добавьте favicon.ico или <link rel=\"icon\"> — влияет на восприятие бренда во вкладках/закладках.", "confidence_default": "high"},
    "viewport_not_responsive": {"label": "Viewport не использует width=device-width", "group": "mobile", "severity": "info", "weight": 2, "recommendation": "Используйте width=device-width в meta viewport для корректного масштабирования на мобильных.", "confidence_default": "medium"},
    "viewport_zoom_disabled": {"label": "Viewport запрещает масштабирование (user-scalable=no)", "group": "mobile", "severity": "warning", "weight": 3, "recommendation": "Не отключайте зум пользователю — это ухудшает доступность на мобильных устройствах.", "confidence_default": "high"},

    # Расширенные проверки индексации/canonical/hreflang
    "canonical_mismatch": {"label": "Canonical отличается от текущего URL", "group": "indexing", "severity": "warning", "weight": 3, "recommendation": "Проверьте canonical: он должен указывать на предпочтительный индексируемый URL.", "confidence_default": "medium"},
    "canonical_malformed": {"label": "Canonical некорректен (нет href / не парсится)", "group": "indexing", "severity": "warning", "weight": 3, "recommendation": "Убедитесь, что href у rel=canonical указан и является валидным URL.", "confidence_default": "high"},
    "canonical_multiple": {"label": "Несколько тегов canonical на странице", "group": "indexing", "severity": "critical", "weight": 5, "recommendation": "Оставьте только один <link rel=\"canonical\"> на странице.", "confidence_default": "high"},
    "canonical_other_domain": {"label": "Canonical ведёт на другой домен", "group": "indexing", "severity": "warning", "weight": 4, "recommendation": "Проверьте, действительно ли канонический URL должен указывать на другой домен.", "confidence_default": "medium"},
    "canonical_http_on_https": {"label": "Canonical на HTTPS-странице указывает на HTTP", "group": "security", "severity": "warning", "weight": 3, "recommendation": "Используйте HTTPS-версию URL в rel=canonical.", "confidence_default": "high"},
    "canonical_to_noindex": {"label": "Canonical ведёт на noindex-страницу", "group": "indexing", "severity": "warning", "weight": 4, "recommendation": "Canonical не должен указывать на страницу, закрытую noindex.", "confidence_default": "high"},
    "canonical_to_error": {"label": "Canonical ведёт на 4xx/5xx", "group": "indexing", "severity": "warning", "weight": 5, "recommendation": "Canonical должен указывать на существующую, доступную страницу.", "confidence_default": "high"},
    "canonical_to_redirect": {"label": "Canonical ведёт на редиректящий URL", "group": "indexing", "severity": "info", "weight": 2, "recommendation": "Укажите в canonical финальный URL после редиректа, а не промежуточный.", "confidence_default": "high"},
    "canonical_chain": {"label": "Цепочка canonical (canonical ведёт на страницу с другим canonical)", "group": "indexing", "severity": "info", "weight": 2, "recommendation": "Каждый canonical в цепочке должен в итоге указывать на один и тот же финальный URL напрямую.", "confidence_default": "medium"},
    "canonical_fragment": {"label": "Canonical содержит fragment (#)", "group": "indexing", "severity": "info", "weight": 1, "recommendation": "Уберите #fragment из canonical URL — он не влияет на индексацию, но обычно избыточен.", "confidence_default": "high"},
    "canonical_query_mismatch": {"label": "Canonical отличается только query-параметрами", "group": "indexing", "severity": "info", "weight": 1, "recommendation": "Как правило, это ожидаемо (например, для отслеживающих параметров) — просто проверьте, что это осознанное решение.", "confidence_default": "low"},

    "hreflang_invalid": {"label": "Проблемы hreflang", "group": "indexing", "severity": "warning", "weight": 3, "recommendation": "Проверьте ISO-коды языков/регионов, абсолютные URL и взаимные ссылки hreflang.", "confidence_default": "high"},
    "hreflang_duplicate_lang": {"label": "Дублирующийся язык/регион в hreflang", "group": "indexing", "severity": "warning", "weight": 2, "recommendation": "Для каждого языка/региона должна быть только одна hreflang-ссылка.", "confidence_default": "high"},
    "hreflang_missing_return": {"label": "Нет взаимной (return) hreflang-ссылки", "group": "indexing", "severity": "warning", "weight": 3, "recommendation": "Целевая страница должна содержать hreflang-ссылку обратно на текущую страницу.", "confidence_default": "medium"},
    "hreflang_to_error": {"label": "hreflang ведёт на 4xx/5xx", "group": "indexing", "severity": "warning", "weight": 4, "recommendation": "hreflang должен указывать на существующую доступную страницу.", "confidence_default": "high"},
    "hreflang_to_noindex": {"label": "hreflang ведёт на noindex-страницу", "group": "indexing", "severity": "warning", "weight": 3, "recommendation": "hreflang не должен указывать на страницу, закрытую от индексации.", "confidence_default": "high"},
    "hreflang_self_missing": {"label": "Нет self-referencing hreflang", "group": "indexing", "severity": "info", "weight": 1, "recommendation": "Страница с hreflang должна включать hreflang-ссылку саму на себя.", "confidence_default": "medium"},
    "http_hreflang_url": {"label": "hreflang ссылается на HTTP вместо HTTPS", "group": "security", "severity": "info", "weight": 1, "recommendation": "Используйте HTTPS-версии URL в hreflang.", "confidence_default": "medium"},

    "noindex_header": {"label": "X-Robots-Tag содержит noindex", "group": "indexing", "severity": "warning", "weight": 3, "recommendation": "Проверьте HTTP-заголовок X-Robots-Tag: noindex закрывает URL от индексации.", "confidence_default": "high"},
    "nofollow_internal": {"label": "Внутренние ссылки с nofollow", "group": "links", "severity": "info", "weight": 1, "recommendation": "Проверьте, действительно ли внутренним ссылкам нужен nofollow.", "confidence_default": "medium"},
    "broken_external_link": {"label": "Битая внешняя ссылка", "group": "links", "severity": "warning", "weight": 3, "recommendation": "Замените или уберите ссылку на внешний ресурс, который не отвечает.", "confidence_default": "high"},
    "external_timeout": {"label": "Внешняя ссылка не ответила за отведённое время", "group": "links", "severity": "info", "weight": 1, "recommendation": "Это может быть временной проблемой внешнего сайта, а не обязательно битой ссылкой — перепроверьте позже.", "confidence_default": "low"},
    "no_incoming_internal_links": {"label": "Нет входящих внутренних ссылок (orphan page)", "group": "links", "severity": "warning", "weight": 3, "recommendation": "Добавьте внутренние ссылки на эту страницу — сейчас на неё не ведёт ни одна ссылка с сайта.", "confidence_default": "medium"},
    "weakly_linked_page": {"label": "Очень мало входящих внутренних ссылок", "group": "links", "severity": "info", "weight": 1, "recommendation": "Рассмотрите добавление дополнительных внутренних ссылок на эту страницу.", "confidence_default": "low"},

    "query_parameter_url": {"label": "URL содержит query-параметры", "group": "url", "severity": "info", "weight": 1, "recommendation": "Проверьте параметры URL и canonical, чтобы избежать ненужных дублей. Служебные параметры (пагинация, поиск) — это нормально.", "confidence_default": "low"},
    "url_too_long": {"label": "Слишком длинный URL", "group": "url", "severity": "info", "weight": 1, "recommendation": "Старайтесь укладываться в разумную длину URL (обычно до ~115 символов).", "confidence_default": "low"},
    "url_uppercase": {"label": "URL содержит заглавные буквы", "group": "url", "severity": "info", "weight": 1, "recommendation": "Используйте только нижний регистр в URL, чтобы избежать дублей из-за регистрозависимости.", "confidence_default": "medium"},
    "url_multiple_slashes": {"label": "URL содержит повторяющиеся слеши", "group": "url", "severity": "info", "weight": 1, "recommendation": "Уберите повторяющиеся слеши (//) из пути URL.", "confidence_default": "high"},
    "url_encoded_chars": {"label": "URL содержит percent-encoded символы", "group": "url", "severity": "info", "weight": 1, "recommendation": "По возможности используйте человекочитаемые URL без избыточного кодирования.", "confidence_default": "low"},
    "url_contains_space": {"label": "URL содержит пробел (%20/+)", "group": "url", "severity": "info", "weight": 1, "recommendation": "Уберите пробелы из URL — замените их на дефис.", "confidence_default": "medium"},
    "url_semicolon_param": {"label": "URL содержит устаревшие ;-параметры", "group": "url", "severity": "info", "weight": 1, "recommendation": "Используйте query-параметры (?key=value) вместо matrix-параметров (;key=value).", "confidence_default": "low"},
    "url_repeated_query_param": {"label": "URL содержит повторяющийся query-параметр", "group": "url", "severity": "info", "weight": 1, "recommendation": "Уберите дублирующиеся query-параметры — обычно это ошибка генерации ссылок.", "confidence_default": "medium"},
    "url_empty_query_param": {"label": "URL содержит пустой query-параметр", "group": "url", "severity": "info", "weight": 1, "recommendation": "Уберите параметры без значения (?param=) из URL.", "confidence_default": "medium"},
    "duplicate_url_variant": {"label": "Похожий URL-вариант той же страницы (регистр/слеши)", "group": "url", "severity": "info", "weight": 2, "recommendation": "Приведите ссылки к единому виду (регистр, слеши) и/или настройте 301-редирект на канонический вариант.", "confidence_default": "medium"},

    # Sitemap consistency
    "sitemap_url_error": {"label": "URL из sitemap вернул 4xx/5xx", "group": "crawling", "severity": "warning", "weight": 4, "recommendation": "Уберите URL из sitemap.xml или исправьте страницу, чтобы она отдавала 200 OK.", "confidence_default": "high"},
    "sitemap_url_redirect": {"label": "URL из sitemap редиректит", "group": "crawling", "severity": "info", "weight": 2, "recommendation": "Укажите в sitemap.xml финальный URL после редиректа.", "confidence_default": "high"},
    "sitemap_url_noindex": {"label": "URL из sitemap закрыт noindex", "group": "indexing", "severity": "warning", "weight": 3, "recommendation": "Уберите noindex-страницы из sitemap.xml — это противоречивый сигнал для поисковика.", "confidence_default": "high"},
    "sitemap_url_blocked": {"label": "URL из sitemap заблокирован robots.txt", "group": "crawling", "severity": "warning", "weight": 4, "recommendation": "Не включайте в sitemap.xml страницы, закрытые Disallow в robots.txt.", "confidence_default": "high"},
    "sitemap_canonical_mismatch": {"label": "URL из sitemap не совпадает с его canonical", "group": "indexing", "severity": "info", "weight": 2, "recommendation": "В sitemap.xml должны быть перечислены канонические URL.", "confidence_default": "medium"},
    "sitemap_duplicate_url": {"label": "Дублирующийся URL внутри sitemap.xml", "group": "crawling", "severity": "info", "weight": 1, "recommendation": "Уберите повторяющиеся <url> записи из sitemap.xml.", "confidence_default": "high"},
    "sitemap_invalid_url": {"label": "Невалидный URL в sitemap.xml", "group": "crawling", "severity": "warning", "weight": 2, "recommendation": "Исправьте некорректные <loc> записи в sitemap.xml (должны быть абсолютные URL).", "confidence_default": "high"},
}


def issue_meta(code: str) -> dict:
    return CATEGORY_META.get(code, {"label": code, "group": "content", "severity": "info", "weight": 1, "recommendation": "", "confidence_default": "low"})


# --------------------------------------------------------------------------
# Безопасный JSON-LD extractor
# --------------------------------------------------------------------------

def _safe_extract_jsonld_nodes(raw_data: Any) -> list[dict]:
    """
    Безопасно "разворачивает" произвольную структуру JSON-LD (dict / list /
    вложенные @graph) в плоский список dict-объектов, БЕЗ мутации исходной
    структуры во время итерации (в отличие от старой реализации, которая
    расширяла список, по которому шёл `for`).
    """
    nodes: list[dict] = []
    stack: list = [raw_data]
    seen_ids = set()
    while stack:
        item = stack.pop()
        if isinstance(item, list):
            stack.extend(item)
            continue
        if not isinstance(item, dict):
            continue
        node_key = id(item)
        if node_key in seen_ids:
            continue
        seen_ids.add(node_key)
        nodes.append(item)
        graph = item.get("@graph")
        if isinstance(graph, list):
            stack.extend(graph)
        elif isinstance(graph, dict):
            stack.append(graph)
    return nodes


def _jsonld_node_types(node: dict) -> list[str]:
    typ = node.get("@type")
    if isinstance(typ, list):
        return [str(t) for t in typ]
    if typ:
        return [str(typ)]
    return []


def _jsonld_has_author(node: dict) -> bool:
    author = node.get("author")
    if not author:
        return False
    if isinstance(author, str):
        return bool(author.strip())
    if isinstance(author, dict):
        return bool(author.get("name") or author.get("@id"))
    if isinstance(author, list):
        return any(_jsonld_has_author({"author": a}) for a in author)
    return False


# Поля, которые считаются "базово ожидаемыми" для распространённых типов
# JSON-LD объектов. Это НЕ полноценная Schema.org валидация — только грубая
# оценка "выглядит ли объект содержательным", чтобы не заявлять "invalid"
# только из-за отсутствия необязательного поля.
_SCHEMA_EXPECTED_FIELDS = {
    "Article": ("headline",), "NewsArticle": ("headline",), "BlogPosting": ("headline",),
    "Product": ("name",), "Organization": ("name",), "WebSite": ("name", "url"),
    "LocalBusiness": ("name", "address"), "FAQPage": ("mainEntity",),
    "HowTo": ("name", "step"), "BreadcrumbList": ("itemListElement",),
}


def _jsonld_semantically_complete(nodes: list[dict]) -> Optional[bool]:
    if not nodes:
        return None
    complete = True
    checked_any = False
    for node in nodes:
        for typ in _jsonld_node_types(node):
            expected = _SCHEMA_EXPECTED_FIELDS.get(typ)
            if not expected:
                continue
            checked_any = True
            if not all(node.get(field_name) for field_name in expected):
                complete = False
    if not checked_any:
        return None
    return complete


# --------------------------------------------------------------------------
# Результат анализа одной страницы
# --------------------------------------------------------------------------

@dataclass
class PageReport:
    url: str
    depth: int
    status_code: Optional[int] = None
    title: Optional[str] = None
    meta_description: Optional[str] = None
    h1_count: int = 0
    headings_present: set = field(default_factory=set)
    images_total: int = 0
    images_without_alt: int = 0
    has_canonical: bool = False
    robots_noindex: bool = False
    response_time_ms: Optional[int] = None
    page_size_bytes: Optional[int] = None
    redirect_count: int = 0
    word_count: Optional[int] = None
    has_viewport: bool = False
    has_open_graph: bool = False
    structured_data_types: list = field(default_factory=list)
    internal_links: int = 0
    external_links: int = 0
    issues: list = field(default_factory=list)  # [{"code": str, "message": str, "confidence": str}]
    # Расширенные сигналы (из первой волны улучшений)
    hreflang_count: int = 0
    canonical_url: Optional[str] = None
    has_meta_robots: bool = False
    has_x_robots_tag: bool = False
    nofollow_links: int = 0
    external_links_checked: int = 0
    images_missing_dimensions: int = 0
    images_not_lazy: int = 0
    forms_without_labels: int = 0
    duplicate_h1_text: bool = False
    text_html_ratio: Optional[float] = None
    language: Optional[str] = None
    has_author: bool = False
    has_date_published: bool = False
    has_date_modified: bool = False
    schema_errors: int = 0
    schema_types: list = field(default_factory=list)

    # Поля v3
    requested_url: Optional[str] = None
    final_url: Optional[str] = None
    requested_scheme: Optional[str] = None
    final_scheme: Optional[str] = None
    redirect_chain: list = field(default_factory=list)
    is_redirect_loop: bool = False
    ssl_error: bool = False
    content_encoding: Optional[str] = None
    cache_control: Optional[str] = None
    etag: Optional[str] = None
    last_modified: Optional[str] = None
    scripts_count: int = 0
    stylesheets_count: int = 0
    inline_css_bytes: int = 0
    inline_js_bytes: int = 0
    has_preload: bool = False
    has_preconnect: bool = False
    has_dns_prefetch: bool = False
    canonical_count: int = 0
    canonical_is_self: bool = False
    canonical_relative: bool = False
    canonical_has_fragment: bool = False
    images_alt_missing: int = 0
    images_alt_empty_decorative: int = 0
    sponsored_links: int = 0
    ugc_links: int = 0
    hreflang_entries: list = field(default_factory=list)  # [{"lang":..,"href":..}]
    page_type: str = "unknown"
    soft_404: bool = False
    is_paginated: bool = False
    pagination_rel_next: Optional[str] = None
    pagination_rel_prev: Optional[str] = None
    robots_blocked: bool = False

    # Поля v3.1
    x_robots_noindex: bool = False
    is_indexable: Optional[bool] = None
    indexability_reasons: list = field(default_factory=list)
    redirect_statuses: list = field(default_factory=list)
    incoming_internal_links: int = 0
    images_alt_empty: int = 0
    images_decorative: int = 0
    images_broken: int = 0
    canonical_target_status: Optional[int] = None
    canonical_target_noindex: Optional[bool] = None
    canonical_target_is_redirect: Optional[bool] = None
    canonical_chain_length: int = 0
    schema_semantically_complete: Optional[bool] = None
    hreflang_self_present: Optional[bool] = None
    external_timeouts: int = 0
    third_party_domains: list = field(default_factory=list)
    duplicate_url_variant_group: Optional[str] = None

    def add_issue(self, code: str, message: str, confidence: Optional[str] = None):
        if confidence is None:
            confidence = issue_meta(code).get("confidence_default", "medium")
        self.issues.append({"code": code, "message": message, "confidence": confidence})

    def to_dict(self) -> dict:
        return {
            "url": self.url,
            "depth": self.depth,
            "status_code": self.status_code,
            "title": self.title,
            "meta_description": self.meta_description,
            "h1_count": self.h1_count,
            "headings_present": sorted(self.headings_present),
            "images_total": self.images_total,
            "images_without_alt": self.images_without_alt,
            "has_canonical": self.has_canonical,
            "robots_noindex": self.robots_noindex,
            "response_time_ms": self.response_time_ms,
            "page_size_bytes": self.page_size_bytes,
            "redirect_count": self.redirect_count,
            "word_count": self.word_count,
            "has_viewport": self.has_viewport,
            "has_open_graph": self.has_open_graph,
            "structured_data_types": self.structured_data_types,
            "internal_links": self.internal_links,
            "external_links": self.external_links,
            "issues": self.issues,
            "hreflang_count": self.hreflang_count,
            "canonical_url": self.canonical_url,
            "has_meta_robots": self.has_meta_robots,
            "has_x_robots_tag": self.has_x_robots_tag,
            "nofollow_links": self.nofollow_links,
            "external_links_checked": self.external_links_checked,
            "images_missing_dimensions": self.images_missing_dimensions,
            "images_not_lazy": self.images_not_lazy,
            "forms_without_labels": self.forms_without_labels,
            "duplicate_h1_text": self.duplicate_h1_text,
            "text_html_ratio": self.text_html_ratio,
            "language": self.language,
            "has_author": self.has_author,
            "has_date_published": self.has_date_published,
            "has_date_modified": self.has_date_modified,
            "schema_errors": self.schema_errors,
            "schema_types": self.schema_types,
            # v3
            "requested_url": self.requested_url,
            "final_url": self.final_url,
            "requested_scheme": self.requested_scheme,
            "final_scheme": self.final_scheme,
            "redirect_chain": self.redirect_chain,
            "is_redirect_loop": self.is_redirect_loop,
            "ssl_error": self.ssl_error,
            "content_encoding": self.content_encoding,
            "cache_control": self.cache_control,
            "etag": self.etag,
            "last_modified": self.last_modified,
            "scripts_count": self.scripts_count,
            "stylesheets_count": self.stylesheets_count,
            "inline_css_bytes": self.inline_css_bytes,
            "inline_js_bytes": self.inline_js_bytes,
            "has_preload": self.has_preload,
            "has_preconnect": self.has_preconnect,
            "has_dns_prefetch": self.has_dns_prefetch,
            "canonical_count": self.canonical_count,
            "canonical_is_self": self.canonical_is_self,
            "canonical_relative": self.canonical_relative,
            "canonical_has_fragment": self.canonical_has_fragment,
            "images_alt_missing": self.images_alt_missing,
            "images_alt_empty_decorative": self.images_alt_empty_decorative,
            "sponsored_links": self.sponsored_links,
            "ugc_links": self.ugc_links,
            "hreflang_entries": self.hreflang_entries,
            "page_type": self.page_type,
            "soft_404": self.soft_404,
            "is_paginated": self.is_paginated,
            "pagination_rel_next": self.pagination_rel_next,
            "pagination_rel_prev": self.pagination_rel_prev,
            "robots_blocked": self.robots_blocked,
            # v3.1
            "x_robots_noindex": self.x_robots_noindex,
            "is_indexable": self.is_indexable,
            "indexability_reasons": self.indexability_reasons,
            "redirect_statuses": self.redirect_statuses,
            "incoming_internal_links": self.incoming_internal_links,
            "images_alt_empty": self.images_alt_empty,
            "images_decorative": self.images_decorative,
            "images_broken": self.images_broken,
            "canonical_target_status": self.canonical_target_status,
            "canonical_target_noindex": self.canonical_target_noindex,
            "canonical_target_is_redirect": self.canonical_target_is_redirect,
            "canonical_chain_length": self.canonical_chain_length,
            "schema_semantically_complete": self.schema_semantically_complete,
            "hreflang_self_present": self.hreflang_self_present,
            "external_timeouts": self.external_timeouts,
            "third_party_domains": self.third_party_domains,
            "duplicate_url_variant_group": self.duplicate_url_variant_group,
        }


# --------------------------------------------------------------------------
# robots.txt
# --------------------------------------------------------------------------

class RobotsInfo:
    """Загружает и разбирает robots.txt: правила Disallow/Allow и ссылки Sitemap:.

    status может быть: "not_checked", "ok", "not_found", "http_error",
    "timeout", "connection_error". found=True означает, что robots.txt был
    успешно получен и разобран (HTTP 200) — это отдельно от статуса, чтобы
    UI мог различать "robots.txt отсутствует" и "robots.txt недоступен из-за
    ошибки сети", что раньше не различалось.
    """

    def __init__(self):
        self.parser: Optional[RobotFileParser] = None
        self.sitemap_urls: list = []
        self.found = False
        self.status = "not_checked"
        self.error: Optional[str] = None
        self.wildcard_user_agent = False
        self.user_agent_count = 0

    async def load(self, session: aiohttp.ClientSession, base_url: str):
        robots_url = urljoin(base_url, "/robots.txt")
        try:
            async with session.get(robots_url, timeout=aiohttp.ClientTimeout(total=REQUEST_TIMEOUT)) as resp:
                if resp.status == 404:
                    self.status = "not_found"
                    return
                if resp.status != 200:
                    self.status = "http_error"
                    self.error = f"HTTP {resp.status}"
                    return
                text = await resp.text(errors="ignore")
        except asyncio.TimeoutError:
            self.status = "timeout"
            self.error = "Timeout while fetching robots.txt"
            return
        except Exception as exc:  # noqa: BLE001 — отсутствие robots.txt не должно останавливать аудит
            self.status = "connection_error"
            self.error = str(exc)
            return

        self.found = True
        self.status = "ok"
        self.parser = RobotFileParser()
        try:
            self.parser.parse(text.splitlines())
        except Exception as exc:  # noqa: BLE001 — некорректный robots.txt не должен ронять аудит
            self.status = "parse_error"
            self.error = str(exc)
            self.parser = None
            return

        for line in text.splitlines():
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            if line.lower().startswith("sitemap:"):
                sitemap_url = line.split(":", 1)[1].strip()
                if sitemap_url and sitemap_url not in self.sitemap_urls:
                    self.sitemap_urls.append(sitemap_url)
            elif line.lower().startswith("user-agent:"):
                self.user_agent_count += 1
                agent = line.split(":", 1)[1].strip()
                if agent == "*":
                    self.wildcard_user_agent = True

    def can_fetch(self, url: str) -> bool:
        if not self.parser:
            return True
        try:
            return self.parser.can_fetch(USER_AGENT, url) and self.parser.can_fetch("*", url)
        except Exception:  # noqa: BLE001
            return True

    def to_dict(self) -> dict:
        return {
            "found": self.found,
            "status": self.status,
            "error": self.error,
            "sitemap_urls": self.sitemap_urls,
            "wildcard_user_agent": self.wildcard_user_agent,
            "user_agent_groups_count": self.user_agent_count,
            "multiple_sitemap_declarations": len(self.sitemap_urls) > 1,
        }


# --------------------------------------------------------------------------
# sitemap.xml (включая sitemap index с вложенными картами, gzip, cycle-guard)
# --------------------------------------------------------------------------

class SitemapInfo:
    """Собирает список URL из sitemap.xml (и вложенных дочерних sitemap).

    Поддерживает: sitemap index, gzip sitemap (без внешних зависимостей —
    через стандартный модуль gzip), защиту от циклов (sitemap A ссылается
    на sitemap B, который снова ссылается на A) и фильтрацию URL с чужого
    домена (например, если в sitemap по ошибке/специально попали абсолютные
    URL другого сайта). Также отдельно фиксирует дубликаты и невалидные
    записи <loc>, чтобы их можно было показать как отдельные проблемы.
    """

    def __init__(self, domain: str):
        self.domain = domain
        self.urls: set = set()
        self.found = False
        self.details: list = []  # [{"url":.., "status":.., "count":.., "error":.., "content_type":..}]
        self._seen_sitemaps: set = set()
        self.duplicate_urls: list = []
        self.invalid_urls: list = []
        self.external_domain_urls: list = []

    @staticmethod
    def _normalize_sitemap_url(url: str) -> str:
        url, _ = urldefrag(url)
        return url.rstrip("/")

    async def load(self, session: aiohttp.ClientSession, base_url: str, candidate_urls: list):
        candidates = list(dict.fromkeys(candidate_urls)) or [urljoin(base_url, "/sitemap.xml")]
        queue = list(candidates)
        children_discovered = 0

        while queue and len(self.urls) < MAX_SITEMAP_URLS and len(self.details) < (MAX_CHILD_SITEMAPS + 1):
            sitemap_url = queue.pop(0)
            norm = self._normalize_sitemap_url(sitemap_url)
            if norm in self._seen_sitemaps:
                continue  # защита от циклов sitemap index
            self._seen_sitemaps.add(norm)

            status, content_type, raw_bytes, error = await self._fetch(session, sitemap_url)
            detail = {"url": sitemap_url, "status": status, "count": 0, "error": error, "content_type": content_type}

            if raw_bytes is None:
                self.details.append(detail)
                continue

            xml_text = self._maybe_decompress(sitemap_url, content_type, raw_bytes)
            if xml_text is None:
                detail["error"] = detail["error"] or "Failed to decode/decompress sitemap body"
                self.details.append(detail)
                continue

            self.found = True
            try:
                soup = BeautifulSoup(xml_text, "xml")
            except Exception as exc:  # noqa: BLE001
                detail["error"] = f"XML parse error: {exc}"
                self.details.append(detail)
                continue

            sitemap_tags = soup.find_all("sitemap")
            if sitemap_tags:
                added = 0
                for tag in sitemap_tags:
                    if children_discovered >= MAX_CHILD_SITEMAPS:
                        break
                    loc = tag.find("loc")
                    if loc and loc.get_text(strip=True):
                        child_url = loc.get_text(strip=True)
                        if self._normalize_sitemap_url(child_url) not in self._seen_sitemaps:
                            queue.append(child_url)
                            children_discovered += 1
                            added += 1
                detail["count"] = added
                self.details.append(detail)
                continue

            url_count = 0
            for url_tag in soup.find_all("url"):
                loc = url_tag.find("loc")
                if not loc or not loc.get_text(strip=True):
                    continue
                candidate = loc.get_text(strip=True)
                candidate_norm = candidate.rstrip("/")
                parsed_candidate = urlparse(candidate_norm)
                if not parsed_candidate.scheme or not parsed_candidate.netloc:
                    if len(self.invalid_urls) < 200:
                        self.invalid_urls.append(candidate)
                    continue
                if parsed_candidate.netloc != self.domain:
                    if len(self.external_domain_urls) < 200:
                        self.external_domain_urls.append(candidate)
                    continue  # не принимаем URL другого домена как URL текущего сайта
                if candidate_norm in self.urls:
                    if len(self.duplicate_urls) < 200:
                        self.duplicate_urls.append(candidate_norm)
                    continue
                self.urls.add(candidate_norm)
                url_count += 1
                if len(self.urls) >= MAX_SITEMAP_URLS:
                    break
            detail["count"] = url_count
            self.details.append(detail)

    @staticmethod
    def _maybe_decompress(url: str, content_type: str, raw_bytes: bytes) -> Optional[str]:
        looks_gzip = raw_bytes[:2] == b"\x1f\x8b" or url.lower().endswith(".gz") or "gzip" in (content_type or "").lower()
        try:
            if looks_gzip:
                try:
                    raw_bytes = gzip.decompress(raw_bytes)
                except OSError:
                    pass  # не было валидным gzip — пробуем как обычный текст
            return raw_bytes.decode("utf-8", errors="ignore")
        except Exception:  # noqa: BLE001
            return None

    @staticmethod
    async def _fetch(session: aiohttp.ClientSession, url: str):
        """Возвращает (status, content_type, raw_bytes|None, error|None)."""
        try:
            async with session.get(url, timeout=aiohttp.ClientTimeout(total=REQUEST_TIMEOUT)) as resp:
                content_type = resp.headers.get("Content-Type", "")
                if resp.status != 200:
                    return resp.status, content_type, None, f"HTTP {resp.status}"
                raw = await resp.read()
                return resp.status, content_type, raw, None
        except asyncio.TimeoutError:
            return 0, "", None, "timeout"
        except Exception as exc:  # noqa: BLE001
            return 0, "", None, str(exc)

    def to_dict(self) -> dict:
        return {
            "found": self.found,
            "url_count": len(self.urls),
            "sitemaps": self.details,
            "duplicate_urls_count": len(self.duplicate_urls),
            "invalid_urls_count": len(self.invalid_urls),
            "external_domain_urls_count": len(self.external_domain_urls),
        }


# --------------------------------------------------------------------------
# Асинхронный рекурсивный краулер
# --------------------------------------------------------------------------

class SiteCrawler:
    """
    Обходит сайт по внутренним ссылкам, собирает технические SEO-параметры
    каждой страницы. Поддерживает уважение robots.txt, ограничение по глубине
    и количеству страниц, колбэк прогресса и мягкую отмену через cancel_event.

    Синхронизация worker/queue (v3): вместо проверки `queue.empty()` (что
    создавало race condition — воркер мог быть "между" обработкой страницы
    и постановкой найденных на ней ссылок в очередь) используется счётчик
    `pending` — количество URL, которые сейчас либо лежат в очереди, либо
    находятся в обработке у какого-то воркера (включая постановку их дочерних
    ссылок в очередь). `pending` увеличивается ДО постановки URL в очередь и
    уменьшается только ПОСЛЕ того, как страница полностью обработана,
    включая постановку найденных на ней ссылок в очередь. Когда pending
    становится 0, взводится `completion_event` — обход точно завершён, а не
    "очередь просто временно пуста".
    """

    def __init__(
        self,
        start_url: str,
        max_pages: int,
        max_depth: int,
        respect_robots: bool = True,
        check_images: bool = False,
        check_external_links: bool = False,
        on_progress: Optional[Callable[[int, int], None]] = None,
        cancel_event: Optional[asyncio.Event] = None,
    ):
        self.start_url = start_url.rstrip("/") or start_url
        self.max_pages = min(max(int(max_pages), 1), MAX_CRAWL_URLS_HARD)
        self.max_depth = min(max(int(max_depth), 0), 20)
        self.respect_robots = respect_robots
        self.check_images = check_images
        self.check_external_links = check_external_links
        self.on_progress = on_progress or (lambda scanned, queued: None)
        self.cancel_event = cancel_event or asyncio.Event()
        self.domain = urlparse(start_url).netloc

        self.visited = set()
        self.queue: asyncio.Queue = asyncio.Queue()
        self.pages: list = []
        self.titles_seen = defaultdict(list)
        self.descriptions_seen = defaultdict(list)
        self.blocked_urls: list = []
        self.homepage_checked_favicon = False
        self.has_favicon = False

        self.semaphore = asyncio.Semaphore(CONCURRENT_REQUESTS)
        self.lock = asyncio.Lock()
        self.robots = RobotsInfo()
        self.sitemap = SitemapInfo(domain=self.domain)
        self._start_time = 0.0

        # v3: корректная синхронизация lifecycle обхода
        self.pending = 0
        self.completion_event: asyncio.Event = asyncio.Event()
        self._query_variants_per_path: dict = defaultdict(set)
        self.hreflang_registry: dict = {}  # url -> [{"lang":..,"href":..}]
        self.reports_by_url: dict = {}      # url -> PageReport (для post-crawl анализа)

        # v3.1
        self.pages_skipped_limit = 0
        self.crawl_termination_reason = "completed"
        self.crawl_started_at: Optional[str] = None
        self.crawl_finished_at: Optional[str] = None
        self.incoming_link_sources: dict = defaultdict(set)  # target_norm -> set(source_norm)

    # -- вспомогательные методы -------------------------------------------------

    def _normalize(self, url: str) -> str:
        url, _ = urldefrag(url)
        if url.endswith("/") and url != self.start_url:
            url = url[:-1]
        return url

    def _is_same_domain(self, url: str) -> bool:
        return urlparse(url).netloc == self.domain

    @staticmethod
    def _is_crawlable_href(href: str) -> bool:
        return not href.startswith(("mailto:", "tel:", "javascript:", "#"))

    def _time_budget_exceeded(self) -> bool:
        return (time.monotonic() - self._start_time) > MAX_JOB_DURATION

    def _detect_page_type(self, url: str, soup: BeautifulSoup, depth: int) -> str:
        """Лёгкая heuristic-классификация страницы по URL/контенту, без внешних AI-API."""
        path = urlparse(url).path or "/"
        if depth == 0 and (path in ("", "/")):
            return "homepage"
        for page_type, pattern in PAGE_TYPE_URL_PATTERNS:
            if pattern.search(path):
                return page_type
        if soup.find("form", attrs={"action": re.compile(r"cart|checkout", re.I)}):
            return "checkout"
        if soup.find(attrs={"itemtype": re.compile(r"schema\.org/Product", re.I)}):
            return "product"
        if soup.find("nav", attrs={"aria-label": re.compile(r"breadcrumb", re.I)}) and soup.find("article"):
            return "article"
        if soup.find("article"):
            return "article"
        return "unknown"

    # -- основной обход ----------------------------------------------------------

    async def crawl(self) -> dict:
        self._start_time = time.monotonic()
        self.crawl_started_at = datetime.now(timezone.utc).isoformat()
        self.pending = 0
        self.completion_event = asyncio.Event()

        connector = aiohttp.TCPConnector(limit=CONCURRENT_REQUESTS)  # SSL проверяется стандартно (без ssl=False)
        async with aiohttp.ClientSession(
            headers={"User-Agent": USER_AGENT},
            timeout=aiohttp.ClientTimeout(total=REQUEST_TIMEOUT),
            connector=connector,
        ) as session:
            if self.respect_robots:
                await self.robots.load(session, self.start_url)

            sitemap_candidates = list(self.robots.sitemap_urls)
            await self.sitemap.load(session, self.start_url, sitemap_candidates)

            await self._enqueue(self.start_url, 0, session=None)  # ставим стартовый URL (без проверки robots)

            workers = [asyncio.create_task(self._worker(session)) for _ in range(CONCURRENT_REQUESTS)]
            await self._supervise()
            self.cancel_event.set()
            for w in workers:
                w.cancel()
            await asyncio.gather(*workers, return_exceptions=True)

        self.crawl_finished_at = datetime.now(timezone.utc).isoformat()
        self._detect_duplicates()
        self._detect_near_duplicate_titles()
        orphan_pages = self._compute_orphan_pages()
        self._analyze_hreflang_relationships()
        self._analyze_canonical_targets()
        self._compute_incoming_links()
        self._detect_url_variants()
        self._compute_indexability_flags()
        sitemap_problem_urls = self._analyze_sitemap_consistency()

        return {
            "pages": self.pages,
            "blocked_urls": self.blocked_urls,
            "sitemap_found": self.sitemap.found,
            "sitemap_urls_count": len(self.sitemap.urls),
            "sitemap_urls": sorted(self.sitemap.urls),
            "sitemap_details": self.sitemap.to_dict(),
            "sitemap_duplicate_urls": self.sitemap.duplicate_urls[:50],
            "sitemap_invalid_urls": self.sitemap.invalid_urls[:50],
            "sitemap_problem_urls": sitemap_problem_urls,
            "orphan_pages": orphan_pages,
            "robots_found": self.robots.found,
            "robots_status": self.robots.status,
            "robots_error": self.robots.error,
            "robots_wildcard_user_agent": self.robots.wildcard_user_agent,
            "robots_multiple_sitemaps": len(self.robots.sitemap_urls) > 1,
            # v3.1 метаданные обхода
            "pages_discovered": len(self.visited),
            "pages_skipped_limit": self.pages_skipped_limit,
            "crawl_limit_reached": len(self.pages) >= self.max_pages,
            "crawl_termination_reason": self.crawl_termination_reason,
            "crawl_started_at": self.crawl_started_at,
            "crawl_finished_at": self.crawl_finished_at,
            "max_pages": self.max_pages,
            "max_depth": self.max_depth,
            "respect_robots": self.respect_robots,
            "check_images": self.check_images,
            "check_external_links": self.check_external_links,
            "crawler_user_agent": USER_AGENT,
            "audit_version": AUDIT_VERSION,
        }

    async def _supervise(self):
        """Ждёт, пока обход не завершится сам (pending==0), либо не сработает
        cancel_event/timeout/лимит страниц — тогда принудительно останавливаем воркеров.
        В любом случае фиксирует причину завершения в crawl_termination_reason."""
        completion_task = asyncio.create_task(self.completion_event.wait())
        try:
            while True:
                if self.completion_event.is_set():
                    self.crawl_termination_reason = "completed"
                    return
                if self.cancel_event.is_set():
                    self.crawl_termination_reason = "cancelled"
                    return
                if self._time_budget_exceeded():
                    self.crawl_termination_reason = "max_duration"
                    return
                async with self.lock:
                    if len(self.pages) >= self.max_pages:
                        self.crawl_termination_reason = "max_pages"
                        return
                try:
                    await asyncio.wait_for(asyncio.shield(completion_task), timeout=0.2)
                    self.crawl_termination_reason = "completed"
                    return
                except asyncio.TimeoutError:
                    continue
        finally:
            if not completion_task.done():
                completion_task.cancel()

    async def _enqueue(self, url: str, depth: int, session: Optional[aiohttp.ClientSession]):
        """Атомарно регистрирует URL как "в работе" (pending += 1) и кладёт в очередь.
        Вызывающая сторона гарантирует, что после этого страница будет обработана
        и учтена через _mark_done(), иначе pending никогда не дойдёт до 0."""
        norm = self._normalize(url)
        async with self.lock:
            if norm in self.visited:
                return
            if len(self.visited) >= self.max_pages * MAX_VISITED_MULTIPLIER:
                return  # защита от explosion URL / crawler traps
            self.visited.add(norm)
            self.pending += 1
        await self.queue.put((url, depth))

    async def _mark_done(self):
        async with self.lock:
            self.pending -= 1
            if self.pending <= 0:
                self.pending = 0
                self.completion_event.set()

    async def _worker(self, session: aiohttp.ClientSession):
        while True:
            if self.cancel_event.is_set():
                return
            try:
                url, depth = await asyncio.wait_for(self.queue.get(), timeout=0.5)
            except asyncio.TimeoutError:
                continue
            except asyncio.CancelledError:
                return

            try:
                async with self.lock:
                    over_limit = len(self.pages) >= self.max_pages
                if over_limit or self.cancel_event.is_set():
                    if over_limit:
                        self.pages_skipped_limit += 1
                    continue  # страница уже "посчитана" как visited, просто не обрабатываем её содержимое
                await self._process_page(session, url, depth)
                self.on_progress(len(self.pages), self.queue.qsize())
            except asyncio.CancelledError:
                await self._mark_done()
                return
            except Exception as exc:  # noqa: BLE001 — воркер не должен умирать из-за неожиданной ошибки
                logger.exception("Unexpected worker error while processing %s: %s", url, exc)
            finally:
                await self._mark_done()

    async def _process_page(self, session: aiohttp.ClientSession, url: str, depth: int):
        report = PageReport(url, depth)
        report.requested_url = url
        report.requested_scheme = urlparse(url).scheme
        started = time.monotonic()

        try:
            async with self.semaphore:
                async with session.get(url, allow_redirects=True) as resp:
                    report.response_time_ms = int((time.monotonic() - started) * 1000)
                    report.status_code = resp.status
                    report.redirect_count = len(resp.history)
                    report.final_url = str(resp.url)
                    report.final_scheme = resp.url.scheme
                    chain = [str(h.url) for h in resp.history] + [str(resp.url)]
                    report.redirect_chain = chain
                    report.redirect_statuses = [h.status for h in resp.history] + [resp.status]
                    if len(chain) != len(set(chain)):
                        report.is_redirect_loop = True
                        report.add_issue("redirect_loop", "Обнаружен цикл в цепочке редиректов")

                    content_type = resp.headers.get("Content-Type", "")
                    report.content_encoding = resp.headers.get("Content-Encoding")
                    report.cache_control = resp.headers.get("Cache-Control")
                    report.etag = resp.headers.get("ETag")
                    report.last_modified = resp.headers.get("Last-Modified")
                    x_robots = resp.headers.get("X-Robots-Tag", "")

                    body = await resp.read()
                    report.page_size_bytes = len(body)

                    if resp.status >= 400:
                        report.add_issue("broken_link", f"Страница вернула код {resp.status}")
                        self._finalize_page(report)
                        return

                    if report.final_scheme == "http":
                        if report.requested_scheme == "https":
                            report.add_issue("https_downgrade", "HTTPS-запрос был перенаправлен обратно на HTTP")
                        else:
                            report.add_issue("not_https", "Страница отдаётся по незащищённому протоколу HTTP и не редиректит на HTTPS")

                    if report.redirect_count > 1 and not report.is_redirect_loop:
                        report.add_issue("redirect_chain", f"Цепочка из {report.redirect_count} редиректов до финального URL: статусы {report.redirect_statuses}")

                    if report.response_time_ms and report.response_time_ms > SLOW_RESPONSE_MS:
                        report.add_issue("slow_response", f"Время ответа сервера: {report.response_time_ms} мс (эвристика по TTFB)")

                    if report.page_size_bytes and report.page_size_bytes > LARGE_PAGE_BYTES:
                        mb = report.page_size_bytes / (1024 * 1024)
                        report.add_issue("large_page_size", f"Вес страницы: {mb:.1f} МБ")

                    if content_type and "text/html" in content_type and not report.content_encoding:
                        report.add_issue("no_compression", "Ответ сервера не содержит Content-Encoding (gzip/br) — HTML не сжат", confidence="low")

                    if "text/html" not in content_type:
                        self._finalize_page(report)
                        return

                    if "noindex" in x_robots.lower():
                        report.has_x_robots_tag = True
                        report.x_robots_noindex = True
                        report.add_issue("noindex_header", f"X-Robots-Tag: {x_robots}")
                    elif x_robots:
                        report.has_x_robots_tag = True

                    html = body.decode(resp.get_encoding() or "utf-8", errors="ignore")
        except asyncio.TimeoutError:
            report.status_code = 0
            report.add_issue("timeout", "Превышено время ожидания ответа сервера")
            self._finalize_page(report)
            return
        except (ssl_module.SSLError, aiohttp.ClientConnectorCertificateError, aiohttp.ClientSSLError) as exc:
            report.status_code = 0
            report.ssl_error = True
            report.add_issue("ssl_error", f"Ошибка SSL-сертификата: {exc}")
            self._finalize_page(report)
            return
        except Exception as exc:  # noqa: BLE001 — одна страница не должна валить весь аудит
            report.status_code = 0
            report.add_issue("connection_error", f"Ошибка соединения: {exc}")
            self._finalize_page(report)
            return

        await self._analyze_html(report, html, session)
        self._finalize_page(report)

        if depth < self.max_depth:
            await self._enqueue_links(html, url, depth)

    def _finalize_page(self, report: PageReport):
        self.pages.append(report)
        self.reports_by_url[self._normalize(report.url)] = report

    # -- разбор HTML --------------------------------------------------------

    async def _analyze_html(self, report: PageReport, html: str, session: aiohttp.ClientSession):
        """Глубокий статический анализ HTML без выполнения JavaScript."""
        soup = BeautifulSoup(html, "lxml")
        html_tag = soup.find("html")
        report.language = html_tag.get("lang", "").strip() if html_tag else None
        if not report.language:
            report.add_issue("no_lang_attribute", "У тега <html> не указан атрибут lang")

        report.page_type = self._detect_page_type(report.url, soup, report.depth)
        is_utility_page = report.page_type in UTILITY_PAGE_TYPES

        # Title / description
        title_tag = soup.find("title")
        if title_tag and title_tag.get_text(strip=True):
            title = title_tag.get_text(" ", strip=True)
            report.title = title
            self.titles_seen[re.sub(r"\s+", " ", title).strip().casefold()].append(report.url)
            if len(title) < TITLE_MIN_LEN:
                report.add_issue("title_too_short", f"Title слишком короткий ({len(title)} симв., диапазон 50–60 — эвристика)")
            elif len(title) > TITLE_MAX_LEN:
                report.add_issue("title_too_long", f"Title слишком длинный ({len(title)} симв., диапазон 50–60 — эвристика)")
            if REPEATED_CHAR_RE.search(title):
                report.add_issue("repeated_char_title", "Title содержит подозрительный повтор одного символа")
        else:
            report.add_issue("no_title", "Отсутствует тег <title>")

        meta_desc = soup.find("meta", attrs={"name": re.compile(r"^description$", re.I)})
        if meta_desc and meta_desc.get("content", "").strip():
            desc = meta_desc["content"].strip()
            report.meta_description = desc
            self.descriptions_seen[re.sub(r"\s+", " ", desc).strip().casefold()].append(report.url)
            if len(desc) < DESC_MIN_LEN:
                report.add_issue("description_too_short", f"Meta description слишком короткая ({len(desc)} симв.)")
            elif len(desc) > DESC_MAX_LEN:
                report.add_issue("description_too_long", f"Meta description слишком длинная ({len(desc)} симв.)")
            if REPEATED_CHAR_RE.search(desc):
                report.add_issue("repeated_char_description", "Meta description содержит подозрительный повтор одного символа")
        else:
            report.add_issue("no_meta_description", "Отсутствует meta description")

        # Headings + hierarchy
        report.headings_present = {f"h{level}" for level in range(1, 7) if soup.find(f"h{level}")}
        h1_tags = soup.find_all("h1")
        report.h1_count = len(h1_tags)
        if not h1_tags:
            report.add_issue("no_h1", "Отсутствует тег <h1>")
        elif len(h1_tags) > 1:
            report.add_issue("multiple_h1", f"Найдено несколько тегов <h1> ({len(h1_tags)})")
        if h1_tags and not any(h.get_text(strip=True) for h in h1_tags):
            report.add_issue("empty_h1", "Тег <h1> присутствует, но не содержит текста")
        if h1_tags:
            longest_h1 = max((h.get_text(" ", strip=True) for h in h1_tags), key=len, default="")
            if len(longest_h1) > 120:
                report.add_issue("h1_too_long", f"H1 очень длинный ({len(longest_h1)} симв.)", confidence="low")
        h1_texts = [re.sub(r"\s+", " ", x.get_text(" ", strip=True)).casefold() for x in h1_tags]
        report.duplicate_h1_text = len(h1_texts) > 1 and len(set(h1_texts)) < len(h1_texts)
        empty_lower_headings = [
            h for level in range(2, 7) for h in soup.find_all(f"h{level}") if not h.get_text(strip=True)
        ]
        if empty_lower_headings:
            report.add_issue("empty_heading", f"Найдено {len(empty_lower_headings)} пустых заголовков H2–H6")
        self._check_heading_hierarchy(report, soup)

        # Images
        images = soup.find_all("img")
        report.images_total = len(images)
        for idx, img in enumerate(images):
            alt = img.get("alt")
            is_decorative = (alt == "") and (img.get("role") == "presentation" or img.get("aria-hidden") == "true")
            src_val = (img.get("src") or "").strip()
            if src_val.lower().endswith(".svg") and alt is None:
                is_decorative = is_decorative or bool(img.get("aria-hidden") == "true")
            if alt is None:
                report.images_alt_missing += 1
            elif alt.strip() == "" and not is_decorative:
                report.images_alt_missing += 1
            elif alt.strip() == "" and is_decorative:
                report.images_decorative += 1
                report.images_alt_empty_decorative += 1
            if not img.get("width") or not img.get("height"):
                report.images_missing_dimensions += 1
            loading = (img.get("loading") or "").lower()
            fetchpriority = (img.get("fetchpriority") or "").lower()
            is_hero = idx < HERO_IMAGE_COUNT or fetchpriority == "high" or loading == "eager"
            if loading != "lazy" and not is_hero:
                report.images_not_lazy += 1
        report.images_alt_empty = report.images_alt_missing  # это поле хранит именно "пустой/отсутствующий не-декоративный alt"
        report.images_without_alt = report.images_alt_missing  # обратная совместимость со старым полем/семантикой
        if report.images_without_alt:
            report.add_issue("images_without_alt", f"{report.images_without_alt} из {report.images_total} изображений без информативного alt")
        if report.images_missing_dimensions >= 2:
            report.add_issue("images_missing_dimensions", f"{report.images_missing_dimensions} изображений без width/height")
        if report.images_total >= 5 and report.images_not_lazy >= max(3, (report.images_total - HERO_IMAGE_COUNT) // 2):
            report.add_issue("images_not_lazy", f"{report.images_not_lazy} некритичных изображений без loading=lazy")
        if self.check_images:
            await self._check_broken_images(report, images, session)

        # Canonical — полноценный аудит
        self._analyze_canonical(report, soup)

        # Robots meta
        robots_tag = soup.find("meta", attrs={"name": re.compile(r"^robots$", re.I)})
        report.has_meta_robots = bool(robots_tag)
        if robots_tag and "noindex" in robots_tag.get("content", "").lower():
            report.robots_noindex = True
            report.add_issue("noindex", "Страница закрыта от индексации (noindex)")

        # Viewport / favicon
        viewport = soup.find("meta", attrs={"name": re.compile(r"^viewport$", re.I)})
        report.has_viewport = bool(viewport)
        if not report.has_viewport:
            report.add_issue("no_viewport", "Отсутствует meta viewport")
        else:
            viewport_content = (viewport.get("content") or "").lower().replace(" ", "")
            if "width=device-width" not in viewport_content:
                report.add_issue("viewport_not_responsive", f"Viewport не содержит width=device-width: {viewport.get('content')}")
            if re.search(r"user-scalable=no", viewport_content) or re.search(r"maximum-scale=1(\.0)?(?!\d)", viewport_content):
                report.add_issue("viewport_zoom_disabled", f"Viewport ограничивает масштабирование: {viewport.get('content')}")

        if not self.homepage_checked_favicon:
            self.homepage_checked_favicon = True
            favicon_link = soup.find("link", attrs={"rel": re.compile(r"(^|\s)icon(\s|$)", re.I)})
            self.has_favicon = bool(favicon_link)
            if not self.has_favicon:
                report.add_issue("no_favicon", "Не найден favicon")

        # Open Graph
        og_tags = soup.find_all("meta", attrs={"property": re.compile(r"^og:", re.I)})
        report.has_open_graph = bool(og_tags)
        if not report.has_open_graph:
            report.add_issue("no_open_graph", "Отсутствуют Open Graph теги")

        # Resource hints / render-blocking signals
        report.has_preload = bool(soup.find("link", attrs={"rel": re.compile(r"(^|\s)preload(\s|$)", re.I)}))
        report.has_preconnect = bool(soup.find("link", attrs={"rel": re.compile(r"(^|\s)preconnect(\s|$)", re.I)}))
        report.has_dns_prefetch = bool(soup.find("link", attrs={"rel": re.compile(r"(^|\s)dns-prefetch(\s|$)", re.I)}))
        report.scripts_count = len(soup.find_all("script", src=True))
        report.stylesheets_count = len(soup.find_all("link", attrs={"rel": re.compile(r"(^|\s)stylesheet(\s|$)", re.I)}))
        report.inline_css_bytes = sum(len((t.string or "").encode("utf-8")) for t in soup.find_all("style"))
        report.inline_js_bytes = sum(len((t.string or "").encode("utf-8")) for t in soup.find_all("script") if not t.get("src"))

        third_party = set()
        for tag, attr in ((soup.find_all("script", src=True), "src"), (soup.find_all("link", attrs={"rel": re.compile(r"(^|\s)stylesheet(\s|$)", re.I)}), "href")):
            for t in tag:
                val = (t.get(attr) or "").strip()
                if not val:
                    continue
                absolute = urljoin(report.url, val)
                netloc = urlparse(absolute).netloc
                if netloc and netloc != self.domain:
                    third_party.add(netloc)
        report.third_party_domains = sorted(third_party)

        # Hreflang — собираем для последующего cross-page анализа
        self._analyze_hreflang(report, soup)

        # Pagination
        rel_next = soup.find("link", attrs={"rel": re.compile(r"(^|\s)next(\s|$)", re.I)})
        rel_prev = soup.find("link", attrs={"rel": re.compile(r"(^|\s)prev(\s|$)", re.I)})
        report.pagination_rel_next = rel_next.get("href") if rel_next else None
        report.pagination_rel_prev = rel_prev.get("href") if rel_prev else None
        report.is_paginated = bool(
            rel_next or rel_prev
            or PAGINATION_QUERY_RE.search(report.url)
            or PAGINATION_PATH_RE.search(urlparse(report.url).path)
        )

        # Structured data (JSON-LD, безопасный extractor) + Microdata/RDFa presence
        ld_scripts = soup.find_all("script", attrs={"type": re.compile(r"application/ld\+json", re.I)})
        schema_types: list = []
        schema_errors = 0
        jsonld_nodes: list = []
        for script in ld_scripts:
            raw = script.string or script.get_text() or ""
            if not raw.strip():
                continue
            try:
                data = json.loads(raw)
            except (json.JSONDecodeError, TypeError, ValueError):
                schema_errors += 1
                continue
            nodes = _safe_extract_jsonld_nodes(data)
            jsonld_nodes.extend(nodes)
            for node in nodes:
                types = _jsonld_node_types(node)
                if not types:
                    report.add_issue("schema_missing_type", "JSON-LD объект без @type")
                schema_types.extend(types)
        report.schema_errors = schema_errors
        report.schema_types = sorted(set(schema_types))
        report.structured_data_types = report.schema_types
        report.schema_semantically_complete = _jsonld_semantically_complete(jsonld_nodes)
        has_other_schema = bool(soup.find(attrs={"itemscope": True}) or soup.find(attrs={"typeof": True}))
        if not report.schema_types and not has_other_schema:
            report.add_issue("no_structured_data", "Не найдена структурированная разметка Schema.org")
        if schema_errors:
            report.add_issue("schema_invalid_json", f"{schema_errors} JSON-LD блок(ов) не удалось разобрать (синтаксически невалидны)")

        # Text and content signals
        analysis_soup = BeautifulSoup(html, "lxml")
        for tag in analysis_soup(["script", "style", "noscript", "template", "svg"]):
            tag.decompose()
        text = analysis_soup.get_text(separator=" ", strip=True)
        words = re.findall(r"\b[\wÀ-ÿА-Яа-яЁёӘәӨөҮүҚқҒғҢңҺһІі]+\b", text, flags=re.UNICODE)
        report.word_count = min(len(words), MAX_TEXT_WORDS_FOR_ANALYSIS)
        if report.word_count < THIN_CONTENT_WORDS and not is_utility_page and not report.is_paginated:
            report.add_issue("thin_content", f"Только {report.word_count} слов текста на странице (эвристика, зависит от типа страницы)")
        html_len = max(len(html.encode("utf-8", errors="ignore")), 1)
        text_len = len(text.encode("utf-8", errors="ignore"))
        report.text_html_ratio = round(text_len / html_len, 3)
        if html_len > 100_000 and report.text_html_ratio < 0.03:
            report.add_issue("low_text_html_ratio", f"Доля видимого текста в HTML: {report.text_html_ratio:.1%}")

        # Soft 404 (несколько независимых сигналов, с учётом page_type)
        self._detect_soft_404(report, text, is_utility_page)

        # Author/date — реальный парсинг полей, а не поиск подстроки
        report.has_author = bool(
            any(_jsonld_has_author(n) for n in jsonld_nodes)
            or soup.find(attrs={"rel": re.compile(r"author", re.I)})
            or soup.find(attrs={"itemprop": re.compile(r"^author$", re.I)})
            or soup.find("meta", attrs={"name": re.compile(r"^author$", re.I)})
        )
        report.has_date_published = bool(
            any(bool(n.get("datePublished")) for n in jsonld_nodes)
            or soup.find(attrs={"itemprop": re.compile(r"^datePublished$", re.I)})
            or soup.find("time", attrs={"datetime": True})
        )
        report.has_date_modified = bool(
            any(bool(n.get("dateModified")) for n in jsonld_nodes)
            or soup.find(attrs={"itemprop": re.compile(r"^dateModified$", re.I)})
        )
        is_article_like = report.page_type in ("article", "blog") or bool(ARTICLE_SCHEMA_TYPES.intersection(report.schema_types))
        if is_article_like:
            if not report.has_author:
                report.add_issue("no_author_signal", "Для статейной страницы не найден явный author")
            if not report.has_date_published:
                report.add_issue("missing_publish_date", "Для статейной страницы не найдена datePublished")

        # Mixed content + HTTP internal links on HTTPS
        if report.final_scheme == "https" or report.url.startswith("https://"):
            mixed = 0
            for tags, attr in ((soup.find_all("img"), "src"), (soup.find_all("script"), "src"), (soup.find_all("link"), "href")):
                for tag in tags:
                    val = (tag.get(attr) or "").strip()
                    if val.startswith("http://"):
                        mixed += 1
            if mixed:
                report.add_issue("mixed_content", f"{mixed} ресурсов загружаются по HTTP")
            http_internal_links = 0
            for a in soup.find_all("a", href=True):
                href = a["href"].strip()
                if href.startswith("http://") and self._is_same_domain(urljoin(report.url, href)):
                    http_internal_links += 1
            if http_internal_links:
                report.add_issue("http_internal_links", f"{http_internal_links} внутренних ссылок ведут на HTTP-версию")

        # Links: internal/external + rel-атрибуты
        external_link_urls: list = []
        for a in soup.find_all("a", href=True):
            href = a["href"].strip()
            if not href or not self._is_crawlable_href(href):
                continue
            absolute = urljoin(report.url, href)
            rel = {x.lower() for x in (a.get("rel") or [])}
            is_empty_link = not a.get_text(strip=True) and not a.get("aria-label") and not a.get("aria-labelledby") and not a.find("img")
            if is_empty_link:
                report.add_issue("empty_link", f"Ссылка без текста/aria-label: {absolute}", confidence="medium")
            if "nofollow" in rel:
                report.nofollow_links += 1
                if self._is_same_domain(absolute):
                    report.add_issue("nofollow_internal", "Внутренняя ссылка имеет rel=nofollow")
            if "sponsored" in rel:
                report.sponsored_links += 1
            if "ugc" in rel:
                report.ugc_links += 1
            if self._is_same_domain(absolute):
                report.internal_links += 1
                target_norm = self._normalize(absolute)
                self.incoming_link_sources[target_norm].add(self._normalize(report.url))
            else:
                report.external_links += 1
                external_link_urls.append(absolute)

        if self.check_external_links and external_link_urls:
            await self._check_broken_external_links(report, external_link_urls, session)

        # URL audit
        self._analyze_url(report)

        # Basic form accessibility
        for form in soup.find_all("form"):
            for control in form.find_all(["input", "select", "textarea"]):
                if control.get("type", "").lower() in {"hidden", "submit", "button", "reset"}:
                    continue
                cid = control.get("id")
                has_label = bool(cid and soup.find("label", attrs={"for": cid})) or bool(control.find_parent("label"))
                if not has_label and not control.get("aria-label") and not control.get("aria-labelledby"):
                    report.forms_without_labels += 1
        if report.forms_without_labels:
            report.add_issue("form_without_label", f"{report.forms_without_labels} полей формы без доступного label")

        # Lightweight static accessibility checks
        ids_seen = [el.get("id") for el in soup.find_all(attrs={"id": True})]
        dup_ids = {i for i in ids_seen if ids_seen.count(i) > 1}
        if dup_ids:
            report.add_issue("duplicate_element_ids", f"Повторяющиеся id: {', '.join(sorted(dup_ids)[:5])}")
        for iframe in soup.find_all("iframe"):
            if not (iframe.get("title") or "").strip():
                report.add_issue("iframe_missing_title", "У <iframe> отсутствует атрибут title", confidence="medium")
                break

    def _check_heading_hierarchy(self, report: PageReport, soup: BeautifulSoup):
        levels = []
        for tag in soup.find_all(re.compile(r"^h[1-6]$")):
            try:
                levels.append(int(tag.name[1]))
            except (IndexError, ValueError):
                continue
        prev = None
        for level in levels:
            if prev is not None and level - prev > 1:
                report.add_issue("heading_hierarchy_skip", f"Пропуск уровня заголовков: H{prev} -> H{level}")
                break  # одного упоминания достаточно, чтобы не заспамить issue-список
            prev = level

    def _analyze_canonical(self, report: PageReport, soup: BeautifulSoup):
        canonical_tags = soup.find_all("link", attrs={"rel": re.compile(r"(^|\s)canonical(\s|$)", re.I)})
        report.canonical_count = len(canonical_tags)
        if not canonical_tags:
            report.add_issue("no_canonical", 'Отсутствует тег <link rel="canonical">')
            return
        if len(canonical_tags) > 1:
            report.add_issue("canonical_multiple", f"Найдено {len(canonical_tags)} тегов canonical на странице")

        canonical = canonical_tags[0]
        href = (canonical.get("href") or "").strip()
        if not href:
            report.add_issue("canonical_malformed", "У тега canonical отсутствует href")
            return

        report.has_canonical = True
        absolute = urljoin(report.url, href)
        parsed = urlparse(absolute)
        if not parsed.scheme or not parsed.netloc:
            report.add_issue("canonical_malformed", f"Canonical href не является валидным URL: {href}")
            return

        report.canonical_url = absolute
        report.canonical_relative = not href.lower().startswith(("http://", "https://"))
        if parsed.fragment:
            report.canonical_has_fragment = True
            report.add_issue("canonical_fragment", f"Canonical содержит #fragment: {absolute}")

        if parsed.netloc != self.domain:
            report.add_issue("canonical_other_domain", f"Canonical указывает на другой домен: {absolute}")
            return

        if report.final_scheme == "https" and parsed.scheme == "http":
            report.add_issue("canonical_http_on_https", f"HTTPS-страница ссылается через canonical на HTTP-версию: {absolute}")

        current_norm = self._normalize(report.final_url or report.url)
        canonical_norm = self._normalize(absolute)
        current_path_q = urlsplit(current_norm)
        canonical_path_q = urlsplit(canonical_norm)

        report.canonical_is_self = current_norm == canonical_norm
        if report.canonical_is_self:
            return

        if current_path_q.path.rstrip("/") == canonical_path_q.path.rstrip("/") and current_path_q.query != canonical_path_q.query:
            current_params = {k for k, _ in parse_qsl(current_path_q.query)}
            extra_params = current_params - {k for k, _ in parse_qsl(canonical_path_q.query)}
            if extra_params and extra_params.issubset(TRACKING_PARAMS | BENIGN_QUERY_PARAMS):
                report.add_issue("canonical_query_mismatch", f"Canonical отличается только query-параметрами: {absolute}")
            else:
                report.add_issue("canonical_mismatch", f"Canonical отличается от текущего URL: {absolute}")
        else:
            report.add_issue("canonical_mismatch", f"Canonical отличается от текущего URL: {absolute}")

    def _analyze_canonical_targets(self):
        """Пост-обход проверка: куда реально ведёт canonical (для целей, которые
        были обойдены в рамках этого же аудита). Если целевая страница не была
        обойдена, статус не утверждается — мы не можем его подтвердить."""
        for report in self.pages:
            if not report.canonical_url or report.canonical_is_self:
                continue
            canon_norm = self._normalize(report.canonical_url)
            target = self.reports_by_url.get(canon_norm)
            if target is None:
                continue
            report.canonical_target_status = target.status_code
            report.canonical_target_noindex = bool(target.robots_noindex or target.x_robots_noindex)
            report.canonical_target_is_redirect = target.redirect_count > 0
            if target.status_code and target.status_code >= 400:
                report.add_issue("canonical_to_error", f"Canonical ведёт на {report.canonical_url}, который вернул {target.status_code}")
            if report.canonical_target_is_redirect:
                report.add_issue("canonical_to_redirect", f"Canonical ведёт на редиректящий URL: {report.canonical_url}")
            if report.canonical_target_noindex:
                report.add_issue("canonical_to_noindex", f"Canonical ведёт на noindex-страницу: {report.canonical_url}")
            if target.canonical_url and not target.canonical_is_self:
                report.canonical_chain_length = 2
                report.add_issue(
                    "canonical_chain",
                    f"Canonical указывает на {report.canonical_url}, у которого canonical, в свою очередь, ведёт на другой URL",
                    confidence="medium",
                )

    def _analyze_hreflang(self, report: PageReport, soup: BeautifulSoup):
        hreflangs = soup.find_all("link", attrs={"rel": re.compile(r"(^|\s)alternate(\s|$)", re.I), "hreflang": True})
        report.hreflang_count = len(hreflangs)
        entries = []
        seen_langs: dict = {}
        for link in hreflangs:
            lang = (link.get("hreflang") or "").strip().lower()
            href = (link.get("href") or "").strip()
            valid_lang = bool(HREFLANG_LANG_RE.fullmatch(lang) or lang == "x-default")
            absolute = urljoin(report.url, href) if href else ""
            valid_url = bool(absolute) and bool(urlparse(absolute).scheme)
            if not valid_lang or not valid_url:
                report.add_issue("hreflang_invalid", f"Некорректный hreflang: {lang} -> {href}")
                continue
            if absolute.startswith("http://") and (report.final_scheme == "https" or report.url.startswith("https://")):
                report.add_issue("http_hreflang_url", f"hreflang ссылается на HTTP: {absolute}", confidence="low")
            if lang in seen_langs and seen_langs[lang] != absolute:
                report.add_issue("hreflang_duplicate_lang", f"Дублирующийся hreflang для '{lang}'")
            seen_langs[lang] = absolute
            entries.append({"lang": lang, "href": absolute})
        report.hreflang_entries = entries
        if entries:
            self.hreflang_registry[self._normalize(report.url)] = entries

    def _detect_soft_404(self, report: PageReport, visible_text: str, is_utility_page: bool):
        if report.status_code != 200:
            return
        signals = 0
        title_text = report.title or ""
        if SOFT_404_TITLE_MARKERS.search(title_text):
            signals += 1
        if SOFT_404_BODY_MARKERS.search(visible_text[:1000]):
            signals += 1
        has_main_content_block = bool(report.headings_present) or (report.word_count or 0) >= SOFT_404_MIN_WORDS
        if not is_utility_page and not has_main_content_block and (report.word_count or 0) < SOFT_404_MIN_WORDS:
            signals += 1
        # Utility-страницы (login/contact/search/checkout и т.д.) часто короткие
        # и без H1-контента совершенно легитимно — не засчитываем этот сигнал им.
        if signals >= 2:
            report.soft_404 = True
            report.add_issue(
                "soft_404",
                "Страница вернула 200 OK, но контент похож на страницу ошибки (совпало несколько независимых признаков)",
                confidence="medium",
            )

    def _analyze_url(self, report: PageReport):
        parsed = urlparse(report.url)
        if parsed.query:
            params_list = parse_qsl(parsed.query, keep_blank_values=True)
            params = {k for k, _ in params_list}
            non_benign = params - BENIGN_QUERY_PARAMS - TRACKING_PARAMS
            if non_benign or len(params) > 3:
                report.add_issue("query_parameter_url", f"URL содержит query-параметры: {parsed.query}")
            keys_list = [k for k, _ in params_list]
            if len(keys_list) != len(set(keys_list)):
                report.add_issue("url_repeated_query_param", f"URL содержит повторяющиеся query-параметры: {parsed.query}")
            if any(v == "" for _, v in params_list):
                report.add_issue("url_empty_query_param", f"URL содержит query-параметр без значения: {parsed.query}")
        if ";" in parsed.path:
            report.add_issue("url_semicolon_param", "URL содержит устаревшие matrix-параметры (;key=value)", confidence="low")
        if "%20" in report.url or "+" in parsed.path:
            report.add_issue("url_contains_space", "URL содержит закодированный пробел")
        if re.search(r"%[0-9A-Fa-f]{2}", parsed.path) and "%20" not in report.url:
            report.add_issue("url_encoded_chars", "URL содержит percent-encoded символы в пути", confidence="low")
        if len(report.url) > 115:
            report.add_issue("url_too_long", f"Длина URL: {len(report.url)} символов")
        if any(c.isupper() for c in parsed.path):
            report.add_issue("url_uppercase", "URL содержит заглавные буквы в пути")
        if "//" in parsed.path:
            report.add_issue("url_multiple_slashes", "URL содержит повторяющиеся слеши в пути")

    async def _check_broken_images(self, report: PageReport, images, session: aiohttp.ClientSession):
        """Проверка: действительно ли изображения загружаются (HEAD, с fallback на GET)."""
        checked = 0
        broken = 0
        for img in images:
            if checked >= MAX_IMAGES_CHECKED_PER_PAGE:
                break
            src = img.get("src")
            if not src:
                continue
            absolute = urljoin(report.url, src)
            checked += 1
            try:
                async with self.semaphore:
                    async with session.head(absolute, timeout=aiohttp.ClientTimeout(total=5), allow_redirects=True) as r:
                        status = r.status
                    if status in (405, 501):  # сервер не поддерживает HEAD — пробуем GET
                        async with session.get(absolute, timeout=aiohttp.ClientTimeout(total=5), allow_redirects=True) as r2:
                            status = r2.status
                    if status >= 400:
                        broken += 1
            except Exception:  # noqa: BLE001
                broken += 1
        report.images_broken = broken
        if broken > 0:
            report.add_issue("broken_image", f"{broken} из {checked} проверенных изображений не загружаются")

    async def _check_broken_external_links(self, report: PageReport, external_urls: list, session: aiohttp.ClientSession):
        """Проверяет ограниченное число внешних ссылок (реально использует лимит).
        Таймаут внешнего ресурса не приравнивается автоматически к "битой" ссылке —
        это отдельный, менее уверенный сигнал (внешний сайт мог быть временно
        перегружен)."""
        checked = 0
        broken = 0
        timed_out = 0
        for url in external_urls:
            if checked >= MAX_EXTERNAL_LINKS_CHECKED_PER_PAGE:
                break
            checked += 1
            try:
                async with self.semaphore:
                    async with session.head(url, timeout=aiohttp.ClientTimeout(total=5), allow_redirects=True) as r:
                        status = r.status
                    if status in (405, 501):
                        async with session.get(url, timeout=aiohttp.ClientTimeout(total=5), allow_redirects=True) as r2:
                            status = r2.status
                    if status >= 400:
                        broken += 1
            except asyncio.TimeoutError:
                timed_out += 1
            except Exception:  # noqa: BLE001
                broken += 1
        report.external_links_checked = checked
        report.external_timeouts = timed_out
        if broken > 0:
            report.add_issue("broken_external_link", f"{broken} из {checked} проверенных внешних ссылок недоступны")
        if timed_out > 0:
            report.add_issue("external_timeout", f"{timed_out} из {checked} проверенных внешних ссылок не ответили за отведённое время", confidence="low")

    async def _enqueue_links(self, html: str, base_url: str, depth: int):
        soup = BeautifulSoup(html, "lxml")
        for a in soup.find_all("a", href=True):
            href = a["href"].strip()
            if not href or not self._is_crawlable_href(href):
                continue

            absolute = self._normalize(urljoin(base_url, href))
            parsed = urlparse(absolute)
            if not self._is_same_domain(absolute):
                continue

            # Защита от crawler traps (faceted-навигация, календари): ограничиваем
            # количество разных query-вариантов одного и того же path.
            if parsed.query:
                variants = self._query_variants_per_path[parsed.path]
                if parsed.query not in variants:
                    if len(variants) >= MAX_QUERY_VARIANTS_PER_PATH:
                        continue
                    variants.add(parsed.query)

            if self.respect_robots and not self.robots.can_fetch(absolute):
                async with self.lock:
                    if absolute not in self.visited:
                        self.visited.add(absolute)
                        self.blocked_urls.append(absolute)
                continue

            async with self.lock:
                if len(self.pages) >= self.max_pages:
                    continue

            await self._enqueue(absolute, depth + 1, session=None)

    def _detect_duplicates(self):
        for title, urls in self.titles_seen.items():
            if len(urls) > 1:
                for report in self.pages:
                    if report.title and re.sub(r"\s+", " ", report.title).strip().casefold() == title:
                        report.add_issue("duplicate_title", f"Title дублируется на {len(urls)} страницах сайта")

        for desc, urls in self.descriptions_seen.items():
            if len(urls) > 1:
                for report in self.pages:
                    if report.meta_description and re.sub(r"\s+", " ", report.meta_description).strip().casefold() == desc:
                        report.add_issue("duplicate_description", f"Meta description дублируется на {len(urls)} страницах сайта")

    def _detect_near_duplicate_titles(self):
        """Сравнение near-duplicate title через difflib. O(n^2), поэтому
        ограничено NEAR_DUPLICATE_TITLE_MAX_PAGES — на больших сайтах эта
        проверка пропускается, чтобы не замедлять построение отчёта."""
        titled_pages = [p for p in self.pages if p.title]
        if len(titled_pages) < 2 or len(titled_pages) > NEAR_DUPLICATE_TITLE_MAX_PAGES:
            return
        already_flagged = set()
        for i in range(len(titled_pages)):
            for j in range(i + 1, len(titled_pages)):
                a, b = titled_pages[i], titled_pages[j]
                if (a.url, b.url) in already_flagged:
                    continue
                norm_a = re.sub(r"\s+", " ", a.title).strip().casefold()
                norm_b = re.sub(r"\s+", " ", b.title).strip().casefold()
                if norm_a == norm_b:
                    continue  # это уже duplicate_title, не дублируем сигнал
                ratio = difflib.SequenceMatcher(None, norm_a, norm_b).ratio()
                if ratio >= NEAR_DUPLICATE_TITLE_RATIO:
                    a.add_issue("similar_title", f"Title почти совпадает с {b.url}", confidence="medium")
                    b.add_issue("similar_title", f"Title почти совпадает с {a.url}", confidence="medium")
                    already_flagged.add((a.url, b.url))

    def _compute_orphan_pages(self) -> list:
        if not self.sitemap.urls:
            return []
        visited_normalized = {u.rstrip("/") for u in self.visited}
        orphans = [u for u in self.sitemap.urls if u.rstrip("/") not in visited_normalized]
        return orphans[:50]  # ограничиваем вывод

    def _analyze_hreflang_relationships(self):
        """Post-crawl проверка взаимности hreflang-ссылок, self-reference и
        статуса целевых страниц (только для внутренних целей — для внешних
        доменов проверка статуса не делается, так как мы их не обходили)."""
        for source_url, entries in self.hreflang_registry.items():
            source_report = self.reports_by_url.get(source_url)
            if source_report is None:
                continue
            self_present = any(self._normalize(e["href"]) == source_url for e in entries)
            source_report.hreflang_self_present = self_present
            if not self_present:
                source_report.add_issue("hreflang_self_missing", "Страница не ссылается сама на себя в собственном наборе hreflang", confidence="medium")
            for entry in entries:
                target_norm = self._normalize(entry["href"])
                if not self._is_same_domain(entry["href"]):
                    continue
                target_report = self.reports_by_url.get(target_norm)
                if target_report is None:
                    continue  # целевая страница не была обойдена — не можем проверить статус/взаимность
                if target_report.status_code and target_report.status_code >= 400:
                    source_report.add_issue("hreflang_to_error", f"hreflang -> {entry['href']} вернул {target_report.status_code}")
                if target_report.robots_noindex or target_report.x_robots_noindex:
                    source_report.add_issue("hreflang_to_noindex", f"hreflang -> {entry['href']} закрыт noindex")
                target_entries = self.hreflang_registry.get(target_norm, [])
                has_return_link = any(self._normalize(te["href"]) == source_url for te in target_entries)
                if not has_return_link:
                    source_report.add_issue("hreflang_missing_return", f"Нет взаимной hreflang-ссылки на странице {entry['href']}")

    def _compute_incoming_links(self):
        """Строит граф внутренних входящих ссылок и находит orphan / слабо
        связанные страницы. Homepage исключается из orphan-проверки — на
        неё по определению ведут внешние источники (переходы напрямую)."""
        for report in self.pages:
            norm = self._normalize(report.url)
            report.incoming_internal_links = len(self.incoming_link_sources.get(norm, set()))
            if report.page_type == "homepage" or report.depth == 0:
                continue
            if report.incoming_internal_links == 0:
                report.add_issue("no_incoming_internal_links", "На эту страницу не ведёт ни одна внутренняя ссылка, найденная при обходе (orphan page)", confidence="medium")
            elif report.incoming_internal_links < WEAK_INTERNAL_LINKS_THRESHOLD:
                report.add_issue("weakly_linked_page", f"Только {report.incoming_internal_links} внутренняя(-ых) ссылка(-и) ведёт на эту страницу", confidence="low")

    def _detect_url_variants(self):
        """Группирует страницы по нормализованному (без учёта регистра пути)
        сигнатуре URL и помечает URL, которые отличаются только регистром или
        служебными слешами, как потенциальные дубли одного и того же ресурса."""
        buckets: dict = defaultdict(list)
        for report in self.pages:
            parsed = urlparse(report.url)
            signature = f"{parsed.scheme}://{parsed.netloc.lower()}{parsed.path.lower().rstrip('/')}?{parsed.query}"
            buckets[signature].append(report)
        for signature, reports in buckets.items():
            if len(reports) < 2:
                continue
            urls_in_group = sorted({r.url for r in reports})
            if len(urls_in_group) < 2:
                continue
            group_label = urls_in_group[0]
            for r in reports:
                r.duplicate_url_variant_group = group_label
                r.add_issue("duplicate_url_variant", f"Похожий URL-вариант этой же страницы также встречен как: {', '.join(u for u in urls_in_group if u != r.url)}", confidence="medium")

    def _compute_indexability_flags(self):
        """Определяет is_indexable и indexability_reasons для каждой
        страницы на основе реальных сигналов (без создания новых issues —
        это информационная сводка, а не сама по себе проблема)."""
        blocked_set = {u.rstrip("/") for u in self.blocked_urls}
        for report in self.pages:
            reasons = []
            url_norm = report.url.rstrip("/")
            if url_norm in blocked_set:
                reasons.append("robots_blocked")
            if report.status_code == 0:
                reasons.append("fetch_error")
            elif report.status_code and report.status_code >= 400:
                reasons.append(f"http_{report.status_code}")
            if report.robots_noindex:
                reasons.append("meta_noindex")
            if report.x_robots_noindex:
                reasons.append("x_robots_noindex")
            if report.redirect_count > 0:
                reasons.append("redirect")
            if report.soft_404:
                reasons.append("soft_404")
            report.indexability_reasons = reasons
            report.is_indexable = bool(report.status_code == 200 and not reasons)

    def _analyze_sitemap_consistency(self) -> list:
        """Сверяет sitemap.xml с реальными результатами обхода: находит URL
        из sitemap, которые возвращают ошибку, редиректят, закрыты noindex,
        заблокированы robots.txt или не совпадают со своим canonical."""
        if not self.sitemap.urls:
            return []
        blocked_set = {u.rstrip("/") for u in self.blocked_urls}
        problems = []
        for sitemap_url in self.sitemap.urls:
            norm = self._normalize(sitemap_url)
            report = self.reports_by_url.get(norm)
            url_rstrip = sitemap_url.rstrip("/")
            if url_rstrip in blocked_set:
                problems.append({"url": sitemap_url, "type": "sitemap_url_blocked"})
                continue
            if report is None:
                continue  # страница не была обойдена в рамках этого аудита — не можем подтвердить проблему
            if report.status_code and report.status_code >= 400:
                problems.append({"url": sitemap_url, "type": "sitemap_url_error"})
                report.add_issue("sitemap_url_error", f"URL присутствует в sitemap.xml, но вернул {report.status_code}")
                continue
            if report.redirect_count > 0:
                problems.append({"url": sitemap_url, "type": "sitemap_url_redirect"})
                report.add_issue("sitemap_url_redirect", "URL присутствует в sitemap.xml, но редиректит на другой адрес")
            if report.robots_noindex or report.x_robots_noindex:
                problems.append({"url": sitemap_url, "type": "sitemap_url_noindex"})
                report.add_issue("sitemap_url_noindex", "URL присутствует в sitemap.xml, но закрыт от индексации (noindex)")
            if report.canonical_url and not report.canonical_is_self:
                canon_norm = report.canonical_url.rstrip("/")
                if canon_norm != url_rstrip:
                    problems.append({"url": sitemap_url, "type": "sitemap_canonical_mismatch"})
                    report.add_issue("sitemap_canonical_mismatch", f"URL в sitemap.xml, но canonical указывает на другой URL: {report.canonical_url}", confidence="medium")
        return problems[:200]


# --------------------------------------------------------------------------
# Indexability matrix (сводная таблица для отчёта)
# --------------------------------------------------------------------------

def compute_indexability(pages: list, blocked_urls: list, sitemap_urls) -> dict:
    """Строит сводную indexability-матрицу и находит конфликты между
    sitemap/canonical/robots/status-code сигналами для итогового отчёта.

    Начиная с v3.1 использует уже вычисленные на этапе обхода
    `p.is_indexable` / `p.indexability_reasons` (см.
    SiteCrawler._compute_indexability_flags) вместо повторного, отдельного
    и потенциально расходящегося расчёта — единственный источник истины
    один. `sitemap_urls` — реальный список URL из sitemap.xml (раньше сюда
    ошибочно передавался пустой set)."""
    blocked_set = {u.rstrip("/") for u in blocked_urls}
    sitemap_set = {u.rstrip("/") for u in (sitemap_urls or [])}
    per_page = []
    conflicts = []

    for p in pages:
        url_norm = p.url.rstrip("/")
        is_blocked = url_norm in blocked_set
        is_error = bool(p.status_code and p.status_code >= 400)
        is_redirect = p.redirect_count > 0
        indexable = p.is_indexable if p.is_indexable is not None else bool(
            p.status_code == 200 and not p.robots_noindex and not p.x_robots_noindex and not is_blocked
        )
        reasons = p.indexability_reasons or []
        in_sitemap = url_norm in sitemap_set
        entry = {
            "url": p.url,
            "indexable": bool(indexable),
            "reasons": reasons,
            "noindex": p.robots_noindex,
            "x_robots_noindex": p.x_robots_noindex,
            "robots_blocked": is_blocked,
            "status": p.status_code,
            "redirect": is_redirect,
            "soft_404": p.soft_404,
            "in_sitemap": in_sitemap,
            "canonical_is_self": p.canonical_is_self,
            "canonical_url": p.canonical_url,
        }
        per_page.append(entry)

        if in_sitemap and (p.robots_noindex or p.x_robots_noindex):
            conflicts.append({"url": p.url, "type": "sitemap_noindex", "message": "URL есть в sitemap, но закрыт noindex"})
        if in_sitemap and is_error:
            conflicts.append({"url": p.url, "type": "sitemap_error", "message": f"URL есть в sitemap, но вернул {p.status_code}"})
        if in_sitemap and is_redirect:
            conflicts.append({"url": p.url, "type": "sitemap_redirect", "message": "URL есть в sitemap, но редиректит"})
        if p.canonical_url and (p.robots_noindex or p.x_robots_noindex) and p.canonical_is_self:
            conflicts.append({"url": p.url, "type": "canonical_noindex", "message": "Страница сама себе canonical, но закрыта noindex"})
        if is_blocked and in_sitemap:
            conflicts.append({"url": p.url, "type": "robots_blocked_sitemap", "message": "URL заблокирован в robots.txt, но присутствует в sitemap"})

    indexable_count = sum(1 for e in per_page if e["indexable"])
    return {
        "pages": per_page,
        "conflicts": conflicts,
        "indexable_count": indexable_count,
        "not_indexable_count": len(per_page) - indexable_count,
    }


# --------------------------------------------------------------------------
# Подсчёт SEO Score и агрегация итогового отчёта
# --------------------------------------------------------------------------

async def run_pagespeed(url: str, strategy: str = "mobile", api_key: Optional[str] = None) -> dict:
    """Опциональный Lighthouse/PageSpeed анализ одной страницы.

    PageSpeed использует Google PageSpeed Insights API; API key можно передать
    явно или через PAGESPEED_API_KEY. При недоступности API возвращается
    структурированная ошибка, а основной crawl не падает.
    """
    strategy = strategy.lower().strip()
    if strategy not in {"mobile", "desktop"}:
        strategy = "mobile"
    params = {"url": url, "strategy": strategy, "category": ["performance", "accessibility", "best-practices", "seo"]}
    key = api_key or os.getenv("PAGESPEED_API_KEY")
    if key:
        params["key"] = key
    try:
        timeout = aiohttp.ClientTimeout(total=PAGESPEED_TIMEOUT)
        async with aiohttp.ClientSession(timeout=timeout) as session:
            async with session.get(PAGESPEED_API_URL, params=params) as resp:
                payload = await resp.json(content_type=None)
                if resp.status >= 400:
                    return {"ok": False, "status": resp.status, "error": payload.get("error", payload)}
        lighthouse = payload.get("lighthouseResult", {})
        cats = lighthouse.get("categories", {})
        audits = lighthouse.get("audits", {})
        def score(name):
            v = cats.get(name, {}).get("score")
            return round(v * 100) if isinstance(v, (int, float)) else None
        def numeric(audit_id):
            val = audits.get(audit_id, {}).get("numericValue")
            return val if isinstance(val, (int, float)) else None
        loading = payload.get("loadingExperience", {}) or {}
        metrics = loading.get("metrics", {}) or {}
        return {
            "ok": True,
            "strategy": strategy,
            "performance_score": score("performance"),
            "accessibility_score": score("accessibility"),
            "best_practices_score": score("best-practices"),
            "seo_score": score("seo"),
            "lab": {
                "lcp_ms": numeric("largest-contentful-paint"),
                "cls": numeric("cumulative-layout-shift"),
                "tbt_ms": numeric("total-blocking-time"),
                "speed_index_ms": numeric("speed-index"),
                "fcp_ms": numeric("first-contentful-paint"),
            },
            "field": metrics,
            "origin_fallback": payload.get("originLoadingExperience", {}).get("metrics", {}),
        }
    except Exception as exc:
        return {"ok": False, "status": 0, "error": str(exc)}


async def run_search_console(access_token: str, site_url: str, start_date: str, end_date: str, dimensions: Optional[list] = None, row_limit: int = 1000) -> dict:
    """Получает Search Console Search Analytics через OAuth access token.

    Search Console требует авторизацию владельца/пользователя свойства; без
    токена функция ничего не отправляет и возвращает понятную ошибку.
    """
    if not access_token:
        return {"ok": False, "error": "Search Console access token is required"}
    dimensions = dimensions or ["query", "page", "device", "country"]
    endpoint = "https://www.googleapis.com/webmasters/v3/sites/" + aiohttp.helpers.quote(site_url, safe="") + "/searchAnalytics/query"
    body = {"startDate": start_date, "endDate": end_date, "dimensions": dimensions, "rowLimit": min(max(int(row_limit), 1), 25000), "type": "web"}
    headers = {"Authorization": f"Bearer {access_token}", "Content-Type": "application/json"}
    try:
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=30)) as session:
            async with session.post(endpoint, headers=headers, json=body) as resp:
                data = await resp.json(content_type=None)
                if resp.status >= 400:
                    return {"ok": False, "status": resp.status, "error": data}
                return {"ok": True, "rows": data.get("rows", []), "response": data}
    except Exception as exc:
        return {"ok": False, "status": 0, "error": str(exc)}


# Каппы на вклад ОДНОЙ категории проблемы (по коду) в общий штраф — не дают
# одной повторяющейся мелкой проблеме "убить" весь score.
_SEVERITY_PENALTY_CAP = {"critical": 30.0, "warning": 18.0, "info": 8.0}
_SEVERITY_FACTOR = {"critical": 1.0, "warning": 0.55, "info": 0.18}

# Знаменатель нормализации на страницу для каждой группы (используется как
# "сколько единиц штрафа на одну страницу считается уже 100%-но плохим
# результатом для этой группы"). Ниже значение — тем "строже" группа.
_GROUP_PAGE_DENOMINATOR = {
    "crawling": 6.0,
    "indexing": 6.0,
    "meta": 7.0,
    "content": 8.0,
    "links": 8.0,
    "performance": 8.0,
    "security": 6.0,
    "mobile": 6.0,
    "social": 10.0,
    "url": 10.0,
}


def _category_weighted_score(pages: list, site_level_issue_counts: dict) -> tuple[int, dict, dict]:
    """Единый (без двойного счёта), детерминированный расчёт SEO Score,
    разложенный по категориям (см. GROUP_LABELS/SCORE_WEIGHTS).

    penalty по каждому issue-коду считается ОДИН раз: для страничных issues —
    один раз на страницу (используем set(), чтобы повторный issue на той же
    странице не давал вклад дважды), для site-level issues — по фактическому
    количеству случаев. Контрибуция каждого КОДА капается по severity
    (_SEVERITY_PENALTY_CAP) в рамках своей группы, чтобы одна массово
    повторяющаяся info/warning проблема не могла обрушить всю группу сама
    по себе. Так как штраф считается относительно total_pages, доля
    затронутых страниц (affected ratio) естественным образом влияет на
    итоговую цифру: одна и та же абсолютная проблема на маленьком сайте
    "весит" больше, чем на сайте с тысячами страниц.

    Результат: (overall_score 0..100, group_penalty по кодам/группам для
    обратной совместимости с полем "category_penalties", group_scores 0..100
    по каждой из GROUP_LABELS-групп для нового поля "score_breakdown").
    """
    total_pages = max(len(pages), 1)

    per_code_contribution: dict = defaultdict(float)
    for p in pages:
        seen_codes = set()
        for issue in p.issues:
            code = issue.get("code")
            if code in seen_codes:
                continue
            seen_codes.add(code)
            meta = issue_meta(code)
            sev = meta.get("severity", "info")
            per_code_contribution[code] += meta.get("weight", 1) * _SEVERITY_FACTOR.get(sev, 0.18)

    for code, count in site_level_issue_counts.items():
        meta = issue_meta(code)
        sev = meta.get("severity", "info")
        per_code_contribution[code] += meta.get("weight", 1) * _SEVERITY_FACTOR.get(sev, 0.18) * count

    group_penalty: dict = defaultdict(float)
    for code, contribution in per_code_contribution.items():
        meta = issue_meta(code)
        sev = meta.get("severity", "info")
        capped = min(contribution, _SEVERITY_PENALTY_CAP.get(sev, 8.0))
        group_penalty[meta.get("group", "content")] += capped

    group_scores: dict = {}
    for group in GROUP_LABELS:
        penalty = group_penalty.get(group, 0.0)
        denominator = max(total_pages * _GROUP_PAGE_DENOMINATOR.get(group, 8.0), 1.0)
        normalized = min(100.0, (penalty / denominator) * 100.0)
        group_scores[group] = int(round(max(0.0, 100.0 - normalized)))

    total_weight = sum(SCORE_WEIGHTS.values()) or 1
    overall = sum(group_scores.get(g, 100) * w for g, w in SCORE_WEIGHTS.items()) / total_weight
    score = int(round(max(0.0, min(100.0, overall))))
    return score, dict(group_penalty), group_scores


def build_summary(crawl_result: dict, start_url: str, elapsed_seconds: float) -> dict:
    pages: list = crawl_result["pages"]
    total_pages = len(pages)

    grouped_issues = defaultdict(list)
    severity_counts = {"critical": 0, "warning": 0, "info": 0}

    for page in pages:
        for issue in page.issues:
            meta = issue_meta(issue["code"])
            grouped_issues[issue["code"]].append({
                "url": page.url,
                "message": issue["message"],
                "confidence": issue.get("confidence", meta.get("confidence_default", "medium")),
            })
            severity_counts[meta["severity"]] += 1

    # Site-level проблемы (не привязаны к конкретной странице) — считаем их
    # ОТДЕЛЬНО от page-level, чтобы передать в скоринг ровно один раз.
    site_level_issue_counts: dict = defaultdict(int)

    if not crawl_result["sitemap_found"]:
        meta = issue_meta("no_sitemap")
        grouped_issues["no_sitemap"].append({"url": start_url, "message": "Sitemap.xml не найден ни в robots.txt, ни по стандартному пути", "confidence": meta.get("confidence_default", "high")})
        severity_counts[meta["severity"]] += 1
        site_level_issue_counts["no_sitemap"] += 1

    if crawl_result["orphan_pages"]:
        meta = issue_meta("orphan_page")
        for url in crawl_result["orphan_pages"]:
            grouped_issues["orphan_page"].append({"url": url, "message": "Страница есть в sitemap.xml, но не найдена ссылками при обходе сайта", "confidence": meta.get("confidence_default", "medium")})
        severity_counts[meta["severity"]] += len(crawl_result["orphan_pages"])
        site_level_issue_counts["orphan_page"] += len(crawl_result["orphan_pages"])

    if crawl_result["blocked_urls"]:
        meta = issue_meta("blocked_by_robots")
        for url in crawl_result["blocked_urls"][:50]:
            grouped_issues["blocked_by_robots"].append({"url": url, "message": "Закрыто от обхода правилом Disallow в robots.txt", "confidence": meta.get("confidence_default", "high")})
        severity_counts[meta["severity"]] += len(crawl_result["blocked_urls"])
        site_level_issue_counts["blocked_by_robots"] += len(crawl_result["blocked_urls"])

    sitemap_duplicate_urls = crawl_result.get("sitemap_duplicate_urls") or []
    if sitemap_duplicate_urls:
        meta = issue_meta("sitemap_duplicate_url")
        for url in sitemap_duplicate_urls:
            grouped_issues["sitemap_duplicate_url"].append({"url": url, "message": "URL повторяется внутри sitemap.xml", "confidence": meta.get("confidence_default", "high")})
        severity_counts[meta["severity"]] += len(sitemap_duplicate_urls)
        site_level_issue_counts["sitemap_duplicate_url"] += len(sitemap_duplicate_urls)

    sitemap_invalid_urls = crawl_result.get("sitemap_invalid_urls") or []
    if sitemap_invalid_urls:
        meta = issue_meta("sitemap_invalid_url")
        for url in sitemap_invalid_urls:
            grouped_issues["sitemap_invalid_url"].append({"url": url, "message": "Запись <loc> в sitemap.xml невалидна", "confidence": meta.get("confidence_default", "high")})
        severity_counts[meta["severity"]] += len(sitemap_invalid_urls)
        site_level_issue_counts["sitemap_invalid_url"] += len(sitemap_invalid_urls)

    score, group_penalty, group_scores = _category_weighted_score(pages, site_level_issue_counts)

    categories = []
    for code, items in sorted(grouped_issues.items(), key=lambda kv: -len(kv[1])):
        meta = issue_meta(code)
        categories.append({
            "code": code,
            "label": meta["label"],
            "group": meta["group"],
            "group_label": GROUP_LABELS.get(meta["group"], meta["group"]),
            "severity": meta["severity"],
            "recommendation": meta["recommendation"],
            "count": len(items),
            "items": items,
        })

    broken_links = len(grouped_issues.get("broken_link", []))

    # Дополнительные агрегаты (не ломают старые ключи, только добавляют новые)
    page_type_stats = defaultdict(int)
    link_stats = {"internal_links": 0, "external_links": 0, "nofollow_links": 0, "sponsored_links": 0, "ugc_links": 0}
    image_stats = {"images_total": 0, "images_without_alt": 0, "images_missing_dimensions": 0, "images_not_lazy": 0, "images_decorative": 0, "images_broken": 0}
    structured_data_stats = defaultdict(int)
    performance_stats = {"avg_response_time_ms": None, "avg_page_size_bytes": None, "slow_pages": 0, "large_pages": 0}
    redirects = {"pages_with_redirects": 0, "redirect_loops": 0, "https_downgrades": 0}
    soft_404_count = 0
    url_issue_count = 0
    orphan_internal_pages_count = 0
    weakly_linked_pages_count = 0
    indexable_pages_count = 0

    response_times = []
    page_sizes = []

    for p in pages:
        page_type_stats[p.page_type] += 1
        link_stats["internal_links"] += p.internal_links
        link_stats["external_links"] += p.external_links
        link_stats["nofollow_links"] += p.nofollow_links
        link_stats["sponsored_links"] += p.sponsored_links
        link_stats["ugc_links"] += p.ugc_links
        image_stats["images_total"] += p.images_total
        image_stats["images_without_alt"] += p.images_without_alt
        image_stats["images_missing_dimensions"] += p.images_missing_dimensions
        image_stats["images_not_lazy"] += p.images_not_lazy
        image_stats["images_decorative"] += p.images_decorative
        image_stats["images_broken"] += p.images_broken
        for t in p.schema_types:
            structured_data_stats[t] += 1
        if p.response_time_ms is not None:
            response_times.append(p.response_time_ms)
        if p.page_size_bytes is not None:
            page_sizes.append(p.page_size_bytes)
        if p.response_time_ms and p.response_time_ms > SLOW_RESPONSE_MS:
            performance_stats["slow_pages"] += 1
        if p.page_size_bytes and p.page_size_bytes > LARGE_PAGE_BYTES:
            performance_stats["large_pages"] += 1
        if p.redirect_count > 0:
            redirects["pages_with_redirects"] += 1
        if p.is_redirect_loop:
            redirects["redirect_loops"] += 1
        if any(i["code"] == "https_downgrade" for i in p.issues):
            redirects["https_downgrades"] += 1
        if p.soft_404:
            soft_404_count += 1
        if any(i["code"] in ("url_too_long", "url_uppercase", "url_multiple_slashes", "query_parameter_url", "url_encoded_chars", "url_contains_space", "url_semicolon_param", "url_repeated_query_param", "url_empty_query_param") for i in p.issues):
            url_issue_count += 1
        if any(i["code"] == "no_incoming_internal_links" for i in p.issues):
            orphan_internal_pages_count += 1
        if any(i["code"] == "weakly_linked_page" for i in p.issues):
            weakly_linked_pages_count += 1
        if p.is_indexable:
            indexable_pages_count += 1

    if response_times:
        performance_stats["avg_response_time_ms"] = round(sum(response_times) / len(response_times))
    if page_sizes:
        performance_stats["avg_page_size_bytes"] = round(sum(page_sizes) / len(page_sizes))

    indexability = compute_indexability(pages, crawl_result["blocked_urls"], crawl_result.get("sitemap_urls", []))

    crawl_stats = {
        "pages_scanned": total_pages,
        "pages_discovered": crawl_result.get("pages_discovered", total_pages),
        "pages_skipped_limit": crawl_result.get("pages_skipped_limit", 0),
        "crawl_limit_reached": crawl_result.get("crawl_limit_reached", False),
        "crawl_termination_reason": crawl_result.get("crawl_termination_reason", "completed"),
        "max_depth_reached": max((p.depth for p in pages), default=0),
        "blocked_by_robots_count": len(crawl_result["blocked_urls"]),
        "orphan_pages_count": len(crawl_result["orphan_pages"]),
        "orphan_internal_pages_count": orphan_internal_pages_count,
        "weakly_linked_pages_count": weakly_linked_pages_count,
        "ssl_errors": sum(1 for p in pages if p.ssl_error),
        "soft_404_count": soft_404_count,
        "url_issue_count": url_issue_count,
        "indexable_pages_count": indexable_pages_count,
    }

    return {
        "start_url": start_url,
        "seo_score": score,
        "score_label": "Technical SEO Audit Score (не Google ranking score)",
        "score_breakdown": {GROUP_LABELS.get(g, g): v for g, v in group_scores.items()},
        "score_breakdown_by_group_code": group_scores,
        "score_weights": SCORE_WEIGHTS,
        "pages_scanned": total_pages,
        "critical_count": severity_counts["critical"],
        "warning_count": severity_counts["warning"],
        "info_count": severity_counts["info"],
        "broken_links_count": broken_links,
        "elapsed_seconds": round(elapsed_seconds, 1),
        "robots_txt_found": crawl_result["robots_found"],
        "robots_txt_status": crawl_result.get("robots_status"),
        "robots_txt_error": crawl_result.get("robots_error"),
        "robots_txt_wildcard_user_agent": crawl_result.get("robots_wildcard_user_agent"),
        "robots_txt_multiple_sitemaps": crawl_result.get("robots_multiple_sitemaps"),
        "sitemap_found": crawl_result["sitemap_found"],
        "sitemap_urls_count": crawl_result["sitemap_urls_count"],
        "sitemap_details": crawl_result.get("sitemap_details"),
        "sitemap_duplicate_urls": sitemap_duplicate_urls,
        "sitemap_invalid_urls": sitemap_invalid_urls,
        "sitemap_problem_urls": crawl_result.get("sitemap_problem_urls", []),
        "categories": categories,
        "category_penalties": group_penalty,
        "pages": [p.to_dict() for p in pages],
        "scoring_method": "weighted_category_score_v3_1",
        # Новые агрегированные блоки (v3), не ломающие старый формат:
        "crawl_stats": crawl_stats,
        "indexability": indexability,
        "redirects": redirects,
        "soft_404_count": soft_404_count,
        "url_issue_count": url_issue_count,
        "link_stats": link_stats,
        "image_stats": image_stats,
        "structured_data_stats": dict(structured_data_stats),
        "page_type_stats": dict(page_type_stats),
        "performance_stats": performance_stats,
        # Audit-level метаданные (v3.1)
        "audit_version": crawl_result.get("audit_version", AUDIT_VERSION),
        "crawl_started_at": crawl_result.get("crawl_started_at"),
        "crawl_finished_at": crawl_result.get("crawl_finished_at"),
        "crawl_duration_seconds": round(elapsed_seconds, 1),
        "crawler_user_agent": crawl_result.get("crawler_user_agent", USER_AGENT),
        "max_pages": crawl_result.get("max_pages"),
        "max_depth": crawl_result.get("max_depth"),
        "respect_robots": crawl_result.get("respect_robots"),
        "check_images": crawl_result.get("check_images"),
        "check_external_links": crawl_result.get("check_external_links"),
        "crawl_termination_reason": crawl_result.get("crawl_termination_reason", "completed"),
        "disclaimer": (
            "Technical audit, not a Google ranking score. Static HTML checks are combined with optional PageSpeed/Lighthouse "
            "and optional Search Console data. JavaScript-rendered content, real-user Core Web Vitals and search performance "
            "are only assessed when the corresponding integrations are enabled. Content quality, backlinks and search intent "
            "require additional context and are not inferred automatically. Page-type heuristics (article/product/utility/etc.) "
            "are used to reduce false positives, but remain heuristics, not certainties. Each issue carries a confidence level "
            "(high/medium/low) reflecting how certain the static analysis is, not a guarantee of real-world impact."
        ),
    }
