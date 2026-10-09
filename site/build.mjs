#!/usr/bin/env node
// Builds the static site, dist/, from papers/*/ :   node site/build.mjs [--papers <dir>] [--out <dir>]
//
//   dist/index.html                the main page: every paper, newest first
//   dist/papers/<slug>/            the paper's folder as shared, plus
//   dist/papers/<slug>/index.html  a placeholder paper page (the interactive page is not built yet)
//   dist/papers/<slug>/lean/index.html   the list of the Lean files (a static host lists no folder)
//   dist/_headers                  Cloudflare Pages: nothing under /papers/ may run a script, load
//                                  anything from elsewhere (the pages' fonts apart) or act on the site
//
// A bundle is UNTRUSTED input. Every string taken from one is escaped; the main page shows plain
// text only (the rendered HTML fields of page.json — paper.html, comments[].html, texHtml — are
// never written into a page here); a link into a bundle is built from checked path segments.
//
// WHERE EACH ELEMENT OF THE MAIN PAGE COMES FROM (one paper = one folder papers/<slug>/):
//
//   title, authors        page/page.json  title, authors
//   arXiv id              f4_seal.json    arxiv   (as the owner declared it; the seal covers it)
//   subject               share.json      subject (optional; the tool does not write it yet, so it
//                         is normally absent and then left out, with the "Subject" sort button).
//                         TODO: record the arXiv primary subject at share time (not fetched here).
//   shared date, @login   share.json      shared_at, shared_by
//   k of n proved         page.json results: n = results.length (the paper's results and those a
//                         correction split off them), k = those with proved === true
//   corrections           results with state === "error" and repair "statement" or "proof"
//   refuted, no repair    results with state === "error" and any other repair ("none")
//   "No error found"      no result has state === "error"
//   clarifications        page.json paper.comments whose kind starts with "reading" (readings of a
//                         statement, of a symbol, and the owner's)
//   cited results         f4_seal.json cited: the distinct node_id (results taken from the
//                         literature as cited, not proved here)
//   filter "Rests on cited results"   cited > 0, or page.json buckets.conditional > 0
//   What the check found  REPORT.md: its first paragraph after the verdict line (the report's own
//                         count sentence). The bundle holds no short prose headline of the main
//                         correction, so none is shown.
//   Findings fold         one line per result with state === "error": its name (bundle.json
//                         names[id], else kind + label), where the repair changes it (repair), and
//                         whether it is proved in Lean (proved). The printed and corrected statements
//                         are TeX; they are on the paper's page, not here.
//   Corrected PDF         page.json paper.pdf, when that file is in the folder
//   Lean code, Report     lean/ and REPORT.md, when they are in the folder
//   seal                  f4_seal.json code
import { copyFileSync, existsSync, lstatSync, mkdirSync, readdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

const ROOT = path.join(path.dirname(fileURLToPath(import.meta.url)), "..");
const TOOL_URL = "https://github.com/Jiyuan-Tan/TheoremChecker";
const FONTS = "https://fonts.googleapis.com/css2?family=Source+Serif+4:ital,opsz,wght@0,8..60,400;0,8..60,600;0,8..60,700;1,8..60,400&family=IBM+Plex+Mono:wght@400;500&display=swap";
const PAGE_SIZE = 20;
const SLUG = /^[a-z0-9][a-z0-9_-]{0,63}$/u;
const ARXIV_ID = /^(?:\d{4}\.\d{4,5}|[a-z-]+(?:\.[A-Za-z-]+)?\/\d{7})(?:v\d+)?$/u;

export const esc = (s) => String(s).replace(/[&<>"']/gu, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" })[c]);
const text = (v) => (typeof v === "string" ? v : "");
/** A string of a bundle as plain text: the commonest TeX wrapping taken off, one line. */
export function plain(v, max = 400) {
  const s = text(v)
    .replace(/\\(?:label|ref|eqref|cite[a-z]*)\{[^{}]*\}/gu, "")
    .replace(/\\(?:emph|textbf|textit|textsc|textrm|text|mathrm)\{([^{}]*)\}/gu, "$1")
    .replace(/\\[,;!]|~/gu, " ")
    .replace(/\\([&%$#_{}])/gu, "$1")
    .replace(/\$/gu, "")
    .replace(/\s+/gu, " ")
    .trim();
  return s.length > max ? `${s.slice(0, max).trimEnd()}…` : s;
}
const count = (n, one, many = `${one}s`) => `${n} ${n === 1 ? one : many}`;
/** A path of a bundle as a relative link: plain segments only, each encoded; null otherwise. */
const href = (rel) => (typeof rel === "string" && rel.split("/").every((s) => s && s !== "." && s !== ".." && !/[\\\p{Cc}]/u.test(s)) ? rel.split("/").map(encodeURIComponent).join("/") : null);
const isFile = (p) => { try { return lstatSync(p).isFile(); } catch { return false; } };
const isDir = (p) => { try { return lstatSync(p).isDirectory(); } catch { return false; } };
const readJson = (p) => { try { return JSON.parse(readFileSync(p, "utf8")); } catch { return null; } };

/** What the pages show of the paper folder `dir`; null when it has no readable page.json. */
export function paperData(dir, slug) {
  const page = readJson(path.join(dir, "page", "page.json"));
  if (!page || typeof page !== "object" || !Array.isArray(page.results)) return null;
  const obj = (v) => (v && typeof v === "object" ? v : {});
  const share = obj(readJson(path.join(dir, "share.json")));
  const seal = obj(readJson(path.join(dir, "f4_seal.json")));
  const names = obj(obj(readJson(path.join(dir, "bundle.json"))).names);
  const results = page.results.filter((r) => r && typeof r === "object");
  const errors = results.filter((r) => r.state === "error");
  const corrected = errors.filter((r) => r.repair === "statement" || r.repair === "proof");
  const comments = Array.isArray(obj(page.paper).comments) ? page.paper.comments : [];
  const cited = new Set((Array.isArray(seal.cited) ? seal.cited : []).map((c) => text(obj(c).node_id)).filter(Boolean)).size;
  const sharedAt = /^\d{4}-\d{2}-\d{2}/u.test(text(share.shared_at)) && !Number.isNaN(Date.parse(share.shared_at)) ? share.shared_at : null;
  const pdf = href(obj(page.paper).pdf);

  // REPORT.md: the paragraph after the verdict line
  let summary = "";
  const reportFile = path.join(dir, "REPORT.md");
  if (isFile(reportFile)) {
    const head = readFileSync(reportFile, "utf8").split(/^## /mu)[0].split(/\n\s*\n/u).map((p) => p.trim());
    const at = head.findIndex((p) => p.startsWith("**Verdict"));
    summary = plain(head.slice(at + 1).find((p) => p && !p.startsWith(">") && !p.startsWith("#")) ?? "", 700);
  }

  return {
    slug,
    title: plain(page.title) || slug,
    authors: plain(page.authors),
    arxiv: ARXIV_ID.test(text(seal.arxiv)) ? seal.arxiv : null,
    subject: plain(share.subject, 80) || null,
    sharedAt,
    sharedBy: /^[A-Za-z0-9-]{1,39}$/u.test(text(share.shared_by)) ? share.shared_by : null,
    total: results.length,
    proved: results.filter((r) => r.proved === true).length,
    errors: errors.length,
    corrections: corrected.length,
    refuted: errors.length - corrected.length,
    clarifications: comments.filter((c) => text(obj(c).kind).startsWith("reading")).length,
    cited,
    restsOnCited: cited > 0 || obj(page.buckets).conditional > 0,
    summary,
    findings: errors.map((r) => ({
      name: plain(names[r.id], 80) || plain(`${text(r.kind)} ${text(r.label) || text(r.id)}`, 80),
      outcome: r.repair === "statement" ? "statement corrected" : r.repair === "proof" ? "statement unchanged, proof corrected" : "refuted, no repair",
      lean: r.proved === true ? "proved in Lean" : "not proved in Lean",
    })),
    pdf: pdf && isFile(path.join(dir, ...obj(page.paper).pdf.split("/"))) ? pdf : null,
    lean: isDir(path.join(dir, "lean")),
    report: isFile(reportFile),
    match: isFile(path.join(dir, "MATCH.md")),
    seal: /^[0-9a-f]{64}$/u.test(text(seal.code)) ? seal.code : null,
  };
}

const CHECK = '<svg width="12" height="12" viewBox="0 0 12 12" fill="none" stroke="currentColor" stroke-width="2" aria-hidden="true"><path d="M2 6.5l2.6 2.6L10 3.4"/></svg>';

function badges(p) {
  const out = [];
  if (p.refuted > 0) out.push(`<span class="badge red">${count(p.refuted, "result")} refuted, no repair keeps ${p.refuted === 1 ? "it" : "them"}</span>`);
  if (p.total > 0) out.push(`<span class="badge green">${CHECK}${p.proved} of ${count(p.total, "result")} proved in Lean 4</span>`);
  if (p.corrections > 0) out.push(`<span class="badge amber">${count(p.corrections, "correction")}</span>`);
  if (p.errors === 0) out.push('<span class="badge grey">No error found</span>');
  if (p.clarifications > 0) out.push(`<span class="badge blue">${count(p.clarifications, "clarification")}</span>`);
  if (p.cited > 0) out.push(`<span class="badge grey">${count(p.cited, "cited result")} taken as stated</span>`);
  return `<div class="badges">${out.join("")}</div>`;
}

/** The meta line: arXiv id · subject · shared date by @login — each when known. */
function meta(p) {
  const shared = [p.sharedAt ? `shared ${esc(p.sharedAt.slice(0, 10))}` : "", p.sharedBy ? `${p.sharedAt ? "" : "shared "}by @${esc(p.sharedBy)}` : ""].filter(Boolean).join(" ");
  return [
    p.arxiv ? `<a href="https://arxiv.org/abs/${esc(p.arxiv)}">arXiv:${esc(p.arxiv)}</a>` : "",
    p.subject ? esc(p.subject) : "",
    shared,
  ].filter(Boolean).join(" · ");
}

const sealSpan = (p) => (p.seal ? `<span class="seal" title="Checksum of the reviewers' verdicts and every file of the bundle: ${p.seal}">seal ${p.seal.slice(0, 12)}</span>` : "");

function entry(p, featured) {
  const base = `papers/${p.slug}/`;
  const flags = [p.corrections > 0 ? "repaired" : "", p.errors === 0 ? "clean" : "", p.restsOnCited ? "cited" : ""].filter(Boolean).join(" ");
  const search = [p.title, p.authors, p.arxiv ?? "", p.slug, p.sharedBy ?? "", p.subject ?? ""].join(" ").toLowerCase();
  return `
  <article class="paper${featured ? " featured" : ""}" data-date="${esc(p.sharedAt ?? "")}" data-corrections="${p.corrections}" data-subject="${esc((p.subject ?? "").toLowerCase())}" data-flags="${flags}" data-search="${esc(search)}">
    <div class="kicker recent">Most recent</div>
    <h2><a href="${base}">${esc(p.title)}</a></h2>
    ${p.authors ? `<div class="authors">${esc(p.authors)}</div>` : ""}
    <div class="meta">${meta(p)}</div>
    ${badges(p)}
    ${p.summary ? `<p class="found"><strong>What the check found.</strong> ${esc(p.summary)}</p>` : ""}
    <div class="actions">
      <a class="main" href="${base}">Read with findings</a>
      ${p.pdf ? `<a href="${base}${p.pdf}">Corrected PDF</a>` : ""}
      ${p.lean ? `<a href="${base}lean/">Lean code</a>` : ""}
      ${p.report ? `<a href="${base}REPORT.md">Report</a>` : ""}
      <span class="grow"></span>
      ${sealSpan(p)}
    </div>
    ${p.findings.length > 0 ? `<details>
      <summary>Findings (${p.findings.length})</summary>
      <ul>
        ${p.findings.map((f) => `<li>${esc(f.name)} — ${f.outcome}, ${f.lean}</li>`).join("\n        ")}
      </ul>
    </details>` : ""}
  </article>`;
}

const CSS = `
[hidden]{display:none!important}
body{margin:0;background:#fdfcfa;font-family:'Source Serif 4',Georgia,serif;color:#1a1a1a;padding:0 16px 64px}
a{color:#820000}a:hover{color:#b1040e}
.wrap{max-width:880px;margin:0 auto}
header{padding:56px 0 28px;border-bottom:1px solid #e0dad0}
.kicker{font-size:.78rem;letter-spacing:.14em;text-transform:uppercase;color:#8c1515;font-weight:600}
header nav{display:flex;flex-wrap:wrap;gap:8px 22px;margin-top:14px;font-size:.95rem}
header nav a{text-decoration:none;border-bottom:1px dotted #c58a8a;color:#8c1515}
header nav .here{font-weight:600}
h1{margin:26px 0 14px;font-size:2.4rem;line-height:1.15;font-weight:700;letter-spacing:-.01em}
.lede{margin:0 0 12px;font-size:1.08rem;line-height:1.6;color:#5c5853;max-width:720px}
.lede:last-child{margin-bottom:0}
.share{display:flex;flex-wrap:wrap;gap:16px 24px;align-items:center;margin:28px 0 8px;padding:18px 22px;background:#f7f5f0;border:1px solid #e0dad0;border-radius:8px}
.share>div{flex:999 1 420px;min-width:0}
.share .t{font-weight:600;font-size:1.05rem}
.share .d{margin-top:4px;font-size:.95rem;line-height:1.5;color:#5c5853}
.share .btn{flex:0 0 auto;display:inline-block;padding:11px 18px;background:#8c1515;color:#fdfcfa;text-decoration:none;border-radius:6px;font-size:.95rem;font-weight:600}
.controls{display:none}
.js .controls{display:block}
.row{display:flex;flex-wrap:wrap;gap:6px;align-items:center;font-size:.85rem}
.row.top{gap:12px 20px;margin:30px 0 6px}
.row.filter{margin-bottom:8px}
.row .lab{color:#6b655d;margin-right:4px}
.sr{position:absolute;left:-9999px}
#q{flex:999 1 260px;min-width:0;box-sizing:border-box;padding:11px 14px;font:inherit;font-size:.95rem;color:#1a1a1a;background:#fdfcfa;border:1px solid #cfc7b9;border-radius:6px}
.pill{font:inherit;padding:9px 13px;border:1px solid #cfc7b9;border-radius:999px;background:#fdfcfa;color:#1a1a1a;cursor:pointer}
.sort .pill[aria-pressed=true]{border-color:#8c1515;background:#8c1515;color:#fdfcfa}
.filter .pill[aria-pressed=true]{border-color:#1a1a1a;background:#1a1a1a;color:#fdfcfa}
.legend{margin:10px 0 0;font-size:.85rem;line-height:1.55;color:#6b655d}
.legend strong{color:#1a1a1a}
.paper{padding:26px 0 22px;border-bottom:1px solid #e8e2d8}
.paper h2{margin:0 0 6px;font-size:1.35rem;line-height:1.3;font-weight:700}
.paper h2 a{color:inherit;text-decoration:none}
.paper .recent{display:none}
.paper.featured{margin-top:26px;padding:22px 24px 20px;background:#f7f5f0;border:1px solid #e0dad0;border-top:3px solid #b1040e;border-radius:8px}
.paper.featured .recent{display:block;font-size:.72rem}
.paper.featured h2{margin:8px 0;font-size:1.55rem;line-height:1.25}
.authors{font-size:.95rem;color:#5c5853}
.meta{margin-top:8px;font-family:'IBM Plex Mono',monospace;font-size:.78rem;color:#6b655d;overflow-wrap:anywhere}
.meta a{color:inherit}
.badges{display:flex;flex-wrap:wrap;gap:8px;margin-top:10px;font-size:.78rem}
.badge{display:inline-flex;align-items:center;gap:5px;padding:4px 9px;border-radius:3px;font-weight:600}
.badge.green{background:#e4efe6;color:#24553a}
.badge.amber{background:#fbe3c4;color:#7a3a06}
.badge.blue{background:#edf1f6;color:#2b4266}
.badge.grey{background:#f1eee7;color:#5c5853}
.badge.red{background:#f6d6d6;color:#7a1f1f}
.found{margin:12px 0 0;font-size:1rem;line-height:1.6}
.actions{display:flex;flex-wrap:wrap;gap:6px 20px;align-items:center;margin-top:12px;font-size:.95rem}
.actions .main{font-weight:600}
.grow{flex:1 1 auto}
.seal{font-family:'IBM Plex Mono',monospace;font-size:.78rem;color:#6b655d}
details{margin-top:12px;font-size:.95rem;color:#5c5853}
details>summary{cursor:pointer;color:#8c1515;padding:6px 0}
details ul{margin:8px 0 0;padding-left:20px;line-height:1.6}
.none{margin:28px 0 0;color:#6b655d}
.pager{display:flex;flex-wrap:wrap;gap:6px 14px;justify-content:center;margin:28px 0 0;font-size:.95rem}
.pager button{font:inherit;background:none;border:0;padding:4px 2px;color:#820000;cursor:pointer;text-decoration:underline}
.pager button[disabled]{color:#9a938c;cursor:default;text-decoration:none}
.pager button[aria-current]{color:#1a1a1a;font-weight:700;text-decoration:none}
.how{margin-top:44px}
.how h2{font-size:1.2rem;margin:0 0 8px}
.how p{margin:0 0 10px;font-size:.98rem;line-height:1.6;color:#5c5853;max-width:720px}
footer{margin-top:44px;padding-top:18px;border-top:1px solid #e0dad0;font-size:.85rem;line-height:1.6;color:#6b655d}
code,.mono{font-family:'IBM Plex Mono',monospace}
.links{margin:18px 0 0;padding-left:20px;line-height:1.9}
.files{margin:18px 0 0;padding:0;list-style:none;font-family:'IBM Plex Mono',monospace;font-size:.85rem;line-height:1.8;overflow-wrap:anywhere}
@media (max-width:560px){header{padding-top:36px}h1{font-size:1.9rem}.paper.featured{padding:18px 16px 16px}.share{padding:16px}}
`;

// Search, sort, filter and paging over the entries' data attributes. Without it the page is the
// plain list, newest first.
const SCRIPT = `
(function () {
  var list = document.getElementById('papers'); if (!list) return;
  var items = [].slice.call(list.querySelectorAll('.paper'));
  var q = document.getElementById('q'), pager = document.getElementById('pager'), none = document.getElementById('none');
  var state = { sort: 'date', filter: '', page: 1 }, SIZE = ${PAGE_SIZE};
  function cmp(a, b) {
    var d = a.dataset, e = b.dataset;
    if (state.sort === 'corrections' && d.corrections !== e.corrections) return e.corrections - d.corrections;
    if (state.sort === 'subject' && d.subject !== e.subject) return !d.subject ? 1 : !e.subject ? -1 : d.subject < e.subject ? -1 : 1;
    return d.date < e.date ? 1 : d.date > e.date ? -1 : 0;
  }
  function button(label, page, current) {
    var b = document.createElement('button'); b.type = 'button'; b.textContent = label;
    if (current) b.setAttribute('aria-current', 'page');
    if (page === null) b.disabled = true; else b.addEventListener('click', function () { state.page = page; draw(); window.scrollTo(0, list.offsetTop - 20); });
    pager.appendChild(b);
  }
  function draw() {
    var words = q.value.toLowerCase().split(/\\s+/).filter(Boolean);
    var shown = items.slice().sort(cmp).filter(function (el) {
      return (!state.filter || (' ' + el.dataset.flags + ' ').indexOf(' ' + state.filter + ' ') >= 0) && words.every(function (w) { return el.dataset.search.indexOf(w) >= 0; });
    });
    var pages = Math.max(1, Math.ceil(shown.length / SIZE)); if (state.page > pages) state.page = pages;
    var plainView = state.sort === 'date' && !state.filter && !words.length && state.page === 1;
    items.forEach(function (el) { el.hidden = true; el.classList.remove('featured'); });
    shown.forEach(function (el, i) { list.appendChild(el); el.hidden = Math.floor(i / SIZE) + 1 !== state.page; });
    if (plainView && shown[0]) shown[0].classList.add('featured');
    none.hidden = shown.length > 0;
    pager.textContent = ''; pager.hidden = pages < 2;
    if (pages > 1) {
      button('\\u2039 Previous', state.page > 1 ? state.page - 1 : null);
      for (var i = 1; i <= pages; i++) button(String(i), i, i === state.page);
      button('Next \\u203a', state.page < pages ? state.page + 1 : null);
    }
  }
  [].forEach.call(document.querySelectorAll('.pill'), function (b) {
    b.addEventListener('click', function () {
      state[b.dataset.set] = b.dataset.value; state.page = 1;
      [].forEach.call(b.parentNode.querySelectorAll('.pill'), function (o) { o.setAttribute('aria-pressed', String(o === b)); });
      draw();
    });
  });
  q.addEventListener('input', function () { state.page = 1; draw(); });
  draw();
})();
`;

const PAPERS_CSP = "default-src 'none'; img-src 'self' data:; style-src 'unsafe-inline' https://fonts.googleapis.com; font-src https://fonts.gstatic.com; sandbox";

const head = (title, extra = "") => `<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>${esc(title)}</title>
<link rel="stylesheet" href="${FONTS}">
<style>${CSS}</style>${extra}
</head>`;

export function indexHtml(papers) {
  const sorted = [...papers].sort((a, b) => (a.sharedAt ?? "") < (b.sharedAt ?? "") ? 1 : (a.sharedAt ?? "") > (b.sharedAt ?? "") ? -1 : a.slug < b.slug ? -1 : 1);
  const pill = (set, value, label, on) => `<button type="button" class="pill" data-set="${set}" data-value="${value}" aria-pressed="${on}">${label}</button>`;
  return `${head("TheoremChecker — checked papers", "\n<script>document.documentElement.className='js'</script>")}
<body>
<div class="wrap">

  <header>
    <div class="kicker">TheoremChecker · Verified papers</div>
    <nav>
      <span class="here">Checked papers</span>
      <a href="#how">How a paper is checked</a>
      <a href="#share">Share a paper</a>
      <a href="${TOOL_URL}">GitHub ↗</a>
    </nav>
    <h1>Checked papers</h1>
    <p class="lede">Each paper here was read by TheoremChecker: every theorem, lemma and assumption was refereed against the paper's own proof, each error found was repaired by the smallest change that keeps the claim, and the corrected results were proved in Lean 4. Open a paper to see every finding beside the sentence it concerns, and the Lean statement behind each result.</p>
    <p class="lede">Papers are shared by the people who ran the check, signed in with GitHub. A page shows what was checked, what was not, and what each result still takes from the literature.</p>
  </header>

  <section id="share" class="share">
    <div>
      <div class="t">Share a paper you checked</div>
      <div class="d">On a finished run, press <em>Share</em> on the paper's page. The bundle is checked automatically and published here under your GitHub name. A share always carries the whole bundle: the corrected paper's TeX source and PDF, the findings, the Lean code and the report.</div>
    </div>
    <a class="btn" href="#how">How sharing works</a>
  </section>

  <div class="controls">
    <div class="row top">
      <label for="q" class="sr">Search papers</label>
      <input id="q" type="search" placeholder="Search title, author, arXiv id">
      <div role="group" aria-label="Sort papers" class="row sort">
        <span class="lab">Sort:</span>
        ${pill("sort", "date", "Newest", true)}
        ${pill("sort", "corrections", "Most corrections", false)}
        ${papers.some((p) => p.subject) ? pill("sort", "subject", "Subject", false) : ""}
      </div>
    </div>
    <div role="group" aria-label="Filter by outcome" class="row filter">
      <span class="lab">Show:</span>
      ${pill("filter", "", "All", true)}
      ${pill("filter", "repaired", "Errors repaired", false)}
      ${pill("filter", "clean", "No error found", false)}
      ${pill("filter", "cited", "Rests on cited results", false)}
    </div>
  </div>
  <p class="legend"><strong>Reading the badges.</strong> <em>Proved in Lean</em> counts the paper's results whose corrected statement Lean certifies. <em>Corrections</em> are errors the referee found and repaired; <em>clarifications</em> are readings of ambiguous wording, not errors. A check covers the paper's results, not the prose around them.</p>

  <div id="papers">${sorted.map((p, i) => entry(p, i === 0)).join("\n")}
  </div>
  <p id="none" class="none"${sorted.length > 0 ? " hidden" : ""}>${sorted.length > 0 ? "No paper matches." : "No paper has been shared yet."}</p>
  <nav id="pager" class="pager" aria-label="Pages" hidden></nav>

  <section id="how" class="how">
    <h2>How a paper is checked, and shared</h2>
    <p>TheoremChecker reads a paper's LaTeX source. Every result is refereed against the paper's own proof; an error is repaired by the smallest change that keeps the claim; the corrected statements are stated and proved in Lean 4, and two reviewers must each pass every Lean statement as saying what the paper says. The tool and its manual are on <a href="${TOOL_URL}">GitHub</a>.</p>
    <p>Pressing <em>Share</em> on a finished run opens a pull request to this registry from your GitHub account, holding the run's bundle. An automatic check confirms the bundle is complete and unchanged since the run wrote it; when it passes, the pull request merges and the paper appears here.</p>
  </section>

  <footer>
    Every page is built from a bundle whose seal was checked when it was shared: the reviewers' verdicts, the Lean code and the corrected paper are the files the check wrote. The seal shows a bundle is complete and unchanged; it does not show who ran the check. "Proved in Lean" means the statement shown on the paper's page compiles with no <span class="mono">sorry</span> and its axioms are listed there.
  </footer>

</div>
<script>${SCRIPT}</script>
</body>
</html>
`;
}

/** The placeholder paper page, dist/papers/<slug>/index.html. */
export function paperHtml(p) {
  const links = [
    p.report ? '<li><a href="REPORT.md">REPORT.md</a> — the report: what was wrong, what was done, what was proved</li>' : "",
    p.match ? '<li><a href="MATCH.md">MATCH.md</a> — each result beside its Lean declaration</li>' : "",
    p.pdf ? `<li><a href="${p.pdf}">Corrected PDF</a> — the paper as it reads after the corrections</li>` : "",
    p.lean ? '<li><a href="lean/">lean/</a> — the Lean code</li>' : "",
  ].filter(Boolean);
  return `${head(`${p.title} — TheoremChecker`)}
<body>
<div class="wrap">
  <header>
    <div class="kicker">TheoremChecker · Verified papers</div>
    <nav><a href="../../">Checked papers</a></nav>
    <h1>${esc(p.title)}</h1>
    ${p.authors ? `<div class="authors">${esc(p.authors)}</div>` : ""}
    <div class="meta">${meta(p)}</div>
    ${badges(p)}
  </header>
  ${p.summary ? `<p class="found"><strong>What the check found.</strong> ${esc(p.summary)}</p>` : ""}
  <ul class="links">
    ${links.join("\n    ")}
  </ul>
  <p class="legend">The interactive page (findings beside the text, Lean statements) is not built yet.</p>
  ${p.seal ? `<footer>seal <span class="mono">${p.seal}</span> — a checksum of the reviewers' verdicts and every file of the bundle. It shows the bundle is complete and unchanged; it does not show who ran the check.</footer>` : ""}
</div>
</body>
</html>
`;
}

/** The regular files and folders of `from`, copied to `to`; anything else is left behind. Returns
 *  the files copied, by path from `from`. */
function copyTree(from, to, rel = "") {
  const out = [];
  mkdirSync(path.join(to, rel), { recursive: true });
  for (const e of readdirSync(path.join(from, rel), { withFileTypes: true }).sort((a, b) => (a.name < b.name ? -1 : 1))) {
    const r = rel ? `${rel}/${e.name}` : e.name;
    if (e.name.startsWith(".") || e.isSymbolicLink() || /\.(?:x?html?|xht|xml|m?js)$/iu.test(e.name)) continue;
    if (e.isDirectory()) out.push(...copyTree(from, to, r));
    else if (e.isFile()) {
      copyFileSync(path.join(from, r), path.join(to, r));
      out.push(r);
    }
  }
  return out;
}

function leanIndexHtml(p, files) {
  return `${head(`Lean code — ${p.title}`)}
<body>
<div class="wrap">
  <header>
    <div class="kicker">TheoremChecker · Verified papers</div>
    <nav><a href="../../../">Checked papers</a><a href="../">${esc(p.title)}</a></nav>
    <h1>Lean code</h1>
    <p class="lede">A standalone Lake project: the paper's Lean, the toolkit modules it imports, and <span class="mono">Check.lean</span>.</p>
  </header>
  <ul class="files">
    ${files.map((f) => `<li><a href="${href(f)}">${esc(f)}</a></li>`).join("\n    ")}
  </ul>
</div>
</body>
</html>
`;
}

/** Builds the site of the papers under `papersDir` into `outDir`; returns the papers it shows. */
export function build({ papersDir = path.join(ROOT, "papers"), outDir = path.join(ROOT, "dist"), log = console.log } = {}) {
  rmSync(outDir, { recursive: true, force: true });
  mkdirSync(path.join(outDir, "papers"), { recursive: true });
  const papers = [];
  const slugs = existsSync(papersDir) ? readdirSync(papersDir, { withFileTypes: true }).filter((e) => e.isDirectory()).map((e) => e.name).sort() : [];
  for (const slug of slugs) {
    const dir = path.join(papersDir, slug);
    const p = SLUG.test(slug) ? paperData(dir, slug) : null;
    if (!p) {
      log(`skipped ${JSON.stringify(slug)}: no readable page/page.json`);
      continue;
    }
    const out = path.join(outDir, "papers", slug);
    const files = copyTree(dir, out);
    writeFileSync(path.join(out, "index.html"), paperHtml(p));
    const lean = files.filter((f) => f.startsWith("lean/") && href(f)).map((f) => f.slice("lean/".length));
    if (p.lean) writeFileSync(path.join(out, "lean", "index.html"), leanIndexHtml(p, lean));
    papers.push(p);
  }
  writeFileSync(path.join(outDir, "index.html"), indexHtml(papers));
  // Cloudflare Pages: a file of a bundle is served as data — no script runs from it (an SVG figure
  // included), and it is sandboxed: it has no origin of the site's. The font hosts are for the
  // pages written above, which are under /papers/ too.
  writeFileSync(path.join(outDir, "_headers"), `/papers/*\n  Content-Security-Policy: ${PAPERS_CSP}\n  X-Content-Type-Options: nosniff\n`);
  log(`built ${papers.length} paper(s) into ${outDir}`);
  return papers;
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const arg = (name) => { const i = process.argv.indexOf(name); return i > 0 && process.argv[i + 1] ? path.resolve(process.argv[i + 1]) : undefined; };
  build({ papersDir: arg("--papers"), outDir: arg("--out") });
}
