import assert from "node:assert/strict";
import { existsSync, readFileSync, writeFileSync } from "node:fs";
import path from "node:path";
import { test } from "node:test";
import { build, CSP, esc, plain } from "../site/build.mjs";
import { copyFixture, FIXTURE, readJson, SLUG, tmp, writeJson } from "./helpers.mjs";

const site = (papersDir) => {
  const outDir = path.join(tmp(), "dist");
  const papers = build({ papersDir, outDir, log: () => {} });
  return { outDir, papers, index: readFileSync(path.join(outDir, "index.html"), "utf8") };
};

test("the index lists the fixture paper with its badges", () => {
  const { outDir, papers, index } = site(path.dirname(FIXTURE));
  assert.equal(papers.length, 1);
  assert.deepEqual(
    { total: papers[0].total, proved: papers[0].proved, corrections: papers[0].corrections, refuted: papers[0].refuted, clarifications: papers[0].clarifications, cited: papers[0].cited },
    { total: 41, proved: 40, corrections: 22, refuted: 0, clarifications: 135, cited: 1 },
  );
  for (const s of [
    "TheoremChecker · Verified papers",
    '<h2><a href="papers/cns_simple_dml/">A Simple and General Debiased Machine Learning Theorem with Finite Sample Guarantees</a></h2>',
    "Victor Chernozhukov, Whitney K. Newey, Rahul Singh",
    "shared 2026-10-09 by @fixture-user",
    "40 of 41 results proved in Lean 4",
    "22 corrections",
    "135 clarifications",
    "1 cited result taken as stated",
    "<strong>What the check found.</strong> 28 result(s) of the paper were examined",
    'href="papers/cns_simple_dml/corrected_paper/main.pdf">Corrected PDF',
    'href="papers/cns_simple_dml/lean/">Lean code',
    'href="papers/cns_simple_dml/#report">Full report',
    "seal e84ecbe79ae9",
    "Findings (22)",
    "<li>Theorem 5.1 — statement corrected, proved in Lean</li>",
    "<li>Corollary B.4 — statement unchanged, proof corrected, proved in Lean</li>",
    'data-flags="repaired cited"',
  ]) assert.ok(index.includes(s), `the index lacks: ${s}`);
  assert.ok(!index.includes("No error found</span>"));
  assert.ok(!index.includes(">Subject<"), "no paper records a subject: no Subject button");
  // the paper's folder is copied, with its page (the viewer's, drawn from page/page.json, over a
  // plain summary) and the list of the Lean files
  const paper = readFileSync(path.join(outDir, "papers", SLUG, "index.html"), "utf8");
  for (const s of [
    '<script src="../../viewer/app.js" data-snapshot="page/page.json"></script>', '<script src="../../viewer/purify.min.js"></script>',
    '<link rel="stylesheet" href="../../viewer/app.css">', '<a class="brand" href="../../">',
    "<title>A Simple and General Debiased Machine Learning Theorem with Finite Sample Guarantees — TheoremChecker</title>",
    'href="REPORT.md"', 'href="corrected_paper/main.pdf"', 'href="lean/"', "40 of 41 results proved in Lean 4",
  ]) assert.ok(paper.includes(s), `the paper page lacks: ${s}`);
  assert.ok(!paper.includes('href="MATCH.md"'), "the result-by-Lean file is not offered");
  assert.ok(!paper.includes("{{"), "every field of the template is filled");
  assert.ok(existsSync(path.join(outDir, "papers", SLUG, "f4_seal.json")));
  assert.ok(readFileSync(path.join(outDir, "papers", SLUG, "lean", "index.html"), "utf8").includes('href="Papers/CnsSimpleDml/TVar.lean"'));
  // the viewer is copied beside the papers (its template apart); GitHub Pages: no header file, no Jekyll
  for (const f of ["app.js", "app.css", "purify.min.js", "katex/katex.min.js", "katex/katex.min.css", "pdfjs/pdf.min.mjs", "pdfjs/pdf.worker.min.mjs", "VERSION"]) assert.ok(existsSync(path.join(outDir, "viewer", f)), `dist/viewer lacks ${f}`);
  assert.ok(!existsSync(path.join(outDir, "viewer", "page.html")) && !existsSync(path.join(outDir, "_headers")) && existsSync(path.join(outDir, ".nojekyll")));
  // every page carries its policy in a <meta>, and runs no inline script
  const leanIndex = readFileSync(path.join(outDir, "papers", SLUG, "lean", "index.html"), "utf8");
  for (const html of [index, paper, leanIndex]) {
    assert.match(html, /<meta http-equiv="Content-Security-Policy" content="default-src 'self'; script-src 'self'; [^"]*base-uri 'none'; form-action 'none'">/u);
    assert.ok(!/<script(?![^>]*\ssrc=)[^>]*>/u.test(html), "an inline script");
  }
  assert.ok(paper.includes(`content="${CSP.replace("font-src 'self' data:", "font-src 'self' data: https://cdn.jsdelivr.net")}"`), "the paper's page: the strict policy, the code font's host apart");
  assert.ok(index.includes('<script src="site.js"></script>') && readFileSync(path.join(outDir, "site.js"), "utf8").includes("document.documentElement.className = 'js'"));
  assert.ok(index.includes("A share carries the whole bundle") && !index.includes("You choose"));
});

test("a bundle's strings are escaped, and its rendered HTML is never used", () => {
  const dir = copyFixture();
  const X = '<script>alert(1)</script>"><img src=x onerror=alert(2)>';
  const file = path.join(dir, "page", "page.json");
  const page = readJson(file);
  page.title = `Title ${X}`;
  page.authors = `Author ${X}`;
  page.paper.html = `<script>alert("paper")</script>`;
  page.paper.comments[0].html = `<script>alert("comment")</script>`;
  page.texHtml = { x: `<script>alert("tex")</script>` };
  page.paper.pdf = 'corrected_paper/"><script>alert(3)</script>.pdf';
  page.results.find((r) => r.state === "error").id = "bad";
  writeJson(file, page);
  const bundle = readJson(path.join(dir, "bundle.json"));
  bundle.names.bad = `Theorem ${X}`;
  writeJson(path.join(dir, "bundle.json"), bundle);
  writeJson(path.join(dir, "share.json"), { shared_by: X, shared_at: X, arxiv: X, subject: `stat.ML ${X}` });
  writeJson(path.join(dir, "f4_seal.json"), { ...readJson(path.join(dir, "f4_seal.json")), arxiv: X, code: X });
  writeFileSync(path.join(dir, "REPORT.md"), `# Report\n\n**Verdict: X**\n\nSummary ${X}\n\n## Next\n`);
  writeFileSync(path.join(dir, "lean", "<img src=x onerror=alert(4)>.lean"), "x");
  // files a browser would run are not served: a page, a script, an SVG
  for (const f of ["index.html", "x.js", "fig.svg"]) writeFileSync(path.join(dir, "corrected_paper", f), "<script>alert(5)</script>");
  page.title = `{{CSP}} {{FALLBACK}} ${page.title}`;
  writeJson(file, page);
  const { outDir, index } = site(path.dirname(dir));
  const pages = [index, readFileSync(path.join(outDir, "papers", SLUG, "index.html"), "utf8"), readFileSync(path.join(outDir, "papers", SLUG, "lean", "index.html"), "utf8")];
  for (const html of pages) {
    assert.ok(!/<script>alert/u.test(html), "a script of the bundle reached a page");
    assert.ok(!/<img/u.test(html), "a tag of the bundle reached a page");
  }
  assert.ok(index.includes("Title &lt;script&gt;alert(1)&lt;/script&gt;&quot;&gt;&lt;img src=x onerror=alert(2)&gt;"));
  for (const f of ["index.html", "x.js", "fig.svg"]) assert.ok(!existsSync(path.join(outDir, "papers", SLUG, "corrected_paper", f)), `${f} was copied`);
  // the template's fields are filled in one pass: a field's text is never read as another field
  assert.ok(pages[1].includes("{{CSP}} {{FALLBACK}} Title"), "the title is written as it reads");
  assert.ok(index.includes("Summary &lt;script&gt;"));
  assert.ok(index.includes("<li>Theorem &lt;script&gt;"));
  assert.ok(index.includes("stat.ML &lt;script&gt;") && index.includes(">Subject<"));
  assert.ok(!index.includes("arXiv:") && !index.includes("by @") && !index.includes('class="seal"'), "malformed id, login and code are left out");
  assert.ok(!index.includes("Corrected PDF"));
  assert.equal(esc(`<a b="c" d='e'>&`), "&lt;a b=&quot;c&quot; d=&#39;e&#39;&gt;&amp;");
  assert.equal(plain("A \\emph{simple} bound \\label{x}for $n$~points"), "A simple bound for n points");
});

test("the other outcomes: no error found, a refuted result, an arXiv id", () => {
  const dir = copyFixture();
  const file = path.join(dir, "page", "page.json");
  const page = readJson(file);
  const errors = page.results.filter((r) => r.state === "error");
  errors[0].repair = "none";
  errors[0].proved = false;
  writeJson(file, page);
  writeJson(path.join(dir, "f4_seal.json"), { ...readJson(path.join(dir, "f4_seal.json")), arxiv: "2105.15197" });
  const clean = copyFixture("clean_paper", path.dirname(dir));
  const cleanPage = readJson(path.join(clean, "page", "page.json"));
  for (const r of cleanPage.results) Object.assign(r, { state: "ok", repair: null, paperError: null });
  writeJson(path.join(clean, "page", "page.json"), { ...cleanPage, slug: "clean_paper", title: "A clean paper", tokens: { calls: 412, uncounted: 0, input: 1_180_000_000, cached: 900_000_000, output: 20_500_000, total: 1_200_500_000 } });
  writeJson(path.join(clean, "share.json"), { shared_by: "fixture-user", shared_at: "2026-10-01", arxiv: null });
  const { index, papers } = site(path.dirname(dir));
  assert.deepEqual(papers.map((p) => p.slug), ["clean_paper", SLUG]);
  for (const s of [
    "1 result refuted, no repair keeps it",
    "39 of 41 results proved in Lean 4",
    "21 corrections",
    '<a href="https://arxiv.org/abs/2105.15197">arXiv:2105.15197</a> · shared 2026-10-09 by @fixture-user</',
    "refuted, no repair, not proved in Lean</li>",
    '<span class="badge grey">No error found</span>',
    'data-flags="clean cited"',
    // the run's token total, when the bundle records it (the fixture paper's does not: no badge)
    '1,200,500,000 tokens in 412 model calls, as the run\'s own ledger counted them">1.2B tokens</span>',
  ]) assert.ok(index.includes(s), `the index lacks: ${s}`);
  // newest first: the featured entry is the fixture, then the clean paper
  assert.ok(index.indexOf("A Simple and General") < index.indexOf("A clean paper"));
  assert.equal(index.match(/class="paper featured"/gu).length, 1);
  assert.equal(index.match(/ tokens<\/span>/gu).length, 1);
});

test("an empty registry, and a folder that is no bundle", () => {
  const papersDir = path.join(tmp(), "papers");
  assert.ok(site(papersDir).index.includes("No paper has been shared yet."));
  const dir = copyFixture();
  writeFileSync(path.join(dir, "page", "page.json"), "{ not json");
  const { papers, outDir } = site(path.dirname(dir));
  assert.equal(papers.length, 0);
  assert.ok(!existsSync(path.join(outDir, "papers", SLUG)));
});

test("only a file of a type no browser runs is copied into the site; the page builds without the rest", () => {
  const dir = copyFixture();
  const refused = ["x.shtml", "y.xsl", "z.xsd", "w.rng", "m.mml", "e.ecma", "F.SVG", "P.Html", "q.out"];
  const kept = ["a.tex", "b.bib", "c.bbl", "d.sty", "e.cls", "f.bst", "fig.PNG", "g.jpg", "h.pdf", "notes.md", "i.txt", "j.json", "LICENSE"];
  for (const f of [...refused, ...kept]) writeFileSync(path.join(dir, "corrected_paper", f), "<script>alert(1)</script>");
  writeFileSync(path.join(dir, "lean", "lean-toolchain"), "leanprover/lean4:v4.33.0\n");
  const { outDir, papers } = site(path.dirname(dir));
  assert.equal(papers.length, 1);
  const at = (f) => path.join(outDir, "papers", SLUG, "corrected_paper", f);
  for (const f of refused) assert.ok(!existsSync(at(f)), `${f} was copied`);
  for (const f of kept) assert.ok(existsSync(at(f)), `${f} was not copied`);
  assert.ok(existsSync(path.join(outDir, "papers", SLUG, "lean", "lean-toolchain")));
  assert.ok(existsSync(path.join(outDir, "papers", SLUG, "index.html")));
});

test("a slug of up to 80 characters, as the check allows, is on the site", () => {
  const long = `p${"a".repeat(79)}`;
  const dir = copyFixture(long);
  const page = readJson(path.join(dir, "page", "page.json"));
  writeJson(path.join(dir, "page", "page.json"), { ...page, slug: long });
  const { papers, outDir } = site(path.dirname(dir));
  assert.equal(papers.length, 1);
  assert.ok(existsSync(path.join(outDir, "papers", long, "index.html")));
});
