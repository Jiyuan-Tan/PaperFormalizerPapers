import assert from "node:assert/strict";
import { existsSync, readFileSync, writeFileSync } from "node:fs";
import path from "node:path";
import { test } from "node:test";
import { build, esc, plain } from "../site/build.mjs";
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
    'href="papers/cns_simple_dml/REPORT.md">Report',
    "seal e84ecbe79ae9",
    "Findings (22)",
    "<li>Theorem 5.1 — statement corrected, proved in Lean</li>",
    "<li>Corollary B.4 — statement unchanged, proof corrected, proved in Lean</li>",
    'data-flags="repaired cited"',
  ]) assert.ok(index.includes(s), `the index lacks: ${s}`);
  assert.ok(!index.includes("No error found</span>"));
  assert.ok(!index.includes(">Subject<"), "no paper records a subject: no Subject button");
  // the paper's folder is copied, with the placeholder page and the list of the Lean files
  const paper = readFileSync(path.join(outDir, "papers", SLUG, "index.html"), "utf8");
  assert.ok(paper.includes("The interactive page (findings beside the text, Lean statements) is not built yet."));
  for (const s of ['href="REPORT.md"', 'href="MATCH.md"', 'href="corrected_paper/main.pdf"', 'href="lean/"', "40 of 41 results proved in Lean 4"]) assert.ok(paper.includes(s), `the paper page lacks: ${s}`);
  assert.ok(existsSync(path.join(outDir, "papers", SLUG, "f4_seal.json")));
  assert.ok(readFileSync(path.join(outDir, "papers", SLUG, "lean", "index.html"), "utf8").includes('href="Papers/CnsSimpleDml/TVar.lean"'));
  assert.match(readFileSync(path.join(outDir, "_headers"), "utf8"), /^\/papers\/\*\n {2}Content-Security-Policy: default-src 'none'; img-src 'self' data:; style-src 'unsafe-inline'[^;\n]*; font-src [^;\n]*; sandbox\n/u);
  assert.ok(index.includes("A share always carries the whole bundle") && !index.includes("You choose"));
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
  const { outDir, index } = site(path.dirname(dir));
  const pages = [index, readFileSync(path.join(outDir, "papers", SLUG, "index.html"), "utf8"), readFileSync(path.join(outDir, "papers", SLUG, "lean", "index.html"), "utf8")];
  for (const html of pages) {
    assert.ok(!/<script>alert/u.test(html), "a script of the bundle reached a page");
    assert.ok(!/<img/u.test(html), "a tag of the bundle reached a page");
  }
  assert.ok(index.includes("Title &lt;script&gt;alert(1)&lt;/script&gt;&quot;&gt;&lt;img src=x onerror=alert(2)&gt;"));
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
  writeJson(path.join(clean, "page", "page.json"), { ...cleanPage, slug: "clean_paper", title: "A clean paper" });
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
  ]) assert.ok(index.includes(s), `the index lacks: ${s}`);
  // newest first: the featured entry is the fixture, then the clean paper
  assert.ok(index.indexOf("A Simple and General") < index.indexOf("A clean paper"));
  assert.equal(index.match(/class="paper featured"/gu).length, 1);
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
