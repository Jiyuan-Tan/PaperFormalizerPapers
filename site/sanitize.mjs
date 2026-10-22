// Cleans each paper's page.json for the site, once, at build time: what the viewer (app.js, snapshot
// mode) would otherwise do in every reader's browser before drawing the paper. It runs in a headless
// Chromium, with the viewer's own DOMPurify (site/viewer/purify.min.js) and the viewer's strict rules
// (`SNAP.strict` in PaperFormalizer's tools/src/ui/static/app.js, repeated below): the same cleaning,
// in the same kind of browser, as a reader's. The result carries `sanitized: "site"`, and the viewer
// then inserts its paper body without cleaning it again.
//
// Everything in page.json is UNTRUSTED: every paper is cleaned, and a page that cannot be cleaned fails
// the build rather than reach the site uncleaned.
import path from "node:path";
import { chromium } from "playwright-core";

// The viewer's strict cleaning, as app.js sets it up (keep the two the same): tags and attributes
// DOMPurify allows, plus `target`; no form, no style element; an id only in the renderer's schemes;
// no `name`, no `data-copy`; no style that lifts an element out of the text (a position other than
// relative or static, a z-index, an inset) — the browser parses the style.
function strictCleaner() {
  const purify = window.DOMPurify;
  const probe = document.createElement("span");
  purify.addHook("uponSanitizeAttribute", (_node, data) => {
    if (data.attrName === "name" || data.attrName === "data-copy" || (data.attrName === "id" && !/^(?:env|alg|bib|lbl|sec|res|fig|tab)-/.test(data.attrValue))) { data.keepAttr = false; return; }
    if (data.attrName !== "style") return;
    probe.style.cssText = data.attrValue;
    const lifts = !["", "relative", "static"].includes(probe.style.position) || probe.style.zIndex !== "" || probe.style.inset !== "";
    if (!lifts) return;
    if (!["", "relative", "static"].includes(probe.style.position)) probe.style.removeProperty("position");
    probe.style.removeProperty("z-index");
    probe.style.removeProperty("inset");
    data.attrValue = probe.style.cssText;
  });
  window.cleanPage = (p) => {
    const clean = (html) => purify.sanitize(String(html ?? ""), { ADD_ATTR: ["target"], FORBID_TAGS: ["form", "style"] });
    if (p.paper && typeof p.paper === "object") {
      p.paper.html = clean(p.paper.html);
      for (const c of Array.isArray(p.paper.comments) ? p.paper.comments : []) if (c && typeof c === "object") { c.html = clean(c.html); if (c.label != null) c.label = clean(c.label); }
      for (const t of Array.isArray(p.paper.toc) ? p.paper.toc : []) if (t && typeof t === "object") t.html = clean(t.html);
    }
    p.texHtml = Object.fromEntries(Object.entries(p.texHtml && typeof p.texHtml === "object" ? p.texHtml : {}).map(([k, v]) => [k, clean(v)]));
    p.sanitized = "site";
    return p;
  };
}

/** A cleaner for page.json objects: `clean(page)` → the page cleaned, marked `sanitized: "site"`;
 *  `close()` when done. `viewerDir`: the viewer, for its DOMPurify. Chromium is Playwright's, or the
 *  executable named by CHROMIUM_PATH. */
export async function pageCleaner(viewerDir) {
  const browser = await chromium.launch(process.env.CHROMIUM_PATH ? { executablePath: process.env.CHROMIUM_PATH } : {});
  const tab = await browser.newPage();
  await tab.setContent("<!doctype html><html><body></body></html>");
  await tab.addScriptTag({ path: path.join(viewerDir, "purify.min.js") });
  await tab.evaluate(strictCleaner);
  return {
    clean: (page) => tab.evaluate((p) => window.cleanPage(p), page),
    close: () => browser.close(),
  };
}
