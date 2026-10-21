/**
 * PaperFormalizer share worker — the one server-side piece of sharing a paper.
 *
 * A sharer's PaperFormalizer uploads a finished run's bundle here; the sharer then
 * signs in with GitHub in their browser, sees what is about to be published under
 * their name, and confirms. The worker dispatches the registry's ingest workflow,
 * which reads the bundle back from here, checks it and adds it to the registry
 * (or opens a pull request for the owner's review), and reports the outcome back.
 *
 * Sign-in proves identity and nothing else: the sign-in app is a CLASSIC OAuth App
 * authorized with no `scope`, so its consent screen says "public data only". A
 * GitHub App would show "Act on your behalf" whatever its permissions. The token is
 * used once, to ask GitHub `/user` who it belongs to, and revoked at once; the
 * worker keeps a signed session cookie of {login, numeric id} for an hour.
 *
 * Nothing here writes to GitHub on the sharer's behalf: the registry is touched only
 * by its own workflow, triggered with the owner's dispatch token.
 *
 * Bindings and settings (wrangler.toml):
 *   SHARES                 R2 bucket: meta/<id>.json and bundles/<id>.tar.gz
 *   UPLOAD_RATELIMIT       per-IP limit on POST /api/uploads      (optional)
 *   LOGIN_RATELIMIT        per-IP limit on /claim and /auth/*     (optional)
 *   GITHUB_CLIENT_ID       the classic OAuth App's client id      (var)
 *   REGISTRY               owner/repo of the registry             (var)
 *   SITE_URL, WORKER_URL   public addresses, each ending in "/"   (vars)
 *   GITHUB_CLIENT_SECRET   the OAuth App's secret                 (secret)
 *   GITHUB_DISPATCH_TOKEN  fine-grained PAT, Contents RW on the registry only (secret)
 *   SESSION_SECRET         HMAC key of state, session and CSRF    (secret)
 *   INGEST_SECRET          bearer the ingest workflow presents    (secret)
 */

const MiB = 1024 * 1024;
export const LIMITS = {
  files: 3000,
  totalBytes: 60 * MiB,
  fileBytes: 24 * MiB,
  archiveBytes: 64 * MiB,
  title: 300,
  authors: 1000,
  arxiv: 64,
  pathBytes: 255,
};
const SLUG_RE = /^[a-z0-9][a-z0-9_-]{0,79}$/;
const HEX64_RE = /^[0-9a-f]{64}$/;
const ID_RE = /^[a-z2-7]{26}$/;
const UPLOAD_TTL_MS = 60 * 60 * 1000;
const SESSION_TTL_MS = 60 * 60 * 1000;
const STATE_TTL_MS = 10 * 60 * 1000;
const CHECK_ALPHABET = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789"; // no O, I, 1, 0
const STATUSES = ["awaiting_upload", "awaiting_sign_in", "submitted", "published", "review", "refused", "expired"];
const RESULT_KINDS = ["published", "review", "refused"];
const UA = "paperformalizer-share-worker";
const MANIFEST_BYTES = 2 * MiB;

export default {
  async fetch(request, env) {
    try {
      return await route(request, env);
    } catch (err) {
      console.error("unhandled", err && err.stack ? err.stack : String(err));
      return json({ error: "internal error" }, 500);
    }
  },
};

async function route(request, env) {
  const url = new URL(request.url);
  const p = url.pathname;
  const m = request.method;
  let r;
  if (p === "/api/uploads" && m === "POST") return createUpload(request, env);
  if ((r = /^\/api\/uploads\/([^/]+)$/.exec(p))) {
    if (m === "PUT") return putArchive(request, env, r[1]);
    if (m === "GET") return poll(request, env, r[1]);
    return json({ error: "method not allowed" }, 405);
  }
  if ((r = /^\/api\/ingest\/([^/]+)(\/archive|\/result)?$/.exec(p))) {
    if (!(await ingestAuthorized(request, env))) return json({ error: "unauthorized" }, 401);
    if (!r[2] && m === "GET") return ingestMeta(env, r[1]);
    if (r[2] === "/archive" && m === "GET") return ingestArchive(env, r[1]);
    if (r[2] === "/result" && m === "POST") return ingestResult(request, env, r[1]);
    return json({ error: "method not allowed" }, 405);
  }
  if ((r = /^\/claim\/([^/]+)$/.exec(p))) {
    const limited = await rateLimited(env.LOGIN_RATELIMIT, request);
    if (limited) return limited;
    if (m === "GET") return claimPage(request, env, r[1]);
    if (m === "POST") return claimSubmit(request, env, r[1]);
    return json({ error: "method not allowed" }, 405);
  }
  if (p === "/auth/callback" && m === "GET") {
    const limited = await rateLimited(env.LOGIN_RATELIMIT, request);
    if (limited) return limited;
    return callback(request, env, url);
  }
  if (p === "/auth/logout" && m === "GET") return logout(url);
  if (p === "/" && m === "GET") return html("PaperFormalizer share", `<p>This address receives papers shared from PaperFormalizer. The shared papers are at <a href="${esc(env.SITE_URL)}">${esc(env.SITE_URL)}</a>.</p>`);
  return json({ error: "not found" }, 404);
}

/* ── the manifest ─────────────────────────────────────────────────────── */

const utf8 = new TextEncoder();

function pathProblem(p) {
  if (typeof p !== "string" || !p) return "an empty path";
  if (utf8.encode(p).length > LIMITS.pathBytes) return `${p}: longer than ${LIMITS.pathBytes} bytes`;
  if (p.startsWith("/") || p.includes("\\")) return `${p}: not a relative POSIX path`;
  // eslint-disable-next-line no-control-regex
  if (/[\u0000-\u001f\u007f]/.test(p)) return `${p}: a control character`;
  for (const seg of p.split("/")) {
    if (!seg || seg === "." || seg === ".." || seg.startsWith(".")) return `${p}: an empty, dot or dotfile segment`;
  }
  return null;
}

/** The manifest's problems, one string each (empty: it is well-formed and within the limits). */
export function manifestProblems(mf) {
  const out = [];
  if (!mf || typeof mf !== "object" || Array.isArray(mf)) return ["the manifest is not an object"];
  if (mf.v !== 1) out.push("v must be 1");
  if (typeof mf.slug !== "string" || !SLUG_RE.test(mf.slug)) out.push("slug must match ^[a-z0-9][a-z0-9_-]{0,79}$");
  if (typeof mf.title !== "string" || mf.title.length > LIMITS.title) out.push(`title must be a string of at most ${LIMITS.title} characters`);
  else if (/\p{Cc}/u.test(mf.title)) out.push("title must hold no control character (a line break included)");
  if (typeof mf.authors !== "string" || mf.authors.length > LIMITS.authors) out.push(`authors must be a string of at most ${LIMITS.authors} characters`);
  else if (/\p{Cc}/u.test(mf.authors)) out.push("authors must hold no control character (a line break included)");
  if (!(mf.arxiv === null || (typeof mf.arxiv === "string" && mf.arxiv.length <= LIMITS.arxiv))) out.push("arxiv must be null or a short string");
  const a = mf.archive;
  if (!a || typeof a !== "object" || !Number.isSafeInteger(a.size) || a.size <= 0 || a.size > LIMITS.archiveBytes || typeof a.sha256 !== "string" || !HEX64_RE.test(a.sha256)) {
    out.push(`archive must be {size: 1..${LIMITS.archiveBytes}, sha256: 64 hex}`);
  }
  if (!Array.isArray(mf.files) || mf.files.length === 0) {
    out.push("files must be a non-empty list");
    return out;
  }
  if (mf.files.length > LIMITS.files) out.push(`${mf.files.length} files, over the limit of ${LIMITS.files}`);
  let total = 0;
  let prev = null;
  for (const f of mf.files.slice(0, LIMITS.files + 1)) {
    if (!f || typeof f !== "object") { out.push("a file entry is not an object"); continue; }
    const pp = pathProblem(f.path);
    if (pp) out.push(pp);
    if (!Number.isSafeInteger(f.size) || f.size < 0) out.push(`${f.path}: size is not a non-negative integer`);
    else if (f.size > LIMITS.fileBytes) out.push(`${f.path}: ${f.size} bytes, over the limit of ${LIMITS.fileBytes} for one file`);
    else total += f.size;
    if (typeof f.sha256 !== "string" || !HEX64_RE.test(f.sha256)) out.push(`${f.path}: sha256 is not 64 hex digits`);
    if (prev !== null && typeof f.path === "string" && !(prev < f.path)) out.push(`${f.path}: files are not sorted by path without repeats`);
    prev = typeof f.path === "string" ? f.path : prev;
    if (out.length > 50) break;
  }
  if (total > LIMITS.totalBytes) out.push(`the files hold ${total} bytes, over the limit of ${LIMITS.totalBytes}`);
  return out;
}

/* ── storage ──────────────────────────────────────────────────────────── */

const metaKey = (id) => `meta/${id}.json`;
const archiveKey = (id) => `bundles/${id}.tar.gz`;

async function readMeta(env, id) {
  if (!ID_RE.test(id)) return null;
  const obj = await env.SHARES.get(metaKey(id));
  if (!obj) return null;
  const meta = JSON.parse(await obj.text());
  // the version read, for a write that must not overwrite another one (`writeMeta`'s `ifEtag`)
  Object.defineProperty(meta, "etag", { value: obj.etag, enumerable: false, writable: true });
  // an upload nobody signed in for within the hour has expired
  if ((meta.status === "awaiting_upload" || meta.status === "awaiting_sign_in") && Date.now() > Date.parse(meta.expires_at)) {
    meta.status = "expired";
  }
  return meta;
}

/** Writes `meta`; with `ifEtag`, only over that version (null when another write came first). */
async function writeMeta(env, meta, ifEtag) {
  const put = await env.SHARES.put(metaKey(meta.id), JSON.stringify(meta), { httpMetadata: { contentType: "application/json" }, ...(ifEtag ? { onlyIf: { etagMatches: ifEtag } } : {}) });
  if (put) Object.defineProperty(meta, "etag", { value: put.etag, enumerable: false, writable: true });
  return put;
}

/* ── the sharer's tool ────────────────────────────────────────────────── */

async function createUpload(request, env) {
  const limited = await rateLimited(env.UPLOAD_RATELIMIT, request);
  if (limited) return limited;
  const len = Number(request.headers.get("Content-Length") || "0");
  if (len > MANIFEST_BYTES) return json({ error: "the manifest is too large" }, 413);
  const text = await readCapped(request, MANIFEST_BYTES);
  if (text === null) return json({ error: "the manifest is too large" }, 413);
  let mf;
  try {
    mf = JSON.parse(text);
  } catch {
    return json({ error: "the manifest is not JSON" }, 400);
  }
  const problems = manifestProblems(mf);
  if (problems.length) return json({ error: "the manifest is refused", problems }, 400);
  const manifest = {
    v: 1, slug: mf.slug, title: mf.title, authors: mf.authors, arxiv: mf.arxiv,
    files: mf.files.map((f) => ({ path: f.path, size: f.size, sha256: f.sha256 })),
    archive: { size: mf.archive.size, sha256: mf.archive.sha256 },
  };
  const id = randomId();
  const pollToken = b64url(randomBytes(32));
  const now = Date.now();
  const meta = {
    id, status: "awaiting_upload", manifest,
    poll_hash: await sha256Hex(pollToken),
    check_code: checkCode(),
    created_at: new Date(now).toISOString(),
    expires_at: new Date(now + UPLOAD_TTL_MS).toISOString(),
    identity: null, submitted_at: null, result: null,
  };
  await writeMeta(env, meta);
  const base = workerBase(env, request);
  return json({
    id,
    upload_url: `${base}api/uploads/${id}`,
    claim_url: `${base}claim/${id}`,
    poll_token: pollToken,
    check_code: meta.check_code,
    expires_at: meta.expires_at,
  }, 201);
}

/** The request's body as text, read no further than `max` bytes; null past that (a chunked body
 *  carries no Content-Length to refuse it by). */
async function readCapped(request, max) {
  if (!request.body) return "";
  const reader = request.body.getReader();
  const parts = [];
  let n = 0;
  for (;;) {
    const { done, value } = await reader.read();
    if (done) break;
    n += value.byteLength;
    if (n > max) { await reader.cancel().catch(() => {}); return null; }
    parts.push(value);
  }
  const all = new Uint8Array(n);
  let at = 0;
  for (const p of parts) { all.set(p, at); at += p.byteLength; }
  return new TextDecoder().decode(all);
}

async function pollAuthorized(request, meta) {
  const token = bearer(request);
  return Boolean(token) && meta && timingSafeEqualStr(await sha256Hex(token), meta.poll_hash);
}

async function putArchive(request, env, id) {
  const limited = await rateLimited(env.UPLOAD_RATELIMIT, request);
  if (limited) return limited;
  const meta = await readMeta(env, id);
  if (!meta || !(await pollAuthorized(request, meta))) return json({ error: "unknown upload or wrong token" }, 404);
  if (meta.status !== "awaiting_upload") return json({ error: `the upload is ${meta.status}`, status: meta.status }, 409);
  // one attempt: an archive that is not the manifest's ends the upload (no retrying 64 MB bodies)
  const fail = async (error) => {
    meta.status = "refused";
    meta.result = { kind: "refused", problems: ["the archive did not match its manifest"] };
    await writeMeta(env, meta);
    return json({ error, status: meta.status }, 400);
  };
  const len = request.headers.get("Content-Length");
  if (len === null || Number(len) !== meta.manifest.archive.size) return fail(`Content-Length must be ${meta.manifest.archive.size}`);
  if (!request.body) return fail("no body");
  try {
    // R2 checks the sha256 itself: no hashing (CPU) here
    await env.SHARES.put(archiveKey(id), request.body, { sha256: meta.manifest.archive.sha256, httpMetadata: { contentType: "application/gzip" } });
  } catch (err) {
    console.error("archive put failed", String(err));
    return fail("the archive does not match the manifest's size and sha256");
  }
  meta.status = "awaiting_sign_in";
  await writeMeta(env, meta);
  return json({ status: meta.status });
}

async function poll(request, env, id) {
  const meta = await readMeta(env, id);
  if (!meta || !(await pollAuthorized(request, meta))) return json({ error: "unknown upload or wrong token" }, 404);
  const out = { status: meta.status, check_code: meta.check_code };
  if (meta.identity) out.login = meta.identity.login;
  if (meta.result) out.result = meta.result;
  return json(out);
}

/* ── the sharer's browser ─────────────────────────────────────────────── */

async function claimPage(request, env, id) {
  const meta = await readMeta(env, id);
  if (!meta) return html("Unknown share", "<p>No share has this address. It may have expired; start the share again from your PaperFormalizer page.</p>", 404);
  const session = await readSession(request, env);
  if (!session) return startSignIn(env, request, id);
  return claimView(env, request, meta, session);
}

async function claimView(env, request, meta, session, note = "") {
  const mf = meta.manifest;
  const base = workerBase(env, request);
  const paperUrl = `${env.SITE_URL}papers/${mf.slug}/`;
  const who = `<p class="who">Signed in as <b>@${esc(session.login)}</b> · <a href="${esc(`${base}auth/logout?to=/claim/${meta.id}`)}">not you? sign out</a> (to switch accounts, sign out of <a href="https://github.com/logout">github.com</a> too: GitHub signs you in again as the same account otherwise)</p>`;
  const facts = `<table>
<tr><th>Title</th><td>${esc(mf.title) || "<i>untitled</i>"}</td></tr>
<tr><th>Authors</th><td>${esc(mf.authors)}</td></tr>
<tr><th>Paper</th><td><code>${esc(mf.slug)}</code>${mf.arxiv ? ` · arXiv ${esc(mf.arxiv)}` : ""}</td></tr>
<tr><th>Bundle</th><td>${mf.files.length} files, ${esc(sizeText(mf.files.reduce((s, f) => s + f.size, 0)))}</td></tr>
<tr><th>Check code</th><td><b class="code">${esc(meta.check_code)}</b></td></tr>
</table>`;
  if (meta.status !== "awaiting_sign_in") {
    return html("Share", `${note ? `<p class="warn">${esc(note)}</p>` : ""}${who}${facts}${statusText(meta, paperUrl)}`);
  }
  const csrf = await csrfToken(env, session, meta.id);
  const body = `${note ? `<p class="warn">${esc(note)}</p>` : ""}${who}${facts}
<div class="warn"><p><b>Sharing publishes this paper.</b> The corrected paper's TeX source and PDF, its Lean code, the report and the page are made public at <a href="${esc(paperUrl)}">${esc(paperUrl)}</a>, under your GitHub name <b>@${esc(session.login)}</b>.</p>
<p>Continue only if you started this share yourself, on your own PaperFormalizer page, and the check code there reads <b class="code">${esc(meta.check_code)}</b>.</p></div>
<form method="post" action="/claim/${esc(meta.id)}"><input type="hidden" name="csrf" value="${esc(csrf)}"><button type="submit">Share publicly as @${esc(session.login)}</button></form>`;
  return html("Share this paper?", body);
}

function statusText(meta, paperUrl) {
  const r = meta.result || {};
  switch (meta.status) {
    case "awaiting_upload": return "<p>The upload has not finished yet. Wait for your PaperFormalizer page to finish sending, then reload this page.</p>";
    case "submitted": return "<p><b>Submitted.</b> The registry is checking the bundle now. You can close this tab; your PaperFormalizer page shows the result.</p>";
    case "published": return `<p><b>Published</b> at <a href="${esc(r.url || paperUrl)}">${esc(r.url || paperUrl)}</a>.</p>`;
    case "review": return `<p><b>Checked, waiting for the owner's review.</b>${r.pr_url ? ` The pull request: <a href="${esc(r.pr_url)}">${esc(r.pr_url)}</a>.` : ""}</p>`;
    case "refused": return `<p><b>Refused</b> by the registry's checks:</p><ul>${(r.problems || []).map((x) => `<li>${esc(x)}</li>`).join("")}</ul>`;
    case "expired": return "<p>This share has expired (an upload waits an hour for sign-in). Start the share again from your PaperFormalizer page.</p>";
    default: return `<p>Status: ${esc(meta.status)}.</p>`;
  }
}

async function startSignIn(env, request, id) {
  const nonce = b64url(randomBytes(24));
  const state = await sign(env, { k: "state", id, nonce, exp: Date.now() + STATE_TTL_MS });
  const auth = new URL("https://github.com/login/oauth/authorize");
  auth.searchParams.set("client_id", env.GITHUB_CLIENT_ID);
  auth.searchParams.set("redirect_uri", `${workerBase(env, request)}auth/callback`);
  // No `scope`: a classic OAuth App with an empty scope reads public data only, and
  // its consent screen says so — no "act on your behalf".
  auth.searchParams.set("state", state);
  const h = new Headers({ Location: auth.toString(), "Cache-Control": "no-store" });
  h.append("Set-Cookie", `tc_oauth=${nonce}; HttpOnly; Secure; SameSite=Lax; Max-Age=600; Path=/auth`);
  return new Response(null, { status: 302, headers: h });
}

async function callback(request, env, url) {
  const code = url.searchParams.get("code") || "";
  const state = await verify(env, url.searchParams.get("state") || "");
  const nonce = cookie(request, "tc_oauth");
  if (!state || state.k !== "state" || !(state.exp > Date.now()) || !ID_RE.test(String(state.id))) {
    return html("Sign-in failed", "<p>The sign-in link is invalid or has expired. Go back to your PaperFormalizer page and open the share link again.</p>", 400);
  }
  if (!nonce || !timingSafeEqualStr(nonce, String(state.nonce))) {
    return html("Sign-in failed", "<p>This sign-in was not started in this browser. Open the share link again.</p>", 400);
  }
  if (!code) return html("Sign-in failed", "<p>GitHub did not return a sign-in code (was the sign-in cancelled?). Open the share link again.</p>", 400);
  const res = await fetch("https://github.com/login/oauth/access_token", {
    method: "POST",
    headers: { "Content-Type": "application/json", Accept: "application/json", "User-Agent": UA },
    body: JSON.stringify({ client_id: env.GITHUB_CLIENT_ID, client_secret: env.GITHUB_CLIENT_SECRET, code, redirect_uri: `${workerBase(env, request)}auth/callback` }),
  });
  const data = await res.json().catch(() => ({}));
  const token = typeof data.access_token === "string" ? data.access_token : "";
  if (!token) {
    console.error("oauth exchange failed", JSON.stringify({ status: res.status, error: data.error, description: data.error_description }));
    return html("Sign-in failed", `<p>GitHub refused the sign-in: ${esc(String(data.error_description || data.error || `HTTP ${res.status}`))}. Open the share link again.</p>`, 502);
  }
  let user = null;
  try {
    user = await githubUser(token);
  } catch (err) {
    console.error("github user failed", String(err));
  } finally {
    await revokeToken(env, token);
  }
  if (!user) return html("Sign-in failed", "<p>GitHub did not say who signed in. Open the share link again.</p>", 502);
  const session = await sign(env, { k: "session", sid: b64url(randomBytes(16)), login: user.login, id: user.id, exp: Date.now() + SESSION_TTL_MS });
  const h = new Headers({ Location: `${workerBase(env, request)}claim/${state.id}`, "Cache-Control": "no-store" });
  h.append("Set-Cookie", `tc_session=${session}; HttpOnly; Secure; SameSite=Lax; Max-Age=3600; Path=/`);
  h.append("Set-Cookie", "tc_oauth=; HttpOnly; Secure; SameSite=Lax; Max-Age=0; Path=/auth");
  return new Response(null, { status: 302, headers: h });
}

async function githubUser(token) {
  const res = await fetch("https://api.github.com/user", {
    headers: { Authorization: `Bearer ${token}`, Accept: "application/vnd.github+json", "User-Agent": UA },
  });
  if (!res.ok) return null;
  const data = await res.json().catch(() => ({}));
  // the numeric id is required: a login is reassignable once an account is renamed
  if (!data || typeof data.login !== "string" || !data.login || !Number.isSafeInteger(data.id) || data.id <= 0) return null;
  return { login: data.login, id: data.id };
}

/** The token served its one purpose: revoke it, so none lingers anywhere. */
async function revokeToken(env, token) {
  try {
    const res = await fetch(`https://api.github.com/applications/${encodeURIComponent(env.GITHUB_CLIENT_ID)}/token`, {
      method: "DELETE",
      headers: { Authorization: `Basic ${btoa(`${env.GITHUB_CLIENT_ID}:${env.GITHUB_CLIENT_SECRET}`)}`, Accept: "application/vnd.github+json", "Content-Type": "application/json", "User-Agent": UA },
      body: JSON.stringify({ access_token: token }),
    });
    if (!res.ok && res.status !== 404) console.error("token revoke failed", res.status);
  } catch (err) {
    console.error("token revoke failed", String(err));
  }
}

async function claimSubmit(request, env, id) {
  const meta = await readMeta(env, id);
  if (!meta) return html("Unknown share", "<p>No share has this address.</p>", 404);
  const session = await readSession(request, env);
  if (!session) return html("Signed out", `<p>Your sign-in has expired. <a href="/claim/${esc(id)}">Sign in again</a>.</p>`, 401);
  let form;
  try { form = await request.formData(); } catch { form = null; }
  const csrf = form ? String(form.get("csrf") || "") : "";
  if (!timingSafeEqualStr(csrf, await csrfToken(env, session, id))) {
    return html("Not confirmed", `<p>This confirmation did not come from the share page. <a href="/claim/${esc(id)}">Open it again</a>.</p>`, 403);
  }
  if (meta.status !== "awaiting_sign_in") return claimView(env, request, meta, session);
  // recorded first, over the version read: a second confirmation (another tab, another account) loses
  // the race and is told so; the ingest the dispatch starts finds the share submitted
  const read = meta.etag;
  meta.identity = { login: session.login, id: session.id };
  meta.status = "submitted";
  meta.submitted_at = new Date().toISOString();
  if (!(await writeMeta(env, meta, read))) {
    const now = await readMeta(env, id);
    return now ? claimView(env, request, now, session, "This share was already confirmed.") : html("Unknown share", "<p>No share has this address.</p>", 404);
  }
  const res = await fetch(`https://api.github.com/repos/${env.REGISTRY}/dispatches`, {
    method: "POST",
    headers: { Authorization: `Bearer ${env.GITHUB_DISPATCH_TOKEN}`, Accept: "application/vnd.github+json", "Content-Type": "application/json", "User-Agent": UA, "X-GitHub-Api-Version": "2022-11-28" },
    body: JSON.stringify({ event_type: "share", client_payload: { id } }),
  }).catch((err) => { console.error("dispatch failed", String(err)); return null; });
  if (!res || !res.ok) {
    if (res) console.error("dispatch failed", res.status);
    meta.identity = null;
    meta.status = "awaiting_sign_in";
    meta.submitted_at = null;
    await writeMeta(env, meta, meta.etag);
    return claimView(env, request, meta, session, "The registry could not be reached. Nothing was shared; try again in a minute.");
  }
  return claimView(env, request, meta, session);
}

function logout(url) {
  const to = url.searchParams.get("to") || "/";
  const safe = /^\/(?![/\\])[A-Za-z0-9_\-/]*$/.test(to) ? to : "/";
  const h = new Headers({ Location: safe, "Cache-Control": "no-store" });
  h.append("Set-Cookie", "tc_session=; HttpOnly; Secure; SameSite=Lax; Max-Age=0; Path=/");
  return new Response(null, { status: 302, headers: h });
}

/* ── the ingest workflow ──────────────────────────────────────────────── */

async function ingestAuthorized(request, env) {
  const token = bearer(request);
  return Boolean(token) && Boolean(env.INGEST_SECRET) && timingSafeEqualStr(await sha256Hex(token), await sha256Hex(env.INGEST_SECRET));
}

async function ingestMeta(env, id) {
  const meta = await readMeta(env, id);
  if (!meta) return json({ error: "unknown upload" }, 404);
  return json({ id: meta.id, status: meta.status, manifest: meta.manifest, identity: meta.identity, created_at: meta.created_at, submitted_at: meta.submitted_at });
}

async function ingestArchive(env, id) {
  const meta = await readMeta(env, id);
  if (!meta) return json({ error: "unknown upload" }, 404);
  const obj = await env.SHARES.get(archiveKey(id));
  if (!obj) return json({ error: "no archive" }, 404);
  return new Response(obj.body, { headers: { "Content-Type": "application/gzip", "Cache-Control": "no-store" } });
}

async function ingestResult(request, env, id) {
  const meta = await readMeta(env, id);
  if (!meta) return json({ error: "unknown upload" }, 404);
  if (meta.status !== "submitted") return json({ error: `the upload is ${meta.status}`, status: meta.status }, 409);
  let body;
  try { body = await request.json(); } catch { return json({ error: "not JSON" }, 400); }
  const problems = [];
  if (!body || !RESULT_KINDS.includes(body.kind)) problems.push(`kind must be one of ${RESULT_KINDS.join(", ")}`);
  const httpsUrl = (v) => v === undefined || (typeof v === "string" && v.length <= 2000 && /^https:\/\/[^\s"'<>]+$/.test(v));
  if (body && !httpsUrl(body.url)) problems.push("url must be an https address");
  if (body && !httpsUrl(body.pr_url)) problems.push("pr_url must be an https address");
  if (body && body.problems !== undefined && !(Array.isArray(body.problems) && body.problems.length <= 200 && body.problems.every((x) => typeof x === "string" && x.length <= 2000))) {
    problems.push("problems must be a list of at most 200 strings");
  }
  if (problems.length) return json({ error: "the result is refused", problems }, 400);
  meta.result = { kind: body.kind };
  for (const k of ["url", "pr_url", "problems"]) if (body[k] !== undefined) meta.result[k] = body[k];
  meta.status = body.kind;
  await writeMeta(env, meta);
  await env.SHARES.delete(archiveKey(id));
  return json({ status: meta.status });
}

/* ── signing, cookies, helpers ────────────────────────────────────────── */

async function hmacKey(env) {
  if (!env.SESSION_SECRET) throw new Error("SESSION_SECRET is not set");
  return crypto.subtle.importKey("raw", utf8.encode(env.SESSION_SECRET), { name: "HMAC", hash: "SHA-256" }, false, ["sign"]);
}

async function hmac(env, text) {
  return b64url(new Uint8Array(await crypto.subtle.sign("HMAC", await hmacKey(env), utf8.encode(text))));
}

/** `payload.signature`, both base64url: a value only this worker can have written. */
async function sign(env, obj) {
  const payload = b64url(utf8.encode(JSON.stringify(obj)));
  return `${payload}.${await hmac(env, `v1|${payload}`)}`;
}

async function verify(env, token) {
  const dot = token.indexOf(".");
  if (dot <= 0 || token.length > 4096) return null;
  const payload = token.slice(0, dot);
  if (!timingSafeEqualStr(token.slice(dot + 1), await hmac(env, `v1|${payload}`))) return null;
  try { return JSON.parse(new TextDecoder().decode(unb64url(payload))); } catch { return null; }
}

async function readSession(request, env) {
  const v = cookie(request, "tc_session");
  if (!v) return null;
  const s = await verify(env, v);
  if (!s || s.k !== "session" || !(s.exp > Date.now()) || typeof s.login !== "string" || !Number.isSafeInteger(s.id)) return null;
  return s;
}

const csrfToken = (env, session, id) => hmac(env, `csrf|${session.sid}|${id}`);

function cookie(request, name) {
  for (const part of (request.headers.get("Cookie") || "").split(";")) {
    const i = part.indexOf("=");
    if (i > 0 && part.slice(0, i).trim() === name) return part.slice(i + 1).trim();
  }
  return "";
}

function bearer(request) {
  // RFC 6750 b64token: a base64 secret (+, /, =) is a token too
  const m = /^Bearer\s+([A-Za-z0-9\-._~+/]+=*)$/.exec((request.headers.get("Authorization") || "").trim());
  return m ? m[1] : "";
}

function timingSafeEqualStr(a, b) {
  const x = utf8.encode(String(a));
  const y = utf8.encode(String(b));
  let diff = x.length ^ y.length;
  for (let i = 0; i < Math.max(x.length, y.length); i++) diff |= (x[i] ?? 0) ^ (y[i] ?? 0);
  return diff === 0;
}

async function sha256Hex(text) {
  const d = new Uint8Array(await crypto.subtle.digest("SHA-256", utf8.encode(text)));
  return [...d].map((b) => b.toString(16).padStart(2, "0")).join("");
}

const randomBytes = (n) => crypto.getRandomValues(new Uint8Array(n));

/** 26 lowercase base32 characters: 128 random bits (130, the top two zero). */
function randomId() {
  const alphabet = "abcdefghijklmnopqrstuvwxyz234567";
  const bytes = randomBytes(17);
  let bits = 0n;
  for (const b of bytes.slice(0, 16)) bits = (bits << 8n) | BigInt(b);
  let out = "";
  for (let i = 0; i < 26; i++) { out = alphabet[Number(bits & 31n)] + out; bits >>= 5n; }
  return out;
}

function checkCode() {
  let out = "";
  for (const b of randomBytes(4)) out += CHECK_ALPHABET[b % CHECK_ALPHABET.length]; // 32 divides 256: unbiased
  return out;
}

function b64url(bytes) {
  let s = "";
  for (const b of bytes) s += String.fromCharCode(b);
  return btoa(s).replace(/\+/g, "-").replace(/\//g, "_").replace(/=+$/, "");
}

function unb64url(s) {
  const bin = atob(s.replace(/-/g, "+").replace(/_/g, "/") + "===".slice((s.length + 3) % 4));
  return Uint8Array.from(bin, (c) => c.charCodeAt(0));
}

function workerBase(env, request) {
  const b = env.WORKER_URL || `${new URL(request.url).origin}/`;
  return b.endsWith("/") ? b : `${b}/`;
}

function sizeText(bytes) {
  return bytes >= MiB ? `${(bytes / MiB).toFixed(1)} MB` : `${Math.max(1, Math.round(bytes / 1024))} kB`;
}

export function esc(s) {
  return String(s ?? "").replace(/[&<>"']/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" })[c]);
}

async function rateLimited(binding, request) {
  if (!binding || typeof binding.limit !== "function") return null;
  let ok = true;
  try {
    const res = await binding.limit({ key: request.headers.get("CF-Connecting-IP") || "anon" });
    ok = !res || res.success !== false;
  } catch {
    ok = true; // never let the limiter itself break the endpoint
  }
  return ok ? null : json({ error: "rate limited" }, 429, { "Retry-After": "10" });
}

function json(obj, status = 200, extra = {}) {
  return new Response(JSON.stringify(obj), { status, headers: { "Content-Type": "application/json", "Cache-Control": "no-store", "X-Content-Type-Options": "nosniff", ...extra } });
}

const PAGE_CSS = "body{font-family:system-ui,sans-serif;max-width:40rem;margin:2rem auto;padding:0 1rem;color:#1a1a1a;background:#fdfcfa;line-height:1.5}table{border-collapse:collapse;margin:1rem 0}th{text-align:left;padding:.2rem 1rem .2rem 0;color:#555;font-weight:500}td{padding:.2rem 0}.warn{background:#fff5e6;border:1px solid #f0c27b;border-radius:6px;padding:.5rem 1rem}.code{font-family:ui-monospace,monospace;letter-spacing:.15em}button{font-size:1rem;padding:.6rem 1.2rem;border-radius:6px;border:1px solid #1f6f43;background:#1f7a4a;color:#fff;cursor:pointer}.who{color:#555}@media (prefers-color-scheme:dark){body{background:#1b1b1b;color:#eee}th,.who{color:#aaa}.warn{background:#3a2c14;border-color:#7a5a20}a{color:#8ab4f8}}";

function html(title, body, status = 200) {
  const page = `<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>${esc(title)}</title><style>${PAGE_CSS}</style></head><body><h1>${esc(title)}</h1>${body}<p class="who"><small>PaperFormalizer shared papers</small></p></body></html>`;
  return new Response(page, {
    status,
    headers: {
      "Content-Type": "text/html; charset=utf-8",
      "Cache-Control": "no-store",
      "Content-Security-Policy": "default-src 'none'; style-src 'unsafe-inline'; img-src https://avatars.githubusercontent.com; form-action 'self'; frame-ancestors 'none'; base-uri 'none'",
      "X-Content-Type-Options": "nosniff",
      "Referrer-Policy": "no-referrer",
    },
  });
}

export { STATUSES };
