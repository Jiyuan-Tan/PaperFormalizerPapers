# PaperFormalizer — Shared Papers

The public registry of papers checked by [PaperFormalizer](https://github.com/Jiyuan-Tan/PaperFormalizer),
a tool that referees a paper's statements, repairs the errors it finds and proves the corrected
results in Lean 4. Each paper here is one folder, `papers/<slug>/`, holding the bundle a finished run
wrote. The site is built from those folders.

Nobody clones this repository to share a paper: the tool does it through GitHub.

## How a paper gets in

1. On a finished run, the user presses **Share** on the paper's page (or runs `paperformalizer share`).
2. The tool uploads the bundle to the Worker (`worker/`) and opens its page, where the user signs in
   with GitHub — identity only: the sign-in asks for no permission — and confirms.
3. The Worker sends the repository a `share` event; `.github/workflows/ingest.yml` runs
   `checks/ingest.mjs`, which fetches the upload and checks it (below).
4. If it passes and the sharer is a trusted sharer (below), the paper is committed on `main` and
   `.github/workflows/pages.yml` rebuilds the site; otherwise it is opened as a pull request that
   waits for the owner to merge it. The sharer's tool shows which, or why the paper was refused.

A pull request a person opens by hand is checked by `.github/workflows/check.yml` instead.

## Who can get a paper in

The seal is a checksum, not a signature: everything in it is computed on the sharer's machine, so
any GitHub account can fabricate a bundle that is consistent with its own seal and passes the
check — with content PaperFormalizer never produced. The check keeps a folder well-formed and
harmless to serve; it does not vouch for what the folder says.

So a share is published without the owner only when its sharer is named in the repository
variable `TRUSTED_SHARERS` (Settings → Secrets and variables → Actions → Variables): a
comma-separated list of GitHub logins, or `*` to let every share that passes the check publish
itself. With the variable unset — the default — every share is still checked, and each one that
passes waits, as a pull request, for the owner to read and merge it. The same list decides whether
a hand-opened pull request merges itself.

Prefer a list of logins to `*`. With `*` nothing limits how much one account publishes: no quota
per account, while GitHub Pages refuses a site over 1 GB (each paper is up to 60 MB, and git keeps
the bytes of a removed one in its history).

A pull request the ingest opens (for a sharer not on the list) was opened with the workflow's own
token, so it starts no workflow: `check` does not run on it, and need not — the ingest ran the same
checks before opening it. Read it and merge it yourself. The ingest also refuses a slug another
account's share is already waiting for review under, so two pending pull requests never replace
each other's paper.

Who shared a paper is the GitHub account the Worker saw sign in: the ingest writes its login and
numeric account id into `share.json`. A paper already in the registry is replaced only by the same
account (by id: a login can be renamed and then taken by someone else).

## A paper folder

    papers/<slug>/
      share.json        who shared it and when (written by the ingest)
      bundle.json       what the run wrote and what its own checks found
      f4_seal.json      the seal: the two reviewers' verdicts and the hash of every sealed file
      f4_reviews.log    what the two reviewers answered
      REPORT.md         the report: what was wrong, what was done, what was proved
      MATCH.md          each result beside its Lean declaration
      README.md         the bundle's own note (optional)
      page/page.json    the snapshot the paper's page is drawn from
      lean/             the Lean code, a standalone Lake project
      corrected_paper/  the corrected TeX, its PDF and TODO.md

A share always carries the whole bundle, the corrected paper's TeX source and PDF included. Every
file is stored non-executable (git mode 100644): the ingest writes them so, and the check rejects
an executable file.

`share.json`:

    { "shared_by": "<github login>", "shared_by_id": <numeric account id>,
      "shared_at": "<ISO date>", "arxiv": "<id or null>" }

`shared_by_id` is optional (a paper shared before ids were recorded has none), and so is `subject`
(a short string, e.g. the arXiv subject), which the tool does not write yet.

## What the check verifies

`checks/ingest.mjs` (a share), `checks/check_pr.mjs` (a hand-opened pull request) and
`checks/check_paper.mjs` (the folder, for both), with no model and no Lean:

- a share: the archive is the one the manifest names (size, sha256); it holds regular files only
  (no link, directory, device or pax/GNU header), with paths inside the folder (no absolute path,
  no `..`, no dotfile), exactly the manifest's files with their sizes and hashes, and no
  `share.json`; the upload was confirmed by a signed-in GitHub account (`checks/tar.mjs` reads the
  archive in memory; nothing of it is run);
- a pull request: it adds or changes files under exactly one `papers/<slug>/`, and nothing else;
  `shared_by` (and `shared_by_id`, when there is one) is the pull request's author; in its tree
  every entry of the folder is a plain file of git mode 100644: no submodule, no symbolic link, no
  executable;
- `share.json` is well-formed, and a paper already in the registry is changed only by the account
  that shared it;
- the required files are there and nothing is outside the layout above: no dotfile, no `.html`,
  `.htm`, `.xhtml`, `.xht`, `.xml`, `.js`, `.mjs` or `.svg` file (GitHub Pages sets no header that
  would keep an SVG opened on its own from running its scripts);
- the folder is under 60 MB and 3000 files, and no file is over 24 MB (the static host's per-file
  limit);
- `page/page.json` parses, has `schema` 1 and the folder's slug;
- **the seal holds**: the code in `f4_seal.json` is the hash of the seal's own contents, both
  reviewers passed every statement, and `f4_reviews.log` and every file under `lean/`,
  `corrected_paper/` and `page/` has the hash the seal names — with no file there that the seal does
  not name (the compiled PDF apart, which the tool leaves out of the seal).

The seal check in `checks/seal.mjs` mirrors the tool's `tools/src/verify/f4_seal.ts`. The tool's own
command is the reference:

    paperformalizer seal papers/<slug>

## What the check does NOT prove

The seal is a checksum, not a signature. It shows a bundle is complete and unchanged since it was
written. It does not show who ran the check, or that the check ran at all: everything in the seal is
computed on the machine of the person who shares, and someone determined could compute a seal for
files of their own. Nothing here runs Lean either; to confirm the proofs, build `lean/` yourself
(`lean/README.md` says how).

Two smaller limits:

- `REPORT.md`, `MATCH.md`, `bundle.json` and `README.md` are outside the seal.
- The arXiv identifier is the one the owner declared; nothing compares it with arXiv.

## Run the checks and build the site

Node 20 or later; there is nothing to install.

    npm test                                   # the tests
    node checks/check_paper.mjs papers/<slug>  # one folder (no argument: every folder)
    node site/build.mjs                        # builds dist/ from papers/

Open `dist/index.html` in a browser, or serve the folder (`npx serve dist`).

The main page lists every paper with its badges; the comment at the top of `site/build.mjs` says
where each number comes from. Each paper also gets `dist/papers/<slug>/`: its folder as shared and
its page, `index.html`, on which every finding stands beside the sentence it concerns and each
result opens the Lean that states it — the local UI's page of a finished run, read-only. A plain
summary (badges, the report's first paragraph, links to the files) stands in it until the page is
drawn, and for a browser that runs no script.

### The paper viewer (`site/viewer/`)

The paper's page is drawn in the browser from `page/page.json` by the local UI's own `app.js`, in its
snapshot mode, with its stylesheet, KaTeX, pdf.js (PDF figures) and DOMPurify. These files are
copied from PaperFormalizer, never edited here:

    node <PaperFormalizer>/tools/scripts/sync_viewer.mjs <this repository>

`site/viewer/VERSION` names the PaperFormalizer commit they come from; run the command again after a
change to the UI's paper page. The build refuses to run without the viewer.

### GitHub Pages

`.github/workflows/pages.yml` builds the site and publishes `dist/` at
`https://<owner>.github.io/<repository>/`. Every link of the site is relative, so it works under
that path and under a domain of its own alike.

GitHub Pages sets no header of the site's choosing, so each page carries its
Content-Security-Policy in a `<meta>` (`CSP` in `site/build.mjs`): scripts, styles, images and
frames of the site only, no form, no `<base>`, no plugin; the paper's page also takes its code font
from jsDelivr, and the pages the build writes their text fonts from Google Fonts. A bundle's
rendered HTML (the paper, its notes, the TeX of the findings) reaches only the paper's page, where
the viewer passes every string through DOMPurify before inserting it. No file of a bundle that a
browser would run is copied into the site: only the inert types of `SERVED_EXT` in
`site/build.mjs` are (PDF, images, TeX, Lean, Markdown, text, JSON, …) — an allowlist, since Pages
types a file by its extension, renders HTML and every XML type, and cannot sandbox a file served at
the top level. The rest stays in the folder in git.

## Owner setup, once

For shares (`ingest.yml`) and the site (`pages.yml`):

1. **Settings → Secrets and variables → Actions → Secrets**: `INGEST_SECRET`, the same value as the
   Worker's secret of that name.
2. **Settings → Secrets and variables → Actions → Variables**: `TRUSTED_SHARERS` ("Who can get a
   paper in"); unset, every share waits for you. `WORKER_URL` and `SITE_URL` only to change the
   defaults (`checks/ingest.mjs`).
3. **Settings → Actions → General → Workflow permissions**: allow GitHub Actions to create and
   approve pull requests (the pull request of a sharer who is not trusted).
4. **Settings → Pages → Source**: GitHub Actions. On a free plan Pages serves a public repository only.
5. The ingest pushes a trusted sharer's paper to `main` with the workflow's own token: a rule on
   `main` that requires a status check or a pull request must let GitHub Actions bypass it
   (a ruleset with "GitHub Actions" as a bypass actor), or those shares fail to push.

For a hand-opened pull request (`check.yml`) to merge itself:

1. **Settings → General → Pull Requests → Allow auto-merge**: on (with squash merging allowed).
2. **Settings → Branches**: protect `main` and **require the status check `check`** (see 5 above).
   Without it a failing pull request could be merged, and auto-merge has nothing to wait for. The
   pull requests the ingest opens never get that check (see "Who can get a paper in"): merge those
   with your admin bypass.

The workflow uses `pull_request_target`, so it always runs the scripts of `main` and only reads the
pull request's files. Keep it that way: never add a step that installs, builds or runs anything from
the pull request.

## License and the papers' rights

The code of this repository (`checks/`, `site/`, `worker/`, `test/`, the workflows) is under the
PaperFormalizer License (`LICENSE`): the MIT License with a responsible-use condition — it must not
be used for targeted harassment, threats or discriminatory abuse, or to spread allegations known to
be false, while good-faith scientific criticism, peer review and the reporting of mathematical
errors, naming the papers and authors concerned, are expressly permitted. The copyright holders are
listed in `AUTHORS`. `site/viewer/` also holds unmodified releases of KaTeX (MIT), pdf.js
(Apache-2.0) and DOMPurify (Apache-2.0 or MPL-2.0).

The shared papers are not under that license: a paper's text, figures and proofs belong to its
authors, and whoever shares a paper states, by sharing it, that they may publish it. To have a paper
taken down, open an issue naming it; the owner removes it as below.

## Remove a paper

Only the owner removes a paper (a pull request that deletes a folder fails the check):

    git rm -r papers/<slug>
    git commit -m "Remove <slug>"
    git push

The site rebuilds without it. The files stay in the git history; rewriting history is a separate,
manual step if a paper must disappear entirely.

## Sharing through the Worker

A sharer needs only a GitHub account: their PaperFormalizer uploads the bundle to the share worker
(`worker/`, a Cloudflare Worker), they sign in with GitHub in the browser (identity only, "public data
only" on the consent screen), confirm on the worker's page, and the worker dispatches this
repository's ingest workflow, which checks the bundle and adds the paper. `worker/README.md` says
what the worker does, how to deploy it and which secrets it holds.
