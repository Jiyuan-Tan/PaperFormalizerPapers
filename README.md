# TheoremChecker — Shared Papers

The public registry of papers checked by [TheoremChecker](https://github.com/Jiyuan-Tan/TheoremChecker),
a tool that referees a paper's statements, repairs the errors it finds and proves the corrected
results in Lean 4. Each paper here is one folder, `papers/<slug>/`, holding the bundle a finished run
wrote. The site is built from those folders.

Nobody clones this repository to share a paper: the tool does it through GitHub.

## How a paper gets in

1. On a finished run, the user presses **Share** on the paper's page.
2. The tool opens a pull request from the user's GitHub account that adds one folder, `papers/<slug>/`.
3. An automatic check runs on the pull request (`.github/workflows/check.yml`).
4. If it passes, the pull request merges itself, and Cloudflare Pages rebuilds the site from `main`.

## A paper folder

    papers/<slug>/
      share.json        who shared it and when (written by the share command)
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
file is stored non-executable (git mode 100644): the share command writes them so, whatever mode
the file had on the sharer's machine, and the check rejects an executable file.

`share.json`:

    { "shared_by": "<github login>", "shared_at": "<ISO date>", "arxiv": "<id or null>" }

`subject` (a short string, e.g. the arXiv subject) is accepted as an optional fourth field; the tool
does not write it yet.

## What the check verifies

`checks/check_pr.mjs` (the pull request) and `checks/check_paper.mjs` (the folder), with no model
and no Lean:

- the pull request adds or changes files under exactly one `papers/<slug>/`, and nothing else;
- `share.json` is well-formed, `shared_by` is the pull request's author, and a paper already in the
  registry is changed only by the person who shared it;
- the required files are there and nothing is outside the layout above: no dotfile, no executable,
  no symbolic link, no `.html` or `.js` file;
- the folder is under 60 MB and no file is over 30 MB;
- `page/page.json` parses, has `schema` 1 and the folder's slug;
- **the seal holds**: the code in `f4_seal.json` is the hash of the seal's own contents, both
  reviewers passed every statement, and `f4_reviews.log` and every file under `lean/`,
  `corrected_paper/` and `page/` has the hash the seal names — with no file there that the seal does
  not name (the compiled PDF apart, which the tool leaves out of the seal).

The seal check in `checks/seal.mjs` mirrors the tool's `tools/src/verify/f4_seal.ts`. The tool's own
command is the reference:

    theoremchecker seal papers/<slug>

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
where each number comes from. Each paper also gets `dist/papers/<slug>/`: its folder as shared and a
short placeholder page. **The full paper page (findings beside the text, the Lean statement of each
result) is the next piece to build**; it will be drawn from `page/page.json`.

### Cloudflare Pages

Connect the repository in the Cloudflare dashboard (Workers & Pages → Create → Pages → Connect to
Git), production branch `main`, and set:

- Build command: `node site/build.mjs`
- Build output directory: `dist`
- Framework preset: none

No `wrangler` file is needed. The build writes `dist/_headers`, which tells Cloudflare that nothing
under `/papers/` may run a script: a bundle's files are served as data.

## Owner setup, once

The workflow can only merge a pull request when the repository lets it:

1. **Settings → General → Pull Requests → Allow auto-merge**: on (with squash merging allowed).
2. **Settings → Branches**: protect `main` and **require the status check `check`**. Without it a
   failing pull request could be merged, and auto-merge has nothing to wait for.

The workflow uses `pull_request_target`, so it always runs the scripts of `main` and only reads the
pull request's files. Keep it that way: never add a step that installs, builds or runs anything from
the pull request.

## Remove a paper

Only the owner removes a paper (a pull request that deletes a folder fails the check):

    git rm -r papers/<slug>
    git commit -m "Remove <slug>"
    git push

The site rebuilds without it. The files stay in the git history; rewriting history is a separate,
manual step if a paper must disappear entirely.
