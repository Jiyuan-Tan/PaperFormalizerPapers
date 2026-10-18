# Corrected paper — tbs_extreme_effects

Ready to submit as far as the mechanical checks go; 12 item(s) to check are listed in `corrected_paper/TODO.md`.

- `corrected_paper/` — the paper as it reads after the corrections: the author's own source (class, preamble, bibliography, figures, file layout), with each corrected statement, proof step and proof written in place of the printed one. Main file `corrected_paper/Arxiv_template.tex`; compiled: `corrected_paper/Arxiv_template.pdf` (65 pages). A reading the statements rely on appears as a remark of the paper at the statement it concerns.
- `corrected_paper/TODO.md` — what remains before submitting, each item with its file and line.
- `REPORT.md` — what was wrong, what was done about it, and what was proved in Lean.
- `MATCH.md` — each result beside its Lean declaration, phrase by phrase.
- `page/page.json` — the paper's page as TheoremChecker's reader draws it (the statements as corrected, the notes, each result's verdict and its Lean), as data.
- `lean/` — the Lean code, a standalone project to send to whoever checks it (`lean/README.md`: how to build it); self-contained.
- `f4_seal.json` — the two reviewers' verdicts on each Lean statement, under the code `770081c9d1171cf3f395677358785d020af928c2f4a508ff8d2a54aec3e52527`, with the hash of every file of `lean/`, `corrected_paper/` and `page/`; `theoremchecker seal` checks it. The files at this directory's root (`REPORT.md`, `MATCH.md`, `bundle.json`, this file) are outside the seal. `f4_reviews.log` — what the two reviewers answered at each review pass of the run, earlier passes included.

What is checked is the paper's results: each corrected statement and proof, and every result that depends on one. The prose around them is the authors', as printed.
