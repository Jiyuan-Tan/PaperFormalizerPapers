# Lean formalization — oai_uniform_influence_hypergraph

A standalone Lake project: `Papers/OaiUniformInfluenceHypergraph/` is the Lean development of the corrected paper (17 file(s)). It depends on the public libraries listed below and on nothing else; what it uses of the author's own library is copied here.

## Build

Lean toolchain: `leanprover/lean4:v4.33.0` (`lean-toolchain`; `elan` installs it). From this directory:

```
lake exe cache get   # fetches the libraries and Mathlib's compiled files
lake build
lake env lean Check.lean   # the axioms of each result
```

`lake build` builds `Papers` (`Papers.OaiUniformInfluenceHypergraph` is the paper). There is no `lake-manifest.json`: Lake writes it on the first command, from the revisions the lakefile pins.

## Libraries it requires

- `Causalean` (Causal inference and statistics foundations (identification, estimation, semiparametrics, concentration).): `https://github.com/Jiyuan-Tan/CausalSmith` at `a7085d88d2e4b30003db7097ca374f4718da0f01`; it brings in `FoML`, `Optlib`
- `mathlib` (the Lean mathematical library): `https://github.com/leanprover-community/mathlib4` at `db584cd6d46c92f209a44c0f1c829460d327499d`

Note: built against a local copy of Causalean (its commit 5ca94e0ac387, with 1 of the files reached changed since): 12 file(s) of it are reached, recorded by content hash in `built-against.json`. That they are the files of the public revision a7085d88d2e4 this bundle requires was NOT verified (not possible offline): `paperformalizer report oai_uniform_influence_hypergraph --verify-public` compares them over the network; by hand: `git hash-object <file>` in the local checkout against the blob hashes of `https://github.com/Jiyuan-Tan/CausalSmith` at `a7085d88d2e4b30003db7097ca374f4718da0f01`.

## The paper's results

- Theorem 1.1: `Papers.OaiUniformInfluenceHypergraph.variance_le_div_log_pow_mul_totalInfluence` (`Papers/OaiUniformInfluenceHypergraph/TMain.lean:201`)
- Lemma 2.1: `Papers.OaiUniformInfluenceHypergraph.sum_lowDegree_fourierCoeff_sq_le` (`Papers/OaiUniformInfluenceHypergraph/Helpers/LowDegree.lean:196`)
- Lemma 3.1: `Papers.OaiUniformInfluenceHypergraph.sum_blockProb_mul_fourierCoeff_sq_le` (`Papers/OaiUniformInfluenceHypergraph/Helpers/Block.lean:164`)
- Lemma 3.2: `Papers.OaiUniformInfluenceHypergraph.blockProb_capture_ge` (`Papers/OaiUniformInfluenceHypergraph/Helpers/Capture.lean:127`)
- Corollary 4.1: `Papers.OaiUniformInfluenceHypergraph.thresholdWidth_le` (`Papers/OaiUniformInfluenceHypergraph/TCorThreshold.lean:18`)

`MATCH.md`, one directory up, sets each statement beside its declaration.

## Checking the axioms

`Check.lean` prints the axioms of each result above (`lake env lean Check.lean`, after the build): none may appear beyond `propext`, `Classical.choice` and `Quot.sound`. The source must contain no `sorry`, `admit` or `axiom`.

## What is in this directory

Nothing from the author's own library.

Imported from the required libraries: `Causalean` (4 module(s)), `Mathlib` (12 module(s)).

## Self-containment

Checked when this directory was written: every import of every file resolves to a file here or to a module of a required library, no path in a lakefile leaves this directory, and nothing names the machine it was built on.

