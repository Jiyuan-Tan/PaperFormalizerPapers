# Lean formalization — oai_bound_dyadic_triangular

A standalone Lake project: `Papers/OaiBoundDyadicTriangular/` is the Lean development of the corrected paper (34 file(s)). It depends on the public libraries listed below and on nothing else; what it uses of the author's own library is copied here.

## Build

Lean toolchain: `leanprover/lean4:v4.33.0` (`lean-toolchain`; `elan` installs it). From this directory:

```
lake exe cache get   # fetches the libraries and Mathlib's compiled files
lake build
lake env lean Check.lean   # the axioms of each result
```

`lake build` builds `Papers` (`Papers.OaiBoundDyadicTriangular` is the paper). There is no `lake-manifest.json`: Lake writes it on the first command, from the revisions the lakefile pins.

## Libraries it requires

- `mathlib` (the Lean mathematical library): `https://github.com/leanprover-community/mathlib4` at `db584cd6d46c92f209a44c0f1c829460d327499d`

## The paper's results

- Theorem 1.1: `Papers.OaiBoundDyadicTriangular.dyadic_triangular_bound` (`Papers/OaiBoundDyadicTriangular/TMain.lean:65`)
- Lemma 2.1: `Papers.OaiBoundDyadicTriangular.matrixEnergy_hessian` (`Papers/OaiBoundDyadicTriangular/Helpers/MatrixHessian.lean:104`)
- Lemma 2.2: `Papers.OaiBoundDyadicTriangular.hessForm_order` (`Papers/OaiBoundDyadicTriangular/Helpers/MatrixHessian.lean:135`)
- Corollary 2.3: `Papers.OaiBoundDyadicTriangular.matrixEnergy_midpoint_gap` (`Papers/OaiBoundDyadicTriangular/TGap.lean:22`)
- Proposition 3.1: `Papers.OaiBoundDyadicTriangular.abs_trace_le_hessForm_sum` (`Papers/OaiBoundDyadicTriangular/TTrace.lean:212`)
- Proposition 4.1: `Papers.OaiBoundDyadicTriangular.energyIncrement_controls_trace` (`Papers/OaiBoundDyadicTriangular/TIncrease.lean:24`)
- Lemma 5.1: `Papers.OaiBoundDyadicTriangular.totalEnergy_bound_and_telescope` (`Papers/OaiBoundDyadicTriangular/Helpers/Summation.lean:262`)
- Lemma 5.2: `Papers.OaiBoundDyadicTriangular.localForm_one_scale_bound` (`Papers/OaiBoundDyadicTriangular/Helpers/Continuity.lean:29`)

`MATCH.md`, one directory up, sets each statement beside its declaration.

## Checking the axioms

`Check.lean` prints the axioms of each result above (`lake env lean Check.lean`, after the build): none may appear beyond `propext`, `Classical.choice` and `Quot.sound`. The source must contain no `sorry`, `admit` or `axiom`.

## What is in this directory

Nothing from the author's own library.

Imported from the required libraries: `Mathlib` (27 module(s)).

## Self-containment

Checked when this directory was written: every import of every file resolves to a file here or to a module of a required library, no path in a lakefile leaves this directory, and nothing names the machine it was built on.

