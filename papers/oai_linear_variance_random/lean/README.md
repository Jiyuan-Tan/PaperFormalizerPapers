# Lean formalization — oai_linear_variance_random

A standalone Lake project: `Papers/OaiLinearVarianceRandom/` is the Lean development of the corrected paper (33 file(s)). It depends on the public libraries listed below and on nothing else; what it uses of the author's own library is copied here.

## Build

Lean toolchain: `leanprover/lean4:v4.33.0` (`lean-toolchain`; `elan` installs it). From this directory:

```
lake exe cache get   # fetches the libraries and Mathlib's compiled files
lake build
lake env lean Check.lean   # the axioms of each result
```

`lake build` builds `Papers` and `Toolkit` (`Papers.OaiLinearVarianceRandom` is the paper). There is no `lake-manifest.json`: Lake writes it on the first command, from the revisions the lakefile pins.

## Libraries it requires

- `Causalean` (Causal inference and statistics foundations (identification, estimation, semiparametrics, concentration).): `https://github.com/Jiyuan-Tan/CausalSmith` at `a7085d88d2e4b30003db7097ca374f4718da0f01`; it brings in `FoML`, `Optlib`
- `mathlib` (the Lean mathematical library): `https://github.com/leanprover-community/mathlib4` at `db584cd6d46c92f209a44c0f1c829460d327499d`

Note: built against a local copy of Causalean (its commit 5ca94e0ac387): 8 file(s) of it are reached, recorded by content hash in `built-against.json`. That they are the files of the public revision a7085d88d2e4 this bundle requires was NOT verified (not possible offline): `paperformalizer report oai_linear_variance_random --verify-public` compares them over the network; by hand: `git hash-object <file>` in the local checkout against the blob hashes of `https://github.com/Jiyuan-Tan/CausalSmith` at `a7085d88d2e4b30003db7097ca374f4718da0f01`.

## The paper's results

- Theorem 1.1: `Papers.OaiLinearVarianceRandom.var_hittingTime_theta_n` (`Papers/OaiLinearVarianceRandom/TMain.lean:124`)
- Lemma 2.1: `Papers.OaiLinearVarianceRandom.oneKillProb_two_rpow_le` (`Papers/OaiLinearVarianceRandom/Helpers/AssignmentSets.lean:347`)
- Lemma 2.2: `Papers.OaiLinearVarianceRandom.potential_drift` (`Papers/OaiLinearVarianceRandom/Helpers/Potential.lean:244`)
- Lemma 3.1: `Papers.OaiLinearVarianceRandom.variance_cappedTime_le_sum_delay_sq` (`Papers/OaiLinearVarianceRandom/Helpers/Omission.lean:119`)
- Lemma 3.2: `Papers.OaiLinearVarianceRandom.condProb_pivotal_le` (`Papers/OaiLinearVarianceRandom/Helpers/Pivotality.lean:36`)
- Lemma 4.1: `Papers.OaiLinearVarianceRandom.condExp_occupation_le` (`Papers/OaiLinearVarianceRandom/Helpers/Pivotality.lean:85`)
- Corollary 4.2: `Papers.OaiLinearVarianceRandom.condExp_pivotal_duration_le` (`Papers/OaiLinearVarianceRandom/TDuration.lean:82`)
- Proposition 4.3: `Papers.OaiLinearVarianceRandom.condExp_delay_sq_le` (`Papers/OaiLinearVarianceRandom/TDelay.lean:25`)
- Lemma 4.4: `Papers.OaiLinearVarianceRandom.incidence_moments_bound` (`Papers/OaiLinearVarianceRandom/Helpers/Moments.lean:292`)
- Corollary 5.2: `Papers.OaiLinearVarianceRandom.levelLocation_window_theta_sqrt` (`Papers/OaiLinearVarianceRandom/TWindow.lean:30`)

`MATCH.md`, one directory up, sets each statement beside its declaration.

## Checking the axioms

`Check.lean` prints the axioms of each result above (`lake env lean Check.lean`, after the build): none may appear beyond `propext`, `Classical.choice` and `Quot.sound`. The source must contain no `sorry`, `admit` or `axiom`.

## What is in this directory

From the author's own library, copied here (1 module(s)): `Toolkit.Foundations.Probability.Processes.DriftRecursion`.

Imported from the required libraries: `Batteries` (1 module(s)), `Causalean` (2 module(s)), `Mathlib` (116 module(s)).

## Self-containment

Checked when this directory was written: every import of every file resolves to a file here or to a module of a required library, no path in a lakefile leaves this directory, and nothing names the machine it was built on.

