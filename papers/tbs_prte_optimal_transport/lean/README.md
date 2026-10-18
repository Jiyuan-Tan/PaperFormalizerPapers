# Lean formalization — tbs_prte_optimal_transport

A standalone Lake project: `Papers/TbsPrteOptimalTransport/` is the Lean development of the corrected paper (432 file(s)). It depends on the public libraries listed below and on nothing else; what it uses of the author's own library is copied here.

## Build

Lean toolchain: `leanprover/lean4:v4.33.0` (`lean-toolchain`; `elan` installs it). From this directory:

```
lake exe cache get   # fetches the libraries and Mathlib's compiled files
lake build
lake env lean Check.lean   # the axioms of each result
```

`lake build` builds `Papers` and `Toolkit` (`Papers.TbsPrteOptimalTransport` is the paper). There is no `lake-manifest.json`: Lake writes it on the first command, from the revisions the lakefile pins.

## Libraries it requires

- `Causalean` (Causal inference and statistics foundations (identification, estimation, semiparametrics, concentration).): `https://github.com/Jiyuan-Tan/CausalSmith` at `a7085d88d2e4b30003db7097ca374f4718da0f01`; it brings in `FoML`, `Optlib`
- `mathlib` (the Lean mathematical library): `https://github.com/leanprover-community/mathlib4` at `db584cd6d46c92f209a44c0f1c829460d327499d`
- `StatLean` (Mathematical statistics: estimation, hypothesis testing, asymptotic statistics, nonparametrics, time series (adapted Stat-Lean).): no public repository carries the adapted copy this was built with, so it is included in `vendor/StatLean/` with its licence (`vendor/StatLean/UPSTREAM.md`: where it comes from)

Note: built against a local copy of Causalean (its commit 5ca94e0ac387): 36 file(s) of it are reached, recorded by content hash in `built-against.json`. That they are the files of the public revision a7085d88d2e4 this bundle requires was NOT verified (not possible offline): `theoremchecker report tbs_prte_optimal_transport --verify-public` compares them over the network; by hand: `git hash-object <file>` in the local checkout against the blob hashes of `https://github.com/Jiyuan-Tan/CausalSmith` at `a7085d88d2e4b30003db7097ca374f4718da0f01`.

## The paper's results

- Theorem 2.3: `Papers.TbsPrteOptimalTransport.productCost_transport_extrema` (`Papers/TbsPrteOptimalTransport/T1dOt.lean:22`)
- Proposition 3.1: `Papers.TbsPrteOptimalTransport.feasible_iff_structural` (`Papers/TbsPrteOptimalTransport/TSharpness.lean:25`)
- Theorem 3.4: `Papers.TbsPrteOptimalTransport.finite_instrument_sharp_bounds` (`Papers/TbsPrteOptimalTransport/TDiscreteLowerBound.lean:40`)
- Theorem 3.7: `Papers.TbsPrteOptimalTransport.general_instrument_sharp_bounds` (`Papers/TbsPrteOptimalTransport/TContinuousLowerBound.lean:29`)
- Theorem 3.8: `Papers.TbsPrteOptimalTransport.conditional_sharp_bounds` (`Papers/TbsPrteOptimalTransport/TCovariateLowerBound.lean:30`)
- Proposition 4.3: `Papers.TbsPrteOptimalTransport.discrete_reduction` (`Papers/TbsPrteOptimalTransport/TDiscreteReduction.lean:28`)
- Proposition 4.4: `Papers.TbsPrteOptimalTransport.J_specialization` (`Papers/TbsPrteOptimalTransport/TJSpecialization.lean:117`)
- Theorem 4.7: `Papers.TbsPrteOptimalTransport.dml_asymptotic_normality` (`Papers/TbsPrteOptimalTransport/TDmlNormality.lean:485`)
- Proposition 4.8: `Papers.TbsPrteOptimalTransport.continuous_reduction` (`Papers/TbsPrteOptimalTransport/TContinuousReduction.lean:30`)
- Theorem 4.10: `Papers.TbsPrteOptimalTransport.plugin_rate` (`Papers/TbsPrteOptimalTransport/TContinuousRate.lean:321`)
- Lemma D.1: `Papers.TbsPrteOptimalTransport.score_mean_and_orthogonality` (`Papers/TbsPrteOptimalTransport/Helpers/ScoreOrthogonality.lean:117`)
- Corollary O5.1: `Papers.TbsPrteOptimalTransport.primitive_learner_rate` (`Papers/TbsPrteOptimalTransport/TContinuousPrimitiveRate.lean:48`)

`MATCH.md`, one directory up, sets each statement beside its declaration.

## Checking the axioms

`Check.lean` prints the axioms of each result above (`lake env lean Check.lean`, after the build): none may appear beyond `propext`, `Classical.choice` and `Quot.sound`. The source must contain no `sorry`, `admit` or `axiom`.

## What is in this directory

From the author's own library, copied here (6 module(s)): `Toolkit.Foundations.Analysis.Calculus.AbsolutelyContinuous`, `Toolkit.Foundations.Probability.Conditioning.FiniteValuedConditionalExpectation`, `Toolkit.Tricks.Probability.Moments.ClippedCouplings`, `Toolkit.Tricks.Probability.Moments.ProductCouplingBounds`, `Toolkit.Tricks.Probability.Moments.QuantileVersions`, `Toolkit.Tricks.Probability.Moments.SymmetricClipping`.

Imported from the required libraries: `Causalean` (20 module(s)), `Mathlib` (201 module(s)), `StatLean` (1 module(s)).

## Self-containment

Checked when this directory was written: every import of every file resolves to a file here or to a module of a required library, no path in a lakefile leaves this directory, and nothing names the machine it was built on.

