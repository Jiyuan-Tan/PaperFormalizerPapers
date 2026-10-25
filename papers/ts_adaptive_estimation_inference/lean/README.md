# Lean formalization — ts_adaptive_estimation_inference

A standalone Lake project: `Papers/TsAdaptiveEstimationInference/` is the Lean development of the corrected paper (129 file(s)). It depends on the public libraries listed below and on nothing else; what it uses of the author's own library is copied here.

## Build

Lean toolchain: `leanprover/lean4:v4.33.0` (`lean-toolchain`; `elan` installs it). From this directory:

```
lake exe cache get   # fetches the libraries and Mathlib's compiled files
lake build
lake env lean Check.lean   # the axioms of each result
```

`lake build` builds `Papers` and `Toolkit` (`Papers.TsAdaptiveEstimationInference` is the paper). There is no `lake-manifest.json`: Lake writes it on the first command, from the revisions the lakefile pins.

## Libraries it requires

- `Causalean` (Causal inference and statistics foundations (identification, estimation, semiparametrics, concentration).): `https://github.com/Jiyuan-Tan/CausalSmith` at `a7085d88d2e4b30003db7097ca374f4718da0f01`; it brings in `FoML`, `Optlib`
- `mathlib` (the Lean mathematical library): `https://github.com/leanprover-community/mathlib4` at `db584cd6d46c92f209a44c0f1c829460d327499d`
- `StatLean` (Mathematical statistics: estimation, hypothesis testing, asymptotic statistics, nonparametrics, time series (adapted Stat-Lean).): no public repository carries the adapted copy this was built with, so it is included in `vendor/StatLean/` with its licence (`vendor/StatLean/UPSTREAM.md`: where it comes from)

Note: built against a local copy of Causalean (its commit 5ca94e0ac387, with 2 of the files reached changed since): 72 file(s) of it are reached, recorded by content hash in `built-against.json`. That they are the files of the public revision a7085d88d2e4 this bundle requires was NOT verified (not possible offline): `paperformalizer report ts_adaptive_estimation_inference --verify-public` compares them over the network; by hand: `git hash-object <file>` in the local checkout against the blob hashes of `https://github.com/Jiyuan-Tan/CausalSmith` at `a7085d88d2e4b30003db7097ca374f4718da0f01`.

## The paper's results

- Theorem 3.1: `Papers.TsAdaptiveEstimationInference.common_dp` (`Papers/TsAdaptiveEstimationInference/TCommonDp.lean:24`)
- Proposition 3.5: `Papers.TsAdaptiveEstimationInference.exist_lambda_deepiv` (`Papers/TsAdaptiveEstimationInference/TExistLambdaDeepiv.lean:65`)
- Theorem 3.6: `Papers.TsAdaptiveEstimationInference.deepiv_rate` (`Papers/TsAdaptiveEstimationInference/TDeepivRate.lean:64`)
- Proposition 3.8: `Papers.TsAdaptiveEstimationInference.exist_lambda_iter_rdiv` (`Papers/TsAdaptiveEstimationInference/TExistLambdaIterRdiv.lean:196`)
- Theorem 3.9: `Papers.TsAdaptiveEstimationInference.iter_rdiv_rate` (`Papers/TsAdaptiveEstimationInference/TIterRdivRate.lean:56`)
- Proposition 3.13: `Papers.TsAdaptiveEstimationInference.exist_lambda` (`Papers/TsAdaptiveEstimationInference/TExistLambda.lean:122`)
- Theorem 3.14: `Papers.TsAdaptiveEstimationInference.tikhonov_rate` (`Papers/TsAdaptiveEstimationInference/TTikhonvRate.lean:45`)
- Proposition 3.17: `Papers.TsAdaptiveEstimationInference.exist_lambda_iter_trae` (`Papers/TsAdaptiveEstimationInference/TExistLambdaIterTrae.lean:118`)
- Theorem 3.18: `Papers.TsAdaptiveEstimationInference.iter_trae_rate` (`Papers/TsAdaptiveEstimationInference/TIterTraeRate.lean:392`)
- Corollary 3.19: `Papers.TsAdaptiveEstimationInference.dr_asymptotic_normality` (`Papers/TsAdaptiveEstimationInference/TNormality.lean:41`)
- Lemma A.1: `Papers.TsAdaptiveEstimationInference.variational_source_uniform` (`Papers/TsAdaptiveEstimationInference/Helpers/SpectralRegularization.lean:544`)
- Lemma B.1: `Papers.TsAdaptiveEstimationInference.t_err_dp` (`Papers/TsAdaptiveEstimationInference/Helpers/RDIV.lean:85`)
- Lemma B.2: `Papers.TsAdaptiveEstimationInference.err_l_dp` (`Papers/TsAdaptiveEstimationInference/Helpers/RDIV.lean:354`)
- Lemma B.3: `Papers.TsAdaptiveEstimationInference.err_r_dp` (`Papers/TsAdaptiveEstimationInference/Helpers/RDIV.lean:605`)
- Lemma B.4: `Papers.TsAdaptiveEstimationInference.str_dp` (`Papers/TsAdaptiveEstimationInference/Helpers/RDIV.lean:705`)
- Corollary B.5: `Papers.TsAdaptiveEstimationInference.rdiv_discrepancy_bound` (`Papers/TsAdaptiveEstimationInference/TRdivDiscrepancyBound.lean:411`)
- Lemma B.6: `Papers.TsAdaptiveEstimationInference.rdiv_accepted_bounds` (`Papers/TsAdaptiveEstimationInference/Helpers/RDIV.lean:833`)
- Lemma B.7: `Papers.TsAdaptiveEstimationInference.iter_bias` (`Papers/TsAdaptiveEstimationInference/Helpers/IterBias.lean:382`)
- Corollary B.9: `Papers.TsAdaptiveEstimationInference.iter_rdiv_discrepancy_bound` (`Papers/TsAdaptiveEstimationInference/TIterRdivDiscrepancyBound.lean:98`)
- Lemma B.10: `Papers.TsAdaptiveEstimationInference.iter_rdiv_accepted_bounds` (`Papers/TsAdaptiveEstimationInference/Helpers/IterRDIV.lean:329`)
- Lemma C.1: `Papers.TsAdaptiveEstimationInference.concentrate_l` (`Papers/TsAdaptiveEstimationInference/Helpers/TRAELossEvents.lean:436`)
- Lemma C.2: `Papers.TsAdaptiveEstimationInference.strong_convexity` (`Papers/TsAdaptiveEstimationInference/Helpers/TRAE.lean:233`)
- Corollary C.3: `Papers.TsAdaptiveEstimationInference.trae_discrepancy_bound` (`Papers/TsAdaptiveEstimationInference/TTraeDiscrepancyBound.lean:35`)
- Lemma C.4: `Papers.TsAdaptiveEstimationInference.trae_accepted_bounds` (`Papers/TsAdaptiveEstimationInference/Helpers/TRAE.lean:284`)
- Lemma C.2: `Papers.TsAdaptiveEstimationInference.iter_trae_strong_propagation` (`Papers/TsAdaptiveEstimationInference/Helpers/IterTRAEPropagation.lean:38`)
- Corollary C.6: `Papers.TsAdaptiveEstimationInference.iter_trae_discrepancy_bound` (`Papers/TsAdaptiveEstimationInference/TIterTraeDiscrepancyBound.lean:53`)
- Lemma C.7: `Papers.TsAdaptiveEstimationInference.iter_trae_accepted_stability` (`Papers/TsAdaptiveEstimationInference/Helpers/IterTRAEStability.lean:282`)
- Proposition D.1: `Papers.TsAdaptiveEstimationInference.rkhs_qp` (`Papers/TsAdaptiveEstimationInference/TRkhsQp.lean:19`)

`MATCH.md`, one directory up, sets each statement beside its declaration.

## Checking the axioms

`Check.lean` prints the axioms of each result above (`lake env lean Check.lean`, after the build): none may appear beyond `propext`, `Classical.choice` and `Quot.sound`. The source must contain no `sorry`, `admit` or `axiom`.

## What is in this directory

From the author's own library, copied here (4 module(s)): `Toolkit.Foundations.Analysis.SpecialFunctions.TikhonovFilter`, `Toolkit.Foundations.LinearAlgebra.Matrix.PosSemidef`, `Toolkit.Foundations.LinearAlgebra.Matrix.TraceExponential`, `Toolkit.Foundations.Probability.Independence.ProductConditioning`.

Imported from the required libraries: `Batteries` (1 module(s)), `Causalean` (15 module(s)), `Mathlib` (156 module(s)), `StatLean` (3 module(s)).

## Moved into the author's library

Results first proved for this paper and since moved into the library, where the paper now uses them:

- `Toolkit.Foundations.Analysis.SpecialFunctions.rpow_mul_div_add_pow_le_rpow_min`
- `Toolkit.Foundations.Probability.Independence.measurableSet_and_le_measureReal_diag_of_indep_of_ae_section`
- `Toolkit.Foundations.LinearAlgebra.Matrix.dotProduct_mulVec_sub_le_of_posSemidef_of_mulVec_eq`
- `Toolkit.Foundations.LinearAlgebra.Matrix.mulVec_eq_of_forall_dotProduct_mulVec_sub_le`

## Self-containment

Checked when this directory was written: every import of every file resolves to a file here or to a module of a required library, no path in a lakefile leaves this directory, and nothing names the machine it was built on.

