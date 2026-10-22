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

Note: built against a local copy of Causalean (its commit 5ca94e0ac387): 36 file(s) of it are reached, recorded by content hash in `built-against.json`. That they are the files of the public revision a7085d88d2e4 this bundle requires was NOT verified (not possible offline): `paperformalizer report tbs_prte_optimal_transport --verify-public` compares them over the network; by hand: `git hash-object <file>` in the local checkout against the blob hashes of `https://github.com/Jiyuan-Tan/CausalSmith` at `a7085d88d2e4b30003db7097ca374f4718da0f01`.

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

From the author's own library, copied here (10 module(s)): `Toolkit.Foundations.Algebra.Order.SortingRearrangement`, `Toolkit.Foundations.Analysis.Calculus.AbsolutelyContinuous`, `Toolkit.Foundations.Probability.Conditioning.FiniteValuedConditionalExpectation`, `Toolkit.Foundations.Probability.Moments.HingeExpansion`, `Toolkit.Tricks.Probability.Distributions.DistributionalTransform`, `Toolkit.Tricks.Probability.Moments.ClippedCouplings`, `Toolkit.Tricks.Probability.Moments.ProductCouplingBounds`, `Toolkit.Tricks.Probability.Moments.QuantileVersions`, `Toolkit.Tricks.Probability.Moments.SymmetricClipping`, `Toolkit.Tricks.Statistics.Asymptotics.ConditionalMarkov`.

Imported from the required libraries: `Batteries` (1 module(s)), `Causalean` (20 module(s)), `Mathlib` (243 module(s)), `StatLean` (1 module(s)).

## Moved into the author's library

Results first proved for this paper and since moved into the library, where the paper now uses them:

- `Toolkit.Tricks.Probability.Distributions.leftCDF`
- `Toolkit.Tricks.Probability.Distributions.distributionalTransform`
- `Toolkit.Tricks.Probability.Distributions.leftCDF_mono`
- `Toolkit.Tricks.Probability.Distributions.measurable_leftCDF`
- `Toolkit.Tricks.Probability.Distributions.measurable_distributionalTransform`
- `Toolkit.Tricks.Probability.Distributions.leftCDF_le_cdf`
- `Toolkit.Tricks.Probability.Distributions.cdf_le_leftCDF`
- `Toolkit.Tricks.Probability.Distributions.leftCDF_eq_leftLim`
- `Toolkit.Tricks.Probability.Distributions.leftCDF_quantile_le`
- `Toolkit.Tricks.Probability.Distributions.distributionalTransform_bounds`
- `Toolkit.Tricks.Probability.Distributions.unifOI_Iio`
- `Toolkit.Tricks.Probability.Distributions.ae_snd_mem_Ioo_prod_unifOI`
- `Toolkit.Tricks.Probability.Distributions.measureReal_singleton_eq_cdf_sub_leftCDF`
- `Toolkit.Tricks.Probability.Distributions.distributionalTransform_lt_quantile_iff`
- `Toolkit.Tricks.Probability.Distributions.distributionalTransform_Iio_interior`
- `Toolkit.Tricks.Probability.Distributions.map_distributionalTransform_eq_unifOI`
- `Toolkit.Tricks.Probability.Distributions.ae_eq_of_ae_le_of_map_eq`
- `Toolkit.Tricks.Probability.Distributions.ae_quantile_distributionalTransform_eq`
- `Toolkit.Tricks.Probability.Distributions.map_distributionalTransform_eq_unifOI_and_ae_eq_quantile`
- `Toolkit.Tricks.Statistics.Asymptotics.measureReal_ge_le_of_condExp_le`
- `Toolkit.Tricks.Statistics.Asymptotics.tendstoInProbability_zero_of_condExp_le_of_tendstoInProbability_zero`
- `Toolkit.Foundations.Probability.Moments.abs_posPart_sub_sub_mul_indicator_le_indicator`
- `Toolkit.Foundations.Probability.Moments.measureReal_Ioc_min_max_le_of_local_bound`
- `Toolkit.Foundations.Probability.Moments.abs_integral_posPart_sub_sub_mul_indicator_le_mul_measureReal_Ioc`
- `Toolkit.Foundations.Probability.Moments.abs_integral_posPart_sub_sub_mul_indicator_le`
- `Toolkit.Foundations.Algebra.Order.sum_zipWith_orderedInsert_le_of_monge`
- `Toolkit.Foundations.Algebra.Order.sum_zipWith_insertionSort_le_of_monge`
- `Toolkit.Foundations.Algebra.Order.sum_zipWith_mergeSort_le_of_monge`
- `Toolkit.Foundations.Algebra.Order.abs_sub_add_abs_sub_le_of_le`
- `Toolkit.Foundations.Algebra.Order.sum_zipWith_abs_sub_mergeSort_le`

## Self-containment

Checked when this directory was written: every import of every file resolves to a file here or to a module of a required library, no path in a lakefile leaves this directory, and nothing names the machine it was built on.

