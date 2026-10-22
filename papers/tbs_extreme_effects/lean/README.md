# Lean formalization — tbs_extreme_effects

A standalone Lake project: `Papers/TbsExtremeEffects/` is the Lean development of the corrected paper (136 file(s)). It depends on the public libraries listed below and on nothing else; what it uses of the author's own library is copied here.

## Build

Lean toolchain: `leanprover/lean4:v4.33.0` (`lean-toolchain`; `elan` installs it). From this directory:

```
lake exe cache get   # fetches the libraries and Mathlib's compiled files
lake build
lake env lean Check.lean   # the axioms of each result
```

`lake build` builds `Papers` and `Toolkit` (`Papers.TbsExtremeEffects` is the paper). There is no `lake-manifest.json`: Lake writes it on the first command, from the revisions the lakefile pins.

## Libraries it requires

- `Causalean` (Causal inference and statistics foundations (identification, estimation, semiparametrics, concentration).): `https://github.com/Jiyuan-Tan/CausalSmith` at `a7085d88d2e4b30003db7097ca374f4718da0f01`; it brings in `FoML`, `Optlib`
- `mathlib` (the Lean mathematical library): `https://github.com/leanprover-community/mathlib4` at `db584cd6d46c92f209a44c0f1c829460d327499d`
- `StatLean` (Mathematical statistics: estimation, hypothesis testing, asymptotic statistics, nonparametrics, time series (adapted Stat-Lean).): no public repository carries the adapted copy this was built with, so it is included in `vendor/StatLean/` with its licence (`vendor/StatLean/UPSTREAM.md`: where it comes from)

Verified: built against a local copy of Causalean (its commit 3292728656ff): 30 file(s) of it are reached, recorded by content hash in `built-against.json`. Each has the content it has at the public revision a7085d88d2e4 this bundle requires (compared over the network).

## The paper's results

- Proposition 3.3: `Papers.TbsExtremeEffects.nete_identification` (`Papers/TbsExtremeEffects/TId.lean:18`)
- Theorem 3.5: `Papers.TbsExtremeEffects.nete_rate` (`Papers/TbsExtremeEffects/TRate.lean:96`)
- Corollary 3.6: `Papers.TbsExtremeEffects.nete_dr_rate_adaptive_threshold` (`Papers/TbsExtremeEffects/TCorRate.lean:27`)
- Lemma A.1: `Papers.TbsExtremeEffects.adaptive_hill_rate` (`Papers/TbsExtremeEffects/Helpers/HillRate.lean:40`)
- Lemma A.2: `Papers.TbsExtremeEffects.eta_dr_rate` (`Papers/TbsExtremeEffects/Helpers/EtaDR.lean:420`)
- Lemma A.3: `Papers.TbsExtremeEffects.eta_ipw_rate` (`Papers/TbsExtremeEffects/Helpers/EtaIPW.lean:411`)
- Corollary A.4: `Papers.TbsExtremeEffects.nete_ipw_rate_adaptive_threshold` (`Papers/TbsExtremeEffects/TCorRateIpw.lean:30`)

`MATCH.md`, one directory up, sets each statement beside its declaration.

## Checking the axioms

`Check.lean` prints the axioms of each result above (`lake env lean Check.lean`, after the build): none may appear beyond `propext`, `Classical.choice` and `Quot.sound`. The source must contain no `sorry`, `admit` or `axiom`.

## What is in this directory

From the author's own library, copied here (13 module(s)): `Toolkit.Foundations.Probability.Concentration.ChernoffBounds`, `Toolkit.Foundations.Probability.Concentration.ExponentialSupermartingale`, `Toolkit.Foundations.Probability.Conditioning.ConditionalIntegrability`, `Toolkit.Foundations.Probability.Conditioning.ConditioningOnEvent`, `Toolkit.Foundations.Probability.Conditioning.JoinFactorization`, `Toolkit.Foundations.Probability.Distributions.DescendingOrderStatistics`, `Toolkit.Foundations.Probability.Distributions.DescendingSortMeasure`, `Toolkit.Foundations.Probability.Distributions.ExponentialOrderedDensity`, `Toolkit.Foundations.Probability.Distributions.ExponentialSpacings`, `Toolkit.Foundations.Probability.Distributions.NormalizedSpacingMap`, `Toolkit.Foundations.Probability.Distributions.SurvivalTransform`, `Toolkit.Foundations.Probability.Independence.Conditioning`, `Toolkit.Foundations.Probability.Independence.ProductConditioning`.

Imported from the required libraries: `Batteries` (1 module(s)), `Causalean` (10 module(s)), `Mathlib` (317 module(s)), `StatLean` (2 module(s)).

## Moved into the author's library

Results first proved for this paper and since moved into the library, where the paper now uses them:

- `Toolkit.Foundations.Probability.Conditioning.condExp_cond_ae_eq_condExp_of_measurableSet`
- `Toolkit.Foundations.Probability.Concentration.measureReal_exists_le_lt_le_exp_of_supermartingale_exp`
- `Toolkit.Foundations.Probability.Conditioning.integrable_mul_of_integrable_condExp_mul`
- `Toolkit.Foundations.Probability.Concentration.supermartingale_exp_mul_sub_of_condExp_exp_increment_le`
- `Toolkit.Foundations.Probability.Independence.map_prodMk_cond_preimage_eq_prod`
- `Toolkit.Foundations.Probability.Independence.cond_pi_univ_pi`
- `Toolkit.Foundations.Probability.Concentration.mgf_sum_le_exp_of_mem_Icc`
- `Toolkit.Foundations.Probability.Concentration.measureReal_sum_le_le_exp_of_mem_Icc_of_nonpos`
- `Toolkit.Foundations.Probability.Concentration.measureReal_sum_le_one_sub_mul_le_exp_of_mem_Icc`
- `Toolkit.Foundations.Probability.Distributions.sortDescending`
- `Toolkit.Foundations.Probability.Distributions.normalizedSpacingLinear`
- `Toolkit.Foundations.Probability.Distributions.normalizedSpacingMap`
- `Toolkit.Foundations.Probability.Distributions.normalizedSpacingMap_apply`
- `Toolkit.Foundations.Probability.Distributions.measurable_normalizedSpacingMap`
- `Toolkit.Foundations.Probability.Distributions.antitone_sortDescending`
- `Toolkit.Foundations.Probability.Distributions.sortDescending_comp_perm`
- `Toolkit.Foundations.Probability.Distributions.sortDescending_eq_comp_of_antitone`
- `Toolkit.Foundations.Probability.Distributions.descendingChamber`
- `Toolkit.Foundations.Probability.Distributions.measurable_sortDescending`
- `Toolkit.Foundations.Probability.Distributions.measurableSet_descendingChamber`
- `Toolkit.Foundations.Probability.Distributions.volume_equal_coordinate_zero`
- `Toolkit.Foundations.Probability.Distributions.volume_descendingChamber_decomposition`
- `Toolkit.Foundations.Probability.Distributions.map_sortDescending_restrict_descendingChamber`
- `Toolkit.Foundations.Probability.Distributions.map_sortDescending_volume`
- `Toolkit.Foundations.Probability.Distributions.map_sortDescending_withDensity`
- `Toolkit.Foundations.Probability.Distributions.normalizedSpacingLinear_det`
- `Toolkit.Foundations.Probability.Distributions.map_normalizedSpacingMap_volume`
- `Toolkit.Foundations.Probability.Distributions.normalizedSpacingMap_nonneg_iff`
- `Toolkit.Foundations.Probability.Distributions.sum_normalizedSpacingMap`
- `Toolkit.Foundations.Probability.Distributions.map_normalizedSpacingMap_withDensity_pullback`
- `Toolkit.Foundations.Probability.Distributions.exponentialProductDensity`
- `Toolkit.Foundations.Probability.Distributions.orderedExponentialDensity`
- `Toolkit.Foundations.Probability.Distributions.pi_expMeasure_eq_withDensity`
- `Toolkit.Foundations.Probability.Distributions.measurable_exponentialProductDensity`
- `Toolkit.Foundations.Probability.Distributions.exponentialProductDensity_comp_perm`
- `Toolkit.Foundations.Probability.Distributions.map_sortDescending_pi_expMeasure`
- `Toolkit.Foundations.Probability.Distributions.orderedExponentialDensity_eq_spacing_pullback`
- `Toolkit.Foundations.Probability.Distributions.map_normalizedSpacing_sortDescending_pi_expMeasure`
- `Toolkit.Foundations.Probability.Distributions.normalizedSpacing`
- `Toolkit.Foundations.Probability.Distributions.measurable_normalizedSpacing`
- `Toolkit.Foundations.Probability.Distributions.iIndepFun_normalizedSpacing_and_map_eq_expMeasure`
- `Toolkit.Foundations.Probability.Distributions.measureReal_Ioi_eq_one_sub_cdf`
- `Toolkit.Foundations.Probability.Distributions.measurable_neg_log_measureReal_Ioi`
- `Toolkit.Foundations.Probability.Distributions.map_neg_log_one_sub_uniform01_eq_expMeasure`
- `Toolkit.Foundations.Probability.Distributions.map_neg_log_one_sub_cdf_eq_expMeasure`
- `Toolkit.Foundations.Probability.Distributions.map_neg_log_measureReal_Ioi_eq_expMeasure`

## Self-containment

Checked when this directory was written: every import of every file resolves to a file here or to a module of a required library, no path in a lakefile leaves this directory, and nothing names the machine it was built on.

