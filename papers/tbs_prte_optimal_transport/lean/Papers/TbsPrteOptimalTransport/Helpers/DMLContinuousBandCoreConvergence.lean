module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLPairedPolicyBlock
public import Papers.TbsPrteOptimalTransport.Helpers.DMLGammaBandTreatment
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousBandShares
/-! Assembly of the continuous band mean and all stochastic residual corrections.
The quantile moment and the product-share correction are kept explicit in the
score decomposition. The assembled core converges in L2 under the encoded rates. -/
@[expose] public section
set_option linter.style.openClassical false

set_option linter.unnecessarySimpa false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
  [Fintype Z]

-- @node: continuousGammaBandCore
/-- For [a latent instrumental-variable model](hyp:M), [a policy derivative](hyp:dphi),
[a level and band specification](hyp:L), [continuous nuisance functions](hyp:e), and
[an observation](hyp:o), the [continuous gamma-weighted band core](goal) is the sum over levels and bands of the fitted band weight times the preceding band target and regression correction, plus the gamma-weighted lower and upper treatment-residual corrections and the paired policy correction. -/
noncomputable def continuousGammaBandCore (M : LatentIVModel Ω X Z)
    (dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e : NuisanceCont L)
    (o : Obs X Z) : ℝ :=
  (∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
    regularValue e.gamma k j o.1 *
      (contJ L e k (j-1) o.1 + continuousBandRegressionCorrection M L e k (j-1) o)) +
  (∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
    regularValue e.gamma k j o.1 *
      ((if k = 0 then 0 else alphaLow M L e k (j-1) o.1 * RpCont L e k o) +
        alphaHigh M L e k (j-1) o.1 * RpCont L e (k+1) o)) +
  continuousPairedPolicyBlock M dphi L e o

-- The two remaining terms are displayed rather than absorbed into a residual.
-- This equality includes the product-score correction and the shifted band index.
-- @node: continuous_fractional_product_score_core_decomposition
/-- [The sum of continuous fractional product scores over all levels and positive band indices equals the gamma-weighted band core plus the gamma-weighted difference of adjacent quantile moments and the band-share correction](goal).
Here each quantile moment is the upper level probability times its upper boundary regression, minus the lower level probability times its lower boundary regression, minus the pooled policy probability net of the lower level probability. -/
lemma continuous_fractional_product_score_core_decomposition
    (M : LatentIVModel Ω X Z) (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e : NuisanceCont L) (o : Obs X Z) :
    let moment := fun k b =>
      positiveValue e.pLev (k+1) o.1 * boundaryValue e.Mplus k b o.1 -
        positiveValue e.pLev k o.1 * minusBoundaryValue e.Mminus k b o.1 -
        (pooledQ phi L e k b o.1 - positiveValue e.pLev k o.1)
    (∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
      psiProd M phi dphi L e k j o) =
      continuousGammaBandCore M dphi L e o +
      (∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
        regularValue e.gamma k j o.1 *
          (nuValue M e k (j-1) o.1 * moment k (j-1) -
            nuValue M e k j o.1 * moment k j)) +
      continuousBandShareCorrection L e o := by
  dsimp only
  unfold continuousGammaBandCore continuousPairedPolicyBlock continuousBandShareCorrection
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro j hj
  have hj1 : j-1+1 = j := by have := (Finset.mem_Icc.mp hj).1; omega
  simp only [psiProd, continuous_band_score_regression_decomposition, hj1]
  ring

-- @node: continuousGammaBandCore_restrictContShares
/-- [Restricting the continuous nuisance shares leaves the gamma-weighted band core unchanged as a function of the observation](goal). -/
lemma continuousGammaBandCore_restrictContShares (M : LatentIVModel Ω X Z)
    (dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e : NuisanceCont L) :
    continuousGammaBandCore M dphi L (restrictContShares L e) =
      continuousGammaBandCore M dphi L e := by
  funext o
  simp only [continuousGammaBandCore, continuousPairedPolicyBlock,
    continuousBandRegressionCorrection, restrictContShares, regularValue, contJ,
    IFJ, IFM, nuValue, alphaLow, alphaHigh, RpCont, RqCont]

-- @node: fitted_continuous_gamma_band_core_memLp
/-- Suppose [the policy is a policy map](hyp:hphi), [its derivative is the specified policy derivative](hyp:hd),
[that derivative is bounded and Lipschitz](hyp:hDerivative), and [the continuous nuisances are admissible](hyp:he).
If [c is positive](hyp:hc), [all positive-level assignment probabilities are at least c almost surely](hyp:hpi), and
[all regular-band denominators are at least c almost surely](hyp:htau), then
[the fitted gamma-weighted band core is square integrable under the observation distribution](goal). -/
lemma fitted_continuous_gamma_band_core_memLp (M : LatentIVModel Ω X Z)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e)
    (c : ℝ) (hc : 0 < c)
    (hpi : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (htau : ∀ r : RegularIndex L, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x) :
    MemLp (continuousGammaBandCore M dphi L e) 2 (observationLaw M) := by
  exact ((fitted_continuous_gamma_regression_block_memLp M L e he c hc hpi).add
    (fitted_continuous_paired_band_treatment_block_memLp M L e he c hc hpi)).add
    (fitted_continuous_paired_policy_block_memLp M phi dphi hphi hd hDerivative
      L e he c hc htau)

-- @node: encoded_continuous_gamma_band_core_sq_tendsto_probability_zero
/-- Suppose [the policy is a policy map](hyp:hphi), [the specified derivative differentiates it](hyp:hd),
[the derivative is bounded and Lipschitz](hyp:hDerivative), and [the true continuous nuisances are admissible](hyp:he0).
Assume [all fitted nuisances satisfy continuous clipping](hyp:hclip), [their shares lie in the simplex](hyp:hshares),
[their encoded components are measurable](hyp:hm), [the boundary densities are bounded](hyp:hDensity),
[each encoded nuisance component's L2 error relative to truth is negligible in probability compared with the inverse fourth root of the sample size](hyp:hr),
[baseline overlap holds with constant cpi](hyp:hov), [policy overlap holds with that constant](hyp:hpol), and
[all fitted denominators satisfy clipping with that constant](hyp:hden).
Then [the observation mean of the squared difference between the fitted and true gamma-weighted band cores, using fits at sample sizes twice the quantity n + 1, converges to zero in probability](goal). -/
lemma encoded_continuous_gamma_band_core_sq_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hDensity : BoundaryDensitiesBounded M L)
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L)))
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hpol : PolicyOverlap M L cpi)
    (hden : ∀ n t, ContDenominatorsClipped L (eh n t) cpi) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o : Obs X Z,
        (continuousGammaBandCore M dphi L (eh (2*(n+1)) t) o -
          continuousGammaBandCore M dphi L (trueNuisance M L) o)^2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  have hc : 0 < cpi/2 := by linarith [hov.1]
  have hp0 (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, cpi/2 ≤ (trueNuisance M L).piLev i x := by
    apply Eventually.of_forall
    intro x
    have hx := hov.2 x i.val i.property.1 i.property.2
    change cpi/2 ≤ (levelSetProb M L).1 i.val x
    linarith [hov.1]
  have ht0 (r : RegularIndex L) :
      ∀ᵐ x ∂xLaw M, cpi/2 ≤ (trueNuisance M L).tauLev r x := by
    have hne := continuous_admissible_policy_nonempty M L _ he0 r
    apply Eventually.of_forall
    intro x
    have hx : cpi ≤ (trueNuisance M L).tauLev r x :=
      hpol.2 x r.val.1 r.val.2 r.property.1 r.property.2.1 r.property.2.2 hne
    linarith [hpol.1]
  let R := fun (e : NuisanceCont L) (o : Obs X Z) =>
    ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
      regularValue e.gamma k j o.1 *
        (contJ L e k (j-1) o.1 + continuousBandRegressionCorrection M L e k (j-1) o)
  let T := fun (e : NuisanceCont L) (o : Obs X Z) =>
    ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
      regularValue e.gamma k j o.1 *
        ((if k = 0 then 0 else alphaLow M L e k (j-1) o.1 * RpCont L e k o) +
          alphaHigh M L e k (j-1) o.1 * RpCont L e (k+1) o)
  let P := continuousPairedPolicyBlock M dphi L
  let F := fun n t o => R (er (2*(n+1)) t) o - R (trueNuisance M L) o
  let G := fun n t o => T (er (2*(n+1)) t) o - T (trueNuisance M L) o
  let H := fun n t o => -(P (er (2*(n+1)) t) o - P (trueNuisance M L) o)
  have hp n t (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, cpi/2 ≤ (er n t).piLev i x :=
    Eventually.of_forall (fun x => (hden n t).1 i x |>.1)
  have ht n t (r : RegularIndex L) :
      ∀ᵐ x ∂xLaw M, cpi/2 ≤ (er n t).tauLev r x :=
    Eventually.of_forall (fun x => ((hden n t).2 r x
      (contFittedSharesSimplex_policy_nonempty L (eh n t) (hshares n t) r)).1)
  have hF n t : MemLp (F n t) 2 (observationLaw M) :=
    (fitted_continuous_gamma_regression_block_memLp M L _ (her _ t)
      (cpi/2) hc (hp _ t)).sub
    (fitted_continuous_gamma_regression_block_memLp M L _ he0 (cpi/2) hc hp0)
  have hG n t : MemLp (G n t) 2 (observationLaw M) :=
    (fitted_continuous_paired_band_treatment_block_memLp M L _ (her _ t)
      (cpi/2) hc (hp _ t)).sub
    (fitted_continuous_paired_band_treatment_block_memLp M L _ he0 (cpi/2) hc hp0)
  have hH n t : MemLp (H n t) 2 (observationLaw M) :=
    ((fitted_continuous_paired_policy_block_memLp M phi dphi hphi hd hDerivative
      L _ (her _ t) (cpi/2) hc (ht _ t)).sub
    (fitted_continuous_paired_policy_block_memLp M phi dphi hphi hd hDerivative
      L _ he0 (cpi/2) hc ht0)).neg
  have hrF : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o, (F n t o)^2 ∂observationLaw M) atTop (fun _ _ => 0) := by
    simpa only [F, R, er, restrictContShares, regularValue, contJ,
      continuousBandRegressionCorrection, IFJ, IFM, nuValue] using
      encoded_continuous_gamma_regression_block_sq_tendsto_probability_zero
        M μ L he0 eh hclip hshares hm hDensity hr cpi hov hden
  have hrG : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o, (G n t o)^2 ∂observationLaw M) atTop (fun _ _ => 0) := by
    simpa only [G, T, er, restrictContShares, regularValue, alphaLow, alphaHigh,
      nuValue, RpCont] using
      encoded_continuous_paired_band_treatment_block_sq_tendsto_probability_zero
        M μ L he0 eh hclip hshares hm hr cpi hov hden
  have hrH : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o, (H n t o)^2 ∂observationLaw M) atTop (fun _ _ => 0) := by
    simpa only [H, P, er, continuousPairedPolicyBlock, restrictContShares,
      regularValue, nuValue, RqCont, neg_sq] using
      encoded_continuous_paired_policy_block_sq_tendsto_probability_zero
        M μ phi dphi hphi hd hDerivative L he0 eh hclip hshares hm hr cpi hpol hden
  have hs := dml_three_term_sq_tendsto_probability_zero μ (observationLaw M)
    F G H hF hG hH hrF hrG hrH
  have hid n t o : continuousGammaBandCore M dphi L (eh (2*(n+1)) t) o -
      continuousGammaBandCore M dphi L (trueNuisance M L) o = F n t o + G n t o - H n t o := by
    rw [← continuousGammaBandCore_restrictContShares M dphi L (eh (2*(n+1)) t)]
    simp only [continuousGammaBandCore, F, G, H, R, T, P, er]
    ring
  simpa only [← hid] using hs

-- @node: encoded_continuous_gamma_band_core_l2_tendsto_probability_zero
/-- Suppose [the policy is a policy map](hyp:hphi), [the specified derivative differentiates it](hyp:hd),
[the derivative is bounded and Lipschitz](hyp:hDerivative), and [the true continuous nuisances are admissible](hyp:he0).
Assume [all fitted nuisances satisfy continuous clipping](hyp:hclip), [the fitted shares lie in the simplex](hyp:hshares),
[the encoded fitted components are measurable](hyp:hm), [the boundary densities are bounded](hyp:hDensity),
[each encoded component's L2 error relative to truth is negligible in probability compared with the inverse fourth root of the sample size](hyp:hr),
[baseline overlap holds with constant cpi](hyp:hov), [policy overlap holds with that constant](hyp:hpol), and
[the fitted denominators satisfy clipping with that constant](hyp:hden).
Then [the L2 distance under the observation distribution between the fitted and true gamma-weighted band cores, using fits at sample sizes twice the quantity n + 1, converges to zero in probability](goal). -/
lemma encoded_continuous_gamma_band_core_l2_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hDensity : BoundaryDensitiesBounded M L)
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L)))
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hpol : PolicyOverlap M L cpi)
    (hden : ∀ n t, ContDenominatorsClipped L (eh n t) cpi) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => Real.sqrt (∫ o : Obs X Z,
        (continuousGammaBandCore M dphi L (eh (2*(n+1)) t) o -
          continuousGammaBandCore M dphi L (trueNuisance M L) o)^2
        ∂observationLaw M)) atTop (fun _ _ => 0) := by
  have hs := encoded_continuous_gamma_band_core_sq_tendsto_probability_zero
    M μ phi dphi hphi hd hDerivative L he0 eh hclip hshares hm hDensity hr cpi hov hpol hden
  have hcont : Continuous (fun t : ℝ => Real.sqrt t) := by fun_prop
  simpa only [Real.sqrt_zero] using
    Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt hcont.continuousAt hs


-- The remaining population quantile moment is an explicit algebraic term.
-- @node: continuousFractionalQuantileMoment
/-- For [a latent instrumental-variable model](hyp:M), [a policy function](hyp:phi),
[a level and band specification](hyp:L), [continuous nuisance functions](hyp:e), and
[an observation](hyp:o), the [continuous fractional quantile moment](goal) first
[forms at each boundary the upper level probability times the upper boundary regression, minus the lower level probability times the lower boundary regression, minus the pooled policy probability net of the lower level probability](step:1),
then [sums over levels and positive bands the band weight times the difference between the preceding and current boundary moments weighted by their respective quantile boundaries](step:2). -/
noncomputable def continuousFractionalQuantileMoment (M : LatentIVModel Ω X Z)
    (phi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e : NuisanceCont L)
    (o : Obs X Z) : ℝ :=
  let moment := fun k b =>
    positiveValue e.pLev (k+1) o.1 * boundaryValue e.Mplus k b o.1 -
      positiveValue e.pLev k o.1 * minusBoundaryValue e.Mminus k b o.1 -
      (pooledQ phi L e k b o.1 - positiveValue e.pLev k o.1)
  ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
    regularValue e.gamma k j o.1 *
      (nuValue M e k (j-1) o.1 * moment k (j-1) - nuValue M e k j o.1 * moment k j)

-- @node: continuous_fractional_score_sub_quantile_moment
/-- [The sum of continuous fractional product scores over all levels and positive bands, minus the continuous fractional quantile moment, equals the gamma-weighted band core plus the band-share correction](goal). -/
lemma continuous_fractional_score_sub_quantile_moment
    (M : LatentIVModel Ω X Z) (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e : NuisanceCont L) (o : Obs X Z) :
    (∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k), psiProd M phi dphi L e k j o) -
      continuousFractionalQuantileMoment M phi L e o =
    continuousGammaBandCore M dphi L e o + continuousBandShareCorrection L e o := by
  have h := continuous_fractional_product_score_core_decomposition M phi dphi L e o
  change _ = _ + continuousFractionalQuantileMoment M phi L e o + _ at h
  rw [h]
  ring

-- @node: fitted_continuous_fractional_score_sub_quantile_moment_memLp
/-- Suppose [the policy is a policy map](hyp:hphi), [the specified derivative differentiates it](hyp:hd),
[the derivative is bounded and Lipschitz](hyp:hDerivative), and [the continuous nuisances are admissible](hyp:he).
If [c is positive](hyp:hc), [all positive-level assignment probabilities are at least c almost surely](hyp:hpi), and
[all regular-band denominators are at least c almost surely](hyp:htau), then
[the summed continuous fractional product score minus its quantile moment is square integrable under the observation distribution](goal). -/
lemma fitted_continuous_fractional_score_sub_quantile_moment_memLp
    (M : LatentIVModel Ω X Z) (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e)
    (c : ℝ) (hc : 0 < c)
    (hpi : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (htau : ∀ r : RegularIndex L, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x) :
    MemLp (fun o : Obs X Z =>
      (∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k), psiProd M phi dphi L e k j o) -
        continuousFractionalQuantileMoment M phi L e o) 2 (observationLaw M) := by
  simp_rw [continuous_fractional_score_sub_quantile_moment]
  exact (fitted_continuous_gamma_band_core_memLp M phi dphi hphi hd hDerivative
    L e he c hc hpi htau).add (fitted_continuous_band_share_correction_memLp M L e he)

-- @node: encoded_continuous_fractional_score_sub_quantile_moment_sq_tendsto_probability_zero
/-- Suppose [the policy is a policy map](hyp:hphi), [the specified derivative differentiates it](hyp:hd),
[the derivative is bounded and Lipschitz](hyp:hDerivative), and [the true continuous nuisances are admissible](hyp:he0).
Assume [all fitted nuisances satisfy continuous clipping](hyp:hclip), [their shares lie in the simplex](hyp:hshares),
[their encoded components are measurable](hyp:hm), [the boundary densities are bounded](hyp:hDensity),
[each encoded nuisance component's L2 error relative to truth is negligible in probability compared with the inverse fourth root of the sample size](hyp:hr),
[baseline overlap holds with constant cpi](hyp:hov), [policy overlap holds with that constant](hyp:hpol), and
[all fitted denominators satisfy clipping with that constant](hyp:hden).
Then [the observation mean of the squared fitted-minus-true difference in the summed fractional product score after subtracting its quantile moment, using fits at sample sizes twice the quantity n + 1, converges to zero in probability](goal). -/
lemma encoded_continuous_fractional_score_sub_quantile_moment_sq_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hDensity : BoundaryDensitiesBounded M L)
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L)))
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hpol : PolicyOverlap M L cpi)
    (hden : ∀ n t, ContDenominatorsClipped L (eh n t) cpi) :
    let score := fun e o =>
      (∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k), psiProd M phi dphi L e k j o) -
        continuousFractionalQuantileMoment M phi L e o
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o : Obs X Z, (score (eh (2*(n+1)) t) o -
        score (trueNuisance M L) o)^2 ∂observationLaw M) atTop (fun _ _ => 0) := by
  dsimp only
  simp_rw [continuous_fractional_score_sub_quantile_moment]
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  let F := fun n t o => continuousGammaBandCore M dphi L (eh (2*(n+1)) t) o -
    continuousGammaBandCore M dphi L (trueNuisance M L) o
  let G := fun n t o => continuousBandShareCorrection L (eh (2*(n+1)) t) o -
    continuousBandShareCorrection L (trueNuisance M L) o
  have hc : 0 < cpi/2 := by linarith [hov.1]
  have hp0 (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, cpi/2 ≤ (trueNuisance M L).piLev i x := by
    apply Eventually.of_forall
    intro x
    have hx := hov.2 x i.val i.property.1 i.property.2
    change cpi/2 ≤ (levelSetProb M L).1 i.val x
    linarith [hov.1]
  have ht0 (r : RegularIndex L) :
      ∀ᵐ x ∂xLaw M, cpi/2 ≤ (trueNuisance M L).tauLev r x := by
    have hne := continuous_admissible_policy_nonempty M L _ he0 r
    apply Eventually.of_forall
    intro x
    have hx : cpi ≤ (trueNuisance M L).tauLev r x :=
      hpol.2 x r.val.1 r.val.2 r.property.1 r.property.2.1 r.property.2.2 hne
    linarith [hpol.1]
  have hF n t : MemLp (F n t) 2 (observationLaw M) := by
    have hfit := fitted_continuous_gamma_band_core_memLp M phi dphi hphi hd hDerivative
      L _ (her (2*(n+1)) t) (cpi/2) hc
      (fun i => Eventually.of_forall (fun x => (hden (2*(n+1)) t).1 i x |>.1))
      (fun r => Eventually.of_forall (fun x => ((hden (2*(n+1)) t).2 r x
        (contFittedSharesSimplex_policy_nonempty L (eh (2*(n+1)) t) (hshares (2*(n+1)) t) r)).1))
    rw [continuousGammaBandCore_restrictContShares] at hfit
    exact hfit.sub (fitted_continuous_gamma_band_core_memLp M phi dphi hphi hd hDerivative
      L _ he0 (cpi/2) hc hp0 ht0)
  have hG n t : MemLp (G n t) 2 (observationLaw M) := by
    have hfit := fitted_continuous_band_share_correction_memLp M L _ (her (2*(n+1)) t)
    convert hfit.sub (fitted_continuous_band_share_correction_memLp M L _ he0) using 1
    funext o
    simp only [G, er, Pi.sub_apply, continuousBandShareCorrection, restrictContShares,
      contJ, regularValue]
  have hz : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun (_ : ℕ) (_ : A) => (0 : ℝ)) atTop (fun _ _ => 0) := by
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
    intro eps heps
    simpa [not_le_of_gt heps] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
  have hs := dml_three_term_sq_tendsto_probability_zero μ (observationLaw M)
    F G (fun _ _ _ => 0) hF hG (fun _ _ => MemLp.zero')
    (encoded_continuous_gamma_band_core_sq_tendsto_probability_zero
      M μ phi dphi hphi hd hDerivative L he0 eh hclip hshares hm hDensity hr cpi hov hpol hden)
    (encoded_continuous_band_share_correction_sq_tendsto_probability_zero
      M μ L he0 eh hclip hshares hm hr) (by simpa using hz)
  convert hs using 1
  funext n t
  congr 1
  funext o
  dsimp only [F, G]
  ring

-- @node: encoded_continuous_fractional_score_sub_quantile_moment_l2_tendsto_probability_zero
/-- Suppose [the policy is a policy map](hyp:hphi), [the specified derivative differentiates it](hyp:hd),
[the derivative is bounded and Lipschitz](hyp:hDerivative), and [the true continuous nuisances are admissible](hyp:he0).
Assume [all fitted nuisances satisfy continuous clipping](hyp:hclip), [their shares lie in the simplex](hyp:hshares),
[their encoded components are measurable](hyp:hm), [the boundary densities are bounded](hyp:hDensity),
[each encoded component's L2 error relative to truth is negligible in probability compared with the inverse fourth root of the sample size](hyp:hr),
[baseline overlap holds with constant cpi](hyp:hov), [policy overlap holds with that constant](hyp:hpol), and
[the fitted denominators satisfy clipping with that constant](hyp:hden).
Then [the L2 distance under the observation distribution between the fitted and true summed fractional product scores after subtracting their respective quantile moments, using fits at sample sizes twice the quantity n + 1, converges to zero in probability](goal). -/
lemma encoded_continuous_fractional_score_sub_quantile_moment_l2_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hDensity : BoundaryDensitiesBounded M L)
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L)))
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hpol : PolicyOverlap M L cpi)
    (hden : ∀ n t, ContDenominatorsClipped L (eh n t) cpi) :
    let score := fun e o =>
      (∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k), psiProd M phi dphi L e k j o) -
        continuousFractionalQuantileMoment M phi L e o
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => Real.sqrt (∫ o : Obs X Z, (score (eh (2*(n+1)) t) o -
        score (trueNuisance M L) o)^2 ∂observationLaw M)) atTop (fun _ _ => 0) := by
  have hs := encoded_continuous_fractional_score_sub_quantile_moment_sq_tendsto_probability_zero
    M μ phi dphi hphi hd hDerivative L he0 eh hclip hshares hm hDensity hr cpi hov hpol hden
  have hcont : Continuous (fun t : ℝ => Real.sqrt t) := by fun_prop
  simpa only [Real.sqrt_zero] using
    Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt hcont.continuousAt hs

end Papers.TbsPrteOptimalTransport
