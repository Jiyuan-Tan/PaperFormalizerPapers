module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLGammaPolicyResidual
/-! Signed lower and upper policy corrections in the continuous product score.
The paired finite block has finite second moment and converges in L2 from the
encoded nuisance rates and clipped policy denominators. -/
@[expose] public section

set_option linter.style.openClassical false
set_option linter.unnecessarySimpa false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]

-- @node: continuousPairedPolicyBlock
/-- For [a latent instrumental-variable model](hyp:M), [a policy derivative indexed by instrument, covariates, and propensity](hyp:dphi), [a finite level structure](hyp:L), [continuous nuisance functions for those levels](hyp:e), and [an observed covariate, instrument, treatment, and outcome tuple](hyp:o), the [paired continuous policy correction](goal) sums over all regular blocks the regular coefficient times the upper quantile-weighted policy residual minus the lower quantile-weighted policy residual. -/
noncomputable def continuousPairedPolicyBlock
    (M : LatentIVModel Ω X Z) (dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e : NuisanceCont L) (o : Obs X Z) : ℝ :=
  ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
    regularValue e.gamma k j o.1 *
      (-nuValue M e k (j-1) o.1 * RqCont dphi L e k (j-1) o +
        nuValue M e k j o.1 * RqCont dphi L e k j o)

-- @node: continuous_paired_policy_block_decomposition
/-- [The paired continuous policy correction equals the sum of the regular-coefficient-weighted upper quantile policy residuals minus the corresponding sum of lower quantile policy residuals](goal). -/
lemma continuous_paired_policy_block_decomposition
    (M : LatentIVModel Ω X Z) (dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e : NuisanceCont L) (o : Obs X Z) :
    continuousPairedPolicyBlock M dphi L e o =
      (∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
        regularValue e.gamma k j o.1 * (nuValue M e k j o.1 * RqCont dphi L e k j o)) -
      ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
        regularValue e.gamma k j o.1 *
          (nuValue M e k (j-1) o.1 * RqCont dphi L e k (j-1) o) := by
  simp only [continuousPairedPolicyBlock, neg_mul, neg_add_eq_sub, mul_sub,
    Finset.sum_sub_distrib]

-- @node: fitted_continuous_paired_policy_block_memLp
/-- If [the policy is a policy map](hyp:hphi), [its specified derivative is valid](hyp:hd), [that derivative is bounded and Lipschitz](hyp:hDerivative), [the continuous nuisance functions are admissible](hyp:he), [the denominator lower bound is positive](hyp:hc), and [every regular policy denominator exceeds that bound almost everywhere](hyp:hclip), then [the paired continuous policy correction is square-integrable under the observation law](goal). -/
lemma fitted_continuous_paired_policy_block_memLp
    (M : LatentIVModel Ω X Z) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ r : RegularIndex L, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x) :
    MemLp (continuousPairedPolicyBlock M dphi L e) 2 (observationLaw M) := by
  convert (fitted_continuous_gamma_policy_block_memLp M phi dphi hphi hd
    hDerivative L e he c hc hclip true).sub
    (fitted_continuous_gamma_policy_block_memLp M phi dphi hphi hd
      hDerivative L e he c hc hclip false) using 1
  funext o
  simp only [Pi.sub_apply, continuous_paired_policy_block_decomposition,
    Bool.false_eq_true, if_false, if_true]

-- @node: encoded_continuous_paired_policy_block_sq_tendsto_probability_zero
/-- Suppose [the policy is a policy map](hyp:hphi), [its specified derivative is valid](hyp:hd), [that derivative is bounded and Lipschitz](hyp:hDerivative), [the true continuous nuisance is admissible](hyp:he0), [all fitted nuisances satisfy continuous clipping](hyp:hclip), [their shares lie in their simplices](hyp:hshares), [all encoded fitted components are measurable](hyp:hm), and [the encoded components satisfy the finite nuisance rates](hyp:hr). Under [policy overlap at the specified overlap constant](hyp:hov) and [clipping of every fitted denominator relative to that constant](hyp:hden), [the observation-law integrated squared difference between fitted and true paired continuous policy corrections converges in probability to zero along even sample sizes](goal). -/
lemma encoded_continuous_paired_policy_block_sq_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L)))
    (cpi : ℝ) (hov : PolicyOverlap M L cpi)
    (hden : ∀ n t, ContDenominatorsClipped L (eh n t) cpi)
    : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o : Obs X Z,
        (continuousPairedPolicyBlock M dphi L (eh (2*(n+1)) t) o -
          continuousPairedPolicyBlock M dphi L (trueNuisance M L) o)^2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  have hc : 0 < cpi/2 := by linarith [hov.1]
  have hd0 (r : RegularIndex L) : ∀ᵐ x ∂xLaw M,
      cpi/2 ≤ (trueNuisance M L).tauLev r x := by
    have hne := continuous_admissible_policy_nonempty M L _ he0 r
    apply Eventually.of_forall
    intro x
    have hx : cpi ≤ (trueNuisance M L).tauLev r x :=
      hov.2 x r.val.1 r.val.2 r.property.1 r.property.2.1 r.property.2.2 hne
    linarith [hov.1]
  let B := fun (upper : Bool) (e : NuisanceCont L) (o : Obs X Z) =>
    ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
      regularValue e.gamma k j o.1 *
        (nuValue M e k (if upper then j else j-1) o.1 *
          RqCont dphi L e k (if upper then j else j-1) o)
  let F := fun upper n t o => B upper (er (2*(n+1)) t) o - B upper (trueNuisance M L) o
  have hmem upper n t : MemLp (F upper n t) 2 (observationLaw M) :=
    (fitted_continuous_gamma_policy_block_memLp M phi dphi hphi hd hDerivative
      L _ (her _ t) (cpi/2) hc (fun r => Eventually.of_forall (fun x =>
        ((hden (2*(n+1)) t).2 r x (contFittedSharesSimplex_policy_nonempty L (eh (2*(n+1)) t)
          (hshares (2*(n+1)) t) r)).1)) upper).sub
    (fitted_continuous_gamma_policy_block_memLp M phi dphi hphi hd hDerivative
      L _ he0 (cpi/2) hc hd0 upper)
  have hrF upper : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o, (F upper n t o)^2 ∂observationLaw M) atTop (fun _ _ => 0) := by
    simpa only [F, B, er, restrictContShares, regularValue, nuValue, RqCont] using
      encoded_continuous_gamma_policy_block_sq_tendsto_probability_zero
        M μ phi dphi hphi hd hDerivative L he0 eh hclip hshares hm hr cpi hov hden upper
  have hz : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun _ : ℕ => fun _ : A => (0 : ℝ)) atTop (fun _ _ => 0) := by
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
    intro eps heps
    simpa [not_le_of_gt heps] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
  have hs := dml_three_term_sq_tendsto_probability_zero μ (observationLaw M)
    (F true) (fun _ _ _ => 0) (F false) (hmem true) (fun _ _ => MemLp.zero)
    (hmem false) (hrF true) (by simpa using hz) (hrF false)
  have hrestriction upper n t o : B upper (er n t) o = B upper (eh n t) o := by
    simp only [B, er, restrictContShares, regularValue, nuValue, RqCont]
  convert hs using 1
  funext n t
  congr 1
  funext o
  simp only [continuous_paired_policy_block_decomposition, F, hrestriction, B,
    Bool.false_eq_true, if_false, if_true]
  ring

-- @node: encoded_continuous_paired_policy_block_l2_tendsto_probability_zero
/-- Suppose [the policy is a policy map](hyp:hphi), [its specified derivative is valid](hyp:hd), [that derivative is bounded and Lipschitz](hyp:hDerivative), [the true continuous nuisance is admissible](hyp:he0), [all fitted nuisances satisfy continuous clipping](hyp:hclip), [their shares lie in their simplices](hyp:hshares), [all encoded fitted components are measurable](hyp:hm), and [the encoded components satisfy the finite nuisance rates](hyp:hr). Under [policy overlap at the specified overlap constant](hyp:hov) and [clipping of every fitted denominator relative to that constant](hyp:hden), [the observation-law L2 distance between fitted and true paired continuous policy corrections converges in probability to zero along even sample sizes](goal). -/
lemma encoded_continuous_paired_policy_block_l2_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L)))
    (cpi : ℝ) (hov : PolicyOverlap M L cpi)
    (hden : ∀ n t, ContDenominatorsClipped L (eh n t) cpi)
    : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => Real.sqrt (∫ o : Obs X Z,
        (continuousPairedPolicyBlock M dphi L (eh (2*(n+1)) t) o -
          continuousPairedPolicyBlock M dphi L (trueNuisance M L) o)^2
        ∂observationLaw M)) atTop (fun _ _ => 0) := by
  have hs := encoded_continuous_paired_policy_block_sq_tendsto_probability_zero
    M μ phi dphi hphi hd hDerivative L he0 eh hclip hshares hm hr cpi hov hden
  have hcont : Continuous (fun t : ℝ => Real.sqrt t) := by fun_prop
  simpa only [Real.sqrt_zero] using
    Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt hcont.continuousAt hs

end Papers.TbsPrteOptimalTransport
