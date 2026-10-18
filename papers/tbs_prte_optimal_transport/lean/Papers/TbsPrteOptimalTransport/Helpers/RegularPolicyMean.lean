module
public import Papers.TbsPrteOptimalTransport.Helpers.RegularRegressionMean
public import Papers.TbsPrteOptimalTransport.Helpers.WeightedPooledPopulation
/-! Population tower transfer for the jointly fitted binary regular policy corrections. -/
@[expose] public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- The null-set clipping used by the tower proof yields measurable versions of
-- both moving branch weights. Their bounds hold even at fitted branch ties.
-- @node: binary_regular_policy_branch_versions
/-- For [an admissible policy](hyp:hphi) and [an admissible binary nuisance](hyp:he),
[the fitted active indicator and its product with the lower-dominance indicator have
measurable versions, each bounded in norm by one everywhere and equal to the original
branch coefficient almost everywhere under the covariate law](goal). -/
lemma binary_regular_policy_branch_versions
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e) (k j : ℕ) :
    ∃ I EI : X → ℝ, Measurable I ∧ Measurable EI ∧
      (∀ x, ‖I x‖ ≤ 1) ∧ (∀ x, ‖EI x‖ ≤ 1) ∧
      I =ᵐ[xLaw M] Iact phi L e k j ∧
      EI =ᵐ[xLaw M] (fun x => Edom phi L e k j x * Iact phi L e k j x) := by
  let pc := fun z x => max 0 (min 1 (e.prop z x))
  let ep : NuisanceBin L := {e with prop := pc}
  have hpc z : Measurable (pc z) := by
    have hm := he.2.1 z
    dsimp only [pc]
    fun_prop
  have hpcR : ∀ z x, pc z x ∈ Icc (0 : ℝ) 1 := fun z x =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hq i := binary_pooledQBin_measurable_of_pointwise_range phi hphi L ep
    hpc hpcR (fun a => (he.2.2.2.1 a).1) (he.2.2.2.2.2.2.2.1) k i
  have hpos i : Measurable (positiveValue ep.pLev i) := by
    unfold positiveValue
    split_ifs
    · exact (he.2.2.2.1 _).1
    · fun_prop
  have hP i : Measurable (positiveValue ep.P1 i) := by
    unfold positiveValue
    split_ifs
    · exact (he.2.2.2.1 _).2.1
    · fun_prop
  have hb : Measurable (fun x => positiveValue ep.pLev (k+1) x - binFullJ L ep k x) := by
    first | fun_prop | exact (hpos (k+1)).sub ((hP (k+1)).sub (hP k))
  have hE := binary_Edom_measurable phi L ep k j (hq (j-1)) hb
  have hI := binary_Iact_measurable phi L ep k j (hq j) (hq (j-1)) hb
  have heq : ∀ᵐ x ∂xLaw M, ∀ i,
      pooledQBin phi L ep k i x = pooledQBin phi L e k i x := by
    filter_upwards [ae_all_iff.mpr he.1] with x hx
    intro i
    simp only [pooledQBin, ep]
    split_ifs
    · rfl
    · rfl
    · apply Finset.sum_congr rfl
      intro z hz
      simp only [pc, min_eq_right (hx z).2, max_eq_right (hx z).1]
    · simp only [zero_mul, Finset.sum_const_zero]
  refine ⟨Iact phi L ep k j, fun x => Edom phi L ep k j x * Iact phi L ep k j x,
    hI, hE.mul hI, ?_, ?_, ?_, ?_⟩
  · intro x
    unfold Iact indicator
    split_ifs <;> norm_num
  · intro x
    dsimp only
    unfold Edom Iact indicator
    split_ifs <;> norm_num
  · filter_upwards [heq] with x hx
    simp only [Iact, hx j, hx (j-1)]
    rfl
  · filter_upwards [heq] with x hx
    simp only [Edom, Iact, hx j, hx (j-1)]
    rfl

-- Using observation-space versions on both sides lets these means combine
-- directly with the four regression corrections. Invalid policy indices
-- have the actual score's structural-zero convention.
-- @node: population_RqBin_weighted_observation_mean_of_admissible
/-- Under [threshold crossing](hyp:h), for [an admissible policy](hyp:hphi) with
[derivative dphi](hyp:hDiff) that [is bounded and Lipschitz](hyp:hDerivative), and
[an admissible binary nuisance](hyp:he), suppose [c is positive](hyp:hc) and [every
fitted pooling denominator is at least c almost everywhere](hyp:hden). If [k does not
exceed the last treatment level](hyp:hk), [the weight is measurable](hyp:hw), and
[its norm is bounded by B almost everywhere](hyp:hwB), [the weighted pooled policy
residual and its instrument-probability-weighted evaluation at the true propensity
are integrable under the observation law and have equal integrals](goal). -/
lemma population_RqBin_weighted_observation_mean_of_admissible
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e)
    (c : ℝ) (hc : 0 < c) (hden : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev a x)
    (k j : ℕ) (hk : k ≤ L.K) (w : X → ℝ) (hw : Measurable w)
    (B : ℝ) (hwB : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ B) :
    Integrable (fun o : Obs X Z => w o.1 * RqBin dphi L e k j o) (observationLaw M) ∧
    Integrable (fun o : Obs X Z => w o.1 * ∑ z, instProb M z o.1 *
      RqBin dphi L e k j (o.1,z,M.prop z o.1,0)) (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 * RqBin dphi L e k j o ∂observationLaw M) =
      ∫ o : Obs X Z, w o.1 * ∑ z, instProb M z o.1 *
        RqBin dphi L e k j (o.1,z,M.prop z o.1,0) ∂observationLaw M := by
  by_cases hj : j = 0 ∨ L.l k < j
  · simp only [RqBin, if_pos hj, mul_zero, Finset.sum_const_zero]
    exact ⟨integrable_zero _ _ _, integrable_zero _ _ _, True.intro⟩
  · have ha : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k := by omega
    let a : RegularIndex L := ⟨(k,j), ha⟩
    have hr := population_RqBin_weighted_finite_mean_of_binary_admissible M h
      phi dphi hphi hDiff hDerivative L e he a c hc (hden a) w hw B hwB
    have hobs := M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
    have hmap : (observationLaw M).map Prod.fst = xLaw M := by
      simpa only [observationLaw, xLaw, Function.comp_def] using
        Measure.map_map measurable_fst hobs
    have hi : Integrable (fun x => w x * ∑ z, instProb M z x *
        RqBin dphi L e k j (x,z,M.prop z x,0)) ((observationLaw M).map Prod.fst) := by
      rw [hmap]
      exact hr.2.1
    refine ⟨hr.1, (integrable_map_measure hi.aestronglyMeasurable
      measurable_fst.aemeasurable).mp hi, ?_⟩
    rw [hr.2.2, ← hmap]
    exact integral_map measurable_fst.aemeasurable hi.aestronglyMeasurable

-- Both moving policy coefficients are derived from admissibility. In
-- particular no branch measurability or residual integrability is assumed.
-- @node: population_binary_regular_policy_correction_fitted_mean
/-- Under [threshold crossing](hyp:h), [an admissible policy](hyp:hphi),
[differentiability with derivative dphi](hyp:hDiff), [a bounded Lipschitz derivative](hyp:hDerivative),
and [an admissible binary nuisance](hyp:he), assume [c is positive](hyp:hc) and [the
fitted pooling denominators are at least c almost everywhere](hyp:hden). For [k no
larger than the last treatment level](hyp:hk) and [a measurable covariate weight](hyp:hw)
whose [norm is at most B almost everywhere](hyp:hwB), [the weighted active upper policy
residual minus the active lower-dominance policy residual and its instrument-averaged
representation at the true propensity are integrable and have equal observation-law integrals](goal). -/
lemma population_binary_regular_policy_correction_fitted_mean
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e)
    (c : ℝ) (hc : 0 < c) (hden : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev a x)
    (k j : ℕ) (hk : k ≤ L.K) (w : X → ℝ) (hw : Measurable w)
    (B : ℝ) (hwB : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ B) :
    Integrable (fun o : Obs X Z => w o.1 *
      (Iact phi L e k j o.1 * RqBin dphi L e k j o -
        Edom phi L e k j o.1 * Iact phi L e k j o.1 * RqBin dphi L e k (j-1) o))
      (observationLaw M) ∧
    Integrable (fun o : Obs X Z => w o.1 *
      (Iact phi L e k j o.1 * (∑ z, instProb M z o.1 *
          RqBin dphi L e k j (o.1,z,M.prop z o.1,0)) -
        Edom phi L e k j o.1 * Iact phi L e k j o.1 * (∑ z, instProb M z o.1 *
          RqBin dphi L e k (j-1) (o.1,z,M.prop z o.1,0)))) (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 *
      (Iact phi L e k j o.1 * RqBin dphi L e k j o -
        Edom phi L e k j o.1 * Iact phi L e k j o.1 * RqBin dphi L e k (j-1) o)
      ∂observationLaw M) =
      ∫ o : Obs X Z, w o.1 *
        (Iact phi L e k j o.1 * (∑ z, instProb M z o.1 *
            RqBin dphi L e k j (o.1,z,M.prop z o.1,0)) -
          Edom phi L e k j o.1 * Iact phi L e k j o.1 * (∑ z, instProb M z o.1 *
            RqBin dphi L e k (j-1) (o.1,z,M.prop z o.1,0))) ∂observationLaw M := by
  obtain ⟨I, EI, hI, hEI, hIb, hEIb, hIe, hEIe⟩ :=
    binary_regular_policy_branch_versions M phi hphi L e he k j
  have hb (f : X → ℝ) (hf : ∀ x, ‖f x‖ ≤ 1) :
      ∀ᵐ x ∂xLaw M, ‖w x * f x‖ ≤ B := by
    filter_upwards [hwB] with x hx
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hf x) (norm_nonneg _)).trans (by simpa using hx)
  have hp := population_RqBin_weighted_observation_mean_of_admissible M h phi dphi
    hphi hDiff hDerivative L e he c hc hden k j hk (fun x => w x * I x)
    (hw.mul hI) B (hb I hIb)
  have hm := population_RqBin_weighted_observation_mean_of_admissible M h phi dphi
    hphi hDiff hDerivative L e he c hc hden k (j-1) hk (fun x => w x * EI x)
    (hw.mul hEI) B (hb EI hEIb)
  have hoI := observationLaw_covariate_ae M _ hIe
  have hoEI := observationLaw_covariate_ae M _ hEIe
  have hobs : (fun o : Obs X Z => (w o.1 * I o.1) * RqBin dphi L e k j o -
      (w o.1 * EI o.1) * RqBin dphi L e k (j-1) o) =ᵐ[observationLaw M]
      (fun o => w o.1 * (Iact phi L e k j o.1 * RqBin dphi L e k j o -
        Edom phi L e k j o.1 * Iact phi L e k j o.1 * RqBin dphi L e k (j-1) o)) := by
    filter_upwards [hoI, hoEI] with o hi hei
    rw [hi, hei]
    ring
  have hmean : (fun o : Obs X Z => (w o.1 * I o.1) *
      (∑ z, instProb M z o.1 * RqBin dphi L e k j (o.1,z,M.prop z o.1,0)) -
      (w o.1 * EI o.1) * (∑ z, instProb M z o.1 *
        RqBin dphi L e k (j-1) (o.1,z,M.prop z o.1,0))) =ᵐ[observationLaw M]
      (fun o => w o.1 * (Iact phi L e k j o.1 *
        (∑ z, instProb M z o.1 * RqBin dphi L e k j (o.1,z,M.prop z o.1,0)) -
        Edom phi L e k j o.1 * Iact phi L e k j o.1 *
          (∑ z, instProb M z o.1 * RqBin dphi L e k (j-1) (o.1,z,M.prop z o.1,0)))) := by
    filter_upwards [hoI, hoEI] with o hi hei
    rw [hi, hei]
    ring
  refine ⟨(hp.1.sub' hm.1).congr hobs, (hp.2.1.sub' hm.2.1).congr hmean, ?_⟩
  rw [← integral_congr_ae hobs, ← integral_congr_ae hmean,
    integral_sub hp.1 hm.1, integral_sub hp.2.1 hm.2.1, hp.2.2, hm.2.2]

-- The true law fixes the finite conditional policy residual mean; every
-- fitted coefficient and denominator remains visible in this expression.
-- @node: binaryRegularPolicyMean
/-- For [a latent instrumental-variable model](hyp:M), [a policy](hyp:phi), [its
candidate derivative](hyp:dphi), [level data](hyp:L), [a fitted binary nuisance](hyp:e),
[a treatment interval k](hyp:k), [a policy index j](hyp:j), and [covariates x](hyp:x),
[the regular binary policy correction mean](goal) is the active upper pooled policy
residual averaged over the instrument at the true propensity, minus the analogous
lower pooled residual weighted by both the active and lower-dominance indicators. -/
noncomputable def binaryRegularPolicyMean (M : LatentIVModel Ω X Z)
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e : NuisanceBin L)
    (k j : ℕ) (x : X) : ℝ :=
  Iact phi L e k j x * (∑ z, instProb M z x * RqBin dphi L e k j (x,z,M.prop z x,0)) -
    Edom phi L e k j x * Iact phi L e k j x *
      (∑ z, instProb M z x * RqBin dphi L e k (j-1) (x,z,M.prop z x,0))

-- This combines the actual six corrections, including moving active branches,
-- and is the tower step needed before the integrated quadratic remainder.
-- @node: population_binary_regular_component_correction_fitted_mean
/-- Under [threshold crossing](hyp:h), [an admissible policy](hyp:hphi), [policy
differentiability with derivative dphi](hyp:hDiff), [a bounded Lipschitz derivative](hyp:hDerivative),
[invariant level ordering](hyp:hOrder), [baseline overlap with constant cpi](hyp:hov),
[binary outcomes almost surely](hyp:hy), and [admissible true](hyp:he0) and [fitted
binary nuisances](hyp:he), suppose [c is positive](hyp:hc), [fitted assignment masses](hyp:hpi)
and [pooling denominators](hyp:htau) are at least c almost everywhere. For [k no larger
than the last treatment level](hyp:hk) and [a measurable weight](hyp:hw) whose [norm
is bounded by B almost everywhere](hyp:hwB), [the weighted component score minus its
fitted hinge and the weighted sum of its regression and policy correction means are
integrable and have equal observation-law integrals](goal). -/
lemma population_binary_regular_component_correction_fitted_mean
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hy : OutcomeBinaryAE M)
    (he0 : BinAdmissible M L (eta0Bin M L)) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (c : ℝ) (hc : 0 < c)
    (hpi : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ e.piLev a x)
    (htau : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev a x)
    (k j : ℕ) (hk : k ≤ L.K) (w : X → ℝ) (hw : Measurable w)
    (B : ℝ) (hwB : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ B) :
    Integrable (fun o : Obs X Z => w o.1 *
      (binScoreComponents phi dphi L e k j o - hMinus phi L e k j o.1))
      (observationLaw M) ∧
    Integrable (fun o : Obs X Z => w o.1 *
      (binaryRegularRegressionMean phi L (eta0Bin M L) e k j o.1 +
        binaryRegularPolicyMean M phi dphi L e k j o.1)) (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 *
      (binScoreComponents phi dphi L e k j o - hMinus phi L e k j o.1)
      ∂observationLaw M) =
      ∫ o : Obs X Z, w o.1 *
        (binaryRegularRegressionMean phi L (eta0Bin M L) e k j o.1 +
          binaryRegularPolicyMean M phi dphi L e k j o.1) ∂observationLaw M := by
  have hr := population_binary_regular_regression_correction_mean_of_admissible
    M h phi hphi L hOrder cpi hov hy he0 e he c hc hpi k j w hw B hwB
  have hp := population_binary_regular_policy_correction_fitted_mean M h phi dphi
    hphi hDiff hDerivative L e he c hc htau k j hk w hw B hwB
  have hf : (fun o : Obs X Z => w o.1 *
      (binScoreComponents phi dphi L e k j o - hMinus phi L e k j o.1)) =
      (fun o => w o.1 * binaryRegularRegressionCorrection phi L e k j o +
        w o.1 * (Iact phi L e k j o.1 * RqBin dphi L e k j o -
          Edom phi L e k j o.1 * Iact phi L e k j o.1 * RqBin dphi L e k (j-1) o)) := by
    funext o
    rw [binScoreComponents_regression_correction_decomposition]
    ring
  rw [hf]
  refine ⟨hr.1.fun_add hp.1, ?_, ?_⟩
  · simpa only [mul_add, binaryRegularPolicyMean] using hr.2.1.fun_add hp.2.1
  · simp_rw [mul_add, binaryRegularPolicyMean]
    rw [integral_add hr.1 hp.1, integral_add hr.2.1 hp.2.1, hr.2.2, hp.2.2]

-- The uniform direction bound supplies tau overlap for every policy level. The
-- fitted product gamma is bounded and measurable by admissibility, so this
-- transfer is uniform near zero along the entire affine nuisance vector.
-- @node: population_binary_regular_policy_path_local_mean
/-- Under [threshold crossing](hyp:h), [an admissible policy](hyp:hphi), [policy
differentiability with derivative dphi](hyp:hDiff), [a bounded Lipschitz derivative](hyp:hDerivative),
[invariant level ordering](hyp:hOrder), and [policy overlap with constant cpi](hyp:hov),
for [an admissible binary direction from the truth](hyp:hd), [all sufficiently small
path parameters simultaneously give integrability and equality of the policy correction
and its covariate mean, both weighted by the fitted regular product weight, for every
treatment index no larger than the last level and every policy index](goal). -/
lemma population_binary_regular_policy_path_local_mean
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del)) :
    ∀ᶠ t : ℝ in nhds 0, ∀ k j, k ≤ L.K →
      let e := eta0Bin M L + t • del
      let w := regularValue e.gamma k j
      Integrable (fun o : Obs X Z => w o.1 *
        (Iact phi L e k j o.1 * RqBin dphi L e k j o -
          Edom phi L e k j o.1 * Iact phi L e k j o.1 * RqBin dphi L e k (j-1) o))
        (observationLaw M) ∧
      Integrable (fun o : Obs X Z => w o.1 * binaryRegularPolicyMean M phi dphi L e k j o.1)
        (observationLaw M) ∧
      (∫ o : Obs X Z, w o.1 *
        (Iact phi L e k j o.1 * RqBin dphi L e k j o -
          Edom phi L e k j o.1 * Iact phi L e k j o.1 * RqBin dphi L e k (j-1) o)
        ∂observationLaw M) =
        ∫ o : Obs X Z, w o.1 * binaryRegularPolicyMean M phi dphi L e k j o.1
          ∂observationLaw M := by
  have hden : ∀ᶠ t : ℝ in nhds 0, ∀ a : RegularIndex L, ∀ᵐ x ∂xLaw M,
      cpi/2 ≤ (eta0Bin M L + t • del).tauLev a x := by
    obtain ⟨C, hC, hb⟩ := binary_pooled_denominator_direction_regular M L
      (eta0Bin M L) del hd
    have radius : 0 < cpi / (2*(C+1)) := by have := hov.1; positivity
    filter_upwards [continuousAt_id.abs.eventually_lt_const (by simpa using radius)]
      with t ht
    change |t| < cpi / (2*(C+1)) at ht
    intro a
    have hbase : ∀ x, cpi ≤ (eta0Bin M L).tauLev a x := fun x =>
      hov.2 x a.val.1 a.val.2 a.property.1 a.property.2.1 a.property.2.2
      (ordered_policy_level_nonempty M (policyProp phi M.prop) L hOrder
        a.val.1 a.val.2 a.property.1 a.property.2.1 a.property.2.2)
    filter_upwards [(hb a).2] with x hx
    simp only [Real.norm_eq_abs] at hx
    have hmul : |t * del.tauLev a x| ≤ |t| * C := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hx (abs_nonneg t)
    have hsmall := (lt_div_iff₀ (by positivity : 0 < 2*(C+1))).mp ht
    change cpi/2 ≤ (eta0Bin M L).tauLev a x + t * del.tauLev a x
    nlinarith [neg_abs_le (t * del.tauLev a x), abs_nonneg t, hbase x]
  obtain ⟨r, hr, hadm⟩ := hd.admissible
  filter_upwards [continuousAt_id.abs.eventually_lt_const (by simpa using hr), hden]
    with t ht hdt
  intro k j hk
  dsimp only
  let e := eta0Bin M L + t • del
  have he : BinAdmissible M L e := hadm t ht
  have hw : Measurable (regularValue e.gamma k j) := by
    first
    | fun_prop
    | unfold regularValue
      split_ifs
      · exact (he.2.2.2.2.2.1 _).2
      · fun_prop
  have hwB : ∀ᵐ x ∂xLaw M, ‖regularValue e.gamma k j x‖ ≤ 1 := by
    unfold regularValue
    split_ifs
    · filter_upwards [he.2.2.2.2.1 _] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg hx.2.1]
      exact hx.2.2
    · exact Eventually.of_forall (fun _ => by norm_num)
  exact population_binary_regular_policy_correction_fitted_mean M h phi dphi hphi hDiff
    hDerivative L e he (cpi/2) (by have := hov.1; positivity) hdt k j hk
    (regularValue e.gamma k j) hw 1 hwB

-- The whole regular component's correction is transferred simultaneously,
-- with the actual fitted product weight, before any derivative is taken.
-- @node: population_binary_regular_component_path_local_mean
/-- Under [threshold crossing](hyp:h), [an admissible policy](hyp:hphi), [policy
differentiability with derivative dphi](hyp:hDiff), [a bounded Lipschitz derivative](hyp:hDerivative),
[invariant level ordering](hyp:hOrder), [baseline overlap](hyp:hov), [policy overlap
with the same constant](hyp:hpol), and [binary outcomes almost surely](hyp:hy), for
[an admissible binary direction from the truth](hyp:hd), [all sufficiently small path
parameters simultaneously give integrability and equality of the component score minus
its fitted hinge and the sum of its regression and policy correction means, weighted by
the fitted regular product weight, for every treatment index no larger than the last
level and every policy index](goal). -/
lemma population_binary_regular_component_path_local_mean
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hpol : PolicyOverlap M L cpi) (hy : OutcomeBinaryAE M) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del)) :
    ∀ᶠ t : ℝ in nhds 0, ∀ k j, k ≤ L.K →
      let e := eta0Bin M L + t • del
      let w := regularValue e.gamma k j
      Integrable (fun o : Obs X Z => w o.1 *
        (binScoreComponents phi dphi L e k j o - hMinus phi L e k j o.1))
        (observationLaw M) ∧
      Integrable (fun o : Obs X Z => w o.1 *
        (binaryRegularRegressionMean phi L (eta0Bin M L) e k j o.1 +
          binaryRegularPolicyMean M phi dphi L e k j o.1)) (observationLaw M) ∧
      (∫ o : Obs X Z, w o.1 *
        (binScoreComponents phi dphi L e k j o - hMinus phi L e k j o.1)
        ∂observationLaw M) =
        ∫ o : Obs X Z, w o.1 *
          (binaryRegularRegressionMean phi L (eta0Bin M L) e k j o.1 +
            binaryRegularPolicyMean M phi dphi L e k j o.1) ∂observationLaw M := by
  filter_upwards [population_binary_regular_regression_path_local_mean M h phi hphi
    L hOrder cpi hov hy del hd, population_binary_regular_policy_path_local_mean M h
      phi dphi hphi hDiff hDerivative L hOrder cpi hpol del hd] with t hr hp
  intro k j hk
  dsimp only
  let e := eta0Bin M L + t • del
  let w := regularValue e.gamma k j
  have hreg := hr k j
  have hpolicy := hp k j hk
  have hf : (fun o : Obs X Z => w o.1 *
      (binScoreComponents phi dphi L e k j o - hMinus phi L e k j o.1)) =
      (fun o => w o.1 * binaryRegularRegressionCorrection phi L e k j o +
        w o.1 * (Iact phi L e k j o.1 * RqBin dphi L e k j o -
          Edom phi L e k j o.1 * Iact phi L e k j o.1 * RqBin dphi L e k (j-1) o)) := by
    funext o
    rw [binScoreComponents_regression_correction_decomposition]
    ring
  rw [hf]
  refine ⟨hreg.1.fun_add hpolicy.1, ?_, ?_⟩
  · simpa only [mul_add] using hreg.2.1.fun_add hpolicy.2.1
  · simp_rw [mul_add]
    rw [integral_add hreg.1 hpolicy.1, integral_add hreg.2.1 hpolicy.2.1,
      hreg.2.2, hpolicy.2.2]

end Papers.TbsPrteOptimalTransport
