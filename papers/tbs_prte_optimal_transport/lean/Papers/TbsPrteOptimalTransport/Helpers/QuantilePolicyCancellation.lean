module
public import Papers.TbsPrteOptimalTransport.Helpers.QuantilePropensityCancellation
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousPolicyBounds
/-! Quantile changes multiply centered policy residuals, even with fitted pooled denominators. -/
public section
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

-- @node: continuous_pooled_denominator_direction_regular
/-- If [a continuous nuisance direction is admissible at the given nuisance value](hyp:hd), [its pooled-denominator components are measurable and almost surely bounded in absolute value by a common nonnegative constant across all regular indices](goal). -/
lemma continuous_pooled_denominator_direction_regular (L : LevelData Z X)
    (eta del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl eta) (.inl del)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : RegularIndex L,
      Measurable (del.tauLev a) ∧ ∀ᵐ x ∂xLaw M, ‖del.tauLev a x‖ ≤ C := by
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  have h0 := hpath 0 (by simpa using hr)
  have ht := hpath (r/2) (by rw [abs_of_pos (by positivity)]; linarith)
  rcases h0 with ⟨_, _, _, _, _, _, hb0, hm0, _⟩
  rcases ht with ⟨_, _, _, _, _, _, hbt, hmt, _⟩
  refine ⟨2/r, by positivity, ?_⟩
  intro a
  apply affine_unit_direction_regular (xLaw M) (eta.tauLev a) (del.tauLev a) r hr
  · have hm : Measurable (fun x => eta.tauLev a x + 0 * del.tauLev a x) := hm0 a
    simpa only [zero_mul, add_zero] using hm
  · exact hmt a
  · have hb : ∀ᵐ x ∂xLaw M, eta.tauLev a x + 0 * del.tauLev a x ∈ Icc (0 : ℝ) 1 := hb0 a
    simpa only [zero_mul, add_zero] using hb
  · exact hbt a

-- @node: continuous_pooled_path_uniform_lower_bound
/-- Suppose [the policy preserves the propensity level ordering](hyp:hL), [the pooled policy probabilities satisfy overlap with the given constant](hyp:hov), and [the continuous nuisance direction is admissible at the truth](hyp:hd). Then [for all path values sufficiently close to zero and every regular index, the perturbed pooled denominator is almost surely at least half the overlap constant](goal). -/
lemma continuous_pooled_path_uniform_lower_bound
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi) (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del)) :
    ∀ᶠ t : ℝ in 𝓝 0, ∀ a : RegularIndex L, ∀ᵐ x ∂xLaw M,
      cpi/2 ≤ (trueNuisance M L + t • del).tauLev a x := by
  obtain ⟨C, hC, hreg⟩ := continuous_pooled_denominator_direction_regular M L
    (trueNuisance M L) del hd
  have hr : 0 < cpi / (2 * (C+1)) := div_pos hov.1 (by positivity)
  filter_upwards [continuousAt_id.abs.eventually_lt_const (by simpa using hr)] with t ht
  change |t| < cpi / (2 * (C+1)) at ht
  intro a
  filter_upwards [(hreg a).2] with x hx
  have hpi : cpi ≤ (trueNuisance M L).tauLev a x :=
    hov.2 x a.val.1 a.val.2 a.property.1 a.property.2.1 a.property.2.2
      (ordered_policy_level_nonempty M q L hL a.val.1 a.val.2 a.property.1
        a.property.2.1 a.property.2.2)
  have hmul : |t * del.tauLev a x| ≤ |t| * C := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hx)
      (abs_nonneg t)
  have hsmall := (lt_div_iff₀ (by positivity : 0 < 2 * (C+1))).mp ht
  change cpi/2 ≤ (trueNuisance M L).tauLev a x + t * del.tauLev a x
  nlinarith [neg_abs_le (t * del.tauLev a x), abs_nonneg t]

-- The true pooled mass divided by the fitted mass changes only the covariate
-- weight in the tower identity. Overlap bounds that ratio, so no additional
-- integrability assumption on an inverse weight is required.
-- @node: population_RqCont_fitted_pooled_denominator_zero
/-- Suppose [threshold crossing holds](hyp:h), [the policy derivative evaluated at the true propensity is jointly measurable](hyp:hdphi), [the policy derivative is bounded and Lipschitz](hyp:hDerivative), [the policy preserves the propensity level ordering](hyp:hL), and [policy overlap holds](hyp:hpol). If [each fitted pooled denominator is measurable](hyp:htau), [the denominator floor is positive](hyp:hc), [each fitted pooled denominator is almost surely above that floor](hyp:hclip), and [the covariate weight is measurable](hyp:hw) and [integrable](hyp:iw), [the weighted continuous policy residual at any regular index, using true nuisances except for the fitted pooled denominators, is integrable and has population mean zero](goal). -/
lemma population_RqCont_fitted_pooled_denominator_zero
    (h : ThresholdCrossing M) (dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (cpi : ℝ) (hpol : PolicyOverlap M L cpi)
    (tau : RegularIndex L → X → ℝ) (htau : ∀ a, Measurable (tau a))
    (c : ℝ) (hc : 0 < c) (hclip : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ tau a x)
    (a : RegularIndex L) (w : X → ℝ) (hw : Measurable w)
    (iw : Integrable w (xLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 *
      RqCont dphi L {trueNuisance M L with tauLev := tau} a.val.1 a.val.2 o)
      (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 *
      RqCont dphi L {trueNuisance M L with tauLev := tau} a.val.1 a.val.2 o
      ∂observationLaw M) = 0 := by
  let mass := (trueNuisance M L).tauLev a
  have hm : Measurable mass := population_instrument_set_probability_measurable M
    (L.T a.val.1 a.val.2)
  have hmass x : mass x ∈ Icc (0 : ℝ) 1 :=
    population_instrument_set_probability_range M (L.T a.val.1 a.val.2) x
  have hpos x : 0 < mass x := hpol.1.trans_le
    (hpol.2 x a.val.1 a.val.2 a.property.1 a.property.2.1 a.property.2.2
      (ordered_policy_level_nonempty M q L hL a.val.1 a.val.2 a.property.1
        a.property.2.1 a.property.2.2))
  let v := fun x => w x * (mass x / tau a x)
  have hv : Measurable v := by fun_prop
  have hratio : ∀ᵐ x ∂xLaw M, ‖mass x / tau a x‖ ≤ c⁻¹ := by
    filter_upwards [hclip a] with x hx
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (hmass x).1,
      abs_of_pos (hc.trans_le hx)]
    calc
      mass x / tau a x ≤ 1 / c := by gcongr; exact (hmass x).2
      _ = c⁻¹ := one_div c
  have iv : Integrable v (xLaw M) := by
    simpa only [v, Pi.div_apply, mul_comm] using
      iw.bdd_mul (hm.div (htau a)).aestronglyMeasurable hratio
  have ir := population_RqCont_integrable_of_integrable_weight M h dphi hdphi hDerivative
    q L hL cpi hpol a.val.1 a.val.2 a.property.1 v hv iv
  have zr := population_RqCont_weighted_integral_zero M h dphi hdphi L
    a.val.1 a.val.2 v hv ir
  have heq : (fun o : Obs X Z => w o.1 *
      RqCont dphi L {trueNuisance M L with tauLev := tau} a.val.1 a.val.2 o)
      =ᵐ[observationLaw M] (fun o => v o.1 *
        RqCont dphi L (trueNuisance M L) a.val.1 a.val.2 o) := by
    filter_upwards [observationLaw_covariate_ae M _ (hclip a)] with o ho
    have hbad : ¬ (a.val.2 = 0 ∨ L.l a.val.1 < a.val.2) := by
      have := a.property; omega
    simp only [RqCont, if_neg hbad, regularValue, dif_pos a.property]
    change w o.1 * ((tau a o.1)⁻¹ * _) =
      (w o.1 * (mass o.1 / tau a o.1)) * ((mass o.1)⁻¹ * _)
    field_simp [ne_of_gt (hc.trans_le ho), ne_of_gt (hpos o.1)]
  exact ⟨ir.congr heq.symm, (integral_congr_ae heq).trans zr⟩

-- Every displacement weight is integrable by admissibility, including the
-- fixed endpoint (whose displacement is zero). The fitted tau may move jointly.
-- @node: population_continuous_admissible_quantile_policy_zero
/-- Suppose [threshold crossing holds](hyp:h), [the policy derivative at the true propensity is jointly measurable](hyp:hdphi), [the derivative is bounded and Lipschitz](hyp:hDerivative), [the policy preserves the propensity level ordering](hyp:hL), [policy overlap holds](hyp:hpol), and [the continuous nuisance direction is admissible at the truth](hyp:hd). For [a level below the number of levels](hyp:hk) and [a boundary index no greater than that level's band count](hyp:hj), [at all path values sufficiently close to zero, the policy residual with perturbed pooled denominators, weighted by the perturbed product weight and quantile displacement, is integrable and has population mean zero](goal). -/
lemma population_continuous_admissible_quantile_policy_zero
    (h : ThresholdCrossing M) (dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (cpi : ℝ) (hpol : PolicyOverlap M L cpi) (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (k j : ℕ) (hk : k < L.K) (hj : j ≤ L.l k) (g : RegularIndex L) :
    ∀ᶠ t : ℝ in 𝓝 0,
      let path := trueNuisance M L + t • del
      let d := fun x => nuValue M {trueNuisance M L with nu := path.nu} k j x -
        bandBoundary M L k j x
      let R := RqCont dphi L {trueNuisance M L with tauLev := path.tauLev} k j
      Integrable (fun o : Obs X Z => (path.gamma g o.1 * d o.1) * R o)
        (observationLaw M) ∧
      (∫ o : Obs X Z, (path.gamma g o.1 * d o.1) * R o ∂observationLaw M) = 0 := by
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  filter_upwards [continuous_pooled_path_uniform_lower_bound M q L hL cpi hpol del hd,
    continuous_admissible_weighted_quantile_displacement_regular M L del hd k j hk hj g,
    continuousAt_id.abs.eventually_lt_const (by simpa using hr)] with t hclip hwd ht
  have had := hpath t ht
  rcases had with ⟨_, _, _, _, _, _, _, htm, _⟩
  dsimp only
  by_cases hj0 : j = 0
  · subst j
    simp only [RqCont, true_or, if_true, mul_zero, integral_zero]
    exact ⟨integrable_zero _ _ _, True.intro⟩
  · let a : RegularIndex L := ⟨(k,j), hk.le, by omega, hj⟩
    exact population_RqCont_fitted_pooled_denominator_zero M h dphi hdphi hDerivative
      q L hL cpi hpol (trueNuisance M L + t • del).tauLev htm
      (cpi/2) (div_pos hpol.1 (by norm_num)) hclip a
      (fun x => (trueNuisance M L + t • del).gamma g x *
        (nuValue M {trueNuisance M L with nu := (trueNuisance M L + t • del).nu} k j x -
          bandBoundary M L k j x)) hwd.1 hwd.2

-- These are the signed policy-residual terms in the quantile telescope of
-- the band score. Both endpoints, gamma, and tau vary on the same path.
-- @node: population_continuous_admissible_quantile_policy_orthogonality
/-- Suppose [threshold crossing holds](hyp:h), [the policy derivative at the true propensity is jointly measurable](hyp:hdphi), [the derivative is bounded and Lipschitz](hyp:hDerivative), [the policy preserves the propensity level ordering](hyp:hL), [policy overlap holds](hyp:hpol), and [the continuous nuisance direction is admissible at the truth](hyp:hd). For [a level below the number of levels](hyp:hk) and [a band index strictly below that level's band count](hyp:hj), [the population mean of the product-weighted difference between upper and lower quantile displacements times their policy residuals has derivative zero at the truth, with the product weights, quantiles, and pooled denominators varying along the same path](goal). -/
lemma population_continuous_admissible_quantile_policy_orthogonality
    (h : ThresholdCrossing M) (dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (cpi : ℝ) (hpol : PolicyOverlap M L cpi) (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (k j : ℕ) (hk : k < L.K) (hj : j < L.l k) (g : RegularIndex L) :
    let path := fun t : ℝ => trueNuisance M L + t • del
    let e := fun t => {trueNuisance M L with tauLev := (path t).tauLev, nu := (path t).nu}
    let b := fun t => {trueNuisance M L with tauLev := (path t).tauLev}
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z, (path t).gamma g o.1 *
      (-(nuValue M (e t) k j o.1 - bandBoundary M L k j o.1) *
          RqCont dphi L (b t) k j o +
        (nuValue M (e t) k (j+1) o.1 - bandBoundary M L k (j+1) o.1) *
          RqCont dphi L (b t) k (j+1) o) ∂observationLaw M) 0 0 := by
  dsimp only
  apply (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
  filter_upwards [population_continuous_admissible_quantile_policy_zero M h dphi hdphi
    hDerivative q L hL cpi hpol del hd k j hk hj.le g,
    population_continuous_admissible_quantile_policy_zero M h dphi hdphi
    hDerivative q L hL cpi hpol del hd k (j+1) hk (by omega) g] with t ha hb
  simp_rw [mul_add, neg_mul, mul_neg, ← mul_assoc]
  have hz := integral_add ha.1.neg hb.1
  simp only [Pi.neg_apply] at hz
  rw [integral_neg, ha.2, hb.2, neg_zero, add_zero] at hz
  simpa only [nuValue] using hz

end Papers.TbsPrteOptimalTransport
