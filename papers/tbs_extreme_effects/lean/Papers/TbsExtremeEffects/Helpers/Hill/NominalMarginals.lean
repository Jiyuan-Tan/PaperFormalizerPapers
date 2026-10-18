module
public import Papers.TbsExtremeEffects.Helpers.Hill.CappedMoments
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Exact nominal Pareto type-II marginal tails for the Hill convolution proof. -/

@[expose] public section
namespace Papers.TbsExtremeEffects
open MeasureTheory Filter
open scoped ENNReal Topology

/-- [A positive tail index](hyp:hb) makes [the type-II Pareto density nonnegative at every supplied point](goal). -/
-- @node: hill_paretoII_density_nonneg
lemma hill_paretoII_density_nonneg {beta : ℝ} (hb : 0 < beta) (x : ℝ) :
    0 ≤ paretoIIDensity beta x := by
  unfold paretoIIDensity
  split_ifs with hx
  · positivity
  · exact le_rfl

/-- [For the supplied tail index](hyp:beta), [the type-II Pareto density is measurable](goal). -/
-- @node: hill_paretoII_density_measurable
@[fun_prop] lemma hill_paretoII_density_measurable (beta : ℝ) :
    Measurable (paretoIIDensity beta) := by
  unfold paretoIIDensity
  exact Measurable.ite measurableSet_Ioi (by fun_prop) measurable_const

/-- [A positive tail index](hyp:hb) and [a nonnegative threshold](hyp:hr) imply that [the density mass above that threshold](goal) equals the type-II Pareto survival expression. -/
-- @node: hill_paretoII_tail_integral
lemma hill_paretoII_tail_integral {beta r : ℝ} (hb : 0 < beta) (hr : 0 ≤ r) :
    (∫ x in Set.Ioi r, paretoIIDensity beta x) = (1 + r) ^ (-beta) := by
  have hInt : IntegrableOn (fun x : ℝ => beta * (x + 1) ^ (-(beta + 1)))
      (Set.Ioi r) :=
    (integrableOn_add_rpow_Ioi_of_lt (by linarith : -(beta + 1) < -1)
      (by linarith : -(1 : ℝ) < r)).const_mul beta
  have hderiv : ∀ x ∈ Set.Ici r,
      HasDerivAt (fun x : ℝ => -(x + 1) ^ (-beta))
        (beta * (x + 1) ^ (-(beta + 1))) x := by
    intro x hx
    have hd := (((hasDerivAt_id x).add_const 1).rpow_const
      (p := -beta) (Or.inl (by linarith [Set.mem_Ici.mp hx] : x + 1 ≠ 0))).neg
    convert! hd using 1
    simp only [id_eq, one_mul, neg_mul, neg_neg,
      show -(beta + 1) = -beta - 1 by ring]
  have hlim : Tendsto (fun x : ℝ => -(x + 1) ^ (-beta)) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop hb).comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_id)).neg
  calc
    _ = ∫ x in Set.Ioi r, beta * (x + 1) ^ (-(beta + 1)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      simp only [paretoIIDensity, if_pos (hr.trans_lt hx), add_comm 1 x]
    _ = _ := by
      simpa only [zero_sub, neg_neg, add_comm r 1] using
        integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hInt hlim

/-- If [the measure has a type-II Pareto law](hyp:hnu) and [the threshold is nonnegative](hyp:hr), then [its real-valued probability above the threshold](goal) is the type-II Pareto survival expression. -/
-- @node: hill_paretoII_survival
lemma hill_paretoII_survival {nu : Measure ℝ} {beta r : ℝ}
    (hnu : IsParetoTypeII nu beta) (hr : 0 ≤ r) :
    nu.real (Set.Ioi r) = (1 + r) ^ (-beta) := by
  rw [hnu.density, Measure.real, withDensity_apply _ measurableSet_Ioi]
  rw [← integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (hill_paretoII_density_nonneg hnu.beta_pos))
    (hill_paretoII_density_measurable beta).aestronglyMeasurable]
  exact hill_paretoII_tail_integral hnu.beta_pos hr

/-- If [the measure has a type-II Pareto law](hyp:hnu), then [a draw from it is nonnegative almost surely](goal). -/
-- @node: hill_paretoII_nonneg_ae
lemma hill_paretoII_nonneg_ae {nu : Measure ℝ} {beta : ℝ}
    (hnu : IsParetoTypeII nu beta) : ∀ᵐ x ∂nu, 0 ≤ x := by
  rw [hnu.density, ae_withDensity_iff
    (hill_paretoII_density_measurable beta).ennreal_ofReal]
  apply Eventually.of_forall
  intro x hx
  by_contra hneg
  have hxzero : paretoIIDensity beta x = 0 := by
    simp [paretoIIDensity, not_lt.mpr (not_le.mp hneg).le]
  exact hx (by rw [hxzero, ENNReal.ofReal_zero])

/-- Given [a positive scale](hyp:ha), [a nonnegative threshold](hyp:hx), [a measurable weighted outcome](hyp:hW), and [a type-II Pareto law for that outcome divided by the scale](hyp:hLaw), [the survival probability of the unscaled outcome](goal) is the stated type-II Pareto expression. -/
-- @node: hill_scaled_paretoII_survival
lemma hill_scaled_paretoII_survival {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : Ω → ℝ) {beta a x : ℝ}
    (ha : 0 < a) (hx : 0 ≤ x) (hW : Measurable W)
    (hLaw : IsParetoTypeII (P.map (fun z => W z / a)) beta) :
    P.real {z | x < W z} = (1 + x / a) ^ (-beta) := by
  have h := hill_paretoII_survival hLaw (div_nonneg hx ha.le)
  rw [Measure.real, Measure.map_apply (by fun_prop) measurableSet_Ioi] at h
  have hset : (fun z => W z / a) ⁻¹' Set.Ioi (x / a) = {z | x < W z} := by
    ext z
    exact div_lt_div_iff_of_pos_right ha
  rw [hset] at h
  exact h

/-- Given [a positive scale](hyp:ha), [a measurable weighted outcome](hyp:hW), and [a type-II Pareto law after division by that scale](hyp:hLaw), [every positive threshold has the stated polynomial upper-tail bound](goal). -/
-- @node: hill_scaled_paretoII_polynomial_tail
lemma hill_scaled_paretoII_polynomial_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : Ω → ℝ) {beta a : ℝ}
    (ha : 0 < a) (hW : Measurable W)
    (hLaw : IsParetoTypeII (P.map (fun z => W z / a)) beta) :
    ∀ x > 0, P.real {z | x < W z} ≤ a ^ beta * x ^ (-beta) := by
  intro x hx
  rw [hill_scaled_paretoII_survival P W ha hx.le hW hLaw]
  calc
    _ ≤ (x / a) ^ (-beta) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith [hLaw.beta_pos])
    _ = a ^ beta * x ^ (-beta) := by
      rw [Real.div_rpow hx.le ha.le, Real.rpow_neg ha.le, div_inv_eq_mul, mul_comm]

/-- Given [a positive scale](hyp:ha), [a measurable weighted outcome](hyp:hW), and [a type-II Pareto law after scaling](hyp:hLaw), [the unscaled outcome is nonnegative almost surely](goal). -/
-- @node: hill_scaled_paretoII_nonneg_ae
lemma hill_scaled_paretoII_nonneg_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : Ω → ℝ) {beta a : ℝ}
    (ha : 0 < a) (hW : Measurable W)
    (hLaw : IsParetoTypeII (P.map (fun z => W z / a)) beta) :
    ∀ᵐ z ∂P, 0 ≤ W z := by
  have h := (ae_map_iff (by fun_prop : AEMeasurable (fun z => W z / a) P)
    measurableSet_Ici).mp (hill_paretoII_nonneg_ae hLaw)
  exact h.mono (fun z hz => (nonneg_of_mul_nonneg_left hz (inv_pos.mpr ha)))

/-- [For component scales](hyp:a), [tail index](hyp:beta), [radius](hyp:r), [convolution multiplier](hyp:kappa), [density](hyp:density), and [error budget](hyp:budget), [the Pareto-data condition](goal) says there is a probability law with measurable scaled type-II component marginals, whose [density partition identity](step:1) and [numerical remainder bound](step:2) hold.

Marginal type-II laws suffice for these residual envelopes; independence is used later for the convolution partition. -/
-- @node: HillLargestSummandParetoData
noncomputable def HillLargestSummandParetoData {m : ℕ} (a : Fin m → ℝ)
    (beta r kappa density budget : ℝ) : Prop :=
  ∃ (P : Measure (Fin m → ℝ)) (W : Fin m → (Fin m → ℝ) → ℝ),
    IsProbabilityMeasure P ∧ (∀ i, Measurable (W i)) ∧
    (∀ i, IsParetoTypeII (P.map (fun z => W i z / a i)) beta) ∧
    density = kappa * ∑ i, ∫ z,
      hillLargestSummandIntegrand a beta r (fun j => W j z) i ∂P ∧
    kappa * (∑ i : Fin m,
      ((beta * (a i) ^ beta * (beta + 1) * (r / 2) ^ (-beta - 2)) *
        (∑ j ∈ Finset.univ.erase i,
          hillCappedMomentEnvelope beta ((a j) ^ beta) (max 1 (r / 2))) +
        (beta * (a i) ^ beta * (r / m) ^ (-beta - 1)) *
          (((∑ j ∈ Finset.univ.erase i, (a j) ^ beta) * (m : ℝ) ^ beta) *
            (r / 2) ^ (-beta)))) ≤ budget

/-- Given [positive component scales](hyp:ha) and [Pareto marginal data](hyp:h), [the corresponding polynomial-tail data](goal) follow. -/
-- @node: hill_polynomial_data_of_pareto_data
lemma hill_polynomial_data_of_pareto_data {m : ℕ} (a : Fin m → ℝ)
    {beta r kappa density budget : ℝ} (ha : ∀ i, 0 < a i)
    (h : HillLargestSummandParetoData a beta r kappa density budget) :
    HillLargestSummandPolynomialData a beta r kappa density budget := by
  obtain ⟨P, W, hP, hW, hLaw, hpartition, hbudget⟩ := h
  refine ⟨P, W, (fun i => (a i) ^ beta), hP, hW, ?_, ?_, hpartition, hbudget⟩
  · rw [ae_all_iff]
    intro i
    exact hill_scaled_paretoII_nonneg_ae P (W i) (ha i) (hW i) (hLaw i)
  · intro i
    exact hill_scaled_paretoII_polynomial_tail P (W i) (ha i) (hW i) (hLaw i)

end Papers.TbsExtremeEffects
