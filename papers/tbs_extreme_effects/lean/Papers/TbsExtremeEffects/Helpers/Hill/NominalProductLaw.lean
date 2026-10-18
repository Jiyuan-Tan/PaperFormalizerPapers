module
public import Papers.TbsExtremeEffects.Helpers.Hill.NominalMarginals
public import Mathlib.MeasureTheory.Integral.Pi
/-! The nominal Pareto product law, weighted marginals, and independence. -/
@[expose] public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators

/-- For [a finite family of sigma-finite measures](hyp:mu), [measurable nonnegative integrands](hyp:f), and [their measurability](hyp:hf), [the integral of their product under the product measure](goal) factors into the product of their integrals. -/
-- @node: hill_lintegral_fin_prod
lemma hill_lintegral_fin_prod {n : ℕ} (mu : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (mu i)] (f : Fin n → ℝ → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    (∫⁻ z, ∏ i, f i (z i) ∂Measure.pi mu) = ∏ i, ∫⁻ x, f i x ∂mu i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← (measurePreserving_piFinSuccAbove mu 0).symm.lintegral_comp_emb
      (MeasurableEquiv.measurableEmbedding _)]
    simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
      Fin.zero_succAbove, cast_eq, Fin.cons_zero]
    rw [lintegral_prod_mul (μ := mu 0) (ν := Measure.pi (fun i => mu i.succ))
      (f := f 0) (g := fun z : Fin n → ℝ => ∏ i, f i.succ (z i))
      (hf 0).aemeasurable
      ((Finset.measurable_prod Finset.univ (fun i _ =>
        (hf i.succ).comp (measurable_pi_apply i))).aemeasurable)]
    rw [ih (fun i => mu i.succ) (fun i => f i.succ) (fun i => hf i.succ)]

/-- [A positive tail index](hyp:hb) ensures that [the nonnegative integral of the type-II Pareto density](goal) is one. -/
-- @node: hill_paretoII_lintegral
lemma hill_paretoII_lintegral {beta : ℝ} (hb : 0 < beta) :
    (∫⁻ x, ENNReal.ofReal (paretoIIDensity beta x)) = 1 := by
  have hzero : (fun x => ENNReal.ofReal (paretoIIDensity beta x)) =
      Set.indicator (Set.Ioi 0) (fun x => ENNReal.ofReal (paretoIIDensity beta x)) := by
    funext x
    by_cases hx : 0 < x <;> simp [Set.indicator, hx, paretoIIDensity]
  rw [hzero, lintegral_indicator measurableSet_Ioi]
  have h := hill_paretoII_tail_integral hb (le_refl (0 : ℝ))
  -- prove finiteness from integrability of the shifted density
  have hInt : IntegrableOn (paretoIIDensity beta) (Set.Ioi 0) := by
    have hpow := (integrableOn_add_rpow_Ioi_of_lt
      (by linarith : -(beta + 1) < -1) (by norm_num : -(1 : ℝ) < 0)).const_mul beta
    apply hpow.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simp [paretoIIDensity, Set.mem_Ioi.mp hx, add_comm]
  rw [← ofReal_integral_eq_lintegral_ofReal hInt
    (Eventually.of_forall (hill_paretoII_density_nonneg hb)), h]
  simp

/-- [A positive tail index](hyp:hb) makes [the measure formed from the type-II Pareto density](goal) a probability measure. -/
-- @node: hill_paretoII_probability
lemma hill_paretoII_probability {beta : ℝ} (hb : 0 < beta) :
    IsProbabilityMeasure (volume.withDensity
      (fun x => ENNReal.ofReal (paretoIIDensity beta x))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    hill_paretoII_lintegral hb]

/-- For a tail index, [the nominal component density](goal) agrees almost everywhere with the product of the one-dimensional type-II Pareto densities. -/
-- @node: hill_nominal_density_product_ae
lemma hill_nominal_density_product_ae {m : ℕ} (beta : ℝ) :
    hillNominalComponentDensity beta =ᵐ[volume]
      (fun z : Fin m → ℝ => ∏ i, paretoIIDensity beta (z i)) := by
  classical
  have hne : ∀ᵐ z : Fin m → ℝ ∂volume, ∀ i, z i ≠ 0 := by
    rw [ae_all_iff]
    intro i
    exact Measure.ae_eval_ne (fun _ : Fin m => (volume : Measure ℝ)) i 0
  filter_upwards [hne] with z hz
  by_cases horth : z ∈ nonnegativeOrthant
  · have hpos : ∀ i, 0 < z i := fun i => lt_of_le_of_ne (horth i) (hz i).symm
    simp_rw [hillNominalComponentDensity, if_pos horth, paretoProductDensity,
      paretoIIDensity, if_pos (hpos _)]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · have hneg : ∃ i, ¬ 0 ≤ z i := by
      simpa only [nonnegativeOrthant, Set.mem_ofPred_eq, not_forall] using horth
    obtain ⟨i, hi⟩ := hneg
    have hprod : (∏ j, paretoIIDensity beta (z j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by
        simp [paretoIIDensity, not_lt.mpr (not_le.mp hi).le])
    simp [hillNominalComponentDensity, horth, hprod]

/-- [A positive tail index](hyp:hb) implies that [the nominal component law](goal) is the product of identical one-dimensional type-II Pareto laws. -/
-- @node: hill_nominal_law_eq_pi
lemma hill_nominal_law_eq_pi {m : ℕ} {beta : ℝ} (hb : 0 < beta) :
    hillNominalComponentLaw beta m = Measure.pi (fun _ : Fin m =>
      volume.withDensity (fun x => ENNReal.ofReal (paretoIIDensity beta x))) := by
  have hP := hill_paretoII_probability hb
  let := hP
  rw [hillNominalComponentLaw]
  have hd : (fun z : Fin m → ℝ => ENNReal.ofReal (hillNominalComponentDensity beta z))
      =ᵐ[volume] (fun z => ∏ i, ENNReal.ofReal (paretoIIDensity beta (z i))) := by
    filter_upwards [hill_nominal_density_product_ae (m := m) beta] with z hz
    rw [hz, ENNReal.ofReal_prod_of_nonneg (fun i _ => hill_paretoII_density_nonneg hb _)]
  rw [withDensity_congr_ae hd]
  apply (Measure.pi_eq (fun s hs => ?_)).symm
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  change (∫⁻ z, ∏ i, ENNReal.ofReal (paretoIIDensity beta (z i))
    ∂(Measure.pi (fun _ : Fin m => (volume : Measure ℝ))).restrict (Set.univ.pi s)) = _
  rw [Measure.restrict_pi_pi, hill_lintegral_fin_prod _ _
    (fun _ => (hill_paretoII_density_measurable beta).ennreal_ofReal)]
  apply Finset.prod_congr rfl
  intro i _
  rw [withDensity_apply _ (hs i)]

/-- [A positive tail index](hyp:hb) and [the number of components](hyp:m) ensure that [the nominal component law](goal) is a probability measure. -/
-- @node: hill_nominal_probability
lemma hill_nominal_probability {beta : ℝ} (hb : 0 < beta) (m : ℕ) :
    IsProbabilityMeasure (hillNominalComponentLaw beta m) := by
  rw [hill_nominal_law_eq_pi hb]
  let := hill_paretoII_probability hb
  infer_instance

/-- [A positive tail index](hyp:hb) and [a chosen coordinate](hyp:i) imply that [that coordinate under the nominal component law](goal) has a type-II Pareto distribution. -/
-- @node: hill_nominal_coordinate_law
lemma hill_nominal_coordinate_law {m : ℕ} {beta : ℝ} (hb : 0 < beta) (i : Fin m) :
    IsParetoTypeII ((hillNominalComponentLaw beta m).map (fun z => z i)) beta := by
  refine ⟨hb, ?_⟩
  rw [hill_nominal_law_eq_pi hb]
  let := hill_paretoII_probability hb
  exact (measurePreserving_eval _ i).map_eq

/-- Given [a positive tail index](hyp:hb), [component weights](hyp:a), [positive weights](hyp:ha), and [a selected coordinate](hyp:i), [the weighted coordinate divided by its weight](goal) has a type-II Pareto distribution. -/
-- @node: hill_nominal_weighted_coordinate_law
lemma hill_nominal_weighted_coordinate_law {m : ℕ} {beta : ℝ}
    (hb : 0 < beta) (a : Fin m → ℝ) (ha : ∀ i, 0 < a i) (i : Fin m) :
    IsParetoTypeII ((hillNominalComponentLaw beta m).map
      (fun z => (a i * z i) / a i)) beta := by
  simpa only [mul_div_cancel_left₀ _ (ha i).ne'] using hill_nominal_coordinate_law hb i

/-- [A positive tail index](hyp:hb) and [component weights](hyp:a) imply that [the weighted nominal coordinates](goal) are mutually independent. -/
-- @node: hill_nominal_weighted_independent
lemma hill_nominal_weighted_independent {m : ℕ} {beta : ℝ}
    (hb : 0 < beta) (a : Fin m → ℝ) :
    iIndepFun (fun i (z : Fin m → ℝ) => a i * z i) (hillNominalComponentLaw beta m) := by
  rw [hill_nominal_law_eq_pi hb]
  let := hill_paretoII_probability hb
  exact iIndepFun_pi (fun i => (by fun_prop : Measurable (fun x : ℝ => a i * x)).aemeasurable)

/-- [For component scales](hyp:a), [tail index](hyp:beta), [radius](hyp:r), [convolution multiplier](hyp:kappa), [density](hyp:density), and [error budget](hyp:budget), [the nominal-data condition](goal) consists of [a nominal-law density partition identity](step:1) and [a numerical remainder budget](step:2).

Its probability law and component marginals are derived from the original product density. -/
-- @node: HillNominalLargestSummandData
noncomputable def HillNominalLargestSummandData {m : ℕ} (a : Fin m → ℝ)
    (beta r kappa density budget : ℝ) : Prop :=
  density = kappa * ∑ i, ∫ z,
    hillLargestSummandIntegrand a beta r (fun j => a j * z j) i
      ∂hillNominalComponentLaw beta m ∧
  kappa * (∑ i : Fin m,
    ((beta * (a i) ^ beta * (beta + 1) * (r / 2) ^ (-beta - 2)) *
      (∑ j ∈ Finset.univ.erase i,
        hillCappedMomentEnvelope beta ((a j) ^ beta) (max 1 (r / 2))) +
      (beta * (a i) ^ beta * (r / m) ^ (-beta - 1)) *
        (((∑ j ∈ Finset.univ.erase i, (a j) ^ beta) * (m : ℝ) ^ beta) *
          (r / 2) ^ (-beta)))) ≤ budget

/-- Given [positive tail index](hyp:hb), [positive component scales](hyp:ha), and [nominal convolution data](hyp:h), [the corresponding Pareto marginal data](goal) can be constructed. -/
-- @node: hill_pareto_data_of_nominal_data
lemma hill_pareto_data_of_nominal_data {m : ℕ} (a : Fin m → ℝ)
    {beta r kappa density budget : ℝ} (hb : 0 < beta) (ha : ∀ i, 0 < a i)
    (h : HillNominalLargestSummandData a beta r kappa density budget) :
    HillLargestSummandParetoData a beta r kappa density budget := by
  refine ⟨hillNominalComponentLaw beta m, (fun i z => a i * z i),
    hill_nominal_probability hb m, ?_, ?_, h.1, h.2⟩
  · intro i
    fun_prop
  · exact hill_nominal_weighted_coordinate_law hb a ha
end Papers.TbsExtremeEffects
