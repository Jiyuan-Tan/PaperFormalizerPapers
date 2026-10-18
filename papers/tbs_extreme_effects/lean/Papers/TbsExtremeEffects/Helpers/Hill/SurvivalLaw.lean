module
public import Papers.TbsExtremeEffects.Helpers.Hill.DensityContinuity
public import Causalean.Stat.OrderStatistic.CDFTransport
public import Papers.TbsExtremeEffects.Helpers.Hill.ExponentialLaw
public import Papers.TbsExtremeEffects.Helpers.Hill.SurvivalCoordinate
public import Toolkit.Foundations.Probability.Distributions.SurvivalTransform
/-! Atomlessness and exponential survival transforms of the full-input radial law. -/
public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators

/-- If [a density](hyp:h) [is measurable](hyp:hmeas), [vanishes outside the nonnegative orthant](hyp:hzero),
and [defines the given measure](hyp:hdensity), then [that measure is concentrated on the nonnegative orthant](goal).
@node: hill_component_orthant_ae -/
lemma hill_component_orthant_ae {m : ℕ} {nu : Measure (Fin m → ℝ)}
    (h : (Fin m → ℝ) → ℝ) (hmeas : Measurable h)
    (hzero : ∀ z, z ∉ nonnegativeOrthant → h z = 0)
    (hdensity : nu = volume.withDensity (fun z => ENNReal.ofReal (h z))) :
    ∀ᵐ z ∂nu, z ∈ nonnegativeOrthant := by
  rw [hdensity, ae_withDensity_iff (hmeas.ennreal_ofReal)]
  apply Eventually.of_forall
  intro z hz
  by_contra hn
  exact hz (by rw [hzero z hn, ENNReal.ofReal_zero])

/-- Under the [specified Pareto tail model](hyp:model), the distribution of the model's
radial variable [has no point masses](goal).
@node: hill_radial_atomless -/
lemma hill_radial_atomless {q d m : ℕ} (M : ExtremeModel q d) (tp : TailParams)
    (model : ParetoTailModel M m tp) : NullSingletonClass (M.mu.map (radius M)) := by
  classical
  obtain ⟨k, hk, nu, hclass, hlaw⟩ := model.density
  obtain ⟨_, h, hmeas, _, hzero, hdensity, _⟩ := hclass
  have hm : 0 < m := by
    obtain ⟨hd, hdm⟩ := model.constants.1
    omega
  let i : Fin m := ⟨0, hm⟩
  let a : Fin m → ℝ := fun j => l1Norm (fun r => model.A r j)
  have ha : a i ≠ 0 := (model.constants.2.1.trans_le (model.matrix.2.1 i).1).ne'
  have hrad : Measurable (fun z => l1Norm (model.A.mulVec z)) := by fun_prop
  have hmap : M.mu.map (radius M) = nu.map (fun z => l1Norm (model.A.mulVec z)) := by
    calc
      _ = (M.mu.map M.U).map l1Norm :=
        (Measure.map_map measurable_l1Norm M.measurable_U).symm
      _ = (nu.map (Matrix.mulVec model.A)).map l1Norm := by rw [hlaw]
      _ = _ := Measure.map_map measurable_l1Norm (by fun_prop)
  constructor
  intro r
  rw [hmap, Measure.map_apply hrad (measurableSet_singleton r)]
  have hne := (withDensity_absolutelyContinuous volume
    (fun z => ENNReal.ofReal (h z))).ae_le (hill_linear_sum_ne_ae_volume a i ha r)
  rw [← hdensity] at hne
  have hnull : ∀ᵐ z ∂nu, l1Norm (model.A.mulVec z) ≠ r := by
    filter_upwards [hne, hill_component_orthant_ae h hmeas hzero hdensity] with z hz horth
    rwa [hill_radial_matrix_sum model.A model.matrix.1 horth]
  simpa only [ae_iff, Set.preimage, Set.mem_singleton_iff, not_not] using hnull

/-- Applying the negative log-survival transform to a uniform random variable
[produces a standard exponential distribution](goal).
@node: hill_uniform_log_exponential -/
lemma hill_uniform_log_exponential :
    Causalean.Stat.OrderStatistic.uniform01.map (fun u : ℝ => -Real.log (1 - u)) =
      expMeasure 1 := by
  haveI : IsProbabilityMeasure Causalean.Stat.OrderStatistic.uniform01 := by
    constructor
    change (volume.restrict (Set.Icc (0 : ℝ) 1)) Set.univ = 1
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    norm_num
  have hmeas : Measurable (fun u : ℝ => -Real.log (1 - u)) := by fun_prop
  let := isProbabilityMeasure_expMeasure (by norm_num : (0 : ℝ) < 1)
  haveI : IsProbabilityMeasure
      (Causalean.Stat.OrderStatistic.uniform01.map (fun u : ℝ => -Real.log (1 - u))) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply hmeas measurableSet_Iic]
  change (volume.restrict (Set.Icc (0 : ℝ) 1)) _ = _
  rw [← restrict_Ioo_eq_restrict_Icc, Measure.restrict_apply' measurableSet_Ioo]
  rw [← ofReal_cdf (expMeasure 1) x, cdf_expMeasure_eq (by norm_num)]
  have hiff : ∀ u ∈ Set.Ioo (0 : ℝ) 1,
      -Real.log (1 - u) ≤ x ↔ u ≤ 1 - Real.exp (-x) := by
    intro u hu
    have hup : 0 < 1 - u := by linarith [hu.2]
    constructor
    · intro h
      have he := Real.exp_le_exp.mpr (show -x ≤ Real.log (1 - u) by linarith)
      rw [Real.exp_log hup] at he
      linarith
    · intro h
      have he : Real.exp (-x) ≤ 1 - u := by linarith
      have hl := Real.log_le_log (Real.exp_pos (-x)) he
      rw [Real.log_exp] at hl
      linarith
  by_cases hx : 0 ≤ x
  · rw [if_pos hx]
    have hpos := Real.exp_pos (-x)
    have hle : Real.exp (-x) ≤ 1 := by
      simpa using Real.exp_le_exp.mpr (show -x ≤ 0 by linarith)
    have hset : (fun u : ℝ => -Real.log (1 - u)) ⁻¹' Set.Iic x ∩ Set.Ioo 0 1 =
        Set.Ioc 0 (1 - Real.exp (-x)) := by
      ext u
      constructor
      · intro h
        exact ⟨h.2.1, (hiff u h.2).mp h.1⟩
      · intro h
        have hu : u ∈ Set.Ioo (0 : ℝ) 1 := ⟨h.1, by linarith [h.2]⟩
        exact ⟨(hiff u hu).mpr h.2, hu⟩
    rw [hset, Real.volume_Ioc]
    simp only [one_mul, sub_zero]
  · rw [if_neg hx]
    have he : 1 < Real.exp (-x) := by
      simpa using Real.exp_lt_exp.mpr (show 0 < -x by linarith)
    have hset : (fun u : ℝ => -Real.log (1 - u)) ⁻¹' Set.Iic x ∩ Set.Ioo 0 1 = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro u h
      have := (hiff u h.2).mp h.1
      linarith [h.2.1]
    rw [hset]
    simp

/-- For an atomless probability distribution, its negative log-survival transform
[has the standard exponential distribution](goal).
@node: hill_log_survival_law_of_atomless -/
lemma hill_log_survival_law_of_atomless (mu : Measure ℝ) [IsProbabilityMeasure mu]
    [NullSingletonClass mu] :
    mu.map (fun x => -Real.log (mu.real (Set.Ioi x))) = expMeasure 1 := by
  exact Toolkit.Foundations.Probability.Distributions.map_neg_log_measureReal_Ioi_eq_expMeasure mu


/-- For the [given extreme model](hyp:M), [tail parameters](hyp:tp), and [Pareto tail
model](hyp:model), the population radial negative log-survival transform [is standard
exponential](goal).
@node: hill_population_survival_exponential -/
lemma hill_population_survival_exponential {q d m : ℕ} (M : ExtremeModel q d)
    (tp : TailParams) (model : ParetoTailModel M m tp) :
    M.mu.map (fun w => -Real.log (tailProb M (radius M w))) = expMeasure 1 := by
  letI := hill_radial_atomless M tp model
  haveI : IsProbabilityMeasure (M.mu.map (radius M)) :=
    Measure.isProbabilityMeasure_map (measurable_radius M).aemeasurable
  have hsurv : ∀ x, (M.mu.map (radius M)).real (Set.Ioi x) = tailProb M x := by
    intro x
    rw [map_measureReal_apply (measurable_radius M) measurableSet_Ioi]
    rfl
  have hmeas : Measurable (fun x => -Real.log (tailProb M x)) := by fun_prop
  calc
    _ = (M.mu.map (radius M)).map (fun x => -Real.log (tailProb M x)) :=
      (Measure.map_map hmeas (measurable_radius M)).symm
    _ = (M.mu.map (radius M)).map
        (fun x => -Real.log ((M.mu.map (radius M)).real (Set.Ioi x))) := by
      simp only [hsurv]
    _ = _ := hill_log_survival_law_of_atomless _

/-- Given an [extreme model](hyp:M), [experiment](hyp:E), [tail parameters](hyp:tp),
[Pareto tail model](hyp:model), and [independent sample](hyp:hiid), the selected raw
observation's radial negative log-survival coordinate [is standard exponential](goal).
@node: hill_raw_survival_coordinates_exponential -/
lemma hill_raw_survival_coordinates_exponential {q d m : ℕ} (M : ExtremeModel q d)
    (E : NeteExperiment M) (tp : TailParams) (model : ParetoTailModel M m tp)
    {n : ℕ} (hiid : IIDSampling E n) (i : Fin n) :
    E.P.map (fun w => -Real.log (tailProb M (l1Norm (E.Zraw i.val w).2.2.2))) =
      expMeasure 1 := by
  let f : Obs q d → ℝ := fun z => -Real.log (tailProb M (l1Norm z.2.2.2))
  have hf : Measurable f := by fun_prop
  have hobs : Measurable (observation M) :=
    M.measurable_X.prodMk (M.measurable_D.prodMk (M.measurable_Y.prodMk M.measurable_U))
  calc
    _ = (E.P.map (E.Zraw i.val)).map f :=
      (Measure.map_map hf (E.measurable_raw i.val)).symm
    _ = (M.mu.map (observation M)).map f := by rw [hiid.2 i]
    _ = M.mu.map (fun w => -Real.log (tailProb M (radius M w))) :=
      Measure.map_map hf hobs
    _ = _ := hill_population_survival_exponential M tp model

end Papers.TbsExtremeEffects
