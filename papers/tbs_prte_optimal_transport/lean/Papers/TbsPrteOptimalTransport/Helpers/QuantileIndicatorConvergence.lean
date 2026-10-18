module
public import Papers.TbsPrteOptimalTransport.Helpers.QuantileScoreRemainder
public import Causalean.Stat.Limit.StochasticOrderEnvelope
/-! Squared indicator errors at moving quantile boundaries under local density bounds. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set

-- The score uses closed lower rays, so disagreement is exactly a half-open
-- interval. This identity also handles reversed and coincident boundaries.
-- @node: quantile_indicator_sq_interval
/-- [The squared difference between the indicators that an outcome is below either of two thresholds equals the indicator of the interval between those thresholds, excluding its lower endpoint and including its upper endpoint](goal). -/
lemma quantile_indicator_sq_interval (a b y : ℝ) :
    (indicator (y ≤ b) - indicator (y ≤ a)) ^ 2 =
      (Ioc (min a b) (max a b)).indicator (fun _ => (1 : ℝ)) y := by
  by_cases hab : a ≤ b
  · rw [min_eq_left hab, max_eq_right hab]
    by_cases hya : y ≤ a
    · have hyb : y ≤ b := hya.trans hab
      simp [indicator, hya, hyb, not_lt_of_ge hya]
    · by_cases hyb : y ≤ b
      · simp [indicator, hya, hyb, lt_of_not_ge hya]
      · simp [indicator, hya, hyb]
  · have hba : b ≤ a := le_of_not_ge hab
    rw [min_eq_right hba, max_eq_left hba]
    by_cases hyb : y ≤ b
    · have hya : y ≤ a := hyb.trans hba
      simp [indicator, hya, hyb, not_lt_of_ge hyb]
    · by_cases hya : y ≤ a
      · simp [indicator, hya, hyb, lt_of_not_ge hyb]
      · simp [indicator, hya, hyb]

-- @node: quantile_indicator_sq_integral
/-- [The integral of the squared difference between two lower-threshold indicators equals the real-valued measure of the interval between the thresholds, excluding its lower endpoint and including its upper endpoint](goal). -/
lemma quantile_indicator_sq_integral (ν : Measure ℝ) (a b : ℝ) :
    (∫ y, (indicator (y ≤ b) - indicator (y ≤ a)) ^ 2 ∂ν) =
      (ν (Ioc (min a b) (max a b))).toReal := by
  simp_rw [quantile_indicator_sq_interval]
  exact integral_indicator_one measurableSet_Ioc

-- A local density controls precisely the disagreement probability, without
-- imposing a density away from the population quantile.
-- @node: quantile_indicator_local_sq_bound
/-- If [the threshold displacement is at most the local radius](hyp:herr) and [every interval within that radius of the reference threshold has mass at most the density cap times its length](hyp:hdensity), [the integrated squared indicator difference is at most the density cap times the absolute threshold displacement](goal). -/
lemma quantile_indicator_local_sq_bound (ν : Measure ℝ)
    (a b r C : ℝ) (herr : |b - a| ≤ r)
    (hdensity : ∀ u v, a - r ≤ u → u ≤ v → v ≤ a + r →
      (ν (Ioc u v)).toReal ≤ C * (v - u)) :
    (∫ y, (indicator (y ≤ b) - indicator (y ≤ a)) ^ 2 ∂ν) ≤ C * |b - a| := by
  rw [quantile_indicator_sq_integral]
  obtain ⟨hlo, hhi⟩ := abs_le.mp herr
  have hr : 0 ≤ r := (abs_nonneg _).trans herr
  have hmass := hdensity (min a b) (max a b)
    (le_min (by linarith) (by linarith)) min_le_max
    (max_le (by linarith) (by linarith))
  have hlen : max a b - min a b = |b - a| := by
    by_cases h : a ≤ b
    · rw [max_eq_right h, min_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
    · rw [max_eq_left (le_of_not_ge h), min_eq_right (le_of_not_ge h),
        abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge h))]
      ring
  simpa only [hlen] using hmass

-- The selected conditional law may be zero off support. Only mass at most
-- one, rather than a probability-measure instance, is needed.
-- @node: quantile_indicator_global_sq_bound
/-- For a finite measure, suppose [the local radius is positive](hyp:hr), [the density cap is nonnegative](hyp:hC), [total mass is at most one](hyp:hmass), and [interval masses within the radius of the reference threshold are bounded by the density cap times interval length](hyp:hdensity). Then [the integrated squared indicator difference is at most the density cap times absolute displacement plus squared displacement divided by squared radius](goal). -/
lemma quantile_indicator_global_sq_bound (ν : Measure ℝ) [IsFiniteMeasure ν]
    (a b r C : ℝ) (hr : 0 < r) (hC : 0 ≤ C) (hmass : ν.real univ ≤ 1)
    (hdensity : ∀ u v, a - r ≤ u → u ≤ v → v ≤ a + r →
      (ν (Ioc u v)).toReal ≤ C * (v - u)) :
    (∫ y, (indicator (y ≤ b) - indicator (y ≤ a)) ^ 2 ∂ν) ≤
      C * |b - a| + (b - a) ^ 2 / r ^ 2 := by
  by_cases he : |b - a| ≤ r
  · exact (quantile_indicator_local_sq_bound ν a b r C he hdensity).trans
      (le_add_of_nonneg_right (by positivity))
  · have hprob : (∫ y, (indicator (y ≤ b) - indicator (y ≤ a)) ^ 2 ∂ν) ≤ 1 := by
      rw [quantile_indicator_sq_integral]
      exact (measureReal_mono (subset_univ _)).trans hmass
    have hlarge : r ≤ |b - a| := le_of_not_ge he
    have hsq : r ^ 2 ≤ (b - a) ^ 2 := by nlinarith [sq_abs (b - a)]
    have hone : (1 : ℝ) ≤ (b - a) ^ 2 / r ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
      simpa using hsq
    exact hprob.trans (hone.trans (le_add_of_nonneg_left (mul_nonneg hC (abs_nonneg _))))

-- Integrating the local linear and remote quadratic controls gives the
-- squared L2 score-error bound used in the conditional Chebyshev step.
-- @node: quantile_indicator_integrated_sq_bound
/-- Under a finite covariate measure, suppose [the error criterion is almost everywhere strongly measurable](hyp:hR), [the boundary error is square integrable](hyp:he), and [the criterion is almost everywhere nonnegative and bounded by the density coefficient times absolute error plus squared error divided by squared radius](hyp:hbound). Then [the criterion is integrable and its integral is at most the density coefficient times integrated absolute error plus integrated squared error divided by squared radius](goal). -/
lemma quantile_indicator_integrated_sq_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (R e : X → ℝ) (r C : ℝ)
    (hR : AEStronglyMeasurable R μ) (he : MemLp e 2 μ)
    (hbound : ∀ᵐ x ∂μ, 0 ≤ R x ∧ R x ≤ C * |e x| + e x ^ 2 / r ^ 2) :
    Integrable R μ ∧
      (∫ x, R x ∂μ) ≤ C * (∫ x, |e x| ∂μ) + (∫ x, e x ^ 2 ∂μ) / r ^ 2 := by
  have hei : Integrable e μ := he.integrable (by norm_num)
  have hdom : Integrable (fun x => C * |e x| + e x ^ 2 / r ^ 2) μ :=
    (hei.abs.const_mul C).add (he.integrable_sq.div_const (r ^ 2))
  have hi : Integrable R μ := hdom.mono' hR (by
    filter_upwards [hbound] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x, C * |e x| + e x ^ 2 / r ^ 2 ∂μ :=
      integral_mono_ae hi hdom (hbound.mono fun _ hx => hx.2)
    _ = _ := by rw [integral_add (hei.abs.const_mul C)
      (he.integrable_sq.div_const (r ^ 2)), integral_const_mul, integral_div]

-- Cauchy--Schwarz expresses the bound using only the boundary's L2 error.
-- @node: quantile_indicator_integrated_L2_bound
/-- Under a probability measure, suppose [the density coefficient is nonnegative](hyp:hC), [the error criterion is almost everywhere strongly measurable](hyp:hR), [the boundary error is square integrable](hyp:he), and [the criterion is almost everywhere nonnegative and bounded by the density coefficient times absolute error plus squared error divided by squared radius](hyp:hbound). Then [the criterion is integrable and its mean is at most the density coefficient times the boundary error's L2 norm plus that norm squared divided by squared radius](goal). -/
lemma quantile_indicator_integrated_L2_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (R e : X → ℝ) (r C : ℝ)
    (hC : 0 ≤ C) (hR : AEStronglyMeasurable R μ) (he : MemLp e 2 μ)
    (hbound : ∀ᵐ x ∂μ, 0 ≤ R x ∧ R x ≤ C * |e x| + e x ^ 2 / r ^ 2) :
    Integrable R μ ∧ (∫ x, R x ∂μ) ≤
      C * (eLpNorm e 2 μ).toReal + (eLpNorm e 2 μ).toReal ^ 2 / r ^ 2 := by
  obtain ⟨hi, hmean⟩ := quantile_indicator_integrated_sq_bound μ R e r C hR he hbound
  have hL1 : (∫ x, |e x| ∂μ) ≤ (eLpNorm e 2 μ).toReal := by
    have h := Causalean.Stat.abs_integral_le_eLpNorm_two he.norm
    have hnn : 0 ≤ ∫ x, ‖e x‖ ∂μ := integral_nonneg fun x => norm_nonneg (e x)
    rw [abs_of_nonneg hnn, eLpNorm_norm] at h
    simpa only [Real.norm_eq_abs] using h
  have hL2 : (∫ x, e x ^ 2 ∂μ) ≤ (eLpNorm e 2 μ).toReal ^ 2 := by
    have h := Causalean.Stat.integral_abs_mul_le_eLpNorm_mul_eLpNorm he he
    simpa only [← sq, abs_pow, sq_abs] using h
  exact ⟨hi, hmean.trans (add_le_add (mul_le_mul_of_nonneg_left hL1 hC)
    (div_le_div_of_nonneg_right hL2 (sq_nonneg r)))⟩

section TreatedLaw
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]

-- Normalization gives mass zero or one, including off-support covariates.
-- @node: treatedLaw_mass_le_one
/-- [The conditional outcome measure for treated observations in any instrument selection set has total real-valued mass at most one, at every covariate value](goal). -/
lemma treatedLaw_mass_le_one (M : LatentIVModel Ω X Z)
    (L : LevelData Z X) (k : ℕ) (x : X) :
    (treatedLaw M L k x).real univ ≤ 1 := by
  let joint := ProbabilityTheory.condDistrib
    (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure x
  let selected := joint.restrict {a | a.2.1 = 1 ∧ a.2.2 ∈ (L.S k : Set Z)}
  have hm : (selected.map Prod.fst) univ = selected univ := by
    rw [Measure.map_apply measurable_fst MeasurableSet.univ]
    simp
  have hmass : treatedLaw M L k x univ ≤ 1 := by
    change ((selected univ)⁻¹ • selected.map Prod.fst) univ ≤ 1
    rw [Measure.smul_apply, hm, smul_eq_mul]
    exact ENNReal.inv_mul_le_one _
  exact (ENNReal.toReal_mono (by norm_num) hmass).trans (by norm_num)

-- This uses the density hypothesis of the actual DML regime and derives the
-- global bound for every fitted threshold, without assuming a global density.
-- @node: dml_quantile_indicator_sq_bound
/-- If [the boundary density bounds hold](hyp:h), [there are a common positive radius and nonnegative density cap such that, for every valid positive band boundary and either adjacent treated law, almost every covariate value admits the following bound for every fitted threshold: integrated squared indicator disagreement is at most the cap times absolute displacement plus squared displacement divided by squared radius](goal). -/
lemma dml_quantile_indicator_sq_bound (M : LatentIVModel Ω X Z)
    (L : LevelData Z X) (h : BoundaryDensitiesBounded M L) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧
      ∀ k < L.K, ∀ j, 1 ≤ j → j ≤ L.l k →
      ∀ k', k' = k + 1 ∨ (1 ≤ k ∧ k' = k) → ∀ᵐ x ∂xLaw M,
        ∀ b, (∫ y, (indicator (y ≤ b) -
          indicator (y ≤ bandBoundary M L k j x)) ^ 2 ∂treatedLaw M L k' x) ≤
          C * |b - bandBoundary M L k j x| +
            (b - bandBoundary M L k j x) ^ 2 / r ^ 2 := by
  obtain ⟨r, C, hr, hd⟩ := h
  refine ⟨r, max C 0, hr, le_max_right _ _, ?_⟩
  intro k hk j hj hjl k' hk'
  filter_upwards [hd k hk j hj hjl k' hk'] with x hx
  intro b
  let := treatedLaw_isFiniteMeasure M L k' x
  apply quantile_indicator_global_sq_bound (treatedLaw M L k' x)
    (bandBoundary M L k j x) b r (max C 0) hr (le_max_right _ _)
    (treatedLaw_mass_le_one M L k' x)
  intro a b ha hab hb
  exact (hx a b ha hab hb).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (sub_nonneg.mpr hab))

-- @node: measurable_treatedLaw_quantile_indicator_sq
/-- If [the reference threshold is measurable in covariates](hyp:ha) and [the fitted threshold is measurable in covariates](hyp:hb), [their squared indicator disagreement integrated against the selected treated outcome law is measurable in covariates](goal). -/
@[fun_prop] lemma measurable_treatedLaw_quantile_indicator_sq
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (k : ℕ)
    (a b : X → ℝ) (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun x => ∫ y, (indicator (y ≤ b x) - indicator (y ≤ a x)) ^ 2
      ∂treatedLaw M L k x) := by
  let κ := ProbabilityTheory.condDistrib
    (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure
  let s : Set (ℝ × ℝ × Z) := {z | z.2.1 = 1 ∧ z.2.2 ∈ (L.S k : Set Z)}
  have hs : MeasurableSet s :=
    (measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const).inter
      ((L.S k).measurableSet.preimage (measurable_snd.comp measurable_snd))
  let F : X × (ℝ × ℝ × Z) → ℝ := fun z =>
    (indicator (z.2.1 ≤ b z.1) - indicator (z.2.1 ≤ a z.1)) ^ 2
  have hIb : Measurable (fun z : X × (ℝ × ℝ × Z) => indicator (z.2.1 ≤ b z.1)) := by
    unfold indicator
    exact Measurable.ite (measurableSet_le (measurable_fst.comp measurable_snd)
      (hb.comp measurable_fst)) measurable_const measurable_const
  have hIa : Measurable (fun z : X × (ℝ × ℝ × Z) => indicator (z.2.1 ≤ a z.1)) := by
    unfold indicator
    exact Measurable.ite (measurableSet_le (measurable_fst.comp measurable_snd)
      (ha.comp measurable_fst)) measurable_const measurable_const
  have hF : StronglyMeasurable F := by
    apply Measurable.stronglyMeasurable
    dsimp only [F]
    fun_prop
  let G := (Prod.snd ⁻¹' s).indicator F
  have hG : StronglyMeasurable G := hF.indicator (hs.preimage measurable_snd)
  have hi : Measurable (fun x => ∫ z, G (x, z) ∂κ x) :=
    (hG.integral_kernel_prod_right').measurable
  have hm : Measurable (fun x => (κ x).restrict s univ) := by
    simpa only [Measure.restrict_apply_univ] using κ.measurable_coe hs
  have hid : (fun x => ∫ y, (indicator (y ≤ b x) - indicator (y ≤ a x)) ^ 2
      ∂treatedLaw M L k x) =
      (fun x => ((κ x).restrict s univ)⁻¹.toReal * ∫ z, G (x, z) ∂κ x) := by
    funext x
    have hfx : StronglyMeasurable (fun y : ℝ =>
        (indicator (y ≤ b x) - indicator (y ≤ a x)) ^ 2) := by
      have hIbx : Measurable (fun y : ℝ => indicator (y ≤ b x)) := by
        unfold indicator
        exact Measurable.ite measurableSet_Iic measurable_const measurable_const
      have hIax : Measurable (fun y : ℝ => indicator (y ≤ a x)) := by
        unfold indicator
        exact Measurable.ite measurableSet_Iic measurable_const measurable_const
      fun_prop
    rw [treatedLaw, integral_smul_measure, smul_eq_mul,
      integral_map_of_stronglyMeasurable measurable_fst hfx]
    congr 1
    rw [← integral_indicator hs]
    rfl
  rw [hid]
  fun_prop

-- All regularity of the integrated squared indicator error is derived from
-- the measurable thresholds and the conditional-law construction.
-- @node: treatedLaw_quantile_indicator_L2_bound
/-- Suppose [the reference threshold is measurable](hyp:ha), [the fitted threshold is measurable](hyp:hb), [the local radius is positive](hyp:hr), [the density cap is nonnegative](hyp:hC), [the threshold displacement is square integrable under the covariate law](hyp:he), and [almost surely, treated interval masses near the reference threshold are bounded by the cap times interval length](hyp:hdensity). Then [conditional squared indicator disagreement is integrable in covariates, and its mean is at most the cap times the displacement's L2 norm plus that norm squared divided by squared radius](goal). -/
lemma treatedLaw_quantile_indicator_L2_bound (M : LatentIVModel Ω X Z)
    (L : LevelData Z X) (k : ℕ) (a b : X → ℝ) (r C : ℝ)
    (ha : Measurable a) (hb : Measurable b) (hr : 0 < r) (hC : 0 ≤ C)
    (he : MemLp (fun x => b x - a x) 2 (xLaw M))
    (hdensity : ∀ᵐ x ∂xLaw M, ∀ u v, a x - r ≤ u → u ≤ v → v ≤ a x + r →
      (treatedLaw M L k x (Ioc u v)).toReal ≤ C * (v - u)) :
    Integrable (fun x => ∫ y, (indicator (y ≤ b x) - indicator (y ≤ a x)) ^ 2
      ∂treatedLaw M L k x) (xLaw M) ∧
    (∫ x, ∫ y, (indicator (y ≤ b x) - indicator (y ≤ a x)) ^ 2
      ∂treatedLaw M L k x ∂xLaw M) ≤
      C * (eLpNorm (fun x => b x - a x) 2 (xLaw M)).toReal +
        (eLpNorm (fun x => b x - a x) 2 (xLaw M)).toReal ^ 2 / r ^ 2 := by
  haveI : IsProbabilityMeasure (xLaw M) :=
    Measure.isProbabilityMeasure_map M.measX.aemeasurable
  have hR : Measurable (fun x => ∫ y,
      (indicator (y ≤ b x) - indicator (y ≤ a x)) ^ 2 ∂treatedLaw M L k x) := by
    fun_prop
  apply quantile_indicator_integrated_L2_bound (xLaw M) _ _ r C hC
    hR.aestronglyMeasurable he
  filter_upwards [hdensity] with x hx
  refine ⟨integral_nonneg fun y => sq_nonneg _, ?_⟩
  let := treatedLaw_isFiniteMeasure M L k x
  exact quantile_indicator_global_sq_bound (treatedLaw M L k x) (a x) (b x) r C
    hr hC (treatedLaw_mass_le_one M L k x) hx

-- This is the nonsmooth part of score convergence in the DML roadmap:
-- L2 convergence of a boundary implies convergence of its indicator in L2.
-- @node: treatedLaw_quantile_indicator_sq_tendsto_zero
/-- Suppose [the reference threshold is measurable](hyp:ha), [every fitted threshold is measurable](hyp:hb), [the local radius is positive](hyp:hr), [the density cap is nonnegative](hyp:hC), [every threshold displacement is square integrable](hyp:he), and [almost surely, treated interval masses near the reference threshold are bounded by the cap times interval length](hyp:hdensity). If [the L2 norms of the threshold displacements converge to zero](hyp:herror), [the covariate averages of the treated-law squared indicator disagreements converge to zero](goal). -/
lemma treatedLaw_quantile_indicator_sq_tendsto_zero (M : LatentIVModel Ω X Z)
    (L : LevelData Z X) (k : ℕ) (a : X → ℝ) (b : ℕ → X → ℝ) (r C : ℝ)
    (ha : Measurable a) (hb : ∀ n, Measurable (b n)) (hr : 0 < r) (hC : 0 ≤ C)
    (he : ∀ n, MemLp (fun x => b n x - a x) 2 (xLaw M))
    (hdensity : ∀ᵐ x ∂xLaw M, ∀ u v, a x - r ≤ u → u ≤ v → v ≤ a x + r →
      (treatedLaw M L k x (Ioc u v)).toReal ≤ C * (v - u))
    (herror : Filter.Tendsto (fun n =>
      (eLpNorm (fun x => b n x - a x) 2 (xLaw M)).toReal) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫ x, ∫ y,
      (indicator (y ≤ b n x) - indicator (y ≤ a x)) ^ 2
        ∂treatedLaw M L k x ∂xLaw M) Filter.atTop (nhds 0) := by
  apply squeeze_zero (fun n => integral_nonneg fun x => integral_nonneg fun y => sq_nonneg _)
    (fun n => (treatedLaw_quantile_indicator_L2_bound M L k a (b n) r C
      ha (hb n) hr hC (he n) hdensity).2)
  have hlim := (herror.const_mul C).add ((herror.pow 2).div_const (r ^ 2))
  simpa only [mul_zero, zero_pow (by norm_num : 2 ≠ 0), zero_div, add_zero] using hlim

end TreatedLaw
end Papers.TbsPrteOptimalTransport
