module
public import Papers.TbsExtremeEffects.Helpers.Hill.OrderedSpacings
public import Papers.TbsExtremeEffects.Helpers.Hill.NominalProductLaw
public import Papers.TbsExtremeEffects.Helpers.Hill.ExponentialLaw
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! The factorial Jacobian and density transport for decreasing exponential spacings. -/

@[expose] public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- The [spacing transformation for a sample of size `n`](hyp:n) is the [linear map](goal)
that multiplies each successive downward difference by its rank. -/
-- @node: hillSpacingLinear
noncomputable def hillSpacingLinear (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  LinearMap.pi fun j => ((j.val + 1 : ℕ) : ℝ) •
    ((LinearMap.proj j : (Fin n → ℝ) →ₗ[ℝ] ℝ) -
      if h : j.val + 1 < n then LinearMap.proj ⟨j.val + 1, h⟩ else 0)

/-- For [a sample size](hyp:n), [a vector of ordered values](hyp:y), and [a rank](hyp:j),
the spacing transformation at that rank is [the rank-weighted difference from the next value](goal). -/
-- @node: hillSpacingLinear_apply
lemma hillSpacingLinear_apply (n : ℕ) (y : Fin n → ℝ) (j : Fin n) :
    hillSpacingLinear n y j = ((j.val + 1 : ℕ) : ℝ) *
      (y j - if h : j.val + 1 < n then y ⟨j.val + 1, h⟩ else 0) := by
  simp only [hillSpacingLinear, LinearMap.pi_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.proj_apply, smul_eq_mul]
  split_ifs <;> rfl

/-- Given [a sample size](hyp:n), [a collection of real-valued observations](hyp:V), and [an outcome](hyp:w),
the ordered spacings are [the spacing transformation of the decreasing order statistics](goal). -/
-- @node: hill_ordered_spacing_eq_linear
lemma hill_ordered_spacing_eq_linear {Ω : Type*} {n : ℕ}
    (V : Fin n → Ω → ℝ) (w : Ω) :
    (fun j => hillOrderedSpacing V j w) = hillSpacingLinear n (hillDecreasingOrder V w) := by
  funext j
  simp only [hillSpacingLinear_apply, hillOrderedSpacing, Nat.cast_add, Nat.cast_one]

/-- For [a sample size](hyp:n), the [determinant of the spacing transformation](goal)
equals the sample-size factorial. -/
-- @node: hillSpacingLinear_det
lemma hillSpacingLinear_det (n : ℕ) :
    LinearMap.det (hillSpacingLinear n) = (n.factorial : ℝ) := by
  classical
  let A := LinearMap.toMatrix' (hillSpacingLinear n)
  have htri : A.IsUpperTriangular := by
    intro i j hij
    have hji : j < i := hij
    have hne : i ≠ j := (ne_of_lt hji).symm
    have hnext : ∀ h : i.val + 1 < n, (⟨i.val + 1, h⟩ : Fin n) ≠ j := by
      intro h heq
      have := congrArg Fin.val heq
      have := Fin.lt_def.mp hji
      simp only [Fin.val_mk, id_eq] at *
      omega
    simp only [A, LinearMap.toMatrix'_apply, hillSpacingLinear_apply]
    split_ifs with h <;> simp [hne, hnext]
  have hdiag (i : Fin n) : A i i = ((i.val + 1 : ℕ) : ℝ) := by
    have hnext : ∀ h : i.val + 1 < n, (⟨i.val + 1, h⟩ : Fin n) ≠ i := by
      intro h heq
      have := congrArg Fin.val heq
      simp only [Fin.val_mk] at *
      omega
    simp only [A, LinearMap.toMatrix'_apply, hillSpacingLinear_apply]
    split_ifs with h <;> simp [hnext]
  rw [← LinearMap.det_toMatrix']
  change A.det = _
  rw [Matrix.det_of_isUpperTriangular htri]
  simp_rw [hdiag]
  change (∏ i : Fin n, (fun j : ℕ => ((j + 1 : ℕ) : ℝ)) i.val) = _
  rw [Fin.prod_univ_eq_prod_range (fun j : ℕ => ((j + 1 : ℕ) : ℝ)) n]
  exact_mod_cast Nat.factorial_eq_prod_range_add_one n |>.symm

/-- For [a sample size](hyp:n), pushing Lebesgue volume through [the spacing transformation](goal)
scales it by the reciprocal of the sample-size factorial. -/
-- @node: hillSpacingLinear_volume
lemma hillSpacingLinear_volume (n : ℕ) :
    volume.map (hillSpacingLinear n) =
      ENNReal.ofReal ((n.factorial : ℝ)⁻¹) • (volume : Measure (Fin n → ℝ)) := by
  have hpos : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  simpa only [hillSpacingLinear_det, abs_of_pos (inv_pos.mpr hpos)] using
    Real.map_linearMap_volume_pi_eq_smul_volume_pi
      (f := hillSpacingLinear n) (by rw [hillSpacingLinear_det]; exact hpos.ne')

/-- For [a real sequence](hyp:y) and [a cutoff](hyp:n), the [sum of rank-weighted successive differences](goal)
equals the partial sum minus the cutoff times the next value. -/
-- @node: hill_weighted_difference_sum
lemma hill_weighted_difference_sum (y : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, ((j : ℝ) + 1) * (y j - y (j + 1))) =
      (∑ j ∈ Finset.range n, y j) - (n : ℝ) * y n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    push_cast
    ring

/-- For [a sample size](hyp:n) and [an ordered-value vector](hyp:y), the [sum of its transformed spacings](goal)
equals the sum of the original values. -/
-- @node: hillSpacingLinear_sum
lemma hillSpacingLinear_sum (n : ℕ) (y : Fin n → ℝ) :
    (∑ j, hillSpacingLinear n y j) = ∑ j, y j := by
  let z : ℕ → ℝ := fun j => if h : j < n then y ⟨j, h⟩ else 0
  have hz : z n = 0 := by simp [z]
  have h := hill_weighted_difference_sum z n
  rw [hz, mul_zero, sub_zero] at h
  rw [← Fin.sum_univ_eq_sum_range] at h
  rw [← Fin.sum_univ_eq_sum_range] at h
  simpa only [z, Fin.is_lt, dif_pos, hillSpacingLinear_apply, Nat.cast_add,
    Nat.cast_one] using h

/-- For [a sample size](hyp:n) and [a vector of values](hyp:y), [all transformed spacings are nonnegative](goal)
exactly when the vector is decreasing and nonnegative at every rank. -/
-- @node: hillSpacingLinear_nonneg_iff
lemma hillSpacingLinear_nonneg_iff (n : ℕ) (y : Fin n → ℝ) :
    (∀ j, 0 ≤ hillSpacingLinear n y j) ↔ Antitone y ∧ ∀ j, 0 ≤ y j := by
  constructor
  · intro h
    let z : ℕ → ℝ := fun j => if h : j < n then y ⟨j, h⟩ else 0
    have hstep : ∀ j, z (j + 1) ≤ z j := by
      intro j
      by_cases hj : j < n
      · have hdiff := h ⟨j, hj⟩
        rw [hillSpacingLinear_apply] at hdiff
        have hcoef : 0 < (((⟨j, hj⟩ : Fin n).val + 1 : ℕ) : ℝ) := by positivity
        have := (mul_nonneg_iff_of_pos_left hcoef).mp hdiff
        simpa only [z, hj, dif_pos, Fin.val_mk, sub_nonneg] using this
      · have hj' : ¬ j + 1 < n := by omega
        simp [z, hj, hj']
    have hanti := antitone_nat_of_succ_le hstep
    constructor
    · intro i j hij
      have := hanti (Fin.le_def.mp hij)
      simpa only [z, i.is_lt, j.is_lt, dif_pos] using this
    · intro j
      have := hanti j.is_lt.le
      simpa [z, j.is_lt] using this
  · rintro ⟨hanti, hpos⟩ j
    rw [hillSpacingLinear_apply]
    apply mul_nonneg (by positivity)
    split_ifs with h
    · exact sub_nonneg.mpr (hanti (by show j.val ≤ j.val + 1; omega))
    · simpa using hpos j

/-- For [a sample size](hyp:n) and [a vector of proposed spacings](hyp:z), the [product exponential density](goal)
is the exponential of minus their sum when all spacings are nonnegative, and zero otherwise. -/
-- @node: hill_exponential_product_pdf
lemma hill_exponential_product_pdf (n : ℕ) (z : Fin n → ℝ) :
    (∏ j, exponentialPDF 1 (z j)) =
      if ∀ j, 0 ≤ z j then ENNReal.ofReal (Real.exp (-∑ j, z j)) else 0 := by
  classical
  by_cases hz : ∀ j, 0 ≤ z j
  · rw [if_pos hz]
    simp_rw [exponentialPDF_of_nonneg (hz _), one_mul]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => (Real.exp_pos _).le),
      ← Real.exp_sum, Finset.sum_neg_distrib]
  · rw [if_neg hz]
    obtain ⟨j, hj⟩ := not_forall.mp hz
    exact Finset.prod_eq_zero (Finset.mem_univ j)
      (exponentialPDF_of_neg (lt_of_not_ge hj))

/-- For [a sample size](hyp:n) and [a vector of ordered values](hyp:y), the [ordered exponential density](goal)
is the factorial times the exponential of minus their sum on decreasing nonnegative vectors, and zero elsewhere. -/
-- @node: hillOrderedExponentialDensity
noncomputable def hillOrderedExponentialDensity (n : ℕ) (y : Fin n → ℝ) : ℝ≥0∞ :=
  if Antitone y ∧ ∀ j, 0 ≤ y j then
    ENNReal.ofReal (n.factorial : ℝ) * ENNReal.ofReal (Real.exp (-∑ j, y j)) else 0

/-- For [a sample size](hyp:n) and [a vector of ordered values](hyp:y), the [ordered exponential density](goal)
equals the factorial times the product of exponential densities of its transformed spacings. -/
-- @node: hill_ordered_density_pullback
lemma hill_ordered_density_pullback (n : ℕ) (y : Fin n → ℝ) :
    hillOrderedExponentialDensity n y = ENNReal.ofReal (n.factorial : ℝ) *
      ∏ j, exponentialPDF 1 (hillSpacingLinear n y j) := by
  classical
  rw [hill_exponential_product_pdf]
  simp only [hillSpacingLinear_nonneg_iff, hillSpacingLinear_sum,
    hillOrderedExponentialDensity]
  split_ifs <;> simp

/-- For [a sample size](hyp:n), the [ordered exponential density is measurable](goal). -/
@[fun_prop]
-- @node: hill_ordered_density_measurable
lemma hill_ordered_density_measurable (n : ℕ) :
    Measurable (hillOrderedExponentialDensity n) := by
  first | fun_prop | skip
  have heq : hillOrderedExponentialDensity n = fun y =>
      ENNReal.ofReal (n.factorial : ℝ) * ∏ j, exponentialPDF 1 (hillSpacingLinear n y j) :=
    funext (hill_ordered_density_pullback n)
  rw [heq]
  apply measurable_const.mul
  apply Finset.measurable_prod
  intro j _
  exact (measurable_exponentialPDFReal 1).ennreal_ofReal.comp
    ((measurable_pi_apply j).comp
      (hillSpacingLinear n).continuous_of_finiteDimensional.measurable)

/-- If [a measure](hyp:mu) is transformed by [a map](hyp:g) that [is measurable](hyp:hg) and [a density](hyp:f) that [is measurable](hyp:hf)
is evaluated after that map, then [mapping the resulting weighted measure equals weighting the mapped measure](goal). -/
-- @node: hill_map_density_comp
lemma hill_map_density_comp {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (mu : Measure Ω) (g : Ω → Ξ) (f : Ξ → ℝ≥0∞)
    (hg : Measurable g) (hf : Measurable f) :
    (mu.withDensity (fun x => f (g x))).map g = (mu.map g).withDensity f := by
  ext s hs
  rw [Measure.map_apply hg hs, withDensity_apply _ (hg hs), withDensity_apply _ hs,
    setLIntegral_map hs hf hg]

/-- For [a sample size](hyp:n), the [Lebesgue measure weighted by the product exponential density](goal)
is the product law of independent standard exponential variables. -/
-- @node: hill_exponential_product_density_law
lemma hill_exponential_product_density_law (n : ℕ) :
    (volume : Measure (Fin n → ℝ)).withDensity (fun z => ∏ j, exponentialPDF 1 (z j)) =
      Measure.pi (fun _ : Fin n => expMeasure 1) := by
  let := isProbabilityMeasure_expMeasure (r := 1) (by norm_num)
  apply (Measure.pi_eq (fun s hs => ?_)).symm
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  change (∫⁻ z, ∏ j, exponentialPDF 1 (z j)
    ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).restrict (Set.univ.pi s)) = _
  rw [Measure.restrict_pi_pi]
  rw [hill_lintegral_fin_prod (fun j => volume.restrict (s j))
    (fun _ => exponentialPDF 1)
    (fun _ => (measurable_exponentialPDFReal 1).ennreal_ofReal)]
  apply Finset.prod_congr rfl
  intro j _
  change _ = (volume.withDensity (exponentialPDF 1)) (s j)
  rw [withDensity_apply _ (hs j)]

/-- For [a sample size](hyp:n), [mapping the ordered exponential-density law through the spacing transformation](goal)
gives the product law of independent standard exponential spacings. -/
-- @node: hill_ordered_exponential_density_spacing_law
lemma hill_ordered_exponential_density_spacing_law (n : ℕ) :
    ((volume : Measure (Fin n → ℝ)).withDensity
      (hillOrderedExponentialDensity n)).map (hillSpacingLinear n) =
      Measure.pi (fun _ : Fin n => expMeasure 1) := by
  let f : (Fin n → ℝ) → ℝ≥0∞ := fun z => ∏ j, exponentialPDF 1 (z j)
  have hf : Measurable f := by
    first | fun_prop | skip
    exact Finset.measurable_prod _ (fun j _ =>
      (measurable_exponentialPDFReal 1).ennreal_ofReal.comp (measurable_pi_apply j))
  have hL : Measurable (hillSpacingLinear n) := by
    fun_prop
  have hd : hillOrderedExponentialDensity n =
      ENNReal.ofReal (n.factorial : ℝ) • (fun y => f (hillSpacingLinear n y)) := by
    funext y
    exact hill_ordered_density_pullback n y
  rw [hd]
  rw [withDensity_smul (f := fun y => f (hillSpacingLinear n y)) _ (hf.comp hL), Measure.map_smul,
    hill_map_density_comp volume _ f hL hf, hillSpacingLinear_volume,
    withDensity_smul_measure, smul_smul]
  have hpos : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  rw [← ENNReal.ofReal_mul hpos.le, mul_inv_cancel₀ hpos.ne', ENNReal.ofReal_one,
    one_smul]
  exact hill_exponential_product_density_law n

/-- If [the observations are measurable](hyp:hV) and [their decreasing order vector has the ordered exponential density](hyp:hDensity), then [the ordered spacings are independent standard exponentials](goal).
Here [the probability measure](hyp:P), [the observation collection](hyp:V), and [the sample size](hyp:n) specify the experiment. -/
-- @node: hill_spacing_joint_law_of_ordered_density
lemma hill_spacing_joint_law_of_ordered_density {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (V : Fin n → Ω → ℝ)
    (hV : ∀ j, Measurable (V j))
    (hDensity : P.map (hillDecreasingOrder V) =
      volume.withDensity (hillOrderedExponentialDensity n)) :
    iIndepFun (hillOrderedSpacing V) P ∧
      ∀ j, P.map (hillOrderedSpacing V j) = expMeasure 1 := by
  let := isProbabilityMeasure_expMeasure (r := 1) (by norm_num)
  have hmeas : Measurable (hillDecreasingOrder V) :=
    measurable_pi_lambda _ (hill_decreasing_order_measurable V hV)
  have hL : Measurable (hillSpacingLinear n) :=
    (hillSpacingLinear n).continuous_of_finiteDimensional.measurable
  have hjoint : P.map (fun w j => hillOrderedSpacing V j w) =
      Measure.pi (fun _ : Fin n => expMeasure 1) := by
    have heq : (fun w j => hillOrderedSpacing V j w) =
        hillSpacingLinear n ∘ hillDecreasingOrder V :=
      funext (hill_ordered_spacing_eq_linear V)
    rw [heq, ← Measure.map_map hL hmeas, hDensity]
    exact hill_ordered_exponential_density_spacing_law n
  have hMarginal : ∀ j, P.map (hillOrderedSpacing V j) = expMeasure 1 := by
    intro j
    have h := congrArg (Measure.map (fun z : Fin n → ℝ => z j)) hjoint
    rw [Measure.map_map (measurable_pi_apply j)
      (measurable_pi_lambda _ (hill_ordered_spacing_measurable V hV))] at h
    exact h.trans (measurePreserving_eval (fun _ : Fin n => expMeasure 1) j).map_eq
  refine ⟨(iIndepFun_iff_map_fun_eq_pi_map
    (fun j => (hill_ordered_spacing_measurable V hV j).aemeasurable)).mpr ?_, hMarginal⟩
  simpa only [hMarginal] using hjoint

end Papers.TbsExtremeEffects
