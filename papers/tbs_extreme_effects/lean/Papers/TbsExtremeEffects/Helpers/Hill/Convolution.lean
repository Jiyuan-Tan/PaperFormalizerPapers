module
public import Papers.TbsExtremeEffects.Helpers.Hill.NominalDensity

/-! Near/far splitting of the largest-summand convolution remainder. -/

@[expose] public section
namespace Papers.TbsExtremeEffects
open MeasureTheory
open scoped BigOperators

/-- If [the tail exponent](hyp:hb), [component scale](hyp:ha), and [radius](hyp:hr) are positive, and [the displacement is nonnegative](hyp:hv) and [at most half the radius](hyp:hvr), [shifting the component density by that displacement has the stated linear error bound](goal).
@node: hill_component_density_near_error -/
lemma hill_component_density_near_error {beta a r v : ℝ}
    (hb : 0 < beta) (ha : 0 < a) (hr : 0 < r)
    (hv : 0 ≤ v) (hvr : v ≤ r / 2) :
    |beta * a ^ beta * (a + (r - v)) ^ (-beta - 1) -
      beta * a ^ beta * (a + r) ^ (-beta - 1)| ≤
      (beta * a ^ beta * (beta + 1) * (r / 2) ^ (-beta - 2)) * v := by
  let f : ℝ → ℝ := fun x => beta * a ^ beta * (a + x) ^ (-beta - 1)
  let f' : ℝ → ℝ := fun x =>
    beta * a ^ beta * (-beta - 1) * (a + x) ^ (-beta - 2)
  have hderiv : ∀ x ∈ Set.Icc (r - v) r,
      HasDerivWithinAt f (f' x) (Set.Icc (r - v) r) x := by
    intro x hx
    have hxpos : 0 < a + x := by linarith [hx.1]
    have hd := (((hasDerivAt_id x).const_add a).rpow_const (p := -beta - 1)
      (Or.inl hxpos.ne')).const_mul (beta * a ^ beta)
    simpa only [f, f', id_eq, one_mul,
      show -beta - 1 - 1 = -beta - 2 by ring, mul_assoc] using hd.hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ico (r - v) r,
      ‖f' x‖ ≤ beta * a ^ beta * (beta + 1) * (r / 2) ^ (-beta - 2) := by
    intro x hx
    have hxpos : 0 < a + x := by linarith [hx.1]
    have hp := Real.rpow_le_rpow_of_nonpos (by linarith : 0 < r / 2)
      (by linarith [hx.1] : r / 2 ≤ a + x) (by linarith : -beta - 2 ≤ 0)
    have heq : ‖f' x‖ = beta * a ^ beta * (beta + 1) * (a + x) ^ (-beta - 2) := by
      dsimp [f']
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos hb,
        abs_of_pos (Real.rpow_pos_of_pos ha _), abs_of_neg (by linarith : -beta - 1 < 0),
        abs_of_pos (Real.rpow_pos_of_pos hxpos _)]
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hp (by positivity)
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound
    r (Set.right_mem_Icc.mpr (by linarith))
  simpa only [f, Real.norm_eq_abs, abs_sub_comm, sub_sub_cancel] using h

/-- For [a probability distribution](hyp:P), [a measurable remainder variable](hyp:hV), [an integrable integrand](hyp:hH), [an integrable truncated remainder](hyp:htrunc), [a near-region error bound](hyp:hnear), and [a far-region error bound](hyp:hfar), [the integral's error is bounded by its near contribution plus its far-tail contribution](goal).
@node: hill_convolution_near_far_error -/
lemma hill_convolution_near_far_error {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (H V : Ω → ℝ)
    {r f₀ near far : ℝ} (hV : Measurable V) (hH : Integrable H P)
    (htrunc : Integrable (fun w => if V w ≤ r / 2 then V w else 0) P)
    (hnear : ∀ᵐ w ∂P, V w ≤ r / 2 → |H w - f₀| ≤ near * V w)
    (hfar : ∀ᵐ w ∂P, r / 2 < V w → |H w - f₀| ≤ far) :
    |(∫ w, H w ∂P) - f₀| ≤
      near * (∫ w, if V w ≤ r / 2 then V w else 0 ∂P) +
        far * P.real {w | r / 2 < V w} := by
  have hs : MeasurableSet {w | r / 2 < V w} := measurableSet_lt measurable_const hV
  have hI : Integrable (fun w => if r / 2 < V w then (1 : ℝ) else 0) P := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
    · exact (Measurable.ite hs measurable_const measurable_const).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun w => by split_ifs <;> norm_num
  have hmajor : Integrable (fun w =>
      near * (if V w ≤ r / 2 then V w else 0) +
        far * (if r / 2 < V w then (1 : ℝ) else 0)) P :=
    (htrunc.const_mul near).add (hI.const_mul far)
  have hbound := norm_integral_le_of_norm_le hmajor (f := fun w => H w - f₀) (by
    filter_upwards [hnear, hfar] with w hn hf
    rw [Real.norm_eq_abs]
    by_cases hw : V w ≤ r / 2
    · simpa [hw, not_lt.mpr hw] using hn hw
    · simpa [hw, lt_of_not_ge hw] using hf (lt_of_not_ge hw))
  rw [integral_sub hH (integrable_const f₀)] at hbound
  simp only [integral_const, probReal_univ, one_smul, Real.norm_eq_abs] at hbound
  rw [integral_add (htrunc.const_mul near) (hI.const_mul far),
    integral_const_mul, integral_const_mul] at hbound
  have hmass : (∫ w, if r / 2 < V w then (1 : ℝ) else 0 ∂P) =
      P.real {w | r / 2 < V w} := by
    simpa [Set.indicator, smul_eq_mul] using
      integral_indicator_const (1 : ℝ) hs (μ := P)
  rwa [hmass] at hbound

/-- For [a probability distribution](hyp:P), [a remainder variable](hyp:V), [a nonnegative radius](hyp:hr), [measurability](hyp:hV), and [almost-sure nonnegativity](hyp:hpos), [the remainder truncated at half the radius is integrable](goal).
@node: hill_truncated_remainder_integrable -/
lemma hill_truncated_remainder_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (V : Ω → ℝ)
    {r : ℝ} (hr : 0 ≤ r) (hV : Measurable V) (hpos : ∀ᵐ w ∂P, 0 ≤ V w) :
    Integrable (fun w => if V w ≤ r / 2 then V w else 0) P := by
  apply Integrable.mono' (integrable_const (r / 2))
  · have hs : MeasurableSet {w | V w ≤ r / 2} := by
      first | fun_prop | exact measurableSet_le hV measurable_const
    exact (Measurable.ite hs hV measurable_const).aestronglyMeasurable
  · filter_upwards [hpos] with w hw
    rw [Real.norm_eq_abs]
    split_ifs with hv
    · rwa [abs_of_nonneg hw]
    · simp only [abs_zero]; positivity

/-- Given [a nonnegative prefactor](hyp:hkappa), [a density represented as the prefactor times the sum of component terms](hyp:hpartition), and [a bound on every component error](hyp:herr), [the error of the resulting summed density is bounded by the prefactor times the sum of those bounds](goal).
@node: hill_convolution_sum_error -/
lemma hill_convolution_sum_error {m : ℕ} (e f b : Fin m → ℝ)
    {density kappa : ℝ} (hkappa : 0 ≤ kappa)
    (hpartition : density = kappa * ∑ i, e i)
    (herr : ∀ i, |e i - f i| ≤ b i) :
    |density - kappa * ∑ i, f i| ≤ kappa * ∑ i, b i := by
  rw [hpartition, ← mul_sub, abs_mul, abs_of_nonneg hkappa, ← Finset.sum_sub_distrib]
  exact mul_le_mul_of_nonneg_left
    ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => herr i)) hkappa

/-- For [a positive tail exponent](hyp:hb), [a positive radius](hyp:hr), [positive component scales](hyp:ha), [a nonnegative prefactor](hyp:hkappa), [measurable remainders](hyp:hV), [their almost-sure nonnegativity](hyp:hpos), [integrable component integrands](hyp:hH), [their near-region formulas](hyp:hnear), [their far-region error bounds](hyp:hfar), and [the density partition](hyp:hpartition), [the convolution density error is bounded by the sum of the stated near and far errors](goal).
@node: hill_convolution_density_error -/
lemma hill_convolution_density_error {m : ℕ}
    (P : Measure (Fin m → ℝ)) [IsProbabilityMeasure P]
    (a : Fin m → ℝ) (H V : Fin m → (Fin m → ℝ) → ℝ) (far : Fin m → ℝ)
    {beta r density kappa : ℝ} (hb : 0 < beta) (hr : 0 < r)
    (ha : ∀ i, 0 < a i) (hkappa : 0 ≤ kappa)
    (hV : ∀ i, Measurable (V i)) (hpos : ∀ i, ∀ᵐ z ∂P, 0 ≤ V i z)
    (hH : ∀ i, Integrable (H i) P)
    (hnear : ∀ i, ∀ᵐ z ∂P, V i z ≤ r / 2 → H i z =
      beta * (a i) ^ beta * (a i + (r - V i z)) ^ (-beta - 1))
    (hfar : ∀ i, ∀ᵐ z ∂P, r / 2 < V i z →
      |H i z - beta * (a i) ^ beta * (a i + r) ^ (-beta - 1)| ≤ far i)
    (hpartition : density = kappa * ∑ i, ∫ z, H i z ∂P) :
    |density - kappa * ∑ i, beta * (a i) ^ beta * (a i + r) ^ (-beta - 1)| ≤
      kappa * ∑ i : Fin m, (
        (beta * (a i) ^ beta * (beta + 1) * (r / 2) ^ (-beta - 2)) *
          (∫ z, if V i z ≤ r / 2 then V i z else 0 ∂P) +
        far i * P.real {z | r / 2 < V i z}) := by
  apply hill_convolution_sum_error _ _ _ hkappa hpartition
  intro i
  apply hill_convolution_near_far_error P (H i) (V i) (hV i) (hH i)
    (hill_truncated_remainder_integrable P (V i) hr.le (hV i) (hpos i))
  · filter_upwards [hnear i, hpos i] with z hz hp
    intro hsmall
    rw [hz hsmall]
    exact hill_component_density_near_error hb (ha i) hr hp hsmall
  · exact hfar i

/-- For [component scales](hyp:a), [a tail exponent](hyp:beta), [a radius](hyp:r), [a prefactor](hyp:kappa), [a density value](hyp:density), and [an error budget](hyp:budget), [the convolution-remainder data condition](goal) asserts [a probability measure](step:1), [measurable remainders](step:2), [their almost-sure nonnegativity](step:3), [integrable component integrands](step:4), [near-region component formulas](step:5), [far-region error bounds](step:6), [the density partition](step:7), and [the numerical remainder bound](step:8).
@node: HillConvolutionRemainderData -/
noncomputable def HillConvolutionRemainderData {m : ℕ} (a : Fin m → ℝ)
    (beta r kappa density budget : ℝ) : Prop :=
  ∃ (P : Measure (Fin m → ℝ)) (H V : Fin m → (Fin m → ℝ) → ℝ)
    (far : Fin m → ℝ),
    IsProbabilityMeasure P ∧
    (∀ i, Measurable (V i)) ∧ (∀ i, ∀ᵐ z ∂P, 0 ≤ V i z) ∧
    (∀ i, Integrable (H i) P) ∧
    (∀ i, ∀ᵐ z ∂P, V i z ≤ r / 2 → H i z =
      beta * (a i) ^ beta * (a i + (r - V i z)) ^ (-beta - 1)) ∧
    (∀ i, ∀ᵐ z ∂P, r / 2 < V i z →
      |H i z - beta * (a i) ^ beta * (a i + r) ^ (-beta - 1)| ≤ far i) ∧
    density = kappa * (∑ i, ∫ z, H i z ∂P) ∧
    kappa * (∑ i : Fin m,
      ((beta * (a i) ^ beta * (beta + 1) * (r / 2) ^ (-beta - 2)) *
        (∫ z, if V i z ≤ r / 2 then V i z else 0 ∂P) +
        far i * P.real {z | r / 2 < V i z})) ≤ budget

/-- Given [a positive tail exponent](hyp:hb), [a positive radius](hyp:hr), [positive component scales](hyp:ha), [a nonnegative prefactor](hyp:hkappa), and [convolution-remainder data](hyp:h), [the density approximation error is at most the assigned budget](goal).
@node: hill_convolution_error_of_remainder_data -/
lemma hill_convolution_error_of_remainder_data {m : ℕ} (a : Fin m → ℝ)
    {beta r kappa density budget : ℝ} (hb : 0 < beta) (hr : 0 < r)
    (ha : ∀ i, 0 < a i) (hkappa : 0 ≤ kappa)
    (h : HillConvolutionRemainderData a beta r kappa density budget) :
    |density - kappa * ∑ i, beta * (a i) ^ beta * (a i + r) ^ (-beta - 1)| ≤
      budget := by
  obtain ⟨P, H, V, far, hP, hV, hpos, hH, hnear, hfar, hpartition, hbudget⟩ := h
  let := hP
  exact (hill_convolution_density_error P a H V far hb hr ha hkappa
    hV hpos hH hnear hfar hpartition).trans hbudget

end Papers.TbsExtremeEffects
