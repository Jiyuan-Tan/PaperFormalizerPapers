module
public import Papers.TbsNeuralCausalPi.Helpers.AntipodalGeometry
public import Mathlib.Analysis.Normed.Group.BallSphere
/-! # Radial identification of the signed geometric sphere

Positive radial normalization identifies the cross-polytope realization with the
sup-norm unit sphere and commutes with the antipodal maps.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi.Antipodal
noncomputable section

-- @node: coordinateAbsSum
/-- For [a real vector](hyp:x) in [dimension n](hyp:n), its
[coordinate absolute sum](goal) is the sum of the absolute values of its coordinates. -/
def coordinateAbsSum {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, |x i|

-- @node: coordinateAbsSum_continuous
/-- [The sum of absolute coordinate values is a continuous function of a real vector](goal)
in [dimension n](hyp:n). -/
@[fun_prop] lemma coordinateAbsSum_continuous (n : ℕ) :
    Continuous (coordinateAbsSum : (Fin n → ℝ) → ℝ) := by
  unfold coordinateAbsSum
  fun_prop

-- @node: coordinateAbsSum_pos
/-- If [a real vector is nonzero](hyp:hx), then
[the sum of its absolute coordinate values is strictly positive](goal). -/
lemma coordinateAbsSum_pos {n : ℕ} {x : Fin n → ℝ} (hx : x ≠ 0) :
    0 < coordinateAbsSum x := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  exact lt_of_lt_of_le (abs_pos.mpr hi)
    (Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i))

-- @node: coordinateAbsSum_smul
/-- Scaling [a real vector](hyp:x) by [a real number](hyp:a)
[multiplies its coordinate absolute sum by the absolute value of that number](goal). -/
lemma coordinateAbsSum_smul {n : ℕ} (a : ℝ) (x : Fin n → ℝ) :
    coordinateAbsSum (a • x) = |a| * coordinateAbsSum x := by
  simp [coordinateAbsSum, abs_mul, Finset.mul_sum]

-- @node: coordinateAbsSum_neg
/-- Negating [a real vector](hyp:x)
[leaves the sum of its absolute coordinate values unchanged](goal). -/
lemma coordinateAbsSum_neg {n : ℕ} (x : Fin n → ℝ) :
    coordinateAbsSum (-x) = coordinateAbsSum x := by
  simp [coordinateAbsSum]

-- @node: signedRadialToSphere
/-- For [a point on the signed cross-polytope](hyp:x) in [dimension n](hyp:n),
its [radial image on the sup-norm unit sphere](goal) is obtained by dividing
the vector by its sup norm. -/
def signedRadialToSphere {n : ℕ} (x : (signedGeometricComplex n).space) :
    Metric.sphere (0 : Fin n → ℝ) 1 :=
  ⟨‖x.val‖⁻¹ • x.val, by
    have hn : ‖x.val‖ ≠ 0 := norm_ne_zero_iff.mpr (signedGeometricComplex_ne_zero x.property)
    simp [Metric.mem_sphere, dist_eq_norm, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), hn]⟩

-- @node: sphereToSignedRadial
/-- For [a point on the sup-norm unit sphere](hyp:x) in [dimension n](hyp:n),
its [radial image on the signed cross-polytope](goal) is obtained by dividing
the vector by the sum of its absolute coordinate values. -/
def sphereToSignedRadial {n : ℕ} (x : Metric.sphere (0 : Fin n → ℝ) 1) :
    (signedGeometricComplex n).space :=
  ⟨(coordinateAbsSum x.val)⁻¹ • x.val, by
    have hx : x.val ≠ 0 := by
      intro hx
      simpa [hx, Metric.mem_sphere, dist_eq_norm] using x.property
    apply signedGeometricComplex_mem_of_sum_abs_eq_one
    change coordinateAbsSum ((coordinateAbsSum x.val)⁻¹ • x.val) = 1
    rw [coordinateAbsSum_smul, abs_of_pos (inv_pos.mpr (coordinateAbsSum_pos hx))]
    exact inv_mul_cancel₀ (ne_of_gt (coordinateAbsSum_pos hx))⟩

-- @node: signedRadialToSphere_continuous
/-- In [dimension n](hyp:n), [radial normalization from the signed cross-polytope
to the sup-norm unit sphere is continuous](goal). -/
@[fun_prop] lemma signedRadialToSphere_continuous (n : ℕ) :
    Continuous (signedRadialToSphere (n := n)) := by
  first | fun_prop | skip
  unfold signedRadialToSphere
  apply Continuous.subtype_mk
  have h : Continuous (fun x : (signedGeometricComplex n).space => ‖x.val‖⁻¹) :=
    continuous_subtype_val.norm.inv₀ (fun x =>
      norm_ne_zero_iff.mpr (signedGeometricComplex_ne_zero x.property))
  exact h.smul continuous_subtype_val

-- @node: sphereToSignedRadial_continuous
/-- In [dimension n](hyp:n), [radial normalization from the sup-norm unit sphere
to the signed cross-polytope is continuous](goal). -/
@[fun_prop] lemma sphereToSignedRadial_continuous (n : ℕ) :
    Continuous (sphereToSignedRadial (n := n)) := by
  first | fun_prop | skip
  unfold sphereToSignedRadial
  apply Continuous.subtype_mk
  have h : Continuous (fun x : Metric.sphere (0 : Fin n → ℝ) 1 =>
      (coordinateAbsSum x.val)⁻¹) := by
    apply ((coordinateAbsSum_continuous n).comp continuous_subtype_val).inv₀
    intro x
    apply ne_of_gt (coordinateAbsSum_pos ?_)
    intro hx
    simpa [hx, Metric.mem_sphere, dist_eq_norm] using x.property
  exact h.smul continuous_subtype_val

-- @node: sphereToSignedRadial_left_inverse
/-- In [dimension n](hyp:n), [sending a signed cross-polytope point to the
sup-norm unit sphere and then back by radial normalization recovers that point](goal). -/
lemma sphereToSignedRadial_left_inverse (n : ℕ) :
    Function.LeftInverse (sphereToSignedRadial (n := n)) signedRadialToSphere := by
  intro x
  apply Subtype.ext
  have hs : coordinateAbsSum x.val = 1 := signedGeometricComplex_sum_abs_eq_one x.property
  have hn : ‖x.val‖ ≠ 0 := norm_ne_zero_iff.mpr (signedGeometricComplex_ne_zero x.property)
  change (coordinateAbsSum (‖x.val‖⁻¹ • x.val))⁻¹ • (‖x.val‖⁻¹ • x.val) = x.val
  rw [coordinateAbsSum_smul, hs, mul_one,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_inv, smul_smul,
    mul_inv_cancel₀ hn, one_smul]

-- @node: signedRadialToSphere_left_inverse
/-- In [dimension n](hyp:n), [sending a sup-norm unit-sphere point to the signed
cross-polytope and then back by radial normalization recovers that point](goal). -/
lemma signedRadialToSphere_left_inverse (n : ℕ) :
    Function.LeftInverse (signedRadialToSphere (n := n)) sphereToSignedRadial := by
  intro x
  apply Subtype.ext
  have hn : ‖x.val‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using x.property
  have hx : x.val ≠ 0 := by intro h; simpa [h] using hn
  have hs := ne_of_gt (coordinateAbsSum_pos hx)
  change ‖(coordinateAbsSum x.val)⁻¹ • x.val‖⁻¹ •
    ((coordinateAbsSum x.val)⁻¹ • x.val) = x.val
  rw [norm_smul, Real.norm_eq_abs, hn, mul_one,
    abs_of_pos (inv_pos.mpr (coordinateAbsSum_pos hx)), inv_inv, smul_smul,
    mul_inv_cancel₀ hs, one_smul]

-- @node: signedSphereHomeomorph
/-- In [dimension n](hyp:n), the [radial homeomorphism between the signed
cross-polytope and the sup-norm unit sphere](goal) sends each point to its
sup-norm normalization and returns it by normalization with its coordinate absolute sum. -/
def signedSphereHomeomorph (n : ℕ) :
    (signedGeometricComplex n).space ≃ₜ Metric.sphere (0 : Fin n → ℝ) 1 where
  toFun := signedRadialToSphere
  invFun := sphereToSignedRadial
  left_inv := sphereToSignedRadial_left_inverse n
  right_inv := signedRadialToSphere_left_inverse n
  continuous_toFun := signedRadialToSphere_continuous n
  continuous_invFun := sphereToSignedRadial_continuous n

-- @node: signedSphereHomeomorph_antipode
/-- For [a point on the signed cross-polytope](hyp:x),
[the radial homeomorphism sends its antipode to the antipode of its image](goal). -/
lemma signedSphereHomeomorph_antipode {n : ℕ} (x : (signedGeometricComplex n).space) :
    signedSphereHomeomorph n ⟨-x.val, signedGeometricComplex_neg_mem x.property⟩ =
      -signedSphereHomeomorph n x := by
  apply Subtype.ext
  change ‖-x.val‖⁻¹ • -x.val = -(‖x.val‖⁻¹ • x.val)
  rw [norm_neg, smul_neg]

end
end Papers.TbsNeuralCausalPi.Antipodal
