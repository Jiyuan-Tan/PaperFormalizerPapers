module

public import Papers.OaiSmoothNonquadraticAffine.Basic

/-! # Coordinate projection and Euclidean distance for the invariant-box proof -/

@[expose] public section

noncomputable section

namespace OaiSmoothNonquadraticAffine

/-- For [a three-dimensional point z](hyp:z), its [projection onto the closed box](goal)
clips each coordinate to the interval from zero to the corresponding upper corner. -/
def boxProjection (z : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => max 0 (min (boxCorner i) (z i)) -- @realizes \Pi(coordinatewise box projection)

/-- For [a three-dimensional point z](hyp:z), the [distance to the box](goal) is the
Euclidean distance from z to its coordinatewise projection onto the box. -/
def boxDistance (z : Fin 3 → ℝ) : ℝ :=
  ‖WithLp.toLp 2 (z - boxProjection z)‖ -- @realizes d(nonnegative Euclidean distance)

/-- For [a proposed Lipschitz constant L](hyp:L) and [a set N of three-dimensional
points](hyp:N), the [Lipschitz bound for the autonomous field on N](goal) requires
[L to be nonnegative](step:1) and [the Euclidean distance between field values at
any two points of N to be at most L times the distance between those points](step:2). -/
def BoxFieldLipschitzBound (L : ℝ) (N : Set (Fin 3 → ℝ)) : Prop :=
  0 ≤ L ∧ ∀ z ∈ N, ∀ z' ∈ N,
    ‖WithLp.toLp 2 (autonomousField z - autonomousField z')‖ ≤
      L * ‖WithLp.toLp 2 (z - z')‖ -- @realizes L(local Euclidean Lipschitz bound for V)


-- @node: boxCorner_pos
/-- [Every coordinate of the upper corner of the box is strictly positive](goal). -/
lemma boxCorner_pos (i : Fin 3) : 0 < boxCorner i := by
  fin_cases i <;> norm_num [boxCorner]

-- @node: autonomousField_corner
/-- [The autonomous vector field vanishes at the upper corner of the box](goal). -/
lemma autonomousField_corner : autonomousField boxCorner = 0 := by
  ext i
  fin_cases i
  · change (9 / 2 : ℝ) * (1 + 7 / 2 - 9 / 2) = 0
    norm_num
  · change (7 / 2 : ℝ) * (9 + 9 / 2 + (12 / 11) * (7 / 2) * (33 / 7) - 9 * (7 / 2)) = 0
    norm_num
  · change (11 - 33 / 7 : ℝ) * (9 / 2) - 8 * (33 / 7) +
      (7 / 2) * (33 / 7) * (1 - (33 / 7) / 11) = 0
    norm_num

-- @node: autonomousField_lower_face
/-- If [z belongs to the closed box](hyp:hz) and [its i-th coordinate is zero](hyp:hi),
then [the i-th component of the autonomous field at z is nonnegative](goal). -/
lemma autonomousField_lower_face {z : Fin 3 → ℝ} (hz : z ∈ boxB)
    (i : Fin 3) (hi : z i = 0) : 0 ≤ autonomousField z i := by
  fin_cases i
  · change 0 ≤ z 0 * (1 + z 1 - z 0)
    change z 0 = 0 at hi
    rw [hi]
    simp
  · change 0 ≤ z 1 * (9 + z 0 + (12 / 11 : ℝ) * z 1 * z 2 - 9 * z 1)
    change z 1 = 0 at hi
    rw [hi]
    simp
  · change 0 ≤ (11 - z 2) * z 0 - 8 * z 2 + z 1 * z 2 * (1 - z 2 / 11)
    change z 2 = 0 at hi
    rw [hi]
    have hA : 0 ≤ z 0 := hz.1 0
    nlinarith

-- @node: autonomousField_upper_face
/-- If [z belongs to the closed box](hyp:hz) and [its i-th coordinate equals the
corresponding upper corner coordinate](hyp:hi), then [the i-th component of the
autonomous field at z is nonpositive](goal). -/
lemma autonomousField_upper_face {z : Fin 3 → ℝ} (hz : z ∈ boxB)
    (i : Fin 3) (hi : z i = boxCorner i) : autonomousField z i ≤ 0 := by
  have hA : 0 ≤ z 0 := hz.1 0
  have hB : 0 ≤ z 1 := hz.1 1
  have hD : 0 ≤ z 2 := hz.1 2
  have hAu : z 0 ≤ 9 / 2 := hz.2 0
  have hBu : z 1 ≤ 7 / 2 := hz.2 1
  have hDu : z 2 ≤ 33 / 7 := hz.2 2
  fin_cases i
  · have hi' : z 0 = 9 / 2 := hi
    change z 0 * (1 + z 1 - z 0) ≤ 0
    rw [hi']
    nlinarith
  · have hi' : z 1 = 7 / 2 := hi
    change z 1 * (9 + z 0 + (12 / 11 : ℝ) * z 1 * z 2 - 9 * z 1) ≤ 0
    rw [hi']
    nlinarith
  · have hi' : z 2 = 33 / 7 := hi
    change (11 - z 2) * z 0 - 8 * z 2 + z 1 * z 2 * (1 - z 2 / 11) ≤ 0
    rw [hi']
    nlinarith

-- @node: boxProjection_mem
/-- [The coordinatewise projection of any three-dimensional point belongs to the closed box](goal). -/
lemma boxProjection_mem (z : Fin 3 → ℝ) : boxProjection z ∈ boxB := by
  constructor
  · intro i
    exact le_max_left _ _
  · intro i
    exact max_le (boxCorner_pos i).le (min_le_left _ _)

-- @node: boxProjection_eq_self
/-- If [z belongs to the closed box](hyp:hz), then [its coordinatewise projection equals z](goal). -/
lemma boxProjection_eq_self {z : Fin 3 → ℝ} (hz : z ∈ boxB) : boxProjection z = z := by
  funext i
  dsimp [boxProjection]
  have hl : 0 ≤ z i := hz.1 i
  rw [min_eq_right (hz.2 i), max_eq_right hl]

-- @node: boxProjection_sq_le
/-- If [p belongs to the closed box](hyp:hp), then [in every coordinate, the squared
distance from z to its projection is no greater than the squared distance from z to p](goal). -/
lemma boxProjection_sq_le (z : Fin 3 → ℝ) {p : Fin 3 → ℝ} (hp : p ∈ boxB)
    (i : Fin 3) : (z i - boxProjection z i) ^ 2 ≤ (z i - p i) ^ 2 := by
  have hpl : 0 ≤ p i := hp.1 i
  have hpu : p i ≤ boxCorner i := hp.2 i
  have hc := (boxCorner_pos i).le
  dsimp [boxProjection]
  rcases le_total (z i) 0 with hz | hz
  · rw [min_eq_right (hz.trans hc), max_eq_left hz]
    nlinarith
  · rcases le_total (z i) (boxCorner i) with hu | hu
    · rw [min_eq_right hu, max_eq_right hz]
      nlinarith [sq_nonneg (z i - p i)]
    · rw [min_eq_left hu, max_eq_right hc]
      nlinarith

-- @node: boxProjection_field_inner_nonpos
/-- [The inner product of the displacement from the box projection to z with the
autonomous field evaluated at that projection is nonpositive](goal). -/
lemma boxProjection_field_inner_nonpos (z : Fin 3 → ℝ) :
    ∑ i, (z i - boxProjection z i) * autonomousField (boxProjection z) i ≤ 0 := by
  apply Finset.sum_nonpos
  intro i _
  have hp := boxProjection_mem z
  have hc := (boxCorner_pos i).le
  rcases le_total (z i) 0 with hz | hz
  · have he : boxProjection z i = 0 := by
      simp [boxProjection, min_eq_right (hz.trans hc), max_eq_left hz]
    rw [he, sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg hz (autonomousField_lower_face hp i he)
  · rcases le_total (z i) (boxCorner i) with hu | hu
    · have he : boxProjection z i = z i := by
        simp [boxProjection, min_eq_right hu, max_eq_right hz]
      simp [he]
    · have he : boxProjection z i = boxCorner i := by
        simp [boxProjection, min_eq_left hu, max_eq_right hc]
      rw [he]
      exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hu)
        (autonomousField_upper_face hp i he)

end OaiSmoothNonquadraticAffine
