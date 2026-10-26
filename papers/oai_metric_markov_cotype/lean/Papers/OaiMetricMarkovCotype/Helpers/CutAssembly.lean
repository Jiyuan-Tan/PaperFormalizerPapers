module
public import Papers.OaiMetricMarkovCotype.Helpers.StoppedEnergy

/-! # Transfer of the killed-walk energy estimate to real ℓ₁ points -/

public section

open MeasureTheory
open scoped BigOperators
namespace Papers.OaiMetricMarkovCotype

variable {n : ℕ}

/-- Given [a family h of real cut coordinates, one vector for each point](hyp:h),
[the squared distance from point i to the reconstruction of the cubed coordinates
at i is at most the squared weighted ℓ₁ distance between its cut encoding and
those cubed coordinates](goal). -/
-- @node: cutReconstruction_approximation_le
lemma cutReconstruction_approximation_le (x : Fin n → RealEllOne)
    (h : Fin n → ↥(cutIndex x) → ℝ) (i : Fin n) :
    dist (x i) (cutReconstruction x (cubicMap (h i))) ^ 2 ≤
      weightedL1Norm (cutWeight x) (cutEncoding x i - cubicMap (h i)) ^ 2 := by
  have hc := cutReconstruction_contraction x (cutEncoding x i) (cubicMap (h i))
  rw [cutReconstruction_encoding] at hc
  exact pow_le_pow_left₀ dist_nonneg (by simpa [dist_eq_norm] using hc) 2

/-- Given [a family h of real cut coordinates, one vector for each point](hyp:h),
[the squared distance between the reconstructions of the cubed coordinates at
i and j is at most the squared weighted ℓ₁ distance between those cubed
coordinate vectors](goal). -/
-- @node: cutReconstruction_transition_le
lemma cutReconstruction_transition_le (x : Fin n → RealEllOne)
    (h : Fin n → ↥(cutIndex x) → ℝ) (i j : Fin n) :
    dist (cutReconstruction x (cubicMap (h i)))
      (cutReconstruction x (cubicMap (h j))) ^ 2 ≤
      weightedL1Norm (cutWeight x) (cubicMap (h i) - cubicMap (h j)) ^ 2 := by
  exact pow_le_pow_left₀ dist_nonneg
    (by simpa [dist_eq_norm] using
      cutReconstruction_contraction x (cubicMap (h i)) (cubicMap (h j))) 2

/-- If [π is a probability vector](hyp:hπ) and [A is a stochastic transition
matrix](hyp:hA), then, for [a family h of real cut coordinates](hyp:h), [the
π-weighted squared approximation error of the reconstructed cubed coordinates
plus t times their transition energy is at most the cut-coordinate approximation
cost plus t times the smoothed cut-coordinate energy](goal). -/
-- @node: cutReconstruction_cotype_cost_le
lemma cutReconstruction_cotype_cost_le (t : ℕ)
    (π : Fin n → ℝ) (hπ : IsProbabilityVector π)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A)
    (x : Fin n → RealEllOne) (h : Fin n → ↥(cutIndex x) → ℝ) :
    (∑ i, π i * dist (x i) (cutReconstruction x (cubicMap (h i))) ^ 2) +
      (t : ℝ) * ∑ i, ∑ j, π i * A i j *
        dist (cutReconstruction x (cubicMap (h i)))
          (cutReconstruction x (cubicMap (h j))) ^ 2 ≤
      approxCost π (cutWeight x) (cutEncoding x) h +
        (t : ℝ) * smoothedEnergy π A (cutWeight x) h := by
  apply add_le_add
  · apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (cutReconstruction_approximation_le x h i) (hπ.1 i)
  · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg t)
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (cutReconstruction_transition_le x h i j)
      (mul_nonneg (hπ.1 i) (hA.nonneg i j))

/-- If [t is a strictly positive geometric time parameter](hyp:ht), [π is a
probability vector](hyp:hπ), [A is stochastic](hyp:hA), and [A is reversible
with respect to π](hyp:hrev), then [the π-weighted squared error of the modified
points plus t times their transition energy is at most 108 times the expected
quartic cut potential between the stopped walk's initial encoding and its
terminal value, using the resolvent as its live-state values](goal).

This includes coincident input points, for which the positive cut index can be empty. -/
-- @node: modifiedPoints_cotype_cost_le_quartic
lemma modifiedPoints_cotype_cost_le_quartic (t : ℕ) (ht : GeometricParameterDomain t)
    (π : Fin n → ℝ) (hπ : IsProbabilityVector π)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A)
    (hrev : IsReversible A π) (x : Fin n → RealEllOne) :
    (∑ i, π i * dist (x i) (modifiedPoints t ht π A x i) ^ 2) +
      (t : ℝ) * ∑ i, ∑ j, π i * A i j *
        dist (modifiedPoints t ht π A x i) (modifiedPoints t ht π A x j) ^ 2 ≤
      108 * ∫ ω, quarticPotential (cutWeight x)
        (stoppedWalkValue (cutEncoding x) (cutEncoding x) 0 ω)
        (stoppedWalkTerminal (resolvent t ht A (cutEncoding x)) (cutEncoding x) ω)
          ∂stoppedWalkMeasure t ht π A hA := by
  classical
  by_cases hsame : ∀ i j, x i = x j
  · have hd (i j : Fin n) : dist (x i) (x j) = 0 := by rw [hsame i j, dist_self]
    simp only [modifiedPoints, if_pos hsame, dist_self, hd,
      zero_pow (by omega : 2 ≠ 0), mul_zero, Finset.sum_const_zero, add_zero]
    exact mul_nonneg (by norm_num) (integral_nonneg fun ω => sq_nonneg _)
  · have hn : 0 < n := by
      by_contra hn
      apply hsame
      intro i
      have := i.isLt
      omega
    have hcuts := cut_decomposition x hn
    have hfinite : FiniteCutIndex ↥(cutIndex x) := (hcuts.resolve_left hsame).1
    have he := stoppedWalk_approxCost_add_energy_le t ht π hπ A hA hrev
      (cutWeight x) (cutWeight_positive x) hfinite (cutEncoding x) (cutEncoding_binary x)
    simp only [modifiedPoints, if_neg hsame]
    exact (cutReconstruction_cotype_cost_le t π hπ A hA x
      (resolvent t ht A (cutEncoding x))).trans he

/-- [The quartic potential between the cut encodings of points i and j, using
their cut weights, equals the squared ℓ₁ distance between the original points](goal). -/
-- @node: cutEncoding_quarticPotential_eq_dist_sq
lemma cutEncoding_quarticPotential_eq_dist_sq (x : Fin n → RealEllOne) (i j : Fin n) :
    quarticPotential (cutWeight x) (cutEncoding x i) (cutEncoding x j) =
      dist (x i) (x j) ^ 2 := by
  unfold quarticPotential
  rw [← cutEncoding_norm_identity, ← cutReconstruction_encoding_distance,
    cutReconstruction_encoding, cutReconstruction_encoding]
  rw [dist_eq_norm, norm_sub_rev]

/-- If [t is a strictly positive geometric time parameter](hyp:ht), [π is a
probability vector](hyp:hπ), and [A is stochastic](hyp:hA), then [almost surely
under the stopped-walk law, the quartic cut potential between the initial
encoding and terminal value equals the squared distance from the original
starting point to the reconstructed terminal value, with the resolvent providing
the walk's live-state values](goal). -/
-- @node: stoppedWalk_cut_potential_eq_endpoint_ae
lemma stoppedWalk_cut_potential_eq_endpoint_ae (t : ℕ) (ht : GeometricParameterDomain t)
    (π : Fin n → ℝ) (hπ : IsProbabilityVector π)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A)
    (x : Fin n → RealEllOne) :
    (fun ω => quarticPotential (cutWeight x)
      (stoppedWalkValue (cutEncoding x) (cutEncoding x) 0 ω)
      (stoppedWalkTerminal (resolvent t ht A (cutEncoding x)) (cutEncoding x) ω)) =ᵐ[
        stoppedWalkMeasure t ht π A hA]
    (fun ω => dist (Sum.elim x x (ω 0))
      (cutReconstruction x
        (stoppedWalkTerminal (resolvent t ht A (cutEncoding x)) (cutEncoding x) ω)) ^ 2) := by
  filter_upwards [stoppedWalkTerminal_eq_input t ht π hπ A hA
    (resolvent t ht A (cutEncoding x)) (cutEncoding x)] with ω hω
  obtain ⟨j, hj, _⟩ := hω
  rw [hj, cutReconstruction_encoding]
  unfold stoppedWalkValue
  cases ω 0 with
  | inl i => exact cutEncoding_quarticPotential_eq_dist_sq x i j
  | inr i => exact cutEncoding_quarticPotential_eq_dist_sq x i j

-- @node: stoppedWalk_cut_potential_integral_eq_endpoint
/-- If [t is a strictly positive geometric time parameter](hyp:ht), [π is a
probability vector](hyp:hπ), and [A is stochastic](hyp:hA), then [the expected
quartic cut potential between the stopped walk's initial encoding and terminal
value equals the expected squared distance from its original starting point
to the reconstructed terminal value, using the resolvent as the live-state
values](goal). -/
lemma stoppedWalk_cut_potential_integral_eq_endpoint (t : ℕ)
    (ht : GeometricParameterDomain t) (π : Fin n → ℝ) (hπ : IsProbabilityVector π)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A)
    (x : Fin n → RealEllOne) :
    (∫ ω, quarticPotential (cutWeight x)
      (stoppedWalkValue (cutEncoding x) (cutEncoding x) 0 ω)
      (stoppedWalkTerminal (resolvent t ht A (cutEncoding x)) (cutEncoding x) ω)
        ∂stoppedWalkMeasure t ht π A hA) =
    ∫ ω, dist (Sum.elim x x (ω 0))
      (cutReconstruction x
        (stoppedWalkTerminal (resolvent t ht A (cutEncoding x)) (cutEncoding x) ω)) ^ 2
          ∂stoppedWalkMeasure t ht π A hA := by
  exact integral_congr_ae (stoppedWalk_cut_potential_eq_endpoint_ae t ht π hπ A hA x)

/-- If [t is a strictly positive geometric time parameter](hyp:ht), [π is a
probability vector](hyp:hπ), and [A is stochastic](hyp:hA), then [the quartic
cut potential between the stopped walk's initial encoding and terminal value
is integrable under the stopped-walk law, with the resolvent providing the
live-state values](goal). -/
-- @node: integrable_stoppedWalk_cut_potential
lemma integrable_stoppedWalk_cut_potential (t : ℕ) (ht : GeometricParameterDomain t)
    (π : Fin n → ℝ) (hπ : IsProbabilityVector π)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A)
    (x : Fin n → RealEllOne) :
    Integrable (fun ω => quarticPotential (cutWeight x)
      (stoppedWalkValue (cutEncoding x) (cutEncoding x) 0 ω)
      (stoppedWalkTerminal (resolvent t ht A (cutEncoding x)) (cutEncoding x) ω))
        (stoppedWalkMeasure t ht π A hA) := by
  let := stoppedWalkMeasure_isProbabilityMeasure t ht π hπ A hA
  apply Integrable.of_bound
    (stronglyMeasurable_quarticPotential
      (stronglyMeasurable_stoppedWalkTerminal _ _)
      (stronglyMeasurable_stoppedWalkValue _ _ 0) (cutWeight x)).aestronglyMeasurable
    ((∑ B, cutWeight x B) ^ 2)
  filter_upwards [stoppedWalkTerminal_eq_input t ht π hπ A hA
    (resolvent t ht A (cutEncoding x)) (cutEncoding x)] with ω hω
  obtain ⟨j, hj, _⟩ := hω
  rw [hj]
  have he : BinaryVector (stoppedWalkValue (cutEncoding x) (cutEncoding x) 0 ω) := by
    unfold stoppedWalkValue
    cases ω 0 <;> exact cutEncoding_binary x _
  exact quarticPotential_cube_bound (cutWeight x) _ _ (cutWeight_positive x)
    (binaryVector_mem_unitCube (cutEncoding_binary x j)) he

-- @node: integrable_stoppedWalk_cut_endpoint
/-- If [t is a strictly positive geometric time parameter](hyp:ht), [π is a
probability vector](hyp:hπ), and [A is stochastic](hyp:hA), then [the squared
distance from the original starting point to the reconstructed terminal value
is integrable under the stopped-walk law, with the resolvent providing the
live-state values](goal). -/
lemma integrable_stoppedWalk_cut_endpoint (t : ℕ) (ht : GeometricParameterDomain t)
    (π : Fin n → ℝ) (hπ : IsProbabilityVector π)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A)
    (x : Fin n → RealEllOne) :
    Integrable (fun ω => dist (Sum.elim x x (ω 0))
      (cutReconstruction x
        (stoppedWalkTerminal (resolvent t ht A (cutEncoding x)) (cutEncoding x) ω)) ^ 2)
          (stoppedWalkMeasure t ht π A hA) := by
  exact (integrable_stoppedWalk_cut_potential t ht π hπ A hA x).congr
    (stoppedWalk_cut_potential_eq_endpoint_ae t ht π hπ A hA x)

/-- If [t is a strictly positive geometric time parameter](hyp:ht), [π is a
probability vector](hyp:hπ), [A is stochastic](hyp:hA), and [A is reversible
with respect to π](hyp:hrev), then [the π-weighted squared error of the modified
points plus t times their transition energy is at most 108 times the expected
squared distance from the stopped walk's original starting point to its
reconstructed terminal value, using the resolvent as the live-state values](goal). -/
-- @node: modifiedPoints_cotype_cost_le_endpoint
lemma modifiedPoints_cotype_cost_le_endpoint (t : ℕ) (ht : GeometricParameterDomain t)
    (π : Fin n → ℝ) (hπ : IsProbabilityVector π)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A)
    (hrev : IsReversible A π) (x : Fin n → RealEllOne) :
    (∑ i, π i * dist (x i) (modifiedPoints t ht π A x i) ^ 2) +
      (t : ℝ) * ∑ i, ∑ j, π i * A i j *
        dist (modifiedPoints t ht π A x i) (modifiedPoints t ht π A x j) ^ 2 ≤
      108 * ∫ ω, dist (Sum.elim x x (ω 0))
        (cutReconstruction x
          (stoppedWalkTerminal (resolvent t ht A (cutEncoding x)) (cutEncoding x) ω)) ^ 2
            ∂stoppedWalkMeasure t ht π A hA := by
  have he := modifiedPoints_cotype_cost_le_quartic t ht π hπ A hA hrev x
  rw [stoppedWalk_cut_potential_integral_eq_endpoint t ht π hπ A hA x] at he
  exact he

end Papers.OaiMetricMarkovCotype
