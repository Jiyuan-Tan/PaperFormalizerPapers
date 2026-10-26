module
public import Papers.OaiMetricMarkovCotype.Basic

/-! # Explicit finite cut coordinates for real ℓ₁ configurations

The base and positive cut vectors are defined coordinatewise. Membership in ℓ₁
is a separate proof obligation, rather than a choice of decomposition witnesses.
-/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Papers.OaiMetricMarkovCotype

variable {n : ℕ}

-- @node: ass:cuts-data
/-- For [a number of labels](hyp:n) and [a family of absolutely summable real sequences indexed by those labels](hyp:_x),
[the cut-data condition](goal) says that there is at least one label. -/
def CutsData (n : ℕ) (_x : Fin n → RealEllOne) : Prop := 0 < n

/-- For [a family of absolutely summable real sequences](hyp:x) with [n labels](hyp:n),
[a subset of labels](hyp:B), and [a coordinate](hyp:k), [the coordinate minimum](goal)
is the smallest value in that subset at that coordinate, or zero if the subset is empty. -/
def coordinateMin (x : Fin n → RealEllOne) (B : Finset (Fin n)) (k : ℕ) : ℝ :=
  if h : B.Nonempty then B.inf' h (fun i => x i k) else 0

/-- For [a family of absolutely summable real sequences](hyp:x) with [n labels](hyp:n),
[a subset of labels](hyp:B), and [a coordinate](hyp:k), [the coordinate maximum](goal)
is the largest value in that subset at that coordinate, or zero if the subset is empty. -/
def coordinateMax (x : Fin n → RealEllOne) (B : Finset (Fin n)) (k : ℕ) : ℝ :=
  if h : B.Nonempty then B.sup' h (fun i => x i k) else 0

-- @node: coordinateMin_norm_le
/-- For [a family of absolutely summable real sequences](hyp:x), [a subset of labels](hyp:B),
and [a coordinate](hyp:k), [the absolute value of the subset's coordinate minimum is at most
the sum of the absolute coordinate values over all labels](goal). -/
lemma coordinateMin_norm_le (x : Fin n → RealEllOne) (B : Finset (Fin n)) (k : ℕ) :
    ‖coordinateMin x B k‖ ≤ ∑ i, ‖x i k‖ := by
  classical
  by_cases h : B.Nonempty
  · obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_inf' h (fun i => x i k)
    rw [coordinateMin, dif_pos h, heq]
    exact Finset.single_le_sum (fun j _ => norm_nonneg (x j k)) (Finset.mem_univ i)
  · simp only [coordinateMin, dif_neg h, norm_zero]
    exact Finset.sum_nonneg (fun i _ => norm_nonneg (x i k))

-- @node: coordinateMax_norm_le
/-- For [a family of absolutely summable real sequences](hyp:x), [a subset of labels](hyp:B),
and [a coordinate](hyp:k), [the absolute value of the subset's coordinate maximum is at most
the sum of the absolute coordinate values over all labels](goal). -/
lemma coordinateMax_norm_le (x : Fin n → RealEllOne) (B : Finset (Fin n)) (k : ℕ) :
    ‖coordinateMax x B k‖ ≤ ∑ i, ‖x i k‖ := by
  classical
  by_cases h : B.Nonempty
  · obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup' h (fun i => x i k)
    rw [coordinateMax, dif_pos h, heq]
    exact Finset.single_le_sum (fun j _ => norm_nonneg (x j k)) (Finset.mem_univ i)
  · simp only [coordinateMax, dif_neg h, norm_zero]
    exact Finset.sum_nonneg (fun i _ => norm_nonneg (x i k))

-- @node: coordinateNormSum_memℓp
/-- For [a finite family of absolutely summable real sequences](hyp:x),
[the sequence obtained by summing their absolute values at each coordinate is absolutely summable](goal). -/
lemma coordinateNormSum_memℓp (x : Fin n → RealEllOne) :
    Memℓp (fun k => ∑ i, ‖x i k‖) 1 := by
  classical
  have hs (s : Finset (Fin n)) : Memℓp (fun k => ∑ i ∈ s, ‖x i k‖) 1 := by
    induction s using Finset.induction_on with
    | empty => simp [Memℓp]
    | @insert i s hi ih =>
      simpa [Memℓp, Finset.sum_insert hi, Pi.add_apply] using (lp.memℓp (x i)).norm.add ih
  exact hs Finset.univ

-- @node: cutBase_memℓp
/-- For [a finite family of absolutely summable real sequences](hyp:x),
[the sequence of coordinate minima over all labels is absolutely summable](goal). -/
lemma cutBase_memℓp (x : Fin n → RealEllOne) :
    Memℓp (coordinateMin x Finset.univ) 1 := by
  exact (coordinateNormSum_memℓp x).mono (coordinateMin_norm_le x Finset.univ)

/-- For [a family of absolutely summable real sequences](hyp:x) with [n labels](hyp:n),
[the cut base](goal) is the absolutely summable sequence of minima over all labels,
using zero at every coordinate if there are no labels.

@realizes v(coordinatewise minimum of all input sequences) -/
def cutBase (x : Fin n → RealEllOne) : RealEllOne :=
  ⟨coordinateMin x Finset.univ, cutBase_memℓp x⟩

/-- For [a family of absolutely summable real sequences](hyp:x) with [n labels](hyp:n),
[a subset of labels](hyp:B), and [a coordinate](hyp:k), [the cut coordinate](goal)
is the positive part of the minimum inside the subset minus the maximum outside it
when the subset is nonempty and proper, and zero otherwise. -/
def cutCoordinate (x : Fin n → RealEllOne) (B : Finset (Fin n)) (k : ℕ) : ℝ :=
  if B.Nonempty ∧ B ≠ Finset.univ then
    max (coordinateMin x B k - coordinateMax x (Finset.univ \ B) k) 0 else 0

-- @node: cutCoordinate_norm_le
/-- For [a family of absolutely summable real sequences](hyp:x), [a subset of labels](hyp:B),
and [a coordinate](hyp:k), [the absolute cut coordinate is at most twice the sum
of absolute coordinate values over all labels](goal). -/
lemma cutCoordinate_norm_le (x : Fin n → RealEllOne) (B : Finset (Fin n)) (k : ℕ) :
    ‖cutCoordinate x B k‖ ≤ 2 * ∑ i, ‖x i k‖ := by
  classical
  by_cases h : B.Nonempty ∧ B ≠ Finset.univ
  · rw [cutCoordinate, if_pos h, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    apply max_le
    · have hmin := coordinateMin_norm_le x B k
      have hmax := coordinateMax_norm_le x (Finset.univ \ B) k
      have hsub := norm_sub_le (coordinateMin x B k) (coordinateMax x (Finset.univ \ B) k)
      have hle := le_abs_self (coordinateMin x B k - coordinateMax x (Finset.univ \ B) k)
      rw [← Real.norm_eq_abs] at hle
      linarith
    · exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => norm_nonneg (x i k)))
  · rw [cutCoordinate, if_neg h, norm_zero]
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => norm_nonneg (x i k)))

-- @node: cutVector_memℓp
/-- For [a finite family of absolutely summable real sequences](hyp:x) and [a subset of labels](hyp:B),
[the sequence of cut coordinates is absolutely summable](goal). -/
lemma cutVector_memℓp (x : Fin n → RealEllOne) (B : Finset (Fin n)) :
    Memℓp (cutCoordinate x B) 1 := by
  have h : Memℓp (fun k => 2 * ∑ i, ‖x i k‖) 1 := by
    simpa [Memℓp, Pi.smul_apply, smul_eq_mul] using (coordinateNormSum_memℓp x).const_smul (2 : ℝ)
  exact h.mono (cutCoordinate_norm_le x B)

/-- For [a family of absolutely summable real sequences](hyp:x) with [n labels](hyp:n)
and [a subset of labels](hyp:B), [the cut vector](goal) is the absolutely summable
sequence of nonnegative cut coordinates for that subset.

@realizes b_B(positive part of the minimum on the cut minus the maximum off it) -/
def cutVector (x : Fin n → RealEllOne) (B : Finset (Fin n)) : RealEllOne :=
  ⟨cutCoordinate x B, cutVector_memℓp x B⟩

/-- For [a family of absolutely summable real sequences](hyp:x) with [n labels](hyp:n),
[the retained cuts](goal) are the nonempty proper subsets whose cut vectors have strictly positive norm.

@realizes \mathcal B(nonempty proper subsets with strictly positive cut norm)
@realizes B(retained cut, a nonempty proper subset of Fin n) -/
def cutIndex (x : Fin n → RealEllOne) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun B => B.Nonempty ∧ B ≠ Finset.univ ∧ 0 < ‖cutVector x B‖)

/-- For [a family of absolutely summable real sequences](hyp:x) with [n labels](hyp:n)
and [a retained cut](hyp:B), [the cut weight](goal) is the ℓ₁ norm of its cut vector.

@realizes w_B(norm of each retained cut vector) -/
def cutWeight (x : Fin n → RealEllOne) (B : ↥(cutIndex x)) : ℝ := ‖cutVector x B.val‖

/-- For [a family of absolutely summable real sequences](hyp:x) with [n labels](hyp:n)
and [a label](hyp:i), [the cut encoding](goal) assigns one to retained cuts containing
that label and zero to all other retained cuts.

@realizes z_i(binary incidence encoding)
@realizes \ind(indicator of state membership in the cut) -/
def cutEncoding (x : Fin n → RealEllOne) (i : Fin n) : ↥(cutIndex x) → ℝ :=
  fun B => if i ∈ B.val then 1 else 0

/-- For [a family of absolutely summable real sequences](hyp:x) with [n labels](hyp:n)
and [real coefficients indexed by its retained cuts](hyp:u), [the reconstruction](goal)
is the cut base plus the sum of the cut vectors multiplied by their respective coefficients.

@realizes T(affine reconstruction: base plus the weighted sum of cut vectors) -/
def cutReconstruction (x : Fin n → RealEllOne) (u : ↥(cutIndex x) → ℝ) : RealEllOne :=
  cutBase x + ∑ B : ↥(cutIndex x), u B • cutVector x B.val

-- @node: cutCoordinate_nonneg
/-- For [a family of absolutely summable real sequences](hyp:x), [a subset of labels](hyp:B),
and [a coordinate](hyp:k), [the cut coordinate is nonnegative](goal). -/
lemma cutCoordinate_nonneg (x : Fin n → RealEllOne) (B : Finset (Fin n)) (k : ℕ) :
    0 ≤ cutCoordinate x B k := by
  classical
  unfold cutCoordinate
  split
  · exact le_max_right _ _
  · exact le_rfl

-- @node: cutCoordinate_eq_zero_of_le
/-- For [a family of absolutely summable real sequences](hyp:x), [a subset of labels](hyp:B),
and [a coordinate](hyp:k), if [a label lies inside the subset](hyp:hi),
[another label lies outside it](hyp:hj), and [the inside value is at most the outside value
at that coordinate](hyp:hij), then [the cut coordinate is zero](goal). -/
lemma cutCoordinate_eq_zero_of_le (x : Fin n → RealEllOne)
    (B : Finset (Fin n)) (k : ℕ) {i j : Fin n}
    (hi : i ∈ B) (hj : j ∉ B) (hij : x i k ≤ x j k) :
    cutCoordinate x B k = 0 := by
  classical
  by_cases h : B.Nonempty ∧ B ≠ Finset.univ
  · have hc : (Finset.univ \ B).Nonempty :=
      ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj⟩⟩
    have hmin : coordinateMin x B k ≤ x i k := by
      rw [coordinateMin, dif_pos h.1]
      exact Finset.inf'_le _ hi
    have hmax : x j k ≤ coordinateMax x (Finset.univ \ B) k := by
      rw [coordinateMax, dif_pos hc]
      exact Finset.le_sup' (fun i => x i k) (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj⟩)
    rw [cutCoordinate, if_pos h, max_eq_right]
    linarith
  · exact if_neg h

-- @node: cutWeight_positive
/-- For [a finite family of absolutely summable real sequences](hyp:x),
[every retained cut has strictly positive weight](goal). -/
lemma cutWeight_positive (x : Fin n → RealEllOne) : PositiveWeights (cutWeight x) := by
  classical
  intro B
  exact (Finset.mem_filter.mp B.property).2.2.2

-- @node: cutEncoding_binary
/-- For [a finite family of absolutely summable real sequences](hyp:x) and [a label](hyp:i),
[every entry of its cut encoding is either zero or one](goal). -/
lemma cutEncoding_binary (x : Fin n → RealEllOne) (i : Fin n) :
    BinaryVector (cutEncoding x i) := by
  classical
  intro B
  by_cases h : i ∈ B.val
  · exact Or.inr (if_pos h)
  · exact Or.inl (if_neg h)

-- @node: cutEncoding_norm_identity
/-- For [a finite family of absolutely summable real sequences](hyp:x) and [two labels](hyp:i,j),
[the weighted ℓ₁ norm of the difference of their cut encodings equals its squared weighted
Euclidean norm](goal). -/
lemma cutEncoding_norm_identity (x : Fin n → RealEllOne) (i j : Fin n) :
    weightedL1Norm (cutWeight x) (cutEncoding x i - cutEncoding x j) =
      weightedHNormSq (cutWeight x) (cutEncoding x i - cutEncoding x j) := by
  classical
  unfold weightedL1Norm weightedHNormSq
  apply Finset.sum_congr rfl
  intro B _
  rcases cutEncoding_binary x i B with hi | hi <;>
    rcases cutEncoding_binary x j B with hj | hj <;>
    simp [Pi.sub_apply, hi, hj]

-- @node: cutReconstruction_sub
/-- For [a finite family of absolutely summable real sequences](hyp:x) and
[two coefficient vectors on the retained cuts](hyp:u,u'), [the difference of their
reconstructions is the sum of the cut vectors multiplied by the corresponding coefficient differences](goal). -/
lemma cutReconstruction_sub (x : Fin n → RealEllOne)
    (u u' : ↥(cutIndex x) → ℝ) :
    cutReconstruction x u - cutReconstruction x u' =
      ∑ B : ↥(cutIndex x), (u B - u' B) • cutVector x B.val := by
  classical
  simp only [cutReconstruction, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib,
    sub_smul]

-- @node: cutReconstruction_contraction
/-- For [a finite family of absolutely summable real sequences](hyp:x) and
[two coefficient vectors on the retained cuts](hyp:u,u'), [the ℓ₁ distance between their
reconstructions is at most the weighted ℓ₁ distance between the coefficient vectors](goal). -/
lemma cutReconstruction_contraction (x : Fin n → RealEllOne)
    (u u' : ↥(cutIndex x) → ℝ) :
    ‖cutReconstruction x u - cutReconstruction x u'‖ ≤
      weightedL1Norm (cutWeight x) (u - u') := by
  classical
  rw [cutReconstruction_sub]
  calc
    ‖∑ B : ↥(cutIndex x), (u B - u' B) • cutVector x B.val‖ ≤
        ∑ B : ↥(cutIndex x), ‖(u B - u' B) • cutVector x B.val‖ :=
      norm_sum_le _ _
    _ = weightedL1Norm (cutWeight x) (u - u') := by
      simp [weightedL1Norm, cutWeight, norm_smul, Real.norm_eq_abs, mul_comm]

-- @node: realEllOne_norm_eq_tsum_abs
/-- For [an absolutely summable real sequence](hyp:a), [its ℓ₁ norm is the infinite sum
of the absolute values of its coordinates](goal). -/
lemma realEllOne_norm_eq_tsum_abs (a : RealEllOne) : ‖a‖ = ∑' k, |a k| := by
  simpa using lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal) a

-- @node: realEllOne_norm_sum_of_coordinate_sign
/-- For [a finite family of absolutely summable real sequences](hyp:f), if
[at each coordinate the entries across the family are all nonnegative or all nonpositive](hyp:hs),
then [the ℓ₁ norm of their sum equals the sum of their ℓ₁ norms](goal). -/
lemma realEllOne_norm_sum_of_coordinate_sign {ι : Type*} [Fintype ι]
    (f : ι → RealEllOne)
    (hs : ∀ k, (∀ B, 0 ≤ f B k) ∨ (∀ B, f B k ≤ 0)) :
    ‖∑ B, f B‖ = ∑ B, ‖f B‖ := by
  classical
  simp only [realEllOne_norm_eq_tsum_abs, lp.coeFn_sum, Finset.sum_apply]
  have habs (k : ℕ) : |∑ B, f B k| = ∑ B, |f B k| := by
    rcases hs k with h | h
    · rw [abs_of_nonneg (Finset.sum_nonneg (fun B _ => h B))]
      exact Finset.sum_congr rfl (fun B _ => (abs_of_nonneg (h B)).symm)
    · rw [abs_of_nonpos (Finset.sum_nonpos (fun B _ => h B))]
      simp_rw [abs_of_nonpos (h _)]
      simp
  simp_rw [habs]
  exact Summable.tsum_finsetSum (fun B _ => by
    simpa using (lp.memℓp (f B)).summable (by norm_num : 0 < (1 : ENNReal).toReal))

-- @node: cutEncoding_increment_coordinate_sign
/-- For [a finite family of absolutely summable real sequences](hyp:x), [two labels](hyp:i,j),
and [a coordinate](hyp:k), [the cut-vector contributions to the difference of their
reconstructions are all nonnegative at that coordinate or all nonpositive there](goal). -/
lemma cutEncoding_increment_coordinate_sign (x : Fin n → RealEllOne) (i j : Fin n)
    (k : ℕ) :
    (∀ B : ↥(cutIndex x), 0 ≤
      ((cutEncoding x i B - cutEncoding x j B) • cutVector x B.val) k) ∨
    (∀ B : ↥(cutIndex x),
      ((cutEncoding x i B - cutEncoding x j B) • cutVector x B.val) k ≤ 0) := by
  classical
  rcases le_total (x j k) (x i k) with hji | hij
  · left
    intro B
    change 0 ≤ (cutEncoding x i B - cutEncoding x j B) * cutCoordinate x B.val k
    by_cases hi : i ∈ B.val <;> by_cases hj : j ∈ B.val
    · simp [cutEncoding, hi, hj]
    · simpa [cutEncoding, hi, hj] using cutCoordinate_nonneg x B.val k
    · rw [cutCoordinate_eq_zero_of_le x B.val k hj hi hji, mul_zero]
    · simp [cutEncoding, hi, hj]
  · right
    intro B
    change (cutEncoding x i B - cutEncoding x j B) * cutCoordinate x B.val k ≤ 0
    by_cases hi : i ∈ B.val <;> by_cases hj : j ∈ B.val
    · simp [cutEncoding, hi, hj]
    · rw [cutCoordinate_eq_zero_of_le x B.val k hi hj hij, mul_zero]
    · simpa [cutEncoding, hi, hj] using neg_nonpos.mpr (cutCoordinate_nonneg x B.val k)
    · simp [cutEncoding, hi, hj]

-- @node: cutReconstruction_encoding_distance
/-- For [a finite family of absolutely summable real sequences](hyp:x) and [two labels](hyp:i,j),
[the ℓ₁ distance between their reconstructed encodings equals the weighted ℓ₁ distance
between their encodings](goal). -/
lemma cutReconstruction_encoding_distance (x : Fin n → RealEllOne) (i j : Fin n) :
    ‖cutReconstruction x (cutEncoding x i) - cutReconstruction x (cutEncoding x j)‖ =
      weightedL1Norm (cutWeight x) (cutEncoding x i - cutEncoding x j) := by
  rw [cutReconstruction_sub,
    realEllOne_norm_sum_of_coordinate_sign _ (cutEncoding_increment_coordinate_sign x i j)]
  simp [weightedL1Norm, cutWeight, norm_smul, Real.norm_eq_abs, mul_comm]

-- @node: cutReconstruction_affine
/-- For [a finite family of absolutely summable real sequences](hyp:x), [a real scalar](hyp:r),
and [two coefficient vectors on the retained cuts](hyp:u,u'), [reconstructing their affine
combination with coefficients equal to the scalar and one minus the scalar gives the same
affine combination of their reconstructions](goal). -/
lemma cutReconstruction_affine (x : Fin n → RealEllOne)
    (r : ℝ) (u u' : ↥(cutIndex x) → ℝ) :
    cutReconstruction x (r • u + (1 - r) • u') =
      r • cutReconstruction x u + (1 - r) • cutReconstruction x u' := by
  classical
  simp only [cutReconstruction, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    add_smul, mul_smul, Finset.sum_add_distrib, smul_add, Finset.smul_sum]
  have hbase : r • cutBase x + (1 - r) • cutBase x = cutBase x := by
    rw [← add_smul]
    simp
  module

-- @node: cutCoordinate_pos_cross
/-- For [a family of absolutely summable real sequences](hyp:x), [a subset of labels](hyp:B),
and [a coordinate](hyp:k), if [the cut coordinate is strictly positive](hyp:hpos),
[one label lies inside the subset](hyp:hi), and [another lies outside it](hyp:hj), then
[the outside value is strictly smaller than the inside value at that coordinate](goal). -/
lemma cutCoordinate_pos_cross (x : Fin n → RealEllOne) (B : Finset (Fin n)) (k : ℕ)
    (hpos : 0 < cutCoordinate x B k) {i j : Fin n} (hi : i ∈ B) (hj : j ∉ B) :
    x j k < x i k := by
  by_contra h
  have hz := cutCoordinate_eq_zero_of_le x B k hi hj (le_of_not_gt h)
  linarith

-- @node: cutReconstruction_encoding_apply
/-- For [a finite family of absolutely summable real sequences](hyp:x), [a label](hyp:i),
and [a coordinate](hyp:k), [the reconstruction of that label's encoding at that coordinate
equals the minimum over all labels plus the sum of the cut coordinates of retained cuts
containing the label](goal). -/
lemma cutReconstruction_encoding_apply (x : Fin n → RealEllOne) (i : Fin n) (k : ℕ) :
    cutReconstruction x (cutEncoding x i) k = coordinateMin x Finset.univ k +
      ∑ B : ↥(cutIndex x), (if i ∈ B.val then cutCoordinate x B.val k else 0) := by
  classical
  unfold cutReconstruction
  rw [lp.coeFn_add, Pi.add_apply, lp.coeFn_sum, Finset.sum_apply]
  change coordinateMin x Finset.univ k +
    ∑ B : ↥(cutIndex x), (cutEncoding x i B) * cutCoordinate x B.val k = _
  congr 1
  apply Finset.sum_congr rfl
  intro B _
  split_ifs with hi <;> simp [cutEncoding, hi]

-- @node: cutReconstruction_encoding_min
/-- For [a finite family of absolutely summable real sequences](hyp:x), [a label](hyp:i),
and [a coordinate](hyp:k), if [that label attains a minimum over all labels at the coordinate](hyp:hmin),
then [reconstructing its encoding recovers its original value at that coordinate](goal). -/
lemma cutReconstruction_encoding_min (x : Fin n → RealEllOne) (i : Fin n) (k : ℕ)
    (hmin : ∀ j, x i k ≤ x j k) :
    cutReconstruction x (cutEncoding x i) k = x i k := by
  classical
  rw [cutReconstruction_encoding_apply]
  have hb : coordinateMin x Finset.univ k = x i k := by
    rw [coordinateMin, dif_pos ⟨i, Finset.mem_univ _⟩]
    exact le_antisymm (Finset.inf'_le _ (Finset.mem_univ i))
      (Finset.le_inf' _ _ (fun j _ => hmin j))
  rw [hb]
  suffices h : (∑ B : ↥(cutIndex x),
      if i ∈ B.val then cutCoordinate x B.val k else 0) = 0 by rw [h, add_zero]
  apply Finset.sum_eq_zero
  intro B _
  split_ifs with hi
  · have hproper := (Finset.mem_filter.mp B.property).2.2.1
    have hex : ∃ j, j ∉ B.val := by
      by_contra h
      apply hproper
      ext j
      simp only [Finset.mem_univ, iff_true]
      exact Classical.not_not.mp (fun hj => h ⟨j, hj⟩)
    obtain ⟨j, hj⟩ := hex
    exact cutCoordinate_eq_zero_of_le x B.val k hi hj (hmin j)
  · rfl

-- @node: cutCoordinate_upper_gap
/-- For [a finite family of absolutely summable real sequences](hyp:x), [two labels](hyp:i,j),
and [a coordinate](hyp:k), if [the second label's value is strictly below the first's](hyp:hij)
and [every label's value is at most the lower value or at least the upper value](hyp:hgap),
then [the cut consisting of labels strictly above the lower value has cut coordinate
equal to the gap between these two values](goal). -/
lemma cutCoordinate_upper_gap (x : Fin n → RealEllOne) (i j : Fin n) (k : ℕ)
    (hij : x j k < x i k)
    (hgap : ∀ a, x a k ≤ x j k ∨ x i k ≤ x a k) :
    cutCoordinate x (Finset.univ.filter (fun a => x j k < x a k)) k =
      x i k - x j k := by
  classical
  let B := Finset.univ.filter (fun a => x j k < x a k)
  have hi : i ∈ B := by simp [B, hij]
  have hj : j ∉ B := by simp [B]
  have hB : B.Nonempty := ⟨i, hi⟩
  have hproper : B ≠ Finset.univ := by
    intro h
    exact hj (h.symm ▸ Finset.mem_univ j)
  have hjc : j ∈ Finset.univ \ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj⟩
  have hc : (Finset.univ \ B).Nonempty := ⟨j, hjc⟩
  have hmin : coordinateMin x B k = x i k := by
    rw [coordinateMin, dif_pos hB]
    apply le_antisymm (Finset.inf'_le _ hi)
    apply Finset.le_inf'
    intro a ha
    exact (hgap a).resolve_left (not_le.mpr (Finset.mem_filter.mp ha).2)
  have hmax : coordinateMax x (Finset.univ \ B) k = x j k := by
    rw [coordinateMax, dif_pos hc]
    apply le_antisymm _ (Finset.le_sup' (fun a => x a k) hjc)
    apply Finset.sup'_le
    intro a ha
    have haB := (Finset.mem_sdiff.mp ha).2
    simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using haB
  change cutCoordinate x B k = _
  rw [cutCoordinate, if_pos ⟨hB, hproper⟩, hmin, hmax, max_eq_left (sub_nonneg.mpr hij.le)]

-- @node: cutCoordinate_adjacent_support
/-- For [a finite family of absolutely summable real sequences](hyp:x), [two labels](hyp:i,j),
and [a coordinate](hyp:k), suppose [every label's value is at most the second label's value
or at least the first label's value](hyp:hgap). If [a subset of labels](hyp:B) has
[strictly positive cut coordinate](hyp:hpos), [contains the first label](hyp:hi), and
[excludes the second label](hyp:hj), then [it consists exactly of the labels whose values
are strictly above the second label's value](goal). -/
lemma cutCoordinate_adjacent_support (x : Fin n → RealEllOne) (i j : Fin n) (k : ℕ)
    (hgap : ∀ a, x a k ≤ x j k ∨ x i k ≤ x a k)
    (B : Finset (Fin n)) (hpos : 0 < cutCoordinate x B k)
    (hi : i ∈ B) (hj : j ∉ B) :
    B = Finset.univ.filter (fun a => x j k < x a k) := by
  classical
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro ha
    exact cutCoordinate_pos_cross x B k hpos ha hj
  · intro ha
    by_contra haB
    have hlt := cutCoordinate_pos_cross x B k hpos hi haB
    rcases hgap a with h | h <;> linarith

-- @node: cutReconstruction_encoding_adjacent
/-- For [a finite family of absolutely summable real sequences](hyp:x), [two labels](hyp:i,j),
and [a coordinate](hyp:k), if [the second label's value is strictly below the first's](hyp:hij)
and [every label's value is at most the lower value or at least the upper value](hyp:hgap),
then [the difference between the reconstructed encodings at that coordinate equals
the difference between the original coordinate values](goal). -/
lemma cutReconstruction_encoding_adjacent (x : Fin n → RealEllOne) (i j : Fin n) (k : ℕ)
    (hij : x j k < x i k)
    (hgap : ∀ a, x a k ≤ x j k ∨ x i k ≤ x a k) :
    cutReconstruction x (cutEncoding x i) k -
      cutReconstruction x (cutEncoding x j) k = x i k - x j k := by
  classical
  let B := Finset.univ.filter (fun a => x j k < x a k)
  have hi : i ∈ B := by simp [B, hij]
  have hj : j ∉ B := by simp [B]
  have hb : cutCoordinate x B k = x i k - x j k :=
    cutCoordinate_upper_gap x i j k hij hgap
  have hB : B ∈ cutIndex x := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ⟨i, hi⟩, ?_, ?_⟩
    · intro h
      exact hj (h.symm ▸ Finset.mem_univ j)
    · apply norm_pos_iff.mpr
      intro hz
      have hz' := congrArg (fun a : RealEllOne => a k) hz
      change cutCoordinate x B k = 0 at hz'
      rw [hb] at hz'
      linarith
  let C : ↥(cutIndex x) := ⟨B, hB⟩
  rw [cutReconstruction_encoding_apply, cutReconstruction_encoding_apply,
    add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single C]
  · simpa only [C, if_pos hi, if_neg hj, sub_zero] using hb
  · intro D _ hDC
    have hDB : D.val ≠ B := fun h => hDC (Subtype.ext h)
    by_cases hDi : i ∈ D.val <;> by_cases hDj : j ∈ D.val
    · simp only [if_pos hDi, if_pos hDj, sub_self]
    · simp only [if_pos hDi, if_neg hDj, sub_zero]
      apply le_antisymm _ (cutCoordinate_nonneg x D.val k)
      by_contra h
      exact hDB (cutCoordinate_adjacent_support x i j k hgap D.val
        (lt_of_not_ge h) hDi hDj)
    · rw [if_neg hDi, if_pos hDj,
        cutCoordinate_eq_zero_of_le x D.val k hDj hDi hij.le, sub_self]
    · simp only [if_neg hDi, if_neg hDj, sub_self]
  · simp

-- @node: cutReconstruction_encoding
/-- For [a finite family of absolutely summable real sequences](hyp:x) and [a label](hyp:i),
[reconstructing that label's cut encoding recovers its original sequence](goal). -/
lemma cutReconstruction_encoding (x : Fin n → RealEllOne) (i : Fin n) :
    cutReconstruction x (cutEncoding x i) = x i := by
  classical
  ext k
  have hall : ∀ m : ℕ, ∀ a : Fin n,
      (Finset.univ.filter (fun b => x b k < x a k)).card = m →
      cutReconstruction x (cutEncoding x a) k = x a k := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro a hm
      let S := Finset.univ.filter (fun b => x b k < x a k)
      by_cases hS : S.Nonempty
      · obtain ⟨b, hb, heq⟩ := Finset.exists_mem_eq_sup' hS (fun b => x b k)
        have hba : x b k < x a k := (Finset.mem_filter.mp hb).2
        have hmax : ∀ c, x c k < x a k → x c k ≤ x b k := by
          intro c hc
          rw [← heq]
          exact Finset.le_sup' (fun b => x b k) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
        have hgap : ∀ c, x c k ≤ x b k ∨ x a k ≤ x c k := by
          intro c
          by_cases hc : x c k < x a k
          · exact Or.inl (hmax c hc)
          · exact Or.inr (le_of_not_gt hc)
        have hcard : (Finset.univ.filter (fun c => x c k < x b k)).card < m := by
          rw [← hm]
          apply Finset.card_lt_card
          apply Finset.ssubset_iff_subset_ne.mpr
          refine ⟨?_, ?_⟩
          · intro c hc
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              lt_trans (Finset.mem_filter.mp hc).2 hba⟩
          · intro he
            have hb' : b ∈ Finset.univ.filter (fun c => x c k < x b k) := he.symm ▸ hb
            exact (lt_irrefl (x b k)) (Finset.mem_filter.mp hb').2
        have hrec := ih _ hcard b rfl
        have hstep := cutReconstruction_encoding_adjacent x a b k hba hgap
        linarith
      · apply cutReconstruction_encoding_min x a k
        intro b
        by_contra h
        exact hS ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge h⟩⟩
  exact hall _ i rfl

-- @node: lem:cuts
/-- For [a finite family of absolutely summable real sequences](hyp:x) with
[at least one label](hyp:h_data), [either all sequences coincide, or the retained cuts
form a nonempty set with positive weights and binary encodings that reconstruct every
sequence, preserve all pairwise distances as both weighted ℓ₁ distances and squared
weighted Euclidean distances, and admit an affine reconstruction that contracts
weighted ℓ₁ distances](goal). -/
lemma cut_decomposition (x : Fin n → RealEllOne) (h_data : CutsData n x) :
    (∀ i j, x i = x j) ∨
      (Nonempty ↥(cutIndex x) ∧
        PositiveWeights (cutWeight x) ∧
        (∀ i, BinaryVector (cutEncoding x i)) ∧
        (∀ i, cutReconstruction x (cutEncoding x i) = x i) ∧
        (∀ i j, ‖x i - x j‖ =
            weightedL1Norm (cutWeight x) (cutEncoding x i - cutEncoding x j) ∧
          weightedL1Norm (cutWeight x) (cutEncoding x i - cutEncoding x j) =
            weightedHNormSq (cutWeight x) (cutEncoding x i - cutEncoding x j)) ∧
        (∀ u u', ‖cutReconstruction x u - cutReconstruction x u'‖ ≤
          weightedL1Norm (cutWeight x) (u - u')) ∧
        (∀ (r : ℝ) u u',
          cutReconstruction x (r • u + (1 - r) • u') =
            r • cutReconstruction x u + (1 - r) • cutReconstruction x u')) := by
  classical
  have hreconstruct : ∀ i, cutReconstruction x (cutEncoding x i) = x i :=
    cutReconstruction_encoding x
  by_cases hsame : ∀ i j, x i = x j
  · exact Or.inl hsame
  · right
    have hnonempty : Nonempty ↥(cutIndex x) := by
      by_contra h
      haveI : IsEmpty ↥(cutIndex x) := ⟨fun B => h ⟨B⟩⟩
      apply hsame
      intro i j
      rw [← hreconstruct i, ← hreconstruct j]
      simp [cutReconstruction]
    exact ⟨hnonempty, cutWeight_positive x, cutEncoding_binary x, hreconstruct,
      fun i j => ⟨by
        rw [← hreconstruct i, ← hreconstruct j]
        exact cutReconstruction_encoding_distance x i j,
        cutEncoding_norm_identity x i j⟩,
      cutReconstruction_contraction x, cutReconstruction_affine x⟩

end Papers.OaiMetricMarkovCotype
