module

public import Papers.OaiCapacityCriterionState.Helpers.CapacityLabels
public import Mathlib.Algebra.Order.Chebyshev

/-! # Small labels and their cubic loss

Positive capacity supplies arbitrarily small nonlinear subsolutions. Bounded
branching turns the coordinatewise nonlinear deficit into a cubic deficit in
the total incoming information, the deterministic budget needed in the converse.
-/

public section

open scoped BigOperators

namespace OaiCapacityCriterionState

variable {B : ℕ}

-- @node: nonlinearLabel_scale
/-- If [c is nonnegative](hyp:hc), [c is at most one](hyp:hc1), and [x is
nonnegative](hyp:hx), [c times x/√(1 + x²) is at most
cx/√(1 + (cx)²)](goal). -/
lemma nonlinearLabel_scale {c x : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) (hx : 0 ≤ x) :
    c * (x / Real.sqrt (1 + x ^ 2)) ≤
      (c * x) / Real.sqrt (1 + (c * x) ^ 2) := by
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_left (mul_nonneg hc hx) (by positivity)
  apply Real.sqrt_le_sqrt
  have hcx : c * x ≤ x := by nlinarith
  nlinarith [mul_nonneg hc hx]

-- @node: FlowLabelRecursion.scale
/-- If [z is a nonnegative labeling bounded at each vertex by the sum of
λ²z/√(1 + z²) over its children](hyp:hz), [c is nonnegative](hyp:hc), and [c is
at most one](hyp:hc1), [multiplying every label by c preserves this nonlinear
recursion inequality](goal). -/
lemma FlowLabelRecursion.scale (T : BoundedTree B) (lam : ℝ)
    (z : List (Fin B) → ℝ) (hz : FlowLabelRecursion T lam z)
    {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    FlowLabelRecursion T lam (fun v => c * z v) := by
  classical
  intro v hv
  refine ⟨mul_nonneg hc (hz v hv).1, ?_⟩
  calc
    c * z v ≤ c * ∑ w ∈ T.children v,
        sqParam lam * z w / Real.sqrt (1 + z w ^ 2) :=
      mul_le_mul_of_nonneg_left (hz v hv).2 hc
    _ = ∑ w ∈ T.children v,
        sqParam lam * (c * (z w / Real.sqrt (1 + z w ^ 2))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro w hw
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
      have hx := (hz (a :: v) (Finset.mem_filter.mp ha).2).1
      simpa only [mul_div_assoc, sqParam] using
        mul_le_mul_of_nonneg_left (nonlinearLabel_scale hc hc1 hx) (sq_nonneg lam)

-- @node: BoundedTree.children_card_le
/-- In a tree with branching bound B, [the number of children of any vertex
is at most B](goal). -/
lemma BoundedTree.children_card_le (T : BoundedTree B) (v : List (Fin B)) :
    (T.children v).card ≤ B := by
  classical
  exact (Finset.card_image_le).trans ((Finset.card_filter_le _ _).trans_eq (by simp))

-- @node: nonlinearLabel_le_one
/-- If [x is nonnegative](hyp:hx), [x/√(1 + x²) is at most one](goal). -/
lemma nonlinearLabel_le_one {x : ℝ} (hx : 0 ≤ x) :
    x / Real.sqrt (1 + x ^ 2) ≤ 1 := by
  apply (div_le_one (by positivity)).mpr
  have hs := Real.sq_sqrt (show 0 ≤ 1 + x ^ 2 by positivity)
  have hn := Real.sqrt_nonneg (1 + x ^ 2)
  nlinarith

-- @node: FlowLabelRecursion.le_branching
/-- If [the channel parameter lies strictly between zero and one](hyp:hlam),
[z is nonnegative and each label is at most the sum of λ²z/√(1 + z²) over its
children](hyp:hz), and [v is a vertex of the tree](hyp:hv), [the label at v is
at most the branching bound B](goal). -/
lemma FlowLabelRecursion.le_branching (T : BoundedTree B) (lam : ℝ)
    (hlam : MainLambda lam) (z : List (Fin B) → ℝ)
    (hz : FlowLabelRecursion T lam z) (v : List (Fin B)) (hv : v ∈ T.verts) :
    z v ≤ B := by
  classical
  calc
    z v ≤ _ := (hz v hv).2
    _ ≤ ∑ _w ∈ T.children v, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro w hw
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
      have hx := (hz (a :: v) (Finset.mem_filter.mp ha).2).1
      rw [mul_div_assoc]
      exact (mul_le_mul_of_nonneg_left (nonlinearLabel_le_one hx) (sq_nonneg lam)).trans
        (by simpa only [mul_one, sqParam] using (sqParam_mem_Ioo lam hlam).2.le)
    _ ≤ B := by simpa using (Nat.cast_le (α := ℝ)).mpr (T.children_card_le v)

-- @node: capacity_pos_iff_small_labels
/-- For [an infinite tree with positive branching bound](hyp:hT), [a channel
parameter strictly between zero and one](hyp:hlam), and [a positive bound
δ](hyp:hdelta), [positive cubic capacity is equivalent to the existence of
nonnegative vertex labels with a positive root label, all at most δ, each label
being at most the sum of λ²z/√(1 + z²) over its children](goal). -/
theorem capacity_pos_iff_small_labels (T : BoundedTree B) (lam : ℝ)
    (hT : MainTree T) (hlam : MainLambda lam) {delta : ℝ} (hdelta : 0 < delta) :
    0 < capacity3 T lam ↔ ∃ z : List (Fin B) → ℝ,
      FlowLabelRecursion T lam z ∧ 0 < z [] ∧ ∀ v ∈ T.verts, z v ≤ delta := by
  constructor
  · intro hcap
    obtain ⟨z, hz, hroot⟩ := (capacity_pos_iff_positive_labels T lam hT hlam).mp hcap
    let c := delta / ((B : ℝ) + delta + 1)
    have hden : 0 < (B : ℝ) + delta + 1 := by positivity
    have hc : 0 < c := div_pos hdelta hden
    have hc1 : c ≤ 1 := (div_le_one hden).mpr (by
      have hB : (0 : ℝ) ≤ B := by positivity
      linarith)
    refine ⟨fun v => c * z v, hz.scale T lam z hc.le hc1,
      mul_pos hc hroot, ?_⟩
    intro v hv
    calc
      c * z v ≤ c * B := mul_le_mul_of_nonneg_left
        (hz.le_branching T lam hlam z v hv) hc.le
      _ ≤ delta := by
        dsimp [c]
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ hden).mpr
        nlinarith
  · rintro ⟨z, hz, hroot, _⟩
    exact (capacity_pos_iff_positive_labels T lam hT hlam).mpr ⟨z, hz, hroot⟩

-- @node: nonlinearLabel_cubic_deficit
/-- If [x is nonnegative](hyp:hx) and [x is at most M](hyp:hxM),
[x/√(1 + x²) is at most x − x³/(2(1 + M²))](goal). -/
lemma nonlinearLabel_cubic_deficit {x M : ℝ} (hx : 0 ≤ x) (hxM : x ≤ M) :
    x / Real.sqrt (1 + x ^ 2) ≤ x - x ^ 3 / (2 * (1 + M ^ 2)) := by
  let s := Real.sqrt (1 + x ^ 2)
  have hs : s ^ 2 = 1 + x ^ 2 := Real.sq_sqrt (by positivity)
  have hs1 : 1 ≤ s := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (by nlinarith : (1 : ℝ) ≤ 1 + x ^ 2)
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs1
  have hdiff : 0 ≤ x - x / s := sub_nonneg.mpr (div_le_self hx hs1)
  have hden : s ^ 2 + s ≤ 2 * (1 + M ^ 2) := by nlinarith
  have hid : (x - x / s) * (s ^ 2 + s) = x ^ 3 := by
    calc
      _ = x * (s ^ 2 - 1) := by field_simp; ring
      _ = _ := by rw [hs]; ring
  have hcubic : x ^ 3 ≤ (x - x / s) * (2 * (1 + M ^ 2)) := by
    rw [← hid]
    exact mul_le_mul_of_nonneg_left hden hdiff
  have hquot : x ^ 3 / (2 * (1 + M ^ 2)) ≤ x - x / s :=
    (div_le_iff₀ (by positivity)).mpr hcubic
  change x / s ≤ _
  linarith

-- @node: FlowLabelRecursion.cubic_budget
/-- If [the channel parameter lies strictly between zero and one](hyp:hlam),
[z is a nonnegative labeling with each label at most the sum of
λ²z/√(1 + z²) over its children](hyp:hz),
[every label is at most M](hyp:hM), and [v belongs to the tree](hyp:hv),
[the incoming sum S of λ² times child labels satisfies
2(1 + M²)B²z(v) + S³ ≤ 2(1 + M²)B²S, where B is the branching bound](goal). -/
lemma FlowLabelRecursion.cubic_budget (T : BoundedTree B) (lam : ℝ)
    (hlam : MainLambda lam) (z : List (Fin B) → ℝ)
    (hz : FlowLabelRecursion T lam z) (M : ℝ)
    (hM : ∀ w ∈ T.verts, z w ≤ M) (v : List (Fin B)) (hv : v ∈ T.verts) :
    let S := ∑ w ∈ T.children v, sqParam lam * z w
    (2 * (1 + M ^ 2) * (B : ℝ) ^ 2) * z v + S ^ 3 ≤
      (2 * (1 + M ^ 2) * (B : ℝ) ^ 2) * S := by
  classical
  let r := sqParam lam
  let A := 2 * (1 + M ^ 2)
  let S := ∑ w ∈ T.children v, r * z w
  let U := ∑ w ∈ T.children v, r * z w ^ 3
  have hr : 0 ≤ r := (sqParam_mem_Ioo lam hlam).1.le
  have hr1 : r ≤ 1 := (sqParam_mem_Ioo lam hlam).2.le
  have hA : 0 < A := by dsimp [A]; positivity
  have hchild (w : List (Fin B)) (hw : w ∈ T.children v) : w ∈ T.verts := by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
    exact (Finset.mem_filter.mp ha).2
  have hx (w : List (Fin B)) (hw : w ∈ T.children v) : 0 ≤ z w :=
    (hz w (hchild w hw)).1
  have hU : 0 ≤ U := Finset.sum_nonneg (fun w hw => mul_nonneg hr (pow_nonneg (hx w hw) _))
  have hdeficit : z v ≤ S - U / A := by
    calc
      z v ≤ _ := (hz v hv).2
      _ ≤ ∑ w ∈ T.children v, r * (z w - z w ^ 3 / A) := by
        apply Finset.sum_le_sum
        intro w hw
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left
          (nonlinearLabel_cubic_deficit (hx w hw) (hM w (hchild w hw))) hr
      _ = S - U / A := by
        dsimp [S, U]
        simp only [mul_sub, div_eq_mul_inv, ← mul_assoc,
          Finset.sum_sub_distrib, Finset.sum_mul]
  have hpower : S ^ 3 ≤ (B : ℝ) ^ 2 * U := by
    calc
      S ^ 3 ≤ ((T.children v).card : ℝ) ^ 2 *
          ∑ w ∈ T.children v, (r * z w) ^ 3 :=
        pow_sum_le_card_mul_sum_pow (fun w hw => mul_nonneg hr (hx w hw)) 2
      _ ≤ (B : ℝ) ^ 2 * U := by
        apply mul_le_mul
        · exact pow_le_pow_left₀ (by positivity)
            ((Nat.cast_le (α := ℝ)).mpr (T.children_card_le v)) 2
        · apply Finset.sum_le_sum
          intro w hw
          have hr3 : r ^ 3 ≤ r := by nlinarith [mul_nonneg hr (sub_nonneg.mpr hr1)]
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_right hr3 (pow_nonneg (hx w hw) _)
        · exact Finset.sum_nonneg (fun w hw => pow_nonneg (mul_nonneg hr (hx w hw)) _)
        · positivity
  have hdeficit' : A * z v + U ≤ A * S := by
    have h := mul_le_mul_of_nonneg_left hdeficit hA.le
    rw [mul_sub, mul_div_cancel₀ _ (ne_of_gt hA)] at h
    linarith
  have h := mul_le_mul_of_nonneg_left hdeficit' (sq_nonneg (B : ℝ))
  change A * (B : ℝ) ^ 2 * z v + S ^ 3 ≤ A * (B : ℝ) ^ 2 * S
  nlinarith

-- @node: capacity_pos_small_cubic_labels
/-- For [an infinite tree with positive branching bound](hyp:hT), [a channel
parameter strictly between zero and one](hyp:hlam), and [a positive bound
δ](hyp:hdelta), [positive cubic capacity](hyp:hcap) ensures [there are nonnegative
labels with each label at most the sum of λ²z/√(1 + z²) over its children, with positive root label
and all labels at most δ, such that at every vertex
2(1 + δ²)B²z(v) + S³ ≤ 2(1 + δ²)B²S, where S is the sum of λ² times child
labels and B is the branching bound](goal). -/
theorem capacity_pos_small_cubic_labels (T : BoundedTree B) (lam : ℝ)
    (hT : MainTree T) (hlam : MainLambda lam) {delta : ℝ} (hdelta : 0 < delta)
    (hcap : 0 < capacity3 T lam) :
    ∃ z : List (Fin B) → ℝ, FlowLabelRecursion T lam z ∧ 0 < z [] ∧
      (∀ v ∈ T.verts, z v ≤ delta) ∧ ∀ v ∈ T.verts,
        let S := ∑ w ∈ T.children v, sqParam lam * z w
        (2 * (1 + delta ^ 2) * (B : ℝ) ^ 2) * z v + S ^ 3 ≤
          (2 * (1 + delta ^ 2) * (B : ℝ) ^ 2) * S := by
  obtain ⟨z, hz, hroot, hsmall⟩ :=
    (capacity_pos_iff_small_labels T lam hT hlam hdelta).mp hcap
  exact ⟨z, hz, hroot, hsmall, hz.cubic_budget T lam hlam z delta hsmall⟩

-- @node: rescale_cubic_budget
/-- If [A is positive](hyp:hA), [c is nonnegative](hyp:hc), [S is
nonnegative](hyp:hS), [Ax + S³ ≤ AS](hyp:hbudget), and [ACc² ≤ 1](hyp:hcoeff),
[the rescaled values satisfy cx + C(cS)³ ≤ cS](goal). -/
lemma rescale_cubic_budget {A C c x S : ℝ} (hA : 0 < A) (hc : 0 ≤ c)
    (hS : 0 ≤ S) (hbudget : A * x + S ^ 3 ≤ A * S)
    (hcoeff : A * C * c ^ 2 ≤ 1) :
    c * x + C * (c * S) ^ 3 ≤ c * S := by
  apply le_of_mul_le_mul_left _ hA
  calc
    A * (c * x + C * (c * S) ^ 3) =
        c * (A * x) + (A * C * c ^ 2) * (c * S ^ 3) := by ring
    _ ≤ c * (A * x) + c * S ^ 3 := by
      exact add_le_add_right (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoeff
          (mul_nonneg hc (pow_nonneg hS 3))) _
    _ = c * (A * x + S ^ 3) := by ring
    _ ≤ c * (A * S) := mul_le_mul_of_nonneg_left hbudget hc
    _ = A * (c * S) := by ring

-- @node: capacity_pos_arbitrary_cubic_budget
/-- For [an infinite tree with positive branching bound](hyp:hT), [a channel
parameter strictly between zero and one](hyp:hlam), [a positive label bound
δ](hyp:hdelta), and [a nonnegative cubic penalty C](hyp:hC), [positive cubic
capacity](hyp:hcap) ensures [there are nonnegative labels with each label at most
the sum of λ²a/√(1 + a²) over its children, with positive root label and all labels at most δ, such that
a(v) + CS³ ≤ S at every vertex, where S is the sum of λ² times child labels](goal). -/
lemma capacity_pos_arbitrary_cubic_budget (T : BoundedTree B) (lam : ℝ)
    (hT : MainTree T) (hlam : MainLambda lam) {delta C : ℝ}
    (hdelta : 0 < delta) (hC : 0 ≤ C) (hcap : 0 < capacity3 T lam) :
    ∃ a : List (Fin B) → ℝ, FlowLabelRecursion T lam a ∧ 0 < a [] ∧
      (∀ v ∈ T.verts, a v ≤ delta) ∧ ∀ v ∈ T.verts,
        let S := ∑ w ∈ T.children v, sqParam lam * a w
        a v + C * S ^ 3 ≤ S := by
  classical
  obtain ⟨z, hz, hroot, hsmall, hbudget⟩ :=
    capacity_pos_small_cubic_labels T lam hT hlam zero_lt_one hcap
  let A : ℝ := 2 * (1 + (1 : ℝ) ^ 2) * (B : ℝ) ^ 2
  have hB : (0 : ℝ) < B := hroot.trans_le (hz.le_branching T lam hlam z [] T.nil_mem)
  have hA : 0 < A := by dsimp [A]; positivity
  have hAC : 0 ≤ A * C := mul_nonneg hA.le hC
  have hden : 0 < A * C + 1 := by positivity
  let c := min 1 (min delta (1 / (A * C + 1)))
  have hc : 0 < c := lt_min zero_lt_one (lt_min hdelta (div_pos zero_lt_one hden))
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcd : c ≤ delta := (min_le_right _ _).trans (min_le_left _ _)
  have hclin : c * (A * C + 1) ≤ 1 := (le_div_iff₀ hden).mp
    ((min_le_right _ _).trans (min_le_right _ _))
  have hcoeff : A * C * c ^ 2 ≤ 1 := by
    have hsq : c ^ 2 ≤ c := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hsq hAC
    nlinarith
  refine ⟨fun v => c * z v, hz.scale T lam z hc.le hc1, mul_pos hc hroot, ?_, ?_⟩
  · intro v hv
    exact (mul_le_mul_of_nonneg_left (hsmall v hv) hc.le).trans (by simpa using hcd)
  · intro v hv
    have hS : 0 ≤ ∑ w ∈ T.children v, sqParam lam * z w := by
      apply Finset.sum_nonneg
      intro w hw
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
      exact mul_nonneg (sq_nonneg lam) (hz _ (Finset.mem_filter.mp hi).2).1
    have hsum : (∑ w ∈ T.children v, sqParam lam * (c * z w)) =
        c * ∑ w ∈ T.children v, sqParam lam * z w := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      ring
    dsimp only
    rw [hsum]
    exact rescale_cubic_budget hA hc.le hS (hbudget v hv) hcoeff

end OaiCapacityCriterionState
