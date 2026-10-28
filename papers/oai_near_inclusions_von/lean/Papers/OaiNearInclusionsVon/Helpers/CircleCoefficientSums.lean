module

public import Papers.OaiNearInclusionsVon.Helpers.CirclePathBounds
public import Papers.OaiNearInclusionsVon.Helpers.CircleSummability

/-! Uniform absolute row and column sums of the finite Laurent matrices. -/

public section

namespace Papers.OaiNearInclusionsVon

open Papers.OaiNearInclusionsVon.ReusedTree
open scoped BigOperators

-- @node: circle_geometric_sum_injective
/-- For [a finite set s](hyp:s), [a natural-number exponent function f](hyp:f), and
[a natural-number lower bound n](hyp:n), if [f is injective on s](hyp:hinj) and
[every exponent on s is at least n](hyp:hmin), then [the sum over s of the deformation
parameter raised to these exponents is at most its n-th power divided by one minus
the deformation parameter](goal). -/
lemma circle_geometric_sum_injective {α : Type*} (s : Finset α) (f : α → ℕ) (n : ℕ)
    (hinj : Set.InjOn f s) (hmin : ∀ a ∈ s, n ≤ f a) :
    ∑ a ∈ s, tParam ^ f a ≤ tParam ^ n / (1 - tParam) := by
  classical
  have ht := circle_deformation_range.1
  have hs : HasSum (fun m : ℕ => tParam ^ (n + m))
      (tParam ^ n / (1 - tParam)) := by
    simpa only [pow_add, div_eq_mul_inv] using
      (hasSum_geometric_of_lt_one ht.le circle_deformation_range.2).mul_left (tParam ^ n)
  have hinj' : Set.InjOn (fun a => f a - n) s := by
    intro a ha b hb he
    change f a - n = f b - n at he
    apply hinj ha hb
    have := hmin a ha
    have := hmin b hb
    omega
  calc
    ∑ a ∈ s, tParam ^ f a =
        ∑ m ∈ s.image (fun a => f a - n), tParam ^ (n + m) := by
      rw [Finset.sum_image hinj']
      apply Finset.sum_congr rfl
      intro a ha
      rw [Nat.add_sub_of_le (hmin a ha)]
    _ ≤ tParam ^ n / (1 - tParam) :=
      hs.summable.sum_le_tsum _ (fun _ _ => by positivity) |>.trans_eq hs.tsum_eq

-- @node: circle_path_tail_sum
/-- For [free-group elements g and x](hyp:g,x), [a finite set of vertices s](hyp:s),
and [a natural number n](hyp:n), if [every vertex in s lies on the reduced-word path
to g](hyp:hpath) and [its word length differs from that of x by at least n](hyp:hmin),
then [the sum over s of the deformation parameter raised to these length differences
is at most twice its n-th power divided by one minus the deformation parameter](goal). -/
lemma circle_path_tail_sum (g x : FreeGrp) (s : Finset FreeGrp) (n : ℕ)
    (hpath : ∀ y ∈ s, y.toWord.IsPrefix g.toWord)
    (hmin : ∀ y ∈ s, n ≤ Nat.dist x.toWord.length y.toWord.length) :
    ∑ y ∈ s, tParam ^ (Nat.dist x.toWord.length y.toWord.length) ≤
      2 * tParam ^ n / (1 - tParam) := by
  classical
  let f := fun y : FreeGrp => Nat.dist x.toWord.length y.toWord.length
  have hinj (b : Bool) : Set.InjOn f
      (s.filter (fun y => decide (y.toWord.length ≤ x.toWord.length) = b)) := by
    intro y hy z hz he
    obtain ⟨hy, hyb⟩ := Finset.mem_filter.mp hy
    obtain ⟨hz, hzb⟩ := Finset.mem_filter.mp hz
    apply treePathVertex_eq_of_length g y z (hpath y hy) (hpath z hz)
    dsimp [f, Nat.dist] at he
    cases b with
    | false =>
      have hy' := of_decide_eq_false hyb
      have hz' := of_decide_eq_false hzb
      omega
    | true =>
      have hy' := of_decide_eq_true hyb
      have hz' := of_decide_eq_true hzb
      omega
  have hb (b : Bool) := circle_geometric_sum_injective
    (s.filter (fun y => decide (y.toWord.length ≤ x.toWord.length) = b)) f n
    (hinj b) (fun y hy => hmin y (Finset.mem_filter.mp hy).1)
  have hsplit : (∑ y ∈ s, tParam ^ f y) =
      (∑ y ∈ s.filter (fun y => decide (y.toWord.length ≤ x.toWord.length) = true),
        tParam ^ f y) +
      (∑ y ∈ s.filter (fun y => decide (y.toWord.length ≤ x.toWord.length) = false),
        tParam ^ f y) := by
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y hy
    cases decide (y.toWord.length ≤ x.toWord.length) <;> simp
  calc
    _ = _ := hsplit
    _ ≤ tParam ^ n / (1 - tParam) + tParam ^ n / (1 - tParam) := add_le_add (hb true) (hb false)
    _ = _ := by ring

-- @node: circle_coefficient_row_sum
/-- For [free-group elements g and x](hyp:g,x) and [an integer coefficient index k](hyp:k),
if [x lies on the reduced-word path to g](hyp:hx), then [the sum of the absolute
path-matrix entries in row x whose column exponent minus row exponent equals k is
at most twice the deformation parameter raised to the absolute value of k, divided
by one minus the deformation parameter](goal). -/
lemma circle_coefficient_row_sum (g x : FreeGrp) (k : ℤ)
    (hx : x.toWord.IsPrefix g.toWord) :
    ∑ y ∈ treePathVertices g,
      (if k = circleExponent y - circleExponent x then ‖circlePathEntry g x y‖ else 0) ≤
      2 * tParam ^ k.natAbs / (1 - tParam) := by
  classical
  rw [← Finset.sum_filter]
  let s := (treePathVertices g).filter (fun y => k = circleExponent y - circleExponent x)
  calc
    _ ≤ ∑ y ∈ s, tParam ^ (Nat.dist x.toWord.length y.toWord.length) := by
      apply Finset.sum_le_sum
      intro y hy
      exact circlePathEntry_decay g x y
        ((mem_treePathVertices g y).mp (Finset.mem_filter.mp hy).1)
    _ ≤ _ := circle_path_tail_sum g x s k.natAbs
      (fun y hy => (mem_treePathVertices g y).mp (Finset.mem_filter.mp hy).1)
      (fun y hy => by
        obtain ⟨hy, hk⟩ := Finset.mem_filter.mp hy
        rw [hk]
        exact circleExponent_path_distance g x y hx ((mem_treePathVertices g y).mp hy))

-- @node: circle_coefficient_column_sum
/-- For [free-group elements g and y](hyp:g,y) and [an integer coefficient index k](hyp:k),
if [y lies on the reduced-word path to g](hyp:hy), then [the sum of the absolute
path-matrix entries in column y whose column exponent minus row exponent equals k is
at most twice the deformation parameter raised to the absolute value of k, divided
by one minus the deformation parameter](goal). -/
lemma circle_coefficient_column_sum (g y : FreeGrp) (k : ℤ)
    (hy : y.toWord.IsPrefix g.toWord) :
    ∑ x ∈ treePathVertices g,
      (if k = circleExponent y - circleExponent x then ‖circlePathEntry g x y‖ else 0) ≤
      2 * tParam ^ k.natAbs / (1 - tParam) := by
  classical
  rw [← Finset.sum_filter]
  let s := (treePathVertices g).filter (fun x => k = circleExponent y - circleExponent x)
  calc
    _ ≤ ∑ x ∈ s, tParam ^ (Nat.dist y.toWord.length x.toWord.length) := by
      apply Finset.sum_le_sum
      intro x hx
      rw [Nat.dist_comm]
      exact circlePathEntry_decay g x y hy
    _ ≤ _ := circle_path_tail_sum g y s k.natAbs
      (fun x hx => (mem_treePathVertices g x).mp (Finset.mem_filter.mp hx).1)
      (fun x hx => by
        obtain ⟨hx, hk⟩ := Finset.mem_filter.mp hx
        rw [hk, Nat.dist_comm]
        exact circleExponent_path_distance g x y ((mem_treePathVertices g x).mp hx) hy)

-- @node: circle_finite_matrix_apply
/-- For [a finite set of free-group indices p](hyp:p), [complex matrix entries a](hyp:a),
[a tree-space vector v](hyp:v), and [a coordinate x](hyp:x), [the matrix formed from
the entries on p applied to v has x-coordinate equal to the sum over p of the
entries in row x times the corresponding coordinates of v when x belongs to p,
and zero otherwise](goal). -/
lemma circle_finite_matrix_apply (p : Finset FreeGrp) (a : FreeGrp → FreeGrp → ℂ)
    (v : TreeSpace) (x : FreeGrp) :
    (∑ i ∈ p, ∑ j ∈ p, a i j • matUnit i j) v x =
      if x ∈ p then ∑ j ∈ p, a x j * v j else 0 := by
  classical
  have hm (i j : FreeGrp) : matUnit i j v = v j • delta i := rfl
  simp only [_root_.sum_apply, _root_.smul_apply, hm, lp.coeFn_sum, Finset.sum_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, delta, lp.single_apply,
    Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq]
  by_cases hx : x ∈ p <;> simp [hx]

-- @node: circle_weighted_row_square
/-- For [a finite set of free-group indices p](hyp:p), [complex weights a](hyp:a), and
[a tree-space vector v](hyp:v), [the squared absolute value of the weighted coordinate
sum over p is at most the sum of the absolute weights times the sum of the squared
coordinate magnitudes weighted by those absolute weights](goal). -/
lemma circle_weighted_row_square (p : Finset FreeGrp) (a : FreeGrp → ℂ)
    (v : TreeSpace) :
    ‖∑ j ∈ p, a j * v j‖ ^ 2 ≤
      (∑ j ∈ p, ‖a j‖) * ∑ j ∈ p, ‖a j‖ * ‖v j‖ ^ 2 := by
  have hnorm : ‖∑ j ∈ p, a j * v j‖ ≤ ∑ j ∈ p, ‖a j‖ * ‖v j‖ := by
    simpa only [norm_mul] using norm_sum_le p (fun j => a j * v j)
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul p
    (r := fun j => ‖a j‖ * ‖v j‖) (f := fun j => ‖a j‖)
    (g := fun j => ‖a j‖ * ‖v j‖ ^ 2)
    (fun _ _ => norm_nonneg _) (fun _ _ => by positivity)
    (fun j hj => by ring_nf; exact le_rfl)
  exact (sq_le_sq₀ (norm_nonneg _)
    (Finset.sum_nonneg (fun _ _ => by positivity)) |>.mpr hnorm).trans hcs

-- @node: circle_finite_schur_bound
/-- For [a finite set of free-group indices p](hyp:p), [complex matrix entries a](hyp:a),
and [a real bound C](hyp:C), if [C is nonnegative](hyp:hC), [each absolute row sum
over p is at most C](hyp:hrow), and [each absolute column sum over p is at most C](hyp:hcol),
then [the operator norm of the matrix supported on p is at most C](goal). -/
lemma circle_finite_schur_bound (p : Finset FreeGrp) (a : FreeGrp → FreeGrp → ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hrow : ∀ i ∈ p, ∑ j ∈ p, ‖a i j‖ ≤ C)
    (hcol : ∀ j ∈ p, ∑ i ∈ p, ‖a i j‖ ≤ C) :
    ‖∑ i ∈ p, ∑ j ∈ p, a i j • matUnit i j‖ ≤ C := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro v
  apply lp.norm_le_of_forall_sum_le (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
    (mul_nonneg hC (norm_nonneg v))
  intro s
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  let A := ∑ i ∈ p, ∑ j ∈ p, a i j • matUnit i j
  have hcoord (i : FreeGrp) :
      ‖A v i‖ ^ 2 ≤ if i ∈ p then C * ∑ j ∈ p, ‖a i j‖ * ‖v j‖ ^ 2 else 0 := by
    rw [circle_finite_matrix_apply]
    by_cases hi : i ∈ p
    · rw [if_pos hi, if_pos hi]
      exact (circle_weighted_row_square p (a i) v).trans
        (mul_le_mul_of_nonneg_right (hrow i hi) (by positivity))
    · simp [hi]
  have hv : ∑ j ∈ p, ‖v j‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.sum_rpow_le_norm_rpow (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) v p
  calc
    ∑ i ∈ s, ‖A v i‖ ^ 2 ≤ ∑ i ∈ s, if i ∈ p then C * ∑ j ∈ p, ‖a i j‖ * ‖v j‖ ^ 2 else 0 :=
      Finset.sum_le_sum (fun i _ => hcoord i)
    _ ≤ ∑ i ∈ p, C * ∑ j ∈ p, ‖a i j‖ * ‖v j‖ ^ 2 := by
      rw [← Finset.sum_filter]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        exact (Finset.mem_filter.mp hi).2
      · intro i hi hni
        positivity
    _ = C * ∑ j ∈ p, (∑ i ∈ p, ‖a i j‖) * ‖v j‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ ≤ C * ∑ j ∈ p, C * ‖v j‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right (hcol j hj) (sq_nonneg _)
    _ ≤ (C * ‖v‖) ^ 2 := by
      rw [← Finset.mul_sum, ← mul_assoc, mul_pow, ← sq]
      exact mul_le_mul_of_nonneg_left hv (sq_nonneg C)

-- @node: circleLaurentCore_norm_le
/-- For [an integer coefficient index k](hyp:k) and [a free-group element g](hyp:g),
[the operator norm of the k-th Laurent core at g is at most the coefficient weight
at k](goal). -/
lemma circleLaurentCore_norm_le (k : ℤ) (g : FreeGrp) :
    ‖circleLaurentCore k g‖ ≤ cWeight k := by
  classical
  have ht := circle_deformation_range.1
  have ht1 := circle_deformation_range.2
  have hmatrix := circle_finite_schur_bound (treePathVertices g)
    (fun x y => if k = circleExponent y - circleExponent x then circlePathEntry g x y else 0)
    (2 * tParam ^ k.natAbs / (1 - tParam)) (by positivity)
    (fun x hx => by
      simpa only [apply_ite, norm_zero] using circle_coefficient_row_sum g x k
        ((mem_treePathVertices g x).mp hx))
    (fun y hy => by
      simpa only [apply_ite, norm_zero] using circle_coefficient_column_sum g y k
        ((mem_treePathVertices g y).mp hy))
  simp only [ite_smul, zero_smul] at hmatrix
  have hid : ‖(if k = 0 then (1 : TreeSpace →L[ℂ] TreeSpace) else 0)‖ ≤
      if k = 0 then (1 : ℝ) else 0 := by
    split_ifs
    · exact ContinuousLinearMap.norm_id_le
    · simp
  exact (norm_add_le _ _).trans ((add_le_add hid hmatrix).trans_eq (by rfl))

-- @node: circleLaurentCoefficients_norm_le
/-- For [an integer coefficient index k](hyp:k) and [a free-group element g](hyp:g),
[the operator norm of the k-th circle Laurent coefficient at g is at most the
coefficient weight at k](goal). -/
lemma circleLaurentCoefficients_norm_le (k : ℤ) (g : FreeGrp) :
    ‖circleLaurentCoefficients k g‖ ≤ cWeight k := by
  rw [circleLaurentCoefficients, CStarRing.norm_mul_coe_unitary]
  exact circleLaurentCore_norm_le k g

end Papers.OaiNearInclusionsVon
