module

public import Papers.OaiBoundDyadicTriangular.Basic

/-!
# Spectral sums for the cubic trace estimate

Pairing the two orientations of an off-diagonal entry gives equation (AE).
The weighted row estimate is the Cauchy--Schwarz step for a smallest index
occurring twice in the cubic expansion. Division is totalized, so zero
spectral values contribute zero without a separate summation domain.
-/

public section

open Matrix
open scoped BigOperators

namespace Papers.OaiBoundDyadicTriangular

-- @node: spectral_pair_sum
/-- [The sum of a real array over all ordered pairs in a finite ordered index set
equals its diagonal sum plus the sum, over strictly increasing pairs, of the two
oppositely oriented entries](goal). -/
lemma spectral_pair_sum {ι : Type*} [Fintype ι] [LinearOrder ι]
    (f : ι → ι → ℝ) :
    (∑ i, ∑ j, f i j) = (∑ i, f i i) +
      ∑ i, ∑ j, if i < j then f i j + f j i else 0 := by
  classical
  have hsplit (i j : ι) : f i j =
      (if j = i then f i i else 0) +
      (if i < j then f i j else 0) + (if j < i then f i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne', not_lt_of_gt h]
    · subst j; simp
    · simp [h, h.ne, not_lt_of_gt h]
  calc
    (∑ i, ∑ j, f i j) =
        (∑ i, f i i) + (∑ i, ∑ j, if i < j then f i j else 0) +
          (∑ i, ∑ j, if j < i then f i j else 0) := by
      conv_lhs => arg 2; ext i; arg 2; ext j; rw [hsplit i j]
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    _ = (∑ i, f i i) + ∑ i, ∑ j, if i < j then f i j + f j i else 0 := by
      rw [Finset.sum_comm (f := fun i j => if j < i then f i j else 0)]
      simp only [ite_add_zero, Finset.sum_add_distrib]
      ring

-- @node: spectral_diagonal_weight
/-- [For any real numbers q and d, q squared times q squared divided by twice q,
then multiplied by d squared, equals q cubed times d squared divided by two](goal).

Division by zero is assigned the value zero. -/
lemma spectral_diagonal_weight (q d : ℝ) :
    q ^ 2 * q ^ 2 / (q + q) * d ^ 2 = q ^ 3 * d ^ 2 / 2 := by
  by_cases hz : q = 0
  · simp [hz]
  · field_simp
    ring

-- @node: spectral_paired_weight_lower
/-- If [y is nonnegative](hyp:hy) and [y is no greater than x](hyp:hxy), then
[x times y squared times d squared is at most twice x squared times y squared
times d squared divided by the sum of x and y](goal). -/
lemma spectral_paired_weight_lower (x y d : ℝ)
    (hy : 0 ≤ y) (hxy : y ≤ x) :
    x * y ^ 2 * d ^ 2 ≤ 2 * (x ^ 2 * y ^ 2 / (x + y) * d ^ 2) := by
  have hx : 0 ≤ x := hy.trans hxy
  by_cases hz : x + y = 0
  · have hxz : x = 0 := by linarith
    simp [hxz]
  have hp : 0 < x + y := lt_of_le_of_ne (add_nonneg hx hy) (Ne.symm hz)
  have hc : x * y ^ 2 ≤ 2 * (x ^ 2 * y ^ 2 / (x + y)) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hp).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (mul_nonneg hx (sq_nonneg y))]
  exact (mul_le_mul_of_nonneg_right hc (sq_nonneg d)).trans_eq (by ring)

/-- If [the spectral weights q are nonnegative](hyp:hq), [decrease with the
index](hyp:hOrder), and [D is symmetric](hyp:hD), then [half the sum of q cubed
times the squared diagonal entries, plus the sum over increasing pairs of the
first weight times the second weight squared times the squared matrix entry,
is at most the sum over all pairs of the squared weights times the squared
matrix entry divided by the sum of the weights](goal).

This is equation (AE), including zero eigenvalues. -/
-- @node: spectral_Q_ge_diagonal_tail
lemma spectral_Q_ge_diagonal_tail {ι : Type*} [Fintype ι] [LinearOrder ι]
    (q : ι → ℝ) (D : Matrix ι ι ℝ) (hq : ∀ i, 0 ≤ q i)
    (hOrder : Antitone q) (hD : D.IsSymm) :
    (∑ i, q i ^ 3 * D i i ^ 2) / 2 +
      (∑ i, ∑ j, if i < j then q i * q j ^ 2 * D i j ^ 2 else 0) ≤
      ∑ i, ∑ j, q i ^ 2 * q j ^ 2 / (q i + q j) * D i j ^ 2 := by
  classical
  rw [spectral_pair_sum (fun i j => q i ^ 2 * q j ^ 2 / (q i + q j) * D i j ^ 2)]
  have hDiag : (∑ i, q i ^ 2 * q i ^ 2 / (q i + q i) * D i i ^ 2) =
      (∑ i, q i ^ 3 * D i i ^ 2) / 2 := by
    simp_rw [spectral_diagonal_weight]
    rw [Finset.sum_div]
  rw [hDiag]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  split_ifs with hij
  · have hs : D j i = D i j := congrFun (congrFun hD.eq i) j
    rw [hs, add_comm (q j) (q i), mul_comm (q j ^ 2) (q i ^ 2), ← two_mul]
    exact spectral_paired_weight_lower _ _ _ (hq j) (hOrder hij.le)
  · exact le_rfl

/-- If [the sum of d squared over the finite set s is at most one](hyp:hRow),
then [the absolute value of the sum of m times d squared over s is at most the
square root of the sum of m squared times d squared over s](goal). -/
-- @node: weighted_row_sum_le_sqrt
lemma weighted_row_sum_le_sqrt {ι : Type*} (s : Finset ι) (m d : ι → ℝ)
    (hRow : ∑ j ∈ s, d j ^ 2 ≤ 1) :
    |∑ j ∈ s, m j * d j ^ 2| ≤ Real.sqrt (∑ j ∈ s, m j ^ 2 * d j ^ 2) := by
  have hNonneg : 0 ≤ ∑ j ∈ s, m j ^ 2 * d j ^ 2 :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq s (fun j => m j * d j) d
  have hRewrite : (∑ j ∈ s, (m j * d j) * d j) = ∑ j ∈ s, m j * d j ^ 2 := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hRewrite] at hCS
  simp only [mul_pow] at hCS
  have hBound := hCS.trans (mul_le_of_le_one_right hNonneg hRow)
  exact (Real.le_sqrt (abs_nonneg _) hNonneg).mpr (by simpa only [sq_abs] using hBound)

/-- If [q is nonnegative](hyp:hq) and [the sum of d squared over s is at most
one](hyp:hRow), then [the absolute value of three times q squared times c times
the sum of m times d squared is at most three times the square root of the
product of q cubed times c squared and q times the sum of m squared times d
squared, with both sums taken over s](goal). -/
-- @node: cubic_twice_le_sqrt
lemma cubic_twice_le_sqrt {ι : Type*} (s : Finset ι) (m d : ι → ℝ)
    (q c : ℝ) (hq : 0 ≤ q) (hRow : ∑ j ∈ s, d j ^ 2 ≤ 1) :
    |3 * q ^ 2 * c * (∑ j ∈ s, m j * d j ^ 2)| ≤
      3 * Real.sqrt ((q ^ 3 * c ^ 2) *
        (q * ∑ j ∈ s, m j ^ 2 * d j ^ 2)) := by
  let S := ∑ j ∈ s, m j ^ 2 * d j ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg
    (fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hRoot : Real.sqrt ((q ^ 3 * c ^ 2) * (q * S)) =
      q ^ 2 * |c| * Real.sqrt S := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
    rw [mul_pow, mul_pow, sq_abs, Real.sq_sqrt hS]
    ring
  rw [hRoot]
  calc
    _ = 3 * q ^ 2 * |c| * |∑ j ∈ s, m j * d j ^ 2| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3),
        abs_of_nonneg (sq_nonneg q)]
    _ ≤ 3 * q ^ 2 * |c| * Real.sqrt S :=
      mul_le_mul_of_nonneg_left (weighted_row_sum_le_sqrt s m d hRow) (by positivity)
    _ = _ := by ring

/-- If [the absolute value of d is at most one](hyp:hd), then [the absolute
value of m cubed times d cubed is at most the cube of the absolute value of m
times d squared](goal). -/
-- @node: cubic_diagonal_le
lemma cubic_diagonal_le (m d : ℝ) (hd : |d| ≤ 1) :
    |m ^ 3 * d ^ 3| ≤ |m| ^ 3 * d ^ 2 := by
  rw [abs_mul, abs_pow, abs_pow]
  have he : |d| ^ 3 = d ^ 2 * |d| := by rw [pow_succ, sq_abs]
  rw [he]
  exact mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_right (sq_nonneg d) hd) (by positivity)

/-- If [every value of A is nonnegative](hyp:hA) and [every value of E is
nonnegative](hyp:hE), then [the sum over s of the square roots of their
pointwise products is at most the square root of the product of their separate
sums over s](goal). -/
-- @node: cubic_sqrt_sum_le
lemma cubic_sqrt_sum_le {ι : Type*} (s : Finset ι) (A E : ι → ℝ)
    (hA : ∀ i, 0 ≤ A i) (hE : ∀ i, 0 ≤ E i) :
    (∑ i ∈ s, Real.sqrt (A i * E i)) ≤
      Real.sqrt ((∑ i ∈ s, A i) * (∑ i ∈ s, E i)) := by
  simp_rw [Real.sqrt_mul (hA _)]
  rw [Real.sqrt_mul (Finset.sum_nonneg (fun i _ => hA i))]
  exact Real.sum_sqrt_mul_sqrt_le s hA hE

/-- If [A is nonnegative](hyp:hA) and [E is nonnegative](hyp:hE), then [A plus
three times E plus three times the square root of their product is at most
five times the sum of half of A and E](goal). -/
-- @node: cubic_AE_le_five
lemma cubic_AE_le_five (A E : ℝ) (hA : 0 ≤ A) (hE : 0 ≤ E) :
    A + 3 * E + 3 * Real.sqrt (A * E) ≤ 5 * (A / 2 + E) := by
  have hRoot : Real.sqrt (A * E) ≤ (A + E) / 2 := by
    have hs := Real.sq_sqrt (mul_nonneg hA hE)
    have hn := Real.sqrt_nonneg (A * E)
    nlinarith [sq_nonneg (A - E)]
  calc
    _ ≤ (5 / 2 : ℝ) * A + (9 / 2 : ℝ) * E := by linarith
    _ ≤ _ := by linarith

/-- If [the identity minus D is positive semidefinite](hyp:hMinus) and [the
identity plus D is positive semidefinite](hyp:hPlus), then [the absolute value
of the quadratic form of D at any vector x is at most the sum of the squared
coordinates of x](goal). -/
-- @node: contraction_abs_quadratic_le
lemma contraction_abs_quadratic_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℝ) (hMinus : (1 - D).PosSemidef)
    (hPlus : (1 + D).PosSemidef) (x : ι → ℝ) :
    |x ⬝ᵥ (D *ᵥ x)| ≤ ∑ i, x i ^ 2 := by
  have hm := hMinus.dotProduct_mulVec_nonneg x
  have hp := hPlus.dotProduct_mulVec_nonneg x
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_add] at hm hp
  have he : x ⬝ᵥ x = ∑ i, x i ^ 2 := by
    simp only [dotProduct, pow_two]
  rw [he] at hm hp
  exact abs_le.mpr ⟨by linarith, by linarith⟩

-- @node: contraction_row_sq_le_one
/-- If [D is symmetric](hyp:hSymm), [the identity minus D is positive
semidefinite](hyp:hMinus), and [the identity plus D is positive
semidefinite](hyp:hPlus), then [the sum of the squared entries in any row i of
D is at most one](goal). -/
lemma contraction_row_sq_le_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℝ) (hSymm : D.IsSymm)
    (hMinus : (1 - D).PosSemidef) (hPlus : (1 + D).PosSemidef) (i : ι) :
    ∑ j, D i j ^ 2 ≤ 1 := by
  open scoped MatrixOrder Matrix.Norms.L2Operator in
    have hProd : ((1 - D) * (1 + D)).PosSemidef := by
      apply LE.le.posSemidef
      apply Commute.mul_nonneg hMinus.nonneg hPlus.nonneg
      unfold Commute SemiconjBy
      noncomm_ring
  have he : (1 - D) * (1 + D) = 1 - D * D := by noncomm_ring
  rw [he] at hProd
  have hd := hProd.diag_nonneg (i := i)
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.mul_apply] at hd
  have hs (j : ι) : D j i = D i j := congrFun (congrFun hSymm.eq i) j
  simp_rw [hs, ← pow_two] at hd
  linarith

-- @node: contraction_diagonal_abs_le_one
/-- If [the identity minus D is positive semidefinite](hyp:hMinus) and [the
identity plus D is positive semidefinite](hyp:hPlus), then [every diagonal
entry of D has absolute value at most one](goal). -/
lemma contraction_diagonal_abs_le_one {ι : Type*} [Finite ι] [DecidableEq ι]
    (D : Matrix ι ι ℝ) (hMinus : (1 - D).PosSemidef)
    (hPlus : (1 + D).PosSemidef) (i : ι) : |D i i| ≤ 1 := by
  let := Fintype.ofFinite ι
  have hm := hMinus.diag_nonneg (i := i)
  have hp := hPlus.diag_nonneg (i := i)
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply_eq] at hm hp
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- If [the identity minus D is positive semidefinite](hyp:hMinus) and [the
identity plus D is positive semidefinite](hyp:hPlus), then [the absolute value
of the quadratic form obtained by restricting both indices to s is at most
the sum over s of the squared coordinates of x](goal). -/
-- @node: contraction_compression_abs_le
lemma contraction_compression_abs_le {ι : Type*} [Finite ι] [DecidableEq ι]
    (D : Matrix ι ι ℝ) (hMinus : (1 - D).PosSemidef)
    (hPlus : (1 + D).PosSemidef) (s : Finset ι) (x : ι → ℝ) :
    |∑ j ∈ s, ∑ k ∈ s, x j * D j k * x k| ≤ ∑ j ∈ s, x j ^ 2 := by
  classical
  let := Fintype.ofFinite ι
  let y : ι → ℝ := fun j => if j ∈ s then x j else 0
  have h := contraction_abs_quadratic_le D hMinus hPlus y
  have he : y ⬝ᵥ (D *ᵥ y) = ∑ j ∈ s, ∑ k ∈ s, x j * D j k * x k := by
    simp [y, dotProduct, Matrix.mulVec, Finset.mul_sum,
      mul_assoc, mul_ite, ite_mul]
  rw [he] at h
  simpa [y, apply_ite (fun z : ℝ => z ^ 2)] using h

/-- If [D is symmetric](hyp:hSymm), [the identity minus D is positive
semidefinite](hyp:hMinus), and [the identity plus D is positive
semidefinite](hyp:hPlus), then [the absolute value of three times m at i times
the sum over j and k in s of the product of their two weights and the entries
of D along the cycle i to j to k to i is at most three times the absolute
weight at i times the sum over j in s of its squared weight times the squared
entry from i to j](goal). -/
-- @node: cubic_once_le_tail
lemma cubic_once_le_tail {ι : Type*} [Finite ι] [DecidableEq ι]
    (D : Matrix ι ι ℝ) (hSymm : D.IsSymm)
    (hMinus : (1 - D).PosSemidef) (hPlus : (1 + D).PosSemidef)
    (m : ι → ℝ) (i : ι) (s : Finset ι) :
    |3 * m i * (∑ j ∈ s, ∑ k ∈ s,
      m j * m k * D i j * D j k * D k i)| ≤
      3 * (|m i| * ∑ j ∈ s, m j ^ 2 * D i j ^ 2) := by
  have h := contraction_compression_abs_le D hMinus hPlus s (fun j => m j * D i j)
  have he : (∑ j ∈ s, ∑ k ∈ s, (m j * D i j) * D j k * (m k * D i k)) =
      ∑ j ∈ s, ∑ k ∈ s, m j * m k * D i j * D j k * D k i := by
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    have hs : D k i = D i k := congrFun (congrFun hSymm.eq i) k
    rw [hs]
    ring
  rw [he] at h
  simp only [mul_pow] at h
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
  exact (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (by ring)

/-- If [D is symmetric](hyp:hSymm), [the identity minus D is positive
semidefinite](hyp:hMinus), and [the identity plus D is positive
semidefinite](hyp:hPlus), then [the absolute value of three times the squared
weight at i times the diagonal entry at i times the sum over j in s of its
weight times the squared entry from i to j is at most three times the square
root of the product of the cubed absolute weight at i times its squared
diagonal entry and the absolute weight at i times the sum over j in s of its
squared absolute weight times the squared entry from i to j](goal). -/
-- @node: cubic_twice_compression_le
lemma cubic_twice_compression_le {ι : Type*} [Finite ι] [DecidableEq ι]
    (D : Matrix ι ι ℝ) (hSymm : D.IsSymm)
    (hMinus : (1 - D).PosSemidef) (hPlus : (1 + D).PosSemidef)
    (m : ι → ℝ) (i : ι) (s : Finset ι) :
    |3 * m i ^ 2 * D i i * (∑ j ∈ s, m j * D i j ^ 2)| ≤
      3 * Real.sqrt ((|m i| ^ 3 * D i i ^ 2) *
        (|m i| * ∑ j ∈ s, |m j| ^ 2 * D i j ^ 2)) := by
  let := Fintype.ofFinite ι
  have hRow : ∑ j ∈ s, D i j ^ 2 ≤ 1 := by
    apply le_trans _ (contraction_row_sq_le_one D hSymm hMinus hPlus i)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (fun j _ _ => sq_nonneg (D i j))
  have h := cubic_twice_le_sqrt s m (fun j => D i j) |m i| (D i i)
    (abs_nonneg _) hRow
  simpa only [sq_abs] using h

/-- If [f is unchanged by cyclic rotation of its three indices](hyp:hCycle),
then [its full triple sum equals its all-equal diagonal sum, plus three times
the sum with the least index occurring twice, plus three times the sum with
the first index strictly smaller than each of the other two](goal).

The last sum allows its other two indices to be equal. -/
-- @node: cyclic_triple_sum_partition
lemma cyclic_triple_sum_partition {ι : Type*} [Fintype ι] [LinearOrder ι]
    (f : ι → ι → ι → ℝ) (hCycle : ∀ i j k, f i j k = f j k i) :
    (∑ i, ∑ j, ∑ k, f i j k) =
      (∑ i, f i i i) +
      3 * (∑ i, ∑ j, if i < j then f i i j else 0) +
      3 * (∑ i, ∑ j, ∑ k, if i < j ∧ i < k then f i j k else 0) := by
  classical
  have hSplit (i j k : ι) : f i j k =
      (if i = j ∧ j = k then f i i i else 0) +
      (if i = j ∧ i < k then f i i k else 0) +
      (if j = k ∧ j < i then f j j i else 0) +
      (if k = i ∧ k < j then f k k j else 0) +
      (if i < j ∧ i < k then f i j k else 0) +
      (if j < k ∧ j < i then f j k i else 0) +
      (if k < i ∧ k < j then f k i j else 0) := by
    rcases lt_trichotomy i j with hij | hij | hji
    · rcases lt_trichotomy i k with hik | hik | hki
      · simp [hij, hij.ne, not_lt_of_gt hij,
          hik, hik.ne', not_lt_of_gt hik]
      · subst k
        simpa [hij, hij.ne, hij.ne', not_lt_of_gt hij] using (hCycle i i j).symm
      · have hkj := hki.trans hij
        simpa [hij, hij.ne, hij.ne', not_lt_of_gt hij,
          hki, hki.ne, hki.ne', not_lt_of_gt hki,
          hkj, hkj.ne, hkj.ne', not_lt_of_gt hkj] using (hCycle k i j).symm
    · subst j
      rcases lt_trichotomy i k with hik | hik | hki
      · simp [hik, hik.ne, hik.ne', not_lt_of_gt hik]
      · subst k; simp
      · simpa [hki, hki.ne, hki.ne', not_lt_of_gt hki] using (hCycle k i i).symm
    · rcases lt_trichotomy j k with hjk | hjk | hkj
      · simpa [hji, hji.ne, hji.ne', not_lt_of_gt hji,
          hjk, hjk.ne, hjk.ne', not_lt_of_gt hjk] using hCycle i j k
      · subst k
        simpa [hji, hji.ne, hji.ne', not_lt_of_gt hji] using hCycle i j j
      · have hki := hkj.trans hji
        simpa [hji, hji.ne, hji.ne', not_lt_of_gt hji,
          hkj, hkj.ne, hkj.ne', not_lt_of_gt hkj,
          hki, hki.ne, hki.ne', not_lt_of_gt hki] using (hCycle k i j).symm
  have hRotate (g : ι → ι → ι → ℝ) :
      (∑ i, ∑ j, ∑ k, g j k i) = ∑ i, ∑ j, ∑ k, g i j k := by
    simpa only using (Finset.sum_comm_cycle
      (s := Finset.univ) (t := Finset.univ) (u := Finset.univ)
      (f := fun i j k => g i j k)).symm
  have hRotate₂ (g : ι → ι → ι → ℝ) :
      (∑ i, ∑ j, ∑ k, g k i j) = ∑ i, ∑ j, ∑ k, g i j k := by
    rw [hRotate (fun i j k => g j k i), hRotate g]
  calc
    _ = (∑ i, ∑ j, ∑ k, (
      (if i = j ∧ j = k then f i i i else 0) +
      (if i = j ∧ i < k then f i i k else 0) +
      (if j = k ∧ j < i then f j j i else 0) +
      (if k = i ∧ k < j then f k k j else 0) +
      (if i < j ∧ i < k then f i j k else 0) +
      (if j < k ∧ j < i then f j k i else 0) +
      (if k < i ∧ k < j then f k i j else 0))) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        exact hSplit i j k
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      rw [hRotate (fun i j k => if i = j ∧ i < k then f i i k else 0),
        hRotate₂ (fun i j k => if i = j ∧ i < k then f i i k else 0),
        hRotate (fun i j k => if i < j ∧ i < k then f i j k else 0),
        hRotate₂ (fun i j k => if i < j ∧ i < k then f i j k else 0)]
      simp only [ite_and]
      simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.mem_univ,
        if_true, Finset.sum_const_zero]
      ring

/-- If [D is symmetric](hyp:hD), then [the full sum of the three weights times
the three matrix entries around each index cycle equals the sum over i of
three contributions: the cubed weight times the cubed diagonal entry; three
times the squared weight and diagonal entry times the sum over j greater than
i of its weight times the squared entry from i to j; and three times the
weight at i times the sum over j and k greater than i of their weights times
the entries along the cycle i to j to k to i](goal). -/
-- @node: spectral_cubic_partition
lemma spectral_cubic_partition {ι : Type*} [Fintype ι] [LinearOrder ι]
    (m : ι → ℝ) (D : Matrix ι ι ℝ) (hD : D.IsSymm) :
    (∑ i, ∑ j, ∑ k, m i * m j * m k * D i j * D j k * D k i) =
      ∑ i, (m i ^ 3 * D i i ^ 3 +
        3 * m i ^ 2 * D i i *
          (∑ j ∈ Finset.univ.filter (i < ·), m j * D i j ^ 2) +
        3 * m i * (∑ j ∈ Finset.univ.filter (i < ·),
          ∑ k ∈ Finset.univ.filter (i < ·),
            m j * m k * D i j * D j k * D k i)) := by
  classical
  let f := fun i j k => m i * m j * m k * D i j * D j k * D k i
  have hCycle : ∀ i j k, f i j k = f j k i := by intros; dsimp [f]; ring
  have hDiag : (∑ i, f i i i) = ∑ i, m i ^ 3 * D i i ^ 3 := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp [f]; ring
  have hTwice : (∑ i, ∑ j, if i < j then f i i j else 0) =
      ∑ i, m i ^ 2 * D i i *
        (∑ j ∈ Finset.univ.filter (i < ·), m j * D i j ^ 2) := by
    simp only [Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs
    · have hs : D j i = D i j := congrFun (congrFun hD.eq i) j
      dsimp [f]; rw [hs]; ring
    · rfl
  have hOnce : (∑ i, ∑ j, ∑ k, if i < j ∧ i < k then f i j k else 0) =
      ∑ i, m i * (∑ j ∈ Finset.univ.filter (i < ·),
        ∑ k ∈ Finset.univ.filter (i < ·),
          m j * m k * D i j * D j k * D k i) := by
    simp only [Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero,
      Finset.sum_ite_irrel, Finset.sum_const_zero, ite_and]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i < j
    · simp only [hij, if_true]
      apply Finset.sum_congr rfl
      intro k _
      split_ifs
      · dsimp [f]; ring
      · rfl
    · simp [hij]
  rw [cyclic_triple_sum_partition f hCycle, hDiag, hTwice, hOnce]
  simp only [Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

/-- If [D is symmetric](hyp:hD), [the identity minus D is positive
semidefinite](hyp:hMinus), and [the identity plus D is positive
semidefinite](hyp:hPlus), then [the absolute value of the weighted cubic cycle
sum is at most five times the sum of half the diagonal sum of cubed absolute
weights times squared diagonal entries and the sum over increasing pairs of
the first absolute weight times the second squared absolute weight times the
squared matrix entry](goal). -/
-- @node: spectral_cubic_le_AE
lemma spectral_cubic_le_AE {ι : Type*} [Fintype ι] [LinearOrder ι]
    (m : ι → ℝ) (D : Matrix ι ι ℝ) (hD : D.IsSymm)
    (hMinus : (1 - D).PosSemidef) (hPlus : (1 + D).PosSemidef) :
    |∑ i, ∑ j, ∑ k, m i * m j * m k * D i j * D j k * D k i| ≤
      5 * ((∑ i, |m i| ^ 3 * D i i ^ 2) / 2 +
        ∑ i, ∑ j, if i < j then |m i| * |m j| ^ 2 * D i j ^ 2 else 0) := by
  classical
  let A := fun i => |m i| ^ 3 * D i i ^ 2
  let E := fun i => |m i| *
    ∑ j ∈ Finset.univ.filter (i < ·), |m j| ^ 2 * D i j ^ 2
  have hA : ∀ i, 0 ≤ A i := by intro i; dsimp [A]; positivity
  have hE : ∀ i, 0 ≤ E i := by
    intro i
    exact mul_nonneg (abs_nonneg _) (Finset.sum_nonneg (fun j _ => by positivity))
  have hEach (i : ι) :
      |m i ^ 3 * D i i ^ 3 +
        3 * m i ^ 2 * D i i *
          (∑ j ∈ Finset.univ.filter (i < ·), m j * D i j ^ 2) +
        3 * m i * (∑ j ∈ Finset.univ.filter (i < ·),
          ∑ k ∈ Finset.univ.filter (i < ·),
            m j * m k * D i j * D j k * D k i)| ≤
      A i + 3 * Real.sqrt (A i * E i) + 3 * E i := by
    apply (abs_add_le _ _).trans
    apply add_le_add
    · apply (abs_add_le _ _).trans
      exact add_le_add
        (cubic_diagonal_le (m i) (D i i)
          (contraction_diagonal_abs_le_one D hMinus hPlus i))
        (cubic_twice_compression_le D hD hMinus hPlus m i _)
    · simpa only [E, sq_abs] using
        cubic_once_le_tail D hD hMinus hPlus m i (Finset.univ.filter (i < ·))
  have hS := cubic_sqrt_sum_le Finset.univ A E hA hE
  have hAN : 0 ≤ ∑ i, A i := Finset.sum_nonneg (fun i _ => hA i)
  have hEN : 0 ≤ ∑ i, E i := Finset.sum_nonneg (fun i _ => hE i)
  have hTail : (∑ i, E i) =
      ∑ i, ∑ j, if i < j then |m i| * |m j| ^ 2 * D i j ^ 2 else 0 := by
    simp only [E, Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero, mul_assoc]
  rw [spectral_cubic_partition m D hD]
  calc
    _ ≤ ∑ i, |m i ^ 3 * D i i ^ 3 +
        3 * m i ^ 2 * D i i *
          (∑ j ∈ Finset.univ.filter (i < ·), m j * D i j ^ 2) +
        3 * m i * (∑ j ∈ Finset.univ.filter (i < ·),
          ∑ k ∈ Finset.univ.filter (i < ·),
            m j * m k * D i j * D j k * D k i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (A i + 3 * Real.sqrt (A i * E i) + 3 * E i) :=
      Finset.sum_le_sum (fun i _ => hEach i)
    _ ≤ (∑ i, A i) + 3 * (∑ i, E i) +
        3 * Real.sqrt ((∑ i, A i) * (∑ i, E i)) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      linarith
    _ ≤ 5 * ((∑ i, A i) / 2 + ∑ i, E i) := cubic_AE_le_five _ _ hAN hEN
    _ = _ := by rw [hTail]

/-- If [D is symmetric](hyp:hD), [the identity minus D is positive
semidefinite](hyp:hMinus), [the identity plus D is positive
semidefinite](hyp:hPlus), and [the absolute weights decrease with the
index](hyp:hOrder), then [the absolute value of the weighted cubic cycle sum
is at most five times the sum over all pairs of the product of their squared
absolute weights and squared matrix entry divided by the sum of their
absolute weights](goal). -/
-- @node: spectral_cubic_le_five_Q
lemma spectral_cubic_le_five_Q {ι : Type*} [Fintype ι] [LinearOrder ι]
    (m : ι → ℝ) (D : Matrix ι ι ℝ) (hD : D.IsSymm)
    (hMinus : (1 - D).PosSemidef) (hPlus : (1 + D).PosSemidef)
    (hOrder : Antitone (fun i => |m i|)) :
    |∑ i, ∑ j, ∑ k, m i * m j * m k * D i j * D j k * D k i| ≤
      5 * ∑ i, ∑ j, |m i| ^ 2 * |m j| ^ 2 / (|m i| + |m j|) * D i j ^ 2 := by
  apply (spectral_cubic_le_AE m D hD hMinus hPlus).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact spectral_Q_ge_diagonal_tail (fun i => |m i|) D (fun i => abs_nonneg _) hOrder hD

end Papers.OaiBoundDyadicTriangular
