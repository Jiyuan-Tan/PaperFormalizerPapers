module

public import Papers.OaiBoundDyadicTriangular.Helpers.AtomIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # The atom-box integral and its normalized matrix trace -/

@[expose] public section

open MeasureTheory Matrix
open scoped BigOperators

namespace Papers.OaiBoundDyadicTriangular

-- @node: atom_count_scale
/-- If [the atom scale is no larger than the parent scale](hyp:hk),
[the atom length times the number of atoms equals the parent interval length](goal). -/
lemma atom_count_scale (k m : ℤ) (hk : m ≤ k) :
    (2 : ℝ) ^ m * (2 ^ (k - m).toNat : ℕ) = (2 : ℝ) ^ k := by
  rw [Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast,
    Int.toNat_of_nonneg (sub_nonneg.mpr hk), ← zpow_add₀ (by norm_num)]
  congr 1
  ring

-- @node: dyadic_subatom_subset
/-- If [the atom scale is no larger than the parent scale](hyp:hk),
[each indexed dyadic subatom lies inside its parent dyadic interval](goal). -/
lemma dyadic_subatom_subset (k m : ℤ) (a : ℕ) (i : Atom k m) (hk : m ≤ k) :
    dyadicInterval m (2 ^ (k - m).toNat * a + i.val) ⊆ dyadicInterval k a := by
  intro x hx
  have hp : 0 < (2 : ℝ) ^ m := by positivity
  have hi : (i.val : ℝ) + 1 ≤ (2 ^ (k - m).toNat : ℕ) := by exact_mod_cast i.isLt
  have hc := atom_count_scale k m hk
  simp only [dyadicInterval, Set.mem_Ico, Nat.cast_add, Nat.cast_mul] at hx ⊢
  constructor
  · nlinarith [show (0 : ℝ) ≤ i.val by positivity]
  · nlinarith [mul_le_mul_of_nonneg_left hi hp.le]

-- @node: dyadicInterval_eq_iUnion_atoms
/-- If [the atom scale is no larger than the parent scale](hyp:hk),
[a parent dyadic interval equals the union of all its indexed atom-scale subintervals](goal). -/
lemma dyadicInterval_eq_iUnion_atoms (k m : ℤ) (a : ℕ) (hk : m ≤ k) :
    dyadicInterval k a = ⋃ i : Atom k m,
      dyadicInterval m (2 ^ (k - m).toNat * a + i.val) := by
  ext x
  constructor
  · intro hx
    have hp : 0 < (2 : ℝ) ^ m := by positivity
    have hx0 : 0 ≤ x := (by positivity : 0 ≤ (2 : ℝ) ^ k * a).trans hx.1
    let q := ⌊x / (2 : ℝ) ^ m⌋₊
    have hq : (q : ℝ) ≤ x / (2 : ℝ) ^ m := Nat.floor_le (div_nonneg hx0 hp.le)
    have hq' : x / (2 : ℝ) ^ m < (q : ℝ) + 1 := Nat.lt_floor_add_one _
    have hc := atom_count_scale k m hk
    have hlo : 2 ^ (k - m).toNat * a ≤ q := by
      apply Nat.le_floor
      apply (le_div_iff₀ hp).mpr
      push_cast
      calc
        _ = ((2 : ℝ) ^ m * (2 ^ (k - m).toNat : ℕ)) * a := by push_cast; ring
        _ = (2 : ℝ) ^ k * a := by rw [hc]
        _ ≤ x := hx.1
    have hhi : q < 2 ^ (k - m).toNat * (a + 1) := by
      have h : (q : ℝ) < (2 ^ (k - m).toNat * (a + 1) : ℕ) := by
        have hmul := (le_div_iff₀ hp).mp hq
        push_cast
        have hu : x < (2 : ℝ) ^ m * ((2 ^ (k - m).toNat : ℕ) * (a + 1)) := by
          rw [← mul_assoc, hc]
          exact hx.2
        apply (mul_lt_mul_iff_right₀ hp).mp
        calc
          _ = (q : ℝ) * (2 : ℝ) ^ m := by ring
          _ ≤ x := hmul
          _ < _ := hu
          _ = _ := by push_cast; ring
      exact_mod_cast h
    let i : Atom k m := ⟨q - 2 ^ (k - m).toNat * a, by
      have he : 2 ^ (k - m).toNat * (a + 1) =
          2 ^ (k - m).toNat * a + 2 ^ (k - m).toNat := by ring
      omega⟩
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    have he : 2 ^ (k - m).toNat * a + i.val = q := by dsimp [i]; omega
    rw [he]
    constructor
    · simpa [mul_comm] using (le_div_iff₀ hp).mp hq
    · simpa [mul_comm] using (div_lt_iff₀ hp).mp hq'
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact dyadic_subatom_subset k m a i hk hi

-- @node: haarSign_eq_on_subatom
/-- If [the parent scale is at least one larger than the atom scale](hyp:hk),
[one point lies in a specified subatom](hyp:hx), and [a second point lies in the
same subatom](hyp:hy), then [the parent interval's Haar sign has the same value
at both points](goal). -/
lemma haarSign_eq_on_subatom (k m : ℤ) (a : ℕ) (i : Atom k m)
    (hk : m + 1 ≤ k) (x y : ℝ)
    (hx : x ∈ dyadicInterval m (2 ^ (k - m).toNat * a + i.val))
    (hy : y ∈ dyadicInterval m (2 ^ (k - m).toNat * a + i.val)) :
    haarSign k a x = haarSign k a y := by
  let M := 2 ^ (k - 1 - m).toNat
  have hM : 0 < M := by dsimp [M]; positivity
  have hN : 2 ^ (k - m).toNat = 2 * M := by
    have he : (k - m).toNat = (k - 1 - m).toNat + 1 := by omega
    rw [he, pow_succ]
    dsimp [M]
    omega
  let j : Atom (k - 1) m := ⟨i.val % M, Nat.mod_lt _ hM⟩
  have hid : 2 ^ (k - m).toNat * a + i.val =
      2 ^ (k - 1 - m).toNat * (2 * a + i.val / M) + j.val := by
    change _ = M * (2 * a + i.val / M) + i.val % M
    simp only [hN]
    nlinarith [Nat.mod_add_div i.val M]
  have hx' := dyadic_subatom_subset (k - 1) m (2 * a + i.val / M) j (by omega)
    (hid ▸ hx)
  have hy' := dyadic_subatom_subset (k - 1) m (2 * a + i.val / M) j (by omega)
    (hid ▸ hy)
  have hd : i.val / M < 2 := by
    apply (Nat.div_lt_iff_lt_mul hM).mpr
    simpa [hN, Nat.mul_comm] using i.isLt
  have h01 : Disjoint (dyadicInterval (k - 1) (2 * a))
      (dyadicInterval (k - 1) (2 * a + 1)) :=
    dyadicInterval_pairwiseDisjoint (k - 1) (by omega)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ hd) with h | h
  · simp only [h, add_zero] at hx' hy'
    have hnx := Set.disjoint_left.mp h01 hx'
    have hny := Set.disjoint_left.mp h01 hy'
    simp [haarSign, hx', hy', hnx, hny]
  · simp only [h] at hx' hy'
    have hnx := Set.disjoint_right.mp h01 hx'
    have hny := Set.disjoint_right.mp h01 hy'
    simp [haarSign, hx', hy', hnx, hny]


-- @node: atomBox
/-- For [a parent scale and an atom scale](hyp:k,m), [three parent interval indices](hyp:n),
and [three atom indices](hyp:i), the [atom box](goal) is the Cartesian product of
the three corresponding half-open atom-scale subintervals. -/
noncomputable def atomBox (k m : ℤ) (n : Fin 3 → ℕ)
    (i : Atom k m × (Atom k m × Atom k m)) : Set (ℝ × (ℝ × ℝ)) :=
  dyadicInterval m (atomIndex k m n 0 i.1) ×ˢ
    (dyadicInterval m (atomIndex k m n 1 i.2.1) ×ˢ
      dyadicInterval m (atomIndex k m n 2 i.2.2))

-- @node: atomPoint
/-- For [a parent scale and an atom scale](hyp:k,m), [three parent interval indices](hyp:n),
and [three atom indices](hyp:i), the [representative atom point](goal) is the point
whose three coordinates are the left endpoints of the corresponding subintervals. -/
noncomputable def atomPoint (k m : ℤ) (n : Fin 3 → ℕ)
    (i : Atom k m × (Atom k m × Atom k m)) : ℝ × (ℝ × ℝ) :=
  ((2 : ℝ) ^ m * atomIndex k m n 0 i.1,
    ((2 : ℝ) ^ m * atomIndex k m n 1 i.2.1,
      (2 : ℝ) ^ m * atomIndex k m n 2 i.2.2))

-- @node: triangularIntegrand
/-- For [a parent scale](hyp:k), [three interval indices](hyp:n),
[three input functions of two real coordinates](hyp:F), and [a point with three
real coordinates](hyp:x), the [triangular integrand](goal) is the product of the
inputs evaluated on the three cyclic coordinate pairs and the three corresponding
one-coordinate Haar signs. -/
noncomputable def triangularIntegrand (k : ℤ) (n : Fin 3 → ℕ)
    (F : Fin 3 → ℝ × ℝ → ℝ) (x : ℝ × (ℝ × ℝ)) : ℝ :=
  F 0 (x.1, x.2.1) * F 1 (x.2.1, x.2.2) * F 2 (x.2.2, x.1) *
    haarSign k (n 0) x.1 * haarSign k (n 1) x.2.1 * haarSign k (n 2) x.2.2

-- @node: atomPoint_mem_atomBox
/-- [The representative point of every atom box belongs to that box](goal). -/
lemma atomPoint_mem_atomBox (k m : ℤ) (n : Fin 3 → ℕ)
    (i : Atom k m × (Atom k m × Atom k m)) : atomPoint k m n i ∈ atomBox k m n i :=
  ⟨dyadicInterval_left_mem _ _, dyadicInterval_left_mem _ _, dyadicInterval_left_mem _ _⟩

-- @node: measurableSet_atomBox
/-- [Every atom box is Lebesgue measurable](goal). -/
lemma measurableSet_atomBox (k m : ℤ) (n : Fin 3 → ℕ)
    (i : Atom k m × (Atom k m × Atom k m)) : MeasurableSet (atomBox k m n i) :=
  measurableSet_Ico.prod (measurableSet_Ico.prod measurableSet_Ico)

-- @node: atomBox_pairwiseDisjoint
/-- [Atom boxes with distinct triples of atom indices are disjoint](goal) within
any fixed parent interval triple. -/
lemma atomBox_pairwiseDisjoint (k m : ℤ) (n : Fin 3 → ℕ) :
    Pairwise (fun i j => Disjoint (atomBox k m n i) (atomBox k m n j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  have he (v : Fin 3) (a b : Atom k m) (y : ℝ)
      (ha : y ∈ dyadicInterval m (atomIndex k m n v a))
      (hb : y ∈ dyadicInterval m (atomIndex k m n v b)) : a = b := by
    by_contra h
    have hn : atomIndex k m n v a ≠ atomIndex k m n v b := by
      simp only [atomIndex, ne_eq, Nat.add_left_cancel_iff, Fin.val_inj]
      exact h
    exact Set.disjoint_left.mp (dyadicInterval_pairwiseDisjoint m hn) ha hb
  exact hij (Prod.ext (he 0 _ _ x.1 hi.1 hj.1)
    (Prod.ext (he 1 _ _ x.2.1 hi.2.1 hj.2.1) (he 2 _ _ x.2.2 hi.2.2 hj.2.2)))

-- @node: iUnion_atomBox
/-- If [the atom scale is no larger than the parent scale](hyp:hk),
[the union of all atom boxes equals the Cartesian product of the three parent
dyadic intervals](goal). -/
lemma iUnion_atomBox (k m : ℤ) (n : Fin 3 → ℕ) (hk : m ≤ k) :
    (⋃ i, atomBox k m n i) = dyadicInterval k (n 0) ×ˢ
      (dyadicInterval k (n 1) ×ˢ dyadicInterval k (n 2)) := by
  rw [dyadicInterval_eq_iUnion_atoms k m (n 0) hk,
    dyadicInterval_eq_iUnion_atoms k m (n 1) hk,
    dyadicInterval_eq_iUnion_atoms k m (n 2) hk]
  ext x
  simp only [Set.mem_iUnion, Set.mem_prod, atomBox, atomIndex]
  constructor
  · rintro ⟨⟨i, j, l⟩, hi, hj, hl⟩
    exact ⟨⟨i, hi⟩, ⟨j, hj⟩, ⟨l, hl⟩⟩
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩, ⟨l, hl⟩⟩
    exact ⟨⟨i, j, l⟩, hi, hj, hl⟩

-- @node: triangularIntegrand_eq_on_atomBox
/-- If [each input is constant on every atom-scale rectangle](hyp:hAtoms),
[the parent scale is at least one larger than the atom scale](hyp:hk), and
[a point belongs to a specified atom box](hyp:hx), then [the triangular integrand
at that point equals its value at the box's representative point](goal). -/
lemma triangularIntegrand_eq_on_atomBox (k m : ℤ) (n : Fin 3 → ℕ)
    (F : Fin 3 → ℝ × ℝ → ℝ) (hAtoms : StepAtoms F m) (hk : m + 1 ≤ k)
    (i : Atom k m × (Atom k m × Atom k m)) (x : ℝ × (ℝ × ℝ))
    (hx : x ∈ atomBox k m n i) :
    triangularIntegrand k n F x = triangularIntegrand k n F (atomPoint k m n i) := by
  have hy := atomPoint_mem_atomBox k m n i
  have hf₀ := hAtoms 0 _ _ (x.1, x.2.1)
    ((atomPoint k m n i).1, (atomPoint k m n i).2.1) ⟨hx.1, hx.2.1⟩ ⟨hy.1, hy.2.1⟩
  have hf₁ := hAtoms 1 _ _ (x.2.1, x.2.2)
    ((atomPoint k m n i).2.1, (atomPoint k m n i).2.2)
    ⟨hx.2.1, hx.2.2⟩ ⟨hy.2.1, hy.2.2⟩
  have hf₂ := hAtoms 2 _ _ (x.2.2, x.1)
    ((atomPoint k m n i).2.2, (atomPoint k m n i).1) ⟨hx.2.2, hx.1⟩ ⟨hy.2.2, hy.1⟩
  have hh₀ := haarSign_eq_on_subatom k m (n 0) i.1 hk _ _ hx.1 hy.1
  have hh₁ := haarSign_eq_on_subatom k m (n 1) i.2.1 hk _ _ hx.2.1 hy.2.1
  have hh₂ := haarSign_eq_on_subatom k m (n 2) i.2.2 hk _ _ hx.2.2 hy.2.2
  unfold triangularIntegrand
  rw [hf₀, hf₁, hf₂, hh₀, hh₁, hh₂]

-- @node: volume_atomBox
/-- [Every atom box has Lebesgue volume equal to two raised to three times the
atom scale](goal). -/
lemma volume_atomBox (k m : ℤ) (n : Fin 3 → ℕ)
    (i : Atom k m × (Atom k m × Atom k m)) :
    volume (atomBox k m n i) = ENNReal.ofReal ((2 : ℝ) ^ (3 * m)) := by
  rw [atomBox, Measure.volume_eq_prod, Measure.prod_prod,
    Measure.volume_eq_prod, Measure.prod_prod]
  have hv (a : ℕ) : volume (dyadicInterval m a) = ENNReal.ofReal ((2 : ℝ) ^ m) := by
    rw [dyadicInterval, Real.volume_Ico]
    congr 1
    ring
  simp only [hv, ← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) ^ m)]
  congr 1
  rw [← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num)]
  congr 1
  ring

-- @node: integrableOn_triangularIntegrand_atomBox
/-- If [each input is constant on every atom-scale rectangle](hyp:hAtoms) and
[the parent scale is at least one larger than the atom scale](hyp:hk), then
[the triangular integrand is integrable over every atom box](goal). -/
lemma integrableOn_triangularIntegrand_atomBox (k m : ℤ) (n : Fin 3 → ℕ)
    (F : Fin 3 → ℝ × ℝ → ℝ) (hAtoms : StepAtoms F m) (hk : m + 1 ≤ k)
    (i : Atom k m × (Atom k m × Atom k m)) :
    IntegrableOn (triangularIntegrand k n F) (atomBox k m n i) := by
  apply (integrableOn_congr_fun
    (triangularIntegrand_eq_on_atomBox k m n F hAtoms hk i)
    (measurableSet_atomBox k m n i)).mpr
  exact integrableOn_const (by rw [volume_atomBox]; exact ENNReal.ofReal_ne_top)

-- @node: integral_triangularIntegrand_atomBox
/-- If [each input is constant on every atom-scale rectangle](hyp:hAtoms) and
[the parent scale is at least one larger than the atom scale](hyp:hk), then
[the integral of the triangular integrand over an atom box equals two raised to
three times the atom scale times its value at the box's representative point](goal). -/
lemma integral_triangularIntegrand_atomBox (k m : ℤ) (n : Fin 3 → ℕ)
    (F : Fin 3 → ℝ × ℝ → ℝ) (hAtoms : StepAtoms F m) (hk : m + 1 ≤ k)
    (i : Atom k m × (Atom k m × Atom k m)) :
    (∫ x in atomBox k m n i, triangularIntegrand k n F x) =
      (2 : ℝ) ^ (3 * m) * triangularIntegrand k n F (atomPoint k m n i) := by
  rw [setIntegral_congr_fun (measurableSet_atomBox k m n i)
    (triangularIntegrand_eq_on_atomBox k m n F hAtoms hk i), setIntegral_const]
  simp only [Measure.real, volume_atomBox,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (3 * m)), smul_eq_mul]

-- @node: localForm_eq_atom_sum
/-- If [each input is constant on every atom-scale rectangle](hyp:hAtoms) and
[the parent scale is at least one larger than the atom scale](hyp:hk), then
[the local trilinear form equals the sum of the triangular integrand at all
representative atom points, multiplied by two raised to three times the atom
scale minus the parent scale](goal). -/
lemma localForm_eq_atom_sum (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (n : Fin 3 → ℕ) (hAtoms : StepAtoms F m) (hk : m + 1 ≤ k) :
    localForm k n F = (2 : ℝ) ^ (3 * m - k) *
      ∑ i : Atom k m × (Atom k m × Atom k m),
        triangularIntegrand k n F (atomPoint k m n i) := by
  change (2 : ℝ) ^ (-k) * (∫ x in _, triangularIntegrand k n F x) = _
  rw [← iUnion_atomBox k m n (by omega),
    integral_iUnion_fintype (measurableSet_atomBox k m n)
      (atomBox_pairwiseDisjoint k m n)
      (integrableOn_triangularIntegrand_atomBox k m n F hAtoms hk)]
  simp_rw [integral_triangularIntegrand_atomBox k m n F hAtoms hk]
  rw [← Finset.mul_sum, ← mul_assoc, ← zpow_add₀ (by norm_num)]
  congr 2
  ring

-- @node: localTrace_eq_atom_sum
/-- [The local matrix trace equals the cube of the normalized atom weight times
the sum of the triangular integrand at all representative atom points](goal). -/
lemma localTrace_eq_atom_sum (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (n : Fin 3 → ℕ) :
    localTrace F k m n = atomWeight k m ^ 3 *
      ∑ i : Atom k m × (Atom k m × Atom k m),
        triangularIntegrand k n F (atomPoint k m n i) := by
  let A (v : Fin 3) := haarDiag k m n v * weightedEdge F k m n v
  have he : localTrace F k m n = (A 0 * A 1 * A 2).trace := by
    unfold localTrace A
    congr 1
    noncomm_ring
  rw [he]
  have hA (v : Fin 3) (i j : Atom k m) : A v i j =
      haarSign k (n v) ((2 : ℝ) ^ m * atomIndex k m n v i) *
        (atomWeight k m * atomValue F k m n v i j) := by
    dsimp [A, haarDiag]
    rw [Matrix.diagonal_mul, weightedEdge, Real.sqrt_mul_self (atomWeight_pos k m).le]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.sum_mul,
    hA, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  simp only [triangularIntegrand, atomPoint, atomValue, nextVertex]
  simp only [show (0 : Fin 3) + 1 = 1 from rfl,
    show (1 : Fin 3) + 1 = 2 from rfl, show (2 : Fin 3) + 1 = 0 from rfl]
  ring

-- @node: traceNormalizedForm_eq_atom_sum
/-- [The trace-normalized form equals the sum of the triangular integrand at all
representative atom points, multiplied by two raised to three times the atom
scale minus the parent scale](goal). -/
lemma traceNormalizedForm_eq_atom_sum (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (n : Fin 3 → ℕ) :
    traceNormalizedForm F k m n = (2 : ℝ) ^ (3 * m - k) *
      ∑ i : Atom k m × (Atom k m × Atom k m),
        triangularIntegrand k n F (atomPoint k m n i) := by
  rw [traceNormalizedForm, localTrace_eq_atom_sum, ← mul_assoc]
  congr 1
  simp only [atomWeight, pow_succ, pow_zero, one_mul,
    ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  ring

-- @node: localForm_eq_traceNormalizedForm
/-- If [each input is constant on every atom-scale rectangle](hyp:hAtoms),
[the three interval indices have bitwise XOR zero](hyp:hTriple),
[the parent scale is at least one larger than the atom scale](hyp:hScale), and
[Haar signs take value one on left halves and minus one on right halves](hyp:hHalves),
then [the local trilinear integral equals the trace-normalized matrix form](goal). -/
lemma localForm_eq_traceNormalizedForm (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (n : Fin 3 → ℕ) (hAtoms : StepAtoms F m) (hTriple : IncreaseTriple n)
    (hScale : IncreaseScale k m) (hHalves : HaarHalvesConvention) :
    localForm k n F = traceNormalizedForm F k m n := by
  exact (localForm_eq_atom_sum F k m n hAtoms hScale).trans
    (traceNormalizedForm_eq_atom_sum F k m n).symm

end Papers.OaiBoundDyadicTriangular
