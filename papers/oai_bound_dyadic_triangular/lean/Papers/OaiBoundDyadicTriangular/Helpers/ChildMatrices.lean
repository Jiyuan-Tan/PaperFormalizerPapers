module

public import Papers.OaiBoundDyadicTriangular.Helpers.AtomTrace
public import Papers.OaiBoundDyadicTriangular.Helpers.HessianTransport
public import Papers.OaiBoundDyadicTriangular.TGap
public import Papers.OaiBoundDyadicTriangular.TTrace

/-! # Child atom embeddings, conditional Gram averages, and vertex energy gaps -/

@[expose] public section

open Matrix
open scoped BigOperators MatrixOrder

namespace Papers.OaiBoundDyadicTriangular

-- @node: child_atom_count
/-- If [the parent scale is at least one above the atom scale](hyp:hk),
[the number of parent atoms is twice the number of atoms in either child](goal). -/
lemma child_atom_count (k m : ℤ) (hk : m + 1 ≤ k) :
    2 ^ (k - m).toNat = 2 * 2 ^ (k - 1 - m).toNat := by
  have he : (k - m).toNat = (k - 1 - m).toNat + 1 := by omega
  rw [he, pow_succ, Nat.mul_comm]

-- @node: childAtom
/-- For [parent scale k and atom scale m](hyp:k,m), with [k at least one above
m](hyp:hk), [a choice of half](hyp:b), and [an atom within that half](hyp:i),
the [corresponding parent atom](goal) has index equal to the half's offset plus
the atom's index. -/
def childAtom (k m : ℤ) (hk : m + 1 ≤ k) (b : Fin 2)
    (i : Atom (k - 1) m) : Atom k m :=
  ⟨b.val * 2 ^ (k - 1 - m).toNat + i.val, by
    rw [child_atom_count k m hk]
    have := b.isLt
    have := i.isLt
    nlinarith⟩

-- @node: childAtom_injective
/-- If [the parent scale is at least one above the atom scale](hyp:hk),
[embedding atoms from either fixed half into the parent is injective](goal). -/
lemma childAtom_injective (k m : ℤ) (hk : m + 1 ≤ k) (b : Fin 2) :
    Function.Injective (childAtom k m hk b) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp [childAtom] at this
  omega

-- @node: childInclusion
/-- For [parent and atom scales](hyp:k,m) with [the parent scale at least one
above the atom scale](hyp:hk) and [a selected half](hyp:b), the [child inclusion matrix](goal)
has [entry one when the parent atom is the embedded child atom](step:1) and
[entry zero otherwise](step:2). -/
def childInclusion (k m : ℤ) (hk : m + 1 ≤ k) (b : Fin 2) :
    Matrix (Atom k m) (Atom (k - 1) m) ℝ :=
  fun i j => if i = childAtom k m hk b j then 1 else 0

-- @node: childInclusion_compress_left
/-- When [the parent scale is at least one above the atom scale](hyp:hk),
[multiplying a matrix on the left by the transposed child inclusion selects
exactly its rows in that child](goal). -/
lemma childInclusion_compress_left (k m : ℤ) (hk : m + 1 ≤ k) (b : Fin 2)
    {α : Type*} (A : Matrix (Atom k m) α ℝ) :
    (childInclusion k m hk b).transpose * A = A.submatrix (childAtom k m hk b) id := by
  ext i j
  simp [Matrix.mul_apply, childInclusion, Matrix.transpose_apply]

-- @node: childInclusion_compress_right
/-- When [the parent scale is at least one above the atom scale](hyp:hk),
[multiplying a matrix on the right by the child inclusion selects exactly its
columns in that child](goal). -/
lemma childInclusion_compress_right (k m : ℤ) (hk : m + 1 ≤ k) (b : Fin 2)
    {α : Type*} (A : Matrix α (Atom k m) ℝ) :
    A * childInclusion k m hk b = A.submatrix id (childAtom k m hk b) := by
  ext i j
  simp [Matrix.mul_apply, childInclusion]

-- @node: childInclusion_isometry
/-- If [the parent scale is at least one above the atom scale](hyp:hk),
[the transposed child inclusion times the child inclusion is the identity,
so the inclusion preserves Euclidean lengths](goal). -/
lemma childInclusion_isometry (k m : ℤ) (hk : m + 1 ≤ k) (b : Fin 2) :
    (childInclusion k m hk b).transpose * childInclusion k m hk b = 1 := by
  rw [childInclusion_compress_left]
  ext i j
  simp [childInclusion, Matrix.one_apply, (childAtom_injective k m hk b).eq_iff]

-- @node: childProjection
/-- For [parent and atom scales](hyp:k,m) with [the parent scale at least one
above the atom scale](hyp:hk) and [a chosen half](hyp:b), the [projection onto that child's
coordinates](goal) is the child inclusion times its transpose. -/
def childProjection (k m : ℤ) (hk : m + 1 ≤ k) (b : Fin 2) :
    Matrix (Atom k m) (Atom k m) ℝ :=
  childInclusion k m hk b * (childInclusion k m hk b).transpose

-- @node: childProjection_isSymm
/-- If [the parent scale is at least one above the atom scale](hyp:hk),
[the projection onto either child's coordinates is symmetric](goal). -/
lemma childProjection_isSymm (k m : ℤ) (hk : m + 1 ≤ k) (b : Fin 2) :
    (childProjection k m hk b).IsSymm := by
  simp [Matrix.IsSymm, childProjection, Matrix.transpose_mul]

-- @node: childProjection_idempotent
/-- If [the parent scale is at least one above the atom scale](hyp:hk),
[applying a child projection twice gives the same matrix as applying it
once](goal). -/
lemma childProjection_idempotent (k m : ℤ) (hk : m + 1 ≤ k) (b : Fin 2) :
    childProjection k m hk b * childProjection k m hk b = childProjection k m hk b := by
  simp only [childProjection, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (childInclusion k m hk b).transpose,
    childInclusion_isometry, Matrix.one_mul]

-- @node: child_atomIndex
/-- If [the parent scale is at least one above the atom scale](hyp:hk),
[an atom's global index computed in a selected child interval equals its global
index computed in the parent interval after embedding](goal). -/
lemma child_atomIndex (k m : ℤ) (hk : m + 1 ≤ k) (n : Fin 3 → ℕ)
    (b : Fin 3 → Fin 2) (v : Fin 3) (i : Atom (k - 1) m) :
    atomIndex (k - 1) m (fun w => 2 * n w + (b w).val) v i =
      atomIndex k m n v (childAtom k m hk (b v) i) := by
  dsimp [atomIndex, childAtom]
  rw [child_atom_count k m hk]
  ring

-- @node: child_weightedEdge
/-- If [the parent scale is at least one above the atom scale](hyp:hk),
[the weighted edge matrix on the selected child intervals is twice the parent
edge matrix restricted to the selected halves at its two endpoints](goal). -/
lemma child_weightedEdge (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (hk : m + 1 ≤ k) (n : Fin 3 → ℕ) (b : Fin 3 → Fin 2) (v : Fin 3) :
    weightedEdge F (k - 1) m (fun w => 2 * n w + (b w).val) v =
      (2 : ℝ) • ((childInclusion k m hk (b v)).transpose * weightedEdge F k m n v *
        childInclusion k m hk (b (v + 1))) := by
  rw [childInclusion_compress_left, childInclusion_compress_right]
  ext i j
  simp only [weightedEdge, Real.sqrt_mul_self (atomWeight_pos _ _).le,
    atomValue, child_atomIndex k m hk, Matrix.smul_apply, smul_eq_mul,
    Matrix.submatrix_apply, id_eq, nextVertex]
  have hw : atomWeight (k - 1) m = 2 * atomWeight k m := by
    unfold atomWeight
    rw [show m - (k - 1) = 1 + (m - k) by ring,
      zpow_add₀ (by norm_num), zpow_one]
  rw [hw]
  ring

-- @node: matrixEnergy_row_isometric_extension
/-- If [an embedding matrix has transpose times itself equal to the
identity](hyp:hJ), [embedding a row covariance matrix by this matrix and its
transpose leaves its matrix energy unchanged](goal). -/
lemma matrixEnergy_row_isometric_extension {α β γ : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] (J : Matrix γ α ℝ) (hJ : J.transpose * J = 1)
    (R : Matrix α β ℝ) :
    matrixEnergy (J * (R * R.transpose) * J.transpose) =
      matrixEnergy (R * R.transpose) := by
  have he : J * (R * R.transpose) * J.transpose = (J * R) * (J * R).transpose := by
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [he, ← matrixEnergy_gram]
  have hg : (J * R).transpose * (J * R) = R.transpose * R := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc J.transpose, hJ, Matrix.one_mul]
  rw [hg, matrixEnergy_gram]

-- @node: childAtom_div
/-- If [the parent scale is at least one above the atom scale](hyp:hk),
[integer division of an embedded atom's index by the number of atoms in a child
recovers the selected half, zero or one](goal). -/
lemma childAtom_div (k m : ℤ) (hk : m + 1 ≤ k) (b : Fin 2)
    (i : Atom (k - 1) m) :
    (childAtom k m hk b i).val / 2 ^ (k - 1 - m).toNat = b.val := by
  dsimp [childAtom]
  rw [Nat.mul_comm b.val, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt i.isLt, add_zero]

-- @node: childAtom_exists
/-- If [the parent scale is at least one above the atom scale](hyp:hk) and
[an atom's index divided by the child atom count identifies the selected
half](hyp:hi), [that atom is the embedding of some atom in that half](goal). -/
lemma childAtom_exists (k m : ℤ) (hk : m + 1 ≤ k) (b : Fin 2)
    (i : Atom k m) (hi : i.val / 2 ^ (k - 1 - m).toNat = b.val) :
    ∃ j, i = childAtom k m hk b j := by
  refine ⟨⟨i.val % 2 ^ (k - 1 - m).toNat, Nat.mod_lt _ (by positivity)⟩, ?_⟩
  apply Fin.ext
  dsimp [childAtom]
  rw [← hi]
  simpa only [Nat.mul_comm] using (Nat.div_add_mod i.val (2 ^ (k - 1 - m).toNat)).symm

-- @node: childProjection_apply
/-- If [the parent scale is at least one above the atom scale](hyp:hk),
[a child projection has entry one exactly on diagonal positions whose atom
index, divided by the child atom count, equals the selected half; all other
entries are zero](goal). -/
lemma childProjection_apply (k m : ℤ) (hk : m + 1 ≤ k) (b : Fin 2)
    (i j : Atom k m) :
    childProjection k m hk b i j =
      if i = j ∧ i.val / 2 ^ (k - 1 - m).toNat = b.val then 1 else 0 := by
  by_cases hi : i.val / 2 ^ (k - 1 - m).toNat = b.val
  · obtain ⟨a, rfl⟩ := childAtom_exists k m hk b i hi
    simp only [childProjection, Matrix.mul_apply, childInclusion, Matrix.transpose_apply,
      (childAtom_injective k m hk b).eq_iff]
    rw [Finset.sum_eq_single a]
    · simp [childAtom_div, eq_comm]
    · intro c _ hc
      simp [Ne.symm hc]
    · simp
  · have hn (a : Atom (k - 1) m) : i ≠ childAtom k m hk b a := by
      intro he
      exact hi (he ▸ childAtom_div k m hk b a)
    simp [childProjection, Matrix.mul_apply, childInclusion, hn, hi]

-- @node: childProjection_sum
/-- If [the parent scale is at least one above the atom scale](hyp:hk),
[the projections onto the two halves sum to the identity matrix](goal). -/
lemma childProjection_sum (k m : ℤ) (hk : m + 1 ≤ k) :
    childProjection k m hk 0 + childProjection k m hk 1 = 1 := by
  ext i j
  have hlt : i.val / 2 ^ (k - 1 - m).toNat < 2 := by
    apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
    simpa only [child_atom_count k m hk, Nat.mul_comm] using i.isLt
  simp only [Matrix.add_apply, childProjection_apply, Matrix.one_apply,
    Fin.val_zero, Fin.val_one]
  by_cases hij : i = j
  · have hi : i.val / 2 ^ (k - 1 - m).toNat = 0 ∨
        i.val / 2 ^ (k - 1 - m).toNat = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ hlt)
    subst j
    rcases hi with hi | hi <;> simp only [hi, and_self, if_true, and_false, if_false] <;> norm_num
  · simp [hij]

-- @node: haarSign_childAtom
/-- If [the parent scale is at least one above the atom scale](hyp:hk),
[the parent's Haar sign at the left endpoint of an embedded atom is the sign
of its selected half: plus one for the first half and minus one for the
second](goal). -/
lemma haarSign_childAtom (k m : ℤ) (hk : m + 1 ≤ k) (a : ℕ)
    (b : Fin 2) (i : Atom (k - 1) m) :
    haarSign k a ((2 : ℝ)^m *
      (2 ^ (k - m).toNat * a + (childAtom k m hk b i).val)) = childSign b := by
  have he : 2 ^ (k - m).toNat * a + (childAtom k m hk b i).val =
      2 ^ (k - 1 - m).toNat * (2 * a + b.val) + i.val := by
    dsimp [childAtom]
    rw [child_atom_count k m hk]
    ring
  have heR := congrArg (fun q : ℕ => (q : ℝ)) he
  push_cast at heR
  rw [heR]
  have hx := dyadic_subatom_subset (k - 1) m (2 * a + b.val) i (by omega)
    (dyadicInterval_left_mem m _)
  push_cast at hx
  have hd := dyadicInterval_pairwiseDisjoint (k - 1) (show 2 * a ≠ 2 * a + 1 by omega)
  fin_cases b
  · simp only [Fin.val_zero, add_zero] at hx
    norm_num only [Nat.cast_zero, add_zero] at hx
    have hn := Set.disjoint_left.mp hd hx
    simp [haarSign, hx, hn, childSign]
  · simp only [Fin.val_one] at hx
    norm_num only [Nat.cast_one] at hx
    have hn := Set.disjoint_right.mp hd hx
    simp [haarSign, hx, hn, childSign]

-- @node: haarDiag_eq_childProjection_sub
/-- If [the parent scale is at least one above the atom scale](hyp:hk),
[the diagonal matrix of Haar signs equals the first child projection minus
the second child projection](goal). -/
lemma haarDiag_eq_childProjection_sub (k m : ℤ) (hk : m + 1 ≤ k)
    (n : Fin 3 → ℕ) (v : Fin 3) :
    haarDiag k m n v = childProjection k m hk 0 - childProjection k m hk 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    have hlt : i.val / 2 ^ (k - 1 - m).toNat < 2 := by
      apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
      simpa only [child_atom_count k m hk, Nat.mul_comm] using i.isLt
    have hv (b : Fin 2) (hi : i.val / 2 ^ (k - 1 - m).toNat = b.val) :
        haarSign k (n v) ((2 : ℝ)^m * atomIndex k m n v i) = childSign b := by
      obtain ⟨a, rfl⟩ := childAtom_exists k m hk b i hi
      simpa only [atomIndex, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
        haarSign_childAtom k m hk (n v) b a
    have hi : i.val / 2 ^ (k - 1 - m).toNat = 0 ∨
        i.val / 2 ^ (k - 1 - m).toNat = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ hlt)
    rcases hi with hi | hi
    · simp [haarDiag, hv 0 hi, Matrix.sub_apply, childProjection_apply, hi, childSign]
    · simp [haarDiag, hv 1 hi, Matrix.sub_apply, childProjection_apply, hi, childSign]
  · simp [haarDiag, Matrix.diagonal_apply_ne _ hij, Matrix.sub_apply,
      childProjection_apply, hij]

-- @node: compressed_rowGram
/-- [For the row matrix formed from twice the compressed outgoing and incoming
edge matrices, embedding its row covariance gives four times the sum of the
two edge covariance contributions, with each neighboring contribution weighted
by its embedding times its transpose and the whole sum multiplied on both
sides by the central embedding times its transpose](goal). -/
lemma compressed_rowGram {α β : Type*} [Fintype α] [Fintype β]
    (J K L : Matrix α β ℝ) (W V : Matrix α α ℝ) :
    J * (rowStar ((2 : ℝ) • (J.transpose * W * K)) ((2 : ℝ) • (L.transpose * V * J)) *
        (rowStar ((2 : ℝ) • (J.transpose * W * K)) ((2 : ℝ) • (L.transpose * V * J))).transpose) *
      J.transpose =
    (4 : ℝ) • ((J * J.transpose) *
      (W * (K * K.transpose) * W.transpose +
        V.transpose * (L * L.transpose) * V) * (J * J.transpose)) := by
  rw [rowStar, Matrix.transpose_fromCols, Matrix.transpose_transpose,
    Matrix.fromCols_mul_fromRows]
  simp only [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_add, Matrix.add_mul,
    smul_add, Matrix.mul_assoc]
  norm_num

-- @node: childGram
/-- Given [three edge functions](hyp:F), [parent and atom scales](hyp:k,m)
with [the parent scale at least one above the atom scale](hyp:hk), [parent interval indices](hyp:n),
[half selections at the three vertices](hyp:b), and [a vertex](hyp:v), the
[embedded child covariance matrix](goal) is obtained by [forming the row matrix
at that vertex for the selected child intervals](step:1), then [embedding its
product with its transpose into the parent coordinates](step:2). -/
noncomputable def childGram (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (hk : m + 1 ≤ k) (n : Fin 3 → ℕ) (b : Fin 3 → Fin 2) (v : Fin 3) :
    Matrix (Atom k m) (Atom k m) ℝ :=
  let R := atomRowStar F (k - 1) m (fun w => 2 * n w + (b w).val) v
  childInclusion k m hk (b v) * (R * R.transpose) *
    (childInclusion k m hk (b v)).transpose

-- @node: childGram_energy
/-- If [the parent scale is at least one above the atom scale](hyp:hk),
[the matrix energy of the embedded child covariance equals the vertex energy
on the selected child intervals](goal). -/
lemma childGram_energy (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (hk : m + 1 ≤ k) (n : Fin 3 → ℕ) (b : Fin 3 → Fin 2) (v : Fin 3) :
    matrixEnergy (childGram F k m hk n b v) =
      vertexEnergy F (k - 1) m (fun w => 2 * n w + (b w).val) v := by
  rw [childGram, matrixEnergy_row_isometric_extension _ (childInclusion_isometry k m hk _)]
  exact (matrixEnergy_gram _).symm

-- @node: childGram_posSemidef
/-- If [the parent scale is at least one above the atom scale](hyp:hk),
[the embedded child covariance matrix is positive semidefinite](goal). -/
lemma childGram_posSemidef (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (hk : m + 1 ≤ k) (n : Fin 3 → ℕ) (b : Fin 3 → Fin 2) (v : Fin 3) :
    (childGram F k m hk n b v).PosSemidef := by
  apply posSemidef_isometric_extension
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_self_mul_conjTranspose
      (atomRowStar F (k - 1) m (fun w => 2 * n w + (b w).val) v)

-- @node: childGram_formula
/-- If [the parent scale is at least one above the atom scale](hyp:hk),
[the embedded child covariance is four times the central child projection
times the sum of the outgoing edge covariance weighted by the next child's
projection and the incoming edge covariance weighted by the previous child's
projection, times the central child projection again](goal). -/
lemma childGram_formula (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (hk : m + 1 ≤ k) (n : Fin 3 → ℕ) (b : Fin 3 → Fin 2) (v : Fin 3) :
    childGram F k m hk n b v =
      (4 : ℝ) • (childProjection k m hk (b v) *
        (weightedEdge F k m n v * childProjection k m hk (b (v + 1)) *
            (weightedEdge F k m n v).transpose +
          (weightedEdge F k m n (v + 2)).transpose *
            childProjection k m hk (b (v + 2)) * weightedEdge F k m n (v + 2)) *
        childProjection k m hk (b v)) := by
  have hv : v + 2 + 1 = v := by fin_cases v <;> rfl
  simp only [childGram, atomRowStar, child_weightedEdge F k m hk, hv]
  exact compressed_rowGram _ _ _ _ _

-- @node: matrixEnergy_midpoint_convex
/-- If [the first matrix is positive semidefinite](hyp:hA) and [the second
matrix is positive semidefinite](hyp:hB), [the matrix energy of their average
is at most the average of their matrix energies](goal). -/
lemma matrixEnergy_midpoint_convex {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Matrix α α ℝ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    matrixEnergy ((1 / 2 : ℝ) • (A + B)) ≤
      (1 / 2 : ℝ) * (matrixEnergy A + matrixEnergy B) := by
  have hz : HessianDirection (1 : Matrix α α ℝ) 0 :=
    ⟨by simp [Matrix.IsSymm], fun _ _ => by simp⟩
  obtain ⟨_, _, _, _, _, _, hc⟩ :=
    matrixEnergy_hessian (1 : Matrix α α ℝ) 0 Matrix.PosSemidef.one hz
  simpa only [smul_add, smul_eq_mul, mul_add] using
    hc.2 hA hB (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)

-- @node: conditionalBits
/-- Given [a distinguished vertex](hyp:v), [its half-selection bit](hyp:a),
and [the next vertex's bit](hyp:c), the [conditional assignment of three
bits](goal) assigns [the first bit to the distinguished vertex](step:1),
[the second bit to the next vertex](step:2), and [their sum modulo two to the
remaining vertex](step:3). -/
def conditionalBits (v : Fin 3) (a c : Fin 2) : Fin 3 → Fin 2 :=
  fun w => if w = v then a else if w = v + 1 then c else a + c

-- @node: conditionalBits_self
/-- [The conditional bit assignment takes the prescribed first bit at the
distinguished vertex](goal). -/
lemma conditionalBits_self (v : Fin 3) (a c : Fin 2) : conditionalBits v a c v = a := by
  simp [conditionalBits]

-- @node: conditionalBits_next
/-- [The conditional bit assignment takes the prescribed second bit at the
next vertex in cyclic order](goal). -/
lemma conditionalBits_next (v : Fin 3) (a c : Fin 2) :
    conditionalBits v a c (v + 1) = c := by
  have hv : v + 1 ≠ v := by fin_cases v <;> decide
  simp [conditionalBits, hv]

-- @node: conditionalBits_prev
/-- [The conditional bit assignment at the remaining vertex is the sum modulo
two of the two prescribed bits](goal). -/
lemma conditionalBits_prev (v : Fin 3) (a c : Fin 2) :
    conditionalBits v a c (v + 2) = a + c := by
  have hv : v + 2 ≠ v := by fin_cases v <;> decide
  have hv' : v + 2 ≠ v + 1 := by fin_cases v <;> decide
  simp [conditionalBits, hv, hv']

-- @node: childBits_eq_conditionalBits
/-- [The four admissible child bit assignments are exactly the conditional
assignments obtained by choosing both bits freely at any distinguished vertex
and its next vertex](goal). -/
lemma childBits_eq_conditionalBits (v : Fin 3) :
    childBits = {conditionalBits v 0 0, conditionalBits v 0 1,
      conditionalBits v 1 0, conditionalBits v 1 1} := by
  fin_cases v <;> decide +kernel

-- @node: sum_childBits_eq_conditionalBits
/-- For [a real-valued function of the three half-selection bits](hyp:f),
[summing over admissible child assignments equals summing over the two freely
chosen bits in the conditional assignment](goal). -/
lemma sum_childBits_eq_conditionalBits (v : Fin 3) (f : (Fin 3 → Fin 2) → ℝ) :
    ∑ b ∈ childBits, f b = ∑ a : Fin 2, ∑ c : Fin 2, f (conditionalBits v a c) := by
  rw [childBits_eq_conditionalBits v]
  have hd : conditionalBits v 0 0 ≠ conditionalBits v 0 1 ∧
      conditionalBits v 0 0 ≠ conditionalBits v 1 0 ∧
      conditionalBits v 0 0 ≠ conditionalBits v 1 1 ∧
      conditionalBits v 0 1 ≠ conditionalBits v 1 0 ∧
      conditionalBits v 0 1 ≠ conditionalBits v 1 1 ∧
      conditionalBits v 1 0 ≠ conditionalBits v 1 1 := by
    fin_cases v <;> decide +kernel
  simp [Fin.sum_univ_two, hd.1, hd.2.1, hd.2.2.1,
    hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2, add_assoc]

-- @node: conditional_childGram_average
/-- If [the parent scale is at least one above the atom scale](hyp:hk),
[averaging the two embedded child covariance matrices while fixing the bit at
the chosen vertex gives twice the parent row covariance projected on both sides
onto that vertex's selected half](goal). -/
lemma conditional_childGram_average (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (hk : m + 1 ≤ k) (n : Fin 3 → ℕ) (v : Fin 3) (a : Fin 2) :
    (1 / 2 : ℝ) • (childGram F k m hk n (conditionalBits v a 0) v +
      childGram F k m hk n (conditionalBits v a 1) v) =
      (2 : ℝ) • (childProjection k m hk a *
        (atomRowStar F k m n v * (atomRowStar F k m n v).transpose) *
        childProjection k m hk a) := by
  simp only [childGram_formula, conditionalBits_self, conditionalBits_next,
    conditionalBits_prev]
  have hs : childProjection k m hk (a + 0) + childProjection k m hk (a + 1) = 1 := by
    fin_cases a
    · exact childProjection_sum k m hk
    · change childProjection k m hk 1 + childProjection k m hk 0 = 1
      rw [add_comm]
      exact childProjection_sum k m hk
  have he :
      childProjection k m hk a *
        (weightedEdge F k m n v * childProjection k m hk 0 *
            (weightedEdge F k m n v).transpose +
          (weightedEdge F k m n (v + 2)).transpose * childProjection k m hk (a + 0) *
            weightedEdge F k m n (v + 2)) * childProjection k m hk a +
      childProjection k m hk a *
        (weightedEdge F k m n v * childProjection k m hk 1 *
            (weightedEdge F k m n v).transpose +
          (weightedEdge F k m n (v + 2)).transpose * childProjection k m hk (a + 1) *
            weightedEdge F k m n (v + 2)) * childProjection k m hk a =
      childProjection k m hk a *
        (atomRowStar F k m n v * (atomRowStar F k m n v).transpose) *
        childProjection k m hk a := by
    rw [← Matrix.add_mul, ← Matrix.mul_add]
    rw [add_add_add_comm, ← Matrix.add_mul, ← Matrix.mul_add,
      ← Matrix.add_mul, ← Matrix.mul_add, childProjection_sum, hs]
    simp [atomRowStar, rowStar, Matrix.transpose_fromCols, Matrix.transpose_transpose,
      Matrix.fromCols_mul_fromRows]
  rw [← smul_add, smul_smul, he]
  norm_num

-- @node: twice_childProjection
/-- If [the parent scale is at least one above the atom scale](hyp:hk),
[twice a child projection equals the identity plus the diagonal Haar matrix
multiplied by that child's sign](goal). -/
lemma twice_childProjection (k m : ℤ) (hk : m + 1 ≤ k)
    (n : Fin 3 → ℕ) (v : Fin 3) (a : Fin 2) :
    (2 : ℝ) • childProjection k m hk a = 1 + childSign a • haarDiag k m n v := by
  rw [haarDiag_eq_childProjection_sub k m hk]
  have hs := childProjection_sum k m hk
  rw [← hs]
  fin_cases a <;> norm_num [childSign] <;> module

-- @node: matrixEnergy_projected_row
/-- If [the projecting matrix is symmetric](hyp:hH) and [its square equals
itself](hyp:hIdem), [the matrix energy of twice the row covariance projected on
both sides equals the matrix energy of the row transpose times twice the
projection times the row matrix](goal). -/
lemma matrixEnergy_projected_row {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (R : Matrix α β ℝ) (H : Matrix α α ℝ) (hH : H.IsSymm) (hIdem : H * H = H) :
    matrixEnergy ((2 : ℝ) • (H * (R * R.transpose) * H)) =
      matrixEnergy (R.transpose * ((2 : ℝ) • H) * R) := by
  let A := Real.sqrt 2 • (H * R)
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hLeft : A * A.transpose = (2 : ℝ) • (H * (R * R.transpose) * H) := by
    simp only [A, Matrix.transpose_smul, Matrix.transpose_mul, hH.eq,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs, Matrix.mul_assoc]
  have hRight : A.transpose * A = R.transpose * ((2 : ℝ) • H) * R := by
    simp only [A, Matrix.transpose_smul, Matrix.transpose_mul, hH.eq,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc H H, hIdem]
  rw [← hLeft, ← matrixEnergy_gram, hRight]

-- @node: conditional_vertexEnergy_bound
/-- If [the parent scale is at least one above the atom scale](hyp:hk),
[the energy of the parent Gram matrix plus the Haar row perturbation with the
chosen half's sign is at most the average vertex energy of the two admissible
children with that half fixed at the chosen vertex](goal). -/
lemma conditional_vertexEnergy_bound (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (hk : m + 1 ≤ k) (n : Fin 3 → ℕ) (v : Fin 3) (a : Fin 2) :
    matrixEnergy (rowGram (atomRowStar F k m n v) +
      childSign a • rowPerturbation (atomRowStar F k m n v) (haarDiag k m n v)) ≤
      (1 / 2 : ℝ) * (vertexEnergy F (k - 1) m
        (fun w => 2 * n w + (conditionalBits v a 0 w).val) v +
        vertexEnergy F (k - 1) m
        (fun w => 2 * n w + (conditionalBits v a 1 w).val) v) := by
  have hc := matrixEnergy_midpoint_convex
    (childGram F k m hk n (conditionalBits v a 0) v)
    (childGram F k m hk n (conditionalBits v a 1) v)
    (childGram_posSemidef F k m hk n _ v) (childGram_posSemidef F k m hk n _ v)
  rw [conditional_childGram_average,
    matrixEnergy_projected_row _ _ (childProjection_isSymm k m hk a)
      (childProjection_idempotent k m hk a), twice_childProjection k m hk n v a,
    childGram_energy, childGram_energy] at hc
  simpa only [rowGram, rowPerturbation, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Matrix.mul_smul, Matrix.smul_mul] using hc

-- @node: haarDiag_isSymm
/-- [The diagonal matrix of Haar signs is symmetric](goal). -/
lemma haarDiag_isSymm (k m : ℤ) (n : Fin 3 → ℕ) (v : Fin 3) :
    (haarDiag k m n v).IsSymm := Matrix.isSymm_diagonal _

-- @node: haarDiag_order_bounds
/-- If [the parent scale is at least one above the atom scale](hyp:hk),
[both the identity minus the diagonal Haar matrix and the identity plus that
matrix are positive semidefinite](goal). -/
lemma haarDiag_order_bounds (k m : ℤ) (hk : m + 1 ≤ k)
    (n : Fin 3 → ℕ) (v : Fin 3) :
    (1 - haarDiag k m n v).PosSemidef ∧ (1 + haarDiag k m n v).PosSemidef := by
  have hp (b : Fin 2) : ((2 : ℝ) • childProjection k m hk b).PosSemidef := by
    apply Matrix.PosSemidef.smul _ (by norm_num)
    simpa only [childProjection, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose (childInclusion k m hk b)
  have h₀ := twice_childProjection k m hk n v 0
  have h₁ := twice_childProjection k m hk n v 1
  norm_num [childSign] at h₀ h₁
  constructor
  · simpa only [h₁, sub_eq_add_neg] using hp 1
  · simpa only [h₀] using hp 0

-- @node: vertexEnergy_child_gap
/-- If [the parent scale is at least one above the atom scale](hyp:hk),
[the average vertex energy over the four admissible children minus the parent
vertex energy is at least the energy Hessian's quadratic form at the parent
Gram matrix in the Haar row-perturbation direction, divided by twice the square
root of two](goal). -/
lemma vertexEnergy_child_gap (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (hk : m + 1 ≤ k) (n : Fin 3 → ℕ) (v : Fin 3) :
    1 / (2 * Real.sqrt 2) *
      hessForm (rowGram (atomRowStar F k m n v)) (rowGram_isHermitian _)
        (rowPerturbation (atomRowStar F k m n v) (haarDiag k m n v)) ≤
      (1 / 4 : ℝ) * (∑ b ∈ childBits, vertexEnergy F (k - 1) m
        (fun w => 2 * n w + (b w).val) v) - vertexEnergy F k m n v := by
  have hP : (rowGram (atomRowStar F k m n v)).PosSemidef := by
    simpa only [rowGram, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self (atomRowStar F k m n v)
  have hD := haarDiag_order_bounds k m hk n v
  have hg := (matrixEnergy_midpoint_gap _ _ hP
    (rowPerturbation_isSymm _ _ (haarDiag_isSymm k m n v))
    (by
      have ho := rowPerturbation_order_bounds (atomRowStar F k m n v)
        (haarDiag k m n v) hD.1 hD.2
      exact ⟨ho.2, ho.1⟩)).2
  have h₀ := conditional_vertexEnergy_bound F k m hk n v 0
  have h₁ := conditional_vertexEnergy_bound F k m hk n v 1
  norm_num only [childSign, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul,
    neg_smul, sub_eq_add_neg] at h₀ h₁
  rw [sum_childBits_eq_conditionalBits v]
  simp only [Fin.sum_univ_two]
  change _ ≤ _ - matrixEnergy (rowGram (atomRowStar F k m n v))
  simp only [sub_eq_add_neg] at hg ⊢
  linarith

-- @node: sum_children_eq_childBits
/-- For [a real-valued function of interval-index triples](hyp:f),
[summing over the children of a parent triple equals summing over admissible
bit assignments after replacing each parent index by twice that index plus
its selected bit](goal). -/
lemma sum_children_eq_childBits (n : Fin 3 → ℕ) (f : (Fin 3 → ℕ) → ℝ) :
    ∑ c ∈ children n, f c = ∑ b ∈ childBits, f (fun w => 2 * n w + (b w).val) := by
  rw [children, Finset.sum_image]
  intro a _ b _ hab
  funext v
  apply Fin.ext
  have hv := congrFun hab v
  dsimp at hv
  omega

end Papers.OaiBoundDyadicTriangular

