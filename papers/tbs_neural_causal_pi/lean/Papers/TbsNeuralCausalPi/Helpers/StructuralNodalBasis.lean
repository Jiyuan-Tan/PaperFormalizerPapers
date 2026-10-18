module
public import Papers.TbsNeuralCausalPi.Helpers.StructuralInterpolation
public import Mathlib.Data.Finset.Lattice.Fold
/-! # Nodal hats on the Kuhn triangulation

The finite minimum below is precisely the minimum of `1`, `1 ± z_k`,
and `1 + z_k - z_l`. The added zero coordinate includes the boundary terms
and makes the construction valid also in dimension zero. On an ordered
simplex, translating to each vertex gives its exact barycentric weight.
-/
@[expose] public section

namespace Papers.TbsNeuralCausalPi
open scoped BigOperators NNReal
set_option linter.style.longLine false
noncomputable section

-- @node: structuralHatTerm
/-- For [a coordinate vector](hyp:z) and [an ordered pair of indices into that vector
with a leading zero added](hyp:ab), the [affine hat term](goal) is one plus the
first selected coordinate minus the second. -/
def structuralHatTerm {d : ℕ} (z : Fin d → ℝ)
    (ab : Fin (d + 1) × Fin (d + 1)) : ℝ :=
  1 + Fin.cons (α := fun _ => ℝ) 0 z ab.1 - Fin.cons (α := fun _ => ℝ) 0 z ab.2

-- @node: structuralNodalHat
/-- For [a coordinate vector](hyp:z), the [structural nodal hat](goal) is the
maximum of zero and the minimum of all affine hat terms formed from its
coordinates together with a leading zero. -/
def structuralNodalHat {d : ℕ} (z : Fin d → ℝ) : ℝ :=
  max 0 (Finset.univ.inf' Finset.univ_nonempty (structuralHatTerm z))

-- @node: structuralHat_min_of_extrema
/-- If the coordinates of a vector augmented by a leading zero are
[all at least a lower bound](hyp:hl) and [all at most an upper bound](hyp:hu),
and [the lower bound is attained](hyp:hla) and [the upper bound is attained](hyp:hua),
then [the minimum affine hat term equals one plus the lower bound minus the upper bound](goal). -/
lemma structuralHat_min_of_extrema {d : ℕ} (z : Fin d → ℝ) (l u : ℝ)
    (hl : ∀ a, l ≤ Fin.cons (α := fun _ => ℝ) 0 z a) (hu : ∀ a, Fin.cons (α := fun _ => ℝ) 0 z a ≤ u)
    (hla : ∃ a, Fin.cons (α := fun _ => ℝ) 0 z a = l) (hua : ∃ a, Fin.cons (α := fun _ => ℝ) 0 z a = u) :
    Finset.univ.inf' Finset.univ_nonempty (structuralHatTerm z) = 1 + l - u := by
  obtain ⟨a, ha⟩ := hla
  obtain ⟨b, hb⟩ := hua
  apply le_antisymm
  · exact (Finset.inf'_le _ (Finset.mem_univ (a, b))).trans_eq
      (by simp only [structuralHatTerm, ha, hb])
  · apply Finset.le_inf'
    intro ab _
    dsimp only [structuralHatTerm]
    linarith [hl ab.1, hu ab.2]

-- @node: orderedVertexShift
/-- For [a coordinate vector](hyp:t), [a simplex vertex index](hyp:i), and
[a coordinate index](hyp:j), the [shifted coordinate](goal) subtracts one from
that coordinate if its index precedes the vertex index, and subtracts zero otherwise. -/
def orderedVertexShift {d : ℕ} (t : Fin d → ℝ) (i : Fin (d + 1)) (j : Fin d) : ℝ :=
  t j - if j.val < i.val then 1 else 0

-- @node: orderedVertexShift_lower_nonpos
/-- If [every coordinate lies between zero and one](hyp:ht), then
[each entry of the vector with a leading one added, minus one, is nonpositive](goal). -/
lemma orderedVertexShift_lower_nonpos {d : ℕ} (t : Fin d → ℝ)
    (ht : ∀ j, t j ∈ Set.Icc 0 1) (i : Fin (d + 1)) :
    Fin.cons (α := fun _ => ℝ) 1 t i - 1 ≤ 0 := by
  refine Fin.cases (by simp) (fun j => ?_) i
  simpa using sub_nonpos.mpr (ht j).2

-- @node: orderedVertexShift_upper_nonneg
/-- If [every coordinate lies between zero and one](hyp:ht), then
[each entry of the vector with a trailing zero added is nonnegative](goal). -/
lemma orderedVertexShift_upper_nonneg {d : ℕ} (t : Fin d → ℝ)
    (ht : ∀ j, t j ∈ Set.Icc 0 1) (i : Fin (d + 1)) :
    0 ≤ Fin.snoc (α := fun _ => ℝ) t 0 i := by
  by_cases hi : i = Fin.last d
  · subst i; simp
  · obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
    simpa using (ht j).1

-- @node: orderedVertexShift_lower
/-- If [all coordinates lie between zero and one](hyp:ht) and
[the coordinates are nonincreasing](hyp:horder), then
[the entry at the vertex index in the vector with a leading one, minus one,
is a lower bound for every coordinate shifted about that vertex](goal). -/
lemma orderedVertexShift_lower {d : ℕ} (t : Fin d → ℝ)
    (ht : ∀ j, t j ∈ Set.Icc 0 1) (horder : Antitone t)
    (i : Fin (d + 1)) (j : Fin d) :
    Fin.cons (α := fun _ => ℝ) 1 t i - 1 ≤ orderedVertexShift t i j := by
  refine Fin.cases ?_ (fun k => ?_) i
  · simpa [orderedVertexShift] using (ht j).1
  · simp only [Fin.cons_succ, orderedVertexShift, Fin.val_succ]
    split_ifs with hj
    · have hjk : j ≤ k := by omega
      linarith [horder hjk]
    · linarith [(ht k).2, (ht j).1]

-- @node: orderedVertexShift_upper
/-- If [all coordinates lie between zero and one](hyp:ht) and
[the coordinates are nonincreasing](hyp:horder), then
[every coordinate shifted about a vertex is at most the entry at that vertex
index in the vector with a trailing zero](goal). -/
lemma orderedVertexShift_upper {d : ℕ} (t : Fin d → ℝ)
    (ht : ∀ j, t j ∈ Set.Icc 0 1) (horder : Antitone t)
    (i : Fin (d + 1)) (j : Fin d) :
    orderedVertexShift t i j ≤ Fin.snoc (α := fun _ => ℝ) t 0 i := by
  by_cases hi : i = Fin.last d
  · subst i
    simp only [orderedVertexShift, Fin.val_last, j.isLt, if_true, Fin.snoc_last]
    linarith [(ht j).2]
  · obtain ⟨k, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
    simp only [Fin.snoc_castSucc, orderedVertexShift, Fin.val_castSucc]
    split_ifs with hj
    · linarith [(ht j).2, (ht k).1]
    · simpa only [sub_zero] using horder (show k ≤ j by omega)

-- @node: orderedVertexShift_lower_attained
/-- For any coordinate vector and vertex index, [some entry of the shifted
vector augmented by a leading zero equals the entry at that vertex index
in the original vector with a leading one, minus one](goal). -/
lemma orderedVertexShift_lower_attained {d : ℕ} (t : Fin d → ℝ)
    (i : Fin (d + 1)) :
    ∃ a, Fin.cons (α := fun _ => ℝ) 0 (orderedVertexShift t i) a = Fin.cons (α := fun _ => ℝ) 1 t i - 1 := by
  refine Fin.cases ?_ (fun k => ?_) i
  · exact ⟨0, by simp⟩
  · refine ⟨k.succ, ?_⟩
    simp [orderedVertexShift]

-- @node: orderedVertexShift_upper_attained
/-- For any coordinate vector and vertex index, [some entry of the shifted
vector augmented by a leading zero equals the entry at that vertex index
in the original vector with a trailing zero](goal). -/
lemma orderedVertexShift_upper_attained {d : ℕ} (t : Fin d → ℝ)
    (i : Fin (d + 1)) :
    ∃ a, Fin.cons (α := fun _ => ℝ) 0 (orderedVertexShift t i) a = Fin.snoc (α := fun _ => ℝ) t 0 i := by
  by_cases hi : i = Fin.last d
  · subst i; exact ⟨0, by simp⟩
  · obtain ⟨k, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
    exact ⟨k.succ, by simp [orderedVertexShift]⟩

-- @node: structuralHat_min_eq_weight
/-- If [all coordinates lie between zero and one](hyp:ht) and
[the coordinates are nonincreasing](hyp:horder), then [the minimum affine hat
term after shifting about a simplex vertex equals that vertex's barycentric weight](goal). -/
lemma structuralHat_min_eq_weight {d : ℕ} (t : Fin d → ℝ)
    (ht : ∀ j, t j ∈ Set.Icc 0 1) (horder : Antitone t)
    (i : Fin (d + 1)) :
    Finset.univ.inf' Finset.univ_nonempty (structuralHatTerm (orderedVertexShift t i)) =
      orderedSimplexWeights t i := by
  have hl : ∀ a, Fin.cons (α := fun _ => ℝ) 1 t i - 1 ≤ Fin.cons (α := fun _ => ℝ) 0 (orderedVertexShift t i) a := by
    intro a
    refine Fin.cases (by simpa using orderedVertexShift_lower_nonpos t ht i)
      (fun j => ?_) a
    exact orderedVertexShift_lower t ht horder i j
  have hu : ∀ a, Fin.cons (α := fun _ => ℝ) 0 (orderedVertexShift t i) a ≤ Fin.snoc (α := fun _ => ℝ) t 0 i := by
    intro a
    refine Fin.cases (by simpa using orderedVertexShift_upper_nonneg t ht i)
      (fun j => ?_) a
    exact orderedVertexShift_upper t ht horder i j
  rw [structuralHat_min_of_extrema _ _ _ hl hu
    (orderedVertexShift_lower_attained t i) (orderedVertexShift_upper_attained t i)]
  dsimp only [orderedSimplexWeights]
  ring

-- @node: structuralNodalHat_eq_weight
/-- If [all coordinates lie between zero and one](hyp:ht) and
[the coordinates are nonincreasing](hyp:horder), then [the nodal hat evaluated
at the vector shifted about a simplex vertex equals that vertex's barycentric weight](goal). -/
lemma structuralNodalHat_eq_weight {d : ℕ} (t : Fin d → ℝ)
    (ht : ∀ j, t j ∈ Set.Icc 0 1) (horder : Antitone t)
    (i : Fin (d + 1)) :
    structuralNodalHat (orderedVertexShift t i) = orderedSimplexWeights t i := by
  rw [structuralNodalHat, structuralHat_min_eq_weight t ht horder i,
    max_eq_right (orderedSimplexWeights_nonneg t ht horder i)]

-- @node: structuralNodalHat_permute
/-- [Permuting the coordinates of any vector leaves its structural nodal hat unchanged](goal). -/
lemma structuralNodalHat_permute {d : ℕ} (z : Fin d → ℝ)
    (p : Equiv.Perm (Fin d)) :
    structuralNodalHat (fun j => z (p j)) = structuralNodalHat z := by
  let e : Fin (d + 1) → Fin (d + 1) :=
    Fin.cases 0 (fun j => (p j).succ)
  have he : Function.Surjective e := by
    intro a
    refine Fin.cases ⟨0, rfl⟩ (fun j => ?_) a
    exact ⟨(p.symm j).succ, by simp [e]⟩
  have hc (a) : Fin.cons (α := fun _ => ℝ) 0 (fun j => z (p j)) a =
      Fin.cons (α := fun _ => ℝ) 0 z (e a) := by
    refine Fin.cases rfl (fun j => rfl) a
  have hm : Finset.univ.inf' Finset.univ_nonempty
      (structuralHatTerm (fun j => z (p j))) =
      Finset.univ.inf' Finset.univ_nonempty (structuralHatTerm z) := by
    apply le_antisymm
    · apply Finset.le_inf'
      rintro ⟨a, b⟩ _
      obtain ⟨a', rfl⟩ := he a
      obtain ⟨b', rfl⟩ := he b
      have h := Finset.inf'_le
        (structuralHatTerm (fun j => z (p j))) (Finset.mem_univ (a', b'))
      simpa only [structuralHatTerm, hc] using h
    · apply Finset.le_inf'
      rintro ⟨a, b⟩ _
      have h := Finset.inf'_le (structuralHatTerm z) (Finset.mem_univ (e a, e b))
      simpa only [structuralHatTerm, hc] using h
  exact congrArg (max 0) hm

-- @node: structuralNodalHat_kuhnVertex
/-- If [a point belongs to the unit cube](hyp:hx) and [its coordinates in the
chosen permutation are nonincreasing](hyp:horder), then [the nodal hat centered
at any vertex of that permuted Kuhn simplex equals the corresponding barycentric weight](goal). -/
lemma structuralNodalHat_kuhnVertex {d : ℕ} (p : Equiv.Perm (Fin d))
    {x : L1Vec d} (hx : x ∈ unitCube d)
    (horder : Antitone (fun j => x.ofLp (p j))) (i : Fin (d + 1)) :
    structuralNodalHat (x - kuhnVertex p i).ofLp =
      orderedSimplexWeights (fun j => x.ofLp (p j)) i := by
  rw [← structuralNodalHat_permute _ p]
  have he : (fun j => (x - kuhnVertex p i).ofLp (p j)) =
      orderedVertexShift (fun j => x.ofLp (p j)) i := by
    funext j
    simp [kuhnVertex, orderedVertexShift]
  rw [he]
  exact structuralNodalHat_eq_weight _ (fun j => hx (p j)) horder i

-- @node: structuralNodalHat_kuhn_sum
/-- If [a point belongs to the unit cube](hyp:hx) and [its coordinates in the
chosen permutation are nonincreasing](hyp:horder), then [the nodal hats centered
at the vertices of that Kuhn simplex sum to one at the point](goal). -/
lemma structuralNodalHat_kuhn_sum {d : ℕ} (p : Equiv.Perm (Fin d))
    {x : L1Vec d} (hx : x ∈ unitCube d)
    (horder : Antitone (fun j => x.ofLp (p j))) :
    ∑ i, structuralNodalHat (x - kuhnVertex p i).ofLp = 1 := by
  simp_rw [structuralNodalHat_kuhnVertex p hx horder]
  exact orderedSimplexWeights_sum _

-- @node: kuhnInterpolant_eq_nodal_sum
/-- If [a point belongs to the unit cube](hyp:hx) and [its coordinates in the
chosen permutation are nonincreasing](hyp:horder), then [the Kuhn interpolant
there is the sum of the sampled vertex values weighted by the nodal hats
centered at those vertices](goal). -/
lemma kuhnInterpolant_eq_nodal_sum {d k : ℕ} (f : L1Vec d → L1Vec k)
    (p : Equiv.Perm (Fin d)) {x : L1Vec d} (hx : x ∈ unitCube d)
    (horder : Antitone (fun j => x.ofLp (p j))) :
    kuhnInterpolant f p x =
      ∑ i, structuralNodalHat (x - kuhnVertex p i).ofLp • f (kuhnVertex p i) := by
  simp_rw [structuralNodalHat_kuhnVertex p hx horder]
  exact orderedSimplexInterpolant_eq_sum _ _

-- @node: structuralNodalHat_nonneg
/-- [The structural nodal hat is nonnegative at every coordinate vector](goal). -/
lemma structuralNodalHat_nonneg {d : ℕ} (z : Fin d → ℝ) :
    0 ≤ structuralNodalHat z := le_max_left _ _

-- @node: structuralNodalHat_le_one
/-- [The structural nodal hat is at most one at every coordinate vector](goal). -/
lemma structuralNodalHat_le_one {d : ℕ} (z : Fin d → ℝ) :
    structuralNodalHat z ≤ 1 := by
  apply max_le (by norm_num)
  exact (Finset.inf'_le (structuralHatTerm z)
    (Finset.mem_univ (0, 0))).trans_eq (by simp [structuralHatTerm])

-- @node: structuralNodalHat_eq_zero_of_separated
/-- If [one selected coordinate of the vector augmented by a leading zero
exceeds another by at least one](hyp:hab), then [the structural nodal hat of
the vector is zero](goal). -/
lemma structuralNodalHat_eq_zero_of_separated {d : ℕ} (z : Fin d → ℝ)
    (a b : Fin (d + 1))
    (hab : 1 + Fin.cons (α := fun _ => ℝ) 0 z a ≤
      Fin.cons (α := fun _ => ℝ) 0 z b) :
    structuralNodalHat z = 0 := by
  apply le_antisymm _ (structuralNodalHat_nonneg z)
  apply max_le le_rfl
  exact (Finset.inf'_le (structuralHatTerm z)
    (Finset.mem_univ (a, b))).trans (sub_nonpos.mpr hab)

-- @node: structuralHatTerm_pos_of_hat_pos
/-- If [the structural nodal hat of a vector is positive](hyp:hz), then
[the affine hat term for any pair of augmented coordinate indices is positive](goal). -/
lemma structuralHatTerm_pos_of_hat_pos {d : ℕ} (z : Fin d → ℝ)
    (hz : 0 < structuralNodalHat z) (a b : Fin (d + 1)) :
    0 < structuralHatTerm z (a, b) := by
  have hm : 0 < Finset.univ.inf' Finset.univ_nonempty (structuralHatTerm z) := by
    exact (lt_max_iff.mp hz).resolve_left (lt_irrefl _)
  exact hm.trans_le (Finset.inf'_le _ (Finset.mem_univ (a, b)))

-- @node: structuralNodalHat_coordinate_bounds
/-- If [the structural nodal hat of a vector is positive](hyp:hz), then
[each coordinate is strictly greater than minus one and strictly less than one](goal). -/
lemma structuralNodalHat_coordinate_bounds {d : ℕ} (z : Fin d → ℝ)
    (hz : 0 < structuralNodalHat z) (j : Fin d) : -1 < z j ∧ z j < 1 := by
  have hlo := structuralHatTerm_pos_of_hat_pos z hz j.succ 0
  have hhi := structuralHatTerm_pos_of_hat_pos z hz 0 j.succ
  simp only [structuralHatTerm, Fin.cons_succ, Fin.cons_zero] at hlo hhi
  constructor <;> linarith

-- @node: structural_binary_antitone_prefix
/-- If [every entry of an integer vector is zero or one](hyp:hw) and
[the entries are nonincreasing](hyp:horder), then [there is a cutoff index
such that the entries before it are one and all remaining entries are zero](goal). -/
lemma structural_binary_antitone_prefix {d : ℕ} (w : Fin d → ℤ)
    (hw : ∀ j, w j = 0 ∨ w j = 1) (horder : Antitone w) :
    ∃ i : Fin (d + 1), ∀ j, w j = if j.val < i.val then 1 else 0 := by
  induction d with
  | zero => exact ⟨0, fun j => Fin.elim0 j⟩
  | succ d ih =>
    rcases hw 0 with hzero | hone
    · refine ⟨0, ?_⟩
      intro j
      have hj := horder (show (0 : Fin (d + 1)) ≤ j from Fin.zero_le j)
      rcases hw j with h | h
      · simpa using h
      · rw [hzero, h] at hj
        omega
    · obtain ⟨i, hi⟩ := ih (fun j => w j.succ) (fun j => hw j.succ)
        (fun a b hab => horder (Fin.succ_le_succ_iff.mpr hab))
      refine ⟨i.succ, ?_⟩
      intro j
      refine Fin.cases (by simpa using hone) (fun k => ?_) j
      simpa using hi k

-- @node: structuralNodalHat_integer_binary
/-- If [all coordinates of a point lie between zero and one](hyp:ht) and
[the nodal hat centered at an integer vector is positive at that point](hyp:hpos),
then [every coordinate of the integer vector is zero or one](goal). -/
lemma structuralNodalHat_integer_binary {d : ℕ} (t : Fin d → ℝ)
    (ht : ∀ j, t j ∈ Set.Icc 0 1) (w : Fin d → ℤ)
    (hpos : 0 < structuralNodalHat (fun j => t j - w j)) :
    ∀ j, w j = 0 ∨ w j = 1 := by
  intro j
  have hb := structuralNodalHat_coordinate_bounds _ hpos j
  have hlo : (-1 : ℝ) < (w j : ℝ) := by linarith [(ht j).1]
  have hhi : (w j : ℝ) < 2 := by linarith [(ht j).2]
  have hlo' : (-1 : ℤ) < w j := by exact_mod_cast hlo
  have hhi' : w j < (2 : ℤ) := by exact_mod_cast hhi
  omega

-- @node: structuralNodalHat_integer_antitone
/-- If [all coordinates of a point lie between zero and one](hyp:ht),
[those coordinates are nonincreasing](hyp:horder), and [the nodal hat centered
at an integer vector is positive at the point](hyp:hpos), then [the integer
vector also has nonincreasing coordinates](goal). -/
lemma structuralNodalHat_integer_antitone {d : ℕ} (t : Fin d → ℝ)
    (ht : ∀ j, t j ∈ Set.Icc 0 1) (horder : Antitone t) (w : Fin d → ℤ)
    (hpos : 0 < structuralNodalHat (fun j => t j - w j)) : Antitone w := by
  have hw := structuralNodalHat_integer_binary t ht w hpos
  intro a b hab
  rcases hw a with ha | ha <;> rcases hw b with hb | hb
  · omega
  · have ht' := horder hab
    have hterm := structuralHatTerm_pos_of_hat_pos _ hpos b.succ a.succ
    simp only [structuralHatTerm, Fin.cons_succ, ha, hb, Int.cast_zero, Int.cast_one] at hterm
    linarith
  · omega
  · omega

-- @node: structuralNodalHat_integer_support
/-- If [all coordinates of a point lie between zero and one](hyp:ht),
[those coordinates are nonincreasing](hyp:horder), and [the nodal hat centered
at an integer vector is positive at the point](hyp:hpos), then [the integer
vector is one before some cutoff index and zero thereafter](goal). -/
lemma structuralNodalHat_integer_support {d : ℕ} (t : Fin d → ℝ)
    (ht : ∀ j, t j ∈ Set.Icc 0 1) (horder : Antitone t) (w : Fin d → ℤ)
    (hpos : 0 < structuralNodalHat (fun j => t j - w j)) :
    ∃ i : Fin (d + 1), ∀ j, w j = if j.val < i.val then 1 else 0 := by
  exact structural_binary_antitone_prefix w
    (structuralNodalHat_integer_binary t ht w hpos)
    (structuralNodalHat_integer_antitone t ht horder w hpos)

-- @node: structuralGridVertex
/-- Given [a coordinate permutation](hyp:p), [a vertex index along the simplex
chain](hyp:i), and [a coordinate index](hyp:j), the [integer grid vertex
coordinate](goal) is one if the coordinate's position in the permutation
precedes the vertex index, and zero otherwise. -/
def structuralGridVertex {d : ℕ} (p : Equiv.Perm (Fin d))
    (i : Fin (d + 1)) (j : Fin d) : ℤ :=
  if (p.symm j).val < i.val then 1 else 0

-- @node: structuralGridVertex_cast
/-- [Converting any coordinate of an integer grid chain vertex to a real number
gives the same coordinate of the corresponding geometric Kuhn vertex](goal). -/
lemma structuralGridVertex_cast {d : ℕ} (p : Equiv.Perm (Fin d))
    (i : Fin (d + 1)) (j : Fin d) :
    (structuralGridVertex p i j : ℝ) = (kuhnVertex p i).ofLp j := by
  simp [structuralGridVertex, kuhnVertex]

-- @node: structuralGridVertex_injective
/-- For any coordinate permutation, [distinct vertex indices along the simplex
chain give distinct integer grid vectors](goal). -/
lemma structuralGridVertex_injective {d : ℕ} (p : Equiv.Perm (Fin d)) :
    Function.Injective (structuralGridVertex p) := by
  intro i k he
  suffices hi : ∀ i k : Fin (d + 1), i.val < k.val →
      structuralGridVertex p i ≠ structuralGridVertex p k by
    rcases lt_trichotomy i.val k.val with h | h | h
    · exact (hi i k h he).elim
    · exact Fin.ext h
    · exact (hi k i h he.symm).elim
  intro i k hik heq
  let j : Fin d := ⟨i.val, by omega⟩
  have h := congrFun heq (p j)
  simp only [structuralGridVertex, Equiv.symm_apply_apply] at h
  have hi : ¬j.val < i.val := by simp [j]
  have hk : j.val < k.val := hik
  simp only [if_neg hi, if_pos hk] at h
  norm_num at h

-- @node: structuralNodalHat_grid_support
/-- If [a point belongs to the unit cube](hyp:hx), [its coordinates in the
chosen permutation are nonincreasing](hyp:horder), and [the nodal hat centered
at an integer vector is positive there](hyp:hpos), then [that integer vector
is a grid vertex of the chosen Kuhn simplex](goal). -/
lemma structuralNodalHat_grid_support {d : ℕ} (p : Equiv.Perm (Fin d))
    {x : L1Vec d} (hx : x ∈ unitCube d)
    (horder : Antitone (fun j => x.ofLp (p j))) (w : Fin d → ℤ)
    (hpos : 0 < structuralNodalHat (fun j => x.ofLp j - w j)) :
    w ∈ Set.range (structuralGridVertex p) := by
  rw [← structuralNodalHat_permute _ p] at hpos
  obtain ⟨i, hi⟩ := structuralNodalHat_integer_support
    (fun j => x.ofLp (p j)) (fun j => hx (p j)) horder (fun j => w (p j)) hpos
  refine ⟨i, ?_⟩
  funext j
  have h := hi (p.symm j)
  simpa only [Equiv.apply_symm_apply, structuralGridVertex] using h.symm

-- @node: structuralNodalHat_grid_zero
/-- If [a point belongs to the unit cube](hyp:hx), [its coordinates in the
chosen permutation are nonincreasing](hyp:horder), and [an integer vector is
not a grid vertex of that Kuhn simplex](hyp:hw), then [the nodal hat centered
at that integer vector is zero at the point](goal). -/
lemma structuralNodalHat_grid_zero {d : ℕ} (p : Equiv.Perm (Fin d))
    {x : L1Vec d} (hx : x ∈ unitCube d)
    (horder : Antitone (fun j => x.ofLp (p j))) (w : Fin d → ℤ)
    (hw : w ∉ Set.range (structuralGridVertex p)) :
    structuralNodalHat (fun j => x.ofLp j - w j) = 0 := by
  apply le_antisymm _ (structuralNodalHat_nonneg _)
  exact le_of_not_gt (fun h => hw (structuralNodalHat_grid_support p hx horder w h))


-- @node: structuralGridPoint
/-- For [an integer coordinate vector](hyp:w), the [structural grid point](goal)
is the same vector with real coordinates, viewed in the space with the sum-of-absolute-values norm. -/
def structuralGridPoint {d : ℕ} (w : Fin d → ℤ) : L1Vec d :=
  WithLp.toLp 1 (fun j => (w j : ℝ))

-- @node: structuralGridPoint_vertex
/-- [Embedding any integer grid chain vertex into the real coordinate space
gives the corresponding geometric Kuhn vertex](goal). -/
lemma structuralGridPoint_vertex {d : ℕ} (p : Equiv.Perm (Fin d))
    (i : Fin (d + 1)) :
    structuralGridPoint (structuralGridVertex p i) = kuhnVertex p i := by
  apply PiLp.ext
  intro j
  exact structuralGridVertex_cast p i j

-- @node: structuralGridInterpolant
/-- Given [a finite set of integer grid vectors](hyp:s), [a vector-valued
function to sample](hyp:f), and [an evaluation point](hyp:x), the [structural
grid interpolant](goal) sums the function's values at those grid points,
each weighted by the nodal hat centered there and evaluated at the evaluation point. -/
def structuralGridInterpolant {d k : ℕ} (s : Finset (Fin d → ℤ))
    (f : L1Vec d → L1Vec k) (x : L1Vec d) : L1Vec k :=
  ∑ w ∈ s, structuralNodalHat (fun j => x.ofLp j - w j) • f (structuralGridPoint w)

-- @node: structuralGridInterpolant_eq_kuhn
/-- If [the finite grid contains every vertex of the chosen Kuhn simplex](hyp:hs),
[the evaluation point belongs to the unit cube](hyp:hx), and [its coordinates
in the chosen permutation are nonincreasing](hyp:horder), then [the structural
grid interpolant equals the Kuhn interpolant at that point](goal). -/
lemma structuralGridInterpolant_eq_kuhn {d k : ℕ} (s : Finset (Fin d → ℤ))
    (f : L1Vec d → L1Vec k) (p : Equiv.Perm (Fin d))
    (hs : ∀ i, structuralGridVertex p i ∈ s)
    {x : L1Vec d} (hx : x ∈ unitCube d)
    (horder : Antitone (fun j => x.ofLp (p j))) :
    structuralGridInterpolant s f x = kuhnInterpolant f p x := by
  classical
  let chain := Finset.univ.image (structuralGridVertex p)
  have hsub : chain ⊆ s := by
    intro w hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
    exact hs i
  have hout (w) (_hw : w ∈ s) (hw : w ∉ chain) :
      structuralNodalHat (fun j => x.ofLp j - w j) • f (structuralGridPoint w) = 0 := by
    have hn : w ∉ Set.range (structuralGridVertex p) := by
      rintro ⟨i, rfl⟩
      exact hw (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    rw [structuralNodalHat_grid_zero p hx horder w hn, zero_smul]
  unfold structuralGridInterpolant
  rw [← Finset.sum_subset hsub hout]
  rw [Finset.sum_image (fun i _ j _ hij => structuralGridVertex_injective p hij)]
  simp only [structuralGridPoint_vertex]
  rw [kuhnInterpolant_eq_nodal_sum f p hx horder]
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  funext j
  rw [structuralGridVertex_cast]
  rfl

-- @node: cellKuhnInterpolant_eq_grid_sum
/-- For [a nonnegative cell width](hyp:h), if [the width is positive](hyp:hh),
[the finite grid contains every vertex of the chosen reference simplex](hyp:hs),
[a reference point belongs to the unit cube](hyp:hz), and [its coordinates in
the chosen permutation are nonincreasing](hyp:horder), then [the physical-cell
Kuhn interpolant at the mapped point equals the structural grid interpolant
of the function composed with the cell map at the reference point](goal). -/
lemma cellKuhnInterpolant_eq_grid_sum {d k : ℕ} (s : Finset (Fin d → ℤ))
    (f : L1Vec d → L1Vec k) (base : L1Vec d) (h : ℝ≥0) (hh : 0 < h)
    (p : Equiv.Perm (Fin d)) (hs : ∀ i, structuralGridVertex p i ∈ s)
    {z : L1Vec d} (hz : z ∈ unitCube d)
    (horder : Antitone (fun j => z.ofLp (p j))) :
    cellKuhnInterpolant f base h p (structuralCellMap base h z) =
      structuralGridInterpolant s (f ∘ structuralCellMap base h) z := by
  rw [cellKuhnInterpolant, structuralCellNormalize_map base h hh]
  exact (structuralGridInterpolant_eq_kuhn s _ p hs hz horder).symm

-- @node: structuralGridInterpolant_translate
/-- [Evaluating the structural grid interpolant at a point translated by an
integer vector equals evaluating at the original point after subtracting that
vector from every grid index and composing the sampled function with the
same translation](goal). -/
lemma structuralGridInterpolant_translate {d k : ℕ} (s : Finset (Fin d → ℤ))
    (f : L1Vec d → L1Vec k) (v : Fin d → ℤ) (x : L1Vec d) :
    structuralGridInterpolant s f (structuralGridPoint v + x) =
      structuralGridInterpolant (s.image (fun w => w - v))
        (fun y => f (structuralGridPoint v + y)) x := by
  classical
  unfold structuralGridInterpolant
  rw [Finset.sum_image (fun a _ b _ hab => by
    simpa only [sub_add_cancel] using congrArg (fun w => w + v) hab)]
  apply Finset.sum_congr rfl
  intro w _
  have hpoint : structuralGridPoint v + structuralGridPoint (w - v) =
      structuralGridPoint w := by
    apply PiLp.ext
    intro j
    simp [structuralGridPoint]
  dsimp only
  rw [hpoint]
  congr 2
  funext j
  simp only [PiLp.add_apply, structuralGridPoint, Pi.sub_apply,
    Int.cast_sub]
  ring

-- @node: structuralGridInterpolant_cell
/-- If [the finite grid contains all vertices of the simplex translated by an
integer vector](hyp:hs), [a local point belongs to the unit cube](hyp:hx), and
[its coordinates in the chosen permutation are nonincreasing](hyp:horder),
then [the structural grid interpolant at the translated point equals the Kuhn
interpolant at the local point of the function composed with that translation](goal). -/
lemma structuralGridInterpolant_cell {d k : ℕ} (s : Finset (Fin d → ℤ))
    (f : L1Vec d → L1Vec k) (v : Fin d → ℤ) (p : Equiv.Perm (Fin d))
    (hs : ∀ i, v + structuralGridVertex p i ∈ s)
    {x : L1Vec d} (hx : x ∈ unitCube d)
    (horder : Antitone (fun j => x.ofLp (p j))) :
    structuralGridInterpolant s f (structuralGridPoint v + x) =
      kuhnInterpolant (fun y => f (structuralGridPoint v + y)) p x := by
  classical
  rw [structuralGridInterpolant_translate]
  apply structuralGridInterpolant_eq_kuhn _ _ p _ hx horder
  intro i
  exact Finset.mem_image.mpr ⟨v + structuralGridVertex p i, hs i,
    add_sub_cancel_left v (structuralGridVertex p i)⟩

-- @node: structuralNodalHat_continuous
/-- [The structural nodal hat is continuous on the whole coordinate space](goal). -/
@[fun_prop] lemma structuralNodalHat_continuous {d : ℕ} :
    Continuous (structuralNodalHat (d := d)) := by
  unfold structuralNodalHat structuralHatTerm
  fun_prop

-- @node: structuralGridInterpolant_continuous
/-- For any finite set of grid points and any function sampled there,
[the structural grid interpolant is continuous as a function of its evaluation point](goal). -/
@[fun_prop] lemma structuralGridInterpolant_continuous {d k : ℕ}
    (s : Finset (Fin d → ℤ)) (f : L1Vec d → L1Vec k) :
    Continuous (structuralGridInterpolant s f) := by
  unfold structuralGridInterpolant
  fun_prop

-- @node: kuhnInterpolant_grid_face_agreement
/-- If [the finite grid contains every translated vertex of the first simplex](hyp:hv)
and [of the second simplex](hyp:hw), [the first local point lies in the unit cube](hyp:hx)
and [so does the second](hyp:hy), [the first point's coordinates are nonincreasing
in the first permutation](hyp:hp) and [the second point's coordinates are
nonincreasing in the second permutation](hyp:hq), and [the two translated
local points coincide](hyp:he), then [the two local Kuhn interpolants of the
correspondingly translated sampled function have equal values at these points](goal). -/
lemma kuhnInterpolant_grid_face_agreement {d k : ℕ} (s : Finset (Fin d → ℤ))
    (f : L1Vec d → L1Vec k) (v w : Fin d → ℤ) (p q : Equiv.Perm (Fin d))
    (hv : ∀ i, v + structuralGridVertex p i ∈ s)
    (hw : ∀ i, w + structuralGridVertex q i ∈ s)
    {x y : L1Vec d} (hx : x ∈ unitCube d) (hy : y ∈ unitCube d)
    (hp : Antitone (fun j => x.ofLp (p j)))
    (hq : Antitone (fun j => y.ofLp (q j)))
    (he : structuralGridPoint v + x = structuralGridPoint w + y) :
    kuhnInterpolant (fun z => f (structuralGridPoint v + z)) p x =
      kuhnInterpolant (fun z => f (structuralGridPoint w + z)) q y := by
  rw [← structuralGridInterpolant_cell s f v p hv hx hp, he,
    structuralGridInterpolant_cell s f w q hw hy hq]

end
end Papers.TbsNeuralCausalPi
