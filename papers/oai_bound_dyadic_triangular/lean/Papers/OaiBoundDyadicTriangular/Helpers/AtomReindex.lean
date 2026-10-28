module

public import Papers.OaiBoundDyadicTriangular.Helpers.AtomCompact
public import Papers.OaiBoundDyadicTriangular.Helpers.AtomMass

/-! # Reindexing edge masses by the scale-m grid -/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Papers.OaiBoundDyadicTriangular

-- @node: admissible_edge_pair_surjective
/-- [Every pair of nonnegative integer indices occurs at a chosen vertex and its
cyclic successor in some interval triple whose three indices have bitwise XOR zero](goal). -/
lemma admissible_edge_pair_surjective (v : Fin 3) :
    Function.Surjective (fun n : admissibleSet => (n.val v, n.val (v + 1))) := by
  rintro ⟨a, b⟩
  fin_cases v
  · refine ⟨⟨![a, b, a ^^^ b], ?_⟩, rfl⟩
    simp [admissibleSet, IsAdmissible, xor3]
  · refine ⟨⟨![a ^^^ b, a, b], ?_⟩, rfl⟩
    simp [admissibleSet, IsAdmissible, xor3, Nat.xor_assoc]
  · refine ⟨⟨![b, a ^^^ b, a], ?_⟩, rfl⟩
    simp [admissibleSet, IsAdmissible, xor3, Nat.xor_left_comm]

-- @node: admissibleEdgeEquiv
/-- For [a chosen vertex of the triangle](hyp:v), the [edge-index bijection](goal)
identifies interval triples whose indices have bitwise XOR zero with pairs of
nonnegative integers, by retaining the indices at that vertex and its cyclic successor. -/
noncomputable def admissibleEdgeEquiv (v : Fin 3) : admissibleSet ≃ ℕ × ℕ :=
  Equiv.ofBijective (fun n => (n.val v, n.val (v + 1)))
    ⟨admissible_edge_pair_injective v, admissible_edge_pair_surjective v⟩

-- @node: tsum_admissible_edge_pair
/-- [Summing a real function of the two edge indices over all triples with bitwise
XOR zero gives the same infinite sum as summing over all pairs of nonnegative integers](goal). -/
lemma tsum_admissible_edge_pair (v : Fin 3) (g : ℕ × ℕ → ℝ) :
    (∑' n : admissibleSet, g (n.val v, n.val (v + 1))) = ∑' p, g p := by
  exact (admissibleEdgeEquiv v).tsum_eq g

-- @node: atomGridEquiv
/-- For [a parent scale and an atom scale](hyp:k,m), the [atom-grid bijection](goal)
identifies a pair of nonnegative block indices together with two atom indices with
a pair of nonnegative grid indices, by multiplying each block index by the number
of atoms and adding its atom index. -/
noncomputable def atomGridEquiv (k m : ℤ) :
    ((ℕ × ℕ) × (Atom k m × Atom k m)) ≃ ℕ × ℕ :=
  (Equiv.prodProdProdComm ℕ ℕ (Atom k m) (Atom k m)).trans
    (Equiv.prodCongr (Nat.divModEquiv (2 ^ (k - m).toNat)).symm
      (Nat.divModEquiv (2 ^ (k - m).toNat)).symm)

-- @node: tsum_atom_blocks
/-- If [a real function on pairs of nonnegative integers is summable](hyp:hg),
[its infinite sum is unchanged by grouping the grid into square blocks of side
length equal to the number of atoms and summing within each block first](goal). -/
lemma tsum_atom_blocks (k m : ℤ) (g : ℕ × ℕ → ℝ) (hg : Summable g) :
    (∑' p : ℕ × ℕ, ∑ i : Atom k m, ∑ j : Atom k m,
      g (2 ^ (k - m).toNat * p.1 + i.val,
        2 ^ (k - m).toNat * p.2 + j.val)) = ∑' p, g p := by
  have hs : Summable (fun p => g (atomGridEquiv k m p)) :=
    (atomGridEquiv k m).summable_iff.mpr hg
  calc
    _ = ∑' p : (ℕ × ℕ) × (Atom k m × Atom k m), g (atomGridEquiv k m p) := by
      rw [hs.tsum_prod]
      apply tsum_congr
      intro p
      rw [tsum_fintype]
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change g (_, _) = g (p.1 * 2 ^ (k - m).toNat + i.val,
        p.2 * 2 ^ (k - m).toNat + j.val)
      simp only [Nat.mul_comm]
    _ = _ := (atomGridEquiv k m).tsum_eq g

-- @node: step_grid_cubes_hasFiniteSupport
/-- If [each input vanishes outside a bounded square in the nonnegative quadrant](hyp:hCompact),
[the absolute cubes of a chosen input sampled on the nonnegative dyadic grid
are nonzero at only finitely many grid points](goal). -/
lemma step_grid_cubes_hasFiniteSupport (F : Fin 3 → ℝ × ℝ → ℝ) (m : ℤ)
    (hCompact : StepCompact F) (v : Fin 3) :
    Function.HasFiniteSupport (fun p : ℕ × ℕ =>
      |F v ((2 : ℝ) ^ m * p.1, (2 : ℝ) ^ m * p.2)| ^ 3) := by
  obtain ⟨R, hR⟩ := hCompact v
  obtain ⟨N, hN⟩ := exists_nat_gt (R / (2 : ℝ) ^ m)
  have hp : 0 < (2 : ℝ) ^ m := by positivity
  have hRN : R < (2 : ℝ) ^ m * N := by
    simpa only [mul_comm] using (div_lt_iff₀ hp).mp hN
  apply ((Set.finite_Iic N).prod (Set.finite_Iic N)).subset
  intro p hn
  change p.1 ≤ N ∧ p.2 ≤ N
  by_contra h
  have hf : F v ((2 : ℝ) ^ m * p.1, (2 : ℝ) ^ m * p.2) = 0 := by
    apply hR _ (by positivity) (by positivity)
    have hl (a : ℕ) (ha : N < a) : R < (2 : ℝ) ^ m * a :=
      hRN.trans (mul_lt_mul_of_pos_left (by exact_mod_cast ha) hp)
    rcases (show N < p.1 ∨ N < p.2 by omega) with h | h
    · exact Or.inl (hl _ h)
    · exact Or.inr (hl _ h)
  exact hn (by simp [hf])

-- @node: atomCubeMass_tsum_eq_grid
/-- If [each input vanishes outside a bounded square in the nonnegative quadrant](hyp:hCompact),
[the sum of a chosen edge's normalized cubic masses over all interval triples with
bitwise XOR zero equals the squared atom weight times the sum of absolute cubes
of that input over the nonnegative atom-scale grid](goal). -/
lemma atomCubeMass_tsum_eq_grid (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (hCompact : StepCompact F) (v : Fin 3) :
    (∑' n : admissibleSet, atomCubeMass F k m n.val v) =
      (atomWeight k m * atomWeight k m) *
        ∑' p : ℕ × ℕ, |F v ((2 : ℝ) ^ m * p.1, (2 : ℝ) ^ m * p.2)| ^ 3 := by
  simp only [atomCubeMass, atomValue, atomIndex, nextVertex,
    ← Finset.mul_sum, tsum_mul_left]
  rw [tsum_admissible_edge_pair v (fun p => ∑ i : Atom k m, ∑ j : Atom k m,
    |F v ((2 : ℝ) ^ m * ((2 ^ (k - m).toNat * p.1 + i.val : ℕ) : ℝ),
      (2 : ℝ) ^ m * ((2 ^ (k - m).toNat * p.2 + j.val : ℕ) : ℝ))| ^ 3)]
  rw [tsum_atom_blocks k m _
    (summable_of_hasFiniteSupport (step_grid_cubes_hasFiniteSupport F m hCompact v))]

-- @node: gridCubeMass
/-- For [three input functions](hyp:F), [an integer grid scale](hyp:m), and
[a chosen edge](hyp:v), the [grid cubic mass](goal) is the sum of the absolute
cubes of that input at nonnegative grid points of spacing two to the grid scale,
multiplied by the grid-cell area. -/
noncomputable def gridCubeMass (F : Fin 3 → ℝ × ℝ → ℝ) (m : ℤ) (v : Fin 3) : ℝ :=
  (2 : ℝ) ^ (2 * m) *
    ∑' p : ℕ × ℕ, |F v ((2 : ℝ) ^ m * p.1, (2 : ℝ) ^ m * p.2)| ^ 3

-- @node: weighted_atomCubeMass_tsum_eq_gridCubeMass
/-- If [each input vanishes outside a bounded square in the nonnegative quadrant](hyp:hCompact),
[the sum of a chosen edge's normalized cubic masses over all interval triples with
bitwise XOR zero, each multiplied by two to twice the parent scale, equals its
grid cubic mass](goal). -/
lemma weighted_atomCubeMass_tsum_eq_gridCubeMass (F : Fin 3 → ℝ × ℝ → ℝ)
    (k m : ℤ) (hCompact : StepCompact F) (v : Fin 3) :
    (∑' n : admissibleSet, (2 : ℝ) ^ (2 * k) * atomCubeMass F k m n.val v) =
      gridCubeMass F m v := by
  rw [tsum_mul_left, atomCubeMass_tsum_eq_grid F k m hCompact v, ← mul_assoc]
  have hw : (2 : ℝ) ^ (2 * k) * (atomWeight k m * atomWeight k m) =
      (2 : ℝ) ^ (2 * m) := by
    rw [atomWeight, ← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num)]
    congr 1
    ring
  rw [hw]
  rfl

-- @node: atomCubeMass_hasFiniteSupport
/-- If [each input vanishes outside a bounded square in the nonnegative quadrant](hyp:hCompact),
[a chosen edge has nonzero normalized cubic mass for only finitely many interval
triples with bitwise XOR zero](goal). -/
lemma atomCubeMass_hasFiniteSupport (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (hCompact : StepCompact F) (v : Fin 3) :
    Function.HasFiniteSupport (fun n : admissibleSet => atomCubeMass F k m n.val v) := by
  apply (weightedEdge_hasFiniteSupport F k m hCompact v).subset
  intro n hn
  change weightedEdge F k m n.val v ≠ 0
  intro hz
  exact hn (atomCubeMass_eq_zero_of_weightedEdge_eq_zero F k m n.val v hz)

-- @node: weighted_atomCubeMass_sum_eq_gridCubeMass_sum
/-- If [each input vanishes outside a bounded square in the nonnegative quadrant](hyp:hCompact),
[summing the three normalized cubic edge masses over all interval triples with
bitwise XOR zero, with weight two to twice the parent scale, gives the sum of the
three grid cubic masses](goal). -/
lemma weighted_atomCubeMass_sum_eq_gridCubeMass_sum (F : Fin 3 → ℝ × ℝ → ℝ)
    (k m : ℤ) (hCompact : StepCompact F) :
    (∑' n : admissibleSet, (2 : ℝ) ^ (2 * k) *
      ∑ v : Fin 3, atomCubeMass F k m n.val v) = ∑ v : Fin 3, gridCubeMass F m v := by
  simp_rw [Finset.mul_sum]
  rw [Summable.tsum_finsetSum]
  · exact Finset.sum_congr rfl fun v _ =>
      weighted_atomCubeMass_tsum_eq_gridCubeMass F k m hCompact v
  · intro v _
    exact (summable_of_hasFiniteSupport
      (atomCubeMass_hasFiniteSupport F k m hCompact v)).mul_left _

end Papers.OaiBoundDyadicTriangular
