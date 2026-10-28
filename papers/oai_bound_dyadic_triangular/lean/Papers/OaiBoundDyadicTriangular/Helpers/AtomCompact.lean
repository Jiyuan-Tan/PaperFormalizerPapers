module

public import Papers.OaiBoundDyadicTriangular.Helpers.DyadicChildren
public import Papers.OaiBoundDyadicTriangular.Helpers.AtomEnergy

/-! # Finiteness of the atom energies for compactly supported inputs -/

public section

open MeasureTheory
open scoped BigOperators

namespace Papers.OaiBoundDyadicTriangular

-- @node: atomIndex_ge_interval_index
/-- For any parent and atom scales, interval triple, vertex, and atom at that vertex,
[the global atom index is at least the vertex's interval index](goal). -/
lemma atomIndex_ge_interval_index (k m : ℤ) (n : Fin 3 → ℕ)
    (v : Fin 3) (i : Atom k m) : n v ≤ atomIndex k m n v i := by
  have hp : 1 ≤ 2 ^ (k - m).toNat := Nat.one_le_pow _ _ (by decide)
  dsimp [atomIndex]
  nlinarith

-- @node: weightedEdge_hasFiniteSupport
/-- If [each of the three input functions vanishes outside a bounded square in the
nonnegative quadrant](hyp:hCompact), then, at any parent and atom scales and any
vertex, [the weighted edge matrix is nonzero for only finitely many admissible
interval triples](goal). -/
lemma weightedEdge_hasFiniteSupport (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (hCompact : StepCompact F) (v : Fin 3) :
    Function.HasFiniteSupport (fun n : admissibleSet => weightedEdge F k m n.val v) := by
  classical
  obtain ⟨R, hR⟩ := hCompact v
  obtain ⟨N, hN⟩ := exists_nat_gt (R / (2 : ℝ) ^ m)
  have hp : 0 < (2 : ℝ) ^ m := by positivity
  have hRN : R < (2 : ℝ) ^ m * N := by
    simpa only [mul_comm] using (div_lt_iff₀ hp).mp hN
  have hz (n : admissibleSet) (hn : N < n.val v ∨ N < n.val (v + 1)) :
      weightedEdge F k m n.val v = 0 := by
    ext i j
    have hx : 0 ≤ (2 : ℝ) ^ m * atomIndex k m n.val v i := by positivity
    have hy : 0 ≤ (2 : ℝ) ^ m * atomIndex k m n.val (v + 1) j := by positivity
    have hl (w : Fin 3) (a : Atom k m) (hw : N < n.val w) :
        R < (2 : ℝ) ^ m * atomIndex k m n.val w a := by
      have hna : N < atomIndex k m n.val w a :=
        hw.trans_le (atomIndex_ge_interval_index k m n.val w a)
      exact hRN.trans (mul_lt_mul_of_pos_left (by exact_mod_cast hna) hp)
    have hf : F v ((2 : ℝ) ^ m * atomIndex k m n.val v i,
        (2 : ℝ) ^ m * atomIndex k m n.val (v + 1) j) = 0 := by
      apply hR _ hx hy
      exact hn.elim (fun h => Or.inl (hl v i h)) (fun h => Or.inr (hl (v + 1) j h))
    simp only [weightedEdge, atomValue, nextVertex, hf, mul_zero, Matrix.zero_apply]
  have hfinite : {n : admissibleSet | n.val v ≤ N ∧ n.val (v + 1) ≤ N}.Finite :=
    ((Set.finite_Iic N).prod (Set.finite_Iic N)).preimage
      (admissible_edge_pair_injective v).injOn
  apply hfinite.subset
  intro n hn
  change weightedEdge F k m n.val v ≠ 0 at hn
  change n.val v ≤ N ∧ n.val (v + 1) ≤ N
  by_contra h
  exact hn (hz n (by omega))

-- @node: matrixEnergy_zero
/-- [The three-halves trace energy of a finite zero matrix is zero](goal). -/
lemma matrixEnergy_zero {ι : Type*} [Fintype ι] [DecidableEq ι] :
    matrixEnergy (0 : Matrix ι ι ℝ) = 0 := by
  simp [matrixEnergy]

-- @node: vertexEnergy_hasFiniteSupport
/-- If [each of the three input functions vanishes outside a bounded square in the
nonnegative quadrant](hyp:hCompact), then, at any parent and atom scales and any
vertex, [the vertex energy is nonzero for only finitely many admissible interval
triples](goal). -/
lemma vertexEnergy_hasFiniteSupport (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (hCompact : StepCompact F) (v : Fin 3) :
    Function.HasFiniteSupport (fun n : admissibleSet => vertexEnergy F k m n.val v) := by
  classical
  apply ((weightedEdge_hasFiniteSupport F k m hCompact v).union
    (weightedEdge_hasFiniteSupport F k m hCompact (v + 2))).subset
  intro n hn
  by_contra h
  simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
  have hz : vertexEnergy F k m n.val v = 0 := by
    simp [vertexEnergy, atomRowStar, rowStar, rowGram, h.1, h.2, matrixEnergy_zero]
  exact hn hz

-- @node: localEnergy_summable
/-- If [each of the three input functions vanishes outside a bounded square in the
nonnegative quadrant](hyp:hCompact), then, at any parent and atom scales,
[the local energies form a summable family over admissible interval triples](goal). -/
lemma localEnergy_summable (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (hCompact : StepCompact F) :
    Summable (fun n : admissibleSet => localEnergy F k m n.val) := by
  apply summable_sum
  intro v _
  exact summable_of_hasFiniteSupport (vertexEnergy_hasFiniteSupport F k m hCompact v)

end Papers.OaiBoundDyadicTriangular
