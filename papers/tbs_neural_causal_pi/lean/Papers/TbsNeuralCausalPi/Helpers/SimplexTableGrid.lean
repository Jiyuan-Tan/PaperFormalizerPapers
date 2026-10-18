module
public import Papers.TbsNeuralCausalPi.Setup.Notation
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Tactic
/-! # Finite simplex tables for the simulation sampling argument

Partition the closed simplex into coordinate floor cells and select a simplex
representative in each occupied cell. This preserves normalization even at zero
weights. Unoccupied cells use a fixed simplex point. The finite code space gives
an explicit table count, and the rounding map is measurable.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
noncomputable section
attribute [local instance] Classical.propDecidable

-- @node: simplexCellIndex
/-- For [an integer mesh resolution](hyp:R) and [a probability vector](hyp:p),
the [cell code](goal) records the integer floor of each coordinate multiplied
by the resolution; a coordinate equal to one receives the resolution itself
as its index. -/
def simplexCellIndex {n : ℕ} (R : ℕ) (p : probabilitySimplex n) :
    Fin n → Fin (R + 1) := fun i =>
  ⟨⌊(R : ℝ) * p.val i⌋₊, (Nat.floor_lt (mul_nonneg (Nat.cast_nonneg R) (p.property.1 i))).mpr (by
    have hi := mem_Icc_of_mem_stdSimplex p.property i
    have h := mul_le_mul_of_nonneg_left hi.2 (Nat.cast_nonneg R : (0 : ℝ) ≤ R)
    push_cast
    linarith)⟩

-- @node: simplexCellIndex_measurable
/-- For any integer mesh resolution, [the map assigning a cell code to a
probability vector is measurable](goal). -/
@[fun_prop] lemma simplexCellIndex_measurable {n : ℕ} (R : ℕ) :
    Measurable (simplexCellIndex (n := n) R) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_to_countable'
  intro c
  have h : Measurable (fun p : probabilitySimplex n => ⌊(R : ℝ) * p.val i⌋₊) := by
    have hcoord : Measurable (fun p : probabilitySimplex n => p.val i) :=
      (measurable_pi_apply i).comp measurable_subtype_coe
    exact (hcoord.const_mul (R : ℝ)).nat_floor
  convert h (measurableSet_singleton c.val) using 1
  ext p
  simp [simplexCellIndex, Fin.ext_iff]

-- @node: simplexCellIndex_coordinate_error
/-- If [the integer mesh resolution is positive](hyp:hR) and [two probability
vectors have the same cell code](hyp:h), then [their values at any given
coordinate differ by strictly less than the reciprocal resolution](goal). -/
lemma simplexCellIndex_coordinate_error {n R : ℕ} (hR : 0 < R)
    (p q : probabilitySimplex n) (h : simplexCellIndex R p = simplexCellIndex R q)
    (i : Fin n) : |p.val i - q.val i| < (R : ℝ)⁻¹ := by
  have hp := Nat.floor_le (mul_nonneg (Nat.cast_nonneg R) (p.property.1 i))
  have hq := Nat.floor_le (mul_nonneg (Nat.cast_nonneg R) (q.property.1 i))
  have hp' := Nat.lt_floor_add_one ((R : ℝ) * p.val i)
  have hq' := Nat.lt_floor_add_one ((R : ℝ) * q.val i)
  have he : ⌊(R : ℝ) * p.val i⌋₊ = ⌊(R : ℝ) * q.val i⌋₊ :=
    congrArg Fin.val (congrFun h i)
  rw [he] at hp hp'
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  rw [abs_lt]
  constructor
  · simpa only [one_div, neg_div] using
      (show -(1 : ℝ) / R < p.val i - q.val i from
        (div_lt_iff₀ hRpos).mpr (by nlinarith))
  · rw [inv_eq_one_div, lt_div_iff₀ hRpos]
    nlinarith

-- @node: simplexCellRepresentative
/-- Given [a fallback probability vector](hyp:p0), [an integer mesh
resolution](hyp:R), and [a cell code](hyp:c), the [cell representative](goal)
is an arbitrarily chosen probability vector with that code if one exists,
and otherwise is the fallback vector. -/
def simplexCellRepresentative {n : ℕ} (p0 : probabilitySimplex n) (R : ℕ)
    (c : Fin n → Fin (R + 1)) : probabilitySimplex n :=
  if h : ∃ p : probabilitySimplex n, simplexCellIndex R p = c then
    Classical.choose h else p0

-- @node: simplexCellRepresentative_index
/-- For any fallback probability vector, mesh resolution, and probability
vector, [the representative of that vector's cell has the same cell code
as the vector itself](goal). -/
lemma simplexCellRepresentative_index {n : ℕ} (p0 : probabilitySimplex n)
    (R : ℕ) (p : probabilitySimplex n) :
    simplexCellIndex R (simplexCellRepresentative p0 R (simplexCellIndex R p)) =
      simplexCellIndex R p := by
  unfold simplexCellRepresentative
  rw [dif_pos ⟨p, rfl⟩]
  exact Classical.choose_spec (show ∃ q : probabilitySimplex n,
    simplexCellIndex R q = simplexCellIndex R p from ⟨p, rfl⟩)

-- @node: simplexRound
/-- Given [a fallback probability vector](hyp:p0), [an integer mesh
resolution](hyp:R), and [a probability vector to approximate](hyp:p), the
[rounded probability vector](goal) is the representative of the cell
containing that vector. -/
def simplexRound {n : ℕ} (p0 : probabilitySimplex n) (R : ℕ)
    (p : probabilitySimplex n) : probabilitySimplex n :=
  simplexCellRepresentative p0 R (simplexCellIndex R p)

-- @node: simplexRound_measurable
/-- For any fallback probability vector and integer mesh resolution,
[rounding probability vectors to their cell representatives is a measurable
map](goal). -/
@[fun_prop] lemma simplexRound_measurable {n : ℕ}
    (p0 : probabilitySimplex n) (R : ℕ) : Measurable (simplexRound p0 R) := by
  exact (measurable_of_finite (simplexCellRepresentative p0 R)).comp
    (simplexCellIndex_measurable R)

-- @node: simplexRound_coordinate_error
/-- If [the integer mesh resolution is positive](hyp:hR), then [rounding any
probability vector changes each given coordinate by strictly less than the
reciprocal resolution](goal), for any choice of fallback vector. -/
lemma simplexRound_coordinate_error {n R : ℕ} (p0 : probabilitySimplex n)
    (hR : 0 < R) (p : probabilitySimplex n) (i : Fin n) :
    |(simplexRound p0 R p).val i - p.val i| < (R : ℝ)⁻¹ :=
  simplexCellIndex_coordinate_error hR _ _ (simplexCellRepresentative_index p0 R p) i

-- @node: simplexTableGrid
/-- Given [a fallback probability vector](hyp:p0), [an integer mesh
resolution](hyp:R), and [a number of table entries](hyp:J), the [finite grid
of probability tables](goal) consists of all tables obtained by assigning
a cell code to each entry and replacing each code by its representative. -/
def simplexTableGrid {n : ℕ} (p0 : probabilitySimplex n) (R J : ℕ) :
    Finset (Fin J → probabilitySimplex n) :=
  Finset.univ.image (fun c : Fin J → (Fin n → Fin (R + 1)) =>
    fun j => simplexCellRepresentative p0 R (c j))

-- @node: simplexTableGrid_card_le
/-- For any fallback probability vector, integer mesh resolution, and number
of table entries, [the probability-table grid contains at most the resolution
plus one raised to the product of the number of coordinates and the number
of entries](goal). -/
lemma simplexTableGrid_card_le {n : ℕ} (p0 : probabilitySimplex n) (R J : ℕ) :
    (simplexTableGrid p0 R J).card ≤ (R + 1) ^ (n * J) := by
  classical
  unfold simplexTableGrid
  simpa [Fintype.card_fun, pow_mul] using
    (Finset.card_image_le (s := Finset.univ)
      (f := fun c : Fin J → (Fin n → Fin (R + 1)) =>
        fun j => simplexCellRepresentative p0 R (c j)))

-- @node: simplexTableGrid_round_mem
/-- For any table of probability vectors, fallback vector, and integer mesh
resolution, [rounding every table entry produces a table in the corresponding
finite grid](goal). -/
lemma simplexTableGrid_round_mem {n : ℕ} (p0 : probabilitySimplex n)
    (R J : ℕ) (p : Fin J → probabilitySimplex n) :
    (fun j => simplexRound p0 R (p j)) ∈ simplexTableGrid p0 R J := by
  classical
  exact Finset.mem_image.mpr ⟨fun j => simplexCellIndex R (p j), Finset.mem_univ _, rfl⟩

-- @node: simplexTableGrid_exists_approximation
/-- If [the integer mesh resolution is positive](hyp:hR), then [every table
of probability vectors has a table in the finite grid whose error at every
entry and coordinate is strictly less than the reciprocal resolution](goal),
for any choice of fallback vector. -/
lemma simplexTableGrid_exists_approximation {n R : ℕ} (p0 : probabilitySimplex n)
    (hR : 0 < R) (J : ℕ) (p : Fin J → probabilitySimplex n) :
    ∃ q ∈ simplexTableGrid p0 R J,
      ∀ j i, |(q j).val i - (p j).val i| < (R : ℝ)⁻¹ :=
  ⟨fun j => simplexRound p0 R (p j), simplexTableGrid_round_mem p0 R J p,
    fun j i => simplexRound_coordinate_error p0 hR (p j) i⟩


-- @node: simplexTableGrid_log_card_le
/-- For any fallback probability vector, integer mesh resolution, and number
of table entries, [the natural logarithm of the grid's cardinality is at most
the number of coordinates times the number of entries times the natural
logarithm of the resolution plus one](goal). -/
lemma simplexTableGrid_log_card_le {n : ℕ} (p0 : probabilitySimplex n) (R J : ℕ) :
    Real.log ((simplexTableGrid p0 R J).card : ℝ) ≤
      (n * J : ℕ) * Real.log (R + 1 : ℕ) := by
  have hnonempty : (simplexTableGrid p0 R J).Nonempty :=
    ⟨_, simplexTableGrid_round_mem p0 R J (fun _ => p0)⟩
  have hpos : (0 : ℝ) < (simplexTableGrid p0 R J).card := by
    exact_mod_cast hnonempty.card_pos
  have hcard : ((simplexTableGrid p0 R J).card : ℝ) ≤
      ((R + 1 : ℕ) : ℝ) ^ (n * J) := by
    exact_mod_cast simplexTableGrid_card_le p0 R J
  exact (Real.log_le_log hpos hcard).trans_eq (Real.log_pow _ _)

-- @node: exists_simplex_table_net
/-- Given a fallback probability vector and a number of table entries, if
[the real error tolerance is positive](hyp:hrho), then [there exists a finite
set of probability tables that approximates every probability table with
error strictly below that tolerance in every entry and coordinate, and whose
logarithmic cardinality is at most the number of coordinates times the number
of entries times the natural logarithm of two plus the reciprocal
tolerance](goal). -/
lemma exists_simplex_table_net {n : ℕ} (p0 : probabilitySimplex n)
    (J : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    ∃ T : Finset (Fin J → probabilitySimplex n),
      (∀ p : Fin J → probabilitySimplex n, ∃ q ∈ T,
        ∀ j i, |(q j).val i - (p j).val i| < rho) ∧
      Real.log (T.card : ℝ) ≤ (n * J : ℕ) * Real.log (2 + rho⁻¹) := by
  let R : ℕ := ⌈rho⁻¹⌉₊
  have hR : 0 < R := Nat.ceil_pos.mpr (inv_pos.mpr hrho)
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  have hmesh : (R : ℝ)⁻¹ ≤ rho := by
    have h := Nat.le_ceil rho⁻¹
    exact (inv_le_comm₀ hRreal hrho).mpr h
  refine ⟨simplexTableGrid p0 R J, ?_, ?_⟩
  · intro p
    obtain ⟨q, hq, herr⟩ := simplexTableGrid_exists_approximation p0 hR J p
    exact ⟨q, hq, fun j i => (herr j i).trans_le hmesh⟩
  · apply (simplexTableGrid_log_card_le p0 R J).trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Real.log_le_log (by positivity : (0 : ℝ) < (R + 1 : ℕ))
    have hc := Nat.ceil_lt_add_one (inv_nonneg.mpr hrho.le)
    dsimp only [R]
    push_cast
    linarith

end
end Papers.TbsNeuralCausalPi
