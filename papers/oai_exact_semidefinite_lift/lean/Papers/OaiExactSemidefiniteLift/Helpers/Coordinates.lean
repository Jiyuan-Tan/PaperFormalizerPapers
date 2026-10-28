module

public import Papers.OaiExactSemidefiniteLift.Helpers.Moment
public import Mathlib.LinearAlgebra.Pi

/-!
# The prescribed 23 coordinates and the remaining 307 coordinates

The split is explicit: twenty constant matrix entries, η cos θ, η sin θ,
and ξ are the output slots. The remaining slots define the auxiliary matrices
by applying the actual moment map. No unspecified matrix certificate is used.
-/

@[expose] public section

noncomputable section

namespace Papers.OaiExactSemidefiniteLift

open Matrix
open scoped BigOperators

/-- A [coefficient slot](goal) is a pair consisting of one of 22 raw coordinates and
one of 15 trigonometric basis indices. -/
abbrev CoeffSlot := Fin 22 × Fin 15

/-- The [output-slot enumeration](goal) lists [the twenty constant matrix-entry slots](step:1),
followed by [the slots for η cos θ, η sin θ, and ξ](step:2). -/
def outputSlot : Fin 23 → CoeffSlot :=
  Fin.append (fun i : Fin 20 => (Fin.castAdd 2 i, 0)) ![(20, 1), (20, 2), (21, 0)]

/-- The [free-slot enumeration](goal) lists the remaining 307 coefficient slots in order:
[the 280 nonconstant slots of the first twenty raw coordinates](step:1),
[the constant slot of raw coordinate 20](step:2),
[the twelve slots of raw coordinate 20 with basis indices 3 through 14](step:3), and
[the fourteen nonconstant slots of raw coordinate 21](step:4). -/
def freeSlot : Fin 307 → CoeffSlot :=
  Fin.append
    (fun i : Fin 280 =>
      let p : Fin 20 × Fin 14 := finProdFinEquiv.symm i
      (Fin.castAdd 2 p.1, p.2.succ))
    (Fin.append
      (Fin.append ![(20, 0)] (fun k : Fin 12 => ((20 : Fin 22), Fin.natAdd 3 k)))
      (fun k : Fin 14 => ((21 : Fin 22), k.succ)))

/-- For [a coefficient slot s](hyp:s), the [unit coefficient array at s](goal) has
[value one at s](step:1) and [value zero at every other slot](step:2). -/
def coeffUnit (s : CoeffSlot) : LiftSpace := fun i k =>
  if (i, k) = s then 1 else 0

/-- For [a coefficient slot s](hyp:s), the [coordinate functional at s](goal) is the
linear functional that returns the entry of a coefficient array at s. -/
def coefficientFunctional (s : CoeffSlot) : LiftFunctional :=
  (LinearMap.proj s.2 : (Fin 15 → ℝ) →ₗ[ℝ] ℝ).comp
    (LinearMap.proj s.1 : LiftSpace →ₗ[ℝ] (Fin 15 → ℝ))

/-- Given [23 output weights x](hyp:x) and [307 free weights v](hyp:v), the
[functional assembled from these coordinates](goal) is the sum of
[the output coordinate functionals weighted by x](step:1) and
[the free coordinate functionals weighted by v](step:2). -/
def functionalFromCoords (x : Fin 23 → ℝ) (v : Fin 307 → ℝ) : LiftFunctional :=
  ∑ ν : Fin 23, x ν • coefficientFunctional (outputSlot ν) +
    ∑ j : Fin 307, v j • coefficientFunctional (freeSlot j)

/-- The [moment-index correspondence](goal) bijectively numbers the pairs of twenty
pencil-row indices and five basis-function indices by the integers from 0 through 99. -/
def momentIndexEquiv : (Fin 20 × Fin 5) ≃ Fin 100 := finProdFinEquiv

/-- For [a linear functional Λ on coefficient arrays](hyp:Λ), the
[100-by-100 moment matrix](goal) is its moment matrix with each row and column pair
relabelled by the moment-index correspondence. -/
def momentMatrix100 (Λ : LiftFunctional) : Mat 100 :=
  fun i j => momentMatrixH Λ (momentIndexEquiv.symm i) (momentIndexEquiv.symm j)

/-- For [an output index ν among the 23 prescribed coordinates](hyp:ν), the
[output coefficient matrix at ν](goal) is the 100-by-100 moment matrix of the
coordinate functional at that output slot. -/
def outputMatrix (ν : Fin 23) : Mat 100 :=
  -- @realizes A_\nu(fixed output coefficient matrices from H)
  momentMatrix100 (coefficientFunctional (outputSlot ν))

/-- For [a free index j among the 307 remaining coordinates](hyp:j), the
[auxiliary coefficient matrix at j](goal) is the 100-by-100 moment matrix of the
coordinate functional at that free slot. -/
def auxiliaryMatrix (j : Fin 307) : Mat 100 :=
  -- @realizes B_j(fixed auxiliary coefficient matrices from H)
  momentMatrix100 (coefficientFunctional (freeSlot j))

/-- Given [23 output weights x](hyp:x) and [307 auxiliary weights v](hyp:v), the
[homogeneous matrix pencil](goal) is the sum of [the output matrices weighted by x](step:1)
and [the auxiliary matrices weighted by v](step:2), with no constant term. -/
def homogeneousPencil (x : Fin 23 → ℝ) (v : Fin 307 → ℝ) : Mat 100 :=
  ∑ ν : Fin 23, x ν • outputMatrix ν + ∑ j : Fin 307, v j • auxiliaryMatrix j

-- @node: coefficientsOf_unit
/-- For [a coefficient slot s](hyp:s), [extracting the coefficients of its
trigonometric basis function times its raw coordinate gives the unit coefficient
array at s](goal). -/
lemma coefficientsOf_unit (s : CoeffSlot) :
    coefficientsOf (fun θ x => trigBasis7 s.2 θ * x s.1) = coeffUnit s := by
  rcases s with ⟨i, k⟩
  have h := coefficientsOf_eval (coeffUnit (i, k))
  convert h using 1
  congr 1
  funext θ x
  simp [coeffUnit, Prod.mk.injEq, ite_and, ite_mul]

-- @node: outputElems_eq_unit
/-- For [an output index ν](hyp:ν), [the corresponding output element is the unit
coefficient array at its output slot](goal). -/
lemma outputElems_eq_unit (ν : Fin 23) : outputElems ν = coeffUnit (outputSlot ν) := by
  rw [← coefficientsOf_unit]
  fin_cases ν <;>
    dsimp [outputElems, coordXElem, coordZElem, YplaneElem, outputSlot, Fin.append, Fin.addCases] <;>
    congr 1 <;> funext θ x <;>
    simp [sliceRawX, sliceRawZ, symFromUpper, upperIdx, sliceRawEta, sliceRawXi,
      trigBasis7, Yplane, dVec, kVec, Fin.sum_univ_succ] <;> ring

-- @node: slotPartitionInverse
/-- For [a coefficient slot s](hyp:s), the [inverse coordinate partition](goal)
returns its output or free index. In the first twenty raw coordinates it returns
[output index i for basis index zero](step:1) or [free index 14i + k − 1 otherwise](step:2);
in raw coordinate 20 it returns [free index 280 for k = 0](step:3),
[output index 19 + k for k = 1 or 2](step:4), or [free index 278 + k for k ≥ 3](step:5);
in raw coordinate 21 it returns [output index 22 for k = 0](step:6) or
[free index 292 + k otherwise](step:7), where i and k are the raw-coordinate and basis indices. -/
def slotPartitionInverse (s : CoeffSlot) : Fin 23 ⊕ Fin 307 :=
  if hi : s.1.val < 20 then
    if hk : s.2.val = 0 then Sum.inl ⟨s.1.val, by omega⟩
    else Sum.inr ⟨s.1.val * 14 + s.2.val - 1, by omega⟩
  else if hj : s.1.val = 20 then
    if hk : s.2.val = 0 then Sum.inr 280
    else if hl : s.2.val < 3 then Sum.inl ⟨19 + s.2.val, by omega⟩
    else Sum.inr ⟨278 + s.2.val, by omega⟩
  else if hk : s.2.val = 0 then Sum.inl 22
  else Sum.inr ⟨292 + s.2.val, by omega⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- @node: output_free_slots_bijective
/-- [The combined output-slot and free-slot enumerations assign exactly one index
to every coefficient slot](goal). -/
lemma output_free_slots_bijective :
    Function.Bijective (Sum.elim outputSlot freeSlot) := by
  have hl : Function.LeftInverse slotPartitionInverse (Sum.elim outputSlot freeSlot) := by
    decide +kernel
  have hr : Function.RightInverse slotPartitionInverse (Sum.elim outputSlot freeSlot) := by
    decide +kernel
  exact ⟨hl.injective, hr.surjective⟩

-- @node: coefficientFunctional_coeffUnit
/-- For [coefficient slots s and t](hyp:s,t), [the coordinate functional at s
evaluated on the unit array at t is one when the slots agree and zero otherwise](goal). -/
lemma coefficientFunctional_coeffUnit (s t : CoeffSlot) :
    coefficientFunctional s (coeffUnit t) = if s = t then 1 else 0 := by
  rfl

-- @node: coeffUnit_expansion
/-- For [a coefficient array a](hyp:a), [a equals the sum of the unit coefficient
arrays weighted by its entry at each slot](goal). -/
lemma coeffUnit_expansion (a : LiftSpace) :
    a = ∑ s : CoeffSlot, a s.1 s.2 • coeffUnit s := by
  ext i k
  simp [coeffUnit, Finset.sum_apply]

-- @node: functionalFromCoords_outputs
/-- For [23 output weights x](hyp:x), [307 free weights v](hyp:v), and
[an output index ν](hyp:ν), [the functional assembled from these weights evaluates
the corresponding output element to the output weight at ν](goal). -/
lemma functionalFromCoords_outputs (x : Fin 23 → ℝ) (v : Fin 307 → ℝ) (ν : Fin 23) :
    functionalFromCoords x v (outputElems ν) = x ν := by
  rw [outputElems_eq_unit]
  have ho (μ : Fin 23) : outputSlot μ = outputSlot ν ↔ μ = ν := by
    constructor
    · intro h
      exact Sum.inl.inj (output_free_slots_bijective.injective h)
    · rintro rfl
      rfl
  have hf (j : Fin 307) : freeSlot j ≠ outputSlot ν := by
    intro h
    have := output_free_slots_bijective.injective (a₁ := Sum.inr j) (a₂ := Sum.inl ν) h
    cases this
  simp [functionalFromCoords, coefficientFunctional_coeffUnit, ho, hf]

-- @node: functional_reconstruction
/-- For [a linear functional Λ on coefficient arrays](hyp:Λ), [Λ is recovered by
assembling the output weights given by its values on the output elements and the
free weights given by its values on the free-slot unit arrays](goal). -/
lemma functional_reconstruction (Λ : LiftFunctional) :
    Λ = functionalFromCoords (fun ν => Λ (outputElems ν))
      (fun j => Λ (coeffUnit (freeSlot j))) := by
  have hsplit (f : CoeffSlot → ℝ) :
      (∑ s, f s) = (∑ ν, f (outputSlot ν)) + ∑ j, f (freeSlot j) := by
    rw [← output_free_slots_bijective.sum_comp f, Fintype.sum_sum_type]
    rfl
  apply LinearMap.ext
  intro a
  calc
    Λ a = ∑ s : CoeffSlot, a s.1 s.2 * Λ (coeffUnit s) := by
      conv_lhs => rw [coeffUnit_expansion a]
      simp
    _ = _ := by
      rw [hsplit]
      simp [functionalFromCoords, outputElems_eq_unit, coefficientFunctional, mul_comm]

-- @node: momentMatrix100_posSemidef_iff
/-- For [a linear functional Λ on coefficient arrays](hyp:Λ), [its relabelled
100-by-100 moment matrix is positive semidefinite if and only if its moment matrix
indexed by row and basis-function pairs is positive semidefinite](goal). -/
lemma momentMatrix100_posSemidef_iff (Λ : LiftFunctional) :
    (momentMatrix100 Λ).PosSemidef ↔ (momentMatrixH Λ).PosSemidef := by
  exact Matrix.posSemidef_submatrix_equiv (M := momentMatrixH Λ) momentIndexEquiv.symm

-- @node: outputMatrix_isSymm
/-- For [an output index ν](hyp:ν), [the corresponding output coefficient matrix
is symmetric](goal). -/
lemma outputMatrix_isSymm (ν : Fin 23) : (outputMatrix ν).IsSymm := by
  exact (momentMatrixH_isSymm (coefficientFunctional (outputSlot ν))).submatrix momentIndexEquiv.symm

-- @node: auxiliaryMatrix_isSymm
/-- For [a free index j](hyp:j), [the corresponding auxiliary coefficient matrix
is symmetric](goal). -/
lemma auxiliaryMatrix_isSymm (j : Fin 307) : (auxiliaryMatrix j).IsSymm := by
  exact (momentMatrixH_isSymm (coefficientFunctional (freeSlot j))).submatrix momentIndexEquiv.symm

-- @node: momentMatrix100_fromCoords
/-- For [23 output weights x](hyp:x) and [307 free weights v](hyp:v), [the
100-by-100 moment matrix of the functional assembled from these weights equals
the homogeneous pencil with those same weights](goal). -/
lemma momentMatrix100_fromCoords (x : Fin 23 → ℝ) (v : Fin 307 → ℝ) :
    momentMatrix100 (functionalFromCoords x v) = homogeneousPencil x v := by
  ext i j
  simp [momentMatrix100, momentMatrixH, functionalFromCoords, homogeneousPencil,
    outputMatrix, auxiliaryMatrix, Matrix.sum_apply]

-- @node: homogeneousPencil_zero
/-- [The homogeneous pencil is the zero matrix when all output and auxiliary
weights are zero](goal). -/
lemma homogeneousPencil_zero : homogeneousPencil 0 0 = 0 := by
  simp [homogeneousPencil]

end Papers.OaiExactSemidefiniteLift
