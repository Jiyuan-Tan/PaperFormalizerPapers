module

public import Papers.OaiExactSemidefiniteLift.Helpers.FunctionSpace

/-!
# Output elements and the finite moment matrix

All coefficient arrays are extracted from the explicit slice pencil. The
realization lemmas connect every extracted entry to its actual function.
Moment positivity quantifies over the entire space (T₂)²⁰.
-/

@[expose] public section

noncomputable section

namespace Papers.OaiExactSemidefiniteLift

open Matrix
open scoped BigOperators

/-- For [row i and column j of the four-by-four X matrix](hyp:i,j), the
[X coordinate element](goal) is the lifting coefficient array extracted from that matrix entry. -/
def coordXElem (i j : Fin 4) : LiftSpace :=
  coefficientsOf (fun _ a => sliceRawX a i j)

/-- For [row i and column j of the four-by-four Z matrix](hyp:i,j), the
[Z coordinate element](goal) is the lifting coefficient array extracted from that matrix entry. -/
def coordZElem (i j : Fin 4) : LiftSpace :=
  coefficientsOf (fun _ a => sliceRawZ a i j)

/-- For [one of the three planar output coordinates](hyp:l), the
[planar output element](goal) is the lifting coefficient array extracted from that
coordinate as a function of the angle and the two scalar slice coordinates. -/
def YplaneElem (l : Fin 3) : LiftSpace :=
  coefficientsOf (fun θ a => Yplane θ (sliceRawEta a) (sliceRawXi a) l)

/-- The [23 output elements](goal) list the upper-triangular entries of X in
lexicographic order, then those of Z in the same order, then the three planar output elements. -/
def outputElems : Fin 23 → LiftSpace :=
  Fin.append (fun k => coordXElem (upperIdx k).1 (upperIdx k).2)
    (Fin.append (fun k => coordZElem (upperIdx k).1 (upperIdx k).2) YplaneElem)

-- @node: def:output
/-- The [output equations](goal) require [a linear functional on the lifting space](hyp:Λ)
to match [prescribed symmetric matrices X and Z](hyp:X,Z) and
[a prescribed three-coordinate output vector](hyp:y):
[its values on all X coordinate elements equal the corresponding entries of X](step:1),
[its values on all Z coordinate elements equal the corresponding entries of Z](step:2),
and [its values on the three planar output elements equal the output vector](step:3). -/
def OutputEquations (Λ : LiftFunctional) (X Z : Sym4) (y : Fin 3 → ℝ) : Prop :=
  (∀ i j, Λ (coordXElem i j) = (X : Mat 4) i j) ∧ -- @realizes X(prescribed symmetric matrix)
  (∀ i j, Λ (coordZElem i j) = (Z : Mat 4) i j) ∧ -- @realizes Z(prescribed symmetric matrix)
  (∀ l, Λ (YplaneElem l) = y l)

/-- The [ordered real trigonometric basis](goal) consists of the constant one,
cosine, sine, cosine of twice the angle, and sine of twice the angle, in that order. -/
def momentBasis : Fin 5 → ℝ → ℝ := -- @realizes f_a(real ordered T_2 basis)
  ![fun _ => 1, -- @realizes f_1(constant real basis function)
    Real.cos, -- @realizes f_2(real cosine basis function)
    Real.sin, fun θ => Real.cos (2 * θ), fun θ => Real.sin (2 * θ)]

/-- For [pencil row i](hyp:i), [basis index a](hyp:a), [pencil column j](hyp:j),
and [basis index b](hyp:b), the [moment entry element](goal) is the lifting
coefficient array extracted from the product of basis functions a and b and pencil entry i, j. -/
def momentEntryElem (i : Fin 20) (a : Fin 5) (j : Fin 20) (b : Fin 5) : LiftSpace :=
  -- @realizes a(moment index in the five-element real basis)
  -- @realizes b(moment index in the five-element real basis)
  coefficientsOf (fun θ x => momentBasis a θ * momentBasis b θ * pencilFromCoords θ x i j)

-- @node: def:moment-matrix
/-- For [a linear functional on the lifting space](hyp:Λ), the [moment matrix](goal)
is the 100-by-100 matrix indexed by pairs of a pencil index and a basis index;
each entry is the functional's value on the corresponding moment entry element. -/
def momentMatrixH (Λ : LiftFunctional) : Matrix (Fin 20 × Fin 5) (Fin 20 × Fin 5) ℝ :=
  -- @realizes H(\Lambda)(real moment matrix indexed by the twenty pencil rows and five functions)
  fun ia jb => Λ (momentEntryElem ia.1 ia.2 jb.1 jb.2)

-- @node: ass:pin-1
/-- The [basis pinning condition](goal) asserts that the moment basis is exactly
the ordered list consisting of one, cosine, sine, cosine of twice the angle,
and sine of twice the angle. -/
def MomentBasisPinned : Prop :=
  momentBasis = ![fun _ => 1, Real.cos, Real.sin,
    fun θ => Real.cos (2 * θ), fun θ => Real.sin (2 * θ)]

/-- Given [twenty rows of five real basis coefficients](hyp:t),
[a component index](hyp:i), and [an angle](hyp:θ), the
[trigonometric vector component](goal) is the sum of that component's coefficients
times the five prescribed basis functions evaluated at the angle. -/
def trigVector (t : Fin 20 → Fin 5 → ℝ) (i : Fin 20) (θ : ℝ) : ℝ :=
  -- @realizes t(real moment coefficient array)
  ∑ a : Fin 5, t i a * momentBasis a θ

/-- For [a vector of twenty real functions of the angle](hyp:q), the
[quadratic function element](goal) is the lifting coefficient array extracted
from the sum, over all pencil rows and columns, of the row component of the vector
times the pencil entry times the column component of the vector. -/
def quadraticFunctionElem (q : Fin 20 → ℝ → ℝ) : LiftSpace :=
  coefficientsOf (fun θ x => ∑ i : Fin 20, ∑ j : Fin 20,
    q i θ * pencilFromCoords θ x i j * q j θ)

/-- For [twenty rows of five real trigonometric coefficients](hyp:t), the
[quadratic element](goal) is the quadratic function element of the vector obtained
by expanding each row in the prescribed five-function basis. -/
def quadElem (t : Fin 20 → Fin 5 → ℝ) : LiftSpace :=
  quadraticFunctionElem (trigVector t)

-- @node: def:moment
/-- [A linear functional on the lifting space](hyp:Λ) satisfies
[moment positivity](goal) when its value on the quadratic function element is
nonnegative for every twenty-component vector whose components are real
trigonometric polynomials of degree at most two. -/
def MomentPositive (Λ : LiftFunctional) : Prop :=
  ∀ q : Fin 20 → ℝ → ℝ, -- @realizes q(real twenty-component trigonometric vector)
    (∀ i, IsTrigPolyLE 2 (q i)) → 0 ≤ Λ (quadraticFunctionElem q)

-- @node: eval_coordXElem
/-- [Evaluating an X coordinate element at any angle, symmetric matrices X and Z,
and scalar slice coordinates returns the corresponding entry of X](goal). -/
lemma eval_coordXElem (i j : Fin 4) (θ : ℝ) (𝒳 𝒵 : Sym4) (η ξ : ℝ) :
    evalLift (coordXElem i j) θ 𝒳 𝒵 η ξ = (𝒳 : Mat 4) i j := by
  unfold coordXElem
  rw [coefficientsOf_realizes]
  · exact congrFun (congrFun (sliceRawX_sliceCoords 𝒳 𝒵 η ξ) i) j
  · intro l
    exact Causalean.Mathlib.Analysis.BernsteinSzegoTrig.isTrigPolyLE_const 7 _
  · intro t x
    exact sliceRawX_linear x i j

-- @node: eval_coordZElem
/-- [Evaluating a Z coordinate element at any angle, symmetric matrices X and Z,
and scalar slice coordinates returns the corresponding entry of Z](goal). -/
lemma eval_coordZElem (i j : Fin 4) (θ : ℝ) (𝒳 𝒵 : Sym4) (η ξ : ℝ) :
    evalLift (coordZElem i j) θ 𝒳 𝒵 η ξ = (𝒵 : Mat 4) i j := by
  unfold coordZElem
  rw [coefficientsOf_realizes]
  · exact congrFun (congrFun (sliceRawZ_sliceCoords 𝒳 𝒵 η ξ) i) j
  · intro l
    exact Causalean.Mathlib.Analysis.BernsteinSzegoTrig.isTrigPolyLE_const 7 _
  · intro t x
    exact sliceRawZ_linear x i j

-- @node: eval_YplaneElem
/-- [Evaluating a planar output element at any angle, symmetric matrices, and
two scalar slice coordinates returns the corresponding planar output coordinate
at that angle and those scalars](goal). -/
lemma eval_YplaneElem (l : Fin 3) (θ : ℝ) (𝒳 𝒵 : Sym4) (η ξ : ℝ) :
    evalLift (YplaneElem l) θ 𝒳 𝒵 η ξ = Yplane θ η ξ l := by
  unfold YplaneElem
  rw [coefficientsOf_realizes]
  · rfl
  · intro i
    fin_cases l
    · refine ⟨fun k => if k = 1 then sliceRawEta (Pi.single i 1) else 0,
        fun _ => 0, ?_⟩
      intro t
      simp [Yplane, dVec, kVec, Finset.sum_range_succ]
    · refine ⟨fun _ => 0,
        fun k => if k = 1 then sliceRawEta (Pi.single i 1) else 0, ?_⟩
      intro t
      simp [Yplane, dVec, kVec, Finset.sum_range_succ]
    · simpa [Yplane, dVec, kVec] using
        Causalean.Mathlib.Analysis.BernsteinSzegoTrig.isTrigPolyLE_const 7
          (sliceRawXi (Pi.single i 1))
  · intro t x
    simp only [Yplane, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    fin_cases l <;>
      simp [Yplane, dVec, kVec, sliceRawEta, sliceRawXi, Pi.single_apply,
        ite_mul, mul_ite, Finset.sum_add_distrib, mul_comm]

-- @node: eval_outputElems
/-- [Evaluating any of the 23 output elements at an angle, two symmetric matrices,
and two scalar slice coordinates gives the corresponding coordinate of the
output consisting of those matrices and their planar output](goal). -/
lemma eval_outputElems (ν : Fin 23) (θ : ℝ) (𝒳 𝒵 : Sym4) (η ξ : ℝ) :
    evalLift (outputElems ν) θ 𝒳 𝒵 η ξ = outputCoords (𝒳, 𝒵, Yplane θ η ξ) ν := by
  fin_cases ν <;>
    simp [outputElems, outputCoords, upperCoords, upperIdx, Fin.append, Fin.addCases,
      eval_coordXElem, eval_coordZElem, eval_YplaneElem]

set_option maxHeartbeats 800000 in
-- @node: outputElems_independent
/-- [The 23 output elements are linearly independent over the real numbers](goal). -/
lemma outputElems_independent : LinearIndependent ℝ outputElems := by
  rw [Fintype.linearIndependent_iff]
  intro c hc ν
  have heval (θ : ℝ) (𝒳 𝒵 : Sym4) (η ξ : ℝ) :
      ∑ i, c i * outputCoords (𝒳, 𝒵, Yplane θ η ξ) i = 0 := by
    have h := congrArg (evaluationFunctional θ 𝒳 𝒵 η ξ) hc
    simpa only [map_sum, map_smul, map_zero, evaluationFunctional,
      LinearMap.coe_mk, AddHom.coe_mk, eval_outputElems, smul_eq_mul] using h
  let Xtest (x : Fin 22 → ℝ) : Sym4 := ⟨sliceRawX x,
    Matrix.isHermitian_iff_isSymm.mpr (symFromUpper_isSymm _)⟩
  let Ztest (x : Fin 22 → ℝ) : Sym4 := ⟨sliceRawZ x,
    Matrix.isHermitian_iff_isSymm.mpr (symFromUpper_isSymm _)⟩
  have hout (θ : ℝ) (x : Fin 22 → ℝ) :
      outputCoords (Xtest x, Ztest x, Yplane θ (x 20) (x 21)) =
        Fin.append (fun i : Fin 20 => x ⟨i.val, by omega⟩)
          ![x 20 * Real.cos θ, x 20 * Real.sin θ, x 21] := by
    ext i
    fin_cases i <;>
      simp [outputCoords, upperCoords, upperIdx, Yplane, dVec, kVec,
        Xtest, Ztest, sliceRawX, sliceRawZ, symFromUpper,
        Fin.sum_univ_succ, Fin.append, Fin.addCases]
  let n : Fin 22 := ⟨if ν.val < 20 then ν.val else if ν.val = 22 then 21 else 20,
    by split <;> (try split) <;> omega⟩
  let x : Fin 22 → ℝ := Pi.single n 1
  have h := heval (if ν.val = 21 then Real.pi / 2 else 0)
    (Xtest x) (Ztest x) (x 20) (x 21)
  rw [hout] at h
  fin_cases ν <;>
    simpa [x, n, Pi.single_apply, Fin.sum_univ_succ, Fin.append, Fin.addCases] using h

-- @node: coordXElem_symm
/-- [Exchanging the row and column indices leaves the X coordinate element unchanged](goal). -/
lemma coordXElem_symm (i j : Fin 4) : coordXElem i j = coordXElem j i := by
  simp only [coordXElem, sliceRawX, symFromUpper, min_comm i j, max_comm i j]

-- @node: coordZElem_symm
/-- [Exchanging the row and column indices leaves the Z coordinate element unchanged](goal). -/
lemma coordZElem_symm (i j : Fin 4) : coordZElem i j = coordZElem j i := by
  simp only [coordZElem, sliceRawZ, symFromUpper, min_comm i j, max_comm i j]

-- @node: outputEquations_iff
/-- [A linear functional satisfies the output equations for two prescribed symmetric
matrices and a three-coordinate vector if and only if its values on all 23 output
elements equal the corresponding coordinates of that prescribed output](goal). -/
lemma outputEquations_iff (Λ : LiftFunctional) (X Z : Sym4) (y : Fin 3 → ℝ) :
    OutputEquations Λ X Z y ↔ ∀ ν, Λ (outputElems ν) = outputCoords (X, Z, y) ν := by
  constructor
  · rintro ⟨hX, hZ, hy⟩ ν
    fin_cases ν <;> simp [outputElems, outputCoords, upperCoords, upperIdx, Fin.append, Fin.addCases, hX, hZ, hy]
  · intro h
    have hX := Matrix.isHermitian_iff_isSymm.mp X.property
    have hZ := Matrix.isHermitian_iff_isSymm.mp Z.property
    have h' : ∀ ν, Λ (outputElems ν) = outputCoords (X, Z, y) ν := h
    simp only [Fin.forall_fin_succ] at h'
    simp [outputElems, outputCoords, upperCoords, upperIdx, Fin.append, Fin.addCases] at h'
    rcases h' with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      fin_cases i <;> fin_cases j
      · exact h0
      · exact h1
      · exact h2
      · exact h3
      · exact (congrArg Λ (coordXElem_symm 1 0)).trans (h1.trans (hX.apply 1 0))
      · exact h4
      · exact h5
      · exact h6
      · exact (congrArg Λ (coordXElem_symm 2 0)).trans (h2.trans (hX.apply 2 0))
      · exact (congrArg Λ (coordXElem_symm 2 1)).trans (h5.trans (hX.apply 2 1))
      · exact h7
      · exact h8
      · exact (congrArg Λ (coordXElem_symm 3 0)).trans (h3.trans (hX.apply 3 0))
      · exact (congrArg Λ (coordXElem_symm 3 1)).trans (h6.trans (hX.apply 3 1))
      · exact (congrArg Λ (coordXElem_symm 3 2)).trans (h8.trans (hX.apply 3 2))
      · exact h9
    · intro i j
      fin_cases i <;> fin_cases j
      · exact h10
      · exact h11
      · exact h12
      · exact h13
      · exact (congrArg Λ (coordZElem_symm 1 0)).trans (h11.trans (hZ.apply 1 0))
      · exact h14
      · exact h15
      · exact h16
      · exact (congrArg Λ (coordZElem_symm 2 0)).trans (h12.trans (hZ.apply 2 0))
      · exact (congrArg Λ (coordZElem_symm 2 1)).trans (h15.trans (hZ.apply 2 1))
      · exact h17
      · exact h18
      · exact (congrArg Λ (coordZElem_symm 3 0)).trans (h13.trans (hZ.apply 3 0))
      · exact (congrArg Λ (coordZElem_symm 3 1)).trans (h16.trans (hZ.apply 3 1))
      · exact (congrArg Λ (coordZElem_symm 3 2)).trans (h18.trans (hZ.apply 3 2))
      · exact h19
    · intro l
      fin_cases l
      · exact h20
      · exact h21
      · exact h22

-- @node: momentBasis_trig
/-- [Each of the five moment basis functions is a real trigonometric polynomial
of degree at most two](goal). -/
lemma momentBasis_trig (a : Fin 5) : IsTrigPolyLE 2 (momentBasis a) := by
  fin_cases a
  · exact Causalean.Mathlib.Analysis.BernsteinSzegoTrig.isTrigPolyLE_const 2 1
  · refine ⟨fun k => if k = 1 then 1 else 0, fun _ => 0, ?_⟩
    intro θ
    simp [momentBasis]
  · refine ⟨fun _ => 0, fun k => if k = 1 then 1 else 0, ?_⟩
    intro θ
    simp [momentBasis]
  · refine ⟨fun k => if k = 2 then 1 else 0, fun _ => 0, ?_⟩
    intro θ
    simp [momentBasis]
  · refine ⟨fun _ => 0, fun k => if k = 2 then 1 else 0, ?_⟩
    intro θ
    simp [momentBasis]

-- @node: momentBasis_spans
/-- [A real function of the angle is a trigonometric polynomial of degree at most
two if and only if it is a real linear combination of the five moment basis
functions, with the same five coefficients at every angle](goal). -/
lemma momentBasis_spans (f : ℝ → ℝ) :
    IsTrigPolyLE 2 f ↔ ∃ t : Fin 5 → ℝ, ∀ θ, f θ = ∑ a, t a * momentBasis a θ := by
  constructor
  · rintro ⟨a, b, h⟩
    refine ⟨![a 0, a 1, b 1, a 2, b 2], ?_⟩
    intro θ
    rw [h θ]
    simp [Finset.sum_range_succ, Fin.sum_univ_succ, momentBasis]
    ring
  · rintro ⟨t, h⟩
    refine ⟨fun k => if k = 0 then t 0 else if k = 1 then t 1 else t 3,
      fun k => if k = 1 then t 2 else t 4, ?_⟩
    intro θ
    rw [h θ]
    simp [Finset.sum_range_succ, Fin.sum_univ_succ, momentBasis]
    ring

-- @node: moment_entry_degree
/-- [For any fixed slice coordinates and pencil row and column, the product of
two moment basis functions and that pencil entry is a real trigonometric
polynomial of degree at most seven](goal).

The bound adds the two basis degrees and the degree three of the angular
factor U: 2 + 2 + 3 = 7, with no uniform degree-six claim. -/
lemma moment_entry_degree (i j : Fin 20) (a b : Fin 5) (x : Fin 22 → ℝ) :
    IsTrigPolyLE 7 (fun θ => momentBasis a θ * momentBasis b θ *
      pencilFromCoords θ x i j) := by
  exact trig_product (trig_product (momentBasis_trig a) (momentBasis_trig b))
    (pencil_entry_trig x i j)

-- @node: eval_momentEntryElem
/-- [Evaluating a moment entry element at an angle, two symmetric matrices, and
two scalar slice coordinates gives the product of its two basis functions at
that angle and the corresponding entry of the twenty-by-twenty slice pencil](goal). -/
lemma eval_momentEntryElem (i j : Fin 20) (a b : Fin 5)
    (θ : ℝ) (𝒳 𝒵 : Sym4) (η ξ : ℝ) :
    evalLift (momentEntryElem i a j b) θ 𝒳 𝒵 η ξ =
      momentBasis a θ * momentBasis b θ * slicePencil20 θ 𝒳 𝒵 η ξ i j := by
  unfold momentEntryElem
  rw [coefficientsOf_realizes]
  · rw [pencilFromCoords_sliceCoords]
  · intro l
    exact moment_entry_degree i j a b _
  · intro t x
    rw [pencilFromCoords_linear t x i j, Finset.mul_sum]
    simp only [mul_assoc]

-- @node: quadElem_expansion
/-- [The quadratic element associated with any twenty-by-five coefficient array
equals the sum of all moment entry elements, each weighted by the product of
the coefficients at its row-basis and column-basis pairs](goal). -/
lemma quadElem_expansion (t : Fin 20 → Fin 5 → ℝ) :
    quadElem t = ∑ i : Fin 20, ∑ j : Fin 20, ∑ a : Fin 5, ∑ b : Fin 5,
      (t i a * t j b) • momentEntryElem i a j b := by
  ext c k
  simp only [quadElem, quadraticFunctionElem, momentEntryElem, coefficientsOf,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [trigVector, Finset.sum_mul, Finset.mul_sum]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2
    ext i
    rw [Finset.sum_comm]
    arg 2
    ext j
    rw [Finset.sum_comm]
    arg 2
    ext b
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro n _
  ring

-- @node: eval_quadraticFunctionElem
/-- If [every component of a twenty-component vector is a real trigonometric
polynomial of degree at most two](hyp:hq), then [evaluating its quadratic
function element at any angle and slice variables equals the quadratic form
of the twenty-by-twenty slice pencil on that vector at that angle](goal). -/
lemma eval_quadraticFunctionElem (q : Fin 20 → ℝ → ℝ)
    (hq : ∀ i, IsTrigPolyLE 2 (q i)) (θ : ℝ) (𝒳 𝒵 : Sym4) (η ξ : ℝ) :
    evalLift (quadraticFunctionElem q) θ 𝒳 𝒵 η ξ =
      ∑ i : Fin 20, ∑ j : Fin 20, q i θ * slicePencil20 θ 𝒳 𝒵 η ξ i j * q j θ := by
  choose t ht using fun i => (momentBasis_spans (q i)).1 (hq i)
  have heq : q = trigVector t := by
    funext i s
    exact ht i s
  rw [heq]
  change evaluationFunctional θ 𝒳 𝒵 η ξ (quadElem t) = _
  rw [quadElem_expansion]
  simp only [map_sum, map_smul, smul_eq_mul]
  change (∑ i, ∑ j, ∑ a, ∑ b,
    (t i a * t j b) * evalLift (momentEntryElem i a j b) θ 𝒳 𝒵 η ξ) = _
  simp_rw [eval_momentEntryElem]
  simp only [trigVector, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

-- @node: pencilFromCoords_isSymm
/-- [The twenty-by-twenty pencil reconstructed from any 22 real slice coordinates
is symmetric at every angle](goal). -/
lemma pencilFromCoords_isSymm (θ : ℝ) (a : Fin 22 → ℝ) :
    (pencilFromCoords θ a).IsSymm := by
  have hX := symFromUpper_isSymm (fun i => a (Fin.castAdd 12 i))
  have hZ := symFromUpper_isSymm (fun i => a (Fin.natAdd 10 (Fin.castAdd 2 i)))
  have hRaw : (slicePencilRaw θ (sliceRawX a) (sliceRawZ a)
      (sliceRawEta a) (sliceRawXi a)).IsSymm := by
    apply Matrix.IsSymm.fromBlocks (B := sliceB θ (sliceRawEta a) (sliceRawXi a)) _ rfl hZ
    apply Matrix.IsSymm.ext
    intro i j
    simp [sliceRawX, hX.apply i.2 j.2, Matrix.one_apply, eq_comm]
  exact hRaw.submatrix sliceIndexEquiv.symm

-- @node: momentMatrixH_isSymm
/-- [The moment matrix of every real linear functional on the lifting space
is symmetric](goal). -/
lemma momentMatrixH_isSymm (Λ : LiftFunctional) : (momentMatrixH Λ).IsSymm := by
  have hEntry (i j : Fin 20) (a b : Fin 5) :
      momentEntryElem i a j b = momentEntryElem j b i a := by
    unfold momentEntryElem
    congr 1
    funext θ x
    rw [(pencilFromCoords_isSymm θ x).apply j i]
    ring
  apply Matrix.IsSymm.ext
  intro i j
  exact congrArg Λ (hEntry j.1 i.1 j.2 i.2)

-- @node: quadElem_apply
/-- [A linear functional's value on the quadratic element of a twenty-by-five
coefficient array equals the quadratic form of its moment matrix on the same
coefficients indexed by component-basis pairs](goal). -/
lemma quadElem_apply (Λ : LiftFunctional) (t : Fin 20 → Fin 5 → ℝ) :
    Λ (quadElem t) = (fun ia : Fin 20 × Fin 5 => t ia.1 ia.2) ⬝ᵥ
      (momentMatrixH Λ *ᵥ (fun ia : Fin 20 × Fin 5 => t ia.1 ia.2)) := by
  rw [quadElem_expansion]
  simp only [map_sum, map_smul, smul_eq_mul, dotProduct, mulVec,
    Fintype.sum_prod_type, Finset.mul_sum, momentMatrixH]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro b _
  ring

-- @node: momentMatrixH_posSemidef_iff
/-- [A linear functional's moment matrix is positive semidefinite if and only if
the functional is nonnegative on the quadratic function element of every
twenty-component vector of real trigonometric polynomials of degree at most two](goal). -/
lemma momentMatrixH_posSemidef_iff (Λ : LiftFunctional) :
    (momentMatrixH Λ).PosSemidef ↔ MomentPositive Λ := by
  constructor
  · intro h q hq
    choose t ht using fun i => (momentBasis_spans (q i)).mp (hq i)
    have heq : q = trigVector t := by
      funext i θ
      exact ht i θ
    rw [heq]
    change 0 ≤ Λ (quadElem t)
    rw [quadElem_apply]
    simpa only [star_trivial] using
      h.dotProduct_mulVec_nonneg (fun ia : Fin 20 × Fin 5 => t ia.1 ia.2)
  · intro h
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (Matrix.isHermitian_iff_isSymm.mpr (momentMatrixH_isSymm Λ))
    intro v
    let t : Fin 20 → Fin 5 → ℝ := fun i a => v (i, a)
    have ht : ∀ i, IsTrigPolyLE 2 (trigVector t i) := by
      intro i
      exact (momentBasis_spans _).mpr ⟨t i, fun _ => rfl⟩
    have hv := h (trigVector t) ht
    change 0 ≤ Λ (quadElem t) at hv
    rw [quadElem_apply] at hv
    simpa only [t, star_trivial] using hv

-- @node: momentMatrixH_add
/-- [The moment matrix of the sum of two linear functionals equals the sum of
their moment matrices](goal). -/
lemma momentMatrixH_add (Λ Γ : LiftFunctional) :
    momentMatrixH (Λ + Γ) = momentMatrixH Λ + momentMatrixH Γ := by
  ext i j
  exact LinearMap.add_apply Λ Γ _

-- @node: momentMatrixH_smul
/-- [Multiplying a linear functional by any real scalar multiplies its moment
matrix by that same scalar](goal). -/
lemma momentMatrixH_smul (r : ℝ) (Λ : LiftFunctional) :
    momentMatrixH (r • Λ) = r • momentMatrixH Λ := by
  ext i j
  rfl

end Papers.OaiExactSemidefiniteLift
