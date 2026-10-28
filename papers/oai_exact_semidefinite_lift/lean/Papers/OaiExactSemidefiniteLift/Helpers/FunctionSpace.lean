module

public import Papers.OaiExactSemidefiniteLift.Helpers.TrigCoefficients
public import Papers.OaiExactSemidefiniteLift.Helpers.Gram
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Szego
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dual.Defs

/-!
# The concrete 330-dimensional trigonometric lifting space

Coefficients use the ordered basis `1, cos θ, sin θ, …, cos 7θ, sin 7θ`.
The evaluation and range lemmas identify this coefficient model with precisely
the homogeneous linear function space in the paper. Coefficients of the explicit
pencil expressions are extracted by the fifteen-point discrete Fourier formula.
-/

@[expose] public section

noncomputable section

namespace Papers.OaiExactSemidefiniteLift

open scoped BigOperators

/-- For [symmetric matrices X and Z](hyp:𝒳,𝒵) and [real scalars η and ξ](hyp:η,ξ),
the [22 slice coordinates](goal) concatenate the upper triangles of X and Z, followed by η and ξ. -/
def sliceCoords (𝒳 𝒵 : Sym4) (η ξ : ℝ) : Fin 22 → ℝ :=
  Fin.append (upperCoords (𝒳 : Mat 4))
    (Fin.append (upperCoords (𝒵 : Mat 4)) ![η, ξ])

/-- From [ten upper-triangular entries](hyp:a), the [reconstructed four-by-four matrix](goal)
reflects the upper triangle across the diagonal. -/
def symFromUpper (a : Fin 10 → ℝ) : Mat 4 := fun i j =>
  ∑ l : Fin 10, if upperIdx l = (min i j, max i j) then a l else 0

/-- From [22 slice coordinates](hyp:a), the [raw X matrix](goal) is the symmetric
four-by-four matrix reconstructed from the first ten coordinates. -/
def sliceRawX (a : Fin 22 → ℝ) : Mat 4 := symFromUpper (fun i => a (Fin.castAdd 12 i))
/-- From [22 slice coordinates](hyp:a), the [raw Z matrix](goal) is the symmetric
four-by-four matrix reconstructed from the next ten coordinates after those of X. -/
def sliceRawZ (a : Fin 22 → ℝ) : Mat 4 :=
  symFromUpper (fun i => a (Fin.natAdd 10 (Fin.castAdd 2 i)))
/-- From [22 slice coordinates](hyp:a), the [raw scalar η](goal) is the penultimate coordinate. -/
def sliceRawEta (a : Fin 22 → ℝ) : ℝ := a 20
/-- From [22 slice coordinates](hyp:a), the [raw scalar ξ](goal) is the last coordinate. -/
def sliceRawXi (a : Fin 22 → ℝ) : ℝ := a 21

/-- At [angle θ](hyp:θ), the [twenty-by-twenty pencil](goal) inserts the matrices
and scalars reconstructed from [22 slice coordinates](hyp:a), with rows and columns numbered zero through nineteen. -/
def pencilFromCoords (θ : ℝ) (a : Fin 22 → ℝ) : Mat 20 := fun i j =>
  slicePencilRaw θ (sliceRawX a) (sliceRawZ a) (sliceRawEta a) (sliceRawXi a)
    (sliceIndexEquiv.symm i) (sliceIndexEquiv.symm j)

-- @node: def:lifting-space
/-- The [lifting coefficient space](goal) consists of real arrays with 22 rows
for slice coordinates and fifteen columns for trigonometric basis functions through frequency seven. -/
abbrev LiftSpace := Fin 22 → Fin 15 → ℝ
-- @realizes \mathcal E(coefficient model of homogeneous linear functions with T_7 coefficients)

/-- The [value of the lifting expansion](goal) for [coefficient array a](hyp:a)
at [angle θ](hyp:θ), [symmetric matrices X and Z](hyp:𝒳,𝒵), and [scalars η and ξ](hyp:η,ξ)
is the sum of each coefficient times its trigonometric basis function and slice coordinate. -/
def evalLift (a : LiftSpace) (θ : ℝ) (𝒳 𝒵 : Sym4) (η ξ : ℝ) : ℝ :=
  ∑ i : Fin 22, ∑ k : Fin 15, a i k * trigBasis7 k θ * sliceCoords 𝒳 𝒵 η ξ i

/-- A [function of an angle, two symmetric matrices, and two scalars](hyp:f)
[belongs to the lifting function space](goal) if there exist 22 coefficient functions such that
[each is a trigonometric polynomial of degree at most seven](step:1) and
[the function is their weighted sum against the 22 slice coordinates at every input](step:2). -/
def IsLiftFunction (f : ℝ → Sym4 → Sym4 → ℝ → ℝ → ℝ) : Prop :=
  ∃ c : Fin 22 → ℝ → ℝ, (∀ i, IsTrigPolyLE 7 (c i)) ∧
    ∀ θ 𝒳 𝒵 η ξ, f θ 𝒳 𝒵 η ξ = ∑ i, c i θ * sliceCoords 𝒳 𝒵 η ξ i

-- @node: symFromUpper_isSymm
/-- [The matrix reconstructed by reflecting ten upper-triangular entries is symmetric](goal). -/
lemma symFromUpper_isSymm (a : Fin 10 → ℝ) : (symFromUpper a).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp [symFromUpper, min_comm, max_comm]

-- @node: sliceRawX_sliceCoords
/-- [Extracting the raw X matrix from the slice coordinates of two symmetric matrices
and two scalars recovers the original X matrix](goal). -/
lemma sliceRawX_sliceCoords (𝒳 𝒵 : Sym4) (η ξ : ℝ) :
    sliceRawX (sliceCoords 𝒳 𝒵 η ξ) = (𝒳 : Mat 4) := by
  have h := (Matrix.isHermitian_iff_isSymm.mp 𝒳.property)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sliceRawX, sliceCoords, symFromUpper, upperCoords, upperIdx, Fin.sum_univ_succ,
      h.apply] <;> exact h.apply 1 0

-- @node: sliceRawZ_sliceCoords
/-- [Extracting the raw Z matrix from the slice coordinates of two symmetric matrices
and two scalars recovers the original Z matrix](goal). -/
lemma sliceRawZ_sliceCoords (𝒳 𝒵 : Sym4) (η ξ : ℝ) :
    sliceRawZ (sliceCoords 𝒳 𝒵 η ξ) = (𝒵 : Mat 4) := by
  have h := (Matrix.isHermitian_iff_isSymm.mp 𝒵.property)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sliceRawZ, sliceCoords, symFromUpper, upperCoords, upperIdx, Fin.sum_univ_succ,
      h.apply] <;> exact h.apply 1 0

-- @node: pencilFromCoords_sliceCoords
/-- [The pencil reconstructed from slice coordinates equals the original twenty-by-twenty
slice pencil at the same angle, symmetric matrices, and scalars](goal). -/
lemma pencilFromCoords_sliceCoords (θ : ℝ) (𝒳 𝒵 : Sym4) (η ξ : ℝ) :
    pencilFromCoords θ (sliceCoords 𝒳 𝒵 η ξ) = slicePencil20 θ 𝒳 𝒵 η ξ := by
  ext i j
  simp only [pencilFromCoords, sliceRawX_sliceCoords, sliceRawZ_sliceCoords,
    slicePencil20, slicePencil]
  rfl

-- @node: evalLift_range
/-- [A function of the angle and slice variables is the evaluation of a lifting coefficient
array if and only if it is homogeneous linear in the 22 slice coordinates with
trigonometric polynomial coefficients of degree at most seven](goal). -/
lemma evalLift_range (f : ℝ → Sym4 → Sym4 → ℝ → ℝ → ℝ) :
    (∃ a : LiftSpace, evalLift a = f) ↔ IsLiftFunction f := by
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨fun i θ => ∑ k, a i k * trigBasis7 k θ, ?_, ?_⟩
    · intro i
      exact (trigBasis7_spans _).2 ⟨a i, fun _ => rfl⟩
    · intro θ 𝒳 𝒵 η ξ
      simp only [evalLift, Finset.sum_mul]
  · rintro ⟨c, hc, hf⟩
    choose a ha using fun i => (trigBasis7_spans (c i)).1 (hc i)
    refine ⟨a, ?_⟩
    funext θ 𝒳 𝒵 η ξ
    rw [hf]
    simp_rw [evalLift, ← Finset.sum_mul, ← ha]

-- @node: liftSpace_finrank
/-- [The lifting coefficient space has real dimension 330](goal). -/
lemma liftSpace_finrank : Module.finrank ℝ LiftSpace = 330 := by
  simp [LiftSpace, Module.finrank_pi_fintype, Module.finrank_pi]

-- @node: evalLift_add
/-- [Evaluating the sum of two lifting coefficient arrays at any angle and slice variables
gives the sum of their separate evaluations](goal). -/
lemma evalLift_add (a b : LiftSpace) (θ : ℝ) (𝒳 𝒵 : Sym4) (η ξ : ℝ) :
    evalLift (a + b) θ 𝒳 𝒵 η ξ = evalLift a θ 𝒳 𝒵 η ξ + evalLift b θ 𝒳 𝒵 η ξ := by
  simp [evalLift, add_mul, Finset.sum_add_distrib]

-- @node: evalLift_smul
/-- [Multiplying a lifting coefficient array by a real scalar multiplies its evaluation
at any angle and slice variables by the same scalar](goal). -/
lemma evalLift_smul (r : ℝ) (a : LiftSpace) (θ : ℝ) (𝒳 𝒵 : Sym4) (η ξ : ℝ) :
    evalLift (r • a) θ 𝒳 𝒵 η ξ = r * evalLift a θ 𝒳 𝒵 η ξ := by
  simp [evalLift, Finset.mul_sum, mul_assoc]

-- @node: def:lifting-functional
/-- A [lifting functional](goal) is a real linear map from the lifting coefficient space to the real numbers. -/
abbrev LiftFunctional := LiftSpace →ₗ[ℝ] ℝ
-- @realizes \Lambda(real linear functional on the concrete lifting space)

/-- The [evaluation functional](goal) at [angle θ](hyp:θ), [symmetric matrices X and Z](hyp:𝒳,𝒵),
and [scalars η and ξ](hyp:η,ξ) is the real linear map taking a coefficient array to its lifting expansion at that input. -/
def evaluationFunctional (θ : ℝ) (𝒳 𝒵 : Sym4) (η ξ : ℝ) : LiftFunctional where
  toFun a := evalLift a θ 𝒳 𝒵 η ξ
  map_add' a b := evalLift_add a b θ 𝒳 𝒵 η ξ
  map_smul' r a := evalLift_smul r a θ 𝒳 𝒵 η ξ

/-- For [a real-valued function of an angle and 22 coordinates](hyp:f), the
[extracted coefficient array](goal) samples the function on each coordinate unit vector
at fifteen equally spaced angles and sums against each trigonometric basis function,
with normalization 1/15 for the constant and 2/15 for nonzero frequencies. -/
def coefficientsOf (f : ℝ → (Fin 22 → ℝ) → ℝ) : LiftSpace := fun i k =>
  (if k.val = 0 then (1 / 15 : ℝ) else 2 / 15) *
    ∑ n : Fin 15, f (sampleAngle n) (Pi.single i 1) * trigBasis7 k (sampleAngle n)

-- @node: coefficientsOf_eval
/-- [Fourier extraction from the homogeneous linear trigonometric expansion of any
lifting coefficient array recovers that array exactly](goal). -/
lemma coefficientsOf_eval (a : LiftSpace) :
    coefficientsOf (fun (θ : ℝ) (x : Fin 22 → ℝ) => ∑ i : Fin 22, ∑ k : Fin 15,
      a i k * trigBasis7 k θ * x i) = a := by
  ext i k
  simp only [coefficientsOf]
  simp only [← Finset.sum_mul, Pi.single_apply]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  have h (l : Fin 15) :
      (if k.val = 0 then (1 / 15 : ℝ) else 2 / 15) *
        (a i l * ∑ n : Fin 15, trigBasis7 l (sampleAngle n) *
          trigBasis7 k (sampleAngle n)) = a i l * (if k = l then 1 else 0) := by
    rw [← mul_assoc, mul_comm _ (a i l), mul_assoc, discrete_trig_orthogonality]
  rw [Finset.mul_sum]
  simp_rw [h]
  simp

-- @node: sliceCoords_surjective
/-- [Every vector of 22 real coordinates is the slice-coordinate vector of some
two symmetric four-by-four matrices and two real scalars](goal). -/
lemma sliceCoords_surjective (x : Fin 22 → ℝ) :
    ∃ (𝒳 𝒵 : Sym4) (η ξ : ℝ), sliceCoords 𝒳 𝒵 η ξ = x := by
  let 𝒳 : Sym4 := ⟨sliceRawX x,
    Matrix.isHermitian_iff_isSymm.mpr (symFromUpper_isSymm _)⟩
  let 𝒵 : Sym4 := ⟨sliceRawZ x,
    Matrix.isHermitian_iff_isSymm.mpr (symFromUpper_isSymm _)⟩
  refine ⟨𝒳, 𝒵, x 20, x 21, ?_⟩
  ext i
  fin_cases i <;>
    simp [sliceCoords, 𝒳, 𝒵, sliceRawX, sliceRawZ, symFromUpper,
      upperCoords, upperIdx, Fin.sum_univ_succ, Fin.append, Fin.addCases]

-- @node: evalLift_injective
/-- [Two lifting coefficient arrays whose evaluations agree at every angle and all
slice variables must be equal](goal). -/
lemma evalLift_injective : Function.Injective evalLift := by
  intro a b hab
  have hraw : (fun (θ : ℝ) (x : Fin 22 → ℝ) => ∑ i : Fin 22, ∑ k : Fin 15,
      a i k * trigBasis7 k θ * x i) =
      (fun (θ : ℝ) (x : Fin 22 → ℝ) => ∑ i : Fin 22, ∑ k : Fin 15,
      b i k * trigBasis7 k θ * x i) := by
    funext θ x
    obtain ⟨𝒳, 𝒵, η, ξ, rfl⟩ := sliceCoords_surjective x
    exact congrFun (congrFun (congrFun (congrFun (congrFun hab θ) 𝒳) 𝒵) η) ξ
  simpa only [coefficientsOf_eval] using congrArg coefficientsOf hraw

-- @node: coefficientsOf_realizes
/-- If [the function on each coordinate unit vector is a trigonometric polynomial
of degree at most seven](hyp:hdegree) and [at every angle the function is the
coordinate-weighted sum of its values on those unit vectors](hyp:hlinear), then
[evaluating its extracted coefficient array at any angle and slice variables
recovers the function at the corresponding slice coordinates](goal). -/
lemma coefficientsOf_realizes (f : ℝ → (Fin 22 → ℝ) → ℝ)
    (hdegree : ∀ i, IsTrigPolyLE 7 (fun θ => f θ (Pi.single i 1)))
    (hlinear : ∀ θ x, f θ x = ∑ i : Fin 22, f θ (Pi.single i 1) * x i)
    (θ : ℝ) (𝒳 𝒵 : Sym4) (η ξ : ℝ) :
    evalLift (coefficientsOf f) θ 𝒳 𝒵 η ξ = f θ (sliceCoords 𝒳 𝒵 η ξ) := by
  choose a ha using fun i => (trigBasis7_spans _).1 (hdegree i)
  have hf : f = fun θ x => ∑ i : Fin 22, ∑ k : Fin 15,
      a i k * trigBasis7 k θ * x i := by
    funext θ x
    rw [hlinear]
    simp_rw [ha, Finset.sum_mul]
  rw [hf, coefficientsOf_eval]
  rfl

-- @node: sliceRawX_linear
/-- [Each entry of the raw X matrix is the sum over the 22 coordinates of that
coordinate times the same matrix entry evaluated on its coordinate unit vector](goal). -/
lemma sliceRawX_linear (x : Fin 22 → ℝ) (i j : Fin 4) :
    sliceRawX x i j = ∑ l : Fin 22, sliceRawX (Pi.single l 1) i j * x l := by
  simp only [sliceRawX, symFromUpper, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp [Pi.single_apply, mul_ite]

-- @node: sliceRawZ_linear
/-- [Each entry of the raw Z matrix is the sum over the 22 coordinates of that
coordinate times the same matrix entry evaluated on its coordinate unit vector](goal). -/
lemma sliceRawZ_linear (x : Fin 22 → ℝ) (i j : Fin 4) :
    sliceRawZ x i j = ∑ l : Fin 22, sliceRawZ (Pi.single l 1) i j * x l := by
  simp only [sliceRawZ, symFromUpper, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp [Pi.single_apply, mul_ite]

-- @node: sliceB_linear_params
/-- [At any fixed angle, each entry of the stacked skew blocks at scalars η and ξ
equals η times that entry at scalar pair (1, 0) plus ξ times that entry at (0, 1)](goal). -/
lemma sliceB_linear_params (θ η ξ : ℝ) (ji : Fin 4 × Fin 4) (k : Fin 4) :
    sliceB θ η ξ ji k = η * sliceB θ 1 0 ji k + ξ * sliceB θ 0 1 ji k := by
  have hF (b : Fin 4) (r : Fin 3) :
      factorColumn θ η ξ b r =
        η * factorColumn θ 1 0 b r + ξ * factorColumn θ 0 1 b r := by
    fin_cases b <;>
      simp [factorColumn, realify, Fθ, Complex.mul_re, Complex.mul_im]
  rcases ji with ⟨b, i⟩
  induction i using Fin.cases with
  | zero =>
    induction k using Fin.cases with
    | zero => simp [sliceB, Bskew]
    | succ k => simpa [sliceB, Bskew] using hF b k
  | succ i =>
    induction k using Fin.cases with
    | zero => simp [sliceB, Bskew, hF]; ring
    | succ k => simp [sliceB, Bskew]

-- @node: pencilFromCoords_linear
/-- [At any fixed angle, each pencil entry is the sum over the 22 slice coordinates
of that coordinate times the same pencil entry evaluated on its coordinate unit vector](goal). -/
lemma pencilFromCoords_linear (θ : ℝ) (x : Fin 22 → ℝ) (i j : Fin 20) :
    pencilFromCoords θ x i j =
      ∑ l : Fin 22, pencilFromCoords θ (Pi.single l 1) i j * x l := by
  have hB (ji : Fin 4 × Fin 4) (k : Fin 4) :
      sliceB θ (sliceRawEta x) (sliceRawXi x) ji k =
        ∑ l : Fin 22,
          sliceB θ (sliceRawEta (Pi.single l 1)) (sliceRawXi (Pi.single l 1)) ji k * x l := by
    conv_lhs => rw [sliceB_linear_params]
    conv_rhs =>
      arg 2
      ext l
      rw [sliceB_linear_params]
    simp [sliceRawEta, sliceRawXi, Pi.single_apply, add_mul, ite_mul,
      Finset.sum_add_distrib]
    <;> ring
  obtain ⟨i, rfl⟩ := sliceIndexEquiv.surjective i
  obtain ⟨j, rfl⟩ := sliceIndexEquiv.surjective j
  simp only [pencilFromCoords, Equiv.symm_apply_apply]
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      simp only [slicePencilRaw, Matrix.fromBlocks_apply₁₁,
        Matrix.kronecker, Matrix.kroneckerMap_apply]
      rw [sliceRawX_linear, Finset.mul_sum]
      simp only [mul_assoc]
    | inr j => exact hB i j
  | inr i =>
    cases j with
    | inl j => exact hB j i
    | inr j => exact sliceRawZ_linear x i j

-- @node: trig_sin_frequency
/-- If [the nonnegative integer frequency k is at most n](hyp:hk), then
[the sine of k times the angle is a trigonometric polynomial of degree at most n](goal). -/
lemma trig_sin_frequency (n k : ℕ) (hk : k ≤ n) :
    IsTrigPolyLE n (fun θ => Real.sin ((k : ℝ) * θ)) := by
  refine ⟨fun _ => 0, fun l => if l = k then 1 else 0, ?_⟩
  intro θ
  simp [Finset.sum_eq_single k, Finset.mem_range.mpr (by omega : k < n + 1)]

-- @node: trig_cos_frequency
/-- If [the nonnegative integer frequency k is at most n](hyp:hk), then
[the cosine of k times the angle is a trigonometric polynomial of degree at most n](goal). -/
lemma trig_cos_frequency (n k : ℕ) (hk : k ≤ n) :
    IsTrigPolyLE n (fun θ => Real.cos ((k : ℝ) * θ)) :=
  (Causalean.Mathlib.Analysis.BernsteinSzegoTrig.cos_nat_mul_isTrigPolyLE k).mono hk

-- @node: trig_difference_frequencies
/-- If [the nonnegative integer frequency i is at most n](hyp:hi) and
[the nonnegative integer frequency j is at most n](hyp:hj), then
[both the cosine and the sine of their signed frequency difference times the angle
are trigonometric polynomials of degree at most n](goal). -/
lemma trig_difference_frequencies (n i j : ℕ) (hi : i ≤ n) (hj : j ≤ n) :
    IsTrigPolyLE n (fun θ => Real.cos (((i : ℝ) - j) * θ)) ∧
    IsTrigPolyLE n (fun θ => Real.sin (((i : ℝ) - j) * θ)) := by
  by_cases h : j ≤ i
  · have heq : (i : ℝ) - j = ((i - j : ℕ) : ℝ) := (Nat.cast_sub h).symm
    simpa only [heq] using
      And.intro (trig_cos_frequency n (i - j) (by omega))
        (trig_sin_frequency n (i - j) (by omega))
  · have heq : (i : ℝ) - j = -((j - i : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : i ≤ j)]
      ring
    constructor
    · simpa only [heq, neg_mul, Real.cos_neg] using
        trig_cos_frequency n (j - i) (by omega)
    · simpa only [heq, neg_mul, Real.sin_neg, neg_one_mul, one_mul] using
        (trig_sin_frequency n (j - i) (by omega)).const_mul (-1)

-- @node: trig_sum
/-- If [every function indexed by a given finite set is a trigonometric polynomial
of degree at most n](hyp:hf), then [their pointwise sum over that set is also
a trigonometric polynomial of degree at most n](goal). -/
lemma trig_sum {ι : Type*} (s : Finset ι) {n : ℕ} (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, IsTrigPolyLE n (f i)) :
    IsTrigPolyLE n (fun θ => ∑ i ∈ s, f i θ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using
      Causalean.Mathlib.Analysis.BernsteinSzegoTrig.isTrigPolyLE_const n 0
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hf i (Finset.mem_insert_self _ _)).add
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

-- @node: trig_frequency_products
/-- If [the nonnegative integer frequency i is at most a](hyp:hi) and
[the nonnegative integer frequency j is at most b](hyp:hj), then
[all four products formed by choosing sine or cosine at each of these frequencies
are trigonometric polynomials of degree at most a plus b](goal). -/
lemma trig_frequency_products (a b i j : ℕ) (hi : i ≤ a) (hj : j ≤ b) :
    IsTrigPolyLE (a + b) (fun θ => Real.cos ((i : ℝ) * θ) * Real.cos ((j : ℝ) * θ)) ∧
    IsTrigPolyLE (a + b) (fun θ => Real.sin ((i : ℝ) * θ) * Real.cos ((j : ℝ) * θ)) ∧
    IsTrigPolyLE (a + b) (fun θ => Real.cos ((i : ℝ) * θ) * Real.sin ((j : ℝ) * θ)) ∧
    IsTrigPolyLE (a + b) (fun θ => Real.sin ((i : ℝ) * θ) * Real.sin ((j : ℝ) * θ)) := by
  have hc := trig_cos_frequency (a + b) (i + j) (by omega)
  have hs := trig_sin_frequency (a + b) (i + j) (by omega)
  have hd := trig_difference_frequencies (a + b) i j (by omega) (by omega)
  have hd' := trig_difference_frequencies (a + b) j i (by omega) (by omega)
  simp only [Nat.cast_add, add_mul] at hc hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply ((hd.1.add hc).const_mul (1 / 2)).congr
    intro θ
    have h := Real.two_mul_cos_mul_cos ((i : ℝ) * θ) ((j : ℝ) * θ)
    rw [sub_mul] at *
    linarith
  · apply ((hd.2.add hs).const_mul (1 / 2)).congr
    intro θ
    have h := Real.two_mul_sin_mul_cos ((i : ℝ) * θ) ((j : ℝ) * θ)
    rw [sub_mul] at *
    linarith
  · apply ((hd'.2.add hs).const_mul (1 / 2)).congr
    intro θ
    have h := Real.two_mul_sin_mul_cos ((j : ℝ) * θ) ((i : ℝ) * θ)
    rw [sub_mul] at *
    rw [add_comm ((j : ℝ) * θ)] at h
    nlinarith
  · apply ((hd.1.sub hc).const_mul (1 / 2)).congr
    intro θ
    have h := Real.two_mul_sin_mul_sin ((i : ℝ) * θ) ((j : ℝ) * θ)
    rw [sub_mul] at *
    linarith

-- @node: trig_product
/-- If [f is a trigonometric polynomial of degree at most a](hyp:hf) and
[g is a trigonometric polynomial of degree at most b](hyp:hg), then
[their pointwise product is a trigonometric polynomial of degree at most a plus b](goal). -/
lemma trig_product {a b : ℕ} {f g : ℝ → ℝ}
    (hf : IsTrigPolyLE a f) (hg : IsTrigPolyLE b g) :
    IsTrigPolyLE (a + b) (fun θ => f θ * g θ) := by
  rcases hf with ⟨c, d, hf⟩
  rcases hg with ⟨e, h, hg⟩
  have hterm (i : ℕ) (hi : i ∈ Finset.range (a + 1))
      (j : ℕ) (hj : j ∈ Finset.range (b + 1)) :=
    trig_frequency_products a b i j (by simpa using hi) (by simpa using hj)
  have hsum := trig_sum (Finset.range (a + 1)) _ (fun i hi =>
    trig_sum (Finset.range (b + 1)) _ (fun j hj =>
      ((((hterm i hi j hj).1.const_mul (c i * e j)).add
        ((hterm i hi j hj).2.2.1.const_mul (c i * h j))).add
        ((hterm i hi j hj).2.1.const_mul (d i * e j))).add
        ((hterm i hi j hj).2.2.2.const_mul (d i * h j))))
  apply hsum.congr
  intro θ
  rw [hf θ, hg θ, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

-- @node: realify_Umat_entry_trig
/-- [Each entry of the real matrix obtained by interleaving the real and imaginary
columns of the angular factor U is a trigonometric polynomial of degree at most three](goal). -/
lemma realify_Umat_entry_trig (i : Fin 3) (j : Fin 4) :
    IsTrigPolyLE 3 (fun θ => realify (Umat θ) i j) := by
  have hc : IsTrigPolyLE 1 Real.cos := by
    simpa using trig_cos_frequency 1 1 (by omega)
  have hs : IsTrigPolyLE 1 Real.sin := by
    simpa using trig_sin_frequency 1 1 (by omega)
  have hcc := (trig_product hc hc).sub (trig_product hs hs)
  have hcs := (trig_product hc hs).const_mul 2
  have hsc := trig_product hs hcc
  have hss := trig_product hs hcs
  have hcc' := trig_product hc hcc
  have hcs' := trig_product hc hcs
  have hc3 := hc.mono (by omega : 1 ≤ 3)
  have hs3 := hs.mono (by omega : 1 ≤ 3)
  fin_cases i <;> fin_cases j
  · apply (hc3.const_mul (-(Real.sqrt 2 / 2))).congr
    intro θ
    simp only [Umat, wPhase_inv_trig]
    simp [realify, wPhase, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Complex.mul_re, Complex.mul_im, pow_two]
    <;> ring <;> simp
  · apply (hs3.const_mul ((Real.sqrt 2 / 2))).congr
    intro θ
    simp only [Umat, wPhase_inv_trig]
    simp [realify, wPhase, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Complex.mul_re, Complex.mul_im, pow_two]
    <;> ring <;> simp
  · apply (hc3.const_mul (-(Real.sqrt 2 / 2))).congr
    intro θ
    simp only [Umat, wPhase_inv_trig]
    simp [realify, wPhase, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Complex.mul_re, Complex.mul_im, pow_two]
    <;> ring <;> simp
  · apply (hs3.const_mul (-(Real.sqrt 2 / 2))).congr
    intro θ
    simp only [Umat, wPhase_inv_trig]
    simp [realify, wPhase, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Complex.mul_re, Complex.mul_im, pow_two]
    <;> ring <;> simp
  · apply (hsc.const_mul ((Real.sqrt 2 / 2))).congr
    intro θ
    simp only [Umat, wPhase_inv_trig]
    simp [realify, wPhase, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Complex.mul_re, Complex.mul_im, pow_two]
    <;> ring <;> simp
  · apply (hss.const_mul (-(Real.sqrt 2 / 2))).congr
    intro θ
    simp only [Umat, wPhase_inv_trig]
    simp [realify, wPhase, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Complex.mul_re, Complex.mul_im, pow_two]
    <;> ring <;> simp
  · apply (hsc.const_mul ((Real.sqrt 2 / 2))).congr
    intro θ
    simp only [Umat, wPhase_inv_trig]
    simp [realify, wPhase, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Complex.mul_re, Complex.mul_im, pow_two]
    <;> ring <;> simp
  · apply (hss.const_mul ((Real.sqrt 2 / 2))).congr
    intro θ
    simp only [Umat, wPhase_inv_trig]
    simp [realify, wPhase, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Complex.mul_re, Complex.mul_im, pow_two]
    <;> ring <;> simp
  · apply (hcc'.const_mul ((Real.sqrt 2 / 2))).congr
    intro θ
    simp only [Umat, wPhase_inv_trig]
    simp [realify, wPhase, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Complex.mul_re, Complex.mul_im, pow_two]
    <;> ring <;> simp
  · apply (hcs'.const_mul (-(Real.sqrt 2 / 2))).congr
    intro θ
    simp only [Umat, wPhase_inv_trig]
    simp [realify, wPhase, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Complex.mul_re, Complex.mul_im, pow_two]
    <;> ring <;> simp
  · apply (hcc'.const_mul (-(Real.sqrt 2 / 2))).congr
    intro θ
    simp only [Umat, wPhase_inv_trig]
    simp [realify, wPhase, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Complex.mul_re, Complex.mul_im, pow_two]
    <;> ring <;> simp
  · apply (hcs'.const_mul (-(Real.sqrt 2 / 2))).congr
    intro θ
    simp only [Umat, wPhase_inv_trig]
    simp [realify, wPhase, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Complex.mul_re, Complex.mul_im, pow_two]
    <;> ring <;> simp

-- @node: pencil_entry_trig
/-- [For any fixed 22 slice coordinates and any row and column, the pencil entry
as a function of the angle is a trigonometric polynomial of degree at most three](goal).

Multiplication by two trigonometric basis functions of degree at most two therefore
gives the bound 2 + 2 + 3 = 7. -/
lemma pencil_entry_trig (a : Fin 22 → ℝ) (i j : Fin 20) :
    IsTrigPolyLE 3 (fun θ => pencilFromCoords θ a i j) := by
  have hF (r : Fin 3) (c : Fin 4) :
      IsTrigPolyLE 3 (fun θ => factorColumn θ (sliceRawEta a) (sliceRawXi a) c r) := by
    apply (((realify_Umat_entry_trig r c).const_mul (sliceRawEta a)).add
      (Causalean.Mathlib.Analysis.BernsteinSzegoTrig.isTrigPolyLE_const 3
        (sliceRawXi a * realify V0 r c))).congr
    intro θ
    simp [factorColumn, realify_Fθ_linear]
  have hB (ji : Fin 4 × Fin 4) (k : Fin 4) :
      IsTrigPolyLE 3 (fun θ => sliceB θ (sliceRawEta a) (sliceRawXi a) ji k) := by
    rcases ji with ⟨b, i⟩
    induction i using Fin.cases with
    | zero =>
      induction k using Fin.cases with
      | zero =>
        simpa [sliceB, Bskew] using
          Causalean.Mathlib.Analysis.BernsteinSzegoTrig.isTrigPolyLE_const 3 0
      | succ k => simpa [sliceB, Bskew] using hF k b
    | succ i =>
      induction k using Fin.cases with
      | zero =>
        simpa [sliceB, Bskew] using (hF i b).const_mul (-1)
      | succ k =>
        simpa [sliceB, Bskew] using
          Causalean.Mathlib.Analysis.BernsteinSzegoTrig.isTrigPolyLE_const 3 0
  obtain ⟨i, rfl⟩ := sliceIndexEquiv.surjective i
  obtain ⟨j, rfl⟩ := sliceIndexEquiv.surjective j
  simp only [pencilFromCoords, Equiv.symm_apply_apply]
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      exact Causalean.Mathlib.Analysis.BernsteinSzegoTrig.isTrigPolyLE_const 3 _
    | inr j => exact hB i j
  | inr i =>
    cases j with
    | inl j => exact hB j i
    | inr j =>
      exact Causalean.Mathlib.Analysis.BernsteinSzegoTrig.isTrigPolyLE_const 3 _

-- @node: outputCoords_linear_add
/-- [The 23 output coordinates of the sum of two output vectors equal the componentwise
sum of their output coordinates](goal). -/
lemma outputCoords_linear_add (x z : V) :
    outputCoords (x + z) = outputCoords x + outputCoords z := by
  ext ν
  fin_cases ν <;> rfl

-- @node: outputCoords_linear_smul
/-- [The 23 output coordinates of a real scalar multiple of an output vector equal
that scalar times its output coordinates](goal). -/
lemma outputCoords_linear_smul (r : ℝ) (x : V) :
    outputCoords (r • x) = r • outputCoords x := by
  ext ν
  fin_cases ν <;> rfl

end Papers.OaiExactSemidefiniteLift
