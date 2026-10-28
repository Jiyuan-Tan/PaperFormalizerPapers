module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Real matrix and dyadic triangular-form setup

Matrices use orthonormal real coordinates. Inputs are ambient functions whose
restrictions to the nonnegative quadrant are the paper's inputs.
-/

@[expose] public section

open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace Papers.OaiBoundDyadicTriangular

-- @env: S1
variable {ι κ η : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype η] [DecidableEq η]

-- @node: ass:real-matrices
/-- For [a field of scalars](hyp:𝕜), [the real-matrix setting means that this field
is isomorphic to the real numbers as a field](goal). -/
def RealMatrixSetting (𝕜 : Type*) [Field 𝕜] : Prop := Nonempty (𝕜 ≃+* ℝ)

-- @node: def:transpose
/-- For [a real rectangular matrix](hyp:R), [its real adjoint is its transpose](goal).

@realizes R(real rectangular row operator in orthonormal coordinates)
@realizes R^*(real transpose) -/
def realAdjoint (R : Matrix ι κ ℝ) : Matrix κ ι ℝ := R.transpose

-- @node: ass:annihilates-kernel
/-- For [a real square matrix defining a kernel](hyp:P) and [a real square direction
matrix](hyp:K), [kernel annihilation means that every vector mapped to zero by the
first matrix is also mapped to zero by the direction matrix](goal). -/
def AnnihilatesKernel (P K : Matrix ι ι ℝ) : Prop :=
  ∀ x : ι → ℝ, P *ᵥ x = 0 → K *ᵥ x = 0

-- @node: def:supported-directions
/-- For [a real square matrix defining the support](hyp:P) and [a real square
direction matrix](hyp:K), [being supported on the first matrix](goal) requires
[the direction matrix to annihilate its kernel](hyp:annihilates). -/
structure SupportedOn (P K : Matrix ι ι ℝ) : Prop where
  annihilates : AnnihilatesKernel P K

-- @node: def:matrix-energy
/-- For [a real square matrix](hyp:P), [its matrix energy is the trace of its
three-halves power, defined by continuous functional calculus](goal).

@realizes \Phi(trace of the three-halves power) -/
noncomputable def matrixEnergy
    (P : Matrix ι ι ℝ) : ℝ := -- @realizes P(real square matrix carrier)
  (cfc (fun x : ℝ => x ^ (3 / 2 : ℝ)) P).trace

/-- For [a real square matrix](hyp:P), [its support subspace is the orthogonal
complement of its kernel in Euclidean space](goal).

@realizes \supp P(orthogonal complement of the Euclidean kernel) -/
noncomputable def supportSubspace (P : Matrix ι ι ℝ) : Submodule ℝ (EuclideanSpace ℝ ι) :=
  (LinearMap.ker (Matrix.toEuclideanLin P))ᗮ

-- @node: def:hessian
/-- For [a real square matrix](hyp:P), [a guarantee that it is symmetric](hyp:hP),
and [a real square direction matrix](hyp:K), [the supported Hessian form](goal)
uses [an orthonormal eigenvector matrix](step:1), [the corresponding eigenvalues](step:2),
and [the direction expressed in that eigenbasis](step:3). Its value is
[three halves times the sum, over pairs of positive eigenvalues, of the squared
direction entry divided by the sum of their square roots; all other pairs contribute
zero](step:4).

@realizes b_P(K)(supported spectral Hessian quadratic form) -/
noncomputable def hessForm (P : Matrix ι ι ℝ) (hP : P.IsHermitian)
    (K : Matrix ι ι ℝ) : ℝ := -- @realizes K(real square direction carrier)
  let V : Matrix ι ι ℝ := hP.eigenvectorUnitary
  let p := hP.eigenvalues -- @realizes p_i(eigenvalues; only the positive ones enter)
  let K' := V.transpose * K * V
  (3 / 2 : ℝ) * ∑ i, ∑ j,
    if 0 < p i ∧ 0 < p j then -- @realizes p_i(positive support eigenvalues)
      K' i j ^ 2 / (Real.sqrt (p i) + Real.sqrt (p j)) else 0

-- @node: ass:hessian-positive-support
/-- For [a real square matrix](hyp:P), [the positive-support condition for the
Hessian means that the matrix is positive semidefinite](goal).

@realizes P(real symmetric positive semidefinite matrix) -/
def HessianPositiveSupport (P : Matrix ι ι ℝ) : Prop := P.PosSemidef

-- @node: ass:hessian-direction
/-- For [a real square base matrix](hyp:P) and [a real square direction matrix](hyp:K),
[being a Hessian direction](goal) means that [the direction is symmetric](step:1)
and [annihilates the base matrix's kernel](step:2).

@realizes K(symmetric direction annihilating the fixed kernel) -/
def HessianDirection (P K : Matrix ι ι ℝ) : Prop :=
  K.IsSymm ∧ AnnihilatesKernel P K

-- @node: ass:order-matrices
/-- For [a first real square comparison matrix](hyp:P) and [a second real square
comparison matrix](hyp:Q), [the order-matrix condition](goal) requires
[the first matrix to be positive semidefinite](step:1) and [the second matrix to
be positive semidefinite](step:2). -/
def OrderMatrices
    (P Q : Matrix ι ι ℝ) : Prop := -- @realizes Q(real square comparison carrier)
  P.PosSemidef ∧ -- @realizes P(positive semidefinite comparison matrix)
  Q.PosSemidef -- @realizes Q(positive semidefinite matrix on the same space)

-- @node: ass:order-factor
/-- For [a real comparison factor](hyp:a), [the order-factor condition means that
the factor is at least one](goal).

@realizes a(real comparison factor at least one) -/
def OrderFactor (a : ℝ) : Prop := 1 ≤ a

-- @node: ass:order-comparison
/-- For [a real square matrix to be bounded](hyp:P), [a real square comparison
matrix](hyp:Q), and [a real scaling factor](hyp:a), [the order comparison means
that the scaled comparison matrix minus the first matrix is positive
semidefinite](goal). -/
def OrderComparison (P Q : Matrix ι ι ℝ) (a : ℝ) : Prop := (a • Q - P).PosSemidef

-- @node: ass:order-direction
/-- For [a real square base matrix](hyp:P) and [a real square direction matrix](hyp:K),
[being an order direction](goal) means that [the direction is symmetric](step:1)
and [annihilates the base matrix's kernel](step:2). -/
def OrderDirection (P K : Matrix ι ι ℝ) : Prop := K.IsSymm ∧ AnnihilatesKernel P K

-- @node: ass:gap-positive
/-- For [a real square midpoint matrix](hyp:T), [the gap-positivity condition
means that this matrix is positive semidefinite](goal).

@realizes T(real positive semidefinite midpoint matrix) -/
def GapPositive (T : Matrix ι ι ℝ) : Prop :=
  T.PosSemidef -- @realizes T(positive semidefinite real square carrier)

-- @node: ass:gap-symmetry
/-- For [a real square midpoint perturbation](hyp:U), [the gap-symmetry condition
means that the perturbation is symmetric](goal).

@realizes U(real symmetric midpoint perturbation) -/
def GapSymmetry (U : Matrix ι ι ℝ) : Prop :=
  U.IsSymm -- @realizes U(symmetric real square carrier)

-- @node: ass:gap-order
/-- For [a real square midpoint matrix](hyp:T) and [a real square perturbation](hyp:U),
[the gap-order condition](goal) requires [the midpoint plus the perturbation to
be positive semidefinite](step:1) and [the midpoint minus the perturbation to be
positive semidefinite](step:2). -/
def GapOrder (T U : Matrix ι ι ℝ) : Prop := (T + U).PosSemidef ∧ (T - U).PosSemidef

-- @node: def:row-star
/-- For [an outgoing real edge matrix](hyp:W) and [an incoming real edge matrix](hyp:V),
[the row star is the horizontal concatenation of the outgoing matrix and the
transpose of the incoming matrix](goal).

@realizes H_v(finite Euclidean coordinate spaces indexed by ι, κ, η)
@realizes W_v(real edge maps from the next vertex)
@realizes R_v(concatenation of the two incident edges)
@realizes \oplus(orthogonal direct sum represented by Sum indices) -/
def rowStar (W : Matrix ι κ ℝ) (V : Matrix η ι ℝ) : Matrix ι (κ ⊕ η) ℝ :=
  Matrix.fromCols W V.transpose

/-- For [a real rectangular matrix](hyp:R), [its row Gram matrix is its transpose
multiplied by the matrix itself](goal).

@realizes T_v(row-star Gram operator) -/
def rowGram (R : Matrix ι κ ℝ) : Matrix κ κ ℝ := R.transpose * R

-- @node: def:trace-perturbation
/-- For [a real rectangular row matrix](hyp:R) and [a real square vertex
matrix](hyp:D), [the row perturbation is the vertex matrix multiplied on the left
by the transpose of the row matrix and on the right by the row matrix](goal).

@realizes U_v(compression of a vertex contraction by its row star) -/
def rowPerturbation (R : Matrix ι κ ℝ) (D : Matrix ι ι ℝ) : Matrix κ κ ℝ :=
  R.transpose * D * R

-- @node: rowGram_isHermitian
/-- For [a real rectangular matrix](hyp:R), [the Gram matrix obtained by multiplying
its transpose by itself is symmetric, hence Hermitian](goal). -/
lemma rowGram_isHermitian {α β : Type*} [Fintype α] (R : Matrix α β ℝ) :
    (rowGram R).IsHermitian := by
  simpa only [rowGram, conjTranspose_eq_transpose_of_trivial] using
    Matrix.isHermitian_conjTranspose_mul_self R

-- @node: ass:trace-symmetry
/-- For [a real square matrix at the first vertex](hyp:D₀), [one at the second
vertex](hyp:D₁), and [one at the third vertex](hyp:D₂), [trace symmetry](goal)
requires [the first matrix to be symmetric](step:1), [the second matrix to be
symmetric](step:2), and [the third matrix to be symmetric](step:3). -/
def TraceSymmetry (D₀ : Matrix ι ι ℝ) (D₁ : Matrix κ κ ℝ)
    (D₂ : Matrix η η ℝ) : Prop :=
  D₀.IsSymm ∧ D₁.IsSymm ∧ D₂.IsSymm -- @realizes D_v(symmetric vertex maps)

-- @node: ass:trace-contraction
/-- For [a real square matrix at the first vertex](hyp:D₀), [one at the second
vertex](hyp:D₁), and [one at the third vertex](hyp:D₂), [the trace-contraction
condition](goal) requires positive semidefiniteness of [the identity minus the
first matrix](step:1), [the identity plus the first matrix](step:2), [the identity
minus the second matrix](step:3), [the identity plus the second matrix](step:4),
[the identity minus the third matrix](step:5), and [the identity plus the third
matrix](step:6).

@realizes D_v(spectral contractions; under symmetry equivalent to operator norm at most one) -/
def TraceContraction (D₀ : Matrix ι ι ℝ) (D₁ : Matrix κ κ ℝ)
    (D₂ : Matrix η η ℝ) : Prop :=
  (1 - D₀).PosSemidef ∧ (1 + D₀).PosSemidef ∧
  (1 - D₁).PosSemidef ∧ (1 + D₁).PosSemidef ∧
  (1 - D₂).PosSemidef ∧ (1 + D₂).PosSemidef

-- @env: S2
variable (k m : ℤ) -- @realizes k(integer dyadic scale) @realizes m(integer atom scale)

-- @node: def:nonnegative-domain
/-- [The nonnegative half-line is the set of real numbers greater than or equal
to zero](goal).

@realizes \R_+(closed nonnegative half-line) -/
def Rplus : Set ℝ := Set.Ici 0

/-- [Quadrant measure is two-dimensional Lebesgue measure restricted to pairs of
nonnegative real numbers](goal). -/
noncomputable def quadrantMeasure : Measure (ℝ × ℝ) := volume.restrict (Rplus ×ˢ Rplus)

-- @node: def:dyadic-intervals
/-- For [an integer scale](hyp:k) and [a nonnegative integer interval index](hyp:n),
[the dyadic interval runs from the index times two raised to the scale to the next
index times two raised to the scale, including the left endpoint and excluding the
right endpoint](goal).

@realizes I(half-open dyadic interval)
@realizes n_I(nonnegative interval index) -/
def dyadicInterval (n : ℕ) : Set ℝ :=
  Set.Ico ((2 : ℝ) ^ k * n) ((2 : ℝ) ^ k * (n + 1))

/-- For [an integer scale](hyp:k), [the dyadic interval family consists of all
half-open intervals at that scale with nonnegative integer indices](goal).

@realizes \cD_k(family of dyadic intervals indexed by natural numbers) -/
def dyadicIntervals : Set (Set ℝ) := Set.range (dyadicInterval k)

-- @node: def:haar-sign
/-- For [an integer scale](hyp:k), [a nonnegative integer interval index](hyp:n),
and [a real evaluation point](hyp:x), [the Haar sign is the indicator of the left
half of the dyadic interval minus the indicator of its right half, evaluated at
that point](goal).

@realizes h_I(left-half indicator minus right-half indicator) -/
noncomputable def haarSign (n : ℕ) (x : ℝ) : ℝ :=
  (dyadicInterval (k - 1) (2 * n)).indicator (fun _ => (1 : ℝ)) x -
  (dyadicInterval (k - 1) (2 * n + 1)).indicator (fun _ => (1 : ℝ)) x

-- @node: def:xor
/-- For [a first natural number](hyp:a), [a second natural number](hyp:b), and
[a third natural number](hyp:c), [their triple XOR is the bitwise exclusive-or
of the three numbers](goal).

@realizes \oplus(bitwise XOR of natural numbers) -/
def xor3 (a b c : ℕ) : ℕ := a ^^^ b ^^^ c

-- @node: def:admissible-triples
/-- For [a triple of nonnegative interval indices](hyp:n), [admissibility means
that the bitwise exclusive-or of its three indices is zero](goal). -/
def IsAdmissible (n : Fin 3 → ℕ) : Prop := xor3 (n 0) (n 1) (n 2) = 0

/-- For [a triple of nonnegative interval indices](hyp:n), [admissibility is
decidable by checking whether the bitwise exclusive-or of the three indices
equals zero](goal). -/
instance (n : Fin 3 → ℕ) : Decidable (IsAdmissible n) :=
  inferInstanceAs (Decidable (xor3 (n 0) (n 1) (n 2) = 0))

/-- [The admissible set consists of all triples of nonnegative interval indices
whose bitwise exclusive-or is zero](goal).

@realizes \cA_k(XOR-admissible interval-index triples, with scale carried separately)
@realizes \mathbf I(triple represented by its three natural interval indices) -/
def admissibleSet : Set (Fin 3 → ℕ) := {n | IsAdmissible n}

-- @node: ass:pin-1
/-- [The Haar-halves convention](goal) requires, at every integer scale and
nonnegative interval index, [the Haar sign to equal one on the left half of the
dyadic interval](step:1) and [to equal minus one on the right half](step:2), with
both halves including their left endpoints and excluding their right endpoints. -/
def HaarHalvesConvention : Prop := ∀ (j : ℤ) (n : ℕ) (x : ℝ),
  (x ∈ Set.Ico ((2 : ℝ)^j * n) ((2 : ℝ)^j * n + (2 : ℝ)^(j-1)) →
    haarSign j n x = 1) ∧
  (x ∈ Set.Ico ((2 : ℝ)^j * n + (2 : ℝ)^(j-1)) ((2 : ℝ)^j * (n+1)) →
    haarSign j n x = -1)

-- @node: def:local-form
/-- For [an integer scale](hyp:k), [a triple of nonnegative interval indices](hyp:n),
and [three real functions of two real variables](hyp:F), [the local form is the
integral over the three indexed dyadic intervals of the functions evaluated on
successive coordinate pairs around a triangle, multiplied by the three Haar
signs and multiplied by two raised to the negative scale](goal).

@realizes L_{\mathbf I}(normalized trilinear integral over the three dyadic intervals) -/
noncomputable def localForm (n : Fin 3 → ℕ) (F : Fin 3 → ℝ × ℝ → ℝ) : ℝ :=
  (2 : ℝ)^(-k) * ∫ x in dyadicInterval k (n 0) ×ˢ
      (dyadicInterval k (n 1) ×ˢ dyadicInterval k (n 2)),
    F 0 (x.1, x.2.1) * F 1 (x.2.1, x.2.2) * F 2 (x.2.2, x.1) *
    haarSign k (n 0) x.1 * haarSign k (n 1) x.2.1 * haarSign k (n 2) x.2.2

-- @node: ass:step-bounded
/-- For [three real functions of two real variables](hyp:F), [step boundedness
means that each function has a finite real bound on its absolute value throughout
the nonnegative quadrant](goal).

@realizes F_v(real functions on the quadrant, bounded there) -/
def StepBounded (F : Fin 3 → ℝ × ℝ → ℝ) : Prop :=
  ∀ v, ∃ C : ℝ, ∀ x ∈ Rplus ×ˢ Rplus, |F v x| ≤ C

-- @node: ass:step-compact
/-- For [three real functions of two real variables](hyp:F), [step compactness
means that each function vanishes in the nonnegative quadrant whenever either
coordinate exceeds some real bound specific to that function](goal). -/
def StepCompact (F : Fin 3 → ℝ × ℝ → ℝ) : Prop :=
  ∀ v, ∃ R : ℝ, ∀ x : ℝ × ℝ, 0 ≤ x.1 → 0 ≤ x.2 →
    (R < x.1 ∨ R < x.2) → F v x = 0 -- @realizes F_v(compact support in the quadrant)

-- @node: ass:step-atoms
/-- For [three real functions of two real variables](hyp:F) and [an integer atom
scale](hyp:m), [the step-atom condition means that each function takes the same
value at any two points in the same rectangle formed from two dyadic intervals
at that scale](goal). -/
def StepAtoms (F : Fin 3 → ℝ × ℝ → ℝ) (m : ℤ) : Prop :=
  ∀ v (a b : ℕ) (x y : ℝ × ℝ),
    x ∈ dyadicInterval m a ×ˢ dyadicInterval m b →
    y ∈ dyadicInterval m a ×ˢ dyadicInterval m b →
      F v x = F v y -- @realizes F_v(constant on every scale-m atom rectangle)

-- @node: ass:main-scales
/-- For [a set of integer scales](hyp:S), [the main-scale condition means that
this set is finite](goal).

@realizes S(finite set of integer scales) -/
def MainScales (S : Set ℤ) : Prop := S.Finite

-- @node: ass:main-inputs
/-- For [three real functions of two real variables](hyp:F), [the main-input
condition](goal) requires each function to [be measurable after extension by zero
outside the nonnegative quadrant](step:1), [have a finite real bound on its
absolute value on that quadrant](step:2), and [vanish there whenever either
coordinate exceeds some real bound specific to that function](step:3). -/
def MainInputs (F : Fin 3 → ℝ × ℝ → ℝ) : Prop := ∀ v,
  Measurable ((Rplus ×ˢ Rplus).indicator (F v)) ∧ -- @realizes F_v(measurable on the quadrant)
  (∃ C : ℝ, ∀ x ∈ Rplus ×ˢ Rplus, |F v x| ≤ C) ∧ -- @realizes F_v(bounded on the quadrant)
  (∃ R : ℝ, ∀ x ∈ Rplus ×ˢ Rplus,
    (R < x.1 ∨ R < x.2) → F v x = 0) -- @realizes F_v(compact support in the quadrant)

-- @node: ass:increase-triple
/-- For [a triple of nonnegative interval indices](hyp:n), [the increase-triple
condition means that the triple is admissible: its three indices have bitwise
exclusive-or zero](goal). -/
def IncreaseTriple (n : Fin 3 → ℕ) : Prop := IsAdmissible n

-- @node: ass:increase-scale
/-- For [an integer atom scale](hyp:m) and [an integer comparison scale](hyp:k),
[the increase-scale condition means that the comparison scale is at least one
greater than the atom scale](goal). -/
def IncreaseScale : Prop := m + 1 ≤ k

-- @node: ass:total-scale
/-- For [an integer atom scale](hyp:m) and [an integer comparison scale](hyp:k),
[the total-scale condition requires the atom scale to be no greater than the
comparison scale](goal). -/
def TotalScale : Prop := m ≤ k

-- @node: ass:total-telescope-scale
/-- For [an integer atom scale](hyp:m) and [an integer comparison scale](hyp:k),
[the total-telescope scale condition requires the comparison scale to be at least
one greater than the atom scale](goal). -/
def TotalTelescopeScale : Prop := m + 1 ≤ k

-- @node: ass:continuity-scale
/-- For [an integer scale](hyp:k), [the continuity-scale condition allows every
integer value of that scale](goal). -/
def ContinuityScale : Prop := k ∈ (Set.univ : Set ℤ)

-- @node: ass:continuity-inputs
/-- For [three real-valued functions of two real variables](hyp:F), [the
continuity-input condition requires each function to be measurable up to a set
of measure zero and to have finite integral of its absolute value cubed, with
respect to Lebesgue measure on the nonnegative quadrant](goal).

@realizes F_v(real L3 functions with respect to quadrant Lebesgue measure) -/
def ContinuityInputs (F : Fin 3 → ℝ × ℝ → ℝ) : Prop :=
  ∀ v, MemLp (F v) 3 quadrantMeasure

/-- [The child-bit set consists of all triples of zero-or-one half-selection
bits whose bitwise exclusive-or is zero](goal).

@realizes b_v(three half-selection bits, each in Fin 2)
@realizes v(cyclic vertex index in Fin 3) -/
def childBits : Finset (Fin 3 → Fin 2) :=
  Finset.univ.filter (fun b => xor3 (b 0).val (b 1).val (b 2).val = 0)

/-- For [a zero-or-one half-selection bit](hyp:b), [the child sign is one when
the bit is zero and minus one when it is one](goal).

@realizes s_v(sign determined by a half-selection bit) -/
def childSign (b : Fin 2) : ℝ := (-1 : ℝ) ^ b.val

-- @node: def:children
/-- For [a triple of nonnegative interval indices](hyp:n), [the children are the
four triples obtained by doubling each index and adding its corresponding
half-selection bit, using all bit triples whose bitwise exclusive-or is
zero](goal).

@realizes \operatorname{ch}(\mathbf I)(four XOR-admissible half-interval children) -/
def children (n : Fin 3 → ℕ) : Finset (Fin 3 → ℕ) :=
  childBits.image (fun b v => 2 * n v + (b v).val)

end Papers.OaiBoundDyadicTriangular
