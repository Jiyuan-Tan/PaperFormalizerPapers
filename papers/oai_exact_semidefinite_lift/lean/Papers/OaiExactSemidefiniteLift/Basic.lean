module

public import Mathlib.Algebra.Star.Module
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Logic.Equiv.Fin.Basic
public import Toolkit.Foundations.Algebra.HyperbolicPolynomials
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.TrigPoly

/-!
# Concrete matrices for the exact semidefinite lift

The setting is deterministic. Symmetric matrices are the real self-adjoint
submodule; all pencils below use the displayed matrices of the paper.
-/

@[expose] public section

noncomputable section

namespace Papers.OaiExactSemidefiniteLift

open Matrix
open scoped BigOperators

/-- For [a dimension n](hyp:n), [the matrix space](goal) consists of real n-by-n matrices. -/
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
/-- For [a dimension n](hyp:n), [the symmetric matrix space](goal) is the real vector
subspace of self-adjoint n-by-n real matrices. -/
abbrev Sym (n : ℕ) := selfAdjoint.submodule ℝ (Mat n)
-- @realizes \Sym^n(real self-adjoint matrix submodule)
/-- [The space of symmetric 4-by-4 matrices](goal) consists of real self-adjoint matrices. -/
abbrev Sym4 := Sym 4
/-- [The space of symmetric 3-by-3 matrices](goal) consists of real self-adjoint matrices. -/
abbrev Sym3 := Sym 3
/-- [The ambient space](goal) consists of triples comprising two real symmetric
4-by-4 matrices and a real three-vector. -/
abbrev V := Sym4 × Sym4 × (Fin 3 → ℝ)
-- @realizes \mathcal V(two symmetric matrices and a real three-vector)

-- @env: S1
variable (θ η ξ : ℝ)
-- @realizes \theta(real angle)
-- @realizes \eta(real plane coefficient)
-- @realizes \xi(real vertical coefficient)

-- @node: def:closed-cone
/-- Given [a real-valued function p on a real vector space](hyp:p) and
[a direction e in that space](hyp:e), [the closed hyperbolicity cone](goal) is the
hyperbolicity cone of p in direction e, defined by nonnegative characteristic roots. -/
abbrev closedCone {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : E → ℝ) (e : E) : Set E :=
  Toolkit.Foundations.Algebra.hyperbolicityCone p e
  -- @realizes K(p,e)(closed cone with nonnegative characteristic roots)

-- @node: def:q
/-- For [a real three-vector y](hyp:y), [the quadratic matrix Q(y)](goal) has diagonal
entries y₀² + y₁², y₁² + y₂², y₂² + y₀² and off-diagonal entries −yᵢyⱼ. -/
def Qmat (y : Fin 3 → ℝ) : Mat 3 :=
  -- @realizes Q(explicit quadratic matrix)
  -- @realizes y(real three-vector)
  !![y 0 ^ 2 + y 1 ^ 2, -y 0 * y 1, -y 0 * y 2;
     -y 0 * y 1, y 1 ^ 2 + y 2 ^ 2, -y 1 * y 2;
     -y 0 * y 2, -y 1 * y 2, y 2 ^ 2 + y 0 ^ 2]

-- @node: def:phi
/-- For [a real three-vector y](hyp:y) and [a real 4-by-4 matrix W](hyp:W),
[the block map Φᵧ(W)](goal) extracts [the upper-left entry a](step:1),
[the last three entries r of the first column](step:2), and
[the lower-right 3-by-3 block T](step:3), then returns
[the matrix with blocks tr(Q(y)T), −rᵀQ(y), −Q(y)r, and aQ(y)](step:4). -/
def PhiMap (y : Fin 3 → ℝ) (W : Mat 4) : Mat 4 := -- @realizes \Phi_y(explicit block linear map)
  let a := W 0 0 -- @realizes a(real upper-left block)
  let r : Fin 3 → ℝ := fun i => W i.succ 0 -- @realizes r(real off-diagonal column)
  let T : Mat 3 := fun i j => W i.succ j.succ
  -- @realizes T(lower-right symmetric block when W is symmetric)
  Matrix.of fun i j =>
    Fin.cases (Fin.cases (Qmat y * T).trace (fun j => - ∑ l, r l * Qmat y l j) j)
      (fun i => Fin.cases (- ∑ l, Qmat y i l * r l) (fun j => a * Qmat y i j) j) i

-- @node: def:p
/-- For [an ambient triple x = (X, Z, y)](hyp:x), [the determinant polynomial p(x)](goal)
is the determinant of det(X)Z − Φᵧ(adj(X)), where adj(X) is the adjugate of X. -/
def pPoly (x : V) : ℝ := -- @realizes p(determinant polynomial) @realizes x(ambient triple)
  ((x.1 : Mat 4).det • (x.2.1 : Mat 4) - PhiMap x.2.2 (x.1 : Mat 4).adjugate).det

/-- [The symmetric identity matrix](goal) is the real 4-by-4 identity, regarded as
an element of the symmetric matrix space. -/
def identity4 : Sym4 := ⟨1, IsSelfAdjoint.one (Mat 4)⟩ -- @realizes I_4(real symmetric identity)
/-- [The distinguished direction e](goal) is the ambient triple consisting of two
4-by-4 identity matrices and the zero three-vector. -/
def eDir : V := (identity4, identity4, 0) -- @realizes e(specified direction)

-- @node: def:cone
/-- [The cone K](goal) is the closed hyperbolicity cone of the determinant polynomial p
in the direction consisting of two identity matrices and a zero vector. -/
def coneK : Set V := closedCone pPoly eDir -- @realizes K(closed hyperbolicity cone)

/-- [The upper-triangular index list](goal) enumerates the ten positions of a 4-by-4
matrix on or above the diagonal in lexicographic order, starting with (0, 0). -/
def upperIdx : Fin 10 → Fin 4 × Fin 4 :=
  ![(0,0), (0,1), (0,2), (0,3), (1,1), (1,2), (1,3), (2,2), (2,3), (3,3)]

/-- For [a real 4-by-4 matrix X](hyp:X), [its upper-triangular coordinate vector](goal)
lists the ten entries on or above the diagonal in lexicographic order. -/
def upperCoords (X : Mat 4) : Fin 10 → ℝ := fun i => X (upperIdx i).1 (upperIdx i).2

-- @node: def:coordinates
/-- For [an ambient triple x = (X, Z, y)](hyp:x), [its 23 output coordinates](goal)
concatenate the ten upper-triangular entries of X, the ten upper-triangular entries
of Z, and the three entries of y, in that order. -/
def outputCoords (x : V) : Fin 23 → ℝ :=
  Fin.append (upperCoords (x.1 : Mat 4))
    (Fin.append (upperCoords (x.2.1 : Mat 4)) x.2.2)

-- @node: def:angular-coordinates
/-- For [a real angle θ](hyp:θ), [the planar unit direction d(θ)](goal) is
the three-vector (cos θ, sin θ, 0). -/
def dVec (θ : ℝ) : Fin 3 → ℝ := ![Real.cos θ, Real.sin θ, 0]
-- @realizes d(\theta)(planar unit direction)

/-- [The vertical unit vector k](goal) is the three-vector (0, 0, 1). -/
def kVec : Fin 3 → ℝ := ![0, 0, 1] -- @realizes k(vertical unit vector)
/-- For [a real angle θ](hyp:θ), [the scalar c](goal) is cos θ. -/
def cosine (θ : ℝ) : ℝ := Real.cos θ -- @realizes c(cosine)
/-- For [a real angle θ](hyp:θ), [the scalar s](goal) is sin θ. -/
def sine (θ : ℝ) : ℝ := Real.sin θ -- @realizes s(sine)
/-- For [a real angle θ](hyp:θ), [the unit complex phase w](goal) is exp(iθ). -/
def wPhase (θ : ℝ) : ℂ := Complex.exp (θ * Complex.I) -- @realizes w(unit complex phase)

-- @node: def:angular-plane
/-- For [a real angle θ](hyp:θ), [a planar coefficient η](hyp:η), and
[a vertical coefficient ξ](hyp:ξ), [the plane parametrization Yθ(η, ξ)](goal)
is η(cos θ, sin θ, 0) + ξ(0, 0, 1). -/
def Yplane (θ η ξ : ℝ) : Fin 3 → ℝ := η • dVec θ + ξ • kVec
-- @realizes Y_\theta(specified real plane parametrization)

-- @node: def:realification
/-- For [a complex 3-by-2 matrix F](hyp:F), [its realification](goal) is the real
3-by-4 matrix whose columns are, in order, the real and imaginary parts of the
first column and then the real and imaginary parts of the second column. -/
def realify (F : Matrix (Fin 3) (Fin 2) ℂ) : Matrix (Fin 3) (Fin 4) ℝ :=
  -- @realizes F(complex three-by-two matrix)
  -- @realizes \widetilde F(interleaved real and imaginary columns)
  fun i => ![(F i 0).re, (F i 0).im, (F i 1).re, (F i 1).im]

/-- For [a complex 3-by-2 matrix F](hyp:F), [the first column vector](goal)
consists of its three entries in the first column. -/
def firstColumn (F : Matrix (Fin 3) (Fin 2) ℂ) : Fin 3 → ℂ := fun i => F i 0
-- @realizes f_1(first complex column)
/-- For [a complex 3-by-2 matrix F](hyp:F), [the second column vector](goal)
consists of its three entries in the second column. -/
def secondColumn (F : Matrix (Fin 3) (Fin 2) ℂ) : Fin 3 → ℂ := fun i => F i 1
-- @realizes f_2(second complex column)

-- @node: def:u
/-- For [a real angle θ](hyp:θ), [the complex angular factor U(θ)](goal) has rows
(−w⁻¹, −w), (sin θ · w⁻², sin θ · w²), and (cos θ · w⁻², −cos θ · w²),
all scaled by 1/√2, where w = exp(iθ). -/
def Umat (θ : ℝ) : Matrix (Fin 3) (Fin 2) ℂ := -- @realizes U(\theta)(explicit angular factor)
  (1 / (Real.sqrt 2 : ℂ)) •
    !![-(wPhase θ)⁻¹, -wPhase θ;
       (Real.sin θ : ℂ) * ((wPhase θ)⁻¹)^2, (Real.sin θ : ℂ) * (wPhase θ)^2;
       (Real.cos θ : ℂ) * ((wPhase θ)⁻¹)^2, -(Real.cos θ : ℂ) * (wPhase θ)^2]

/-- [The constant complex factor V₀](goal) is the 3-by-2 matrix with rows
(0, 0), (i, i), and (1, 1), all scaled by 1/√2. -/
def V0 : Matrix (Fin 3) (Fin 2) ℂ := -- @realizes V_0(constant complex factor)
  (1 / (Real.sqrt 2 : ℂ)) • !![0, 0; Complex.I, Complex.I; 1, 1]

/-- For [a real angle θ](hyp:θ), [a planar coefficient η](hyp:η), and
[a vertical coefficient ξ](hyp:ξ), [the complex angular Gram factor Fθ(η, ξ)](goal)
is the linear combination ηU(θ) + ξV₀. -/
def Fθ (θ η ξ : ℝ) : Matrix (Fin 3) (Fin 2) ℂ := -- @realizes F_\theta(angular Gram factor)
  (η : ℂ) • Umat θ + (ξ : ℂ) • V0

/-- For [a real angle θ](hyp:θ), [a planar coefficient η](hyp:η), and
[a vertical coefficient ξ](hyp:ξ), [the real angular Gram factor](goal)
is the realification of ηU(θ) + ξV₀, with real and imaginary columns interleaved. -/
def realFθ (θ η ξ : ℝ) := realify (Fθ θ η ξ)
-- @realizes \widetilde F_\theta(real angular Gram factor)

-- @node: def:bj
/-- For [a real three-vector r](hyp:r), [the skew-symmetric matrix B(r)](goal)
is the 4-by-4 block matrix with upper-left entry zero, upper-right row rᵀ,
lower-left column −r, and lower-right block zero. -/
def Bskew (r : Fin 3 → ℝ) : Mat 4 := -- @realizes B(r)(explicit skew matrix)
  fun i j => Fin.cases (Fin.cases 0 (fun j => r j) j)
    (fun i => Fin.cases (-r i) (fun _ => 0) j) i

/-- For [a real four-vector u](hyp:u), [the matrix Jᵤ](goal) is the 3-by-4 block
matrix whose first column is the last three coordinates of u and whose remaining
block is −u₀ times the 3-by-3 identity. -/
def Ju (u : Fin 4 → ℝ) : Matrix (Fin 3) (Fin 4) ℝ :=
  -- @realizes J_u(vector block map)
  -- @realizes u(real four-vector)
  fun i j => Fin.cases (u i.succ) (fun j => -u 0 * (1 : Mat 3) i j) j

/-- For [a real four-vector u](hyp:u), [its head coordinate](goal) is its first entry u₀. -/
def uHead (u : Fin 4 → ℝ) : ℝ := u 0 -- @realizes u_0(first coordinate)
/-- For [a real four-vector u](hyp:u), [its tail vector](goal) consists of its last
three coordinates in their original order. -/
def uTail (u : Fin 4 → ℝ) : Fin 3 → ℝ := fun i => u i.succ -- @realizes u'(last three coordinates)
/-- For [a real angle θ](hyp:θ), [a planar coefficient η](hyp:η),
[a vertical coefficient ξ](hyp:ξ), and [a column index j from zero to three](hyp:j),
[the factor column rⱼ](goal) is column j of the realification of ηU(θ) + ξV₀. -/
def factorColumn (θ η ξ : ℝ) (j : Fin 4) : Fin 3 → ℝ :=
  -- @realizes r_j(columns of the real angular factor)
  fun i => realify (Fθ θ η ξ) i j

/-- For [a real angle θ](hyp:θ), [a planar coefficient η](hyp:η),
[a vertical coefficient ξ](hyp:ξ), and [a real 4-by-4 matrix W](hyp:W),
[the factor sum](goal) is the sum of B(rⱼ)ᵀWB(rⱼ) over the four columns rⱼ
of the real angular Gram factor. -/
def phiFactorSum (θ η ξ : ℝ) (W : Mat 4) : Mat 4 :=
  ∑ j : Fin 4, (Bskew (factorColumn θ η ξ j))ᵀ * W * Bskew (factorColumn θ η ξ j)

/-- For [a real three-vector y](hyp:y), [a real four-vector u](hyp:u), and
[a real 4-by-4 matrix W](hyp:W), [the scalar quadratic-form expression](goal)
is the trace of JᵤWJᵤᵀQ(y). -/
def phiQuadraticForm (y : Fin 3 → ℝ) (u : Fin 4 → ℝ) (W : Mat 4) : ℝ :=
  (Ju u * W * (Ju u)ᵀ * Qmat y).trace

/-- [The slice index set](goal) is the disjoint union of sixteen ordered pairs
of indices from zero to three and four individual indices from zero to three. -/
abbrev SliceIndex := (Fin 4 × Fin 4) ⊕ Fin 4

/-- [The slice index correspondence](goal) labels a pair (j, k) by 4j + k and
an individual index k by 16 + k, giving a bijection with the integers from zero to nineteen. -/
def sliceIndexEquiv : SliceIndex ≃ Fin 20 :=
  (Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin 4))).trans finSumFinEquiv

/-- For [a real angle θ](hyp:θ), [a planar coefficient η](hyp:η), and
[a vertical coefficient ξ](hyp:ξ), [the 16-by-4 slice block](goal) vertically
stacks the four skew-symmetric matrices B(rⱼ), where rⱼ are the columns of the
real angular Gram factor. -/
def sliceB (θ η ξ : ℝ) : Matrix (Fin 4 × Fin 4) (Fin 4) ℝ :=
  -- @realizes \mathcal B_\theta(stack of four skew blocks)
  fun ji k => Bskew (factorColumn θ η ξ ji.1) ji.2 k

/-- For [a real angle θ](hyp:θ), [a real 4-by-4 matrix X](hyp:𝒳),
[a real 4-by-4 matrix Z](hyp:𝒵), [a planar coefficient η](hyp:η), and
[a vertical coefficient ξ](hyp:ξ), [the raw 20-by-20 slice pencil](goal) has
four copies of X on the upper-left block diagonal, the slice block Bθ(η, ξ)
in the upper-right, its transpose in the lower-left, and Z in the lower-right. -/
def slicePencilRaw (θ : ℝ) (𝒳 𝒵 : Mat 4) (η ξ : ℝ) : Matrix SliceIndex SliceIndex ℝ :=
  Matrix.fromBlocks (Matrix.kronecker (1 : Mat 4) 𝒳) (sliceB θ η ξ) (sliceB θ η ξ)ᵀ 𝒵

-- @node: def:slice-pencil
/-- For [a real angle θ](hyp:θ), [a real symmetric 4-by-4 matrix X](hyp:𝒳),
[a real symmetric 4-by-4 matrix Z](hyp:𝒵), [a planar coefficient η](hyp:η), and
[a vertical coefficient ξ](hyp:ξ), [the symmetric 20-by-20 slice pencil](goal)
has four copies of X on the upper-left block diagonal, the slice block Bθ(η, ξ)
in the upper-right, its transpose in the lower-left, and Z in the lower-right. -/
def slicePencil (θ : ℝ) (𝒳 𝒵 : Sym4) (η ξ : ℝ) : Matrix SliceIndex SliceIndex ℝ :=
  -- @realizes L_\theta(explicit twenty-by-twenty symmetric pencil)
  -- @realizes \mathcal X(symmetric slice matrix)
  -- @realizes \mathcal Z(symmetric slice matrix)
  slicePencilRaw θ 𝒳 𝒵 η ξ

/-- For [a real angle θ](hyp:θ), [a real symmetric 4-by-4 matrix X](hyp:𝒳),
[a real symmetric 4-by-4 matrix Z](hyp:𝒵), [a planar coefficient η](hyp:η), and
[a vertical coefficient ξ](hyp:ξ), [the numerically indexed slice pencil](goal)
is the 20-by-20 slice pencil with both rows and columns relabeled from zero to
nineteen, placing the sixteen paired indices before the four individual indices. -/
def slicePencil20 (θ : ℝ) (𝒳 𝒵 : Sym4) (η ξ : ℝ) : Mat 20 :=
  fun i j => slicePencil θ 𝒳 𝒵 η ξ (sliceIndexEquiv.symm i) (sliceIndexEquiv.symm j)

-- @node: def:polarization
/-- For [a real three-vector y](hyp:y) and [a real three-vector z](hyp:z),
[the bilinear polarization of Q](goal) is one half of Q(y + z) − Q(y) − Q(z). -/
def Qpol (y z : Fin 3 → ℝ) : Mat 3 := -- @realizes Q(y,z)(symmetric bilinear polarization)
  (1 / 2 : ℝ) • QuadraticMap.polar Qmat y z

-- @node: def:weighted-pairing
/-- For [a real symmetric 3-by-3 weight matrix S, without a positivity restriction](hyp:S)
and [a complex 3-by-2 matrix F](hyp:F) and [a complex 3-by-2 matrix H](hyp:H),
[their weighted real pairing](goal) is the trace of the transpose of the
realification of F multiplied by S and by the realification of H. -/
def weightedPairing (S : Sym3) -- @realizes S(arbitrary real symmetric weight; no PSD restriction)
    (F H : Matrix (Fin 3) (Fin 2) ℂ) : ℝ :=
  -- @realizes \langle F,H\rangle_S(real trace pairing)
  -- @realizes H(complex pairing argument)
  ((realify F)ᵀ * (S : Mat 3) * realify H).trace

-- @node: def:trigonometric-spaces
/-- [The real trigonometric-polynomial predicate](goal) says that a real-valued
function is, at every real argument, a sum of sine and cosine terms with real
coefficients and integer frequencies from zero through a given natural-number
degree bound. -/
abbrev IsTrigPolyLE := Causalean.Mathlib.Analysis.BernsteinSzegoTrig.IsTrigPolyLE
-- @realizes \mathcal T_j(real degree-bounded trigonometric space)

-- @node: def:complex-trigonometric-polynomials
/-- For [a natural-number degree bound j](hyp:j) and [a complex-valued function f
of a real argument](hyp:f), [the complex trigonometric-polynomial predicate](goal)
means that complex coefficients exist for which f(θ) equals the sum of
cℓ exp(iℓθ) over integer frequencies ℓ from −j to j, at every real angle θ. -/
def IsComplexTrigPolyLE (j : ℕ) (f : ℝ → ℂ) : Prop :=
  ∃ c : ℤ → ℂ, ∀ θ, f θ = ∑ ℓ ∈ Finset.Icc (-(j : ℤ)) (j : ℤ),
    c ℓ * Complex.exp ((ℓ : ℂ) * θ * Complex.I)

-- @node: ass:matching
/-- For [a real three-vector z](hyp:z), [matching nondegeneracy](goal) means that
its first two coordinates are not both zero. -/
def MatchingNondegenerate (z : Fin 3 → ℝ) : Prop :=
  -- @realizes z(real three-vector with nonzero planar part)
  (z 0, z 1) ≠ (0, 0)

-- @node: ass:slice-positive-definite
/-- For [a real symmetric 4-by-4 matrix X](hyp:𝒳), [slice positive definiteness](goal)
means that X is positive definite. -/
def SlicePosDef (𝒳 : Sym4) : Prop := (𝒳 : Mat 4).PosDef

-- @node: ass:pin-2
/-- [The complex trigonometric-polynomial representation condition](goal) asserts
that, for every natural-number degree bound j and every complex-valued function f
of a real argument, f is a complex trigonometric polynomial of degree at most j
if and only if complex coefficients represent f(θ) as the sum of cℓ exp(iℓθ)
over integer frequencies ℓ from −j to j at every real angle θ. -/
def ComplexTrigPolyPinned : Prop :=
  ∀ (j : ℕ) (f : ℝ → ℂ), IsComplexTrigPolyLE j f ↔
    ∃ c : ℤ → ℂ, ∀ θ, f θ = ∑ ℓ ∈ Finset.Icc (-(j : ℤ)) (j : ℤ),
      c ℓ * Complex.exp ((ℓ : ℂ) * θ * Complex.I)

end Papers.OaiExactSemidefiniteLift
