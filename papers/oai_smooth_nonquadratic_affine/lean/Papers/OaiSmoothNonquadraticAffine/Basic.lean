module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Smooth nonquadratic affine maximal graphs: shared definitions

The ambient spaces have the Euclidean norm. Radial profiles are ambient real
functions restricted to their stated intervals. All positivity is pointwise.
The coordinate functions used under differentiation are extended by zero outside
the open domain where the paper's quotients are defined.
-/

@[expose] public section

noncomputable section

open Set Matrix
open scoped BigOperators RealInnerProductSpace Topology ContDiff

namespace OaiSmoothNonquadraticAffine

-- @env: S1
variable {m : ℕ} -- @realizes m(natural spatial dimension; positive via ReductionDimension)
variable {n : ℕ} -- @realizes n(natural graph dimension; m+1 in reduction and 10 in main)

/-- For [spatial dimension m](hyp:m) and [spatial coordinate i](hyp:i), the
[spatial basis vector](goal) has value one in coordinate i and zero elsewhere,
including in the final time coordinate. -/
def spatialBasis (m : ℕ) (i : Fin m) : EuclideanSpace ℝ (Fin (m + 1)) :=
  EuclideanSpace.single i.castSucc 1 -- @realizes e_i(standard spatial basis vector)

/-- For [spatial dimension m](hyp:m), the [time basis vector](goal) has value one
in the final coordinate of the space with m spatial coordinates and zero elsewhere. -/
def timeBasis (m : ℕ) : EuclideanSpace ℝ (Fin (m + 1)) :=
  EuclideanSpace.single (Fin.last m) 1 -- @realizes e_t(standard last-coordinate basis vector)

/-- For [a point z with m spatial coordinates and one time coordinate](hyp:z),
the [spatial projection](goal) retains the first m coordinates. -/
def xPart (z : EuclideanSpace ℝ (Fin (m + 1))) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun i => z i.castSucc) -- @realizes x(spatial coordinates in Euclidean space)

/-- For [a point z with m spatial coordinates and one time coordinate](hyp:z),
the [time projection](goal) is its last coordinate. -/
def tPart (z : EuclideanSpace ℝ (Fin (m + 1))) : ℝ :=
  z (Fin.last m) -- @realizes t(real last coordinate)

/-- For [a real-valued function u on Euclidean space](hyp:u) and [a point z](hyp:z),
the [Hessian matrix](goal) consists of the second partial derivatives of u at z
in the standard orthonormal basis. -/
def hessianMatrix (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (z : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun (i : Fin n) (j : Fin n) => -- @realizes i(Fin n) @realizes j(Fin n)
    fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.single j 1)) z
      (EuclideanSpace.single i 1) -- @realizes H(spatial Hessian when applied to F in dimension m)

-- @node: def:hessian-positivity
/-- For [a real-valued function u](hyp:u) and [a domain S](hyp:S),
[Hessian positivity](goal) means that the Hessian of u is positive definite at every point of S. -/
def HessianPositive (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (S : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ z ∈ S, -- @realizes w(positive-Hessian domain restriction)
    (hessianMatrix u z).PosDef -- @realizes u(pointwise Hessian positivity on its domain)

/-- For [a real-valued function u](hyp:u) and [a point z](hyp:z), the
[cofactor matrix](goal) is the adjugate of the Hessian of u at z.

For a positive definite Hessian, this equals its determinant times its inverse. -/
def cofactorMatrix (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (z : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  (hessianMatrix u z).adjugate -- @realizes U(cofactor matrix of the full Hessian)

/-- For [dimension n](hyp:n), [a real-valued function u on n-dimensional Euclidean
space](hyp:u), and [a point z](hyp:z), the [affine weight](goal) is the determinant
of the Hessian of u at z raised to the power −(n + 1)/(n + 2).

The ambient real-valued formula also supplies the extension used for differentiation. -/
def affineWeight (n : ℕ) (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (hessianMatrix u z).det ^ (-((n : ℝ) + 1) / ((n : ℝ) + 2)) -- @realizes w(determinant power)

/-- If [the Hessian of u is positive definite throughout S](hyp:hH) and
[z belongs to S](hyp:hz), then [the affine weight of u at z is strictly positive](goal). -/
lemma affineWeight_pos {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {S : Set (EuclideanSpace ℝ (Fin n))}
    (hH : HessianPositive u S) -- @realizes w(positive-Hessian domain constraint)
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ S) :
    0 < affineWeight n u z := by -- @realizes w(strictly positive range on the domain)
  exact Real.rpow_pos_of_pos (hH z hz).det_pos _

-- @node: def:affine-equation
/-- For [dimension n](hyp:n), [a real-valued function u](hyp:u), and [a domain S](hyp:S),
the [affine maximal equation](goal) requires that, at every point of S, the sum
over all coordinate pairs of the cofactor entries of the Hessian of u times the
corresponding Hessian entries of its affine weight equals zero. -/
def AffineMaximalEquation (n : ℕ) (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (S : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ z ∈ S, ∑ i, ∑ j, cofactorMatrix u z i j * hessianMatrix (affineWeight n u) z i j = 0

/-- For [spatial dimension m](hyp:m), the [reduction coefficient k](goal) equals m + 2. -/
def reductionK (m : ℕ) : ℝ :=
  (m : ℝ) + 2 -- @realizes k(dimension-dependent scalar m+2)

-- @node: def:reduction-parameters
/-- For [spatial dimension m](hyp:m), the [reduction exponent γ](goal) equals (m + 3)/(m + 2). -/
def reductionGamma (m : ℕ) : ℝ :=
  ((m : ℝ) + 3) / ((m : ℝ) + 2) -- @realizes \gamma(dimension-dependent exponent)

-- @node: ass:reduction-dimension
/-- For [a natural-number spatial dimension m](hyp:m), the [dimension condition](goal)
requires m to be at least one. -/
def ReductionDimension (m : ℕ) : Prop :=
  1 ≤ m -- @realizes m(positive integer spatial dimension)

-- @node: ass:reduction-functions
/-- For [a spatial domain Ω](hyp:Ω) and [real-valued spatial functions F and P](hyp:F,P),
the [reduction regularity and positivity condition](goal) requires [Ω to be open](step:1),
[F to be infinitely differentiable on Ω](step:2), [P to be infinitely differentiable
on Ω](step:3), and [both functions to be strictly positive throughout Ω](step:4). -/
def ReductionFunctions (Ω : Set (EuclideanSpace ℝ (Fin m)))
    (F P : EuclideanSpace ℝ (Fin m) → ℝ) : Prop :=
  IsOpen Ω ∧ -- @realizes \Omega(open spatial domain)
  ContDiffOn ℝ ∞ F Ω ∧ -- @realizes F(smooth spatial function on Omega)
  ContDiffOn ℝ ∞ P Ω ∧ -- @realizes P(smooth spatial function on Omega)
  ∀ x ∈ Ω, 0 < F x ∧ 0 < P x -- @realizes F(positive range) @realizes P(positive range)

-- @node: ass:reduction-hessian
/-- For [a spatial domain Ω](hyp:Ω) and [a real-valued spatial function F](hyp:F),
the [reduction Hessian condition](goal) requires the Hessian of F to be positive
definite throughout Ω. -/
def ReductionHessianPosDef (Ω : Set (EuclideanSpace ℝ (Fin m)))
    (F : EuclideanSpace ℝ (Fin m) → ℝ) : Prop :=
  HessianPositive F Ω -- @realizes H(pointwise positive definite spatial Hessian)

-- @node: ass:reduction-system
/-- For [spatial dimension m](hyp:m), [a domain Ω](hyp:Ω), and [spatial functions
F and P](hyp:F,P), the [reduced system](goal) requires, at every point of Ω,
[the Hessian determinant of F to equal F times P to the power −(m + 3)/(m + 2)](step:1)
and [the trace of the inverse Hessian of F times the Hessian of P, plus (m + 2)P/F,
to equal zero](step:2). -/
def ReducedSystem (m : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin m)))
    (F P : EuclideanSpace ℝ (Fin m) → ℝ) : Prop :=
  ∀ x ∈ Ω,
    (hessianMatrix F x).det = F x * P x ^ (-reductionGamma m) ∧ -- @realizes P(determinant relation)
    Matrix.trace ((hessianMatrix F x)⁻¹ * hessianMatrix P x) + reductionK m * P x / F x = 0

/-- For [a spatial function F](hyp:F) and [a point z with spatial and time coordinates](hyp:z),
the [reduction graph value](goal) is the square root of the sum of the squared
value of F at the spatial coordinates and the squared time coordinate. -/
def reductionGraph (F : EuclideanSpace ℝ (Fin m) → ℝ)
    (z : EuclideanSpace ℝ (Fin (m + 1))) : ℝ :=
  Real.sqrt (F (xPart z) ^ 2 + tPart z ^ 2) -- @realizes u(graph)

-- @env: S2
variable (F P : ℝ → ℝ) -- @realizes F(real radial profile) @realizes P(auxiliary radial profile)

-- @node: def:radial-profiles
/-- For [spatial dimension m](hyp:m), [a real radial profile f](hyp:f), and
[a spatial point x](hyp:x), the [radial extension](goal) evaluates f at the Euclidean norm of x. -/
def radialExtension (m : ℕ) (f : ℝ → ℝ) (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  f ‖x‖ -- @realizes r(nonnegative Euclidean radius)

-- @node: def:radial-derivative
/-- For [a real radial profile F](hyp:F), the [radial variable y](goal) is its
derivative with respect to the radius. -/
abbrev radialY : ℝ → ℝ :=
  deriv F -- @realizes y(radial derivative of F)

/-- For [an auxiliary radial profile P](hyp:P), the [radial variable Z](goal) is
its derivative with respect to the radius. -/
abbrev radialZ : ℝ → ℝ :=
  deriv P -- @realizes Z(radial derivative of P)

-- @node: def:radial-system
/-- For [spatial dimension m](hyp:m), [coefficient k and exponent γ](hyp:k,γ),
[radial profiles F and P](hyp:F,P), and [a set of radii J](hyp:J), the [radial
system](goal) requires at every radius in J that [F be twice continuously
differentiable](step:1), [P be twice continuously differentiable](step:2),
[(F′) raised to m − 1 times F″ equal r raised to m − 1 times F times P raised
to −γ](step:3), and [the derivative of (F′) raised to m − 1 times P′ equal
−k times r raised to m − 1 times P raised to 1 − γ](step:4). -/
def RadialSystem (m : ℕ) (k γ : ℝ) (F P : ℝ → ℝ) (J : Set ℝ) : Prop :=
  ∀ r ∈ J, ContDiffAt ℝ 2 F r ∧ ContDiffAt ℝ 2 P r ∧
    deriv F r ^ (m - 1) * deriv (deriv F) r = r ^ (m - 1) * F r * P r ^ (-γ) ∧
    deriv (fun s => deriv F s ^ (m - 1) * deriv P s) r =
      -k * r ^ (m - 1) * P r ^ (1 - γ)

/-- The [fixed spatial dimension for the radial construction](goal) is nine. -/
abbrev radialDim : ℕ := 9 -- @realizes m(nine spatial dimensions in the radial construction)

/-- The [fixed coefficient k for the radial construction](goal) is eleven. -/
def radialK : ℝ := 11 -- @realizes k(radial value 11)

-- @node: def:constants
/-- The [fixed exponent γ for the radial construction](goal) is 12/11. -/
def radialGamma : ℝ := 12 / 11 -- @realizes \gamma(radial value 12/11)

/-- For [a local radius ε](hyp:ε) and [radial profiles F and P](hyp:F,P), the
[local solution data condition](goal) requires [ε to be positive](step:1),
[the radial system with dimension nine, coefficient eleven, and exponent 12/11
to hold for 0 < r < ε](step:2), [the nine-dimensional radial extension of F to be
smooth on the ball of radius ε about zero](step:3), [the same smoothness for the
radial extension of P](step:4), [F at zero to equal one](step:5), [P at zero to
equal one](step:6), [the Hessian of the radial extension of F at zero to be the
identity](step:7), [the Hessian of the radial extension of P at zero to be −11/9
times the identity](step:8), and [F, P, F′, and F″ to be positive and P′ negative
for 0 < r < ε](step:9). -/
def LocalSolutionData (ε : ℝ) (F P : ℝ → ℝ) : Prop :=
  0 < ε ∧ -- @realizes \varepsilon(positive local radius)
  RadialSystem radialDim radialK radialGamma F P (Ioo 0 ε) ∧
  ContDiffOn ℝ ∞ (radialExtension 9 F) (Metric.ball 0 ε) ∧ -- @realizes F(smooth at origin)
  ContDiffOn ℝ ∞ (radialExtension 9 P) (Metric.ball 0 ε) ∧ -- @realizes P(smooth at origin)
  F 0 = 1 ∧ P 0 = 1 ∧
  hessianMatrix (radialExtension 9 F) 0 = 1 ∧ -- @realizes I(nine-dimensional identity matrix)
  hessianMatrix (radialExtension 9 P) 0 = -(11 / 9 : ℝ) • (1 : Matrix (Fin 9) (Fin 9) ℝ) ∧
  ∀ r ∈ Ioo 0 ε, 0 < F r ∧ 0 < P r ∧ 0 < deriv F r ∧
    0 < deriv (deriv F) r ∧ deriv P r < 0

/-- For [an outer endpoint R, possibly positive infinity](hyp:R), the [radial
interval](goal) consists of [strictly positive radii](step:1) that [are strictly
less than R](step:2). -/
def radialInterval (R : WithTop ℝ) : Set ℝ :=
  {r | 0 < r ∧ (r : WithTop ℝ) < R}

/-- For [radial profiles F and P](hyp:F,P) and [an outer endpoint R, possibly
positive infinity](hyp:R), the [positive radial solution condition](goal) requires
[R to be positive](step:1), [the radial system with dimension nine, coefficient
eleven, and exponent 12/11 to hold between zero and R](step:2), and [F, P, and F′
to be positive throughout that interval](step:3). -/
def PositiveRadialSolution (F P : ℝ → ℝ) (R : WithTop ℝ) : Prop :=
  0 < R ∧ RadialSystem radialDim radialK radialGamma F P (radialInterval R) ∧
  ∀ r ∈ radialInterval R, 0 < F r ∧ 0 < P r ∧ 0 < deriv F r

-- @node: def:continuation
/-- For [initial radial profiles F₀ and P₀](hyp:F₀,P₀), [a local radius ε](hyp:ε),
[continued profiles F and P](hyp:F,P), and [an outer endpoint R, possibly positive
infinity](hyp:R), the [maximal continuation condition](goal) requires [ε to be
positive](step:1), [ε to be at most R](step:2), [F and P to agree with F₀ and P₀
from zero inclusive to ε exclusive](step:3), [F and P to be a positive radial
solution up to R](step:4), and [no positive radial solution on a strictly larger
interval to agree with F and P at zero and at all radii between zero and R](step:5). -/
def IsMaximalContinuation (F₀ P₀ : ℝ → ℝ) (ε : ℝ)
    (F P : ℝ → ℝ) (R : WithTop ℝ) : Prop :=
  0 < ε ∧ (ε : WithTop ℝ) ≤ R ∧
  (∀ r ∈ Ico 0 ε, F r = F₀ r ∧ P r = P₀ r) ∧
  PositiveRadialSolution F P R ∧
  ¬ ∃ (R' : WithTop ℝ) (F' P' : ℝ → ℝ), R < R' ∧
    PositiveRadialSolution F' P' R' ∧
    ∀ r ∈ insert 0 (radialInterval R), F' r = F r ∧ P' r = P r

/-- For [a radius r](hyp:r), [profile values F and P](hyp:F,P), and [a radial
derivative value y](hyp:y), with [r positive](hyp:_hr), [F positive](hyp:_hF),
[P positive](hyp:_hP), and [y positive](hyp:_hy), the [regular acceleration G](goal)
equals r to the eighth power times F times P to the power −12/11, divided by y
to the eighth power. -/
def regularG (r F P y : ℝ) (_hr : 0 < r) (_hF : 0 < F)
    (_hP : 0 < P) (_hy : 0 < y) : ℝ :=
  r ^ 8 * F * P ^ (-(12 / 11 : ℝ)) / y ^ 8 -- @realizes G(regular positive-domain right-hand side)

-- @node: def:regular-system
/-- For [a radius r](hyp:r) and [a state v with entries (F, P, y, Z)](hyp:v),
with [r positive](hyp:hr), [F positive](hyp:hF), [P positive](hyp:hP), and
[y positive](hyp:hy), the [regular first order vector field](goal) first
[sets G equal to r⁸ F P to the power −12/11 divided by y⁸](step:1), then
[returns (y, Z, G, −8GZ/y − 11r⁸ P to the power −1/11 divided by y⁸)](step:2). -/
def regularField (r : ℝ) (v : Fin 4 → ℝ) (hr : 0 < r) (hF : 0 < v 0)
    (hP : 0 < v 1) (hy : 0 < v 2) : Fin 4 → ℝ :=
  let G := regularG r (v 0) (v 1) (v 2) hr hF hP hy
  ![v 2, v 3, G, -8 * G / v 2 * v 3 - 11 * r ^ 8 * v 1 ^ (-(1 / 11 : ℝ)) / v 2 ^ 8]

-- @node: def:ratios
/-- For [a radial profile F](hyp:F) and [a radius r](hyp:r), with [r positive](hyp:_hr)
and [F at r nonzero](hyp:_hF), the [logarithmic ratio A](goal) equals rF′(r)/F(r). -/
def ratioA (F : ℝ → ℝ) (r : ℝ) (_hr : 0 < r) (_hF : F r ≠ 0) : ℝ :=
  r * deriv F r / F r -- @realizes A(first radial logarithmic coordinate)

/-- For [a radial profile F](hyp:F) and [a radius r](hyp:r), with [r positive](hyp:_hr)
and [F′ at r nonzero](hyp:_hy), the [logarithmic ratio B](goal) equals rF″(r)/F′(r). -/
def ratioB (F : ℝ → ℝ) (r : ℝ) (_hr : 0 < r) (_hy : deriv F r ≠ 0) : ℝ :=
  r * deriv (deriv F) r / deriv F r -- @realizes B(second radial logarithmic coordinate)

/-- For [an auxiliary radial profile P](hyp:P) and [a radius r](hyp:r), with
[r positive](hyp:_hr) and [P at r nonzero](hyp:_hP), the [logarithmic ratio C](goal)
equals −rP′(r)/P(r). -/
def ratioC (P : ℝ → ℝ) (r : ℝ) (_hr : 0 < r) (_hP : P r ≠ 0) : ℝ :=
  -(r * deriv P r / P r) -- @realizes C(auxiliary radial logarithmic coordinate)

-- @node: def:normalized-ratio
/-- For [radial profiles F and P](hyp:F,P) and [a radius r](hyp:r), with
[r positive](hyp:hr), [F′ at r nonzero](hyp:hy), [P at r nonzero](hyp:hP), and
[the ratio B = rF″(r)/F′(r) positive](hyp:_hB), the [normalized ratio D](goal)
equals C/B, where C = −rP′(r)/P(r). -/
def ratioD (F P : ℝ → ℝ) (r : ℝ) (hr : 0 < r) (hy : deriv F r ≠ 0)
    (hP : P r ≠ 0) (_hB : 0 < ratioB F r hr hy) : ℝ :=
  ratioC P r hr hP / ratioB F r hr hy -- @realizes D(normalized radial logarithmic coordinate)

/-- For [radial profiles F and P](hyp:F,P) and [a radius r](hyp:r), the [radial
coordinate domain condition](goal) requires [r to be positive](step:1),
[F at r to be nonzero](step:2), [P at r to be nonzero](step:3), [F′ at r to be
nonzero](step:4), and [rF″(r)/F′(r) to be positive](step:5). -/
def RadialCoordinateDomain (F P : ℝ → ℝ) (r : ℝ) : Prop :=
  0 < r ∧ F r ≠ 0 ∧ P r ≠ 0 ∧ deriv F r ≠ 0 ∧
    0 < r * deriv (deriv F) r / deriv F r

/-- For [radial profiles F and P](hyp:F,P) and [a radius r](hyp:r), the [extended
radial coordinate vector](goal) equals [(A, B, D) when r is positive, F(r), P(r),
and F′(r) are nonzero, and B is positive](step:1), and [the zero vector otherwise](step:2),
where A = rF′(r)/F(r), B = rF″(r)/F′(r), and D = −rP′(r)/(P(r)B). -/
def radialCoordinates (F P : ℝ → ℝ) (r : ℝ) : Fin 3 → ℝ :=
  @dite _ (RadialCoordinateDomain F P r) (Classical.propDecidable _) (fun h =>
    ![ratioA F r h.1 h.2.1,
      ratioB F r h.1 h.2.2.2.1,
      ratioD F P r h.1 h.2.2.2.1 h.2.2.1 h.2.2.2.2])
    (fun _ => 0)

-- @node: def:logarithmic-time
/-- For [a real-valued function g of the radius](hyp:g) and [a radius r](hyp:r),
with [r positive](hyp:_hr), the [logarithmic time derivative](goal) is the derivative
of g composed with the exponential function, evaluated at log r. -/
def logTimeDeriv (g : ℝ → ℝ) (r : ℝ) (_hr : 0 < r) : ℝ :=
  deriv (fun τ => g (Real.exp τ)) (Real.log r)

/-- For [a coordinate vector z = (A, B, D)](hyp:z), the [autonomous vector field](goal)
has entries A(1 + B − A), B(9 + A + (12/11)BD − 9B), and
(11 − D)A − 8D + BD(1 − D/11). -/
def autonomousField (z : Fin 3 → ℝ) : Fin 3 → ℝ := -- @realizes z(point of real coordinate space)
  ![z 0 * (1 + z 1 - z 0), -- @realizes A(free first coordinate)
    z 1 * (9 + z 0 + (12 / 11 : ℝ) * z 1 * z 2 - 9 * z 1), -- @realizes B(free second coordinate)
    (11 - z 2) * z 0 - 8 * z 2 + 
      z 1 * z 2 * (1 - z 2 / 11)] -- @realizes D(third coordinate) @realizes V(field)

/-- The [upper corner of the invariant box](goal) is the vector (9/2, 7/2, 33/7). -/
def boxCorner : Fin 3 → ℝ :=
  ![9 / 2, 7 / 2, 33 / 7] -- @realizes a_*(upper corner in real coordinate space)

/-- The [closed invariant box](goal) consists of vectors (A, B, D) satisfying
0 ≤ A ≤ 9/2, 0 ≤ B ≤ 7/2, and 0 ≤ D ≤ 33/7. -/
def boxB : Set (Fin 3 → ℝ) :=
  Icc 0 boxCorner -- @realizes \mathcal B(product of the three stated closed intervals)

/-- For [a real-valued function u on n-dimensional Euclidean space](hyp:u),
[being quadratic](goal) means that there exist a real matrix A, a vector b, and
a constant c such that, at every point z, u(z) equals the inner product of z
with Az, plus the inner product of b with z, plus c. -/
def IsQuadraticFunction (u : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∃ (A : Matrix (Fin n) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin n)) (c : ℝ),
    ∀ z, u z = ⟪z, WithLp.toLp 2 (A *ᵥ z)⟫ + ⟪b, z⟫ + c

end OaiSmoothNonquadraticAffine
