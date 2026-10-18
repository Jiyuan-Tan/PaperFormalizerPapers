module
public import Papers.TbsExtremeEffects.Setup.Model
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The joint component-density class and its nonnegative matrix images.
The density is joint; no component independence is imposed. -/

@[expose] public section
namespace Papers.TbsExtremeEffects
open MeasureTheory
set_option linter.style.longLine false
open scoped BigOperators ENNReal Topology
noncomputable section

-- @env: S2
variable {q d m : ℕ}

/-- [The tail-model parameters](goal) collect lower and upper column bounds, a volume bound, a density-error constant, a tail exponent, and a tail cutoff constant. -/
structure TailParams where
  l : ℝ
  u : ℝ
  sigma : ℝ -- @realizes \sigma(matrix-volume lower bound)
  xi : ℝ -- @realizes \xi(relative density error constant)
  s : ℝ -- @realizes s(tail-model exponent)
  zeta : ℝ -- @realizes \zeta(exact-tail cutoff constant)

/-- [The tail index $\beta$](hyp:beta) and [evaluation point $x$](hyp:x) determine [the type-II Pareto density](goal), which equals $\beta(1+x)^{-\beta-1}$ for positive $x$ and zero otherwise.
@realizes f(type II Pareto density, separate from conditional-mean f) -/
def paretoIIDensity (beta x : ℝ) : ℝ :=
  if 0 < x then beta * (1 + x) ^ (-(beta + 1)) else 0

-- @node: def:pareto-type-ii
/-- [The measure $\nu$](hyp:nu) has [a type-II Pareto law with tail index $\beta$](goal) when [the index is positive](hyp:beta) and the measure has the corresponding density. -/
structure IsParetoTypeII (nu : Measure ℝ) (beta : ℝ) : Prop where
  beta_pos : 0 < beta
  density : nu = volume.withDensity (fun x => ENNReal.ofReal (paretoIIDensity beta x))

/-- [The tail index $\beta$](hyp:beta) and [component vector $z$](hyp:z) determine [the product Pareto density](goal) obtained by multiplying the type-II factors. -/
def paretoProductDensity (beta : ℝ) (z : Fin m → ℝ) : ℝ :=
  beta ^ m * ∏ i, (1 + z i) ^ (-(beta + 1))

-- @node: ass:pin-fix-10c2ec7b
/-- [The tail index $\beta$](hyp:beta) and [component dimension $m$](hyp:m) satisfy [the component-dimension convention](goal) when the product-density formula holds for every $m$-component vector. -/
def ComponentDimensionConvention (beta : ℝ) (m : ℕ) : Prop :=
  ∀ z : Fin m → ℝ, paretoProductDensity beta z =
    beta ^ m * ∏ i : Fin m, (1 + z i) ^ (-(beta + 1))

-- @node: ass:pin-36
/-- [The density $h$](hyp:h), [tail index $\beta$](hyp:beta), [cutoff constant $\zeta$](hyp:zeta), [tail exponent $s$](hyp:s), and [index $k$](hyp:k) satisfy [exact tail proportionality](goal) when [a positive proportionality constant exists](step:1) and [almost every sufficiently large nonnegative vector has density equal to that constant times the product Pareto density](step:2). -/
def ExactTailProportional (h : (Fin m → ℝ) → ℝ) (beta zeta s : ℝ) (k : ℕ) : Prop :=
  ∃ kappa : ℝ, 0 < kappa ∧ ∀ᵐ z ∂(volume : Measure (Fin m → ℝ)),
    z ∈ nonnegativeOrthant →
    zeta * (k : ℝ) ^ ((1 - 2 * s) / beta) < l1Norm z →
      h z = kappa * paretoProductDensity beta z

/-- [The tail index $\beta$](hyp:beta), [tail parameters](hyp:tp), and [component-class index $k$](hyp:k) determine [the component-law class](goal) of nonnegative probability densities that approximate the product Pareto density and become exactly proportional to it in the far tail.
@realizes \tilde M_k(probability laws on the nonnegative component orthant) -/
def componentClass (beta : ℝ) (tp : TailParams) (k : ℕ) : Set (Measure (Fin m → ℝ)) :=
  {nu | IsProbabilityMeasure nu ∧ ∃ h : (Fin m → ℝ) → ℝ,
    Measurable h ∧ (∀ z, 0 ≤ h z) ∧
    (∀ z, z ∉ nonnegativeOrthant → h z = 0) ∧
    nu = volume.withDensity (fun z => ENNReal.ofReal (h z)) ∧
    (∀ z ∈ nonnegativeOrthant,
      |(h z - paretoProductDensity beta z) / paretoProductDensity beta z| ≤
        tp.xi * (k : ℝ) ^ (-tp.s)) ∧
    ExactTailProportional h beta tp.zeta tp.s k}

/-- [The tail parameters](hyp:tp) determine [the matrix class](goal) of nonnegative matrices whose column norms and Gram volume meet the stated bounds.
@realizes \mathcal{A}(nonnegative matrices with column and Gram-volume bounds)
@realizes A(fixed matrix carrier Matrix (Fin d) (Fin m) ℝ) -/
def matrixClass (tp : TailParams) : Set (Matrix (Fin d) (Fin m) ℝ) :=
  {A | (∀ r i, 0 ≤ A r i) ∧ -- @realizes A(nonnegative matrix entries)
    (∀ i, tp.l ≤ l1Norm (fun r => A r i) ∧ l1Norm (fun r => A r i) ≤ tp.u) ∧ -- @realizes A(column l1 norms between fixed l and u)
    tp.sigma ≤ Real.sqrt (Matrix.det (A.transpose * A))} -- @realizes A(Gram-volume at least sigma)

/-- [The component dimension $m$](hyp:m), [tail index $\beta$](hyp:beta), [tail parameters](hyp:tp), and [index $k$](hyp:k) determine [the tail-law class](goal) of matrix images of admissible component laws.
@realizes M_k(class of laws of AZ for one positive component-class index)
@realizes Z(component law on Fin m → ℝ, constrained by componentClass) -/
def tailClass (m : ℕ) (beta : ℝ) (tp : TailParams) (k : ℕ) : Set (Measure (Fin d → ℝ)) :=
  {nu | ∃ A : Matrix (Fin d) (Fin m) ℝ, A ∈ matrixClass tp ∧
    ∃ nuZ ∈ componentClass beta tp k, nu = nuZ.map (Matrix.mulVec A)}
/-- [The component dimension $m$](hyp:m), [tail index $\beta$](hyp:beta), and [tail parameters](hyp:tp) determine [the tail-model class](goal), the union of tail-law classes over positive indices.
@realizes M(union of noise-law classes over positive k) -/
def tailModelClass (m : ℕ) (beta : ℝ) (tp : TailParams) : Set (Measure (Fin d → ℝ)) :=
  {nu | ∃ k : ℕ, 1 ≤ k ∧ nu ∈ tailClass m beta tp k}

-- @node: ass:mvary-density
/-- [The extreme model $M$](hyp:M), [matrix $A$](hyp:A), and [tail parameters](hyp:tp) satisfy [the varying-density condition](goal) when [a positive component-class index exists](step:1), [an admissible component law at that index exists](step:2), and [the model's transformed noise law is its image under $A$](step:3). -/
def MvaryDensity (M : ExtremeModel q d) (A : Matrix (Fin d) (Fin m) ℝ)
    (tp : TailParams) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ ∃ nuZ : Measure (Fin m → ℝ),
    nuZ ∈ componentClass M.beta tp k ∧ M.mu.map M.U = nuZ.map (Matrix.mulVec A)
-- @node: ass:mvary-matrix
/-- [The matrix $A$](hyp:A) and [tail parameters](hyp:tp) satisfy [the varying-matrix condition](goal) exactly when $A$ belongs to the admissible matrix class. -/
def MvaryMatrix (A : Matrix (Fin d) (Fin m) ℝ) (tp : TailParams) : Prop := A ∈ matrixClass tp
/-- [The noise dimension $d$](hyp:d) and [component dimension $m$](hyp:m) satisfy [the dimension convention](goal) when [the noise dimension is at least two](step:1) and [it does not exceed the component dimension](step:2). -/
def DimensionConvention (d m : ℕ) : Prop := 2 ≤ d ∧ d ≤ m
-- @node: ass:mvary-constants
/-- [The noise dimension $d$](hyp:d), [component dimension $m$](hyp:m), and [tail parameters](hyp:tp) satisfy [the varying-model constants condition](goal) when [the dimension convention holds](step:1), [the lower column bound is positive](step:2), [the lower column bound is below one](step:3), [the upper column bound exceeds one](step:4), [the tail exponent is positive](step:5), [the tail exponent is below one half](step:6), [the volume bound is positive](step:7), [the density-error constant is positive](step:8), [the density-error constant is below one](step:9), and [the tail cutoff constant is positive](step:10). -/
def MvaryConstants (d m : ℕ) (tp : TailParams) : Prop :=
  DimensionConvention d m ∧ 0 < tp.l ∧ tp.l < 1 ∧ 1 < tp.u ∧
  0 < tp.s ∧ tp.s < 1 / 2 ∧ -- @realizes s(range (0,1/2))
  0 < tp.sigma ∧ -- @realizes \sigma(positive matrix-volume bound)
  0 < tp.xi ∧ tp.xi < 1 ∧ -- @realizes \xi(range (0,1))
  0 < tp.zeta -- @realizes \zeta(positive tail cutoff)

/-- An admissible representation of the noise law, carrying its fixed matrix.
Class membership is `Nonempty (ParetoTailModel M m tp)`. -/
-- @node: def:pareto-tail-model
structure ParetoTailModel (M : ExtremeModel q d) (m : ℕ) (tp : TailParams) where
  A : Matrix (Fin d) (Fin m) ℝ -- @realizes A(fixed representation matrix; range via matrix)
  density : MvaryDensity M A tp
  matrix : MvaryMatrix A tp
  constants : MvaryConstants d m tp

/-- [The extreme model $M$](hyp:M) determines [its noise law](goal) as the distribution of its noise vector. -/
def noiseLaw (M : ExtremeModel q d) := M.mu.map M.U
-- @node: ass:pin-fix-8964f8dd
/-- [The extreme model $M$](hyp:M) satisfies [the noise-law specification](goal) when its named noise law is the distribution of its noise vector. -/
def TailModelSpecifiesNoiseLaw (M : ExtremeModel q d) : Prop := noiseLaw M = M.mu.map M.U


/-- [The extreme model $M$](hyp:M) and [threshold $t$](hyp:t) determine [the conditional angular law](goal) by mapping the tail law to directions.

Conditional angular laws and their l1 Kantorovich–Rubinstein dual. -/
def directionLaw (M : ExtremeModel q d) (t : ℝ) := (tailLaw M t).map (direction M)
/-- [The test function $\phi$](hyp:phi) satisfies [the angular test condition](goal) when [it is measurable](step:1) and [it is one-Lipschitz on the positive $\ell_1$ unit sphere](step:2). -/
def angularTest (phi : (Fin d → ℝ) → ℝ) : Prop :=
  Measurable phi ∧ ∀ u ∈ positiveSphere l1Norm, ∀ v ∈ positiveSphere l1Norm,
    |phi u - phi v| ≤ l1Norm (u - v)
/-- [The extreme model $M$](hyp:M) and [threshold $t$](hyp:t) determine [the angular Wasserstein discrepancy](goal), the largest difference in expectations over admissible angular test functions. -/
def angularW1 (M : ExtremeModel q d) (t : ℝ) : ℝ :=
  sSup {a | ∃ phi : (Fin d → ℝ) → ℝ, angularTest phi ∧
    a = |(∫ u, phi u ∂(directionLaw M t)) - ∫ u, phi u ∂M.S|}

/-- [The extreme model $M$](hyp:M), [tail parameters](hyp:tp), [rate constant $C_W$](hyp:CW), [logarithmic exponent $k$](hyp:k), and [onset threshold $t_W$](hyp:tW) satisfy [the angular rate bound](goal) when [the rate constant is positive](step:1), [the logarithmic exponent is nonnegative](step:2), [the onset is at least one](step:3), and [the angular discrepancy obeys the stated two-term bound beyond that onset](step:4). -/
def AngularRateBound (M : ExtremeModel q d) (tp : TailParams) (CW k tW : ℝ) : Prop :=
  0 < CW ∧ 0 ≤ k ∧ -- @realizes k(fixed nonnegative angular logarithmic exponent)
  1 ≤ tW ∧ ∀ t, tW ≤ t →
    angularW1 M t ≤ CW * (Real.log t) ^ k * t ^ (-min 1 M.beta) +
      CW * t ^ (-(M.beta * tp.s / (1 - 2 * tp.s)))

/-- [The extreme model $M$](hyp:M), [angular onset $t_W$](hyp:tW), [doubly robust onset $t_{DR}$](hyp:tDR), and [inverse-probability-weighted onset $t_{IPW}$](hyp:tIPW) satisfy [the large-cutoff condition](goal) when [the angular onset is at least one](step:1), [it dominates the doubly robust onset](step:2), [it dominates the inverse-probability-weighted onset](step:3), [the homogeneity error is small beyond it](step:4), and [tail probabilities obey the stated Pareto-type ratio bound](step:5). -/
-- @node: ass:pin-41
def RateCutoffLarge (M : ExtremeModel q d) (tW tDR tIPW : ℝ) : Prop :=
  1 ≤ tW ∧ tDR ≤ tW ∧ tIPW ≤ tW ∧
  (∀ r, tW ≤ r → M.e r ≤ 1) ∧
  ∀ t, tW ≤ t → ∀ r, 1 ≤ r →
    tailProb M (t * r) / tailProb M t ≤ 4 * r ^ (-M.beta)

end
end Papers.TbsExtremeEffects
