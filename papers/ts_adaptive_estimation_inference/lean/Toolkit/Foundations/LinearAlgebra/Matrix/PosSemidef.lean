module

public import Causalean.Experimentation.DesignBased.FinitePopulationCLT.PermutationTransport
public import Causalean.Experimentation.DesignBased.FinitePopulationVariance
public import Causalean.Experimentation.DesignBased.InProb
public import Causalean.Experimentation.DesignBased.SequentialSampling
public import Causalean.Stat.CLT.ChiSquared
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Data.Finset.Sort
public import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Measure.DiracProba
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
public import Mathlib.Probability.Distributions.Gaussian.CharFun
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Toolkit.Foundations.LinearAlgebra.Matrix.TraceExponential

/-!
# Toolkit.Foundations.LinearAlgebra.Matrix.PosSemidef

Entry bounds, limits and contractions for positive semidefinite matrices
-/

public section

namespace Toolkit.Foundations.LinearAlgebra.Matrix

section

open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory
open Causalean.Experimentation.DesignBased
open Causalean.Experimentation.FinitePopulationMoments

-- @node: posSemidef_entry_sq_le_diag_mul_diag
/-- For [a positive semidefinite real matrix](hyp:hV), [the square of its entry at two chosen coordinates is no larger than the product of the corresponding diagonal entries](goal). -/
lemma posSemidef_sq_apply_le_diag_mul_diag {K : ℕ}
    (V : Matrix (Fin K) (Fin K) ℝ) (hV : V.PosSemidef) (c d : Fin K) :
    V c d ^ 2 ≤ V c c * V d d := by
  have hs : V d c = V c d := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_apply, star_trivial]
      using congrFun (congrFun hV.isHermitian c) d
  have hq (t : ℝ) : 0 ≤ V c c * (t * t) + (2 * V c d) * t + V d d := by
    have h := hV.dotProduct_mulVec_nonneg (Pi.single c t + Pi.single d 1)
    simp [star_trivial, Matrix.mulVec_add, add_dotProduct, dotProduct_add,
      Matrix.mulVec_single, single_dotProduct, Matrix.col, hs] at h
    nlinarith [h]
  have h := discrim_le_zero hq
  unfold discrim at h
  nlinarith

end

end Toolkit.Foundations.LinearAlgebra.Matrix

namespace Toolkit.Foundations.LinearAlgebra.Matrix

/-- The trace of the product of [a nonzero](hyp:hZ0) [positive semidefinite real matrix](hyp:hZ)
with [a positive definite real matrix](hyp:hB) [is strictly positive](goal).

This is the statement that positive definite matrices lie in the interior of the self-dual
positive semidefinite cone (Boyd and Vandenberghe, *Convex Optimization*, Example 2.24; Horn and
Johnson, *Matrix Analysis*, Section 7.5). The product is taken with the positive semidefinite
factor first; cyclic invariance of trace gives the same conclusion with the factors reversed.
-/
theorem trace_mul_pos_of_posDef_of_posSemidef_of_ne_zero
    {ι : Type*} [Fintype ι] (B Z : _root_.Matrix ι ι ℝ)
    (hB : B.PosDef) (hZ : Z.PosSemidef) (hZ0 : Z ≠ 0) :
    0 < _root_.Matrix.trace (Z * B) := by
  classical
  open scoped MatrixOrder in
  have hSsq : CFC.sqrt Z * CFC.sqrt Z = Z := by
    simpa only [pow_two] using CFC.sq_sqrt Z hZ.nonneg
  let S := CFC.sqrt Z
  have hSstar : star S = S := (CFC.sqrt_nonneg Z).isSelfAdjoint.star_eq
  have hS0 : S ≠ 0 := by
    intro h
    apply hZ0
    calc
      Z = S * S := hSsq.symm
      _ = 0 := by rw [h, zero_mul]
  obtain ⟨i, hi⟩ : ∃ i, S.col i ≠ 0 := by
    by_contra! h
    apply hS0
    ext j i
    exact congrFun (h i) j
  have hd (j : ι) : (star S * B * S) j j =
      dotProduct (star (S.col j)) (_root_.Matrix.mulVec B (S.col j)) := by
    rw [_root_.Matrix.mul_assoc]
    rfl
  have htrace : 0 < _root_.Matrix.trace (star S * B * S) := by
    apply Finset.sum_pos'
    · intro j _
      change 0 ≤ (star S * B * S) j j
      rw [hd]
      exact hB.posSemidef.dotProduct_mulVec_nonneg _
    · exact ⟨i, Finset.mem_univ i, by
        change 0 < (star S * B * S) i i
        rw [hd]
        exact hB.dotProduct_mulVec_pos hi⟩
  rw [_root_.Matrix.trace_mul_cycle, hSstar, hSsq] at htrace
  exact htrace

end Toolkit.Foundations.LinearAlgebra.Matrix



namespace Toolkit.Foundations.LinearAlgebra.Matrix

/-- A [real symmetric square matrix](hyp:hB) [is positive semidefinite exactly when the trace of
its product with every real positive semidefinite matrix of the same size is nonnegative](goal).

This is the self-duality of the positive semidefinite cone, also called Fejér's trace theorem
(Horn and Johnson, *Matrix Analysis*, 2nd ed., Corollary 7.5.4; Boyd and Vandenberghe,
*Convex Optimization*, Example 2.24). The positive semidefinite test matrix is the first factor
of the trace pairing; the converse direction tests against rank-one outer products `x xᵀ`.
-/
theorem posSemidef_iff_forall_posSemidef_trace_mul_nonneg
    {ι : Type*} [Fintype ι] (B : _root_.Matrix ι ι ℝ) (hB : B.IsSymm) :
    B.PosSemidef ↔
      ∀ Z : _root_.Matrix ι ι ℝ, Z.PosSemidef → 0 ≤ (Z * B).trace := by
  constructor
  · intro h Z hZ
    exact trace_mul_nonneg_of_posSemidef hZ h
  · intro h
    apply _root_.Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (_root_.Matrix.isHermitian_iff_isSymm.mpr hB)
    intro x
    -- Testing with x xᵀ recovers the quadratic form xᵀ B x.
    have hx := h (_root_.Matrix.vecMulVec x (star x))
      (_root_.Matrix.posSemidef_vecMulVec_self_star x)
    rw [_root_.Matrix.trace_mul_comm, _root_.Matrix.mul_vecMulVec,
      _root_.Matrix.trace_vecMulVec, dotProduct_comm] at hx
    exact hx

end Toolkit.Foundations.LinearAlgebra.Matrix

namespace Toolkit.Foundations.LinearAlgebra.Matrix

noncomputable section

open _root_.Matrix
open scoped BigOperators MatrixOrder

/-- If [the first matrix is positive semidefinite](hyp:hA), [the second matrix is
positive semidefinite](hyp:hB), and [their product has zero trace](hyp:htr),
[their matrix product is zero](goal). -/
-- @node: psd_mul_eq_zero_of_trace_eq_zero
lemma mul_eq_zero_of_posSemidef_of_trace_mul_eq_zero {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (htr : (A * B).trace = 0) : A * B = 0 := by
  obtain ⟨X, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  obtain ⟨Y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  simp only [Matrix.star_eq_conjTranspose] at htr ⊢
  have hnorm : ((X * Yᴴ)ᴴ * (X * Yᴴ)).trace = 0 := by
    calc
      _ = (Y * (Xᴴ * X) * Yᴴ).trace := by
        congr 1
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
        noncomm_ring
      _ = ((Xᴴ * X) * (Yᴴ * Y)).trace := by
        rw [Matrix.trace_mul_cycle']
        simp only [Matrix.mul_assoc]
      _ = 0 := htr
  have hXY := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hnorm
  calc
    _ = Xᴴ * (X * Yᴴ) * Y := by noncomm_ring
    _ = 0 := by rw [hXY, Matrix.mul_zero, Matrix.zero_mul]

end

end Toolkit.Foundations.LinearAlgebra.Matrix


namespace Toolkit.Foundations.LinearAlgebra.Matrix

section L2OpNormTraceBound

open scoped Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

/-- The trace of [a positive semidefinite real matrix](hyp:hA) times [a symmetric real
matrix](hyp:hB) [is at most the symmetric matrix's spectral (Euclidean operator) norm times
the trace of the positive semidefinite matrix](goal).

This holds for every finite index set, including the empty one; the norm is the one of the
`Matrix.Norms.L2Operator` scope. Standard (Bhatia, *Matrix Analysis*, 1997, Ch. III): apply
`trace_mul_nonneg_of_posSemidef` to the positive semidefinite matrix `‖B‖ • 1 - B`.
-/
theorem trace_mul_le_l2_opNorm_mul_trace_of_posSemidef
    {ι : Type*} [Fintype ι] {A B : _root_.Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hB : B.IsSymm) :
    (A * B).trace ≤ ‖B‖ * A.trace := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
    let := h
    simp [_root_.Matrix.trace]
  | inr h =>
    let := h
    open scoped MatrixOrder in
    have hle : B ≤ algebraMap ℝ (_root_.Matrix ι ι ℝ) ‖B‖ :=
      le_algebraMap_of_spectrum_le
        (fun r hr => (Real.le_norm_self r).trans (spectrum.norm_le_norm_of_mem hr))
        (_root_.Matrix.isHermitian_iff_isSymm.mpr hB).isSelfAdjoint
    have hpsd : (‖B‖ • (1 : _root_.Matrix ι ι ℝ) - B).PosSemidef := by
      simpa only [_root_.Matrix.le_iff, Algebra.algebraMap_eq_smul_one] using hle
    have htrace := trace_mul_nonneg_of_posSemidef hA hpsd
    simp only [mul_sub, _root_.Matrix.mul_smul, mul_one,
      _root_.Matrix.trace_sub, _root_.Matrix.trace_smul, smul_eq_mul] at htrace
    exact sub_nonneg.mp htrace

/-- For [a positive semidefinite real matrix](hyp:hA), [the trace of its product with the
Gram matrix `G Gᵀ` of any real rectangular matrix `G` is at most its own trace times the
squared spectral norm of `G`](goal).

No index set needs to be nonempty. This is the form used to bound a noise term
`trace(A·W)` with `W = G Gᵀ` in semidefinite-relaxation analyses.
-/
theorem trace_mul_gram_le_trace_mul_l2_opNorm_sq_of_posSemidef
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {A : _root_.Matrix ι ι ℝ} (hA : A.PosSemidef)
    (G : _root_.Matrix ι κ ℝ) :
    (A * (G * G.transpose)).trace ≤ A.trace * ‖G‖ ^ 2 := by
  classical
  have hsymm : (G * G.transpose).IsSymm := by
    simp only [_root_.Matrix.IsSymm, _root_.Matrix.transpose_mul,
      _root_.Matrix.transpose_transpose]
  have hnorm : ‖G * G.transpose‖ = ‖G‖ ^ 2 := by
    have h := _root_.Matrix.l2_opNorm_conjTranspose_mul_self G.transpose
    simpa [_root_.Matrix.conjTranspose_eq_transpose_of_trivial,
      _root_.Matrix.l2_opNorm_conjTranspose,
      ← _root_.Matrix.conjTranspose_eq_transpose_of_trivial, pow_two] using h
  simpa only [hnorm, mul_comm] using
    trace_mul_le_l2_opNorm_mul_trace_of_posSemidef hA hsymm

end L2OpNormTraceBound

end Toolkit.Foundations.LinearAlgebra.Matrix


namespace Toolkit.Foundations.LinearAlgebra.Matrix

/-- Solutions of the normal equation minimize a positive semidefinite quadratic:
if [a real square matrix A is positive semidefinite](hyp:hA) and
[a vector x solves the normal equation A x = b](hyp:hx), then
[the value of the quadratic xᵀAx − 2·xᵀb at x is no greater than its value
zᵀAz − 2·zᵀb at any other vector z](goal).

No invertibility of the matrix and no positive dimension is required (Boyd and Vandenberghe,
*Convex Optimization*, 2004, §4.2.5 and Appendix A.5.4). The proof expands the nonnegative
quadratic form at `z - x` and uses the symmetry of the matrix to identify the cross terms.
-/
theorem dotProduct_mulVec_sub_le_of_posSemidef_of_mulVec_eq
    {N : ℕ} (A : _root_.Matrix (Fin N) (Fin N) ℝ) (hA : A.PosSemidef)
    (b x : Fin N → ℝ) (hx : A.mulVec x = b) (z : Fin N → ℝ) :
    x ⬝ᵥ A.mulVec x - 2 * x ⬝ᵥ b ≤ z ⬝ᵥ A.mulVec z - 2 * z ⬝ᵥ b := by
  have hnonneg : 0 ≤ (z - x) ⬝ᵥ A.mulVec (z - x) := by
    simpa using hA.dotProduct_mulVec_nonneg (z - x)
  have hsymm : A.IsSymm := _root_.Matrix.isHermitian_iff_isSymm.mp hA.isHermitian
  have hcross : x ⬝ᵥ A.mulVec z = z ⬝ᵥ A.mulVec x := by
    simpa only [hsymm.eq] using _root_.Matrix.dotProduct_transpose_mulVec A x z
  rw [_root_.Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub] at hnonneg
  rw [hx] at hnonneg hcross ⊢
  linarith

end Toolkit.Foundations.LinearAlgebra.Matrix


namespace Toolkit.Foundations.LinearAlgebra.Matrix

/-- Minimizers of a quadratic form solve the normal equation: if
[a real square matrix A is symmetric](hyp:hA) and
[x minimizes the objective zᵀAz − 2·zᵀb over every real vector z](hyp:hmin), then
[x solves the normal equation A x = b](goal).

This is the necessary first-order condition for unconstrained quadratic minimization
(Boyd and Vandenberghe, *Convex Optimization*, 2004, §4.2.5 and Appendix A.5.4). Neither
positive semidefiniteness nor invertibility is assumed, and the dimension may be zero; the
converse direction is `dotProduct_mulVec_sub_le_of_posSemidef_of_mulVec_eq`.
-/
theorem mulVec_eq_of_forall_dotProduct_mulVec_sub_le
    {N : ℕ} (A : _root_.Matrix (Fin N) (Fin N) ℝ) (hA : A.IsSymm)
    (b x : Fin N → ℝ)
    (hmin : ∀ z : Fin N → ℝ,
      x ⬝ᵥ A.mulVec x - 2 * x ⬝ᵥ b ≤
        z ⬝ᵥ A.mulVec z - 2 * z ⬝ᵥ b) :
    A.mulVec x = b := by
  -- Test minimality along x + t • v; the resulting scalar quadratic in t is nonnegative,
  -- so its discriminant vanishes, forcing v ⬝ᵥ A x = v ⬝ᵥ b for every direction v.
  apply dotProduct_eq
  intro v
  have hsym : x ⬝ᵥ A.mulVec v = v ⬝ᵥ A.mulVec x := by
    simpa only [hA.eq] using _root_.Matrix.dotProduct_transpose_mulVec A x v
  have hquad : ∀ t : ℝ, 0 ≤ (v ⬝ᵥ A.mulVec v) * (t * t) +
      (2 * (v ⬝ᵥ A.mulVec x - v ⬝ᵥ b)) * t + 0 := by
    intro t
    have ht := hmin (x + t • v)
    simp only [_root_.Matrix.mulVec_add, _root_.Matrix.mulVec_smul,
      add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      smul_eq_mul] at ht
    rw [hsym] at ht
    nlinarith [ht]
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  have hv : v ⬝ᵥ A.mulVec x = v ⬝ᵥ b := by
    nlinarith [sq_nonneg (v ⬝ᵥ A.mulVec x - v ⬝ᵥ b)]
  simpa only [dotProduct_comm] using hv

end Toolkit.Foundations.LinearAlgebra.Matrix
