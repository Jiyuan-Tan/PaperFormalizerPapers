module

public import Batteries.Logic
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.FunLike.Equiv
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Real.Star
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.SetLike.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Logic.Function.CompTypeclasses
public import Mathlib.Order.Basic
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.Linarith.Preprocessing
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Algebra.Star.Real
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Defs

/-!
# Trace exponential: Klein's inequality, the Gibbs variational formula, monotonicity

For finite real symmetric matrices, with `exp` and `log` given by Mathlib's continuous
functional calculus (`cfc Real.exp`, `CFC.log`), this module provides

* `trace_mul_nonneg_of_posSemidef`: `tr (A B) ≥ 0` for positive semidefinite `A`, `B`;
* `klein_trace_inequality`: `tr A - tr B ≤ tr (A (log A - log B))` for positive definite
  `A`, `B`;
* `trace_exp_variational`: `tr exp C` is the attained maximum of
  `tr (A C) - tr (A log A) + tr A` over positive definite `A`;
* `trace_exp_mono`: `C ≤ D` in the Loewner order implies `tr exp C ≤ tr exp D`.

The Loewner order is written out as positive semidefiniteness of `D - C`.

Reference: J. A. Tropp, *User-friendly tail bounds for sums of random matrices*,
Found. Comput. Math. 12 (2012), §2–3.
-/

public section

open scoped Matrix.Norms.L2Operator MatrixOrder

namespace Toolkit.Foundations.LinearAlgebra.Matrix

variable {n : Type*} [Fintype n]

/-- If [two real square matrices are positive semidefinite](hyp:hA,hB), then [the trace of
their product is nonnegative](goal). -/
theorem trace_mul_nonneg_of_posSemidef {A B : _root_.Matrix n n ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  -- Conjugate B by the CFC square root of A and use trace cyclicity.
  classical
  have h := (hB.mul_mul_conjTranspose_same (CFC.sqrt A)).trace_nonneg
  rw [show (CFC.sqrt A).conjTranspose = CFC.sqrt A from
      (CFC.sqrt_nonneg A).isSelfAdjoint.star_eq,
    _root_.Matrix.trace_mul_cycle, ← sq, CFC.sq_sqrt A hA.nonneg] at h
  exact h

variable [DecidableEq n]

/-- Trace of a diagonal matrix in an orthonormal basis. -/
private theorem trace_unitary_diagonal
    (U : unitary (_root_.Matrix n n ℝ)) (a : n → ℝ) :
    ((U : _root_.Matrix n n ℝ) * _root_.Matrix.diagonal a *
      star (U : _root_.Matrix n n ℝ)).trace = ∑ i, a i := by
  rw [_root_.Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul,
    _root_.Matrix.trace_diagonal]

/-- For two orthogonal matrices `U`, `V` and two real spectra `a`, `b`, [the trace of the
product of `U diag(a) Uᵀ` and `V diag(b) Vᵀ` is the double sum of `a_i b_j` weighted by the
squared entries of `Uᵀ V`](goal). -/
theorem trace_unitary_diagonal_mul
    (U V : unitary (_root_.Matrix n n ℝ)) (a b : n → ℝ) :
    ((U : _root_.Matrix n n ℝ) * _root_.Matrix.diagonal a *
      star (U : _root_.Matrix n n ℝ) *
      ((V : _root_.Matrix n n ℝ) * _root_.Matrix.diagonal b *
        star (V : _root_.Matrix n n ℝ))).trace =
    ∑ i, ∑ j, a i * b j * ((star (U : _root_.Matrix n n ℝ) * V) i j)^2 := by
  let W : unitary (_root_.Matrix n n ℝ) := star U * V
  have htrace :
      (_root_.Matrix.diagonal a * (W : _root_.Matrix n n ℝ) *
        _root_.Matrix.diagonal b * star (W : _root_.Matrix n n ℝ)).trace =
      ∑ i, ∑ j, a i * b j * (W i j)^2 := by
    unfold _root_.Matrix.trace
    apply Finset.sum_congr rfl
    intro i _
    change ((_root_.Matrix.diagonal a * (W : _root_.Matrix n n ℝ) *
      _root_.Matrix.diagonal b) * star (W : _root_.Matrix n n ℝ)) i i = _
    rw [_root_.Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    simp only [_root_.Matrix.mul_diagonal, _root_.Matrix.diagonal_mul,
      _root_.Matrix.star_eq_conjTranspose, _root_.Matrix.conjTranspose_apply, star_trivial]
    ring
  change _ = ∑ i, ∑ j, a i * b j * (W i j)^2
  rw [← htrace]
  simp only [W, Submonoid.coe_mul, Unitary.coe_star, star_mul, star_star]
  calc
    _ = ((U : _root_.Matrix n n ℝ) * (_root_.Matrix.diagonal a *
        star (U : _root_.Matrix n n ℝ) * V * _root_.Matrix.diagonal b *
        star (V : _root_.Matrix n n ℝ))).trace := by simp only [mul_assoc]
    _ = ((_root_.Matrix.diagonal a * star (U : _root_.Matrix n n ℝ) * V *
        _root_.Matrix.diagonal b * star (V : _root_.Matrix n n ℝ)) * U).trace :=
      _root_.Matrix.trace_mul_comm _ _
    _ = _ := by simp only [mul_assoc]

/-- If [two real square matrices `A`, `B` are positive definite](hyp:hA,hB), then [the
difference of their traces is at most the trace of `A (log A - log B)`](goal).

This is Klein's inequality: the matrix relative entropy `tr (A (log A - log B))` is at least
`tr A - tr B`. The proof diagonalises `A` and `B` separately; the squared overlaps of the
two eigenbases form a doubly stochastic matrix, reducing the claim to the scalar
`a log (a/b) - a + b ≥ 0`. -/
theorem klein_trace_inequality {A B : _root_.Matrix n n ℝ}
    (hA : A.PosDef) (hB : B.PosDef) :
    A.trace - B.trace ≤ (A * (CFC.log A - CFC.log B)).trace := by
  let a := hA.isHermitian.eigenvalues
  let b := hB.isHermitian.eigenvalues
  let U := hA.isHermitian.eigenvectorUnitary
  let V := hB.isHermitian.eigenvectorUnitary
  let W : unitary (_root_.Matrix n n ℝ) := star U * V
  let w : n → n → ℝ := fun i j => (W i j)^2
  have hrow (i : n) : ∑ j, w i j = 1 := by
    have h := congrArg (fun M : _root_.Matrix n n ℝ => M i i)
      (Unitary.coe_mul_star_self W)
    simpa [w, _root_.Matrix.mul_apply, _root_.Matrix.star_eq_conjTranspose, pow_two] using h
  have hcol (j : n) : ∑ i, w i j = 1 := by
    have h := congrArg (fun M : _root_.Matrix n n ℝ => M j j)
      (Unitary.coe_star_mul_self W)
    simpa [w, _root_.Matrix.mul_apply, _root_.Matrix.star_eq_conjTranspose, pow_two] using h
  have hspecA : A = (U : _root_.Matrix n n ℝ) * _root_.Matrix.diagonal a *
      star (U : _root_.Matrix n n ℝ) := by
    simpa [U, a, Unitary.conjStarAlgAut_apply] using hA.isHermitian.spectral_theorem
  have hspecB : B = (V : _root_.Matrix n n ℝ) * _root_.Matrix.diagonal b *
      star (V : _root_.Matrix n n ℝ) := by
    simpa [V, b, Unitary.conjStarAlgAut_apply] using hB.isHermitian.spectral_theorem
  have hlogB : CFC.log B = (V : _root_.Matrix n n ℝ) *
      _root_.Matrix.diagonal (fun j => Real.log (b j)) *
      star (V : _root_.Matrix n n ℝ) := by
    rw [CFC.log, hB.isHermitian.cfc_eq, _root_.Matrix.IsHermitian.cfc]
    simp [V, b, Unitary.conjStarAlgAut_apply, Function.comp_def]
  have htrA : A.trace = ∑ i, a i := by rw [hspecA, trace_unitary_diagonal]
  have htrB : B.trace = ∑ j, b j := by rw [hspecB, trace_unitary_diagonal]
  have hent : (A * CFC.log A).trace = ∑ i, a i * Real.log (a i) := by
    rw [CFC.log, hA.isHermitian.cfc_eq, _root_.Matrix.IsHermitian.cfc]
    nth_rw 1 [hA.isHermitian.spectral_theorem]
    rw [← map_mul, Unitary.conjStarAlgAut_apply, _root_.Matrix.trace_mul_cycle,
      Unitary.coe_star_mul_self, one_mul, _root_.Matrix.diagonal_mul_diagonal,
      _root_.Matrix.trace_diagonal]
    simp [a]
  have hcross : (A * CFC.log B).trace = ∑ i, ∑ j, a i * Real.log (b j) * w i j := by
    rw [hspecA, hlogB, trace_unitary_diagonal_mul]
    rfl
  have hscalar (i j : n) :
      0 ≤ a i * (Real.log (a i) - Real.log (b j)) - a i + b j := by
    have ha : 0 < a i := hA.eigenvalues_pos i
    have hb : 0 < b j := hB.eigenvalues_pos j
    have h := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos hb ha)) ha.le
    rw [Real.log_div hb.ne' ha.ne'] at h
    have hab : a i * (b j / a i) = b j := by field_simp
    nlinarith
  have hnonneg : 0 ≤ ∑ i, ∑ j,
      (a i * (Real.log (a i) - Real.log (b j)) - a i + b j) * w i j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (hscalar i j) (sq_nonneg _)
  have hsumA : (∑ i, ∑ j, a i * w i j) = ∑ i, a i := by
    simp_rw [← Finset.mul_sum, hrow, mul_one]
  have hsumB : (∑ i, ∑ j, b j * w i j) = ∑ j, b j := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hcol, mul_one]
  have hsumEnt : (∑ i, ∑ j, (a i * Real.log (a i)) * w i j) =
      ∑ i, a i * Real.log (a i) := by
    simp_rw [← Finset.mul_sum, hrow, mul_one]
  have hexpand : (∑ i, ∑ j,
      (a i * (Real.log (a i) - Real.log (b j)) - a i + b j) * w i j) =
      (∑ i, a i * Real.log (a i)) - (∑ i, ∑ j, a i * Real.log (b j) * w i j) -
        (∑ i, a i) + ∑ j, b j := by
    simp only [mul_sub, sub_mul, add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hsumEnt, hsumA, hsumB]
  rw [_root_.Matrix.mul_sub, _root_.Matrix.trace_sub, hent, hcross, htrA, htrB]
  rw [hexpand] at hnonneg
  linarith

/-- For [a real symmetric matrix `C`](hyp:hC), [the trace of its exponential is the
largest value of `tr (A C) - tr (A log A) + tr A` as `A` ranges over positive definite
matrices, and this maximum is attained](goal).

This is the Gibbs variational formula; the maximiser is `A = exp C`. -/
theorem trace_exp_variational {C : _root_.Matrix n n ℝ} (hC : C.IsHermitian) :
    IsGreatest
      {r : ℝ | ∃ A : _root_.Matrix n n ℝ, A.PosDef ∧
        r = (A * C).trace - (A * CFC.log A).trace + A.trace}
      (cfc Real.exp C).trace := by
  -- Apply Klein with B=cfc Real.exp C and CFC.log_exp; equality is attained
  -- by A=B. Derive B.PosDef by spectral positivity (including empty n).
  have hB : (cfc Real.exp C).PosDef := by
    rw [hC.cfc_eq, _root_.Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
      _root_.Matrix.IsUnit.posDef_star_right_conjugate_iff Unitary.isUnit_coe,
      _root_.Matrix.posDef_diagonal_iff]
    intro i
    simpa using Real.exp_pos (hC.eigenvalues i)
  have hlog : CFC.log (cfc Real.exp C) = C := by
    rw [CFC.real_exp_eq_normedSpace_exp hC.isSelfAdjoint, CFC.log_exp C hC.isSelfAdjoint]
  refine ⟨⟨cfc Real.exp C, hB, ?_⟩, ?_⟩
  · rw [hlog]
    ring
  · rintro r ⟨A, hA, rfl⟩
    have h := klein_trace_inequality hA hB
    rw [hlog, _root_.Matrix.mul_sub, _root_.Matrix.trace_sub] at h
    linarith

/-- If [two real matrices `C`, `D` are symmetric](hyp:hC,hD) and [`D - C` is positive
semidefinite, that is `C ≤ D` in the Loewner order](hyp:hCD), then [the trace of the
exponential of `C` is at most the trace of the exponential of `D`](goal). -/
theorem trace_exp_mono {C D : _root_.Matrix n n ℝ}
    (hC : C.IsHermitian) (hD : D.IsHermitian) (hCD : (D - C).PosSemidef) :
    (cfc Real.exp C).trace ≤ (cfc Real.exp D).trace := by
  -- Use the maximizer A=exp C in the variational formula for D. The change
  -- in the trace pairing is tr(A*(D-C))≥0. This avoids matrix derivatives.
  obtain ⟨A, hA, hmax⟩ := (trace_exp_variational hC).1
  have hpair := trace_mul_nonneg_of_posSemidef hA.posSemidef hCD
  have hbound : (A * D).trace - (A * CFC.log A).trace + A.trace ≤
      (cfc Real.exp D).trace :=
    (trace_exp_variational hD).2 ⟨A, hA, rfl⟩
  rw [_root_.Matrix.mul_sub, _root_.Matrix.trace_sub] at hpair
  linarith

end Toolkit.Foundations.LinearAlgebra.Matrix
