module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Center
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.VonNeumannAlgebra.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.FunLike.Equiv
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Real.Star
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.SetLike.Basic
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Filter.Ultrafilter.Defs
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Star
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

/-!
# Toolkit.Foundations.Analysis.Normed.WeakOperatorLimits

Limits of operators in the weak operator topology: compactness of the unit ball and closedness of von Neumann algebras
-/

public section

namespace Toolkit.Foundations.Analysis.Normed

section

open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- If [every operator in a sequence has norm at most one](hyp:hT), [for any
ultrafilter on the sequence indices there is an operator of norm at most one
to which all matrix coefficients converge along that ultrafilter](goal). -/
-- @node: bounded_operators_ultrafilter_limit
lemma exists_norm_le_one_tendsto_inner_of_forall_norm_le_one (T : ℕ → H →L[ℂ] H)
    (hT : ∀ j, ‖T j‖ ≤ 1) (u : Ultrafilter ℕ) :
    ∃ B : H →L[ℂ] H, ‖B‖ ≤ 1 ∧
      ∀ x y, Tendsto (fun j => inner ℂ y (T j x)) (u : Filter ℕ)
        (𝓝 (inner ℂ y (B x))) := by
  classical
  have hex (x : H) : ∃ f : WeakDual ℂ H,
      ‖f.toStrongDual‖ ≤ ‖x‖ ∧
      Tendsto (fun j => (InnerProductSpace.toDual ℂ H (T j x)).toWeakDual)
        (u : Filter ℕ) (𝓝 f) := by
    obtain ⟨f, hf, hlim⟩ := (WeakDual.isCompact_closedBall (0 : StrongDual ℂ H) ‖x‖).ultrafilter_le_nhds (u.map (fun j =>
        (InnerProductSpace.toDual ℂ H (T j x)).toWeakDual)) (by
          apply le_principal_iff.mpr
          change ∀ᶠ j in (u : Filter ℕ), _
          exact Eventually.of_forall fun j => by
            simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
            exact ((InnerProductSpace.toDual ℂ H).norm_map _).le.trans
              ((T j).le_opNorm x |>.trans (by nlinarith [hT j, norm_nonneg x])))
    exact ⟨f, by simpa using hf, hlim⟩
  choose f hf hlim using hex
  let b : H → H := fun x => (InnerProductSpace.toDual ℂ H).symm (f x).toStrongDual
  have hb (x : H) : ‖b x‖ ≤ ‖x‖ := by
    simpa only [b, LinearIsometryEquiv.norm_map] using hf x
  have hw (x y : H) : Tendsto (fun j => inner ℂ y (T j x)) (u : Filter ℕ)
      (𝓝 (inner ℂ y (b x))) := by
    have hh := (WeakDual.eval_continuous y).continuousAt.tendsto.comp (hlim x)
    have he : inner ℂ (b x) y = (f x).toStrongDual y :=
      InnerProductSpace.toDual_symm_apply
    change Tendsto (fun j => inner ℂ (T j x) y) (u : Filter ℕ)
      (𝓝 ((f x).toStrongDual y)) at hh
    rw [← he] at hh
    simpa only [RCLike.star_def, inner_conj_symm] using hh.star
  let B₀ : H →ₗ[ℂ] H :=
    { toFun := b
      map_add' := fun x z => by
        apply ext_inner_left ℂ
        intro y
        exact tendsto_nhds_unique (hw (x + z) y)
          (by simpa only [map_add, inner_add_right] using (hw x y).add (hw z y))
      map_smul' := fun c x => by
        apply ext_inner_left ℂ
        intro y
        exact tendsto_nhds_unique (hw (c • x) y)
          (by simpa only [map_smul, inner_smul_right, RingHom.id_apply]
            using (hw x y).const_mul c) }
  let B := B₀.mkContinuous 1 (by intro x; simpa only [B₀, LinearMap.coe_mk, AddHom.coe_mk, one_mul] using hb x)
  exact ⟨B, B₀.mkContinuous_norm_le zero_le_one _, hw⟩

end

end Toolkit.Foundations.Analysis.Normed

namespace Toolkit.Foundations.Analysis.Normed

section

open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- If [a net of operators eventually belongs to a von Neumann algebra](hyp:hT)
and [all its matrix coefficients converge to those of B](hyp:hlim),
[B belongs to the algebra](goal). -/
-- @node: vonNeumann_mem_of_wot_tendsto
lemma mem_vonNeumannAlgebra_of_tendsto_inner {ι : Type*} {l : Filter ι} [NeBot l]
    (A : VonNeumannAlgebra H) (T : ι → H →L[ℂ] H) (B : H →L[ℂ] H)
    (hT : ∀ᶠ j in l, T j ∈ A)
    (hlim : ∀ x y, Tendsto (fun j => inner ℂ y (T j x)) l
      (𝓝 (inner ℂ y (B x)))) : B ∈ A := by
  have hw : Tendsto (fun j => ContinuousLinearMapWOT.ofCLM (T j)) l
      (𝓝 (ContinuousLinearMapWOT.ofCLM B)) :=
    ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr hlim
  rw [← SetLike.mem_coe, ← A.centralizer_centralizer]
  intro Q hQ
  have he : (fun j => ContinuousLinearMapWOT.ofCLM (T j) *
      ContinuousLinearMapWOT.ofCLM Q) =ᶠ[l]
      (fun j => ContinuousLinearMapWOT.ofCLM Q * ContinuousLinearMapWOT.ofCLM (T j)) := by
    filter_upwards [hT] with j hj
    exact congrArg ContinuousLinearMapWOT.ofCLM (hQ _ hj)
  have h₁ := hw.mul_const (ContinuousLinearMapWOT.ofCLM Q)
  have h₂ := hw.const_mul (ContinuousLinearMapWOT.ofCLM Q)
  exact congrArg ContinuousLinearMapWOT.toCLM (tendsto_nhds_unique (h₁.congr' he) h₂).symm

end

end Toolkit.Foundations.Analysis.Normed
