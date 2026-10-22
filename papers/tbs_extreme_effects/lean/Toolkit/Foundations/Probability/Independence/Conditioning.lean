module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.SProd
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.AEMeasurable
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

/-!
# Toolkit.Foundations.Probability.Independence.Conditioning

General preservation properties of independence under conditioning on measurable events.
-/

public section

namespace Toolkit.Foundations.Probability.Independence

/-- For [a probability law, two random variables, measurability, their independence, and a measurable event](hyp:μ,f,g,hg,hfg,s,hs), [conditioning on an event determined by the second variable preserves their independence](goal). -/
lemma cond_preimage {Ω α β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (f : Ω → α) (g : Ω → β) (hg : Measurable g)
    (hfg : ProbabilityTheory.IndepFun f g μ)
    (s : Set β) (hs : MeasurableSet s) :
    ProbabilityTheory.IndepFun f g (ProbabilityTheory.cond μ (g ⁻¹' s)) := by
  open MeasureTheory ProbabilityTheory in
    let S : Set Ω := g ⁻¹' s
    have hS : MeasurableSet S := hs.preimage hg
    by_cases hzero : μ S = 0
    · rw [cond_eq_zero_of_meas_eq_zero hzero]
      simp [indepFun_iff_measure_inter_preimage_eq_mul]
    apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
    intro u v hu hv
    let A : Set Ω := f ⁻¹' u
    let B : Set Ω := g ⁻¹' v
    have hSV : MeasurableSet (s ∩ v) := hs.inter hv
    have hi : μ (A ∩ (S ∩ B)) = μ A * μ (S ∩ B) := by
      simpa only [A, B, S, Set.preimage_inter] using
        hfg.measure_inter_preimage_eq_mul u (s ∩ v) hu hSV
    have hj : μ (A ∩ S) = μ A * μ S := by
      simpa only [A, S] using hfg.measure_inter_preimage_eq_mul u s hu hs
    have hc : (μ S)⁻¹ * μ S = 1 :=
      ENNReal.inv_mul_cancel hzero (measure_ne_top μ S)
    change (cond μ S) (A ∩ B) = (cond μ S) A * (cond μ S) B
    rw [cond_apply hS, cond_apply hS, cond_apply hS]
    rw [show S ∩ (A ∩ B) = A ∩ (S ∩ B) by ext x; simp [and_left_comm], hi]
    rw [show S ∩ A = A ∩ S by ext x; simp [and_comm], hj]
    calc
      (μ S)⁻¹ * (μ A * μ (S ∩ B)) =
          ((μ S)⁻¹ * μ A * μ S) * ((μ S)⁻¹ * μ (S ∩ B)) := by
        symm
        calc
          _ = ((μ S)⁻¹ * (μ A * μ (S ∩ B))) * ((μ S)⁻¹ * μ S) := by ac_rfl
          _ = _ := by rw [hc, mul_one]
      _ = _ := by simp only [mul_assoc]

end Toolkit.Foundations.Probability.Independence

namespace Toolkit.Foundations.Probability.Independence

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

-- @node: independent_tail_pair_law
/-- If [the first variable is measurable](hyp:hf), [the second variable is measurable](hyp:hg), [the two variables are independent](hyp:hind), [the conditioning set is measurable](hyp:hs), and [that set has positive probability under the second variable](hyp:hpos), then the [conditional joint law of the pair](goal) factors into the marginal law of the first variable and the conditional law of the second. -/
lemma map_prodMk_cond_preimage_eq_prod {W A B : Type*}
    [MeasurableSpace W] [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure W) [IsProbabilityMeasure P] (f : W → A) (g : W → B)
    (hf : Measurable f) (hg : Measurable g) (hind : IndepFun f g P)
    (s : Set B) (hs : MeasurableSet s) (hpos : P (g ⁻¹' s) ≠ 0) :
    (cond P (g ⁻¹' s)).map (fun w => (f w, g w)) =
      (P.map f).prod ((cond P (g ⁻¹' s)).map g) := by
  let : IsProbabilityMeasure (cond P (g ⁻¹' s)) := cond_isProbabilityMeasure hpos
  apply Measure.ext_prod
  intro a b ha hb
  rw [Measure.map_apply (hf.prodMk hg) (ha.prod hb), Measure.prod_prod,
    Measure.map_apply hf ha, Measure.map_apply hg hb,
    cond_apply (hg hs), cond_apply (hg hs)]
  have hset : g ⁻¹' s ∩ (fun w => (f w, g w)) ⁻¹' (a ×ˢ b) =
      f ⁻¹' a ∩ g ⁻¹' (b ∩ s) := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod]
    tauto
  rw [hset, hind.measure_inter_preimage_eq_mul a (b ∩ s) ha (hb.inter hs)]
  have hset' : g ⁻¹' s ∩ g ⁻¹' b = g ⁻¹' (b ∩ s) := by ext w; simp [and_comm]
  rw [hset']
  ring

end

end Toolkit.Foundations.Probability.Independence
