module

public import Causalean.Stat.Coupling.Basic
public import Causalean.Stat.Coupling.Monotone.ProductLoss.Coupling
public import Causalean.Stat.Coupling.Monotone.ProductLoss.PIT
public import Causalean.Stat.Quantile.Quantile
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.AEMeasurable
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.MeasureTheory.OuterMeasure.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Probability.CDF
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.Defs
public import Toolkit.Tricks.Probability.Moments.SymmetricClipping

/-!
# Clipping marginal laws and monotone couplings

How symmetric clipping acts on real laws and their couplings: a clipped
probability law has a finite second moment whatever the tails of the original,
clipping both coordinates of a coupling gives a coupling of the clipped
marginals, the quantile of a clipped law is the clipped quantile, and the
comonotone and countermonotone couplings of the clipped laws are the clipped
comonotone and countermonotone couplings of the original laws.
-/

public section

namespace Toolkit.Tricks.Probability.Moments

open MeasureTheory ProbabilityTheory Set
open Causalean.Stat

/-- For [a probability law on the real line](hyp:μ,hprob) and [an integer
clipping radius](hyp:n), [the clipped law has a finite second moment](goal). -/
theorem memLp_two_map_symmetricClip (μ : Measure ℝ) [hprob : IsProbabilityMeasure μ]
    (n : ℕ) : MemLp (fun x : ℝ => x) 2 (μ.map (symmetricClip n)) := by
  -- Pull MemLp back through the measurable map, then use MemLp.of_bound.
  apply (memLp_map_measure_iff measurable_id.aestronglyMeasurable
    (measurable_symmetricClip n).aemeasurable).2
  change MemLp (symmetricClip n) 2 μ
  exact MemLp.of_bound (measurable_symmetricClip n).aestronglyMeasurable (n : ℝ)
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using abs_symmetricClip_le n x)

/-- Given [a coupling of two real laws](hyp:hπ) and [an integer clipping
radius](hyp:n), [clipping both coordinates gives a coupling of the two clipped
marginal laws](goal). -/
theorem isCoupling_map_symmetricClip {π : Measure (ℝ × ℝ)} {μ ν : Measure ℝ}
    (hπ : IsCoupling π μ ν) (n : ℕ) :
    IsCoupling (π.map (fun z => (symmetricClip n z.1, symmetricClip n z.2)))
      (μ.map (symmetricClip n)) (ν.map (symmetricClip n)) := by
  -- Use IsCoupling's three fields and Measure.map_map.
  have hm : Measurable (fun z : ℝ × ℝ => (symmetricClip n z.1, symmetricClip n z.2)) :=
    ((measurable_symmetricClip n).comp measurable_fst).prodMk
      ((measurable_symmetricClip n).comp measurable_snd)
  have : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  refine ⟨Measure.isProbabilityMeasure_map hm.aemeasurable, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hm, ← hπ.map_fst,
      Measure.map_map (measurable_symmetricClip n) measurable_fst]
    rfl
  · rw [Measure.map_map measurable_snd hm, ← hπ.map_snd,
      Measure.map_map (measurable_symmetricClip n) measurable_snd]
    rfl

/-- For [a real probability law](hyp:μ,hprob), [an integer clipping radius](hyp:n),
and [a quantile level strictly between zero and one](hyp:ht0,ht1), [the quantile
of the clipped law equals the clipped original quantile](goal). -/
theorem quantile_map_symmetricClip (μ : Measure ℝ) [hprob : IsProbabilityMeasure μ]
    (n : ℕ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    quantile (μ.map (symmetricClip n)) t = symmetricClip n (quantile μ t) := by
  -- Compare both sides against every real cutoff using quantile_le_iff.
  -- Below -n the clipped cdf is zero, between -n and n it is the old cdf,
  -- and at or above n it is one. Treat n = 0 without a positivity assumption.
  have : IsProbabilityMeasure (μ.map (symmetricClip n)) :=
    Measure.isProbabilityMeasure_map (measurable_symmetricClip n).aemeasurable
  have hcut (x : ℝ) :
      quantile (μ.map (symmetricClip n)) t ≤ x ↔ symmetricClip n (quantile μ t) ≤ x := by
    rw [quantile_le_iff ht0 ht1]
    by_cases hlo : x < -(n : ℝ)
    · have hpre : symmetricClip n ⁻¹' Iic x = ∅ := by
        ext y
        simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
        exact not_le.mpr (hlo.trans_le (le_max_left _ _))
      rw [cdf_eq_real, Measure.real, Measure.map_apply (measurable_symmetricClip n)
        measurableSet_Iic, hpre]
      simp only [measure_empty, ENNReal.toReal_zero]
      exact iff_of_false (not_le.mpr ht0)
        (not_le.mpr (hlo.trans_le (le_max_left _ _)))
    · have hxlo : -(n : ℝ) ≤ x := le_of_not_gt hlo
      by_cases hhi : (n : ℝ) ≤ x
      · have hpre : symmetricClip n ⁻¹' Iic x = univ := by
          ext y
          simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
          exact (abs_le.mp (abs_symmetricClip_le n y)).2.trans hhi
        rw [cdf_eq_real, Measure.real, Measure.map_apply (measurable_symmetricClip n)
          measurableSet_Iic, hpre]
        simp only [measure_univ, ENNReal.toReal_one]
        exact iff_of_true ht1.le ((abs_le.mp (abs_symmetricClip_le n _)).2.trans hhi)
      · have hpre : symmetricClip n ⁻¹' Iic x = Iic x := by
          ext y
          simp [symmetricClip, hxlo, hhi]
        rw [cdf_eq_real, Measure.real, Measure.map_apply (measurable_symmetricClip n)
          measurableSet_Iic, hpre, ← Measure.real, ← cdf_eq_real,
          ← quantile_le_iff ht0 ht1]
        simp [symmetricClip, hxlo, hhi]
  exact le_antisymm ((hcut _).mpr le_rfl) ((hcut _).mp le_rfl)

/-- For [two real probability laws](hyp:μ,ν,hprobμ,hprobν) and [a clipping
radius](hyp:n), [clipping their comonotone coupling gives the comonotone coupling
of their clipped laws](goal). -/
theorem map_comonotoneCoupling_symmetricClip (μ ν : Measure ℝ)
    [hprobμ : IsProbabilityMeasure μ] [hprobν : IsProbabilityMeasure ν] (n : ℕ) :
    (comonotoneCoupling μ ν).map
        (fun z => (symmetricClip n z.1, symmetricClip n z.2)) =
      comonotoneCoupling (μ.map (symmetricClip n)) (ν.map (symmetricClip n)) := by
  -- Unfold the coupling, compose maps, and apply quantile_map_symmetricClip
  -- almost everywhere on unifOI. No global quantile measurability is needed.
  have hm : Measurable (fun z : ℝ × ℝ => (symmetricClip n z.1, symmetricClip n z.2)) :=
    ((measurable_symmetricClip n).comp measurable_fst).prodMk
      ((measurable_symmetricClip n).comp measurable_snd)
  unfold comonotoneCoupling
  rw [AEMeasurable.map_map_of_aemeasurable hm.aemeasurable
    ((aemeasurable_quantile_unifOI μ).prodMk (aemeasurable_quantile_unifOI ν))]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioo] with t ht
  simp only [Function.comp_apply]
  rw [quantile_map_symmetricClip μ n ht.1 ht.2,
    quantile_map_symmetricClip ν n ht.1 ht.2]

/-- For [two real probability laws](hyp:μ,ν,hprobμ,hprobν) and [a clipping
radius](hyp:n), [clipping their countermonotone coupling gives the countermonotone
coupling of their clipped laws](goal). -/
theorem map_countermonotoneCoupling_symmetricClip (μ ν : Measure ℝ)
    [hprobμ : IsProbabilityMeasure μ] [hprobν : IsProbabilityMeasure ν] (n : ℕ) :
    (countermonotoneCoupling μ ν).map
        (fun z => (symmetricClip n z.1, symmetricClip n z.2)) =
      countermonotoneCoupling (μ.map (symmetricClip n)) (ν.map (symmetricClip n)) := by
  -- The same map composition proof, using 0 < 1-t < 1 on the unit interval.
  have hm : Measurable (fun z : ℝ × ℝ => (symmetricClip n z.1, symmetricClip n z.2)) :=
    ((measurable_symmetricClip n).comp measurable_fst).prodMk
      ((measurable_symmetricClip n).comp measurable_snd)
  have hνmap : AEMeasurable (quantile ν) (unifOI.map (fun t : ℝ => 1 - t)) := by
    rw [map_one_sub_unifOI]
    exact aemeasurable_quantile_unifOI ν
  have hνr : AEMeasurable (fun t : ℝ => quantile ν (1 - t)) unifOI :=
    hνmap.comp_measurable (measurable_const.sub measurable_id)
  unfold countermonotoneCoupling
  rw [AEMeasurable.map_map_of_aemeasurable hm.aemeasurable
    ((aemeasurable_quantile_unifOI μ).prodMk hνr)]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioo] with t ht
  simp only [Function.comp_apply]
  rw [quantile_map_symmetricClip μ n ht.1 ht.2,
    quantile_map_symmetricClip ν n (by linarith [ht.2]) (by linarith [ht.1])]

end Toolkit.Tricks.Probability.Moments
