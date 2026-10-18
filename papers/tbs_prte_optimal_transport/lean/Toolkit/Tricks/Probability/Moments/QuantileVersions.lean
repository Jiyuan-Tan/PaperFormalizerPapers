module

public import Causalean.Stat.Coupling.Monotone.ProductLoss.Coupling
public import Causalean.Stat.Coupling.Monotone.ProductLoss.PIT
public import Causalean.Stat.Quantile.Quantile
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Data.ENNReal.Real
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Data.Set.Countable
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Disjoint
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Set.Pairwise.Basic
public import Mathlib.Logic.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.NullMeasurable
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.MeasureTheory.OuterMeasure.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.BourbakiWitt
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Disjoint
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Heyting.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.SetNotation
public import Mathlib.Probability.CDF
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.Defs

/-!
# Quantile conventions and invariance of cross-moment formulas

The strict generalized inverse of a real law's distribution function, and the
fact that the integrals over the open unit interval of same-level and
opposite-level quantile products do not depend on which version of the quantile
function is used.

The lower generalized inverse is supplied by Causalean. The strict generalized
inverse used by Villani agrees with it except at countably many interior levels.
More generally every nondecreasing inverse-transform version has this property.
Endpoint values are immaterial because integration uses the open unit interval.
-/

@[expose] public section

namespace Toolkit.Tricks.Probability.Moments

open MeasureTheory ProbabilityTheory Set
open Causalean.Stat

/-- For [a real law](hyp:μ) and [a real probability level](hyp:t), [the strict
generalized inverse](goal) is the infimum of real cutoffs whose cumulative
probability strictly exceeds that level. -/
noncomputable def strictQuantile (μ : Measure ℝ) (t : ℝ) : ℝ :=
  sInf {x : ℝ | t < cdf μ x}

/-- For [a real probability law](hyp:μ,hprob), [the strict and lower generalized
inverses differ at only countably many levels inside the open unit interval](goal). -/
theorem countable_strictQuantile_ne_quantile (μ : Measure ℝ)
    [hprob : IsProbabilityMeasure μ] :
    {t : ℝ | t ∈ Ioo (0 : ℝ) 1 ∧ strictQuantile μ t ≠ quantile μ t}.Countable := by
  -- At a discrepant level the cdf is constant on a nonempty open interval
  -- between the two inverses. Distinct levels yield disjoint such intervals;
  -- second countability makes the family of intervals countable.
  have hne (t : ℝ) (ht : t < 1) : {x : ℝ | t < cdf μ x}.Nonempty := by
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      ((tendsto_cdf_atTop μ).eventually_const_lt ht)
    exact ⟨N, hN N le_rfl⟩
  have hbd (t : ℝ) (ht : 0 < t) : BddBelow {x : ℝ | t < cdf μ x} :=
    (bddBelow_quantileSet (μ := μ) ht).mono
      (show {x : ℝ | t < cdf μ x} ⊆ quantileSet μ t from fun x hx => by
        change t < cdf μ x at hx
        exact hx.le)
  have hle (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      quantile μ t ≤ strictQuantile μ t := by
    apply le_csInf (hne t ht.2)
    intro x hx
    exact quantile_le_of_le_cdf ht.1 hx.le
  have hflat (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (x : ℝ)
      (hx : x ∈ Ioo (quantile μ t) (strictQuantile μ t)) : cdf μ x = t := by
    apply le_antisymm
    · by_contra h
      have : strictQuantile μ t ≤ x := csInf_le (hbd t ht.1) (lt_of_not_ge h)
      exact (not_le_of_gt hx.2) this
    · exact le_cdf_of_quantile_le ht.2 hx.1.le
  have hd : PairwiseDisjoint
      {t : ℝ | t ∈ Ioo (0 : ℝ) 1 ∧ strictQuantile μ t ≠ quantile μ t}
      (fun t => Ioo (quantile μ t) (strictQuantile μ t)) := by
    intro t ht u hu htu
    apply Set.disjoint_left.2
    intro x hxt hxu
    exact htu ((hflat t ht.1 x hxt).symm.trans (hflat u hu.1 x hxu))
  exact hd.countable_of_isOpen (fun _ _ => isOpen_Ioo) (fun t ht =>
    nonempty_Ioo.mpr (lt_of_le_of_ne (hle t ht.1) (Ne.symm ht.2)))

/-- For [a real probability law](hyp:μ,hprob) and [a version of its quantile
function that is nondecreasing on the open unit interval](hyp:Q,hmono) and
[transforms a uniform draw into this law](hyp:hlaw), [that version differs from
the lower generalized inverse at only countably many interior levels](goal). -/
theorem countable_ne_quantile_of_monotoneOn_of_map_eq (μ : Measure ℝ)
    [hprob : IsProbabilityMeasure μ] (Q : ℝ → ℝ)
    (hmono : MonotoneOn Q (Ioo (0 : ℝ) 1)) (hlaw : unifOI.map Q = μ) :
    {t : ℝ | t ∈ Ioo (0 : ℝ) 1 ∧ Q t ≠ quantile μ t}.Countable := by
  -- Comparing sublevel-set measures sandwiches this version between the lower
  -- and strict inverses, so its exceptions are among the strict inverse exceptions.
  have hmeas : AEMeasurable Q unifOI :=
    aemeasurable_restrict_of_monotoneOn measurableSet_Ioo hmono
  have hray (x : ℝ) : volume (Q ⁻¹' Iic x ∩ Ioo (0 : ℝ) 1) =
      ENNReal.ofReal (cdf μ x) := by
    rw [ofReal_cdf μ x, ← hlaw, Measure.map_apply₀ hmeas
      measurableSet_Iic.nullMeasurableSet, unifOI, Measure.restrict_apply' measurableSet_Ioo]
  have hlower (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : quantile μ t ≤ Q t := by
    apply quantile_le_of_le_cdf ht.1
    have hsub : Ioo (0 : ℝ) t ⊆ Q ⁻¹' Iic (Q t) ∩ Ioo (0 : ℝ) 1 := by
      intro u hu
      have huI : u ∈ Ioo (0 : ℝ) 1 := ⟨hu.1, hu.2.trans ht.2⟩
      exact ⟨hmono huI ht hu.2.le, huI⟩
    have hv := measure_mono (μ := volume) hsub
    rw [hray, Real.volume_Ioo, sub_zero] at hv
    exact (ENNReal.ofReal_le_ofReal_iff (cdf_nonneg μ (Q t))).mp hv
  have hupper (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : Q t ≤ strictQuantile μ t := by
    have hne : {x : ℝ | t < cdf μ x}.Nonempty := by
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
        ((tendsto_cdf_atTop μ).eventually_const_lt ht.2)
      exact ⟨N, hN N le_rfl⟩
    apply le_csInf hne
    intro x hx
    change t < cdf μ x at hx
    by_contra h
    have hxQ : x < Q t := lt_of_not_ge h
    have hsub : Q ⁻¹' Iic x ∩ Ioo (0 : ℝ) 1 ⊆ Ioo (0 : ℝ) t := by
      intro u hu
      refine ⟨hu.2.1, ?_⟩
      by_contra hut
      have := hmono ht hu.2 (le_of_not_gt hut)
      exact (not_le_of_gt hxQ) (this.trans hu.1)
    have hv := measure_mono (μ := volume) hsub
    rw [hray, Real.volume_Ioo, sub_zero] at hv
    have := (ENNReal.ofReal_le_ofReal_iff ht.1.le).mp hv
    exact (not_le_of_gt hx) this
  apply (countable_strictQuantile_ne_quantile μ).mono
  intro t ht
  refine ⟨ht.1, ?_⟩
  intro heq
  exact ht.2 (le_antisymm ((hupper t ht.1).trans_eq heq) (hlower t ht.1))

/-- For [two real laws](hyp:μ,ν) and [versions of their quantiles](hyp:Q,R)
that [differ from the lower inverses at only countably many interior levels](hyp:hQ,hR),
[both the same-level and opposite-level product integrals are unchanged](goal). -/
theorem integral_quantile_mul_eq_of_countable (μ ν : Measure ℝ) (Q R : ℝ → ℝ)
    (hQ : {t : ℝ | t ∈ Ioo (0 : ℝ) 1 ∧ Q t ≠ quantile μ t}.Countable)
    (hR : {t : ℝ | t ∈ Ioo (0 : ℝ) 1 ∧ R t ≠ quantile ν t}.Countable) :
    (∫ t in Ioo (0 : ℝ) 1, Q t * R t) =
        (∫ t in Ioo (0 : ℝ) 1, quantile μ t * quantile ν t) ∧
    (∫ t in Ioo (0 : ℝ) 1, Q t * R (1 - t)) =
        (∫ t in Ioo (0 : ℝ) 1, quantile μ t * quantile ν (1 - t)) := by
  -- Countable subsets of the line are volume-null. Convert each countable
  -- exception set to an AE equality on unifOI. Transport the second equality
  -- through reflection using map_one_sub_unifOI, then use integral_congr_ae.
  have hQae : Q =ᵐ[unifOI] quantile μ := by
    apply (ae_restrict_iff' measurableSet_Ioo).2
    filter_upwards [hQ.ae_notMem volume] with t ht hmem
    exact not_ne_iff.mp (fun hne => ht ⟨hmem, hne⟩)
  have hRae : R =ᵐ[unifOI] quantile ν := by
    apply (ae_restrict_iff' measurableSet_Ioo).2
    filter_upwards [hR.ae_notMem volume] with t ht hmem
    exact not_ne_iff.mp (fun hne => ht ⟨hmem, hne⟩)
  have hRreflect : (fun t : ℝ => R (1 - t)) =ᵐ[unifOI]
      (fun t => quantile ν (1 - t)) := by
    apply ae_of_ae_map (f := fun t : ℝ => 1 - t)
      (p := fun t => R t = quantile ν t)
      (measurable_const.sub measurable_id).aemeasurable
    rw [map_one_sub_unifOI]
    exact hRae
  exact ⟨integral_congr_ae (hQae.mul hRae),
    integral_congr_ae (hQae.mul hRreflect)⟩

/-- For [two real probability laws](hyp:μ,ν,hprobμ,hprobν), [both quantile-product
integrals are unchanged when the lower inverse is replaced by the strict
generalized inverse](goal). -/
theorem integral_strictQuantile_mul_eq (μ ν : Measure ℝ)
    [hprobμ : IsProbabilityMeasure μ] [hprobν : IsProbabilityMeasure ν] :
    (∫ t in Ioo (0 : ℝ) 1, strictQuantile μ t * strictQuantile ν t) =
        (∫ t in Ioo (0 : ℝ) 1, quantile μ t * quantile ν t) ∧
    (∫ t in Ioo (0 : ℝ) 1, strictQuantile μ t * strictQuantile ν (1 - t)) =
        (∫ t in Ioo (0 : ℝ) 1, quantile μ t * quantile ν (1 - t)) := by
  exact integral_quantile_mul_eq_of_countable μ ν (strictQuantile μ) (strictQuantile ν)
    (countable_strictQuantile_ne_quantile μ) (countable_strictQuantile_ne_quantile ν)

/-- For [two real probability laws](hyp:μ,ν,hprobμ,hprobν) and [versions of
their quantile functions that are nondecreasing on the open unit
interval](hyp:Q,R,hQ,hR) and [transform uniform draws into the respective
laws](hyp:hlawQ,hlawR), [both quantile-product integrals agree with those of the
lower generalized inverses](goal). -/
theorem integral_quantile_mul_eq_of_monotoneOn_of_map_eq (μ ν : Measure ℝ)
    [hprobμ : IsProbabilityMeasure μ] [hprobν : IsProbabilityMeasure ν] (Q R : ℝ → ℝ)
    (hQ : MonotoneOn Q (Ioo (0 : ℝ) 1)) (hR : MonotoneOn R (Ioo (0 : ℝ) 1))
    (hlawQ : unifOI.map Q = μ) (hlawR : unifOI.map R = ν) :
    (∫ t in Ioo (0 : ℝ) 1, Q t * R t) =
        (∫ t in Ioo (0 : ℝ) 1, quantile μ t * quantile ν t) ∧
    (∫ t in Ioo (0 : ℝ) 1, Q t * R (1 - t)) =
        (∫ t in Ioo (0 : ℝ) 1, quantile μ t * quantile ν (1 - t)) := by
  exact integral_quantile_mul_eq_of_countable μ ν Q R
    (countable_ne_quantile_of_monotoneOn_of_map_eq μ Q hQ hlawQ)
    (countable_ne_quantile_of_monotoneOn_of_map_eq ν R hR hlawR)

end Toolkit.Tricks.Probability.Moments
