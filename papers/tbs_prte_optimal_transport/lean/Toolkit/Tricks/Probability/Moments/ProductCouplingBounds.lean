module

public import Causalean.Stat.Coupling.Basic
public import Causalean.Stat.Coupling.Monotone.ProductLoss.Coupling
public import Causalean.Stat.Coupling.Monotone.ProductLoss.Optimality
public import Causalean.Stat.Coupling.Monotone.ProductLoss.PIT
public import Causalean.Stat.Quantile.Quantile
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Data.ENNReal.Holder
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.AEMeasurable
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.Defs
public import Toolkit.Tricks.Probability.Moments.ClippedCouplings
public import Toolkit.Tricks.Probability.Moments.SymmetricClipping

/-!
# Sharp bounds on the expected product with given real marginals

The Hoeffding–Fréchet bounds: over all couplings of two real probability laws
with Hölder-conjugate finite moments, the expected product is least under the
countermonotone coupling and greatest under the comonotone coupling, with both
extreme values given in closed form as quantile integrals over the open unit
interval.

This extends Causalean's second-moment rearrangement theorem to all conjugate
Hölder exponents, including bounded times integrable. The minimizer and maximizer
are the existing countermonotone and comonotone quantile couplings.

Reference: Villani, Topics in Optimal Transportation, Chapter 2, Section 2.2.2,
Theorem 2.18 and Remarks 2.19, pp. 74–75. The quadratic-cost theorem gives the
product-cost theorem for fixed square-integrable marginals. Here clipping and
dominated convergence extend it beyond the quadratic-moment setting.
-/

public section

namespace Toolkit.Tricks.Probability.Moments

open MeasureTheory ProbabilityTheory Set
open Causalean.Stat
open scoped ENNReal

/-- For [two real laws](hyp:μ,ν), [the product
expectation under their comonotone coupling equals the integral of their
same-level quantile products over the open unit interval](goal). -/
theorem integral_mul_comonotoneCoupling (μ ν : Measure ℝ) :
    (∫ z, z.1 * z.2 ∂comonotoneCoupling μ ν) =
      ∫ t in Ioo (0 : ℝ) 1, quantile μ t * quantile ν t := by
  unfold comonotoneCoupling
  rw [integral_map]
  · rfl
  · exact (aemeasurable_quantile_unifOI μ).prodMk (aemeasurable_quantile_unifOI ν)
  · exact (measurable_fst.mul measurable_snd).aestronglyMeasurable

/-- For [two real laws](hyp:μ,ν), [the product
expectation under their countermonotone coupling equals the integral of their
opposite-level quantile products over the open unit interval](goal). -/
theorem integral_mul_countermonotoneCoupling (μ ν : Measure ℝ) :
    (∫ z, z.1 * z.2 ∂countermonotoneCoupling μ ν) =
      ∫ t in Ioo (0 : ℝ) 1, quantile μ t * quantile ν (1 - t) := by
  have hR : AEMeasurable (fun t : ℝ => quantile ν (1 - t)) unifOI := by
    have hq : AEMeasurable (quantile ν) (unifOI.map (fun t : ℝ => 1 - t)) := by
      rw [map_one_sub_unifOI]
      exact aemeasurable_quantile_unifOI ν
    exact hq.comp_measurable (measurable_const.sub measurable_id)
  unfold countermonotoneCoupling
  rw [integral_map]
  · rfl
  · exact (aemeasurable_quantile_unifOI μ).prodMk hR
  · exact (measurable_fst.mul measurable_snd).aestronglyMeasurable

/-- For [two real probability laws](hyp:μ,ν,hprobμ,hprobν), [conjugate Hölder
exponents](hyp:hpq), and [finite corresponding absolute moments](hyp:hμ,hν),
[both the same-level and opposite-level products of their quantiles are
integrable over the open unit interval](goal). -/
theorem integrable_quantile_mul (μ ν : Measure ℝ)
    [hprobμ : IsProbabilityMeasure μ] [hprobν : IsProbabilityMeasure ν]
    {p q : ℝ≥0∞} [hpq : p.HolderConjugate q]
    (hμ : MemLp (fun x : ℝ => x) p μ) (hν : MemLp (fun x : ℝ => x) q ν) :
    IntegrableOn (fun t => quantile μ t * quantile ν t) (Ioo (0 : ℝ) 1) ∧
    IntegrableOn (fun t => quantile μ t * quantile ν (1 - t)) (Ioo (0 : ℝ) 1) := by
  have hc := integrable_mul_of_isCoupling (isCoupling_comonotoneCoupling μ ν) hμ hν
  have ha := integrable_mul_of_isCoupling (isCoupling_countermonotoneCoupling μ ν) hμ hν
  unfold comonotoneCoupling at hc
  unfold countermonotoneCoupling at ha
  have hR : AEMeasurable (fun t : ℝ => quantile ν (1 - t)) unifOI := by
    have hq : AEMeasurable (quantile ν) (unifOI.map (fun t : ℝ => 1 - t)) := by
      rw [map_one_sub_unifOI]
      exact aemeasurable_quantile_unifOI ν
    exact hq.comp_measurable (measurable_const.sub measurable_id)
  constructor
  · exact hc.comp_aemeasurable
      ((aemeasurable_quantile_unifOI μ).prodMk (aemeasurable_quantile_unifOI ν))
  · exact ha.comp_aemeasurable ((aemeasurable_quantile_unifOI μ).prodMk hR)

/-- For [a coupling of two real probability laws](hyp:hπ,hprobμ,hprobν) with
[conjugate Hölder exponents](hyp:hpq) and [finite corresponding absolute
moments](hyp:hμ,hν), [its expected product lies between the countermonotone
and comonotone expected products](goal). -/
theorem integral_mul_bounds_of_isCoupling {π : Measure (ℝ × ℝ)} {μ ν : Measure ℝ}
    [hprobμ : IsProbabilityMeasure μ] [hprobν : IsProbabilityMeasure ν]
    {p q : ℝ≥0∞} [hpq : p.HolderConjugate q]
    (hπ : IsCoupling π μ ν) (hμ : MemLp (fun x : ℝ => x) p μ)
    (hν : MemLp (fun x : ℝ => x) q ν) :
    (∫ z, z.1 * z.2 ∂countermonotoneCoupling μ ν) ≤ (∫ z, z.1 * z.2 ∂π) ∧
    (∫ z, z.1 * z.2 ∂π) ≤ (∫ z, z.1 * z.2 ∂comonotoneCoupling μ ν) := by
  /- Proof bridge.
  For each n : ℕ let Tn z = (symmetricClip n z.1, symmetricClip n z.2).
  Its measurability is the prodMk of the two clipped coordinate maps.
  Register IsProbabilityMeasure (μ.map (symmetricClip n)) and its ν analogue
  with Measure.isProbabilityMeasure_map (measurable_symmetricClip n).aemeasurable;
  these instances are required when calling the Causalean L² bounds.

  Apply countermonotone_le_product_expectation and
  product_expectation_le_comonotone to isCoupling_map_symmetricClip hπ n,
  passing memLp_two_map_symmetricClip μ n and the ν analogue. Rewrite the
  extremal measures backwards with map_countermonotoneCoupling_symmetricClip
  and map_comonotoneCoupling_symmetricClip. A local identity, valid for every
  measure ρ on ℝ × ℝ, pulls the product integral under ρ.map Tn back to
  ∫ z, symmetricClip n z.1 * symmetricClip n z.2 ∂ρ. Use integral_map with
  Tn's aemeasurability and (measurable_fst.mul measurable_snd)'s
  aestronglyMeasurable proof; this identity needs no moment assumptions.

  Obtain product integrability under π, countermonotoneCoupling μ ν, and
  comonotoneCoupling μ ν from integrable_mul_of_isCoupling hπ hμ hν and
  the two existing isCoupling lemmas. Each corresponding clipped integral
  sequence converges by tendsto_integral_symmetricClip_mul. Finish each bound
  with le_of_tendsto_of_tendsto and Filter.Eventually.of_forall applied to the
  finite-radius inequalities. No change to p or q is needed, even at endpoints.
  -/
  have hmap (ρ : Measure (ℝ × ℝ)) (n : ℕ) :
      (∫ z, z.1 * z.2 ∂ρ.map
        (fun z => (symmetricClip n z.1, symmetricClip n z.2))) =
      ∫ z, symmetricClip n z.1 * symmetricClip n z.2 ∂ρ := by
    exact integral_map
      (((measurable_symmetricClip n).comp measurable_fst).prodMk
        ((measurable_symmetricClip n).comp measurable_snd)).aemeasurable
      (measurable_fst.mul measurable_snd).aestronglyMeasurable
  have hbounds (n : ℕ) :
      (∫ z, symmetricClip n z.1 * symmetricClip n z.2 ∂countermonotoneCoupling μ ν) ≤
        (∫ z, symmetricClip n z.1 * symmetricClip n z.2 ∂π) ∧
      (∫ z, symmetricClip n z.1 * symmetricClip n z.2 ∂π) ≤
        (∫ z, symmetricClip n z.1 * symmetricClip n z.2 ∂comonotoneCoupling μ ν) := by
    let : IsProbabilityMeasure (μ.map (symmetricClip n)) :=
      Measure.isProbabilityMeasure_map (measurable_symmetricClip n).aemeasurable
    let : IsProbabilityMeasure (ν.map (symmetricClip n)) :=
      Measure.isProbabilityMeasure_map (measurable_symmetricClip n).aemeasurable
    have hlo := countermonotone_le_product_expectation (isCoupling_map_symmetricClip hπ n)
      (memLp_two_map_symmetricClip μ n) (memLp_two_map_symmetricClip ν n)
    have hhi := product_expectation_le_comonotone (isCoupling_map_symmetricClip hπ n)
      (memLp_two_map_symmetricClip μ n) (memLp_two_map_symmetricClip ν n)
    rw [← map_countermonotoneCoupling_symmetricClip μ ν n, hmap, hmap] at hlo
    rw [← map_comonotoneCoupling_symmetricClip μ ν n, hmap, hmap] at hhi
    exact ⟨hlo, hhi⟩
  have hπlim := tendsto_integral_symmetricClip_mul π
    (integrable_mul_of_isCoupling hπ hμ hν)
  have hlolim := tendsto_integral_symmetricClip_mul (countermonotoneCoupling μ ν)
    (integrable_mul_of_isCoupling (isCoupling_countermonotoneCoupling μ ν) hμ hν)
  have hhilim := tendsto_integral_symmetricClip_mul (comonotoneCoupling μ ν)
    (integrable_mul_of_isCoupling (isCoupling_comonotoneCoupling μ ν) hμ hν)
  exact ⟨le_of_tendsto_of_tendsto hlolim hπlim
      (Filter.Eventually.of_forall fun n => (hbounds n).1),
    le_of_tendsto_of_tendsto hπlim hhilim
      (Filter.Eventually.of_forall fun n => (hbounds n).2)⟩

/-- Hoeffding–Fréchet bounds for the expected product over couplings on the real
line give the comonotone maximum and countermonotone minimum under Hölder-conjugate
moments. For [two real probability marginals](hyp:μ,ν,hprobμ,hprobν),
[conjugate exponents from one through infinity](hyp:hpq), and [finite corresponding
absolute moments, with essential boundedness at infinity](hyp:hμ,hν), [every
coupling has an integrable product, and its least and greatest possible expected
products are the opposite-level and same-level quantile integrals](goal).

Both values are attained by the existing uniform-quantile couplings, whose
integrals are identified above. The comonotone joint CDF is the minimum of the
marginal CDFs by Causalean.Stat.jointCdf_comonotoneCoupling. The module
QuantileVersions proves invariance under changes at countably many levels,
including the strict generalized inverse. MemLp at infinity is equivalent to an
almost-sure bound; for Borel probability laws on the real line this is bounded
support.
-/
theorem isLeast_and_isGreatest_integral_mul_of_isCoupling (μ ν : Measure ℝ)
    [hprobμ : IsProbabilityMeasure μ] [hprobν : IsProbabilityMeasure ν]
    {p q : ℝ≥0∞} [hpq : p.HolderConjugate q]
    (hμ : MemLp (fun x : ℝ => x) p μ) (hν : MemLp (fun x : ℝ => x) q ν) :
    (∀ π : Measure (ℝ × ℝ), IsCoupling π μ ν →
      Integrable (fun z : ℝ × ℝ => z.1 * z.2) π) ∧
    IsLeast {m : ℝ | ∃ π : Measure (ℝ × ℝ), IsCoupling π μ ν ∧
      (∫ z, z.1 * z.2 ∂π) = m}
      (∫ t in Ioo (0 : ℝ) 1, quantile μ t * quantile ν (1 - t)) ∧
    IsGreatest {m : ℝ | ∃ π : Measure (ℝ × ℝ), IsCoupling π μ ν ∧
      (∫ z, z.1 * z.2 ∂π) = m}
      (∫ t in Ioo (0 : ℝ) 1, quantile μ t * quantile ν t) := by
  refine ⟨fun π hπ => integrable_mul_of_isCoupling hπ hμ hν, ?_, ?_⟩
  · refine ⟨⟨countermonotoneCoupling μ ν, isCoupling_countermonotoneCoupling μ ν,
      integral_mul_countermonotoneCoupling μ ν⟩, ?_⟩
    rintro m ⟨π, hπ, rfl⟩
    rw [← integral_mul_countermonotoneCoupling μ ν]
    exact (integral_mul_bounds_of_isCoupling hπ hμ hν).1
  · refine ⟨⟨comonotoneCoupling μ ν, isCoupling_comonotoneCoupling μ ν,
      integral_mul_comonotoneCoupling μ ν⟩, ?_⟩
    rintro m ⟨π, hπ, rfl⟩
    rw [← integral_mul_comonotoneCoupling μ ν]
    exact (integral_mul_bounds_of_isCoupling hπ hμ hν).2

/-- For [a coupling of two real probability laws](hyp:hπ,hprobμ,hprobν),
[conjugate Hölder exponents](hyp:hpq), and [finite corresponding absolute
moments](hyp:hμ,hν), [the expected product is bounded below by the opposite-level
quantile integral and above by the same-level quantile integral](goal). -/
theorem integral_quantile_mul_bounds_of_isCoupling {π : Measure (ℝ × ℝ)}
    {μ ν : Measure ℝ} [hprobμ : IsProbabilityMeasure μ] [hprobν : IsProbabilityMeasure ν]
    {p q : ℝ≥0∞} [hpq : p.HolderConjugate q]
    (hπ : IsCoupling π μ ν) (hμ : MemLp (fun x : ℝ => x) p μ)
    (hν : MemLp (fun x : ℝ => x) q ν) :
    (∫ t in Ioo (0 : ℝ) 1, quantile μ t * quantile ν (1 - t)) ≤
        (∫ z, z.1 * z.2 ∂π) ∧
    (∫ z, z.1 * z.2 ∂π) ≤
        (∫ t in Ioo (0 : ℝ) 1, quantile μ t * quantile ν t) := by
  simpa only [integral_mul_countermonotoneCoupling, integral_mul_comonotoneCoupling] using
    integral_mul_bounds_of_isCoupling hπ hμ hν

end Toolkit.Tricks.Probability.Moments
