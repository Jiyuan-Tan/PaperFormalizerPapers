module

public import Causalean.Stat.Coupling.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Data.ENNReal.Real
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.NNReal.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.MeasurableSpace.Prod
public import Mathlib.MeasureTheory.Measure.AEMeasurable
public import Mathlib.MeasureTheory.Measure.Comap
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.NullMeasurable
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Order.Basic
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.ConditionallyCompletePartialOrder.Defs
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Defs

/-!
# One-Wasserstein cost, Lipschitz contrasts and weak duality

The one-Wasserstein cost `wasserstein1 μ ν` is the infimum, over probability
couplings (Causalean's `Causalean.Stat.IsCoupling`), of the expected distance
between the two coordinates; no existence of an optimal coupling is built in,
and an empty coupling set gives cost infinity. The Lipschitz contrast
`lipschitzContrast μ ν f` is the signed difference of expectations.

This module provides:
* weak Kantorovich–Rubinstein duality: the positive part of the contrast of a
  one-Lipschitz function is at most the cost of any coupling, hence at most
  `wasserstein1` (under integrability, or finite first moments);
* transfer to a carrying set: laws giving full mass to a measurable set have
  the same cost and the same contrasts as their laws on that subtype;
* couplings of finite probability mixtures from a transport matrix of mixture
  weights, and a cost bound for product laws concentrated near two points.

Strong duality on compact metric spaces is in
`Toolkit.Foundations.MeasureTheory.KantorovichRubinstein`.

Reference: C. Villani, *Topics in Optimal Transportation*, Theorem 1.14;
C. Villani, *Optimal Transport, Old and New*, Remark 6.5.
-/

@[expose] public section

namespace Toolkit.Foundations.MeasureTheory

open _root_.MeasureTheory
open scoped BigOperators ENNReal

section Basic

variable {X : Type*}

/-- For [two measures](hyp:μ,ν) on [a Borel extended metric space](hyp:X),
their [one-Wasserstein cost](goal) is the infimum, over all probability
couplings with those marginals, of the expected distance between the two
coordinates (infinite when no coupling exists). -/
noncomputable def wasserstein1 [PseudoEMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ ν : Measure X) : ℝ≥0∞ :=
  ⨅ (π : Measure (X × X)) (_ : Causalean.Stat.IsCoupling π μ ν),
    ∫⁻ z, edist z.1 z.2 ∂π

/-- For [two measures](hyp:μ,ν) on [a measurable space](hyp:X) and
[a real test function](hyp:f), the [Lipschitz contrast](goal) is the
expectation of the function under the first measure minus its expectation
under the second. -/
noncomputable def lipschitzContrast [MeasurableSpace X]
    (μ ν : Measure X) (f : X → ℝ) : ℝ :=
  ∫ x, f x ∂μ - ∫ x, f x ∂ν

variable [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- [Any probability coupling of two measures](hyp:hπ) has [expected distance
between its coordinates at least the measures' one-Wasserstein cost](goal). -/
theorem wasserstein1_le_cost {μ ν : Measure X} {π : Measure (X × X)}
    (hπ : Causalean.Stat.IsCoupling π μ ν) :
    wasserstein1 μ ν ≤ ∫⁻ z, edist z.1 z.2 ∂π := by
  exact iInf_le_of_le π (iInf_le_of_le hπ le_rfl)

omit [BorelSpace X] in
/-- For [a probability coupling of two measures](hyp:hπ) and [a one-Lipschitz
function](hyp:hf) [integrable under both measures](hyp:hfμ,hfν), [the positive
part of the function's expectation contrast is at most the coupling's expected
distance](goal). -/
theorem lipschitzContrast_le_cost {μ ν : Measure X} {π : Measure (X × X)}
    {f : X → ℝ} (hπ : Causalean.Stat.IsCoupling π μ ν)
    (hf : LipschitzWith 1 f) (hfμ : Integrable f μ) (hfν : Integrable f ν) :
    ENNReal.ofReal (lipschitzContrast μ ν f) ≤ ∫⁻ z, edist z.1 z.2 ∂π := by
  have hfst : Integrable f (π.map Prod.fst) := hπ.map_fst.symm ▸ hfμ
  have hsnd : Integrable f (π.map Prod.snd) := hπ.map_snd.symm ▸ hfν
  have hμint : ∫ x, f x ∂μ = ∫ z, f z.1 ∂π := by
    rw [← hπ.map_fst]
    exact integral_map measurable_fst.aemeasurable hfst.aestronglyMeasurable
  have hνint : ∫ x, f x ∂ν = ∫ z, f z.2 ∂π := by
    rw [← hπ.map_snd]
    exact integral_map measurable_snd.aemeasurable hsnd.aestronglyMeasurable
  calc
    ENNReal.ofReal (lipschitzContrast μ ν f) ≤
        edist (∫ x, f x ∂μ) (∫ x, f x ∂ν) := by
      rw [lipschitzContrast, edist_dist, Real.dist_eq]
      exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ = edist (∫ z, f z.1 ∂π) (∫ z, f z.2 ∂π) := by rw [hμint, hνint]
    _ ≤ ∫⁻ z, edist (f z.1) (f z.2) ∂π :=
      edist_integral_le_lintegral_edist
        (hfst.comp_measurable measurable_fst) (hsnd.comp_measurable measurable_snd)
    _ ≤ ∫⁻ z, edist z.1 z.2 ∂π := lintegral_mono fun z => by
      simpa using hf.edist_le_mul z.1 z.2

/-- For [a one-Lipschitz function](hyp:hf) that is [integrable under both
measures](hyp:hfμ,hfν), [the positive part of its expectation contrast is at
most the measures' one-Wasserstein cost](goal). -/
theorem lipschitzContrast_le_wasserstein1 {μ ν : Measure X} {f : X → ℝ}
    (hf : LipschitzWith 1 f) (hfμ : Integrable f μ) (hfν : Integrable f ν) :
    ENNReal.ofReal (lipschitzContrast μ ν f) ≤ wasserstein1 μ ν := by
  refine le_iInf fun π => le_iInf fun hπ => ?_
  exact lipschitzContrast_le_cost hπ hf hfμ hfν

/-- Under [a probability measure](hyp:hμ), [a one-Lipschitz function](hyp:hf)
is [integrable](goal) whenever [the distance to a fixed reference point
has finite expectation](hyp:hmoment). -/
theorem integrable_lipschitz_of_firstMoment {μ : Measure X}
    [hμ : IsProbabilityMeasure μ] {f : X → ℝ} (x₀ : X)
    (hf : LipschitzWith 1 f) (hmoment : Integrable (fun x => dist x x₀) μ) :
    Integrable f μ := by
  refine ((integrable_const |f x₀|).add hmoment).mono'
    hf.continuous.aestronglyMeasurable ?_
  filter_upwards [] with x
  calc
    ‖f x‖ ≤ ‖f x₀‖ + ‖f x - f x₀‖ := norm_le_insert' _ _
    _ ≤ |f x₀| + dist x x₀ := by
      simpa only [Real.norm_eq_abs, ← Real.dist_eq, one_mul, NNReal.coe_one] using
        add_le_add_right (hf.dist_le_mul x x₀) |f x₀|

/-- **Weak Kantorovich–Rubinstein duality.** For [two probability
measures](hyp:hμ,hν) with [finite first moments about a common reference
point](hyp:x₀,hμmoment,hνmoment) and [any one-Lipschitz test function](hyp:hf),
[the positive part of its expectation contrast is at most the measures'
one-Wasserstein cost](goal). -/
theorem lipschitzContrast_le_wasserstein1_of_firstMoment {μ ν : Measure X}
    [hμ : IsProbabilityMeasure μ] [hν : IsProbabilityMeasure ν]
    (x₀ : X) (hμmoment : Integrable (fun x => dist x x₀) μ)
    (hνmoment : Integrable (fun x => dist x x₀) ν)
    {f : X → ℝ} (hf : LipschitzWith 1 f) :
    ENNReal.ofReal (lipschitzContrast μ ν f) ≤ wasserstein1 μ ν := by
  exact lipschitzContrast_le_wasserstein1 hf
    (integrable_lipschitz_of_firstMoment x₀ hf hμmoment)
    (integrable_lipschitz_of_firstMoment x₀ hf hνmoment)

end Basic

section Subtype

variable {X : Type*} [MeasurableSpace X]

/-- [A probability law](hyp:hμ) giving [full mass](hyp:hμK) to
[a measurable set](hyp:hK) induces [a probability law on that set whose
pushforward along the inclusion recovers the original law](goal). -/
theorem probability_comap_subtype (μ : Measure X) [hμ : IsProbabilityMeasure μ]
    (K : Set X) (hK : MeasurableSet K) (hμK : μ K = 1) :
    IsProbabilityMeasure (μ.comap ((↑) : K → X)) ∧
      (μ.comap ((↑) : K → X)).map ((↑) : K → X) = μ := by
  refine ⟨⟨?_⟩, ?_⟩
  · rw [comap_subtype_coe_apply hK]
    simpa only [Set.image_univ, Subtype.range_coe] using hμK
  · rw [map_comap_subtype_coe hK]
    apply Measure.restrict_eq_self_of_ae_mem
    exact (ae_mem_iff_measure_eq hK.nullMeasurableSet).2 (by simpa using hμK)

/-- For [two probability laws](hyp:hμ,hν) giving [full mass to the same
measurable set](hyp:hK,hμK,hνK), [each real test function](hyp:f) has [the
same expectation contrast under the original laws as its restriction has under
their laws on that set](goal).

The test function need not be measurable away from the carrying set. -/
theorem lipschitzContrast_eq_subtype_comap (μ ν : Measure X)
    [hμ : IsProbabilityMeasure μ] [hν : IsProbabilityMeasure ν]
    (K : Set X) (hK : MeasurableSet K) (hμK : μ K = 1) (hνK : ν K = 1)
    (f : X → ℝ) :
    lipschitzContrast μ ν f =
      lipschitzContrast (μ.comap ((↑) : K → X)) (ν.comap ((↑) : K → X))
        (fun x : K => f x.val) := by
  have hμmap := (probability_comap_subtype μ K hK hμK).2
  have hνmap := (probability_comap_subtype ν K hK hνK).2
  unfold lipschitzContrast
  conv_lhs =>
    rw [← hμmap, ← hνmap]
    rw [(MeasurableEmbedding.subtype_coe hK).integral_map,
      (MeasurableEmbedding.subtype_coe hK).integral_map]

variable [MetricSpace X] [BorelSpace X]

/-- For [two probability laws](hyp:hμ,hν) giving [full mass to a measurable
set](hyp:hK,hμK,hνK), [their one-Wasserstein cost equals the cost between
their laws on that set](goal).

Neither compactness nor second countability of the ambient space is needed. -/
theorem wasserstein1_subtype_comap (μ ν : Measure X)
    [hμ : IsProbabilityMeasure μ] [hν : IsProbabilityMeasure ν]
    (K : Set X) (hK : MeasurableSet K) (hμK : μ K = 1) (hνK : ν K = 1) :
    wasserstein1 μ ν =
      wasserstein1 (μ.comap ((↑) : K → X)) (ν.comap ((↑) : K → X)) := by
  let i : K → X := Subtype.val
  let e : K × K → X × X := Prod.map i i
  have hi : MeasurableEmbedding i := MeasurableEmbedding.subtype_coe hK
  have he : MeasurableEmbedding e := hi.prodMap hi
  have hμmap := (probability_comap_subtype μ K hK hμK).2
  have hνmap := (probability_comap_subtype ν K hK hνK).2
  have hfst (ρ : Measure (K × K)) :
      (ρ.map e).map Prod.fst = (ρ.map Prod.fst).map i := by
    rw [Measure.map_map measurable_fst he.measurable,
      Measure.map_map hi.measurable measurable_fst]
    rfl
  have hsnd (ρ : Measure (K × K)) :
      (ρ.map e).map Prod.snd = (ρ.map Prod.snd).map i := by
    rw [Measure.map_map measurable_snd he.measurable,
      Measure.map_map hi.measurable measurable_snd]
    rfl
  have hcost (ρ : Measure (K × K)) :
      (∫⁻ z, edist z.1 z.2 ∂(ρ.map e)) = ∫⁻ z, edist z.1 z.2 ∂ρ := by
    rw [he.lintegral_map]
    rfl
  apply le_antisymm
  · refine le_iInf fun ρ => le_iInf fun hρ => ?_
    let := hρ.isProbabilityMeasure
    have hp : Causalean.Stat.IsCoupling (ρ.map e) μ ν := by
      refine ⟨ρ.isProbabilityMeasure_map he.measurable.aemeasurable, ?_, ?_⟩
      · rw [hfst, hρ.map_fst]
        exact hμmap
      · rw [hsnd, hρ.map_snd]
        exact hνmap
    exact (wasserstein1_le_cost hp).trans_eq (hcost ρ)
  · refine le_iInf fun π => le_iInf fun hπ => ?_
    let := hπ.isProbabilityMeasure
    have hμae : ∀ᵐ x ∂μ, x ∈ K :=
      (ae_mem_iff_measure_eq hK.nullMeasurableSet).2 (by simpa using hμK)
    have hνae : ∀ᵐ x ∂ν, x ∈ K :=
      (ae_mem_iff_measure_eq hK.nullMeasurableSet).2 (by simpa using hνK)
    have hπfst : ∀ᵐ z ∂π, z.1 ∈ K := by
      apply (ae_map_iff (p := fun x => x ∈ K) measurable_fst.aemeasurable hK).1
      simpa only [hπ.map_fst] using hμae
    have hπsnd : ∀ᵐ z ∂π, z.2 ∈ K := by
      apply (ae_map_iff (p := fun x => x ∈ K) measurable_snd.aemeasurable hK).1
      simpa only [hπ.map_snd] using hνae
    have hπrange : ∀ᵐ z ∂π, z ∈ Set.range e := by
      filter_upwards [hπfst, hπsnd] with z hz₁ hz₂
      exact ⟨(⟨z.1, hz₁⟩, ⟨z.2, hz₂⟩), rfl⟩
    have hmap : (π.comap e).map e = π := by
      rw [he.map_comap]
      exact Measure.restrict_eq_self_of_ae_mem hπrange
    have hp : Causalean.Stat.IsCoupling (π.comap e)
        (μ.comap i) (ν.comap i) := by
      refine ⟨?_, ?_, ?_⟩
      · apply (Measure.isProbabilityMeasure_map_iff he.measurable.aemeasurable).1
        rw [hmap]
        infer_instance
      · have hm : ((π.comap e).map Prod.fst).map i = μ := by
          rw [← hfst, hmap, hπ.map_fst]
        rw [← hm, hi.comap_map]
      · have hm : ((π.comap e).map Prod.snd).map i = ν := by
          rw [← hsnd, hmap, hπ.map_snd]
        rw [← hm, hi.comap_map]
    apply (wasserstein1_le_cost hp).trans_eq
    rw [← hcost, hmap]

end Subtype

section Mixture

/-- Given [two finite families of probability laws](hyp:ρ,σ,hρ,hσ),
[mixture weights for the first family with total mass one](hyp:a,ha), [weights
for the second family](hyp:b), and [a weight matrix](hyp:p) [whose row sums are
the first weights](hyp:hrow) and [whose column sums are the second
weights](hyp:hcol), [the matrix-weighted sum of the product laws is a coupling
of the two mixtures](goal). -/
theorem finite_product_mixture_coupling {X ι κ : Type*} [MeasurableSpace X]
    [Fintype ι] [Fintype κ] (ρ : ι → Measure X) (σ : κ → Measure X)
    (hρ : ∀ i, IsProbabilityMeasure (ρ i)) (hσ : ∀ j, IsProbabilityMeasure (σ j))
    (a : ι → ℝ≥0∞) (b : κ → ℝ≥0∞) (p : ι → κ → ℝ≥0∞)
    (ha : ∑ i, a i = 1) (hrow : ∀ i, ∑ j, p i j = a i)
    (hcol : ∀ j, ∑ i, p i j = b j) :
    Causalean.Stat.IsCoupling (∑ i, ∑ j, p i j • (ρ i).prod (σ j))
      (∑ i, a i • ρ i) (∑ j, b j • σ j) := by
  let (i : ι) : IsProbabilityMeasure (ρ i) := hρ i
  let (j : κ) : IsProbabilityMeasure (σ j) := hσ j
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · simpa only [Measure.finsetSum_apply, Measure.smul_apply, measure_univ,
      smul_eq_mul, mul_one, hrow] using ha
  · simp_rw [Measure.map_finset_sum measurable_fst.aemeasurable,
      Measure.map_smul, Measure.map_fst_prod, measure_univ, one_smul]
    simp_rw [← Finset.sum_smul, hrow]
  · simp_rw [Measure.map_finset_sum measurable_snd.aemeasurable,
      Measure.map_smul, Measure.map_snd_prod, measure_univ, one_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, hcol]

/-- For [two probability laws](hyp:ρ,σ,hρ,hσ) whose draws [lie almost surely
within a common nonnegative radius of two reference points](hyp:x₀,y₀,hε,hρmesh,hσmesh),
[the expected distance under their product law is at most the distance between
the reference points plus twice that radius](goal). -/
theorem lintegral_edist_prod_le_of_ae_dist_le {X : Type*}
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (ρ σ : Measure X) [hρ : IsProbabilityMeasure ρ] [hσ : IsProbabilityMeasure σ]
    (x₀ y₀ : X) {ε : ℝ} (hε : 0 ≤ ε)
    (hρmesh : ∀ᵐ x ∂ρ, dist x x₀ ≤ ε)
    (hσmesh : ∀ᵐ y ∂σ, dist y y₀ ≤ ε) :
    (∫⁻ z, edist z.1 z.2 ∂ρ.prod σ) ≤
      edist x₀ y₀ + ENNReal.ofReal (2 * ε) := by
  have hx : ∀ᵐ z ∂ρ.prod σ, dist z.1 x₀ ≤ ε :=
    measurePreserving_fst.quasiMeasurePreserving.ae hρmesh
  have hy : ∀ᵐ z ∂ρ.prod σ, dist z.2 y₀ ≤ ε :=
    measurePreserving_snd.quasiMeasurePreserving.ae hσmesh
  calc
    (∫⁻ z, edist z.1 z.2 ∂ρ.prod σ) ≤
        ∫⁻ _z, edist x₀ y₀ + ENNReal.ofReal (2 * ε) ∂ρ.prod σ := by
      apply lintegral_mono_ae
      filter_upwards [hx, hy] with z hx hy
      rw [edist_dist, edist_dist, ← ENNReal.ofReal_add dist_nonneg (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have htri := dist_triangle4 z.1 x₀ y₀ z.2
      rw [dist_comm y₀ z.2] at htri
      linarith
    _ = edist x₀ y₀ + ENNReal.ofReal (2 * ε) := by simp

end Mixture

end Toolkit.Foundations.MeasureTheory
