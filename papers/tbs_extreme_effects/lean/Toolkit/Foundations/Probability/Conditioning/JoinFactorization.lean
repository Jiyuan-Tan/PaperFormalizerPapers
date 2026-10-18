module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Countable.Defs
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Logic.Function.Defs
public import Mathlib.Logic.Pairwise
public import Mathlib.MeasureTheory.Function.AEEqFun
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL1
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Function.L1Space.AEEqFun
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Trim
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.MeasureTheory.PiSystem
public import Mathlib.Order.BourbakiWitt
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.ConditionallyCompletePartialOrder.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Disjoint
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Heyting.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real

/-!
# Toolkit.Foundations.Probability.Conditioning.JoinFactorization

Conditional expectations given a join of σ-algebras: dropping conditionally independent or independent information
-/

public section

namespace Toolkit.Foundations.Probability.Conditioning

noncomputable section

open MeasureTheory
variable {Ω : Type*}
variable {m G : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
open scoped BigOperators
variable {Ω : Type*} {m G H : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- Intersections of events measurable in [the first σ-algebra](hyp:m) and [the second σ-algebra](hyp:G) form a [π-system](goal). -/
lemma isPiSystem_inter (m G : MeasurableSpace Ω) :
    IsPiSystem {u : Set Ω | ∃ s t, MeasurableSet[m] s ∧ MeasurableSet[G] t ∧ u = s ∩ t} := by
  rintro _ ⟨s₁, t₁, hs₁, ht₁, rfl⟩ _ ⟨s₂, t₂, hs₂, ht₂, rfl⟩ _
  exact ⟨s₁ ∩ s₂, t₁ ∩ t₂, hs₁.inter hs₂, ht₁.inter ht₂, Set.inter_inter_inter_comm _ _ _ _⟩

/-- The [join of the two σ-algebras](goal) is generated by intersections of an event measurable in [the first σ-algebra](hyp:m) and an event measurable in [the second σ-algebra](hyp:G). -/
lemma sup_eq_generateFrom_inter (m G : MeasurableSpace Ω) :
    m ⊔ G = MeasurableSpace.generateFrom
      {u | ∃ s t, MeasurableSet[m] s ∧ MeasurableSet[G] t ∧ u = s ∩ t} := by
  refine le_antisymm (sup_le ?_ ?_) (MeasurableSpace.generateFrom_le ?_)
  · intro s hs
    exact MeasurableSpace.measurableSet_generateFrom ⟨s, Set.univ, hs, .univ, (Set.inter_univ s).symm⟩
  · intro t ht
    exact MeasurableSpace.measurableSet_generateFrom ⟨Set.univ, t, .univ, ht, (Set.univ_inter t).symm⟩
  · rintro _ ⟨s, t, hs, ht, rfl⟩
    exact (le_sup_left (a := m) s hs).inter (le_sup_right (a := m) t ht)

/-- If [the two σ-algebras lie in the ambient σ-algebra](hyp:hm,hG), [the event is measurable](hyp:hA), and [its indicator factorizes conditionally against every event of the second σ-algebra](hyp:hfac), then [conditioning that indicator on their join equals conditioning it on the first σ-algebra](goal). -/
lemma condExp_indicator_sup_eq_of_event_factorization (hm : m ≤ mΩ) (hG : G ≤ mΩ)
    {A : Set Ω} (hA : MeasurableSet A)
    (hfac : ∀ t, MeasurableSet[G] t →
      μ[(A ∩ t).indicator (fun _ => (1 : ℝ)) | m] =ᵐ[μ]
        μ[A.indicator (fun _ => (1 : ℝ)) | m] * μ[t.indicator (fun _ => (1 : ℝ)) | m]) :
    μ[A.indicator (fun _ => (1 : ℝ)) | m ⊔ G] =ᵐ[μ] μ[A.indicator (fun _ => (1 : ℝ)) | m] := by
  set iA : Ω → ℝ := A.indicator (fun _ => (1 : ℝ)) with hiA
  set g : Ω → ℝ := μ[iA | m] with hg
  have hle : m ⊔ G ≤ mΩ := sup_le hm hG
  have hiA_int : Integrable iA μ := (integrable_const (1 : ℝ)).indicator hA
  have hg_int : Integrable g μ := integrable_condExp
  have hind_int : ∀ t, MeasurableSet t → Integrable (t.indicator (fun _ => (1 : ℝ))) μ :=
    fun t ht => (integrable_const (1 : ℝ)).indicator ht
  refine (ae_eq_condExp_of_forall_setIntegral_eq hle hiA_int
    (fun s _ _ => hg_int.integrableOn) ?_
    (((stronglyMeasurable_condExp (m := m) (μ := μ) (f := iA)).mono
      (le_sup_left : m ≤ m ⊔ G)).aestronglyMeasurable)).symm
  rintro s hs -
  induction s, hs using MeasurableSpace.induction_on_inter (sup_eq_generateFrom_inter m G)
    (isPiSystem_inter m G) with
  | empty => simp
  | basic u hu =>
    obtain ⟨s, t, hs, ht, rfl⟩ := hu
    have hs0 : MeasurableSet s := hm s hs
    have ht0 : MeasurableSet t := hG t ht
    -- both sides equal `∫ x in s, g x * μ[1_t | m] x ∂μ`
    have hgt : t.indicator g = g * t.indicator (fun _ => (1 : ℝ)) := by
      funext x
      by_cases hx : x ∈ t <;> simp [hx]
    have hAt : t.indicator iA = (A ∩ t).indicator (fun _ => (1 : ℝ)) := by
      rw [hiA, Set.indicator_indicator, Set.inter_comm]
    have hleft : ∫ x in s ∩ t, g x ∂μ =
        ∫ x in s, g x * μ[t.indicator (fun _ => (1 : ℝ)) | m] x ∂μ := by
      rw [← setIntegral_indicator ht0, hgt,
        ← setIntegral_condExp hm (by rw [← hgt]; exact hg_int.indicator ht0) hs]
      refine setIntegral_congr_ae (hm s hs) ?_
      filter_upwards [condExp_mul_of_stronglyMeasurable_left (μ := μ) (m := m)
        (stronglyMeasurable_condExp (f := iA)) (by rw [← hgt]; exact hg_int.indicator ht0)
        (hind_int t ht0)] with x hx _
      exact hx
    have hright : ∫ x in s ∩ t, iA x ∂μ =
        ∫ x in s, g x * μ[t.indicator (fun _ => (1 : ℝ)) | m] x ∂μ := by
      rw [← setIntegral_indicator ht0, hAt,
        ← setIntegral_condExp hm (hind_int _ (hA.inter ht0)) hs]
      refine setIntegral_congr_ae (hm s hs) ?_
      filter_upwards [hfac t ht] with x hx _
      exact hx
    rw [hleft, hright]
  | compl t htm ih =>
    have ht0 : MeasurableSet t := hle t htm
    have h1 := integral_add_compl ht0 hg_int
    have h2 := integral_add_compl ht0 hiA_int
    have h3 : ∫ x, g x ∂μ = ∫ x, iA x ∂μ := integral_condExp hm
    linarith
  | iUnion f hfd hfm ih =>
    have hfm0 : ∀ i, MeasurableSet (f i) := fun i => hle _ (hfm i)
    have h1 := hasSum_integral_iUnion hfm0 hfd hg_int.integrableOn
    have h2 := hasSum_integral_iUnion hfm0 hfd hiA_int.integrableOn
    rw [show (fun i => ∫ x in f i, g x ∂μ) = fun i => ∫ x in f i, iA x ∂μ from
      funext fun i => ih i] at h1
    exact h1.unique h2

/-- [If the base, G, and H sigma-fields are contained in the ambient sigma-field](hyp:hm,hG,hH), [H-events and G-events conditionally factorize given the base](hyp:hfac), [the complex function is integrable](hyp:hf), and [it is H-measurable almost everywhere](hyp:hfH), [conditioning it on the base together with G agrees almost everywhere with conditioning on the base alone](goal). -/
-- @node: condExp_sup_eq_of_event_factorization
theorem condExp_sup_eq_of_event_factorization (hm : m ≤ mΩ) (hG : G ≤ mΩ) (hH : H ≤ mΩ)
    (hfac : ∀ A, MeasurableSet[H] A → ∀ t, MeasurableSet[G] t →
      μ[(A ∩ t).indicator (fun _ => (1 : ℝ)) | m] =ᵐ[μ]
        μ[A.indicator (fun _ => (1 : ℝ)) | m] * μ[t.indicator (fun _ => (1 : ℝ)) | m])
    {f : Ω → ℂ} (hf : Integrable f μ) (hfH : AEStronglyMeasurable[H] f μ) :
    μ[f | m ⊔ G] =ᵐ[μ] μ[f | m] := by
  have hmG : m ⊔ G ≤ mΩ := sup_le hm hG
  rw [← memLp_one_iff_integrable] at hf
  refine MemLp.induction_stronglyMeasurable hH ENNReal.one_ne_top
    (fun f => μ[f | m ⊔ G] =ᵐ[μ] μ[f | m]) ?_ ?_ ?_ ?_ hf hfH
  · intro c s hs _
    let L : ℝ →L[ℝ] ℂ := ContinuousLinearMap.toSpanSingleton ℝ c
    have hind : Integrable (s.indicator fun _ => (1 : ℝ)) μ :=
      (integrable_const (1 : ℝ)).indicator (hH s hs)
    have hsc : (s.indicator fun _ => c) = L ∘ s.indicator (fun _ => (1 : ℝ)) := by
      funext ω
      by_cases hω : ω ∈ s <;> simp [L, hω]
    have h1 : μ[s.indicator (fun _ => (1 : ℝ)) | m ⊔ G] =ᵐ[μ]
        μ[s.indicator (fun _ => (1 : ℝ)) | m] :=
      condExp_indicator_sup_eq_of_event_factorization hm hG (hH s hs) (hfac s hs)
    rw [hsc]
    filter_upwards [(L.comp_condExp_comm (m := m ⊔ G) hind), (L.comp_condExp_comm (m := m) hind),
      h1] with ω h2 h3 h1
    rw [← h2, ← h3, Function.comp_apply, Function.comp_apply, h1]
  · intro u v _ hu hv _ _ hu' hv'
    rw [memLp_one_iff_integrable] at hu hv
    filter_upwards [condExp_add hu hv (m ⊔ G), condExp_add hu hv m, hu', hv'] with ω h1 h2 h3 h4
    rw [h1, h2, Pi.add_apply, Pi.add_apply, h3, h4]
  · have hset : {f : lpMeas ℂ ℝ H 1 μ | μ[(f : Ω → ℂ) | m ⊔ G] =ᵐ[μ] μ[(f : Ω → ℂ) | m]} =
        {f : lpMeas ℂ ℝ H 1 μ |
          condExpL1CLM ℂ hmG μ (f : Lp ℂ 1 μ) = condExpL1CLM ℂ hm μ (f : Lp ℂ 1 μ)} := by
      ext f
      simp only [Set.mem_ofPred_eq]
      have hi : Integrable ((f : Lp ℂ 1 μ) : Ω → ℂ) μ := L1.integrable_coeFn _
      have h1 := condExp_ae_eq_condExpL1CLM hmG hi
      have h2 := condExp_ae_eq_condExpL1CLM hm hi
      rw [Integrable.toL1_coeFn] at h1 h2
      constructor
      · intro h
        exact Lp.ext (h1.symm.trans (h.trans h2))
      · intro h
        rw [h] at h1
        exact h1.trans h2.symm
    rw [hset]
    exact isClosed_eq ((condExpL1CLM ℂ hmG μ).continuous.comp continuous_subtype_val)
      ((condExpL1CLM ℂ hm μ).continuous.comp continuous_subtype_val)
  · intro u v huv _ hu
    exact (condExp_congr_ae huv.symm).trans (hu.trans (condExp_congr_ae huv))

end

end Toolkit.Foundations.Probability.Conditioning


namespace Toolkit.Foundations.Probability.Conditioning

section IndependentInformation

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Independent information can be dropped from a conditional expectation: on a probability
space, if [F, G, and H are sub-σ-algebras of the events](hyp:hF,hG,hH),
[H is independent of the information generated by F together with G](hyp:hInd), and
[a real random variable is integrable](hyp:hf) and
[almost everywhere equal to an F-measurable function](hyp:hfF), then
[its conditional expectation given G together with H equals its conditional expectation
given G almost everywhere](goal).

This is the role of independence in Williams, *Probability with Martingales*, §9.7(k), with
the σ-algebra generated by the random variable replaced by any σ-algebra for which it has a
measurable version. No regular conditional distributions or standard Borel assumptions are
needed; the proof checks the defining set-integral identity on the π-system of intersections
of a G-event with an H-event.
-/
theorem condExp_sup_eq_of_indep_sup {F G H : MeasurableSpace Ω}
    (hF : F ≤ mΩ) (hG : G ≤ mΩ) (hH : H ≤ mΩ)
    (hInd : Indep H (F ⊔ G) μ) {f : Ω → ℝ}
    (hf : Integrable f μ) (hfF : AEStronglyMeasurable[F] f μ) :
    μ[f | G ⊔ H] =ᵐ[μ] μ[f | G] := by
  classical
  -- Factorization for an a.e. measurable version of any integrable real function.
  have factor : ∀ {K : MeasurableSpace Ω} (hK : K ≤ mΩ) {k : Ω → ℝ},
      Indep K H μ → Integrable k μ → AEStronglyMeasurable[K] k μ →
      ∀ t, MeasurableSet[H] t →
        ∫ x in t, k x ∂μ = μ.real t * ∫ x, k x ∂μ := by
    intro K hK k hind hk hkm t ht
    have hce : μ[k | H] =ᵐ[μ] fun _ => ∫ x, k x ∂μ := by
      have hv := condExp_indep_eq hK hH hkm.stronglyMeasurable_mk hind
      have hi := integral_congr_ae hkm.ae_eq_mk
      exact (condExp_congr_ae hkm.ae_eq_mk).trans (hv.trans (by rw [hi]))
    calc
      ∫ x in t, k x ∂μ = ∫ x in t, μ[k | H] x ∂μ :=
        (setIntegral_condExp hH hk ht).symm
      _ = ∫ _ in t, (∫ x, k x ∂μ) ∂μ :=
        setIntegral_congr_ae (hH t ht) (hce.mono fun _ hx _ => hx)
      _ = μ.real t * ∫ x, k x ∂μ := by rw [setIntegral_const, smul_eq_mul]
  let g : Ω → ℝ := μ[f | G]
  have hg : Integrable g μ := integrable_condExp
  have hgm : StronglyMeasurable[G] g := stronglyMeasurable_condExp
  have hle : G ⊔ H ≤ mΩ := sup_le hG hH
  refine (ae_eq_condExp_of_forall_setIntegral_eq hle hf
    (fun _ _ _ => hg.integrableOn) ?_
    ((hgm.mono (le_sup_left : G ≤ G ⊔ H)).aestronglyMeasurable)).symm
  rintro u hu -
  induction u, hu using MeasurableSpace.induction_on_inter (sup_eq_generateFrom_inter G H)
    (isPiSystem_inter G H) with
  | empty => simp
  | basic u hu =>
    obtain ⟨s, t, hs, ht, rfl⟩ := hu
    have hs0 : MeasurableSet[mΩ] s := hG s hs
    have hsf : AEStronglyMeasurable[F ⊔ G] (s.indicator f) μ := by
      refine ⟨s.indicator (hfF.mk f),
        (hfF.stronglyMeasurable_mk.mono (le_sup_left : F ≤ F ⊔ G)).indicator
          (le_sup_right (a := F) s hs), ?_⟩
      filter_upwards [hfF.ae_eq_mk] with x hx
      by_cases hxs : x ∈ s <;> simp [hxs, hx]
    have hsg : AEStronglyMeasurable[G] (s.indicator g) μ :=
      (hgm.indicator hs).aestronglyMeasurable
    have hfg := factor (sup_le hF hG) hInd.symm (hf.indicator hs0) hsf t ht
    have hgg := factor hG
      (indep_of_indep_of_le_left hInd.symm (le_sup_right : G ≤ F ⊔ G))
      (hg.indicator hs0) hsg t ht
    rw [setIntegral_indicator hs0, Set.inter_comm, integral_indicator hs0] at hfg hgg
    rw [hgg, hfg, show ∫ x in s, g x ∂μ = ∫ x in s, f x ∂μ from
      setIntegral_condExp hG hf hs]
  | compl t htm ih =>
    have ht0 : MeasurableSet[mΩ] t := hle t htm
    have h1 := integral_add_compl ht0 hg
    have h2 := integral_add_compl ht0 hf
    have h3 : ∫ x, g x ∂μ = ∫ x, f x ∂μ := integral_condExp hG
    linarith
  | iUnion v hvd hvm ih =>
    have hvm0 : ∀ i, MeasurableSet[mΩ] (v i) := fun i => hle _ (hvm i)
    have h1 := hasSum_integral_iUnion hvm0 hvd hg.integrableOn
    have h2 := hasSum_integral_iUnion hvm0 hvd hf.integrableOn
    rw [show (fun i => ∫ x in v i, g x ∂μ) = fun i => ∫ x in v i, f x ∂μ from
      funext fun i => ih i] at h1
    exact h1.unique h2

end IndependentInformation

end Toolkit.Foundations.Probability.Conditioning
