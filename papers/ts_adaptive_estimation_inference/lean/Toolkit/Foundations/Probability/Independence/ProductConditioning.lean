module

public import Causalean.Mathlib.Probability.IdentDistrib.CenteredSum
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Data.Countable.Defs
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Data.ENNReal.BigOperators
public import Mathlib.Data.ENNReal.Real
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Set.Prod
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Trim
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Notation
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.MetricSpace.ProperSpace.Real
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Order.Real

/-!
# Toolkit.Foundations.Probability.Independence.ProductConditioning

Conditioning product laws on coordinate rectangles
-/

public section

namespace Toolkit.Foundations.Probability.Independence

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

-- @node: sample_cond_pi_rectangle
/-- Given [measurable coordinate conditioning sets](hyp:hs) with [positive probability in every coordinate](hyp:hpos), [conditioning a product law on their rectangle equals the product of the coordinatewise conditional laws](goal). -/
lemma cond_pi_univ_pi {I Z : Type*} [Fintype I] [MeasurableSpace Z]
    (μ : I → Measure Z) [∀ i, IsProbabilityMeasure (μ i)]
    (s : I → Set Z) (hs : ∀ i, MeasurableSet (s i))
    (hpos : ∀ i, μ i (s i) ≠ 0) :
    cond (Measure.pi μ) (Set.univ.pi s) = Measure.pi (fun i => cond (μ i) (s i)) := by
  letI (i : I) : IsProbabilityMeasure (cond (μ i) (s i)) := cond_isProbabilityMeasure (hpos i)
  apply (Measure.pi_eq fun u hu => ?_).symm
  rw [cond_apply (MeasurableSet.univ_pi hs), ← Set.pi_inter_distrib,
    Measure.pi_pi, Measure.pi_pi]
  simp_rw [cond_apply (hs _)]
  rw [ENNReal.prod_inv_distrib (fun i _ j _ _ => Or.inr (measure_ne_top (μ j) (s j))),
    ← Finset.prod_mul_distrib]

end

end Toolkit.Foundations.Probability.Independence

namespace Toolkit.Foundations.Probability.Independence

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-- If [the nuisance map is measurable](hyp:hg), [the nuisance and sample have the stated product joint law](hyp:hjoint), [the joint bad event is measurable](hyp:hE), [the probability bound is delta](hyp:delta), and [almost every nuisance-specific section of that event has probability at most delta](hyp:hsections), then [the realized joint bad event has probability at most delta](goal). -/
-- @node: excess_independent_event_probability_le
lemma measure_prodMk_mem_le_of_ae_measure_section_le
    {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (Q : Measure B) [SFinite Q]
    (g : Ω → A) (sample : Ω → B) (hg : Measurable g)
    (hjoint : MeasurePreserving (fun w => (g w, sample w)) mu ((mu.map g).prod Q))
    (E : Set (A × B)) (hE : MeasurableSet E) (delta : ℝ≥0∞)
    (hsections : ∀ᵐ w ∂mu, Q {b | (g w, b) ∈ E} ≤ delta) :
    mu {w | (g w, sample w) ∈ E} ≤ delta := by
  have hsec : ∀ᵐ a ∂mu.map g, Q (Prod.mk a ⁻¹' E) ≤ delta := by
    apply (ae_map_iff hg.aemeasurable
      (measurableSet_le (measurable_measure_prodMk_left hE) measurable_const)).2
    exact hsections
  calc
    mu {w | (g w, sample w) ∈ E} = ((mu.map g).prod Q) E := by
      rw [← hjoint.map_eq, Measure.map_apply hjoint.measurable hE]
      rfl
    _ = ∫⁻ a, Q (Prod.mk a ⁻¹' E) ∂mu.map g := Measure.prod_apply hE
    _ ≤ ∫⁻ _a, delta ∂mu.map g := lintegral_mono_ae hsec
    _ = delta := by simp [Measure.map_apply hg MeasurableSet.univ]

end

end Toolkit.Foundations.Probability.Independence

namespace Toolkit.Foundations.Probability.Independence

section

set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- If [training and calibration information are both contained in the ambient
information](hyp:ht,hc) and [these two information sets are independent](hyp:hindep),
[the success relation is jointly measurable for these two information sets](hyp:hR),
[the failure probability ζ lies strictly between zero and one](hyp:hζ), and
[almost every fixed training sample gives calibration success probability at least
1 − ζ](hyp:hsections), then [success with both arguments evaluated on the observed
sample is a measurable event with probability at least 1 − ζ](goal). -/
-- @node: rdiv_event_of_independent_frozen_sections
lemma measurableSet_and_le_measureReal_diag_of_indep_of_ae_section
    (P : Measure Ω) [IsProbabilityMeasure P]
    (mt mc : MeasurableSpace Ω) (ht : mt ≤ mΩ) (hc : mc ≤ mΩ)
    (hindep : Indep mt mc P) (R : Ω → Ω → Prop)
    (hR : MeasurableSet[mt.prod mc] {p : Ω × Ω | R p.1 p.2})
    (ζ : ℝ) (hζ : ζ ∈ Set.Ioo (0 : ℝ) 1)
    (hsections : ∀ᵐ training ∂P, 1 - ζ ≤ P.real {ω | R training ω}) :
    @MeasurableSet Ω mΩ {ω | R ω ω} ∧ 1 - ζ ≤ P.real {ω | R ω ω} := by
  let mp := mt
  letI : MeasurableSpace Ω := mΩ
  let mf := mc
  letI : MeasurableSpace Ω := mΩ
  have hp : mp ≤ mΩ := ht
  have hf : mf ≤ mΩ := hc
  have hdiag : @Measurable Ω (Ω × Ω) mΩ (mp.prod mf)
      (fun ω => (ω, ω)) := (measurable_id'' hp).prodMk (measurable_id'' hf)
  refine ⟨hdiag hR, ?_⟩
  have hmap : @Measure.map Ω Ω mΩ mf id P = P.trim hf := by
    apply @Measure.ext Ω mf
    intro s hs
    rw [@Measure.map_apply Ω Ω mΩ mf P id (measurable_id'' hf) s hs]
    exact (trim_measurableSet_eq hf hs).symm
  have hjoint := Causalean.Mathlib.indep_trim_prod_map_eq
    (mΩ := mΩ) (mβ := mf) (μ := P) mp hp (Z := id) (by
      letI : MeasurableSpace Ω := mf
      exact (measurable_id'' hf).aemeasurable)
    (by simpa only [MeasurableSpace.comap_id] using
      hindep)
  rw [hmap] at hjoint
  have hsec (ω : Ω) : @MeasurableSet Ω mf {ω' | R ω ω'} := hR.preimage
    (measurable_const.prodMk measurable_id)
  have hbound : ∀ᵐ ω ∂P,
      ENNReal.ofReal (1 - ζ) ≤ (P.trim hf) {ω' | R ω ω'} := by
    filter_upwards [hsections] with ω hω
    rw [trim_measurableSet_eq hf (hsec ω)]
    exact (ENNReal.ofReal_le_ofReal hω).trans_eq
      (ENNReal.ofReal_toReal (measure_ne_top P _))
  have hbmeas : @MeasurableSet Ω mp
      {ω | ENNReal.ofReal (1 - ζ) ≤ (P.trim hf) {ω' | R ω ω'}} :=
    by
      letI : MeasurableSpace Ω := mp
      exact measurableSet_le measurable_const
        (@measurable_measure_prodMk_left Ω Ω mp mf (P.trim hf) inferInstance _ hR)
  have hbtrim : ∀ᵐ ω ∂P.trim hp,
      ENNReal.ofReal (1 - ζ) ≤ (P.trim hf) {ω' | R ω ω'} := by
    rw [ae_iff] at hbound ⊢
    exact (@trim_measurableSet_eq Ω mp mΩ P _ hp hbmeas.compl).trans hbound
  have hprob : ENNReal.ofReal (1 - ζ) ≤ P {ω | R ω ω} := by
    calc
      _ = ∫⁻ _ω, ENNReal.ofReal (1 - ζ) ∂P.trim hp := by
        rw [lintegral_const, trim_measurableSet_eq hp (@MeasurableSet.univ Ω mp)]
        simp
      _ ≤ ∫⁻ ω, (P.trim hf) {ω' | R ω ω'} ∂P.trim hp :=
        lintegral_mono_ae hbtrim
      _ = @Measure.prod Ω Ω mp mf (P.trim hp) (P.trim hf) {p | R p.1 p.2} :=
        (by
          letI : MeasurableSpace Ω := mp
          exact (@Measure.prod_apply Ω Ω mp mf (P.trim hp) (P.trim hf) inferInstance _ hR).symm)
      _ = P {ω | R ω ω} := by
        rw [← hjoint]
        exact @Measure.map_apply Ω (Ω × Ω) mΩ (mp.prod mf) P
          (fun ω => (ω, ω)) hdiag _ hR
  have ht := ENNReal.toReal_mono (measure_ne_top P _) hprob
  rwa [ENNReal.toReal_ofReal (by linarith [hζ.2])] at ht

end

end Toolkit.Foundations.Probability.Independence
