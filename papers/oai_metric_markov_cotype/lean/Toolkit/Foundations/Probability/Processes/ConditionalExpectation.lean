module

public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Prod.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.SProd
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.SetLike.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.MeasurableSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.MeasureTheory.MeasurableSpace.PreorderRestrict
public import Mathlib.MeasureTheory.Measure.AEMeasurable
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Trim
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Nat
public import Mathlib.Order.Notation
public import Mathlib.Order.Restriction
public import Mathlib.Probability.Kernel.Basic
public import Mathlib.Probability.Kernel.Composition.CompProd
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Kernel.Defs
public import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import Mathlib.Probability.Process.Filtration
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real
public import Toolkit.Foundations.Probability.Processes.NaturalFiltration
public import Toolkit.Foundations.Probability.Processes.PathLaw
public import Toolkit.Foundations.Probability.Processes.RandomUpdate

/-!
# Conditional expectations from history kernels

The one-step conditional expectation of a process: given the natural filtration at time `t`,
a payoff of the history and the next state has conditional expectation equal to its integral
against the transition kernel at the observed history (`condExp_history_next`). This module also
gives the whole-path and `k`-step versions, conditional probabilities of events, the
algorithm form (integration against the noise law) and the recorded-noise form. The initial
state may be random; the bridge is the general `condExp_of_joint_kernel`, which needs neither
boundedness nor standard Borel spaces, only integrability under the joint law.
-/

public section

namespace Toolkit.Foundations.Probability.Processes

open MeasureTheory ProbabilityTheory

variable {Ω H Z E : Type*} [MeasurableSpace Ω] [MeasurableSpace H] [MeasurableSpace Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- If [the observed history and next draw are measurable](hyp:hU,hW),
[their joint law factors through the history kernel](hyp:hjoint), and
[the payoff is integrable under this joint law](hyp:hF), then
[its conditional expectation given the history is its kernel integral](goal).

The proof uses the set-integral characterization of `condExp` and Fubini for
`Measure.compProd`; no regular conditional distribution is needed.
-/
theorem condExp_of_joint_kernel (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → H) (W : Ω → Z) (hU : Measurable U) (hW : Measurable W)
    (κ : Kernel H Z) [IsMarkovKernel κ]
    (hjoint : μ.map (fun ω => (U ω, W ω)) = (μ.map U).compProd κ)
    (F : H × Z → E) (hF : Integrable F ((μ.map U).compProd κ)) :
    μ[(fun ω => F (U ω, W ω)) | MeasurableSpace.comap U inferInstance] =ᵐ[μ]
      fun ω => ∫ z, F (U ω, z) ∂κ (U ω) := by
  have hUW : Measurable (fun ω => (U ω, W ω)) := hU.prodMk hW
  have hFmap : Integrable F (μ.map (fun ω => (U ω, W ω))) := by
    rwa [hjoint]
  have hFcomp : Integrable (fun ω => F (U ω, W ω)) μ :=
    hFmap.comp_aemeasurable hUW.aemeasurable
  have hI : Integrable (fun h => ∫ z, F (h, z) ∂κ h) (μ.map U) := by
    rw [Measure.compProd] at hF
    simpa using hF.integral_compProd
  refine (ae_eq_condExp_of_forall_setIntegral_eq hU.comap_le hFcomp
    (fun _ _ _ => (hI.comp_aemeasurable hU.aemeasurable).integrableOn) ?_ ?_).symm
  · rintro _ ⟨s, hs, rfl⟩ _
    simp only [Function.comp_apply]
    rw [← setIntegral_map hs hI.aestronglyMeasurable hU.aemeasurable]
    have hmap := setIntegral_map (hs.prod MeasurableSet.univ)
      hFmap.aestronglyMeasurable hUW.aemeasurable
    simp only [Set.mk_preimage_prod, Set.preimage_univ, Set.inter_univ] at hmap
    rw [← hmap, hjoint]
    simpa only [Set.mk_preimage_prod, Set.preimage_univ, Set.inter_univ,
      Measure.restrict_univ] using
      (Measure.setIntegral_compProd hs MeasurableSet.univ hF.integrableOn).symm
  · exact hI.aestronglyMeasurable.comp_ae_measurable' hU.aemeasurable

variable {X : ℕ → Type*} [∀ t, MeasurableSpace (X t)]

/-- For [a payoff integrable under the joint history and next-state law](hyp:hF),
[its one-step conditional expectation is its integral against the transition law](goal). -/
theorem condExp_history_next (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (κ : Transition X) [∀ t, IsMarkovKernel (κ t)] (t : ℕ)
    (F : History X t × X (t + 1) → E)
    (hF : Integrable F (((pathLaw μ₀ κ).map (history X t)).compProd (κ t))) :
    (pathLaw μ₀ κ)[(fun ω => F (history X t ω, coordinate X (t + 1) ω)) |
      naturalFiltration X t] =ᵐ[pathLaw μ₀ κ]
      fun ω => ∫ x, F (history X t ω, x) ∂κ t (history X t ω) := by
  rw [naturalFiltration, Filtration.piLE_eq_comap_frestrictLe]
  exact condExp_of_joint_kernel (pathLaw μ₀ κ) (history X t)
    (coordinate X (t + 1)) (Preorder.measurable_frestrictLe t)
    (measurable_pi_apply (t + 1)) (κ t) (joint_history_next μ₀ κ t) F hF

/-- [An integrable future path payoff](hyp:hF) has [conditional expectation obtained by
restarting the trajectory kernel from the observed history](goal).

This extends Mathlib's fixed-initial-history `Kernel.condExp_traj` to a random initial state,
through `joint_history_path`.
-/
theorem condExp_path (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (κ : Transition X) [∀ t, IsMarkovKernel (κ t)] (t : ℕ) (F : Path X → E)
    (hF : Integrable F (pathLaw μ₀ κ)) :
    (pathLaw μ₀ κ)[F | naturalFiltration X t] =ᵐ[pathLaw μ₀ κ]
      fun ω => ∫ ω', F ω' ∂Kernel.traj κ t (history X t ω) := by
  have hj : Measurable (fun ω : Path X => (history X t ω, ω)) :=
    (Preorder.measurable_frestrictLe t).prodMk measurable_id
  have hm :
      ((((pathLaw μ₀ κ).map (history X t)).compProd (Kernel.traj κ t)).map Prod.snd) =
        pathLaw μ₀ κ := by
    rw [← joint_history_path, Measure.map_map measurable_snd hj]
    exact Measure.map_id
  have hi : Integrable (fun p : History X t × Path X => F p.2)
      (((pathLaw μ₀ κ).map (history X t)).compProd (Kernel.traj κ t)) := by
    have hFm : Integrable F
        ((((pathLaw μ₀ κ).map (history X t)).compProd (Kernel.traj κ t)).map Prod.snd) :=
      hm.symm ▸ hF
    exact hFm.comp_aemeasurable measurable_snd.aemeasurable
  rw [naturalFiltration, Filtration.piLE_eq_comap_frestrictLe]
  exact condExp_of_joint_kernel (pathLaw μ₀ κ) (history X t) id
    (Preorder.measurable_frestrictLe t) measurable_id (Kernel.traj κ t)
    (joint_history_path μ₀ κ t) (fun p => F p.2) hi

/-- [An integrable statistic of a later history](hyp:hG) has [conditional expectation obtained
by integrating over the intervening finite trajectory](goal).

This is the `k`-step version; integrability is required only under the later history's law.
-/
theorem condExp_history_future (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (κ : Transition X) [∀ t, IsMarkovKernel (κ t)] (t k : ℕ)
    (G : History X (t + k) → E)
    (hG : Integrable G ((pathLaw μ₀ κ).map (history X (t + k)))) :
    (pathLaw μ₀ κ)[(fun ω => G (history X (t + k) ω)) | naturalFiltration X t]
      =ᵐ[pathLaw μ₀ κ] fun ω =>
        ∫ h, G h ∂Kernel.partialTraj κ t (t + k) (history X t ω) := by
  have hj : Measurable (fun ω : Path X => (history X t ω, history X (t + k) ω)) :=
    (Preorder.measurable_frestrictLe t).prodMk (Preorder.measurable_frestrictLe (t + k))
  have hm :
      ((((pathLaw μ₀ κ).map (history X t)).compProd
        (Kernel.partialTraj κ t (t + k))).map Prod.snd) =
          (pathLaw μ₀ κ).map (history X (t + k)) := by
    rw [← joint_history_future, Measure.map_map measurable_snd hj]
    rfl
  have hi : Integrable (fun p : History X t × History X (t + k) => G p.2)
      (((pathLaw μ₀ κ).map (history X t)).compProd (Kernel.partialTraj κ t (t + k))) := by
    have hGm : Integrable G
        ((((pathLaw μ₀ κ).map (history X t)).compProd
          (Kernel.partialTraj κ t (t + k))).map Prod.snd) := hm.symm ▸ hG
    exact hGm.comp_aemeasurable measurable_snd.aemeasurable
  rw [naturalFiltration, Filtration.piLE_eq_comap_frestrictLe]
  exact condExp_of_joint_kernel (pathLaw μ₀ κ) (history X t) (history X (t + k))
    (Preorder.measurable_frestrictLe t) (Preorder.measurable_frestrictLe (t + k))
    (Kernel.partialTraj κ t (t + k)) (joint_history_future μ₀ κ t (t + k))
    (fun p => G p.2) hi

/-- [A measurable event involving the history and next state](hyp:hA) has
[conditional probability equal to its transition-kernel probability](goal). -/
theorem condExp_history_event (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (κ : Transition X) [∀ t, IsMarkovKernel (κ t)] (t : ℕ)
    (A : Set (History X t × X (t + 1))) (hA : MeasurableSet A) :
    (pathLaw μ₀ κ)[(fun ω => A.indicator (fun _ => (1 : ℝ))
      (history X t ω, coordinate X (t + 1) ω)) | naturalFiltration X t]
      =ᵐ[pathLaw μ₀ κ] fun ω =>
        (κ t (history X t ω)).real {x | (history X t ω, x) ∈ A} := by
  have hi : Integrable (A.indicator (fun _ => (1 : ℝ)))
      (((pathLaw μ₀ κ).map (history X t)).compProd (κ t)) :=
    (integrable_const (1 : ℝ)).indicator hA
  refine (condExp_history_next μ₀ κ t _ hi).trans ?_
  filter_upwards [] with ω
  have hs : MeasurableSet {x | (history X t ω, x) ∈ A} :=
    hA.preimage measurable_prodMk_left
  classical
  calc
    _ = ∫ x, {x | (history X t ω, x) ∈ A}.indicator (fun _ => (1 : ℝ)) x
        ∂κ t (history X t ω) := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    _ = _ := integral_indicator_one hs

variable {Ξ : ℕ → Type*} [∀ t, MeasurableSpace (Ξ t)]

/-- With [jointly measurable updates](hyp:hf) and [an integrable next-state payoff](hyp:hF),
[the algorithm's conditional expectation is the adaptive noise integral
of the updated payoff](goal). -/
theorem condExp_algorithm_next (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (ν : (t : ℕ) → Kernel (History X t) (Ξ t)) [∀ t, IsMarkovKernel (ν t)]
    (f : (t : ℕ) → History X t × Ξ t → X (t + 1)) (hf : ∀ t, Measurable (f t))
    (t : ℕ) (F : History X t × X (t + 1) → E)
    (hF : Integrable F (((pathLaw μ₀ (algorithmTransition ν f hf)).map (history X t)).compProd
      (algorithmTransition ν f hf t))) :
    (pathLaw μ₀ (algorithmTransition ν f hf))[(fun ω =>
      F (history X t ω, coordinate X (t + 1) ω)) | naturalFiltration X t]
      =ᵐ[pathLaw μ₀ (algorithmTransition ν f hf)] fun ω =>
        ∫ z, F (history X t ω, f t (history X t ω, z)) ∂ν t (history X t ω) := by
  refine (condExp_history_next μ₀ (algorithmTransition ν f hf) t F hF).trans ?_
  have hi := (Measure.integrable_compProd_iff hF.aestronglyMeasurable).mp hF |>.1
  have hi' := ae_of_ae_map (Preorder.measurable_frestrictLe t).aemeasurable hi
  filter_upwards [hi'] with ω hω
  change (∫ x, F (history X t ω, x) ∂updateKernel (ν t) (f t) (hf t)
    (history X t ω)) = _
  change Integrable (fun x => F (history X t ω, x))
    (updateKernel (ν t) (f t) (hf t) (history X t ω)) at hω
  rw [updateKernel_apply] at hω ⊢
  exact integral_map
    ((hf t).comp (measurable_const.prodMk measurable_id)).aemeasurable
    hω.aestronglyMeasurable

/-- With [jointly measurable updates](hyp:hf) and [an integrable history-and-noise payoff](hyp:hF),
[the recorded noise has conditional expectation given by its adaptive sampling law](goal).

The conditioning history retains earlier noises, while the current sampling law sees the
projected original history, exactly as in the recorded construction.
-/
theorem condExp_recorded_noise (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (ν : (t : ℕ) → Kernel (History X t) (Ξ t)) [∀ t, IsMarkovKernel (ν t)]
    (f : (t : ℕ) → History X t × Ξ t → X (t + 1)) (hf : ∀ t, Measurable (f t))
    (t : ℕ) (F : History X t × Ξ t → E)
    (hF : Integrable (fun p => F (recordedHistory t p.1, p.2))
      (((pathLaw (μ₀.map ULift.up) (recordedTransition ν f hf)).map
        (history (RecordedState X Ξ) t)).compProd
        ((ν t).comap (recordedHistory t) (measurable_recordedHistory t)))) :
    (pathLaw (μ₀.map ULift.up) (recordedTransition ν f hf))[(fun ω =>
      F (recordedHistory t (history (RecordedState X Ξ) t ω), (ω (t + 1)).2)) |
        naturalFiltration (RecordedState X Ξ) t]
      =ᵐ[pathLaw (μ₀.map ULift.up) (recordedTransition ν f hf)] fun ω =>
        ∫ z, F (recordedHistory t (history (RecordedState X Ξ) t ω), z)
          ∂ν t (recordedHistory t (history (RecordedState X Ξ) t ω)) := by
  let μinit : Measure (RecordedState X Ξ 0) := μ₀.map ULift.up
  letI hinit : IsProbabilityMeasure μinit :=
    Measure.isProbabilityMeasure_map measurable_up.aemeasurable
  let μ : Measure (Path (RecordedState X Ξ)) :=
    pathLaw μinit (recordedTransition ν f hf)
  letI : IsProbabilityMeasure μ :=
    pathLaw_isProbabilityMeasure _ _
  let U := history (RecordedState X Ξ) t
  let κ : Kernel (History (RecordedState X Ξ) t) (Ξ t) :=
    (ν t).comap (recordedHistory t) (measurable_recordedHistory t)
  let g : History (RecordedState X Ξ) t × Ξ t → RecordedState X Ξ (t + 1) :=
    fun p => (f t (recordedHistory t p.1, p.2), p.2)
  have hg : Measurable g :=
    ((hf t).comp (((measurable_recordedHistory t).comp measurable_fst).prodMk
      measurable_snd)).prodMk measurable_snd
  have hU : Measurable U := Preorder.measurable_frestrictLe t
  have hW : Measurable (fun ω : Path (RecordedState X Ξ) => (ω (t + 1)).2) :=
    measurable_snd.comp (measurable_pi_apply (t + 1))
  have hj : μ.map (fun ω => (U ω, (ω (t + 1)).2)) = (μ.map U).compProd κ := by
    have hj0 := joint_history_next (X := RecordedState X Ξ)
      μinit (recordedTransition ν f hf) t
    change μ.map (fun ω => (U ω, ω (t + 1))) =
      (μ.map U).compProd (updateKernel κ g hg) at hj0
    rw [compProd_updateKernel _ κ g hg] at hj0
    have hp : Measurable (fun p : History (RecordedState X Ξ) t ×
        RecordedState X Ξ (t + 1) => (p.1, p.2.2)) :=
      measurable_fst.prodMk (measurable_snd.comp measurable_snd)
    have hm := congrArg (fun ρ => ρ.map (fun p : History (RecordedState X Ξ) t ×
      RecordedState X Ξ (t + 1) => (p.1, p.2.2))) hj0
    rw [Measure.map_map hp (hU.prodMk (measurable_pi_apply (t + 1))),
      Measure.map_map hp (measurable_fst.prodMk hg)] at hm
    simpa only [Function.comp_def, g, Prod.mk.eta, Measure.map_id, Measure.map_id'] using hm
  rw [naturalFiltration, Filtration.piLE_eq_comap_frestrictLe]
  exact condExp_of_joint_kernel μ U _ hU hW κ hj
    (fun p => F (recordedHistory t p.1, p.2)) hF

end Toolkit.Foundations.Probability.Processes
