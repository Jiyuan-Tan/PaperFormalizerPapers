module

public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.SetLike.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.AEMeasurable
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Nat
public import Mathlib.Probability.Kernel.Basic
public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.Defs
public import Toolkit.Foundations.Probability.Processes.PathLaw
public import Toolkit.Foundations.Probability.Processes.PathProjection

/-!
# Algorithms driven by adaptive random updates

An algorithm step `X (t+1) = f t (hist t, ξ t)` draws its noise `ξ t` from a law `ν t` that
may depend on the whole history; noise spaces are arbitrary measurable spaces that may change
with time (a mini-batch, a random index set, several draws per step). This module provides the
induced kernel `updateKernel` and transition family `algorithmTransition`, the identity giving
the joint law of the history and the next state, i.i.d. noise as a constant kernel, and the
recorded variant `recordedTransition`, whose state also keeps the draw; discarding the recorded
noise recovers the original path law (`map_recorded_pathLaw`).
-/

@[expose] public section

namespace Toolkit.Foundations.Probability.Processes

universe u v

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {H Z Y : Type*} [MeasurableSpace H] [MeasurableSpace Z] [MeasurableSpace Y]

/-- The [random-update kernel](goal) samples from [the history-dependent noise law](hyp:ν)
and applies [the jointly measurable update](hyp:f,_hf), using
[the history, noise, and output spaces](hyp:H,Z,Y). -/
noncomputable def updateKernel (ν : Kernel H Z) [IsMarkovKernel ν]
    (f : H × Z → Y) (_hf : Measurable f) : Kernel H Y := (Kernel.id ×ₖ ν).map f

/-- Applying [the update map](hyp:f) with [joint measurability](hyp:hf) to
[the probability noise kernel](hyp:ν), on [the history, noise, and output spaces](hyp:H,Z,Y),
gives [a probability transition kernel](goal). -/
instance updateKernel_isMarkov (ν : Kernel H Z) [IsMarkovKernel ν]
    (f : H × Z → Y) (hf : Measurable f) : IsMarkovKernel (updateKernel ν f hf) := by
  unfold updateKernel
  exact Kernel.IsMarkovKernel.map (Kernel.id ×ₖ ν) hf

/-- With [a jointly measurable update](hyp:hf) at [the observed history](hyp:h),
[the next-state law is the noise law pushed forward by the update at that history](goal). -/
theorem updateKernel_apply (ν : Kernel H Z) [IsMarkovKernel ν]
    (f : H × Z → Y) (hf : Measurable f) (h : H) :
    updateKernel ν f hf h = (ν h).map (fun z => f (h, z)) := by
  have hm : Measurable (fun z : Z => f (h, z)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  ext s hs
  rw [updateKernel, Kernel.map_apply' _ hf _ hs,
    Kernel.id_prod_apply' _ _ (hf hs),
    Measure.map_apply hm hs]
  rfl

/-- [Measurable updates and deterministic noise selections](hyp:hf,hz) give
[exactly the deterministic composed update kernel](goal). -/
theorem updateKernel_deterministic (f : H × Z → Y) (hf : Measurable f)
    (z : H → Z) (hz : Measurable z) :
    updateKernel (Kernel.deterministic z hz) f hf =
      Kernel.deterministic (fun h => f (h, z h)) (hf.comp (measurable_id.prodMk hz)) := by
  change (Kernel.deterministic id measurable_id ×ₖ Kernel.deterministic z hz).map f = _
  rw [Kernel.deterministic_prod_deterministic measurable_id hz]
  rw [Kernel.deterministic_map (measurable_id.prodMk hz) hf]
  rfl

/-- For [a jointly measurable update](hyp:hf), [the joint history and updated-state law is
the joint history and noise law pushed forward while retaining the history](goal).

No pointwise integrability is involved; the identity is between measures on measurable sets.
-/
theorem compProd_updateKernel (μ : Measure H) [SFinite μ]
    (ν : Kernel H Z) [IsMarkovKernel ν] (f : H × Z → Y) (hf : Measurable f) :
    μ.compProd (updateKernel ν f hf) =
      (μ.compProd ν).map (fun p => (p.1, f p)) := by
  have hg : Measurable (fun p : H × Z => (p.1, f p)) := measurable_fst.prodMk hf
  ext s hs
  rw [Measure.compProd_apply hs, Measure.map_apply hg hs,
    Measure.compProd_apply (hg hs)]
  apply lintegral_congr
  intro h
  have hm : Measurable (fun z : Z => f (h, z)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  rw [updateKernel_apply, Measure.map_apply hm
    (hs.preimage measurable_prodMk_left)]
  rfl

variable {X Ξ : ℕ → Type*} [∀ t, MeasurableSpace (X t)] [∀ t, MeasurableSpace (Ξ t)]

/-- The [algorithm's transition family](goal) uses [the adaptive noise laws](hyp:ν) and
[the jointly measurable updates](hyp:f,hf) for [the changing state and noise spaces](hyp:X,Ξ). -/
noncomputable def algorithmTransition (ν : (t : ℕ) → Kernel (History X t) (Ξ t))
    [∀ t, IsMarkovKernel (ν t)] (f : (t : ℕ) → History X t × Ξ t → X (t + 1))
    (hf : ∀ t, Measurable (f t)) : Transition X := fun t => updateKernel (ν t) (f t) (hf t)

/-- [The updates](hyp:f) with [joint measurability](hyp:hf), driven by
[the adaptive noise kernels](hyp:ν) on [the changing state and noise spaces](hyp:X,Ξ),
give [a probability algorithm transition](goal) at [each time](hyp:t). -/
instance algorithmTransition_isMarkov (ν : (t : ℕ) → Kernel (History X t) (Ξ t))
    [∀ t, IsMarkovKernel (ν t)] (f : (t : ℕ) → History X t × Ξ t → X (t + 1))
    (hf : ∀ t, Measurable (f t)) (t : ℕ) :
    IsMarkovKernel (algorithmTransition ν f hf t) := by
  unfold algorithmTransition
  infer_instance

/-- Under [jointly measurable updates](hyp:hf), [the coordinate process has the algorithm's
joint history and updated-state law](goal). -/
theorem joint_history_algorithm (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (ν : (t : ℕ) → Kernel (History X t) (Ξ t)) [∀ t, IsMarkovKernel (ν t)]
    (f : (t : ℕ) → History X t × Ξ t → X (t + 1)) (hf : ∀ t, Measurable (f t)) (t : ℕ) :
    (pathLaw μ₀ (algorithmTransition ν f hf)).map
      (fun ω => (history X t ω, coordinate X (t + 1) ω)) =
    (((pathLaw μ₀ (algorithmTransition ν f hf)).map (history X t)).compProd (ν t)).map
      (fun p => (p.1, f t p)) := by
  rw [joint_history_next]
  exact compProd_updateKernel _ (ν t) (f t) (hf t)

/-- The [independent identically distributed noise kernel](goal) always samples from
[the fixed noise law](hyp:ν), regardless of [the time](hyp:t) or history in
[the changing state spaces](hyp:X). -/
def iidNoise {Z : Type*} [MeasurableSpace Z] (X : ℕ → Type*)
    [∀ t, MeasurableSpace (X t)] (ν : Measure Z) (t : ℕ) : Kernel (History X t) Z :=
  Kernel.const _ ν

/-- [The fixed probability noise law](hyp:ν) gives [a probability kernel](goal)
at [each time](hyp:t) on histories in [the changing state spaces](hyp:X). -/
instance iidNoise_isMarkov {Z : Type*} [MeasurableSpace Z] (ν : Measure Z)
    [IsProbabilityMeasure ν] (t : ℕ) : IsMarkovKernel (iidNoise X ν t) := by
  unfold iidNoise
  infer_instance

/-- The [recorded state spaces](goal) keep [the original states](hyp:X) and
[the noises](hyp:Ξ): [time zero contains only the initial state](step:1), while
[each later state also contains the preceding draw](step:2). -/
def RecordedState (X : ℕ → Type u) (Ξ : ℕ → Type v) : ℕ → Type (max u v)
  | 0 => ULift.{v} (X 0)
  | t + 1 => X (t + 1) × Ξ t

/-- The [recorded states have their product measurable spaces](goal) at
[each time](hyp:t), inherited from [the original state and noise spaces](hyp:X,Ξ). -/
instance recordedState_measurableSpace (t : ℕ) : MeasurableSpace (RecordedState X Ξ t) := by
  cases t <;> dsimp [RecordedState] <;> infer_instance

/-- The [state projection](goal) extracts the original state from a recorded state in
[the state and noise spaces](hyp:X,Ξ), [directly at time zero](step:1) and
[by discarding the retained noise later](step:2). -/
def recordedValue (X : ℕ → Type u) (Ξ : ℕ → Type v) :
    (t : ℕ) → (y : RecordedState X Ξ t) → X t
  | 0, y => y.down
  | _ + 1, y => y.1

/-- The [projected history](goal) discards all retained noise from [the recorded history](hyp:h)
through [the specified time](hyp:t) in [the state and noise spaces](hyp:X,Ξ). -/
def recordedHistory (t : ℕ) (h : History (RecordedState X Ξ) t) : History X t :=
  fun i => recordedValue X Ξ i (h i)

/-- [Projecting a recorded history is measurable](goal). -/
theorem measurable_recordedHistory (t : ℕ) : Measurable (recordedHistory (X := X) (Ξ := Ξ) t) := by
  apply measurable_pi_lambda
  intro ⟨i, hi⟩
  cases i with
  | zero => exact measurable_down.comp (measurable_pi_apply (⟨0, hi⟩ : Finset.Iic t))
  | succ i => exact measurable_fst.comp (measurable_pi_apply (⟨i + 1, hi⟩ : Finset.Iic t))

/-- The [recorded algorithm transitions](goal) use [adaptive noise laws](hyp:ν) and
[jointly measurable updates](hyp:f,hf) in [the state and noise spaces](hyp:X,Ξ), while
retaining each sampled noise alongside the new state. -/
noncomputable def recordedTransition (ν : (t : ℕ) → Kernel (History X t) (Ξ t))
    [∀ t, IsMarkovKernel (ν t)] (f : (t : ℕ) → History X t × Ξ t → X (t + 1))
    (hf : ∀ t, Measurable (f t)) : Transition (RecordedState X Ξ) :=
  fun t => updateKernel
    ((ν t).comap (recordedHistory t) (measurable_recordedHistory t))
    (fun p => (f t (recordedHistory t p.1, p.2), p.2))
    ((hf t |>.comp (((measurable_recordedHistory t).comp measurable_fst).prodMk
      measurable_snd)).prodMk measurable_snd)

/-- [The updates](hyp:f) with [joint measurability](hyp:hf), driven by
[the adaptive noise kernels](hyp:ν) on [the state and noise spaces](hyp:X,Ξ),
give [a probability recorded transition](goal) at [each time](hyp:t). -/
instance recordedTransition_isMarkov (ν : (t : ℕ) → Kernel (History X t) (Ξ t))
    [∀ t, IsMarkovKernel (ν t)] (f : (t : ℕ) → History X t × Ξ t → X (t + 1))
    (hf : ∀ t, Measurable (f t)) (t : ℕ) :
    IsMarkovKernel (recordedTransition ν f hf t) := by
  unfold recordedTransition updateKernel
  apply Kernel.IsMarkovKernel.map
  exact ((hf t |>.comp (((measurable_recordedHistory t).comp measurable_fst).prodMk
    measurable_snd)).prodMk measurable_snd)

set_option backward.isDefEq.respectTransparency false in
/-- For [jointly measurable updates](hyp:hf), [discarding the recorded noises gives exactly
the original algorithm path law](goal).

This is `map_pathLaw_projectPath` applied to `recordedValue`; the state and noise spaces need
not be standard Borel.
-/
theorem map_recorded_pathLaw (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (ν : (t : ℕ) → Kernel (History X t) (Ξ t)) [∀ t, IsMarkovKernel (ν t)]
    (f : (t : ℕ) → History X t × Ξ t → X (t + 1)) (hf : ∀ t, Measurable (f t)) :
    (pathLaw (μ₀.map ULift.up) (recordedTransition ν f hf)).map
      (fun ω t => recordedValue X Ξ t (ω t)) = pathLaw μ₀ (algorithmTransition ν f hf) := by
  have hvalue : ∀ t, Measurable (recordedValue X Ξ t) := by
    intro t
    cases t with
    | zero => exact measurable_down
    | succ t => exact measurable_fst
  have hstep : ∀ t h,
      (recordedTransition ν f hf t h).map (recordedValue X Ξ (t + 1)) =
        algorithmTransition ν f hf t (projectHistory (recordedValue X Ξ) t h) := by
    intro t h
    rw [recordedTransition, updateKernel_apply, Kernel.comap_apply]
    change ((ν t (recordedHistory t h)).map
      (fun z => (f t (recordedHistory t h, z), z))).map Prod.fst = _
    have hm : Measurable (fun z : Ξ t => (f t (recordedHistory t h, z), z)) :=
      ((hf t).comp (measurable_const.prodMk measurable_id)).prodMk measurable_id
    rw [Measure.map_map measurable_fst hm]
    exact (updateKernel_apply (ν t) (f t) (hf t) (recordedHistory t h)).symm
  have hinit : (μ₀.map (ULift.up : X 0 → RecordedState X Ξ 0)).map
      (recordedValue X Ξ 0) = μ₀ := by
    rw [Measure.map_map (hvalue 0) measurable_up]
    exact Measure.map_id
  have : IsProbabilityMeasure (μ₀.map (ULift.up : X 0 → RecordedState X Ξ 0)) :=
    Measure.isProbabilityMeasure_map measurable_up.aemeasurable
  change (pathLaw (μ₀.map ULift.up) (recordedTransition ν f hf)).map
    (projectPath (recordedValue X Ξ)) = _
  rw [map_pathLaw_projectPath _ (recordedTransition ν f hf)
    (algorithmTransition ν f hf) (recordedValue X Ξ) hvalue hstep, hinit]

end Toolkit.Foundations.Probability.Processes
