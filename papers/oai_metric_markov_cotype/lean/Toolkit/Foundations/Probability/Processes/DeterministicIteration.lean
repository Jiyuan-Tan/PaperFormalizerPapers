module

public import Mathlib.Data.Countable.Defs
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.FunLike.Equiv
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Logic.Unique
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.Dirac
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Map
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Nat
public import Mathlib.Order.RelClasses
public import Mathlib.Probability.Kernel.Defs
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import Toolkit.Foundations.Probability.Processes.PathLaw

/-!
# Current-state deterministic updates and homogeneous Markov kernels

Special cases of the full-history construction. A deterministic iteration
`x (t+1) = g t (x t)` (the state type may still change with the step) is the Dirac case: its
path law is the point mass at the ordinary iterate sequence, which is the trajectory almost
surely. A time-homogeneous Markov chain on a fixed state space applies one kernel to the latest
state at every step.
-/

@[expose] public section

namespace Toolkit.Foundations.Probability.Processes

open MeasureTheory ProbabilityTheory

variable {X : ℕ → Type*} [∀ t, MeasurableSpace (X t)]

/-- The [current-state history update](goal) applies [the time-dependent update maps](hyp:g)
to the last coordinate of [the observed history](hyp:h) at [the chosen time](hyp:t)
in [the changing state spaces](hyp:X). -/
def currentStateUpdate (g : (t : ℕ) → X t → X (t + 1)) (t : ℕ)
    (h : History X t) : X (t + 1) := g t (h ⟨t, Finset.mem_Iic.mpr le_rfl⟩)

/-- [Measurable current-state update maps](hyp:hg) induce
[measurable full-history updates](goal) at every time. -/
theorem measurable_currentStateUpdate (g : (t : ℕ) → X t → X (t + 1))
    (hg : ∀ t, Measurable (g t)) (t : ℕ) : Measurable (currentStateUpdate g t) :=
  (hg t).comp (measurable_pi_apply _)

/-- The [ordinary deterministic iterate sequence](goal) in [the changing state spaces](hyp:X)
uses [an initial state](hyp:x) and [time-dependent current-state updates](hyp:g):
[its initial value is that state](step:1), and [each next value is the corresponding update
of the previous value](step:2). -/
def currentStatePath (x : X 0) (g : (t : ℕ) → X t → X (t + 1)) : (t : ℕ) → X t
  | 0 => x
  | t + 1 => g t (currentStatePath x g t)

/-- [The full-history deterministic trajectory equals the ordinary current-state
iterate sequence at every time](goal). -/
theorem deterministicPath_currentState_eq (x : X 0)
    (g : (t : ℕ) → X t → X (t + 1)) :
    deterministicPath x (currentStateUpdate g) = currentStatePath x g := by
  funext t
  induction t with
  | zero =>
    rw [deterministicPath, iterateInduction]
    suffices hs : uniqueElim (α := fun i : Finset.Iic 0 => X i) x
        (⟨0, by simp⟩ : Finset.Iic 0) = x by
      simpa [initialHistory, currentStatePath] using hs
    exact uniqueElim_default (α := fun i : Finset.Iic 0 => X i) x
  | succ t ih =>
    rw [deterministicPath_succ]
    change g t (deterministicPath x (currentStateUpdate g) t) =
      g t (currentStatePath x g t)
    rw [ih]

/-- The [current-state deterministic transition family](goal) uses
[the time-dependent updates](hyp:g), whose [measurability](hyp:hg) is required,
in [the changing state spaces](hyp:X). -/
noncomputable def currentStateDeterministicTransition (g : (t : ℕ) → X t → X (t + 1))
    (hg : ∀ t, Measurable (g t)) : Transition X :=
  deterministicTransition (currentStateUpdate g) (measurable_currentStateUpdate g hg)

/-- [Measurable current-state updates](hyp:g,hg) in [the changing spaces](hyp:X)
give [a probability transition kernel](goal) at [each step](hyp:t). -/
instance currentStateDeterministicTransition_isMarkov
    (g : (t : ℕ) → X t → X (t + 1)) (hg : ∀ t, Measurable (g t)) (t : ℕ) :
    IsMarkovKernel (currentStateDeterministicTransition g hg t) := by
  unfold currentStateDeterministicTransition
  infer_instance

/-- [Measurable current-state updates](hyp:hg) generate
[a path law concentrated on the ordinary iterate sequence](goal). -/
theorem pathLaw_currentState_deterministic (x : X 0)
    (g : (t : ℕ) → X t → X (t + 1)) (hg : ∀ t, Measurable (g t)) :
    pathLaw (Measure.dirac x) (currentStateDeterministicTransition g hg) =
      Measure.dirac (currentStatePath x g) := by
  change pathLaw (Measure.dirac x)
    (deterministicTransition (currentStateUpdate g) (measurable_currentStateUpdate g hg)) = _
  rw [pathLaw_deterministic, deterministicPath_currentState_eq]

/-- When state singletons are measurable, [measurable current-state updates](hyp:hg)
give [the ordinary deterministic iterate sequence almost surely](goal). -/
theorem ae_eq_currentStatePath [∀ t, MeasurableSingletonClass (X t)]
    (x : X 0) (g : (t : ℕ) → X t → X (t + 1)) (hg : ∀ t, Measurable (g t)) :
    ∀ᵐ ω ∂pathLaw (Measure.dirac x) (currentStateDeterministicTransition g hg),
      ω = currentStatePath x g := by
  rw [pathLaw_currentState_deterministic]
  simp

variable {S : Type*} [MeasurableSpace S]

/-- The [homogeneous Markov transition family](goal) uses
[one fixed current-state kernel](hyp:q) on [the fixed state space](hyp:S) at every step. -/
def homogeneousTransition (q : Kernel S S) : Transition (fun _ => S) :=
  markovTransition (fun _ => q)

/-- [A fixed probability current-state kernel](hyp:q) on [the state space](hyp:S)
gives [a probability homogeneous history kernel](goal) at [every step](hyp:t). -/
instance homogeneousTransition_isMarkov (q : Kernel S S) [IsMarkovKernel q] (t : ℕ) :
    IsMarkovKernel (homogeneousTransition q t) := by
  unfold homogeneousTransition
  infer_instance

/-- At [the observed history](hyp:h), [a homogeneous Markov transition applies
the same fixed kernel to the latest state](goal). -/
theorem homogeneousTransition_apply (q : Kernel S S) (t : ℕ)
    (h : History (fun _ => S) t) :
    homogeneousTransition q t h = q (h ⟨t, Finset.mem_Iic.mpr le_rfl⟩) := rfl

end Toolkit.Foundations.Probability.Processes
