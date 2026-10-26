module

public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.Countable.Defs
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.FunLike.Equiv
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Unique
public import Mathlib.MeasureTheory.Constructions.Projective
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.MeasurableSpace.PreorderRestrict
public import Mathlib.MeasureTheory.Measure.AEMeasurable
public import Mathlib.MeasureTheory.Measure.Dirac
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Map
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Lattice
public import Mathlib.Order.Nat
public import Mathlib.Order.RelClasses
public import Mathlib.Order.Restriction
public import Mathlib.Probability.Kernel.Basic
public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.Probability.Kernel.Composition.CompNotation
public import Mathlib.Probability.Kernel.Composition.Lemmas
public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.Defs
public import Mathlib.Probability.Kernel.IonescuTulcea.Maps
public import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Processes with changing state spaces and history-dependent transitions

A process is given by state spaces `X t` that may change with time, an initial law on `X 0`,
and transition kernels `κ t` from the whole history through time `t` to the next state. Its
path law `pathLaw μ₀ κ` is Mathlib's Ionescu–Tulcea trajectory measure `Kernel.trajMeasure`;
no standard Borel assumption is needed. This module provides the history and coordinate maps,
the joint laws of a history with the next state, with the whole path and with a later history,
and the two basic special cases: Markov kernels that only read the latest state, and
deterministic (Dirac) updates, whose path law is concentrated on the iterate sequence.

Reference: O. Kallenberg, *Foundations of Modern Probability*, 3rd ed., Springer 2021,
Theorem 8.24.
-/

@[expose] public section

namespace Toolkit.Foundations.Probability.Processes

open MeasureTheory ProbabilityTheory

variable (X : ℕ → Type*) [∀ t, MeasurableSpace (X t)]

/-- The [history through a given time](goal) records states in [the changing state spaces](hyp:X)
up to and including [that time](hyp:t). -/
abbrev History (t : ℕ) := (i : Finset.Iic t) → X i

/-- A [path](goal) contains one state at every time in [the changing state spaces](hyp:X). -/
abbrev Path := (t : ℕ) → X t

/-- The [observed history](goal) restricts [a path](hyp:ω) in
[the changing state spaces](hyp:X) to [the times through the observation time](hyp:t). -/
def history (t : ℕ) (ω : Path X) : History X t := Preorder.frestrictLe t ω

/-- The [coordinate process](goal) reads the state at [the requested time](hyp:t) from
[a path](hyp:ω) in [the changing state spaces](hyp:X). -/
def coordinate (t : ℕ) (ω : Path X) : X t := ω t

/-- The [transition family](goal) specifies a law for the next state, given the entire finite
past, in [the changing state spaces](hyp:X). -/
abbrev Transition := (t : ℕ) → Kernel (History X t) (X (t + 1))

variable {X}

/-- The [path law](goal) starts from [the initial distribution](hyp:μ₀) and uses
[the history-dependent transition laws](hyp:κ) on [the changing state spaces](hyp:X). -/
noncomputable def pathLaw (μ₀ : Measure (X 0)) (κ : Transition X)
    [∀ t, IsMarkovKernel (κ t)] : Measure (Path X) := Kernel.trajMeasure μ₀ κ

/-- The [path law is a probability distribution](goal) when [the initial law](hyp:μ₀)
is a probability distribution and [the history transitions](hyp:κ) are probability kernels
on [the changing state spaces](hyp:X). -/
instance pathLaw_isProbabilityMeasure (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (κ : Transition X) [∀ t, IsMarkovKernel (κ t)] :
    IsProbabilityMeasure (pathLaw μ₀ κ) := by
  unfold pathLaw
  infer_instance

/-- [The initial coordinate has exactly the initial law](goal). -/
theorem map_coordinate_zero (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (κ : Transition X) [∀ t, IsMarkovKernel (κ t)] :
    (pathLaw μ₀ κ).map (coordinate X 0) = μ₀ := by
  change (Kernel.trajMeasure μ₀ κ).map
    ((MeasurableEquiv.piUnique (fun i : Finset.Iic 0 => X i)) ∘
      Preorder.frestrictLe 0) = μ₀
  rw [← Measure.map_map (MeasurableEquiv.measurable _) (Preorder.measurable_frestrictLe 0)]
  rw [Kernel.trajMeasure, Measure.map_comp _ _ (Preorder.measurable_frestrictLe 0),
    Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]
  exact MeasurableEquiv.map_map_symm _

/-- [The joint distribution of the history and the next state is the history law followed by
the transition kernel](goal). -/
theorem joint_history_next (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (κ : Transition X) [∀ t, IsMarkovKernel (κ t)] (t : ℕ) :
    (pathLaw μ₀ κ).map (fun ω => (history X t ω, coordinate X (t + 1) ω)) =
      ((pathLaw μ₀ κ).map (history X t)).compProd (κ t) := by
  exact Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure.symm

/-- [The joint history and entire path law is the history law followed by the trajectory
kernel restarted at that history](goal).

This lifts `Kernel.partialTraj_compProd_traj` through the random initial state; it is the
measure-level input for conditional expectations of arbitrary future path payoffs.
-/
theorem joint_history_path (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (κ : Transition X) [∀ t, IsMarkovKernel (κ t)] (t : ℕ) :
    (pathLaw μ₀ κ).map (fun ω => (history X t ω, ω)) =
      ((pathLaw μ₀ κ).map (history X t)).compProd (Kernel.traj κ t) := by
  symm
  change ((Kernel.trajMeasure μ₀ κ).map (Preorder.frestrictLe t)).compProd
    (Kernel.traj κ t) =
      (Kernel.trajMeasure μ₀ κ).map (fun x => (Preorder.frestrictLe t x, x))
  rw [Measure.compProd_eq_comp_prod, Kernel.trajMeasure,
    Measure.map_comp _ _ (by fun_prop), Kernel.traj_map_frestrictLe,
    Measure.comp_assoc, Measure.map_comp _ _ (by fun_prop)]
  congr with x₀ : 1
  rw [Kernel.comp_apply, ← Measure.compProd_eq_comp_prod,
    Kernel.map_apply _ (by fun_prop), Kernel.partialTraj_compProd_traj (Nat.zero_le t)]

/-- [The joint law of any two finite histories is the first history law followed by
the finite trajectory kernel to the second observation time](goal).

The two observation times need not be ordered: a later history and the restriction to an
earlier one are both covered.
-/
theorem joint_history_future (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (κ : Transition X) [∀ t, IsMarkovKernel (κ t)] (a b : ℕ) :
    (pathLaw μ₀ κ).map (fun ω => (history X a ω, history X b ω)) =
      ((pathLaw μ₀ κ).map (history X a)).compProd (Kernel.partialTraj κ a b) := by
  have h := congrArg (fun ρ : Measure (History X a × Path X) =>
    ρ.map (Prod.map id (history X b))) (joint_history_path μ₀ κ a)
  change ((pathLaw μ₀ κ).map (fun ω => (Preorder.frestrictLe a ω, ω))).map
    (Prod.map id (Preorder.frestrictLe b)) =
      (((pathLaw μ₀ κ).map (Preorder.frestrictLe a)).compProd (Kernel.traj κ a)).map
        (Prod.map id (Preorder.frestrictLe b)) at h
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.compProd_map (Preorder.measurable_frestrictLe b),
    Kernel.traj_map_frestrictLe] at h
  exact h

/-- The [Markov transition family](goal) applies [each current-state kernel](hyp:q) to the
latest coordinate in the history of [the changing state spaces](hyp:X). -/
def markovTransition (q : (t : ℕ) → Kernel (X t) (X (t + 1))) : Transition X :=
  fun t => (q t).comap (fun h => h ⟨t, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _)

/-- [The current-state probability kernels](hyp:q) on [the changing state spaces](hyp:X)
induce [a probability history kernel](goal) at [each time](hyp:t). -/
instance markovTransition_isMarkov (q : (t : ℕ) → Kernel (X t) (X (t + 1)))
    [∀ t, IsMarkovKernel (q t)] (t : ℕ) : IsMarkovKernel (markovTransition q t) := by
  unfold markovTransition
  infer_instance

/-- At [the observed history](hyp:h), [a Markov history kernel only uses
the most recent state](goal). -/
theorem markovTransition_apply (q : (t : ℕ) → Kernel (X t) (X (t + 1)))
    (t : ℕ) (h : History X t) :
    markovTransition q t h = q t (h ⟨t, Finset.mem_Iic.mpr le_rfl⟩) := rfl

/-- The [deterministic transition family](goal) assigns all probability to
[each history update](hyp:f),
whose [measurability](hyp:hf) is required, in [the changing state spaces](hyp:X). -/
noncomputable def deterministicTransition (f : (t : ℕ) → History X t → X (t + 1))
    (hf : ∀ t, Measurable (f t)) : Transition X := fun t => Kernel.deterministic (f t) (hf t)

/-- [The history updates](hyp:f) with [measurability](hyp:hf) on
[the changing state spaces](hyp:X) give [a probability transition kernel](goal)
at [each time](hyp:t). -/
instance deterministicTransition_isMarkov (f : (t : ℕ) → History X t → X (t + 1))
    (hf : ∀ t, Measurable (f t)) (t : ℕ) :
    IsMarkovKernel (deterministicTransition f hf t) := by
  unfold deterministicTransition
  infer_instance

/-- The [initial history](goal) consists of [one initial state](hyp:x) in
[the time-zero state space](hyp:X). -/
def initialHistory (x : X 0) : History X 0 :=
  (MeasurableEquiv.piUnique (fun i : Finset.Iic 0 => X i)).symm x

/-- [Turning an initial state into a one-coordinate history is measurable](goal). -/
theorem measurable_initialHistory : Measurable (initialHistory (X := X)) := by
  apply measurable_pi_lambda
  intro i
  have hi : i = (⟨0, by simp⟩ : Finset.Iic 0) :=
    Subtype.ext (Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.property))
  subst i
  exact measurable_id

/-- The [deterministic path](goal) starts at [the initial state](hyp:x) and iterates
[the full-history updates](hyp:f) in [the changing state spaces](hyp:X). -/
noncomputable def deterministicPath (x : X 0) (f : (t : ℕ) → History X t → X (t + 1)) :
    Path X := iterateInduction (initialHistory x) f

/-- [The deterministic path obeys the full-history update rule at every step](goal). -/
theorem deterministicPath_succ (x : X 0)
    (f : (t : ℕ) → History X t → X (t + 1)) (t : ℕ) :
    deterministicPath x f (t + 1) = f t (history X t (deterministicPath x f)) := by
  change iterateInduction (initialHistory x) f (t + 1) = _
  rw [iterateInduction]
  rfl

/-- For [measurable history updates](hyp:hf), [every finite trajectory law is concentrated
on the corresponding deterministic iterates](goal).

This finite-dimensional statement holds from an arbitrary initial history and time; it is the
input for `pathLaw_deterministic`.
-/
theorem partialTraj_deterministic (f : (t : ℕ) → History X t → X (t + 1))
    (hf : ∀ t, Measurable (f t)) (a b : ℕ) (initial : History X a) :
    Kernel.partialTraj (deterministicTransition f hf) a b initial =
      Measure.dirac (history X b (iterateInduction initial f)) := by
  classical
  induction b with
  | zero =>
      rw [Kernel.partialTraj_zero, Kernel.deterministic_apply]
      apply congrArg Measure.dirac
      have h := frestrictLe_iterateInduction initial f
      exact congrArg (Preorder.frestrictLe₂ (Nat.zero_le a)) h.symm
  | succ b ih =>
      by_cases hba : b + 1 ≤ a
      · rw [Kernel.partialTraj_le hba, Kernel.deterministic_apply]
        apply congrArg Measure.dirac
        have h := frestrictLe_iterateInduction initial f
        exact congrArg (Preorder.frestrictLe₂ hba) h.symm
      · rw [Kernel.partialTraj_succ_of_le (by omega),
          Kernel.map_apply _ measurable_IicProdIoc,
          Kernel.comp_apply, ih, Measure.dirac_bind (Kernel.measurable _),
          Kernel.prod_apply, Kernel.id_apply]
        simp only [deterministicTransition,
          Kernel.map_apply _ (MeasurableEquiv.piSingleton b).measurable,
          Kernel.deterministic_apply, Measure.map_dirac' (MeasurableEquiv.piSingleton b).measurable,
          Measure.dirac_prod_dirac]
        rw [Measure.map_dirac' measurable_IicProdIoc]
        apply congrArg Measure.dirac
        funext ⟨i, hiic⟩
        simp only [history, IicProdIoc_def, Preorder.frestrictLe_apply]
        split_ifs with hi
        · rfl
        · have hi' : i = b + 1 := by
            have := Finset.mem_Iic.mp hiic
            omega
          subst hi'
          simp only [MeasurableEquiv.piSingleton, MeasurableEquiv.coe_mk]
          rw [iterateInduction, dif_neg hba]
          rfl

/-- [Measurable history updates](hyp:hf) started at one point generate
[a path law concentrated on the deterministic iterate sequence](goal).

The proof identifies finite-history marginals and uses uniqueness of the projective limit,
so no standard Borel assumption is needed.
-/
theorem pathLaw_deterministic (x : X 0) (f : (t : ℕ) → History X t → X (t + 1))
    (hf : ∀ t, Measurable (f t)) :
    pathLaw (Measure.dirac x) (deterministicTransition f hf) =
      Measure.dirac (deterministicPath x f) := by
  rw [pathLaw, Kernel.trajMeasure]
  change (Kernel.traj (deterministicTransition f hf) 0) ∘ₘ
    ((Measure.dirac x).map (initialHistory (X := X))) = _
  rw [Measure.map_dirac' measurable_initialHistory]
  rw [Measure.dirac_bind (Kernel.measurable _)]
  change Kernel.trajFun (deterministicTransition f hf) 0 (initialHistory x) =
    Measure.dirac (deterministicPath x f)
  refine (Kernel.isProjectiveLimit_trajFun _ _ _).unique ?_
  apply (isProjectiveLimit_nat_iff
    (Kernel.isProjectiveMeasureFamily_partialTraj (deterministicTransition f hf)
      (initialHistory x)) _).2
  intro n
  rw [inducedFamily_Iic, partialTraj_deterministic,
    Measure.map_dirac' (Preorder.measurable_frestrictLe n)]
  rfl

/-- With measurable singletons, [measurable deterministic updates](hyp:hf) give
[the deterministic iterate sequence almost surely](goal). -/
theorem ae_eq_deterministicPath [∀ t, MeasurableSingletonClass (X t)]
    (x : X 0) (f : (t : ℕ) → History X t → X (t + 1)) (hf : ∀ t, Measurable (f t)) :
    ∀ᵐ ω ∂pathLaw (Measure.dirac x) (deterministicTransition f hf),
      ω = deterministicPath x f := by
  rw [pathLaw_deterministic x f hf]
  simp

end Toolkit.Foundations.Probability.Processes
