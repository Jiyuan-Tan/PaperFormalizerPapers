module

public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.FunLike.Equiv
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Unique
public import Mathlib.MeasureTheory.Constructions.Projective
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.MeasurableSpace.Basic
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
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Lattice
public import Mathlib.Order.Nat
public import Mathlib.Order.RelClasses
public import Mathlib.Order.Restriction
public import Mathlib.Probability.Kernel.Basic
public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.Probability.Kernel.Composition.CompMap
public import Mathlib.Probability.Kernel.Composition.CompNotation
public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.Defs
public import Mathlib.Probability.Kernel.IonescuTulcea.Maps
public import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import Mathlib.Probability.Kernel.MeasurableLIntegral
public import Toolkit.Foundations.Probability.Processes.PathLaw

/-!
# Coordinate projections of history-dependent processes

A measurable state projection `φ t : X t → Y t` may discard information at each time (for
example recorded noise). When the projected next-state law depends only on the projected
history, the projected finite trajectories and the projected path law are those of the target
process (`map_partialTraj_projectHistory`, `map_pathLaw_projectPath`). No standard Borel
hypothesis is required.
-/

@[expose] public section

namespace Toolkit.Foundations.Probability.Processes

open MeasureTheory ProbabilityTheory

variable {X Y : ℕ → Type*} [∀ t, MeasurableSpace (X t)] [∀ t, MeasurableSpace (Y t)]

/-- The [projected history](goal) applies [the time-specific state projections](hyp:φ) to
[a history](hyp:h) through [the chosen time](hyp:t) in
[the original and projected state spaces](hyp:X,Y). -/
def projectHistory (φ : (t : ℕ) → X t → Y t) (t : ℕ) (h : History X t) : History Y t :=
  fun i => φ i (h i)

/-- The [projected path](goal) applies [the time-specific state projections](hyp:φ) to
[a path](hyp:ω) in [the original and projected state spaces](hyp:X,Y). -/
def projectPath (φ : (t : ℕ) → X t → Y t) (ω : Path X) : Path Y := fun t => φ t (ω t)

/-- [Measurable state projections](hyp:hφ) give [a measurable history projection](goal). -/
theorem measurable_projectHistory (φ : (t : ℕ) → X t → Y t)
    (hφ : ∀ t, Measurable (φ t)) (t : ℕ) : Measurable (projectHistory φ t) := by
  exact measurable_pi_lambda _ (fun i => (hφ i).comp (measurable_pi_apply i))

/-- [Measurable state projections](hyp:hφ) give [a measurable path projection](goal). -/
theorem measurable_projectPath (φ : (t : ℕ) → X t → Y t)
    (hφ : ∀ t, Measurable (φ t)) : Measurable (projectPath φ) := by
  exact measurable_pi_lambda _ (fun t => (hφ t).comp (measurable_pi_apply t))

omit [∀ t, MeasurableSpace (X t)] [∀ t, MeasurableSpace (Y t)] in
/-- [Restricting a projected path gives the projected restriction of the original path](goal). -/
theorem history_projectPath (φ : (t : ℕ) → X t → Y t) (t : ℕ) (ω : Path X) :
    history Y t (projectPath φ ω) = projectHistory φ t (history X t ω) := rfl

/-- If [the state projections are measurable](hyp:hφ) and
[each projected next-state law agrees with the target transition on projected histories](hyp:hstep),
then, from [the given initial history](hyp:h),
[projecting any finite trajectory gives the target finite trajectory law](goal).

This finite statement is proved by induction on the terminal time and does not use
uniqueness of the infinite trajectory law.
-/
theorem map_partialTraj_projectHistory
    (κ : Transition X) [∀ t, IsMarkovKernel (κ t)]
    (η : Transition Y) [∀ t, IsMarkovKernel (η t)]
    (φ : (t : ℕ) → X t → Y t) (hφ : ∀ t, Measurable (φ t))
    (hstep : ∀ t h, (κ t h).map (φ (t + 1)) = η t (projectHistory φ t h))
    (a b : ℕ) (h : History X a) :
    (Kernel.partialTraj κ a b h).map (projectHistory φ b) =
      Kernel.partialTraj η a b (projectHistory φ a h) := by
  classical
  have hnext (n : ℕ) (g : History X n) :
      (Kernel.partialTraj κ n (n + 1) g).map (projectHistory φ (n + 1)) =
        Kernel.partialTraj η n (n + 1) (projectHistory φ n g) := by
    let FX : History X n × X (n + 1) → History X (n + 1) :=
      fun p => IicProdIoc n (n + 1) (p.1, MeasurableEquiv.piSingleton n p.2)
    let FY : History Y n × Y (n + 1) → History Y (n + 1) :=
      fun p => IicProdIoc n (n + 1) (p.1, MeasurableEquiv.piSingleton n p.2)
    have hFX : Measurable FX :=
      measurable_IicProdIoc.comp
        (measurable_fst.prodMk ((MeasurableEquiv.piSingleton n).measurable.comp measurable_snd))
    have hFY : Measurable FY :=
      measurable_IicProdIoc.comp
        (measurable_fst.prodMk ((MeasurableEquiv.piSingleton n).measurable.comp measurable_snd))
    have hcomm : projectHistory φ (n + 1) ∘ FX =
        FY ∘ Prod.map (projectHistory φ n) (φ (n + 1)) := by
      funext p ⟨i, hi⟩
      simp only [Function.comp_apply, FX, FY, projectHistory, IicProdIoc_def,
        MeasurableEquiv.piSingleton, MeasurableEquiv.coe_mk]
      split_ifs with hin
      · rfl
      · have heq : i = n + 1 := by
          have := Finset.mem_Iic.mp hi
          omega
        subst i
        rfl
    have hx : Kernel.partialTraj κ n (n + 1) g =
        ((Measure.dirac g).prod (κ n g)).map FX := by
      rw [Kernel.partialTraj_succ_self, Kernel.map_apply _ measurable_IicProdIoc,
        Kernel.prod_apply, Kernel.id_apply,
        Kernel.map_apply _ (MeasurableEquiv.piSingleton n).measurable]
      rw [← Measure.map_id (μ := Measure.dirac g),
        Measure.map_prod_map _ _ measurable_id (MeasurableEquiv.piSingleton n).measurable,
        Measure.map_map (by fun_prop) (by fun_prop), Measure.map_id]
      rfl
    have hy : Kernel.partialTraj η n (n + 1) (projectHistory φ n g) =
        ((Measure.dirac (projectHistory φ n g)).prod
          (η n (projectHistory φ n g))).map FY := by
      rw [Kernel.partialTraj_succ_self, Kernel.map_apply _ measurable_IicProdIoc,
        Kernel.prod_apply, Kernel.id_apply,
        Kernel.map_apply _ (MeasurableEquiv.piSingleton n).measurable]
      rw [← Measure.map_id (μ := Measure.dirac (projectHistory φ n g)),
        Measure.map_prod_map _ _ measurable_id (MeasurableEquiv.piSingleton n).measurable,
        Measure.map_map (by fun_prop) (by fun_prop), Measure.map_id]
      rfl
    rw [hx, hy, Measure.map_map (measurable_projectHistory φ hφ _) hFX, hcomm,
      ← Measure.map_map hFY ((measurable_projectHistory φ hφ n).prodMap (hφ (n + 1))),
      ← Measure.map_prod_map _ _ (measurable_projectHistory φ hφ n) (hφ (n + 1)),
      Measure.map_dirac' (measurable_projectHistory φ hφ n), hstep]
  induction b with
  | zero =>
      rw [Kernel.partialTraj_zero, Kernel.partialTraj_zero,
        Kernel.deterministic_apply, Kernel.deterministic_apply,
        Measure.map_dirac' (measurable_projectHistory φ hφ 0)]
      rfl
  | succ b ih =>
      by_cases hba : b + 1 ≤ a
      · rw [Kernel.partialTraj_le hba, Kernel.partialTraj_le hba,
          Kernel.deterministic_apply, Kernel.deterministic_apply,
          Measure.map_dirac' (measurable_projectHistory φ hφ (b + 1))]
        rfl
      · rw [Kernel.partialTraj_succ_eq_comp (κ := κ) (a := a) (b := b) (by omega),
          Kernel.partialTraj_succ_eq_comp (κ := η) (a := a) (b := b) (by omega),
          Kernel.comp_apply, Kernel.comp_apply,
          Measure.map_comp _ _ (measurable_projectHistory φ hφ (b + 1))]
        have hk : (Kernel.partialTraj κ b (b + 1)).map (projectHistory φ (b + 1)) =
            (Kernel.partialTraj η b (b + 1)).comap (projectHistory φ b)
              (measurable_projectHistory φ hφ b) := by
          ext g s hs
          rw [Kernel.map_apply _ (measurable_projectHistory φ hφ (b + 1)),
            Kernel.comap_apply, hnext]
        rw [hk]
        change ((Kernel.partialTraj η b (b + 1)).comap (projectHistory φ b)
          (measurable_projectHistory φ hφ b)) ∘ₘ (Kernel.partialTraj κ a b h) = _
        rw [← Measure.deterministic_comp_eq_map (measurable_projectHistory φ hφ b)] at ih
        rw [← Kernel.comp_deterministic_eq_comap, ← Measure.comp_assoc, ih]

/-- If [the state projections are measurable](hyp:hφ) and
[the one-step projected laws agree](hyp:hstep), then
[the projected path law is the target path law started at the projected initial law](goal).

This applies to recorded-noise algorithms and other state augmentations; it uses finite
marginals and projective-limit uniqueness, not regular conditional laws.
-/
theorem map_pathLaw_projectPath (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (κ : Transition X) [∀ t, IsMarkovKernel (κ t)]
    (η : Transition Y) [∀ t, IsMarkovKernel (η t)]
    (φ : (t : ℕ) → X t → Y t) (hφ : ∀ t, Measurable (φ t))
    (hstep : ∀ t h, (κ t h).map (φ (t + 1)) = η t (projectHistory φ t h)) :
    (pathLaw μ₀ κ).map (projectPath φ) = pathLaw (μ₀.map (φ 0)) η := by
  have htraj (a : ℕ) (h : History X a) :
      (Kernel.traj κ a h).map (projectPath φ) =
        Kernel.traj η a (projectHistory φ a h) := by
    symm
    refine (Kernel.isProjectiveLimit_trajFun η a (projectHistory φ a h)).unique ?_
    apply (isProjectiveLimit_nat_iff
      (Kernel.isProjectiveMeasureFamily_partialTraj η (projectHistory φ a h)) _).2
    intro n
    rw [inducedFamily_Iic,
      Measure.map_map (Preorder.measurable_frestrictLe n) (measurable_projectPath φ hφ)]
    change (Kernel.traj κ a h).map
      (projectHistory φ n ∘ Preorder.frestrictLe n) = _
    rw [← Measure.map_map (measurable_projectHistory φ hφ n)
      (Preorder.measurable_frestrictLe n),
      ← Kernel.map_apply _ (Preorder.measurable_frestrictLe n),
      Kernel.traj_map_frestrictLe, map_partialTraj_projectHistory κ η φ hφ hstep]
  have hk : (Kernel.traj κ 0).map (projectPath φ) =
      (Kernel.traj η 0).comap (projectHistory φ 0)
        (measurable_projectHistory φ hφ 0) := by
    ext h s hs
    rw [Kernel.map_apply _ (measurable_projectPath φ hφ), Kernel.comap_apply, htraj]
  have hinit : projectHistory φ 0 ∘ initialHistory (X := X) =
      initialHistory (X := Y) ∘ φ 0 := by
    funext x i
    have hi : i = (⟨0, by simp⟩ : Finset.Iic 0) :=
      Subtype.ext (Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.property))
    subst i
    rfl
  rw [pathLaw, pathLaw, Kernel.trajMeasure, Kernel.trajMeasure]
  change ((Kernel.traj κ 0) ∘ₘ (μ₀.map (initialHistory (X := X)))).map
    (projectPath φ) = (Kernel.traj η 0) ∘ₘ
      ((μ₀.map (φ 0)).map (initialHistory (X := Y)))
  rw [Measure.map_comp _ _ (measurable_projectPath φ hφ), hk,
    ← Kernel.comp_deterministic_eq_comap, ← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map (measurable_projectHistory φ hφ 0),
    Measure.map_map (measurable_projectHistory φ hφ 0) measurable_initialHistory,
    hinit, ← Measure.map_map measurable_initialHistory (hφ 0)]

end Toolkit.Foundations.Probability.Processes

namespace Toolkit.Foundations.Probability.Processes

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

-- @node: chain_map_compProd_transport
/-- For [a map from the original state space to the transported state space](hyp:f)
that [is measurable](hyp:hf), suppose [the original transition law agrees almost
everywhere with the transported transition law evaluated at the mapped state](hyp:hκ).
Then [mapping the first coordinate of the joint state-transition law equals
forming the joint law from the mapped state distribution and transported kernel](goal). -/
lemma map_prodMap_compProd_eq_compProd_map {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) [SFinite μ] (κ : Kernel A C) [IsSFiniteKernel κ]
    (η : Kernel B C) [IsSFiniteKernel η] (f : A → B) (hf : Measurable f)
    (hκ : ∀ᵐ a ∂μ, κ a = η (f a)) :
    (μ.compProd κ).map (Prod.map f id) = (μ.map f).compProd η := by
  ext s hs
  rw [Measure.map_apply (hf.prodMap measurable_id) hs,
    Measure.compProd_apply (hs.preimage (hf.prodMap measurable_id)),
    Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  apply lintegral_congr_ae
  filter_upwards [hκ] with a ha
  rw [ha]
  rfl

end

end Toolkit.Foundations.Probability.Processes
