module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Countable.Basic
public import Mathlib.Data.Countable.Defs
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.SetLike.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.MeasurableSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Trim
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Order.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompletePartialOrder.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.Nat
public import Mathlib.Order.Notation
public import Mathlib.Order.RelClasses
public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real
public import Toolkit.Foundations.Probability.PoissonEquation

/-!
# Conditional moments of finite-state Markov transitions

Conditional expectations of a finite-state process given its observed past,
when its finite-dimensional path probabilities factor into an initial mass and
successive transition-matrix entries. All state observations are measurable for
the full sigma algebra on the finite state space, and conditional expectation is
taken with respect to the sigma algebra generated by the observations up to and
including the current time.

* `observedInformation` is that sigma algebra; `observedInformation_mono` and
  `observedInformation_le` make it a filtration.
* `integral_finite_score` and `condExp_finite_joint` compute an integral and a
  conditional expectation of a finite-valued score from state probabilities.
* `condExp_next_pair_score` and `condExp_next_score` are the Markov property: the
  conditional mean of a score of the next state is its transition-weighted average.
* `transitionInnovation` is the martingale difference of a state function;
  `condExp_transitionInnovation` gives its conditional mean and second moment, and
  `sum_score_eq_innovations_add_boundary` is the Poisson-equation decomposition of
  a reward sum into innovations plus a boundary term.
* `memLp_finiteState_score`: a score of a finite-state observation is bounded.

Reference: Meyn and Tweedie, Markov Chains and Stochastic Stability, Section 17.4
(the martingale decomposition of an additive functional).
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Toolkit.Foundations.Probability.Conditioning

/-- For [a sequence of state observations](hyp:U) and [a time index](hyp:n),
[the observed information](goal) is [the sigma algebra generated by the first
n plus one state observations](step:1). -/
@[instance_reducible]
noncomputable def observedInformation {T Ω : Type*}
    (U : ℕ → Ω → T) (n : ℕ) : MeasurableSpace Ω :=
  ⨆ k : Fin (n + 1), MeasurableSpace.comap (U k) ⊤

/-- For [a finite transition matrix](hyp:R), [a state-observation process](hyp:U),
[a real state function](hyp:g), [a time](hyp:k), and [an outcome](hyp:ω),
[the transition innovation](goal) is [the next function value minus its
transition average at the current state](step:1). -/
noncomputable def transitionInnovation {T Ω : Type*} [Fintype T]
    (R : Matrix T T ℝ) (U : ℕ → Ω → T) (g : T → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  g (U (k + 1) ω) - R.mulVec g (U k ω)

/-- If [every observation of a state process is measurable](hyp:hU), then
[its observed information at every time is contained in the ambient sigma algebra](goal). -/
theorem observedInformation_le {T Ω : Type*} [mΩ : MeasurableSpace Ω]
    {U : ℕ → Ω → T} (hU : ∀ k, @Measurable Ω T mΩ ⊤ (U k)) (n : ℕ) :
    observedInformation U n ≤ mΩ := by
  exact iSup_le fun k => (hU k).comap_le

/-- For [a sequence of observations](hyp:U), [the information obtained by observing
through time n grows as n increases](goal). -/
theorem observedInformation_mono {T Ω : Type*} (U : ℕ → Ω → T) :
    Monotone (observedInformation U) := by
  intro n m hnm
  refine iSup_le fun i => ?_
  exact le_iSup_of_le (⟨i.val, by omega⟩ : Fin (m + 1)) le_rfl

/-- If [the observations are measurable on a finite state space](hyp:hU), then
[every real score of a single observation has finite Lp seminorm at every exponent,
including infinity](goal). -/
theorem memLp_finiteState_score {T Ω : Type*} [Finite T] [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {U : ℕ → Ω → T}
    (hU : ∀ k, @Measurable Ω T mΩ ⊤ (U k)) (g : T → ℝ) (n : ℕ)
    (p : ENNReal) : MemLp (fun ω => g (U n ω)) p μ := by
  -- A finite-range measurable real function is uniformly bounded, including in L∞.
  classical
  let := Fintype.ofFinite T
  have hg : @Measurable T ℝ ⊤ _ g := fun _ _ => trivial
  apply MemLp.of_bound (hg.comp (hU n)).aestronglyMeasurable (∑ x : T, ‖g x‖)
  exact Filter.Eventually.of_forall fun ω =>
    Finset.single_le_sum (fun x _ => norm_nonneg (g x)) (Finset.mem_univ (U n ω))

/-- If [a finite-valued random variable is measurable](hyp:hX), then
[the integral of any real score equals the sum of its values weighted by the
probabilities of the corresponding states](goal). -/
theorem integral_finite_score {A Ω : Type*} [Fintype A] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {X : Ω → A}
    (hX : @Measurable Ω A _ ⊤ X) (v : A → ℝ) :
    (∫ ω, v (X ω) ∂μ) = ∑ a, μ.real {ω | X ω = a} * v a := by
  classical
  have hs (a : A) : MeasurableSet {ω | X ω = a} := hX (t := {a}) trivial
  have hi (a : A) : Integrable ({ω | X ω = a}.indicator (fun _ => v a)) μ :=
    (integrable_const _).indicator (hs a)
  have he (ω : Ω) : v (X ω) =
      ∑ a : A, {ω | X ω = a}.indicator (fun _ => v a) ω := by
    simp [Set.indicator_apply]
  calc
    _ = ∫ ω, ∑ a : A, {ω | X ω = a}.indicator (fun _ => v a) ω ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall he)
    _ = _ := by
      rw [integral_finsetSum Finset.univ (fun a _ => hi a)]
      simp_rw [integral_indicator (hs _), setIntegral_const, smul_eq_mul]

/-- For [two measurable finite-valued random variables](hyp:hX,hY), if
[their joint state probabilities equal the first variable's state probabilities
times the transition weights](hyp:hw), then [the conditional mean of any score
of the pair, given the first variable, equals its transition-weighted average](goal). -/
theorem condExp_finite_joint {A B Ω : Type*} [Fintype A] [Fintype B]
    [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → A} {Y : Ω → B}
    (hX : @Measurable Ω A mΩ ⊤ X) (hY : @Measurable Ω B mΩ ⊤ Y)
    (w : A → B → ℝ)
    (hw : ∀ a b, μ.real {ω | X ω = a ∧ Y ω = b} =
      μ.real {ω | X ω = a} * w a b) (q : A → B → ℝ) :
    μ[fun ω => q (X ω) (Y ω) | MeasurableSpace.comap X ⊤] =ᵐ[μ]
      fun ω => ∑ b, w (X ω) b * q (X ω) b := by
  classical
  let Z : Ω → A × B := fun ω => (X ω, Y ω)
  have hZ : @Measurable Ω (A × B) mΩ ⊤ Z := by
    intro s _
    have he : Z ⁻¹' s = ⋃ a : A, ⋃ b : B,
        {ω | (a, b) ∈ s ∧ X ω = a ∧ Y ω = b} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq]
      constructor
      · intro h
        exact ⟨X ω, Y ω, h, rfl, rfl⟩
      · rintro ⟨a, b, h, ha, hb⟩
        simpa [Z, ha, hb] using h
    rw [he]
    exact MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b => by
      by_cases h : (a, b) ∈ s
      · simpa [h, Set.preimage, Set.inter_def] using
          (hX (t := {a}) trivial).inter (hY (t := {b}) trivial)
      · simp only [h, false_and, Set.ofPred_false]
        exact MeasurableSet.empty
  have hm := hX.comap_le
  have hg : @Measurable Ω ℝ (MeasurableSpace.comap X ⊤) _
      (fun ω => ∑ b, w (X ω) b * q (X ω) b) :=
    (show @Measurable A ℝ ⊤ _ (fun a : A => ∑ b, w a b * q a b)
      from fun _ _ => trivial).comp (Measurable.of_comap_le le_rfl)
  apply (ae_eq_condExp_of_forall_setIntegral_eq hm
    (f := fun ω => q (X ω) (Y ω))
    (g := fun ω => ∑ b, w (X ω) b * q (X ω) b)
    ((memLp_finiteState_score μ (U := fun _ => Z) (fun _ => hZ)
      (fun z : A × B => q z.1 z.2) 0 1).integrable (by simp))
    (fun s _ _ => ((memLp_finiteState_score μ (U := fun _ => X) (fun _ => hX)
      (fun a : A => ∑ b, w a b * q a b) 0 1).integrable (by simp)).integrableOn)
    ?_ hg.aestronglyMeasurable).symm
  intro s hs _
  obtain ⟨t, _, rfl⟩ := hs
  rw [← integral_indicator (hX (t := t) trivial), ← integral_indicator (hX (t := t) trivial)]
  have he₁ : (X ⁻¹' t).indicator (fun ω => ∑ b, w (X ω) b * q (X ω) b) =
      fun ω => if X ω ∈ t then ∑ b, w (X ω) b * q (X ω) b else 0 := by
    rfl
  have he₂ : (X ⁻¹' t).indicator (fun ω => q (X ω) (Y ω)) =
      fun ω => if (Z ω).1 ∈ t then q (Z ω).1 (Z ω).2 else 0 := by
    rfl
  rw [he₁, he₂,
    integral_finite_score μ hX (fun a => if a ∈ t then ∑ b, w a b * q a b else 0),
    integral_finite_score μ hZ (fun z : A × B => if z.1 ∈ t then q z.1 z.2 else 0),
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ t
  · simp only [ha, if_pos]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    have he : {ω | Z ω = (a, b)} = {ω | X ω = a ∧ Y ω = b} := by
      ext ω
      simp [Z, Prod.mk.injEq]
    rw [he, hw]
    ring
  · simp [ha]

/-- For [measurable finite-state observations](hyp:hU) whose
[path probabilities factor into initial masses and successive transition entries](hyp:hpaths),
[the conditional mean of any score of two consecutive states, given the observed
past, equals its transition-weighted average from the current state](goal). -/
theorem condExp_next_pair_score {T Ω : Type*} [Fintype T]
    [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {R : Matrix T T ℝ} {nu : T → ℝ} {U : ℕ → Ω → T}
    (hU : ∀ k, @Measurable Ω T mΩ ⊤ (U k))
    (hpaths : ∀ (n : ℕ) (x : Fin (n + 1) → T),
      μ.real {ω | ∀ i : Fin (n + 1), U i ω = x i} =
        nu (x 0) * ∏ i : Fin n, R (x i.castSucc) (x i.succ))
    (q : T → T → ℝ) (k : ℕ) :
    μ[fun ω => q (U k ω) (U (k + 1) ω) | observedInformation U k] =ᵐ[μ]
      fun ω => ∑ y, R (U k ω) y * q (U k ω) y := by
  classical
  let : MeasurableSpace T := ⊤
  let H : Ω → (Fin (k + 1) → T) := fun ω i => U i ω
  have htop : (inferInstance : MeasurableSpace (Fin (k + 1) → T)) = ⊤ := by
    ext s
    exact iff_of_true (MeasurableSet.of_discrete) trivial
  have hH : @Measurable Ω (Fin (k + 1) → T) mΩ ⊤ H := by
    rw [← htop]
    exact measurable_pi_iff.mpr fun i => hU i
  have hG : observedInformation U k = MeasurableSpace.comap H ⊤ := by
    rw [← htop, MeasurableSpace.comap_process_pi]
    rfl
  have hw (x : Fin (k + 1) → T) (y : T) :
      μ.real {ω | H ω = x ∧ U (k + 1) ω = y} =
        μ.real {ω | H ω = x} * R (x (Fin.last k)) y := by
    let z : Fin (k + 2) → T := Fin.snoc x y
    have he : {ω | H ω = x ∧ U (k + 1) ω = y} =
        {ω | ∀ i : Fin (k + 2), U i ω = z i} := by
      ext ω
      constructor
      · rintro ⟨hx, hy⟩ i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa [z] using hy
        · simpa [z] using congrFun hx j
      · intro hz
        constructor
        · funext i
          simpa [H, z] using hz i.castSucc
        · simpa [z] using hz (Fin.last (k + 1))
    have hex : {ω | H ω = x} = {ω | ∀ i : Fin (k + 1), U i ω = x i} := by
      ext ω
      exact funext_iff
    rw [he, hex, hpaths, hpaths, Fin.prod_univ_castSucc]
    have hcast (i : Fin k) : i.castSucc.succ = i.succ.castSucc := rfl
    simp only [z, Fin.snoc_castSucc, hcast]
    -- The final transition starts at the last coordinate of the old history.
    simp [Fin.snoc, mul_assoc]
  rw [hG]
  exact condExp_finite_joint μ hH (hU (k + 1))
    (fun x y => R (x (Fin.last k)) y) hw (fun x y => q (x (Fin.last k)) y)

/-- For [measurable finite-state observations](hyp:hU) whose [finite-dimensional
probabilities factor into initial masses and successive transition entries](hyp:hpaths),
[the conditional mean of any next-state score given the observed past equals the
transition-weighted score at the current state](goal). -/
theorem condExp_next_score {T Ω : Type*} [Fintype T]
    [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {R : Matrix T T ℝ} {nu : T → ℝ} {U : ℕ → Ω → T}
    (hU : ∀ k, @Measurable Ω T mΩ ⊤ (U k))
    (hpaths : ∀ (n : ℕ) (x : Fin (n + 1) → T),
      μ.real {ω | ∀ i : Fin (n + 1), U i ω = x i} =
        nu (x 0) * ∏ i : Fin n, R (x i.castSucc) (x i.succ))
    (g : T → ℝ) (k : ℕ) :
    μ[fun ω => g (U (k + 1) ω) | observedInformation U k] =ᵐ[μ]
      fun ω => R.mulVec g (U k ω) := by
  -- Partition Ω by the finite history (U₀,...,U_k). On each atom, append a
  -- last state and use hpaths. Work with unnormalized integrals, so atoms of
  -- probability zero require no division or strict positivity assumption.
  simpa only [Matrix.mulVec, dotProduct] using
    condExp_next_pair_score μ hU hpaths (fun _ y => g y) k

/-- Under [measurability of finite-state observations](hyp:hU) and [the Markov
cylinder-probability formula](hyp:hpaths), [every transition innovation has
conditional mean zero and conditional second moment equal to the current state's
innovation variance](goal). -/
theorem condExp_transitionInnovation {T Ω : Type*} [Fintype T]
    [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {R : Matrix T T ℝ} {nu : T → ℝ} {U : ℕ → Ω → T}
    (hU : ∀ k, @Measurable Ω T mΩ ⊤ (U k))
    (hpaths : ∀ (n : ℕ) (x : Fin (n + 1) → T),
      μ.real {ω | ∀ i : Fin (n + 1), U i ω = x i} =
        nu (x 0) * ∏ i : Fin n, R (x i.castSucc) (x i.succ))
    (g : T → ℝ) (k : ℕ) :
    (μ[transitionInnovation R U g k | observedInformation U k] =ᵐ[μ] 0) ∧
    (μ[fun ω => (transitionInnovation R U g k ω) ^ 2 | observedInformation U k] =ᵐ[μ]
      fun ω => innovationVariance R g (U k ω)) := by
  -- Use condExp_next_score for g and g² and pull out current-state factors.
  -- Alternatively apply it to each finite current-state indicator times the
  -- next-state squared innovation. hpaths implies normalization on visited states.
  have hm := observedInformation_le hU k
  have hc : @Measurable Ω T (observedInformation U k) ⊤ (U k) :=
    Measurable.of_comap_le (le_iSup
      (fun i : Fin (k + 1) => MeasurableSpace.comap (U i) ⊤) (Fin.last k))
  have hg : @Measurable T ℝ ⊤ _ (R.mulVec g) := fun _ _ => trivial
  have hi : Integrable (fun ω => g (U (k + 1) ω)) μ :=
    (memLp_finiteState_score μ hU g (k + 1) 1).integrable (by simp)
  have hj : Integrable (fun ω => R.mulVec g (U k ω)) μ :=
    (memLp_finiteState_score μ hU (R.mulVec g) k 1).integrable (by simp)
  have hjc := condExp_of_stronglyMeasurable hm (hg.comp hc).stronglyMeasurable hj
  simp only [Function.comp_def] at hjc
  constructor
  · change μ[(fun ω => g (U (k + 1) ω)) - (fun ω => R.mulVec g (U k ω)) |
        observedInformation U k] =ᵐ[μ] 0
    refine (condExp_sub hi hj _).trans ?_
    rw [hjc]
    filter_upwards [condExp_next_score μ hU hpaths g k] with ω hω
    simp [Pi.sub_apply, hω]
  · simpa only [transitionInnovation, innovationVariance] using
      condExp_next_pair_score μ hU hpaths (fun x y => (g y - R.mulVec g x) ^ 2) k

/-- If [a reward equals its Poisson potential minus the potential's transition
average](hyp:hpoisson), then [its first n observations sum to the sum of the first
n transition innovations plus the initial potential minus the terminal potential](goal). -/
theorem sum_score_eq_innovations_add_boundary {T Ω : Type*} [Fintype T]
    (R : Matrix T T ℝ) (U : ℕ → Ω → T) (f g : T → ℝ)
    (hpoisson : ∀ x, g x - R.mulVec g x = f x) (n : ℕ) (ω : Ω) :
    (∑ k ∈ Finset.range n, f (U k ω)) =
      (∑ k ∈ Finset.range n, transitionInnovation R U g k ω) + g (U 0 ω) - g (U n ω) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, ← hpoisson]
    simp only [transitionInnovation]
    ring

end Toolkit.Foundations.Probability.Conditioning
