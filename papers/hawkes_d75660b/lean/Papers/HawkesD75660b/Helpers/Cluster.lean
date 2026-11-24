module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Dirac
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Process.Predictable
public import Papers.HawkesD75660b.Basic

/-! Finite actual epoch configurations and the predictable left intensity. -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

namespace Papers.HawkesD75660b

/-- An [epoch configuration](goal) consists of a positive finite number of nonnegative
event times, strictly increasing and starting with the root at time zero.
@realizes \tau_i(finite nonnegative epoch vector, root zero, strictly increasing)
@realizes N(positive number n+1 of actual epochs, with no further actual points) -/
abbrev EpochConfiguration :=
  (n : ℕ) × {e : Fin (n + 1) → ℝ≥0 // e 0 = 0 ∧ StrictMono e}

-- @env: S1
variable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (C : Ω → EpochConfiguration)

/-- For [a configuration assignment to outcomes](hyp:C) and [an outcome](hyp:ω),
the [cluster epochs](goal) are the nonnegative event times in that outcome's configuration.
@realizes \tau_i(nonnegative actual epoch, indexed only by Fin (n+1)) -/
def clusterEpoch (ω : Ω) : Fin ((C ω).1 + 1) → ℝ≥0 := (C ω).2.val

open Classical in
/-- For [a configuration assignment](hyp:C), [observation time](hyp:t), and
[outcome](hyp:ω), the [cluster count](goal) is the number of event times at or before
the observation time, including the root at zero.
@realizes N_t(Nat cardinality of the actual epochs at or before t)
@realizes t(nonnegative observation time) -/
def clusterCountingProcess (t : ℝ≥0) (ω : Ω) : ℕ :=
  (Finset.univ.filter (fun i => clusterEpoch C ω i ≤ t)).card

/-- For [a configuration assignment](hyp:C) and [an outcome](hyp:ω), the
[cluster point measure](goal) places one unit of mass at each event time, including the root. -/
def clusterPointMeasure (ω : Ω) : Measure ℝ≥0 :=
  ∑ i, Measure.dirac (clusterEpoch C ω i)

open Classical in
-- @node: def:intensitydefeq
/-- For [a configuration assignment](hyp:C), [a nonnegative excitation kernel](hyp:g),
[an observation time](hyp:t), and [an outcome](hyp:ω), the [post-jump cluster intensity](goal)
is the sum of the kernel evaluated at elapsed times since all events at or before that time.
@realizes \lambda_t(nonnegative finite sum of the kernel at elapsed times)
@realizes g(nonnegative kernel on nonnegative time)
@realizes t(nonnegative time argument) -/
def clusterIntensity (g : ℝ≥0 → ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  ∑ i, if clusterEpoch C ω i ≤ t then g (t - clusterEpoch C ω i) else 0

open Classical in
/-- For [a configuration assignment](hyp:C), [a nonnegative excitation kernel](hyp:g),
[an observation time](hyp:t), and [an outcome](hyp:ω), the [left cluster intensity](goal)
sums the kernel at elapsed times since events strictly before the observation time. -/
def clusterLeftIntensity (g : ℝ≥0 → ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  ∑ i, if clusterEpoch C ω i < t then g (t - clusterEpoch C ω i) else 0

-- @node: def:cluster-size
/-- For [a configuration assignment](hyp:C) and [an outcome](hyp:ω), the
[cluster size](goal) is the total number of events, including the root.
@realizes N(positive Nat count of exactly all actual epochs) -/
def clusterSize (ω : Ω) : ℕ := (C ω).1 + 1

-- @node: def:cluster-duration
/-- For [a configuration assignment](hyp:C) and [an outcome](hyp:ω), the
[cluster duration](goal) is the last event time.
@realizes \tau(nonnegative last epoch at index N-1) -/
def clusterDuration (ω : Ω) : ℝ≥0 := clusterEpoch C ω (Fin.last (C ω).1)

-- @node: clusterCountingProcess_eventually
/-- For a finite cluster at any outcome, [the count equals the total cluster size
at every sufficiently late observation time](goal). -/
lemma clusterCountingProcess_eventually (ω : Ω) :
    ∀ᶠ t in Filter.atTop, clusterCountingProcess C t ω = clusterSize C ω := by
  classical
  filter_upwards [Filter.eventually_ge_atTop (clusterDuration C ω)] with t ht
  have hall : ∀ i, clusterEpoch C ω i ≤ t := by
    intro i
    exact le_trans ((C ω).2.property.2.monotone (Fin.le_last i)) ht
  simp [clusterCountingProcess, hall, clusterSize]

-- @node: clusterCountingProcess_tendsto
/-- For a finite cluster at any outcome, [the count converges to the total cluster size
as observation time tends to infinity](goal). -/
lemma clusterCountingProcess_tendsto (ω : Ω) :
    Filter.Tendsto (fun t => clusterCountingProcess C t ω) Filter.atTop
      (nhds (clusterSize C ω)) := by
  exact Filter.Tendsto.congr' (Filter.EventuallyEq.symm (clusterCountingProcess_eventually C ω))
    tendsto_const_nhds

-- @node: clusterCountingProcess_zero
/-- For every outcome, [the cluster count at time zero is one](goal), counting only the root. -/
lemma clusterCountingProcess_zero (ω : Ω) : clusterCountingProcess C 0 ω = 1 := by
  classical
  have hroot : clusterEpoch C ω 0 = 0 := (C ω).2.property.1
  have hzero : ∀ i, clusterEpoch C ω i ≤ 0 ↔ i = 0 := by
    intro i
    constructor
    · intro hi
      apply (C ω).2.property.2.injective
      exact le_antisymm (hi.trans hroot.ge) (hroot.le.trans zero_le)
    · rintro rfl
      exact hroot.le
  have hf : Finset.univ.filter (fun i => clusterEpoch C ω i ≤ 0) = {0} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact hzero i
  simp only [clusterCountingProcess, hf, Finset.card_singleton]

-- @node: clusterDuration_size_one
/-- If [the cluster has exactly one event](hyp:h), [its duration is zero](goal). -/
lemma clusterDuration_size_one (ω : Ω) (h : clusterSize C ω = 1) :
    clusterDuration C ω = 0 := by
  have hn : (C ω).1 = 0 := by
    change (C ω).1 + 1 = 1 at h
    omega
  have hi : Fin.last (C ω).1 = (0 : Fin ((C ω).1 + 1)) := by
    apply Fin.ext
    simpa using hn
  unfold clusterDuration
  rw [hi]
  exact (C ω).2.property.1

-- @node: clusterIntensity_pointMeasure
/-- For [a nonnegative excitation kernel g](hyp:g), if [g is measurable](hyp:hg), then at [any nonnegative time t](hyp:t) and
outcome [the post-jump cluster intensity equals the integral of the kernel at elapsed
times against the cluster point measure over the closed interval from zero to that time](goal). -/
lemma clusterIntensity_pointMeasure (g : ℝ≥0 → ℝ≥0) (hg : Measurable g)
    (t : ℝ≥0) (ω : Ω) :
    (clusterIntensity C g t ω : ℝ≥0∞) =
      ∫⁻ u in Set.Icc 0 t, (g (t - u) : ℝ≥0∞) ∂clusterPointMeasure C ω := by
  classical
  rw [clusterPointMeasure, ← Measure.restrictₗ_apply, map_sum]
  simp only [lintegral_finsetSum_measure, Measure.restrictₗ_apply, setLIntegral_dirac]
  simp only [clusterIntensity, ENNReal.coe_finset_sum, Set.mem_Icc, zero_le, true_and]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> simp

-- @node: measurable_epochConfiguration_elim
/-- If [a function of epoch configurations is measurable for each fixed number of events](hyp:hf),
then [it is measurable on the full space of finite epoch configurations](goal). -/
@[fun_prop] lemma measurable_epochConfiguration_elim {β : Type*} [MeasurableSpace β]
    (f : EpochConfiguration → β)
    (hf : ∀ n, Measurable (fun e => f ⟨n, e⟩)) : Measurable f := by
  intro s hs
  exact MeasurableSpace.measurableSet_iInf.mpr (fun n => hf n hs)

-- @node: measurable_clusterCountingProcess
/-- If [the configuration assignment is measurable](hyp:hC), then for [any fixed nonnegative observation time t](hyp:t), [the cluster count
at t is a measurable function of the outcome](goal). -/
@[fun_prop] lemma measurable_clusterCountingProcess (hC : Measurable C) (t : ℝ≥0) :
    Measurable (clusterCountingProcess C t) := by
  classical
  have hf : Measurable (fun c : EpochConfiguration => clusterCountingProcess id t c) := by
    apply measurable_epochConfiguration_elim
    intro n
    simp_rw [clusterCountingProcess, Finset.card_eq_sum_ones, Finset.sum_filter]
    change Measurable (fun e : {e : Fin (n + 1) → ℝ≥0 // e 0 = 0 ∧ StrictMono e} =>
      ∑ i : Fin (n + 1),
      if e.val i ≤ t then (1 : ℕ) else 0)
    apply Finset.measurable_sum
    intro i hi
    apply Measurable.ite
    · exact measurableSet_le ((measurable_pi_apply i).comp measurable_subtype_coe)
        measurable_const
    · exact measurable_const
    · exact measurable_const
  exact hf.comp hC

-- @node: measurable_clusterDuration
/-- If [the configuration assignment is measurable](hyp:hC), then [the cluster duration
is a measurable function of the outcome](goal). -/
@[fun_prop] lemma measurable_clusterDuration (hC : Measurable C) :
    Measurable (clusterDuration C) := by
  have hf : Measurable (fun c : EpochConfiguration => clusterDuration id c) := by
    apply measurable_epochConfiguration_elim
    intro n
    simp only [clusterDuration, clusterEpoch, id_eq]
    exact (measurable_pi_apply (Fin.last n)).comp measurable_subtype_coe
  exact hf.comp hC

/-- For [a configuration assignment](hyp:C) with [measurability](hyp:hC), the
[cluster natural filtration](goal) records the information generated by the root-inclusive
counting process up to each time. -/
def clusterNaturalFiltration (hC : Measurable C) : Filtration ℝ≥0 ‹MeasurableSpace Ω› :=
  Filtration.natural (clusterCountingProcess C)
    (fun t => (measurable_clusterCountingProcess C hC t).stronglyMeasurable)

/-- For [a configuration assignment](hyp:C), [a Markovian kernel parameter](hyp:ρ),
[an observation time](hyp:t), and [an outcome](hyp:ω), the [compensated cluster count](goal)
is the count excluding the root minus the integral of the left cluster intensity from zero
to the observation time. -/
def compensatedClusterCount (ρ : ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℝ :=
  (clusterCountingProcess C t ω : ℝ) - 1 -
    ∫ u in (0 : ℝ)..(t : ℝ),
      (clusterLeftIntensity C (markovianKernel ρ) (Real.toNNReal u) ω : ℝ)

/-- For [a probability measure on outcomes](hyp:P), [a configuration assignment](hyp:C),
and [a Borel size-law parameter](hyp:ρ), the [Hawkes cluster sampling assumptions](goal)
require [the configuration assignment to be measurable](step:1) and
[the cluster size to have the Borel law with that parameter under the probability measure](step:2).

The intensity interpretation is kept separately in the explicit pin-4 atom. -/
def hawkesClusterWorld (ρ : ℝ≥0) : Prop :=
  Measurable C ∧
  HasLaw (clusterSize C) (borelMeasure ρ) P -- @realizes N(Borel size law on the observed space)

open Classical in
-- @node: ass:pin-4
/-- For [a probability measure on outcomes](hyp:P), [a configuration assignment](hyp:C),
and [a Markovian kernel parameter](hyp:ρ), the [cluster counting convention](goal) requires
[the count to include exactly the events at or before each observation time](step:1),
[the post-jump intensity to equal the elapsed-time kernel integral against the point measure](step:2),
[the post-jump intensity to be right-continuous](step:3),
[its limit from the left at each positive time to equal the left cluster intensity](step:4),
and [a measurable configuration assignment for which the left intensity is strongly predictable
and the compensated count is integrable at every time and is a martingale in the natural
counting filtration under the probability measure](step:5).

The compensator excludes the deterministic root at zero. -/
def clusterCountingConvention (ρ : ℝ≥0) : Prop :=
  (∀ t ω, clusterCountingProcess C t ω =
    (Finset.univ.filter (fun i => clusterEpoch C ω i ≤ t)).card) ∧ -- @realizes N_t(count)
  (∀ t ω, (clusterIntensity C (markovianKernel ρ) t ω : ℝ≥0∞) =
    ∫⁻ u in Set.Icc 0 t, (markovianKernel ρ (t - u) : ℝ≥0∞)
      ∂clusterPointMeasure C ω) ∧ -- @realizes u(point-measure integration on [0,t])
  (∀ ω t, ContinuousWithinAt (fun s => clusterIntensity C (markovianKernel ρ) s ω)
    (Set.Ici t) t) ∧ -- @realizes \lambda_t(right-continuous post-jump version)
  (∀ ω t, 0 < t → Filter.Tendsto (fun s => clusterIntensity C (markovianKernel ρ) s ω)
    (nhdsWithin t (Set.Iio t)) (nhds (clusterLeftIntensity C (markovianKernel ρ) t ω))) ∧
  (∃ hC : Measurable C,
    IsStronglyPredictable (clusterNaturalFiltration C hC)
      (clusterLeftIntensity C (markovianKernel ρ)) ∧
    (∀ t, Integrable (compensatedClusterCount C ρ t) P) ∧
    Martingale (compensatedClusterCount C ρ) (clusterNaturalFiltration C hC) P)

end Papers.HawkesD75660b
