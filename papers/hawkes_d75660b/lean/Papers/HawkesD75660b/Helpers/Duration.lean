module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Distributions.Exponential
public import Papers.HawkesD75660b.Helpers.GeneratingFunction
public import Papers.HawkesD75660b.Helpers.Cluster
public import Papers.HawkesD75660b.Helpers.ParkingEnumeration

/-! The actual dependent size/count/exponential-gap mixture. -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

namespace Papers.HawkesD75660b

/-- For [a number n of gaps](hyp:n), a [gap vector](goal) consists of n nonnegative
real coordinates, with no coordinates when n is zero.
@realizes Z_i(nonnegative coordinates indexed by Fin n, or no variables for n=0) -/
abbrev GapVector (n : ℕ) := Fin n → ℝ≥0

/-- A [duration sample](goal) records a nonnegative integer n, a count vector of
length n, and n nonnegative gap coordinates; its total size is n + 1. -/
abbrev DurationSample := (n : ℕ) × (CountVector n × GapVector n)

/-- For [a count vector κ](hyp:κ) and [a gap coordinate a](hyp:a), the
[exponential gap rate](goal) is the cumulative count through position a + 1,
minus that position, plus one. -/
def gapRate {n : ℕ} (κ : CountVector n) (a : Fin n) : ℝ :=
  (prefixCount κ (a.val + 1) : ℝ) - (a.val + 1) + 1

/-- Given [a count vector κ](hyp:κ), the [joint gap measure](goal) is the product
of exponential measures with rates determined by κ, expressed as nonnegative
real gap coordinates. -/
def countGapMeasure {n : ℕ} (κ : CountVector n) : Measure (GapVector n) :=
  Measure.pi (fun a => (expMeasure (gapRate κ a)).map Real.toNNReal)

/-- For [a number n of gaps](hyp:n), the [component measure](goal) mixes the
joint gap measures over all length-n count vectors with entries from zero to n,
using their preference-count masses and retaining each count vector alongside its gaps. -/
def durationComponentMeasure (n : ℕ) : Measure (CountVector n × GapVector n) :=
  ∑ k : Fin n → Fin (n + 1),
    ENNReal.ofReal (preferenceCountMass n (fun a => (k a).val)) •
      (countGapMeasure (fun a => (k a).val)).map (fun z => (fun a => (k a).val, z))

/-- For [a nonnegative branching parameter ρ](hyp:ρ), the [combinatorial duration
sample measure](goal) mixes the components with n gaps using Borel mass at size
n + 1, retaining the component index in each sample. -/
def combinatorialMeasure (ρ : ℝ≥0) : Measure DurationSample :=
  Measure.sum (fun n => ENNReal.ofReal (borelMass ρ (n + 1)) •
    (durationComponentMeasure n).map (fun q => Sigma.mk n q))

-- @node: def:combx-duration
/-- For [a duration sample q](hyp:q), the [combinatorial duration](goal) is the
sum of all its gap coordinates, with the empty sum equal to zero at size one.
@realizes \tau(nonnegative sum of all sampled gaps; empty sum zero at N=1) -/
def combinatorialDuration (q : DurationSample) : ℝ≥0 := ∑ a, q.2.2 a

-- @node: gapRate_pos
/-- If [κ satisfies the preference-count conditions](hyp:hκ), [the exponential
rate at every gap coordinate a is strictly positive](goal). -/
lemma gapRate_pos {n : ℕ} {κ : CountVector n} (hκ : PreferenceCounts κ) (a : Fin n) :
    0 < gapRate κ a := by
  have hp : a.val + 1 ≤ prefixCount κ (a.val + 1) :=
    hκ.prefix (a.val + 1) (by omega) (by omega)
  have hp' : (a.val : ℝ) + 1 ≤ (prefixCount κ (a.val + 1) : ℝ) := by
    exact_mod_cast hp
  unfold gapRate
  linarith

-- @node: expMeasure_ae_nonneg
/-- For any real rate r, [the exponential measure assigns full measure to
nonnegative real values](goal). -/
lemma expMeasure_ae_nonneg (r : ℝ) : ∀ᵐ x ∂expMeasure r, 0 ≤ x := by
  change ∀ᵐ x ∂volume.withDensity (gammaPDF 1 r), 0 ≤ x
  rw [ae_withDensity_iff (show Measurable (gammaPDF 1 r) by
    unfold gammaPDF
    fun_prop)]
  exact Filter.Eventually.of_forall (fun x hx =>
    le_of_not_gt (fun h => hx (gammaPDF_of_neg h)))

-- @node: expMeasure_map_toNNReal_coe
/-- For any real rate r, [mapping the exponential measure to nonnegative reals
and then back to real values recovers the original exponential measure](goal). -/
lemma expMeasure_map_toNNReal_coe (r : ℝ) :
    ((expMeasure r).map Real.toNNReal).map ((↑) : ℝ≥0 → ℝ) = expMeasure r := by
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  calc
    (expMeasure r).map (NNReal.toReal ∘ Real.toNNReal) = (expMeasure r).map id := by
      apply Measure.map_congr
      filter_upwards [expMeasure_ae_nonneg r] with x hx
      exact Real.coe_toNNReal x hx
    _ = expMeasure r := Measure.map_id

-- @node: countGapMeasure_joint_law
/-- If [κ satisfies the preference-count conditions](hyp:hκ), [the real-valued
gap coordinates under its joint gap measure have the product of exponential
measures with the corresponding gap rates](goal). -/
lemma countGapMeasure_joint_law {n : ℕ} {κ : CountVector n} (hκ : PreferenceCounts κ) :
    (countGapMeasure κ).map (fun z a => (z a : ℝ)) =
      Measure.pi (fun a => expMeasure (gapRate κ a)) := by
  have (a : Fin n) : IsProbabilityMeasure (expMeasure (gapRate κ a)) :=
    isProbabilityMeasure_expMeasure (gapRate_pos hκ a)
  unfold countGapMeasure
  rw [Measure.pi_map_pi (fun a => (show Measurable ((↑) : ℝ≥0 → ℝ) by fun_prop).aemeasurable)]
  simp_rw [expMeasure_map_toNNReal_coe]

-- @node: countGapMeasure_probability
/-- If [κ satisfies the preference-count conditions](hyp:hκ), [its joint gap
measure is a probability measure](goal). -/
lemma countGapMeasure_probability {n : ℕ} {κ : CountVector n}
    (hκ : PreferenceCounts κ) : IsProbabilityMeasure (countGapMeasure κ) := by
  have (a : Fin n) : IsProbabilityMeasure (expMeasure (gapRate κ a)) :=
    isProbabilityMeasure_expMeasure (gapRate_pos hκ a)
  have (a : Fin n) : IsProbabilityMeasure
      ((expMeasure (gapRate κ a)).map Real.toNNReal) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  unfold countGapMeasure
  infer_instance

-- @node: durationComponentMeasure_count_law
/-- For every number n of gaps, [the count vector under the component measure
has the preference-count distribution for n](goal). -/
lemma durationComponentMeasure_count_law (n : ℕ) :
    HasLaw Prod.fst (preferenceCountMeasure n) (durationComponentMeasure n) := by
  classical
  refine ⟨by fun_prop, ?_⟩
  unfold durationComponentMeasure preferenceCountMeasure
  rw [Measure.map_finset_sum (by fun_prop)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Measure.map_smul]
  by_cases hκ : PreferenceCounts (fun a => (k a).val)
  · have := countGapMeasure_probability hκ
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    change _ • (countGapMeasure (fun a => (k a).val)).map
      (fun _ => fun a => (k a).val) = _
    rw [Measure.map_const, measure_univ, one_smul]
  · simp [preferenceCountMass, hκ]

-- @node: durationComponentMeasure_probability
/-- For every number n of gaps, [the component measure is a probability
measure](goal). -/
lemma durationComponentMeasure_probability (n : ℕ) :
    IsProbabilityMeasure (durationComponentMeasure n) := by
  have := preferenceCountMeasure_probability n
  exact (durationComponentMeasure_count_law n).isProbabilityMeasure

-- @node: durationComponentMeasure_fiber_gaps
/-- If [κ satisfies the preference-count conditions](hyp:hκ) and [s is a
measurable set of gap vectors](hyp:hs), [the component measure of samples with
count vector κ and gaps in s equals the preference-count mass of κ multiplied
by its joint gap measure of s](goal). -/
lemma durationComponentMeasure_fiber_gaps {n : ℕ} {κ : CountVector n}
    (hκ : PreferenceCounts κ) {s : Set (GapVector n)} (hs : MeasurableSet s) :
    durationComponentMeasure n ({κ} ×ˢ s) =
      ENNReal.ofReal (preferenceCountMass n κ) * countGapMeasure κ s := by
  classical
  let b : Fin n → Fin (n + 1) := fun a => ⟨κ a,
    Nat.lt_succ_of_le (preferenceCounts_coordinate_bound hκ a)⟩
  have heq (k : Fin n → Fin (n + 1)) : (fun a => (k a).val) = κ ↔ k = b := by
    constructor
    · intro h
      funext a
      exact Fin.ext (congrFun h a)
    · rintro rfl
      rfl
  unfold durationComponentMeasure
  rw [Measure.finsetSum_apply]
  have hterm (k : Fin n → Fin (n + 1)) :
      (ENNReal.ofReal (preferenceCountMass n (fun a => (k a).val)) •
        (countGapMeasure (fun a => (k a).val)).map
          (fun z => (fun a => (k a).val, z))) ({κ} ×ˢ s) =
      if k = b then ENNReal.ofReal (preferenceCountMass n κ) * countGapMeasure κ s else 0 := by
    rw [Measure.smul_apply, Measure.map_apply (by fun_prop)
      ((measurableSet_singleton κ).prod hs)]
    by_cases hk : k = b
    · subst k
      simp [b, smul_eq_mul]
    · have hkκ := mt (heq k).mp hk
      have hpre : (fun z : GapVector n => (fun a => (k a).val, z)) ⁻¹' ({κ} ×ˢ s) = ∅ := by
        ext z
        simp [hkκ]
      simp [hk, hpre, smul_eq_mul]
  simp_rw [hterm]
  simp

-- @node: durationComponentMeasure_conditional_gaps
/-- If [κ satisfies the preference-count conditions](hyp:hκ) and [the
preference-count distribution gives κ positive mass](hyp:hpos), [conditioning
the component measure on count vector κ gives the gaps the joint gap law
associated with κ](goal). -/
lemma durationComponentMeasure_conditional_gaps {n : ℕ} (κ : CountVector n)
    (hκ : PreferenceCounts κ) (hpos : 0 < preferenceCountMeasure n {κ}) :
    HasLaw Prod.snd (countGapMeasure κ)
      (ProbabilityTheory.cond (durationComponentMeasure n) {q | q.1 = κ}) := by
  classical
  have := preferenceCountMeasure_probability n
  have hweight : ENNReal.ofReal (preferenceCountMass n κ) = preferenceCountMeasure n {κ} := by
    rw [← preferenceCountMeasure_singleton, ofReal_measureReal]
  have hfiber : durationComponentMeasure n {q | q.1 = κ} = preferenceCountMeasure n {κ} :=
    (durationComponentMeasure_count_law n).measure_eq (measurableSet_singleton κ)
  refine ⟨by fun_prop, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (by fun_prop) hs,
    cond_apply' (measurable_snd hs), hfiber]
  have hset : {q : CountVector n × GapVector n | q.1 = κ} ∩ Prod.snd ⁻¹' s = {κ} ×ˢ s := by
    ext q
    rfl
  rw [hset, durationComponentMeasure_fiber_gaps hκ hs, hweight, ← mul_assoc,
    ENNReal.inv_mul_cancel (ne_of_gt hpos) (measure_ne_top _ _), one_mul]

-- @node: measurable_durationSize
/-- [The total size of a duration sample, equal to its component index plus one,
is a measurable function](goal). -/
@[fun_prop] lemma measurable_durationSize :
    Measurable (fun q : DurationSample => q.1 + 1) := by
  intro s hs
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro n
  exact (measurable_const : Measurable
    (fun _ : CountVector n × GapVector n => n + 1)) hs

-- @node: measurable_durationSample_mk
/-- For every number n of gaps, [embedding a count-vector and gap-vector pair
into the n-th component of the duration sample space is measurable](goal). -/
@[fun_prop] lemma measurable_durationSample_mk (n : ℕ) :
    Measurable (fun q : CountVector n × GapVector n => (Sigma.mk n q : DurationSample)) := by
  intro s hs
  exact MeasurableSpace.measurableSet_iInf.mp hs n

-- @node: combinatorialMeasure_size_law
/-- If [the nonnegative branching parameter ρ is subcritical](hyp:ρ,hρ), [the total size under
the combinatorial sample measure has the Borel distribution with parameter ρ](goal). -/
lemma combinatorialMeasure_size_law (ρ : ℝ≥0) (hρ : subcritical ρ) :
    HasLaw (fun q : DurationSample => q.1 + 1) (borelMeasure ρ) (combinatorialMeasure ρ) := by
  refine ⟨measurable_durationSize.aemeasurable, ?_⟩
  unfold combinatorialMeasure
  rw [Measure.map_sum measurable_durationSize.aemeasurable]
  have hmap (n : ℕ) :
      ((durationComponentMeasure n).map (fun q => Sigma.mk n q)).map
        (fun q : DurationSample => q.1 + 1) = Measure.dirac (n + 1) := by
    have := durationComponentMeasure_probability n
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    change (durationComponentMeasure n).map (fun _ => n + 1) = _
    rw [Measure.map_const, measure_univ, one_smul]
  simp_rw [Measure.map_smul, hmap]
  apply Measure.ext
  intro s hs
  unfold borelMeasure
  rw [Measure.sum_apply _ hs, Measure.sum_apply _ hs]
  have hshift := tsum_eq_zero_add'
    (f := fun n : ℕ => (ENNReal.ofReal (borelMass ρ n) • Measure.dirac n) s)
    ENNReal.summable
  have hzero : (ENNReal.ofReal (borelMass ρ 0) • Measure.dirac 0) s = 0 := by
    simp [borelMass]
  simpa only [hzero, zero_add] using hshift.symm


-- @node: combinatorialMeasure_probability
/-- If [the nonnegative branching parameter ρ is subcritical](hyp:ρ,hρ), [the combinatorial
sample measure is a probability measure](goal). -/
lemma combinatorialMeasure_probability (ρ : ℝ≥0) (hρ : subcritical ρ) :
    IsProbabilityMeasure (combinatorialMeasure ρ) := by
  have := borelMeasure_probability ρ hρ
  exact (combinatorialMeasure_size_law ρ hρ).isProbabilityMeasure

-- @node: measurable_combinatorialDuration
/-- [The sum of a duration sample's gap coordinates is a measurable
function](goal). -/
@[fun_prop] lemma measurable_combinatorialDuration : Measurable combinatorialDuration := by
  intro s hs
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro n
  change MeasurableSet ((fun q : CountVector n × GapVector n => ∑ a, q.2 a) ⁻¹' s)
  exact (show Measurable (fun q : CountVector n × GapVector n => ∑ a, q.2 a) by
    fun_prop) hs

-- @env: S3
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : Ω → EpochConfiguration) (ρ : ℝ≥0)

-- @node: ass:pin-6
/-- Given [an underlying measure P](hyp:P), [an epoch configuration C for each
outcome](hyp:C), and [a nonnegative branching parameter ρ](hyp:ρ), the
[duration representation property](goal) asserts that the observed cluster
duration under P and the sum of gaps under the combinatorial sample measure
with parameter ρ have identical distributions. -/
def durationRepresentation : Prop :=
  IdentDistrib (clusterDuration C) combinatorialDuration P (combinatorialMeasure ρ)

end Papers.HawkesD75660b
