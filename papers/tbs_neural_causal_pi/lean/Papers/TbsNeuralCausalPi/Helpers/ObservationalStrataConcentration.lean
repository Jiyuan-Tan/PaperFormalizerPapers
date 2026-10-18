module
public import Papers.TbsNeuralCausalPi.Helpers.ObservationalStrataSampling
public import Causalean.Mathlib.Probability.FinitePartitionConditional
/-! # Averaging stratum sampling bounds over the observed label pattern

The realized category counts determine which conditional IID estimate applies.
Averaging over patterns does not multiply its failure probability by the number
of patterns. Small counts are charged separately. Empirical stratum masses are
exactly their observed frequencies, including empty strata.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
open scoped ENNReal

attribute [local instance] Classical.propDecidable

/-- Suppose [each observation is measurable](hyp:hsample), [the categorical label is measurable](hyp:hlabel),
and [the failure event E is measurable](hyp:hE). For [a probability bound beta](hyp:beta),
if [the conditional probability of E is at most beta for every complete label pattern of positive probability](hyp:hcond),
then [the unconditional probability of E is at most beta](goal). -/
-- @node: label_pattern_failure_probability_le
lemma label_pattern_failure_probability_le
    {Omega X I A : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
    [MeasurableSpace A] [Fintype I] [Fintype A] [MeasurableSingletonClass A]
    (Q : Measure Omega) [IsProbabilityMeasure Q]
    (sample : I → Omega → X) (hsample : ∀ i, Measurable (sample i))
    (label : X → A) (hlabel : Measurable label)
    (E : Set Omega) (hE : MeasurableSet E) (beta : ℝ≥0∞)
    (hcond : ∀ c : I → A, Q {w | ∀ i, label (sample i w) = c i} ≠ 0 →
      (cond Q {w | ∀ i, label (sample i w) = c i}) E ≤ beta) :
    Q E ≤ beta := by
  classical
  have hcell (c : I → A) : MeasurableSet {w | ∀ i, label (sample i w) = c i} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i =>
      (hlabel.comp (hsample i)) (measurableSet_singleton (c i))
  apply Causalean.Mathlib.Probability.measure_le_of_cond_le_on_finite_partition Q
    (fun c : I → A => {w | ∀ i, label (sample i w) = c i})
    hcell ?_ ?_ E hE beta hcond
  · intro c d hcd
    apply Set.disjoint_left.mpr
    intro w hc hd
    exact hcd (funext fun i => (hc i).symm.trans (hd i))
  · ext w
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact ⟨fun i => label (sample i w), fun _ => rfl⟩

/-- Suppose [each observation is measurable](hyp:hsample), [the categorical label is measurable](hyp:hlabel),
and [the failure event E is measurable](hyp:hE). For [a probability bound beta](hyp:beta),
if [every good label pattern of positive probability gives conditional failure probability at most beta](hyp:hcond),
then [the unconditional failure probability is at most the probability of a pattern that is not good plus beta](goal). -/
-- @node: label_pattern_failure_probability_le_of_good_counts
lemma label_pattern_failure_probability_le_of_good_counts
    {Omega X I A : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
    [MeasurableSpace A] [Fintype I] [Fintype A] [MeasurableSingletonClass A]
    (Q : Measure Omega) [IsProbabilityMeasure Q]
    (sample : I → Omega → X) (hsample : ∀ i, Measurable (sample i))
    (label : X → A) (hlabel : Measurable label)
    (good : (I → A) → Prop) (E : Set Omega) (hE : MeasurableSet E) (beta : ℝ≥0∞)
    (hcond : ∀ c : I → A, good c →
      Q {w | ∀ i, label (sample i w) = c i} ≠ 0 →
      (cond Q {w | ∀ i, label (sample i w) = c i}) E ≤ beta) :
    Q E ≤ Q {w | ¬ good (fun i => label (sample i w))} + beta := by
  classical
  let H : Set Omega := {w | good (fun i => label (sample i w))}
  have hH : MeasurableSet H := by
    have hp : Measurable (fun w i => label (sample i w)) := by fun_prop
    exact hp (Set.toFinite {c | good c}).measurableSet
  have hgood : Q (E ∩ H) ≤ beta := by
    apply label_pattern_failure_probability_le Q sample hsample label hlabel
      (E ∩ H) (hE.inter hH) beta
    intro c hc
    by_cases hg : good c
    · exact (measure_mono Set.inter_subset_left).trans (hcond c hg hc)
    · have hempty : {w | ∀ i, label (sample i w) = c i} ∩ (E ∩ H) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro w ⟨hw, _, hgw⟩
        have heq : (fun i => label (sample i w)) = c := funext hw
        exact hg (heq ▸ hgw)
      rw [cond_apply' (hE.inter hH), hempty]
      simp
  calc
    Q E ≤ Q (Hᶜ ∪ (E ∩ H)) := measure_mono (by intro w hw; by_cases h : w ∈ H <;> simp_all)
    _ ≤ Q Hᶜ + Q (E ∩ H) := measure_union_le _ _
    _ ≤ _ := add_le_add_right hgood _

/-- Suppose [each observation is measurable](hyp:hsample), [the observations are independent](hyp:hind),
[each has population law mu](hyp:hlaw), and [the categorical label is measurable](hyp:hlabel).
For [a selection of indices for each label pattern](hyp:e) that [has no repetitions](hyp:he)
and [selects only category a](hyp:hc), let [B be the selected-sample failure events](hyp:B),
with [each such event measurable](hyp:hB), and suppose [the original failure event E is measurable](hyp:hE)
and [implies the corresponding selected-sample failure on each pattern](hyp:hbad).
Given [a bound beta](hyp:beta) such that [every good pattern's product conditional law assigns its selected failure event probability at most beta](hyp:hbound),
[the probability of E is at most the probability of a pattern that is not good plus beta](goal). -/
-- @node: iid_stratum_sampling_failure_probability_le
lemma iid_stratum_sampling_failure_probability_le
    {Omega X I A : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
    [MeasurableSpace A] [Fintype I] [Fintype A] [MeasurableSingletonClass A]
    (Q : Measure Omega) [IsProbabilityMeasure Q] (mu : Measure X)
    [IsProbabilityMeasure mu]
    (sample : I → Omega → X) (hsample : ∀ i, Measurable (sample i))
    (hind : iIndepFun sample Q) (hlaw : ∀ i, Q.map (sample i) = mu)
    (label : X → A) (hlabel : Measurable label) (a : A)
    (N : (I → A) → ℕ) (e : ∀ c : I → A, Fin (N c) → I)
    (he : ∀ c, Function.Injective (e c)) (hc : ∀ (c : I → A) (j : Fin (N c)), c (e c j) = a)
    (good : (I → A) → Prop)
    (B : ∀ c, Set (Fin (N c) → X)) (hB : ∀ c, MeasurableSet (B c))
    (E : Set Omega) (hE : MeasurableSet E)
    (hbad : ∀ c w, (∀ i, label (sample i w) = c i) → w ∈ E →
      (fun j => sample (e c j) w) ∈ B c)
    (beta : ℝ≥0∞)
    (hbound : ∀ c, good c →
      (Measure.pi (fun _ : Fin (N c) => cond mu (label ⁻¹' {a}))) (B c) ≤ beta) :
    Q E ≤ Q {w | ¬ good (fun i => label (sample i w))} + beta := by
  classical
  apply label_pattern_failure_probability_le_of_good_counts Q sample hsample label hlabel
    good E hE beta
  intro c hg hpos
  have hcell : MeasurableSet {w | ∀ i, label (sample i w) = c i} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i =>
      (hlabel.comp (hsample i)) (measurableSet_singleton (c i))
  have htransfer := iid_stratum_conditional_event_probability Q mu sample hsample hind hlaw
    label hlabel c hpos a (e c) (he c) (hc c) (B c) (hB c)
  apply le_trans ?_ ((le_of_eq htransfer).trans (hbound c hg))
  rw [← cond_inter_self hcell E Q,
    ← cond_inter_self hcell {w | (fun j => sample (e c j) w) ∈ B c} Q]
  apply measure_mono
  rintro w ⟨hw, hEw⟩
  exact ⟨hw, hbad c w hw hEw⟩

/-- For [a measurable stratum S](hyp:hS), [its empirical probability equals the number of sample observations in S divided by the whole sample size](goal).

The identity uses extended nonnegative numbers and also covers zero counts and an empty sample. -/
-- @node: empiricalMeasure_stratum_mass
lemma empiricalMeasure_stratum_mass
    {X : Type*} [MeasurableSpace X] {m : ℕ}
    (x : Fin m → X) (S : Set X) (hS : MeasurableSet S) :
    (empiricalMeasure x) S = (m : ℝ≥0∞)⁻¹ *
      ((Finset.univ.filter fun i => x i ∈ S).card : ℝ≥0∞) := by
  classical
  simp only [empiricalMeasure, Measure.smul_apply, Measure.finsetSum_apply,
    Measure.dirac_apply' _ hS, smul_eq_mul]
  congr 1
  simp [Set.indicator, Finset.sum_boole]

/-- For [a measurable stratum S](hyp:hS), [its real-valued empirical probability equals the number of sample observations in S divided by the whole sample size](goal).

Division by zero is interpreted as zero, so the formula includes an empty sample. -/
-- @node: empiricalMeasure_stratum_real_mass
lemma empiricalMeasure_stratum_real_mass
    {X : Type*} [MeasurableSpace X] {m : ℕ}
    (x : Fin m → X) (S : Set X) (hS : MeasurableSet S) :
    (empiricalMeasure x).real S =
      ((Finset.univ.filter fun i => x i ∈ S).card : ℝ) / m := by
  classical
  rw [Measure.real, empiricalMeasure_stratum_mass x S hS,
    ENNReal.toReal_mul, ENNReal.toReal_inv]
  simp [div_eq_mul_inv, mul_comm]

/-- Suppose [the categorical label is measurable](hyp:hlabel), [S is measurable](hyp:hS),
[mu assigns S probability one](hyp:hm), [nu assigns S probability one](hyp:hn), and
[all distances within S are at most D](hyp:hdiam). If
[the conditional Wasserstein distance is at most t in every category having positive mass under both laws](hyp:herr),
then [the full Wasserstein distance is at most t plus D divided by two times the sum of absolute category-probability differences](goal). -/
-- @node: observational_wasserstein_le_of_stratum_errors
lemma observational_wasserstein_le_of_stratum_errors
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {k : ℕ}
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (label : X → Fin k) (hlabel : Measurable label)
    (S : Set X) (hS : MeasurableSet S) (hm : mu S = 1) (hn : nu S = 1)
    (D t : ℝ) (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ D)
    (herr : ∀ i, mu (label ⁻¹' {i}) ≠ 0 → nu (label ⁻¹' {i}) ≠ 0 →
      wasserstein1 (cond mu (label ⁻¹' {i})) (cond nu (label ⁻¹' {i})) ≤
        ENNReal.ofReal t) :
    wasserstein1 mu nu ≤ ENNReal.ofReal t +
      ENNReal.ofReal (D / 2 * ∑ i,
        |mu.real (label ⁻¹' {i}) - nu.real (label ⁻¹' {i})|) := by
  obtain ⟨rho, sigma, hcond, htransport⟩ :=
    observational_stratified_wasserstein_le mu nu label hlabel S hS hm hn D hdiam
  apply htransport.trans
  apply add_le_add_left
  calc
    _ ≤ ∑ i, ENNReal.ofReal (mu.real (label ⁻¹' {i})) * ENNReal.ofReal t := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hmu : mu (label ⁻¹' {i}) = 0
      · simp [Measure.real, hmu]
      by_cases hnu : nu (label ⁻¹' {i}) = 0
      · simp [Measure.real, hnu]
      exact mul_le_mul'
        (ENNReal.ofReal_le_ofReal (min_le_left _ _))
        (by rw [(hcond i).1 hmu, (hcond i).2 hnu]; exact herr i hmu hnu)
    _ = ENNReal.ofReal t := by
      rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg
        (fun i _ => show 0 ≤ mu.real (label ⁻¹' {i}) from ENNReal.toReal_nonneg),
        (finite_stratum_weights_simplex mu label hlabel).2]
      simp

end Papers.TbsNeuralCausalPi
