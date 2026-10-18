module
public import Papers.TbsNeuralCausalPi.Helpers.ObservationalFrequencyConcentration
public import Mathlib.Data.Fintype.EquivFin
/-! # Wasserstein concentration at the realized stratum size

The conditional empirical measure is the empirical law of the observations
selected by the complete label pattern. Product-law estimates uniform over
large enough sample sizes therefore transfer without a union bound over
patterns. Small counts are controlled by the established frequency tail.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

/-- [The indices assigned category a can be enumerated without repetitions by a sequence whose length is exactly their count, with every such index appearing](goal). -/
-- @node: exists_stratum_enumeration
lemma exists_stratum_enumeration {I A : Type*} [Fintype I]
    (c : I → A) (a : A) :
    ∃ e : Fin ((Finset.univ.filter fun i => c i = a).card) → I,
      Function.Injective e ∧ ∀ i, c i = a ↔ ∃ j, e j = i := by
  classical
  let s := Finset.univ.filter fun i => c i = a
  let e : Fin s.card → I := fun j => ((Finset.equivFin s).symm j).val
  refine ⟨e, Subtype.val_injective.comp (Finset.equivFin s).symm.injective, ?_⟩
  intro i
  constructor
  · intro hi
    let z : s := ⟨i, by simp [s, hi]⟩
    exact ⟨Finset.equivFin s z, by simp [e, z]⟩
  · rintro ⟨j, rfl⟩
    exact (Finset.mem_filter.mp ((Finset.equivFin s).symm j).property).2

/-- For [a sample of positive size](hyp:hm), suppose [each observation is measurable](hyp:hsample)
and [the finite-valued label is measurable](hyp:hlabel). If
[property P defines a measurable event for an empirical measure of every fixed sample size](hyp:hP),
then [P also defines a measurable event for the empirical law conditional on category a](goal). -/
-- @node: measurableSet_empirical_cond_stratum
lemma measurableSet_empirical_cond_stratum
    {Omega X A : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
    [MeasurableSpace A] [Finite A] [MeasurableSingletonClass A]
    {m : ℕ} (hm : 0 < m) (sample : Fin m → Omega → X)
    (hsample : ∀ i, Measurable (sample i))
    (label : X → A) (hlabel : Measurable label) (a : A)
    (P : Measure X → Prop)
    (hP : ∀ N : ℕ, MeasurableSet {x : Fin N → X | P (empiricalMeasure x)}) :
    MeasurableSet {w | P (cond (empiricalMeasure (fun i => sample i w)) (label ⁻¹' {a}))} := by
  classical
  let := Fintype.ofFinite A
  choose e he hcover using (fun c : Fin m → A => exists_stratum_enumeration c a)
  have hselected (c : Fin m → A) (w : Omega)
      (hw : ∀ i, label (sample i w) = c i) :=
    empiricalMeasure_cond_eq_selected hm (fun i => sample i w)
      (label ⁻¹' {a}) (hlabel (measurableSet_singleton a)) (e c) (he c) (by
        intro i
        change label (sample i w) = a ↔ _
        rw [hw i]
        exact hcover c i)
  have heq : {w | P (cond (empiricalMeasure (fun i => sample i w)) (label ⁻¹' {a}))} =
      ⋃ c : Fin m → A, {w | ∀ i, label (sample i w) = c i} ∩
        {w | P (empiricalMeasure (fun j => sample (e c j) w))} := by
    ext w
    constructor
    · intro hw
      apply Set.mem_iUnion.mpr
      refine ⟨fun i => label (sample i w), fun _ => rfl, ?_⟩
      change P _
      rw [← hselected _ w (fun _ => rfl)]
      exact hw
    · intro hw
      obtain ⟨c, hc, hp⟩ := Set.mem_iUnion.mp hw
      change P _
      rw [hselected c w hc]
      exact hp
  rw [heq]
  apply MeasurableSet.iUnion
  intro c
  apply MeasurableSet.inter
  · simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i =>
      (hlabel.comp (hsample i)) (measurableSet_singleton (c i))
  · exact (hP _).preimage (by fun_prop)

/-- For [a sample of positive size m](hyp:hm), suppose [each observation is measurable](hyp:hsample),
[the observations are independent](hyp:hind), [each has population law mu](hyp:hlaw),
[the categorical label is measurable](hyp:hlabel), and [category a has positive population probability](hyp:ha).
Given [a probability bound beta](hyp:beta), assume [the conditional empirical Wasserstein failure events at tolerance t are measurable for every fixed sample size](hyp:hB)
and [their probabilities under independent category-a draws are at most beta whenever the size is at least half the expected category-a count](hyp:hbound).
Then [the actual category-a conditional empirical failure probability is at most beta plus twice the number of categories times the exponential of minus twice m times the square of the category-a probability divided by twice the number of categories](goal). -/
-- @node: iid_observational_stratum_wasserstein_tail
lemma iid_observational_stratum_wasserstein_tail
    {Omega X A : Type*} [MeasurableSpace Omega] [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace A]
    [Fintype A] [Nonempty A] [MeasurableSingletonClass A]
    (Q : Measure Omega) [IsProbabilityMeasure Q] (mu : Measure X) [IsProbabilityMeasure mu]
    {m : ℕ} (hm : 0 < m) (sample : Fin m → Omega → X)
    (hsample : ∀ i, Measurable (sample i)) (hind : iIndepFun sample Q)
    (hlaw : ∀ i, Q.map (sample i) = mu)
    (label : X → A) (hlabel : Measurable label)
    (a : A) (ha : 0 < mu.real (label ⁻¹' {a})) (t : ℝ) (beta : ℝ≥0∞)
    (hB : ∀ N : ℕ, MeasurableSet {x : Fin N → X |
      ¬ wasserstein1 (cond mu (label ⁻¹' {a})) (empiricalMeasure x) ≤ ENNReal.ofReal t})
    (hbound : ∀ N : ℕ, m * mu.real (label ⁻¹' {a}) / 2 ≤ N →
      (Measure.pi (fun _ : Fin N => cond mu (label ⁻¹' {a})))
        {x | ¬ wasserstein1 (cond mu (label ⁻¹' {a})) (empiricalMeasure x) ≤
          ENNReal.ofReal t} ≤ beta) :
    Q {w | ¬ wasserstein1 (cond mu (label ⁻¹' {a}))
        (cond (empiricalMeasure (fun i => sample i w)) (label ⁻¹' {a})) ≤ ENNReal.ofReal t} ≤
      ENNReal.ofReal (2 * Fintype.card A * Real.exp
        (-2 * m * ((mu.real (label ⁻¹' {a}) / 2) / Fintype.card A) ^ 2)) + beta := by
  classical
  have hE := measurableSet_empirical_cond_stratum hm sample hsample label hlabel a
    (fun nu => ¬ wasserstein1 (cond mu (label ⁻¹' {a})) nu ≤ ENNReal.ofReal t) hB
  let N : (Fin m → A) → ℕ := fun c => (Finset.univ.filter fun i => c i = a).card
  choose e he hcover using (fun c : Fin m → A => exists_stratum_enumeration c a)
  have hc (c : Fin m → A) (j : Fin (N c)) : c (e c j) = a :=
    (hcover c (e c j)).mpr ⟨j, rfl⟩
  let good : (Fin m → A) → Prop := fun c => m * mu.real (label ⁻¹' {a}) / 2 ≤ N c
  have htransfer := iid_stratum_sampling_failure_probability_le Q mu sample hsample hind hlaw
    label hlabel a N e he hc good
    (fun c => {x : Fin (N c) → X | ¬ wasserstein1 (cond mu (label ⁻¹' {a}))
      (empiricalMeasure x) ≤ ENNReal.ofReal t})
    (fun c => hB (N c)) _ hE (by
      intro c w hw hbad
      have hselected := empiricalMeasure_cond_eq_selected hm (fun i => sample i w)
        (label ⁻¹' {a}) (hlabel (measurableSet_singleton a)) (e c) (he c) (by
          intro i
          change label (sample i w) = a ↔ _
          rw [hw i]
          exact hcover c i)
      change ¬ wasserstein1 _ _ ≤ _
      rw [← hselected]
      exact hbad)
    beta (fun c hg => hbound (N c) hg)
  apply htransfer.trans
  apply add_le_add _ le_rfl
  have htail := iid_observational_small_count_tail Q mu hm sample hsample hind hlaw
    label hlabel a ha
  rw [← ENNReal.ofReal_toReal (measure_ne_top Q _)]
  apply ENNReal.ofReal_le_ofReal
  simpa only [good, N, not_le, Measure.real] using htail

/-- For [a sample of positive size m](hyp:hm), suppose [each observation is measurable](hyp:hsample),
[the observations are independent](hyp:hind), [each has population law mu](hyp:hlaw),
[the categorical label is measurable](hyp:hlabel), [S is measurable](hyp:hS), and [S has population probability one](hyp:hmuS).
Assume [D is nonnegative](hyp:hD), [t is nonnegative](hyp:ht), [the frequency tolerance e is positive](hyp:he),
and [distances within S are at most D](hyp:hdiam). Given [category-specific probability bounds beta](hyp:beta),
suppose [the conditional empirical failure events at tolerance t are measurable in every positive-mass category and at every sample size](hyp:hB)
and [their product-law probabilities are bounded by the corresponding beta whenever the sample size is at least half the expected category count](hyp:hbound).
Then [the full empirical Wasserstein failure probability at tolerance t plus D times e divided by two is bounded by the frequency tail and the sum, over positive-mass categories, of their small-count tails and beta bounds](goal).

Each frequency tail is twice the number of categories times the exponential of minus twice m times the squared tolerance divided by the squared number of categories; a small-count tail uses half the category probability as its tolerance. -/
-- @node: iid_observational_wasserstein_failure_le_of_product_tails
lemma iid_observational_wasserstein_failure_le_of_product_tails
    {Omega X : Type*} [MeasurableSpace Omega] [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] {k m : ℕ} [Nonempty (Fin k)]
    (Q : Measure Omega) [IsProbabilityMeasure Q] (mu : Measure X) [IsProbabilityMeasure mu]
    (hm : 0 < m) (sample : Fin m → Omega → X)
    (hsample : ∀ i, Measurable (sample i)) (hind : iIndepFun sample Q)
    (hlaw : ∀ i, Q.map (sample i) = mu)
    (label : X → Fin k) (hlabel : Measurable label)
    (S : Set X) (hS : MeasurableSet S) (hmuS : mu S = 1)
    (D t e : ℝ) (hD : 0 ≤ D) (ht : 0 ≤ t) (he : 0 < e)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ D)
    (beta : Fin k → ℝ≥0∞)
    (hB : ∀ a, 0 < mu.real (label ⁻¹' {a}) → ∀ N : ℕ,
      MeasurableSet {x : Fin N → X | ¬ wasserstein1 (cond mu (label ⁻¹' {a}))
        (empiricalMeasure x) ≤ ENNReal.ofReal t})
    (hbound : ∀ a, 0 < mu.real (label ⁻¹' {a}) → ∀ N : ℕ,
      m * mu.real (label ⁻¹' {a}) / 2 ≤ N →
      (Measure.pi (fun _ : Fin N => cond mu (label ⁻¹' {a})))
        {x | ¬ wasserstein1 (cond mu (label ⁻¹' {a})) (empiricalMeasure x) ≤
          ENNReal.ofReal t} ≤ beta a) :
    Q {w | ¬ wasserstein1 mu (empiricalMeasure (fun i => sample i w)) ≤
      ENNReal.ofReal (t + D / 2 * e)} ≤
      ENNReal.ofReal (2 * k * Real.exp (-2 * m * (e / k) ^ 2)) +
        ∑ a, if 0 < mu.real (label ⁻¹' {a}) then
          ENNReal.ofReal (2 * k * Real.exp
            (-2 * m * ((mu.real (label ⁻¹' {a}) / 2) / k) ^ 2)) + beta a else 0 := by
  classical
  apply iid_observational_wasserstein_failure_le Q mu hm sample hsample hind hlaw
    label hlabel S hS hmuS D t e hD ht he hdiam
  intro a
  by_cases ha : 0 < mu.real (label ⁻¹' {a})
  · rw [if_pos ha]
    have htail := iid_observational_stratum_wasserstein_tail Q mu hm sample hsample hind hlaw
      label hlabel a ha t (beta a) (hB a ha) (hbound a ha)
    simp only [Fintype.card_fin] at htail
    apply le_trans (measure_mono ?_)
      htail
    intro w hw
    exact hw.2.2
  · rw [if_neg ha]
    have hzero : mu (label ⁻¹' {a}) = 0 := by
      have hreal : mu.real (label ⁻¹' {a}) = 0 :=
        le_antisymm (le_of_not_gt ha) ENNReal.toReal_nonneg
      simpa only [Measure.real, ENNReal.toReal_eq_zero_iff, measure_ne_top, or_false] using hreal
    simp only [hzero, ne_eq, not_true_eq_false, false_and, Set.ofPred_false, measure_empty,
      le_refl]

/-- For [a sample size N greater than zero](hyp:hN), [the empirical law of N copies of v is the point mass at v](goal). -/
-- @node: empiricalMeasure_const_eq_dirac
lemma empiricalMeasure_const_eq_dirac {X : Type*} [MeasurableSpace X]
    {N : ℕ} (hN : 0 < N) (v : X) :
    empiricalMeasure (fun _ : Fin N => v) = Measure.dirac v := by
  simp only [empiricalMeasure, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ≥0∞, smul_smul]
  rw [ENNReal.inv_mul_cancel (by exact_mod_cast hN.ne') (by simp), one_smul]

/-- For [a sample size N greater than zero](hyp:hN), [independent draws from the point mass at v have zero probability of empirical Wasserstein distance exceeding the nonnegative part of any real tolerance t](goal). -/
-- @node: dirac_empirical_wasserstein_failure_zero
lemma dirac_empirical_wasserstein_failure_zero
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {N : ℕ} (hN : 0 < N) (v : X) (t : ℝ) :
    (Measure.pi (fun _ : Fin N => Measure.dirac v))
      {x | ¬ wasserstein1 (Measure.dirac v) (empiricalMeasure x) ≤ ENNReal.ofReal t} = 0 := by
  have hcoord (i : Fin N) :
      ∀ᵐ x ∂Measure.pi (fun _ : Fin N => Measure.dirac v), x i = v := by
    apply (ae_map_iff (f := fun x : Fin N → X => x i) (p := fun y => y = v)
      (measurable_pi_apply i).aemeasurable (measurableSet_singleton v)).mp
    rw [(measurePreserving_eval (fun _ : Fin N => Measure.dirac v) i).map_eq]
    rw [ae_dirac_eq]
    exact Filter.eventually_pure.mpr rfl
  have hdiag : wasserstein1 (Measure.dirac v) (Measure.dirac v) = 0 := by
    apply le_antisymm _ bot_le
    have hc : Measure.dirac (v, v) ∈ couplings (Measure.dirac v) (Measure.dirac v) :=
      ⟨inferInstance, by simp, by simp⟩
    apply (wasserstein1_eq_couplings _ _).trans_le
    apply iInf_le_of_le ⟨Measure.dirac (v, v), hc⟩
    simp
  have hgood : ∀ᵐ x ∂Measure.pi (fun _ : Fin N => Measure.dirac v),
      wasserstein1 (Measure.dirac v) (empiricalMeasure x) ≤ ENNReal.ofReal t := by
    filter_upwards [ae_all_iff.mpr hcoord] with x hx
    have heq : x = fun _ => v := funext hx
    rw [heq, empiricalMeasure_const_eq_dirac hN v, hdiag]
    exact bot_le
  exact ae_iff.mp hgood

end Papers.TbsNeuralCausalPi
