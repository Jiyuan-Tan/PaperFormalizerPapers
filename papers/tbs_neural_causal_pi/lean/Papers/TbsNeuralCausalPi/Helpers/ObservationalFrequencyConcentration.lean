module
public import Papers.TbsNeuralCausalPi.Helpers.ObservationalStrataConcentration
public import Causalean.Stat.Minimax.SideInformation.Finite.Concentration
/-! # Concentration of the actual observational category frequencies

The finite-alphabet Hoeffding bound transfers to the complete categorical labels
of paired IID observations. No independence within an observation is required.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
open Causalean.Stat.Minimax.FiniteSideInformation
open scoped ENNReal
attribute [local instance] Classical.propDecidable

-- @node: finite_label_frequency_tail
/-- For independent draws from a probability law on a finite nonempty
alphabet, with [positive sample size m](hyp:hm) and [positive tolerance e](hyp:he),
[the probability that the sum of absolute empirical frequency errors is at
least e is at most twice the alphabet size times the exponential of minus
twice m times the squared ratio of e to the alphabet size](goal). -/
lemma finite_label_frequency_tail
    {A : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (p : Measure A) [IsProbabilityMeasure p]
    {m : ℕ} (hm : 0 < m) {e : ℝ} (he : 0 < e) :
    (Measure.pi (fun _ : Fin m => p)).real
      {z | e ≤ ∑ a, |empiricalFrequency A hm z a - p.real {a}|} ≤
        2 * Fintype.card A * Real.exp (-2 * m * (e / Fintype.card A) ^ 2) := by
  classical
  let w : FinitePmf A := ⟨fun a => p.real {a},
    ⟨fun _ => ENNReal.toReal_nonneg, by
      simpa using (sum_measureReal_singleton (μ := p) (Finset.univ : Finset A))⟩⟩
  have hatom (z : Fin m → A) :
      (Measure.pi (fun _ : Fin m => p)).real {z} = productProbability A w z := by
    simp only [Measure.real, Measure.pi_singleton, ENNReal.toReal_prod]
    rfl
  have hsum : (Measure.pi (fun _ : Fin m => p)).real
      {z | e ≤ ∑ a, |empiricalFrequency A hm z a - p.real {a}|} =
      ∑ z : Fin m → A, if e ≤ empiricalL1 A hm z w then productProbability A w z else 0 := by
    rw [← Finset.sum_filter]
    simp_rw [← hatom]
    rw [sum_measureReal_singleton]
    congr 1
    ext z
    simp [empiricalL1, w]
  rw [hsum]
  exact empiricalL1_tail A hm w he

-- @node: iid_observational_frequency_tail
/-- For [a positive sample size m](hyp:hm), suppose the observations are
[measurable](hyp:hsample), [independent under the sampling law](hyp:hind), and
[each distributed according to the population law](hyp:hlaw), with [a measurable
finite-valued label](hyp:hlabel) and [positive tolerance e](hyp:he). [The
probability that the sum of absolute differences between observed label
frequencies and population label probabilities is at least e is at most twice
the number of labels times the exponential of minus twice m times the squared
ratio of e to the number of labels](goal). -/
lemma iid_observational_frequency_tail
    {Omega X A : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
    [MeasurableSpace A] [Fintype A] [Nonempty A] [MeasurableSingletonClass A]
    (Q : Measure Omega) [IsProbabilityMeasure Q] (mu : Measure X) [IsProbabilityMeasure mu]
    {m : ℕ} (hm : 0 < m) (sample : Fin m → Omega → X)
    (hsample : ∀ i, Measurable (sample i)) (hind : iIndepFun sample Q)
    (hlaw : ∀ i, Q.map (sample i) = mu)
    (label : X → A) (hlabel : Measurable label) {e : ℝ} (he : 0 < e) :
    Q.real {w | e ≤ ∑ a,
      |(((Finset.univ.filter fun i => label (sample i w) = a).card : ℝ) / m) -
        mu.real (label ⁻¹' {a})|} ≤
      2 * Fintype.card A * Real.exp (-2 * m * (e / Fintype.card A) ^ 2) := by
  classical
  let p := mu.map label
  have hp : IsProbabilityMeasure p := Measure.isProbabilityMeasure_map hlabel.aemeasurable
  have hjoint : Q.map (fun w i => label (sample i w)) =
      Measure.pi (fun _ : Fin m => p) := by
    have hj := (hind.comp (fun _ => label) (fun _ => hlabel)).map_fun_eq_pi_map
      (fun i => (hlabel.comp (hsample i)).aemeasurable)
    simp only [Function.comp_def] at hj
    rw [hj]
    congr 1
    funext i
    change Q.map (label ∘ sample i) = p
    rw [← Measure.map_map hlabel (hsample i), hlaw i]
  have hfreq (z : Fin m → A) (a : A) : empiricalFrequency A hm z a =
      ((Finset.univ.filter fun i => z i = a).card : ℝ) / m := by
    simp [empiricalFrequency, Finset.sum_boole]
  have hmass (a : A) : p.real {a} = mu.real (label ⁻¹' {a}) := by
    simp [p, Measure.real, Measure.map_apply hlabel (measurableSet_singleton a)]
  have htail := finite_label_frequency_tail p hm he
  simp_rw [hfreq, hmass] at htail
  rw [← hjoint, Measure.real, Measure.map_apply (by fun_prop)
    (by exact (Set.toFinite _).measurableSet)] at htail
  simpa only [Measure.real, Set.preimage_ofPred_eq] using htail

-- @node: iid_observational_small_count_tail
/-- For [a positive sample size m](hyp:hm), suppose the observations are
[measurable](hyp:hsample), [independent](hyp:hind), and [each distributed
according to the population law](hyp:hlaw), with [a measurable finite-valued
label](hyp:hlabel) and [positive population probability p for label a](hyp:ha).
[The probability that label a occurs fewer than m times p divided by two
times is at most twice the number of labels times the exponential of minus
twice m times the squared ratio of p to twice the number of labels](goal). -/
lemma iid_observational_small_count_tail
    {Omega X A : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
    [MeasurableSpace A] [Fintype A] [Nonempty A] [MeasurableSingletonClass A]
    (Q : Measure Omega) [IsProbabilityMeasure Q] (mu : Measure X) [IsProbabilityMeasure mu]
    {m : ℕ} (hm : 0 < m) (sample : Fin m → Omega → X)
    (hsample : ∀ i, Measurable (sample i)) (hind : iIndepFun sample Q)
    (hlaw : ∀ i, Q.map (sample i) = mu)
    (label : X → A) (hlabel : Measurable label)
    (a : A) (ha : 0 < mu.real (label ⁻¹' {a})) :
    Q.real {w | ((Finset.univ.filter fun i => label (sample i w) = a).card : ℝ) <
      m * mu.real (label ⁻¹' {a}) / 2} ≤
      2 * Fintype.card A * Real.exp
        (-2 * m * ((mu.real (label ⁻¹' {a}) / 2) / Fintype.card A) ^ 2) := by
  classical
  apply le_trans (measureReal_mono ?_)
    (iid_observational_frequency_tail Q mu hm sample hsample hind hlaw label hlabel (half_pos ha))
  intro w hw
  change ((Finset.univ.filter fun i => label (sample i w) = a).card : ℝ) <
    m * mu.real (label ⁻¹' {a}) / 2 at hw
  change mu.real (label ⁻¹' {a}) / 2 ≤ _
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hcount : ((Finset.univ.filter fun i => label (sample i w) = a).card : ℝ) / m <
      mu.real (label ⁻¹' {a}) / 2 := by
    apply (div_lt_iff₀ hmR).mpr
    nlinarith [hw]
  calc
    _ ≤ |((Finset.univ.filter fun i => label (sample i w) = a).card : ℝ) / m -
        mu.real (label ⁻¹' {a})| := by
      rw [abs_of_neg (by linarith)]
      linarith
    _ ≤ ∑ b, |((Finset.univ.filter fun i => label (sample i w) = b).card : ℝ) / m -
        mu.real (label ⁻¹' {b})| :=
      Finset.single_le_sum (f := fun b =>
        |((Finset.univ.filter fun i => label (sample i w) = b).card : ℝ) / m -
          mu.real (label ⁻¹' {b})|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ a)

-- @node: iid_empirical_stratum_mass_tail
/-- For [a positive sample size m](hyp:hm), suppose the observations are
[measurable](hyp:hsample), [independent](hyp:hind), and [each distributed
according to the population law](hyp:hlaw), with [a measurable finite-valued
label](hyp:hlabel) and [positive tolerance e](hyp:he). [The probability that
the sum of absolute population-versus-empirical stratum mass differences is
at least e is at most twice the number of labels times the exponential of
minus twice m times the squared ratio of e to the number of labels](goal). -/
lemma iid_empirical_stratum_mass_tail
    {Omega X A : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
    [MeasurableSpace A] [Fintype A] [Nonempty A] [MeasurableSingletonClass A]
    (Q : Measure Omega) [IsProbabilityMeasure Q] (mu : Measure X) [IsProbabilityMeasure mu]
    {m : ℕ} (hm : 0 < m) (sample : Fin m → Omega → X)
    (hsample : ∀ i, Measurable (sample i)) (hind : iIndepFun sample Q)
    (hlaw : ∀ i, Q.map (sample i) = mu)
    (label : X → A) (hlabel : Measurable label) {e : ℝ} (he : 0 < e) :
    Q.real {w | e ≤ ∑ a,
      |mu.real (label ⁻¹' {a}) -
        (empiricalMeasure (fun i => sample i w)).real (label ⁻¹' {a})|} ≤
      2 * Fintype.card A * Real.exp (-2 * m * (e / Fintype.card A) ^ 2) := by
  have hmass (w : Omega) (a : A) := empiricalMeasure_stratum_real_mass
    (fun i => sample i w) (label ⁻¹' {a}) (hlabel (measurableSet_singleton a))
  simpa only [hmass, Set.mem_preimage, Set.mem_singleton_iff, abs_sub_comm] using
    (iid_observational_frequency_tail Q mu hm sample hsample hind hlaw label hlabel he)

-- @node: iid_observational_wasserstein_failure_le
/-- For [a positive sample size m](hyp:hm), assume [measurable
observations](hyp:hsample) that are [independent](hyp:hind) and [each have the
population law](hyp:hlaw), [a measurable categorical label](hyp:hlabel), and
[a measurable carrier S](hyp:hS) with [population mass one](hyp:hmuS).
Given [a nonnegative diameter bound D](hyp:hD), [a nonnegative conditional
error tolerance t](hyp:ht), [a positive frequency tolerance e](hyp:he),
[pairwise distances in S at most D](hyp:hdiam), and [stratum failure bounds
beta](hyp:beta) such that [each stratum's conditional empirical Wasserstein-1
error exceeds t, with both stratum masses nonzero, with probability at most
its beta](hyp:hstratum), [the probability that the full empirical
Wasserstein-1 error exceeds t plus D times e divided by two is at most the
sum of the beta bounds plus twice the number of labels times the exponential
of minus twice m times the squared ratio of e to the number of labels](goal). -/
lemma iid_observational_wasserstein_failure_le
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
    (hstratum : ∀ a, Q {w |
      mu (label ⁻¹' {a}) ≠ 0 ∧
      (empiricalMeasure (fun i => sample i w)) (label ⁻¹' {a}) ≠ 0 ∧
      ¬ wasserstein1 (cond mu (label ⁻¹' {a}))
        (cond (empiricalMeasure (fun i => sample i w)) (label ⁻¹' {a})) ≤ ENNReal.ofReal t}
        ≤ beta a) :
    Q {w | ¬ wasserstein1 mu (empiricalMeasure (fun i => sample i w)) ≤
      ENNReal.ofReal (t + D / 2 * e)} ≤
      ENNReal.ofReal (2 * k * Real.exp (-2 * m * (e / k) ^ 2)) + ∑ a, beta a := by
  classical
  let F : Set Omega := {w | e ≤ ∑ a,
    |mu.real (label ⁻¹' {a}) -
      (empiricalMeasure (fun i => sample i w)).real (label ⁻¹' {a})|}
  let B : Fin k → Set Omega := fun a => {w |
    mu (label ⁻¹' {a}) ≠ 0 ∧
    (empiricalMeasure (fun i => sample i w)) (label ⁻¹' {a}) ≠ 0 ∧
    ¬ wasserstein1 (cond mu (label ⁻¹' {a}))
      (cond (empiricalMeasure (fun i => sample i w)) (label ⁻¹' {a})) ≤ ENNReal.ofReal t}
  have hsupport : ∀ᵐ w ∂Q, ∀ i, sample i w ∈ S := by
    apply ae_all_iff.mpr
    intro i
    have hs : ∀ᵐ x ∂mu, x ∈ S := by
      apply ae_iff.mpr
      change mu Sᶜ = 0
      rw [measure_compl hS (measure_ne_top mu S), measure_univ, hmuS, tsub_self]
    have hsmap : ∀ᵐ x ∂Q.map (sample i), x ∈ S := by rw [hlaw i]; exact hs
    exact (ae_map_iff (hsample i).aemeasurable hS).mp hsmap
  have hsub : ∀ᵐ w ∂Q,
      (¬ wasserstein1 mu (empiricalMeasure (fun i => sample i w)) ≤
        ENNReal.ofReal (t + D / 2 * e)) → w ∈ F ∪ ⋃ a, B a := by
    filter_upwards [hsupport] with w hw
    intro hfail
    by_cases hf : w ∈ F
    · exact Or.inl hf
    by_cases hb : w ∈ ⋃ a, B a
    · exact Or.inr hb
    have hlocal : ∀ a, mu (label ⁻¹' {a}) ≠ 0 →
        (empiricalMeasure (fun i => sample i w)) (label ⁻¹' {a}) ≠ 0 →
        wasserstein1 (cond mu (label ⁻¹' {a}))
          (cond (empiricalMeasure (fun i => sample i w)) (label ⁻¹' {a})) ≤ ENNReal.ofReal t := by
      intro a ha hna
      by_contra h
      exact hb (Set.mem_iUnion.mpr ⟨a, ha, hna, h⟩)
    have hemp : (empiricalMeasure (fun i => sample i w)) S = 1 := by
      rw [empiricalMeasure_stratum_mass _ S hS]
      simp only [hw, Finset.filter_true, Finset.card_univ, Fintype.card_fin]
      exact ENNReal.inv_mul_cancel (by exact_mod_cast hm.ne') (by simp)
    let := empiricalMeasure_probability hm (fun i => sample i w)
    have hW := observational_wasserstein_le_of_stratum_errors mu
      (empiricalMeasure (fun i => sample i w)) label hlabel S hS hmuS hemp D t hdiam hlocal
    have hfreq : (∑ a, |mu.real (label ⁻¹' {a}) -
      (empiricalMeasure (fun i => sample i w)).real (label ⁻¹' {a})|) ≤ e :=
        le_of_lt (lt_of_not_ge hf)
    have herr := mul_le_mul_of_nonneg_left hfreq (div_nonneg hD (by norm_num : (0 : ℝ) ≤ 2))
    exact False.elim (hfail (hW.trans (by
      rw [← ENNReal.ofReal_add ht (mul_nonneg (div_nonneg hD (by norm_num))
        (Finset.sum_nonneg fun _ _ => abs_nonneg _))]
      exact ENNReal.ofReal_le_ofReal (by linarith [herr]))))
  have hf : Q F ≤ ENNReal.ofReal (2 * k * Real.exp (-2 * m * (e / k) ^ 2)) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top Q F)]
    exact ENNReal.ofReal_le_ofReal (by
      simpa [F, Measure.real] using
        iid_empirical_stratum_mass_tail Q mu hm sample hsample hind hlaw label hlabel he)
  exact (measure_mono_ae hsub).trans ((measure_union_le F _).trans
    (add_le_add hf ((measure_iUnion_fintype_le Q B).trans
      (Finset.sum_le_sum fun a _ => hstratum a))))

end Papers.TbsNeuralCausalPi
