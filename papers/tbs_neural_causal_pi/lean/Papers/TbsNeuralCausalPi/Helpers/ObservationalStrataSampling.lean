module
public import Papers.TbsNeuralCausalPi.Helpers.ObservationalMixtureTransport
public import Toolkit.Foundations.Probability.Independence.ProductConditioning
public import Toolkit.Foundations.Probability.Conditioning.ConditioningOnEvent
/-! # IID sampling conditional on the complete categorical pattern

Conditioning independent observations on all their categorical labels preserves
independence, with the normalized conditional law in each coordinate. In
particular, the observations in one stratum form an IID sample, although the
coordinates inside each observation need not be independent.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- If [each observation is measurable](hyp:hsample), [the observations are independent](hyp:hind),
[each has population law mu](hyp:hlaw), and [the categorical label is measurable](hyp:hlabel),
then [the probability of any complete label pattern equals the product of its population category probabilities](goal). -/
-- @node: iid_label_pattern_probability
lemma iid_label_pattern_probability
    {Omega X I A : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
    [MeasurableSpace A] [Fintype I] [MeasurableSingletonClass A]
    (Q : Measure Omega) [IsProbabilityMeasure Q] (mu : Measure X)
    [IsProbabilityMeasure mu]
    (sample : I → Omega → X) (hsample : ∀ i, Measurable (sample i))
    (hind : iIndepFun sample Q) (hlaw : ∀ i, Q.map (sample i) = mu)
    (label : X → A) (hlabel : Measurable label) (c : I → A) :
    Q {w | ∀ i, label (sample i w) = c i} = ∏ i, mu (label ⁻¹' {c i}) := by
  have hjoint : Q.map (fun w i => sample i w) = Measure.pi (fun _ : I => mu) := by
    rw [hind.map_fun_eq_pi_map (fun i => (hsample i).aemeasurable)]
    simp_rw [hlaw]
  have hrect : MeasurableSet (Set.univ.pi (fun i => label ⁻¹' {c i})) :=
    MeasurableSet.univ_pi (fun i => hlabel (measurableSet_singleton _))
  calc
    _ = (Q.map (fun w i => sample i w)) (Set.univ.pi (fun i => label ⁻¹' {c i})) := by
      rw [Measure.map_apply (by fun_prop) hrect]
      congr 1
      ext w
      simp
    _ = _ := by rw [hjoint, Measure.pi_pi]

/-- If [each observation is measurable](hyp:hsample), [the observations are independent](hyp:hind),
[each has population law mu](hyp:hlaw), [the label is measurable](hyp:hlabel), and
[the specified complete label pattern has positive probability](hyp:hpos), then
[the joint law conditional on that pattern is the product of the corresponding population category-conditional laws](goal). -/
-- @node: iid_label_pattern_conditional_law
lemma iid_label_pattern_conditional_law
    {Omega X I A : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
    [MeasurableSpace A] [Fintype I] [MeasurableSingletonClass A]
    (Q : Measure Omega) [IsProbabilityMeasure Q] (mu : Measure X)
    [IsProbabilityMeasure mu]
    (sample : I → Omega → X) (hsample : ∀ i, Measurable (sample i))
    (hind : iIndepFun sample Q) (hlaw : ∀ i, Q.map (sample i) = mu)
    (label : X → A) (hlabel : Measurable label) (c : I → A)
    (hpos : Q {w | ∀ i, label (sample i w) = c i} ≠ 0) :
    (cond Q {w | ∀ i, label (sample i w) = c i}).map (fun w i => sample i w) =
      Measure.pi (fun i => cond mu (label ⁻¹' {c i})) := by
  have hjoint : Q.map (fun w i => sample i w) = Measure.pi (fun _ : I => mu) := by
    rw [hind.map_fun_eq_pi_map (fun i => (hsample i).aemeasurable)]
    simp_rw [hlaw]
  have hrect : MeasurableSet (Set.univ.pi (fun i => label ⁻¹' {c i})) :=
    MeasurableSet.univ_pi (fun i => hlabel (measurableSet_singleton _))
  have hpre : {w | ∀ i, label (sample i w) = c i} =
      (fun w i => sample i w) ⁻¹' Set.univ.pi (fun i => label ⁻¹' {c i}) := by
    ext w
    simp
  have hmarg : ∀ i, mu (label ⁻¹' {c i}) ≠ 0 := by
    rw [iid_label_pattern_probability Q mu sample hsample hind hlaw label hlabel c] at hpos
    exact fun i => (Finset.prod_ne_zero_iff.mp hpos) i (Finset.mem_univ i)
  rw [hpre, Toolkit.Foundations.Probability.Conditioning.map_cond_preimage Q _
    (by fun_prop) _ hrect, hjoint]
  exact Toolkit.Foundations.Probability.Independence.cond_pi_univ_pi _ _
    (fun i => hlabel (measurableSet_singleton _)) hmarg

/-- If [each observation is measurable](hyp:hsample), [the observations are independent](hyp:hind),
[each has population law mu](hyp:hlaw), [the label is measurable](hyp:hlabel), and
[the specified complete label pattern has positive probability](hyp:hpos), then
[the conditional law of any selected observation is the population law conditional on its specified category](goal). -/
-- @node: iid_label_pattern_conditional_marginal
lemma iid_label_pattern_conditional_marginal
    {Omega X I A : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
    [MeasurableSpace A] [Fintype I] [MeasurableSingletonClass A]
    (Q : Measure Omega) [IsProbabilityMeasure Q] (mu : Measure X)
    [IsProbabilityMeasure mu]
    (sample : I → Omega → X) (hsample : ∀ i, Measurable (sample i))
    (hind : iIndepFun sample Q) (hlaw : ∀ i, Q.map (sample i) = mu)
    (label : X → A) (hlabel : Measurable label) (c : I → A)
    (hpos : Q {w | ∀ i, label (sample i w) = c i} ≠ 0) (i : I) :
    (cond Q {w | ∀ j, label (sample j w) = c j}).map (sample i) =
      cond mu (label ⁻¹' {c i}) := by
  have hmarg : ∀ j, mu (label ⁻¹' {c j}) ≠ 0 := by
    rw [iid_label_pattern_probability Q mu sample hsample hind hlaw label hlabel c] at hpos
    exact fun j => (Finset.prod_ne_zero_iff.mp hpos) j (Finset.mem_univ j)
  let (j : I) : IsProbabilityMeasure (cond mu (label ⁻¹' {c j})) :=
    cond_isProbabilityMeasure (hmarg j)
  have h := congrArg (fun nu : Measure (I → X) => nu.map (Function.eval i))
    (iid_label_pattern_conditional_law Q mu sample hsample hind hlaw label hlabel c hpos)
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    (measurePreserving_eval (fun j => cond mu (label ⁻¹' {c j})) i).map_eq] at h
  exact h

/-- If [each observation is measurable](hyp:hsample), [the observations are independent](hyp:hind),
[each has population law mu](hyp:hlaw), [the label is measurable](hyp:hlabel), and
[the specified complete label pattern has positive probability](hyp:hpos), then
[the observations remain independent conditional on that pattern](goal). -/
-- @node: iid_label_pattern_conditional_independent
lemma iid_label_pattern_conditional_independent
    {Omega X I A : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
    [MeasurableSpace A] [Fintype I] [MeasurableSingletonClass A]
    (Q : Measure Omega) [IsProbabilityMeasure Q] (mu : Measure X)
    [IsProbabilityMeasure mu]
    (sample : I → Omega → X) (hsample : ∀ i, Measurable (sample i))
    (hind : iIndepFun sample Q) (hlaw : ∀ i, Q.map (sample i) = mu)
    (label : X → A) (hlabel : Measurable label) (c : I → A)
    (hpos : Q {w | ∀ i, label (sample i w) = c i} ≠ 0) :
    iIndepFun sample (cond Q {w | ∀ i, label (sample i w) = c i}) := by
  let := cond_isProbabilityMeasure hpos
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hsample i).aemeasurable)).mpr
  rw [iid_label_pattern_conditional_law Q mu sample hsample hind hlaw label hlabel c hpos]
  congr 1
  funext i
  exact (iid_label_pattern_conditional_marginal Q mu sample hsample hind hlaw
    label hlabel c hpos i).symm

/-- Suppose [each observation is measurable](hyp:hsample), [the observations are independent](hyp:hind),
[each has population law mu](hyp:hlaw), [the label is measurable](hyp:hlabel), and
[the specified complete label pattern has positive probability](hyp:hpos).
If [the selected indices have no repetitions](hyp:he) and [all have category a in that pattern](hyp:hc),
then [their joint conditional law is the product of copies of the population law conditional on category a](goal). -/
-- @node: iid_stratum_subsample_conditional_law
lemma iid_stratum_subsample_conditional_law
    {Omega X I A J : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
    [MeasurableSpace A] [Fintype I] [Fintype J] [MeasurableSingletonClass A]
    (Q : Measure Omega) [IsProbabilityMeasure Q] (mu : Measure X)
    [IsProbabilityMeasure mu]
    (sample : I → Omega → X) (hsample : ∀ i, Measurable (sample i))
    (hind : iIndepFun sample Q) (hlaw : ∀ i, Q.map (sample i) = mu)
    (label : X → A) (hlabel : Measurable label) (c : I → A)
    (hpos : Q {w | ∀ i, label (sample i w) = c i} ≠ 0)
    (a : A) (e : J → I) (he : Function.Injective e) (hc : ∀ j, c (e j) = a) :
    (cond Q {w | ∀ i, label (sample i w) = c i}).map (fun w j => sample (e j) w) =
      Measure.pi (fun _ : J => cond mu (label ⁻¹' {a})) := by
  have hi := (iid_label_pattern_conditional_independent Q mu sample hsample hind hlaw
    label hlabel c hpos).precomp he
  rw [hi.map_fun_eq_pi_map (fun j => (hsample (e j)).aemeasurable)]
  congr 1
  funext j
  rw [iid_label_pattern_conditional_marginal Q mu sample hsample hind hlaw
    label hlabel c hpos, hc j]

/-- Suppose [each observation is measurable](hyp:hsample), [the observations are independent](hyp:hind),
[each has population law mu](hyp:hlaw), [the label is measurable](hyp:hlabel), and
[the specified complete label pattern has positive probability](hyp:hpos).
If [category a has positive population probability](hyp:ha), [the selected indices have no repetitions](hyp:he),
[all selected indices have category a in the pattern](hyp:hc), and [the latent projection is measurable](hyp:hlatent),
then [the selected latent values have joint conditional law equal to the product of their category-conditional latent laws](goal). -/
-- @node: iid_stratum_latent_subsample_conditional_law
lemma iid_stratum_latent_subsample_conditional_law
    {Omega X Z I A J : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
    [MeasurableSpace Z] [MeasurableSpace A] [Fintype I] [Fintype J]
    [MeasurableSingletonClass A]
    (Q : Measure Omega) [IsProbabilityMeasure Q] (mu : Measure X)
    [IsProbabilityMeasure mu]
    (sample : I → Omega → X) (hsample : ∀ i, Measurable (sample i))
    (hind : iIndepFun sample Q) (hlaw : ∀ i, Q.map (sample i) = mu)
    (label : X → A) (hlabel : Measurable label) (c : I → A)
    (hpos : Q {w | ∀ i, label (sample i w) = c i} ≠ 0)
    (a : A) (ha : mu (label ⁻¹' {a}) ≠ 0)
    (e : J → I) (he : Function.Injective e) (hc : ∀ j, c (e j) = a)
    (latent : X → Z) (hlatent : Measurable latent) :
    (cond Q {w | ∀ i, label (sample i w) = c i}).map
        (fun w j => latent (sample (e j) w)) =
      Measure.pi (fun _ : J => (cond mu (label ⁻¹' {a})).map latent) := by
  let := cond_isProbabilityMeasure ha
  let : IsProbabilityMeasure ((cond mu (label ⁻¹' {a})).map latent) :=
    Measure.isProbabilityMeasure_map hlatent.aemeasurable
  have h := congrArg (fun nu : Measure (J → X) =>
    nu.map (fun x j => latent (x j)))
    (iid_stratum_subsample_conditional_law Q mu sample hsample hind hlaw
      label hlabel c hpos a e he hc)
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.pi_map_pi (fun _ => hlatent.aemeasurable)] at h
  exact h

/-- Suppose [each observation is measurable](hyp:hsample), [the observations are independent](hyp:hind),
[each has population law mu](hyp:hlaw), [the label is measurable](hyp:hlabel), and
[the specified complete label pattern has positive probability](hyp:hpos).
If [the selected indices have no repetitions](hyp:he), [all have category a in the pattern](hyp:hc),
and [the selected-sample event B is measurable](hyp:hB), then
[its probability conditional on the pattern equals its probability under independent draws from the population law conditional on category a](goal). -/
-- @node: iid_stratum_conditional_event_probability
lemma iid_stratum_conditional_event_probability
    {Omega X I A J : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
    [MeasurableSpace A] [Fintype I] [Fintype J] [MeasurableSingletonClass A]
    (Q : Measure Omega) [IsProbabilityMeasure Q] (mu : Measure X)
    [IsProbabilityMeasure mu]
    (sample : I → Omega → X) (hsample : ∀ i, Measurable (sample i))
    (hind : iIndepFun sample Q) (hlaw : ∀ i, Q.map (sample i) = mu)
    (label : X → A) (hlabel : Measurable label) (c : I → A)
    (hpos : Q {w | ∀ i, label (sample i w) = c i} ≠ 0)
    (a : A) (e : J → I) (he : Function.Injective e) (hc : ∀ j, c (e j) = a)
    (B : Set (J → X)) (hB : MeasurableSet B) :
    (cond Q {w | ∀ i, label (sample i w) = c i})
        {w | (fun j => sample (e j) w) ∈ B} =
      (Measure.pi (fun _ : J => cond mu (label ⁻¹' {a}))) B := by
  rw [← iid_stratum_subsample_conditional_law Q mu sample hsample hind hlaw
    label hlabel c hpos a e he hc, Measure.map_apply (by fun_prop) hB]
  rfl

/-- If [each observation is measurable](hyp:hsample), [each has population law mu](hyp:hlaw),
[the label is measurable](hyp:hlabel), and [category a has zero population probability](hyp:ha),
then [almost surely no observation in the finite sample has category a](goal). -/
-- @node: zero_probability_category_absent_ae
lemma zero_probability_category_absent_ae
    {Omega X I A : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
    [MeasurableSpace A] [Finite I] [MeasurableSingletonClass A]
    (Q : Measure Omega) (mu : Measure X)
    (sample : I → Omega → X) (hsample : ∀ i, Measurable (sample i))
    (hlaw : ∀ i, Q.map (sample i) = mu)
    (label : X → A) (hlabel : Measurable label) (a : A)
    (ha : mu (label ⁻¹' {a}) = 0) :
    ∀ᵐ w ∂Q, ∀ i, label (sample i w) ≠ a := by
  apply (ae_all_iff).mpr
  intro i
  apply ae_iff.mpr
  have h := congrArg (fun nu : Measure X => nu (label ⁻¹' {a})) (hlaw i)
  rw [Measure.map_apply (hsample i) (hlabel (measurableSet_singleton a)), ha] at h
  simpa only [Set.preimage, Set.mem_singleton_iff, Set.mem_setOf_eq, not_not] using h

/-- For [a sample of positive size](hyp:hm) and [a measurable stratum S](hyp:hS),
if [the selected indices have no repetitions](hyp:he) and [cover exactly the observations in S](hyp:hcover),
then [the empirical law conditional on S equals the empirical law of the selected observations](goal).

An empty selection gives zero on both sides. -/
-- @node: empiricalMeasure_cond_eq_selected
lemma empiricalMeasure_cond_eq_selected
    {X : Type*} [MeasurableSpace X] {m N : ℕ} (hm : 0 < m)
    (x : Fin m → X) (S : Set X) (hS : MeasurableSet S)
    (e : Fin N → Fin m) (he : Function.Injective e)
    (hcover : ∀ i, x i ∈ S ↔ ∃ j, e j = i) :
    cond (empiricalMeasure x) S = empiricalMeasure (fun j => x (e j)) := by
  classical
  have hsum : (∑ j, Measure.dirac (x (e j))) =
      ∑ i ∈ Finset.univ.filter (fun i => x i ∈ S), Measure.dirac (x i) := by
    apply Finset.sum_bij (fun j _ => e j)
    · intro j _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hcover (e j)).mpr ⟨j, rfl⟩
    · intro i _ j _ h
      exact he h
    · intro i hi
      obtain ⟨j, hj⟩ := (hcover i).mp (Finset.mem_filter.mp hi).2
      exact ⟨j, Finset.mem_univ _, hj⟩
    · intro j _
      rfl
  have hrestrict : (empiricalMeasure x).restrict S =
      (m : ℝ≥0∞)⁻¹ • ∑ j, Measure.dirac (x (e j)) := by
    rw [empiricalMeasure, Measure.restrict_smul, hsum]
    congr 1
    ext T hT
    simp only [Measure.restrict_apply hT, Measure.finsetSum_apply,
      Measure.dirac_apply' _ (hT.inter hS), Measure.dirac_apply' _ hT]
    simp [Finset.sum_filter, Set.indicator, and_comm, Finset.filter_filter]
  have hmass : (empiricalMeasure x) S = (m : ℝ≥0∞)⁻¹ * N := by
    have h := congrArg (fun nu : Measure X => nu Set.univ) hrestrict
    simpa only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Measure.smul_apply, Measure.finsetSum_apply, measure_univ, smul_eq_mul,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] using h
  rw [ProbabilityTheory.cond, hmass, hrestrict, smul_smul, empiricalMeasure]
  congr 1
  have hm0 : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast hm.ne'
  rw [ENNReal.mul_inv (by simp) (by simp [hm0]), inv_inv]
  calc
    _ = (N : ℝ≥0∞)⁻¹ * ((m : ℝ≥0∞) * (m : ℝ≥0∞)⁻¹) := by ac_rfl
    _ = _ := by rw [ENNReal.mul_inv_cancel (by exact_mod_cast hm.ne') (by simp), mul_one]

end Papers.TbsNeuralCausalPi
