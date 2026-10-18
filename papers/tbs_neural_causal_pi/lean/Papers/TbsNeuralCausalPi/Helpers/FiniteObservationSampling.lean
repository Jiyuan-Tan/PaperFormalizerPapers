module
public import Papers.TbsNeuralCausalPi.Helpers.ObservationalSelectedConcentration
/-! # Sampling when categorical labels determine the complete observation

This is the zero-dimensional non-Gumbel latent branch of the observational
sampling argument. Conditional laws are point masses, and the complete-law
error is controlled solely by the actual categorical frequency error.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

-- @node: cond_eq_dirac_of_ae_label_determines
/-- If [the label map is measurable](hyp:hlabel), [an observation almost surely
equals the encoded value of its label](hyp:hdet), and [a given label has nonzero
mass under the finite observation measure](hyp:ha), [the conditional law given
that label is the point mass at its encoded value](goal). -/
lemma cond_eq_dirac_of_ae_label_determines
    {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableSingletonClass A] (mu : Measure X) [IsFiniteMeasure mu]
    (label : X → A) (hlabel : Measurable label) (v : A → X)
    (hdet : ∀ᵐ x ∂mu, x = v (label x)) (a : A)
    (ha : mu (label ⁻¹' {a}) ≠ 0) :
    cond mu (label ⁻¹' {a}) = Measure.dirac (v a) := by
  let := cond_isProbabilityMeasure ha
  have heq : (fun x : X => x) =ᵐ[cond mu (label ⁻¹' {a})] (fun _ => v a) := by
    filter_upwards [cond_absolutelyContinuous.ae_le hdet,
      ae_cond_mem (μ := mu) (hlabel (measurableSet_singleton a))] with x hx hxa
    exact hx.trans (congrArg v hxa)
  calc
    _ = (cond mu (label ⁻¹' {a})).map id := (Measure.map_id).symm
    _ = (cond mu (label ⁻¹' {a})).map (fun _ => v a) := Measure.map_congr heq
    _ = _ := by simp [Measure.map_const]

-- @node: finite_observation_law_eq_map
/-- If [a finite-valued label map is measurable](hyp:hlabel) and [observations
almost surely equal the encoded values of their labels](hyp:hdet), [the
observation measure equals the label measure pushed through the encoding](goal). -/
lemma finite_observation_law_eq_map
    {X : Type*} [MeasurableSpace X] {k : ℕ}
    (mu : Measure X) (label : X → Fin k) (hlabel : Measurable label)
    (v : Fin k → X) (hdet : ∀ᵐ x ∂mu, x = v (label x)) :
    mu = (mu.map label).map v := by
  rw [Measure.map_map (measurable_of_countable v) hlabel]
  exact (Measure.map_id).symm.trans (Measure.map_congr hdet)

-- @node: finite_observation_empirical_wasserstein_le
/-- Suppose [a finite-valued label map is measurable](hyp:hlabel), [population
observations almost surely equal their encoded labels](hyp:hdet), [the sample
size is positive](hyp:hm), [each sample observation equals its encoded label](hyp:hx),
and [all encoded values are at pairwise distance at most D](hyp:hdiam). Then
[the Wasserstein distance between the population and empirical observation laws
is at most D divided by two times the sum of absolute population versus empirical
label-probability differences](goal). -/
lemma finite_observation_empirical_wasserstein_le
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {k m : ℕ}
    (mu : Measure X) [IsProbabilityMeasure mu]
    (label : X → Fin k) (hlabel : Measurable label) (v : Fin k → X)
    (hdet : ∀ᵐ x ∂mu, x = v (label x)) (hm : 0 < m) (x : Fin m → X)
    (hx : ∀ i, x i = v (label (x i))) (D : ℝ)
    (hdiam : ∀ i j, dist (v i) (v j) ≤ D) :
    wasserstein1 mu (empiricalMeasure x) ≤ ENNReal.ofReal (D / 2 *
      ∑ a, |mu.real (label ⁻¹' {a}) - (empiricalMeasure x).real (label ⁻¹' {a})|) := by
  let := empiricalMeasure_probability hm x
  let := Measure.isProbabilityMeasure_map (μ := mu) hlabel.aemeasurable
  let := empiricalMeasure_probability hm (fun i => label (x i))
  have hex : empiricalMeasure x =
      (empiricalMeasure (fun i => label (x i))).map v := by
    rw [empiricalMeasure_map_eq _ v (measurable_of_countable v)]
    congr 1
    exact funext hx
  have hpop := finite_observation_law_eq_map mu label hlabel v hdet
  have hmass (a : Fin k) : (mu.map label).real {a} = mu.real (label ⁻¹' {a}) := by
    rw [Measure.real, Measure.map_apply hlabel (measurableSet_singleton a)]
    rfl
  have hemp (a : Fin k) :
      (empiricalMeasure (fun i => label (x i))).real {a} =
        (empiricalMeasure x).real (label ⁻¹' {a}) := by
    rw [← empiricalMeasure_map_eq x label hlabel, Measure.real,
      Measure.map_apply hlabel (measurableSet_singleton a)]
    rfl
  calc
    _ = wasserstein1 ((mu.map label).map v)
        ((empiricalMeasure (fun i => label (x i))).map v) := congrArg₂ wasserstein1 hpop hex
    _ ≤ _ := by
      rw [finite_table_map_eq _ v, finite_table_map_eq _ v]
      simpa only [hmass, hemp] using categorical_wasserstein_half_l1_le
        (finite_type_masses_simplex (mu.map label))
        (finite_type_masses_simplex (empiricalMeasure (fun i => label (x i)))) v D hdiam

-- @node: iid_finite_observation_wasserstein_tail
/-- Suppose [the sample size m is positive](hyp:hm), [each observation is a
measurable random variable](hyp:hsample), [the observations are mutually independent](hyp:hind),
and [each has the population law](hyp:hlaw). If [the finite-valued label map is
measurable](hyp:hlabel), [population observations almost surely equal their
encoded labels](hyp:hdet), [D is nonnegative](hyp:hD), [e is positive](hyp:he),
and [encoded observations have pairwise distance at most D](hyp:hdiam), then
[the probability that the empirical Wasserstein error exceeds D e divided by
two is at most 2k exp(−2m(e/k)²), where k is the number of labels](goal). -/
lemma iid_finite_observation_wasserstein_tail
    {Omega X : Type*} [MeasurableSpace Omega] [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] {k m : ℕ} [Nonempty (Fin k)]
    (Q : Measure Omega) [IsProbabilityMeasure Q] (mu : Measure X) [IsProbabilityMeasure mu]
    (hm : 0 < m) (sample : Fin m → Omega → X)
    (hsample : ∀ i, Measurable (sample i)) (hind : iIndepFun sample Q)
    (hlaw : ∀ i, Q.map (sample i) = mu)
    (label : X → Fin k) (hlabel : Measurable label) (v : Fin k → X)
    (hdet : ∀ᵐ x ∂mu, x = v (label x)) (D e : ℝ) (hD : 0 ≤ D) (he : 0 < e)
    (hdiam : ∀ i j, dist (v i) (v j) ≤ D) :
    Q {w | ¬ wasserstein1 mu (empiricalMeasure (fun i => sample i w)) ≤
      ENNReal.ofReal (D / 2 * e)} ≤
        ENNReal.ofReal (2 * k * Real.exp (-2 * m * (e / k)^2)) := by
  have hmeas : MeasurableSet {x : X | x = v (label x)} := by
    have heq : {x : X | x = v (label x)} =
        ⋃ a, (label ⁻¹' {a}) ∩ {v a} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff,
        Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hx
        exact ⟨label x, rfl, hx⟩
      · rintro ⟨a, ha, hx⟩
        simpa only [ha] using hx
    rw [heq]
    exact MeasurableSet.iUnion fun a =>
      (hlabel (measurableSet_singleton a)).inter (measurableSet_singleton (v a))
  have hsdet : ∀ᵐ w ∂Q, ∀ i, sample i w = v (label (sample i w)) := by
    apply ae_all_iff.mpr
    intro i
    apply (ae_map_iff (hsample i).aemeasurable hmeas).mp
    rw [hlaw i]
    exact hdet
  have hsub : ∀ᵐ w ∂Q,
      (¬ wasserstein1 mu (empiricalMeasure (fun i => sample i w)) ≤
        ENNReal.ofReal (D / 2 * e)) →
      e ≤ ∑ a, |mu.real (label ⁻¹' {a}) -
        (empiricalMeasure (fun i => sample i w)).real (label ⁻¹' {a})| := by
    filter_upwards [hsdet] with w hw
    intro hbad
    by_contra hfreq
    have hW := finite_observation_empirical_wasserstein_le mu label hlabel v hdet hm
      (fun i => sample i w) hw D hdiam
    exact hbad (hW.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (le_of_not_ge hfreq) (by positivity))))
  apply (measure_mono_ae hsub).trans
  change Q {w | e ≤ ∑ a, |mu.real (label ⁻¹' {a}) -
    (empiricalMeasure (fun i => sample i w)).real (label ⁻¹' {a})|} ≤ _
  rw [← ENNReal.ofReal_toReal (measure_ne_top Q _)]
  apply ENNReal.ofReal_le_ofReal
  simpa only [Measure.real, Fintype.card_fin] using
    iid_empirical_stratum_mass_tail Q mu hm sample hsample hind hlaw label hlabel he

-- @node: iid_finite_observation_wasserstein_polynomial_tail
/-- Suppose [the sample size m exceeds one](hyp:hm), [each observation is
measurable](hyp:hsample), [the observations are mutually independent](hyp:hind),
and [each has the population law](hyp:hlaw). If [the finite-valued label map is
measurable](hyp:hlabel), [population observations almost surely equal their
encoded labels](hyp:hdet), [D is nonnegative](hyp:hD), and [encoded values have
pairwise distance at most D](hyp:hdiam), then [the probability that the empirical
Wasserstein error exceeds (D/2) k √(2 log(m)/m) is at most 2k/m⁴, where k is the
number of labels](goal). -/
lemma iid_finite_observation_wasserstein_polynomial_tail
    {Omega X : Type*} [MeasurableSpace Omega] [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] {k m : ℕ} [Nonempty (Fin k)]
    (Q : Measure Omega) [IsProbabilityMeasure Q] (mu : Measure X) [IsProbabilityMeasure mu]
    (hm : 1 < m) (sample : Fin m → Omega → X)
    (hsample : ∀ i, Measurable (sample i)) (hind : iIndepFun sample Q)
    (hlaw : ∀ i, Q.map (sample i) = mu)
    (label : X → Fin k) (hlabel : Measurable label) (v : Fin k → X)
    (hdet : ∀ᵐ x ∂mu, x = v (label x)) (D : ℝ) (hD : 0 ≤ D)
    (hdiam : ∀ i j, dist (v i) (v j) ≤ D) :
    Q {w | ¬ wasserstein1 mu (empiricalMeasure (fun i => sample i w)) ≤
      ENNReal.ofReal (D / 2 * (k * Real.sqrt (2 * Real.log m / m)))} ≤
        ENNReal.ofReal (2 * k / (m : ℝ)^4) := by
  have hmR : (1 : ℝ) < m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hkN : 0 < k := by simpa only [Fintype.card_fin] using Fintype.card_pos (α := Fin k)
  have hk : (0 : ℝ) < k := Nat.cast_pos.mpr hkN
  have hlog : 0 < Real.log m := Real.log_pos hmR
  have hrad : 0 < 2 * Real.log m / m := by positivity
  have he : 0 < (k : ℝ) * Real.sqrt (2 * Real.log m / m) := by positivity
  have htail := iid_finite_observation_wasserstein_tail Q mu (by omega) sample hsample hind
    hlaw label hlabel v hdet D _ hD he hdiam
  have hcancel : ((k : ℝ) * Real.sqrt (2 * Real.log m / m)) / k =
      Real.sqrt (2 * Real.log m / m) := by field_simp
  have hexp : Real.exp (-2 * m * (((k : ℝ) * Real.sqrt (2 * Real.log m / m)) / k)^2) =
      ((m : ℝ)^4)⁻¹ := by
    rw [hcancel, Real.sq_sqrt hrad.le]
    have halg : -2 * (m : ℝ) * (2 * Real.log m / m) = -(4 * Real.log m) := by
      field_simp
      ring
    rw [halg, Real.exp_neg, show (4 : ℝ) * Real.log m = (4 : ℕ) * Real.log m by norm_num,
      Real.exp_nat_mul, Real.exp_log hmpos]
  rw [hexp] at htail
  simpa only [div_eq_mul_inv] using htail

end Papers.TbsNeuralCausalPi
