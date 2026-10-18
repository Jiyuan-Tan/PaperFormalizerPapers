module
public import Papers.TbsNeuralCausalPi.Helpers.ObservationalSelectedConcentration
public import Papers.TbsNeuralCausalPi.Helpers.WassersteinBounds
/-! # Conditional latent sampling through the fixed-label observation maps

A conditional joint latent law need not be a product over latent coordinates.
Only the observations are independent. On a compact latent domain, a Lipschitz
fixed-label observation map transfers its empirical Wasserstein tail to the
complete observed stratum. Combining these transfers with the actual label
counts leaves only the latent empirical concentration estimate to prove.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

-- @node: fixed_label_conditional_observation_law
/-- Suppose [the observation map is measurable](hyp:hobserved), [the latent
map is measurable](hyp:hlatent), [the label is measurable](hyp:hlabel), and
[each fixed-label reconstruction map is measurable](hyp:hphi), with [the
observation almost surely equal to the reconstruction from its label and
latent value](hyp:hdet). [Conditioning the observed law on label a gives the
same measure as conditioning the original law on that observed label,
taking its latent marginal, and applying the reconstruction map for a](goal). -/
lemma fixed_label_conditional_observation_law
    {Omega X Z A : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
    [MeasurableSpace Z] [MeasurableSpace A] [MeasurableSingletonClass A]
    (Q : Measure Omega) [IsProbabilityMeasure Q]
    (observed : Omega → X) (latent : Omega → Z)
    (hobserved : Measurable observed) (hlatent : Measurable latent)
    (label : X → A) (hlabel : Measurable label)
    (phi : A → Z → X) (hphi : ∀ a, Measurable (phi a))
    (hdet : ∀ᵐ w ∂Q, observed w = phi (label (observed w)) (latent w)) (a : A) :
    cond (Q.map observed) (label ⁻¹' {a}) =
      ((cond Q ((label ∘ observed) ⁻¹' {a})).map latent).map (phi a) := by
  have hcell : MeasurableSet (label ⁻¹' {a}) := hlabel (measurableSet_singleton a)
  have hcellQ : MeasurableSet ((label ∘ observed) ⁻¹' {a}) :=
    hcell.preimage hobserved
  have heq : observed =ᵐ[cond Q ((label ∘ observed) ⁻¹' {a})] phi a ∘ latent := by
    filter_upwards [cond_absolutelyContinuous.ae_le hdet,
      ae_cond_mem (μ := Q) hcellQ] with w hw hwa
    change label (observed w) = a at hwa
    simpa only [hwa, Function.comp_apply] using hw
  calc
    _ = (cond Q ((label ∘ observed) ⁻¹' {a})).map observed := by
      exact (Toolkit.Foundations.Probability.Conditioning.map_cond_preimage
        Q observed hobserved (label ⁻¹' {a}) hcell).symm
    _ = (cond Q ((label ∘ observed) ⁻¹' {a})).map (phi a ∘ latent) :=
      Measure.map_congr heq
    _ = _ := (Measure.map_map (hphi a) hlatent).symm

-- @node: fixed_label_conditional_latent_probability
/-- If [the observation map is measurable](hyp:hobserved), [the latent map
is measurable](hyp:hlatent), [the label is measurable](hyp:hlabel), and [the
observed label a has nonzero probability](hyp:ha), [the latent marginal of
the original law conditioned on that observed label is a probability
measure](goal). -/
lemma fixed_label_conditional_latent_probability
    {Omega X Z A : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
    [MeasurableSpace Z] [MeasurableSpace A] [MeasurableSingletonClass A]
    (Q : Measure Omega) [IsProbabilityMeasure Q]
    (observed : Omega → X) (latent : Omega → Z)
    (hobserved : Measurable observed) (hlatent : Measurable latent)
    (label : X → A) (hlabel : Measurable label) (a : A)
    (ha : (Q.map observed) (label ⁻¹' {a}) ≠ 0) :
    IsProbabilityMeasure ((cond Q ((label ∘ observed) ⁻¹' {a})).map latent) := by
  have hpos : Q ((label ∘ observed) ⁻¹' {a}) ≠ 0 := by
    simpa only [Measure.map_apply hobserved (hlabel (measurableSet_singleton a)),
      Set.preimage_comp] using ha
  let := cond_isProbabilityMeasure hpos
  exact Measure.isProbabilityMeasure_map hlatent.aemeasurable

-- @node: compact_empirical_pushforward_wasserstein_le
/-- On a compact latent domain, for [a positive sample size](hyp:hN),
[a nonnegative constant L](hyp:L), and [a map f with Lipschitz constant
L](hyp:hf), [the Wasserstein-1 distance between the pushed-forward population
law and the empirical law of the transformed draws is at most L times the
original population-to-empirical Wasserstein-1 distance](goal). -/
lemma compact_empirical_pushforward_wasserstein_le
    {X Y : Type*} [MetricSpace X] [CompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] [MetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (mu : Measure X) [IsProbabilityMeasure mu] {N : ℕ} (hN : 0 < N)
    (x : Fin N → X) (f : X → Y) (L : ℝ≥0) (hf : LipschitzWith L f) :
    wasserstein1 (mu.map f) (empiricalMeasure (fun j => f (x j))) ≤
      (L : ℝ≥0∞) * wasserstein1 mu (empiricalMeasure x) := by
  have hfm : Measurable f := by
    first | fun_prop | exact hf.continuous.measurable
  let := empiricalMeasure_probability hN x
  rw [← empiricalMeasure_map_eq x f hfm]
  have h := PushForward.map_le_of_compact_range mu (empiricalMeasure x)
    f f hfm hfm L hf 0 (by intro z; simp)
    (Set.range f) (isCompact_range hf.continuous)
    (fun z => Set.mem_range_self z) (fun z => Set.mem_range_self z)
  simpa only [add_zero] using h

-- @node: compact_pushforward_empirical_failure_le
/-- On a compact latent domain, given [a positive sample size](hyp:hN),
[a nonnegative constant L](hyp:L), [a map f with Lipschitz constant L](hyp:hf),
[tolerances satisfying L times s at most t](hyp:hst), and [a measurable
transformed empirical Wasserstein-1 failure event at tolerance t](hyp:hB),
[the failure probability for independent draws from the pushed-forward law
at tolerance t is at most the failure probability for independent latent draws
at tolerance s](goal). -/
lemma compact_pushforward_empirical_failure_le
    {X Y : Type*} [MetricSpace X] [CompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] [MetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (mu : Measure X) [IsProbabilityMeasure mu] {N : ℕ} (hN : 0 < N)
    (f : X → Y) (L : ℝ≥0) (hf : LipschitzWith L f) (s t : ℝ)
    (hst : (L : ℝ) * s ≤ t)
    (hB : MeasurableSet {y : Fin N → Y |
      ¬ wasserstein1 (mu.map f) (empiricalMeasure y) ≤ ENNReal.ofReal t}) :
    (Measure.pi (fun _ : Fin N => mu.map f))
      {y | ¬ wasserstein1 (mu.map f) (empiricalMeasure y) ≤ ENNReal.ofReal t} ≤
    (Measure.pi (fun _ : Fin N => mu))
      {x | ¬ wasserstein1 mu (empiricalMeasure x) ≤ ENNReal.ofReal s} := by
  have hfm : Measurable f := by
    first | fun_prop | exact hf.continuous.measurable
  rw [← Measure.pi_map_pi (fun _ : Fin N => hfm.aemeasurable),
    Measure.map_apply (by fun_prop) hB]
  apply measure_mono
  intro x hx hgood
  apply hx
  have hscaled : (L : ℝ≥0∞) * wasserstein1 mu (empiricalMeasure x) ≤
      (L : ℝ≥0∞) * ENNReal.ofReal s := by gcongr
  apply ((compact_empirical_pushforward_wasserstein_le mu hN x f L hf).trans hscaled).trans
  rw [show (L : ℝ≥0∞) = ENNReal.ofReal (L : ℝ) by simp,
    ← ENNReal.ofReal_mul L.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal hst

-- @node: iid_observational_wasserstein_failure_le_of_latent_tails
/-- For [a positive sample size m](hyp:hm), assume [measurable
observations](hyp:hsample) that are [independent](hyp:hind) and [each have the
population law](hyp:hlaw), [a measurable categorical label](hyp:hlabel),
[a measurable carrier S](hyp:hS) with [population mass one](hyp:hmuS),
[a nonnegative diameter bound D](hyp:hD), [a nonnegative observed tolerance
t](hyp:ht), [a positive frequency tolerance e](hyp:he), and [pairwise distances
in S at most D](hyp:hdiam). Given [nonnegative stratum Lipschitz constants
L](hyp:L), [reconstruction maps with those constants](hyp:hphi), [positive-mass
conditional observed laws obtained by pushing forward the stratum latent
laws](hyp:hcond), [latent tolerances whose products with L are at most
t](hyp:hst), [stratum tail bounds beta](hyp:beta), [measurable conditional
observed failure events for all sample sizes](hyp:hB), and [latent empirical
failure probabilities bounded by beta whenever the count is at least half its
expected value](hyp:hbound), [the probability that the full empirical
Wasserstein-1 error exceeds t plus D times e divided by two is at most the
categorical frequency bound plus, over positive-mass labels, the small-count
bound and beta: the frequency bound is twice the number of labels times the
exponential of minus twice m times the squared ratio of e to the number of
labels, and each small-count bound replaces e by half the label's population
probability](goal). -/
lemma iid_observational_wasserstein_failure_le_of_latent_tails
    {Omega X Z : Type*} [MeasurableSpace Omega] [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Z] [CompactSpace Z] [SecondCountableTopology Z]
    [MeasurableSpace Z] [BorelSpace Z] {k m : ℕ} [Nonempty (Fin k)]
    (Q : Measure Omega) [IsProbabilityMeasure Q] (mu : Measure X) [IsProbabilityMeasure mu]
    (hm : 0 < m) (sample : Fin m → Omega → X)
    (hsample : ∀ i, Measurable (sample i)) (hind : iIndepFun sample Q)
    (hlaw : ∀ i, Q.map (sample i) = mu)
    (label : X → Fin k) (hlabel : Measurable label)
    (S : Set X) (hS : MeasurableSet S) (hmuS : mu S = 1)
    (D t e : ℝ) (hD : 0 ≤ D) (ht : 0 ≤ t) (he : 0 < e)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ D)
    (latent : Fin k → ProbabilityMeasure Z) (phi : Fin k → Z → X)
    (L : Fin k → ℝ≥0) (hphi : ∀ a, LipschitzWith (L a) (phi a))
    (hcond : ∀ a, 0 < mu.real (label ⁻¹' {a}) →
      cond mu (label ⁻¹' {a}) = (latent a : Measure Z).map (phi a))
    (s : Fin k → ℝ) (hst : ∀ a, (L a : ℝ) * s a ≤ t)
    (beta : Fin k → ℝ≥0∞)
    (hB : ∀ a, 0 < mu.real (label ⁻¹' {a}) → ∀ N : ℕ,
      MeasurableSet {x : Fin N → X | ¬ wasserstein1 (cond mu (label ⁻¹' {a}))
        (empiricalMeasure x) ≤ ENNReal.ofReal t})
    (hbound : ∀ a, 0 < mu.real (label ⁻¹' {a}) → ∀ N : ℕ,
      m * mu.real (label ⁻¹' {a}) / 2 ≤ N →
      (Measure.pi (fun _ : Fin N => (latent a : Measure Z)))
        {z | ¬ wasserstein1 (latent a : Measure Z) (empiricalMeasure z) ≤
          ENNReal.ofReal (s a)} ≤ beta a) :
    Q {w | ¬ wasserstein1 mu (empiricalMeasure (fun i => sample i w)) ≤
      ENNReal.ofReal (t + D / 2 * e)} ≤
      ENNReal.ofReal (2 * k * Real.exp (-2 * m * (e / k) ^ 2)) +
        ∑ a, if 0 < mu.real (label ⁻¹' {a}) then
          ENNReal.ofReal (2 * k * Real.exp
            (-2 * m * ((mu.real (label ⁻¹' {a}) / 2) / k) ^ 2)) + beta a else 0 := by
  apply iid_observational_wasserstein_failure_le_of_product_tails Q mu hm sample
    hsample hind hlaw label hlabel S hS hmuS D t e hD ht he hdiam beta hB
  intro a ha N hcount
  have hN : 0 < N := by
    have hpos : 0 < (m : ℝ) * mu.real (label ⁻¹' {a}) / 2 := by positivity
    exact_mod_cast (lt_of_lt_of_le hpos hcount)
  have hmeas := hB a ha N
  rw [hcond a ha] at hmeas ⊢
  exact (compact_pushforward_empirical_failure_le (latent a : Measure Z) hN
    (phi a) (L a) (hphi a) (s a) t (hst a) hmeas).trans (hbound a ha N hcount)

end Papers.TbsNeuralCausalPi
