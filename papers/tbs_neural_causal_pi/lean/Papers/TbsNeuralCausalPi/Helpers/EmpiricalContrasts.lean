module
public import Papers.TbsNeuralCausalPi.Helpers.EmpiricalSqrt
public import Papers.TbsNeuralCausalPi.Setup.Optimization
public import StatLean.ComputationalStatistics.Core.EmpiricalMeasure
/-! # Push-forward contrasts and the squared-loss reduction

The empirical law is the finite average already provided by StatLean. These
identities connect its integral to the square-root normalization in the
uniform Wasserstein proof, including the strict failure event.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- If [S is a measurable subset of the finite-dimensional outcome space](hyp:hS),
[the test h is continuous on S](hyp:hh), [R is nonnegative](hyp:hR), and
[the absolute value of h is at most R on S](hyp:hbound), then
[there exists a globally measurable function agreeing with h on S and bounded
in absolute value by R everywhere](goal). -/
-- @node: exists_measurable_bounded_test_representative
lemma exists_measurable_bounded_test_representative {d : ℕ}
    {S : Set (L1Vec d)} (hS : MeasurableSet S) {h : L1Vec d → ℝ}
    (hh : ContinuousOn h S) {R : ℝ} (hR : 0 ≤ R)
    (hbound : ∀ y ∈ S, |h y| ≤ R) :
    ∃ g : L1Vec d → ℝ, Measurable g ∧
      (∀ y ∈ S, g y = h y) ∧ ∀ y, |g y| ≤ R := by
  classical
  let g := S.piecewise h (fun _ => 0)
  have hmeas : Measurable g := by
    first | fun_prop | exact hh.measurable_piecewise continuousOn_const hS
  refine ⟨g, hmeas, ?_, ?_⟩
  · intro y hy
    exact Set.piecewise_eq_of_mem S h (fun _ => 0) hy
  · intro y
    by_cases hy : y ∈ S
    · simpa only [g, Set.piecewise_eq_of_mem S h (fun _ => 0) hy] using hbound y hy
    · simpa only [g, Set.piecewise_eq_of_notMem S h (fun _ => 0) hy, abs_zero] using hR

/-- If [f is measurable](hyp:hf), [S is measurable](hyp:hS),
[every value of f belongs to S](hyp:himage), and [h and g agree on S](hyp:heq),
then [the integrals of h and g under the law obtained by mapping Q through f are equal](goal). -/
-- @node: pushforward_test_integral_congr_on
lemma pushforward_test_integral_congr_on
    {X E : Type*} [MeasurableSpace X] [MeasurableSpace E]
    (Q : Measure X) {f : X → E} (hf : Measurable f)
    {S : Set E} (hS : MeasurableSet S) (himage : ∀ x, f x ∈ S)
    {h g : E → ℝ} (heq : ∀ y ∈ S, h y = g y) :
    (∫ y, h y ∂Q.map f) = ∫ y, g y ∂Q.map f := by
  have hae : ∀ᵐ y ∂Q.map f, y ∈ S :=
    (ae_map_iff hf.aemeasurable hS).mpr (Filter.Eventually.of_forall himage)
  exact integral_congr_ae (hae.mono heq)

/-- If [g is measurable](hyp:hg), then [its integral under the empirical law
of n observations equals the sum of its observed values divided by n](goal),
with the reciprocal of zero interpreted as zero for an empty sample. -/
-- @node: empiricalMeasure_integral_eq_average
lemma empiricalMeasure_integral_eq_average {X : Type*} [MeasurableSpace X]
    {n : ℕ} (x : Fin n → X) {g : X → ℝ} (hg : Measurable g) :
    (∫ y, g y ∂empiricalMeasure x) = (n : ℝ)⁻¹ * ∑ i, g (x i) := by
  exact StatLean.ComputationalStatistics.integral_empiricalMeasure hg.stronglyMeasurable

/-- If [the structural map f is measurable](hyp:hf) and [the test h is measurable](hyp:hh),
then [the population-minus-empirical integral of h under the laws mapped through f
equals the population integral of h composed with f minus its sample average](goal). -/
-- @node: pushforward_test_contrast_eq_average
lemma pushforward_test_contrast_eq_average
    {X E : Type*} [MeasurableSpace X] [MeasurableSpace E]
    (mu : ProbabilityMeasure X) {f : X → E} (hf : Measurable f)
    {h : E → ℝ} (hh : Measurable h) {n : ℕ} (x : Fin n → X) :
    (∫ y, h y ∂((mu : Measure X).map f)) -
        ∫ y, h y ∂((empiricalMeasure x).map f) =
      (∫ y, h (f y) ∂(mu : Measure X)) - (n : ℝ)⁻¹ * ∑ i, h (f (x i)) := by
  rw [integral_map hf.aemeasurable hh.aestronglyMeasurable,
    integral_map hf.aemeasurable hh.aestronglyMeasurable,
    empiricalMeasure_integral_eq_average x (g := fun y => h (f y)) (hh.comp hf)]

/-- If [f is measurable](hyp:hf), [h is measurable](hyp:hh), [R is positive](hyp:hR),
[the absolute value of h composed with f is bounded by R everywhere](hyp:hbound),
and [the sample size is positive](hyp:hn), then
[the population-minus-empirical integral of h under the mapped laws equals twice R
times the population-minus-sample average of the squared normalized square-root test composed with f](goal). -/
-- @node: pushforward_sqrt_squared_loss_contrast
lemma pushforward_sqrt_squared_loss_contrast
    {X E : Type*} [MeasurableSpace X] [MeasurableSpace E]
    (mu : ProbabilityMeasure X) {f : X → E} (hf : Measurable f)
    {h : E → ℝ} (hh : Measurable h) {R : ℝ} (hR : 0 < R)
    (hbound : ∀ y, |h (f y)| ≤ R) {n : ℕ} (hn : 0 < n) (x : Fin n → X) :
    (∫ y, h y ∂((mu : Measure X).map f)) -
        ∫ y, h y ∂((empiricalMeasure x).map f) =
      2 * R * ((∫ y, (normalizedSqrtTest h R (f y))^2 ∂(mu : Measure X)) -
        (n : ℝ)⁻¹ * ∑ i, (normalizedSqrtTest h R (f (x i)))^2) := by
  rw [pushforward_test_contrast_eq_average mu hf hh x]
  exact normalizedSqrtTest_squared_loss_contrast mu hR (hh.comp hf) hbound hn x

/-- If [every map in F is measurable](hyp:hF), [the test h is measurable](hyp:hh),
[R is positive](hyp:hR), [the error threshold is nonnegative](hyp:heps),
[h composed with every map in F is bounded in absolute value by R](hyp:hbound),
and [the sample size is positive](hyp:hn), then
[every sample for which some mapped population-minus-empirical test integral
strictly exceeds the error threshold also has a normalized square-root test from
the transformed class whose absolute squared-loss contrast is at least the
error threshold divided by twice R](goal). -/
-- @node: pushforward_failure_subset_squared_loss
lemma pushforward_failure_subset_squared_loss
    {X E : Type*} [MeasurableSpace X] [MeasurableSpace E]
    (mu : ProbabilityMeasure X) {F : Set (X → E)}
    (hF : ∀ f ∈ F, Measurable f) {h : E → ℝ} (hh : Measurable h)
    {R eps : ℝ} (hR : 0 < R) (heps : 0 ≤ eps)
    (hbound : ∀ f ∈ F, ∀ y, |h (f y)| ≤ R) {n : ℕ} (hn : 0 < n) :
    {x : Fin n → X | ∃ f ∈ F,
      ENNReal.ofReal eps < ENNReal.ofReal
        ((∫ y, h y ∂((mu : Measure X).map f)) -
          ∫ y, h y ∂((empiricalMeasure x).map f))} ⊆
    {x : Fin n → X | ∃ g ∈ ((fun f : X → E => normalizedSqrtTest h R ∘ f) '' F),
      eps / (2*R) ≤ |(∫ y, (g y)^2 ∂(mu : Measure X)) -
        (n : ℝ)⁻¹ * ∑ i, (g (x i))^2|} := by
  rintro x ⟨f, hf, hbad⟩
  refine ⟨normalizedSqrtTest h R ∘ f, Set.mem_image_of_mem _ hf, ?_⟩
  have hreal : eps < (∫ y, h y ∂((mu : Measure X).map f)) -
      ∫ y, h y ∂((empiricalMeasure x).map f) :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg heps).mp hbad
  rw [pushforward_sqrt_squared_loss_contrast mu (hF f hf) hh hR (hbound f hf) hn x]
    at hreal
  exact ((div_lt_iff₀ (by positivity : 0 < 2*R)).mpr
    (by simpa only [mul_comm, Function.comp_apply] using hreal)).le.trans (le_abs_self _)

/-- Suppose [every map in F is measurable](hyp:hF), [the output set S is measurable](hyp:hS),
[every map in F takes all its values in S](hyp:himage), [h is continuous on S](hyp:hh),
[R is positive](hyp:hR), [the error threshold is nonnegative](hyp:heps),
[h is bounded in absolute value by R on S](hyp:hbound), and [the sample size is positive](hyp:hn).
Then [there exists a globally measurable test agreeing with h on S and bounded
in absolute value by R, such that every sample with a mapped test contrast
strictly exceeding the error threshold has a normalized square-root test from
the transformed class whose absolute squared-loss contrast is at least the
error threshold divided by twice R](goal). -/
-- @node: supported_test_failure_subset_squared_loss
lemma supported_test_failure_subset_squared_loss
    {X : Type*} [MeasurableSpace X] {d : ℕ} (mu : ProbabilityMeasure X)
    {F : Set (X → L1Vec d)} (hF : ∀ f ∈ F, Measurable f)
    {S : Set (L1Vec d)} (hS : MeasurableSet S)
    (himage : ∀ f ∈ F, ∀ x, f x ∈ S)
    {h : L1Vec d → ℝ} (hh : ContinuousOn h S)
    {R eps : ℝ} (hR : 0 < R) (heps : 0 ≤ eps)
    (hbound : ∀ y ∈ S, |h y| ≤ R) {n : ℕ} (hn : 0 < n) :
    ∃ g : L1Vec d → ℝ, Measurable g ∧ (∀ y ∈ S, g y = h y) ∧
      (∀ y, |g y| ≤ R) ∧
      {x : Fin n → X | ∃ f ∈ F,
        ENNReal.ofReal eps < ENNReal.ofReal
          ((∫ y, h y ∂((mu : Measure X).map f)) -
            ∫ y, h y ∂((empiricalMeasure x).map f))} ⊆
      {x : Fin n → X | ∃ z ∈ ((fun f : X → L1Vec d => normalizedSqrtTest g R ∘ f) '' F),
        eps / (2*R) ≤ |(∫ y, (z y)^2 ∂(mu : Measure X)) -
          (n : ℝ)⁻¹ * ∑ i, (z (x i))^2|} := by
  obtain ⟨g, hg, heq, hgBound⟩ :=
    exists_measurable_bounded_test_representative hS hh hR.le hbound
  refine ⟨g, hg, heq, hgBound, ?_⟩
  intro x hx
  apply pushforward_failure_subset_squared_loss mu hF hg hR heps
    (fun f hf y => hgBound (f y)) hn
  rcases hx with ⟨f, hf, hbad⟩
  have hid (Q : Measure X) := pushforward_test_integral_congr_on Q (hF f hf) hS
    (himage f hf) (fun y hy => (heq y hy).symm)
  exact ⟨f, hf, by rwa [hid (mu : Measure X), hid (empiricalMeasure x)] at hbad⟩

end
end Papers.TbsNeuralCausalPi
