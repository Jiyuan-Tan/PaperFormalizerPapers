module
public import Papers.TbsNeuralCausalPi.Helpers.DoseResponseAveraging
/-! # Product-measure domination from conditional treatment overlap

The density lower bound is used on the intervention interval only. Integrating
the resulting conditional-measure inequalities gives the product domination
needed by the squared-regression averaging argument.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal

/-- Given [a nonnegative, possibly infinite conditional density p](hyp:p) and
[a measurable dose set I](hyp:hI), suppose [almost every covariate's conditional
dose law has density p relative to the reference law](hyp:hdensity) and [p is
at least the nonnegative part of delta throughout I for almost every
covariate](hyp:hoverlap). Then [for almost every covariate, the conditional dose
law dominates the reference law restricted to I and multiplied by the
nonnegative part of delta](goal). -/
-- @node: overlap_conditional_measure_le
lemma overlap_conditional_measure_le
    {X T : Type*} [MeasurableSpace X] [MeasurableSpace T]
    (mu : Measure X) (rho : Measure T) (kappa : Kernel X T)
    (p : X × T → ℝ≥0∞) (I : Set T) (hI : MeasurableSet I) (delta : ℝ)
    (hdensity : ∀ᵐ x ∂mu, kappa x = rho.withDensity (fun t => p (x, t)))
    (hoverlap : ∀ᵐ x ∂mu, ∀ t ∈ I, ENNReal.ofReal delta ≤ p (x, t)) :
    ∀ᵐ x ∂mu, ENNReal.ofReal delta • rho.restrict I ≤ kappa x := by
  filter_upwards [hdensity, hoverlap] with x hx hlow
  rw [hx]
  calc
    ENNReal.ofReal delta • rho.restrict I =
        (rho.restrict I).withDensity (fun _ => ENNReal.ofReal delta) :=
      (withDensity_const _).symm
    _ ≤ (rho.restrict I).withDensity (fun t => p (x,t)) := by
      apply withDensity_mono
      filter_upwards [ae_restrict_mem hI] with t ht
      exact hlow t ht
    _ = (rho.withDensity (fun t => p (x,t))).restrict I :=
      (restrict_withDensity hI _).symm
    _ ≤ _ := Measure.restrict_le_self

/-- Given [a nonnegative, possibly infinite conditional density p](hyp:p) and
[a measurable dose set I](hyp:hI), suppose [almost every covariate's conditional
dose law has density p relative to the reference law](hyp:hdensity) and [p is
at least the nonnegative part of delta throughout I for almost every
covariate](hyp:hoverlap). Then [the joint law formed from the covariate measure
and the conditional dose kernel dominates the product of the covariate measure
and the reference law restricted to I, multiplied by the nonnegative part of
delta](goal). -/
-- @node: overlap_product_measure_le_compProd
lemma overlap_product_measure_le_compProd
    {X T : Type*} [MeasurableSpace X] [MeasurableSpace T]
    (mu : Measure X) [SFinite mu] (rho : Measure T) [SFinite rho]
    (kappa : Kernel X T) [IsSFiniteKernel kappa]
    (p : X × T → ℝ≥0∞) (I : Set T) (hI : MeasurableSet I) (delta : ℝ)
    (hdensity : ∀ᵐ x ∂mu, kappa x = rho.withDensity (fun t => p (x, t)))
    (hoverlap : ∀ᵐ x ∂mu, ∀ t ∈ I, ENNReal.ofReal delta ≤ p (x, t)) :
    ENNReal.ofReal delta • (mu.prod (rho.restrict I)) ≤ mu.compProd kappa := by
  have hconditional := overlap_conditional_measure_le mu rho kappa p I hI delta
    hdensity hoverlap
  apply Measure.le_iff.mpr
  intro S hS
  rw [Measure.smul_apply, smul_eq_mul, Measure.prod_apply hS, Measure.compProd_apply hS,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hconditional] with x hx
  exact hx (Prod.mk x ⁻¹' S)

/-- Suppose [the regression contrast is measurable](hyp:hd), [delta is
positive](hyp:hdelta), [the observed joint measure dominates delta times the
product of the finite reference dose law and the covariate probability
law](hyp:hoverlap), and [the squared contrast is integrable under the observed
joint measure](hyp:heta). Then [both the contrast and its square are integrable
under the reference dose–covariate product measure](goal). -/
-- @node: overlap_regression_integrable
lemma overlap_regression_integrable
    {X T : Type*} [MeasurableSpace X] [MeasurableSpace T]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (rho : Measure T) [IsFiniteMeasure rho] (eta : Measure (T × X))
    (d : T × X → ℝ) (hd : Measurable d) (delta : ℝ) (hdelta : 0 < delta)
    (hoverlap : ENNReal.ofReal delta • (rho.prod mu) ≤ eta)
    (heta : Integrable (fun z => (d z) ^ 2) eta) :
    Integrable d (rho.prod mu) ∧
      Integrable (fun z => (d z) ^ 2) (rho.prod mu) := by
  have hscaled := heta.mono_measure hoverlap
  have hsquare : Integrable (fun z => (d z) ^ 2) (rho.prod mu) :=
    (integrable_smul_measure (ne_of_gt (ENNReal.ofReal_pos.mpr hdelta))
      ENNReal.ofReal_ne_top).1 hscaled
  refine ⟨?_, hsquare⟩
  apply (hsquare.add (integrable_const (1 : ℝ))).mono' (by fun_prop)
  exact Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs]
    change |d z| ≤ (d z) ^ 2 + 1
    nlinarith [sq_nonneg (|d z| - 1), sq_abs (d z)]

/-- Suppose [the regression contrast is measurable](hyp:hd), [delta is
positive](hyp:hdelta), [the observed joint measure dominates delta times the
product of the finite reference dose law and the covariate probability
law](hyp:hoverlap), and [the squared contrast is integrable under the observed
joint measure](hyp:heta). Then [the square of the covariate-averaged contrast is
integrable under the reference dose law, and delta times its integral is at
most the observed integral of the squared contrast](goal). -/
-- @node: overlap_regression_mean_square_le_of_integrable
lemma overlap_regression_mean_square_le_of_integrable
    {X T : Type*} [MeasurableSpace X] [MeasurableSpace T]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (rho : Measure T) [IsFiniteMeasure rho] (eta : Measure (T × X))
    (d : T × X → ℝ) (hd : Measurable d) (delta : ℝ) (hdelta : 0 < delta)
    (hoverlap : ENNReal.ofReal delta • (rho.prod mu) ≤ eta)
    (heta : Integrable (fun z => (d z) ^ 2) eta) :
    Integrable (fun t => (∫ x, d (t, x) ∂mu) ^ 2) rho ∧
      delta * (∫ t, (∫ x, d (t, x) ∂mu) ^ 2 ∂rho) ≤
        ∫ z, (d z) ^ 2 ∂eta := by
  obtain ⟨hi, hi2⟩ := overlap_regression_integrable mu rho eta d hd delta hdelta
    hoverlap heta
  exact ⟨(integrated_regression_mean_square_le mu rho d hi hi2).1,
    overlap_regression_mean_square_le mu rho eta d delta hdelta hoverlap hi hi2 heta⟩

/-- Given [a nonnegative, possibly infinite conditional density p](hyp:p) and
[a measurable dose set I](hyp:hI), suppose [delta is positive](hyp:hdelta),
[almost every covariate's conditional dose law has density p relative to the
finite reference law](hyp:hdensity), and [p is at least delta throughout I for
almost every covariate](hyp:hoverlap). If [the dose–covariate regression contrast
is measurable](hyp:hd) and [its square is integrable under the joint law formed
from the covariate probability law and the conditional dose kernel, with dose
listed first](hyp:heta), then [the squared covariate-averaged contrast is
integrable over I under the reference law, and delta times its integral is at
most the joint-law integral of the squared contrast](goal). -/
-- @node: overlap_conditional_regression_mean_square_le
lemma overlap_conditional_regression_mean_square_le
    {X T : Type*} [MeasurableSpace X] [MeasurableSpace T]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (rho : Measure T) [IsFiniteMeasure rho]
    (kappa : Kernel X T) [IsSFiniteKernel kappa]
    (p : X × T → ℝ≥0∞) (I : Set T) (hI : MeasurableSet I)
    (delta : ℝ) (hdelta : 0 < delta)
    (hdensity : ∀ᵐ x ∂mu, kappa x = rho.withDensity (fun t => p (x, t)))
    (hoverlap : ∀ᵐ x ∂mu, ∀ t ∈ I, ENNReal.ofReal delta ≤ p (x, t))
    (d : T × X → ℝ) (hd : Measurable d)
    (heta : Integrable (fun z => (d z) ^ 2) ((mu.compProd kappa).map Prod.swap)) :
    Integrable (fun t => (∫ x, d (t, x) ∂mu) ^ 2) (rho.restrict I) ∧
      delta * (∫ t in I, (∫ x, d (t, x) ∂mu) ^ 2 ∂rho) ≤
        ∫ z, (d z) ^ 2 ∂((mu.compProd kappa).map Prod.swap) := by
  have hdom := overlap_product_measure_le_compProd mu rho kappa p I hI delta
    hdensity hoverlap
  have hswap := Measure.map_mono hdom measurable_swap
  rw [Measure.map_smul, Measure.prod_swap] at hswap
  exact overlap_regression_mean_square_le_of_integrable mu (rho.restrict I)
    ((mu.compProd kappa).map Prod.swap) d hd delta hdelta hswap heta

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}

/-- Given [a nonnegative, possibly infinite density p for treatment conditional
on its parents](hyp:p), suppose [the treatment has reference density p under the
model's observational law](hyp:hdensity) and [p is at least the nonnegative part
of delta throughout the closed dose interval for almost every parent
value](hyp:hoverlap). Then [the observational joint law of parents and treatment
dominates the product of the observational parent marginal and the reference
dose law restricted to that interval, multiplied by the nonnegative part of
delta](goal). -/
-- @node: treatment_reference_parent_product_le
lemma treatment_reference_parent_product_le (M : EuclideanSCM kind dims)
    (T : Fin n) (P : ProbabilityMeasure ℝ) (treatment : Joint kind → ℝ)
    (p : ParentSpace M T × ℝ → ℝ≥0∞) (delta t1 t2 : ℝ)
    (hdensity : TreatmentReferenceDensity M T treatment P p)
    (hoverlap : ∀ᵐ x ∂((observationalLaw M).map (parentValues M T)),
      ∀ t ∈ Set.Icc t1 t2, ENNReal.ofReal delta ≤ p (x, t)) :
    ENNReal.ofReal delta •
        (((observationalLaw M).map (parentValues M T)).prod
          ((P : Measure ℝ).restrict (Set.Icc t1 t2))) ≤
      (observationalLaw M).map (fun v => (parentValues M T v, treatment v)) := by
  let obs := observationalLaw M
  let : IsFiniteMeasure obs := observationalLaw_finite M
  let joint := obs.map (fun v => (parentValues M T v, treatment v))
  have hparent : Measurable (parentValues M T) := by
    first | fun_prop | skip
    unfold parentValues
    exact scm_toLp_measurable.comp (measurable_pi_lambda _ fun c =>
      (measurable_pi_apply _).comp scm_ofLp_measurable)
  have hfst : joint.fst = obs.map (parentValues M T) := by
    exact Measure.fst_map_prodMk hdensity.2.1
  have hjoint : joint = ((obs.map (parentValues M T)).compProd joint.condKernel) := by
    simpa only [hfst] using (joint.disintegrate joint.condKernel).symm
  rw [show (observationalLaw M).map
      (fun v => (parentValues M T v, treatment v)) = joint from rfl, hjoint]
  exact overlap_product_measure_le_compProd _ (P : Measure ℝ) joint.condKernel p
    (Set.Icc t1 t2) measurableSet_Icc delta hdensity.2.2.2 hoverlap

/-- Given [a nonnegative, possibly infinite density p for treatment conditional
on its parents](hyp:p), suppose [the treatment has reference density p under the
model's observational law](hyp:hdensity), [delta is positive](hyp:hdelta), and
[p is at least delta throughout the closed dose interval for almost every
parent value](hyp:hoverlap). If [the dose–parent regression contrast is
measurable](hyp:hd) and [its square evaluated at the observed treatment and
parents is observationally integrable](hyp:hsquare), then [the squared contrast
averaged over the observational parent marginal is integrable over that
interval under the reference dose law, and delta times its integral is at most
the observational integral of the squared contrast](goal). -/
-- @node: treatment_reference_parent_mean_square_le
lemma treatment_reference_parent_mean_square_le (M : EuclideanSCM kind dims)
    (T : Fin n) (P : ProbabilityMeasure ℝ) (treatment : Joint kind → ℝ)
    (p : ParentSpace M T × ℝ → ℝ≥0∞) (delta t1 t2 : ℝ)
    (hdensity : TreatmentReferenceDensity M T treatment P p) (hdelta : 0 < delta)
    (hoverlap : ∀ᵐ x ∂((observationalLaw M).map (parentValues M T)),
      ∀ t ∈ Set.Icc t1 t2, ENNReal.ofReal delta ≤ p (x, t))
    (d : ℝ × ParentSpace M T → ℝ) (hd : Measurable d)
    (hsquare : Integrable (fun v => (d (treatment v, parentValues M T v)) ^ 2)
      (observationalLaw M)) :
    Integrable (fun t => (∫ x, d (t, x)
      ∂(observationalLaw M).map (parentValues M T)) ^ 2)
        ((P : Measure ℝ).restrict (Set.Icc t1 t2)) ∧
      delta * (∫ t in Set.Icc t1 t2,
        (∫ x, d (t, x) ∂(observationalLaw M).map (parentValues M T)) ^ 2
          ∂(P : Measure ℝ)) ≤
        ∫ v, (d (treatment v, parentValues M T v)) ^ 2 ∂observationalLaw M := by
  let := M.probability
  haveI : IsProbabilityMeasure (observationalLaw M) :=
    Measure.isProbabilityMeasure_map (evalSteps_measurable M _ _).aemeasurable
  have hparent : Measurable (parentValues M T) := by
    first | fun_prop | skip
    unfold parentValues
    exact scm_toLp_measurable.comp (measurable_pi_lambda _ fun c =>
      (measurable_pi_apply _).comp scm_ofLp_measurable)
  have hjoint : Measurable (fun v => (parentValues M T v, treatment v)) :=
    hparent.prodMk hdensity.2.1
  have hswap : Measurable (fun v => (treatment v, parentValues M T v)) :=
    hdensity.2.1.prodMk hparent
  haveI : IsProbabilityMeasure ((observationalLaw M).map (parentValues M T)) :=
    Measure.isProbabilityMeasure_map hparent.aemeasurable
  have hdom := Measure.map_mono
    (treatment_reference_parent_product_le M T P treatment p delta t1 t2 hdensity hoverlap)
    measurable_swap
  rw [Measure.map_smul, Measure.prod_swap, Measure.map_map measurable_swap hjoint] at hdom
  dsimp only [Function.comp_def, Prod.swap] at hdom
  have hi : Integrable (fun z => (d z) ^ 2)
      ((observationalLaw M).map (fun v => (treatment v, parentValues M T v))) :=
    (integrable_map_measure (hd.pow_const 2).aestronglyMeasurable hswap.aemeasurable).2 hsquare
  obtain ⟨hmean, hbound⟩ := overlap_regression_mean_square_le_of_integrable
    ((observationalLaw M).map (parentValues M T))
    ((P : Measure ℝ).restrict (Set.Icc t1 t2)) _ d hd delta hdelta hdom hi
  refine ⟨hmean, ?_⟩
  simpa only [integral_map hswap.aemeasurable (hd.pow_const 2).aestronglyMeasurable]
    using hbound

end Papers.TbsNeuralCausalPi
