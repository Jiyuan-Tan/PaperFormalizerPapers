module
public import Papers.TbsNeuralCausalPi.Helpers.DoseResponseBoundedRegression
/-! # Averaging and overlap in the dose-response comparison

The squared mean regression gap is bounded by its mean square under the
covariate law. Measure domination then transfers this bound to the reference
dose law, before the final decomposition is integrated.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory Filter
open scoped ENNReal

/-- If [f is integrable under a probability law](hyp:hf) and [its square is
integrable under that law](hyp:hf2), then [the square of its mean is at most
its mean square](goal). -/
-- @node: regression_mean_square_le
lemma regression_mean_square_le
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [IsProbabilityMeasure mu]
    (f : X → ℝ) (hf : Integrable f mu)
    (hf2 : Integrable (fun x => (f x) ^ 2) mu) :
    (∫ x, f x ∂mu) ^ 2 ≤ ∫ x, (f x) ^ 2 ∂mu := by
  let m := ∫ x, f x ∂mu
  have heq : (fun x => (f x - m) ^ 2) =
      (fun x => (f x) ^ 2 - (2 * m) * f x + m ^ 2) := by
    funext x
    ring
  have hpos : 0 ≤ ∫ x, (f x - m) ^ 2 ∂mu :=
    integral_nonneg (fun x => sq_nonneg _)
  rw [heq] at hpos
  rw [integral_add (f := fun x => (f x) ^ 2 - (2 * m) * f x)
      (g := fun _ => m ^ 2) (hf2.sub (hf.const_mul (2 * m))) (integrable_const _),
    integral_sub (f := fun x => (f x) ^ 2) (g := fun x => (2 * m) * f x)
      hf2 (hf.const_mul (2 * m)), integral_const_mul] at hpos
  simp only [integral_const, probReal_univ, one_smul] at hpos
  dsimp [m] at hpos
  nlinarith

/-- If [the discrepancy is integrable under the product of the dose measure
and covariate probability law](hyp:hd) and [its square is integrable under
that product](hyp:hd2), then [the squared covariate-averaged discrepancy is
integrable over doses, and its dose integral is at most the joint integral
of the squared discrepancy](goal). -/
-- @node: integrated_regression_mean_square_le
lemma integrated_regression_mean_square_le
    {X T : Type*} [MeasurableSpace X] [MeasurableSpace T]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (rho : Measure T) [SFinite rho] (d : T × X → ℝ)
    (hd : Integrable d (rho.prod mu))
    (hd2 : Integrable (fun z => (d z) ^ 2) (rho.prod mu)) :
    Integrable (fun t => (∫ x, d (t, x) ∂mu) ^ 2) rho ∧
      (∫ t, (∫ x, d (t, x) ∂mu) ^ 2 ∂rho) ≤
        ∫ z, (d z) ^ 2 ∂(rho.prod mu) := by
  have hpoint : ∀ᵐ t ∂rho,
      (∫ x, d (t, x) ∂mu) ^ 2 ≤ ∫ x, (d (t, x)) ^ 2 ∂mu := by
    filter_upwards [hd.prod_right_ae, hd2.prod_right_ae] with t ht ht2
    exact regression_mean_square_le mu _ ht ht2
  have hm : AEStronglyMeasurable (fun t => (∫ x, d (t, x) ∂mu) ^ 2) rho := by
    first | fun_prop | exact hd.integral_prod_left.aestronglyMeasurable.pow 2
  have hi : Integrable (fun t => (∫ x, d (t, x) ∂mu) ^ 2) rho := by
    apply hd2.integral_prod_left.mono' hm
    filter_upwards [hpoint] with t ht
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (∫ x, d (t, x) ∂mu))]
      using ht
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ t, ∫ x, (d (t, x)) ^ 2 ∂mu ∂rho :=
      integral_mono_ae hi hd2.integral_prod_left hpoint
    _ = _ := (integral_prod _ hd2).symm

/-- If [delta is positive](hyp:hdelta), [the observational input measure
dominates delta times the reference dose–covariate product measure](hyp:hoverlap),
[the discrepancy is integrable under that product](hyp:hd), [its square is
integrable under that product](hyp:hd2), and [its square is integrable under
the observational measure](hyp:heta),
then [delta times the dose integral of the squared covariate-averaged
discrepancy is at most its observational mean square](goal). -/
-- @node: overlap_regression_mean_square_le
lemma overlap_regression_mean_square_le
    {X T : Type*} [MeasurableSpace X] [MeasurableSpace T]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (rho : Measure T) [SFinite rho] (eta : Measure (T × X))
    (d : T × X → ℝ) (delta : ℝ) (hdelta : 0 < delta)
    (hoverlap : ENNReal.ofReal delta • (rho.prod mu) ≤ eta)
    (hd : Integrable d (rho.prod mu))
    (hd2 : Integrable (fun z => (d z) ^ 2) (rho.prod mu))
    (heta : Integrable (fun z => (d z) ^ 2) eta) :
    delta * (∫ t, (∫ x, d (t, x) ∂mu) ^ 2 ∂rho) ≤
      ∫ z, (d z) ^ 2 ∂eta := by
  have hj := (integrated_regression_mean_square_le mu rho d hd hd2).2
  calc
    _ ≤ delta * ∫ z, (d z) ^ 2 ∂(rho.prod mu) :=
      mul_le_mul_of_nonneg_left hj hdelta.le
    _ = ∫ z, (d z) ^ 2 ∂(ENNReal.ofReal delta • (rho.prod mu)) := by
      rw [integral_smul_measure, ENNReal.toReal_ofReal hdelta.le, smul_eq_mul]
    _ ≤ _ := integral_mono_measure hoverlap (Eventually.of_forall (fun z => sq_nonneg _)) heta

/-- For [a nonnegative, possibly infinite joint density p](hyp:p), if
[delta is positive](hyp:hdelta), [p is at least delta almost everywhere under
the reference dose–covariate product measure](hyp:hoverlap), [the discrepancy
is integrable under that product](hyp:hd), [its square is integrable under
that product](hyp:hd2), and [its square
is integrable under the measure with density p](hyp:heta), then [delta times
the dose integral of the squared covariate-averaged discrepancy is at most
its integral square under the measure with density p](goal). -/
-- @node: overlap_density_regression_mean_square_le
lemma overlap_density_regression_mean_square_le
    {X T : Type*} [MeasurableSpace X] [MeasurableSpace T]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (rho : Measure T) [SFinite rho] (p : T × X → ℝ≥0∞)
    (d : T × X → ℝ) (delta : ℝ) (hdelta : 0 < delta)
    (hoverlap : ∀ᵐ z ∂(rho.prod mu), ENNReal.ofReal delta ≤ p z)
    (hd : Integrable d (rho.prod mu))
    (hd2 : Integrable (fun z => (d z) ^ 2) (rho.prod mu))
    (heta : Integrable (fun z => (d z) ^ 2) ((rho.prod mu).withDensity p)) :
    delta * (∫ t, (∫ x, d (t, x) ∂mu) ^ 2 ∂rho) ≤
      ∫ z, (d z) ^ 2 ∂((rho.prod mu).withDensity p) := by
  apply overlap_regression_mean_square_le mu rho _ d delta hdelta _ hd hd2 heta
  simpa only [MeasureTheory.withDensity_const] using withDensity_mono hoverlap

/-- Suppose [the response gap is measurable](hyp:hgap), [delta is positive](hyp:hdelta),
[the observational input measure dominates delta times the reference product
measure](hyp:hoverlap), [the regression discrepancy is integrable under that
product](hyp:hd), [its square is integrable under that product](hyp:hd2), and
[its square is integrable observationally](hyp:heta).
If [the observational mean square discrepancy is at most CW W](hyp:hreg),
[the response gap equals the covariate-averaged discrepancy plus c almost
everywhere](hyp:hdecomp), and [the absolute value of c is at most Ly W almost
everywhere](hyp:hc), then [the integrated squared response gap is at most
2 CW W / delta plus 2 Ly squared W squared times the total dose mass](goal). -/
-- @node: dose_response_bound_of_overlap_and_regression
lemma dose_response_bound_of_overlap_and_regression
    {X T : Type*} [MeasurableSpace X] [MeasurableSpace T]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (rho : Measure T) [IsFiniteMeasure rho] (eta : Measure (T × X))
    (d : T × X → ℝ) (gap c : T → ℝ) (hgap : Measurable gap)
    (Ly W CW delta : ℝ) (hdelta : 0 < delta)
    (hoverlap : ENNReal.ofReal delta • (rho.prod mu) ≤ eta)
    (hd : Integrable d (rho.prod mu))
    (hd2 : Integrable (fun z => (d z) ^ 2) (rho.prod mu))
    (heta : Integrable (fun z => (d z) ^ 2) eta)
    (hreg : (∫ z, (d z) ^ 2 ∂eta) ≤ CW * W)
    (hdecomp : ∀ᵐ t ∂rho, gap t = (∫ x, d (t, x) ∂mu) + c t)
    (hc : ∀ᵐ t ∂rho, |c t| ≤ Ly * W) :
    (∫ t, (gap t) ^ 2 ∂rho) ≤
      2 * CW / delta * W + 2 * Ly ^ 2 * W ^ 2 * (rho Set.univ).toReal := by
  have hmean := integrated_regression_mean_square_le mu rho d hd hd2
  have hover := overlap_regression_mean_square_le mu rho eta d delta hdelta
    hoverlap hd hd2 heta
  exact dose_response_integrated_decomposition_le rho gap
    (fun t => ∫ x, d (t, x) ∂mu) c hgap hmean.1 Ly W CW delta hdelta
    hdecomp hc (hover.trans hreg)

end Papers.TbsNeuralCausalPi
