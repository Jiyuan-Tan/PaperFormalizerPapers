module
public import Papers.TbsPrteOptimalTransport.Helpers.ConnectedIV
public import Causalean.Mathlib.MeasureTheory.Function.Analytic.UniversalMeasurability.UniversalMeasurability
/-!
# Completed measurability of fitted propensity endpoints

Infima over the instrument domain need not be Borel measurable for arbitrary
measurable learners. Analytic projections give measurable versions under each
finite training-block law, without any assumption on the ambient sample space.
-/
public section
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set
universe v

-- @node: aemeasurable_bounded_parameter_infimum
/-- For standard Borel parameter and index spaces with a nonempty index space and a
finite parameter measure, if [a real-valued function is jointly measurable](hyp:hf) and
[is nonnegative at every parameter-index pair](hyp:hb), then [its infimum over the index
is measurable up to a null set under the parameter measure](goal). -/
lemma aemeasurable_bounded_parameter_infimum
    {T B : Type*} [MeasurableSpace T] [StandardBorelSpace T]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    (μ : Measure T) [IsFiniteMeasure μ] (f : T × B → ℝ)
    (hf : Measurable f) (hb : ∀ t b, 0 ≤ f (t, b)) :
    AEMeasurable (fun t => sInf (range (fun b => f (t, b)))) μ := by
  letI := upgradeStandardBorel T
  have hnull : NullMeasurable (fun t => sInf (range (fun b => f (t, b)))) μ := by
    apply measurable_of_Iio
    intro r
    have he : (fun t => sInf (range (fun b => f (t, b)))) ⁻¹' Iio r =
        Prod.fst '' {tb : T × B | f tb < r} := by
      ext t
      change sInf (range (fun b => f (t, b))) < r ↔ _
      rw [csInf_lt_iff (show BddBelow (range (fun b => f (t, b))) from
        ⟨0, by rintro _ ⟨b, rfl⟩; exact hb t b⟩) (range_nonempty _)]
      simp only [mem_image, mem_setOf_eq, mem_range]
      constructor
      · rintro ⟨v, ⟨b, rfl⟩, hv⟩
        exact ⟨(t, b), hv, rfl⟩
      · rintro ⟨⟨t', b⟩, hv, rfl⟩
        exact ⟨f (t', b), ⟨b, rfl⟩, hv⟩
    change NullMeasurableSet ((fun t : T => sInf (range (fun b => f (t, b)))) ⁻¹' Iio r) μ
    rw [he]
    exact ((measurableSet_lt hf measurable_const).analyticSet_image
      measurable_fst).nullMeasurableSet μ
  exact hnull.aemeasurable

-- @node: aemeasurable_bounded_parameter_supremum
/-- For standard Borel parameter and index spaces with a nonempty index space and a
finite parameter measure, if [a real-valued function is jointly measurable](hyp:hf) and
[is at most one at every parameter-index pair](hyp:hb), then [its supremum over the
index is measurable up to a null set under the parameter measure](goal). -/
lemma aemeasurable_bounded_parameter_supremum
    {T B : Type*} [MeasurableSpace T] [StandardBorelSpace T]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    (μ : Measure T) [IsFiniteMeasure μ] (f : T × B → ℝ)
    (hf : Measurable f) (hb : ∀ t b, f (t, b) ≤ 1) :
    AEMeasurable (fun t => sSup (range (fun b => f (t, b)))) μ := by
  letI := upgradeStandardBorel T
  have hnull : NullMeasurable (fun t => sSup (range (fun b => f (t, b)))) μ := by
    apply measurable_of_Ioi
    intro r
    have he : (fun t => sSup (range (fun b => f (t, b)))) ⁻¹' Ioi r =
        Prod.fst '' {tb : T × B | r < f tb} := by
      ext t
      change r < sSup (range (fun b => f (t, b))) ↔ _
      rw [lt_csSup_iff (show BddAbove (range (fun b => f (t, b))) from
        ⟨1, by rintro _ ⟨b, rfl⟩; exact hb t b⟩) (range_nonempty _)]
      simp only [mem_image, mem_setOf_eq, mem_range]
      constructor
      · rintro ⟨v, ⟨b, rfl⟩, hv⟩
        exact ⟨(t, b), hv, rfl⟩
      · rintro ⟨⟨t', b⟩, hv, rfl⟩
        exact ⟨f (t', b), ⟨b, rfl⟩, hv⟩
    change NullMeasurableSet ((fun t : T => sSup (range (fun b => f (t, b)))) ⁻¹' Ioi r) μ
    rw [he]
    exact ((measurableSet_lt measurable_const hf).analyticSet_image
      measurable_fst).nullMeasurableSet μ
  exact hnull.aemeasurable

-- @node: aemeasurable_fitted_propensity_endpoints
/-- For standard Borel training, covariate, and nonempty instrument spaces and any
finite measure on training data and covariates, if [the fitted propensity is jointly
measurable in training data, instrument, and covariates](hyp:hp) and [always lies between
zero and one](hyp:hb), then [both its lower and upper endpoints over instruments are
measurable up to a null set under that measure](goal). -/
lemma aemeasurable_fitted_propensity_endpoints
    {T : Type*} {X Z : Type v} [MeasurableSpace T] [StandardBorelSpace T]
    [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]
    (μ : Measure (T × X)) [IsFiniteMeasure μ] (p : T → Z → X → ℝ)
    (hp : Measurable (fun tzx : T × Z × X => p tzx.1 tzx.2.1 tzx.2.2))
    (hb : ∀ t z x, p t z x ∈ Icc (0 : ℝ) 1) :
    AEMeasurable (fun tx => pLow (p tx.1) tx.2) μ ∧
    AEMeasurable (fun tx => pHigh (p tx.1) tx.2) μ := by
  have hm : Measurable (fun txz : (T × X) × Z => p txz.1.1 txz.2 txz.1.2) := by
    first | fun_prop | exact hp.comp (by fun_prop)
  exact ⟨aemeasurable_bounded_parameter_infimum μ _ hm
      (fun tx z => (hb tx.1 z tx.2).1),
    aemeasurable_bounded_parameter_supremum μ _ hm
      (fun tx z => (hb tx.1 z tx.2).2)⟩

-- @node: aemeasurable_training_endpoint_pullback
/-- For standard Borel training-summary, covariate, and nonempty instrument spaces and
any finite measure on the original sample and covariates, suppose [the map from the
sample to its training summary is measurable](hyp:hv), [the fitted propensity is jointly
measurable in that summary, instrument, and covariates](hyp:hp), and [all fitted
propensities lie between zero and one](hyp:hb). Then [both fitted propensity endpoints
over instruments, evaluated using the sample's training summary, are measurable up to
a null set under the original sample-covariate measure](goal). -/
lemma aemeasurable_training_endpoint_pullback
    {A T : Type*} {X Z : Type v} [MeasurableSpace A]
    [MeasurableSpace T] [StandardBorelSpace T]
    [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]
    (μ : Measure (A × X)) [IsFiniteMeasure μ]
    (view : A → T) (hv : Measurable view) (p : T → Z → X → ℝ)
    (hp : Measurable (fun tzx : T × Z × X => p tzx.1 tzx.2.1 tzx.2.2))
    (hb : ∀ t z x, p t z x ∈ Icc (0 : ℝ) 1) :
    AEMeasurable (fun ax => pLow (p (view ax.1)) ax.2) μ ∧
    AEMeasurable (fun ax => pHigh (p (view ax.1)) ax.2) μ := by
  have hview : Measurable (fun ax : A × X => (view ax.1, ax.2)) := by fun_prop
  have he := aemeasurable_fitted_propensity_endpoints
    (μ.map (fun ax => (view ax.1, ax.2))) p hp hb
  exact ⟨he.1.comp_measurable hview, he.2.comp_measurable hview⟩

end Papers.TbsPrteOptimalTransport
