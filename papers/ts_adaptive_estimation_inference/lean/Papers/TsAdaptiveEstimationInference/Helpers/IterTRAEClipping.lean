module
public import Papers.TsAdaptiveEstimationInference.Helpers.TRAESquaredNorm
/-! Clipping and normalization of fixed-center iterative quadratic losses.
The identities hold for the supplied representatives on the common envelope.
They assert no concentration inequality or probability budget.
-/
@[expose] public section
set_option linter.unusedVariables false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory
variable {W X Z Ω : Type*} [MeasurableSpace W] [MeasurableSpace X]
  [MeasurableSpace Z] [MeasurableSpace Ω]
  (V : IVWorld W X Z) (P : Measure Ω)
  (sample : AnalysisSample V P) (split : SampleSplit)

/-- In [the instrumental-variable model](hyp:V), the [clipped squared distance](goal)
between [a hypothesis](hyp:h) and [a reference hypothesis](hyp:a) at
[an observation](hyp:w) is their absolute prediction difference divided by
[the normalization scale](hyp:s), capped at one and squared. -/
-- @node: iterTraeClippedDistance
noncomputable def iterTraeClippedDistance (s : ℝ) (h a : V.Hbar.toSubmodule)
    (w : W) : ℝ :=
  (min |(primalVersion V h (V.xOf w) - primalVersion V a (V.xOf w)) / s| 1) ^ 2

/-- [The normalized, clipped squared prediction distance between any two
hypotheses is a measurable function of the observation](goal). -/
-- @node: iter_trae_clipped_distance_measurable
@[fun_prop] lemma iter_trae_clipped_distance_measurable (s : ℝ)
    (h a : V.Hbar.toSubmodule) : Measurable (iterTraeClippedDistance V s h a) := by
  unfold iterTraeClippedDistance
  have hh : Measurable (fun w => primalVersion V h (V.xOf w)) :=
    (V.primal_measurable h).comp V.measurable_x
  have ha : Measurable (fun w => primalVersion V a (V.xOf w)) :=
    (V.primal_measurable a).comp V.measurable_x
  exact (((hh.sub ha).div_const s).abs.min measurable_const).pow_const 2

/-- [The normalized, clipped squared prediction distance lies between zero and
one at every observation](goal). -/
-- @node: iter_trae_clipped_distance_mem_Icc
lemma iter_trae_clipped_distance_mem_Icc (s : ℝ)
    (h a : V.Hbar.toSubmodule) (w : W) :
    iterTraeClippedDistance V s h a w ∈ Set.Icc (0 : ℝ) 1 := by
  unfold iterTraeClippedDistance
  constructor
  · positivity
  · exact (pow_le_pow_left₀ (le_min (abs_nonneg _) zero_le_one)
      (min_le_right _ _) 2).trans_eq (by norm_num)

/-- If [the normalization scale is positive](hyp:hs), [the squared distance from
a fixed center, normalized and clipped at one, changes by at most twice the
change in its argument divided by the scale](goal). -/
-- @node: iter_trae_clipped_center_lipschitz
lemma iter_trae_clipped_center_lipschitz (s center u v : ℝ) (hs : 0 < s) :
    |(min |(u - center) / s| 1) ^ 2 - (min |(v - center) / s| 1) ^ 2| ≤
      (2 / s) * |u - v| := by
  have h := trae_clipped_square_lipschitz ((u - center) / s) ((v - center) / s)
  calc
    _ ≤ 2 * |(u - center) / s - (v - center) / s| := h
    _ = _ := by
      rw [← sub_div, sub_sub_sub_cancel_right, abs_div, abs_of_pos hs]
      ring

/-- If [the scale is positive](hyp:hs), [it is at least twice the envelope
bound](hyp:hBs), and [the hypothesis prediction](hyp:hh) and [the reference
prediction](hyp:ha) each have absolute value at most that bound, [the clipped
distance equals the squared prediction difference divided by the squared
scale](goal). -/
-- @node: iter_trae_clipped_distance_eq
lemma iter_trae_clipped_distance_eq (s B : ℝ) (hs : 0 < s) (hBs : 2 * B ≤ s)
    (h a : V.Hbar.toSubmodule) (w : W)
    (hh : |primalVersion V h (V.xOf w)| ≤ B)
    (ha : |primalVersion V a (V.xOf w)| ≤ B) :
    iterTraeClippedDistance V s h a w =
      (primalVersion V h (V.xOf w) - primalVersion V a (V.xOf w)) ^ 2 / s ^ 2 := by
  have hdiff : |primalVersion V h (V.xOf w) - primalVersion V a (V.xOf w)| ≤ s :=
    (abs_sub _ _).trans ((add_le_add hh ha).trans (by linarith only [hBs]))
  unfold iterTraeClippedDistance
  rw [min_eq_left (by rw [abs_div, abs_of_pos hs]; exact (div_le_one hs).2 hdiff),
    sq_abs, div_pow]

/-- If [the envelope bound is nonnegative](hyp:hB), [every class member's
prediction at this observation is bounded by it](hyp:hw), [the reference is zero
or belongs to the class](hyp:ha), and [the zero hypothesis predicts zero at this
observation](hyp:hzero), [the reference prediction also satisfies the envelope
bound](goal). -/
-- @node: iter_trae_zero_or_class_bound
lemma iter_trae_zero_or_class_bound (B : ℝ) (hB : 0 ≤ B) (w : W)
    (hw : ∀ h ∈ V.H, |primalVersion V h (V.xOf w)| ≤ B)
    (a : V.Hbar.toSubmodule) (ha : a = 0 ∨ a ∈ V.H)
    (hzero : primalVersion V 0 (V.xOf w) = 0) :
    |primalVersion V a (V.xOf w)| ≤ B := by
  rcases ha with rfl | ha
  · simpa only [hzero, abs_zero] using hB
  · exact hw a ha

/-- If [the scale is positive](hyp:hs) and [at least twice the envelope
bound](hyp:hBs), [the TRAE boundedness assumptions hold](hyp:hBound), [the
representatives share a common almost-sure envelope](hyp:hCommon), [the
hypothesis belongs to the class](hyp:hh), and [the reference is zero or a class
member](hyp:ha), [the expected clipped distance equals their squared Hilbert
distance divided by the squared scale](goal). -/
-- @node: iter_trae_clipped_distance_integral
lemma iter_trae_clipped_distance_integral (s B : ℝ) (hs : 0 < s)
    (hBs : 2 * B ≤ s) (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B)
    (h a : V.Hbar.toSubmodule) (hh : h ∈ V.H) (ha : a = 0 ∨ a ∈ V.H) :
    (∫ w, iterTraeClippedDistance V s h a w ∂V.law) = ‖h - a‖ ^ 2 / s ^ 2 := by
  calc
    _ = ∫ w, (primalVersion V h (V.xOf w) - primalVersion V a (V.xOf w)) ^ 2 /
        s ^ 2 ∂V.law := by
      apply integral_congr_ae
      filter_upwards [hBound.2.2.1, primalVersion_zero_ae V] with w hw hzero
      exact iter_trae_clipped_distance_eq V s B hs hBs h a w (hw h hh)
        (iter_trae_zero_or_class_bound V B hBound.1 w hw a ha hzero)
    _ = _ := by rw [integral_div, trae_primal_difference_energy]

/-- Suppose [the scale is positive](hyp:hs) and [at least twice the envelope
bound](hyp:hBs), [TRAE boundedness holds](hyp:hBound), [a common almost-sure
envelope holds](hyp:hCommon), [all class predictions satisfy the envelope on the
fitting observations](hyp:hω), and [zero predicts zero throughout the
sample](hyp:hZero). For [a class hypothesis](hyp:hh) and [a reference that is
zero or in the class](hyp:ha), [the empirical squared-distance error equals the
squared scale times the empirical-minus-population clipped-distance
error](goal). -/
-- @node: iter_trae_clipped_distance_transfer
lemma iter_trae_clipped_distance_transfer (s B : ℝ) (hs : 0 < s)
    (hBs : 2 * B ≤ s) (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B)
    (n : ℕ) (ω : Ω)
    (hω : ∀ i ∈ split.fit n, ∀ h ∈ V.H,
      |primalVersion V h (V.xOf (sample.Z i ω))| ≤ B)
    (hZero : ω ∈ sampleZeroEvent V P sample)
    (h a : V.Hbar.toSubmodule) (hh : h ∈ V.H) (ha : a = 0 ∨ a ∈ V.H) :
    primalEmpDistanceSq V P sample split n ω h a - ‖h - a‖ ^ 2 =
      s ^ 2 * (blockAverage V P sample (split.fit n)
        (iterTraeClippedDistance V s h a) ω -
          ∫ w, iterTraeClippedDistance V s h a w ∂V.law) := by
  have hemp : blockAverage V P sample (split.fit n)
      (iterTraeClippedDistance V s h a) ω =
      primalEmpDistanceSq V P sample split n ω h a / s ^ 2 := by
    simp only [primalEmpDistanceSq, blockAverage]
    rw [mul_div_assoc, Finset.sum_div]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    exact iter_trae_clipped_distance_eq V s B hs hBs h a _
      (hω i hi h hh)
      (iter_trae_zero_or_class_bound V B hBound.1 _ (hω i hi) a ha
        (sampleZeroEvent_spec V P sample hZero i).1)
  rw [hemp, iter_trae_clipped_distance_integral V s B hs hBs hBound hCommon h a hh ha]
  field_simp

/-- Suppose [the scale is positive](hyp:hs) and [at least twice the envelope
bound](hyp:hBs), [TRAE boundedness holds](hyp:hBound), [a common almost-sure
envelope holds](hyp:hCommon), [all class predictions satisfy the fitting-sample
envelope](hyp:hω), and [zero predicts zero throughout the sample](hyp:hZero).
For [the first class hypothesis](hyp:hh), [the second class hypothesis](hyp:ha),
and [a center that is zero or a class member](hyp:hc), [the empirical-minus-
population difference of their squared distances from the center equals the
squared scale times the difference of their clipped-distance deviations](goal). -/
-- @node: iter_trae_clipped_center_transfer
lemma iter_trae_clipped_center_transfer (s B : ℝ) (hs : 0 < s)
    (hBs : 2 * B ≤ s) (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B)
    (n : ℕ) (ω : Ω)
    (hω : ∀ i ∈ split.fit n, ∀ h ∈ V.H,
      |primalVersion V h (V.xOf (sample.Z i ω))| ≤ B)
    (hZero : ω ∈ sampleZeroEvent V P sample)
    (h a center : V.Hbar.toSubmodule)
    (hh : h ∈ V.H) (ha : a ∈ V.H) (hc : center = 0 ∨ center ∈ V.H) :
    (primalEmpDistanceSq V P sample split n ω a center -
        primalEmpDistanceSq V P sample split n ω h center) -
      (‖a - center‖ ^ 2 - ‖h - center‖ ^ 2) =
      s ^ 2 * ((blockAverage V P sample (split.fit n)
          (iterTraeClippedDistance V s a center) ω -
            ∫ w, iterTraeClippedDistance V s a center w ∂V.law) -
        (blockAverage V P sample (split.fit n)
          (iterTraeClippedDistance V s h center) ω -
            ∫ w, iterTraeClippedDistance V s h center w ∂V.law)) := by
  have hfirst := iter_trae_clipped_distance_transfer V P sample split s B hs hBs
    hBound hCommon n ω hω hZero a center ha hc
  have hsecond := iter_trae_clipped_distance_transfer V P sample split s B hs hBs
    hBound hCommon n ω hω hZero h center hh hc
  linarith only [hfirst, hsecond]

end Papers.TsAdaptiveEstimationInference
