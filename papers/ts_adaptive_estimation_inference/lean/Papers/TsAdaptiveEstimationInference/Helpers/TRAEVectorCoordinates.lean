module
public import Papers.TsAdaptiveEstimationInference.Helpers.TRAESquaredNorm
/-! The coordinate and process obligations in the local Bennett specialization.

The independent star coordinates retain the exact process measurability recorded
in `TRAEBoundedness`. The cited carrier is simultaneous absolute concentration
at the paper-calibrated scales. Broader arbitrary-radius concentration remains
a separate local proof obligation outside the calibrated loss-event path,
with its coordinate envelope and global Lipschitz requirements proved below.
-/
public section
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option maxHeartbeats 600000
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory
open scoped Topology
variable {𝒲 𝒳 𝒵 : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] (V : IVWorld 𝒲 𝒳 𝒵)

/-- [The absolute difference in any one of three coordinates is at most the
Euclidean distance between the two vectors](goal). -/
-- @node: trae_coordinate_le_euclidean
lemma trae_coordinate_le_euclidean (u v : Fin 3 → ℝ) (i : Fin 3) :
    |u i - v i| ≤ Real.sqrt (∑ j, (u j - v j) ^ 2) := by
  apply (Real.le_sqrt (abs_nonneg _) (Finset.sum_nonneg fun j _ => sq_nonneg _)).2
  rw [sq_abs]
  exact Finset.single_le_sum (fun j _ => sq_nonneg (u j - v j)) (Finset.mem_univ i)

/-- [Clipping two real numbers to the same symmetric envelope cannot increase
their absolute difference](goal). -/
-- @node: trae_clip_lipschitz
lemma trae_clip_lipschitz (B u v : ℝ) :
    |max (-B) (min u B) - max (-B) (min v B)| ≤ |u - v| := by
  have hc : LipschitzWith 1 (fun x : ℝ => max (-B) (min x B)) :=
    (LipschitzWith.id.min_const B).const_max (-B)
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hc.dist_le_mul u v

/-- If [the clipping bound is nonnegative](hyp:hB), then [the absolute change
in the clipped three-coordinate loss is at most four plus twice that bound,
multiplied by the Euclidean distance between its inputs](goal). -/
-- @node: trae_clipped_loss_lipschitz
lemma trae_clipped_loss_lipschitz (B : ℝ) (hB : 0 ≤ B)
    (w : 𝒲) (u v : Fin 3 → ℝ) :
    |traeClippedLoss B w u - traeClippedLoss B w v| ≤
      (4 + 2 * B) * Real.sqrt (∑ i, (u i - v i) ^ 2) := by
  have hclip (x : ℝ) : |max (-B) (min x B)| ≤ B := by
    apply abs_le.mpr
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  have hs := (localizedSquaredLossLipschitz B _ _ hB (hclip (u 2)) (hclip (v 2))).trans
    (mul_le_mul_of_nonneg_left (trae_clip_lipschitz B (u 2) (v 2)) (by positivity))
  have ht : |traeClippedLoss B w u - traeClippedLoss B w v| ≤
      2 * |u 0 - v 0| + 2 * |u 1 - v 1| +
        |(max (-B) (min (u 2) B)) ^ 2 - (max (-B) (min (v 2) B)) ^ 2| := by
    unfold traeClippedLoss
    calc
      _ = |(2 * (u 0 - v 0) - 2 * (u 1 - v 1)) -
          ((max (-B) (min (u 2) B)) ^ 2 - (max (-B) (min (v 2) B)) ^ 2)| := by
            congr 1; ring
      _ ≤ |2 * (u 0 - v 0) - 2 * (u 1 - v 1)| +
          |(max (-B) (min (u 2) B)) ^ 2 - (max (-B) (min (v 2) B)) ^ 2| := abs_sub _ _
      _ ≤ _ := by
        have h := abs_sub (2 * (u 0 - v 0)) (2 * (u 1 - v 1))
        norm_num only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h
        linarith
  have h0 := trae_coordinate_le_euclidean u v 0
  have h1 := trae_coordinate_le_euclidean u v 1
  have h2 := mul_le_mul_of_nonneg_left (trae_coordinate_le_euclidean u v 2)
    (show 0 ≤ 2 * B by positivity)
  linarith

/-- [The class of three-coordinate functions whose coordinates belong to the
star hulls of the moment, product-observation, and critic-observation classes,
respectively, is exactly the TRAE loss process class](goal). -/
-- @node: trae_loss_class_coordinates
lemma trae_loss_class_coordinates :
    {v : 𝒲 → Fin 3 → ℝ | ∀ i, (fun w => v w i) ∈
      (![starClass (momentImageClass V), starClass (productObservationClass V),
        starClass (criticObservationClass V)] : Fin 3 → Set (𝒲 → ℝ)) i} =
      traeLossClass V := by
  ext v
  constructor
  · intro hv
    refine ⟨_, hv 0, _, hv 1, _, hv 2, ?_⟩
    funext w i
    fin_cases i <;> rfl
  · rintro ⟨g1, hg1, g2, hg2, g3, hg3, rfl⟩ i
    fin_cases i
    · exact hg1
    · exact hg2
    · exact hg3

/-- If [the envelope bound is nonnegative](hyp:hB) and [all functions in the
original class are simultaneously bounded in absolute value by it almost
surely](hyp:hF), then [the same simultaneous bound holds for their star hull
almost surely](goal). -/
-- @node: trae_star_envelope
lemma trae_star_envelope {F : Set (𝒲 → ℝ)} {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ᵐ w ∂V.law, ∀ g ∈ F, |g w| ≤ B) :
    ∀ᵐ w ∂V.law, ∀ g ∈ starClass F, |g w| ≤ B := by
  filter_upwards [hF] with w hw
  rintro g ⟨a, ha, f, hf, rfl⟩
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ha.1]
  exact (mul_le_mul_of_nonneg_left (hw f hf) ha.1).trans
    (by simpa using mul_le_mul_of_nonneg_right ha.2 hB)

/-- Under [the TRAE boundedness and process-measurability assumptions at bound
B](hyp:hBound) and [the simultaneous bounds outside a common null set](hyp:hCommon),
[every function in each of the three star-coordinate classes is bounded in
absolute value by B plus B squared, simultaneously almost surely](goal). -/
-- @node: trae_vector_coordinate_envelope
lemma trae_vector_coordinate_envelope (B : ℝ) (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B) :
    ∀ᵐ w ∂V.law, ∀ i : Fin 3, ∀ g ∈
      (![starClass (momentImageClass V), starClass (productObservationClass V),
        starClass (criticObservationClass V)] : Fin 3 → Set (𝒲 → ℝ)) i,
      |g w| ≤ B + B ^ 2 := by
  have hm : ∀ᵐ w ∂V.law, ∀ g ∈ momentImageClass V, |g w| ≤ B := by
    filter_upwards [hCommon.mono (fun _ hw => hw.2.2)] with w hw
    rintro g ⟨f, hf, rfl⟩
    exact hw f hf
  have hp : ∀ᵐ w ∂V.law, ∀ g ∈ productObservationClass V, |g w| ≤ B ^ 2 := by
    filter_upwards [hCommon.mono (fun _ hw => hw.1),
      hCommon.mono (fun _ hw => hw.2.1)] with w hw hf
    rintro g ⟨h, hh, f, hff, rfl⟩
    dsimp only
    rw [abs_mul, pow_two]
    exact mul_le_mul (hw h hh) (hf f hff) (abs_nonneg _) hBound.1
  have hf : ∀ᵐ w ∂V.law, ∀ g ∈ criticObservationClass V, |g w| ≤ B := by
    filter_upwards [hCommon.mono (fun _ hw => hw.2.1)] with w hw
    rintro g ⟨f, hf, rfl⟩
    exact hw f hf
  filter_upwards [trae_star_envelope V hBound.1 hm,
    trae_star_envelope V (sq_nonneg B) hp, trae_star_envelope V hBound.1 hf] with w hm hp hf
  intro i g hg
  fin_cases i
  · exact (hm g hg).trans (by nlinarith [sq_nonneg B])
  · exact (hp g hg).trans (by linarith [hBound.1])
  · exact (hf g hg).trans (by nlinarith [sq_nonneg B])

/-- Under [the TRAE boundedness and process-measurability assumptions](hyp:hBound)
and [the simultaneous common-null-set bounds](hyp:hCommon), [the localized
clipped-loss process for independently chosen moment, product, and critic star
coordinates has the required measurability](goal). -/
-- @node: trae_vector_process_measurable
lemma trae_vector_process_measurable (B : ℝ) (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B) :
    MeasurableLocalizedLoss V.law
      {v : 𝒲 → Fin 3 → ℝ | ∀ i, (fun w => v w i) ∈
        (![starClass (momentImageClass V), starClass (productObservationClass V),
          starClass (criticObservationClass V)] : Fin 3 → Set (𝒲 → ℝ)) i}
      (fun _ => 0) (traeClippedLoss B) := by
  rw [trae_loss_class_coordinates]
  exact hBound.2.2.2.2.2

/-- If [the hypothesis class is nonempty](hyp:hH) and [the critic class is
nonempty](hyp:hF), then [the zero function belongs to each of the moment,
product-observation, and critic-observation star-coordinate classes](goal). -/
-- @node: trae_vector_coordinate_zero
lemma trae_vector_coordinate_zero (hH : V.H.Nonempty) (hF : V.F.Nonempty) :
    ∀ i : Fin 3, (0 : 𝒲 → ℝ) ∈
      (![starClass (momentImageClass V), starClass (productObservationClass V),
        starClass (criticObservationClass V)] : Fin 3 → Set (𝒲 → ℝ)) i := by
  obtain ⟨h, hh⟩ := hH
  obtain ⟨f, hf⟩ := hF
  have hz {F : Set (𝒲 → ℝ)} (g : 𝒲 → ℝ) (hg : g ∈ F) :
      (0 : 𝒲 → ℝ) ∈ starClass F := ⟨0, ⟨le_rfl, zero_le_one⟩, g, hg, (zero_smul ℝ g).symm⟩
  intro i
  fin_cases i
  · exact hz (V.m f) ⟨f, hf, rfl⟩
  · exact hz _ ⟨h, hh, f, hf, rfl⟩
  · exact hz _ ⟨f, hf, rfl⟩

/-- [Taking the star hull of a function class twice gives the same class as
taking it once](goal). -/
-- @node: trae_star_star
lemma trae_star_star {A : Type*} (F : Set (A → ℝ)) :
    starClass (starClass F) = starClass F := by
  ext g
  constructor
  · rintro ⟨a, ha, f, ⟨b, hb, f, hf, rfl⟩, rfl⟩
    refine ⟨a * b, ⟨mul_nonneg ha.1 hb.1, ?_⟩, f, hf, ?_⟩
    · exact (mul_le_mul_of_nonneg_right ha.2 hb.1).trans (by simpa using hb.2)
    · exact smul_smul a b f
  · intro hg
    exact ⟨1, ⟨zero_le_one, le_rfl⟩, g, hg, (one_smul ℝ g).symm⟩

/-- Under [the TRAE boundedness and process-measurability assumptions](hyp:hBound),
[simultaneous bounds outside a common null set](hyp:hCommon), and [mean-square
continuity of the moment map](hyp:hMSC), [there is a positive constant such that,
for every admissible hypothesis and critic, the sum of the population L² norms
of the moment, hypothesis-times-critic, and critic observations is at most that
constant times the critic's Hilbert-space norm](goal). -/
-- @node: trae_vector_input_norms
lemma trae_vector_input_norms (B : ℝ) (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B)
    (hMSC : MeanSquareContinuity V) :
    ∃ K > 0, ∀ h ∈ V.H, ∀ f ∈ V.F,
      inputL2Norm V.law (V.m f) +
        inputL2Norm V.law (fun w => primalVersion V h (V.xOf w) *
          dualVersion V f (V.zOf w)) +
        inputL2Norm V.law (fun w => dualVersion V f (V.zOf w)) ≤ K * ‖f‖ := by
  obtain ⟨Cm, hm⟩ := hMSC
  let M := max Cm 0
  refine ⟨Real.sqrt M + B + 1, by positivity [hBound.1], ?_⟩
  intro h hh f hf
  have hdual : (∫ w, dualVersion V f (V.zOf w) ^ 2 ∂V.law) = ‖f‖ ^ 2 := by
    calc
      _ = ∫ w, ((f : Lp ℝ 2 V.law) w) ^ 2 ∂V.law := by
        apply integral_congr_ae
        filter_upwards [V.dual_coherent f] with w hw
        exact congrArg (fun x : ℝ => x ^ 2) hw
      _ = _ := by
        simpa only [L2.inner_def, RCLike.inner_apply, conj_trivial, ← pow_two,
          Submodule.norm_coe] using real_inner_self_eq_norm_sq (f : Lp ℝ 2 V.law)
  have hdi : Integrable (fun w => dualVersion V f (V.zOf w) ^ 2) V.law := by
    apply Integrable.congr (Lp.memLp (f : Lp ℝ 2 V.law)).integrable_sq
    filter_upwards [V.dual_coherent f] with w hw
    exact congrArg (fun x : ℝ => x ^ 2) hw.symm
  have hmle : inputL2Norm V.law (V.m f) ≤ Real.sqrt M * ‖f‖ := by
    unfold inputL2Norm
    calc
      _ ≤ Real.sqrt (M * ‖f‖ ^ 2) := Real.sqrt_le_sqrt
        ((hm f hf).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)))
      _ = _ := by rw [Real.sqrt_mul (le_max_right _ _), Real.sqrt_sq (norm_nonneg _)]
  have hple : inputL2Norm V.law (fun w => primalVersion V h (V.xOf w) *
      dualVersion V f (V.zOf w)) ≤ B * ‖f‖ := by
    have hsq : ∀ᵐ w ∂V.law,
        (primalVersion V h (V.xOf w) * dualVersion V f (V.zOf w)) ^ 2 ≤
          B ^ 2 * dualVersion V f (V.zOf w) ^ 2 := by
      filter_upwards [hBound.2.2.1] with w hw
      rw [mul_pow]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hw h hh) 2
    unfold inputL2Norm
    calc
      _ ≤ Real.sqrt (∫ w, B ^ 2 * dualVersion V f (V.zOf w) ^ 2 ∂V.law) := by
        apply Real.sqrt_le_sqrt
        exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => sq_nonneg _)
          (hdi.const_mul _) hsq
      _ = B * ‖f‖ := by
        rw [integral_const_mul, hdual, Real.sqrt_mul (sq_nonneg B),
          Real.sqrt_sq hBound.1, Real.sqrt_sq (norm_nonneg _)]
  have hd : inputL2Norm V.law (fun w => dualVersion V f (V.zOf w)) = ‖f‖ := by
    rw [inputL2Norm, hdual, Real.sqrt_sq (norm_nonneg _)]
  rw [hd]
  nlinarith only [hmle, hple]

end Papers.TsAdaptiveEstimationInference

namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory ProbabilityTheory
open scoped Topology
variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]
  (V : IVWorld 𝒲 𝒳 𝒵) (P : Measure Ω) [IsProbabilityMeasure P]
  (sample : AnalysisSample V P) (split : SampleSplit)

/-- If [the critic observation at the given observation is bounded in absolute
value by B](hyp:hf), then [the clipped loss evaluated at the moment,
hypothesis-times-critic, and critic coordinates equals the TRAE integrand at
that observation](goal). -/
-- @node: trae_clipped_loss_eq_integrand
lemma trae_clipped_loss_eq_integrand (B : ℝ) (w : 𝒲)
    (h : V.Hbar.toSubmodule) (f : V.Qbar.toSubmodule)
    (hf : |dualVersion V f (V.zOf w)| ≤ B) :
    traeClippedLoss B w ![V.m f w,
      primalVersion V h (V.xOf w) * dualVersion V f (V.zOf w),
      dualVersion V f (V.zOf w)] = traeIntegrand V h f w := by
  obtain ⟨hl, hu⟩ := abs_le.mp hf
  change 2 * V.m f w - 2 * (primalVersion V h (V.xOf w) * dualVersion V f (V.zOf w)) -
    (max (-B) (min (dualVersion V f (V.zOf w)) B)) ^ 2 = _
  rw [min_eq_left hu, max_eq_right hl]
  unfold traeIntegrand
  ring

end Papers.TsAdaptiveEstimationInference
