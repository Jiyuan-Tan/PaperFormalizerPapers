module
public import Mathlib.Probability.Kernel.MeasurableLIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
/-! Measurable integration against a Borel L1-valued selection.

A Borel measurable selection into a possibly nonseparable L1 space need not
have jointly measurable chosen representatives. Its positive and negative
parts nevertheless define measure kernels: evaluation on each measurable set
is a continuous set integral. This is the appropriate interface for smoothing
by a jointly measurable density, and requires no separability assumption.
-/
public section
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal


variable {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]

/-- For [the reference measure μ](hyp:μ), [the measurable structure on integrable real functions modulo almost-everywhere equality](goal) consists of their Borel sets. -/
noncomputable local instance (μ : Measure X) : MeasurableSpace (Lp ℝ 1 μ) := borel _
/-- [The measurable structure on integrable real functions modulo almost-everywhere equality is the Borel structure](goal). -/
local instance (μ : Measure X) : BorelSpace (Lp ℝ 1 μ) := ⟨rfl⟩
/-- For [the reference measure μ](hyp:μ), [the measurable structure on square-integrable real functions modulo almost-everywhere equality](goal) consists of their Borel sets. -/
noncomputable local instance (μ : Measure X) : MeasurableSpace (Lp ℝ 2 μ) := borel _
/-- [The measurable structure on square-integrable real functions modulo almost-everywhere equality is the Borel structure](goal). -/
local instance (μ : Measure X) : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩

/-- For [a reference measure μ](hyp:μ), [the positive-part kernel](goal) assigns to each integrable function the measure with density equal to its positive part relative to μ. -/
noncomputable def rdivL1PositiveKernel (μ : Measure X) : Kernel (Lp ℝ 1 μ) X where
  toFun f := μ.withDensity (fun x => ENNReal.ofReal (f x))
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    have he (f : Lp ℝ 1 μ) :
        μ.withDensity (fun x => ENNReal.ofReal (f x)) s =
          ENNReal.ofReal (∫ x in s, (Lp.posPart f) x ∂μ) := by
      rw [withDensity_apply _ hs]
      rw [ofReal_integral_eq_lintegral_ofReal
        ((L1.integrable_coeFn (Lp.posPart f)).restrict) (by
          filter_upwards [ae_restrict_of_ae (Lp.coeFn_posPart f)] with x hx
          rw [hx]
          exact le_max_right _ _)]
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_of_ae (Lp.coeFn_posPart f)] with x hx
      rw [hx]
      simp
    simp_rw [he]
    exact ((continuous_setIntegral s).comp Lp.continuous_posPart).measurable.ennreal_ofReal

/-- [The measure obtained by weighting μ by the positive part of any integrable function is finite](goal). -/
lemma rdivL1PositiveKernel_finite (μ : Measure X) (f : Lp ℝ 1 μ) :
    IsFiniteMeasure (rdivL1PositiveKernel μ f) := by
  refine ⟨?_⟩
  change μ.withDensity (fun x => ENNReal.ofReal (f x)) Set.univ < ∞
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  exact lt_of_le_of_lt (lintegral_ofReal_le_lintegral_enorm _)
    (L1.integrable_coeFn f).2

/-- If [every measure in a kernel is finite](hyp:hκ) and [the nonnegative extended-real integrand is jointly measurable](hyp:hf), then [its integral against the parameter-dependent kernel measure is measurable in the parameter](goal). -/
lemma rdiv_measurable_lintegral_of_finite_sections
    (κ : Kernel A X) (hκ : ∀ a, IsFiniteMeasure (κ a))
    {f : A × X → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun a => ∫⁻ x, f (a, x) ∂κ a) := by
  let F : ℕ → SimpleFunc (A × X) ℝ≥0∞ := SimpleFunc.eapprox f
  have h (a : A) (x : X) : (⨆ n, F n (a, x)) = f (a, x) :=
    SimpleFunc.iSup_eapprox_apply hf (a, x)
  simp_rw [← h]
  have he (a : A) : (∫⁻ x, ⨆ n, F n (a, x) ∂κ a) =
      ⨆ n, ∫⁻ x, F n (a, x) ∂κ a := by
    apply lintegral_iSup
    · intro n
      exact (F n).measurable.comp measurable_prodMk_left
    · intro i j hij x
      exact SimpleFunc.monotone_eapprox f hij _
  simp_rw [he]
  apply Measurable.iSup
  intro n
  refine SimpleFunc.induction
    (motive := fun g => Measurable (fun a => ∫⁻ x, g (a, x) ∂κ a)) ?_ ?_ (F n)
  · intro c t ht
    simp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise, SimpleFunc.coe_const,
      SimpleFunc.coe_zero, Set.piecewise_eq_indicator]
    have hm := Kernel.measurable_kernel_prodMk_left_of_finite (κ := κ) ht hκ
    have heq (a : A) :
        (∫⁻ x, t.indicator (fun _ => c) (a, x) ∂κ a) =
          c * κ a (Prod.mk a ⁻¹' t) := by
      change (∫⁻ x, (Prod.mk a ⁻¹' t).indicator (fun _ => c) x ∂κ a) = _
      rw [lintegral_indicator (measurable_prodMk_left ht), lintegral_const]
      simp
    change Measurable (fun a => ∫⁻ x, t.indicator (fun _ => c) (a, x) ∂κ a)
    simp_rw [heq]
    exact hm.const_mul c
  · intro g₁ g₂ _ hm₁ hm₂
    simp only [SimpleFunc.coe_add, Pi.add_apply]
    have heq (a : A) :
        (∫⁻ x, g₁ (a, x) + g₂ (a, x) ∂κ a) =
          (∫⁻ x, g₁ (a, x) ∂κ a) + ∫⁻ x, g₂ (a, x) ∂κ a := by
      apply lintegral_add_left
      exact g₁.measurable.comp measurable_prodMk_left
    simp_rw [heq]
    exact hm₁.add hm₂

/-- If [a selection of integrable functions is Borel measurable](hyp:hF) and [a nonnegative extended-real weight is jointly measurable](hyp:hw), then [integrating the weight against the positive-part density measure of the selected function gives a measurable function of the parameter](goal). -/
lemma rdiv_measurable_selected_positive_integral
    (μ : Measure X) {F : A → Lp ℝ 1 μ} (hF : Measurable F)
    {w : A × X → ℝ≥0∞} (hw : Measurable w) :
    Measurable (fun a => ∫⁻ x, w (a, x)
      ∂μ.withDensity (fun x => ENNReal.ofReal (F a x))) := by
  let κ : Kernel A X :=
    { toFun := fun a => rdivL1PositiveKernel μ (F a)
      measurable' := (rdivL1PositiveKernel μ).measurable.comp hF }
  exact rdiv_measurable_lintegral_of_finite_sections κ
    (fun a => rdivL1PositiveKernel_finite μ (F a)) hw

/-- Given [a reference measure μ](hyp:μ), [a family F of integrable functions](hyp:F), [a real weight w depending on the parameter and input](hyp:w), and [a parameter value a](hyp:a), [the selected L1 integral](goal) is the difference of the real-valued nonnegative integrals of the positive part of w against the positive- and negative-part density measures of F at a. -/
noncomputable def rdivSelectedL1Integral (μ : Measure X)
    (F : A → Lp ℝ 1 μ) (w : A × X → ℝ) (a : A) : ℝ :=
  (∫⁻ x, ENNReal.ofReal (w (a, x))
    ∂μ.withDensity (fun x => ENNReal.ofReal (F a x))).toReal -
  (∫⁻ x, ENNReal.ofReal (w (a, x))
    ∂μ.withDensity (fun x => ENNReal.ofReal ((-F a) x))).toReal

/-- If [the selection of integrable functions is Borel measurable](hyp:hF) and [the real weight is jointly measurable](hyp:hw), then [the selected L1 integral is measurable in its parameter](goal). -/
lemma rdivSelectedL1Integral_measurable (μ : Measure X)
    {F : A → Lp ℝ 1 μ} (hF : Measurable F)
    {w : A × X → ℝ} (hw : Measurable w) :
    Measurable (rdivSelectedL1Integral μ F w) :=
  (rdiv_measurable_selected_positive_integral μ hF hw.ennreal_ofReal).ennreal_toReal.sub
    (rdiv_measurable_selected_positive_integral μ
      (continuous_neg.measurable.comp hF) hw.ennreal_ofReal).ennreal_toReal

/-- If [f is measurable](hyp:hf), [w is measurable](hyp:hw), and [w is everywhere nonnegative](hyp:hw0), then [the real value of the nonnegative integral of w against the positive-part density measure of f equals the ordinary integral of the positive part of f times w](goal). -/
lemma rdiv_positive_weight_integral (μ : Measure X) (f w : X → ℝ)
    (hf : Measurable f) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) :
    (∫⁻ x, ENNReal.ofReal (w x)
      ∂μ.withDensity (fun x => ENNReal.ofReal (f x))).toReal =
      ∫ x, max (f x) 0 * w x ∂μ := by
  rw [lintegral_withDensity_eq_lintegral_mul μ hf.ennreal_ofReal hw.ennreal_ofReal]
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun x => mul_nonneg (le_max_right _ _) (hw0 x))
    ((hf.max measurable_const).mul hw).aestronglyMeasurable]
  congr 1
  apply lintegral_congr_ae
  exact ae_of_all _ fun x => by
    simp only [Pi.mul_apply, ENNReal.ofReal_mul' (hw0 x)]
    simp

/-- At a fixed parameter, if [the weight is measurable](hyp:hw), [the weight is everywhere nonnegative](hyp:hw0), and [the selected function times the weight is integrable](hyp:hi), then [the selected L1 integral equals the ordinary integral of that product](goal). -/
lemma rdivSelectedL1Integral_eq (μ : Measure X)
    (F : A → Lp ℝ 1 μ) (w : A × X → ℝ) (a : A)
    (hw : Measurable (fun x => w (a, x))) (hw0 : ∀ x, 0 ≤ w (a, x))
    (hi : Integrable (fun x => F a x * w (a, x)) μ) :
    rdivSelectedL1Integral μ F w a = ∫ x, F a x * w (a, x) ∂μ := by
  have hpos : Integrable (fun x => max (F a x) 0 * w (a, x)) μ := by
    apply hi.norm.mono' (((Lp.stronglyMeasurable (F a)).measurable.max
      measurable_const).mul hw).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      change |max (F a x) 0 * w (a, x)| ≤ |F a x * w (a, x)|
      rw [abs_mul, abs_mul, abs_of_nonneg (le_max_right _ _),
        abs_of_nonneg (hw0 x)]
      exact mul_le_mul_of_nonneg_right (max_le (le_abs_self _) (abs_nonneg _)) (hw0 x)
  have hneg : Integrable (fun x => max (-F a x) 0 * w (a, x)) μ := by
    apply hi.norm.mono' (((Lp.stronglyMeasurable (F a)).measurable.neg.max
      measurable_const).mul hw).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      change |max (-F a x) 0 * w (a, x)| ≤ |F a x * w (a, x)|
      rw [abs_mul, abs_mul, abs_of_nonneg (le_max_right _ _),
        abs_of_nonneg (hw0 x)]
      exact mul_le_mul_of_nonneg_right (max_le (neg_le_abs _) (abs_nonneg _)) (hw0 x)
  unfold rdivSelectedL1Integral
  rw [rdiv_positive_weight_integral μ _ _ (Lp.stronglyMeasurable _).measurable hw hw0,
    rdiv_positive_weight_integral μ _ _ (Lp.stronglyMeasurable _).measurable hw hw0]
  have he : (∫ x, max ((-F a) x) 0 * w (a, x) ∂μ) =
      ∫ x, max (-F a x) 0 * w (a, x) ∂μ := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_neg (F a)] with x hx
    simp only [hx, Pi.neg_apply]
  rw [he, ← integral_sub hpos hneg]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    have hm : max (F a x) 0 - max (-F a x) 0 = F a x := by
      rcases le_total 0 (F a x) with hx | hx
      · rw [max_eq_left hx, max_eq_right (by linarith)]
        ring
      · rw [max_eq_right hx, max_eq_left (by linarith)]
        ring
    dsimp only
    rw [← sub_mul, hm]

/-- For [a probability measure μ](hyp:μ), [the continuous linear inclusion from square-integrable to integrable functions](goal) preserves the represented function and has norm at most one. -/
noncomputable def rdivL2ToL1 (μ : Measure X) [IsProbabilityMeasure μ] :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 1 μ :=
  LinearMap.mkContinuous
    { toFun := fun f => ((Lp.memLp f).integrable (by norm_num)).toL1 f
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [Integrable.coeFn_toL1 ((Lp.memLp (f + g)).integrable (by norm_num)),
          Integrable.coeFn_toL1 ((Lp.memLp f).integrable (by norm_num)),
          Integrable.coeFn_toL1 ((Lp.memLp g).integrable (by norm_num)),
          Lp.coeFn_add f g,
          Lp.coeFn_add (((Lp.memLp f).integrable (by norm_num)).toL1 f)
            (((Lp.memLp g).integrable (by norm_num)).toL1 g)] with x hfg hf hg hsum hsum1
        simp only [hfg, hsum1, hf, hg, hsum, Pi.add_apply]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [Integrable.coeFn_toL1 ((Lp.memLp (c • f)).integrable (by norm_num)),
          Integrable.coeFn_toL1 ((Lp.memLp f).integrable (by norm_num)),
          Lp.coeFn_smul c f,
          Lp.coeFn_smul c (((Lp.memLp f).integrable (by norm_num)).toL1 f)] with x hcf hf hsm hsm1
        simp only [RingHom.id_apply, hcf, hsm1, hf, hsm, Pi.smul_apply] }
    1 (by
      intro f
      change ‖((Lp.memLp f).integrable (by norm_num)).toL1 f‖ ≤ 1 * ‖f‖
      rw [one_mul, Lp.norm_def, Lp.norm_def,
        eLpNorm_congr_ae (Integrable.coeFn_toL1 ((Lp.memLp f).integrable (by norm_num)))]
      exact ENNReal.toReal_mono (Lp.memLp f).2.ne
        (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
          (Lp.aestronglyMeasurable f)))

/-- [The L2-to-L1 inclusion of a square-integrable function agrees with that function almost everywhere under the probability measure μ](goal). -/
lemma rdivL2ToL1_coe (μ : Measure X) [IsProbabilityMeasure μ] (f : Lp ℝ 2 μ) :
    rdivL2ToL1 μ f =ᵐ[μ] f :=
  Integrable.coeFn_toL1 ((Lp.memLp f).integrable (by norm_num))

/-- Given [a probability measure μ](hyp:μ), [a family F of square-integrable functions](hyp:F), and [a real weight w depending on the parameter and input](hyp:w), [the selected L2 integral](goal) is the selected L1 integral after applying the L2-to-L1 inclusion to each member of F. -/
noncomputable def rdivSelectedL2Integral (μ : Measure X) [IsProbabilityMeasure μ]
    (F : A → Lp ℝ 2 μ) (w : A × X → ℝ) : A → ℝ :=
  rdivSelectedL1Integral μ (fun a => rdivL2ToL1 μ (F a)) w

/-- If [the selection of square-integrable functions is Borel measurable](hyp:hF) and [the real weight is jointly measurable](hyp:hw), then [the selected L2 integral is measurable in its parameter](goal). -/
lemma rdivSelectedL2Integral_measurable (μ : Measure X) [IsProbabilityMeasure μ]
    {F : A → Lp ℝ 2 μ} (hF : Measurable F)
    {w : A × X → ℝ} (hw : Measurable w) :
    Measurable (rdivSelectedL2Integral μ F w) :=
  rdivSelectedL1Integral_measurable μ ((rdivL2ToL1 μ).continuous.measurable.comp hF) hw

/-- At a fixed parameter, if [the weight is measurable](hyp:hw), [the weight is everywhere nonnegative](hyp:hw0), and [the selected square-integrable function times the weight is integrable](hyp:hi), then [the selected L2 integral equals the ordinary integral of that product](goal). -/
lemma rdivSelectedL2Integral_eq (μ : Measure X) [IsProbabilityMeasure μ]
    (F : A → Lp ℝ 2 μ) (w : A × X → ℝ) (a : A)
    (hw : Measurable (fun x => w (a, x))) (hw0 : ∀ x, 0 ≤ w (a, x))
    (hi : Integrable (fun x => F a x * w (a, x)) μ) :
    rdivSelectedL2Integral μ F w a = ∫ x, F a x * w (a, x) ∂μ := by
  have he : (fun x => rdivL2ToL1 μ (F a) x * w (a, x)) =ᵐ[μ]
      (fun x => F a x * w (a, x)) :=
    (rdivL2ToL1_coe μ (F a)).mono fun x hx => by simpa only using congrArg (fun y => y * w (a, x)) hx
  exact (rdivSelectedL1Integral_eq μ _ w a hw hw0 (hi.congr he.symm)).trans
    (integral_congr_ae he)

end Papers.TsAdaptiveEstimationInference
