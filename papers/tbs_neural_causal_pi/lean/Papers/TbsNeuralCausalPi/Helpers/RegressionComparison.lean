module
public import Papers.TbsNeuralCausalPi.Setup.Assumptions.Auxiliary
public import Papers.TbsNeuralCausalPi.Helpers.WassersteinSpace
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
/-! # Test functions for the regression Wasserstein comparison

The two contrasts are the outcome times the regression difference, and the
fitted regression times that difference, as in the paper's proof.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped ENNReal NNReal

/-- On a compact metric space, for [a nonnegative constant c](hyp:c), if
[the test function is c-Lipschitz](hyp:hg), then [its expectation under the
first probability law minus its expectation under the second is at most c
times their Wasserstein distance of order one](goal). -/
-- @node: regression_compact_contrast_le
lemma regression_compact_contrast_le {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
    (mu nu : ProbabilityMeasure X) (g : X → ℝ) (c : ℝ≥0)
    (hg : LipschitzWith c g) :
    (∫ x, g x ∂(mu : Measure X)) - (∫ x, g x ∂(nu : Measure X)) ≤
      c * (wasserstein1 (mu : Measure X) (nu : Measure X)).toReal := by
  classical
  by_cases hc : c = 0
  · subst c
    let x₀ := (mu.nonempty).some
    have heq : g = fun _ => g x₀ := by
      funext x
      apply dist_le_zero.mp
      simpa using hg.dist_le_mul x x₀
    rw [heq]
    simp only [integral_const, probReal_univ, one_smul, sub_self, NNReal.coe_zero,
      zero_mul, le_refl]
  · have hcpos : 0 < (c : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hc)
    let h : X → ℝ := fun x => g x / c
    have hh : LipschitzWith 1 h := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [h, Real.dist_eq, ← sub_div, abs_div, abs_of_pos hcpos,
        NNReal.coe_one, one_mul]
      apply (div_le_iff₀ hcpos).2
      simpa only [Real.dist_eq, mul_comm] using hg.dist_le_mul x y
    have hi (a : ProbabilityMeasure X) : Integrable h (a : Measure X) :=
      hh.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hw := Toolkit.Foundations.MeasureTheory.lipschitzContrast_le_wasserstein1
      hh (hi mu) (hi nu)
    rw [← wasserstein1_eq_toolkit] at hw
    have hw' := (ENNReal.ofReal_le_iff_le_toReal (wasserstein1_ne_top_compact mu nu)).1 hw
    simp only [Toolkit.Foundations.MeasureTheory.lipschitzContrast, h, integral_div,
      ← sub_div] at hw'
    exact (div_le_iff₀ hcpos).1 hw' |>.trans_eq (mul_comm _ _)

/-- If [S is compact](hyp:hS), [the first probability law gives S full mass](hyp:hmu),
[the second gives S full mass](hyp:hnu), and the test function is
[Lipschitz on S](hyp:hg) with [nonnegative constant c](hyp:c), then [its
expectation under the first law minus that under the second is at most c
times their Wasserstein distance of order one](goal). -/
-- @node: regression_compact_support_contrast_le
lemma regression_compact_support_contrast_le {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (mu nu : ProbabilityMeasure X) (S : Set X) (hS : IsCompact S)
    (hmu : (mu : Measure X) S = 1) (hnu : (nu : Measure X) S = 1)
    (g : X → ℝ) (c : ℝ≥0) (hg : LipschitzOnWith c g S) :
    (∫ x, g x ∂(mu : Measure X)) - (∫ x, g x ∂(nu : Measure X)) ≤
      c * (wasserstein1 (mu : Measure X) (nu : Measure X)).toReal := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let m := (mu : Measure X).comap ((↑) : S → X)
  let n := (nu : Measure X).comap ((↑) : S → X)
  let : IsProbabilityMeasure m :=
    (Toolkit.Foundations.MeasureTheory.probability_comap_subtype _ S hS.measurableSet hmu).1
  let : IsProbabilityMeasure n :=
    (Toolkit.Foundations.MeasureTheory.probability_comap_subtype _ S hS.measurableSet hnu).1
  have hw := Toolkit.Foundations.MeasureTheory.wasserstein1_subtype_comap
    (mu : Measure X) (nu : Measure X) S hS.measurableSet hmu hnu
  have he := Toolkit.Foundations.MeasureTheory.lipschitzContrast_eq_subtype_comap
    (mu : Measure X) (nu : Measure X) S hS.measurableSet hmu hnu g
  change Toolkit.Foundations.MeasureTheory.lipschitzContrast _ _ g ≤ _
  rw [he, wasserstein1_eq_toolkit, hw]
  exact regression_compact_contrast_le ⟨m, inferInstance⟩ ⟨n, inferInstance⟩
    (fun x : S => g x) c hg.to_restrict

/-- For [a nonnegative Lipschitz constant L](hyp:L) and [a nonnegative magnitude
bound K](hyp:K), if [f is L-Lipschitz](hyp:hf), [the fitted regression is
L-Lipschitz](hyp:hfhat), and [both functions are globally bounded in absolute
value by K](hyp:hb), then [the fitted-minus-true regression difference times
the outcome is Lipschitz on the treatment-outcome box of radius K, in the
sum metric, with constant twice K times the maximum of L and one](goal). -/
-- @node: regression_outcome_test_lipschitz
lemma regression_outcome_test_lipschitz
    (f fhat : ℝ → ℝ) (L : ℝ≥0) (K : ℝ≥0)
    (hf : LipschitzWith L f) (hfhat : LipschitzWith L fhat)
    (hb : RegressionGloballyBounded f fhat K) :
    LipschitzOnWith (2 * K * max L 1)
      (fun x : L1Vec 2 => (fhat (x.ofLp 0) - f (x.ofLp 0)) * x.ofLp 1)
      (boundedCube 2 K) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have ha : |fhat (x.ofLp 0) - f (x.ofLp 0)| ≤ 2 * K :=
    (abs_sub _ _).trans (by linarith [(hb (x.ofLp 0)).1, (hb (x.ofLp 0)).2])
  have hd : |(fhat (x.ofLp 0) - f (x.ofLp 0)) -
      (fhat (y.ofLp 0) - f (y.ofLp 0))| ≤
      2 * L * |x.ofLp 0 - y.ofLp 0| := by
    have h := (hfhat.sub hf).dist_le_mul (x.ofLp 0) (y.ofLp 0)
    simpa only [Real.dist_eq, NNReal.coe_add, two_mul] using h
  have hsplit :
      (fhat (x.ofLp 0) - f (x.ofLp 0)) * x.ofLp 1 -
        (fhat (y.ofLp 0) - f (y.ofLp 0)) * y.ofLp 1 =
      (fhat (x.ofLp 0) - f (x.ofLp 0)) * (x.ofLp 1 - y.ofLp 1) +
        y.ofLp 1 * ((fhat (x.ofLp 0) - f (x.ofLp 0)) -
          (fhat (y.ofLp 0) - f (y.ofLp 0))) := by ring
  rw [Real.dist_eq, hsplit]
  calc
    _ ≤ |fhat (x.ofLp 0) - f (x.ofLp 0)| * |x.ofLp 1 - y.ofLp 1| +
        |y.ofLp 1| * |(fhat (x.ofLp 0) - f (x.ofLp 0)) -
          (fhat (y.ofLp 0) - f (y.ofLp 0))| := by
      simpa only [abs_mul] using abs_add_le
        ((fhat (x.ofLp 0) - f (x.ofLp 0)) * (x.ofLp 1 - y.ofLp 1))
        (y.ofLp 1 * ((fhat (x.ofLp 0) - f (x.ofLp 0)) -
          (fhat (y.ofLp 0) - f (y.ofLp 0))))
    _ ≤ (2 * K) * |x.ofLp 1 - y.ofLp 1| + K * (2 * L * |x.ofLp 0 - y.ofLp 0|) := by
      gcongr
      exact hy 1
    _ ≤ (2 * K * max (L : ℝ) 1) *
        (|x.ofLp 0 - y.ofLp 0| + |x.ofLp 1 - y.ofLp 1|) := by
      have ht := mul_le_mul_of_nonneg_right (le_max_left (L : ℝ) 1)
        (abs_nonneg (x.ofLp 0 - y.ofLp 0))
      have hy' := mul_le_mul_of_nonneg_right (le_max_right (L : ℝ) 1)
        (abs_nonneg (x.ofLp 1 - y.ofLp 1))
      nlinarith [mul_nonneg K.coe_nonneg (sub_nonneg.mpr ht),
        mul_nonneg K.coe_nonneg (sub_nonneg.mpr hy')]
    _ = _ := by
      simp only [PiLp.dist_eq_of_L1, Fin.sum_univ_two, Real.dist_eq,
        NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_max, NNReal.coe_one]

/-- For [a nonnegative Lipschitz constant L](hyp:L) and [a nonnegative magnitude
bound K](hyp:K), if [f is L-Lipschitz](hyp:hf), [the fitted regression is
L-Lipschitz](hyp:hfhat), and [both are globally bounded in absolute value by
K](hyp:hb), then [the fitted-minus-true regression difference multiplied by
the fitted regression is globally Lipschitz with constant four times L times K](goal). -/
-- @node: regression_fitted_test_lipschitz
lemma regression_fitted_test_lipschitz
    (f fhat : ℝ → ℝ) (L : ℝ≥0) (K : ℝ≥0)
    (hf : LipschitzWith L f) (hfhat : LipschitzWith L fhat)
    (hb : RegressionGloballyBounded f fhat K) :
    LipschitzWith (4 * L * K) (fun t => (fhat t - f t) * fhat t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have ha : |fhat x - f x| ≤ 2 * K :=
    (abs_sub _ _).trans (by linarith [(hb x).1, (hb x).2])
  have hd : |(fhat x - f x) - (fhat y - f y)| ≤ 2 * L * |x-y| := by
    simpa only [Real.dist_eq, NNReal.coe_add, two_mul] using
      (hfhat.sub hf).dist_le_mul x y
  have hh : |fhat x - fhat y| ≤ L * |x-y| := by
    simpa only [Real.dist_eq] using hfhat.dist_le_mul x y
  have hsplit : (fhat x - f x) * fhat x - (fhat y - f y) * fhat y =
      (fhat x - f x) * (fhat x - fhat y) +
        fhat y * ((fhat x - f x) - (fhat y - f y)) := by ring
  rw [Real.dist_eq, hsplit]
  calc
    _ ≤ |fhat x - f x| * |fhat x - fhat y| +
        |fhat y| * |(fhat x - f x) - (fhat y - f y)| := by
      simpa only [abs_mul] using abs_add_le
        ((fhat x - f x) * (fhat x - fhat y))
        (fhat y * ((fhat x - f x) - (fhat y - f y)))
    _ ≤ (2 * K) * (L * |x-y|) + K * (2 * L * |x-y|) := by
      gcongr
      exact (hb y).2
    _ = _ := by simp only [NNReal.coe_mul, NNReal.coe_ofNat, Real.dist_eq]; ring

/-- If [the treatment is measurable](hyp:hT), [the treatment weight is
measurable](hyp:ha), [the outcome is integrable](hyp:hY), [the weighted outcome
is integrable](hyp:haY), and [f evaluated at treatment equals the conditional
mean outcome given treatment almost surely](hyp:hreg), then [the integral of
the weighted outcome equals the integral of the same weight times the regression](goal). -/
-- @node: regression_weighted_outcome_integral
lemma regression_weighted_outcome_integral {X Z : Type*}
    [mX : MeasurableSpace X] [mZ : MeasurableSpace Z]
    (mu : Measure X) [IsFiniteMeasure mu] (T : X → Z) (Y : X → ℝ) (hT : Measurable T)
    (a f : Z → ℝ) (ha : Measurable a) (hY : Integrable Y mu)
    (haY : Integrable (fun x => a (T x) * Y x) mu)
    (hreg : (fun x => f (T x)) =ᵐ[mu]
      mu[Y | MeasurableSpace.comap T mZ]) :
    (∫ x, a (T x) * Y x ∂mu) = ∫ x, a (T x) * f (T x) ∂mu := by
  let m := MeasurableSpace.comap T mZ
  have hm : m ≤ mX := hT.comap_le
  have haT : StronglyMeasurable[m] (fun x => a (T x)) := by
    first | fun_prop | exact (ha.comp (measurable_iff_comap_le.mpr le_rfl)).stronglyMeasurable
  calc
    _ = ∫ x, mu[fun x => a (T x) * Y x | m] x ∂mu := (integral_condExp hm).symm
    _ = ∫ x, a (T x) * mu[Y | m] x ∂mu :=
      integral_congr_ae (condExp_mul_of_stronglyMeasurable_left haT haY hY)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hreg] with x hx using congrArg (a (T x) * ·) hx.symm

/-- For [a nonnegative Lipschitz constant L](hyp:L), assume [K is positive](hyp:hK),
[f and the fitted regression are globally L-Lipschitz measurable conditional
mean versions under the second and first laws respectively](hyp:hregression),
[both regressions are globally bounded in absolute value by K](hyp:hbounded),
and [both laws give full mass to the treatment-outcome box of radius K](hyp:hsupport).
Then [the mean squared regression difference under the second law is at most
four times L times K plus twice K times the maximum of L and one, multiplied
by the Wasserstein distance of order one between the laws in the sum metric](goal). -/
lemma regression_gap_le_wasserstein_global (mu nu : ProbabilityMeasure (L1Vec 2))
    (f fhat : ℝ → ℝ) (L : ℝ≥0) (K : ℝ) (hK : 0 < K)
    (hregression : LipschitzRegressionVersionsGlobal (mu : Measure (L1Vec 2)) (nu : Measure (L1Vec 2)) f
      fhat L)
    (hbounded : RegressionGloballyBounded f fhat K)
    (hsupport : RegressionLawsSupportedInBox (mu : Measure (L1Vec 2)) (nu : Measure (L1Vec 2)) K) :
    (∫ x : L1Vec 2, (f (x.ofLp 0) - fhat (x.ofLp 0))^2 ∂(nu : Measure (L1Vec 2))) ≤
      (4 * L * K + 2 * K * max (L : ℝ) 1) *
        (wasserstein1 (mu : Measure (L1Vec 2)) (nu : Measure (L1Vec 2))).toReal := by
  let : BorelSpace (L1Vec 2) := ⟨rfl⟩
  obtain ⟨hf, hfhat, hfm, hfhatm, hreg, hreghat⟩ := hregression
  let k : ℝ≥0 := ⟨K, hK.le⟩
  let T : L1Vec 2 → ℝ := fun x => x.ofLp 0
  let Y : L1Vec 2 → ℝ := fun x => x.ofLp 1
  let a : ℝ → ℝ := fun t => fhat t - f t
  let g : L1Vec 2 → ℝ := fun x => a (T x) * Y x
  let H : L1Vec 2 → ℝ := fun x => a (T x) * fhat (T x)
  have hT : Continuous T := by fun_prop
  have hY : Continuous Y := by fun_prop
  have ha : Continuous a := hfhat.continuous.sub hf.continuous
  have hg : Continuous g := (ha.comp hT).mul hY
  have hH : Continuous H := (ha.comp hT).mul (hfhat.continuous.comp hT)
  have hi (rho : ProbabilityMeasure (L1Vec 2))
      (hrho : (rho : Measure (L1Vec 2)) (boundedCube 2 K) = 1)
      (u : L1Vec 2 → ℝ) (hu : Continuous u) :
      Integrable u (rho : Measure (L1Vec 2)) := by
    have hmem : ∀ᵐ x ∂(rho : Measure (L1Vec 2)), x ∈ boundedCube 2 K :=
      (ae_mem_iff_measure_eq (boundedCube_isCompact 2 K).measurableSet.nullMeasurableSet).2
        (by simpa using hrho)
    have hi := hu.continuousOn.integrableOn_compact
      (μ := (rho : Measure (L1Vec 2))) (boundedCube_isCompact 2 K)
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hmem] at hi
  have hgm : (∫ x, g x ∂(mu : Measure (L1Vec 2))) =
      ∫ x, H x ∂(mu : Measure (L1Vec 2)) :=
    regression_weighted_outcome_integral (mu : Measure (L1Vec 2)) T Y hT.measurable
      a fhat ha.measurable (hi mu hsupport.1 Y hY) (hi mu hsupport.1 g hg) hreghat
  have hgn : (∫ x, g x ∂(nu : Measure (L1Vec 2))) =
      ∫ x, a (T x) * f (T x) ∂(nu : Measure (L1Vec 2)) :=
    regression_weighted_outcome_integral (nu : Measure (L1Vec 2)) T Y hT.measurable
      a f ha.measurable (hi nu hsupport.2 Y hY) (hi nu hsupport.2 g hg) hreg
  have hgLip : LipschitzOnWith (2 * k * max L 1) g (boundedCube 2 K) :=
    regression_outcome_test_lipschitz f fhat L k hf hfhat hbounded
  have hHLip : LipschitzWith (4 * L * k) (fun t => a t * fhat t) :=
    regression_fitted_test_lipschitz f fhat L k hf hfhat hbounded
  have hHLip' : LipschitzWith (4 * L * k) H := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact (hHLip.dist_le_mul (T x) (T y)).trans
      (mul_le_mul_of_nonneg_left (PiLp.dist_apply_le x y 0) (by positivity))
  have hgc := regression_compact_support_contrast_le mu nu (boundedCube 2 K)
    (boundedCube_isCompact 2 K) hsupport.1 hsupport.2 g (2 * k * max L 1) hgLip
  have hhc := regression_compact_support_contrast_le mu nu (boundedCube 2 K)
    (boundedCube_isCompact 2 K) hsupport.1 hsupport.2 (fun x => -H x)
    (4 * L * k) hHLip'.neg.lipschitzOnWith
  simp only [integral_neg] at hhc
  have hiH := hi nu hsupport.2 H hH
  have hiF := hi nu hsupport.2 (fun x => a (T x) * f (T x))
    ((ha.comp hT).mul (hf.continuous.comp hT))
  have hsquare :
      (∫ x : L1Vec 2, (f (T x) - fhat (T x))^2 ∂(nu : Measure (L1Vec 2))) =
      (∫ x, H x ∂(nu : Measure (L1Vec 2))) -
        ∫ x, a (T x) * f (T x) ∂(nu : Measure (L1Vec 2)) := by
    rw [← integral_sub hiH hiF]
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [H, a]
    ring
  rw [hgm, hgn] at hgc
  change (∫ x, (f (T x) - fhat (T x))^2 ∂(nu : Measure (L1Vec 2))) ≤ _
  rw [hsquare]
  change _ ≤ (2 * K * max (L : ℝ) 1) * _ at hgc
  change -_ - -_ ≤ (4 * (L : ℝ) * K) * _ at hhc
  linarith

/-- For [a nonnegative Lipschitz constant L](hyp:L), if [K is positive](hyp:hK),
[the two regressions are L-Lipschitz on the interval from minus K to K and
represent the conditional means under the second and first laws respectively](hyp:hregression),
[both regressions are bounded in absolute value by K on that interval](hyp:hbounded),
and [both laws give full mass to the treatment-outcome box of radius K](hyp:hsupport),
then [there exist globally L-Lipschitz measurable regression versions with the
same conditional-mean identities, globally bounded by K, which agree with the
original regressions throughout that interval](goal). -/
lemma regression_versions_extend_from_box
    (mu nu : ProbabilityMeasure (L1Vec 2)) (f fhat : ℝ → ℝ)
    (L : ℝ≥0) (K : ℝ) (hK : 0 < K)
    (hregression : LipschitzRegressionVersions (mu : Measure (L1Vec 2))
      (nu : Measure (L1Vec 2)) f fhat L K)
    (hbounded : RegressionBounded f fhat K)
    (hsupport : RegressionLawsSupportedInBox (mu : Measure (L1Vec 2))
      (nu : Measure (L1Vec 2)) K) :
    ∃ F Fhat : ℝ → ℝ,
      LipschitzRegressionVersionsGlobal (mu : Measure (L1Vec 2))
        (nu : Measure (L1Vec 2)) F Fhat L ∧
      RegressionGloballyBounded F Fhat K ∧
      ∀ t ∈ Set.Icc (-K) K, F t = f t ∧ Fhat t = fhat t := by
  obtain ⟨hf, hfhat, hreg, hreghat⟩ := hregression
  let clamp := Set.projIcc (-K) K (by linarith : -K ≤ K)
  let F : ℝ → ℝ := fun t => f (clamp t).val
  let Fhat : ℝ → ℝ := fun t => fhat (clamp t).val
  have hF : LipschitzWith L F := by
    simpa only [mul_one, Function.comp_def, Set.domRestrict, F, clamp] using hf.to_restrict.comp (LipschitzWith.projIcc (by linarith : -K ≤ K))
  have hFhat : LipschitzWith L Fhat := by
    simpa only [mul_one, Function.comp_def, Set.domRestrict, Fhat, clamp] using hfhat.to_restrict.comp (LipschitzWith.projIcc (by linarith : -K ≤ K))
  have heq (t : ℝ) (ht : t ∈ Set.Icc (-K) K) : F t = f t ∧ Fhat t = fhat t := by
    simp [F, Fhat, clamp, Set.projIcc_of_mem (by linarith : -K ≤ K) ht]
  have hmem (rho : ProbabilityMeasure (L1Vec 2))
      (hrho : (rho : Measure (L1Vec 2)) (boundedCube 2 K) = 1) :
      ∀ᵐ x ∂(rho : Measure (L1Vec 2)), x ∈ boundedCube 2 K :=
    (ae_mem_iff_measure_eq (boundedCube_isCompact 2 K).measurableSet.nullMeasurableSet).2
      (by simpa using hrho)
  refine ⟨F, Fhat, ⟨hF, hFhat, hF.continuous.measurable,
    hFhat.continuous.measurable, ?_, ?_⟩, ?_, heq⟩
  · filter_upwards [hmem nu hsupport.2, hreg] with x hx hregx
    exact ((heq (x.ofLp 0) (abs_le.mp (hx 0))).1).trans hregx
  · filter_upwards [hmem mu hsupport.1, hreghat] with x hx hregx
    exact ((heq (x.ofLp 0) (abs_le.mp (hx 0))).2).trans hregx
  · intro t
    exact hbounded (clamp t).val (clamp t).property

-- @node: lem:lip-condition
/-- For [a nonnegative Lipschitz constant L](hyp:L), assume [K is positive](hyp:hK),
[the two regressions are L-Lipschitz on the interval from minus K to K and
represent the conditional means under the second and first laws respectively](hyp:hregression),
[both regressions are bounded in absolute value by K on that interval](hyp:hbounded),
and [both laws give full mass to the treatment-outcome box of radius K](hyp:hsupport).
Then [the mean squared regression difference under the second law is at most
four times L times K plus twice K times the maximum of L and one, multiplied
by the Wasserstein distance of order one between the laws in the sum metric](goal). -/
lemma regression_gap_le_wasserstein (mu nu : ProbabilityMeasure (L1Vec 2))
    (f fhat : ℝ → ℝ) (L : ℝ≥0) (K : ℝ) (hK : 0 < K)
    (hregression : LipschitzRegressionVersions (mu : Measure (L1Vec 2))
      (nu : Measure (L1Vec 2)) f fhat L K)
    (hbounded : RegressionBounded f fhat K)
    (hsupport : RegressionLawsSupportedInBox (mu : Measure (L1Vec 2))
      (nu : Measure (L1Vec 2)) K) :
    (∫ x : L1Vec 2, (f (x.ofLp 0) - fhat (x.ofLp 0))^2 ∂(nu : Measure (L1Vec 2))) ≤
      (4 * L * K + 2 * K * max (L : ℝ) 1) *
        (wasserstein1 (mu : Measure (L1Vec 2)) (nu : Measure (L1Vec 2))).toReal := by
  obtain ⟨F, Fhat, hreg, hb, heq⟩ :=
    regression_versions_extend_from_box mu nu f fhat L K hK hregression hbounded hsupport
  have hmem : ∀ᵐ x ∂(nu : Measure (L1Vec 2)), x ∈ boundedCube 2 K :=
    (ae_mem_iff_measure_eq (boundedCube_isCompact 2 K).measurableSet.nullMeasurableSet).2
      (by simpa using hsupport.2)
  have hint : (∫ x : L1Vec 2, (f (x.ofLp 0) - fhat (x.ofLp 0))^2
      ∂(nu : Measure (L1Vec 2))) =
      ∫ x : L1Vec 2, (F (x.ofLp 0) - Fhat (x.ofLp 0))^2
        ∂(nu : Measure (L1Vec 2)) := by
    apply integral_congr_ae
    filter_upwards [hmem] with x hx
    obtain ⟨hF, hFhat⟩ := heq (x.ofLp 0) (abs_le.mp (hx 0))
    rw [hF, hFhat]
  rw [hint]
  exact regression_gap_le_wasserstein_global mu nu F Fhat L K hK hreg hb hsupport

end Papers.TbsNeuralCausalPi
