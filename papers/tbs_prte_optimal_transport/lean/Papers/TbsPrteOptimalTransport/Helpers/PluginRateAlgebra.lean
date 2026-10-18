module
public import Papers.TbsPrteOptimalTransport.Helpers.ConnectedIV
public import Causalean.Stat.EmpiricalProcess.CrossFitRate
/-!
# Stochastic assembly of the continuous plug-in nuisance errors

The paper's nuisance assumptions use strict exceedance events, so they also
cover a zero nuisance rate with exactly zero error. The final rate includes
the positive evaluation-sample rate. This permits conversion to the library's
weak-exceedance stochastic order without excluding zero nuisance rates.
-/
public section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace Papers.TbsPrteOptimalTransport

-- @node: isBigOp_of_eq_on_high_probability_event
/-- If [two error sequences agree on each designated good event](hyp:heq),
[the measure of the complementary events tends to zero](hyp:hbad), and
[the second error is bounded in probability at a given rate](hyp:hg),
[the first error is bounded in probability at that same rate](goal). -/
lemma isBigOp_of_eq_on_high_probability_event
    {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {f g : ℕ → A → ℝ} {r : ℕ → ℝ} (good : ℕ → Set A)
    (heq : ∀ n a, a ∈ good n → f n a = g n a)
    (hbad : Tendsto (fun n => μ (good n)ᶜ) atTop (𝓝 0))
    (hg : Causalean.Stat.IsBigOp g r μ) : Causalean.Stat.IsBigOp f r μ := by
  intro δ hδ
  by_cases htop : δ = ⊤
  · exact ⟨1, one_pos, Eventually.of_forall (fun n => by simp [htop])⟩
  have hhalf : 0 < δ / 2 := ENNReal.div_pos hδ.ne' (by norm_num)
  obtain ⟨K, hK, htail⟩ := hg (δ / 2) hhalf
  have hb : ∀ᶠ n in atTop, μ (good n)ᶜ ≤ δ / 2 :=
    (hbad.eventually (eventually_lt_nhds hhalf)).mono (fun _ h => h.le)
  refine ⟨K, hK, ?_⟩
  filter_upwards [htail, hb] with n hn hbn
  calc
    μ {a | K * r n ≤ ‖f n a‖} ≤
        μ ({a | K * r n ≤ ‖g n a‖} ∪ (good n)ᶜ) := by
      apply measure_mono
      intro a ha
      by_cases h : a ∈ good n
      · apply Or.inl
        change K * r n ≤ ‖g n a‖
        change K * r n ≤ ‖f n a‖ at ha
        rw [heq n a h] at ha
        exact ha
      · exact Or.inr h
    _ ≤ μ {a | K * r n ≤ ‖g n a‖} + μ (good n)ᶜ := measure_union_le _ _
    _ ≤ δ / 2 + δ / 2 := add_le_add hn hbn
    _ = δ := ENNReal.add_halves δ

-- @node: boundedAtRate_isBigOp_of_le
/-- If [an error satisfies the strict-exceedance boundedness condition at one rate](hyp:h),
[that rate is no larger than a second rate at every sample size](hyp:hrs), and
[the second rate is eventually positive](hyp:hs),
[the error is bounded in probability at the second rate](goal). -/
lemma boundedAtRate_isBigOp_of_le {A : Type*} [MeasurableSpace A]
    {μ : Measure A} {error : ℕ → A → ℝ} {r s : ℕ → ℝ}
    (h : BoundedAtRate μ error r) (hrs : ∀ n, r n ≤ s n)
    (hs : ∀ᶠ n in atTop, 0 < s n) :
    Causalean.Stat.IsBigOp error s μ := by
  intro ε hε
  by_cases htop : ε = ∞
  · exact ⟨1, one_pos, Filter.Eventually.of_forall (fun n => by simp [htop])⟩
  have hε' : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
  obtain ⟨C, hC, htail⟩ := h.2 ε.toReal hε'
  simp only [ENNReal.ofReal_toReal htop] at htail
  refine ⟨2 * C, mul_pos (by norm_num) hC, ?_⟩
  filter_upwards [htail, hs] with n hn hsn
  apply le_trans (measure_mono _) hn
  intro a ha
  change C * r n < |error n a|
  change (2 * C) * s n ≤ ‖error n a‖ at ha
  rw [Real.norm_eq_abs] at ha
  have hdom := mul_le_mul_of_nonneg_left (hrs n) hC.le
  have hstrict : C * s n < (2 * C) * s n := by
    nlinarith [mul_pos hC hsn]
  exact (hdom.trans_lt hstrict).trans_le ha

-- @node: plugin_total_rate_positive
/-- If [the endpoint rate is nonnegative at every sample size](hyp:he),
[the regression rate is nonnegative at every sample size](hyp:hg), and
[the boundary-law rate is nonnegative at every sample size](hyp:hm),
[their sum with the inverse square root of sample size is eventually strictly positive](goal). -/
lemma plugin_total_rate_positive (re rg rmu : ℕ → ℝ)
    (he : ∀ n, 0 ≤ re n) (hg : ∀ n, 0 ≤ rg n) (hm : ∀ n, 0 ≤ rmu n) :
    ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ)^(-1/2 : ℝ) + re n + rg n + rmu n := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hp := Real.rpow_pos_of_pos hn' (-1/2 : ℝ)
  linarith [he n, hg n, hm n]

-- @node: plugin_nuisance_sum_rate
/-- If [each of the three endpoint errors is bounded at the endpoint rate](hyp:he),
[the regression error is bounded at the regression rate](hyp:hg), and
[the boundary-law error is bounded at the boundary-law rate](hyp:hm),
[any fixed-coefficient sum consisting of twice the first endpoint error plus the second, the boundary-law and regression errors, and a multiple of the third endpoint error is bounded in probability at the sum of the three rates and the inverse square root of sample size](goal). -/
lemma plugin_nuisance_sum_rate {A : Type*} [MeasurableSpace A]
    {μ : Measure A} (e : Fin 3 → ℕ → A → ℝ) (g m : ℕ → A → ℝ)
    (re rg rmu : ℕ → ℝ) (C B : ℝ)
    (he : ∀ j, BoundedAtRate μ (e j) re)
    (hg : BoundedAtRate μ g rg) (hm : BoundedAtRate μ m rmu) :
    Causalean.Stat.IsBigOp
      (fun n a => C * (2 * e 0 n a + e 1 n a) + m n a + g n a + B * e 2 n a)
      (fun n => (n : ℝ)^(-1/2 : ℝ) + re n + rg n + rmu n) μ := by
  let r := fun n : ℕ => (n : ℝ)^(-1/2 : ℝ) + re n + rg n + rmu n
  have hre := (he 0).1
  have hrg := hg.1
  have hrm := hm.1
  have hpos : ∀ᶠ n in atTop, 0 < r n :=
    plugin_total_rate_positive re rg rmu hre hrg hrm
  have he' (j : Fin 3) : Causalean.Stat.IsBigOp (e j) r μ := by
    apply boundedAtRate_isBigOp_of_le (he j) _ hpos
    intro n
    dsimp [r]
    linarith [Real.rpow_nonneg (Nat.cast_nonneg n) (-1/2 : ℝ), hrg n, hrm n]
  have hg' : Causalean.Stat.IsBigOp g r μ := by
    apply boundedAtRate_isBigOp_of_le hg _ hpos
    intro n
    dsimp [r]
    linarith [Real.rpow_nonneg (Nat.cast_nonneg n) (-1/2 : ℝ), hre n, hrm n]
  have hm' : Causalean.Stat.IsBigOp m r μ := by
    apply boundedAtRate_isBigOp_of_le hm _ hpos
    intro n
    dsimp [r]
    linarith [Real.rpow_nonneg (Nat.cast_nonneg n) (-1/2 : ℝ), hre n, hrg n]
  exact ((((he' 0).const_mul 2 |>.add (he' 1)).const_mul C |>.add hm').add hg').add
    ((he' 2).const_mul B)

-- @node: isBigOp_of_abs_le_ae
/-- If [the absolute first error is at most the absolute second error almost everywhere at every sample size](hyp:h)
and [the second error is bounded in probability at a given rate](hyp:hg),
[the first error is bounded in probability at the same rate](goal). -/
lemma isBigOp_of_abs_le_ae {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {f g : ℕ → A → ℝ} {r : ℕ → ℝ}
    (h : ∀ n, ∀ᵐ a ∂μ, |f n a| ≤ |g n a|)
    (hg : Causalean.Stat.IsBigOp g r μ) : Causalean.Stat.IsBigOp f r μ := by
  intro δ hδ
  obtain ⟨K, hK, htail⟩ := hg δ hδ
  refine ⟨K, hK, htail.mono fun n hn => ?_⟩
  apply le_trans (measure_mono_ae ?_) hn
  filter_upwards [h n] with a ha
  intro hf
  exact hf.trans (by simpa only [Real.norm_eq_abs] using ha)

universe u v
variable {Ω : Type u} {X Z : Type v} {A : Type*}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: plugin_nuisance_envelope_rate
/-- For [a covariate-indexed fallback probability law supported on the outcome range](hyp:zeroLaw), if [the three integrated endpoint errors satisfy their common vanishing rate condition](hyp:hEndpoint),
[the fitted regression satisfies its range restriction and the sum of its two integrated target errors satisfies the regression rate condition](hyp:hRegression), and
[the integrated lower-propensity-weighted boundary-law distance satisfies the boundary-law rate condition](hyp:hBoundary),
[the population nuisance envelope—outcome magnitude times twice the first endpoint error plus the second, plus the boundary-law and regression errors, plus the absolute lower outcome bound times the third endpoint error—is bounded in probability at the sum of the three nuisance rates and the inverse square root of sample size](goal). -/
lemma plugin_nuisance_envelope_rate (M : LatentIVModel Ω X Z)
    (zeroLaw : X → {ν : ProbabilityMeasure ℝ // ν.toMeasure M.Ysetᶜ = 0})
    (μ : Measure A) (phi : Z → X → ℝ → ℝ)
    (pHat : ℕ → A → Z → X → ℝ) (gHat : ℕ → A → ℝ → X → ℝ)
    (QHat : ℕ → A → X → ℝ → ℝ) (re rg rmu : ℕ → ℝ)
    (hEndpoint : EndpointMapRates M μ phi pHat re)
    (hRegression : RegressionTargetRate M μ phi pHat gHat rg)
    (hBoundary : BoundaryLawRate M zeroLaw μ QHat rmu) :
    let e := fun (j : Fin 3) n a => ∫ zx,
      |endpointMap (pHat n a) (policyProp phi (pHat n a)) j zx -
        endpointMap M.prop (policyProp phi M.prop) j zx| ∂zxLaw M
    let g := fun n a => ∫ zx,
      (|gHat n a (clampPolicy (pHat n a) (policyProp phi (pHat n a)) zx.1 zx.2) zx.2 -
        g1 M (clampPolicy M.prop (policyProp phi M.prop) zx.1 zx.2) zx.2| +
       |gHat n a (pHat n a zx.1 zx.2) zx.2 - g1 M (M.prop zx.1 zx.2) zx.2|) ∂zxLaw M
    let m := fun n a => ∫ x, pLow M.prop x *
      quantileDistanceIntegral (boundaryLawHat QHat n a x) (boundaryLaw M zeroLaw x) ∂xLaw M
    Causalean.Stat.IsBigOp
      (fun n a => outcomeMagnitude M * (2 * e 0 n a + e 1 n a) +
        m n a + g n a + |M.yMin| * e 2 n a)
      (fun n => (n : ℝ)^(-1/2 : ℝ) + re n + rg n + rmu n) μ := by
  intro e g m
  exact plugin_nuisance_sum_rate e g m re rg rmu (outcomeMagnitude M) |M.yMin|
    hEndpoint.2.2 hRegression.2 hBoundary

end Papers.TbsPrteOptimalTransport
