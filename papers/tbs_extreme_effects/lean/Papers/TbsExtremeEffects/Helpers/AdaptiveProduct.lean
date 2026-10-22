module
public import Papers.TbsExtremeEffects.Helpers.ThresholdLocalization
public import Papers.TbsExtremeEffects.Helpers.ProductAssembly

/-! Vanishing denominator perturbations and product assembly at adaptive thresholds. -/

@[expose] public section
noncomputable section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
variable {q d : ℕ} {M : ExtremeModel q d}

/-- [The adaptive radial perturbation](goal) combines the [extreme-value model](hyp:M),
the [Hill-error constant](hyp:Cg), [confidence tolerance](hyp:delta), [exponent-rate function](hyp:Ralpha), and [sample size](hyp:n). -/
-- @node: adaptiveRadialQ
def adaptiveRadialQ (M : ExtremeModel q d) (Cg delta : ℝ)
    (Ralpha : ℕ → ℝ → ℝ) (n : ℕ) : ℝ :=
  Ralpha n (delta / 6) * (gamma M + hillErrorBound M Cg delta n) +
    |M.alpha| * hillErrorBound M Cg delta n

/-- [The adaptive radial scale](goal) is the sum of a logarithmic polynomial term determined by the [model](hyp:M), [Hill-error constant](hyp:Cg), [confidence tolerance](hyp:delta), and [tail-index exponent](hyp:cAlpha), and the [sample-size-dependent](hyp:n) Hill term. -/
-- @node: adaptiveRadialScale
def adaptiveRadialScale (M : ExtremeModel q d) (Cg delta cAlpha : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (-cAlpha) * Real.log n * Real.log (6 / delta) +
    |M.alpha| * hillErrorBound M Cg delta n

/-- If [the rate has the stated polynomial envelope](hyp:hRate), [its exponent is positive](hyp:ha), and [the confidence tolerance lies in its admissible domain](hyp:hd), then [the rate at that tolerance converges to zero](goal). -/
-- @node: rateTheta_tendsto_zero
lemma rateTheta_tendsto_zero {rate : ℕ → ℝ → ℝ} {a eps : ℝ}
    (hRate : RateTheta rate a) (ha : 0 < a) (hd : ConfidenceDomain eps) :
    Tendsto (fun n => rate n eps) atTop (𝓝 0) := by
  obtain ⟨c, C, hc, hcC, n0, _, hBounds⟩ := hRate
  have hlog : 0 ≤ Real.log (1 / eps) :=
    Real.log_nonneg ((one_le_div hd.1).mpr hd.2.le)
  have hUpper : Tendsto (fun n : ℕ => C * Real.log (1 / eps) * (n : ℝ) ^ (-a))
      atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop ha).comp
      tendsto_natCast_atTop_atTop).const_mul (C * Real.log (1 / eps))
  apply squeeze_zero' _ _ hUpper
  · filter_upwards [eventually_ge_atTop n0] with n hn
    exact (mul_nonneg (mul_nonneg hc.le hlog) (Real.rpow_nonneg (Nat.cast_nonneg n) _)).trans
      (hBounds n hn eps hd.1 hd.2).1
  · filter_upwards [eventually_ge_atTop n0] with n hn
    exact (hBounds n hn eps hd.1 hd.2).2

/-- If [the model's tail index is positive](hyp:hb) and [the confidence tolerance is positive](hyp:hd), then [the Hill error converges to zero](goal). -/
-- @node: hillErrorBound_tendsto_zero
lemma hillErrorBound_tendsto_zero {Cg delta : ℝ} (hb : 0 < M.beta) (hd : 0 < delta) :
    Tendsto (hillErrorBound M Cg delta) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => hillErrorBound M Cg delta n * Real.log n)
      atTop (𝓝 0) := by
    simpa only [hillErrorBound, mul_assoc, mul_zero] using
      (hillRateShape_log_tendsto_zero hb (by positivity : 0 < 48 / delta)).const_mul Cg
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (1 : ℝ))
  have hdom : ∀ᶠ n : ℕ in atTop,
      |hillErrorBound M Cg delta n| ≤ |hillErrorBound M Cg delta n * Real.log n| := by
    filter_upwards [hlog] with n hn
    change 1 ≤ Real.log (n : ℝ) at hn
    rw [abs_mul, abs_of_nonneg (show 0 ≤ Real.log (n : ℝ) by linarith)]
    exact le_mul_of_one_le_right (abs_nonneg _) hn
  exact squeeze_zero_norm' hdom (by simpa using hlim.abs)

/-- If [the tail index is positive](hyp:hb), [the rescaled confidence tolerance is admissible](hyp:hd), [the exponent rate is positive](hyp:hcAlpha), and [the exponent estimator has the stated rate](hyp:hRate), then [the joint exponent-and-Hill perturbation converges to zero](goal). -/
-- @node: adaptiveRadialQ_tendsto_zero
lemma adaptiveRadialQ_tendsto_zero {Cg delta cAlpha : ℝ}
    {Ralpha : ℕ → ℝ → ℝ} (hb : 0 < M.beta) (hd : ConfidenceDomain (delta / 6))
    (hcAlpha : 0 < cAlpha) (hRate : RateTheta Ralpha cAlpha) :
    Tendsto (adaptiveRadialQ M Cg delta Ralpha) atTop (𝓝 0) := by
  have hdpos : 0 < delta := by linarith [hd.1]
  have hbnd := hillErrorBound_tendsto_zero (M := M) (Cg := Cg) hb hdpos
  have ha := rateTheta_tendsto_zero hRate hcAlpha hd
  change Tendsto (fun n => Ralpha n (delta / 6) *
    (gamma M + hillErrorBound M Cg delta n) + |M.alpha| * hillErrorBound M Cg delta n)
    atTop (𝓝 0)
  simpa only [adaptiveRadialQ, zero_mul, mul_zero, add_zero] using
    (ha.mul (tendsto_const_nhds.add hbnd)).add (hbnd.const_mul |M.alpha|)

/-- If [the tail index is positive](hyp:hb), [the rescaled tolerance is admissible](hyp:hd), and [the exponent error has the stated rate](hyp:hRate), then [some positive constant eventually bounds the joint perturbation by the adaptive radial scale whenever the Hill error is nonnegative](goal). -/
-- @node: adaptiveRadialQ_rate_bound
lemma adaptiveRadialQ_rate_bound {Cg delta cAlpha : ℝ} {Ralpha : ℕ → ℝ → ℝ}
    (hb : 0 < M.beta) (hd : ConfidenceDomain (delta / 6))
    (hRate : RateTheta Ralpha cAlpha) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ n : ℕ in atTop,
      0 ≤ hillErrorBound M Cg delta n →
      0 ≤ adaptiveRadialScale M Cg delta cAlpha n ∧
      adaptiveRadialQ M Cg delta Ralpha n ≤
        D * adaptiveRadialScale M Cg delta cAlpha n := by
  obtain ⟨c, C, hc, hcC, n0, _, hBounds⟩ := hRate
  have hg : 0 ≤ gamma M := by unfold gamma; positivity
  have hC : 0 < C := hc.trans_le hcC
  let D := max (C * (gamma M + 1)) 1
  have hD : 0 < D := zero_lt_one.trans_le (le_max_right _ _)
  refine ⟨D, hD, ?_⟩
  have hdpos : 0 < delta := by linarith [hd.1]
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (1 : ℝ))
  have hsmall := (tendsto_order.mp
    (hillErrorBound_tendsto_zero (M := M) (Cg := Cg) hb hdpos)).2 1 zero_lt_one
  filter_upwards [eventually_ge_atTop n0, hlog, hsmall] with n hn hnlog hnsmall
  intro hbnd
  change 1 ≤ Real.log (n : ℝ) at hnlog
  have htol : 1 / (delta / 6) = 6 / delta := by ring
  have hl : 0 ≤ Real.log (6 / delta) := by
    rw [← htol]
    exact Real.log_nonneg ((one_le_div hd.1).mpr hd.2.le)
  let z := (n : ℝ) ^ (-cAlpha) * Real.log n * Real.log (6 / delta)
  have hz : 0 ≤ z := mul_nonneg
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (by linarith)) hl
  have ha : 0 ≤ Ralpha n (delta / 6) :=
    (mul_nonneg (mul_nonneg hc.le (by rwa [htol]))
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)).trans (hBounds n hn _ hd.1 hd.2).1
  have hupper : Ralpha n (delta / 6) ≤ C * z := by
    calc
      _ ≤ C * Real.log (6 / delta) * (n : ℝ) ^ (-cAlpha) := by
        simpa only [htol] using (hBounds n hn _ hd.1 hd.2).2
      _ ≤ (C * Real.log (6 / delta) * (n : ℝ) ^ (-cAlpha)) * Real.log n :=
        le_mul_of_one_le_right (by positivity) hnlog
      _ = C * z := by dsimp [z]; ring
  have hpart : Ralpha n (delta / 6) * (gamma M + hillErrorBound M Cg delta n) ≤
      D * z := by
    calc
      _ ≤ Ralpha n (delta / 6) * (gamma M + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) ha
      _ ≤ C * z * (gamma M + 1) :=
        mul_le_mul_of_nonneg_right hupper (by positivity)
      _ = (C * (gamma M + 1)) * z := by ring
      _ ≤ D * z := mul_le_mul_of_nonneg_right (le_max_left _ _) hz
  have hw : 0 ≤ |M.alpha| * hillErrorBound M Cg delta n := mul_nonneg (abs_nonneg _) hbnd
  refine ⟨add_nonneg hz hw, ?_⟩
  change Ralpha n (delta / 6) * (gamma M + hillErrorBound M Cg delta n) +
    |M.alpha| * hillErrorBound M Cg delta n ≤ D * (z + _)
  calc
    _ ≤ D * z + D * (|M.alpha| * hillErrorBound M Cg delta n) :=
      add_le_add hpart (le_mul_of_one_le_left hw (le_max_right _ _))
    _ = _ := (mul_add _ _ _).symm

/-- For [an experiment](hyp:E), if [the radial denominator is positive](hyp:hh), [the tail mean is nonnegative](hyp:hg), [the exponent estimate is accurate](hyp:hAlpha), [the Hill estimate is accurate](hyp:hHill), and [their joint perturbation is small](hyp:hSmall), then [the reciprocal estimate and its error obey the displayed bounds](goal). -/
-- @node: adaptive_muHat_bounds
lemma adaptive_muHat_bounds (E : NeteExperiment M) {n : ℕ} {Cg delta : ℝ}
    {Ralpha : ℕ → ℝ → ℝ} {w : E.Om}
    (hh : 0 < radialH M) (hg : 0 ≤ gamma M)
    (hAlpha : |E.alphaHat n w - M.alpha| ≤ Ralpha n (delta / 6))
    (hHill : |gamma M - hillAdaptive E n (delta / 6) w| ≤ hillErrorBound M Cg delta n)
    (hSmall : adaptiveRadialQ M Cg delta Ralpha n ≤ radialH M / 2) :
    |muHat E n (delta / 6) w| ≤ 2 / radialH M ∧
      |muHat E n (delta / 6) w - 1 / radialH M| ≤
        2 * adaptiveRadialQ M Cg delta Ralpha n / radialH M ^ 2 := by
  let R : ℕ → ℝ → ℝ := fun n eps => Ralpha n (2 * eps)
  have htol : 2 * (delta / 12) = delta / 6 := by ring
  have ha : 0 ≤ R n (delta / 12) := by
    dsimp [R]; rw [htol]; exact (abs_nonneg _).trans hAlpha
  have hA : |E.alphaHat n w - M.alpha| ≤ R n (delta / 12) := by
    simpa only [R, htol] using hAlpha
  have hH : |hillAdaptive E n (delta / 6) w - gamma M| ≤ hillErrorBound M Cg delta n := by
    rwa [abs_sub_comm]
  have hQ : radialQ M Cg delta R n = adaptiveRadialQ M Cg delta Ralpha n := by
    simp only [radialQ, adaptiveRadialQ, R, htol]
  obtain ⟨hMu, hError⟩ := muHat_bound_of_radialQ_small E n Cg delta R w
    hh hg ha hA hH (hQ.symm ▸ hSmall)
  refine ⟨hMu, (muHat_radial_error_bound E n Cg delta R w hh hg ha hA hH).trans ?_⟩
  simpa only [hQ] using hError

/-- For [an experiment](hyp:E), if [the tail index is positive](hyp:hb), [the model exponent is below it](hyp:hAlpha), [the rescaled tolerance is admissible](hyp:hd), [the rate exponent is positive](hyp:hcAlpha), and [the exponent estimator has the stated rate](hyp:hRate), then [eventually every sample satisfying the two estimation-error bounds also satisfies the reciprocal bounds](goal). -/
-- @node: adaptive_muHat_bounds_eventually
lemma adaptive_muHat_bounds_eventually (E : NeteExperiment M) {Cg delta cAlpha : ℝ}
    {Ralpha : ℕ → ℝ → ℝ} (hb : 0 < M.beta) (hAlpha : AlphaLtBeta M)
    (hd : ConfidenceDomain (delta / 6)) (hcAlpha : 0 < cAlpha)
    (hRate : RateTheta Ralpha cAlpha) :
    ∀ᶠ n : ℕ in atTop, ∀ w,
      |E.alphaHat n w - M.alpha| ≤ Ralpha n (delta / 6) →
      |gamma M - hillAdaptive E n (delta / 6) w| ≤ hillErrorBound M Cg delta n →
      |muHat E n (delta / 6) w| ≤ 2 / radialH M ∧
        |muHat E n (delta / 6) w - 1 / radialH M| ≤
          2 * adaptiveRadialQ M Cg delta Ralpha n / radialH M ^ 2 := by
  have hh := radialH_pos hb hAlpha
  have hlim := adaptiveRadialQ_tendsto_zero (Cg := Cg) hb hd hcAlpha hRate
  filter_upwards [(tendsto_order.mp hlim).2 _ (half_pos hh)] with n hn
  intro w ha hg
  exact adaptive_muHat_bounds E hh (by unfold gamma; positivity) ha hg hn.le

/-- For [an experiment](hyp:E) and [estimator kind](hyp:kind), if [the target factors as the target contrast times the reciprocal radial quantity](hyp:hTarget), [the reciprocal estimate obeys its two bounds](hyp:hMu), and [the contrast estimate has error at most the supplied tolerance](hyp:hEta), then [the product estimator has the displayed error bound](goal). -/
-- @node: adaptive_product_error_bound
lemma adaptive_product_error_bound (E : NeteExperiment M) (kind : EstimatorKind)
    {n : ℕ} {t Cg delta e : ℝ} {Ralpha : ℕ → ℝ → ℝ} {w : E.Om}
    (hTarget : thetaNETE M = etaTarget M * (1 / radialH M))
    (hMu : |muHat E n (delta / 6) w| ≤ 2 / radialH M ∧
      |muHat E n (delta / 6) w - 1 / radialH M| ≤
        2 * adaptiveRadialQ M Cg delta Ralpha n / radialH M ^ 2)
    (hEta : |etaEstimate E kind n t w - etaTarget M| ≤ e) :
    |neteEstimator E kind n t (delta / 6) w - thetaNETE M| ≤
      (2 / radialH M) * e + |etaTarget M| *
        (2 * adaptiveRadialQ M Cg delta Ralpha n / radialH M ^ 2) := by
  have he : 0 ≤ e := (abs_nonneg _).trans hEta
  have h := product_estimate_error_bound hTarget hEta hMu.2
  have hFinal := h.trans (add_le_add
    (mul_le_mul_of_nonneg_right hMu.1 he) le_rfl)
  convert hFinal using 1 <;> cases kind <;> rfl

end Papers.TbsExtremeEffects
