module
public import Papers.TbsExtremeEffects.Helpers.ProductBounds

/-! Deterministic perturbation and product assembly for the NETE rate theorem. -/

@[expose] public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory
variable {q d : ℕ} {M : ExtremeModel q d}

-- @node: radialH_pos
/-- If [the model's tail index is positive](hyp:hbeta) and [its exponent is smaller than that tail index](hyp:hAlpha), then [the radial denominator target is positive](goal). -/
lemma radialH_pos (hbeta : 0 < M.beta) (hAlpha : AlphaLtBeta M) :
    0 < radialH M := by
  unfold radialH gamma
  have ha : M.alpha / M.beta < 1 := (div_lt_one hbeta).mpr hAlpha
  rw [mul_one_div]
  linarith

-- @node: radial_target_eq_inv_h
/-- If [the model's tail index is positive](hyp:hbeta) and [its exponent is below that tail index](hyp:hAlpha), then [the target tail-index ratio equals the reciprocal radial denominator](goal). -/
lemma radial_target_eq_inv_h (hbeta : 0 < M.beta) (hAlpha : AlphaLtBeta M) :
    M.beta / (M.beta - M.alpha) = 1 / radialH M := by
  have hh := (radialH_pos hbeta hAlpha).ne'
  unfold radialH gamma at *
  field_simp

-- @node: exponent_hill_product_error
/-- If [the true Hill parameter is nonnegative](hyp:hg), [the exponent-error allowance is nonnegative](hyp:_ha), [the estimated exponent is within that allowance](hyp:hAlpha), and [the estimated Hill parameter is within its error allowance](hyp:hHill), then [their product error has the stated bound](goal). -/
lemma exponent_hill_product_error {alpha ahat gamma ghat a b : ℝ}
    (hg : 0 ≤ gamma) (_ha : 0 ≤ a)
    (hAlpha : |ahat - alpha| ≤ a) (hHill : |ghat - gamma| ≤ b) :
    |ahat * ghat - alpha * gamma| ≤ a * (gamma + b) + |alpha| * b := by
  have hghat : |ghat| ≤ gamma + b := by
    calc
      _ ≤ |ghat - gamma| + |gamma| := by
        simpa only [sub_add_cancel] using abs_add_le (ghat - gamma) gamma
      _ ≤ b + gamma := by gcongr; rw [abs_of_nonneg hg]
      _ = gamma + b := add_comm _ _
  calc
    _ = |ghat * (ahat - alpha) + alpha * (ghat - gamma)| := by congr 1; ring
    _ ≤ |ghat| * |ahat - alpha| + |alpha| * |ghat - gamma| := by
      simpa only [abs_mul] using abs_add_le (ghat * (ahat - alpha)) (alpha * (ghat - gamma))
    _ ≤ (gamma + b) * a + |alpha| * b := by
      exact add_le_add (mul_le_mul hghat hAlpha (abs_nonneg _) (by linarith [abs_nonneg ghat]))
        (mul_le_mul_of_nonneg_left hHill (abs_nonneg _))
    _ = _ := by ring

-- @node: muHat_radial_error_bound
/-- Given [an experiment](hyp:E), [a sample size](hyp:n), [a Hill coefficient and tolerance](hyp:Cg,delta), [an exponent-error rate](hyp:Ralpha), and [an outcome](hyp:w), if [the radial target is positive](hyp:hh), [the Hill parameter is nonnegative](hyp:hg), [the exponent-error rate is nonnegative](hyp:ha), [the exponent estimator obeys its error bound](hyp:hAlpha), and [the Hill estimator obeys its error bound](hyp:hHill), then [the reciprocal-radial estimator is within its radial error bound](goal). -/
lemma muHat_radial_error_bound (E : NeteExperiment M) (n : ℕ)
    (Cg delta : ℝ) (Ralpha : ℕ → ℝ → ℝ) (w : E.Om)
    (hh : 0 < radialH M) (hg : 0 ≤ gamma M)
    (ha : 0 ≤ Ralpha n (delta / 12))
    (hAlpha : |E.alphaHat n w - M.alpha| ≤ Ralpha n (delta / 12))
    (hHill : |hillAdaptive E n (delta / 6) w - gamma M| ≤ hillErrorBound M Cg delta n) :
    |muHat E n (delta / 6) w - 1 / radialH M| ≤ radialError E Cg delta Ralpha n w := by
  have hprod := exponent_hill_product_error hg ha hAlpha hHill
  change |E.alphaHat n w * hillAdaptive E n (delta / 6) w - M.alpha * gamma M| ≤
    radialQ M Cg delta Ralpha n at hprod
  let u := 1 - E.alphaHat n w * hillAdaptive E n (delta / 6) w
  have hdiff : radialH M - u =
      E.alphaHat n w * hillAdaptive E n (delta / 6) w - M.alpha * gamma M := by
    dsimp [u, radialH]; ring
  by_cases hu : u = 0
  · have hden : estimatedDenominator E n delta w = 0 := by
      change |u| = 0; rw [hu, abs_zero]
    simp only [muHat, show 1 - E.alphaHat n w * hillAdaptive E n (delta / 6) w = 0 from hu,
      ↓reduceIte, zero_sub, abs_neg, abs_of_pos (one_div_pos.mpr hh),
      radialError, hden, lt_self_iff_false]
    exact le_rfl
  · have hden : 0 < estimatedDenominator E n delta w := abs_pos.mpr hu
    change |(if u = 0 then 0 else u⁻¹) - 1 / radialH M| ≤ _
    rw [if_neg hu, radialError, if_pos hden, one_div,
      inv_sub_inv hu hh.ne', abs_div, abs_mul, abs_of_pos hh, hdiff]
    change _ ≤ radialQ M Cg delta Ralpha n / (radialH M * |u|)
    rw [mul_comm (radialH M) |u|]
    exact div_le_div_of_nonneg_right hprod (mul_nonneg (abs_nonneg _) hh.le)

-- @node: product_estimate_error_bound
/-- If [the target equals the product of its two population factors](hyp:hTarget), [the first estimated factor has error at most its allowance](hyp:hEta), and [the second estimated factor has error at most its allowance](hyp:hMu), then [the estimated product has the stated error bound](goal). -/
lemma product_estimate_error_bound {eta etahat mu muhat theta e r : ℝ}
    (hTarget : theta = eta * mu) (hEta : |etahat - eta| ≤ e)
    (hMu : |muhat - mu| ≤ r) :
    |etahat * muhat - theta| ≤ |muhat| * e + |eta| * r := by
  rw [hTarget]
  calc
    _ = |muhat * (etahat - eta) + eta * (muhat - mu)| := by congr 1; ring
    _ ≤ |muhat| * |etahat - eta| + |eta| * |muhat - mu| := by
      simpa only [abs_mul] using abs_add_le (muhat * (etahat - eta)) (eta * (muhat - mu))
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hEta (abs_nonneg _))
      (mul_le_mul_of_nonneg_left hMu (abs_nonneg _))

-- @node: estimatedDenominator_lower_bound
/-- Given [an experiment](hyp:E), [sample size](hyp:n), [Hill coefficient and tolerance](hyp:Cg,delta), [exponent-error rate](hyp:Ralpha), and [outcome](hyp:w), if [the Hill parameter is nonnegative](hyp:hg), [the exponent-error rate is nonnegative](hyp:ha), [the exponent estimator has its stated error](hyp:hAlpha), and [the Hill estimator has its stated error](hyp:hHill), then [the estimated denominator is at least the radial target minus the product-error budget](goal). -/
lemma estimatedDenominator_lower_bound (E : NeteExperiment M) (n : ℕ)
    (Cg delta : ℝ) (Ralpha : ℕ → ℝ → ℝ) (w : E.Om)
    (hg : 0 ≤ gamma M) (ha : 0 ≤ Ralpha n (delta / 12))
    (hAlpha : |E.alphaHat n w - M.alpha| ≤ Ralpha n (delta / 12))
    (hHill : |hillAdaptive E n (delta / 6) w - gamma M| ≤ hillErrorBound M Cg delta n) :
    radialH M - radialQ M Cg delta Ralpha n ≤ estimatedDenominator E n delta w := by
  have hp := exponent_hill_product_error hg ha hAlpha hHill
  change _ ≤ radialQ M Cg delta Ralpha n at hp
  have hid : radialH M =
      (1 - E.alphaHat n w * hillAdaptive E n (delta / 6) w) +
      (E.alphaHat n w * hillAdaptive E n (delta / 6) w - M.alpha * gamma M) := by
    unfold radialH; ring
  have h : radialH M ≤ |1 - E.alphaHat n w * hillAdaptive E n (delta / 6) w| +
      |E.alphaHat n w * hillAdaptive E n (delta / 6) w - M.alpha * gamma M| := by
    calc
      _ ≤ |radialH M| := le_abs_self _
      _ = _ := congrArg abs hid
      _ ≤ _ := abs_add_le _ _
  change radialH M - radialQ M Cg delta Ralpha n ≤
    |1 - E.alphaHat n w * hillAdaptive E n (delta / 6) w|
  linarith

-- @node: muHat_bound_of_radialQ_small
/-- Given [an experiment](hyp:E), [sample size](hyp:n), [Hill coefficient and tolerance](hyp:Cg,delta), [exponent-error rate](hyp:Ralpha), and [outcome](hyp:w), if [the radial target is positive](hyp:hh), [the Hill parameter is nonnegative](hyp:hg), [the exponent-error rate is nonnegative](hyp:ha), [the exponent and Hill estimators obey their error bounds](hyp:hAlpha,hHill), and [the product-error budget is at most half the radial target](hyp:hQ), then [the reciprocal estimate and its radial error satisfy the two displayed bounds](goal). -/
lemma muHat_bound_of_radialQ_small (E : NeteExperiment M) (n : ℕ)
    (Cg delta : ℝ) (Ralpha : ℕ → ℝ → ℝ) (w : E.Om)
    (hh : 0 < radialH M) (hg : 0 ≤ gamma M)
    (ha : 0 ≤ Ralpha n (delta / 12))
    (hAlpha : |E.alphaHat n w - M.alpha| ≤ Ralpha n (delta / 12))
    (hHill : |hillAdaptive E n (delta / 6) w - gamma M| ≤ hillErrorBound M Cg delta n)
    (hQ : radialQ M Cg delta Ralpha n ≤ radialH M / 2) :
    |muHat E n (delta / 6) w| ≤ 2 / radialH M ∧
    radialError E Cg delta Ralpha n w ≤ 2 * radialQ M Cg delta Ralpha n / radialH M ^ 2 := by
  have hl := estimatedDenominator_lower_bound E n Cg delta Ralpha w hg ha hAlpha hHill
  have hden : radialH M / 2 ≤ estimatedDenominator E n delta w := by linarith
  have hpos : 0 < estimatedDenominator E n delta w := (half_pos hh).trans_le hden
  have hu : 1 - E.alphaHat n w * hillAdaptive E n (delta / 6) w ≠ 0 :=
    abs_pos.mp hpos
  have hp := exponent_hill_product_error hg ha hAlpha hHill
  change _ ≤ radialQ M Cg delta Ralpha n at hp
  have hQ0 : 0 ≤ radialQ M Cg delta Ralpha n := (abs_nonneg _).trans hp
  constructor
  · rw [muHat, if_neg hu, abs_inv]
    change (estimatedDenominator E n delta w)⁻¹ ≤ _
    calc
      _ ≤ (radialH M / 2)⁻¹ := (inv_le_inv₀ hpos (half_pos hh)).mpr hden
      _ = 2 / radialH M := by rw [inv_div]
  · rw [radialError, if_pos hpos]
    calc
      _ ≤ radialQ M Cg delta Ralpha n / (radialH M * (radialH M / 2)) :=
        div_le_div_of_nonneg_left hQ0 (mul_pos hh (half_pos hh))
          (mul_le_mul_of_nonneg_left hden hh.le)
      _ = _ := by field_simp

-- @node: nete_product_bounds_of_factor_errors
/-- Given [an experiment](hyp:E), [sample size](hyp:n), [threshold and rate constants](hyp:t,Cg,delta,c,Cgb,a0), [nuisance rates](hyp:Rp,Rg,Ralpha), [DR and IPW truncation bounds](hyp:Bdr,Bipw), and [an outcome](hyp:w), if [the NETE target factorizes as stated](hyp:hTarget), [the radial target is positive](hyp:hh), [the Hill parameter is nonnegative](hyp:hg), [the exponent-rate allowance is nonnegative](hyp:ha), [the exponent and Hill errors obey their bounds](hyp:hAlpha,hHill), and [the DR and IPW first-factor errors obey their bounds](hyp:hDR,hIPW), then [both NETE product-error bounds hold](goal). -/
lemma nete_product_bounds_of_factor_errors (E : NeteExperiment M) (n : ℕ)
    (t Cg delta c Cgb a0 : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (Bdr Bipw : E.Om → ℝ) (w : E.Om)
    (hTarget : thetaNETE M = etaTarget M * (1 / radialH M))
    (hh : 0 < radialH M) (hg : 0 ≤ gamma M)
    (ha : 0 ≤ Ralpha n (delta / 12))
    (hAlpha : |E.alphaHat n w - M.alpha| ≤ Ralpha n (delta / 12))
    (hHill : |hillAdaptive E n (delta / 6) w - gamma M| ≤ hillErrorBound M Cg delta n)
    (hDR : |etaEstimate E .dr n t w - etaTarget M| ≤
      rateFirstFactorError E .dr c Cgb a0 Rp Rg Ralpha n t delta Bdr w)
    (hIPW : |etaEstimate E .ipw n t w - etaTarget M| ≤
      rateFirstFactorError E .ipw c Cgb a0 Rp Rg Ralpha n t delta Bipw w) :
    (|thetaHatDR E n t (delta / 6) w - thetaNETE M| ≤
      |muHat E n (delta / 6) w| *
        rateFirstFactorError E .dr c Cgb a0 Rp Rg Ralpha n t delta Bdr w +
      |etaTarget M| * radialError E Cg delta Ralpha n w) ∧
    (|thetaHatIPW E n t (delta / 6) w - thetaNETE M| ≤
      |muHat E n (delta / 6) w| *
        rateFirstFactorError E .ipw c Cgb a0 Rp Rg Ralpha n t delta Bipw w +
      |etaTarget M| * radialError E Cg delta Ralpha n w) := by
  have hMu := muHat_radial_error_bound E n Cg delta Ralpha w hh hg ha hAlpha hHill
  exact ⟨product_estimate_error_bound hTarget hDR hMu,
    product_estimate_error_bound hTarget hIPW hMu⟩

/-- For [an experiment](hyp:E), [overlap, scaling, and confidence constants](hyp:c,Cgb,a0,C,Cg,V,delta), [nuisance rates](hyp:Rp,Rg,Ralpha), [sample size](hyp:n), [threshold](hyp:t), [DR and IPW truncation bounds](hyp:Bdr,Bipw), and [outcome](hyp:w), [the product-rate-factor event](goal) requires adequate evaluation count, exponent and Hill accuracy, DR and IPW first-factor accuracy, and conditional simplified product bounds. These are [clauses 1](step:1), [2](step:2), [3](step:3), [4](step:4), [5](step:5), and [6](step:6). -/
-- @node: ProductRateFactors
def ProductRateFactors (E : NeteExperiment M)
    (c Cgb a0 C Cg V delta : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (n : ℕ) (t : ℝ) (Bdr Bipw : E.Om → ℝ) (w : E.Om) : Prop :=
  (n : ℝ) * tailProb M t / 4 ≤ evalCount E n t w ∧
  |E.alphaHat n w - M.alpha| ≤ Ralpha n (delta / 12) ∧
  |hillAdaptive E n (delta / 6) w - gamma M| ≤ hillErrorBound M Cg delta n ∧
  |etaEstimate E .dr n t w - etaTarget M| ≤
    rateFirstFactorError E .dr c Cgb a0 Rp Rg Ralpha n t delta Bdr w ∧
  |etaEstimate E .ipw n t w - etaTarget M| ≤
    rateFirstFactorError E .ipw c Cgb a0 Rp Rg Ralpha n t delta Bipw w ∧
  (secondMomentsOnNuisance E n t (delta / 12) Rp Rg Ralpha V → Real.exp 1 ≤ t →
    Ralpha n (delta / 12) * Real.log t ≤ 1 →
    radialQ M Cg delta Ralpha n ≤ radialH M / 2 →
      (|thetaHatDR E n t (delta / 6) w - thetaNETE M| ≤
        C * simplifiedRate E .dr V Cg delta Rp Rg Ralpha n t w) ∧
      (|thetaHatIPW E n t (delta / 6) w - thetaNETE M| ≤
        C * simplifiedRate E .ipw V Cg delta Rp Rg Ralpha n t w))

-- @node: productSuccess_of_rate_factors
/-- Given [an experiment](hyp:E), [overlap, scaling, and confidence constants](hyp:c,Cgb,a0,C,Cg,V,delta), [nuisance rates](hyp:Rp,Rg,Ralpha), [sample size](hyp:n), [threshold](hyp:t), [DR and IPW truncation bounds](hyp:Bdr,Bipw), and [an outcome](hyp:w), if [the NETE target has its radial factorization](hyp:hTarget), [the radial target is positive](hyp:hh), [the Hill parameter is nonnegative](hyp:hg), and [all product-rate factors hold](hyp:h), then [product success holds](goal). -/
lemma productSuccess_of_rate_factors (E : NeteExperiment M)
    (c Cgb a0 C Cg V delta : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (n : ℕ) (t : ℝ) (Bdr Bipw : E.Om → ℝ) (w : E.Om)
    (hTarget : thetaNETE M = etaTarget M * (1 / radialH M))
    (hh : 0 < radialH M) (hg : 0 ≤ gamma M)
    (h : ProductRateFactors E c Cgb a0 C Cg V delta Rp Rg Ralpha n t Bdr Bipw w) :
    ProductSuccess E c Cgb a0 C Cg V delta Rp Rg Ralpha n t Bdr Bipw w := by
  obtain ⟨hcount, hAlpha, hHill, hDR, hIPW, hSimple⟩ := h
  have ha := (abs_nonneg (E.alphaHat n w - M.alpha)).trans hAlpha
  obtain ⟨hDRprod, hIPWprod⟩ := nete_product_bounds_of_factor_errors E n t Cg delta c Cgb a0
    Rp Rg Ralpha Bdr Bipw w hTarget hh hg ha hAlpha hHill hDR hIPW
  exact ⟨hcount, hDRprod, hIPWprod, hSimple⟩

end Papers.TbsExtremeEffects
