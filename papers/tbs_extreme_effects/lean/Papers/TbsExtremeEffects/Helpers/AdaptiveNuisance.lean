module
public import Papers.TbsExtremeEffects.Helpers.AdaptiveTailRates
public import Papers.TbsExtremeEffects.Helpers.ThresholdSampling
public import Papers.TbsExtremeEffects.Helpers.DRMean

/-! Uniform nuisance-product rates from the deterministic endpoint count bound. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
variable {q d : ℕ} {M : ExtremeModel q d}

/-- If [a rate has polynomial order](hyp:hRate), [that order is nonnegative](hyp:ha), [the count-growth exponent is positive](hyp:he), [the count multiplier is positive](hyp:hL), and [the confidence argument is valid](hyp:hd), then [a polynomial lower bound on a count yields the stated rate bound](goal).

@node: rateTheta_at_polynomial_count -/
lemma rateTheta_at_polynomial_count {rate : ℕ → ℝ → ℝ} {a e L eps : ℝ}
    (hRate : RateTheta rate a) (ha : 0 ≤ a) (he : 0 < e)
    (hL : 0 < L) (hd : ConfidenceDomain eps) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ n : ℕ in atTop, ∀ k : ℕ,
      L * (n : ℝ) ^ e ≤ (k : ℝ) →
      0 ≤ rate k eps ∧
      rate k eps ≤ D * Real.log (1 / eps) * (n : ℝ) ^ (-e * a) := by
  obtain ⟨c, C, hc, hcC, n0, _, hBounds⟩ := hRate
  have hC : 0 < C := hc.trans_le hcC
  have hlog : 0 ≤ Real.log (1 / eps) :=
    Real.log_nonneg ((one_le_div hd.1).mpr hd.2.le)
  have hGrowth : Tendsto (fun n : ℕ => L * (n : ℝ) ^ e) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hL).mpr
      ((tendsto_rpow_atTop he).comp tendsto_natCast_atTop_atTop)
  refine ⟨C * L ^ (-a), by positivity, ?_⟩
  filter_upwards [hGrowth.eventually (eventually_ge_atTop (n0 : ℝ)),
    eventually_ge_atTop (1 : ℕ)] with n hn hn1
  intro k hk
  have hk0 : n0 ≤ k := by exact_mod_cast hn.trans hk
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hpow : (k : ℝ) ^ (-a) ≤ L ^ (-a) * (n : ℝ) ^ (-e * a) := by
    calc
      _ ≤ (L * (n : ℝ) ^ e) ^ (-a) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hk (by linarith)
      _ = _ := by
        rw [Real.mul_rpow hL.le (Real.rpow_nonneg hnR.le _),
          ← Real.rpow_mul hnR.le]
        congr 2
        ring
  refine ⟨(mul_nonneg (mul_nonneg hc.le hlog)
    (Real.rpow_nonneg (Nat.cast_nonneg k) _)).trans (hBounds k hk0 eps hd.1 hd.2).1, ?_⟩
  calc
    _ ≤ C * Real.log (1 / eps) * (k : ℝ) ^ (-a) := (hBounds k hk0 eps hd.1 hd.2).2
    _ ≤ C * Real.log (1 / eps) * (L ^ (-a) * (n : ℝ) ^ (-e * a)) :=
      mul_le_mul_of_nonneg_left hpow (mul_nonneg hC.le hlog)
    _ = _ := by ring

/-- For [an even sample size](hyp:hn), [its integer half equals half of its real-valued size](goal).

@node: even_sample_half_cast -/
lemma even_sample_half_cast {n : ℕ} (hn : EvenSampleSize n) :
    (n / 2 : ℕ) = (n : ℝ) / 2 := by
  obtain ⟨k, hk⟩ := hn.2
  have hhalf : n / 2 = k := by omega
  rw [hhalf, hk]
  push_cast
  ring

/-- If [the propensity rate has order one half](hyp:hRp), [the regression rate has order one half](hyp:hRg), [the count multiplier is positive](hyp:hL), [the target rate exponent is positive](hyp:hr), and [the confidence argument is valid](hyp:hd), then [their product at the training half and a sufficiently large count has the stated mixed rate](goal).

@node: nuisance_product_at_polynomial_count -/
lemma nuisance_product_at_polynomial_count {Rp Rg : ℕ → ℝ → ℝ} {L r eps : ℝ}
    (hRp : RateTheta Rp (1 / 2)) (hRg : RateTheta Rg (1 / 2))
    (hL : 0 < L) (hr : 0 < r) (hd : ConfidenceDomain eps) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ n : ℕ in atTop, EvenSampleSize n → ∀ k : ℕ,
      L * (n : ℝ) ^ (2 * r) ≤ (k : ℝ) →
      Rp (n / 2) eps * Rg k eps ≤
        D * Real.log (1 / eps) ^ 2 * (n : ℝ) ^ (-(1 / 2 : ℝ) - r) := by
  obtain ⟨Dp, hDp, hp⟩ := rateTheta_at_polynomial_count hRp
    (by norm_num) (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1 / 2) hd
  obtain ⟨Dg, hDg, hg⟩ := rateTheta_at_polynomial_count hRg
    (by norm_num) (by positivity : 0 < 2 * r) hL hd
  refine ⟨Dp * Dg, mul_pos hDp hDg, ?_⟩
  filter_upwards [hp, hg] with n hp hg
  intro hn k hk
  have hhalf : (1 / 2 : ℝ) * (n : ℝ) ^ (1 : ℝ) ≤ (n / 2 : ℕ) := by
    rw [Real.rpow_one, even_sample_half_cast hn]
    linarith
  obtain ⟨hp0, hpU⟩ := hp (n / 2) hhalf
  obtain ⟨hg0, hgU⟩ := hg k hk
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn.1
  calc
    _ ≤ (Dp * Real.log (1 / eps) * (n : ℝ) ^ (-1 * (1 / 2 : ℝ))) *
        (Dg * Real.log (1 / eps) * (n : ℝ) ^ (-(2 * r) * (1 / 2 : ℝ))) :=
      mul_le_mul hpU hgU hg0 (hp0.trans hpU)
    _ = _ := by
      have hpow : (n : ℝ) ^ (-1 * (1 / 2 : ℝ)) *
          (n : ℝ) ^ (-(2 * r) * (1 / 2 : ℝ)) =
          (n : ℝ) ^ (-(1 / 2 : ℝ) - r) := by
        rw [← Real.rpow_add hnR]
        congr 1
        ring
      calc
        _ = (Dp * Dg) * Real.log (1 / eps) ^ 2 *
          ((n : ℝ) ^ (-1 * (1 / 2 : ℝ)) * (n : ℝ) ^ (-(2 * r) * (1 / 2 : ℝ))) := by ring
        _ = _ := by rw [hpow]

/-- If [the propensity rate has order one half](hyp:hRp), [the regression rate has order one half](hyp:hRg), [the tail-count multiplier is positive](hyp:hL), [the target rate exponent is positive](hyp:hr), [the confidence argument is valid](hyp:hd), and [the endpoint tail probability has the stated eventual lower bound](hyp:hTail), then [a positive constant eventually controls the nuisance product throughout the threshold band](goal).

@node: adaptive_band_nuisance_product_rate -/
lemma adaptive_band_nuisance_product_rate (E : NeteExperiment M)
    {Rp Rg : ℕ → ℝ → ℝ} {L r delta cminus cplus : ℝ} {kappa : ℝ → ℝ}
    (hRp : RateTheta Rp (1 / 2)) (hRg : RateTheta Rg (1 / 2))
    (hL : 0 < L) (hr : 0 < r) (hd : ConfidenceDomain (delta / 6))
    (hTail : ∀ᶠ n : ℕ in atTop, L * (n : ℝ) ^ (-1 + 2 * r) ≤
      tailProb M (2 * cplus * (n : ℝ) ^ kappa (gamma M))) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ n : ℕ in atTop, EvenSampleSize n → ∀ w,
      (n : ℝ) * tailProb M (2 * cplus * (n : ℝ) ^ kappa (gamma M)) / 4 ≤
        (trainCount E n (2 * cplus * (n : ℝ) ^ kappa (gamma M)) w : ℝ) →
      ∀ t ∈ thresholdBand M cminus cplus kappa n,
        Rp (n / 2) (delta / 6) * Rg (trainCount E n t w) (delta / 6) ≤
          D * Real.log (6 / delta) ^ 2 * (n : ℝ) ^ (-(1 / 2 : ℝ) - r) := by
  obtain ⟨D, hD, hProduct⟩ := nuisance_product_at_polynomial_count hRp hRg
    (by positivity : 0 < L / 4) hr hd
  refine ⟨D, hD, ?_⟩
  filter_upwards [hTail, hProduct] with n hn hProduct
  intro heven w hCount t ht
  have hnR : 0 < (n : ℝ) := by exact_mod_cast heven.1
  have hFloor : (L / 4) * (n : ℝ) ^ (2 * r) ≤
      (n : ℝ) * tailProb M (2 * cplus * (n : ℝ) ^ kappa (gamma M)) / 4 := by
    calc
      _ = (n : ℝ) * (L * (n : ℝ) ^ (-1 + 2 * r)) / 4 := by
        have hpow : (n : ℝ) * (n : ℝ) ^ (-1 + 2 * r) = (n : ℝ) ^ (2 * r) := by
          nth_rw 1 [← Real.rpow_one (n : ℝ)]
          rw [← Real.rpow_add hnR]
          congr 1
          ring
        rw [show (n : ℝ) * (L * (n : ℝ) ^ (-1 + 2 * r)) =
          L * ((n : ℝ) * (n : ℝ) ^ (-1 + 2 * r)) by ring, hpow]
        ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hn hnR.le) (by norm_num)
  have hThreshold : trainCount E n (2 * cplus * (n : ℝ) ^ kappa (gamma M)) w ≤
      trainCount E n t w := trainCount_antitone_threshold E n w ht.2
  have hAt := hProduct heven (trainCount E n t w)
    (hFloor.trans (hCount.trans (by exact_mod_cast hThreshold)))
  have htol : 1 / (delta / 6) = 6 / delta := by ring
  simpa only [htol] using hAt

/-- Given [regularly varying noise](hyp:hRV), [an even sample](hyp:hn), [estimated overlap](hyp:hOverlap), [an almost-everywhere propensity-error bound](hyp:hp), and [almost-everywhere regression-error bounds for both treatments](hyp:hg), [the DR bias integral is bounded by the product of the two nuisance errors](goal).

@node: dr_bias_integral_bound_at_training_size -/
lemma dr_bias_integral_bound_at_training_size (E : NeteExperiment M)
    (hRV : NoiseRegularlyVarying M) {n : ℕ} (hn : EvenSampleSize n)
    {c t rp rg : ℝ} (hOverlap : EstimatedOverlap E c)
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ) (w : E.Om)
    (hp : ∀ᵐ x ∂(M.mu.map M.X), |M.p x - E.pHat n w x| ≤ rp)
    (hg : ∀ b : Bool, ∀ᵐ z ∂covariateDirectionLaw M t,
      |reg (z.1, b, z.2) - E.gHat n w z.1 b z.2| ≤ rg) :
    |∫ v, drBiasIntegrand E n reg w v ∂tailLaw M t| ≤ (2 / c) * rp * rg := by
  let := tailLaw_probability M hRV t
  have hpTail : ∀ᵐ v ∂tailLaw M t,
      |M.p (M.X v) - E.pHat n w (M.X v)| ≤ rp :=
    cond_absolutelyContinuous.ae_le (ae_of_ae_map M.measurable_X.aemeasurable hp)
  have hgTail (b : Bool) : ∀ᵐ v ∂tailLaw M t,
      |reg (M.X v, b, direction M v) - E.gHat n w (M.X v) b (direction M v)| ≤ rg :=
    ae_of_ae_map (M.measurable_X.prodMk (measurable_direction M)).aemeasurable (hg b)
  apply dr_conditional_bias_integral_bound (tailLaw M t)
    (fun v => M.p (M.X v)) (fun v => E.pHat n w (M.X v))
    (fun v => reg (M.X v, true, direction M v))
    (fun v => reg (M.X v, false, direction M v))
    (fun v => E.gHat n w (M.X v) true (direction M v))
    (fun v => E.gHat n w (M.X v) false (direction M v)) hOverlap.1
  · exact Filter.Eventually.of_forall (fun v =>
      ⟨(hOverlap.2.2 n hn w (M.X v) (M.X_mem_domain v)).1, by
        linarith [(hOverlap.2.2 n hn w (M.X v) (M.X_mem_domain v)).2]⟩)
  · exact hpTail
  · exact (hgTail true).and (hgTail false)

/-- Given [regularly varying noise](hyp:hRV), [estimated overlap](hyp:hOverlap), [a half-order propensity rate](hyp:hRp), [a half-order regression rate](hyp:hRg), [a positive tail-count multiplier](hyp:hL), [a positive target rate exponent](hyp:hr), [a valid confidence domain](hyp:hd), and [the endpoint tail-probability lower bound](hyp:hTail), [a positive constant eventually bounds DR bias uniformly over the threshold band](goal).

@node: adaptive_band_dr_bias_rate -/
lemma adaptive_band_dr_bias_rate (E : NeteExperiment M)
    (hRV : NoiseRegularlyVarying M) {Rp Rg : ℕ → ℝ → ℝ}
    {L r delta c cminus cplus : ℝ} {kappa : ℝ → ℝ}
    (hOverlap : EstimatedOverlap E c)
    (hRp : RateTheta Rp (1 / 2)) (hRg : RateTheta Rg (1 / 2))
    (hL : 0 < L) (hr : 0 < r) (hd : ConfidenceDomain (delta / 6))
    (hTail : ∀ᶠ n : ℕ in atTop, L * (n : ℝ) ^ (-1 + 2 * r) ≤
      tailProb M (2 * cplus * (n : ℝ) ^ kappa (gamma M))) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ n : ℕ in atTop, EvenSampleSize n → ∀ w,
      (n : ℝ) * tailProb M (2 * cplus * (n : ℝ) ^ kappa (gamma M)) / 4 ≤
        (trainCount E n (2 * cplus * (n : ℝ) ^ kappa (gamma M)) w : ℝ) →
      ∀ t ∈ thresholdBand M cminus cplus kappa n,
      ∀ reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ,
        (∀ᵐ x ∂(M.mu.map M.X), |M.p x - E.pHat n w x| ≤ Rp (n / 2) (delta / 6)) →
        (∀ b : Bool, ∀ᵐ z ∂covariateDirectionLaw M t,
          |reg (z.1, b, z.2) - E.gHat n w z.1 b z.2| ≤
            Rg (trainCount E n t w) (delta / 6)) →
        |∫ v, drBiasIntegrand E n reg w v ∂tailLaw M t| ≤
          D * Real.log (6 / delta) ^ 2 * (n : ℝ) ^ (-(1 / 2 : ℝ) - r) := by
  obtain ⟨D, hD, hProduct⟩ := adaptive_band_nuisance_product_rate E
    hRp hRg hL hr hd hTail
  refine ⟨(2 / c) * D, mul_pos (div_pos (by norm_num) hOverlap.1) hD, ?_⟩
  filter_upwards [hProduct] with n hProduct
  intro hn w hCount t ht reg hp hg
  have hBias := dr_bias_integral_bound_at_training_size E hRV hn hOverlap reg w hp hg
  calc
    _ ≤ (2 / c) * (Rp (n / 2) (delta / 6) * Rg (trainCount E n t w) (delta / 6)) := by
      simpa only [mul_assoc] using hBias
    _ ≤ (2 / c) * (D * Real.log (6 / delta) ^ 2 * (n : ℝ) ^ (-(1 / 2 : ℝ) - r)) :=
      mul_le_mul_of_nonneg_left (hProduct hn w hCount t ht)
        (div_nonneg (by norm_num) hOverlap.1.le)
    _ = _ := by ring

end Papers.TbsExtremeEffects
