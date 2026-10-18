module
public import Papers.TbsExtremeEffects.Helpers.ProductAssembly
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Logarithmic exponent control and finite-variance NETE product assembly. -/

@[expose] public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory
variable {q d : ℕ} {M : ExtremeModel q d}

-- @node: exp_sub_one_secant_bound
/-- If [the argument is nonnegative](hyp:hz) and [at most one](hyp:hz1), then [the exponential increment is bounded by its secant slope on this interval](goal). -/
lemma exp_sub_one_secant_bound {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Real.exp z - 1 ≤ (Real.exp 1 - 1) * z := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    (show 0 ≤ 1 - z by linarith) hz (show 1 - z + z = 1 by ring)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, Real.exp_zero] at h
  linarith

-- @node: radial_increment_log_bound
/-- If [the threshold is at least `exp 1`](hyp:ht), [the exponent perturbation is nonnegative](hyp:ha), [the multiplier is nonnegative](hyp:hK), and [the exponent–log-threshold product is at most one](hyp:hz), then [the radial increment has the stated logarithmic bound](goal). -/
lemma radial_increment_log_bound {t a K : ℝ} (ht : Real.exp 1 ≤ t)
    (ha : 0 ≤ a) (hK : 0 ≤ K) (hz : a * Real.log t ≤ 1) :
    t ^ a - 1 + K * a * t ^ a ≤
      (Real.exp 1 - 1 + K * Real.exp 1) * (a * Real.log t) := by
  have htpos : 0 < t := (Real.exp_pos 1).trans_le ht
  have hlog : 1 ≤ Real.log t := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) ht
  have hz0 : 0 ≤ a * Real.log t := mul_nonneg ha (by linarith)
  have hpow : t ^ a = Real.exp (a * Real.log t) := by
    rw [Real.rpow_def_of_pos htpos, mul_comm]
  have hpowle : t ^ a ≤ Real.exp 1 := by rw [hpow]; exact Real.exp_le_exp.mpr hz
  have hinc : t ^ a - 1 ≤ (Real.exp 1 - 1) * (a * Real.log t) := by
    rw [hpow]; exact exp_sub_one_secant_bound hz0 hz
  have halog : a ≤ a * Real.log t := by nlinarith
  have hterm : K * a * t ^ a ≤ K * Real.exp 1 * (a * Real.log t) := by
    calc
      _ ≤ K * a * Real.exp 1 := mul_le_mul_of_nonneg_left hpowle (mul_nonneg hK ha)
      _ ≤ K * Real.exp 1 * (a * Real.log t) := by
        simpa only [mul_assoc, mul_comm, mul_left_comm] using
          mul_le_mul_of_nonneg_left halog (mul_nonneg hK (Real.exp_pos 1).le)
  nlinarith only [hinc, hterm]

-- @node: radialQ_log_bound
/-- Given [a sample size](hyp:n), [the Hill coefficient, tolerance, exponent cap, and threshold](hyp:Cg,delta,a0,t), and [an exponent-error rate](hyp:Ralpha), if [the Hill parameter is nonnegative](hyp:hg), [the exponent-error rate is nonnegative](hyp:ha), [that rate is below the exponent cap](hyp:ha0), [the Hill-error bound is nonnegative](hyp:hb), and [the threshold is at least `exp 1`](hyp:ht), then [the radial product-error budget has the stated logarithmic bound](goal). -/
lemma radialQ_log_bound (n : ℕ) (Cg delta a0 t : ℝ) (Ralpha : ℕ → ℝ → ℝ)
    (hg : 0 ≤ gamma M) (ha : 0 ≤ Ralpha n (delta / 12))
    (ha0 : Ralpha n (delta / 12) ≤ a0)
    (hb : 0 ≤ hillErrorBound M Cg delta n) (ht : Real.exp 1 ≤ t) :
    radialQ M Cg delta Ralpha n ≤ (gamma M + a0 + |M.alpha|) *
      (Ralpha n (delta / 12) * Real.log t + hillErrorBound M Cg delta n) := by
  have hlog : 1 ≤ Real.log t := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) ht
  have hz : Ralpha n (delta / 12) ≤ Ralpha n (delta / 12) * Real.log t := by
    nlinarith
  have hzb : 0 ≤ Ralpha n (delta / 12) * Real.log t := by positivity
  have h0 : 0 ≤ a0 := ha.trans ha0
  have hprod := mul_le_mul_of_nonneg_right ha0 hb
  have hgam := mul_le_mul_of_nonneg_left hz hg
  unfold radialQ
  nlinarith [mul_nonneg hg hb, mul_nonneg h0 hzb, mul_nonneg (abs_nonneg M.alpha) hzb]

-- @node: variance_sampling_radius_of_count
/-- If [the variance cap is nonnegative](hyp:hV), [the tolerance is positive](hyp:hd), [the tail mass is positive](hyp:hm), and [the observed count is at least one quarter of that mass](hyp:hc), then [the variance sampling radius is bounded by the displayed mass-based radius](goal). -/
lemma variance_sampling_radius_of_count {V delta mass count : ℝ}
    (hV : 0 ≤ V) (hd : 0 < delta) (hm : 0 < mass)
    (hc : mass / 4 ≤ count) :
    Real.sqrt (12 * V / (delta * count)) ≤
      Real.sqrt 48 * Real.sqrt (V / (delta * mass)) := by
  have hcount : 0 < count := (by positivity : 0 < mass / 4).trans_le hc
  have hden : delta * (mass / 4) ≤ delta * count :=
    mul_le_mul_of_nonneg_left hc hd.le
  calc
    _ ≤ Real.sqrt (12 * V / (delta * (mass / 4))) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_left (by positivity)
        (by positivity) hden)
    _ = Real.sqrt (48 * (V / (delta * mass))) := by congr 1; field_simp; ring
    _ = _ := Real.sqrt_mul (by norm_num) _

/-- For [an experiment](hyp:E), [overlap, tail, simplification, variance, and confidence constants](hyp:c,Cgb,a0,D,Cg,V,delta), [nuisance rates](hyp:Rp,Rg,Ralpha), [sample size](hyp:n), [threshold](hyp:t), [DR and IPW truncation bounds](hyp:Bdr,Bipw), and [outcome](hyp:w), [the first-factor-rate event](goal) requires adequate count, exponent and Hill accuracy, both first-factor errors, and conditional simplified first-factor and radial-rate bounds. These are [clauses 1](step:1), [2](step:2), [3](step:3), [4](step:4), [5](step:5), and [6](step:6). -/
-- @node: ProductFirstFactorRates
def ProductFirstFactorRates (E : NeteExperiment M)
    (c Cgb a0 D Cg V delta : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ)
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
      ∀ kind : EstimatorKind,
        |etaEstimate E kind n t w - etaTarget M| ≤
          D * simplifiedRate E kind V Cg delta Rp Rg Ralpha n t w ∧
        Ralpha n (delta / 12) * Real.log t + hillErrorBound M Cg delta n ≤
          simplifiedRate E kind V Cg delta Rp Rg Ralpha n t w)

-- @node: productRateFactors_of_first_factor_rates
/-- Given [an experiment](hyp:E), [overlap, tail, simplification, variance, and confidence constants](hyp:c,Cgb,a0,D,Cg,V,delta), [nuisance rates](hyp:Rp,Rg,Ralpha), [sample size](hyp:n), [threshold](hyp:t), [DR and IPW truncation bounds](hyp:Bdr,Bipw), and [an outcome](hyp:w), if [the NETE target factorizes radially](hyp:hTarget), [the radial target is positive](hyp:hh), [the Hill parameter is nonnegative](hyp:hg), [the simplification coefficient is positive](hyp:hD), [the exponent-error rate is below its cap](hyp:ha0), and [the first-factor-rate event holds](hyp:h), then [the product-rate-factor event holds with the displayed assembled coefficient](goal). -/
lemma productRateFactors_of_first_factor_rates (E : NeteExperiment M)
    (c Cgb a0 D Cg V delta : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (n : ℕ) (t : ℝ) (Bdr Bipw : E.Om → ℝ) (w : E.Om)
    (hTarget : thetaNETE M = etaTarget M * (1 / radialH M))
    (hh : 0 < radialH M) (hg : 0 ≤ gamma M) (hD : 0 < D)
    (ha0 : Ralpha n (delta / 12) ≤ a0)
    (h : ProductFirstFactorRates E c Cgb a0 D Cg V delta Rp Rg Ralpha n t Bdr Bipw w) :
    ProductRateFactors E c Cgb a0
      (2 / radialH M * D + |etaTarget M| * (2 / radialH M ^ 2) *
        (gamma M + a0 + |M.alpha|)) Cg V delta Rp Rg Ralpha n t Bdr Bipw w := by
  obtain ⟨hcount, hAlpha, hHill, hDR, hIPW, hFirst⟩ := h
  refine ⟨hcount, hAlpha, hHill, hDR, hIPW, ?_⟩
  intro hMom ht hz hQ
  have ha := (abs_nonneg _).trans hAlpha
  have hb := (abs_nonneg _).trans hHill
  have hmu := muHat_bound_of_radialQ_small E n Cg delta Ralpha w hh hg ha hAlpha hHill hQ
  have hrad := radialQ_log_bound n Cg delta a0 t Ralpha hg ha ha0 hb ht
  have hCq : 0 ≤ gamma M + a0 + |M.alpha| := by
    have := ha.trans ha0
    positivity
  have hOne (kind : EstimatorKind) :
      |neteEstimator E kind n t (delta / 6) w - thetaNETE M| ≤
        (2 / radialH M * D + |etaTarget M| * (2 / radialH M ^ 2) *
          (gamma M + a0 + |M.alpha|)) *
          simplifiedRate E kind V Cg delta Rp Rg Ralpha n t w := by
    obtain ⟨hEta, hRate⟩ := hFirst hMom ht hz hQ kind
    have hR : 0 ≤ simplifiedRate E kind V Cg delta Rp Rg Ralpha n t w := by
      have hlog : 0 ≤ Real.log t := by
        have hlog1 : 1 ≤ Real.log t := by
          simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) ht
        linarith
      exact (add_nonneg (mul_nonneg ha hlog) hb).trans hRate
    have hMu := muHat_radial_error_bound E n Cg delta Ralpha w hh hg ha hAlpha hHill
    have hprod := product_estimate_error_bound hTarget hEta hMu
    have hradRate : radialQ M Cg delta Ralpha n ≤
        (gamma M + a0 + |M.alpha|) * simplifiedRate E kind V Cg delta Rp Rg Ralpha n t w :=
      hrad.trans (mul_le_mul_of_nonneg_left hRate hCq)
    have hradius : radialError E Cg delta Ralpha n w ≤
        (2 / radialH M ^ 2) * (gamma M + a0 + |M.alpha|) *
          simplifiedRate E kind V Cg delta Rp Rg Ralpha n t w := by
      apply hmu.2.trans
      calc
        _ = (2 / radialH M ^ 2) * radialQ M Cg delta Ralpha n := by ring
        _ ≤ (2 / radialH M ^ 2) * ((gamma M + a0 + |M.alpha|) *
            simplifiedRate E kind V Cg delta Rp Rg Ralpha n t w) :=
          mul_le_mul_of_nonneg_left hradRate (by positivity)
        _ = _ := by ring
    have hfinal := hprod.trans (add_le_add
      (mul_le_mul_of_nonneg_right hmu.1 (mul_nonneg hD.le hR))
      (mul_le_mul_of_nonneg_left hradius (abs_nonneg _)))
    calc
      _ = |etaEstimate E kind n t w * muHat E n (delta / 6) w - thetaNETE M| := by
        cases kind <;> rfl
      _ ≤ _ := hfinal
      _ = _ := by ring
  exact ⟨hOne .dr, hOne .ipw⟩

end Papers.TbsExtremeEffects
