module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIV
/-! Deterministic projected-error and calibration assembly for iterative RDIV.

The noise multiplier is retained explicitly. These deductions do not assert
the coefficient-one envelope or construct its simultaneous probability event.
-/
public section
namespace Papers.TsAdaptiveEstimationInference

/-- Suppose [the total error](hyp:hu), [the fitting error](hyp:hv), [the bias](hyp:hb),
[the calibration coefficient](hyp:hC), and [the noise scale](hyp:hnu) are nonnegative.
If [total error is at most fitting error plus bias](hyp:hsplit) and [the statistic differs
from squared total error by at most the calibration coefficient times noise times total
error plus the coefficient times squared noise](hyp:hcal), then [the statistic is at most
three times squared fitting error plus three times squared bias plus squared noise times
the sum of the squared calibration coefficient and that coefficient](goal). -/
-- @node: iter_rdiv_calibration_upper_of_error_split
lemma iter_rdiv_calibration_upper_of_error_split
    (stat u v b C nu : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hb : 0 ≤ b)
    (hC : 0 ≤ C) (hnu : 0 ≤ nu) (hsplit : u ≤ v + b)
    (hcal : |stat - u ^ 2| ≤ C * nu * u + C * nu ^ 2) :
    stat ≤ 3 * v ^ 2 + 3 * b ^ 2 + (C ^ 2 + C) * nu ^ 2 := by
  have hsq : u ^ 2 ≤ (v + b) ^ 2 := sq_le_sq₀ hu (add_nonneg hv hb) |>.2 hsplit
  have hlin := mul_le_mul_of_nonneg_left hsplit (mul_nonneg hC hnu)
  have hupper := (abs_le.mp hcal).2
  have htriangle := sq_nonneg (v - b)
  have hyoungv := sq_nonneg (v - C * nu)
  have hyoungb := sq_nonneg (b - C * nu)
  nlinarith only [hsq, hlin, hupper, htriangle, hyoungv, hyoungb]

variable {W X Z : Type*} [MeasurableSpace W] [MeasurableSpace X]
  [MeasurableSpace Z] (V : IVWorld W X Z)

/-- For [a candidate in the population Hilbert space](hyp:h), [its projected error relative
to the minimum-norm solution is at most its projected distance to the population iterate
plus that iterate's projected bias relative to the minimum-norm solution](goal). -/
-- @node: iter_rdiv_projected_error_split
lemma iter_rdiv_projected_error_split
    (h : V.Hbar.toSubmodule) (lam : ℝ) (j : ℕ) :
    ‖projCondExpOp V (h - minNormSolution V)‖ ≤
      ‖projCondExpOp V (h - populationIterate V lam j)‖ +
        ‖projCondExpOp V (populationIterate V lam j - minNormSolution V)‖ := by
  have heq : projCondExpOp V (h - minNormSolution V) =
      projCondExpOp V (h - populationIterate V lam j) +
        projCondExpOp V (populationIterate V lam j - minNormSolution V) := by
    rw [← map_add]
    congr 1
    abel
  rw [heq]
  exact norm_add_le _ _

/-- Assume [the range condition](hyp:hRange), [the source condition with exponent beta and
source vector w₀](hyp:hSource), [at least one iteration](hyp:ht), and [a nonnegative
calibration coefficient](hyp:hC). Then [a positive constant uniformly bounds the calibration
statistic by that constant times the sum of the fitting scale divided by penalty, squared
noise, and squared source-vector norm times the penalty raised to the qualification
exponent, whenever the penalty is positive, noise is nonnegative, the weighted fitting
error is bounded by the fitting scale divided by penalty, and the quadratic calibration
comparison holds](goal). -/
-- @node: iter_rdiv_projected_upper_from_stability
lemma iter_rdiv_projected_upper_from_stability
    (β : ℝ) (w₀ : V.Hbar.toSubmodule)
    (hRange : RangeCondition V) (hSource : BetaSourceCondition V β w₀)
    (t : ℕ) (ht : 1 ≤ t) (C : ℝ) (hC : 0 ≤ C) :
    ∃ K > (0 : ℝ), ∀ (h : V.Hbar.toSubmodule) (lam a delta nu stat : ℝ),
      0 < lam → 0 ≤ nu →
      lam * ‖h - populationIterate V lam t‖ ^ 2 +
          ‖projCondExpOp V (h - populationIterate V lam t)‖ ^ 2 ≤
        a * delta ^ 2 / lam →
      |stat - ‖projCondExpOp V (h - minNormSolution V)‖ ^ 2| ≤
        C * nu * ‖projCondExpOp V (h - minNormSolution V)‖ + C * nu ^ 2 →
      stat ≤ K * (a * delta ^ 2 / lam + nu ^ 2) +
        K * ‖w₀‖ ^ 2 * lam ^ qualificationExponent β t := by
  obtain ⟨Cb, hCb, hbias⟩ := iter_bias V β w₀ hRange hSource t ht
  let K := 3 + (C ^ 2 + C) + 3 * Cb
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro h lam a delta nu stat hlam hnu henergy hcal
  have hvar : ‖projCondExpOp V (h - populationIterate V lam t)‖ ^ 2 ≤
      a * delta ^ 2 / lam := by
    have hnonneg := mul_nonneg hlam.le (sq_nonneg ‖h - populationIterate V lam t‖)
    linarith only [henergy, hnonneg]
  have hnoise : 0 ≤ a * delta ^ 2 / lam := (sq_nonneg _).trans hvar
  have hb := (hbias lam hlam).2.2.2.1
  change ‖projCondExpOp V (populationIterate V lam t - minNormSolution V)‖ ^ 2 ≤
    Cb * ‖w₀‖ ^ 2 * lam ^ qualificationExponent β t at hb
  have hupper := iter_rdiv_calibration_upper_of_error_split stat
    ‖projCondExpOp V (h - minNormSolution V)‖
    ‖projCondExpOp V (h - populationIterate V lam t)‖
    ‖projCondExpOp V (populationIterate V lam t - minNormSolution V)‖ C nu
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hC hnu
    (iter_rdiv_projected_error_split V h lam t) hcal
  have h3 : 3 ≤ K := by dsimp [K]; nlinarith only [hC, hCb, sq_nonneg C]
  have hnuK : C ^ 2 + C ≤ K := by dsimp [K]; linarith only [hCb]
  have hbK : 3 * Cb ≤ K := by dsimp [K]; nlinarith only [hC, sq_nonneg C]
  have hscale : 0 ≤ ‖w₀‖ ^ 2 * lam ^ qualificationExponent β t := by positivity
  have hvarK := mul_le_mul_of_nonneg_right h3 hnoise
  have hnuK := mul_le_mul_of_nonneg_right hnuK (sq_nonneg nu)
  have hbK := mul_le_mul_of_nonneg_right hbK hscale
  nlinarith only [hupper, hvar, hb, hvarK, hnuK, hbK]

/-- Assume [the range condition](hyp:hRange), [the source condition with exponent beta and
source vector w₀](hyp:hSource), [at least one iteration](hyp:_ht), [a nonnegative calibration
coefficient](hyp:hC), [a positive inflation factor](hyp:hL), [its square is at least
three](hyp:hLsq), and [its square is at least the squared calibration coefficient plus
that coefficient](hyp:hCL). Then [every candidate satisfying the weighted fitting and
quadratic calibration bounds at accuracies divided by the inflation factor has calibration
statistic at most the public fitting scale divided by penalty plus squared public noise
plus three times squared source-vector norm times the penalty raised to the qualification
exponent, for positive penalties and nonnegative fitting coefficients and noise](goal). -/
lemma iter_rdiv_projected_upper_from_preinflation_uniform
    (β : ℝ) (w₀ : V.Hbar.toSubmodule)
    (hRange : RangeCondition V) (hSource : BetaSourceCondition V β w₀)
    (t : ℕ) (_ht : 1 ≤ t) (C L : ℝ) (hC : 0 ≤ C) (hL : 0 < L)
    (hLsq : 3 ≤ L ^ 2) (hCL : C ^ 2 + C ≤ L ^ 2) :
    ∀ (h : V.Hbar.toSubmodule) (lam a delta nu stat : ℝ),
      0 < lam → 0 ≤ a → 0 ≤ nu →
      lam * ‖h - populationIterate V lam t‖ ^ 2 +
          ‖projCondExpOp V (h - populationIterate V lam t)‖ ^ 2 ≤
        a * (delta / L) ^ 2 / lam →
      |stat - ‖projCondExpOp V (h - minNormSolution V)‖ ^ 2| ≤
        C * (nu / L) * ‖projCondExpOp V (h - minNormSolution V)‖ +
          C * (nu / L) ^ 2 →
      stat ≤ a * delta ^ 2 / lam + nu ^ 2 +
        3 * ‖w₀‖ ^ 2 * lam ^ qualificationExponent β t := by
  intro h lam a delta nu stat hlam ha hnu henergy hcal
  have hvar : ‖projCondExpOp V (h - populationIterate V lam t)‖ ^ 2 ≤
      a * (delta / L) ^ 2 / lam := by
    have hpos := mul_nonneg hlam.le (sq_nonneg ‖h - populationIterate V lam t‖)
    linarith only [henergy, hpos]
  have hb := iter_bias_projected_le V β w₀ hRange hSource lam hlam t
  have hupper := iter_rdiv_calibration_upper_of_error_split stat
    ‖projCondExpOp V (h - minNormSolution V)‖
    ‖projCondExpOp V (h - populationIterate V lam t)‖
    ‖projCondExpOp V (populationIterate V lam t - minNormSolution V)‖ C (nu / L)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hC (div_nonneg hnu hL.le)
    (iter_rdiv_projected_error_split V h lam t) hcal
  have hfit : 3 * (a * (delta / L) ^ 2 / lam) ≤ a * delta ^ 2 / lam := by
    have hscale := mul_le_mul_of_nonneg_right hLsq
      (div_nonneg (mul_nonneg ha (sq_nonneg delta)) hlam.le)
    apply (le_of_mul_le_mul_right ?_ (sq_pos_of_pos hL))
    calc
      (3 * (a * (delta / L) ^ 2 / lam)) * L ^ 2 =
          3 * (a * delta ^ 2 / lam) := by field_simp [ne_of_gt hL, ne_of_gt hlam]
      _ ≤ (a * delta ^ 2 / lam) * L ^ 2 := by nlinarith only [hscale]
  have hcalibration : (C ^ 2 + C) * (nu / L) ^ 2 ≤ nu ^ 2 := by
    apply (le_of_mul_le_mul_right ?_ (sq_pos_of_pos hL))
    calc
      ((C ^ 2 + C) * (nu / L) ^ 2) * L ^ 2 =
          (C ^ 2 + C) * nu ^ 2 := by field_simp [ne_of_gt hL, ne_of_gt hlam]
      _ ≤ nu ^ 2 * L ^ 2 := by
        nlinarith only [mul_le_mul_of_nonneg_right hCL (sq_nonneg nu)]
  linarith only [hupper, hvar, hb, hfit, hcalibration]

/-- Assume [the range condition](hyp:hRange), [the source condition with exponent beta and
source vector w₀](hyp:hSource), [at least one iteration](hyp:ht), [a nonnegative calibration
coefficient](hyp:hC), [a positive inflation factor](hyp:hL), [its square is at least
three](hyp:hLsq), and [its square dominates the squared calibration coefficient plus
that coefficient](hyp:hCL). Then [there is a positive bias constant such that the
calibration statistic is at most the public fitting scale divided by penalty plus squared
public noise plus the bias constant times squared source-vector norm times the penalty
raised to the qualification exponent, whenever the weighted fitting and quadratic
calibration bounds hold at accuracies divided by the inflation factor, the penalty is
positive, and the fitting coefficient and noise are nonnegative](goal). -/
lemma iter_rdiv_projected_upper_from_preinflation
    (β : ℝ) (w₀ : V.Hbar.toSubmodule)
    (hRange : RangeCondition V) (hSource : BetaSourceCondition V β w₀)
    (t : ℕ) (ht : 1 ≤ t) (C L : ℝ) (hC : 0 ≤ C) (hL : 0 < L)
    (hLsq : 3 ≤ L ^ 2) (hCL : C ^ 2 + C ≤ L ^ 2) :
    ∃ K > (0 : ℝ), ∀ (h : V.Hbar.toSubmodule) (lam a delta nu stat : ℝ),
      0 < lam → 0 ≤ a → 0 ≤ nu →
      lam * ‖h - populationIterate V lam t‖ ^ 2 +
          ‖projCondExpOp V (h - populationIterate V lam t)‖ ^ 2 ≤
        a * (delta / L) ^ 2 / lam →
      |stat - ‖projCondExpOp V (h - minNormSolution V)‖ ^ 2| ≤
        C * (nu / L) * ‖projCondExpOp V (h - minNormSolution V)‖ +
          C * (nu / L) ^ 2 →
      stat ≤ a * delta ^ 2 / lam + nu ^ 2 +
        K * ‖w₀‖ ^ 2 * lam ^ qualificationExponent β t := by
  obtain ⟨Cb, hCb, hbias⟩ := iter_bias V β w₀ hRange hSource t ht
  refine ⟨3 * Cb, by positivity, ?_⟩
  intro h lam a delta nu stat hlam ha hnu henergy hcal
  have hvar : ‖projCondExpOp V (h - populationIterate V lam t)‖ ^ 2 ≤
      a * (delta / L) ^ 2 / lam := by
    have hpos := mul_nonneg hlam.le (sq_nonneg ‖h - populationIterate V lam t‖)
    linarith only [henergy, hpos]
  have hb := (hbias lam hlam).2.2.2.1
  change ‖projCondExpOp V (populationIterate V lam t - minNormSolution V)‖ ^ 2 ≤
    Cb * ‖w₀‖ ^ 2 * lam ^ qualificationExponent β t at hb
  have hupper := iter_rdiv_calibration_upper_of_error_split stat
    ‖projCondExpOp V (h - minNormSolution V)‖
    ‖projCondExpOp V (h - populationIterate V lam t)‖
    ‖projCondExpOp V (populationIterate V lam t - minNormSolution V)‖ C (nu / L)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hC (div_nonneg hnu hL.le)
    (iter_rdiv_projected_error_split V h lam t) hcal
  have hfit : 3 * (a * (delta / L) ^ 2 / lam) ≤ a * delta ^ 2 / lam := by
    have hscale := mul_le_mul_of_nonneg_right hLsq
      (div_nonneg (mul_nonneg ha (sq_nonneg delta)) hlam.le)
    apply (le_of_mul_le_mul_right ?_ (sq_pos_of_pos hL))
    calc
      (3 * (a * (delta / L) ^ 2 / lam)) * L ^ 2 =
          3 * (a * delta ^ 2 / lam) := by field_simp [ne_of_gt hL, ne_of_gt hlam]
      _ ≤ (a * delta ^ 2 / lam) * L ^ 2 := by nlinarith only [hscale]
  have hcalibration : (C ^ 2 + C) * (nu / L) ^ 2 ≤ nu ^ 2 := by
    apply (le_of_mul_le_mul_right ?_ (sq_pos_of_pos hL))
    calc
      ((C ^ 2 + C) * (nu / L) ^ 2) * L ^ 2 =
          (C ^ 2 + C) * nu ^ 2 := by field_simp [ne_of_gt hL, ne_of_gt hlam]
      _ ≤ nu ^ 2 * L ^ 2 := by
        nlinarith only [mul_le_mul_of_nonneg_right hCL (sq_nonneg nu)]
  linarith only [hupper, hvar, hb, hfit, hcalibration]

end Papers.TsAdaptiveEstimationInference
