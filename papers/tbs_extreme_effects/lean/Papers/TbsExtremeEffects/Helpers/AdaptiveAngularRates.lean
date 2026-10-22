module
public import Papers.TbsExtremeEffects.Helpers.ThresholdBand
public import Papers.TbsExtremeEffects.Helpers.AngularRates
public import Papers.TbsExtremeEffects.Helpers.AdaptiveExponent
public import Papers.TbsExtremeEffects.Helpers.HomogeneityError

/-! Angular logarithmic rates uniformly over deterministic threshold bands. -/

@[expose] public section
set_option linter.style.multiGoal false
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
noncomputable section
variable {q d : ℕ} {M : ExtremeModel q d}

/-- [A positive tail index](hyp:hb), [a positive sampling exponent](hyp:hs), and [the low-regime cutoff on that exponent](hyp:hsCut) ensure that [both angular decay exponents dominate the sampling exponent](goal).

@node: lowRegime_angular_exponents -/
lemma lowRegime_angular_exponents {s : ℝ} (hb : 0 < M.beta)
    (hs : 0 < s) (hsCut : s < 1 / (2 + max 1 M.beta)) :
    s ≤ min 1 M.beta * lowRegimeExponent s (gamma M) ∧
    s ≤ (M.beta * s / (1 - 2 * s)) * lowRegimeExponent s (gamma M) := by
  have hden : 0 < 2 + max 1 M.beta := by
    have := le_max_left (1 : ℝ) M.beta
    linarith
  have hcut : s * (2 + max 1 M.beta) < 1 := (lt_div_iff₀ hden).mp hsCut
  have hsThird : s < 1 / 3 := by
    have h := mul_le_mul_of_nonneg_left (le_max_left (1 : ℝ) M.beta) hs.le
    nlinarith
  have hsDen : 0 < 1 - 2 * s := by linarith
  constructor
  · by_cases h : M.beta ≤ 1
    · simp only [min_eq_right h, lowRegimeExponent, gamma]
      have heq : M.beta * ((1 - 2 * s) * (1 / M.beta)) = 1 - 2 * s := by
        field_simp
      rw [heq]
      linarith
    · have hb1 : 1 ≤ M.beta := le_of_not_ge h
      have hsb : s * (2 + M.beta) < 1 := by
        have h := mul_le_mul_of_nonneg_left (le_max_right (1 : ℝ) M.beta) hs.le
        nlinarith
      simp only [min_eq_left hb1, lowRegimeExponent, gamma, one_mul]
      rw [mul_one_div]
      exact (le_div_iff₀ hb).mpr (by nlinarith)
  · have heq : (M.beta * s / (1 - 2 * s)) *
        lowRegimeExponent s (gamma M) = s := by
      unfold lowRegimeExponent gamma
      field_simp [hb.ne', hsDen.ne', show 1 - s * 2 ≠ 0 by linarith]
      <;> ring
    exact heq.ge

/-- [A positive tail index](hyp:hb), [an exponent at or above the regime cutoff](hyp:hsCut), and [an exponent below one half](hyp:hsHalf) ensure that [both high-regime angular exponents dominate the balanced count rate](goal).

@node: highRegime_angular_exponents -/
lemma highRegime_angular_exponents {s : ℝ} (hb : 0 < M.beta)
    (hsCut : 1 / (2 + max 1 M.beta) ≤ s) (hsHalf : s < 1 / 2) :
    corRateExponent M.beta ≤ min 1 M.beta * highRegimeExponent (gamma M) ∧
    corRateExponent M.beta ≤ (M.beta * s / (1 - 2 * s)) *
      highRegimeExponent (gamma M) := by
  have hsDen : 0 < 1 - 2 * s := by linarith
  by_cases h : M.beta ≤ 1
  · have hg : 1 ≤ gamma M := (le_div_iff₀ hb).mpr (by linarith)
    have hs : 1 / 3 ≤ s := by norm_num [max_eq_left h] at hsCut ⊢; exact hsCut
    simp only [min_eq_right h, highRegimeExponent, min_eq_left hg,
      corRateExponent, max_eq_right h]
    unfold gamma
    constructor
    · have heq : M.beta * ((1 / M.beta) / (1 + 2 * 1)) = 1 / 3 := by
        field_simp
        <;> ring
      rw [heq]
      norm_num
    · have heq : (M.beta * s / (1 - 2 * s)) *
          ((1 / M.beta) / (1 + 2 * 1)) = s / (3 * (1 - 2 * s)) := by
        field_simp
        <;> ring
      rw [heq]
      apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 3) hsDen)).mpr
      nlinarith
  · have hb1 : 1 ≤ M.beta := le_of_not_ge h
    have hg : gamma M ≤ 1 := (div_le_iff₀ hb).mpr (by linarith)
    have hden : 0 < 2 + M.beta := by positivity
    have hs : 1 ≤ s * (2 + M.beta) := by
      apply (div_le_iff₀ hden).mp
      simpa only [max_eq_right hb1] using hsCut
    have hk : highRegimeExponent (gamma M) = 1 / (2 + M.beta) := by
      rw [highRegimeExponent, min_eq_right hg]
      unfold gamma
      field_simp
      <;> ring
    rw [hk]
    simp only [corRateExponent, max_eq_left hb1, min_eq_left hb1, one_mul]
    refine ⟨le_rfl, ?_⟩
    have hcoef : 1 ≤ M.beta * s / (1 - 2 * s) :=
      (le_div_iff₀ hsDen).mpr (by nlinarith)
    exact le_mul_of_one_le_left (by positivity) hcoef

/-- For [an experiment](hyp:E), [an estimator type](hyp:kind), [a threshold rule](hyp:tn), [a logarithmic exponent](hyp:k), [a variance constant](hyp:V), [a Hill-error constant](hyp:Cg), [a confidence tolerance](hyp:delta), [a tail-index exponent](hyp:cAlpha), [a polynomial rate exponent](hyp:r), [a sample size](hyp:n), and [a data realization](hyp:w), [the angular corollary rate](goal) is the stated sum of stochastic, nuisance, angular, and tail-error terms. -/
def corRateAngular (E : NeteExperiment M) (kind : EstimatorKind)
    (tn : ℕ → E.Om → ℝ) (k V Cg delta cAlpha r : ℝ) (n : ℕ) (w : E.Om) :=
  Real.sqrt (V / delta) * (n : ℝ) ^ (-r) +
    (match kind with
     | .dr => Real.log (6 / delta) ^ 2 * (n : ℝ) ^ (-(1 / 2 : ℝ) - r)
     | .ipw => Real.log (6 / delta) * (n : ℝ) ^ (-(1 / 2 : ℝ))) +
    eBar M (tn n w) + (Real.log n) ^ k * (n : ℝ) ^ (-r) +
    (n : ℝ) ^ (-cAlpha) * Real.log n * Real.log (6 / delta) +
    |M.alpha| * hillErrorBound M Cg delta n

/-- [A positive threshold constant](hyp:hc), [a nonnegative inverse-power exponent](hyp:hz), [a sample size at least one](hyp:hn), [a rate exponent no larger than the available polynomial decay](hyp:hr), and [a threshold above its polynomial lower bound](hyp:ht) imply that [the inverse threshold power is bounded by the corresponding inverse sample-size power](goal).

@node: polynomial_threshold_inverse_power_bound -/
lemma polynomial_threshold_inverse_power_bound {c z b r t : ℝ} {n : ℕ}
    (hc : 0 < c) (hz : 0 ≤ z) (hn : 1 ≤ (n : ℝ))
    (hr : r ≤ z * b) (ht : c * (n : ℝ) ^ b ≤ t) :
    t ^ (-z) ≤ c ^ (-z) * (n : ℝ) ^ (-r) := by
  have hnpos : 0 < (n : ℝ) := zero_lt_one.trans_le hn
  have hlpos : 0 < c * (n : ℝ) ^ b := by positivity
  calc
    t ^ (-z) ≤ (c * (n : ℝ) ^ b) ^ (-z) :=
      Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith)
        hlpos (hlpos.trans_le ht) ht
    _ = c ^ (-z) * (n : ℝ) ^ (b * (-z)) := by
      rw [Real.mul_rpow hc.le (Real.rpow_nonneg hnpos.le _),
        ← Real.rpow_mul hnpos.le]
    _ ≤ c ^ (-z) * (n : ℝ) ^ (-r) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hn (by nlinarith))
        (Real.rpow_nonneg hc.le _)

/-- Given [regularly varying noise](hyp:hRV), [asymptotic homogeneity](hyp:hHom), [a positive tail exponent below one half](hyp:hs,hsHalf), [an angular-rate bound](hyp:hAngular), [positive ordered band constants](hyp:hc,hcc), [a valid confidence level](hyp:hd,hd1), [a positive band-growth exponent](hyp:hk), and [two rate-exponent restrictions](hyp:hr1,hr2), [there is a positive constant eventually comparing the original corollary rate with its angular-rate version throughout the threshold band](goal).

@node: adaptive_corRate_angular_comparison -/
lemma adaptive_corRate_angular_comparison (E : NeteExperiment M) (kind : EstimatorKind)
    (tp : TailParams) (hRV : NoiseRegularlyVarying M)
    (hHom : AsymptoticHomogeneity M) (hs : 0 < tp.s) (hsHalf : tp.s < 1 / 2)
    (CW k tW cminus cplus V Cg delta cAlpha r : ℝ) (kappa : ℝ → ℝ)
    (tn : ℕ → E.Om → ℝ) (hAngular : AngularRateBound M tp CW k tW)
    (hc : 0 < cminus) (hcc : cminus ≤ cplus) (hd : 0 < delta) (hd1 : delta < 1 / 2)
    (hk : 0 < kappa (gamma M))
    (hr1 : r ≤ min 1 M.beta * kappa (gamma M))
    (hr2 : r ≤ (M.beta * tp.s / (1 - 2 * tp.s)) * kappa (gamma M)) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ n : ℕ in atTop, ∀ w,
      tn n w ∈ thresholdBand M cminus cplus kappa n →
      0 ≤ hillErrorBound M Cg delta n →
      corRate E kind tn V Cg delta cAlpha r n w ≤
        D * corRateAngular E kind tn k V Cg delta cAlpha r n w := by
  let b := kappa (gamma M)
  let z := M.beta * tp.s / (1 - 2 * tp.s)
  let H := b + |Real.log (2 * cplus)|
  let J := H ^ k * (cminus / 2) ^ (-min 1 M.beta) + (cminus / 2) ^ (-z)
  let B := 2 * M.L * CW * J
  have hcp : 0 < cplus := hc.trans_le hcc
  have hz : 0 ≤ z := by dsimp [z]; exact (div_pos (mul_pos hRV.1 hs) (by linarith)).le
  have hmin : 0 ≤ min 1 M.beta := le_min (by norm_num) hRV.1.le
  have hH : 0 < H := by dsimp [H, b]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hL : 0 ≤ M.L := hHom.2.2.2.1
  have hCW : 0 ≤ CW := hAngular.1.le
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hHom.2.2.2.1) hAngular.1.le) hJ
  have hLower : Tendsto (fun n : ℕ => (cminus / 2) * (n : ℝ) ^ b) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by positivity)).mpr
      ((tendsto_rpow_atTop hk).comp tendsto_natCast_atTop_atTop)
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (1 : ℝ))
  obtain ⟨Tb, hTb⟩ := eventually_atTop.mp (eBar_eventually_bddAbove M hHom)
  refine ⟨B + 1, by positivity, ?_⟩
  filter_upwards [hLower.eventually (eventually_ge_atTop (max tW (max 1 Tb))),
    hlog, eventually_ge_atTop (1 : ℕ)] with n hLowerN hnlog hn1
  change 1 ≤ Real.log (n : ℝ) at hnlog
  intro w ht hHill
  have htlo : (cminus / 2) * (n : ℝ) ^ b ≤ tn n w := ht.1
  have hthi : tn n w ≤ 2 * cplus * (n : ℝ) ^ b := ht.2
  have htW : tW ≤ tn n w := ((le_max_left _ _).trans hLowerN).trans htlo
  have ht1 : 1 ≤ tn n w :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans hLowerN)).trans htlo
  have htTb : Tb ≤ tn n w :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans hLowerN)).trans htlo
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnpos : 0 < (n : ℝ) := zero_lt_one.trans_le hnR
  have hLogT : (Real.log (tn n w)) ^ k ≤ H ^ k * (Real.log n) ^ k := by
    calc
      _ ≤ (H * Real.log n) ^ k :=
        Real.rpow_le_rpow (Real.log_nonneg ht1)
          (polynomial_threshold_log_bound (by positivity) hk.le hnlog
            (zero_lt_one.trans_le ht1) hthi) hAngular.2.1
      _ = _ := Real.mul_rpow hH.le (by linarith)
  have hPower1 := polynomial_threshold_inverse_power_bound
    (by positivity : 0 < cminus / 2) hmin hnR hr1 htlo
  have hPower2 := polynomial_threshold_inverse_power_bound
    (by positivity : 0 < cminus / 2) hz hnR hr2 htlo
  have hLogOne : 1 ≤ (Real.log (n : ℝ)) ^ k :=
    Real.one_le_rpow hnlog hAngular.2.1
  have hAng : 2 * M.L * angularW1 M (tn n w) ≤
      B * ((Real.log n) ^ k * (n : ℝ) ^ (-r)) := by
    apply (angular_term_bound M tp hHom hAngular htW).trans
    have hFirst := mul_le_mul hLogT hPower1
      (Real.rpow_nonneg (zero_lt_one.trans_le ht1).le _) (by positivity)
    have hSecond : (tn n w) ^ (-z) ≤
        ((cminus / 2) ^ (-z) * (n : ℝ) ^ (-r)) * (Real.log n) ^ k := by
      apply hPower2.trans
      exact le_mul_of_one_le_right (by positivity) hLogOne
    have hSum := add_le_add hFirst hSecond
    have hScale := mul_le_mul_of_nonneg_left hSum
      (by positivity : 0 ≤ 2 * M.L * CW)
    convert hScale using 1 <;> dsimp [angularTerm, B, J, z] <;> ring
  have he : 0 ≤ eBar M (tn n w) :=
    eBar_nonneg M hHom (zero_lt_one.trans_le ht1) (hTb _ htTb)
  have hLogDelta : 0 ≤ Real.log (6 / delta) :=
    Real.log_nonneg ((one_le_div hd).mpr (by linarith))
  let R := Real.sqrt (V / delta) * (n : ℝ) ^ (-r) +
      (match kind with
       | .dr => Real.log (6 / delta) ^ 2 * (n : ℝ) ^ (-(1 / 2 : ℝ) - r)
       | .ipw => Real.log (6 / delta) * (n : ℝ) ^ (-(1 / 2 : ℝ))) +
      eBar M (tn n w) +
      (n : ℝ) ^ (-cAlpha) * Real.log n * Real.log (6 / delta) +
      |M.alpha| * hillErrorBound M Cg delta n
  let A := (Real.log (n : ℝ)) ^ k * (n : ℝ) ^ (-r)
  have hRest : 0 ≤ R := by dsimp [R]; cases kind <;> positivity
  have hRate : 0 ≤ A := by dsimp [A]; positivity
  calc
    corRate E kind tn V Cg delta cAlpha r n w = R + 2 * M.L * angularW1 M (tn n w) := by
      dsimp [corRate, R]; cases kind <;> simp only <;> ring
    _ ≤ R + B * A := add_le_add_right hAng R
    _ ≤ (B + 1) * (R + A) := by
      nlinarith only [mul_nonneg hB hRest, hRate]
    _ = (B + 1) * corRateAngular E kind tn k V Cg delta cAlpha r n w := by
      dsimp [corRateAngular, R, A]; cases kind <;> simp only <;> ring


end
end Papers.TbsExtremeEffects
