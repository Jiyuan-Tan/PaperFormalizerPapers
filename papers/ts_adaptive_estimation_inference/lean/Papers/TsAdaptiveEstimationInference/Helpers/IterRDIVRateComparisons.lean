module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVOracleEvent
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVRateAssembly
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVProjectedEnvelope
/-! Deterministic rate comparisons from recursive stability and calibration.
The internal accuracy rescaling leaves the public discrepancy threshold fixed.
-/
public section
set_option linter.style.longLine false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter
open scoped Topology
variable {W X Z Ω : Type*} [MeasurableSpace W] [MeasurableSpace X]
  [MeasurableSpace Z] [MeasurableSpace Ω]

/-- Under [the range condition](hyp:hRange), [the source condition with exponent beta and
source vector w₀](hyp:hSource), and [at least one iteration](hyp:ht), [positive strong-error
and bias constants give three comparisons: the nonnegative calibration statistic is bounded
by iterative noise plus penalty-power bias, projected squared error by four times statistic
plus noise, and strong squared error by a constant times iterative stability plus statistic
and noise raised to beta divided by beta plus one, whenever fitting and calibration scales
and the propagation coefficient are nonnegative, the penalty is positive, the projected
and Hilbert fitting bounds hold, and the calibration comparison has coefficient one
sixteenth](goal). -/
-- @node: iter_rdiv_rate_comparisons_of_stability
lemma iter_rdiv_rate_comparisons_of_stability
    (V : IVWorld W X Z) (β : ℝ) (w₀ : V.Hbar.toSubmodule) (t : ℕ)
    (hRange : RangeCondition V) (hSource : BetaSourceCondition V β w₀)
    (ht : 1 ≤ t) :
    ∃ CV > 0, ∃ Cb > 0, ∀ (d v a lam stat : ℝ) (h : V.Hbar.toSubmodule),
      0 ≤ d → 0 ≤ v → 0 ≤ a → 0 < lam → 0 ≤ stat →
      ‖projCondExpOp V (h - populationIterate V lam t)‖ ^ 2 ≤
        a * d ^ 2 / lam / 16 →
      ‖h - populationIterate V lam t‖ ^ 2 ≤ a * d ^ 2 / lam ^ 2 →
      |stat - ‖projCondExpOp V (h - minNormSolution V)‖ ^ 2| ≤
        v / 16 * ‖projCondExpOp V (h - minNormSolution V)‖ + v ^ 2 / 16 →
      stat ≤ iterRdivNoiseLevel a d v lam + Cb * lam ^ qualificationExponent β t ∧
      ‖projCondExpOp V (h - minNormSolution V)‖ ^ 2 ≤
        4 * (stat + iterRdivNoiseLevel a d v lam) ∧
      ‖h - minNormSolution V‖ ^ 2 ≤ CV * (iterRdivStability a d lam +
        (stat + iterRdivNoiseLevel a d v lam) ^ (β / (β + 1))) := by
  obtain ⟨Cbias, hCbias, hbias⟩ := iter_bias V β w₀ hRange hSource t ht
  let γ := β / (β + 1)
  let S := ‖w₀‖ ^ (2 / (β + 1)) * (10 : ℝ) ^ γ
  refine ⟨3 + 2 * S, by dsimp [S]; positivity, 3 * Cbias * ‖w₀‖ ^ 2 + 1,
    by positivity, ?_⟩
  intro d v a lam stat h hd hv ha hlam hstat hweakvar hstrongvar hcal
  let U := ‖projCondExpOp V (h - minNormSolution V)‖
  let W := ‖projCondExpOp V (h - populationIterate V lam t)‖
  let R := ‖projCondExpOp V (populationIterate V lam t - minNormSolution V)‖
  let F := a * d ^ 2 / lam
  let Q := stat + iterRdivNoiseLevel a d v lam
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q, iterRdivNoiseLevel, iterRdivScale]; positivity
  have hFQ : F ≤ Q := by
    dsimp [Q, F, iterRdivNoiseLevel, iterRdivScale]
    linarith only [hstat, sq_nonneg v]
  have hvQ : v ^ 2 ≤ Q := by
    dsimp [Q, iterRdivNoiseLevel, iterRdivScale]
    linarith only [hstat, hF]
  have hstatQ : stat ≤ Q := by
    dsimp [Q, iterRdivNoiseLevel, iterRdivScale]
    linarith only [hF, sq_nonneg v]
  have htriangle : U ^ 2 ≤ 2 * W ^ 2 + 2 * R ^ 2 := by
    have heq : projCondExpOp V (h - minNormSolution V) =
        projCondExpOp V (h - populationIterate V lam t) +
          projCondExpOp V (populationIterate V lam t - minNormSolution V) := by
      simp only [map_sub]; abel
    dsimp only [U, W, R]
    rw [heq]
    simpa only [mul_add] using
      (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2).trans add_sq_le
  have hreverse : R ^ 2 ≤ 2 * U ^ 2 + 2 * W ^ 2 := by
    have heq : projCondExpOp V (populationIterate V lam t - minNormSolution V) =
        projCondExpOp V (h - minNormSolution V) -
          projCondExpOp V (h - populationIterate V lam t) := by
      simp only [map_sub]; abel
    dsimp only [U, W, R]
    rw [heq]
    simpa only [mul_add] using
      (pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 2).trans add_sq_le
  have hγ : 0 ≤ γ := by dsimp [γ]; positivity [hSource.1]
  have hcal' : |stat - U ^ 2| ≤ v * U + v ^ 2 := by
    apply hcal.trans
    have hU : 0 ≤ U := norm_nonneg _
    nlinarith only [mul_nonneg hv hU, sq_nonneg v]
  have hweak : U ^ 2 ≤ 4 * Q := by
    have hlo := (abs_le.mp hcal').1
    have hy := sq_nonneg (U - v)
    nlinarith only [hlo, hy, hvQ, hstatQ, hQ]
  have hR : R ^ 2 ≤ 10 * Q := by
    nlinarith only [hreverse, hweak, hweakvar, hFQ, hF]
  have hstrongbias : ‖populationIterate V lam t - minNormSolution V‖ ^ 2 ≤
      S * Q ^ γ := by
    have hi := (hbias lam hlam).2.2.2.2.2
    have heq : R ^ (2 * β / (β + 1)) = (R ^ 2) ^ γ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
      congr 1
      dsimp [γ]; ring
    change _ ≤ ‖w₀‖ ^ (2 / (β + 1)) * R ^ (2 * β / (β + 1)) at hi
    rw [heq] at hi
    have hm := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (sq_nonneg R) hR hγ)
      (show 0 ≤ ‖w₀‖ ^ (2 / (β + 1)) by positivity)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 10) hQ] at hm
    exact hi.trans (by simpa only [S, mul_assoc] using hm)
  have htotal : ‖h - minNormSolution V‖ ^ 2 ≤
      2 * ‖h - populationIterate V lam t‖ ^ 2 +
        2 * ‖populationIterate V lam t - minNormSolution V‖ ^ 2 := by
    have heq : h - minNormSolution V =
        (h - populationIterate V lam t) +
          (populationIterate V lam t - minNormSolution V) := by abel
    rw [heq]
    simpa only [mul_add] using
      (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2).trans add_sq_le
  refine ⟨?_, hweak, ?_⟩
  · have hb := (hbias lam hlam).2.2.2.1
    change R ^ 2 ≤ Cbias * ‖w₀‖ ^ 2 * lam ^ qualificationExponent β t at hb
    have hi := (abs_le.mp hcal).2
    change stat - U ^ 2 ≤ v / 16 * U + v ^ 2 / 16 at hi
    have hy := sq_nonneg (U - v / 16)
    have hp : 0 ≤ lam ^ qualificationExponent β t := Real.rpow_nonneg hlam.le _
    dsimp only [iterRdivNoiseLevel, iterRdivScale]
    nlinarith only [hb, hi, hy, htriangle, hweakvar, hF, sq_nonneg v, hp]
  · have hV : 0 ≤ iterRdivStability a d lam := by
      unfold iterRdivStability iterRdivScale; positivity
    have hpow : 0 ≤ Q ^ γ := Real.rpow_nonneg hQ _
    have hS : 0 ≤ S := by dsimp [S]; positivity
    change _ ≤ (3 + 2 * S) * (iterRdivStability a d lam + Q ^ γ)
    change _ ≤ iterRdivStability a d lam at hstrongvar
    nlinarith only [htotal, hstrongvar, hstrongbias, hV, hpow,
      mul_nonneg hS hV]

/-- If [the fitting coefficient is at least one](hyp:hA) and [the calibration coefficient
is positive](hyp:hC), then [an inflation factor of at least one makes the fitting
coefficient divided by its square, the calibration coefficient divided by it, and the
calibration coefficient divided by its square all at most one sixteenth](goal). -/
-- @node: iter_rdiv_rate_rescaling
lemma iter_rdiv_rate_rescaling (A C : ℝ) (hA : 1 ≤ A) (hC : 0 < C) :
    ∃ L ≥ (1 : ℝ), A / L ^ 2 ≤ 1 / 16 ∧ C / L ≤ 1 / 16 ∧
      C / L ^ 2 ≤ 1 / 16 := by
  let L := 16 * (A + C + 1)
  have hL : 1 ≤ L := by dsimp [L]; linarith only [hA, hC]
  have hAL : 16 * A ≤ L := by dsimp [L]; linarith only [hC]
  have hCL : 16 * C ≤ L := by dsimp [L]; linarith only [hA]
  have hsq : L ≤ L ^ 2 := by nlinarith only [hL]
  refine ⟨L, hL, ?_, ?_, ?_⟩
  · apply (div_le_iff₀ (by positivity : 0 < L ^ 2)).2
    nlinarith only [hAL, hsq]
  · apply (div_le_iff₀ (by linarith only [hL] : 0 < L)).2
    linarith only [hCL]
  · apply (div_le_iff₀ (by positivity : 0 < L ^ 2)).2
    nlinarith only [hCL, hsq]

/-- Assume [a valid grid ratio](hyp:hρ), [the range condition](hyp:hRange), [the source
condition with exponent beta and source vector w₀](hyp:hSource), and [at least one
iteration](hyp:ht). Then [a positive upper limit on the oracle multiplier ensures that
each smaller positive multiplier admits a constant giving a measurable event with the
original probability guarantee, the discrepancy envelope with bias coefficient three
times squared source-vector norm, and the iterative projected and strong squared-error
rates for the selected penalty, whenever sample size, propagation coefficient and fitting
accuracy are positive, calibration accuracy is nonnegative, the stable oracle radius is
at most two, and a measurable initial event supplies nonnegative discrepancies and the
fitting and calibration comparisons with coefficient one sixteenth](goal). -/
-- @node: iter_rdiv_rate_event_of_small_comparisons
lemma iter_rdiv_rate_event_of_small_comparisons
    (V : IVWorld W X Z) (β : ℝ) (w₀ : V.Hbar.toSubmodule) (t : ℕ)
    (ρ : ℝ) (hρ : GridDomain ρ)
    (hRange : RangeCondition V) (hSource : BetaSourceCondition V β w₀)
    (ht : 1 ≤ t) :
    ∃ cmax > 0, ∀ c ∈ Set.Ioc (0 : ℝ) cmax, ∃ C > 0,
    ∀ (P : Measure Ω) [IsProbabilityMeasure P] (ξ a : ℝ)
      (δ ν : ℕ → ℝ) (n : ℕ) (E : Set Ω)
      (candidate : ℝ → Ω → V.Hbar.toSubmodule)
      (D : Ω → V.Hbar.toSubmodule → ℝ),
      0 < n → 0 < a → 0 < δ n → 0 ≤ ν n →
      MeasurableSet E → 1 - ξ ≤ P.real E →
      IterRDIVOracleSegmentStability ρ c a β t δ ν n →
      iterRdivOracleRadius c a β t δ ν n ≤ 2 →
      (∀ ω ∈ E, ∀ lam ∈ regGrid ρ n,
        lam ∈ Set.Icc (iterRdivOraclePoint ρ c a β t δ ν n) 2 →
        0 ≤ D ω (candidate lam ω) ∧
        ‖projCondExpOp V (candidate lam ω - populationIterate V lam t)‖ ^ 2 ≤
          a * δ n ^ 2 / lam / 16 ∧
        ‖candidate lam ω - populationIterate V lam t‖ ^ 2 ≤
          a * δ n ^ 2 / lam ^ 2 ∧
        |D ω (candidate lam ω) -
          ‖projCondExpOp V (candidate lam ω - minNormSolution V)‖ ^ 2| ≤
          ν n / 16 * ‖projCondExpOp V (candidate lam ω - minNormSolution V)‖ +
            ν n ^ 2 / 16) →
      ∃ F : Set Ω, MeasurableSet F ∧ 1 - ξ ≤ P.real F ∧
      (∀ ω ∈ F, ∀ lam ∈ regGrid ρ n,
        lam ∈ Set.Icc (iterRdivOraclePoint ρ c a β t δ ν n) 2 →
        D ω (candidate lam ω) ≤ iterRdivNoiseLevel a (δ n) (ν n) lam +
          3 * ‖w₀‖ ^ 2 * lam ^ qualificationExponent β t) ∧ ∀ ω ∈ F,
        let lam := selectedPenalty ρ n (fun l => D ω (candidate l ω))
          (iterRdivNoiseLevel a (δ n) (ν n))
        ‖projCondExpOp V (candidate lam ω - minNormSolution V)‖ ^ 2 ≤
          C * iterRdivErrorScale β a (δ n) (ν n) t ∧
        ‖candidate lam ω - minNormSolution V‖ ^ 2 ≤ C *
          ((a * δ n ^ 2) ^ ((qualificationExponent β t - 1) /
            (qualificationExponent β t + 1)) +
            iterRdivErrorScale β a (δ n) (ν n) t ^ (β / (β + 1))) := by
  obtain ⟨CV, hCV, Cb, hCb, hcompare⟩ :=
    iter_rdiv_rate_comparisons_of_stability V β w₀ t hRange hSource ht
  have hq : 1 < qualificationExponent β t := by
    have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
    exact lt_min (by linarith only [hSource.1]) (by linarith only [htR])
  refine ⟨1 / (2 * Cb + 1), by positivity, ?_⟩
  intro c hc
  have hc1 : c ≤ 1 := hc.2.trans ((div_le_one (by positivity)).2 (by linarith))
  have hsmall (p : ℝ) (hp : 1 ≤ p) : Cb * c ^ p ≤ 1 / 2 := by
    have hpow : c ^ p ≤ c := by
      conv_rhs => rw [← Real.rpow_one c]
      exact Real.rpow_le_rpow_of_exponent_ge hc.1 hc1 hp
    have hm := (le_div_iff₀ (by positivity : 0 < 2 * Cb + 1)).1 hc.2
    exact (mul_le_mul_of_nonneg_left hpow hCb.le).trans (by nlinarith only [hm, hc.1])
  obtain ⟨C, hC, hrate⟩ := iter_rdiv_common_dp_oracle_rates
    4 CV Cb ρ c β t hρ hc.1 hSource.1 ht (by norm_num) hCV hCb
    (hsmall _ (by linarith only [hq])) (hsmall _ hq.le)
  refine ⟨C, hC, ?_⟩
  intro P _ ξ a δ ν n E candidate D hn ha hd hv hE hpE horacle hradius hgood
  have hround := oraclePoint_radius_bounds ρ _ n hρ hradius horacle
  have hρpos : 0 < ρ := by linarith only [hρ.1]
  have hlpos : 0 < iterRdivOraclePoint ρ c a β t δ ν n := by
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hround.1
    rw [iterRdivOraclePoint, ← hk]
    exact mul_pos (by norm_num) (pow_pos hρpos _)
  have hS : StabilityRegionSubset (Set.Icc (iterRdivOraclePoint ρ c a β t δ ν n) 2) :=
    fun _ h => ⟨hlpos.trans_le h.1, h.2⟩
  have hγ : 0 ≤ β / (β + 1) := by positivity [hSource.1]
  have hcomp := iter_rdiv_generic_comparisons_of_accepted_bounds P (projCondExpOp V)
    (minNormSolution V) ρ ξ 4 CV Cb (β / (β + 1)) (qualificationExponent β t)
    a (δ n) (ν n) n (Set.Icc (iterRdivOraclePoint ρ c a β t δ ν n) 2) E candidate D
    hE hpE hS hCV.le (fun ω hω lam hl hs => (hgood ω hω lam hl hs).1)
    (fun ω hω lam hl hs => by
      obtain ⟨hs0, hw, hv', hcal⟩ := hgood ω hω lam hl hs
      exact (hcompare _ _ _ _ _ _ hd.le hv ha.le (hS hs).1 hs0 hw hv' hcal).1)
    (fun ω hω lam hl hs => by
      obtain ⟨hs0, hw, hv', hcal⟩ := hgood ω hω lam hl hs
      exact (hcompare _ _ _ _ _ _ hd.le hv ha.le (hS hs).1 hs0 hw hv' hcal).2)
  have henvelope : ∀ ω ∈ E, ∀ lam ∈ regGrid ρ n,
      lam ∈ Set.Icc (iterRdivOraclePoint ρ c a β t δ ν n) 2 →
      D ω (candidate lam ω) ≤ iterRdivNoiseLevel a (δ n) (ν n) lam +
        3 * ‖w₀‖ ^ 2 * lam ^ qualificationExponent β t := by
    intro ω hω lam hl hs
    obtain ⟨_, hw, _, hcal⟩ := hgood ω hω lam hl hs
    have hlam := (hS hs).1
    have hcal' : |D ω (candidate lam ω) -
        ‖projCondExpOp V (candidate lam ω - minNormSolution V)‖ ^ 2| ≤
        (ν n / 4) * ‖projCondExpOp V (candidate lam ω - minNormSolution V)‖ +
          (ν n / 4) ^ 2 := by
      nlinarith only [hcal, mul_nonneg hv
        (norm_nonneg (projCondExpOp V (candidate lam ω - minNormSolution V)))]
    have hu := iter_rdiv_calibration_upper_of_error_split
      (D ω (candidate lam ω))
      ‖projCondExpOp V (candidate lam ω - minNormSolution V)‖
      ‖projCondExpOp V (candidate lam ω - populationIterate V lam t)‖
      ‖projCondExpOp V (populationIterate V lam t - minNormSolution V)‖
      1 (ν n / 4) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      (by norm_num) (by positivity)
      (iter_rdiv_projected_error_split V (candidate lam ω) lam t)
      (by simpa only [one_mul] using hcal')
    have hb := iter_bias_projected_le V β w₀ hRange hSource lam hlam t
    have hnoise : 0 ≤ a * δ n ^ 2 / lam := by positivity
    dsimp only [iterRdivNoiseLevel, iterRdivScale]
    nlinarith only [hu, hw, hb, hnoise, sq_nonneg (ν n)]
  refine ⟨E, hE, hpE, henvelope, ?_⟩
  intro ω hω
  have hb := hrate P (projCondExpOp V) (minNormSolution V) ξ a (δ n) (ν n)
    n E (iterRdivOraclePoint ρ c a β t δ ν n) candidate D hn ha.le
    (mul_pos ha (sq_pos_of_pos hd)) hv hround.1 hlpos hround.2.1 hround.2.2 hcomp
    (fun ω hω lam hl hs => by
      obtain ⟨hs0, hw, hv', hcal⟩ := hgood ω hω lam hl hs
      exact ⟨hs0, (hcompare _ _ _ _ _ _ hd.le hv ha.le (hS hs).1 hs0 hw hv' hcal).2.2⟩)
    ω hω
  exact ⟨hb.2.2.1, hb.2.2.2⟩

/-- Assume [fixed-center loss concentration](hyp:hFix), [squared-loss concentration](hyp:hSq),
[localized density concentration](hyp:hLi), [the instrumental-variable model](hyp:hIV),
[the range condition](hyp:hRange), [density realizability](hyp:hDensity), [the density
bounds](hyp:hBounds), [the outcome bound](hyp:hY), [the hypothesis-class bound](hyp:hHyp),
[a valid grid ratio](hyp:hρ), [a confidence level strictly between zero and one](hyp:hξ),
[a propagation coefficient at least one](hyp:ha), and [at least one iteration](hyp:ht).
Suppose also [the pilot satisfies its regression rate](hyp:hPilot), [the density estimate
selects likelihood maximizers](hyp:hMLE), [the fitting classes are measurable](hyp:hMeas),
[the likelihood processes are measurable](hyp:hLik), [the selected density](hyp:hDV) and
[selected pilot](hyp:hPV) have coherent versions, [the pilot is bounded by B](hyp:hPilotBound),
[fixed-center suprema have coherent versions](hyp:hVersion), [the raw density](hyp:hG)
and [hypothesis](hyp:hH) curves bound critical radii, [the raw curves dominate confidence
floors](hyp:hFloor), and [the base accuracies are calibrated](hyp:hScale). Then [a sufficient
inflation threshold gives, for nonnegative vanishing calibrated public accuracies and a
source condition, a positive range of oracle multipliers such that realizable selected
iterates with attained minima admit eventual events carrying the discrepancy envelope
with bias factor three and both iterative error rates: projected squared error is bounded
by a constant times the iterative error scale, and strong squared error by that constant
times the fitting qualification rate plus the iterative error scale raised to beta divided
by beta plus one](goal). -/
-- @node: iter_rdiv_eventual_rate_from_joint_event
lemma iter_rdiv_eventual_rate_from_joint_event
    {pilotInputSupport : Set Z} (V : IVWorld W X Z)
    (hFix : IterRDIVFixedCenterLocalizedConcentration (Ω := Ω) V)
    (hSq : IterRDIVSquaredLossLocalizedConcentration (Ω := Ω) V)
    (hLi : LiLocalizedConcentration V)
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG ρ ξ a : ℝ) (t : ℕ)
    (hIV : RDIVSetting V mu g₀) (hRange : RangeCondition V)
    (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hY : OutcomeBounded V B) (hHyp : HypothesisClassBounded V support B)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (sample : AnalysisSample V P) (split : SampleSplit)
    (gHat : ℕ → Ω → X → Z → ℝ) (rHat : ℕ → Ω → Z → ℝ)
    (rawG rawH rawR : ℕ → ℝ → ℝ) (baseδ baseν : ℕ → ℝ)
    (hρ : GridDomain ρ) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1) (ha : 1 ≤ a) (ht : 1 ≤ t)
    (hPilot : PilotRegressionRate V P sample split rHat rawR)
    (hMLE : MLEMaximizerSelected V P sample split G gHat)
    (hMeas : RDIVClassesMeasurable V P sample split mu G g₀ gHat)
    (hLik : RDIVLikelihoodProcessesMeasurable V G g₀)
    (hDV : RDIVSelectedDensityVersion V P sample split mu gHat)
    (hPV : RDIVSelectedPilotVersion V P sample split rHat)
    (hPilotBound : PilotBounded V P rHat pilotInputSupport B)
    (hVersion : IterRDIVFixedCenterSupremumVersion V P sample split mu gHat ρ)
    (hG : DensityCriticalRadiusBound V G g₀ rawG)
    (hH : HypothesisCriticalRadiusBound V mu G rawH ρ)
    (hFloor : RDIVRadiusFloor rawG rawH ρ)
    (hScale : RDIVScaleCalibration ρ ξ baseδ baseν rawG rawH rawR t) :
    ∃ required ≥ (1 : ℝ), ∀ (κδ κν β : ℝ) (w₀ : V.Hbar.toSubmodule)
      (δ ν : ℕ → ℝ),
      CalibratedValidBounds δ ν baseδ baseν κδ κν required →
      CalibrationDeterministic δ ν → BetaSourceCondition V β w₀ →
      ∃ cmax > 0, ∀ c ∈ Set.Ioc (0 : ℝ) cmax,
      ∀ (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule),
      IterRealizableRDIV V ρ c a β t δ ν →
      IterRDIVMinimaAttained V P sample split mu gHat ρ t iter →
      ∃ C > 0, ∀ᶠ n in atTop, ∃ E : Set Ω,
        IterRDIVDiscrepancyEnvelope V P sample split mu gHat rHat
          ρ ξ c a β t δ ν w₀ iter n E 3 ∧ ∀ ω ∈ E,
        let lam := selectedPenalty ρ n
          (fun l => rdivCalibrationStat V P sample split mu gHat rHat n ω (iter n t l ω))
          (iterRdivNoiseLevel a (δ n) (ν n))
        ‖projCondExpOp V (iter n t lam ω - minNormSolution V)‖ ^ 2 ≤
          C * iterRdivErrorScale β a (δ n) (ν n) t ∧
        ‖iter n t lam ω - minNormSolution V‖ ^ 2 ≤ C *
          ((a * δ n ^ 2) ^ ((qualificationExponent β t - 1) /
            (qualificationExponent β t + 1)) +
            iterRdivErrorScale β a (δ n) (ν n) t ^ (β / (β + 1))) := by
  obtain ⟨D, hD, Ccal, hCcal, hevent⟩ := iter_rdiv_joint_stability_calibration_event
    (pilotInputSupport := pilotInputSupport) V hFix hSq hLi mu G g₀ support B c₀ CG
    hIV hRange hDensity hBounds hY hHyp
  obtain ⟨R, hR, hevent⟩ := hevent P inferInstance sample split gHat rHat ρ
    rawG rawH rawR hPilot hMLE hMeas hLik hDV hPV hPilotBound hVersion hG hH hFloor
  have hA := (iterRdivStabilityCoefficients_bounds D hD).2.2 t ht
  obtain ⟨L, hL, hAL, hCL, hCLsq⟩ := iter_rdiv_rate_rescaling
    (iterRdivStabilityCoefficients D t) Ccal hA hCcal
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨K, hK, hradii⟩ := iter_rdiv_calibrated_radii V mu G g₀ ρ
    rawG rawH rawR hG hH hFloor
  refine ⟨max (L * R) K, hK.trans (le_max_right _ _), ?_⟩
  intro κδ κν β w₀ δ ν hInflation hNonneg hSource
  have hκδ : R ≤ κδ / L := (le_div_iff₀ hLpos).2 (by
    have hb := (le_max_left (L * R) K).trans hInflation.2.2.1
    nlinarith only [hb])
  have hκν : R ≤ κν / L := (le_div_iff₀ hLpos).2 (by
    have hb := (le_max_left (L * R) K).trans hInflation.2.2.2.1
    nlinarith only [hb])
  have hscaled : CalibratedValidBounds (fun n => δ n / L) (fun n => ν n / L)
      baseδ baseν (κδ / L) (κν / L) R := by
    refine ⟨hR.trans hκδ, hR.trans hκν, hκδ, hκν, ?_, ?_⟩
    · intro n; dsimp only; rw [hInflation.2.2.2.2.1 n]; ring
    · intro n; dsimp only; rw [hInflation.2.2.2.2.2 n]; ring
  have hquarter : ξ / 4 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith only [hξ.1, hξ.2]
  have hRates (n : ℕ) (hn : 0 < n) :
      0 ≤ rawG n (ξ / 4) ∧
      0 ≤ rawH n (iterGridConfidence ρ ξ n t / 4) ∧ 0 ≤ rawR n (ξ / 4) := by
    obtain ⟨hbudget, heq⟩ := iter_rdiv_quarter_budget ρ ξ n t hξ ht
    have hh := (hH n hn _ hbudget).1.1.le
    rw [heq] at hh
    exact ⟨(hG n hn _ hquarter).1.le, hh, (hPilot.2 n hn _ hquarter).1⟩
  have hlim := iter_rdiv_inflated_scales_tendsto δ ν baseδ baseν κδ κν _
    hInflation hNonneg hScale.2.2
  have hq : 0 < qualificationExponent β t := by
    unfold qualificationExponent
    exact lt_min (by linarith only [hSource.1]) (by positivity)
  have hradlim (c : ℝ) : Tendsto (iterRdivOracleRadius c a β t δ ν) atTop (𝓝 0) := by
    have hd : Tendsto (fun n => a * δ n ^ 2) atTop (𝓝 0) := by
      simpa using (hlim.1.pow 2).const_mul a
    have hp := hd.rpow_const_nhds_zero (by positivity : 0 < 1 / (qualificationExponent β t + 1))
    have hv := hlim.2.rpow_const_nhds_zero (by positivity : 0 < 2 / qualificationExponent β t)
    change Tendsto (fun n => c * max ((a * δ n ^ 2) ^
      (1 / (qualificationExponent β t + 1))) (ν n ^ (2 / qualificationExponent β t))) atTop (𝓝 0)
    simpa only [max_self, mul_zero] using (hp.max hv).const_mul c
  obtain ⟨cmax, hcmax, hrate⟩ := iter_rdiv_rate_event_of_small_comparisons
    (Ω := Ω) V β w₀ t ρ hρ hRange hSource ht
  refine ⟨cmax, hcmax, ?_⟩
  intro c hc iter hRealizable hMinima
  obtain ⟨C, hC, hrate⟩ := hrate c hc
  refine ⟨C, hC, ?_⟩
  have horacle := iter_rdiv_oracle_exists_of_inflation ρ c a β ξ t δ ν
    baseδ baseν rawG rawH rawR κδ κν _ hρ hc.1 ha hSource.1 hξ hScale
    hInflation hNonneg hRates
  filter_upwards [horacle, (tendsto_order.1 (hradlim c)).2 2 (by norm_num),
    eventually_gt_atTop (0 : ℕ)] with n hnOracle hnRadius hn
  have hρpos : 0 < ρ := by linarith only [hρ.1]
  have hdom (lam : ℝ) (hlam : lam ∈ regGrid ρ n)
      (_ : lam ∈ Set.Icc (iterRdivOraclePoint ρ c a β t δ ν n) 2) :
      lam ∈ Set.Ioc (0 : ℝ) 2 := by
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hlam
    refine ⟨mul_pos (by norm_num) (pow_pos hρpos _), ?_⟩
    have hp := pow_le_pow_of_le_one hρpos.le hρ.2.le (Nat.zero_le k)
    simpa only [pow_zero, mul_one, gridValue] using
      mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2)
  obtain ⟨E, hE, hpE, hfit, hcal⟩ := hevent ξ t (fun n => δ n / L)
    (fun n => ν n / L) baseδ baseν (κδ / L) (κν / L) hρ hξ hScale hscaled
    n (Set.Icc (iterRdivOraclePoint ρ c a β t δ ν n) 2)
    (iterRdivOracleRadius c a β t δ ν n) ⟨hnOracle, fun lam _ hs => hs.1⟩
    (fun j lam => iter n j lam)
    hn hdom (fun lam hl hs j hj hjt => hRealizable n hnOracle j hj hjt lam hl hs)
    (fun lam hl _ => (hMinima n hn lam hl).1)
    (fun lam hl ω => ((hMinima n hn lam hl).1.2 t ht le_rfl ω).1)
    (fun lam hl => (hMinima n hn lam hl).2 t le_rfl)
  have hInflationK : CalibratedValidBounds δ ν baseδ baseν κδ κν K :=
    ⟨hInflation.1, hInflation.2.1, (le_max_right _ _).trans hInflation.2.2.1,
      (le_max_right _ _).trans hInflation.2.2.2.1, hInflation.2.2.2.2⟩
  have hd := (hradii ξ t δ ν baseδ baseν κδ κν K hξ hScale hInflationK n hn).1
  have hrateN := hrate P ξ a δ ν n E (fun lam => iter n t lam)
    (fun ω h => rdivCalibrationStat V P sample split mu gHat rHat n ω h)
    hn (lt_of_lt_of_le zero_lt_one ha) hd (hNonneg.2 n) hE hpE hnOracle hnRadius.le
  have hgood : ∀ ω ∈ E, ∀ lam ∈ regGrid ρ n,
      lam ∈ Set.Icc (iterRdivOraclePoint ρ c a β t δ ν n) 2 →
      0 ≤ rdivCalibrationStat V P sample split mu gHat rHat n ω (iter n t lam ω) ∧
      ‖projCondExpOp V (iter n t lam ω - populationIterate V lam t)‖ ^ 2 ≤
        a * δ n ^ 2 / lam / 16 ∧
      ‖iter n t lam ω - populationIterate V lam t‖ ^ 2 ≤ a * δ n ^ 2 / lam ^ 2 ∧
      |rdivCalibrationStat V P sample split mu gHat rHat n ω (iter n t lam ω) -
        ‖projCondExpOp V (iter n t lam ω - minNormSolution V)‖ ^ 2| ≤
        ν n / 16 * ‖projCondExpOp V (iter n t lam ω - minNormSolution V)‖ +
          ν n ^ 2 / 16 := by
    intro ω hω lam hl hs
    obtain ⟨henergy, hstrong⟩ := hfit ω hω lam hl hs t ht le_rfl
    have hlam := (hdom lam hl hs).1
    have hcoef : iterRdivStabilityCoefficients D t / L ^ 2 ≤ a / 16 :=
      hAL.trans (by linarith only [ha])
    have hnum : iterRdivStabilityCoefficients D t * (δ n / L) ^ 2 ≤
        a * δ n ^ 2 / 16 := by
      convert mul_le_mul_of_nonneg_right hcoef (sq_nonneg (δ n)) using 1 <;> (first | rfl | ring)
    have hweak : ‖projCondExpOp V (iter n t lam ω - populationIterate V lam t)‖ ^ 2 ≤
        a * δ n ^ 2 / lam / 16 := by
      have hm := div_le_div_of_nonneg_right hnum hlam.le
      have he := mul_nonneg hlam.le (sq_nonneg ‖iter n t lam ω - populationIterate V lam t‖)
      have heq : a * δ n ^ 2 / 16 / lam = a * δ n ^ 2 / lam / 16 := by ring
      rw [heq] at hm
      linarith only [henergy, hm, he]
    have hstrong' : ‖iter n t lam ω - populationIterate V lam t‖ ^ 2 ≤
        a * δ n ^ 2 / lam ^ 2 := by
      apply hstrong.trans
      apply div_le_div_of_nonneg_right _ (sq_nonneg lam)
      have hn0 : 0 ≤ a * δ n ^ 2 := mul_nonneg (by linarith only [ha]) (sq_nonneg _)
      linarith only [hnum, hn0]
    have hcal' := hcal ω hω lam hl
    have hcalnum : Ccal * (ν n / L) *
        ‖projCondExpOp V (iter n t lam ω - minNormSolution V)‖ +
          Ccal * (ν n / L) ^ 2 ≤
        ν n / 16 * ‖projCondExpOp V (iter n t lam ω - minNormSolution V)‖ +
          ν n ^ 2 / 16 := by
      have h1 := mul_le_mul_of_nonneg_right hCL
        (mul_nonneg (hNonneg.2 n) (norm_nonneg (projCondExpOp V
          (iter n t lam ω - minNormSolution V))))
      have h2 := mul_le_mul_of_nonneg_right hCLsq (sq_nonneg (ν n))
      convert add_le_add h1 h2 using 1 <;> (first | rfl | ring)
    refine ⟨?_, hweak, hstrong', hcal'.trans hcalnum⟩
    unfold rdivCalibrationStat blockAverage
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  obtain ⟨F, hF, hpF, henv, hrates⟩ := hrateN hgood
  exact ⟨F, ⟨hF, hpF, by norm_num, henv⟩, hrates⟩

end Papers.TsAdaptiveEstimationInference
