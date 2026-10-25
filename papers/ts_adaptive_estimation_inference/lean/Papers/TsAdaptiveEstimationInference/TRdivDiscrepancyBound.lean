module
public import Papers.TsAdaptiveEstimationInference.Helpers.Selection
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIV
/-! TRdivDiscrepancyBound for adaptive inverse problems. -/
public section
set_option linter.style.longLine false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter
open scoped Topology
variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]
  {pilotInputSupport : Set 𝒵}
  (V : IVWorld 𝒲 𝒳 𝒵) (P : Measure Ω) [IsProbabilityMeasure P]
  (sample : AnalysisSample V P) (split : SampleSplit)
-- rawG/rawH/rawR are the confidence-parametric input bounds. The hScale
-- premise explicitly instantiates their evaluated public curves; the public
-- δ and ν in every conclusion are calibrated from exactly that instantiation.
-- The public log floor is rdivPublicLogScale ρ ξ; component-budget floors
-- are handled locally through the fixed calibration multipliers.
variable (ρ ξ B β : ℝ) (w₀ : V.Hbar.toSubmodule)
  (δ ν baseδ baseν : ℕ → ℝ) (rawG rawH rawR tildeδ : ℕ → ℝ → ℝ)
  (κδ κν required c₀ CG Cm : ℝ) (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ)
  (mu : Measure 𝒳) (G : Set (𝒳 → 𝒵 → ℝ)) (g₀ : 𝒳 → 𝒵 → ℝ)
  (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (rHat : ℕ → Ω → 𝒵 → ℝ)
  (support : Set (𝒳 × 𝒵)) (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
  (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule)
  (a b c : ℝ) (t : ℕ)
/-- With [localized likelihood concentration](hyp:hLi_of_gate), [localized vector
concentration](hyp:hVector_of_gate), [a grid factor at least one-half and less than one](hyp:hρ), [a failure
level strictly between zero and one](hyp:hξ), and [a valid IV density model](hyp:hIV),
[there is a positive calibration threshold, uniform over inflation rules, source
exponents and witnesses, and accuracy curves, such that the range and source
conditions, solution and density realizability, density bounds, the pilot
regression rate, bounded outcomes, hypotheses and pilot, measurable fitting
classes and likelihood processes, valid fitting-supremum and selected density
and pilot versions, density and hypothesis critical-radius bounds with their
floor, public scale calibration using component-budget-evaluated accuracy curves,
attained fitting minima, sufficient inflation, deterministic accuracy curves,
and likelihood-maximizing density estimates imply the existence of a comparison
constant at least 64 and, at every positive sample size, a measurable event of
probability at least one minus the failure level carrying the RDIV comparisons
with that constant and the discrepancy envelope with bias coefficient 64](goal).

The public accuracy curves are defined by evaluating the primitive bounds
at the allocated component budgets, before applying the paper's relabelling
convention (main.tex:258 and appendices.tex:126–129). Calibration is stated
literally at ξ and η_n for these public curves, with the prescribed public
logarithmic floor. The primitive radius and pilot hypotheses retain their
original confidence domains. The local common-event construction uses the
same raw curves: ξ/4 for density and pilot, η_n/4 for each grid family.
Only the explicit logarithmic floors are compared when absorbing numerical
factors into the fixed calibration multipliers. The bias coefficient is the
closed number 64, obtained from variationalConst (1/4) = 16. The auxiliary
comparison constant is chosen separately and may be enlarged by consumers. -/
lemma rdiv_discrepancy_bound_uniform_at_versions
    (hLi_of_gate : LiLocalizedConcentration V)
    (hVector_of_gate : LipschitzVectorLocalizedConcentration V P sample split)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (hIV : RDIVSetting V mu g₀)
    : let publicG := rdivEvaluatedAccuracy rawG; -- @realizes \delta_{n,\mathcal G}(public density radius after component-budget evaluation)
      let publicH := rdivEvaluatedAccuracy rawH; -- @realizes \delta_{n,\mathcal H}(public hypothesis radius after component-budget evaluation)
      let publicR := rdivEvaluatedAccuracy rawR; -- @realizes \delta_{n,r}(public pilot accuracy after component-budget evaluation)
      ∃ required > 0, ∀ (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ),
      ∀ (β : ℝ) (w₀ : V.Hbar.toSubmodule)
      (δ ν : ℕ → ℝ),
      (hRange : RangeCondition V) →
      (hSource : BetaSourceCondition V β w₀) →
      (hRealizable : H0MemHypothesisClass V) →
      (hDensity : DensityRealizable V mu G g₀) →
      (hDensityBounds : DensityBounds G g₀ support c₀ CG) →
      (hPilotRate : PilotRegressionRate V P sample split rHat rawR) →
      (hOutcome : OutcomeBounded V B) →
      (hHypBound : HypothesisClassBounded V support B) →
      (hPilotBound : PilotBounded V P rHat pilotInputSupport B) →
      (hSupMeas : RDIVClassesMeasurable V P sample split mu G g₀ gHat) →
      (hLikMeas : RDIVLikelihoodProcessesMeasurable V G g₀) →
      (hFittingVersion : RDIVFittingSupremumVersion V P sample split mu gHat ρ) →
      (hSelectedDensityVersion : RDIVSelectedDensityVersion V P sample split mu gHat) →
      (hSelectedPilotVersion : RDIVSelectedPilotVersion V P sample split rHat) →
      (hDensityRadius : DensityCriticalRadiusBound V G g₀ rawG) →
      (hHypRadius : HypothesisCriticalRadiusBound V mu G rawH ρ) →
      (hRadiusFloor : RDIVRadiusFloor rawG rawH ρ) →
      (hScale : RDIVPublicScaleCalibration ρ ξ baseδ baseν publicG publicH publicR) →
      (hMinima : RDIVMinimaAttained V P sample split mu gHat ρ candidate) →
      (hInflation : CalibratedValidBounds δ ν baseδ baseν (κ₀ B c₀ CG Cm).1 (κ₀ B c₀ CG Cm).2 required) →
      (hDeterministic : CalibrationDeterministic δ ν) →
      (hMLE : MLEMaximizerSelected V P sample split G gHat) →
      ∃ C > 0, 64 ≤ C ∧ ∀ n : ℕ, 0 < n → ∃ E : Set Ω,
      MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧
      RDIVComparisonsOn V P sample split mu g₀ gHat rHat ρ ξ ν rawG rawH rawR candidate n E C ∧ RDIVDiscrepancyEnvelope V P sample split mu gHat rHat ρ β δ ν w₀ candidate n E 64 := by
  classical
  dsimp only
  -- Fix all sampling constants before introducing the source data.
  by_cases hSetup : RangeCondition V ∧ H0MemHypothesisClass V ∧
      DensityRealizable V mu G g₀ ∧ DensityBounds G g₀ support c₀ CG ∧
      PilotRegressionRate V P sample split rHat rawR ∧ OutcomeBounded V B ∧
      HypothesisClassBounded V support B ∧ PilotBounded V P rHat pilotInputSupport B ∧
      RDIVClassesMeasurable V P sample split mu G g₀ gHat ∧
      RDIVLikelihoodProcessesMeasurable V G g₀ ∧
      RDIVFittingSupremumVersion V P sample split mu gHat ρ ∧
      RDIVSelectedDensityVersion V P sample split mu gHat ∧
  RDIVSelectedPilotVersion V P sample split rHat ∧
      DensityCriticalRadiusBound V G g₀ rawG ∧ HypothesisCriticalRadiusBound V mu G rawH ρ ∧
      RDIVRadiusFloor rawG rawH ρ ∧
      RDIVScaleCalibration ρ ξ baseδ baseν rawG rawH rawR 1 ∧
      RDIVMinimaAttained V P sample split mu gHat ρ candidate ∧
      MLEMaximizerSelected V P sample split G gHat
  · obtain ⟨hr, hh, hd, hdb, hp, hy, hhb, hpb, hm, hlik, hversion, hselectedVersion, hpilotVersion, hdRad, hhRad, hf, hs, hmin, hMLE⟩ := hSetup
    obtain ⟨Ce, hCe, hevent⟩ := err_l_dp_local (hSelectedPilotVersion := hpilotVersion) (hLi_of_gate := hLi_of_gate) (hVector_of_gate := hVector_of_gate)
      (V := V) (P := P) (sample := sample) (split := split)
      (ρ := ρ) (ξ := ξ) (B := B) (δ := baseδ) (ν := baseν)
      (δG := rawG) (δH := rawH) (δr := rawR) (c₀ := c₀) (CG := CG)
      (mu := mu) (G := G) (g₀ := g₀) (gHat := gHat) (rHat := rHat)
      (support := support) (candidate := candidate)
      hρ hξ hIV hr hh hd hdb hp hy hhb hpb hm hlik hversion hselectedVersion
      hdRad hhRad hf hs hmin hMLE
    obtain ⟨Cl, hCl, hloss⟩ := err_r_dp
      (V := V) (P := P) (sample := sample) (split := split)
      (ρ := ρ) (ξ := ξ) (B := B) (δ := baseδ) (ν := baseν)
      (δG := rawG) (δH := rawH) (δr := rawR) (c₀ := c₀) (CG := CG)
      (mu := mu) (G := G) (g₀ := g₀) (gHat := gHat) (rHat := rHat)
      (support := support) (candidate := candidate)
      hρ hξ hIV hr hh hd hdb hp hy hhb hpb hm
      hdRad hhRad hf hs hmin hMLE Ce hCe
    let A := 2 * (Cl ^ 2 + 2 * Cl)
    let K := Ce ^ 2 + 2 * Ce
    let R := 2 * A + K + 1
    have hA : 0 < A := by dsimp [A]; positivity
    have hK : 0 < K := by dsimp [K]; positivity
    refine ⟨R, by dsimp [R]; positivity, ?_⟩
    intro κ₀
    let κδ := (κ₀ B c₀ CG Cm).1
    let κν := (κ₀ B c₀ CG Cm).2
    intro β w₀ δ ν hRange hSource hRealizable hDensity hDensityBounds
      hPilotRate hOutcome hHypBound hPilotBound hSupMeas hLikMeas hFittingVersion hSelectedDensityVersion hSelectedPilotVersion hDensityRadius hHypRadius
      hRadiusFloor hScale hMinima hInflation hDeterministic hMLE'
    obtain ⟨hCs, hsource⟩ := (variational_source_uniform V β w₀ hSource).2
      (1 / 4) (by norm_num)
    let Cs := variationalConst (1 / 4)
    have hCsValue : Cs = 16 := by norm_num [Cs, variationalConst]
    let C := Ce + 4 * Cs + 1
    have hC : 0 < C := by dsimp [C]; positivity
    have hCeC : Ce ≤ C := by dsimp [C]; linarith
    have hCsC : 4 * Cs ≤ (64 : ℝ) := by rw [hCsValue]; norm_num
    have h64C : (64 : ℝ) ≤ C := by dsimp [C]; rw [hCsValue]; linarith
    have hkδ := hInflation.1
    have hkν := hInflation.2.1
    have hAk : 2 * A ≤ κδ ^ 2 := by
      have hk := hInflation.2.2.1
      dsimp [R] at hk
      nlinarith only [hk, hkδ, hK]
    have hKk : K ≤ κν ^ 2 := by
      have hk := hInflation.2.2.2.1
      dsimp [R] at hk
      nlinarith only [hk, hkν, hA]
    refine ⟨C, hC, h64C, ?_⟩
    intro n hn
    obtain ⟨E, hE, hpE, hcomp, _⟩ := hevent n hn
    have hquarter : ξ / 4 ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hξ.1, hξ.2]
    have hG : 0 ≤ rawG n (ξ / 4) := (hdRad n hn _ hquarter).1.le
    have hH : 0 ≤ rawH n (gridConfidence ρ ξ n / 4) := by
      have hh := (hhRad n hn (ξ / 4) hquarter).1.1.le
      have he : gridConfidence ρ (ξ / 4) n = gridConfidence ρ ξ n / 4 := by
        unfold gridConfidence
        ring
      rwa [he] at hh
    have hr0 : 0 ≤ rawR n (ξ / 4) := (hp.2 n hn _ hquarter).1
    have hd0 : 0 ≤ baseδ n := by
      have hsum := (((rdivScaleCalibration_one_iff_public ρ ξ baseδ baseν
        rawG rawH rawR).mp hs).1 n hn).1
      change rawG n (ξ / 4) + rawH n (gridConfidence ρ ξ n / 4) +
        rdivPublicLogScale ρ ξ n ≤ baseδ n at hsum
      have hl : 0 ≤ rdivPublicLogScale ρ ξ n := Real.sqrt_nonneg _
      linarith only [hsum, hG, hH, hl]
    have hv0 := (rdiv_calibration_scale_domination ρ ξ Ce baseδ baseν rawG rawH rawR
      hs hCe.le n hn hG hr0).1
    have hv : baseν n ≤ ν n := by
      rw [hInflation.2.2.2.2.2 n]
      nlinarith only [hkν, hv0]
    have hv2 : baseν n ^ 2 ≤ ν n ^ 2 := pow_le_pow_left₀ hv0 hv 2
    have hnoiseFit : 2 * A * baseδ n ^ 2 ≤ δ n ^ 2 := by
      rw [hInflation.2.2.2.2.1 n]
      nlinarith only [mul_le_mul_of_nonneg_right hAk (sq_nonneg (baseδ n))]
    have hnoiseCal : K * baseν n ^ 2 ≤ ν n ^ 2 := by
      rw [hInflation.2.2.2.2.2 n]
      nlinarith only [mul_le_mul_of_nonneg_right hKk (sq_nonneg (baseν n))]
    have hcomp' : RDIVComparisonsOn V P sample split mu g₀ gHat rHat ρ ξ ν
        rawG rawH rawR candidate n E C := by
      intro ω hω
      obtain ⟨hpre, hfit, hcal⟩ := hcomp ω hω
      refine ⟨rdiv_preliminaryOn_mono V mu g₀ gHat rHat ξ Ce C rawG rawR n ω
        hG hCeC hpre, ?_, ?_⟩
      · intro lam hlam h hh
        exact (hfit lam hlam h hh).trans (mul_le_mul_of_nonneg_right hCeC
          (add_nonneg (mul_nonneg hH (norm_nonneg _)) (sq_nonneg _)))
      · intro lam hlam
        apply (hcal lam hlam).trans
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right
            ((mul_le_mul_of_nonneg_left hv hCe.le).trans
              (mul_le_mul_of_nonneg_right hCeC (hDeterministic.2 n))) (norm_nonneg _)
        · exact (mul_le_mul_of_nonneg_left hv2 hCe.le).trans
            (mul_le_mul_of_nonneg_right hCeC (sq_nonneg _))
    refine ⟨E, hE, hpE, hcomp', by norm_num, ?_⟩
    intro ω hω lam hlam
    have hdom : lam ∈ Set.Ioc (0 : ℝ) 2 := by
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hlam
      refine ⟨mul_pos (by norm_num) (pow_pos (by linarith [hρ.1]) _), ?_⟩
      have hpow : ρ ^ k ≤ 1 := pow_le_one₀ (by linarith [hρ.1]) hρ.2.le
      dsimp [gridValue]
      linarith
    have hlampos := hdom.1
    let h := candidate n lam ω
    let u := h - minNormSolution V
    let U := ‖u‖
    let W := ‖projCondExpOp V u‖ ^ 2
    have hh : h ∈ V.H := ((hmin n hn lam hlam).1 ω).1
    have hopt := ((hmin n hn lam hlam).1 ω).2 (minNormSolution V) hRealizable
    have herr := (abs_le.mp (hloss n hn E hE hpE hcomp ω hω h hh lam hlam)).2
    have hnorm : ‖h‖ ^ 2 - ‖minNormSolution V‖ ^ 2 =
        U ^ 2 + 2 * inner ℝ (minNormSolution V) u := by
      have heq : h = minNormSolution V + u := by dsimp [u]; abel
      conv_lhs => rw [heq, norm_add_sq_real]
      dsimp [U]
      ring
    have hpop : populationRisk V lam h - populationRisk V lam (minNormSolution V) =
        W + lam * (U ^ 2 + 2 * inner ℝ (minNormSolution V) u) := by
      rw [populationRisk, populationRisk,
        rdivPopulationLoss_eq V mu g₀ hIV hRange B hOutcome h,
        rdivPopulationLoss_eq V mu g₀ hIV hRange B hOutcome (minNormSolution V)]
      simp only [sub_self, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
      rw [show ‖projCondExpOp V (h - minNormSolution V)‖ ^ 2 = W from rfl]
      calc
        _ = W + lam * (‖h‖ ^ 2 - ‖minNormSolution V‖ ^ 2) := by ring
        _ = _ := by rw [hnorm]
    rw [hpop] at herr
    have hbasic : W + lam * U ^ 2 ≤ Cl * (baseδ n * U + baseδ n ^ 2) +
        2 * lam * |inner ℝ (minNormSolution V) u| := by
      have hi := mul_le_mul_of_nonneg_left (neg_abs_le (inner ℝ (minNormSolution V) u))
        (by positivity : 0 ≤ 2 * lam)
      change empiricalRisk V P sample split mu gHat n ω lam h ≤ _ at hopt
      change W + lam * (U ^ 2 + 2 * inner ℝ (minNormSolution V) u) - _ ≤
        Cl * (baseδ n * U + baseδ n ^ 2) at herr
      linarith only [herr, hopt, hi]
    have hYoung : Cl * baseδ n * U ≤ lam / 4 * U ^ 2 +
        Cl ^ 2 * (baseδ n ^ 2 / lam) := by
      apply (mul_le_mul_iff_left₀ hdom.1).mp
      have hc : lam * (baseδ n ^ 2 / lam) = baseδ n ^ 2 :=
        mul_div_cancel₀ _ hdom.1.ne'
      nlinarith only [sq_nonneg (lam * U - 2 * Cl * baseδ n), hc]
    have hn2 : baseδ n ^ 2 ≤ 2 * (baseδ n ^ 2 / lam) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hdom.1).2
      nlinarith only [mul_le_mul_of_nonneg_right hdom.2 (sq_nonneg (baseδ n))]
    have hsource' := (hsource u).1 lam hdom
    change 2 * lam * |inner ℝ (minNormSolution V) u| ≤
      (1 / 4 : ℝ) * (W + lam * U ^ 2) +
        Cs * ‖w₀‖ ^ 2 * lam ^ biasExponent β at hsource'
    have hW : W ≤ A * (baseδ n ^ 2 / lam) +
        2 * Cs * (‖w₀‖ ^ 2 * lam ^ biasExponent β) := by
      have hu : 0 ≤ lam * U ^ 2 := by positivity
      have hn' := mul_le_mul_of_nonneg_left hn2 hCl.le
      have hW0 : 0 ≤ W := sq_nonneg _
      have hb0 : 0 ≤ Cs * ‖w₀‖ ^ 2 * lam ^ biasExponent β := by positivity
      have hn0 : 0 ≤ (Cl ^ 2 + 2 * Cl) * (baseδ n ^ 2 / lam) := by positivity
      dsimp only [A]
      nlinarith only [hbasic, hYoung, hn', hsource', hu, hW0, hb0, hn0]
    have hcal := (abs_le.mp ((hcomp ω hω).2.2 lam hlam)).2
    have hcross : Ce * baseν n * ‖projCondExpOp V u‖ ≤
        W + Ce ^ 2 * baseν n ^ 2 := by
      dsimp only [W]
      nlinarith only [sq_nonneg (‖projCondExpOp V u‖ - Ce * baseν n)]
    have hD : rdivCalibrationStat V P sample split mu gHat rHat n ω h ≤
        2 * W + K * baseν n ^ 2 := by
      change rdivCalibrationStat V P sample split mu gHat rHat n ω h - W ≤
        Ce * baseν n * ‖projCondExpOp V u‖ + Ce * baseν n ^ 2 at hcal
      dsimp only [K]
      have he := mul_nonneg hCe.le (sq_nonneg (baseν n))
      nlinarith only [hcal, hcross, he]
    have hfit := div_le_div_of_nonneg_right hnoiseFit hdom.1.le
    rw [mul_div_assoc] at hfit
    have hbias := mul_le_mul_of_nonneg_right hCsC
      (show 0 ≤ ‖w₀‖ ^ 2 * lam ^ biasExponent β by positivity)
    change rdivCalibrationStat V P sample split mu gHat rHat n ω h ≤ _
    unfold rdivNoiseLevel
    nlinarith only [hD, hW, hfit, hnoiseCal, hbias]
  · refine ⟨1, zero_lt_one, ?_⟩
    intro κ₀
    let κδ := (κ₀ B c₀ CG Cm).1
    let κν := (κ₀ B c₀ CG Cm).2
    intro β w₀ δ ν hRange hSource hRealizable hDensity hDensityBounds
      hPilotRate hOutcome hHypBound hPilotBound hSupMeas hLikMeas hFittingVersion hSelectedDensityVersion hSelectedPilotVersion hDensityRadius hHypRadius
      hRadiusFloor hScale hMinima hInflation hDeterministic hMLE
    have hs := (rdivScaleCalibration_one_iff_public ρ ξ baseδ baseν rawG rawH rawR).mpr hScale
    exact (hSetup ⟨hRange, hRealizable, hDensity, hDensityBounds, hPilotRate, hOutcome,
      hHypBound, hPilotBound, hSupMeas, hLikMeas, hFittingVersion, hSelectedDensityVersion, hSelectedPilotVersion, hDensityRadius, hHypRadius, hRadiusFloor,
      hs, hMinima, hMLE⟩).elim


/-- Given [localized likelihood concentration](hyp:hLi_of_gate), [localized vector
concentration](hyp:hVector_of_gate), [a grid factor at least one-half and less than one](hyp:hρ), [a failure
level strictly between zero and one](hyp:hξ), and [a valid IV density model](hyp:hIV),
[there is a positive calibration threshold, uniform over inflation rules, source
exponents and witnesses, and accuracy curves, such that the range and source
conditions, solution and density realizability, density bounds, the pilot rate,
bounded outcomes, hypotheses and pilot, measurable fitting classes and likelihood
processes, valid fitting-supremum and selected density and pilot versions, density
and hypothesis critical-radius control with its floor, public scale calibration
using component-budget-evaluated accuracy curves, attained fitting minima,
sufficient inflation, deterministic accuracy curves, and likelihood-maximizing
density estimates imply the existence of one positive constant and, for every
positive sample size, a measurable event of probability at least one minus the
failure level carrying both the RDIV comparisons and discrepancy envelope with
that same constant](goal).

Compatibility projection using one enlarged constant for comparisons and bias.
The public envelope below keeps its closed bias coefficient separately. -/
lemma rdiv_discrepancy_bound_at_versions
    (hLi_of_gate : LiLocalizedConcentration V)
    (hVector_of_gate : LipschitzVectorLocalizedConcentration V P sample split)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (hIV : RDIVSetting V mu g₀)
    : let publicG := rdivEvaluatedAccuracy rawG; -- @realizes \delta_{n,\mathcal G}(public density radius after component-budget evaluation)
      let publicH := rdivEvaluatedAccuracy rawH; -- @realizes \delta_{n,\mathcal H}(public hypothesis radius after component-budget evaluation)
      let publicR := rdivEvaluatedAccuracy rawR; -- @realizes \delta_{n,r}(public pilot accuracy after component-budget evaluation)
      ∃ required > 0, ∀ (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ),
      ∀ (β : ℝ) (w₀ : V.Hbar.toSubmodule)
      (δ ν : ℕ → ℝ),
      (hRange : RangeCondition V) →
      (hSource : BetaSourceCondition V β w₀) →
      (hRealizable : H0MemHypothesisClass V) →
      (hDensity : DensityRealizable V mu G g₀) →
      (hDensityBounds : DensityBounds G g₀ support c₀ CG) →
      (hPilotRate : PilotRegressionRate V P sample split rHat rawR) →
      (hOutcome : OutcomeBounded V B) →
      (hHypBound : HypothesisClassBounded V support B) →
      (hPilotBound : PilotBounded V P rHat pilotInputSupport B) →
      (hSupMeas : RDIVClassesMeasurable V P sample split mu G g₀ gHat) →
      (hLikMeas : RDIVLikelihoodProcessesMeasurable V G g₀) →
      (hFittingVersion : RDIVFittingSupremumVersion V P sample split mu gHat ρ) →
      (hSelectedDensityVersion : RDIVSelectedDensityVersion V P sample split mu gHat) →
      (hSelectedPilotVersion : RDIVSelectedPilotVersion V P sample split rHat) →
      (hDensityRadius : DensityCriticalRadiusBound V G g₀ rawG) →
      (hHypRadius : HypothesisCriticalRadiusBound V mu G rawH ρ) →
      (hRadiusFloor : RDIVRadiusFloor rawG rawH ρ) →
      (hScale : RDIVPublicScaleCalibration ρ ξ baseδ baseν publicG publicH publicR) →
      (hMinima : RDIVMinimaAttained V P sample split mu gHat ρ candidate) →
      (hInflation : CalibratedValidBounds δ ν baseδ baseν (κ₀ B c₀ CG Cm).1 (κ₀ B c₀ CG Cm).2 required) →
      (hDeterministic : CalibrationDeterministic δ ν) →
      (hMLE : MLEMaximizerSelected V P sample split G gHat) →
      ∃ C > 0, ∀ n : ℕ, 0 < n → ∃ E : Set Ω,
      MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧
      RDIVComparisonsOn V P sample split mu g₀ gHat rHat ρ ξ ν rawG rawH rawR candidate n E C ∧ RDIVDiscrepancyEnvelope V P sample split mu gHat rHat ρ β δ ν w₀ candidate n E C := by
  obtain ⟨required, hrequired, hbound⟩ := rdiv_discrepancy_bound_uniform_at_versions
    (V := V) (P := P) (sample := sample) (split := split)
    (ρ := ρ) (ξ := ξ) (B := B) (baseδ := baseδ) (baseν := baseν)
    (rawG := rawG) (rawH := rawH) (rawR := rawR)
    (c₀ := c₀) (CG := CG) (Cm := Cm) (mu := mu) (G := G) (g₀ := g₀)
    (gHat := gHat) (rHat := rHat) (support := support) (candidate := candidate)
    hLi_of_gate hVector_of_gate hρ hξ hIV
  refine ⟨required, hrequired, ?_⟩
  intro κ₀ β w₀ δ ν hRange hSource hRealizable hDensity hDensityBounds
    hPilotRate hOutcome hHypBound hPilotBound hSupMeas hLikMeas hFittingVersion
    hSelectedDensityVersion hSelectedPilotVersion hDensityRadius hHypRadius
    hRadiusFloor hScale hMinima hInflation hDeterministic hMLE
  obtain ⟨C, hC, h64C, hevent⟩ := hbound κ₀ β w₀ δ ν hRange hSource hRealizable
    hDensity hDensityBounds hPilotRate hOutcome hHypBound hPilotBound hSupMeas
    hLikMeas hFittingVersion hSelectedDensityVersion hSelectedPilotVersion
    hDensityRadius hHypRadius hRadiusFloor hScale hMinima hInflation hDeterministic hMLE
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨E, hE, hpE, hcomp, henv⟩ := hevent n hn
  refine ⟨E, hE, hpE, hcomp, hC, ?_⟩
  intro ω hω lam hlam
  apply (henv.2 ω hω lam hlam).trans
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right h64C (sq_nonneg _)) (Real.rpow_nonneg (by
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hlam
      exact le_of_lt (mul_pos (by norm_num) (pow_pos (by linarith [hρ.1]) k))) _)



/-- Suppose [localized likelihood concentration holds](hyp:hLi_of_gate), [the
chosen hypothesis versions are measurable](hyp:hmeas) and [agree almost surely
with the population hypotheses](hyp:hcoherent), and [localized vector concentration
holds for those versions](hyp:hVector_of_gate). Then [for every grid factor at
least one-half and less than one, every failure level strictly between zero and
one, and every valid IV density model for these versions, there is a positive
calibration threshold, uniform over inflation rules, source exponents and
witnesses, and accuracy curves, such that the range and source conditions,
solution and density realizability, density bounds, the pilot rate, bounded
outcomes, chosen hypotheses and pilot, measurable fitting classes and likelihood
processes, valid fitting-supremum and selected density and pilot versions, density
and hypothesis critical-radius bounds with their floor, public scale calibration
using component-budget-evaluated accuracy curves, attained fitting minima for
these versions, sufficient inflation, deterministic accuracy curves, and
likelihood-maximizing density estimates imply the existence of a positive
comparison constant and, at every sample size meeting the RDIV minimum, a
measurable event of probability at least one minus the failure level carrying
the version-specific RDIV comparisons and the discrepancy envelope with bias
coefficient 64](goal).

Choose the bounded measurable function versions first and use them in
all fitting, calibration, penalty and recursive-center definitions. The
boundedness premise constrains these chosen functions, not the unrelated
representatives of the ambient L2 presentation. Selected minima are assumed
for these exact functions; none is transferred from another presentation. -/
-- @node: thm:rdiv-discrepancy-bound
theorem rdiv_discrepancy_bound
    (hLi_of_gate : LiLocalizedConcentration V)
    (versions : V.Hbar.toSubmodule → 𝒳 → ℝ)
    (hmeas : ∀ h, Measurable (versions h))
    (hcoherent : ∀ h, (fun w => versions h (V.xOf w)) =ᵐ[V.law]
      ((h : Lp ℝ 2 V.law) : 𝒲 → ℝ))
    (hVector_of_gate : LipschitzVectorLocalizedConcentration
      (rdivWithPrimalVersions V versions hmeas hcoherent) P sample split) :
    ∀ (_hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (_hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (_hIV : RDIVSetting (rdivWithPrimalVersions V versions hmeas hcoherent) mu g₀),
      let publicG := rdivEvaluatedAccuracy rawG; -- @realizes \delta_{n,\mathcal G}(public density radius after component-budget evaluation)
      let publicH := rdivEvaluatedAccuracy rawH; -- @realizes \delta_{n,\mathcal H}(public hypothesis radius after component-budget evaluation)
      let publicR := rdivEvaluatedAccuracy rawR; -- @realizes \delta_{n,r}(public pilot accuracy after component-budget evaluation)
      ∃ required > 0, ∀ (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ),
      ∀ (β : ℝ) (w₀ : (rdivWithPrimalVersions V versions hmeas hcoherent).Hbar.toSubmodule)
      (δ ν : ℕ → ℝ),
      (hRange : RangeCondition V) →
      (hSource : BetaSourceCondition (rdivWithPrimalVersions V versions hmeas hcoherent) β w₀) →
      (hRealizable : H0MemHypothesisClass V) →
      (hDensity : DensityRealizable (rdivWithPrimalVersions V versions hmeas hcoherent) mu G g₀) →
      (hDensityBounds : DensityBounds G g₀ support c₀ CG) →
      (hPilotRate : PilotRegressionRate (rdivWithPrimalVersions V versions hmeas hcoherent) P sample split rHat rawR) →
      (hOutcome : OutcomeBounded (rdivWithPrimalVersions V versions hmeas hcoherent) B) →
      (hHypBound : HypothesisClassBounded (rdivWithPrimalVersions V versions hmeas hcoherent) support B) →
      (hPilotBound : PilotBounded (rdivWithPrimalVersions V versions hmeas hcoherent) P rHat pilotInputSupport B) →
      (hSupMeas : RDIVClassesMeasurable (rdivWithPrimalVersions V versions hmeas hcoherent) P sample split mu G g₀ gHat) →
      (hLikMeas : RDIVLikelihoodProcessesMeasurable V G g₀) →
      (hFittingVersion : RDIVFittingSupremumVersion (rdivWithPrimalVersions V versions hmeas hcoherent) P sample split mu gHat ρ) →
      (hSelectedDensityVersion : RDIVSelectedDensityVersion (rdivWithPrimalVersions V versions hmeas hcoherent) P sample split mu gHat) →
      (hSelectedPilotVersion : RDIVSelectedPilotVersion (rdivWithPrimalVersions V versions hmeas hcoherent) P sample split rHat) →
      (hDensityRadius : DensityCriticalRadiusBound (rdivWithPrimalVersions V versions hmeas hcoherent) G g₀ rawG) →
      (hHypRadius : HypothesisCriticalRadiusBound (rdivWithPrimalVersions V versions hmeas hcoherent) mu G rawH ρ) →
      (hRadiusFloor : RDIVRadiusFloor rawG rawH ρ) →
      (hScale : RDIVPublicScaleCalibration ρ ξ baseδ baseν publicG publicH publicR) →
      (hMinima : RDIVMinimaAttained (rdivWithPrimalVersions V versions hmeas hcoherent) P sample split mu gHat ρ candidate) →
      (hInflation : CalibratedValidBounds δ ν baseδ baseν (κ₀ B c₀ CG Cm).1 (κ₀ B c₀ CG Cm).2 required) →
      (hDeterministic : CalibrationDeterministic δ ν) →
      (hMLE : MLEMaximizerSelected (rdivWithPrimalVersions V versions hmeas hcoherent) P sample split G gHat) →
      ∃ C > 0, ∀ n : ℕ, rdivMinSampleSize B ≤ n → ∃ E : Set Ω,
      MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧
      RDIVComparisonsOn (rdivWithPrimalVersions V versions hmeas hcoherent) P sample split mu g₀ gHat rHat ρ ξ ν rawG rawH rawR candidate n E C ∧ RDIVDiscrepancyEnvelope (rdivWithPrimalVersions V versions hmeas hcoherent) P sample split mu gHat rHat ρ β δ ν w₀ candidate n E 64 := by
  dsimp only
  intro hρ hξ hIV
  obtain ⟨required, hrequired, hbound⟩ := rdiv_discrepancy_bound_uniform_at_versions (hLi_of_gate := hLi_of_gate) (hVector_of_gate := hVector_of_gate)
    (V := rdivWithPrimalVersions V versions hmeas hcoherent)
    (P := P) (sample := sample) (split := split)
    (ρ := ρ) (ξ := ξ) (B := B) (baseδ := baseδ) (baseν := baseν)
    (rawG := rawG) (rawH := rawH) (rawR := rawR)
    (c₀ := c₀) (CG := CG) (Cm := Cm) (mu := mu) (G := G) (g₀ := g₀)
    (gHat := gHat) (rHat := rHat) (support := support) (candidate := candidate)
    hρ hξ hIV
  refine ⟨required, hrequired, ?_⟩
  intro κ₀ β w₀ δ ν hRange hSource hRealizable hDensity hDensityBounds
    hPilotRate hOutcome hHypBound hPilotBound hSupMeas hLikMeas hFittingVersion
    hSelectedDensityVersion hSelectedPilotVersion hDensityRadius hHypRadius
    hRadiusFloor hScale hMinima hInflation hDeterministic hMLE
  obtain ⟨C, hC, _h64C, hevent⟩ := hbound κ₀ β w₀ δ ν hRange hSource hRealizable
    hDensity hDensityBounds hPilotRate hOutcome hHypBound hPilotBound hSupMeas
    hLikMeas hFittingVersion hSelectedDensityVersion hSelectedPilotVersion
    hDensityRadius hHypRadius hRadiusFloor hScale hMinima hInflation hDeterministic hMLE
  refine ⟨C, hC, ?_⟩
  intro n hn
  exact hevent n (lt_of_lt_of_le (by norm_num : 0 < 2) ((le_max_left _ _).trans hn))

end Papers.TsAdaptiveEstimationInference
