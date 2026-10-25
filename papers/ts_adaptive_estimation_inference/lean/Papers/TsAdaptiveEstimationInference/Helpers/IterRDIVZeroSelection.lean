module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVRateComparisons
/-! Initial acceptance at the fixed penalty two when the population solution vanishes.
The same joint fitting and calibration construction is used without an oracle segment.
-/
public section
set_option linter.style.longLine false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory
variable {W X Z Ω : Type*} [MeasurableSpace W] [MeasurableSpace X]
  [MeasurableSpace Z] [MeasurableSpace Ω]

/-- Under [the range condition](hyp:hRange), if [the minimum-norm population
solution is zero](hyp:hz) and [the regularization penalty is positive](hyp:hlam),
[every deterministic population iterate is zero](goal). -/
-- @node: populationIterate_eq_zero_of_zero_solution
lemma populationIterate_eq_zero_of_zero_solution (V : IVWorld W X Z)
    (hRange : RangeCondition V) (hz : ZeroSolutionCase V)
    (lam : ℝ) (hlam : 0 < lam) (j : ℕ) : populationIterate V lam j = 0 := by
  have h := populationIterate_residual_identity V hRange lam hlam j
  change minNormSolution V = 0 at hz
  simpa only [hz, map_zero, zero_sub, neg_eq_zero] using h

/-- Assume [fixed-center concentration](hyp:hFix), [squared-loss
concentration](hyp:hSq), [Li concentration](hyp:hLi), [the RDIV model
conditions](hyp:hIV), [the range condition](hyp:hRange), [the minimum-norm
solution belongs to the hypothesis class](hyp:hRealizable), [density
realizability](hyp:hDensity), [the density bounds](hyp:hBounds), [bounded
outcomes](hyp:hY), and [a bounded hypothesis class](hyp:hHyp). With [an
admissible grid ratio](hyp:hρ), [a failure budget strictly between zero and
one](hyp:hξ), [a noise multiplier at least one](hyp:ha), and [a positive
iteration horizon](hyp:ht), suppose [the selected pilot has the regression
rate](hyp:hPilot), [the selected density maximizes likelihood](hyp:hMLE), [the
RDIV class processes are measurable](hyp:hMeas), [the likelihood processes are
measurable](hyp:hLik), [the selected density has the required
representative](hyp:hDV), [the selected pilot has the required
representative](hyp:hPV), [the pilot is bounded on its input support](hyp:hPilotBound),
[fixed-center suprema have the required versions](hyp:hVersion), [the density
critical-radius bounds hold](hyp:hG), [the hypothesis critical-radius bounds
hold](hyp:hH), [the radius floor holds](hyp:hFloor), and [the base scales are
calibrated](hyp:hScale). [There is an inflation threshold at least one such
that any sufficiently inflated deterministic accuracy bounds and attained
iterative minima yield, at every positive sample size, a measurable event of
probability at least one minus the failure budget on which, when the population
solution is zero, the terminal estimator at penalty two has calibration
statistic at most three halves of the iterative noise level](goal). -/
-- @node: iter_rdiv_zero_initial_acceptance_event
lemma iter_rdiv_zero_initial_acceptance_event
    {pilotInputSupport : Set Z} (V : IVWorld W X Z)
    (hFix : IterRDIVFixedCenterLocalizedConcentration (Ω := Ω) V)
    (hSq : IterRDIVSquaredLossLocalizedConcentration (Ω := Ω) V)
    (hLi : LiLocalizedConcentration V)
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG ρ ξ a : ℝ) (t : ℕ)
    (hIV : RDIVSetting V mu g₀) (hRange : RangeCondition V)
    (hRealizable : H0MemHypothesisClass V)
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
    ∃ required ≥ (1 : ℝ), ∀ (κδ κν : ℝ) (δ ν : ℕ → ℝ),
      CalibratedValidBounds δ ν baseδ baseν κδ κν required →
      CalibrationDeterministic δ ν →
      ∀ (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule),
      IterRDIVMinimaAttained V P sample split mu gHat ρ t iter →
      ∀ n, 0 < n → ∃ E : Set Ω, MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧
        ∀ ω ∈ E, ZeroSolutionCase V →
          rdivCalibrationStat V P sample split mu gHat rHat n ω (iter n t 2 ω) ≤
            (3 / 2 : ℝ) * iterRdivNoiseLevel a (δ n) (ν n) 2 := by
  classical
  by_cases hz : ZeroSolutionCase V
  · obtain ⟨D, hD, Ccal, hCcal, hevent⟩ := iter_rdiv_joint_stability_calibration_event
      (pilotInputSupport := pilotInputSupport) V hFix hSq hLi mu G g₀ support B c₀ CG
      hIV hRange hDensity hBounds hY hHyp
    obtain ⟨R, hR, hevent⟩ := hevent P inferInstance sample split gHat rHat ρ
      rawG rawH rawR hPilot hMLE hMeas hLik hDV hPV hPilotBound hVersion hG hH hFloor
    have hA := (iterRdivStabilityCoefficients_bounds D hD).2.2 t ht
    obtain ⟨L, hL, hAL, hCL, hCLsq⟩ := iter_rdiv_rate_rescaling
      (iterRdivStabilityCoefficients D t) Ccal hA hCcal
    have hLpos : 0 < L := zero_lt_one.trans_le hL
    refine ⟨L * R, one_le_mul_of_one_le_of_one_le hL hR, ?_⟩
    intro κδ κν δ ν hInflation hNonneg iter hMinima n hn
    have hκδ : R ≤ κδ / L := (le_div_iff₀ hLpos).2 (by
      nlinarith only [hInflation.2.2.1])
    have hκν : R ≤ κν / L := (le_div_iff₀ hLpos).2 (by
      nlinarith only [hInflation.2.2.2.1])
    have hscaled : CalibratedValidBounds (fun n => δ n / L) (fun n => ν n / L)
        baseδ baseν (κδ / L) (κν / L) R := by
      refine ⟨hR.trans hκδ, hR.trans hκν, hκδ, hκν, ?_, ?_⟩
      · intro n; dsimp only; rw [hInflation.2.2.2.2.1 n]; ring
      · intro n; dsimp only; rw [hInflation.2.2.2.2.2 n]; ring
    have hgrid : (2 : ℝ) ∈ regGrid ρ n := Finset.mem_image.mpr
      ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _), by simp [gridValue]⟩
    have hstar (lam : ℝ) (_hl : lam ∈ regGrid ρ n) (hs : lam ∈ ({2} : Set ℝ))
        (j : ℕ) (_hj : 1 ≤ j) (_hjt : j ≤ t) : populationIterate V lam j ∈ V.H := by
      have hl : lam = 2 := Set.mem_singleton_iff.mp hs
      rw [hl, populationIterate_eq_zero_of_zero_solution V hRange hz 2 (by norm_num) j]
      simpa only [H0MemHypothesisClass, show minNormSolution V = 0 from hz] using hRealizable
    obtain ⟨E, hE, hpE, hfit, hcal⟩ := hevent ξ t (fun n => δ n / L)
      (fun n => ν n / L) baseδ baseν (κδ / L) (κν / L) hρ hξ hScale hscaled
      n {2} 2 ⟨by
        apply (terminalGrid_le ρ hρ n hn).trans
        have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
        exact (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)).2 (by nlinarith),
        fun lam _ hs => by
          have he : lam = 2 := Set.mem_singleton_iff.mp hs
          rw [he]
          exact (oraclePoint_radius_bounds ρ 2 n hρ (by norm_num) (by
            apply (terminalGrid_le ρ hρ n hn).trans
            have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
            exact (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)).2 (by nlinarith))).2.2⟩
      (fun j lam => iter n j lam) hn
      (fun lam _ hs => by have := Set.mem_singleton_iff.mp hs; subst lam; norm_num)
      hstar (fun lam hl _ => (hMinima n hn lam hl).1)
      (fun lam hl ω => ((hMinima n hn lam hl).1.2 t ht le_rfl ω).1)
      (fun lam hl => (hMinima n hn lam hl).2 t le_rfl)
    refine ⟨E, hE, hpE, ?_⟩
    intro ω hω _
    have henergy := (hfit ω hω 2 hgrid (by simp) t ht le_rfl).1
    rw [populationIterate_eq_zero_of_zero_solution V hRange hz 2 (by norm_num) t,
      sub_zero] at henergy
    have hcal' := (abs_le.mp (hcal ω hω 2 hgrid)).2
    change minNormSolution V = 0 at hz
    rw [hz, sub_zero] at hcal'
    let U := ‖projCondExpOp V (iter n t 2 ω)‖
    have hnum : iterRdivStabilityCoefficients D t * (δ n / L) ^ 2 ≤ δ n ^ 2 / 16 := by
      have hm := mul_le_mul_of_nonneg_right hAL (sq_nonneg (δ n))
      calc
        _ = (iterRdivStabilityCoefficients D t / L ^ 2) * δ n ^ 2 := by ring
        _ ≤ (1 / 16 : ℝ) * δ n ^ 2 := hm
        _ = _ := by ring
    have hweak : U ^ 2 ≤ δ n ^ 2 / 32 := by
      dsimp only [U]
      nlinarith only [henergy, hnum, sq_nonneg ‖iter n t 2 ω‖]
    have hcalnum : Ccal * (ν n / L) * U + Ccal * (ν n / L) ^ 2 ≤
        ν n / 16 * U + ν n ^ 2 / 16 := by
      have h1 := mul_le_mul_of_nonneg_right hCL
        (mul_nonneg (hNonneg.2 n) (norm_nonneg (projCondExpOp V (iter n t 2 ω))))
      have h2 := mul_le_mul_of_nonneg_right hCLsq (sq_nonneg (ν n))
      convert add_le_add h1 h2 using 1 <;> (first | rfl | ring)
    have hy : 0 ≤ (U - ν n / 16) ^ 2 := sq_nonneg _
    have haδ := mul_le_mul_of_nonneg_right ha (sq_nonneg (δ n))
    dsimp only [iterRdivNoiseLevel, iterRdivScale]
    change _ - U ^ 2 ≤ _ at hcal'
    nlinarith only [hcal', hcalnum, hweak, hy, haδ, sq_nonneg (δ n), sq_nonneg (ν n)]
  · refine ⟨1, le_rfl, ?_⟩
    intro κδ κν δ ν _ _ iter _ n _
    refine ⟨Set.univ, MeasurableSet.univ, ?_, ?_⟩
    · simp only [probReal_univ]; linarith only [hξ.1]
    · intro ω _ hzero; exact (hz hzero).elim

end Papers.TsAdaptiveEstimationInference
