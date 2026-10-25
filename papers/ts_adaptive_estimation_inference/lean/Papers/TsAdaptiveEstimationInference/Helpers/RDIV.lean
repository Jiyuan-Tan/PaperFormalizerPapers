module
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVSetup
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVPerturbation
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVPreliminaryEvent
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVMoments
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVOperatorBridge
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVAccepted
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVPreliminaryRateEvent
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVLossBridge
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVFittingLocal
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVCalibrationFitted
/-! Helpers — RDIV for adaptive inverse problems.

Here δG, δH and δr denote raw confidence-parametric curves. Every hScale uses
the raw-instantiation wrapper RDIVScaleCalibration at horizon one, equivalent to
the public premise RDIVPublicScaleCalibration at rdivEvaluatedAccuracy δG/δH/δr
(rdivScaleCalibration_one_iff_public). Its logarithmic floor is fixed by
rdivPublicLogScale; the component-budget floor is handled by calibrated inflation.
Thus the displayed raw evaluations at ξ/4 and gridConfidence ρ ξ n/4 are exactly
the public calibrated quantities used by the main results. Conditioning on the
preliminary data, thawing, and fitting/calibration grid unions are local proof
obligations of err_l_dp; they are not new inputs to the cited carrier. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.tacticAnalysis.introMerge false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter
open scoped Topology
variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]
  {pilotInputSupport : Set 𝒵}
  (V : IVWorld 𝒲 𝒳 𝒵) (P : Measure Ω) [IsProbabilityMeasure P]
  (sample : AnalysisSample V P) (split : SampleSplit)
variable (ρ ξ B β : ℝ) (w₀ : V.Hbar.toSubmodule)
  (δ ν baseδ baseν : ℕ → ℝ) (δG δH δr tildeδ : ℕ → ℝ → ℝ)
  (κδ κν required c₀ CG Cm : ℝ) (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ)
  (mu : Measure 𝒳) (G : Set (𝒳 → 𝒵 → ℝ)) (g₀ : 𝒳 → 𝒵 → ℝ)
  (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (rHat : ℕ → Ω → 𝒵 → ℝ)
  (support : Set (𝒳 × 𝒵)) (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
  (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule)
  (a b c : ℝ) (t : ℕ)
/-- For [a failure budget strictly between zero and one](hyp:hξ), suppose
[the density event](hyp:hd), [pilot event](hyp:hp), [fitting event](hyp:hf), and
[calibration event](hyp:hc) are measurable and have probability at least one minus
a quarter of the budget [for density](hyp:hpd), [for the pilot](hyp:hpp),
[for fitting](hyp:hpf), and [for calibration](hyp:hpc).
[Their intersection has probability at least one minus the full budget](goal). -/
-- @node: rdivCommonEventBudget
lemma rdivCommonEventBudget (ξ : ℝ) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (density pilot fitting calibration : Set Ω)
    (hd : MeasurableSet density) (hp : MeasurableSet pilot)
    (hf : MeasurableSet fitting) (hc : MeasurableSet calibration)
    (hpd : 1 - ξ / 4 ≤ P.real density) (hpp : 1 - ξ / 4 ≤ P.real pilot)
    (hpf : 1 - ξ / 4 ≤ P.real fitting) (hpc : 1 - ξ / 4 ≤ P.real calibration) :
    1 - ξ ≤ P.real (density ∩ pilot ∩ fitting ∩ calibration) := by
  have hbad : P.real (density ∩ pilot ∩ fitting ∩ calibration)ᶜ ≤ ξ := by
    rw [Set.compl_inter, Set.compl_inter, Set.compl_inter]
    have h₁ := measureReal_union_le (μ := P) densityᶜ pilotᶜ
    have h₂ := measureReal_union_le (μ := P) (densityᶜ ∪ pilotᶜ) fittingᶜ
    have h₃ := measureReal_union_le (μ := P) (densityᶜ ∪ pilotᶜ ∪ fittingᶜ) calibrationᶜ
    linarith [probReal_add_probReal_compl (μ := P) hd,
      probReal_add_probReal_compl (μ := P) hp,
      probReal_add_probReal_compl (μ := P) hf,
      probReal_add_probReal_compl (μ := P) hc]
  linarith [probReal_add_probReal_compl (μ := P) (((hd.inter hp).inter hf).inter hc)]

/-- Assume [localized likelihood concentration](hyp:hLi_of_gate),
[a grid ratio in $[1/2,1)$](hyp:hρ), [a failure budget strictly between zero and one](hyp:hξ),
[the RDIV model](hyp:hIV), [density realizability](hyp:hDensity),
[the density bounds on its support](hyp:hDensityBounds), [the pilot regression rate](hyp:hPilotRate),
[bounded outcomes](hyp:hOutcome), [bounded hypotheses](hyp:hHypBound),
[a bounded pilot](hyp:hPilotBound), [measurable class suprema](hyp:hSupMeas),
[measurable likelihood processes](hyp:hLikMeas), [the fitting supremum version](hyp:hFittingVersion),
[the selected density version](hyp:hSelectedDensityVersion), [the selected pilot version](hyp:hSelectedPilotVersion),
[density critical-radius control](hyp:hDensityRadius), [hypothesis critical-radius control](hyp:hHypRadius),
[the radius floor](hyp:hRadiusFloor), and [selection of a likelihood maximizer](hyp:hMLE).
[One positive constant gives, for every positive sample size, a measurable event
of probability at least one minus the budget on which integrated squared Hellinger
error is bounded by the squared half-budget density radius, pilot error by its
half-budget radius, and operator error, relative operator error, and conditional-to-population
loss increments by the half-budget density radius with the stated norm factors](goal). -/
-- @node: lem:t-err-dp
lemma t_err_dp
    (hLi_of_gate : LiLocalizedConcentration V)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (hIV : RDIVSetting V mu g₀)
    (hDensity : DensityRealizable V mu G g₀)
    (hDensityBounds : DensityBounds G g₀ support c₀ CG)
    (hPilotRate : PilotRegressionRate V P sample split rHat δr)
    (hOutcome : OutcomeBounded V B)
    (hHypBound : HypothesisClassBounded V support B)
    (hPilotBound : PilotBounded V P rHat pilotInputSupport B)
    (hSupMeas : RDIVClassesMeasurable V P sample split mu G g₀ gHat)
    (hLikMeas : RDIVLikelihoodProcessesMeasurable V G g₀)
    (hFittingVersion : RDIVFittingSupremumVersion V P sample split mu gHat ρ)
    (hSelectedDensityVersion : RDIVSelectedDensityVersion V P sample split mu gHat)
    (hSelectedPilotVersion : RDIVSelectedPilotVersion V P sample split rHat)
    (hDensityRadius : DensityCriticalRadiusBound V G g₀ δG)
    (hHypRadius : HypothesisCriticalRadiusBound V mu G δH ρ)
    (hRadiusFloor : RDIVRadiusFloor δG δH ρ)
    (hMLE : MLEMaximizerSelected V P sample split G gHat)
    : ∃ C > 0, ∀ n : ℕ, 0 < n → ∃ E : Set Ω,
      MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧ ∀ ω ∈ E,
      (∫ z, hellingerSqDensity mu (fun x => gHat n ω x z) (fun x => g₀ x z)
        ∂V.law.map V.zOf) ≤ C * δG n (ξ / 2) ^ 2 ∧
      inputL2Norm (V.law.map V.zOf) (rHat n ω - dualVersion V (momentRepresenter V)) ≤ δr n (ξ / 2) ∧
      (∀ h ∈ V.H, inputL2Norm (V.law.map V.zOf)
        (estimatedOperator V mu gHat n ω h - dualVersion V (projCondExpOp V h)) ≤ C * δG n (ξ / 2)) ∧
      (∀ h ∈ V.H, ∀ h' ∈ V.H,
        inputL1Norm (V.law.map V.zOf)
          (estimatedOperator V mu gHat n ω (h - h') - dualVersion V (projCondExpOp V (h - h'))) ≤
          C * δG n (ξ / 2) * ‖h - h'‖) ∧
      ∀ h ∈ V.H, ∀ h' ∈ V.H,
        |(conditionalPopulationLoss V mu gHat n ω h - conditionalPopulationLoss V mu gHat n ω h') -
          (rdivPopulationLoss V h - rdivPopulationLoss V h')| ≤ C * δG n (ξ / 2) * ‖h - h'‖ := by
  obtain ⟨Cd, hCd, hdensity⟩ := rdiv_density_half_confidence_event (hLi_of_gate := hLi_of_gate) V P sample split
    mu G g₀ gHat support c₀ CG δG δH ρ ξ hIV hDensity
    hDensityBounds hSelectedDensityVersion hMLE hSupMeas hLikMeas hDensityRadius hRadiusFloor hξ
  let Cg := 2 * B * Real.sqrt Cd
  let Cr := Real.sqrt (2 * (CG / c₀ + 1)) * Real.sqrt Cd
  let Cl := 4 * B * Cr + 2 * Cg
  let C := Cd + Cg + Cr + Cl + 1
  have hB := hOutcome.1
  have hCg : 0 ≤ Cg := by dsimp [Cg]; positivity
  have hCr : 0 ≤ Cr := by dsimp [Cr]; positivity
  have hCl : 0 ≤ Cl := by dsimp [Cl]; positivity
  have hdC : Cd ≤ C := by dsimp [C]; linarith
  have hgC : Cg ≤ C := by dsimp [C]; linarith
  have hrC : Cr ≤ C := by dsimp [C]; linarith
  have hlC : Cl ≤ C := by dsimp [C]; linarith
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro n hn
  obtain ⟨D, hD, hpD, hlocal⟩ := hdensity n hn
  obtain ⟨E, hE, hpE, hpre⟩ := rdiv_preliminary_event_of_density_event V P sample split
    rHat δr hPilotRate ξ hξ n hn D hD hpD
  refine ⟨E, hE, hpE, ?_⟩
  intro ω hω
  obtain ⟨hωD, hpilot⟩ := hpre ω hω
  obtain ⟨hg, hrate⟩ := hlocal ω hωD
  have hhalf : ξ / 2 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hξ.1, hξ.2]
  have hδ : 0 ≤ δG n (ξ / 2) := (hDensityRadius n hn (ξ / 2) hhalf).1.le
  refine ⟨hrate.trans (mul_le_mul_of_nonneg_right hdC (sq_nonneg _)), hpilot, ?_, ?_, ?_⟩
  · intro h hh
    exact (rdiv_estimated_operator_global_rate V mu G g₀ gHat support B c₀ CG Cd
      (δG n (ξ / 2)) n ω hIV hDensity hDensityBounds hHypBound hB hg hCd.le hδ hrate h hh).trans
      (mul_le_mul_of_nonneg_right hgC hδ)
  · intro h hh h' hh'
    exact (rdiv_estimated_operator_relative_rate V mu G g₀ gHat support c₀ CG Cd
      (δG n (ξ / 2)) n ω hIV hDensity hDensityBounds hg hCd.le hδ hrate (h - h')).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hrC hδ) (norm_nonneg _))
  · intro h hh h' hh'
    exact (rdiv_conditional_population_loss_rate V mu G g₀ gHat support B c₀ CG Cd
      (δG n (ξ / 2)) n ω hIV hDensity hDensityBounds hHypBound hOutcome hg hCd.le hδ hrate
      h hh h' hh').trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlC hδ) (norm_nonneg _))

/-- Suppose [the preliminary constant](hyp:hCpre), [fitting constant](hyp:hCfit),
and [calibration constant](hyp:hCcal) are positive, [the failure budget lies strictly
between zero and one](hyp:hξ), and [the quarter-budget density radius](hyp:hG),
[the quarter-grid-budget hypothesis radius](hyp:hH), and [the calibration scale](hyp:hν)
are nonnegative. If [the preliminary event](hyp:hD), [fitting event](hyp:hF), and
[calibration event](hyp:hK) are measurable, spend [at most half the budget](hyp:hpD),
[at most a quarter for fitting](hyp:hpF), and [at most a quarter for calibration](hyp:hpK),
and satisfy [the preliminary comparisons](hyp:hpre), [the conditional-to-empirical
risk increment bounds over the grid](hyp:hfit), and [the projected calibration
comparison on the preliminary-calibration intersection](hyp:hcal),
[their intersection is measurable, has probability at least one minus the full
budget, and satisfies the joint RDIV comparisons with the sum of the three constants](goal). -/
-- @node: rdiv_comparison_event_assembly
lemma rdiv_comparison_event_assembly
    (Cpre Cfit Ccal : ℝ) (hCpre : 0 < Cpre) (hCfit : 0 < Cfit) (hCcal : 0 < Ccal)
    (n : ℕ) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (hG : 0 ≤ δG n (ξ / 4)) (hH : 0 ≤ δH n (gridConfidence ρ ξ n / 4))
    (hν : 0 ≤ ν n) (D F K : Set Ω)
    (hD : MeasurableSet D) (hF : MeasurableSet F) (hK : MeasurableSet K)
    (hpD : 1 - ξ / 2 ≤ P.real D) (hpF : 1 - ξ / 4 ≤ P.real F)
    (hpK : 1 - ξ / 4 ≤ P.real K)
    (hpre : ∀ ω ∈ D, RDIVPreliminaryOn V mu g₀ gHat rHat ξ δG δr n ω Cpre)
    (hfit : ∀ ω ∈ F, ∀ lam ∈ regGrid ρ n, ∀ h ∈ V.H,
      |(conditionalRisk V mu gHat n ω lam h - conditionalRisk V mu gHat n ω lam (minNormSolution V)) -
        (empiricalRisk V P sample split mu gHat n ω lam h -
          empiricalRisk V P sample split mu gHat n ω lam (minNormSolution V))| ≤
        Cfit * (δH n (gridConfidence ρ ξ n / 4) * ‖h - minNormSolution V‖ +
          δH n (gridConfidence ρ ξ n / 4) ^ 2))
    (hcal : ∀ ω ∈ D, ω ∈ K → ∀ lam ∈ regGrid ρ n,
      |rdivCalibrationStat V P sample split mu gHat rHat n ω (candidate n lam ω) -
        ‖projCondExpOp V (candidate n lam ω - minNormSolution V)‖ ^ 2| ≤
        Ccal * ν n * ‖projCondExpOp V (candidate n lam ω - minNormSolution V)‖ +
          Ccal * ν n ^ 2) :
    MeasurableSet (D ∩ F ∩ K) ∧ 1 - ξ ≤ P.real (D ∩ F ∩ K) ∧
      RDIVComparisonsOn V P sample split mu g₀ gHat rHat ρ ξ ν δG δH δr candidate
        n (D ∩ F ∩ K) (Cpre + Cfit + Ccal) := by
  refine ⟨(hD.inter hF).inter hK, ?_, ?_⟩
  · have hbad : P.real (D ∩ F ∩ K)ᶜ ≤ ξ := by
      rw [Set.compl_inter, Set.compl_inter]
      have h₁ := measureReal_union_le (μ := P) Dᶜ Fᶜ
      have h₂ := measureReal_union_le (μ := P) (Dᶜ ∪ Fᶜ) Kᶜ
      linarith [probReal_add_probReal_compl (μ := P) hD,
        probReal_add_probReal_compl (μ := P) hF,
        probReal_add_probReal_compl (μ := P) hK]
    linarith [probReal_add_probReal_compl (μ := P) ((hD.inter hF).inter hK)]
  intro ω hω
  have hp : Cpre ≤ Cpre + Cfit + Ccal := by linarith
  have hf : Cfit ≤ Cpre + Cfit + Ccal := by linarith
  have hc : Ccal ≤ Cpre + Cfit + Ccal := by linarith
  refine ⟨rdiv_preliminaryOn_mono V mu g₀ gHat rHat ξ Cpre (Cpre + Cfit + Ccal)
    δG δr n ω hG hp (hpre ω hω.1.1), ?_, ?_⟩
  · intro lam hlam h hh
    exact (hfit ω hω.1.2 lam hlam h hh).trans
      (mul_le_mul_of_nonneg_right hf
        (add_nonneg (mul_nonneg hH (norm_nonneg _)) (sq_nonneg _)))
  · intro lam hlam
    exact (hcal ω hω.1.1 hω.2 lam hlam).trans (add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hν) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right hc (sq_nonneg _)))

/-- Under [localized likelihood concentration](hyp:hLi_of_gate), [the RDIV model](hyp:hIV),
[density realizability](hyp:hDensity), [support-wise density bounds](hyp:hBounds),
[the selected density version](hyp:hSelectedDensityVersion), [selection of a likelihood maximizer](hyp:hMLE),
[measurable class suprema](hyp:hMeas), [measurable likelihood processes](hyp:hLikMeas),
[density critical-radius control](hyp:hRadius), [the radius floor](hyp:hFloor), and
[a failure budget strictly between zero and one](hyp:hξ), [one positive constant
gives a measurable event at every positive sample size with failure probability at
most half the budget, on which the selected density belongs to its model class and
its integrated squared Hellinger error is bounded by that constant times the squared
half-budget density radius](goal). -/
lemma rdiv_density_event_local
    (hLi_of_gate : LiLocalizedConcentration V)
    (mu : Measure 𝒳) (G : Set (𝒳 → 𝒵 → ℝ)) (g₀ : 𝒳 → 𝒵 → ℝ)
    (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (support : Set (𝒳 × 𝒵)) (c₀ CG : ℝ)
    (δG δH : ℕ → ℝ → ℝ) (ρ ξ : ℝ)
    (hIV : RDIVSetting V mu g₀) (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hSelectedDensityVersion : RDIVSelectedDensityVersion V P sample split mu gHat)
    (hMLE : MLEMaximizerSelected V P sample split G gHat)
    (hMeas : RDIVClassesMeasurable V P sample split mu G g₀ gHat)
    (hLikMeas : RDIVLikelihoodProcessesMeasurable V G g₀)
    (hRadius : DensityCriticalRadiusBound V G g₀ δG)
    (hFloor : RDIVRadiusFloor δG δH ρ) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C > 0, ∀ n : ℕ, 0 < n → ∃ E : Set Ω,
      MeasurableSet E ∧ 1 - ξ / 2 ≤ P.real E ∧ ∀ ω ∈ E,
        gHat n ω ∈ G ∧ (∫ z,
          hellingerSqDensity mu (fun x => gHat n ω x z) (fun x => g₀ x z)
            ∂V.law.map V.zOf) ≤ C * δG n (ξ / 2) ^ 2 := by
  exact rdiv_density_half_confidence_event (hLi_of_gate := hLi_of_gate) V P sample split
    mu G g₀ gHat support c₀ CG δG δH ρ ξ hIV hDensity
    hBounds hSelectedDensityVersion hMLE hMeas hLikMeas hRadius hFloor hξ

/-- Assuming [localized likelihood concentration](hyp:hLi_of_gate), [the RDIV model](hyp:hIV),
[density realizability](hyp:hDensity), [support-wise density bounds](hyp:hBounds),
[the pilot regression rate](hyp:hPilot), [bounded outcomes](hyp:hOutcome),
[bounded hypotheses](hyp:hHyp), [the selected density version](hyp:hSelectedDensityVersion),
[selection of a likelihood maximizer](hyp:hMLE), [measurable class suprema](hyp:hMeas),
[measurable likelihood processes](hyp:hLikMeas), [density critical-radius control](hyp:hRadius),
[the radius floor](hyp:hFloor), and [a failure budget strictly between zero and one](hyp:hξ),
[one positive constant gives, at every positive sample size, a measurable event with
failure probability at most half the budget on which the selected density belongs
to its model class and all preliminary density, pilot, operator and loss comparisons hold](goal). -/
lemma rdiv_preliminary_event_local
    (hLi_of_gate : LiLocalizedConcentration V)
    (mu : Measure 𝒳) (G : Set (𝒳 → 𝒵 → ℝ)) (g₀ : 𝒳 → 𝒵 → ℝ)
    (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (rHat : ℕ → Ω → 𝒵 → ℝ)
    (support : Set (𝒳 × 𝒵)) (B c₀ CG ρ ξ : ℝ)
    (δG δH δr : ℕ → ℝ → ℝ)
    (hIV : RDIVSetting V mu g₀) (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hPilot : PilotRegressionRate V P sample split rHat δr)
    (hOutcome : OutcomeBounded V B) (hHyp : HypothesisClassBounded V support B)
    (hSelectedDensityVersion : RDIVSelectedDensityVersion V P sample split mu gHat)
    (hMLE : MLEMaximizerSelected V P sample split G gHat)
    (hMeas : RDIVClassesMeasurable V P sample split mu G g₀ gHat)
    (hLikMeas : RDIVLikelihoodProcessesMeasurable V G g₀)
    (hRadius : DensityCriticalRadiusBound V G g₀ δG)
    (hFloor : RDIVRadiusFloor δG δH ρ) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C > 0, ∀ n : ℕ, 0 < n → ∃ E : Set Ω,
      MeasurableSet E ∧ 1 - ξ / 2 ≤ P.real E ∧ ∀ ω ∈ E,
        gHat n ω ∈ G ∧ RDIVPreliminaryOn V mu g₀ gHat rHat ξ δG δr n ω C := by
  have hhalf : ξ / 2 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hξ.1, hξ.2]
  have hquarter : ξ / 4 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hξ.1, hξ.2]
  obtain ⟨Cd, hCd, hdensity⟩ := rdiv_density_event_local (hLi_of_gate := hLi_of_gate) V P sample split
    mu G g₀ gHat support c₀ CG δG δH ρ (ξ / 2) hIV hDensity
    hBounds hSelectedDensityVersion hMLE hMeas hLikMeas hRadius hFloor hhalf
  have heq : ξ / 2 / 2 = ξ / 4 := by ring
  simp only [heq] at hdensity
  let Cg := 2 * B * Real.sqrt Cd
  let Cr := Real.sqrt (2 * (CG / c₀ + 1)) * Real.sqrt Cd
  let Cl := 4 * B * Cr + 2 * Cg
  let C := Cd + Cg + Cr + Cl + 1
  have hB := hOutcome.1
  have hCg : 0 ≤ Cg := by dsimp [Cg]; positivity
  have hCr : 0 ≤ Cr := by dsimp [Cr]; positivity
  have hCl : 0 ≤ Cl := by dsimp [Cl]; positivity
  have hdC : Cd ≤ C := by dsimp [C]; linarith
  have hgC : Cg ≤ C := by dsimp [C]; linarith
  have hrC : Cr ≤ C := by dsimp [C]; linarith
  have hlC : Cl ≤ C := by dsimp [C]; linarith
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro n hn
  obtain ⟨D, hD, hpD, hlocal⟩ := hdensity n hn
  obtain ⟨E, hE, hpE, hpre⟩ := rdiv_preliminary_event_of_density_event V P sample split
    rHat δr hPilot (ξ / 2) hhalf n hn D hD (by simpa only [heq] using hpD)
  simp only [heq] at hpre
  obtain ⟨N, hsub, hN, hN0⟩ := exists_measurable_superset_of_null
    (hPilot.2 n hn (ξ / 4) hquarter).2.1
  refine ⟨E \ N, hE.diff hN, ?_, ?_⟩
  · simpa only [measureReal_def, measure_sdiff_null hN0] using hpE
  intro ω hω
  obtain ⟨hωD, hpilot⟩ := hpre ω hω.1
  obtain ⟨hg, hrate⟩ := hlocal ω hωD
  have hmem : MemLp (rHat n ω) 2 (V.law.map V.zOf) := by
    by_contra h
    exact hω.2 (hsub h)
  have hδ : 0 ≤ δG n (ξ / 4) := (hRadius n hn (ξ / 4) hquarter).1.le
  refine ⟨hg, hrate.trans (mul_le_mul_of_nonneg_right hdC (sq_nonneg _)),
    hmem, hpilot, ?_, ?_, ?_⟩
  · intro h hh
    exact (rdiv_estimated_operator_global_rate V mu G g₀ gHat support B c₀ CG Cd
      (δG n (ξ / 4)) n ω hIV hDensity hBounds hHyp hB hg hCd.le hδ hrate h hh).trans
      (mul_le_mul_of_nonneg_right hgC hδ)
  · intro h hh h' hh'
    exact (rdiv_estimated_operator_relative_rate V mu G g₀ gHat support c₀ CG Cd
      (δG n (ξ / 4)) n ω hIV hDensity hBounds hg hCd.le hδ hrate (h - h')).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hrC hδ) (norm_nonneg _))
  · intro h hh h' hh'
    exact (rdiv_conditional_population_loss_rate V mu G g₀ gHat support B c₀ CG Cd
      (δG n (ξ / 4)) n ω hIV hDensity hBounds hHyp hOutcome hg hCd.le hδ hrate
      h hh h' hh').trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlC hδ) (norm_nonneg _))


-- @node: lem:err-l-dp
/-- Assume [localized likelihood concentration](hyp:hLi_of_gate),
[vector Lipschitz concentration](hyp:hVector_of_gate), [a grid ratio in $[1/2,1)$](hyp:hρ),
[a failure budget strictly between zero and one](hyp:hξ), [the RDIV model](hyp:hIV),
[the range condition](hyp:hRange), [solution realizability](hyp:hRealizable),
[density realizability](hyp:hDensity), [density bounds](hyp:hDensityBounds),
[the pilot regression rate](hyp:hPilotRate), [bounded outcomes](hyp:hOutcome),
[bounded hypotheses](hyp:hHypBound), [a bounded pilot](hyp:hPilotBound),
[measurable class suprema](hyp:hSupMeas), [measurable likelihood processes](hyp:hLikMeas),
[the fitting supremum version](hyp:hFittingVersion), [the selected density version](hyp:hSelectedDensityVersion),
[the selected pilot version](hyp:hSelectedPilotVersion), [density critical-radius control](hyp:hDensityRadius),
[hypothesis critical-radius control](hyp:hHypRadius), [the radius floor](hyp:hRadiusFloor),
[calibrated accuracy and noise scales](hyp:hScale), [attained empirical minima](hyp:hMinima),
and [selection of a likelihood maximizer](hyp:hMLE). [One positive constant gives,
for each positive sample size, a measurable event of probability at least one minus
the budget carrying all joint RDIV comparisons, uniformly bounded conditional-to-empirical
risk increments over hypotheses and grid penalties, and calibration error bounded by
the noise scale times projected estimation error plus squared noise scale](goal). -/
lemma err_l_dp
    (hLi_of_gate : LiLocalizedConcentration V)
    (hVector_of_gate : LipschitzVectorLocalizedConcentration V P sample split)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (hIV : RDIVSetting V mu g₀)
    (hRange : RangeCondition V)
    (hRealizable : H0MemHypothesisClass V)
    (hDensity : DensityRealizable V mu G g₀)
    (hDensityBounds : DensityBounds G g₀ support c₀ CG)
    (hPilotRate : PilotRegressionRate V P sample split rHat δr)
    (hOutcome : OutcomeBounded V B)
    (hHypBound : HypothesisClassBounded V support B)
    (hPilotBound : PilotBounded V P rHat pilotInputSupport B)
    (hSupMeas : RDIVClassesMeasurable V P sample split mu G g₀ gHat)
    (hLikMeas : RDIVLikelihoodProcessesMeasurable V G g₀)
    (hFittingVersion : RDIVFittingSupremumVersion V P sample split mu gHat ρ)
    (hSelectedDensityVersion : RDIVSelectedDensityVersion V P sample split mu gHat)
    (hSelectedPilotVersion : RDIVSelectedPilotVersion V P sample split rHat)
    (hDensityRadius : DensityCriticalRadiusBound V G g₀ δG)
    (hHypRadius : HypothesisCriticalRadiusBound V mu G δH ρ)
    (hRadiusFloor : RDIVRadiusFloor δG δH ρ)
    (hScale : RDIVScaleCalibration ρ ξ δ ν δG δH δr 1)
    (hMinima : RDIVMinimaAttained V P sample split mu gHat ρ candidate)
    (hMLE : MLEMaximizerSelected V P sample split G gHat)
    : ∃ C > 0, ∀ n : ℕ, 0 < n → ∃ E : Set Ω,
      MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧
      RDIVComparisonsOn V P sample split mu g₀ gHat rHat ρ ξ ν δG δH δr candidate n E C ∧ ∀ ω ∈ E,
      (∀ lam ∈ regGrid ρ n, ∀ h ∈ V.H,
        |(conditionalRisk V mu gHat n ω lam h - conditionalRisk V mu gHat n ω lam (minNormSolution V)) -
          (empiricalRisk V P sample split mu gHat n ω lam h - empiricalRisk V P sample split mu gHat n ω lam (minNormSolution V))| ≤
          C * (δH n (gridConfidence ρ ξ n / 4) * ‖h - minNormSolution V‖ +
            δH n (gridConfidence ρ ξ n / 4) ^ 2)) ∧
      ∀ lam ∈ regGrid ρ n,
        |rdivCalibrationStat V P sample split mu gHat rHat n ω (candidate n lam ω) - ‖projCondExpOp V (candidate n lam ω - minNormSolution V)‖ ^ 2| ≤
          C * ν n * ‖projCondExpOp V (candidate n lam ω - minNormSolution V)‖ + C * ν n ^ 2 := by
  obtain ⟨Cfit, hCfit, hfitEvent⟩ := rdiv_fitting_comparison_event V P sample split
    mu G g₀ gHat support B c₀ CG ρ ξ δG δH hVector_of_gate hρ hξ hIV hRange
    hRealizable hDensity hDensityBounds hOutcome hHypBound hMLE hSupMeas hFittingVersion
    hHypRadius hRadiusFloor
  obtain ⟨Cpre, hCpre, hpreliminary⟩ := rdiv_preliminary_event_local (hLi_of_gate := hLi_of_gate) V P sample split
    mu G g₀ gHat rHat support B c₀ CG ρ ξ δG δH δr hIV hDensity
    hDensityBounds hPilotRate hOutcome hHypBound hSelectedDensityVersion hMLE hSupMeas hLikMeas hDensityRadius hRadiusFloor hξ
  have hB := hOutcome.1
  let K := 4 * (4 * B + 8 * B ^ 2 + 3)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨Ccal, hCcal, htransfer⟩ := rdiv_calibration_projected_comparison_calibrated V
    mu G g₀ gHat rHat support B c₀ CG ρ ξ Cpre K δ ν δG δH δr
    hIV hRange hDensity hDensityBounds hHypBound hOutcome.1 hCpre.le hK hScale
  refine ⟨Cpre + Cfit + Ccal, by positivity, ?_⟩
  intro n hn
  obtain ⟨D, hD, hpD, hpre⟩ := hpreliminary n hn
  obtain ⟨F, hF, hpF, hfit⟩ := hfitEvent n hn
  obtain ⟨Ecal, hEcal, hpEcal, hcal⟩ := rdiv_fitted_calibration_bernstein_event (hSelectedPilotVersion := hSelectedPilotVersion)
    (hSelectedDensityVersion := hSelectedDensityVersion)
    V P sample split mu G g₀ gHat rHat support B c₀ CG ρ ξ δr candidate
    hIV hDensity hDensityBounds hHypBound hOutcome.1 hPilotRate hPilotBound
    hSupMeas hMinima hMLE hξ n hn
  have hquarter : ξ / 4 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hξ.1, hξ.2]
  have hG := (hDensityRadius n hn (ξ / 4) hquarter).1.le
  have hH : 0 ≤ δH n (gridConfidence ρ ξ n / 4) := by
    have hh := (hHypRadius n hn (ξ / 4) hquarter).1.1.le
    have he : gridConfidence ρ (ξ / 4) n = gridConfidence ρ ξ n / 4 := by
      unfold gridConfidence
      ring
    rwa [he] at hh
  have hr := (hPilotRate.2 n hn (ξ / 4) hquarter).1
  have hν := (rdiv_calibration_scale_domination ρ ξ Cpre δ ν δG δH δr
    hScale hCpre.le n hn hG hr).1
  have hfloor : rdivPublicLogScale ρ ξ n ≤ ν n := by
    have hs := ((rdivScaleCalibration_one_iff_public ρ ξ δ ν δG δH δr).mp
      hScale).1 n hn |>.2
    change δG n (ξ / 4) + δr n (ξ / 4) + rdivPublicLogScale ρ ξ n ≤ ν n at hs
    linarith only [hs, hG, hr]
  have ha : Real.sqrt (Real.log (2 / (gridConfidence ρ ξ n / 4)) / n) ≤ 2 * ν n :=
    (rdiv_calibration_log_radius_le ρ ξ hρ hξ n hn).trans
      (mul_le_mul_of_nonneg_left hfloor (by norm_num))
  have hcalProjected : ∀ ω ∈ D, ω ∈ Ecal → ∀ lam ∈ regGrid ρ n,
      |rdivCalibrationStat V P sample split mu gHat rHat n ω (candidate n lam ω) -
        ‖projCondExpOp V (candidate n lam ω - minNormSolution V)‖ ^ 2| ≤
        Ccal * ν n * ‖projCondExpOp V (candidate n lam ω - minNormSolution V)‖ +
          Ccal * ν n ^ 2 := by
    intro ω hωD hωcal lam hlam
    apply htransfer n hn ω (hpre ω hωD).1 (hpre ω hωD).2 hG
      (candidate n lam ω) ((hMinima n hn lam hlam).1 ω).1
    have hb := hcal ω hωcal lam hlam
    let Q := inputL2Norm (V.law.map V.zOf)
      (rHat n ω - estimatedOperator V mu gHat n ω (candidate n lam ω))
    let a := Real.sqrt (Real.log (2 / (gridConfidence ρ ξ n / 4)) / n)
    have hQ : 0 ≤ Q := Real.sqrt_nonneg _
    have ha0 : 0 ≤ a := Real.sqrt_nonneg _
    have hlinear : a * Q ≤ 2 * ν n * Q := mul_le_mul_of_nonneg_right ha hQ
    have hsquare : a ^ 2 ≤ 4 * ν n ^ 2 := by
      have hs := pow_le_pow_left₀ ha0 ha 2
      nlinarith only [hs]
    have hbase : a * Q + a ^ 2 ≤ 4 * (ν n * Q + ν n ^ 2) := by
      nlinarith only [hlinear, hsquare, mul_nonneg hν hQ]
    have hcoef : 0 ≤ 4 * B + 8 * B ^ 2 + 3 := by positivity
    apply hb.trans
    change (4 * B + 8 * B ^ 2 + 3) * (a * Q + a ^ 2) ≤ _
    have hi := mul_le_mul_of_nonneg_left hbase hcoef
    dsimp only [K]
    nlinarith only [hi]
  obtain ⟨hE, hpE, hcomp⟩ := rdiv_comparison_event_assembly V P sample split
    ρ ξ ν δG δH δr mu g₀ gHat rHat candidate Cpre Cfit Ccal hCpre hCfit hCcal
    n hξ hG hH hν D F Ecal hD hF hEcal hpD hpF hpEcal
    (fun ω hω => (hpre ω hω).2) hfit hcalProjected
  exact ⟨D ∩ F ∩ Ecal, hE, hpE, hcomp, fun ω hω => (hcomp ω hω).2⟩

/-- Under [localized likelihood concentration](hyp:hLi_of_gate),
[vector Lipschitz concentration](hyp:hVector_of_gate), [a grid ratio in $[1/2,1)$](hyp:hρ),
[a failure budget strictly between zero and one](hyp:hξ), [the RDIV model](hyp:hIV),
[the range condition](hyp:hRange), [solution realizability](hyp:hRealizable),
[density realizability](hyp:hDensity), [density bounds](hyp:hDensityBounds),
[the pilot regression rate](hyp:hPilotRate), [bounded outcomes](hyp:hOutcome),
[bounded hypotheses](hyp:hHypBound), [a bounded pilot](hyp:hPilotBound),
[measurable class suprema](hyp:hSupMeas), [measurable likelihood processes](hyp:hLikMeas),
[the fitting supremum version](hyp:hFittingVersion), [the selected density version](hyp:hSelectedDensityVersion),
[the selected pilot version](hyp:hSelectedPilotVersion), [density critical-radius control](hyp:hDensityRadius),
[hypothesis critical-radius control](hyp:hHypRadius), [the radius floor](hyp:hRadiusFloor),
[calibrated accuracy and noise scales](hyp:hScale), [attained empirical minima](hyp:hMinima),
and [selection of a likelihood maximizer](hyp:hMLE), [there is one positive constant
such that every positive sample size admits a measurable event of probability at
least one minus the budget satisfying all joint RDIV comparisons, the grid-uniform
conditional-to-empirical risk increment bound, and the calibration bound by noise
scale times projected estimation error plus squared noise scale](goal). -/
-- @node: err_l_dp_local
lemma err_l_dp_local
    (hLi_of_gate : LiLocalizedConcentration V)
    (hVector_of_gate : LipschitzVectorLocalizedConcentration V P sample split)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (hIV : RDIVSetting V mu g₀)
    (hRange : RangeCondition V)
    (hRealizable : H0MemHypothesisClass V)
    (hDensity : DensityRealizable V mu G g₀)
    (hDensityBounds : DensityBounds G g₀ support c₀ CG)
    (hPilotRate : PilotRegressionRate V P sample split rHat δr)
    (hOutcome : OutcomeBounded V B)
    (hHypBound : HypothesisClassBounded V support B)
    (hPilotBound : PilotBounded V P rHat pilotInputSupport B)
    (hSupMeas : RDIVClassesMeasurable V P sample split mu G g₀ gHat)
    (hLikMeas : RDIVLikelihoodProcessesMeasurable V G g₀)
    (hFittingVersion : RDIVFittingSupremumVersion V P sample split mu gHat ρ)
    (hSelectedDensityVersion : RDIVSelectedDensityVersion V P sample split mu gHat)
    (hSelectedPilotVersion : RDIVSelectedPilotVersion V P sample split rHat)
    (hDensityRadius : DensityCriticalRadiusBound V G g₀ δG)
    (hHypRadius : HypothesisCriticalRadiusBound V mu G δH ρ)
    (hRadiusFloor : RDIVRadiusFloor δG δH ρ)
    (hScale : RDIVScaleCalibration ρ ξ δ ν δG δH δr 1)
    (hMinima : RDIVMinimaAttained V P sample split mu gHat ρ candidate)
    (hMLE : MLEMaximizerSelected V P sample split G gHat)
    : ∃ C > 0, ∀ n : ℕ, 0 < n → ∃ E : Set Ω,
      MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧
      RDIVComparisonsOn V P sample split mu g₀ gHat rHat ρ ξ ν δG δH δr candidate n E C ∧ ∀ ω ∈ E,
      (∀ lam ∈ regGrid ρ n, ∀ h ∈ V.H,
        |(conditionalRisk V mu gHat n ω lam h - conditionalRisk V mu gHat n ω lam (minNormSolution V)) -
          (empiricalRisk V P sample split mu gHat n ω lam h - empiricalRisk V P sample split mu gHat n ω lam (minNormSolution V))| ≤
          C * (δH n (gridConfidence ρ ξ n / 4) * ‖h - minNormSolution V‖ +
            δH n (gridConfidence ρ ξ n / 4) ^ 2)) ∧
      ∀ lam ∈ regGrid ρ n,
        |rdivCalibrationStat V P sample split mu gHat rHat n ω (candidate n lam ω) - ‖projCondExpOp V (candidate n lam ω - minNormSolution V)‖ ^ 2| ≤
          C * ν n * ‖projCondExpOp V (candidate n lam ω - minNormSolution V)‖ + C * ν n ^ 2 := by
  obtain ⟨Cfit, hCfit, hfitEvent⟩ := rdiv_fitting_concentration_local V P sample split
    mu G g₀ gHat support B c₀ CG ρ ξ δG δH hVector_of_gate hρ hξ hIV hRange
    hRealizable hDensity hDensityBounds hOutcome hHypBound hMLE hSupMeas hFittingVersion
    hHypRadius hRadiusFloor
  obtain ⟨Cpre, hCpre, hpreliminary⟩ := rdiv_preliminary_event_local (hLi_of_gate := hLi_of_gate) V P sample split
    mu G g₀ gHat rHat support B c₀ CG ρ ξ δG δH δr hIV hDensity
    hDensityBounds hPilotRate hOutcome hHypBound hSelectedDensityVersion hMLE hSupMeas hLikMeas hDensityRadius hRadiusFloor hξ
  have hB := hOutcome.1
  let K := 4 * (4 * B + 8 * B ^ 2 + 3)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨Ccal, hCcal, htransfer⟩ := rdiv_calibration_projected_comparison_calibrated V
    mu G g₀ gHat rHat support B c₀ CG ρ ξ Cpre K δ ν δG δH δr
    hIV hRange hDensity hDensityBounds hHypBound hOutcome.1 hCpre.le hK hScale
  refine ⟨Cpre + Cfit + Ccal, by positivity, ?_⟩
  intro n hn
  obtain ⟨D, hD, hpD, hpre⟩ := hpreliminary n hn
  obtain ⟨F, hF, hpF, hfit⟩ := hfitEvent n hn
  obtain ⟨Ecal, hEcal, hpEcal, hcal⟩ := rdiv_fitted_calibration_bernstein_event (hSelectedPilotVersion := hSelectedPilotVersion)
    (hSelectedDensityVersion := hSelectedDensityVersion)
    V P sample split mu G g₀ gHat rHat support B c₀ CG ρ ξ δr candidate
    hIV hDensity hDensityBounds hHypBound hOutcome.1 hPilotRate hPilotBound
    hSupMeas hMinima hMLE hξ n hn
  have hquarter : ξ / 4 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hξ.1, hξ.2]
  have hG := (hDensityRadius n hn (ξ / 4) hquarter).1.le
  have hH : 0 ≤ δH n (gridConfidence ρ ξ n / 4) := by
    have hh := (hHypRadius n hn (ξ / 4) hquarter).1.1.le
    have he : gridConfidence ρ (ξ / 4) n = gridConfidence ρ ξ n / 4 := by
      unfold gridConfidence
      ring
    rwa [he] at hh
  have hr := (hPilotRate.2 n hn (ξ / 4) hquarter).1
  have hν := (rdiv_calibration_scale_domination ρ ξ Cpre δ ν δG δH δr
    hScale hCpre.le n hn hG hr).1
  have hfloor : rdivPublicLogScale ρ ξ n ≤ ν n := by
    have hs := ((rdivScaleCalibration_one_iff_public ρ ξ δ ν δG δH δr).mp
      hScale).1 n hn |>.2
    change δG n (ξ / 4) + δr n (ξ / 4) + rdivPublicLogScale ρ ξ n ≤ ν n at hs
    linarith only [hs, hG, hr]
  have ha : Real.sqrt (Real.log (2 / (gridConfidence ρ ξ n / 4)) / n) ≤ 2 * ν n :=
    (rdiv_calibration_log_radius_le ρ ξ hρ hξ n hn).trans
      (mul_le_mul_of_nonneg_left hfloor (by norm_num))
  have hcalProjected : ∀ ω ∈ D, ω ∈ Ecal → ∀ lam ∈ regGrid ρ n,
      |rdivCalibrationStat V P sample split mu gHat rHat n ω (candidate n lam ω) -
        ‖projCondExpOp V (candidate n lam ω - minNormSolution V)‖ ^ 2| ≤
        Ccal * ν n * ‖projCondExpOp V (candidate n lam ω - minNormSolution V)‖ +
          Ccal * ν n ^ 2 := by
    intro ω hωD hωcal lam hlam
    apply htransfer n hn ω (hpre ω hωD).1 (hpre ω hωD).2 hG
      (candidate n lam ω) ((hMinima n hn lam hlam).1 ω).1
    have hb := hcal ω hωcal lam hlam
    let Q := inputL2Norm (V.law.map V.zOf)
      (rHat n ω - estimatedOperator V mu gHat n ω (candidate n lam ω))
    let a := Real.sqrt (Real.log (2 / (gridConfidence ρ ξ n / 4)) / n)
    have hQ : 0 ≤ Q := Real.sqrt_nonneg _
    have ha0 : 0 ≤ a := Real.sqrt_nonneg _
    have hlinear : a * Q ≤ 2 * ν n * Q := mul_le_mul_of_nonneg_right ha hQ
    have hsquare : a ^ 2 ≤ 4 * ν n ^ 2 := by
      have hs := pow_le_pow_left₀ ha0 ha 2
      nlinarith only [hs]
    have hbase : a * Q + a ^ 2 ≤ 4 * (ν n * Q + ν n ^ 2) := by
      nlinarith only [hlinear, hsquare, mul_nonneg hν hQ]
    have hcoef : 0 ≤ 4 * B + 8 * B ^ 2 + 3 := by positivity
    apply hb.trans
    change (4 * B + 8 * B ^ 2 + 3) * (a * Q + a ^ 2) ≤ _
    have hi := mul_le_mul_of_nonneg_left hbase hcoef
    dsimp only [K]
    nlinarith only [hi]
  obtain ⟨hE, hpE, hcomp⟩ := rdiv_comparison_event_assembly V P sample split
    ρ ξ ν δG δH δr mu g₀ gHat rHat candidate Cpre Cfit Ccal hCpre hCfit hCcal
    n hξ hG hH hν D F Ecal hD hF hEcal hpD hpF hpEcal
    (fun ω hω => (hpre ω hω).2) hfit hcalProjected
  exact ⟨D ∩ F ∩ Ecal, hE, hpE, hcomp, fun ω hω => (hcomp ω hω).2⟩

-- @node: lem:err-r-dp
/-- Suppose [the grid ratio lies in $[1/2,1)$](hyp:hρ), [the failure budget lies
strictly between zero and one](hyp:hξ), [the RDIV model](hyp:hIV),
[the range condition](hyp:hRange), [solution realizability](hyp:hRealizable),
[density realizability](hyp:hDensity), [density bounds](hyp:hDensityBounds),
[the pilot regression rate](hyp:hPilotRate), [bounded outcomes](hyp:hOutcome),
[bounded hypotheses](hyp:hHypBound), [a bounded pilot](hyp:hPilotBound),
[measurable class suprema](hyp:hSupMeas), [density critical-radius control](hyp:hDensityRadius),
[hypothesis critical-radius control](hyp:hHypRadius), [the radius floor](hyp:hRadiusFloor),
[calibrated accuracy and noise scales](hyp:hScale), [attained empirical minima](hyp:hMinima),
and [selection of a likelihood maximizer](hyp:hMLE) hold. [For each positive event
constant, one positive error constant bounds, on every measurable joint-comparison
event of the prescribed probability, the discrepancy between population and empirical
risk increments relative to the minimum-norm solution by accuracy times distance
to that solution plus squared accuracy, uniformly over hypotheses and grid penalties](goal). -/
lemma err_r_dp
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (hIV : RDIVSetting V mu g₀)
    (hRange : RangeCondition V)
    (hRealizable : H0MemHypothesisClass V)
    (hDensity : DensityRealizable V mu G g₀)
    (hDensityBounds : DensityBounds G g₀ support c₀ CG)
    (hPilotRate : PilotRegressionRate V P sample split rHat δr)
    (hOutcome : OutcomeBounded V B)
    (hHypBound : HypothesisClassBounded V support B)
    (hPilotBound : PilotBounded V P rHat pilotInputSupport B)
    (hSupMeas : RDIVClassesMeasurable V P sample split mu G g₀ gHat)
    (hDensityRadius : DensityCriticalRadiusBound V G g₀ δG)
    (hHypRadius : HypothesisCriticalRadiusBound V mu G δH ρ)
    (hRadiusFloor : RDIVRadiusFloor δG δH ρ)
    (hScale : RDIVScaleCalibration ρ ξ δ ν δG δH δr 1)
    (hMinima : RDIVMinimaAttained V P sample split mu gHat ρ candidate)
    (hMLE : MLEMaximizerSelected V P sample split G gHat)
    : ∀ Cevent : ℝ, 0 < Cevent → ∃ C > 0, ∀ n : ℕ, 0 < n →
      ∀ E : Set Ω, MeasurableSet E → 1 - ξ ≤ P.real E →
      RDIVComparisonsOn V P sample split mu g₀ gHat rHat ρ ξ ν δG δH δr candidate n E Cevent →
      ∀ ω ∈ E,
      ∀ h ∈ V.H, ∀ lam ∈ regGrid ρ n,
        |(populationRisk V lam h - populationRisk V lam (minNormSolution V)) -
          (empiricalRisk V P sample split mu gHat n ω lam h - empiricalRisk V P sample split mu gHat n ω lam (minNormSolution V))| ≤
          C * (δ n * ‖h - minNormSolution V‖ + δ n ^ 2) := by
  intro Cevent hCevent
  refine ⟨2 * Cevent, by positivity, ?_⟩
  intro n hn E hE hprob hComparisons ω hω h hh lam hlam
  have hquarter : ξ / 4 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hξ.1, hξ.2]
  have hG : 0 ≤ δG n (ξ / 4) :=
    (hDensityRadius n hn (ξ / 4) hquarter).1.le
  have hH : 0 ≤ δH n (gridConfidence ρ ξ n / 4) := by
    have hp := (hHypRadius n hn (ξ / 4) hquarter).1.1.le
    have heq : gridConfidence ρ (ξ / 4) n = gridConfidence ρ ξ n / 4 := by
      unfold gridConfidence
      ring
    rwa [heq] at hp
  have hsc := ((rdivScaleCalibration_one_iff_public ρ ξ δ ν δG δH δr).mp hScale).1 n hn |>.1
  change δG n (ξ / 4) + δH n (gridConfidence ρ ξ n / 4) +
    rdivPublicLogScale ρ ξ n ≤ δ n at hsc
  have hlog : 0 ≤ rdivPublicLogScale ρ ξ n := Real.sqrt_nonneg _
  have hGδ : δG n (ξ / 4) ≤ δ n := by linarith only [hsc, hH, hlog]
  have hHδ : δH n (gridConfidence ρ ξ n / 4) ≤ δ n := by
    linarith only [hsc, hG, hlog]
  have hδ : 0 ≤ δ n := hG.trans hGδ
  have hpre := (hComparisons ω hω).1.2.2.2.2.2 h hh
    (minNormSolution V) hRealizable
  have hfit := (hComparisons ω hω).2.1 lam hlam h hh
  have hpenalty :
      (populationRisk V lam h - populationRisk V lam (minNormSolution V)) -
        (empiricalRisk V P sample split mu gHat n ω lam h -
          empiricalRisk V P sample split mu gHat n ω lam (minNormSolution V)) =
      -((conditionalPopulationLoss V mu gHat n ω h -
          conditionalPopulationLoss V mu gHat n ω (minNormSolution V)) -
        (rdivPopulationLoss V h - rdivPopulationLoss V (minNormSolution V))) +
      ((conditionalRisk V mu gHat n ω lam h -
          conditionalRisk V mu gHat n ω lam (minNormSolution V)) -
        (empiricalRisk V P sample split mu gHat n ω lam h -
          empiricalRisk V P sample split mu gHat n ω lam (minNormSolution V))) := by
    unfold populationRisk conditionalRisk
    ring
  rw [hpenalty]
  calc
    _ ≤ |(conditionalPopulationLoss V mu gHat n ω h -
          conditionalPopulationLoss V mu gHat n ω (minNormSolution V)) -
        (rdivPopulationLoss V h - rdivPopulationLoss V (minNormSolution V))| +
      |(conditionalRisk V mu gHat n ω lam h -
          conditionalRisk V mu gHat n ω lam (minNormSolution V)) -
        (empiricalRisk V P sample split mu gHat n ω lam h -
          empiricalRisk V P sample split mu gHat n ω lam (minNormSolution V))| := by
      simpa only [abs_neg] using abs_add_le
        (-((conditionalPopulationLoss V mu gHat n ω h -
          conditionalPopulationLoss V mu gHat n ω (minNormSolution V)) -
          (rdivPopulationLoss V h - rdivPopulationLoss V (minNormSolution V)))) _
    _ ≤ Cevent * δG n (ξ / 4) * ‖h - minNormSolution V‖ +
        Cevent * (δH n (gridConfidence ρ ξ n / 4) * ‖h - minNormSolution V‖ +
          δH n (gridConfidence ρ ξ n / 4) ^ 2) := add_le_add hpre hfit
    _ ≤ Cevent * δ n * ‖h - minNormSolution V‖ +
        Cevent * (δ n * ‖h - minNormSolution V‖ + δ n ^ 2) := by
      gcongr
    _ ≤ _ := by nlinarith only [mul_nonneg hCevent.le (sq_nonneg (δ n))]

-- @node: lem:str-dp
/-- Under [a grid ratio in $[1/2,1)$](hyp:hρ), [a failure budget strictly between
zero and one](hyp:hξ), [the RDIV model](hyp:hIV), [the range condition](hyp:hRange),
[the source condition with the given exponent and witness](hyp:hSource),
[solution realizability](hyp:hRealizable), [density realizability](hyp:hDensity),
[density bounds](hyp:hDensityBounds), [the pilot regression rate](hyp:hPilotRate),
[bounded outcomes](hyp:hOutcome), [bounded hypotheses](hyp:hHypBound),
[a bounded pilot](hyp:hPilotBound), [measurable class suprema](hyp:hSupMeas),
[density critical-radius control](hyp:hDensityRadius), [hypothesis critical-radius control](hyp:hHypRadius),
[the radius floor](hyp:hRadiusFloor), [calibrated accuracy and noise scales](hyp:hScale),
[attained empirical minima](hyp:hMinima), and [selection of a likelihood maximizer](hyp:hMLE),
[for each positive event constant there is one positive constant bounding the sum
of squared projected estimation error and penalty-weighted squared norm error by
squared accuracy divided by penalty plus squared source-witness norm times penalty
to the bias exponent, for every grid penalty on any measurable joint-comparison
event of the prescribed probability](goal). -/
lemma str_dp
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (hIV : RDIVSetting V mu g₀)
    (hRange : RangeCondition V)
    (hSource : BetaSourceCondition V β w₀)
    (hRealizable : H0MemHypothesisClass V)
    (hDensity : DensityRealizable V mu G g₀)
    (hDensityBounds : DensityBounds G g₀ support c₀ CG)
    (hPilotRate : PilotRegressionRate V P sample split rHat δr)
    (hOutcome : OutcomeBounded V B)
    (hHypBound : HypothesisClassBounded V support B)
    (hPilotBound : PilotBounded V P rHat pilotInputSupport B)
    (hSupMeas : RDIVClassesMeasurable V P sample split mu G g₀ gHat)
    (hDensityRadius : DensityCriticalRadiusBound V G g₀ δG)
    (hHypRadius : HypothesisCriticalRadiusBound V mu G δH ρ)
    (hRadiusFloor : RDIVRadiusFloor δG δH ρ)
    (hScale : RDIVScaleCalibration ρ ξ δ ν δG δH δr 1)
    (hMinima : RDIVMinimaAttained V P sample split mu gHat ρ candidate)
    (hMLE : MLEMaximizerSelected V P sample split G gHat)
    : ∀ Cevent : ℝ, 0 < Cevent → ∃ C > 0, ∀ n : ℕ, 0 < n →
      ∀ E : Set Ω, MeasurableSet E → 1 - ξ ≤ P.real E →
      RDIVComparisonsOn V P sample split mu g₀ gHat rHat ρ ξ ν δG δH δr candidate n E Cevent →
      ∀ ω ∈ E,
      ∀ lam ∈ regGrid ρ n,
        ‖projCondExpOp V (candidate n lam ω - minNormSolution V)‖ ^ 2 + lam * ‖candidate n lam ω - minNormSolution V‖ ^ 2 ≤
          C * (δ n ^ 2 / lam + ‖w₀‖ ^ 2 * lam ^ biasExponent β) := by
  intro Cevent hCevent
  obtain ⟨Ce, hCe, herror⟩ := err_r_dp
    (V := V) (P := P) (sample := sample) (split := split)
    (ρ := ρ) (ξ := ξ) (B := B) (δ := δ) (ν := ν)
    (δG := δG) (δH := δH) (δr := δr) (c₀ := c₀) (CG := CG)
    (mu := mu) (G := G) (g₀ := g₀) (gHat := gHat) (rHat := rHat)
    (support := support) (candidate := candidate)
    hρ hξ hIV hRange hRealizable hDensity
    hDensityBounds hPilotRate hOutcome hHypBound hPilotBound hSupMeas
    hDensityRadius hHypRadius hRadiusFloor hScale hMinima hMLE Cevent hCevent
  obtain ⟨Cs, hCs, hsource⟩ := (variational_source V β w₀ hSource).2
    (1 / 4) (by norm_num)
  let C := 2 * (Ce ^ 2 + 2 * Ce + Cs) + 1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro n hn E hE hprob hComparisons ω hω lam hlam
  have hlamDom : lam ∈ Set.Ioc (0 : ℝ) 2 := by
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hlam
    have hρpos : 0 < ρ := by linarith only [hρ.1]
    refine ⟨mul_pos (by norm_num) (pow_pos hρpos k), ?_⟩
    have hp := pow_le_pow_of_le_one hρpos.le hρ.2.le (Nat.zero_le k)
    simpa only [gridValue, pow_zero, mul_one] using
      mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2)
  have hlampos := hlamDom.1
  let h := candidate n lam ω
  let u := h - minNormSolution V
  let U := ‖u‖
  let W := ‖projCondExpOp V u‖ ^ 2
  have hh : h ∈ V.H := (hMinima n hn lam hlam).1 ω |>.1
  have hopt := ((hMinima n hn lam hlam).1 ω).2 (minNormSolution V) hRealizable
  have herr := (abs_le.mp
    (herror n hn E hE hprob hComparisons ω hω h hh lam hlam)).2
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
  have hbasic : W + lam * U ^ 2 ≤ Ce * (δ n * U + δ n ^ 2) +
      2 * lam * |inner ℝ (minNormSolution V) u| := by
    have hi := neg_abs_le (inner ℝ (minNormSolution V) u)
    have hi' := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 2 * lam)
    change empiricalRisk V P sample split mu gHat n ω lam h ≤ _ at hopt
    change W + lam * (U ^ 2 + 2 * inner ℝ (minNormSolution V) u) - _ ≤
      Ce * (δ n * U + δ n ^ 2) at herr
    linarith only [herr, hopt, hi']
  have hYoung : Ce * δ n * U ≤ lam / 4 * U ^ 2 + Ce ^ 2 * (δ n ^ 2 / lam) := by
    apply (mul_le_mul_iff_left₀ hlamDom.1).mp
    have hcancel : lam * (δ n ^ 2 / lam) = δ n ^ 2 :=
      mul_div_cancel₀ _ hlamDom.1.ne'
    nlinarith only [sq_nonneg (lam * U - 2 * Ce * δ n), hcancel]
  have hnoise : δ n ^ 2 ≤ 2 * (δ n ^ 2 / lam) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hlamDom.1).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hlamDom.2 (sq_nonneg (δ n))]
  have hsource' := (hsource u).1 lam hlamDom
  change 2 * lam * |inner ℝ (minNormSolution V) u| ≤
    (1 / 4 : ℝ) * (W + lam * U ^ 2) + Cs * ‖w₀‖ ^ 2 * lam ^ biasExponent β at hsource'
  have henergy : W + lam * U ^ 2 ≤
      2 * (Ce ^ 2 + 2 * Ce) * (δ n ^ 2 / lam) +
        2 * Cs * (‖w₀‖ ^ 2 * lam ^ biasExponent β) := by
    have hn := mul_le_mul_of_nonneg_left hnoise hCe.le
    have hW : 0 ≤ W := sq_nonneg _
    nlinarith only [hbasic, hYoung, hn, hsource', hW]
  change W + lam * U ^ 2 ≤ _
  apply henergy.trans
  have hvar : 0 ≤ δ n ^ 2 / lam := by positivity
  have hbias : 0 ≤ ‖w₀‖ ^ 2 * lam ^ biasExponent β := by positivity
  have hcoefv : 2 * (Ce ^ 2 + 2 * Ce) ≤ C := by dsimp [C]; linarith
  have hcoefb : 2 * Cs ≤ C := by dsimp [C]; nlinarith only [hCe, sq_nonneg Ce]
  nlinarith only [mul_le_mul_of_nonneg_right hcoefv hvar,
    mul_le_mul_of_nonneg_right hcoefb hbias]

-- @node: lem:rdiv-accepted-bounds
/-- Given [a grid ratio in $[1/2,1)$](hyp:hρ), [a failure budget strictly between
zero and one](hyp:hξ), and [the RDIV model](hyp:hIV), [a positive inflation threshold
exists such that sufficiently calibrated bounds yield, for every positive event
constant, a positive error constant controlling projected estimation error by the
calibration statistic plus noise and norm error by the stability term plus that
same quantity to the interpolation exponent, uniformly over grid penalties on
every measurable joint-comparison event of the prescribed probability,
under the range condition, the source condition,
solution realizability, density realizability,
density bounds, the pilot regression rate,
bounded outcomes, bounded hypotheses,
a bounded pilot, measurable class suprema,
measurable likelihood processes, the fitting supremum version,
the selected density version, the selected pilot version,
density critical-radius control, hypothesis critical-radius control,
the radius floor, calibration of the base scales,
attained empirical minima, inflation above the required threshold,
deterministic calibration, and selection of a likelihood maximizer](goal). -/
lemma rdiv_accepted_bounds
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (hIV : RDIVSetting V mu g₀)
    : ∃ required > 0, ∀ (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ),
      ∀ (β : ℝ) (w₀ : V.Hbar.toSubmodule)
      (δ ν : ℕ → ℝ),
      (hRange : RangeCondition V) →
      (hSource : BetaSourceCondition V β w₀) →
      (hRealizable : H0MemHypothesisClass V) →
      (hDensity : DensityRealizable V mu G g₀) →
      (hDensityBounds : DensityBounds G g₀ support c₀ CG) →
      (hPilotRate : PilotRegressionRate V P sample split rHat δr) →
      (hOutcome : OutcomeBounded V B) →
      (hHypBound : HypothesisClassBounded V support B) →
      (hPilotBound : PilotBounded V P rHat pilotInputSupport B) →
      (hSupMeas : RDIVClassesMeasurable V P sample split mu G g₀ gHat) →
      (hLikMeas : RDIVLikelihoodProcessesMeasurable V G g₀) →
      (hFittingVersion : RDIVFittingSupremumVersion V P sample split mu gHat ρ) →
      (hSelectedDensityVersion : RDIVSelectedDensityVersion V P sample split mu gHat) →
      (hSelectedPilotVersion : RDIVSelectedPilotVersion V P sample split rHat) →
      (hDensityRadius : DensityCriticalRadiusBound V G g₀ δG) →
      (hHypRadius : HypothesisCriticalRadiusBound V mu G δH ρ) →
      (hRadiusFloor : RDIVRadiusFloor δG δH ρ) →
      (hScale : RDIVScaleCalibration ρ ξ baseδ baseν δG δH δr 1) →
      (hMinima : RDIVMinimaAttained V P sample split mu gHat ρ candidate) →
      (hInflation : CalibratedValidBounds δ ν baseδ baseν (κ₀ B c₀ CG Cm).1 (κ₀ B c₀ CG Cm).2 required) →
      (hDeterministic : CalibrationDeterministic δ ν) →
      (hMLE : MLEMaximizerSelected V P sample split G gHat) →
      ∀ Cevent : ℝ, 0 < Cevent → ∃ C > 0, ∀ n : ℕ, 0 < n →
      ∀ E : Set Ω, MeasurableSet E → 1 - ξ ≤ P.real E →
      RDIVComparisonsOn V P sample split mu g₀ gHat rHat ρ ξ ν δG δH δr candidate n E Cevent →
      ∀ ω ∈ E,
      ∀ lam ∈ regGrid ρ n,
        ‖projCondExpOp V (candidate n lam ω - minNormSolution V)‖ ^ 2 ≤
          C * (rdivCalibrationStat V P sample split mu gHat rHat n ω (candidate n lam ω) + rdivNoiseLevel (δ n) (ν n) lam) ∧
        ‖candidate n lam ω - minNormSolution V‖ ^ 2 ≤ C * (rdivStability (δ n) lam +
          (rdivCalibrationStat V P sample split mu gHat rHat n ω (candidate n lam ω) + rdivNoiseLevel (δ n) (ν n) lam) ^ interpolationExponent β) := by
  refine ⟨1, by norm_num, ?_⟩
  intro κ₀
  let κδ := (κ₀ B c₀ CG Cm).1
  let κν := (κ₀ B c₀ CG Cm).2
  intro β w₀ δ ν hRange hSource hRealizable hDensity hDensityBounds
    hPilotRate hOutcome hHypBound hPilotBound hSupMeas hLikMeas hFittingVersion hSelectedDensityVersion hSelectedPilotVersion hDensityRadius hHypRadius
    hRadiusFloor hScale hMinima hInflation hDeterministic hMLE
  intro Cevent hCevent
  have hquarter : ξ / 4 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hξ.1, hξ.2]
  have hG : ∀ n, 0 < n → 0 ≤ δG n (ξ / 4) := by
    intro n hn
    exact (hDensityRadius n hn (ξ / 4) hquarter).1.le
  have hH : ∀ n, 0 < n → 0 ≤ δH n (gridConfidence ρ ξ n / 4) := by
    intro n hn
    have hh := (hHypRadius n hn (ξ / 4) hquarter).1.1.le
    have he : gridConfidence ρ (ξ / 4) n = gridConfidence ρ ξ n / 4 := by
      unfold gridConfidence
      ring
    rwa [he] at hh
  have hsc := (rdivScaleCalibration_one_iff_public ρ ξ baseδ baseν δG δH δr).mp hScale
  have hdom : ∀ n, 0 < n →
      δG n (ξ / 4) ≤ δ n ∧ δH n (gridConfidence ρ ξ n / 4) ≤ δ n := by
    intro n hn
    have hs := (hsc.1 n hn).1
    change δG n (ξ / 4) + δH n (gridConfidence ρ ξ n / 4) +
      rdivPublicLogScale ρ ξ n ≤ baseδ n at hs
    have hg := hG n hn
    have hh := hH n hn
    have hl : 0 ≤ rdivPublicLogScale ρ ξ n := Real.sqrt_nonneg _
    have hb : 0 ≤ baseδ n := by linarith only [hg, hh, hl, hs]
    have hd : baseδ n ≤ δ n := by
      rw [hInflation.2.2.2.2.1 n]
      nlinarith only [hInflation.1, hb]
    constructor <;> linarith only [hg, hh, hl, hs, hd]
  obtain ⟨C, hC, hlocal⟩ := rdiv_accepted_bounds_local V P sample split
    mu g₀ gHat rHat ρ ξ B β Cevent δ ν δG δH δr w₀ candidate
    hρ hCevent hIV hRange hSource hRealizable hOutcome hMinima hG hH
    (fun n hn => (hdom n hn).1) (fun n hn => (hdom n hn).2)
  refine ⟨C, hC, ?_⟩
  intro n hn E hE hprob hEvent
  exact hlocal n hn E hEvent


/-- For [the instrumental-variable world](hyp:V), [sampling law](hyp:P),
[analysis sample](hyp:sample), [sample split](hyp:split), [grid ratio](hyp:ρ),
[failure budget](hyp:ξ), [envelope constant](hyp:B), [source exponent](hyp:β),
[source witness](hyp:w₀), [accuracy curve](hyp:δ), [noise curve](hyp:ν),
[base accuracy curve](hyp:baseδ), [base noise curve](hyp:baseν),
[density radius curve](hyp:δG), [hypothesis radius curve](hyp:δH),
[pilot radius curve](hyp:δr), [required inflation threshold](hyp:required),
[lower density bound](hyp:c₀), [upper density bound](hyp:CG),
[continuity constant](hyp:Cm), [inflation rule](hyp:κ₀), [reference measure](hyp:mu),
[density class](hyp:G), [true density](hyp:g₀), [density estimates](hyp:gHat),
[pilot estimates](hyp:rHat), [density support](hyp:support),
[pilot input support](hyp:pilotInputSupport), and [candidate estimators](hyp:candidate),
[the RDIV discrepancy scope](goal) evaluates [the public density accuracy](step:1),
[the public hypothesis accuracy](step:2), and [the public pilot accuracy](step:3),
and extracts [the accuracy inflation factor](step:4) and [the noise inflation factor](step:5).
It requires [an admissible grid ratio](step:6), [an interior failure budget](step:7),
[the RDIV model](step:8), [the range condition](step:9), [the source condition](step:10),
[solution realizability](step:11), [density realizability](step:12), [density bounds](step:13),
[the pilot rate](step:14), [bounded outcomes](step:15), [bounded hypotheses](step:16),
[a bounded pilot](step:17), [measurable class suprema](step:18),
[measurable likelihood processes](step:19), [the fitting supremum version](step:20),
[the selected density version](step:21), [the selected pilot version](step:22),
[density critical-radius control](step:23), [hypothesis critical-radius control](step:24),
[the radius floor](step:25), [public calibration of the base scales](step:26),
[attained empirical minima](step:27), [sufficient calibrated inflation](step:28),
[deterministic calibration](step:29), and [selection of a likelihood maximizer](step:30). -/
-- @node: ass:pin-174
noncomputable def PinRdivDiscrepancyBoundScope : Prop :=
  let publicG := rdivEvaluatedAccuracy δG
  let publicH := rdivEvaluatedAccuracy δH
  let publicR := rdivEvaluatedAccuracy δr
  let κδ := (κ₀ B c₀ CG Cm).1
  let κν := (κ₀ B c₀ CG Cm).2
  ρ ∈ Set.Ico (1 / 2 : ℝ) 1 ∧ ξ ∈ Set.Ioo (0 : ℝ) 1 ∧
  RDIVSetting V mu g₀ ∧ RangeCondition V ∧ BetaSourceCondition V β w₀ ∧
  H0MemHypothesisClass V ∧ DensityRealizable V mu G g₀ ∧
  DensityBounds G g₀ support c₀ CG ∧
  PilotRegressionRate V P sample split rHat δr ∧ OutcomeBounded V B ∧
  HypothesisClassBounded V support B ∧ PilotBounded V P rHat pilotInputSupport B ∧
  RDIVClassesMeasurable V P sample split mu G g₀ gHat ∧
  RDIVLikelihoodProcessesMeasurable V G g₀ ∧
  RDIVFittingSupremumVersion V P sample split mu gHat ρ ∧
  RDIVSelectedDensityVersion V P sample split mu gHat ∧
  RDIVSelectedPilotVersion V P sample split rHat ∧
  DensityCriticalRadiusBound V G g₀ δG ∧
  HypothesisCriticalRadiusBound V mu G δH ρ ∧ RDIVRadiusFloor δG δH ρ ∧
  RDIVPublicScaleCalibration ρ ξ baseδ baseν publicG publicH publicR ∧
  RDIVMinimaAttained V P sample split mu gHat ρ candidate ∧
  CalibratedValidBounds δ ν baseδ baseν κδ κν required ∧
  CalibrationDeterministic δ ν ∧
  MLEMaximizerSelected V P sample split G gHat

/-- [The accepted-bounds scope](goal) is the RDIV discrepancy scope, with all of
its model, measurability, radius, calibration, minimization, and density-selection
requirements and the same parameters. -/
-- @node: ass:pin-196
noncomputable def PinRdivAcceptedBoundsScope := @PinRdivDiscrepancyBoundScope

end Papers.TsAdaptiveEstimationInference
