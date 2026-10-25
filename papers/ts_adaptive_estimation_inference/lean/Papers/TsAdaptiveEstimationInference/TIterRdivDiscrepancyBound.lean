module
public import Papers.TsAdaptiveEstimationInference.Helpers.Selection
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIV
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVProjectedEnvelope
/-! TIterRdivDiscrepancyBound for adaptive inverse problems. -/
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
omit [IsProbabilityMeasure P] in
/-- Suppose [the range condition](hyp:hRange) and [the source condition](hyp:hSource)
hold, [the grid factor lies between one-half inclusive and one exclusive](hyp:hρ),
[there is at least one iteration](hyp:ht), [all positive-index propagation
multipliers are at least one](hyp:hSeq), [the raw comparison constant is
nonnegative](hyp:hCraw), [the inflation scale is positive](hyp:hL), [its square
is at least three](hyp:hLsq) and [dominates the raw constant squared plus the
raw constant](hyp:hCL), and [the accuracy curves are deterministic and
nonnegative](hyp:hδν). Then [at every sample size, an event carrying the
pre-inflation iterative RDIV comparisons also carries the discrepancy envelope
with coefficient three](goal).

Derive the coefficient-one envelope from the retained pre-inflation
certificate of the common constructor. This conditional helper makes no claim
about an event carrying only the coarser public stability inequalities. -/
lemma iter_rdiv_discrepancy_bound_on_event
    (hRange : RangeCondition V) (hSource : BetaSourceCondition V β w₀)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (ht : 1 ≤ t) (aSeq : ℕ → ℝ)
    (hSeq : ∀ j, 1 ≤ j → 1 ≤ aSeq j)
    (Craw L : ℝ) (hCraw : 0 ≤ Craw) (hL : 0 < L)
    (hLsq : 3 ≤ L ^ 2) (hCL : Craw ^ 2 + Craw ≤ L ^ 2)
    (hδν : CalibrationDeterministic δ ν) :
    ∀ n : ℕ, ∀ E : Set Ω,
      IterRDIVPreinflationOn V P sample split mu gHat rHat ρ c β aSeq t δ ν iter n E Craw L →
      IterRDIVDiscrepancyOn V P sample split mu gHat rHat ρ c (aSeq t) β t
        δ ν w₀ iter n E 3 := by
  have hupper := iter_rdiv_projected_upper_from_preinflation_uniform V β w₀
    hRange hSource t ht Craw L hCraw hL hLsq hCL
  intro n E hraw
  refine ⟨by norm_num, ?_⟩
  intro ω hω lam hl hs
  have hstep := (hraw ω hω).1 t ht le_rfl lam hl hs
  have hcal := (hraw ω hω).2 lam hl hs
  have hnum : 0 ≤ aSeq t := (by norm_num : (0 : ℝ) ≤ 1).trans (hSeq t ht)
  have hlam : 0 < lam := by
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hl
    exact mul_pos (by norm_num) (pow_pos (by linarith only [hρ.1]) k)
  exact hupper (iter n t lam ω) lam (aSeq t) (δ n) (ν n)
    (rdivCalibrationStat V P sample split mu gHat rHat n ω (iter n t lam ω))
    hlam hnum (hδν.2 n) hstep.1 hcal


/-- Given [fixed-center concentration](hyp:hFix_of_gate), [squared-loss concentration](hyp:hSq_of_gate),
[localized likelihood concentration](hyp:hLi_of_gate), and [a valid IV density
model](hyp:hIV), [there exist a population-dependent propagation sequence and
positive comparison constants such that, for any probability sampling law,
a grid factor between one-half inclusive and one exclusive, a failure level strictly between zero and
one, and a positive iteration count, a positive calibration
threshold makes the range and source conditions, solution
and density realizability, density bounds and the
pilot rate, bounded outcomes, hypotheses, and
pilot, measurable fitting and likelihood
processes, the fitting, selected density, selected pilot,
and fixed-center versions,
density and hypothesis radius bounds and their floor,
scale calibration, attained fitting minima, sufficient
inflation, deterministic accuracy curves,
iterative realizability, attained iterative minima,
and likelihood-maximizing density estimates, together with the
oracle-segment discrepancy condition at a positive sample size,
imply a measurable event of probability at least one minus the failure level
carrying iterative RDIV comparisons, stability, and the discrepancy envelope
for that same propagation sequence](goal).

Project the common constructed event to the public discrepancy envelope.
The same chosen sequence, original candidates and public oracle domain occur in
all three certificates. Quantitative absorption uses the retained pre-inflation
estimates, without spending any additional probability. -/
-- @node: thm:iter-rdiv-discrepancy-bound
theorem iter_rdiv_discrepancy_bound
    (hFix_of_gate : IterRDIVFixedCenterLocalizedConcentration (Ω := Ω) V)
    (hSq_of_gate : IterRDIVSquaredLossLocalizedConcentration (Ω := Ω) V)
    (hLi_of_gate : LiLocalizedConcentration V) (B c₀ CG : ℝ) (mu : Measure 𝒳)
    (G : Set (𝒳 → 𝒵 → ℝ)) (g₀ : 𝒳 → 𝒵 → ℝ) (support : Set (𝒳 × 𝒵))
    (hIV : RDIVSetting V mu g₀) :
    ∃ aSeq : ℕ → ℝ, aSeq 0 = 0 ∧ (∀ j, 1 ≤ j → 1 ≤ aSeq j) ∧ -- @realizes a_j(sequence depending only on its index and fixed population quantities)
      ∃ C > 0, ∃ Cenv > 0,
      ∀ (P : Measure Ω) (_hProbability : IsProbabilityMeasure P)
        (sample : AnalysisSample V P) (split : SampleSplit)
        (ρ ξ Cm : ℝ) (t : ℕ)
        (baseδ baseν : ℕ → ℝ) (δG δH δr : ℕ → ℝ → ℝ)
        (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (rHat : ℕ → Ω → 𝒵 → ℝ)
        (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
        (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule),
      let a := aSeq t -- @realizes a_t(terminal member of the same population-only sequence)
      (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) → (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1) →
      (ht : 1 ≤ t) →
      ∃ required > 0, ∀ (c : ℝ), 0 < c → ∀ (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ),
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
      (hFixedCenterVersion : IterRDIVFixedCenterSupremumVersion V P sample split mu gHat ρ) →
      (hDensityRadius : DensityCriticalRadiusBound V G g₀ δG) →
      (hHypRadius : HypothesisCriticalRadiusBound V mu G δH ρ) →
      (hRadiusFloor : RDIVRadiusFloor δG δH ρ) →
      (hScale : RDIVScaleCalibration ρ ξ baseδ baseν δG δH δr t) →
      (hMinima : RDIVMinimaAttained V P sample split mu gHat ρ candidate) →
      (hInflation : CalibratedValidBounds δ ν baseδ baseν (κ₀ B c₀ CG Cm).1 (κ₀ B c₀ CG Cm).2 required) →
      (hDeterministic : CalibrationDeterministic δ ν) →
      (hIterRealizable : IterRealizableRDIV V ρ c a β t δ ν) →
      (hIterMinima : IterRDIVMinimaAttained V P sample split mu gHat ρ t iter) →
      (hMLE : MLEMaximizerSelected V P sample split G gHat) →
      ∀ n : ℕ, 0 < n →
      (hOracle : IterRDIVOracleSegmentDiscrepancy ρ c a β t δ ν n) → ∃ E : Set Ω, -- @realizes \mathcal E_{n,t}^{\mathrm{IR}}(joint iteration-grid and calibration event per n)
      MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧
      IterRDIVComparisonsOn V P sample split mu g₀ gHat rHat ξ δG δH δr ρ c a β t δ ν iter n E C ∧
      IterRDIVStabilityOn V P sample split mu gHat rHat ρ c β aSeq t δ ν iter n E C ∧
      IterRDIVDiscrepancyEnvelope V P sample split mu gHat rHat ρ ξ c a β t δ ν w₀ iter n E Cenv := by
  obtain ⟨aSeq, hzero, hseq, Craw, hCraw, L, hL, hLsq, hCL, Cevent, hCevent, hjoint⟩ :=
    iter_rdiv_constructed_event (V := V) (Ω := Ω) hFix_of_gate hSq_of_gate
      hLi_of_gate B c₀ CG mu G g₀ support hIV
  refine ⟨aSeq, hzero, hseq, Cevent, hCevent, 3, by norm_num, ?_⟩
  intro P hProbability sample split ρ ξ Cm t baseδ baseν δG δH δr
    gHat rHat candidate iter
  dsimp only
  intro hρ hξ ht
  let : IsProbabilityMeasure P := hProbability
  obtain ⟨R, hR, hjoint⟩ := hjoint P hProbability sample split ρ ξ Cm t
    baseδ baseν δG δH δr gHat rHat candidate iter hρ hξ ht
  refine ⟨R, hR, ?_⟩
  intro c hc κ₀ β w₀ δ ν hRange hSource hRealizable hDensity hBounds
    hPilot hY hHyp hPB hMeas hLik hFitting hDV hPV hFV hG hH hFloor
    hScale hMinima hInflation hDeterministic hIterRealizable hIterMinima hMLE
  have henv := iter_rdiv_discrepancy_bound_on_event
    (V := V) (P := P) (sample := sample) (split := split)
    (ρ := ρ) (β := β) (w₀ := w₀) (t := t) (c := c) (δ := δ) (ν := ν) (mu := mu) (gHat := gHat)
    (rHat := rHat) (iter := iter) hRange hSource hρ ht aSeq hseq
    Craw L hCraw.le (lt_of_lt_of_le zero_lt_one hL) hLsq hCL hDeterministic
  intro n hn hOracle
  obtain ⟨E, hE, hpE, hcomp, hstab, hraw⟩ := hjoint c hc κ₀ β w₀ δ ν hRange hSource
    hRealizable hDensity hBounds hPilot hY hHyp hPB hMeas hLik hFitting hDV hPV
    hFV hG hH hFloor hScale hMinima hInflation hDeterministic
    hIterRealizable hIterMinima hMLE n hn hOracle
  exact ⟨E, hE, hpE, hcomp, hstab, hE, hpE, henv n E hraw⟩

end Papers.TsAdaptiveEstimationInference
