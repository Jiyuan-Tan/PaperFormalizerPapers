module
public import Papers.TsAdaptiveEstimationInference.Helpers.Selection
public import Papers.TsAdaptiveEstimationInference.Helpers.Acceptance
public import Papers.TsAdaptiveEstimationInference.TTraeDiscrepancyBound
/-! TExistLambda for adaptive inverse problems. -/
@[expose] public section
set_option linter.style.longLine false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter
open scoped Topology
variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]
  (V : IVWorld 𝒲 𝒳 𝒵) (P : Measure Ω) [IsProbabilityMeasure P]
  (sample : AnalysisSample V P) (split : SampleSplit)
variable (ρ ξ B β : ℝ) (w₀ : V.Hbar.toSubmodule) -- @realizes \xi(prescribed real failure-probability parameter)
  (δ ν baseδ baseν : ℕ → ℝ) (δG δH δr tildeδ : ℕ → ℝ → ℝ)
  (κδ κν required c₀ CG Cm : ℝ) (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ)
  (mu : Measure 𝒳) (G : Set (𝒳 → 𝒵 → ℝ)) (g₀ : 𝒳 → 𝒵 → ℝ)
  (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (rHat : ℕ → Ω → 𝒵 → ℝ)
  (support : Set (𝒳 × 𝒵)) (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
  (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule)
  (a b c : ℝ) (t : ℕ)
/-- Given [localized TRAE concentration](hyp:hBennett_of_gate), [the range,
closeness, boundedness, mean-square continuity, critical-radius and scale-calibration
conditions imply a positive uniform constant such that, at every positive sample
size with a valid allocated failure level, a measurable event of probability at
least one minus that level bounds every feasible population residual loss by
its empirical loss plus the constant times the sum of squared accuracy and
accuracy times the residual norm](goal).

Specialize calibrated absolute deviation to feasible population residuals.
The existing range hypothesis is threaded from the public setup. -/
-- @node: traeResidualConcentration
lemma traeResidualConcentration
    (hBennett_of_gate : TRAELocalizedConcentration V) :
  ∀ (B : ℝ) (tildeδ : ℕ → ℝ → ℝ) (δ allocation : ℕ → ℝ),
    RangeCondition V → ClosenessCondition V → TRAEBoundedness V B → TRAECommonNullSetBoundedness V B → MeanSquareContinuity V →
    TRAECriticalRadiusBound V tildeδ → TRAEScaleCalibration δ tildeδ allocation →
    ∃ C > 0, ∀ n : ℕ, 0 < n → allocation n ∈ Set.Ioo (0 : ℝ) 1 →
      ∃ E : Set Ω, MeasurableSet E ∧ 1 - allocation n ≤ P.real E ∧
        ∀ ω ∈ E, ∀ h ∈ V.H,
          let f := projCondExpOp V (minNormSolution V - h)
          (∫ w, traeIntegrand V h f w ∂V.law) ≤
            blockAverage V P sample (split.fit n) (traeIntegrand V h f) ω +
              C * (δ n ^ 2 + δ n * ‖f‖) := by
  intro B tildeδ δ allocation hRange hClose hBound hCommon hMSC hComplexity hScale
  obtain ⟨C, hC, hdeviation⟩ := trae_calibrated_deviation_at_allocation
    V P sample split hBennett_of_gate B tildeδ hBound hCommon hMSC hComplexity
  refine ⟨C, hC, ?_⟩
  intro n hn halloc
  obtain ⟨E, hE, hpE, hdev⟩ :=
    hdeviation δ allocation hRange hClose hScale n hn halloc
  refine ⟨E, hE, ?_, ?_⟩
  · linarith [halloc.1]
  · intro ω hω h hh
    linarith only [(abs_le.mp (hdev ω hω h hh _ (hClose h hh))).1]

/-- Given [localized TRAE concentration](hyp:hBennett_of_gate), [the squared-norm
comparison](hyp:hNorm_of_gate), [a grid factor between one-half inclusive and one
exclusive](hyp:hρ), and [a failure level strictly between zero and one](hyp:hξ),
[there is a positive calibration threshold such that the range condition,
the source condition, solution realizability,
closeness, mean-square continuity, boundedness,
a common boundedness null set, critical-radius control,
allocated scale calibration, attained fitting minima,
adequate inflation of the base bounds, and deterministic accuracy
curves yield one positive constant and, at every positive
sample size, a measurable event of probability at least one minus the failure
level carrying the TRAE loss comparisons and discrepancy envelope](goal).

The conditional selection proposition uses a paper-local common-event
construction. Residual concentration is proved above; reverse comparisons,
squared-norm instantiation, confidence subdivision and the envelope are local
obligations under exactly the proposition's recorded hypotheses. A residual
comparison is never promoted to the generic cited Bennett carrier. -/
-- @node: trae_selection_envelope_local
lemma trae_selection_envelope_local
    (hBennett_of_gate : TRAELocalizedConcentration V)
    (hNorm_of_gate : SquaredNormLocalizedComparison V P sample split)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1) -- @realizes \xi(failure level strictly between zero and one)
    : ∃ required > 0, ∀ (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ),
      ∀ (β : ℝ) (w₀ : V.Hbar.toSubmodule)
      (δ ν : ℕ → ℝ),
      (hRange : RangeCondition V) →
      (hSource : BetaSourceCondition V β w₀) →
      (hRealizable : H0MemHypothesisClass V) →
      (hClose : ClosenessCondition V) →
      (hMSC : MeanSquareContinuity V) →
      (hBound : TRAEBoundedness V B) → (hCommon : TRAECommonNullSetBoundedness V B) →
      (hComplexity : TRAECriticalRadiusBound V tildeδ) →
      (hScale : TRAEScaleCalibration baseδ tildeδ (fun n => gridConfidence ρ ξ n)) →
      (hMinima : TRAEMinimaAttained V P sample split ρ candidate) →
      (hInflation : CalibratedValidBounds δ ν baseδ baseν (κ₀ B c₀ CG Cm).1 (κ₀ B c₀ CG Cm).2 required) →
      (hDeterministic : CalibrationDeterministic δ ν) →
      ∃ C > 0, ∀ n : ℕ, 0 < n → ∃ E : Set Ω,
      MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧
      TRAEComparisonsOn V P sample split δ n E C ∧ TRAEDiscrepancyEnvelope V P sample split ρ β δ w₀ candidate n E C := by
  exact trae_discrepancy_bound (hBennett_of_gate := hBennett_of_gate) (V := V) (P := P) (sample := sample) (split := split)
    (ρ := ρ) (ξ := ξ) (B := B) (baseδ := baseδ) (baseν := baseν)
    (tildeδ := tildeδ) (c₀ := c₀) (CG := CG) (Cm := Cm) (candidate := candidate)
    hNorm_of_gate hρ hξ

/-- Under [localized TRAE concentration](hyp:hBennett_of_gate), [the squared-norm
comparison](hyp:hNorm_of_gate), [a grid factor between one-half inclusive and one
exclusive](hyp:hρ), and [a failure level strictly between zero and one](hyp:hξ),
[there is a positive calibration threshold such that the range condition,
the source condition, solution realizability,
closeness, mean-square continuity, boundedness,
common-null-set boundedness, critical-radius control,
allocated scale calibration, attained fitting minima,
sufficient calibration inflation, and deterministic accuracy
curves imply a logarithmic grid-size bound and a positive
uniform constant giving, at every eligible sample size, a measurable event of
probability at least one minus the failure level with the discrepancy envelope,
acceptance, the fit-count bound, and the initial-or-adjacent return alternative](goal).

Acceptance and the return alternatives hold on one common event for each n.
Residual concentration is a local proof obligation under the recorded modeling
and calibration assumptions, including the allocated confidence levels. Only the
squared-norm and generic Bennett comparisons are supplied as cited inputs. -/
-- @node: prop:exist-lambda
theorem exist_lambda
    (hBennett_of_gate : TRAELocalizedConcentration V)
    (hNorm_of_gate : SquaredNormLocalizedComparison V P sample split)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1) -- @realizes \xi(failure level strictly between zero and one)
    : ∃ required > 0, ∀ (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ),
      ∀ (β : ℝ) (w₀ : V.Hbar.toSubmodule)
      (δ ν : ℕ → ℝ),
      (hRange : RangeCondition V) →
      (hSource : BetaSourceCondition V β w₀) →
      (hRealizable : H0MemHypothesisClass V) →
      (hClose : ClosenessCondition V) →
      (hMSC : MeanSquareContinuity V) →
      (hBound : TRAEBoundedness V B) → (hCommon : TRAECommonNullSetBoundedness V B) →
      (hComplexity : TRAECriticalRadiusBound V tildeδ) →
      (hScale : TRAEScaleCalibration baseδ tildeδ (fun n => gridConfidence ρ ξ n)) →
      (hMinima : TRAEMinimaAttained V P sample split ρ candidate) →
      (hInflation : CalibratedValidBounds δ ν baseδ baseν (κ₀ B c₀ CG Cm).1 (κ₀ B c₀ CG Cm).2 required) →
      (hDeterministic : CalibrationDeterministic δ ν) →
      (∃ Clog > 0, ∀ n : ℕ, traeMinSampleSize B ≤ n →
        (terminalIndex ρ n + 1 : ℕ) ≤ Clog * Real.log n) ∧
      ∃ C > 0, ∀ n : ℕ, traeMinSampleSize B ≤ n → ∃ E : Set Ω,
        TRAESelectionOnEvent
          (V := V) (P := P) (sample := sample) (split := split) (ρ := ρ) (ξ := ξ)
          (β := β) (w₀ := w₀) (δ := δ) (candidate := candidate)
          (fun _ => E) n C := by
  classical
  obtain ⟨required, hrequired, hdiscrepancy⟩ := trae_selection_envelope_local (hBennett_of_gate := hBennett_of_gate)
    (V := V) (P := P) (sample := sample) (split := split)
    (ρ := ρ) (ξ := ξ) (B := B) (baseδ := baseδ) (baseν := baseν)
    (tildeδ := tildeδ) (c₀ := c₀) (CG := CG) (Cm := Cm) (candidate := candidate)
    hNorm_of_gate hρ hξ
  refine ⟨required, hrequired, ?_⟩
  intro κ₀
  let κδ := (κ₀ B c₀ CG Cm).1
  let κν := (κ₀ B c₀ CG Cm).2
  intro β w₀ δ ν hRange hSource hRealizable hClose hMSC hBound hCommon
    hComplexity hScale hMinima hInflation hDeterministic
  obtain ⟨C, hC, hevent⟩ := hdiscrepancy κ₀ β w₀ δ ν hRange hSource
    hRealizable hClose hMSC hBound hCommon hComplexity hScale hMinima hInflation
    hDeterministic
  constructor
  · obtain ⟨Clog, hClog, hlog⟩ := terminalIndex_log_bound ρ hρ
    exact ⟨Clog, hClog, fun n hn => hlog n ((le_max_left _ _).trans hn)⟩
  · refine ⟨C, hC, ?_⟩
    intro n hn
    have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
    have hn0 : 0 < n := by omega
    obtain ⟨E, hE, hp, hcomp, henv⟩ := hevent n hn0
    obtain ⟨S, hS, hSae, hSbound⟩ := trae_sample_bounded_event V P sample B hBound hCommon
    refine ⟨E ∩ S, hE.inter hS, ?_, ?_, ?_, ?_⟩
    · have heq : (E ∩ S : Set Ω) =ᵐ[P] E := by
        filter_upwards [hSae] with ω hω
        exact propext ⟨fun h => h.1, fun h => ⟨h, hω⟩⟩
      rwa [measureReal_congr heq]
    · exact fun ω hω => hcomp ω hω.1
    · exact ⟨henv.1, fun ω hω => henv.2 ω hω.1⟩
    · intro ω hω
      let lam := gridValue ρ (terminalIndex ρ n)
      have hlam : lam ∈ regGrid ρ n := by
        exact Finset.mem_image.mpr
          ⟨terminalIndex ρ n, Finset.mem_range.mpr (Nat.lt_succ_self _), rfl⟩
      have hlpos : 0 < lam := mul_pos (by norm_num) (pow_pos (by linarith [hρ.1]) _)
      have hnorm : primalEmpSq V P sample split n ω (minNormSolution V) ≤ B ^ 2 := by
        unfold primalEmpSq blockAverage
        rw [split.card_fit]
        have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
        apply (inv_mul_le_iff₀ hn').2
        calc
          _ ≤ ∑ _i ∈ split.fit n, B ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            have hb := hSbound ω hω.2 i _ hRealizable
            nlinarith [sq_abs (primalVersion V (minNormSolution V) (V.xOf (sample.Z i ω))),
              mul_nonneg (sub_nonneg.mpr hb) (add_nonneg hBound.1 (abs_nonneg
                (primalVersion V (minNormSolution V) (V.xOf (sample.Z i ω)))))]
          _ = _ := by simp [split.card_fit]
      have hopt := ((hMinima n hn0 lam hlam).1 ω).2 _ hRealizable
      have hnonneg : 0 ≤ lam * primalEmpSq V P sample split n ω (candidate n lam ω) := by
        unfold primalEmpSq blockAverage
        positivity
      have hfit : traeEmpiricalLoss V P sample split n ω (candidate n lam ω) ≤
          δ n ^ 2 + lam * B ^ 2 := by
        have hz := (henv.2 ω hω.1).1
        have hd := mul_le_mul_of_nonneg_left hnorm hlpos.le
        linarith only [hopt, hnonneg, hz, hd]
      have hfloor := trae_calibrated_square_floor baseδ δ tildeδ
        (fun n => gridConfidence ρ ξ n) ν baseν κδ κν required hScale hInflation n hn0
      have hsize : 2 * B ^ 2 ≤ (n : ℝ) := by
        have hnceil : ⌈2 * B ^ 2⌉₊ ≤ n := (le_max_right _ _).trans hn
        exact (Nat.le_ceil _).trans (by exact_mod_cast hnceil)
      have hrem := terminal_remainder_le_half (B ^ 2) lam (δ n ^ 2) n
        (sq_nonneg _) hn0 hsize (terminalGrid_le ρ hρ n hn0) hfloor
      have hAccept : Accepts ρ n
          (fun l => traeEmpiricalLoss V P sample split n ω (candidate n l ω))
          (traeNoiseLevel (δ n)) := by
        refine ⟨terminalIndex ρ n, le_rfl, ?_⟩
        change traeEmpiricalLoss V P sample split n ω (candidate n lam ω) ≤ 3 / 2 * δ n ^ 2
        linarith only [hfit, hrem]
      obtain ⟨hindex, hcases⟩ := discrepancyIndex_first_acceptance ρ n _ _ hρ hAccept
      exact ⟨hAccept, Nat.add_le_add_right hindex 1, hcases⟩


/-- For [the instrumental-variable model](hyp:V), [sampling law](hyp:P), [analysis
sample](hyp:sample), [sample split](hyp:split), [grid factor](hyp:ρ), [failure
level](hyp:ξ), [boundedness scale](hyp:B), [accuracy curve](hyp:δ), and [candidate
estimator family](hyp:candidate), [the joint selection property](goal) means that
each eligible sample size admits a measurable event of probability at least one
minus the failure level on which [some grid penalty is accepted](step:1),
[the number of fits does not exceed the grid size](step:2), and [the returned
index is either zero or positive with the adjacent discrepancy relation](step:3).

For every eligible sample size, one measurable event carries acceptance,
the fit-count bound and the return alternative jointly. This is a conclusion,
never a separately supplied hypothesis. -/
-- @node: ass:pin-193
noncomputable def PinExistLambdaOnEvent : Prop :=
  ∀ n : ℕ, traeMinSampleSize B ≤ n → ∃ E : Set Ω, -- @realizes \mathcal E_n(common event chosen at each eligible sample size)
    MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧ ∀ ω ∈ E,
      let D := fun lam => traeEmpiricalLoss V P sample split n ω (candidate n lam ω)
      let A := traeNoiseLevel (δ n)
      let k := discrepancyIndex ρ n D A
      Accepts ρ n D A ∧ k + 1 ≤ terminalIndex ρ n + 1 ∧
        (k = 0 ∨ (0 < k ∧ AdjacentDiscrepancyRelation ρ
          (selectedPenalty ρ n D A) D A))

end Papers.TsAdaptiveEstimationInference
