module
public import Papers.TsAdaptiveEstimationInference.Helpers.Selection
public import Papers.TsAdaptiveEstimationInference.TCommonDp
public import Papers.TsAdaptiveEstimationInference.TTraeDiscrepancyBound
public import Papers.TsAdaptiveEstimationInference.Helpers.TikhonovOracle
public import Papers.TsAdaptiveEstimationInference.Helpers.TRAEAdaptiveRates
/-! TTikhonvRate for adaptive inverse problems. -/
@[expose] public section
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option maxHeartbeats 600000
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter
open scoped Topology
variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]
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
/-- Given [localized TRAE concentration](hyp:hBennett_of_gate), [the squared-norm
comparison](hyp:hNorm_of_gate), and [a grid factor between one-half inclusive
and one exclusive](hyp:hρ), [there is a positive calibration-threshold function
of the critical-radius curve, chosen before the source exponent and witness,
such that the range, source, realizability, closeness, mean-square continuity,
boundedness and minimizer-attainment conditions give one positive rate constant
uniform over calibrated deterministic accuracy curves and confidence; at every
eligible sample size, both selected Tikhonov error bounds hold on a measurable
event of probability at least one minus the failure level](goal).

The rate constant is uniform over the accuracy sequences, their base
curves and all admissible calibration multipliers, as well as confidence.
The source-independent threshold is a function of the critical-radius curve;
it is selected before the source exponent and source witness.
The squared-norm citation chooses its comparison constant before baseδ and ξ;
the local common-event construction specializes it at gridConfidence ρ ξ n.
Boundedness and localized loss measurability concern this primal world only. -/
-- @node: thm:tikhonv-rate
theorem tikhonov_rate
    (hBennett_of_gate : TRAELocalizedConcentration V)
    (hNorm_of_gate : SquaredNormLocalizedComparison V P sample split)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) :
    ∃ required : (ℕ → ℝ → ℝ) → ℝ,
      (∀ tildeδ, 0 < required tildeδ) ∧
      ∀ (β : ℝ) (w₀ : V.Hbar.toSubmodule),
      RangeCondition V → BetaSourceCondition V β w₀ →
      H0MemHypothesisClass V → ClosenessCondition V →
      MeanSquareContinuity V → TRAEBoundedness V B → TRAECommonNullSetBoundedness V B →
      TRAEMinimaAttained V P sample split ρ candidate →
      ∃ C > 0, ∀ (baseδ baseν δ ν : ℕ → ℝ) (tildeδ : ℕ → ℝ → ℝ)
        (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ),
      TRAECriticalRadiusBound V tildeδ →
      CalibratedValidBounds δ ν baseδ baseν (κ₀ B c₀ CG Cm).1 (κ₀ B c₀ CG Cm).2 (required tildeδ) →
      CalibrationDeterministic δ ν →
      ∀ ξ : ℝ, ξ ∈ Set.Ioo (0 : ℝ) 1 →
      TRAEScaleCalibration baseδ tildeδ (fun n => gridConfidence ρ ξ n) →
      ∀ n : ℕ, traeMinSampleSize B ≤ n → ∃ E : Set Ω,
        TRAERateOnEvent
          (V := V) (P := P) (sample := sample) (split := split) (ρ := ρ) (ξ := ξ)
          (β := β) (δ := δ) (candidate := candidate)
          (fun _ => E) n C := by
  classical
  obtain ⟨R, hR, hrate⟩ := trae_rate_of_calibrated_comparisons_uniform
    V P sample split ρ B candidate hρ
  -- Choose both comparison constants before the calibrated accuracy and confidence.
  have hUniformEvent : ∀ tildeδ : ℕ → ℝ → ℝ, ∃ Ce > 0,
      ∀ (baseδ : ℕ → ℝ) (ξ : ℝ), ξ ∈ Set.Ioo (0 : ℝ) 1 →
      RangeCondition V → H0MemHypothesisClass V → ClosenessCondition V →
      MeanSquareContinuity V → TRAEBoundedness V B → TRAECommonNullSetBoundedness V B →
      TRAECriticalRadiusBound V tildeδ →
      TRAEScaleCalibration baseδ tildeδ (fun n => gridConfidence ρ ξ n) →
      ∀ n : ℕ, 0 < n → ∃ E : Set Ω,
        MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧
          TRAEComparisonsOn V P sample split baseδ n E Ce := by
    intro tildeδ
    by_cases hSetup : MeanSquareContinuity V ∧ TRAEBoundedness V B ∧ TRAECommonNullSetBoundedness V B ∧
        TRAECriticalRadiusBound V tildeδ
    · obtain ⟨hMSC0, hBound0, hCommon0, hComplexity0⟩ := hSetup
      obtain ⟨Cl, hCl, hLoss⟩ := traeLossEventAtAllocationUniform V P sample split
        hBennett_of_gate B tildeδ hMSC0 hBound0 hCommon0 hComplexity0
      have hUniformNorm : ∃ Cn > 0,
          ∀ (baseδ : ℕ → ℝ) (ξ : ℝ), ξ ∈ Set.Ioo (0 : ℝ) 1 →
          H0MemHypothesisClass V →
          TRAEScaleCalibration baseδ tildeδ (fun n => gridConfidence ρ ξ n) →
          ∀ n : ℕ, 0 < n → ∃ En : Set Ω,
            MeasurableSet En ∧ 1 - gridConfidence ρ ξ n ≤ P.real En ∧
              ∀ ω ∈ En, ω ∈ sampleZeroEvent V P sample ∧ ∀ h ∈ V.H,
                |(primalEmpSq V P sample split n ω h -
                    primalEmpSq V P sample split n ω (minNormSolution V)) -
                  (‖h‖ ^ 2 - ‖minNormSolution V‖ ^ 2)| ≤
                    Cn * (baseδ n * ‖h - minNormSolution V‖ + baseδ n ^ 2) := by
        obtain ⟨Cn, hCn, hUniform⟩ :=
          hNorm_of_gate inferInstance B tildeδ hBound0 hCommon0 hComplexity0
        refine ⟨Cn, hCn, ?_⟩
        intro baseδ ξ hξ hRealizable hScale n hn
        have hk : (1 : ℝ) ≤ (terminalIndex ρ n + 1 : ℝ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
        have hValid : gridConfidence ρ ξ n ∈ Set.Ioo (0 : ℝ) 1 := by
          constructor
          · unfold gridConfidence; positivity [hξ.1]
          · unfold gridConfidence
            apply (div_lt_iff₀ (by positivity)).2
            norm_num only [Nat.cast_add, Nat.cast_one, one_mul]
            linarith only [hk, hξ.2]
        obtain ⟨En, hEn, hpn, hnorm⟩ := hUniform baseδ (fun n => gridConfidence ρ ξ n)
          hRealizable hScale n hn hValid
        refine ⟨En ∩ sampleZeroEvent V P sample,
          hEn.inter (sampleZeroEvent_measurable V P sample), ?_, ?_⟩
        · have heq : (En ∩ sampleZeroEvent V P sample : Set Ω) =ᵐ[P] En := by
            filter_upwards [sampleZeroEvent_ae V P sample] with ω hω
            exact propext ⟨fun h => h.1, fun h => ⟨h, hω⟩⟩
          rwa [measureReal_congr heq]
        · intro ω hω
          exact ⟨hω.2, hnorm ω hω.1⟩
      obtain ⟨Cn, hCn, hNorm⟩ := hUniformNorm
      let Ce := Cl + Cn + 1
      have hCe : 0 < Ce := by dsimp [Ce]; positivity
      have hClCe : Cl ≤ Ce := by dsimp [Ce]; linarith
      have hCnCe : Cn ≤ Ce := by dsimp [Ce]; linarith
      refine ⟨Ce, hCe, ?_⟩
      intro baseδ ξ hξ hRange hRealizable hClose hMSC hBound hCommon hComplexity hScale n hn
      have hρpos : 0 < ρ := by linarith only [hρ.1]
      have hlogden : 0 < Real.log (1 / ρ) :=
        Real.log_pos ((lt_div_iff₀ hρpos).2 (by linarith only [hρ.2]))
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hkpos : 0 < terminalIndex ρ n := by
        apply Nat.ceil_pos.mpr
        exact div_pos (Real.log_pos (by nlinarith only [hn1])) hlogden
      have hk2 : (2 : ℝ) ≤ (terminalIndex ρ n + 1 : ℝ) := by
        exact_mod_cast (show 2 ≤ terminalIndex ρ n + 1 by omega)
      have hValid : gridConfidence ρ ξ n ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor
        · unfold gridConfidence; positivity [hξ.1]
        · unfold gridConfidence
          apply (div_lt_iff₀ (by positivity)).2
          norm_num only [Nat.cast_add, Nat.cast_one, one_mul]
          linarith only [hk2, hξ.2]
      have hbudget : 2 * gridConfidence ρ ξ n ≤ ξ := by
        unfold gridConfidence
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (by positivity)).2
        norm_num only [Nat.cast_add, Nat.cast_one]
        nlinarith only [hk2, hξ.1]
      obtain ⟨El, hEl, hpl, hloss⟩ := hLoss baseδ (fun n => gridConfidence ρ ξ n)
        hRange hClose hScale n hn hValid
      obtain ⟨En, hEn, hpn, hnorm⟩ := hNorm baseδ ξ hξ hRealizable hScale n hn
      let E := El ∩ En
      have hE : MeasurableSet E := hEl.inter hEn
      have hprob : 1 - ξ ≤ P.real E := by
        have hu := measureReal_union_le (μ := P) Elᶜ Enᶜ
        rw [← Set.compl_inter] at hu
        linarith [probReal_add_probReal_compl (μ := P) hEl,
          probReal_add_probReal_compl (μ := P) hEn,
          probReal_add_probReal_compl (μ := P) hE, hValid.1]
      have hd : 0 ≤ baseδ n :=
        (Real.rpow_nonneg (by positivity) _).trans
          ((le_max_right _ _).trans (hScale.1 n hn))
      have hloss' (ω : Ω) (hω : ω ∈ E) (h : V.Hbar.toSubmodule) (hh : h ∈ V.H) :
          (1 / 2 : ℝ) * traePopulationLoss V h - Ce * baseδ n ^ 2 ≤
            traeEmpiricalLoss V P sample split n ω h ∧
          traeEmpiricalLoss V P sample split n ω h ≤
            (5 / 4 : ℝ) * traePopulationLoss V h + Ce * baseδ n ^ 2 := by
        have hb := hloss ω hω.1 h hh
        have hc := mul_le_mul_of_nonneg_right hClCe (sq_nonneg (baseδ n))
        constructor <;> linarith only [hb.1, hb.2, hc]
      refine ⟨E, hE, hprob, ?_⟩
      intro ω hω
      refine ⟨hloss' ω hω, ?_, ?_⟩
      · intro h hh
        exact ((hnorm ω hω.2).2 h hh).trans
          (mul_le_mul_of_nonneg_right hCnCe (by positivity))
      · refine ⟨?_, (hnorm ω hω.2).1⟩
        have hz := (hloss' ω hω (minNormSolution V) hRealizable).2
        simpa only [traePopulationLoss_eq V hRange hClose _ hRealizable,
          sub_self, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
          zero_add] using hz
    · refine ⟨1, zero_lt_one, ?_⟩
      intro baseδ ξ hξ hRange hRealizable hClose hMSC hBound hCommon hComplexity
      exact False.elim (hSetup ⟨hMSC, hBound, hCommon, hComplexity⟩)
  choose Ce hCe hevent using hUniformEvent
  refine ⟨fun tildeδ => R (Ce tildeδ), fun tildeδ => hR _ (hCe tildeδ), ?_⟩
  intro β w₀ hRange hSource hRealizable hClose hMSC hBound hCommon hMinima
  obtain ⟨C, hC, hrates⟩ := hrate β w₀ hRange hSource hRealizable hClose hBound hCommon hMinima
  refine ⟨C, hC, ?_⟩
  intro baseδ baseν δ ν tildeδ κ₀
  let κδ := (κ₀ B c₀ CG Cm).1
  let κν := (κ₀ B c₀ CG Cm).2
  intro hComplexity hInflation hDeterministic ξ hξ hScale n hn
  have hn0 : 0 < n := by have := (le_max_left _ _).trans hn; omega
  have hBase (k : ℕ) (hk : 0 < k) : 0 ≤ baseδ k :=
    (Real.rpow_nonneg (by positivity) _).trans
      ((le_max_right _ _).trans (hScale.1 k hk))
  have hFloor : ∀ k : ℕ, 0 < k → 1 / (k : ℝ) ≤ δ k ^ 2 :=
    trae_calibrated_square_floor baseδ δ tildeδ (fun k => gridConfidence ρ ξ k)
      ν baseν κδ κν (R (Ce tildeδ)) hScale hInflation
  obtain ⟨E, hE, hp, hcomp⟩ := hevent tildeδ baseδ ξ hξ hRange hRealizable
    hClose hMSC hBound hCommon hComplexity hScale n hn0
  exact ⟨E, hE, hp, hrates (Ce tildeδ) (hCe tildeδ) baseδ baseν δ ν κδ κν
    hBase hInflation hDeterministic hFloor n hn E hE hcomp⟩

/-- For [the IV model](hyp:V), [sampling law](hyp:P), [analysis sample](hyp:sample),
[sample split](hyp:split), [grid factor](hyp:ρ), [failure level](hyp:ξ), [boundedness
scale](hyp:B), [source exponent](hyp:β), [accuracy curve](hyp:δ), and [candidate
estimator family](hyp:candidate), [the joint Tikhonov rate property](goal) requires
one positive constant such that every eligible sample size admits a measurable
event of probability at least one minus the failure level carrying both the
selected estimator's prediction and estimation rate bounds.

One positive rate constant works for every eligible sample size, with both
error bounds on the same measurable event at each size. This is a conclusion,
never a separately supplied hypothesis. -/
-- @node: ass:pin-194
noncomputable def PinTikhonovRateJointEvent : Prop :=
  ∃ C > 0, ∀ n : ℕ, traeMinSampleSize B ≤ n → ∃ E : Set Ω, -- @realizes \mathcal E_n(common event for the strong and weak error bounds)
    TRAERateOnEvent (V := V) (P := P) (sample := sample) (split := split)
      (ρ := ρ) (ξ := ξ) (β := β) (δ := δ) (candidate := candidate) (fun _ => E) n C

end Papers.TsAdaptiveEstimationInference
