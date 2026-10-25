module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAEFittingConcentration
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAEAnchoredEvents
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAEScalarEvents
/-! Self-center fitting comparisons at the recorded deterministic population centers. -/
public section
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory
variable {W X Z Ω : Type*} [MeasurableSpace W] [MeasurableSpace X]
  [MeasurableSpace Z] [MeasurableSpace Ω] (V : IVWorld W X Z)

variable (P : Measure Ω) [IsProbabilityMeasure P]
  (sample : AnalysisSample V P) (split : SampleSplit)

/-- Under [fixed-center squared-loss concentration](hyp:hSource), [positive clipping](hyp:hs)
[at least twice the envelope bound](hyp:hBs), [boundedness](hyp:hBound),
[a common almost-sure envelope](hyp:hCommon), and [critical-radius control](hyp:hComplexity),
[one positive constant uniform in calibrated scales gives measurable iteration-grid
events, each with failure probability at most one twenty-fourth of its allocation,
whose intersection bounds the centered clipped squared error of every empirical
iterate about its population iterate by accuracy times their distance plus squared
accuracy, on the oracle segment when the grid floor is covered, population iterates
are realizable, empirical minima are attained, and localized processes are measurable](goal). -/
-- @node: iter_trae_self_center_iteration_grid_events
lemma iter_trae_self_center_iteration_grid_events
    (hSource : IterTRAEFixedCenterSquaredLossConcentration V)
    (B s : ℝ) (hs : 0 < s) (hBs : 2 * B ≤ s) (tildeδ : ℕ → ℝ → ℝ)
    (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B) (hComplexity : TRAECriticalRadiusBound V tildeδ) :
    ∃ C > 0, ∀ (accuracy allocation : ℕ → ℝ),
      TRAEScaleCalibration accuracy tildeδ allocation →
      ∀ (ρ c b β : ℝ) (δ : ℕ → ℝ) (t : ℕ)
      (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule),
      GridDomain ρ → IterRealizableTRAE V ρ c b β t δ →
      IterTRAEMinimaAttained V P sample split ρ t iter →
      IterTRAELocalizedProcessesMeasurable V B ρ t
        (fun n => c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))) →
      ∀ n : ℕ, 0 < n → allocation n ∈ Set.Ioo (0 : ℝ) 1 →
      ∃ S : Fin t → Fin (terminalIndex ρ n + 1) → Set Ω,
        (∀ j k, MeasurableSet (S j k) ∧ 1 - allocation n / 24 ≤ P.real (S j k)) ∧
        ∀ (_hOracle : gridValue ρ (terminalIndex ρ n) ≤
          c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))),
        ∀ ω ∈ (⋂ j, ⋂ k, S j k), ∀ lam ∈ regGrid ρ n,
          lam ∈ Set.Icc (iterTraeOraclePoint ρ c b β t δ n) 2 →
          ∀ j, 1 ≤ j → j ≤ t →
          s ^ 2 * |blockAverage V P sample (split.fit n)
              (iterTraeClippedDistance V s (iter n j lam ω) (populationIterate V lam j)) ω -
            ∫ w, iterTraeClippedDistance V s (iter n j lam ω)
              (populationIterate V lam j) w ∂V.law| ≤
          C * (accuracy n * ‖iter n j lam ω - populationIterate V lam j‖ + accuracy n ^ 2) := by
  classical
  obtain ⟨radius, hcomplex, M, hM, hcal⟩ :=
    iter_trae_quarter_scale_calibration V tildeδ hComplexity
  obtain ⟨radius', hcomplex', L, hL, hcal'⟩ :=
    iter_trae_quarter_scale_calibration V radius hcomplex
  obtain ⟨D, hD, hdev⟩ := iter_trae_self_center_fitting_at_allocation
    V P sample split hSource B s hs hBs radius' hBound hCommon hcomplex'
  let K := L * M
  have hK : 1 ≤ K := by dsimp [K]; nlinarith only [hM, hL]
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  refine ⟨D * (K ^ 2 + K), by positivity, ?_⟩
  intro accuracy allocation hScale ρ c b β δ t iter hρ hIter hMinima hProcesses n hn hv
  let alloc4 := fun n => if allocation n ∈ Set.Ioo (0 : ℝ) 1 then allocation n / 4 else 1
  let alloc16 := fun n => if alloc4 n ∈ Set.Ioo (0 : ℝ) 1 then alloc4 n / 4 else 1
  have hv4 : alloc4 n ∈ Set.Ioo (0 : ℝ) 1 := by
    dsimp [alloc4]; rw [if_pos hv]; constructor <;> linarith [hv.1, hv.2]
  have hv16 : alloc16 n ∈ Set.Ioo (0 : ℝ) 1 := by
    dsimp [alloc16]; rw [if_pos hv4]; constructor <;> linarith [hv4.1, hv4.2]
  have heval : alloc16 n / 2 = allocation n / 32 := by
    dsimp [alloc16]; rw [if_pos hv4]; dsimp [alloc4]; rw [if_pos hv]; ring
  have hscale16 : TRAEScaleCalibration (fun n => L * (M * accuracy n)) radius' alloc16 :=
    hcal' _ _ (hcal _ _ hScale)
  have hd : 0 ≤ accuracy n :=
    (Real.rpow_nonneg (by positivity) _).trans ((le_max_right _ _).trans (hScale.1 n hn))
  let defined := gridValue ρ (terminalIndex ρ n) ≤
    c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))
  let segment := fun lam => lam ∈ Set.Icc (iterTraeOraclePoint ρ c b β t δ n) 2
  have hex : ∀ j : Fin t, ∀ k : Fin (terminalIndex ρ n + 1),
      ∃ E : Set Ω, MeasurableSet E ∧ 1 - allocation n / 24 ≤ P.real E ∧
        ∀ (_hd : defined) (_hs : segment (gridValue ρ k)),
        ∀ ω ∈ E, ∀ h ∈ V.H,
          s ^ 2 * |blockAverage V P sample (split.fit n)
              (iterTraeClippedDistance V s h (populationIterate V (gridValue ρ k) (j + 1))) ω -
            ∫ w, iterTraeClippedDistance V s h (populationIterate V (gridValue ρ k) (j + 1)) w ∂V.law| ≤
          (D * (K ^ 2 + K)) * (accuracy n * ‖h - populationIterate V (gridValue ρ k) (j + 1)‖ + accuracy n ^ 2) := by
    intro j k
    by_cases hdefined : defined
    · by_cases hsegment : segment (gridValue ρ k)
      · have hlam : gridValue ρ k ∈ regGrid ρ n :=
          Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr k.isLt, rfl⟩
        have hprocess := (hProcesses.2 n hn hdefined (j + 1) (by omega) (by omega)
          (gridValue ρ k) hlam hsegment).2
        have hmem := hIter n hdefined (j + 1) (by omega) (by omega)
          (gridValue ρ k) hlam hsegment
        obtain ⟨c', hc', heq, hcross, hlow, hu, hp⟩ :=
          iter_trae_grid_anchor_parameters ρ n t hρ (gridValue ρ k) hlam
        have hdev' := hdev (fun n => L * (M * accuracy n)) alloc16 hscale16 n hn hv16
          ρ c' 2 1 (fun _ => 1) t (j + 1) hρ hc' le_rfl zero_lt_one (by omega) (by omega)
        dsimp only at hdev'
        rw [heq] at hdev'
        obtain ⟨E, hE, hpE, hgood⟩ := hdev' hcross (gridValue ρ k) hlam hlow hu hp hmem
          (by simpa only [iter_trae_scalar_primal_class_eq] using hprocess)
        refine ⟨E, hE, ?_, ?_⟩
        · rw [heval] at hpE
          linarith [hv.1]
        · intro _ _ ω hω h hh
          have he := hgood ω hω h hh
          have hk : K ≤ K ^ 2 + K := by nlinarith only [sq_nonneg K]
          have hk2 : K ^ 2 ≤ K ^ 2 + K := by linarith only [hKpos]
          apply he.trans
          calc
            _ = D * (K * (accuracy n * ‖h - populationIterate V (gridValue ρ k) (j + 1)‖) + K ^ 2 * accuracy n ^ 2) := by
              dsimp [K]; ring
            _ ≤ D * ((K ^ 2 + K) * (accuracy n * ‖h - populationIterate V (gridValue ρ k) (j + 1)‖) +
                (K ^ 2 + K) * accuracy n ^ 2) := by
              apply mul_le_mul_of_nonneg_left _ hD.le
              exact add_le_add (mul_le_mul_of_nonneg_right hk (by positivity))
                (mul_le_mul_of_nonneg_right hk2 (sq_nonneg _))
            _ = _ := by ring
      · refine ⟨Set.univ, MeasurableSet.univ, ?_, ?_⟩
        · simpa using (show 1 - allocation n / 24 ≤ 1 by linarith [hv.1])
        · intro _ h; exact (hsegment h).elim
    · refine ⟨Set.univ, MeasurableSet.univ, ?_, ?_⟩
      · simpa using (show 1 - allocation n / 24 ≤ 1 by linarith [hv.1])
      · intro h; exact (hdefined h).elim
  choose S hS hpS hgS using hex
  refine ⟨S, fun j k => ⟨hS j k, hpS j k⟩, ?_⟩
  intro hOracle ω hω lam hlam hsegment j hj hjt
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hlam
  let ji : Fin t := ⟨j - 1, by omega⟩
  let ki : Fin (terminalIndex ρ n + 1) := ⟨k, Finset.mem_range.mp hk⟩
  have hmem : ω ∈ S ji ki := Set.mem_iInter.mp (Set.mem_iInter.mp hω ji) ki
  have hstep : (ji : ℕ) + 1 = j := by dsimp [ji]; omega
  have hresult := hgS ji ki hOracle hsegment ω hmem _
    (((hMinima n hn _ (Finset.mem_image.mpr ⟨k, hk, rfl⟩)).1.2 j hj hjt ω).1)
  simpa only [hstep] using hresult

end Papers.TsAdaptiveEstimationInference
