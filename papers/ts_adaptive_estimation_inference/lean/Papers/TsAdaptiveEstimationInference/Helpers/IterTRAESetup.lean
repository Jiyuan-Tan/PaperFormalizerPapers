module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAECore
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAEFittingConcentration
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAENormConcentration
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAEAnchoredEvents
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAEScalarEvents
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAESelfConcentration
/-! Iterative TRAE common concentration event and its allocated-confidence interface. -/
public section
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 800000
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
/-- Assuming [localized scalar concentration](hyp:hBennett_of_gate),
[anchored concentration](hyp:hAnchored_of_gate), [fixed-center squared-loss concentration](hyp:hFixedSq_of_gate),
[scalar Lipschitz concentration](hyp:hNorm_of_gate), [a grid ratio in $[1/2,1)$](hyp:hρ),
[at least one iteration](hyp:ht), [a positive oracle scale](hyp:hc),
[an oracle multiplier at least two](hyp:hb), [mean-square continuity](hyp:hMSC),
[mean-square continuity of increments](hyp:hIterMSC), [boundedness](hyp:hBound),
[a common almost-sure envelope](hyp:hCommon), and [critical-radius control](hyp:hComplexity),
[there is a positive concentration constant uniform in confidence such that, for
calibrated scales, the range, realizability, closeness, attained-minima and localized
measurability conditions yield three measurable events per iteration-grid pair,
each spending one third of its budget, whose common event has probability at least
one minus the confidence budget, satisfies all iterative concentration comparisons,
and bounds every fitting-sample hypothesis representative by the envelope constant](goal). -/
lemma iter_trae_concentration_event_uniform_confidence_with_bounds
    (hBennett_of_gate : TRAELocalizedConcentration V)
    (hAnchored_of_gate : IterTRAEAnchoredLocalizedConcentration V)
    (hFixedSq_of_gate : IterTRAEFixedCenterSquaredLossConcentration V)
    (hNorm_of_gate : ScalarLipschitzLocalizedConcentration V P sample split)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1)
    (ht : 1 ≤ t) (hc : 0 < c) (hb : 2 ≤ b)
    (hMSC : MeanSquareContinuity V) (hIterMSC : IterMeanSquareContinuity V)
    (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B) (hComplexity : TRAECriticalRadiusBound V tildeδ) :
    ∃ Cevent > 0, ∀ ξ : ℝ, ξ ∈ Set.Ioo (0 : ℝ) 1 →
      TRAEScaleCalibration baseδ tildeδ (fun n => iterGridConfidence ρ ξ n t) →
      ∀ (β : ℝ) (δ : ℕ → ℝ),
      RangeCondition V → H0MemHypothesisClass V → ClosenessCondition V →
      IterRealizableTRAE V ρ c b β t δ →
      TRAEMinimaAttained V P sample split ρ candidate →
      IterTRAEMinimaAttained V P sample split ρ t iter →
      IterTRAELocalizedProcessesMeasurable V B ρ t (fun n => c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))) →
      ∀ n : ℕ, 0 < n →
      ∃ component : Fin t → Fin (terminalIndex ρ n + 1) → Fin 3 → Set Ω,
        (∀ j k a, MeasurableSet (component j k a) ∧
          1 - iterGridConfidence ρ ξ n t / 3 ≤ P.real (component j k a)) ∧
        let E := iterTraeCommonEvent ρ n t component
        MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧ -- @realizes \mathcal E_{n,t}^{\mathrm{IT}}(measurable common event with the full allocated probability)
        IterTRAEConcentrationOn V P sample split ρ c b β t δ baseδ iter n E Cevent ∧
        (∀ ω ∈ E, ∀ i ∈ split.fit n, ∀ h ∈ V.H,
          |primalVersion V h (V.xOf (sample.Z i ω))| ≤ B) := by
  classical
  obtain ⟨D, hD, hdeviation⟩ := trae_calibrated_deviation_at_third_allocation
    V P sample split hBennett_of_gate B tildeδ hBound hCommon hMSC hComplexity
  obtain ⟨Cm, hm⟩ := hIterMSC
  obtain ⟨N, hN, hcoordinates⟩ := trae_increment_input_norms V B Cm hBound hCommon
    (fun f hf k hk => (hm f hf k hk).2)
  let s := 2 * B + 1
  have hs : 0 < s := by dsimp [s]; linarith only [hBound.1]
  have hBs : 2 * B ≤ s := by dsimp [s]; linarith
  -- Anchored vector and scalar concentration are specialized locally below.
  -- The recorded self-center process supplies each actual squared-error event.
  -- Transfer to the original losses uses the simultaneous envelope.
  -- No variational, propagation, discrepancy or stability conclusion is assumed.
  have hremaining : ∃ K > 0,
    ∀ ξ : ℝ, ξ ∈ Set.Ioo (0 : ℝ) 1 →
    TRAEScaleCalibration baseδ tildeδ (fun n => iterGridConfidence ρ ξ n t) →
    ∀ (β : ℝ) (δ : ℕ → ℝ),
      RangeCondition V → H0MemHypothesisClass V → ClosenessCondition V →
      IterRealizableTRAE V ρ c b β t δ →
      TRAEMinimaAttained V P sample split ρ candidate →
      IterTRAEMinimaAttained V P sample split ρ t iter →
      IterTRAELocalizedProcessesMeasurable V B ρ t (fun n => c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))) →
      ∀ n : ℕ, 0 < n →
      ∃ remainder : Fin t → Fin (terminalIndex ρ n + 1) → Fin 2 → Set Ω,
        (∀ j k a, MeasurableSet (remainder j k a) ∧
          1 - iterGridConfidence ρ ξ n t / 3 ≤ P.real (remainder j k a)) ∧
        let R := ⋂ j, ⋂ k, ⋂ a, remainder j k a
        (∀ ω ∈ R, ∀ h ∈ V.H,
          |(primalEmpSq V P sample split n ω h -
              primalEmpSq V P sample split n ω (minNormSolution V)) -
            (‖h‖ ^ 2 - ‖minNormSolution V‖ ^ 2)| ≤
            K * (baseδ n * ‖h - minNormSolution V‖ + baseδ n ^ 2)) ∧
        ∀ (_hOracleDefined : gridValue ρ (terminalIndex ρ n) ≤
            c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))),
        ∀ ω ∈ R, ∀ lam ∈ regGrid ρ n,
          lam ∈ Set.Icc (iterTraeOraclePoint ρ c b β t δ n) 2 →
          ∀ j, 1 ≤ j → j ≤ t →
            (∀ h ∈ V.H, ∀ f ∈ V.F,
              let g := populationIterate V lam j
              let k := projCondExpOp V (minNormSolution V - g)
              |blockAverage V P sample (split.fit n) (fun w => traeIntegrand V h f w - traeIntegrand V g k w) ω -
                ∫ w, traeIntegrand V h f w - traeIntegrand V g k w ∂V.law| ≤
              K * (baseδ n * (inputL2Norm V.law (V.m f - V.m k) +
                inputL2Norm V.law (fun w =>
                  primalVersion V h (V.xOf w) * dualVersion V f (V.zOf w) -
                    primalVersion V g (V.xOf w) * dualVersion V k (V.zOf w)) +
                inputL2Norm V.law (fun w =>
                  dualVersion V f (V.zOf w) - dualVersion V k (V.zOf w))) +
                baseδ n ^ 2)) ∧
            (s ^ 2 * |(blockAverage V P sample (split.fit n)
                  (iterTraeClippedDistance V s (populationIterate V lam j)
                    (populationIterate V lam (j - 1))) ω -
                ∫ w, iterTraeClippedDistance V s (populationIterate V lam j)
                  (populationIterate V lam (j - 1)) w ∂V.law) -
              (blockAverage V P sample (split.fit n)
                  (iterTraeClippedDistance V s (iter n j lam ω)
                    (populationIterate V lam (j - 1))) ω -
                ∫ w, iterTraeClippedDistance V s (iter n j lam ω)
                  (populationIterate V lam (j - 1)) w ∂V.law)| ≤
              K * (baseδ n * ‖iter n j lam ω - populationIterate V lam j‖ + baseδ n ^ 2)) ∧
            (∀ k, 1 ≤ k → k ≤ t →
              s ^ 2 * |blockAverage V P sample (split.fit n)
                  (iterTraeClippedDistance V s (iter n k lam ω)
                    (populationIterate V lam k)) ω -
                ∫ w, iterTraeClippedDistance V s (iter n k lam ω)
                  (populationIterate V lam k) w ∂V.law| ≤
                K * (baseδ n * ‖iter n k lam ω - populationIterate V lam k‖ +
                  baseδ n ^ 2)) := by
      obtain ⟨C0, hC0, hNorm⟩ :=
        iter_trae_squared_norm_at_third_allocation V P sample split
          hNorm_of_gate B tildeδ hBound hCommon hComplexity
      obtain ⟨Ca, hCa, hAnchored⟩ :=
        iter_trae_anchored_iteration_grid_events V P sample split
          hAnchored_of_gate B tildeδ hBound hCommon hComplexity
      -- The fixed-center and squared-error families use the recorded processes
      -- with explicit subdivisions of the same iteration--grid budget.
      have hscalar : ∃ Cs > 0,
        ∀ ξ : ℝ, ξ ∈ Set.Ioo (0 : ℝ) 1 →
        TRAEScaleCalibration baseδ tildeδ (fun n => iterGridConfidence ρ ξ n t) →
        ∀ (β : ℝ) (δ : ℕ → ℝ),
          RangeCondition V → H0MemHypothesisClass V → ClosenessCondition V →
          IterRealizableTRAE V ρ c b β t δ →
          TRAEMinimaAttained V P sample split ρ candidate →
          IterTRAEMinimaAttained V P sample split ρ t iter →
          IterTRAELocalizedProcessesMeasurable V B ρ t (fun n => c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))) →
          ∀ n : ℕ, 0 < n →
          ∃ S : Fin t → Fin (terminalIndex ρ n + 1) → Set Ω,
            (∀ j k, MeasurableSet (S j k) ∧
              1 - iterGridConfidence ρ ξ n t / 6 ≤ P.real (S j k)) ∧
            ∀ (_hOracleDefined : gridValue ρ (terminalIndex ρ n) ≤
                c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))),
            ∀ ω ∈ (⋂ j, ⋂ k, S j k), ∀ lam ∈ regGrid ρ n,
              lam ∈ Set.Icc (iterTraeOraclePoint ρ c b β t δ n) 2 →
              ∀ j, 1 ≤ j → j ≤ t →
                (s ^ 2 * |(blockAverage V P sample (split.fit n)
                      (iterTraeClippedDistance V s (populationIterate V lam j)
                        (populationIterate V lam (j - 1))) ω -
                    ∫ w, iterTraeClippedDistance V s (populationIterate V lam j)
                      (populationIterate V lam (j - 1)) w ∂V.law) -
                  (blockAverage V P sample (split.fit n)
                      (iterTraeClippedDistance V s (iter n j lam ω)
                        (populationIterate V lam (j - 1))) ω -
                    ∫ w, iterTraeClippedDistance V s (iter n j lam ω)
                      (populationIterate V lam (j - 1)) w ∂V.law)| ≤
                  Cs * (baseδ n * ‖iter n j lam ω - populationIterate V lam j‖ + baseδ n ^ 2)) ∧
                (∀ k, 1 ≤ k → k ≤ t →
                  s ^ 2 * |blockAverage V P sample (split.fit n)
                      (iterTraeClippedDistance V s (iter n k lam ω)
                        (populationIterate V lam k)) ω -
                    ∫ w, iterTraeClippedDistance V s (iter n k lam ω)
                      (populationIterate V lam k) w ∂V.law| ≤
                    Cs * (baseδ n * ‖iter n k lam ω - populationIterate V lam k‖ +
                      baseδ n ^ 2)) := by
        obtain ⟨Cf, hCf, hFixedEvents⟩ :=
          iter_trae_fixed_center_iteration_grid_events V P sample split
            hFixedSq_of_gate B s hs hBs tildeδ hBound hCommon hComplexity
        have hself : ∃ Cself > 0,
          ∀ ξ : ℝ, ξ ∈ Set.Ioo (0 : ℝ) 1 →
          TRAEScaleCalibration baseδ tildeδ (fun n => iterGridConfidence ρ ξ n t) →
          ∀ (β : ℝ) (δ : ℕ → ℝ),
            RangeCondition V → H0MemHypothesisClass V → ClosenessCondition V →
            IterRealizableTRAE V ρ c b β t δ →
            TRAEMinimaAttained V P sample split ρ candidate →
            IterTRAEMinimaAttained V P sample split ρ t iter →
            IterTRAELocalizedProcessesMeasurable V B ρ t (fun n => c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))) →
            ∀ n : ℕ, 0 < n →
            ∃ S : Fin t → Fin (terminalIndex ρ n + 1) → Set Ω,
              (∀ j k, MeasurableSet (S j k) ∧
                1 - iterGridConfidence ρ ξ n t / 24 ≤ P.real (S j k)) ∧
              ∀ (_hOracleDefined : gridValue ρ (terminalIndex ρ n) ≤
                  c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))),
              ∀ ω ∈ (⋂ j, ⋂ k, S j k), ∀ lam ∈ regGrid ρ n,
                lam ∈ Set.Icc (iterTraeOraclePoint ρ c b β t δ n) 2 →
                  ∀ k, 1 ≤ k → k ≤ t →
                    s ^ 2 * |blockAverage V P sample (split.fit n)
                        (iterTraeClippedDistance V s (iter n k lam ω)
                          (populationIterate V lam k)) ω -
                      ∫ w, iterTraeClippedDistance V s (iter n k lam ω)
                        (populationIterate V lam k) w ∂V.law| ≤
                      Cself * (baseδ n * ‖iter n k lam ω - populationIterate V lam k‖ +
                        baseδ n ^ 2) := by
          obtain ⟨Cself, hCself, hSelfSq⟩ :=
            iter_trae_self_center_iteration_grid_events V P sample split
              hFixedSq_of_gate B s hs hBs tildeδ hBound hCommon hComplexity
          refine ⟨Cself, hCself, ?_⟩
          intro ξ hξ hScale β δ hRange hRealizable hClose hIterRealizable
            hMinima hIterMinima hProcesses n hn
          have halloc : iterGridConfidence ρ ξ n t ∈ Set.Ioo (0 : ℝ) 1 := by
            have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
            have hkR : (1 : ℝ) ≤ (terminalIndex ρ n + 1 : ℕ) := by
              exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
            have hden : 1 ≤ (t : ℝ) * (terminalIndex ρ n + 1 : ℕ) := by nlinarith
            constructor
            · unfold iterGridConfidence
              positivity [hξ.1]
            · unfold iterGridConfidence
              rw [Nat.cast_mul]
              apply (div_lt_iff₀ (by positivity)).2
              simpa only [one_mul] using hξ.2.trans_le hden
          exact hSelfSq baseδ (fun n => iterGridConfidence ρ ξ n t) hScale
            ρ c b β δ t iter hρ hIterRealizable hIterMinima hProcesses n hn halloc
        obtain ⟨Cself, hCself, hSelfEvents⟩ := hself
        refine ⟨Cf + Cself, by positivity, ?_⟩
        intro ξ hξ hScale β δ hRange hRealizable hClose hIterRealizable
          hMinima hIterMinima hProcesses n hn
        have halloc : iterGridConfidence ρ ξ n t ∈ Set.Ioo (0 : ℝ) 1 := by
          have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
          have hkR : (1 : ℝ) ≤ (terminalIndex ρ n + 1 : ℕ) := by
            exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
          have hden : 1 ≤ (t : ℝ) * (terminalIndex ρ n + 1 : ℕ) := by nlinarith
          constructor
          · unfold iterGridConfidence
            positivity [hξ.1]
          · unfold iterGridConfidence
            rw [Nat.cast_mul]
            apply (div_lt_iff₀ (by positivity)).2
            simpa only [one_mul] using hξ.2.trans_le hden
        obtain ⟨A, hA, hgA⟩ := hFixedEvents baseδ
          (fun n => iterGridConfidence ρ ξ n t) hScale ρ c b β δ t hρ
          hIterRealizable hProcesses n hn halloc
        obtain ⟨S, hS, hgS⟩ := hSelfEvents ξ hξ hScale β δ hRange hRealizable
          hClose hIterRealizable hMinima hIterMinima hProcesses n hn
        refine ⟨fun j k => A j k ∩ S j k, ?_, ?_⟩
        · intro j k
          refine ⟨(hA j k).1.inter (hS j k).1, ?_⟩
          have hpa := probReal_add_probReal_compl (μ := P) (hA j k).1
          have hps := probReal_add_probReal_compl (μ := P) (hS j k).1
          have hpi := probReal_add_probReal_compl (μ := P)
            ((hA j k).1.inter (hS j k).1)
          have hu := measureReal_union_le (μ := P) (A j k)ᶜ (S j k)ᶜ
          rw [← Set.compl_inter] at hu
          change 1 - iterGridConfidence ρ ξ n t / 6 ≤ P.real (A j k ∩ S j k)
          linarith [(hA j k).2, (hS j k).2]
        · intro hOracle ω hω lam hlam hsegment j hj hjt
          have hm : ∀ j k, ω ∈ A j k ∩ S j k := by
            simpa only [Set.mem_iInter] using hω
          have hmA : ω ∈ ⋂ j, ⋂ k, A j k := by
            simp only [Set.mem_iInter]
            exact fun j k => (hm j k).1
          have hmS : ω ∈ ⋂ j, ⋂ k, S j k := by
            simp only [Set.mem_iInter]
            exact fun j k => (hm j k).2
          have hd : 0 ≤ baseδ n :=
            (Real.rpow_nonneg (by positivity) _).trans
              ((le_max_right _ _).trans (hScale.1 n hn))
          constructor
          · have hh := ((hIterMinima n hn lam hlam).1.2 j hj hjt ω).1
            exact (hgA hOracle ω hmA lam hlam hsegment j hj hjt
              (iter n j lam ω) hh).trans
              (mul_le_mul_of_nonneg_right (by linarith : Cf ≤ Cf + Cself)
                (by positivity))
          · intro k hk hkt
            exact (hgS hOracle ω hmS lam hlam hsegment k hk hkt).trans
              (mul_le_mul_of_nonneg_right (by linarith : Cself ≤ Cf + Cself)
                (by positivity))
      obtain ⟨Cs, hCs, hscalar⟩ := hscalar
      let K := C0 + Ca + Cs
      have h0K : C0 ≤ K := by dsimp [K]; linarith
      have haK : Ca ≤ K := by dsimp [K]; linarith
      have hsK : Cs ≤ K := by dsimp [K]; linarith
      refine ⟨K, by dsimp [K]; positivity, ?_⟩
      intro ξ hξ hScale β δ hRange hRealizable hClose hIterRealizable
        hMinima hIterMinima hProcesses n hn
      have halloc : iterGridConfidence ρ ξ n t ∈ Set.Ioo (0 : ℝ) 1 := by
        have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
        have hkR : (1 : ℝ) ≤ (terminalIndex ρ n + 1 : ℕ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
        have hden : 1 ≤ (t : ℝ) * (terminalIndex ρ n + 1 : ℕ) := by nlinarith
        constructor
        · unfold iterGridConfidence
          positivity [hξ.1]
        · unfold iterGridConfidence
          rw [Nat.cast_mul]
          apply (div_lt_iff₀ (by positivity)).2
          simpa only [one_mul] using hξ.2.trans_le hden
      obtain ⟨E0, hE0, hp0, hg0⟩ := hNorm baseδ
        (fun n => iterGridConfidence ρ ξ n t) hRealizable hScale n hn halloc
      obtain ⟨A, hA, hgA⟩ := hAnchored baseδ
        (fun n => iterGridConfidence ρ ξ n t) hScale ρ c b β δ t hρ
        hClose hIterRealizable hProcesses n hn halloc
      obtain ⟨S, hS, hgS⟩ := hscalar ξ hξ hScale β δ hRange hRealizable hClose
        hIterRealizable hMinima hIterMinima hProcesses n hn
      let remainder : Fin t → Fin (terminalIndex ρ n + 1) → Fin 2 → Set Ω :=
        fun j k a => if a = 0 then E0 else A j k ∩ S j k
      have hrem : ∀ j k a, MeasurableSet (remainder j k a) ∧
          1 - iterGridConfidence ρ ξ n t / 3 ≤ P.real (remainder j k a) := by
        intro j k a
        fin_cases a
        · exact ⟨hE0, hp0⟩
        · change MeasurableSet (A j k ∩ S j k) ∧ _
          refine ⟨(hA j k).1.inter (hS j k).1, ?_⟩
          have hpa := probReal_add_probReal_compl (μ := P) (hA j k).1
          have hps := probReal_add_probReal_compl (μ := P) (hS j k).1
          have hpi := probReal_add_probReal_compl (μ := P)
            ((hA j k).1.inter (hS j k).1)
          have hu := measureReal_union_le (μ := P) (A j k)ᶜ (S j k)ᶜ
          rw [← Set.compl_inter] at hu
          change 1 - iterGridConfidence ρ ξ n t / 3 ≤ P.real (A j k ∩ S j k)
          linarith [(hA j k).2, (hS j k).2, halloc.1]
      refine ⟨remainder, hrem, ?_, ?_⟩
      · intro ω hω h hh
        have hm : ω ∈ E0 :=
          Set.mem_iInter.mp (Set.mem_iInter.mp (Set.mem_iInter.mp hω
            (⟨0, by omega⟩ : Fin t)) 0) 0
        apply (hg0 ω hm h hh).trans
        have hd : 0 ≤ baseδ n :=
          (Real.rpow_nonneg (by positivity) _).trans
            ((le_max_right _ _).trans (hScale.1 n hn))
        exact mul_le_mul_of_nonneg_right h0K (by positivity)
      · intro hOracle ω hω lam hlam hsegment j hj hjt
        have hm : ∀ j k a, ω ∈ remainder j k a := by
          simpa only [Set.mem_iInter] using hω
        have hmA : ω ∈ ⋂ j, ⋂ k, A j k := by
          simp only [Set.mem_iInter]
          intro j k
          exact (hm j k 1).1
        have hmS : ω ∈ ⋂ j, ⋂ k, S j k := by
          simp only [Set.mem_iInter]
          intro j k
          exact (hm j k 1).2
        have hd : 0 ≤ baseδ n :=
          (Real.rpow_nonneg (by positivity) _).trans
            ((le_max_right _ _).trans (hScale.1 n hn))
        obtain ⟨hfixed, hself⟩ := hgS hOracle ω hmS lam hlam hsegment j hj hjt
        refine ⟨?_, ?_, ?_⟩
        · intro h hh f hf
          apply (hgA hOracle ω hmA lam hlam hsegment j hj hjt h hh f hf).trans
          apply mul_le_mul_of_nonneg_right haK
          unfold inputL2Norm
          positivity
        · exact hfixed.trans (mul_le_mul_of_nonneg_right hsK (by positivity))
        · intro k hk hkt
          exact (hself k hk hkt).trans (mul_le_mul_of_nonneg_right hsK (by positivity))
  obtain ⟨K, hK, hremaining⟩ := hremaining
  let Cevent := D + 2 * D ^ 2 + 1 + (K + 1) + 2 * (K + 1) ^ 2 + K * (N + 1)
  have hExtra : 0 ≤ K * (N + 1) := by positivity
  have hCevent : 0 < Cevent := by dsimp [Cevent]; positivity
  have hlarge : D + 2 * D ^ 2 + 1 ≤ Cevent := by dsimp [Cevent]; nlinarith only [hD, hK, sq_nonneg D, sq_nonneg K, hExtra]
  have hKC : K ≤ Cevent := by dsimp [Cevent]; nlinarith only [hD, hK, sq_nonneg D, sq_nonneg K, hExtra]
  have hcenterC : (K + 1) + 2 * (K + 1) ^ 2 ≤ Cevent := by dsimp [Cevent]; nlinarith only [hD, hK, sq_nonneg D, sq_nonneg K, hExtra]
  have hINC : K * (N + 1) ≤ Cevent := by
    dsimp [Cevent]
    nlinarith only [hD, hK, sq_nonneg D, sq_nonneg K]
  refine ⟨Cevent, hCevent, ?_⟩
  intro ξ hξ hScale β δ hRange hRealizable hClose hIterRealizable hMinima hIterMinima hProcesses n hn
  have halloc : iterGridConfidence ρ ξ n t ∈ Set.Ioo (0 : ℝ) 1 := by
    have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have hkR : (1 : ℝ) ≤ (terminalIndex ρ n + 1 : ℕ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    have hden : 1 ≤ (t : ℝ) * (terminalIndex ρ n + 1 : ℕ) := by nlinarith
    constructor
    · unfold iterGridConfidence
      positivity [hξ.1]
    · unfold iterGridConfidence
      rw [Nat.cast_mul]
      apply (div_lt_iff₀ (by positivity)).2
      simpa only [one_mul] using hξ.2.trans_le hden
  obtain ⟨Eabs, hEabs, hpabs, habs⟩ :=
    hdeviation baseδ (fun n => iterGridConfidence ρ ξ n t)
      hRange hClose hScale n hn halloc
  obtain ⟨remainder, hrem, hnorm, hincrement⟩ :=
    hremaining ξ hξ hScale β δ hRange hRealizable hClose hIterRealizable hMinima hIterMinima hProcesses n hn
  obtain ⟨Ebound, hEbound, haebound, hbound⟩ :=
    trae_fitting_bounded_event V P sample split B hBound hCommon n
  have hpabsBound : 1 - iterGridConfidence ρ ξ n t / 3 ≤ P.real (Eabs ∩ Ebound) := by
    have heq : (Eabs ∩ Ebound : Set Ω) =ᵐ[P] Eabs := by
      filter_upwards [haebound] with ω hω
      apply propext
      change (ω ∈ Eabs ∧ ω ∈ Ebound) ↔ ω ∈ Eabs
      exact and_iff_left hω
    rw [measureReal_congr heq]
    exact hpabs
  let component : Fin t → Fin (terminalIndex ρ n + 1) → Fin 3 → Set Ω :=
    fun j k => ![Eabs ∩ Ebound, remainder j k 0, remainder j k 1]
  have hcomponent : ∀ j k a, MeasurableSet (component j k a) ∧
      1 - iterGridConfidence ρ ξ n t / 3 ≤ P.real (component j k a) := by
    intro j k a
    fin_cases a
    · exact ⟨hEabs.inter hEbound, hpabsBound⟩
    · exact hrem j k 0
    · exact hrem j k 1
  obtain ⟨hE, hpE⟩ := iterTraeCommonEvent_probability P ρ ξ n t ht component hcomponent
  refine ⟨component, hcomponent, hE, hpE, ?_⟩
  let E := iterTraeCommonEvent ρ n t component
  let R := ⋂ j, ⋂ k, ⋂ a, remainder j k a
  have hsubset (ω : Ω) (hω : ω ∈ E) : ω ∈ Eabs ∧ ω ∈ R := by
    have hmem : ∀ j k a, ω ∈ component j k a := by
      simpa only [E, iterTraeCommonEvent, Set.mem_iInter] using hω
    constructor
    · exact (hmem ⟨0, by omega⟩ 0 0).1
    · simp only [R, Set.mem_iInter]
      intro j k a
      fin_cases a
      · exact hmem j k 1
      · exact hmem j k 2
  have hbounded (ω : Ω) (hω : ω ∈ E) : ∀ i ∈ split.fit n, ∀ h ∈ V.H,
      |primalVersion V h (V.xOf (sample.Z i ω))| ≤ B := by
    have hmem : ∀ j k a, ω ∈ component j k a := by
      simpa only [E, iterTraeCommonEvent, Set.mem_iInter] using hω
    exact (hbound ω (hmem ⟨0, by omega⟩ 0 0).2).2
  have hZero (ω : Ω) (hω : ω ∈ E) : ω ∈ sampleZeroEvent V P sample := by
    have hmem : ∀ j k a, ω ∈ component j k a := by
      simpa only [E, iterTraeCommonEvent, Set.mem_iInter] using hω
    exact (hbound ω (hmem ⟨0, by omega⟩ 0 0).2).1
  have hr : 0 ≤ baseδ n :=
    (Real.rpow_nonneg (by positivity) _).trans
      ((le_max_right _ _).trans (hScale.1 n hn))
  have hDC : D + 2 * D ^ 2 ≤ Cevent := by linarith
  have hDC' : D ≤ Cevent := by nlinarith [sq_nonneg D]
  refine ⟨?_, hbounded⟩
  constructor
  · intro ω hω
    have hm := hsubset ω hω
    have hloss := trae_loss_comparison_of_deviation V P sample split hRange hClose
      n ω (baseδ n) D Cevent hD.le hr hDC (habs ω hm.1)
    have hnorm' := hnorm ω hm.2
    refine ⟨hloss, ?_, ?_⟩
    · intro h hh
      exact (hnorm' h hh).trans (mul_le_mul_of_nonneg_right hKC (by positivity))
    · refine ⟨?_, hZero ω hω⟩
      have hz := (hloss (minNormSolution V) hRealizable).2
      have hpop : traePopulationLoss V (minNormSolution V) = 0 := by
        rw [traePopulationLoss_eq V hRange hClose _ hRealizable]
        simp
      simpa only [hpop, mul_zero, zero_add] using hz
  · intro hOracle ω hω lam hlam hsegment j hj hjt
    have hm := hsubset ω hω
    obtain ⟨hinc, hfixed, hsquared⟩ :=
      hincrement hOracle ω hm.2 lam hlam hsegment j hj hjt
    refine ⟨?_, ?_, ?_⟩
    · intro h hh f hf
      have hb := habs ω hm.1 h hh f hf
      have hc := mul_le_mul_of_nonneg_right hDC'
        (show 0 ≤ baseδ n ^ 2 + baseδ n * ‖f‖ by positivity)
      nlinarith only [hb, hc]
    · intro h hh f hf
      let g := populationIterate V lam j
      let k := projCondExpOp V (minNormSolution V - g)
      have hg : g ∈ V.H := hIterRealizable n hOracle j hj hjt lam hlam hsegment
      have hk : k ∈ V.F := hClose g hg
      have hconvert := trae_increment_remainder_le N K (baseδ n)
        _ _ _ _ _ hN.le hK.le hr (by positivity) (norm_nonneg (f - k))
        (hcoordinates h hh g f hf k hk)
      apply ((hinc h hh f hf).trans hconvert).trans
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hINC
        (show 0 ≤ baseδ n * ‖h - g‖ *
          (eLpNorm (dualVersion V k) ⊤ (V.law.map V.zOf)).toReal +
          baseδ n * ‖f - k‖ + baseδ n ^ 2 by positivity)
    · have hpop (k : ℕ) (hk : 1 ≤ k) (hkt : k ≤ t) :
          populationIterate V lam k ∈ V.H :=
        hIterRealizable n hOracle k hk hkt lam hlam hsegment
      have hfit (k : ℕ) (hk : 1 ≤ k) (hkt : k ≤ t) : iter n k lam ω ∈ V.H :=
        ((hIterMinima n hn lam hlam).1.2 k hk hkt ω).1
      have hcenter : populationIterate V lam (j - 1) = 0 ∨
          populationIterate V lam (j - 1) ∈ V.H := by
        by_cases hz : j - 1 = 0
        · left; simp only [hz, populationIterate]
        · exact Or.inr (hpop _ (by omega) (by omega))
      have hfixedRaw := iter_trae_clipped_center_transfer V P sample split
        s B hs hBs hBound hCommon n ω (hbounded ω hω) (hZero ω hω)
        (iter n j lam ω) (populationIterate V lam j) (populationIterate V lam (j - 1))
        (hfit j hj hjt) (hpop j hj hjt) hcenter
      have hfixedBound :
          |(primalEmpDistanceSq V P sample split n ω (populationIterate V lam j)
                (populationIterate V lam (j - 1)) -
              primalEmpDistanceSq V P sample split n ω (iter n j lam ω)
                (populationIterate V lam (j - 1))) -
            (‖populationIterate V lam j - populationIterate V lam (j - 1)‖ ^ 2 -
              ‖iter n j lam ω - populationIterate V lam (j - 1)‖ ^ 2)| ≤
            K * (baseδ n * ‖iter n j lam ω - populationIterate V lam j‖ + baseδ n ^ 2) := by
        rw [hfixedRaw, abs_mul, abs_of_nonneg (sq_nonneg s)]
        exact hfixed
      have hsquaredBound (k : ℕ) (hk : 1 ≤ k) (hkt : k ≤ t) :
          |primalEmpDistanceSq V P sample split n ω (iter n k lam ω)
              (populationIterate V lam k) - ‖iter n k lam ω - populationIterate V lam k‖ ^ 2| ≤
            K * (baseδ n * ‖iter n k lam ω - populationIterate V lam k‖ + baseδ n ^ 2) := by
        rw [iter_trae_clipped_distance_transfer V P sample split s B hs hBs hBound hCommon
          n ω (hbounded ω hω) (hZero ω hω) _ _ (hfit k hk hkt) (Or.inr (hpop k hk hkt)),
          abs_mul, abs_of_nonneg (sq_nonneg s)]
        exact hsquared k hk hkt
      exact (iter_empirical_center_comparison_of_squared_comparisons V P sample split
        n t j ω K (baseδ n) lam (fun k => iter n k lam ω) hK.le hr hjt
        ((hIterMinima n hn lam hlam).1.1 ω) hsquaredBound hfixedBound).trans
        (mul_le_mul_of_nonneg_right hcenterC (by positivity))


-- @node: iter_trae_concentration_event_uniform_confidence
/-- Under [localized scalar concentration](hyp:hBennett_of_gate),
[anchored concentration](hyp:hAnchored_of_gate), [fixed-center squared-loss concentration](hyp:hFixedSq_of_gate),
[scalar Lipschitz concentration](hyp:hNorm_of_gate), [a grid ratio in $[1/2,1)$](hyp:hρ),
[at least one iteration](hyp:ht), [a positive oracle scale](hyp:hc),
[an oracle multiplier at least two](hyp:hb), [mean-square continuity](hyp:hMSC),
[mean-square continuity of increments](hyp:hIterMSC), [boundedness](hyp:hBound),
[a common almost-sure envelope](hyp:hCommon), and [critical-radius control](hyp:hComplexity),
[one positive constant works for every confidence budget and calibrated scale:
whenever the range, realizability, closeness, attained-minima and localized
measurability conditions hold, three measurable component events per iteration-grid
pair each spend one third of its budget, and their common event has probability
at least one minus the confidence budget and satisfies the iterative concentration comparisons](goal). -/
lemma iter_trae_concentration_event_uniform_confidence
    (hBennett_of_gate : TRAELocalizedConcentration V)
    (hAnchored_of_gate : IterTRAEAnchoredLocalizedConcentration V)
    (hFixedSq_of_gate : IterTRAEFixedCenterSquaredLossConcentration V)
    (hNorm_of_gate : ScalarLipschitzLocalizedConcentration V P sample split)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1)
    (ht : 1 ≤ t) (hc : 0 < c) (hb : 2 ≤ b)
    (hMSC : MeanSquareContinuity V) (hIterMSC : IterMeanSquareContinuity V)
    (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B) (hComplexity : TRAECriticalRadiusBound V tildeδ) :
    ∃ Cevent > 0, ∀ ξ : ℝ, ξ ∈ Set.Ioo (0 : ℝ) 1 →
      TRAEScaleCalibration baseδ tildeδ (fun n => iterGridConfidence ρ ξ n t) →
      ∀ (β : ℝ) (δ : ℕ → ℝ),
      RangeCondition V → H0MemHypothesisClass V → ClosenessCondition V →
      IterRealizableTRAE V ρ c b β t δ →
      TRAEMinimaAttained V P sample split ρ candidate →
      IterTRAEMinimaAttained V P sample split ρ t iter →
      IterTRAELocalizedProcessesMeasurable V B ρ t (fun n => c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))) →
      ∀ n : ℕ, 0 < n →
      ∃ component : Fin t → Fin (terminalIndex ρ n + 1) → Fin 3 → Set Ω,
        (∀ j k a, MeasurableSet (component j k a) ∧
          1 - iterGridConfidence ρ ξ n t / 3 ≤ P.real (component j k a)) ∧
        let E := iterTraeCommonEvent ρ n t component
        MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧ -- @realizes \mathcal E_{n,t}^{\mathrm{IT}}(measurable common event with the full allocated probability)
        IterTRAEConcentrationOn V P sample split ρ c b β t δ baseδ iter n E Cevent := by
  obtain ⟨C, hC, hevent⟩ := iter_trae_concentration_event_uniform_confidence_with_bounds
    V P sample split (ρ := ρ) (B := B) (baseδ := baseδ) (tildeδ := tildeδ)
    (candidate := candidate) (iter := iter) (b := b) (c := c) (t := t)
    hBennett_of_gate hAnchored_of_gate hFixedSq_of_gate hNorm_of_gate hρ ht hc hb hMSC hIterMSC hBound hCommon hComplexity
  refine ⟨C, hC, ?_⟩
  intro ξ hξ hScale β δ hRange hRealizable hClose hIterRealizable hMinima hIterMinima
    hProcesses n hn
  obtain ⟨component, hcomponent, hE, hpE, hcon, _hbounded⟩ :=
    hevent ξ hξ hScale β δ hRange hRealizable hClose hIterRealizable hMinima hIterMinima
      hProcesses n hn
  exact ⟨component, hcomponent, hE, hpE, hcon⟩

/-- Given [localized scalar concentration](hyp:hBennett_of_gate),
[anchored concentration](hyp:hAnchored_of_gate), [fixed-center squared-loss concentration](hyp:hFixedSq_of_gate),
[scalar Lipschitz concentration](hyp:hNorm_of_gate), [a grid ratio in $[1/2,1)$](hyp:hρ),
[a confidence budget strictly between zero and one](hyp:hξ), [at least one iteration](hyp:ht),
[a positive oracle scale](hyp:hc), [an oracle multiplier at least two](hyp:hb),
[mean-square continuity](hyp:hMSC), [mean-square continuity of increments](hyp:hIterMSC),
[boundedness](hyp:hBound), [a common almost-sure envelope](hyp:hCommon),
[critical-radius control](hyp:hComplexity), and [calibration to the iteration-grid budgets](hyp:hScale),
[one positive constant yields three measurable component events per iteration-grid
pair, each spending one third of its budget, whose common event has probability
at least one minus the confidence budget and satisfies all iterative concentration
comparisons, whenever the range, realizability, closeness, attained-minima and
localized measurability conditions hold](goal). -/
-- @node: iter_trae_concentration_event
lemma iter_trae_concentration_event
    (hBennett_of_gate : TRAELocalizedConcentration V)
    (hAnchored_of_gate : IterTRAEAnchoredLocalizedConcentration V)
    (hFixedSq_of_gate : IterTRAEFixedCenterSquaredLossConcentration V)
    (hNorm_of_gate : ScalarLipschitzLocalizedConcentration V P sample split)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (ht : 1 ≤ t) (hc : 0 < c) (hb : 2 ≤ b)
    (hMSC : MeanSquareContinuity V) (hIterMSC : IterMeanSquareContinuity V)
    (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B) (hComplexity : TRAECriticalRadiusBound V tildeδ)
    (hScale : TRAEScaleCalibration baseδ tildeδ (fun n => iterGridConfidence ρ ξ n t)) :
    ∃ Cevent > 0, ∀ (β : ℝ) (δ : ℕ → ℝ),
      RangeCondition V → H0MemHypothesisClass V → ClosenessCondition V →
      IterRealizableTRAE V ρ c b β t δ →
      TRAEMinimaAttained V P sample split ρ candidate →
      IterTRAEMinimaAttained V P sample split ρ t iter →
      IterTRAELocalizedProcessesMeasurable V B ρ t (fun n => c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))) →
      ∀ n : ℕ, 0 < n →
      ∃ component : Fin t → Fin (terminalIndex ρ n + 1) → Fin 3 → Set Ω,
        (∀ j k a, MeasurableSet (component j k a) ∧
          1 - iterGridConfidence ρ ξ n t / 3 ≤ P.real (component j k a)) ∧
        let E := iterTraeCommonEvent ρ n t component
        MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧ -- @realizes \mathcal E_{n,t}^{\mathrm{IT}}(measurable common event with the full allocated probability)
        IterTRAEConcentrationOn V P sample split ρ c b β t δ baseδ iter n E Cevent := by
  obtain ⟨C, hC, hevent⟩ := iter_trae_concentration_event_uniform_confidence
    (hAnchored_of_gate := hAnchored_of_gate)
    (hFixedSq_of_gate := hFixedSq_of_gate) (hNorm_of_gate := hNorm_of_gate)
    (hBennett_of_gate := hBennett_of_gate) V P sample split
    (ρ := ρ) (B := B) (baseδ := baseδ) (tildeδ := tildeδ)
    (candidate := candidate) (iter := iter) (b := b) (c := c) (t := t)
    hρ ht hc hb hMSC hIterMSC hBound hCommon hComplexity
  exact ⟨C, hC, hevent ξ hξ hScale⟩


end Papers.TsAdaptiveEstimationInference
