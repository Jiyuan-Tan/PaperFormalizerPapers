module
public import Papers.TsAdaptiveEstimationInference.Helpers.TRAE
/-! Confidence subdivision for the iterative h0 squared-norm comparison.
Only forward evaluation of the recorded complexity curve is used.
-/
public section
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory
variable {W X Z Ω : Type*} [MeasurableSpace W] [MeasurableSpace X]
  [MeasurableSpace Z] [MeasurableSpace Ω]
  (V : IVWorld W X Z) (P : Measure Ω) [IsProbabilityMeasure P]
  (sample : AnalysisSample V P) (split : SampleSplit)

/-- Assuming [scalar Lipschitz localized concentration](hyp:hNorm), [model
boundedness](hyp:hBound), [a common null-set envelope](hyp:hCommon), and [the
critical-radius complexity bound](hyp:hComplexity), [one positive constant works
for every calibrated accuracy curve when the minimum-norm solution belongs to
the hypothesis class: at each positive sample size with valid allocation there
is a measurable event of probability at least one minus a third of the allocation,
uniformly bounding the empirical-minus-population difference of squared norms
relative to that solution by the constant times accuracy times distance from the
solution plus squared accuracy](goal). -/
-- @node: iter_trae_squared_norm_at_third_allocation
lemma iter_trae_squared_norm_at_third_allocation
    (hNorm : ScalarLipschitzLocalizedConcentration V P sample split)
    (B : ℝ) (tildeδ : ℕ → ℝ → ℝ)
    (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B)
    (hComplexity : TRAECriticalRadiusBound V tildeδ) :
    ∃ C > 0, ∀ (δ allocation : ℕ → ℝ),
      H0MemHypothesisClass V → TRAEScaleCalibration δ tildeδ allocation →
      ∀ n : ℕ, 0 < n → allocation n ∈ Set.Ioo (0 : ℝ) 1 →
      ∃ E : Set Ω, MeasurableSet E ∧ 1 - allocation n / 3 ≤ P.real E ∧
        ∀ ω ∈ E, ∀ h ∈ V.H,
          |(primalEmpSq V P sample split n ω h -
              primalEmpSq V P sample split n ω (minNormSolution V)) -
            (‖h‖ ^ 2 - ‖minNormSolution V‖ ^ 2)| ≤
            C * (δ n * ‖h - minNormSolution V‖ + δ n ^ 2) := by
  classical
  let forward : ℝ → ℝ := fun ζ => if ζ < 1 / 4 then 4 * ζ else ζ
  let radius : ℕ → ℝ → ℝ := fun n ζ =>
    if ζ ∈ Set.Ioo (0 : ℝ) 1 then
      max (tildeδ n (forward ζ)) (confidenceFloor n ζ) else 0
  have hforward (ζ : ℝ) (hζ : ζ ∈ Set.Ioo (0 : ℝ) 1) :
      forward ζ ∈ Set.Ioo (0 : ℝ) 1 := by
    dsimp [forward]
    split <;> constructor <;> linarith [hζ.1, hζ.2]
  have hcomplex : TRAECriticalRadiusBound V radius := by
    refine ⟨1, zero_lt_one, ?_⟩
    intro n hn ζ hζ
    obtain ⟨_, hp, hm, hf, hh, hdiff⟩ := hComplexity.choose_spec.2 n hn
      (forward ζ) (hforward ζ hζ)
    have hmono : tildeδ n (forward ζ) ≤ radius n ζ := by
      dsimp [radius]
      rw [if_pos hζ]
      exact le_max_left _ _
    refine ⟨?_, criticalRadiusBound_mono _ _ _ _ _ hp hmono,
      criticalRadiusBound_mono _ _ _ _ _ hm hmono,
      criticalRadiusBound_mono _ _ _ _ _ hf hmono,
      criticalRadiusBound_mono _ _ _ _ _ hh hmono,
      criticalRadiusBound_mono _ _ _ _ _ hdiff hmono⟩
    simpa only [radius, if_pos hζ, one_mul] using
      (le_max_right (tildeδ n (forward ζ)) (confidenceFloor n ζ))
  obtain ⟨K, hK, hfloor⟩ := trae_radius_uniform_at_allocation V tildeδ hComplexity
  let M := K + 2
  have hM : 1 ≤ M := by dsimp [M]; linarith
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  obtain ⟨D, hD, hsource⟩ := hNorm inferInstance B radius hBound hCommon hcomplex
  refine ⟨D * (M ^ 2 + M), by positivity, ?_⟩
  intro δ allocation hRealizable hScale
  let allocated : ℕ → ℝ := fun n =>
    if allocation n ∈ Set.Ioo (0 : ℝ) 1 then allocation n / 4 else 1
  have hd (n : ℕ) (hn : 0 < n) : 0 ≤ δ n :=
    (Real.rpow_nonneg (by positivity) _).trans
      ((le_max_right _ _).trans (hScale.1 n hn))
  have hdM (n : ℕ) (hn : 0 < n) : δ n ≤ M * δ n := by
    nlinarith only [hd n hn, hM]
  have hcal : TRAEScaleCalibration (fun n => M * δ n) radius allocated := by
    constructor
    · intro n hn
      apply max_le
      · by_cases hv : allocation n ∈ Set.Ioo (0 : ℝ) 1
        · have hvquarter : allocation n / 4 ∈ Set.Ioo (0 : ℝ) 1 := by
            constructor <;> linarith [hv.1, hv.2]
          have hvhalf : allocation n / 2 ∈ Set.Ioo (0 : ℝ) 1 := by
            constructor <;> linarith [hv.1, hv.2]
          have hfwd : forward (allocation n / 4) = allocation n := by
            dsimp only [forward]
            rw [if_pos (by linarith [hv.2])]
            ring
          simp only [allocated, if_pos hv, radius, if_pos hvquarter, hfwd]
          apply max_le
          · exact ((le_max_left _ _).trans (hScale.1 n hn)).trans (hdM n hn)
          · have hhalf := confidenceFloor_half_le n (allocation n / 2) hn hvhalf
            have hsmall := (le_max_right _ _).trans (hScale.1 n hn)
            have hfirst := (hfloor δ allocation hScale n hn hv).1
            rw [show allocation n / 2 / 2 = allocation n / 4 by ring] at hhalf
            dsimp only [M]
            linarith only [hhalf, hsmall, hfirst, hd n hn]
        · simpa only [allocated, if_neg hv, radius,
            show ¬ (1 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 by simp, if_false] using
              (show 0 ≤ M * δ n by positivity [hd n hn])
      · exact ((le_max_right _ _).trans (hScale.1 n hn)).trans (hdM n hn)
    · simpa using hScale.2.const_mul M
  intro n hn hv
  have hvalid : allocated n ∈ Set.Ioo (0 : ℝ) 1 := by
    dsimp [allocated]
    rw [if_pos hv]
    constructor <;> linarith [hv.1, hv.2]
  obtain ⟨E, hE, hpE, hgood⟩ :=
    hsource (fun n => M * δ n) allocated hRealizable hcal n hn hvalid
  refine ⟨E, hE, ?_, ?_⟩
  · simp only [allocated, if_pos hv] at hpE
    linarith [hv.1]
  · intro ω hω h hh
    apply (hgood ω hω h hh).trans
    have hlinear : M ≤ M ^ 2 + M := by nlinarith only [sq_nonneg M]
    have hsquare : M ^ 2 ≤ M ^ 2 + M := by linarith only [hMpos]
    calc
      _ = D * (M * (δ n * ‖h - minNormSolution V‖) + M ^ 2 * δ n ^ 2) := by ring
      _ ≤ D * ((M ^ 2 + M) * (δ n * ‖h - minNormSolution V‖) +
          (M ^ 2 + M) * δ n ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hD.le
        exact add_le_add (mul_le_mul_of_nonneg_right hlinear (by positivity [hd n hn]))
          (mul_le_mul_of_nonneg_right hsquare (sq_nonneg _))
      _ = _ := by ring

end Papers.TsAdaptiveEstimationInference
