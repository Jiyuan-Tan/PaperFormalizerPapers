module
public import Papers.TsAdaptiveEstimationInference.Helpers.TRAE
/-! Common TRAE events for confidence sequences, with constants uniform in sample size. -/
public section
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

/-- Assume [localized concentration for the adversarial loss](hyp:hBennett_of_gate),
[the range condition](hyp:hRange), [admissibility of projected residuals as
critics](hyp:hClose), [bounded model classes with envelope B](hyp:hBound),
[boundedness outside one common null set](hyp:hCommon), [mean-square
continuity](hyp:hMSC), [the critical-radius bounds](hyp:hComplexity), and
[scale calibration for the accuracy and confidence allocation](hyp:hScale).
Then [one positive constant gives, at every positive sample size with valid
allocated confidence, measurable forward and reverse comparison events each
of probability at least one minus half that allocation, whose intersection
has probability at least one minus the allocation; uniformly over hypotheses
and critics, the population and empirical adversarial integrands bound each
other with remainder equal to that constant times squared accuracy plus
accuracy times the critic norm](goal). -/
lemma trae_deviations_at_allocation
    (hBennett_of_gate : TRAELocalizedConcentration V)
    (B : ℝ) (δ : ℕ → ℝ) (tildeδ : ℕ → ℝ → ℝ)
    (allocation : ℕ → ℝ)
    (hRange : RangeCondition V) (hClose : ClosenessCondition V)
    (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B) (hMSC : MeanSquareContinuity V)
    (hComplexity : TRAECriticalRadiusBound V tildeδ)
    (hScale : TRAEScaleCalibration δ tildeδ allocation) :
    ∃ C > 0, ∀ n : ℕ, 0 < n → allocation n ∈ Set.Ioo (0 : ℝ) 1 →
      ∃ Eforward Ereverse : Set Ω,
      MeasurableSet Eforward ∧ MeasurableSet Ereverse ∧
      1 - allocation n / 2 ≤ P.real Eforward ∧
      1 - allocation n / 2 ≤ P.real Ereverse ∧
      1 - allocation n ≤ P.real (Eforward ∩ Ereverse) ∧
      (∀ ω ∈ Eforward, ∀ h ∈ V.H, ∀ f ∈ V.F,
        (∫ w, traeIntegrand V h f w ∂V.law) ≤
          blockAverage V P sample (split.fit n) (traeIntegrand V h f) ω +
            C * (δ n ^ 2 + δ n * ‖f‖)) ∧
      (∀ ω ∈ Ereverse, ∀ h ∈ V.H, ∀ f ∈ V.F,
        blockAverage V P sample (split.fit n) (traeIntegrand V h f) ω ≤
          (∫ w, traeIntegrand V h f w ∂V.law) +
            C * (δ n ^ 2 + δ n * ‖f‖)) := by
  let K : ℝ := 1
  have hK : 0 < K := zero_lt_one
  obtain ⟨C₀, hC₀, hBoth⟩ := trae_calibrated_deviation_at_allocation
    V P sample split hBennett_of_gate B tildeδ hBound hCommon hMSC hComplexity
  let Cf := C₀
  let Cr := C₀
  have hCf : 0 < Cf := hC₀
  have hCr : 0 < Cr := hC₀
  let D := K ^ 2 + K
  let C := (Cf + Cr) * D
  have hD : 0 < D := by dsimp [D]; positivity
  have hC : 0 < C := mul_pos (add_pos hCf hCr) hD
  refine ⟨C, hC, ?_⟩
  intro n hn hValid
  have hhalf : allocation n / 2 ∈ Set.Ioo (0 : ℝ) 1 := by
    obtain ⟨ha, hb⟩ := hValid
    constructor <;> linarith
  obtain ⟨Ef, hEf, hpf, hboth⟩ :=
    hBoth δ allocation hRange hClose hScale n hn hValid
  let Er := Ef
  have hEr : MeasurableSet Er := hEf
  have hpr : 1 - allocation n / 2 ≤ P.real Er := hpf
  have hd : 0 ≤ δ n :=
    (show 0 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) by positivity).trans
      ((le_max_right _ _).trans (hScale.1 n hn))
  have hprob : 1 - allocation n ≤ P.real (Ef ∩ Er) := by
    have hu := measureReal_union_le (μ := P) Efᶜ Erᶜ
    rw [← Set.compl_inter] at hu
    linarith [probReal_add_probReal_compl (μ := P) hEf,
      probReal_add_probReal_compl (μ := P) hEr,
      probReal_add_probReal_compl (μ := P) (hEf.inter hEr)]
  have hinflate (f : V.Qbar.toSubmodule) :
      (K * δ n) ^ 2 + K * δ n * ‖f‖ ≤ D * (δ n ^ 2 + δ n * ‖f‖) := by
    change (K * δ n) ^ 2 + K * δ n * ‖(f : Lp ℝ 2 V.law)‖ ≤
      (K ^ 2 + K) * (δ n ^ 2 + δ n * ‖(f : Lp ℝ 2 V.law)‖)
    nlinarith only [mul_nonneg hK.le (sq_nonneg (δ n)),
      mul_nonneg (sq_nonneg K) (mul_nonneg hd (norm_nonneg (f : Lp ℝ 2 V.law)))]
  have hCfC : Cf * D ≤ C := by
    dsimp [C]
    nlinarith [mul_nonneg hCr.le hD.le]
  have hCrC : Cr * D ≤ C := by
    dsimp [C]
    nlinarith [mul_nonneg hCf.le hD.le]
  refine ⟨Ef, Er, hEf, hEr, hpf, hpr, hprob, ?_, ?_⟩
  · intro ω hω h hh f hff
    have hb := (abs_le.mp (hboth ω hω h hh f hff)).1
    have hi := mul_le_mul_of_nonneg_left (hinflate f) hCf.le
    have hc := mul_le_mul_of_nonneg_right hCfC
      (show 0 ≤ δ n ^ 2 + δ n * ‖f‖ by positivity)
    nlinarith only [hb, hi, hc]
  · intro ω hω h hh f hff
    have hb := (abs_le.mp (hboth ω hω h hh f hff)).2
    have hi := mul_le_mul_of_nonneg_left (hinflate f) hCr.le
    have hc := mul_le_mul_of_nonneg_right hCrC
      (show 0 ≤ δ n ^ 2 + δ n * ‖f‖ by positivity)
    nlinarith only [hb, hi, hc]

/-- Assume [localized concentration for the adversarial loss](hyp:hBennett_of_gate),
[localized squared-norm comparisons](hyp:hNorm), [the range condition](hyp:hRange),
[admissibility of the minimum-norm solution](hyp:hRealizable), [admissibility of
projected residuals as critics](hyp:hClose), [mean-square continuity](hyp:hMSC),
[bounded model classes with envelope B](hyp:hBound), [boundedness outside one
common null set](hyp:hCommon), [the critical-radius bounds](hyp:hComplexity),
and [scale calibration for the accuracy and confidence allocation](hyp:hScale).
Then [one positive comparison constant works at every positive sample size
with valid allocated confidence, on a measurable event of probability at least
one minus twice the allocation carrying all the adversarial-loss, squared-norm,
minimum-norm-loss and zero-representative comparisons](goal). -/
lemma trae_common_event_at_allocation
    (hBennett_of_gate : TRAELocalizedConcentration V)
    (B : ℝ) (δ : ℕ → ℝ) (tildeδ : ℕ → ℝ → ℝ) (allocation : ℕ → ℝ)
    (hNorm : SquaredNormLocalizedComparison V P sample split)
    (hRange : RangeCondition V) (hRealizable : H0MemHypothesisClass V)
    (hClose : ClosenessCondition V) (hMSC : MeanSquareContinuity V)
    (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B) (hComplexity : TRAECriticalRadiusBound V tildeδ)
    (hScale : TRAEScaleCalibration δ tildeδ allocation) :
    ∃ C > 0, ∀ n : ℕ, 0 < n → allocation n ∈ Set.Ioo (0 : ℝ) 1 →
      ∃ E : Set Ω, MeasurableSet E ∧ 1 - 2 * allocation n ≤ P.real E ∧
        TRAEComparisonsOn V P sample split δ n E C := by
  obtain ⟨Cf, hCf, hDeviations⟩ := trae_deviations_at_allocation (hBennett_of_gate := hBennett_of_gate) V P sample split 
    B δ tildeδ allocation hRange hClose hBound hCommon hMSC hComplexity hScale
  obtain ⟨Cn, hCn, hNormEvents⟩ := trae_squared_norm_at_allocation V P sample split hNorm B tildeδ δ allocation
    hBound hCommon hRealizable hComplexity hScale
  let C := Cf + 2 * Cf ^ 2 + Cn + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hCfC : Cf + 2 * Cf ^ 2 ≤ C := by dsimp [C]; linarith
  have hCnC : Cn ≤ C := by dsimp [C]; nlinarith [sq_nonneg Cf]
  refine ⟨C, hC, ?_⟩
  intro n hn hValid
  obtain ⟨Ef, Er, hEf, hEr, hpf, hpr, hpair, hforward, hreverse⟩ :=
    hDeviations n hn hValid
  obtain ⟨En, hEn, hpn, hnorm⟩ := hNormEvents n hn hValid
  let E := (Ef ∩ Er) ∩ En
  have hE : MeasurableSet E := (hEf.inter hEr).inter hEn
  have hprob : 1 - 2 * allocation n ≤ P.real E := by
    have hu := measureReal_union_le (μ := P) (Ef ∩ Er)ᶜ Enᶜ
    rw [← Set.compl_inter] at hu
    linarith [probReal_add_probReal_compl (μ := P) (hEf.inter hEr),
      probReal_add_probReal_compl (μ := P) hEn,
      probReal_add_probReal_compl (μ := P) hE]
  have hd : 0 ≤ δ n :=
    (show 0 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) by positivity).trans
      ((le_max_right _ _).trans (hScale.1 n hn))
  have hloss (ω : Ω) (hω : ω ∈ E) (h : V.Hbar.toSubmodule) (hh : h ∈ V.H) :
      (1 / 2 : ℝ) * traePopulationLoss V h - C * δ n ^ 2 ≤
        traeEmpiricalLoss V P sample split n ω h ∧
      traeEmpiricalLoss V P sample split n ω h ≤
        (5 / 4 : ℝ) * traePopulationLoss V h + C * δ n ^ 2 := by
    let r := projCondExpOp V (minNormSolution V - h)
    have hr : r ∈ V.F := hClose h hh
    have : Nonempty V.F := ⟨⟨r, hr⟩⟩
    have hpop : traePopulationLoss V h = ‖r‖ ^ 2 := by
      rw [traePopulationLoss_eq V hRange hClose h hh]
      have heq : projCondExpOp V (h - minNormSolution V) = -r := by
        dsimp [r]
        rw [← map_neg, neg_sub]
      rw [heq, norm_neg]
    have hUpper (f : V.F) :
        blockAverage V P sample (split.fit n) (traeIntegrand V h f) ω ≤
          (5 / 4 : ℝ) * ‖r‖ ^ 2 + C * δ n ^ 2 := by
      have hb := hreverse ω hω.1.2 h hh f f.property
      rw [trae_integrand_mean V hRange] at hb
      have hi : inner ℝ r (f : V.Qbar.toSubmodule) ≤ ‖r‖ * ‖(f : V.Qbar.toSubmodule)‖ :=
        real_inner_le_norm _ _
      have hs1 := sq_nonneg (‖(f : V.Qbar.toSubmodule)‖ - ‖r‖ - Cf * δ n / 2)
      have hs2 := sq_nonneg (‖r‖ / 2 - Cf * δ n)
      have hc := mul_le_mul_of_nonneg_right hCfC (sq_nonneg (δ n))
      change _ ≤ 2 * inner ℝ r (f : V.Qbar.toSubmodule) -
        ‖(f : V.Qbar.toSubmodule)‖ ^ 2 +
        Cf * (δ n ^ 2 + δ n * ‖(f : V.Qbar.toSubmodule)‖) at hb
      nlinarith
    have hbdd : BddAbove (Set.range (fun f : V.F =>
        blockAverage V P sample (split.fit n) (traeIntegrand V h f) ω)) := by
      refine ⟨(5 / 4 : ℝ) * ‖r‖ ^ 2 + C * δ n ^ 2, ?_⟩
      rintro _ ⟨f, rfl⟩
      exact hUpper f
    rw [hpop]
    constructor
    · have hf := hforward ω hω.1.1 h hh r hr
      rw [trae_integrand_mean V hRange] at hf
      change 2 * inner ℝ r r - ‖r‖ ^ 2 ≤ _ at hf
      rw [real_inner_self_eq_norm_sq] at hf
      have hle := le_ciSup hbdd (⟨r, hr⟩ : V.F)
      have hs := sq_nonneg (‖r‖ - Cf * δ n)
      have hc := mul_le_mul_of_nonneg_right hCfC (sq_nonneg (δ n))
      change _ ≤ traeEmpiricalLoss V P sample split n ω h at hle
      nlinarith
    · exact ciSup_le hUpper
  refine ⟨E, hE, hprob, ?_⟩
  intro ω hω
  refine ⟨hloss ω hω, ?_, ?_⟩
  · intro h hh
    exact ((hnorm ω hω.2).2 h hh).trans (mul_le_mul_of_nonneg_right hCnC
      (add_nonneg (mul_nonneg hd (norm_nonneg _)) (sq_nonneg _)))
  · refine ⟨?_, (hnorm ω hω.2).1⟩
    have hz := (hloss ω hω (minNormSolution V) hRealizable).2
    simpa only [traePopulationLoss_eq V hRange hClose _ hRealizable,
      sub_self, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
      zero_add] using hz

end Papers.TsAdaptiveEstimationInference
