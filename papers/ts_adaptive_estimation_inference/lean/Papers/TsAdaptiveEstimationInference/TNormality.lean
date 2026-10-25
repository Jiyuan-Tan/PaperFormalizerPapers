module
public import Papers.TsAdaptiveEstimationInference.Helpers.DoublyRobust
public import Papers.TsAdaptiveEstimationInference.Helpers.DRScoreContinuity
public import Papers.TsAdaptiveEstimationInference.Helpers.DRScoreCLT
public import Papers.TsAdaptiveEstimationInference.Helpers.DRBiasRate
public import Papers.TsAdaptiveEstimationInference.Helpers.DREvaluation
public import Papers.TsAdaptiveEstimationInference.TTikhonvRate
public import Papers.TsAdaptiveEstimationInference.Helpers.DRAdaptiveRates
/-! Asymptotic linearity and normality from independent doubly robust evaluation. -/
public section
set_option linter.style.longLine false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter ProbabilityTheory
open scoped Topology
variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]
/-- Suppose [the target functional is continuous](hyp:hTarget), [the grid factor
lies between one-half inclusive and one exclusive](hyp:hρ), and [a family of
primal candidate estimators](hyp:hCandidate) is given together with [primal
localized TRAE concentration](hyp:hBennett_of_gate), [dual localized TRAE
concentration](hyp:hDualBennett_of_gate), [the primal squared-norm comparison](hyp:hNorm_of_gate),
and [the dual squared-norm comparison](hyp:hDualNorm_of_gate). [There is a positive
calibration threshold such that the range and source conditions,
solution realizability, closeness, mean-square
continuity, primal boundedness, primal and dual
common-null-set boundedness, critical-radius control,
scale calibration, attained fitting minima, sufficient
inflation, deterministic accuracy curves,
the joint primal-dual nuisance assumptions, a vanishing valid
confidence sequence, a common primal-dual accuracy scale,
Hölder continuity of the score, the doubly robust rate condition,
an independent evaluation sample, and positive score variance
imply that the root-sample-size-scaled doubly robust estimation error differs
from its centered-score average by a term vanishing in probability and converges
in distribution to a centered normal law with the score variance](goal).

Apply the nuisance rate result separately to the primal and exchanged worlds.
`PrimalDualTRAEHypotheses` supplies each world's own boundedness and localized
loss measurability; the two Bennett inputs refer to those same two worlds. -/
-- @node: thm:normality
theorem dr_asymptotic_normality (V : IVWorld 𝒲 𝒳 𝒵)
    (hTarget : Continuous V.targetFunctional)
    (P : Measure Ω) [IsProbabilityMeasure P] (sample : AnalysisSample V P) (split : SampleSplit)
    (ρ B c₀ CG Cm C γh γq : ℝ) (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1)
    (training : ℕ → MeasurableSpace Ω)
    (baseδ baseν ξseq : ℕ → ℝ) (tildeδh tildeδq : ℕ → ℝ → ℝ)
    (hCandidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule) -- @realizes \hat h(primal candidate family; selected below by traeSelected)
    (qCandidate : ℕ → ℝ → Ω → V.Qbar.toSubmodule) -- @realizes \hat q(dual candidate family; selected below by the exchanged problem)
    (hBennett_of_gate : TRAELocalizedConcentration V)
    (hDualBennett_of_gate : TRAELocalizedConcentration (dualWorld V hTarget))
    (hNorm_of_gate : SquaredNormLocalizedComparison V P sample split)
    (hDualNorm_of_gate : SquaredNormLocalizedComparison (dualWorld V hTarget) P sample split) :
    ∃ required > 0, ∀ (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ),
      ∀ (βh βq : ℝ) (wh : V.Hbar.toSubmodule) (wq : V.Qbar.toSubmodule)
      (δ ν : ℕ → ℝ),
      (hRange : RangeCondition V) →
      (hSource : BetaSourceCondition V βh wh) →
      (hRealizable : H0MemHypothesisClass V) →
      (hClose : ClosenessCondition V) → (hMSC : MeanSquareContinuity V) →
      (hBound : TRAEBoundedness V B) → (hEnvelope : TRAECommonNullSetBoundedness V B) →
      (qCommon : TRAECommonNullSetBoundedness (dualWorld V hTarget) B) → (hComplexity : TRAECriticalRadiusBound V tildeδh) →
      (hScale : TRAEScaleCalibration baseδ tildeδh (fun n => gridConfidence ρ (ξseq n / 2) n)) →
      (hMinima : TRAEMinimaAttained V P sample split ρ hCandidate) →
      (hInflation : CalibratedValidBounds δ ν baseδ baseν (κ₀ B c₀ CG Cm).1 (κ₀ B c₀ CG Cm).2 required) →
      (hDeterministic : CalibrationDeterministic δ ν) →
      (hBoth : PrimalDualTRAEHypotheses V hTarget P sample split ρ B βh βq wh wq
        tildeδh tildeδq δ ν baseδ baseν ξseq required c₀ CG Cm κ₀ hCandidate qCandidate) →
      (hConfidence : ConfidenceSequence ξseq) →
      (hCommon : CommonTRAEScale ρ δ ξseq tildeδh tildeδq) →
      (hScore : ScoreHolderContinuity V C γh γq) →
      (hRate : DoublyRobustRateCondition δ βh βq) →
      (hEvaluation : IndependentEvaluationSample V hTarget P sample split training
        (fun n ω => hCandidate n (traeSelected V P sample split ρ δ hCandidate n ω) ω)
        (fun n ω => qCandidate n (traeSelected (dualWorld V hTarget) P sample split ρ δ qCandidate n ω) ω)) →
      (hVariance : ScoreVariancePositive V hTarget) →
      let statistic := fun (n : ℕ) (ω : Ω) => Real.sqrt n *
        (drEstimator V P sample split n
          (hCandidate n (traeSelected V P sample split ρ δ hCandidate n ω) ω)
          (qCandidate n (traeSelected (dualWorld V hTarget) P sample split ρ δ qCandidate n ω) ω) ω -
          targetValue V)
      TendstoInMeasure P
        (fun n ω => statistic n ω - Real.sqrt n *
          blockAverage V P sample (split.eval n) (centeredScore V hTarget) ω)
        atTop (fun _ => 0) ∧
      TendstoInDistribution statistic atTop (id : ℝ → ℝ) (fun _ => P)
        (gaussianReal 0 (Real.toNNReal (scoreVariance V hTarget))) := by
  classical
  obtain ⟨required, hrequired, hjoint⟩ := dr_adaptive_joint_rate_events V hTarget P sample split
    ρ B c₀ CG Cm baseδ baseν ξseq tildeδh tildeδq hCandidate qCandidate
    hBennett_of_gate hDualBennett_of_gate hNorm_of_gate hDualNorm_of_gate hρ
  refine ⟨required, hrequired, ?_⟩
  intro κ₀
  let κδ := (κ₀ B c₀ CG Cm).1
  let κν := (κ₀ B c₀ CG Cm).2
  intro βh βq wh wq δ ν hRange hSource hRealizable hClose hMSC
    hBound hEnvelope qCommon hComplexity hScale hMinima hInflation hDeterministic
    hBoth hConfidence hCommon hScore hRate hEvaluation hVariance
  obtain ⟨Ch, hCh, Cq, hCq, E, hE, hprob, hrates⟩ :=
    hjoint κ₀ βh βq wh wq δ ν hBoth hEnvelope qCommon hConfidence
  let hhat := fun n ω => hCandidate n (traeSelected V P sample split ρ δ hCandidate n ω) ω
  let qhat := fun n ω => qCandidate n (traeSelected (dualWorld V hTarget) P sample split ρ δ qCandidate n ω) ω
  obtain ⟨_, qRange, _, qSource, _, qReal, _, _, _, _, _, qBound, _⟩ := hBoth
  have hβ : DRSourceDomain βh βq := ⟨hSource.1, qSource.1⟩
  have hξlim : Tendsto (fun n => 2 * ξseq n) atTop (𝓝 0) := by
    simpa using hConfidence.2.2.const_mul 2
  have hδlim := dr_accuracy_tendsto_zero δ βh βq hβ hRate
  have hbias := drScore_root_n_bias_of_rate_events V hTarget P hRange qRange
    hhat qhat E (fun n => 2 * ξseq n) δ βh βq Ch Cq hβ hDeterministic.1
    hCh.le hCq.le hE hprob hξlim hRate (by
      filter_upwards [hrates] with n hn
      intro ω hω
      exact (hn ω hω).2.2)
  have hα (β : ℝ) (hβ : 0 < β) : 0 < interpolationExponent β := by
    unfold interpolationExponent truncatedSource
    exact div_pos (lt_min hβ zero_lt_one) (by positivity)
  have hconsistent := dr_nuisance_consistency_of_rate_events P hhat (minNormSolution V)
    E (fun n => 2 * ξseq n) δ Ch (interpolationExponent βh) hCh.le (hα βh hβ.1)
    hDeterministic.1 hE hprob hξlim hδlim (by
      filter_upwards [hrates] with n hn
      intro ω hω
      exact (hn ω hω).2.2.1)
  have qconsistent := dr_nuisance_consistency_of_rate_events P qhat (dualMinNormSolution V hTarget)
    E (fun n => 2 * ξseq n) δ Cq (interpolationExponent βq) hCq.le (hα βq hβ.2)
    hDeterministic.1 hE hprob hξlim hδlim (by
      filter_upwards [hrates] with n hn
      intro ω hω
      exact (hn ω hω).2.2.2.1)
  have qReal' : dualMinNormSolution V hTarget ∈ V.Q := by
    rwa [H0MemHypothesisClass, dualWorld_solution V hTarget qRange] at qReal
  obtain ⟨energy, henergyNonneg, henergyLimit, henergy⟩ :=
    drScore_energy_envelope_of_rate_events V hTarget B C γh γq βh βq Ch Cq δ
      hBound qBound hScore hβ hCh.le hCq.le hDeterministic.1 hδlim hRealizable
      qReal' hhat qhat E (by
        filter_upwards [hrates] with n hn
        intro ω hω
        obtain ⟨hh, hq, hhr, hqr, _, _⟩ := hn ω hω
        exact ⟨hh, hq, hhr, hqr⟩)
  dsimp only
  let statistic := fun (n : ℕ) (ω : Ω) => Real.sqrt n *
    (drEstimator V P sample split n (hhat n ω) (qhat n ω) ω - targetValue V)
  -- The adaptive rates and root-n bias above reduce normality to independent
  -- evaluation of a coherent jointly measurable score-difference version.
  suffices heval :
      TendstoInMeasure P (fun (n : ℕ) ω => Real.sqrt n *
        (blockAverage V P sample (split.eval n)
          (fun w => drScore V (hhat n ω) (qhat n ω) w -
            drScore V (minNormSolution V) (dualMinNormSolution V hTarget) w) ω -
          ∫ w, drScore V (hhat n ω) (qhat n ω) w -
            drScore V (minNormSolution V) (dualMinNormSolution V hTarget) w ∂V.law))
        atTop (fun _ => 0) ∧ (∀ n, AEMeasurable (statistic n) P) by
    have hlinear := drEstimator_asymptotic_linear_of_remainders V hTarget P sample split
      hRange qRange hhat qhat heval.1 hbias
    exact ⟨hlinear, drEstimator_normality_of_asymptotic_linear V hTarget P sample split
      hRange qRange hVariance statistic heval.2 hlinear⟩
  let d := fun n ω w => drScore V (hhat n ω) (qhat n ω) w -
    drScore V (minNormSolution V) (dualMinNormSolution V hTarget) w
  suffices hversion : ∃ g : ℕ → Ω → 𝒲 → ℝ,
      (∀ n, Measurable[(training n).prod ‹MeasurableSpace 𝒲›]
        (Function.uncurry (g n))) ∧
      (∀ n, ∀ᵐ ω ∂P, g n ω =ᵐ[V.law] d n ω ∧
        ∀ i ∈ split.eval n, g n ω (sample.Z i ω) = d n ω (sample.Z i ω)) by
    obtain ⟨g, hg, hagree⟩ := hversion
    have hgAmbient (n : ℕ) : Measurable (Function.uncurry (g n)) := by
      exact (hg n).comp
        ((measurable_fst.mono le_rfl (hEvaluation n).1).prodMk measurable_snd)
    have havg (n : ℕ) :
        (fun ω => blockAverage V P sample (split.eval n) (g n ω) ω) =ᵐ[P]
        (fun ω => blockAverage V P sample (split.eval n) (d n ω) ω) := by
      filter_upwards [hagree n] with ω hω
      unfold blockAverage
      congr 1
      exact Finset.sum_congr rfl (fun i hi => hω.2 i hi)
    have hcentered := dr_eval_centered_of_ambient_energy_events V P sample split
      training (fun n => (hEvaluation n).1)
      (fun n => dr_eval_indep_training V hTarget P sample split training hhat qhat hEvaluation n)
      g hg E (fun n => 2 * ξseq n) energy henergyNonneg hprob hξlim henergyLimit (by
        filter_upwards [henergy] with n hn
        filter_upwards [hagree n] with ω hω
        intro hmem
        obtain ⟨hLp, hb⟩ := hn ω hmem
        refine ⟨(memLp_congr_ae hω.1).2 hLp, ?_⟩
        have heq : (fun w => g n ω w ^ 2) =ᵐ[V.law] (fun w => d n ω w ^ 2) :=
          hω.1.mono fun w hw => congrArg (fun x : ℝ => x ^ 2) hw
        exact (integral_congr_ae heq).trans_le hb)
    constructor
    · apply hcentered.congr _ Filter.EventuallyEq.rfl
      intro n
      filter_upwards [hagree n, havg n] with ω hω hb
      rw [hb, integral_congr_ae hω.1]
    · intro n
      have hpop : Measurable (drScore V (minNormSolution V) (dualMinNormSolution V hTarget)) := by
        unfold drScore
        exact ((V.measurable_mt _).add (V.measurable_m _)).sub
          (((V.primal_measurable _).comp V.measurable_x).mul
            ((V.dual_measurable _).comp V.measurable_z))
      have hm : Measurable (fun ω => Real.sqrt n *
          (blockAverage V P sample (split.eval n)
            (fun w => g n ω w + drScore V (minNormSolution V) (dualMinNormSolution V hTarget) w) ω -
              targetValue V)) := by
        apply Measurable.const_mul
        apply Measurable.sub_const
        unfold blockAverage
        apply Measurable.const_mul
        exact Finset.measurable_sum _ (fun i _ =>
          ((hgAmbient n).comp (measurable_id.prodMk (sample.meas i))).add
            (hpop.comp (sample.meas i)))
      apply hm.aemeasurable.congr
      filter_upwards [hagree n] with ω hω
      dsimp only [statistic]
      congr 2
      unfold drEstimator blockAverage
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      dsimp only
      rw [hω.2 i hi]
      dsimp only [d, drScore]
      ring
  have hversions := fun n => (hEvaluation n).2.2.2.2
  choose g hg hagree heval using hversions
  refine ⟨g, hg, ?_⟩
  intro n
  filter_upwards [hagree n, heval n] with ω hpop hsample
  exact ⟨hpop, hsample⟩

end Papers.TsAdaptiveEstimationInference
