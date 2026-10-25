module
public import Papers.TsAdaptiveEstimationInference.Helpers.DRScoreCLT
public import Papers.TsAdaptiveEstimationInference.Helpers.DRScoreContinuity
public import Papers.TsAdaptiveEstimationInference.Helpers.DRBiasRate
public import Causalean.Mathlib.Probability.IdentDistrib.CenteredSum
public import StatLean.AsymptoticStatistics.ForMathlib.TendstoInMeasureAlgebra
/-! Conditional second-moment control on the independent evaluation block.

The event localization retains convergence in probability of the conditional
energy; it does not require convergence of its unconditional expectation.
-/
public section
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]
  (V : IVWorld 𝒲 𝒳 𝒵)
variable (hTarget : Continuous V.targetFunctional)
variable (P : Measure Ω) [IsProbabilityMeasure P]
  (sample : AnalysisSample V P) (split : SampleSplit)

/-- [At every sample size, the joint distribution of the evaluation
observations is the product of their common population law](goal). -/
-- @node: dr_eval_tuple_law
lemma dr_eval_tuple_law (n : ℕ) :
    P.map (fun ω (i : split.eval n) => sample.Z i ω) =
      Measure.pi (fun _ : split.eval n => V.law) := by
  have hi := sample.indep.precomp
    (show Function.Injective (Subtype.val : split.eval n → ℕ) from Subtype.val_injective)
  have hm := (iIndepFun_iff_map_fun_eq_pi_map
    (fun i : split.eval n => (sample.meas i).aemeasurable)).mp hi
  calc
    _ = Measure.pi (fun i : split.eval n => P.map (sample.Z i)) := hm
    _ = _ := by
      congr with i
      rw [← (sample.identDist i).map_eq, sample.law]

omit [IsProbabilityMeasure P] in
/-- For [estimated primal nuisances indexed by sample size and sample
outcome](hyp:hhat), if [the training information and fitted nuisances satisfy
the independent evaluation sample conditions](hyp:hEvaluation), then [the
training sigma-field is independent of the entire evaluation tuple at every
sample size](goal). -/
-- @node: dr_eval_indep_training
lemma dr_eval_indep_training (training : ℕ → MeasurableSpace Ω)
    (hhat : ℕ → Ω → V.Hbar.toSubmodule) (qhat : ℕ → Ω → V.Qbar.toSubmodule)
    (hEvaluation : IndependentEvaluationSample V hTarget P sample split training hhat qhat)
    (n : ℕ) :
    Indep (training n) (MeasurableSpace.comap
      (fun ω (i : split.eval n) => sample.Z i ω) inferInstance) P := by
  apply (Indep_iff _ _ _).2
  intro A B hA hB
  apply (hEvaluation n).2.2.1 A B hA
  have hle : MeasurableSpace.comap
      (fun ω (i : split.eval n) => sample.Z i ω) inferInstance ≤
      ⨆ i ∈ split.eval n, MeasurableSpace.comap (sample.Z i) inferInstance := by
    rw [MeasurableSpace.comap_process_pi]
    apply iSup_le
    intro i
    exact le_iSup_of_le i.val (le_iSup_of_le i.property le_rfl)
  exact hle _ hB

/-- Suppose [the sample size is positive](hyp:hn), [the training sigma-field
is contained in the ambient sigma-field](hyp:htraining), [training is
independent of the evaluation tuple](hyp:hindep), [g is jointly measurable in
the training information and a population observation](hyp:hg), and [each
training-specific function g is square integrable under the population
law](hyp:hLp). Then [the expected square of the centered evaluation average
of g multiplied by the square root of sample size is at most the expectation
of its training-specific population second moment](goal). -/
-- @node: dr_eval_centered_second_moment
lemma dr_eval_centered_second_moment (n : ℕ) (hn : 0 < n)
    (training : ℕ → MeasurableSpace Ω) (htraining : training n ≤ ‹MeasurableSpace Ω›)
    (hindep : Indep (training n) (MeasurableSpace.comap
      (fun ω (i : split.eval n) => sample.Z i ω) inferInstance) P)
    (g : Ω → 𝒲 → ℝ)
    (hg : Measurable[(training n).prod ‹MeasurableSpace 𝒲›] (Function.uncurry g))
    (hLp : ∀ ω, MemLp (g ω) 2 V.law) :
    (∫⁻ ω, ENNReal.ofReal ((Real.sqrt n *
      (blockAverage V P sample (split.eval n) (g ω) ω - ∫ w, g ω w ∂V.law)) ^ 2) ∂P) ≤
      ∫⁻ ω, ENNReal.ofReal (∫ w, g ω w ^ 2 ∂V.law) ∂P := by
  have hsum (ω : Ω) : Real.sqrt n *
      (blockAverage V P sample (split.eval n) (g ω) ω - ∫ w, g ω w ∂V.law) =
      (Real.sqrt n)⁻¹ * ∑ i ∈ split.eval n,
        (g ω (sample.Z i ω) - ∫ w, g ω w ∂V.law) := by
    rw [mul_sub, dr_eval_normalized_sum, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul, split.card_eval]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hs : (Real.sqrt n) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
    have hs' : Real.sqrt n ≠ 0 := by positivity
    field_simp
    rw [hs]
    ring
  simp_rw [hsum]
  have hb := Causalean.Mathlib.iid_centered_sum_sq_lintegral_le
    (split.eval n) (by simpa only [split.card_eval] using hn)
    sample.Z (fun i _ => sample.meas i) (training n) htraining hindep
    (dr_eval_tuple_law V P sample split n) g hg hLp
  simp only [split.card_eval] at hb
  apply hb.trans_eq
  apply lintegral_congr
  intro ω
  simpa only [Real.norm_eq_abs, sq_abs] using
    Causalean.Mathlib.eLpNorm_two_sq_toReal_eq_integral_sq (hLp ω)

/-- Suppose [the sample size is positive](hyp:hn), [the training sigma-field
is contained in the ambient sigma-field](hyp:htraining), [training is
independent of the evaluation tuple](hyp:hindep), [g is jointly measurable in
training and a population observation](hyp:hg), [E is a training-measurable
event](hyp:hE), and [r is nonnegative](hyp:hr). If [g is square integrable for
each training outcome in E](hyp:hLp) and [its population second moment is at
most r on E](hyp:henergy), then [the integral over E of the squared centered
evaluation average multiplied by sample size is at most r](goal). -/
-- @node: dr_eval_centered_second_moment_on_event
lemma dr_eval_centered_second_moment_on_event (n : ℕ) (hn : 0 < n)
    (training : ℕ → MeasurableSpace Ω) (htraining : training n ≤ ‹MeasurableSpace Ω›)
    (hindep : Indep (training n) (MeasurableSpace.comap
      (fun ω (i : split.eval n) => sample.Z i ω) inferInstance) P)
    (g : Ω → 𝒲 → ℝ)
    (hg : Measurable[(training n).prod ‹MeasurableSpace 𝒲›] (Function.uncurry g))
    (E : Set Ω) (hE : MeasurableSet[training n] E) (r : ℝ) (hr : 0 ≤ r)
    (hLp : ∀ ω ∈ E, MemLp (g ω) 2 V.law)
    (henergy : ∀ ω ∈ E, (∫ w, g ω w ^ 2 ∂V.law) ≤ r) :
    (∫⁻ ω in E, ENNReal.ofReal ((Real.sqrt n *
      (blockAverage V P sample (split.eval n) (g ω) ω - ∫ w, g ω w ∂V.law)) ^ 2) ∂P) ≤
      ENNReal.ofReal r := by
  classical
  let gt : Ω → 𝒲 → ℝ := fun ω w => if ω ∈ E then g ω w else 0
  have hgt : Measurable[(training n).prod ‹MeasurableSpace 𝒲›]
      (Function.uncurry gt) := by
    exact Measurable.ite (hE.preimage measurable_fst) hg measurable_const
  have hgtLp : ∀ ω, MemLp (gt ω) 2 V.law := by
    intro ω
    by_cases hω : ω ∈ E
    · simpa only [gt, if_pos hω] using hLp ω hω
    · simp only [gt, if_neg hω]
      exact memLp_const 0
  have hb := dr_eval_centered_second_moment V P sample split n hn
    training htraining hindep gt hgt hgtLp
  have hright : (∫⁻ ω, ENNReal.ofReal (∫ w, gt ω w ^ 2 ∂V.law) ∂P) ≤
      ENNReal.ofReal r := by
    calc
      _ ≤ ∫⁻ _ω : Ω, ENNReal.ofReal r ∂P := by
        apply lintegral_mono
        intro ω
        apply ENNReal.ofReal_le_ofReal
        by_cases hω : ω ∈ E
        · simpa only [gt, if_pos hω] using henergy ω hω
        · simpa only [gt, if_neg hω, zero_pow (by decide : 2 ≠ 0), integral_zero]
            using hr
      _ = _ := by simp
  have hEA : MeasurableSet E := htraining _ hE
  calc
    _ = ∫⁻ ω, ENNReal.ofReal ((Real.sqrt n *
        (blockAverage V P sample (split.eval n) (gt ω) ω - ∫ w, gt ω w ∂V.law)) ^ 2) ∂P := by
      rw [← lintegral_indicator hEA _]
      apply lintegral_congr
      intro ω
      by_cases hω : ω ∈ E
      · simp only [Set.indicator_of_mem hω, gt, if_pos hω]
      · simp [gt, hω, blockAverage]
    _ ≤ _ := hb.trans hright

/-- Suppose [the sample size is positive](hyp:hn), [the training sigma-field
is contained in the ambient sigma-field](hyp:htraining), [training is
independent of the evaluation tuple](hyp:hindep), [g is jointly measurable in
training and a population observation](hyp:hg), [E is a training-measurable
event](hyp:hE), and [r is nonnegative](hyp:hr). If [g is square integrable on
E](hyp:hLp), [its population second moment is at most r on E](hyp:henergy),
and [ε is positive](hyp:hε), then [the probability that the absolute centered
evaluation average multiplied by the square root of sample size is at least
ε is at most the probability of the complement of E plus r divided by ε
squared](goal). -/
-- @node: dr_eval_centered_tail_on_event
lemma dr_eval_centered_tail_on_event (n : ℕ) (hn : 0 < n)
    (training : ℕ → MeasurableSpace Ω) (htraining : training n ≤ ‹MeasurableSpace Ω›)
    (hindep : Indep (training n) (MeasurableSpace.comap
      (fun ω (i : split.eval n) => sample.Z i ω) inferInstance) P)
    (g : Ω → 𝒲 → ℝ)
    (hg : Measurable[(training n).prod ‹MeasurableSpace 𝒲›] (Function.uncurry g))
    (E : Set Ω) (hE : MeasurableSet[training n] E) (r : ℝ) (hr : 0 ≤ r)
    (hLp : ∀ ω ∈ E, MemLp (g ω) 2 V.law)
    (henergy : ∀ ω ∈ E, (∫ w, g ω w ^ 2 ∂V.law) ≤ r)
    (ε : ℝ) (hε : 0 < ε) :
    P.real {ω | ε ≤ |Real.sqrt n *
      (blockAverage V P sample (split.eval n) (g ω) ω - ∫ w, g ω w ∂V.law)|} ≤
      P.real Eᶜ + r / ε ^ 2 := by
  let R : Ω → ℝ := fun ω => Real.sqrt n *
    (blockAverage V P sample (split.eval n) (g ω) ω - ∫ w, g ω w ∂V.law)
  have hgA : Measurable (Function.uncurry g) := hg.comp
    ((measurable_fst.mono le_rfl htraining).prodMk measurable_snd)
  have hR : Measurable R := by
    apply Measurable.const_mul
    apply Measurable.sub
    · unfold blockAverage
      apply Measurable.const_mul
      exact Finset.measurable_sum _ (fun i _ => hgA.comp
        (measurable_id.prodMk (sample.meas i)))
    · exact hgA.stronglyMeasurable.integral_prod_right.measurable
  have htail : MeasurableSet {ω | ε ≤ |R ω|} :=
    measurableSet_le measurable_const hR.abs
  have hsqpos : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hb := dr_eval_centered_second_moment_on_event V P sample split n hn
    training htraining hindep g hg E hE r hr hLp henergy
  have hmark : (P.restrict E) {ω | ε ≤ |R ω|} ≤
      ENNReal.ofReal r / ENNReal.ofReal (ε ^ 2) := by
    calc
      _ ≤ (P.restrict E) {ω | ENNReal.ofReal (ε ^ 2) ≤ ENNReal.ofReal (R ω ^ 2)} := by
        apply measure_mono
        intro ω hω
        apply ENNReal.ofReal_le_ofReal
        have := pow_le_pow_left₀ hε.le hω 2
        simpa only [sq_abs] using this
      _ ≤ (∫⁻ ω in E, ENNReal.ofReal (R ω ^ 2) ∂P) /
          ENNReal.ofReal (ε ^ 2) := meas_ge_le_lintegral_div
        (hR.pow_const 2 |>.ennreal_ofReal.aemeasurable)
        (by positivity) ENNReal.ofReal_ne_top
      _ ≤ _ := by gcongr
  have hEA : MeasurableSet E := htraining _ hE
  have hprob : P {ω | ε ≤ |R ω|} ≤
      P Eᶜ + ENNReal.ofReal r / ENNReal.ofReal (ε ^ 2) := by
    calc
      _ ≤ P (Eᶜ ∪ ({ω | ε ≤ |R ω|} ∩ E)) := measure_mono (by
        intro ω hω
        by_cases hmem : ω ∈ E
        · exact Or.inr ⟨hω, hmem⟩
        · exact Or.inl hmem)
      _ ≤ P Eᶜ + P ({ω | ε ≤ |R ω|} ∩ E) := measure_union_le _ _
      _ ≤ _ := by
        rw [← Measure.restrict_apply htail]
        exact add_le_add le_rfl hmark
  have hfinite : P Eᶜ + ENNReal.ofReal r / ENNReal.ofReal (ε ^ 2) ≠ ⊤ := by
    finiteness
  have ht := ENNReal.toReal_mono hfinite hprob
  rw [ENNReal.toReal_add (measure_ne_top P Eᶜ) (by finiteness),
    ENNReal.toReal_div, ENNReal.toReal_ofReal hr, ENNReal.toReal_ofReal hsqpos.le] at ht
  exact ht

/-- Suppose [each training sigma-field is contained in the ambient
sigma-field](hyp:htraining), [training is independent of its evaluation
tuple](hyp:hindep), [the random functions are jointly measurable in training
and a population observation](hyp:hg), [the events are training
measurable](hyp:hE), [the second-moment bounds are nonnegative](hyp:hr),
[the event probabilities are at least one minus the failure sequence](hyp:hprob),
and [the failure sequence tends to zero](hyp:hξlim) and [the second-moment
bounds tend to zero](hyp:hrlim). If [eventually on these events each random function is square
integrable with population second moment at most its bound](hyp:henergy),
then [the centered evaluation averages multiplied by the square root of
sample size converge to zero in probability](goal). -/
-- @node: dr_eval_centered_tendstoInMeasure_of_energy_events
lemma dr_eval_centered_tendstoInMeasure_of_energy_events
    (training : ℕ → MeasurableSpace Ω)
    (htraining : ∀ n, training n ≤ ‹MeasurableSpace Ω›)
    (hindep : ∀ n, Indep (training n) (MeasurableSpace.comap
      (fun ω (i : split.eval n) => sample.Z i ω) inferInstance) P)
    (g : ℕ → Ω → 𝒲 → ℝ)
    (hg : ∀ n, Measurable[(training n).prod ‹MeasurableSpace 𝒲›]
      (Function.uncurry (g n)))
    (E : ℕ → Set Ω) (hE : ∀ n, MeasurableSet[training n] (E n))
    (ξ r : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n)
    (hprob : ∀ n, 1 - ξ n ≤ P.real (E n))
    (hξlim : Tendsto ξ atTop (𝓝 0)) (hrlim : Tendsto r atTop (𝓝 0))
    (henergy : ∀ᶠ n in atTop, ∀ ω ∈ E n,
      MemLp (g n ω) 2 V.law ∧ (∫ w, g n ω w ^ 2 ∂V.law) ≤ r n) :
    TendstoInMeasure P (fun (n : ℕ) ω => Real.sqrt n *
      (blockAverage V P sample (split.eval n) (g n ω) ω - ∫ w, g n ω w ∂V.law))
      atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  have hlim : Tendsto (fun n => ξ n + r n / ε ^ 2) atTop (𝓝 0) := by
    simpa only [zero_div, add_zero] using hξlim.add (hrlim.div_const (ε ^ 2))
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => measureReal_nonneg) ?_ hlim
  filter_upwards [henergy, eventually_gt_atTop 0] with n hn hnpos
  have hb := dr_eval_centered_tail_on_event V P sample split n hnpos
    training (htraining n) (hindep n) (g n) (hg n) (E n) (hE n) (r n) (hr n)
    (fun ω hω => (hn ω hω).1) (fun ω hω => (hn ω hω).2) ε hε
  have hcompl : P.real (E n)ᶜ ≤ ξ n := by
    linarith only [probReal_add_probReal_compl (μ := P) (htraining n _ (hE n)), hprob n]
  simp only [sub_zero, Real.norm_eq_abs] at ⊢
  exact hb.trans (add_le_add hcompl le_rfl)

/-- Assume [primal TRAE boundedness with envelope B](hyp:hBound), [dual TRAE
boundedness with envelope B](hyp:qBound), [mean-square Hölder continuity of
the score components with constant C and positive exponents](hyp:hScore),
[positive source exponents](hyp:hβ), [a nonnegative primal rate
constant](hyp:hCh), [a nonnegative dual rate constant](hyp:hCq), [nonnegative
accuracy scales](hyp:hδ) [tending to zero](hyp:hδlim), [membership of the
minimum-norm primal solution in its hypothesis class](hyp:hRealizable), and
[membership of the minimum-norm dual solution in its hypothesis
class](hyp:qRealizable). For [estimated primal nuisances](hyp:hhat), if
[eventually on the events both nuisance estimates belong to their classes
and their squared strong errors satisfy the respective interpolation rate
bounds](hyp:hrates), then [there is a nonnegative deterministic sequence
tending to zero that eventually bounds the population second moment of the
estimated-minus-true score on these events, where that score difference is
also square integrable](goal). -/
-- @node: drScore_energy_envelope_of_rate_events
lemma drScore_energy_envelope_of_rate_events
    (B C γh γq βh βq Ch Cq : ℝ) (δ : ℕ → ℝ)
    (hBound : TRAEBoundedness V B) (qBound : TRAEBoundedness (dualWorld V hTarget) B)
    (hScore : ScoreHolderContinuity V C γh γq)
    (hβ : DRSourceDomain βh βq) (hCh : 0 ≤ Ch) (hCq : 0 ≤ Cq)
    (hδ : ∀ n, 0 ≤ δ n) (hδlim : Tendsto δ atTop (𝓝 0))
    (hRealizable : H0MemHypothesisClass V)
    (qRealizable : dualMinNormSolution V hTarget ∈ V.Q)
    (hhat : ℕ → Ω → V.Hbar.toSubmodule) (qhat : ℕ → Ω → V.Qbar.toSubmodule)
    (E : ℕ → Set Ω)
    (hrates : ∀ᶠ n in atTop, ∀ ω ∈ E n,
      hhat n ω ∈ V.H ∧ qhat n ω ∈ V.Q ∧
      ‖hhat n ω - minNormSolution V‖ ^ 2 ≤ Ch * δ n ^ (2 * interpolationExponent βh) ∧
      ‖qhat n ω - dualMinNormSolution V hTarget‖ ^ 2 ≤ Cq * δ n ^ (2 * interpolationExponent βq)) :
    ∃ r : ℕ → ℝ, (∀ n, 0 ≤ r n) ∧ Tendsto r atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, ∀ ω ∈ E n,
        MemLp (fun w => drScore V (hhat n ω) (qhat n ω) w -
          drScore V (minNormSolution V) (dualMinNormSolution V hTarget) w) 2 V.law ∧
        (∫ w, (drScore V (hhat n ω) (qhat n ω) w -
          drScore V (minNormSolution V) (dualMinNormSolution V hTarget) w) ^ 2 ∂V.law) ≤ r n := by
  let ah : ℕ → ℝ := fun n => Real.sqrt Ch * δ n ^ interpolationExponent βh
  let aq : ℕ → ℝ := fun n => Real.sqrt Cq * δ n ^ interpolationExponent βq
  let r : ℕ → ℝ := fun n =>
    3 * |C| * (ah n ^ γh + aq n ^ γq) + 6 * B ^ 2 * (ah n ^ 2 + aq n ^ 2)
  have hα (β : ℝ) (hβ : 0 < β) : 0 < interpolationExponent β := by
    unfold interpolationExponent truncatedSource
    exact div_pos (lt_min hβ zero_lt_one) (by positivity)
  have hah : Tendsto ah atTop (𝓝 0) := by
    have hp := hδlim.rpow_const (Or.inr (hα βh hβ.1).le)
    simpa only [Real.zero_rpow (hα βh hβ.1).ne', mul_zero] using
      hp.const_mul (Real.sqrt Ch)
  have haq : Tendsto aq atTop (𝓝 0) := by
    have hp := hδlim.rpow_const (Or.inr (hα βq hβ.2).le)
    simpa only [Real.zero_rpow (hα βq hβ.2).ne', mul_zero] using
      hp.const_mul (Real.sqrt Cq)
  have hr : Tendsto r atTop (𝓝 0) := by
    have hh := hah.rpow_const (Or.inr hScore.1.le)
    have hq := haq.rpow_const (Or.inr hScore.2.1.le)
    have ht := ((hh.add hq).const_mul (3 * |C|)).add
      (((hah.pow 2).add (haq.pow 2)).const_mul (6 * B ^ 2))
    simpa only [Real.zero_rpow hScore.1.ne', Real.zero_rpow hScore.2.1.ne',
      zero_pow (by decide : 2 ≠ 0), add_zero, mul_zero] using ht
  refine ⟨r, fun n => by
    dsimp [r, ah, aq]
    have hd := hδ n
    positivity, hr, ?_⟩
  filter_upwards [hrates] with n hn
  intro ω hω
  obtain ⟨hh, hq, hhrate, hqrate⟩ := hn ω hω
  obtain ⟨hint, henergy⟩ := drScore_difference_energy V hTarget B C γh γq hBound qBound
    hScore (hhat n ω) (minNormSolution V) (qhat n ω) (dualMinNormSolution V hTarget)
    hh hRealizable hq qRealizable
  refine ⟨(memLp_two_iff_integrable_sq
    ((drScore_integrable V _ _).sub (drScore_integrable V _ _)).aestronglyMeasurable).2 hint, ?_⟩
  have hh' : ‖hhat n ω - minNormSolution V‖ ≤ ah n :=
    dr_norm_rate_of_sq _ (δ n) Ch _ (hδ n) hCh hhrate
  have hq' : ‖qhat n ω - dualMinNormSolution V hTarget‖ ≤ aq n :=
    dr_norm_rate_of_sq _ (δ n) Cq _ (hδ n) hCq hqrate
  apply henergy.trans
  calc
    _ ≤ 3 * |C| * (‖hhat n ω - minNormSolution V‖ ^ γh +
        ‖qhat n ω - dualMinNormSolution V hTarget‖ ^ γq) +
        6 * B ^ 2 * (‖hhat n ω - minNormSolution V‖ ^ 2 +
          ‖qhat n ω - dualMinNormSolution V hTarget‖ ^ 2) := by
      gcongr
      exact le_abs_self C
    _ ≤ r n := by
      dsimp [r]
      gcongr <;> first
        | exact hScore.1.le
        | exact hScore.2.1.le
        | exact hh'
        | exact hq'
        | simpa only [Submodule.coe_sub, Submodule.norm_coe] using hh'
        | simpa only [Submodule.coe_sub, Submodule.norm_coe] using hq'

/-- Suppose [each training sigma-field is contained in the ambient
sigma-field](hyp:htraining), [training is independent of its evaluation
tuple](hyp:hindep), [primal TRAE boundedness holds with envelope B](hyp:hBound),
[dual TRAE boundedness holds with envelope B](hyp:qBound), [the score
components satisfy mean-square Hölder continuity with constant C and positive
exponents](hyp:hScore), [the source exponents are positive](hyp:hβ), [the
primal rate constant is nonnegative](hyp:hCh), [the dual rate constant is
nonnegative](hyp:hCq), and [the accuracy scales are nonnegative](hyp:hδ)
[and tend to zero](hyp:hδlim). Assume [the minimum-norm primal solution
belongs to its hypothesis class](hyp:hRealizable) and [the minimum-norm dual
solution belongs to its hypothesis class](hyp:qRealizable); for [estimated
primal nuisances](hyp:hhat), assume [the estimated-minus-true score is jointly
measurable in training and an observation](hyp:hg), [the events are training
measurable](hyp:hE), [their probabilities are at least one minus the failure
sequence](hyp:hprob), [the failure sequence tends to zero](hyp:hξlim), and
[eventually on these events both estimates belong to their classes and
satisfy the squared strong interpolation rate bounds](hyp:hrates). Then
[the evaluation average of the score difference, centered by its population
mean and multiplied by the square root of sample size, converges to zero in
probability](goal). -/
-- @node: dr_eval_centered_tendstoInMeasure_of_rate_events
lemma dr_eval_centered_tendstoInMeasure_of_rate_events
    (training : ℕ → MeasurableSpace Ω)
    (htraining : ∀ n, training n ≤ ‹MeasurableSpace Ω›)
    (hindep : ∀ n, Indep (training n) (MeasurableSpace.comap
      (fun ω (i : split.eval n) => sample.Z i ω) inferInstance) P)
    (B C γh γq βh βq Ch Cq : ℝ) (ξ δ : ℕ → ℝ)
    (hBound : TRAEBoundedness V B) (qBound : TRAEBoundedness (dualWorld V hTarget) B)
    (hScore : ScoreHolderContinuity V C γh γq)
    (hβ : DRSourceDomain βh βq) (hCh : 0 ≤ Ch) (hCq : 0 ≤ Cq)
    (hδ : ∀ n, 0 ≤ δ n) (hδlim : Tendsto δ atTop (𝓝 0))
    (hRealizable : H0MemHypothesisClass V)
    (qRealizable : dualMinNormSolution V hTarget ∈ V.Q)
    (hhat : ℕ → Ω → V.Hbar.toSubmodule) (qhat : ℕ → Ω → V.Qbar.toSubmodule)
    (hg : ∀ n, Measurable[(training n).prod ‹MeasurableSpace 𝒲›]
      (fun p : Ω × 𝒲 => drScore V (hhat n p.1) (qhat n p.1) p.2 -
        drScore V (minNormSolution V) (dualMinNormSolution V hTarget) p.2))
    (E : ℕ → Set Ω) (hE : ∀ n, MeasurableSet[training n] (E n))
    (hprob : ∀ n, 1 - ξ n ≤ P.real (E n)) (hξlim : Tendsto ξ atTop (𝓝 0))
    (hrates : ∀ᶠ n in atTop, ∀ ω ∈ E n,
      hhat n ω ∈ V.H ∧ qhat n ω ∈ V.Q ∧
      ‖hhat n ω - minNormSolution V‖ ^ 2 ≤ Ch * δ n ^ (2 * interpolationExponent βh) ∧
      ‖qhat n ω - dualMinNormSolution V hTarget‖ ^ 2 ≤ Cq * δ n ^ (2 * interpolationExponent βq)) :
    TendstoInMeasure P (fun (n : ℕ) ω => Real.sqrt n *
      (blockAverage V P sample (split.eval n)
        (fun w => drScore V (hhat n ω) (qhat n ω) w -
          drScore V (minNormSolution V) (dualMinNormSolution V hTarget) w) ω -
        ∫ w, drScore V (hhat n ω) (qhat n ω) w -
          drScore V (minNormSolution V) (dualMinNormSolution V hTarget) w ∂V.law))
      atTop (fun _ => 0) := by
  obtain ⟨r, hr, hrlim, henergy⟩ := drScore_energy_envelope_of_rate_events V hTarget
    B C γh γq βh βq Ch Cq δ hBound qBound hScore hβ hCh hCq hδ hδlim
    hRealizable qRealizable hhat qhat E hrates
  exact dr_eval_centered_tendstoInMeasure_of_energy_events V P sample split
    training htraining hindep _ hg E hE ξ r hr hprob hξlim hrlim henergy

/-- Under [the primal range condition](hyp:hRange) and [the dual range
condition](hyp:hDualRange), consider [estimated primal nuisances](hyp:hhat).
If [the centered evaluation average of the estimated-minus-true score,
multiplied by the square root of sample size, converges to zero in
probability](hyp:hcentered) and [the population score bias multiplied by the
square root of sample size also converges to zero in probability](hyp:hbias),
then [the scaled estimation error differs from the scaled evaluation average
of the centered true score by a quantity converging to zero in probability](goal). -/
-- @node: drEstimator_asymptotic_linear_of_remainders
lemma drEstimator_asymptotic_linear_of_remainders
    (hRange : RangeCondition V) (hDualRange : RangeCondition (dualWorld V hTarget))
    (hhat : ℕ → Ω → V.Hbar.toSubmodule) (qhat : ℕ → Ω → V.Qbar.toSubmodule)
    (hcentered : TendstoInMeasure P (fun (n : ℕ) ω => Real.sqrt n *
      (blockAverage V P sample (split.eval n)
        (fun w => drScore V (hhat n ω) (qhat n ω) w -
          drScore V (minNormSolution V) (dualMinNormSolution V hTarget) w) ω -
        ∫ w, drScore V (hhat n ω) (qhat n ω) w -
          drScore V (minNormSolution V) (dualMinNormSolution V hTarget) w ∂V.law))
      atTop (fun _ => 0))
    (hbias : TendstoInMeasure P (fun (n : ℕ) ω => Real.sqrt n *
      ((∫ w, drScore V (hhat n ω) (qhat n ω) w ∂V.law) - targetValue V))
      atTop (fun _ => 0)) :
    TendstoInMeasure P (fun (n : ℕ) ω => Real.sqrt n *
      (drEstimator V P sample split n (hhat n ω) (qhat n ω) ω - targetValue V) -
        Real.sqrt n * blockAverage V P sample (split.eval n) (centeredScore V hTarget) ω)
      atTop (fun _ => 0) := by
  have htrue : (∫ w, drScore V (minNormSolution V) (dualMinNormSolution V hTarget) w ∂V.law) =
      targetValue V := by
    have ht := drScore_bias_identity V hTarget hRange hDualRange
      (minNormSolution V) (dualMinNormSolution V hTarget)
    simpa only [sub_self, map_zero, inner_zero_left, neg_zero, sub_eq_zero] using ht
  apply (hcentered.add_zero hbias).congr' _ Filter.EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact Filter.Eventually.of_forall fun ω => by
    have he := drEstimator_remainder_decomposition V hTarget P sample split n hn
      (hhat n ω) (qhat n ω) ω
    rw [integral_sub (drScore_integrable V _ _) (drScore_integrable V _ _), htrue] at he
    dsimp only
    rw [integral_sub (drScore_integrable V _ _) (drScore_integrable V _ _), htrue]
    linear_combination -(Real.sqrt n) * he

/-- Under [the primal range condition](hyp:hRange), [the dual range
condition](hyp:hDualRange), and [square integrability and strictly positive
variance of the population score](hyp:hVariance), suppose [each statistic is
almost everywhere measurable](hyp:hmeas) and [its difference from the
evaluation average of the centered true score multiplied by the square root
of sample size converges to zero in probability](hyp:hlinear). Then [the
statistics converge in distribution to a mean-zero Gaussian with the
population score variance](goal). -/
-- @node: drEstimator_normality_of_asymptotic_linear
lemma drEstimator_normality_of_asymptotic_linear
    (hRange : RangeCondition V) (hDualRange : RangeCondition (dualWorld V hTarget))
    (hVariance : ScoreVariancePositive V hTarget)
    (statistic : ℕ → Ω → ℝ) (hmeas : ∀ n, AEMeasurable (statistic n) P)
    (hlinear : TendstoInMeasure P
      (fun n ω => statistic n ω - Real.sqrt n *
        blockAverage V P sample (split.eval n) (centeredScore V hTarget) ω)
      atTop (fun _ => 0)) :
    TendstoInDistribution statistic atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 (Real.toNNReal (scoreVariance V hTarget))) := by
  exact tendstoInDistribution_of_tendstoInMeasure_sub statistic id
    (centeredScore_eval_clt V hTarget P sample split hRange hDualRange hVariance) hlinear hmeas

/-- Assume [each training sigma-field is contained in the ambient
sigma-field](hyp:htraining), [training is independent of its evaluation
tuple](hyp:hindep), [the primal range condition](hyp:hRange), [the dual range
condition](hyp:hDualRange), [primal TRAE boundedness with envelope B](hyp:hBound),
[dual TRAE boundedness with envelope B](hyp:qBound), [mean-square Hölder
continuity of the score components with constant C and positive
exponents](hyp:hScore), [positive source exponents](hyp:hβ), [a nonnegative
primal rate constant](hyp:hCh), [a nonnegative dual rate constant](hyp:hCq),
[nonnegative accuracy scales](hyp:hδ), [the doubly robust little-o accuracy
rate](hyp:hRate), [membership of the minimum-norm primal solution in its
class](hyp:hRealizable), and [membership of the minimum-norm dual solution
in its class](hyp:qRealizable). For [estimated primal nuisances](hyp:hhat),
assume [the estimated-minus-true score is jointly measurable in training and
an observation](hyp:hg), [the events are training measurable](hyp:hE), [their
probabilities are at least one minus the failure sequence](hyp:hprob), [the
failure sequence tends to zero](hyp:hξlim), and [eventually on the events both
estimates belong to their classes, their squared strong errors satisfy the
interpolation rates, and their squared operator errors are bounded by their
constants times the accuracy scale squared](hyp:hrates). Then [the estimation
error multiplied by the square root of sample size equals the similarly
scaled evaluation average of the centered true score up to a remainder
converging to zero in probability](goal). -/
-- @node: drEstimator_asymptotic_linear_of_rate_events
lemma drEstimator_asymptotic_linear_of_rate_events
    (training : ℕ → MeasurableSpace Ω)
    (htraining : ∀ n, training n ≤ ‹MeasurableSpace Ω›)
    (hindep : ∀ n, Indep (training n) (MeasurableSpace.comap
      (fun ω (i : split.eval n) => sample.Z i ω) inferInstance) P)
    (B C γh γq βh βq Ch Cq : ℝ) (ξ δ : ℕ → ℝ)
    (hRange : RangeCondition V) (hDualRange : RangeCondition (dualWorld V hTarget))
    (hBound : TRAEBoundedness V B) (qBound : TRAEBoundedness (dualWorld V hTarget) B)
    (hScore : ScoreHolderContinuity V C γh γq)
    (hβ : DRSourceDomain βh βq) (hCh : 0 ≤ Ch) (hCq : 0 ≤ Cq)
    (hδ : ∀ n, 0 ≤ δ n) (hRate : DoublyRobustRateCondition δ βh βq)
    (hRealizable : H0MemHypothesisClass V)
    (qRealizable : dualMinNormSolution V hTarget ∈ V.Q)
    (hhat : ℕ → Ω → V.Hbar.toSubmodule) (qhat : ℕ → Ω → V.Qbar.toSubmodule)
    (hg : ∀ n, Measurable[(training n).prod ‹MeasurableSpace 𝒲›]
      (fun p : Ω × 𝒲 => drScore V (hhat n p.1) (qhat n p.1) p.2 -
        drScore V (minNormSolution V) (dualMinNormSolution V hTarget) p.2))
    (E : ℕ → Set Ω) (hE : ∀ n, MeasurableSet[training n] (E n))
    (hprob : ∀ n, 1 - ξ n ≤ P.real (E n)) (hξlim : Tendsto ξ atTop (𝓝 0))
    (hrates : ∀ᶠ n in atTop, ∀ ω ∈ E n,
      hhat n ω ∈ V.H ∧ qhat n ω ∈ V.Q ∧
      ‖hhat n ω - minNormSolution V‖ ^ 2 ≤ Ch * δ n ^ (2 * interpolationExponent βh) ∧
      ‖qhat n ω - dualMinNormSolution V hTarget‖ ^ 2 ≤ Cq * δ n ^ (2 * interpolationExponent βq) ∧
      ‖projCondExpOp V (hhat n ω - minNormSolution V)‖ ^ 2 ≤ Ch * δ n ^ 2 ∧
      ‖adjointOp V (qhat n ω - dualMinNormSolution V hTarget)‖ ^ 2 ≤ Cq * δ n ^ 2) :
    TendstoInMeasure P (fun (n : ℕ) ω => Real.sqrt n *
      (drEstimator V P sample split n (hhat n ω) (qhat n ω) ω - targetValue V) -
        Real.sqrt n * blockAverage V P sample (split.eval n) (centeredScore V hTarget) ω)
      atTop (fun _ => 0) := by
  have hcentered := dr_eval_centered_tendstoInMeasure_of_rate_events V hTarget P sample split
    training htraining hindep B C γh γq βh βq Ch Cq ξ δ hBound qBound hScore hβ
    hCh hCq hδ (dr_accuracy_tendsto_zero δ βh βq hβ hRate) hRealizable qRealizable
    hhat qhat hg E hE hprob hξlim (by
      filter_upwards [hrates] with n hn
      intro ω hω
      obtain ⟨hh, hq, hhRate, hqRate, _, _⟩ := hn ω hω
      exact ⟨hh, hq, hhRate, hqRate⟩)
  have hbias := drScore_root_n_bias_of_rate_events V hTarget P hRange hDualRange
    hhat qhat E ξ δ βh βq Ch Cq hβ hδ hCh hCq
    (fun n => htraining n _ (hE n)) hprob hξlim hRate (by
      filter_upwards [hrates] with n hn
      intro ω hω
      exact (hn ω hω).2.2)
  exact drEstimator_asymptotic_linear_of_remainders V hTarget P sample split hRange hDualRange
    hhat qhat hcentered hbias

/-- Suppose [each training sigma-field is contained in the ambient
sigma-field](hyp:htraining), [training is independent of its evaluation
tuple](hyp:hindep), [the random functions are jointly measurable in training
and an observation](hyp:hg), [the second-moment bounds are
nonnegative](hyp:hr), [the event probabilities are at least one minus the
failure sequence](hyp:hprob), [the failure sequence tends to zero](hyp:hξlim),
and [the second-moment bounds tend to zero](hyp:hrlim). If [eventually, almost
everywhere on each event, the random function is square integrable with
population second moment at most its bound](hyp:henergy), then [the centered
evaluation averages multiplied by the square root of sample size converge
to zero in probability](goal). -/
-- @node: dr_eval_centered_of_ambient_energy_events
lemma dr_eval_centered_of_ambient_energy_events
    (training : ℕ → MeasurableSpace Ω)
    (htraining : ∀ n, training n ≤ ‹MeasurableSpace Ω›)
    (hindep : ∀ n, Indep (training n) (MeasurableSpace.comap
      (fun ω (i : split.eval n) => sample.Z i ω) inferInstance) P)
    (g : ℕ → Ω → 𝒲 → ℝ)
    (hg : ∀ n, Measurable[(training n).prod ‹MeasurableSpace 𝒲›]
      (Function.uncurry (g n)))
    (E : ℕ → Set Ω) (ξ r : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n)
    (hprob : ∀ n, 1 - ξ n ≤ P.real (E n))
    (hξlim : Tendsto ξ atTop (𝓝 0)) (hrlim : Tendsto r atTop (𝓝 0))
    (henergy : ∀ᶠ n in atTop, ∀ᵐ ω ∂P, ω ∈ E n →
      MemLp (g n ω) 2 V.law ∧ (∫ w, g n ω w ^ 2 ∂V.law) ≤ r n) :
    TendstoInMeasure P (fun (n : ℕ) ω => Real.sqrt n *
      (blockAverage V P sample (split.eval n) (g n ω) ω - ∫ w, g n ω w ∂V.law))
      atTop (fun _ => 0) := by
  let energy := fun n ω => ∫⁻ w, ENNReal.ofReal (g n ω w ^ 2) ∂V.law
  let F := fun n => {ω | energy n ω ≤ ENNReal.ofReal (r n)}
  have hmeas (n : ℕ) : Measurable[training n] (energy n) := by
    let : MeasurableSpace Ω := training n
    exact (((hg n).pow_const 2).ennreal_ofReal).lintegral_prod_right
  have hF (n : ℕ) : MeasurableSet[training n] (F n) :=
    measurableSet_le (hmeas n) measurable_const
  have hsection (n : ℕ) (ω : Ω) : Measurable (g n ω) := by
    first | fun_prop | exact (hg n).comp (measurable_const.prodMk measurable_id)
  have hbound (n : ℕ) (ω : Ω) (hω : ω ∈ F n) :
      MemLp (g n ω) 2 V.law ∧ (∫ w, g n ω w ^ 2 ∂V.law) ≤ r n := by
    have hi : Integrable (fun w => g n ω w ^ 2) V.law :=
      (lintegral_ofReal_ne_top_iff_integrable
        ((hsection n ω).pow_const 2).aestronglyMeasurable
        (ae_of_all _ fun w => sq_nonneg _)).mp
          (ne_of_lt (hω.trans_lt ENNReal.ofReal_lt_top))
    refine ⟨(memLp_two_iff_integrable_sq (hsection n ω).aestronglyMeasurable).2 hi, ?_⟩
    have heq := ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun w => sq_nonneg _)
    exact (ENNReal.ofReal_le_ofReal_iff (hr n)).mp (heq.trans_le hω)
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  have hlim : Tendsto (fun n => ξ n + r n / ε ^ 2) atTop (𝓝 0) := by
    simpa only [zero_div, add_zero] using hξlim.add (hrlim.div_const (ε ^ 2))
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => measureReal_nonneg) ?_ hlim
  filter_upwards [henergy, eventually_gt_atTop 0] with n hn hnpos
  have hsub : E n ≤ᵐ[P] F n := by
    filter_upwards [hn] with ω hω
    intro hmem
    obtain ⟨hLp, hb⟩ := hω hmem
    change energy n ω ≤ ENNReal.ofReal (r n)
    dsimp only [energy]
    rw [← ofReal_integral_eq_lintegral_ofReal hLp.integrable_sq
      (ae_of_all _ fun w => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hb
  have hp : 1 - ξ n ≤ P.real (F n) := hprob n |>.trans
    (ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsub))
  have hcompl : P.real (F n)ᶜ ≤ ξ n := by
    linarith only [probReal_add_probReal_compl (μ := P) (htraining n _ (hF n)), hp]
  have hb := dr_eval_centered_tail_on_event V P sample split n hnpos
    training (htraining n) (hindep n) (g n) (hg n) (F n) (hF n) (r n) (hr n)
    (fun ω hω => (hbound n ω hω).1) (fun ω hω => (hbound n ω hω).2) ε hε
  simp only [sub_zero, Real.norm_eq_abs] at ⊢
  exact hb.trans (add_le_add hcompl le_rfl)

end Papers.TsAdaptiveEstimationInference
