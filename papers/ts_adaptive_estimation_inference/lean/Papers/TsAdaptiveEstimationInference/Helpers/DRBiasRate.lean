module
public import Papers.TsAdaptiveEstimationInference.Helpers.DoublyRobust
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
/-! The better-source bias rate and its transfer to convergence in probability. -/
public section

namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter
open scoped Topology

/-- If [both source exponents are positive](hyp:hβ), then [the doubly robust
rate exponent and the mixed strong/weak error exponent are positive, and their
product is one-half](goal). -/
-- @node: dr_rate_exponent_identity
lemma dr_rate_exponent_identity (βh βq : ℝ) (hβ : DRSourceDomain βh βq) :
    0 < drRateExponent βh βq ∧
    0 < 1 + interpolationExponent (betterSource βh βq) ∧
    drRateExponent βh βq * (1 + interpolationExponent (betterSource βh βq)) = 1 / 2 := by
  have hb : 0 < min (betterSource βh βq) 1 :=
    lt_min (hβ.1.trans_le (le_max_left _ _)) zero_lt_one
  change 0 < (1 + min (betterSource βh βq) 1) / (2 + 4 * min (betterSource βh βq) 1) ∧ _
  refine ⟨div_pos (by linarith) (by linarith), ?_, ?_⟩
  · unfold interpolationExponent truncatedSource
    positivity
  · unfold drRateExponent interpolationExponent truncatedSource
    field_simp
    ring

/-- If [both source exponents are positive](hyp:hβ) and [the accuracy scale is
little-o of sample size raised to the negative doubly robust rate
exponent](hyp:hRate), then [the accuracy scale tends to zero](goal). -/
-- @node: dr_accuracy_tendsto_zero
lemma dr_accuracy_tendsto_zero (δ : ℕ → ℝ) (βh βq : ℝ)
    (hβ : DRSourceDomain βh βq) (hRate : DoublyRobustRateCondition δ βh βq) :
    Tendsto δ atTop (𝓝 0) := by
  exact hRate.tendsto_zero_of_tendsto
    ((tendsto_rpow_neg_atTop (dr_rate_exponent_identity βh βq hβ).1).comp
      tendsto_natCast_atTop_atTop)

/-- If [both source exponents are positive](hyp:hβ) and [the accuracy scale is
little-o of sample size raised to the negative doubly robust rate
exponent](hyp:hRate), then [the square root of sample size times the accuracy
scale raised to one plus the interpolation exponent of the better source
tends to zero](goal). -/
-- @node: dr_root_n_accuracy_tendsto_zero
lemma dr_root_n_accuracy_tendsto_zero (δ : ℕ → ℝ) (βh βq : ℝ)
    (hβ : DRSourceDomain βh βq) (hRate : DoublyRobustRateCondition δ βh βq) :
    Tendsto (fun (n : ℕ) => Real.sqrt n * δ n ^
      (1 + interpolationExponent (betterSource βh βq))) atTop (𝓝 0) := by
  obtain ⟨_, hp, hid⟩ := dr_rate_exponent_identity βh βq hβ
  have hpow := hRate.rpow hp
    (Filter.Eventually.of_forall fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have heq (n : ℕ) :
      ((n : ℝ) ^ (-drRateExponent βh βq)) ^
          (1 + interpolationExponent (betterSource βh βq)) = (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    nlinarith only [hid]
  simp_rw [heq] at hpow
  have ht := hpow.tendsto_div_nhds_zero
  simpa only [Real.rpow_neg (Nat.cast_nonneg _), div_inv_eq_mul,
    ← Real.sqrt_eq_rpow, mul_comm] using ht

variable {𝒲 𝒳 𝒵 : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] (V : IVWorld 𝒲 𝒳 𝒵)
variable (hTarget : Continuous V.targetFunctional)

/-- Under [the primal range condition](hyp:hRange) and [the dual range
condition](hyp:hDualRange), suppose [the accuracy scale is nonnegative](hyp:hδ),
[the primal rate constant is nonnegative](hyp:hCh), [the dual rate constant
is nonnegative](hyp:hCq), [the primal strong error is
bounded by its constant times the accuracy scale to its interpolation
exponent](hyp:hh), [the dual strong error satisfies the analogous bound](hyp:hq),
and [the primal operator error is bounded by its constant times the accuracy
scale](hyp:hTh) and [the dual adjoint error is bounded by its constant times
the accuracy scale](hyp:hTq). Then [the
absolute population score bias is at most the product of the two constants
times the accuracy scale raised to one plus the interpolation exponent of the
better source](goal). -/
-- @node: drScore_bias_of_rates
lemma drScore_bias_of_rates (hRange : RangeCondition V)
    (hDualRange : RangeCondition (dualWorld V hTarget))
    (h : V.Hbar.toSubmodule) (q : V.Qbar.toSubmodule)
    (βh βq δ Ch Cq : ℝ) (hδ : 0 ≤ δ) (hCh : 0 ≤ Ch) (hCq : 0 ≤ Cq)
    (hh : ‖h - minNormSolution V‖ ≤ Ch * δ ^ interpolationExponent βh)
    (hq : ‖q - dualMinNormSolution V hTarget‖ ≤ Cq * δ ^ interpolationExponent βq)
    (hTh : ‖projCondExpOp V (h - minNormSolution V)‖ ≤ Ch * δ)
    (hTq : ‖adjointOp V (q - dualMinNormSolution V hTarget)‖ ≤ Cq * δ) :
    |(∫ w, drScore V h q w ∂V.law) - targetValue V| ≤
      Ch * Cq * δ ^ (1 + interpolationExponent (betterSource βh βq)) := by
  have hb := drScore_bias_bounds V hTarget hRange hDualRange h q
  by_cases hz : δ = 0
  · subst δ
    have hz' : ‖adjointOp V (q - dualMinNormSolution V hTarget)‖ = 0 :=
      le_antisymm (by simpa using hTq) (norm_nonneg _)
    rw [hz', mul_zero] at hb
    exact hb.1.trans (by positivity)
  rcases le_total βq βh with hbetter | hbetter
  · rw [betterSource, max_eq_left hbetter]
    calc
      _ ≤ (Ch * δ ^ interpolationExponent βh) * (Cq * δ) :=
        hb.1.trans (mul_le_mul hh hTq (norm_nonneg _) (by positivity))
      _ = _ := by rw [add_comm (1 : ℝ), Real.rpow_add_one hz]; ring
  · rw [betterSource, max_eq_right hbetter]
    calc
      _ ≤ (Cq * δ ^ interpolationExponent βq) * (Ch * δ) :=
        hb.2.trans (mul_le_mul hq hTh (norm_nonneg _) (by positivity))
      _ = _ := by rw [add_comm (1 : ℝ), Real.rpow_add_one hz]; ring

/-- If [the accuracy scale is nonnegative](hyp:hδ), [C is nonnegative](hyp:hC),
and [the squared norm of u is at most C times the accuracy scale raised to twice
α](hyp:hu), then [the norm of u is at most the square root of C times the
accuracy scale raised to α](goal). -/
-- @node: dr_norm_rate_of_sq
lemma dr_norm_rate_of_sq {H : Type*} [SeminormedAddCommGroup H]
    (u : H) (δ C α : ℝ) (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hu : ‖u‖ ^ 2 ≤ C * δ ^ (2 * α)) :
    ‖u‖ ≤ Real.sqrt C * δ ^ α := by
  have hp : (δ ^ α) ^ 2 = δ ^ (2 * α) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ]
    congr 1
    ring
  have hsq : (Real.sqrt C * δ ^ α) ^ 2 = C * δ ^ (2 * α) := by
    rw [mul_pow, Real.sq_sqrt hC, hp]
  have hnonneg : 0 ≤ Real.sqrt C * δ ^ α := by positivity
  nlinarith only [hu, hsq, hnonneg, norm_nonneg u]

/-- If [the events are measurable](hyp:hE), [their probabilities are at least
one minus the failure sequence](hyp:hprob), [the failure sequence tends to
zero](hyp:hξ), [the deterministic error bound tends to zero](hyp:hr), and
[eventually the absolute value of the random quantity is bounded by that
error bound on each event](hyp:hbound), then [the random quantities converge
to zero in probability](goal). -/
-- @node: dr_tendstoInMeasure_of_event_bound
lemma dr_tendstoInMeasure_of_event_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (E : ℕ → Set Ω) (ξ r : ℕ → ℝ)
    (hE : ∀ n, MeasurableSet (E n)) (hprob : ∀ n, 1 - ξ n ≤ P.real (E n))
    (hξ : Tendsto ξ atTop (𝓝 0)) (hr : Tendsto r atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop, ∀ ω ∈ E n, |X n ω| ≤ r n) :
    TendstoInMeasure P X atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => measureReal_nonneg) ?_ hξ
  filter_upwards [hbound, (tendsto_order.1 hr).2 ε hε] with n hn hrn
  have hsub : {ω | ε ≤ ‖X n ω - 0‖} ⊆ (E n)ᶜ := by
    intro ω hω hmem
    have hx := hn ω hmem
    simp only [sub_zero, Real.norm_eq_abs, Set.mem_ofPred_eq] at hω
    linarith
  have hcompl : P.real (E n)ᶜ ≤ ξ n := by
    linarith [probReal_add_probReal_compl (μ := P) (hE n), hprob n]
  exact (measureReal_mono hsub).trans hcompl

/-- Suppose [the rate constant is nonnegative](hyp:hC), [the error exponent is
positive](hyp:hα), [the accuracy scale is nonnegative at every sample
size](hyp:hδ), [the events are measurable](hyp:hE), [their probabilities are
at least one minus the failure sequence](hyp:hprob), [the failure sequence
tends to zero](hyp:hξ), and [the accuracy scale tends to zero](hyp:hδlim).
If [eventually on these events the squared estimation error is bounded by the
rate constant times the accuracy scale raised to twice the error
exponent](hyp:hrate), then [the norm of the estimation error converges to zero
in probability](goal). -/
-- @node: dr_nuisance_consistency_of_rate_events
lemma dr_nuisance_consistency_of_rate_events {Ω H : Type*} [MeasurableSpace Ω]
    [SeminormedAddCommGroup H] (P : Measure Ω) [IsProbabilityMeasure P]
    (u : ℕ → Ω → H) (u₀ : H) (E : ℕ → Set Ω) (ξ δ : ℕ → ℝ)
    (C α : ℝ) (hC : 0 ≤ C) (hα : 0 < α) (hδ : ∀ n, 0 ≤ δ n)
    (hE : ∀ n, MeasurableSet (E n)) (hprob : ∀ n, 1 - ξ n ≤ P.real (E n))
    (hξ : Tendsto ξ atTop (𝓝 0)) (hδlim : Tendsto δ atTop (𝓝 0))
    (hrate : ∀ᶠ n in atTop, ∀ ω ∈ E n, ‖u n ω - u₀‖ ^ 2 ≤ C * δ n ^ (2 * α)) :
    TendstoInMeasure P (fun n ω => ‖u n ω - u₀‖) atTop (fun _ => 0) := by
  have hpow : Tendsto (fun n => δ n ^ α) atTop (𝓝 0) := by
    simpa only [Real.zero_rpow hα.ne'] using hδlim.rpow_const (Or.inr hα.le)
  have hlim : Tendsto (fun n => Real.sqrt C * δ n ^ α) atTop (𝓝 0) := by
    simpa using hpow.const_mul (Real.sqrt C)
  apply dr_tendstoInMeasure_of_event_bound P _ E ξ _ hE hprob hξ hlim
  filter_upwards [hrate] with n hn
  intro ω hω
  rw [abs_of_nonneg (norm_nonneg _)]
  exact dr_norm_rate_of_sq _ (δ n) C α (hδ n) hC (hn ω hω)

/-- Under [the primal range condition](hyp:hRange) and [the dual range
condition](hyp:hDualRange),
consider [a sequence of estimated primal nuisances](hyp:hhat). Assume [positive
source exponents](hyp:hβ), [nonnegative accuracy scales](hyp:hδ), [a nonnegative
primal rate constant](hyp:hCh), [a nonnegative dual rate constant](hyp:hCq), [measurable events](hyp:hE)
[with probabilities at least one minus the failure sequence](hyp:hprob), [a
failure sequence tending to zero](hyp:hξ), and [the doubly robust little-o
accuracy rate](hyp:hRate). If [eventually on these events both squared strong
errors satisfy their interpolation rates and both squared operator errors are
bounded by their constants times the accuracy scale squared](hyp:hrates), then
[the population score bias multiplied by the square root of sample size
converges to zero in probability](goal). -/
-- @node: drScore_root_n_bias_of_rate_events
lemma drScore_root_n_bias_of_rate_events {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hRange : RangeCondition V) (hDualRange : RangeCondition (dualWorld V hTarget))
    (hhat : ℕ → Ω → V.Hbar.toSubmodule) (qhat : ℕ → Ω → V.Qbar.toSubmodule)
    (E : ℕ → Set Ω) (ξ δ : ℕ → ℝ) (βh βq Ch Cq : ℝ)
    (hβ : DRSourceDomain βh βq) (hδ : ∀ n, 0 ≤ δ n)
    (hCh : 0 ≤ Ch) (hCq : 0 ≤ Cq)
    (hE : ∀ n, MeasurableSet (E n)) (hprob : ∀ n, 1 - ξ n ≤ P.real (E n))
    (hξ : Tendsto ξ atTop (𝓝 0)) (hRate : DoublyRobustRateCondition δ βh βq)
    (hrates : ∀ᶠ n in atTop, ∀ ω ∈ E n,
      (‖hhat n ω - minNormSolution V‖ ^ 2 ≤ Ch * δ n ^ (2 * interpolationExponent βh)) ∧
      (‖qhat n ω - dualMinNormSolution V hTarget‖ ^ 2 ≤ Cq * δ n ^ (2 * interpolationExponent βq)) ∧
      (‖projCondExpOp V (hhat n ω - minNormSolution V)‖ ^ 2 ≤ Ch * δ n ^ 2) ∧
      (‖adjointOp V (qhat n ω - dualMinNormSolution V hTarget)‖ ^ 2 ≤ Cq * δ n ^ 2)) :
    TendstoInMeasure P (fun (n : ℕ) ω => Real.sqrt n *
      ((∫ w, drScore V (hhat n ω) (qhat n ω) w ∂V.law) - targetValue V))
      atTop (fun _ => 0) := by
  have hlim := (dr_root_n_accuracy_tendsto_zero δ βh βq hβ hRate).const_mul
    (Real.sqrt Ch * Real.sqrt Cq)
  simp only [mul_zero] at hlim
  apply dr_tendstoInMeasure_of_event_bound P _ E ξ _ hE hprob hξ hlim
  filter_upwards [hrates] with n hn
  intro ω hω
  obtain ⟨hh, hq, hTh, hTq⟩ := hn ω hω
  have hh' := dr_norm_rate_of_sq _ (δ n) Ch _ (hδ n) hCh hh
  have hq' := dr_norm_rate_of_sq _ (δ n) Cq _ (hδ n) hCq hq
  have hTh' : ‖projCondExpOp V (hhat n ω - minNormSolution V)‖ ≤ Real.sqrt Ch * δ n := by
    simpa using dr_norm_rate_of_sq _ (δ n) Ch 1 (hδ n) hCh (by simpa using hTh)
  have hTq' : ‖adjointOp V (qhat n ω - dualMinNormSolution V hTarget)‖ ≤ Real.sqrt Cq * δ n := by
    simpa using dr_norm_rate_of_sq _ (δ n) Cq 1 (hδ n) hCq (by simpa using hTq)
  have hb := drScore_bias_of_rates V hTarget hRange hDualRange (hhat n ω) (qhat n ω)
    βh βq (δ n) (Real.sqrt Ch) (Real.sqrt Cq) (hδ n)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hh' hq' hTh' hTq'
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ Real.sqrt n * (Real.sqrt Ch * Real.sqrt Cq *
        δ n ^ (1 + interpolationExponent (betterSource βh βq))) :=
      mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)
    _ = _ := by ring

end Papers.TsAdaptiveEstimationInference
