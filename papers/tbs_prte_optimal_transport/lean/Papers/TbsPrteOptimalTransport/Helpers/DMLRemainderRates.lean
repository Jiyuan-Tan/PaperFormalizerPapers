module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLProcedure
/-! Finite nuisance-error maxima and the second-order stochastic rate in the DML proof. -/
public section
set_option linter.unusedSectionVars false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Filter
open scoped Topology ENNReal

-- A fixed finite collection of componentwise rates gives the same rate for
-- the nonnegative maximum used in the score remainder bounds.
-- @node: maxErrors_isLittleOp
/-- If [the rate is positive at every sample size](hyp:hr) and [each error in a fixed finite list is negligible in probability relative to that rate](hyp:he), then [the maximum of those errors and zero is negligible at the same rate](goal). -/
lemma maxErrors_isLittleOp {A C : Type*} [MeasurableSpace A]
    (μ : Measure A) (s : List C) (e : ℕ → A → C → ℝ) (r : ℕ → ℝ)
    (hr : ∀ n, 0 < r n)
    (he : ∀ c ∈ s, Causalean.Stat.IsLittleOp (fun n a => e n a c) r μ) :
    Causalean.Stat.IsLittleOp (fun n a => maxErrors (s.map (e n a))) r μ := by
  induction s with
  | nil =>
    intro eps heps
    have hempty (n : ℕ) : {a : A | eps * r n ≤ ‖maxErrors ([] : List ℝ)‖} = ∅ := by
      ext a
      simp only [maxErrors, List.foldr_nil, norm_zero, Set.mem_ofPred_eq,
        Set.mem_empty_iff_false, iff_false]
      exact not_le_of_gt (mul_pos heps (hr n))
    simpa only [List.map_nil, hempty, measure_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
  | cons c s ih =>
    have hc := he c (by simp)
    have ht := ih (fun d hd => he d (by simp [hd]))
    have ha : Causalean.Stat.IsLittleOp (fun n a => |e n a c|) r μ := by
      simpa only [Causalean.Stat.IsLittleOp, Causalean.Stat.Modes.IsLittleOpF,
        Real.norm_eq_abs, abs_abs] using hc
    have hsum := ha.add_eventually_nonneg_rate
      (Eventually.of_forall (fun n => (hr n).le)) ht
    apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul one_pos hsum
    intro n a
    have hn := maxErrors_nonneg (s.map (e n a))
    simp only [List.map_cons, maxErrors, List.foldr_cons]
    change |max (e n a c) (maxErrors (s.map (e n a)))| ≤
      1 * |(|e n a c| + maxErrors (s.map (e n a)))|
    rw [one_mul, abs_of_nonneg (add_nonneg (abs_nonneg _) hn),
      abs_of_nonneg (hn.trans (le_max_right _ _))]
    exact max_le ((le_abs_self _).trans (le_add_of_nonneg_right hn))
      (le_add_of_nonneg_left (abs_nonneg _))

-- @node: dml_quarter_rate_product
/-- If [the first random sequence is negligible relative to the full sample size to the power minus one quarter](hyp:hf) and [the second sequence has the same rate](hyp:hg), then [their product is negligible relative to the full sample size to the power minus one half](goal), where the full sample size is twice the evaluation sample size. -/
lemma dml_quarter_rate_product {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (f g : ℕ → A → ℝ)
    (hf : Causalean.Stat.IsLittleOp f
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ)
    (hg : Causalean.Stat.IsLittleOp g
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ) :
    Causalean.Stat.IsLittleOp (fun n a => f n a * g n a)
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 2 : ℝ)) μ := by
  have hp (n : ℕ) : 0 < ((2 * (n + 1) : ℕ) : ℝ) := by positivity
  have hr : ∀ᶠ n in atTop, 0 < ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ) :=
    Eventually.of_forall (fun n => Real.rpow_pos_of_pos (hp n) (-1 / 4 : ℝ))
  have h := Causalean.Stat.Modes.IsLittleOpF.mul hf hg hr hr
  have hid (n : ℕ) :
      ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ) *
        ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ) =
      ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 2 : ℝ) := by
    rw [← Real.rpow_add (hp n)]
    norm_num
  simpa only [hid] using h

-- This is the rate implication after the score expectation has actually
-- been expanded; it does not assume or replace that expansion.
-- @node: dml_quadratic_bias_isLittleOp
/-- If [the bounding constant is positive](hyp:hC), [the regression error](hyp:hreg) and [the weight error](hyp:hwt) are each negligible relative to the full sample size to the power minus one quarter, and [the absolute bias is bounded by that constant times the squared regression error plus the regression–weight error product](hyp:hbound), then [the bias is negligible relative to the full sample size to the power minus one half](goal). -/
lemma dml_quadratic_bias_isLittleOp {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (bias reg wt : ℕ → A → ℝ) (C : ℝ) (hC : 0 < C)
    (hreg : Causalean.Stat.IsLittleOp reg
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ)
    (hwt : Causalean.Stat.IsLittleOp wt
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ)
    (hbound : ∀ n a, |bias n a| ≤ C * (reg n a ^ 2 + reg n a * wt n a)) :
    Causalean.Stat.IsLittleOp bias
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 2 : ℝ)) μ := by
  have hs := dml_quarter_rate_product μ reg reg hreg hreg
  simp only [← sq] at hs
  have hp := dml_quarter_rate_product μ reg wt hreg hwt
  have hsum := hs.add_eventually_nonneg_rate
    (Eventually.of_forall (fun _ => Real.rpow_nonneg (by positivity) _)) hp
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul hC hsum
  intro n a
  exact (hbound n a).trans (mul_le_mul_of_nonneg_left (le_abs_self _) hC.le)

-- The normalization is the evaluation-half normalization in the theorem,
-- while the nuisance rates are expressed using the full sample size.
-- @node: dml_root_n_bias_tendsto_probability
/-- If [the bias is negligible relative to the inverse square root of the full sample size](hyp:hbias), then [the bias multiplied by the square root of the evaluation sample size converges to zero in probability](goal), with full sample size twice the evaluation sample size. -/
lemma dml_root_n_bias_tendsto_probability {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (bias : ℕ → A → ℝ)
    (hbias : Causalean.Stat.IsLittleOp bias
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 2 : ℝ)) μ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) * bias n a) atTop (fun _ _ => 0) := by
  have hp (n : ℕ) : 0 < ((2 * (n + 1) : ℕ) : ℝ) := by positivity
  have hscale (n : ℕ) : Real.sqrt ((n + 1 : ℕ) : ℝ) *
      ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 2 : ℝ) ≤ 1 := by
    calc
      _ ≤ Real.sqrt ((2 * (n + 1) : ℕ) : ℝ) *
          ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 2 : ℝ) := by
        apply mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_)
          (Real.rpow_nonneg (hp n).le _)
        push_cast
        linarith
      _ = 1 := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add (hp n)]
        norm_num
  rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
  intro eps heps
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hbias eps heps)
    (fun _ => zero_le)
  intro n
  apply measure_mono
  intro a ha
  change eps ≤ ‖Real.sqrt ((n + 1 : ℕ) : ℝ) * bias n a - 0‖ at ha
  simp only [sub_zero, norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)] at ha
  change eps * ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 2 : ℝ) ≤ ‖bias n a‖
  rw [Real.norm_eq_abs]
  calc
    _ ≤ (Real.sqrt ((n + 1 : ℕ) : ℝ) * |bias n a|) *
        ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg (hp n).le _)
    _ = (Real.sqrt ((n + 1 : ℕ) : ℝ) *
        ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 2 : ℝ)) * |bias n a| := by ring
    _ ≤ |bias n a| := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hscale n) (abs_nonneg _)

-- @node: dml_quadratic_bias_root_n_negligible
/-- Suppose [the bounding constant is positive](hyp:hC), [the regression error](hyp:hreg) and [the weight error](hyp:hwt) are negligible relative to the full sample size to the power minus one quarter, and [the absolute bias is at most that constant times the squared regression error plus the regression–weight error product](hyp:hbound). Then [the bias multiplied by the square root of the evaluation sample size converges to zero in probability](goal), when the full sample has twice as many observations. -/
lemma dml_quadratic_bias_root_n_negligible {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (bias reg wt : ℕ → A → ℝ) (C : ℝ) (hC : 0 < C)
    (hreg : Causalean.Stat.IsLittleOp reg
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ)
    (hwt : Causalean.Stat.IsLittleOp wt
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ)
    (hbound : ∀ n a, |bias n a| ≤ C * (reg n a ^ 2 + reg n a * wt n a)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) * bias n a) atTop (fun _ _ => 0) := by
  exact dml_root_n_bias_tendsto_probability μ bias
    (dml_quadratic_bias_isLittleOp μ bias reg wt C hC hreg hwt hbound)

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- This consumes the actual componentwise nuisance-rate predicate, rather
-- than assuming a rate for a maximum as an extra theorem hypothesis.
-- @node: nuisanceRates_finite_maxErrors
/-- If [each fitted nuisance component has population L² error negligible relative to the full sample size to the power minus one quarter](hyp:h), then [the maximum of zero and the errors for any fixed finite list of components has the same rate along even full sample sizes](goal). -/
lemma nuisanceRates_finite_maxErrors {C : Type*} (M : LatentIVModel Ω X Z)
    (μ : Measure A) (fit : ℕ → A → C → X → ℝ) (truth : C → X → ℝ)
    (s : List C) (h : FiniteNuisanceRates M μ fit truth) :
    Causalean.Stat.IsLittleOp
      (fun n a => maxErrors (s.map (fun c => finiteL2Error M (fit (2 * (n + 1)) a c) (truth c))))
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ := by
  apply maxErrors_isLittleOp
  · intro n
    apply Real.rpow_pos_of_pos
    positivity
  · intro c _
    exact h c

end Papers.TbsPrteOptimalTransport
