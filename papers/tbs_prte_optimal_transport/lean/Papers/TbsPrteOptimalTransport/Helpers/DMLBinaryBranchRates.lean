module
public import Papers.TbsPrteOptimalTransport.Helpers.BinaryBranchConvergence
public import Papers.TbsPrteOptimalTransport.Helpers.DMLIndicatorRates
/-! Componentwise stochastic rates for binary active branches and their debiased remainder. -/
@[expose] public section
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Filter
open scoped Topology

-- @node: binaryFittedHingeRemainder
/-- For [the true upper argument](hyp:q), [lower argument](hyp:l), and
[boundary](hyp:b), and their [fitted upper](hyp:qh), [lower](hyp:lh), and
[boundary](hyp:bh) counterparts, the [fitted hinge remainder](goal) is the change
in the positive part of the upper argument minus the larger of the lower argument
and boundary, less its linear correction using the fitted strict active-branch indicators. -/
noncomputable def binaryFittedHingeRemainder (q l b qh lh bh : ℝ) : ℝ :=
  max 0 (qh - max lh bh) - max 0 (q - max l b) -
    (indicator (qh > max lh bh) * (qh - q) -
      indicator (lh < bh ∧ bh < qh) * (bh - b) -
      indicator (lh > bh) * indicator (qh > max lh bh) * (lh - l))

-- The sum of absolute component errors is a common envelope for all three
-- affine arguments. Its energy is controlled by their componentwise energies.
-- @node: integral_sq_abs_sum_three_le
/-- If [the first error](hyp:hf), [second error](hyp:hg), and
[third error](hyp:h,hh) are square integrable, then [their absolute sum is square
integrable and its integrated square is at most three times the sum of their
individual integrated squares](goal). -/
lemma integral_sq_abs_sum_three_le {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (f g h : X → ℝ)
    (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) (hh : MemLp h 2 ν) :
    MemLp (fun x => |f x| + |g x| + |h x|) 2 ν ∧
      (∫ x, (|f x| + |g x| + |h x|) ^ 2 ∂ν) ≤
        3 * ((∫ x, f x ^ 2 ∂ν) + (∫ x, g x ^ 2 ∂ν) + ∫ x, h x ^ 2 ∂ν) := by
  have he : MemLp (fun x => |f x| + |g x| + |h x|) 2 ν := by
    simpa only [Real.norm_eq_abs, Pi.add_def] using (hf.norm.add hg.norm).add hh.norm
  refine ⟨he, ?_⟩
  have hi : Integrable (fun x => f x ^ 2 + g x ^ 2 + h x ^ 2) ν :=
    (hf.integrable_sq.add hg.integrable_sq).add hh.integrable_sq
  calc
    _ ≤ ∫ x, 3 * (f x ^ 2 + g x ^ 2 + h x ^ 2) ∂ν := by
      apply integral_mono he.integrable_sq (hi.const_mul 3)
      intro x
      change (|f x| + |g x| + |h x|) ^ 2 ≤ 3 * (f x ^ 2 + g x ^ 2 + h x ^ 2)
      nlinarith [sq_nonneg (|f x| - |g x|), sq_nonneg (|f x| - |h x|),
        sq_nonneg (|g x| - |h x|), sq_abs (f x), sq_abs (g x), sq_abs (h x)]
    _ = _ := by
      have hfg : Integrable (fun x => f x ^ 2 + g x ^ 2) ν :=
        hf.integrable_sq.add hg.integrable_sq
      rw [integral_const_mul, integral_add hfg hh.integrable_sq,
        integral_add hf.integrable_sq hg.integrable_sq]

-- @node: binary_branch_component_energy_bound
/-- Suppose [the separation constant is positive](hyp:hc), [the true upper,
lower, and boundary arguments are measurable](hyp:hq,hl,hb), [their fitted
counterparts are measurable](hyp:hqh,hlh,hbh), and [each component error is
square integrable](hyp:heq,hel,heb). If [almost everywhere the upper-minus-lower
gap and the boundary's distances from both arguments are at least the separation
constant](hyp:hgap), then [the squared binary branch error is integrable and its
integral is at most 36 divided by the squared separation constant times the sum
of the three component error energies](goal). -/
lemma binary_branch_component_energy_bound {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (q l b qh lh bh : X → ℝ) (c : ℝ)
    (hc : 0 < c) (hq : Measurable q) (hl : Measurable l) (hb : Measurable b)
    (hqh : Measurable qh) (hlh : Measurable lh) (hbh : Measurable bh)
    (heq : MemLp (fun x => qh x - q x) 2 ν)
    (hel : MemLp (fun x => lh x - l x) 2 ν)
    (heb : MemLp (fun x => bh x - b x) 2 ν)
    (hgap : ∀ᵐ x ∂ν, c ≤ q x - l x ∧ c ≤ |b x - l x| ∧ c ≤ |b x - q x|) :
    Integrable (fun x => binaryBranchSqError (q x) (l x) (b x) (qh x) (lh x) (bh x)) ν ∧
      (∫ x, binaryBranchSqError (q x) (l x) (b x) (qh x) (lh x) (bh x) ∂ν) ≤
        (36 / c ^ 2) * ((∫ x, (qh x - q x) ^ 2 ∂ν) +
          (∫ x, (lh x - l x) ^ 2 ∂ν) + ∫ x, (bh x - b x) ^ 2 ∂ν) := by
  obtain ⟨he, henergy⟩ := integral_sq_abs_sum_three_le ν _ _ _ heq hel heb
  have herr : ∀ᵐ x ∂ν,
      |qh x - q x| ≤ |qh x - q x| + |lh x - l x| + |bh x - b x| ∧
      |lh x - l x| ≤ |qh x - q x| + |lh x - l x| + |bh x - b x| ∧
      |bh x - b x| ≤ |qh x - q x| + |lh x - l x| + |bh x - b x| := by
    apply Eventually.of_forall
    intro x
    have := abs_nonneg (qh x - q x)
    have := abs_nonneg (lh x - l x)
    have := abs_nonneg (bh x - b x)
    constructor
    · linarith
    constructor <;> linarith
  obtain ⟨hi, hbound⟩ := binary_branch_integrated_sq_error_bound ν q l b qh lh bh
    _ c hc hq hl hb hqh hlh hbh he hgap herr
  refine ⟨hi, hbound.trans ?_⟩
  calc
    _ ≤ (12 / c ^ 2) * (3 * ((∫ x, (qh x - q x) ^ 2 ∂ν) +
        (∫ x, (lh x - l x) ^ 2 ∂ν) + ∫ x, (bh x - b x) ^ 2 ∂ν)) :=
      mul_le_mul_of_nonneg_left henergy (by positivity)
    _ = _ := by ring

-- @node: binary_hinge_component_energy_bound
/-- Suppose [the separation constant is positive](hyp:hc), [the true upper,
lower, and boundary arguments are measurable](hyp:hq,hl,hb), [their fitted
counterparts are measurable](hyp:hqh,hlh,hbh), and [each component error is
square integrable](hyp:heq,hel,heb). If [almost everywhere the upper-minus-lower
gap and the boundary's distances from both arguments are at least the separation
constant](hyp:hgap), then [the fitted hinge remainder is integrable and the
absolute value of its integral is at most 78 divided by the separation constant
times the sum of the three component error energies](goal). -/
lemma binary_hinge_component_energy_bound {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (q l b qh lh bh : X → ℝ) (c : ℝ)
    (hc : 0 < c) (hq : Measurable q) (hl : Measurable l) (hb : Measurable b)
    (hqh : Measurable qh) (hlh : Measurable lh) (hbh : Measurable bh)
    (heq : MemLp (fun x => qh x - q x) 2 ν)
    (hel : MemLp (fun x => lh x - l x) 2 ν)
    (heb : MemLp (fun x => bh x - b x) 2 ν)
    (hgap : ∀ᵐ x ∂ν, c ≤ q x - l x ∧ c ≤ |b x - l x| ∧ c ≤ |b x - q x|) :
    Integrable (fun x => binaryFittedHingeRemainder
      (q x) (l x) (b x) (qh x) (lh x) (bh x)) ν ∧
      |∫ x, binaryFittedHingeRemainder (q x) (l x) (b x) (qh x) (lh x) (bh x) ∂ν| ≤
        (78 / c) * ((∫ x, (qh x - q x) ^ 2 ∂ν) +
          (∫ x, (lh x - l x) ^ 2 ∂ν) + ∫ x, (bh x - b x) ^ 2 ∂ν) := by
  obtain ⟨he, henergy⟩ := integral_sq_abs_sum_three_le ν _ _ _ heq hel heb
  have herr : ∀ᵐ x ∂ν,
      |qh x - q x| ≤ |qh x - q x| + |lh x - l x| + |bh x - b x| ∧
      |lh x - l x| ≤ |qh x - q x| + |lh x - l x| + |bh x - b x| ∧
      |bh x - b x| ≤ |qh x - q x| + |lh x - l x| + |bh x - b x| := by
    apply Eventually.of_forall
    intro x
    have := abs_nonneg (qh x - q x)
    have := abs_nonneg (lh x - l x)
    have := abs_nonneg (bh x - b x)
    constructor
    · linarith
    constructor <;> linarith
  have h := binary_hinge_fitted_score_integrated_remainder ν q l b
    (fun x => qh x - q x) (fun x => lh x - l x) (fun x => bh x - b x)
    _ c hc hq hl hb (by fun_prop) (by fun_prop) (by fun_prop) he hgap herr
  simp only [add_sub_cancel] at h
  change Integrable (fun x => binaryFittedHingeRemainder
    (q x) (l x) (b x) (qh x) (lh x) (bh x)) ν ∧
    |∫ x, binaryFittedHingeRemainder (q x) (l x) (b x) (qh x) (lh x) (bh x) ∂ν| ≤
      (26 / c) * (∫ x, (|qh x - q x| + |lh x - l x| + |bh x - b x|) ^ 2 ∂ν) at h
  refine ⟨h.1, h.2.trans ?_⟩
  calc
    _ ≤ (26 / c) * (3 * ((∫ x, (qh x - q x) ^ 2 ∂ν) +
        (∫ x, (lh x - l x) ^ 2 ∂ν) + ∫ x, (bh x - b x) ^ 2 ∂ν)) :=
      mul_le_mul_of_nonneg_left henergy (by positivity)
    _ = _ := by ring

-- @node: dml_three_component_energies_isLittleOp
/-- If [the first component's root integrated squared error is of smaller order
in probability than the inverse fourth root of twice the sample index plus
two](hyp:hf), [the second component has the same rate](hyp:hg), and [the third
component has the same rate](hyp:h,hh), then [the sum of their integrated squared
errors is of smaller order in probability than the inverse square root of twice
the sample index plus two](goal). -/
lemma dml_three_component_energies_isLittleOp {A X : Type*}
    [MeasurableSpace A] [MeasurableSpace X] (μ : Measure A) (ν : Measure X)
    (f g h : ℕ → A → X → ℝ)
    (hf : Causalean.Stat.IsLittleOp (fun n a => Real.sqrt (∫ x, f n a x ^ 2 ∂ν))
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ)
    (hg : Causalean.Stat.IsLittleOp (fun n a => Real.sqrt (∫ x, g n a x ^ 2 ∂ν))
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ)
    (hh : Causalean.Stat.IsLittleOp (fun n a => Real.sqrt (∫ x, h n a x ^ 2 ∂ν))
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ) :
    Causalean.Stat.IsLittleOp (fun n a => (∫ x, f n a x ^ 2 ∂ν) +
      (∫ x, g n a x ^ 2 ∂ν) + ∫ x, h n a x ^ 2 ∂ν)
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 2 : ℝ)) μ := by
  have hfs := dml_quarter_rate_product μ _ _ hf hf
  have hgs := dml_quarter_rate_product μ _ _ hg hg
  have hhs := dml_quarter_rate_product μ _ _ hh hh
  simp only [← sq, Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)] at hfs hgs hhs
  have hr : ∀ᶠ n in atTop,
      0 ≤ ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 2 : ℝ) :=
    Eventually.of_forall (fun n => Real.rpow_nonneg (by positivity) _)
  exact (hfs.add_eventually_nonneg_rate hr hgs).add_eventually_nonneg_rate hr hhs

-- This is the stochastic counterpart of the deterministic gap lemma: the
-- branch-error energy is o_P(n^(-1/2)), without convergence of expected rates.
-- @node: binary_branch_component_energy_isLittleOp
/-- Suppose [the separation constant is positive](hyp:hc), [the true upper,
lower, and boundary arguments are measurable](hyp:hq,hl,hb), [every fitted
argument is measurable](hyp:hqh,hlh,hbh), and [every component error is square
integrable](hyp:heq,hel,heb). If [the true upper-minus-lower gap and the boundary's
distances from both arguments are at least that constant almost everywhere](hyp:hgap),
and [the upper, lower, and boundary root integrated squared errors are each of
smaller order in probability than the inverse fourth root of twice the sample
index plus two](hyp:hrq,hrl,hrb), then [the integrated squared binary
branch error is of smaller order in probability than the inverse square root of
twice the sample index plus two](goal). -/
lemma binary_branch_component_energy_isLittleOp {A X : Type*}
    [MeasurableSpace A] [MeasurableSpace X] (μ : Measure A) (ν : Measure X)
    (q l b : X → ℝ) (qh lh bh : ℕ → A → X → ℝ) (c : ℝ)
    (hc : 0 < c) (hq : Measurable q) (hl : Measurable l) (hb : Measurable b)
    (hqh : ∀ n a, Measurable (qh n a)) (hlh : ∀ n a, Measurable (lh n a))
    (hbh : ∀ n a, Measurable (bh n a))
    (heq : ∀ n a, MemLp (fun x => qh n a x - q x) 2 ν)
    (hel : ∀ n a, MemLp (fun x => lh n a x - l x) 2 ν)
    (heb : ∀ n a, MemLp (fun x => bh n a x - b x) 2 ν)
    (hgap : ∀ᵐ x ∂ν, c ≤ q x - l x ∧ c ≤ |b x - l x| ∧ c ≤ |b x - q x|)
    (hrq : Causalean.Stat.IsLittleOp
      (fun n a => Real.sqrt (∫ x, (qh n a x - q x) ^ 2 ∂ν))
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ)
    (hrl : Causalean.Stat.IsLittleOp
      (fun n a => Real.sqrt (∫ x, (lh n a x - l x) ^ 2 ∂ν))
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ)
    (hrb : Causalean.Stat.IsLittleOp
      (fun n a => Real.sqrt (∫ x, (bh n a x - b x) ^ 2 ∂ν))
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ) :
    Causalean.Stat.IsLittleOp (fun n a => ∫ x,
      binaryBranchSqError (q x) (l x) (b x) (qh n a x) (lh n a x) (bh n a x) ∂ν)
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 2 : ℝ)) μ := by
  have he := dml_three_component_energies_isLittleOp μ ν
    (fun n a x => qh n a x - q x) (fun n a x => lh n a x - l x)
    (fun n a x => bh n a x - b x) hrq hrl hrb
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul (by positivity : 0 < 36 / c ^ 2) he
  intro n a
  rw [abs_of_nonneg (integral_nonneg fun x =>
    add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _))]
  exact (binary_branch_component_energy_bound ν q l b (qh n a) (lh n a) (bh n a)
    c hc hq hl hb (hqh n a) (hlh n a) (hbh n a) (heq n a) (hel n a) (heb n a)
    hgap).2.trans (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity))

-- @node: binary_hinge_component_remainder_isLittleOp
/-- Suppose [the separation constant is positive](hyp:hc), [the true upper,
lower, and boundary arguments are measurable](hyp:hq,hl,hb), [every fitted
argument is measurable](hyp:hqh,hlh,hbh), and [every component error is square
integrable](hyp:heq,hel,heb). If [the true upper-minus-lower gap and the boundary's
distances from both arguments are at least that constant almost everywhere](hyp:hgap),
and [the upper, lower, and boundary root integrated squared errors are each of
smaller order in probability than the inverse fourth root of twice the sample
index plus two](hyp:hrq,hrl,hrb), then [the integrated fitted hinge
remainder is of smaller order in probability than the inverse square root of
twice the sample index plus two](goal). -/
lemma binary_hinge_component_remainder_isLittleOp {A X : Type*}
    [MeasurableSpace A] [MeasurableSpace X] (μ : Measure A) (ν : Measure X)
    (q l b : X → ℝ) (qh lh bh : ℕ → A → X → ℝ) (c : ℝ)
    (hc : 0 < c) (hq : Measurable q) (hl : Measurable l) (hb : Measurable b)
    (hqh : ∀ n a, Measurable (qh n a)) (hlh : ∀ n a, Measurable (lh n a))
    (hbh : ∀ n a, Measurable (bh n a))
    (heq : ∀ n a, MemLp (fun x => qh n a x - q x) 2 ν)
    (hel : ∀ n a, MemLp (fun x => lh n a x - l x) 2 ν)
    (heb : ∀ n a, MemLp (fun x => bh n a x - b x) 2 ν)
    (hgap : ∀ᵐ x ∂ν, c ≤ q x - l x ∧ c ≤ |b x - l x| ∧ c ≤ |b x - q x|)
    (hrq : Causalean.Stat.IsLittleOp
      (fun n a => Real.sqrt (∫ x, (qh n a x - q x) ^ 2 ∂ν))
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ)
    (hrl : Causalean.Stat.IsLittleOp
      (fun n a => Real.sqrt (∫ x, (lh n a x - l x) ^ 2 ∂ν))
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ)
    (hrb : Causalean.Stat.IsLittleOp
      (fun n a => Real.sqrt (∫ x, (bh n a x - b x) ^ 2 ∂ν))
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ) :
    Causalean.Stat.IsLittleOp (fun n a => ∫ x,
      binaryFittedHingeRemainder (q x) (l x) (b x) (qh n a x) (lh n a x) (bh n a x) ∂ν)
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 2 : ℝ)) μ := by
  have he := dml_three_component_energies_isLittleOp μ ν
    (fun n a x => qh n a x - q x) (fun n a x => lh n a x - l x)
    (fun n a x => bh n a x - b x) hrq hrl hrb
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul (by positivity : 0 < 78 / c) he
  intro n a
  exact (binary_hinge_component_energy_bound ν q l b (qh n a) (lh n a) (bh n a)
    c hc hq hl hb (hqh n a) (hlh n a) (hbh n a) (heq n a) (hel n a) (heb n a)
    hgap).2.trans (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity))

-- A nonnegative energy at the half-rate converges to zero, as does its L2 norm.
-- @node: dml_half_rate_energy_l2_tendsto_probability_zero
/-- If [an energy is nonnegative for every sample index and realization](hyp:hE)
and [is of smaller order in probability than the inverse square root of twice
the sample index plus two](hyp:hr), then [its square root converges to zero in
probability](goal). -/
lemma dml_half_rate_energy_l2_tendsto_probability_zero {A : Type*}
    [MeasurableSpace A] (μ : Measure A) (E : ℕ → A → ℝ)
    (hE : ∀ n a, 0 ≤ E n a)
    (hr : Causalean.Stat.IsLittleOp E
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 2 : ℝ)) μ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt (E n a)) atTop (fun _ _ => 0) := by
  have hscaled := dml_root_n_bias_tendsto_probability μ E hr
  have hraw := probability_zero_of_nonneg_le μ E _ hscaled (by
    intro n
    apply Eventually.of_forall
    intro a
    have hn : 1 ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) := by
      have : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt this
    exact ⟨hE n a, by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hn (hE n a)⟩)
  have hcont : Continuous (fun t : ℝ => Real.sqrt t) := by fun_prop
  simpa only [Real.sqrt_zero] using
    Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt hcont.continuousAt hraw

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- Clipped affine arguments supply L2 membership; this introduces no separate
-- moment condition on the nuisances in the paper's theorem.
-- @node: clipped_binary_argument_errors_memLp
/-- If [the fitted argument is measurable](hyp:hfit), [the true argument is
measurable](hyp:htruth), and [both arguments lie almost everywhere in the same
fixed closed interval under the covariate law](hyp:hf,ht),
then [their difference is square integrable under that law](goal). -/
lemma clipped_binary_argument_errors_memLp (M : LatentIVModel Ω X Z)
    (fit truth : X → ℝ) (lo hi : ℝ)
    (hfit : Measurable fit) (htruth : Measurable truth)
    (hf : ∀ᵐ x ∂xLaw M, fit x ∈ Set.Icc lo hi)
    (ht : ∀ᵐ x ∂xLaw M, truth x ∈ Set.Icc lo hi) :
    MemLp (fun x => fit x - truth x) 2 (xLaw M) := by
  haveI : IsProbabilityMeasure (xLaw M) :=
    Measure.isProbabilityMeasure_map M.measX.aemeasurable
  have hfm : MemLp fit 2 (xLaw M) := by
    apply memLp_of_bounded hf
    fun_prop
  have htm : MemLp truth 2 (xLaw M) := by
    apply memLp_of_bounded ht
    fun_prop
  exact hfm.sub htm

-- Identify the scalar remainder with the fitted active coefficients in the
-- paper's binary score, including at fitted ties.
-- @node: hMinus_binaryFittedHingeRemainder_eq
/-- [The scalar fitted hinge remainder evaluated at the pooled upper and lower
policy arguments and the success-probability-minus-full-adjustment boundary
equals the change in the binary hinge term less the upper, boundary, and lower
argument corrections weighted by the fitted active coefficients](goal). -/
lemma hMinus_binaryFittedHingeRemainder_eq (phi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e0 e1 : NuisanceBin L) (k j : ℕ) (x : X) :
    binaryFittedHingeRemainder
      (pooledQBin phi L e0 k j x) (pooledQBin phi L e0 k (j - 1) x)
      (positiveValue e0.pLev (k + 1) x - binFullJ L e0 k x)
      (pooledQBin phi L e1 k j x) (pooledQBin phi L e1 k (j - 1) x)
      (positiveValue e1.pLev (k + 1) x - binFullJ L e1 k x) =
    hMinus phi L e1 k j x - hMinus phi L e0 k j x -
      (Iact phi L e1 k j x * (pooledQBin phi L e1 k j x - pooledQBin phi L e0 k j x) -
        Dbd phi L e1 k j x * ((positiveValue e1.pLev (k + 1) x - binFullJ L e1 k x) -
          (positiveValue e0.pLev (k + 1) x - binFullJ L e0 k x)) -
        Edom phi L e1 k j x * Iact phi L e1 k j x *
          (pooledQBin phi L e1 k (j - 1) x - pooledQBin phi L e0 k (j - 1) x)) := by
  rfl

-- The indices 0, 1, 2 represent the upper policy level, the lower policy
-- level, and the binary hinge boundary respectively.
-- @node: nuisanceRates_binary_branch_l2_tendsto_probability_zero
/-- Suppose [the separation constant is positive](hyp:hc), [all fitted
components are measurable](hyp:hfit), [all true components are measurable](hyp:htruth),
and [the fitted and true components lie almost everywhere in the same fixed
closed interval](hyp:hf,ht). If [the true upper-minus-lower gap and the
boundary's distances from both arguments are at least the separation constant
almost everywhere](hyp:hgap) and [each component's root integrated squared error
at twice the sample index plus two is of smaller order in probability than the
inverse fourth root of that index](hyp:hrates), then [the root integrated squared binary
branch error, using fits at twice the sample index plus two, converges to zero
in probability](goal). -/
lemma nuisanceRates_binary_branch_l2_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A)
    (fit : ℕ → A → Fin 3 → X → ℝ) (truth : Fin 3 → X → ℝ)
    (lo hi c : ℝ) (hc : 0 < c)
    (hfit : ∀ n a i, Measurable (fit n a i))
    (htruth : ∀ i, Measurable (truth i))
    (hf : ∀ n a i, ∀ᵐ x ∂xLaw M, fit n a i x ∈ Set.Icc lo hi)
    (ht : ∀ i, ∀ᵐ x ∂xLaw M, truth i x ∈ Set.Icc lo hi)
    (hgap : ∀ᵐ x ∂xLaw M, c ≤ truth 0 x - truth 1 x ∧
      c ≤ |truth 2 x - truth 1 x| ∧ c ≤ |truth 2 x - truth 0 x|)
    (hrates : FiniteNuisanceRates M μ fit truth) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt (∫ x, binaryBranchSqError
        (truth 0 x) (truth 1 x) (truth 2 x)
        (fit (2 * (n + 1)) a 0 x) (fit (2 * (n + 1)) a 1 x)
        (fit (2 * (n + 1)) a 2 x) ∂xLaw M)) atTop (fun _ _ => 0) := by
  apply dml_half_rate_energy_l2_tendsto_probability_zero
  · intro n a
    exact integral_nonneg fun x =>
      add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
  · apply binary_branch_component_energy_isLittleOp μ (xLaw M)
      (truth 0) (truth 1) (truth 2)
      (fun n a => fit (2 * (n + 1)) a 0)
      (fun n a => fit (2 * (n + 1)) a 1)
      (fun n a => fit (2 * (n + 1)) a 2) c hc
      (htruth 0) (htruth 1) (htruth 2)
      (fun n a => hfit _ a 0) (fun n a => hfit _ a 1) (fun n a => hfit _ a 2)
    · intro n a
      exact clipped_binary_argument_errors_memLp M _ _ lo hi
        (hfit _ a 0) (htruth 0) (hf _ a 0) (ht 0)
    · intro n a
      exact clipped_binary_argument_errors_memLp M _ _ lo hi
        (hfit _ a 1) (htruth 1) (hf _ a 1) (ht 1)
    · intro n a
      exact clipped_binary_argument_errors_memLp M _ _ lo hi
        (hfit _ a 2) (htruth 2) (hf _ a 2) (ht 2)
    · exact hgap
    · exact hrates 0
    · exact hrates 1
    · exact hrates 2

-- This remainder uses fitted active indicators, as the score does. A rate
-- for the plug-in target alone would not establish this conclusion.
-- @node: nuisanceRates_binary_hinge_root_n_negligible
/-- Suppose [the separation constant is positive](hyp:hc), [all fitted
components are measurable](hyp:hfit), [all true components are measurable](hyp:htruth),
and [the fitted and true components lie almost everywhere in the same fixed
closed interval](hyp:hf,ht). If [the true upper-minus-lower gap and the
boundary's distances from both arguments are at least the separation constant
almost everywhere](hyp:hgap) and [each component's root integrated squared error
at twice the sample index plus two is of smaller order in probability than the
inverse fourth root of that index](hyp:hrates), then [the integrated fitted hinge
remainder, using fits at twice the sample index plus two and multiplied by the
square root of the sample index plus one, converges to zero in probability](goal). -/
lemma nuisanceRates_binary_hinge_root_n_negligible
    (M : LatentIVModel Ω X Z) (μ : Measure A)
    (fit : ℕ → A → Fin 3 → X → ℝ) (truth : Fin 3 → X → ℝ)
    (lo hi c : ℝ) (hc : 0 < c)
    (hfit : ∀ n a i, Measurable (fit n a i))
    (htruth : ∀ i, Measurable (truth i))
    (hf : ∀ n a i, ∀ᵐ x ∂xLaw M, fit n a i x ∈ Set.Icc lo hi)
    (ht : ∀ i, ∀ᵐ x ∂xLaw M, truth i x ∈ Set.Icc lo hi)
    (hgap : ∀ᵐ x ∂xLaw M, c ≤ truth 0 x - truth 1 x ∧
      c ≤ |truth 2 x - truth 1 x| ∧ c ≤ |truth 2 x - truth 0 x|)
    (hrates : FiniteNuisanceRates M μ fit truth) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        ∫ x, binaryFittedHingeRemainder (truth 0 x) (truth 1 x) (truth 2 x)
          (fit (2 * (n + 1)) a 0 x) (fit (2 * (n + 1)) a 1 x)
          (fit (2 * (n + 1)) a 2 x) ∂xLaw M) atTop (fun _ _ => 0) := by
  apply dml_root_n_bias_tendsto_probability
  apply binary_hinge_component_remainder_isLittleOp μ (xLaw M)
    (truth 0) (truth 1) (truth 2)
    (fun n a => fit (2 * (n + 1)) a 0)
    (fun n a => fit (2 * (n + 1)) a 1)
    (fun n a => fit (2 * (n + 1)) a 2) c hc
    (htruth 0) (htruth 1) (htruth 2)
    (fun n a => hfit _ a 0) (fun n a => hfit _ a 1) (fun n a => hfit _ a 2)
  · intro n a
    exact clipped_binary_argument_errors_memLp M _ _ lo hi
      (hfit _ a 0) (htruth 0) (hf _ a 0) (ht 0)
  · intro n a
    exact clipped_binary_argument_errors_memLp M _ _ lo hi
      (hfit _ a 1) (htruth 1) (hf _ a 1) (ht 1)
  · intro n a
    exact clipped_binary_argument_errors_memLp M _ _ lo hi
      (hfit _ a 2) (htruth 2) (hf _ a 2) (ht 2)
  · exact hgap
  · exact hrates 0
  · exact hrates 1
  · exact hrates 2

end Papers.TbsPrteOptimalTransport
