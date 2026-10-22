module
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.Probability.Martingale.Basic
public import Papers.TbsExtremeEffects.Helpers.Hill.Renyi
public import Toolkit.Foundations.Probability.Concentration.ExponentialSupermartingale

/-! Centered exponential moment bounds and the Hill spacing supermartingales. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

/-- If [the tilt is nonnegative](hyp:hlam) and [smaller than one](hyp:hlamone), then [its positive exponential log-moment is bounded by the Bernstein quadratic envelope](goal).
-/
-- @node: hill_log_mgf_positive_bound
lemma hill_log_mgf_positive_bound {lam : ℝ} (hlam : 0 ≤ lam) (hlamone : lam < 1) :
    -lam - Real.log (1 - lam) ≤ lam ^ 2 / (2 * (1 - lam)) := by
  let F : ℝ → ℝ := fun x => x ^ 2 / (2 * (1 - x)) + x + Real.log (1 - x)
  have hderiv : ∀ x ∈ Set.Icc 0 lam,
      HasDerivAt F (x ^ 2 / (2 * (1 - x) ^ 2)) x := by
    intro x hx
    have hden : 1 - x ≠ 0 := by linarith [hx.2]
    have hd := (((hasDerivAt_id x).pow 2).div
      (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).const_mul 2)
      (by simpa using hden)).add (hasDerivAt_id x)
    have hlog := ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).log hden
    convert hd.add hlog using 1 <;> first | rfl | (dsimp; field_simp; ring)
  have hmono : MonotoneOn F (Set.Icc 0 lam) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun x hx => (hderiv x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hderiv x (interior_subset hx)).hasDerivWithinAt)
      (fun x _ => by positivity)
  have h := hmono ⟨le_rfl, hlam⟩ ⟨hlam, le_rfl⟩ hlam
  simp only [F, zero_pow (by norm_num : 2 ≠ 0), zero_div, zero_add, sub_zero,
    Real.log_one] at h
  linarith

/-- If [the tilt is nonnegative](hyp:hlam) and [smaller than one](hyp:hlamone), then [its negative exponential log-moment is bounded by the Bernstein quadratic envelope](goal).
-/
-- @node: hill_log_mgf_negative_bound
lemma hill_log_mgf_negative_bound {lam : ℝ} (hlam : 0 ≤ lam) (hlamone : lam < 1) :
    lam - Real.log (1 + lam) ≤ lam ^ 2 / (2 * (1 - lam)) := by
  let F : ℝ → ℝ := fun x => x ^ 2 / 2 - x + Real.log (1 + x)
  have hderiv : ∀ x ∈ Set.Icc 0 lam, HasDerivAt F (x ^ 2 / (1 + x)) x := by
    intro x hx
    have hden : 1 + x ≠ 0 := by linarith [hx.1]
    have hd := (((hasDerivAt_id x).pow 2).div_const 2).sub (hasDerivAt_id x)
    have hlog := ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)).log hden
    convert hd.add hlog using 1 <;> first | rfl | (dsimp; field_simp; ring)
  have hmono : MonotoneOn F (Set.Icc 0 lam) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun x hx => (hderiv x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hderiv x (interior_subset hx)).hasDerivWithinAt)
      (fun x hx => div_nonneg (sq_nonneg x) (by linarith [(interior_subset hx).1]))
  have h := hmono ⟨le_rfl, hlam⟩ ⟨hlam, le_rfl⟩ hlam
  simp only [F, zero_pow (by norm_num : 2 ≠ 0), zero_div, sub_zero,
    add_zero, Real.log_one] at h
  have hquad : lam ^ 2 / 2 ≤ lam ^ 2 / (2 * (1 - lam)) := by
    apply div_le_div_of_nonneg_left (sq_nonneg lam) (by positivity)
    linarith
  linarith

/-- If [the process is strongly adapted](hyp:hB), [the tilt is positive](hyp:hlam), [the tilt is below one](hyp:hlamone), [both compensated exponentials are integrable](hyp:hInt), [both exponential increments are integrable](hyp:hInc), and [their conditional moments have the exact exponential values](hyp:hMoment), then [the positive and negative compensated exponential processes are supermartingales](goal).
-/
-- @node: hill_supermartingales_of_exponential_increment_moments
lemma hill_supermartingales_of_exponential_increment_moments
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℕ → Ω → ℝ)
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (hB : StronglyAdapted ℱ B)
    {lam : ℝ} (hlam : 0 < lam) (hlamone : lam < 1)
    (hInt : ∀ i,
      Integrable (fun w => Real.exp
        (lam * B i w - (i : ℝ) * (lam ^ 2 / (2 * (1 - lam))))) P ∧
      Integrable (fun w => Real.exp
        (lam * (-B i w) - (i : ℝ) * (lam ^ 2 / (2 * (1 - lam))))) P)
    (hInc : ∀ i,
      Integrable (fun w => Real.exp (lam * (B (i + 1) w - B i w))) P ∧
      Integrable (fun w => Real.exp (-lam * (B (i + 1) w - B i w))) P)
    (hMoment : ∀ i,
      P[(fun w => Real.exp (lam * (B (i + 1) w - B i w))) | ℱ i]
        =ᵐ[P] (fun _ => Real.exp (-lam) / (1 - lam)) ∧
      P[(fun w => Real.exp (-lam * (B (i + 1) w - B i w))) | ℱ i]
        =ᵐ[P] fun _ => Real.exp lam / (1 + lam)) :
    Supermartingale (fun i w => Real.exp
      (lam * B i w - (i : ℝ) * (lam ^ 2 / (2 * (1 - lam))))) ℱ P ∧
    Supermartingale (fun i w => Real.exp
      (lam * (-B i w) - (i : ℝ) * (lam ^ 2 / (2 * (1 - lam))))) ℱ P := by
  have hplus : Real.exp (-lam) / (1 - lam) ≤
      Real.exp (lam ^ 2 / (2 * (1 - lam))) := by
    have heq : Real.exp (-lam) / (1 - lam) = Real.exp (-lam - Real.log (1 - lam)) := by
      rw [Real.exp_sub, Real.exp_log (by linarith : 0 < 1 - lam)]
    rw [heq]
    exact Real.exp_le_exp.mpr (hill_log_mgf_positive_bound hlam.le hlamone)
  have hminus : Real.exp lam / (1 + lam) ≤
      Real.exp (lam ^ 2 / (2 * (1 - lam))) := by
    have heq : Real.exp lam / (1 + lam) = Real.exp (lam - Real.log (1 + lam)) := by
      rw [Real.exp_sub, Real.exp_log (by linarith : 0 < 1 + lam)]
    rw [heq]
    exact Real.exp_le_exp.mpr (hill_log_mgf_negative_bound hlam.le hlamone)
  constructor
  · apply Toolkit.Foundations.Probability.Concentration.supermartingale_exp_mul_sub_of_condExp_exp_increment_le P B ℱ lam _ hB
      (fun i => (hInt i).1) (fun i => (hInc i).1)
    intro i
    exact ((hMoment i).1).le.trans (Eventually.of_forall fun _ => hplus)
  · apply Toolkit.Foundations.Probability.Concentration.supermartingale_exp_mul_sub_of_condExp_exp_increment_le P (fun i w => -B i w) ℱ lam _ hB.neg
      (fun i => (hInt i).2)
    · intro i
      convert (hInc i).2 using 1
      funext w
      congr 1
      ring
    · intro i
      have heq : (fun w => Real.exp (lam * (-B (i + 1) w - -B i w))) =
          (fun w => Real.exp (-lam * (B (i + 1) w - B i w))) := by
        funext w
        congr 1
        ring
      rw [heq]
      exact ((hMoment i).2).le.trans (Eventually.of_forall fun _ => hminus)

/-- If [the process is constant after the horizon](hyp:hStopped) and [each compensated exponential up to that horizon is integrable](hyp:hInt), then [the compensated exponential is integrable at every time](goal).
-/
-- @node: hill_compensated_integrable_of_finite_horizon
lemma hill_compensated_integrable_of_finite_horizon
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (B : ℕ → Ω → ℝ)
    (n : ℕ) (lam c : ℝ) (hStopped : ∀ i, n ≤ i → ∀ w, B i w = B n w)
    (hInt : ∀ i ≤ n, Integrable (fun w => Real.exp (lam * B i w - (i : ℝ) * c)) P) :
    ∀ i, Integrable (fun w => Real.exp (lam * B i w - (i : ℝ) * c)) P := by
  intro i
  by_cases hi : i ≤ n
  · exact hInt i hi
  · have heq : (fun w => Real.exp (lam * B i w - (i : ℝ) * c)) =
        fun w => Real.exp (((n : ℝ) - i) * c) * Real.exp (lam * B n w - (n : ℝ) * c) := by
      funext w
      rw [hStopped i (by omega) w, ← Real.exp_add]
      congr 1
      ring
    rw [heq]
    exact (hInt n le_rfl).const_mul _

/-- If [the compensation is nonnegative](hyp:hc), [the process is strongly adapted](hyp:hB), [the process is constant after its horizon](hyp:hStopped), [compensated exponentials before the horizon are integrable](hyp:hInt), [exponential increments before the horizon are integrable](hyp:hInc), and [their conditional moments satisfy the bound](hyp:hMoment), then [the compensated exponential process is a supermartingale](goal).
-/
-- @node: hill_supermartingale_of_finite_increment_moment
lemma hill_supermartingale_of_finite_increment_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℕ → Ω → ℝ)
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (n : ℕ) (lam c : ℝ) (hc : 0 ≤ c)
    (hB : StronglyAdapted ℱ B)
    (hStopped : ∀ i, n ≤ i → ∀ w, B i w = B n w)
    (hInt : ∀ i ≤ n, Integrable (fun w => Real.exp (lam * B i w - (i : ℝ) * c)) P)
    (hInc : ∀ i < n, Integrable (fun w => Real.exp (lam * (B (i + 1) w - B i w))) P)
    (hMoment : ∀ i < n,
      P[(fun w => Real.exp (lam * (B (i + 1) w - B i w))) | ℱ i]
        ≤ᵐ[P] fun _ => Real.exp c) :
    Supermartingale (fun i w => Real.exp (lam * B i w - (i : ℝ) * c)) ℱ P := by
  have hzero : ∀ i, n ≤ i →
      (fun w => Real.exp (lam * (B (i + 1) w - B i w))) = fun _ => (1 : ℝ) := by
    intro i hi
    funext w
    rw [hStopped (i + 1) (by omega) w, hStopped i hi w, sub_self, mul_zero, Real.exp_zero]
  apply Toolkit.Foundations.Probability.Concentration.supermartingale_exp_mul_sub_of_condExp_exp_increment_le P B ℱ lam c hB
    (hill_compensated_integrable_of_finite_horizon P B n lam c hStopped hInt)
  · intro i
    by_cases hi : i < n
    · exact hInc i hi
    · rw [hzero i (by omega)]
      exact integrable_const 1
  · intro i
    by_cases hi : i < n
    · exact hMoment i hi
    · rw [hzero i (by omega), condExp_const (ℱ.le i)]
      exact Eventually.of_forall fun _ => Real.one_le_exp_iff.mpr hc

/-- If [the process is strongly adapted](hyp:hB), [it is constant after the observation horizon](hyp:hStopped), [the tilt is positive](hyp:hlam), [the tilt is below one](hyp:hlamone), [both compensated exponentials up to the horizon are integrable](hyp:hInt), [both exponential increments before it are integrable](hyp:hInc), and [their conditional moments take the exact exponential values](hyp:hMoment), then [both finite-horizon Bernstein exponential processes are supermartingales](goal).
-/
-- @node: hill_supermartingales_of_finite_exponential_increment_moments
lemma hill_supermartingales_of_finite_exponential_increment_moments
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℕ → Ω → ℝ)
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (n : ℕ) (hB : StronglyAdapted ℱ B)
    (hStopped : ∀ i, n ≤ i → ∀ w, B i w = B n w)
    {lam : ℝ} (hlam : 0 < lam) (hlamone : lam < 1)
    (hInt : ∀ i ≤ n,
      Integrable (fun w => Real.exp
        (lam * B i w - (i : ℝ) * (lam ^ 2 / (2 * (1 - lam))))) P ∧
      Integrable (fun w => Real.exp
        (lam * (-B i w) - (i : ℝ) * (lam ^ 2 / (2 * (1 - lam))))) P)
    (hInc : ∀ i < n,
      Integrable (fun w => Real.exp (lam * (B (i + 1) w - B i w))) P ∧
      Integrable (fun w => Real.exp (-lam * (B (i + 1) w - B i w))) P)
    (hMoment : ∀ i < n,
      P[(fun w => Real.exp (lam * (B (i + 1) w - B i w))) | ℱ i]
        =ᵐ[P] (fun _ => Real.exp (-lam) / (1 - lam)) ∧
      P[(fun w => Real.exp (-lam * (B (i + 1) w - B i w))) | ℱ i]
        =ᵐ[P] fun _ => Real.exp lam / (1 + lam)) :
    Supermartingale (fun i w => Real.exp
      (lam * B i w - (i : ℝ) * (lam ^ 2 / (2 * (1 - lam))))) ℱ P ∧
    Supermartingale (fun i w => Real.exp
      (lam * (-B i w) - (i : ℝ) * (lam ^ 2 / (2 * (1 - lam))))) ℱ P := by
  have hc : 0 ≤ lam ^ 2 / (2 * (1 - lam)) := by positivity
  have hplus : Real.exp (-lam) / (1 - lam) ≤
      Real.exp (lam ^ 2 / (2 * (1 - lam))) := by
    rw [show Real.exp (-lam) / (1 - lam) = Real.exp (-lam - Real.log (1 - lam)) by
      rw [Real.exp_sub, Real.exp_log (by linarith : 0 < 1 - lam)]]
    exact Real.exp_le_exp.mpr (hill_log_mgf_positive_bound hlam.le hlamone)
  have hminus : Real.exp lam / (1 + lam) ≤
      Real.exp (lam ^ 2 / (2 * (1 - lam))) := by
    rw [show Real.exp lam / (1 + lam) = Real.exp (lam - Real.log (1 + lam)) by
      rw [Real.exp_sub, Real.exp_log (by linarith : 0 < 1 + lam)]]
    exact Real.exp_le_exp.mpr (hill_log_mgf_negative_bound hlam.le hlamone)
  constructor
  · apply hill_supermartingale_of_finite_increment_moment P B ℱ n lam _ hc hB hStopped
      (fun i hi => (hInt i hi).1) (fun i hi => (hInc i hi).1)
    intro i hi
    exact ((hMoment i hi).1).le.trans (Eventually.of_forall fun _ => hplus)
  · apply hill_supermartingale_of_finite_increment_moment P (fun i w => -B i w) ℱ n lam _ hc
      hB.neg (fun i hi w => congrArg Neg.neg (hStopped i hi w)) (fun i hi => (hInt i hi).2)
    · intro i hi
      convert (hInc i hi).2 using 1
      funext w
      congr 1
      ring
    · intro i hi
      have heq : (fun w => Real.exp (lam * (-B (i + 1) w - -B i w))) =
          (fun w => Real.exp (-lam * (B (i + 1) w - B i w))) := by
        funext w
        congr 1
        ring
      rw [heq]
      exact ((hMoment i hi).2).le.trans (Eventually.of_forall fun _ => hminus)

end Papers.TbsExtremeEffects
