module
public import Papers.TbsExtremeEffects.Helpers.Hill.Exponential
public import Mathlib.Probability.Distributions.Exponential

/-! Exact exponential tail probabilities and analytic side conditions for the
finite Hill spacing construction. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

/-- For a [positive exponential rate](hyp:hr) and a [nonnegative threshold](hyp:hz), [the probability of exceeding the threshold is the exponential survival probability](goal).
-/
-- @node: hill_exponential_survival
lemma hill_exponential_survival {r z : ℝ} (hr : 0 < r) (hz : 0 ≤ z) :
    (expMeasure r).real (Set.Ioi z) = Real.exp (-(r * z)) := by
  let := isProbabilityMeasure_expMeasure hr
  have h := cdf_expMeasure_eq hr z
  rw [cdf_eq_real, if_pos hz] at h
  have hc := measureReal_add_measureReal_compl
    (μ := expMeasure r) (s := Set.Iic z) measurableSet_Iic
  rw [Set.compl_Iic, probReal_univ, h] at hc
  linarith

/-- If [the variable is measurable](hyp:hV), [its distribution is standard exponential](hyp:hLaw), and [the threshold is nonnegative](hyp:hz), then [the mean of its exceedance indicator is the exponential survival probability](goal).
-/
-- @node: hill_exponential_exceedance_mean
lemma hill_exponential_exceedance_mean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (V : Ω → ℝ)
    (hV : Measurable V) (hLaw : P.map V = expMeasure 1)
    {z : ℝ} (hz : 0 ≤ z) :
    (∫ w, if z < V w then (1 : ℝ) else 0 ∂P) = Real.exp (-z) := by
  have hA : MeasurableSet {w | z < V w} := measurableSet_lt measurable_const hV
  have hind : (fun w => if z < V w then (1 : ℝ) else 0) =
      Set.indicator {w | z < V w} (fun _ => (1 : ℝ)) := by
    funext w
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [hind, integral_indicator_const _ hA, smul_eq_mul, mul_one]
  have hm : P.real {w | z < V w} = (expMeasure 1).real (Set.Ioi z) := by
    rw [← hLaw]
    simp only [Measure.real, Measure.map_apply hV measurableSet_Ioi]
    rfl
  rw [hm]
  simpa only [one_mul] using hill_exponential_survival (r := 1) (by norm_num) hz

/-- If [the variable is measurable](hyp:hV), [it has the standard exponential distribution](hyp:hLaw), [the selected order index is positive](hyp:hk), and [twice that index does not exceed the sample size](hyp:hkn), then [the exceedance probability at the logarithmic threshold equals twice the index divided by the sample size](goal).
-/
-- @node: hill_exponential_threshold_mean
lemma hill_exponential_threshold_mean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (V : Ω → ℝ)
    (hV : Measurable V) (hLaw : P.map V = expMeasure 1)
    {n k : ℕ} (hk : 0 < k) (hkn : 2 * k ≤ n) :
    (∫ w, if Real.log ((n : ℝ) / (2 * k)) < V w then (1 : ℝ) else 0 ∂P) =
      2 * (k : ℝ) / n := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hratio : 1 ≤ (n : ℝ) / (2 * k) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * (k : ℝ))).mpr
    norm_num only [one_mul]
    exact_mod_cast hkn
  rw [hill_exponential_exceedance_mean P V hV hLaw (Real.log_nonneg hratio),
    Real.exp_neg, Real.exp_log (by positivity : 0 < (n : ℝ) / (2 * k)), inv_div]

/-- If [the conditional-moment constant is nonzero](hyp:hc) and [the conditional expectation of the variable equals that constant almost surely](hyp:h), then [the variable is integrable](goal).
-/
-- @node: hill_integrable_of_nonzero_conditional_moment
lemma hill_integrable_of_nonzero_conditional_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (G : MeasurableSpace Ω)
    (f : Ω → ℝ) {c : ℝ} (hc : c ≠ 0)
    (h : P[f | G] =ᵐ[P] fun _ => c) : Integrable f P := by
  by_contra hn
  rw [condExp_of_not_integrable hn] at h
  have heq : (0 : ℝ) = c := by
    obtain ⟨w, hw⟩ := h.exists
    exact hw
  exact hc heq.symm

/-- If [the tilt is positive](hyp:hlam), [the tilt is below one](hyp:hlamone), and [the positive and negative exponential increments have their exact conditional moments](hyp:h), then [both exponential increments are integrable](goal).
-/
-- @node: hill_increment_integrable_of_exact_moments
lemma hill_increment_integrable_of_exact_moments {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℕ → Ω → ℝ)
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) {lam : ℝ}
    (hlam : 0 < lam) (hlamone : lam < 1) (i : ℕ)
    (h : P[(fun w => Real.exp (lam * (B (i + 1) w - B i w))) | ℱ i]
        =ᵐ[P] (fun _ => Real.exp (-lam) / (1 - lam)) ∧
      P[(fun w => Real.exp (-lam * (B (i + 1) w - B i w))) | ℱ i]
        =ᵐ[P] (fun _ => Real.exp lam / (1 + lam))) :
    Integrable (fun w => Real.exp (lam * (B (i + 1) w - B i w))) P ∧
      Integrable (fun w => Real.exp (-lam * (B (i + 1) w - B i w))) P := by
  constructor
  · exact hill_integrable_of_nonzero_conditional_moment P (ℱ i) _
      (ne_of_gt (by positivity)) h.1
  · exact hill_integrable_of_nonzero_conditional_moment P (ℱ i) _
      (ne_of_gt (by positivity)) h.2

end Papers.TbsExtremeEffects
