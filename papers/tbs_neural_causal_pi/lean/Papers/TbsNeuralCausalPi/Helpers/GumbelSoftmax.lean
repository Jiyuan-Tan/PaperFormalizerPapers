module
public import Papers.TbsNeuralCausalPi.Setup.Networks
public import Papers.TbsNeuralCausalPi.Helpers.KantorovichCube
public import Mathlib.Analysis.Calculus.MeanValue
public import Papers.TbsNeuralCausalPi.Setup.Assumptions.Auxiliary
/-! # Gumbel-softmax coupling error -/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.haveILetI false
set_option linter.deprecated false
open MeasureTheory ProbabilityTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable
-- @node: exponential_one_ae_pos
/-- [A draw from the exponential distribution with rate one is strictly positive with probability one](goal). -/
lemma exponential_one_ae_pos : ∀ᵐ x ∂expMeasure 1, 0 < x := by
  let := isProbabilityMeasure_expMeasure (by norm_num : (0 : ℝ) < 1)
  have hzero : expMeasure 1 (Set.Iic 0) = 0 := by
    rw [← ofReal_cdf, cdf_expMeasure_eq (by norm_num)]
    norm_num
  simpa only [ae_iff, not_lt, Set.Iic] using hzero

-- @node: gumbelLaw_Iic
/-- [The probability that a standard Gumbel draw is at most x is exp(−exp(−x))](goal). -/
lemma gumbelLaw_Iic (x : ℝ) :
    gumbelLaw (Set.Iic x) = ENNReal.ofReal (Real.exp (-Real.exp (-x))) := by
  let := isProbabilityMeasure_expMeasure (by norm_num : (0 : ℝ) < 1)
  have hno : NullSingletonClass (expMeasure 1) := by
    unfold expMeasure gammaMeasure
    infer_instance
  let := hno
  rw [gumbelLaw, Measure.map_apply (by fun_prop) measurableSet_Iic]
  have heq : (fun y => -Real.log y) ⁻¹' Set.Iic x =ᵐ[expMeasure 1]
      Set.Ici (Real.exp (-x)) := by
    filter_upwards [exponential_one_ae_pos] with y hy
    apply propext
    change -Real.log y ≤ x ↔ Real.exp (-x) ≤ y
    rw [neg_le, Real.le_log_iff_exp_le hy]
  rw [measure_congr heq, ← measure_congr (Ioi_ae_eq_Ici (μ := expMeasure 1)),
    ← Set.compl_Iic, measure_compl measurableSet_Iic (measure_ne_top _ _),
    measure_univ, ← ofReal_cdf, cdf_expMeasure_eq (by norm_num),
    if_pos (Real.exp_pos _).le, one_mul]
  have hexp : 0 ≤ Real.exp (-Real.exp (-x)) := (Real.exp_pos _).le
  have hle : Real.exp (-Real.exp (-x)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.exp_pos _).le)
  rw [← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub 1 (by linarith : 0 ≤ 1 - Real.exp (-Real.exp (-x)))]
  congr 1
  ring

-- @node: gumbelLaw_cdf
/-- [The standard Gumbel cumulative distribution function at x equals exp(−exp(−x))](goal). -/
lemma gumbelLaw_cdf (x : ℝ) : cdf gumbelLaw x = Real.exp (-Real.exp (-x)) := by
  let := gumbelLaw_probability
  rw [cdf_eq_real, measureReal_def, gumbelLaw_Iic, ENNReal.toReal_ofReal (Real.exp_pos _).le]

-- @node: gumbel_cdf_hasDerivAt
/-- [The function exp(−exp(−x)) has derivative exp(−x − exp(−x)) at every real x](goal). -/
lemma gumbel_cdf_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y => Real.exp (-Real.exp (-y)))
      (Real.exp (-x - Real.exp (-x))) x := by
  convert ((((hasDerivAt_id x).neg.exp).neg).exp) using 1 <;>
    simp [Real.exp_sub, Real.exp_neg, mul_comm, div_eq_mul_inv]

-- @node: gumbel_density_le
/-- [The standard Gumbel density exp(−x − exp(−x)) is at most exp(−1) at every real x](goal). -/
lemma gumbel_density_le (x : ℝ) : Real.exp (-x - Real.exp (-x)) ≤ Real.exp (-1) := by
  apply Real.exp_le_exp.mpr
  have h := Real.add_one_le_exp (-x)
  linarith

-- @node: gumbelLaw_Ioc_le
/-- [The probability that a standard Gumbel draw lies in `(a, b]` is at most the nonnegative part of (b − a) exp(−1)](goal). -/
lemma gumbelLaw_Ioc_le (a b : ℝ) :
    gumbelLaw (Set.Ioc a b) ≤ ENNReal.ofReal ((b-a) * Real.exp (-1)) := by
  let := gumbelLaw_probability
  rw [← measure_cdf gumbelLaw, StieltjesFunction.measure_Ioc]
  simp_rw [gumbelLaw_cdf]
  by_cases hab : a ≤ b
  · apply ENNReal.ofReal_le_ofReal
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun x (_ : x ∈ Set.Icc a b) => (gumbel_cdf_hasDerivAt x).hasDerivWithinAt)
      (fun x (_ : x ∈ Set.Ico a b) => by
        simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using gumbel_density_le x)
      b (Set.right_mem_Icc.mpr hab)
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs, mul_comm] using h)
  · have hmono := (cdf gumbelLaw).mono' (le_of_not_ge hab)
    rw [gumbelLaw_cdf, gumbelLaw_cdf] at hmono
    rw [ENNReal.ofReal_eq_zero.mpr (sub_nonpos.mpr hmono)]
    exact bot_le

-- @node: softmaxWeights_measurable
/-- [The softmax selector is a measurable function of its input scores for any weights and temperature](goal). -/
@[fun_prop] lemma softmaxWeights_measurable {n : ℕ} (p : Fin n → ℝ) (tau : ℝ) :
    Measurable (softmaxWeights p tau) := by
  let : BorelSpace (L1Vec n) := ⟨rfl⟩
  have hterm : ∀ k, Measurable (fun G : Fin n → ℝ =>
      if p k = 0 then 0 else Real.exp ((Real.log (p k) + G k) / tau)) := by
    intro k
    by_cases hk : p k = 0
    · simp only [hk, if_true]
      exact measurable_const
    · simp only [hk, if_false]
      fun_prop
  unfold softmaxWeights
  apply (PiLp.continuous_toLp 1 _).measurable.comp
  apply measurable_pi_lambda
  intro k
  exact (hterm k).div (Finset.measurable_sum _ (fun j _ => hterm j))

-- @node: softmaxWeights_denominator_pos
/-- If [there is at least one category](hyp:hn), then [summing exp((log weight + input score) / temperature) over all categories gives a strictly positive number](goal). -/
lemma softmaxWeights_denominator_pos {n : ℕ} (hn : 0 < n)
    (p : Fin n → ℝ) (tau : ℝ) (G : Fin n → ℝ) :
    0 < ∑ j, Real.exp ((Real.log (p j) + G j) / tau) := by
  exact Finset.sum_pos (fun j _ => Real.exp_pos _) ⟨⟨0, hn⟩, Finset.mem_univ _⟩

-- @node: softmaxWeights_nonneg
/-- [Every coordinate of the softmax selector is nonnegative, for any weights, temperature, and input scores](goal). -/
lemma softmaxWeights_nonneg {n : ℕ} (p : Fin n → ℝ) (tau : ℝ)
    (G : Fin n → ℝ) (j : Fin n) : 0 ≤ (softmaxWeights p tau G).ofLp j := by
  dsimp [softmaxWeights]
  apply div_nonneg <;> positivity

-- @node: softmaxWeights_sum
/-- If [there is at least one category](hyp:hn) and [every weight is strictly positive](hyp:hp), then [the softmax coordinates sum to one for every temperature and input vector](goal). -/
lemma softmaxWeights_sum {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) (hp : ∀ k, 0 < p k)
    (tau : ℝ) (G : Fin n → ℝ) : ∑ j, (softmaxWeights p tau G).ofLp j = 1 := by
  have hne : ∀ k, p k ≠ 0 := fun k => (hp k).ne'
  simp only [softmaxWeights, WithLp.ofLp_toLp, hne, if_false]
  rw [← Finset.sum_div]
  exact div_self (softmaxWeights_denominator_pos hn p tau G).ne'

-- @node: softmaxWeights_le_one
/-- If [there is at least one category](hyp:hn) and [every weight is strictly positive](hyp:hp), then [each softmax coordinate is at most one](goal). -/
lemma softmaxWeights_le_one {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) (hp : ∀ k, 0 < p k)
    (tau : ℝ) (G : Fin n → ℝ) (j : Fin n) :
    (softmaxWeights p tau G).ofLp j ≤ 1 := by
  rw [← softmaxWeights_sum hn p hp tau G]
  exact Finset.single_le_sum (fun k _ => softmaxWeights_nonneg p tau G k)
    (Finset.mem_univ j)

-- @node: hardWeights_eq_oneHot
/-- If [j is the first category maximizing the extended log weight plus input score](hyp:hj), then [the hard selector equals the vector with value one at j and zero elsewhere](goal). -/
lemma hardWeights_eq_oneHot {n : ℕ} (p : Fin n → ℝ) (G : Fin n → ℝ)
    (j : Fin n)
    (hj : firstArgmax (fun k => extendedLog (p k) + (G k : EReal)) = some j) :
    hardWeights p G = WithLp.toLp 1 (fun k => if k = j then (1 : ℝ) else 0) := by
  apply (WithLp.ofLp_injective 1)
  funext k
  simp [hardWeights, hj, eq_comm]

-- @node: hardWeights_measurable
/-- If [there is at least one category](hyp:hn), then [the hard selector is a measurable function of its input scores for any weights](goal). -/
@[fun_prop] lemma hardWeights_measurable {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) :
    Measurable (hardWeights p) := by
  let : BorelSpace (L1Vec n) := ⟨rfl⟩
  let default : Fin n := ⟨0, hn⟩
  let selector := fun G : Fin n → ℝ =>
    (firstArgmax (fun k => extendedLog (p k) + (G k : EReal))).getD default
  have hs : Measurable selector := by
    apply firstArgmax_getD_measurable
    intro k
    fun_prop
  have heq : hardWeights p = fun G =>
      WithLp.toLp 1 (fun k => if selector G = k then (1 : ℝ) else 0) := by
    funext G
    obtain ⟨j, hj⟩ := firstArgmax_exists hn (fun k => extendedLog (p k) + (G k : EReal))
    rw [hardWeights_eq_oneHot p G j hj]
    simp [selector, hj, eq_comm]
  rw [heq]
  apply (PiLp.continuous_toLp 1 _).measurable.comp
  apply measurable_pi_lambda
  intro k
  exact Measurable.ite (measurableSet_eq_fun hs measurable_const)
    measurable_const measurable_const

-- @node: softmaxWeights_hardWeights_dist
/-- If [there is at least one category](hyp:hn), [all weights are strictly positive](hyp:hp), and [j is the first category maximizing the extended log weight plus input score](hyp:hj), then [the sum of absolute coordinate differences between the soft and hard selectors equals twice the total soft weight on categories other than j](goal). -/
lemma softmaxWeights_hardWeights_dist {n : ℕ} (hn : 0 < n)
    (p : Fin n → ℝ) (hp : ∀ k, 0 < p k) (tau : ℝ) (G : Fin n → ℝ) (j : Fin n)
    (hj : firstArgmax (fun k => extendedLog (p k) + (G k : EReal)) = some j) :
    dist (softmaxWeights p tau G) (hardWeights p G) =
      2 * ∑ k ∈ Finset.univ.erase j, (softmaxWeights p tau G).ofLp k := by
  classical
  rw [hardWeights_eq_oneHot p G j hj, PiLp.dist_eq_sum (p := 1) (by norm_num)]
  simp only [ENNReal.toReal_one, Real.rpow_one, one_div, inv_one, Real.dist_eq]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  have he : ∀ k ∈ Finset.univ.erase j,
      |(softmaxWeights p tau G).ofLp k - (if k = j then 1 else 0)| =
        (softmaxWeights p tau G).ofLp k := by
    intro k hk
    rw [if_neg (Finset.ne_of_mem_erase hk), sub_zero,
      abs_of_nonneg (softmaxWeights_nonneg p tau G k)]
  simp_rw [Finset.sum_congr rfl he]
  simp only [ite_true]
  rw [abs_of_nonpos (sub_nonpos.mpr (softmaxWeights_le_one hn p hp tau G j))]
  have hsum := softmaxWeights_sum hn p hp tau G
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)] at hsum
  linarith

-- @node: softmaxWeights_hardWeights_dist_le_two
/-- If [there is at least one category](hyp:hn) and [all weights are strictly positive](hyp:hp), then [the sum of absolute coordinate differences between the soft and hard selectors is at most two](goal). -/
lemma softmaxWeights_hardWeights_dist_le_two {n : ℕ} (hn : 0 < n)
    (p : Fin n → ℝ) (hp : ∀ k, 0 < p k) (tau : ℝ) (G : Fin n → ℝ) :
    dist (softmaxWeights p tau G) (hardWeights p G) ≤ 2 := by
  obtain ⟨j, hj⟩ := firstArgmax_exists hn (fun k => extendedLog (p k) + (G k : EReal))
  rw [softmaxWeights_hardWeights_dist hn p hp tau G j hj]
  have hsum := softmaxWeights_sum hn p hp tau G
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)] at hsum
  have hnonneg := softmaxWeights_nonneg p tau G j
  linarith

-- @node: softmaxWeights_le_exp_of_gap
/-- Suppose [there is at least one category](hyp:hn), [all weights are strictly positive](hyp:hp), and [the temperature is strictly positive](hyp:htau). If [the log weight plus input score of k is at least delta below that of j](hyp:hgap), then [the soft weight of k is at most exp(−delta / tau)](goal). -/
lemma softmaxWeights_le_exp_of_gap {n : ℕ} (hn : 0 < n)
    (p : Fin n → ℝ) (hp : ∀ k, 0 < p k) {tau : ℝ} (htau : 0 < tau) (G : Fin n → ℝ)
    (j k : Fin n) (delta : ℝ)
    (hgap : Real.log (p k) + G k ≤ Real.log (p j) + G j - delta) :
    (softmaxWeights p tau G).ofLp k ≤ Real.exp (-delta / tau) := by
  have hne : ∀ k, p k ≠ 0 := fun k => (hp k).ne'
  simp only [softmaxWeights, WithLp.ofLp_toLp, hne, if_false]
  change Real.exp _ / (∑ l, Real.exp _) ≤ _
  calc
    Real.exp ((Real.log (p k) + G k) / tau) /
        (∑ l, Real.exp ((Real.log (p l) + G l) / tau)) ≤
      Real.exp ((Real.log (p k) + G k) / tau) /
        Real.exp ((Real.log (p j) + G j) / tau) := by
      apply div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _)
      exact Finset.single_le_sum
        (fun l _ => (Real.exp_pos ((Real.log (p l) + G l) / tau)).le) (Finset.mem_univ j)
    _ = Real.exp ((Real.log (p k) + G k - (Real.log (p j) + G j)) / tau) := by
      rw [sub_div, Real.exp_sub]
    _ ≤ Real.exp (-delta / tau) := by
      apply Real.exp_le_exp.mpr
      apply div_le_div_of_nonneg_right _ htau.le
      linarith

-- @node: softmaxWeights_hardWeights_dist_le_of_gap
/-- Suppose [there is at least one category](hyp:hn), [all weights are strictly positive](hyp:hp), and [the temperature is strictly positive](hyp:htau). If [j is the first category maximizing the extended log weight plus input score](hyp:hj) and [every other category's log weight plus input score is at least delta below j's](hyp:hgap), then [the sum of absolute coordinate differences between the soft and hard selectors is at most 2(n − 1) exp(−delta / tau)](goal). -/
lemma softmaxWeights_hardWeights_dist_le_of_gap {n : ℕ} (hn : 0 < n)
    (p : Fin n → ℝ) (hp : ∀ k, 0 < p k) {tau : ℝ} (htau : 0 < tau) (G : Fin n → ℝ)
    (j : Fin n) (delta : ℝ)
    (hj : firstArgmax (fun k => extendedLog (p k) + (G k : EReal)) = some j)
    (hgap : ∀ k, k ≠ j → Real.log (p k) + G k ≤ Real.log (p j) + G j - delta) :
    dist (softmaxWeights p tau G) (hardWeights p G) ≤
      2 * (n - 1 : ℕ) * Real.exp (-delta / tau) := by
  rw [softmaxWeights_hardWeights_dist hn p hp tau G j hj]
  calc
    2 * (∑ k ∈ Finset.univ.erase j, (softmaxWeights p tau G).ofLp k) ≤
        2 * ∑ k ∈ Finset.univ.erase j, Real.exp (-delta / tau) := by
      gcongr with k hk
      exact softmaxWeights_le_exp_of_gap hn p hp htau G j k delta
        (hgap k (Finset.ne_of_mem_erase hk))
    _ = 2 * (n - 1 : ℕ) * Real.exp (-delta / tau) := by
      simp [Finset.card_erase_of_mem (Finset.mem_univ j), mul_assoc]

-- @node: gumbelInputs_probability
/-- [The joint law of n independent standard Gumbel inputs is a probability measure](goal). -/
lemma gumbelInputs_probability (n : ℕ) : IsProbabilityMeasure (gumbelInputs n) := by
  let := gumbelLaw_probability
  unfold gumbelInputs
  infer_instance

-- @node: wasserstein_gumbelSoftmax_le_coupling_cost
/-- If [there is at least one category](hyp:hn), then [the Wasserstein distance of order one between the soft and hard selector laws is at most their expected sum of absolute coordinate differences when both use the same independent Gumbel inputs](goal). -/
lemma wasserstein_gumbelSoftmax_le_coupling_cost {n : ℕ} (hn : 0 < n)
    (p : Fin n → ℝ) (tau : ℝ) :
    wasserstein1 (gumbelSoftmaxLaw p tau) (gumbelHardLaw p) ≤
      ∫⁻ G, edist (softmaxWeights p tau G) (hardWeights p G) ∂gumbelInputs n := by
  let := gumbelInputs_probability n
  let : BorelSpace (L1Vec n) := ⟨rfl⟩
  let pair := fun G => (softmaxWeights p tau G, hardWeights p G)
  have hp : Measurable pair := (softmaxWeights_measurable p tau).prodMk
    (hardWeights_measurable hn p)
  have hc : (gumbelInputs n).map pair ∈
      couplings (gumbelSoftmaxLaw p tau) (gumbelHardLaw p) := by
    refine ⟨Measure.isProbabilityMeasure_map hp.aemeasurable, ?_, ?_⟩
    · rw [Measure.map_map measurable_fst hp]
      rfl
    · rw [Measure.map_map measurable_snd hp]
      rfl
  calc
    wasserstein1 (gumbelSoftmaxLaw p tau) (gumbelHardLaw p) ≤
        ∫⁻ z, edist z.1 z.2 ∂(gumbelInputs n).map pair :=
      (wasserstein1_eq_couplings _ _).trans_le (iInf_le_of_le ⟨_, hc⟩ le_rfl)
    _ = _ := by rw [lintegral_map (by fun_prop) hp]

-- @node: gumbelLaw_nullSingleton
/-- [Every singleton has probability zero under the standard Gumbel law](goal). -/
lemma gumbelLaw_nullSingleton : NullSingletonClass gumbelLaw := by
  let := gumbelLaw_probability
  refine ⟨fun a => ?_⟩
  rw [← measure_cdf gumbelLaw, StieltjesFunction.measure_singleton]
  have hc : Continuous (fun x => cdf gumbelLaw x) := by
    simp_rw [gumbelLaw_cdf]
    fun_prop
  rw [hc.continuousAt.continuousWithinAt.leftLim_eq]
  simp

-- @node: gumbel_pair_oneSided_gap_le
/-- [For two independent standard Gumbel draws shifted by a and b, the probability that the first shifted draw minus the second is nonnegative and strictly less than delta is at most the nonnegative part of delta exp(−1)](goal). -/
lemma gumbel_pair_oneSided_gap_le (a b delta : ℝ) :
    (gumbelLaw.prod gumbelLaw) {z : ℝ × ℝ |
      0 ≤ (a + z.1) - (b + z.2) ∧ (a + z.1) - (b + z.2) < delta} ≤
      ENNReal.ofReal (delta * Real.exp (-1)) := by
  let := gumbelLaw_probability
  let := gumbelLaw_nullSingleton
  have hm : MeasurableSet {z : ℝ × ℝ |
      0 ≤ (a + z.1) - (b + z.2) ∧ (a + z.1) - (b + z.2) < delta} := by
    have hf : Measurable (fun z : ℝ × ℝ => (a+z.1)-(b+z.2)) := by fun_prop
    exact (measurableSet_le measurable_const hf).inter
      (measurableSet_lt hf measurable_const)
  rw [Measure.prod_apply_symm hm]
  calc
    (∫⁻ y, gumbelLaw ((fun x => (x, y)) ⁻¹' {z : ℝ × ℝ |
        0 ≤ (a + z.1) - (b + z.2) ∧ (a + z.1) - (b + z.2) < delta}) ∂gumbelLaw) ≤
        ∫⁻ _y, ENNReal.ofReal (delta * Real.exp (-1)) ∂gumbelLaw := by
      apply lintegral_mono
      intro y
      calc
        _ ≤ gumbelLaw (Set.Icc (b+y-a) (b+y-a+delta)) := by
          apply measure_mono
          intro x hx
          change 0 ≤ (a+x)-(b+y) ∧ (a+x)-(b+y) < delta at hx
          constructor <;> linarith [hx.1, hx.2]
        _ = gumbelLaw (Set.Ioc (b+y-a) (b+y-a+delta)) :=
          (measure_congr (Ioc_ae_eq_Icc (μ := gumbelLaw))).symm
        _ ≤ _ := by
          simpa only [add_sub_cancel_left] using gumbelLaw_Ioc_le (b+y-a) (b+y-a+delta)
    _ = _ := by simp

-- @node: gumbelInputs_pair_map
/-- If [i and j are distinct categories](hyp:hij), then [the joint law of their Gumbel inputs is the product of two standard Gumbel laws](goal). -/
lemma gumbelInputs_pair_map {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    (gumbelInputs n).map (fun G => (G i, G j)) = gumbelLaw.prod gumbelLaw := by
  let := gumbelLaw_probability
  have hind := iIndepFun_pi (μ := fun _ : Fin n => gumbelLaw)
    (X := fun _ => (id : ℝ → ℝ)) (fun _ => measurable_id.aemeasurable)
  have hpair := (hind.indepFun hij).map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
  simpa only [gumbelInputs, id_eq, (measurePreserving_eval (fun _ : Fin n => gumbelLaw) i).map_eq,
    (measurePreserving_eval (fun _ : Fin n => gumbelLaw) j).map_eq] using hpair

-- @node: gumbelInputs_oneSided_gap_le
/-- If [i and j are distinct categories](hyp:hij), then [the probability that the log-weight-shifted Gumbel score of i minus that of j is nonnegative and strictly less than delta is at most the nonnegative part of delta exp(−1)](goal). -/
lemma gumbelInputs_oneSided_gap_le {n : ℕ} (p : Fin n → ℝ) (i j : Fin n)
    (hij : i ≠ j) (delta : ℝ) :
    (gumbelInputs n) {G |
      0 ≤ (Real.log (p i) + G i) - (Real.log (p j) + G j) ∧
        (Real.log (p i) + G i) - (Real.log (p j) + G j) < delta} ≤
      ENNReal.ofReal (delta * Real.exp (-1)) := by
  have hm : MeasurableSet {z : ℝ × ℝ |
      0 ≤ (Real.log (p i) + z.1) - (Real.log (p j) + z.2) ∧
        (Real.log (p i) + z.1) - (Real.log (p j) + z.2) < delta} := by
    have hf : Measurable (fun z : ℝ × ℝ =>
      (Real.log (p i) + z.1) - (Real.log (p j) + z.2)) := by fun_prop
    exact (measurableSet_le measurable_const hf).inter
      (measurableSet_lt hf measurable_const)
  have h := gumbel_pair_oneSided_gap_le (Real.log (p i)) (Real.log (p j)) delta
  rw [← gumbelInputs_pair_map i j hij, Measure.map_apply (by fun_prop) hm] at h
  exact h

-- @node: gumbelNearTie
/-- For [category weights p](hyp:p) and [a gap threshold delta](hyp:delta), the [near-tie event](goal) consists of input vectors for which some ordered pair of distinct categories has a nonnegative difference of log-weight-shifted scores strictly less than delta. -/
def gumbelNearTie {n : ℕ} (p : Fin n → ℝ) (delta : ℝ) : Set (Fin n → ℝ) :=
  ⋃ ij : (Finset.univ : Finset (Fin n)).offDiag,
    {G | 0 ≤ (Real.log (p ij.val.1) + G ij.val.1) -
        (Real.log (p ij.val.2) + G ij.val.2) ∧
      (Real.log (p ij.val.1) + G ij.val.1) -
        (Real.log (p ij.val.2) + G ij.val.2) < delta}

-- @node: gumbelNearTie_measurableSet
/-- [The event that some pair of distinct log-weight-shifted input scores has a nonnegative gap strictly less than delta is measurable](goal). -/
lemma gumbelNearTie_measurableSet {n : ℕ} (p : Fin n → ℝ) (delta : ℝ) :
    MeasurableSet (gumbelNearTie p delta) := by
  apply MeasurableSet.iUnion
  intro ij
  have hf : Measurable (fun G : Fin n → ℝ =>
      (Real.log (p ij.val.1) + G ij.val.1) -
        (Real.log (p ij.val.2) + G ij.val.2)) := by fun_prop
  exact (measurableSet_le measurable_const hf).inter (measurableSet_lt hf measurable_const)

-- @node: gumbelNearTie_measure_le
/-- [Under independent standard Gumbel inputs, the probability of a near tie at threshold delta is at most the nonnegative part of n(n − 1) delta exp(−1)](goal). -/
lemma gumbelNearTie_measure_le {n : ℕ} (p : Fin n → ℝ) (delta : ℝ) :
    (gumbelInputs n) (gumbelNearTie p delta) ≤
      ENNReal.ofReal ((n : ℝ) * (n-1 : ℕ) * delta * Real.exp (-1)) := by
  classical
  calc
    (gumbelInputs n) (gumbelNearTie p delta) ≤
        ∑ ij : (Finset.univ : Finset (Fin n)).offDiag,
          (gumbelInputs n) {G |
            0 ≤ (Real.log (p ij.val.1) + G ij.val.1) -
              (Real.log (p ij.val.2) + G ij.val.2) ∧
            (Real.log (p ij.val.1) + G ij.val.1) -
              (Real.log (p ij.val.2) + G ij.val.2) < delta} := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _ij : (Finset.univ : Finset (Fin n)).offDiag,
        ENNReal.ofReal (delta * Real.exp (-1)) := by
      apply Finset.sum_le_sum
      intro ij _
      exact gumbelInputs_oneSided_gap_le p _ _ (Finset.mem_offDiag.mp ij.property).2.2 delta
    _ = _ := by
      have hc : ((Finset.univ : Finset (Fin n)).offDiag).card = n * (n-1) := by
        simp only [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
        rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, hc, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      push_cast
      ring

-- @node: firstArgmax_log_score_maximizes
/-- If [all weights are strictly positive](hyp:hp) and [j is the first category maximizing the extended log weight plus input score](hyp:hj), then [every category k has log weight plus input score at most that of j](goal). -/
lemma firstArgmax_log_score_maximizes {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ k, 0 < p k) (G : Fin n → ℝ) (j : Fin n)
    (hj : firstArgmax (fun k => extendedLog (p k) + (G k : EReal)) = some j)
    (k : Fin n) : Real.log (p k) + G k ≤ Real.log (p j) + G j := by
  have h := firstArgmax_maximizes _ j hj k
  simpa [extendedLog, ne_of_gt (hp k), ne_of_gt (hp j), ← EReal.coe_add] using h

-- @node: gumbelSoftmax_coupling_cost_le_threshold
/-- Suppose [there is at least one category](hyp:hn), [all weights are strictly positive](hyp:hp), [the temperature tau is strictly positive](hyp:htau), and [the threshold delta is nonnegative](hyp:hdelta). Then [the expected sum of absolute coordinate differences between the soft and hard selectors using the same Gumbel inputs is at most 2 delta n(n − 1) exp(−1) + 2(n − 1) exp(−delta / tau)](goal). -/
lemma gumbelSoftmax_coupling_cost_le_threshold {n : ℕ} (hn : 0 < n)
    (p : Fin n → ℝ) (hp : ∀ k, 0 < p k) {tau : ℝ} (htau : 0 < tau)
    (delta : ℝ) (hdelta : 0 ≤ delta) :
    (∫⁻ G, edist (softmaxWeights p tau G) (hardWeights p G) ∂gumbelInputs n) ≤
      ENNReal.ofReal (2 * delta * n * (n-1 : ℕ) * Real.exp (-1) +
        2 * (n-1 : ℕ) * Real.exp (-delta / tau)) := by
  classical
  let := gumbelInputs_probability n
  let := gumbelLaw_probability
  let E := gumbelNearTie p delta
  let c : ℝ := 2 * (n-1 : ℕ) * Real.exp (-delta / tau)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hm : MeasurableSet E := gumbelNearTie_measurableSet p delta
  have hpoint : ∀ G, edist (softmaxWeights p tau G) (hardWeights p G) ≤
      E.indicator (fun _ => (2 : ℝ≥0∞)) G + ENNReal.ofReal c := by
    intro G
    by_cases hG : G ∈ E
    · rw [Set.indicator_of_mem hG, edist_dist]
      exact (ENNReal.ofReal_le_ofReal (softmaxWeights_hardWeights_dist_le_two hn p hp tau G)).trans
        (by simp)
    · rw [Set.indicator_of_notMem hG, zero_add, edist_dist]
      obtain ⟨j, hj⟩ := firstArgmax_exists hn (fun k => extendedLog (p k) + (G k : EReal))
      apply ENNReal.ofReal_le_ofReal
      apply softmaxWeights_hardWeights_dist_le_of_gap hn p hp htau G j delta hj
      intro k hkj
      have hmax := firstArgmax_log_score_maximizes p hp G j hj k
      have hnot : ¬ (Real.log (p j) + G j) - (Real.log (p k) + G k) < delta := by
        intro hsmall
        apply hG
        apply Set.mem_iUnion.mpr
        refine ⟨⟨(j,k), by simp [hkj.symm]⟩, ?_⟩
        exact ⟨sub_nonneg.mpr hmax, hsmall⟩
      linarith [le_of_not_gt hnot]
  calc
    (∫⁻ G, edist (softmaxWeights p tau G) (hardWeights p G) ∂gumbelInputs n) ≤ ∫⁻ G, E.indicator (fun _ => (2 : ℝ≥0∞)) G + ENNReal.ofReal c ∂gumbelInputs n :=
      lintegral_mono hpoint
    _ = 2 * (gumbelInputs n) E + ENNReal.ofReal c := by
      rw [lintegral_add_left (measurable_const.indicator hm), lintegral_indicator hm]
      simp
    _ ≤ 2 * ENNReal.ofReal ((n : ℝ) * (n-1 : ℕ) * delta * Real.exp (-1)) +
        ENNReal.ofReal c := by
      gcongr
      exact gumbelNearTie_measure_le p delta
    _ = _ := by
      rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_add (by positivity) hc]
      congr 1
      dsimp [c]
      ring

-- @node: wasserstein_gumbelSoftmax_le_threshold
/-- Suppose [there is at least one category](hyp:hn), [all weights are strictly positive](hyp:hp), [the temperature tau is strictly positive](hyp:htau), and [the threshold delta is nonnegative](hyp:hdelta). Then [the Wasserstein distance of order one between the soft and hard selector laws is at most 2 delta n(n − 1) exp(−1) + 2(n − 1) exp(−delta / tau)](goal). -/
lemma wasserstein_gumbelSoftmax_le_threshold {n : ℕ} (hn : 0 < n)
    (p : Fin n → ℝ) (hp : ∀ k, 0 < p k) {tau : ℝ} (htau : 0 < tau)
    (delta : ℝ) (hdelta : 0 ≤ delta) :
    wasserstein1 (gumbelSoftmaxLaw p tau) (gumbelHardLaw p) ≤
      ENNReal.ofReal (2 * delta * n * (n-1 : ℕ) * Real.exp (-1) +
        2 * (n-1 : ℕ) * Real.exp (-delta / tau)) := by
  exact (wasserstein_gumbelSoftmax_le_coupling_cost hn p tau).trans
    (gumbelSoftmax_coupling_cost_le_threshold hn p hp htau delta hdelta)

-- @node: gumbelSoftmax_coupling_cost_le
/-- If [there is at least one category](hyp:hn) and [all weights are strictly positive and the temperature tau lies strictly between zero and one](hyp:hparameters), then [the expected sum of absolute coordinate differences between the soft and hard selectors using the same Gumbel inputs is at most 2(n − 1) tau − 2n(n − 1) exp(−1) tau log(tau)](goal). -/
lemma gumbelSoftmax_coupling_cost_le {n : ℕ} (hn : 1 ≤ n)
    (p : Fin n → ℝ) (tau : ℝ) (hparameters : SoftmaxParameters p tau) :
    (∫⁻ G, edist (softmaxWeights p tau G) (hardWeights p G) ∂gumbelInputs n) ≤
      ENNReal.ofReal (2 * (n-1 : ℕ) * tau -
        2 * n * (n-1 : ℕ) * Real.exp (-1) * tau * Real.log tau) := by
  rcases hparameters with ⟨htau, htau_one, hp⟩
  have hlog : Real.log tau < 0 := Real.log_neg htau htau_one
  have hdelta : 0 ≤ -tau * Real.log tau := mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr htau.le)
    hlog.le
  have hb := gumbelSoftmax_coupling_cost_le_threshold (by omega) p hp htau
    (-tau * Real.log tau) hdelta
  have heq : -(-tau * Real.log tau) / tau = Real.log tau := by
    field_simp
  have hexp : Real.exp (-(-tau * Real.log tau) / tau) = tau := by
    rw [heq, Real.exp_log htau]
  calc
    _ ≤ ENNReal.ofReal (2 * (-tau * Real.log tau) * n * (n-1 : ℕ) * Real.exp (-1) +
        2 * (n-1 : ℕ) * Real.exp (-(-tau * Real.log tau) / tau)) := hb
    _ = _ := by
      rw [hexp]
      congr 1
      ring

-- @node: lem:gumbel-err
/-- If [there is at least one category](hyp:hn) and [all weights are strictly positive and the temperature tau lies strictly between zero and one](hyp:hparameters), then [the Wasserstein distance of order one between the soft and hard selector laws is at most 2(n − 1) tau − 2n(n − 1) exp(−1) tau log(tau)](goal). -/
lemma wasserstein_gumbelSoftmax_le {n : ℕ} (hn : 1 ≤ n)
    (p : Fin n → ℝ) (tau : ℝ) (hparameters : SoftmaxParameters p tau) :
    wasserstein1 (gumbelSoftmaxLaw p tau) (gumbelHardLaw p) ≤
      ENNReal.ofReal (2 * (n-1 : ℕ) * tau -
        2 * n * (n-1 : ℕ) * Real.exp (-1) * tau * Real.log tau) := by
  exact (wasserstein_gumbelSoftmax_le_coupling_cost (by omega) p tau).trans
    (gumbelSoftmax_coupling_cost_le hn p tau hparameters)
-- @node: gumbel_scores_ne_ae
/-- [With probability one under independent standard Gumbel inputs, every pair of distinct categories has unequal scores after adding the log weights](goal). -/
lemma gumbel_scores_ne_ae {n : ℕ} (p : Fin n → ℝ) :
    ∀ᵐ G ∂gumbelInputs n, ∀ i j, i ≠ j →
      Real.log (p i) + G i ≠ Real.log (p j) + G j := by
  letI := gumbelLaw_probability
  letI := gumbelLaw_nullSingleton
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall (fun _ h => (h hij).elim)
  have hm : MeasurableSet {z : ℝ × ℝ |
      Real.log (p i) + z.1 = Real.log (p j) + z.2} := by
    apply measurableSet_eq_fun <;> fun_prop
  have hz : (gumbelLaw.prod gumbelLaw) {z : ℝ × ℝ |
      Real.log (p i) + z.1 = Real.log (p j) + z.2} = 0 := by
    rw [Measure.prod_apply_symm hm]
    have he (y : ℝ) : (fun x => (x,y)) ⁻¹' {z : ℝ × ℝ |
        Real.log (p i) + z.1 = Real.log (p j) + z.2} =
        {Real.log (p j) + y - Real.log (p i)} := by
      ext x
      change Real.log (p i) + x = Real.log (p j) + y ↔
        x = Real.log (p j) + y - Real.log (p i)
      constructor <;> intro h <;> linarith
    simp_rw [he, measure_singleton, lintegral_zero]
  rw [← gumbelInputs_pair_map i j hij,
    Measure.map_apply (by fun_prop) hm] at hz
  have hne : ∀ᵐ G ∂gumbelInputs n,
      Real.log (p i) + G i ≠ Real.log (p j) + G j := by
    simpa only [ae_iff, not_not, Set.preimage_setOf_eq] using hz
  exact hne.mono (fun _ h _ => h)

-- @node: softmaxWeights_tendsto_hardWeights_ae
/-- If [there is at least one category](hyp:hn) and [all weights are strictly positive](hyp:hp), then [for almost every vector of independent standard Gumbel inputs, the soft selector converges to the hard selector on that same input vector as the temperature tends to zero through positive values](goal). -/
lemma softmaxWeights_tendsto_hardWeights_ae {n : ℕ} (hn : 0 < n)
    (p : Fin n → ℝ) (hp : ∀ j, 0 < p j) :
    ∀ᵐ g ∂gumbelInputs n, Filter.Tendsto (fun tau => softmaxWeights p tau g)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (hardWeights p g)) := by
  classical
  filter_upwards [gumbel_scores_ne_ae p] with G hG
  obtain ⟨j, hj⟩ := firstArgmax_exists hn (fun k => extendedLog (p k) + (G k : EReal))
  have hlose (k : Fin n) (hk : k ∈ Finset.univ.erase j) :
      Filter.Tendsto (fun tau => (softmaxWeights p tau G).ofLp k)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hkj := Finset.ne_of_mem_erase hk
    have hlt : Real.log (p k) + G k < Real.log (p j) + G j :=
      lt_of_le_of_ne (firstArgmax_log_score_maximizes p hp G j hj k) (hG k j hkj)
    have hexp : Filter.Tendsto
        (fun tau : ℝ => Real.exp (-(Real.log (p j) + G j -
          (Real.log (p k) + G k)) / tau))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      simp only [div_eq_mul_inv]
      exact Real.tendsto_exp_atBot.comp
        (Filter.Tendsto.const_mul_atTop_of_neg (by linarith)
          tendsto_inv_nhdsGT_zero)
    apply squeeze_zero' (Filter.Eventually.of_forall
      (fun tau => softmaxWeights_nonneg p tau G k)) _ hexp
    filter_upwards [self_mem_nhdsWithin] with tau htau
    exact softmaxWeights_le_exp_of_gap hn p hp htau G j k _ (by linarith)
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hs := tendsto_finset_sum (Finset.univ.erase j) hlose
  have hdist := hs.const_mul 2
  simpa only [softmaxWeights_hardWeights_dist hn p hp _ G j hj,
    Finset.sum_const_zero, mul_zero] using hdist

-- @node: def:lemma-gumbel-err-softmax
/-- Given [a positive number of categories](hyp:hn), [category weights p](hyp:p) that [are all strictly positive](hyp:hp), and [a temperature tau](hyp:tau) that [is strictly positive](hyp:htau), the [Gumbel-softmax construction](goal) first forms [the family of soft selectors and the hard selector on common independent Gumbel inputs, together with their almost-sure convergence as temperature decreases to zero](step:1), and then returns [this certified pair together with the soft law at temperature tau and the hard law](step:2). -/
noncomputable def gumbelSoftmaxConstruction {n : ℕ} (hn : 0 < n) -- @realizes n(positive softmax dimension)
    (p : Fin n → ℝ) (hp : ∀ j, 0 < p j) -- @realizes p_i(strictly positive weights, with no normalization requirement)
    (tau : ℝ) (htau : 0 < tau) := -- @realizes \tau(positive temperature for the selected soft law)
  let vectors : {v : (ℝ → (Fin n → ℝ) → L1Vec n) × ((Fin n → ℝ) → L1Vec n) //
      ∀ᵐ g ∂gumbelInputs n, Filter.Tendsto (fun tau => v.1 tau g)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (v.2 g))} := -- @realizes X^0(almost-sure zero-temperature limit using the same Gumbel inputs)
    ⟨(softmaxWeights p, hardWeights p), softmaxWeights_tendsto_hardWeights_ae hn p hp⟩
  (vectors, (gumbelInputs n).map (vectors.val.1 tau), -- @realizes \mu^\tau(law of the positive-temperature vector on the same Gumbel inputs)
    (gumbelInputs n).map vectors.val.2) -- @realizes \mu^0(law of its almost-sure limit on those inputs)

end Papers.TbsNeuralCausalPi
