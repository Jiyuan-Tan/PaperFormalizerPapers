module
public import Papers.TbsNeuralCausalPi.Helpers.EmpiricalTransportMeasurability
public import Papers.TbsNeuralCausalPi.Setup.CitedResults
/-! # Euclidean source concentration for one-norm laws

A change of finite-dimensional norm transports the cited empirical tail.
All constants are fixed before the sample size and tolerance.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- For [a dimension d](hyp:d), [the continuous linear equivalence between
one-norm vectors and Euclidean vectors](goal) preserves all d real coordinates
while changing the norm from the one-norm to the Euclidean norm. -/
-- @node: l1EuclideanEquiv
def l1EuclideanEquiv (d : ℕ) : L1Vec d ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
  (PiLp.continuousLinearEquiv 1 ℝ (fun _ : Fin d => ℝ)).trans
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm

/-- If [R is nonnegative](hyp:_hR) and [a probability law on d-dimensional
one-norm vectors has norm at most R almost surely](hyp:hmu), [the exponential
of the squared Euclidean norm is integrable under the same law transported
to Euclidean space](goal). -/
-- @node: l1Euclidean_integrable_exp_sq
lemma l1Euclidean_integrable_exp_sq (d : ℕ) (mu : ProbabilityMeasure (L1Vec d))
    (R : ℝ) (_hR : 0 ≤ R) (hmu : ∀ᵐ z ∂(mu : Measure (L1Vec d)), ‖z‖ ≤ R) :
    Integrable (fun z : EuclideanSpace ℝ (Fin d) => Real.exp (‖z‖ ^ (2 : ℝ)))
      ((mu : Measure (L1Vec d)).map (l1EuclideanEquiv d)) := by
  simp only [Real.rpow_two]
  apply Integrable.of_bound (by fun_prop)
    (Real.exp ((‖(l1EuclideanEquiv d).toContinuousLinearMap‖ * R)^2))
  apply (ae_map_iff (by fun_prop)
    (measurableSet_le (by fun_prop) measurable_const)).mpr
  filter_upwards [hmu] with z hz
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  exact ((l1EuclideanEquiv d).toContinuousLinearMap.le_opNorm z).trans
    (mul_le_mul_of_nonneg_left hz (norm_nonneg _))

/-- If [k is at least one](hyp:hk) and [x is positive](hyp:hx), [the logarithm
of two plus k divided by x is at most the product of one plus log k divided
by log two and the logarithm of two plus the reciprocal of x](goal). -/
-- @node: fournier_critical_log_rescale
lemma fournier_critical_log_rescale {k x : ℝ} (hk : 1 ≤ k) (hx : 0 < x) :
    Real.log (2 + (x/k)⁻¹) ≤
      (1 + Real.log k / Real.log 2) * Real.log (2 + x⁻¹) := by
  have hk0 : 0 < k := zero_lt_one.trans_le hk
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogk : 0 ≤ Real.log k := Real.log_nonneg hk
  have hlog2 : Real.log 2 ≤ Real.log (2 + x⁻¹) :=
    Real.log_le_log (by norm_num) (le_add_of_nonneg_right (inv_nonneg.mpr hx.le))
  have hmul := mul_le_mul_of_nonneg_left hlog2
    (div_nonneg hlogk htwo.le)
  rw [div_mul_cancel₀ _ htwo.ne'] at hmul
  calc
    Real.log (2 + (x/k)⁻¹) ≤ Real.log (k * (2 + x⁻¹)) := by
      apply Real.log_le_log (by positivity)
      rw [inv_div, div_eq_mul_inv]
      nlinarith
    _ = Real.log k + Real.log (2 + x⁻¹) :=
      Real.log_mul hk0.ne' (by positivity)
    _ ≤ _ := by nlinarith

/-- If [k is at least one](hyp:hk), [there is a positive constant a such that,
for every x strictly between zero and one, a times the dimension-dependent
exponent at x is at most that exponent evaluated at the ratio of x to k: the
exponent at a positive tolerance is its square in dimension one, the squared
ratio of the tolerance to the logarithm of two plus its reciprocal in dimension
two, and the tolerance to the power d otherwise](goal). -/
-- @node: fournier_exponent_rescale
lemma fournier_exponent_rescale (d : ℕ) {k : ℝ} (hk : 1 ≤ k) :
    ∃ a : ℝ, 0 < a ∧ ∀ x : ℝ, 0 < x → x < 1 →
      a * (if d = 1 then x^2 else if d = 2 then
        (x / Real.log (2 + x⁻¹))^2 else x^d) ≤
      (if d = 1 then (x/k)^2 else if d = 2 then
        ((x/k) / Real.log (2 + (x/k)⁻¹))^2 else (x/k)^d) := by
  let q := k * (1 + Real.log k / Real.log 2)
  have hk0 : 0 < k := zero_lt_one.trans_le hk
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hqk : k ≤ q := by
    dsimp [q]
    have h := div_nonneg (Real.log_nonneg hk) htwo.le
    nlinarith
  have hq : 0 < q := hk0.trans_le hqk
  refine ⟨min (q⁻¹ ^ 2) (k⁻¹ ^ d), lt_min (by positivity) (by positivity), ?_⟩
  intro x hx _hx1
  have ha2 := min_le_left (q⁻¹ ^ 2) (k⁻¹ ^ d)
  have had := min_le_right (q⁻¹ ^ 2) (k⁻¹ ^ d)
  split_ifs with hd1 hd2
  · calc
      _ ≤ q⁻¹ ^ 2 * x^2 := mul_le_mul_of_nonneg_right ha2 (sq_nonneg x)
      _ = (x/q)^2 := by ring
      _ ≤ (x/k)^2 := pow_le_pow_left₀ (by positivity)
        (div_le_div_of_nonneg_left hx.le hk0 hqk) 2
  · have hL : 0 < Real.log (2 + x⁻¹) := Real.log_pos (by linarith [inv_pos.mpr hx])
    have hLk : 0 < Real.log (2 + (x/k)⁻¹) :=
      Real.log_pos (by linarith [inv_pos.mpr (div_pos hx hk0)])
    have hlog := fournier_critical_log_rescale hk hx
    have hden : k * Real.log (2 + (x/k)⁻¹) ≤ Real.log (2 + x⁻¹) * q := by
      dsimp [q]
      nlinarith
    have hratio : (x / Real.log (2 + x⁻¹)) / q ≤
        (x/k) / Real.log (2 + (x/k)⁻¹) := by
      rw [div_div, div_div]
      exact div_le_div_of_nonneg_left hx.le (mul_pos hk0 hLk) hden
    calc
      _ ≤ q⁻¹ ^ 2 * (x / Real.log (2 + x⁻¹))^2 :=
        mul_le_mul_of_nonneg_right ha2 (sq_nonneg _)
      _ = ((x / Real.log (2 + x⁻¹)) / q)^2 := by ring
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hratio 2
  · calc
      _ ≤ k⁻¹ ^ d * x^d := mul_le_mul_of_nonneg_right had (by positivity)
      _ = (x/k)^d := by rw [div_eq_mul_inv, mul_pow, mul_comm]

/-- Assume [the Fournier–Guillin small-deviation bound](hyp:hFG), [a positive
dimension d](hyp:hd), [a nonnegative radius R](hyp:hR), and [a probability law
on one-norm vectors whose norm is at most R almost surely](hyp:hmu). Then
[there are positive constants C and c and a scale factor k at least one such
that, for every positive sample size N and tolerance x strictly between zero
and one, the probability that the empirical first Wasserstein error exceeds x
is at most C times the exponential of minus c times N times the exponent
evaluated at the ratio of x to k; that exponent is the squared tolerance in
dimension one, the squared ratio of the tolerance to the logarithm of two plus its reciprocal in
dimension two, and the tolerance to the power d otherwise](goal). -/
-- @node: fournier_l1_tail_rescaled
lemma fournier_l1_tail_rescaled
    (hFG : FournierGuillinSmallDeviation) (d : ℕ) (hd : 0 < d)
    (mu : ProbabilityMeasure (L1Vec d))
    (R : ℝ) (hR : 0 ≤ R) (hmu : ∀ᵐ z ∂(mu : Measure (L1Vec d)), ‖z‖ ≤ R) :
    ∃ C c k : ℝ, 0 < C ∧ 0 < c ∧ 1 ≤ k ∧
      ∀ N : ℕ, 0 < N → ∀ x : ℝ, 0 < x → x < 1 →
        (Measure.pi (fun _ : Fin N => (mu : Measure (L1Vec d))))
          {z | ¬ wasserstein1 (mu : Measure (L1Vec d)) (empiricalMeasure z) ≤ ENNReal.ofReal x} ≤
        ENNReal.ofReal (C * Real.exp (-c * N *
          (if d = 1 then (x/k)^2 else if d = 2 then
            ((x/k) / Real.log (2 + (x/k)⁻¹))^2 else (x/k)^d))) := by
  let E := l1EuclideanEquiv d
  let nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) :=
    mu.map (by fun_prop : Measurable E).aemeasurable
  have hmoment := l1Euclidean_integrable_exp_sq d mu R hR hmu
  obtain ⟨C, c, hC, hc, htail⟩ := hFG d hd 2 1
    (∫ z, Real.exp (‖z‖ ^ (2 : ℝ)) ∂(nu : Measure (EuclideanSpace ℝ (Fin d))))
    (by norm_num) (by norm_num)
  let k : ℝ≥0 := max 1 ‖E.symm.toContinuousLinearMap‖₊
  have hk1 : (1 : ℝ) ≤ k := by
    exact_mod_cast (le_max_left 1 ‖E.symm.toContinuousLinearMap‖₊)
  have hk : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk1
  refine ⟨C, c, k, hC, hc, hk1, ?_⟩
  intro N hN x hx hx1
  have hxk : 0 < x / k := div_pos hx hk
  have hxk1 : x / k ≤ 1 := (div_le_self hx.le hk1).trans hx1.le
  have hsource := htail nu
    (by simpa only [one_mul, nu, E, ProbabilityMeasure.toMeasure_map] using hmoment)
    (by simp) N hN
    (x/k) hxk hxk1
  have hi : (nu : Measure (EuclideanSpace ℝ (Fin d))).map E.symm = (mu : Measure (L1Vec d)) := by
    change ((mu : Measure (L1Vec d)).map E).map E.symm = _
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    simp only [Function.comp_def, E.symm_apply_apply]
    rw [show (fun x : L1Vec d => x) = id from rfl, Measure.map_id]
  have hEL : LipschitzWith k E.symm :=
    E.symm.toContinuousLinearMap.lipschitz.weaken (le_max_right _ _)
  have hsub : {z : Fin N → L1Vec d | ¬ wasserstein1 (mu : Measure (L1Vec d))
      (empiricalMeasure z) ≤ ENNReal.ofReal x} ⊆
      (fun z i => E (z i)) ⁻¹'
      {z | ENNReal.ofReal (x/k) ≤
        wasserstein1 (empiricalMeasure z) (nu : Measure (EuclideanSpace ℝ (Fin d)))} := by
    intro z hz
    change ENNReal.ofReal (x/k) ≤
      wasserstein1 (empiricalMeasure (fun i => E (z i)))
        (nu : Measure (EuclideanSpace ℝ (Fin d)))
    by_contra hbad
    apply hz
    have ht := empirical_pushforward_wasserstein_le (nu : Measure (EuclideanSpace ℝ (Fin d))) hN
      (fun i => E (z i)) E.symm k hEL
    rw [hi] at ht
    simp only [E.symm_apply_apply] at ht
    have hgood : wasserstein1 (nu : Measure (EuclideanSpace ℝ (Fin d)))
        (empiricalMeasure (fun i => E (z i))) ≤
        ENNReal.ofReal (x/k) := by
      have hs := wasserstein1_symm nu
        ⟨empiricalMeasure (fun i => E (z i)), empiricalMeasure_probability hN _⟩
      simp only [ProbabilityMeasure.coe_mk] at hs
      rw [hs]
      exact (lt_of_not_ge hbad).le
    calc
      _ ≤ (k : ℝ≥0∞) * wasserstein1 (nu : Measure (EuclideanSpace ℝ (Fin d)))
          (empiricalMeasure (fun i => E (z i))) := ht
      _ ≤ (k : ℝ≥0∞) * ENNReal.ofReal (x/k) := by gcongr
      _ = ENNReal.ofReal x := by
        rw [show (k : ℝ≥0∞) = ENNReal.ofReal (k : ℝ) by simp,
          ← ENNReal.ofReal_mul k.coe_nonneg, mul_div_cancel₀ _ hk.ne']
  have hpi : Measurable (fun z : Fin N → L1Vec d => fun i => E (z i)) :=
    measurable_pi_lambda _ (fun i => E.continuous.measurable.comp (measurable_pi_apply i))
  refine (measure_mono hsub).trans ((Measure.le_map_apply hpi.aemeasurable _).trans ?_)
  rw [Measure.pi_map_pi (fun _ => (show Measurable E by fun_prop).aemeasurable)]
  simpa only [nu, ProbabilityMeasure.toMeasure_map, empiricalMeasure] using hsource

/-- Assume [the Fournier–Guillin small-deviation bound](hyp:hFG), [a positive
dimension d](hyp:hd), [a nonnegative radius R](hyp:hR), and [a probability law
on one-norm vectors whose norm is at most R almost surely](hyp:hmu). Then
[there are positive constants C and c such that, for every positive sample size
N and tolerance x strictly between zero and one, the probability that the
empirical first Wasserstein error exceeds x is at most C times the exponential
of minus c times N times a dimension-dependent factor: x squared in dimension
one, the squared ratio of x to the logarithm of two plus its reciprocal in
dimension two, and x to the power d otherwise](goal). -/
-- @node: fournier_l1_exponential_bound
lemma fournier_l1_exponential_bound
    (hFG : FournierGuillinSmallDeviation) (d : ℕ) (hd : 0 < d)
    (mu : ProbabilityMeasure (L1Vec d))
    (R : ℝ) (hR : 0 ≤ R) (hmu : ∀ᵐ z ∂(mu : Measure (L1Vec d)), ‖z‖ ≤ R) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ N : ℕ, 0 < N → ∀ x : ℝ, 0 < x → x < 1 →
        (Measure.pi (fun _ : Fin N => (mu : Measure (L1Vec d))))
          {z | ¬ wasserstein1 (mu : Measure (L1Vec d))
            (empiricalMeasure z) ≤ ENNReal.ofReal x} ≤
        ENNReal.ofReal (C * Real.exp (-c * N *
          (if d = 1 then x^2 else if d = 2 then
            (x / Real.log (2 + x⁻¹))^2 else x^d))) := by
  obtain ⟨C, c, k, hC, hc, hk, ht⟩ := fournier_l1_tail_rescaled hFG d hd mu R hR hmu
  obtain ⟨a, ha, hexp⟩ := fournier_exponent_rescale d hk
  refine ⟨C, c * a, hC, mul_pos hc ha, ?_⟩
  intro N hN x hx hx1
  refine (ht N hN x hx hx1).trans (ENNReal.ofReal_le_ofReal ?_)
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (hexp x hx hx1)
    (mul_nonneg hc.le (show (0 : ℝ) ≤ N by positivity))
  nlinarith

end
end Papers.TbsNeuralCausalPi
