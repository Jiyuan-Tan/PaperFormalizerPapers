module
public import Papers.TbsNeuralCausalPi.Setup.Assumptions.Estimation
/-! # Vanishing sampling tolerances under the estimation growth schedule

The depth exponent is strictly below one half. Logarithmic factors therefore
preserve convergence of both sampling terms, including the squared logarithm
in the observational term.
-/
public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.whitespace false
open Filter Asymptotics
open scoped Topology

-- @node: estimation_log_pow_mul_neg_rpow_tendsto
/-- For [a positive exponent](hyp:hp), [the negative power of a real variable
times any fixed nonnegative integer power of its logarithm tends to zero as
the variable tends to infinity](goal). -/
lemma estimation_log_pow_mul_neg_rpow_tendsto {p : ℝ} (hp : 0 < p) (k : ℕ) :
    Tendsto (fun x : ℝ => x ^ (-p) * (Real.log x)^k) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (k : ℝ) hp).tendsto_div_nhds_zero
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.rpow_natCast, Real.rpow_neg hx.le]
  ring

-- @node: estimation_depth_sampling_tendsto
/-- If [the simulation size tends to infinity](hyp:hm), [the depth exponent is
strictly below one half](hyp:hp), and [depth is bounded in order by simulation
size raised to that exponent](hyp:hdepth), then [depth times the logarithm of
simulation size divided by its square root tends to zero](goal). -/
lemma estimation_depth_sampling_tendsto {m : ℕ → ℕ} {depth : ℕ → ℝ} {p : ℝ}
    (hm : Tendsto (fun r => (m r : ℝ)) atTop atTop) (hp : p < 1/2)
    (hdepth : depth =O[atTop] (fun r => (m r : ℝ)^p)) :
    Tendsto (fun r => depth r * Real.log (m r) / Real.sqrt (m r)) atTop (𝓝 0) := by
  have hbase := (estimation_log_pow_mul_neg_rpow_tendsto (by linarith : 0 < 1/2 - p) 1).comp hm
  have hbase' : Tendsto (fun r => (m r : ℝ)^p *
      (Real.log (m r) / Real.sqrt (m r))) atTop (𝓝 0) := by
    apply hbase.congr'
    filter_upwards [hm.eventually (eventually_gt_atTop (0 : ℝ))] with r hr
    dsimp only [Function.comp_def]
    rw [pow_one, neg_sub, Real.sqrt_eq_rpow, Real.rpow_sub hr]
    ring
  have hbound := hdepth.mul (isBigO_refl
    (fun r => Real.log (m r) / Real.sqrt (m r)) atTop)
  simpa only [mul_div_assoc] using hbound.trans_tendsto hbase'

-- @node: consistencyGrowth_depth_sampling_tendsto_zero
/-- Under [the consistency growth schedule](hyp:h), [the sum of the two network
depths times the logarithm of simulation size divided by its square root tends
to zero](goal). -/
lemma consistencyGrowth_depth_sampling_tendsto_zero {dU : ℕ}
    {m W0 L1 L2 : ℕ → ℕ} {tau lam : ℕ → ℝ}
    (h : ConsistencyGrowthSchedule dU m W0 L1 L2 tau lam) :
    Tendsto (fun r => (L1 r + L2 r : ℕ) * Real.log (m r) / Real.sqrt (m r))
      atTop (𝓝 0) := by
  have hp : (dU : ℝ) / (2 * dU + 4) < 1/2 := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * dU + 4)]
    linarith
  have h1 := estimation_depth_sampling_tendsto (consistencyGrowth_simulation_tendsto h)
    hp h.2.1.1
  have h2 := estimation_depth_sampling_tendsto (consistencyGrowth_simulation_tendsto h)
    hp h.2.2.1.1
  simpa only [Nat.cast_add, add_mul, add_div, zero_add] using h1.add h2

-- @node: consistencyGrowth_sN_eventually_eq
/-- If [the tolerance multiplier is positive](hyp:hc), [every regularization
parameter is positive](hyp:hlam), and [the consistency growth schedule holds](hyp:h),
then [eventually the sampling tolerance equals its multiplier times the sum of
the latent simulation rate, the depth times log-size over square-root-size term,
the observational negative-power rate times squared log sample size, and the
regularization parameter times the log of the product of sample sizes](goal). -/
lemma consistencyGrowth_sN_eventually_eq {dU DU : ℕ}
    {m W0 L1 L2 : ℕ → ℕ} {tau lam : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c) (hlam : ∀ r, 0 < lam r)
    (h : ConsistencyGrowthSchedule dU m W0 L1 L2 tau lam) :
    ∀ᶠ r in atTop, sN c DU m L1 L2 lam r =
      c * ((m r : ℝ)^(-(1 : ℝ)/(max 1 DU + 2)) * Real.log (m r) +
        (L1 r + L2 r : ℕ) * Real.log (m r) / Real.sqrt (m r) +
        (r : ℝ)^(-(1 : ℝ)/max 2 DU) * (Real.log r)^2 +
        Real.log (r * m r) * lam r) := by
  filter_upwards [(consistencyGrowth_simulation_tendsto h).eventually
    (eventually_gt_atTop (1 : ℝ)), eventually_ge_atTop (1 : ℕ)] with r hm hr
  have hlog : 0 < Real.log (m r) := Real.log_pos hm
  have hprod : (1 : ℝ) ≤ (r : ℝ) * (m r : ℝ) := by
    have hrr : (1 : ℝ) ≤ r := by exact_mod_cast hr
    nlinarith
  have hlogprod : 0 ≤ Real.log (r * m r) := Real.log_nonneg hprod
  have hfirst : 0 < (m r : ℝ)^(-(1 : ℝ)/(max 1 DU + 2)) * Real.log (m r) :=
    mul_pos (Real.rpow_pos_of_pos (by linarith) _) hlog
  have hdepth : 0 ≤ (L1 r + L2 r : ℕ) * Real.log (m r) / Real.sqrt (m r) := by
    positivity
  have hobs : 0 ≤ (r : ℝ)^(-(1 : ℝ)/max 2 DU) * (Real.log r)^2 := by
    positivity
  have hbias : 0 ≤ Real.log (r * m r) * lam r := mul_nonneg hlogprod (hlam r).le
  unfold sN
  rw [if_pos (mul_pos hc (by linarith))]

-- @node: consistencyGrowth_sN_tendsto_zero
/-- If [the sampling multiplier is positive](hyp:hc), [all regularization
parameters are positive](hyp:hlam), and [the consistency growth schedule holds](hyp:h),
then [the prescribed sampling tolerance tends to zero](goal). -/
lemma consistencyGrowth_sN_tendsto_zero {dU DU : ℕ}
    {m W0 L1 L2 : ℕ → ℕ} {tau lam : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c) (hlam : ∀ r, 0 < lam r)
    (h : ConsistencyGrowthSchedule dU m W0 L1 L2 tau lam) :
    Tendsto (sN c DU m L1 L2 lam) atTop (𝓝 0) := by
  have hsim : Tendsto (fun r => (m r : ℝ)^(-(1 : ℝ)/(max 1 DU + 2)) *
      Real.log (m r)) atTop (𝓝 0) := by
    simpa only [neg_div, pow_one, Function.comp_def] using
      (estimation_log_pow_mul_neg_rpow_tendsto
        (by positivity : 0 < (1 : ℝ)/(max 1 DU + 2)) 1).comp
        (consistencyGrowth_simulation_tendsto h)
  have hobs : Tendsto (fun r : ℕ => (r : ℝ)^(-(1 : ℝ)/max 2 DU) *
      (Real.log r)^2) atTop (𝓝 0) := by
    simpa only [neg_div, Function.comp_def] using
      (estimation_log_pow_mul_neg_rpow_tendsto
        (by positivity : 0 < (1 : ℝ)/max 2 DU) 2).comp tendsto_natCast_atTop_atTop
  have hbias := (consistencyGrowth_width_temperature_bias h).2.2
  have hrate := (((hsim.add (consistencyGrowth_depth_sampling_tendsto_zero h)).add
    hobs).add hbias).const_mul c
  simp only [zero_add, mul_zero] at hrate
  exact hrate.congr'
    ((consistencyGrowth_sN_eventually_eq (DU := DU) hc hlam h).mono (fun _ hr => hr.symm))

-- @node: consistencyGrowth_radius_tendsto_zero
/-- If [the input dimension](hyp:hdin) and [latent approximation dimension](hyp:hdU)
are positive, [the approximation multiplier](hyp:hce) and [sampling multiplier](hyp:hcs)
are positive, [all temperatures](hyp:htau) and [regularization parameters](hyp:hlam)
are positive, and [the consistency growth schedule holds](hyp:h), then [the
prescribed sum of approximation and sampling tolerances tends to zero](goal). -/
lemma consistencyGrowth_radius_tendsto_zero {dU din DU : ℕ}
    {m W0 L1 L2 : ℕ → ℕ} {tau lam : ℕ → ℝ} {ce cs : ℝ}
    (hdin : 0 < din) (hdU : 0 < dU) (hce : 0 < ce) (hcs : 0 < cs)
    (htau : ∀ r, 0 < tau r) (hlam : ∀ r, 0 < lam r)
    (h : ConsistencyGrowthSchedule dU m W0 L1 L2 tau lam) :
    Tendsto (consistencyRadius ce cs din dU DU m W0 L1 L2 hdin hdU tau lam)
      atTop (𝓝 0) := by
  change Tendsto (fun r => epsN ce din dU hdin hdU W0 L1 L2 tau r +
    sN cs DU m L1 L2 lam r) atTop (𝓝 0)
  simpa only [zero_add] using
    (consistencyGrowth_epsN_tendsto_zero hdin hdU hce htau h).add
      (consistencyGrowth_sN_tendsto_zero (DU := DU) hcs hlam h)

-- @node: consistencyGrowth_eventually_small_radius
/-- If [the input dimension](hyp:hdin), [latent approximation dimension](hyp:hdU),
[approximation multiplier](hyp:hce), and [sampling multiplier](hyp:hcs) are positive,
[every temperature](hyp:htau) and [regularization parameter](hyp:hlam) is positive,
[the consistency growth schedule holds](hyp:h), and [the chosen radii eventually
equal the prescribed approximation-plus-sampling radii](hyp:halpha), then [the
chosen radii tend to zero and are eventually at most one](goal). -/
lemma consistencyGrowth_eventually_small_radius {dU din DU : ℕ}
    {m W0 L1 L2 : ℕ → ℕ} {tau lam alpha : ℕ → ℝ} {ce cs : ℝ}
    (hdin : 0 < din) (hdU : 0 < dU) (hce : 0 < ce) (hcs : 0 < cs)
    (htau : ∀ r, 0 < tau r) (hlam : ∀ r, 0 < lam r)
    (h : ConsistencyGrowthSchedule dU m W0 L1 L2 tau lam)
    (halpha : ∀ᶠ r in atTop, alpha r =
      consistencyRadius ce cs din dU DU m W0 L1 L2 hdin hdU tau lam r) :
    Tendsto alpha atTop (𝓝 0) ∧ ∀ᶠ r in atTop, alpha r ≤ 1 := by
  have hlim := (consistencyGrowth_radius_tendsto_zero (DU := DU)
    hdin hdU hce hcs htau hlam h).congr' (halpha.mono (fun _ hr => hr.symm))
  exact ⟨hlim, (hlim.eventually (gt_mem_nhds zero_lt_one)).mono (fun _ hr => hr.le)⟩

end Papers.TbsNeuralCausalPi
