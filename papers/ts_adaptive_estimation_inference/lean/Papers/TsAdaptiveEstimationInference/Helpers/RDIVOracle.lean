module
public import Papers.TsAdaptiveEstimationInference.Helpers.Selection
public import Papers.TsAdaptiveEstimationInference.Helpers.TikhonovOracle
/-! Scalar balancing estimates for the one-step and iterative RDIV rates. -/
public section

namespace Papers.TsAdaptiveEstimationInference
open Filter
open scoped Topology

/-- If [the source exponent β is positive](hyp:hβ), [the bias exponent exceeds
one and the interpolation exponent equals the bias exponent minus one divided
by the bias exponent](goal). -/
-- @node: rdiv_interpolation_exponent_identity
lemma rdiv_interpolation_exponent_identity (β : ℝ) (hβ : 0 < β) :
    1 < biasExponent β ∧
      interpolationExponent β = (biasExponent β - 1) / biasExponent β := by
  have hp : 1 < biasExponent β := lt_min (by linarith) (by norm_num)
  refine ⟨hp, ?_⟩
  unfold interpolationExponent truncatedSource biasExponent
  rcases le_total β 1 with hb | hb
  · rw [min_eq_left hb, min_eq_left (by linarith : β + 1 ≤ 2)]
    congr 1 <;> ring
  · rw [min_eq_right hb, min_eq_right (by linarith : 2 ≤ β + 1)]
    norm_num

/-- If [β is positive](hyp:hβ) and [the fitting accuracy d is nonnegative](hyp:hd),
[d to the power twice the bias exponent minus two divided by the bias exponent
plus one is bounded by the RDIV error scale raised to the interpolation exponent](goal). -/
-- @node: rdiv_strong_rate_absorption
lemma rdiv_strong_rate_absorption (β d v : ℝ) (hβ : 0 < β) (hd : 0 ≤ d) :
    d ^ (2 * (biasExponent β - 1) / (biasExponent β + 1)) ≤
      rdivErrorScale β d v ^ interpolationExponent β := by
  obtain ⟨hp, hα⟩ := rdiv_interpolation_exponent_identity β hβ
  have hα0 : 0 ≤ interpolationExponent β := by rw [hα]; positivity
  have he : 2 * biasExponent β / (biasExponent β + 1) *
      interpolationExponent β = 2 * (biasExponent β - 1) / (biasExponent β + 1) := by
    rw [hα]
    field_simp
  calc
    _ = (d ^ (2 * biasExponent β / (biasExponent β + 1))) ^
        interpolationExponent β := by rw [← Real.rpow_mul hd, he]
    _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hd _)
      (le_add_of_nonneg_right (sq_nonneg v)) hα0

/-- If [β is positive](hyp:hβ), [d is nonnegative](hyp:hd), and [C is
nonnegative](hyp:hC), [C times the sum of the fitting strong-error power and the
interpolated RDIV error scale is at most twice C times that interpolated scale](goal). -/
-- @node: rdiv_strong_rate_simplification
lemma rdiv_strong_rate_simplification (β d v C : ℝ)
    (hβ : 0 < β) (hd : 0 ≤ d) (hC : 0 ≤ C) :
    C * (d ^ (2 * (biasExponent β - 1) / (biasExponent β + 1)) +
      rdivErrorScale β d v ^ interpolationExponent β) ≤
        (2 * C) * rdivErrorScale β d v ^ interpolationExponent β := by
  have h := mul_le_mul_of_nonneg_left (rdiv_strong_rate_absorption β d v hβ hd) hC
  nlinarith only [h]

/-- If [the grid factor ρ is positive](hyp:hρ), [the radius multiplier c is
positive](hyp:hc), [p is positive](hyp:hp), [the fitting accuracy d is
positive](hyp:hd), and [the penalty is at least ρc times the larger of
d raised to 2/(p+1) and v raised to 2/p](hyp:hlower), [the RDIV noise level is
at most the sum of d raised to 2p/(p+1) and v squared, multiplied by one plus
the reciprocal of ρc](goal). -/
-- @node: rdiv_oracle_noise_rate
lemma rdiv_oracle_noise_rate (ρ c p d v lam : ℝ)
    (hρ : 0 < ρ) (hc : 0 < c) (hp : 0 < p) (hd : 0 < d)
    (hlower : ρ * (c * max (d ^ (2 / (p + 1))) (v ^ (2 / p))) ≤ lam) :
    rdivNoiseLevel d v lam ≤
      ((ρ * c)⁻¹ + 1) * (d ^ (2 * p / (p + 1)) + v ^ 2) := by
  have hlo : ρ * (c * d ^ (2 / (p + 1))) ≤ lam :=
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (le_max_left _ _) hc.le) hρ.le).trans hlower
  have hrate := trae_oracle_variance_rate ρ c (p + 1) d lam hρ hc
    (by linarith) hd hlo
  have he : 2 * (p + 1 - 1) / (p + 1) = 2 * p / (p + 1) := by ring
  rw [he] at hrate
  unfold rdivNoiseLevel
  have hK : 0 ≤ (ρ * c)⁻¹ := by positivity
  have hd0 : 0 ≤ d ^ (2 * p / (p + 1)) := Real.rpow_nonneg hd.le _
  nlinarith only [hrate, hd0, mul_nonneg hK (sq_nonneg v)]

/-- If [ρ is positive](hyp:hρ), [c is positive](hyp:hc), [p exceeds one](hyp:hp),
[d is positive](hyp:hd), and [the penalty is at least ρc times the larger of
d raised to 2/(p+1) and v raised to 2/p](hyp:hlower), [fitting stability is
at most d raised to 2(p−1)/(p+1) divided by the square of ρc](goal). -/
-- @node: rdiv_oracle_stability_rate
lemma rdiv_oracle_stability_rate (ρ c p d v lam : ℝ)
    (hρ : 0 < ρ) (hc : 0 < c) (hp : 1 < p) (hd : 0 < d)
    (hlower : ρ * (c * max (d ^ (2 / (p + 1))) (v ^ (2 / p))) ≤ lam) :
    rdivStability d lam ≤
      (ρ * c)⁻¹ ^ 2 * d ^ (2 * (p - 1) / (p + 1)) := by
  have hlo : ρ * (c * d ^ (2 / (p + 1))) ≤ lam :=
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (le_max_left _ _) hc.le) hρ.le).trans hlower
  have hr : 0 < ρ * (c * d ^ (2 / (p + 1))) := by positivity
  unfold rdivStability
  calc
    _ ≤ d ^ 2 / (ρ * (c * d ^ (2 / (p + 1)))) ^ 2 :=
      div_le_div_of_nonneg_left (sq_nonneg d) (sq_pos_of_pos hr)
        (pow_le_pow_left₀ hr.le hlo 2)
    _ = _ := by
      have he : 2 * (p - 1) / (p + 1) = 2 - (2 / (p + 1)) * 2 := by
        field_simp
        ring
      rw [he, Real.rpow_sub hd, Real.rpow_two, Real.rpow_mul hd.le,
        Real.rpow_two]
      field_simp

/-- Suppose [ρ satisfies the geometric grid restrictions](hyp:hρ), [c is
positive](hyp:hc) and [at most one](hyp:hc1), [p exceeds one](hyp:hp),
[d is positive](hyp:hd) and [at most c](hyp:hdc), [v is nonnegative](hyp:hv)
and [at most one](hyp:hv1), [the sample size n is positive](hyp:hn), and
[d squared is at least 1/n](hyp:hfloor). Then [rounding c times the larger
of d raised to 2/(p+1) and v raised to 2/p gives a point in the regularization
grid between ρ times that radius and the radius itself](goal). -/
-- @node: rdiv_small_noise_oracle
lemma rdiv_small_noise_oracle (ρ c p d v : ℝ) (n : ℕ)
    (hρ : GridDomain ρ) (hc : 0 < c) (hc1 : c ≤ 1)
    (hp : 1 < p) (hd : 0 < d) (hdc : d ≤ c) (hv : 0 ≤ v) (hv1 : v ≤ 1)
    (hn : 0 < n) (hfloor : 1 / (n : ℝ) ≤ d ^ 2) :
    oraclePoint ρ n (c * max (d ^ (2 / (p + 1))) (v ^ (2 / p))) ∈ regGrid ρ n ∧
      ρ * (c * max (d ^ (2 / (p + 1))) (v ^ (2 / p))) ≤
        oraclePoint ρ n (c * max (d ^ (2 / (p + 1))) (v ^ (2 / p))) ∧
      oraclePoint ρ n (c * max (d ^ (2 / (p + 1))) (v ^ (2 / p))) ≤
        c * max (d ^ (2 / (p + 1))) (v ^ (2 / p)) := by
  have hd1 : d ≤ 1 := hdc.trans hc1
  have hpow : d ^ 2 ≤ d ^ (2 / (p + 1)) := by
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_ge hd hd1
      ((div_le_iff₀ (by linarith : 0 < p + 1)).2 (by linarith))
  have hmax : max (d ^ (2 / (p + 1))) (v ^ (2 / p)) ≤ 1 :=
    max_le (Real.rpow_le_one hd.le hd1 (by positivity))
      (Real.rpow_le_one hv hv1 (by positivity))
  apply oraclePoint_radius_bounds ρ _ n hρ (by nlinarith)
  have ht := terminalGrid_le ρ hρ n hn
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / (n : ℝ)) hfloor 2
  have hd2c : d ^ 2 ≤ c := by nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hd1)]
  calc
    gridValue ρ (terminalIndex ρ n) ≤ 1 / (n : ℝ) ^ 2 := ht
    _ = (1 / (n : ℝ)) ^ 2 := by ring
    _ ≤ (d ^ 2) ^ 2 := hsq
    _ ≤ c * d ^ 2 := by nlinarith [mul_nonneg (sq_nonneg d) (sub_nonneg.mpr hd2c)]
    _ ≤ c * d ^ (2 / (p + 1)) := mul_le_mul_of_nonneg_left hpow hc.le
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) hc.le

/-- Suppose [the bias constant is nonnegative](hyp:hCb), [c is nonnegative](hyp:hc),
[p is positive](hyp:hp), [d is nonnegative](hyp:hd), [v is nonnegative](hyp:hv),
[the penalty is positive](hyp:hlam) and [at most c times the larger of d raised
to 2/(p+1) and v raised to 2/p](hyp:hupper), while [the bias constant times
c raised to p+1 is at most one half](hyp:hsmallFit) and [the bias constant times
c raised to p is at most one half](hyp:hsmallCal). Then [the bias constant times
the penalty raised to p is at most half the RDIV noise level](goal). -/
-- @node: rdiv_oracle_bias_crossing
lemma rdiv_oracle_bias_crossing (Cb c p d v lam : ℝ)
    (hCb : 0 ≤ Cb) (hc : 0 ≤ c) (hp : 0 < p)
    (hd : 0 ≤ d) (hv : 0 ≤ v) (hlam : 0 < lam)
    (hupper : lam ≤ c * max (d ^ (2 / (p + 1))) (v ^ (2 / p)))
    (hsmallFit : Cb * c ^ (p + 1) ≤ 1 / 2)
    (hsmallCal : Cb * c ^ p ≤ 1 / 2) :
    Cb * lam ^ p ≤ 1 / 2 * rdivNoiseLevel d v lam := by
  rcases le_total (v ^ (2 / p)) (d ^ (2 / (p + 1))) with h | h
  · rw [max_eq_left h] at hupper
    have hb := trae_oracle_bias_crossing Cb c (p + 1) d lam hCb hc
      (by linarith) hd hlam.le hupper hsmallFit
    rw [Real.rpow_add_one hlam.ne'] at hb
    have hdiv : Cb * lam ^ p ≤ (1 / 2 * d ^ 2) / lam :=
      (le_div_iff₀ hlam).2 (by nlinarith only [hb])
    apply hdiv.trans
    unfold rdivNoiseLevel
    calc
      _ = 1 / 2 * (d ^ 2 / lam) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (sq_nonneg v)) (by norm_num)
  · rw [max_eq_right h] at hupper
    have hb := trae_oracle_bias_crossing Cb c p v lam hCb hc hp hv
      hlam.le hupper hsmallCal
    exact hb.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (div_nonneg (sq_nonneg d) hlam.le)) (by norm_num))

/-- If [ρ is positive](hyp:hρ), [c is positive](hyp:hc), [β is positive](hyp:hβ),
[d is nonnegative](hyp:hd), [v is nonnegative](hyp:hv), and [the penalty is at
least ρc times the balancing radius formed from d and v using the bias
exponent](hyp:hlower), [v squared divided by the penalty is at most the
interpolated RDIV error scale divided by ρc](goal). -/
-- @node: rdiv_oracle_calibration_ratio
lemma rdiv_oracle_calibration_ratio (ρ c β d v lam : ℝ)
    (hρ : 0 < ρ) (hc : 0 < c) (hβ : 0 < β) (hd : 0 ≤ d) (hv : 0 ≤ v)
    (hlower : ρ * (c * max (d ^ (2 / (biasExponent β + 1)))
      (v ^ (2 / biasExponent β))) ≤ lam) :
    v ^ 2 / lam ≤ (ρ * c)⁻¹ * rdivErrorScale β d v ^ interpolationExponent β := by
  obtain ⟨hp, hα⟩ := rdiv_interpolation_exponent_identity β hβ
  by_cases hz : v = 0
  · subst v
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div]
    unfold rdivErrorScale
    positivity
  have hvpos : 0 < v := lt_of_le_of_ne hv (Ne.symm hz)
  have hlo : ρ * (c * v ^ (2 / biasExponent β)) ≤ lam :=
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (le_max_right _ _) hc.le) hρ.le).trans hlower
  have hb := trae_oracle_variance_rate ρ c (biasExponent β) v lam hρ hc
    (by linarith) hvpos hlo
  have he : v ^ (2 * (biasExponent β - 1) / biasExponent β) =
      (v ^ 2) ^ interpolationExponent β := by
    rw [← Real.rpow_two, ← Real.rpow_mul hv]
    congr 1
    rw [hα]
    ring
  rw [he] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow (sq_nonneg v)
    (le_add_of_nonneg_left (Real.rpow_nonneg hd _)) (by rw [hα]; positivity)

/-- Suppose [ρ satisfies the grid restrictions](hyp:hρ), [c is positive](hyp:hc)
and [at most one](hyp:hc1), [β is positive](hyp:hβ), [the fitting accuracy
sequence is nonnegative](hyp:hδ), [the nuisance accuracy sequence is
nonnegative](hyp:hν), [the fitting accuracies tend to zero](hyp:hδlim),
[the nuisance accuracies tend to zero](hyp:hνlim), and [eventually the squared
fitting accuracy is at least the reciprocal sample size](hyp:hfloor). Then
[one positive constant bounds both oracle noise and stability by their RDIV
rates for all sufficiently large sample sizes](goal). -/
-- @node: rdiv_oracle_scales
lemma rdiv_oracle_scales (ρ c β : ℝ) (δ ν : ℕ → ℝ)
    (hρ : GridDomain ρ) (hc : 0 < c) (hc1 : c ≤ 1) (hβ : 0 < β)
    (hδ : ∀ n, 0 ≤ δ n) (hν : ∀ n, 0 ≤ ν n)
    (hδlim : Tendsto δ atTop (𝓝 0)) (hνlim : Tendsto ν atTop (𝓝 0))
    (hfloor : ∀ᶠ n : ℕ in atTop, 1 / (n : ℝ) ≤ δ n ^ 2) :
    RDIVOracleScales ρ c β δ ν := by
  have hp := (rdiv_interpolation_exponent_identity β hβ).1
  have hρpos : 0 < ρ := by linarith only [hρ.1]
  let K := (ρ * c)⁻¹
  have hK : 0 < K := by dsimp [K]; positivity
  let C := K + 1 + K ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [hfloor, (tendsto_order.1 hδlim).2 c hc,
    (tendsto_order.1 hνlim).2 1 zero_lt_one, eventually_gt_atTop 0]
    with n hfn hdn hvn hn
  have hd : 0 < δ n := by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hfpos : 0 < 1 / (n : ℝ) := by positivity
    nlinarith only [hfn, hfpos, hδ n]
  have hround := rdiv_small_noise_oracle ρ c (biasExponent β) (δ n) (ν n) n
    hρ hc hc1 hp hd hdn.le (hν n) hvn.le hn hfn
  have hnoise := rdiv_oracle_noise_rate ρ c (biasExponent β) (δ n) (ν n)
    _ hρpos hc (by linarith) hd hround.2.1
  have hstable := rdiv_oracle_stability_rate ρ c (biasExponent β) (δ n) (ν n)
    _ hρpos hc hp hd hround.2.1
  constructor
  · exact hnoise.trans (mul_le_mul_of_nonneg_right
      (by dsimp [C, K]; nlinarith only [sq_nonneg ((ρ * c)⁻¹)])
      (add_nonneg (Real.rpow_nonneg hd.le _) (sq_nonneg _)))
  · exact hstable.trans (mul_le_mul_of_nonneg_right
      (by dsimp [C]; linarith only [hK]) (Real.rpow_nonneg hd.le _))

/-- If [ρ is positive](hyp:hρ), [c is positive](hyp:hc), [β is positive](hyp:hβ),
[d is positive](hyp:hd), [v is nonnegative](hyp:hv), and [the penalty is at
least ρc times the RDIV balancing radius](hyp:hlower), [the noise divided by
the penalty is bounded by the fitting strong-error power divided by the square
of ρc plus the interpolated error scale divided by ρc](goal). -/
-- @node: rdiv_oracle_noise_ratio_rate
lemma rdiv_oracle_noise_ratio_rate (ρ c β d v lam : ℝ)
    (hρ : 0 < ρ) (hc : 0 < c) (hβ : 0 < β) (hd : 0 < d) (hv : 0 ≤ v)
    (hlower : ρ * (c * max (d ^ (2 / (biasExponent β + 1)))
      (v ^ (2 / biasExponent β))) ≤ lam) :
    rdivNoiseLevel d v lam / lam ≤
      (ρ * c)⁻¹ ^ 2 * d ^ (2 * (biasExponent β - 1) / (biasExponent β + 1)) +
        (ρ * c)⁻¹ * rdivErrorScale β d v ^ interpolationExponent β := by
  have hs := rdiv_oracle_stability_rate ρ c (biasExponent β) d v lam hρ hc
    (rdiv_interpolation_exponent_identity β hβ).1 hd hlower
  have hv' := rdiv_oracle_calibration_ratio ρ c β d v lam hρ hc hβ hd.le hv
    hlower
  calc
    _ = rdivStability d lam + v ^ 2 / lam := by
      unfold rdivNoiseLevel rdivStability
      ring
    _ ≤ _ := add_le_add hs hv'

/-- For [a nonnegative scale s](hyp:hs), [its square root raised to twice p
equals s raised to p](goal). -/
-- @node: iter_rdiv_sqrt_scale_power
lemma iter_rdiv_sqrt_scale_power (s p : ℝ) (hs : 0 ≤ s) :
    (Real.sqrt s) ^ (2 * p) = s ^ p := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hs]
  congr 1
  ring

/-- Suppose [ρ is positive](hyp:hρ), [c is positive](hyp:hc), [q exceeds
one](hyp:hq), [the propagated squared accuracy a times d squared is
positive](hyp:hs), and [the penalty is at least ρc times the larger of the
propagated squared accuracy raised to 1/(q+1) and v raised to 2/q](hyp:hlower).
Then [iterative noise is bounded by one plus the reciprocal of ρc times the
sum of the propagated squared accuracy raised to q/(q+1) and v squared, and
iterative stability is bounded by the propagated squared accuracy raised to
(q−1)/(q+1) divided by the square of ρc](goal). -/
-- @node: iter_rdiv_oracle_scalar_rates
lemma iter_rdiv_oracle_scalar_rates (ρ c a q d v lam : ℝ)
    (hρ : 0 < ρ) (hc : 0 < c) (hq : 1 < q) (hs : 0 < a * d ^ 2)
    (hlower : ρ * (c * max ((a * d ^ 2) ^ (1 / (q + 1)))
      (v ^ (2 / q))) ≤ lam) :
    iterRdivNoiseLevel a d v lam ≤
        ((ρ * c)⁻¹ + 1) * ((a * d ^ 2) ^ (q / (q + 1)) + v ^ 2) ∧
      iterRdivStability a d lam ≤
        (ρ * c)⁻¹ ^ 2 * (a * d ^ 2) ^ ((q - 1) / (q + 1)) := by
  have hpower (p : ℝ) : (Real.sqrt (a * d ^ 2)) ^ (2 * p) =
      (a * d ^ 2) ^ p := iter_rdiv_sqrt_scale_power _ p hs.le
  have hrad : (Real.sqrt (a * d ^ 2)) ^ (2 / (q + 1)) =
      (a * d ^ 2) ^ (1 / (q + 1)) := by
    rw [show 2 / (q + 1) = 2 * (1 / (q + 1)) by ring, hpower]
  have hlo : ρ * (c * max ((Real.sqrt (a * d ^ 2)) ^ (2 / (q + 1)))
      (v ^ (2 / q))) ≤ lam := by rwa [hrad]
  have hn := rdiv_oracle_noise_rate ρ c q (Real.sqrt (a * d ^ 2)) v lam
    hρ hc (by linarith) (Real.sqrt_pos.2 hs) hlo
  have hv := rdiv_oracle_stability_rate ρ c q (Real.sqrt (a * d ^ 2)) v lam
    hρ hc hq (Real.sqrt_pos.2 hs) hlo
  rw [show 2 * q / (q + 1) = 2 * (q / (q + 1)) by ring, hpower] at hn
  rw [show 2 * (q - 1) / (q + 1) = 2 * ((q - 1) / (q + 1)) by ring,
    hpower] at hv
  simpa only [rdivNoiseLevel, rdivStability, iterRdivNoiseLevel,
    iterRdivStability, iterRdivScale, Real.sq_sqrt hs.le] using And.intro hn hv

/-- Suppose [ρ satisfies the grid restrictions](hyp:hρ), [c is positive](hyp:hc)
and [at most one](hyp:hc1), [the propagation factor a is at least one](hyp:ha),
[β is positive](hyp:hβ), [there is at least one iteration](hyp:ht), [the fitting
accuracies are nonnegative](hyp:hδ), [the nuisance accuracies are
nonnegative](hyp:hν), [the fitting accuracies tend to zero](hyp:hδlim), [the
nuisance accuracies tend to zero](hyp:hνlim), and [eventually the squared fitting
accuracy is at least the reciprocal sample size](hyp:hfloor). Then [the iterative
oracle noise and stability satisfy their respective rate bounds with a common
positive constant for all sufficiently large sample sizes](goal). -/
-- @node: iter_rdiv_oracle_scales
lemma iter_rdiv_oracle_scales (ρ c a β : ℝ) (t : ℕ) (δ ν : ℕ → ℝ)
    (hρ : GridDomain ρ) (hc : 0 < c) (hc1 : c ≤ 1) (ha : 1 ≤ a)
    (hβ : 0 < β) (ht : 1 ≤ t)
    (hδ : ∀ n, 0 ≤ δ n) (hν : ∀ n, 0 ≤ ν n)
    (hδlim : Tendsto δ atTop (𝓝 0)) (hνlim : Tendsto ν atTop (𝓝 0))
    (hfloor : ∀ᶠ n : ℕ in atTop, 1 / (n : ℝ) ≤ δ n ^ 2) :
    IterRDIVOracleScales ρ c a β t δ ν := by
  have ha0 : 0 ≤ a := by linarith only [ha]
  have hq : 1 < qualificationExponent β t := by
    unfold qualificationExponent
    have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
    exact lt_min (by linarith only [hβ]) (by linarith only [htR])
  have hρ0 : 0 < ρ := by linarith only [hρ.1]
  let d : ℕ → ℝ := fun n => Real.sqrt a * δ n
  have hd0 (n : ℕ) : 0 ≤ d n := mul_nonneg (Real.sqrt_nonneg _) (hδ n)
  have hdsq (n : ℕ) : d n ^ 2 = a * δ n ^ 2 := by
    dsimp only [d]
    rw [mul_pow, Real.sq_sqrt ha0]
  have hdpow (n : ℕ) (p : ℝ) : d n ^ (2 * p) = (a * δ n ^ 2) ^ p := by
    rw [Real.rpow_mul (hd0 n), Real.rpow_two, hdsq]
  have hrad (n : ℕ) : d n ^ (2 / (qualificationExponent β t + 1)) =
      (a * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1)) := by
    rw [show 2 / (qualificationExponent β t + 1) =
      2 * (1 / (qualificationExponent β t + 1)) by ring, hdpow]
  have hdlim : Tendsto d atTop (𝓝 0) := by
    simpa only [mul_zero] using hδlim.const_mul (Real.sqrt a)
  let K := (ρ * c)⁻¹
  let C := K + 1 + K ^ 2
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  filter_upwards [hfloor, (tendsto_order.1 hdlim).2 c hc,
    (tendsto_order.1 hνlim).2 1 zero_lt_one, eventually_gt_atTop 0]
    with n hfn hdn hvn hn
  have hdfloor : 1 / (n : ℝ) ≤ d n ^ 2 := by
    rw [hdsq]
    exact hfn.trans (by nlinarith only [ha, sq_nonneg (δ n)])
  have hdpos : 0 < d n := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hp : 0 < 1 / (n : ℝ) := by positivity
    nlinarith only [hdfloor, hp, hd0 n]
  have hround := rdiv_small_noise_oracle ρ c (qualificationExponent β t)
    (d n) (ν n) n hρ hc hc1 hq hdpos hdn.le (hν n) hvn.le hn hdfloor
  rw [hrad] at hround
  have hrates := iter_rdiv_oracle_scalar_rates ρ c a (qualificationExponent β t)
    (δ n) (ν n) (iterRdivOraclePoint ρ c a β t δ ν n) hρ0 hc hq
    (by rw [← hdsq]; exact sq_pos_of_pos hdpos) hround.2.1
  constructor
  · exact hrates.1.trans (mul_le_mul_of_nonneg_right
      (by dsimp [C, K]; nlinarith only [sq_nonneg ((ρ * c)⁻¹)])
      (add_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _)))
  · exact hrates.2.trans (mul_le_mul_of_nonneg_right
      (by dsimp [C]; linarith only [hK]) (Real.rpow_nonneg (by positivity) _))

/-- Suppose [a is nonnegative](hyp:ha), [β is positive](hyp:hβ), [d is
nonnegative](hyp:hd) and [at most one](hyp:hd1), [v is nonnegative](hyp:hv)
and [at most M times d](hyp:hvd), and [the iteration count provides qualification
at least β+1](hyp:hqual). Then [the iterative error scale is bounded by
(a raised to (β+1)/(β+2) plus M squared) times d raised to 2(β+1)/(β+2),
and the sum of the stability power and the error scale raised to β/(β+1)
is bounded by (a raised to β/(β+2) plus that same coefficient raised to
β/(β+1)) times d raised to 2β/(β+2)](goal). -/
-- @node: iter_rdiv_qualified_rate_simplification
lemma iter_rdiv_qualified_rate_simplification (a β M d v : ℝ) (t : ℕ)
    (ha : 0 ≤ a) (hβ : 0 < β)
    (hd : 0 ≤ d) (hd1 : d ≤ 1) (hv : 0 ≤ v) (hvd : v ≤ M * d)
    (hqual : IterQualificationRDIV β t) :
    iterRdivErrorScale β a d v t ≤
        (a ^ ((β + 1) / (β + 2)) + M ^ 2) * d ^ (2 * (β + 1) / (β + 2)) ∧
      (a * d ^ 2) ^ ((qualificationExponent β t - 1) /
          (qualificationExponent β t + 1)) +
        iterRdivErrorScale β a d v t ^ (β / (β + 1)) ≤
      (a ^ (β / (β + 2)) +
        (a ^ ((β + 1) / (β + 2)) + M ^ 2) ^ (β / (β + 1))) *
          d ^ (2 * β / (β + 2)) := by
  have hq : qualificationExponent β t = β + 1 := min_eq_left hqual
  have hden : 0 < β + 2 := by linarith only [hβ]
  have hden1 : 0 < β + 1 := by linarith only [hβ]
  have hpower (p : ℝ) : (a * d ^ 2) ^ p = a ^ p * d ^ (2 * p) := by
    rw [Real.mul_rpow ha (sq_nonneg d), Real.rpow_mul hd, Real.rpow_two]
  have hdweak : d ^ 2 ≤ d ^ (2 * (β + 1) / (β + 2)) := by
    rw [← Real.rpow_two]
    apply Real.rpow_le_rpow_of_exponent_ge' hd hd1 (by positivity)
    apply (div_le_iff₀ hden).2
    linarith only [hβ]
  have hvbound : v ^ 2 ≤ M ^ 2 * d ^ (2 * (β + 1) / (β + 2)) := by
    calc
      v ^ 2 ≤ (M * d) ^ 2 := pow_le_pow_left₀ hv hvd 2
      _ = M ^ 2 * d ^ 2 := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hdweak (sq_nonneg M)
  have heps : iterRdivErrorScale β a d v t ≤
      (a ^ ((β + 1) / (β + 2)) + M ^ 2) *
        d ^ (2 * (β + 1) / (β + 2)) := by
    unfold iterRdivErrorScale
    rw [hq, show β + 1 + 1 = β + 2 by ring, hpower]
    have he : 2 * ((β + 1) / (β + 2)) = 2 * (β + 1) / (β + 2) := by ring
    rw [he]
    nlinarith only [hvbound]
  refine ⟨heps, ?_⟩
  have hraised := Real.rpow_le_rpow (by
    unfold iterRdivErrorScale
    positivity) heps (by positivity : 0 ≤ β / (β + 1))
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hd] at hraised
  have hexp : (2 * (β + 1) / (β + 2)) * (β / (β + 1)) =
      2 * β / (β + 2) := by field_simp
  rw [hexp] at hraised
  rw [hq, show β + 1 - 1 = β by ring, show β + 1 + 1 = β + 2 by ring,
    hpower]
  have he : 2 * (β / (β + 2)) = 2 * β / (β + 2) := by ring
  rw [he]
  nlinarith only [hraised]

end Papers.TsAdaptiveEstimationInference
