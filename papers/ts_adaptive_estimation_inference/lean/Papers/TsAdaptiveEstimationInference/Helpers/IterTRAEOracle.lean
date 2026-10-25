module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAERefinedPropagation
public import Papers.TsAdaptiveEstimationInference.Helpers.TikhonovOracle
public import Papers.TsAdaptiveEstimationInference.TCommonDp
/-! Oracle scale calculations and deterministic selection for the iterative TRAE rate. -/
public section
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter
open scoped Topology

/-- If [the regularization penalty is positive](hyp:hlam) and [at least the
square root of the multiplier times squared accuracy](hyp:hstable), [the noise
level equals squared accuracy plus the multiplier times squared accuracy divided
by the penalty](goal). -/
-- @node: iterTraeNoiseLevel_stable
lemma iterTraeNoiseLevel_stable (b d lam : ℝ) (hlam : 0 < lam)
    (hstable : Real.sqrt (b * d ^ 2) ≤ lam) :
    iterTraeNoiseLevel b d lam = d ^ 2 + b * d ^ 2 / lam := by
  have hs := (Real.sqrt_le_iff).1 hstable |>.2
  unfold iterTraeNoiseLevel iterTraeScale
  rw [min_eq_right]
  apply (div_le_iff₀ hlam).2
  nlinarith only [hs]

/-- If [the multiplier is at least two](hyp:hb), [the smaller penalty is
positive](hyp:hx), [it does not exceed the larger penalty](hyp:hxy), [the larger
penalty is at most two](hyp:hy), and [the smaller penalty is at least the square-root
stability threshold](hyp:hs), then [the noise level at the larger penalty is no
greater than at the smaller one, and its ratio to the larger penalty is at most
twice the stability level there](goal). -/
-- @node: iterTraeNoiseLevel_stable_comparison
lemma iterTraeNoiseLevel_stable_comparison (b d x y : ℝ) (hb : 2 ≤ b)
    (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 2)
    (hs : Real.sqrt (b * d ^ 2) ≤ x) :
    iterTraeNoiseLevel b d y ≤ iterTraeNoiseLevel b d x ∧
      iterTraeNoiseLevel b d y / y ≤ 2 * iterTraeStability b d y := by
  have hy0 := hx.trans_le hxy
  rw [iterTraeNoiseLevel_stable b d x hx hs,
    iterTraeNoiseLevel_stable b d y hy0 (hs.trans hxy)]
  constructor
  · exact add_le_add le_rfl
      (div_le_div_of_nonneg_left (by positivity : 0 ≤ b * d ^ 2) hx hxy)
  · unfold iterTraeStability iterTraeScale
    apply (div_le_iff₀ hy0).2
    have hd : d ^ 2 * y ≤ b * d ^ 2 := by nlinarith [sq_nonneg d]
    have hdiv : d ^ 2 ≤ b * d ^ 2 / y := (le_div_iff₀ hy0).2 hd
    have heq : (2 * (b * d ^ 2 / y ^ 2)) * y = 2 * (b * d ^ 2 / y) := by
      field_simp
    rw [heq]
    linarith

/-- Suppose [the grid ratio is positive](hyp:hρ), [the balancing coefficient is
positive](hyp:hc), [the multiplier is at least two](hyp:hb), [the qualification
exponent exceeds one](hyp:hq), [the multiplier times squared accuracy is
positive](hyp:hd) and [at most one](hyp:hs), and [the penalty is at least the grid
ratio times the balancing coefficient times that scale raised to the reciprocal
of one plus the exponent](hyp:hlower). Then [the noise level is bounded by one
plus the inverse grid-ratio–coefficient product times the scale to exponent
q divided by q plus one, and stability is bounded by the squared inverse product
times the scale to exponent q minus one divided by q plus one](goal). -/
-- @node: iterTraeOracle_scalar_rates
lemma iterTraeOracle_scalar_rates (ρ c b q d lam : ℝ)
    (hρ : 0 < ρ) (hc : 0 < c) (hb : 2 ≤ b) (hq : 1 < q)
    (hd : 0 < b * d ^ 2) (hs : b * d ^ 2 ≤ 1)
    (hlower : ρ * (c * (b * d ^ 2) ^ (1 / (q + 1))) ≤ lam) :
    iterTraeNoiseLevel b d lam ≤
        (1 + (ρ * c)⁻¹) * (b * d ^ 2) ^ (q / (q + 1)) ∧
      iterTraeStability b d lam ≤
        (ρ * c)⁻¹ ^ 2 * (b * d ^ 2) ^ ((q - 1) / (q + 1)) := by
  let s := b * d ^ 2
  let a := 1 / (q + 1)
  have ha : 0 < a := by dsimp [a]; positivity
  have hr : 0 < ρ * (c * s ^ a) := by positivity
  have hl : 0 < lam := hr.trans_le hlower
  have hp : s ^ (q / (q + 1)) = s / s ^ a := by
    rw [show q / (q + 1) = 1 - a by dsimp [a]; field_simp; ring,
      Real.rpow_sub hd, Real.rpow_one]
  have hv : s ^ ((q - 1) / (q + 1)) = s / (s ^ a) ^ 2 := by
    rw [show (q - 1) / (q + 1) = 1 - a * 2 by dsimp [a]; field_simp; ring,
      Real.rpow_sub hd, Real.rpow_one, Real.rpow_mul hd.le, Real.rpow_two]
  have hrate : s ≤ s ^ (q / (q + 1)) := by
    conv_lhs => rw [← Real.rpow_one s]
    apply Real.rpow_le_rpow_of_exponent_ge hd hs
    apply (div_le_one (by linarith : 0 < q + 1)).2
    linarith
  have hd2 : d ^ 2 ≤ s := by dsimp [s]; nlinarith [sq_nonneg d]
  constructor
  · calc
      iterTraeNoiseLevel b d lam ≤ d ^ 2 + s / lam := by
        exact add_le_add le_rfl (min_le_right lam (s / lam))
      _ ≤ s ^ (q / (q + 1)) + s / (ρ * (c * s ^ a)) :=
        add_le_add (hd2.trans hrate) (div_le_div_of_nonneg_left hd.le hr hlower)
      _ = _ := by rw [hp]; dsimp [s]; field_simp
  · change s / lam ^ 2 ≤ _
    calc
      s / lam ^ 2 ≤ s / (ρ * (c * s ^ a)) ^ 2 :=
        div_le_div_of_nonneg_left hd.le (sq_pos_of_pos hr)
          (pow_le_pow_left₀ hr.le hlower 2)
      _ = _ := by rw [hv]; dsimp [s]; field_simp

/-- If [the scale is nonnegative](hyp:hs) and [at most one](hyp:hs1), [the source
exponent is positive](hyp:hβ), [the qualification exponent exceeds one](hyp:hq),
and [it is at most one plus the source exponent](hyp:hqβ), then [raising the
scale to q divided by q plus one and then to the source exponent divided by one
plus that exponent gives at most the scale raised to q minus one divided by
q plus one](goal). -/
-- @node: iterTrae_source_rate_power
lemma iterTrae_source_rate_power (s β q : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hβ : 0 < β) (hq : 1 < q) (hqβ : q ≤ β + 1) :
    (s ^ (q / (q + 1))) ^ (β / (β + 1)) ≤ s ^ ((q - 1) / (q + 1)) := by
  rw [← Real.rpow_mul hs]
  apply Real.rpow_le_rpow_of_exponent_ge' hs hs1 (by positivity)
  apply (div_le_iff₀ (by linarith : 0 < q + 1)).2
  have heq : (q / (q + 1) * (β / (β + 1))) * (q + 1) = q * β / (β + 1) := by
    field_simp
  rw [heq]
  apply (le_div_iff₀ (by linarith : 0 < β + 1)).2
  nlinarith only [hqβ]

/-- If [the grid ratio lies in its admissible range](hyp:hρ), [the balancing
coefficient is positive](hyp:hc), [the multiplier is at least two](hyp:hb), [the
source exponent is positive](hyp:hβ), [the iteration horizon is at least
one](hyp:ht), and [the accuracy curve is calibrated to the complexity curve and
confidence allocation](hyp:hScale), then [one positive constant eventually bounds
the oracle noise and stability levels by that constant times the noise scale
(the multiplier times squared accuracy) raised respectively to the qualification exponent divided
by one plus that exponent and to the qualification exponent minus one divided
by one plus that exponent](goal). -/
-- @node: iterTraeOracleScales_of_calibration
lemma iterTraeOracleScales_of_calibration (ρ c b β : ℝ) (t : ℕ)
    (δ : ℕ → ℝ) (tildeδ : ℕ → ℝ → ℝ) (allocation : ℕ → ℝ)
    (hρ : GridDomain ρ) (hc : 0 < c) (hb : 2 ≤ b) (hβ : 0 < β) (ht : 1 ≤ t)
    (hScale : TRAEScaleCalibration δ tildeδ allocation) :
    IterTRAEOracleScales ρ c b β t δ := by
  have hr : 0 < ρ := by linarith [hρ.1]
  have hq : 1 < qualificationExponent β t := by
    unfold qualificationExponent
    have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
    exact lt_min (by linarith) (by linarith)
  let K := max (1 + (ρ * c)⁻¹) ((ρ * c)⁻¹ ^ 2)
  have hK : 0 < K := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hlimit : Tendsto (fun n => b * δ n ^ 2) atTop (𝓝 0) := by
    simpa using (hScale.2.pow 2).const_mul b
  have hradius : Tendsto
      (fun n => c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1)))
      atTop (𝓝 0) := by
    simpa using (hlimit.rpow_const_nhds_zero (by positivity :
      0 < 1 / (qualificationExponent β t + 1))).const_mul c
  refine ⟨K, hK, ?_⟩
  filter_upwards [iterTraeOraclePoint_stable_eventually ρ c b β t δ tildeδ allocation
    hρ hc hb hβ ht hScale, hlimit.eventually (gt_mem_nhds zero_lt_one),
    hradius.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 2)),
    eventually_gt_atTop 0] with n hn hs hrad hn0
  have hd : 0 < δ n := (Real.rpow_pos_of_pos (by positivity) _).trans_le
    ((le_max_right _ _).trans (hScale.1 n hn0))
  obtain ⟨k, hk, hkr⟩ := hn.1
  have hterminal : gridValue ρ (terminalIndex ρ n) ≤
      c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1)) :=
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one hr.le hρ.2.le hk) (by norm_num)).trans hkr
  have hround := oraclePoint_radius_bounds ρ _ n hρ hrad.le hterminal
  have hRates := iterTraeOracle_scalar_rates ρ c b (qualificationExponent β t)
    (δ n) (iterTraeOraclePoint ρ c b β t δ n) hr hc hb hq
    (by positivity) hs.le hround.2.1
  exact ⟨hRates.1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)),
    hRates.2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))⟩

/-- If [the bias coefficient is nonnegative](hyp:hCb) and [the qualification
exponent exceeds one](hyp:hq), then [there is a positive upper bound on the
balancing coefficient such that every positive coefficient up to that bound,
raised to one plus the qualification exponent and multiplied by the bias
coefficient, is at most one half](goal). -/
-- @node: iterTraeOracle_crossing_constant
lemma iterTraeOracle_crossing_constant (Cb q : ℝ) (hCb : 0 ≤ Cb) (hq : 1 < q) :
    ∃ cmax > 0, ∀ c ∈ Set.Ioc (0 : ℝ) cmax, Cb * c ^ (q + 1) ≤ 1 / 2 := by
  refine ⟨1 / (2 * Cb + 1), by positivity, ?_⟩
  intro c hc
  have hc1 : c ≤ 1 := hc.2.trans ((div_le_one (by positivity)).2 (by linarith))
  have hp : c ^ (q + 1) ≤ c := by
    conv_rhs => rw [← Real.rpow_one c]
    exact Real.rpow_le_rpow_of_exponent_ge hc.1 hc1 (by linarith)
  have hm := (le_div_iff₀ (by positivity : 0 < 2 * Cb + 1)).1 hc.2
  exact (mul_le_mul_of_nonneg_left hp hCb).trans (by nlinarith [hc.1])

/-- Suppose [the bias coefficient is nonnegative](hyp:hCb), [the balancing
coefficient is positive](hyp:hc), [the multiplier is nonnegative](hyp:hb), [the
qualification exponent exceeds one](hyp:hq), [the penalty is positive](hyp:hlam)
and [above the square-root stability threshold](hyp:hs), [it is no greater than
the balancing coefficient times the noise scale raised to the reciprocal of one
plus the qualification exponent](hyp:hupper), and [the bias coefficient times
the balancing coefficient to that exponent plus one is at most one half](hyp:hsmall).
Then [the bias coefficient times the penalty raised to the qualification exponent
is at most half the noise level at this penalty](goal). -/
-- @node: iterTraeOracle_crossing
lemma iterTraeOracle_crossing (Cb c b d q lam : ℝ)
    (hCb : 0 ≤ Cb) (hc : 0 < c) (hb : 0 ≤ b) (hq : 1 < q) (hlam : 0 < lam)
    (hs : Real.sqrt (b * d ^ 2) ≤ lam)
    (hupper : lam ≤ c * (b * d ^ 2) ^ (1 / (q + 1)))
    (hsmall : Cb * c ^ (q + 1) ≤ 1 / 2) :
    OracleCrossing (iterTraeNoiseLevel b d) Cb q lam := by
  have hs0 : 0 ≤ b * d ^ 2 := by positivity
  have hp : Cb * lam ^ (q + 1) ≤ 1 / 2 * (b * d ^ 2) := by
    calc
      _ ≤ Cb * (c * (b * d ^ 2) ^ (1 / (q + 1))) ^ (q + 1) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hlam.le hupper (by linarith)) hCb
      _ = (Cb * c ^ (q + 1)) * (b * d ^ 2) := by
        rw [Real.mul_rpow hc.le (by positivity), ← Real.rpow_mul hs0,
          one_div_mul_cancel (by linarith : q + 1 ≠ 0), Real.rpow_one]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hsmall hs0
  have hpower : lam ^ (q + 1) = lam ^ q * lam := by
    rw [Real.rpow_add hlam, Real.rpow_one]
  rw [hpower, ← mul_assoc] at hp
  have hdiv : Cb * lam ^ q ≤ 1 / 2 * (b * d ^ 2 / lam) := by
    calc
      Cb * lam ^ q ≤ (1 / 2 * (b * d ^ 2)) / lam := (le_div_iff₀ hlam).2 hp
      _ = _ := by ring
  unfold OracleCrossing genericBias
  rw [iterTraeNoiseLevel_stable b d lam hlam hs]
  nlinarith only [hdiv, sq_nonneg d]

/-- Given [a positive approximation coefficient](hyp:hCA), [a positive variance
coefficient](hyp:hCV), [a positive bias coefficient](hyp:hCb), [an admissible grid
ratio](hyp:hρ), [a positive balancing coefficient](hyp:hc), [a multiplier at least
two](hyp:hb), [a positive source exponent](hyp:hβ), and [a qualification exponent
greater than one](hyp:hq) [and no greater than one plus the source exponent](hyp:hqβ),
[there is a positive constant such that, whenever the positive noise scale is at
most one and a grid oracle lies above both the stability threshold and rounded
balancing scale, the discrepancy and accepted-stability comparisons and oracle
crossing on an event imply squared weak and strong errors of the discrepancy-selected
candidate bounded respectively by that constant times the scale to powers
q divided by q plus one and q minus one divided by q plus one](goal). -/
-- @node: iterTrae_rate_on_event
lemma iterTrae_rate_on_event (CA CV Cb ρ c b β q : ℝ)
    (hCA : 0 < CA) (hCV : 0 < CV) (hCb : 0 < Cb)
    (hρ : GridDomain ρ) (hc : 0 < c) (hb : 2 ≤ b)
    (hβ : 0 < β) (hq : 1 < q) (hqβ : q ≤ β + 1) :
    ∃ C > 0, ∀ {Ω H Q : Type*} [MeasurableSpace Ω]
      [NormedAddCommGroup H] [NormedAddCommGroup Q]
      [NormedSpace ℝ H] [NormedSpace ℝ Q]
      (P : Measure Ω) [IsProbabilityMeasure P] (T : H →L[ℝ] Q) (h₀ : H)
      (ξ : ℝ) (n : ℕ) (_hn : 0 < n) (d lamo : ℝ) (E : Set Ω)
      (candidate : ℝ → Ω → H) (D : Ω → H → ℝ),
      0 < b * d ^ 2 → b * d ^ 2 ≤ 1 → lamo ∈ regGrid ρ n →
      Real.sqrt (b * d ^ 2) ≤ lamo →
      ρ * (c * (b * d ^ 2) ^ (1 / (q + 1))) ≤ lamo →
      GenericEventComparisons P T h₀ ρ ξ CA CV Cb (β / (β + 1)) q n
        (Set.Icc lamo 2) E candidate D (iterTraeNoiseLevel b d) →
      OracleCrossing (iterTraeNoiseLevel b d) Cb q lamo →
      ∀ ω ∈ E,
        ‖T (candidate (selectedPenalty ρ n (fun l => D ω (candidate l ω))
          (iterTraeNoiseLevel b d)) ω - h₀)‖ ^ 2 ≤
          C * (b * d ^ 2) ^ (q / (q + 1)) ∧
        ‖candidate (selectedPenalty ρ n (fun l => D ω (candidate l ω))
          (iterTraeNoiseLevel b d)) ω - h₀‖ ^ 2 ≤
          C * (b * d ^ 2) ^ ((q - 1) / (q + 1)) := by
  let γ := β / (β + 1)
  have hγ : γ ∈ Set.Ioc (0 : ℝ) 1 := by
    dsimp [γ]
    exact ⟨by positivity, (div_le_one (by linarith)).2 (by linarith)⟩
  obtain ⟨K, hK, hDP⟩ := common_dp CA CV Cb γ q ⟨hCA, hCV, hCb, hγ, hq⟩
  let Ka := 1 + (ρ * c)⁻¹
  let Kv := (ρ * c)⁻¹ ^ 2
  have hr : 0 < ρ := by linarith [hρ.1]
  have hKa : 0 < Ka := by dsimp [Ka]; positivity
  have hKv : 0 ≤ Kv := sq_nonneg _
  let C := max (K * Ka) (K * (2 * Kv + Ka ^ γ))
  refine ⟨C, lt_of_lt_of_le (mul_pos hK hKa) (le_max_left _ _), ?_⟩
  intro Ω H Q _ _ _ _ _ P _ T h₀ ξ n hn d lamo E candidate D
    hd hs ho hstable hlower hcomp hcross ω hω
  have hoDom := trae_grid_domain ρ hρ n lamo ho
  have hNoise : NoiseLevelNonneg ρ n (iterTraeNoiseLevel b d) := by
    intro lam hlam
    have hl := (trae_grid_domain ρ hρ n lam hlam).1
    unfold iterTraeNoiseLevel iterTraeScale
    positivity
  have hDomain : StabilityRegionSubset (Set.Icc lamo 2) :=
    fun _ hx => ⟨hoDom.1.trans_le hx.1, hx.2⟩
  have hSegment : OracleSegmentStable ρ n (Set.Icc lamo 2) lamo :=
    ⟨ho, fun _ hx => hx.2⟩
  have hMono : NoiseLevelAntitoneOnSegment ρ n (iterTraeNoiseLevel b d) lamo := by
    intro x hx y hy hxy
    exact (iterTraeNoiseLevel_stable_comparison b d x y hb
      (hoDom.1.trans_le hx.2.1) hxy hy.2.2 (hstable.trans hx.2.1)).1
  have hselected := hDP P T h₀ ρ ξ hρ n hn (Set.Icc lamo 2) E lamo
    candidate D (iterTraeNoiseLevel b d) hNoise hDomain hcomp hSegment hMono
    hcross ω hω
  have hRates := iterTraeOracle_scalar_rates ρ c b q d lamo hr hc hb hq hd hs hlower
  have hratio := (iterTraeNoiseLevel_stable_comparison b d lamo lamo hb
    hoDom.1 le_rfl hoDom.2 hstable).2
  have hpower : (iterTraeNoiseLevel b d lamo) ^ γ ≤
      Ka ^ γ * (b * d ^ 2) ^ ((q - 1) / (q + 1)) := by
    calc
      _ ≤ (Ka * (b * d ^ 2) ^ (q / (q + 1))) ^ γ :=
        Real.rpow_le_rpow (hNoise lamo ho) hRates.1 hγ.1.le
      _ = Ka ^ γ * ((b * d ^ 2) ^ (q / (q + 1))) ^ γ :=
        Real.mul_rpow hKa.le (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (iterTrae_source_rate_power _ β q hd.le hs hβ hq hqβ) (by positivity)
  constructor
  · calc
      _ ≤ K * iterTraeNoiseLevel b d lamo := hselected.2.2.2.1
      _ ≤ (K * Ka) * (b * d ^ 2) ^ (q / (q + 1)) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hRates.1 hK.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · calc
      _ ≤ K * (iterTraeNoiseLevel b d lamo / lamo +
          (iterTraeNoiseLevel b d lamo) ^ γ) := hselected.2.2.2.2
      _ ≤ (K * (2 * Kv + Ka ^ γ)) * (b * d ^ 2) ^ ((q - 1) / (q + 1)) := by
        have hv := hRates.2
        change iterTraeStability b d lamo ≤ Kv * _ at hv
        have hsum := add_le_add (hratio.trans (mul_le_mul_of_nonneg_left hv (by norm_num)))
          hpower
        have hm := mul_le_mul_of_nonneg_left hsum hK.le
        nlinarith only [hm]
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- If [the multiplier is nonnegative](hyp:hb), [accuracy is nonnegative](hyp:hd),
and [the iteration horizon qualifies for the source exponent](hyp:hqual), [the
weak oracle power of multiplier times squared accuracy equals the multiplier to
power beta plus one divided by beta plus two times accuracy to twice that power,
and the strong oracle power equals the multiplier to power beta divided by beta
plus two times accuracy to twice that power](goal). -/
-- @node: iterTrae_qualified_scale_identities
lemma iterTrae_qualified_scale_identities (b d β : ℝ) (t : ℕ)
    (hb : 0 ≤ b) (hd : 0 ≤ d) (hqual : IterQualificationTRAE β t) :
    (b * d ^ 2) ^ (qualificationExponent β t / (qualificationExponent β t + 1)) =
        b ^ ((β + 1) / (β + 2)) * d ^ (2 * (β + 1) / (β + 2)) ∧
      (b * d ^ 2) ^ ((qualificationExponent β t - 1) / (qualificationExponent β t + 1)) =
        b ^ (β / (β + 2)) * d ^ (2 * β / (β + 2)) := by
  have hq : qualificationExponent β t = β + 1 := min_eq_left hqual
  rw [hq]
  constructor <;>
    rw [Real.mul_rpow hb (sq_nonneg d), ← Real.rpow_natCast,
      ← Real.rpow_mul hd] <;> congr 1 <;> congr 1 <;> ring

end Papers.TsAdaptiveEstimationInference
