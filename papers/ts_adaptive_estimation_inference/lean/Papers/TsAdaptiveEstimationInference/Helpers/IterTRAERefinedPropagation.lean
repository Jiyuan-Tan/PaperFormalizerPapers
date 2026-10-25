module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAEStability
/-! Propagation with the preliminary accuracy retained for discrepancy calibration. -/
@[expose] public section
set_option linter.style.longLine false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter
open scoped Topology
variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]

/-- For [an envelope bound](hyp:B), [a concentration-event constant](hyp:Cevent),
and [an iteration horizon](hyp:t), [the preliminary noise coefficient](goal) is
computed by [forming sixteen times the square of a sum whose first term is the
product of the event constant squared plus twice that constant plus one with the
envelope bound plus one, and whose second term is twice the event constant plus
one](step:1), [forming sixteen
times the square of the event constant squared plus five times that constant
plus two](step:2), and [multiplying twice the second quantity by one plus the
horizon-th power of twice the first quantity plus one](step:3). -/
-- @node: iterTraeNoiseConstant
noncomputable def iterTraeNoiseConstant (B Cevent : ℝ) (t : ℕ) : ℝ :=
  let A := 16 * ((Cevent ^ 2 + 2 * Cevent + 1) * (B + 1) + 2 * Cevent + 1) ^ 2
  let W := 16 * ((Cevent ^ 2 + 4 * Cevent + 1) + Cevent + 1) ^ 2
  2 * W * ((2 * A + 1) ^ t + 1)

/-- Suppose [the grid ratio is admissible](hyp:hρ), [the horizon is at least
one](hyp:ht), [the noise multiplier is at least one](hyp:hb), [the range
condition holds](hyp:hRange), [the model satisfies the source condition with the
given exponent and witness](hyp:hSource), [the closeness condition holds](hyp:hClose),
[the model is bounded](hyp:hBound), [a common null-set envelope holds](hyp:hCommon),
and [the concentration-event constant is positive](hyp:hCevent). Then [there is
a positive bias coefficient, uniform over balancing coefficients, such that
iterative realizability and attained minima imply, at positive sample sizes with
nonnegative preliminary radius and a grid reaching the balancing scale, terminal
population loss on any common concentration event is bounded throughout the
oracle segment by the preliminary noise coefficient times squared radius plus
the noise multiplier times squared radius divided by penalty, plus the bias
coefficient times squared source-witness norm times penalty to the qualification
exponent](goal). -/
-- @node: iter_trae_preliminary_weak_bound_uniform
lemma iter_trae_preliminary_weak_bound_uniform
    (V : IVWorld 𝒲 𝒳 𝒵) (P : Measure Ω) [IsProbabilityMeasure P]
    (sample : AnalysisSample V P) (split : SampleSplit)
    (ρ b β B Cevent : ℝ) (t : ℕ) (δ r : ℕ → ℝ)
    (w₀ : V.Hbar.toSubmodule)
    (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (hρ : GridDomain ρ) (ht : 1 ≤ t) (hb : 1 ≤ b)
    (hRange : RangeCondition V) (hSource : BetaSourceCondition V β w₀)
    (hClose : ClosenessCondition V) (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B)
    (hCevent : 0 < Cevent) :
    ∃ C > 0, ∀ c : ℝ, IterRealizableTRAE V ρ c b β t δ →
      IterTRAEMinimaAttained V P sample split ρ t iter → ∀ n, 0 < n → 0 ≤ r n →
      gridValue ρ (terminalIndex ρ n) ≤
        c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1)) →
      ∀ E : Set Ω,
      IterTRAEConcentrationOn V P sample split ρ c b β t δ r iter n E Cevent →
      ∀ ω ∈ E, ∀ lam ∈ regGrid ρ n,
      lam ∈ Set.Icc (iterTraeOraclePoint ρ c b β t δ n) 2 →
      traePopulationLoss V (iter n t lam ω) ≤
        iterTraeNoiseConstant B Cevent t * (r n ^ 2 + b * r n ^ 2 / lam) +
          C * ‖w₀‖ ^ 2 * lam ^ qualificationExponent β t := by
  let A := 16 * ((Cevent ^ 2 + 2 * Cevent + 1) * (B + 1) + 2 * Cevent + 1) ^ 2
  let D := 2 * A + 1
  let W := 16 * ((Cevent ^ 2 + 4 * Cevent + 1) + Cevent + 1) ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 1 ≤ D := by dsimp [D]; linarith only [hA]
  have hD0 : 0 ≤ D := by linarith only [hD]
  have hW : 0 ≤ W := by dsimp [W]; positivity
  obtain ⟨Cb, hCb, hbias⟩ := iter_bias V β w₀ hRange hSource t ht
  let R := D ^ t
  have hR : 1 ≤ R := one_le_pow₀ hD
  refine ⟨(2 * W + 2) * Cb, by positivity, ?_⟩
  intro c hIterRealizable hIterMinima n hn hr hOracle E hEvent ω hω lam hl hs
  have hgridDomain (lam : ℝ) (hl : lam ∈ regGrid ρ n) : 0 < lam := by
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hl
    exact mul_pos (by norm_num) (pow_pos (by linarith only [hρ.1]) k)
  have hstrong (lam : ℝ) (hl : lam ∈ regGrid ρ n)
      (hs : lam ∈ Set.Icc (iterTraeOraclePoint ρ c b β t δ n) 2) :
      ∀ j, j ≤ t → iterStrongVariance V j lam (iter n j lam ω) ^ 2 ≤
        D ^ j * (r n ^ 2 / lam ^ 2) := by
    exact iter_trae_strong_variance_explicit V P sample split ρ c b β B Cevent t
      δ r iter hρ hRange hClose hBound hCommon hCevent hIterRealizable hIterMinima
      n hn hr hOracle E hEvent ω hω lam hl hs
  have hlam := hgridDomain lam hl
  have hEst := (hIterMinima n hn lam hl).1
  have hStar := hIterRealizable n hOracle t ht le_rfl lam hl hs
  have hstep := (iter_trae_step_bounds V P sample split ρ c b β B Cevent
    t n t δ r iter E hRange hClose hBound hCommon hCevent.le hr hOracle hEvent
    ω hω lam hl hs hlam ht le_rfl hStar hEst).2
  let p := iterStrongVariance V (t - 1) lam (iter n (t - 1) lam ω)
  let u := iterWeakVariance V t lam (iter n t lam ω)
  let v := iterWeakBias V t lam
  change u ^ 2 ≤ W * (v ^ 2 + r n ^ 2 + lam * p ^ 2) at hstep
  have hpStrong : p ^ 2 ≤ R * (r n ^ 2 / lam ^ 2) := by
    exact (hstrong lam hl hs (t - 1) (by omega)).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hD (by omega : t - 1 ≤ t))
        (by positivity))
  have hp : lam * p ^ 2 ≤ R * (b * r n ^ 2 / lam) := by
    have hi := mul_le_mul_of_nonneg_left hpStrong hlam.le
    have he : lam * (R * (r n ^ 2 / lam ^ 2)) = R * (r n ^ 2 / lam) := by
      field_simp
    rw [he] at hi
    exact hi.trans (mul_le_mul_of_nonneg_left
      (by apply div_le_div_of_nonneg_right _ hlam.le; nlinarith only [hb, sq_nonneg (r n)])
      (by positivity))
  have hv : v ^ 2 ≤ Cb * ‖w₀‖ ^ 2 * lam ^ qualificationExponent β t :=
    (hbias lam hlam).2.2.2.1
  have htriangle : traePopulationLoss V (iter n t lam ω) ≤ 2 * u ^ 2 + 2 * v ^ 2 := by
    rw [traePopulationLoss_eq V hRange hClose _ ((hEst.2 t ht le_rfl ω).1)]
    have heq : projCondExpOp V (iter n t lam ω - minNormSolution V) =
        projCondExpOp V (iter n t lam ω - populationIterate V lam t) +
          projCondExpOp V (populationIterate V lam t - minNormSolution V) := by
      simp only [map_sub]
      abel
    have hn := norm_add_le (projCondExpOp V (iter n t lam ω - populationIterate V lam t))
      (projCondExpOp V (populationIterate V lam t - minNormSolution V))
    rw [← heq] at hn
    change ‖projCondExpOp V (iter n t lam ω - minNormSolution V)‖ ≤ u + v at hn
    have hu : 0 ≤ u := norm_nonneg _
    have hv : 0 ≤ v := norm_nonneg _
    nlinarith only [hn, hu, hv, norm_nonneg (projCondExpOp V (iter n t lam ω - minNormSolution V)), sq_nonneg (u - v)]
  have hstep' := hstep.trans (mul_le_mul_of_nonneg_left
    (show v ^ 2 + r n ^ 2 + lam * p ^ 2 ≤
      v ^ 2 + r n ^ 2 + R * (b * r n ^ 2 / lam) by linarith only [hp]) hW)
  have hnoise : r n ^ 2 + R * (b * r n ^ 2 / lam) ≤
      (R + 1) * (r n ^ 2 + b * r n ^ 2 / lam) := by
    nlinarith only [mul_nonneg (show 0 ≤ R by positivity) (sq_nonneg (r n)),
      show 0 ≤ b * r n ^ 2 / lam by positivity]
  have hn := mul_le_mul_of_nonneg_left hnoise (show 0 ≤ 2 * W by positivity)
  have hv' := mul_le_mul_of_nonneg_left hv (show 0 ≤ 2 * W + 2 by positivity)
  change traePopulationLoss V (iter n t lam ω) ≤
    (2 * W * (R + 1)) * (r n ^ 2 + b * r n ^ 2 / lam) +
      ((2 * W + 2) * Cb) * ‖w₀‖ ^ 2 * lam ^ qualificationExponent β t
  nlinarith only [htriangle, hstep', hn, hv']

/-- Suppose [the grid ratio is admissible](hyp:hρ), [the horizon is at least
one](hyp:ht), [the noise multiplier is at least one](hyp:hb), [the range condition
holds](hyp:hRange), [the source condition holds with the given exponent and
witness](hyp:hSource), [the closeness condition holds](hyp:hClose), [the model is
bounded](hyp:hBound), [a common null-set envelope holds](hyp:hCommon), [the event
constant is positive](hyp:hCevent), [the iterative population sequence is
realizable](hyp:hIterRealizable), and [the iterative empirical minima are
attained](hyp:hIterMinima). Then [one positive bias coefficient bounds terminal
population loss on every common concentration event and throughout the oracle
segment, at positive sample sizes with nonnegative preliminary radius and a
grid reaching the balancing scale, by the preliminary noise coefficient times
squared radius plus multiplier times squared radius divided by penalty, plus
the bias coefficient times squared source-witness norm times penalty to the
qualification exponent](goal). -/
-- @node: iter_trae_preliminary_weak_bound
lemma iter_trae_preliminary_weak_bound
    (V : IVWorld 𝒲 𝒳 𝒵) (P : Measure Ω) [IsProbabilityMeasure P]
    (sample : AnalysisSample V P) (split : SampleSplit)
    (ρ c b β B Cevent : ℝ) (t : ℕ) (δ r : ℕ → ℝ)
    (w₀ : V.Hbar.toSubmodule)
    (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (hρ : GridDomain ρ) (ht : 1 ≤ t) (hb : 1 ≤ b)
    (hRange : RangeCondition V) (hSource : BetaSourceCondition V β w₀)
    (hClose : ClosenessCondition V) (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B)
    (hCevent : 0 < Cevent)
    (hIterRealizable : IterRealizableTRAE V ρ c b β t δ)
    (hIterMinima : IterTRAEMinimaAttained V P sample split ρ t iter) :
    ∃ C > 0, ∀ n, 0 < n → 0 ≤ r n →
      gridValue ρ (terminalIndex ρ n) ≤
        c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1)) →
      ∀ E : Set Ω,
      IterTRAEConcentrationOn V P sample split ρ c b β t δ r iter n E Cevent →
      ∀ ω ∈ E, ∀ lam ∈ regGrid ρ n,
      lam ∈ Set.Icc (iterTraeOraclePoint ρ c b β t δ n) 2 →
      traePopulationLoss V (iter n t lam ω) ≤
        iterTraeNoiseConstant B Cevent t * (r n ^ 2 + b * r n ^ 2 / lam) +
          C * ‖w₀‖ ^ 2 * lam ^ qualificationExponent β t := by
  obtain ⟨C, hC, h⟩ := iter_trae_preliminary_weak_bound_uniform V P sample split
    ρ b β B Cevent t δ r w₀ iter hρ ht hb hRange hSource hClose hBound hCommon hCevent
  exact ⟨C, hC, h c hIterRealizable hIterMinima⟩

/-- If [the grid ratio is admissible](hyp:hρ), [the balancing coefficient is
positive](hyp:hc), [the noise multiplier is at least two](hyp:hb), [the source
exponent is positive](hyp:hβ), [the iteration horizon is at least one](hyp:ht),
and [the accuracy curve is calibrated to the complexity curve and confidence
allocation](hyp:hScale), then [eventually the grid reaches the balancing radius
and the oracle penalty is at least the square root of the multiplier times
squared accuracy](goal). -/
-- @node: iterTraeOraclePoint_stable_eventually
lemma iterTraeOraclePoint_stable_eventually (ρ c b β : ℝ) (t : ℕ)
    (δ : ℕ → ℝ) (tildeδ : ℕ → ℝ → ℝ) (allocation : ℕ → ℝ)
    (hρ : GridDomain ρ) (hc : 0 < c) (hb : 2 ≤ b) (hβ : 0 < β) (ht : 1 ≤ t)
    (hScale : TRAEScaleCalibration δ tildeδ allocation) :
    ∀ᶠ n in atTop,
      (∃ k ≤ terminalIndex ρ n, gridValue ρ k ≤
        c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))) ∧
      Real.sqrt (b * δ n ^ 2) ≤ iterTraeOraclePoint ρ c b β t δ n := by
  let q := qualificationExponent β t
  let a := 1 / (q + 1)
  have hq : 1 < q := by
    dsimp [q, qualificationExponent]
    have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
    exact lt_min (by linarith) (by linarith)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha' : a < 1 / 2 := by
    dsimp [a]
    apply (div_lt_div_iff₀ (by linarith : 0 < q + 1) (by norm_num : (0 : ℝ) < 2)).2
    linarith
  have hs : Tendsto (fun n => b * δ n ^ 2) atTop (𝓝 0) := by
    simpa using (hScale.2.pow 2).const_mul b
  have hsmall := (hs.rpow_const_nhds_zero (by linarith : 0 < 1 / 2 - a)).eventually
    (gt_mem_nhds (show 0 < ρ * c by have := hρ.1; positivity))
  have hradius : Tendsto (fun n => c * (b * δ n ^ 2) ^ a) atTop (𝓝 0) := by
    simpa using (hs.rpow_const_nhds_zero ha).const_mul c
  have hsmall' := hradius.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 2))
  filter_upwards [iterTraeOraclePoint_eventually ρ c b β t δ tildeδ allocation
    hρ hc hb hβ ht hScale, hsmall, hsmall'] with n hn hpow hr
  obtain ⟨k, hk, hkr, hfirst, heq⟩ := hn
  have hterminal : gridValue ρ (terminalIndex ρ n) ≤ c * (b * δ n ^ 2) ^ a :=
    (show gridValue ρ (terminalIndex ρ n) ≤ gridValue ρ k from
      mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one (by linarith only [hρ.1]) hρ.2.le hk) (by norm_num)).trans hkr
  refine ⟨⟨k, hk, hkr⟩, ?_⟩
  have hlower := (oraclePoint_radius_bounds ρ _ n hρ hr.le hterminal).2.1
  change ρ * (c * (b * δ n ^ 2) ^ a) ≤ iterTraeOraclePoint ρ c b β t δ n at hlower
  apply le_trans _ hlower
  have hnonneg : 0 ≤ b * δ n ^ 2 := by positivity
  by_cases hz : b * δ n ^ 2 = 0
  · simp [hz, Real.zero_rpow (ne_of_gt ha)]
  · have hpos : 0 < b * δ n ^ 2 := lt_of_le_of_ne hnonneg (Ne.symm hz)
    rw [Real.sqrt_eq_rpow]
    calc
      (b * δ n ^ 2) ^ (1 / 2 : ℝ) =
          (b * δ n ^ 2) ^ (1 / 2 - a) * (b * δ n ^ 2) ^ a := by
        rw [← Real.rpow_add hpos]; congr 1; ring
      _ ≤ (ρ * c) * (b * δ n ^ 2) ^ a :=
        mul_le_mul_of_nonneg_right hpow.le (by positivity)
      _ = _ := by ring

end Papers.TsAdaptiveEstimationInference
