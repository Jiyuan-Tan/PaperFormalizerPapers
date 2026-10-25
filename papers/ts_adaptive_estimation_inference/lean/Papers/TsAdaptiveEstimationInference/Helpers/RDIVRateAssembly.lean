module
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVOracle
public import Papers.TsAdaptiveEstimationInference.TCommonDp
/-! Deterministic assembly of the RDIV oracle rates from the common discrepancy principle. -/
public section

namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter
open scoped Topology

/-- [The RDIV noise level is nonincreasing as the positive regularization penalty increases](goal). -/
-- @node: rdiv_noise_antitoneOn
lemma rdiv_noise_antitoneOn (d v : ℝ) :
    AntitoneOn (rdivNoiseLevel d v) (Set.Ioi 0) := by
  intro x hx y hy hxy
  exact add_le_add (div_le_div_of_nonneg_left (sq_nonneg d) hx hxy) (le_refl (v ^ 2))

/-- For [a target vector h₀](hyp:h₀), suppose [E is measurable](hyp:hE), [E has probability at least one minus ξ](hyp:hprob), [the strong-error constant CV is nonnegative](hyp:hCV), [the candidate discrepancy is nonnegative on E at every grid penalty](hyp:hD), [that discrepancy is bounded by the RDIV noise plus Cb times the penalty raised to p](hyp:henvelope), and [on E at every grid penalty the squared weak error is at most CA times the sum of discrepancy and noise, while the squared strong error is at most CV times the sum of RDIV stability and the α-th power of that same discrepancy-and-noise sum](hyp:haccepted). Then [these candidates and discrepancies satisfy the generic event comparisons on the penalty interval `(0, 2]`, with the same constants and RDIV noise level](goal). -/
-- @node: rdiv_generic_comparisons_of_accepted_bounds
lemma rdiv_generic_comparisons_of_accepted_bounds
    {Ω H Q : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedAddCommGroup Q]
    [NormedSpace ℝ H] [NormedSpace ℝ Q]
    (P : Measure Ω) (T : H →L[ℝ] Q) (h₀ : H)
    (ρ ξ CA CV Cb α p d v : ℝ) (n : ℕ) (E : Set Ω)
    (candidate : ℝ → Ω → H) (D : Ω → H → ℝ)
    (hE : MeasurableSet E) (hprob : 1 - ξ ≤ P.real E)
    (hCV : 0 ≤ CV)
    (hD : ∀ ω ∈ E, ∀ lam ∈ regGrid ρ n, 0 ≤ D ω (candidate lam ω))
    (henvelope : ∀ ω ∈ E, ∀ lam ∈ regGrid ρ n,
      D ω (candidate lam ω) ≤ rdivNoiseLevel d v lam + Cb * lam ^ p)
    (haccepted : ∀ ω ∈ E, ∀ lam ∈ regGrid ρ n,
      ‖T (candidate lam ω - h₀)‖ ^ 2 ≤
        CA * (D ω (candidate lam ω) + rdivNoiseLevel d v lam) ∧
      ‖candidate lam ω - h₀‖ ^ 2 ≤ CV * (rdivStability d lam +
        (D ω (candidate lam ω) + rdivNoiseLevel d v lam) ^ α)) :
    GenericEventComparisons P T h₀ ρ ξ CA CV Cb α p n (Set.Ioc 0 2) E
      candidate D (rdivNoiseLevel d v) := by
  refine ⟨hE, hprob, ?_⟩
  intro ω hω lam hlam hdom
  refine ⟨henvelope ω hω lam hlam, (haccepted ω hω lam hlam).1, ?_⟩
  apply (haccepted ω hω lam hlam).2.trans
  apply mul_le_mul_of_nonneg_left _ hCV
  apply add_le_add _ le_rfl
  have hnum : d ^ 2 / lam ≤ D ω (candidate lam ω) + rdivNoiseLevel d v lam := by
    dsimp [rdivNoiseLevel]
    linarith only [hD ω hω lam hlam, sq_nonneg v]
  calc
    rdivStability d lam = (d ^ 2 / lam) / lam := by
      unfold rdivStability
      ring
    _ ≤ _ := div_le_div_of_nonneg_right hnum hdom.1.le

/-- Suppose [ρ defines an admissible geometric grid](hyp:hρ), [the oracle scale c is positive](hyp:hc), [the source exponent β is positive](hyp:hβ), [the weak-error constant CA is positive](hyp:hCA), [the strong-error constant CV is positive](hyp:hCV), [the bias constant Cb is positive](hyp:hCb), [Cb times c raised to one plus the bias exponent is at most one half](hyp:hsmallFit), and [Cb times c raised to the bias exponent is at most one half](hyp:hsmallCal). Then [a positive constant uniformly bounds the selected candidate's squared weak error by the RDIV error scale and its squared strong error by the sum of the fitting power and the interpolated error scale; whenever the positive fitting error, nonnegative calibration error, positive sample size, grid oracle within the prescribed rounding bounds, and generic event comparisons are given, the discrepancy rule accepts, selects a penalty at least the oracle penalty, and the strong bound is at most twice that constant times the interpolated error scale](goal). -/
-- @node: rdiv_common_dp_oracle_rates
lemma rdiv_common_dp_oracle_rates (CA CV Cb ρ c β : ℝ)
    (hρ : GridDomain ρ) (hc : 0 < c) (hβ : 0 < β)
    (hCA : 0 < CA) (hCV : 0 < CV) (hCb : 0 < Cb)
    (hsmallFit : Cb * c ^ (biasExponent β + 1) ≤ 1 / 2)
    (hsmallCal : Cb * c ^ biasExponent β ≤ 1 / 2) :
    ∃ C > 0, ∀ {Ω H Q : Type*} [MeasurableSpace Ω]
      [NormedAddCommGroup H] [NormedAddCommGroup Q]
      [NormedSpace ℝ H] [NormedSpace ℝ Q]
      (P : Measure Ω) [IsProbabilityMeasure P] (T : H →L[ℝ] Q) (h₀ : H)
      (ξ d v : ℝ) (n : ℕ) (hn : 0 < n) (E : Set Ω) (lamo : ℝ)
      (candidate : ℝ → Ω → H) (D : Ω → H → ℝ)
      (hd : 0 < d) (hv : 0 ≤ v)
      (hgrid : lamo ∈ regGrid ρ n) (hlam : 0 < lamo)
      (hlower : ρ * (c * max (d ^ (2 / (biasExponent β + 1)))
        (v ^ (2 / biasExponent β))) ≤ lamo)
      (hupper : lamo ≤ c * max (d ^ (2 / (biasExponent β + 1)))
        (v ^ (2 / biasExponent β)))
      (hComparisons : GenericEventComparisons P T h₀ ρ ξ CA CV Cb
        (interpolationExponent β) (biasExponent β) n (Set.Ioc 0 2) E
        candidate D (rdivNoiseLevel d v)),
      ∀ ω ∈ E,
        let lam := selectedPenalty ρ n (fun l => D ω (candidate l ω)) (rdivNoiseLevel d v)
        Accepts ρ n (fun l => D ω (candidate l ω)) (rdivNoiseLevel d v) ∧
        lamo ≤ lam ∧
        ‖T (candidate lam ω - h₀)‖ ^ 2 ≤ C * rdivErrorScale β d v ∧
        ‖candidate lam ω - h₀‖ ^ 2 ≤ C *
          (d ^ (2 * (biasExponent β - 1) / (biasExponent β + 1)) +
            rdivErrorScale β d v ^ interpolationExponent β) ∧
        C * (d ^ (2 * (biasExponent β - 1) / (biasExponent β + 1)) +
          rdivErrorScale β d v ^ interpolationExponent β) ≤
            (2 * C) * rdivErrorScale β d v ^ interpolationExponent β := by
  have hp := (rdiv_interpolation_exponent_identity β hβ).1
  have hb : 0 < truncatedSource β := lt_min hβ zero_lt_one
  have hα : 0 < interpolationExponent β := div_pos hb (by linarith)
  have hα1 : interpolationExponent β ≤ 1 := by
    apply (div_le_one (by linarith : 0 < 1 + truncatedSource β)).2
    linarith
  obtain ⟨Cd, hCd, hdp⟩ := common_dp CA CV Cb (interpolationExponent β)
    (biasExponent β) ⟨hCA, hCV, hCb, ⟨hα, hα1⟩, hp⟩
  let K := (ρ * c)⁻¹
  let N := K + 1
  let C := Cd * (N + K ^ 2 + K + N ^ interpolationExponent β)
  have hρpos : 0 < ρ := by linarith only [hρ.1]
  have hK : 0 < K := by dsimp [K]; positivity
  have hN : 0 < N := by dsimp [N]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Ω H Q _ _ _ _ _ P _ T h₀ ξ d v n hn E lamo candidate D
    hd hv hgrid hlam hlower hupper hComparisons ω hω
  have hnoise : NoiseLevelNonneg ρ n (rdivNoiseLevel d v) := by
    intro l hl
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hl
    have hlpos : 0 < gridValue ρ k := mul_pos (by norm_num) (pow_pos hρpos k)
    exact add_nonneg (div_nonneg (sq_nonneg d) hlpos.le) (sq_nonneg v)
  have hsegment : OracleSegmentStable ρ n (Set.Ioc 0 2) lamo :=
    ⟨hgrid, fun _ h => ⟨hlam.trans_le h.2.1, h.2.2⟩⟩
  have hmono : NoiseLevelAntitoneOnSegment ρ n (rdivNoiseLevel d v) lamo := by
    intro x hx y hy hxy
    exact rdiv_noise_antitoneOn d v (hlam.trans_le hx.2.1)
      (hlam.trans_le hy.2.1) hxy
  have hcross : OracleCrossing (rdivNoiseLevel d v) Cb (biasExponent β) lamo :=
    rdiv_oracle_bias_crossing Cb c (biasExponent β) d v lamo hCb.le hc.le
      (by linarith) hd.le hv hlam hupper hsmallFit hsmallCal
  obtain ⟨haccept, _, hselected, hweak, hstrong⟩ := hdp P T h₀ ρ ξ hρ n hn
    (Set.Ioc 0 2) E lamo candidate D (rdivNoiseLevel d v) hnoise
    (fun _ h => h) hComparisons hsegment hmono hcross ω hω
  have hε : 0 ≤ rdivErrorScale β d v :=
    add_nonneg (Real.rpow_nonneg hd.le _) (sq_nonneg v)
  have hεα : 0 ≤ rdivErrorScale β d v ^ interpolationExponent β := by positivity
  have hfit : 0 ≤ d ^ (2 * (biasExponent β - 1) / (biasExponent β + 1)) := by
    positivity
  have hnr := rdiv_oracle_noise_rate ρ c (biasExponent β) d v lamo
    hρpos hc (by linarith) hd hlower
  have hratio := rdiv_oracle_noise_ratio_rate ρ c β d v lamo
    hρpos hc hβ hd hv hlower
  have hpower : rdivNoiseLevel d v lamo ^ interpolationExponent β ≤
      N ^ interpolationExponent β * rdivErrorScale β d v ^ interpolationExponent β := by
    rw [← Real.mul_rpow hN.le hε]
    exact Real.rpow_le_rpow (add_nonneg
      (div_nonneg (sq_nonneg d) hlam.le) (sq_nonneg v)) hnr hα.le
  refine ⟨haccept, hselected, ?_, ?_,
    rdiv_strong_rate_simplification β d v C hβ hd.le hC.le⟩
  · apply hweak.trans
    have hcN : Cd * N ≤ C := by
      dsimp [C]
      nlinarith only [sq_nonneg K, hK, Real.rpow_pos_of_pos hN (interpolationExponent β), hCd]
    calc
      _ ≤ Cd * (N * rdivErrorScale β d v) := mul_le_mul_of_nonneg_left hnr hCd.le
      _ = Cd * N * rdivErrorScale β d v := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcN hε
  · apply hstrong.trans
    have h₁ := mul_le_mul_of_nonneg_left (add_le_add hratio hpower) hCd.le
    have h₂ : Cd * K ^ 2 ≤ C := by
      dsimp [C]
      nlinarith only [hN, hK, Real.rpow_pos_of_pos hN (interpolationExponent β), hCd]
    have h₃ : Cd * (K + N ^ interpolationExponent β) ≤ C := by
      dsimp [C]
      nlinarith only [hN, sq_nonneg K, hCd]
    nlinarith only [h₁, mul_le_mul_of_nonneg_right h₂ hfit,
      mul_le_mul_of_nonneg_right h₃ hεα]

/-- For [a target vector h₀](hyp:h₀), suppose [ρ defines an admissible grid](hyp:hρ), [β is positive](hyp:hβ), [CA is positive](hyp:hCA), [CV is positive](hyp:hCV), [Cb is positive](hyp:hCb), [the fitting scale δ is nonnegative](hyp:hδ), [the calibration scale ν is nonnegative](hyp:hν), [δ converges to zero](hyp:hδlim), [ν converges to zero](hyp:hνlim), and [δ squared is eventually at least the reciprocal sample size](hyp:hfloor). Then [there is a positive constant such that, for all sufficiently large sample sizes and every event satisfying the generic comparisons, the selected candidate's squared weak error is bounded by that constant times the RDIV error scale, its squared strong error is bounded by that constant times the sum of the fitting power and the interpolated error scale, and this last bound is at most twice the constant times the interpolated error scale](goal). -/
-- @node: rdiv_eventual_rates_of_comparisons
lemma rdiv_eventual_rates_of_comparisons
    {Ω H Q : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedAddCommGroup Q]
    [NormedSpace ℝ H] [NormedSpace ℝ Q]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : H →L[ℝ] Q) (h₀ : H)
    (CA CV Cb ρ ξ β : ℝ) (δ ν : ℕ → ℝ)
    (candidate : ℕ → ℝ → Ω → H) (D : ℕ → Ω → H → ℝ)
    (hρ : GridDomain ρ) (hβ : 0 < β)
    (hCA : 0 < CA) (hCV : 0 < CV) (hCb : 0 < Cb)
    (hδ : ∀ n, 0 ≤ δ n) (hν : ∀ n, 0 ≤ ν n)
    (hδlim : Tendsto δ atTop (𝓝 0)) (hνlim : Tendsto ν atTop (𝓝 0))
    (hfloor : ∀ᶠ n : ℕ in atTop, 1 / (n : ℝ) ≤ δ n ^ 2) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop, ∀ E : Set Ω,
      GenericEventComparisons P T h₀ ρ ξ CA CV Cb
        (interpolationExponent β) (biasExponent β) n (Set.Ioc 0 2) E
        (candidate n) (D n) (rdivNoiseLevel (δ n) (ν n)) →
      ∀ ω ∈ E,
        let lam := selectedPenalty ρ n (fun l => D n ω (candidate n l ω))
          (rdivNoiseLevel (δ n) (ν n))
        ‖T (candidate n lam ω - h₀)‖ ^ 2 ≤ C * rdivErrorScale β (δ n) (ν n) ∧
        ‖candidate n lam ω - h₀‖ ^ 2 ≤ C *
          (δ n ^ (2 * (biasExponent β - 1) / (biasExponent β + 1)) +
            rdivErrorScale β (δ n) (ν n) ^ interpolationExponent β) ∧
        C * (δ n ^ (2 * (biasExponent β - 1) / (biasExponent β + 1)) +
          rdivErrorScale β (δ n) (ν n) ^ interpolationExponent β) ≤
            (2 * C) * rdivErrorScale β (δ n) (ν n) ^ interpolationExponent β := by
  let c := 1 / (2 * (Cb + 1))
  have hc : 0 < c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 :=
    (div_le_one (by positivity : 0 < 2 * (Cb + 1))).2 (by linarith)
  have hp := (rdiv_interpolation_exponent_identity β hβ).1
  have hsmall : ∀ p : ℝ, 1 ≤ p → Cb * c ^ p ≤ 1 / 2 := by
    intro p hp
    have hpow := Real.rpow_le_self_of_le_one hc.le hc1 hp
    have hmul : Cb * c ≤ 1 / 2 := by
      dsimp [c]
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      field_simp
      linarith
    exact (mul_le_mul_of_nonneg_left hpow hCb.le).trans hmul
  obtain ⟨C, hC, hrates⟩ := rdiv_common_dp_oracle_rates CA CV Cb ρ c β
    hρ hc hβ hCA hCV hCb (hsmall _ (by linarith)) (hsmall _ hp.le)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hfloor, (tendsto_order.1 hδlim).2 c hc,
    (tendsto_order.1 hνlim).2 1 zero_lt_one, eventually_gt_atTop 0]
    with n hfn hdn hvn hn
  intro E hcomp ω hω
  have hd : 0 < δ n := by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hfpos : 0 < 1 / (n : ℝ) := by positivity
    nlinarith only [hfn, hfpos, hδ n]
  obtain ⟨hgrid, hlower, hupper⟩ := rdiv_small_noise_oracle ρ c (biasExponent β)
    (δ n) (ν n) n hρ hc hc1 hp hd hdn.le (hν n) hvn.le hn hfn
  have hlam : 0 < oraclePoint ρ n
      (c * max (δ n ^ (2 / (biasExponent β + 1))) (ν n ^ (2 / biasExponent β))) := by
    have hρpos : 0 < ρ := by linarith only [hρ.1]
    exact lt_of_lt_of_le (by positivity) hlower
  exact (hrates P T h₀ ξ (δ n) (ν n) n hn E _ (candidate n) (D n)
    hd (hν n) hgrid hlam hlower hupper hcomp ω hω).2.2

end Papers.TsAdaptiveEstimationInference
