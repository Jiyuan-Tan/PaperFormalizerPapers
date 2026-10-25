module
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVOracle
public import Papers.TsAdaptiveEstimationInference.TCommonDp
/-! Deterministic selection and refined strong rates for iterative RDIV.

These implications consume the on-event conclusions of discrepancy and accepted
bounds. They construct no concentration event and supply no statistical premise.
-/
public section

namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory

/-- If [the propagation coefficient is nonnegative](hyp:ha), then [both the iterative
noise level and the iterative stability scale weakly decrease as the positive penalty
increases](goal). -/
-- @node: iter_rdiv_scales_antitoneOn
lemma iter_rdiv_scales_antitoneOn (a d v : ℝ) (ha : 0 ≤ a) :
    AntitoneOn (iterRdivNoiseLevel a d v) (Set.Ioi 0) ∧
      AntitoneOn (iterRdivStability a d) (Set.Ioi 0) := by
  constructor
  · intro x hx y hy hxy
    exact add_le_add
      (div_le_div_of_nonneg_left (mul_nonneg ha (sq_nonneg d)) hx hxy) le_rfl
  · intro x hx y hy hxy
    exact div_le_div_of_nonneg_left (mul_nonneg ha (sq_nonneg d))
      (sq_pos_of_pos hx) (pow_le_pow_left₀ hx.le hxy 2)

/-- For [a target in the parameter space](hyp:h₀), suppose [the event is measurable](hyp:hE)
and [has probability at least one minus the confidence level](hyp:hprob), [the penalty
segment contains only positive penalties at most two](hyp:hS), and [the strong-error comparison coefficient
is nonnegative](hyp:hCV). If, throughout that event and grid segment, [the discrepancy
is nonnegative](hyp:hD), [it is bounded by iterative noise plus the penalty-power bias
envelope](hyp:henvelope), and [projected squared error is bounded by a constant times
discrepancy plus noise while strong squared error is bounded by a constant times iterative
stability plus that sum raised to the interpolation exponent](hyp:haccepted), then [the
same measurable event and probability bound satisfy the discrepancy and projected-error
comparisons and the generic strong-error comparison, whose linear term is discrepancy
plus noise divided by penalty](goal). -/
-- @node: iter_rdiv_generic_comparisons_of_accepted_bounds
lemma iter_rdiv_generic_comparisons_of_accepted_bounds
    {Ω H Q : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedAddCommGroup Q]
    [NormedSpace ℝ H] [NormedSpace ℝ Q]
    (P : Measure Ω) (T : H →L[ℝ] Q) (h₀ : H)
    (ρ ξ CA CV Cb γ q a d v : ℝ) (n : ℕ) (S : Set ℝ) (E : Set Ω)
    (candidate : ℝ → Ω → H) (D : Ω → H → ℝ)
    (hE : MeasurableSet E) (hprob : 1 - ξ ≤ P.real E)
    (hS : StabilityRegionSubset S) (hCV : 0 ≤ CV)
    (hD : ∀ ω ∈ E, ∀ lam ∈ regGrid ρ n, lam ∈ S →
      0 ≤ D ω (candidate lam ω))
    (henvelope : ∀ ω ∈ E, ∀ lam ∈ regGrid ρ n, lam ∈ S →
      D ω (candidate lam ω) ≤ iterRdivNoiseLevel a d v lam + Cb * lam ^ q)
    (haccepted : ∀ ω ∈ E, ∀ lam ∈ regGrid ρ n, lam ∈ S →
      ‖T (candidate lam ω - h₀)‖ ^ 2 ≤
        CA * (D ω (candidate lam ω) + iterRdivNoiseLevel a d v lam) ∧
      ‖candidate lam ω - h₀‖ ^ 2 ≤ CV * (iterRdivStability a d lam +
        (D ω (candidate lam ω) + iterRdivNoiseLevel a d v lam) ^ γ)) :
    GenericEventComparisons P T h₀ ρ ξ CA CV Cb γ q n S E
      candidate D (iterRdivNoiseLevel a d v) := by
  refine ⟨hE, hprob, ?_⟩
  intro ω hω lam hlam hs
  refine ⟨henvelope ω hω lam hlam hs, (haccepted ω hω lam hlam hs).1, ?_⟩
  apply (haccepted ω hω lam hlam hs).2.trans
  apply mul_le_mul_of_nonneg_left _ hCV
  apply add_le_add _ le_rfl
  have hnum : a * d ^ 2 / lam ≤
      D ω (candidate lam ω) + iterRdivNoiseLevel a d v lam := by
    dsimp [iterRdivNoiseLevel, iterRdivScale]
    linarith only [hD ω hω lam hlam hs, sq_nonneg v]
  calc
    iterRdivStability a d lam = (a * d ^ 2 / lam) / lam := by
      unfold iterRdivStability iterRdivScale
      ring
    _ ≤ _ := div_le_div_of_nonneg_right hnum (hS hs).1.le

/-- If [the comparison and bias constants are positive, the interpolation exponent is
positive and at most one, and the bias exponent exceeds one](hyp:hParameters), then
[a positive constant ensures that the discrepancy principle accepts its selected penalty,
selects at least the oracle penalty, and bounds selected projected squared error by oracle
noise and selected strong squared error by oracle stability plus oracle noise raised to
the interpolation exponent, whenever the grid is valid, sample size and oracle penalty
are positive, the propagation coefficient is nonnegative, generic event comparisons and
oracle crossing hold, and discrepancy nonnegativity and the sharper strong-error bound
hold on the oracle segment](goal). -/
-- @node: iter_rdiv_selected_errors_of_comparisons
lemma iter_rdiv_selected_errors_of_comparisons (CA CV Cb γ q : ℝ)
    (hParameters : GenericDPParameters CA CV Cb γ q) :
    ∃ C > 0, ∀ {Ω H Q : Type*} [MeasurableSpace Ω]
      [NormedAddCommGroup H] [NormedAddCommGroup Q]
      [NormedSpace ℝ H] [NormedSpace ℝ Q]
      (P : Measure Ω) [IsProbabilityMeasure P] (T : H →L[ℝ] Q) (h₀ : H)
      (ρ ξ a d v : ℝ) (n : ℕ) (E : Set Ω) (lamo : ℝ)
      (candidate : ℝ → Ω → H) (D : Ω → H → ℝ),
      GridDomain ρ → 0 < n → 0 ≤ a → 0 < lamo →
      GenericEventComparisons P T h₀ ρ ξ CA CV Cb γ q n (Set.Icc lamo 2) E
        candidate D (iterRdivNoiseLevel a d v) →
      lamo ∈ regGrid ρ n → OracleCrossing (iterRdivNoiseLevel a d v) Cb q lamo →
      (∀ ω ∈ E, ∀ lam ∈ regGrid ρ n, lam ∈ Set.Icc lamo 2 →
        0 ≤ D ω (candidate lam ω) ∧
        ‖candidate lam ω - h₀‖ ^ 2 ≤ CV * (iterRdivStability a d lam +
          (D ω (candidate lam ω) + iterRdivNoiseLevel a d v lam) ^ γ)) →
      ∀ ω ∈ E,
        let lam := selectedPenalty ρ n (fun l => D ω (candidate l ω))
          (iterRdivNoiseLevel a d v)
        Accepts ρ n (fun l => D ω (candidate l ω)) (iterRdivNoiseLevel a d v) ∧
        lamo ≤ lam ∧
        ‖T (candidate lam ω - h₀)‖ ^ 2 ≤ C * iterRdivNoiseLevel a d v lamo ∧
        ‖candidate lam ω - h₀‖ ^ 2 ≤ C * (iterRdivStability a d lamo +
          iterRdivNoiseLevel a d v lamo ^ γ) := by
  obtain ⟨Cd, hCd, hdp⟩ := common_dp CA CV Cb γ q hParameters
  let C := Cd + CV * (1 + (5 / 2 : ℝ) ^ γ)
  have hCV : 0 < CV := hParameters.2.1
  have hγ : 0 < γ := hParameters.2.2.2.1.1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Ω H Q _ _ _ _ _ P _ T h₀ ρ ξ a d v n E lamo candidate D
    hρ hn ha hlam hcomp hgrid hcross hrefined ω hω
  have hρpos : 0 < ρ := by linarith only [hρ.1]
  have hnoise : NoiseLevelNonneg ρ n (iterRdivNoiseLevel a d v) := by
    intro l hl
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hl
    have hlpos : 0 < gridValue ρ k := mul_pos (by norm_num) (pow_pos hρpos k)
    exact add_nonneg
      (div_nonneg (mul_nonneg ha (sq_nonneg d)) hlpos.le) (sq_nonneg v)
  have hS : StabilityRegionSubset (Set.Icc lamo 2) :=
    fun _ h => ⟨hlam.trans_le h.1, h.2⟩
  have hmono : NoiseLevelAntitoneOnSegment ρ n (iterRdivNoiseLevel a d v) lamo := by
    intro x hx y hy hxy
    exact (iter_rdiv_scales_antitoneOn a d v ha).1
      (hlam.trans_le hx.2.1) (hlam.trans_le hy.2.1) hxy
  obtain ⟨haccept, _, hselected, hweak, _⟩ := hdp P T h₀ ρ ξ hρ n hn
    (Set.Icc lamo 2) E lamo candidate D (iterRdivNoiseLevel a d v)
    hnoise hS hcomp ⟨hgrid, fun _ h => h.2⟩ hmono hcross ω hω
  let f := fun l => D ω (candidate l ω)
  let A := iterRdivNoiseLevel a d v
  let lam := selectedPenalty ρ n f A
  have hidx : discrepancyIndex ρ n f A ≤ terminalIndex ρ n ∧
      f lam ≤ 3 / 2 * A lam := by
    have he : ∃ k, k ≤ terminalIndex ρ n ∧ f (gridValue ρ k) ≤
        3 / 2 * A (gridValue ρ k) := haccept
    simpa only [lam, selectedPenalty, discrepancyIndex, dif_pos he] using Nat.find_spec he
  have hselGrid : lam ∈ regGrid ρ n :=
    Finset.mem_image.mpr ⟨_, Finset.mem_range.mpr (Nat.lt_succ_of_le hidx.1), rfl⟩
  have hsel2 : lam ≤ 2 := by
    have hp := pow_le_pow_of_le_one hρpos.le hρ.2.le
      (Nat.zero_le (discrepancyIndex ρ n f A))
    simpa [lam, selectedPenalty, gridValue] using
      mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2)
  have hselS : lam ∈ Set.Icc lamo 2 := ⟨hselected, hsel2⟩
  have hAo : 0 ≤ A lamo := hnoise lamo hgrid
  have hAl : A lam ≤ A lamo := hmono ⟨hgrid, le_rfl, hsel2.trans' hselected⟩
    ⟨hselGrid, hselS⟩ hselected
  have hsum : f lam + A lam ≤ (5 / 2 : ℝ) * A lamo := by
    linarith only [hidx.2, hAl]
  have href := hrefined ω hω lam hselGrid hselS
  have hpow : (f lam + A lam) ^ γ ≤
      (5 / 2 : ℝ) ^ γ * A lamo ^ γ := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 5 / 2) hAo]
    exact Real.rpow_le_rpow (add_nonneg href.1 (hnoise lam hselGrid)) hsum hγ.le
  have hvar : iterRdivStability a d lam ≤ iterRdivStability a d lamo :=
    (iter_rdiv_scales_antitoneOn a d v ha).2 hlam (hlam.trans_le hselected) hselected
  have hV : 0 ≤ iterRdivStability a d lamo := by
    exact div_nonneg (mul_nonneg ha (sq_nonneg d)) (sq_nonneg lamo)
  have hpower : 0 ≤ A lamo ^ γ := Real.rpow_nonneg hAo _
  refine ⟨haccept, hselected, hweak.trans ?_, href.2.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (by positivity : 0 ≤ CV * (1 + (5 / 2 : ℝ) ^ γ))) hAo
  · have hb := mul_le_mul_of_nonneg_left (add_le_add hvar hpow) hCV.le
    have hp : 0 ≤ (5 / 2 : ℝ) ^ γ := by positivity
    dsimp only [C]
    nlinarith only [hb, mul_nonneg hCV.le hpower,
      mul_nonneg (mul_nonneg hCV.le hp) hV, mul_nonneg hCd.le (add_nonneg hV hpower)]

/-- Assume [a valid geometric grid ratio](hyp:hρ), [a positive oracle multiplier](hyp:hc),
[a positive source exponent](hyp:hβ), [at least one iteration](hyp:ht), [positive projected-error](hyp:hCA),
[strong-error](hyp:hCV), and [bias](hyp:hCb) comparison constants, and [a bias constant
times the oracle multiplier raised to one plus the qualification exponent at most one
half](hyp:hsmallFit) and [the same product with the qualification exponent at most one
half](hyp:hsmallCal). Then [a positive constant gives acceptance, selection above the
geometrically rounded oracle, a projected squared-error bound by the iterative error
scale, and a strong squared-error bound by the sum of the fitting scale raised to the
ratio of qualification exponent minus one to qualification exponent plus one and the
iterative error scale raised to beta divided by beta plus one, whenever the oracle is
rounded within one grid factor of its prescribed radius and the generic event and sharper
strong-error comparisons hold with positive sample size and fitting scale and nonnegative
propagation coefficient and calibration scale](goal). -/
-- @node: iter_rdiv_common_dp_oracle_rates
lemma iter_rdiv_common_dp_oracle_rates (CA CV Cb ρ c β : ℝ) (t : ℕ)
    (hρ : GridDomain ρ) (hc : 0 < c) (hβ : 0 < β) (ht : 1 ≤ t)
    (hCA : 0 < CA) (hCV : 0 < CV) (hCb : 0 < Cb)
    (hsmallFit : Cb * c ^ (qualificationExponent β t + 1) ≤ 1 / 2)
    (hsmallCal : Cb * c ^ qualificationExponent β t ≤ 1 / 2) :
    ∃ C > 0, ∀ {Ω H Q : Type*} [MeasurableSpace Ω]
      [NormedAddCommGroup H] [NormedAddCommGroup Q]
      [NormedSpace ℝ H] [NormedSpace ℝ Q]
      (P : Measure Ω) [IsProbabilityMeasure P] (T : H →L[ℝ] Q) (h₀ : H)
      (ξ a d v : ℝ) (n : ℕ) (E : Set Ω) (lamo : ℝ)
      (candidate : ℝ → Ω → H) (D : Ω → H → ℝ),
      0 < n → 0 ≤ a → 0 < a * d ^ 2 → 0 ≤ v →
      lamo ∈ regGrid ρ n → 0 < lamo →
      ρ * (c * max ((a * d ^ 2) ^ (1 / (qualificationExponent β t + 1)))
        (v ^ (2 / qualificationExponent β t))) ≤ lamo →
      lamo ≤ c * max ((a * d ^ 2) ^ (1 / (qualificationExponent β t + 1)))
        (v ^ (2 / qualificationExponent β t)) →
      GenericEventComparisons P T h₀ ρ ξ CA CV Cb (β / (β + 1))
        (qualificationExponent β t) n (Set.Icc lamo 2) E candidate D
        (iterRdivNoiseLevel a d v) →
      (∀ ω ∈ E, ∀ lam ∈ regGrid ρ n, lam ∈ Set.Icc lamo 2 →
        0 ≤ D ω (candidate lam ω) ∧
        ‖candidate lam ω - h₀‖ ^ 2 ≤ CV * (iterRdivStability a d lam +
          (D ω (candidate lam ω) + iterRdivNoiseLevel a d v lam) ^ (β / (β + 1)))) →
      ∀ ω ∈ E,
        let lam := selectedPenalty ρ n (fun l => D ω (candidate l ω))
          (iterRdivNoiseLevel a d v)
        Accepts ρ n (fun l => D ω (candidate l ω)) (iterRdivNoiseLevel a d v) ∧
        lamo ≤ lam ∧
        ‖T (candidate lam ω - h₀)‖ ^ 2 ≤ C * iterRdivErrorScale β a d v t ∧
        ‖candidate lam ω - h₀‖ ^ 2 ≤ C *
          ((a * d ^ 2) ^ ((qualificationExponent β t - 1) /
            (qualificationExponent β t + 1)) +
            iterRdivErrorScale β a d v t ^ (β / (β + 1))) := by
  have hq : 1 < qualificationExponent β t := by
    have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
    exact lt_min (by linarith only [hβ]) (by linarith only [htR])
  have hγ : 0 < β / (β + 1) := div_pos hβ (by linarith only [hβ])
  have hγ1 : β / (β + 1) ≤ 1 :=
    (div_le_one (by linarith only [hβ] : 0 < β + 1)).2 (by linarith)
  obtain ⟨C₀, hC₀, hselected⟩ := iter_rdiv_selected_errors_of_comparisons
    CA CV Cb (β / (β + 1)) (qualificationExponent β t)
    ⟨hCA, hCV, hCb, ⟨hγ, hγ1⟩, hq⟩
  let K := (ρ * c)⁻¹
  let N := K + 1
  let C := C₀ * (N + K ^ 2 + N ^ (β / (β + 1)))
  have hρpos : 0 < ρ := by linarith only [hρ.1]
  have hK : 0 < K := by dsimp [K]; positivity
  have hN : 0 < N := by dsimp [N]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Ω H Q _ _ _ _ _ P _ T h₀ ξ a d v n E lamo candidate D
    hn ha hs hv hgrid hlam hlower hupper hcomp hrefined ω hω
  have hrad : (Real.sqrt (a * d ^ 2)) ^ (2 / (qualificationExponent β t + 1)) =
      (a * d ^ 2) ^ (1 / (qualificationExponent β t + 1)) := by
    rw [show 2 / (qualificationExponent β t + 1) =
      2 * (1 / (qualificationExponent β t + 1)) by ring,
      iter_rdiv_sqrt_scale_power _ _ hs.le]
  have hcross := rdiv_oracle_bias_crossing Cb c (qualificationExponent β t)
    (Real.sqrt (a * d ^ 2)) v lamo hCb.le hc.le (by linarith only [hq])
    (Real.sqrt_nonneg _) hv hlam (by simpa only [hrad] using hupper)
    hsmallFit hsmallCal
  have hcross' : OracleCrossing (iterRdivNoiseLevel a d v) Cb
      (qualificationExponent β t) lamo := by
    simpa only [OracleCrossing, genericBias, rdivNoiseLevel,
      iterRdivNoiseLevel, iterRdivScale, Real.sq_sqrt hs.le] using hcross
  obtain ⟨haccept, hloc, hweak, hstrong⟩ := hselected P T h₀ ρ ξ a d v n E lamo
    candidate D hρ hn ha hlam hcomp hgrid hcross' hrefined ω hω
  have hrates := iter_rdiv_oracle_scalar_rates ρ c a (qualificationExponent β t)
    d v lamo hρpos hc hq hs hlower
  have hε : 0 ≤ iterRdivErrorScale β a d v t :=
    add_nonneg (Real.rpow_nonneg hs.le _) (sq_nonneg v)
  have hεγ : 0 ≤ iterRdivErrorScale β a d v t ^ (β / (β + 1)) := by positivity
  have hfit : 0 ≤ (a * d ^ 2) ^ ((qualificationExponent β t - 1) /
      (qualificationExponent β t + 1)) := Real.rpow_nonneg hs.le _
  have hpower : iterRdivNoiseLevel a d v lamo ^ (β / (β + 1)) ≤
      N ^ (β / (β + 1)) * iterRdivErrorScale β a d v t ^ (β / (β + 1)) := by
    rw [← Real.mul_rpow hN.le hε]
    exact Real.rpow_le_rpow (add_nonneg (div_nonneg hs.le hlam.le)
      (sq_nonneg v)) hrates.1 hγ.le
  have hNpow : 0 ≤ N ^ (β / (β + 1)) := by positivity
  have hcN : C₀ * N ≤ C := by
    dsimp [C]
    nlinarith only [mul_nonneg hC₀.le (add_nonneg (sq_nonneg K) hNpow)]
  have hcK : C₀ * K ^ 2 ≤ C := by
    dsimp [C]
    nlinarith only [mul_nonneg hC₀.le (add_nonneg hN.le hNpow)]
  have hcP : C₀ * N ^ (β / (β + 1)) ≤ C := by
    dsimp [C]
    nlinarith only [mul_nonneg hC₀.le (add_nonneg hN.le (sq_nonneg K))]
  refine ⟨haccept, hloc, hweak.trans ?_, hstrong.trans ?_⟩
  · calc
      C₀ * iterRdivNoiseLevel a d v lamo ≤
          C₀ * (N * iterRdivErrorScale β a d v t) :=
        mul_le_mul_of_nonneg_left hrates.1 hC₀.le
      _ = (C₀ * N) * iterRdivErrorScale β a d v t := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcN hε
  · have hb := mul_le_mul_of_nonneg_left (add_le_add hrates.2 hpower) hC₀.le
    nlinarith only [hb, mul_le_mul_of_nonneg_right hcK hfit,
      mul_le_mul_of_nonneg_right hcP hεγ]

end Papers.TsAdaptiveEstimationInference
