module
public import Papers.TsAdaptiveEstimationInference.Helpers.Selection
public import Papers.TsAdaptiveEstimationInference.Helpers.TRAE
public import Papers.TsAdaptiveEstimationInference.Helpers.TRAEUniformCalibration
public import Papers.TsAdaptiveEstimationInference.TCommonDp
public import Papers.TsAdaptiveEstimationInference.Helpers.TikhonovOracle
/-! Accuracy-independent deterministic TRAE comparisons and rates. -/
public section
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option maxHeartbeats 600000
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter
open scoped Topology
variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]
  (V : IVWorld 𝒲 𝒳 𝒵) (P : Measure Ω) [IsProbabilityMeasure P]
  (sample : AnalysisSample V P) (split : SampleSplit)

/-- Assume [a grid ratio at least one half and less than one](hyp:hρ), [the
range condition](hyp:hRange), [the source condition with exponent β and source
element w₀](hyp:hSource), [admissibility of the minimum-norm solution](hyp:hRealizable),
[closure of projected residuals in the critic class](hyp:hClose), [attainment
of the candidate minima](hyp:hMinima), and [a positive event comparison
constant](hyp:hCevent). Then [there is a positive constant chosen before the
accuracy curves such that, for any deterministically calibrated curves and
any measurable event of probability at least one minus its failure budget
supporting the TRAE comparisons at a positive sample size, each grid candidate
on that event satisfies two bounds: its empirical loss plus half the
regularization parameter times squared estimation error is bounded by the
constant times the sum of accuracy squared and source norm squared times the
parameter to the bias exponent; its squared estimation error is bounded by
the constant times the sum of accuracy squared divided by the parameter and
the interpolation power of the sum of empirical loss and accuracy squared](goal). -/
-- @node: trae_strong_from_comparisons_uniform
lemma trae_strong_from_comparisons_uniform
    (ρ β : ℝ) (w₀ : V.Hbar.toSubmodule)
    (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hRange : RangeCondition V) (hSource : BetaSourceCondition V β w₀)
    (hRealizable : H0MemHypothesisClass V) (hClose : ClosenessCondition V)
    (hMinima : TRAEMinimaAttained V P sample split ρ candidate)
    (Cevent : ℝ) (hCevent : 0 < Cevent) :
      ∃ C > 0, ∀ (δ ν : ℕ → ℝ), CalibrationDeterministic δ ν → ∀ ξ : ℝ, ∀ n : ℕ, 0 < n →
      ∀ E : Set Ω, MeasurableSet E → 1 - ξ ≤ P.real E →
      TRAEComparisonsOn V P sample split δ n E Cevent → ∀ ω ∈ E,
      ∀ lam ∈ regGrid ρ n,
        traeEmpiricalLoss V P sample split n ω (candidate n lam ω) + lam / 2 * ‖candidate n lam ω - minNormSolution V‖ ^ 2 ≤
          C * (δ n ^ 2 + ‖w₀‖ ^ 2 * lam ^ biasExponent β) ∧
        ‖candidate n lam ω - minNormSolution V‖ ^ 2 ≤ C * (δ n ^ 2 / lam +
          (traeEmpiricalLoss V P sample split n ω (candidate n lam ω) + δ n ^ 2) ^ interpolationExponent β) := by
  obtain ⟨Cs, hCs, hs⟩ := (variational_source V β w₀ hSource).2
    (1 / 16) (by norm_num)
  let A := 3 * Cevent + 4 * Cevent ^ 2
  let D := 2 + 2 * Cevent
  let α := interpolationExponent β
  let K := Cs * ‖w₀‖ ^ (2 / (1 + truncatedSource β))
  let C := 2 * (A + Cevent + Cs) + 2 * A + 2 * K * D ^ α + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hb : 0 < truncatedSource β := lt_min hSource.1 zero_lt_one
  have hα : 0 < α := by
    dsimp [α, interpolationExponent]
    positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro δ ν hDeterministic ξ n hn E hE hprob hComparisons ω hω lam hlam
  have hl : lam ∈ Set.Ioc (0 : ℝ) 2 := by
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hlam
    dsimp [gridValue]
    constructor
    · exact mul_pos (by norm_num) (pow_pos (by linarith [hρ.1]) _)
    · have hp : ρ ^ k ≤ 1 := pow_le_one₀ (by linarith [hρ.1]) hρ.2.le
      linarith
  have hl0 : 0 < lam := hl.1
  obtain ⟨hh, hOpt⟩ := (hMinima n hn lam hlam).1 ω
  let h := candidate n lam ω
  let u := h - minNormSolution V
  let L := traeEmpiricalLoss V P sample split n ω h
  have hL : 0 ≤ L := traeEmpiricalLoss_nonneg V P sample split hRealizable hClose n ω h ((hComparisons ω hω).2.2.2)
  have hbase := trae_empirical_optimality V P sample split hRealizable hCevent
    (hDeterministic.1 n) hl hComparisons hω hh (hOpt _ hRealizable)
  change L + lam * (‖u‖ ^ 2 + 2 * inner ℝ (minNormSolution V) u) ≤
    A * δ n ^ 2 + lam / 8 * ‖u‖ ^ 2 at hbase
  have hw : ‖projCondExpOp V u‖ ^ 2 ≤ 2 * L + 2 * Cevent * δ n ^ 2 := by
    have hc := ((hComparisons ω hω).1 h hh).1
    rw [traePopulationLoss_eq V hRange hClose h hh] at hc
    change (1 / 2 : ℝ) * ‖projCondExpOp V u‖ ^ 2 - Cevent * δ n ^ 2 ≤ L at hc
    linarith
  have hinner : -|inner ℝ (minNormSolution V) u| ≤ inner ℝ (minNormSolution V) u :=
    neg_abs_le _
  have hneg := mul_le_mul_of_nonneg_left hinner (by positivity : 0 ≤ 2 * lam)
  have henergy := (hs u).1 lam hl
  have hfirst : L + lam / 2 * ‖u‖ ^ 2 ≤
      2 * (A + Cevent + Cs) * (δ n ^ 2 + ‖w₀‖ ^ 2 * lam ^ biasExponent β) := by
    have hbias : 0 ≤ ‖w₀‖ ^ 2 * lam ^ biasExponent β := by positivity
    have ht : 0 ≤ lam * ‖u‖ ^ 2 := by positivity
    have hcross : 0 ≤ (A + Cevent) * (‖w₀‖ ^ 2 * lam ^ biasExponent β) := by positivity
    have hnoise : 0 ≤ Cs * δ n ^ 2 := by positivity
    nlinarith
  have hKD : 0 ≤ K * D ^ α := by positivity
  have hCfirst : 2 * (A + Cevent + Cs) ≤ C := by
    dsimp [C]
    linarith
  constructor
  · exact hfirst.trans (mul_le_mul_of_nonneg_right hCfirst (by positivity))
  · have hsecond := (hs u).2
    have hnorm : (13 / 16 : ℝ) * ‖u‖ ^ 2 ≤
        A * δ n ^ 2 / lam + K * ‖projCondExpOp V u‖ ^
          (2 * truncatedSource β / (1 + truncatedSource β)) := by
      apply (mul_le_mul_iff_right₀ hl0).mp
      rw [mul_add, mul_div_cancel₀ _ (ne_of_gt hl0)]
      change lam * ((13 / 16 : ℝ) * ‖u‖ ^ 2) ≤ A * δ n ^ 2 +
        lam * (Cs * ‖w₀‖ ^ (2 / (1 + truncatedSource β)) *
          ‖projCondExpOp V u‖ ^ (2 * truncatedSource β / (1 + truncatedSource β)))
      have hpos := mul_le_mul_of_nonneg_left hsecond hl.1.le
      nlinarith only [hbase, hpos, hneg, hL]
    have hwD : ‖projCondExpOp V u‖ ^ 2 ≤ D * (L + δ n ^ 2) := by
      calc
        _ ≤ 2 * L + 2 * Cevent * δ n ^ 2 := hw
        _ ≤ _ := by
          dsimp [D]
          nlinarith only [mul_nonneg hCevent.le hL, sq_nonneg (δ n)]
    have hpow : ‖projCondExpOp V u‖ ^ (2 * truncatedSource β / (1 + truncatedSource β)) ≤
        D ^ α * (L + δ n ^ 2) ^ α := by
      calc
        _ = (‖projCondExpOp V u‖ ^ 2) ^ α := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
          congr 1
          dsimp [α, interpolationExponent]
          ring
        _ ≤ (D * (L + δ n ^ 2)) ^ α :=
          Real.rpow_le_rpow (sq_nonneg _) hwD hα.le
        _ = _ := Real.mul_rpow hD.le (by positivity)
    have hkpow := mul_le_mul_of_nonneg_left hpow hK
    have hx : 0 ≤ δ n ^ 2 / lam := by positivity
    have hp : 0 ≤ (L + δ n ^ 2) ^ α := by positivity
    have hcA : 2 * A ≤ C := by dsimp [C]; linarith
    have hcK : 2 * K * D ^ α ≤ C := by dsimp [C]; linarith
    have hca := mul_le_mul_of_nonneg_right hcA hx
    have hck := mul_le_mul_of_nonneg_right hcK hp
    change ‖u‖ ^ 2 ≤ C * (δ n ^ 2 / lam + (L + δ n ^ 2) ^ α)
    have hh2 : ‖u‖ ^ 2 ≤ 2 * (A * (δ n ^ 2 / lam) +
        K * D ^ α * (L + δ n ^ 2) ^ α) := by
      rw [mul_div_assoc] at hnorm
      nlinarith only [hnorm, hkpow, sq_nonneg ‖u‖]
    nlinarith only [hh2, hca, hck]

/-- Assume [a grid ratio at least one half and less than one](hyp:hρ), [the
range condition](hyp:hRange), [the source condition with exponent β and source
element w₀](hyp:hSource), [admissibility of the minimum-norm solution](hyp:hRealizable),
[closure of projected residuals in the critic class](hyp:hClose), [TRAE
boundedness and process measurability](hyp:hBound), [common-null-set bounds](hyp:hCommon),
[attainment of the candidate minima](hyp:hMinima), and [a positive event
comparison constant](hyp:hCe). Then [a positive constant chosen before the
accuracy curves bounds the discrepancy-selected candidate's squared projected
error by accuracy squared and its squared estimation error by accuracy to the
power twice the truncated source exponent divided by one plus that exponent,
each multiplied by the constant, on any measurable event supporting both the
TRAE comparisons and discrepancy envelope, whenever deterministic calibration,
the inverse-sample-size floor for accuracy squared, and the minimum sample-size
requirement hold](goal). -/
-- @node: trae_selected_rate_uniform
lemma trae_selected_rate_uniform
    (ρ B β : ℝ) (w₀ : V.Hbar.toSubmodule)
    (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hRange : RangeCondition V) (hSource : BetaSourceCondition V β w₀)
    (hRealizable : H0MemHypothesisClass V) (hClose : ClosenessCondition V)
    (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B)
    (hMinima : TRAEMinimaAttained V P sample split ρ candidate)
    (Ce : ℝ) (hCe : 0 < Ce) :
    ∃ C > 0, ∀ (δ ν : ℕ → ℝ), CalibrationDeterministic δ ν →
      (∀ n : ℕ, 0 < n → 1 / (n : ℝ) ≤ δ n ^ 2) → ∀ n : ℕ, traeMinSampleSize B ≤ n →
      ∀ E : Set Ω, MeasurableSet E →
      TRAEComparisonsOn V P sample split δ n E Ce →
      TRAEDiscrepancyEnvelope V P sample split ρ β δ w₀ candidate n E Ce →
      ∀ ω ∈ E,
        ‖projCondExpOp V (candidate n (traeSelected V P sample split ρ δ candidate n ω) ω -
          minNormSolution V)‖ ^ 2 ≤ C * δ n ^ 2 ∧
        ‖candidate n (traeSelected V P sample split ρ δ candidate n ω) ω -
          minNormSolution V‖ ^ 2 ≤
            C * δ n ^ (2 * truncatedSource β / (1 + truncatedSource β)) := by
  classical
  obtain ⟨Cs, hCs, hstrong⟩ := trae_strong_from_comparisons_uniform
    V P sample split ρ β w₀ candidate
    hρ hRange hSource hRealizable hClose hMinima Ce hCe
  let p := biasExponent β
  let α := interpolationExponent β
  have hp : 1 < p := lt_min (by linarith [hSource.1]) (by norm_num)
  have hp2 : p ≤ 2 := min_le_right _ _
  have hb : 0 < truncatedSource β := lt_min hSource.1 zero_lt_one
  have hpb : p = 1 + truncatedSource β := by
    dsimp [p, biasExponent, truncatedSource]
    rcases le_total β 1 with h | h
    · rw [min_eq_left h, min_eq_left (by linarith)]; ring
    · rw [min_eq_right h, min_eq_right (by linarith)]; ring
  have hα : 0 < α := div_pos hb (by linarith)
  have hα1 : α ≤ 1 := (div_le_one (by linarith : 0 < 1 + truncatedSource β)).2 (by linarith)
  have hexp : 2 * (p - 1) / p = 2 * α := by
    dsimp [α, interpolationExponent]
    rw [hpb]; ring
  let CA := 2 + 2 * Ce
  let Cb := Ce * ‖w₀‖ ^ 2 + 1
  let CV := Cs + 1
  have hCA : 0 < CA := by dsimp [CA]; positivity
  have hCb : 0 < Cb := by dsimp [Cb]; positivity
  have hCV : 0 < CV := by dsimp [CV]; positivity
  have hCsCV : Cs ≤ CV := by dsimp [CV]; linarith
  have halpha : 2 * truncatedSource β / (1 + truncatedSource β) = 2 * α := by
    dsimp [α, interpolationExponent]; ring
  obtain ⟨Cd, hCd, hdp⟩ := common_dp CA CV Cb α p ⟨hCA, hCV, hCb, ⟨hα, hα1⟩, hp⟩
  let c := 1 / (2 * (Cb + 1))
  have hc : 0 < c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := (div_le_one (by positivity : 0 < 2 * (Cb + 1))).2 (by linarith)
  have hcb : Cb * c ^ p ≤ 1 / 2 := by
    have hpow := Real.rpow_le_self_of_le_one hc.le hc1 hp.le
    have hmul : Cb * c ≤ 1 / 2 := by
      dsimp [c]
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      field_simp
      linarith
    exact (mul_le_mul_of_nonneg_left hpow hCb.le).trans hmul
  let K := (ρ * c)⁻¹ + 1
  have hρpos : 0 < ρ := by linarith [hρ.1]
  have hK : 0 < K := by dsimp [K]; positivity
  let C := Cd * (K + 1) + 4 * B ^ 2 / c ^ 2 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro δ ν hDeterministic hFloor n hn E hE hcomp henv ω hω
  have hn0 : 0 < n := by have := (le_max_left _ _).trans hn; omega
  have hprob : 1 - (1 : ℝ) ≤ P.real E := by simp
  rw [halpha]
  have hfloor := hFloor n hn0
  have hd : 0 < δ n := by
    have hd0 := hDeterministic.1 n
    have hi : 0 < 1 / (n : ℝ) := by positivity
    nlinarith
  have hgrid : ∀ lam ∈ regGrid ρ n, lam ∈ Set.Ioc (0 : ℝ) 2 :=
    fun lam hlam => trae_grid_domain ρ hρ n lam hlam
  have hcmp : GenericEventComparisons P (projCondExpOp V) (minNormSolution V)
      ρ 1 CA CV Cb α p n (Set.Ioc 0 2) E (candidate n)
      (fun ω h => traeEmpiricalLoss V P sample split n ω h) (traeNoiseLevel (δ n)) := by
    refine ⟨hE, hprob, ?_⟩
    intro ω' hω' lam hlam hstable
    have hh := ((hMinima n hn0 lam hlam).1 ω').1
    have hL := traeEmpiricalLoss_nonneg V P sample split hRealizable hClose n ω' (candidate n lam ω') ((hcomp ω' hω').2.2.2)
    have hw := ((hcomp ω' hω').1 _ hh).1
    rw [traePopulationLoss_eq V hRange hClose _ hh] at hw
    have hs := (hstrong δ ν hDeterministic 1 n hn0 E hE hprob hcomp ω' hω' lam hlam).2
    refine ⟨?_, ?_, ?_⟩
    · have he := (henv.2 ω' hω').2 lam hlam
      change _ ≤ δ n ^ 2 + Cb * lam ^ p
      have hb' : Ce * ‖w₀‖ ^ 2 ≤ Cb := by dsimp [Cb]; linarith
      exact he.trans (add_le_add_right
        (mul_le_mul_of_nonneg_right hb' (Real.rpow_nonneg hstable.1.le p)) _)
    · change _ ≤ CA * (_ + δ n ^ 2)
      change (1 / 2 : ℝ) * ‖(projCondExpOp V
        (candidate n lam ω' - minNormSolution V) : Lp ℝ 2 V.law)‖ ^ 2 -
        Ce * δ n ^ 2 ≤ _ at hw
      dsimp [CA]
      nlinarith only [hw, hL, mul_nonneg hCe.le hL, sq_nonneg (δ n)]
    · have hdiv : δ n ^ 2 / lam ≤
          (traeEmpiricalLoss V P sample split n ω' (candidate n lam ω') + δ n ^ 2) / lam :=
        div_le_div_of_nonneg_right (by linarith) hstable.1.le
      have hpow : 0 ≤ (traeEmpiricalLoss V P sample split n ω' (candidate n lam ω') +
          δ n ^ 2) ^ α := Real.rpow_nonneg (add_nonneg hL (sq_nonneg _)) _
      have hnonneg : 0 ≤ (traeEmpiricalLoss V P sample split n ω' (candidate n lam ω') +
          δ n ^ 2) / lam +
          (traeEmpiricalLoss V P sample split n ω' (candidate n lam ω') + δ n ^ 2) ^ α :=
        add_nonneg (div_nonneg (add_nonneg hL (sq_nonneg _)) hstable.1.le) hpow
      exact hs.trans ((mul_le_mul_of_nonneg_left (add_le_add_left hdiv _) hCs.le).trans
        (mul_le_mul_of_nonneg_right hCsCV hnonneg))
  by_cases hsmall : δ n ≤ c
  · obtain ⟨hoGrid, hoLow, hoHigh⟩ := trae_small_noise_oracle ρ c p (δ n) n
      hρ hc hc1 hp hp2 hd hsmall hn0 hfloor
    let lo := oraclePoint ρ n (c * δ n ^ (2 / p))
    have hlo : 0 < lo := (hgrid lo hoGrid).1
    have hcross : OracleCrossing (traeNoiseLevel (δ n)) Cb p lo :=
      trae_oracle_bias_crossing Cb c p (δ n) lo hCb.le hc.le (by linarith) hd.le
        hlo.le hoHigh hcb
    have hsegment : OracleSegmentStable ρ n (Set.Ioc 0 2) lo :=
      ⟨hoGrid, fun _ h => hgrid _ h.1⟩
    have hresult := hdp P (projCondExpOp V) (minNormSolution V) ρ 1 hρ n hn0
      (Set.Ioc 0 2) E lo (candidate n)
      (fun ω h => traeEmpiricalLoss V P sample split n ω h) (traeNoiseLevel (δ n))
      (fun _ _ => sq_nonneg _) (fun _ h => h) hcmp hsegment
      (fun _ _ _ _ _ => le_rfl) hcross ω hω
    have hv := trae_oracle_variance_rate ρ c p (δ n) lo hρpos hc (by linarith) hd hoLow
    rw [hexp] at hv
    have heq : (δ n ^ 2) ^ α = δ n ^ (2 * α) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hd.le]
      norm_num
    have hrate : δ n ^ 2 / lo + (δ n ^ 2) ^ α ≤ K * δ n ^ (2 * α) := by
      rw [heq]
      dsimp [K]
      linarith
    have hCdC : Cd ≤ C := by dsimp [C]; nlinarith [div_nonneg (by positivity : 0 ≤ 4 * B ^ 2) (sq_nonneg c)]
    have hCK : Cd * K ≤ C := by
      dsimp [C]
      nlinarith [div_nonneg (by positivity : 0 ≤ 4 * B ^ 2) (sq_nonneg c)]
    constructor
    · exact hresult.2.2.2.1.trans (mul_le_mul_of_nonneg_right hCdC (sq_nonneg _))
    · exact hresult.2.2.2.2.trans ((mul_le_mul_of_nonneg_left hrate hCd.le).trans
        (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hCK (by positivity)))
  · have hsel : traeSelected V P sample split ρ δ candidate n ω ∈ regGrid ρ n := by
      have hi : discrepancyIndex ρ n
          (fun lam => traeEmpiricalLoss V P sample split n ω (candidate n lam ω))
          (traeNoiseLevel (δ n)) ≤ terminalIndex ρ n := by
        unfold discrepancyIndex
        split
        next he => exact (Nat.find_spec he).1
        next => exact le_rfl
      exact Finset.mem_image.mpr ⟨_, Finset.mem_range.mpr (Nat.lt_succ_of_le hi), rfl⟩
    have hh := ((hMinima n hn0 _ hsel).1 ω).1
    have hhB := trae_hypothesis_norm_le V B hBound _ hh
    have hh0B := trae_hypothesis_norm_le V B hBound _ hRealizable
    have herr : ‖candidate n (traeSelected V P sample split ρ δ candidate n ω) ω - minNormSolution V‖ ^ 2 ≤ 4 * B ^ 2 := by
      have ht := norm_sub_le (candidate n (traeSelected V P sample split ρ δ candidate n ω) ω) (minNormSolution V)
      calc
        _ ≤ (B + B) ^ 2 := pow_le_pow_left₀ (norm_nonneg _)
          (ht.trans (add_le_add hhB hh0B)) 2
        _ = 4 * B ^ 2 := by ring
    have hweak : ‖projCondExpOp V (candidate n (traeSelected V P sample split ρ δ candidate n ω) ω - minNormSolution V)‖ ^ 2 ≤ 4 * B ^ 2 := by
      have ht := (projCondExpOp V).le_opNorm (candidate n (traeSelected V P sample split ρ δ candidate n ω) ω - minNormSolution V)
      have hcT := mul_le_mul_of_nonneg_right (projCondExpOp_norm_le_one V)
        (norm_nonneg (candidate n (traeSelected V P sample split ρ δ candidate n ω) ω - minNormSolution V))
      have hcontract : ‖projCondExpOp V
          (candidate n (traeSelected V P sample split ρ δ candidate n ω) ω - minNormSolution V)‖ ≤
          ‖candidate n (traeSelected V P sample split ρ δ candidate n ω) ω - minNormSolution V‖ := by
        simpa using ht.trans hcT
      exact (pow_le_pow_left₀ (norm_nonneg _) hcontract 2).trans herr
    have hlarge := trae_large_noise_floor c (δ n) (2 * α) hc hc1 (le_of_not_ge hsmall) (by positivity) (by linarith)
    have hBC : 4 * B ^ 2 / c ^ 2 ≤ C := by
      dsimp [C]
      linarith only [mul_nonneg hCd.le hK.le, hCd.le]
    have hbound (x : ℝ) (hx : c ^ 2 ≤ x) : 4 * B ^ 2 ≤ C * x := by
      calc
        4 * B ^ 2 = (4 * B ^ 2 / c ^ 2) * c ^ 2 := by field_simp
        _ ≤ (4 * B ^ 2 / c ^ 2) * x := mul_le_mul_of_nonneg_left hx (by positivity)
        _ ≤ C * x := mul_le_mul_of_nonneg_right hBC ((sq_nonneg c).trans hx)
    exact ⟨hweak.trans (hbound _ hlarge.1), herr.trans (hbound _ hlarge.2)⟩

/-- For [a grid ratio at least one half and less than one](hyp:hρ), [there is
a positive calibration threshold for each positive event constant, chosen
before the source, such that under the range, source, realizability, closeness,
boundedness, common-null-set, and attained-minima conditions a positive rate
constant can be chosen before the event constant and all accuracy curves:
calibrated inflation of nonnegative base accuracy, deterministic calibration,
and the inverse-sample-size floor imply that, at every sufficiently large
sample size, base TRAE comparisons on a measurable event bound the
discrepancy-selected candidate's squared projected error by the rate constant
times accuracy squared and its squared estimation error by that constant times
accuracy to the power twice the truncated source exponent divided by one plus
that exponent, throughout the same event](goal). -/
-- @node: trae_rate_of_calibrated_comparisons_uniform
lemma trae_rate_of_calibrated_comparisons_uniform
    (ρ B : ℝ) (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) :
    ∃ required : ℝ → ℝ, (∀ Ce > 0, 0 < required Ce) ∧
      ∀ (β : ℝ) (w₀ : V.Hbar.toSubmodule),
      RangeCondition V → BetaSourceCondition V β w₀ →
      H0MemHypothesisClass V → ClosenessCondition V → TRAEBoundedness V B → TRAECommonNullSetBoundedness V B →
      TRAEMinimaAttained V P sample split ρ candidate →
      ∃ C > 0, ∀ Ce > 0, ∀ (baseδ baseν δ ν : ℕ → ℝ) (κδ κν : ℝ),
      (∀ n : ℕ, 0 < n → 0 ≤ baseδ n) →
      CalibratedValidBounds δ ν baseδ baseν κδ κν (required Ce) →
      CalibrationDeterministic δ ν →
      (∀ n : ℕ, 0 < n → 1 / (n : ℝ) ≤ δ n ^ 2) →
      ∀ n : ℕ, traeMinSampleSize B ≤ n → ∀ E : Set Ω, MeasurableSet E →
      TRAEComparisonsOn V P sample split baseδ n E Ce →
      ∀ ω ∈ E,
        ‖projCondExpOp V (candidate n
          (traeSelected V P sample split ρ δ candidate n ω) ω - minNormSolution V)‖ ^ 2 ≤
          C * δ n ^ 2 ∧
        ‖candidate n (traeSelected V P sample split ρ δ candidate n ω) ω -
          minNormSolution V‖ ^ 2 ≤
          C * δ n ^ (2 * truncatedSource β / (1 + truncatedSource β)) := by
  obtain ⟨required, hrequired, hcalibrate⟩ := trae_discrepancy_uniform
    V P sample split ρ candidate hρ
  refine ⟨required, hrequired, ?_⟩
  intro β w₀ hRange hSource hRealizable hClose hBound hCommon hMinima
  obtain ⟨Cd, hCd, hcompare⟩ := hcalibrate β w₀ hRange hSource hRealizable hClose hMinima
  obtain ⟨C, hC, hrate⟩ := trae_selected_rate_uniform V P sample split
    ρ B β w₀ candidate hρ hRange hSource hRealizable hClose hBound hCommon hMinima Cd hCd
  refine ⟨C, hC, ?_⟩
  intro Ce hCe baseδ baseν δ ν κδ κν hBase hInflation hDeterministic hFloor n hn E hE hcomp
  have hn0 : 0 < n := by have := (le_max_left _ _).trans hn; omega
  obtain ⟨hcomp', henv⟩ := hcompare Ce hCe baseδ baseν δ ν κδ κν
    hBase hInflation hDeterministic n hn0 E hcomp
  exact hrate δ ν hDeterministic hFloor n hn E hE hcomp' henv

end Papers.TsAdaptiveEstimationInference
