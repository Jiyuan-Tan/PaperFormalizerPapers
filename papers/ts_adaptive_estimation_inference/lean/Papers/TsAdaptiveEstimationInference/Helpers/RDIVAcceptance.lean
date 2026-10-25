module
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVDensityBounds
/-! Deterministic terminal and initial tests for the RDIV discrepancy search.

The projected-statistic bound is derived from conditional density normalization
and the hypothesis envelope on the common support.
-/
public section
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory

/-- If [the grid ratio is at least one half and less than one](hyp:hρ) and
[the sample size is positive](hyp:hn), [the terminal grid index is positive](goal). -/
-- @node: rdiv_terminalIndex_pos
lemma rdiv_terminalIndex_pos (ρ : ℝ) (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1)
    (n : ℕ) (hn : 0 < n) : 0 < terminalIndex ρ n := by
  have hr : 0 < ρ := by linarith [hρ.1]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have harg : 1 < 2 * (n : ℝ) ^ 2 := by nlinarith
  have hlog : 0 < Real.log (1 / ρ) :=
    Real.log_pos ((lt_div_iff₀ hr).2 (by simpa using hρ.2))
  have hc := Nat.le_ceil (Real.log (2 * (n : ℝ) ^ 2) / Real.log (1 / ρ))
  have hp : 0 < Real.log (2 * (n : ℝ) ^ 2) / Real.log (1 / ρ) :=
    div_pos (Real.log_pos harg) hlog
  change _ ≤ (terminalIndex ρ n : ℝ) at hc
  exact_mod_cast (lt_of_lt_of_le hp hc)

/-- If [the grid ratio is at least one half and less than one](hyp:hρ),
[the failure probability lies strictly between zero and one](hyp:hξ), and
[the sample size is positive](hyp:hn), [the squared public logarithmic scale
is at least the natural logarithm of two divided by the sample size](goal). -/
-- @node: rdiv_public_log_square_floor
lemma rdiv_public_log_square_floor (ρ ξ : ℝ)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (n : ℕ) (hn : 0 < n) :
    Real.log 2 / n ≤ rdivPublicLogScale ρ ξ n ^ 2 := by
  have hk : (2 : ℝ) ≤ (terminalIndex ρ n + 1 : ℕ) := by
    exact_mod_cast (show 2 ≤ terminalIndex ρ n + 1 by
      have := rdiv_terminalIndex_pos ρ hρ n hn
      omega)
  have hratio : (2 : ℝ) ≤ (terminalIndex ρ n + 1 : ℕ) / ξ := by
    apply (le_div_iff₀ hξ.1).2
    linarith [hξ.2]
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hratio
  have hl0 : 0 ≤ Real.log ((terminalIndex ρ n + 1 : ℕ) / ξ) :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le.trans hl
  simp only [Nat.cast_add, Nat.cast_one] at hl hl0
  unfold rdivPublicLogScale
  rw [Real.sq_sqrt (div_nonneg hl0 (Nat.cast_nonneg n))]
  exact div_le_div_of_nonneg_right hl (Nat.cast_nonneg n)

/-- If [the grid ratio is at least one half and less than one](hyp:hρ),
[the failure probability lies strictly between zero and one](hyp:hξ),
[the sample size is positive](hyp:hn), and [δ dominates the public logarithmic
scale](hyp:hfloor), [the terminal noise level is at least the sample size
times the natural logarithm of two](goal). -/
-- @node: rdiv_terminal_noise_floor
lemma rdiv_terminal_noise_floor (ρ ξ δ ν : ℝ)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (n : ℕ) (hn : 0 < n) (hfloor : rdivPublicLogScale ρ ξ n ≤ δ) :
    (n : ℝ) * Real.log 2 ≤ rdivNoiseLevel δ ν (gridValue ρ (terminalIndex ρ n)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hl : 0 < gridValue ρ (terminalIndex ρ n) :=
    mul_pos (by norm_num) (pow_pos (by linarith [hρ.1]) _)
  have hd : Real.log 2 / n ≤ δ ^ 2 :=
    (rdiv_public_log_square_floor ρ ξ hρ hξ n hn).trans
      (pow_le_pow_left₀ (Real.sqrt_nonneg _) hfloor 2)
  have hd' : Real.log 2 ≤ δ ^ 2 * n := (div_le_iff₀ hn').1 hd
  have ht := terminalGrid_le ρ hρ n hn
  have ht' := (le_div_iff₀ (sq_pos_of_pos hn')).1 ht
  have hnl : 0 ≤ (n : ℝ) * Real.log 2 := by positivity
  have hprod := mul_le_mul_of_nonneg_left ht' hnl
  have hgoal : (n : ℝ) * Real.log 2 * gridValue ρ (terminalIndex ρ n) ≤ δ ^ 2 := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hn')).mp
    calc
      _ ≤ (n : ℝ) * Real.log 2 := by nlinarith only [hprod]
      _ ≤ (n : ℝ) ^ 2 * δ ^ 2 := by
        nlinarith only [mul_le_mul_of_nonneg_right hd' hn'.le]
  have hdiv := (le_div_iff₀ hl).2 hgoal
  unfold rdivNoiseLevel
  linarith only [hdiv, sq_nonneg ν]

/-- If [the grid ratio is at least one half and less than one](hyp:hρ),
[the failure probability lies strictly between zero and one](hyp:hξ),
[the sample size meets the minimum required for envelope B](hyp:hn), and
[δ dominates the public logarithmic scale](hyp:hfloor), [four times B squared
is at most three halves of the terminal noise level](goal). -/
-- @node: rdiv_terminal_threshold_bound
lemma rdiv_terminal_threshold_bound (ρ ξ B δ ν : ℝ)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (n : ℕ) (hn : rdivMinSampleSize B ≤ n)
    (hfloor : rdivPublicLogScale ρ ξ n ≤ δ) :
    4 * B ^ 2 ≤ 3 / 2 * rdivNoiseLevel δ ν (gridValue ρ (terminalIndex ρ n)) := by
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hn0 : 0 < n := by omega
  have hceil : ⌈8 * B ^ 2 / (3 * Real.log 2)⌉₊ ≤ n :=
    (le_max_right _ _).trans hn
  have hsize : 8 * B ^ 2 / (3 * Real.log 2) ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs := (div_le_iff₀ (by positivity : 0 < 3 * Real.log 2)).1 hsize
  have hf := rdiv_terminal_noise_floor ρ ξ δ ν hρ hξ n hn0 hfloor
  linarith only [hs, hf]

/-- If [the discrepancy at penalty two is at most its noise level](hyp:hD),
[the discrepancy search selects index zero](goal). -/
-- @node: rdiv_initial_index_zero
lemma rdiv_initial_index_zero (ρ δ ν : ℝ) (n : ℕ) (D : ℝ → ℝ)
    (hD : D 2 ≤ rdivNoiseLevel δ ν 2) :
    discrepancyIndex ρ n D (rdivNoiseLevel δ ν) = 0 := by
  have hnoise : 0 ≤ rdivNoiseLevel δ ν 2 := by
    unfold rdivNoiseLevel
    positivity
  have hinit : D (gridValue ρ 0) ≤ 3 / 2 * rdivNoiseLevel δ ν (gridValue ρ 0) := by
    simpa only [gridValue, pow_zero, mul_one] using
      (show D 2 ≤ 3 / 2 * rdivNoiseLevel δ ν 2 by linarith only [hD, hnoise])
  have he : ∃ k ≤ terminalIndex ρ n,
      D (gridValue ρ k) ≤ 3 / 2 * rdivNoiseLevel δ ν (gridValue ρ k) :=
    ⟨0, Nat.zero_le _, hinit⟩
  unfold discrepancyIndex
  rw [dif_pos he]
  exact Nat.le_zero.mp (Nat.find_min' he ⟨Nat.zero_le _, hinit⟩)

variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]
  (V : IVWorld 𝒲 𝒳 𝒵) (P : Measure Ω)
  (sample : AnalysisSample V P) (split : SampleSplit)

/-- If [the failure probability lies strictly between zero and one](hyp:hξ),
[the density critical radii are valid](hyp:hG), [the hypothesis critical radii
are valid](hyp:hH), [the base scales satisfy public scale calibration](hyp:hscale),
[the final scales are valid calibrated inflations of the base scales](hyp:hinflate),
and [the sample size is positive](hyp:hn), [the final δ scale dominates the
public logarithmic scale](goal). -/
-- @node: rdiv_calibrated_public_log_floor
lemma rdiv_calibrated_public_log_floor (mu : Measure 𝒳)
    (G : Set (𝒳 → 𝒵 → ℝ)) (g₀ : 𝒳 → 𝒵 → ℝ)
    (ρ ξ : ℝ) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (rawG rawH rawR : ℕ → ℝ → ℝ) (δ ν baseδ baseν : ℕ → ℝ)
    (κδ κν required : ℝ)
    (hG : DensityCriticalRadiusBound V G g₀ rawG)
    (hH : HypothesisCriticalRadiusBound V mu G rawH ρ)
    (hscale : RDIVPublicScaleCalibration ρ ξ baseδ baseν
      (rdivEvaluatedAccuracy rawG) (rdivEvaluatedAccuracy rawH)
      (rdivEvaluatedAccuracy rawR))
    (hinflate : CalibratedValidBounds δ ν baseδ baseν κδ κν required)
    (n : ℕ) (hn : 0 < n) : rdivPublicLogScale ρ ξ n ≤ δ n := by
  have hquarter : ξ / 4 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hξ.1, hξ.2]
  have hg := (hG n hn (ξ / 4) hquarter).1.le
  have hh := (hH n hn (ξ / 4) hquarter).1.1.le
  have heq : gridConfidence ρ (ξ / 4) n = gridConfidence ρ ξ n / 4 := by
    unfold gridConfidence
    ring
  rw [heq] at hh
  have hs := (hscale.1 n hn).1
  change rawG n (ξ / 4) + rawH n (gridConfidence ρ ξ n / 4) +
    rdivPublicLogScale ρ ξ n ≤ baseδ n at hs
  have hf : rdivPublicLogScale ρ ξ n ≤ baseδ n := by linarith only [hg, hh, hs]
  have hb : 0 ≤ baseδ n := (Real.sqrt_nonneg _).trans hf
  have hδ : baseδ n ≤ δ n := by
    rw [hinflate.2.2.2.2.1 n]
    nlinarith only [hinflate.1, hb]
  exact hf.trans hδ

/-- If [the sample size is positive](hyp:hn), [the pilot is bounded in absolute
value by B at every calibration observation](hyp:hr), and [the estimated
operator applied to h has the same bound there](hyp:hT), [the calibration
statistic is at most four times B squared](goal). -/
-- @node: rdiv_calibration_stat_le_four
lemma rdiv_calibration_stat_le_four (mu : Measure 𝒳)
    (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (rHat : ℕ → Ω → 𝒵 → ℝ)
    (B : ℝ) (n : ℕ) (hn : 0 < n) (ω : Ω) (h : V.Hbar.toSubmodule)
    (hr : ∀ i ∈ split.cal n, |rHat n ω (V.zOf (sample.Z i ω))| ≤ B)
    (hT : ∀ i ∈ split.cal n,
      |estimatedOperator V mu gHat n ω h (V.zOf (sample.Z i ω))| ≤ B) :
    rdivCalibrationStat V P sample split mu gHat rHat n ω h ≤ 4 * B ^ 2 := by
  unfold rdivCalibrationStat blockAverage
  rw [split.card_cal]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  apply (inv_mul_le_iff₀ hn').2
  calc
    _ ≤ ∑ _i ∈ split.cal n, 4 * B ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have ha := abs_le.mp (hr i hi)
      have hb := abs_le.mp (hT i hi)
      nlinarith [sq_nonneg (rHat n ω (V.zOf (sample.Z i ω)) -
        estimatedOperator V mu gHat n ω h (V.zOf (sample.Z i ω)) - 2 * B),
        sq_nonneg (rHat n ω (V.zOf (sample.Z i ω)) -
        estimatedOperator V mu gHat n ω h (V.zOf (sample.Z i ω)) + 2 * B)]
    _ = _ := by simp [split.card_cal]

/-- Assume [the density class is realizable](hyp:hDensity), [its densities obey
the common support and density bounds](hyp:hBounds), [the hypothesis class is
bounded by B on that support](hyp:hHyp), and [B is nonnegative](hyp:hB).
If [the sample size is positive](hyp:hn), [the fitted density belongs to the
class](hyp:hg), [h belongs to the hypothesis class](hyp:hh), [the pilot is bounded
by B at calibration observations](hyp:hr), and [the fitted density integrates
to one at each such observation](hyp:hg1), [the calibration statistic is at most
four times B squared](goal). -/
-- @node: rdiv_calibration_stat_le_four_of_density
lemma rdiv_calibration_stat_le_four_of_density (mu : Measure 𝒳)
    (G : Set (𝒳 → 𝒵 → ℝ)) (g₀ : 𝒳 → 𝒵 → ℝ)
    (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (rHat : ℕ → Ω → 𝒵 → ℝ)
    (support : Set (𝒳 × 𝒵)) (B c₀ CG : ℝ)
    (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hHyp : HypothesisClassBounded V support B) (hB : 0 ≤ B)
    (n : ℕ) (hn : 0 < n) (ω : Ω) (hg : gHat n ω ∈ G)
    (h : V.Hbar.toSubmodule) (hh : h ∈ V.H)
    (hr : ∀ i ∈ split.cal n, |rHat n ω (V.zOf (sample.Z i ω))| ≤ B)
    (hg1 : ∀ i ∈ split.cal n,
      (∫ x, gHat n ω x (V.zOf (sample.Z i ω)) ∂mu) = 1) :
    rdivCalibrationStat V P sample split mu gHat rHat n ω h ≤ 4 * B ^ 2 := by
  apply rdiv_calibration_stat_le_four V P sample split mu gHat rHat B n hn ω h hr
  intro i hi
  have hgi : Integrable (fun x => gHat n ω x (V.zOf (sample.Z i ω))) mu := by
    by_contra hnot
    have hnorm := hg1 i hi
    rw [integral_undef hnot] at hnorm
    norm_num at hnorm
  exact rdiv_density_operator_support_bound mu (gHat n ω) (primalVersion V h) B
    support hB (V.primal_measurable h) (hHyp h hh)
    (hBounds.2.2.2.2 (gHat n ω) hg) _ hgi
    (fun x => (hDensity.2 (gHat n ω) hg).2.1 x _) (hg1 i hi)

/-- If [the grid ratio is at least one half and less than one](hyp:hρ),
[the failure probability lies strictly between zero and one](hyp:hξ),
[the sample size meets the minimum for B](hyp:hn), [δ dominates the public
logarithmic scale](hyp:hfloor), and [the terminal discrepancy is at most four
times B squared](hyp:hD), [the search accepts, uses at most the terminal index
plus one fits, and either selects index zero or selects a positive index
satisfying the adjacent discrepancy relation](goal). -/
-- @node: rdiv_search_of_terminal_bound
lemma rdiv_search_of_terminal_bound (ρ ξ B δ ν : ℝ)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (n : ℕ) (hn : rdivMinSampleSize B ≤ n) (D : ℝ → ℝ)
    (hfloor : rdivPublicLogScale ρ ξ n ≤ δ)
    (hD : D (gridValue ρ (terminalIndex ρ n)) ≤ 4 * B ^ 2) :
    Accepts ρ n D (rdivNoiseLevel δ ν) ∧
      discrepancyIndex ρ n D (rdivNoiseLevel δ ν) + 1 ≤ terminalIndex ρ n + 1 ∧
      (discrepancyIndex ρ n D (rdivNoiseLevel δ ν) = 0 ∨
        (0 < discrepancyIndex ρ n D (rdivNoiseLevel δ ν) ∧
          AdjacentDiscrepancyRelation ρ (selectedPenalty ρ n D (rdivNoiseLevel δ ν))
            D (rdivNoiseLevel δ ν))) := by
  have hAccept : Accepts ρ n D (rdivNoiseLevel δ ν) :=
    ⟨terminalIndex ρ n, le_rfl, hD.trans
      (rdiv_terminal_threshold_bound ρ ξ B δ ν hρ hξ n hn hfloor)⟩
  have hi := discrepancyIndex_first_acceptance ρ n D (rdivNoiseLevel δ ν) hρ hAccept
  exact ⟨hAccept, Nat.add_le_add_right hi.1 1, hi.2⟩

/-- If [the source exponent is positive](hyp:hβ) and [the minimum-norm solution
is zero](hyp:hz), [the source condition holds at that exponent with zero witness](goal). -/
-- @node: rdiv_zero_source_witness
lemma rdiv_zero_source_witness (β : ℝ) (hβ : 0 < β) (hz : ZeroSolutionCase V) :
    BetaSourceCondition V β 0 := by
  refine ⟨hβ, ?_⟩
  rw [map_zero]
  exact hz

/-- If [the candidate family satisfies a discrepancy envelope with zero source
witness on E](hyp:henv) and [the sample outcome belongs to E](hyp:hω),
[the calibration discrepancy search selects index zero](goal). -/
-- @node: rdiv_zero_envelope_initial_index
lemma rdiv_zero_envelope_initial_index (mu : Measure 𝒳)
    (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (rHat : ℕ → Ω → 𝒵 → ℝ)
    (ρ β : ℝ) (δ ν : ℕ → ℝ)
    (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (n : ℕ) (E : Set Ω) (C : ℝ)
    (henv : RDIVDiscrepancyEnvelope V P sample split mu gHat rHat ρ β δ ν
      0 candidate n E C) (ω : Ω) (hω : ω ∈ E) :
    discrepancyIndex ρ n
      (fun lam => rdivCalibrationStat V P sample split mu gHat rHat n ω (candidate n lam ω))
      (rdivNoiseLevel (δ n) (ν n)) = 0 := by
  apply rdiv_initial_index_zero
  have hgrid : (2 : ℝ) ∈ regGrid ρ n := by
    exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), by simp [gridValue]⟩
  simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, add_zero]
    using henv.2 ω hω 2 hgrid

end Papers.TsAdaptiveEstimationInference
