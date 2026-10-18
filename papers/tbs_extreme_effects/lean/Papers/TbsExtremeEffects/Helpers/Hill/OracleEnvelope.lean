module
public import Papers.TbsExtremeEffects.Helpers.Hill.OracleCutoff

/-! Construction of a bias-admissible Hill candidate from the tail envelope. -/

@[expose] public section
namespace Papers.TbsExtremeEffects
open Filter
open scoped Topology

/-- Given [a bias function](hyp:eta), [a fixed tail cutoff](hyp:v₀), and [a threshold](hyp:v), [the Hill tail-bias envelope](goal) is the supremum of the absolute bias over all arguments at least as large as both thresholds. -/
-- @node: hillTailBiasEnvelope
noncomputable def hillTailBiasEnvelope (eta : ℝ → ℝ) (v₀ v : ℝ) : ℝ :=
  sSup ((fun w => |eta w|) '' Set.Ici (max v v₀))

/-- If [the absolute-bias values above the fixed tail cutoff are bounded above](hyp:hb), then [the absolute-bias values above the larger of that cutoff and any threshold are bounded above](goal). -/
-- @node: hill_tail_bias_image_bddAbove
lemma hill_tail_bias_image_bddAbove (eta : ℝ → ℝ) {v₀ v : ℝ}
    (hb : BddAbove ((fun w => |eta w|) '' Set.Ici v₀)) :
    BddAbove ((fun w => |eta w|) '' Set.Ici (max v v₀)) := by
  apply hb.mono
  rintro z ⟨w, hw, rfl⟩
  exact ⟨w, (le_max_right v v₀).trans hw, rfl⟩

/-- If [the absolute-bias values above the fixed tail cutoff are bounded above](hyp:hb), then [the Hill tail-bias envelope is nonincreasing as its threshold rises](goal). -/
-- @node: hillTailBiasEnvelope_antitone
lemma hillTailBiasEnvelope_antitone (eta : ℝ → ℝ) {v₀ : ℝ}
    (hb : BddAbove ((fun w => |eta w|) '' Set.Ici v₀)) :
    Antitone (hillTailBiasEnvelope eta v₀) := by
  intro x y hxy
  unfold hillTailBiasEnvelope
  apply csSup_le_csSup (hill_tail_bias_image_bddAbove eta hb)
  · exact ⟨|eta (max y v₀)|, ⟨max y v₀, Set.self_mem_Ici, rfl⟩⟩
  rintro z ⟨w, hw, rfl⟩
  exact ⟨w, (max_le_max_right v₀ hxy).trans hw, rfl⟩

/-- If [the absolute-bias values above the fixed tail cutoff are bounded above](hyp:hb) and [the argument is at least that cutoff](hyp:hv), then [the Hill tail-bias envelope at that argument is at least the absolute bias there](goal). -/
-- @node: abs_bias_le_hillTailBiasEnvelope
lemma abs_bias_le_hillTailBiasEnvelope (eta : ℝ → ℝ) {v₀ v : ℝ}
    (hb : BddAbove ((fun w => |eta w|) '' Set.Ici v₀)) (hv : v₀ ≤ v) :
    |eta v| ≤ hillTailBiasEnvelope eta v₀ v := by
  apply le_csSup (hill_tail_bias_image_bddAbove eta hb)
  exact ⟨v, by simp only [max_eq_left hv, Set.mem_Ici]; exact le_rfl, rfl⟩

/-- If [every argument above the larger threshold has absolute bias at most the stated bound](hyp:hbound), then [the Hill tail-bias envelope is at most that bound](goal). -/
-- @node: hillTailBiasEnvelope_le
lemma hillTailBiasEnvelope_le (eta : ℝ → ℝ) {v₀ v b : ℝ}
    (hbound : ∀ w ≥ max v v₀, |eta w| ≤ b) :
    hillTailBiasEnvelope eta v₀ v ≤ b := by
  unfold hillTailBiasEnvelope
  apply csSup_le
  · exact ⟨|eta (max v v₀)|, ⟨max v v₀, Set.self_mem_Ici, rfl⟩⟩
  rintro z ⟨w, hw, rfl⟩
  exact hbound w hw

/-- For a tail-bias envelope, if [the tail parameter is positive](hyp:hb), [the confidence level lies in its allowed domain](hyp:hd), [the envelope coefficient is nonnegative](hyp:hC), [the tail cutoff is positive](hyp:hv), and [the envelope satisfies the displayed beta-dependent tail bound](hyp:henvelope), then [there is a positive fixed candidate constant for which eventually the rounded candidate is an admissible Hill index and its tail bias fits the confidence budget](goal). -/
-- @node: hill_envelope_candidate_eventually
lemma hill_envelope_candidate_eventually (etaBar : ℝ → ℝ)
    {beta delta C v₀ : ℝ} (hb : 0 < beta) (hd : ConfidenceDomain delta)
    (hC : 0 ≤ C) (hv : 0 < v₀)
    (henvelope : ∀ v ≥ v₀, etaBar v ≤
      if beta = 1 then C * v ^ (-1 : ℝ) * Real.log v
      else C * v ^ (-min 1 (1 / beta))) :
    ∃ a > 0, ∀ᶠ n : ℕ in atTop,
      let k := ⌊a * hillOracleScale beta n (hillDeviation n delta)⌋₊
      1 ≤ k ∧ k ∈ Finset.Icc (hillLower n) (n - 1) ∧
        v₀ ≤ (n : ℝ) / (2 * k) ∧
        Real.sqrt k * etaBar ((n : ℝ) / (2 * k)) ≤ (1 / beta) * hillDeviation n delta := by
  have hg : 0 < 1 / beta := one_div_pos.mpr hb
  by_cases hbeta : beta = 1
  · obtain ⟨a, ha, hbias⟩ := hill_log_envelope_candidate_constant etaBar hC hg
      (by simpa only [hbeta, if_true] using henvelope)
    refine ⟨a, ha, ?_⟩
    filter_upwards [hill_oracle_candidate_eventually_admissible hb hd ha hv,
      eventually_ge_atTop (2 : ℕ)] with n hn hn2
    dsimp only at hn ⊢
    refine ⟨hn.1, hn.2.1, hn.2.2, ?_⟩
    apply hbias n (hillDeviation n delta) _
      (by exact_mod_cast hn2) (zero_lt_one.trans_le (hillDeviation_ge_one n hd))
      (by omega) hn.2.2
    simp only [hillOracleScale, hbeta, if_true, mul_assoc]
    exact le_rfl
  · have hp : 0 < min 1 (1 / beta) := lt_min zero_lt_one hg
    obtain ⟨a, ha, hbias⟩ := hill_power_envelope_candidate_constant etaBar hp hC hg
      (by simpa only [hbeta, if_false] using henvelope)
    refine ⟨a, ha, ?_⟩
    filter_upwards [hill_oracle_candidate_eventually_admissible hb hd ha hv,
      eventually_ge_atTop (1 : ℕ)] with n hn hn1
    dsimp only at hn ⊢
    refine ⟨hn.1, hn.2.1, hn.2.2, ?_⟩
    apply hbias n (hillDeviation n delta) _
      (by exact_mod_cast hn1) (zero_lt_one.trans_le (hillDeviation_ge_one n hd))
      (by omega) hn.2.2
    simp only [hillOracleScale, hbeta, if_false, mul_assoc]
    exact le_rfl

/-- For [a bias function](hyp:eta) and [a tail envelope](hyp:etaBar), if [the index is positive](hyp:hk), [the envelope is nonincreasing on the tail](hyp:hmono), [the envelope bounds absolute bias on that tail](hyp:heta), [the candidate threshold lies in the tail domain](hyp:hdomain), [that threshold is no greater than the exponential threshold](hyp:hthreshold), [the evaluation point is at least the exponential threshold's logarithm](hyp:hu), and [the candidate threshold meets its bias budget](hyp:hbudget), then [the absolute bias at the evaluation point is bounded by the budget divided by the square root of the index](goal). -/
-- @node: hill_tail_envelope_above_threshold
lemma hill_tail_envelope_above_threshold (eta etaBar : ℝ → ℝ)
    {n g c y u v₀ : ℝ} {k : ℕ} (hk : 0 < k)
    (hmono : AntitoneOn etaBar (Set.Ici v₀))
    (heta : ∀ v ≥ v₀, |eta v| ≤ etaBar v)
    (hdomain : v₀ ≤ n / (2 * k))
    (hthreshold : n / (2 * k) ≤ Real.exp y) (hu : y ≤ u)
    (hbudget : Real.sqrt k * etaBar (n / (2 * k)) ≤ g * c) :
    |eta (Real.exp u)| ≤ g * c / Real.sqrt k := by
  have harg : n / (2 * k) ≤ Real.exp u :=
    hthreshold.trans (Real.exp_le_exp.mpr hu)
  have hs : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hk)
  apply (heta _ (hdomain.trans harg)).trans
  apply (hmono hdomain (hdomain.trans harg) harg).trans
  exact (le_div_iff₀ hs).mpr (by simpa only [mul_comm] using hbudget)

end Papers.TbsExtremeEffects
