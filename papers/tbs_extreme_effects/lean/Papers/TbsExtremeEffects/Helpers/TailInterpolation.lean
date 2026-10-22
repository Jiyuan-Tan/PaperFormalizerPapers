module
public import Papers.TbsExtremeEffects.Helpers.TailSurvival
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Interpolation from normalizing-sequence tails to real thresholds. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
variable {q d : ℕ}

-- @node: tailProb_tendsto_zero
/-- For [an extreme-value model](hyp:M) with [regularly varying noise](hyp:hRV), [the probability of exceeding a radius tends to zero as the radius grows](goal). -/
lemma tailProb_tendsto_zero (M : ExtremeModel q d) (hRV : NoiseRegularlyVarying M) :
    Tendsto (tailProb M) atTop (𝓝 0) := by
  have hbase := normalized_tailProb_limit M hRV (r := 1) (by norm_num)
  simp only [mul_one, Real.one_rpow] at hbase
  have hseq : Tendsto (fun n => tailProb M (M.bRV n)) atTop (𝓝 0) := by
    apply (hbase.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))).congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact mul_div_cancel_left₀ _ (by exact_mod_cast (Nat.zero_lt_of_lt hn).ne')
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun t => ha.trans_le (tailProb_nonneg M t)
  · intro a ha
    obtain ⟨n, hn⟩ := ((tendsto_order.1 hseq).2 a ha).exists
    filter_upwards [eventually_ge_atTop (M.bRV n)] with t ht
    exact (tailProb_antitone M ht).trans_lt hn

/-- For [an extreme-value model](hyp:M) with [regularly varying noise](hyp:hRV), [there is an integer-valued index tending to infinity whose product with the tail probability converges to the model's tail-mass constant](goal).

Calibrate an integer index by the tail mass rather than by monotonicity of `bRV`. -/
-- @node: exists_tail_mass_index
lemma exists_tail_mass_index (M : ExtremeModel q d) (hRV : NoiseRegularlyVarying M) :
    ∃ k : ℝ → ℕ, Tendsto k atTop atTop ∧
      Tendsto (fun t => (k t : ℝ) * tailProb M t) atTop (𝓝 M.cRV) := by
  let z : ℝ → ℝ := fun t => M.cRV / tailProb M t
  have hzpos (t : ℝ) : 0 < z t :=
    div_pos hRV.2.2.mass_pos (tailProb_pos_of_regularVariation M hRV t)
  have hz : Tendsto z atTop atTop := by
    apply tendsto_atTop.2
    intro a
    have hden : 0 < M.cRV / (max a 0 + 1) := div_pos hRV.2.2.mass_pos (by positivity)
    filter_upwards [(tendsto_order.1 (tailProb_tendsto_zero M hRV)).2 _ hden] with t ht
    have hF := tailProb_pos_of_regularVariation M hRV t
    have hbound : max a 0 + 1 < z t := by
      apply (lt_div_iff₀ hF).2
      have := (lt_div_iff₀ (by positivity : 0 < max a 0 + 1)).1 ht
      nlinarith
    exact (le_max_left a 0).trans (by linarith)
  let k : ℝ → ℕ := fun t => ⌊z t⌋₊
  have hk : Tendsto k atTop atTop := by
    apply tendsto_atTop.2
    intro n
    filter_upwards [hz.eventually (eventually_ge_atTop (n : ℝ))] with t ht
    exact Nat.le_floor ht
  refine ⟨k, hk, ?_⟩
  have hratio := (tendsto_nat_floor_div_atTop (R := ℝ)).comp hz
  have hmass := hratio.const_mul M.cRV
  simp only [mul_one] at hmass
  apply hmass.congr'
  apply Eventually.of_forall
  intro t
  dsimp [k, z]
  field_simp [(tailProb_pos_of_regularVariation M hRV t).ne', hRV.2.2.mass_pos.ne']

/-- For [an extreme-value model](hyp:M) with [regularly varying noise](hyp:hRV), [an integer index tending to infinity](hyp:hk), and [that index calibrated so its tail mass converges to the model's tail-mass constant](hyp:hmass), [multiplying its normalizing radius by factors just below or above one eventually brackets every threshold](goal).

The mass-calibrated index brackets a real threshold by arbitrarily close dilations. -/
-- @node: tail_mass_index_bracket
lemma tail_mass_index_bracket (M : ExtremeModel q d) (hRV : NoiseRegularlyVarying M)
    (k : ℝ → ℕ) (hk : Tendsto k atTop atTop)
    (hmass : Tendsto (fun t => (k t : ℝ) * tailProb M t) atTop (𝓝 M.cRV)) :
    (∀ s, 0 < s → s < 1 → ∀ᶠ t in atTop, M.bRV (k t) * s < t) ∧
      (∀ s, 1 < s → ∀ᶠ t in atTop, t < M.bRV (k t) * s) := by
  constructor
  · intro s hs hsone
    have hpow : 1 < s ^ (-M.beta) := by
      simpa using Real.rpow_lt_rpow_of_neg hs hsone (neg_neg_of_pos hRV.1)
    have hlim := (normalized_tailProb_limit M hRV hs).comp hk
    have hgap : 0 < M.cRV * s ^ (-M.beta) - M.cRV := by
      nlinarith [hRV.2.2.mass_pos]
    filter_upwards [(tendsto_order.1 (hlim.sub hmass)).1 0 hgap] with t ht
    by_contra hnot
    have hle := tailProb_antitone M (not_lt.mp hnot)
    have := mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg (k t) : (0 : ℝ) ≤ k t)
    dsimp at ht
    linarith
  · intro s hs
    have hspos : 0 < s := by linarith
    have hpow : s ^ (-M.beta) < 1 := by
      simpa using Real.rpow_lt_rpow_of_neg (by norm_num : (0 : ℝ) < 1)
        hs (neg_neg_of_pos hRV.1)
    have hlim := (normalized_tailProb_limit M hRV hspos).comp hk
    have hgap : 0 < M.cRV - M.cRV * s ^ (-M.beta) := by
      nlinarith [hRV.2.2.mass_pos]
    filter_upwards [(tendsto_order.1 (hmass.sub hlim)).1 0 hgap] with t ht
    by_contra hnot
    have hle := tailProb_antitone M (not_lt.mp hnot)
    have := mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg (k t) : (0 : ℝ) ≤ k t)
    dsimp at ht
    linarith

-- @node: tail_mass_index_ratio_limit
/-- For [an extreme-value model](hyp:M) with [regularly varying noise](hyp:hRV), [an integer index tending to infinity](hyp:hk), [a tail-mass calibration for that index](hyp:hmass), and [a positive dilation](hyp:hs), [the ratio of the tail probability at the indexed normalizing radius to the tail probability at the threshold converges to the corresponding power law](goal). -/
lemma tail_mass_index_ratio_limit (M : ExtremeModel q d) (hRV : NoiseRegularlyVarying M)
    (k : ℝ → ℕ) (hk : Tendsto k atTop atTop)
    (hmass : Tendsto (fun t => (k t : ℝ) * tailProb M t) atTop (𝓝 M.cRV))
    {s : ℝ} (hs : 0 < s) :
    Tendsto (fun t => tailProb M (M.bRV (k t) * s) / tailProb M t)
      atTop (𝓝 (s ^ (-M.beta))) := by
  have hlim := ((normalized_tailProb_limit M hRV hs).comp hk).div
    hmass hRV.2.2.mass_pos.ne'
  rw [mul_div_cancel_left₀ _ hRV.2.2.mass_pos.ne'] at hlim
  apply hlim.congr'
  filter_upwards [hk.eventually (eventually_ge_atTop (1 : ℕ))] with t ht
  exact mul_div_mul_left _ _ (by exact_mod_cast (Nat.zero_lt_of_lt ht).ne')

/-- For [an extreme-value model](hyp:M) with [regularly varying noise](hyp:hRV) and [a positive dilation](hyp:hx), [the ratio of tail probabilities at the dilated and original thresholds converges to the power-law ratio](goal).

Monotonicity interpolates the polar certificate without assuming a monotone normalizer. -/
-- @node: tailProb_ratio_limit
lemma tailProb_ratio_limit (M : ExtremeModel q d) (hRV : NoiseRegularlyVarying M)
    {x : ℝ} (hx : 0 < x) :
    Tendsto (fun t => tailProb M (t * x) / tailProb M t)
      atTop (𝓝 (x ^ (-M.beta))) := by
  obtain ⟨k, hk, hmass⟩ := exists_tail_mass_index M hRV
  have hbracket := tail_mass_index_bracket M hRV k hk hmass
  have hcont : ContinuousAt (fun s : ℝ => (s * x) ^ (-M.beta)) 1 := by
    exact (continuousAt_id.mul continuousAt_const).rpow_const
      (Or.inl (by simpa only [Pi.mul_apply, id_eq, one_mul] using hx.ne'))
  have hc : Tendsto (fun s : ℝ => (s * x) ^ (-M.beta)) (𝓝 1)
      (𝓝 (x ^ (-M.beta))) := by simpa only [one_mul] using hcont.tendsto
  apply tendsto_order.2
  constructor
  · intro a ha
    have hnear := (tendsto_order.1 hc).1 a ha
    obtain ⟨lo, hi, ⟨hlo, hhi⟩, hsub⟩ := hnear.exists_Ioo_subset
    let s := (1 + hi) / 2
    have hs : 1 < s := by dsimp [s]; linarith
    have hsa : a < (s * x) ^ (-M.beta) :=
      hsub ⟨by dsimp [s]; linarith, by dsimp [s]; linarith⟩
    have hlim := tail_mass_index_ratio_limit M hRV k hk hmass
      (mul_pos (by linarith : 0 < s) hx)
    filter_upwards [hbracket.2 s hs, (tendsto_order.1 hlim).1 a hsa] with t ht hratio
    apply hratio.trans_le
    apply (div_le_div_iff_of_pos_right (tailProb_pos_of_regularVariation M hRV t)).2
    apply tailProb_antitone M
    nlinarith [mul_lt_mul_of_pos_right ht hx]
  · intro a ha
    have hnear := (tendsto_order.1 hc).2 a ha
    obtain ⟨lo, hi, ⟨hlo, hhi⟩, hsub⟩ := hnear.exists_Ioo_subset
    let s := (max lo 0 + 1) / 2
    have hlo' : max lo 0 < 1 := max_lt hlo (by norm_num)
    have hspos : 0 < s := by dsimp [s]; positivity
    have hsone : s < 1 := by dsimp [s]; linarith
    have hsa : (s * x) ^ (-M.beta) < a := by
      apply hsub
      constructor
      · dsimp [s]; linarith [le_max_left lo 0]
      · linarith
    have hlim := tail_mass_index_ratio_limit M hRV k hk hmass (mul_pos hspos hx)
    filter_upwards [hbracket.1 s hspos hsone, (tendsto_order.1 hlim).2 a hsa]
      with t ht hratio
    apply lt_of_le_of_lt _ hratio
    apply (div_le_div_iff_of_pos_right (tailProb_pos_of_regularVariation M hRV t)).2
    apply tailProb_antitone M
    nlinarith [mul_lt_mul_of_pos_right ht hx]

end Papers.TbsExtremeEffects
