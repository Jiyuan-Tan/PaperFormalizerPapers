module
public import Papers.TbsExtremeEffects.Basic
public import Mathlib.Tactic

/-! Scalar survival consequences of the polar regular-variation certificate. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators
variable {q d : ℕ}

-- @node: measurable_l1Norm
/-- [The $ℓ1$ norm is a measurable function](goal). -/
@[fun_prop] lemma measurable_l1Norm : Measurable (l1Norm (k := d)) := by
  unfold l1Norm
  fun_prop

-- @node: measurable_radius
/-- For [an extreme-value model](hyp:M), [its noise radius is measurable](goal). -/
@[fun_prop] lemma measurable_radius (M : ExtremeModel q d) : Measurable (radius M) := by
  unfold radius
  exact measurable_l1Norm.comp M.measurable_U

-- @node: measurableSet_positiveSphere_l1
/-- [The nonnegative $ℓ1$ unit sphere is a measurable set](goal). -/
lemma measurableSet_positiveSphere_l1 :
    MeasurableSet (positiveSphere (l1Norm (k := d))) := by
  have horth : MeasurableSet (nonnegativeOrthant (k := d)) := by
    unfold nonnegativeOrthant
    simpa only [Set.ofPred_forall] using MeasurableSet.iInter (fun i : Fin d =>
      measurableSet_le (measurable_const (a := (0 : ℝ)))
        (measurable_pi_apply i (X := fun _ : Fin d => ℝ)))
  exact horth.inter (measurable_l1Norm (d := d) (measurableSet_singleton 1))

-- @node: relativeSphereFrontier_self
/-- For [a radial gauge](hyp:N), [the relative frontier of its entire positive sphere is empty](goal). -/
lemma relativeSphereFrontier_self (N : (Fin d → ℝ) → ℝ) :
    relativeSphereFrontier N (positiveSphere N) = ∅ := by
  have hfull : {v : {u // u ∈ positiveSphere N} | v.val ∈ positiveSphere N} = Set.univ := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact v.property
  simp only [relativeSphereFrontier, hfull, frontier_univ, Set.image_empty]

-- @node: direction_mem_positiveSphere
/-- For [an extreme-value model](hyp:M), if [an observation has positive radius](hyp:hw), then [its normalized noise direction lies on the nonnegative $ℓ1$ unit sphere](goal). -/
lemma direction_mem_positiveSphere (M : ExtremeModel q d) {w : M.Om}
    (hw : 0 < radius M w) : direction M w ∈ positiveSphere l1Norm := by
  refine ⟨fun i => div_nonneg (M.U_nonnegative w i) hw.le, ?_⟩
  change (∑ i, |M.U w i / radius M w|) = 1
  simp only [abs_div, abs_of_nonneg hw.le]
  rw [← Finset.sum_div]
  exact div_self hw.ne'

-- @node: tailProb_nonneg
/-- For [an extreme-value model](hyp:M) and [a threshold](hyp:t), [the probability of exceeding that threshold is nonnegative](goal). -/
lemma tailProb_nonneg (M : ExtremeModel q d) (t : ℝ) : 0 ≤ tailProb M t :=
  ENNReal.toReal_nonneg

-- @node: tailProb_antitone
/-- For [an extreme-value model](hyp:M), [its exceedance probability cannot increase as the threshold rises](goal). -/
lemma tailProb_antitone (M : ExtremeModel q d) : Antitone (tailProb M) := by
  intro s t hst
  exact ENNReal.toReal_mono (measure_ne_top M.mu _)
    (measure_mono fun w hw => hst.trans_lt hw)

-- @node: measurable_tailProb
/-- For [an extreme-value model](hyp:M), [its exceedance-probability function is measurable](goal). -/
@[fun_prop] lemma measurable_tailProb (M : ExtremeModel q d) : Measurable (tailProb M) :=
  (tailProb_antitone M).measurable

/-- For [an extreme-value model](hyp:M) with [regularly varying noise](hyp:hRV) and [a positive radial multiplier](hyp:hr), [the normalizer times the tail probability at that multiplier converges to the tail-mass constant times the corresponding power law](goal).

Using the entire sphere removes the angular restriction from the tail certificate. -/
-- @node: normalized_tailProb_limit
lemma normalized_tailProb_limit (M : ExtremeModel q d) (hRV : NoiseRegularlyVarying M)
    {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n : ℕ => (n : ℝ) * tailProb M (M.bRV n * r))
      atTop (𝓝 (M.cRV * r ^ (-M.beta))) := by
  have cert := hRV.2.2
  have := cert.spectral_probability
  have hmass : M.S (positiveSphere l1Norm) = 1 := by
    have hfull : M.S (positiveSphere l1Norm) = M.S Set.univ :=
      measure_eq_measure_of_null_sdiff (Set.subset_univ _)
        (by rw [← Set.compl_eq_univ_sdiff]; exact cert.spectral_support)
    simpa using hfull
  have hlim := cert.setwise r hr (positiveSphere l1Norm)
    measurableSet_positiveSphere_l1 (Set.Subset.refl _)
    (by rw [relativeSphereFrontier_self, measure_empty])
  simp only [hmass, ENNReal.toReal_one, mul_one] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hb : 0 < M.bRV n * r := mul_pos (cert.normalizer_pos n hn) hr
  have hevent : M.U ⁻¹' {u | M.bRV n * r < l1Norm u ∧
      (fun i => u i / l1Norm u) ∈ positiveSphere l1Norm} =
      {w | M.bRV n * r < radius M w} := by
    ext w
    constructor
    · exact fun h => h.1
    · intro hw
      exact ⟨hw, direction_mem_positiveSphere M (hb.trans hw)⟩
  have hmeas : MeasurableSet {u : Fin d → ℝ | M.bRV n * r < l1Norm u ∧
      (fun i => u i / l1Norm u) ∈ positiveSphere l1Norm} := by
    apply (measurableSet_lt measurable_const measurable_l1Norm).inter
    apply measurableSet_positiveSphere_l1.preimage
    fun_prop
  rw [Measure.map_apply M.measurable_U hmeas, hevent]
  rfl

/-- For [an extreme-value model](hyp:M) with [regularly varying noise](hyp:hRV), [the exceedance probability at every threshold is positive](goal).

The positive limiting tail mass implies that conditioning at every finite radius is valid. -/
-- @node: tailProb_pos_of_regularVariation
lemma tailProb_pos_of_regularVariation (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (t : ℝ) : 0 < tailProb M t := by
  have hlim := normalized_tailProb_limit M hRV (r := 1) (by norm_num)
  simp only [mul_one, Real.one_rpow] at hlim
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) * tailProb M (M.bRV n) :=
    (tendsto_order.1 hlim).1 0 hRV.2.2.mass_pos
  obtain ⟨n, hnpos, hnt⟩ := (hpos.and
    (hRV.2.2.normalizer_tendsto.eventually (eventually_ge_atTop t))).exists
  have htail : 0 < tailProb M (M.bRV n) := by
    by_contra h
    have hzero : tailProb M (M.bRV n) = 0 :=
      le_antisymm (not_lt.mp h) (tailProb_nonneg M _)
    rw [hzero, mul_zero] at hnpos
    exact (lt_irrefl 0) hnpos
  exact htail.trans_le (tailProb_antitone M hnt)

-- @node: tailProb_normalizer_ratio_limit
/-- For [an extreme-value model](hyp:M) with [regularly varying noise](hyp:hRV) and [a positive radial multiplier](hyp:hr), [the ratio of exceedance probabilities at the multiplied and original normalizing radii converges to the corresponding power law](goal). -/
lemma tailProb_normalizer_ratio_limit (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n : ℕ => tailProb M (M.bRV n * r) / tailProb M (M.bRV n))
      atTop (𝓝 (r ^ (-M.beta))) := by
  have hbase := normalized_tailProb_limit M hRV (r := 1) (by norm_num)
  simp only [mul_one, Real.one_rpow] at hbase
  have hratio := (normalized_tailProb_limit M hRV hr).div hbase hRV.2.2.mass_pos.ne'
  have hcancel : M.cRV * r ^ (-M.beta) / M.cRV = r ^ (-M.beta) := by
    exact mul_div_cancel_left₀ _ hRV.2.2.mass_pos.ne'
  rw [hcancel] at hratio
  apply hratio.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact mul_div_mul_left _ _ (by exact_mod_cast (Nat.zero_lt_of_lt hn).ne')

-- @node: radialFactor_eq_one_of_alpha_zero
/-- For [an extreme-value model](hyp:M), [regularly varying noise](hyp:hRV), [a zero radial exponent](hyp:hzero), and [a threshold](hyp:t), [the radial factor equals one](goal). -/
lemma radialFactor_eq_one_of_alpha_zero (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hzero : M.alpha = 0) (t : ℝ) :
    radialFactor M t = 1 := by
  have htail : M.mu {w | t < radius M w} ≠ 0 := by
    intro h
    have hpos := tailProb_pos_of_regularVariation M hRV t
    simp only [tailProb, h, ENNReal.toReal_zero] at hpos
    exact (lt_irrefl 0) hpos
  have : IsProbabilityMeasure (tailLaw M t) := cond_isProbabilityMeasure htail
  simp [radialFactor, hzero]

end Papers.TbsExtremeEffects
