module
public import Papers.TbsExtremeEffects.Helpers.TailInterpolation
public import Mathlib.MeasureTheory.Measure.Portmanteau

/-! Angular continuity-set convergence at real thresholds. -/

@[expose] public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
variable {q d : ℕ}

/-- For [an extreme-value model](hyp:M), [the direction map is measurable](goal). -/
-- @node: measurable_direction
@[fun_prop] lemma measurable_direction (M : ExtremeModel q d) : Measurable (direction M) := by
  unfold direction
  have hU := M.measurable_U
  fun_prop

/-- [The angular tail probability](goal) for [an extreme-value model](hyp:M), [an angular set](hyp:B), and [a radial threshold](hyp:t) is the model mass above that threshold whose direction lies in the set. -/
-- @node: angularTailProb
def angularTailProb (M : ExtremeModel q d) (B : Set (Fin d → ℝ)) (t : ℝ) : ℝ :=
  (M.mu {w | t < radius M w ∧ direction M w ∈ B}).toReal

/-- For [an extreme-value model](hyp:M) and [an angular set](hyp:B), [angular tail probability is nonincreasing in the radial threshold](goal). -/
-- @node: angularTailProb_antitone
lemma angularTailProb_antitone (M : ExtremeModel q d) (B : Set (Fin d → ℝ)) :
    Antitone (angularTailProb M B) := by
  intro s t hst
  exact ENNReal.toReal_mono (measure_ne_top M.mu _)
    (measure_mono fun w hw => ⟨hst.trans_lt hw.1, hw.2⟩)

/-- For [an extreme-value model](hyp:M), if [its noise is regularly varying](hyp:hRV), [the angular set is measurable](hyp:hB), [it lies on the positive l1 sphere](hyp:hsub), [its relative-sphere boundary has zero spectral mass](hyp:hboundary), and [the radial multiplier is positive](hyp:hr), then [the normalized angular tail probability converges to the stated spectral limit](goal). -/
-- @node: normalized_angularTailProb_limit
lemma normalized_angularTailProb_limit (M : ExtremeModel q d) (hRV : NoiseRegularlyVarying M)
    (B : Set (Fin d → ℝ)) (hB : MeasurableSet B) (hsub : B ⊆ positiveSphere l1Norm)
    (hboundary : M.S (relativeSphereFrontier l1Norm B) = 0) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n : ℕ => (n : ℝ) * angularTailProb M B (M.bRV n * r))
      atTop (𝓝 (M.cRV * r ^ (-M.beta) * (M.S B).toReal)) := by
  have hlim := hRV.2.2.setwise r hr B hB hsub hboundary
  convert hlim using 1
  funext n
  have hmeas : MeasurableSet {u : Fin d → ℝ | M.bRV n * r < l1Norm u ∧
      (fun i => u i / l1Norm u) ∈ B} := by
    apply (measurableSet_lt measurable_const measurable_l1Norm).inter
    apply hB.preimage
    fun_prop
  rw [Measure.map_apply M.measurable_U hmeas]
  rfl

/-- For [an extreme-value model](hyp:M), if [its noise is regularly varying](hyp:hRV), [the angular set is measurable](hyp:hB), [it lies on the positive l1 sphere](hyp:hsub), [its relative-sphere boundary has zero spectral mass](hyp:hboundary), [the integer index tends to infinity](hyp:hk), [the indexed tail mass has the stated limit](hyp:hmass), and [the radial multiplier is positive](hyp:hs), then [the angular tail probability divided by the tail probability converges to the stated spectral limit](goal). -/
-- @node: angularTailProb_mass_index_limit
lemma angularTailProb_mass_index_limit (M : ExtremeModel q d) (hRV : NoiseRegularlyVarying M)
    (B : Set (Fin d → ℝ)) (hB : MeasurableSet B) (hsub : B ⊆ positiveSphere l1Norm)
    (hboundary : M.S (relativeSphereFrontier l1Norm B) = 0)
    (k : ℝ → ℕ) (hk : Tendsto k atTop atTop)
    (hmass : Tendsto (fun t => (k t : ℝ) * tailProb M t) atTop (𝓝 M.cRV))
    {s : ℝ} (hs : 0 < s) :
    Tendsto (fun t => angularTailProb M B (M.bRV (k t) * s) / tailProb M t)
      atTop (𝓝 (s ^ (-M.beta) * (M.S B).toReal)) := by
  have hlim := ((normalized_angularTailProb_limit M hRV B hB hsub hboundary hs).comp hk).div
    hmass hRV.2.2.mass_pos.ne'
  have heq : M.cRV * s ^ (-M.beta) * (M.S B).toReal / M.cRV =
      s ^ (-M.beta) * (M.S B).toReal := by
    field_simp [hRV.2.2.mass_pos.ne']
  rw [heq] at hlim
  apply hlim.congr'
  filter_upwards [hk.eventually (eventually_ge_atTop (1 : ℕ))] with t ht
  exact mul_div_mul_left _ _ (by exact_mod_cast (Nat.zero_lt_of_lt ht).ne')

/-- For [an extreme-value model](hyp:M), if [its noise is regularly varying](hyp:hRV), [the angular set is measurable](hyp:hB), [it lies on the positive l1 sphere](hyp:hsub), and [its relative-sphere boundary has zero spectral mass](hyp:hboundary), then [the angular-to-radial tail ratio converges to the spectral mass of the set](goal). -/
-- @node: angularTailProb_ratio_limit
lemma angularTailProb_ratio_limit (M : ExtremeModel q d) (hRV : NoiseRegularlyVarying M)
    (B : Set (Fin d → ℝ)) (hB : MeasurableSet B) (hsub : B ⊆ positiveSphere l1Norm)
    (hboundary : M.S (relativeSphereFrontier l1Norm B) = 0) :
    Tendsto (fun t => angularTailProb M B t / tailProb M t)
      atTop (𝓝 ((M.S B).toReal)) := by
  obtain ⟨k, hk, hmass⟩ := exists_tail_mass_index M hRV
  have hbracket := tail_mass_index_bracket M hRV k hk hmass
  have hcont : ContinuousAt (fun s : ℝ => s ^ (-M.beta) * (M.S B).toReal) 1 := by
    exact (continuousAt_id.rpow_const (Or.inl (by norm_num))).mul continuousAt_const
  have hc : Tendsto (fun s : ℝ => s ^ (-M.beta) * (M.S B).toReal) (𝓝 1)
      (𝓝 ((M.S B).toReal)) := by simpa only [Real.one_rpow, one_mul] using hcont.tendsto
  apply tendsto_order.2
  constructor
  · intro a ha
    have hnear := (tendsto_order.1 hc).1 a ha
    obtain ⟨lo, hi, ⟨hlo, hhi⟩, hsub'⟩ := hnear.exists_Ioo_subset
    let s := (1 + hi) / 2
    have hs : 1 < s := by dsimp [s]; linarith
    have hsa : a < s ^ (-M.beta) * (M.S B).toReal :=
      hsub' ⟨by dsimp [s]; linarith, by dsimp [s]; linarith⟩
    have hlim := angularTailProb_mass_index_limit M hRV B hB hsub hboundary k hk hmass
      (by linarith : 0 < s)
    filter_upwards [hbracket.2 s hs, (tendsto_order.1 hlim).1 a hsa] with t ht hratio
    apply hratio.trans_le
    apply (div_le_div_iff_of_pos_right (tailProb_pos_of_regularVariation M hRV t)).2
    exact angularTailProb_antitone M B ht.le
  · intro a ha
    have hnear := (tendsto_order.1 hc).2 a ha
    obtain ⟨lo, hi, ⟨hlo, hhi⟩, hsub'⟩ := hnear.exists_Ioo_subset
    let s := (max lo 0 + 1) / 2
    have hlo' : max lo 0 < 1 := max_lt hlo (by norm_num)
    have hspos : 0 < s := by dsimp [s]; positivity
    have hsone : s < 1 := by dsimp [s]; linarith
    have hsa : s ^ (-M.beta) * (M.S B).toReal < a := by
      apply hsub'
      constructor
      · dsimp [s]; linarith [le_max_left lo 0]
      · linarith
    have hlim := angularTailProb_mass_index_limit M hRV B hB hsub hboundary k hk hmass hspos
    filter_upwards [hbracket.1 s hspos hsone, (tendsto_order.1 hlim).2 a hsa]
      with t ht hratio
    apply lt_of_le_of_lt _ hratio
    apply (div_le_div_iff_of_pos_right (tailProb_pos_of_regularVariation M hRV t)).2
    exact angularTailProb_antitone M B ht.le

/-- For [an angular set](hyp:B), [the relative-sphere frontier of its intersection with the positive l1 sphere is contained in its ordinary frontier](goal). -/
-- @node: relativeSphereFrontier_inter_subset
lemma relativeSphereFrontier_inter_subset (B : Set (Fin d → ℝ)) :
    relativeSphereFrontier l1Norm (B ∩ positiveSphere l1Norm) ⊆ frontier B := by
  intro u hu
  obtain ⟨v, hv, rfl⟩ := hu
  have heq : {v : {u : Fin d → ℝ // u ∈ positiveSphere l1Norm} |
      v.val ∈ B ∩ positiveSphere l1Norm} = Subtype.val ⁻¹' B := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, and_iff_left_iff_imp]
    exact fun _ => v.property
  rw [heq] at hv
  exact continuous_subtype_val.frontier_preimage_subset B hv

/-- For [an extreme-value model](hyp:M), if [its noise is regularly varying](hyp:hRV), then [the distribution of directions conditional on exceeding the threshold is a probability measure](goal). -/
-- @node: angular_law_probability
lemma angular_law_probability (M : ExtremeModel q d) (hRV : NoiseRegularlyVarying M) (t : ℝ) :
    IsProbabilityMeasure ((tailLaw M t).map (direction M)) := by
  have htail : M.mu {w | t < radius M w} ≠ 0 := by
    exact fun h => (tailProb_pos_of_regularVariation M hRV t).ne'
      (by simp only [tailProb, h, ENNReal.toReal_zero])
  have : IsProbabilityMeasure (tailLaw M t) := cond_isProbabilityMeasure htail
  exact Measure.isProbabilityMeasure_map (measurable_direction M).aemeasurable

/-- For [an extreme-value model](hyp:M), [a measurable angular set](hyp:hB), and [a radial threshold](hyp:t), [the conditional directional probability of the set equals its angular tail probability divided by the radial tail probability](goal). -/
-- @node: angular_law_real_apply
lemma angular_law_real_apply (M : ExtremeModel q d) (B : Set (Fin d → ℝ))
    (hB : MeasurableSet B) (t : ℝ) :
    (((tailLaw M t).map (direction M)) B).toReal = angularTailProb M B t / tailProb M t := by
  rw [Measure.map_apply (measurable_direction M) hB]
  rw [tailLaw, cond_apply (measurableSet_lt measurable_const (measurable_radius M))]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv]
  rw [div_eq_mul_inv, mul_comm]
  rfl

/-- For [an extreme-value model](hyp:M), [an angular set](hyp:B), and [a positive threshold](hyp:ht), [intersecting the set with the positive l1 sphere does not change its angular tail probability](goal). -/
-- @node: angularTailProb_inter_sphere
lemma angularTailProb_inter_sphere (M : ExtremeModel q d) (B : Set (Fin d → ℝ))
    {t : ℝ} (ht : 0 < t) :
    angularTailProb M (B ∩ positiveSphere l1Norm) t = angularTailProb M B t := by
  unfold angularTailProb
  congr 2
  ext w
  constructor
  · exact fun h => ⟨h.1, h.2.1⟩
  · exact fun h => ⟨h.1, h.2, direction_mem_positiveSphere M (ht.trans h.1)⟩

/-- For [an extreme-value model](hyp:M), if [its noise is regularly varying](hyp:hRV), [the angular set is measurable](hyp:hB), and [its frontier has zero spectral mass](hyp:hboundary), then [the conditional directional probability of the set converges to its spectral mass](goal). -/
-- @node: angular_law_continuity_set_limit
lemma angular_law_continuity_set_limit (M : ExtremeModel q d) (hRV : NoiseRegularlyVarying M)
    (B : Set (Fin d → ℝ)) (hB : MeasurableSet B) (hboundary : M.S (frontier B) = 0) :
    Tendsto (fun t => (((tailLaw M t).map (direction M)) B).toReal)
      atTop (𝓝 ((M.S B).toReal)) := by
  have hnull : M.S (relativeSphereFrontier l1Norm (B ∩ positiveSphere l1Norm)) = 0 :=
    measure_mono_null (relativeSphereFrontier_inter_subset B) hboundary
  have hsupport : M.S (B ∩ positiveSphere l1Norm) = M.S B := by
    apply measure_eq_measure_of_null_sdiff Set.inter_subset_left
    apply measure_mono_null _ hRV.2.2.spectral_support
    intro u hu
    exact fun hs => hu.2 ⟨hu.1, hs⟩
  have hlim := angularTailProb_ratio_limit M hRV (B ∩ positiveSphere l1Norm)
    (hB.inter measurableSet_positiveSphere_l1) Set.inter_subset_right hnull
  rw [hsupport] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [angular_law_real_apply M B hB, angularTailProb_inter_sphere M B ht]

/-- For [an extreme-value model](hyp:M), if [its noise is regularly varying](hyp:hRV), then [the conditional directional laws converge weakly to the spectral law](goal). -/
-- @node: angular_law_weak_limit
lemma angular_law_weak_limit (M : ExtremeModel q d) (hRV : NoiseRegularlyVarying M) :
    Tendsto (fun t => (⟨(tailLaw M t).map (direction M), angular_law_probability M hRV t⟩ :
      ProbabilityMeasure (Fin d → ℝ))) atTop
      (nhds (X := ProbabilityMeasure (Fin d → ℝ)) ⟨M.S, hRV.2.2.spectral_probability⟩) := by
  let laws : ℝ → ProbabilityMeasure (Fin d → ℝ) := fun t =>
    ⟨(tailLaw M t).map (direction M), angular_law_probability M hRV t⟩
  let limitLaw : ProbabilityMeasure (Fin d → ℝ) := ⟨M.S, hRV.2.2.spectral_probability⟩
  have : IsProbabilityMeasure M.S := hRV.2.2.spectral_probability
  have hsets : ∀ {B : Set (Fin d → ℝ)}, MeasurableSet B → M.S (frontier B) = 0 →
      Tendsto (fun t => (laws t : Measure (Fin d → ℝ)) B) atTop (𝓝 (M.S B)) := by
    intro B hB hnull
    have h := ENNReal.continuous_ofReal.tendsto ((M.S B).toReal) |>.comp
      (angular_law_continuity_set_limit M hRV B hB hnull)
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _)] at h
    apply h.congr'
    apply Eventually.of_forall
    intro t
    have := angular_law_probability M hRV t
    exact ENNReal.ofReal_toReal (measure_ne_top _ _)
  change Tendsto laws atTop (𝓝 limitLaw)
  apply tendsto_of_forall_isClosed_limsup_le
  intro F hF
  rw [← ENNReal.coe_le_coe, ENNReal.ofNNReal_limsup
    (isBoundedUnder_of_eventually_le (a := 1) (by simp))]
  have hright : (limitLaw F : ℝ≥0∞) = M.S F :=
    ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure limitLaw F
  rw [hright]
  simpa only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
    limsup_measure_closed_le_of_forall_tendsto_measure hsets F hF

/-- [The positive l1 sphere is compact](goal). -/
-- @node: isCompact_positiveSphere_l1
lemma isCompact_positiveSphere_l1 : IsCompact (positiveSphere (l1Norm (k := d))) := by
  have hcontinuous : Continuous (l1Norm (k := d)) := by
    unfold l1Norm
    fun_prop
  have hclosed : IsClosed (positiveSphere (l1Norm (k := d))) := by
    have ho : IsClosed (nonnegativeOrthant (k := d)) := by
      unfold nonnegativeOrthant
      simpa only [Set.ofPred_forall] using isClosed_iInter (fun i : Fin d =>
        isClosed_le continuous_const (continuous_apply i))
    exact ho.inter (isClosed_eq hcontinuous continuous_const)
  apply (isCompact_Icc : IsCompact (Set.Icc (0 : Fin d → ℝ) 1)).of_isClosed_subset hclosed
  intro u hu
  refine ⟨hu.1, fun i => ?_⟩
  have hi : |u i| ≤ l1Norm u := Finset.single_le_sum (fun j _ => abs_nonneg (u j))
    (Finset.mem_univ i)
  change u i ≤ 1
  simpa only [hu.2, abs_of_nonneg (hu.1 i)] using hi

/-- For [an extreme-value model](hyp:M) and [a positive threshold](hyp:ht), [conditional directions lie on the positive l1 sphere almost surely](goal). -/
-- @node: angular_law_ae_sphere
lemma angular_law_ae_sphere (M : ExtremeModel q d) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ s ∂((tailLaw M t).map (direction M)), s ∈ positiveSphere l1Norm := by
  apply (ae_map_iff (measurable_direction M).aemeasurable
    measurableSet_positiveSphere_l1).2
  exact ae_cond_of_forall_mem (measurableSet_lt measurable_const (measurable_radius M))
    (fun w hw => direction_mem_positiveSphere M (ht.trans hw))

/-- For [an extreme-value model](hyp:M), if [its noise is regularly varying](hyp:hRV), then [the spectral law lies on the positive l1 sphere almost surely](goal). -/
-- @node: spectral_ae_sphere
lemma spectral_ae_sphere (M : ExtremeModel q d) (hRV : NoiseRegularlyVarying M) :
    ∀ᵐ s ∂M.S, s ∈ positiveSphere l1Norm := by
  rw [ae_iff]
  exact hRV.2.2.spectral_support

end Papers.TbsExtremeEffects
