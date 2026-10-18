module
public import Papers.TbsExtremeEffects.Helpers.WeightedContrast
public import Toolkit.Foundations.Probability.Independence.Conditioning

/-! Joint radial-angular tail probabilities and averaging over the independent covariate. -/

@[expose] public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
variable {q d : ℕ}

/-- For [a specified extreme-value model](hyp:M), [a threshold](hyp:t), and [an outcome](hyp:w), [the radial-angular map](goal) sends that outcome to its radius divided by the threshold and its angular direction.

@node: radialAngularMap -/
noncomputable def radialAngularMap (M : ExtremeModel q d) (t : ℝ) (w : M.Om) :
    ℝ × (Fin d → ℝ) := (radius M w / t, direction M w)

/-- For [a specified extreme-value model](hyp:M) and [a threshold](hyp:t), [the radial-angular law](goal) is the tail law at that threshold, expressed in radial-angular coordinates.

@node: radialAngularLaw -/
noncomputable def radialAngularLaw (M : ExtremeModel q d) (t : ℝ) :
    Measure (ℝ × (Fin d → ℝ)) := (tailLaw M t).map (radialAngularMap M t)

/-- [The radial-angular transformation is measurable](goal), so it can be used to push probability laws forward.

@node: measurable_radialAngularMap -/
@[fun_prop] lemma measurable_radialAngularMap (M : ExtremeModel q d) (t : ℝ) :
    Measurable (radialAngularMap M t) := by
  unfold radialAngularMap
  fun_prop

/-- If [the noise is regularly varying](hyp:hRV), [the radial-angular law is a probability measure](goal) at every threshold.

@node: radialAngularLaw_probability -/
lemma radialAngularLaw_probability (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (t : ℝ) : IsProbabilityMeasure (radialAngularLaw M t) := by
  let := tailLaw_probability M hRV t
  exact Measure.isProbabilityMeasure_map (measurable_radialAngularMap M t).aemeasurable

/-- If [the noise is regularly varying](hyp:hRV), [the angular set is measurable](hyp:hB), [lies on the positive unit sphere](hyp:hsub), and [its relative spherical boundary has zero spectral mass](hyp:hboundary), then [its tail probability at a scaled threshold, divided by the original tail probability, converges to the Pareto scaling times its spectral mass](goal), for [a positive scale factor](hyp:hr).

@node: angularTailProb_scaled_ratio_limit -/
lemma angularTailProb_scaled_ratio_limit (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (B : Set (Fin d → ℝ)) (hB : MeasurableSet B)
    (hsub : B ⊆ positiveSphere l1Norm)
    (hboundary : M.S (relativeSphereFrontier l1Norm B) = 0) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun t => angularTailProb M B (t * r) / tailProb M t) atTop
      (𝓝 (r ^ (-M.beta) * (M.S B).toReal)) := by
  have hscale : Tendsto (fun t : ℝ => t * r) atTop atTop :=
    (tendsto_mul_const_atTop_of_pos hr).mpr tendsto_id
  have h := ((angularTailProb_ratio_limit M hRV B hB hsub hboundary).comp hscale).mul
    (tailProb_ratio_limit M hRV hr)
  rw [mul_comm (M.S B).toReal] at h
  apply h.congr'
  exact Eventually.of_forall fun t => by
    dsimp only [Function.comp_def]
    field_simp [(tailProb_pos_of_regularVariation M hRV (t * r)).ne']

/-- For [a measurable angular set](hyp:hB), [a positive threshold](hyp:ht), and [a radial lower bound at least one](hyp:hr), [the radial-angular law of the corresponding survival rectangle equals the scaled angular tail probability divided by the tail probability](goal).

@node: radialAngularLaw_survival_rectangle -/
lemma radialAngularLaw_survival_rectangle (M : ExtremeModel q d)
    (B : Set (Fin d → ℝ)) (hB : MeasurableSet B) {t r : ℝ}
    (ht : 0 < t) (hr : 1 ≤ r) :
    ((radialAngularLaw M t) (Set.Ioi r ×ˢ B)).toReal =
      angularTailProb M B (t * r) / tailProb M t := by
  rw [radialAngularLaw, Measure.map_apply (measurable_radialAngularMap M t)
    (measurableSet_Ioi.prod hB), tailLaw,
    cond_apply (measurableSet_lt measurable_const (measurable_radius M))]
  have hset : {w | t < radius M w} ∩
      radialAngularMap M t ⁻¹' (Set.Ioi r ×ˢ B) =
      {w | t * r < radius M w ∧ direction M w ∈ B} := by
    ext w
    change (t < radius M w ∧ r < radius M w / t ∧ direction M w ∈ B) ↔ _
    rw [lt_div_iff₀ ht, mul_comm r t]
    have htr : t ≤ t * r := by nlinarith
    exact ⟨fun h => h.2, fun h => ⟨htr.trans_lt h.1, h⟩⟩
  rw [hset, ENNReal.toReal_mul, ENNReal.toReal_inv]
  simp only [angularTailProb, tailProb, div_eq_mul_inv, mul_comm]

/-- If [the noise is regularly varying](hyp:hRV), [the angular set is measurable](hyp:hB), [is contained in the positive unit sphere](hyp:hsub), and [has zero spectral mass on its relative spherical boundary](hyp:hboundary), then [the probability of its radial survival rectangle converges to its Pareto-scaled spectral mass](goal), for [a radial lower bound at least one](hyp:hr).

@node: radialAngularLaw_survival_rectangle_limit -/
lemma radialAngularLaw_survival_rectangle_limit (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (B : Set (Fin d → ℝ)) (hB : MeasurableSet B)
    (hsub : B ⊆ positiveSphere l1Norm)
    (hboundary : M.S (relativeSphereFrontier l1Norm B) = 0) {r : ℝ} (hr : 1 ≤ r) :
    Tendsto (fun t => ((radialAngularLaw M t) (Set.Ioi r ×ˢ B)).toReal) atTop
      (𝓝 (r ^ (-M.beta) * (M.S B).toReal)) := by
  apply (angularTailProb_scaled_ratio_limit M hRV B hB hsub hboundary
    (by linarith : 0 < r)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact (radialAngularLaw_survival_rectangle M B hB ht hr).symm

/-- At [a positive threshold](hyp:ht), [radial-angular draws lie almost surely above radial level one and on the positive unit sphere](goal).

@node: radialAngularLaw_ae_support -/
lemma radialAngularLaw_ae_support (M : ExtremeModel q d) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ z ∂radialAngularLaw M t, 1 ≤ z.1 ∧ z.2 ∈ positiveSphere l1Norm := by
  apply (ae_map_iff (measurable_radialAngularMap M t).aemeasurable
    ((measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_positiveSphere_l1.preimage measurable_snd))).2
  filter_upwards [scaled_radius_ge_one_tailLaw M ht,
    ae_cond_mem (μ := M.mu) (measurableSet_lt measurable_const (measurable_radius M))]
    with w hrad hw
  exact ⟨hrad, direction_mem_positiveSphere M (ht.trans hw)⟩

/-- If [the noise is regularly varying](hyp:hRV), [the angular set is measurable](hyp:hB), [its ordinary boundary has zero spectral mass](hyp:hboundary), and [the radial lower bound is at least one](hyp:hr), then [the radial-angular probability of the survival rectangle converges to the Pareto-scaled spectral mass of that set](goal). Ambient angular continuity sets need not themselves be subsets of the sphere.

@node: radialAngularLaw_survival_continuity_set_limit -/
lemma radialAngularLaw_survival_continuity_set_limit (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (B : Set (Fin d → ℝ)) (hB : MeasurableSet B)
    (hboundary : M.S (frontier B) = 0) {r : ℝ} (hr : 1 ≤ r) :
    Tendsto (fun t => ((radialAngularLaw M t) (Set.Ioi r ×ˢ B)).toReal) atTop
      (𝓝 (r ^ (-M.beta) * (M.S B).toReal)) := by
  have hnull : M.S (relativeSphereFrontier l1Norm (B ∩ positiveSphere l1Norm)) = 0 :=
    measure_mono_null (relativeSphereFrontier_inter_subset B) hboundary
  have hsupport : M.S (B ∩ positiveSphere l1Norm) = M.S B := by
    apply measure_eq_measure_of_null_sdiff Set.inter_subset_left
    apply measure_mono_null _ hRV.2.2.spectral_support
    intro u hu
    exact fun hs => hu.2 ⟨hu.1, hs⟩
  have hlim := radialAngularLaw_survival_rectangle_limit M hRV (B ∩ positiveSphere l1Norm)
    (hB.inter measurableSet_positiveSphere_l1) Set.inter_subset_right hnull hr
  rw [hsupport] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [radialAngularLaw_survival_rectangle M _ (hB.inter measurableSet_positiveSphere_l1) ht hr,
    angularTailProb_inter_sphere M B (ht.trans_le (by nlinarith : t ≤ t * r)),
    radialAngularLaw_survival_rectangle M B hB ht hr]

/-- If [the noise is regularly varying](hyp:hRV), [the angular set is measurable](hyp:hB), [its ordinary boundary has zero spectral mass](hyp:hboundary), [the lower radial endpoint is at least one](hyp:ha), and [the interval endpoints are ordered](hyp:hab), then [the probability of the radial-angular half-open rectangle converges to the difference of Pareto survival factors times its spectral mass](goal).

@node: radialAngularLaw_interval_rectangle_limit -/
lemma radialAngularLaw_interval_rectangle_limit (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (B : Set (Fin d → ℝ)) (hB : MeasurableSet B)
    (hboundary : M.S (frontier B) = 0) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    Tendsto (fun t => ((radialAngularLaw M t) (Set.Ioc a b ×ˢ B)).toReal) atTop
      (𝓝 ((a ^ (-M.beta) - b ^ (-M.beta)) * (M.S B).toReal)) := by
  have hlim := (radialAngularLaw_survival_continuity_set_limit M hRV B hB hboundary ha).sub
    (radialAngularLaw_survival_continuity_set_limit M hRV B hB hboundary (ha.trans hab))
  rw [← sub_mul] at hlim
  apply hlim.congr'
  apply Eventually.of_forall
  intro t
  let := radialAngularLaw_probability M hRV t
  have hset : Set.Ioc a b ×ˢ B = (Set.Ioi a ×ˢ B) \ (Set.Ioi b ×ˢ B) := by
    ext z
    simp only [Set.mem_prod, Set.mem_Ioc, Set.mem_Ioi, Set.mem_sdiff]
    constructor
    · intro h
      exact ⟨⟨h.1.1, h.2⟩, fun h' => (not_lt_of_ge h.1.2) h'.1⟩
    · intro h
      exact ⟨⟨h.1.1, le_of_not_gt (fun hb => h.2 ⟨hb, h.1.2⟩)⟩, h.1.2⟩
  rw [hset]
  symm
  exact measureReal_sdiff (fun z hz => ⟨hab.trans_lt hz.1, hz.2⟩)
    (measurableSet_Ioi.prod hB)

/-- If [the noise is regularly varying](hyp:hRV) and [is independent of the covariate](hyp:hNoise), then [the joint tail law of the covariate and radial-angular coordinates factors into their marginal laws](goal).

@node: covariate_radialAngular_tail_pair_law -/
lemma covariate_radialAngular_tail_pair_law (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M) (t : ℝ) :
    (tailLaw M t).map (fun w => (M.X w, radialAngularMap M t w)) =
      (M.mu.map M.X).prod (radialAngularLaw M t) := by
  have hpos : M.mu (M.U ⁻¹' {u | t < l1Norm u}) ≠ 0 := by
    intro h
    change M.mu {w | t < radius M w} = 0 at h
    exact (tailProb_pos_of_regularVariation M hRV t).ne'
      (by simp only [tailProb, h, ENNReal.toReal_zero])
  have hset : MeasurableSet {u : Fin d → ℝ | t < l1Norm u} :=
    measurableSet_lt measurable_const measurable_l1Norm
  have hlaw := Toolkit.Foundations.Probability.Independence.map_prodMk_cond_preimage_eq_prod M.mu M.X M.U M.measurable_X M.measurable_U
    (covariate_noise_independent M hNoise) _ hset hpos
  let T : (Fin d → ℝ) → ℝ × (Fin d → ℝ) :=
    fun u => (l1Norm u / t, fun i => u i / l1Norm u)
  have hT : Measurable T := by fun_prop
  have hmap := congrArg (fun ν => ν.map (Prod.map id T)) hlaw
  rw [Measure.map_map (measurable_id.prodMap hT) (M.measurable_X.prodMk M.measurable_U),
    ← Measure.map_prod_map _ _ measurable_id hT, Measure.map_id,
    Measure.map_map hT M.measurable_U] at hmap
  exact hmap

/-- If [the noise is regularly varying](hyp:hRV), [independent of the covariate](hyp:hNoise), [the covariate is bounded](hyp:hX), [the model is asymptotically homogeneous](hyp:hHom), [the homogeneity exponent is below the tail exponent](hyp:hAlpha), and [the bounded continuous function](hyp:H) [equals the treated-minus-untreated model contrast for every covariate in the model ball and every positive unit direction](hyp:hH), then [the weighted angular contrast average equals the corresponding joint radial-angular average](goal). Independence removes the covariate coordinate before taking the joint tail limit.

@node: weightedAngularContrast_eq_joint_average -/
lemma weightedAngularContrast_eq_joint_average (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M)
    (hX : CovariateBounded M) (hHom : AsymptoticHomogeneity M)
    (hAlpha : M.alpha < M.beta)
    (H : BoundedContinuousFunction ((Fin q → ℝ) × (Fin d → ℝ)) ℝ)
    (hH : ∀ x, l1Norm x ≤ M.R → ∀ s ∈ positiveSphere l1Norm,
      H (x, s) = M.g x true s - M.g x false s) :
    ∀ᶠ t in atTop, (∫ w, weightedAngularContrast M t w ∂tailLaw M t) =
      ∫ z, (∫ x, H (x, z.2) ∂M.mu.map M.X) * z.1 ^ M.alpha ∂radialAngularLaw M t := by
  filter_upwards [weightedAngularContrast_eventually_integrable M hRV hX hHom hAlpha,
    eventually_gt_atTop (0 : ℝ)] with t hInt ht
  let F : (Fin q → ℝ) × (ℝ × (Fin d → ℝ)) → ℝ :=
    fun z => H (z.1, z.2.2) * z.2.1 ^ M.alpha
  have hF : Measurable F := by fun_prop
  have heq : weightedAngularContrast M t =ᵐ[tailLaw M t]
      (fun w => F (M.X w, radialAngularMap M t w)) := by
    filter_upwards [weightedAngularContrast_ae_extension M hX H hH ht,
      scaled_radius_ge_one_tailLaw M ht] with w hw hrad
    have hr : 0 ≤ radius M w := by
      have := (le_div_iff₀ ht).mp hrad
      linarith
    simpa only [F, radialAngularMap, Real.div_rpow hr ht.le] using hw
  have hpair : Measurable (fun w => (M.X w, radialAngularMap M t w)) := by
    have hx := M.measurable_X
    fun_prop
  have hMap := (integrable_map_measure hF.aestronglyMeasurable hpair.aemeasurable).mpr
    (hInt.congr heq)
  rw [covariate_radialAngular_tail_pair_law M hRV hNoise t] at hMap
  let := radialAngularLaw_probability M hRV t
  let : IsProbabilityMeasure (M.mu.map M.X) :=
    Measure.isProbabilityMeasure_map M.measurable_X.aemeasurable
  calc
    _ = ∫ w, F (M.X w, radialAngularMap M t w) ∂tailLaw M t := integral_congr_ae heq
    _ = ∫ z, F z ∂(M.mu.map M.X).prod (radialAngularLaw M t) := by
      rw [← integral_map hpair.aemeasurable hF.aestronglyMeasurable,
        covariate_radialAngular_tail_pair_law M hRV hNoise t]
    _ = ∫ z, (∫ x, F (x, z) ∂M.mu.map M.X) ∂radialAngularLaw M t :=
      integral_prod_symm F hMap
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => integral_mul_const (z.1 ^ M.alpha) _

/-- If [the noise is regularly varying](hyp:hRV), [independent of the covariate](hyp:hNoise), [the covariate is bounded](hyp:hX), [the model is asymptotically homogeneous](hyp:hHom), [the homogeneity exponent is below the tail exponent](hyp:hAlpha), [the contrast represents the treatment difference on the relevant domain](hyp:hH), and [the joint radial-angular average converges to the stated limit](hyp:hJoint), then [the weighted angular contrast average converges to that same limit](goal).

@node: weightedAngularContrast_tendsto_of_joint_average -/
lemma weightedAngularContrast_tendsto_of_joint_average (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M)
    (hX : CovariateBounded M) (hHom : AsymptoticHomogeneity M)
    (hAlpha : M.alpha < M.beta)
    (H : BoundedContinuousFunction ((Fin q → ℝ) × (Fin d → ℝ)) ℝ)
    (hH : ∀ x, l1Norm x ≤ M.R → ∀ s ∈ positiveSphere l1Norm,
      H (x, s) = M.g x true s - M.g x false s) {l : ℝ}
    (hJoint : Tendsto (fun t =>
      ∫ z, (∫ x, H (x, z.2) ∂M.mu.map M.X) * z.1 ^ M.alpha ∂radialAngularLaw M t)
      atTop (𝓝 l)) :
    Tendsto (fun t => ∫ w, weightedAngularContrast M t w ∂tailLaw M t) atTop (𝓝 l) := by
  apply hJoint.congr'
  exact (weightedAngularContrast_eq_joint_average M hRV hNoise hX hHom hAlpha H hH).mono
    fun _ h => h.symm

/-- If [the noise is regularly varying](hyp:hRV), [independent of the covariate](hyp:hNoise), [the covariate is bounded](hyp:hX), [the model is asymptotically homogeneous](hyp:hHom), and [the homogeneity exponent is zero](hyp:hz), then [the weighted angular contrast average converges to the angular target times the stated tail-moment factor](goal). Zero homogeneity exponent reduces the weighted limit to the proved angular limit.

@node: weightedAngularContrast_tendsto_of_alpha_zero -/
lemma weightedAngularContrast_tendsto_of_alpha_zero (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M)
    (hX : CovariateBounded M) (hHom : AsymptoticHomogeneity M)
    (hz : M.alpha = 0) :
    Tendsto (fun t => ∫ w, weightedAngularContrast M t w ∂tailLaw M t) atTop
      (𝓝 (etaTarget M * (M.beta / (M.beta - M.alpha)))) := by
  have hAngular := angularFactor_tendsto_etaTarget M hRV hNoise hX hHom
  have heq : (fun t => ∫ w, weightedAngularContrast M t w ∂tailLaw M t) =
      angularFactor M := by
    funext t
    simp only [weightedAngularContrast, angularFactor, hz, Real.rpow_zero, div_self one_ne_zero,
      mul_one]
  rw [heq, hz, sub_zero, div_self hRV.1.ne', mul_one]
  exact hAngular

end Papers.TbsExtremeEffects
