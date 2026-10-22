module
public import Papers.TbsExtremeEffects.Helpers.JointTailLaw
public import Papers.TbsExtremeEffects.Helpers.ParetoRadial

/-! Continuity-set rectangle limits with the Pareto--spectral product as target.
Strict tail conditioning also handles radial endpoints below one. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
variable {q d : ℕ}

/-- For [a positive tail threshold](hyp:ht), [the radial-angular tail law is concentrated on radial coordinates strictly larger than one](goal).
@node: radialAngularLaw_ae_strict_radial_support -/
lemma radialAngularLaw_ae_strict_radial_support (M : ExtremeModel q d)
    {t : ℝ} (ht : 0 < t) :
    ∀ᵐ z ∂radialAngularLaw M t, 1 < z.1 := by
  apply (ae_map_iff (measurable_radialAngularMap M t).aemeasurable
    (measurableSet_lt measurable_const measurable_fst)).2
  filter_upwards [ae_cond_mem (μ := M.mu)
    (measurableSet_lt measurable_const (measurable_radius M))] with w hw
  change 1 < radius M w / t
  exact (lt_div_iff₀ ht).2 (by simpa using hw)

/-- For [a spectral set](hyp:B), [a positive tail threshold](hyp:ht), and [a radial cutoff](hyp:r), [replacing the cutoff by its maximum with one leaves this radial-angular tail probability unchanged](goal).
@node: radialAngularLaw_survival_clamp -/
lemma radialAngularLaw_survival_clamp (M : ExtremeModel q d)
    (B : Set (Fin d → ℝ)) {t : ℝ} (ht : 0 < t) (r : ℝ) :
    radialAngularLaw M t (Set.Ioi r ×ˢ B) =
      radialAngularLaw M t (Set.Ioi (max 1 r) ×ˢ B) := by
  apply measure_congr
  filter_upwards [radialAngularLaw_ae_strict_radial_support M ht] with z hz
  change (r < z.1 ∧ z.2 ∈ B) = (max 1 r < z.1 ∧ z.2 ∈ B)
  apply propext
  exact ⟨fun h => ⟨max_lt hz h.1, h.2⟩,
    fun h => ⟨(le_max_right 1 r).trans_lt h.1, h.2⟩⟩

/-- If [the Pareto shape parameter is positive](hyp:hb), then for [any radial cutoff](hyp:r), [the unit-scale Pareto survival probability equals the power of the cutoff clamped below at one](goal).
@node: pareto_unit_survival_all -/
lemma pareto_unit_survival_all {beta : ℝ} (hb : 0 < beta) (r : ℝ) :
    ((paretoMeasure 1 beta) (Set.Ioi r)).toReal = (max 1 r) ^ (-beta) := by
  let : IsProbabilityMeasure (paretoMeasure 1 beta) :=
    isProbabilityMeasure_paretoMeasure (by norm_num) hb
  by_cases hr : 1 ≤ r
  · rw [max_eq_right hr]
    exact pareto_unit_survival hb hr
  · rw [max_eq_left (le_of_not_ge hr), Real.one_rpow]
    have hunit := pareto_unit_survival hb (le_refl (1 : ℝ))
    simp only [Real.one_rpow] at hunit
    change (paretoMeasure 1 beta).real (Set.Ioi r) = 1
    apply le_antisymm
    · simpa only [measureReal_def, measure_univ, ENNReal.toReal_one] using
        (measureReal_mono (μ := paretoMeasure 1 beta) (Set.subset_univ (Set.Ioi r)))
    · change 1 ≤ (paretoMeasure 1 beta).real (Set.Ioi r)
      calc
        1 = (paretoMeasure 1 beta).real (Set.Ioi 1) := hunit.symm
        _ ≤ _ := measureReal_mono (μ := paretoMeasure 1 beta)
          (Set.Ioi_subset_Ioi (le_of_not_ge hr))

/-- Given [regularly varying noise](hyp:hRV), [a measurable spectral set](hyp:hB), [a spectral boundary of zero mass](hyp:hboundary), and [a radial cutoff](hyp:r), [the radial-angular tail probability converges to its Pareto--spectral product-law value](goal).
@node: radialAngularLaw_survival_product_limit -/
lemma radialAngularLaw_survival_product_limit (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (B : Set (Fin d → ℝ)) (hB : MeasurableSet B)
    (hboundary : M.S (frontier B) = 0) (r : ℝ) :
    Tendsto (fun t => ((radialAngularLaw M t) (Set.Ioi r ×ˢ B)).toReal) atTop
      (𝓝 (((paretoMeasure 1 M.beta).prod M.S) (Set.Ioi r ×ˢ B)).toReal) := by
  let : IsProbabilityMeasure M.S := hRV.2.2.spectral_probability
  rw [Measure.prod_prod, ENNReal.toReal_mul, pareto_unit_survival_all hRV.1]
  apply (radialAngularLaw_survival_continuity_set_limit M hRV B hB hboundary
    (le_max_left 1 r)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [radialAngularLaw_survival_clamp M B ht r]

/-- Given [regularly varying noise](hyp:hRV), [a measurable spectral set](hyp:hB), [a spectral boundary of zero mass](hyp:hboundary), and [ordered radial endpoints](hyp:hab), [the radial-angular rectangle probability converges to its Pareto--spectral product-law value](goal).
@node: radialAngularLaw_interval_product_limit -/
lemma radialAngularLaw_interval_product_limit (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) (B : Set (Fin d → ℝ)) (hB : MeasurableSet B)
    (hboundary : M.S (frontier B) = 0) {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun t => ((radialAngularLaw M t) (Set.Ioc a b ×ˢ B)).toReal) atTop
      (𝓝 (((paretoMeasure 1 M.beta).prod M.S) (Set.Ioc a b ×ˢ B)).toReal) := by
  let : IsProbabilityMeasure M.S := hRV.2.2.spectral_probability
  let : IsProbabilityMeasure (paretoMeasure 1 M.beta) :=
    isProbabilityMeasure_paretoMeasure (by norm_num) hRV.1
  have hset : Set.Ioc a b ×ˢ B = (Set.Ioi a ×ˢ B) \ (Set.Ioi b ×ˢ B) := by
    ext z
    simp only [Set.mem_prod, Set.mem_Ioc, Set.mem_Ioi, Set.mem_sdiff]
    constructor
    · intro h
      exact ⟨⟨h.1.1, h.2⟩, fun h' => (not_lt_of_ge h.1.2) h'.1⟩
    · intro h
      exact ⟨⟨h.1.1, le_of_not_gt (fun hb => h.2 ⟨hb, h.1.2⟩)⟩, h.1.2⟩
  have hsub : Set.Ioi b ×ˢ B ⊆ Set.Ioi a ×ˢ B :=
    fun z hz => ⟨hab.trans_lt hz.1, hz.2⟩
  have hlim := (radialAngularLaw_survival_product_limit M hRV B hB hboundary a).sub
    (radialAngularLaw_survival_product_limit M hRV B hB hboundary b)
  change Tendsto (fun t => (radialAngularLaw M t).real (Set.Ioc a b ×ˢ B)) atTop
    (𝓝 (((paretoMeasure 1 M.beta).prod M.S).real (Set.Ioc a b ×ˢ B)))
  have htarget := measureReal_sdiff (μ := (paretoMeasure 1 M.beta).prod M.S)
    hsub (measurableSet_Ioi.prod hB)
  rw [← hset] at htarget
  rw [htarget]
  apply hlim.congr'
  apply Eventually.of_forall
  intro t
  let := radialAngularLaw_probability M hRV t
  dsimp only
  rw [hset]
  exact (measureReal_sdiff hsub (measurableSet_Ioi.prod hB)).symm

/-- For [a finite collection of rectangles](hyp:I), [their lower endpoints](hyp:a), [upper endpoints](hyp:b), [heights](hyp:c), [spectral sets](hyp:B), [measurable spectral sets](hyp:hB), and [a finite measure](hyp:μ), [the integral of the rectangle step function equals the corresponding finite weighted sum of rectangle masses](goal).
@node: integral_rectangle_step -/
lemma integral_rectangle_step {ι : Type*} (I : Finset ι)
    (a b c : ι → ℝ) (B : ι → Set (Fin d → ℝ))
    (hB : ∀ i ∈ I, MeasurableSet (B i))
    (μ : Measure (ℝ × (Fin d → ℝ))) [IsFiniteMeasure μ] :
    (∫ z, ∑ i ∈ I, (Set.Ioc (a i) (b i) ×ˢ B i).indicator (fun _ => c i) z ∂μ) =
      ∑ i ∈ I, μ.real (Set.Ioc (a i) (b i) ×ˢ B i) * c i := by
  rw [integral_finsetSum I (fun i hi =>
    (integrable_const (c i)).indicator (measurableSet_Ioc.prod (hB i hi)))]
  apply Finset.sum_congr rfl
  intro i hi
  exact integral_indicator_const (c i) (measurableSet_Ioc.prod (hB i hi))

/-- Given [regularly varying noise](hyp:hRV), [ordered endpoints for every selected rectangle](hyp:hab), [measurable spectral sets](hyp:hB), and [zero spectral mass on every boundary](hyp:hboundary), [the expectation of the finite rectangle step function converges to its Pareto--spectral product-law expectation](goal).
@node: radialAngularLaw_rectangle_step_limit -/
lemma radialAngularLaw_rectangle_step_limit (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) {ι : Type*} (I : Finset ι)
    (a b c : ι → ℝ) (B : ι → Set (Fin d → ℝ))
    (hab : ∀ i ∈ I, a i ≤ b i) (hB : ∀ i ∈ I, MeasurableSet (B i))
    (hboundary : ∀ i ∈ I, M.S (frontier (B i)) = 0) :
    Tendsto (fun t => ∫ z,
      ∑ i ∈ I, (Set.Ioc (a i) (b i) ×ˢ B i).indicator (fun _ => c i) z
        ∂radialAngularLaw M t) atTop
      (𝓝 (∫ z, ∑ i ∈ I,
        (Set.Ioc (a i) (b i) ×ˢ B i).indicator (fun _ => c i) z
          ∂(paretoMeasure 1 M.beta).prod M.S)) := by
  let : IsProbabilityMeasure M.S := hRV.2.2.spectral_probability
  let : IsProbabilityMeasure (paretoMeasure 1 M.beta) :=
    isProbabilityMeasure_paretoMeasure (by norm_num) hRV.1
  rw [integral_rectangle_step I a b c B hB]
  have hlim := tendsto_finsetSum I (fun i hi =>
    (radialAngularLaw_interval_product_limit M hRV (B i) (hB i hi)
      (hboundary i hi) (hab i hi)).mul_const (c i))
  apply hlim.congr'
  apply Eventually.of_forall
  intro t
  let := radialAngularLaw_probability M hRV t
  exact (integral_rectangle_step I a b c B hB (radialAngularLaw M t)).symm

end Papers.TbsExtremeEffects
