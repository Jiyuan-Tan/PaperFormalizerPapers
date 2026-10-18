module
public import Papers.TbsExtremeEffects.Helpers.JointRectangles

/-! Joint weak convergence from continuity rectangles. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology
variable {q d : ℕ}

/-- If [the noise is regularly varying](hyp:hRV), then [the radial-angular tail laws converge weakly to the product of a unit-scale Pareto radial law and the spectral angular law](goal).

@node: radialAngularLaw_weak_limit -/
lemma radialAngularLaw_weak_limit (M : ExtremeModel q d)
    (hRV : NoiseRegularlyVarying M) :
    Tendsto (fun t => (⟨radialAngularLaw M t, radialAngularLaw_probability M hRV t⟩ :
      ProbabilityMeasure (ℝ × (Fin d → ℝ)))) atTop
      (nhds (X := ProbabilityMeasure (ℝ × (Fin d → ℝ)))
        ⟨(paretoMeasure 1 M.beta).prod M.S, by
          let := hRV.2.2.spectral_probability
          let := isProbabilityMeasure_paretoMeasure (by norm_num : (0 : ℝ) < 1) hRV.1
          infer_instance⟩) := by
  let : IsProbabilityMeasure M.S := hRV.2.2.spectral_probability
  let : IsProbabilityMeasure (paretoMeasure 1 M.beta) :=
    isProbabilityMeasure_paretoMeasure (by norm_num) hRV.1
  let laws : ℝ → ProbabilityMeasure (ℝ × (Fin d → ℝ)) := fun t =>
    ⟨radialAngularLaw M t, radialAngularLaw_probability M hRV t⟩
  let target : ProbabilityMeasure (ℝ × (Fin d → ℝ)) :=
    ⟨(paretoMeasure 1 M.beta).prod M.S, inferInstance⟩
  -- Half-open radial intervals and angular continuity sets form a π-system.
  let P : Set (Set (ℝ × (Fin d → ℝ))) := {A | ∃ a b : ℝ,
    ∃ B : Set (Fin d → ℝ), MeasurableSet B ∧ M.S (frontier B) = 0 ∧
      A = Ioc a b ×ˢ B}
  have hP : IsPiSystem P := by
    rintro _ ⟨a, b, B, hB, hnB, rfl⟩ _ ⟨c, e, C, hC, hnC, rfl⟩ _
    refine ⟨max a c, min b e, B ∩ C, hB.inter hC, null_frontier_inter hnB hnC, ?_⟩
    rw [prod_inter_prod]
    congr 1
    ext r
    simp only [mem_inter_iff, mem_Ioc, max_lt_iff, le_min_iff]
    tauto
  change Tendsto laws atTop (𝓝 target)
  apply hP.tendsto_probabilityMeasure_of_tendsto_of_mem
  · rintro _ ⟨a, b, B, hB, _, rfl⟩
    exact measurableSet_Ioc.prod hB
  -- Angular thickenings have null frontier for arbitrarily small radii.
  · intro u hu x hxu
    obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.1 hu x hxu
    obtain ⟨r, hr, hn⟩ := exists_null_frontier_thickening M.S {x.2} hε
    simp only [thickening_singleton] at hn
    refine ⟨Ioc (x.1 - ε / 2) (x.1 + ε / 2) ×ˢ ball x.2 r,
      ⟨_, _, _, measurableSet_ball, hn, rfl⟩, ?_, ?_⟩
    · rw [nhds_prod_eq]
      exact Filter.prod_mem_prod (Ioc_mem_nhds (by linarith) (by linarith))
        (ball_mem_nhds _ hr.1)
    · apply Subset.trans _ hsub
      rw [← ball_prod_same]
      apply Set.prod_mono _ (ball_subset_ball hr.2.le)
      intro y hy
      rw [mem_ball, Real.dist_eq, abs_lt]
      change x.1 - ε / 2 < y ∧ y ≤ x.1 + ε / 2 at hy
      constructor <;> linarith
  · rintro _ ⟨a, b, B, hB, hnB, rfl⟩
    have hreal : Tendsto (fun t => (radialAngularLaw M t).real (Ioc a b ×ˢ B)) atTop
        (𝓝 (((paretoMeasure 1 M.beta).prod M.S).real (Ioc a b ×ˢ B))) := by
      by_cases hab : a ≤ b
      · exact radialAngularLaw_interval_product_limit M hRV B hB hnB hab
      · have hempty : Ioc a b = ∅ := Ioc_eq_empty_of_le (le_of_not_ge hab)
        simp only [hempty, empty_prod, measureReal_empty]
        exact tendsto_const_nhds
    have henn := ENNReal.continuous_ofReal.tendsto _ |>.comp hreal
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] at henn
    have henn' : Tendsto (fun t => (laws t : Measure _) (Ioc a b ×ˢ B)) atTop
        (𝓝 ((target : Measure _) (Ioc a b ×ˢ B))) := by
      apply henn.congr'
      apply Eventually.of_forall
      intro t
      let := radialAngularLaw_probability M hRV t
      exact ENNReal.ofReal_toReal (measure_ne_top _ _)
    apply ENNReal.tendsto_coe.1
    simpa only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using henn'

end Papers.TbsExtremeEffects
