module
public import Papers.TbsNeuralCausalPi.Helpers.HilbertSection
public import Papers.TbsNeuralCausalPi.Helpers.HilbertQuantile
public import Mathlib.MeasureTheory.Measure.OpenPos
/-! # Representing dominated laws by a time change of a uniform curve

This assembles the measurable first-hit lift and the quantile time change. The
remaining geometric input is a uniform, surjective Hölder curve.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped NNReal

-- @node: exists_hilbert_real_parameter_lift
/-- Suppose [a curve H](hyp:H) [is continuous on the closed unit interval](hyp:hH)
and [reaches every point of the target space there](hyp:hsurj).
For [a probability law P](hyp:P) and [a nonnegative constant c](hyp:c), if
[P dominates c times the uniform-time law of H](hyp:hdom), [there exists a probability
law rho assigning mass one to the unit interval, dominating c times uniform
unit-interval measure, and having image P under H](goal). -/
lemma exists_hilbert_real_parameter_lift {Y : Type*}
    [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (H : ℝ → Y) (hH : ContinuousOn H (Set.Icc (0 : ℝ) 1))
    (hsurj : Function.Surjective (fun t : Set.Icc (0 : ℝ) 1 => H t))
    (P : Measure Y) [IsProbabilityMeasure P] (c : ℝ≥0)
    (hdom : c • (volume.restrict (Set.Icc (0 : ℝ) 1)).map H ≤ P) :
    ∃ rho : Measure ℝ, IsProbabilityMeasure rho ∧
      rho (Set.Icc (0 : ℝ) 1) = 1 ∧
      c • volume.restrict (Set.Icc (0 : ℝ) 1) ≤ rho ∧ rho.map H = P := by
  let I := Set.Icc (0 : ℝ) 1
  let lam : Measure I := volume.comap Subtype.val
  have hlam : lam.map Subtype.val = volume.restrict I :=
    map_comap_subtype_coe measurableSet_Icc volume
  let : IsProbabilityMeasure lam := ⟨by
    have heq := congrArg (fun m : Measure ℝ => m Set.univ) hlam
    simpa [Measure.map_apply measurable_subtype_coe, I, Real.volume_Icc] using heq⟩
  let Hsub : I → Y := fun t => H t
  have hHsub : Measurable Hsub := by
    first | fun_prop | exact hH.domRestrict.measurable
  have hHa : AEMeasurable H (volume.restrict I) := by
    first | fun_prop | exact hH.aemeasurable measurableSet_Icc
  have hmap : lam.map Hsub = (volume.restrict I).map H := by
    rw [← hlam]
    exact (AEMeasurable.map_map_of_aemeasurable
      (by rwa [hlam]) measurable_subtype_coe.aemeasurable).symm
  obtain ⟨rhoI, hrhoI, hdomI, hpushI⟩ :=
    exists_hilbert_parameter_lift Hsub hH.domRestrict hsurj lam P c (by rwa [hmap])
  let : IsProbabilityMeasure rhoI := hrhoI
  let rho := rhoI.map Subtype.val
  have hrho : IsProbabilityMeasure rho := by
    dsimp [rho]
    exact Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
  have hmass : rho I = 1 := by
    dsimp [rho]
    rw [Measure.map_apply measurable_subtype_coe measurableSet_Icc]
    have hpre : ((↑) : I → ℝ) ⁻¹' I = Set.univ := by
      ext t
      simp
    rw [hpre, measure_univ]
  refine ⟨rho, hrho, hmass, ?_, ?_⟩
  · have hm := Measure.map_mono hdomI measurable_subtype_coe
    rwa [Measure.map_smul, hlam] at hm
  · have hHa' : AEMeasurable H rho := by
      have hrestrict : rho.restrict I = rho :=
        Measure.restrict_eq_self_of_ae_mem
          ((mem_ae_iff_prob_eq_one measurableSet_Icc).2 hmass)
      rw [← hrestrict]
      exact hH.aemeasurable measurableSet_Icc
    change (rhoI.map Subtype.val).map H = P
    rw [AEMeasurable.map_map_of_aemeasurable hHa' measurable_subtype_coe.aemeasurable]
    exact hpushI

-- @node: exists_representing_holder_curve_of_uniform_curve
/-- Let [H be a curve](hyp:H) with [nonnegative Hölder constant A and exponent r](hyp:A,r),
where [r is positive](hyp:hr). Suppose [H satisfies this Hölder bound on the closed
unit interval](hyp:hH) and [reaches every point of the target space there](hyp:hsurj).
For [a probability law P](hyp:P) and [a nonnegative constant c](hyp:c) that
[is positive](hyp:hc), if [P dominates c times the uniform-time law of H](hyp:hdom),
[there exists a continuous curve staying in H's unit-interval image, with uniform-time
law P, Hölder exponent r, and Hölder constant A times c to the power minus r](goal). -/
lemma exists_representing_holder_curve_of_uniform_curve {Y : Type*}
    [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (H : ℝ → Y) (A r : ℝ≥0) (hr : 0 < r)
    (hH : HolderOnWith A r H (Set.Icc (0 : ℝ) 1))
    (hsurj : Function.Surjective (fun t : Set.Icc (0 : ℝ) 1 => H t))
    (P : Measure Y) [IsProbabilityMeasure P] (c : ℝ≥0) (hc : 0 < c)
    (hdom : c • (volume.restrict (Set.Icc (0 : ℝ) 1)).map H ≤ P) :
    ∃ gamma : ℝ → Y, ContinuousOn gamma (Set.Icc (0 : ℝ) 1) ∧
      Set.MapsTo gamma (Set.Icc (0 : ℝ) 1)
        (H '' Set.Icc (0 : ℝ) 1) ∧
      (volume.restrict (Set.Icc (0 : ℝ) 1)).map gamma = P ∧
      HolderOnWith (A * c⁻¹ ^ (r : ℝ)) r gamma (Set.Icc (0 : ℝ) 1) := by
  obtain ⟨rho, hrho, hmass, hdomrho, hpush⟩ :=
    exists_hilbert_real_parameter_lift H (hH.continuousOn hr) hsurj P c hdom
  let : IsProbabilityMeasure rho := hrho
  obtain ⟨Q, hLip, hcont, hmem, hzero, hone, hQ⟩ :=
    exists_dominated_interval_reparameterization rho hmass c hc hdomrho
  have hholder : HolderOnWith (A * c⁻¹ ^ (r : ℝ)) r (H ∘ Q)
      (Set.Icc (0 : ℝ) 1) := by
    simpa only [mul_one] using hH.comp hLip.holderOnWith hmem
  refine ⟨H ∘ Q, hholder.continuousOn hr, ?_, ?_, hholder⟩
  · intro t ht
    exact ⟨Q t, hmem ht, rfl⟩
  · have hQmeas : AEMeasurable Q (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
      first | fun_prop | exact hcont.aemeasurable measurableSet_Icc
    have hHmeas : AEMeasurable H rho := by
      have hrestrict : rho.restrict (Set.Icc (0 : ℝ) 1) = rho :=
        Measure.restrict_eq_self_of_ae_mem
          ((mem_ae_iff_prob_eq_one measurableSet_Icc).2 hmass)
      rw [← hrestrict]
      exact (hH.continuousOn hr).aemeasurable measurableSet_Icc
    rw [← AEMeasurable.map_map_of_aemeasurable (by rwa [hQ]) hQmeas, hQ, hpush]

-- @node: continuous_interval_map_open_pos
/-- For [a curve gamma](hyp:gamma) [continuous on the closed unit interval](hyp:hgamma),
[a time t in that interval](hyp:ht), and [a target set U](hyp:U) that
[is open](hyp:hU) and [contains the curve's value at t](hyp:hmem),
[U has positive probability under the uniform-time law of gamma](goal). -/
lemma continuous_interval_map_open_pos {Y : Type*}
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (gamma : ℝ → Y) (hgamma : ContinuousOn gamma (Set.Icc (0 : ℝ) 1))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (U : Set Y) (hU : IsOpen U) (hmem : gamma t ∈ U) :
    0 < ((volume.restrict (Set.Icc (0 : ℝ) 1)).map gamma) U := by
  have hn := (hgamma t ht).preimage_mem_nhdsWithin (hU.mem_nhds hmem)
  obtain ⟨V, hV, hsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hn
  obtain ⟨O, hOV, hO, htO⟩ := mem_nhds_iff.mp hV
  have htclosure : t ∈ closure (Set.Ioo (0 : ℝ) 1) := by
    rwa [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  have hnonempty : (O ∩ Set.Ioo (0 : ℝ) 1).Nonempty :=
    mem_closure_iff.mp htclosure O hO htO
  have hpos := (hO.inter isOpen_Ioo).measure_pos volume hnonempty
  have hle : volume (O ∩ Set.Ioo (0 : ℝ) 1) ≤
      volume ((gamma ⁻¹' U) ∩ Set.Icc (0 : ℝ) 1) := by
    apply measure_mono
    intro x hx
    have hxI : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.2.1.le, hx.2.2.le⟩
    exact ⟨hsub ⟨hOV hx.1, hxI⟩, hxI⟩
  rw [Measure.map_apply_of_aemeasurable
    (by first | fun_prop | exact hgamma.aemeasurable measurableSet_Icc) hU.measurableSet,
    Measure.restrict_apply' measurableSet_Icc]
  exact hpos.trans_le hle

end Papers.TbsNeuralCausalPi
