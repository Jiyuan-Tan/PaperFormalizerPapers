module
public import Papers.TbsExtremeEffects.Helpers.Hill.SurvivalFromDensity
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The radial survival derivative from the actual tail density law. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory Filter
open scoped ENNReal Topology

/-- If [the density is measurable](hyp:hf), [nonnegative above the cutoff](hyp:hpos), and
[matches the tail measure at that cutoff](hyp:hLaw), then [the density is integrable over the tail](goal).
@node: hill_tail_density_integrable -/
lemma hill_tail_density_integrable (nu : Measure ℝ) [IsFiniteMeasure nu]
    (f : ℝ → ℝ) {a : ℝ} (hf : Measurable f)
    (hpos : ∀ x > a, 0 ≤ f x)
    (hLaw : nu (Set.Ioi a) =
      (volume.withDensity (fun x => ENNReal.ofReal (f x))) (Set.Ioi a)) :
    IntegrableOn f (Set.Ioi a) := by
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi a)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hpos x hx
  apply (lintegral_ofReal_ne_top_iff_integrable
    hf.aestronglyMeasurable hnonneg).mp
  rw [← withDensity_apply _ measurableSet_Ioi, ← hLaw]
  exact measure_ne_top nu _

/-- If [the density is measurable](hyp:hf), [integrable above the cutoff](hyp:hi), the evaluation
point [lies above that cutoff](hyp:hr), and [the density is continuous there](hyp:hc), then the
tail integral [has derivative equal to minus the density](goal).
@node: hill_tail_integral_hasDerivAt -/
lemma hill_tail_integral_hasDerivAt (f : ℝ → ℝ) {a r : ℝ}
    (hf : Measurable f) (hi : IntegrableOn f (Set.Ioi a))
    (hr : a < r) (hc : ContinuousAt f r) :
    HasDerivAt (fun y => ∫ x : ℝ in Set.Ioi y, f x) (-f r) r := by
  have hFTC := intervalIntegral.integral_hasDerivAt_right
    (IntervalIntegrable.refl (f := f) (a := r))
    hf.stronglyMeasurable.stronglyMeasurableAtFilter hc
  have hlocal : (fun y => (∫ x : ℝ in Set.Ioi r, f x) - ∫ x in r..y, f x)
      =ᶠ[𝓝 r] (fun y => ∫ x : ℝ in Set.Ioi y, f x) := by
    filter_upwards [Ioi_mem_nhds hr] with y hy
    have hir := hi.mono_set (Set.Ioi_subset_Ioi hr.le)
    have hiy := hi.mono_set (Set.Ioi_subset_Ioi hy.le)
    have hdiff := intervalIntegral.integral_Ioi_sub_Ioi' hir hiy
    linarith
  exact (hFTC.const_sub _).congr_of_eventuallyEq hlocal.symm

/-- If [the density is measurable](hyp:hf), [nonnegative above the cutoff](hyp:hpos), and
[represents every tail probability above it](hyp:hLaw), then at a [point above the cutoff](hyp:hr)
where [the density is continuous](hyp:hc), the survival function [has derivative minus the density](goal).
@node: hill_survival_hasDerivAt_of_density -/
lemma hill_survival_hasDerivAt_of_density (nu : Measure ℝ) [IsFiniteMeasure nu]
    (f : ℝ → ℝ) {a r : ℝ} (hf : Measurable f)
    (hpos : ∀ x > a, 0 ≤ f x)
    (hLaw : ∀ x ≥ a, nu (Set.Ioi x) =
      (volume.withDensity (fun y => ENNReal.ofReal (f y))) (Set.Ioi x))
    (hr : a < r) (hc : ContinuousAt f r) :
    HasDerivAt (fun y => nu.real (Set.Ioi y)) (-f r) r := by
  have hi := hill_tail_density_integrable nu f hf hpos (hLaw a le_rfl)
  have hlocal : (fun y => nu.real (Set.Ioi y))
      =ᶠ[𝓝 r] (fun y => ∫ x : ℝ in Set.Ioi y, f x) := by
    filter_upwards [Ioi_mem_nhds hr] with y hy
    exact hill_tail_mass_eq_density_integral nu f hf
      (fun x hx => hpos x (hy.trans hx)) (hLaw y hy.le)
  exact (hill_tail_integral_hasDerivAt f hf hi hr hc).congr_of_eventuallyEq hlocal

/-- If [a density is measurable](hyp:hf) and [represents tail probabilities strictly above a cutoff](hyp:hLaw),
then at a [point above the cutoff](hyp:hr) where [the density is continuous](hyp:hc) and
[nonnegative](hyp:hfr), the survival function [has derivative minus that density](goal).
@node: hill_survival_hasDerivAt_of_tail_density -/
lemma hill_survival_hasDerivAt_of_tail_density (nu : Measure ℝ) [IsFiniteMeasure nu]
    (f : ℝ → ℝ) {a r : ℝ} (hf : Measurable f)
    (hLaw : ∀ x > a, nu (Set.Ioi x) =
      (volume.withDensity (fun y => ENNReal.ofReal (f y))) (Set.Ioi x))
    (hr : a < r) (hc : ContinuousAt f r) (hfr : 0 ≤ f r) :
    HasDerivAt (fun y => nu.real (Set.Ioi y)) (-f r) r := by
  let g : ℝ → ℝ := fun y => max (f y) 0
  have hg : Measurable g := by fun_prop
  have hgc : ContinuousAt g r := by
    fun_prop
  have hpositive : ∀ y > (a + r) / 2, 0 ≤ g y := fun y _ => le_max_right _ _
  have hglaw : ∀ x ≥ (a + r) / 2, nu (Set.Ioi x) =
      (volume.withDensity (fun y => ENNReal.ofReal (g y))) (Set.Ioi x) := by
    intro x hx
    rw [hLaw x (by linarith)]
    congr 2
    funext y
    simp [g, ENNReal.ofReal_max]
  have h := hill_survival_hasDerivAt_of_density nu g hg hpositive hglaw
    (by linarith : (a + r) / 2 < r) hgc
  simpa only [g, max_eq_left hfr] using h

end Papers.TbsExtremeEffects
