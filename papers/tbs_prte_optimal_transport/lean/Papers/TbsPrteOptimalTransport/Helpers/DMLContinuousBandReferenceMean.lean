module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousFirstBandBias
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousBandIndicatorJoint
/-! Population regression centering for every continuous band.
Clipping supplies integrability of the residual products, including both moving
endpoint factors. The fitted gamma and assignment denominator may vary together. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: continuous_reference_band_regression_correction_zero
/-- Under [the model's structural assumptions](hyp:hStruct), [known outcome
endpoints](hyp:hend), and [admissibility of the true nuisance](hyp:he0), take
[measurable assignment denominators](hyp:hpi) that [are bounded below almost
everywhere by the clipping constant](hyp:hclip), where [that constant is
positive](hyp:hc), and a weight that [is measurable](hyp:hw) and [square
integrable](hyp:hw2). If [the treatment index is below the maximum](hyp:hk) and
[the band number is below the level's band count](hyp:hj), then [the weighted
band regression correction using true nuisances and these denominators is
integrable and has mean zero](goal). -/
lemma continuous_reference_band_regression_correction_zero
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (L : LevelData Z X) (he0 : ContAdmissible M L (trueNuisance M L))
    (pi : PositiveIndex L.K → X → ℝ) (hpi : ∀ i, Measurable (pi i))
    (c : ℝ) (hc : 0 < c) (hclip : ∀ i, ∀ᵐ x ∂xLaw M, c ≤ pi i x)
    (w : X → ℝ) (hw : Measurable w) (hw2 : MemLp w 2 (xLaw M))
    (k j : ℕ) (hk : k < L.K) (hj : j < L.l k) :
    Integrable (fun o : Obs X Z => w o.1 * continuousBandRegressionCorrection M L
      {trueNuisance M L with piLev := pi} k j o) (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 * continuousBandRegressionCorrection M L
      {trueNuisance M L with piLev := pi} k j o ∂observationLaw M) = 0 := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  have hboundary b (hb : b ≤ L.l k) :
      Measurable (bandBoundary M L k b) ∧ MemLp (bandBoundary M L k b) 2 (xLaw M) := by
    have heq : nuValue M (trueNuisance M L) k b = bandBoundary M L k b := by
      funext x
      exact population_nuValue_eq_bandBoundary M L k b hk hb x
    have hm : Measurable (nuValue M (trueNuisance M L) k b) := by
      fun_prop
    have hbound := continuous_admissible_nuValue_abs_bound M L _ he0 k b
    rw [heq] at hm hbound
    refine ⟨hm, MemLp.of_bound hm.aestronglyMeasurable (|M.yMin| + |M.yMax|) ?_⟩
    simpa only [Real.norm_eq_abs] using hbound
  obtain ⟨ha, ha2⟩ := hboundary j hj.le
  obtain ⟨hb, hb2⟩ := hboundary (j+1) (by omega)
  apply population_continuous_band_regression_correction_zero M L pi hpi
    k j hk hj ha hb w hw
  · intro plus
    exact population_IFJ_fitted_denominator_integrable M hStruct hend L pi hpi
      c hc hclip plus k j hk hj ha hb w hw (hw2.integrable (by norm_num))
  · intro plus
    exact population_IFM_fitted_denominator_integrable M L pi hpi c hc hclip
      plus k j hk hj.le ha _ (by fun_prop) (hw2.integrable_mul ha2)
  · intro plus
    exact population_IFM_fitted_denominator_integrable M L pi hpi c hc hclip
      plus k (j+1) hk (by omega) hb _ (by fun_prop) (hw2.integrable_mul hb2)

-- Neither fitted endpoint ordering nor an atomlessness assumption is needed
-- for this reduction. The nonlinear remainder retains the actual Ioc band.
-- @node: continuous_restored_band_regression_correction_nonlinear_mean
/-- Under [the structural assumptions](hyp:hStruct) and [known outcome
endpoints](hyp:hend), suppose [the fitted nuisance is admissible](hyp:he),
[truth is admissible](hyp:he0), [the clipping constant is positive](hyp:hc),
and [the fitted assignment denominators are at least that constant almost
everywhere](hyp:hclip). For [a treatment index below the maximum](hyp:hk) and
[a band number below the level's band count](hyp:hj), [the fitted-share-weighted
upper-minus-lower nonlinear boundary remainder is integrable, and its mean
equals the fitted-share-weighted regression correction mean after restoring
true band regressions; each remainder is the debiased boundary discrepancy
between true and fitted endpoints multiplied by its treatment-weighted
assignment indicator divided by the fitted denominator, with the lower term
zero at level zero](goal). -/
lemma continuous_restored_band_regression_correction_nonlinear_mean
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (he0 : ContAdmissible M L (trueNuisance M L))
    (c : ℝ) (hc : 0 < c) (hclip : ∀ i, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (g : RegularIndex L) (k j : ℕ) (hk : k < L.K) (hj : j < L.l k) :
    let h := continuousBandRegressionHybrid e (trueNuisance M L)
    let R := fun plus (o : Obs X Z) =>
      (if !plus && k == 0 then 0 else
        indicator (o.2.1 ∈ L.S (if plus then k+1 else k)) * o.2.2.1 /
          positiveValue e.piLev (if plus then k+1 else k) o.1) *
        continuousDebiasedBandBoundary
          (bandBoundary M L k j o.1) (bandBoundary M L k (j+1) o.1)
          (nuValue M h k j o.1) (nuValue M h k (j+1) o.1) o.2.2.2
    Integrable (fun o : Obs X Z => e.gamma g o.1 * (R true o - R false o))
      (observationLaw M) ∧
    (∫ o : Obs X Z, e.gamma g o.1 * continuousBandRegressionCorrection M L h k j o
      ∂observationLaw M) =
    (∫ o : Obs X Z, e.gamma g o.1 * (R true o - R false o) ∂observationLaw M) := by
  intro h R
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  let b := {trueNuisance M L with piLev := e.piLev}
  have hh := continuous_band_regression_hybrid_admissible M L e _ he he0
  have hpi : ∀ i, Measurable (e.piLev i) := by
    first | fun_prop | skip
    rcases he with ⟨_, _, _, _, _, hm, _⟩
    exact hm
  have hgm : Measurable (e.gamma g) := by
    first | fun_prop | skip
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hm, _⟩
    exact hm g
  have hg2 : MemLp (e.gamma g) 2 (xLaw M) := by
    have hg := fitted_continuous_regular_gamma_memLp M L e he g.val.1 g.val.2
    have heq : regularValue e.gamma g.val.1 g.val.2 = e.gamma g := by
      funext x
      simp only [regularValue, dif_pos g.property]
    rwa [heq] at hg
  have iD := fitted_continuous_weighted_band_regression_correction_integrable M L h hh
    c hc hclip g k j hk
  change Integrable (fun o : Obs X Z => e.gamma g o.1 *
    continuousBandRegressionCorrection M L h k j o) (observationLaw M) at iD
  obtain ⟨iB, zB⟩ := continuous_reference_band_regression_correction_zero M hStruct hend
    L he0 e.piLev hpi c hc hclip (e.gamma g) hgm hg2 k j hk hj
  let F := fun plus t (o : Obs X Z) =>
    (e.gamma g o.1 * (nuValue M h k t o.1 - bandBoundary M L k t o.1)) *
      IFM M L b plus k t o
  have hF plus t (ht : t ≤ L.l k) : Integrable (F plus t) (observationLaw M) ∧
      (∫ o, F plus t o ∂observationLaw M) = 0 := by
    have hn : Measurable (nuValue M h k t) := by fun_prop
    have hn0 : Measurable (nuValue M (trueNuisance M L) k t) := by fun_prop
    have heq : nuValue M (trueNuisance M L) k t = bandBoundary M L k t := by
      funext x
      exact population_nuValue_eq_bandBoundary M L k t hk ht x
    have hb : Measurable (bandBoundary M L k t) := heq ▸ hn0
    have hn2 : MemLp (nuValue M h k t) 2 (xLaw M) := by
      apply MemLp.of_bound hn.aestronglyMeasurable (|M.yMin| + |M.yMax|)
      simpa only [Real.norm_eq_abs] using continuous_admissible_nuValue_abs_bound M L h hh k t
    have hb2 : MemLp (bandBoundary M L k t) 2 (xLaw M) := by
      rw [← heq]
      apply MemLp.of_bound hn0.aestronglyMeasurable (|M.yMin| + |M.yMax|)
      simpa only [Real.norm_eq_abs] using continuous_admissible_nuValue_abs_bound M L _ he0 k t
    have hwi := hg2.integrable_mul (hn2.sub hb2)
    have hwm : Measurable (fun x => e.gamma g x *
        (nuValue M h k t x - bandBoundary M L k t x)) := by fun_prop
    have hi := population_IFM_fitted_denominator_integrable M L e.piLev hpi c hc hclip
      plus k t hk ht hb _ hwm hwi
    exact ⟨hi, population_IFM_fitted_denominator_weighted_zero M L e.piLev hpi
      plus k t hk ht hb _ hwm hi⟩
  obtain ⟨ipa, zpa⟩ := hF true j hj.le
  obtain ⟨ima, zma⟩ := hF false j hj.le
  obtain ⟨ipb, zpb⟩ := hF true (j+1) (by omega)
  obtain ⟨imb, zmb⟩ := hF false (j+1) (by omega)
  have heq (o : Obs X Z) : e.gamma g o.1 * continuousBandRegressionCorrection M L h k j o =
      e.gamma g o.1 * continuousBandRegressionCorrection M L b k j o +
      e.gamma g o.1 * (R true o - R false o) +
      (F true j o - F false j o) - (F true (j+1) o - F false (j+1) o) := by
    have hp := continuous_band_quantile_difference_residual_decomposition M L h b true
      rfl rfl rfl rfl rfl k j o
    have hm := continuous_band_quantile_difference_residual_decomposition M L h b false
      rfl rfl rfl rfl rfl k j o
    have hnb t (ht : t ≤ L.l k) : nuValue M b k t o.1 = bandBoundary M L k t o.1 :=
      population_nuValue_eq_bandBoundary M L k t hk ht o.1
    unfold continuousBandRegressionCorrection
    dsimp only [R, F]
    simp only [hnb j hj.le, hnb (j+1) (by omega)] at hp hm ⊢
    simp only [Bool.not_true, Bool.not_false, Bool.false_and, Bool.true_and,
      Bool.false_eq_true, Bool.true_eq, if_true, if_false] at hp hm ⊢
    linear_combination e.gamma g o.1 * hp - e.gamma g o.1 * hm
  have iR : Integrable (fun o : Obs X Z => e.gamma g o.1 * (R true o - R false o))
      (observationLaw M) := by
    apply ((((iD.sub' iB).sub' (ipa.sub' ima)).fun_add (ipb.sub' imb))).congr
    filter_upwards [] with o
    simp only [heq o]
    ring
  refine ⟨iR, ?_⟩
  simp_rw [heq]
  rw [integral_sub ((iB.fun_add iR).fun_add (ipa.sub' ima)) (ipb.sub' imb),
    integral_add (iB.fun_add iR) (ipa.sub' ima), integral_add iB iR,
    integral_sub ipa ima, integral_sub ipb imb, zB, zpa, zma, zpb, zmb]
  ring

-- @node: continuous_restored_band_regression_block_nonlinear_mean
/-- Assume [the structural assumptions](hyp:hStruct), [known outcome
endpoints](hyp:hend), [admissibility of the fitted nuisance](hyp:he),
[admissibility of truth](hyp:he0), [a positive clipping constant](hyp:hc), and
[fitted assignment denominators bounded below by that constant almost
everywhere](hyp:hclip). If [each treatment and band pair in the finite block
lies strictly below its corresponding maximum](hyp:ht), then [the sum of
fitted-share-weighted upper-minus-lower nonlinear boundary remainders is
integrable and has the same mean as the summed regression corrections after
restoring true band regressions; each remainder uses the true and fitted
endpoints and the treatment-weighted assignment indicator divided by the
fitted denominator, with the lower term zero at level zero](goal). -/
lemma continuous_restored_band_regression_block_nonlinear_mean
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (he0 : ContAdmissible M L (trueNuisance M L))
    (c : ℝ) (hc : 0 < c) (hclip : ∀ i, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (t : Finset ((ℕ × ℕ) × RegularIndex L))
    (ht : ∀ a ∈ t, a.1.1 < L.K ∧ a.1.2 < L.l a.1.1) :
    let h := continuousBandRegressionHybrid e (trueNuisance M L)
    let R := fun (a : (ℕ × ℕ) × RegularIndex L) plus (o : Obs X Z) =>
      (if !plus && a.1.1 == 0 then 0 else
        indicator (o.2.1 ∈ L.S (if plus then a.1.1+1 else a.1.1)) * o.2.2.1 /
          positiveValue e.piLev (if plus then a.1.1+1 else a.1.1) o.1) *
        continuousDebiasedBandBoundary
          (bandBoundary M L a.1.1 a.1.2 o.1) (bandBoundary M L a.1.1 (a.1.2+1) o.1)
          (nuValue M h a.1.1 a.1.2 o.1) (nuValue M h a.1.1 (a.1.2+1) o.1) o.2.2.2
    Integrable (fun o : Obs X Z => ∑ a ∈ t,
      e.gamma a.2 o.1 * (R a true o - R a false o)) (observationLaw M) ∧
    (∫ o : Obs X Z, ∑ a ∈ t, e.gamma a.2 o.1 *
      continuousBandRegressionCorrection M L h a.1.1 a.1.2 o ∂observationLaw M) =
    (∫ o : Obs X Z, ∑ a ∈ t, e.gamma a.2 o.1 * (R a true o - R a false o)
      ∂observationLaw M) := by
  intro h R
  have hh := continuous_band_regression_hybrid_admissible M L e _ he he0
  have hmean a (ha : a ∈ t) := continuous_restored_band_regression_correction_nonlinear_mean
    M hStruct hend L e he he0 c hc hclip a.2 a.1.1 a.1.2 (ht a ha).1 (ht a ha).2
  have hi a (ha : a ∈ t) : Integrable (fun o : Obs X Z =>
      e.gamma a.2 o.1 * (R a true o - R a false o)) (observationLaw M) := (hmean a ha).1
  have hreg a (ha : a ∈ t) : Integrable (fun o : Obs X Z => e.gamma a.2 o.1 *
      continuousBandRegressionCorrection M L h a.1.1 a.1.2 o) (observationLaw M) :=
    fitted_continuous_weighted_band_regression_correction_integrable M L h hh c hc hclip
      a.2 a.1.1 a.1.2 (ht a ha).1
  refine ⟨integrable_finsetSum t hi, ?_⟩
  rw [integral_finsetSum t hreg, integral_finsetSum t hi]
  apply Finset.sum_congr rfl
  intro a ha
  exact (hmean a ha).2

end Papers.TbsPrteOptimalTransport
