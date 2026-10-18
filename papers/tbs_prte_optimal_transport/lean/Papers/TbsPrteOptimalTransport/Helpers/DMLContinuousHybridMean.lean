module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousJointBlock
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousFullProductBias
/-! Exact centering with fitted denominators and true full-interval regressions.
Restoring the regressions leaves every residual correction centered even when
both the instrument probabilities and the signed product weights remain fitted. -/
public section
set_option linter.style.haveILetI false
set_option linter.style.openClassical false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: continuous_full_hybrid_admissible
/-- If [the true nuisance is admissible](hyp:he0) and [the fitted nuisance is
admissible](hyp:he), then [the hybrid retaining fitted assignment probabilities
and signed full-interval weights while using all other true coordinates is admissible](goal). -/
lemma continuous_full_hybrid_admissible (L : LevelData Z X) (e : NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L)) (he : ContAdmissible M L e) :
    ContAdmissible M L {trueNuisance M L with piLev := e.piLev, gammaFull := e.gammaFull} := by
  rcases he0 with ⟨h1, h2, h3, h4, _, _, h7, h8, h9, h10, _, _, hrest⟩
  rcases he with ⟨_, _, _, _, h5, h6, _, _, _, _, h11, h12, _⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hrest⟩

-- The selected conditional mean centers the outcome residual under any
-- measurable fitted denominator; no equality with the true denominator is used.
-- @node: continuous_full_hybrid_outcome_weighted_zero
/-- For [an admissible fitted nuisance](hyp:he) and [a measurable covariate weight](hyp:hw),
if [the weighted outcome residual using true regressions and fitted assignment
probabilities is integrable](hyp:hi), then [its expectation is zero](goal). -/
lemma continuous_full_hybrid_outcome_weighted_zero (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e)
    (plus : Bool) (k : Fin L.K) (w : X → ℝ) (hw : Measurable w)
    (hi : Integrable (fun o : Obs X Z => w o.1 * continuousFullOutcomeResidual L
      {trueNuisance M L with piLev := e.piLev, gammaFull := e.gammaFull} plus k o)
      (observationLaw M)) :
    (∫ o : Obs X Z, w o.1 * continuousFullOutcomeResidual L
      {trueNuisance M L with piLev := e.piLev, gammaFull := e.gammaFull} plus k o
      ∂observationLaw M) = 0 := by
  have hc i : Measurable (positiveValue e.piLev i) := by
    first | fun_prop | exact (fitted_continuous_assignment_coordinates M L e he i).1
  cases plus
  · by_cases hk0 : k.val = 0
    · simp [continuousFullOutcomeResidual, hk0]
    have hk1 : 1 ≤ k.val := by omega
    have heq : ∀ o : Obs X Z, continuousFullOutcomeResidual L
        {trueNuisance M L with piLev := e.piLev, gammaFull := e.gammaFull} false k o =
        indicator (o.2.1 ∈ L.S k) * o.2.2.1 / positiveValue e.piLev k o.1 *
          (o.2.2.2 - ∫ y, y ∂treatedLaw M L k o.1) := by
      intro o
      simp [continuousFullOutcomeResidual, minusFullValue, hk0, hk1, k.isLt,
        trueNuisance, treatedBandMean]
    simp_rw [heq] at hi ⊢
    exact population_selected_treatment_weighted_integral_zero M L k
      (fun _ y => y) measurable_snd _ w (hc k) hw hi
  · have heq : ∀ o : Obs X Z, continuousFullOutcomeResidual L
        {trueNuisance M L with piLev := e.piLev, gammaFull := e.gammaFull} true k o =
        indicator (o.2.1 ∈ L.S (k+1)) * o.2.2.1 / positiveValue e.piLev (k+1) o.1 *
          (o.2.2.2 - ∫ y, y ∂treatedLaw M L (k+1) o.1) := by
      intro o
      simp [continuousFullOutcomeResidual, fullValue, k.isLt, trueNuisance, treatedBandMean]
    simp_rw [heq] at hi ⊢
    exact population_selected_treatment_weighted_integral_zero M L (k+1)
      (fun _ y => y) measurable_snd _ w (hc (k+1)) hw hi

-- The structural conditional treatment mean centers the propensity residual
-- after pulling its fitted denominator into the instrument/covariate weight.
-- @node: continuous_full_hybrid_treatment_weighted_zero
/-- Under [threshold crossing](hyp:h) and [a covariate-invariant ordering of baseline
and policy propensity levels](hyp:hOrder), take [an admissible fitted nuisance](hyp:he),
[an index no larger than the level count](hyp:hk), and [a measurable covariate
weight](hyp:hw). If [the weighted treatment residual with true treatment means
and fitted assignment probabilities is integrable](hyp:hi), then [its expectation
is zero](goal). -/
lemma continuous_full_hybrid_treatment_weighted_zero (h : ThresholdCrossing M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hOrder : LevelOrderInvariant M.prop q L)
    (e : NuisanceCont L) (he : ContAdmissible M L e)
    (k : ℕ) (hk : k ≤ L.K) (w : X → ℝ) (hw : Measurable w)
    (hi : Integrable (fun o : Obs X Z => w o.1 * RpCont L
      {trueNuisance M L with piLev := e.piLev, gammaFull := e.gammaFull} k o)
      (observationLaw M)) :
    (∫ o : Obs X Z, w o.1 * RpCont L
      {trueNuisance M L with piLev := e.piLev, gammaFull := e.gammaFull} k o
      ∂observationLaw M) = 0 := by
  by_cases hk0 : k = 0
  · simp [RpCont, hk0]
  have hkp : 1 ≤ k ∧ k ≤ L.K := ⟨by omega, hk⟩
  let weight : Z × X → ℝ := fun zx =>
    w zx.2 * indicator (zx.1 ∈ L.S k) / positiveValue e.piLev k zx.2
  have hc : Measurable (positiveValue e.piLev k) := by
    first | fun_prop | exact (fitted_continuous_assignment_coordinates M L e he k).1
  have hm : Measurable weight := by
    dsimp only [weight]
    fun_prop
  have heq (o : Obs X Z) : w o.1 * RpCont L
      {trueNuisance M L with piLev := e.piLev, gammaFull := e.gammaFull} k o =
      weight (o.2.1, o.1) * (o.2.2.1 - M.prop o.2.1 o.1) := by
    simp only [RpCont, if_neg hk0, positiveValue, dif_pos hkp, trueNuisance, weight]
    by_cases hz : o.2.1 ∈ L.S k
    · have hp := (hOrder.2.2.2.2.2.1 o.1 k o.2.1 hk).mp hz
      rw [hp]
      ring
    · simp [indicator, hz]
  simp_rw [heq] at hi ⊢
  exact population_treatment_weighted_integral_zero M h weight hm hi

-- @node: continuous_full_hybrid_product_mean
/-- Assume [threshold crossing](hyp:h), [invariant ordering of baseline and policy
levels](hyp:hOrder), [admissibility of the true nuisance](hyp:he0), [admissibility
of the fitted nuisance](hyp:he), [potential-outcome support restrictions](hyp:hp),
[consistency](hyp:hcons), and [known outcome endpoints](hyp:hend). With [a positive
overlap bound](hyp:hc) and [fitted assignment probabilities almost surely above
it](hyp:hclip), [the hybrid product score using true regressions but fitted
assignment probabilities and signed weights is integrable and has expectation
equal to the covariate mean of the true signed weight times the true full-interval
contrast](goal). -/
lemma continuous_full_hybrid_product_mean (h : ThresholdCrossing M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hOrder : LevelOrderInvariant M.prop q L)
    (e : NuisanceCont L) (he0 : ContAdmissible M L (trueNuisance M L))
    (he : ContAdmissible M L e)
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (k : Fin L.K) :
    let b := {trueNuisance M L with piLev := e.piLev, gammaFull := e.gammaFull}
    Integrable (psiFullProd L b k) (observationLaw M) ∧
    (∫ o, psiFullProd L b k o ∂observationLaw M) =
      ∫ x, gammaFull M L k x * contFullJ L (trueNuisance M L) k x ∂xLaw M := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  dsimp only
  let b := {trueNuisance M L with piLev := e.piLev, gammaFull := e.gammaFull}
  have hb := continuous_full_hybrid_admissible M L e he0 he
  have hg := (fitted_continuous_gammaFull_coordinates M L e he k).1
  have ip := (fitted_continuous_weighted_full_residual_memLp M L b hb hp hcons hend
    c hc hclip true k).integrable (by norm_num)
  have im := (fitted_continuous_weighted_full_residual_memLp M L b hb hp hcons hend
    c hc hclip false k).integrable (by norm_num)
  have irp := (fitted_continuous_full_treatment_correction_memLp M L b hb
    c hc hclip true k).integrable (by norm_num)
  have irm := (fitted_continuous_full_treatment_correction_memLp M L b hb
    c hc hclip false k).integrable (by norm_num)
  simp only [Bool.false_eq_true, if_true, if_false] at irp irm
  have zp := continuous_full_hybrid_outcome_weighted_zero M L e he true k _ hg ip
  have zm := continuous_full_hybrid_outcome_weighted_zero M L e he false k _ hg im
  have hwp := hg.mul (population_continuous_full_mean_measurable M L true k)
  have hwm := hg.mul (population_continuous_full_mean_measurable M L false k)
  simp only [Bool.true_eq, if_true] at hwp
  simp only [Bool.false_eq_true, if_false] at hwm
  have zrp := continuous_full_hybrid_treatment_weighted_zero M h q L hOrder e he
    (k+1) (by omega) _ hwp irp
  have zrm := continuous_full_hybrid_treatment_weighted_zero M h q L hOrder e he
    k k.isLt.le _ hwm irm
  change (∫ o : Obs X Z, (b.gammaFull k o.1 * fullValue b.JfullPlus k o.1) *
    RpCont L b (k.val+1) o ∂observationLaw M) = 0 at zrp
  change (∫ o : Obs X Z, (b.gammaFull k o.1 * minusFullValue b k o.1) *
    RpCont L b k o ∂observationLaw M) = 0 at zrm
  obtain ⟨hi, hm⟩ := fitted_continuous_full_product_mean_decomposition M L b hb
    hp hcons hend c hc hclip k
  refine ⟨hi, ?_⟩
  rw [hm, zp, zm, zrp, zrm]
  simp only [add_zero, sub_zero]
  rfl

-- This identity concerns the expectation of the actual fitted score. Its
-- two terms are the already bounded joint regression error and product error.
-- @node: continuous_full_product_exact_bias_decomposition
/-- Under [threshold crossing](hyp:h), [invariant ordering of baseline and policy
levels](hyp:hOrder), [admissibility of the true nuisance](hyp:he0), [admissibility
of the fitted nuisance](hyp:he), [potential-outcome support restrictions](hyp:hp),
[consistency](hyp:hcons), [known outcome endpoints](hyp:hend), [a positive overlap
bound](hyp:hc), and [fitted assignment probabilities almost surely above it](hyp:hclip),
[the fitted product-score bias equals the mean fitted-weighted change from
restoring both regressions, minus the mean product of the signed-weight error
and the full-interval contrast error](goal). -/
lemma continuous_full_product_exact_bias_decomposition (h : ThresholdCrossing M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hOrder : LevelOrderInvariant M.prop q L)
    (e : NuisanceCont L) (he0 : ContAdmissible M L (trueNuisance M L))
    (he : ContAdmissible M L e)
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (k : Fin L.K) :
    let b := {trueNuisance M L with piLev := e.piLev, gammaFull := e.gammaFull}
    (∫ o, psiFullProd L e k o ∂observationLaw M) -
      (∫ x, gammaFull M L k x * contFullJ L (trueNuisance M L) k x ∂xLaw M) =
    (∫ o : Obs X Z, e.gammaFull k o.1 * (psiFullJ L e k o - psiFullJ L b k o)
      ∂observationLaw M) -
    (∫ x, (e.gammaFull k x - (trueNuisance M L).gammaFull k x) *
      (contFullJ L e k x - contFullJ L (trueNuisance M L) k x) ∂xLaw M) := by
  dsimp only
  let b := {trueNuisance M L with piLev := e.piLev, gammaFull := e.gammaFull}
  have hb := continuous_full_hybrid_admissible M L e he0 he
  have hm := (continuous_full_hybrid_product_mean M h q L hOrder e he0 he
    hp hcons hend c hc hclip k).2
  have iwe := fitted_continuous_weighted_full_component_integrable M L e he
    hp hcons hend c hc hclip k
  have iwb := fitted_continuous_weighted_full_component_integrable M L b hb
    hp hcons hend c hc hclip k
  let C := fun (s : NuisanceCont L) x => e.gammaFull k x * contFullJ L s k x
  have ic (s : NuisanceCont L) (hs : ContAdmissible M L s) :
      Integrable (C s) (xLaw M) :=
    (fitted_continuous_gammaFull_memLp M L e he k).integrable_mul
      (fitted_contFullJ_memLp M L s hs k)
  have mc (s : NuisanceCont L) (hs : ContAdmissible M L s) :=
    observationLaw_covariate_integral M (C s) (by
      dsimp only [C]
      first
      | fun_prop
      | exact (fitted_continuous_gammaFull_coordinates M L e he k).1.mul
          (fitted_contFullJ_measurable M L s hs k))
  have ico (s : NuisanceCont L) (hs : ContAdmissible M L s) :
      Integrable (fun o : Obs X Z => C s o.1) (observationLaw M) :=
    ((fitted_continuous_gammaFull_memLp M L e he k).comp_measurePreserving
      (observationLaw_fst_measurePreserving M)).integrable_mul
        ((fitted_contFullJ_memLp M L s hs k).comp_measurePreserving
          (observationLaw_fst_measurePreserving M))
  have mp (s : NuisanceCont L) (hs : ContAdmissible M L s)
      (hgamma : s.gammaFull = e.gammaFull)
      (iw : Integrable (fun o : Obs X Z => e.gammaFull k o.1 * psiFullJ L s k o)
        (observationLaw M)) :
      (∫ o, psiFullProd L s k o ∂observationLaw M) =
        (∫ x, gammaFull M L k x * contFullJ L s k x ∂xLaw M) +
        (∫ o : Obs X Z, e.gammaFull k o.1 * psiFullJ L s k o ∂observationLaw M) -
        ∫ x, C s x ∂xLaw M := by
    have heq (o : Obs X Z) : psiFullProd L s k o =
        (indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k)) *
          contFullJ L s k o.1 + e.gammaFull k o.1 * psiFullJ L s k o - C s o.1 := by
      simp only [psiFullProd, fullValue, dif_pos k.isLt, hgamma, C]
      ring
    simp_rw [heq]
    rw [integral_sub ((fitted_continuous_full_event_mean M L s hs k).1.fun_add iw)
      (ico s hs), integral_add (fitted_continuous_full_event_mean M L s hs k).1 iw,
      (fitted_continuous_full_event_mean M L s hs k).2, mc s hs]
  have pe := mp e he rfl iwe
  have pb := mp b hb rfl iwb
  have ig (s : NuisanceCont L) (hs : ContAdmissible M L s) :
      Integrable (fun x => gammaFull M L k x * contFullJ L s k x) (xLaw M) :=
    (fitted_continuous_gammaFull_memLp M L _ he0 k).integrable_mul
      (fitted_contFullJ_memLp M L s hs k)
  have cross : (∫ x, (e.gammaFull k x - (trueNuisance M L).gammaFull k x) *
      (contFullJ L e k x - contFullJ L (trueNuisance M L) k x) ∂xLaw M) =
      (∫ x, C e x ∂xLaw M) - (∫ x, C b x ∂xLaw M) -
      ((∫ x, gammaFull M L k x * contFullJ L e k x ∂xLaw M) -
        ∫ x, gammaFull M L k x * contFullJ L b k x ∂xLaw M) := by
    rw [← integral_sub (ic e he) (ic b hb), ← integral_sub (ig e he) (ig b hb),
      ← integral_sub ((ic e he).sub' (ic b hb)) ((ig e he).sub' (ig b hb))]
    apply integral_congr_ae
    filter_upwards [] with x
    change (e.gammaFull k x - gammaFull M L k x) *
      (contFullJ L e k x - contFullJ L b k x) = _
    dsimp only [C]
    ring
  rw [cross]
  simp only [mul_sub]
  rw [integral_sub iwe iwb]
  change (∫ o, psiFullProd L e k o ∂observationLaw M) - _ = _
  linear_combination pe - pb + hm

-- @node: fitted_continuous_full_product_bias_bound
/-- Suppose [threshold crossing holds](hyp:h), [baseline and policy levels have
invariant ordering](hyp:hOrder), [the true nuisance is admissible](hyp:he0), [the
fitted nuisance is admissible](hyp:he), [potential outcomes satisfy support
restrictions](hyp:hp), [consistency holds](hyp:hcons), and [outcome endpoints are
known](hyp:hend). With [a positive overlap bound](hyp:hc) and [fitted assignment
probabilities almost surely above it](hyp:hclip), [the absolute product-score bias
is at most the sum of the two adjacent assignment-probability L2 errors times
their treatment-propensity-weighted outcome-mean L2 errors, divided by the overlap
bound, plus the signed-weight L2 error times the contrast L2 error](goal). -/
lemma fitted_continuous_full_product_bias_bound (h : ThresholdCrossing M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hOrder : LevelOrderInvariant M.prop q L)
    (e : NuisanceCont L) (he0 : ContAdmissible M L (trueNuisance M L))
    (he : ContAdmissible M L e)
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (k : Fin L.K) :
    |(∫ o, psiFullProd L e k o ∂observationLaw M) -
      (∫ x, gammaFull M L k x * contFullJ L (trueNuisance M L) k x ∂xLaw M)| ≤
      finiteL2Error M (positiveValue e.piLev (k.val+1))
        (positiveValue (trueNuisance M L).piLev (k.val+1)) *
        finiteL2Error M (fun x => positiveValue e.pLev (k.val+1) x * fullValue e.JfullPlus k x)
          (fun x => positiveValue (trueNuisance M L).pLev (k.val+1) x *
            fullValue (trueNuisance M L).JfullPlus k x) / c +
      finiteL2Error M (positiveValue e.piLev k.val) (positiveValue (trueNuisance M L).piLev k.val) *
        finiteL2Error M (fun x => positiveValue e.pLev k.val x * minusFullValue e k x)
          (fun x => positiveValue (trueNuisance M L).pLev k.val x *
            minusFullValue (trueNuisance M L) k x) / c +
      finiteL2Error M (e.gammaFull k) ((trueNuisance M L).gammaFull k) *
        finiteL2Error M (contFullJ L e k) (contFullJ L (trueNuisance M L) k) := by
  rw [continuous_full_product_exact_bias_decomposition M h q L hOrder e he0 he
    hp hcons hend c hc hclip k]
  apply (abs_sub _ _).trans
  apply add_le_add
  · exact fitted_continuous_full_joint_regression_bias_bound M L e he0 he
      hp hcons hend c hc hclip k
  · apply le_trans _ (fitted_continuous_full_product_absolute_cross_error_bound M L
      (trueNuisance M L) e he0 he k).2
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (fun x => (e.gammaFull k x - (trueNuisance M L).gammaFull k x) *
        (contFullJ L e k x - contFullJ L (trueNuisance M L) k x))

end Papers.TbsPrteOptimalTransport
