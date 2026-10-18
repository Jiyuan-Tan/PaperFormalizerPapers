module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousTreatmentResidual
/-! Exact expectations of fitted continuous full-interval product scores.
The signed instrument event is integrated using the true instrument kernel.
All four fitted residual corrections remain in the score expectation. -/
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

-- @node: fitted_continuous_full_event_mean
/-- For [admissible fitted nuisances](hyp:he), [the policy-minus-baseline
instrument indicator times the fitted full-interval contrast is integrable, and
its observation mean equals the covariate mean of the true instrument-probability
contrast times that fitted full-interval contrast](goal). -/
lemma fitted_continuous_full_event_mean (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e) (k : Fin L.K) :
    Integrable (fun o : Obs X Z =>
      (indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k)) *
        contFullJ L e k o.1) (observationLaw M) ∧
    (∫ o : Obs X Z,
      (indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k)) *
        contFullJ L e k o.1 ∂observationLaw M) =
      ∫ x, gammaFull M L k x * contFullJ L e k x ∂xLaw M := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  have hi := (fitted_continuous_full_event_memLp M L e he k).integrable (by norm_num)
  have hj := fitted_contFullJ_measurable M L e he k
  let f : Z × X → ℝ := fun zx =>
    (indicator (zx.1 ∈ higherPolicy L k) - indicator (zx.1 ∈ higherBaseline L k)) *
      contFullJ L e k zx.2
  have hf : Measurable f := by
    dsimp only [f]
    fun_prop
  have hsel (C : Finset Z) (x : X) :
      (∑ z, instProb M z x * indicator (z ∈ C)) = ∑ z ∈ C, instProb M z x := by
    simp only [indicator, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hs (x : X) : (∑ z, instProb M z x * f (z, x)) =
      gammaFull M L k x * contFullJ L e k x := by
    simp only [f, ← mul_assoc, ← Finset.sum_mul, mul_sub,
      Finset.sum_sub_distrib, hsel, gammaFull]
  exact ⟨hi, by simpa only [hs, f] using population_instrument_integral M f hf hi⟩

-- This is the expectation of the actual fitted product score, rather than
-- the expectation of its plug-in target alone.
-- @node: fitted_continuous_full_product_mean_decomposition
/-- For [admissible fitted nuisances](hyp:he), under [potential outcomes almost surely
in the outcome domain](hyp:hp), [consistency](hyp:hcons), [known outcome endpoints](hyp:hend),
[a positive denominator floor](hyp:hc), and [assignment probabilities bounded
below by that floor almost everywhere](hyp:hclip), [the fitted full-interval
product score is integrable and its mean equals the covariate mean of the true
instrument-probability contrast times the fitted full-interval contrast, plus
the upper weighted outcome residual, minus the lower weighted outcome residual,
plus the upper treatment correction, minus the lower treatment correction,
each averaged over observations](goal). -/
lemma fitted_continuous_full_product_mean_decomposition (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e)
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (k : Fin L.K) :
    Integrable (psiFullProd L e k) (observationLaw M) ∧
    (∫ o, psiFullProd L e k o ∂observationLaw M) =
      (∫ x, gammaFull M L k x * contFullJ L e k x ∂xLaw M) +
      (∫ o, e.gammaFull k o.1 * continuousFullOutcomeResidual L e true k o
        ∂observationLaw M) -
      (∫ o, e.gammaFull k o.1 * continuousFullOutcomeResidual L e false k o
        ∂observationLaw M) +
      (∫ o, (e.gammaFull k o.1 * fullValue e.JfullPlus k o.1) * RpCont L e (k.val+1) o
        ∂observationLaw M) -
      (∫ o, (e.gammaFull k o.1 * minusFullValue e k o.1) * RpCont L e k o
        ∂observationLaw M) := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  obtain ⟨hi, hm⟩ := fitted_continuous_full_event_mean M L e he k
  have ip := (fitted_continuous_weighted_full_residual_memLp M L e he hp hcons hend
    c hc hclip true k).integrable (by norm_num)
  have im := (fitted_continuous_weighted_full_residual_memLp M L e he hp hcons hend
    c hc hclip false k).integrable (by norm_num)
  have irp := (fitted_continuous_full_treatment_correction_memLp M L e he
    c hc hclip true k).integrable (by norm_num)
  have irm := (fitted_continuous_full_treatment_correction_memLp M L e he
    c hc hclip false k).integrable (by norm_num)
  simp only [Bool.false_eq_true, if_true, if_false] at irp irm
  refine ⟨(fitted_continuous_full_score_product_memLp M L e he hp hcons hend
    c hc hclip k).integrable (by norm_num), ?_⟩
  simp_rw [continuous_full_product_correction_decomposition]
  rw [integral_sub (((hi.fun_add ip).sub' im).fun_add irp) irm,
    integral_add ((hi.fun_add ip).sub' im) irp,
    integral_sub (hi.fun_add ip) im, integral_add hi ip, hm]

-- @node: true_continuous_full_product_mean
/-- In [a threshold-crossing model](hyp:h) with [level ordering invariant between
baseline and the specified alternative propensity](hyp:hOrder), [admissible true
nuisances](hyp:he), [potential outcomes in the outcome domain almost surely](hyp:hp), [consistency](hyp:hcons),
[known outcome endpoints](hyp:hend), and [baseline overlap](hyp:hov), [the true
full-interval product score is integrable and its observation mean equals the
covariate mean of the true instrument-probability contrast times the true
full-interval outcome contrast](goal). -/
lemma true_continuous_full_product_mean
    (h : ThresholdCrossing M) (q : Z → X → ℝ) (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop q L)
    (he : ContAdmissible M L (trueNuisance M L))
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (c : ℝ) (hov : BaselineOverlapWitness M L c) (k : Fin L.K) :
    Integrable (psiFullProd L (trueNuisance M L) k) (observationLaw M) ∧
    (∫ o, psiFullProd L (trueNuisance M L) k o ∂observationLaw M) =
      ∫ x, gammaFull M L k x * contFullJ L (trueNuisance M L) k x ∂xLaw M := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  have hclip (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, c ≤ (trueNuisance M L).piLev i x := by
    exact Eventually.of_forall (fun x => hov.2 x i i.property.1 i.property.2)
  have ip := (fitted_continuous_weighted_full_residual_memLp M L _ he hp hcons hend
    c hov.1 hclip true k).integrable (by norm_num)
  have im := (fitted_continuous_weighted_full_residual_memLp M L _ he hp hcons hend
    c hov.1 hclip false k).integrable (by norm_num)
  have irp := (fitted_continuous_full_treatment_correction_memLp M L _ he
    c hov.1 hclip true k).integrable (by norm_num)
  have irm := (fitted_continuous_full_treatment_correction_memLp M L _ he
    c hov.1 hclip false k).integrable (by norm_num)
  simp only [Bool.false_eq_true, if_true, if_false] at irp irm
  have hg := (fitted_continuous_gammaFull_coordinates M L _ he k).1
  have hz := (population_continuous_full_correction_weighted_zero M h q L hOrder
    k k.isLt ((trueNuisance M L).gammaFull k) hg ip im irp irm).2
  simp_rw [continuous_full_score_correction_decomposition, mul_sub, mul_add,
    ← mul_assoc] at hz
  rw [integral_sub ((ip.fun_add irp).sub' im) irm,
    integral_sub (ip.fun_add irp) im, integral_add ip irp] at hz
  obtain ⟨hi, hm⟩ := fitted_continuous_full_product_mean_decomposition M L _ he
    hp hcons hend c hov.1 hclip k
  refine ⟨hi, ?_⟩
  rw [hm]
  linear_combination hz

-- @node: true_continuous_full_block_mean
/-- In [a threshold-crossing model](hyp:h), under [invariant level ordering for
the specified alternative propensity](hyp:hOrder), [admissible true nuisances](hyp:he),
[potential outcomes in the outcome domain almost surely](hyp:hp), [consistency](hyp:hcons), [known outcome
endpoints](hyp:hend), and [baseline overlap](hyp:hov), [the sum of true
full-interval product scores over all levels is integrable and its observation
mean equals the covariate mean of the sum of true instrument-probability
contrasts times true full-interval outcome contrasts](goal). -/
lemma true_continuous_full_block_mean
    (h : ThresholdCrossing M) (q : Z → X → ℝ) (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop q L)
    (he : ContAdmissible M L (trueNuisance M L))
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (c : ℝ) (hov : BaselineOverlapWitness M L c) :
    Integrable (fun o => ∑ k : Fin L.K, psiFullProd L (trueNuisance M L) k o)
      (observationLaw M) ∧
    (∫ o, ∑ k : Fin L.K, psiFullProd L (trueNuisance M L) k o ∂observationLaw M) =
      ∫ x, ∑ k : Fin L.K,
        gammaFull M L k x * contFullJ L (trueNuisance M L) k x ∂xLaw M := by
  have hm k := true_continuous_full_product_mean M h q L hOrder he hp hcons hend c hov k
  have hi (k : Fin L.K) : Integrable
      (fun x => gammaFull M L k x * contFullJ L (trueNuisance M L) k x) (xLaw M) :=
    (fitted_continuous_gammaFull_memLp M L _ he k).integrable_mul
      (fitted_contFullJ_memLp M L _ he k)
  refine ⟨integrable_finsetSum _ (fun k _ => (hm k).1), ?_⟩
  rw [integral_finsetSum _ (fun k _ => (hm k).1),
    integral_finsetSum _ (fun k _ => hi k)]
  exact Finset.sum_congr rfl (fun k _ => (hm k).2)

end Papers.TbsPrteOptimalTransport
