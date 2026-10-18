module
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousFullBounds
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationContinuousFullDenominators
/-! Full-interval continuous moments with integrability derived from support and overlap. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: population_continuous_full_mean_of_clipped_denominator
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
and [invariant baseline and policy level ordering](hyp:hL), let [the replacement
assignment denominators be measurable](hyp:hpi), with [a positive floor](hyp:hc0)
[that bounds every denominator below almost surely](hyp:hcl). For [a level below
the total number of levels](hyp:hk) and [a measurable](hyp:hw), [integrable
covariate weight](hyp:hwi), [the weighted full-interval score with true regressions
and replacement denominators is integrable and has the same mean as the weighted
true full-interval regression contrast](goal). -/
lemma population_continuous_full_mean_of_clipped_denominator
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (pi : PositiveIndex L.K → X → ℝ) (hpi : ∀ a, Measurable (pi a))
    (c0 : ℝ) (hc0 : 0 < c0) (hcl : ∀ a, ∀ᵐ x ∂xLaw M, c0 ≤ pi a x)
    (k : ℕ) (hk : k < L.K)
    (w : X → ℝ) (hw : Measurable w) (hwi : Integrable w (xLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 *
      psiFullJ L {trueNuisance M L with piLev := pi} k o) (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 * psiFullJ L {trueNuisance M L with piLev := pi} k o
      ∂observationLaw M) =
      ∫ o : Obs X Z, w o.1 * contFullJ L (trueNuisance M L) k o.1 ∂observationLaw M := by
  have mp := population_continuous_full_mean_measurable M L true k
  have mm := population_continuous_full_mean_measurable M L false k
  have ip := population_continuous_full_mean_weight_integrable M h he L true k w hwi
  have im := population_continuous_full_mean_weight_integrable M h he L false k w hwi
  simp only [Bool.false_eq_true, if_true, if_false] at mp mm ip im
  exact population_continuous_full_fitted_denominator_weighted_mean M h.2.2.2.1 q L hL
    pi hpi k hk w hw
    (population_contFullJ_weighted_integrable M h he q L hL k w hw hwi)
    (population_continuous_full_outcome_fitted_denominator_integrable M h he L pi hpi
      c0 hc0 hcl true k hk w hw hwi)
    (population_continuous_full_outcome_fitted_denominator_integrable M h he L pi hpi
      c0 hc0 hcl false k hk w hw hwi)
    (population_RpCont_integrable_of_integrable_weight M h.2.2.2.1 q L hL pi hpi
      c0 hc0 hcl (k + 1) _ (hw.mul mp) ip)
    (population_RpCont_integrable_of_integrable_weight M h.2.2.2.1 q L hL pi hpi
      c0 hc0 hcl k _ (hw.mul mm) im)

-- @node: population_continuous_full_mean_from_overlap
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[invariant baseline and policy level ordering](hyp:hL), and [baseline overlap with
floor cpi](hyp:hov), take [a level below the total number of levels](hyp:hk) and
[a measurable](hyp:hw), [integrable covariate weight](hyp:hwi). Then [the weighted
true full-interval score is integrable and its mean equals the mean of the weighted
true full-interval regression contrast](goal). -/
lemma population_continuous_full_mean_from_overlap
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (k : ℕ) (hk : k < L.K)
    (w : X → ℝ) (hw : Measurable w) (hwi : Integrable w (xLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 * psiFullJ L (trueNuisance M L) k o)
      (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 * psiFullJ L (trueNuisance M L) k o ∂observationLaw M) =
      ∫ o : Obs X Z, w o.1 * contFullJ L (trueNuisance M L) k o.1 ∂observationLaw M := by
  have hpi a : Measurable ((trueNuisance M L).piLev a) :=
    population_instrument_set_probability_measurable M (L.S a.val)
  have hcl a : ∀ᵐ x ∂xLaw M, cpi ≤ (trueNuisance M L).piLev a x :=
    Eventually.of_forall (fun x => hov.2 x a.val a.property.1 a.property.2)
  exact population_continuous_full_mean_of_clipped_denominator M h he q L hL
    (trueNuisance M L).piLev hpi cpi hov.1 hcl k hk w hw hwi

-- @node: population_continuous_full_product_mean_from_overlap
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[invariant baseline and policy level ordering](hyp:hL), and [baseline overlap with
floor cpi](hyp:hov), take [a level below the total number of levels](hyp:hk) and
[a measurable](hyp:hw), [integrable covariate weight](hyp:hwi). Then [the weighted
true full-interval product score is integrable and its mean equals the mean of
the true full-interval regression contrast multiplied by the covariate weight
and the policy-minus-baseline assignment probability](goal). -/
lemma population_continuous_full_product_mean_from_overlap
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (k : ℕ) (hk : k < L.K)
    (w : X → ℝ) (hw : Measurable w) (hwi : Integrable w (xLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 * psiFullProd L (trueNuisance M L) k o)
      (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 * psiFullProd L (trueNuisance M L) k o ∂observationLaw M) =
      ∫ o : Obs X Z, (w o.1 * gammaFull M L k o.1) *
        contFullJ L (trueNuisance M L) k o.1 ∂observationLaw M := by
  have hg : Measurable (gammaFull M L k) := by
    first | fun_prop | skip
    exact (population_instrument_set_probability_measurable M _).sub
      (population_instrument_set_probability_measurable M _)
  have hgb : ∀ᵐ x ∂xLaw M, ‖gammaFull M L k x‖ ≤ 1 := by
    apply Eventually.of_forall
    intro x
    have ha := population_instrument_set_probability_range M (higherPolicy L k) x
    have hb := population_instrument_set_probability_range M (higherBaseline L k) x
    rw [Real.norm_eq_abs, abs_le]
    change -1 ≤ (∑ z ∈ higherPolicy L k, instProb M z x) -
        (∑ z ∈ higherBaseline L k, instProb M z x) ∧
      (∑ z ∈ higherPolicy L k, instProb M z x) -
        (∑ z ∈ higherBaseline L k, instProb M z x) ≤ 1
    constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
  have iwg : Integrable (fun x => w x * gammaFull M L k x) (xLaw M) := by
    simpa only [mul_comm] using hwi.bdd_mul hg.aestronglyMeasurable hgb
  obtain ⟨hs, hm⟩ := population_continuous_full_mean_from_overlap M h he q L hL cpi
    hov k hk (fun x => w x * gammaFull M L k x) (hw.mul hg) iwg
  have ib := population_contFullJ_weighted_integrable M h he q L hL k w hw hwi
  obtain ⟨hi, hz⟩ := population_continuous_full_product_assignment_zero M h.2.2.2.1
    q L hL k hk w hw
    (population_assignment_residual_weighted_integrable M (higherPolicy L k) _ ib)
    (population_assignment_residual_weighted_integrable M (higherBaseline L k) _ ib)
  have hgamma x : fullValue (trueNuisance M L).gammaFull k x = gammaFull M L k x := by
    simp only [fullValue, dif_pos hk, trueNuisance]
  simp only [hgamma] at hi hz
  simp only [psiFullProd, hgamma, mul_add, ← mul_assoc]
  refine ⟨hs.fun_add hi, ?_⟩
  rw [integral_add hs hi, hz, add_zero]
  exact hm

-- Both denominator and covariate-weight paths may vary; residual means stay zero.
-- @node: population_continuous_full_residual_path_from_clipping
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
and [invariant baseline and policy level ordering](hyp:hL), suppose [c0 is
positive](hyp:hc0) and [near zero the denominator path is measurable and bounded
below by c0 almost surely, while the covariate weight path is measurable and
integrable](hyp:hp). For [a level below the total number of levels](hyp:hk),
[the mean weighted difference between the full-interval score with true
regressions and moving denominators and the true regression contrast has
derivative zero at zero](goal). -/
lemma population_continuous_full_residual_path_from_clipping
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (pi : ℝ → PositiveIndex L.K → X → ℝ) (w : ℝ → X → ℝ)
    (c0 : ℝ) (hc0 : 0 < c0)
    (hp : ∀ᶠ t : ℝ in 𝓝 0, (∀ a, Measurable (pi t a)) ∧
      (∀ a, ∀ᵐ x ∂xLaw M, c0 ≤ pi t a x) ∧
      Measurable (w t) ∧ Integrable (w t) (xLaw M))
    (k : ℕ) (hk : k < L.K) :
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z, w t o.1 *
      (psiFullJ L {trueNuisance M L with piLev := pi t} k o -
        contFullJ L (trueNuisance M L) k o.1) ∂observationLaw M) 0 0 := by
  apply (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
  filter_upwards [hp] with t ht
  have hi := population_contFullJ_weighted_integrable M h he q L hL k
    (w t) ht.2.2.1 ht.2.2.2
  obtain ⟨hs, hm⟩ := population_continuous_full_mean_of_clipped_denominator M h he q L hL
    (pi t) ht.1 c0 hc0 ht.2.1 k hk (w t) ht.2.2.1 ht.2.2.2
  simp_rw [mul_sub]
  rw [integral_sub hs hi, hm, sub_self]

end Papers.TbsPrteOptimalTransport
