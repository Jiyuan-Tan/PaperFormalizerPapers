module
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousTailAdmissibleDerivative
public import Papers.TbsPrteOptimalTransport.Helpers.JointTailPopulation
/-! Observation-law identification and simultaneous continuous tail orthogonality. -/
@[expose] public section
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- The common tail has no outcome regression. A zero auxiliary success field
-- lets us reuse its bounded-score and tower lemmas without assuming binary Y.
-- @node: continuousTailCarrier
/-- For [an instrument space](hyp:Z), [a covariate space](hyp:X), [a system of
baseline and policy levels](hyp:L), and [continuous-outcome nuisance functions
for that system](hyp:e), the [common-tail binary carrier](goal)
retains the propensity, level, assignment, pooling-share, and weight functions,
and sets the auxiliary success regression to zero. -/
def continuousTailCarrier (L : LevelData Z X) (e : NuisanceCont L) : NuisanceBin L :=
  ⟨e.prop, e.pLev, fun _ _ => 0, e.piLev, e.tauLev, e.share,
    e.gammaFull, e.gamma, e.gammaTail⟩

-- @node: continuousTailCarrier_admissible
/-- If [continuous-outcome nuisance functions are admissible for the model and
level system](hyp:he), [their common-tail binary carrier is admissible as
well](goal). -/
lemma continuousTailCarrier_admissible (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) : BinAdmissible M L (continuousTailCarrier L e) := by
  rcases he with ⟨hp, hmp, hpk, hmpk, hpi, hmpi, ht, hmt, hs, hms,
    hgf, hmgf, hg, hmg, htail, hmtail, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsum⟩
  refine ⟨hp, hmp, ?_, ?_, ?_, ?_, hs, hms, hsum, hgf, hmgf, htail, hmtail⟩
  · intro a
    filter_upwards [hpk a, hpi a] with x hx hy
    exact ⟨hx, ⟨le_rfl, zero_le_one⟩, hy⟩
  · intro a
    exact ⟨hmpk a, measurable_const, hmpi a⟩
  · intro a
    filter_upwards [ht a, hg a] with x hx hy
    exact ⟨hx, hy⟩
  · exact fun a => ⟨hmt a, hmg a⟩

-- @node: population_commonTailScore_finite_mean_of_continuous_admissible
/-- Suppose [treatment follows a threshold-crossing model](hyp:h), [the policy
map is measurable and preserves the unit interval](hyp:hphi), [it has the
specified derivative](hyp:hDiff), [that derivative is uniformly bounded and
Lipschitz](hyp:hDerivative), [there is at least one positive baseline
level](hyp:hK), and [the continuous nuisance functions are admissible](hyp:he).
If [a lower bound is positive](hyp:hc) and [the highest-level assignment
probability is almost surely at least that bound](hyp:hpi), then [the population
mean of the common-tail score equals its covariate mean after averaging over
instruments and evaluating treatment at the true instrument-specific
propensity and the unused outcome at zero](goal). -/
lemma population_commonTailScore_finite_mean_of_continuous_admissible
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (c : ℝ) (hc : 0 < c)
    (hpi : ∀ᵐ x ∂xLaw M, c ≤ positiveValue e.piLev L.K x) :
    (∫ o, commonTailScore M phi dphi L e.prop e.pLev e.piLev e.gammaTail o
      ∂observationLaw M) =
    ∫ x, ∑ z, instProb M z x * commonTailScore M phi dphi L
      e.prop e.pLev e.piLev e.gammaTail (x, z, M.prop z x, 0) ∂xLaw M := by
  exact population_commonTailScore_finite_mean_of_binary_admissible M h
    phi dphi hphi hDiff hDerivative L hK (continuousTailCarrier L e)
    (continuousTailCarrier_admissible M L e he) c hc hpi

-- @node: population_continuous_tail_joint_path_integrable_of_admissible
/-- Suppose [the policy map is measurable and preserves the unit
interval](hyp:hphi), [it has the specified derivative](hyp:hDiff), [that derivative
is uniformly bounded and Lipschitz](hyp:hDerivative), [there is at least one
positive baseline level](hyp:hK), [baseline assignment probabilities satisfy
overlap](hyp:hov), and [the continuous nuisance direction is admissible at the
truth](hyp:hd). Then [the common-tail score with all nuisance functions perturbed
jointly is integrable over observations for every sufficiently small
step](goal). -/
lemma population_continuous_tail_joint_path_integrable_of_admissible
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del)) :
    ∀ᶠ t : ℝ in 𝓝 0, Integrable (commonTailScore M phi dphi L
      (trueNuisance M L + t • del).prop (trueNuisance M L + t • del).pLev
      (trueNuisance M L + t • del).piLev (trueNuisance M L + t • del).gammaTail)
      (observationLaw M) := by
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  have hidx : 1 ≤ L.K ∧ L.K ≤ L.K := ⟨hK, le_rfl⟩
  filter_upwards [continuousAt_id.abs.eventually_lt_const (by simpa using hr),
    continuous_assignment_path_uniform_lower_bound M L cpi hov del hd] with t ht hpi
  apply commonTailScore_integrable_of_binary_admissible M phi dphi hphi hDiff hDerivative
    L hK (continuousTailCarrier L (trueNuisance M L + t • del))
    (continuousTailCarrier_admissible M L _ (hpath t ht)) (cpi/2)
    (div_pos hov.1 (by norm_num))
  simpa only [continuousTailCarrier, positiveValue, dif_pos hidx] using hpi ⟨L.K,hidx⟩

-- All nuisance fields entering the tail move together. The finite mean's
-- quadratic cancellation is transferred through the population tower identity.
-- @node: population_continuous_tail_joint_orthogonality_of_admissible
/-- Suppose [treatment follows a threshold-crossing model](hyp:h), [the policy
map is measurable and preserves the unit interval](hyp:hphi), [it has the
specified derivative](hyp:hDiff), [that derivative is uniformly bounded and
Lipschitz](hyp:hDerivative), [there is at least one positive baseline
level](hyp:hK), [baseline and policy propensities respect the level
ordering](hyp:hOrder), [baseline assignment probabilities satisfy
overlap](hyp:hov), and [the continuous nuisance direction is admissible at the
truth](hyp:hd). Then [the population mean of the common-tail score has derivative
zero at step zero when its nuisance functions move jointly along that
direction](goal). -/
lemma population_continuous_tail_joint_orthogonality_of_admissible
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del)) :
    HasDerivAt (fun t : ℝ => ∫ o, commonTailScore M phi dphi L
      (trueNuisance M L + t • del).prop (trueNuisance M L + t • del).pLev
      (trueNuisance M L + t • del).piLev (trueNuisance M L + t • del).gammaTail o
      ∂observationLaw M) 0 0 := by
  have hfinite := population_continuous_tail_finite_mean_joint_orthogonality_of_admissible
    M h phi dphi hphi hDiff hDerivative L hK cpi hov del hd
  apply hfinite.congr_of_eventuallyEq
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  have hidx : 1 ≤ L.K ∧ L.K ≤ L.K := ⟨hK, le_rfl⟩
  filter_upwards [continuousAt_id.abs.eventually_lt_const (by simpa using hr),
    continuous_assignment_path_uniform_lower_bound M L cpi hov del hd] with t ht hpi
  have hfinal : ∀ᵐ x ∂xLaw M,
      cpi/2 ≤ positiveValue (trueNuisance M L + t • del).piLev L.K x := by
    simpa only [positiveValue, dif_pos hidx] using hpi ⟨L.K,hidx⟩
  rw [population_commonTailScore_finite_mean_of_continuous_admissible M h
    phi dphi hphi hDiff hDerivative L hK _ (hpath t ht)
    (cpi/2) (div_pos hov.1 (by norm_num)) hfinal]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  have hlevel : ∀ z ∈ L.S L.K,
      M.prop z x = positiveValue (trueNuisance M L).pLev L.K x := by
    intro z hz
    simp only [positiveValue, dif_pos hidx, trueNuisance]
    exact (hOrder.2.2.2.2.2.1 x L.K z le_rfl).mp hz
  have hmass : ∑ z ∈ L.S L.K, instProb M z x =
      positiveValue (trueNuisance M L).piLev L.K x := by
    simp only [positiveValue, dif_pos hidx, trueNuisance, levelSetProb]
  exact commonTailScore_joint_finite_conditional_mean M phi dphi L hK
    M.prop del.prop (trueNuisance M L).pLev del.pLev (trueNuisance M L).piLev del.piLev
    (trueNuisance M L).gammaTail del.gammaTail x (fun z => instProb M z x) t
    hlevel hmass rfl

end Papers.TbsPrteOptimalTransport
