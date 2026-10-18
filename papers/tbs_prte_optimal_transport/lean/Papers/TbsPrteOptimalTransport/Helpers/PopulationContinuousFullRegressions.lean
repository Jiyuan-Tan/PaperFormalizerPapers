module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationContinuousFullProducts
/-! Exact population cancellation for simultaneous full-interval regression changes. -/
@[expose] public section
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

-- The propensity and outcome regression enter the full score through their
-- product. This includes simultaneous changes of both nuisance groups.
-- @node: continuousFullRegressionCoefficient
/-- For [an ordered level system](hyp:L), [continuous nuisance functions](hyp:e),
[a choice of upper or lower side](hyp:plus), [an interval index](hyp:k), and
[a covariate value](hyp:x), the [full-interval regression coefficient](goal)
is the product of the chosen level's propensity and full-interval outcome
mean, with value zero on the lower side at index zero. -/
noncomputable def continuousFullRegressionCoefficient (L : LevelData Z X)
    (e : NuisanceCont L) (plus : Bool) (k : ℕ) (x : X) : ℝ :=
  if plus then positiveValue e.pLev (k + 1) x * fullValue e.JfullPlus k x
  else if k = 0 then 0 else positiveValue e.pLev k x * minusFullValue e k x

-- @node: continuous_full_regression_coefficient_measurable
/-- If [all level propensity functions are measurable](hyp:hp), [all upper
full-interval outcome regressions are measurable](hyp:hj), and [all lower
full-interval outcome regressions are measurable](hyp:hm), then [the
full-interval regression coefficient on either side of any interval is
measurable in covariates](goal). -/
@[fun_prop] lemma continuous_full_regression_coefficient_measurable
    (L : LevelData Z X) (e : NuisanceCont L)
    (hp : ∀ a, Measurable (e.pLev a))
    (hj : ∀ a, Measurable (e.JfullPlus a))
    (hm : ∀ a, Measurable (e.JfullMinus a)) (plus : Bool) (k : ℕ) :
    Measurable (continuousFullRegressionCoefficient L e plus k) := by
  first | fun_prop | skip
  unfold continuousFullRegressionCoefficient positiveValue fullValue minusFullValue
  split_ifs <;> first | fun_prop | exact measurable_const

-- @node: continuous_full_fixed_denominator_difference
/-- If [two nuisance specifications have identical assignment
probabilities](hyp:hpi), then [their full-interval score difference equals
the upper regression-coefficient difference times one minus the normalized
upper assignment indicator, minus the analogous lower product](goal). -/
lemma continuous_full_fixed_denominator_difference (L : LevelData Z X)
    (e b : NuisanceCont L) (hpi : e.piLev = b.piLev) (k : ℕ) (o : Obs X Z) :
    psiFullJ L e k o - psiFullJ L b k o =
      (continuousFullRegressionCoefficient L e true k o.1 -
        continuousFullRegressionCoefficient L b true k o.1) *
        (1 - indicator (o.2.1 ∈ L.S (k + 1)) / positiveValue b.piLev (k + 1) o.1) -
      (continuousFullRegressionCoefficient L e false k o.1 -
        continuousFullRegressionCoefficient L b false k o.1) *
        (1 - indicator (o.2.1 ∈ L.S k) / positiveValue b.piLev k o.1) := by
  rw [psiFullJ_regression_decomposition, psiFullJ_regression_decomposition]
  simp only [hpi, continuousFullRegressionCoefficient, Bool.false_eq_true,
    if_true, if_false]
  split_ifs <;> ring

-- @node: population_continuous_full_regression_integral_eq
/-- Assume [baseline overlap with the specified lower bound](hyp:hov), [the
candidate assignment probabilities equal their true values](hyp:hpi), and
[the covariate weight is measurable](hyp:hw). If [the upper
regression-coefficient difference from truth is measurable](hyp:hpmeas), [the
lower difference is measurable](hyp:hmmeas), [the weighted upper difference
times one minus its normalized assignment indicator is integrable](hyp:hp),
[the analogous lower product is integrable](hyp:hm), and [the weighted true
score is integrable](hyp:hs), then [the weighted candidate full-interval
score is integrable and has the same expectation as the weighted true
score](goal). -/
lemma population_continuous_full_regression_integral_eq
    (L : LevelData Z X) (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (e : NuisanceCont L) (hpi : e.piLev = (trueNuisance M L).piLev)
    (k : Fin L.K) (w : X → ℝ) (hw : Measurable w)
    (hpmeas : Measurable (fun x => continuousFullRegressionCoefficient L e true k x -
      continuousFullRegressionCoefficient L (trueNuisance M L) true k x))
    (hmmeas : Measurable (fun x => continuousFullRegressionCoefficient L e false k x -
      continuousFullRegressionCoefficient L (trueNuisance M L) false k x))
    (hp : Integrable (fun o : Obs X Z => (w o.1 *
      (continuousFullRegressionCoefficient L e true k o.1 -
        continuousFullRegressionCoefficient L (trueNuisance M L) true k o.1)) *
      (1 - indicator (o.2.1 ∈ L.S (k + 1)) /
        positiveValue (trueNuisance M L).piLev (k + 1) o.1)) (observationLaw M))
    (hm : Integrable (fun o : Obs X Z => (w o.1 *
      (continuousFullRegressionCoefficient L e false k o.1 -
        continuousFullRegressionCoefficient L (trueNuisance M L) false k o.1)) *
      (1 - indicator (o.2.1 ∈ L.S k) /
        positiveValue (trueNuisance M L).piLev k o.1)) (observationLaw M))
    (hs : Integrable (fun o : Obs X Z => w o.1 * psiFullJ L (trueNuisance M L) k o)
      (observationLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 * psiFullJ L e k o) (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 * psiFullJ L e k o ∂observationLaw M) =
      ∫ o : Obs X Z, w o.1 * psiFullJ L (trueNuisance M L) k o ∂observationLaw M := by
  have hden i (hi : 1 ≤ i ∧ i ≤ L.K) (x : X) :
      positiveValue (trueNuisance M L).piLev i x = ∑ z ∈ L.S i, instProb M z x := by
    simp only [positiveValue, dif_pos hi, trueNuisance, levelSetProb]
  have zp : (∫ o : Obs X Z, (w o.1 *
      (continuousFullRegressionCoefficient L e true k o.1 -
        continuousFullRegressionCoefficient L (trueNuisance M L) true k o.1)) *
      (1 - indicator (o.2.1 ∈ L.S (k + 1)) /
        positiveValue (trueNuisance M L).piLev (k + 1) o.1) ∂observationLaw M) = 0 := by
    have hk : 1 ≤ k.val + 1 ∧ k.val + 1 ≤ L.K := by omega
    simp_rw [hden _ hk] at hp ⊢
    exact population_normalized_assignment_weighted_integral_zero M _ _ (hw.mul hpmeas)
      (Filter.Eventually.of_forall fun x => hov.1.trans_le (hov.2 x _ hk.1 hk.2)) hp
  have zm : (∫ o : Obs X Z, (w o.1 *
      (continuousFullRegressionCoefficient L e false k o.1 -
        continuousFullRegressionCoefficient L (trueNuisance M L) false k o.1)) *
      (1 - indicator (o.2.1 ∈ L.S k) /
        positiveValue (trueNuisance M L).piLev k o.1) ∂observationLaw M) = 0 := by
    by_cases hk0 : k.val = 0
    · simp [continuousFullRegressionCoefficient, hk0]
    · have hk : 1 ≤ k.val ∧ k.val ≤ L.K := by omega
      simp_rw [hden _ hk] at hm ⊢
      exact population_normalized_assignment_weighted_integral_zero M _ _ (hw.mul hmmeas)
        (Filter.Eventually.of_forall fun x => hov.1.trans_le (hov.2 x _ hk.1 hk.2)) hm
  have heq : (fun o : Obs X Z => w o.1 * psiFullJ L e k o) =
      (fun o => w o.1 * psiFullJ L (trueNuisance M L) k o +
        ((w o.1 * (continuousFullRegressionCoefficient L e true k o.1 -
          continuousFullRegressionCoefficient L (trueNuisance M L) true k o.1)) *
          (1 - indicator (o.2.1 ∈ L.S (k + 1)) /
            positiveValue (trueNuisance M L).piLev (k + 1) o.1) -
        (w o.1 * (continuousFullRegressionCoefficient L e false k o.1 -
          continuousFullRegressionCoefficient L (trueNuisance M L) false k o.1)) *
          (1 - indicator (o.2.1 ∈ L.S k) /
            positiveValue (trueNuisance M L).piLev k o.1))) := by
    funext o
    have hd := continuous_full_fixed_denominator_difference L e (trueNuisance M L) hpi k o
    linear_combination w o.1 * hd
  rw [heq]
  refine ⟨hs.fun_add (hp.sub' hm), ?_⟩
  rw [integral_add hs (hp.sub' hm), integral_sub hp hm, zp, zm]
  ring

-- Only local path integrability is required. The exact cancellation above
-- covers joint propensity and regression changes, including their cross term.
-- @node: population_continuous_full_joint_regression_path_orthogonality
/-- Assume [baseline overlap with the specified lower bound](hyp:hov), [a
nuisance path whose assignment probabilities equal truth at every parameter
value](hyp:hpi), [a positive neighborhood radius](hyp:hradius), and [a
measurable covariate weight](hyp:hw). If throughout that neighborhood [the
upper regression-coefficient difference from truth is measurable](hyp:hpmeas),
[the lower difference is measurable](hyp:hmmeas), [the weighted upper
difference times one minus its normalized assignment indicator is
integrable](hyp:hp), and [the analogous lower product is integrable](hyp:hm),
and if [the weighted true score is integrable](hyp:hs), then [the expected
weighted full-interval score has derivative zero at zero along the joint
propensity and outcome-regression path](goal). -/
lemma population_continuous_full_joint_regression_path_orthogonality
    (L : LevelData Z X) (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (e : ℝ → NuisanceCont L)
    (hpi : ∀ t, (e t).piLev = (trueNuisance M L).piLev)
    (radius : ℝ) (hradius : 0 < radius)
    (k : Fin L.K) (w : X → ℝ) (hw : Measurable w)
    (hpmeas : ∀ t, |t| < radius → Measurable (fun x => continuousFullRegressionCoefficient L (e t) true k x -
      continuousFullRegressionCoefficient L (trueNuisance M L) true k x))
    (hmmeas : ∀ t, |t| < radius → Measurable (fun x => continuousFullRegressionCoefficient L (e t) false k x -
      continuousFullRegressionCoefficient L (trueNuisance M L) false k x))
    (hp : ∀ t, |t| < radius → Integrable (fun o : Obs X Z => (w o.1 *
      (continuousFullRegressionCoefficient L (e t) true k o.1 -
        continuousFullRegressionCoefficient L (trueNuisance M L) true k o.1)) *
      (1 - indicator (o.2.1 ∈ L.S (k + 1)) /
        positiveValue (trueNuisance M L).piLev (k + 1) o.1)) (observationLaw M))
    (hm : ∀ t, |t| < radius → Integrable (fun o : Obs X Z => (w o.1 *
      (continuousFullRegressionCoefficient L (e t) false k o.1 -
        continuousFullRegressionCoefficient L (trueNuisance M L) false k o.1)) *
      (1 - indicator (o.2.1 ∈ L.S k) /
        positiveValue (trueNuisance M L).piLev k o.1)) (observationLaw M))
    (hs : Integrable (fun o : Obs X Z => w o.1 * psiFullJ L (trueNuisance M L) k o)
      (observationLaw M)) :
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z, w o.1 * psiFullJ L (e t) k o
      ∂observationLaw M) 0 0 := by
  apply (hasDerivAt_const (0 : ℝ)
    (∫ o : Obs X Z, w o.1 * psiFullJ L (trueNuisance M L) k o
      ∂observationLaw M)).congr_of_eventuallyEq
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, |t| < radius :=
    continuousAt_id.abs.eventually_lt_const (by simpa using hradius)
  filter_upwards [hnear] with t ht
  exact (population_continuous_full_regression_integral_eq M L cpi hov (e t) (hpi t)
    k w hw (hpmeas t ht) (hmmeas t ht) (hp t ht) (hm t ht) hs).2

end Papers.TbsPrteOptimalTransport
