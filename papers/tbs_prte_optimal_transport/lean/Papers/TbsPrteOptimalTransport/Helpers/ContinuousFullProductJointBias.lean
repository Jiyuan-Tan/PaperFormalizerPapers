module
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousFullJointBias
/-! Joint full-interval regression and signed product-weight cancellation. -/
public section
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

-- Centering uses the population assignment law even when the fitted weight
-- is signed and the fitted plug-in regression differs from the truth.
-- @node: population_continuous_fitted_full_assignment_zero
/-- If [the fitted full-interval regression contrast is measurable](hyp:hj) and
[integrable under the observation law](hyp:hi), then [its product with the
policy-minus-baseline assignment indicator contrast centered by its true
conditional probability is integrable and has population mean zero](goal). -/
lemma population_continuous_fitted_full_assignment_zero
    (L : LevelData Z X) (e : NuisanceCont L) (k : ℕ)
    (hj : Measurable (contFullJ L e k))
    (hi : Integrable (fun o : Obs X Z => contFullJ L e k o.1) (observationLaw M)) :
    Integrable (fun o : Obs X Z => contFullJ L e k o.1 *
      (indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k) -
        gammaFull M L k o.1)) (observationLaw M) ∧
    (∫ o : Obs X Z, contFullJ L e k o.1 *
      (indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k) -
        gammaFull M L k o.1) ∂observationLaw M) = 0 := by
  have ip := population_assignment_residual_weighted_integrable M (higherPolicy L k) _ hi
  have im := population_assignment_residual_weighted_integrable M (higherBaseline L k) _ hi
  have hz := population_signed_assignment_weighted_integral_zero M
    (higherPolicy L k) (higherBaseline L k) (contFullJ L e k) hj ip im
  have hid : (fun o : Obs X Z => contFullJ L e k o.1 *
      (indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k) -
        gammaFull M L k o.1)) =
      (fun o => contFullJ L e k o.1 *
        (indicator (o.2.1 ∈ higherPolicy L k) - ∑ z ∈ higherPolicy L k, instProb M z o.1) -
        contFullJ L e k o.1 *
        (indicator (o.2.1 ∈ higherBaseline L k) - ∑ z ∈ higherBaseline L k, instProb M z o.1)) := by
    funext o
    unfold gammaFull
    ring
  exact ⟨by rw [hid]; exact ip.sub' im, hz⟩

-- The two linear weight contributions cancel. The remaining term is the
-- product of weight error and regression error, including simultaneous p/J changes.
-- @node: population_continuous_full_fixed_denominator_product_bias
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[invariant baseline and policy level ordering](hyp:hL), and [baseline overlap with
floor cpi](hyp:hov), suppose [the fitted assignment denominators equal the
truth](hyp:hpi). Assume [the fitted assignment contrast weight is measurable](hyp:hg)
and [integrable](hyp:ig), [the fitted regression contrast is measurable](hyp:hj)
and [integrable under the observation law](hyp:ij), [the upper and lower regression
coefficient errors are measurable](hyp:hpmeas,hmmeas), [their products with the
fitted weight and the respective normalized assignment defects are
integrable](hyp:ip,im), and [the product of the true-minus-fitted weight and the
fitted-minus-true regression contrast is integrable](hyp:ir). Then [the fitted
full-interval product score is integrable and its mean equals the true weighted
regression contrast mean plus the mean product of those weight and regression
errors](goal). -/
lemma population_continuous_full_fixed_denominator_product_bias
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (e : NuisanceCont L) (hpi : e.piLev = (trueNuisance M L).piLev) (k : Fin L.K)
    (hg : Measurable (e.gammaFull k)) (ig : Integrable (e.gammaFull k) (xLaw M))
    (hj : Measurable (contFullJ L e k))
    (ij : Integrable (fun o : Obs X Z => contFullJ L e k o.1) (observationLaw M))
    (hpmeas : Measurable (fun x => continuousFullRegressionCoefficient L e true k x -
      continuousFullRegressionCoefficient L (trueNuisance M L) true k x))
    (hmmeas : Measurable (fun x => continuousFullRegressionCoefficient L e false k x -
      continuousFullRegressionCoefficient L (trueNuisance M L) false k x))
    (ip : Integrable (fun o : Obs X Z => (e.gammaFull k o.1 *
      (continuousFullRegressionCoefficient L e true k o.1 -
        continuousFullRegressionCoefficient L (trueNuisance M L) true k o.1)) *
      (1 - indicator (o.2.1 ∈ L.S (k+1)) /
        positiveValue (trueNuisance M L).piLev (k+1) o.1)) (observationLaw M))
    (im : Integrable (fun o : Obs X Z => (e.gammaFull k o.1 *
      (continuousFullRegressionCoefficient L e false k o.1 -
        continuousFullRegressionCoefficient L (trueNuisance M L) false k o.1)) *
      (1 - indicator (o.2.1 ∈ L.S k) /
        positiveValue (trueNuisance M L).piLev k o.1)) (observationLaw M))
    (ir : Integrable (fun o : Obs X Z => (gammaFull M L k o.1 - e.gammaFull k o.1) *
      (contFullJ L e k o.1 - contFullJ L (trueNuisance M L) k o.1)) (observationLaw M)) :
    Integrable (psiFullProd L e k) (observationLaw M) ∧
    (∫ o : Obs X Z, psiFullProd L e k o ∂observationLaw M) =
      (∫ o : Obs X Z, gammaFull M L k o.1 * contFullJ L (trueNuisance M L) k o.1
        ∂observationLaw M) +
      ∫ o : Obs X Z, (gammaFull M L k o.1 - e.gammaFull k o.1) *
        (contFullJ L e k o.1 - contFullJ L (trueNuisance M L) k o.1)
        ∂observationLaw M := by
  obtain ⟨is0, zs0⟩ := population_continuous_full_mean_from_overlap M h he q L hL
    cpi hov k k.isLt (e.gammaFull k) hg ig
  obtain ⟨is, zs⟩ := population_continuous_full_regression_integral_eq M L cpi hov
    e hpi k (e.gammaFull k) hg hpmeas hmmeas ip im is0
  obtain ⟨ia, za⟩ := population_continuous_fitted_full_assignment_zero M L e k hj ij
  have ij0 := population_contFullJ_weighted_integrable M h he q L hL k
    (e.gammaFull k) hg ig
  have ig0 : Measurable (gammaFull M L k) := by
    first
    | fun_prop
    | exact (population_instrument_set_probability_measurable M _).sub
        (population_instrument_set_probability_measurable M _)
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  have ig0i : Integrable (gammaFull M L k) (xLaw M) :=
    Integrable.of_bound ig0.aestronglyMeasurable 1
      (Eventually.of_forall fun x => by
        have hp := population_instrument_set_probability_range M (higherPolicy L k) x
        have hm := population_instrument_set_probability_range M (higherBaseline L k) x
        rw [Real.norm_eq_abs, abs_le]
        unfold gammaFull
        constructor <;> linarith [hp.1, hp.2, hm.1, hm.2])
  have it := population_contFullJ_weighted_integrable M h he q L hL k
    (gammaFull M L k) ig0 ig0i
  have hid : (fun o : Obs X Z => psiFullProd L e k o) =
      (fun o => e.gammaFull k o.1 * psiFullJ L e k o +
        contFullJ L e k o.1 *
          (indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k) -
            gammaFull M L k o.1) +
        (gammaFull M L k o.1 * contFullJ L (trueNuisance M L) k o.1 -
          e.gammaFull k o.1 * contFullJ L (trueNuisance M L) k o.1) +
        (gammaFull M L k o.1 - e.gammaFull k o.1) *
          (contFullJ L e k o.1 - contFullJ L (trueNuisance M L) k o.1)) := by
    funext o
    simp only [psiFullProd, fullValue, dif_pos k.isLt]
    ring
  change Integrable (fun o : Obs X Z => psiFullProd L e k o) _ ∧ _
  rw [hid]
  refine ⟨((is.fun_add ia).fun_add (it.sub' ij0)).fun_add ir, ?_⟩
  rw [integral_add ((is.fun_add ia).fun_add (it.sub' ij0)) ir,
    integral_add (is.fun_add ia) (it.sub' ij0), integral_add is ia,
    integral_sub it ij0, za, zs, zs0]
  ring

-- @node: continuous_full_J_eq_regression_coefficient_contrast
/-- [The full-interval regression contrast at any covariate value equals its
upper regression coefficient minus its lower regression coefficient](goal). -/
lemma continuous_full_J_eq_regression_coefficient_contrast
    (L : LevelData Z X) (e : NuisanceCont L) (k : ℕ) (x : X) :
    contFullJ L e k x = continuousFullRegressionCoefficient L e true k x -
      continuousFullRegressionCoefficient L e false k x := by
  simp only [contFullJ, continuousFullRegressionCoefficient, Bool.false_eq_true,
    if_true, if_false]
  by_cases hk : k = 0
  · simp [hk, positiveValue]
  · simp [hk]

-- The path conditions concern primitive regressions and residual integrability.
-- The vanishing score derivative is obtained from the population bias identity,
-- rather than assumed as a conditional-score property.
-- @node: population_continuous_full_joint_regression_weight_orthogonality
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[invariant baseline and policy level ordering](hyp:hL), and [baseline overlap with
floor cpi](hyp:hov), consider [a nuisance path starting at the truth](hyp:he0)
and [nonnegative coefficient and weight error constants D and C](hyp:hD,hC).
Suppose [near zero the denominators remain true, the fitted weight and regression
contrast are measurable and integrable, both coefficient errors are measurable
and bounded almost surely by D times the absolute displacement, the weight error
is bounded almost surely by C times that displacement, and the two fitted-weight
coefficient-error products with normalized assignment defects are
integrable](hyp:hlocal). Then [the population mean of the fitted full-interval
product score has derivative zero at zero](goal). -/
lemma population_continuous_full_joint_regression_weight_orthogonality
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (e : ℝ → NuisanceCont L) (he0 : e 0 = trueNuisance M L)
    (k : Fin L.K) (D C : ℝ) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hlocal : ∀ᶠ t : ℝ in 𝓝 0,
      (e t).piLev = (trueNuisance M L).piLev ∧
      Measurable ((e t).gammaFull k) ∧ Integrable ((e t).gammaFull k) (xLaw M) ∧
      Measurable (contFullJ L (e t) k) ∧
      Integrable (fun o : Obs X Z => contFullJ L (e t) k o.1) (observationLaw M) ∧
      (∀ plus, Measurable (fun x => continuousFullRegressionCoefficient L (e t) plus k x -
        continuousFullRegressionCoefficient L (trueNuisance M L) plus k x)) ∧
      (∀ plus, ∀ᵐ x ∂xLaw M,
        |continuousFullRegressionCoefficient L (e t) plus k x -
          continuousFullRegressionCoefficient L (trueNuisance M L) plus k x| ≤ D * |t|) ∧
      (∀ᵐ x ∂xLaw M, |gammaFull M L k x - (e t).gammaFull k x| ≤ C * |t|) ∧
      Integrable (fun o : Obs X Z => ((e t).gammaFull k o.1 *
        (continuousFullRegressionCoefficient L (e t) true k o.1 -
          continuousFullRegressionCoefficient L (trueNuisance M L) true k o.1)) *
        (1 - indicator (o.2.1 ∈ L.S (k+1)) /
          positiveValue (trueNuisance M L).piLev (k+1) o.1)) (observationLaw M) ∧
      Integrable (fun o : Obs X Z => ((e t).gammaFull k o.1 *
        (continuousFullRegressionCoefficient L (e t) false k o.1 -
          continuousFullRegressionCoefficient L (trueNuisance M L) false k o.1)) *
        (1 - indicator (o.2.1 ∈ L.S k) /
          positiveValue (trueNuisance M L).piLev k o.1)) (observationLaw M)) :
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z, psiFullProd L (e t) k o
      ∂observationLaw M) 0 0 := by
  haveI : IsProbabilityMeasure (observationLaw M) := by
    unfold observationLaw
    exact Measure.isProbabilityMeasure_map
      (M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))).aemeasurable
  have ht0 := hlocal.self_of_nhds
  have hj0 := population_continuous_full_J_measurable M h.2.2.2.1 q L hL k
  have hg0 : Measurable (gammaFull M L k) := by
    first
    | fun_prop
    | exact (population_instrument_set_probability_measurable M _).sub
        (population_instrument_set_probability_measurable M _)
  let R : ℝ → Obs X Z → ℝ := fun t o =>
    (gammaFull M L k o.1 - (e t).gammaFull k o.1) *
      (contFullJ L (e t) k o.1 - contFullJ L (trueNuisance M L) k o.1)
  have hR0 : R 0 = fun _ => (0 : ℝ) := by
    funext o
    simp only [R, he0, sub_self, mul_zero]
  have hr : ∀ᶠ t : ℝ in 𝓝 0, AEStronglyMeasurable (R t) (observationLaw M) ∧
      ∀ᵐ o ∂observationLaw M, |R t o| ≤ (2 * C * D) * t^2 := by
    filter_upwards [hlocal] with t ht
    have hgt := ht.2.1
    have hjt := ht.2.2.2.1
    have hrm : Measurable (R t) := by
      dsimp only [R]
      fun_prop
    refine ⟨hrm.aestronglyMeasurable, ?_⟩
    dsimp only [R]
    apply observationLaw_covariate_ae M (fun x =>
      |(gammaFull M L k x - (e t).gammaFull k x) *
        (contFullJ L (e t) k x - contFullJ L (trueNuisance M L) k x)| ≤
        (2 * C * D) * t^2)
    filter_upwards [ht.2.2.2.2.2.2.1 true, ht.2.2.2.2.2.2.1 false,
      ht.2.2.2.2.2.2.2.1] with x hp hm hg
    have hJ : |contFullJ L (e t) k x - contFullJ L (trueNuisance M L) k x| ≤
        2 * D * |t| := by
      rw [continuous_full_J_eq_regression_coefficient_contrast,
        continuous_full_J_eq_regression_coefficient_contrast]
      have hid (a b c d : ℝ) : a - b - (c - d) = (a - c) - (b - d) := by ring
      rw [hid]
      exact (abs_sub _ _).trans (by linarith)
    rw [abs_mul]
    calc
      _ ≤ (C * |t|) * (2 * D * |t|) :=
        mul_le_mul hg hJ (abs_nonneg _) (by positivity)
      _ = (2 * C * D) * t^2 := by rw [← sq_abs t]; ring
  have hder := integral_local_quadratic_orthogonality (observationLaw M) R
    (2 * C * D) (by rw [hR0]; exact integrable_zero _ _ _)
    (by filter_upwards [hr] with t ht; simpa only [hR0, sub_zero] using ht)
  let target := ∫ o : Obs X Z, gammaFull M L k o.1 *
    contFullJ L (trueNuisance M L) k o.1 ∂observationLaw M
  have hd := (hasDerivAt_const (0 : ℝ) target).add hder
  simp only [zero_add] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [hlocal, hr] with t ht hrt
  have ir : Integrable (R t) (observationLaw M) :=
    Integrable.of_bound hrt.1 ((2 * C * D) * t^2)
      (by simpa only [Real.norm_eq_abs] using hrt.2)
  exact (population_continuous_full_fixed_denominator_product_bias M h he q L hL cpi hov
    (e t) ht.1 k ht.2.1 ht.2.2.1 ht.2.2.2.1 ht.2.2.2.2.1
    (ht.2.2.2.2.2.1 true) (ht.2.2.2.2.2.1 false)
    ht.2.2.2.2.2.2.2.2.1 ht.2.2.2.2.2.2.2.2.2 ir).2

-- The reciprocal defect is integrable for a bounded measurable coefficient.
-- This includes the structural zero, where positiveValue is identically zero.
-- @node: population_continuous_full_reciprocal_defect_integrable
/-- Suppose [the fitted assignment denominators are measurable](hyp:hpi),
[c is positive](hyp:hc), and [all fitted denominators are at least c almost
surely](hyp:hclip). For [a measurable coefficient](hyp:hv) [bounded in magnitude
by B almost surely](hyp:hb), [its product with one minus the ratio of the true
to fitted assignment denominator is integrable under the observation law at
every index, including the structural zero index](goal). -/
lemma population_continuous_full_reciprocal_defect_integrable
    (L : LevelData Z X) (e : NuisanceCont L)
    (hpi : ∀ a, Measurable (e.piLev a))
    (c B : ℝ) (hc : 0 < c) (hclip : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ e.piLev a x)
    (v : X → ℝ) (hv : Measurable v) (hb : ∀ᵐ x ∂xLaw M, ‖v x‖ ≤ B)
    (i : ℕ) :
    Integrable (fun o : Obs X Z => v o.1 *
      (1 - positiveValue (trueNuisance M L).piLev i o.1 /
        positiveValue e.piLev i o.1)) (observationLaw M) := by
  by_cases hi : 1 ≤ i ∧ i ≤ L.K
  · obtain ⟨iz, ir, hz⟩ := population_fitted_normalized_assignment_defect M (L.S i)
      (e.piLev ⟨i,hi⟩) v (hpi _) hv c B hc (hclip _) hb
    simpa only [positiveValue, dif_pos hi, trueNuisance, levelSetProb] using ir
  · haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
    simp only [positiveValue, dif_neg hi, zero_div, sub_zero, mul_one]
    apply Integrable.of_bound (hv.comp measurable_fst).aestronglyMeasurable B
    exact observationLaw_covariate_ae M _ hb

-- Simultaneous changes leave three products of nuisance errors: the two
-- regression/denominator defects and the signed weight/regression defect.
-- @node: population_continuous_full_joint_product_bias
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
and [invariant baseline and policy level ordering](hyp:hL), suppose [the fitted
denominators are measurable](hyp:hpi), [c is positive](hyp:hc), and [all fitted
denominators are at least c almost surely](hyp:hclip). Assume [the fitted weight
is measurable](hyp:hg) and [integrable](hyp:ig), [the fitted regression contrast
is measurable](hyp:hj) and [integrable under the observation law](hyp:ij),
[the fitted weight times each regression coefficient error is measurable](hyp:hm),
[the upper and lower such products have magnitude at most Bp and Bm almost
surely](hyp:hBp,hBm), and [the true-minus-fitted weight times the fitted-minus-true
regression contrast is integrable](hyp:ir). Then [the fitted full-interval product
score is integrable and its mean equals the true target mean plus the upper
weighted coefficient-error reciprocal-denominator defect mean, minus the lower
one, plus the mean product of the weight and regression contrast errors](goal). -/
lemma population_continuous_full_joint_product_bias
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (e : NuisanceCont L) (hpi : ∀ a, Measurable (e.piLev a))
    (c : ℝ) (hc : 0 < c) (hclip : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ e.piLev a x)
    (k : Fin L.K) (hg : Measurable (e.gammaFull k))
    (ig : Integrable (e.gammaFull k) (xLaw M))
    (hj : Measurable (contFullJ L e k))
    (ij : Integrable (fun o : Obs X Z => contFullJ L e k o.1) (observationLaw M))
    (hm : ∀ plus, Measurable (fun x => e.gammaFull k x *
      (continuousFullRegressionCoefficient L e plus k x -
        continuousFullRegressionCoefficient L (trueNuisance M L) plus k x)))
    (Bp Bm : ℝ)
    (hBp : ∀ᵐ x ∂xLaw M, ‖e.gammaFull k x *
      (continuousFullRegressionCoefficient L e true k x -
        continuousFullRegressionCoefficient L (trueNuisance M L) true k x)‖ ≤ Bp)
    (hBm : ∀ᵐ x ∂xLaw M, ‖e.gammaFull k x *
      (continuousFullRegressionCoefficient L e false k x -
        continuousFullRegressionCoefficient L (trueNuisance M L) false k x)‖ ≤ Bm)
    (ir : Integrable (fun o : Obs X Z => (gammaFull M L k o.1 - e.gammaFull k o.1) *
      (contFullJ L e k o.1 - contFullJ L (trueNuisance M L) k o.1)) (observationLaw M)) :
    Integrable (psiFullProd L e k) (observationLaw M) ∧
    (∫ o : Obs X Z, psiFullProd L e k o ∂observationLaw M) =
      (∫ o : Obs X Z, gammaFull M L k o.1 * contFullJ L (trueNuisance M L) k o.1
        ∂observationLaw M) +
      (∫ o : Obs X Z, (e.gammaFull k o.1 *
        (continuousFullRegressionCoefficient L e true k o.1 -
          continuousFullRegressionCoefficient L (trueNuisance M L) true k o.1)) *
        (1 - positiveValue (trueNuisance M L).piLev (k+1) o.1 /
          positiveValue e.piLev (k+1) o.1) ∂observationLaw M) -
      (∫ o : Obs X Z, (e.gammaFull k o.1 *
        (continuousFullRegressionCoefficient L e false k o.1 -
          continuousFullRegressionCoefficient L (trueNuisance M L) false k o.1)) *
        (1 - positiveValue (trueNuisance M L).piLev k o.1 /
          positiveValue e.piLev k o.1) ∂observationLaw M) +
      ∫ o : Obs X Z, (gammaFull M L k o.1 - e.gammaFull k o.1) *
        (contFullJ L e k o.1 - contFullJ L (trueNuisance M L) k o.1)
        ∂observationLaw M := by
  obtain ⟨is, zs⟩ := population_continuous_full_joint_fitted_bias M h he q L hL
    e hpi c hc hclip k (e.gammaFull k) hg ig (hm true) (hm false) Bp Bm hBp hBm
  obtain ⟨ia, za⟩ := population_continuous_fitted_full_assignment_zero M L e k hj ij
  have ij0 := population_contFullJ_weighted_integrable M h he q L hL k
    (e.gammaFull k) hg ig
  have hg0 : Measurable (gammaFull M L k) := by
    first
    | fun_prop
    | exact (population_instrument_set_probability_measurable M _).sub
        (population_instrument_set_probability_measurable M _)
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  have ig0 : Integrable (gammaFull M L k) (xLaw M) :=
    Integrable.of_bound hg0.aestronglyMeasurable 1
      (Eventually.of_forall fun x => by
        have hp := population_instrument_set_probability_range M (higherPolicy L k) x
        have hm := population_instrument_set_probability_range M (higherBaseline L k) x
        rw [Real.norm_eq_abs, abs_le]
        unfold gammaFull
        constructor <;> linarith [hp.1, hp.2, hm.1, hm.2])
  have it := population_contFullJ_weighted_integrable M h he q L hL k
    (gammaFull M L k) hg0 ig0
  have hid : (fun o : Obs X Z => psiFullProd L e k o) =
      (fun o => e.gammaFull k o.1 * psiFullJ L e k o +
        contFullJ L e k o.1 *
          (indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k) -
            gammaFull M L k o.1) +
        (gammaFull M L k o.1 * contFullJ L (trueNuisance M L) k o.1 -
          e.gammaFull k o.1 * contFullJ L (trueNuisance M L) k o.1) +
        (gammaFull M L k o.1 - e.gammaFull k o.1) *
          (contFullJ L e k o.1 - contFullJ L (trueNuisance M L) k o.1)) := by
    funext o
    simp only [psiFullProd, fullValue, dif_pos k.isLt]
    ring
  change Integrable (fun o : Obs X Z => psiFullProd L e k o) _ ∧ _
  rw [hid]
  refine ⟨((is.fun_add ia).fun_add (it.sub' ij0)).fun_add ir, ?_⟩
  rw [integral_add ((is.fun_add ia).fun_add (it.sub' ij0)) ir,
    integral_add (is.fun_add ia) (it.sub' ij0), integral_add is ia,
    integral_sub it ij0, za, zs]
  ring

-- Primitive coefficient, denominator, and weight errors control the entire
-- fitted product score bias, including their simultaneous interactions.
-- @node: population_continuous_full_joint_product_bias_bound
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
and [invariant baseline and policy level ordering](hyp:hL), assume [the fitted
denominators are measurable](hyp:hpi), [c is positive](hyp:hc), [all fitted
denominators are at least c almost surely](hyp:hclip), [the fitted weight is
measurable](hyp:hg), [the fitted regression contrast is measurable](hyp:hj) and
[integrable under the observation law](hyp:ij), and [both regression coefficient
errors are measurable](hyp:hm). If [B, D, C, and G are nonnegative](hyp:hB,hD,hC,hG),
[the fitted weight has magnitude at most B almost surely](hyp:hgb), [both
coefficient errors have magnitude at most D almost surely](hyp:ha), [all
denominator errors have magnitude at most C almost surely](hyp:hd), and [the
weight error has magnitude at most G almost surely](hyp:hge), then [the fitted
full-interval product score is integrable and its absolute population bias is
at most 2 B D C / c + 2 G D](goal). -/
lemma population_continuous_full_joint_product_bias_bound
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (e : NuisanceCont L) (hpi : ∀ a, Measurable (e.piLev a))
    (c : ℝ) (hc : 0 < c) (hclip : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ e.piLev a x)
    (k : Fin L.K) (hg : Measurable (e.gammaFull k))
    (hj : Measurable (contFullJ L e k))
    (ij : Integrable (fun o : Obs X Z => contFullJ L e k o.1) (observationLaw M))
    (hm : ∀ plus, Measurable (fun x => continuousFullRegressionCoefficient L e plus k x -
      continuousFullRegressionCoefficient L (trueNuisance M L) plus k x))
    (B D C G : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hgb : ∀ᵐ x ∂xLaw M, ‖e.gammaFull k x‖ ≤ B)
    (ha : ∀ plus, ∀ᵐ x ∂xLaw M,
      |continuousFullRegressionCoefficient L e plus k x -
        continuousFullRegressionCoefficient L (trueNuisance M L) plus k x| ≤ D)
    (hd : ∀ a, ∀ᵐ x ∂xLaw M, |e.piLev a x - (trueNuisance M L).piLev a x| ≤ C)
    (hge : ∀ᵐ x ∂xLaw M, |gammaFull M L k x - e.gammaFull k x| ≤ G) :
    Integrable (psiFullProd L e k) (observationLaw M) ∧
    |(∫ o : Obs X Z, psiFullProd L e k o ∂observationLaw M) -
      ∫ o : Obs X Z, gammaFull M L k o.1 * contFullJ L (trueNuisance M L) k o.1
        ∂observationLaw M| ≤ 2 * (B * D * C / c) + 2 * G * D := by
  haveI : IsProbabilityMeasure (observationLaw M) := by
    unfold observationLaw
    exact Measure.isProbabilityMeasure_map
      (M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))).aemeasurable
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  have ig : Integrable (e.gammaFull k) (xLaw M) :=
    Integrable.of_bound hg.aestronglyMeasurable B hgb
  have hwm (plus : Bool) : Measurable (fun x => e.gammaFull k x *
      (continuousFullRegressionCoefficient L e plus k x -
        continuousFullRegressionCoefficient L (trueNuisance M L) plus k x)) := by
    fun_prop
  have hwb (plus : Bool) : ∀ᵐ x ∂xLaw M, ‖e.gammaFull k x *
      (continuousFullRegressionCoefficient L e plus k x -
        continuousFullRegressionCoefficient L (trueNuisance M L) plus k x)‖ ≤ B * D := by
    filter_upwards [hgb, ha plus] with x hx hy
    simp only [norm_mul, Real.norm_eq_abs] at hx ⊢
    exact mul_le_mul hx hy (abs_nonneg _) hB
  let R : Obs X Z → ℝ := fun o => (gammaFull M L k o.1 - e.gammaFull k o.1) *
    (contFullJ L e k o.1 - contFullJ L (trueNuisance M L) k o.1)
  have hg0 : Measurable (gammaFull M L k) := by
    first
    | fun_prop
    | exact (population_instrument_set_probability_measurable M _).sub
        (population_instrument_set_probability_measurable M _)
  have hj0 := population_continuous_full_J_measurable M h.2.2.2.1 q L hL k
  have hRm : Measurable R := by dsimp only [R]; fun_prop
  have hRb : ∀ᵐ o ∂observationLaw M, |R o| ≤ 2 * G * D := by
    apply observationLaw_covariate_ae M (fun x =>
      |(gammaFull M L k x - e.gammaFull k x) *
        (contFullJ L e k x - contFullJ L (trueNuisance M L) k x)| ≤ 2*G*D)
    filter_upwards [ha true, ha false, hge] with x hp hn hgx
    have hJ : |contFullJ L e k x - contFullJ L (trueNuisance M L) k x| ≤ 2*D := by
      rw [continuous_full_J_eq_regression_coefficient_contrast,
        continuous_full_J_eq_regression_coefficient_contrast]
      have hid (a b c d : ℝ) : a-b-(c-d) = (a-c)-(b-d) := by ring
      rw [hid]
      exact (abs_sub _ _).trans (by linarith)
    rw [abs_mul]
    nlinarith [mul_le_mul hgx hJ (abs_nonneg _) hG]
  have ir : Integrable R (observationLaw M) :=
    Integrable.of_bound hRm.aestronglyMeasurable (2*G*D)
      (by simpa only [Real.norm_eq_abs] using hRb)
  have hrint : |∫ o, R o ∂observationLaw M| ≤ 2*G*D := by
    have hb : ∀ᵐ o ∂observationLaw M, ‖R o‖ ≤ 2*G*D := by
      simpa only [Real.norm_eq_abs] using hRb
    simpa using norm_integral_le_of_norm_le_const hb
  have hdef (plus : Bool) (i : ℕ) (hi : 1 ≤ i ∧ i ≤ L.K) :
      |∫ o : Obs X Z, (e.gammaFull k o.1 *
        (continuousFullRegressionCoefficient L e plus k o.1 -
          continuousFullRegressionCoefficient L (trueNuisance M L) plus k o.1)) *
        (1 - positiveValue (trueNuisance M L).piLev i o.1 /
          positiveValue e.piLev i o.1) ∂observationLaw M| ≤ B*D*C/c := by
    have hb : ∀ᵐ o ∂observationLaw M, |(e.gammaFull k o.1 *
        (continuousFullRegressionCoefficient L e plus k o.1 -
          continuousFullRegressionCoefficient L (trueNuisance M L) plus k o.1)) *
        (1 - positiveValue (trueNuisance M L).piLev i o.1 /
          positiveValue e.piLev i o.1)| ≤ B*D*C/c := by
      apply observationLaw_covariate_ae M (fun x => |(e.gammaFull k x *
        (continuousFullRegressionCoefficient L e plus k x -
          continuousFullRegressionCoefficient L (trueNuisance M L) plus k x)) *
        (1 - positiveValue (trueNuisance M L).piLev i x /
          positiveValue e.piLev i x)| ≤ B*D*C/c)
      filter_upwards [hgb, ha plus, hclip ⟨i,hi⟩, hd ⟨i,hi⟩] with x hx ha hclip hd
      simp only [positiveValue, dif_pos hi]
      simpa only [abs_one, mul_one, one_pow] using
        continuous_full_coefficient_reciprocal_defect_bound _ _ _ _ _ D C B 1 c
          hc hclip (by simpa using ha) (by simpa using hd)
          (by simpa only [Real.norm_eq_abs] using hx) hD hC
    have hbn : ∀ᵐ o ∂observationLaw M, ‖(e.gammaFull k o.1 *
        (continuousFullRegressionCoefficient L e plus k o.1 -
          continuousFullRegressionCoefficient L (trueNuisance M L) plus k o.1)) *
        (1 - positiveValue (trueNuisance M L).piLev i o.1 /
          positiveValue e.piLev i o.1)‖ ≤ B*D*C/c := by
      simpa only [Real.norm_eq_abs] using hb
    simpa using norm_integral_le_of_norm_le_const hbn
  obtain ⟨is, hs⟩ := population_continuous_full_joint_product_bias M h he q L hL
    e hpi c hc hclip k hg ig hj ij hwm (B*D) (B*D) (hwb true) (hwb false) ir
  refine ⟨is, ?_⟩
  rw [hs]
  have hid (a b c d : ℝ) : a+b-c+d-a = (b-c)+d := by ring
  rw [hid]
  apply (abs_add_le _ _).trans
  have hp := hdef true (k+1) (by omega)
  have hn : |∫ o : Obs X Z, (e.gammaFull k o.1 *
      (continuousFullRegressionCoefficient L e false k o.1 -
        continuousFullRegressionCoefficient L (trueNuisance M L) false k o.1)) *
      (1 - positiveValue (trueNuisance M L).piLev k o.1 /
        positiveValue e.piLev k o.1) ∂observationLaw M| ≤ B*D*C/c := by
    by_cases hk0 : k.val = 0
    · simp only [continuousFullRegressionCoefficient, Bool.false_eq_true, if_false,
        if_pos hk0, sub_self, mul_zero, zero_mul, integral_zero, abs_zero]
      positivity
    · exact hdef false k (by omega)
  dsimp only [R] at hrint
  convert! add_le_add ((abs_sub _ _).trans (add_le_add hp hn)) hrint using 1 <;> ring

-- The primitive local path controls imply a quadratic population remainder.
-- In particular, separate partial-derivative cancellations are not needed.
-- @node: population_continuous_full_joint_product_orthogonality
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
and [invariant baseline and policy level ordering](hyp:hL), consider [a nuisance
path starting at the truth](hyp:he0), with [nonnegative B, D, C, and G](hyp:hB,hD,hC,hG)
and [positive c](hyp:hc). Suppose [near zero the fitted denominators are measurable
and at least c almost surely, the fitted weight and regression contrast are
measurable, the contrast is integrable, the coefficient errors are measurable,
the weight is bounded in magnitude by B almost surely, and the coefficient,
denominator, and weight errors are bounded almost surely by D, C, and G times
the absolute displacement, respectively](hyp:hlocal). Then [the population mean
of the fitted full-interval product score has derivative zero at zero, and the
score is integrable for all sufficiently small displacements](goal). -/
lemma population_continuous_full_joint_product_orthogonality
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (e : ℝ → NuisanceCont L) (he0 : e 0 = trueNuisance M L)
    (k : Fin L.K) (B D C G c : ℝ)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hC : 0 ≤ C) (hG : 0 ≤ G) (hc : 0 < c)
    (hlocal : ∀ᶠ t : ℝ in 𝓝 0,
      (∀ a, Measurable ((e t).piLev a)) ∧
      (∀ a, ∀ᵐ x ∂xLaw M, c ≤ (e t).piLev a x) ∧
      Measurable ((e t).gammaFull k) ∧ Measurable (contFullJ L (e t) k) ∧
      Integrable (fun o : Obs X Z => contFullJ L (e t) k o.1) (observationLaw M) ∧
      (∀ plus, Measurable (fun x => continuousFullRegressionCoefficient L (e t) plus k x -
        continuousFullRegressionCoefficient L (trueNuisance M L) plus k x)) ∧
      (∀ᵐ x ∂xLaw M, ‖(e t).gammaFull k x‖ ≤ B) ∧
      (∀ plus, ∀ᵐ x ∂xLaw M,
        |continuousFullRegressionCoefficient L (e t) plus k x -
          continuousFullRegressionCoefficient L (trueNuisance M L) plus k x| ≤ D * |t|) ∧
      (∀ a, ∀ᵐ x ∂xLaw M,
        |(e t).piLev a x - (trueNuisance M L).piLev a x| ≤ C * |t|) ∧
      (∀ᵐ x ∂xLaw M, |gammaFull M L k x - (e t).gammaFull k x| ≤ G * |t|)) :
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z, psiFullProd L (e t) k o
      ∂observationLaw M) 0 0 ∧
    (∀ᶠ t : ℝ in 𝓝 0, Integrable (psiFullProd L (e t) k)
      (observationLaw M)) := by
  have hi : ∀ᶠ t : ℝ in 𝓝 0, Integrable (psiFullProd L (e t) k)
      (observationLaw M) := by
    filter_upwards [hlocal] with t ht
    rcases ht with ⟨hpim, hclip, hgm, hjm, hji, hcm, hgb, ha, hd, hge⟩
    exact (population_continuous_full_joint_product_bias_bound M h he q L hL
      (e t) hpim c hc hclip k hgm hjm hji hcm B (D*|t|) (C*|t|) (G*|t|)
      hB (by positivity) (by positivity) (by positivity) hgb ha hd hge).1
  refine ⟨?_, hi⟩
  let target := ∫ o : Obs X Z, gammaFull M L k o.1 *
    contFullJ L (trueNuisance M L) k o.1 ∂observationLaw M
  have hb : ∀ᶠ t : ℝ in 𝓝 0,
      |(∫ o : Obs X Z, psiFullProd L (e t) k o ∂observationLaw M) - target| ≤
        (2*(B*D*C/c) + 2*G*D) * t^2 := by
    filter_upwards [hlocal] with t ht
    rcases ht with ⟨hpim, hclip, hgm, hjm, hji, hcm, hgb, ha, hd, hge⟩
    have hs := (population_continuous_full_joint_product_bias_bound M h he q L hL
      (e t) hpim c hc hclip k hgm hjm hji hcm B (D*|t|) (C*|t|) (G*|t|)
      hB (by positivity) (by positivity) (by positivity) hgb ha hd hge).2
    have hid : 2*(B*(D*|t|)*(C*|t|)/c) + 2*(G*|t|)*(D*|t|) =
        (2*(B*D*C/c)+2*G*D)*t^2 := by rw [← sq_abs t]; ring
    rwa [hid] at hs
  have hz : (∫ o : Obs X Z, psiFullProd L (e 0) k o ∂observationLaw M) = target := by
    have hzero := hb.self_of_nhds
    simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero] at hzero
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _)))
  have ho : (fun t : ℝ => (∫ o : Obs X Z, psiFullProd L (e t) k o
      ∂observationLaw M) - ∫ o : Obs X Z, psiFullProd L (e 0) k o ∂observationLaw M)
      =O[𝓝 0] (fun t : ℝ => t^2) := by
    apply Asymptotics.IsBigO.of_bound (2*(B*D*C/c)+2*G*D)
    filter_upwards [hb] with t ht
    simpa only [hz, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)] using ht
  apply HasDerivAt.of_isLittleO
  simpa only [smul_zero, sub_zero] using
    ho.trans_isLittleO (Asymptotics.isLittleO_pow_id (𝕜 := ℝ) (by norm_num : 1 < 2))

end Papers.TbsPrteOptimalTransport
