module
public import Papers.TbsPrteOptimalTransport.Helpers.JointTailRemainder
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationInstrumentMoments
/-! Population identification and integrated simultaneous tail-score cancellation. -/
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

-- Center at the true treatment mean even when every fitted field moves.
-- @node: commonTailScore_treatment_centered_decomposition
/-- If [there is at least one propensity level](hyp:hK), then [the common tail score
equals its value with treatment replaced by the true conditional mean and outcome
set to zero, plus the treatment residual times the outcome floor times the difference
between the tail-region policy derivative and the final-level indicator weighted by
the tail-weight-to-assignment-denominator ratio](goal). -/
lemma commonTailScore_treatment_centered_decomposition
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (hK : LevelCountPos L.K)
    (prop : Z → X → ℝ) (pk pi : PositiveIndex L.K → X → ℝ)
    (g : X → ℝ) (o : Obs X Z) :
    commonTailScore M phi dphi L prop pk pi g o =
      commonTailScore M phi dphi L prop pk pi g (o.1, o.2.1, M.prop o.2.1 o.1, 0) +
      (M.yMin * (indicator (o.2.1 ∈ policyUnion L L.K 1) *
        dphi o.2.1 o.1 (prop o.2.1 o.1) -
        g o.1 / positiveValue pi L.K o.1 * indicator (o.2.1 ∈ L.S L.K))) *
        (o.2.2.1 - M.prop o.2.1 o.1) := by
  rw [commonTailScore_residual_decomposition M phi dphi L hK,
    commonTailScore_residual_decomposition M phi dphi L hK]
  ring

-- The tower property first removes W's residual, then averages over Z.
-- These are analytic conditions on the two explicit summands, not an
-- assumption of either the tail mean identity or its derivative.
-- @node: population_commonTailScore_finite_conditional_mean
/-- If [the model satisfies threshold crossing](hyp:h), [there is at least one level](hyp:hK),
[the treatment-centered score is measurable in instrument and covariates](hyp:hf),
[its treatment-residual coefficient is measurable in those variables](hyp:hw),
[the treatment-centered score is observation-integrable](hyp:hi), and [the coefficient
times the treatment residual is observation-integrable](hyp:hr), then [the common
tail score is observation-integrable and its population mean equals the covariate
average of the true-instrument-probability-weighted score with treatment fixed at
its true conditional mean and outcome set to zero](goal). -/
lemma population_commonTailScore_finite_conditional_mean
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (prop : Z → X → ℝ) (pk pi : PositiveIndex L.K → X → ℝ) (g : X → ℝ)
    (hf : Measurable (fun zx : Z × X => commonTailScore M phi dphi L
      prop pk pi g (zx.2, zx.1, M.prop zx.1 zx.2, 0)))
    (hw : Measurable (fun zx : Z × X => M.yMin *
      (indicator (zx.1 ∈ policyUnion L L.K 1) * dphi zx.1 zx.2 (prop zx.1 zx.2) -
        g zx.2 / positiveValue pi L.K zx.2 * indicator (zx.1 ∈ L.S L.K))))
    (hi : Integrable (fun o : Obs X Z => commonTailScore M phi dphi L
      prop pk pi g (o.1, o.2.1, M.prop o.2.1 o.1, 0)) (observationLaw M))
    (hr : Integrable (fun o : Obs X Z => (M.yMin *
      (indicator (o.2.1 ∈ policyUnion L L.K 1) * dphi o.2.1 o.1 (prop o.2.1 o.1) -
        g o.1 / positiveValue pi L.K o.1 * indicator (o.2.1 ∈ L.S L.K))) *
        (o.2.2.1 - M.prop o.2.1 o.1)) (observationLaw M)) :
    Integrable (commonTailScore M phi dphi L prop pk pi g) (observationLaw M) ∧
    (∫ o, commonTailScore M phi dphi L prop pk pi g o ∂observationLaw M) =
      ∫ x, ∑ z, instProb M z x * commonTailScore M phi dphi L
        prop pk pi g (x, z, M.prop z x, 0) ∂xLaw M := by
  have hz := population_treatment_weighted_integral_zero M h _ hw hr
  have heq : commonTailScore M phi dphi L prop pk pi g = fun o =>
      commonTailScore M phi dphi L prop pk pi g (o.1, o.2.1, M.prop o.2.1 o.1, 0) +
      (M.yMin * (indicator (o.2.1 ∈ policyUnion L L.K 1) *
        dphi o.2.1 o.1 (prop o.2.1 o.1) -
        g o.1 / positiveValue pi L.K o.1 * indicator (o.2.1 ∈ L.S L.K))) *
        (o.2.2.1 - M.prop o.2.1 o.1) := by
    funext o
    exact commonTailScore_treatment_centered_decomposition M phi dphi L hK prop pk pi g o
  constructor
  · rw [heq]
    exact hi.fun_add hr
  · conv_lhs => rw [heq]
    rw [integral_add hi hr, hz, add_zero]
    exact population_instrument_integral M _ hf hi

-- Identification of the actual simultaneous affine score path. Neither the
-- true residual nor the finite instrument law is replaced by a fitted law.
-- @node: population_commonTailScore_joint_path_mean
/-- If [the model satisfies threshold crossing](hyp:h), [there is at least one level](hyp:hK),
[the levels preserve the ordering of the true and policy propensities](hyp:hOrder),
[the treatment-centered score along the nuisance path is measurable](hyp:hf), [its
treatment-residual coefficient is measurable](hyp:hw), [the treatment-centered score
is observation-integrable](hyp:hi), and [the coefficient times the treatment residual
is observation-integrable](hyp:hr), then [the population mean of the score along the
simultaneous affine path equals the covariate integral of the outcome floor times
the true-probability-weighted sum of debiased tail policies, minus the perturbed
final-level propensity times the true tail weight, plus the path parameter times
the perturbed tail-weight-to-denominator ratio times the final-level propensity
direction and true denominator](goal). -/
lemma population_commonTailScore_joint_path_mean
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (del : NuisanceBin L) (t : ℝ)
    (hf : Measurable (fun zx : Z × X => commonTailScore M phi dphi L
      (eta0Bin M L + t • del).prop (eta0Bin M L + t • del).pLev
      (eta0Bin M L + t • del).piLev (eta0Bin M L + t • del).gammaTail
      (zx.2, zx.1, M.prop zx.1 zx.2, 0)))
    (hw : Measurable (fun zx : Z × X => M.yMin *
      (indicator (zx.1 ∈ policyUnion L L.K 1) *
        dphi zx.1 zx.2 ((eta0Bin M L + t • del).prop zx.1 zx.2) -
        (eta0Bin M L + t • del).gammaTail zx.2 /
          positiveValue (eta0Bin M L + t • del).piLev L.K zx.2 *
            indicator (zx.1 ∈ L.S L.K))))
    (hi : Integrable (fun o : Obs X Z => commonTailScore M phi dphi L
      (eta0Bin M L + t • del).prop (eta0Bin M L + t • del).pLev
      (eta0Bin M L + t • del).piLev (eta0Bin M L + t • del).gammaTail
      (o.1, o.2.1, M.prop o.2.1 o.1, 0)) (observationLaw M))
    (hr : Integrable (fun o : Obs X Z => (M.yMin *
      (indicator (o.2.1 ∈ policyUnion L L.K 1) *
        dphi o.2.1 o.1 ((eta0Bin M L + t • del).prop o.2.1 o.1) -
        (eta0Bin M L + t • del).gammaTail o.1 /
          positiveValue (eta0Bin M L + t • del).piLev L.K o.1 *
            indicator (o.2.1 ∈ L.S L.K))) *
        (o.2.2.1 - M.prop o.2.1 o.1)) (observationLaw M)) :
    (∫ o, commonTailScore M phi dphi L (eta0Bin M L + t • del).prop
      (eta0Bin M L + t • del).pLev (eta0Bin M L + t • del).piLev
      (eta0Bin M L + t • del).gammaTail o ∂observationLaw M) =
    ∫ x, M.yMin * ((∑ z ∈ policyUnion L L.K 1, instProb M z x *
      (phi z x (M.prop z x + t * del.prop z x) -
        t * (dphi z x (M.prop z x + t * del.prop z x) * del.prop z x))) -
      (positiveValue (eta0Bin M L).pLev L.K x + t * positiveValue del.pLev L.K x) *
        (eta0Bin M L).gammaTail x +
      t * (((eta0Bin M L).gammaTail x + t * del.gammaTail x) /
        (positiveValue (eta0Bin M L).piLev L.K x + t * positiveValue del.piLev L.K x) *
          (positiveValue del.pLev L.K x * positiveValue (eta0Bin M L).piLev L.K x)))
      ∂xLaw M := by
  rw [(population_commonTailScore_finite_conditional_mean M h phi dphi L hK
    _ _ _ _ hf hw hi hr).2]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  have hidx : 1 ≤ L.K ∧ L.K ≤ L.K := ⟨hK, le_rfl⟩
  have hlevel : ∀ z ∈ L.S L.K, M.prop z x = positiveValue (eta0Bin M L).pLev L.K x := by
    intro z hz
    simp only [positiveValue, dif_pos hidx, eta0Bin]
    exact (hOrder.2.2.2.2.2.1 x L.K z le_rfl).mp hz
  have hpi : ∑ z ∈ L.S L.K, instProb M z x = positiveValue (eta0Bin M L).piLev L.K x := by
    simp only [positiveValue, dif_pos hidx, eta0Bin, levelSetProb]
  exact commonTailScore_joint_finite_conditional_mean M phi dphi L hK
    M.prop del.prop (eta0Bin M L).pLev del.pLev (eta0Bin M L).piLev del.piLev
    (eta0Bin M L).gammaTail del.gammaTail x (fun z => instProb M z x) t
    hlevel hpi rfl

-- Uniform bounds on the three baseline directions give a common local
-- reciprocal bound. The scalar cancellation is integrated before differentiating.
-- @node: tail_baseline_joint_integral_orthogonality
/-- Suppose [the denominator lower bound is positive](hyp:hc), [the bounds on the
propensity, denominator, and tail-weight directions are nonnegative](hyp:hR,hC,hG),
[the jointly perturbed baseline expression is measurable for every path parameter](hyp:hmeas),
and [the initial negative propensity times tail weight is integrable](hyp:hbase).
If [almost everywhere the three directions obey those bounds, the initial denominator
lies between its lower bound and one, and the initial tail weight has absolute value
at most one](hyp:hbound), then [the integral of the negative perturbed propensity times
the initial tail weight, plus the path parameter times the perturbed tail-weight-to-denominator
ratio times the propensity direction and initial denominator, has derivative zero at zero](goal). -/
lemma tail_baseline_joint_integral_orthogonality {B : Type*} [MeasurableSpace B]
    (ν : Measure B) [IsProbabilityMeasure ν] (p dp pi dpi g dg : B → ℝ)
    (c R C G : ℝ) (hc : 0 < c) (hR : 0 ≤ R) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hmeas : ∀ t : ℝ, Measurable (fun b => -(p b + t * dp b) * g b +
      t * ((g b + t * dg b) / (pi b + t * dpi b) * (dp b * pi b))))
    (hbase : Integrable (fun b => -(p b) * g b) ν)
    (hbound : ∀ᵐ b ∂ν, |dp b| ≤ R ∧ |dpi b| ≤ C ∧ |dg b| ≤ G ∧
      pi b ∈ Icc c 1 ∧ |g b| ≤ 1) :
    HasDerivAt (fun t : ℝ => ∫ b, -(p b + t * dp b) * g b +
      t * ((g b + t * dg b) / (pi b + t * dpi b) * (dp b * pi b)) ∂ν) 0 0 := by
  let F : ℝ → B → ℝ := fun t b => -(p b + t * dp b) * g b +
    t * ((g b + t * dg b) / (pi b + t * dpi b) * (dp b * pi b))
  have h0 : F 0 = fun b => -(p b) * g b := by
    funext b
    simp only [F, zero_mul, add_zero]
  apply integral_local_quadratic_orthogonality ν F (R * (C+G) / (c/2))
    (by rw [h0]; exact hbase)
  have radius : 0 < c / (2*(C+1)) := by positivity
  filter_upwards [continuousAt_id.abs.eventually_lt_const (by simpa using radius)] with t ht
  change |t| < c / (2*(C+1)) at ht
  refine ⟨(hmeas t).aestronglyMeasurable, ?_⟩
  filter_upwards [hbound] with b hb
  rcases hb with ⟨hdb, hdib, hdgb, hpib, hgb⟩
  have hden : c/2 ≤ pi b + t * dpi b := by
    have hmul : |t * dpi b| ≤ |t| * C := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hdib (abs_nonneg t)
    have hsmall := (lt_div_iff₀ (by positivity : 0 < 2*(C+1))).mp ht
    nlinarith [neg_abs_le (t * dpi b), abs_nonneg t, hpib.1]
  have hpia : |pi b| ≤ 1 := by
    rw [abs_of_nonneg (by linarith [hpib.1])]
    exact hpib.2
  have hcoef : |dp b| * (|g b| * |dpi b| + |dg b| * |pi b|) / (c/2) ≤
      R * (C+G) / (c/2) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc
      _ ≤ R * (1*C + G*1) := by gcongr
      _ = _ := by ring
  have hb := tail_baseline_joint_remainder_bound (p b) (dp b) (pi b) (dpi b)
    (g b) (dg b) t (c/2) (by positivity) hden
  rw [h0]
  change |-(p b + t * dp b) * g b +
    t * ((g b + t * dg b) / (pi b + t * dpi b) * (dp b * pi b)) -
      (-(p b) * g b)| ≤ _
  convert! hb.trans (mul_le_mul_of_nonneg_left hcoef (sq_nonneg t)) using 1 <;> ring_nf

-- Policy directions need only L2 control. The local integrability hypotheses
-- concern the displayed summands and allow the finite sum to pass through the integral.
-- @node: tail_joint_finite_integral_orthogonality
/-- Suppose [the policy has the specified propensity derivative](hyp:hdphi), [its
Lipschitz constant is nonnegative](hyp:hLip), [its derivative obeys that uniform
Lipschitz bound on the unit interval](hyp:hlip), [the denominator lower bound is
positive](hyp:hc), and [the three baseline direction bounds are nonnegative](hyp:hR,hC,hG).
If [each policy propensity direction is square integrable](hyp:hdp), [instrument masses
lie between zero and one almost everywhere](hyp:hmass), [initial propensities do too](hyp:hp),
[their affine paths remain in that interval throughout a common neighborhood of zero](hyp:hpath),
[each weighted debiased policy term is locally integrable along the path](hyp:hipol),
[the joint baseline correction is locally integrable along the path](hyp:hibase),
[that correction is measurable at every path parameter](hyp:hmeas), and [almost
everywhere the baseline directions obey their bounds, the denominator lies between
its positive lower bound and one, and the tail weight has absolute value at most one](hyp:hbound),
then [the integral of the outcome-floor-scaled finite sum of debiased policies and
joint baseline correction has derivative zero at zero](goal). -/
lemma tail_joint_finite_integral_orthogonality
    (ν : Measure X) [IsProbabilityMeasure ν]
    (phi dphi : Z → X → ℝ → ℝ) (hdphi : PolicyDifferentiable phi dphi)
    (Lip : ℝ) (hLip : 0 ≤ Lip)
    (hlip : ∀ z x a b, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 →
      |dphi z x a - dphi z x b| ≤ Lip * |a-b|)
    (s : Finset Z) (p dp mass : Z → X → ℝ) (pk dpk pi dpi g dg : X → ℝ)
    (ymin c R C G : ℝ) (hc : 0 < c) (hR : 0 ≤ R) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hdp : ∀ z ∈ s, MemLp (dp z) 2 ν)
    (hmass : ∀ z ∈ s, ∀ᵐ x ∂ν, mass z x ∈ Icc (0 : ℝ) 1)
    (hp : ∀ z ∈ s, ∀ᵐ x ∂ν, p z x ∈ Icc (0 : ℝ) 1)
    (hpath : ∀ᶠ t : ℝ in nhds 0, ∀ z ∈ s, ∀ᵐ x ∂ν,
      p z x + t * dp z x ∈ Icc (0 : ℝ) 1)
    (hipol : ∀ᶠ t : ℝ in nhds 0, ∀ z ∈ s, Integrable (fun x => mass z x *
      (phi z x (p z x + t * dp z x) - t * (dphi z x (p z x + t * dp z x) * dp z x))) ν)
    (hibase : ∀ᶠ t : ℝ in nhds 0, Integrable (fun x =>
      -(pk x + t * dpk x) * g x +
        t * ((g x + t * dg x) / (pi x + t * dpi x) * (dpk x * pi x))) ν)
    (hmeas : ∀ t : ℝ, Measurable (fun x => -(pk x + t * dpk x) * g x +
      t * ((g x + t * dg x) / (pi x + t * dpi x) * (dpk x * pi x))))
    (hbound : ∀ᵐ x ∂ν, |dpk x| ≤ R ∧ |dpi x| ≤ C ∧ |dg x| ≤ G ∧
      pi x ∈ Icc c 1 ∧ |g x| ≤ 1) :
    HasDerivAt (fun t : ℝ => ∫ x, ymin *
      ((∑ z ∈ s, mass z x * (phi z x (p z x + t * dp z x) -
        t * (dphi z x (p z x + t * dp z x) * dp z x))) -
        (pk x + t * dpk x) * g x +
        t * ((g x + t * dg x) / (pi x + t * dpi x) * (dpk x * pi x))) ∂ν) 0 0 := by
  have hpol : ∀ z ∈ s, HasDerivAt (fun t : ℝ => ∫ x, mass z x *
      (phi z x (p z x + t * dp z x) -
        t * (dphi z x (p z x + t * dp z x) * dp z x)) ∂ν) 0 0 := by
    intro z hz
    apply policy_debiased_weighted_integral_orthogonality ν phi dphi hdphi
      Lip hLip hlip z (p z) (dp z) (mass z) (hdp z hz) (hmass z hz) (hp z hz)
    · exact hpath.mono (fun _ ht => ht z hz)
    · exact hipol.mono (fun _ ht => (ht z hz).aestronglyMeasurable)
    · simpa only [zero_mul, add_zero, sub_zero] using hipol.self_of_nhds z hz
  have hb := tail_baseline_joint_integral_orthogonality ν pk dpk pi dpi g dg
    c R C G hc hR hC hG hmeas
    (by simpa only [zero_mul, add_zero] using hibase.self_of_nhds) hbound
  have hs : HasDerivAt (fun t : ℝ => ∑ z ∈ s, ∫ x, mass z x *
      (phi z x (p z x + t * dp z x) -
        t * (dphi z x (p z x + t * dp z x) * dp z x)) ∂ν) 0 0 := by
    simpa only [Finset.sum_const_zero] using HasDerivAt.fun_sum hpol
  have hd := (hs.add hb).const_mul ymin
  simp only [add_zero, mul_zero] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [hipol, hibase] with t ht hb
  rw [integral_const_mul]
  have heq : (fun x => (∑ z ∈ s, mass z x *
      (phi z x (p z x + t * dp z x) - t * (dphi z x (p z x + t * dp z x) * dp z x))) -
      (pk x + t * dpk x) * g x +
        t * ((g x + t * dg x) / (pi x + t * dpi x) * (dpk x * pi x))) =
      (fun x => (∑ z ∈ s, mass z x *
        (phi z x (p z x + t * dp z x) - t * (dphi z x (p z x + t * dp z x) * dp z x))) +
        (-(pk x + t * dpk x) * g x +
          t * ((g x + t * dg x) / (pi x + t * dpi x) * (dpk x * pi x)))) := by
    funext x
    ring
  rw [heq, integral_add (integrable_finsetSum _ ht) hb, integral_finsetSum _ ht]
  rfl

end Papers.TbsPrteOptimalTransport
