module
public import Papers.TbsPrteOptimalTransport.Helpers.JointTailPopulation
public import Papers.TbsPrteOptimalTransport.Helpers.IPWRegressionRemainder
/-! Fitted terminal scores: tower identification and second-order conditional bias.
The fitted nuisance vector need not lie on an admissible affine path. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set
open scoped Classical

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- Integrability, not just the value of the integral, transfers through the
-- model's conditional instrument kernel.
-- @node: population_instrument_finite_mean_integrable
/-- If an instrument–covariate function is [measurable](hyp:hw) and
[integrable under the observation law](hyp:hi), then [its average over the true
conditional instrument probabilities is integrable under the covariate law](goal). -/
lemma population_instrument_finite_mean_integrable (w : Z × X → ℝ) (hw : Measurable w)
    (hi : Integrable (fun o : Obs X Z => w (o.2.1, o.1)) (observationLaw M)) :
    Integrable (fun x => ∑ z, instProb M z x * w (z, x)) (xLaw M) := by
  haveI := M.instKernel_markov
  have hf : Measurable (fun o : Obs X Z => w (o.2.1, o.1)) := by fun_prop
  have hobs := M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
  have hi' : Integrable (fun s => w (M.Zv s, M.Xv s)) M.law.toMeasure :=
    (integrable_map_measure hf.aestronglyMeasurable hobs.aemeasurable).mp hi
  have hpair : StronglyMeasurable (fun p : X × Z => w (p.2, p.1)) := by fun_prop
  have hc := condExp_prod_ae_eq_integral_condDistrib M.measX M.measZ.aemeasurable hpair hi'
  have hver := ae_of_ae_map M.measX.aemeasurable M.instKernel_version
  have heq : M.law.toMeasure[(fun s => w (M.Zv s, M.Xv s)) |
      MeasurableSpace.comap M.Xv inferInstance] =ᵐ[M.law.toMeasure]
      (fun s => ∑ z, instProb M z (M.Xv s) * w (z, M.Xv s)) := by
    filter_upwards [hc, hver] with s hs hv
    rw [hs, ← hv, integral_fintype (Integrable.of_finite)]
    rfl
  have hsum : Measurable (fun x => ∑ z, instProb M z x * w (z, x)) := by
    apply Finset.measurable_sum
    intro z hz
    exact ((Kernel.measurable_coe _ (measurableSet_singleton z)).ennreal_toReal).mul
      (hw.comp (measurable_const.prodMk measurable_id))
  exact (integrable_map_measure hsum.aestronglyMeasurable M.measX.aemeasurable).mpr
    ((integrable_condExp (μ := M.law.toMeasure)
      (m := MeasurableSpace.comap M.Xv inferInstance)
      (f := fun s => w (M.Zv s, M.Xv s))).congr heq)

-- The expectation uses the true instrument masses and treatment mean,
-- while every coefficient in the evaluated score is fitted.
-- @node: fitted_tail_finite_mean
/-- If [there is at least one propensity level](hyp:hK) and [the baseline and
policy propensities obey the specified level ordering](hyp:hOrder), then [the
true-instrument average of the fitted tail score equals the minimum outcome times
the sum of the linearized policy mass, minus the fitted terminal propensity times
the true tail mass, plus the terminal propensity error times the true terminal
level mass and the fitted tail-to-level-mass ratio](goal). -/
lemma fitted_tail_finite_mean (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (e : NuisanceBin L) (x : X) :
    (∑ z, instProb M z x * commonTailScore M phi dphi L
      e.prop e.pLev e.piLev e.gammaTail (x, z, M.prop z x, 0)) =
      M.yMin * ((∑ z ∈ policyUnion L L.K 1, instProb M z x *
        (phi z x (e.prop z x) + dphi z x (e.prop z x) * (M.prop z x - e.prop z x))) -
        positiveValue e.pLev L.K x * gammaTail M L x +
        e.gammaTail x / positiveValue e.piLev L.K x *
          ((positiveValue e.pLev L.K x - L.pLev L.K x) * (levelSetProb M L).1 L.K x)) := by
  have hi : 1 ≤ L.K ∧ L.K ≤ L.K := ⟨hK, le_rfl⟩
  have hlevel : ∀ z ∈ L.S L.K,
      M.prop z x = positiveValue (eta0Bin M L).pLev L.K x := by
    intro z hz
    simpa only [positiveValue, dif_pos hi, eta0Bin] using
      (hOrder.2.2.2.2.2.1 x L.K z le_rfl).mp hz
  have hpi : ∑ z ∈ L.S L.K, instProb M z x =
      positiveValue (eta0Bin M L).piLev L.K x := by
    simp only [positiveValue, dif_pos hi, eta0Bin, levelSetProb]
  have hg : ∑ z ∈ policyUnion L L.K 1, instProb M z x = gammaTail M L x := rfl
  have h := commonTailScore_joint_finite_conditional_mean M phi dphi L hK
    M.prop (fun z x => e.prop z x - M.prop z x)
    (eta0Bin M L).pLev (fun k x => e.pLev k x - (eta0Bin M L).pLev k x)
    (eta0Bin M L).piLev (fun k x => e.piLev k x - (eta0Bin M L).piLev k x)
    (gammaTail M L) (fun x => e.gammaTail x - gammaTail M L x)
    x (fun z => instProb M z x) 1 hlevel hpi hg
  simp only [one_mul, add_sub_cancel, positiveValue, dif_pos hi, eta0Bin] at h ⊢
  have hpol (z : Z) : phi z x (e.prop z x) -
      dphi z x (e.prop z x) * (e.prop z x - M.prop z x) =
      phi z x (e.prop z x) + dphi z x (e.prop z x) * (M.prop z x - e.prop z x) := by ring
  simpa only [hpol] using h

-- The structural tower identity supplies the mean of the actual fitted score;
-- no conditional score-mean identity is added as a hypothesis.
-- @node: fitted_tail_population_mean
/-- Under [threshold crossing](hyp:h), a [valid policy map](hyp:hphi) with
[the specified derivative](hyp:hDiff) and [a bounded Lipschitz derivative](hyp:hDerivative),
[a positive number of levels](hyp:hK), and [invariant baseline and policy level
ordering](hyp:hOrder), suppose [the fitted binary nuisances are admissible](hyp:he),
[the clipping constant is positive](hyp:hc), and [the fitted terminal level mass
is almost surely at least that constant](hyp:hclip). Then [the fitted tail score
is integrable and its population mean is the covariate average of the minimum
outcome times the linearized policy mass minus the fitted terminal propensity
times the true tail mass, plus the terminal propensity error times the true level
mass and the fitted tail-to-level-mass ratio](goal). -/
lemma fitted_tail_population_mean (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (e : NuisanceBin L) (he : BinAdmissible M L e)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ᵐ x ∂xLaw M, c ≤ positiveValue e.piLev L.K x) :
    Integrable (commonTailScore M phi dphi L e.prop e.pLev e.piLev e.gammaTail)
      (observationLaw M) ∧
    (∫ o, commonTailScore M phi dphi L e.prop e.pLev e.piLev e.gammaTail o
      ∂observationLaw M) =
      ∫ x, M.yMin * ((∑ z ∈ policyUnion L L.K 1, instProb M z x *
        (phi z x (e.prop z x) + dphi z x (e.prop z x) * (M.prop z x - e.prop z x))) -
        positiveValue e.pLev L.K x * gammaTail M L x +
        e.gammaTail x / positiveValue e.piLev L.K x *
          ((positiveValue e.pLev L.K x - L.pLev L.K x) * (levelSetProb M L).1 L.K x))
        ∂xLaw M := by
  refine ⟨commonTailScore_integrable_of_binary_admissible M phi dphi hphi hDiff
    hDerivative L hK e he c hc hclip, ?_⟩
  rw [population_commonTailScore_finite_mean_of_binary_admissible M h phi dphi
    hphi hDiff hDerivative L hK e he c hc hclip]
  simp_rw [fitted_tail_finite_mean M phi dphi L hK hOrder e]

-- Policy Taylor errors are quadratic; baseline regression errors multiply
-- denominator and terminal-weight errors. There is no first-order weight term.
-- @node: fitted_tail_conditional_bias_bound
/-- Suppose [the policy has the specified derivative](hyp:hd), [the Lipschitz
constant is nonnegative](hyp:hLip), and [the derivative is Lipschitz on the unit
interval with that constant](hyp:hlip). With [at least one level](hyp:hK),
[invariant baseline and policy level ordering](hyp:hOrder), [a positive clipping
constant](hyp:hc), [a fitted terminal level mass at least that constant](hyp:hden),
and [fitted propensities in the unit interval on the tail policy union](hyp:hph),
[the absolute conditional tail-score bias is at most the absolute minimum outcome
times the sum of the instrument-weighted quadratic propensity errors and the
terminal propensity error times the tail-mass and level-mass errors, weighted by
their true counterparts and divided by the clipping constant](goal). -/
lemma fitted_tail_conditional_bias_bound
    (phi dphi : Z → X → ℝ → ℝ) (hd : PolicyDifferentiable phi dphi)
    (Lip : ℝ) (hLip : 0 ≤ Lip)
    (hlip : ∀ z x a b, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 →
      |dphi z x a - dphi z x b| ≤ Lip * |a - b|)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (e : NuisanceBin L) (x : X) (c : ℝ) (hc : 0 < c)
    (hden : c ≤ positiveValue e.piLev L.K x)
    (hph : ∀ z ∈ policyUnion L L.K 1, e.prop z x ∈ Icc (0 : ℝ) 1) :
    |(∑ z, instProb M z x * commonTailScore M phi dphi L
        e.prop e.pLev e.piLev e.gammaTail (x, z, M.prop z x, 0)) -
      M.yMin * ((∑ z ∈ policyUnion L L.K 1, instProb M z x * phi z x (M.prop z x)) -
        L.pLev L.K x * gammaTail M L x)| ≤
      |M.yMin| * ((∑ z ∈ policyUnion L L.K 1,
        instProb M z x * (Lip * (e.prop z x - M.prop z x)^2)) +
        |positiveValue e.pLev L.K x - L.pLev L.K x| *
          (|gammaTail M L x| * |positiveValue e.piLev L.K x - (levelSetProb M L).1 L.K x| +
            |e.gammaTail x - gammaTail M L x| * |(levelSetProb M L).1 L.K x|) / c) := by
  have hi : 1 ≤ L.K ∧ L.K ≤ L.K := ⟨hK, le_rfl⟩
  have hb := tail_joint_finite_mean_remainder_bound phi dphi hd Lip hLip hlip
    (policyUnion L L.K 1) x (fun z => M.prop z x)
    (fun z => e.prop z x - M.prop z x) (fun z => instProb M z x)
    (L.pLev L.K x) (positiveValue e.pLev L.K x - L.pLev L.K x)
    ((levelSetProb M L).1 L.K x)
    (positiveValue e.piLev L.K x - (levelSetProb M L).1 L.K x)
    (gammaTail M L x) (e.gammaTail x - gammaTail M L x) M.yMin 1 c hc
    (by simpa using hden) (fun z _ => ENNReal.toReal_nonneg)
    (fun z _ => M.rangeProp z x) (by simpa using hph)
  simp only [one_mul, add_sub_cancel, one_pow, mul_one] at hb
  rw [fitted_tail_finite_mean M phi dphi L hK hOrder e]
  have hpol (z : Z) : phi z x (e.prop z x) -
      dphi z x (e.prop z x) * (e.prop z x - M.prop z x) =
      phi z x (e.prop z x) + dphi z x (e.prop z x) * (M.prop z x - e.prop z x) := by ring
  simpa only [hpol] using hb

-- Clipping gives a measurable representative on the policy's documented
-- domain. Kernel averaging then supplies conditional-mean integrability.
-- @node: fitted_tail_finite_mean_integrable
/-- Under [threshold crossing](hyp:h), a [valid policy map](hyp:hphi) with
[the specified derivative](hyp:hDiff) and [a bounded Lipschitz derivative](hyp:hDerivative),
[at least one level](hyp:hK), [admissible fitted binary nuisances](hyp:he),
[a positive clipping constant](hyp:hc), and [an almost sure lower bound by that
constant on the fitted terminal level mass](hyp:hclip), [the true-instrument
average of the fitted tail score evaluated at the true treatment mean is
integrable under the covariate law](goal). -/
lemma fitted_tail_finite_mean_integrable (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (c : ℝ) (hc : 0 < c)
    (hclip : ∀ᵐ x ∂xLaw M, c ≤ positiveValue e.piLev L.K x) :
    Integrable (fun x => ∑ z, instProb M z x * commonTailScore M phi dphi L
      e.prop e.pLev e.piLev e.gammaTail (x, z, M.prop z x, 0)) (xLaw M) := by
  let pc : Z → X → ℝ := fun z x => max 0 (min 1 (e.prop z x))
  have hpc : Measurable (fun zx : Z × X => pc zx.1 zx.2) := by
    apply measurable_from_prod_countable_right
    intro z
    have hm := he.2.1 z
    dsimp only [pc]
    fun_prop
  have hpcR : ∀ z x, pc z x ∈ Icc (0 : ℝ) 1 := fun z x =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hq : Measurable (fun zx : Z × X => phi zx.1 zx.2 (pc zx.1 zx.2)) :=
    hphi.1.comp (measurable_fst.prodMk
      (measurable_snd.prodMk (hpc.subtype_mk (h := fun zx => hpcR zx.1 zx.2))))
  have hdq := policy_derivative_graph_measurable phi dphi hphi hDiff pc hpc hpcR
  have hi : 1 ≤ L.K ∧ L.K ≤ L.K := ⟨hK, le_rfl⟩
  have hpk : Measurable (positiveValue e.pLev L.K) := by
    change Measurable (fun x => positiveValue e.pLev L.K x)
    simpa only [positiveValue, dif_pos hi] using (he.2.2.2.1 ⟨L.K,hi⟩).1
  have hpi : Measurable (positiveValue e.piLev L.K) := by
    change Measurable (fun x => positiveValue e.piLev L.K x)
    simpa only [positiveValue, dif_pos hi] using (he.2.2.2.1 ⟨L.K,hi⟩).2.2
  have hgm : Measurable e.gammaTail := he.2.2.2.2.2.2.2.2.2.2.2.2
  have hind (s : Finset Z) : Measurable (fun zx : Z × X => indicator (zx.1 ∈ s)) := by
    unfold indicator
    exact Measurable.ite (s.finite_toSet.measurableSet.preimage measurable_fst)
      measurable_const measurable_const
  have hmprop := h.2.1
  have hf : Measurable (fun zx : Z × X => commonTailScore M phi dphi L
      pc e.pLev e.piLev e.gammaTail (zx.2, zx.1, M.prop zx.1 zx.2, 0)) := by
    unfold commonTailScore
    first
    | fun_prop
    | apply Measurable.sub
      · exact ((measurable_const.mul (hind _)).mul (hq.sub (hpk.comp measurable_snd))).add
          (((measurable_const.mul (hind _)).mul hdq).mul (h.2.1.sub hpc))
      · split_ifs <;> fun_prop
  have heq : ∀ᵐ x ∂xLaw M, ∀ z, pc z x = e.prop z x := by
    filter_upwards [ae_all_iff.mpr he.1] with x hx
    intro z
    simp only [pc, min_eq_right (hx z).2, max_eq_right (hx z).1]
  have hic := commonTailScore_centered_integrable_of_binary_admissible M h
    phi dphi hphi hDiff hDerivative L hK e he c hc hclip
  have hip : Integrable (fun o : Obs X Z => commonTailScore M phi dphi L
      pc e.pLev e.piLev e.gammaTail (o.1, o.2.1, M.prop o.2.1 o.1, 0))
      (observationLaw M) := by
    apply hic.congr
    filter_upwards [observationLaw_covariate_ae M _ heq] with o ho
    simp only [commonTailScore, ho o.2.1]
  apply (population_instrument_finite_mean_integrable M _ hf hip).congr
  filter_upwards [heq] with x hx
  apply Finset.sum_congr rfl
  intro z hz
  simp only [commonTailScore, hx z]

-- The actual fitted tail score has quadratic bias in the paper's L2 errors.
-- Clipping derives all moments used below, including the cross-products.
-- @node: fitted_tail_bias_L2_bound
/-- Under [threshold crossing](hyp:h), a [valid policy map](hyp:hphi) with
[the specified derivative](hyp:hd) and [a bounded Lipschitz derivative](hyp:hDerivative),
assume [a nonnegative Lipschitz constant](hyp:hLip) [bounds derivative differences
on the unit interval](hyp:hlip), [there is at least one level](hyp:hK), and
[baseline and policy level ordering is invariant](hyp:hOrder). If [the fitted
nuisances](hyp:he) and [true nuisances](hyp:he0) are admissible, [baseline overlap
holds](hyp:hov), [the clipping constant is positive](hyp:hc), and [the fitted
terminal level mass is almost surely bounded below by it](hyp:hclip), then [the
absolute population tail-score bias is bounded by the absolute minimum outcome
times the Lipschitz constant times the sum of squared propensity L2 errors, plus
the terminal propensity L2 error times the sum of the terminal level-mass and
tail-mass L2 errors divided by the clipping constant](goal). -/
lemma fitted_tail_bias_L2_bound (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (Lip : ℝ) (hLip : 0 ≤ Lip)
    (hlip : ∀ z x a b, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 →
      |dphi z x a - dphi z x b| ≤ Lip * |a - b|)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (e : NuisanceBin L) (he : BinAdmissible M L e)
    (he0 : BinAdmissible M L (eta0Bin M L))
    (cpi c : ℝ) (hov : BaselineOverlapWitness M L cpi) (hc : 0 < c)
    (hclip : ∀ᵐ x ∂xLaw M, c ≤ positiveValue e.piLev L.K x) :
    let err := fun z x => e.prop z x - M.prop z x
    let ep := fun x => positiveValue e.pLev L.K x - L.pLev L.K x
    let et := fun x => positiveValue e.piLev L.K x - (levelSetProb M L).1 L.K x
    let eg := fun x => e.gammaTail x - gammaTail M L x
    |(∫ o, commonTailScore M phi dphi L e.prop e.pLev e.piLev e.gammaTail o
        ∂observationLaw M) -
      (∫ o, commonTailScore M phi dphi L (eta0Bin M L).prop (eta0Bin M L).pLev
        (eta0Bin M L).piLev (eta0Bin M L).gammaTail o ∂observationLaw M)| ≤
      |M.yMin| * (Lip * (∑ z ∈ policyUnion L L.K 1, (eLpNorm (err z) 2 (xLaw M)).toReal ^ 2) +
        (eLpNorm ep 2 (xLaw M)).toReal *
          ((eLpNorm et 2 (xLaw M)).toReal + (eLpNorm eg 2 (xLaw M)).toReal) / c) := by
  dsimp only
  let err := fun z x => e.prop z x - M.prop z x
  let ep := fun x => positiveValue e.pLev L.K x - L.pLev L.K x
  let et := fun x => positiveValue e.piLev L.K x - (levelSetProb M L).1 L.K x
  let eg := fun x => e.gammaTail x - gammaTail M L x
  let F := fun (e' : NuisanceBin L) x => ∑ z, instProb M z x * commonTailScore M phi dphi L
    e'.prop e'.pLev e'.piLev e'.gammaTail (x, z, M.prop z x, 0)
  let E := fun x => |M.yMin| * (Lip * (∑ z ∈ policyUnion L L.K 1, (err z x)^2) +
    (|ep x * et x| + |ep x * eg x|) / c)
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  haveI := M.instKernel_markov
  have hi : 1 ≤ L.K ∧ L.K ≤ L.K := ⟨hK, le_rfl⟩
  have hunit (f : X → ℝ) (hf : Measurable f)
      (hb : ∀ᵐ x ∂xLaw M, f x ∈ Icc (0 : ℝ) 1) : MemLp f 2 (xLaw M) := by
    apply MemLp.of_bound hf.aestronglyMeasurable 1
    filter_upwards [hb] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
    exact hx.2
  have hp : ∀ z, MemLp (err z) 2 (xLaw M) := by
    intro z
    exact (hunit _ (he.2.1 z) (he.1 z)).sub
      (hunit _ (h.2.1.comp (measurable_const.prodMk measurable_id))
        (Filter.Eventually.of_forall (M.rangeProp z)))
  have hep : MemLp ep 2 (xLaw M) := by
    simpa only [ep, positiveValue, dif_pos hi, eta0Bin, Pi.sub_def] using
      (hunit _ (he.2.2.2.1 ⟨L.K,hi⟩).1
        ((he.2.2.1 ⟨L.K,hi⟩).mono (fun _ hx => hx.1))).sub
      (hunit _ (he0.2.2.2.1 ⟨L.K,hi⟩).1
        ((he0.2.2.1 ⟨L.K,hi⟩).mono (fun _ hx => hx.1)))
  have het : MemLp et 2 (xLaw M) := by
    simpa only [et, positiveValue, dif_pos hi, eta0Bin, Pi.sub_def] using
      (hunit _ (he.2.2.2.1 ⟨L.K,hi⟩).2.2
        ((he.2.2.1 ⟨L.K,hi⟩).mono (fun _ hx => hx.2.2))).sub
      (hunit _ (he0.2.2.2.1 ⟨L.K,hi⟩).2.2
        ((he0.2.2.1 ⟨L.K,hi⟩).mono (fun _ hx => hx.2.2)))
  have heg : MemLp eg 2 (xLaw M) :=
    (hunit _ he.2.2.2.2.2.2.2.2.2.2.2.2 he.2.2.2.2.2.2.2.2.2.2.2.1).sub
      (hunit _ he0.2.2.2.2.2.2.2.2.2.2.2.2 he0.2.2.2.2.2.2.2.2.2.2.2.1)
  have isq (z : Z) : Integrable (fun x => (err z x)^2) (xLaw M) := (hp z).integrable_sq
  have ipt : Integrable (fun x => |ep x * et x|) (xLaw M) := (hep.integrable_mul het).abs
  have ipg : Integrable (fun x => |ep x * eg x|) (xLaw M) := (hep.integrable_mul heg).abs
  have iE : Integrable E (xLaw M) :=
    (((integrable_finsetSum _ (fun z _ => isq z)).const_mul Lip).fun_add
      ((ipt.fun_add ipg).div_const c)).const_mul |M.yMin|
  have hclip0 : ∀ᵐ x ∂xLaw M, cpi ≤ positiveValue (eta0Bin M L).piLev L.K x := by
    exact Filter.Eventually.of_forall (fun x => by
      simpa only [positiveValue, dif_pos hi, eta0Bin] using hov.2 x L.K hK le_rfl)
  have ifit := fitted_tail_finite_mean_integrable M h phi dphi hphi hd hDerivative
    L hK e he c hc hclip
  have i0 := fitted_tail_finite_mean_integrable M h phi dphi hphi hd hDerivative
    L hK (eta0Bin M L) he0 cpi hov.1 hclip0
  have h0 (x : X) : F (eta0Bin M L) x = M.yMin *
      ((∑ z ∈ policyUnion L L.K 1, instProb M z x * phi z x (M.prop z x)) -
        L.pLev L.K x * gammaTail M L x) := by
    simpa only [F, eta0Bin, sub_self, mul_zero, zero_mul, add_zero, positiveValue, dif_pos hi]
      using fitted_tail_finite_mean M phi dphi L hK hOrder (eta0Bin M L) x
  have hbound : ∀ᵐ x ∂xLaw M, |F e x - F (eta0Bin M L) x| ≤ E x := by
    filter_upwards [hclip, ae_all_iff.mpr he.1, he0.2.2.1 ⟨L.K,hi⟩,
      he0.2.2.2.2.2.2.2.2.2.2.2.1] with x hcx hpx h0x hgx
    rw [h0]
    have hb := fitted_tail_conditional_bias_bound M phi dphi hd Lip hLip hlip
      L hK hOrder e x c hc hcx (fun z _ => hpx z)
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply add_le_add
    · rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro z hz
      have hm : instProb M z x ≤ 1 := measureReal_le_one
      simpa only [one_mul, err] using
        mul_le_mul_of_nonneg_right hm (mul_nonneg hLip (sq_nonneg (err z x)))
    · apply div_le_div_of_nonneg_right _ hc.le
      have hgb : |gammaTail M L x| ≤ 1 := by
        change gammaTail M L x ∈ Icc (0 : ℝ) 1 at hgx
        rw [abs_of_nonneg hgx.1]
        exact hgx.2
      have ht0 : (levelSetProb M L).1 L.K x ∈ Icc (0 : ℝ) 1 := h0x.2.2
      have htb : |(levelSetProb M L).1 L.K x| ≤ 1 := by
        rw [abs_of_nonneg ht0.1]
        exact ht0.2
      change |ep x| * (|gammaTail M L x| * |et x| +
        |eg x| * |(levelSetProb M L).1 L.K x|) ≤ |ep x * et x| + |ep x * eg x|
      calc
        _ ≤ |ep x| * (|et x| + |eg x|) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact add_le_add (by simpa using mul_le_mul_of_nonneg_right hgb (abs_nonneg (et x)))
            (by simpa using mul_le_mul_of_nonneg_left htb (abs_nonneg (eg x)))
        _ = _ := by rw [abs_mul, abs_mul]; ring
  rw [population_commonTailScore_finite_mean_of_binary_admissible M h phi dphi hphi hd
    hDerivative L hK e he c hc hclip,
    population_commonTailScore_finite_mean_of_binary_admissible M h phi dphi hphi hd
    hDerivative L hK (eta0Bin M L) he0 cpi hov.1 hclip0]
  change |(∫ x, F e x ∂xLaw M) - (∫ x, F (eta0Bin M L) x ∂xLaw M)| ≤ _
  rw [← integral_sub ifit i0]
  have hsq (z : Z) : (∫ x, (err z x)^2 ∂xLaw M) ≤
      (eLpNorm (err z) 2 (xLaw M)).toReal ^ 2 := by
    simpa only [← sq, abs_sq] using
      Causalean.Stat.integral_abs_mul_le_eLpNorm_mul_eLpNorm (hp z) (hp z)
  calc
    _ ≤ ∫ x, |F e x - F (eta0Bin M L) x| ∂xLaw M := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x => F e x - F (eta0Bin M L) x)
    _ ≤ ∫ x, E x ∂xLaw M := integral_mono_ae (ifit.sub' i0).abs iE hbound
    _ = |M.yMin| * (Lip * (∑ z ∈ policyUnion L L.K 1, ∫ x, (err z x)^2 ∂xLaw M) +
        ((∫ x, |ep x * et x| ∂xLaw M) + (∫ x, |ep x * eg x| ∂xLaw M)) / c) := by
      dsimp only [E]
      rw [integral_const_mul, integral_add
        ((integrable_finsetSum _ (fun z _ => isq z)).const_mul Lip)
        ((ipt.fun_add ipg).div_const c), integral_const_mul,
        integral_finsetSum _ (fun z _ => isq z), integral_div, integral_add ipt ipg]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun z _ => hsq z)) hLip
      · apply div_le_div_of_nonneg_right _ hc.le
        rw [mul_add]
        exact add_le_add (Causalean.Stat.integral_abs_mul_le_eLpNorm_mul_eLpNorm hep het)
          (Causalean.Stat.integral_abs_mul_le_eLpNorm_mul_eLpNorm hep heg)

end Papers.TbsPrteOptimalTransport
