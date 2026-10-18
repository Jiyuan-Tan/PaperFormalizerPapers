module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousBandSmoothReduction
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousBandPropensityRates
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousPoolingBias
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousHybridMean
/-! Propensity restoration in the remaining continuous smooth band correction.
The regression residual does not depend on the level propensity. Thus the
joint propensity/assignment cancellation also controls the smooth correction,
and the product bias reduces to a hybrid with true band regressions and levels. -/
public section
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: continuous_band_regression_correction_propensity_hybrid_eq
/-- [Replacing the level treatment propensities by those from another nuisance vector leaves the continuous band regression correction unchanged at every observation](goal). -/
lemma continuous_band_regression_correction_propensity_hybrid_eq
    (L : LevelData Z X) (e b : NuisanceCont L) (k j : ℕ) (o : Obs X Z) :
    continuousBandRegressionCorrection M L (continuousBandPropensityHybrid e b) k j o =
      continuousBandRegressionCorrection M L e k j o := by
  rfl

-- @node: continuous_band_smooth_propensity_difference
/-- [The change in a continuous band's smooth correction when level treatment propensities are replaced equals the corresponding change in the full band score component](goal). -/
lemma continuous_band_smooth_propensity_difference
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e b : NuisanceCont L) (k j : ℕ) (o : Obs X Z) :
    continuousBandSmoothCorrection M phi dphi L e k j o -
        continuousBandSmoothCorrection M phi dphi L
          (continuousBandPropensityHybrid e b) k j o =
      contScoreComponents M phi dphi L e k j o -
        contScoreComponents M phi dphi L (continuousBandPropensityHybrid e b) k j o := by
  have he := continuous_band_component_correction_decomposition M phi dphi L e k j o
  have hb := continuous_band_component_correction_decomposition M phi dphi L
    (continuousBandPropensityHybrid e b) k j o
  rw [continuous_band_regression_correction_propensity_hybrid_eq M] at hb
  linear_combination hb - he

-- @node: encoded_continuous_smooth_propensity_restoration_root_n_negligible
/-- Suppose [the true nuisances are admissible](hyp:he0), [all fitted nuisances are admissible](hyp:heh),
and [their encoded coordinates satisfy the finite-coordinate nuisance rate conditions relative to truth](hyp:hr).
For [a positive band index within the selected level](hyp:hj), assume [a positive clipping threshold](hyp:hc)
and [fitted level assignment probabilities bounded below by it almost everywhere](hyp:hclip).
Then [the population mean of the fitted-band-weighted change in the smooth correction from restoring true level treatment propensities, multiplied by the square root of the evaluation-half size, converges in probability to zero along even sample sizes](goal). -/
lemma encoded_continuous_smooth_propensity_restoration_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (k : Fin L.K) (j : ℕ) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        (∫ o : Obs X Z, regularValue (eh (2*(n+1)) a).gamma k j o.1 *
          (continuousBandSmoothCorrection M phi dphi L (eh (2*(n+1)) a) k (j-1) o -
            continuousBandSmoothCorrection M phi dphi L
              (continuousBandPropensityHybrid (eh (2*(n+1)) a) (trueNuisance M L))
              k (j-1) o) ∂observationLaw M)) atTop (fun _ _ => 0) := by
  simp_rw [continuous_band_smooth_propensity_difference M]
  exact encoded_continuous_gamma_band_propensity_restoration_root_n_negligible
    M μ phi dphi L eh he0 heh hr k j hj c hc hclip

-- @node: encoded_continuous_band_product_bias_restored_smooth_difference_root_n_negligible
/-- Under [the structural model assumptions](hyp:hStruct) and [known outcome endpoints](hyp:hend), assume
[a valid policy](hyp:hphi) [with the specified derivative](hyp:hd) and [a bounded, Lipschitz derivative](hyp:hDerivative),
[policy-invariant level order](hyp:hL), [baseline overlap](hyp:hov), and [separated propensity gaps](hyp:hg).
Suppose [the true nuisances](hyp:he0) and [all fitted nuisances](hyp:heh) are admissible,
[boundary densities are bounded](hyp:hdensity), [there is no atom at the lower outcome endpoint](hyp:h0),
and [the encoded nuisance coordinates satisfy the finite-coordinate rate conditions](hyp:hr).
For [a level below the terminal level](hyp:hk) and [a positive band index within that level](hyp:hj),
assume [a positive clipping threshold](hyp:hc), [fitted level assignment probabilities bounded below by it](hyp:hpi),
and [fitted band probabilities bounded below by it](hyp:htau), almost everywhere.
Then [the band product-score mean bias minus the fitted-band-weighted smooth-correction mean with true regression coordinates and level treatment propensities, multiplied by the square root of the evaluation-half size, converges in probability to zero along even sample sizes](goal). -/
lemma encoded_continuous_band_product_bias_restored_smooth_difference_root_n_negligible
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi gap : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hg : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hdensity : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L)
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (c : ℝ) (hc : 0 < c)
    (hpi : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x)
    (htau : ∀ n a r, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).tauLev r x) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        (((∫ o, psiProd M phi dphi L (eh (2*(n+1)) a) k j o ∂observationLaw M) -
          (∫ x, gamma M L k j x * contJ L (trueNuisance M L) k (j-1) x ∂xLaw M)) -
          ∫ o : Obs X Z, regularValue (eh (2*(n+1)) a).gamma k j o.1 *
            continuousBandSmoothCorrection M phi dphi L
              (continuousBandPropensityHybrid
                (continuousBandRegressionHybrid (eh (2*(n+1)) a) (trueNuisance M L))
                (trueNuisance M L)) k (j-1) o ∂observationLaw M))
      atTop (fun _ _ => 0) := by
  let bh := fun n a => continuousBandRegressionHybrid (eh n a) (trueNuisance M L)
  let ph := fun n a => continuousBandPropensityHybrid (bh n a) (trueNuisance M L)
  have hb n a := continuous_band_regression_hybrid_admissible M L _ _ (heh n a) he0
  have hp n a := continuous_band_propensity_hybrid_admissible M L _ _ (hb n a) he0
  have hreduce := encoded_continuous_band_product_bias_smooth_difference_root_n_negligible
    M hStruct hend μ phi dphi hphi hd hDerivative L hL cpi gap hov hg
    eh he0 heh hdensity h0 hr k j hk hj c hc hpi htau
  have hrestore := encoded_continuous_smooth_propensity_restoration_root_n_negligible
    M μ phi dphi L bh he0 hb
    (encoded_continuous_band_regression_hybrid_rates M μ L _ eh hr)
    ⟨k,hk⟩ j hj c hc hpi
  have hs := (show TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ)) from hreduce).add_zero
    (show TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ)) from hrestore)
  change TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ))
  convert hs using 1
  funext n a
  have ib := fitted_continuous_weighted_band_smooth_correction_integrable
    M phi dphi hphi hd hDerivative L (bh (2*(n+1)) a) (hb _ a) he0
    k j hk hj c hc (hpi _ a) (htau _ a)
  have ip := fitted_continuous_weighted_band_smooth_correction_integrable
    M phi dphi hphi hd hDerivative L (ph (2*(n+1)) a) (hp _ a) he0
    k j hk hj c hc (hpi _ a) (htau _ a)
  change Integrable (fun o : Obs X Z => regularValue (eh (2*(n+1)) a).gamma k j o.1 *
    continuousBandSmoothCorrection M phi dphi L (bh (2*(n+1)) a) k (j-1) o)
    (observationLaw M) at ib
  change Integrable (fun o : Obs X Z => regularValue (eh (2*(n+1)) a).gamma k j o.1 *
    continuousBandSmoothCorrection M phi dphi L (ph (2*(n+1)) a) k (j-1) o)
    (observationLaw M) at ip
  have hgamma n a : (bh n a).gamma = (eh n a).gamma := rfl
  simp only [hgamma, mul_sub]
  dsimp only [ph] at ip
  rw [integral_sub ib ip]
  dsimp only [bh]
  ring

-- @node: continuous_restored_smooth_correction_policy_decomposition
/-- Under [the structural model assumptions](hyp:hStruct) and [known outcome endpoints](hyp:hend), suppose
[level order is policy invariant](hyp:hL), [baseline overlap holds](hyp:hov), [policy overlap holds](hyp:hpol),
[boundary densities are bounded](hyp:hdensity), and [there is no atom at the lower outcome endpoint](hyp:h0).
For [a level below the terminal level](hyp:hk) and [a band below that level's final boundary](hyp:hj),
[the smooth correction after restoring true regression coordinates and level treatment propensities equals, almost everywhere, the negative lower-boundary quantile times its policy residual plus the upper-boundary quantile times its policy residual, together with the lower and upper treatment-residual terms, omitting the lower term at level zero](goal). -/
lemma continuous_restored_smooth_correction_policy_decomposition
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hdensity : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L)
    (e : NuisanceCont L) (k j : ℕ) (hk : k < L.K) (hj : j < L.l k) :
    let b := continuousBandPropensityHybrid
      (continuousBandRegressionHybrid e (trueNuisance M L)) (trueNuisance M L)
    ∀ᵐ o ∂observationLaw M,
      continuousBandSmoothCorrection M phi dphi L b k j o =
        -nuValue M e k j o.1 *
          (pooledQ phi L b k j o.1 + RqCont dphi L b k j o -
            pooledQ phi L (trueNuisance M L) k j o.1) +
        nuValue M e k (j+1) o.1 *
          (pooledQ phi L b k (j+1) o.1 + RqCont dphi L b k (j+1) o -
            pooledQ phi L (trueNuisance M L) k (j+1) o.1) +
        (if k = 0 then 0 else alphaLow M L b k j o.1 * RpCont L b k o) +
        alphaHigh M L b k j o.1 * RpCont L b (k+1) o := by
  intro b
  filter_upwards [observationLaw_covariate_ae M _
    (population_continuous_score_quantile_moment_of_density M hStruct hend
      phi L hL cpi hov hpol hdensity h0)] with o ho
  have ha := ho k hk j hj.le
  have hb := ho k hk (j+1) (by omega)
  simp only [continuousBandSmoothCorrection, continuousQuantileBoundaryContrast,
    continuousQuantilePolicyWidth, contJ]
  change _ = _
  have hp : b.pLev = (trueNuisance M L).pLev := rfl
  have hMp : b.Mplus = (trueNuisance M L).Mplus := rfl
  have hMm : b.Mminus = (trueNuisance M L).Mminus := rfl
  have hJp : b.Jplus = (trueNuisance M L).Jplus := rfl
  have hJm : b.Jminus = (trueNuisance M L).Jminus := rfl
  have hn t : nuValue M b k t o.1 = nuValue M e k t o.1 := rfl
  simp only [hp, hMp, hMm, hJp, hJm, hn]
  linear_combination nuValue M e k j o.1 * ha - nuValue M e k (j+1) o.1 * hb

-- @node: continuous_restored_smooth_correction_policy_mean
/-- Under [the structural model assumptions](hyp:hStruct) and [known outcome endpoints](hyp:hend), assume
[a valid policy](hyp:hphi) [with the specified derivative](hyp:hd) and [a bounded, Lipschitz derivative](hyp:hDerivative),
[policy-invariant level order](hyp:hL), [baseline overlap](hyp:hov), [policy overlap](hyp:hpol),
[bounded boundary densities](hyp:hdensity), and [no atom at the lower outcome endpoint](hyp:h0).
Suppose [the fitted nuisances](hyp:he) and [true nuisances](hyp:he0) are admissible.
For [a level below the terminal level](hyp:hk) and [a positive band index within that level](hyp:hj), assume
[a positive clipping threshold](hyp:hc), [level assignment probabilities bounded below by it](hyp:hpi),
and [band probabilities bounded below by it](hyp:htau), almost everywhere.
Then [the fitted-band-weighted mean smooth correction with true regression coordinates and level treatment propensities equals the negative mean lower-boundary policy residual weighted by the fitted band weight and lower quantile, plus the analogous upper-boundary mean](goal). -/
lemma continuous_restored_smooth_correction_policy_mean
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hdensity : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L)
    (e : NuisanceCont L) (he : ContAdmissible M L e)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (c : ℝ) (hc : 0 < c)
    (hpi : ∀ i, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (htau : ∀ r, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x) :
    let b := continuousBandPropensityHybrid
      (continuousBandRegressionHybrid e (trueNuisance M L)) (trueNuisance M L)
    (∫ o : Obs X Z, regularValue e.gamma k j o.1 *
      continuousBandSmoothCorrection M phi dphi L b k (j-1) o ∂observationLaw M) =
      -(∫ o : Obs X Z, (regularValue e.gamma k j o.1 * nuValue M e k (j-1) o.1) *
        (pooledQ phi L b k (j-1) o.1 + RqCont dphi L b k (j-1) o -
          pooledQ phi L (trueNuisance M L) k (j-1) o.1) ∂observationLaw M) +
      (∫ o : Obs X Z, (regularValue e.gamma k j o.1 * nuValue M e k j o.1) *
        (pooledQ phi L b k j o.1 + RqCont dphi L b k j o -
          pooledQ phi L (trueNuisance M L) k j o.1) ∂observationLaw M) := by
  intro b
  let g : RegularIndex L := ⟨(k,j),hk.le,hj⟩
  have hb := continuous_band_propensity_hybrid_admissible M L _ _
    (continuous_band_regression_hybrid_admissible M L _ _ he he0) he0
  have hg x : regularValue e.gamma k j x = b.gamma g x := by
    simp only [regularValue, dif_pos (show k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from ⟨hk.le,hj⟩)]
    rfl
  have hn t x : nuValue M e k t x = nuValue M b k t x := rfl
  have hgm : Measurable (b.gamma g) := by
    first | fun_prop | skip
    rcases hb with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hm, _⟩
    exact hm g
  have hw t : Measurable (fun x => b.gamma g x * nuValue M b k t x) := by fun_prop
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  have hw2 t : MemLp (fun x => b.gamma g x * nuValue M b k t x) 2 (xLaw M) := by
    apply MemLp.of_bound (hw t).aestronglyMeasurable (|M.yMin| + |M.yMax|)
    filter_upwards [hb.2.2.2.2.2.2.2.2.2.2.2.2.1 g,
      continuous_admissible_nuValue_abs_bound M L b hb k t] with x hx hn
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hx.1]
    exact (mul_le_mul hx.2 hn (abs_nonneg _) (by positivity)).trans_eq (one_mul _)
  let P := fun t (o : Obs X Z) => (b.gamma g o.1 * nuValue M b k t o.1) *
    (pooledQ phi L b k t o.1 + RqCont dphi L b k t o -
      pooledQ phi L (trueNuisance M L) k t o.1)
  have iP t : Integrable (P t) (observationLaw M) := by
    have iq := ((hw2 t).comp_measurePreserving (observationLaw_fst_measurePreserving M)).integrable_mul
      ((fitted_continuous_pooledQ_memLp M phi hphi L b hb k t).comp_measurePreserving
        (observationLaw_fst_measurePreserving M))
    have iq0 := ((hw2 t).comp_measurePreserving (observationLaw_fst_measurePreserving M)).integrable_mul
      ((fitted_continuous_pooledQ_memLp M phi hphi L _ he0 k t).comp_measurePreserving
        (observationLaw_fst_measurePreserving M))
    have ir := (fitted_continuous_gamma_quantile_policy_residual_memLp
      M phi dphi hphi hd hDerivative L b hb c hc htau g k t hk.le).integrable (by norm_num)
    convert (iq.fun_add ir).sub' iq0 using 1
    funext o
    dsimp only [P, Function.comp_apply, Pi.mul_apply]
    ring
  let R := fun (s : Bool) (o : Obs X Z) => b.gamma g o.1 *
    ((if s then alphaHigh M L b k (j-1) o.1 else alphaLow M L b k (j-1) o.1) *
      RpCont L b (if s then k+1 else k) o)
  have iR s : Integrable (R s) (observationLaw M) :=
    (fitted_continuous_gamma_alpha_treatment_memLp M L b hb c hc hpi
      g s k (j-1) hk).integrable (by norm_num)
  have zR s : (∫ o, R s o ∂observationLaw M) = 0 := by
    have hm : Measurable (fun x => b.gamma g x *
      (if s then alphaHigh M L b k (j-1) x else alphaLow M L b k (j-1) x)) := by
      first | fun_prop | (cases s <;> simp only [Bool.true_eq, Bool.false_eq_true, if_true, if_false] <;> fun_prop)
    have hi : Integrable (fun o : Obs X Z =>
      (b.gamma g o.1 * (if s then alphaHigh M L b k (j-1) o.1 else alphaLow M L b k (j-1) o.1)) *
        RpCont L {trueNuisance M L with piLev := b.piLev, gammaFull := b.gammaFull}
          (if s then k+1 else k) o) (observationLaw M) := by
      convert iR s using 1
      funext o
      have hr i : RpCont L {trueNuisance M L with piLev := b.piLev, gammaFull := b.gammaFull} i o =
          RpCont L b i o := rfl
      rw [hr]
      dsimp only [R]
      ring
    have hz := continuous_full_hybrid_treatment_weighted_zero M hStruct.2.2.2.1
      (policyProp phi M.prop) L hL b hb (if s then k+1 else k)
      (by cases s <;> simp <;> omega) _ hm hi
    convert hz using 1
    congr 1
    funext o
    change b.gamma g o.1 * (_ * RpCont L b _ o) = (b.gamma g o.1 * _) * RpCont L b _ o
    ring
  have heq : ∀ᵐ o ∂observationLaw M,
      regularValue e.gamma k j o.1 * continuousBandSmoothCorrection M phi dphi L b k (j-1) o =
        -P (j-1) o + P j o + R false o + R true o := by
    filter_upwards [continuous_restored_smooth_correction_policy_decomposition M hStruct hend
      phi dphi L hL cpi hov hpol hdensity h0 e k (j-1) hk (by omega)] with o ho
    rw [ho]
    simp only [hg, hn, Nat.sub_add_cancel hj.1]
    dsimp only [P, R]
    simp only [Bool.true_eq, Bool.false_eq_true, if_true, if_false]
    by_cases hk0 : k = 0
    · simp only [hk0, if_true, RpCont, if_true]
      ring
    · simp only [if_neg hk0]
      ring
  rw [integral_congr_ae heq]
  have h1 := integral_add (((iP (j-1)).neg.fun_add (iP j)).fun_add (iR false)) (iR true)
  have h2 := integral_add ((iP (j-1)).neg.fun_add (iP j)) (iR false)
  have h3 := integral_add (iP (j-1)).neg (iP j)
  simp only [Pi.neg_apply] at h1 h2 h3
  rw [h1, h2, h3, integral_neg, zR false, zR true]
  simp only [add_zero, P, ← hg, ← hn]

-- @node: encoded_continuous_restored_smooth_correction_root_n_negligible
/-- Under [the structural model assumptions](hyp:hStruct) and [known outcome endpoints](hyp:hend), assume
[a valid policy](hyp:hphi) [with the specified derivative](hyp:hd) and [a bounded, Lipschitz derivative](hyp:hDerivative),
[policy-invariant level order](hyp:hL), [baseline overlap](hyp:hov), and [policy overlap](hyp:hpol).
Suppose [the true nuisances](hyp:he0) and [all fitted nuisances](hyp:heh) are admissible,
[boundary densities are bounded](hyp:hdensity), [there is no atom at the lower outcome endpoint](hyp:h0),
and [the encoded nuisance coordinates satisfy the finite-coordinate rate conditions](hyp:hr).
For [a level below the terminal level](hyp:hk) and [a positive band index within that level](hyp:hj), assume
[a positive clipping threshold](hyp:hc), [fitted level assignment probabilities bounded below by it](hyp:hpi),
and [fitted band probabilities bounded below by it](hyp:htau), almost everywhere.
Then [the fitted-band-weighted mean smooth correction with true regression coordinates and level treatment propensities, multiplied by the square root of the evaluation-half size, converges in probability to zero along even sample sizes](goal). -/
lemma encoded_continuous_restored_smooth_correction_root_n_negligible
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hdensity : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L)
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (c : ℝ) (hc : 0 < c)
    (hpi : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x)
    (htau : ∀ n a r, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).tauLev r x) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        ∫ o : Obs X Z, regularValue (eh (2*(n+1)) a).gamma k j o.1 *
          continuousBandSmoothCorrection M phi dphi L
            (continuousBandPropensityHybrid
              (continuousBandRegressionHybrid (eh (2*(n+1)) a) (trueNuisance M L))
              (trueNuisance M L)) k (j-1) o ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  let bh := fun n a => continuousBandPropensityHybrid
    (continuousBandRegressionHybrid (eh n a) (trueNuisance M L)) (trueNuisance M L)
  let g : RegularIndex L := ⟨(k,j),hk.le,hj⟩
  have hb n a := continuous_band_propensity_hybrid_admissible M L _ _
    (continuous_band_regression_hybrid_admissible M L _ _ (heh n a) he0) he0
  have hrb : FiniteNuisanceRates M μ (fun n a => contComponent M L (bh n a))
      (contComponent M L (trueNuisance M L)) :=
    encoded_continuous_band_propensity_hybrid_rates M μ L _ _
      (encoded_continuous_band_regression_hybrid_rates M μ L _ eh hr)
  let P := fun t n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
    ∫ o : Obs X Z, (regularValue (eh (2*(n+1)) a).gamma k j o.1 *
      nuValue M (eh (2*(n+1)) a) k t o.1) *
      (pooledQ phi L (bh (2*(n+1)) a) k t o.1 +
        RqCont dphi L (bh (2*(n+1)) a) k t o -
        pooledQ phi L (trueNuisance M L) k t o.1) ∂observationLaw M
  have hP t (ht : t ≤ L.l k) : TendstoInMeasure μ (P t) atTop (fun _ => (0 : ℝ)) := by
    by_cases ht0 : t = 0
    · subst t
      have hz : P 0 = fun _ _ => (0 : ℝ) := by
        funext n a
        simp only [P, pooledQ, RqCont, if_true, true_or, add_zero, bh,
          continuousBandPropensityHybrid, sub_self, mul_zero, integral_zero]
      rw [hz]
      intro eps heps
      simpa only [edist_self, not_le.mpr heps, Set.ofPred_false, measure_empty]
        using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
    · let r : RegularIndex L := ⟨(k,t),hk.le,by omega,ht⟩
      have hh := encoded_continuous_observed_quantile_policy_bias_root_n_negligible
        M hStruct.2.2.2.1 μ phi dphi hphi hd hDerivative L hL cpi hpol bh
        he0 hb hrb g r k t c hc (fun n a => htau n a r)
      convert (show TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ)) from hh) using 1
      funext n a
      dsimp only [P, r]
      congr 1
      congr 1
      funext o
      simp only [regularValue, dif_pos (show k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from ⟨hk.le,hj⟩), P]
      rfl
  have hs := (hP j hj.2).sub_zero (hP (j-1) (by omega))
  change TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ))
  convert hs using 1
  funext n a
  rw [continuous_restored_smooth_correction_policy_mean M hStruct hend phi dphi hphi hd
    hDerivative L hL cpi hov hpol hdensity h0 (eh (2*(n+1)) a) (heh _ a)
    he0 k j hk hj c hc (hpi _ a) (htau _ a)]
  dsimp only [P, bh]
  ring

-- @node: encoded_continuous_band_product_bias_root_n_negligible
/-- Under [the structural model assumptions](hyp:hStruct) and [known outcome endpoints](hyp:hend), assume
[a valid policy](hyp:hphi) [with the specified derivative](hyp:hd) and [a bounded, Lipschitz derivative](hyp:hDerivative),
[policy-invariant level order](hyp:hL), [baseline overlap](hyp:hov), [policy overlap](hyp:hpol),
and [separated propensity gaps](hyp:hg).
Suppose [the true nuisances](hyp:he0) and [all fitted nuisances](hyp:heh) are admissible,
[boundary densities are bounded](hyp:hdensity), [there is no atom at the lower outcome endpoint](hyp:h0),
and [the encoded nuisance coordinates satisfy the finite-coordinate rate conditions](hyp:hr).
For [a level below the terminal level](hyp:hk) and [a positive band index within that level](hyp:hj), assume
[a positive clipping threshold](hyp:hc), [fitted level assignment probabilities bounded below by it](hyp:hpi),
and [fitted band probabilities bounded below by it](hyp:htau), almost everywhere.
Then [the difference between the fitted band product-score mean and the covariate mean of the true band weight times the true band regression contrast, multiplied by the square root of the evaluation-half size, converges in probability to zero along even sample sizes](goal). -/
lemma encoded_continuous_band_product_bias_root_n_negligible
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi gap : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hpol : PolicyOverlap M L cpi)
    (hg : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hdensity : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L)
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (c : ℝ) (hc : 0 < c)
    (hpi : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x)
    (htau : ∀ n a r, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).tauLev r x) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        ((∫ o, psiProd M phi dphi L (eh (2*(n+1)) a) k j o ∂observationLaw M) -
          (∫ x, gamma M L k j x * contJ L (trueNuisance M L) k (j-1) x ∂xLaw M)))
      atTop (fun _ _ => 0) := by
  have hreduce := encoded_continuous_band_product_bias_restored_smooth_difference_root_n_negligible
    M hStruct hend μ phi dphi hphi hd hDerivative L hL cpi gap hov hg eh he0 heh
    hdensity h0 hr k j hk hj c hc hpi htau
  have hs := encoded_continuous_restored_smooth_correction_root_n_negligible
    M hStruct hend μ phi dphi hphi hd hDerivative L hL cpi hov hpol eh he0 heh
    hdensity h0 hr k j hk hj c hc hpi htau
  have hadd := (show TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ)) from hreduce).add_zero
    (show TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ)) from hs)
  change TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ))
  convert hadd using 1
  funext n a
  ring

-- @node: encoded_continuous_band_product_block_bias_root_n_negligible
/-- Under [the structural model assumptions](hyp:hStruct) and [known outcome endpoints](hyp:hend), assume
[a valid policy](hyp:hphi) [with the specified derivative](hyp:hd) and [a bounded, Lipschitz derivative](hyp:hDerivative),
[policy-invariant level order](hyp:hL), [baseline overlap](hyp:hov), [policy overlap](hyp:hpol),
and [separated propensity gaps](hyp:hg).
Suppose [the true nuisances](hyp:he0) and [all fitted nuisances](hyp:heh) are admissible,
[boundary densities are bounded](hyp:hdensity), [there is no atom at the lower outcome endpoint](hyp:h0),
and [the encoded nuisance coordinates satisfy the finite-coordinate rate conditions](hyp:hr).
For [a finite block of positive band indices at levels below the terminal level](hyp:hidx), assume
[a positive clipping threshold](hyp:hc), [fitted level assignment probabilities bounded below by it](hyp:hpi),
and [fitted band probabilities bounded below by it](hyp:htau), almost everywhere.
Then [the difference between the mean summed fitted band product scores and the mean summed true band-weighted regression contrasts, multiplied by the square root of the evaluation-half size, converges in probability to zero along even sample sizes](goal). -/
lemma encoded_continuous_band_product_block_bias_root_n_negligible
    (hStruct : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi gap : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hpol : PolicyOverlap M L cpi)
    (hg : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hdensity : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L)
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (t : Finset (ℕ × ℕ))
    (hidx : ∀ i ∈ t, i.1 < L.K ∧ 1 ≤ i.2 ∧ i.2 ≤ L.l i.1)
    (c : ℝ) (hc : 0 < c)
    (hpi : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x)
    (htau : ∀ n a r, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).tauLev r x) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        ((∫ o : Obs X Z, ∑ i ∈ t, psiProd M phi dphi L (eh (2*(n+1)) a) i.1 i.2 o
            ∂observationLaw M) -
          (∫ x, ∑ i ∈ t, gamma M L i.1 i.2 x *
            contJ L (trueNuisance M L) i.1 (i.2-1) x ∂xLaw M)))
      atTop (fun _ _ => 0) := by
  let F := fun (i : ℕ × ℕ) n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
    ((∫ o, psiProd M phi dphi L (eh (2*(n+1)) a) i.1 i.2 o ∂observationLaw M) -
      (∫ x, gamma M L i.1 i.2 x * contJ L (trueNuisance M L) i.1 (i.2-1) x ∂xLaw M))
  have hF i (hi : i ∈ t) : TendstoInMeasure μ (F i) atTop (fun _ => (0 : ℝ)) :=
    encoded_continuous_band_product_bias_root_n_negligible M hStruct hend μ
      phi dphi hphi hd hDerivative L hL cpi gap hov hpol hg eh he0 heh
      hdensity h0 hr i.1 i.2 (hidx i hi).1 (hidx i hi).2 c hc hpi htau
  have hs : TendstoInMeasure μ (fun n a => ∑ i ∈ t, F i n a)
      atTop (fun _ => (0 : ℝ)) := by
    induction t using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      intro eps heps
      simpa only [edist_self, not_le.mpr heps, Set.ofPred_false, measure_empty]
        using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
    | @insert i t hi ih =>
      have hsingle := hF i (Finset.mem_insert_self i t)
      have hrest := ih (fun b hb => hidx b (Finset.mem_insert_of_mem hb))
        (fun b hb => hF b (Finset.mem_insert_of_mem hb))
      simpa only [Finset.sum_insert hi] using hsingle.add_zero hrest
  change TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ))
  convert hs using 1
  funext n a
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  have icomp i (hi : i ∈ t) := (fitted_continuous_weighted_band_component_memLp
    M phi dphi hphi hd hDerivative L (eh (2*(n+1)) a) (heh _ a)
    c hc (hpi _ a) (htau _ a) i.1 i.2 (hidx i hi).1 (hidx i hi).2).integrable
    (by norm_num : (1 : ENNReal) ≤ 2)
  have iprod i (hi : i ∈ t) := (fitted_continuous_band_product_mean_decomposition
    M phi dphi L (eh (2*(n+1)) a) (heh _ a) i.1 i.2
    (hidx i hi).1.le (hidx i hi).2 (icomp i hi)).1
  have itarget i (hi : i ∈ t) : Integrable (fun x => gamma M L i.1 i.2 x *
      contJ L (trueNuisance M L) i.1 (i.2-1) x) (xLaw M) := by
    have ht : regularValue (trueNuisance M L).gamma i.1 i.2 = gamma M L i.1 i.2 := by
      funext x
      simp only [regularValue, trueNuisance, dif_pos (show
        i.1 ≤ L.K ∧ 1 ≤ i.2 ∧ i.2 ≤ L.l i.1 from ⟨(hidx i hi).1.le, (hidx i hi).2⟩)]
    rw [← ht]
    exact (fitted_continuous_regular_gamma_memLp M L _ he0 i.1 i.2).integrable_mul
      (fitted_contJ_memLp M L _ he0 i.1 (i.2-1))
  rw [integral_finsetSum t iprod, integral_finsetSum t itarget]
  simp only [F, ← Finset.sum_sub_distrib, Finset.mul_sum]

end Papers.TbsPrteOptimalTransport
