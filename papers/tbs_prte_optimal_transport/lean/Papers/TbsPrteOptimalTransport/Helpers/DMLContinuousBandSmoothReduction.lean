module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLCrossedBandBias
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousRestoredBandBias
/-! Reduction of the fitted band product bias to its smooth correction.
The product cross-error and the restored regression correction are negligible
at root-n scale. The remaining expression retains the quantile moments and
the propensity and pooled-policy residuals needed for the final cancellation. -/
@[expose] public section
set_option linter.style.haveILetI false
set_option linter.unusedFintypeInType false
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

-- @node: continuousBandSmoothCorrection
/-- For [a latent instrumental-variable model](hyp:M), [a policy map](hyp:phi)
and [its proposed derivative](hyp:dphi), [treatment levels and policy bands](hyp:L),
[a continuous nuisance fit](hyp:e), [a level](hyp:k), [a band index](hyp:j), and
[an observation](hyp:o), [the smooth band correction](goal) is the fitted-minus-true
band moment plus the difference of boundary contrasts net of policy widths at
successive quantile boundaries, plus the lower and upper treatment-residual
corrections, minus the lower quantile times its policy residual and plus the
upper quantile times its policy residual; the baseline lower treatment term is zero. -/
noncomputable def continuousBandSmoothCorrection
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e : NuisanceCont L) (k j : ℕ) (o : Obs X Z) : ℝ :=
  contJ L e k j o.1 - contJ L (trueNuisance M L) k j o.1 +
    (continuousQuantileBoundaryContrast M L e k j o.1 -
      continuousQuantilePolicyWidth M phi L e k j o.1) -
    (continuousQuantileBoundaryContrast M L e k (j+1) o.1 -
      continuousQuantilePolicyWidth M phi L e k (j+1) o.1) +
    (if k = 0 then 0 else alphaLow M L e k j o.1 * RpCont L e k o) +
    alphaHigh M L e k j o.1 * RpCont L e (k+1) o -
    nuValue M e k j o.1 * RqCont dphi L e k j o +
    nuValue M e k (j+1) o.1 * RqCont dphi L e k (j+1) o

-- @node: continuous_band_component_correction_decomposition
/-- [The continuous band score component minus the population band moment equals
the sum of the regression correction and the smooth correction, at every
observation](goal). -/
lemma continuous_band_component_correction_decomposition
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e : NuisanceCont L) (k j : ℕ) (o : Obs X Z) :
    contScoreComponents M phi dphi L e k j o -
        contJ L (trueNuisance M L) k j o.1 =
      continuousBandRegressionCorrection M L e k j o +
        continuousBandSmoothCorrection M phi dphi L e k j o := by
  rw [continuous_band_score_regression_decomposition]
  simp only [continuousBandSmoothCorrection, continuousQuantileBoundaryContrast,
    continuousQuantilePolicyWidth]
  ring

-- @node: fitted_continuous_weighted_band_smooth_correction_integrable
/-- Suppose [the policy map is valid](hyp:hphi), [its proposed derivative is its
derivative](hyp:hd), [that derivative is bounded and Lipschitz](hyp:hDerivative),
[the fitted and population nuisances are admissible](hyp:he,he0), [the level is
nonterminal](hyp:hk), and [the band index lies between one and the number of bands
at that level](hyp:hj). If [the denominator bound is positive](hyp:hc), and [fitted
level instrument probabilities](hyp:hpi) and [fitted policy probabilities](hyp:htau)
are bounded below by it almost everywhere, [the fitted share times the smooth
correction for the preceding band index is integrable under the observation law](goal). -/
lemma fitted_continuous_weighted_band_smooth_correction_integrable
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (c : ℝ) (hc : 0 < c)
    (hpi : ∀ i, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (htau : ∀ r, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x) :
    Integrable (fun o : Obs X Z => regularValue e.gamma k j o.1 *
      continuousBandSmoothCorrection M phi dphi L e k (j-1) o) (observationLaw M) := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  let g : RegularIndex L := ⟨(k,j), hk.le, hj⟩
  have iscore := (fitted_continuous_weighted_band_component_memLp M phi dphi hphi hd
    hDerivative L e he c hc hpi htau k j hk hj).integrable (by norm_num)
  have itarget := ((fitted_continuous_regular_gamma_memLp M L e he k j).comp_measurePreserving
    (observationLaw_fst_measurePreserving M)).integrable_mul
    ((fitted_contJ_memLp M L _ he0 k (j-1)).comp_measurePreserving
      (observationLaw_fst_measurePreserving M))
  have ireg := fitted_continuous_weighted_band_regression_correction_integrable
    M L e he c hc hpi g k (j-1) hk
  have hg (x : X) : regularValue e.gamma k j x = e.gamma g x := by
    simp only [regularValue, dif_pos (show k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from ⟨hk.le,hj⟩), g]
  convert (iscore.sub' itarget).sub' ireg using 1
  funext o
  change regularValue e.gamma k j o.1 *
      continuousBandSmoothCorrection M phi dphi L e k (j-1) o =
    regularValue e.gamma k j o.1 * contScoreComponents M phi dphi L e k (j-1) o -
      regularValue e.gamma k j o.1 * contJ L (trueNuisance M L) k (j-1) o.1 -
      e.gamma g o.1 * continuousBandRegressionCorrection M L e k (j-1) o
  rw [← hg, ← mul_sub, continuous_band_component_correction_decomposition M]
  ring

-- @node: encoded_continuous_band_product_bias_smooth_difference_root_n_negligible
/-- Assume [the structural model assumptions](hyp:hStruct), [known outcome
endpoints](hyp:hend), [a valid policy map](hyp:hphi), [the proposed policy
derivative is correct](hyp:hd), [a bounded Lipschitz policy derivative](hyp:hDerivative),
[invariant level ordering under the policy](hyp:hL), [baseline overlap](hyp:hov),
and [separated baseline and policy propensity gaps](hyp:hg). With [admissible
population nuisances](hyp:he0), [admissible fitted nuisances](hyp:heh), [bounded
boundary densities](hyp:hdensity), [no atom at the lower outcome endpoint](hyp:h0),
[componentwise nuisance L² errors that vanish faster in probability than the
inverse fourth root of sample size](hyp:hr), [a nonterminal level](hyp:hk), [a valid positive
band index](hyp:hj), [a positive denominator bound](hyp:hc), and [fitted instrument
probabilities](hyp:hpi) and [policy probabilities](hyp:htau) bounded below by it
almost everywhere, [the population bias of the fitted band product minus the
expected fitted-share-weighted smooth correction evaluated at the fit with
population regressions restored is negligible in probability after multiplication
by the square root of the evaluation half's size, along sample sizes twice one
plus the index](goal). -/
lemma encoded_continuous_band_product_bias_smooth_difference_root_n_negligible
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
              (continuousBandRegressionHybrid (eh (2*(n+1)) a) (trueNuisance M L))
              k (j-1) o ∂observationLaw M)) atTop (fun _ _ => 0) := by
  let g : RegularIndex L := ⟨(k,j), hk.le, hj⟩
  let bh := fun n a => continuousBandRegressionHybrid (eh n a) (trueNuisance M L)
  have hb n a := continuous_band_regression_hybrid_admissible M L _ _ (heh n a) he0
  have hdifference := encoded_continuous_band_bias_restored_component_difference_root_n_negligible
    M μ phi dphi hphi hd hDerivative L eh he0 heh hr {(k,j)}
    (by intro i hi; obtain rfl := Finset.mem_singleton.mp hi; exact ⟨hk,hj⟩)
    c hc hpi htau
  simp only [Finset.sum_singleton] at hdifference
  have hreg := encoded_continuous_restored_band_regression_correction_root_n_negligible
    M hStruct hend μ (policyProp phi M.prop) L hL cpi gap hov hg eh he0 heh
    hdensity h0 hr k (j-1) hk (by omega) g c hc hpi
  have hs := (show TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ)) from hdifference).add_zero
    (show TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ)) from hreg)
  change TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ))
  convert hs using 1
  funext n a
  have hg' (o : Obs X Z) : regularValue (eh (2*(n+1)) a).gamma k j o.1 =
      (eh (2*(n+1)) a).gamma g o.1 := by
    simp only [regularValue, dif_pos (show k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from ⟨hk.le,hj⟩), g]
  have ireg := fitted_continuous_weighted_band_regression_correction_integrable
    M L (bh (2*(n+1)) a) (hb _ a) c hc (hpi _ a) g k (j-1) hk
  have ismooth := fitted_continuous_weighted_band_smooth_correction_integrable
    M phi dphi hphi hd hDerivative L (bh (2*(n+1)) a) (hb _ a) he0 k j hk hj
    c hc (hpi _ a) (htau _ a)
  change Integrable (fun o : Obs X Z => (eh (2*(n+1)) a).gamma g o.1 *
    continuousBandRegressionCorrection M L (bh (2*(n+1)) a) k (j-1) o)
    (observationLaw M) at ireg
  change Integrable (fun o : Obs X Z => regularValue (eh (2*(n+1)) a).gamma k j o.1 *
    continuousBandSmoothCorrection M phi dphi L (bh (2*(n+1)) a) k (j-1) o)
    (observationLaw M) at ismooth
  have heq :
      (∫ o : Obs X Z, regularValue (eh (2*(n+1)) a).gamma k j o.1 *
        (contScoreComponents M phi dphi L (bh (2*(n+1)) a) k (j-1) o -
          contJ L (trueNuisance M L) k (j-1) o.1) ∂observationLaw M) =
      (∫ o : Obs X Z, (eh (2*(n+1)) a).gamma g o.1 *
        continuousBandRegressionCorrection M L (bh (2*(n+1)) a) k (j-1) o
        ∂observationLaw M) +
      (∫ o : Obs X Z, regularValue (eh (2*(n+1)) a).gamma k j o.1 *
        continuousBandSmoothCorrection M phi dphi L (bh (2*(n+1)) a) k (j-1) o
        ∂observationLaw M) := by
    rw [← integral_add ireg ismooth]
    apply integral_congr_ae
    filter_upwards [] with o
    rw [continuous_band_component_correction_decomposition M, hg']
    ring
  dsimp only [bh] at heq
  rw [heq]
  ring

-- @node: encoded_continuous_band_product_block_bias_smooth_difference_root_n_negligible
/-- Under [the structural model assumptions](hyp:hStruct), [known outcome
endpoints](hyp:hend), [a valid policy map](hyp:hphi), [correct policy
differentiation](hyp:hd), [a bounded Lipschitz derivative](hyp:hDerivative),
[policy-invariant level ordering](hyp:hL), [baseline overlap](hyp:hov), [propensity
gap separation](hyp:hg), [admissible population nuisances](hyp:he0), [admissible
fits](hyp:heh), [bounded boundary densities](hyp:hdensity), [no atom at the lower
outcome endpoint](hyp:h0), and [componentwise nuisance L² errors that vanish faster
in probability than the inverse fourth root of sample size](hyp:hr), consider [a finite
block whose levels are nonterminal and whose band indices are valid and
positive](hyp:hidx). If [the denominator bound is positive](hyp:hc) and [all fitted
instrument probabilities](hyp:hpi) and [policy probabilities](hyp:htau) exceed it
almost everywhere, [the block's population product bias minus its expected
fitted-share-weighted smooth correction with population regressions restored
converges to zero in probability after multiplication by the square root of the
evaluation half's size, along sample sizes twice one plus the index](goal). -/
lemma encoded_continuous_band_product_block_bias_smooth_difference_root_n_negligible
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
    (t : Finset (ℕ × ℕ))
    (hidx : ∀ i ∈ t, i.1 < L.K ∧ 1 ≤ i.2 ∧ i.2 ≤ L.l i.1)
    (c : ℝ) (hc : 0 < c)
    (hpi : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x)
    (htau : ∀ n a r, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).tauLev r x) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        (((∫ o : Obs X Z, ∑ i ∈ t,
            psiProd M phi dphi L (eh (2*(n+1)) a) i.1 i.2 o ∂observationLaw M) -
          (∫ x, ∑ i ∈ t, gamma M L i.1 i.2 x *
            contJ L (trueNuisance M L) i.1 (i.2-1) x ∂xLaw M)) -
          ∫ o : Obs X Z, ∑ i ∈ t, regularValue (eh (2*(n+1)) a).gamma i.1 i.2 o.1 *
            continuousBandSmoothCorrection M phi dphi L
              (continuousBandRegressionHybrid (eh (2*(n+1)) a) (trueNuisance M L))
              i.1 (i.2-1) o ∂observationLaw M)) atTop (fun _ _ => 0) := by
  let bh := fun n a => continuousBandRegressionHybrid (eh n a) (trueNuisance M L)
  let F := fun (i : ℕ × ℕ) n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
    (((∫ o, psiProd M phi dphi L (eh (2*(n+1)) a) i.1 i.2 o ∂observationLaw M) -
      (∫ x, gamma M L i.1 i.2 x * contJ L (trueNuisance M L) i.1 (i.2-1) x ∂xLaw M)) -
      ∫ o : Obs X Z, regularValue (eh (2*(n+1)) a).gamma i.1 i.2 o.1 *
        continuousBandSmoothCorrection M phi dphi L (bh (2*(n+1)) a) i.1 (i.2-1) o
        ∂observationLaw M)
  have hF i (hi : i ∈ t) : TendstoInMeasure μ (F i) atTop (fun _ => (0 : ℝ)) :=
    encoded_continuous_band_product_bias_smooth_difference_root_n_negligible
      M hStruct hend μ phi dphi hphi hd hDerivative L hL cpi gap hov hg
      eh he0 heh hdensity h0 hr i.1 i.2 (hidx i hi).1 (hidx i hi).2 c hc hpi htau
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
  have ismooth i (hi : i ∈ t) : Integrable (fun o : Obs X Z =>
      regularValue (eh (2*(n+1)) a).gamma i.1 i.2 o.1 *
        continuousBandSmoothCorrection M phi dphi L (bh (2*(n+1)) a) i.1 (i.2-1) o)
      (observationLaw M) := fitted_continuous_weighted_band_smooth_correction_integrable
        M phi dphi hphi hd hDerivative L (bh (2*(n+1)) a)
        (continuous_band_regression_hybrid_admissible M L _ _ (heh _ a) he0) he0
        i.1 i.2 (hidx i hi).1 (hidx i hi).2 c hc (hpi _ a) (htau _ a)
  rw [integral_finsetSum t iprod, integral_finsetSum t itarget,
    integral_finsetSum t ismooth]
  simp only [F, bh, ← Finset.sum_sub_distrib, Finset.mul_sum]

end Papers.TbsPrteOptimalTransport
