module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousBandBiasTransfer
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousBandRegressionHybrid
public import Papers.TbsPrteOptimalTransport.Helpers.DMLQuantilePolicyBlock
public import StatLean.AsymptoticStatistics.ForMathlib.TendstoInMeasureAlgebra
/-! Reduction of the continuous band bias to population band regressions.
The regression/denominator cancellation and the gamma/target cross-error
are negligible at root-n scale. The remaining correction is evaluated at
the concrete regression-restoring hybrid. -/
public section
set_option linter.style.emptyLine false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
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

-- @node: fitted_continuous_weighted_band_component_memLp
/-- Suppose [the policy is valid](hyp:hphi), [the specified derivative differentiates it](hyp:hd), [the derivative is bounded and Lipschitz](hyp:hDerivative), and [the nuisance record is admissible](hyp:he). If [the common denominator bound is positive](hyp:hc), [positive-level probabilities exceed that bound almost everywhere](hyp:hpi), [regular-band probabilities also exceed it almost everywhere](hyp:htau), [the level is below the level count](hyp:hk), and [the band index lies between one and the number of bands at that level](hyp:hj), then [the gamma-weighted continuous band score component is square integrable under the observation law](goal). -/
lemma fitted_continuous_weighted_band_component_memLp
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e)
    (c : ℝ) (hc : 0 < c)
    (hpi : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (htau : ∀ r : RegularIndex L, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x)
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    MemLp (fun o : Obs X Z => regularValue e.gamma k j o.1 *
      contScoreComponents M phi dphi L e k (j-1) o) 2 (observationLaw M) := by
  let g : RegularIndex L := ⟨(k,j), hk.le, hj⟩
  have hQ b : MemLp (fun o : Obs X Z => e.gamma g o.1 * nuValue M e k b o.1 *
      (positiveValue e.pLev (k+1) o.1 * boundaryValue e.Mplus k b o.1 -
        positiveValue e.pLev k o.1 * minusBoundaryValue e.Mminus k b o.1 -
        (pooledQ phi L e k b o.1 - positiveValue e.pLev k o.1) +
        IFM M L e true k b o - IFM M L e false k b o)) 2 (observationLaw M) := by
    have hB := (fitted_continuous_gamma_quantile_boundary_contrast_memLp
      M L e he g k b).comp_measurePreserving (observationLaw_fst_measurePreserving M)
    have hW := (fitted_continuous_gamma_quantile_policy_width_memLp
      M phi hphi L e he g k b).comp_measurePreserving (observationLaw_fst_measurePreserving M)
    have hI := fitted_continuous_quantile_gamma_IFM_contrast_memLp M L e he c hc hpi g k b hk
    convert (hB.sub hW).add hI using 1
    funext o
    simp only [Pi.add_apply, Pi.sub_apply, Function.comp_apply,
      continuousQuantileBoundaryContrast, continuousQuantilePolicyWidth]
    ring
  have hJ := fitted_continuous_gamma_contJ_memLp M L e he g k (j-1)
  have hIp := fitted_continuous_gamma_IFJ_memLp M L e he c hc hpi g true k (j-1) hk
  have hIm := fitted_continuous_gamma_IFJ_memLp M L e he c hc hpi g false k (j-1) hk
  have hAp := fitted_continuous_gamma_alpha_treatment_memLp M L e he c hc hpi g true k (j-1) hk
  have hAm : MemLp (fun o : Obs X Z => e.gamma g o.1 *
      (if k = 0 then 0 else alphaLow M L e k (j-1) o.1 * RpCont L e k o))
      2 (observationLaw M) := by
    by_cases hk0 : k = 0
    · simp only [hk0, if_true, mul_zero]
      exact MemLp.zero'
    · simpa only [if_neg hk0, Bool.false_eq_true, if_false] using
        fitted_continuous_gamma_alpha_treatment_memLp M L e he c hc hpi g false k (j-1) hk
  have hRp := fitted_continuous_gamma_quantile_policy_residual_memLp
    M phi dphi hphi hd hDerivative L e he c hc htau g k (j-1) hk.le
  have hRq := fitted_continuous_gamma_quantile_policy_residual_memLp
    M phi dphi hphi hd hDerivative L e he c hc htau g k j hk.le
  have hs := ((((((((hJ.add hIp).sub hIm).add (hQ (j-1))).sub (hQ j)).add hAm).add hAp).sub hRp).add hRq)
  convert hs using 1
  funext o
  simp only [Pi.add_apply, Pi.sub_apply, Bool.true_eq, if_true, contScoreComponents,
    regularValue, dif_pos (show k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from ⟨hk.le,hj⟩)]
  have hj' : j-1+1 = j := by omega
  simp only [hj']
  change _ = _
  dsimp only [g]
  ring

-- @node: continuous_restored_band_weighted_component_integrable
/-- If [the fitted nuisance record is admissible](hyp:he), [the replacement regression record is admissible](hyp:hb), [the clipping bound is positive](hyp:hc), [fitted positive-level probabilities exceed it almost everywhere](hyp:hclip), and [the original gamma-weighted band component is integrable](hyp:hi), then [the gamma-weighted band component remains integrable after replacing its band regressions by those of the replacement record](goal). -/
lemma continuous_restored_band_weighted_component_integrable
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e b : NuisanceCont L)
    (he : ContAdmissible M L e) (hb : ContAdmissible M L b)
    (k : Fin L.K) (j : ℕ) (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (hi : Integrable (fun o : Obs X Z => regularValue e.gamma k j o.1 *
      contScoreComponents M phi dphi L e k (j-1) o) (observationLaw M)) :
    Integrable (fun o : Obs X Z => regularValue e.gamma k j o.1 *
      contScoreComponents M phi dphi L (continuousBandRegressionHybrid e b)
        k (j-1) o) (observationLaw M) := by
  have hh := continuous_band_regression_hybrid_admissible M L e b he hb
  have hg := fitted_continuous_regular_gamma_measurable M L e he k j
  have hgb : ∀ᵐ x ∂xLaw M, |regularValue e.gamma k j x| ≤ 1 := by
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hb, _⟩
    unfold regularValue
    split_ifs with h
    · filter_upwards [hb ⟨(k,j),h⟩] with x hx
      simpa only [abs_of_nonneg hx.1] using hx.2
    · exact Eventually.of_forall (fun _ => by norm_num)
  have hd := continuous_band_weighted_joint_regression_integrable M phi dphi L
    e (continuousBandRegressionHybrid e b) he hh rfl rfl rfl rfl rfl rfl
    k (j-1) _ hg hgb c hc hclip
  convert hi.sub' hd using 1
  funext o
  ring

-- @node: encoded_continuous_restored_band_component_difference_root_n_negligible
/-- Suppose [the true nuisance record is admissible](hyp:he0), [every fitted nuisance record is admissible](hyp:heh), and [the encoded fitted coordinates satisfy the finite nuisance convergence rates toward truth](hyp:hr). If [every level in the finite band collection is below the level count](hyp:hk), [the clipping bound is positive](hyp:hc), and [all fitted positive-level probabilities exceed it almost everywhere](hyp:hclip), then [the sum of population gamma-weighted differences between fitted band components and their true-regression-restored versions, evaluated at sample size twice the half-sample size and multiplied by its square root, converges in probability to zero](goal). -/
lemma encoded_continuous_restored_band_component_difference_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (t : Finset (ℕ × ℕ)) (hk : ∀ i ∈ t, i.1 < L.K)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        ∑ i ∈ t, ∫ o : Obs X Z, regularValue (eh (2*(n+1)) a).gamma i.1 i.2 o.1 *
          (contScoreComponents M phi dphi L (eh (2*(n+1)) a) i.1 (i.2-1) o -
            contScoreComponents M phi dphi L
              (continuousBandRegressionHybrid (eh (2*(n+1)) a) (trueNuisance M L))
              i.1 (i.2-1) o) ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  let bh := fun n a => continuousBandRegressionHybrid (eh n a) (trueNuisance M L)
  let F := fun (i : ℕ × ℕ) n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
    ∫ o : Obs X Z, regularValue (eh (2*(n+1)) a).gamma i.1 i.2 o.1 *
      (contScoreComponents M phi dphi L (eh (2*(n+1)) a) i.1 (i.2-1) o -
        contScoreComponents M phi dphi L (bh (2*(n+1)) a) i.1 (i.2-1) o)
      ∂observationLaw M
  have hF i (hit : i ∈ t) : TendstoInMeasure μ (F i) atTop (fun _ => (0 : ℝ)) := by
    exact encoded_continuous_gamma_band_joint_regression_bias_root_n_negligible
      M μ phi dphi L eh bh he0 heh
      (fun n a => continuous_band_regression_hybrid_admissible M L _ _ (heh n a) he0)
      hr (encoded_continuous_band_regression_hybrid_rates M μ L _ eh hr)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      ⟨i.1, hk i hit⟩ i.2 c hc hclip
  have hs : TendstoInMeasure μ (fun n a => ∑ i ∈ t, F i n a)
      atTop (fun _ => (0 : ℝ)) := by
    induction t using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      intro eps heps
      simpa only [edist_self, not_le.mpr heps, Set.ofPred_false, measure_empty]
        using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
    | @insert i t hit ih =>
      have hi := hF i (Finset.mem_insert_self i t)
      have ht := ih (fun b hb => hk b (Finset.mem_insert_of_mem hb))
        (fun b hb => hF b (Finset.mem_insert_of_mem hb))
      simpa only [Finset.sum_insert hit] using hi.add_zero ht
  change TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ))
  simpa only [F, bh, Finset.mul_sum] using hs

-- @node: encoded_continuous_band_bias_restored_component_difference_root_n_negligible
/-- Suppose [the policy is valid](hyp:hphi), [the specified derivative differentiates it](hyp:hd), [the derivative is bounded and Lipschitz](hyp:hDerivative), [the true nuisance record is admissible](hyp:he0), [all fitted records are admissible](hyp:heh), and [their encoded coordinates satisfy the finite nuisance rates toward truth](hyp:hr). If [the finite collection contains valid nonterminal levels and regular bands](hyp:hidx), [the clipping bound is positive](hyp:hc), [fitted positive-level probabilities exceed it almost everywhere](hyp:hclip), and [fitted regular-band probabilities do too](hyp:htau), then [the population fitted band-product bias differs from the sum of gamma-weighted true-regression-restored component corrections by a quantity that, at even sample sizes and after multiplication by the square root of the half-sample size, converges in probability to zero](goal). -/
lemma encoded_continuous_band_bias_restored_component_difference_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X)
    (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (t : Finset (ℕ × ℕ))
    (hidx : ∀ i ∈ t, i.1 < L.K ∧ 1 ≤ i.2 ∧ i.2 ≤ L.l i.1)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x)
    (htau : ∀ n a r, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).tauLev r x) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        (((∫ o : Obs X Z, ∑ i ∈ t,
            psiProd M phi dphi L (eh (2*(n+1)) a) i.1 i.2 o ∂observationLaw M) -
          (∫ x, ∑ i ∈ t, gamma M L i.1 i.2 x *
            contJ L (trueNuisance M L) i.1 (i.2-1) x ∂xLaw M)) -
        (∑ i ∈ t, ∫ o : Obs X Z, regularValue (eh (2*(n+1)) a).gamma i.1 i.2 o.1 *
          (contScoreComponents M phi dphi L
              (continuousBandRegressionHybrid (eh (2*(n+1)) a) (trueNuisance M L))
              i.1 (i.2-1) o -
            contJ L (trueNuisance M L) i.1 (i.2-1) o.1) ∂observationLaw M)))
      atTop (fun _ _ => 0) := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  have hi n a i (hit : i ∈ t) :=
    (fitted_continuous_weighted_band_component_memLp M phi dphi hphi hd hDerivative L
      (eh n a) (heh n a) c hc (hclip n a) (htau n a) i.1 i.2
      (hidx i hit).1 (hidx i hit).2).integrable (by norm_num)

  have hb := encoded_continuous_band_product_bias_component_difference_root_n_negligible
    M μ phi dphi L eh he0 heh hr t (fun i hit => ⟨(hidx i hit).1.le, (hidx i hit).2⟩) hi
  have hd := encoded_continuous_restored_band_component_difference_root_n_negligible
    M μ phi dphi L eh he0 heh hr t (fun i hit => (hidx i hit).1) c hc hclip
  have hs := (show TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ)) from hb).add_zero
    (show TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ)) from hd)
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  have hi0 n a (i : ℕ × ℕ) : Integrable (fun o : Obs X Z =>
      regularValue (eh n a).gamma i.1 i.2 o.1 *
        contJ L (trueNuisance M L) i.1 (i.2-1) o.1) (observationLaw M) :=
    ((fitted_continuous_regular_gamma_memLp M L _ (heh n a) i.1 i.2).comp_measurePreserving
      (observationLaw_fst_measurePreserving M)).integrable_mul
      ((fitted_contJ_memLp M L _ he0 i.1 (i.2-1)).comp_measurePreserving
        (observationLaw_fst_measurePreserving M))
  have hih n a i (hit : i ∈ t) := continuous_restored_band_weighted_component_integrable
    M phi dphi L (eh n a) (trueNuisance M L) (heh n a) he0
    ⟨i.1, (hidx i hit).1⟩ i.2 c hc (hclip n a) (hi n a i hit)
  change TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ))
  convert hs using 1
  funext n a
  have hid :
      (∑ i ∈ t, ∫ o : Obs X Z, regularValue (eh (2*(n+1)) a).gamma i.1 i.2 o.1 *
        (contScoreComponents M phi dphi L (eh (2*(n+1)) a) i.1 (i.2-1) o -
          contJ L (trueNuisance M L) i.1 (i.2-1) o.1) ∂observationLaw M) =
      (∑ i ∈ t, ∫ o : Obs X Z, regularValue (eh (2*(n+1)) a).gamma i.1 i.2 o.1 *
        (contScoreComponents M phi dphi L
            (continuousBandRegressionHybrid (eh (2*(n+1)) a) (trueNuisance M L))
            i.1 (i.2-1) o - contJ L (trueNuisance M L) i.1 (i.2-1) o.1)
        ∂observationLaw M) +
      (∑ i ∈ t, ∫ o : Obs X Z, regularValue (eh (2*(n+1)) a).gamma i.1 i.2 o.1 *
        (contScoreComponents M phi dphi L (eh (2*(n+1)) a) i.1 (i.2-1) o -
          contScoreComponents M phi dphi L
            (continuousBandRegressionHybrid (eh (2*(n+1)) a) (trueNuisance M L))
            i.1 (i.2-1) o) ∂observationLaw M) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hit
    have he := hi (2*(n+1)) a i hit
    have hh := hih (2*(n+1)) a i hit
    have hzero := hi0 (2*(n+1)) a i
    simp only [mul_sub, integral_sub he hzero, integral_sub hh hzero,
      integral_sub he hh]
    ring
  rw [hid]
  ring

end Papers.TbsPrteOptimalTransport
