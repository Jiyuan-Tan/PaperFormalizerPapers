module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLWeightedPolicyConvergence
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRegularHingeConvergence
/-! L2 convergence of the actual fractional binary product scores. The event
hinge, weighted regression correction, and weighted policy correction are
assembled before taking the finite sum over levels and boundaries. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedFintypeInType false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: psiProdBin_correction_split
/-- [The binary regular product score equals the policy-union indicator times the lower hinge, plus the regular weight times the regression correction, plus the regular weight times the policy correction](goal). -/
lemma psiProdBin_correction_split (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e : NuisanceBin L) (k j : ℕ) (o : Obs X Z) :
    psiProdBin phi dphi L e k j o =
      indicator (o.2.1 ∈ policyUnion L k j) * hMinus phi L e k j o.1 +
        regularValue e.gamma k j o.1 * binaryRegularRegressionCorrection phi L e k j o +
        regularValue e.gamma k j o.1 * binaryRegularPolicyCorrection phi dphi L e k j o := by
  rw [psiProdBin_event_hinge_split]
  unfold binScoreComponents binaryRegularRegressionCorrection binaryRegularPolicyCorrection
  ring

-- @node: fitted_regular_product_memLp
/-- For [a valid policy map](hyp:hphi) with [the specified derivative](hyp:hd) that is [bounded and Lipschitz](hyp:hDerivative), [admissible binary nuisances](hyp:he), and [an almost surely binary outcome](hyp:hy), assume [a positive common lower bound](hyp:hc) on [the level probabilities](hyp:hpi) and [the regular-cell probabilities](hyp:htau). At [a level below the level count](hyp:hk) and [a valid positive boundary](hyp:hj), [the fitted regular product score is square integrable under the observation distribution](goal). -/
lemma fitted_regular_product_memLp
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e)
    (hy : OutcomeBinaryAE M) (c : ℝ) (hc : 0 < c)
    (hpi : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (htau : ∀ r : RegularIndex L, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x)
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    MemLp (psiProdBin phi dphi L e k j) 2 (observationLaw M) := by
  have hh := fitted_event_hinge_memLp M phi hphi L e he k j hk hj
  have hr := fitted_weighted_regular_regression_correction_memLp M phi hphi L e he
    hy c hc hpi k j hk
  have hp := fitted_weighted_regular_policy_correction_memLp M phi dphi hphi hd hDerivative
    L e he c hc htau k j hk.le
  convert (hh.add hr).add hp using 1
  funext o
  exact psiProdBin_correction_split phi dphi L e k j o

-- @node: nuisanceRates_regular_product_sq_tendsto_probability_zero
/-- Suppose [the policy is valid](hyp:hphi), [has the specified derivative](hyp:hd), and [that derivative is bounded and Lipschitz](hyp:hDerivative), with [admissible reference nuisances](hyp:he0), [every fitted nuisance collection admissible](hyp:heh), and [an almost surely binary outcome](hyp:hy). If [a positive constant](hyp:hc) bounds below [both reference and fitted level probabilities](hyp:hpi) and [both reference and fitted regular-cell probabilities](hyp:htau), the componentwise L² errors in [propensities](hyp:hrp), [level masses](hyp:hrlev), [outcome regressions](hyp:hrP), [level probabilities](hyp:hrpi), [regular-cell probabilities](hyp:hrt), [shares within every regular cell](hyp:hrs), and [regular product weights](hyp:hrg) are negligible at the inverse-fourth-root sample-size rate, and, at [a level below the level count](hyp:hk) and [a valid positive boundary](hyp:hj), [a positive separation constant](hyp:hsep) [bounds below the reference pooled-argument gap and the distances of the probability-minus-full-level argument from both pooled arguments almost surely](hyp:hgap), then [the population mean squared fitted-minus-reference regular product score converges to zero in probability along even sample sizes](goal). -/
lemma nuisanceRates_regular_product_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hy : OutcomeBinaryAE M) (c : ℝ) (hc : 0 < c)
    (hpi : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (htau : ∀ n a (r : RegularIndex L), ∀ᵐ x ∂xLaw M,
      c ≤ e0.tauLev r x ∧ c ≤ (eh n a).tauLev r x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrt : FiniteNuisanceRates M μ (fun n a => (eh n a).tauLev) e0.tauLev)
    (hrs : ∀ r : RegularIndex L,
      FiniteNuisanceRates M μ (fun n a => (eh n a).share r) (e0.share r))
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gamma) e0.gamma)
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (sep : ℝ) (hsep : 0 < sep)
    (hgap : ∀ᵐ x ∂xLaw M,
      sep ≤ pooledQBin phi L e0 k j x - pooledQBin phi L e0 k (j-1) x ∧
      sep ≤ |positiveValue e0.pLev (k+1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k (j-1) x| ∧
      sep ≤ |positiveValue e0.pLev (k+1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k j x|) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        (psiProdBin phi dphi L (eh (2*(n+1)) a) k j o -
          psiProdBin phi dphi L e0 k j o)^2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  let H := fun (e : NuisanceBin L) (o : Obs X Z) =>
    indicator (o.2.1 ∈ policyUnion L k j) * hMinus phi L e k j o.1
  let R := fun (e : NuisanceBin L) (o : Obs X Z) =>
    regularValue e.gamma k j o.1 * binaryRegularRegressionCorrection phi L e k j o
  let P := fun (e : NuisanceBin L) (o : Obs X Z) =>
    regularValue e.gamma k j o.1 * binaryRegularPolicyCorrection phi dphi L e k j o
  have hH (e : NuisanceBin L) (he : BinAdmissible M L e) :=
    fitted_event_hinge_memLp M phi hphi L e he k j hk hj
  have hR (e : NuisanceBin L) (he : BinAdmissible M L e)
      (hcl : ∀ i, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) :=
    fitted_weighted_regular_regression_correction_memLp M phi hphi L e he hy c hc hcl k j hk
  have hP (e : NuisanceBin L) (he : BinAdmissible M L e)
      (hcl : ∀ r, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x) :=
    fitted_weighted_regular_policy_correction_memLp M phi dphi hphi hd hDerivative
      L e he c hc hcl k j hk.le
  have hrH := nuisanceRates_event_hinge_sq_tendsto_probability_zero M μ phi dphi hphi hd
    hDerivative L e0 eh he0 heh hrp hrlev hrP hrs k j hk hj
  have hrR := nuisanceRates_weighted_regular_regression_correction_sq_tendsto_probability_zero
    M μ phi dphi hphi hd hDerivative L e0 eh he0 heh hy c hc hpi
    hrp hrlev hrP hrpi hrs hrg k j hk hj sep hsep hgap
  have hrP' := nuisanceRates_weighted_regular_policy_correction_sq_tendsto_probability_zero
    M μ phi dphi hphi hd hDerivative L e0 eh he0 heh c hc htau
    hrp hrlev hrP hrt hrs hrg k j hk hj sep hsep hgap
  have hs := dml_three_term_sq_tendsto_probability_zero μ (observationLaw M)
    (fun n a o => H (eh (2*(n+1)) a) o - H e0 o)
    (fun n a o => R (eh (2*(n+1)) a) o - R e0 o)
    (fun n a o => -(P (eh (2*(n+1)) a) o - P e0 o))
    (fun n a => (hH _ (heh _ a)).sub (hH e0 he0))
    (fun n a => (hR _ (heh _ a) (fun i => (hpi _ a i).mono (fun _ hx => hx.2))).sub
      (hR e0 he0 (fun i => (hpi (2*(n+1)) a i).mono (fun _ hx => hx.1))))
    (fun n a => ((hP _ (heh _ a) (fun r => (htau _ a r).mono (fun _ hx => hx.2))).sub
      (hP e0 he0 (fun r => (htau (2*(n+1)) a r).mono (fun _ hx => hx.1)))).neg)
    hrH hrR (by simpa only [P, neg_sq] using hrP')
  have hid (n : ℕ) (a : A) (o : Obs X Z) :
      psiProdBin phi dphi L (eh (2*(n+1)) a) k j o - psiProdBin phi dphi L e0 k j o =
      (H (eh (2*(n+1)) a) o - H e0 o) + (R (eh (2*(n+1)) a) o - R e0 o) -
        -(P (eh (2*(n+1)) a) o - P e0 o) := by
    simp only [psiProdBin_correction_split, H, R, P]
    ring
  simpa only [hid] using hs

-- @node: fitted_regular_score_block_memLp
/-- With [a valid policy map](hyp:hphi), [its specified derivative](hyp:hd) that is [bounded and Lipschitz](hyp:hDerivative), [admissible binary nuisances](hyp:he), and [an almost surely binary outcome](hyp:hy), suppose [a positive constant](hyp:hc) bounds below [every level probability](hyp:hpi) and [every regular-cell probability](hyp:htau). Then [the sum of the regular product scores over all levels below the level count and all their positive boundaries is square integrable under the observation distribution](goal). -/
lemma fitted_regular_score_block_memLp
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e)
    (hy : OutcomeBinaryAE M) (c : ℝ) (hc : 0 < c)
    (hpi : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (htau : ∀ r : RegularIndex L, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x) :
    MemLp (fun o : Obs X Z => ∑ k ∈ Finset.range L.K,
      ∑ j ∈ Finset.Icc 1 (L.l k), psiProdBin phi dphi L e k j o) 2 (observationLaw M) := by
  apply memLp_finsetSum
  intro k hk
  apply memLp_finsetSum
  intro j hj
  exact fitted_regular_product_memLp M phi dphi hphi hd hDerivative L e he hy c hc hpi htau
    k j (Finset.mem_range.mp hk) (Finset.mem_Icc.mp hj)

-- @node: nuisanceRates_regular_score_block_sq_tendsto_probability_zero
/-- For [a valid policy](hyp:hphi) with [the specified derivative](hyp:hd) that is [bounded and Lipschitz](hyp:hDerivative), assume [admissible reference nuisances](hyp:he0), [admissible fitted nuisances at every sample size and realization](hyp:heh), [an almost surely binary outcome](hyp:hy), and [a positive common lower bound](hyp:hc) on [reference and fitted level probabilities](hyp:hpi) and [reference and fitted regular-cell probabilities](hyp:htau). If componentwise L² errors for [propensities](hyp:hrp), [level masses](hyp:hrlev), [outcome regressions](hyp:hrP), [level probabilities](hyp:hrpi), [regular-cell probabilities](hyp:hrt), [shares in each regular cell](hyp:hrs), and [regular weights](hyp:hrg) are negligible at the inverse-fourth-root sample-size rate, and [a positive separation constant](hyp:hsep) [uniformly separates the two reference pooled arguments and separates the probability-minus-full-level argument from each of them at every valid level and boundary, almost surely](hyp:hgap), then [the population mean squared difference between the fitted and reference sums of regular product scores converges to zero in probability along even sample sizes](goal). -/
lemma nuisanceRates_regular_score_block_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hy : OutcomeBinaryAE M) (c : ℝ) (hc : 0 < c)
    (hpi : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (htau : ∀ n a (r : RegularIndex L), ∀ᵐ x ∂xLaw M,
      c ≤ e0.tauLev r x ∧ c ≤ (eh n a).tauLev r x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrt : FiniteNuisanceRates M μ (fun n a => (eh n a).tauLev) e0.tauLev)
    (hrs : ∀ r : RegularIndex L,
      FiniteNuisanceRates M μ (fun n a => (eh n a).share r) (e0.share r))
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gamma) e0.gamma)
    (sep : ℝ) (hsep : 0 < sep)
    (hgap : ∀ k, k < L.K → ∀ j, 1 ≤ j ∧ j ≤ L.l k → ∀ᵐ x ∂xLaw M,
      sep ≤ pooledQBin phi L e0 k j x - pooledQBin phi L e0 k (j-1) x ∧
      sep ≤ |positiveValue e0.pLev (k+1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k (j-1) x| ∧
      sep ≤ |positiveValue e0.pLev (k+1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k j x|) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        ((∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
            psiProdBin phi dphi L (eh (2*(n+1)) a) k j o) -
          ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
            psiProdBin phi dphi L e0 k j o)^2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  let F := fun (k j n : ℕ) (a : A) (o : Obs X Z) =>
    psiProdBin phi dphi L (eh (2*(n+1)) a) k j o - psiProdBin phi dphi L e0 k j o
  have hF (k j n : ℕ) (a : A) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
      MemLp (F k j n a) 2 (observationLaw M) :=
    (fitted_regular_product_memLp M phi dphi hphi hd hDerivative L _ (heh _ a) hy c hc
      (fun i => (hpi _ a i).mono (fun _ hx => hx.2))
      (fun r => (htau _ a r).mono (fun _ hx => hx.2)) k j hk hj).sub
      (fitted_regular_product_memLp M phi dphi hphi hd hDerivative L e0 he0 hy c hc
        (fun i => (hpi (2*(n+1)) a i).mono (fun _ hx => hx.1))
        (fun r => (htau (2*(n+1)) a r).mono (fun _ hx => hx.1)) k j hk hj)
  have hs := dml_finset_sum_sq_tendsto_probability_zero μ (observationLaw M)
    (Finset.range L.K) (fun k n a o => ∑ j ∈ Finset.Icc 1 (L.l k), F k j n a o)
    (fun k hk n a => memLp_finsetSum _
      (fun j hj => hF k j n a (Finset.mem_range.mp hk) (Finset.mem_Icc.mp hj))) (by
      intro k hk
      apply dml_finset_sum_sq_tendsto_probability_zero μ (observationLaw M)
        (Finset.Icc 1 (L.l k)) (F k)
        (fun j hj n a => hF k j n a (Finset.mem_range.mp hk) (Finset.mem_Icc.mp hj))
      intro j hj
      exact nuisanceRates_regular_product_sq_tendsto_probability_zero M μ phi dphi hphi hd
        hDerivative L e0 eh he0 heh hy c hc hpi htau hrp hrlev hrP hrpi hrt hrs hrg
        k j (Finset.mem_range.mp hk) (Finset.mem_Icc.mp hj) sep hsep
        (hgap k (Finset.mem_range.mp hk) j (Finset.mem_Icc.mp hj)))
  simpa only [F, Finset.sum_sub_distrib] using hs

-- @node: fitted_binary_score_memLp
/-- Given [a valid policy map](hyp:hphi) with [the specified derivative](hyp:hd) that is [bounded and Lipschitz](hyp:hDerivative), [a positive level count](hyp:hK), [admissible binary nuisances](hyp:he), and [an almost surely binary outcome](hyp:hy), if [a positive constant](hyp:hc) bounds below [all level probabilities](hyp:hpi) and [all regular-cell probabilities](hyp:htau), then [the complete fitted binary score is square integrable under the observation distribution](goal). -/
lemma fitted_binary_score_memLp
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (e : NuisanceBin L) (he : BinAdmissible M L e)
    (hy : OutcomeBinaryAE M) (c : ℝ) (hc : 0 < c)
    (hpi : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (htau : ∀ r : RegularIndex L, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x) :
    MemLp (fun o => psiBin M phi dphi L hK o e) 2 (observationLaw M) := by
  have hfull := fitted_full_score_block_memLp M L e he hy c hc hpi
  have hreg := fitted_regular_score_block_memLp M phi dphi hphi hd hDerivative
    L e he hy c hc hpi htau
  have htail := fitted_commonTailScore_memLp M phi dphi hphi hd hDerivative L e he c hc hpi
  convert (hfull.add hreg).add htail using 1
  funext o
  simp only [psiBin, Finset.sum_add_distrib, Pi.add_apply]

-- Every score block is now controlled by original nuisance rates.
-- @node: nuisanceRates_binary_score_sq_tendsto_probability_zero
/-- Assume [a valid policy map](hyp:hphi), [its specified derivative](hyp:hd) that is [bounded and Lipschitz](hyp:hDerivative), [a positive level count](hyp:hK), [admissible reference nuisances](hyp:he0), [admissible fitted nuisances for every sample size and realization](hyp:heh), and [an almost surely binary outcome](hyp:hy), with [a positive common lower bound](hyp:hc) on [reference and fitted level probabilities](hyp:hpi) and [reference and fitted regular-cell probabilities](hyp:htau). If componentwise L² errors for [propensities](hyp:hrp), [level masses](hyp:hrlev), [outcome regressions](hyp:hrP), [level probabilities](hyp:hrpi), [regular-cell probabilities](hyp:hrt), [regular-cell shares](hyp:hrs), [regular weights](hyp:hrg), [full-level weights](hyp:hrfull), and [the tail weight](hyp:hrtail) are negligible at the inverse-fourth-root sample-size rate, and [a positive separation constant](hyp:hsep) [bounds below every reference pooled-argument gap and both distances from the probability-minus-full-level argument to the pooled arguments almost surely](hyp:hgap), then [the population mean squared difference between the complete fitted and reference binary scores converges to zero in probability along even sample sizes](goal). -/
lemma nuisanceRates_binary_score_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hy : OutcomeBinaryAE M) (c : ℝ) (hc : 0 < c)
    (hpi : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (htau : ∀ n a (r : RegularIndex L), ∀ᵐ x ∂xLaw M,
      c ≤ e0.tauLev r x ∧ c ≤ (eh n a).tauLev r x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrt : FiniteNuisanceRates M μ (fun n a => (eh n a).tauLev) e0.tauLev)
    (hrs : ∀ r : RegularIndex L,
      FiniteNuisanceRates M μ (fun n a => (eh n a).share r) (e0.share r))
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gamma) e0.gamma)
    (hrfull : FiniteNuisanceRates M μ (fun n a => (eh n a).gammaFull) e0.gammaFull)
    (hrtail : FiniteNuisanceRates M μ (fun n a (_ : Unit) => (eh n a).gammaTail)
      (fun _ => e0.gammaTail))
    (sep : ℝ) (hsep : 0 < sep)
    (hgap : ∀ k, k < L.K → ∀ j, 1 ≤ j ∧ j ≤ L.l k → ∀ᵐ x ∂xLaw M,
      sep ≤ pooledQBin phi L e0 k j x - pooledQBin phi L e0 k (j-1) x ∧
      sep ≤ |positiveValue e0.pLev (k+1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k (j-1) x| ∧
      sep ≤ |positiveValue e0.pLev (k+1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k j x|) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        (psiBin M phi dphi L hK o (eh (2*(n+1)) a) -
          psiBin M phi dphi L hK o e0)^2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  let F := fun (e : NuisanceBin L) (o : Obs X Z) =>
    ∑ k ∈ Finset.range L.K, psiFullProdBin L e k o
  let R := fun (e : NuisanceBin L) (o : Obs X Z) =>
    ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k), psiProdBin phi dphi L e k j o
  let T := fun (e : NuisanceBin L) => commonTailScore M phi dphi L e.prop e.pLev e.piLev e.gammaTail
  have hF (e : NuisanceBin L) (he : BinAdmissible M L e)
      (hcl : ∀ i, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) :=
    fitted_full_score_block_memLp M L e he hy c hc hcl
  have hR (e : NuisanceBin L) (he : BinAdmissible M L e)
      (hcl : ∀ i, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
      (hct : ∀ r, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x) :=
    fitted_regular_score_block_memLp M phi dphi hphi hd hDerivative L e he hy c hc hcl hct
  have hT (e : NuisanceBin L) (he : BinAdmissible M L e)
      (hcl : ∀ i, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) :=
    fitted_commonTailScore_memLp M phi dphi hphi hd hDerivative L e he c hc hcl
  have hrF := nuisanceRates_full_score_block_sq_tendsto_probability_zero M μ L e0 eh
    he0 heh hy c hc hpi hrP hrpi hrfull
  have hsum (e : NuisanceBin L) (o : Obs X Z) :
      (∑ k : Fin L.K, psiFullProdBin L e k o) = F e o :=
    Fin.sum_univ_eq_sum_range (fun k => psiFullProdBin L e k o) L.K
  simp only [hsum] at hrF
  have hrR := nuisanceRates_regular_score_block_sq_tendsto_probability_zero M μ phi dphi hphi
    hd hDerivative L e0 eh he0 heh hy c hc hpi htau hrp hrlev hrP hrpi hrt hrs hrg sep hsep hgap
  have hrT := nuisanceRates_commonTailScore_sq_tendsto_probability_zero M μ phi dphi hphi hd
    hDerivative L e0 eh he0 heh c hc hpi hrp hrlev hrpi hrtail
  have hs := dml_three_term_sq_tendsto_probability_zero μ (observationLaw M)
    (fun n a o => F (eh (2*(n+1)) a) o - F e0 o)
    (fun n a o => R (eh (2*(n+1)) a) o - R e0 o)
    (fun n a o => -(T (eh (2*(n+1)) a) o - T e0 o))
    (fun n a => (hF _ (heh _ a) (fun i => (hpi _ a i).mono (fun _ hx => hx.2))).sub
      (hF e0 he0 (fun i => (hpi (2*(n+1)) a i).mono (fun _ hx => hx.1))))
    (fun n a => (hR _ (heh _ a) (fun i => (hpi _ a i).mono (fun _ hx => hx.2))
      (fun r => (htau _ a r).mono (fun _ hx => hx.2))).sub
      (hR e0 he0 (fun i => (hpi (2*(n+1)) a i).mono (fun _ hx => hx.1))
        (fun r => (htau (2*(n+1)) a r).mono (fun _ hx => hx.1))))
    (fun n a => ((hT _ (heh _ a) (fun i => (hpi _ a i).mono (fun _ hx => hx.2))).sub
      (hT e0 he0 (fun i => (hpi (2*(n+1)) a i).mono (fun _ hx => hx.1)))).neg)
    hrF hrR (by simpa only [T, neg_sq] using hrT)
  have hid (n : ℕ) (a : A) (o : Obs X Z) :
      psiBin M phi dphi L hK o (eh (2*(n+1)) a) - psiBin M phi dphi L hK o e0 =
      (F (eh (2*(n+1)) a) o - F e0 o) + (R (eh (2*(n+1)) a) o - R e0 o) -
        -(T (eh (2*(n+1)) a) o - T e0 o) := by
    simp only [psiBin, Finset.sum_add_distrib, F, R, T]
    ring
  simpa only [hid] using hs

-- @node: nuisanceRates_binary_score_l2_tendsto_probability_zero
/-- Suppose [the policy map is valid](hyp:hphi), [has the specified derivative](hyp:hd), and [its derivative is bounded and Lipschitz](hyp:hDerivative), with [a positive level count](hyp:hK), [admissible reference nuisances](hyp:he0), [admissible fitted nuisances throughout](hyp:heh), and [an almost surely binary outcome](hyp:hy). Under [a positive common lower bound](hyp:hc) for [reference and fitted level probabilities](hyp:hpi) and [reference and fitted regular-cell probabilities](hyp:htau), inverse-fourth-root little-o rates for the componentwise L² errors in [propensities](hyp:hrp), [level masses](hyp:hrlev), [outcome regressions](hyp:hrP), [level probabilities](hyp:hrpi), [regular-cell probabilities](hyp:hrt), [regular-cell shares](hyp:hrs), [regular weights](hyp:hrg), [full-level weights](hyp:hrfull), and [the tail weight](hyp:hrtail), and [a positive separation constant](hyp:hsep) [separating the reference pooled arguments from each other and the probability-minus-full-level argument from both of them at every valid level and boundary almost surely](hyp:hgap), [the population L² distance between the complete fitted and reference binary scores converges to zero in probability along even sample sizes](goal). -/
lemma nuisanceRates_binary_score_l2_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hy : OutcomeBinaryAE M) (c : ℝ) (hc : 0 < c)
    (hpi : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (htau : ∀ n a (r : RegularIndex L), ∀ᵐ x ∂xLaw M,
      c ≤ e0.tauLev r x ∧ c ≤ (eh n a).tauLev r x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrt : FiniteNuisanceRates M μ (fun n a => (eh n a).tauLev) e0.tauLev)
    (hrs : ∀ r : RegularIndex L,
      FiniteNuisanceRates M μ (fun n a => (eh n a).share r) (e0.share r))
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gamma) e0.gamma)
    (hrfull : FiniteNuisanceRates M μ (fun n a => (eh n a).gammaFull) e0.gammaFull)
    (hrtail : FiniteNuisanceRates M μ (fun n a (_ : Unit) => (eh n a).gammaTail)
      (fun _ => e0.gammaTail))
    (sep : ℝ) (hsep : 0 < sep)
    (hgap : ∀ k, k < L.K → ∀ j, 1 ≤ j ∧ j ≤ L.l k → ∀ᵐ x ∂xLaw M,
      sep ≤ pooledQBin phi L e0 k j x - pooledQBin phi L e0 k (j-1) x ∧
      sep ≤ |positiveValue e0.pLev (k+1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k (j-1) x| ∧
      sep ≤ |positiveValue e0.pLev (k+1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k j x|) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt (∫ o : Obs X Z,
        (psiBin M phi dphi L hK o (eh (2*(n+1)) a) -
          psiBin M phi dphi L hK o e0)^2 ∂observationLaw M))
      atTop (fun _ _ => 0) := by
  have hs := nuisanceRates_binary_score_sq_tendsto_probability_zero M μ phi dphi hphi hd
    hDerivative L hK e0 eh he0 heh hy c hc hpi htau hrp hrlev hrP hrpi hrt hrs hrg
    hrfull hrtail sep hsep hgap
  have hcont : Continuous (fun t : ℝ => Real.sqrt t) := by fun_prop
  simpa only [Real.sqrt_zero] using
    Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt hcont.continuousAt hs

end Papers.TbsPrteOptimalTransport
