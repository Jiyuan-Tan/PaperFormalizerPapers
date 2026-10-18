module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBinaryBiasAssembly
public import Papers.TbsPrteOptimalTransport.Helpers.DMLOracleRemainder
/-! Root-n equivalence of the fitted binary oracle evaluation average and
its true-score average, using the original componentwise nuisance rates. -/
public section

set_option linter.style.haveILetI false
set_option linter.style.longLine false
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

-- @node: nuisanceRates_binary_oracle_remainder_negligible
/-- Under [equal half-split sampling](hyp:hSplit), [a valid policy map](hyp:hphi),
[its specified derivative](hyp:hd), [a bounded Lipschitz derivative](hyp:hDerivative),
[threshold crossing](hyp:h), and [almost surely binary outcomes](hyp:hy), assume
[a positive level count](hyp:hK), [measurable baseline level propensities](hyp:hlev),
[covariate-invariant level ordering](hyp:hOrder), [policy overlap](hyp:hov),
[baseline overlap](hyp:hbase), [an admissible true nuisance record](hyp:he0), and
[admissible fitted records](hyp:heh). Suppose [the fitted denominator bound is positive](hyp:hc),
[the branch-separation bound is positive](hyp:hsep), and almost surely the fitted
[baseline masses](hyp:hpi) and [regular group masses](hyp:htau) exceed the denominator bound.
Assume finite nuisance rates for [instrument propensities](hyp:hrp),
[baseline level propensities](hyp:hrlev), [treated-success regressions](hyp:hrP),
[baseline masses](hyp:hrpi), [each group's shares](hyp:hrs), [regular group masses](hyp:hrt),
[regular policy-union probability weights](hyp:hrg), [higher-policy minus higher-baseline probability weights](hyp:hrfull), and
[the tail policy probability](hyp:hrtail), with [adjacent true pooled policy levels separated
by the branch bound and both endpoints separated by that bound from the adjusted next baseline level](hyp:hgap).
If [the fitted-minus-true score factors through the training data and a fresh observation](hyp:hscore)
via [a sample-size-indexed function of the training view and a fresh observation](hyp:f)
that is [measurable](hyp:hf), [square integrable for each training realization](hyp:hsection),
and [square integrable when evaluated on each evaluation observation](hyp:hfit), then
[the difference between fitted and true score averages, multiplied by the square root
of the evaluation-sample size, converges in probability to zero](goal). -/
lemma nuisanceRates_binary_oracle_remainder_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (h : ThresholdCrossing M) (hy : OutcomeBinaryAE M)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hlev : ∀ k, Measurable (L.pLev k))
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi)
    (hbase : BaselineOverlapWitness M L cpi)
    (he0 : BinAdmissible M L (eta0Bin M L)) (eh : ℕ → A → NuisanceBin L)
    (heh : ∀ n a, BinAdmissible M L (eh n a))
    (c sep : ℝ) (hc : 0 < c) (hsep : 0 < sep)
    (hpi : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x)
    (htau : ∀ n a t, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).tauLev t x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) M.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) (eta0Bin M L).pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) (eta0Bin M L).P1)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) (eta0Bin M L).piLev)
    (hrs : ∀ t, FiniteNuisanceRates M μ (fun n a => (eh n a).share t) ((eta0Bin M L).share t))
    (hrt : FiniteNuisanceRates M μ (fun n a => (eh n a).tauLev) (eta0Bin M L).tauLev)
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gamma) (eta0Bin M L).gamma)
    (hrfull : FiniteNuisanceRates M μ (fun n a => (eh n a).gammaFull) (eta0Bin M L).gammaFull)
    (hrtail : FiniteNuisanceRates M μ (fun n a (_ : Unit) => (eh n a).gammaTail)
      (fun _ => (eta0Bin M L).gammaTail))
    (hgap : ∀ k ∈ Finset.range L.K, ∀ j ∈ Finset.Icc 1 (L.l k), ∀ᵐ x ∂xLaw M,
      sep ≤ pooledQBin phi L (eta0Bin M L) k j x -
        pooledQBin phi L (eta0Bin M L) k (j - 1) x ∧
      sep ≤ |positiveValue (eta0Bin M L).pLev (k + 1) x -
        binFullJ L (eta0Bin M L) k x -
        pooledQBin phi L (eta0Bin M L) k (j - 1) x| ∧
      sep ≤ |positiveValue (eta0Bin M L).pLev (k + 1) x -
        binFullJ L (eta0Bin M L) k x -
        pooledQBin phi L (eta0Bin M L) k j x|)
    (f : ∀ n, (Finset ℕ × (Fin (2 * (n + 1)) → Unit ⊕ Obs X Z)) × Obs X Z → ℝ)
    (hscore : ∀ n a o,
      psiBin M phi dphi L hK o (eh (2 * (n + 1)) a) -
        psiBin M phi dphi L hK o (eta0Bin M L) =
      f n (trainingView M S I₁ (2 * (n + 1)) a, o))
    (hf : ∀ n, Measurable (f n))
    (hsection : ∀ n t, MemLp (fun o => f n (t, o)) 2 (observationLaw M))
    (hfit : ∀ n i, MemLp (fun a => f n
      (trainingView M S I₁ (2 * (n + 1)) a,
        S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) a) i) a)) 2 μ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (dmlRV M S I₂ (fun n a o => psiBin M phi dphi L hK o (eh n a))
            (2 * (n + 1)) a -
          dmlRV M S I₂ (fun _ _ o => psiBin M phi dphi L hK o (eta0Bin M L))
            (2 * (n + 1)) a)) atTop (fun _ _ => 0) := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  have hpi0 (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, cpi ≤ (eta0Bin M L).piLev i x :=
    Eventually.of_forall (fun x => hbase.2 x i i.property.1 i.property.2)
  have htau0 (r : RegularIndex L) :
      ∀ᵐ x ∂xLaw M, cpi ≤ (eta0Bin M L).tauLev r x :=
    Eventually.of_forall (fun x => hov.2 x r.val.1 r.val.2 r.property.1 r.property.2.1 r.property.2.2
      (ordered_policy_level_nonempty M _ L hOrder _ _ r.property.1
        r.property.2.1 r.property.2.2))
  have hc' : 0 < min c cpi := lt_min hc hbase.1
  have hpiboth (n : ℕ) (a : A) (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, min c cpi ≤ (eta0Bin M L).piLev i x ∧
        min c cpi ≤ (eh n a).piLev i x := by
    filter_upwards [hpi0 i, hpi n a i] with x h0 hh
    exact ⟨(min_le_right _ _).trans h0, (min_le_left _ _).trans hh⟩
  have htauboth (n : ℕ) (a : A) (r : RegularIndex L) :
      ∀ᵐ x ∂xLaw M, min c cpi ≤ (eta0Bin M L).tauLev r x ∧
        min c cpi ≤ (eh n a).tauLev r x := by
    filter_upwards [htau0 r, htau n a r] with x h0 hh
    exact ⟨(min_le_right _ _).trans h0, (min_le_left _ _).trans hh⟩
  have hr := nuisanceRates_binary_score_sq_tendsto_probability_zero M μ phi dphi
    hphi hd hDerivative L hK (eta0Bin M L) eh he0 heh hy (min c cpi) hc'
    hpiboth htauboth hrp hrlev hrP hrpi hrt hrs hrg hrfull hrtail sep hsep
    (fun k hk j hj => hgap k (Finset.mem_range.mpr hk) j (Finset.mem_Icc.mpr hj))
  have hb := nuisanceRates_binary_score_bias_root_n_negligible M μ phi dphi hphi
    hd hDerivative h hy L hK hlev hOrder cpi hov hbase he0 eh heh c sep hc hsep
    hpi htau hrp hrlev hrP hrpi hrs hrt hrg hrfull hrtail hgap
  have hi (n : ℕ) (a : A) :
      (∫ o, f n (trainingView M S I₁ (2 * (n + 1)) a, o) ∂observationLaw M) =
      (∫ o, psiBin M phi dphi L hK o (eh (2 * (n + 1)) a) ∂observationLaw M) -
        (∫ o, psiBin M phi dphi L hK o (eta0Bin M L) ∂observationLaw M) := by
    simp_rw [← hscore]
    exact integral_sub
      ((fitted_binary_score_memLp M phi dphi hphi hd hDerivative L hK _
        (heh _ a) hy c hc (hpi _ a) (htau _ a)).integrable (by norm_num))
      ((fitted_binary_score_memLp M phi dphi hphi hd hDerivative L hK _
        he0 hy cpi hbase.1 hpi0 htau0).integrable (by norm_num))
  apply equalHalfSplit_oracle_score_remainder_negligible M μ S I₁ I₂ hSplit
    (fun n a o => psiBin M phi dphi L hK o (eh n a))
    (fun o => psiBin M phi dphi L hK o (eta0Bin M L)) f hscore hf hsection hfit
  · simpa only [← hscore] using hr
  · simpa only [hi] using hb

end Papers.TbsPrteOptimalTransport
