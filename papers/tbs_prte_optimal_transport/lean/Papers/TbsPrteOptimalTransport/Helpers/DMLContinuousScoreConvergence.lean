module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousEncodedFull
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousEncodedTail
public import Papers.TbsPrteOptimalTransport.Helpers.DMLQuantilePolicyBlock
/-! Second moments and L₂ convergence of the assembled continuous oracle score.
The full, fractional and terminal blocks are combined before applying conditional
Chebyshev to the evaluation-sample score difference. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
  [Fintype Z]

-- @node: continuous_total_score_block_decomposition
/-- With [a positive number of levels](hyp:hK), [the continuous total score equals the sum of the full-level score products, the regular-band score products, and the common tail score](goal). -/
lemma continuous_total_score_block_decomposition (M : LatentIVModel Ω X Z)
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (hK : LevelCountPos L.K) (e : NuisanceCont L) (o : Obs X Z) :
    psiCont M phi dphi L hK o e =
      (∑ k ∈ Finset.range L.K, psiFullProd L e k o) +
      (∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
        psiProd M phi dphi L e k j o) +
      commonTailScore M phi dphi L e.prop e.pLev e.piLev e.gammaTail o := by
  simp only [psiCont, Finset.sum_add_distrib]

set_option maxHeartbeats 800000 in
-- The three bounded block proofs require additional elaboration fuel.
-- @node: fitted_continuous_total_score_memLp
/-- Suppose [the policy is valid](hyp:hphi), [the specified derivative differentiates it](hyp:hd), [the derivative is bounded and Lipschitz](hyp:hDerivative), [the level count is positive](hyp:hK), [the nuisance record is admissible](hyp:he), [potential outcomes satisfy the support restriction](hyp:hp), [observed outcomes satisfy consistency](hyp:hcons), and [outcome endpoints are known](hyp:hend). If [the denominator bound is positive](hyp:hc), [positive-level probabilities exceed it almost everywhere](hyp:hpi), and [regular-band probabilities also exceed it almost everywhere](hyp:htau), then [the continuous total score is square integrable under the observation law](goal). -/
lemma fitted_continuous_total_score_memLp (M : LatentIVModel Ω X Z)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (e : NuisanceCont L) (he : ContAdmissible M L e)
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (c : ℝ) (hc : 0 < c)
    (hpi : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (htau : ∀ r : RegularIndex L, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x) :
    MemLp (fun o => psiCont M phi dphi L hK o e) 2 (observationLaw M) := by
  simp_rw [continuous_total_score_block_decomposition]
  exact ((fitted_continuous_full_score_block_memLp M L e he hp hcons hend c hc hpi).add
    (fitted_continuous_fractional_product_score_memLp M phi dphi hphi hd hDerivative
      L e he c hc hpi htau)).add
    (fitted_continuous_commonTailScore_memLp M phi dphi hphi hd hDerivative L e he c hc hpi)

-- @node: encoded_continuous_total_score_sq_tendsto_probability_zero
/-- Suppose [treatment follows the threshold-crossing model](hyp:h), [the policy is valid](hyp:hphi), [the specified derivative differentiates it](hyp:hd), [the derivative is bounded and Lipschitz](hyp:hDerivative), [the level count is positive](hyp:hK), [level ordering is policy invariant](hyp:hOrder), [potential outcomes satisfy the support restriction](hyp:hp), [observed outcomes satisfy consistency](hyp:hcons), and [outcome endpoints are known](hyp:hend). If [the true nuisance record is admissible](hyp:he0), [fitted records satisfy continuous clipping](hyp:hclip), [their shares lie in the simplex](hyp:hshares), [their encoded coordinates are measurable](hyp:hm), [those coordinates satisfy the finite nuisance rates toward truth](hyp:hr), [boundary densities are bounded](hyp:hDensity), [baseline overlap has the specified witness](hyp:hov), [policy overlap holds at the same bound](hyp:hpol), and [all fitted denominators are clipped at that bound](hyp:hden), then [the population integrated squared error of the continuous total score at even sample sizes converges in probability to zero](goal). -/
lemma encoded_continuous_total_score_sq_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A)
    (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L)))
    (hDensity : BoundaryDensitiesBounded M L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hpol : PolicyOverlap M L cpi)
    (hden : ∀ n t, ContDenominatorsClipped L (eh n t) cpi) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o : Obs X Z,
        (psiCont M phi dphi L hK o (eh (2*(n+1)) t) -
          psiCont M phi dphi L hK o (trueNuisance M L))^2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  have hc : 0 < cpi/2 := by linarith [hov.1]
  have hp0 (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, cpi/2 ≤ (trueNuisance M L).piLev i x := by
    apply Eventually.of_forall
    intro x
    have hx := hov.2 x i.val i.property.1 i.property.2
    change cpi/2 ≤ (levelSetProb M L).1 i.val x
    linarith [hov.1]
  have ht0 (r : RegularIndex L) :
      ∀ᵐ x ∂xLaw M, cpi/2 ≤ (trueNuisance M L).tauLev r x := by
    have hne := continuous_admissible_policy_nonempty M L _ he0 r
    apply Eventually.of_forall
    intro x
    have hx : cpi ≤ (trueNuisance M L).tauLev r x :=
      hpol.2 x r.val.1 r.val.2 r.property.1 r.property.2.1 r.property.2.2 hne
    linarith [hpol.1]
  have hpf n t (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, cpi/2 ≤ (er n t).piLev i x :=
    Eventually.of_forall (fun x => (hden n t).1 i x |>.1)
  have htf n t (r : RegularIndex L) :
      ∀ᵐ x ∂xLaw M, cpi/2 ≤ (er n t).tauLev r x :=
    Eventually.of_forall (fun x => ((hden n t).2 r x
      (contFittedSharesSimplex_policy_nonempty L (eh n t) (hshares n t) r)).1)
  let F := fun (e : NuisanceCont L) (o : Obs X Z) =>
    ∑ k ∈ Finset.range L.K, psiFullProd L e k o
  let G := fun (e : NuisanceCont L) (o : Obs X Z) =>
    ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k), psiProd M phi dphi L e k j o
  let T := fun (e : NuisanceCont L) =>
    commonTailScore M phi dphi L e.prop e.pLev e.piLev e.gammaTail
  have hF n t : MemLp (fun o => F (eh (2*(n+1)) t) o - F (trueNuisance M L) o)
      2 (observationLaw M) := by
    exact (fitted_continuous_full_score_block_memLp M L _ (her _ t) hp hcons hend
      (cpi/2) hc (hpf _ t)).sub
      (fitted_continuous_full_score_block_memLp M L _ he0 hp hcons hend (cpi/2) hc hp0)
  have hG n t : MemLp (fun o => G (eh (2*(n+1)) t) o - G (trueNuisance M L) o)
      2 (observationLaw M) := by
    have hf := fitted_continuous_fractional_product_score_memLp
      M phi dphi hphi hd hDerivative L (er (2*(n+1)) t) (her (2*(n+1)) t) (cpi/2) hc
        (hpf (2*(n+1)) t) (htf (2*(n+1)) t)
    have hf' : G (er (2*(n+1)) t) = G (eh (2*(n+1)) t) := by
      funext o
      have hs := psiCont_restrictContShares M phi dphi L hK o (eh (2*(n+1)) t)
      simp only [continuous_total_score_block_decomposition] at hs
      change F (eh (2*(n+1)) t) o + G (er (2*(n+1)) t) o + T (eh (2*(n+1)) t) o =
        F (eh (2*(n+1)) t) o + G (eh (2*(n+1)) t) o + T (eh (2*(n+1)) t) o at hs
      linarith
    change MemLp (G (er (2*(n+1)) t)) 2 (observationLaw M) at hf
    rw [hf'] at hf
    exact hf.sub (fitted_continuous_fractional_product_score_memLp
      M phi dphi hphi hd hDerivative L _ he0 (cpi/2) hc hp0 ht0)
  have hT n t : MemLp (fun o => -(T (eh (2*(n+1)) t) o - T (trueNuisance M L) o))
      2 (observationLaw M) :=
    ((fitted_continuous_commonTailScore_memLp M phi dphi hphi hd hDerivative L _
      (her _ t) (cpi/2) hc (hpf _ t)).sub
      (fitted_continuous_commonTailScore_memLp M phi dphi hphi hd hDerivative L _
        he0 (cpi/2) hc hp0)).neg
  have hrF := (encoded_continuous_full_oracle_remainders M μ h
    (policyProp phi M.prop) L hOrder hp hcons hend cpi hov he0 eh hclip hshares hm hden hr).2
  have hrG := encoded_continuous_fractional_product_score_sq_tendsto_probability_zero
    M μ phi dphi hphi hd hDerivative L he0 eh hclip hshares hm hr hDensity cpi hov hpol hden
  have hrT := (encoded_continuous_tail_oracle_remainders M μ h
    phi dphi hphi hd hDerivative L hK hOrder cpi hov he0 eh hclip hshares hm hden hr).2
  have hs := dml_three_term_sq_tendsto_probability_zero μ (observationLaw M)
    (fun n t o => F (eh (2*(n+1)) t) o - F (trueNuisance M L) o)
    (fun n t o => G (eh (2*(n+1)) t) o - G (trueNuisance M L) o)
    (fun n t o => -(T (eh (2*(n+1)) t) o - T (trueNuisance M L) o))
    hF hG hT hrF hrG (by simpa only [neg_sq] using hrT)
  convert hs using 1
  funext n t
  congr 1
  funext o
  simp only [continuous_total_score_block_decomposition, F, G, T]
  ring

-- @node: encoded_continuous_total_score_l2_tendsto_probability_zero
/-- Suppose [treatment follows the threshold-crossing model](hyp:h), [the policy is valid](hyp:hphi), [the specified derivative differentiates it](hyp:hd), [the derivative is bounded and Lipschitz](hyp:hDerivative), [the level count is positive](hyp:hK), [level ordering is policy invariant](hyp:hOrder), [potential outcomes satisfy the support restriction](hyp:hp), [observed outcomes satisfy consistency](hyp:hcons), and [outcome endpoints are known](hyp:hend). If [the true nuisance record is admissible](hyp:he0), [fitted records satisfy continuous clipping](hyp:hclip), [their shares lie in the simplex](hyp:hshares), [their encoded coordinates are measurable](hyp:hm), [those coordinates satisfy the finite nuisance rates toward truth](hyp:hr), [boundary densities are bounded](hyp:hDensity), [baseline overlap has the specified witness](hyp:hov), [policy overlap holds at the same bound](hyp:hpol), and [all fitted denominators are clipped at that bound](hyp:hden), then [the square root of the population integrated squared error of the continuous total score at even sample sizes converges in probability to zero](goal). -/
lemma encoded_continuous_total_score_l2_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A)
    (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L)))
    (hDensity : BoundaryDensitiesBounded M L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hpol : PolicyOverlap M L cpi)
    (hden : ∀ n t, ContDenominatorsClipped L (eh n t) cpi) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => Real.sqrt (∫ o : Obs X Z,
        (psiCont M phi dphi L hK o (eh (2*(n+1)) t) -
          psiCont M phi dphi L hK o (trueNuisance M L))^2 ∂observationLaw M))
      atTop (fun _ _ => 0) := by
  have hs := encoded_continuous_total_score_sq_tendsto_probability_zero
    M μ h phi dphi hphi hd hDerivative L hK hOrder hp hcons hend he0
    eh hclip hshares hm hr hDensity cpi hov hpol hden
  have hc : Continuous (fun t : ℝ => Real.sqrt t) := by fun_prop
  simpa only [Real.sqrt_zero] using
    Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt hc.continuousAt hs

end Papers.TbsPrteOptimalTransport
