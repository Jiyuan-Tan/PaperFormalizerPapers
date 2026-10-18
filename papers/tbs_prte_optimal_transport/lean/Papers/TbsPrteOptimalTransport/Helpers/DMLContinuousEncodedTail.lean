module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousComponentBridge
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousTailBias
/-! Continuous terminal-score oracle remainders from the encoded nuisance conditions.
The policy derivative condition supplies the Taylor constant, and denominator
clipping supplies a common positive bound for the fitted and true scores. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]

-- @node: encoded_continuous_tail_oracle_remainders
/-- Under [threshold crossing](hyp:h), [a valid policy map](hyp:hphi), [differentiability with the specified policy derivative](hyp:hd),
[a bounded Lipschitz policy derivative](hyp:hDerivative), [a positive treatment-level count](hyp:hK),
[invariant ordering of baseline and policy treatment levels](hyp:hOrder), [baseline assignment overlap with the specified constant](hyp:hov), and
[admissibility of the true nuisance record](hyp:he0), suppose [fitted records obey clipping bounds](hyp:hclip),
[their shares form simplices on policy sets](hyp:hshares), [their encoded coordinates are measurable](hyp:hm),
[their denominators are clipped using the overlap constant](hyp:hden), and [the encoded nuisance family satisfies the finite nuisance rates](hyp:hr).
Then [both the square-root-scaled population mean difference and the population squared difference between fitted and true common tail scores converge in probability to zero, using fits at sample size twice a positive integer and scaling by the square root of that integer](goal). -/
lemma encoded_continuous_tail_oracle_remainders (M : LatentIVModel Ω X Z)
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n a, ContClipping M L (eh n a))
    (hshares : ∀ n a, ContFittedSharesSimplex L (eh n a))
    (hm : ∀ n a c, Measurable (contComponent M L (eh n a) c))
    (hden : ∀ n a, ContDenominatorsClipped L (eh n a) cpi)
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L))) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        ((∫ o, commonTailScore M phi dphi L (eh (2*(n+1)) a).prop
            (eh (2*(n+1)) a).pLev (eh (2*(n+1)) a).piLev
            (eh (2*(n+1)) a).gammaTail o ∂observationLaw M) -
          (∫ o, commonTailScore M phi dphi L (trueNuisance M L).prop
            (trueNuisance M L).pLev (trueNuisance M L).piLev
            (trueNuisance M L).gammaTail o ∂observationLaw M)))
      atTop (fun _ _ => 0) ∧
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o,
        (commonTailScore M phi dphi L (eh (2*(n+1)) a).prop
            (eh (2*(n+1)) a).pLev (eh (2*(n+1)) a).piLev
            (eh (2*(n+1)) a).gammaTail o -
          commonTailScore M phi dphi L (trueNuisance M L).prop
            (trueNuisance M L).pLev (trueNuisance M L).piLev
            (trueNuisance M L).gammaTail o)^2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  let er := fun n a => restrictContShares L (eh n a)
  have her n a : ContAdmissible M L (er n a) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n a)
      (hclip n a) (hshares n a) (hm n a)
  obtain ⟨hrp, hrlev, hrpi, _, _, _, _, hrg, _⟩ :=
    continuous_component_rates_to_oracle_rates M μ L eh (trueNuisance M L) hr
  have hc : 0 < cpi / 2 := by linarith [hov.1]
  have hfit n a (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, cpi / 2 ≤ (er n a).piLev i x :=
    Eventually.of_forall (fun x => (hden n a).1 i x |>.1)
  have hboth n a (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, cpi / 2 ≤ (trueNuisance M L).piLev i x ∧
        cpi / 2 ≤ (er n a).piLev i x := by
    filter_upwards [hfit n a i] with x hx
    refine ⟨?_, hx⟩
    have h0 : cpi ≤ (trueNuisance M L).piLev i x :=
      hov.2 x i i.property.1 i.property.2
    linarith [hov.1]
  have hterminal n a : ∀ᵐ x ∂xLaw M,
      cpi / 2 ≤ positiveValue (er n a).piLev L.K x := by
    simpa only [positiveValue, dif_pos (show 1 ≤ L.K ∧ L.K ≤ L.K from ⟨hK, le_rfl⟩)]
      using hfit n a ⟨L.K, ⟨hK, le_rfl⟩⟩
  obtain ⟨B, Lip, hB, hLip, hb⟩ := hDerivative
  have hder : PolicyDerivativeBoundedLipschitz dphi := ⟨B, Lip, hB, hLip, hb⟩
  have hmean := nuisanceRates_continuous_tail_root_n_bias_negligible M μ h
    phi dphi hphi hd hder Lip hLip (fun z x a b ha hb' => (hb z x a b ha hb').2)
    L hK hOrder er her he0 cpi (cpi / 2) hov hc hterminal hrp hrlev hrpi hrg
  have hsq := nuisanceRates_continuous_commonTailScore_sq_tendsto_probability_zero M μ
    phi dphi hphi hd hder L (trueNuisance M L) er he0 her (cpi / 2) hc
    hboth hrp hrlev hrpi hrg
  exact ⟨hmean, hsq⟩

end Papers.TbsPrteOptimalTransport
