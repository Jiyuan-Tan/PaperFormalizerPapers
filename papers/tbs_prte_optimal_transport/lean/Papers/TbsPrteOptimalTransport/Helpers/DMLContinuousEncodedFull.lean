module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousComponentBridge
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousFullBiasAssembly
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousTreatmentResidual
/-! Continuous full-interval oracle conclusions from the encoded nuisance conditions.
The share restriction supplies admissibility without changing any full-interval
coordinate. Componentwise rates then control both the actual score bias and
the population squared score difference used by conditional Chebyshev. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]

-- @node: encoded_continuous_full_oracle_remainders
/-- Under [threshold crossing](hyp:h), [invariant ordering of baseline and counterfactual treatment levels](hyp:hOrder),
[the potential-outcome support restriction](hyp:hp), [consistency](hyp:hcons), [known outcome endpoints](hyp:hend),
[baseline assignment overlap with the specified constant](hyp:hov), and [admissibility of the true nuisance record](hyp:he0), suppose
[fitted records obey clipping bounds](hyp:hclip), [their shares form simplices on policy sets](hyp:hshares),
[their encoded coordinates are measurable](hyp:hm), [their denominators are clipped using the overlap constant](hyp:hden), and
[the encoded nuisance family satisfies the finite nuisance rates](hyp:hr).
Then [both the square-root-scaled population mean difference and the population squared difference between the fitted and true full-interval score sums converge in probability to zero, using fits at sample size twice a positive integer and scaling by the square root of that integer](goal). -/
lemma encoded_continuous_full_oracle_remainders (M : LatentIVModel Ω X Z)
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (h : ThresholdCrossing M) (q : Z → X → ℝ) (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop q L)
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
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
        ((∫ o, ∑ k : Fin L.K, psiFullProd L (eh (2*(n+1)) a) k o ∂observationLaw M) -
          (∫ o, ∑ k : Fin L.K, psiFullProd L (trueNuisance M L) k o ∂observationLaw M)))
      atTop (fun _ _ => 0) ∧
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o,
        ((∑ k ∈ Finset.range L.K, psiFullProd L (eh (2*(n+1)) a) k o) -
          ∑ k ∈ Finset.range L.K, psiFullProd L (trueNuisance M L) k o)^2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  classical
  let er := fun n a => restrictContShares L (eh n a)
  have her n a : ContAdmissible M L (er n a) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n a)
      (hclip n a) (hshares n a) (hm n a)
  obtain ⟨_, hrp, hrpi, _, _, hrg, _, _, _, _, _, _, _, hrplus, hrminus⟩ :=
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
  have hb := nuisanceRates_continuous_full_score_block_bias_root_n_negligible
    M μ h q L hOrder er he0 her hp hcons hend (cpi / 2) hc hfit
    hrpi hrp hrplus hrminus hrg
  have hs := nuisanceRates_continuous_full_score_block_sq_tendsto_probability_zero
    M μ L (trueNuisance M L) er he0 her hp hcons hend (cpi / 2) hc hboth
    hrp hrpi hrplus hrminus hrg
  have hmean := (true_continuous_full_block_mean M h q L hOrder he0
    hp hcons hend cpi hov).2
  rw [← hmean] at hb
  exact ⟨hb, hs⟩

end Papers.TbsPrteOptimalTransport
