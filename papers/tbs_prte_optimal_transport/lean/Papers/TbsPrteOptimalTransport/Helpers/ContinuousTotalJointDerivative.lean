module
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousFullAdmissibleDerivative
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousBandFinalDerivative
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousTailPopulation
/-! Finite assembly of the continuous total score's simultaneous nuisance derivative. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false
set_option linter.style.longLine false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: population_continuous_total_joint_orthogonality_of_admissible
/-- Assume [the structural model conditions](hyp:h), [known outcome endpoints](hyp:he), [a valid policy map](hyp:hphi), [its differentiability with the specified derivative](hyp:hDiff), [a bounded Lipschitz policy derivative](hyp:hDerivative), [a positive number of levels](hyp:hK), [policy-invariant level ordering](hyp:hL), [policy levels away from the boundary](hyp:hOff), [separated baseline and policy propensities](hyp:hGap), [baseline overlap](hyp:hov), [policy overlap](hyp:hpol), [bounded boundary densities](hyp:hden), [no lower-endpoint atom](hyp:h0), and [measurable boundaries at all relevant bands](hyp:hb). For [an admissible simultaneous nuisance direction at the truth](hyp:hd), [the population mean of the total continuous score has derivative zero at zero along the affine nuisance path, and the score is integrable for every path parameter sufficiently close to zero](goal). -/
lemma population_continuous_total_joint_orthogonality_of_admissible
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hOff : PolicyLevelOffBoundary L) (gap : ℝ)
    (hGap : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hden : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L)
    (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (hb : ∀ k j, k < L.K → j ≤ L.l k → Measurable (bandBoundary M L k j)) :
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
      psiCont M phi dphi L hK o (trueNuisance M L + t • del)
        ∂observationLaw M) 0 0 ∧
    (∀ᶠ t : ℝ in 𝓝 0, Integrable (fun o : Obs X Z =>
      psiCont M phi dphi L hK o (trueNuisance M L + t • del))
        (observationLaw M)) := by
  let e := fun t : ℝ => trueNuisance M L + t • del
  let f := fun (t : ℝ) (k : ℕ) => psiFullProd L (e t) k
  let g := fun (t : ℝ) (k j : ℕ) => psiProd M phi dphi L (e t) k j
  let tail := fun t : ℝ => commonTailScore M phi dphi L
    (e t).prop (e t).pLev (e t).piLev (e t).gammaTail
  have hf (k : ℕ) (hk : k ∈ Finset.range L.K) :
      HasDerivAt (fun t : ℝ => ∫ o, f t k o ∂observationLaw M) 0 0 ∧
      ∀ᶠ t : ℝ in 𝓝 0, Integrable (f t k) (observationLaw M) :=
    population_continuous_full_joint_product_orthogonality_of_admissible M h he
      (policyProp phi M.prop) L hL cpi hov del hd ⟨k, Finset.mem_range.mp hk⟩
  have hg (k : ℕ) (hk : k ∈ Finset.range L.K) (j : ℕ)
      (hj : j ∈ Finset.Icc 1 (L.l k)) :
      HasDerivAt (fun t : ℝ => ∫ o, g t k j o ∂observationLaw M) 0 0 ∧
      ∀ᶠ t : ℝ in 𝓝 0, Integrable (g t k j) (observationLaw M) := by
    have hk' := Finset.mem_range.mp hk
    rcases Finset.mem_Icc.mp hj with ⟨hj1, hj2⟩
    have hj' : j-1 < L.l k := by omega
    have hh := population_continuous_band_joint_orthogonality_of_admissible M h he
      phi dphi hphi hDiff hDerivative L hL hOff gap hGap cpi hov hpol hden h0
      del hd ⟨k,hk'⟩ (j-1) hj' (hb k (j-1) hk' (by omega))
      (hb k (j-1+1) hk' (by omega))
    simpa only [Nat.sub_add_cancel hj1] using hh
  have ht := population_continuous_tail_joint_orthogonality_of_admissible M h.2.2.2.1
    phi dphi hphi hDiff hDerivative L hK hL cpi hov del hd
  have it := population_continuous_tail_joint_path_integrable_of_admissible M
    phi dphi hphi hDiff hDerivative L hK cpi hov del hd
  have hi : ∀ᶠ t : ℝ in 𝓝 0, ∀ k ∈ Finset.range L.K,
      Integrable (f t k) (observationLaw M) ∧
      ∀ j ∈ Finset.Icc 1 (L.l k), Integrable (g t k j) (observationLaw M) := by
    apply (Finset.eventually_all _).mpr
    intro k hk
    exact (hf k hk).2.and ((Finset.eventually_all _).mpr (fun j hj => (hg k hk j hj).2))
  have hs : HasDerivAt (fun t : ℝ => ∑ k ∈ Finset.range L.K,
      ((∫ o, f t k o ∂observationLaw M) +
        ∑ j ∈ Finset.Icc 1 (L.l k), ∫ o, g t k j o ∂observationLaw M)) 0 0 := by
    have hdK (k : ℕ) (hk : k ∈ Finset.range L.K) :=
      (hf k hk).1.add (HasDerivAt.fun_sum (fun j hj => (hg k hk j hj).1))
    simpa only [Finset.sum_const_zero, add_zero, Pi.add_apply] using HasDerivAt.fun_sum hdK
  have hm : ∀ᶠ t : ℝ in 𝓝 0,
      Integrable (fun o => psiCont M phi dphi L hK o (e t)) (observationLaw M) ∧
      (∫ o, psiCont M phi dphi L hK o (e t) ∂observationLaw M) =
        (∑ k ∈ Finset.range L.K, ((∫ o, f t k o ∂observationLaw M) +
          ∑ j ∈ Finset.Icc 1 (L.l k), ∫ o, g t k j o ∂observationLaw M)) +
        ∫ o, tail t o ∂observationLaw M := by
    filter_upwards [hi, it] with t ht hit
    have ik (k : ℕ) (hk : k ∈ Finset.range L.K) :=
      (ht k hk).1.fun_add (integrable_finsetSum _ (ht k hk).2)
    refine ⟨(integrable_finsetSum _ ik).fun_add hit, ?_⟩
    change (∫ o, (∑ k ∈ Finset.range L.K,
      (f t k o + ∑ j ∈ Finset.Icc 1 (L.l k), g t k j o)) + tail t o
        ∂observationLaw M) = _
    rw [integral_add (integrable_finsetSum _ ik) hit, integral_finsetSum _ ik]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [integral_add (ht k hk).1 (integrable_finsetSum _ (ht k hk).2),
      integral_finsetSum _ (ht k hk).2]
  refine ⟨?_, hm.mono fun _ h => h.1⟩
  have hdTotal := hs.add ht
  simp only [add_zero] at hdTotal
  exact hdTotal.congr_of_eventuallyEq (hm.mono fun _ h => h.2)

end Papers.TbsPrteOptimalTransport
