module
public import Papers.TbsPrteOptimalTransport.Helpers.QuantileBandAssembly
/-! Finite assembly of quantile changes in the actual continuous total score. -/
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

-- Full intervals and the tail have no quantile dependence, so they cancel
-- before integration; no integrability of the two complete scores is needed.
-- @node: continuous_total_quantile_difference
/-- With [a positive number of propensity levels](hyp:hK), [replacing only the boundary quantiles in the continuous total score changes that score by exactly the sum of the changes in its band product scores](goal). -/
lemma continuous_total_quantile_difference
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (hK : LevelCountPos L.K)
    (eta : NuisanceCont L) (nu : BoundaryIndex L → X → ℝ) (o : Obs X Z) :
    psiCont M phi dphi L hK o {eta with nu := nu} - psiCont M phi dphi L hK o eta =
      ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
        (psiProd M phi dphi L {eta with nu := nu} k j o -
          psiProd M phi dphi L eta k j o) := by
  have hf : ∀ k, psiFullProd L {eta with nu := nu} k o = psiFullProd L eta k o :=
    fun _ => rfl
  simp only [psiCont, hf, add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib,
    add_sub_add_left_eq_sub]

-- @node: continuous_total_quantile_difference_integral
/-- With [a positive number of propensity levels](hyp:hK), if [every band product score change caused by replacing boundary quantiles is integrable under the observation law](hyp:hi), then [the resulting total score change is integrable and its expectation equals the sum of the band change expectations](goal). -/
lemma continuous_total_quantile_difference_integral
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (hK : LevelCountPos L.K)
    (eta : NuisanceCont L) (nu : BoundaryIndex L → X → ℝ)
    (hi : ∀ k ∈ Finset.range L.K, ∀ j ∈ Finset.Icc 1 (L.l k),
      Integrable (fun o : Obs X Z => psiProd M phi dphi L {eta with nu := nu} k j o -
        psiProd M phi dphi L eta k j o) (observationLaw M)) :
    Integrable (fun o => psiCont M phi dphi L hK o {eta with nu := nu} -
      psiCont M phi dphi L hK o eta) (observationLaw M) ∧
    (∫ o, psiCont M phi dphi L hK o {eta with nu := nu} -
      psiCont M phi dphi L hK o eta ∂observationLaw M) =
      ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
        ∫ o, psiProd M phi dphi L {eta with nu := nu} k j o -
          psiProd M phi dphi L eta k j o ∂observationLaw M := by
  simp_rw [continuous_total_quantile_difference]
  refine ⟨integrable_finsetSum _ (fun k hk => integrable_finsetSum _ (hi k hk)), ?_⟩
  rw [integral_finsetSum _ (fun k hk => integrable_finsetSum _ (hi k hk))]
  apply Finset.sum_congr rfl
  intro k hk
  exact integral_finsetSum _ (hi k hk)

-- Each band uses the conditional quantile equation, centered propensity and
-- policy residuals, and the quadratic swept-boundary estimate. Finiteness
-- permits one common neighborhood for integrability and derivative assembly.
-- @node: population_continuous_total_quantile_telescope_orthogonality
/-- Suppose [the model satisfies the structural assumptions](hyp:h), [the outcome endpoints are known](hyp:he), [the policy derivative evaluated at the baseline propensity is measurable](hyp:hdphi), and [the policy derivative is bounded and Lipschitz](hyp:hDerivative). With [a positive level count](hyp:hK), assume [the level ordering is invariant under the policy](hyp:hL), [policy levels stay off the boundary](hyp:hOff), [baseline and policy propensities satisfy the specified gap separation](hyp:hGap), [baseline overlap holds at the given constant](hyp:hov), [policy overlap holds at that constant](hyp:hpol), [boundary densities are bounded](hyp:hden), [there is no atom at the lower endpoint](hyp:h0), [the nuisance perturbation is admissible at the truth](hyp:hd), and [all band boundaries are measurable](hyp:hb). Then [the expected total score change from adding the quantile perturbation to the path that already perturbs the other nuisance components has derivative zero at zero, and the score change is integrable for all sufficiently small perturbations](goal). -/
lemma population_continuous_total_quantile_telescope_orthogonality
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
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
    let path := fun t : ℝ => trueNuisance M L + t • del
    let b := fun t => {trueNuisance M L with piLev := (path t).piLev, tauLev := (path t).tauLev, gamma := (path t).gamma}
    let e := fun t => {b t with nu := (path t).nu}
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
      psiCont M phi dphi L hK o (e t) - psiCont M phi dphi L hK o (b t)
        ∂observationLaw M) 0 0 ∧
    (∀ᶠ t : ℝ in 𝓝 0, Integrable (fun o : Obs X Z =>
      psiCont M phi dphi L hK o (e t) - psiCont M phi dphi L hK o (b t))
        (observationLaw M)) := by
  dsimp only
  let path := fun t : ℝ => trueNuisance M L + t • del
  let b := fun t => {trueNuisance M L with piLev := (path t).piLev, tauLev := (path t).tauLev, gamma := (path t).gamma}
  let e := fun t => {b t with nu := (path t).nu}
  have hband : ∀ k ∈ Finset.range L.K, ∀ j ∈ Finset.Icc 1 (L.l k),
      HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
        psiProd M phi dphi L (e t) k j o - psiProd M phi dphi L (b t) k j o
          ∂observationLaw M) 0 0 ∧
      (∀ᶠ t : ℝ in 𝓝 0, Integrable (fun o : Obs X Z =>
        psiProd M phi dphi L (e t) k j o - psiProd M phi dphi L (b t) k j o)
          (observationLaw M)) := by
    intro k hk j hj
    have hk' := Finset.mem_range.mp hk
    obtain ⟨hj1, hjl⟩ := Finset.mem_Icc.mp hj
    simpa only [Nat.sub_add_cancel hj1] using
      population_continuous_band_quantile_product_orthogonality M h he phi dphi
        hdphi hDerivative L hL hOff gap hGap cpi hov hpol hden h0 del hd
        k (j-1) hk' (by omega) (hb k (j-1) hk' (by omega)) (by simpa only [Nat.sub_add_cancel hj1] using hb k j hk' hjl)
  have hi : ∀ᶠ t : ℝ in 𝓝 0, ∀ k ∈ Finset.range L.K,
      ∀ j ∈ Finset.Icc 1 (L.l k), Integrable (fun o : Obs X Z =>
        psiProd M phi dphi L (e t) k j o - psiProd M phi dphi L (b t) k j o)
          (observationLaw M) := by
    apply (Finset.eventually_all _).mpr
    intro k hk
    apply (Finset.eventually_all _).mpr
    intro j hj
    exact (hband k hk j hj).2
  have hmean : ∀ᶠ t : ℝ in 𝓝 0,
      Integrable (fun o : Obs X Z => psiCont M phi dphi L hK o (e t) -
        psiCont M phi dphi L hK o (b t)) (observationLaw M) ∧
      (∫ o : Obs X Z, psiCont M phi dphi L hK o (e t) -
        psiCont M phi dphi L hK o (b t) ∂observationLaw M) =
        ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
          ∫ o : Obs X Z, psiProd M phi dphi L (e t) k j o -
            psiProd M phi dphi L (b t) k j o ∂observationLaw M := by
    filter_upwards [hi] with t ht
    exact continuous_total_quantile_difference_integral M phi dphi L hK
      (b t) (path t).nu ht
  have hsum : HasDerivAt (fun t : ℝ =>
      ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
        ∫ o : Obs X Z, psiProd M phi dphi L (e t) k j o -
          psiProd M phi dphi L (b t) k j o ∂observationLaw M) 0 0 := by
    have hk : ∀ k ∈ Finset.range L.K, HasDerivAt (fun t : ℝ =>
        ∑ j ∈ Finset.Icc 1 (L.l k), ∫ o : Obs X Z,
          psiProd M phi dphi L (e t) k j o - psiProd M phi dphi L (b t) k j o
            ∂observationLaw M) 0 0 := by
      intro k hk
      simpa only [Finset.sum_const_zero] using
        HasDerivAt.fun_sum (fun j hj => (hband k hk j hj).1)
    simpa only [Finset.sum_const_zero] using HasDerivAt.fun_sum hk
  exact ⟨hsum.congr_of_eventuallyEq (hmean.mono fun _ ht => ht.2),
    hmean.mono fun _ ht => ht.1⟩

end Papers.TbsPrteOptimalTransport
