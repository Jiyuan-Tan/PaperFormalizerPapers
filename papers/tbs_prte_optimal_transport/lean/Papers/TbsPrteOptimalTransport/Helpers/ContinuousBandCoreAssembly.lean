module
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousBandPolicyRegressionAssembly
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousMovingPropensity
/-! Joint continuous regular-band cancellation through all core nuisance coordinates. -/
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

-- @node: population_continuous_band_quantile_propensity_telescope
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[a measurable policy preserving the unit interval](hyp:hphi), [policy
differentiability with the specified derivative](hyp:hDiff), [a bounded Lipschitz
policy derivative](hyp:hDerivative), [a level partition preserving baseline and
policy propensity order](hyp:hL), [policy levels off the boundaries](hyp:hOff),
[separation of propensities by the specified gap](hyp:hGap), [baseline overlap](hyp:hov),
[policy overlap at the same bound](hyp:hpol), [bounded boundary densities](hyp:hden),
and [no atom at the lower endpoint](hyp:h0), take [an admissible continuous
direction from truth](hyp:hd) and [a band within its level](hyp:hj) with [measurable
lower](hyp:ha) and [upper boundaries](hyp:hb). [The population product-score
difference has derivative zero at zero and is integrable near zero when comparing
the path with instrument propensities, policy shares, and band regressions fixed
at truth to the same path with baseline propensity levels and quantile thresholds
additionally fixed](goal). -/
lemma population_continuous_band_quantile_propensity_telescope
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hOff : PolicyLevelOffBoundary L) (gap : ℝ)
    (hGap : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hden : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L)
    (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (k : Fin L.K) (j : ℕ) (hj : j < L.l k)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j+1))) :
    let path := fun t : ℝ => trueNuisance M L + t • del
    let e := fun t => {path t with prop := (trueNuisance M L).prop, share := (trueNuisance M L).share, Jplus := (trueNuisance M L).Jplus, Jminus := (trueNuisance M L).Jminus, Mplus := (trueNuisance M L).Mplus, Mminus := (trueNuisance M L).Mminus}
    let b := fun t => {e t with pLev := (trueNuisance M L).pLev, nu := (trueNuisance M L).nu}
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
      psiProd M phi dphi L (e t) k (j+1) o - psiProd M phi dphi L (b t) k (j+1) o
        ∂observationLaw M) 0 0 ∧
    (∀ᶠ t : ℝ in 𝓝 0, Integrable (fun o : Obs X Z =>
      psiProd M phi dphi L (e t) k (j+1) o - psiProd M phi dphi L (b t) k (j+1) o)
        (observationLaw M)) := by
  dsimp only
  let path := fun t : ℝ => trueNuisance M L + t • del
  let e := fun t => {path t with prop := (trueNuisance M L).prop, share := (trueNuisance M L).share, Jplus := (trueNuisance M L).Jplus, Jminus := (trueNuisance M L).Jminus, Mplus := (trueNuisance M L).Mplus, Mminus := (trueNuisance M L).Mminus}
  let a := fun t => {e t with pLev := (trueNuisance M L).pLev}
  let b := fun t => {a t with nu := (trueNuisance M L).nu}
  let d : NuisanceCont L := {del with prop := 0, share := 0}
  have had := continuous_direction_freeze_policy_coordinates M L (trueNuisance M L) del hd
  have hpath (t : ℝ) : trueNuisance M L + t • d =
      {path t with prop := (trueNuisance M L).prop, share := (trueNuisance M L).share} := by
    dsimp only [d, path]
    change NuisanceCont.mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _
    congr 1 <;> ext <;> simp <;> change t * (0 : ℝ) = 0 <;> exact mul_zero t
  have hP := population_continuous_band_moving_quantile_propensity_product_derivative M
    phi dphi L cpi hov d had k j hj
  dsimp only at hP
  simp_rw [hpath] at hP
  have hdphi := policy_derivative_graph_measurable phi dphi hphi hDiff M.prop h.2.2.2.1.2.1 M.rangeProp
  have hQ := population_continuous_band_quantile_product_orthogonality M h he
    phi dphi hdphi hDerivative L hL hOff gap hGap cpi hov hpol hden h0 del hd
    k j k.isLt hj ha hb
  dsimp only at hQ
  change HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
      psiProd M phi dphi L (a t) k (j+1) o - psiProd M phi dphi L (b t) k (j+1) o
        ∂observationLaw M) 0 0 ∧
    (∀ᶠ t : ℝ in 𝓝 0, Integrable (fun o : Obs X Z =>
      psiProd M phi dphi L (a t) k (j+1) o - psiProd M phi dphi L (b t) k (j+1) o)
        (observationLaw M)) at hQ
  have hi : ∀ᶠ t : ℝ in 𝓝 0,
      Integrable (fun o : Obs X Z => psiProd M phi dphi L (e t) k (j+1) o -
        psiProd M phi dphi L (b t) k (j+1) o) (observationLaw M) ∧
      (∫ o : Obs X Z, psiProd M phi dphi L (e t) k (j+1) o -
        psiProd M phi dphi L (b t) k (j+1) o ∂observationLaw M) =
        (∫ o : Obs X Z, psiProd M phi dphi L (e t) k (j+1) o -
          psiProd M phi dphi L (a t) k (j+1) o ∂observationLaw M) +
        ∫ o : Obs X Z, psiProd M phi dphi L (a t) k (j+1) o -
          psiProd M phi dphi L (b t) k (j+1) o ∂observationLaw M := by
    filter_upwards [hP.2, hQ.2] with t htP htQ
    have hid : (fun o : Obs X Z => psiProd M phi dphi L (e t) k (j+1) o -
        psiProd M phi dphi L (b t) k (j+1) o) =
        (fun o => (psiProd M phi dphi L (e t) k (j+1) o -
          psiProd M phi dphi L (a t) k (j+1) o) +
          (psiProd M phi dphi L (a t) k (j+1) o -
          psiProd M phi dphi L (b t) k (j+1) o)) := by funext o; ring
    rw [hid]
    exact ⟨htP.add htQ, integral_add htP htQ⟩
  refine ⟨?_, hi.mono fun _ ht => ht.1⟩
  have hs := hP.1.add hQ.1
  simp only [add_zero] at hs
  exact hs.congr_of_eventuallyEq (hi.mono fun _ ht => ht.2)

-- @node: population_continuous_band_core_joint_telescope
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[a measurable policy preserving the unit interval](hyp:hphi), [policy
differentiability with the specified derivative](hyp:hDiff), [a bounded Lipschitz
policy derivative](hyp:hDerivative), [a level partition preserving baseline and
policy propensity order](hyp:hL), [policy levels off the boundaries](hyp:hOff),
[separation of propensities by the specified gap](hyp:hGap), [baseline overlap](hyp:hov),
[policy overlap at the same bound](hyp:hpol), [bounded boundary densities](hyp:hden),
and [no atom at the lower endpoint](hyp:h0), take [an admissible continuous
direction from truth](hyp:hd) and [a band within its level](hyp:hj) with [measurable
lower](hyp:ha) and [upper boundaries](hyp:hb). [The population product-score
difference between the full path and that path with instrument propensities,
policy shares, band outcome and distribution regressions, baseline propensity
levels, and quantile thresholds fixed at truth has derivative zero at zero;
the score difference is integrable for all sufficiently small path parameters](goal). -/
lemma population_continuous_band_core_joint_telescope
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hOff : PolicyLevelOffBoundary L) (gap : ℝ)
    (hGap : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hden : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L)
    (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (k : Fin L.K) (j : ℕ) (hj : j < L.l k)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j+1))) :
    let e := fun t : ℝ => trueNuisance M L + t • del
    let b := fun t => {e t with prop := (trueNuisance M L).prop, share := (trueNuisance M L).share, Jplus := (trueNuisance M L).Jplus, Jminus := (trueNuisance M L).Jminus, Mplus := (trueNuisance M L).Mplus, Mminus := (trueNuisance M L).Mminus, pLev := (trueNuisance M L).pLev, nu := (trueNuisance M L).nu}
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
      psiProd M phi dphi L (e t) k (j+1) o - psiProd M phi dphi L (b t) k (j+1) o
        ∂observationLaw M) 0 0 ∧
    (∀ᶠ t : ℝ in 𝓝 0, Integrable (fun o : Obs X Z =>
      psiProd M phi dphi L (e t) k (j+1) o - psiProd M phi dphi L (b t) k (j+1) o)
        (observationLaw M)) := by
  dsimp only
  let e := fun t : ℝ => trueNuisance M L + t • del
  let a := fun t => {e t with prop := (trueNuisance M L).prop, share := (trueNuisance M L).share, Jplus := (trueNuisance M L).Jplus, Jminus := (trueNuisance M L).Jminus, Mplus := (trueNuisance M L).Mplus, Mminus := (trueNuisance M L).Mminus}
  let b := fun t => {a t with pLev := (trueNuisance M L).pLev, nu := (trueNuisance M L).nu}
  have hP := population_continuous_band_policy_regression_telescope M h.2.2.2.1
    phi dphi hphi hDiff hDerivative L hL cpi hov hpol del hd k j hj
  have hQ := population_continuous_band_quantile_propensity_telescope M h he
    phi dphi hphi hDiff hDerivative L hL hOff gap hGap cpi hov hpol hden h0 del hd
    k j hj ha hb
  dsimp only at hP hQ
  have hi : ∀ᶠ t : ℝ in 𝓝 0,
      Integrable (fun o : Obs X Z => psiProd M phi dphi L (e t) k (j+1) o -
        psiProd M phi dphi L (b t) k (j+1) o) (observationLaw M) ∧
      (∫ o : Obs X Z, psiProd M phi dphi L (e t) k (j+1) o -
        psiProd M phi dphi L (b t) k (j+1) o ∂observationLaw M) =
        (∫ o : Obs X Z, psiProd M phi dphi L (e t) k (j+1) o -
          psiProd M phi dphi L (a t) k (j+1) o ∂observationLaw M) +
        ∫ o : Obs X Z, psiProd M phi dphi L (a t) k (j+1) o -
          psiProd M phi dphi L (b t) k (j+1) o ∂observationLaw M := by
    filter_upwards [hP.2, hQ.2] with t htP htQ
    have hid : (fun o : Obs X Z => psiProd M phi dphi L (e t) k (j+1) o -
        psiProd M phi dphi L (b t) k (j+1) o) =
        (fun o => (psiProd M phi dphi L (e t) k (j+1) o -
          psiProd M phi dphi L (a t) k (j+1) o) +
          (psiProd M phi dphi L (a t) k (j+1) o -
          psiProd M phi dphi L (b t) k (j+1) o)) := by funext o; ring
    rw [hid]
    exact ⟨htP.add htQ, integral_add htP htQ⟩
  refine ⟨?_, hi.mono fun _ ht => ht.1⟩
  have hs := hP.1.add hQ.1
  simp only [add_zero] at hs
  exact hs.congr_of_eventuallyEq (hi.mono fun _ ht => ht.2)


-- Finite assembly retains eventual integrability for the next proof step.
-- @node: population_continuous_regular_sum_core_joint_telescope
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[a measurable policy preserving the unit interval](hyp:hphi), [policy
differentiability with the specified derivative](hyp:hDiff), [a bounded Lipschitz
policy derivative](hyp:hDerivative), [a level partition preserving baseline and
policy propensity order](hyp:hL), [policy levels off the boundaries](hyp:hOff),
[separation of propensities by the specified gap](hyp:hGap), [baseline overlap](hyp:hov),
[policy overlap at the same bound](hyp:hpol), [bounded boundary densities](hyp:hden),
[no atom at the lower endpoint](hyp:h0), [an admissible continuous direction
from truth](hyp:hd), and [measurability of every band boundary](hyp:hb), [the
population sum of regular-band product-score differences has derivative zero
at zero and is integrable near zero when comparing the full path to that path
with instrument propensities, policy shares, band outcome and distribution
regressions, baseline propensity levels, and quantile thresholds fixed at truth](goal). -/
lemma population_continuous_regular_sum_core_joint_telescope
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hOff : PolicyLevelOffBoundary L) (gap : ℝ)
    (hGap : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hden : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L)
    (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (hb : ∀ k j, k < L.K → j ≤ L.l k → Measurable (bandBoundary M L k j)) :
    let e := fun t : ℝ => trueNuisance M L + t • del
    let b := fun t => {e t with
      prop := (trueNuisance M L).prop, share := (trueNuisance M L).share, Jplus := (trueNuisance M L).Jplus, Jminus := (trueNuisance M L).Jminus, Mplus := (trueNuisance M L).Mplus, Mminus := (trueNuisance M L).Mminus, pLev := (trueNuisance M L).pLev, nu := (trueNuisance M L).nu}
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
      ∑ k : Fin L.K, ∑ j ∈ Finset.range (L.l k),
        (psiProd M phi dphi L (e t) k (j+1) o -
          psiProd M phi dphi L (b t) k (j+1) o) ∂observationLaw M) 0 0 ∧
    (∀ᶠ t : ℝ in 𝓝 0, Integrable (fun o : Obs X Z =>
      ∑ k : Fin L.K, ∑ j ∈ Finset.range (L.l k),
        (psiProd M phi dphi L (e t) k (j+1) o -
          psiProd M phi dphi L (b t) k (j+1) o)) (observationLaw M)) := by
  dsimp only
  let e := fun t : ℝ => trueNuisance M L + t • del
  let b := fun t => {e t with
    prop := (trueNuisance M L).prop, share := (trueNuisance M L).share, Jplus := (trueNuisance M L).Jplus, Jminus := (trueNuisance M L).Jminus, Mplus := (trueNuisance M L).Mplus, Mminus := (trueNuisance M L).Mminus, pLev := (trueNuisance M L).pLev, nu := (trueNuisance M L).nu}
  let f := fun (t : ℝ) (k : Fin L.K) (j : ℕ) (o : Obs X Z) =>
    psiProd M phi dphi L (e t) k (j+1) o - psiProd M phi dphi L (b t) k (j+1) o
  have hcomp (k : Fin L.K) (j : ℕ) (hj : j ∈ Finset.range (L.l k)) :
      HasDerivAt (fun t : ℝ => ∫ o, f t k j o ∂observationLaw M) 0 0 ∧
      ∀ᶠ t : ℝ in 𝓝 0, Integrable (f t k j) (observationLaw M) := by
    have hj' := Finset.mem_range.mp hj
    exact population_continuous_band_core_joint_telescope M h he phi dphi hphi hDiff
      hDerivative L hL hOff gap hGap cpi hov hpol hden h0 del hd k j hj'
      (hb k j k.isLt hj'.le) (hb k (j+1) k.isLt (by omega))

  have hi : ∀ᶠ t : ℝ in 𝓝 0, ∀ k : Fin L.K, ∀ j ∈ Finset.range (L.l k),
      Integrable (f t k j) (observationLaw M) := by
    apply (Filter.eventually_all).mpr
    intro k
    exact (Finset.eventually_all _).mpr (fun j hj => (hcomp k j hj).2)
  have hdSum : HasDerivAt (fun t : ℝ => ∑ k : Fin L.K,
      ∑ j ∈ Finset.range (L.l k), ∫ o, f t k j o ∂observationLaw M) 0 0 := by
    have hdk (k : Fin L.K) : HasDerivAt (fun t : ℝ =>
        ∑ j ∈ Finset.range (L.l k), ∫ o, f t k j o ∂observationLaw M) 0 0 := by
      simpa only [Finset.sum_const_zero] using
        HasDerivAt.fun_sum (fun j hj => (hcomp k j hj).1)
    simpa only [Finset.sum_const_zero] using
      HasDerivAt.fun_sum (fun k (_ : k ∈ Finset.univ) => hdk k)
  refine ⟨hdSum.congr_of_eventuallyEq ?_, ?_⟩
  · filter_upwards [hi] with t ht
    symm
    rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (ht k))]
    apply Finset.sum_congr rfl
    intro k _
    exact (integral_finsetSum _ (ht k)).symm
  · filter_upwards [hi] with t ht
    exact integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (ht k))


end Papers.TbsPrteOptimalTransport
