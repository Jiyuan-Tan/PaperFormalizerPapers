module
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousFrozenBandWeights
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousBandCoreAssembly
/-! Complete assembly of simultaneous continuous regular-band score derivatives. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: population_continuous_frozen_core_band_joint_derivative
/-- Assume [the structural model conditions](hyp:h), [known outcome endpoints](hyp:he),
[a valid policy map](hyp:hphi), [a policy derivative equal to the derivative of that map](hyp:hDiff),
and [a bounded Lipschitz policy derivative](hyp:hDerivative). If [baseline and policy
propensities have a covariate-invariant level ordering](hyp:hL), [policy levels avoid
band boundaries](hyp:hOff), [the propensity gaps satisfy the specified separation](hyp:hGap),
[baseline assignment overlap holds](hyp:hov), [policy overlap holds with the same
constant](hyp:hpol), [boundary densities are bounded](hyp:hden), and [there is no atom
at the lower outcome endpoint](hyp:h0), then, for [an admissible direction at the true
nuisances](hyp:hd), [a band index below the level's band count](hyp:hj),
[a measurable lower boundary](hyp:ha), and [a measurable upper boundary](hyp:hb),
[the band product score along the path varying only assignment denominators, pooled
denominators, and regular weights has population derivative zero at time zero and is
integrable throughout some neighborhood of zero](goal). -/
lemma population_continuous_frozen_core_band_joint_derivative
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
    let b := fun t => {trueNuisance M L with piLev := (e t).piLev, tauLev := (e t).tauLev, gamma := (e t).gamma}
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
      psiProd M phi dphi L (b t) k (j+1) o ∂observationLaw M) 0 0 ∧
    (∀ᶠ t : ℝ in 𝓝 0, Integrable (psiProd M phi dphi L (b t) k (j+1))
      (observationLaw M)) := by
  dsimp only
  have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  let e := fun t : ℝ => trueNuisance M L + t • del
  let b := fun t => {trueNuisance M L with piLev := (e t).piLev, tauLev := (e t).tauLev, gamma := (e t).gamma}
  let a : RegularIndex L := ⟨(k,j+1), k.isLt.le, by dsimp only; omega, by dsimp only; omega⟩
  have hdphi := policy_derivative_graph_measurable phi dphi hphi hDiff
    M.prop h.2.2.2.1.2.1 M.rangeProp
  obtain ⟨r, hr, hadm⟩ := hd.admissible
  have hm : ∀ᶠ t : ℝ in 𝓝 0,
      Integrable (psiProd M phi dphi L (b t) k (j+1)) (observationLaw M) ∧
      (∫ o : Obs X Z, psiProd M phi dphi L (b t) k (j+1) o ∂observationLaw M) =
        ∫ o : Obs X Z, gamma M L k (j+1) o.1 *
          contJ L (trueNuisance M L) k j o.1 ∂observationLaw M := by
    filter_upwards [continuous_assignment_path_uniform_lower_bound M L cpi hov del hd,
      continuous_pooled_path_uniform_lower_bound M (policyProp phi M.prop) L hL cpi hpol del hd,
      continuousAt_id.abs.eventually_lt_const (by simpa using hr)] with t hp htau ht
    have het := hadm t ht
    rcases het with ⟨_, _, _, _, _, hpim, _, htaum, _, _, _, _, hgb, hgm, _⟩
    have hg : Measurable (regularValue (e t).gamma k (j+1)) := by
      change Measurable (fun x => regularValue (e t).gamma k (j+1) x)
      simpa only [regularValue, dif_pos (show k.val ≤ L.K ∧ 1 ≤ j+1 ∧ j+1 ≤ L.l k from ⟨k.isLt.le, by omega, by omega⟩)] using hgm a
    have ig : Integrable (regularValue (e t).gamma k (j+1)) (xLaw M) := by
      apply Integrable.of_bound hg.aestronglyMeasurable 1
      filter_upwards [hgb a] with x hx
      simp only [regularValue, dif_pos (show k.val ≤ L.K ∧ 1 ≤ j+1 ∧ j+1 ≤ L.l k from ⟨k.isLt.le, by omega, by omega⟩)]
      change ‖(e t).gamma a x‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
      exact hx.2
    exact population_continuous_fitted_band_product_mean M h he phi dphi hdphi
      hDerivative L hL cpi hov hpol (e t).piLev hpim (e t).tauLev htaum
      (cpi/2) (div_pos hov.1 (by norm_num)) hp htau k j k.isLt hj ha hb
      hden h0 (e t).gamma hg ig
  refine ⟨?_, hm.mono fun _ ht => ht.1⟩
  exact (hasDerivAt_const (0 : ℝ) _).congr_of_eventuallyEq (hm.mono fun _ ht => ht.2)

-- @node: population_continuous_band_joint_orthogonality_of_admissible
/-- Under [the structural model conditions](hyp:h), [known outcome endpoints](hyp:he),
[a valid policy map](hyp:hphi), [the specified policy derivative](hyp:hDiff), and
[boundedness and Lipschitz continuity of that derivative](hyp:hDerivative), assume
[covariate-invariant ordering of baseline and policy propensity levels](hyp:hL),
[policy levels off band boundaries](hyp:hOff), [the specified propensity-gap separation](hyp:hGap),
[baseline overlap](hyp:hov), [policy overlap with the same constant](hyp:hpol),
[bounded boundary densities](hyp:hden), and [no atom at the lower outcome endpoint](hyp:h0).
For [an admissible nuisance direction at the truth](hyp:hd), [a valid band index](hyp:hj),
[a measurable lower boundary](hyp:ha), and [a measurable upper boundary](hyp:hb),
[the band product score along the full simultaneous affine nuisance path has population
derivative zero at time zero and is integrable throughout some neighborhood of zero](goal). -/
lemma population_continuous_band_joint_orthogonality_of_admissible
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
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
      psiProd M phi dphi L (trueNuisance M L + t • del) k (j+1) o
        ∂observationLaw M) 0 0 ∧
    (∀ᶠ t : ℝ in 𝓝 0, Integrable
      (psiProd M phi dphi L (trueNuisance M L + t • del) k (j+1))
        (observationLaw M)) := by
  let e := fun t : ℝ => trueNuisance M L + t • del
  let b := fun t => {trueNuisance M L with piLev := (e t).piLev, tauLev := (e t).tauLev, gamma := (e t).gamma}
  have hcore := population_continuous_band_core_joint_telescope M h he phi dphi
    hphi hDiff hDerivative L hL hOff gap hGap cpi hov hpol hden h0 del hd k j hj ha hb
  have hbase := population_continuous_frozen_core_band_joint_derivative M h he phi dphi
    hphi hDiff hDerivative L hL hOff gap hGap cpi hov hpol hden h0 del hd k j hj ha hb
  dsimp only at hcore hbase
  change HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
    psiProd M phi dphi L (e t) k (j+1) o - psiProd M phi dphi L (b t) k (j+1) o
      ∂observationLaw M) 0 0 ∧
    (∀ᶠ t : ℝ in 𝓝 0, Integrable (fun o : Obs X Z =>
      psiProd M phi dphi L (e t) k (j+1) o - psiProd M phi dphi L (b t) k (j+1) o)
        (observationLaw M)) at hcore
  have hi : ∀ᶠ t : ℝ in 𝓝 0,
      Integrable (psiProd M phi dphi L (e t) k (j+1)) (observationLaw M) ∧
      (∫ o : Obs X Z, psiProd M phi dphi L (e t) k (j+1) o ∂observationLaw M) =
        (∫ o : Obs X Z, psiProd M phi dphi L (e t) k (j+1) o -
          psiProd M phi dphi L (b t) k (j+1) o ∂observationLaw M) +
        ∫ o : Obs X Z, psiProd M phi dphi L (b t) k (j+1) o ∂observationLaw M := by
    filter_upwards [hcore.2, hbase.2] with t ht hc
    have hid : psiProd M phi dphi L (e t) k (j+1) = fun o : Obs X Z =>
        (psiProd M phi dphi L (e t) k (j+1) o - psiProd M phi dphi L (b t) k (j+1) o) +
        psiProd M phi dphi L (b t) k (j+1) o := by funext o; ring
    have ie : Integrable (psiProd M phi dphi L (e t) k (j+1)) (observationLaw M) := by
      rw [hid]
      exact ht.fun_add hc
    refine ⟨ie, ?_⟩
    rw [integral_sub ie hc]
    ring
  refine ⟨?_, hi.mono fun _ ht => ht.1⟩
  have hs := hcore.1.add hbase.1
  simp only [add_zero] at hs
  exact hs.congr_of_eventuallyEq (hi.mono fun _ ht => ht.2)

-- @node: population_continuous_regular_sum_joint_orthogonality_of_admissible
/-- Assume [the structural model conditions](hyp:h), [known outcome endpoints](hyp:he),
[a valid policy map](hyp:hphi), [the specified policy derivative](hyp:hDiff),
[a bounded Lipschitz policy derivative](hyp:hDerivative), [covariate-invariant ordering
of baseline and policy propensity levels](hyp:hL), [policy levels off band boundaries](hyp:hOff),
[the specified propensity-gap separation](hyp:hGap), [baseline overlap](hyp:hov),
[policy overlap with the same constant](hyp:hpol), [bounded boundary densities](hyp:hden),
and [no atom at the lower outcome endpoint](hyp:h0). For [an admissible nuisance direction
at the truth](hyp:hd), if [every boundary at every treatment level below the level count
is measurable](hyp:hb), then [the sum of all regular-band product scores along the full
affine nuisance path has population derivative zero at time zero and is integrable
throughout some neighborhood of zero](goal). -/
lemma population_continuous_regular_sum_joint_orthogonality_of_admissible
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
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
      ∑ k : Fin L.K, ∑ j ∈ Finset.range (L.l k),
        psiProd M phi dphi L (trueNuisance M L + t • del) k (j+1) o
          ∂observationLaw M) 0 0 ∧
    (∀ᶠ t : ℝ in 𝓝 0, Integrable (fun o : Obs X Z =>
      ∑ k : Fin L.K, ∑ j ∈ Finset.range (L.l k),
        psiProd M phi dphi L (trueNuisance M L + t • del) k (j+1) o)
          (observationLaw M)) := by
  let f := fun (t : ℝ) (k : Fin L.K) (j : ℕ) =>
    psiProd M phi dphi L (trueNuisance M L + t • del) k (j+1)
  have hcomp (k : Fin L.K) (j : ℕ) (hj : j ∈ Finset.range (L.l k)) :
      HasDerivAt (fun t : ℝ => ∫ o, f t k j o ∂observationLaw M) 0 0 ∧
      ∀ᶠ t : ℝ in 𝓝 0, Integrable (f t k j) (observationLaw M) := by
    have hj' := Finset.mem_range.mp hj
    exact population_continuous_band_joint_orthogonality_of_admissible M h he phi dphi
      hphi hDiff hDerivative L hL hOff gap hGap cpi hov hpol hden h0 del hd k j hj'
      (hb k j k.isLt hj'.le) (hb k (j+1) k.isLt (by omega))
  have hi : ∀ᶠ t : ℝ in 𝓝 0, ∀ k : Fin L.K, ∀ j ∈ Finset.range (L.l k),
      Integrable (f t k j) (observationLaw M) := by
    apply Filter.eventually_all.mpr
    intro k
    exact (Finset.eventually_all _).mpr (fun j hj => (hcomp k j hj).2)
  have hs : HasDerivAt (fun t : ℝ => ∑ k : Fin L.K,
      ∑ j ∈ Finset.range (L.l k), ∫ o, f t k j o ∂observationLaw M) 0 0 := by
    have hdk (k : Fin L.K) : HasDerivAt (fun t : ℝ =>
        ∑ j ∈ Finset.range (L.l k), ∫ o, f t k j o ∂observationLaw M) 0 0 := by
      simpa only [Finset.sum_const_zero] using
        HasDerivAt.fun_sum (fun j hj => (hcomp k j hj).1)
    simpa only [Finset.sum_const_zero] using
      HasDerivAt.fun_sum (fun k (_ : k ∈ Finset.univ) => hdk k)
  refine ⟨hs.congr_of_eventuallyEq ?_, ?_⟩
  · filter_upwards [hi] with t ht
    symm
    rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (ht k))]
    apply Finset.sum_congr rfl
    intro k _
    exact (integral_finsetSum _ (ht k)).symm
  · filter_upwards [hi] with t ht
    exact integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (ht k))

end Papers.TbsPrteOptimalTransport
