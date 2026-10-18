module
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousBandAdmissiblePropensity
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousBandPolicyAssembly
/-! Joint baseline-propensity and pooled-policy cancellation in continuous band scores. -/
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

-- These coordinates have separate range constraints; the share simplex is retained.
-- @node: continuous_admissible_replace_band_core
/-- If [the first nuisance collection is admissible](hyp:he) and [the second is
admissible](hyp:hb), [replacing the first collection's level propensities, band
quantiles, and upper and lower outcome and indicator regressions with those of
the second preserves admissibility](goal). -/
lemma continuous_admissible_replace_band_core (L : LevelData Z X)
    (e b : NuisanceCont L) (he : ContAdmissible M L e) (hb : ContAdmissible M L b) :
    ContAdmissible M L {e with pLev := b.pLev, nu := b.nu, Jplus := b.Jplus, Jminus := b.Jminus, Mplus := b.Mplus, Mminus := b.Mminus} := by
  rcases he with ⟨e1, e2, _, _, e5, e6, e7, e8, e9, e10, e11, e12,
    e13, e14, e15, e16, _, _, _, _, _, _, _, _, _, _, e27, e28, e29, e30, e31⟩
  rcases hb with ⟨_, _, b3, b4, _, _, _, _, _, _, _, _, _, _, _, _,
    b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, _, _, _, _, _⟩
  exact ⟨e1, e2, b3, b4, e5, e6, e7, e8, e9, e10, e11, e12,
    e13, e14, e15, e16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26,
    e27, e28, e29, e30, e31⟩

-- @node: continuous_direction_freeze_band_core
/-- If [a joint direction is admissible at the reference nuisance collection](hyp:hd),
[setting its level-propensity, band-quantile, and upper and lower outcome- and
indicator-regression directions to zero preserves admissibility at that reference](goal). -/
lemma continuous_direction_freeze_band_core (L : LevelData Z X)
    (eta del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl eta) (.inl del)) :
    IsAdmissibleDirection M L (.inl eta)
      (.inl {del with pLev := 0, nu := 0, Jplus := 0, Jminus := 0, Mplus := 0, Mminus := 0}) := by
  obtain ⟨r, hr, hp⟩ := hd.admissible
  have h0 : ContAdmissible M L eta := by
    have := hp 0 (by simpa using hr)
    rwa [continuous_nuisance_path_zero] at this
  refine ⟨r, hr, ?_⟩
  intro t ht
  have h := continuous_admissible_replace_band_core M L
    (eta + t • del) eta (hp t ht) h0
  have hid : eta + t • {del with pLev := 0, nu := 0, Jplus := 0, Jminus := 0, Mplus := 0, Mminus := 0} =
      {eta + t • del with pLev := eta.pLev, nu := eta.nu, Jplus := eta.Jplus, Jminus := eta.Jminus, Mplus := eta.Mplus, Mminus := eta.Mminus} := by
    change NuisanceCont.mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _
    congr 1 <;> ext <;> simp <;> change t * (0 : ℝ) = 0 <;> exact mul_zero t
  rwa [hid]

-- The first telescope removes pLev. On the resulting admissible subpath,
-- the second removes prop/share, with pi/tau/gamma still moving jointly.
-- @node: population_continuous_band_propensity_policy_telescope
/-- Under [the structural model assumptions](hyp:h), [known outcome endpoints](hyp:he),
[a valid policy map](hyp:hphi), [policy differentiability](hyp:hDiff), [a bounded
Lipschitz policy derivative](hyp:hDerivative), [invariant baseline and policy level
ordering](hyp:hL), [baseline overlap](hyp:hov), [policy overlap](hyp:hpol), and
[an admissible joint direction from truth](hyp:hd), consider [a band index below
the level's band count](hyp:hj) with [a measurable lower boundary](hyp:ha) and
[a measurable upper boundary](hyp:hb). [Along the affine path with band quantiles
and regressions held at truth, additionally freezing level propensities, instrument
propensities, and pooling shares produces a product-score difference with expected
derivative zero at zero that is integrable for all sufficiently small perturbations](goal). -/
lemma population_continuous_band_propensity_policy_telescope
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (k : Fin L.K) (j : ℕ) (hj : j < L.l k)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j+1))) :
    let e := fun t : ℝ => {trueNuisance M L + t • del with nu := (trueNuisance M L).nu, Jplus := (trueNuisance M L).Jplus, Jminus := (trueNuisance M L).Jminus, Mplus := (trueNuisance M L).Mplus, Mminus := (trueNuisance M L).Mminus}
    let b := fun t => {e t with pLev := (trueNuisance M L).pLev, prop := (trueNuisance M L).prop, share := (trueNuisance M L).share}
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
      psiProd M phi dphi L (e t) k (j+1) o - psiProd M phi dphi L (b t) k (j+1) o
        ∂observationLaw M) 0 0 ∧
    (∀ᶠ t : ℝ in 𝓝 0, Integrable (fun o : Obs X Z =>
      psiProd M phi dphi L (e t) k (j+1) o - psiProd M phi dphi L (b t) k (j+1) o)
        (observationLaw M)) := by
  dsimp only
  let e := fun t : ℝ => {trueNuisance M L + t • del with nu := (trueNuisance M L).nu, Jplus := (trueNuisance M L).Jplus, Jminus := (trueNuisance M L).Jminus, Mplus := (trueNuisance M L).Mplus, Mminus := (trueNuisance M L).Mminus}
  let a := fun t => {e t with pLev := (trueNuisance M L).pLev}
  let b := fun t => {a t with prop := (trueNuisance M L).prop, share := (trueNuisance M L).share}
  let d : NuisanceCont L := {del with pLev := 0, nu := 0, Jplus := 0, Jminus := 0, Mplus := 0, Mminus := 0}
  have had := continuous_direction_freeze_band_core M L (trueNuisance M L) del hd
  have hpath (t : ℝ) : trueNuisance M L + t • d = a t := by
    dsimp only [d, a, e]
    change NuisanceCont.mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _
    congr 1 <;> ext <;> simp <;> change t * (0 : ℝ) = 0 <;> exact mul_zero t
  have hP := population_continuous_band_admissible_propensity_product_derivative M h he
    phi dphi L hL cpi hov del hd k j hj ha hb
  have hQ := population_continuous_band_policy_product_telescope M h.2.2.2.1
    phi dphi hphi hDiff hDerivative L hL cpi hpol d had k j hj
  dsimp only at hP hQ
  simp_rw [hpath] at hQ
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

-- The finite sum retains both the derivative and the integrability needed by
-- the next telescope in the total continuous score.
-- @node: population_continuous_regular_sum_propensity_policy_telescope
/-- Under [the structural model assumptions](hyp:h), [known outcome endpoints](hyp:he),
[a valid policy map](hyp:hphi), [policy differentiability](hyp:hDiff), [a bounded
Lipschitz policy derivative](hyp:hDerivative), [invariant baseline and policy level
ordering](hyp:hL), [baseline overlap](hyp:hov), [policy overlap](hyp:hpol),
[an admissible joint direction from truth](hyp:hd), and [measurability of all band
boundaries](hyp:hb), [the sum of regular-band product-score differences from
freezing level propensities, instrument propensities, and pooling shares, along
the path already holding band quantiles and regressions at truth, has expected
derivative zero at zero and is integrable for all sufficiently small perturbations](goal). -/
lemma population_continuous_regular_sum_propensity_policy_telescope
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (hb : ∀ k j, k < L.K → j ≤ L.l k → Measurable (bandBoundary M L k j)) :
    let e := fun t : ℝ => {trueNuisance M L + t • del with nu := (trueNuisance M L).nu, Jplus := (trueNuisance M L).Jplus, Jminus := (trueNuisance M L).Jminus, Mplus := (trueNuisance M L).Mplus, Mminus := (trueNuisance M L).Mminus}
    let b := fun t => {e t with
      prop := (trueNuisance M L).prop, share := (trueNuisance M L).share, pLev := (trueNuisance M L).pLev}
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
      ∑ k : Fin L.K, ∑ j ∈ Finset.range (L.l k),
        (psiProd M phi dphi L (e t) k (j+1) o -
          psiProd M phi dphi L (b t) k (j+1) o) ∂observationLaw M) 0 0 ∧
    (∀ᶠ t : ℝ in 𝓝 0, Integrable (fun o : Obs X Z =>
      ∑ k : Fin L.K, ∑ j ∈ Finset.range (L.l k),
        (psiProd M phi dphi L (e t) k (j+1) o -
          psiProd M phi dphi L (b t) k (j+1) o)) (observationLaw M)) := by
  dsimp only
  let e := fun t : ℝ => {trueNuisance M L + t • del with nu := (trueNuisance M L).nu, Jplus := (trueNuisance M L).Jplus, Jminus := (trueNuisance M L).Jminus, Mplus := (trueNuisance M L).Mplus, Mminus := (trueNuisance M L).Mminus}
  let b := fun t => {e t with
    prop := (trueNuisance M L).prop, share := (trueNuisance M L).share, pLev := (trueNuisance M L).pLev}
  let f := fun (t : ℝ) (k : Fin L.K) (j : ℕ) (o : Obs X Z) =>
    psiProd M phi dphi L (e t) k (j+1) o - psiProd M phi dphi L (b t) k (j+1) o
  have hcomp (k : Fin L.K) (j : ℕ) (hj : j ∈ Finset.range (L.l k)) :
      HasDerivAt (fun t : ℝ => ∫ o, f t k j o ∂observationLaw M) 0 0 ∧
      ∀ᶠ t : ℝ in 𝓝 0, Integrable (f t k j) (observationLaw M) := by
    have hj' := Finset.mem_range.mp hj
    exact population_continuous_band_propensity_policy_telescope M h he phi dphi hphi hDiff
      hDerivative L hL cpi hov hpol del hd k j hj'
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
