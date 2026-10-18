module
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousBandRegressionAssembly
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousBandPolicyAssembly
/-! Joint regression and pooled-policy removal with moving continuous quantile boundaries. -/
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

-- @node: continuous_admissible_replace_policy_coordinates
/-- If [the first nuisance collection is admissible](hyp:he) and [the second is
admissible](hyp:hb), [replacing the first collection's instrument propensities and
pooling shares with those of the second preserves admissibility](goal). -/
lemma continuous_admissible_replace_policy_coordinates (L : LevelData Z X)
    (e b : NuisanceCont L) (he : ContAdmissible M L e) (hb : ContAdmissible M L b) :
    ContAdmissible M L {e with prop := b.prop, share := b.share} := by
  rcases he with ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, e31⟩
  rcases hb with ⟨b1, b2, _, _, _, _, _, _, b9, b10, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, b31⟩
  exact ⟨b1, b2, e3, e4, e5, e6, e7, e8, b9, b10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, b31⟩

-- @node: continuous_direction_freeze_policy_coordinates
/-- If [a nuisance direction is admissible at the reference collection](hyp:hd),
[setting its instrument-propensity and pooling-share directions to zero preserves
admissibility at the same reference collection](goal). -/
lemma continuous_direction_freeze_policy_coordinates (L : LevelData Z X)
    (eta del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl eta) (.inl del)) :
    IsAdmissibleDirection M L (.inl eta)
      (.inl {del with prop := 0, share := 0}) := by
  obtain ⟨r, hr, hp⟩ := hd.admissible
  have h0 : ContAdmissible M L eta := by
    have := hp 0 (by simpa using hr)
    rwa [continuous_nuisance_path_zero] at this
  refine ⟨r, hr, ?_⟩
  intro t ht
  have h := continuous_admissible_replace_policy_coordinates M L
    (eta + t • del) eta (hp t ht) h0
  have hid : eta + t • {del with prop := 0, share := 0} =
      {eta + t • del with prop := eta.prop, share := eta.share} := by
    change NuisanceCont.mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _
    congr 1 <;> ext <;> simp <;> change t * (0 : ℝ) = 0 <;> exact mul_zero t
  rwa [hid]

-- Policy removal precedes regression removal; the boundary path is retained.
-- @node: population_continuous_band_policy_regression_telescope
/-- Under [threshold crossing](hyp:h), [a valid policy map](hyp:hphi),
[policy differentiability](hyp:hDiff), [a bounded Lipschitz policy derivative](hyp:hDerivative),
[invariant baseline and policy level ordering](hyp:hL), [baseline overlap](hyp:hov),
[policy overlap](hyp:hpol), and [an admissible joint direction from truth](hyp:hd),
for [a band index below the level's band count](hyp:hj), [the product-score
difference from holding instrument propensities, pooling shares, and all band
outcome and indicator regressions at truth has expected derivative zero at zero
and is integrable for every sufficiently small perturbation](goal). -/
lemma population_continuous_band_policy_regression_telescope
    (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (k : Fin L.K) (j : ℕ) (hj : j < L.l k) :
    let e := fun t : ℝ => trueNuisance M L + t • del
    let b := fun t => {e t with prop := (trueNuisance M L).prop, share := (trueNuisance M L).share, Jplus := (trueNuisance M L).Jplus, Jminus := (trueNuisance M L).Jminus, Mplus := (trueNuisance M L).Mplus, Mminus := (trueNuisance M L).Mminus}
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
      psiProd M phi dphi L (e t) k (j+1) o - psiProd M phi dphi L (b t) k (j+1) o
        ∂observationLaw M) 0 0 ∧
    (∀ᶠ t : ℝ in 𝓝 0, Integrable (fun o : Obs X Z =>
      psiProd M phi dphi L (e t) k (j+1) o - psiProd M phi dphi L (b t) k (j+1) o)
        (observationLaw M)) := by
  dsimp only
  let e := fun t : ℝ => trueNuisance M L + t • del
  let a := fun t => {e t with prop := (trueNuisance M L).prop, share := (trueNuisance M L).share}
  let b := fun t => {a t with Jplus := (trueNuisance M L).Jplus, Jminus := (trueNuisance M L).Jminus, Mplus := (trueNuisance M L).Mplus, Mminus := (trueNuisance M L).Mminus}
  let d : NuisanceCont L := {del with prop := 0, share := 0}
  have had := continuous_direction_freeze_policy_coordinates M L (trueNuisance M L) del hd
  have hpath (t : ℝ) : trueNuisance M L + t • d = a t := by
    dsimp only [d, a, e]
    change NuisanceCont.mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _
    congr 1 <;> ext <;> simp <;> change t * (0 : ℝ) = 0 <;> exact mul_zero t
  have hP := population_continuous_band_policy_product_telescope M h
    phi dphi hphi hDiff hDerivative L hL cpi hpol del hd k j hj
  have hQ := population_continuous_band_regressions_joint_telescope_orthogonality M
    phi dphi L cpi hov d had k j hj
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

-- Finite assembly retains eventual integrability for the next proof step.
-- @node: population_continuous_regular_sum_policy_regression_telescope
/-- Under [threshold crossing](hyp:h), [a valid policy map](hyp:hphi),
[policy differentiability](hyp:hDiff), [a bounded Lipschitz policy derivative](hyp:hDerivative),
[invariant baseline and policy level ordering](hyp:hL), [baseline overlap](hyp:hov),
[policy overlap](hyp:hpol), and [an admissible joint direction from truth](hyp:hd),
[the sum over regular bands of product-score differences from holding instrument
propensities, pooling shares, and all band outcome and indicator regressions at
truth has expected derivative zero at zero and is integrable for every sufficiently
small perturbation](goal). -/
lemma population_continuous_regular_sum_policy_regression_telescope
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del)) :
    let e := fun t : ℝ => trueNuisance M L + t • del
    let b := fun t => {e t with
      prop := (trueNuisance M L).prop, share := (trueNuisance M L).share, Jplus := (trueNuisance M L).Jplus, Jminus := (trueNuisance M L).Jminus, Mplus := (trueNuisance M L).Mplus, Mminus := (trueNuisance M L).Mminus}
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
    prop := (trueNuisance M L).prop, share := (trueNuisance M L).share, Jplus := (trueNuisance M L).Jplus, Jminus := (trueNuisance M L).Jminus, Mplus := (trueNuisance M L).Mplus, Mminus := (trueNuisance M L).Mminus}
  let f := fun (t : ℝ) (k : Fin L.K) (j : ℕ) (o : Obs X Z) =>
    psiProd M phi dphi L (e t) k (j+1) o - psiProd M phi dphi L (b t) k (j+1) o
  have hcomp (k : Fin L.K) (j : ℕ) (hj : j ∈ Finset.range (L.l k)) :
      HasDerivAt (fun t : ℝ => ∫ o, f t k j o ∂observationLaw M) 0 0 ∧
      ∀ᶠ t : ℝ in 𝓝 0, Integrable (f t k j) (observationLaw M) := by
    have hj' := Finset.mem_range.mp hj
    exact population_continuous_band_policy_regression_telescope M h phi dphi hphi hDiff
      hDerivative L hL cpi hov hpol del hd k j hj'

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
