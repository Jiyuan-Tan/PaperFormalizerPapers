module
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousBandRegressionAssembly
public import Papers.TbsPrteOptimalTransport.Helpers.QuantileTotalAssembly
/-! Joint cancellation of continuous band regressions and quantiles. -/
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

-- Selecting these coordinates preserves every range and simplex constraint.
-- @node: continuous_admissible_select_band_quantile_regressions
/-- If [the reference nuisance collection is admissible](hyp:he) and [the donor
collection is admissible](hyp:hb), [taking the donor's assignment and pooled
denominators, regular-band weights, band quantiles, and upper and lower outcome
and indicator regressions while retaining the reference's other coordinates
preserves admissibility](goal). -/
lemma continuous_admissible_select_band_quantile_regressions (L : LevelData Z X)
    (eta b : NuisanceCont L) (he : ContAdmissible M L eta) (hb : ContAdmissible M L b) :
    ContAdmissible M L {eta with piLev := b.piLev, tauLev := b.tauLev, gamma := b.gamma, nu := b.nu, Jplus := b.Jplus, Jminus := b.Jminus, Mplus := b.Mplus, Mminus := b.Mminus} := by
  rcases he with ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12,
    e13, e14, e15, e16, e17, e18, e19, e20, e21, e22,
    e23, e24, e25, e26, e27, e28, e29, e30, e31⟩
  rcases hb with ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12,
    b13, b14, b15, b16, b17, b18, b19, b20, b21, b22,
    b23, b24, b25, b26, b27, b28, b29, b30, b31⟩
  exact ⟨e1, e2, e3, e4, b5, b6, b7, b8, e9, e10, e11, e12,
    b13, b14, e15, e16, b17, b18, b19, b20, b21, b22,
    b23, b24, b25, b26, e27, e28, e29, e30, e31⟩

-- @node: continuous_direction_select_band_quantile_regressions
/-- If [a joint nuisance direction is admissible at the reference collection](hyp:hd),
[retaining only its assignment and pooled denominator, regular-band weight, band
quantile, and upper and lower band outcome- and indicator-regression directions,
with every other direction set to zero, preserves admissibility at that reference](goal). -/
lemma continuous_direction_select_band_quantile_regressions (L : LevelData Z X)
    (eta del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl eta) (.inl del)) :
    IsAdmissibleDirection M L (.inl eta)
      (.inl {del with prop := 0, pLev := 0, share := 0, higherPolicyFit := 0, higherBaselineFit := 0, gammaFull := 0, gammaTail := 0, JfullPlus := 0, JfullMinus := 0}) := by
  obtain ⟨r, hr, hp⟩ := hd.admissible
  have h0 : ContAdmissible M L eta := by
    have := hp 0 (by simpa using hr)
    rwa [continuous_nuisance_path_zero] at this
  refine ⟨r, hr, ?_⟩
  intro t ht
  have h := continuous_admissible_select_band_quantile_regressions M L eta
    (eta + t • del) h0 (hp t ht)
  have hid : eta + t • {del with prop := 0, pLev := 0, share := 0, higherPolicyFit := 0, higherBaselineFit := 0, gammaFull := 0, gammaTail := 0, JfullPlus := 0, JfullMinus := 0} =
      {eta with piLev := (eta + t • del).piLev, tauLev := (eta + t • del).tauLev, gamma := (eta + t • del).gamma, nu := (eta + t • del).nu, Jplus := (eta + t • del).Jplus, Jminus := (eta + t • del).Jminus, Mplus := (eta + t • del).Mplus, Mminus := (eta + t • del).Mminus} := by
    change NuisanceCont.mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _
    congr 1 <;> ext <;> simp <;> change t * (0 : ℝ) = 0 <;> exact mul_zero t
  rwa [hid]

-- Regression residual cancellation and the swept-boundary quadratic estimate
-- apply successively to one admissible path. Denominators and weights move jointly.
-- @node: population_continuous_total_band_quantile_regressions_joint_orthogonality
/-- Under [the structural model assumptions](hyp:h), [known outcome endpoints](hyp:he),
[measurability of the policy derivative evaluated at true propensities](hyp:hdphi),
[a bounded Lipschitz policy derivative](hyp:hDerivative), [a positive number of
levels](hyp:hK), [invariant baseline and policy level ordering](hyp:hL), [policy
levels away from band boundaries](hyp:hOff), [separation of baseline and policy
propensities by the specified gap](hyp:hGap), [baseline overlap](hyp:hov), [policy
overlap](hyp:hpol), [bounded boundary densities](hyp:hden), [no atom at the lower
endpoint](hyp:h0), [an admissible joint direction from truth](hyp:hd), and
[measurability of all band boundaries](hyp:hb), [jointly moving the band quantiles
and outcome and indicator regressions, while assignment denominators, pooled
denominators, and regular-band weights follow their affine paths and all other
nuisances stay at truth, produces a total-score difference from freezing those
quantiles and regressions whose expectation has derivative zero at zero and which
is integrable for every sufficiently small perturbation](goal). -/
lemma population_continuous_total_band_quantile_regressions_joint_orthogonality
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
    let b := fun t => {trueNuisance M L with
      piLev := (path t).piLev, tauLev := (path t).tauLev, gamma := (path t).gamma}
    let e := fun t => {b t with
      nu := (path t).nu,
      Jplus := (path t).Jplus, Jminus := (path t).Jminus,
      Mplus := (path t).Mplus, Mminus := (path t).Mminus}
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
      psiCont M phi dphi L hK o (e t) - psiCont M phi dphi L hK o (b t)
        ∂observationLaw M) 0 0 ∧
    (∀ᶠ t : ℝ in 𝓝 0, Integrable (fun o : Obs X Z =>
      psiCont M phi dphi L hK o (e t) - psiCont M phi dphi L hK o (b t))
        (observationLaw M)) := by
  dsimp only
  let path := fun t : ℝ => trueNuisance M L + t • del
  let b := fun t => {trueNuisance M L with
    piLev := (path t).piLev, tauLev := (path t).tauLev, gamma := (path t).gamma}
  let a := fun t => {b t with nu := (path t).nu}
  let e := fun t => {a t with
    Jplus := (path t).Jplus, Jminus := (path t).Jminus,
    Mplus := (path t).Mplus, Mminus := (path t).Mminus}
  let d : NuisanceCont L := {del with
    prop := 0, pLev := 0, share := 0,
    higherPolicyFit := 0, higherBaselineFit := 0, gammaFull := 0, gammaTail := 0,
    JfullPlus := 0, JfullMinus := 0}
  have had := continuous_direction_select_band_quantile_regressions M L
    (trueNuisance M L) del hd
  have hpath (t : ℝ) : trueNuisance M L + t • d = e t := by
    dsimp only [d, e, a, b, path]
    change NuisanceCont.mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _
    congr 1 <;> ext <;> simp <;> change t * (0 : ℝ) = 0 <;> exact mul_zero t
  have hR := population_continuous_total_band_regressions_joint_telescope_orthogonality M
    phi dphi L hK cpi hov d had
  dsimp only at hR
  simp_rw [hpath] at hR
  have hQ := population_continuous_total_quantile_telescope_orthogonality M h he
    phi dphi hdphi hDerivative L hK hL hOff gap hGap cpi hov hpol hden h0 del hd hb
  dsimp only at hQ
  have hi : ∀ᶠ t : ℝ in 𝓝 0,
      Integrable (fun o : Obs X Z => psiCont M phi dphi L hK o (e t) -
        psiCont M phi dphi L hK o (b t)) (observationLaw M) ∧
      (∫ o : Obs X Z, psiCont M phi dphi L hK o (e t) -
        psiCont M phi dphi L hK o (b t) ∂observationLaw M) =
        (∫ o : Obs X Z, psiCont M phi dphi L hK o (e t) -
          psiCont M phi dphi L hK o (a t) ∂observationLaw M) +
        ∫ o : Obs X Z, psiCont M phi dphi L hK o (a t) -
          psiCont M phi dphi L hK o (b t) ∂observationLaw M := by
    filter_upwards [hR.2, hQ.2] with t htR htQ
    have hid : (fun o : Obs X Z => psiCont M phi dphi L hK o (e t) -
        psiCont M phi dphi L hK o (b t)) =
        (fun o => (psiCont M phi dphi L hK o (e t) -
          psiCont M phi dphi L hK o (a t)) +
          (psiCont M phi dphi L hK o (a t) -
          psiCont M phi dphi L hK o (b t))) := by funext o; ring
    rw [hid]
    exact ⟨htR.add htQ, integral_add htR htQ⟩
  refine ⟨?_, hi.mono fun _ ht => ht.1⟩
  have hs := hR.1.add hQ.1
  simp only [add_zero] at hs
  exact hs.congr_of_eventuallyEq (hi.mono fun _ ht => ht.2)

-- Regression residual cancellation and the swept-boundary quadratic estimate
-- apply successively to one admissible path. Denominators and weights move jointly.
-- @node: population_continuous_band_quantile_regressions_joint_orthogonality
/-- Under [the structural model assumptions](hyp:h), [known outcome endpoints](hyp:he),
[measurability of the policy derivative evaluated at true propensities](hyp:hdphi),
[a bounded Lipschitz policy derivative](hyp:hDerivative), [invariant baseline and
policy level ordering](hyp:hL), [policy levels away from band boundaries](hyp:hOff),
[separation of baseline and policy propensities by the specified gap](hyp:hGap),
[baseline overlap](hyp:hov), [policy overlap](hyp:hpol), [bounded boundary densities](hyp:hden),
[no atom at the lower endpoint](hyp:h0), and [an admissible joint direction from
truth](hyp:hd), take [a band index below the level's band count](hyp:hj) with
[a measurable lower boundary](hyp:ha) and [a measurable upper boundary](hyp:hb).
[Jointly moving the band quantiles and outcome and indicator regressions, while
assignment denominators, pooled denominators, and regular-band weights follow
their affine paths and all other nuisances stay at truth, produces a product-score
difference from freezing those quantiles and regressions whose expectation has
derivative zero at zero and which is integrable for all sufficiently small perturbations](goal). -/
lemma population_continuous_band_quantile_regressions_joint_orthogonality
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
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
    let b := fun t => {trueNuisance M L with
      piLev := (path t).piLev, tauLev := (path t).tauLev, gamma := (path t).gamma}
    let e := fun t => {b t with
      nu := (path t).nu,
      Jplus := (path t).Jplus, Jminus := (path t).Jminus,
      Mplus := (path t).Mplus, Mminus := (path t).Mminus}
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
      psiProd M phi dphi L (e t) k (j+1) o - psiProd M phi dphi L (b t) k (j+1) o
        ∂observationLaw M) 0 0 ∧
    (∀ᶠ t : ℝ in 𝓝 0, Integrable (fun o : Obs X Z =>
      psiProd M phi dphi L (e t) k (j+1) o - psiProd M phi dphi L (b t) k (j+1) o)
        (observationLaw M)) := by
  dsimp only
  let path := fun t : ℝ => trueNuisance M L + t • del
  let b := fun t => {trueNuisance M L with
    piLev := (path t).piLev, tauLev := (path t).tauLev, gamma := (path t).gamma}
  let a := fun t => {b t with nu := (path t).nu}
  let e := fun t => {a t with
    Jplus := (path t).Jplus, Jminus := (path t).Jminus,
    Mplus := (path t).Mplus, Mminus := (path t).Mminus}
  let d : NuisanceCont L := {del with
    prop := 0, pLev := 0, share := 0,
    higherPolicyFit := 0, higherBaselineFit := 0, gammaFull := 0, gammaTail := 0,
    JfullPlus := 0, JfullMinus := 0}
  have had := continuous_direction_select_band_quantile_regressions M L
    (trueNuisance M L) del hd
  have hpath (t : ℝ) : trueNuisance M L + t • d = e t := by
    dsimp only [d, e, a, b, path]
    change NuisanceCont.mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _
    congr 1 <;> ext <;> simp <;> change t * (0 : ℝ) = 0 <;> exact mul_zero t
  have hR := population_continuous_band_regressions_joint_telescope_orthogonality M
    phi dphi L cpi hov d had k j hj
  dsimp only at hR
  simp_rw [hpath] at hR
  have hQ := population_continuous_band_quantile_product_orthogonality M h he
    phi dphi hdphi hDerivative L hL hOff gap hGap cpi hov hpol hden h0 del hd
    k j k.isLt hj ha hb
  dsimp only at hQ
  have hi : ∀ᶠ t : ℝ in 𝓝 0,
      Integrable (fun o : Obs X Z => psiProd M phi dphi L (e t) k (j+1) o -
        psiProd M phi dphi L (b t) k (j+1) o) (observationLaw M) ∧
      (∫ o : Obs X Z, psiProd M phi dphi L (e t) k (j+1) o -
        psiProd M phi dphi L (b t) k (j+1) o ∂observationLaw M) =
        (∫ o : Obs X Z, psiProd M phi dphi L (e t) k (j+1) o -
          psiProd M phi dphi L (a t) k (j+1) o ∂observationLaw M) +
        ∫ o : Obs X Z, psiProd M phi dphi L (a t) k (j+1) o -
          psiProd M phi dphi L (b t) k (j+1) o ∂observationLaw M := by
    filter_upwards [hR.2, hQ.2] with t htR htQ
    have hid : (fun o : Obs X Z => psiProd M phi dphi L (e t) k (j+1) o -
        psiProd M phi dphi L (b t) k (j+1) o) =
        (fun o => (psiProd M phi dphi L (e t) k (j+1) o -
          psiProd M phi dphi L (a t) k (j+1) o) +
          (psiProd M phi dphi L (a t) k (j+1) o -
          psiProd M phi dphi L (b t) k (j+1) o)) := by funext o; ring
    rw [hid]
    exact ⟨htR.add htQ, integral_add htR htQ⟩
  refine ⟨?_, hi.mono fun _ ht => ht.1⟩
  have hs := hR.1.add hQ.1
  simp only [add_zero] at hs
  exact hs.congr_of_eventuallyEq (hi.mono fun _ ht => ht.2)

end Papers.TbsPrteOptimalTransport
