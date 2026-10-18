module
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousBandOutcomeJoint
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousBandIndicatorJoint
/-! Joint removal of the continuous band outcome and indicator regressions. -/
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

-- The admissibility constraints on J are separate from the simplex constraint.
-- @node: continuous_admissible_replace_band_outcome_regressions
/-- If [the first nuisance collection is admissible](hyp:he) and [the second is
admissible](hyp:hb), [replacing the first collection's upper and lower band outcome
regressions with those of the second preserves admissibility](goal). -/
lemma continuous_admissible_replace_band_outcome_regressions (L : LevelData Z X)
    (e b : NuisanceCont L) (he : ContAdmissible M L e) (hb : ContAdmissible M L b) :
    ContAdmissible M L {e with Jplus := b.Jplus, Jminus := b.Jminus} := by
  rcases he with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
    _, _, _, _, h27, h28, h29, h30, h31⟩
  rcases hb with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, b23, b24, b25, b26, _, _, _, _, _⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
    b23, b24, b25, b26, h27, h28, h29, h30, h31⟩

-- Freezing the two band J coordinates is an admissible affine subpath.
-- @node: continuous_direction_freeze_band_outcome_regressions
/-- If [a joint nuisance direction is admissible at the reference collection](hyp:hd),
[setting its upper and lower band outcome-regression directions to zero preserves
admissibility at that same reference collection](goal). -/
lemma continuous_direction_freeze_band_outcome_regressions (L : LevelData Z X)
    (eta del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl eta) (.inl del)) :
    IsAdmissibleDirection M L (.inl eta)
      (.inl {del with Jplus := 0, Jminus := 0}) := by
  obtain ⟨r, hr, hp⟩ := hd.admissible
  have h0 : ContAdmissible M L eta := by
    have := hp 0 (by simpa using hr)
    rwa [continuous_nuisance_path_zero] at this
  refine ⟨r, hr, ?_⟩
  intro t ht
  have h := continuous_admissible_replace_band_outcome_regressions M L
    (eta + t • del) eta (hp t ht) h0
  have hid : eta + t • {del with Jplus := 0, Jminus := 0} =
      {eta + t • del with Jplus := eta.Jplus, Jminus := eta.Jminus} := by
    change NuisanceCont.mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _
    congr 1 <;> ext <;> simp <;> change t * (0 : ℝ) = 0 <;> exact mul_zero t
  rwa [hid]

-- Both conditional-mean groups cancel on the same joint path. The intermediate
-- path freezes J alone, so the M cancellation still retains moving p/nu/pi/gamma.
-- @node: population_continuous_band_regressions_joint_telescope_orthogonality
/-- Under [baseline overlap](hyp:hov) and [an admissible joint direction from
truth](hyp:hd), for [a band index below the level's band count](hyp:hj), [the expected
product-score difference between the full affine path and the path holding both
outcome and both indicator regressions at truth has derivative zero at zero, and
the difference is integrable for all sufficiently small perturbations](goal). -/
lemma population_continuous_band_regressions_joint_telescope_orthogonality
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (k : Fin L.K) (j : ℕ) (hj : j < L.l k) :
    let e := fun t : ℝ => trueNuisance M L + t • del
    let b := fun t => {e t with
      Jplus := (trueNuisance M L).Jplus, Jminus := (trueNuisance M L).Jminus,
      Mplus := (trueNuisance M L).Mplus, Mminus := (trueNuisance M L).Mminus}
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
      psiProd M phi dphi L (e t) k (j+1) o - psiProd M phi dphi L (b t) k (j+1) o
        ∂observationLaw M) 0 0 ∧
    (∀ᶠ t : ℝ in 𝓝 0, Integrable (fun o : Obs X Z =>
      psiProd M phi dphi L (e t) k (j+1) o - psiProd M phi dphi L (b t) k (j+1) o)
        (observationLaw M)) := by
  dsimp only
  let e := fun t : ℝ => trueNuisance M L + t • del
  let a := fun t => {e t with
    Jplus := (trueNuisance M L).Jplus, Jminus := (trueNuisance M L).Jminus}
  let b := fun t => {a t with
    Mplus := (trueNuisance M L).Mplus, Mminus := (trueNuisance M L).Mminus}
  let d : NuisanceCont L := {del with Jplus := 0, Jminus := 0}
  have had := continuous_direction_freeze_band_outcome_regressions M L _ del hd
  have hpath (t : ℝ) : trueNuisance M L + t • d = a t := by
    dsimp only [d, a, e]
    change NuisanceCont.mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _
    congr 1 <;> ext <;> simp <;> change t * (0 : ℝ) = 0 <;> exact mul_zero t
  have hJ := population_continuous_band_outcome_joint_telescope_orthogonality M
    phi dphi L cpi hov del hd k j hj
  have hM := population_continuous_band_indicator_joint_telescope_orthogonality M
    phi dphi L cpi hov d had k j hj
  dsimp only at hJ hM
  simp_rw [hpath] at hM
  have hi : ∀ᶠ t : ℝ in 𝓝 0,
      Integrable (fun o : Obs X Z => psiProd M phi dphi L (e t) k (j+1) o -
        psiProd M phi dphi L (b t) k (j+1) o) (observationLaw M) ∧
      (∫ o : Obs X Z, psiProd M phi dphi L (e t) k (j+1) o -
        psiProd M phi dphi L (b t) k (j+1) o ∂observationLaw M) =
        (∫ o : Obs X Z, psiProd M phi dphi L (e t) k (j+1) o -
          psiProd M phi dphi L (a t) k (j+1) o ∂observationLaw M) +
        ∫ o : Obs X Z, psiProd M phi dphi L (a t) k (j+1) o -
          psiProd M phi dphi L (b t) k (j+1) o ∂observationLaw M := by
    filter_upwards [hJ.2, hM.2] with t htJ htM
    have hid : (fun o : Obs X Z => psiProd M phi dphi L (e t) k (j+1) o -
        psiProd M phi dphi L (b t) k (j+1) o) =
        (fun o => (psiProd M phi dphi L (e t) k (j+1) o -
          psiProd M phi dphi L (a t) k (j+1) o) +
          (psiProd M phi dphi L (a t) k (j+1) o -
          psiProd M phi dphi L (b t) k (j+1) o)) := by funext o; ring
    rw [hid]
    exact ⟨htJ.add htM, integral_add htJ htM⟩
  refine ⟨?_, hi.mono fun _ ht => ht.1⟩
  have hs := hJ.1.add hM.1
  simp only [add_zero] at hs
  exact hs.congr_of_eventuallyEq (hi.mono fun _ ht => ht.2)

-- Finite assembly removes all band J/M regressions at once, leaving the
-- quantile, propensity, policy, denominator, and product-weight path intact.
-- @node: population_continuous_total_band_regressions_joint_telescope_orthogonality
/-- With [a positive number of levels](hyp:hK), [baseline overlap](hyp:hov), and
[an admissible joint direction from truth](hyp:hd), [the expected total-score
difference between the full affine path and the path holding all band outcome and
indicator regressions at truth has derivative zero at zero, and the difference is
integrable for every sufficiently small perturbation](goal). -/
lemma population_continuous_total_band_regressions_joint_telescope_orthogonality
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (hK : LevelCountPos L.K)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del)) :
    let e := fun t : ℝ => trueNuisance M L + t • del
    let b := fun t => {e t with
      Jplus := (trueNuisance M L).Jplus, Jminus := (trueNuisance M L).Jminus,
      Mplus := (trueNuisance M L).Mplus, Mminus := (trueNuisance M L).Mminus}
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
      psiCont M phi dphi L hK o (e t) - psiCont M phi dphi L hK o (b t)
        ∂observationLaw M) 0 0 ∧
    (∀ᶠ t : ℝ in 𝓝 0, Integrable (fun o : Obs X Z =>
      psiCont M phi dphi L hK o (e t) - psiCont M phi dphi L hK o (b t))
        (observationLaw M)) := by
  dsimp only
  let e := fun t : ℝ => trueNuisance M L + t • del
  let a := fun t => {e t with
    Jplus := (trueNuisance M L).Jplus, Jminus := (trueNuisance M L).Jminus}
  let b := fun t => {a t with
    Mplus := (trueNuisance M L).Mplus, Mminus := (trueNuisance M L).Mminus}
  let d : NuisanceCont L := {del with Jplus := 0, Jminus := 0}
  have had := continuous_direction_freeze_band_outcome_regressions M L _ del hd
  have hpath (t : ℝ) : trueNuisance M L + t • d = a t := by
    dsimp only [d, a, e]
    change NuisanceCont.mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _
    congr 1 <;> ext <;> simp <;> change t * (0 : ℝ) = 0 <;> exact mul_zero t
  have hJ := population_continuous_total_outcome_regression_telescope_orthogonality M
    phi dphi L hK cpi hov del hd
  have hM := population_continuous_total_indicator_regression_telescope_orthogonality M
    phi dphi L hK cpi hov d had
  dsimp only at hJ hM
  simp_rw [hpath] at hM
  have hi : ∀ᶠ t : ℝ in 𝓝 0,
      Integrable (fun o : Obs X Z => psiCont M phi dphi L hK o (e t) -
        psiCont M phi dphi L hK o (b t)) (observationLaw M) ∧
      (∫ o : Obs X Z, psiCont M phi dphi L hK o (e t) -
        psiCont M phi dphi L hK o (b t) ∂observationLaw M) =
        (∫ o : Obs X Z, psiCont M phi dphi L hK o (e t) -
          psiCont M phi dphi L hK o (a t) ∂observationLaw M) +
        ∫ o : Obs X Z, psiCont M phi dphi L hK o (a t) -
          psiCont M phi dphi L hK o (b t) ∂observationLaw M := by
    filter_upwards [hJ.2, hM.2] with t htJ htM
    have hid : (fun o : Obs X Z => psiCont M phi dphi L hK o (e t) -
        psiCont M phi dphi L hK o (b t)) =
        (fun o => (psiCont M phi dphi L hK o (e t) -
          psiCont M phi dphi L hK o (a t)) +
          (psiCont M phi dphi L hK o (a t) -
          psiCont M phi dphi L hK o (b t))) := by funext o; ring
    rw [hid]
    exact ⟨htJ.add htM, integral_add htJ htM⟩
  refine ⟨?_, hi.mono fun _ ht => ht.1⟩
  have hs := hJ.1.add hM.1
  simp only [add_zero] at hs
  exact hs.congr_of_eventuallyEq (hi.mono fun _ ht => ht.2)

end Papers.TbsPrteOptimalTransport
