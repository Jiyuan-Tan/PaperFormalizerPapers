module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousTailConvergence
public import Papers.TbsPrteOptimalTransport.Helpers.DMLActivePolicyConvergence
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousComponentBridge
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousRieszCoordinates
/-! Continuous pooled-policy residual moments and convergence.
The residual depends only on shared propensity and policy-mass coordinates.
Projecting these coordinates reuses the derivative and reciprocal bounds without
imposing any binary-outcome assumption on the continuous model. -/
public section

set_option linter.style.haveILetI false
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]

-- @node: RqCont_continuousTailCoordinates
/-- [The binary policy residual evaluated on the continuous nuisance tail coordinates
equals the continuous policy residual at the same observation and level indices](goal). -/
lemma RqCont_continuousTailCoordinates (dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e : NuisanceCont L) (k j : ℕ) (o : Obs X Z) :
    RqBin dphi L (continuousTailCoordinates L e) k j o = RqCont dphi L e k j o := rfl

-- @node: fitted_RqCont_memLp
/-- If [the policy map is valid](hyp:hphi), [its derivative is the specified function](hyp:hd),
[that derivative is bounded and Lipschitz](hyp:hDerivative), [the nuisances are
admissible](hyp:he), [the denominator floor is positive](hyp:hc), [every regular policy
mass exceeds that floor almost surely](hyp:hclip), and [the level index does not exceed
the number of levels](hyp:hk), [the fitted continuous policy residual is square
integrable under the observation law](goal). -/
lemma fitted_RqCont_memLp (M : LatentIVModel Ω X Z)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ r : RegularIndex L, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x)
    (k j : ℕ) (hk : k ≤ L.K) :
    MemLp (RqCont dphi L e k j) 2 (observationLaw M) := by
  exact fitted_RqBin_memLp M phi dphi hphi hd hDerivative L
    (continuousTailCoordinates L e) (continuousTailCoordinates_admissible M L e he)
    c hc hclip k j hk

-- @node: fitted_RqCont_abs_bound
/-- If [the derivative bound is nonnegative](hyp:hB), [the policy derivative is bounded
in absolute value by it on the unit interval](hyp:hb), [the nuisances are admissible](hyp:he),
[the denominator floor is positive](hyp:hc), [regular policy masses exceed that floor
almost surely](hyp:hclip), and [the level index does not exceed the number of levels](hyp:hk),
[the absolute fitted policy residual is almost surely at most the policy-set cardinality
times the derivative bound divided by the denominator floor](goal). -/
lemma fitted_RqCont_abs_bound (M : LatentIVModel Ω X Z)
    (dphi : Z → X → ℝ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ z x p, p ∈ Icc (0 : ℝ) 1 → |dphi z x p| ≤ B)
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ r : RegularIndex L, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x)
    (k j : ℕ) (hk : k ≤ L.K) :
    ∀ᵐ o ∂observationLaw M, |RqCont dphi L e k j o| ≤ (L.T k j).card * B / c := by
  exact fitted_RqBin_abs_bound M dphi B hB hb L
    (continuousTailCoordinates L e) (continuousTailCoordinates_admissible M L e he)
    c hc hclip k j hk

-- @node: nuisanceRates_RqCont_sq_tendsto_probability_zero
/-- Suppose [the policy map is valid](hyp:hphi), [the specified derivative differentiates
it](hyp:hd), [the derivative is bounded and Lipschitz](hyp:hDerivative), and [the reference
and all fitted nuisances are admissible](hyp:he0,heh). If [a positive denominator
floor](hyp:hc) [bounds both reference and fitted regular policy masses below almost
surely](hyp:hclip), [each propensity L² error is smaller in probability than the inverse
fourth root of sample size](hyp:hrp), [each policy-mass L² error has that rate](hyp:hrt),
and [the level index does not exceed the
number of levels](hyp:hk), [the integrated squared error of the fitted continuous policy
residual converges in probability to zero along sample sizes twice one plus the index](goal). -/
lemma nuisanceRates_RqCont_sq_tendsto_probability_zero (M : LatentIVModel Ω X Z)
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (r : RegularIndex L), ∀ᵐ x ∂xLaw M,
      c ≤ e0.tauLev r x ∧ c ≤ (eh n a).tauLev r x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrt : FiniteNuisanceRates M μ (fun n a => (eh n a).tauLev) e0.tauLev)
    (k j : ℕ) (hk : k ≤ L.K) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, (RqCont dphi L (eh (2*(n+1)) a) k j o -
        RqCont dphi L e0 k j o)^2 ∂observationLaw M) atTop (fun _ _ => 0) := by
  exact nuisanceRates_RqBin_sq_tendsto_probability_zero M μ phi dphi hphi hd hDerivative L
    (continuousTailCoordinates L e0) (fun n a => continuousTailCoordinates L (eh n a))
    (continuousTailCoordinates_admissible M L e0 he0)
    (fun n a => continuousTailCoordinates_admissible M L (eh n a) (heh n a))
    c hc hclip hrp hrt k j hk

-- A unit-mass share vector cannot be supported on an empty policy set.
-- @node: contFittedSharesSimplex_policy_nonempty
/-- If [fitted shares satisfy the simplex restrictions](hyp:hs), [the policy set at
each regular index is nonempty](goal). -/
lemma contFittedSharesSimplex_policy_nonempty (L : LevelData Z X)
    (e : NuisanceCont L) (hs : ContFittedSharesSimplex L e) (r : RegularIndex L) :
    (L.T r.val.1 r.val.2).Nonempty := by
  apply Finset.nonempty_iff_ne_empty.mpr
  intro hempty
  have hsum := (hs r (Classical.choice inferInstance)).2
  rw [hempty, Finset.sum_empty] at hsum
  exact zero_ne_one hsum

-- @node: encoded_continuous_RqCont_sq_tendsto_probability_zero
/-- Assume [a valid policy map](hyp:hphi) [with the specified derivative](hyp:hd),
[a bounded Lipschitz derivative](hyp:hDerivative), [admissible true nuisances](hyp:he0),
[clipped fitted nuisances](hyp:hclip), [fitted share simplexes](hyp:hshares),
[measurable fitted components](hyp:hm), [encoded componentwise L² errors toward truth
smaller in probability than the inverse fourth root of sample size](hyp:hr),
[policy overlap](hyp:hov), and [clipped fitted denominators](hyp:hden). If [the level
index does not exceed the number of levels](hyp:hk), [the integrated squared error of
the fitted continuous policy residual relative to truth converges in probability to
zero along sample sizes twice one plus the index](goal). -/
lemma encoded_continuous_RqCont_sq_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L)))
    (cpi : ℝ) (hov : PolicyOverlap M L cpi)
    (hden : ∀ n t, ContDenominatorsClipped L (eh n t) cpi)
    (k j : ℕ) (hk : k ≤ L.K) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o, (RqCont dphi L (eh (2*(n+1)) t) k j o -
        RqCont dphi L (trueNuisance M L) k j o)^2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  obtain ⟨hrp, _, _, hrt, _⟩ :=
    continuous_component_rates_to_oracle_rates M μ L eh (trueNuisance M L) hr
  have hc : 0 < cpi/2 := by linarith [hov.1]
  have hboth n t (r : RegularIndex L) : ∀ᵐ x ∂xLaw M,
      cpi/2 ≤ (trueNuisance M L).tauLev r x ∧ cpi/2 ≤ (er n t).tauLev r x := by
    have hne := contFittedSharesSimplex_policy_nonempty L (eh n t) (hshares n t) r
    apply Eventually.of_forall
    intro x
    have htrue : cpi ≤ (trueNuisance M L).tauLev r x :=
      hov.2 x r.val.1 r.val.2 r.property.1 r.property.2.1 r.property.2.2 hne
    exact ⟨by linarith [hov.1], ((hden n t).2 r x hne).1⟩
  simpa only [er, RqCont_restrictContShares] using
    nuisanceRates_RqCont_sq_tendsto_probability_zero M μ phi dphi hphi hd hDerivative L
      (trueNuisance M L) er he0 her (cpi/2) hc hboth hrp hrt k j hk

-- @node: continuous_admissible_policy_nonempty
/-- If [the continuous nuisances are admissible](hyp:he), [the policy set at every
regular index is nonempty](goal). -/
lemma continuous_admissible_policy_nonempty (M : LatentIVModel Ω X Z)
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e)
    (r : RegularIndex L) : (L.T r.val.1 r.val.2).Nonempty := by
  haveI : IsProbabilityMeasure (xLaw M) := Measure.isProbabilityMeasure_map M.measX.aemeasurable
  rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, hs⟩
  obtain ⟨x, hx⟩ := (hs r).exists
  apply Finset.nonempty_iff_ne_empty.mpr
  intro hempty
  rw [hempty, Finset.sum_empty] at hx
  exact zero_ne_one hx.1

-- @node: fitted_continuous_quantile_policy_residual_memLp
/-- If [the policy map is valid](hyp:hphi), [it has the specified derivative](hyp:hd),
[the derivative is bounded and Lipschitz](hyp:hDerivative), [the nuisances are admissible](hyp:he),
[the denominator floor is positive](hyp:hc), [regular policy masses exceed it almost
surely](hyp:hclip), and [the level index does not exceed the number of levels](hyp:hk),
[the fitted quantile times the continuous policy residual is square integrable under
the observation law](goal). -/
lemma fitted_continuous_quantile_policy_residual_memLp (M : LatentIVModel Ω X Z)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ r : RegularIndex L, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x)
    (k j : ℕ) (hk : k ≤ L.K) :
    MemLp (fun o : Obs X Z => nuValue M e k j o.1 * RqCont dphi L e k j o)
      2 (observationLaw M) := by
  have hq := fitted_RqCont_memLp M phi dphi hphi hd hDerivative L e he c hc hclip k j hk
  have hn : Measurable (fun o : Obs X Z => nuValue M e k j o.1) := by fun_prop
  apply (hq.norm.const_mul (|M.yMin| + |M.yMax|)).mono' (by
    first | fun_prop | exact hn.aestronglyMeasurable.mul hq.1)
  filter_upwards [observationLaw_covariate_ae M _
    (continuous_admissible_nuValue_abs_bound M L e he k j)] with o ho
  rw [norm_mul, Real.norm_eq_abs (nuValue M e k j o.1)]
  exact mul_le_mul_of_nonneg_right ho (norm_nonneg _)

-- Quantile estimation enters only as a bounded smooth weight here.
-- @node: encoded_continuous_quantile_policy_residual_sq_tendsto_probability_zero
/-- Assume [a valid policy map](hyp:hphi) [with the specified derivative](hyp:hd),
[a bounded Lipschitz derivative](hyp:hDerivative), [admissible true nuisances](hyp:he0),
[clipped fitted nuisances](hyp:hclip), [fitted share simplexes](hyp:hshares),
[measurable fitted components](hyp:hm), [encoded componentwise L² errors toward truth
smaller in probability than the inverse fourth root of sample size](hyp:hr),
[policy overlap](hyp:hov), and [clipped fitted denominators](hyp:hden). If [the level
index does not exceed the number of levels](hyp:hk), [the integrated squared error of
the fitted quantile-weighted policy residual relative to its true counterpart converges
in probability to zero along sample sizes twice one plus the index](goal). -/
lemma encoded_continuous_quantile_policy_residual_sq_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L)))
    (cpi : ℝ) (hov : PolicyOverlap M L cpi)
    (hden : ∀ n t, ContDenominatorsClipped L (eh n t) cpi)
    (k j : ℕ) (hk : k ≤ L.K) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o : Obs X Z,
        (nuValue M (eh (2*(n+1)) t) k j o.1 * RqCont dphi L (eh (2*(n+1)) t) k j o -
          nuValue M (trueNuisance M L) k j o.1 * RqCont dphi L (trueNuisance M L) k j o)^2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  have hc : 0 < cpi/2 := by linarith [hov.1]
  have hd0 (r : RegularIndex L) : ∀ᵐ x ∂xLaw M,
      cpi/2 ≤ (trueNuisance M L).tauLev r x := by
    have hne := continuous_admissible_policy_nonempty M L _ he0 r
    apply Eventually.of_forall
    intro x
    have hx : cpi ≤ (trueNuisance M L).tauLev r x :=
      hov.2 x r.val.1 r.val.2 r.property.1 r.property.2.1 r.property.2.2 hne
    linarith [hov.1]
  have hdh n t (r : RegularIndex L) : ∀ᵐ x ∂xLaw M,
      cpi/2 ≤ (er n t).tauLev r x :=
    Eventually.of_forall (fun x => ((hden n t).2 r x
      (contFittedSharesSimplex_policy_nonempty L _ (hshares n t) r)).1)
  let N := fun (e : NuisanceCont L) (o : Obs X Z) => nuValue M e k j o.1
  let Q := fun (e : NuisanceCont L) => RqCont dphi L e k j
  have hN (e : NuisanceCont L) (he : ContAdmissible M L e) :
      MemLp (N e) 2 (observationLaw M) := by
    haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
    apply MemLp.of_bound (by fun_prop) (|M.yMin| + |M.yMax|)
    simpa only [N, Real.norm_eq_abs] using observationLaw_covariate_ae M _
      (continuous_admissible_nuValue_abs_bound M L e he k j)
  have hQ0 : MemLp (Q (trueNuisance M L)) 2 (observationLaw M) :=
    fitted_RqCont_memLp M phi dphi hphi hd hDerivative L _ he0 (cpi/2) hc hd0 k j hk
  have hQh n t : MemLp (Q (er (2*(n+1)) t)) 2 (observationLaw M) :=
    fitted_RqCont_memLp M phi dphi hphi hd hDerivative L _ (her _ t)
      (cpi/2) hc (hdh _ t) k j hk
  obtain ⟨B, D, hB, hD, hb⟩ := hDerivative
  have hrN : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o, (N (er (2*(n+1)) t) o - N (trueNuisance M L) o)^2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
    let z0 : Z := Classical.choice inferInstance
    have hrate := nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hr (8,k,j,z0)
    have hi n t := observationLaw_covariate_integral M
      (fun x => (nuValue M (er (2*(n+1)) t) k j x - nuValue M (trueNuisance M L) k j x)^2)
      (by
        first | fun_prop | skip
        exact ((continuous_admissible_nuValue_measurable M L _ (her _ t) k j).sub
          (continuous_admissible_nuValue_measurable M L _ he0 k j)).pow_const 2)
    dsimp only [N]
    simp_rw [hi]
    simpa only [er, restrictContShares, contComponent, nuValue] using hrate
  have hs := dml_ae_weighted_residual_sq_tendsto_probability_zero μ (observationLaw M)
    (N (trueNuisance M L)) (Q (trueNuisance M L))
    (fun n t => N (er (2*(n+1)) t)) (fun n t => Q (er (2*(n+1)) t))
    (|M.yMin| + |M.yMax|) ((L.T k j).card * B / (cpi/2))
    (hN _ he0).1 hQ0.1 (fun n t => (hN _ (her _ t)).1) (fun n t => (hQh n t).1)
    (fun n t => (hN _ (her _ t)).sub (hN _ he0)) (fun n t => (hQh n t).sub hQ0)
    (fun n t => observationLaw_covariate_ae M _
      (continuous_admissible_nuValue_abs_bound M L _ (her _ t) k j))
    (fun _ _ => fitted_RqCont_abs_bound M dphi B hB
      (fun z x p hp => (hb z x p p hp hp).1) L _ he0 (cpi/2) hc hd0 k j hk)
    hrN (by
      simpa only [Q, er, RqCont_restrictContShares] using
        encoded_continuous_RqCont_sq_tendsto_probability_zero M μ phi dphi hphi hd
          ⟨B,D,hB,hD,hb⟩ L he0 eh hclip hshares hm hr cpi hov hden k j hk)
  simpa only [N, Q, er, restrictContShares, nuValue, RqCont] using hs

end Papers.TbsPrteOptimalTransport
