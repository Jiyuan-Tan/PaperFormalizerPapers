module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousPolicyResidual
/-! Gamma-weighted quantile policy corrections for the continuous DML score.
Bounded fitted weights preserve second moments, and their component rates
combine with the quantile-policy residual convergence. -/
public section

set_option linter.style.haveILetI false
set_option linter.style.openClassical false
set_option linter.unreachableTactic false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedTactic false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]

-- @node: fitted_continuous_quantile_policy_residual_abs_bound
/-- If [the derivative bound is nonnegative](hyp:hB), [the policy derivative has absolute value at most that bound for every instrument, covariate, and propensity between zero and one](hyp:hb), [the continuous nuisances are admissible](hyp:he), [the policy-denominator lower bound is positive](hyp:hc), and [all regular policy-level probabilities are at least that bound almost everywhere](hyp:hclip), then, at [a population level no larger than the terminal level](hyp:hk), [the absolute quantile-weighted policy residual is almost surely bounded by the sum of the absolute outcome endpoints times the number of instruments in the policy group times the derivative bound divided by the denominator lower bound](goal). -/
lemma fitted_continuous_quantile_policy_residual_abs_bound
    (M : LatentIVModel Ω X Z) (dphi : Z → X → ℝ → ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ z x p, p ∈ Icc (0 : ℝ) 1 → |dphi z x p| ≤ B)
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ r : RegularIndex L, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x)
    (k j : ℕ) (hk : k ≤ L.K) :
    ∀ᵐ o ∂observationLaw M, |nuValue M e k j o.1 * RqCont dphi L e k j o| ≤
      (|M.yMin| + |M.yMax|) * ((L.T k j).card * B / c) := by
  filter_upwards [observationLaw_covariate_ae M _
    (continuous_admissible_nuValue_abs_bound M L e he k j),
    fitted_RqCont_abs_bound M dphi B hB hb L e he c hc hclip k j hk]
    with o hn hq
  rw [abs_mul]
  exact mul_le_mul hn hq (abs_nonneg _) (by positivity)

-- @node: fitted_continuous_gamma_quantile_policy_residual_memLp
/-- Suppose [the policy is a valid policy map](hyp:hphi), [its specified derivative differentiates it](hyp:hd), [that derivative is bounded and Lipschitz](hyp:hDerivative), [the continuous nuisances are admissible](hyp:he), [the policy-denominator bound is positive](hyp:hc), and [regular policy-level probabilities are at least that bound almost everywhere](hyp:hclip). For [a population level no larger than the terminal level](hyp:hk), [gamma times the quantile-weighted policy residual is square integrable under the observation law](goal). -/
lemma fitted_continuous_gamma_quantile_policy_residual_memLp
    (M : LatentIVModel Ω X Z) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ r : RegularIndex L, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x)
    (g : RegularIndex L) (k j : ℕ) (hk : k ≤ L.K) :
    MemLp (fun o : Obs X Z => e.gamma g o.1 *
      (nuValue M e k j o.1 * RqCont dphi L e k j o)) 2 (observationLaw M) := by
  have hR := fitted_continuous_quantile_policy_residual_memLp M phi dphi hphi hd
    hDerivative L e he c hc hclip k j hk
  have hg : Measurable (e.gamma g) := by
    first | fun_prop | skip
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hm, _⟩
    exact hm g
  have hgb : ∀ᵐ x ∂xLaw M, |e.gamma g x| ≤ 1 := by
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hb, _⟩
    filter_upwards [hb g] with x hx
    simpa only [abs_of_nonneg hx.1] using hx.2
  apply hR.norm.mono' (by
    first | fun_prop | exact (hg.comp measurable_fst).aestronglyMeasurable.mul hR.1)
  filter_upwards [observationLaw_covariate_ae M _ hgb] with o ho
  rw [norm_mul, Real.norm_eq_abs (e.gamma g o.1)]
  exact (mul_le_mul_of_nonneg_right ho (norm_nonneg _)).trans_eq (one_mul _)

-- @node: encoded_continuous_gamma_quantile_policy_residual_sq_tendsto_probability_zero
/-- Assume [a valid policy map](hyp:hphi) with [the specified derivative](hyp:hd) that [is bounded and Lipschitz](hyp:hDerivative), [admissible true nuisances](hyp:he0), [clipped fitted nuisances](hyp:hclip), [nonnegative fitted shares summing to one](hyp:hshares), [measurable encoded fitted components](hyp:hm), and [componentwise L2 errors of smaller order in probability than the inverse fourth root of sample size](hyp:hr). With [policy overlap](hyp:hov), [overlap-based fitted denominator clipping](hyp:hden), and [a population level no larger than the terminal level](hyp:hk), [the observation-integrated squared error of gamma times the quantile-weighted policy residual converges in probability to zero along sample sizes twice one plus the index](goal). -/
lemma encoded_continuous_gamma_quantile_policy_residual_sq_tendsto_probability_zero
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
    (g : RegularIndex L) (k j : ℕ) (hk : k ≤ L.K) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o : Obs X Z,
        ((eh (2*(n+1)) t).gamma g o.1 *
            (nuValue M (eh (2*(n+1)) t) k j o.1 *
              RqCont dphi L (eh (2*(n+1)) t) k j o) -
          (trueNuisance M L).gamma g o.1 *
            (nuValue M (trueNuisance M L) k j o.1 *
              RqCont dphi L (trueNuisance M L) k j o))^2
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
    have hx := hov.2 x r.val.1 r.val.2 r.property.1 r.property.2.1 r.property.2.2 hne
    change cpi ≤ (trueNuisance M L).tauLev r x at hx
    linarith [hov.1]
  have hdh n t (r : RegularIndex L) : ∀ᵐ x ∂xLaw M,
      cpi/2 ≤ (er n t).tauLev r x :=
    Eventually.of_forall (fun x => ((hden n t).2 r x
      (contFittedSharesSimplex_policy_nonempty L _ (hshares n t) r)).1)
  let G := fun (e : NuisanceCont L) (o : Obs X Z) => e.gamma g o.1
  let R := fun (e : NuisanceCont L) (o : Obs X Z) =>
    nuValue M e k j o.1 * RqCont dphi L e k j o
  have hg (e : NuisanceCont L) (he : ContAdmissible M L e) (g : RegularIndex L) :
      Measurable (e.gamma g) ∧ (∀ᵐ x ∂xLaw M, |e.gamma g x| ≤ 1) := by
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hb, hm, _⟩
    refine ⟨?_, ?_⟩
    · first | fun_prop | exact hm g
    · filter_upwards [hb g] with x hx
      simpa only [abs_of_nonneg hx.1] using hx.2
  have hG (e : NuisanceCont L) (he : ContAdmissible M L e) :
      MemLp (G e) 2 (observationLaw M) := by
    haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
    apply MemLp.of_bound (by
      first | fun_prop | exact ((hg e he g).1.comp measurable_fst).aestronglyMeasurable) 1
    simpa only [G, Real.norm_eq_abs] using observationLaw_covariate_ae M _ (hg e he g).2
  have hR0 : MemLp (R (trueNuisance M L)) 2 (observationLaw M) :=
    fitted_continuous_quantile_policy_residual_memLp M phi dphi hphi hd hDerivative
      L _ he0 (cpi/2) hc hd0 k j hk
  have hRh n t : MemLp (R (er (2*(n+1)) t)) 2 (observationLaw M) :=
    fitted_continuous_quantile_policy_residual_memLp M phi dphi hphi hd hDerivative
      L _ (her _ t) (cpi/2) hc (hdh _ t) k j hk
  obtain ⟨_, _, _, _, _, _, hrg, _⟩ :=
    continuous_component_rates_to_oracle_rates M μ L eh (trueNuisance M L) hr
  have hrG := nuisanceRates_covariate_sq_tendsto_probability_zero M μ _ _
    (fun g => (hg _ he0 g).1) (fun n t g => (hg _ (her n t) g).1) hrg g
  obtain ⟨B, D, hB, hD, hb⟩ := hDerivative
  have hs := dml_ae_weighted_residual_sq_tendsto_probability_zero μ (observationLaw M)
    (G (trueNuisance M L)) (R (trueNuisance M L))
    (fun n t => G (er (2*(n+1)) t)) (fun n t => R (er (2*(n+1)) t))
    1 ((|M.yMin| + |M.yMax|) * ((L.T k j).card * B / (cpi/2)))
    (hG _ he0).1 hR0.1 (fun n t => (hG _ (her _ t)).1) (fun n t => (hRh n t).1)
    (fun n t => (hG _ (her _ t)).sub (hG _ he0)) (fun n t => (hRh n t).sub hR0)
    (fun n t => observationLaw_covariate_ae M _ (hg _ (her _ t) g).2)
    (fun _ _ => fitted_continuous_quantile_policy_residual_abs_bound M dphi B hB
      (fun z x p hp => (hb z x p p hp hp).1) L _ he0 (cpi/2) hc hd0 k j hk)
    hrG (by
      simpa only [R, er, restrictContShares, nuValue, RqCont] using
        encoded_continuous_quantile_policy_residual_sq_tendsto_probability_zero
          M μ phi dphi hphi hd ⟨B,D,hB,hD,hb⟩ L he0 eh hclip hshares hm hr
          cpi hov hden k j hk)
  simpa only [G, R, er, restrictContShares, nuValue, RqCont] using hs


-- @node: fitted_continuous_gamma_policy_block_memLp
/-- Given [a valid policy map](hyp:hphi), [its specified derivative](hyp:hd), [boundedness and Lipschitz continuity of that derivative](hyp:hDerivative), [admissible continuous nuisances](hyp:he), [a positive policy-denominator bound](hyp:hc), and [regular policy-level probabilities bounded below by it almost everywhere](hyp:hclip), [the sum over nonterminal levels and regular bands of gamma times the quantile-weighted policy residual is square integrable](goal), using either each band's upper boundary or its preceding boundary as selected. -/
lemma fitted_continuous_gamma_policy_block_memLp
    (M : LatentIVModel Ω X Z) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ r : RegularIndex L, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x)
    (upper : Bool) :
    MemLp (fun o : Obs X Z => ∑ k ∈ Finset.range L.K,
      ∑ j ∈ Finset.Icc 1 (L.l k), regularValue e.gamma k j o.1 *
        (nuValue M e k (if upper then j else j-1) o.1 *
          RqCont dphi L e k (if upper then j else j-1) o))
      2 (observationLaw M) := by
  apply memLp_finsetSum
  intro k hk
  apply memLp_finsetSum
  intro j hj
  have hg : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k :=
    ⟨(Finset.mem_range.mp hk).le, Finset.mem_Icc.mp hj⟩
  simpa only [regularValue, dif_pos hg] using
    fitted_continuous_gamma_quantile_policy_residual_memLp M phi dphi hphi hd
      hDerivative L e he c hc hclip ⟨(k,j), hg⟩ k
      (if upper then j else j-1) (Finset.mem_range.mp hk).le

-- @node: encoded_continuous_gamma_policy_block_sq_tendsto_probability_zero
/-- Suppose [the policy is a valid policy map](hyp:hphi), [its specified derivative differentiates it](hyp:hd), [the derivative is bounded and Lipschitz](hyp:hDerivative), [the true nuisances are admissible](hyp:he0), [fitted nuisances are clipped](hyp:hclip), [fitted shares are nonnegative and sum to one](hyp:hshares), [encoded fitted components are measurable](hyp:hm), and [componentwise L2 errors are of smaller order in probability than the inverse fourth root of sample size](hyp:hr). Under [policy overlap](hyp:hov) and [overlap-based fitted denominator clipping](hyp:hden), [the observation-integrated squared error of the gamma-weighted quantile-policy-residual block, evaluated at the selected upper or preceding band boundaries, converges in probability to zero along sample sizes twice one plus the index](goal). -/
lemma encoded_continuous_gamma_policy_block_sq_tendsto_probability_zero
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
    (upper : Bool) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o : Obs X Z,
        ((∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
          regularValue (eh (2*(n+1)) t).gamma k j o.1 *
            (nuValue M (eh (2*(n+1)) t) k (if upper then j else j-1) o.1 *
              RqCont dphi L (eh (2*(n+1)) t) k (if upper then j else j-1) o)) -
          ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
            regularValue (trueNuisance M L).gamma k j o.1 *
              (nuValue M (trueNuisance M L) k (if upper then j else j-1) o.1 *
                RqCont dphi L (trueNuisance M L) k (if upper then j else j-1) o))^2
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
  let F := fun (k j n : ℕ) (t : A) (o : Obs X Z) =>
    regularValue (er (2*(n+1)) t).gamma k j o.1 *
      (nuValue M (er (2*(n+1)) t) k (if upper then j else j-1) o.1 *
        RqCont dphi L (er (2*(n+1)) t) k (if upper then j else j-1) o) -
    regularValue (trueNuisance M L).gamma k j o.1 *
      (nuValue M (trueNuisance M L) k (if upper then j else j-1) o.1 *
        RqCont dphi L (trueNuisance M L) k (if upper then j else j-1) o)
  have hF k j n t (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
      MemLp (F k j n t) 2 (observationLaw M) := by
    have hg : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k := ⟨hk.le, hj⟩
    have hdh (r : RegularIndex L) : ∀ᵐ x ∂xLaw M,
        cpi/2 ≤ (er (2*(n+1)) t).tauLev r x :=
      Eventually.of_forall (fun x => ((hden (2*(n+1)) t).2 r x
        (contFittedSharesSimplex_policy_nonempty L (eh (2*(n+1)) t)
          (hshares (2*(n+1)) t) r)).1)
    convert
      (fitted_continuous_gamma_quantile_policy_residual_memLp M phi dphi hphi hd
        hDerivative L _ (her _ t) (cpi/2) hc hdh ⟨(k,j), hg⟩ k
        (if upper then j else j-1) hk.le).sub
      (fitted_continuous_gamma_quantile_policy_residual_memLp M phi dphi hphi hd
        hDerivative L _ he0 (cpi/2) hc hd0 ⟨(k,j), hg⟩ k
        (if upper then j else j-1) hk.le) using 1
    funext o
    simp only [F, regularValue, dif_pos hg, Pi.sub_apply]
  have hs := dml_finset_sum_sq_tendsto_probability_zero μ (observationLaw M)
    (Finset.range L.K) (fun k n t o => ∑ j ∈ Finset.Icc 1 (L.l k), F k j n t o)
    (fun k hk n t => memLp_finsetSum _
      (fun j hj => hF k j n t (Finset.mem_range.mp hk) (Finset.mem_Icc.mp hj))) (by
      intro k hk
      apply dml_finset_sum_sq_tendsto_probability_zero μ (observationLaw M)
        (Finset.Icc 1 (L.l k)) (F k)
        (fun j hj n t => hF k j n t (Finset.mem_range.mp hk) (Finset.mem_Icc.mp hj))
      intro j hj
      have hg : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k :=
        ⟨(Finset.mem_range.mp hk).le, Finset.mem_Icc.mp hj⟩
      simpa only [F, er, restrictContShares, regularValue, dif_pos hg, nuValue, RqCont] using
        encoded_continuous_gamma_quantile_policy_residual_sq_tendsto_probability_zero
          M μ phi dphi hphi hd hDerivative L he0 eh hclip hshares hm hr cpi hov
          hden ⟨(k,j), hg⟩ k (if upper then j else j-1) (Finset.mem_range.mp hk).le)
  simpa only [F, er, restrictContShares, regularValue, nuValue, RqCont,
    Finset.sum_sub_distrib] using hs

end Papers.TbsPrteOptimalTransport
