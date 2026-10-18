module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLGammaIndicatorContrast
public import Papers.TbsPrteOptimalTransport.Helpers.DMLFractionalResidualConvergence
public import Papers.TbsPrteOptimalTransport.Helpers.DMLObservedResidualConvergence
/-! Quantile-weighted boundary residual convergence for the continuous DML score.
Clipping controls the multiplier and overlap controls the population residual;
the two fitted errors are combined using the bounded-product energy bound. -/
public section
set_option linter.unreachableTactic false
set_option linter.unusedFintypeInType false
set_option linter.unusedTactic false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: fitted_continuous_gamma_IFM_abs_bound
/-- If [the continuous nuisance functions are admissible](hyp:he), [the denominator bound is positive](hyp:hc), and [every positive-level baseline probability is almost surely at least that bound](hyp:hden), then, for [a level below the number of levels](hyp:hk), [the absolute gamma-weighted boundary-indicator residual on either chosen side is almost surely at most two divided by the denominator bound](goal). -/
lemma fitted_continuous_gamma_IFM_abs_bound [Fintype Z]
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (c : ℝ) (hc : 0 < c)
    (hden : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (g : RegularIndex L) (plus : Bool) (k j : ℕ) (hk : k < L.K) :
    ∀ᵐ o ∂observationLaw M, |e.gamma g o.1 * IFM M L e plus k j o| ≤ 2 / c := by
  have hgb : ∀ᵐ x ∂xLaw M, |e.gamma g x| ≤ 1 := by
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hb, _⟩
    filter_upwards [hb g] with x hx
    simpa only [abs_of_nonneg hx.1] using hx.2
  have hJ : (∀ᵐ x ∂xLaw M, |boundaryValue e.Mplus k j x| ≤ 1) ∧
      (∀ᵐ x ∂xLaw M, |minusBoundaryValue e.Mminus k j x| ≤ 1) := by
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hp, _, hn, _⟩
    constructor
    · unfold boundaryValue
      split_ifs with hj hlast
      · filter_upwards [hp ⟨(k,j), hj⟩] with x hx
        simpa only [abs_of_nonneg hx.1] using hx.2
      · exact Eventually.of_forall (by simp)
      · exact Eventually.of_forall (by simp)
    · unfold minusBoundaryValue
      split_ifs with hj hlast
      · filter_upwards [hn ⟨(k,j), hj⟩] with x hx
        simpa only [abs_of_nonneg hx.1] using hx.2
      · exact Eventually.of_forall (by simp)
      · exact Eventually.of_forall (by simp)
  have hside (i : PositiveIndex L.K) (J : X → ℝ)
      (hb : ∀ᵐ x ∂xLaw M, |J x| ≤ 1) :
      ∀ᵐ o ∂observationLaw M, |e.gamma g o.1 *
        (indicator (o.2.1 ∈ L.S i.val) * o.2.2.1 / e.piLev i o.1 *
          (indicator (o.2.2.2 ≤ nuValue M e k j o.1) - J o.1))| ≤ 2 / c := by
    filter_upwards [observationLaw_covariate_ae M _ hgb,
      observationLaw_covariate_ae M _ hb,
      observationLaw_covariate_ae M _ (hden i), observationLaw_treatment_range M]
      with o hg hJ hd hW
    have hs : |indicator (o.2.1 ∈ L.S i.val)| ≤ 1 := by
      unfold indicator; split_ifs <;> norm_num
    have hy : |indicator (o.2.2.2 ≤ nuValue M e k j o.1)| ≤ 1 := by
      unfold indicator; split_ifs <;> norm_num
    have hw : |o.2.2.1| ≤ 1 := by rw [abs_of_nonneg hW.1]; exact hW.2
    have hp0 : 0 < e.piLev i o.1 := hc.trans_le hd
    have herr : |indicator (o.2.2.2 ≤ nuValue M e k j o.1) - J o.1| ≤ 2 :=
      (abs_sub _ _).trans (by linarith)
    rw [abs_mul, abs_mul, abs_div, abs_mul, abs_of_pos (hc.trans_le hd)]
    calc
      _ ≤ 1 * ((1 * 1) / e.piLev i o.1 * 2) := by
        gcongr <;> first | fun_prop | assumption | positivity
      _ = 2 / e.piLev i o.1 := by ring
      _ ≤ 2 / c := div_le_div_of_nonneg_left (by norm_num) hc hd
  cases plus with
  | true =>
    have hi : 1 ≤ k+1 ∧ k+1 ≤ L.K := by omega
    simpa only [IFM, Bool.not_true, Bool.false_eq_true, false_and, if_false, if_true,
      positiveValue, dif_pos hi] using hside ⟨k+1, hi⟩ _ hJ.1
  | false =>
    by_cases hk0 : k = 0
    · subst k
      simp only [IFM, Bool.not_false, and_self, if_true, mul_zero, abs_zero]
      exact Eventually.of_forall (fun _ => by positivity)
    · have hi : 1 ≤ k ∧ k ≤ L.K := by omega
      simpa only [IFM, Bool.not_false, true_and, hk0, if_false,
        Bool.false_eq_true, positiveValue, dif_pos hi] using hside ⟨k, hi⟩ _ hJ.2

-- @node: encoded_continuous_nuValue_sq_tendsto_probability_zero
/-- If [the true continuous nuisances are admissible](hyp:he0), [every encoded fitted nuisance component is measurable](hyp:hm), and [the fitted finite-component errors satisfy the nuisance convergence rates](hyp:hr), then [the population mean squared error of the boundary quantile at any level and boundary indices, evaluated at even sample sizes, converges in probability to zero](goal). -/
lemma encoded_continuous_nuValue_sq_tendsto_probability_zero [Fintype Z]
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L))) (k j : ℕ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o : Obs X Z,
        (nuValue M (eh (2*(n+1)) t) k j o.1 -
          nuValue M (trueNuisance M L) k j o.1)^2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  let z0 : Z := Classical.choice inferInstance
  have hs := nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hr (8,k,j,z0)
  have hmnu n t : Measurable (nuValue M (eh n t) k j) := by
    change Measurable (fun x => nuValue M (eh n t) k j x)
    exact hm n t (8,k,j,z0)
  have hm0 := continuous_admissible_nuValue_measurable M L _ he0 k j
  have hms n t : Measurable (fun x =>
      (nuValue M (eh (2*(n+1)) t) k j x -
        nuValue M (trueNuisance M L) k j x)^2) := by
    fun_prop
  simp only [contComponent] at hs
  simpa only [observationLaw_covariate_integral M _ (hms _ _)] using hs

-- @node: fitted_continuous_quantile_gamma_IFM_contrast_memLp
/-- Suppose [the continuous nuisance functions are admissible](hyp:he), [the denominator bound is positive](hyp:hc), and [every positive-level baseline probability is almost surely at least that bound](hyp:hden). For [a level below the number of levels](hyp:hk), [the boundary quantile times the gamma-weighted difference between the plus-side and minus-side boundary-indicator residuals is square integrable under the population observation law](goal). -/
lemma fitted_continuous_quantile_gamma_IFM_contrast_memLp [Fintype Z]
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (c : ℝ) (hc : 0 < c)
    (hden : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (g : RegularIndex L) (k j : ℕ) (hk : k < L.K) :
    MemLp (fun o : Obs X Z => nuValue M e k j o.1 *
      (e.gamma g o.1 * (IFM M L e true k j o - IFM M L e false k j o)))
      2 (observationLaw M) := by
  have hp := fitted_continuous_gamma_IFM_memLp M L e he c hc hden g true k j hk
  have hm := fitted_continuous_gamma_IFM_memLp M L e he c hc hden g false k j hk
  have hR : MemLp (fun o : Obs X Z => e.gamma g o.1 *
      (IFM M L e true k j o - IFM M L e false k j o)) 2 (observationLaw M) := by
    convert hp.sub hm using 1
    funext o
    simp only [Pi.sub_apply, mul_sub]
  have hnu : Measurable (fun o : Obs X Z => nuValue M e k j o.1) := by fun_prop
  apply hR.of_le_mul (c := |M.yMin| + |M.yMax|)
    (f := fun o : Obs X Z => nuValue M e k j o.1 *
      (e.gamma g o.1 * (IFM M L e true k j o - IFM M L e false k j o)))
    (hnu.aestronglyMeasurable.mul hR.1)
  filter_upwards [observationLaw_covariate_ae M _
    (continuous_admissible_nuValue_abs_bound M L e he k j)] with o ho
  rw [norm_mul, Real.norm_eq_abs (nuValue M e k j o.1)]
  exact mul_le_mul_of_nonneg_right ho (norm_nonneg _)

-- @node: encoded_continuous_quantile_gamma_IFM_contrast_sq_tendsto_probability_zero
/-- Suppose [the true continuous nuisances are admissible](hyp:he0), [the fitted nuisances are clipped](hyp:hclip), [their shares satisfy the simplex constraints](hyp:hshares), [their encoded components are measurable](hyp:hm), [boundary densities are bounded](hyp:hd), and [their finite-component errors satisfy the nuisance convergence rates](hyp:hr). With [baseline overlap at the chosen bound](hyp:hov), [fitted denominators clipped at that bound](hyp:hden), and [a level below the number of levels](hyp:hk), [the population mean squared error of the boundary-quantile-weighted gamma contrast of plus-side and minus-side boundary-indicator residuals at even sample sizes converges in probability to zero](goal). -/
lemma encoded_continuous_quantile_gamma_IFM_contrast_sq_tendsto_probability_zero
    [Fintype Z]
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hd : BoundaryDensitiesBounded M L)
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L)))
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hden : ∀ n t, ContDenominatorsClipped L (eh n t) cpi)
    (g : RegularIndex L) (k j : ℕ) (hk : k < L.K) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o : Obs X Z,
        (nuValue M (eh (2*(n+1)) t) k j o.1 *
            ((eh (2*(n+1)) t).gamma g o.1 *
              (IFM M L (eh (2*(n+1)) t) true k j o -
                IFM M L (eh (2*(n+1)) t) false k j o)) -
          nuValue M (trueNuisance M L) k j o.1 *
            ((trueNuisance M L).gamma g o.1 *
              (IFM M L (trueNuisance M L) true k j o -
                IFM M L (trueNuisance M L) false k j o)))^2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  have hc : 0 < cpi / 2 := by linarith [hov.1]
  have hden0 (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, cpi / 2 ≤ (trueNuisance M L).piLev i x := by
    apply Eventually.of_forall
    intro x
    have hi := hov.2 x i.val i.property.1 i.property.2
    change cpi / 2 ≤ (levelSetProb M L).1 i.val x
    linarith [hov.1]
  let w := fun (e : NuisanceCont L) (o : Obs X Z) => nuValue M e k j o.1
  let R := fun (e : NuisanceCont L) (o : Obs X Z) => e.gamma g o.1 *
    (IFM M L e true k j o - IFM M L e false k j o)
  have hw (e : NuisanceCont L) (he : ContAdmissible M L e) :
      MemLp (w e) 2 (observationLaw M) := by
    have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
    have hn : MemLp (nuValue M e k j) 2 (xLaw M) :=
      MemLp.of_bound (by fun_prop) (|M.yMin| + |M.yMax|)
        (by simpa only [Real.norm_eq_abs] using
          continuous_admissible_nuValue_abs_bound M L e he k j)
    exact hn.comp_measurePreserving (observationLaw_fst_measurePreserving M)
  have hR (e : NuisanceCont L) (he : ContAdmissible M L e)
      (hpi : ∀ i, ∀ᵐ x ∂xLaw M, cpi / 2 ≤ e.piLev i x) :
      MemLp (R e) 2 (observationLaw M) := by
    convert
      (fitted_continuous_gamma_IFM_memLp M L e he (cpi/2) hc hpi g true k j hk).sub
        (fitted_continuous_gamma_IFM_memLp M L e he (cpi/2) hc hpi g false k j hk) using 1
    funext o
    simp only [R, Pi.sub_apply, mul_sub]
  have hRh n t := hR (er (2*(n+1)) t) (her _ t)
    (fun i => Eventually.of_forall (fun x => (hden _ t).1 i x |>.1))
  have hR0 := hR _ he0 hden0
  have hs := dml_ae_weighted_residual_sq_tendsto_probability_zero μ (observationLaw M)
    (w (trueNuisance M L)) (R (trueNuisance M L))
    (fun n t => w (er (2*(n+1)) t)) (fun n t => R (er (2*(n+1)) t))
    (|M.yMin| + |M.yMax|) (4 / (cpi / 2))
    (hw _ he0).1 hR0.1 (fun n t => (hw _ (her _ t)).1)
    (fun n t => (hRh n t).1)
    (fun n t => (hw _ (her _ t)).sub (hw _ he0))
    (fun n t => (hRh n t).sub hR0)
    (fun n t => observationLaw_covariate_ae M _
      (continuous_admissible_nuValue_abs_bound M L _ (her _ t) k j))
    (fun n t => by
      filter_upwards [fitted_continuous_gamma_IFM_abs_bound M L _ he0
        (cpi/2) hc hden0 g true k j hk,
        fitted_continuous_gamma_IFM_abs_bound M L _ he0
          (cpi/2) hc hden0 g false k j hk] with o hp hm
      dsimp only [R]
      rw [mul_sub]
      apply (abs_sub _ _).trans
      simp only [div_eq_mul_inv] at hp hm ⊢
      linarith)
    (by simpa only [w, er, restrictContShares, nuValue] using
      encoded_continuous_nuValue_sq_tendsto_probability_zero M μ L he0 eh hm hr k j)
    (by simpa only [R, er, restrictContShares, IFM, nuValue] using
      (encoded_continuous_gamma_IFM_contrast_sq_tendsto_probability_zero
        M μ L he0 eh hclip hshares hm hd hr cpi hov hden g k j hk))
  simpa only [w, R, er, restrictContShares, IFM, nuValue] using hs

-- @node: encoded_continuous_quantile_gamma_IFM_contrast_l2_tendsto_probability_zero
/-- If [the true continuous nuisances are admissible](hyp:he0), [the fitted nuisances are clipped](hyp:hclip), [their shares satisfy the simplex constraints](hyp:hshares), [their encoded components are measurable](hyp:hm), [boundary densities are bounded](hyp:hd), and [their finite-component errors satisfy the nuisance convergence rates](hyp:hr), with [baseline overlap at the chosen bound](hyp:hov) and [fitted denominators clipped at that bound](hyp:hden), then, for [a level below the number of levels](hyp:hk), [the square root of the population mean squared error of the boundary-quantile-weighted gamma contrast of plus-side and minus-side boundary-indicator residuals at even sample sizes converges in probability to zero](goal). -/
lemma encoded_continuous_quantile_gamma_IFM_contrast_l2_tendsto_probability_zero
    [Fintype Z]
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hd : BoundaryDensitiesBounded M L)
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L)))
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hden : ∀ n t, ContDenominatorsClipped L (eh n t) cpi)
    (g : RegularIndex L) (k j : ℕ) (hk : k < L.K) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => Real.sqrt (∫ o : Obs X Z,
        (nuValue M (eh (2*(n+1)) t) k j o.1 *
            ((eh (2*(n+1)) t).gamma g o.1 *
              (IFM M L (eh (2*(n+1)) t) true k j o -
                IFM M L (eh (2*(n+1)) t) false k j o)) -
          nuValue M (trueNuisance M L) k j o.1 *
            ((trueNuisance M L).gamma g o.1 *
              (IFM M L (trueNuisance M L) true k j o -
                IFM M L (trueNuisance M L) false k j o)))^2
        ∂observationLaw M)) atTop (fun _ _ => 0) := by
  have hs := encoded_continuous_quantile_gamma_IFM_contrast_sq_tendsto_probability_zero
    M μ L he0 eh hclip hshares hm hd hr cpi hov hden g k j hk
  have hcont : Continuous (fun t : ℝ => Real.sqrt t) := by fun_prop
  simpa only [Real.sqrt_zero] using
    Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt hcont.continuousAt hs

end Papers.TbsPrteOptimalTransport
