module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousBandTreatment
/-! Fitted product weights and finite assembly of the continuous band propensity corrections.
The smooth representers and clipped treatment residuals converge componentwise;
bounded fitted gamma weights preserve this convergence, including the zero baseline. -/
public section
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.unnecessarySimpa false
set_option linter.unreachableTactic false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
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
  [Fintype Z]

-- @node: fitted_continuous_gamma_alpha_treatment_memLp
/-- If [the continuous nuisance functions are admissible](hyp:he), [the denominator bound is positive](hyp:hc), and [every positive-level baseline probability is at least that bound almost everywhere](hyp:hden), then, for [a nonterminal population level](hyp:hk), [the gamma-weighted product of the selected upper or lower propensity representer and its treatment residual is square integrable under the observation law](goal). -/
lemma fitted_continuous_gamma_alpha_treatment_memLp (M : LatentIVModel Ω X Z)
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e)
    (c : ℝ) (hc : 0 < c)
    (hden : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (g : RegularIndex L) (plus : Bool) (k j : ℕ) (hk : k < L.K) :
    MemLp (fun o : Obs X Z => e.gamma g o.1 *
      ((if plus then alphaHigh M L e k j o.1 else alphaLow M L e k j o.1) *
        RpCont L e (if plus then k+1 else k) o)) 2 (observationLaw M) := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  have hg : Measurable (e.gamma g) := by
    first | fun_prop | skip
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hm, _⟩
    exact hm g
  have hgb : ∀ᵐ x ∂xLaw M, |e.gamma g x| ≤ 1 := by
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hb, _⟩
    filter_upwards [hb g] with x hx
    simpa only [abs_of_nonneg hx.1] using hx.2
  have ha := continuous_admissible_alpha_abs_bounds M L e he k j
  have hm : Measurable (fun x => if plus then alphaHigh M L e k j x
      else alphaLow M L e k j x) := by
    first | fun_prop | (cases plus <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop)
  have hb : ∀ᵐ x ∂xLaw M,
      |if plus then alphaHigh M L e k j x else alphaLow M L e k j x| ≤
        5 * (|M.yMin| + |M.yMax|) := by
    cases plus
    · exact ha.2
    · exact ha.1
  have hi : (if plus then k+1 else k) ≤ L.K := by cases plus <;> simp <;> omega
  apply MemLp.of_bound (by
    first | fun_prop | exact ((hg.comp measurable_fst).mul
      ((hm.comp measurable_fst).mul (fitted_RpCont_measurable M L e he _))).aestronglyMeasurable)
    (5 * (|M.yMin| + |M.yMax|) * (1/c))
  filter_upwards [observationLaw_covariate_ae M _ hgb,
    observationLaw_covariate_ae M _ hb,
    fitted_RpCont_abs_bound M L e he c hc hden _ hi] with o hg ha hr
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  exact (mul_le_mul hg (mul_le_mul ha hr (abs_nonneg _) (by positivity))
    (by positivity) zero_le_one).trans_eq (one_mul _)

-- @node: encoded_continuous_gamma_alpha_treatment_sq_tendsto_probability_zero
/-- Suppose [the true continuous nuisance functions are admissible](hyp:he0), [all fitted nuisances obey their clipping bounds](hyp:hclip), [fitted shares are nonnegative and sum to one](hyp:hshares), [all encoded fitted components are measurable](hyp:hm), and [each component has L2 error of smaller order in probability than the inverse fourth root of sample size](hyp:hr). If [baseline overlap holds](hyp:hov), [fitted denominators obey the overlap-based clipping bounds](hyp:hden), and [the population level is nonterminal](hyp:hk), then [the observation-integrated squared error of the gamma-weighted selected propensity representer times its treatment residual, fitted at sample sizes twice one plus the index, converges in probability to zero](goal). -/
lemma encoded_continuous_gamma_alpha_treatment_sq_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L)))
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hden : ∀ n t, ContDenominatorsClipped L (eh n t) cpi)
    (g : RegularIndex L) (plus : Bool) (k j : ℕ) (hk : k < L.K) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o : Obs X Z,
        ((eh (2*(n+1)) t).gamma g o.1 *
            ((if plus then alphaHigh M L (eh (2*(n+1)) t) k j o.1
              else alphaLow M L (eh (2*(n+1)) t) k j o.1) *
              RpCont L (eh (2*(n+1)) t) (if plus then k+1 else k) o) -
          (trueNuisance M L).gamma g o.1 *
            ((if plus then alphaHigh M L (trueNuisance M L) k j o.1
              else alphaLow M L (trueNuisance M L) k j o.1) *
              RpCont L (trueNuisance M L) (if plus then k+1 else k) o))^2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  let f := fun (e : NuisanceCont L) (o : Obs X Z) =>
    (if plus then alphaHigh M L e k j o.1 else alphaLow M L e k j o.1) *
      RpCont L e (if plus then k+1 else k) o
  have hc : 0 < cpi/2 := by linarith [hov.1]
  have hd0 (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, cpi/2 ≤ (trueNuisance M L).piLev i x := by
    apply Eventually.of_forall
    intro x
    have h0 : cpi ≤ (trueNuisance M L).piLev i x := hov.2 x i i.property.1 i.property.2
    linarith [hov.1]
  have hw (e : NuisanceCont L) (he : ContAdmissible M L e) :
      Measurable (e.gamma g) ∧ (∀ᵐ x ∂xLaw M, |e.gamma g x| ≤ 1) := by
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hb, hm, _⟩
    refine ⟨by first | fun_prop | exact hm g, ?_⟩
    filter_upwards [hb g] with x hx
    simpa only [abs_of_nonneg hx.1] using hx.2
  have hwmem (e : NuisanceCont L) (he : ContAdmissible M L e) :
      MemLp (fun o : Obs X Z => e.gamma g o.1) 2 (observationLaw M) := by
    haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
    apply MemLp.of_bound (by first | fun_prop | exact ((hw e he).1.comp measurable_fst).aestronglyMeasurable) 1
    simpa only [Real.norm_eq_abs] using observationLaw_covariate_ae M _ (hw e he).2
  have hf (e : NuisanceCont L) (he : ContAdmissible M L e) : Measurable (f e) := by
    dsimp only [f]
    first | fun_prop | (cases plus <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop)
  have hi : (if plus then k+1 else k) ≤ L.K := by cases plus <;> simp <;> omega
  have hfb : ∀ᵐ o ∂observationLaw M, |f (trueNuisance M L) o| ≤
      5 * (|M.yMin| + |M.yMax|) * (1/(cpi/2)) := by
    have ha := continuous_admissible_alpha_abs_bounds M L _ he0 k j
    have hb : ∀ᵐ x ∂xLaw M,
        |if plus then alphaHigh M L (trueNuisance M L) k j x
          else alphaLow M L (trueNuisance M L) k j x| ≤ 5 * (|M.yMin| + |M.yMax|) := by
      cases plus
      · exact ha.2
      · exact ha.1
    filter_upwards [observationLaw_covariate_ae M _ hb,
      fitted_RpCont_abs_bound M L _ he0 (cpi/2) hc hd0 _ hi] with o ha hr
    dsimp only [f]
    rw [abs_mul]
    exact mul_le_mul ha hr (abs_nonneg _) (by positivity)
  obtain ⟨_, _, _, _, _, _, hrg, _⟩ :=
    continuous_component_rates_to_oracle_rates M μ L eh (trueNuisance M L) hr
  have hint n t := observationLaw_covariate_integral M
    (fun x => ((er (2*(n+1)) t).gamma g x - (trueNuisance M L).gamma g x)^2)
    (by first | fun_prop | exact ((hw _ (her _ t)).1.sub (hw _ he0).1).pow_const 2)
  have hs := dml_weighted_residual_sq_tendsto_probability_zero μ (observationLaw M)
    (fun o => (trueNuisance M L).gamma g o.1) (f (trueNuisance M L))
    (fun n t o => (er (2*(n+1)) t).gamma g o.1) (fun n t => f (er (2*(n+1)) t))
    1 (5 * (|M.yMin| + |M.yMax|) * (1/(cpi/2)))
    (by first | fun_prop | exact (hw _ he0).1.comp measurable_fst) (hf _ he0)
    (fun n t => by first | fun_prop | exact (hw _ (her _ t)).1.comp measurable_fst)
    (fun n t => hf _ (her _ t))
    (fun n t => (hwmem _ (her _ t)).sub (hwmem _ he0))
    (fun n t => (fitted_continuous_alpha_treatment_memLp M L _ (her _ t) (cpi/2) hc
      (fun i => Eventually.of_forall (fun x => (hden _ t).1 i x |>.1)) plus k j hk).sub
      (fitted_continuous_alpha_treatment_memLp M L _ he0 (cpi/2) hc hd0 plus k j hk))
    (fun n t => observationLaw_covariate_ae M _ (hw _ (her _ t)).2)
    (fun _ _ => hfb)
    (by
      have hrw : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
          (fun n t => ∫ x, ((er (2*(n+1)) t).gamma g x -
            (trueNuisance M L).gamma g x)^2 ∂xLaw M) atTop (fun _ _ => 0) := by
        simpa only [er, restrictContShares] using
          nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hrg g
      simpa only [hint] using hrw)
    (encoded_continuous_alpha_treatment_sq_tendsto_probability_zero
      M μ L he0 eh hclip hshares hm hr cpi hov hden plus k j hk)
  simpa only [f, er, restrictContShares, alphaHigh, alphaLow, nuValue, RpCont] using hs

-- @node: fitted_continuous_gamma_alpha_treatment_block_memLp
/-- If [the continuous nuisance functions are admissible](hyp:he), [the denominator bound is positive](hyp:hc), and [positive-level baseline probabilities are at least that bound almost everywhere](hyp:hden), then [the sum over nonterminal population levels and regular bands of gamma-weighted selected upper or lower propensity representers times their treatment residuals is square integrable](goal); each regular band uses the preceding outcome-band coordinate. -/
lemma fitted_continuous_gamma_alpha_treatment_block_memLp
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (c : ℝ) (hc : 0 < c)
    (hden : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (plus : Bool) :
    MemLp (fun o : Obs X Z => ∑ k ∈ Finset.range L.K,
      ∑ j ∈ Finset.Icc 1 (L.l k), regularValue e.gamma k j o.1 *
        ((if plus then alphaHigh M L e k (j-1) o.1
          else alphaLow M L e k (j-1) o.1) *
          RpCont L e (if plus then k+1 else k) o)) 2 (observationLaw M) := by
  apply memLp_finsetSum
  intro k hk
  apply memLp_finsetSum
  intro j hj
  have hg : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k :=
    ⟨(Finset.mem_range.mp hk).le, Finset.mem_Icc.mp hj⟩
  simpa only [regularValue, dif_pos hg] using
    fitted_continuous_gamma_alpha_treatment_memLp M L e he c hc hden
      ⟨(k,j), hg⟩ plus k (j-1) (Finset.mem_range.mp hk)

-- @node: encoded_continuous_gamma_alpha_treatment_block_sq_tendsto_probability_zero
/-- Under [admissibility of the true nuisances](hyp:he0), [clipping of every fitted nuisance](hyp:hclip), [nonnegative fitted shares summing to one](hyp:hshares), [measurability of the encoded fitted components](hyp:hm), and [componentwise L2 errors of smaller order in probability than the inverse fourth root of sample size](hyp:hr), assume [baseline overlap](hyp:hov) and [overlap-based clipping of fitted denominators](hyp:hden). Then [the observation-integrated squared error of the summed gamma-weighted treatment correction on the selected upper or lower side converges in probability to zero along sample sizes twice one plus the index](goal), with regular band weights paired with the preceding outcome-band coordinate. -/
lemma encoded_continuous_gamma_alpha_treatment_block_sq_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L)))
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hden : ∀ n t, ContDenominatorsClipped L (eh n t) cpi) (plus : Bool) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o : Obs X Z,
        ((∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
          regularValue (eh (2*(n+1)) t).gamma k j o.1 *
            ((if plus then alphaHigh M L (eh (2*(n+1)) t) k (j-1) o.1
              else alphaLow M L (eh (2*(n+1)) t) k (j-1) o.1) *
              RpCont L (eh (2*(n+1)) t) (if plus then k+1 else k) o)) -
          ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
            regularValue (trueNuisance M L).gamma k j o.1 *
              ((if plus then alphaHigh M L (trueNuisance M L) k (j-1) o.1
              else alphaLow M L (trueNuisance M L) k (j-1) o.1) *
              RpCont L (trueNuisance M L) (if plus then k+1 else k) o)) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  have hc : 0 < cpi/2 := by linarith [hov.1]
  have hd0 (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, cpi/2 ≤ (trueNuisance M L).piLev i x := by
    apply Eventually.of_forall
    intro x
    have h0 : cpi ≤ (trueNuisance M L).piLev i x := hov.2 x i i.property.1 i.property.2
    linarith [hov.1]
  let F := fun (k j n : ℕ) (t : A) (o : Obs X Z) =>
    regularValue (er (2*(n+1)) t).gamma k j o.1 *
      ((if plus then alphaHigh M L (er (2*(n+1)) t) k (j-1) o.1
              else alphaLow M L (er (2*(n+1)) t) k (j-1) o.1) *
              RpCont L (er (2*(n+1)) t) (if plus then k+1 else k) o) -
    regularValue (trueNuisance M L).gamma k j o.1 *
      ((if plus then alphaHigh M L (trueNuisance M L) k (j-1) o.1
              else alphaLow M L (trueNuisance M L) k (j-1) o.1) *
              RpCont L (trueNuisance M L) (if plus then k+1 else k) o)
  have hF k j n t (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
      MemLp (F k j n t) 2 (observationLaw M) := by
    have hg : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k := ⟨hk.le, hj⟩
    convert
      (fitted_continuous_gamma_alpha_treatment_memLp M L (er (2*(n+1)) t)
        (her (2*(n+1)) t) (cpi/2) hc
        (fun i => Eventually.of_forall (fun x => (hden _ t).1 i x |>.1))
        ⟨(k,j), hg⟩ plus k (j-1) hk).sub
      (fitted_continuous_gamma_alpha_treatment_memLp M L _ he0 (cpi/2) hc hd0
        ⟨(k,j), hg⟩ plus k (j-1) hk) using 1
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
      simpa only [F, regularValue, dif_pos hg, er, restrictContShares, alphaHigh, alphaLow, nuValue, RpCont] using
        encoded_continuous_gamma_alpha_treatment_sq_tendsto_probability_zero
          M μ L he0 eh hclip hshares hm hr cpi hov hden
          ⟨(k,j), hg⟩ plus k (j-1) (Finset.mem_range.mp hk))
  simpa only [F, er, restrictContShares, regularValue, alphaHigh, alphaLow, nuValue, RpCont,
    Finset.sum_sub_distrib] using hs

-- Each side retains its own fitted gamma and shifted band coordinate.
-- The baseline lower-side term vanishes because RpCont at level zero is zero.
-- The L2 norm is the square root of the assembled nonnegative energy.
-- @node: encoded_continuous_gamma_alpha_treatment_block_l2_tendsto_probability_zero
/-- Suppose [the true nuisances are admissible](hyp:he0), [fitted nuisances are clipped](hyp:hclip), [their shares are nonnegative and sum to one](hyp:hshares), [their encoded components are measurable](hyp:hm), and [their componentwise L2 errors are of smaller order in probability than the inverse fourth root of sample size](hyp:hr). With [baseline overlap](hyp:hov) and [overlap-based fitted denominator clipping](hyp:hden), [the L2 distance between the fitted and true summed gamma-weighted treatment corrections on the selected side converges in probability to zero along sample sizes twice one plus the index](goal). -/
lemma encoded_continuous_gamma_alpha_treatment_block_l2_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L)))
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hden : ∀ n t, ContDenominatorsClipped L (eh n t) cpi) (plus : Bool) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => Real.sqrt (∫ o : Obs X Z,
        ((∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
          regularValue (eh (2*(n+1)) t).gamma k j o.1 *
            ((if plus then alphaHigh M L (eh (2*(n+1)) t) k (j-1) o.1
              else alphaLow M L (eh (2*(n+1)) t) k (j-1) o.1) *
              RpCont L (eh (2*(n+1)) t) (if plus then k+1 else k) o)) -
          ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
            regularValue (trueNuisance M L).gamma k j o.1 *
              ((if plus then alphaHigh M L (trueNuisance M L) k (j-1) o.1
              else alphaLow M L (trueNuisance M L) k (j-1) o.1) *
              RpCont L (trueNuisance M L) (if plus then k+1 else k) o)) ^ 2
        ∂observationLaw M)) atTop (fun _ _ => 0) := by
  have hs := encoded_continuous_gamma_alpha_treatment_block_sq_tendsto_probability_zero
    M μ L he0 eh hclip hshares hm hr cpi hov hden plus
  have hcont : Continuous (fun t : ℝ => Real.sqrt t) := by fun_prop
  simpa only [Real.sqrt_zero] using
    Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt hcont.continuousAt hs

-- The score omits the lower correction at its structural-zero level.
-- @node: continuous_band_lower_correction_eq
/-- [Setting the lower treatment correction to zero at population level zero gives the same value as using the lower propensity representer times the treatment residual at every level](goal). -/
lemma continuous_band_lower_correction_eq (M : LatentIVModel Ω X Z)
    (L : LevelData Z X) (e : NuisanceCont L) (k j : ℕ) (o : Obs X Z) :
    (if k = 0 then 0 else alphaLow M L e k j o.1 * RpCont L e k o) =
      alphaLow M L e k j o.1 * RpCont L e k o := by
  by_cases hk : k = 0
  · subst k
    simp only [RpCont, ↓reduceIte, mul_zero]
  · simp only [hk, if_false]

-- @node: fitted_continuous_paired_band_treatment_block_memLp
/-- Given [admissible continuous nuisances](hyp:he), [a positive denominator bound](hyp:hc), and [positive-level baseline probabilities bounded below almost everywhere](hyp:hden), [the sum over nonterminal levels and regular bands of gamma times the sum of lower and upper treatment corrections is square integrable](goal), with the lower correction omitted at level zero and each band using the preceding outcome-band coordinate. -/
lemma fitted_continuous_paired_band_treatment_block_memLp
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (c : ℝ) (hc : 0 < c)
    (hden : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) :
    MemLp (fun o : Obs X Z => ∑ k ∈ Finset.range L.K,
      ∑ j ∈ Finset.Icc 1 (L.l k), regularValue e.gamma k j o.1 *
        ((if k = 0 then 0 else alphaLow M L e k (j-1) o.1 * RpCont L e k o) +
          alphaHigh M L e k (j-1) o.1 * RpCont L e (k+1) o))
      2 (observationLaw M) := by
  have hs := (fitted_continuous_gamma_alpha_treatment_block_memLp
    M L e he c hc hden false).add
    (fitted_continuous_gamma_alpha_treatment_block_memLp M L e he c hc hden true)
  convert hs using 1
  funext o
  simp only [Pi.add_apply, Bool.false_eq_true, if_false, if_true,
    continuous_band_lower_correction_eq, mul_add, Finset.sum_add_distrib]

-- @node: encoded_continuous_paired_band_treatment_block_sq_tendsto_probability_zero
/-- If [the true nuisances are admissible](hyp:he0), [fitted nuisances satisfy clipping](hyp:hclip), [fitted shares are nonnegative and sum to one](hyp:hshares), [encoded fitted components are measurable](hyp:hm), and [componentwise L2 errors are of smaller order in probability than the inverse fourth root of sample size](hyp:hr), then, under [baseline overlap](hyp:hov) and [overlap-based fitted denominator clipping](hyp:hden), [the observation-integrated squared error of the gamma-weighted block combining lower and upper treatment corrections converges in probability to zero along sample sizes twice one plus the index](goal). -/
lemma encoded_continuous_paired_band_treatment_block_sq_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L)))
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hden : ∀ n t, ContDenominatorsClipped L (eh n t) cpi) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o : Obs X Z,
        ((∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
          regularValue (eh (2*(n+1)) t).gamma k j o.1 *
            ((if k = 0 then 0 else alphaLow M L (eh (2*(n+1)) t) k (j-1) o.1 *
              RpCont L (eh (2*(n+1)) t) k o) +
              alphaHigh M L (eh (2*(n+1)) t) k (j-1) o.1 *
                RpCont L (eh (2*(n+1)) t) (k+1) o)) -
          ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
            regularValue (trueNuisance M L).gamma k j o.1 *
              ((if k = 0 then 0 else alphaLow M L (trueNuisance M L) k (j-1) o.1 *
                RpCont L (trueNuisance M L) k o) +
                alphaHigh M L (trueNuisance M L) k (j-1) o.1 *
                  RpCont L (trueNuisance M L) (k+1) o))^2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  have hc : 0 < cpi/2 := by linarith [hov.1]
  have hd0 (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, cpi/2 ≤ (trueNuisance M L).piLev i x := by
    apply Eventually.of_forall
    intro x
    have h0 : cpi ≤ (trueNuisance M L).piLev i x := hov.2 x i i.property.1 i.property.2
    linarith [hov.1]
  let B := fun (plus : Bool) (e : NuisanceCont L) (o : Obs X Z) =>
    ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
      regularValue e.gamma k j o.1 *
        ((if plus then alphaHigh M L e k (j-1) o.1 else alphaLow M L e k (j-1) o.1) *
          RpCont L e (if plus then k+1 else k) o)
  let F := fun plus n t o => B plus (er (2*(n+1)) t) o - B plus (trueNuisance M L) o
  have hmem plus n t : MemLp (F plus n t) 2 (observationLaw M) :=
    (fitted_continuous_gamma_alpha_treatment_block_memLp M L _ (her _ t) (cpi/2) hc
      (fun i => Eventually.of_forall (fun x => (hden _ t).1 i x |>.1)) plus).sub
    (fitted_continuous_gamma_alpha_treatment_block_memLp M L _ he0 (cpi/2) hc hd0 plus)
  have hrF plus : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o, (F plus n t o)^2 ∂observationLaw M) atTop (fun _ _ => 0) := by
    simpa only [F, B, er, restrictContShares, regularValue, alphaHigh, alphaLow, nuValue, RpCont] using
      encoded_continuous_gamma_alpha_treatment_block_sq_tendsto_probability_zero
        M μ L he0 eh hclip hshares hm hr cpi hov hden plus
  have hz : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun _ : ℕ => fun _ : A => (0 : ℝ)) atTop (fun _ _ => 0) := by
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
    intro eps heps
    simpa [not_le_of_gt heps] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
  have hs := dml_three_term_sq_tendsto_probability_zero μ (observationLaw M)
    (F false) (F true) (fun _ _ _ => 0) (hmem false) (hmem true)
    (fun _ _ => MemLp.zero) (hrF false) (hrF true) (by simpa using hz)
  have hrestriction plus n t o : B plus (er n t) o = B plus (eh n t) o := by
    simp only [B, er, restrictContShares, regularValue, alphaHigh, alphaLow, nuValue, RpCont]
  convert hs using 1
  funext n t
  congr 1
  funext o
  simp only [F, hrestriction]
  simp only [B, Bool.false_eq_true, if_false, if_true,
    continuous_band_lower_correction_eq, mul_add, Finset.sum_add_distrib]
  ring

end Papers.TbsPrteOptimalTransport
