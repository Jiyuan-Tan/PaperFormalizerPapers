module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousRieszCoordinates
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousTreatmentResidual
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousMovingPropensity
/-! L2 control of the continuous band's propensity corrections.
Smooth representer convergence and clipped treatment-residual convergence
control both the upper and lower level corrections. -/
public section
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.unusedFintypeInType false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
  [Fintype Z]

-- @node: fitted_continuous_alpha_treatment_memLp
/-- If [the nuisance fit is admissible](hyp:he), [the denominator bound is
positive](hyp:hc), [all positive-level fitted instrument probabilities exceed that
bound almost everywhere](hyp:hden), and [the band level is below the terminal
level](hyp:hk), [the selected upper or lower propensity representer times its
matching treatment residual is square-integrable under the observation law](goal). -/
lemma fitted_continuous_alpha_treatment_memLp (M : LatentIVModel Ω X Z)
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e)
    (c : ℝ) (hc : 0 < c)
    (hden : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (plus : Bool) (k j : ℕ) (hk : k < L.K) :
    MemLp (fun o : Obs X Z =>
      (if plus then alphaHigh M L e k j o.1 else alphaLow M L e k j o.1) *
        RpCont L e (if plus then k+1 else k) o) 2 (observationLaw M) := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  have hi : (if plus then k+1 else k) ≤ L.K := by cases plus <;> simp <;> omega
  have ha := continuous_admissible_alpha_abs_bounds M L e he k j
  have hm : Measurable (fun x => if plus then alphaHigh M L e k j x
      else alphaLow M L e k j x) := by
    first | fun_prop | (cases plus <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop)
  have hb : ∀ᵐ x ∂xLaw M,
      |if plus then alphaHigh M L e k j x else alphaLow M L e k j x| ≤
        5 * (|M.yMin| + |M.yMax|) := by cases plus <;> simp_all only [Bool.false_eq_true, ↓reduceIte]
  apply MemLp.of_bound (by
    first | fun_prop | exact ((hm.comp measurable_fst).mul
      (fitted_RpCont_measurable M L e he _)).aestronglyMeasurable) (5 * (|M.yMin| + |M.yMax|) * (1/c))
  filter_upwards [observationLaw_covariate_ae M _ hb,
    fitted_RpCont_abs_bound M L e he c hc hden _ hi] with o ho hr
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul ho hr (abs_nonneg _) (by positivity)

-- @node: encoded_continuous_alpha_treatment_sq_tendsto_probability_zero
/-- Assume [population nuisance admissibility](hyp:he0), [clipping of every
fit](hyp:hclip), [simplex-valued fitted shares](hyp:hshares), [measurable encoded
components](hyp:hm), [componentwise L² errors that vanish faster in probability
than the inverse fourth root of sample size](hyp:hr), [baseline
overlap with the specified constant](hyp:hov), and [denominators clipped using
that constant](hyp:hden). For [a band level below the terminal level](hyp:hk),
[the observation-integrated squared error of the selected upper or lower
representer times its treatment residual converges to zero in probability,
along sample sizes twice one plus the index](goal). -/
lemma encoded_continuous_alpha_treatment_sq_tendsto_probability_zero
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
    (plus : Bool) (k j : ℕ) (hk : k < L.K) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o : Obs X Z,
        ((if plus then alphaHigh M L (eh (2*(n+1)) t) k j o.1
          else alphaLow M L (eh (2*(n+1)) t) k j o.1) *
            RpCont L (eh (2*(n+1)) t) (if plus then k+1 else k) o -
          (if plus then alphaHigh M L (trueNuisance M L) k j o.1
            else alphaLow M L (trueNuisance M L) k j o.1) *
            RpCont L (trueNuisance M L) (if plus then k+1 else k) o)^2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  let w := fun (e : NuisanceCont L) x =>
    if plus then alphaHigh M L e k j x else alphaLow M L e k j x
  let i := if plus then k+1 else k
  have hi : i ≤ L.K := by dsimp [i]; cases plus <;> simp <;> omega
  have hw (e : NuisanceCont L) (he : ContAdmissible M L e) : Measurable (w e) := by
    dsimp [w]
    first | fun_prop | (cases plus <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop)
  have hwb (e : NuisanceCont L) (he : ContAdmissible M L e) :
      ∀ᵐ x ∂xLaw M, |w e x| ≤ 5 * (|M.yMin| + |M.yMax|) := by
    have h := continuous_admissible_alpha_abs_bounds M L e he k j
    cases plus
    · exact h.2
    · exact h.1
  have hwm (e : NuisanceCont L) (he : ContAdmissible M L e) : MemLp (w e) 2 (xLaw M) := by
    dsimp [w]; cases plus
    · exact fitted_continuous_alphaLow_memLp M L e he k j
    · exact fitted_continuous_alphaHigh_memLp M L e he k j
  have hrw : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (w (er (2*(n+1)) t) x - w (trueNuisance M L) x)^2
        ∂xLaw M) atTop (fun _ _ => 0) := by
    cases plus
    · simpa only [w, Bool.false_eq_true, ↓reduceIte, er, restrictContShares, alphaLow, nuValue] using
        encoded_continuous_alphaLow_sq_tendsto_probability_zero M μ L he0 eh hclip hshares hm hr k j
    · simpa only [w, ↓reduceIte, er, restrictContShares, alphaHigh, nuValue] using
        encoded_continuous_alphaHigh_sq_tendsto_probability_zero M μ L he0 eh hclip hshares hm hr k j
  have hc : 0 < cpi/2 := by linarith [hov.1]
  have hboth n t (a : PositiveIndex L.K) : ∀ᵐ x ∂xLaw M,
      cpi/2 ≤ (trueNuisance M L).piLev a x ∧ cpi/2 ≤ (er n t).piLev a x := by
    apply Eventually.of_forall
    intro x
    have h0 : cpi ≤ (trueNuisance M L).piLev a x := hov.2 x a a.property.1 a.property.2
    exact ⟨by linarith [hov.1], (hden n t).1 a x |>.1⟩
  obtain ⟨_, hrp, hrpi, _⟩ :=
    continuous_component_rates_to_oracle_rates M μ L eh (trueNuisance M L) hr
  have hrr := nuisanceRates_RpCont_sq_tendsto_probability_zero M μ L _ er he0 her
    (cpi/2) hc hboth hrp hrpi i hi
  have hint n t := observationLaw_covariate_integral M
    (fun x => (w (er (2*(n+1)) t) x - w (trueNuisance M L) x)^2) (by
      first | fun_prop | exact ((hw _ (her _ t)).sub (hw _ he0)).pow_const 2)
  have hs := dml_weighted_residual_sq_tendsto_probability_zero μ (observationLaw M)
    (fun o => w (trueNuisance M L) o.1) (RpCont L (trueNuisance M L) i)
    (fun n t o => w (er (2*(n+1)) t) o.1)
    (fun n t => RpCont L (er (2*(n+1)) t) i)
    (5 * (|M.yMin| + |M.yMax|)) (1/(cpi/2))
    (by fun_prop) (by fun_prop) (by intro n t; first | fun_prop | exact (hw _ (her _ t)).comp measurable_fst)
    (by intro n t; first | fun_prop | exact fitted_RpCont_measurable M L _ (her _ t) i)
    (fun n t => ((hwm _ (her _ t)).sub (hwm _ he0)).comp_measurePreserving
      (observationLaw_fst_measurePreserving M))
    (fun n t => (fitted_RpCont_memLp M L _ (her _ t) (cpi/2) hc
      (fun a => (hboth _ t a).mono (fun _ h => h.2)) i hi).sub
      (fitted_RpCont_memLp M L _ he0 (cpi/2) hc
        (fun a => (hboth (2*(n+1)) t a).mono (fun _ h => h.1)) i hi))
    (fun n t => observationLaw_covariate_ae M _ (hwb _ (her _ t)))
    (fun n t => fitted_RpCont_abs_bound M L _ he0 (cpi/2) hc
      (fun a => (hboth n t a).mono (fun _ h => h.1)) i hi)
    (by simpa only [hint] using hrw) hrr
  simpa only [w, i, er, restrictContShares, alphaHigh, alphaLow, nuValue, RpCont] using hs

-- @node: encoded_continuous_alpha_treatment_l2_tendsto_probability_zero
/-- Given [an admissible population nuisance](hyp:he0), [clipped fits](hyp:hclip),
[simplex-valued fitted shares](hyp:hshares), [measurable encoded components](hyp:hm),
[componentwise L² errors that vanish faster in probability than the inverse
fourth root of sample size](hyp:hr), [baseline overlap](hyp:hov), and [denominator
clipping at the overlap constant](hyp:hden), for [a nonterminal band level](hyp:hk)
[the square root of the observation-integrated squared error of the selected
propensity representer times its treatment residual converges to zero in
probability along sample sizes twice one plus the index](goal). -/
lemma encoded_continuous_alpha_treatment_l2_tendsto_probability_zero
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
    (plus : Bool) (k j : ℕ) (hk : k < L.K) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => Real.sqrt (∫ o : Obs X Z,
        ((if plus then alphaHigh M L (eh (2*(n+1)) t) k j o.1
          else alphaLow M L (eh (2*(n+1)) t) k j o.1) *
            RpCont L (eh (2*(n+1)) t) (if plus then k+1 else k) o -
          (if plus then alphaHigh M L (trueNuisance M L) k j o.1
            else alphaLow M L (trueNuisance M L) k j o.1) *
            RpCont L (trueNuisance M L) (if plus then k+1 else k) o)^2
        ∂observationLaw M)) atTop (fun _ _ => 0) := by
  have hs := encoded_continuous_alpha_treatment_sq_tendsto_probability_zero
    M μ L he0 eh hclip hshares hm hr cpi hov hden plus k j hk
  have hcont : Continuous (fun t : ℝ => Real.sqrt t) := by fun_prop
  simpa only [Real.sqrt_zero] using
    Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt hcont.continuousAt hs

end Papers.TbsPrteOptimalTransport
