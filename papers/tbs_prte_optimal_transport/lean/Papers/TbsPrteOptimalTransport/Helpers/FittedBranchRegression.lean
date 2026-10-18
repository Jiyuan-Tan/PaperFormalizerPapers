module
public import Papers.TbsPrteOptimalTransport.Helpers.RegressionEndpointMargins
/-! Fitted-branch residual centering along binary regression paths. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set
open scoped Classical

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)

variable [Fintype Z] [DecidableEq Z]

-- @node: population_binary_fitted_branch_correction_zero
/-- Under [threshold crossing](hyp:h), [measurability of the policy derivative evaluated at
the true propensity](hyp:hdphi), and [invariance of the baseline and policy level ordering](hyp:hOrder),
suppose [the covariate weight is measurable](hyp:hw) and [the fitted interior-boundary,
dominance, and active-set indicators are measurable](hyp:hD,hE,hI).
If [the weighted upper and lower treated-success residuals](hyp:hPplus,hPminus),
[the weighted upper and lower baseline-propensity residuals](hyp:hpplus,hpminus), and
[the weighted current and preceding policy-propensity residuals are integrable](hyp:hqplus,hqminus),
then [their fitted-branch correction is integrable and has expectation zero: the interior
indicator multiplies the upper-minus-lower success residual and subtracts the upper propensity
residual, the dominance and active indicators subtract the lower propensity residual only
in the first band, and the active indicator adds the current policy residual minus the
dominance-weighted preceding policy residual](goal). -/
lemma population_binary_fitted_branch_correction_zero (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (L : LevelData Z X) (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (eb : NuisanceBin L) (k j : ℕ) (w : X → ℝ) (hw : Measurable w)
    (hD : Measurable (Dbd phi L eb k j))
    (hE : Measurable (Edom phi L eb k j))
    (hI : Measurable (Iact phi L eb k j))
    (hPplus : Integrable (fun o : Obs X Z => w o.1 * RP L (eta0Bin M L) (k + 1) o)
      (observationLaw M))
    (hPminus : Integrable (fun o : Obs X Z => w o.1 * RP L (eta0Bin M L) k o)
      (observationLaw M))
    (hpplus : Integrable (fun o : Obs X Z => w o.1 * Rp L (eta0Bin M L) (k + 1) o)
      (observationLaw M))
    (hpminus : Integrable (fun o : Obs X Z => w o.1 * Rp L (eta0Bin M L) k o)
      (observationLaw M))
    (hqplus : Integrable (fun o : Obs X Z => w o.1 * RqBin dphi L (eta0Bin M L) k j o)
      (observationLaw M))
    (hqminus : Integrable (fun o : Obs X Z => w o.1 * RqBin dphi L (eta0Bin M L) k (j - 1) o)
      (observationLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 *
      (Dbd phi L eb k j o.1 * (RP L (eta0Bin M L) (k+1) o - RP L (eta0Bin M L) k o) -
        Dbd phi L eb k j o.1 * Rp L (eta0Bin M L) (k+1) o -
        (if j = 1 then Edom phi L eb k j o.1 * Iact phi L eb k j o.1 *
          Rp L (eta0Bin M L) k o else 0) +
        Iact phi L eb k j o.1 * RqBin dphi L (eta0Bin M L) k j o -
        Edom phi L eb k j o.1 * Iact phi L eb k j o.1 *
          RqBin dphi L (eta0Bin M L) k (j-1) o))
      (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 *
      (Dbd phi L eb k j o.1 * (RP L (eta0Bin M L) (k+1) o - RP L (eta0Bin M L) k o) -
        Dbd phi L eb k j o.1 * Rp L (eta0Bin M L) (k+1) o -
        (if j = 1 then Edom phi L eb k j o.1 * Iact phi L eb k j o.1 *
          Rp L (eta0Bin M L) k o else 0) +
        Iact phi L eb k j o.1 * RqBin dphi L (eta0Bin M L) k j o -
        Edom phi L eb k j o.1 * Iact phi L eb k j o.1 *
          RqBin dphi L (eta0Bin M L) k (j-1) o)
      ∂observationLaw M) = 0 := by
  let D := Dbd phi L eb k j
  let E := Edom phi L eb k j
  let I := Iact phi L eb k j
  have hEI : Measurable (fun x => E x * I x) := hE.mul hI
  have hDb : ∀ x, ‖D x‖ ≤ 1 := by
    intro x
    simp only [D, Dbd, indicator]
    split_ifs <;> norm_num
  have hIb : ∀ x, ‖I x‖ ≤ 1 := by
    intro x
    simp only [I, Iact, indicator]
    split_ifs <;> norm_num
  have hEIb : ∀ x, ‖E x * I x‖ ≤ 1 := by
    intro x
    simp only [E, I, Edom, Iact, indicator]
    split_ifs <;> norm_num
  have hmul (c : X → ℝ) (hc : Measurable c) (hcb : ∀ x, ‖c x‖ ≤ 1)
      (r : Obs X Z → ℝ) (hr : Integrable (fun o => w o.1 * r o) (observationLaw M)) :
      Integrable (fun o => (w o.1 * c o.1) * r o) (observationLaw M) := by
    have hi := hr.bdd_mul (hc.comp measurable_fst).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun o : Obs X Z => hcb o.1))
    convert hi using 1
    ext o
    simp only [Function.comp_apply]
    ring
  have iPp := hmul D hD hDb _ hPplus
  have iPm := hmul D hD hDb _ hPminus
  have ipp := hmul D hD hDb _ hpplus
  have ipm := hmul (fun x => E x * I x) hEI hEIb _ hpminus
  have iqp := hmul I hI hIb _ hqplus
  have iqm := hmul (fun x => E x * I x) hEI hEIb _ hqminus
  have zPp := population_RP_weighted_integral_zero M L (k + 1) (fun x => w x * D x) (hw.mul hD) iPp
  have zPm := population_RP_weighted_integral_zero M L k (fun x => w x * D x) (hw.mul hD) iPm
  have zpp := population_Rp_weighted_integral_zero M h (policyProp phi M.prop) L hOrder (k + 1)
    (fun x => w x * D x) (hw.mul hD) ipp
  have zpm := population_Rp_weighted_integral_zero M h (policyProp phi M.prop) L hOrder k
    (fun x => w x * (E x * I x)) (hw.mul hEI) ipm
  have zqp := population_RqBin_weighted_integral_zero M h dphi hdphi L k j
    (fun x => w x * I x) (hw.mul hI) iqp
  have zqm := population_RqBin_weighted_integral_zero M h dphi hdphi L k (j - 1)
    (fun x => w x * (E x * I x)) (hw.mul hEI) iqm
  let low := fun o : Obs X Z => if j = 1 then
    (w o.1 * (E o.1 * I o.1)) * Rp L (eta0Bin M L) k o else 0
  have ilow : Integrable low (observationLaw M) := by
    dsimp only [low]
    split_ifs
    · exact ipm
    · exact integrable_zero _ _ _
  have zlow : (∫ o, low o ∂observationLaw M) = 0 := by
    dsimp only [low]
    split_ifs
    · exact zpm
    · simp
  have hid : (fun o : Obs X Z => w o.1 *
      (Dbd phi L eb k j o.1 * (RP L (eta0Bin M L) (k+1) o - RP L (eta0Bin M L) k o) -
        Dbd phi L eb k j o.1 * Rp L (eta0Bin M L) (k+1) o -
        (if j = 1 then Edom phi L eb k j o.1 * Iact phi L eb k j o.1 *
          Rp L (eta0Bin M L) k o else 0) +
        Iact phi L eb k j o.1 * RqBin dphi L (eta0Bin M L) k j o -
        Edom phi L eb k j o.1 * Iact phi L eb k j o.1 *
          RqBin dphi L (eta0Bin M L) k (j-1) o)) =
      (fun o => (w o.1 * D o.1) * RP L (eta0Bin M L) (k + 1) o -
        (w o.1 * D o.1) * RP L (eta0Bin M L) k o -
        (w o.1 * D o.1) * Rp L (eta0Bin M L) (k + 1) o - low o +
        (w o.1 * I o.1) * RqBin dphi L (eta0Bin M L) k j o -
        (w o.1 * (E o.1 * I o.1)) * RqBin dphi L (eta0Bin M L) k (j - 1) o) := by
    funext o
    dsimp only [binScoreComponents, D, E, I, low]
    split_ifs <;> ring
  rw [hid]
  refine ⟨(((iPp.sub' iPm).sub' ipp).sub' ilow).fun_add iqp |>.sub' iqm, ?_⟩
  rw [integral_sub ((((iPp.sub' iPm).sub' ipp).sub' ilow).fun_add iqp) iqm,
    integral_add (((iPp.sub' iPm).sub' ipp).sub' ilow) iqp,
    integral_sub ((iPp.sub' iPm).sub' ipp) ilow,
    integral_sub (iPp.sub' iPm) ipp, integral_sub iPp iPm,
    zPp, zPm, zpp, zlow, zqp, zqm]
  ring

-- The assignment terms cancel even with a moving fitted-branch weight.
-- Zero and invalid levels have a zero regression direction automatically.
-- @node: population_binary_regression_assignment_correction_zero
/-- Under [baseline overlap with the proposed positive lower bound](hyp:hov), suppose
[the direction bound is nonnegative](hyp:hC), [each positive-level regression direction
is measurable and bounded in norm by that bound almost surely](hyp:hd),
[the covariate weight is measurable](hyp:hw), [its bound is nonnegative](hyp:hB), and
[its norm is at most that bound almost surely](hyp:hwb).
Then [the covariate weight times the path size times the difference between the upper-minus-lower
normalized assignment-weighted directions and the unweighted upper-minus-lower directions
is integrable and has expectation zero](goal). -/
lemma population_binary_regression_assignment_correction_zero
    (L : LevelData Z X) (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (d : PositiveIndex L.K → X → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hd : ∀ a, Measurable (d a) ∧ ∀ᵐ x ∂xLaw M, ‖d a x‖ ≤ C)
    (w : X → ℝ) (hw : Measurable w) (B : ℝ) (hB : 0 ≤ B)
    (hwb : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ B) (k : ℕ) (t : ℝ) :
    let R := fun o : Obs X Z => w o.1 * t *
      (indicator (o.2.1 ∈ L.S (k+1)) / positiveValue (eta0Bin M L).piLev (k+1) o.1 *
        positiveValue d (k+1) o.1 -
      indicator (o.2.1 ∈ L.S k) / positiveValue (eta0Bin M L).piLev k o.1 *
        positiveValue d k o.1 -
      (positiveValue d (k+1) o.1 - positiveValue d k o.1))
    Integrable R (observationLaw M) ∧ (∫ o, R o ∂observationLaw M) = 0 := by
  dsimp only
  let c := fun i (o : Obs X Z) => (w o.1 * positiveValue d i o.1) *
    (1 - indicator (o.2.1 ∈ L.S i) / positiveValue (eta0Bin M L).piLev i o.1)
  have hc : ∀ i, Integrable (c i) (observationLaw M) ∧
      (∫ o, c i o ∂observationLaw M) = 0 := by
    intro i
    by_cases hi : 1 ≤ i ∧ i ≤ L.K
    · have hpdef : ∀ x, positiveValue (eta0Bin M L).piLev i x =
          ∑ z ∈ L.S i, instProb M z x := by
        intro x
        simp only [positiveValue, dif_pos hi, eta0Bin, levelSetProb]
      have hdm := (binary_positive_regression_direction_regular M L d C hC hd i).1
      have hdb := (binary_positive_regression_direction_regular M L d C hC hd i).2
      have hb : ∀ᵐ x ∂xLaw M, ‖w x * positiveValue d i x‖ ≤ B*C := by
        filter_upwards [hwb, hdb] with x hx hdx
        rw [norm_mul]
        exact mul_le_mul hx hdx (norm_nonneg _) hB
      have hm : Measurable (fun x => w x * positiveValue d i x) := by fun_prop
      have hp : ∀ x, cpi ≤ ∑ z ∈ L.S i, instProb M z x :=
        fun x => hov.2 x i hi.1 hi.2
      have hint := population_normalized_assignment_integrable M (L.S i) cpi hov.1 hp
        (fun x => w x * positiveValue d i x) hm (B*C) hb
      have hz := population_normalized_assignment_weighted_integral_zero M (L.S i)
        (fun x => w x * positiveValue d i x) hm
        (Filter.Eventually.of_forall fun x => hov.1.trans_le (hp x)) hint
      dsimp only [c]
      simp_rw [hpdef]
      exact ⟨hint, hz⟩
    · simp only [c, positiveValue, dif_neg hi, mul_zero, zero_mul]
      exact ⟨integrable_zero _ _ _, by simp⟩
  have hid : (fun o : Obs X Z => w o.1 * t *
      (indicator (o.2.1 ∈ L.S (k+1)) / positiveValue (eta0Bin M L).piLev (k+1) o.1 *
        positiveValue d (k+1) o.1 -
      indicator (o.2.1 ∈ L.S k) / positiveValue (eta0Bin M L).piLev k o.1 *
        positiveValue d k o.1 -
      (positiveValue d (k+1) o.1 - positiveValue d k o.1))) =
      (fun o => -t * (c (k+1) o - c k o)) := by
    funext o
    dsimp only [c]
    ring
  rw [hid]
  refine ⟨((hc (k+1)).1.sub' (hc k).1).const_mul (-t), ?_⟩
  rw [integral_const_mul, integral_sub (hc (k+1)).1 (hc k).1,
    (hc (k+1)).2, (hc k).2, sub_self, mul_zero]

-- Exact expectation identity for the actual score, with the estimated
-- branch retained. The only remaining regression contribution is the
-- debiased hinge controlled by the integrated quadratic remainder.
-- @node: population_binary_regression_component_integral_path
/-- Under [threshold crossing](hyp:h), [measurability of the policy derivative at the true
propensity](hyp:hdphi), [invariance of the baseline and policy level ordering](hyp:hOrder),
and [baseline overlap](hyp:hov), suppose [the regression-direction bound is nonnegative](hyp:hC),
[all positive-level directions are measurable and almost surely bounded by it](hyp:hd),
[the covariate weight is measurable](hyp:hw), [its bound is nonnegative](hyp:hB), and
[its norm is almost surely bounded by it](hyp:hwb).
If [the interior-boundary, dominance, and active-set indicators along the regression path
are measurable](hyp:hD,hE,hI), [the weighted baseline upper and lower success residuals](hyp:hPplus,hPminus),
[the weighted baseline upper and lower treatment-propensity residuals](hyp:hpplus,hpminus),
[the weighted baseline current and preceding policy-propensity residuals](hyp:hqplus,hqminus),
and [the weighted fitted hinge minus its interior-indicator-weighted regression increment
are integrable](hyp:hplugin), then [the weighted binary score component along this path
is integrable and its expectation equals that of the weighted fitted hinge minus the
interior indicator times the path size times the upper-minus-lower regression direction](goal). -/
lemma population_binary_regression_component_integral_path
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (L : LevelData Z X) (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (d : PositiveIndex L.K → X → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hd : ∀ a, Measurable (d a) ∧ ∀ᵐ x ∂xLaw M, ‖d a x‖ ≤ C)
    (w : X → ℝ) (hw : Measurable w) (B : ℝ) (hB : 0 ≤ B)
    (hwb : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ B) (k j : ℕ) (t : ℝ)
    (hD : Measurable (Dbd phi L
      {eta0Bin M L with P1 := fun a x => (eta0Bin M L).P1 a x + t * d a x} k j))
    (hE : Measurable (Edom phi L
      {eta0Bin M L with P1 := fun a x => (eta0Bin M L).P1 a x + t * d a x} k j))
    (hI : Measurable (Iact phi L
      {eta0Bin M L with P1 := fun a x => (eta0Bin M L).P1 a x + t * d a x} k j))
    (hPplus : Integrable (fun o : Obs X Z => w o.1 * RP L (eta0Bin M L) (k+1) o)
      (observationLaw M))
    (hPminus : Integrable (fun o : Obs X Z => w o.1 * RP L (eta0Bin M L) k o)
      (observationLaw M))
    (hpplus : Integrable (fun o : Obs X Z => w o.1 * Rp L (eta0Bin M L) (k+1) o)
      (observationLaw M))
    (hpminus : Integrable (fun o : Obs X Z => w o.1 * Rp L (eta0Bin M L) k o)
      (observationLaw M))
    (hqplus : Integrable (fun o : Obs X Z => w o.1 * RqBin dphi L (eta0Bin M L) k j o)
      (observationLaw M))
    (hqminus : Integrable (fun o : Obs X Z => w o.1 * RqBin dphi L (eta0Bin M L) k (j-1) o)
      (observationLaw M))
    (hplugin : Integrable (fun o : Obs X Z =>
      let et := {eta0Bin M L with P1 := fun a x => (eta0Bin M L).P1 a x + t * d a x}
      w o.1 * (hMinus phi L et k j o.1 - Dbd phi L et k j o.1 *
        (t * (positiveValue d (k+1) o.1 - positiveValue d k o.1)))) (observationLaw M)) :
    let et := {eta0Bin M L with P1 := fun a x => (eta0Bin M L).P1 a x + t * d a x}
    Integrable (fun o : Obs X Z => w o.1 * binScoreComponents phi dphi L et k j o)
      (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 * binScoreComponents phi dphi L et k j o ∂observationLaw M) =
      ∫ o : Obs X Z, w o.1 * (hMinus phi L et k j o.1 - Dbd phi L et k j o.1 *
        (t * (positiveValue d (k+1) o.1 - positiveValue d k o.1))) ∂observationLaw M := by
  dsimp only
  let et := {eta0Bin M L with P1 := fun a x => (eta0Bin M L).P1 a x + t * d a x}
  let corr := fun o : Obs X Z => w o.1 *
    (Dbd phi L et k j o.1 * (RP L (eta0Bin M L) (k+1) o - RP L (eta0Bin M L) k o) -
      Dbd phi L et k j o.1 * Rp L (eta0Bin M L) (k+1) o -
      (if j = 1 then Edom phi L et k j o.1 * Iact phi L et k j o.1 *
        Rp L (eta0Bin M L) k o else 0) +
      Iact phi L et k j o.1 * RqBin dphi L (eta0Bin M L) k j o -
      Edom phi L et k j o.1 * Iact phi L et k j o.1 *
        RqBin dphi L (eta0Bin M L) k (j-1) o)
  have hc : Integrable corr (observationLaw M) ∧
      (∫ o, corr o ∂observationLaw M) = 0 :=
    population_binary_fitted_branch_correction_zero M h phi dphi hdphi L hOrder et
      k j w hw hD hE hI hPplus hPminus hpplus hpminus hqplus hqminus
  have hDb : ∀ x, ‖Dbd phi L et k j x‖ ≤ 1 := by
    intro x
    unfold Dbd indicator
    split_ifs <;> norm_num
  have hwd : ∀ᵐ x ∂xLaw M, ‖w x * Dbd phi L et k j x‖ ≤ B := by
    filter_upwards [hwb] with x hx
    rw [norm_mul]
    calc
      _ ≤ B * 1 := mul_le_mul hx (hDb x) (norm_nonneg _) hB
      _ = B := mul_one B
  let assign := fun o : Obs X Z => (w o.1 * Dbd phi L et k j o.1) * t *
    (indicator (o.2.1 ∈ L.S (k+1)) / positiveValue (eta0Bin M L).piLev (k+1) o.1 *
      positiveValue d (k+1) o.1 -
    indicator (o.2.1 ∈ L.S k) / positiveValue (eta0Bin M L).piLev k o.1 *
      positiveValue d k o.1 - (positiveValue d (k+1) o.1 - positiveValue d k o.1))
  have ha : Integrable assign (observationLaw M) ∧
      (∫ o, assign o ∂observationLaw M) = 0 :=
    population_binary_regression_assignment_correction_zero M L cpi hov d C hC hd
      (fun x => w x * Dbd phi L et k j x) (hw.mul hD) B hB hwd k t
  let plug := fun o : Obs X Z => w o.1 * (hMinus phi L et k j o.1 - Dbd phi L et k j o.1 *
    (t * (positiveValue d (k+1) o.1 - positiveValue d k o.1)))
  have hid : (fun o : Obs X Z => w o.1 * binScoreComponents phi dphi L et k j o) =
      (fun o => plug o + corr o - assign o) := by
    funext o
    rw [binary_regression_score_path_decomposition]
    dsimp only [plug, corr, assign]
    ring
  change Integrable (fun o : Obs X Z => w o.1 * binScoreComponents phi dphi L et k j o) _ ∧ _
  rw [hid]
  refine ⟨(hplugin.fun_add hc.1).sub' ha.1, ?_⟩
  rw [integral_sub (hplugin.fun_add hc.1) ha.1, integral_add hplugin hc.1,
    hc.2, ha.2, add_zero, sub_zero]

-- All analytic premises above are derived here. This is orthogonality of
-- the actual regular product score for simultaneous positive-level P1 paths.
-- @node: population_binary_regular_product_regression_orthogonality_of_admissible
/-- Under [threshold crossing](hyp:h), suppose [the policy is a policy map](hyp:hphi),
[its derivative at the true propensity is measurable](hyp:hdphi), [the derivative bound
is nonnegative](hyp:hB), and [the absolute derivative is uniformly bounded by it](hyp:hbphi).
Assume [invariance of the baseline and policy level ordering](hyp:hOrder),
[measurability of every baseline propensity level](hyp:hlev), [baseline overlap](hyp:hov),
[policy overlap](hyp:hpol), [binary outcomes almost surely](hyp:hy), and
[admissibility of the binary nuisance direction at the true nuisance](hyp:had).
For [a baseline bin before the final bin](hyp:hk) and [an interior policy-band index](hyp:hj),
if [the margin is positive](hyp:hc) and [both adjacent pooled policy levels are separated
from the upper baseline propensity minus the full-interval outcome contrast by at least
that margin almost surely](hyp:hgap), then [the expected regular binary product score
has derivative zero at zero when all positive-level outcome regressions move simultaneously
along the regression part of that direction](goal). -/
lemma population_binary_regular_product_regression_orthogonality_of_admissible
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (B : ℝ) (hB : 0 ≤ B) (hbphi : ∀ z x, |dphi z x (M.prop z x)| ≤ B)
    (L : LevelData Z X) (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hlev : ∀ i, Measurable (L.pLev i)) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hy : OutcomeBinaryAE M) (del : NuisanceBin L)
    (had : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del))
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (c : ℝ) (hc : 0 < c)
    (hgap : ∀ᵐ x ∂xLaw M,
      c ≤ |positiveValue (eta0Bin M L).pLev (k+1) x - binFullJ L (eta0Bin M L) k x -
        pooledQBin phi L (eta0Bin M L) k (j-1) x| ∧
      c ≤ |positiveValue (eta0Bin M L).pLev (k+1) x - binFullJ L (eta0Bin M L) k x -
        pooledQBin phi L (eta0Bin M L) k j x|) :
    HasDerivAt (fun t : ℝ => ∫ o, psiProdBin phi dphi L
      {eta0Bin M L with P1 := fun a x => (eta0Bin M L).P1 a x + t * del.P1 a x}
      k j o ∂observationLaw M) 0 0 := by
  have : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  have : IsProbabilityMeasure (xLaw M) := Measure.isProbabilityMeasure_map M.measX.aemeasurable
  have he := binary_admissible_direction_origin M L (eta0Bin M L) del had
  obtain ⟨C, hC, hd⟩ := binary_regression_direction_regular M L (eta0Bin M L) del had
  have hpos i := binary_positive_regression_direction_regular M L del.P1 C hC hd i
  let d := fun x => positiveValue del.P1 (k+1) x - positiveValue del.P1 k x
  have hdm : Measurable d := (hpos (k+1)).1.sub (hpos k).1
  have hdb : ∀ᵐ x ∂xLaw M, ‖d x‖ ≤ 2*C := by
    filter_upwards [(hpos (k+1)).2, (hpos k).2] with x hp hm
    exact (norm_sub_le _ _).trans (by linarith)
  let et : ℝ → NuisanceBin L := fun t : ℝ => {eta0Bin M L with P1 := fun a x => (eta0Bin M L).P1 a x + t * del.P1 a x}
  let w := gamma M L k j
  have hw : Measurable w := population_instrument_set_probability_measurable M (policyUnion L k j)
  have hwb : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ 1 := by
    apply Filter.Eventually.of_forall
    intro x
    have hx := population_instrument_set_probability_range M (policyUnion L k j) x
    simpa only [w, gamma, Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2
  have hq := population_pooledQBin_measurable M h phi hphi L hlev k j
  have hl := population_pooledQBin_measurable M h phi hphi L hlev k (j-1)
  have hp : Measurable (positiveValue (eta0Bin M L).pLev (k+1)) := by
    unfold positiveValue
    split_ifs
    · exact hlev (k+1)
    · fun_prop
  have hb0 : Measurable (fun x => positiveValue (eta0Bin M L).pLev (k+1) x -
      binFullJ L (eta0Bin M L) k x) := by fun_prop
  have hbt (t : ℝ) : Measurable (fun x => positiveValue (et t).pLev (k+1) x -
      binFullJ L (et t) k x) := by
    have hid : (fun x => positiveValue (et t).pLev (k+1) x - binFullJ L (et t) k x) =
        (fun x => (positiveValue (eta0Bin M L).pLev (k+1) x -
          binFullJ L (eta0Bin M L) k x) + t * (-d x)) := by
      funext x
      exact binary_regression_boundary_path L (eta0Bin M L) del.P1 k x t
    rw [hid]
    fun_prop
  have hD t : Measurable (Dbd phi L (et t) k j) :=
    binary_Dbd_measurable phi L (et t) k j hq hl (hbt t)
  have hE t : Measurable (Edom phi L (et t) k j) :=
    binary_Edom_measurable phi L (et t) k j hl (hbt t)
  have hI t : Measurable (Iact phi L (et t) k j) :=
    binary_Iact_measurable phi L (et t) k j hq hl (hbt t)
  have hH t : Measurable (hMinus phi L (et t) k j) := by
    unfold hMinus
    exact measurable_const.max (hq.sub (hl.max (hbt t)))
  have hHb t : ∀ᵐ x ∂xLaw M, ‖hMinus phi L (et t) k j x‖ ≤ 1 := by
    filter_upwards [pooledQBin_range M phi L (eta0Bin M L) hphi he k hk j hj.2,
      pooledQBin_range M phi L (eta0Bin M L) hphi he k hk (j-1)
        ((Nat.sub_le j 1).trans hj.2)] with x hqx hlx
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
    apply max_le zero_le_one
    exact (sub_le_self _ (hlx.1.trans (le_max_left _ _))).trans hqx.2
  have hDb t : ∀ x, ‖Dbd phi L (et t) k j x‖ ≤ 1 := by
    intro x
    unfold Dbd indicator
    split_ifs <;> norm_num
  have iP i := population_binary_weighted_RP_integrable M L cpi hov hy he i w hw 1 hwb
  have ip i := population_binary_weighted_Rp_integrable M L cpi hov he i w hw 1 hwb
  have iq a := population_binary_weighted_RqBin_integrable M h dphi hdphi B hB hbphi
    phi L hOrder cpi hpol he k a w hw 1 hwb
  let f := fun t x => w x * (hMinus phi L (et t) k j x - Dbd phi L (et t) k j x * (t*d x))
  have hfm t : Measurable (f t) := by dsimp only [f]; fun_prop
  have hfint t : Integrable (fun o : Obs X Z => f t o.1) (observationLaw M) := by
    have ih : Integrable (fun o : Obs X Z => hMinus phi L (et t) k j o.1)
        (observationLaw M) := Integrable.of_bound ((hH t).comp measurable_fst).aestronglyMeasurable
          1 (observationLaw_covariate_ae M _ (hHb t))
    have id : Integrable (fun o : Obs X Z => t*d o.1) (observationLaw M) := by
      apply Integrable.of_bound ((hdm.comp measurable_fst).const_mul t).aestronglyMeasurable (|t| * (2*C))
      filter_upwards [observationLaw_covariate_ae M _ hdb] with o ho
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left ho (abs_nonneg t)
    have iDd := id.bdd_mul ((hD t).comp measurable_fst).aestronglyMeasurable
      (Filter.Eventually.of_forall fun o : Obs X Z => hDb t o.1)
    exact (ih.sub' iDd).bdd_mul (hw.comp measurable_fst).aestronglyMeasurable
      (observationLaw_covariate_ae M _ hwb)
  have hmap : (observationLaw M).map Prod.fst = xLaw M := by
    have hm := M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
    simpa only [observationLaw, xLaw, Function.comp_def] using Measure.map_map measurable_fst hm
  have heq t : (∫ o, psiProdBin phi dphi L (et t) k j o ∂observationLaw M) =
      ∫ x, f t x ∂xLaw M := by
    have hcomp := population_binary_regression_component_integral_path M h phi dphi hdphi
      L hOrder cpi hov del.P1 C hC hd w hw 1 zero_le_one hwb k j t
      (hD t) (hE t) (hI t) (iP (k+1)) (iP k) (ip (k+1)) (ip k) (iq j) (iq (j-1)) (hfint t)
    have hres := population_assignment_residual_integrable M (policyUnion L k j)
      (hMinus phi L (et t) k j) (hH t) 1 (hHb t)
    have hz := population_assignment_weighted_integral_zero M (policyUnion L k j)
      (hMinus phi L (et t) k j) (hH t) hres
    have hid : (fun o => psiProdBin phi dphi L (et t) k j o) =
        (fun o => w o.1 * binScoreComponents phi dphi L (et t) k j o +
          hMinus phi L (et t) k j o.1 * (indicator (o.2.1 ∈ policyUnion L k j) - w o.1)) := by
      funext o
      simp only [psiProdBin, regularValue, dif_pos (show k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from ⟨hk.le, hj⟩), et, eta0Bin]
      rfl
    change Integrable (fun o : Obs X Z => hMinus phi L (et t) k j o.1 *
      (indicator (o.2.1 ∈ policyUnion L k j) - w o.1)) (observationLaw M) at hres
    change (∫ o : Obs X Z, hMinus phi L (et t) k j o.1 *
      (indicator (o.2.1 ∈ policyUnion L k j) - w o.1) ∂observationLaw M) = 0 at hz
    rw [hid, integral_add hcomp.1 hres, hz, add_zero, hcomp.2]
    change (∫ o : Obs X Z, f t o.1 ∂observationLaw M) = _
    rw [← hmap]
    exact (integral_map measurable_fst.aemeasurable (hfm t).aestronglyMeasurable).symm
  have hR := population_binary_weighted_regression_endpoint_remainder_of_admissible M h phi hphi L hlev
    del had k j c hc hgap
  have het0 : et 0 = eta0Bin M L := by
    simp only [et, zero_mul, add_zero]
    rfl
  have hconst : Integrable (fun x => w x * hMinus phi L (eta0Bin M L) k j x) (xLaw M) := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [hwb, hHb 0] with x hwx hhx
    simpa only [het0, norm_mul, mul_one] using
      mul_le_mul hwx hhx (norm_nonneg _) zero_le_one
  have hsplit : (fun t : ℝ => ∫ o, psiProdBin phi dphi L (et t) k j o ∂observationLaw M) =
      (fun t => (∫ x, w x * (hMinus phi L (et t) k j x - hMinus phi L (eta0Bin M L) k j x -
        Dbd phi L (et t) k j x * (t*d x)) ∂xLaw M) +
        ∫ x, w x * hMinus phi L (eta0Bin M L) k j x ∂xLaw M) := by
    funext t
    rw [heq]
    have hi := (integrable_map_measure (hfm t).aestronglyMeasurable measurable_fst.aemeasurable).mpr (hfint t)
    rw [hmap] at hi
    have hid : (fun x => w x * (hMinus phi L (et t) k j x - hMinus phi L (eta0Bin M L) k j x -
        Dbd phi L (et t) k j x * (t*d x))) =
        (fun x => f t x - w x * hMinus phi L (eta0Bin M L) k j x) := by
      funext x
      dsimp only [f]
      ring
    rw [hid, integral_sub hi hconst]
    ring
  rw [show (fun t : ℝ => ∫ o, psiProdBin phi dphi L
    {eta0Bin M L with P1 := fun a x => (eta0Bin M L).P1 a x + t * del.P1 a x}
    k j o ∂observationLaw M) = _ from hsplit]
  exact hR.add_const _

-- Both margins come from the outcome gap, with the fixed zero included at j = 1.
-- @node: population_binary_regression_endpoint_margins
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[a finite reduction of the instrument space](hyp:hf), [invariance of the baseline and policy
level ordering](hyp:hOrder), [policy overlap](hyp:hpol), and [the discrete outcome-gap
condition with the proposed margin](hyp:hgap), for [a baseline bin before the final bin](hyp:hk)
and [an interior policy-band index](hyp:hj), [both adjacent pooled policy levels differ
in absolute value from the true upper baseline propensity minus the true full-interval
outcome contrast by at least that margin, almost surely in covariates](goal). -/
lemma population_binary_regression_endpoint_margins
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (hf : InstrumentFiniteReduction Z) (phi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hpol : PolicyOverlap M L cpi) (ch : ℝ)
    (hgap : DiscreteOutcomeGapWitness M L ch)
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    ∀ᵐ x ∂xLaw M,
      ch ≤ |positiveValue (eta0Bin M L).pLev (k+1) x - binFullJ L (eta0Bin M L) k x -
        pooledQBin phi L (eta0Bin M L) k (j-1) x| ∧
      ch ≤ |positiveValue (eta0Bin M L).pLev (k+1) x - binFullJ L (eta0Bin M L) k x -
        pooledQBin phi L (eta0Bin M L) k j x| := by
  have hl : 1 ≤ L.l k := hj.1.trans hj.2
  filter_upwards [hgap.2 k hk hl (j-1) (by omega), hgap.2 k hk hl j hj.2,
    population_binary_full_contrast_eq_Jfull M h he hf (policyProp phi M.prop) L hOrder k hk]
    with x hlow hupp hfull
  rw [population_binary_baseline_value M _ L hOrder (k+1) (by omega), hfull,
    population_pooledQBin_eq_ordered_level M phi L hOrder cpi hpol k (j-1) hk.le (by omega),
    population_pooledQBin_eq_ordered_level M phi L hOrder cpi hpol k j hk.le hj.2]
  exact ⟨hlow, hupp⟩

-- @node: population_binary_regular_product_regression_orthogonality_of_gap
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he), and
[a finite reduction of the instrument space](hyp:hf), suppose [the policy is a policy map](hyp:hphi),
[its derivative at the true propensity is measurable](hyp:hdphi), [the derivative bound
is nonnegative](hyp:hB), and [the absolute derivative is uniformly bounded by it](hyp:hbphi).
Assume [invariance of the baseline and policy level ordering](hyp:hOrder),
[measurability of all baseline propensity levels](hyp:hlev), [baseline overlap](hyp:hov),
[policy overlap](hyp:hpol), [binary outcomes almost surely](hyp:hy),
[admissibility of the binary nuisance direction at the true nuisance](hyp:had), and
[a positive discrete outcome gap](hyp:hgap).
For [a baseline bin before the final bin](hyp:hk) and [an interior policy-band index](hyp:hj),
[the expected regular binary product score has derivative zero at zero along the simultaneous
positive-level outcome-regression perturbation specified by that direction](goal). -/
lemma population_binary_regular_product_regression_orthogonality_of_gap
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (hf : InstrumentFiniteReduction Z) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (B : ℝ) (hB : 0 ≤ B) (hbphi : ∀ z x, |dphi z x (M.prop z x)| ≤ B)
    (L : LevelData Z X) (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hlev : ∀ i, Measurable (L.pLev i)) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hy : OutcomeBinaryAE M) (del : NuisanceBin L)
    (had : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del))
    (hgap : DiscreteOutcomeGap M L) (k j : ℕ) (hk : k < L.K)
    (hj : 1 ≤ j ∧ j ≤ L.l k) :
    HasDerivAt (fun t : ℝ => ∫ o, psiProdBin phi dphi L
      {eta0Bin M L with P1 := fun a x => (eta0Bin M L).P1 a x + t * del.P1 a x}
      k j o ∂observationLaw M) 0 0 := by
  obtain ⟨ch, hch, hmargin⟩ := hgap
  exact population_binary_regular_product_regression_orthogonality_of_admissible M
    h.2.2.2.1 phi dphi hphi hdphi B hB hbphi L hOrder hlev cpi hov hpol hy del had
    k j hk hj ch hch
    (population_binary_regression_endpoint_margins M h he hf phi L hOrder cpi hpol
      ch ⟨hch, hmargin⟩ k j hk hj)

end Papers.TbsPrteOptimalTransport
