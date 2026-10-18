module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationFullJointMean
/-! Weighted fitted treatment-residual tower identities for simultaneous binary nuisance paths. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- A bounded reciprocal transfers integrability from the population residual.
-- @node: population_binary_Rp_fitted_denominator_integrable
/-- Given [baseline assignment overlap](hyp:hov) and [admissibility of the true binary
nuisance](hyp:he), suppose [the fitted assignment denominators are measurable at every
positive level](hyp:hpi), [their lower bound is positive](hyp:hc), and [each denominator
is at least that bound almost everywhere](hyp:hp). Then [the treatment residual using the
true regression and fitted denominators is integrable under the observation law at every
level, including levels outside the positive range](goal). -/
lemma population_binary_Rp_fitted_denominator_integrable
    (L : LevelData Z X) (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (he : BinAdmissible M L (eta0Bin M L))
    (pi : PositiveIndex L.K → X → ℝ) (hpi : ∀ a, Measurable (pi a))
    (c : ℝ) (hc : 0 < c) (hp : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ pi a x) (i : ℕ) :
    Integrable (Rp L {eta0Bin M L with piLev := pi} i) (observationLaw M) := by
  by_cases hi : 1 ≤ i ∧ i ≤ L.K
  · let a : PositiveIndex L.K := ⟨i, hi⟩
    let w : X → ℝ := fun x => (eta0Bin M L).piLev a x / pi a x
    have hw : Measurable w := (he.2.2.2.1 a).2.2.div (hpi a)
    have hb : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ 1 / c := by
      filter_upwards [hp a, he.2.2.1 a] with x hx heX
      have htrue : (eta0Bin M L).piLev a x ∈ Icc (0 : ℝ) 1 := heX.2.2
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg htrue.1, abs_of_pos (hc.trans_le hx)]
      exact (div_le_div_of_nonneg_right htrue.2 (hc.trans_le hx).le).trans
        (div_le_div_of_nonneg_left zero_le_one hc hx)
    have iw := (population_binary_Rp_integrable M L cpi hov he i).bdd_mul
      (hw.comp measurable_fst).aestronglyMeasurable (observationLaw_covariate_ae M _ hb)
    apply iw.congr
    filter_upwards [observationLaw_covariate_ae M _ (hp a)] with o ho
    have ht : 0 < positiveValue (eta0Bin M L).piLev i o.1 := by
      simpa only [positiveValue, dif_pos hi, eta0Bin] using
        hov.1.trans_le (hov.2 o.1 i hi.1 hi.2)
    have hf : 0 < pi a o.1 := hc.trans_le ho
    dsimp only [Function.comp_apply, w]
    simp only [Rp, if_neg (show i ≠ 0 by omega), positiveValue, dif_pos hi]
    simp only [positiveValue, dif_pos hi] at ht
    change 0 < pi ⟨i, hi⟩ o.1 at hf
    dsimp only [a]
    field_simp [ne_of_gt ht, ne_of_gt hf]
  · have hz : Rp L {eta0Bin M L with piLev := pi} i = fun _ => (0 : ℝ) := by
      funext o
      by_cases hi0 : i = 0 <;> simp [Rp, hi0, positiveValue, hi]
    rw [hz]
    exact integrable_zero _ _ _

-- The population treatment residual stays centered. The remaining term is the
-- fitted regression error times the true assignment mass over its fitted mass.
-- @node: population_Rp_joint_fitted_weighted_mean
/-- Under [threshold crossing](hyp:h), [invariance of the level order between the true
propensity and the comparison propensity](hyp:hOrder), [baseline assignment overlap](hyp:hov),
and [admissibility of the true binary nuisance](hyp:he), suppose [the fitted treatment
regressions](hyp:hP) and [assignment denominators](hyp:hpi) are measurable, [the denominator
lower bound is positive](hyp:hc), [all fitted denominators exceed it almost
everywhere](hyp:hclip), and [the fitted regressions are uniformly bounded in absolute
value almost everywhere](hyp:hPB). For [a measurable covariate weight](hyp:hw) that [is
almost everywhere bounded in absolute value](hyp:hwB), [both the weighted fitted treatment
residual and the weight times the true assignment mass times the true-minus-fitted
regression divided by the fitted assignment mass are integrable, and their population
means coincide](goal). -/
lemma population_Rp_joint_fitted_weighted_mean
    (h : ThresholdCrossing M) (q : Z → X → ℝ)
    (L : LevelData Z X) (hOrder : LevelOrderInvariant M.prop q L) (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (he : BinAdmissible M L (eta0Bin M L))
    (P pi : PositiveIndex L.K → X → ℝ)
    (hP : ∀ a, Measurable (P a)) (hpi : ∀ a, Measurable (pi a))
    (c D : ℝ) (hc : 0 < c) (hclip : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ pi a x)
    (hPB : ∀ a, ∀ᵐ x ∂xLaw M, ‖P a x‖ ≤ D)
    (w : X → ℝ) (hw : Measurable w) (B : ℝ)
    (hwB : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ B) (i : ℕ) :
    Integrable (fun o : Obs X Z => w o.1 *
      Rp L {eta0Bin M L with pLev := P, piLev := pi} i o) (observationLaw M) ∧
    Integrable (fun o : Obs X Z => w o.1 * positiveValue (eta0Bin M L).piLev i o.1 *
      (positiveValue (eta0Bin M L).pLev i o.1 - positiveValue P i o.1) /
        positiveValue pi i o.1) (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 * Rp L {eta0Bin M L with pLev := P, piLev := pi} i o
      ∂observationLaw M) =
      ∫ o : Obs X Z, w o.1 * positiveValue (eta0Bin M L).piLev i o.1 *
        (positiveValue (eta0Bin M L).pLev i o.1 - positiveValue P i o.1) /
          positiveValue pi i o.1 ∂observationLaw M := by
  by_cases hi : 1 ≤ i ∧ i ≤ L.K
  · let a : PositiveIndex L.K := ⟨i, hi⟩
    let v : X → ℝ := fun x => w x * ((eta0Bin M L).pLev a x - P a x)
    have hv : Measurable v := hw.mul (((he.2.2.2.1 a).1).sub (hP a))
    have hvB : ∀ᵐ x ∂xLaw M, ‖v x‖ ≤ B * (1+D) := by
      filter_upwards [hwB, hPB a, he.2.2.1 a] with x hx hp ht
      have htB : ‖(eta0Bin M L).pLev a x‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg ht.1.1]
        exact ht.1.2
      calc
        _ = ‖w x‖ * ‖(eta0Bin M L).pLev a x - P a x‖ := norm_mul _ _
        _ ≤ B * (1+D) := mul_le_mul hx
          ((norm_sub_le _ _).trans (add_le_add htB hp)) (norm_nonneg _)
          ((norm_nonneg _).trans hx)
    obtain ⟨iz, im, hz⟩ := population_fitted_assignment_weighted_mean M (L.S i)
      (pi a) v (hpi a) hv c (B*(1+D)) hc (hclip a) hvB
    have ir := (population_binary_Rp_fitted_denominator_integrable M L cpi hov he
      pi hpi c hc hclip i).bdd_mul (hw.comp measurable_fst).aestronglyMeasurable
        (observationLaw_covariate_ae M _ hwB)
    change Integrable (fun o : Obs X Z => w o.1 *
      Rp L {eta0Bin M L with piLev := pi} i o) (observationLaw M) at ir
    have zr := population_Rp_denominator_weighted_integral_zero M h q L pi hpi hOrder i w hw ir
    have hid : (fun o : Obs X Z => w o.1 *
        Rp L {eta0Bin M L with pLev := P, piLev := pi} i o) =
        (fun o => w o.1 * Rp L {eta0Bin M L with piLev := pi} i o +
          v o.1 * indicator (o.2.1 ∈ L.S i) / pi a o.1) := by
      funext o
      simp only [Rp, if_neg (show i ≠ 0 by omega), positiveValue, dif_pos hi, v, a]
      ring
    constructor
    · change Integrable (fun o => w o.1 * Rp L _ i o) _
      rw [hid]
      exact ir.fun_add iz
    · have hmean : (fun o : Obs X Z => v o.1 * (∑ z ∈ L.S i, instProb M z o.1) / pi a o.1) =
          (fun o : Obs X Z => w o.1 * positiveValue (eta0Bin M L).piLev i o.1 *
            (positiveValue (eta0Bin M L).pLev i o.1 - positiveValue P i o.1) /
              positiveValue pi i o.1) := by
        funext o
        simp only [positiveValue, dif_pos hi, eta0Bin, levelSetProb, v, a]
        ring
      constructor
      · rwa [← hmean]
      · rw [hid, integral_add ir iz, zr, zero_add, hz, hmean]
  · have hz : ∀ o : Obs X Z, w o.1 *
        Rp L {eta0Bin M L with pLev := P, piLev := pi} i o = 0 := by
      intro o
      by_cases hi0 : i = 0 <;> simp [Rp, hi0, positiveValue, hi]
    simp only [hz, positiveValue, dif_neg hi, mul_zero, sub_self, zero_div, integral_zero]
    exact ⟨integrable_zero _ _ _, integrable_zero _ _ _, True.intro⟩

-- The residual depends only on its regression and assignment denominator,
-- so the identity applies to the entire fitted nuisance vector.
-- @node: population_RP_weighted_mean_of_binary_admissible
/-- Assume [baseline assignment overlap](hyp:hov), [an almost surely binary outcome](hyp:hy),
[admissibility of the true binary nuisance](hyp:he0), and [admissibility of the fitted
binary nuisance](hyp:he). If [the denominator lower bound is positive](hyp:hc), [every
fitted assignment denominator exceeds it almost everywhere](hyp:hden), and [the covariate
weight is measurable](hyp:hw) and [almost everywhere bounded in absolute value](hyp:hwB),
[the weighted fitted treated-outcome residual and the weight times the true assignment mass times
the true-minus-fitted treated-outcome regression divided by the fitted assignment mass are both
integrable and have equal population means](goal). -/
lemma population_RP_weighted_mean_of_binary_admissible
    (L : LevelData Z X) (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hy : OutcomeBinaryAE M)
    (he0 : BinAdmissible M L (eta0Bin M L))
    (e : NuisanceBin L) (he : BinAdmissible M L e)
    (c : ℝ) (hc : 0 < c) (hden : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ e.piLev a x)
    (w : X → ℝ) (hw : Measurable w) (B : ℝ)
    (hwB : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ B) (i : ℕ) :
    Integrable (fun o : Obs X Z => w o.1 * RP L e i o) (observationLaw M) ∧
    Integrable (fun o : Obs X Z => w o.1 * positiveValue (eta0Bin M L).piLev i o.1 *
      (positiveValue (eta0Bin M L).P1 i o.1 - positiveValue e.P1 i o.1) /
        positiveValue e.piLev i o.1) (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 * RP L e i o ∂observationLaw M) =
      ∫ o : Obs X Z, w o.1 * positiveValue (eta0Bin M L).piLev i o.1 *
        (positiveValue (eta0Bin M L).P1 i o.1 - positiveValue e.P1 i o.1) /
          positiveValue e.piLev i o.1 ∂observationLaw M := by
  have hb : ∀ a, ∀ᵐ x ∂xLaw M, ‖e.P1 a x‖ ≤ 1 := by
    intro a
    filter_upwards [he.2.2.1 a] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx.2.1.1]
    exact hx.2.1.2
  have hm := population_RP_joint_fitted_weighted_mean M L cpi hov hy he0
    e.P1 e.piLev (fun a => (he.2.2.2.1 a).2.1)
    (fun a => (he.2.2.2.1 a).2.2) c 1 hc hden hb w hw B hwB i
  have heq : RP L {eta0Bin M L with P1 := e.P1, piLev := e.piLev} i =
      RP L e i := rfl
  simpa only [heq] using hm

-- The residual depends only on its regression and assignment denominator,
-- so the identity applies to the entire fitted nuisance vector.
-- @node: population_Rp_weighted_mean_of_binary_admissible
/-- Assume [baseline assignment overlap](hyp:hov), [threshold crossing](hyp:h),
[invariance of the level order between the true and comparison propensities](hyp:hOrder),
[admissibility of the true binary nuisance](hyp:he0), and [admissibility of the fitted
binary nuisance](hyp:he). If [the denominator lower bound is positive](hyp:hc), [every
fitted assignment denominator exceeds it almost everywhere](hyp:hden), and [the covariate
weight is measurable](hyp:hw) and [almost everywhere bounded in absolute value](hyp:hwB),
[the weighted fitted treatment residual and the weight times the true assignment mass
times the true-minus-fitted treatment regression divided by the fitted assignment mass
are both integrable and have equal population means](goal). -/
lemma population_Rp_weighted_mean_of_binary_admissible
    (L : LevelData Z X) (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (h : ThresholdCrossing M) (q : Z → X → ℝ)
    (hOrder : LevelOrderInvariant M.prop q L)
    (he0 : BinAdmissible M L (eta0Bin M L))
    (e : NuisanceBin L) (he : BinAdmissible M L e)
    (c : ℝ) (hc : 0 < c) (hden : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ e.piLev a x)
    (w : X → ℝ) (hw : Measurable w) (B : ℝ)
    (hwB : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ B) (i : ℕ) :
    Integrable (fun o : Obs X Z => w o.1 * Rp L e i o) (observationLaw M) ∧
    Integrable (fun o : Obs X Z => w o.1 * positiveValue (eta0Bin M L).piLev i o.1 *
      (positiveValue (eta0Bin M L).pLev i o.1 - positiveValue e.pLev i o.1) /
        positiveValue e.piLev i o.1) (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 * Rp L e i o ∂observationLaw M) =
      ∫ o : Obs X Z, w o.1 * positiveValue (eta0Bin M L).piLev i o.1 *
        (positiveValue (eta0Bin M L).pLev i o.1 - positiveValue e.pLev i o.1) /
          positiveValue e.piLev i o.1 ∂observationLaw M := by
  have hb : ∀ a, ∀ᵐ x ∂xLaw M, ‖e.pLev a x‖ ≤ 1 := by
    intro a
    filter_upwards [he.2.2.1 a] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx.1.1]
    exact hx.1.2
  have hm := population_Rp_joint_fitted_weighted_mean M h q L hOrder cpi hov he0
    e.pLev e.piLev (fun a => (he.2.2.2.1 a).1)
    (fun a => (he.2.2.2.1 a).2.2) c 1 hc hden hb w hw B hwB i
  have heq : Rp L {eta0Bin M L with pLev := e.pLev, piLev := e.piLev} i =
      Rp L e i := rfl
  simpa only [heq] using hm

-- All positive assignment levels retain overlap on one uniform time neighborhood.
-- @node: binary_assignment_denominators_uniform_neighborhood
/-- Given [baseline assignment overlap with a positive common lower bound](hyp:hov) and
[an admissible direction at the true binary nuisance](hyp:hd), [throughout some neighborhood
of zero path displacement, every positive-level fitted assignment denominator is almost
everywhere at least half the baseline lower bound](goal). -/
lemma binary_assignment_denominators_uniform_neighborhood
    (L : LevelData Z X) (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del)) :
    ∀ᶠ t : ℝ in nhds 0, ∀ a, ∀ᵐ x ∂xLaw M,
      cpi/2 ≤ (eta0Bin M L + t • del).piLev a x := by
  obtain ⟨C, hC, hb⟩ := binary_assignment_denominator_direction_regular M L
    (eta0Bin M L) del hd
  have hcpi := hov.1
  have radius : 0 < cpi / (2*(C+1)) := by positivity
  filter_upwards [continuousAt_id.abs.eventually_lt_const (by simpa using radius)] with t ht
  change |t| < cpi / (2*(C+1)) at ht
  intro a
  filter_upwards [(hb a).2] with x hx
  simp only [Real.norm_eq_abs] at hx
  have hmul : |t * del.piLev a x| ≤ |t| * C := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg t)
  have hsmall := (lt_div_iff₀ (by positivity : 0 < 2*(C+1))).mp ht
  have htrue := hov.2 x a.val a.property.1 a.property.2
  change cpi ≤ (eta0Bin M L).piLev a x at htrue
  change cpi/2 ≤ (eta0Bin M L).piLev a x + t * del.piLev a x
  nlinarith [neg_abs_le (t * del.piLev a x), abs_nonneg t]

-- Moving branch and product weights may be used here. No independence between
-- their nuisance directions and the regression/denominator directions is needed.
-- @node: population_binary_weighted_residual_path_local_mean
/-- Suppose [threshold crossing holds](hyp:h), [the true and comparison propensities induce
the same level order](hyp:hOrder), [baseline assignment overlap holds](hyp:hov), [the outcome
is almost surely binary](hyp:hy), and [the binary nuisance direction is admissible at the
truth](hyp:hd). For [covariate weights measurable at each path displacement](hyp:hw) and
[uniformly bounded in absolute value almost everywhere](hyp:hwB), [throughout a neighborhood
of zero and at every level, the weighted fitted treated-outcome and treatment residuals and their
respective weighted true-assignment-mass times true-minus-fitted-regression ratios are
integrable, and each residual's population mean equals the mean of its corresponding
ratio](goal). -/
lemma population_binary_weighted_residual_path_local_mean
    (h : ThresholdCrossing M) (q : Z → X → ℝ)
    (L : LevelData Z X) (hOrder : LevelOrderInvariant M.prop q L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hy : OutcomeBinaryAE M)
    (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del))
    (w : ℝ → X → ℝ) (hw : ∀ t, Measurable (w t)) (B : ℝ)
    (hwB : ∀ t, ∀ᵐ x ∂xLaw M, ‖w t x‖ ≤ B) :
    ∀ᶠ t : ℝ in nhds 0, ∀ i,
      Integrable (fun o : Obs X Z => w t o.1 * RP L (eta0Bin M L + t • del) i o)
        (observationLaw M) ∧
      Integrable (fun o : Obs X Z => w t o.1 * Rp L (eta0Bin M L + t • del) i o)
        (observationLaw M) ∧
      Integrable (fun o : Obs X Z => w t o.1 * positiveValue (eta0Bin M L).piLev i o.1 *
        (positiveValue (eta0Bin M L).P1 i o.1 -
          positiveValue (eta0Bin M L + t • del).P1 i o.1) /
            positiveValue (eta0Bin M L + t • del).piLev i o.1) (observationLaw M) ∧
      Integrable (fun o : Obs X Z => w t o.1 * positiveValue (eta0Bin M L).piLev i o.1 *
        (positiveValue (eta0Bin M L).pLev i o.1 -
          positiveValue (eta0Bin M L + t • del).pLev i o.1) /
            positiveValue (eta0Bin M L + t • del).piLev i o.1) (observationLaw M) ∧
      (∫ o : Obs X Z, w t o.1 * RP L (eta0Bin M L + t • del) i o
        ∂observationLaw M) =
        (∫ o : Obs X Z, w t o.1 * positiveValue (eta0Bin M L).piLev i o.1 *
          (positiveValue (eta0Bin M L).P1 i o.1 -
            positiveValue (eta0Bin M L + t • del).P1 i o.1) /
              positiveValue (eta0Bin M L + t • del).piLev i o.1 ∂observationLaw M) ∧
      (∫ o : Obs X Z, w t o.1 * Rp L (eta0Bin M L + t • del) i o
        ∂observationLaw M) =
        (∫ o : Obs X Z, w t o.1 * positiveValue (eta0Bin M L).piLev i o.1 *
          (positiveValue (eta0Bin M L).pLev i o.1 -
            positiveValue (eta0Bin M L + t • del).pLev i o.1) /
              positiveValue (eta0Bin M L + t • del).piLev i o.1 ∂observationLaw M) := by
  have he0 := binary_admissible_direction_origin M L (eta0Bin M L) del hd
  obtain ⟨r, hr, hadm⟩ := hd.admissible
  filter_upwards [continuousAt_id.abs.eventually_lt_const (by simpa using hr),
    binary_assignment_denominators_uniform_neighborhood M L cpi hov del hd] with t ht hden
  intro i
  have he := hadm t ht
  have hc : 0 < cpi/2 := by have := hov.1; positivity
  have hP := population_RP_weighted_mean_of_binary_admissible M L cpi hov hy he0
    (eta0Bin M L + t • del) he (cpi/2) hc hden (w t) (hw t) B (hwB t) i
  have hp := population_Rp_weighted_mean_of_binary_admissible M L cpi hov h q hOrder he0
    (eta0Bin M L + t • del) he (cpi/2) hc hden (w t) (hw t) B (hwB t) i
  exact ⟨hP.1, hp.1, hP.2.1, hp.2.1, hP.2.2, hp.2.2⟩

end Papers.TbsPrteOptimalTransport
