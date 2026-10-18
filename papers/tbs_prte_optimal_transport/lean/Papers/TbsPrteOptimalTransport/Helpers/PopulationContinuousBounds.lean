module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationContinuousBandMean
public import Papers.TbsPrteOptimalTransport.Helpers.LIVPart
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousLearners
/-! Outcome envelopes for the constructed continuous selected regressions. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical

-- Zero-mass selected cells have average zero, so no positivity is needed.
-- @node: selected_average_norm_le_of_bound
/-- For a finite measure, if [the bound is nonnegative](hyp:hC) and
[the absolute value of the integrand is at most that bound almost everywhere](hyp:hg),
[the absolute value of its normalized average is at most the same bound](goal). -/
lemma selected_average_norm_le_of_bound {B : Type*} [MeasurableSpace B]
    (mu : Measure B) [IsFiniteMeasure mu] (g : B → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ᵐ a ∂mu, ‖g a‖ ≤ C) : ‖⨍ a, g a ∂mu‖ ≤ C := by
  rw [average_eq, smul_eq_mul, norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (measureReal_nonneg)), ← div_eq_inv_mul]
  by_cases hz : mu.real univ = 0
  · simpa only [hz, div_zero] using hC
  · apply (div_le_iff₀ (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hz))).mpr
    exact norm_integral_le_of_norm_le_const hg

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: population_selected_integral_norm_bound
/-- Under [the structural assumptions](hyp:h), if [the outcome function is measurable
at every covariate](hyp:hg) and [its absolute value on the outcome support is bounded
by the model's outcome magnitude](hyp:hb), [its integral under the selected treated-outcome
law has absolute value at most that magnitude for almost every covariate](goal). -/
lemma population_selected_integral_norm_bound
    (h : StructuralAssumptions M)
    (L : LevelData Z X) (i : ℕ) (g : X → ℝ → ℝ)
    (hg : ∀ x, Measurable (g x))
    (hb : ∀ x y, y ∈ M.Yset → ‖g x y‖ ≤ outcomeMagnitude M) :
    ∀ᵐ x ∂xLaw M, ‖∫ y, g x y ∂treatedLaw M L i x‖ ≤ outcomeMagnitude M := by
  filter_upwards [conditional_observed_outcome_supported M h] with x hx
  let joint := condDistrib (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure x
  let sel := joint.restrict {a : ℝ × ℝ × Z | a.2.1 = 1 ∧ a.2.2 ∈ (L.S i : Set Z)}
  have hs : ∀ᵐ a ∂joint, a.1 ∈ M.Yset := ae_iff.mpr hx
  have hb' : ∀ᵐ a ∂sel, ‖g x a.1‖ ≤ outcomeMagnitude M :=
    (hs.filter_mono (ae_mono Measure.restrict_le_self)).mono fun a ha => hb x a.1 ha
  unfold treatedLaw
  rw [normalized_selected_mean_eq_average _ _ _ (hg x)]
  exact selected_average_norm_le_of_bound sel (fun a => g x a.1) (outcomeMagnitude M)
    ((abs_nonneg M.yMin).trans (le_max_left _ _)) hb'

-- The envelope also applies to truncated first moments and the structural zero.
-- @node: population_treatedBandMean_norm_bound
/-- Under [the structural assumptions](hyp:h) and [known outcome endpoints](hyp:he),
[every treated-outcome mean, whether for a band or the full outcome range and on
either side, has absolute value bounded by the model's outcome magnitude for almost every covariate](goal). -/
lemma population_treatedBandMean_norm_bound
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (L : LevelData Z X) (plus full : Bool) (k j : ℕ) :
    ∀ᵐ x ∂xLaw M, ‖treatedBandMean M L plus full k j x‖ ≤ outcomeMagnitude M := by
  have hC : 0 ≤ outcomeMagnitude M := (abs_nonneg M.yMin).trans (le_max_left _ _)
  by_cases hz : (!plus && k == 0) = true
  · simp only [treatedBandMean, if_pos hz, norm_zero]
    exact Eventually.of_forall (fun _ => hC)
  cases full
  · let g : X → ℝ → ℝ := fun x y => y * indicator
      (bandBoundary M L k j x < y ∧ y ≤ bandBoundary M L k (j + 1) x)
    have hg (x : X) : Measurable (g x) := by
      dsimp only [g, indicator]
      exact measurable_id.mul (Measurable.ite measurableSet_Ioc measurable_const measurable_const)
    have hb x y (hy : y ∈ M.Yset) : ‖g x y‖ ≤ outcomeMagnitude M := by
      dsimp only [g, indicator]
      split_ifs
      · simpa using outcome_norm_le_magnitude M he hy
      · simpa using hC
    have hi := population_selected_integral_norm_bound M h L
      (if plus then k + 1 else k) g hg hb
    simpa only [g, treatedBandMean, if_neg hz, Bool.false_eq_true, if_false,
      continuous_band_indicator_integral_eq] using hi
  · simpa only [treatedBandMean, if_neg hz, Bool.true_eq, if_true] using
      population_selected_integral_norm_bound M h L (if plus then k + 1 else k)
        (fun _ y => y) (fun _ => measurable_id) (fun _ _ hy => outcome_norm_le_magnitude M he hy)

-- Integrability is derived from an integrable covariate weight, the compact
-- outcome envelope, and a positive denominator bound, including fitted weights.
-- @node: population_selected_treatment_residual_integrable
/-- Under [the structural assumptions](hyp:h), for [a jointly measurable outcome
function](hyp:hg) [bounded in absolute value on the outcome support by the model's
outcome magnitude](hyp:hb), [a measurable denominator](hyp:hc) with
[a positive lower bound](hyp:hc0) [holding almost everywhere](hyp:hcl), and
[a measurable covariate weight](hyp:hw) [integrable under the covariate law](hyp:hwi),
[the weighted treated-outcome residual, centered by its selected treated-law mean
and multiplied by the selected-class and treatment indicators divided by the denominator,
is integrable under the observation law](goal). -/
lemma population_selected_treatment_residual_integrable
    (h : StructuralAssumptions M) (L : LevelData Z X) (i : ℕ)
    (g : X → ℝ → ℝ) (hg : Measurable (Function.uncurry g))
    (hb : ∀ x y, y ∈ M.Yset → ‖g x y‖ ≤ outcomeMagnitude M)
    (c : X → ℝ) (hc : Measurable c) (c0 : ℝ) (hc0 : 0 < c0)
    (hcl : ∀ᵐ x ∂xLaw M, c0 ≤ c x)
    (w : X → ℝ) (hw : Measurable w) (hwi : Integrable w (xLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 *
      (indicator (o.2.1 ∈ L.S i) * o.2.2.1 / c o.1 *
        (g o.1 o.2.2.2 - ∫ y, g o.1 y ∂treatedLaw M L i o.1))) (observationLaw M) := by
  let r : Obs X Z → ℝ := fun o => indicator (o.2.1 ∈ L.S i) * o.2.2.1 / c o.1 *
    (g o.1 o.2.2.2 - ∫ y, g o.1 y ∂treatedLaw M L i o.1)
  have hm : Measurable r := by
    dsimp only [r]
    have hmean := population_treated_integral_measurable M L i g hg
    have hi : Measurable (fun o : Obs X Z => indicator (o.2.1 ∈ L.S i)) := by
      unfold indicator
      exact Measurable.ite ((L.S i).finite_toSet.measurableSet.preimage measurable_snd.fst)
        measurable_const measurable_const
    exact ((hi.mul measurable_snd.snd.fst).div (hc.comp measurable_fst)).mul
      ((hg.comp (measurable_fst.prodMk measurable_snd.snd.snd)).sub
        (hmean.comp measurable_fst))
  have hobs := M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
  have hmap : (observationLaw M).map Prod.fst = xLaw M := by
    simpa only [observationLaw, xLaw, Function.comp_def] using Measure.map_map measurable_fst hobs
  have hwi' : Integrable (fun o : Obs X Z => w o.1) (observationLaw M) := by
    apply (integrable_map_measure hw.aestronglyMeasurable measurable_fst.aemeasurable).mp
    rwa [hmap]
  have hy : ∀ᵐ o : Obs X Z ∂observationLaw M, o.2.2.2 ∈ M.Yset := by
    apply (ae_map_iff hobs.aemeasurable
      (h.2.2.2.2.2.2.1.measurableSet.preimage measurable_snd.snd.snd)).mpr
    exact observed_outcome_supported M h
  have ht : ∀ᵐ o : Obs X Z ∂observationLaw M, ‖o.2.2.1‖ ≤ 1 := by
    apply (ae_map_iff hobs.aemeasurable
      (measurableSet_le (by fun_prop) measurable_const)).mpr
    exact Eventually.of_forall (fun s => by rcases M.rangeW s with hs | hs <;> simp [hs])
  have hmean := population_selected_integral_norm_bound M h L i g (fun _ => hg.of_uncurry_left) hb
  have hr : ∀ᵐ o : Obs X Z ∂observationLaw M,
      ‖r o‖ ≤ (2 * outcomeMagnitude M) / c0 := by
    filter_upwards [hy, ht, observationLaw_covariate_ae M _ hcl,
      observationLaw_covariate_ae M _ hmean] with o hyo hto hco hmo
    have hi : ‖indicator (o.2.1 ∈ L.S i)‖ ≤ 1 := by
      unfold indicator
      split_ifs <;> norm_num
    have hcpos : 0 < c o.1 := hc0.trans_le hco
    have hn : ‖g o.1 o.2.2.2 - ∫ y, g o.1 y ∂treatedLaw M L i o.1‖ ≤
        2 * outcomeMagnitude M := by
      exact (norm_sub_le _ _).trans (by linarith [hb o.1 o.2.2.2 hyo])
    calc
      ‖r o‖ = (‖indicator (o.2.1 ∈ L.S i)‖ * ‖o.2.2.1‖) / c o.1 *
        ‖g o.1 o.2.2.2 - ∫ y, g o.1 y ∂treatedLaw M L i o.1‖ := by
          simp only [r, norm_mul, norm_div, Real.norm_eq_abs, abs_of_pos hcpos]
      _ ≤ (1 * 1) / c0 * (2 * outcomeMagnitude M) := by
        gcongr
      _ = (2 * outcomeMagnitude M) / c0 := by ring
  simpa only [r, mul_comm] using hwi'.bdd_mul hm.aestronglyMeasurable hr

-- @node: population_selected_treatment_weighted_centering_of_bound
/-- Under [the structural assumptions](hyp:h), if [the outcome function is jointly
measurable](hyp:hg) and [bounded on the outcome support by the model's outcome
magnitude in absolute value](hyp:hb), [the denominator is measurable](hyp:hc),
[its lower bound is positive](hyp:hc0) and [holds almost everywhere](hyp:hcl), and
[the covariate weight is measurable](hyp:hw) and [integrable](hyp:hwi),
[the population expectation of the weighted selected-class treatment residual,
divided by that denominator and centered at its selected treated-law mean, is zero](goal). -/
lemma population_selected_treatment_weighted_centering_of_bound
    (h : StructuralAssumptions M) (L : LevelData Z X) (i : ℕ)
    (g : X → ℝ → ℝ) (hg : Measurable (Function.uncurry g))
    (hb : ∀ x y, y ∈ M.Yset → ‖g x y‖ ≤ outcomeMagnitude M)
    (c : X → ℝ) (hc : Measurable c) (c0 : ℝ) (hc0 : 0 < c0)
    (hcl : ∀ᵐ x ∂xLaw M, c0 ≤ c x)
    (w : X → ℝ) (hw : Measurable w) (hwi : Integrable w (xLaw M)) :
    (∫ o : Obs X Z, w o.1 *
      (indicator (o.2.1 ∈ L.S i) * o.2.2.1 / c o.1 *
        (g o.1 o.2.2.2 - ∫ y, g o.1 y ∂treatedLaw M L i o.1))
      ∂observationLaw M) = 0 := by
  exact population_selected_treatment_weighted_integral_zero M L i g hg c w hc hw
    (population_selected_treatment_residual_integrable M h L i g hg hb c hc c0 hc0 hcl w hw hwi)

-- @node: population_IFJ_fitted_denominator_integrable
/-- Under [the structural assumptions](hyp:h) and [known outcome endpoints](hyp:he),
if [fitted baseline-class probability denominators are measurable](hyp:hpi) and
[have a positive common lower bound](hyp:hc0) [almost everywhere for every class](hyp:hcl),
then for [a nonfinal bin](hyp:hk), [a band index below its policy-level count](hyp:hj),
[measurable lower](hyp:ha) and [upper boundaries](hyp:hb), and
[a measurable](hyp:hw), [integrable covariate weight](hyp:hwi),
[the weighted treated-band residual with the fitted denominators is integrable on either selected side](goal). -/
lemma population_IFJ_fitted_denominator_integrable
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M) (L : LevelData Z X)
    (pi : PositiveIndex L.K → X → ℝ) (hpi : ∀ a, Measurable (pi a))
    (c0 : ℝ) (hc0 : 0 < c0) (hcl : ∀ a, ∀ᵐ x ∂xLaw M, c0 ≤ pi a x)
    (plus : Bool) (k j : ℕ) (hk : k < L.K) (hj : j < L.l k)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j + 1)))
    (w : X → ℝ) (hw : Measurable w) (hwi : Integrable w (xLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 *
      IFJ M L {trueNuisance M L with piLev := pi} plus k j o) (observationLaw M) := by
  let g : X → ℝ → ℝ := fun x y => y *
    indicator (bandBoundary M L k j x < y ∧ y ≤ bandBoundary M L k (j + 1) x)
  have hg : Measurable (Function.uncurry g) := by fun_prop
  have hgb x y (hy : y ∈ M.Yset) : ‖g x y‖ ≤ outcomeMagnitude M := by
    dsimp only [g, indicator]
    split_ifs
    · simpa using outcome_norm_le_magnitude M he hy
    · have hC : 0 ≤ outcomeMagnitude M := (abs_nonneg M.yMin).trans (le_max_left _ _)
      simpa using hC
  have hc i : Measurable (positiveValue pi i) := by
    first | fun_prop | skip
    unfold positiveValue
    split_ifs
    · exact hpi _
    · fun_prop
  have hcb i (hi : 1 ≤ i ∧ i ≤ L.K) :
      ∀ᵐ x ∂xLaw M, c0 ≤ positiveValue pi i x := by
    simpa only [positiveValue, dif_pos hi] using hcl ⟨i, hi⟩
  have hmean i x := continuous_band_indicator_integral_eq M L i k j x
  have hnu b (hbl : b ≤ L.l k) x :
      nuValue M {trueNuisance M L with piLev := pi} k b x = bandBoundary M L k b x :=
    population_nuValue_eq_bandBoundary M L k b hk hbl x
  cases plus
  · by_cases hk0 : k = 0
    · subst k
      simp [IFJ]
    have hk1 : 1 ≤ k := by omega
    have heq : ∀ o : Obs X Z,
        IFJ M L {trueNuisance M L with piLev := pi} false k j o =
        indicator (o.2.1 ∈ L.S k) * o.2.2.1 / positiveValue pi k o.1 *
          (g o.1 o.2.2.2 - ∫ y, g o.1 y ∂treatedLaw M L k o.1) := by
      intro o
      simp only [IFJ, Bool.not_false, Bool.true_and, Bool.false_eq_true,
        beq_iff_eq, hk0, if_false, hnu j hj.le o.1, hnu (j + 1) (by omega) o.1]
      simp [g, hmean, minusMeanValue, hk1, hk, hj.le, trueNuisance, treatedBandMean, hk0]
    simp_rw [heq]
    exact population_selected_treatment_residual_integrable M h L k g hg hgb _ (hc k)
      c0 hc0 (hcb k ⟨hk1, hk.le⟩) w hw hwi
  · have heq : ∀ o : Obs X Z,
        IFJ M L {trueNuisance M L with piLev := pi} true k j o =
        indicator (o.2.1 ∈ L.S (k + 1)) * o.2.2.1 / positiveValue pi (k + 1) o.1 *
          (g o.1 o.2.2.2 - ∫ y, g o.1 y ∂treatedLaw M L (k + 1) o.1) := by
      intro o
      simp only [IFJ, Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false,
        if_true, hnu j hj.le o.1, hnu (j + 1) (by omega) o.1]
      simp [g, hmean, meanValue, hk, hj.le, trueNuisance, treatedBandMean]
    simp_rw [heq]
    exact population_selected_treatment_residual_integrable M h L (k + 1) g hg hgb _
      (hc (k + 1)) c0 hc0 (hcb (k + 1) ⟨by omega, by omega⟩) w hw hwi

-- @node: population_IFJ_weighted_centering_of_clipped_denominator
/-- Under [the structural assumptions](hyp:h) and [known outcome endpoints](hyp:he),
with [measurable fitted baseline-class probability denominators](hyp:hpi),
[a positive common lower bound](hyp:hc0) [valid almost everywhere for every class](hyp:hcl),
[a nonfinal bin](hyp:hk), [a band index below its policy-level count](hyp:hj),
[measurable lower](hyp:ha) and [upper band boundaries](hyp:hb), and
[a measurable](hyp:hw), [integrable covariate weight](hyp:hwi),
[the weighted treated-band residual using these denominators has population expectation zero on either selected side](goal). -/
lemma population_IFJ_weighted_centering_of_clipped_denominator
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M) (L : LevelData Z X)
    (pi : PositiveIndex L.K → X → ℝ) (hpi : ∀ a, Measurable (pi a))
    (c0 : ℝ) (hc0 : 0 < c0) (hcl : ∀ a, ∀ᵐ x ∂xLaw M, c0 ≤ pi a x)
    (plus : Bool) (k j : ℕ) (hk : k < L.K) (hj : j < L.l k)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j + 1)))
    (w : X → ℝ) (hw : Measurable w) (hwi : Integrable w (xLaw M)) :
    (∫ o : Obs X Z, w o.1 * IFJ M L {trueNuisance M L with piLev := pi}
      plus k j o ∂observationLaw M) = 0 := by
  exact population_IFJ_fitted_denominator_weighted_zero M L pi hpi plus k j hk hj ha hb w hw
    (population_IFJ_fitted_denominator_integrable M h he L pi hpi c0 hc0 hcl
      plus k j hk hj ha hb w hw hwi)

end Papers.TbsPrteOptimalTransport
