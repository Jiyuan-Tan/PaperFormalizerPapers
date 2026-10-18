module
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousPropensityBounds
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationContinuousFullProducts
/-! Compact outcome and overlap bounds for continuous full-interval moments. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: population_continuous_full_mean_norm_bound
/-- Under the [structural assumptions](hyp:h) and [known outcome endpoints](hyp:he),
[the absolute population full-interval outcome mean on either side of any treatment interval is almost surely at most the maximum absolute outcome endpoint](goal). -/
lemma population_continuous_full_mean_norm_bound
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (L : LevelData Z X) (plus : Bool) (k : ℕ) :
    ∀ᵐ x ∂xLaw M,
      ‖(if plus then fullValue (trueNuisance M L).JfullPlus k x
        else minusFullValue (trueNuisance M L) k x)‖ ≤ outcomeMagnitude M := by
  have hC : 0 ≤ outcomeMagnitude M := (abs_nonneg M.yMin).trans (le_max_left _ _)
  filter_upwards [population_treatedBandMean_norm_bound M h he L plus true k 0]
    with x hx
  cases plus
  · simp only [Bool.false_eq_true, if_false]
    unfold minusFullValue
    split_ifs
    · exact hx
    · simpa using hC
  · simp only [Bool.true_eq, if_true]
    unfold fullValue
    split_ifs
    · exact hx
    · simpa using hC

-- @node: population_continuous_full_mean_weight_integrable
/-- Under the [structural assumptions](hyp:h) and [known outcome endpoints](hyp:he),
if [the covariate weight is integrable](hyp:hwi),
[its product with the population full-interval outcome mean on either side is integrable under the covariate distribution](goal). -/
lemma population_continuous_full_mean_weight_integrable
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (L : LevelData Z X) (plus : Bool) (k : ℕ)
    (w : X → ℝ) (hwi : Integrable w (xLaw M)) :
    Integrable (fun x => w x * (if plus then fullValue (trueNuisance M L).JfullPlus k x
      else minusFullValue (trueNuisance M L) k x)) (xLaw M) := by
  simpa only [mul_comm] using hwi.bdd_mul
    (population_continuous_full_mean_measurable M L plus k).aestronglyMeasurable
    (population_continuous_full_mean_norm_bound M h he L plus k)

-- @node: population_contFullJ_norm_bound
/-- Under the [structural assumptions](hyp:h), [known outcome endpoints](hyp:he), and
[invariant level ordering](hyp:hL), [the absolute population full-interval outcome contrast is almost surely at most twice the maximum absolute outcome endpoint](goal). -/
lemma population_contFullJ_norm_bound
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (k : ℕ) :
    ∀ᵐ x ∂xLaw M, ‖contFullJ L (trueNuisance M L) k x‖ ≤ 2 * outcomeMagnitude M := by
  have hr := (canonical_level_ranges M.prop q L
    (fun z x => (hL.2.2.2.2.2.2.2.2.2.1 z x).1)
    (fun z x => (hL.2.2.2.2.2.2.2.2.2.1 z x).2) hL).1
  have hp i x : ‖positiveValue (trueNuisance M L).pLev i x‖ ≤ 1 := by
    unfold positiveValue
    split_ifs with hi
    · change ‖L.pLev i x‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (hr x i (by omega)).1]
      exact (hr x i (by omega)).2
    · norm_num
  filter_upwards [population_continuous_full_mean_norm_bound M h he L true k,
    population_continuous_full_mean_norm_bound M h he L false k] with x hplus hminus
  simp only [Bool.true_eq, Bool.false_eq_true, if_true, if_false] at hplus hminus
  calc
    _ ≤ ‖positiveValue (trueNuisance M L).pLev (k + 1) x‖ *
        ‖fullValue (trueNuisance M L).JfullPlus k x‖ +
        ‖positiveValue (trueNuisance M L).pLev k x‖ *
        ‖minusFullValue (trueNuisance M L) k x‖ := by
      simpa only [contFullJ, norm_mul] using norm_sub_le
        (positiveValue (trueNuisance M L).pLev (k + 1) x *
          fullValue (trueNuisance M L).JfullPlus k x)
        (positiveValue (trueNuisance M L).pLev k x * minusFullValue (trueNuisance M L) k x)
    _ ≤ 1 * outcomeMagnitude M + 1 * outcomeMagnitude M := by gcongr <;> exact hp _ _
    _ = _ := by ring

-- @node: population_contFullJ_weighted_integrable
/-- Under the [structural assumptions](hyp:h), [known outcome endpoints](hyp:he), and
[invariant level ordering](hyp:hL), if the covariate weight is [measurable](hyp:hw) and
[integrable](hyp:hwi), [the weighted population full-interval outcome contrast is integrable under the observation distribution](goal). -/
lemma population_contFullJ_weighted_integrable
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (k : ℕ) (w : X → ℝ) (hw : Measurable w) (hwi : Integrable w (xLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 * contFullJ L (trueNuisance M L) k o.1)
      (observationLaw M) := by
  have hm := population_continuous_full_J_measurable M h.2.2.2.1 q L hL k
  have hi : Integrable (fun x => w x * contFullJ L (trueNuisance M L) k x) (xLaw M) := by
    simpa only [mul_comm] using hwi.bdd_mul hm.aestronglyMeasurable
      (population_contFullJ_norm_bound M h he q L hL k)
  have hobs := M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
  have hmap : (observationLaw M).map Prod.fst = xLaw M := by
    simpa only [observationLaw, xLaw, Function.comp_def] using Measure.map_map measurable_fst hobs
  apply (integrable_map_measure (hw.mul hm).aestronglyMeasurable measurable_fst.aemeasurable).mp
  rwa [hmap]

-- @node: population_continuous_full_outcome_fitted_denominator_integrable
/-- Under the [structural assumptions](hyp:h) and [known outcome endpoints](hyp:he), suppose
[all fitted assignment denominators are measurable](hyp:hpi) and
[almost surely bounded below by the clipping constant](hyp:hcl), which [is positive](hyp:hc0).
For [a treatment interval below the level count](hyp:hk) and a [measurable](hyp:hw),
[integrable covariate weight](hyp:hwi), [the weighted full-interval outcome residual with fitted assignment denominators is integrable under the observation distribution on either side](goal). -/
lemma population_continuous_full_outcome_fitted_denominator_integrable
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (L : LevelData Z X)
    (pi : PositiveIndex L.K → X → ℝ) (hpi : ∀ a, Measurable (pi a))
    (c0 : ℝ) (hc0 : 0 < c0) (hcl : ∀ a, ∀ᵐ x ∂xLaw M, c0 ≤ pi a x)
    (plus : Bool) (k : ℕ) (hk : k < L.K)
    (w : X → ℝ) (hw : Measurable w) (hwi : Integrable w (xLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 *
      continuousFullOutcomeResidual L {trueNuisance M L with piLev := pi} plus k o)
      (observationLaw M) := by
  have hc i : Measurable (positiveValue pi i) := by
    first | fun_prop | skip
    unfold positiveValue
    split_ifs
    · exact hpi _
    · fun_prop
  have hg : Measurable (Function.uncurry (fun (_ : X) (y : ℝ) => y)) := measurable_snd
  have hb : ∀ (x : X) y, y ∈ M.Yset → ‖y‖ ≤ outcomeMagnitude M :=
    fun _ _ hy => outcome_norm_le_magnitude M he hy
  cases plus
  · by_cases hk0 : k = 0
    · subst k
      simp only [continuousFullOutcomeResidual, Bool.not_false, Bool.true_eq,
        true_and, if_true, mul_zero]
      exact integrable_zero _ _ _
    have hi : 1 ≤ k ∧ k ≤ L.K := ⟨by omega, hk.le⟩
    have hl : ∀ᵐ x ∂xLaw M, c0 ≤ positiveValue pi k x := by
      simpa only [positiveValue, dif_pos hi] using hcl ⟨k, hi⟩
    have hr := population_selected_treatment_residual_integrable M h L k
      (fun _ y => y) hg hb (positiveValue pi k) (hc k) c0 hc0 hl w hw hwi
    simpa [continuousFullOutcomeResidual, minusFullValue, hk0, hi.1, hk,
      trueNuisance, treatedBandMean] using hr
  · have hi : 1 ≤ k + 1 ∧ k + 1 ≤ L.K := ⟨by omega, by omega⟩
    have hl : ∀ᵐ x ∂xLaw M, c0 ≤ positiveValue pi (k + 1) x := by
      simpa only [positiveValue, dif_pos hi] using hcl ⟨k + 1, hi⟩
    have hr := population_selected_treatment_residual_integrable M h L (k + 1)
      (fun _ y => y) hg hb (positiveValue pi (k + 1)) (hc (k + 1)) c0 hc0 hl w hw hwi
    simpa [continuousFullOutcomeResidual, fullValue, hk, trueNuisance, treatedBandMean] using hr

end Papers.TbsPrteOptimalTransport
