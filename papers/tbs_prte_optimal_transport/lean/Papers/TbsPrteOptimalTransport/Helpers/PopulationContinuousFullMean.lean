module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationContinuousResidual
/-! Weighted full-interval continuous moments and the signed product-weight cancellation. -/
@[expose] public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set
open scoped Classical

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- The minus correction is absent at the structural zero, just as in psiFullJ.
-- @node: continuousFullOutcomeResidual
/-- For [an ordered level system](hyp:L), [continuous nuisance functions](hyp:e),
[a choice of upper or lower side](hyp:plus), [an interval index](hyp:k), and
[an observation](hyp:o), the [full-interval outcome residual](goal) is zero on
the lower side at index zero; otherwise it is the outcome minus the chosen
full-interval mean, multiplied by the treatment and selected-instrument
indicators and divided by the chosen assignment probability. -/
noncomputable def continuousFullOutcomeResidual (L : LevelData Z X)
    (e : NuisanceCont L) (plus : Bool) (k : ℕ) (o : Obs X Z) : ℝ :=
  if !plus ∧ k = 0 then 0 else
    indicator (o.2.1 ∈ L.S (if plus then k+1 else k)) * o.2.2.1 /
      positiveValue e.piLev (if plus then k+1 else k) o.1 *
        (o.2.2.2 - if plus then fullValue e.JfullPlus k o.1 else minusFullValue e k o.1)

-- @node: population_continuous_full_mean_measurable
/-- [The population full-interval mean on either side of any interval is a
measurable function of covariates](goal). -/
@[fun_prop] lemma population_continuous_full_mean_measurable
    (L : LevelData Z X) (plus : Bool) (k : ℕ) :
    Measurable (fun x => if plus then fullValue (trueNuisance M L).JfullPlus k x
      else minusFullValue (trueNuisance M L) k x) := by
  first | fun_prop | skip
  have hi i := population_treated_integral_measurable M L i (fun _ y => y)
    measurable_snd
  cases plus
  · simp only [Bool.false_eq_true, if_false, minusFullValue]
    split_ifs with hk
    · have hk0 : k ≠ 0 := by omega
      simpa [trueNuisance, treatedBandMean, hk0] using hi k
    · fun_prop
  · simp only [Bool.true_eq, if_true, fullValue]
    split_ifs
    · simpa [trueNuisance, treatedBandMean] using hi (k+1)
    · fun_prop

-- Selected conditional means center the actual score residual, including W.
-- @node: population_continuous_full_outcome_weighted_zero
/-- If [the interval index is below the number of levels](hyp:hk),
[the covariate weight is measurable](hyp:hw), and [the weighted population
outcome residual on the chosen side is integrable](hyp:hi), then [that weighted
residual has expectation zero under the observation law](goal). -/
lemma population_continuous_full_outcome_weighted_zero (L : LevelData Z X)
    (plus : Bool) (k : ℕ) (hk : k < L.K) (w : X → ℝ) (hw : Measurable w)
    (hi : Integrable (fun o : Obs X Z => w o.1 *
      continuousFullOutcomeResidual L (trueNuisance M L) plus k o) (observationLaw M)) :
    (∫ o : Obs X Z, w o.1 * continuousFullOutcomeResidual L (trueNuisance M L)
      plus k o ∂observationLaw M) = 0 := by
  have hc i : Measurable (positiveValue (trueNuisance M L).piLev i) := by
    first | fun_prop | skip
    unfold positiveValue
    split_ifs
    · change Measurable (fun x => ∑ z ∈ L.S i, (M.instKernel x {z}).toReal)
      exact Finset.measurable_sum _ (fun z _ =>
        (Kernel.measurable_coe _ (measurableSet_singleton z)).ennreal_toReal)
    · fun_prop
  cases plus
  · by_cases hk0 : k = 0
    · subst k
      simp [continuousFullOutcomeResidual]
    have hk1 : 1 ≤ k := by omega
    have heq : ∀ o : Obs X Z,
        continuousFullOutcomeResidual L (trueNuisance M L) false k o =
        indicator (o.2.1 ∈ L.S k) * o.2.2.1 /
          positiveValue (trueNuisance M L).piLev k o.1 *
            (o.2.2.2 - ∫ y, y ∂treatedLaw M L k o.1) := by
      intro o
      simp [continuousFullOutcomeResidual, minusFullValue, hk0, hk1, hk,
        trueNuisance, treatedBandMean]
    simp_rw [heq] at hi ⊢
    exact population_selected_treatment_weighted_integral_zero M L k (fun _ y => y)
      measurable_snd _ w (hc k) hw hi
  · have heq : ∀ o : Obs X Z,
        continuousFullOutcomeResidual L (trueNuisance M L) true k o =
        indicator (o.2.1 ∈ L.S (k+1)) * o.2.2.1 /
          positiveValue (trueNuisance M L).piLev (k+1) o.1 *
            (o.2.2.2 - ∫ y, y ∂treatedLaw M L (k+1) o.1) := by
      intro o
      simp [continuousFullOutcomeResidual, fullValue, hk, trueNuisance, treatedBandMean]
    simp_rw [heq] at hi ⊢
    exact population_selected_treatment_weighted_integral_zero M L (k+1) (fun _ y => y)
      measurable_snd _ w (hc (k+1)) hw hi

-- @node: continuous_full_score_correction_decomposition
/-- [The full-interval score minus its plug-in component equals the upper
outcome residual plus the upper mean times the upper propensity residual,
minus the corresponding lower outcome residual and lower mean times the
lower propensity residual](goal). -/
lemma continuous_full_score_correction_decomposition (L : LevelData Z X)
    (e : NuisanceCont L) (k : ℕ) (o : Obs X Z) :
    psiFullJ L e k o - contFullJ L e k o.1 =
      continuousFullOutcomeResidual L e true k o +
        fullValue e.JfullPlus k o.1 * RpCont L e (k+1) o -
      continuousFullOutcomeResidual L e false k o -
        minusFullValue e k o.1 * RpCont L e k o := by
  by_cases hk : k = 0
  · subst k
    simp only [psiFullJ, continuousFullOutcomeResidual, Bool.not_true, Bool.false_eq_true,
      Bool.not_false, Bool.true_eq, false_and, true_and, if_false, if_true,
      RpCont, minusFullValue]
    split_ifs <;> ring
  · simp only [psiFullJ, continuousFullOutcomeResidual, Bool.not_true, Bool.false_eq_true,
      Bool.not_false, Bool.true_eq, false_and, true_and, hk, if_false, if_true]
    ring

-- Each term is centered with its own measurable covariate weight. No
-- conditional moment of the assembled score is assumed here.
-- @node: population_continuous_full_correction_weighted_zero
/-- Suppose [the model satisfies threshold crossing](hyp:h), [the baseline
propensities and policy indices share the level ordering](hyp:hOrder),
[the interval index is below the number of levels](hyp:hk), and [the covariate
weight is measurable](hyp:hw). If [the weighted upper outcome residual is
integrable](hyp:hp), [the weighted lower outcome residual is integrable](hyp:hm),
[the upper propensity residual multiplied by the weight and upper mean is
integrable](hyp:hrp), and [the corresponding lower propensity term is
integrable](hyp:hrm), then [the weighted population score correction is
integrable and has expectation zero](goal). -/
lemma population_continuous_full_correction_weighted_zero
    (h : ThresholdCrossing M) (q : Z → X → ℝ) (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop q L) (k : ℕ) (hk : k < L.K)
    (w : X → ℝ) (hw : Measurable w)
    (hp : Integrable (fun o : Obs X Z => w o.1 *
      continuousFullOutcomeResidual L (trueNuisance M L) true k o) (observationLaw M))
    (hm : Integrable (fun o : Obs X Z => w o.1 *
      continuousFullOutcomeResidual L (trueNuisance M L) false k o) (observationLaw M))
    (hrp : Integrable (fun o : Obs X Z =>
      (w o.1 * fullValue (trueNuisance M L).JfullPlus k o.1) *
        RpCont L (trueNuisance M L) (k+1) o) (observationLaw M))
    (hrm : Integrable (fun o : Obs X Z =>
      (w o.1 * minusFullValue (trueNuisance M L) k o.1) *
        RpCont L (trueNuisance M L) k o) (observationLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 *
      (psiFullJ L (trueNuisance M L) k o - contFullJ L (trueNuisance M L) k o.1))
      (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 *
      (psiFullJ L (trueNuisance M L) k o - contFullJ L (trueNuisance M L) k o.1)
      ∂observationLaw M) = 0 := by
  have hwp := hw.mul (population_continuous_full_mean_measurable M L true k)
  have hwm := hw.mul (population_continuous_full_mean_measurable M L false k)
  simp only [Bool.true_eq, if_true] at hwp
  simp only [Bool.false_eq_true, if_false] at hwm
  have zp := population_continuous_full_outcome_weighted_zero M L true k hk w hw hp
  have zm := population_continuous_full_outcome_weighted_zero M L false k hk w hw hm
  have zrp := population_RpCont_weighted_integral_zero M h q L hOrder (k+1)
    (fun x => w x * fullValue (trueNuisance M L).JfullPlus k x) hwp hrp
  have zrm := population_RpCont_weighted_integral_zero M h q L hOrder k
    (fun x => w x * minusFullValue (trueNuisance M L) k x) hwm hrm
  simp_rw [continuous_full_score_correction_decomposition, mul_sub, mul_add, ← mul_assoc]
  refine ⟨((hp.fun_add hrp).sub' hm).sub' hrm, ?_⟩
  rw [integral_sub ((hp.fun_add hrp).sub' hm) hrm, integral_sub (hp.fun_add hrp) hm,
    integral_add hp hrp, zp, zm, zrp, zrm]
  ring

-- @node: population_continuous_full_component_weighted_mean
/-- Suppose [threshold crossing holds](hyp:h), [baseline propensities and policy
indices share the level ordering](hyp:hOrder), [the interval index is below the
number of levels](hyp:hk), and [the covariate weight is measurable](hyp:hw).
If [the weighted plug-in component](hyp:hJ), [the weighted upper outcome
residual](hyp:hp), [the weighted lower outcome residual](hyp:hm), [the upper
propensity residual times the weight and upper mean](hyp:hrp), and [the lower
propensity residual times the weight and lower mean](hyp:hrm) are integrable,
then [the weighted full-interval population score is integrable and has the
same expectation as its weighted plug-in component](goal). -/
lemma population_continuous_full_component_weighted_mean
    (h : ThresholdCrossing M) (q : Z → X → ℝ) (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop q L) (k : ℕ) (hk : k < L.K)
    (w : X → ℝ) (hw : Measurable w)
    (hJ : Integrable (fun o : Obs X Z => w o.1 * contFullJ L (trueNuisance M L) k o.1)
      (observationLaw M))
    (hp : Integrable (fun o : Obs X Z => w o.1 *
      continuousFullOutcomeResidual L (trueNuisance M L) true k o) (observationLaw M))
    (hm : Integrable (fun o : Obs X Z => w o.1 *
      continuousFullOutcomeResidual L (trueNuisance M L) false k o) (observationLaw M))
    (hrp : Integrable (fun o : Obs X Z =>
      (w o.1 * fullValue (trueNuisance M L).JfullPlus k o.1) *
        RpCont L (trueNuisance M L) (k+1) o) (observationLaw M))
    (hrm : Integrable (fun o : Obs X Z =>
      (w o.1 * minusFullValue (trueNuisance M L) k o.1) *
        RpCont L (trueNuisance M L) k o) (observationLaw M)) :
    Integrable (fun o : Obs X Z => w o.1 * psiFullJ L (trueNuisance M L) k o)
      (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 * psiFullJ L (trueNuisance M L) k o ∂observationLaw M) =
      ∫ o : Obs X Z, w o.1 * contFullJ L (trueNuisance M L) k o.1 ∂observationLaw M := by
  obtain ⟨hi, hz⟩ := population_continuous_full_correction_weighted_zero M h q L hOrder
    k hk w hw hp hm hrp hrm
  have hid : (fun o : Obs X Z => w o.1 * psiFullJ L (trueNuisance M L) k o) =
      (fun o => w o.1 * contFullJ L (trueNuisance M L) k o.1 + w o.1 *
        (psiFullJ L (trueNuisance M L) k o - contFullJ L (trueNuisance M L) k o.1)) := by
    funext o
    ring
  rw [hid]
  exact ⟨hJ.fun_add hi, by rw [integral_add hJ hi, hz, add_zero]⟩

-- The signed gamma_full residual has the same coefficient cancellation as
-- an unsigned product. Its derivative is centered by the preceding proof.
-- @node: population_continuous_full_product_weight_orthogonality
/-- Suppose [threshold crossing holds](hyp:h), [baseline propensities and policy
indices share the level ordering](hyp:hOrder), and [the perturbation of the
chosen interval's signed assignment weight is measurable](hyp:hd). If [the
unperturbed product score is integrable](hyp:hbase), [the upper outcome residual
times the perturbation](hyp:hp), [the lower outcome residual times the
perturbation](hyp:hm), [the upper propensity residual times the perturbation
and upper mean](hyp:hrp), and [the lower propensity residual times the
perturbation and lower mean](hyp:hrm) are integrable, then [the expected product
score has derivative zero at zero along the additive assignment-weight
perturbation](goal). -/
lemma population_continuous_full_product_weight_orthogonality
    (h : ThresholdCrossing M) (q : Z → X → ℝ) (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop q L)
    (d : Fin L.K → X → ℝ) (k : Fin L.K) (hd : Measurable (d k))
    (hbase : Integrable (fun o => psiFullProd L (trueNuisance M L) k o) (observationLaw M))
    (hp : Integrable (fun o : Obs X Z => d k o.1 *
      continuousFullOutcomeResidual L (trueNuisance M L) true k o) (observationLaw M))
    (hm : Integrable (fun o : Obs X Z => d k o.1 *
      continuousFullOutcomeResidual L (trueNuisance M L) false k o) (observationLaw M))
    (hrp : Integrable (fun o : Obs X Z =>
      (d k o.1 * fullValue (trueNuisance M L).JfullPlus k o.1) *
        RpCont L (trueNuisance M L) (k+1) o) (observationLaw M))
    (hrm : Integrable (fun o : Obs X Z =>
      (d k o.1 * minusFullValue (trueNuisance M L) k o.1) *
        RpCont L (trueNuisance M L) k o) (observationLaw M)) :
    HasDerivAt (fun t : ℝ => ∫ o, psiFullProd L
      {trueNuisance M L with gammaFull := fun a x => (trueNuisance M L).gammaFull a x + t * d a x}
      k o ∂observationLaw M) 0 0 := by
  obtain ⟨hi, hz⟩ := population_continuous_full_correction_weighted_zero M h q L hOrder
    k k.isLt (d k) hd hp hm hrp hrm
  have hpath := product_score_weight_path (observationLaw M)
    (fun o => (trueNuisance M L).gammaFull k o.1) (fun o => d k o.1)
    (fun o => psiFullJ L (trueNuisance M L) k o)
    (fun o => contFullJ L (trueNuisance M L) k o.1)
    (fun o => indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k))
    (by simpa only [psiFullProd, fullValue, dif_pos k.isLt] using hbase) hi hz
  have heq : (fun t : ℝ => ∫ o, psiFullProd L
      {trueNuisance M L with gammaFull := fun a x => (trueNuisance M L).gammaFull a x + t * d a x}
      k o ∂observationLaw M) =
      (fun _ : ℝ => ∫ o, psiFullProd L (trueNuisance M L) k o ∂observationLaw M) := by
    funext t
    have hs : ∀ o, psiFullJ L
        {trueNuisance M L with gammaFull := fun a x => (trueNuisance M L).gammaFull a x + t * d a x}
        k o = psiFullJ L (trueNuisance M L) k o := fun _ => rfl
    have hj : ∀ x, contFullJ L
        {trueNuisance M L with gammaFull := fun a x => (trueNuisance M L).gammaFull a x + t * d a x}
        k x = contFullJ L (trueNuisance M L) k x := fun _ => rfl
    simpa only [psiFullProd, hs, hj, fullValue, dif_pos k.isLt] using hpath t
  rw [heq]
  exact hasDerivAt_const 0 _

end Papers.TbsPrteOptimalTransport
