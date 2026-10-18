module
public import Papers.TbsPrteOptimalTransport.Helpers.DenominatorOrthogonality
/-! Exact tail-score cancellations for the final baseline propensity and its weight. -/
public section
set_option linter.unusedSectionVars false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory

-- The policy event and the weighted baseline assignment have the same
-- conditional mean. Their difference is the baseline propensity derivative.
-- @node: tail_baseline_conditional_centering
/-- Suppose [the conditioning information is contained in the ambient information](hyp:hm),
[the policy weight is measurable with respect to the conditioning information](hyp:hg),
and [the assignment weight](hyp:ha), [its product with the policy weight](hyp:hga),
and [the policy event variable](hyp:he) are integrable. If [the assignment weight has
conditional mean one](hyp:hassign) and [the policy event variable has conditional
mean equal to the policy weight](hyp:hpolicy), [the policy-weighted assignment
minus the policy event variable has conditional mean zero almost everywhere](goal). -/
lemma tail_baseline_conditional_centering {B : Type*} [mB : MeasurableSpace B]
    (ν : Measure B) (m : MeasurableSpace B) (hm : m ≤ mB)
    [SigmaFinite (ν.trim hm)] (g a event : B → ℝ)
    (hg : StronglyMeasurable[m] g) (ha : Integrable a ν)
    (hga : Integrable (g * a) ν) (he : Integrable event ν)
    (hassign : ν[a | m] =ᵐ[ν] (fun _ => (1 : ℝ)))
    (hpolicy : ν[event | m] =ᵐ[ν] g) :
    ν[(fun b => g b * a b - event b) | m] =ᵐ[ν] 0 := by
  let : MeasurableSpace B := mB
  have hid : (fun b => g b * a b - event b) = g * a - event := by
    funext b
    rfl
  rw [hid]
  filter_upwards [condExp_sub hga he m,
    condExp_mul_of_stronglyMeasurable_left hg hga ha, hassign, hpolicy]
    with b hsub hmul hca hce
  simpa only [Pi.sub_apply, Pi.mul_apply, hmul, hca, hce, mul_one,
    sub_self, Pi.zero_apply] using hsub

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- The policy plug-in and policy residual do not use this coefficient.
-- @node: commonTailScore_weight_path
/-- If [there is at least one positive propensity level](hyp:hK), [adding a scalar
multiple of a direction to the tail weight subtracts from the tail score that
scalar times the minimum outcome, the direction divided by the final assignment
probability, and the treatment residual restricted to the final level set](goal). -/
lemma commonTailScore_weight_path (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (prop : Z → X → ℝ) (pk pi : PositiveIndex L.K → X → ℝ)
    (g d : X → ℝ) (o : Obs X Z) (t : ℝ) :
    commonTailScore M phi dphi L prop pk pi (fun x => g x + t * d x) o =
      commonTailScore M phi dphi L prop pk pi g o - t *
        (M.yMin * d o.1 / positiveValue pi L.K o.1 *
          (indicator (o.2.1 ∈ L.S L.K) *
            (o.2.2.1 - positiveValue pk L.K o.1))) := by
  have hk : L.K ≠ 0 := by unfold LevelCountPos at hK; omega
  simp only [commonTailScore, if_neg hk, div_eq_mul_inv]
  ring

-- @node: commonTailScore_weight_orthogonality
/-- Suppose [there is at least one positive propensity level](hyp:hK),
[the conditioning information is contained in the observation information](hyp:hm),
and [the tail-weight direction](hyp:hd) and [the final assignment probability](hyp:hpi)
are measurable with respect to it. If [the final-level treatment residual is
integrable](hyp:hr) and [conditionally centered](hyp:hzero), and [its product with
the minimum outcome and the direction divided by the final assignment probability](hyp:hwr)
and [the unperturbed tail score](hyp:hbase) are integrable, [the population tail
score has zero derivative at zero along this tail-weight perturbation](goal). -/
lemma commonTailScore_weight_orthogonality (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (prop : Z → X → ℝ) (pk pi : PositiveIndex L.K → X → ℝ) (g d : X → ℝ)
    (m : MeasurableSpace (Obs X Z)) (hm : m ≤ Prod.instMeasurableSpace)
    [SigmaFinite ((observationLaw M).trim hm)]
    (hd : StronglyMeasurable[m] (fun o : Obs X Z => d o.1))
    (hpi : StronglyMeasurable[m] (fun o : Obs X Z => positiveValue pi L.K o.1))
    (hr : Integrable (fun o : Obs X Z => indicator (o.2.1 ∈ L.S L.K) *
      (o.2.2.1 - positiveValue pk L.K o.1)) (observationLaw M))
    (hzero : (observationLaw M)[(fun o : Obs X Z => indicator (o.2.1 ∈ L.S L.K) *
      (o.2.2.1 - positiveValue pk L.K o.1)) | m] =ᵐ[observationLaw M] 0)
    (hwr : Integrable (fun o : Obs X Z => M.yMin * d o.1 /
      positiveValue pi L.K o.1 * (indicator (o.2.1 ∈ L.S L.K) *
        (o.2.2.1 - positiveValue pk L.K o.1))) (observationLaw M))
    (hbase : Integrable (commonTailScore M phi dphi L prop pk pi g) (observationLaw M)) :
    HasDerivAt (fun t : ℝ => ∫ o, commonTailScore M phi dphi L prop pk pi
      (fun x => g x + t * d x) o ∂observationLaw M) 0 0 := by
  let : MeasurableSpace (Obs X Z) := Prod.instMeasurableSpace
  have hw : StronglyMeasurable[m] (fun o : Obs X Z => M.yMin * d o.1) := by
    exact stronglyMeasurable_const.mul hd
  have hz := score_denominator_residual_mean_zero (observationLaw M) m hm
    (fun o : Obs X Z => M.yMin * d o.1)
    (fun o : Obs X Z => positiveValue pi L.K o.1)
    (fun o : Obs X Z => indicator (o.2.1 ∈ L.S L.K) *
      (o.2.2.1 - positiveValue pk L.K o.1)) hw hpi hr hwr hzero
  have heq : (fun t : ℝ => ∫ o, commonTailScore M phi dphi L prop pk pi
      (fun x => g x + t * d x) o ∂observationLaw M) =
      (fun _ : ℝ => ∫ o, commonTailScore M phi dphi L prop pk pi g o
        ∂observationLaw M) := by
    funext t
    simp_rw [commonTailScore_weight_path M phi dphi L hK]
    rw [integral_sub hbase (hwr.const_mul t), integral_const_mul, hz,
      mul_zero, sub_zero]
  rw [heq]
  exact hasDerivAt_const 0 _

-- All positive baseline levels may be updated; only the final one enters.
-- @node: commonTailScore_baseline_path
/-- If [there is at least one positive propensity level](hyp:hK), [perturbing all
baseline propensity levels changes the tail score by the perturbation size times
the minimum outcome and the final-level direction, multiplied by the difference
between the tail-weighted inverse-probability assignment and the tail policy-event
indicator](goal). -/
lemma commonTailScore_baseline_path (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (prop : Z → X → ℝ) (pk pi d : PositiveIndex L.K → X → ℝ)
    (g : X → ℝ) (o : Obs X Z) (t : ℝ) :
    commonTailScore M phi dphi L prop (fun k x => pk k x + t * d k x) pi g o =
      commonTailScore M phi dphi L prop pk pi g o + t *
        (M.yMin * positiveValue d L.K o.1 *
          (g o.1 * (indicator (o.2.1 ∈ L.S L.K) / positiveValue pi L.K o.1) -
            indicator (o.2.1 ∈ policyUnion L L.K 1))) := by
  have hk : L.K ≠ 0 := by unfold LevelCountPos at hK; omega
  have hi : 1 ≤ L.K ∧ L.K ≤ L.K := ⟨hK, le_rfl⟩
  simp only [commonTailScore, if_neg hk, positiveValue, dif_pos hi, div_eq_mul_inv]
  ring

-- Assignment centering cancels the plug-in derivative against the p_K residual.
-- @node: commonTailScore_baseline_orthogonality
/-- Suppose [there is at least one positive propensity level](hyp:hK),
[the conditioning information is contained in the observation information](hyp:hm),
and [the tail weight](hyp:hg) and [the final baseline perturbation direction](hyp:hd)
are measurable with respect to it. If [the inverse-probability final-level
assignment](hyp:ha), [its product with the tail weight](hyp:hga), and [the tail
policy-event indicator](hyp:he) are integrable, [the assignment has conditional mean
one](hyp:hassign), [the policy-event indicator has conditional mean equal to the
tail weight](hyp:hpolicy), and [the minimum-outcome-scaled direction times the
difference of those weighted indicators](hyp:hwr) and [the unperturbed tail
score](hyp:hbase) are integrable, [the population tail score has zero derivative
at zero along the joint baseline-level perturbation](goal). -/
lemma commonTailScore_baseline_orthogonality (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (prop : Z → X → ℝ) (pk pi d : PositiveIndex L.K → X → ℝ) (g : X → ℝ)
    (m : MeasurableSpace (Obs X Z)) (hm : m ≤ Prod.instMeasurableSpace)
    [SigmaFinite ((observationLaw M).trim hm)]
    (hg : StronglyMeasurable[m] (fun o : Obs X Z => g o.1))
    (hd : StronglyMeasurable[m] (fun o : Obs X Z => positiveValue d L.K o.1))
    (ha : Integrable (fun o : Obs X Z => indicator (o.2.1 ∈ L.S L.K) /
      positiveValue pi L.K o.1) (observationLaw M))
    (hga : Integrable (fun o : Obs X Z => g o.1 *
      (indicator (o.2.1 ∈ L.S L.K) / positiveValue pi L.K o.1)) (observationLaw M))
    (he : Integrable (fun o : Obs X Z => indicator (o.2.1 ∈ policyUnion L L.K 1))
      (observationLaw M))
    (hassign : (observationLaw M)[(fun o : Obs X Z => indicator (o.2.1 ∈ L.S L.K) /
      positiveValue pi L.K o.1) | m] =ᵐ[observationLaw M] (fun _ => (1 : ℝ)))
    (hpolicy : (observationLaw M)[(fun o : Obs X Z =>
      indicator (o.2.1 ∈ policyUnion L L.K 1)) | m] =ᵐ[observationLaw M]
        (fun o => g o.1))
    (hwr : Integrable (fun o : Obs X Z => M.yMin * positiveValue d L.K o.1 *
      (g o.1 * (indicator (o.2.1 ∈ L.S L.K) / positiveValue pi L.K o.1) -
        indicator (o.2.1 ∈ policyUnion L L.K 1))) (observationLaw M))
    (hbase : Integrable (commonTailScore M phi dphi L prop pk pi g) (observationLaw M)) :
    HasDerivAt (fun t : ℝ => ∫ o, commonTailScore M phi dphi L prop
      (fun k x => pk k x + t * d k x) pi g o ∂observationLaw M) 0 0 := by
  let : MeasurableSpace (Obs X Z) := Prod.instMeasurableSpace
  have hc := tail_baseline_conditional_centering (observationLaw M) m hm
    (fun o : Obs X Z => g o.1)
    (fun o : Obs X Z => indicator (o.2.1 ∈ L.S L.K) / positiveValue pi L.K o.1)
    (fun o : Obs X Z => indicator (o.2.1 ∈ policyUnion L L.K 1))
    hg ha hga he hassign hpolicy
  have hw : StronglyMeasurable[m]
      (fun o : Obs X Z => M.yMin * positiveValue d L.K o.1) := by fun_prop
  have hz := score_weighted_conditional_residual_zero (observationLaw M) m hm
    (fun o : Obs X Z => M.yMin * positiveValue d L.K o.1)
    (fun o : Obs X Z => g o.1 *
      (indicator (o.2.1 ∈ L.S L.K) / positiveValue pi L.K o.1) -
        indicator (o.2.1 ∈ policyUnion L L.K 1))
    (fun _ => (0 : ℝ)) hw (hga.sub' he) (integrable_zero _ _ _)
    (by simpa only [sub_zero] using hwr) hc (by fun_prop)
  simp only [sub_zero] at hz
  have heq : (fun t : ℝ => ∫ o, commonTailScore M phi dphi L prop
      (fun k x => pk k x + t * d k x) pi g o ∂observationLaw M) =
      (fun _ : ℝ => ∫ o, commonTailScore M phi dphi L prop pk pi g o
        ∂observationLaw M) := by
    funext t
    simp_rw [commonTailScore_baseline_path M phi dphi L hK]
    rw [integral_add hbase (hwr.const_mul t), integral_const_mul, hz,
      mul_zero, add_zero]
  rw [heq]
  exact hasDerivAt_const 0 _

-- This form separates the policy residual (centered given X,Z) from the
-- baseline residual (centered given X and the final level set).
-- @node: commonTailScore_residual_decomposition
/-- If [there is at least one positive propensity level](hyp:hK), [the tail score
equals the minimum outcome times the tail policy-event indicator times the gap
between the policy propensity and final baseline propensity, plus the
policy-derivative-weighted treatment residual, minus the final-level treatment
residual weighted by the minimum outcome and the tail weight divided by the final
assignment probability](goal). -/
lemma commonTailScore_residual_decomposition (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (prop : Z → X → ℝ) (pk pi : PositiveIndex L.K → X → ℝ)
    (g : X → ℝ) (o : Obs X Z) :
    commonTailScore M phi dphi L prop pk pi g o =
      M.yMin * indicator (o.2.1 ∈ policyUnion L L.K 1) *
        (phi o.2.1 o.1 (prop o.2.1 o.1) - positiveValue pk L.K o.1) +
      (M.yMin * indicator (o.2.1 ∈ policyUnion L L.K 1) *
        dphi o.2.1 o.1 (prop o.2.1 o.1)) * (o.2.2.1 - prop o.2.1 o.1) -
      M.yMin * g o.1 / positiveValue pi L.K o.1 *
        (indicator (o.2.1 ∈ L.S L.K) * (o.2.2.1 - positiveValue pk L.K o.1)) := by
  have hk : L.K ≠ 0 := by unfold LevelCountPos at hK; omega
  simp only [commonTailScore, if_neg hk, div_eq_mul_inv]
  ring

-- @node: commonTailScore_population_mean
/-- Suppose [there is at least one positive propensity level](hyp:hK) and [the first](hyp:hmx)
and [second](hyp:hmz) conditioning information sets are contained in the observation
information. Assume [the tail weight](hyp:hg) and [final assignment probability](hyp:hpi)
are measurable with respect to the first, and [the minimum-outcome-scaled policy
derivative on the tail policy event is measurable with respect to the second](hyp:hcoef).
If [the propensity treatment residual](hyp:hrp) and [the final-level treatment
residual](hyp:hrk) are integrable, [the former is centered conditional on the second
information set](hyp:hzp), [the latter is centered conditional on the first](hyp:hzk),
and [the policy-derivative correction](hyp:hip), [the inverse-probability tail-weight
correction](hyp:hik), and [the tail policy plug-in term](hyp:ht) are integrable,
[the population tail score equals the mean of the minimum outcome times the tail
policy-event indicator times the gap between policy and final baseline propensities](goal). -/
lemma commonTailScore_population_mean (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (prop : Z → X → ℝ) (pk pi : PositiveIndex L.K → X → ℝ) (g : X → ℝ)
    (mx mz : MeasurableSpace (Obs X Z))
    (hmx : mx ≤ Prod.instMeasurableSpace) (hmz : mz ≤ Prod.instMeasurableSpace)
    [SigmaFinite ((observationLaw M).trim hmx)]
    [SigmaFinite ((observationLaw M).trim hmz)]
    (hg : StronglyMeasurable[mx] (fun o : Obs X Z => g o.1))
    (hpi : StronglyMeasurable[mx] (fun o : Obs X Z => positiveValue pi L.K o.1))
    (hcoef : StronglyMeasurable[mz] (fun o : Obs X Z => M.yMin *
      indicator (o.2.1 ∈ policyUnion L L.K 1) * dphi o.2.1 o.1 (prop o.2.1 o.1)))
    (hrp : Integrable (fun o : Obs X Z => o.2.2.1 - prop o.2.1 o.1) (observationLaw M))
    (hrk : Integrable (fun o : Obs X Z => indicator (o.2.1 ∈ L.S L.K) *
      (o.2.2.1 - positiveValue pk L.K o.1)) (observationLaw M))
    (hzp : (observationLaw M)[(fun o : Obs X Z => o.2.2.1 - prop o.2.1 o.1) | mz]
      =ᵐ[observationLaw M] 0)
    (hzk : (observationLaw M)[(fun o : Obs X Z => indicator (o.2.1 ∈ L.S L.K) *
      (o.2.2.1 - positiveValue pk L.K o.1)) | mx] =ᵐ[observationLaw M] 0)
    (hip : Integrable (fun o : Obs X Z =>
      (M.yMin * indicator (o.2.1 ∈ policyUnion L L.K 1) *
        dphi o.2.1 o.1 (prop o.2.1 o.1)) * (o.2.2.1 - prop o.2.1 o.1))
      (observationLaw M))
    (hik : Integrable (fun o : Obs X Z => M.yMin * g o.1 / positiveValue pi L.K o.1 *
      (indicator (o.2.1 ∈ L.S L.K) * (o.2.2.1 - positiveValue pk L.K o.1)))
      (observationLaw M))
    (ht : Integrable (fun o : Obs X Z => M.yMin *
      indicator (o.2.1 ∈ policyUnion L L.K 1) *
        (phi o.2.1 o.1 (prop o.2.1 o.1) - positiveValue pk L.K o.1))
      (observationLaw M)) :
    (∫ o, commonTailScore M phi dphi L prop pk pi g o ∂observationLaw M) =
      ∫ o, M.yMin * indicator (o.2.1 ∈ policyUnion L L.K 1) *
        (phi o.2.1 o.1 (prop o.2.1 o.1) - positiveValue pk L.K o.1)
        ∂observationLaw M := by
  let : MeasurableSpace (Obs X Z) := Prod.instMeasurableSpace
  have hw : StronglyMeasurable[mx] (fun o : Obs X Z => M.yMin * g o.1) := by
    exact stronglyMeasurable_const.mul hg
  have hp := score_denominator_residual_mean_zero (observationLaw M) mz hmz
    (fun o : Obs X Z => M.yMin * indicator (o.2.1 ∈ policyUnion L L.K 1) *
      dphi o.2.1 o.1 (prop o.2.1 o.1)) (fun _ => (1 : ℝ))
    (fun o : Obs X Z => o.2.2.1 - prop o.2.1 o.1)
    hcoef (by fun_prop) hrp (by simpa only [div_one] using hip) hzp
  simp only [div_one] at hp
  have hk := score_denominator_residual_mean_zero (observationLaw M) mx hmx
    (fun o : Obs X Z => M.yMin * g o.1)
    (fun o : Obs X Z => positiveValue pi L.K o.1)
    (fun o : Obs X Z => indicator (o.2.1 ∈ L.S L.K) *
      (o.2.2.1 - positiveValue pk L.K o.1)) hw hpi hrk hik hzk
  simp_rw [commonTailScore_residual_decomposition M phi dphi L hK]
  have hsum := ht.add hip
  simp only [Pi.add_def] at hsum
  rw [integral_sub hsum hik, integral_add ht hip, hp, hk, add_zero, sub_zero]

end Papers.TbsPrteOptimalTransport
