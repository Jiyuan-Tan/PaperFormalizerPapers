module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationBinaryAdmissibility
public import Papers.TbsPrteOptimalTransport.Helpers.FullRegressionOrthogonality
/-! Population assignment residuals and full-interval regression cancellation. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set
open scoped Classical

universe u v
variable {Ω : Type u} {X Z : Type v} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: population_assignment_conditional_mean
/-- [The conditional expectation, given covariates, of the indicator that the
instrument belongs to C equals the sum of its conditional atom probabilities over C,
almost surely under the population law](goal). -/
lemma population_assignment_conditional_mean (C : Finset Z) :
    M.law.toMeasure[(fun s => indicator (M.Zv s ∈ C)) |
      MeasurableSpace.comap M.Xv inferInstance] =ᵐ[M.law.toMeasure]
      (fun s => ∑ z ∈ C, instProb M z (M.Xv s)) := by
  have hC : MeasurableSet (C : Set Z) := C.finite_toSet.measurableSet
  have hf : Measurable (fun z : Z => indicator (z ∈ C)) := by
    unfold indicator
    exact Measurable.ite hC measurable_const measurable_const
  have hi : Integrable (fun s => indicator (M.Zv s ∈ C)) M.law.toMeasure := by
    apply (integrable_const (1 : ℝ)).mono' (hf.comp M.measZ).aestronglyMeasurable
    filter_upwards [] with s
    by_cases hs : M.Zv s ∈ C <;> simp [indicator, hs]
  have hc := condExp_ae_eq_integral_condDistrib M.measX M.measZ.aemeasurable
    hf.stronglyMeasurable hi
  have hv := ae_of_ae_map M.measX.aemeasurable M.instKernel_version
  haveI := M.instKernel_markov
  filter_upwards [hc, hv] with s hs hv
  rw [hs, ← hv]
  change (∫ z, indicator (z ∈ C) ∂M.instKernel (M.Xv s)) = _
  have hid : (fun z : Z => indicator (z ∈ C)) = (C : Set Z).indicator (1 : Z → ℝ) := by
    funext z
    simp [indicator, Set.indicator]
  rw [hid, integral_indicator_one hC]
  change (M.instKernel (M.Xv s)).real (C : Set Z) =
    ∑ z ∈ C, (M.instKernel (M.Xv s)).real {z}
  exact (sum_measureReal_singleton C).symm

-- @node: population_assignment_weighted_integral_zero
/-- If [the covariate weight is measurable](hyp:hw) and [its product with the
instrument-set indicator minus that set's conditional probability is integrable](hyp:hi),
then [the population integral of this weighted assignment residual is zero](goal). -/
lemma population_assignment_weighted_integral_zero (C : Finset Z)
    (w : X → ℝ) (hw : Measurable w)
    (hi : Integrable (fun o : Obs X Z => w o.1 *
      (indicator (o.2.1 ∈ C) - ∑ z ∈ C, instProb M z o.1)) (observationLaw M)) :
    (∫ o : Obs X Z, w o.1 * (indicator (o.2.1 ∈ C) -
      ∑ z ∈ C, instProb M z o.1) ∂observationLaw M) = 0 := by
  let p := fun x => ∑ z ∈ C, instProb M z x
  have hp : Measurable p := population_instrument_set_probability_measurable M C
  have hC : MeasurableSet (C : Set Z) := C.finite_toSet.measurableSet
  have ha : Measurable (fun z : Z => indicator (z ∈ C)) := by
    unfold indicator
    exact Measurable.ite hC measurable_const measurable_const
  let f : Obs X Z → ℝ := fun o => w o.1 * (indicator (o.2.1 ∈ C) - p o.1)
  have hf : Measurable f := by
    dsimp only [f]
    fun_prop
  have hobs := M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
  have hi' : Integrable (fun s => f (M.Xv s, M.Zv s, M.W s, M.Y s)) M.law.toMeasure :=
    (integrable_map_measure hf.aestronglyMeasurable hobs.aemeasurable).mp hi
  let m := MeasurableSpace.comap M.Xv inferInstance
  let : MeasurableSpace Ω := mΩ
  have hm : m ≤ mΩ := M.measX.comap_le
  have hw' : StronglyMeasurable[m] (fun s => w (M.Xv s)) :=
    hw.stronglyMeasurable.comp_measurable (comap_measurable _)
  have hp' : StronglyMeasurable[m] (fun s => p (M.Xv s)) :=
    hp.stronglyMeasurable.comp_measurable (comap_measurable _)
  have hai : Integrable (fun s => indicator (M.Zv s ∈ C)) M.law.toMeasure := by
    apply (integrable_const (1 : ℝ)).mono' (ha.comp M.measZ).aestronglyMeasurable
    filter_upwards [] with s
    by_cases hs : M.Zv s ∈ C <;> simp [indicator, hs]
  have hpi : Integrable (fun s => p (M.Xv s)) M.law.toMeasure := by
    apply (integrable_const (1 : ℝ)).mono' (hp.comp M.measX).aestronglyMeasurable
    filter_upwards [] with s
    change ‖∑ z ∈ C, instProb M z (M.Xv s)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (population_instrument_set_probability_range M C _).1]
    exact (population_instrument_set_probability_range M C _).2
  have hz := score_weighted_conditional_residual_zero M.law.toMeasure m hm
    (fun s => w (M.Xv s)) (fun s => indicator (M.Zv s ∈ C))
    (fun s => p (M.Xv s)) hw' hai hpi hi'
    (population_assignment_conditional_mean M C) hp'
  change (∫ o, f o ∂observationLaw M) = 0
  rw [observationLaw, integral_map hobs.aemeasurable hf.aestronglyMeasurable]
  exact hz

-- @node: population_normalized_assignment_weighted_integral_zero
/-- If [the covariate weight is measurable](hyp:hw), [the conditional probability of
instrument set C is positive almost everywhere](hyp:hpos), and [the weight times one
minus the set indicator divided by that probability is integrable](hyp:hi), then
[the population integral of this weighted normalized assignment residual is zero](goal). -/
lemma population_normalized_assignment_weighted_integral_zero (C : Finset Z)
    (w : X → ℝ) (hw : Measurable w)
    (hpos : ∀ᵐ x ∂xLaw M, 0 < ∑ z ∈ C, instProb M z x)
    (hi : Integrable (fun o : Obs X Z => w o.1 *
      (1 - indicator (o.2.1 ∈ C) / (∑ z ∈ C, instProb M z o.1))) (observationLaw M)) :
    (∫ o : Obs X Z, w o.1 *
      (1 - indicator (o.2.1 ∈ C) / (∑ z ∈ C, instProb M z o.1)) ∂observationLaw M) = 0 := by
  let p := fun x => ∑ z ∈ C, instProb M z x
  have hp : Measurable p := population_instrument_set_probability_measurable M C
  have hobs := observationLaw_covariate_ae M _ hpos
  have hid : (fun o : Obs X Z => w o.1 * (1 - indicator (o.2.1 ∈ C) / p o.1)) =ᵐ[observationLaw M]
      (fun o => (-w o.1 / p o.1) * (indicator (o.2.1 ∈ C) - p o.1)) := by
    filter_upwards [hobs] with o ho
    dsimp only [p]
    field_simp [ne_of_gt ho]
    <;> ring
  have hi' := hi.congr hid
  have hz := population_assignment_weighted_integral_zero M C (fun x => -w x / p x)
    (by fun_prop) hi'
  exact (integral_congr_ae hid).trans hz

-- The population denominators give cancellation for simultaneous positive-level
-- regression directions, including the fixed zero boundary. No conditional
-- orthogonality premise is imposed on the score.
-- @node: population_binary_full_regression_integral_path
/-- Suppose [baseline-class probabilities satisfy overlap with bound cpi](hyp:hoverlap),
[the covariate weight is measurable](hyp:hw), [each positive-level regression direction
is measurable](hyp:hd), [the baseline weighted full-bin regression score is integrable](hyp:hs),
[the weight times the upper-level direction times its normalized assignment residual
is integrable](hyp:hp), and [the analogous lower-level term, using zero residual at
the zero boundary, is integrable](hyp:hm). Then [the population integral of the weighted
full-bin regression contrast with its two regression corrections is unchanged by any
simultaneous affine perturbation of the positive-level treated regressions](goal). -/
lemma population_binary_full_regression_integral_path (L : LevelData Z X)
    (cpi : ℝ) (hoverlap : BaselineOverlapWitness M L cpi)
    (d : PositiveIndex L.K → X → ℝ) (k : Fin L.K)
    (w : X → ℝ) (hw : Measurable w)
    (hd : ∀ a, Measurable (d a))
    (hs : Integrable (fun o : Obs X Z => w o.1 *
      (binFullJ L (eta0Bin M L) k o.1 + RP L (eta0Bin M L) (k+1) o -
        RP L (eta0Bin M L) k o)) (observationLaw M))
    (hp : Integrable (fun o : Obs X Z => (w o.1 * positiveValue d (k+1) o.1) *
      (1 - indicator (o.2.1 ∈ L.S (k+1)) / positiveValue (eta0Bin M L).piLev (k+1) o.1))
      (observationLaw M))
    (hm : Integrable (fun o : Obs X Z => (w o.1 * positiveValue d k o.1) *
      (1 - (if k.val = 0 then 1 else indicator (o.2.1 ∈ L.S k) /
        positiveValue (eta0Bin M L).piLev k o.1))) (observationLaw M)) (t : ℝ) :
    (∫ o : Obs X Z,
      let et := {eta0Bin M L with P1 := fun a x => (eta0Bin M L).P1 a x + t * d a x}
      w o.1 * (binFullJ L et k o.1 + RP L et (k+1) o - RP L et k o) ∂observationLaw M) =
    ∫ o : Obs X Z, w o.1 * (binFullJ L (eta0Bin M L) k o.1 +
      RP L (eta0Bin M L) (k+1) o - RP L (eta0Bin M L) k o) ∂observationLaw M := by
  have hkplus : 1 ≤ k.val + 1 ∧ k.val + 1 ≤ L.K := by omega
  have hdp : Measurable (positiveValue d (k+1)) := by
    change Measurable (fun x => positiveValue d (k.val+1) x)
    simpa only [positiveValue, dif_pos hkplus] using hd ⟨k.val+1, hkplus⟩
  have zplus : (∫ o : Obs X Z, (w o.1 * positiveValue d (k+1) o.1) *
      (1 - indicator (o.2.1 ∈ L.S (k+1)) / positiveValue (eta0Bin M L).piLev (k+1) o.1)
      ∂observationLaw M) = 0 := by
    have hpdef : ∀ x, positiveValue (eta0Bin M L).piLev (k+1) x =
        ∑ z ∈ L.S (k+1), instProb M z x := by
      intro x
      simp only [positiveValue, dif_pos hkplus, eta0Bin, levelSetProb]
    simp_rw [hpdef] at hp ⊢
    apply population_normalized_assignment_weighted_integral_zero M _ _ (hw.mul hdp) _ hp
    exact Filter.Eventually.of_forall fun x =>
      hoverlap.1.trans_le (hoverlap.2 x (k+1) hkplus.1 hkplus.2)
  have zminus : (∫ o : Obs X Z, (w o.1 * positiveValue d k o.1) *
      (1 - (if k.val = 0 then 1 else indicator (o.2.1 ∈ L.S k) /
        positiveValue (eta0Bin M L).piLev k o.1)) ∂observationLaw M) = 0 := by
    by_cases hkzero : k.val = 0
    · simp [hkzero]
    · have hkpos : 1 ≤ k.val ∧ k.val ≤ L.K := by omega
      have hdm : Measurable (positiveValue d k) := by
        change Measurable (fun x => positiveValue d k.val x)
        simpa only [positiveValue, dif_pos hkpos] using hd ⟨k.val, hkpos⟩
      have hpdef : ∀ x, positiveValue (eta0Bin M L).piLev k x =
          ∑ z ∈ L.S k, instProb M z x := by
        intro x
        simp only [positiveValue, dif_pos hkpos, eta0Bin, levelSetProb]
      simp_rw [if_neg hkzero, hpdef] at hm ⊢
      apply population_normalized_assignment_weighted_integral_zero M _ _ (hw.mul hdm) _ hm
      exact Filter.Eventually.of_forall fun x =>
        hoverlap.1.trans_le (hoverlap.2 x k hkpos.1 hkpos.2)
  have hid : (fun o : Obs X Z =>
      let et := {eta0Bin M L with P1 := fun a x => (eta0Bin M L).P1 a x + t * d a x}
      w o.1 * (binFullJ L et k o.1 + RP L et (k+1) o - RP L et k o)) =
      (fun o => w o.1 * (binFullJ L (eta0Bin M L) k o.1 +
        RP L (eta0Bin M L) (k+1) o - RP L (eta0Bin M L) k o) + t *
        ((w o.1 * positiveValue d (k+1) o.1) *
          (1 - indicator (o.2.1 ∈ L.S (k+1)) / positiveValue (eta0Bin M L).piLev (k+1) o.1) -
        (w o.1 * positiveValue d k o.1) *
          (1 - (if k.val = 0 then 1 else indicator (o.2.1 ∈ L.S k) /
            positiveValue (eta0Bin M L).piLev k o.1)))) := by
    funext o
    dsimp only
    rw [binary_full_regression_path]
    ring
  rw [hid, integral_add hs ((hp.sub' hm).const_mul t), integral_const_mul,
    integral_sub hp hm, zplus, zminus]
  ring

-- @node: population_binary_full_regression_orthogonality
/-- Suppose [baseline-class probabilities satisfy overlap with bound cpi](hyp:hoverlap),
[the covariate weight is measurable](hyp:hw), [each positive-level regression direction
is measurable](hyp:hd), [the baseline weighted full-bin regression score is integrable](hyp:hs),
[the weighted upper-level direction times its normalized assignment residual is
integrable](hyp:hp), and [the analogous lower-level term, using zero residual at the
zero boundary, is integrable](hyp:hm). Then [the population integral of the weighted
full-bin regression contrast with its two regression corrections has derivative zero
at the truth along the simultaneous positive-level regression path](goal). -/
lemma population_binary_full_regression_orthogonality (L : LevelData Z X)
    (cpi : ℝ) (hoverlap : BaselineOverlapWitness M L cpi)
    (d : PositiveIndex L.K → X → ℝ) (k : Fin L.K)
    (w : X → ℝ) (hw : Measurable w)
    (hd : ∀ a, Measurable (d a))
    (hs : Integrable (fun o : Obs X Z => w o.1 *
      (binFullJ L (eta0Bin M L) k o.1 + RP L (eta0Bin M L) (k+1) o -
        RP L (eta0Bin M L) k o)) (observationLaw M))
    (hp : Integrable (fun o : Obs X Z => (w o.1 * positiveValue d (k+1) o.1) *
      (1 - indicator (o.2.1 ∈ L.S (k+1)) / positiveValue (eta0Bin M L).piLev (k+1) o.1))
      (observationLaw M))
    (hm : Integrable (fun o : Obs X Z => (w o.1 * positiveValue d k o.1) *
      (1 - (if k.val = 0 then 1 else indicator (o.2.1 ∈ L.S k) /
        positiveValue (eta0Bin M L).piLev k o.1))) (observationLaw M)) :
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
      let et := {eta0Bin M L with P1 := fun a x => (eta0Bin M L).P1 a x + t * d a x}
      w o.1 * (binFullJ L et k o.1 + RP L et (k+1) o - RP L et k o) ∂observationLaw M) 0 0 := by
  have heq : (fun t : ℝ => ∫ o : Obs X Z,
      let et := {eta0Bin M L with P1 := fun a x => (eta0Bin M L).P1 a x + t * d a x}
      w o.1 * (binFullJ L et k o.1 + RP L et (k+1) o - RP L et k o) ∂observationLaw M) =
      (fun _ : ℝ => ∫ o : Obs X Z, w o.1 * (binFullJ L (eta0Bin M L) k o.1 +
        RP L (eta0Bin M L) (k+1) o - RP L (eta0Bin M L) k o) ∂observationLaw M) := by
    funext t
    exact population_binary_full_regression_integral_path M L cpi hoverlap d k w hw hd hs hp hm t
  rw [heq]
  exact hasDerivAt_const 0 _


-- The full-bin product has a signed assignment residual. Center its two
-- indicators separately; no positivity of gammaFull is used.
-- @node: population_signed_assignment_weighted_integral_zero
/-- If [the covariate weight is measurable](hyp:hw), [the weight times the centered
indicator of instrument membership in C is integrable](hyp:hC), and [the weight times
the centered indicator of membership in D is integrable](hyp:hD), then [the
population integral of the weight times the difference of the two indicators minus
the difference of their conditional probabilities is zero](goal). -/
lemma population_signed_assignment_weighted_integral_zero (C D : Finset Z)
    (w : X → ℝ) (hw : Measurable w)
    (hC : Integrable (fun o : Obs X Z => w o.1 *
      (indicator (o.2.1 ∈ C) - ∑ z ∈ C, instProb M z o.1)) (observationLaw M))
    (hD : Integrable (fun o : Obs X Z => w o.1 *
      (indicator (o.2.1 ∈ D) - ∑ z ∈ D, instProb M z o.1)) (observationLaw M)) :
    (∫ o : Obs X Z, w o.1 * (indicator (o.2.1 ∈ C) - indicator (o.2.1 ∈ D) -
      ((∑ z ∈ C, instProb M z o.1) - ∑ z ∈ D, instProb M z o.1))
      ∂observationLaw M) = 0 := by
  have hid : (fun o : Obs X Z => w o.1 *
      (indicator (o.2.1 ∈ C) - indicator (o.2.1 ∈ D) -
        ((∑ z ∈ C, instProb M z o.1) - ∑ z ∈ D, instProb M z o.1))) =
      (fun o => w o.1 * (indicator (o.2.1 ∈ C) - ∑ z ∈ C, instProb M z o.1) -
        w o.1 * (indicator (o.2.1 ∈ D) - ∑ z ∈ D, instProb M z o.1)) := by
    funext o
    ring
  rw [hid, integral_sub hC hD,
    population_assignment_weighted_integral_zero M C w hw hC,
    population_assignment_weighted_integral_zero M D w hw hD, sub_self]

-- @node: binary_full_product_regression_path
/-- [Along an affine change to all positive-level treated regressions, the binary
full-bin product score equals the baseline full-bin assignment contrast times the
perturbed regression contrast with its corrections, plus the baseline regression
contrast times the signed assignment residual, plus path time times the difference
of the adjacent regression directions times that same signed residual](goal). -/
lemma binary_full_product_regression_path (L : LevelData Z X) (e : NuisanceBin L)
    (d : PositiveIndex L.K → X → ℝ) (k : ℕ) (o : Obs X Z) (t : ℝ) :
    let et := {e with P1 := fun a x => e.P1 a x + t * d a x}
    psiFullProdBin L et k o =
      fullValue e.gammaFull k o.1 *
        (binFullJ L et k o.1 + RP L et (k+1) o - RP L et k o) +
      binFullJ L e k o.1 * (indicator (o.2.1 ∈ higherPolicy L k) -
        indicator (o.2.1 ∈ higherBaseline L k) - fullValue e.gammaFull k o.1) +
      t * ((positiveValue d (k+1) o.1 - positiveValue d k o.1) *
        (indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k) -
          fullValue e.gammaFull k o.1)) := by
  dsimp only
  have hJ : binFullJ L {e with P1 := fun a x => e.P1 a x + t * d a x} k o.1 =
      binFullJ L e k o.1 + t * (positiveValue d (k+1) o.1 - positiveValue d k o.1) := by
    simp only [binFullJ, positiveValue]
    split_ifs <;> ring
  simp only [psiFullProdBin, hJ]
  ring

-- This is the product-score inheritance step of the paper's proof for all
-- positive-level P1 directions simultaneously. The assignment law supplies
-- every cancellation, including the signed higher-bin residual.
-- @node: population_binary_full_product_regression_integral_path
/-- Suppose [baseline-class probabilities satisfy overlap with bound cpi](hyp:hoverlap),
[each positive-level regression direction is measurable](hyp:hd), [the baseline full-bin
regression score weighted by the full-bin assignment contrast is integrable](hyp:hs),
[the assignment contrast times the upper regression direction times its normalized
assignment residual is integrable](hyp:hp), [the analogous lower term with zero residual
at the zero boundary is integrable](hyp:hm), [the baseline regression contrast times
the signed higher-bin assignment residual is integrable](hyp:hb), [the difference of
adjacent regression directions times the centered higher-policy-bin indicator is
integrable](hyp:hC), and [that direction difference times the centered higher-baseline-bin
indicator is integrable](hyp:hD). Then [the
population integral of the binary full-bin product score is unchanged by any simultaneous
affine perturbation of the positive-level treated regressions](goal). -/
lemma population_binary_full_product_regression_integral_path (L : LevelData Z X)
    (cpi : ℝ) (hoverlap : BaselineOverlapWitness M L cpi)
    (d : PositiveIndex L.K → X → ℝ) (k : Fin L.K) (hd : ∀ a, Measurable (d a))
    (hs : Integrable (fun o : Obs X Z => gammaFull M L k o.1 *
      (binFullJ L (eta0Bin M L) k o.1 + RP L (eta0Bin M L) (k+1) o -
        RP L (eta0Bin M L) k o)) (observationLaw M))
    (hp : Integrable (fun o : Obs X Z => (gammaFull M L k o.1 * positiveValue d (k+1) o.1) *
      (1 - indicator (o.2.1 ∈ L.S (k+1)) / positiveValue (eta0Bin M L).piLev (k+1) o.1))
      (observationLaw M))
    (hm : Integrable (fun o : Obs X Z => (gammaFull M L k o.1 * positiveValue d k o.1) *
      (1 - (if k.val = 0 then 1 else indicator (o.2.1 ∈ L.S k) /
        positiveValue (eta0Bin M L).piLev k o.1))) (observationLaw M))
    (hb : Integrable (fun o : Obs X Z => binFullJ L (eta0Bin M L) k o.1 *
      (indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k) -
        gammaFull M L k o.1)) (observationLaw M))
    (hC : Integrable (fun o : Obs X Z =>
      (positiveValue d (k+1) o.1 - positiveValue d k o.1) *
        (indicator (o.2.1 ∈ higherPolicy L k) -
          ∑ z ∈ higherPolicy L k, instProb M z o.1)) (observationLaw M))
    (hD : Integrable (fun o : Obs X Z =>
      (positiveValue d (k+1) o.1 - positiveValue d k o.1) *
        (indicator (o.2.1 ∈ higherBaseline L k) -
          ∑ z ∈ higherBaseline L k, instProb M z o.1)) (observationLaw M)) (t : ℝ) :
    (∫ o : Obs X Z,
      psiFullProdBin L {eta0Bin M L with P1 := fun a x => (eta0Bin M L).P1 a x + t * d a x}
        k o ∂observationLaw M) =
      ∫ o : Obs X Z, psiFullProdBin L (eta0Bin M L) k o ∂observationLaw M := by
  have hg : Measurable (gammaFull M L k) := by
    first
    | fun_prop
    | exact (population_instrument_set_probability_measurable M _).sub
        (population_instrument_set_probability_measurable M _)
  have hdv (a : ℕ) : Measurable (positiveValue d a) := by
    unfold positiveValue
    split_ifs with ha
    · exact hd ⟨a, ha⟩
    · fun_prop
  have hz := population_signed_assignment_weighted_integral_zero M
    (higherPolicy L k) (higherBaseline L k)
    (fun x => positiveValue d (k+1) x - positiveValue d k x)
    ((hdv _).sub (hdv _)) hC hD
  have hr : Integrable (fun o : Obs X Z =>
      (positiveValue d (k+1) o.1 - positiveValue d k o.1) *
        (indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k) -
          gammaFull M L k o.1)) (observationLaw M) := by
    convert hC.sub' hD using 1
    funext o
    simp only [gammaFull]
    ring
  have hs' : Integrable (fun o : Obs X Z => gammaFull M L k o.1 *
      (binFullJ L {eta0Bin M L with P1 := fun a x => (eta0Bin M L).P1 a x + t * d a x} k o.1 +
        RP L {eta0Bin M L with P1 := fun a x => (eta0Bin M L).P1 a x + t * d a x} (k+1) o -
        RP L {eta0Bin M L with P1 := fun a x => (eta0Bin M L).P1 a x + t * d a x} k o))
      (observationLaw M) := by
    apply (hs.add ((hp.sub' hm).const_mul t)).congr
    filter_upwards [] with o
    rw [binary_full_regression_path]
    dsimp only [Pi.add_apply]
    ring
  have hgamma (x : X) : fullValue (eta0Bin M L).gammaFull k x = gammaFull M L k x := by
    simp only [fullValue, dif_pos k.isLt, eta0Bin]
  let et : NuisanceBin L :=
    {eta0Bin M L with P1 := fun a x => (eta0Bin M L).P1 a x + t * d a x}
  let A : Obs X Z → ℝ := fun o => gammaFull M L k o.1 *
    (binFullJ L et k o.1 + RP L et (k+1) o - RP L et k o)
  let B : Obs X Z → ℝ := fun o => binFullJ L (eta0Bin M L) k o.1 *
    (indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k) -
      gammaFull M L k o.1)
  let R : Obs X Z → ℝ := fun o => (positiveValue d (k+1) o.1 - positiveValue d k o.1) *
    (indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k) -
      gammaFull M L k o.1)
  have hid : (fun o => psiFullProdBin L et k o) = (fun o => (A o + B o) + t * R o) := by
    funext o
    simpa only [A, B, R, hgamma] using
      binary_full_product_regression_path L (eta0Bin M L) d k o t
  change (∫ o, psiFullProdBin L et k o ∂observationLaw M) = _
  rw [hid]
  have hiA : Integrable A (observationLaw M) := hs'
  have hiB : Integrable B (observationLaw M) := hb
  have hiR : Integrable R (observationLaw M) := hr
  have hsplit : (∫ o, (A o + B o) + t * R o ∂observationLaw M) =
      (∫ o, A o ∂observationLaw M) + (∫ o, B o ∂observationLaw M) +
        t * (∫ o, R o ∂observationLaw M) := by
    calc
      _ = (∫ o, A o + B o ∂observationLaw M) +
          (∫ o, t * R o ∂observationLaw M) := integral_add (hiA.add hiB) (hiR.const_mul t)
      _ = _ := by rw [integral_add hiA hiB, integral_const_mul]
  rw [hsplit]
  have hz' : (∫ o, R o ∂observationLaw M) = 0 := hz
  rw [hz', mul_zero, add_zero]
  change (∫ o, gammaFull M L k o.1 *
    (binFullJ L et k o.1 + RP L et (k+1) o - RP L et k o) ∂observationLaw M) +
      (∫ o, B o ∂observationLaw M) = _
  rw [population_binary_full_regression_integral_path M L cpi hoverlap d k
    (gammaFull M L k) hg hd hs hp hm t]
  have hbase : (fun o => psiFullProdBin L (eta0Bin M L) k o) =
      (fun o => gammaFull M L k o.1 *
        (binFullJ L (eta0Bin M L) k o.1 + RP L (eta0Bin M L) (k+1) o -
          RP L (eta0Bin M L) k o) + B o) := by
    funext o
    simp only [psiFullProdBin, hgamma, B]
  rw [hbase]
  exact (integral_add hs hb).symm

-- @node: population_binary_full_product_regression_orthogonality
/-- Suppose [baseline-class probabilities satisfy overlap with bound cpi](hyp:hoverlap),
[each positive-level regression direction is measurable](hyp:hd), [the baseline full-bin
regression score weighted by the full-bin assignment contrast is integrable](hyp:hs),
[the assignment contrast times the upper regression direction times its normalized
assignment residual is integrable](hyp:hp), [the analogous lower term with zero residual
at the zero boundary is integrable](hyp:hm), [the baseline regression contrast times
the signed higher-bin assignment residual is integrable](hyp:hb), [the difference of
adjacent regression directions times the centered higher-policy-bin indicator is
integrable](hyp:hC), and [that direction difference times the centered higher-baseline-bin
indicator is integrable](hyp:hD). Then [the
population integral of the binary full-bin product score has derivative zero at the
truth along the simultaneous positive-level regression path](goal). -/
lemma population_binary_full_product_regression_orthogonality (L : LevelData Z X)
    (cpi : ℝ) (hoverlap : BaselineOverlapWitness M L cpi)
    (d : PositiveIndex L.K → X → ℝ) (k : Fin L.K) (hd : ∀ a, Measurable (d a))
    (hs : Integrable (fun o : Obs X Z => gammaFull M L k o.1 *
      (binFullJ L (eta0Bin M L) k o.1 + RP L (eta0Bin M L) (k+1) o -
        RP L (eta0Bin M L) k o)) (observationLaw M))
    (hp : Integrable (fun o : Obs X Z => (gammaFull M L k o.1 * positiveValue d (k+1) o.1) *
      (1 - indicator (o.2.1 ∈ L.S (k+1)) / positiveValue (eta0Bin M L).piLev (k+1) o.1))
      (observationLaw M))
    (hm : Integrable (fun o : Obs X Z => (gammaFull M L k o.1 * positiveValue d k o.1) *
      (1 - (if k.val = 0 then 1 else indicator (o.2.1 ∈ L.S k) /
        positiveValue (eta0Bin M L).piLev k o.1))) (observationLaw M))
    (hb : Integrable (fun o : Obs X Z => binFullJ L (eta0Bin M L) k o.1 *
      (indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k) -
        gammaFull M L k o.1)) (observationLaw M))
    (hC : Integrable (fun o : Obs X Z =>
      (positiveValue d (k+1) o.1 - positiveValue d k o.1) *
        (indicator (o.2.1 ∈ higherPolicy L k) -
          ∑ z ∈ higherPolicy L k, instProb M z o.1)) (observationLaw M))
    (hD : Integrable (fun o : Obs X Z =>
      (positiveValue d (k+1) o.1 - positiveValue d k o.1) *
        (indicator (o.2.1 ∈ higherBaseline L k) -
          ∑ z ∈ higherBaseline L k, instProb M z o.1)) (observationLaw M)) :
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
      psiFullProdBin L {eta0Bin M L with P1 := fun a x => (eta0Bin M L).P1 a x + t * d a x}
        k o ∂observationLaw M) 0 0 := by
  have heq : (fun t : ℝ => ∫ o : Obs X Z,
      psiFullProdBin L {eta0Bin M L with P1 := fun a x => (eta0Bin M L).P1 a x + t * d a x}
        k o ∂observationLaw M) =
      (fun _ : ℝ => ∫ o : Obs X Z, psiFullProdBin L (eta0Bin M L) k o ∂observationLaw M) := by
    funext t
    exact population_binary_full_product_regression_integral_path M L cpi hoverlap
      d k hd hs hp hm hb hC hD t
  rw [heq]
  exact hasDerivAt_const 0 _

end Papers.TbsPrteOptimalTransport
