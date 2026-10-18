module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationTreatmentResidual
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
/-! Instrument-event moments from the model's conditional instrument kernel. -/
public section
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

-- @node: population_instrument_integral
/-- If [a function of the instrument and covariates is measurable](hyp:hw) and
[integrable under the observation law](hyp:hi), [its population mean equals the
covariate average of its sum over instrument values weighted by their conditional
probabilities](goal). -/
lemma population_instrument_integral (w : Z × X → ℝ) (hw : Measurable w)
    (hi : Integrable (fun o : Obs X Z => w (o.2.1, o.1)) (observationLaw M)) :
    (∫ o : Obs X Z, w (o.2.1, o.1) ∂observationLaw M) =
      ∫ x, ∑ z, instProb M z x * w (z, x) ∂xLaw M := by
  haveI := M.instKernel_markov
  let f : Obs X Z → ℝ := fun o => w (o.2.1, o.1)
  have hf : Measurable f := by
    dsimp only [f]
    fun_prop
  have hobs := M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
  have hi' : Integrable (fun s => w (M.Zv s, M.Xv s)) M.law.toMeasure :=
    (integrable_map_measure hf.aestronglyMeasurable hobs.aemeasurable).mp hi
  have hpair : StronglyMeasurable (fun p : X × Z => w (p.2, p.1)) := by
    fun_prop
  have hc := condExp_prod_ae_eq_integral_condDistrib M.measX M.measZ.aemeasurable hpair hi'
  have hver := ae_of_ae_map M.measX.aemeasurable M.instKernel_version
  have heq : M.law.toMeasure[(fun s => w (M.Zv s, M.Xv s)) |
      MeasurableSpace.comap M.Xv inferInstance] =ᵐ[M.law.toMeasure]
      (fun s => ∑ z, instProb M z (M.Xv s) * w (z, M.Xv s)) := by
    filter_upwards [hc, hver] with s hs hv
    rw [hs, ← hv, integral_fintype (Integrable.of_finite)]
    rfl
  have hsum : Measurable (fun x => ∑ z, instProb M z x * w (z, x)) := by
    apply Finset.measurable_sum
    intro z hz
    exact ((Kernel.measurable_coe _ (measurableSet_singleton z)).ennreal_toReal).mul
      (hw.comp (measurable_const.prodMk measurable_id))
  calc
    _ = ∫ s, w (M.Zv s, M.Xv s) ∂M.law.toMeasure :=
      integral_map hobs.aemeasurable hf.aestronglyMeasurable
    _ = ∫ s, M.law.toMeasure[(fun s => w (M.Zv s, M.Xv s)) |
        MeasurableSpace.comap M.Xv inferInstance] s ∂M.law.toMeasure :=
      (integral_condExp M.measX.comap_le).symm
    _ = ∫ s, ∑ z, instProb M z (M.Xv s) * w (z, M.Xv s) ∂M.law.toMeasure :=
      integral_congr_ae heq
    _ = _ := (integral_map M.measX.aemeasurable hsum.aestronglyMeasurable).symm

-- This covers every policy union and each of the two events in the signed
-- full-interval weight, without assuming a conditional score identity.
-- @node: population_instrument_event_residual_zero
/-- If [the covariate weight is measurable](hyp:hw), [its product with the
selected-instrument indicator is integrable](hyp:he), and [its product with the
conditional probability of that instrument event is integrable](hyp:hm), [the
weight times the difference between the event indicator and its conditional
probability has population integral zero](goal). -/
lemma population_instrument_event_residual_zero (C : Finset Z)
    (w : X → ℝ) (hw : Measurable w)
    (he : Integrable (fun o : Obs X Z => w o.1 * indicator (o.2.1 ∈ C))
      (observationLaw M))
    (hm : Integrable (fun o : Obs X Z => w o.1 * ∑ z ∈ C, instProb M z o.1)
      (observationLaw M)) :
    (∫ o : Obs X Z, w o.1 *
      (indicator (o.2.1 ∈ C) - ∑ z ∈ C, instProb M z o.1) ∂observationLaw M) = 0 := by
  let f : Z × X → ℝ := fun zx => w zx.2 * indicator (zx.1 ∈ C)
  have hf : Measurable f := by
    dsimp only [f]
    unfold indicator
    exact (hw.comp measurable_snd).mul
      (Measurable.ite (C.finite_toSet.measurableSet.preimage measurable_fst)
        measurable_const measurable_const)
  have hs : ∀ x, (∑ z, instProb M z x * f (z, x)) =
      w x * ∑ z ∈ C, instProb M z x := by
    intro x
    simp only [f, indicator]
    simp_rw [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    ring
  have hp := population_instrument_integral M f hf he
  simp_rw [hs] at hp
  have hmass : Measurable (fun x => w x * ∑ z ∈ C, instProb M z x) := by
    apply hw.mul
    exact Finset.measurable_sum _ (fun z _ =>
      (Kernel.measurable_coe _ (measurableSet_singleton z)).ennreal_toReal)
  have hobs := M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
  have hmap : (observationLaw M).map Prod.fst = xLaw M := by
    simpa only [observationLaw, xLaw, Function.comp_def] using
      Measure.map_map measurable_fst hobs
  have hmom : (∫ o : Obs X Z, w o.1 * ∑ z ∈ C, instProb M z o.1 ∂observationLaw M) =
      ∫ x, w x * ∑ z ∈ C, instProb M z x ∂xLaw M := by
    rw [← hmap]
    exact (integral_map measurable_fst.aemeasurable hmass.aestronglyMeasurable).symm
  simp_rw [mul_sub]
  rw [integral_sub he hm, hp, hmom, sub_self]

-- @node: population_policyProp_measurable
/-- Under [threshold crossing](hyp:h), if [the policy transformation is measurable
on unit-interval propensities and preserves that interval](hyp:hphi), [the policy
propensity is jointly measurable in instrument and covariates](goal). -/
@[fun_prop] lemma population_policyProp_measurable (h : ThresholdCrossing M)
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi) :
    Measurable (fun zx : Z × X => policyProp phi M.prop zx.1 zx.2) := by
  have hp : Measurable (fun zx : Z × X =>
      (⟨M.prop zx.1 zx.2, M.rangeProp zx.1 zx.2⟩ : Icc (0 : ℝ) 1)) := by
    first | fun_prop | exact h.2.1.subtype_mk
  exact hphi.1.comp (measurable_fst.prodMk (measurable_snd.prodMk hp))

-- Both outcome scores have this same tail. The two correction expectations
-- are obtained from the structural treatment conditional mean, and the
-- remaining instrument event is averaged using the actual instrument kernel.
-- @node: population_commonTailScore_mean
/-- Under [threshold crossing](hyp:h), [a measurable policy map preserving the
unit interval](hyp:hphi), [measurability of the candidate policy derivative at
baseline propensities](hyp:hdphi), [a positive number of levels](hyp:hK), and [a
consistent baseline and policy level ordering](hyp:hOrder), assume [the selected
policy-minus-terminal-propensity term scaled by the lower outcome endpoint is
integrable](hyp:ht), [the selected treatment residual weighted by that endpoint
and the policy derivative is integrable](hyp:hp), [the terminal assignment
residual times its tail weight is integrable](hyp:hk), and [the terminal level
propensity is measurable](hyp:hlev). Then [the mean common tail score at the true
components equals the lower outcome endpoint times the covariate average of the
conditional instrument-probability-weighted policy-minus-terminal-propensity
differences over the terminal policy instrument set](goal). -/
lemma population_commonTailScore_mean (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (ht : Integrable (fun o : Obs X Z => M.yMin *
      indicator (o.2.1 ∈ policyUnion L L.K 1) *
      (phi o.2.1 o.1 (M.prop o.2.1 o.1) - positiveValue (eta0Bin M L).pLev L.K o.1))
      (observationLaw M))
    (hp : Integrable (fun o : Obs X Z =>
      (M.yMin * indicator (o.2.1 ∈ policyUnion L L.K 1) *
        dphi o.2.1 o.1 (M.prop o.2.1 o.1)) * (o.2.2.1 - M.prop o.2.1 o.1))
      (observationLaw M))
    (hk : Integrable (fun o : Obs X Z => gammaTail M L o.1 *
      Rp L (eta0Bin M L) L.K o) (observationLaw M))
    (hlev : Measurable (L.pLev L.K)) :
    (∫ o, commonTailScore M phi dphi L M.prop (eta0Bin M L).pLev
      (eta0Bin M L).piLev (gammaTail M L) o ∂observationLaw M) =
      ∫ x, M.yMin * ∑ z ∈ policyUnion L L.K 1,
        instProb M z x * (policyProp phi M.prop z x - L.pLev L.K x) ∂xLaw M := by
  have hk0 : L.K ≠ 0 := by unfold LevelCountPos at hK; omega
  have hiK : 1 ≤ L.K ∧ L.K ≤ L.K := ⟨hK, le_rfl⟩
  have hgamma : Measurable (gammaTail M L) := by
    change Measurable (fun x => ∑ z ∈ policyUnion L L.K 1, instProb M z x)
    exact Finset.measurable_sum _ (fun z _ =>
      (Kernel.measurable_coe _ (measurableSet_singleton z)).ennreal_toReal)
  let weight : Z × X → ℝ := fun zx => M.yMin *
    indicator (zx.1 ∈ policyUnion L L.K 1) * dphi zx.1 zx.2 (M.prop zx.1 zx.2)
  have hweight : Measurable weight := by
    dsimp only [weight]
    unfold indicator
    exact (measurable_const.mul (Measurable.ite
      ((policyUnion L L.K 1).finite_toSet.measurableSet.preimage measurable_fst)
      measurable_const measurable_const)).mul hdphi
  have zp := population_treatment_weighted_integral_zero M h weight hweight hp
  have zk := population_Rp_weighted_integral_zero M h (policyProp phi M.prop) L hOrder
    L.K (gammaTail M L) hgamma hk
  have hid : ∀ o : Obs X Z,
      commonTailScore M phi dphi L M.prop (eta0Bin M L).pLev
        (eta0Bin M L).piLev (gammaTail M L) o =
      M.yMin * indicator (o.2.1 ∈ policyUnion L L.K 1) *
        (phi o.2.1 o.1 (M.prop o.2.1 o.1) - positiveValue (eta0Bin M L).pLev L.K o.1) +
      weight (o.2.1, o.1) * (o.2.2.1 - M.prop o.2.1 o.1) -
      M.yMin * (gammaTail M L o.1 * Rp L (eta0Bin M L) L.K o) := by
    intro o
    simp only [commonTailScore, Rp, if_neg hk0, weight, div_eq_mul_inv]
    ring
  simp_rw [hid]
  have hp' : Integrable (fun o : Obs X Z => weight (o.2.1, o.1) *
      (o.2.2.1 - M.prop o.2.1 o.1)) (observationLaw M) := hp
  rw [integral_sub (ht.fun_add hp') (hk.const_mul M.yMin), integral_add ht hp',
    integral_const_mul, zp, zk, mul_zero, add_zero, sub_zero]
  let f : Z × X → ℝ := fun zx => M.yMin * indicator (zx.1 ∈ policyUnion L L.K 1) *
    (policyProp phi M.prop zx.1 zx.2 - L.pLev L.K zx.2)
  have hf : Measurable f := by
    dsimp only [f]
    unfold indicator
    exact (measurable_const.mul (Measurable.ite
      ((policyUnion L L.K 1).finite_toSet.measurableSet.preimage measurable_fst)
      measurable_const measurable_const)).mul
        ((population_policyProp_measurable M h phi hphi).sub (hlev.comp measurable_snd))
  have hi : Integrable (fun o : Obs X Z => f (o.2.1, o.1)) (observationLaw M) := by
    simpa only [f, positiveValue, dif_pos hiK, eta0Bin, policyProp] using ht
  have hfint := population_instrument_integral M f hf hi
  have hs : ∀ x, (∑ z, instProb M z x * f (z, x)) =
      M.yMin * ∑ z ∈ policyUnion L L.K 1,
        instProb M z x * (policyProp phi M.prop z x - L.pLev L.K x) := by
    intro x
    simp only [f, indicator]
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    ring
  simp_rw [hs] at hfint
  simpa only [f, positiveValue, dif_pos hiK, eta0Bin, policyProp] using hfint

-- @node: population_binFullJ_measurable
/-- [The full binary outcome contrast evaluated at the true nuisance is a
measurable function of covariates at every level](goal). -/
@[fun_prop] lemma population_binFullJ_measurable (L : LevelData Z X) (k : ℕ) :
    Measurable (binFullJ L (eta0Bin M L) k) := by
  unfold binFullJ positiveValue
  split_ifs <;> first | fun_prop | exact measurable_const

-- The signed gamma coefficient remains intact: the two event plug-ins are
-- averaged using the kernel, while both selected-success residuals center.
-- @node: population_binary_full_product_mean
/-- If [the true full binary outcome contrast times the difference between the
higher-policy and higher-baseline instrument indicators is integrable](hyp:he),
and [the full instrument weight times the upper-level outcome residual
correction](hyp:hp) and [the corresponding lower-level correction](hyp:hm) are
integrable, [the population mean of the full binary product score at the true
nuisance equals the covariate average of the true full outcome contrast times
the full instrument probability weight](goal). -/
lemma population_binary_full_product_mean (L : LevelData Z X) (k : Fin L.K)
    (he : Integrable (fun o : Obs X Z => binFullJ L (eta0Bin M L) k o.1 *
      (indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k)))
      (observationLaw M))
    (hp : Integrable (fun o : Obs X Z => gammaFull M L k o.1 *
      RP L (eta0Bin M L) (k + 1) o) (observationLaw M))
    (hm : Integrable (fun o : Obs X Z => gammaFull M L k o.1 *
      RP L (eta0Bin M L) k o) (observationLaw M)) :
    (∫ o, psiFullProdBin L (eta0Bin M L) k o ∂observationLaw M) =
      ∫ x, gammaFull M L k x * binFullJ L (eta0Bin M L) k x ∂xLaw M := by
  have hgamma : Measurable (gammaFull M L k) := by
    unfold gammaFull
    apply Measurable.sub <;>
      exact Finset.measurable_sum _ (fun z _ =>
        (Kernel.measurable_coe _ (measurableSet_singleton z)).ennreal_toReal)
  have zp := population_RP_weighted_integral_zero M L (k + 1) (gammaFull M L k) hgamma hp
  have zm := population_RP_weighted_integral_zero M L k (gammaFull M L k) hgamma hm
  have hid : ∀ o : Obs X Z, psiFullProdBin L (eta0Bin M L) k o =
      binFullJ L (eta0Bin M L) k o.1 *
        (indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k)) +
      gammaFull M L k o.1 * RP L (eta0Bin M L) (k + 1) o -
      gammaFull M L k o.1 * RP L (eta0Bin M L) k o := by
    intro o
    simp only [psiFullProdBin, fullValue, dif_pos k.isLt, eta0Bin]
    ring
  simp_rw [hid]
  rw [integral_sub (he.fun_add hp) hm, integral_add he hp, zp, zm, add_zero, sub_zero]
  let f : Z × X → ℝ := fun zx => binFullJ L (eta0Bin M L) k zx.2 *
    (indicator (zx.1 ∈ higherPolicy L k) - indicator (zx.1 ∈ higherBaseline L k))
  have hf : Measurable f := by
    dsimp only [f]
    unfold indicator
    exact ((population_binFullJ_measurable M L k).comp measurable_snd).mul
      ((Measurable.ite ((higherPolicy L k).finite_toSet.measurableSet.preimage measurable_fst)
        measurable_const measurable_const).sub
      (Measurable.ite ((higherBaseline L k).finite_toSet.measurableSet.preimage measurable_fst)
        measurable_const measurable_const))
  have hsel (C : Finset Z) (x : X) :
      (∑ z, instProb M z x * (binFullJ L (eta0Bin M L) k x * indicator (z ∈ C))) =
      binFullJ L (eta0Bin M L) k x * ∑ z ∈ C, instProb M z x := by
    simp only [indicator, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    ring
  have hs : ∀ x, (∑ z, instProb M z x * f (z, x)) =
      gammaFull M L k x * binFullJ L (eta0Bin M L) k x := by
    intro x
    simp only [f, mul_sub, Finset.sum_sub_distrib, hsel, gammaFull]
    ring
  have hi := population_instrument_integral M f hf he
  simpa only [hs, f] using hi

end Papers.TbsPrteOptimalTransport
