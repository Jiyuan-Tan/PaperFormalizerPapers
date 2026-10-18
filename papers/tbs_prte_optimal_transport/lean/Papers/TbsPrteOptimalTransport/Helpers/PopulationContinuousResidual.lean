module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationTreatmentResidual
/-! Centering the continuous-outcome corrections under the selected conditional law. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set
open scoped Classical

-- Normalization and pushforward recover the selected-cell average, also
-- on zero-mass cells. This is the conditional mean used by the score.
-- @node: normalized_selected_mean_eq_average
/-- If [the outcome transformation is measurable](hyp:hg), [its integral under the
normalized outcome law for treated observations with instruments in the selected set
equals its average over that cell under the original joint law](goal). -/
lemma normalized_selected_mean_eq_average {Z : Type*} [MeasurableSpace Z]
    (ν : Measure (ℝ × ℝ × Z)) (D : Set Z) (g : ℝ → ℝ)
    (hg : Measurable g) :
    (∫ y, g y ∂((ν.restrict {a | a.2.1 = 1 ∧ a.2.2 ∈ D}) univ)⁻¹ •
      (ν.restrict {a | a.2.1 = 1 ∧ a.2.2 ∈ D}).map Prod.fst) =
    ⨍ a in {a : ℝ × ℝ × Z | a.2.1 = 1 ∧ a.2.2 ∈ D}, g a.1 ∂ν := by
  rw [integral_smul_measure, integral_map measurable_fst.aemeasurable
    hg.aestronglyMeasurable, average_eq, ENNReal.toReal_inv]
  rfl

-- Binary treatment turns the W-weighted residual into selection on W = 1.
-- The selected regression centers it exactly, without an overlap premise.
-- @node: selected_treatment_residual_integral_zero
/-- If [the instrument selection set is measurable](hyp:hD), [the outcome
transformation is measurable](hyp:hg), and [treatment is almost surely zero or
one](hyp:hW), [the selected treatment-weighted outcome transformation, centered at
its selected treated mean and divided by any constant, has integral zero](goal). -/
lemma selected_treatment_residual_integral_zero {Z : Type*} [MeasurableSpace Z]
    (ν : Measure (ℝ × ℝ × Z)) [IsFiniteMeasure ν]
    (D : Set Z) (hD : MeasurableSet D) (g : ℝ → ℝ) (hg : Measurable g)
    (hW : ∀ᵐ a ∂ν, a.2.1 = 0 ∨ a.2.1 = 1) (c : ℝ) :
    (∫ a : ℝ × ℝ × Z, indicator (a.2.2 ∈ D) * a.2.1 / c *
      (g a.1 - ∫ y, g y ∂((ν.restrict {a | a.2.1 = 1 ∧ a.2.2 ∈ D}) univ)⁻¹ •
        (ν.restrict {a | a.2.1 = 1 ∧ a.2.2 ∈ D}).map Prod.fst) ∂ν) = 0 := by
  let E : Set (ℝ × ℝ × Z) := {a | a.2.1 = 1 ∧ a.2.2 ∈ D}
  have hE : MeasurableSet E :=
    (measurableSet_eq_fun measurable_snd.fst measurable_const).inter
      (hD.preimage measurable_snd.snd)
  rw [normalized_selected_mean_eq_average ν D g hg]
  have hid : (fun a : ℝ × ℝ × Z => indicator (a.2.2 ∈ D) * a.2.1 / c *
      (g a.1 - ⨍ b in E, g b.1 ∂ν)) =ᵐ[ν]
      (fun a => c⁻¹ * E.indicator (fun a => g a.1 - ⨍ b in E, g b.1 ∂ν) a) := by
    filter_upwards [hW] with a ha
    rcases ha with ha | ha <;> by_cases hz : a.2.2 ∈ D <;>
      simp [ha, hz, E, indicator, Set.indicator, div_eq_mul_inv]
  rw [integral_congr_ae hid, integral_const_mul, integral_indicator hE,
    integral_sub_average, mul_zero]

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- The conditional law inherits binary treatment from the model itself.
-- @node: population_joint_treatment_binary
/-- [For almost every covariate value, treatment is zero or one almost surely under
the conditional joint law of outcome, treatment, and instrument](goal). -/
lemma population_joint_treatment_binary :
    ∀ᵐ x ∂xLaw M, ∀ᵐ a ∂condDistrib
      (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure x,
      a.2.1 = 0 ∨ a.2.1 = 1 := by
  haveI : IsProbabilityMeasure (xLaw M) := by
    unfold xLaw
    exact Measure.isProbabilityMeasure_map M.measX.aemeasurable
  apply Measure.ae_ae_of_ae_compProd (μ := xLaw M)
    (κ := condDistrib (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure)
    (p := fun p : X × (ℝ × ℝ × Z) => p.2.2.1 = 0 ∨ p.2.2.1 = 1)
  change ∀ᵐ p ∂(M.law.toMeasure.map M.Xv) ⊗ₘ
    condDistrib (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure,
    p.2.2.1 = 0 ∨ p.2.2.1 = 1
  rw [compProd_map_condDistrib (M.measY.prodMk (M.measW.prodMk M.measZ)).aemeasurable]
  apply (ae_map_iff (M.measX.prodMk
    (M.measY.prodMk (M.measW.prodMk M.measZ))).aemeasurable (by
      exact (measurableSet_eq_fun measurable_snd.snd.fst measurable_const).union
        (measurableSet_eq_fun measurable_snd.snd.fst measurable_const))).mpr
  exact Filter.Eventually.of_forall M.rangeW

-- @node: population_selected_treatment_kernel_zero
/-- If [the outcome transformation is measurable at every covariate value](hyp:hg),
[its residual about the selected treated mean, weighted by selected treatment and
divided by a covariate-dependent scale, has conditional integral zero for almost
every covariate value](goal). -/
lemma population_selected_treatment_kernel_zero (L : LevelData Z X) (k : ℕ)
    (g : X → ℝ → ℝ) (hg : ∀ x, Measurable (g x)) (c : X → ℝ) :
    ∀ᵐ x ∂xLaw M,
      (∫ a : ℝ × ℝ × Z, indicator (a.2.2 ∈ L.S k) * a.2.1 / c x *
        (g x a.1 - ∫ y, g x y ∂treatedLaw M L k x)
        ∂condDistrib (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure x) = 0 := by
  filter_upwards [population_joint_treatment_binary M] with x hx
  exact selected_treatment_residual_integral_zero _ (L.S k : Set Z)
    (L.S k).finite_toSet.measurableSet (g x) (hg x) hx (c x)

-- The full treated-outcome regression is a genuine selected conditional mean.
-- @node: population_continuous_full_outcome_kernel_zero
/-- [The outcome residual about the full treated mean at the next level, weighted
by treatment and selection into that level and divided by any covariate-dependent
scale, has conditional integral zero for almost every covariate value](goal). -/
lemma population_continuous_full_outcome_kernel_zero (L : LevelData Z X)
    (k : ℕ) (c : X → ℝ) :
    ∀ᵐ x ∂xLaw M,
      (∫ a : ℝ × ℝ × Z, indicator (a.2.2 ∈ L.S (k+1)) * a.2.1 / c x *
        (a.1 - treatedBandMean M L true true k 0 x)
        ∂condDistrib (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure x) = 0 := by
  simpa only [treatedBandMean, Bool.not_true, Bool.false_and, Bool.false_eq_true,
    if_false, Bool.true_eq, if_true] using
    population_selected_treatment_kernel_zero M L (k+1) (fun _ y => y)
      (fun _ => measurable_id) c

-- Interior estimated boundaries and the fixed lower endpoint use exactly
-- the population quantile selected in the nuisance construction.
-- @node: population_nuValue_eq_bandBoundary
/-- If [the level index is below the number of levels](hyp:hk) and [the boundary
index does not exceed the number of bands at that level](hyp:hj), [the boundary
value extracted from the true nuisance equals the population band boundary at
every covariate value](goal). -/
lemma population_nuValue_eq_bandBoundary (L : LevelData Z X)
    (k j : ℕ) (hk : k < L.K) (hj : j ≤ L.l k) (x : X) :
    nuValue M (trueNuisance M L) k j x = bandBoundary M L k j x := by
  by_cases hj0 : j = 0
  · simp [nuValue, bandBoundary, hj0]
  · have hj1 : 1 ≤ j := by omega
    simp [nuValue, hj0, hk, hj1, hj, trueNuisance]

-- @node: population_IFJ_plus_kernel_zero
/-- If [the level index is valid](hyp:hk) and [the band index is below the number
of bands at that level](hyp:hj), [the upper-level band outcome correction evaluated
at the true nuisance has conditional mean zero for almost every covariate
value](goal). -/
lemma population_IFJ_plus_kernel_zero (L : LevelData Z X)
    (k j : ℕ) (hk : k < L.K) (hj : j < L.l k) :
    ∀ᵐ x ∂xLaw M,
      (∫ a : ℝ × ℝ × Z, IFJ M L (trueNuisance M L) true k j
        (x, a.2.2, a.2.1, a.1)
        ∂condDistrib (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure x) = 0 := by
  let g : X → ℝ → ℝ := fun x y =>
    y * indicator (bandBoundary M L k j x < y ∧ y ≤ bandBoundary M L k (j+1) x)
  have hg (x : X) : Measurable (g x) := by
    dsimp only [g, indicator]
    first
    | fun_prop
    | exact measurable_id.mul
        (Measurable.ite measurableSet_Ioc measurable_const measurable_const)
  have hmean (x : X) : (∫ y, g x y ∂treatedLaw M L (k+1) x) =
      treatedBandMean M L true false k j x := by
    simp only [treatedBandMean, Bool.not_true, Bool.false_and, Bool.false_eq_true,
      if_false, Bool.true_eq, if_true]
    rw [← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ Ioc (bandBoundary M L k j x) (bandBoundary M L k (j+1) x)
    <;> simp only [mem_Ioc] at hy
    <;> simp [g, indicator, Set.indicator, mem_Ioc, hy]
  have hzero := population_selected_treatment_kernel_zero M L (k+1) g hg
    (positiveValue (trueNuisance M L).piLev (k+1))
  filter_upwards [hzero] with x hx
  have hv : meanValue (trueNuisance M L).Jplus k j x =
      treatedBandMean M L true false k j x := by
    simp [meanValue, hk, hj.le, trueNuisance]
  simpa only [IFJ, Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false,
    Bool.true_eq, if_true, population_nuValue_eq_bandBoundary M L k j hk hj.le x,
    population_nuValue_eq_bandBoundary M L k (j+1) hk (by omega) x,
    hv, ← hmean x, g] using hx

-- @node: population_IFJ_minus_kernel_zero
/-- If [the level index is valid](hyp:hk) and [the band index is below the number
of bands at that level](hyp:hj), [the lower-level band outcome correction evaluated
at the true nuisance has conditional mean zero for almost every covariate
value](goal). -/
lemma population_IFJ_minus_kernel_zero (L : LevelData Z X)
    (k j : ℕ) (hk : k < L.K) (hj : j < L.l k) :
    ∀ᵐ x ∂xLaw M,
      (∫ a : ℝ × ℝ × Z, IFJ M L (trueNuisance M L) false k j
        (x, a.2.2, a.2.1, a.1)
        ∂condDistrib (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure x) = 0 := by
  by_cases hk0 : k = 0
  · subst k
    simp [IFJ]
  have hk1 : 1 ≤ k := by omega
  let g : X → ℝ → ℝ := fun x y =>
    y * indicator (bandBoundary M L k j x < y ∧ y ≤ bandBoundary M L k (j+1) x)
  have hg (x : X) : Measurable (g x) := by
    dsimp only [g, indicator]
    first
    | fun_prop
    | exact measurable_id.mul
        (Measurable.ite measurableSet_Ioc measurable_const measurable_const)
  have hmean (x : X) : (∫ y, g x y ∂treatedLaw M L k x) =
      treatedBandMean M L false false k j x := by
    simp only [treatedBandMean, Bool.not_false, Bool.true_and, Bool.false_eq_true,
      Bool.true_eq, beq_iff_eq, hk0, if_false]
    rw [← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ Ioc (bandBoundary M L k j x) (bandBoundary M L k (j+1) x)
    <;> simp only [mem_Ioc] at hy
    <;> simp [g, indicator, Set.indicator, mem_Ioc, hy]
  have hzero := population_selected_treatment_kernel_zero M L k g hg
    (positiveValue (trueNuisance M L).piLev k)
  filter_upwards [hzero] with x hx
  have hv : minusMeanValue (trueNuisance M L).Jminus k j x =
      treatedBandMean M L false false k j x := by
    simp [minusMeanValue, hk1, hk, hj.le, trueNuisance]
  simpa only [IFJ, Bool.not_false, Bool.true_and, Bool.false_eq_true, Bool.true_eq,
    beq_iff_eq, hk0, if_false,
    population_nuValue_eq_bandBoundary M L k j hk hj.le x,
    population_nuValue_eq_bandBoundary M L k (j+1) hk (by omega) x,
    hv, ← hmean x, g] using hx

-- This includes the fixed lower boundary j = 0; terminal CDF values are
-- handled separately because the score fixes them at one.
-- @node: population_IFM_kernel_zero
/-- If [the level index is valid](hyp:hk) and [the boundary index does not exceed
the number of bands at that level](hyp:hj), [the boundary probability correction
on either the upper or lower side, evaluated at the true nuisance, has conditional
mean zero for almost every covariate value](goal). -/
lemma population_IFM_kernel_zero (L : LevelData Z X)
    (plus : Bool) (k j : ℕ) (hk : k < L.K) (hj : j ≤ L.l k) :
    ∀ᵐ x ∂xLaw M,
      (∫ a : ℝ × ℝ × Z, IFM M L (trueNuisance M L) plus k j
        (x, a.2.2, a.2.1, a.1)
        ∂condDistrib (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure x) = 0 := by
  let lev := if plus then k+1 else k
  let g : X → ℝ → ℝ := fun x y => indicator (y ≤ bandBoundary M L k j x)
  have hg (x : X) : Measurable (g x) := by
    dsimp only [g, indicator]
    first | fun_prop | exact Measurable.ite measurableSet_Iic measurable_const measurable_const
  have hmean (x : X) : (∫ y, g x y ∂treatedLaw M L lev x) =
      (treatedLaw M L lev x (Iic (bandBoundary M L k j x))).toReal := by
    have hid : g x = (Iic (bandBoundary M L k j x)).indicator (fun _ => (1 : ℝ)) := by
      funext y
      simp [g, indicator, Set.indicator]
    rw [hid]
    exact integral_indicator_one measurableSet_Iic
  have hzero := population_selected_treatment_kernel_zero M L lev g hg
    (positiveValue (trueNuisance M L).piLev lev)
  cases plus
  · by_cases hk0 : k = 0
    · subst k
      simp [IFM]
    have hk1 : 1 ≤ k := by omega
    filter_upwards [hzero] with x hx
    rw [hmean x] at hx
    have hv : minusBoundaryValue (trueNuisance M L).Mminus k j x =
        (treatedLaw M L k x (Iic (bandBoundary M L k j x))).toReal := by
      simp [minusBoundaryValue, hk1, hk, hj, trueNuisance, boundaryIndicatorMean, hk0]
    simpa only [IFM, Bool.not_false, Bool.true_eq, true_and, hk0, if_false,
      Bool.false_eq_true, population_nuValue_eq_bandBoundary M L k j hk hj x,
      hv, lev, g] using hx
  · filter_upwards [hzero] with x hx
    rw [hmean x] at hx
    have hv : boundaryValue (trueNuisance M L).Mplus k j x =
        (treatedLaw M L (k+1) x (Iic (bandBoundary M L k j x))).toReal := by
      simp [boundaryValue, hk, hj, trueNuisance, boundaryIndicatorMean]
    simpa only [IFM, Bool.not_true, Bool.false_eq_true, false_and, if_false,
      Bool.true_eq, if_true, population_nuValue_eq_bandBoundary M L k j hk hj x,
      hv, lev, g] using hx

-- The selected regression has a measurable version by its explicit kernel
-- construction, rather than by adding measurability to a frozen statement.
-- @node: population_treated_integral_measurable
/-- If [the outcome transformation is jointly measurable in covariates and
outcome](hyp:hg), [its integral under the selected treated outcome law is a
measurable function of covariates](goal). -/
@[fun_prop] lemma population_treated_integral_measurable (L : LevelData Z X) (k : ℕ)
    (g : X → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) :
    Measurable (fun x => ∫ y, g x y ∂treatedLaw M L k x) := by
  let C : Set (ℝ × ℝ × Z) := {a | a.2.1 = 1 ∧ a.2.2 ∈ (L.S k : Set Z)}
  have hC : MeasurableSet C :=
    (measurableSet_eq_fun measurable_snd.fst measurable_const).inter
      ((L.S k).finite_toSet.measurableSet.preimage measurable_snd.snd)
  have hG : StronglyMeasurable (fun p : X × (ℝ × ℝ × Z) =>
      C.indicator (fun a => g p.1 a.1) p.2) := by
    first
    | fun_prop
    | have he : (fun p : X × (ℝ × ℝ × Z) => C.indicator (fun a => g p.1 a.1) p.2) =
          (Prod.snd ⁻¹' C).indicator (fun p => g p.1 p.2.1) := by
        funext p
        simp [Set.indicator]
      rw [he]
      exact (hg.comp (measurable_fst.prodMk measurable_snd.fst)).stronglyMeasurable.indicator
        (hC.preimage measurable_snd)
  have hi := hG.integral_condDistrib (Y := fun s => (M.Y s, M.W s, M.Zv s))
    (X := M.Xv) (μ := M.law.toMeasure)
  have hm := (Kernel.measurable_coe
    (condDistrib (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure) hC).ennreal_toReal
  have heq : (fun x => ∫ y, g x y ∂treatedLaw M L k x) = fun x =>
      ((condDistrib (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure x C).toReal)⁻¹ *
        ∫ a, C.indicator (fun a => g x a.1) a
          ∂condDistrib (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure x := by
    funext x
    unfold treatedLaw
    rw [normalized_selected_mean_eq_average _ (L.S k : Set Z) (g x)
      (hg.of_uncurry_left), average_eq]
    simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul,
      integral_indicator hC, C]
  rw [heq]
  exact hm.inv.mul hi.measurable

-- Tower-property centering is retained under any measurable covariate weight.
-- Integrability concerns the actual residual product, not an assumed moment.
-- @node: population_selected_treatment_weighted_integral_zero
/-- If [the outcome transformation is jointly measurable](hyp:hg), [the
covariate-dependent divisor is measurable](hyp:hc), [the covariate weight is
measurable](hyp:hw), and [the weighted selected treatment residual is
integrable](hyp:hi), [that residual, centered at the selected treated mean, has
population integral zero](goal). -/
lemma population_selected_treatment_weighted_integral_zero (L : LevelData Z X) (k : ℕ)
    (g : X → ℝ → ℝ) (hg : Measurable (Function.uncurry g))
    (c w : X → ℝ) (hc : Measurable c) (hw : Measurable w)
    (hi : Integrable (fun o : Obs X Z => w o.1 *
      (indicator (o.2.1 ∈ L.S k) * o.2.2.1 / c o.1 *
        (g o.1 o.2.2.2 - ∫ y, g o.1 y ∂treatedLaw M L k o.1))) (observationLaw M)) :
    (∫ o : Obs X Z, w o.1 *
      (indicator (o.2.1 ∈ L.S k) * o.2.2.1 / c o.1 *
        (g o.1 o.2.2.2 - ∫ y, g o.1 y ∂treatedLaw M L k o.1)) ∂observationLaw M) = 0 := by
  let f : Obs X Z → ℝ := fun o => w o.1 *
    (indicator (o.2.1 ∈ L.S k) * o.2.2.1 / c o.1 *
      (g o.1 o.2.2.2 - ∫ y, g o.1 y ∂treatedLaw M L k o.1))
  have hf : Measurable f := by
    dsimp only [f]
    have hs : Measurable (fun o : Obs X Z => indicator (o.2.1 ∈ L.S k)) := by
      unfold indicator
      exact Measurable.ite ((L.S k).finite_toSet.measurableSet.preimage
        measurable_snd.fst) measurable_const measurable_const
    exact (hw.comp measurable_fst).mul
      (((hs.mul measurable_snd.snd.fst).div (hc.comp measurable_fst)).mul
        ((hg.comp (measurable_fst.prodMk measurable_snd.snd.snd)).sub
          ((population_treated_integral_measurable M L k g hg).comp measurable_fst)))
  have hobs := M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
  have hi' : Integrable (fun s => f (M.Xv s, M.Zv s, M.W s, M.Y s)) M.law.toMeasure :=
    (integrable_map_measure hf.aestronglyMeasurable hobs.aemeasurable).mp hi
  have hjoint := M.measY.prodMk (M.measW.prodMk M.measZ)
  have hpair : StronglyMeasurable (fun p : X × (ℝ × ℝ × Z) =>
      f (p.1, p.2.2.2, p.2.2.1, p.2.1)) := by
    exact hf.stronglyMeasurable.comp_measurable
      (measurable_fst.prodMk (measurable_snd.snd.snd.prodMk
        (measurable_snd.snd.fst.prodMk measurable_snd.fst)))
  have ht := condExp_prod_ae_eq_integral_condDistrib M.measX hjoint.aemeasurable hpair hi'
  have hz := ae_of_ae_map M.measX.aemeasurable
    (population_selected_treatment_kernel_zero M L k g (fun _ => hg.of_uncurry_left) c)
  have hzero : M.law.toMeasure[(fun s => f (M.Xv s, M.Zv s, M.W s, M.Y s)) |
      MeasurableSpace.comap M.Xv inferInstance] =ᵐ[M.law.toMeasure] (fun _ => (0 : ℝ)) := by
    filter_upwards [ht, hz] with s hs hz
    rw [hs]
    dsimp only [f]
    rw [integral_const_mul, hz, mul_zero]
  change (∫ o, f o ∂observationLaw M) = 0
  rw [observationLaw, integral_map hobs.aemeasurable hf.aestronglyMeasurable,
    ← integral_condExp M.measX.comap_le, integral_congr_ae hzero]
  simp

end Papers.TbsPrteOptimalTransport
