module
public import Papers.TbsPrteOptimalTransport.Helpers.Orthogonality
public import Mathlib.MeasureTheory.Integral.Average
/-! Conditional centering of the actual population treated-success regression. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set
open scoped Classical

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: treatedSuccess_eq_selected_average
/-- For [a nonzero level](hyp:hk), [the population treated-success regression at a given
covariate equals the average of outcome times treatment over that level's instrument
set in the conditional distribution of outcome, treatment, and instrument](goal). -/
lemma treatedSuccess_eq_selected_average (L : LevelData Z X) (k : ℕ)
    (hk : k ≠ 0) (x : X) :
    treatedSuccess M L k x =
      ⨍ a in {a : ℝ × ℝ × Z | a.2.2 ∈ (L.S k : Set Z)}, a.1 * a.2.1
        ∂condDistrib (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure x := by
  simp only [treatedSuccess, if_neg hk, average_eq, measureReal_def, smul_eq_mul]

-- @node: treatedSuccess_measurable
/-- [The population treated-success regression at every level is a measurable function
of covariates](goal). -/
@[fun_prop] lemma treatedSuccess_measurable (L : LevelData Z X) (k : ℕ) :
    Measurable (treatedSuccess M L k) := by
  by_cases hk : k = 0
  · subst k
    change Measurable (fun _ : X => (0 : ℝ))
    exact measurable_const
  let C : Set (ℝ × ℝ × Z) := {a | a.2.2 ∈ (L.S k : Set Z)}
  have hC : MeasurableSet C :=
    (L.S k).finite_toSet.measurableSet.preimage (measurable_snd.comp measurable_snd)
  have hg : StronglyMeasurable (fun p : X × (ℝ × ℝ × Z) =>
      C.indicator (fun a => a.1 * a.2.1) p.2) := by
    fun_prop
  have hi := hg.integral_condDistrib (Y := fun s => (M.Y s, M.W s, M.Zv s))
    (X := M.Xv) (μ := M.law.toMeasure)
  have hm := (Kernel.measurable_coe
    (condDistrib (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure) hC).ennreal_toReal
  have heq : treatedSuccess M L k = fun x =>
      ((condDistrib (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure x C).toReal)⁻¹ *
      ∫ a, C.indicator (fun a => a.1 * a.2.1) a
        ∂condDistrib (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure x := by
    funext x
    simp only [treatedSuccess, if_neg hk, Measure.restrict_apply MeasurableSet.univ,
      univ_inter, integral_indicator hC, C]
  rw [heq]
  exact hm.inv.mul hi.measurable

-- This identity uses the defining conditional mean, including at zero-mass
-- covariate fibers. It does not postulate a conditional score moment.
-- @node: population_RP_kernel_integral_zero
/-- [At every covariate value and level, the population treated-success residual
integrates to zero under the conditional distribution of outcome, treatment, and
instrument](goal). -/
lemma population_RP_kernel_integral_zero (L : LevelData Z X)
    (k : ℕ) (x : X) :
    (∫ a : ℝ × ℝ × Z, RP L (eta0Bin M L) k (x, a.2.2, a.2.1, a.1)
      ∂condDistrib (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure x) = 0 := by
  by_cases hk : 1 ≤ k ∧ k ≤ L.K
  · have hk0 : k ≠ 0 := by omega
    let C : Set (ℝ × ℝ × Z) := {a | a.2.2 ∈ (L.S k : Set Z)}
    have hC : MeasurableSet C :=
      (L.S k).finite_toSet.measurableSet.preimage (measurable_snd.comp measurable_snd)
    have hid : (fun a : ℝ × ℝ × Z => RP L (eta0Bin M L) k (x, a.2.2, a.2.1, a.1)) =
        (fun a => (positiveValue (eta0Bin M L).piLev k x)⁻¹ *
          C.indicator (fun a => a.1 * a.2.1 - treatedSuccess M L k x) a) := by
      funext a
      simp only [RP, if_neg hk0, positiveValue, dif_pos hk, eta0Bin]
      simp [indicator, C, Set.indicator, div_eq_mul_inv]
    rw [hid, integral_const_mul, integral_indicator hC,
      treatedSuccess_eq_selected_average M L k hk0 x, integral_sub_average, mul_zero]
  · have hz : ∀ a : ℝ × ℝ × Z,
        RP L (eta0Bin M L) k (x, a.2.2, a.2.1, a.1) = 0 := by
      intro a
      by_cases hk0 : k = 0
      · simp [RP, hk0]
      · simp [RP, hk0, positiveValue, hk]
    simp_rw [hz]
    simp

-- @node: population_RP_measurable
/-- [The treated-success residual evaluated at the population binary nuisance is
measurable as a function of the observation](goal). -/
@[fun_prop] lemma population_RP_measurable (L : LevelData Z X) (k : ℕ) :
    Measurable (RP L (eta0Bin M L) k) := by
  have hpi : Measurable (fun x => (levelSetProb M L).1 k x) := by
    change Measurable (fun x => ∑ z ∈ L.S k, (M.instKernel x {z}).toReal)
    exact Finset.measurable_sum _ (fun z _ =>
      (Kernel.measurable_coe _ (measurableSet_singleton z)).ennreal_toReal)
  have hsel : MeasurableSet {o : Obs X Z | o.2.1 ∈ (L.S k : Set Z)} :=
    (L.S k).finite_toSet.measurableSet.preimage (measurable_fst.comp measurable_snd)
  have hi : Measurable (fun o : Obs X Z => indicator (o.2.1 ∈ L.S k)) := by
    unfold indicator
    exact Measurable.ite hsel measurable_const measurable_const
  by_cases hk : 1 ≤ k ∧ k ≤ L.K
  · have hk0 : k ≠ 0 := by omega
    change Measurable (fun o => RP L (eta0Bin M L) k o)
    simp only [RP, if_neg hk0, positiveValue, dif_pos hk, eta0Bin]
    exact (hi.div (hpi.comp measurable_fst)).mul
      ((measurable_snd.snd.snd.mul measurable_snd.snd.fst).sub
        ((treatedSuccess_measurable M L k).comp measurable_fst))
  · have hz : RP L (eta0Bin M L) k = (fun _ => (0 : ℝ)) := by
      funext o
      by_cases hk0 : k = 0 <;> simp [RP, hk0, positiveValue, hk]
    rw [hz]
    fun_prop

-- Tower property for the constructed population regression. Covariate weights
-- may be signed; integrability is the sole analytic requirement on the product.
-- @node: population_RP_weighted_integral_zero
/-- If [a covariate weight is measurable](hyp:hw) and [its product with the population
treated-success residual is integrable](hyp:hi), then [that weighted residual has
population mean zero](goal). -/
lemma population_RP_weighted_integral_zero (L : LevelData Z X) (k : ℕ)
    (w : X → ℝ) (hw : Measurable w)
    (hi : Integrable (fun o : Obs X Z => w o.1 * RP L (eta0Bin M L) k o)
      (observationLaw M)) :
    (∫ o : Obs X Z, w o.1 * RP L (eta0Bin M L) k o ∂observationLaw M) = 0 := by
  let f : Obs X Z → ℝ := fun o => w o.1 * RP L (eta0Bin M L) k o
  have hf : Measurable f := by
    dsimp only [f]
    fun_prop
  have hobs : Measurable (fun s => (M.Xv s, M.Zv s, M.W s, M.Y s)) := by
    first | fun_prop | exact M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
  have hi' : Integrable (fun s => f (M.Xv s, M.Zv s, M.W s, M.Y s)) M.law.toMeasure :=
    (integrable_map_measure hf.aestronglyMeasurable hobs.aemeasurable).mp hi
  have hjoint : Measurable (fun s => (M.Y s, M.W s, M.Zv s)) := by
    first | fun_prop | exact M.measY.prodMk (M.measW.prodMk M.measZ)
  have hpair : StronglyMeasurable (fun p : X × (ℝ × ℝ × Z) =>
      f (p.1, p.2.2.2, p.2.2.1, p.2.1)) := by
    fun_prop
  have hc := condExp_prod_ae_eq_integral_condDistrib M.measX hjoint.aemeasurable hpair hi'
  have hz : M.law.toMeasure[(fun s => f (M.Xv s, M.Zv s, M.W s, M.Y s)) |
      MeasurableSpace.comap M.Xv inferInstance] =ᵐ[M.law.toMeasure] (fun _ => (0 : ℝ)) := by
    filter_upwards [hc] with s hs
    rw [hs]
    dsimp only [f]
    rw [integral_const_mul, population_RP_kernel_integral_zero, mul_zero]
  change (∫ o, f o ∂observationLaw M) = 0
  calc
    _ = ∫ s, f (M.Xv s, M.Zv s, M.W s, M.Y s) ∂M.law.toMeasure :=
      integral_map hobs.aemeasurable hf.aestronglyMeasurable
    _ = ∫ s, M.law.toMeasure[(fun s => f (M.Xv s, M.Zv s, M.W s, M.Y s)) |
        MeasurableSpace.comap M.Xv inferInstance] s ∂M.law.toMeasure :=
      (integral_condExp M.measX.comap_le).symm
    _ = ∫ _ : Ω, (0 : ℝ) ∂M.law.toMeasure := integral_congr_ae hz
    _ = 0 := by simp

-- The binary full-interval component has its advertised moment, derived from
-- the selected conditional law rather than assumed as a score identity.
-- @node: population_binary_full_component_weighted_mean
/-- For [a measurable covariate weight](hyp:hw), if [the weighted full-interval binary
contrast](hyp:hJ), [the weighted upper-level treated-success residual](hyp:hp), and
[the weighted lower-level treated-success residual](hyp:hm) are integrable, then
[the weighted full-interval component score has the same population mean as the
weighted binary contrast](goal). -/
lemma population_binary_full_component_weighted_mean (L : LevelData Z X) (k : ℕ)
    (w : X → ℝ) (hw : Measurable w)
    (hJ : Integrable (fun o : Obs X Z => w o.1 * binFullJ L (eta0Bin M L) k o.1)
      (observationLaw M))
    (hp : Integrable (fun o : Obs X Z => w o.1 * RP L (eta0Bin M L) (k+1) o)
      (observationLaw M))
    (hm : Integrable (fun o : Obs X Z => w o.1 * RP L (eta0Bin M L) k o)
      (observationLaw M)) :
    (∫ o : Obs X Z, w o.1 * (binFullJ L (eta0Bin M L) k o.1 +
      RP L (eta0Bin M L) (k+1) o - RP L (eta0Bin M L) k o) ∂observationLaw M) =
      ∫ o : Obs X Z, w o.1 * binFullJ L (eta0Bin M L) k o.1 ∂observationLaw M := by
  simp_rw [mul_sub, mul_add]
  have hadd : Integrable (fun o : Obs X Z =>
      w o.1 * binFullJ L (eta0Bin M L) k o.1 + w o.1 * RP L (eta0Bin M L) (k+1) o)
      (observationLaw M) := by
    exact hJ.add hp
  rw [integral_sub hadd hm, integral_add hJ hp,
    population_RP_weighted_integral_zero M L (k+1) w hw hp,
    population_RP_weighted_integral_zero M L k w hw hm, add_zero, sub_zero]

-- The signed gamma_full direction now cancels for the actual population score
-- without a premise asserting conditional orthogonality of that score.
-- @node: population_binary_full_product_weight_orthogonality
/-- If [the weight direction at the chosen level is measurable](hyp:hd), [the population
full-interval binary product score is integrable](hyp:hbase), and [the direction times
each of the upper- and lower-level treated-success residuals is integrable](hyp:hp,hm),
then [the population score mean has derivative zero at zero when only its full-interval
product weight is perturbed in that direction](goal). -/
lemma population_binary_full_product_weight_orthogonality (L : LevelData Z X)
    (d : Fin L.K → X → ℝ) (k : Fin L.K) (hd : Measurable (d k))
    (hbase : Integrable (fun o => psiFullProdBin L (eta0Bin M L) k o) (observationLaw M))
    (hp : Integrable (fun o : Obs X Z => d k o.1 * RP L (eta0Bin M L) (k+1) o)
      (observationLaw M))
    (hm : Integrable (fun o : Obs X Z => d k o.1 * RP L (eta0Bin M L) k o)
      (observationLaw M)) :
    HasDerivAt (fun t : ℝ => ∫ o, psiFullProdBin L
      {eta0Bin M L with gammaFull := fun k x => (eta0Bin M L).gammaFull k x + t * d k x}
      k o ∂observationLaw M) 0 0 := by
  have hid : ∀ o : Obs X Z,
      (binFullJ L (eta0Bin M L) k o.1 + RP L (eta0Bin M L) (k+1) o -
        RP L (eta0Bin M L) k o) - binFullJ L (eta0Bin M L) k o.1 =
      RP L (eta0Bin M L) (k+1) o - RP L (eta0Bin M L) k o := by
    intro o
    ring
  have hres : Integrable (fun o : Obs X Z => d k o.1 *
      ((binFullJ L (eta0Bin M L) k o.1 + RP L (eta0Bin M L) (k+1) o -
        RP L (eta0Bin M L) k o) - binFullJ L (eta0Bin M L) k o.1))
      (observationLaw M) := by
    simpa only [hid, mul_sub] using hp.sub' hm
  have hz : (∫ o : Obs X Z, d k o.1 *
      ((binFullJ L (eta0Bin M L) k o.1 + RP L (eta0Bin M L) (k+1) o -
        RP L (eta0Bin M L) k o) - binFullJ L (eta0Bin M L) k o.1)
      ∂observationLaw M) = 0 := by
    simp_rw [hid, mul_sub]
    rw [integral_sub hp hm, population_RP_weighted_integral_zero M L (k+1) (d k) hd hp,
      population_RP_weighted_integral_zero M L k (d k) hd hm, sub_self]
  have hpath := product_score_weight_path (observationLaw M)
    (fun o => (eta0Bin M L).gammaFull k o.1) (fun o => d k o.1)
    (fun o => binFullJ L (eta0Bin M L) k o.1 + RP L (eta0Bin M L) (k+1) o -
      RP L (eta0Bin M L) k o)
    (fun o => binFullJ L (eta0Bin M L) k o.1)
    (fun o => indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k))
    (by simpa only [psiFullProdBin, fullValue, dif_pos k.isLt] using hbase) hres hz
  have heq : (fun t : ℝ => ∫ o, psiFullProdBin L
      {eta0Bin M L with gammaFull := fun k x => (eta0Bin M L).gammaFull k x + t * d k x}
      k o ∂observationLaw M) =
      (fun _ : ℝ => ∫ o, psiFullProdBin L (eta0Bin M L) k o ∂observationLaw M) := by
    funext t
    have hP : ∀ i o, RP L
        {eta0Bin M L with gammaFull := fun k x => (eta0Bin M L).gammaFull k x + t * d k x}
        i o = RP L (eta0Bin M L) i o := fun _ _ => rfl
    have hJ : ∀ x, binFullJ L
        {eta0Bin M L with gammaFull := fun k x => (eta0Bin M L).gammaFull k x + t * d k x}
        k x = binFullJ L (eta0Bin M L) k x := fun _ => rfl
    simpa only [psiFullProdBin, hP, hJ, fullValue, dif_pos k.isLt] using hpath t
  rw [heq]
  exact hasDerivAt_const 0 _

end Papers.TbsPrteOptimalTransport
