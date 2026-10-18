module
public import Papers.TbsPrteOptimalTransport.Helpers.RangeRegularity
/-! Measurable interval laws and their endpoint-extended quantiles. -/
public section
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

-- Untagged construction helpers, as requested by the ordered-range directive.
/-- [The quantile of a probability kernel is jointly measurable in the conditioning value
and the probability rank, when the rank lies strictly between zero and one](goal). -/
@[fun_prop] lemma measurable_kernel_interior_quantile
    {B : Type*} [MeasurableSpace B] (K : Kernel B ℝ) [IsMarkovKernel K] :
    Measurable (fun bt : B × Ioo (0 : ℝ) 1 =>
      Causalean.Stat.quantile (K bt.1) bt.2.val) := by
  refine measurable_of_Iic fun r => ?_
  have heq : (fun bt : B × Ioo (0 : ℝ) 1 =>
      Causalean.Stat.quantile (K bt.1) bt.2.val) ⁻¹' Iic r =
      {bt | bt.2.val ≤ (K bt.1 (Iic r)).toReal} := by
    ext bt
    rw [mem_preimage, mem_Iic, Causalean.Stat.quantile_le_iff
      bt.2.property.1 bt.2.property.2, cdf_eq_real]
    rfl
  rw [heq]
  exact measurableSet_le (by fun_prop)
    (((K.measurable_coe measurableSet_Iic).comp measurable_fst).ennreal_toReal)

/-- [Extending a probability kernel's quantile by fixed values at ranks zero and one,
and by zero outside the unit interval, gives a jointly measurable function of the
conditioning value and rank](goal). -/
@[fun_prop] lemma measurable_kernel_endpoint_quantile
    {B : Type*} [MeasurableSpace B] (K : Kernel B ℝ) [IsMarkovKernel K]
    (lo hi : ℝ) :
    Measurable (fun bt : B × ℝ =>
      if bt.2 = 0 then lo else if bt.2 = 1 then hi else
        if bt.2 ∈ Ioo (0 : ℝ) 1 then
          Causalean.Stat.quantile (K bt.1) bt.2 else 0) := by
  classical
  let S : Set (B × ℝ) := {bt | bt.2 ∈ Ioo (0 : ℝ) 1}
  have hS : MeasurableSet S := measurableSet_Ioo.preimage measurable_snd
  have hf : Measurable (fun bt : S =>
      Causalean.Stat.quantile (K bt.val.1) bt.val.2) := by
    exact (measurable_kernel_interior_quantile K).comp
      ((measurable_fst.comp measurable_subtype_coe).prodMk
        ((measurable_snd.comp measurable_subtype_coe).subtype_mk
          (h := fun bt : S => bt.property)))
  have hq : Measurable (fun bt : B × ℝ =>
      if bt.2 ∈ Ioo (0 : ℝ) 1 then
        Causalean.Stat.quantile (K bt.1) bt.2 else 0) := by
    exact hf.dite measurable_const hS
  exact Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const)
    measurable_const (Measurable.ite
      (measurableSet_eq_fun measurable_snd measurable_const) measurable_const hq)

/-- If [the lower interval endpoint is measurable](hyp:ha) and [the upper interval
endpoint is measurable](hyp:hb), then [mixing a kernel over the interval that excludes
its lower endpoint and includes its upper endpoint, and dividing by its length,
gives a measure that depends measurably on the conditioning value](goal). -/
@[fun_prop] lemma measurable_normalized_interval_bind
    {B : Type*} [MeasurableSpace B] (K : Kernel (ℝ × B) ℝ)
    (a b : B → ℝ) (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun x => (ENNReal.ofReal (b x - a x))⁻¹ •
      (volume.restrict (Ioc (a x) (b x))).bind (fun u => K (u, x))) := by
  classical
  refine Measure.measurable_of_measurable_coe _ fun T hT => ?_
  simp only [Measure.smul_apply, smul_eq_mul]
  have hK (x : B) : Measurable (fun u => K (u, x)) := by fun_prop
  simp_rw [Measure.bind_apply hT (hK _).aemeasurable]
  have hS : MeasurableSet {xu : B × ℝ | xu.2 ∈ Ioc (a xu.1) (b xu.1)} := by
    exact (measurableSet_lt (ha.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd (hb.comp measurable_fst))
  have hm : Measurable (fun xu : B × ℝ => K (xu.2, xu.1) T) :=
    (K.measurable_coe hT).comp measurable_swap
  have hi := (hm.indicator hS).lintegral_prod_right' (ν := volume)
  have heq (x : B) : (∫⁻ u, {xu : B × ℝ | xu.2 ∈ Ioc (a xu.1) (b xu.1)}.indicator
      (fun xu => K (xu.2, xu.1) T) (x, u)) =
      ∫⁻ u in Ioc (a x) (b x), K (u, x) T := by
    change (∫⁻ u, (Ioc (a x) (b x)).indicator (fun u => K (u, x) T) u) = _
    exact lintegral_indicator (measurableSet_Ioc (a := a x) (b := b x)) _
  simp_rw [heq] at hi
  exact ((hb.sub ha).ennreal_ofReal.inv).mul hi

/-- If [the lower endpoint is measurable](hyp:ha) and [the upper endpoint is
measurable](hyp:hb), then [there is a probability kernel equal to the uniform
interval mixture of the original probability kernel whenever the lower endpoint
is smaller than the upper endpoint, and equal to a point mass at the chosen fallback
value otherwise](goal). -/
lemma exists_normalized_interval_kernel
    {B : Type*} [MeasurableSpace B] (K : Kernel (ℝ × B) ℝ) [IsMarkovKernel K]
    (a b : B → ℝ) (ha : Measurable a) (hb : Measurable b) (y : ℝ) :
    ∃ L : Kernel B ℝ, IsMarkovKernel L ∧ ∀ x,
      L x = if a x < b x then (ENNReal.ofReal (b x - a x))⁻¹ •
        (volume.restrict (Ioc (a x) (b x))).bind (fun u => K (u, x))
        else Measure.dirac y := by
  classical
  let F := fun x => if a x < b x then (ENNReal.ofReal (b x - a x))⁻¹ •
    (volume.restrict (Ioc (a x) (b x))).bind (fun u => K (u, x))
    else Measure.dirac y
  have hF : Measurable F :=
    (measurable_normalized_interval_bind K a b ha hb).ite
      (measurableSet_lt ha hb) measurable_const
  let L : Kernel B ℝ := ⟨F, hF⟩
  have hprob (x : B) : IsProbabilityMeasure (L x) := by
    by_cases hx : a x < b x
    · constructor
      change (F x) univ = 1
      dsimp only [F]
      rw [if_pos hx]
      rw [Measure.smul_apply]
      let Kx := K.comap (fun u : ℝ => (u, x)) (by fun_prop)
      change (ENNReal.ofReal (b x - a x))⁻¹ *
        ((volume.restrict (Ioc (a x) (b x))).bind Kx) univ = 1
      rw [interval_kernel_mass Kx]
      exact ENNReal.inv_mul_cancel
        (ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hx)) ENNReal.ofReal_ne_top
    · change IsProbabilityMeasure (F x)
      dsimp only [F]
      rw [if_neg hx]
      infer_instance
  exact ⟨L, ⟨hprob⟩, fun _ => rfl⟩

end Papers.TbsPrteOptimalTransport
