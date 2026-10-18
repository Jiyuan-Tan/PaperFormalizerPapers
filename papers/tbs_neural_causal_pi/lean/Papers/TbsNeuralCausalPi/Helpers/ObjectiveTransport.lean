module
public import Papers.TbsNeuralCausalPi.Setup.Optimization
public import Papers.TbsNeuralCausalPi.Helpers.KantorovichCube
/-! # Transport control of finite intervention-averaged objectives -/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory Filter
open scoped NNReal ENNReal Topology

/-- If [the real objective is Lipschitz with constant L](hyp:hF),
[c is positive](hyp:hc), [L is at most c](hyp:hLc), [the objective is integrable
under the first measure](hyp:hmu) and [under the second measure](hyp:hnu),
[delta is nonnegative](hyp:hdelta), and [the Wasserstein distance between
the measures is at most delta](hyp:hW), then [the absolute difference
between their objective integrals is at most c times delta](goal). -/
-- @node: objective_abs_integral_sub_le_of_wasserstein
lemma objective_abs_integral_sub_le_of_wasserstein
    {X : Type*} [MeasurableSpace X] [MetricSpace X] [BorelSpace X]
    {mu nu : Measure X} {F : X → ℝ} {L : ℝ≥0} {c delta : ℝ}
    (hF : LipschitzWith L F) (hc : 0 < c) (hLc : (L : ℝ) ≤ c)
    (hmu : Integrable F mu) (hnu : Integrable F nu) (hdelta : 0 ≤ delta)
    (hW : wasserstein1 mu nu ≤ ENNReal.ofReal delta) :
    |(∫ x, F x ∂mu) - ∫ x, F x ∂nu| ≤ c * delta := by
  let f : X → ℝ := fun x => F x / c
  have hf : LipschitzWith 1 f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [f, NNReal.coe_one, one_mul, Real.dist_eq, ← sub_div,
      abs_div, abs_of_pos hc]
    apply (div_le_iff₀ hc).2
    exact (hF.dist_le_mul x y).trans (by
      rw [mul_comm (dist x y) c]
      exact mul_le_mul_of_nonneg_right hLc dist_nonneg)
  have hfm : Integrable f mu := hmu.div_const c
  have hfn : Integrable f nu := hnu.div_const c
  have hpos := Toolkit.Foundations.MeasureTheory.lipschitzContrast_le_wasserstein1
    hf hfm hfn
  have hneg := Toolkit.Foundations.MeasureTheory.lipschitzContrast_le_wasserstein1
    hf.neg hfm.neg hfn.neg
  rw [← wasserstein1_eq_toolkit] at hpos hneg
  have hp := (ENNReal.ofReal_le_ofReal_iff hdelta).mp (hpos.trans hW)
  have hn := (ENNReal.ofReal_le_ofReal_iff hdelta).mp (hneg.trans hW)
  simp only [Toolkit.Foundations.MeasureTheory.lipschitzContrast, f,
    Pi.neg_apply, integral_neg, integral_div] at hp hn
  apply abs_le.mpr
  constructor
  · have h := (div_le_iff₀ hc).mp (show
        (-(∫ x, F x ∂mu) + ∫ x, F x ∂nu) / c ≤ delta by
      simpa only [neg_div, add_div, sub_eq_add_neg, neg_neg] using hn)
    linarith
  · have h := (div_le_iff₀ hc).mp (show
        ((∫ x, F x ∂mu) - ∫ x, F x ∂nu) / c ≤ delta by
      simpa only [sub_div] using hp)
    linarith

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}

/-- If [the objective is Lipschitz with constant L](hyp:hF), [c is positive](hyp:hc),
[L is at most c](hyp:hLc), [the first model's iterated objective is defined](hyp:hM),
[the second model's iterated objective is defined](hyp:hN), [delta is
nonnegative](hyp:hdelta), and [the models' interventional laws have Wasserstein
distance at most delta for almost every intervention index](hyp:hW), then
[their intervention-averaged objective values differ in absolute value by
at most c times delta](goal). -/
-- @node: objectiveIntegral_abs_sub_le_of_interventional_transport
lemma objectiveIntegral_abs_sub_le_of_interventional_transport
    (M N : EuclideanSCM kind dims) {I : Type*} [MeasurableSpace I]
    (t : I → LawIntervention kind) (muT : Measure I) [IsProbabilityMeasure muT]
    (F : Joint kind → ℝ) {L : ℝ≥0} {c delta : ℝ}
    (hF : LipschitzWith L F) (hc : 0 < c) (hLc : (L : ℝ) ≤ c)
    (hM : objectiveDefined M t muT F) (hN : objectiveDefined N t muT F)
    (hdelta : 0 ≤ delta)
    (hW : ∀ᵐ s ∂muT, wasserstein1 (interventionalLaw M (t s))
      (interventionalLaw N (t s)) ≤ ENNReal.ofReal delta) :
    |objectiveIntegral M t muT F - objectiveIntegral N t muT F| ≤ c * delta := by
  have hmeas : Measurable F := by
    first | fun_prop | exact hF.continuous.measurable
  have hpoint : ∀ᵐ s ∂muT,
      |(∫ u, F (intervenedEval M (t s).val u) ∂M.latentLaw) -
        ∫ u, F (intervenedEval N (t s).val u) ∂N.latentLaw| ≤ c * delta := by
    filter_upwards [hM.1, hN.1, hW] with s hms hns hws
    have hm : AEMeasurable (intervenedEval M (t s).val) M.latentLaw := by fun_prop
    have hn : AEMeasurable (intervenedEval N (t s).val) N.latentLaw := by fun_prop
    have hmi : Integrable F (interventionalLaw M (t s)) :=
      (integrable_map_measure hmeas.aestronglyMeasurable hm).mpr hms
    have hni : Integrable F (interventionalLaw N (t s)) :=
      (integrable_map_measure hmeas.aestronglyMeasurable hn).mpr hns
    have h := objective_abs_integral_sub_le_of_wasserstein hF hc hLc hmi hni hdelta hws
    simpa only [interventionalLaw, integral_map hm hmeas.aestronglyMeasurable,
      integral_map hn hmeas.aestronglyMeasurable] using h
  unfold objectiveIntegral
  rw [← integral_sub hM.2 hN.2]
  calc
    |∫ s, (∫ u, F (intervenedEval M (t s).val u) ∂M.latentLaw) -
        ∫ u, F (intervenedEval N (t s).val u) ∂N.latentLaw ∂muT| ≤
        ∫ s, |(∫ u, F (intervenedEval M (t s).val u) ∂M.latentLaw) -
          ∫ u, F (intervenedEval N (t s).val u) ∂N.latentLaw| ∂muT :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _, c * delta ∂muT := integral_mono_ae (hM.2.sub hN.2).abs
      (integrable_const _) hpoint
    _ = c * delta := by simp

/-- If [the objective is Lipschitz](hyp:hF), [the target model's iterated
objective is defined](hyp:hM), [the approximating models' iterated objectives
are defined for all sufficiently large indices](hyp:hN), [the transport
tolerances converge to zero](hyp:hdelta), [these tolerances are eventually
nonnegative](hyp:hnonneg), and [eventually the approximating and target
interventional laws have Wasserstein distance at most the corresponding
tolerance for almost every intervention index](hyp:hW), then
[the approximating models' intervention-averaged objective values converge
to the target model's objective value](goal). -/
-- @node: objectiveIntegral_tendsto_of_interventional_transport
lemma objectiveIntegral_tendsto_of_interventional_transport
    (M : EuclideanSCM kind dims) (N : ℕ → EuclideanSCM kind dims)
    {I : Type*} [MeasurableSpace I]
    (t : I → LawIntervention kind) (muT : Measure I) [IsProbabilityMeasure muT]
    (F : Joint kind → ℝ) {L : ℝ≥0} (hF : LipschitzWith L F)
    (hM : objectiveDefined M t muT F)
    (hN : ∀ᶠ r in atTop, objectiveDefined (N r) t muT F)
    (delta : ℕ → ℝ) (hdelta : Tendsto delta atTop (𝓝 0))
    (hnonneg : ∀ᶠ r in atTop, 0 ≤ delta r)
    (hW : ∀ᶠ r in atTop, ∀ᵐ s ∂muT,
      wasserstein1 (interventionalLaw (N r) (t s))
        (interventionalLaw M (t s)) ≤ ENNReal.ofReal (delta r)) :
    Tendsto (fun r => objectiveIntegral (N r) t muT F) atTop
      (𝓝 (objectiveIntegral M t muT F)) := by
  have hc : 0 < max (L : ℝ) 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hbound : ∀ᶠ r in atTop,
      dist (objectiveIntegral (N r) t muT F) (objectiveIntegral M t muT F) ≤
        max (L : ℝ) 1 * delta r := by
    filter_upwards [hN, hnonneg, hW] with r hnr hdr hwr
    exact objectiveIntegral_abs_sub_le_of_interventional_transport (N r) M t muT F
      hF hc (le_max_left _ _) hnr hM hdr hwr
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg)) hbound
    (by simpa using hdelta.const_mul (max (L : ℝ) 1))

end Papers.TbsNeuralCausalPi
