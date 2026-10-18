module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationContinuousBounds
public import Papers.TbsPrteOptimalTransport.Helpers.QuantileIndicatorConvergence
/-! Interval ranges for the continuous population selected regressions.
The zero-mass convention is retained explicitly: selected averages lie in any
bounding interval containing zero. Truncated outcome means therefore lie in
the clipping interval used by the continuous DML nuisance construction. -/
public section
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical

-- @node: selected_average_mem_Icc_of_zero_mem
/-- For a finite measure, suppose [the lower bound is at most zero](hyp:hlo),
[the upper bound is at least zero](hyp:hhi), [the function is almost everywhere
strongly measurable](hyp:hg), and [its values lie almost everywhere between
these bounds](hyp:hb). Then [its normalized average lies between the same
bounds, including when the measure has zero mass](goal). -/
lemma selected_average_mem_Icc_of_zero_mem {B : Type*} [MeasurableSpace B]
    (μ : Measure B) [IsFiniteMeasure μ] (g : B → ℝ) (lo hi : ℝ)
    (hlo : lo ≤ 0) (hhi : 0 ≤ hi) (hg : AEStronglyMeasurable g μ)
    (hb : ∀ᵐ b ∂μ, g b ∈ Icc lo hi) :
    (⨍ b, g b ∂μ) ∈ Icc lo hi := by
  have hint : Integrable g μ := by
    apply Integrable.of_bound hg (max |lo| |hi|)
    filter_upwards [hb] with b h
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have := le_max_left |lo| |hi|
      linarith [neg_abs_le lo, h.1]
    · exact h.2.trans ((le_abs_self hi).trans (le_max_right _ _))
  rw [average_eq, smul_eq_mul, ← div_eq_inv_mul]
  by_cases hz : μ.real univ = 0
  · simpa only [hz, div_zero, mem_Icc] using And.intro hlo hhi
  have hpos : 0 < μ.real univ :=
    lt_of_le_of_ne measureReal_nonneg (Ne.symm hz)
  constructor
  · apply (le_div_iff₀ hpos).mpr
    have h := integral_mono_ae (integrable_const lo) hint (hb.mono (fun _ h => h.1))
    simpa only [integral_const, smul_eq_mul, mul_comm] using h
  · apply (div_le_iff₀ hpos).mpr
    have h := integral_mono_ae hint (integrable_const hi) (hb.mono (fun _ h => h.2))
    simpa only [integral_const, smul_eq_mul, mul_comm] using h

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: population_selected_integral_mem_Icc_of_zero_mem
/-- Under [the structural assumptions](hyp:h), if [the lower bound is at most
zero](hyp:hlo), [the upper bound is at least zero](hyp:hhi), [the outcome
transformation is measurable in outcomes at each covariate value](hyp:hg),
and [the transformation lies between these bounds on the outcome
support](hyp:hb), then [its selected treated mean at the chosen level lies
between the same bounds for almost every covariate value](goal). -/
lemma population_selected_integral_mem_Icc_of_zero_mem
    (h : StructuralAssumptions M) (L : LevelData Z X) (i : ℕ)
    (g : X → ℝ → ℝ) (lo hi : ℝ) (hlo : lo ≤ 0) (hhi : 0 ≤ hi)
    (hg : ∀ x, Measurable (g x))
    (hb : ∀ x y, y ∈ M.Yset → g x y ∈ Icc lo hi) :
    ∀ᵐ x ∂xLaw M, (∫ y, g x y ∂treatedLaw M L i x) ∈ Icc lo hi := by
  filter_upwards [conditional_observed_outcome_supported M h] with x hx
  let joint := condDistrib (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure x
  let sel := joint.restrict {a : ℝ × ℝ × Z | a.2.1 = 1 ∧ a.2.2 ∈ (L.S i : Set Z)}
  have hs : ∀ᵐ a ∂joint, a.1 ∈ M.Yset := ae_iff.mpr hx
  have hb' : ∀ᵐ a ∂sel, g x a.1 ∈ Icc lo hi :=
    (hs.filter_mono (ae_mono Measure.restrict_le_self)).mono (fun a ha => hb x a.1 ha)
  unfold treatedLaw
  rw [normalized_selected_mean_eq_average _ _ _ (hg x)]
  exact selected_average_mem_Icc_of_zero_mem sel (fun a => g x a.1) lo hi
    hlo hhi (by
      first | fun_prop | exact ((hg x).comp measurable_fst).aestronglyMeasurable) hb'

-- @node: population_treated_band_mean_range
/-- Under [the structural assumptions](hyp:h) and [known outcome
endpoints](hyp:he), [the treated outcome mean truncated to any chosen band,
on either side of an interval, lies almost everywhere between the smaller
of zero and the lower outcome endpoint and the larger of zero and the upper
outcome endpoint](goal). -/
lemma population_treated_band_mean_range
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (L : LevelData Z X) (plus : Bool) (k j : ℕ) :
    ∀ᵐ x ∂xLaw M, treatedBandMean M L plus false k j x ∈
      Icc (min 0 M.yMin) (max 0 M.yMax) := by
  by_cases hz : (!plus && k == 0) = true
  · simp only [treatedBandMean, if_pos hz]
    exact Eventually.of_forall (fun _ =>
      ⟨min_le_left _ _, le_max_left _ _⟩)
  let g : X → ℝ → ℝ := fun x y => y * indicator
    (bandBoundary M L k j x < y ∧ y ≤ bandBoundary M L k (j + 1) x)
  have hg (x : X) : Measurable (g x) := by
    dsimp only [g, indicator]
    first
    | fun_prop
    | exact measurable_id.mul
        (Measurable.ite measurableSet_Ioc measurable_const measurable_const)
  have hb x y (hy : y ∈ M.Yset) :
      g x y ∈ Icc (min 0 M.yMin) (max 0 M.yMax) := by
    dsimp only [g, indicator]
    split_ifs
    · simpa only [mul_one, mem_Icc] using And.intro
        ((min_le_right _ _).trans (he.1.2 hy))
        ((he.2.2 hy).trans (le_max_right _ _))
    · simpa only [mul_zero, mem_Icc] using And.intro (min_le_left _ _) (le_max_left _ _)
  have hr := population_selected_integral_mem_Icc_of_zero_mem M h L
    (if plus then k + 1 else k) g _ _ (min_le_left _ _) (le_max_left _ _) hg hb
  simpa only [g, treatedBandMean, if_neg hz, Bool.false_eq_true, if_false,
    continuous_band_indicator_integral_eq] using hr

-- @node: population_boundary_indicator_mean_range
/-- [The selected treated mean of the boundary indicator is between zero and
one at every covariate value, for either side and any interval and boundary
indices](goal). -/
lemma population_boundary_indicator_mean_range (L : LevelData Z X)
    (plus : Bool) (k j : ℕ) (x : X) :
    boundaryIndicatorMean M L plus k j x ∈ Icc (0 : ℝ) 1 := by
  by_cases hz : (!plus && k == 0) = true
  · simpa only [boundaryIndicatorMean, if_pos hz, mem_Icc] using
      And.intro (le_rfl : (0 : ℝ) ≤ 0) zero_le_one
  · simp only [boundaryIndicatorMean, if_neg hz]
    let := treatedLaw_isFiniteMeasure M L (if plus then k + 1 else k) x
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    exact (measureReal_mono (μ := treatedLaw M L (if plus then k + 1 else k) x)
      (Set.subset_univ _)).trans
      (treatedLaw_mass_le_one M L (if plus then k + 1 else k) x)

end Papers.TbsPrteOptimalTransport
