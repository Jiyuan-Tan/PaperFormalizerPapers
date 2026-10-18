module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationContinuousRanges
public import Papers.TbsPrteOptimalTransport.Helpers.GapQuantileMoments
/-! Tight outcome ranges for the population full-interval regressions.
Baseline overlap and the positive ordered propensity levels give nonzero
selected cells, so their conditional averages lie between the outcome
endpoints even when that interval does not contain zero. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

-- @node: selected_average_mem_Icc_of_mass_ne_zero
/-- For a finite measure [with nonzero total mass](hyp:hμ), if [a real-valued
function is almost everywhere strongly measurable](hyp:hg) and [lies almost
everywhere between the lower and upper bounds](hyp:hb), then [its normalized
average lies between the same bounds](goal). -/
lemma selected_average_mem_Icc_of_mass_ne_zero {B : Type*} [MeasurableSpace B]
    (μ : Measure B) [IsFiniteMeasure μ] (hμ : μ univ ≠ 0)
    (g : B → ℝ) (lo hi : ℝ) (hg : AEStronglyMeasurable g μ)
    (hb : ∀ᵐ b ∂μ, g b ∈ Icc lo hi) :
    (⨍ b, g b ∂μ) ∈ Icc lo hi := by
  have hint : Integrable g μ := by
    apply Integrable.of_bound hg (max |lo| |hi|)
    filter_upwards [hb] with b h
    rw [Real.norm_eq_abs]
    exact abs_le_max_abs_abs h.1 h.2
  have hpos : 0 < μ.real univ := ENNReal.toReal_pos hμ (measure_ne_top _ _)
  rw [average_eq, smul_eq_mul, ← div_eq_inv_mul]
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

-- @node: population_positive_level_selected_mass_ne_zero
/-- Under [the model's structural assumptions](hyp:h), [a common ordering of
baseline propensities and policy indices](hyp:hL), and [baseline overlap with
the specified positive lower bound](hyp:hov), [for almost every covariate
value, every positive level's conditional cell of treated observations with
instruments in its selected set has nonzero mass](goal). -/
lemma population_positive_level_selected_mass_ne_zero
    (h : StructuralAssumptions M) (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) :
    ∀ᵐ x ∂xLaw M, ∀ i : PositiveIndex L.K,
      (condDistrib (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure x).restrict
        {a : ℝ × ℝ × Z | a.2.1 = 1 ∧ a.2.2 ∈ (L.S i : Set Z)} univ ≠ 0 := by
  have := M.instKernel_markov
  filter_upwards [conditional_selected_submeasure_mass M h] with x hx
  intro i
  have hS : MeasurableSet (L.S i : Set Z) := (L.S i).finite_toSet.measurableSet
  have hp : 0 < L.pLev i x := by
    have hz : L.pLev 0 x = 0 := by rw [hL.1 x 0 (by omega)]; simp [pLevel]
    have hs := hL.2.2.2.2.2.2.2.1 x 0 i (by omega) i.property.2
    rwa [hz] at hs
  have hmass : M.instKernel x (L.S i : Set Z) ≠ 0 := by
    have hs := sum_measureReal_singleton (μ := M.instKernel x) (L.S i)
    have hv := hov.2 x i i.property.1 i.property.2
    change cpi ≤ ∑ z ∈ L.S i, (M.instKernel x).real {z} at hv
    rw [hs] at hv
    have hpos := hov.1.trans_le hv
    intro hz
    exact (lt_irrefl (0 : ℝ)) (by
      simpa only [measureReal_def, hz, ENNReal.toReal_zero] using hpos)
  have heq : ∀ᵐ z ∂(M.instKernel x).restrict (L.S i : Set Z),
      M.prop z x = L.pLev i x := by
    filter_upwards [ae_restrict_mem hS] with z hz
    exact (hL.2.2.2.2.2.1 x i z i.property.2).mp hz
  rw [hx _ hS, lintegral_congr_ae (heq.mono (fun z hz => by rw [hz])),
    lintegral_const, Measure.restrict_apply_univ]
  exact mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr hp) hmass

-- @node: population_positive_level_selected_integral_range
/-- Under [the structural assumptions](hyp:h), [a common ordering of baseline
propensities and policy indices](hyp:hL), and [baseline overlap with the
specified lower bound](hyp:hov), if [the outcome transformation is measurable
in outcomes at every covariate value](hyp:hg) and [takes values between the
lower and upper bounds on the outcome support](hyp:hb), then [for almost every
covariate value, its conditional treated mean at every positive level lies
between those bounds](goal). -/
lemma population_positive_level_selected_integral_range
    (h : StructuralAssumptions M) (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi)
    (g : X → ℝ → ℝ) (lo hi : ℝ)
    (hg : ∀ x, Measurable (g x))
    (hb : ∀ x y, y ∈ M.Yset → g x y ∈ Icc lo hi) :
    ∀ᵐ x ∂xLaw M, ∀ i : PositiveIndex L.K,
      (∫ y, g x y ∂treatedLaw M L i x) ∈ Icc lo hi := by
  filter_upwards [conditional_observed_outcome_supported M h,
    population_positive_level_selected_mass_ne_zero M h q L hL cpi hov] with x hx hm
  intro i
  let joint := condDistrib (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure x
  let sel := joint.restrict {a : ℝ × ℝ × Z | a.2.1 = 1 ∧ a.2.2 ∈ (L.S i : Set Z)}
  have hs : ∀ᵐ a ∂joint, a.1 ∈ M.Yset := ae_iff.mpr hx
  have hb' : ∀ᵐ a ∂sel, g x a.1 ∈ Icc lo hi :=
    (hs.filter_mono (ae_mono Measure.restrict_le_self)).mono (fun a ha => hb x a.1 ha)
  unfold treatedLaw
  rw [normalized_selected_mean_eq_average _ _ _ (hg x)]
  exact selected_average_mem_Icc_of_mass_ne_zero sel (hm i) (fun a => g x a.1)
    lo hi (by
      first | fun_prop | exact ((hg x).comp measurable_fst).aestronglyMeasurable) hb'

-- @node: population_treated_full_mean_range
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[a common ordering of baseline propensities and policy indices](hyp:hL), and
[baseline overlap with the specified lower bound](hyp:hov), if [the interval
index is below the number of levels](hyp:hk) and [the lower side is used only
at indices at least one](hyp:hminus), then [the chosen full-interval treated
mean lies between the outcome endpoints for almost every covariate
value](goal). -/
lemma population_treated_full_mean_range
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (plus : Bool) (k : ℕ) (hk : k < L.K) (hminus : plus = false → 1 ≤ k) :
    ∀ᵐ x ∂xLaw M, treatedBandMean M L plus true k 0 x ∈ Icc M.yMin M.yMax := by
  have hr := population_positive_level_selected_integral_range M h q L hL cpi hov
    (fun _ y => y) M.yMin M.yMax (fun _ => measurable_id)
    (fun _ _ hy => ⟨he.1.2 hy, he.2.2 hy⟩)
  cases plus
  · have hk0 : k ≠ 0 := by have := hminus rfl; omega
    filter_upwards [hr] with x hx
    simpa only [treatedBandMean, Bool.not_false, Bool.true_and, beq_iff_eq,
      hk0, Bool.false_eq_true, if_false, Bool.true_eq, if_true] using
      hx ⟨k, hminus rfl, hk.le⟩
  · filter_upwards [hr] with x hx
    simpa only [treatedBandMean, Bool.not_true, Bool.false_and, Bool.false_eq_true,
      if_false, Bool.true_eq, if_true] using hx ⟨k+1, by omega, by omega⟩

-- @node: population_continuous_full_nuisance_ranges
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[a common ordering of baseline propensities and policy indices](hyp:hL), and
[baseline overlap with the specified lower bound](hyp:hov), [every true upper
and lower full-interval outcome regression lies between the outcome endpoints
almost everywhere under the covariate distribution](goal). -/
lemma population_continuous_full_nuisance_ranges
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) :
    (∀ k, ∀ᵐ x ∂xLaw M, (trueNuisance M L).JfullPlus k x ∈ Icc M.yMin M.yMax) ∧
    (∀ k, ∀ᵐ x ∂xLaw M, (trueNuisance M L).JfullMinus k x ∈ Icc M.yMin M.yMax) := by
  constructor
  · intro k
    exact population_treated_full_mean_range M h he q L hL cpi hov true k k.isLt
      (by simp)
  · intro k
    exact population_treated_full_mean_range M h he q L hL cpi hov false k k.property.2
      (fun _ => k.property.1)

-- @node: population_treated_full_mean_measurable
/-- [The full-interval treated mean on either side of any interval index is
measurable as a function of covariates](goal). -/
@[fun_prop] lemma population_treated_full_mean_measurable
    (L : LevelData Z X) (plus : Bool) (k : ℕ) :
    Measurable (treatedBandMean M L plus true k 0) := by
  have hm := population_treated_integral_measurable M L (if plus then k+1 else k)
    (fun (_ : X) (y : ℝ) => y) (by fun_prop)
  change Measurable (fun x => treatedBandMean M L plus true k 0 x)
  by_cases hz : (!plus && k == 0) = true
  · simp only [treatedBandMean, if_pos hz]
    fun_prop
  · simpa only [treatedBandMean, if_neg hz, Bool.true_eq, if_true] using hm

-- @node: population_continuous_full_nuisance_memLp
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[a common ordering of baseline propensities and policy indices](hyp:hL), and
[baseline overlap with the specified lower bound](hyp:hov), [every true upper
and lower full-interval outcome regression is square-integrable under the
covariate distribution](goal). -/
lemma population_continuous_full_nuisance_memLp
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) :
    (∀ k, MemLp ((trueNuisance M L).JfullPlus k) 2 (xLaw M)) ∧
    (∀ k, MemLp ((trueNuisance M L).JfullMinus k) 2 (xLaw M)) := by
  have : IsProbabilityMeasure (xLaw M) := Measure.isProbabilityMeasure_map M.measX.aemeasurable
  have hr := population_continuous_full_nuisance_ranges M h he q L hL cpi hov
  constructor
  · intro k
    have hm : Measurable ((trueNuisance M L).JfullPlus k) := by fun_prop
    exact memLp_of_bounded (hr.1 k) hm.aestronglyMeasurable 2
  · intro k
    have hm : Measurable ((trueNuisance M L).JfullMinus k) := by fun_prop
    exact memLp_of_bounded (hr.2 k) hm.aestronglyMeasurable 2

end Papers.TbsPrteOptimalTransport
