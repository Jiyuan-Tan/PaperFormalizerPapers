module
public import Papers.TbsNeuralCausalPi.Helpers.WassersteinSpace
public import Papers.TbsNeuralCausalPi.Helpers.EmpiricalContrasts
public import Papers.TbsNeuralCausalPi.Helpers.EmpiricalWassersteinSteps
public import Papers.TbsNeuralCausalPi.Helpers.FiniteTableTransport
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
/-! # Measurable empirical transport errors for compactly supported laws

The empirical sample may range over the entire ambient metric space. A compact
carrier for the population law, enlarged by its finitely many sample points,
suffices for duality. Extending the dual tests gives one fixed global test class,
whose supremum is lower semicontinuous in the sample.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped ENNReal NNReal

/-- For [a nonnegative Lipschitz constant L](hyp:L), if [the readout f is
L-Lipschitz](hyp:hf), then [the Wasserstein distance between the two pushforward
probability laws is at most L times their original Wasserstein distance](goal). -/
-- @node: wasserstein1_map_lipschitz_le
lemma wasserstein1_map_lipschitz_le
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (f : X → Y) (L : ℝ≥0) (hf : LipschitzWith L f) :
    wasserstein1 (mu.map f) (nu.map f) ≤ (L : ℝ≥0∞) * wasserstein1 mu nu := by
  have hfm : Measurable f := by first | fun_prop | exact hf.continuous.measurable
  have hp : mu.prod nu ∈ couplings mu nu := by
    refine ⟨inferInstance, ?_, ?_⟩ <;> simp
  let : Nonempty (couplings mu nu) := ⟨⟨mu.prod nu, hp⟩⟩
  rw [wasserstein1_eq_couplings mu nu, ENNReal.mul_iInf (by simp)]
  refine le_iInf fun pi => ?_
  let := pi.property.1
  let F : X × X → Y × Y := fun z => (f z.1, f z.2)
  have hF : Measurable F := by fun_prop
  have hc : pi.val.map F ∈ couplings (mu.map f) (nu.map f) := by
    refine ⟨Measure.isProbabilityMeasure_map hF.aemeasurable, ?_, ?_⟩
    · rw [Measure.map_map measurable_fst hF,
        show Prod.fst ∘ F = f ∘ Prod.fst from rfl,
        ← Measure.map_map hfm measurable_fst, pi.property.2.1]
    · rw [Measure.map_map measurable_snd hF,
        show Prod.snd ∘ F = f ∘ Prod.snd from rfl,
        ← Measure.map_map hfm measurable_snd, pi.property.2.2]
  calc
    wasserstein1 (mu.map f) (nu.map f) ≤ ∫⁻ z, edist z.1 z.2 ∂pi.val.map F :=
      (wasserstein1_eq_couplings _ _).trans_le (iInf_le_of_le ⟨_, hc⟩ le_rfl)
    _ = ∫⁻ z, edist (f z.1) (f z.2) ∂pi.val := by
      rw [lintegral_map (by fun_prop) hF]
    _ ≤ ∫⁻ z : X × X, (L : ℝ≥0∞) * edist z.1 z.2 ∂pi.val :=
      lintegral_mono (fun z => hf.edist_le_mul z.1 z.2)
    _ = _ := lintegral_const_mul _ (by fun_prop)

/-- If [the sample size is positive](hyp:hN), then for [a nonnegative constant
L](hyp:L) and [an L-Lipschitz readout f](hyp:hf), [the Wasserstein distance between
the readout population law and the empirical readout law is at most L times the
original population-to-empirical Wasserstein distance](goal). -/
-- @node: empirical_pushforward_wasserstein_le
lemma empirical_pushforward_wasserstein_le
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (mu : Measure X) [IsProbabilityMeasure mu] {N : ℕ} (hN : 0 < N)
    (x : Fin N → X) (f : X → Y) (L : ℝ≥0) (hf : LipschitzWith L f) :
    wasserstein1 (mu.map f) (empiricalMeasure (fun i => f (x i))) ≤
      (L : ℝ≥0∞) * wasserstein1 mu (empiricalMeasure x) := by
  have hfm : Measurable f := by first | fun_prop | exact hf.continuous.measurable
  let := empiricalMeasure_probability hN x
  rw [← empiricalMeasure_map_eq x f hfm]
  exact wasserstein1_map_lipschitz_le mu (empiricalMeasure x) f L hf

/-- If [S is compact](hyp:hS), [the first law assigns S probability one](hyp:hmu),
and [the second law assigns S probability one](hyp:hnu), then [their Wasserstein distance
equals the supremum, over globally one-Lipschitz real tests, of the nonnegative
part of the first expectation minus the second](goal). -/
-- @node: wasserstein1_eq_iSup_global_lipschitz_of_compact_mass
lemma wasserstein1_eq_iSup_global_lipschitz_of_compact_mass
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (S : Set X) (hS : IsCompact S) (hmu : mu S = 1) (hnu : nu S = 1) :
    wasserstein1 mu nu =
      ⨆ f : {f : X → ℝ // LipschitzWith 1 f}, ENNReal.ofReal
        ((∫ x, f.val x ∂mu) - ∫ x, f.val x ∂nu) := by
  have hma : ∀ᵐ x ∂mu, x ∈ S :=
    (ae_mem_iff_measure_eq hS.measurableSet.nullMeasurableSet).mpr (by simpa using hmu)
  have hna : ∀ᵐ x ∂nu, x ∈ S :=
    (ae_mem_iff_measure_eq hS.measurableSet.nullMeasurableSet).mpr (by simpa using hnu)
  rw [wasserstein1_eq_toolkit,
    Toolkit.Foundations.MeasureTheory.wasserstein1_eq_iSup_lipschitzOn mu nu S hS hmu hnu]
  apply le_antisymm
  · apply iSup_le
    intro f
    obtain ⟨g, hg, heq⟩ := f.property.extend_real
    have hmi : (∫ x, f.val x ∂mu) = ∫ x, g x ∂mu :=
      integral_congr_ae (hma.mono (fun x hx => heq hx))
    have hni : (∫ x, f.val x ∂nu) = ∫ x, g x ∂nu :=
      integral_congr_ae (hna.mono (fun x hx => heq hx))
    change ENNReal.ofReal ((∫ x, f.val x ∂mu) - ∫ x, f.val x ∂nu) ≤ _
    rw [hmi, hni]
    exact le_iSup_of_le ⟨g, hg⟩ le_rfl
  · apply iSup_le
    intro f
    exact le_iSup_of_le ⟨f.val, f.property.lipschitzOnWith⟩ le_rfl

/-- If [the sample size is positive](hyp:hN) and [every observation belongs to
S](hyp:hx), then [the empirical measure assigns S mass one](goal). -/
-- @node: empiricalMeasure_mass_one_of_range_subset
lemma empiricalMeasure_mass_one_of_range_subset
    {X : Type*} [MeasurableSpace X] {N : ℕ} (hN : 0 < N)
    (x : Fin N → X) (S : Set X) (hx : ∀ i, x i ∈ S) :
    empiricalMeasure x S = 1 := by
  classical
  simp only [empiricalMeasure, Measure.smul_apply, Measure.coe_finsetSum,
    Finset.sum_apply, Measure.dirac_apply_of_mem (hx _),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hN.ne') (by simp)

-- @node: empirical_wasserstein_eq_iSup_global_lipschitz
/-- If [S is compact](hyp:hS), [the population law assigns S probability
one](hyp:hmu), and [the sample size is positive](hyp:hN), then [the
population-to-empirical Wasserstein distance equals the supremum over globally
one-Lipschitz real tests of the nonnegative part of the population expectation
minus the sample average](goal). -/
lemma empirical_wasserstein_eq_iSup_global_lipschitz
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (S : Set X) (hS : IsCompact S) (hmu : mu S = 1)
    {N : ℕ} (hN : 0 < N) (x : Fin N → X) :
    wasserstein1 mu (empiricalMeasure x) =
      ⨆ f : {f : X → ℝ // LipschitzWith 1 f}, ENNReal.ofReal
        ((∫ y, f.val y ∂mu) - (N : ℝ)⁻¹ * ∑ i, f.val (x i)) := by
  let := empiricalMeasure_probability hN x
  have hfull : mu (S ∪ Set.range x) = 1 := by
    apply le_antisymm (by simpa only [measure_univ] using
      (measure_mono (Set.subset_univ (S ∪ Set.range x)) :
        mu (S ∪ Set.range x) ≤ mu Set.univ))
    exact hmu ▸ measure_mono Set.subset_union_left
  rw [wasserstein1_eq_iSup_global_lipschitz_of_compact_mass mu (empiricalMeasure x)
    (S ∪ Set.range x) (hS.union (Set.finite_range x).isCompact) hfull
    (empiricalMeasure_mass_one_of_range_subset hN x _
      (fun i => Or.inr (Set.mem_range_self i)))]
  congr 1
  funext f
  rw [empiricalMeasure_integral_eq_average x f.property.continuous.measurable]

-- @node: lowerSemicontinuous_empirical_wasserstein_of_compact_mass
/-- If [S is compact](hyp:hS), [the population law assigns S probability
one](hyp:hmu), and [the sample size is positive](hyp:hN), then [the Wasserstein
distance from the population law to the empirical law is lower semicontinuous
as a function of the sample](goal). -/
lemma lowerSemicontinuous_empirical_wasserstein_of_compact_mass
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (S : Set X) (hS : IsCompact S) (hmu : mu S = 1)
    {N : ℕ} (hN : 0 < N) :
    LowerSemicontinuous (fun x : Fin N → X => wasserstein1 mu (empiricalMeasure x)) := by
  simp_rw [empirical_wasserstein_eq_iSup_global_lipschitz mu S hS hmu hN]
  apply lowerSemicontinuous_iSup
  intro f
  apply Continuous.lowerSemicontinuous
  apply ENNReal.continuous_ofReal.comp
  apply continuous_const.sub
  apply continuous_const.mul
  exact continuous_finsetSum _ (fun i _ => f.property.continuous.comp (continuous_apply i))

-- @node: measurable_empirical_wasserstein_of_compact_mass
/-- If [S is compact](hyp:hS), [the population law assigns S probability
one](hyp:hmu), and [the sample size is positive](hyp:hN), then [the Wasserstein
distance from the population law to the empirical law is a measurable function
of the sample](goal). -/
@[fun_prop] lemma measurable_empirical_wasserstein_of_compact_mass
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (S : Set X) (hS : IsCompact S) (hmu : mu S = 1)
    {N : ℕ} (hN : 0 < N) :
    Measurable (fun x : Fin N → X => wasserstein1 mu (empiricalMeasure x)) := by
  exact (lowerSemicontinuous_empirical_wasserstein_of_compact_mass mu S hS hmu hN).measurable

/-- If [S is compact](hyp:hS) and [the population law assigns S probability
one](hyp:hmu), then [the event that the population-to-empirical Wasserstein
distance exceeds the nonnegative part of t is measurable, for every sample
size](goal). -/
-- @node: measurableSet_empirical_wasserstein_failure_of_compact_mass
lemma measurableSet_empirical_wasserstein_failure_of_compact_mass
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (S : Set X) (hS : IsCompact S) (hmu : mu S = 1)
    (N : ℕ) (t : ℝ) :
    MeasurableSet {x : Fin N → X |
      ¬ wasserstein1 mu (empiricalMeasure x) ≤ ENNReal.ofReal t} := by
  by_cases hN : 0 < N
  · exact (measurableSet_le
      (measurable_empirical_wasserstein_of_compact_mass mu S hS hmu hN)
      measurable_const).compl
  · have hzero : N = 0 := by omega
    subst N
    exact (Set.toFinite _).measurableSet

/-- For a probability law on a compact latent space, if [the readout f is
continuous](hyp:hf), then [the event that its pushforward law has Wasserstein
distance from the empirical law exceeding the nonnegative part of t is
measurable, for every sample size](goal). -/
-- @node: measurableSet_empirical_wasserstein_failure_compact_pushforward
lemma measurableSet_empirical_wasserstein_failure_compact_pushforward
    {Z X : Type*} [TopologicalSpace Z] [CompactSpace Z]
    [MeasurableSpace Z] [OpensMeasurableSpace Z]
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (mu : Measure Z) [IsProbabilityMeasure mu] (f : Z → X) (hf : Continuous f)
    (N : ℕ) (t : ℝ) :
    MeasurableSet {x : Fin N → X |
      ¬ wasserstein1 (mu.map f) (empiricalMeasure x) ≤ ENNReal.ofReal t} := by
  have hfm : Measurable f := by fun_prop
  let := Measure.isProbabilityMeasure_map hfm.aemeasurable (μ := mu)
  apply measurableSet_empirical_wasserstein_failure_of_compact_mass
    (mu.map f) (Set.range f) (isCompact_range hf)
  rw [Measure.map_apply hfm (isCompact_range hf).measurableSet]
  simp only [Set.preimage_range, measure_univ]

end Papers.TbsNeuralCausalPi
