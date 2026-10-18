module
public import Papers.TbsNeuralCausalPi.Setup.Notation
public import Papers.TbsNeuralCausalPi.Helpers.KantorovichCube
public import Papers.TbsNeuralCausalPi.Helpers.CompactTransportContinuity
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Prokhorov
/-! # Compact-space properties of the coupling-infimum Wasserstein function
These are proved helpers for Stage 3. No metric instance is assumed or installed.
The topology on `ProbabilityMeasure` in the convergence helper is Mathlib's
weak topology.
-/
public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

-- @node: wasserstein1_symm
/-- For two probability laws on a metric space with its Borel measurable sets,
[the Wasserstein distance is unchanged when the laws are exchanged](goal). -/
lemma wasserstein1_symm {X : Type*} [MeasurableSpace X] [MetricSpace X]
    [BorelSpace X] (mu nu : ProbabilityMeasure X) :
    wasserstein1 (mu : Measure X) (nu : Measure X) =
      wasserstein1 (nu : Measure X) (mu : Measure X) := by
  have hle (a b : ProbabilityMeasure X) :
      wasserstein1 (a : Measure X) (b : Measure X) ≤
        wasserstein1 (b : Measure X) (a : Measure X) := by
    rw [wasserstein1_eq_couplings (b : Measure X) (a : Measure X)]
    refine le_iInf fun pi => ?_
    let := pi.property.1
    have hc : (pi.val.map Prod.swap) ∈ couplings (a : Measure X) (b : Measure X) := by
      refine ⟨pi.val.isProbabilityMeasure_map (by fun_prop), ?_, ?_⟩
      · rw [Measure.map_map (by fun_prop) (by fun_prop)]
        exact pi.property.2.2
      · rw [Measure.map_map (by fun_prop) (by fun_prop)]
        exact pi.property.2.1
    calc
      wasserstein1 (a : Measure X) (b : Measure X) ≤
          ∫⁻ z, edist z.1 z.2 ∂(pi.val.map Prod.swap) :=
        (wasserstein1_eq_couplings _ _).trans_le (iInf_le_of_le ⟨_, hc⟩ le_rfl)
      _ = ∫⁻ z, edist z.1 z.2 ∂pi.val := by
        change (∫⁻ z, edist z.1 z.2 ∂(pi.val.map
          (MeasurableEquiv.prodComm (α := X) (β := X)))) = _
        rw [(MeasurableEquiv.prodComm (α := X) (β := X)).measurableEmbedding.lintegral_map]
        change (∫⁻ z, edist z.2 z.1 ∂pi.val) = _
        simp only [edist_comm]
  exact le_antisymm (hle mu nu) (hle nu mu)

-- @node: wasserstein1_triangle_compact
/-- For three probability laws on a compact metric space, [the Wasserstein
distance from the first to the third is at most the distance from the first to
the second plus the distance from the second to the third](goal). -/
lemma wasserstein1_triangle_compact {X : Type*} [MeasurableSpace X] [MetricSpace X]
    [BorelSpace X] [CompactSpace X] (mu nu rho : ProbabilityMeasure X) :
    wasserstein1 (mu : Measure X) (rho : Measure X) ≤
      wasserstein1 (mu : Measure X) (nu : Measure X) +
        wasserstein1 (nu : Measure X) (rho : Measure X) := by
  simp only [wasserstein1_eq_toolkit]
  rw [Toolkit.Foundations.MeasureTheory.wasserstein1_eq_iSup_lipschitz]
  refine iSup_le fun f => ?_
  have hi (a : ProbabilityMeasure X) : Integrable f.val (a : Measure X) :=
    f.property.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsplit : Toolkit.Foundations.MeasureTheory.lipschitzContrast
      (mu : Measure X) (rho : Measure X) f.val =
      Toolkit.Foundations.MeasureTheory.lipschitzContrast
        (mu : Measure X) (nu : Measure X) f.val +
      Toolkit.Foundations.MeasureTheory.lipschitzContrast
        (nu : Measure X) (rho : Measure X) f.val := by
    unfold Toolkit.Foundations.MeasureTheory.lipschitzContrast
    ring
  rw [hsplit]
  exact ENNReal.ofReal_add_le.trans (add_le_add
    (Toolkit.Foundations.MeasureTheory.lipschitzContrast_le_wasserstein1
      f.property (hi mu) (hi nu))
    (Toolkit.Foundations.MeasureTheory.lipschitzContrast_le_wasserstein1
      f.property (hi nu) (hi rho)))

/-- If [a common carrier is compact](hyp:hS), [the first probability law gives
it full mass](hyp:hm), [the second gives it full mass](hyp:hn), and [the third
gives it full mass](hyp:hr),
[the Wasserstein distance from the first to the third is at most the sum of
the distances through the second](goal). -/
-- @node: wasserstein1_triangle_compact_mass
lemma wasserstein1_triangle_compact_mass
    {X : Type*} [MeasurableSpace X] [MetricSpace X] [BorelSpace X]
    (mu nu rho : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    [IsProbabilityMeasure rho] (S : Set X) (hS : IsCompact S)
    (hm : mu S = 1) (hn : nu S = 1) (hr : rho S = 1) :
    wasserstein1 mu rho ≤ wasserstein1 mu nu + wasserstein1 nu rho := by
  simp only [wasserstein1_eq_toolkit]
  rw [Toolkit.Foundations.MeasureTheory.wasserstein1_eq_iSup_lipschitzOn mu rho S hS hm hr,
    Toolkit.Foundations.MeasureTheory.wasserstein1_eq_iSup_lipschitzOn mu nu S hS hm hn,
    Toolkit.Foundations.MeasureTheory.wasserstein1_eq_iSup_lipschitzOn nu rho S hS hn hr]
  refine iSup_le (fun f => ?_)
  have hsplit : Toolkit.Foundations.MeasureTheory.lipschitzContrast mu rho f.val =
      Toolkit.Foundations.MeasureTheory.lipschitzContrast mu nu f.val +
      Toolkit.Foundations.MeasureTheory.lipschitzContrast nu rho f.val := by
    unfold Toolkit.Foundations.MeasureTheory.lipschitzContrast
    ring
  rw [hsplit]
  exact ENNReal.ofReal_add_le.trans
    (add_le_add (le_iSup_of_le f le_rfl) (le_iSup_of_le f le_rfl))


-- @node: integral_eq_of_wasserstein1_zero_compact
/-- On a compact metric space, if [two probability laws have zero Wasserstein
distance](hyp:hzero) and [a real-valued function is Lipschitz](hyp:hf),
[its expectations under the two laws agree](goal). -/
lemma integral_eq_of_wasserstein1_zero_compact {X : Type*}
    [MeasurableSpace X] [MetricSpace X] [BorelSpace X] [CompactSpace X]
    (mu nu : ProbabilityMeasure X)
    (hzero : wasserstein1 (mu : Measure X) (nu : Measure X) = 0)
    (f : X → ℝ) {L : ℝ≥0} (hf : LipschitzWith L f) :
    (∫ x, f x ∂(mu : Measure X)) = ∫ x, f x ∂(nu : Measure X) := by
  let c : ℝ := max (L : ℝ) 1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let g : X → ℝ := fun x => f x / c
  have hg : LipschitzWith 1 g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul, Real.dist_eq, g, ← sub_div, abs_div,
      abs_of_pos hc]
    apply (div_le_iff₀ hc).2
    calc
      |f x - f y| ≤ (L : ℝ) * dist x y := by
        simpa only [Real.dist_eq] using hf.dist_le_mul x y
      _ ≤ c * dist x y := mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg
      _ = dist x y * c := mul_comm _ _
  have hi (a : ProbabilityMeasure X) : Integrable g (a : Measure X) :=
    hg.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hle (a b : ProbabilityMeasure X)
      (hab : wasserstein1 (a : Measure X) (b : Measure X) = 0) :
      (∫ x, g x ∂(a : Measure X)) ≤ ∫ x, g x ∂(b : Measure X) := by
    have h := Toolkit.Foundations.MeasureTheory.lipschitzContrast_le_wasserstein1
      hg (hi a) (hi b)
    rw [← wasserstein1_eq_toolkit, hab] at h
    have := ENNReal.ofReal_eq_zero.mp (le_antisymm h bot_le)
    exact sub_nonpos.mp this
  have heq := le_antisymm (hle mu nu hzero)
    (hle nu mu (by rw [← wasserstein1_symm mu nu, hzero]))
  simp only [g, integral_div] at heq
  exact (div_left_inj' (ne_of_gt hc)).mp heq

-- @node: wasserstein1_eq_zero_iff_compact
/-- For probability laws on a compact metric space, [their Wasserstein distance
is zero if and only if they are the same law](goal). -/
lemma wasserstein1_eq_zero_iff_compact {X : Type*} [MeasurableSpace X] [MetricSpace X]
    [BorelSpace X] [CompactSpace X] (mu nu : ProbabilityMeasure X) :
    wasserstein1 (mu : Measure X) (nu : Measure X) = 0 ↔ mu = nu := by
  constructor
  · intro hzero
    have ht : Tendsto (fun _ : ℕ => mu) atTop (𝓝 nu) := by
      apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
      intro f _ hf
      obtain ⟨L, hL⟩ := hf
      rw [integral_eq_of_wasserstein1_zero_compact mu nu hzero f hL]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique tendsto_const_nhds ht
  · rintro rfl
    rw [wasserstein1_eq_toolkit,
      Toolkit.Foundations.MeasureTheory.wasserstein1_eq_iSup_lipschitz]
    simp only [Toolkit.Foundations.MeasureTheory.lipschitzContrast, sub_self,
      ENNReal.ofReal_zero]
    exact iSup_eq_bot.mpr (fun _ => rfl)

-- @node: wasserstein1_ne_top_compact
/-- For any two probability laws on a compact metric space, [their Wasserstein
distance is finite](goal). -/
lemma wasserstein1_ne_top_compact {X : Type*} [MeasurableSpace X] [MetricSpace X]
    [BorelSpace X] [CompactSpace X] (mu nu : ProbabilityMeasure X) :
    wasserstein1 (mu : Measure X) (nu : Measure X) ≠ ⊤ := by
  let pi := (mu : Measure X).prod (nu : Measure X)
  have hc : pi ∈ couplings (mu : Measure X) (nu : Measure X) :=
    ⟨inferInstance, by simp [pi], by simp [pi]⟩
  have hcost : (∫⁻ z : X × X, edist z.1 z.2 ∂pi) ≤ Metric.ediam (Set.univ : Set X) := by
    calc
      (∫⁻ z : X × X, edist z.1 z.2 ∂pi) ≤
          ∫⁻ _ : X × X, Metric.ediam (Set.univ : Set X) ∂pi :=
        lintegral_mono fun z => Metric.edist_le_ediam_of_mem (Set.mem_univ _) (Set.mem_univ _)
      _ = Metric.ediam (Set.univ : Set X) := by simp [pi]
  exact ne_top_of_le_ne_top isCompact_univ.isBounded.ediam_ne_top
    (((wasserstein1_eq_couplings _ _).trans_le (iInf_le_of_le ⟨pi, hc⟩ le_rfl)).trans hcost)

-- @node: tendsto_wasserstein1_iff_weak_compact
/-- On a compact metric space, [a family of probability laws approaches a fixed
law in Wasserstein distance along a given filter if and only if it converges
weakly to that law along the same filter](goal). -/
lemma tendsto_wasserstein1_iff_weak_compact {X I : Type*} [MeasurableSpace X]
    [MetricSpace X] [BorelSpace X] [CompactSpace X]
    (l : Filter I) (mu : I → ProbabilityMeasure X) (nu : ProbabilityMeasure X) :
    Tendsto (fun i => wasserstein1 (mu i : Measure X) (nu : Measure X)) l (𝓝 0) ↔
      Tendsto mu l (𝓝 nu) := by
  constructor
  · intro h
    apply tendsto_nhds_of_unique_mapClusterPt
    intro rho hrho
    have hc := hrho.continuousAt_comp (continuous_wasserstein1_right_compact nu).continuousAt
    have hz : wasserstein1 (rho : Measure X) (nu : Measure X) = 0 :=
      eq_of_nhds_neBot (hc.clusterPt.mono h).neBot
    exact (wasserstein1_eq_zero_iff_compact rho nu).mp hz
  · intro h
    have hz : wasserstein1 (nu : Measure X) (nu : Measure X) = 0 :=
      (wasserstein1_eq_zero_iff_compact nu nu).mpr rfl
    simpa only [Function.comp_def, hz] using
      ((continuous_wasserstein1_right_compact nu).tendsto nu).comp h
end Papers.TbsNeuralCausalPi
