module
public import Papers.TbsNeuralCausalPi.Helpers.GumbelMaxClosedSimplex
public import Papers.TbsNeuralCausalPi.Helpers.ApproximationTransport
/-! # Finite laws of the canonical categorical selector

Integrating the intrinsic Gumbels gives a finite encoded law, also when
some propensity coordinates vanish. An independent private block can then
be integrated before constructing the categorical history coupling.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Given [the guarantee that the categorical label count is positive](hyp:hk) and [a nonnegative weight vector whose coordinates sum to one](hyp:hw), [the canonical selector under independent Gumbel inputs has the categorical distribution with those weights](goal). -/
-- @node: canonicalSelector_categorical_law
lemma canonicalSelector_categorical_law {k : ℕ}
    (hk : ∀ m, Sum.inr k = (Sum.inr m : NodeKind) → 0 < m)
    (w : L1Vec k) (hw : w.ofLp ∈ probabilitySimplex k) :
    (gumbelInputs k).map (fun (G : Fin k → ℝ) =>
      canonicalSelector (.inr k) hk w (WithLp.toLp 1 G)) =
        ∑ i, ENNReal.ofReal (w.ofLp i) • Measure.dirac i := by
  let s : (Fin k → ℝ) → Fin k := fun G => canonicalSelector (.inr k) hk w (WithLp.toLp 1 G)
  have hs : Measurable s := by
    apply firstArgmax_getD_measurable
    intro j
    fun_prop
  change (gumbelInputs k).map s = _
  rw [Measure.map_eq_sum _ s hs, Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  have he : s ⁻¹' {i} = {G | firstArgmax
      (fun j => extendedLog (w.ofLp j) + (G j : EReal)) = some i} := by
    ext G
    obtain ⟨j, hj⟩ := firstArgmax_exists (hk k rfl)
      (fun j => extendedLog (w.ofLp j) + (G j : EReal))
    change ((firstArgmax (fun j => extendedLog (w.ofLp j) + (G j : EReal))).getD
      ⟨0, hk k rfl⟩ = i) ↔ _ = some i
    rw [hj]
    simp
  rw [he, gumbel_firstArgmax_probability_nonneg w.ofLp hw.1 hw.2]

/-- Given [the guarantee that the categorical label count is positive](hyp:hk) and [a weight vector in the probability simplex](hyp:hw), [any encoding of the canonical Gumbel-selected label has the finite mixture distribution placing each label's weight at its encoded value](goal). -/
-- @node: canonicalSelector_encoded_law
lemma canonicalSelector_encoded_law {Y : Type*} [MeasurableSpace Y] {k : ℕ}
    (hk : ∀ m, Sum.inr k = (Sum.inr m : NodeKind) → 0 < m)
    (w : L1Vec k) (hw : w.ofLp ∈ probabilitySimplex k)
    (v : Fin k → Y) :
    (gumbelInputs k).map (fun (G : Fin k → ℝ) =>
      v (canonicalSelector (.inr k) hk w (WithLp.toLp 1 G))) =
        ∑ i, ENNReal.ofReal (w.ofLp i) • Measure.dirac (v i) := by
  have hs : Measurable (fun G : Fin k → ℝ =>
      canonicalSelector (.inr k) hk w (WithLp.toLp 1 G)) := by
    apply firstArgmax_getD_measurable
    intro j
    fun_prop
  have hv : Measurable v := measurable_of_countable v
  calc
    _ = ((gumbelInputs k).map (fun (G : Fin k → ℝ) =>
        canonicalSelector (.inr k) hk w (WithLp.toLp 1 G))).map v :=
      (Measure.map_map hv hs).symm
    _ = (∑ i, ENNReal.ofReal (w.ofLp i) • Measure.dirac i).map v :=
      congrArg (fun mu : Measure (Fin k) => mu.map v)
        (canonicalSelector_categorical_law hk w hw)
    _ = _ := by
      rw [← Measure.sum_fintype, Measure.map_sum hv.aemeasurable, Measure.sum_fintype]
      simp_rw [Measure.map_smul, Measure.map_dirac' hv]

/-- Given [a positive categorical label count](hyp:hk), [a measurable propensity vector depending on the private block](hyp:hp) that [belongs to the probability simplex almost everywhere under the block law](hyp:hps), and [an encoding measurable in the block for each label](hyp:hv), [the encoded selector under the product of the block law and independent Gumbels has the distribution obtained by integrating its conditional finite categorical laws over the block](goal). -/
-- @node: privateBlock_canonicalSelector_law
lemma privateBlock_canonicalSelector_law
    {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y] {k : ℕ}
    (rho : Measure Z) [SFinite rho]
    (hk : ∀ m, Sum.inr k = (Sum.inr m : NodeKind) → 0 < m)
    (p : Z → L1Vec k) (hp : Measurable p)
    (hps : ∀ᵐ z ∂rho, (p z).ofLp ∈ probabilitySimplex k)
    (v : Z → Fin k → Y) (hv : ∀ i, Measurable (fun z => v z i)) :
    (rho.prod (gumbelInputs k)).map (fun z => v z.1
      (canonicalSelector (.inr k) hk (p z.1) (WithLp.toLp 1 z.2))) =
      rho.bind (categoricalEncodedKernel (fun z => (p z).ofLp) (by fun_prop) v hv) := by
  let := gumbelInputs_probability k
  have hselect : Measurable (fun z : Z × (Fin k → ℝ) =>
      canonicalSelector (.inr k) hk (p z.1) (WithLp.toLp 1 z.2)) := by
    apply firstArgmax_getD_measurable
    intro j
    fun_prop
  have hv' : Measurable (fun z : Z × Fin k => v z.1 z.2) :=
    measurable_from_prod_countable_left hv
  have hF : Measurable (fun z : Z × (Fin k → ℝ) => v z.1
      (canonicalSelector (.inr k) hk (p z.1) (WithLp.toLp 1 z.2))) :=
    hv'.comp (measurable_fst.prodMk hselect)
  ext s hs
  rw [Measure.map_apply hF hs, Measure.prod_apply (hs.preimage hF),
    Measure.bind_apply hs (categoricalEncodedKernel
      (fun z => (p z).ofLp) (by fun_prop) v hv).aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [hps] with z hz
  have h := congrArg (fun mu : Measure Y => mu s)
    (canonicalSelector_encoded_law hk (p z) hz (v z))
  have hslice : Measurable (fun (G : Fin k → ℝ) =>
      v z (canonicalSelector (.inr k) hk (p z) (WithLp.toLp 1 G))) :=
    hF.comp measurable_prodMk_left
  rw [Measure.map_apply hslice hs] at h
  exact h

/-- Under a finite measure, if [the propensity vector is measurable](hyp:hp) and [belongs to the probability simplex almost everywhere](hyp:hps), [each of its coordinates is integrable](goal). -/
-- @node: simplex_coordinate_integrable
lemma simplex_coordinate_integrable
    {Z : Type*} [MeasurableSpace Z] {k : ℕ}
    (rho : Measure Z) [IsFiniteMeasure rho] (p : Z → L1Vec k) (hp : Measurable p)
    (hps : ∀ᵐ z ∂rho, (p z).ofLp ∈ probabilitySimplex k) (i : Fin k) :
    Integrable (fun z => (p z).ofLp i) rho := by
  have hm : Measurable (fun z => (p z).ofLp i) := by fun_prop
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  filter_upwards [hps] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (hz.1 i)]
  exact (mem_Icc_of_mem_stdSimplex hz i).2

/-- If [a random propensity vector is measurable](hyp:hp) and [belongs to the probability simplex almost surely](hyp:hps), [its coordinatewise expectation under the probability law also belongs to the probability simplex](goal). -/
-- @node: integral_simplex_mem
lemma integral_simplex_mem
    {Z : Type*} [MeasurableSpace Z] {k : ℕ}
    (rho : Measure Z) [IsProbabilityMeasure rho] (p : Z → L1Vec k) (hp : Measurable p)
    (hps : ∀ᵐ z ∂rho, (p z).ofLp ∈ probabilitySimplex k) :
    (fun i => ∫ z, (p z).ofLp i ∂rho) ∈ probabilitySimplex k := by
  refine ⟨fun i => integral_nonneg_of_ae (hps.mono fun z hz => hz.1 i), ?_⟩
  rw [← integral_finsetSum _ (fun i _ => simplex_coordinate_integrable rho p hp hps i)]
  calc
    (∫ z, ∑ i, (p z).ofLp i ∂rho) = ∫ _z, (1 : ℝ) ∂rho :=
      integral_congr_ae (hps.mono fun z hz => hz.2)
    _ = 1 := by simp

/-- Given [a positive categorical label count](hyp:hk) and [a measurable propensity vector depending on the private block](hyp:hp) that [belongs to the probability simplex almost surely](hyp:hps), [the encoded selector with independent Gumbel inputs has the finite mixture distribution whose weights are the expected propensities and whose atoms are the encoded labels](goal). -/
-- @node: privateBlock_canonicalSelector_mixture
lemma privateBlock_canonicalSelector_mixture
    {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y] {k : ℕ}
    (rho : Measure Z) [IsProbabilityMeasure rho]
    (hk : ∀ m, Sum.inr k = (Sum.inr m : NodeKind) → 0 < m)
    (p : Z → L1Vec k) (hp : Measurable p)
    (hps : ∀ᵐ z ∂rho, (p z).ofLp ∈ probabilitySimplex k) (v : Fin k → Y) :
    (rho.prod (gumbelInputs k)).map (fun z => v
      (canonicalSelector (.inr k) hk (p z.1) (WithLp.toLp 1 z.2))) =
      ∑ i, ENNReal.ofReal (∫ z, (p z).ofLp i ∂rho) • Measure.dirac (v i) := by
  rw [privateBlock_canonicalSelector_law rho hk p hp hps (fun _ => v)
    (fun _ => measurable_const)]
  ext s hs
  rw [Measure.bind_apply hs (categoricalEncodedKernel
    (fun z => (p z).ofLp) (by fun_prop) (fun _ => v)
    (fun _ => measurable_const)).aemeasurable]
  simp only [categoricalEncodedKernel, Kernel.coe_mk, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul]
  rw [lintegral_finsetSum _ (fun i _ => by fun_prop)]
  apply Finset.sum_congr rfl
  intro i _
  rw [lintegral_mul_const _ (by fun_prop),
    ← ofReal_integral_eq_lintegral_ofReal (simplex_coordinate_integrable rho p hp hps i)
      (hps.mono fun z hz => hz.1 i)]

end Papers.TbsNeuralCausalPi
