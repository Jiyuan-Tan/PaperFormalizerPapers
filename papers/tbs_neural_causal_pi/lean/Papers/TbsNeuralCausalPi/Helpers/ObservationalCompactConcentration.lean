module
public import Papers.TbsNeuralCausalPi.Helpers.FixedLabelLatentCoordinates
public import Papers.TbsNeuralCausalPi.Helpers.ObservationalRateExponents
public import Papers.TbsNeuralCausalPi.Setup.CitedResults
public import Papers.TbsNeuralCausalPi.Helpers.FournierNormConversion
/-! # Transporting conditional latent concentration to the compact carrier

The empirical cost on the joint latent cube is exactly its cost after
embedding into the total non-Gumbel coordinate space. Thus a concentration
estimate for that finite-dimensional law suffices, with no independence
assumption on coordinates within a conditional latent draw.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

-- @node: observational_wasserstein1_subtype_map
/-- For [a measurable subset of a metric space](hyp:hS), [embedding two
probability laws on that subset into the ambient space preserves their
Wasserstein-1 distance](goal). -/
lemma observational_wasserstein1_subtype_map
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (S : Set X) (hS : MeasurableSet S)
    (mu nu : Measure S) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    wasserstein1 (mu.map Subtype.val) (nu.map Subtype.val) = wasserstein1 mu nu := by
  have he := MeasurableEmbedding.subtype_coe hS
  have := Measure.isProbabilityMeasure_map he.measurable.aemeasurable (μ := mu)
  have := Measure.isProbabilityMeasure_map he.measurable.aemeasurable (μ := nu)
  have hm : mu.map Subtype.val S = 1 := by
    rw [Measure.map_apply he.measurable hS]
    simp
  have hn : nu.map Subtype.val S = 1 := by
    rw [Measure.map_apply he.measurable hS]
    simp
  have h := Toolkit.Foundations.MeasureTheory.wasserstein1_subtype_comap
    (mu.map Subtype.val) (nu.map Subtype.val) S hS hm hn
  simpa only [wasserstein1, he.comap_map] using h

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}

-- @node: jointLatentCube_vector_empirical_wasserstein
/-- For [a nonnegative radius K bounding each latent block coordinate](hyp:K)
and [a positive sample size](hyp:hN), [the Wasserstein-1 distance from a
law on the joint latent cube to its empirical measure equals the distance
after expressing both the law and the same draws as one-norm vectors](goal). -/
lemma jointLatentCube_vector_empirical_wasserstein
    (K : ℝ≥0) (mu : ProbabilityMeasure (jointLatentCube dims K))
    {N : ℕ} (hN : 0 < N) (z : Fin N → jointLatentCube dims K) :
    wasserstein1
      ((mu : Measure (jointLatentCube dims K)).map
        (fun x : jointLatentCube dims K => jointLatentVectorEquiv dims x.val))
      (empiricalMeasure (fun i => jointLatentVectorEquiv dims (z i).val)) =
      wasserstein1 (mu : Measure _) (empiricalMeasure z) := by
  have : NeZero N := ⟨hN.ne'⟩
  have := empiricalMeasure_probability hN z
  rw [show (fun x : jointLatentCube dims K => jointLatentVectorEquiv dims x.val) =
    (jointLatentVectorEquiv dims) ∘ Subtype.val from rfl,
    ← Measure.map_map (by fun_prop) measurable_subtype_coe,
    jointLatentVectorEquiv_empirical_wasserstein,
    ← empiricalMeasure_map_eq z Subtype.val (by fun_prop)]
  exact observational_wasserstein1_subtype_map _
    (jointLatentCube_isCompact K).measurableSet _ _

-- @node: categoricalStratum_compact_vector_empirical_failure_eq
/-- Given [a nonnegative cube radius K](hyp:K) with [the model's variables
bounded at K](hyp:hK) and [a positive sample size](hyp:hN), [the probability
that the conditional latent empirical Wasserstein-1 error exceeds t is the
same on the compact latent cube and in its one-norm vector coordinates](goal). -/
lemma categoricalStratum_compact_vector_empirical_failure_eq
    (M : EuclideanSCM kind dims) (K : ℝ≥0) (hK : VariablesBoundedAt M K)
    (c : CategoricalStratum kind) {N : ℕ} (hN : 0 < N) (t : ℝ) :
    (Measure.pi (fun _ : Fin N =>
      (categoricalStratumCompactLatentLaw M K hK c : Measure (jointLatentCube dims K))))
      {z | ¬ wasserstein1 (categoricalStratumCompactLatentLaw M K hK c : Measure _)
        (empiricalMeasure z) ≤ ENNReal.ofReal t} =
    (Measure.pi (fun _ : Fin N =>
      (categoricalStratumVectorLatentLaw M K hK c : Measure (L1Vec (∑ j, dims j)))))
      {z | ¬ wasserstein1 (categoricalStratumVectorLatentLaw M K hK c : Measure _)
        (empiricalMeasure z) ≤ ENNReal.ofReal t} := by
  have hB := measurableSet_empirical_wasserstein_failure_of_compact_mass
    (categoricalStratumVectorLatentLaw M K hK c : Measure (L1Vec (∑ j, dims j)))
    (boundedCube (∑ j, dims j) K) (boundedCube_isCompact _ _)
    (categoricalStratumVectorLatentLaw_cube M K hK c) N t
  rw [categoricalStratumVectorLatentLaw, ProbabilityMeasure.toMeasure_map] at hB ⊢
  rw [← Measure.pi_map_pi (fun _ : Fin N =>
    (show Measurable ((jointLatentVectorEquiv dims) ∘
      (Subtype.val : jointLatentCube dims K → Latent dims)) by fun_prop).aemeasurable),
    Measure.map_apply (by fun_prop) hB]
  congr 1
  ext z
  change (¬ wasserstein1 _ (empiricalMeasure z) ≤ _) ↔
    (¬ wasserstein1 _
      (empiricalMeasure (fun i => jointLatentVectorEquiv dims (z i).val)) ≤ _)
  simp only [Function.comp_def]
  rw [jointLatentCube_vector_empirical_wasserstein K
    (categoricalStratumCompactLatentLaw M K hK c) hN z]

-- @node: categoricalStratum_compact_latent_tails_of_exponential_bound
/-- Given [a nonnegative cube radius K](hyp:K), [variables bounded at K](hyp:hK),
[positive total latent dimension](hyp:hd), [nonnegative stratum
prefactors](hyp:hB), [positive rates for positive-mass strata](hyp:hrate), and
[the dimension-dependent exponential empirical Wasserstein-1 bound for each
positive-mass vector latent law at every positive sample size and tolerance
between zero and one](hyp:hexp), [eventually every positive-mass stratum and
every count at least half its expected count have compact latent empirical
failure probability at the observational tolerance bounded by the stratum
prefactor times the inverse fourth power of the overall sample size](goal). -/
lemma categoricalStratum_compact_latent_tails_of_exponential_bound
    (M : EuclideanSCM kind dims) (K : ℝ≥0) (hK : VariablesBoundedAt M K)
    (hd : 0 < ∑ j, dims j) (B rate : CategoricalStratum kind → ℝ)
    (hB : ∀ c, 0 ≤ B c)
    (hrate : ∀ c,
      0 < (observationalLaw M).real (observedCategoricalStratum ⁻¹' {c}) → 0 < rate c)
    (hexp : ∀ c,
      0 < (observationalLaw M).real (observedCategoricalStratum ⁻¹' {c}) →
      ∀ N : ℕ, 0 < N → ∀ x : ℝ, 0 < x → x < 1 →
      (Measure.pi (fun _ : Fin N =>
        (categoricalStratumVectorLatentLaw M K hK c : Measure (L1Vec (∑ j, dims j)))))
        {z | ¬ wasserstein1 (categoricalStratumVectorLatentLaw M K hK c : Measure _)
          (empiricalMeasure z) ≤ ENNReal.ofReal x} ≤
        ENNReal.ofReal (B c * Real.exp (-rate c * N *
          (if (∑ j, dims j) = 1 then x^2 else if (∑ j, dims j) = 2 then
            (x / Real.log (2 + x⁻¹))^2 else x^(∑ j, dims j))))) :
    ∀ᶠ r : ℕ in atTop, ∀ c,
      0 < (observationalLaw M).real (observedCategoricalStratum ⁻¹' {c}) →
      ∀ N : ℕ, r * (observationalLaw M).real (observedCategoricalStratum ⁻¹' {c}) / 2 ≤ N →
      (Measure.pi (fun _ : Fin N =>
        (categoricalStratumCompactLatentLaw M K hK c : Measure (jointLatentCube dims K))))
        {z | ¬ wasserstein1 (categoricalStratumCompactLatentLaw M K hK c : Measure _)
          (empiricalMeasure z) ≤ ENNReal.ofReal (observationalRateScale (∑ j, dims j) r)} ≤
        ENNReal.ofReal (B c * (r : ℝ)^(-(4 : ℤ))) := by
  filter_upwards [observational_finite_strata_exponential_tail hd
    (fun c => (observationalLaw M).real (observedCategoricalStratum ⁻¹' {c}))
    rate B hrate hB, observationalRateScale_eventually_small (∑ j, dims j),
    eventually_ge_atTop (1 : ℕ)] with r hr hs hr1
  intro c hc N hN
  have hNpos : 0 < N := by
    have hrpos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    have hcount : (0 : ℝ) < N := (div_pos (mul_pos hrpos hc) (by norm_num)).trans_le hN
    exact_mod_cast hcount
  rw [categoricalStratum_compact_vector_empirical_failure_eq M K hK c hNpos]
  exact (hexp c hc N hNpos _ hs.1 hs.2).trans
    (ENNReal.ofReal_le_ofReal (hr c hc N hN))

-- @node: categoricalStratum_vector_exponential_bound_of_fournier
/-- Assuming [the Fournier–Guillin small-deviation bound](hyp:hFournierGuillin_of_gate),
given [a nonnegative cube radius K](hyp:K), [model variables bounded at K](hyp:hK),
and [positive total latent dimension](hyp:hd), [there exist nonnegative stratum
prefactors and rates positive on positive-mass strata such that each such
stratum's vector latent empirical Wasserstein-1 failure probability is bounded
by the prefactor times an exponential with exponent minus the rate times the
sample size times the squared tolerance in dimension one, the squared
logarithmically corrected tolerance in dimension two, or the dimension-th
power of the tolerance in higher dimensions, for every positive sample size
and tolerance strictly between zero and one](goal). -/
lemma categoricalStratum_vector_exponential_bound_of_fournier
    (hFournierGuillin_of_gate : FournierGuillinSmallDeviation)
    (M : EuclideanSCM kind dims) (K : ℝ≥0) (hK : VariablesBoundedAt M K)
    (hd : 0 < ∑ j, dims j) :
    ∃ B rate : CategoricalStratum kind → ℝ,
      (∀ c, 0 ≤ B c) ∧
      (∀ c, 0 < (observationalLaw M).real (observedCategoricalStratum ⁻¹' {c}) →
        0 < rate c) ∧
      (∀ c, 0 < (observationalLaw M).real (observedCategoricalStratum ⁻¹' {c}) →
        ∀ N : ℕ, 0 < N → ∀ x : ℝ, 0 < x → x < 1 →
        (Measure.pi (fun _ : Fin N =>
          (categoricalStratumVectorLatentLaw M K hK c : Measure (L1Vec (∑ j, dims j)))))
          {z | ¬ wasserstein1 (categoricalStratumVectorLatentLaw M K hK c : Measure _)
            (empiricalMeasure z) ≤ ENNReal.ofReal x} ≤
          ENNReal.ofReal (B c * Real.exp (-rate c * N *
            (if (∑ j, dims j) = 1 then x^2 else if (∑ j, dims j) = 2 then
              (x / Real.log (2 + x⁻¹))^2 else x^(∑ j, dims j))))) := by
  have h := fun c : CategoricalStratum kind => fournier_l1_exponential_bound
    hFournierGuillin_of_gate (∑ j, dims j) hd
    (categoricalStratumVectorLatentLaw M K hK c) ((∑ j, dims j) * (K : ℝ))
    (by positivity) (categoricalStratumVectorLatentLaw_ae_norm_le M K hK c)
  choose B rate hB hrate htail using h
  exact ⟨B, rate, fun c => (hB c).le, fun c _ => hrate c, fun c _ => htail c⟩

end Papers.TbsNeuralCausalPi
