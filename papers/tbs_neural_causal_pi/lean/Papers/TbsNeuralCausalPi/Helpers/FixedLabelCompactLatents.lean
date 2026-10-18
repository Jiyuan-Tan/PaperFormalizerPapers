module
public import Papers.TbsNeuralCausalPi.Helpers.FixedLabelStrata
public import Papers.TbsNeuralCausalPi.Helpers.EmpiricalTransportMeasurability
/-! # Compact conditional joint latent laws for the actual categorical strata

Conditioning is performed on the actual complete categorical label, before
restricting its joint latent marginal to the bounded cube. No product structure
is asserted for this conditional law. Zero-mass labels receive a fixed Dirac
probability law solely to make the finite family total.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}

-- @node: jointLatentCube
/-- For [latent block dimensions](hyp:dims) and [a nonnegative radius](hyp:K),
define [the joint latent cube consisting of vectors whose every coordinate has
absolute value at most that radius](goal). -/
def jointLatentCube (dims : Fin b → ℕ) (K : ℝ≥0) : Set (Latent dims) :=
  {z | ∀ a, |z.ofLp a| ≤ K}

-- @node: jointLatentCube_isCompact
/-- For [any nonnegative radius](hyp:K), [the joint latent cube is compact](goal). -/
lemma jointLatentCube_isCompact (K : ℝ≥0) : IsCompact (jointLatentCube dims K) := by
  have hc := (isCompact_univ_pi
    (fun _ : Σ j, Fin (dims j) => isCompact_Icc (a := -(K : ℝ)) (b := K))).image
      (PiLp.continuous_toLp 1 _)
  convert hc using 1
  ext z
  simp only [jointLatentCube, Set.mem_ofPred_eq, abs_le, Set.mem_image]
  constructor
  · intro hz
    exact ⟨z.ofLp, fun a _ => hz a, WithLp.toLp_ofLp 1 z⟩
  · rintro ⟨x, hx, rfl⟩
    exact fun a => hx a (Set.mem_univ a)

-- @node: jointLatentCube_compactSpace
/-- For [the latent block dimensions](hyp:dims) and [a nonnegative
radius](hyp:K), equip [the joint latent cube with its compact-space
structure](goal). -/
instance jointLatentCube_compactSpace (K : ℝ≥0) :
    CompactSpace (jointLatentCube dims K) :=
  isCompact_iff_compactSpace.mp (jointLatentCube_isCompact K)

-- @node: jointLatentCube_zero
/-- For [the latent block dimensions](hyp:dims) and [a nonnegative
radius](hyp:K), define [the zero vector as a point of the joint latent
cube](goal). -/
def jointLatentCube_zero (K : ℝ≥0) : jointLatentCube dims K :=
  ⟨0, by intro a; simpa only [WithLp.ofLp_zero, Pi.zero_apply, abs_zero] using K.coe_nonneg⟩

-- @node: categoricalStratumLatentLaw
/-- For [a structural causal model](hyp:M) and [a complete categorical
label](hyp:c), define [the joint latent law obtained by conditioning the
model's exogenous law on that factual label and then discarding the intrinsic
Gumbel coordinates](goal). -/
def categoricalStratumLatentLaw (M : EuclideanSCM kind dims)
    (c : CategoricalStratum kind) : Measure (Latent dims) :=
  (cond M.latentLaw ((observedCategoricalStratum ∘
    intervenedEval M (fun _ => none)) ⁻¹' {c})).map jointNonGumbel

-- @node: categoricalStratumLatentLaw_ae_cube
/-- For [a structural causal model](hyp:M), [a nonnegative bound](hyp:K)
such that [the model's variables are bounded by it](hyp:hK), and [any complete
categorical label](hyp:c), [the conditional joint latent law assigns almost
every vector to the cube of that radius](goal). -/
lemma categoricalStratumLatentLaw_ae_cube (M : EuclideanSCM kind dims)
    (K : ℝ≥0) (hK : VariablesBoundedAt M K) (c : CategoricalStratum kind) :
    ∀ᵐ z ∂categoricalStratumLatentLaw M c, z ∈ jointLatentCube dims K :=
  categoricalStratum_conditional_latent_ae_box M K hK c

-- @node: categoricalStratumLatentLaw_probability
/-- For [a structural causal model](hyp:M) and [a complete categorical
label](hyp:c), if [that label has nonzero observational mass](hyp:hc), then
[its conditional joint latent law is a probability measure](goal). -/
lemma categoricalStratumLatentLaw_probability (M : EuclideanSCM kind dims)
    (c : CategoricalStratum kind)
    (hc : (observationalLaw M) (observedCategoricalStratum ⁻¹' {c}) ≠ 0) :
    IsProbabilityMeasure (categoricalStratumLatentLaw M c) :=
  categoricalStratum_conditional_latent_probability M c hc

-- @node: categoricalStratumLatentLaw_comap_probability
/-- For [a structural causal model](hyp:M), [a nonnegative bound](hyp:K)
such that [the model's variables are bounded by it](hyp:hK), and [a complete
categorical label](hyp:c) with [nonzero observational mass](hyp:hc),
[restricting its conditional joint latent law to the cube gives a probability
measure on that cube](goal). -/
lemma categoricalStratumLatentLaw_comap_probability (M : EuclideanSCM kind dims)
    (K : ℝ≥0) (hK : VariablesBoundedAt M K) (c : CategoricalStratum kind)
    (hc : (observationalLaw M) (observedCategoricalStratum ⁻¹' {c}) ≠ 0) :
    IsProbabilityMeasure (Measure.comap (Subtype.val : jointLatentCube dims K → Latent dims)
      (categoricalStratumLatentLaw M c)) := by
  let := categoricalStratumLatentLaw_probability M c hc
  apply (MeasurableEmbedding.subtype_coe
    (jointLatentCube_isCompact (dims := dims) K).measurableSet).isProbabilityMeasure_comap
  simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using
    categoricalStratumLatentLaw_ae_cube M K hK c

-- @node: categoricalStratumCompactLatentLaw
/-- For [a structural causal model](hyp:M), [a nonnegative bound](hyp:K),
[a guarantee that its variables are bounded by that bound](hyp:hK), and
[a complete categorical label](hyp:c), define [a probability law on the joint
latent cube: the conditional joint latent law restricted to the cube when the
label has nonzero observational mass, and a point mass at zero otherwise](goal). -/
def categoricalStratumCompactLatentLaw (M : EuclideanSCM kind dims)
    (K : ℝ≥0) (hK : VariablesBoundedAt M K) (c : CategoricalStratum kind) :
    ProbabilityMeasure (jointLatentCube dims K) := by
  classical
  exact if hc : (observationalLaw M) (observedCategoricalStratum ⁻¹' {c}) ≠ 0 then
    ⟨Measure.comap Subtype.val (categoricalStratumLatentLaw M c),
      categoricalStratumLatentLaw_comap_probability M K hK c hc⟩
  else ⟨Measure.dirac (jointLatentCube_zero K), inferInstance⟩

-- @node: categoricalStratumCompactLatentLaw_map
/-- For [a structural causal model](hyp:M), [a nonnegative bound](hyp:K)
such that [its variables are bounded by it](hyp:hK), and [a complete categorical
label](hyp:c) with [nonzero observational mass](hyp:hc), [viewing its compact
latent law as a law on the full latent space recovers the conditional joint
latent law](goal). -/
lemma categoricalStratumCompactLatentLaw_map (M : EuclideanSCM kind dims)
    (K : ℝ≥0) (hK : VariablesBoundedAt M K) (c : CategoricalStratum kind)
    (hc : (observationalLaw M) (observedCategoricalStratum ⁻¹' {c}) ≠ 0) :
    (categoricalStratumCompactLatentLaw M K hK c :
      Measure (jointLatentCube dims K)).map Subtype.val =
      categoricalStratumLatentLaw M c := by
  classical
  unfold categoricalStratumCompactLatentLaw
  rw [dif_pos hc]
  change (Measure.comap (Subtype.val : jointLatentCube dims K → Latent dims)
    (categoricalStratumLatentLaw M c)).map Subtype.val = _
  rw [map_comap_subtype_coe (jointLatentCube_isCompact K).measurableSet]
  exact Measure.restrict_eq_self_of_ae_mem (categoricalStratumLatentLaw_ae_cube M K hK c)

-- @node: categoricalStratumCompactLatentLaw_zero_mass
/-- For [a structural causal model](hyp:M), [a nonnegative bound](hyp:K)
such that [its variables are bounded by it](hyp:hK), and [a complete categorical
label](hyp:c) with [zero observational mass](hyp:hc), [the compact latent law
for that label is the point mass at the zero vector](goal). -/
lemma categoricalStratumCompactLatentLaw_zero_mass (M : EuclideanSCM kind dims)
    (K : ℝ≥0) (hK : VariablesBoundedAt M K) (c : CategoricalStratum kind)
    (hc : (observationalLaw M) (observedCategoricalStratum ⁻¹' {c}) = 0) :
    (categoricalStratumCompactLatentLaw M K hK c : Measure (jointLatentCube dims K)) =
      Measure.dirac (jointLatentCube_zero (dims := dims) K) := by
  classical
  unfold categoricalStratumCompactLatentLaw
  rw [dif_neg (not_not.mpr hc)]
  rfl

-- @node: categoricalStratumCompactObservation
/-- For [a structural causal model](hyp:M), [a nonnegative cube radius](hyp:K),
[a complete categorical label](hyp:c), and [a latent vector in that cube](hyp:z),
define [the complete observation obtained by fixing the categorical nodes at
that label and evaluating with this latent vector and zero intrinsic noise](goal). -/
def categoricalStratumCompactObservation (M : EuclideanSCM kind dims)
    (K : ℝ≥0) (c : CategoricalStratum kind) (z : jointLatentCube dims K) : Joint kind :=
  fixedLabelObservation M (categoricalStratumAssignment c) z.val

-- @node: categoricalStratumCompactObservation_lipschitz
/-- For [a structural causal model](hyp:M), [nonnegative cube and mechanism
bounds](hyp:K,L), [continuous mechanisms Lipschitz with the mechanism
bound](hyp:hL), and [a complete categorical label](hyp:c), [the observation
map on the latent cube with that label fixed is Lipschitz with the recursive
budget after the number of nodes squared plus the number of nodes steps](goal). -/
lemma categoricalStratumCompactObservation_lipschitz (M : EuclideanSCM kind dims)
    (K L : ℝ≥0) (hL : ContinuousMechanismsLipschitz M L) (c : CategoricalStratum kind) :
    LipschitzWith (fixedLabelLipschitzBudget M L (n * n + n))
      (categoricalStratumCompactObservation M K c) := by
  change LipschitzWith _
    (fixedLabelObservation M (categoricalStratumAssignment c) ∘ Subtype.val)
  simpa only [mul_one] using
    (categoricalStratumObservation_lipschitz M L hL c).comp
      (LipschitzWith.subtype_val (jointLatentCube dims K))

-- @node: categoricalStratum_compact_conditional_observation_law
/-- For [a structural causal model](hyp:M), [a nonnegative bound](hyp:K)
such that [its variables are bounded by it](hyp:hK), and [a complete categorical
label](hyp:c) with [nonzero observational mass](hyp:hc), [the observational law
conditional on that label is the image of its compact joint latent law under
the observation map with the label fixed](goal). -/
lemma categoricalStratum_compact_conditional_observation_law (M : EuclideanSCM kind dims)
    (K : ℝ≥0) (hK : VariablesBoundedAt M K) (c : CategoricalStratum kind)
    (hc : (observationalLaw M) (observedCategoricalStratum ⁻¹' {c}) ≠ 0) :
    cond (observationalLaw M) (observedCategoricalStratum ⁻¹' {c}) =
      (categoricalStratumCompactLatentLaw M K hK c : Measure (jointLatentCube dims K)).map
        (categoricalStratumCompactObservation M K c) := by
  rw [categoricalStratum_conditional_observation_law]
  change (categoricalStratumLatentLaw M c).map _ = _
  rw [← categoricalStratumCompactLatentLaw_map M K hK c hc,
    Measure.map_map (by fun_prop) measurable_subtype_coe]
  rfl

-- @node: categoricalStratum_measurableSet_empirical_failure
/-- For [a structural causal model](hyp:M), [nonnegative variable and mechanism
bounds](hyp:K,L), [variables bounded by the variable bound](hyp:hK),
[continuous mechanisms Lipschitz with the mechanism bound](hyp:hL), and
[a complete categorical label](hyp:c) with [nonzero observational mass](hyp:hc),
at [any sample size](hyp:N) and [any real threshold](hyp:t), [the set of samples
whose empirical law fails to be within that threshold of the conditional
observational law in Wasserstein distance of order one is measurable](goal).

Real thresholds are converted to nonnegative extended values, so negative
thresholds are treated as zero. -/
lemma categoricalStratum_measurableSet_empirical_failure (M : EuclideanSCM kind dims)
    (K L : ℝ≥0) (hK : VariablesBoundedAt M K)
    (hL : ContinuousMechanismsLipschitz M L) (c : CategoricalStratum kind)
    (hc : (observationalLaw M) (observedCategoricalStratum ⁻¹' {c}) ≠ 0)
    (N : ℕ) (t : ℝ) :
    MeasurableSet {x : Fin N → Joint kind |
      ¬ wasserstein1 (cond (observationalLaw M) (observedCategoricalStratum ⁻¹' {c}))
        (empiricalMeasure x) ≤ ENNReal.ofReal t} := by
  rw [categoricalStratum_compact_conditional_observation_law M K hK c hc]
  exact measurableSet_empirical_wasserstein_failure_compact_pushforward
    (categoricalStratumCompactLatentLaw M K hK c : Measure (jointLatentCube dims K))
    (categoricalStratumCompactObservation M K c)
    (categoricalStratumCompactObservation_lipschitz M K L hL c).continuous N t

-- @node: categoricalStratum_compact_empirical_failure_le
/-- For [a structural causal model](hyp:M), [nonnegative variable and mechanism
bounds](hyp:K,L), [variables bounded by the variable bound](hyp:hK),
[continuous mechanisms Lipschitz with the mechanism bound](hyp:hL), and
[a complete categorical label](hyp:c) with [nonzero observational mass](hyp:hc),
assume [the sample size is positive](hyp:hN) and choose [latent and observation
thresholds](hyp:s,t) such that [the recursive observation Lipschitz budget
times the latent threshold is at most the observation threshold](hyp:hst).
Then [the probability that an independent sample from the conditional
observational law exceeds its Wasserstein threshold is at most the analogous
failure probability for an independent sample of the same size from the
compact joint latent law at the latent threshold](goal).

Wasserstein distance has order one; real thresholds are converted to
nonnegative extended values, treating negative thresholds as zero. -/
lemma categoricalStratum_compact_empirical_failure_le (M : EuclideanSCM kind dims)
    (K L : ℝ≥0) (hK : VariablesBoundedAt M K)
    (hL : ContinuousMechanismsLipschitz M L) (c : CategoricalStratum kind)
    (hc : (observationalLaw M) (observedCategoricalStratum ⁻¹' {c}) ≠ 0)
    {N : ℕ} (hN : 0 < N) (s t : ℝ)
    (hst : (fixedLabelLipschitzBudget M L (n * n + n) : ℝ) * s ≤ t) :
    (Measure.pi (fun _ : Fin N =>
      cond (observationalLaw M) (observedCategoricalStratum ⁻¹' {c})))
      {x | ¬ wasserstein1
        (cond (observationalLaw M) (observedCategoricalStratum ⁻¹' {c}))
        (empiricalMeasure x) ≤ ENNReal.ofReal t} ≤
    (Measure.pi (fun _ : Fin N =>
      (categoricalStratumCompactLatentLaw M K hK c :
        Measure (jointLatentCube dims K))))
      {z | ¬ wasserstein1
        (categoricalStratumCompactLatentLaw M K hK c : Measure (jointLatentCube dims K))
        (empiricalMeasure z) ≤ ENNReal.ofReal s} := by
  have hB := categoricalStratum_measurableSet_empirical_failure M K L hK hL c hc N t
  rw [categoricalStratum_compact_conditional_observation_law M K hK c hc] at hB ⊢
  exact compact_pushforward_empirical_failure_le
    (categoricalStratumCompactLatentLaw M K hK c : Measure (jointLatentCube dims K)) hN
    (categoricalStratumCompactObservation M K c) _
    (categoricalStratumCompactObservation_lipschitz M K L hL c) s t hst hB

-- @node: bounded_observation_coordinate_diameter
/-- For [a nonnegative bound](hyp:K) and [two complete observation
vectors](hyp:x,y), if [every coordinate of the first vector has absolute value
at most that bound](hyp:hx) and [the same holds for the second vector](hyp:hy),
then [their distance is at most twice the bound times the total number of
observation coordinates](goal). -/
lemma bounded_observation_coordinate_diameter (K : ℝ≥0) (x y : Joint kind)
    (hx : ∀ a, |x.ofLp a| ≤ K) (hy : ∀ a, |y.ofLp a| ≤ K) :
    dist x y ≤ 2 * K * Fintype.card (Σ i, Fin (valueDim (kind i))) := by
  rw [PiLp.dist_eq_of_L1]
  calc
    _ ≤ ∑ _a : Σ i, Fin (valueDim (kind i)), (2 * K : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      rw [Real.dist_eq]
      exact (abs_sub (x.ofLp a) (y.ofLp a)).trans (by linarith [hx a, hy a])
    _ = _ := by simp [mul_comm]

-- @node: iid_canonical_observational_failure_le_of_compact_latent_tails
/-- Under [a probability law on the sampling space](hyp:Q), consider
[a structural causal model](hyp:M), [nonnegative variable and mechanism
bounds](hyp:K,L), [variables bounded by the variable bound](hyp:hK),
[continuous mechanisms Lipschitz with the mechanism bound](hyp:hL),
[a positive sample size](hyp:hm), and [observation draws](hyp:sample) that are
[measurable](hyp:hsample), [mutually independent](hyp:hind), and [each
distributed according to the model's observational law](hyp:hlaw). Choose
[latent, observation, and label-frequency error thresholds](hyp:s,t,e) with
[nonnegative observation threshold](hyp:ht), [positive frequency error](hyp:he),
and [the recursive Lipschitz budget times the latent threshold at most the
observation threshold](hyp:hst); let [a nonnegative extended tail bound for
each complete categorical label](hyp:beta) [bound its compact latent empirical
Wasserstein failure probability whenever its mass is positive and its sample
size is at least half its expected count in the full sample](hyp:hbound).
Then [the complete empirical observation law's Wasserstein failure probability
at the observation threshold plus half the coordinate diameter bound times
the frequency error is at most the label-frequency concentration term plus,
over all positive-mass labels, a count concentration term and the specified
latent tail bound](goal).

The distance is Wasserstein distance of order one. Writing C for the number
of complete categorical labels and m for the sample size, the frequency term
is 2C exp(-2m(e/C)²). For a label of observational probability p, its count
term is 2C exp(-2m((p/2)/C)²). The coordinate diameter bound is twice the
variable bound times the total number of observation coordinates. -/
lemma iid_canonical_observational_failure_le_of_compact_latent_tails
    {Omega : Type*} [MeasurableSpace Omega]
    (Q : Measure Omega) [IsProbabilityMeasure Q] (M : EuclideanSCM kind dims)
    (K L : ℝ≥0) (hK : VariablesBoundedAt M K)
    (hL : ContinuousMechanismsLipschitz M L)
    {m : ℕ} (hm : 0 < m) (sample : Fin m → Omega → Joint kind)
    (hsample : ∀ i, Measurable (sample i)) (hind : iIndepFun sample Q)
    (hlaw : ∀ i, Q.map (sample i) = observationalLaw M)
    (s t e : ℝ) (ht : 0 ≤ t) (he : 0 < e)
    (hst : (fixedLabelLipschitzBudget M L (n * n + n) : ℝ) * s ≤ t)
    (beta : CategoricalStratum kind → ℝ≥0∞)
    (hbound : ∀ c, 0 < (observationalLaw M).real (observedCategoricalStratum ⁻¹' {c}) →
      ∀ N : ℕ, m * (observationalLaw M).real (observedCategoricalStratum ⁻¹' {c}) / 2 ≤ N →
      (Measure.pi (fun _ : Fin N =>
        (categoricalStratumCompactLatentLaw M K hK c : Measure (jointLatentCube dims K))))
        {z | ¬ wasserstein1
          (categoricalStratumCompactLatentLaw M K hK c : Measure (jointLatentCube dims K))
          (empiricalMeasure z) ≤ ENNReal.ofReal s} ≤ beta c) :
    Q {w | ¬ wasserstein1 (observationalLaw M)
      (empiricalMeasure (fun i => sample i w)) ≤ ENNReal.ofReal
        (t + (2 * K * Fintype.card (Σ i, Fin (valueDim (kind i)))) / 2 * e)} ≤
      ENNReal.ofReal (2 * Fintype.card (CategoricalStratum kind) * Real.exp
        (-2 * m * (e / Fintype.card (CategoricalStratum kind)) ^ 2)) +
      ∑ c, if 0 < (observationalLaw M).real (observedCategoricalStratum ⁻¹' {c}) then
        ENNReal.ofReal (2 * Fintype.card (CategoricalStratum kind) * Real.exp
          (-2 * m * (((observationalLaw M).real (observedCategoricalStratum ⁻¹' {c}) / 2) /
            Fintype.card (CategoricalStratum kind)) ^ 2)) + beta c else 0 := by
  classical
  let := M.probability
  let : IsProbabilityMeasure (observationalLaw M) :=
    Measure.isProbabilityMeasure_map (by fun_prop [intervenedEval])
  have hB (c : CategoricalStratum kind)
      (hc : 0 < (observationalLaw M).real (observedCategoricalStratum ⁻¹' {c})) (N : ℕ) :=
    categoricalStratum_measurableSet_empirical_failure M K L hK hL c
      (by intro hz; simp [Measure.real, hz] at hc) N t
  let E := Fintype.equivFin (CategoricalStratum kind)
  let : Nonempty (Fin (Fintype.card (CategoricalStratum kind))) :=
    ⟨E (fun _ => ⟨0, by omega⟩)⟩
  let label := E ∘ observedCategoricalStratum
  have hcell (a : Fin (Fintype.card (CategoricalStratum kind))) :
      label ⁻¹' {a} = observedCategoricalStratum ⁻¹' {E.symm a} := by
    ext v
    change E (observedCategoricalStratum v) = a ↔ observedCategoricalStratum v = E.symm a
    exact E.eq_symm_apply.symm
  have hcond (a : Fin (Fintype.card (CategoricalStratum kind)))
      (ha : 0 < (observationalLaw M).real (label ⁻¹' {a})) :
      cond (observationalLaw M) (label ⁻¹' {a}) =
        (categoricalStratumCompactLatentLaw M K hK (E.symm a) :
          Measure (jointLatentCube dims K)).map
            (categoricalStratumCompactObservation M K (E.symm a)) := by
    rw [hcell] at ha ⊢
    apply categoricalStratum_compact_conditional_observation_law M K hK
    intro hz
    simp [Measure.real, hz] at ha
  have htail := iid_observational_wasserstein_failure_le_of_latent_tails
    Q (observationalLaw M) hm sample hsample hind hlaw label
    ((measurable_of_finite E).comp (by fun_prop))
    {v | ∀ a, |v.ofLp a| ≤ K} (joint_coordinate_box_isCompact K).measurableSet
    (observationalLaw_bounded_coordinates M K hK)
    (2 * K * Fintype.card (Σ i, Fin (valueDim (kind i)))) t e
    (by positivity) ht he (fun x hx y hy => bounded_observation_coordinate_diameter K x y hx hy)
    (fun a => categoricalStratumCompactLatentLaw M K hK (E.symm a))
    (fun a => categoricalStratumCompactObservation M K (E.symm a))
    (fun _ => fixedLabelLipschitzBudget M L (n * n + n))
    (fun a => categoricalStratumCompactObservation_lipschitz M K L hL (E.symm a))
    hcond (fun _ => s) (fun _ => hst) (fun a => beta (E.symm a))
    (by simpa only [hcell] using fun a => hB (E.symm a))
    (by simpa only [hcell] using fun a => hbound (E.symm a))
  simp only [hcell] at htail
  convert htail using 1
  congr 1
  exact (E.symm.sum_comp _).symm

end
end Papers.TbsNeuralCausalPi
