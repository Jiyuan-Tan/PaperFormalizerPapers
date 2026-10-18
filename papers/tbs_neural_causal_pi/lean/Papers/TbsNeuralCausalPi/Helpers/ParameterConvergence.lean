module
public import Papers.TbsNeuralCausalPi.Helpers.StructuralCompactness
/-! # Coordinate convergence in the population parameter distance

The real-valued distance loses no information through `ENNReal.toReal`:
all structural distances and latent costs on the compact carriers are finite.
In particular, parameter convergence gives uniform convergence in the output
one-norm, including structural coordinates with zero output dimension.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory Filter
open scoped NNReal ENNReal Topology

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {C : Fin b → Set (Fin n)} {K L : ℝ≥0}

-- @node: population_structural_supDistOn_ne_top
/-- [The uniform coordinatewise distance between two population structural
mechanisms on the input cube is finite at every node](goal). -/
lemma population_structural_supDistOn_ne_top
    (p q : PopulationParam kind dims dag C K L) (i : Fin n) :
    supDistOn Set.univ (p.parameter.1.val i) (q.parameter.1.val i) ≠ ⊤ := by
  letI := isCompact_iff_compactSpace.mp
    (inputCube_isCompact (kind := kind) (dims := dims) (dag := dag) (C := C) K i)
  have hp := ((p.parameter.1.property.1 i).1).continuous
  have hq := ((q.parameter.1.property.1 i).1).continuous
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (hp.sub hq).continuousOn
  apply ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := B))
  apply iSup_le
  intro x
  apply ENNReal.ofReal_le_ofReal
  exact (show ‖(p.parameter.1.val i x - q.parameter.1.val i x).ofLp‖ ≤
    ‖p.parameter.1.val i x - q.parameter.1.val i x‖ from
      (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
        (fun j => PiLp.norm_apply_le (p := (1 : ENNReal)) _ j)).trans
    (hB x (Set.mem_univ _))

-- @node: paramDist_nonneg
/-- [The parameter distance between any two population parameters is
nonnegative](goal). -/
lemma paramDist_nonneg (p q : PopulationParam kind dims dag C K L) :
    0 ≤ paramDist p q := by
  exact add_nonneg (Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg))
    (Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg))

-- @node: population_structural_toReal_le_paramDist
/-- [At each node, the real-valued uniform coordinatewise distance between the
two structural mechanisms on the input cube is at most their total parameter
distance](goal). -/
lemma population_structural_toReal_le_paramDist
    (p q : PopulationParam kind dims dag C K L) (i : Fin n) :
    (supDistOn Set.univ (p.parameter.1.val i) (q.parameter.1.val i)).toReal ≤
      paramDist p q := by
  unfold paramDist cubeParamDist
  apply le_trans (Finset.single_le_sum (f := fun i =>
    (supDistOn Set.univ (p.parameter.1.val i) (q.parameter.1.val i)).toReal)
    (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ i))
  exact
    (le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)))

-- @node: population_latent_toReal_le_paramDist
/-- [For each latent block, the real-valued Wasserstein distance between the
two block distributions on the bounded cube is at most the total parameter
distance](goal). -/
lemma population_latent_toReal_le_paramDist
    (p q : PopulationParam kind dims dag C K L) (j : Fin b) :
    (wasserstein1 (p.parameter.2 j : Measure (boundedCube (dims j) K))
      (q.parameter.2 j : Measure (boundedCube (dims j) K))).toReal ≤ paramDist p q := by
  unfold paramDist cubeParamDist
  apply le_trans (Finset.single_le_sum (f := fun j =>
    (wasserstein1 (p.parameter.2 j : Measure (boundedCube (dims j) K))
      (q.parameter.2 j : Measure (boundedCube (dims j) K))).toReal)
    (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ j))
  exact
    (le_add_of_nonneg_left (Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)))

/-- [At any input in a node's input cube, the output one-norm difference between
two population structural mechanisms is at most the node's output dimension
times their parameter distance](goal). -/
-- @node: population_structural_norm_sub_le_paramDist
lemma population_structural_norm_sub_le_paramDist
    (p q : PopulationParam kind dims dag C K L) (i : Fin n) (x : inputCube K i) :
    ‖p.parameter.1.val i x - q.parameter.1.val i x‖ ≤
      (outputDim (kind i) : ℝ) * paramDist p q := by
  have hs : ‖(p.parameter.1.val i x - q.parameter.1.val i x).ofLp‖ ≤
      (supDistOn Set.univ (p.parameter.1.val i) (q.parameter.1.val i)).toReal := by
    apply (ENNReal.ofReal_le_iff_le_toReal
      (population_structural_supDistOn_ne_top p q i)).mp
    exact le_iSup_of_le ⟨x, Set.mem_univ _⟩ le_rfl
  calc
    ‖p.parameter.1.val i x - q.parameter.1.val i x‖ =
        ∑ j : Fin (outputDim (kind i)),
          ‖(p.parameter.1.val i x - q.parameter.1.val i x).ofLp j‖ :=
      PiLp.norm_eq_of_L1 _
    _ ≤ ∑ _j : Fin (outputDim (kind i)), paramDist p q := by
      apply Finset.sum_le_sum
      intro j _
      exact (norm_le_pi_norm (f := (p.parameter.1.val i x - q.parameter.1.val i x).ofLp) j).trans
        (hs.trans (population_structural_toReal_le_paramDist p q i))
    _ = (outputDim (kind i) : ℝ) * paramDist p q := by simp

-- @node: paramDist_tendsto_uniformly
/-- If [a sequence of population parameters converges to a target in parameter
distance](hyp:h), [its structural mechanisms at each fixed node converge uniformly
on the input cube to the target mechanism](goal). -/
lemma paramDist_tendsto_uniformly
    (p : ℕ → PopulationParam kind dims dag C K L)
    (q : PopulationParam kind dims dag C K L)
    (h : Tendsto (fun r => paramDist (p r) q) atTop (𝓝 0)) (i : Fin n) :
    TendstoUniformly (fun r => (p r).parameter.1.val i) (q.parameter.1.val i) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro eps heps
  have ht : Tendsto (fun r => (outputDim (kind i) : ℝ) * paramDist (p r) q)
      atTop (𝓝 0) := by simpa using h.const_mul (outputDim (kind i) : ℝ)
  filter_upwards [ht.eventually (gt_mem_nhds heps)] with r hr x
  exact lt_of_le_of_lt (by
    simpa only [dist_eq_norm, norm_sub_rev] using
      population_structural_norm_sub_le_paramDist (p r) q i x) hr

-- @node: paramDist_tendsto_latent_wasserstein
/-- If [a sequence of population parameters converges to a target in parameter
distance](hyp:h), [the Wasserstein distance from each fixed latent block's
distribution to the target block distribution tends to zero](goal). -/
lemma paramDist_tendsto_latent_wasserstein
    (p : ℕ → PopulationParam kind dims dag C K L)
    (q : PopulationParam kind dims dag C K L)
    (h : Tendsto (fun r => paramDist (p r) q) atTop (𝓝 0)) (j : Fin b) :
    Tendsto (fun r => wasserstein1
      ((p r).parameter.2 j : Measure (boundedCube (dims j) K))
      (q.parameter.2 j : Measure (boundedCube (dims j) K))) atTop (𝓝 0) := by
  letI := isCompact_iff_compactSpace.mp (boundedCube_isCompact (dims j) K)
  have ht := squeeze_zero (fun r => ENNReal.toReal_nonneg)
    (fun r => population_latent_toReal_le_paramDist (p r) q j) h
  have he := ENNReal.tendsto_ofReal ht
  simpa only [ENNReal.ofReal_toReal
    (wasserstein1_ne_top_compact _ _), ENNReal.ofReal_zero] using he

/-- [The parameter distance, viewed as an extended nonnegative number, equals
the sum of the uniform coordinatewise distances between structural mechanisms
on their input cubes and the Wasserstein distances between latent block
distributions](goal). -/
-- @node: paramDist_ofReal_eq_sum
lemma paramDist_ofReal_eq_sum
    (p q : PopulationParam kind dims dag C K L) :
    ENNReal.ofReal (paramDist p q) =
      (∑ i, supDistOn Set.univ (p.parameter.1.val i) (q.parameter.1.val i)) +
      ∑ j, wasserstein1 (p.parameter.2 j : Measure (boundedCube (dims j) K))
        (q.parameter.2 j : Measure (boundedCube (dims j) K)) := by
  letI (j : Fin b) := isCompact_iff_compactSpace.mp (boundedCube_isCompact (dims j) K)
  unfold paramDist cubeParamDist
  rw [ENNReal.ofReal_add (Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg))
    (Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg))]
  simp only [ENNReal.ofReal_sum_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)]
  congr 1
  · exact Finset.sum_congr rfl (fun i _ =>
      ENNReal.ofReal_toReal (population_structural_supDistOn_ne_top p q i))
  · exact Finset.sum_congr rfl (fun j _ =>
      ENNReal.ofReal_toReal (wasserstein1_ne_top_compact _ _))

/-- [Convergence to a target in parameter distance is equivalent to uniform
convergence of every structural mechanism on its input cube together with
convergence to zero of every latent block's Wasserstein distance to its target
distribution](goal). -/
-- @node: paramDist_tendsto_zero_iff_coordinates
lemma paramDist_tendsto_zero_iff_coordinates
    (p : ℕ → PopulationParam kind dims dag C K L)
    (q : PopulationParam kind dims dag C K L) :
    Tendsto (fun r => paramDist (p r) q) atTop (𝓝 0) ↔
      (∀ i, TendstoUniformly (fun r => (p r).parameter.1.val i)
        (q.parameter.1.val i) atTop) ∧
      (∀ j, Tendsto (fun r => wasserstein1
        ((p r).parameter.2 j : Measure (boundedCube (dims j) K))
        (q.parameter.2 j : Measure (boundedCube (dims j) K))) atTop (𝓝 0)) := by
  constructor
  · intro h
    exact ⟨paramDist_tendsto_uniformly p q h, paramDist_tendsto_latent_wasserstein p q h⟩
  · rintro ⟨hf, hmu⟩
    have hstruct := fun i => estimation_supDistOn_tendsto_zero_of_uniform
      (fun r => (p r).parameter.1.val i) (q.parameter.1.val i) (hf i)
    have hlatent : ∀ j, Tendsto (fun r => (wasserstein1
        ((p r).parameter.2 j : Measure (boundedCube (dims j) K))
        (q.parameter.2 j : Measure (boundedCube (dims j) K))).toReal) atTop (𝓝 0) := by
      intro j
      exact (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp (hmu j)
    simpa only [paramDist, cubeParamDist, Finset.sum_const_zero, zero_add] using
      (tendsto_finsetSum Finset.univ (fun i _ => hstruct i)).add
        (tendsto_finsetSum Finset.univ (fun j _ => hlatent j))

-- @node: paramDist_tendsto_latent_weak
/-- If [a sequence of population parameters converges to a target in parameter
distance](hyp:h), [each fixed latent block's probability distribution converges
weakly to the target block distribution on the bounded cube](goal). -/
lemma paramDist_tendsto_latent_weak
    (p : ℕ → PopulationParam kind dims dag C K L)
    (q : PopulationParam kind dims dag C K L)
    (h : Tendsto (fun r => paramDist (p r) q) atTop (𝓝 0)) (j : Fin b) :
    Tendsto (fun r => (p r).parameter.2 j) atTop (𝓝 (q.parameter.2 j)) := by
  letI := isCompact_iff_compactSpace.mp (boundedCube_isCompact (dims j) K)
  exact (tendsto_wasserstein1_iff_weak_compact atTop
    (fun r => (p r).parameter.2 j) (q.parameter.2 j)).mp
      (paramDist_tendsto_latent_wasserstein p q h j)

end Papers.TbsNeuralCausalPi
