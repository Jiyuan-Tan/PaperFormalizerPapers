module
public import Papers.TbsNeuralCausalPi.Setup.Optimization
public import Papers.TbsNeuralCausalPi.Helpers.WassersteinSpace
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
/-! # Compact structural coordinates for the consistency parameter space

The uniform topology retains the full cube domain. Continuous outputs stay in
the closed one-norm ball and categorical outputs stay in the closed simplex.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory Filter BoundedContinuousFunction
open scoped NNReal ENNReal Topology

/-- For [a nonnegative Lipschitz bound](hyp:L) and [an output set](hyp:S)
that is [compact](hyp:hS), [the bounded continuous functions on a compact
input space satisfying that Lipschitz bound and taking values in the output
set form a compact set in the uniform norm](goal). -/
-- @node: estimation_isCompact_lipschitz_range
lemma estimation_isCompact_lipschitz_range
    {X Y : Type*} [PseudoMetricSpace X] [CompactSpace X] [MetricSpace Y]
    (L : ℝ≥0) (S : Set Y) (hS : IsCompact S) :
    IsCompact {f : X →ᵇ Y | LipschitzWith L f ∧ ∀ x, f x ∈ S} := by
  have hclosed : IsClosed {f : X →ᵇ Y | LipschitzWith L f ∧ ∀ x, f x ∈ S} := by
    have hLip : IsClosed {f : X →ᵇ Y | LipschitzWith L f} :=
      (isClosed_setOfPred_lipschitzWith (α := X) (β := Y) L).preimage
        (BoundedContinuousFunction.continuous_coe (α := X) (β := Y))
    have hRange : IsClosed {f : X →ᵇ Y | ∀ x, f x ∈ S} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter (fun x => hS.isClosed.preimage
        (lipschitz_eval_const x).continuous)
    exact hLip.inter hRange
  apply arzela_ascoli₂ S hS _ hclosed (fun f x hf => hf.2 x)
  apply Metric.equicontinuous_of_continuity_modulus (fun r => (L : ℝ) * r)
    (by simpa using (tendsto_id.const_mul (L : ℝ) :
      Tendsto (fun r : ℝ => (L : ℝ) * r) (𝓝 0) (𝓝 ((L : ℝ) * 0))))
  intro x y f
  exact f.property.1.dist_le_mul x y

/-- For [a nonnegative radius](hyp:K) and [a structural node](hyp:i),
[the cube of parent and latent input coordinates is compact](goal), including
when there are no input coordinates. -/
-- @node: inputCube_isCompact
lemma inputCube_isCompact {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
    {dag : Causalean.Graph.DAG (Fin n)} {C : Fin b → Set (Fin n)}
    (K : ℝ≥0) (i : Fin n) :
    IsCompact (inputCube (kind := kind) (dims := dims) (dag := dag) (C := C) K i) := by
  let J := Sum (Σ p : {p // p ∈ dag.parents i}, Fin (valueDim (kind p)))
    (Σ j : {j // j ∈ canonicalIncidence C i}, Fin (dims j))
  have hc := (isCompact_univ_pi (fun _ : J => isCompact_Icc (a := -(K : ℝ)) (b := K))).image
    (PiLp.continuous_toLp (p := (1 : ENNReal)) (β := fun _ : J => ℝ))
  convert hc using 1
  ext x
  simp only [inputCube, Set.mem_ofPred_eq, abs_le, Set.mem_image]
  constructor
  · intro hx
    exact ⟨x.ofLp, fun j _ => hx j, WithLp.toLp_ofLp 1 x⟩
  · rintro ⟨y, hy, rfl⟩
    exact fun j => hy j (Set.mem_univ j)

/-- For [a nonnegative output bound](hyp:K) and [a node type](hyp:kind),
the [structural output set](goal) is [the closed one-norm ball centered at
zero with that bound for a continuous node](step:1), or [the probability
simplex for a categorical node](step:2). -/
-- @node: estimationStructuralOutputSet
def estimationStructuralOutputSet (K : ℝ≥0) (kind : NodeKind) :
    Set (L1Vec (outputDim kind)) :=
  match kind with
  | .inl _ => Metric.closedBall 0 K
  | .inr k => {v | v.ofLp ∈ probabilitySimplex k}

-- @node: estimationStructuralOutputSet_isCompact
/-- For [a nonnegative output bound](hyp:K) and [a node type](hyp:kind),
[the structural output set, whether a closed one-norm ball or a probability
simplex, is compact](goal). -/
lemma estimationStructuralOutputSet_isCompact (K : ℝ≥0) (kind : NodeKind) :
    IsCompact (estimationStructuralOutputSet K kind) := by
  cases kind with
  | inl d => exact isCompact_closedBall 0 K
  | inr k =>
    have hc := (isCompact_stdSimplex ℝ (Fin k)).image
      (PiLp.continuous_toLp (p := (1 : ENNReal)) (β := fun _ : Fin k => ℝ))
    have heq : estimationStructuralOutputSet K (.inr k) =
        WithLp.toLp 1 '' probabilitySimplex k := by
      ext v
      constructor
      · intro hv
        exact ⟨v.ofLp, hv, WithLp.toLp_ofLp 1 v⟩
      · rintro ⟨w, hw, rfl⟩
        exact hw
    rw [heq]
    exact hc

/-- For [a nonnegative output bound](hyp:K), [a node type](hyp:kind), and
[a vector-valued function](hyp:f), [all function values belong to the
structural output set exactly when the one-norm bound holds for a continuous
node and the probability-simplex constraint holds for a categorical
node](goal). -/
-- @node: estimationStructuralOutputSet_constraints
lemma estimationStructuralOutputSet_constraints {X : Type*}
    (K : ℝ≥0) (kind : NodeKind) (f : X → L1Vec (outputDim kind)) :
    (∀ x, f x ∈ estimationStructuralOutputSet K kind) ↔
      (∀ d, kind = Sum.inl d → ∀ x, ‖f x‖ ≤ K) ∧
      (∀ k (h : kind = Sum.inr k) x,
        (fun j : Fin k => (f x).ofLp
          (Fin.cast (congrArg outputDim h).symm j)) ∈ probabilitySimplex k) := by
  cases kind with
  | inl d =>
    simp [estimationStructuralOutputSet, Metric.mem_closedBall, dist_zero_right]
  | inr k =>
    simp only [estimationStructuralOutputSet, Set.mem_ofPred, Sum.inr_ne_inl,
      IsEmpty.forall_iff, implies_true, true_and]
    constructor
    · intro hf k' h x
      obtain rfl := Sum.inr.inj h
      simpa [outputDim] using hf x
    · intro hf x
      simpa [outputDim] using hf k rfl x

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {C : Fin b → Set (Fin n)}

/-- For [a nonnegative cube and output bound and a nonnegative Lipschitz
bound](hyp:K,L) and [a node](hyp:i), [the bounded continuous functions on its
input cube satisfying the Lipschitz bound, the continuous-output one-norm
bound, and the categorical probability-simplex constraints form a compact
set in the uniform norm](goal). -/
-- @node: estimation_cube_structural_coordinate_isCompact
lemma estimation_cube_structural_coordinate_isCompact (K L : ℝ≥0) (i : Fin n) :
    IsCompact {f : ↥(inputCube (kind := kind) (dims := dims) (dag := dag) (C := C) K i)
        →ᵇ L1Vec (outputDim (kind i)) |
      (fun x => f x) ∈ cubePopulationClass K L i ∧
        ∀ k (h : kind i = Sum.inr k) x,
          (fun j : Fin k => (f x).ofLp
            (Fin.cast (congrArg outputDim h).symm j)) ∈ probabilitySimplex k} := by
  let := isCompact_iff_compactSpace.mp
    (inputCube_isCompact (kind := kind) (dims := dims) (dag := dag) (C := C) K i)
  have hc := estimation_isCompact_lipschitz_range
    (X := ↥(inputCube (kind := kind) (dims := dims) (dag := dag) (C := C) K i))
    L (estimationStructuralOutputSet K (kind i))
    (estimationStructuralOutputSet_isCompact K (kind i))
  have heq : {f : ↥(inputCube (kind := kind) (dims := dims) (dag := dag) (C := C) K i)
        →ᵇ L1Vec (outputDim (kind i)) |
      (fun x => f x) ∈ cubePopulationClass K L i ∧
        ∀ k (h : kind i = Sum.inr k) x,
          (fun j : Fin k => (f x).ofLp
            (Fin.cast (congrArg outputDim h).symm j)) ∈ probabilitySimplex k} =
      {f : ↥(inputCube (kind := kind) (dims := dims) (dag := dag) (C := C) K i)
        →ᵇ L1Vec (outputDim (kind i)) |
        LipschitzWith L f ∧ ∀ x, f x ∈ estimationStructuralOutputSet K (kind i)} := by
    ext f
    rw [Set.mem_ofPred, Set.mem_ofPred,
      estimationStructuralOutputSet_constraints]
    change (LipschitzWith L f ∧ _) ∧ _ ↔ LipschitzWith L f ∧ _ ∧ _
    exact and_assoc
  rw [heq]
  exact hc

/-- For [a number of nodes](hyp:n), [a number of latent blocks](hyp:b),
[node types](hyp:kind), [latent dimensions](hyp:dims), [a causal
directed acyclic graph](hyp:dag), [latent incidence sets](hyp:C), and
[a nonnegative input radius](hyp:K), the [family of structural cube
maps](goal) consists of one bounded continuous vector-valued function on
each node's input cube, with output dimension determined by its node type. -/
-- @node: EstimationCubeMaps
abbrev EstimationCubeMaps (kind : Fin n → NodeKind) (dims : Fin b → ℕ)
    (dag : Causalean.Graph.DAG (Fin n)) (C : Fin b → Set (Fin n)) (K : ℝ≥0) :=
  ∀ i, ↥(inputCube (kind := kind) (dims := dims) (dag := dag) (C := C) K i)
    →ᵇ L1Vec (outputDim (kind i))

/-- For [a number of nodes](hyp:n), [a number of latent blocks](hyp:b),
[node types](hyp:kind), [latent dimensions](hyp:dims), [a causal
directed acyclic graph](hyp:dag), [latent incidence sets](hyp:C), and
[nonnegative cube and output and Lipschitz bounds](hyp:K,L), the
[structural population set](goal) consists of families of bounded continuous
cube maps such that, at every node, [the map satisfies the Lipschitz bound
and, for continuous outputs, the one-norm bound](step:1) and [categorical
outputs are probability vectors](step:2). -/
-- @node: estimationCubeStructuralSet
def estimationCubeStructuralSet (K L : ℝ≥0) :
    Set (EstimationCubeMaps kind dims dag C K) :=
  {f | ∀ i, (fun x => f i x) ∈ cubePopulationClass K L i ∧
    ∀ k (h : kind i = Sum.inr k) x,
      (fun j : Fin k => (f i x).ofLp
        (Fin.cast (congrArg outputDim h).symm j)) ∈ probabilitySimplex k}

/-- For [nonnegative cube and output and Lipschitz bounds](hyp:K,L),
[the structural population set is compact in the product of the nodewise
uniform topologies](goal). -/
-- @node: estimationCubeStructuralSet_isCompact
lemma estimationCubeStructuralSet_isCompact (K L : ℝ≥0) :
    IsCompact (estimationCubeStructuralSet (kind := kind) (dims := dims)
      (dag := dag) (C := C) K L) := by
  simpa only [estimationCubeStructuralSet, Set.pi, Set.mem_univ, forall_const, Set.mem_ofPred] using
    isCompact_univ_pi (estimation_cube_structural_coordinate_isCompact
      (kind := kind) (dims := dims) (dag := dag) (C := C) K L)

/-- For [nonnegative cube and output and Lipschitz bounds](hyp:K,L), let
[a sequence of structural cube maps](hyp:f) have [every nodewise map satisfy
the Lipschitz bound and the continuous-output one-norm bound](hyp:hf) and
[all categorical outputs in their
probability simplices](hyp:hsimplex). Then [there is a limiting family satisfying
the same Lipschitz and continuous-output bounds and simplex constraints and a
single strictly increasing subsequence along which every nodewise map
converges uniformly to its limit](goal). -/
-- @node: estimation_cube_structural_uniform_subsequence
lemma estimation_cube_structural_uniform_subsequence (K L : ℝ≥0)
    (f : ℕ → CubeFunctions kind dims dag C K)
    (hf : ∀ r i, f r i ∈ cubePopulationClass K L i)
    (hsimplex : ∀ r i k (h : kind i = Sum.inr k) x,
      (fun j : Fin k => (f r i x).ofLp
        (Fin.cast (congrArg outputDim h).symm j)) ∈ probabilitySimplex k) :
    ∃ g : CubeFunctions kind dims dag C K,
      (∀ i, g i ∈ cubePopulationClass K L i) ∧
      (∀ i k (h : kind i = Sum.inr k) x,
        (fun j : Fin k => (g i x).ofLp
          (Fin.cast (congrArg outputDim h).symm j)) ∈ probabilitySimplex k) ∧
      ∃ phi : ℕ → ℕ, StrictMono phi ∧
        ∀ i, TendstoUniformly (fun r => f (phi r) i) (g i) atTop := by
  let (i : Fin n) := isCompact_iff_compactSpace.mp
    (inputCube_isCompact (kind := kind) (dims := dims) (dag := dag) (C := C) K i)
  let seq : ℕ → EstimationCubeMaps kind dims dag C K := fun r i =>
    mkOfCompact ⟨f r i, (hf r i).1.continuous⟩
  have hseq : ∀ r, seq r ∈ estimationCubeStructuralSet K L := by
    intro r i
    exact ⟨hf r i, hsimplex r i⟩
  obtain ⟨g, hg, phi, hphi, hlim⟩ :=
    (estimationCubeStructuralSet_isCompact (kind := kind) (dims := dims)
      (dag := dag) (C := C) K L).tendsto_subseq hseq
  refine ⟨fun i x => g i x, fun i => (hg i).1, fun i => (hg i).2, phi, hphi, ?_⟩
  intro i
  have hi := ((continuous_apply i).tendsto g).comp hlim
  exact BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hi

/-- For [nonnegative cube and output and Lipschitz bounds](hyp:K,L) and
[a sequence of population parameters with these bounds](hyp:p), [there is a
population parameter with the same bounds and a single strictly increasing
subsequence along which every structural function converges uniformly and
every latent marginal converges to the corresponding limiting marginal in
the first Wasserstein distance](goal). -/
-- @node: estimation_population_parameter_subsequence
lemma estimation_population_parameter_subsequence (K L : ℝ≥0)
    (p : ℕ → PopulationParam kind dims dag C K L) :
    ∃ q : PopulationParam kind dims dag C K L, ∃ phi : ℕ → ℕ,
      StrictMono phi ∧
      (∀ i, TendstoUniformly (fun r => (p (phi r)).parameter.1.val i)
        (q.parameter.1.val i) atTop) ∧
      (∀ j, Tendsto (fun r => wasserstein1
        ((p (phi r)).parameter.2 j : Measure (boundedCube (dims j) K))
        (q.parameter.2 j : Measure (boundedCube (dims j) K))) atTop (𝓝 0)) := by
  let (i : Fin n) := isCompact_iff_compactSpace.mp
    (inputCube_isCompact (kind := kind) (dims := dims) (dag := dag) (C := C) K i)
  let (j : Fin b) := isCompact_iff_compactSpace.mp (boundedCube_isCompact (dims j) K)
  let seq : ℕ → EstimationCubeMaps kind dims dag C K ×
      (∀ j, ProbabilityMeasure (boundedCube (dims j) K)) := fun r =>
    (fun i => mkOfCompact ⟨(p r).parameter.1.val i,
      ((p r).parameter.1.property.1 i).1.continuous⟩, (p r).parameter.2)
  have hc : IsCompact (estimationCubeStructuralSet (kind := kind) (dims := dims)
      (dag := dag) (C := C) K L ×ˢ
      (Set.univ : Set (∀ j, ProbabilityMeasure (boundedCube (dims j) K)))) :=
    (estimationCubeStructuralSet_isCompact K L).prod isCompact_univ
  have hseq : ∀ r, seq r ∈ estimationCubeStructuralSet K L ×ˢ Set.univ := by
    intro r
    refine ⟨?_, Set.mem_univ _⟩
    intro i
    exact ⟨(p r).parameter.1.property.1 i, (p r).parameter.1.property.2.1 i⟩
  obtain ⟨g, hg, phi, hphi, hlim⟩ := hc.tendsto_subseq hseq
  have hmeas : ∀ i, Measurable (fun x => g.1 i x) := by
    intro i
    fun_prop
  let q : PopulationParam kind dims dag C K L :=
    ⟨(⟨fun i x => g.1 i x, (fun i => (hg.1 i).1),
      (fun i => (hg.1 i).2), hmeas⟩, g.2)⟩
  refine ⟨q, phi, hphi, ?_, ?_⟩
  · intro i
    have hi := (((continuous_apply i).comp continuous_fst).tendsto g).comp hlim
    exact BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hi
  · intro j
    apply (tendsto_wasserstein1_iff_weak_compact atTop
      (fun r => (p (phi r)).parameter.2 j) (q.parameter.2 j)).mpr
    exact (((continuous_apply j).comp continuous_snd).tendsto g).comp hlim

/-- For [a sequence of vector-valued functions](hyp:f) and [a limiting
function](hyp:g), if [the sequence converges uniformly to the limit in the
one-norm](hyp:h), then [the real-valued uniform coordinate error over the
whole domain tends to zero](goal), even for zero-dimensional outputs. -/
-- @node: estimation_supDistOn_tendsto_zero_of_uniform
lemma estimation_supDistOn_tendsto_zero_of_uniform {X : Type*} {d : ℕ}
    (f : ℕ → X → L1Vec d) (g : X → L1Vec d)
    (h : TendstoUniformly f g atTop) :
    Tendsto (fun r => (supDistOn Set.univ (f r) g).toReal) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro eps heps
  filter_upwards [Metric.tendstoUniformly_iff.mp h (eps / 2) (by positivity)] with r hr
  have hsup : supDistOn Set.univ (f r) g ≤ ENNReal.ofReal (eps / 2) := by
    apply iSup_le
    intro x
    apply ENNReal.ofReal_le_ofReal
    have hn : ‖(f r x - g x).ofLp‖ ≤ ‖f r x - g x‖ := by
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro j
      exact PiLp.norm_apply_le (p := (1 : ENNReal)) _ j
    exact hn.trans (by simpa only [dist_eq_norm, norm_sub_rev] using (hr x).le)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsup
  rw [ENNReal.toReal_ofReal (by positivity)] at hreal
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg] using
    (lt_of_le_of_lt hreal (by linarith : eps / 2 < eps))

/-- For [nonnegative cube and output and Lipschitz bounds](hyp:K,L) and
[a sequence of population parameters with these bounds](hyp:p), [there is a
population parameter with the same bounds and a strictly increasing
subsequence whose parameter distance to that limit tends to zero, where the
distance sums uniform structural errors and marginal first Wasserstein
distances](goal). -/
-- @node: estimation_population_paramDist_subsequence
lemma estimation_population_paramDist_subsequence (K L : ℝ≥0)
    (p : ℕ → PopulationParam kind dims dag C K L) :
    ∃ q : PopulationParam kind dims dag C K L, ∃ phi : ℕ → ℕ,
      StrictMono phi ∧ Tendsto (fun r => paramDist (p (phi r)) q) atTop (𝓝 0) := by
  obtain ⟨q, phi, hphi, hf, hmu⟩ := estimation_population_parameter_subsequence K L p
  have hstruct := fun i => estimation_supDistOn_tendsto_zero_of_uniform
    (fun r => (p (phi r)).parameter.1.val i) (q.parameter.1.val i) (hf i)
  have hlatent : ∀ j, Tendsto (fun r => (wasserstein1
      ((p (phi r)).parameter.2 j : Measure (boundedCube (dims j) K))
      (q.parameter.2 j : Measure (boundedCube (dims j) K))).toReal) atTop (𝓝 0) := by
    intro j
    exact (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp (hmu j)
  refine ⟨q, phi, hphi, ?_⟩
  simpa only [paramDist, cubeParamDist, Finset.sum_const_zero, zero_add] using
    (tendsto_finsetSum Finset.univ (fun i _ => hstruct i)).add
      (tendsto_finsetSum Finset.univ (fun j _ => hlatent j))

end Papers.TbsNeuralCausalPi
