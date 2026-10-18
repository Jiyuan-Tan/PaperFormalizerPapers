module
public import Papers.TbsNeuralCausalPi.Helpers.CausalPropensityAlphabet
public import Papers.TbsNeuralCausalPi.Helpers.CausalTableSampling
public import Papers.TbsNeuralCausalPi.Helpers.EstimationCandidateBounds
public import Papers.TbsNeuralCausalPi.Helpers.CanonicalConditionalPropensity
/-! # Construction of the complete causal-table readout

Evaluate the fixed-label continuous equations at the common latent grid
representative. This gives a bounded readout with the required mesh error.
The readout does not enter the indicator pattern count: only the paired
latent code and categorical label do. Clipping totalizes the latent code
without altering any generated block in its prescribed cube.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

-- @node: simulationLatentCubePoint
/-- For [the dimensions of finitely many latent blocks](hyp:b,dims), [a nonnegative cube radius](hyp:K),
and [a latent input](hyp:z), [the clipped latent point](goal) is the concatenated
latent vector with every coordinate clamped between minus and plus that radius. -/
def simulationLatentCubePoint (K : ℝ≥0) (z : Latent dims) :
    boundedCube (∑ j, dims j) K :=
  ⟨truncK K (jointLatentVectorEquiv dims z), by
    intro i
    exact abs_le.mpr (coordinateClamp_mapsTo (-(K : ℝ)) K
      (by linarith [K.coe_nonneg]) _ i)⟩

-- @node: simulationLatentCubePoint_measurable
/-- For [a nonnegative cube radius](hyp:K), [clipping and concatenating the
latent blocks into that cube is a measurable map](goal). -/
@[fun_prop] lemma simulationLatentCubePoint_measurable (K : ℝ≥0) :
    Measurable (simulationLatentCubePoint (dims := dims) K) := by
  fun_prop [simulationLatentCubePoint, truncK]

-- @node: simulationLatentCubePoint_eq_of_mem
/-- For [a nonnegative cube radius](hyp:K), if [a latent input already lies in
that cube](hyp:hz), then
[clipping its concatenated vector leaves it unchanged](goal). -/
lemma simulationLatentCubePoint_eq_of_mem (K : ℝ≥0) (z : Latent dims)
    (hz : z ∈ jointLatentCube dims K) :
    (simulationLatentCubePoint K z).val = jointLatentVectorEquiv dims z := by
  apply coordinateClamp_fixes
  intro i
  exact abs_le.mp ((jointLatentVectorEquiv_mem_cube K z).mpr hz i)

-- @node: categoricalStratumAssignment_coordinate_bound
/-- For [a nonnegative latent radius](hyp:K), if [a categorical stratum assigns
an intervention value at a node](hyp:hv), then [the absolute value of each
coordinate of that value is bounded by the corresponding observation radius](goal). -/
lemma categoricalStratumAssignment_coordinate_bound
    (M : CanonicalSCM kind dims dag G C) (K : ℝ≥0)
    (c : CategoricalStratum kind) (i : Fin n) (v : L1Vec (valueDim (kind i)))
    (hv : categoricalStratumAssignment c i = some v) (j : Fin (valueDim (kind i))) :
    |v.ofLp j| ≤ estimationObservationRadius kind K := by
  have ha := categoricalStratumAssignment_admissible M.toEuclideanSCM c i v hv
  split at ha
  · rename_i d hi
    simp [categoricalStratumAssignment, hi, noiseDim] at hv
  · rename_i k hi
    obtain ⟨label, hlabel⟩ := ha
    rw [hlabel j, abs_of_nonneg (Nat.cast_nonneg _)]
    exact (show ((label.val + 1 : ℕ) : ℝ) ≤ k by exact_mod_cast label.isLt).trans
      (estimationObservationRadius_labels K i k hi)

-- @node: joint_norm_le_of_coordinate_bound
/-- If [every coordinate of a joint observation has absolute value at most a
common bound](hyp:hv), then [its sum-of-absolute-values norm is at most the total
number of coordinates times that bound](goal). -/
lemma joint_norm_le_of_coordinate_bound (v : Joint kind) (B : ℝ)
    (hv : ∀ i j, |v.ofLp ⟨i,j⟩| ≤ B) :
    ‖v‖ ≤ (∑ i, valueDim (kind i)) * B := by
  rw [PiLp.norm_eq_of_L1]
  calc
    _ ≤ ∑ _a : Σ i, Fin (valueDim (kind i)), B := by
      apply Finset.sum_le_sum
      rintro ⟨i,j⟩ _
      simpa only [Real.norm_eq_abs] using hv i j
    _ = _ := by simp

-- @node: restrictedCandidate_fixedLabelObservation_norm_le
/-- For [nonnegative latent-radius and mechanism bounds](hyp:K,L), if [a candidate satisfies the observation-radius and mechanism-Lipschitz
restrictions](hyp:hR), then [every fixed-label observation, at any latent input,
has norm at most the total observation dimension times the observation radius](goal). -/
lemma restrictedCandidate_fixedLabelObservation_norm_le {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    (K L : ℝ≥0) (R : NCMIn kind dims dag G C counts F0 F1)
    (hR : restrictedCandidate K L R) (c : CategoricalStratum kind) (z : Latent dims) :
    ‖fixedLabelObservation R.canonical.toEuclideanSCM (categoricalStratumAssignment c) z‖ ≤
      (∑ i, valueDim (kind i)) * (estimationObservationRadius kind K : ℝ) := by
  apply joint_norm_le_of_coordinate_bound
  exact fun i j => restrictedCandidate_intervened_coordinate_bound K L R hR
    ⟨categoricalStratumAssignment c, categoricalStratumAssignment_admissible R.canonical.toEuclideanSCM c⟩
    (categoricalStratumAssignment_coordinate_bound R.canonical K c) _ i j

-- @node: categoricalStratum_grid_readout_error_le
/-- For [a nonnegative mechanism bound](hyp:L), suppose [the continuous mechanisms
are Lipschitz with that bound](hyp:hL), [the grid representative selected by the
code is within the mesh radius of every cube point](hyp:hgrid), and [the latent
input lies in that cube](hyp:hz). Then [the fixed-label observation and its grid
readout are within the fixed-label Lipschitz budget times the mesh radius](goal). -/
lemma categoricalStratum_grid_readout_error_le
    (M : EuclideanSCM kind dims) (L : ℝ≥0)
    (hL : ContinuousMechanismsLipschitz M L)
    {s : ℕ} {K : ℝ≥0} {rho : ℝ}
    (grid : Fin s → boundedCube (∑ j, dims j) K)
    (code : boundedCube (∑ j, dims j) K → Fin s)
    (hgrid : ∀ x, dist x.val (grid (code x)).val ≤ rho)
    (z : Latent dims) (hz : z ∈ jointLatentCube dims K) (c : CategoricalStratum kind) :
    dist (fixedLabelObservation M (categoricalStratumAssignment c) z)
      (categoricalStratumVectorObservation M c
        (grid (code (simulationLatentCubePoint K z))).val) ≤
        (fixedLabelLipschitzBudget M L (n*n+n) : ℝ) * rho := by
  have h := (categoricalStratumVectorObservation_lipschitz M L hL c).dist_le_mul
    (jointLatentVectorEquiv dims z) (grid (code (simulationLatentCubePoint K z))).val
  simp only [categoricalStratumVectorObservation, LinearIsometryEquiv.symm_apply_apply] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [simulationLatentCubePoint_eq_of_mem K z hz] using
    hgrid (simulationLatentCubePoint K z)

-- @node: generatorClassN_jointNonGumbel_mem_cube
/-- For [the generator component dimensions](hyp:dC) and [a nonnegative cube
radius](hyp:K), [the concatenated non-Gumbel latent output of any candidate in
the specified generator class lies in that cube for every simulation input](goal). -/
lemma generatorClassN_jointNonGumbel_mem_cube {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C}
    (dC : ∀ j, Fin (counts j) → ℕ) (K : ℝ≥0) (D c1 c2 : ℕ)
    (L1 L2 : ℕ → ℕ) (tau : ℕ → ℝ) (r : ℕ)
    (R : NCMIn kind dims dag G C counts F0
      (generatorClassN counts dC K D c1 c2 L1 L2 tau r))
    (z : SimulationInput kind counts) :
    jointNonGumbel (ncmSimulationExogenous R z) ∈ jointLatentCube dims K := by
  rintro ⟨j,i⟩
  exact generatorClassN_mem_boundedCube dC K D c1 c2 L1 L2 tau r j
    (R.generator j) (R.generatorMem j) (z.1 j) i

-- @node: restrictedCandidate_causalTable_grid_readout
/-- For [generator component dimensions](hyp:dC) and [nonnegative latent-radius
and mechanism bounds](hyp:K,L), suppose [the candidate satisfies the corresponding
restrictions](hyp:hR) and [every coded grid representative is within the mesh
radius of its cube point](hyp:hgrid). Then [simulated observations and all
fixed-label grid readouts have norm at most the total observation dimension times
the observation radius, and every fixed-label simulation differs from its coded
readout by at most the fixed-label Lipschitz budget times the mesh radius](goal). -/
lemma restrictedCandidate_causalTable_grid_readout {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C}
    (dC : ∀ j, Fin (counts j) → ℕ) (K L : ℝ≥0) (D c1 c2 : ℕ)
    (L1 L2 : ℕ → ℕ) (tau : ℕ → ℝ) (r : ℕ)
    (R : NCMIn kind dims dag G C counts F0
      (generatorClassN counts dC K D c1 c2 L1 L2 tau r))
    (hR : restrictedCandidate K L R)
    {s : ℕ} {rho : ℝ} (grid : Fin s → boundedCube (∑ j, dims j) K)
    (code : boundedCube (∑ j, dims j) K → Fin s)
    (hgrid : ∀ x, dist x.val (grid (code x)).val ≤ rho) :
    let B := (∑ i, valueDim (kind i)) * (estimationObservationRadius kind K : ℝ)
    let v := fun c j => categoricalStratumVectorObservation R.canonical.toEuclideanSCM c
      (grid j).val
    (∀ z, ‖ncmEval R z‖ ≤ B) ∧ (∀ c j, ‖v c j‖ ≤ B) ∧
      ∀ z c, dist (fixedLabelObservation R.canonical.toEuclideanSCM
        (categoricalStratumAssignment c) (jointNonGumbel (ncmSimulationExogenous R z)))
        (v c (code (simulationLatentCubePoint K
          (jointNonGumbel (ncmSimulationExogenous R z))))) ≤
        (fixedLabelLipschitzBudget R.canonical.toEuclideanSCM L (n*n+n) : ℝ) * rho := by
  have hcont : ContinuousMechanismsLipschitz R.canonical.toEuclideanSCM L := by
    intro i d hi
    rw [funext (canonical_continuousMap_eq_weights R.canonical i d hi)]
    exact (hR i).1
  refine ⟨fun z => joint_norm_le_of_coordinate_bound _ _
    (restrictedCandidate_ncmEval_coordinate_bound K L R hR z),
    fun c j => restrictedCandidate_fixedLabelObservation_norm_le K L R hR c _, ?_⟩
  intro z c
  exact categoricalStratum_grid_readout_error_le R.canonical.toEuclideanSCM L hcont
    grid code hgrid _ (generatorClassN_jointNonGumbel_mem_cube dC K D c1 c2 L1 L2 tau r R z) c

-- @node: causalTablePropensityBudget
/-- For [a canonical causal model with finitely many nodes and latent blocks,
specified node types and block dimensions, a directed acyclic graph, an
undirected graph, and block incidence sets](hyp:M,n,b,kind,dims,dag,G,C) and [a nonnegative mechanism
bound](hyp:L), [the causal-table propensity budget](goal) is the sum over nodes
of the mechanism bound times the structural input dimension times one plus the
fixed-label Lipschitz budget at that node's topological rank. -/
def causalTablePropensityBudget (M : CanonicalSCM kind dims dag G C) (L : ℝ≥0) : ℝ≥0 :=
  ∑ i, L * ((structuralInputSize M.toEuclideanSCM i : ℝ≥0) *
    (fixedLabelLipschitzBudget M.toEuclideanSCM L (dag.topoOrder i) + 1))

-- @node: causalTablePropensityBudget_node_le
/-- For [a nonnegative mechanism bound](hyp:L), [each node's mechanism bound times its structural input dimension times
one plus its fixed-label Lipschitz budget is at most the total causal-table
propensity budget](goal). -/
lemma causalTablePropensityBudget_node_le
    (M : CanonicalSCM kind dims dag G C) (L : ℝ≥0) (i : Fin n) :
    L * ((structuralInputSize M.toEuclideanSCM i : ℝ≥0) *
      (fixedLabelLipschitzBudget M.toEuclideanSCM L (dag.topoOrder i) + 1)) ≤
      causalTablePropensityBudget M L :=
  by
    unfold causalTablePropensityBudget
    exact Finset.single_le_sum (f := fun j => L *
      ((structuralInputSize M.toEuclideanSCM j : ℝ≥0) *
        (fixedLabelLipschitzBudget M.toEuclideanSCM L (dag.topoOrder j) + 1)))
      (fun _ _ => zero_le) (Finset.mem_univ i)

-- @node: restrictedCandidate_exists_causalTable_grid
/-- Given [fallback categorical probability vectors](hyp:p0), [generator component
dimensions](hyp:dC), and [nonnegative latent-radius and mechanism bounds](hyp:K,L),
suppose [the candidate satisfies those restrictions](hyp:hR), [the probability-grid
resolution is positive](hyp:hN), [the mesh radius is nonnegative](hyp:hrho), and
[each coded grid representative is within that radius of its cube point](hyp:hgrid).
Then [there is a table in the finite propensity alphabet whose entries depend
only on earlier labels and whose coordinate errors on every generated latent
input are bounded by the propensity budget times the mesh radius plus the
reciprocal probability-grid resolution](goal). -/
lemma restrictedCandidate_exists_causalTable_grid {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C}
    (p0 : ∀ i k, kind i = Sum.inr k → probabilitySimplex k)
    (dC : ∀ j, Fin (counts j) → ℕ) (K L : ℝ≥0) (D c1 c2 : ℕ)
    (L1 L2 : ℕ → ℕ) (tau : ℕ → ℝ) (r : ℕ)
    (R : NCMIn kind dims dag G C counts F0
      (generatorClassN counts dC K D c1 c2 L1 L2 tau r))
    (hR : restrictedCandidate K L R)
    {s N : ℕ} (hN : 0 < N) {rho : ℝ} (hrho : 0 ≤ rho)
    (grid : Fin s → boundedCube (∑ j, dims j) K)
    (code : boundedCube (∑ j, dims j) K → Fin s)
    (hgrid : ∀ x, dist x.val (grid (code x)).val ≤ rho) :
    ∃ table ∈ causalPropensityTableGrid p0 N s,
      (∀ i k hi c c', (∀ j, dag.topoOrder j < dag.topoOrder i → c j = c' j) →
        table i k hi c = table i k hi c') ∧
      ∀ i k hi z c j,
        |(fixedLabelCategoricalPropensity R.canonical c i k hi
            (jointNonGumbel (ncmSimulationExogenous R z))).val j -
          (table i k hi c (code (simulationLatentCubePoint K
            (jointNonGumbel (ncmSimulationExogenous R z))))).val j| ≤
          (causalTablePropensityBudget R.canonical L : ℝ) * rho + (N : ℝ)⁻¹ := by
  have hcont : ContinuousMechanismsLipschitz R.canonical.toEuclideanSCM L := by
    intro i d hi
    rw [funext (canonical_continuousMap_eq_weights R.canonical i d hi)]
    exact (hR i).1
  have hprop : CategoricalPropensityLipschitz R.canonical.toEuclideanSCM R.canonical.f L := by
    refine ⟨fun i _ _ => (hR i).1, ?_⟩
    intro i k hi j
    exact canonical_propensity_conditional_probability R.canonical i k hi j
  obtain ⟨table, ht, herr, hcausal⟩ := exists_causalPropensityTableGrid_approximation
    p0 R.canonical L hcont hprop hN grid code hgrid
  refine ⟨table, ht, hcausal, ?_⟩
  intro i k hi z c j
  have hz := generatorClassN_jointNonGumbel_mem_cube dC K D c1 c2 L1 L2 tau r R z
  have h := herr i k hi c (simulationLatentCubePoint K
    (jointNonGumbel (ncmSimulationExogenous R z))) j
  rw [simulationLatentCubePoint_eq_of_mem K _ hz,
    LinearIsometryEquiv.symm_apply_apply] at h
  apply h.trans
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_right _ hrho
  exact_mod_cast causalTablePropensityBudget_node_le R.canonical L i

-- @node: canonical_fixedLabelLipschitzBudget_eq
/-- For [a common nonnegative mechanism bound](hyp:L), [two canonical models
with the same graph, incidence structure, and dimensions have equal fixed-label
Lipschitz budgets at every recursion depth](goal). -/
lemma canonical_fixedLabelLipschitzBudget_eq
    (M M' : CanonicalSCM kind dims dag G C) (L : ℝ≥0) (r : ℕ) :
    fixedLabelLipschitzBudget M.toEuclideanSCM L r =
      fixedLabelLipschitzBudget M'.toEuclideanSCM L r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [fixedLabelLipschitzBudget, ih]
    rfl

-- @node: causalTablePropensityBudget_eq
/-- For [a common nonnegative mechanism bound](hyp:L), [two canonical models
with the same graph, incidence structure, and dimensions have equal causal-table
propensity budgets](goal). -/
lemma causalTablePropensityBudget_eq
    (M M' : CanonicalSCM kind dims dag G C) (L : ℝ≥0) :
    causalTablePropensityBudget M L = causalTablePropensityBudget M' L := by
  unfold causalTablePropensityBudget
  apply Finset.sum_congr rfl
  intro i _
  rw [canonical_fixedLabelLipschitzBudget_eq M M']
  rfl

-- @node: restrictedCandidate_causalTable_grid_sampling
/-- Given [fallback categorical probability vectors](hyp:p0), [generator component
dimensions](hyp:dC), and [nonnegative latent-radius and mechanism bounds](hyp:K,L),
assume [the candidate satisfies those restrictions](hyp:hR), [the probability-grid
resolution is positive](hyp:hN), [the mesh radius is nonnegative](hyp:hrho), [the
latent grid code is measurable](hyp:hcode), and [its representatives approximate
all cube points within the mesh radius](hyp:hgrid). Then [a table in the finite
propensity alphabet exists such that, for any positive sample size and nonnegative
error tolerance dominating twice the summed categorical noise dimensions times
the propensity approximation error, empirical errors at most that tolerance for
the ambiguity event and every type subset imply a Wasserstein distance of order
one from the observational law to the empirical simulation law of at most twice
the fixed-label Lipschitz budget times the mesh radius plus eight times the norm
bound times the tolerance](goal). -/
lemma restrictedCandidate_causalTable_grid_sampling {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C}
    (p0 : ∀ i k, kind i = Sum.inr k → probabilitySimplex k)
    (dC : ∀ j, Fin (counts j) → ℕ) (K L : ℝ≥0) (D c1 c2 : ℕ)
    (L1 L2 : ℕ → ℕ) (tau : ℕ → ℝ) (r : ℕ)
    (R : NCMIn kind dims dag G C counts F0
      (generatorClassN counts dC K D c1 c2 L1 L2 tau r))
    (hR : restrictedCandidate K L R)
    {s N : ℕ} (hN : 0 < N) {rho : ℝ} (hrho : 0 ≤ rho)
    (grid : Fin s → boundedCube (∑ j, dims j) K)
    (code : boundedCube (∑ j, dims j) K → Fin s) (hcode : Measurable code)
    (hgrid : ∀ x, dist x.val (grid (code x)).val ≤ rho) :
    ∃ table ∈ causalPropensityTableGrid p0 N s,
      let code' := code ∘ simulationLatentCubePoint K
      let a := (causalTablePropensityBudget R.canonical L : ℝ) * rho + (N : ℝ)⁻¹
      let bad := ncmCausalTableAmbiguity R code' table a
      let B := (∑ i, valueDim (kind i)) * (estimationObservationRadius kind K : ℝ)
      ∀ (m : ℕ), 0 < m → ∀ (draws : Fin m → SimulationInput kind counts) (e : ℝ),
        0 ≤ e →
        2 * (∑ i, ∑ _c : CategoricalStratum kind, (noiseDim (kind i) : ℝ)) * a ≤ e →
        |(simulationInputLaw kind counts).real bad - (m : ℝ)⁻¹ *
          ∑ j, bad.indicator (fun _ => (1 : ℝ)) (draws j)| ≤ e →
        (∀ t : Set (Fin s × CategoricalStratum kind),
          |(simulationInputLaw kind counts).real (ncmCausalTableType R code' table ⁻¹' t) -
            (m : ℝ)⁻¹ * ∑ j,
              if ncmCausalTableType R code' table (draws j) ∈ t then (1 : ℝ) else 0| ≤ e) →
        wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
          (empiricalMeasure (fun j => ncmEval R (draws j))) ≤
          ENNReal.ofReal (2 *
            ((fixedLabelLipschitzBudget R.canonical.toEuclideanSCM L (n*n+n) : ℝ) * rho) +
              8 * B * e) := by
  classical
  obtain ⟨table, ht, hcausal, herr⟩ := restrictedCandidate_exists_causalTable_grid
    p0 dC K L D c1 c2 L1 L2 tau r R hR hN hrho grid code hgrid
  obtain ⟨hbound, hvbound, hread⟩ := restrictedCandidate_causalTable_grid_readout
    dC K L D c1 c2 L1 L2 tau r R hR grid code hgrid
  refine ⟨table, ht, ?_⟩
  intro code' a bad B m hm draws e he hevent hamb hsub
  have hcode' : Measurable code' := by fun_prop
  exact (ncmCausalTable_sampling_transport R code' hcode' table hcausal a
    (by dsimp [a]; positivity) herr
    (fun c j => categoricalStratumVectorObservation R.canonical.toEuclideanSCM c (grid j).val)
    ((fixedLabelLipschitzBudget R.canonical.toEuclideanSCM L (n*n+n) : ℝ) * rho)
    B e (by positivity) (by dsimp [B]; positivity) he hbound hvbound hread
    hevent).2.2 m hm draws hamb hsub

end
end Papers.TbsNeuralCausalPi
