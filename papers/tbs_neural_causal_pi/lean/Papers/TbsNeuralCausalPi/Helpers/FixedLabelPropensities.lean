module
public import Papers.TbsNeuralCausalPi.Helpers.FixedLabelStrata
public import Papers.TbsNeuralCausalPi.Helpers.FixedLabelLatentCoordinates
public import Papers.TbsNeuralCausalPi.Helpers.SimulationPrefixTables
/-! # Actual categorical propensity tables with labels fixed

The structural input just before a node is visited is a Lipschitz function
of the joint non-Gumbel vector when categorical labels are fixed. It always
belongs to the actual structural domain. Consequently canonical propensities
give closed-simplex-valued Lipschitz table entries, including zero weights.
On the realized label stratum these entries are the factual propensities.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

-- @node: fixedLabelStructuralInput
/-- Given [a structural causal model](hyp:M), [fixed categorical labels](hyp:c),
[a node](hyp:i), and [joint non-Gumbel latent coordinates](hyp:z), the
[fixed-label structural input](goal) is that node's input just before it is
visited, obtained by evaluating earlier nodes with those labels fixed. -/
def fixedLabelStructuralInput (M : EuclideanSCM kind dims)
    (c : CategoricalStratum kind) (i : Fin n) (z : Latent dims) :=
  structuralInput M i
    (evalSteps M (categoricalStratumAssignment c) (nonGumbelLift z) (M.dag.topoOrder i))
    (nonGumbelLift z)

-- @node: fixedLabelStructuralInput_measurable
/-- [For fixed categorical labels and a node, the structural input is a
measurable function of the joint non-Gumbel latent coordinates](goal). -/
@[fun_prop] lemma fixedLabelStructuralInput_measurable
    (M : EuclideanSCM kind dims) (c : CategoricalStratum kind) (i : Fin n) :
    Measurable (fixedLabelStructuralInput M c i) := by
  fun_prop [fixedLabelStructuralInput]

-- @node: fixedLabelStructuralInput_mem_domain
/-- [The structural input obtained from any fixed categorical labels and
joint non-Gumbel latent vector belongs to the node's structural domain](goal). -/
lemma fixedLabelStructuralInput_mem_domain (M : EuclideanSCM kind dims)
    (c : CategoricalStratum kind) (i : Fin n) (z : Latent dims) :
    fixedLabelStructuralInput M c i z ∈ M.domain i := by
  exact evalSteps_structuralInput_mem_domain M (categoricalStratumAssignment c)
    (categoricalStratumAssignment_admissible M c) (nonGumbelLift z) i _ rfl

-- @node: fixedLabelStructuralInput_lipschitz
/-- For [a nonnegative constant](hyp:L), if [the continuous mechanisms are
Lipschitz with that constant](hyp:hL), [the fixed-label structural input is Lipschitz in the latent
coordinates, with constant equal to the input size times one plus the
fixed-label propagation budget before the node is visited](goal). -/
lemma fixedLabelStructuralInput_lipschitz (M : EuclideanSCM kind dims)
    (L : ℝ≥0) (hL : ContinuousMechanismsLipschitz M L)
    (c : CategoricalStratum kind) (i : Fin n) :
    LipschitzWith ((structuralInputSize M i : ℝ≥0) *
      (fixedLabelLipschitzBudget M L (M.dag.topoOrder i) + 1))
        (fixedLabelStructuralInput M c i) := by
  apply LipschitzWith.of_dist_le_mul
  intro z z'
  have h := evalSteps_fixed_labels_dist_le M L hL
    ⟨categoricalStratumAssignment c, categoricalStratumAssignment_admissible M c⟩
    (categoricalStratumAssignment_covers M c) (M.dag.topoOrder i) z z'
  apply (structuralInput_dist_nonGumbelLift_le M i _ _ z z').trans
  calc
    _ ≤ (structuralInputSize M i : ℝ) *
        ((fixedLabelLipschitzBudget M L (M.dag.topoOrder i) : ℝ) * dist z z' +
          dist z z') := mul_le_mul_of_nonneg_left (add_le_add h le_rfl) (by positivity)
    _ = _ := by simp only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast,
        NNReal.coe_one]; ring

-- @node: fixedLabelCategoricalPropensity
/-- Given [a canonical structural causal model](hyp:M), [fixed categorical
labels](hyp:c), [a node](hyp:i), [a category count](hyp:k) [identifying that
node as categorical](hyp:hi), and [joint non-Gumbel latent coordinates](hyp:z),
the [fixed-label propensity vector](goal) evaluates the node's mechanism at its
fixed-label structural input and regards its category weights as a probability
vector in the closed simplex. -/
def fixedLabelCategoricalPropensity (M : CanonicalSCM kind dims dag G C)
    (c : CategoricalStratum kind) (i : Fin n) (k : ℕ) (hi : kind i = Sum.inr k)
    (z : Latent dims) : probabilitySimplex k :=
  ⟨fun j => (M.f i (fixedLabelStructuralInput M.toEuclideanSCM c i z)).ofLp
      (Fin.cast (congrArg outputDim hi).symm j),
    M.simplex i k hi _ (fixedLabelStructuralInput_mem_domain M.toEuclideanSCM c i z).1⟩

-- @node: fixedLabelCategoricalPropensity_measurable
/-- For [a node with the given number of categories](hyp:hi), [its
fixed-label propensity vector is measurable in the joint non-Gumbel latent
coordinates](goal). -/
@[fun_prop] lemma fixedLabelCategoricalPropensity_measurable
    (M : CanonicalSCM kind dims dag G C) (c : CategoricalStratum kind)
    (i : Fin n) (k : ℕ) (hi : kind i = Sum.inr k) :
    Measurable (fixedLabelCategoricalPropensity M c i k hi) := by
  apply Measurable.subtype_mk
  apply measurable_pi_lambda
  intro j
  exact (measurable_pi_apply _).comp (scm_ofLp_measurable.comp
    ((M.structuralMeasurable i).comp
      (fixedLabelStructuralInput_measurable M.toEuclideanSCM c i)))

-- @node: fixedLabelCategoricalPropensity_coordinate_lipschitz
/-- Given [a nonnegative Lipschitz bound](hyp:L), suppose [the continuous
mechanisms satisfy that bound](hyp:hcont) and [the categorical propensities
satisfy it on their structural domains](hyp:hprop). For [a node with the given
number of categories](hyp:hi), [each fixed-label propensity coordinate is
Lipschitz in the latent vector, with constant equal to that bound times the
structural input size times one plus the propagation budget before the node](goal). -/
lemma fixedLabelCategoricalPropensity_coordinate_lipschitz
    (M : CanonicalSCM kind dims dag G C) (L : ℝ≥0)
    (hcont : ContinuousMechanismsLipschitz M.toEuclideanSCM L)
    (hprop : CategoricalPropensityLipschitz M.toEuclideanSCM M.f L)
    (c : CategoricalStratum kind) (i : Fin n) (k : ℕ) (hi : kind i = Sum.inr k)
    (j : Fin k) :
    LipschitzWith (L * ((structuralInputSize M.toEuclideanSCM i : ℝ≥0) *
      (fixedLabelLipschitzBudget M.toEuclideanSCM L (dag.topoOrder i) + 1)))
      (fun z => (fixedLabelCategoricalPropensity M c i k hi z).val j) := by
  apply LipschitzWith.of_dist_le_mul
  intro z z'
  apply (PiLp.dist_apply_le _ _ _).trans
  apply ((hprop.1 i k hi).dist_le_mul _
    (fixedLabelStructuralInput_mem_domain M.toEuclideanSCM c i z) _
    (fixedLabelStructuralInput_mem_domain M.toEuclideanSCM c i z')).trans
  simpa only [NNReal.coe_mul, mul_assoc, show M.toEuclideanSCM.dag = dag from rfl] using
    mul_le_mul_of_nonneg_left
      ((fixedLabelStructuralInput_lipschitz M.toEuclideanSCM L hcont c i).dist_le_mul z z')
      L.coe_nonneg

-- @node: evalSteps_factual_stratum_eq_fixed_labels
/-- [Fixing categorical labels to their factual values and retaining only
the joint non-Gumbel latent coordinates reproduces the factual evaluation
history after any number of steps](goal). -/
lemma evalSteps_factual_stratum_eq_fixed_labels (M : EuclideanSCM kind dims)
    (u : Exogenous kind dims) (r : ℕ) :
    evalSteps M (categoricalStratumAssignment
      (observedCategoricalStratum (intervenedEval M (fun _ => none) u)))
        (nonGumbelLift (jointNonGumbel u)) r =
      evalSteps M (fun _ => none) u r := by
  let c := observedCategoricalStratum (intervenedEval M (fun _ => none) u)
  exact (evalSteps_fixed_labels_eq_nonGumbelLift M (categoricalStratumAssignment c)
    (categoricalStratumAssignment_covers M c) u r).symm.trans
      (evalSteps_eq_of_factual_assignments M (fun _ => none)
        (categoricalStratumAssignment c) u (fun i => by
          cases ht : categoricalStratumAssignment c i with
          | none => exact Or.inl rfl
          | some v =>
            apply Or.inr
            congr 1
            exact PiLp.ext (categoricalStratumAssignment_matches_factual M u i v ht)) r)

-- @node: fixedLabelStructuralInput_factual_stratum
/-- [At the factual categorical stratum and factual non-Gumbel latent vector,
the fixed-label structural input equals the actual input just before the node
is visited in the evaluation without intervention](goal). -/
lemma fixedLabelStructuralInput_factual_stratum (M : EuclideanSCM kind dims)
    (u : Exogenous kind dims) (i : Fin n) :
    fixedLabelStructuralInput M
      (observedCategoricalStratum (intervenedEval M (fun _ => none) u)) i
      (jointNonGumbel u) =
    structuralInput M i (evalSteps M (fun _ => none) u (M.dag.topoOrder i)) u := by
  unfold fixedLabelStructuralInput
  rw [evalSteps_factual_stratum_eq_fixed_labels]
  rfl

-- @node: fixedLabelCategoricalPropensity_factual_stratum
/-- For [a node with the given number of categories](hyp:hi), [each
fixed-label propensity coordinate at the factual stratum and latent vector
equals the corresponding coordinate of the mechanism evaluated at its factual
structural input](goal). -/
lemma fixedLabelCategoricalPropensity_factual_stratum
    (M : CanonicalSCM kind dims dag G C) (u : Exogenous kind dims)
    (i : Fin n) (k : ℕ) (hi : kind i = Sum.inr k) (j : Fin k) :
    (fixedLabelCategoricalPropensity M
      (observedCategoricalStratum (intervenedEval M.toEuclideanSCM (fun _ => none) u))
      i k hi (jointNonGumbel u)).val j =
      (M.f i (structuralInput M.toEuclideanSCM i
        (evalSteps M.toEuclideanSCM (fun _ => none) u (dag.topoOrder i)) u)).ofLp
          (Fin.cast (congrArg outputDim hi).symm j) := by
  simp only [fixedLabelCategoricalPropensity, fixedLabelStructuralInput_factual_stratum]
  rfl

-- @node: exists_fixedLabelCategoricalPropensity_tables
/-- Given [a nonnegative Lipschitz bound](hyp:L), assume [the continuous
mechanisms obey it](hyp:hcont), [the categorical propensities obey it on their
domains](hyp:hprop), [the chosen node has the given number of categories](hyp:hi),
[the approximation tolerance is positive](hyp:heta), and [the code assigns
each cube point a grid point within the mesh radius](hyp:hgrid). Then [there
is a finite family of simplex-valued tables whose log cardinality is at most
the number of strata times the category count times the grid size times the
logarithm of the sum of two and the reciprocal tolerance, containing a table that
approximates every stratum's propensity coordinate within the mesh radius
times its Lipschitz bound plus the tolerance](goal).

The propensity Lipschitz bound is the mechanism bound times the structural
input size times the sum of one and the fixed-label propagation budget before
the node. -/
lemma exists_fixedLabelCategoricalPropensity_tables
    (M : CanonicalSCM kind dims dag G C) (L : ℝ≥0)
    (hcont : ContinuousMechanismsLipschitz M.toEuclideanSCM L)
    (hprop : CategoricalPropensityLipschitz M.toEuclideanSCM M.f L)
    (i : Fin n) (k : ℕ) (hi : kind i = Sum.inr k)
    {s : ℕ} {K rho eta : ℝ} (heta : 0 < eta)
    (grid : Fin s → boundedCube (∑ j, dims j) K)
    (code : boundedCube (∑ j, dims j) K → Fin s)
    (hgrid : ∀ x, dist x.val (grid (code x)).val ≤ rho) :
    ∃ T : Finset (CategoricalStratum kind → Fin s → probabilitySimplex k),
      Real.log (T.card : ℝ) ≤
        (∑ _c : CategoricalStratum kind, ((k * s : ℕ) : ℝ)) *
          Real.log (2 + eta⁻¹) ∧
      ∃ table ∈ T, ∀ c x j,
        |(fixedLabelCategoricalPropensity M c i k hi
            ((jointLatentVectorEquiv dims).symm x.val)).val j -
          (table c (code x)).val j| ≤
        (L * ((structuralInputSize M.toEuclideanSCM i : ℝ≥0) *
          (fixedLabelLipschitzBudget M.toEuclideanSCM L (dag.topoOrder i) + 1)) : ℝ≥0) *
            rho + eta := by
  let B : ℝ≥0 := L * ((structuralInputSize M.toEuclideanSCM i : ℝ≥0) *
    (fixedLabelLipschitzBudget M.toEuclideanSCM L (dag.topoOrder i) + 1))
  obtain ⟨T, hT, happ⟩ := exists_simulation_prefix_table_net
    (fun _ : CategoricalStratum kind => k)
    (fun c => fixedLabelCategoricalPropensity M c i k hi 0) heta B grid code hgrid
  refine ⟨T, hT, ?_⟩
  apply happ (fun c x => fixedLabelCategoricalPropensity M c i k hi
    ((jointLatentVectorEquiv dims).symm x.val))
  intro c j
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [LinearIsometryEquiv.dist_map, Subtype.dist_eq] using
    (fixedLabelCategoricalPropensity_coordinate_lipschitz M L hcont hprop c i k hi j).dist_le_mul
      ((jointLatentVectorEquiv dims).symm x.val) ((jointLatentVectorEquiv dims).symm y.val)

end
end Papers.TbsNeuralCausalPi
