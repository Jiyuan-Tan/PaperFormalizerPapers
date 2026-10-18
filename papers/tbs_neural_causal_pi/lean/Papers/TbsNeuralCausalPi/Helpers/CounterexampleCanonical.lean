module
public import Papers.TbsNeuralCausalPi.Setup.Assumptions.Estimation
public import Papers.TbsNeuralCausalPi.Setup.CitedResults
public import Papers.TbsNeuralCausalPi.Helpers.FiniteLatentRegularity
public import Papers.TbsNeuralCausalPi.Helpers.CounterexampleMechanisms
public import Papers.TbsNeuralCausalPi.Helpers.CounterexampleFiniteLaws
public import Papers.TbsNeuralCausalPi.Helpers.CanonicalLatentIndependence
public import Papers.TbsNeuralCausalPi.Helpers.InterventionalMoments
/-! # Backdoor observational convergence with an ATE gap -/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.unusedSimpArgs false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.deprecated false
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable

/-- For [a source node numbered from zero to two](hyp:i) and [a target node in the same range](hyp:j),
[a directed edge exists exactly when the source number is smaller than the target number](goal). -/
def backdoorEdges (i j : Fin 3) : Prop := i < j
-- @node: backdoorAcyclic
/-- [The three-node backdoor edge relation has no directed cycle](goal). -/
lemma backdoorAcyclic : ∀ i, ¬ Relation.TransGen backdoorEdges i i := by
  intro i h
  have hlt : ∀ {a b}, Relation.TransGen backdoorEdges a b → a < b := by
    intro a b hab
    induction hab with
    | single h => exact h
    | tail h hlast ih => exact lt_trans ih hlast
  exact (lt_irrefl i) (hlt h)
/-- [The backdoor directed acyclic graph has arrows from node zero to node one,
from node zero to node two, and from node one to node two](goal). -/
def backdoorDAG : Causalean.Graph.DAG (Fin 3) :=
  ⟨backdoorEdges, inferInstance, backdoorAcyclic⟩
/-- [The backdoor causal graph combines the three ordered directed arrows with no bidirected edges](goal). -/
def backdoorGraph : CausalGraph 3 := (backdoorDAG, ⊥)
/-- For [a node numbered from zero to two](hyp:i), [its variable type is binary categorical
at node one and one-dimensional continuous at nodes zero and two](goal). -/
def backdoorKind (i : Fin 3) : NodeKind := if i = 1 then .inr 2 else .inl 1
/-- For [a Boolean treatment choice](hyp:t), [the intervention sets node one to category two
when true and category one when false, leaving the other nodes unassigned](goal). -/
def binaryAssignment (t : Bool) : Intervention backdoorKind :=
  fun i => if i = 1 then some (WithLp.toLp 1 (fun _ => if t then 2 else 1)) else none
-- @node: binaryAssignment_admissible
/-- For either Boolean treatment choice, [the corresponding assignment uses a valid category
for the binary treatment node](goal). -/
lemma binaryAssignment_admissible (t : Bool) :
    AdmissibleIntervention backdoorKind (binaryAssignment t) := by
  intro i v hv
  by_cases hi : i = 1
  · subst i
    simp only [binaryAssignment, ite_true, Option.some.injEq] at hv
    subst v
    cases t
    · exact ⟨⟨0, by decide⟩, by intro j; simp⟩
    · exact ⟨⟨1, by decide⟩, by intro j; simp⟩
  · simp [binaryAssignment, hi] at hv
-- @node: binaryAssignment_sameTreatment
/-- [The two binary interventions assign exactly the same set of nodes](goal). -/
lemma binaryAssignment_sameTreatment : ∀ i,
    (binaryAssignment true i).isSome = (binaryAssignment false i).isSome := by
  intro i
  by_cases hi : i = 1 <;> simp [binaryAssignment, hi]
-- @node: backdoorOutcomeKind
/-- [Node two, the outcome node, is one-dimensional and continuous](goal). -/
lemma backdoorOutcomeKind : backdoorKind 2 = Sum.inl 1 := by
  unfold backdoorKind
  rw [if_neg (by decide)]
/-- From [a joint realization of the three observed variables](hyp:v),
[the outcome is the scalar value at node two](goal). -/
def backdoorOutcome (v : Joint backdoorKind) : ℝ :=
  v.ofLp ⟨2, ⟨0, Nat.zero_lt_succ 0⟩⟩
/-- For [a structural causal model with the backdoor variable types](hyp:M),
[the treatment-effect contrast is the latent-law integral of the outcome under category two
minus the outcome under category one](goal).

This totalized integral equals the domain-restricted `ate` when the contrast is integrable;
the witness and identification proofs establish that integrability locally. -/
def backdoorATE {b : ℕ} {dims : Fin b → ℕ} (M : EuclideanSCM backdoorKind dims) : ℝ :=
  ∫ u, backdoorOutcome (intervenedEval M (binaryAssignment true) u) -
    backdoorOutcome (intervenedEval M (binaryAssignment false) u) ∂M.latentLaw

/-- For [a canonical structural causal model on the backdoor graph](hyp:M),
[the counterexample assumptions](goal) require [mutual independence of the named latent blocks](step:1),
[a partition of latent coordinates into private blocks and categorical Gumbel noises](step:2),
[categorical generation by the Gumbel argmax rule](step:3),
[a common nonnegative Lipschitz bound for the continuous mechanisms and categorical propensities,
with the propensities equal to conditional category probabilities](step:4),
[a positive almost-sure bound on observed variables and private latent coordinates](step:5), and
[generator regularity of every private block law](step:6). -/
def counterexampleAtoms {b : ℕ} {dims : Fin b → ℕ}
    {G : SimpleGraph (Fin 3)} {C : Fin b → Set (Fin 3)}
    (M : CanonicalSCM backdoorKind dims backdoorDAG G C) : Prop :=
  LatentBlocksIndependent M.toEuclideanSCM ∧ LatentGumbelDecomposition M.toEuclideanSCM ∧
  CategoricalGumbelArgmax M.toEuclideanSCM M.f ∧
  (∃ L : ℝ≥0, ContinuousMechanismsLipschitz M.toEuclideanSCM L ∧
    CategoricalPropensityLipschitz M.toEuclideanSCM M.f L) ∧
  (∃ K : ℝ, VariablesBoundedAt M.toEuclideanSCM K) ∧ LatentLawsGeneratorRegular M

-- @node: ass:pin-204
/-- In [a canonical backdoor model without bidirected edges](hyp:M), for [a private latent block](hyp:j)
and [a designated coordinate in that block](hyp:a'), [the second Bernoulli reading](goal) requires
[probability one third of value one](step:1) and [probability two thirds of value zero](step:2).

This law is a conclusion of the constructed witness. -/
def CounterexampleSecondBernoulliReading {b : ℕ} {dims : Fin b → ℕ}
    {C : Fin b → Set (Fin 3)}
    (M : CanonicalSCM backdoorKind dims backdoorDAG (⊥ : SimpleGraph (Fin 3)) C)
    (j : Fin b) (a' : Fin (dims j)) : Prop :=
  M.latentLaw {u | (blockProjection j u).ofLp a' = 1} = ENNReal.ofReal (1/3 : ℝ) ∧
    M.latentLaw {u | (blockProjection j u).ofLp a' = 0} = ENNReal.ofReal (2/3 : ℝ)

/-- For [a canonical backdoor model without bidirected edges](hyp:M), [a private latent block](hyp:j),
[a first coordinate](hyp:a), and [a second coordinate in that block](hyp:a'),
[the Bernoulli-coordinate condition](goal) requires [the coordinates to be distinct](step:1),
[the block to belong to the outcome's component](step:2),
[the first coordinate to be Bernoulli with success probability three fifths](step:3),
[the second to be Bernoulli with success probability one third](step:4),
[independence of the two coordinates](step:5), and
[probabilities one third and two thirds for the second coordinate's values one and zero](step:6). -/
def counterexampleBernoulliCoordinates {b : ℕ} {dims : Fin b → ℕ}
    {C : Fin b → Set (Fin 3)}
    (M : CanonicalSCM backdoorKind dims backdoorDAG (⊥ : SimpleGraph (Fin 3)) C)
    (j : Fin b) (a a' : Fin (dims j)) : Prop :=
  a ≠ a' ∧ 2 ∈ C j ∧
    (M.latentLaw.map (fun u => (blockProjection j u).ofLp a) =
      ENNReal.ofReal (2/5:ℝ) • Measure.dirac 0 + ENNReal.ofReal (3/5:ℝ) • Measure.dirac 1) ∧
    (M.latentLaw.map (fun u => (blockProjection j u).ofLp a') =
      ENNReal.ofReal (2/3:ℝ) • Measure.dirac 0 + ENNReal.ofReal (1/3:ℝ) • Measure.dirac 1) ∧
    ProbabilityTheory.IndepFun (fun u => (blockProjection j u).ofLp a)
      (fun u => (blockProjection j u).ofLp a') M.latentLaw ∧
    CounterexampleSecondBernoulliReading M j a'

/-- For [a canonical backdoor model without bidirected edges](hyp:M), [a private latent block](hyp:j),
[its first designated coordinate](hyp:a), and [its second designated coordinate](hyp:a'),
[the outcome-connection condition](goal) requires a real-valued latent disturbance that is
[measurable](step:1), [integrable](step:2), and [mean zero](step:3), such that
[almost surely, under either binary intervention, a zero covariate makes the outcome equal
to the first coordinate for treatment category two or the second coordinate otherwise,
plus that disturbance](step:4). -/
def counterexampleOutcomeConnection {b : ℕ} {dims : Fin b → ℕ}
    {C : Fin b → Set (Fin 3)}
    (M : CanonicalSCM backdoorKind dims backdoorDAG (⊥ : SimpleGraph (Fin 3)) C)
    (j : Fin b) (a a' : Fin (dims j)) : Prop :=
  ∃ Uy : Exogenous backdoorKind dims → ℝ,
    Measurable Uy ∧ Integrable Uy M.latentLaw ∧ (∫ u, Uy u ∂M.latentLaw) = 0 ∧
    ∀ᵐ u ∂M.latentLaw, ∀ t : Bool,
      let v := intervenedEval M.toEuclideanSCM (binaryAssignment t) u
      v.ofLp ⟨0, ⟨0, Nat.zero_lt_succ 0⟩⟩ = 0 →
      backdoorOutcome v =
        (if v.ofLp ⟨1, ⟨0, Nat.zero_lt_succ 0⟩⟩ = 2 then
          (blockProjection j u).ofLp a else (blockProjection j u).ofLp a') + Uy u

-- @node: counterexampleComponents
/-- For [a node numbered from zero to two](hyp:j), [its private latent component is the singleton
containing that node](goal). -/
def counterexampleComponents (j : Fin 3) : Set (Fin 3) := {j}

-- @node: counterexampleDims
/-- [The three private latent blocks have dimensions one, zero, and two, respectively,
for the covariate, treatment, and outcome nodes](goal). -/
def counterexampleDims : Fin 3 → ℕ := ![1, 0, 2]

-- @node: counterexampleComponents_component
/-- For any node, [its singleton private component is a maximal bidirected clique
in the graph with no bidirected edges](goal). -/
lemma counterexampleComponents_component (j : Fin 3) :
    IsC2Component (⊥ : SimpleGraph (Fin 3)) (counterexampleComponents j) := by
  constructor
  refine ⟨SimpleGraph.isClique_singleton _, ?_⟩
  intro s hs hsub x hx
  exact (SimpleGraph.isClique_bot_iff.mp hs) hx (hsub (Set.mem_singleton j))

-- @node: counterexampleComponents_exhaustive
/-- If [a set of nodes is a maximal bidirected clique in the graph with no bidirected edges](hyp:hs),
then [it equals the designated singleton component of some node](goal). -/
lemma counterexampleComponents_exhaustive (s : Set (Fin 3))
    (hs : IsC2Component (⊥ : SimpleGraph (Fin 3)) s) :
    ∃ j, counterexampleComponents j = s := by
  have hne : s.Nonempty := by
    by_contra h
    have he : s = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have hm := hs.maximalClique.2 (SimpleGraph.isClique_singleton (0 : Fin 3))
      (by simp [he])
    have := hm (Set.mem_singleton (0 : Fin 3))
    simp [he] at this
  obtain ⟨j, hj⟩ := hne
  refine ⟨j, Set.Subset.antisymm (Set.singleton_subset_iff.mpr hj) ?_⟩
  intro x hx
  exact (SimpleGraph.isClique_bot_iff.mp hs.maximalClique.1) hx hj

-- @node: counterexampleBlockProjection
/-- For [a private block index](hyp:j) and [a three-coordinate latent vector](hyp:z),
[the block projection](goal) returns [the first coordinate for the covariate block](step:1),
[the empty vector for the treatment block](step:2), or
[the second and third coordinates together for the outcome block](step:3). -/
def counterexampleBlockProjection (j : Fin 3) (z : L1Vec 3) :
    L1Vec (counterexampleDims j) :=
  Fin.cases (WithLp.toLp 1 ![z.ofLp 0])
    (Fin.cases 0 (Fin.cases (WithLp.toLp 1 ![z.ofLp 1, z.ofLp 2]) (fun k => k.elim0))) j

-- @node: counterexampleBlockProjection_measurable
/-- For each private block, [the projection from the three-coordinate latent vector
to that block is measurable](goal). -/
@[fun_prop] lemma counterexampleBlockProjection_measurable (j : Fin 3) :
    Measurable (counterexampleBlockProjection j) := by
  fin_cases j
  · change Measurable (fun z : L1Vec 3 => WithLp.toLp 1 ![z.ofLp 0])
    fun_prop
  · change Measurable (fun _ : L1Vec 3 => (0 : L1Vec 0))
    fun_prop
  · change Measurable (fun z : L1Vec 3 => WithLp.toLp 1 ![z.ofLp 1, z.ofLp 2])
    fun_prop

-- @node: counterexampleBlockLaw
/-- For [a private block index](hyp:j), [its probability law is the distribution of that block's
projection under the counterexample's finite latent law](goal). -/
def counterexampleBlockLaw (j : Fin 3) : ProbabilityMeasure (L1Vec (counterexampleDims j)) :=
  letI := counterexampleTrueFiniteLatentLaw_probability
  ⟨counterexampleTrueFiniteLatentLaw.map (counterexampleBlockProjection j),
    Measure.isProbabilityMeasure_map (counterexampleBlockProjection_measurable j).aemeasurable⟩

-- @node: counterexampleTrueFiniteLatentLaw_ae_atoms
/-- [The counterexample's finite latent law assigns probability one to its designated latent atoms](goal). -/
lemma counterexampleTrueFiniteLatentLaw_ae_atoms :
    ∀ᵐ z ∂counterexampleTrueFiniteLatentLaw, z ∈ Set.range counterexampleTrueLatentAtom := by
  rw [counterexampleTrueFiniteLatentLaw, ← Measure.sum_fintype, Measure.ae_sum_iff]
  intro i
  apply Measure.ae_smul_measure
  apply (ae_dirac_iff (Set.finite_range counterexampleTrueLatentAtom).measurableSet).mpr
  exact Set.mem_range_self i

-- @node: counterexampleBlockLaw_regular
/-- For every private block, [its finite probability law satisfies the generator regularity conditions](goal). -/
lemma counterexampleBlockLaw_regular (j : Fin 3) :
    GeneratorRegular (counterexampleBlockLaw j : Measure (L1Vec (counterexampleDims j))) := by
  let := counterexampleTrueFiniteLatentLaw_probability
  apply generatorRegular_of_finite_carrier _
    ((Set.finite_range counterexampleTrueLatentAtom).image (counterexampleBlockProjection j))
  apply (ae_map_iff (counterexampleBlockProjection_measurable j).aemeasurable
    ((Set.finite_range counterexampleTrueLatentAtom).image
      (counterexampleBlockProjection j)).measurableSet).mpr
  have ha := counterexampleTrueFiniteLatentLaw_ae_atoms
  filter_upwards [ha] with z hz
  exact Set.mem_image_of_mem _ hz

-- @node: counterexampleOutcomeInput
/-- From [the outcome equation's structural input](hyp:x), [the ordered four-coordinate outcome
input consists of the covariate, treatment, first private outcome noise, and second private outcome noise](goal). -/
def counterexampleOutcomeInput
    (x : StructuralInput backdoorKind counterexampleDims backdoorDAG
      (canonicalIncidence counterexampleComponents) 2) : L1Vec 4 :=
  WithLp.toLp 1 ![
    x.ofLp (.inl ⟨⟨0, by rw [Causalean.Graph.DAG.mem_parents]; exact (by decide : (0 : Fin 3) < 2)⟩, ⟨0, by decide⟩⟩),
    x.ofLp (.inl ⟨⟨1, by rw [Causalean.Graph.DAG.mem_parents]; exact (by decide : (1 : Fin 3) < 2)⟩, ⟨0, by decide⟩⟩),
    x.ofLp (.inr ⟨⟨2, by simp [canonicalIncidence, counterexampleComponents]⟩, ⟨0, by decide⟩⟩),
    x.ofLp (.inr ⟨⟨2, by simp [canonicalIncidence, counterexampleComponents]⟩, ⟨1, by decide⟩⟩)]

-- @node: counterexampleOutcomeInput_measurable
/-- [Extracting the ordered covariate, treatment, and two private noise coordinates
from the outcome's structural input is measurable](goal). -/
@[fun_prop] lemma counterexampleOutcomeInput_measurable :
    Measurable counterexampleOutcomeInput := by
  unfold counterexampleOutcomeInput
  fun_prop

-- @node: counterexampleStructuralWeights
/-- For [a node numbered from zero to two](hyp:i), [its structural weight map](goal) is
[minus one plus the private covariate noise shifted by one and clipped to the unit interval at node zero](step:1),
[the counterexample's treatment propensity vector evaluated at the parent covariate at node one](step:2), or
[the scalar counterexample outcome function evaluated at the ordered covariate, treatment,
and two private noises at node two](step:3). -/
def counterexampleStructuralWeights (i : Fin 3) :
    StructuralInput backdoorKind counterexampleDims backdoorDAG
      (canonicalIncidence counterexampleComponents) i → L1Vec (outputDim (backdoorKind i)) :=
  Fin.cases (fun x => WithLp.toLp 1 (fun _ =>
      -1 + counterexampleClamp (x.ofLp (.inr
        ⟨⟨0, by simp [canonicalIncidence, counterexampleComponents]⟩, ⟨0, by decide⟩⟩) + 1)))
    (Fin.cases (fun x => counterexampleTruePropensity
      (x.ofLp (.inl ⟨⟨0, by rw [Causalean.Graph.DAG.mem_parents];
                            exact (by decide : (0 : Fin 3) < 1)⟩, ⟨0, by decide⟩⟩)))
      (Fin.cases (fun x => WithLp.toLp 1 (fun _ =>
        counterexampleTrueOutcome (counterexampleOutcomeInput x))) (fun k => k.elim0))) i

-- @node: counterexampleStructuralWeights_measurable
/-- For every node, [the counterexample's structural weight map is measurable](goal). -/
@[fun_prop] lemma counterexampleStructuralWeights_measurable (i : Fin 3) :
    Measurable (counterexampleStructuralWeights i) := by
  fin_cases i
  · change Measurable (fun x : StructuralInput backdoorKind counterexampleDims backdoorDAG
      (canonicalIncidence counterexampleComponents) 0 => WithLp.toLp 1 (fun _ : Fin 1 =>
      -1 + counterexampleClamp (x.ofLp (.inr
        ⟨⟨0, by simp [canonicalIncidence, counterexampleComponents]⟩, ⟨0, by decide⟩⟩) + 1)))
    fun_prop
  · change Measurable (fun x : StructuralInput backdoorKind counterexampleDims backdoorDAG
      (canonicalIncidence counterexampleComponents) 1 => counterexampleTruePropensity
      (x.ofLp (.inl ⟨⟨0, by rw [Causalean.Graph.DAG.mem_parents];
                            exact (by decide : (0 : Fin 3) < 1)⟩, ⟨0, by decide⟩⟩)))
    fun_prop
  · change Measurable (fun x => WithLp.toLp 1 (fun _ : Fin 1 =>
      counterexampleTrueOutcome (counterexampleOutcomeInput x)))
    fun_prop

-- @node: counterexampleTrueSCM
/-- [The counterexample's canonical limiting structural causal model uses the backdoor directed graph,
no bidirected edges, singleton private components of dimensions one, zero, and two,
the specified structural weight maps, and the finite private block laws](goal).

The canonical constructor supplies independent intrinsic Gumbel coordinates. -/
def counterexampleTrueSCM : CanonicalSCM backdoorKind counterexampleDims backdoorDAG
    (⊥ : SimpleGraph (Fin 3)) counterexampleComponents where
  categoricalPositive := by
    intro i k h
    fin_cases i <;> simp [backdoorKind] at h
    omega
  component := counterexampleComponents_component
  exhaustive := counterexampleComponents_exhaustive
  distinct := by
    intro i j h
    exact Set.singleton_injective h
  f := counterexampleStructuralWeights
  structuralMeasurable := counterexampleStructuralWeights_measurable
  blockLaw := counterexampleBlockLaw
  simplex := by
    intro i k h x hx
    fin_cases i <;> simp [backdoorKind] at h
    subst k
    exact counterexampleTruePropensity_simplex _

-- @node: counterexampleTrueSCM_regular
/-- [Every private latent block law of the counterexample's canonical model satisfies
the generator regularity conditions](goal). -/
lemma counterexampleTrueSCM_regular : LatentLawsGeneratorRegular counterexampleTrueSCM := by
  intro j
  exact counterexampleBlockLaw_regular j

-- @node: counterexampleInputCoordinate_lipschitz
/-- For any coordinate of a finite real vector, [extracting that coordinate is Lipschitz
with constant one under the sum-of-absolute-values norm](goal). -/
lemma counterexampleInputCoordinate_lipschitz {I : Type*} [Fintype I] (j : I) :
    LipschitzWith 1 (fun z : WithLp 1 (I → ℝ) => z.ofLp j) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa using PiLp.dist_apply_le x y j

-- @node: counterexampleOutcomeInput_lipschitz
/-- [Extracting the four ordered outcome inputs is Lipschitz with constant four
under the sum-of-absolute-values norms](goal). -/
lemma counterexampleOutcomeInput_lipschitz : LipschitzWith 4 counterexampleOutcomeInput := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h (j : Fin 4) :
      dist ((counterexampleOutcomeInput x).ofLp j) ((counterexampleOutcomeInput y).ofLp j) ≤
        dist x y := by
    fin_cases j <;> exact PiLp.dist_apply_le x y _
  calc
    _ = ∑ j : Fin 4, dist ((counterexampleOutcomeInput x).ofLp j)
        ((counterexampleOutcomeInput y).ofLp j) := PiLp.dist_eq_of_L1 _ _
    _ ≤ ∑ _ : Fin 4, dist x y := Finset.sum_le_sum (fun j _ => h j)
    _ = _ := by norm_num

-- @node: counterexampleStructuralWeights_zero
/-- For any structural input to the covariate node, [the structural weight is the scalar
minus one plus the private covariate noise shifted by one and clipped to the unit interval](goal). -/
lemma counterexampleStructuralWeights_zero
    (x : StructuralInput backdoorKind counterexampleDims backdoorDAG
      (canonicalIncidence counterexampleComponents) 0) :
    counterexampleStructuralWeights 0 x = WithLp.toLp 1 (fun _ : Fin 1 =>
      -1 + counterexampleClamp (x.ofLp (.inr
        ⟨⟨0, by simp [canonicalIncidence, counterexampleComponents]⟩, ⟨0, by decide⟩⟩) + 1)) := rfl

-- @node: counterexampleStructuralWeights_one
/-- For any structural input to the treatment node, [the structural weight vector equals
the counterexample's treatment propensity vector evaluated at the parent covariate](goal). -/
lemma counterexampleStructuralWeights_one
    (x : StructuralInput backdoorKind counterexampleDims backdoorDAG
      (canonicalIncidence counterexampleComponents) 1) :
    counterexampleStructuralWeights 1 x = counterexampleTruePropensity
      (x.ofLp (.inl ⟨⟨0, by rw [Causalean.Graph.DAG.mem_parents];
                            exact (by decide : (0 : Fin 3) < 1)⟩, ⟨0, by decide⟩⟩)) := rfl

-- @node: counterexampleStructuralWeights_two
/-- For any structural input to the outcome node, [the structural weight is the scalar
counterexample outcome function evaluated at the ordered covariate, treatment, and two private noises](goal). -/
lemma counterexampleStructuralWeights_two
    (x : StructuralInput backdoorKind counterexampleDims backdoorDAG
      (canonicalIncidence counterexampleComponents) 2) :
    counterexampleStructuralWeights 2 x = WithLp.toLp 1 (fun _ : Fin 1 =>
      counterexampleTrueOutcome (counterexampleOutcomeInput x)) := rfl

-- @node: counterexampleStructuralWeights_lipschitz
/-- For every node, [the counterexample's structural weight map is globally Lipschitz
with constant twenty under the sum-of-absolute-values norms](goal). -/
lemma counterexampleStructuralWeights_lipschitz (i : Fin 3) :
    LipschitzWith 20 (counterexampleStructuralWeights i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  fin_cases i
  · change dist (α := L1Vec 1) (counterexampleStructuralWeights 0 x)
      (counterexampleStructuralWeights 0 y) ≤ (20 : ℝ) * dist x y
    rw [counterexampleStructuralWeights_zero, counterexampleStructuralWeights_zero,
      PiLp.dist_eq_of_L1, Fin.sum_univ_one]
    have h := counterexampleClamp_lipschitz.dist_le_mul
      (x.ofLp (.inr ⟨⟨0, by simp [canonicalIncidence, counterexampleComponents]⟩,
        ⟨0, by decide⟩⟩) + 1)
      (y.ofLp (.inr ⟨⟨0, by simp [canonicalIncidence, counterexampleComponents]⟩,
        ⟨0, by decide⟩⟩) + 1)
    have hp := PiLp.dist_apply_le x y (.inr
      ⟨⟨0, by simp [canonicalIncidence, counterexampleComponents]⟩, ⟨0, by decide⟩⟩)
    simp only [WithLp.ofLp_toLp, Real.dist_eq, NNReal.coe_one, one_mul,
      add_sub_add_right_eq_sub] at h hp ⊢
    norm_num
    calc
      _ = |counterexampleClamp (x.ofLp (.inr ⟨⟨0, by simp [canonicalIncidence,
          counterexampleComponents]⟩, ⟨0, by decide⟩⟩) + 1) -
          counterexampleClamp (y.ofLp (.inr ⟨⟨0, by simp [canonicalIncidence,
          counterexampleComponents]⟩, ⟨0, by decide⟩⟩) + 1)| := by congr 1
      _ ≤ dist x y := h.trans hp
      _ ≤ 20 * dist x y := by nlinarith [(dist_nonneg : 0 ≤ dist x y)]
  · change dist (α := L1Vec 2) (counterexampleStructuralWeights 1 x)
      (counterexampleStructuralWeights 1 y) ≤ (20 : ℝ) * dist x y
    rw [counterexampleStructuralWeights_one, counterexampleStructuralWeights_one]
    have h := counterexampleTruePropensity_lipschitz.dist_le_mul
      (x.ofLp (.inl ⟨⟨0, by exact backdoorDAG.mem_parents.mpr (by decide : (0 : Fin 3) < 1)⟩, ⟨0, by decide⟩⟩))
      (y.ofLp (.inl ⟨⟨0, by exact backdoorDAG.mem_parents.mpr (by decide : (0 : Fin 3) < 1)⟩, ⟨0, by decide⟩⟩))
    have hp := PiLp.dist_apply_le x y (.inl
      ⟨⟨0, by exact backdoorDAG.mem_parents.mpr (by decide : (0 : Fin 3) < 1)⟩, ⟨0, by decide⟩⟩)
    norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] at h ⊢
    calc
      _ ≤ (1/4 : ℝ) * dist x y :=
        h.trans (mul_le_mul_of_nonneg_left hp (by norm_num))
      _ ≤ 20 * dist x y := by nlinarith [(dist_nonneg : 0 ≤ dist x y)]
  · change dist (α := L1Vec 1) (counterexampleStructuralWeights 2 x)
      (counterexampleStructuralWeights 2 y) ≤ (20 : ℝ) * dist x y
    rw [counterexampleStructuralWeights_two, counterexampleStructuralWeights_two,
      PiLp.dist_eq_of_L1, Fin.sum_univ_one]
    have h := counterexampleTrueOutcome_lipschitz.comp counterexampleOutcomeInput_lipschitz
    convert h.dist_le_mul x y using 1 <;> norm_num [Function.comp_def]

-- @node: counterexampleTrueSCM_independent
/-- [The named private latent blocks and categorical noise blocks of the counterexample's
canonical model are mutually independent](goal). -/
lemma counterexampleTrueSCM_independent :
    LatentBlocksIndependent counterexampleTrueSCM.toEuclideanSCM :=
  canonical_latent_blocks_independent counterexampleTrueSCM

-- @node: counterexampleTrueSCM_gumbel_decomposition
/-- [The named latent coordinates of the counterexample's canonical model partition
into private block coordinates and categorical Gumbel noise coordinates](goal). -/
lemma counterexampleTrueSCM_gumbel_decomposition :
    LatentGumbelDecomposition counterexampleTrueSCM.toEuclideanSCM := by
  constructor
  · ext j
    cases j <;> simp
  · apply Set.disjoint_left.mpr
    rintro x ⟨a, rfl⟩ ⟨b, h⟩
    cases h

-- @node: counterexampleTrueSCM_block_law
/-- For every private block, [its marginal distribution under the counterexample's
canonical latent law equals its prescribed finite block law](goal). -/
lemma counterexampleTrueSCM_block_law (j : Fin 3) :
    counterexampleTrueSCM.latentLaw.map (blockProjection j) =
      (counterexampleBlockLaw j : Measure (L1Vec (counterexampleDims j))) := by
  let M := counterexampleTrueSCM
  let := fun i => canonicalNamedLatentLaw_probability M i
  have hm : Measurable (blockProjection (kind := backdoorKind) (dims := counterexampleDims) j) := by
    fun_prop [blockProjection]
  rw [canonical_latentLaw_eq_named_product M,
    Measure.map_map hm restoreNamedLatents_measurable]
  change (Measure.pi (canonicalNamedLatentLaw M)).map (fun z => z (.inl j)) = _
  exact (measurePreserving_eval (canonicalNamedLatentLaw M) (.inl j)).map_eq

-- @node: counterexampleTrueSCM_continuous_lipschitz
/-- [All continuous structural mechanisms of the counterexample's canonical model
are Lipschitz with common constant twenty on their admissible domains,
under the sum-of-absolute-values norms](goal). -/
lemma counterexampleTrueSCM_continuous_lipschitz :
    ContinuousMechanismsLipschitz counterexampleTrueSCM.toEuclideanSCM 20 := by
  intro i d hi
  fin_cases i <;> simp [backdoorKind] at hi
  · subst d
    exact (counterexampleStructuralWeights_lipschitz 0).lipschitzOnWith
  · subst d
    exact (counterexampleStructuralWeights_lipschitz 2).lipschitzOnWith

-- @node: counterexampleTrueSCM_propensity_lipschitz
/-- [For every categorical node of the counterexample's canonical model, its structural
weight map is Lipschitz with constant twenty on its admissible domain under the
sum-of-absolute-values norms](goal). -/
lemma counterexampleTrueSCM_propensity_lipschitz :
    ∀ i k, backdoorKind i = Sum.inr k →
      LipschitzOnWith 20 (counterexampleTrueSCM.f i)
        (counterexampleTrueSCM.toEuclideanSCM.domain i) := by
  intro i k hi
  exact (counterexampleStructuralWeights_lipschitz i).lipschitzOnWith

-- @node: counterexampleTrueSCM_weights_positive
/-- [At every admissible input to each categorical node of the counterexample's canonical
model, all category weights are nonnegative and their sum is strictly positive](goal).

Positivity here is positivity of the total weight, with no strengthening
to an open-simplex premise. -/
lemma counterexampleTrueSCM_weights_positive :
    CategoricalWeightsPositive counterexampleTrueSCM.toEuclideanSCM counterexampleTrueSCM.f := by
  intro i k hi
  fin_cases i <;> simp [backdoorKind] at hi
  subst k
  intro x hx
  have hs := counterexampleTrueSCM.simplex 1 2 rfl x hx.1
  change (counterexampleTrueSCM.f 1 x).ofLp ∈ stdSimplex ℝ (Fin 2) at hs
  refine ⟨hs.1, ?_⟩
  change 0 < ∑ j : Fin 2, (counterexampleTrueSCM.f 1 x).ofLp j
  rw [hs.2]
  exact zero_lt_one

-- @node: counterexampleTrueSCM_latent_bounded
/-- [Under the counterexample's canonical latent law, every coordinate of every private
latent block has absolute value at most one, almost surely](goal).

No assertion is made about the separate Gumbel coordinates. -/
lemma counterexampleTrueSCM_latent_bounded :
    ∀ᵐ u ∂counterexampleTrueSCM.latentLaw, ∀ j k, |(blockProjection j u).ofLp k| ≤ 1 := by
  have hset (d : ℕ) : MeasurableSet {x : L1Vec d | ∀ k, |x.ofLp k| ≤ 1} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter (fun k => measurableSet_le (by fun_prop) measurable_const)
  have hblock (j : Fin 3) :
      ∀ᵐ x ∂(counterexampleBlockLaw j : Measure (L1Vec (counterexampleDims j))),
        ∀ k, |x.ofLp k| ≤ 1 := by
    apply (ae_map_iff (counterexampleBlockProjection_measurable j).aemeasurable
      (hset (counterexampleDims j))).mpr
    filter_upwards [counterexampleTrueFiniteLatentLaw_ae_atoms] with z hz
    obtain ⟨⟨x,a,b⟩, rfl⟩ := hz
    fin_cases j
    · intro k
      fin_cases k
      change |-1 + (x.val : ℝ)| ≤ 1
      fin_cases x <;> norm_num
    · intro k
      exact Fin.elim0 k
    · intro k
      fin_cases k
      · change |(a.val : ℝ)| ≤ 1
        rw [abs_of_nonneg (Nat.cast_nonneg _)]
        exact_mod_cast Nat.le_of_lt_succ a.isLt
      · change |(b.val : ℝ)| ≤ 1
        rw [abs_of_nonneg (Nat.cast_nonneg _)]
        exact_mod_cast Nat.le_of_lt_succ b.isLt
  apply ae_all_iff.mpr
  intro j
  have hm : Measurable (blockProjection (kind := backdoorKind) (dims := counterexampleDims) j) := by
    fun_prop [blockProjection]
  apply (ae_map_iff hm.aemeasurable (hset (counterexampleDims j))).mp
  rw [counterexampleTrueSCM_block_law]
  exact hblock j

-- @node: counterexampleTrueSCM_variables_bounded
/-- [There exists a positive deterministic bound that, almost surely under the
counterexample's canonical latent law, bounds the absolute values of all observed
coordinates without intervention and all private latent block coordinates](goal). -/
lemma counterexampleTrueSCM_variables_bounded :
    ∃ K : ℝ, VariablesBoundedAt counterexampleTrueSCM.toEuclideanSCM K := by
  obtain ⟨R, hR, hv⟩ := evalSteps_bounded_of_nonGumbel_bounded
    counterexampleTrueSCM.toEuclideanSCM 20 counterexampleTrueSCM_continuous_lipschitz
    (fun _ => none) (noIntervention_admissible backdoorKind) 1 (3*3+3)
  refine ⟨max 1 R, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  filter_upwards [counterexampleTrueSCM_latent_bounded] with u hu
  constructor
  · intro i j
    exact (hv u hu i j).trans (le_max_right _ _)
  · intro j k
    exact (hu j k).trans (le_max_left _ _)

end
end Papers.TbsNeuralCausalPi
