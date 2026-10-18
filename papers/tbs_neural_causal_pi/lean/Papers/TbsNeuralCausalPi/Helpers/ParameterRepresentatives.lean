module
public import Papers.TbsNeuralCausalPi.Helpers.EstimationCandidateBounds
public import Papers.TbsNeuralCausalPi.Helpers.StructuralScalarExtension
public import Papers.TbsNeuralCausalPi.Helpers.StructuralCanonicalExtension
/-! # Cube representatives of neural candidates

The latent cube laws are obtained by restricting the clipped generator laws.
For structural domains containing the input cube, restriction also supplies
the structural parameter, without choosing any off-domain extension.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped NNReal ENNReal
set_option backward.isDefEq.respectTransparency false

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)} {K L : ℝ≥0}

-- @node: toParam_marginal_map_eq
/-- If [the structural functions restricted to the input cubes belong to the
chosen structural classes](hyp:hF), [categorical outputs on those cubes lie
in their probability simplexes](hyp:hs), and [each latent block law assigns
full mass to its bounded cube](hyp:hK), [mapping any block law of the resulting
cube parameter into the ambient space recovers the original block law](goal). -/
lemma toParam_marginal_map_eq
    (M : CanonicalSCM kind dims dag G C)
    (F : CubeStructuralClass kind dims dag C K)
    (hF : ∀ i, (fun x : inputCube K i => M.f i x.val) ∈ F i)
    (hs : ∀ i k (h : kind i = Sum.inr k) (x : inputCube K i),
      (fun j : Fin k => (M.f i x.val).ofLp
        (Fin.cast (congrArg outputDim h).symm j)) ∈ probabilitySimplex k)
    (hK : ∀ j, (M.blockLaw j : Measure _) (boundedCube (dims j) K) = 1)
    (j : Fin b) :
    ((toParam M K F hF hs hK).2 j : Measure (boundedCube (dims j) K)).map
      Subtype.val = (M.blockLaw j : Measure _) := by
  exact (Toolkit.Foundations.MeasureTheory.probability_comap_subtype
    (M.blockLaw j : Measure _) (boundedCube (dims j) K)
    (boundedCube_isCompact _ _).measurableSet (hK j)).2

-- @node: populationRepresentation_exists_of_cube_conditions
/-- If [the candidate's structural functions on the input cubes belong to the
population classes with bounds K and L](hyp:hF), [its categorical outputs on
those cubes lie in their probability simplexes](hyp:hs), and [each latent block
law assigns full mass to its bounded cube](hyp:hK), [there exists a population
parameter representing the candidate](goal). -/
lemma populationRepresentation_exists_of_cube_conditions
    {counts : Fin b → ℕ} {F0 : StructuralClass kind dims dag C}
    {F1 : GeneratorClass dims counts}
    (R : NCMIn kind dims dag G C counts F0 F1)
    (hF : ∀ i, (fun x : inputCube K i => R.canonical.f i x.val) ∈
      cubePopulationClass K L i)
    (hs : ∀ i k (h : kind i = Sum.inr k) (x : inputCube K i),
      (fun j : Fin k => (R.canonical.f i x.val).ofLp
        (Fin.cast (congrArg outputDim h).symm j)) ∈ probabilitySimplex k)
    (hK : ∀ j, (R.canonical.blockLaw j : Measure _) (boundedCube (dims j) K) = 1) :
    ∃ p : PopulationParam kind dims dag C K L, populationRepresentation p R := by
  refine ⟨⟨toParam R.canonical K (cubePopulationClass K L) hF hs hK⟩, ?_, ?_⟩
  · intro i x _
    rfl
  · intro j
    exact (toParam_marginal_map_eq R.canonical _ hF hs hK j).symm

-- @node: restrictedCandidate_populationRepresentation_of_latent_support
/-- If [a neural candidate satisfies the structural restrictions with bounds
K and L](hyp:hR) and [every latent block law assigns full mass to its bounded
cube](hyp:hK), [there exists a population parameter representing the
candidate](goal).

The structural functions can be extended with the same Lipschitz constant
and convex output ranges before restriction to the cubes; agreement is
required only at actual inputs. -/
lemma restrictedCandidate_populationRepresentation_of_latent_support
    {counts : Fin b → ℕ} {F0 : StructuralClass kind dims dag C}
    {F1 : GeneratorClass dims counts}
    (R : NCMIn kind dims dag G C counts F0 F1)
    (hR : restrictedCandidate K L R)
    (hK : ∀ j, (R.canonical.blockLaw j : Measure _) (boundedCube (dims j) K) = 1) :
    ∃ p : PopulationParam kind dims dag C K L, populationRepresentation p R := by
  classical
  have hext (i : Fin n) :
      ∃ g : Input kind dims dag C i → L1Vec (outputDim (kind i)),
        LipschitzWith L g ∧
        ((kind i).isLeft = true → ∀ x, ‖g x‖ ≤ K) ∧
        ((kind i).isRight = true → ∀ x,
          (g x).ofLp ∈ probabilitySimplex (outputDim (kind i))) ∧
        Set.EqOn g (R.canonical.f i) (R.canonical.domain i none) := by
    have hkind : (∃ d, kind i = Sum.inl d) ∨ ∃ k, kind i = Sum.inr k := by
      cases hi : kind i with
      | inl d => exact Or.inl ⟨d, rfl⟩
      | inr k => exact Or.inr ⟨k, rfl⟩
    rcases hkind with ⟨d, hi⟩ | ⟨k, hi⟩
    · obtain ⟨g, hg, hb, heq⟩ := canonical_bounded_vector_structural_extension
        R.canonical i L K (hR i).1
        (restrictedCandidate_continuous_output_bound K L R hR i d hi)
      exact ⟨g, hg, fun _ => hb, by simp [hi], heq⟩
    · obtain ⟨g, hg, hs, heq⟩ := canonical_simplex_structural_extension
        R.canonical i k hi L (hR i).1
      exact ⟨g, hg, by simp [hi], fun _ => hs, heq⟩
  choose f hf hb hs heq using hext
  have hsimplex (i : Fin n) (k : ℕ) (hi : kind i = Sum.inr k)
      (x : Input kind dims dag C i) :
      (fun j : Fin k => (f i x).ofLp
        (Fin.cast (congrArg outputDim hi).symm j)) ∈ probabilitySimplex k := by
    have h := hs i (by simp [hi]) x
    refine ⟨fun j => h.1 _, ?_⟩
    exact (Equiv.sum_comp (finCongr (congrArg outputDim hi).symm) _).trans h.2
  let N : CanonicalSCM kind dims dag G C :=
    { R.canonical with
      f := f
      structuralMeasurable := by
        intro i
        first | fun_prop | exact (hf i).continuous.measurable
      simplex := fun i k hi x _ => hsimplex i k hi x }
  have hF : ∀ i, (fun x : inputCube K i => N.f i x.val) ∈
      cubePopulationClass K L i := by
    intro i
    constructor
    · intro x y
      exact hf i x.val y.val
    · intro d hi x
      exact hb i (by simp [hi]) x.val
  have hNs : ∀ i k (hi : kind i = Sum.inr k) (x : inputCube K i),
      (fun j : Fin k => (N.f i x.val).ofLp
        (Fin.cast (congrArg outputDim hi).symm j)) ∈ probabilitySimplex k :=
    fun i k hi x => hsimplex i k hi x.val
  refine ⟨⟨toParam N K (cubePopulationClass K L) hF hNs hK⟩, ?_, ?_⟩
  · intro i x hx
    exact (heq i hx).symm
  · intro j
    exact (toParam_marginal_map_eq N _ hF hNs hK j).symm

-- @node: restrictedCandidate_cube_conditions_of_domain
/-- If [a neural candidate satisfies the structural restrictions with bounds
K and L](hyp:hR) and [each input cube is contained in its actual structural
domain](hyp:hdom), [its structural functions restricted to the cubes belong
to the population classes, and its categorical outputs there lie in their
probability simplexes](goal). -/
lemma restrictedCandidate_cube_conditions_of_domain
    {counts : Fin b → ℕ} {F0 : StructuralClass kind dims dag C}
    {F1 : GeneratorClass dims counts}
    (R : NCMIn kind dims dag G C counts F0 F1)
    (hR : restrictedCandidate K L R)
    (hdom : ∀ i, inputCube (kind := kind) (dims := dims) (dag := dag) (C := C) K i ⊆
      R.canonical.domain i) :
    (∀ i, (fun x : inputCube K i => R.canonical.f i x.val) ∈
      cubePopulationClass K L i) ∧
    (∀ i k (h : kind i = Sum.inr k) (x : inputCube K i),
      (fun j : Fin k => (R.canonical.f i x.val).ofLp
        (Fin.cast (congrArg outputDim h).symm j)) ∈ probabilitySimplex k) := by
  constructor
  · intro i
    constructor
    · intro x y
      exact (hR i).1 (hdom i x.property) (hdom i y.property)
    · intro d hd x
      exact restrictedCandidate_continuous_output_bound K L R hR i d hd x.val
        (hdom i x.property)
  · intro i k hi x
    exact R.canonical.simplex i k hi x.val (hdom i x.property).1

-- @node: restrictedCandidate_populationRepresentation_of_continuous_parents
/-- For [a choice of input dimensions for the latent generator networks](hyp:dC),
if [the neural candidate satisfies the structural restrictions with bounds
K and L](hyp:hR) and [every parent of every node is continuous](hyp:hparents),
[there exists a population parameter representing the candidate](goal).

Categorical terminal nodes are allowed. -/
lemma restrictedCandidate_populationRepresentation_of_continuous_parents
    {counts : Fin b → ℕ} {F0 : StructuralClass kind dims dag C}
    (dC : ∀ j, Fin (counts j) → ℕ) (D c1 c2 : ℕ)
    (L1 L2 : ℕ → ℕ) (tau : ℕ → ℝ) (r : ℕ)
    (R : NCMIn kind dims dag G C counts F0
      (generatorClassN counts dC K D c1 c2 L1 L2 tau r))
    (hR : restrictedCandidate K L R)
    (hparents : ∀ i p, p ∈ dag.parents i → (kind p).isLeft = true) :
    ∃ p : PopulationParam kind dims dag C K L, populationRepresentation p R := by
  have hdom : ∀ i, inputCube (kind := kind) (dims := dims) (dag := dag) (C := C) K i ⊆
      R.canonical.domain i := by
    intro i
    rw [canonical_domain_eq_univ_of_continuous_parents R.canonical i (hparents i)]
    exact Set.subset_univ _
  obtain ⟨hF, hs⟩ := restrictedCandidate_cube_conditions_of_domain R hR hdom
  exact populationRepresentation_exists_of_cube_conditions R hF hs
    (ncm_generatorClassN_blockLaw_box dC K D c1 c2 L1 L2 tau r R)

end Papers.TbsNeuralCausalPi
