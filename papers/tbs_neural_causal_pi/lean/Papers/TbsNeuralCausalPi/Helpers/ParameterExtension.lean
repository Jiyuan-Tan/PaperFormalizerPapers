module
public import Papers.TbsNeuralCausalPi.Helpers.ParameterConvergence
public import Papers.TbsNeuralCausalPi.Helpers.BoundedPopulationTransport
/-! # Lipschitz representatives of compact population parameters

Clipping structural inputs extends each cube map with its original Lipschitz
constant and output constraints. The extension agrees with the existing
parameter model on all inputs used by bounded interventions.
-/
public section
namespace Papers.TbsNeuralCausalPi
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped NNReal ENNReal Topology

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)} {K L : ℝ≥0}

-- @node: structuralBoxProjection_mem_inputCube
/-- For [a nonnegative cube radius K](hyp:K), [clipping a structural input coordinatewise to the bounding interval places
it in the node's input cube](goal). -/
lemma structuralBoxProjection_mem_inputCube
    (M : CanonicalSCM kind dims dag G C) (K : ℝ≥0) (i : Fin n)
    (x : Input kind dims dag C i) :
    structuralBoxProjection M K i x ∈ inputCube K i := by
  intro j
  change |max (-(K : ℝ)) (min (x.ofLp j) K)| ≤ K
  exact abs_le.mpr ⟨le_max_left _ _,
    max_le (by linarith [K.coe_nonneg]) (min_le_right _ _)⟩

-- @node: boxTruncated_ofParam_apply
/-- If [every categorical node's number of categories is at most the bounding
radius](hyp:hlabels), [the clipped population mechanism at any input equals the
original cube mechanism evaluated at the coordinatewise clipped input](goal). -/
lemma boxTruncated_ofParam_apply
    (base : CanonicalSCM kind dims dag G C)
    (p : PopulationParam kind dims dag C K L)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ K)
    (i : Fin n) (x : Input kind dims dag C i) :
    (boxTruncatedSCM (ofParam base p.parameter) K hlabels).f i x =
      p.parameter.1.val i ⟨structuralBoxProjection (ofParam base p.parameter) K i x,
        structuralBoxProjection_mem_inputCube _ K i x⟩ := by
  change paramFunction p.parameter i (structuralBoxProjection _ K i x) = _
  rw [paramFunction, dif_pos (structuralBoxProjection_mem_inputCube _ K i x)]

-- @node: boxTruncated_ofParam_lipschitz
/-- If [every categorical node's number of categories is at most the bounding
radius](hyp:hlabels), [each clipped population structural mechanism is globally
Lipschitz with the population Lipschitz bound](goal). -/
lemma boxTruncated_ofParam_lipschitz
    (base : CanonicalSCM kind dims dag G C)
    (p : PopulationParam kind dims dag C K L)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ K) (i : Fin n) :
    LipschitzWith L ((boxTruncatedSCM (ofParam base p.parameter) K hlabels).f i) := by
  have hp := (p.parameter.1.property.1 i).1
  have hc := (structuralBoxProjection_lipschitz (ofParam base p.parameter) K i).subtype_mk
    (structuralBoxProjection_mem_inputCube _ K i)
  have h := hp.comp hc
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [boxTruncated_ofParam_apply base p hlabels i x,
    boxTruncated_ofParam_apply base p hlabels i y]
  simpa only [NNReal.coe_mul, NNReal.coe_one, mul_one, Function.comp_def] using h.dist_le_mul x y

-- @node: ofParam_continuous_output_bound
/-- [At every continuous node and every structural input, the population
model's mechanism has output one-norm at most the bounding radius](goal). -/
lemma ofParam_continuous_output_bound
    (base : CanonicalSCM kind dims dag G C)
    (p : PopulationParam kind dims dag C K L) :
    ∀ i d, kind i = Sum.inl d → ∀ x, ‖(ofParam base p.parameter).f i x‖ ≤ K := by
  intro i d hi x
  change ‖paramFunction p.parameter i x‖ ≤ K
  classical
  by_cases hx : x ∈ inputCube K i
  · simp only [paramFunction, dif_pos hx]
    exact (p.parameter.1.property.1 i).2 d hi ⟨x, hx⟩
  · simp only [paramFunction, dif_neg hx, hi, Sum.isRight_inl, Bool.false_eq_true,
      ↓reduceIte]
    change ‖(0 : L1Vec (outputDim (kind i)))‖ ≤ K
    simpa using K.coe_nonneg

-- @node: boxTruncated_ofParam_continuous_output_bound
/-- If [every categorical node's number of categories is at most the bounding
radius](hyp:hlabels), [the clipped population mechanism at every continuous node
has output one-norm at most that radius for every input](goal). -/
lemma boxTruncated_ofParam_continuous_output_bound
    (base : CanonicalSCM kind dims dag G C)
    (p : PopulationParam kind dims dag C K L)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ K) :
    ∀ i d, kind i = Sum.inl d → ∀ x,
      ‖(boxTruncatedSCM (ofParam base p.parameter) K hlabels).f i x‖ ≤ K := by
  intro i d hi x
  rw [boxTruncated_ofParam_apply base p hlabels i x]
  exact (p.parameter.1.property.1 i).2 d hi _

-- @node: ofParam_variablesBoundedAt
/-- If [the bounding radius is positive](hyp:hK) and [every categorical node's
number of categories is at most that radius](hyp:hlabels), [the population model's
observed coordinates and non-Gumbel latent block coordinates are almost surely
bounded in absolute value by that radius](goal). -/
lemma ofParam_variablesBoundedAt
    (base : CanonicalSCM kind dims dag G C)
    (p : PopulationParam kind dims dag C K L) (hK : 0 < K)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ K) :
    VariablesBoundedAt (ofParam base p.parameter).toEuclideanSCM K := by
  refine ⟨by exact_mod_cast hK, ?_⟩
  filter_upwards [ofParam_latent_coordinates_bounded base p.parameter] with u hu
  refine ⟨?_, hu⟩
  intro i j
  exact ofParam_evalSteps_coordinate_bounded base p.parameter
    (noIntervention kind).val u hlabels (by simp [noIntervention]) (n * n + n) i j

-- @node: boxTruncated_ofParam_interventionalLaw_eq
/-- If [the bounding radius is positive](hyp:hK), [every categorical node's
number of categories is at most that radius](hyp:hlabels), and [the intervention's
assigned coordinates are bounded in absolute value by that radius](hyp:ht),
[clipping the population model leaves its intervention law unchanged](goal). -/
lemma boxTruncated_ofParam_interventionalLaw_eq
    (base : CanonicalSCM kind dims dag G C)
    (p : PopulationParam kind dims dag C K L) (hK : 0 < K)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ K)
    (t : LawIntervention kind)
    (ht : ∀ i v, t.val i = some v → ∀ j, |v.ofLp j| ≤ K) :
    interventionalLaw (boxTruncatedSCM (ofParam base p.parameter) K hlabels).toEuclideanSCM t =
      interventionalLaw (ofParam base p.parameter).toEuclideanSCM t := by
  exact boxTruncatedSCM_interventionalLaw_eq_of_output_bound _ K hlabels
    (fun i d hi x _ => ofParam_continuous_output_bound base p i d hi x)
    (ofParam_variablesBoundedAt base p hK hlabels) t ht

/-- If [every categorical node's number of categories is at most the bounding
radius](hyp:hlabels), [the clipped population model belongs to the canonical
class whose mechanisms satisfy the population Lipschitz bound and have output
one-norm at most the bounding radius](goal). -/
-- @node: boxTruncated_ofParam_mem_boundedLipClass
lemma boxTruncated_ofParam_mem_boundedLipClass
    (base : CanonicalSCM kind dims dag G C)
    (p : PopulationParam kind dims dag C K L)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ K) :
    boxTruncatedSCM (ofParam base p.parameter) K hlabels ∈
      canonicalClass (boundedLipClass K L) := by
  intro i
  constructor
  · intro x hx y hy
    exact (boxTruncated_ofParam_lipschitz base p hlabels i).edist_le_mul x y
  · intro x hx
    change ‖(boxTruncatedSCM (ofParam base p.parameter) K hlabels).f i x‖ ≤ K
    rw [boxTruncated_ofParam_apply base p hlabels i x]
    let z : inputCube K i := ⟨structuralBoxProjection (ofParam base p.parameter) K i x,
      structuralBoxProjection_mem_inputCube _ K i x⟩
    change ‖p.parameter.1.val i z‖ ≤ K
    have hcases : (∃ d, kind i = Sum.inl d) ∨ (∃ k, kind i = Sum.inr k) := by
      cases kind i with
      | inl d => exact Or.inl ⟨d, rfl⟩
      | inr k => exact Or.inr ⟨k, rfl⟩
    rcases hcases with ⟨d, h⟩ | ⟨k, h⟩
    · exact (p.parameter.1.property.1 i).2 d h z
    · have hs := p.parameter.1.property.2.1 i k h z
      have hnorm : ‖p.parameter.1.val i z‖ = 1 := by
        rw [PiLp.norm_eq_of_L1]
        calc
          _ = ∑ j : Fin k, ‖(p.parameter.1.val i z).ofLp
              (Fin.cast (congrArg outputDim h).symm j)‖ :=
            (Equiv.sum_comp (finCongr (congrArg outputDim h).symm) _).symm
          _ = ∑ j : Fin k, (p.parameter.1.val i z).ofLp
              (Fin.cast (congrArg outputDim h).symm j) :=
            Finset.sum_congr rfl (fun j _ => Real.norm_of_nonneg (hs.1 j))
          _ = 1 := hs.2
      rw [hnorm]
      exact (by exact_mod_cast base.categoricalPositive i k h : (1 : ℝ) ≤ k).trans
        (hlabels i k h)

-- @node: ofParam_blockLaw_cube
/-- [Each latent block distribution of the population model assigns probability
one to its bounded cube](goal). -/
lemma ofParam_blockLaw_cube
    (base : CanonicalSCM kind dims dag G C)
    (p : PopulationParam kind dims dag C K L) (j : Fin b) :
    ((ofParam base p.parameter).blockLaw j : Measure (L1Vec (dims j)))
      (boundedCube (dims j) K) = 1 := by
  change (p.parameter.2 j : Measure (boundedCube (dims j) K)).map Subtype.val
    (boundedCube (dims j) K) = 1
  rw [Measure.map_apply (by fun_prop) (boundedCube_isCompact _ _).measurableSet]
  have he : Subtype.val ⁻¹' boundedCube (dims j) K =
      (Set.univ : Set (boundedCube (dims j) K)) := by
    ext x
    exact iff_of_true x.property (Set.mem_univ _)
  rw [he, measure_univ]

/-- If [every categorical node's number of categories is at most the bounding
radius](hyp:hlabels), [the intervention domain has full probability and bounds
both category counts and assigned intervention coordinates by that radius](hyp:hdomain),
and [the original population model has a defined iterated objective](hyp:hp) and
[the clipped population model has a defined iterated objective](hyp:hext),
[their intervention-averaged objectives are equal](goal). -/
-- @node: boxTruncated_ofParam_objectiveIntegral_eq
lemma boxTruncated_ofParam_objectiveIntegral_eq
    (base : CanonicalSCM kind dims dag G C)
    (p : PopulationParam kind dims dag C K L)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ K)
    {I : Type*} [MeasurableSpace I] (t : I → LawIntervention kind)
    (muT : Measure I) [IsProbabilityMeasure muT] (F : Joint kind → ℝ)
    (domain : Set I) (hdomain : populationObjectiveDomain K domain t muT)
    (hp : objectiveDefined (ofParam base p.parameter).toEuclideanSCM t muT F)
    (hext : objectiveDefined
      (boxTruncatedSCM (ofParam base p.parameter) K hlabels).toEuclideanSCM t muT F) :
    objectiveIntegral (boxTruncatedSCM (ofParam base p.parameter) K hlabels).toEuclideanSCM
      t muT F = objectiveIntegral (ofParam base p.parameter).toEuclideanSCM t muT F := by
  have h := consistencyObjective_eq_of_cube_agreement base
    (boxTruncatedSCM (ofParam base p.parameter) K hlabels) p t muT F domain hdomain
    (fun i x _ => by
      change paramFunction p.parameter i
        (structuralBoxProjection (ofParam base p.parameter) K i x.val) = _
      rw [structuralBoxProjection_eq_self _ K i x.val x.property]
      exact dif_pos x.property)
    (fun _ => rfl) hext hp
  exact h

/-- Suppose [the bounding radius is positive](hyp:hK), [every categorical node's
number of categories is at most that radius](hyp:hlabels), and [the intervention
domain has full probability and bounds both category counts and assigned
intervention coordinates by that radius](hyp:hdomain). If [every feasible bounded
Lipschitz population model has a defined objective](hyp:hdefined), [this parameter
model has a defined objective](hyp:hp), and [its observational law has zero
Wasserstein distance from the base law](hyp:hW), [the population lower bound is
at most this parameter model's intervention-averaged objective](goal). -/
-- @node: populationLowerBound_le_cube_objective
lemma populationLowerBound_le_cube_objective
    (base : CanonicalSCM kind dims dag G C)
    (p : PopulationParam kind dims dag C K L) (hK : 0 < K)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ K)
    {I : Type*} [MeasurableSpace I] (t : I → LawIntervention kind)
    (muT : Measure I) [IsProbabilityMeasure muT] (F : Joint kind → ℝ)
    (domain : Set I) (hdomain : populationObjectiveDomain K domain t muT)
    (hdefined : populationObjectivesDefined base K L t muT F)
    (hp : objectiveDefined (ofParam base p.parameter).toEuclideanSCM t muT F)
    (hW : wasserstein1 (observationalLaw (ofParam base p.parameter).toEuclideanSCM)
      (observationalLaw base.toEuclideanSCM) = 0) :
    populationLowerBound base K L t muT F hdefined ≤
      (objectiveIntegral (ofParam base p.parameter).toEuclideanSCM t muT F : EReal) := by
  let N := boxTruncatedSCM (ofParam base p.parameter) K hlabels
  have hN := boxTruncated_ofParam_mem_boundedLipClass base p hlabels
  have hU : ∀ j, (N.blockLaw j : Measure (L1Vec (dims j))) (boundedCube (dims j) K) = 1 :=
    ofParam_blockLaw_cube base p
  have hNW : wasserstein1 (observationalLaw N.toEuclideanSCM)
      (observationalLaw base.toEuclideanSCM) = 0 := by
    rw [show observationalLaw N.toEuclideanSCM =
        observationalLaw (ofParam base p.parameter).toEuclideanSCM from
      boxTruncated_ofParam_interventionalLaw_eq base p hK hlabels
        (noIntervention kind) (by simp [noIntervention])]
    exact hW
  have hext := hdefined N hN hU hNW
  have hobj := boxTruncated_ofParam_objectiveIntegral_eq base p hlabels
    t muT F domain hdomain hp hext
  unfold populationLowerBound
  apply le_trans (iInf_le_of_le N (iInf_le_of_le hN
    (iInf_le_of_le hU (iInf_le_of_le hNW le_rfl))))
  exact le_of_eq (congrArg (fun x : ℝ => (x : EReal)) hobj)

/-- If [every categorical node's number of categories is at most the bounding
radius](hyp:hlabels), [the uniform coordinatewise distance between two clipped
population mechanisms on any input set is at most the uniform coordinatewise
distance between their cube mechanisms on the entire input cube](goal). -/
-- @node: boxTruncated_ofParam_supDistOn_le
lemma boxTruncated_ofParam_supDistOn_le
    (base : CanonicalSCM kind dims dag G C)
    (p q : PopulationParam kind dims dag C K L)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ K)
    (i : Fin n) (S : Set (Input kind dims dag C i)) :
    supDistOn S ((boxTruncatedSCM (ofParam base p.parameter) K hlabels).f i)
      ((boxTruncatedSCM (ofParam base q.parameter) K hlabels).f i) ≤
        supDistOn Set.univ (p.parameter.1.val i) (q.parameter.1.val i) := by
  apply iSup_le
  intro x
  simp only [boxTruncated_ofParam_apply base p hlabels,
    boxTruncated_ofParam_apply base q hlabels]
  exact le_iSup_of_le
    ⟨⟨structuralBoxProjection (ofParam base p.parameter) K i x.val,
      structuralBoxProjection_mem_inputCube _ K i x.val⟩, Set.mem_univ _⟩ le_rfl

-- @node: boxTruncated_ofParam_structural_error_le_paramDist
/-- Given [an input set for each node on which to compare mechanisms](hyp:S),
if [every categorical node's number of categories is at most the bounding
radius](hyp:hlabels), [the sum over nodes of the uniform coordinatewise distances
between two clipped population mechanisms on any chosen input sets is at most
their parameter distance, viewed as an extended nonnegative number](goal). -/
lemma boxTruncated_ofParam_structural_error_le_paramDist
    (base : CanonicalSCM kind dims dag G C)
    (p q : PopulationParam kind dims dag C K L)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ K)
    (S : ∀ i, Set (Input kind dims dag C i)) :
    (∑ i, supDistOn (S i)
      ((boxTruncatedSCM (ofParam base p.parameter) K hlabels).f i)
      ((boxTruncatedSCM (ofParam base q.parameter) K hlabels).f i)) ≤
        ENNReal.ofReal (paramDist p q) := by
  rw [paramDist_ofReal_eq_sum]
  exact (Finset.sum_le_sum (fun i _ =>
    boxTruncated_ofParam_supDistOn_le base p q hlabels i (S i))).trans
      (le_add_of_nonneg_right bot_le)

end Papers.TbsNeuralCausalPi
