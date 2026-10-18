module
public import Papers.TbsNeuralCausalPi.Helpers.CanonicalConditionalPropensity
public import Papers.TbsNeuralCausalPi.Helpers.BoundedEvaluation
public import Papers.TbsNeuralCausalPi.Helpers.SimulationTableAmbiguity
public import Papers.TbsNeuralCausalPi.Helpers.GeneratorArchitectureBudgets
public import Papers.TbsNeuralCausalPi.Helpers.DoseResponseNonDescendant
/-! # Construction-derived support bounds for restricted neural candidates

Clipping carries every generated private block into its prescribed cube.
The continuous output restriction and the finite categorical label ranges
then bound actual observations uniformly over representations and sample sizes.
The common radius includes all labels, including labels of zero true probability.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

-- @node: estimationObservationRadius
/-- For [a fixed number of nodes](hyp:n), [their continuous or categorical
types](hyp:kind), and [a nonnegative output bound](hyp:K), the [common observation
radius](goal) is that bound plus the total number of categories summed over all
categorical nodes. -/
def estimationObservationRadius (kind : Fin n → NodeKind) (K : ℝ≥0) : ℝ≥0 :=
  K + ∑ i, (noiseDim (kind i) : ℝ≥0)

-- @node: estimationObservationRadius_ge
/-- For [a nonnegative output bound K](hyp:K), [the common observation radius is at least K](goal). -/
lemma estimationObservationRadius_ge (K : ℝ≥0) :
    K ≤ estimationObservationRadius kind K := le_add_of_nonneg_right (by positivity)

-- @node: estimationObservationRadius_labels
/-- For [a nonnegative output bound K](hyp:K), if [a node is categorical with the specified number of categories](hyp:hi),
[that number is at most the common observation radius](goal). -/
lemma estimationObservationRadius_labels (K : ℝ≥0) (i : Fin n) (k : ℕ)
    (hi : kind i = Sum.inr k) : (k : ℝ) ≤ estimationObservationRadius kind K := by
  have h := Finset.single_le_sum (f := fun i => (noiseDim (kind i) : ℝ≥0))
    (fun _ _ => zero_le) (Finset.mem_univ i)
  have hk : (k : ℝ≥0) ≤ estimationObservationRadius kind K := by
    simpa only [estimationObservationRadius, hi, noiseDim] using
      h.trans (le_add_of_nonneg_left (by positivity))
  exact_mod_cast hk

-- @node: generatorClassN_mem_boundedCube
/-- For [private-coordinate dimensions assigned to each block](hyp:dC) and
[a nonnegative clipping radius K](hyp:K), if
[a generator belongs to the clipped neural generator class](hyp:hg), then
[its output at every input lies in the block's cube with the clipping radius](goal). -/
lemma generatorClassN_mem_boundedCube {counts : Fin b → ℕ}
    (dC : ∀ j, Fin (counts j) → ℕ) (K : ℝ≥0) (D c1 c2 : ℕ)
    (L1 L2 : ℕ → ℕ) (tau : ℕ → ℝ) (r : ℕ) (j : Fin b)
    (g : ((Fin (counts j) → ℝ) × (Fin (counts j) → ℝ)) → L1Vec (dims j))
    (hg : g ∈ generatorClassN counts dC K D c1 c2 L1 L2 tau r j)
    (z : (Fin (counts j) → ℝ) × (Fin (counts j) → ℝ)) :
    g z ∈ boundedCube (dims j) K := by
  obtain ⟨q, rfl⟩ := hg
  intro k
  change |max (-(K : ℝ)) (min ((q.eval z).ofLp k) K)| ≤ K
  exact abs_le.mpr ⟨le_max_left _ _,
    max_le (by linarith [K.coe_nonneg]) (min_le_right _ _)⟩

-- @node: restrictedCandidate_intervened_coordinate_bound
/-- For [a nonnegative output bound K](hyp:K) and [a nonnegative Lipschitz bound L](hyp:L),
if [a neural causal model satisfies the output and Lipschitz restrictions](hyp:hR)
and [every coordinate fixed by the intervention is bounded in absolute value by
the common observation radius](hyp:ht), then [every coordinate evaluated under
that intervention is bounded in absolute value by the same radius, for every
exogenous input](goal). -/
lemma restrictedCandidate_intervened_coordinate_bound {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    (K L : ℝ≥0) (R : NCMIn kind dims dag G C counts F0 F1)
    (hR : restrictedCandidate K L R) (t : LawIntervention kind)
    (ht : ∀ i v, t.val i = some v → ∀ j,
      |v.ofLp j| ≤ estimationObservationRadius kind K)
    (u : Exogenous kind dims) (i : Fin n) (j : Fin (valueDim (kind i))) :
    |(intervenedEval R.canonical.toEuclideanSCM t.val u).ofLp ⟨i,j⟩| ≤
      estimationObservationRadius kind K := by
  apply canonical_evalSteps_coordinate_bound R.canonical
    (estimationObservationRadius kind K) (estimationObservationRadius_labels K)
    _ t ht u (n * n + n) i j
  intro i d hi x hx
  exact (restrictedCandidate_continuous_output_bound K L R hR i d hi x hx).trans
    (by exact_mod_cast estimationObservationRadius_ge (kind := kind) K)

-- @node: restrictedCandidate_ncmEval_coordinate_bound
/-- For [a nonnegative output bound K](hyp:K) and [a nonnegative Lipschitz bound L](hyp:L),
if [a neural causal model satisfies the output and Lipschitz restrictions](hyp:hR),
then [each coordinate of its simulated observation is bounded in absolute value
by the common observation radius, for every simulation input](goal). -/
lemma restrictedCandidate_ncmEval_coordinate_bound {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    (K L : ℝ≥0) (R : NCMIn kind dims dag G C counts F0 F1)
    (hR : restrictedCandidate K L R) (z : SimulationInput kind counts)
    (i : Fin n) (j : Fin (valueDim (kind i))) :
    |(ncmEval R z).ofLp ⟨i,j⟩| ≤ estimationObservationRadius kind K := by
  exact restrictedCandidate_intervened_coordinate_bound K L R hR
    (noIntervention kind) (by simp [noIntervention]) _ i j

-- @node: restrictedCandidate_observationalLaw_box
/-- For [a nonnegative output bound K](hyp:K) and [a nonnegative Lipschitz bound L](hyp:L),
if [a neural causal model satisfies the output and Lipschitz restrictions](hyp:hR),
then [its observational law assigns probability one to the box whose coordinates
are bounded in absolute value by the common observation radius](goal). -/
lemma restrictedCandidate_observationalLaw_box {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    (K L : ℝ≥0) (R : NCMIn kind dims dag G C counts F0 F1)
    (hR : restrictedCandidate K L R) :
    observationalLaw R.canonical.toEuclideanSCM
      {v | ∀ c, |v.ofLp c| ≤ estimationObservationRadius kind K} = 1 := by
  let := simulationInputLaw_probability kind counts
  rw [← ncmEval_law R, Measure.map_apply (by fun_prop)
    (joint_coordinate_box_isCompact (kind := kind) _).measurableSet]
  have heq : ncmEval R ⁻¹' {v | ∀ c, |v.ofLp c| ≤ estimationObservationRadius kind K} =
      Set.univ := by
    ext z
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    rintro ⟨i,j⟩
    exact restrictedCandidate_ncmEval_coordinate_bound K L R hR z i j
  rw [heq, measure_univ]

-- @node: ncm_generatorClassN_blockLaw_box
/-- With [private-coordinate dimensions assigned to each block](hyp:dC) and
[a nonnegative clipping radius](hyp:K), [the latent law of each block generated
by the clipped neural class assigns probability one to its cube of that radius](goal). -/
lemma ncm_generatorClassN_blockLaw_box {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C}
    (dC : ∀ j, Fin (counts j) → ℕ) (K : ℝ≥0) (D c1 c2 : ℕ)
    (L1 L2 : ℕ → ℕ) (tau : ℕ → ℝ) (r : ℕ)
    (R : NCMIn kind dims dag G C counts F0
      (generatorClassN counts dC K D c1 c2 L1 L2 tau r)) (j : Fin b) :
    (R.canonical.blockLaw j : Measure _) (boundedCube (dims j) K) = 1 := by
  let := generatorInputLaw_probability (counts j)
  rw [R.blockLaw_eq j, Measure.map_apply (by fun_prop)
    (boundedCube_isCompact (dims j) K).measurableSet]
  have heq : R.generator j ⁻¹' boundedCube (dims j) K = Set.univ := by
    ext z
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    exact generatorClassN_mem_boundedCube dC K D c1 c2 L1 L2 tau r j
      (R.generator j) (R.generatorMem j) z
  rw [heq, measure_univ]

-- @node: ncm_generatorClassN_latent_ae_bound
/-- For [private-coordinate dimensions assigned to each block](hyp:dC) and
[a nonnegative clipping radius K](hyp:K),
[almost every latent draw from a model in the clipped neural generator class
has every block coordinate bounded in absolute value by the clipping radius](goal). -/
lemma ncm_generatorClassN_latent_ae_bound {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C}
    (dC : ∀ j, Fin (counts j) → ℕ) (K : ℝ≥0) (D c1 c2 : ℕ)
    (L1 L2 : ℕ → ℕ) (tau : ℕ → ℝ) (r : ℕ)
    (R : NCMIn kind dims dag G C counts F0
      (generatorClassN counts dC K D c1 c2 L1 L2 tau r)) :
    ∀ᵐ u ∂ R.canonical.latentLaw, ∀ j k, |(blockProjection j u).ofLp k| ≤ K := by
  apply ae_all_iff.mpr
  intro j
  have hb : ∀ᵐ x ∂(R.canonical.blockLaw j : Measure _), x ∈ boundedCube (dims j) K :=
    (ae_mem_iff_measure_eq (boundedCube_isCompact (dims j) K).measurableSet.nullMeasurableSet).mpr
      (by simpa only [measure_univ] using
        ncm_generatorClassN_blockLaw_box dC K D c1 c2 L1 L2 tau r R j)
  rw [← canonical_blockProjection_law R.canonical j] at hb
  exact (ae_map_iff (by fun_prop [blockProjection])
    (boundedCube_isCompact (dims j) K).measurableSet).mp hb

-- @node: restrictedCandidate_variablesBoundedAt
/-- Given [private-coordinate dimensions for each block](hyp:dC) and
[output and Lipschitz bounds](hyp:K,L), if [the output bound is positive](hyp:hK)
and [a model with clipped neural generators satisfies those restrictions](hyp:hR),
then [its observed variables and latent block coordinates are almost surely
bounded by the positive common observation radius](goal).

Intrinsic Gumbel noise is excluded from this bound. -/
lemma restrictedCandidate_variablesBoundedAt {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C}
    (dC : ∀ j, Fin (counts j) → ℕ) (K L : ℝ≥0) (hK : 0 < K)
    (D c1 c2 : ℕ) (L1 L2 : ℕ → ℕ) (tau : ℕ → ℝ) (r : ℕ)
    (R : NCMIn kind dims dag G C counts F0
      (generatorClassN counts dC K D c1 c2 L1 L2 tau r))
    (hR : restrictedCandidate K L R) :
    VariablesBoundedAt R.canonical.toEuclideanSCM (estimationObservationRadius kind K) := by
  refine ⟨?_, ?_⟩
  · have hpos := hK.trans_le (estimationObservationRadius_ge (kind := kind) K)
    exact_mod_cast hpos
  filter_upwards [ncm_generatorClassN_latent_ae_bound dC K D c1 c2 L1 L2 tau r R]
    with u hu
  constructor
  · intro i j
    exact restrictedCandidate_intervened_coordinate_bound K L R hR
      (noIntervention kind) (by simp [noIntervention]) u i j
  · intro j k
    exact (hu j k).trans (by exact_mod_cast estimationObservationRadius_ge (kind := kind) K)

-- @node: estimationObservationBox_dist_le
/-- For [a nonnegative output bound](hyp:K), if [every coordinate of the first
observation](hyp:hx) and [every coordinate of the second observation](hyp:hy) is
bounded in absolute value by the common observation radius, then [their distance
is at most the total number of observation coordinates times twice that radius](goal). -/
lemma estimationObservationBox_dist_le (K : ℝ≥0) (x y : Joint kind)
    (hx : ∀ c, |x.ofLp c| ≤ estimationObservationRadius kind K)
    (hy : ∀ c, |y.ofLp c| ≤ estimationObservationRadius kind K) :
    dist x y ≤ Fintype.card (Σ i, Fin (valueDim (kind i))) *
      (2 * (estimationObservationRadius kind K : ℝ)) := by
  rw [PiLp.dist_eq_of_L1]
  calc
    _ ≤ ∑ _c : Σ i, Fin (valueDim (kind i)),
        2 * (estimationObservationRadius kind K : ℝ) := by
      apply Finset.sum_le_sum
      intro c _
      rw [Real.dist_eq]
      exact (abs_sub (x.ofLp c) (y.ofLp c)).trans (by linarith [hx c, hy c])
    _ = _ := by simp

-- @node: restrictedCandidate_mem_boundedLipClass
/-- For [output and Lipschitz bounds](hyp:K,L), if [the output bound is at least
one whenever a categorical node exists](hyp:hcatK) and [a neural causal model
satisfies the corresponding candidate restrictions](hyp:hR), then [its canonical
model belongs to the population class with those output and Lipschitz bounds](goal). -/
lemma restrictedCandidate_mem_boundedLipClass {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    (K L : ℝ≥0) (hcatK : ∀ i k, kind i = Sum.inr k → (1 : ℝ) ≤ K)
    (R : NCMIn kind dims dag G C counts F0 F1) (hR : restrictedCandidate K L R) :
    R.canonical ∈ canonicalClass (boundedLipClass K L) := by
  intro i
  refine ⟨(hR i).1.mono (fun x hx => ⟨hx, Set.mem_univ _⟩), ?_⟩
  intro x hx
  have hcases : (∃ d, kind i = Sum.inl d) ∨ (∃ k, kind i = Sum.inr k) := by
    cases kind i with
    | inl d => exact Or.inl ⟨d, rfl⟩
    | inr k => exact Or.inr ⟨k, rfl⟩
  rcases hcases with ⟨d, hi⟩ | ⟨k, hi⟩
  · exact restrictedCandidate_continuous_output_bound K L R hR i d hi x ⟨hx, Set.mem_univ _⟩
  · have hs := R.canonical.simplex i k hi x hx
    have hn : ‖R.canonical.f i x‖ = 1 := by
      rw [PiLp.norm_eq_of_L1]
      change (∑ j, |(R.canonical.f i x).ofLp j|) = 1
      have hs' : (R.canonical.f i x).ofLp ∈ stdSimplex ℝ (Fin (outputDim (kind i))) := by
        constructor
        · intro j
          have h := hs.1 (Fin.cast (congrArg outputDim hi) j)
          have he : Fin.cast (congrArg outputDim hi).symm
              (Fin.cast (congrArg outputDim hi) j) = j := Fin.ext rfl
          dsimp only at h
          rwa [he] at h
        · exact (Equiv.sum_comp (finCongr (congrArg outputDim hi).symm)
            (fun j => (R.canonical.f i x).ofLp j)).symm.trans hs.2
      simpa only [abs_of_nonneg (hs'.1 _)] using hs'.2
    exact hn.le.trans (hcatK i k hi)

-- @node: restrictedCandidate_mem_populationOptimizationModels
/-- Given [private-coordinate dimensions for each block](hyp:dC) and
[output and Lipschitz bounds](hyp:K,L), suppose [the output bound is at least one
whenever a categorical node exists](hyp:hcatK), [a candidate with clipped neural
generators satisfies those restrictions](hyp:hR), and [its observational law has
zero Wasserstein distance from the reference model's law](hyp:heq). Then [the
candidate is admissible for the reference model's bounded population optimization](goal). -/
lemma restrictedCandidate_mem_populationOptimizationModels {counts : Fin b → ℕ}
    (base : CanonicalSCM kind dims dag G C)
    {F0 : StructuralClass kind dims dag C}
    (dC : ∀ j, Fin (counts j) → ℕ) (K L : ℝ≥0)
    (hcatK : ∀ i k, kind i = Sum.inr k → (1 : ℝ) ≤ K)
    (D c1 c2 : ℕ) (L1 L2 : ℕ → ℕ) (tau : ℕ → ℝ) (r : ℕ)
    (R : NCMIn kind dims dag G C counts F0
      (generatorClassN counts dC K D c1 c2 L1 L2 tau r))
    (hR : restrictedCandidate K L R)
    (heq : wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
      (observationalLaw base.toEuclideanSCM) = 0) :
    R.canonical.toEuclideanSCM ∈ populationOptimizationModels base K L := by
  exact ⟨R.canonical, restrictedCandidate_mem_boundedLipClass K L hcatK R hR,
    ncm_generatorClassN_blockLaw_box dC K D c1 c2 L1 L2 tau r R, heq, rfl⟩

-- @node: restrictedCandidates_compact_observation_box
/-- For [fixed output and Lipschitz bounds](hyp:K,L), [there exist a compact set
of observations and a nonnegative diameter bound such that every simulated
observation from every restricted candidate lies in that set, and any two points
of the set are at most that distance apart](goal). -/
lemma restrictedCandidates_compact_observation_box (K L : ℝ≥0)
    (counts : Fin b → ℕ) (F0 : StructuralClass kind dims dag C)
    (F1 : GeneratorClass dims counts) :
    ∃ S : Set (Joint kind), ∃ B : ℝ, IsCompact S ∧ 0 ≤ B ∧
      (∀ R : NCMIn kind dims dag G C counts F0 F1, restrictedCandidate K L R →
        ∀ z, ncmEval R z ∈ S) ∧
      (∀ x ∈ S, ∀ y ∈ S, dist x y ≤ B) := by
  refine ⟨{v | ∀ c, |v.ofLp c| ≤ estimationObservationRadius kind K},
    Fintype.card (Σ i, Fin (valueDim (kind i))) *
      (2 * (estimationObservationRadius kind K : ℝ)),
    joint_coordinate_box_isCompact _, by positivity, ?_, ?_⟩
  · intro R hR z
    rintro ⟨i,j⟩
    exact restrictedCandidate_ncmEval_coordinate_bound K L R hR z i j
  · intro x hx y hy
    exact estimationObservationBox_dist_le K x y hx hy

end
end Papers.TbsNeuralCausalPi
