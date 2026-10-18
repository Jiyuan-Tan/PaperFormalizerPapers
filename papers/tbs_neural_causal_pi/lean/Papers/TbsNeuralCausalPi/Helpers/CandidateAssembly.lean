module
public import Papers.TbsNeuralCausalPi.Helpers.StructuralClassBudgets
public import Papers.TbsNeuralCausalPi.Helpers.NetworkMeasurability
/-! # Assembling normalized structural networks and clipped generators

Simplex-valued raw networks already equal their categorical normalizations.
Their independently generated marginal laws define a canonical neural candidate
without imposing any further condition on its approximation error.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped NNReal
noncomputable section
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

-- @node: structuralClassN_neural_realization
/-- For [a canonical causal model](hyp:M), [output and Lipschitz budgets](hyp:K,L),
[network width and complexity budgets](hyp:W,c), and [a node](hyp:i), if
[a structural function](hyp:f) [belongs to the budgeted structural network
class](hyp:hf), then [a finite ReLU network represents that function exactly
in finite structural-input coordinates](goal). -/
lemma structuralClassN_neural_realization (M : CanonicalSCM kind dims dag G C)
    (K L : ℝ≥0) (W c : ℕ) (i : Fin n)
    (f : Input kind dims dag C i → L1Vec (outputDim (kind i)))
    (hf : f ∈ structuralClassN M K L (fun _ => W) c 0 i) :
    ∃ W' D', ∃ q : ReLUNet (structuralInputSize M.toEuclideanSCM i)
      (outputDim (kind i)) W' D',
      ∀ x, f (structuralFiniteCoordinates M.toEuclideanSCM i x) = q.eval x := by
  obtain ⟨q, _, hq⟩ := hf
  obtain ⟨Q, hQ, _⟩ := relu_truncK q K K.coe_nonneg
  exact ⟨_, _, Q, fun x => (hq x).trans (congrFun hQ x).symm⟩

-- @node: generatorClassN_measurable
/-- Given [component dimensions for each latent block](hyp:dC), [a clipping
bound](hyp:K), [generator architecture budgets](hyp:D,c1,c2,L1,L2), [a temperature](hyp:tau),
and [a block](hyp:j), if [a latent generator](hyp:g) [belongs to the prescribed
generator network class](hyp:hg), then [the generator is measurable](goal). -/
@[fun_prop] lemma generatorClassN_measurable {counts : Fin b → ℕ}
    (dC : ∀ j, Fin (counts j) → ℕ) (K : ℝ≥0) (D c1 c2 L1 L2 : ℕ)
    (tau : ℝ) (j : Fin b)
    (g : ((Fin (counts j) → ℝ) × (Fin (counts j) → ℝ)) → L1Vec (dims j))
    (hg : g ∈ generatorClassN counts dC K D c1 c2
      (fun _ => L1) (fun _ => L2) (fun _ => tau) 0 j) : Measurable g := by
  obtain ⟨q, rfl⟩ := hg
  change Measurable (coordinateClamp (-(K : ℝ)) K ∘ q.eval)
  fun_prop

-- @node: generatorClassN_neural_realization
/-- Given [component dimensions for each latent block](hyp:dC), [a clipping
bound](hyp:K), [generator architecture budgets](hyp:D,c1,c2,L1,L2), [a temperature](hyp:tau),
and [a block](hyp:j), if [a latent generator](hyp:g) [belongs to the prescribed
generator network class](hyp:hg), then [it has a neural generator realization](goal). -/
lemma generatorClassN_neural_realization {counts : Fin b → ℕ}
    (dC : ∀ j, Fin (counts j) → ℕ) (K : ℝ≥0) (D c1 c2 L1 L2 : ℕ)
    (tau : ℝ) (j : Fin b)
    (g : ((Fin (counts j) → ℝ) × (Fin (counts j) → ℝ)) → L1Vec (dims j))
    (hg : g ∈ generatorClassN counts dC K D c1 c2
      (fun _ => L1) (fun _ => L2) (fun _ => tau) 0 j) :
    NeuralGeneratorRealizable g := by
  obtain ⟨q, rfl⟩ := hg
  exact Or.inr ⟨dC j, _, _, _, _, tau, q, Or.inr ⟨K, rfl⟩⟩

-- @node: normalizedNetworkSCM
/-- The [canonical model assembled from normalized structural functions](goal)
uses [a reference canonical model's categorical and component structure](hyp:M),
[new structural functions](hyp:f) that [are measurable](hyp:hf) and
[take values in the probability simplex at categorical nodes](hyp:hs), and
[prescribed probability laws for the latent blocks](hyp:P). -/
def normalizedNetworkSCM (M : CanonicalSCM kind dims dag G C)
    (f : ∀ i, Input kind dims dag C i → L1Vec (outputDim (kind i)))
    (hf : ∀ i, Measurable (f i))
    (hs : ∀ i, (kind i).isRight = true → ∀ x,
      (f i x).ofLp ∈ probabilitySimplex (outputDim (kind i)))
    (P : ∀ j, ProbabilityMeasure (L1Vec (dims j))) :
    CanonicalSCM kind dims dag G C where
  categoricalPositive := M.categoricalPositive
  component := M.component
  exhaustive := M.exhaustive
  distinct := M.distinct
  f := f
  structuralMeasurable := hf
  blockLaw := P
  simplex := by
    intro i k h x hx
    have hi : (kind i).isRight = true := by rw [h]; rfl
    have hp := hs i hi x
    refine ⟨fun j => hp.1 _, ?_⟩
    exact (Equiv.sum_comp (finCongr (congrArg outputDim h).symm)
      (fun j => (f i x).ofLp j)).trans hp.2

-- @node: normalizedNetworksCandidate
/-- The [neural causal candidate assembled from normalized networks](goal) uses
[a reference canonical model](hyp:M), [output and Lipschitz budgets](hyp:K,L),
[latent component counts](hyp:counts), [component dimensions](hyp:dC),
[structural and generator architecture budgets](hyp:D,W,c0,c1,c2,L1,L2), and
[a temperature](hyp:tau). Its [structural functions](hyp:f)
[belong to the budgeted structural class](hyp:hfclass), [are globally Lipschitz
with the prescribed constant](hyp:hfLip), and [are simplex-valued at categorical
nodes](hyp:hs); its [latent generators](hyp:g) [belong to the budgeted generator
class](hyp:hgclass), and their generated marginal laws supply the latent blocks. -/
def normalizedNetworksCandidate (M : CanonicalSCM kind dims dag G C)
    (K L : ℝ≥0) (counts : Fin b → ℕ) (dC : ∀ j, Fin (counts j) → ℕ)
    (D W c0 c1 c2 L1 L2 : ℕ) (tau : ℝ)
    (f : ∀ i, Input kind dims dag C i → L1Vec (outputDim (kind i)))
    (hfclass : ∀ i, f i ∈ structuralClassN M K L (fun _ => W) c0 0 i)
    (hfLip : ∀ i, LipschitzWith L (f i))
    (hs : ∀ i, (kind i).isRight = true → ∀ x,
      (f i x).ofLp ∈ probabilitySimplex (outputDim (kind i)))
    (g : ∀ j, ((Fin (counts j) → ℝ) × (Fin (counts j) → ℝ)) → L1Vec (dims j))
    (hgclass : ∀ j, g j ∈ generatorClassN counts dC K D c1 c2
      (fun _ => L1) (fun _ => L2) (fun _ => tau) 0 j) :
    NCMIn kind dims dag G C counts (structuralClassN M K L (fun _ => W) c0 0)
      (generatorClassN counts dC K D c1 c2
        (fun _ => L1) (fun _ => L2) (fun _ => tau) 0) where
  canonical := normalizedNetworkSCM M f (fun i => (hfLip i).continuous.measurable) hs
    (fun j => by
      letI := generatorInputLaw_probability (counts j)
      exact ⟨(generatorInputLaw (counts j)).map (g j),
        Measure.isProbabilityMeasure_map
          (generatorClassN_measurable dC K D c1 c2 L1 L2 tau j (g j) (hgclass j)).aemeasurable⟩)
  rawStructural := f
  structuralMem := hfclass
  structuralNetworks := fun i => structuralClassN_neural_realization M K L W c0 i (f i) (hfclass i)
  continuousEq := fun _ _ _ => rfl
  categoricalEq := by
    intro i k h
    have hi : (kind i).isRight = true := by rw [h]; rfl
    constructor
    · intro x hx hn hp
      exact (structural_normalized_simplex_eq_self (hs i hi x)).symm
    · intro x hx
      exact ⟨(hs i hi x).1, by rw [(hs i hi x).2]; norm_num⟩
  generator := g
  generatorMem := hgclass
  generatorNetworks := fun j =>
    generatorClassN_neural_realization dC K D c1 c2 L1 L2 tau j (g j) (hgclass j)
  blockLaw_eq := fun _ => rfl

-- @node: normalizedNetworksCandidate_restricted
/-- For [a reference canonical model](hyp:M), [output and Lipschitz budgets](hyp:K,L),
[latent component counts and dimensions](hyp:counts,dC), [network architecture
budgets](hyp:D,W,c0,c1,c2,L1,L2), and [a temperature](hyp:tau), suppose
[structural functions](hyp:f) [belong to the budgeted class](hyp:hfclass),
[are globally Lipschitz with the prescribed constant](hyp:hfLip), and
[are simplex-valued at categorical nodes](hyp:hs), while [latent generators](hyp:g)
[belong to the generator class](hyp:hgclass). If [the continuous structural
outputs satisfy the output bound everywhere](hyp:hbound), then [the assembled
normalized-network candidate satisfies the output and regularity restrictions](goal). -/
lemma normalizedNetworksCandidate_restricted (M : CanonicalSCM kind dims dag G C)
    (K L : ℝ≥0) (counts : Fin b → ℕ) (dC : ∀ j, Fin (counts j) → ℕ)
    (D W c0 c1 c2 L1 L2 : ℕ) (tau : ℝ)
    (f : ∀ i, Input kind dims dag C i → L1Vec (outputDim (kind i)))
    (hfclass : ∀ i, f i ∈ structuralClassN M K L (fun _ => W) c0 0 i)
    (hfLip : ∀ i, LipschitzWith L (f i))
    (hs : ∀ i, (kind i).isRight = true → ∀ x,
      (f i x).ofLp ∈ probabilitySimplex (outputDim (kind i)))
    (g : ∀ j, ((Fin (counts j) → ℝ) × (Fin (counts j) → ℝ)) → L1Vec (dims j))
    (hgclass : ∀ j, g j ∈ generatorClassN counts dC K D c1 c2
      (fun _ => L1) (fun _ => L2) (fun _ => tau) 0 j)
    (hbound : ∀ i, (kind i).isLeft = true → ∀ x, ‖f i x‖ ≤ K) :
    restrictedCandidate K L
      (normalizedNetworksCandidate M K L counts dC D W c0 c1 c2 L1 L2 tau
        f hfclass hfLip hs g hgclass) := by
  intro i
  refine ⟨(hfLip i).lipschitzOnWith, ?_, ?_⟩
  · intro d hd x hx
    exact hbound i (by rw [hd]; rfl) x
  · intro k hk
    exact (hfLip i).lipschitzOnWith

/-- For [a canonical causal model](hyp:M) and [output and Lipschitz budgets](hyp:K,L),
assume [the output budget is positive](hyp:hK), [the maximum structural-input
dimension is positive](hyp:hD), and [the output budget is at least one whenever
a categorical node is present](hyp:hcatK). If [target structural functions](hyp:f)
[are Lipschitz with the prescribed constant on their input cubes](hyp:hf),
[have bounded continuous outputs there](hyp:hcont), and [have simplex-valued
categorical outputs there](hyp:hcat), then [positive complexity and width
thresholds and a positive error constant exist such that every larger network
budget and every family of admissible latent generators admit a restricted
neural candidate with exactly those generated block laws and total uniform
structural error at most the constant times the Lipschitz budget times width
to the negative reciprocal of the maximum input dimension](goal). -/
-- @node: restricted_candidates_from_structural_budgets
lemma restricted_candidates_from_structural_budgets
    (M : CanonicalSCM kind dims dag G C) (K L : ℝ≥0) (hK : 0 < K)
    (hD : 0 < maxInDim M.toEuclideanSCM)
    (hcatK : ∀ i, (kind i).isRight = true → (1 : ℝ) ≤ K)
    (f : ∀ i, Input kind dims dag C i → L1Vec (outputDim (kind i)))
    (hf : ∀ i, LipschitzOnWith L (f i) (inputCube K i))
    (hcont : ∀ i, (kind i).isLeft = true → ∀ x ∈ inputCube K i, ‖f i x‖ ≤ K)
    (hcat : ∀ i, (kind i).isRight = true → ∀ x ∈ inputCube K i,
      (f i x).ofLp ∈ probabilitySimplex (outputDim (kind i))) :
    ∃ c0 B : ℕ, 0 < c0 ∧ 0 < B ∧ ∃ A : ℝ, 0 < A ∧
      ∀ c W : ℕ, c0 ≤ c → B ≤ W →
      ∀ (counts : Fin b → ℕ) (dC : ∀ j, Fin (counts j) → ℕ)
        (D c1 c2 L1 L2 : ℕ) (tau : ℝ)
        (g : ∀ j, ((Fin (counts j) → ℝ) × (Fin (counts j) → ℝ)) → L1Vec (dims j)),
        (∀ j, g j ∈ generatorClassN counts dC K D c1 c2
          (fun _ => L1) (fun _ => L2) (fun _ => tau) 0 j) →
        ∃ R : NCMIn kind dims dag G C counts
          (structuralClassN M K L (fun _ => W) c 0)
          (generatorClassN counts dC K D c1 c2
            (fun _ => L1) (fun _ => L2) (fun _ => tau) 0),
          restrictedCandidate K L R ∧
          (∀ j, (R.canonical.blockLaw j : Measure _) =
            (generatorInputLaw (counts j)).map (g j)) ∧
          (∑ i, supDistOn (inputCube K i) (f i) (R.canonical.f i)) ≤
            ENNReal.ofReal (A * L * (W : ℝ)^(-(1 : ℝ) / maxInDim M.toEuclideanSCM)) := by
  obtain ⟨c0, B, hc0, hB, A, hA, happ⟩ :=
    structural_classN_mixed_budgets M K hK hD hcatK
  refine ⟨c0, B, hc0, hB, A, hA, ?_⟩
  intro c W hc hW counts dC D c1 c2 L1 L2 tau g hg
  obtain ⟨fhat, hclass, hLip, hbound, hs, _, _, herr⟩ :=
    happ c hc W hW L f hf hcont hcat
  refine ⟨normalizedNetworksCandidate M K L counts dC D W c c1 c2 L1 L2 tau
    fhat hclass hLip hs g hg, ?_, fun _ => rfl, herr⟩
  exact normalizedNetworksCandidate_restricted M K L counts dC D W c c1 c2 L1 L2 tau
    fhat hclass hLip hs g hg hbound

end
end Papers.TbsNeuralCausalPi
