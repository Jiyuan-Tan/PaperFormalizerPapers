module

public import Papers.TbsNeuralCausalPi.Helpers.ArchitectureAssembly
public import Papers.TbsNeuralCausalPi.Setup.Optimization
public import Papers.TbsNeuralCausalPi.Setup.Assumptions.Model
public import Papers.TbsNeuralCausalPi.Setup.Assumptions.Generators
public import Papers.TbsNeuralCausalPi.Setup.CitedResults
public import Papers.TbsNeuralCausalPi.Helpers.CubeDimension
/-! # Thresholds selected from the structural and latent network constructions -/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
open MeasureTheory
open scoped NNReal
noncomputable section
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)} {C : Fin b → Set (Fin n)}

-- @node: architecture_thresholds_from_constructions
/-- For [nonnegative mechanism regularity and output bounds L and K](hyp:L,K),
[latent component sets](hyp:sets), [their chart dimensions](hyp:dC), and
[a nonnegative chart regularity bound](hyp:Lchart), suppose [the model and
components satisfy the architecture construction premises](hyp:hmodel),
[Perekrestenko quantized generation is available](hyp:hPerekrestenko_of_gate),
[Yarotsky coordinate approximation is available](hyp:hYarotskyCoordinate_of_gate),
and [Yarotsky structural approximation is available](hyp:hYarotskyStructural_of_gate).
Then [there exist three positive architecture thresholds that are admissible
factors for themselves and certify the structural and latent network
constructions for these data](goal). -/
lemma architecture_thresholds_from_constructions
    (M : CanonicalSCM kind dims dag G C) (L K : ℝ≥0) (counts : Fin b → ℕ)
    (sets : ∀ j, Fin (counts j) → Set (L1Vec (dims j)))
    (dC : ∀ j, Fin (counts j) → ℕ) (Lchart : ℝ≥0)
    (hmodel : ArchitectureConstructionPremises M L K counts sets dC Lchart)
    (hPerekrestenko_of_gate : PerekrestenkoQuantizedGeneration)
    (hYarotskyCoordinate_of_gate : YarotskyCoordinateApprox)
    (hYarotskyStructural_of_gate : YarotskyStructuralApprox) :
    ∃ a : ℕ × ℕ × ℕ,
      ArchitectureFactorSelection a.1 a.2.1 a.2.2 a.1 a.2.1 a.2.2 ∧
      ArchitectureConstructionThresholds M K (LhatF M.toEuclideanSCM L)
        counts dC a.1 a.2.1 a.2.2 := by
  classical
  have hext (i : Fin n) :
      ∃ g : Input kind dims dag C i → L1Vec (outputDim (kind i)),
        LipschitzWith L g ∧
        ((kind i).isLeft = true → ∀ x, ‖g x‖ ≤ K) ∧
        ((kind i).isRight = true → ∀ x,
          (g x).ofLp ∈ probabilitySimplex (outputDim (kind i))) ∧
        Set.EqOn g (M.f i) (M.domain i none) := by
    have hf := hmodel.2.2.2.2.2.2.2.2.2.1 i
    have hkind : (∃ d, kind i = Sum.inl d) ∨ ∃ k, kind i = Sum.inr k := by
      cases hi : kind i with
      | inl d => exact Or.inl ⟨d, rfl⟩
      | inr k => exact Or.inr ⟨k, rfl⟩
    rcases hkind with ⟨d, hi⟩ | ⟨k, hi⟩
    · obtain ⟨g, hg, hb, heq⟩ := canonical_bounded_vector_structural_extension M i L K hf
        (hmodel.2.2.2.2.2.2.2.2.2.2.1 i d hi)
      exact ⟨g, hg, fun _ => hb, by simp [hi], heq⟩
    · obtain ⟨g, hg, hs, heq⟩ := canonical_simplex_structural_extension M i k hi L hf
      exact ⟨g, hg, by simp [hi], fun _ => hs, heq⟩
  choose f hf hb hs heq using hext
  apply architecture_thresholds_of_cube_extension M L K counts sets dC Lchart
    hmodel hYarotskyCoordinate_of_gate f ?_ ?_ ?_ ?_
  · intro i
    by_cases ho : 0 < outputDim (kind i)
    · exact (hf i).lipschitzOnWith.weaken
        (L_le_LhatF_of_positive_output M.toEuclideanSCM L hmodel.2.2.2.2.2.1.1 i ho)
    · apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      have he : f i x = f i y := by
        apply PiLp.ext
        intro j
        exact (ho (Nat.zero_lt_of_lt j.isLt)).elim
      rw [he, dist_self]
      positivity
  · intro i hi x hx
    exact hb i hi x
  · intro i hi x hx
    exact hs i hi x
  · intro i x hx
    exact heq i ⟨hx.1, Set.mem_univ _⟩

-- @node: ass:pin-fix-bd620122
/-- For [a canonical causal model M](hyp:M), [nonnegative mechanism regularity
and output bounds L and K](hyp:L,K), [latent component counts](hyp:counts),
[component chart dimensions](hyp:dC), [three construction thresholds](hyp:a0,a1,a2),
[a certificate that these thresholds support the architecture constructions for
the model and component data](hyp:hcert), and [three proposed architecture
factors](hyp:c0,c1,c2), [the numerical architecture constants condition](goal)
says that the thresholds are positive and the proposed factors dominate them.

The certificate is a parameter; this condition itself contains only the
positivity and factor inequalities. -/
def ConstructionArchitectureConstantsReading
    (M : CanonicalSCM kind dims dag G C) (L K : ℝ≥0) (counts : Fin b → ℕ)
    (dC : ∀ j, Fin (counts j) → ℕ) (a0 a1 a2 : ℕ)
    (hcert : ArchitectureConstructionThresholds M K (LhatF M.toEuclideanSCM L)
      counts dC a0 a1 a2) (c0 c1 c2 : ℕ) : Prop :=
  ArchitectureFactorSelection a0 a1 a2 c0 c1 c2

/-- Given [a canonical causal model M](hyp:M), [nonnegative mechanism regularity
and output bounds L and K](hyp:L,K), [latent component counts](hyp:counts),
[component sets](hyp:sets), [chart dimensions](hyp:dC), [a nonnegative chart
regularity bound](hyp:Lchart), [the architecture construction premises for
these data](hyp:hmodel), [Perekrestenko quantized generation](hyp:hPerekrestenko_of_gate),
[Yarotsky coordinate approximation](hyp:hYarotskyCoordinate_of_gate), and
[Yarotsky structural approximation](hyp:hYarotskyStructural_of_gate), [the
selected architecture thresholds](goal) are one triple whose existence is
guaranteed by the construction theorem. -/
def selectedArchitectureThresholds
    (M : CanonicalSCM kind dims dag G C) (L K : ℝ≥0) (counts : Fin b → ℕ)
    (sets : ∀ j, Fin (counts j) → Set (L1Vec (dims j)))
    (dC : ∀ j, Fin (counts j) → ℕ) (Lchart : ℝ≥0)
    (hmodel : ArchitectureConstructionPremises M L K counts sets dC Lchart)
    (hPerekrestenko_of_gate : PerekrestenkoQuantizedGeneration)
    (hYarotskyCoordinate_of_gate : YarotskyCoordinateApprox)
    (hYarotskyStructural_of_gate : YarotskyStructuralApprox) : ℕ × ℕ × ℕ :=
  Classical.choose (architecture_thresholds_from_constructions M L K counts sets dC Lchart
    hmodel hPerekrestenko_of_gate hYarotskyCoordinate_of_gate hYarotskyStructural_of_gate)

/-- For [a canonical causal model M](hyp:M), [nonnegative mechanism regularity
and output bounds L and K](hyp:L,K), [latent component counts](hyp:counts),
[component sets](hyp:sets), [chart dimensions](hyp:dC), [a nonnegative chart
regularity bound](hyp:Lchart), [Perekrestenko quantized generation](hyp:hPerekrestenko_of_gate),
[Yarotsky coordinate approximation](hyp:hYarotskyCoordinate_of_gate),
[Yarotsky structural approximation](hyp:hYarotskyStructural_of_gate),
[three construction thresholds](hyp:a0,a1,a2), and [three proposed architecture
factors](hyp:c0,c1,c2), [the construction architecture factor selection
condition](goal) requires positive thresholds and proposed factors at least
as large as the corresponding thresholds. -/
def ConstructionArchitectureFactorSelection
    (M : CanonicalSCM kind dims dag G C) (L K : ℝ≥0) (counts : Fin b → ℕ)
    (sets : ∀ j, Fin (counts j) → Set (L1Vec (dims j)))
    (dC : ∀ j, Fin (counts j) → ℕ) (Lchart : ℝ≥0)
    (hPerekrestenko_of_gate : PerekrestenkoQuantizedGeneration)
    (hYarotskyCoordinate_of_gate : YarotskyCoordinateApprox)
    (hYarotskyStructural_of_gate : YarotskyStructuralApprox)
    (a0 a1 a2 c0 c1 c2 : ℕ) : Prop :=
  ArchitectureFactorSelection a0 a1 a2 c0 c1 c2

end
end Papers.TbsNeuralCausalPi
