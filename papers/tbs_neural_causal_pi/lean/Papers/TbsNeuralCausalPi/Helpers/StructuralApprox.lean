module

public import Papers.TbsNeuralCausalPi.Helpers.ArchitectureThresholds
public import Papers.TbsNeuralCausalPi.Helpers.StructuralCommonBudgets
public import Papers.TbsNeuralCausalPi.Helpers.DeepReLUApprox
public import Papers.TbsNeuralCausalPi.Setup.Assumptions.Estimation
public import Papers.TbsNeuralCausalPi.Setup.CitedResults
public import Papers.TbsNeuralCausalPi.Helpers.EuclideanModulus
public import Papers.TbsNeuralCausalPi.Helpers.StructuralGluing
public import Papers.TbsNeuralCausalPi.Helpers.WideQuantization
public import Papers.TbsNeuralCausalPi.Helpers.WideGeneratorSupport
public import Papers.TbsNeuralCausalPi.Helpers.GeneratorArchitectureBudgets
/-! # Fixed-depth approximation preserving the Lipschitz bound -/
public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
open scoped NNReal


open MeasureTheory
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)} {C : Fin b → Set (Fin n)}

/-- Assuming [the structural approximation theorem of Yarotsky is available](hyp:hgate),
[each positive input dimension has a positive constant such that every
coordinate of a canonical structural function that is Lipschitz on the unit
cube admits, at every positive hidden depth, a scalar ReLU approximation of
width twice the input dimension plus ten, with uniform error at most the
constant times the Lipschitz bound times depth to the power minus two divided
by input dimension](goal). -/
-- @node: yarotskyStructural_lipschitz
lemma yarotskyStructural_lipschitz (hgate : YarotskyStructuralApprox) :
    ∀ d : ℕ, 0 < d → ∃ a : ℝ, 0 < a ∧
      ∀ (n b : ℕ) (kind : Fin n → NodeKind) (dims : Fin b → ℕ)
        (dag : Causalean.Graph.DAG (Fin n)) (G : SimpleGraph (Fin n))
        (C : Fin b → Set (Fin n)) (M : CanonicalSCM kind dims dag G C)
        (i : Fin n) (hd : structuralInputSize M.toEuclideanSCM i = d),
        let f := fun x : L1Vec d => M.f i
          (structuralFiniteCoordinates M.toEuclideanSCM i
            (WithLp.toLp 1 (fun k => x.ofLp (Fin.cast hd k))))
        ∀ L : ℝ≥0, LipschitzOnWith L f (unitCube d) →
          ∀ j : Fin (outputDim (kind i)),
            ∀ depth : ℕ, 1 ≤ depth → ∃ q : ReLUNet d 1 (2*d+10) depth,
              ∀ x ∈ unitCube d,
                |(f x).ofLp j - (q.eval x).ofLp 0| ≤
                  a * L * (depth : ℝ) ^ (-(2 : ℝ) / d) := by
  intro d hd
  obtain ⟨a, c, ha, hc, happrox⟩ := hgate d hd
  refine ⟨a * d * c, by positivity, ?_⟩
  intro n b kind dims dag G C M i hdim f L hf j depth hdepth
  obtain ⟨q, hq⟩ := happrox n b kind dims dag G C M i hdim L hf j depth hdepth
  refine ⟨q, ?_⟩
  intro x hx
  refine (hq x hx).trans ?_
  have hmod := euclidModulus_le_of_lipschitzOn
    (lipschitzOnWith_output_coordinate hf j)
    (r := c * (depth : ℝ) ^ (-(2 : ℝ) / d)) (by positivity)
  calc
    _ ≤ a * (L * d * (c * (depth : ℝ) ^ (-(2 : ℝ) / d))) :=
      mul_le_mul_of_nonneg_left hmod ha.le
    _ = _ := by ring

/-- Assuming [the structural approximation theorem of Yarotsky is available](hyp:hgate)
and [the selected structural function has positive input dimension](hyp:hd),
[there is a positive constant, fixed before the Lipschitz and depth budgets,
such that whenever the function is Lipschitz on its unit cube, every positive
hidden depth admits a vector ReLU approximation of width equal to output
dimension times twice input dimension plus ten, with coordinatewise uniform
error bounded by the constant times the Lipschitz bound times depth to the
power minus two divided by input dimension](goal). -/
-- @node: yarotskyStructural_vector_lipschitz
lemma yarotskyStructural_vector_lipschitz (hgate : YarotskyStructuralApprox)
    (M : CanonicalSCM kind dims dag G C) (i : Fin n)
    (hd : 0 < structuralInputSize M.toEuclideanSCM i) :
    ∃ a : ℝ, 0 < a ∧ ∀ L : ℝ≥0,
      LipschitzOnWith L
        (fun x => M.f i (structuralFiniteCoordinates M.toEuclideanSCM i x))
        (unitCube (structuralInputSize M.toEuclideanSCM i)) →
      ∀ depth : ℕ, 1 ≤ depth →
        ∃ q : ReLUNet (structuralInputSize M.toEuclideanSCM i)
          (outputDim (kind i))
          (outputDim (kind i) * (2 * structuralInputSize M.toEuclideanSCM i + 10)) depth,
          ∀ x ∈ unitCube (structuralInputSize M.toEuclideanSCM i), ∀ j,
            |(M.f i (structuralFiniteCoordinates M.toEuclideanSCM i x)).ofLp j -
              (q.eval x).ofLp j| ≤
                a * L * (depth : ℝ) ^ (-(2 : ℝ) / structuralInputSize M.toEuclideanSCM i) := by
  classical
  obtain ⟨a, ha, happrox⟩ := yarotskyStructural_lipschitz hgate _ hd
  refine ⟨a, ha, ?_⟩
  intro L hLip depth hdepth
  have hcoordinates := happrox n b kind dims dag G C M i rfl L
    (by simpa only [Fin.cast_refl, id_eq, WithLp.toLp_ofLp] using hLip)
  choose q hq using fun j => hcoordinates j depth hdepth
  obtain ⟨Q, hQ⟩ := relu_parallel_stack_constructed q
  refine ⟨Q, ?_⟩
  intro x hx j
  rw [hQ]
  simpa only [Fin.cast_refl, id_eq, WithLp.toLp_ofLp] using hq j x hx

/-- For [nonnegative Lipschitz and boundedness budgets](hyp:L,K), [component
sets for each latent block](hyp:sets), [their chart dimensions](hyp:dC), and
[a nonnegative chart regularity bound](hyp:Lchart), suppose [the true model
satisfies the inherited deep-network premises](hyp:hinherited), [its structural
functions satisfy the prescribed Lipschitz bounds](hyp:hstructural), [its
variables are bounded by the boundedness budget](hyp:hbound), [its continuous
outputs have norm at most that budget on their domains](hyp:hcontinuousOutput),
[each block law has the specified finite support components](hyp:hsupp),
[those components have Lipschitz homeomorphic cube charts](hyp:hhomeo), [their
conditional laws satisfy lower-bound domination](hyp:hdom), and [their pullbacks
vanish on the chart boundaries](hyp:hboundary). If [Perekrestenko quantized
generation](hyp:hPerekrestenko_of_gate), [Yarotsky coordinate approximation](hyp:hYarotskyCoordinate_of_gate),
and [Yarotsky structural approximation](hyp:hYarotskyStructural_of_gate) are
available, [three architecture factors exist that satisfy both factor
selection and the construction thresholds for the model, boundedness budget,
induced structural Lipschitz budget, component counts, and chart dimensions](goal). -/
-- @node: exists_architecture_construction_thresholds
lemma exists_architecture_construction_thresholds
    (M : CanonicalSCM kind dims dag G C) (L K : ℝ≥0)
    (counts : Fin b → ℕ) (sets : ∀ j, Fin (counts j) → Set (L1Vec (dims j)))
    (dC : ∀ j, Fin (counts j) → ℕ) (Lchart : ℝ≥0)
    (hinherited : TrueSCMDeepNNPremises M L)
    (hstructural : TrueStructuralLipschitz M L K)
    (hbound : VariablesBoundedAt M.toEuclideanSCM K)
    (hcontinuousOutput : ∀ i d, kind i = Sum.inl d → ∀ x ∈ M.domain i none, ‖M.f i x‖ ≤ K)
    (hsupp : ∀ j, SupportFiniteComponents (M.blockLaw j : Measure _) (sets j))
    (hhomeo : ∀ j, ComponentsLipschitzHomeomorphic (sets j) (dC j) Lchart)
    (hdom : ∀ j i, LowerBoundDomination (d := dC j i)
      (ProbabilityTheory.cond (M.blockLaw j : Measure _) (sets j i)) (sets j i) Lchart)
    (hboundary : ∀ j i, PullbackVanishesOnBoundary (d := dC j i)
      (ProbabilityTheory.cond (M.blockLaw j : Measure _) (sets j i)) (sets j i) Lchart)
    (hPerekrestenko_of_gate : PerekrestenkoQuantizedGeneration)
    (hYarotskyCoordinate_of_gate : YarotskyCoordinateApprox)
    (hYarotskyStructural_of_gate : YarotskyStructuralApprox) :
    ∃ a0 a1 a2 : ℕ, ArchitectureFactorSelection a0 a1 a2 a0 a1 a2 ∧
      ArchitectureConstructionThresholds M K (LhatF M.toEuclideanSCM L)
        counts dC a0 a1 a2 := by
  rcases hinherited with
    ⟨hind, hdecomp, hcat, hcont, hprop, _, hregular, hdomain, hdim⟩
  have hmodel : ArchitectureConstructionPremises M L K counts sets dC Lchart :=
    ⟨hind, hdecomp, hcat, hbound, hregular,
      ⟨hdim.1, hdim.2⟩, hdomain, hcont, hprop, hstructural,
      hcontinuousOutput, hsupp, hhomeo, hdom, hboundary⟩
  obtain ⟨a, hselection, hthresholds⟩ :=
    architecture_thresholds_from_constructions M L K counts sets dC Lchart hmodel
      hPerekrestenko_of_gate hYarotskyCoordinate_of_gate hYarotskyStructural_of_gate
  exact ⟨a.1, a.2.1, a.2.2, hselection, hthresholds⟩

end Papers.TbsNeuralCausalPi
