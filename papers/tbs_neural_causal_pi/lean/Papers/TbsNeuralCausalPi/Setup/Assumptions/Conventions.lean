module
public import Papers.TbsNeuralCausalPi.Setup.Assumptions.Estimation
public import Papers.TbsNeuralCausalPi.Setup.Assumptions.Auxiliary
public import Papers.TbsNeuralCausalPi.Setup.Cubes
public import Papers.TbsNeuralCausalPi.Setup.CitedResults
/-! # Records of the pinned readings; only the push-forward norm convention is threaded -/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)} {C : Fin b → Set (Fin n)}
-- @node: ass:pin-205
/-- For [a structural causal model](hyp:M), [a treatment node](hyp:T),
[its scalar treatment function](hyp:treatment), [a reference probability law](hyp:P),
[a conditional density relative to that law](hyp:p), [an overlap lower bound](hyp:delta),
and [two interval endpoints](hyp:t1,t2), [the overlap condition requires that density
to describe the treatment conditional on its parents, with a positive lower bound
throughout the closed interval for almost every parent vector](goal). -/
def TreatmentOverlapDensityReading (M : EuclideanSCM kind dims) (T : Fin n)
    (treatment : Joint kind → ℝ) (P : ProbabilityMeasure ℝ)
    (p : ParentSpace M T × ℝ → ℝ≥0∞) (delta t1 t2 : ℝ) : Prop :=
  TreatmentOverlap M T treatment P p delta t1 t2

-- @node: ass:pin-206
/-- For [two treatment–outcome measures](hyp:mu,nu), [two regression functions,
the first for the second measure and the second for the first](hyp:f,fhat),
[a Lipschitz constant](hyp:L), and [a box radius](hyp:K), [the regression condition
requires both functions to be Lipschitz on the closed interval from minus the radius
to the radius and to equal their respective conditional expectations almost surely](goal). -/
def LipschitzRegressionBoxReading (mu nu : Measure (L1Vec 2))
    (f fhat : ℝ → ℝ) (L : ℝ≥0) (K : ℝ) : Prop :=
  LipschitzRegressionVersions mu nu f fhat L K

-- @node: ass:pin-fix-448b19a0
/-- For [a measure](hyp:mu) and [an event, without a measurability requirement](hyp:E),
[completion preserves the event's outer measure](goal). -/
def SampleLawCompletionProbability {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (E : Set X) : Prop :=
  mu.completion E = mu E

-- @node: ass:pin-fix-b83fa4d1
/-- For [two measures on a finite-dimensional vector space with the one-norm distance](hyp:mu,nu),
[Wasserstein-1 equals the infimum, over all couplings, of the expected one-norm
distance between the two coupled vectors](goal). -/
def ProductWassersteinOneNormReading {d : ℕ} (mu nu : Measure (L1Vec d)) : Prop :=
  wasserstein1 mu nu = ⨅ pi : couplings mu nu, ∫⁻ z, edist z.1 z.2 ∂pi.val

-- @node: ass:pin-177
/-- For [a bidirected graph](hyp:graph) and [a set of vertices](hyp:component),
[the component condition says that the set is a clique maximal under inclusion](goal). -/
def C2ComponentMaximalReading (graph : SimpleGraph (Fin n))
    (component : Set (Fin n)) : Prop :=
  Maximal graph.IsClique component

-- @node: ass:pin-fix-f6f485b1
/-- On [a specified domain](hyp:K), [the uniform-distance convention says that,
for any two vector-valued functions, their uniform distance is the supremum of
their absolute coordinate differences over that domain and all coordinates](goal). -/
def SupNormConventionPushForward {X : Type*} {d : ℕ} (K : Set X) : Prop :=
  ∀ F Fhat : X → L1Vec d,
    supDistOn K F Fhat =
      ⨆ x : K, ⨆ j : Fin d, ENNReal.ofReal |(F x).ofLp j - (Fhat x).ofLp j|
-- @node: ass:pin-fix-00130002
/-- For [a three-part generator](hyp:q), [its output law is the push-forward of
the full generator input law, including its Gumbel noise, through its evaluation map](goal). -/
def GeneratorLawIncludesGumbel {N d : ℕ} {dC : Fin N → ℕ} {W1 L1 W2 L2 : ℕ} {tau : ℝ} (q : ThreePartGenerator N d dC W1 L1 W2 L2 tau) : Prop :=
  generatorLaw q = (generatorInputLaw N).map q.eval

-- @node: ass:pin-fix-5f02b8a6
/-- For [an error depending on width, depth, and temperature](hyp:e) and
[a comparison rate with the same arguments](hyp:rate), [the asymptotic bound](goal)
requires a multiplier, an integer threshold, and a temperature cutoff such that
[the multiplier is positive](step:1), [the threshold is at least one](step:2),
[the cutoff is positive](step:3), [the cutoff is less than one](step:4), and
[the error is at most the
multiplier times the rate for all widths and depths above the threshold and all
positive temperatures below the cutoff](step:5). -/
def GeneratorBoundAsymptoticReading (e rate : ℕ → ℕ → ℝ → ℝ) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∃ B : ℕ, 1 ≤ B ∧ ∃ tauBar : ℝ,
    0 < tauBar ∧ tauBar < 1 ∧ ∀ W L : ℕ, B ≤ W → B ≤ L → ∀ tau : ℝ,
    0 < tau → tau < tauBar → e W L tau ≤ A * rate W L tau

-- @node: ass:pin-191
/-- For [a structural causal model](hyp:M) and [an intervention](hyp:t),
[the recursive intervention convention](goal) requires [each evaluated coordinate
to use its assigned intervention value when present, and otherwise the original
mechanism evaluated at the intervened parent values](step:1), and [the intervention
law to be the push-forward of the original latent law through that evaluation](step:2). -/
def InterventionRecursiveEvaluationReading (M : EuclideanSCM kind dims)
    (t : LawIntervention kind) : Prop :=
  (∀ u i j, (intervenedEval M t.val u).ofLp ⟨i,j⟩ =
    ((t.val i).getD (nodeValue M i (intervenedEval M t.val u) u)).ofLp j) ∧
    interventionalLaw M t = M.latentLaw.map (intervenedEval M t.val)

-- @node: ass:pin-fix-945d85ed
/-- For [an error depending on three network budgets and temperature](hyp:e)
and [a comparison rate with the same arguments](hyp:rate), [the deep-network
asymptotic bound](goal) requires a multiplier, three integer budget thresholds,
and a temperature cutoff such that [the multiplier is positive](step:1),
[the first threshold is at least one](step:2), [the second is at least one](step:3),
[the third is at least one](step:4), [the cutoff is positive](step:5),
[the cutoff is less than one](step:6), and
[the error is at most the multiplier times the rate whenever all three budgets
exceed their respective thresholds and the temperature is positive and below
the cutoff](step:7). -/
def DeepNNBoundAsymptoticReading (e rate : ℕ → ℕ → ℕ → ℝ → ℝ) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∃ B0 B1 B2 : ℕ, 1 ≤ B0 ∧ 1 ≤ B1 ∧ 1 ≤ B2 ∧
    ∃ tauBar : ℝ, 0 < tauBar ∧ tauBar < 1 ∧
      ∀ L0 L1 L2 : ℕ, B0 ≤ L0 → B1 ≤ L1 → B2 ≤ L2 → ∀ tau : ℝ,
        0 < tau → tau < tauBar → e L0 L1 L2 tau ≤ A * rate L0 L1 L2 tau

-- @node: ass:pin-fix-9bbf998f
/-- For [a component set](hyp:S), [a homeomorphism from the zero-dimensional
unit cube onto that set](hyp:h), [a first network with no output coordinates](hyp:g1),
and [a second network with no input coordinates](hyp:g2), [the singleton-block
condition requires a point](goal) such that [the component is its singleton](step:1),
[the homeomorphism always returns that point](step:2), [the first network always
returns the zero vector](step:3), and [the second always returns that point](step:4). -/
def SingletonComponentBlocks {d W1 L1 W2 L2 : ℕ} (S : Set (L1Vec d))
    (h : homeoClass (unitCube 0) S) (g1 : ReLUNet 1 0 W1 L1)
    (g2 : ReLUNet 0 d W2 L2) : Prop :=
  ∃ x, S = {x} ∧ (∀ z : unitCube 0, (h z).val = x) ∧
    (∀ z, g1.eval z = 0) ∧ ∀ z, g2.eval z = x

-- @node: ass:pin-fix-761562d5
/-- For [two point clouds](hyp:x,y), [their respective real weights](hyp:mu,nu),
and [an entropic regularization parameter](hyp:lam), [the Sinkhorn divergence
equals the entropic transport cost between the clouds minus half of each
cloud's entropic self-transport cost, using the same ground distance throughout](goal). -/
def SinkhornSelfTermsGroundCost {a b d : ℕ} (x : Fin a → L1Vec d) (y : Fin b → L1Vec d) (mu : Fin a → ℝ) (nu : Fin b → ℝ) (lam : ℝ) : Prop :=
  sinkhornDivergence lam x y mu nu = entropicW1 lam x y mu nu -
    entropicW1 lam x x mu mu / 2 - entropicW1 lam y y nu nu / 2

-- @node: ass:pin-fix-ca667e13
/-- For [two probability laws on a vector space with the one-norm distance](hyp:mu,nu),
[a nonnegative regularization parameter](hyp:lam), [its strict positivity](hyp:hlam),
and [finite first moments of the first and second laws](hyp:hmu,hnu),
[the law-level Sinkhorn divergence equals the real-valued entropic transport cost
between the laws minus half of each law's real-valued entropic self-transport cost](goal). -/
def SinkhornDebiasedReading {d : ℕ} (mu nu : ProbabilityMeasure (L1Vec d))
    (lam : ℝ≥0) (hlam : 0 < lam)
    (hmu : Integrable (fun x => ‖x‖) (mu : Measure (L1Vec d)))
    (hnu : Integrable (fun x => ‖x‖) (nu : Measure (L1Vec d))) : Prop :=
  lawSinkhornDivergence lam hlam mu nu hmu hnu =
    (lawEntropicW1 lam mu nu).toReal - (lawEntropicW1 lam mu mu).toReal / 2 -
      (lawEntropicW1 lam nu nu).toReal / 2

-- @node: ass:pin-fix-d19c63b5
/-- For [a measure](hyp:mu), [events indexed by two real tolerances](hyp:E), and
[a bound indexed by the same tolerances](hyp:bound), [the fixed-tolerance condition
requires each event's measure to be at most its bound for every pair of positive
tolerances](goal). -/
def SupWassersteinFixedTolerances {X : Type*} [MeasurableSpace X] (mu : Measure X) (E : ℝ → ℝ → Set X) (bound : ℝ → ℝ → ℝ≥0∞) : Prop :=
  ∀ delta eps : ℝ, 0 < delta → 0 < eps → mu (E delta eps) ≤ bound delta eps

-- @node: ass:pin-fix-c356d336
/-- [The canonical-model logarithm convention assigns negative infinity to the
extended logarithm of zero](goal). -/
def LogZeroConventionCanonical  : Prop :=
  extendedLog 0 = ⊥

-- @node: ass:pin-fix-ab17be7a
/-- [The approximation logarithm convention assigns negative infinity to the
extended logarithm of zero](goal). -/
def LogZeroConventionApprox  : Prop :=
  extendedLog 0 = ⊥

-- @node: ass:pin-fix-9463b114
/-- [The neural causal model logarithm convention assigns negative infinity to
the extended logarithm of zero](goal). -/
def LogZeroConventionNCM  : Prop :=
  extendedLog 0 = ⊥

-- @node: ass:pin-fix-e896f793
/-- In [a specified dimension](hyp:d), [the closed-cell condition requires every
dyadic cube at every refinement level to be closed](goal). -/
def HilbertCellsClosed (d : ℕ) : Prop :=
  ∀ r, ∀ S ∈ dyadicCubeCollection d r, IsClosed S

-- @node: ass:pin-fix-c85b9186
/-- In [a specified dimension](hyp:d), for [an ordering of cell words at every
refinement level](hyp:O), [the bijective-ordering condition requires each ordering
to be a bijection](goal). -/
def HilbertOrderingBijective (d : ℕ) (O : ∀ r, Fin (2^(d*r)) → CellWord d r) : Prop :=
  ∀ r, Function.Bijective (O r)

-- @node: ass:pin-fix-0bcb2cef
/-- For [a dimension](hyp:d) and [an adjacency condition indexed by level and
position](hyp:E), [the adjacency-range condition requires adjacency at every level
and every position from one up to, but excluding, the number of cells at that level](goal). -/
def HilbertAdjacencyRange (d : ℕ) (E : ℕ → ℕ → Prop) : Prop :=
  ∀ r i : ℕ, 1 ≤ i → i < 2^(d*r) → E r i

-- @node: ass:pin-fix-4a86c2eb
/-- For [a domain](hyp:S) and [two vector-valued structural functions](hyp:f,g),
[the structural uniform-distance convention equates their uniform distance with
the supremum of absolute coordinate differences over the domain and all coordinates](goal). -/
def StructuralSupNormConvention {X : Type*} {d : ℕ} (S : Set X) (f g : X → L1Vec d) : Prop :=
  supDistOn S f g = ⨆ x : S, ⨆ j : Fin d, ENNReal.ofReal |(f x).ofLp j-(g x).ofLp j|

-- @node: ass:pin-fix-0a7b21b0
/-- Given [a structural-function class](hyp:F0), [a generator class](hyp:F1),
[a magnitude bound](hyp:K), [a Lipschitz bound](hyp:L), [observed data](hyp:sample),
[common simulation draws](hyp:draws), [an entropic regularization parameter](hyp:lam),
[a discrepancy tolerance](hyp:alpha), and [a set of model representations](hyp:representations),
[the representation-optimization condition says this set consists exactly of
representations satisfying the continuous and categorical regularity restrictions
and whose simulated empirical law has Sinkhorn divergence from the observed
empirical law at most the tolerance](goal). -/
def OptimizationOverRepresentations {counts : Fin b → ℕ}
    (F0 : StructuralClass kind dims dag C) (F1 : GeneratorClass dims counts)
    (K L : ℝ≥0) {r m : ℕ} (sample : Fin r → Joint kind)
    (draws : Fin m → SimulationInput kind counts) (lam alpha : ℝ)
    (representations : Set (NCMIn kind dims dag G C counts F0 F1)) : Prop :=
  representations = {R | restrictedCandidate K L R ∧ sinkhornDivergence lam
    (fun i => jointVector (ncmEval R (draws i)))
    (fun i => jointVector (sample i)) (uniformWeights m) (uniformWeights r) ≤ alpha}

-- @node: ass:pin-fix-84ccd033
/-- For [a structural-function class](hyp:F0), [a generator class](hyp:F1),
[a magnitude bound](hyp:K), [a Lipschitz bound](hyp:L), [an intervention family](hyp:t),
[its averaging probability measure](hyp:muT), [an outcome objective](hyp:F),
[observed data](hyp:sample), [common simulation draws](hyp:draws),
[an entropic regularization parameter](hyp:lam), [a discrepancy tolerance](hyp:alpha),
[well-defined objectives for all candidates satisfying the regularity restrictions](hyp:hdefined),
and [an extended-real value](hyp:value), [the infimum condition equates that value
with the infimum of intervention-averaged objectives over those representations
whose empirical Sinkhorn divergence is within the tolerance](goal). -/
def EmpiricalValueIsInfimum {counts : Fin b → ℕ}
    (F0 : StructuralClass kind dims dag C) (F1 : GeneratorClass dims counts)
    (K L : ℝ≥0) {I : Type*} [MeasurableSpace I] (t : I → LawIntervention kind)
    (muT : Measure I) [IsProbabilityMeasure muT] (F : Joint kind → ℝ) {r m : ℕ}
    (sample : Fin r → Joint kind) (draws : Fin m → SimulationInput kind counts)
    (lam alpha : ℝ) (hdefined : empiricalObjectivesDefined (G := G) F0 F1 (restrictedCandidate K L) t muT F) (value : EReal) : Prop :=
  value = restrictedEmpiricalPIValue (G := G) F0 F1 K L t muT F sample draws lam alpha hdefined

-- @node: ass:pin-210
/-- For [a structural-function class](hyp:F0), [a generator class](hyp:F1),
[an intervention family](hyp:t), [its averaging probability measure](hyp:muT),
[an outcome objective](hyp:F), [observed data](hyp:sample),
[common simulation draws](hyp:draws), [an entropic regularization parameter](hyp:lam),
[a discrepancy tolerance](hyp:alpha), [well-defined objectives for every
representation in these classes](hyp:hdefined), and [an extended-real value](hyp:value),
[the empirical infimum condition equates that value with the infimum of
intervention-averaged objectives over representations whose empirical Sinkhorn
divergence from the data is within the tolerance](goal). -/
def EmpiricalValueInfimumReading {counts : Fin b → ℕ}
    (F0 : StructuralClass kind dims dag C) (F1 : GeneratorClass dims counts)
    {I : Type*} [MeasurableSpace I] (t : I → LawIntervention kind)
    (muT : Measure I) [IsProbabilityMeasure muT] (F : Joint kind → ℝ) {r m : ℕ}
    (sample : Fin r → Joint kind) (draws : Fin m → SimulationInput kind counts)
    (lam alpha : ℝ) (hdefined : empiricalObjectivesDefined (G := G) F0 F1 (fun _ => True) t muT F) (value : EReal) : Prop :=
  value = empiricalPIValue (G := G) F0 F1 t muT F sample draws lam alpha hdefined

-- @node: ass:pin-fix-9675bba5
/-- For [extended-real scores on finitely many ordered labels](hyp:score),
[the smallest-argmax condition says that whenever the selector returns a label](goal),
[its score is at least every other score](step:1) and [it is no larger than any
label with the same score](step:2). -/
def ArgmaxSmallestLabel {k : ℕ} (score : Fin k → EReal) : Prop :=
  ∀ j, firstArgmax score = some j → (∀ l, score l ≤ score j) ∧
    ∀ l, score l = score j → j ≤ l

-- @node: ass:bk-owner-8
/-- [The categorical tie convention requires that, for every finite number of
labels and every extended-real score function, any label returned by the selector
maximizes the score and is the smallest maximizing label](goal). -/
def CategoricalArgmaxTieSmallestLabel : Prop :=
  ∀ (k : ℕ) (score : Fin k → EReal), ArgmaxSmallestLabel score

-- @node: ass:pin-fix-9d74053b
/-- For [two tolerance sequences](hyp:eps,s) and [their respective comparison
sequences](hyp:a,b), [the asymptotic tolerance-order condition](goal) requires
[the first tolerance to be bounded in absolute value by a constant multiple of
its comparison sequence eventually](step:1) and [the same eventual bound for
the second tolerance and its comparison sequence](step:2). -/
def ToleranceOrdersAsymptotic (eps s a b : ℕ → ℝ) : Prop :=
  Asymptotics.IsBigO atTop eps a ∧ Asymptotics.IsBigO atTop s b

-- @node: ass:pin-fix-f66ad243
/-- For [a depth sequence](hyp:depth) and [an input dimension](hyp:din),
[the depth-expression convention requires the sequence to have the same
asymptotic order as the constant one plus the natural logarithm of that dimension](goal). -/
def DepthExpressionConvention (depth : ℕ → ℝ) (din : ℕ) : Prop :=
  Asymptotics.IsTheta atTop depth (fun _ => 1+Real.log din)

-- @node: ass:pin-fix-676b96c3
/-- For [fixed component counts in each block](hyp:counts), [their component
dimensions](hyp:dC), [sample-size-dependent component counts](hyp:countsN), and
[sample-size-dependent component dimensions](hyp:dCN), [the fixed-structure
condition requires the counts to equal the fixed counts at every sample size
and each corresponding component dimension to equal its fixed dimension](goal). -/
def FixedGeneratorComponentStructure (counts : Fin b → ℕ)
    (dC : ∀ j, Fin (counts j) → ℕ) (countsN : ℕ → Fin b → ℕ)
    (dCN : ∀ r j, Fin (countsN r j) → ℕ) : Prop :=
  ∃ hcounts : ∀ r, countsN r = counts,
    ∀ r j i, dCN r j i = dC j (Fin.cast (congrFun (hcounts r) j) i)

-- @node: ass:pin-fix-2fe04b0e
/-- For [a dimension](hyp:d) and [a sequence of spatial cell collections](hyp:collections),
[the dyadic-cell convention requires each collection to equal the dyadic cube
collection at that refinement level](goal). -/
def HolderCurveDyadicCellsReading (d : ℕ) (collections : ℕ → Set (Set (Fin d → ℝ))) : Prop :=
  ∀ r, collections r = dyadicCubeCollection d r

-- @node: ass:pin-fix-c778b424
/-- For [a dimension](hyp:d) and [a proposed reference measure](hyp:lambda),
[the cube-measure convention identifies that measure with Lebesgue measure
restricted to the unit cube](goal). -/
def CubeLebesgueReading (d : ℕ) (lambda : Measure (Fin d → ℝ)) : Prop := -- @realizes \lambda(reference cube Lebesgue measure)
  lambda = cubeLebesgue d

-- @node: ass:pin-fix-7a79e01d
/-- For [a dimension](hyp:d) and [time intervals indexed by refinement level
and cell position](hyp:intervals), [the interval convention identifies every
interval with the corresponding dyadic time cell](goal). -/
def HolderCurveIntervalsReading (d : ℕ) (intervals : ∀ r, Fin (2^(d*r)) → Set ℝ) : Prop :=
  ∀ r k, intervals r k = dyadicTimeCell d r k

-- @node: ass:pin-fix-2a1e7b01
/-- For [a dimension](hyp:d), [spatial construction cells indexed by cell words](hyp:cells),
and [a bijective ordering of those words at every refinement level](hyp:O),
[the interval-mass convention requires every ordered cell to have unit-cube
Lebesgue mass equal to two raised to minus the dimension times the level](goal). -/
def IntervalMassLebesgueReading (d : ℕ)
    (cells : ∀ r, CellWord d r → Set (Fin d → ℝ)) -- @realizes \mathcal{C}_n(carrier of the actual construction cell family)
    (O : ∀ r, Fin (2^(d*r)) ≃ CellWord d r) : Prop := -- @realizes O_n(bijection ordering the actual construction cells)
  ∀ r i, cubeLebesgue d (cells r (O r i)) =
    ENNReal.ofReal ((2:ℝ)^(-(d*r : ℤ))) -- @realizes \mathcal{C}_n(Lebesgue mass of each actual ordered construction cell)

-- @node: ass:pin-203
/-- For [category weights](hyp:p), [a gap threshold](hyp:delta), and [an event
in the space of noise vectors](hyp:E), [the gap-event convention says that this
event consists exactly of vectors for which some pair of distinct, increasingly
ordered labels has noise-plus-log-weight scores differing in absolute value by
less than the threshold](goal). -/
def GumbelGapEventReading {k : ℕ} (p : Fin k → ℝ) (delta : ℝ) (E : Set (Fin k → ℝ)) : Prop :=
  E = {g | ∃ i j, i < j ∧ |g i+Real.log (p i)-(g j+Real.log (p j))| < delta}

-- @node: ass:pin-185
/-- For [a canonical structural causal model](hyp:M), [a Lipschitz constant](hyp:L),
and [a magnitude-bound parameter](hyp:K), [the true-model regularity condition
requires every original structural function to be Lipschitz with that constant
on its complete structural domain](goal).

The magnitude-bound parameter does not affect this condition. -/
def LipschitzRefersToTrueModel (M : CanonicalSCM kind dims dag G C) (L K : ℝ≥0) : Prop :=
  TrueStructuralLipschitz M L K

-- @node: ass:pin-159
/-- For [a limiting parameter domain](hyp:ThetaInf), [a sequence of real-valued
constraint functions](hyp:gn), [a Lipschitz constant](hyp:L), and [an additive
slack sequence](hyp:tau), [the approximate Lipschitz condition bounds the absolute
difference of each constraint function at any two points of that domain by the
constant times their distance plus that function's slack](goal). -/
def ApproxLipschitzDomainReading {X : Type*} [MetricSpace X] (ThetaInf : Set X) (gn : ℕ → X → ℝ) (L : ℝ≥0) (tau : ℕ → ℝ) : Prop :=
  ApproxLipschitzConstraints ThetaInf gn L tau

-- @node: ass:pin-172
/-- For [a sequence of approximating parameter sets](hyp:Theta), [a limiting
parameter domain](hyp:ThetaInf), and [an approximation-error sequence](hyp:eps),
[the approximation condition requires the existence of a compact subset of the
limiting domain whose every point, at every index, lies within the corresponding
error of some point in the approximating set](goal). -/
def ApproximationQuantifierReading {X : Type*} [MetricSpace X] (Theta : ℕ → Set X) (ThetaInf : Set X) (eps : ℕ → ℝ) : Prop :=
  CompactSubsetApproximable Theta ThetaInf eps

-- @node: ass:pin-52
/-- For [a limiting parameter domain](hyp:ThetaInf), [a sequence of real-valued
constraint functions](hyp:gn), [a Lipschitz constant](hyp:L), and [an additive
slack sequence](hyp:tau), [the limiting-domain convention requires each function's
absolute difference at any two points of that domain to be at most the constant
times their distance plus the corresponding slack](goal). -/
def ApproxLipschitzThetaInfReading {X : Type*} [MetricSpace X]
    (ThetaInf : Set X) (gn : ℕ → X → ℝ) (L : ℝ≥0) (tau : ℕ → ℝ) : Prop :=
  ApproxLipschitzConstraints ThetaInf gn L tau

-- @node: ass:pin-207
/-- For [a class of vector-valued functions](hyp:F) and [a real magnitude
bound](hyp:K), [the uniform-bound condition requires a positive bound that
dominates the absolute value of every output coordinate of every function
at every input](goal). -/
def SupNormBoundReading {X : Type*} {d : ℕ} (F : Set (X → L1Vec d)) (K : ℝ) : Prop :=
  ClassUniformlyBounded F K

-- @node: ass:pin-181
/-- For [a structural causal model](hyp:M) and [its categorical mechanism weights](hyp:p),
[the conditional categorical-law convention](goal) requires [nonnegative weights
with positive total on each complete categorical structural domain](step:1),
[normalized weights evaluated at the random structural input to equal the
conditional category probabilities almost surely](step:2), and [the extended
logarithm of zero to be negative infinity](step:3). -/
def CategoricalLawConditionalReading (M : EuclideanSCM kind dims) (p : MechanismWeights M) : Prop :=
  CategoricalWeightsPositive M p ∧ categoricalConditionalLaw M p ∧ extendedLog 0 = ⊥

-- @node: ass:pin-182
/-- For [a structural causal model](hyp:M), [categorical propensity maps](hyp:p),
and [a common Lipschitz bound](hyp:L), [the propensity regularity condition requires
these maps to be Lipschitz on their full structural domains and their coordinates
to equal the conditional category probabilities almost surely](goal). -/
def PropensityLipschitzReading (M : EuclideanSCM kind dims) (p : MechanismWeights M) (L : ℝ≥0) : Prop :=
  CategoricalPropensityLipschitz M p L

-- @node: ass:pin-183
/-- For [a structural causal model](hyp:M), [the almost-sure boundedness condition
requires a positive finite bound on the absolute values of all observed coordinates
and all non-Gumbel latent block coordinates, almost surely under its latent law](goal). -/
def BoundednessAlmostSureReading (M : EuclideanSCM kind dims) : Prop :=
  ∃ K : ℝ, VariablesBoundedAt M K

-- @node: ass:pin-154
/-- For [two structural causal models](hyp:M,Mhat) and [a common bound](hyp:K),
[the joint boundedness condition requires that bound to be positive and to bound
every observed and non-Gumbel latent coordinate in absolute value almost surely
under each model's own latent law](goal). -/
def BothModelsBoundedReading (M Mhat : EuclideanSCM kind dims) (K : ℝ) : Prop :=
  AllVariablesNormBounded M Mhat K

-- @node: ass:pin-186
/-- For [a structural causal model](hyp:M), [the unit-cube convention identifies
every structural approximation domain with the closed cube whose coordinates
range from zero to one](goal). -/
def UnitCubeDomainReading (M : EuclideanSCM kind dims) : Prop :=
  ∀ i, structuralApproximationDomain M i =
    {x | ∀ j, x.ofLp j ∈ Set.Icc (0 : ℝ) 1}

-- @node: ass:pin-189
/-- For [a structural causal model](hyp:M), [the bidirected-edge convention says
that two nodes are adjacent exactly when they are distinct and some latent block
incident to the first is statistically dependent on some block incident to the
second, under the model's latent law](goal). -/
def BidirectedArrowReading (M : EuclideanSCM kind dims) : Prop :=
  ∀ i j, (causalGraph M).2.Adj i j ↔ i ≠ j ∧
    (∃ k : Fin b, k ∈ M.incidence i ∧ ∃ l : Fin b, l ∈ M.incidence j ∧
      ¬ ProbabilityTheory.IndepFun (blockProjection k) (blockProjection l) M.latentLaw)

-- @node: ass:pin-owner-1
/-- For [a canonical structural causal model](hyp:M) and [an admissible class of
structural mechanisms](hyp:F), [canonical-class membership requires each restricted
mechanism to belong to its designated class, without further restricting the latent law](goal). -/
def CanonicalClassArbitraryLatentReading (M : CanonicalSCM kind dims dag G C) (F : AdmissibleStructuralClass kind dims dag C) : Prop :=
  M ∈ canonicalClass F

-- @node: ass:pin-33
/-- For [a homeomorphism between two topological spaces](hyp:f), [the homeomorphism
condition](goal) requires [the map to be bijective](step:1), [the map to be
continuous](step:2), and [its inverse to be continuous](step:3). -/
def HomeomorphismReading {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ Y) : Prop :=
  Function.Bijective f ∧ Continuous f ∧ Continuous f.symm

-- @node: ass:pin-192
/-- For [a ReLU network with specified width and depth budgets](hyp:q), [the
architecture condition](goal) requires [exactly the budgeted number of hidden
layers](step:1) and [each hidden layer to have at most the budgeted width](step:2). -/
def ReLUArchitectureReading {din dout W L : ℕ} (q : ReLUNet din dout W L) : Prop :=
  q.hidden.length = L ∧ ∀ l ∈ q.hidden, l.output ≤ W

-- @node: ass:pin-owner-3
/-- For [a ReLU network](hyp:q), [a covering radius](hyp:eps), and [a set of
vectors](hyp:S), [the architecture and covering convention](goal) requires
[the network to have its prescribed hidden-layer count and width bound](step:1)
and [the strict covering number to equal the infimum of cardinalities of subsets
of the set whose open balls of that radius cover the set](step:2). -/
def ReLUWidthCoveringOwnerReading {din dout W L d : ℕ}
    (q : ReLUNet din dout W L) (eps : ℝ≥0∞) (S : Set (L1Vec d)) : Prop :=
  ReLUArchitectureReading q ∧
    strictCoveringNumber eps S =
      ⨅ C : {C : Set (L1Vec d) // C ⊆ S ∧
        ∀ x ∈ S, ∃ y ∈ C, edist x y < eps}, C.val.encard

-- @node: ass:pin-owner-4
/-- For [a ReLU network](hyp:q), [a covering radius](hyp:eps), and [a set of
vectors](hyp:S), [the covering-number convention requires the prescribed network
depth and width bounds and identifies the strict covering number with the infimum
of cardinalities of covers with centers in the set and distances strictly below
the radius](goal). -/
def CoveringNumberOwnerReading {din dout W L d : ℕ}
    (q : ReLUNet din dout W L) (eps : ℝ≥0∞) (S : Set (L1Vec d)) : Prop :=
  ReLUWidthCoveringOwnerReading q eps S

-- @node: ass:pin-208
/-- For [a neural causal model representation](hyp:R), [the categorical-noise
condition requires nonnegative mechanism weights with positive totals, the
corresponding normalized conditional category probabilities, categorical choices
by smallest-label maximization of log weights plus noise, and independent standard
Gumbel coordinates within each node's noise vector](goal). -/
def NCMCategoricalNoiseReading {counts : Fin b → ℕ} {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts} (R : NCMIn kind dims dag G C counts F0 F1) : Prop :=
  CategoricalGumbelArgmax R.canonical.toEuclideanSCM R.canonical.f

-- @node: ass:pin-209
/-- For [category weights](hyp:p), [component output vectors](hyp:V), and [an
output function of temperature and noise](hyp:output), [the mixing-layer condition
requires, whenever the weights form a probability vector](goal), [positive-temperature
outputs to be softmax-weighted component sums](step:1), [zero-temperature outputs
to be hard-selection component sums](step:2), [each hard-selection probability to
equal its category weight](step:3), and [soft weights to converge to hard weights
almost surely as positive temperature tends to zero](step:4). -/
def GumbelMixingLayerReading {k d : ℕ} (p : Fin k → ℝ)
    (V : Fin k → L1Vec d) (output : ℝ → (Fin k → ℝ) → L1Vec d) : Prop :=
  p ∈ stdSimplex ℝ (Fin k) →
    (∀ tau : ℝ, 0 < tau → ∀ g, output tau g =
      WithLp.toLp 1 (fun j => ∑ i, (V i).ofLp j * (softmaxWeights p tau g).ofLp i)) ∧ -- @realizes \hat{g}_3^\tau(layer output is the matrix of all component values times the soft weights)
    (∀ g, output 0 g = WithLp.toLp 1
      (fun j => ∑ i, (V i).ofLp j * (hardWeights p g).ofLp i)) ∧
    (∀ i, (gumbelHardLaw p) {x | x.ofLp i = 1} = ENNReal.ofReal (p i)) ∧
    ∀ᵐ g ∂gumbelInputs k, Tendsto (fun tau => softmaxWeights p tau g)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (hardWeights p g))

-- @node: ass:pin-194
/-- For [a structural-function class](hyp:F0), [a generator class](hyp:F1), and
[an unrestricted neural causal model representation](hyp:R), [the membership
condition](goal) requires [each raw structural function to belong to its designated
class](step:1) and [each block generator to belong to its designated class](step:2). -/
def NCMMembershipReading {counts : Fin b → ℕ}
    (F0 : StructuralClass kind dims dag C) (F1 : GeneratorClass dims counts)
    (R : NCMIn kind dims dag G C counts (fun _ => Set.univ) (fun _ => Set.univ)) : Prop :=
  (∀ i, R.rawStructural i ∈ F0 i) ∧ ∀ j, R.generator j ∈ F1 j

-- @node: ass:pin-197
/-- For [a reference canonical model](hyp:base), [a magnitude bound](hyp:K),
[a Lipschitz bound](hyp:L), [an intervention family](hyp:t), [its averaging
probability measure](hyp:muT), [an outcome objective](hyp:F), [well-defined
objectives for all feasible population models](hyp:hdefined), and [an extended-real
value](hyp:value), [the population-value condition identifies that value with
the infimum of intervention-averaged objectives over bounded Lipschitz models
with bounded latent blocks and zero observational Wasserstein distance from
the reference model](goal). -/
def PopulationValueReading (base : CanonicalSCM kind dims dag G C) (K L : ℝ≥0)
    {I : Type*} [MeasurableSpace I] (t : I → LawIntervention kind) (muT : Measure I)
    [IsProbabilityMeasure muT] (F : Joint kind → ℝ)
    (hdefined : populationObjectivesDefined base K L t muT F) (value : EReal) : Prop :=
  value = populationLowerBound base K L t muT F hdefined

-- @node: ass:pin-198
/-- For [an outcome objective](hyp:F), [an outcome node](hyp:Y), [the requirement
that this node be scalar](hyp:hY), [two intervention endpoints](hyp:t1,t2),
[their strict ordering](hyp:h), and [an averaging measure](hyp:muT), [the uniform
intervention condition](goal) requires [the objective to equal the designated
outcome coordinate at every joint value](step:1) and [the measure to be the
uniform probability law between the endpoints](step:2). -/
def UniformInterventionReading (F : Joint kind → ℝ)
    (Y : Fin n) (hY : valueDim (kind Y) = 1)
    (t1 t2 : ℝ) (h : t1 < t2) (muT : Measure ℝ) : Prop :=
  (∀ v, F v = v.ofLp ⟨Y, Fin.cast hY.symm ⟨0, Nat.zero_lt_succ 0⟩⟩) ∧ -- @realizes F(the fixed objective equals the designated scalar outcome coordinate)
    muT = uniformIntervention t1 t2 h -- @realizes \mu_T(the fixed uniform probability law on the intervention interval)

-- @node: ass:pin-199
/-- For [a structural causal model](hyp:M), [the maximum-dimension convention](goal)
identifies [its maximum latent dimension with the maximum block dimension](step:1),
[its maximum input dimension with the maximum structural input size](step:2),
and [its maximum output dimension with the maximum node output size](step:3),
using zero for a maximum over an empty index set. -/
def LatentDimMaxReading (M : EuclideanSCM kind dims) : Prop :=
  maxLatentDim M = Finset.univ.sup dims ∧
    maxInDim M = Finset.univ.sup (structuralInputSize M) ∧
    maxOutDim M = Finset.univ.sup (fun i => outputDim (kind i))

-- @node: ass:pin-201
/-- For [a canonical structural causal model](hyp:M), [the marginal-law condition
requires every latent block marginal to be a probability measure](goal). -/
def ParameterMarginalsReading (M : CanonicalSCM kind dims dag G C) : Prop :=
  ∀ j, IsProbabilityMeasure (M.blockLaw j : Measure (L1Vec (dims j)))

-- @node: ass:pin-211
/-- For [category weights](hyp:p), [the shared-noise condition requires, whenever
every weight is strictly positive](goal), [the positive-temperature softmax law
to be the image of the standard Gumbel input law under soft selection](step:1),
[the hard-selection law to be the image of the same input law under hard
selection](step:2), and [soft selections using one fixed noise draw to converge
almost surely to its hard selection as positive temperature tends to zero](step:3). -/
def GumbelSoftmaxSameDrawReading {k : ℕ} (p : Fin k → ℝ) : Prop :=
  (∀ j, 0 < p j) →
    (∀ tau : ℝ, 0 < tau → gumbelSoftmaxLaw p tau =
      (gumbelInputs k).map (softmaxWeights p tau)) ∧
    gumbelHardLaw p = (gumbelInputs k).map (hardWeights p) ∧
    ∀ᵐ g ∂gumbelInputs k, Tendsto (fun tau => softmaxWeights p tau g)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (hardWeights p g))

-- @node: ass:pin-fix-507a5848
/-- For [a component dimension](hyp:q), [a quantization count](hyp:n), [an integer
depth parameter](hyp:s), [a quantization scale](hyp:delta), and [a mesh size](hyp:mesh),
[the generator parameter choice](goal) requires [positive dimension](step:1),
[a count of at least two](step:2), [depth one](step:3), [the scale to be the
reciprocal of the ceiling of the square root of the dimension times one plus
the dimension times the count times one less than the count](step:4), and
[the mesh to equal the scale divided by the count](step:5). -/
def PerekrestenkoParameterChoiceReading (q n s : ℕ) (delta mesh : ℝ) : Prop := -- @realizes s(natural-number depth parameter; fixed to one below)
  0 < q ∧ 2 ≤ n ∧ s = 1 ∧ -- @realizes s(fixed integer depth s = 1, distinct from delta and delta / n)
    delta = (⌈Real.sqrt q * (q + 1) * n * ((n : ℝ) - 1)⌉₊ : ℝ)⁻¹ ∧
    mesh = delta / n

-- @node: ass:pin-fix-c514425b
/-- For [dimension-dependent width constants](hyp:A), [clipped-network widths
indexed by dimension and quantization count](hyp:clippedWidth), and [refinement
integers indexed by dimension and width budget](hyp:refinement), [the refinement
condition requires, in every positive dimension, a constant at least one, clipped
width at most that constant times the count raised to the dimension for counts
at least two, and, for budgets at least the constant times two raised to the
dimension, a refinement equal to the natural-number floor of the dimension-th
root of the budget divided by the constant and at least two](goal). -/
def PerekrestenkoRefinementIntegerReading (A : ℕ → ℝ)
    (clippedWidth : ℕ → ℕ → ℕ) (refinement : ℕ → ℕ → ℕ) : Prop :=
  ∀ q : ℕ, 0 < q → 1 ≤ A q ∧
    (∀ n : ℕ, 2 ≤ n → (clippedWidth q n : ℝ) ≤ A q * (n : ℝ)^q) ∧
    ∀ W : ℕ, A q * (2 : ℝ)^q ≤ W →
      refinement q W = ⌊((W : ℝ) / A q) ^ (1 / (q : ℝ))⌋₊ ∧
      2 ≤ refinement q W

-- @node: ass:pin-fix-73abef8c
/-- For [a canonical model](hyp:M), [a Lipschitz bound, magnitude bound, and
truncation radius](hyp:L,K,R), [a node](hyp:i), [a target mechanism](hyp:f),
[a depth-indexed approximating family](hyp:fhat), [a depth-indexed ReLU network
family with the prescribed width and four reserved layers](hyp:q), [a box
radius](hyp:B), [two error constants](hyp:Cᵢ,A), [a depth threshold](hyp:N), and
[an error sequence](hyp:eps), [the projected approximation condition](goal)
requires [positive structural input dimension](step:1), [the box radius to equal
the model's prescribed approximation radius](step:2), and [a certificate that
the networks approximate the structural interpolant with these constants above
the threshold, such that at every such depth the error equals the second constant
times depth raised to minus two divided by input dimension, the approximant is
the certified structural approximation, and its coordinates are the network
output after input clipping, floored at that error for categorical nodes](step:3). -/
def ProjectedFlooredApproximantReading
    (M : CanonicalSCM kind dims dag G C) (L K R : ℝ≥0) (i : Fin n)
    (f : L1Vec (structuralInputSize M.toEuclideanSCM i) → L1Vec (outputDim (kind i)))
    (fhat : ℕ → L1Vec (structuralInputSize M.toEuclideanSCM i) → L1Vec (outputDim (kind i)))
    (q : ∀ ℓ : ℕ, ReLUNet (structuralInputSize M.toEuclideanSCM i) (outputDim (kind i))
      (outputDim (kind i) * (2 * structuralInputSize M.toEuclideanSCM i + 10)) (ℓ - 4))
    (B : ℝ≥0) (Cᵢ A : ℝ) (N : ℕ) (eps : ℕ → ℝ) : Prop :=
  0 < structuralInputSize M.toEuclideanSCM i ∧
    B = structuralApproximationBox M L K R ∧
    ∃ hchosen : StructuralApproximantWitness M L K R i f q Cᵢ A N,
      ∀ L0 : ℕ, ∀ hbudget : N ≤ L0,
        eps L0 = A * (L0 : ℝ)^(-(2 : ℝ) / structuralInputSize M.toEuclideanSCM i) ∧
        fhat L0 = structuralApproximant M L K R i f q Cᵢ A N hchosen L0 (fun _ => hbudget) ∧
        ∀ x j, (fhat L0 x).ofLp j =
          if (kind i).isRight then max (eps L0) (((q L0).eval (clipBox B x)).ofLp j)
          else ((q L0).eval (clipBox B x)).ofLp j

-- @node: ass:pin-fix-bbf1c78a
/-- For [a mechanism with no input coordinates](hyp:f) and [its proposed
approximant](hyp:fhat), [the zero-input convention requires the approximant
to equal the original constant function exactly](goal). -/
def ZeroInputExactApproximantReading {dout : ℕ}
    (f fhat : L1Vec 0 → L1Vec dout) : Prop :=
  fhat = f

-- @node: ass:pin-fix-8429b12c
/-- For [component dimensions](hyp:dC), [width and depth budgets for the first
and second network stages](hyp:W1,L1,W2,L2), [a temperature](hyp:tau), and [a
proposed latent-generator class](hyp:F1), [the shared-temperature convention
identifies that class with exactly the evaluation functions of three-part
generators having those component dimensions, budgets, and Gumbel-softmax
temperature](goal). -/
def DeepNNSharedTemperatureReading {N d : ℕ} (dC : Fin N → ℕ)
    (W1 L1 W2 L2 : ℕ) (tau : ℝ)
    (F1 : Set (((Fin N → ℝ) × (Fin N → ℝ)) → L1Vec d)) : Prop :=
  F1 = {g | ∃ q : ThreePartGenerator N d dC W1 L1 W2 L2 tau, g = q.eval}


-- @node: ass:pin-187
/-- For [a common magnitude bound](hyp:K), [an intervention index domain](hyp:domain),
[an intervention family](hyp:t), [an averaging measure](hyp:muT), [sample-size-indexed
empirical model classes](hyp:empirical), and [a population model class](hyp:population),
[the optimization bound condition](goal) requires [all empirical candidates to
have observed and non-Gumbel latent coordinates bounded almost surely by this
positive bound](step:1), [the same boundedness for all population candidates](step:2),
[every categorical node's category count to be at most the bound](step:3), and
[every assigned intervention coordinate on the domain to be bounded in absolute
value by the bound](step:4).

The averaging measure imposes no additional restriction in this condition. -/
def OptimizationClassBoundScopeReading (K : ℝ≥0) {I : Type*} [MeasurableSpace I]
    (domain : Set I) (t : I → LawIntervention kind) (muT : Measure I)
    (empirical : ℕ → Set (EuclideanSCM kind dims))
    (population : Set (EuclideanSCM kind dims)) : Prop :=
  (∀ r M, M ∈ empirical r → VariablesBoundedAt M K) ∧
    (∀ M, M ∈ population → VariablesBoundedAt M K) ∧
    (∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ K) ∧
    (∀ s ∈ domain, ∀ i v, (t s).val i = some v → ∀ j, |v.ofLp j| ≤ K)

-- @node: ass:pin-188
/-- For [a common coordinate bound](hyp:K), [an intervention index domain](hyp:domain),
[an intervention family](hyp:t), [an averaging measure](hyp:muT), [sample-size-indexed
empirical model classes](hyp:empirical), and [a population model class](hyp:population),
[the rate bound condition](goal) requires [every empirical model's observed and
non-Gumbel latent coordinates to be bounded almost surely by this positive
bound](step:1), [the same coordinate bound for every population model](step:2),
[category counts no greater than the bound](step:3), and [absolute values of
assigned intervention coordinates no greater than the bound throughout the
domain](step:4).

The averaging measure imposes no additional restriction in this condition. -/
def RateClassBoundSupNormReading (K : ℝ≥0) {I : Type*} [MeasurableSpace I]
    (domain : Set I) (t : I → LawIntervention kind) (muT : Measure I)
    (empirical : ℕ → Set (EuclideanSCM kind dims))
    (population : Set (EuclideanSCM kind dims)) : Prop :=
  (∀ r M, M ∈ empirical r → VariablesBoundedAt M K) ∧
    (∀ M, M ∈ population → VariablesBoundedAt M K) ∧
    (∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ K) ∧
    (∀ s ∈ domain, ∀ i v, (t s).val i = some v → ∀ j, |v.ofLp j| ≤ K)

-- @node: ass:pin-190
/-- For [a canonical structural causal model](hyp:M), [the zero-propensity
convention](goal) requires [each categorical mechanism's output to be a
nonnegative probability vector throughout its full structural domain](step:1)
and [the extended logarithm of zero to be negative infinity](step:2). -/
def CanonicalZeroPropensityReading (M : CanonicalSCM kind dims dag G C) : Prop :=
  (∀ i k, kind i = Sum.inr k → ∀ x ∈ M.domain i none,
    (M.f i x).ofLp ∈ stdSimplex ℝ (Fin (outputDim (kind i)))) ∧
    extendedLog 0 = ⊥

-- @node: ass:pin-196
/-- For [component dimensions](hyp:dC), [width and depth budgets for the two
network stages](hyp:W1,L1,W2,L2), [a Gumbel-softmax temperature](hyp:tau), and
[a clipping bound](hyp:K), [the truncation convention](goal) requires [the clipped
generator class to consist exactly of three-part generator outputs clipped after
evaluation](step:1) and [each clipped coordinate to equal the maximum of minus
the bound and the minimum of the original coordinate and the bound](step:2). -/
def TruncationClippingReading {N d : ℕ} (dC : Fin N → ℕ)
    (W1 L1 W2 L2 : ℕ) (tau K : ℝ) : Prop :=
  clippedGeneratorClass dC W1 L1 W2 L2 tau K =
    {g | ∃ q : ThreePartGenerator N d dC W1 L1 W2 L2 tau, g = truncK K ∘ q.eval} ∧
    ∀ (x : L1Vec d) j, (truncK K x).ofLp j = max (-K) (min (x.ofLp j) K)

-- @node: ass:pin-fix-419eb8e3
/-- [The deep causal network width condition](goal) requires [the structural
network width multiplier to be positive](step:1), [the first generator stage's
width multiplier to be positive](step:2), and [the second generator stage's width
multiplier to be positive](step:3). -/
def DeepNCMAbsoluteWidthReading : Prop :=
  0 < deepStructuralWidthFactor ∧ 0 < deepFirstWidthFactor ∧ 0 < deepSecondWidthFactor

-- @node: ass:pin-fix-43f1bb71
/-- For [latent block probability laws](hyp:blockLaw), [component counts](hyp:counts),
[component sets in each block](hyp:sets), [their chart dimensions](hyp:dC), and
[a common chart regularity bound](hyp:Lchart), [the latent-law condition](goal)
requires [each block law to have the specified finite support components](step:1),
[those components to admit Lipschitz homeomorphic cube charts with the given
dimensions and bound](step:2), [each component's conditional law to satisfy
lower-bound domination in its chart](step:3), and [each such conditional law's
pullback to give zero mass to the cube boundary](step:4). -/
def DeepNNLatentLawPremisesReading
    (blockLaw : ∀ j, ProbabilityMeasure (L1Vec (dims j)))
    (counts : Fin b → ℕ) (sets : ∀ j, Fin (counts j) → Set (L1Vec (dims j)))
    (dC : ∀ j, Fin (counts j) → ℕ) (Lchart : ℝ≥0) : Prop :=
  (∀ j, SupportFiniteComponents (blockLaw j : Measure _) (sets j)) ∧
    (∀ j, ComponentsLipschitzHomeomorphic (sets j) (dC j) Lchart) ∧
    (∀ j i, LowerBoundDomination (d := dC j i)
      (ProbabilityTheory.cond (blockLaw j : Measure _) (sets j i)) (sets j i) Lchart) ∧
    ∀ j i, PullbackVanishesOnBoundary (d := dC j i)
      (ProbabilityTheory.cond (blockLaw j : Measure _) (sets j i)) (sets j i) Lchart

-- @node: ass:pin-fix-8cc0dba5
/-- For [a dimension](hyp:d) and [construction cells indexed by level and cell
word](hyp:cells), [the closed-box partition condition](goal) requires [each cell
to be the carrier of a closed coordinate box, possibly degenerate](step:1) and
[the union of the cells at every level to equal the closed unit cube](step:2). -/
def PartitionClosedBoxCellsReading (d : ℕ)
    (cells : ∀ r, CellWord d r → Set (Fin d → ℝ)) : Prop :=
  (∀ r w, ∃ box : Box d, cells r w = box.carrier) ∧
    ∀ r, (⋃ w, cells r w) = {x | ∀ j, x j ∈ Set.Icc (0 : ℝ) 1}

-- @node: ass:pin-fix-99ac9bb3
/-- For [a dimension](hyp:d) and [construction cells indexed by level and cell
word](hyp:cells), [the disjoint-interior condition requires any two unequal cell
sets at the same level to have disjoint interiors in the ambient Euclidean space](goal). -/
def PartitionInteriorsDisjointReading (d : ℕ)
    (cells : ∀ r, CellWord d r → Set (Fin d → ℝ)) : Prop :=
  ∀ r (w w' : CellWord d r), cells r w ≠ cells r w' →
    Disjoint (interior (cells r w)) (interior (cells r w'))

-- @node: ass:pin-fix-db6ed772
/-- [The generator width condition](goal) requires [the first network stage's
width multiplier to be positive](step:1) and [the second network stage's width
multiplier to be positive](step:2). -/
def DeepGeneratorAbsoluteWidthReading : Prop :=
  0 < deepFirstWidthFactor ∧ 0 < deepSecondWidthFactor

end
end Papers.TbsNeuralCausalPi
