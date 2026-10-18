module
public import Papers.TbsNeuralCausalPi.Setup.SCM
public import Mathlib.Data.List.Chain
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Data.EReal.Basic
/-! # ReLU networks and generator layers
Hidden layers apply coordinatewise ReLU; the output layer is affine.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
open MeasureTheory
open scoped ENNReal NNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The [universal width multiplier for structural approximation](goal) is twelve. -/
def deepStructuralWidthFactor : ℕ := 12
/-- The [universal width multiplier for first generator blocks](goal) is twelve. -/
def deepFirstWidthFactor : ℕ := 12
/-- The [universal width multiplier for clipped second generator blocks](goal) is thirteen. -/
def deepSecondWidthFactor : ℕ := 13

/-- An [affine layer](goal) consists of input and output dimensions, a real weight matrix,
and a real bias vector. -/
abbrev AffineLayer := Σ a : ℕ, Σ b : ℕ, (Fin b → Fin a → ℝ) × (Fin b → ℝ)
/-- For [an affine layer](hyp:l), its [input dimension](goal) is the number of input coordinates. -/
def AffineLayer.input (l : AffineLayer) : ℕ := l.1
/-- For [an affine layer](hyp:l), its [output dimension](goal) is the number of output coordinates. -/
def AffineLayer.output (l : AffineLayer) : ℕ := l.2.1
/-- Applying [an affine layer](hyp:l) to [an input sequence](hyp:x) gives
[the matrix-weighted input plus bias on the output coordinates, and zero elsewhere](goal). -/
def AffineLayer.apply (l : AffineLayer) (x : ℕ → ℝ) : ℕ → ℝ :=
  fun j => if h : j < l.output then
    (∑ i : Fin l.input, l.2.2.1 ⟨j, h⟩ i * x i.val) + l.2.2.2 ⟨j, h⟩ else 0

/-- For [an affine layer](hyp:l) and [an input sequence](hyp:x), the
[ReLU layer output](goal) replaces each negative affine output by zero. -/
def reluLayer (l : AffineLayer) (x : ℕ → ℝ) : ℕ → ℝ :=
  fun j => max 0 (l.apply x j)
/-- Given [an initial input dimension](hyp:din) and [a list of affine layers](hyp:ls),
the [final width](goal) is the last layer's output dimension, or the initial dimension
when the list is empty. -/
def finalWidth (din : ℕ) (ls : List AffineLayer) : ℕ :=
  ((ls.getLast?).map AffineLayer.output).getD din

-- @node: def:relu-networks
/-- A [ReLU network](goal) with [input dimension](hyp:din), [output dimension](hyp:dout),
[hidden width bound](hyp:W), and [exact hidden depth](hyp:L) stores compatible affine
hidden layers followed by ReLU, together with an unrestricted affine output layer. -/
structure ReLUNet (din dout W L : ℕ) where -- @realizes \mathcal{NN}(hidden affine layers followed by ReLU and a signed affine output)
  hidden : List AffineLayer -- @realizes \mathcal{NN}(finite affine hidden-layer data)
  depth : hidden.length = L -- @realizes L(exactly L hidden layers)
  widths : ∀ l ∈ hidden, l.output ≤ W -- @realizes W(width budget)
  firstInput : ∀ l, hidden.head? = some l → l.input = din
  compatible : hidden.IsChain (fun l l' => l.output = l'.input)
  outputWeight : Fin dout → Fin (finalWidth din hidden) → ℝ
  outputBias : Fin dout → ℝ

-- @env: S2
variable {din dout W L : ℕ}
/-- For [a ReLU network](hyp:q) with [input dimension](hyp:din), [output dimension](hyp:dout),
[width bound](hyp:W), and [hidden depth](hyp:L), its [value at an input vector](goal)
is obtained by [zero-padding that input vector](hyp:x) [to form the initial sequence](step:1),
[applying the hidden affine and ReLU layers in order](step:2), and
[applying the final affine output layer](step:3). -/
def ReLUNet.eval (q : ReLUNet din dout W L) (x : L1Vec din) : L1Vec dout :=
  let input : ℕ → ℝ := fun j => if h : j < din then x.ofLp ⟨j, h⟩ else 0
  let hidden := q.hidden.foldl (fun z l => reluLayer l z) input
  WithLp.toLp 1 (fun j => (∑ i, q.outputWeight j i * hidden i.val) + q.outputBias j)
/-- For [input dimension](hyp:din), [output dimension](hyp:dout), [width bound](hyp:W),
and [hidden depth](hyp:L), the [neural function class](goal) consists of all functions
represented by ReLU networks with those dimensions and budgets. -/
def NN (din dout W L : ℕ) : Set (L1Vec din → L1Vec dout) :=
  Set.range (ReLUNet.eval (din := din) (dout := dout) (W := W) (L := L))
/-- For [a real clipping level](hyp:K) and [a vector](hyp:x), the [truncated vector](goal)
is obtained coordinatewise by first taking the minimum with the level and then the
maximum with its negative. -/
def truncK {d : ℕ} (K : ℝ) (x : L1Vec d) : L1Vec d :=
  WithLp.toLp 1 (fun j => max (-K) (min (x.ofLp j) K))

-- @node: def:truncated-neural-class
/-- A [Lipschitz network equipped for truncation](goal), with [input dimension](hyp:din),
[output dimension](hyp:dout), [width bound](hyp:W), [hidden depth](hyp:L),
[Lipschitz bound](hyp:Lf), and [clipping level](hyp:K), stores a ReLU network whose
unclipped evaluation satisfies that Lipschitz bound. -/
structure TruncatedLipNet (din dout W L : ℕ) (Lf : ℝ≥0) (K : ℝ) where -- @realizes \mathcal{NN}^{L_f,K}(ReLU network and the intrinsic Lipschitz bound before clipping)
  network : ReLUNet din dout W L
  lipschitz : LipschitzWith Lf network.eval -- @realizes \mathcal{NN}^{L_f,K}(Lip bound)
/-- For [a Lipschitz network equipped for truncation](hyp:q) with [input dimension](hyp:din),
[output dimension](hyp:dout), [width bound](hyp:W), and [hidden depth](hyp:L), its
[evaluation function](goal) clips each coordinate of the underlying network's output
at the designated level. -/
def TruncatedLipNet.eval {Lf : ℝ≥0} {K : ℝ}
    (q : TruncatedLipNet din dout W L Lf K) : L1Vec din → L1Vec dout :=
  truncK K ∘ q.network.eval

/-- For [component weights](hyp:p), [a temperature](hyp:tau), and [additive score shocks](hyp:G),
the [softmax weight vector](goal) normalizes the exponentials of log weights plus shocks,
divided by temperature; components with zero weight contribute zero to numerator and denominator. -/
def softmaxWeights {n : ℕ} (p : Fin n → ℝ) (tau : ℝ) (G : Fin n → ℝ) : L1Vec n := -- @realizes X^\tau(coordinate exponential formula at a positive temperature in every consumer) -- @realizes \tau(coordinate exponential formula at a positive temperature in every consumer)
  WithLp.toLp 1 (fun k => (if p k = 0 then 0 else Real.exp ((Real.log (p k) + G k) / tau)) /
    ∑ j, if p j = 0 then 0 else Real.exp ((Real.log (p j) + G j) / tau))
/-- For [component weights](hyp:p) and [additive score shocks](hyp:G), the
[hard selector vector](goal) puts one at the smallest label maximizing extended log
weight plus shock and zero elsewhere; it is the empty vector if there are no labels. -/
def hardWeights {n : ℕ} (p : Fin n → ℝ) (G : Fin n → ℝ) : L1Vec n := -- @realizes X^0(one-hot vector at the smallest maximizing label)
  WithLp.toLp 1 (fun k => if firstArgmax (fun j => extendedLog (p j) + (G j : EReal)) = some k
    then 1 else 0)

-- @node: def:gumbel-softmax-layer
/-- Given [component output vectors](hyp:V), [component weights](hyp:p),
[a temperature](hyp:tau), and [score shocks](hyp:G), the [mixture output](goal)
is the weighted sum of the component vectors, using the hard selector at zero
temperature and softmax weights otherwise. -/
def gumbelSoftmaxMix {n d : ℕ} (V : Fin n → L1Vec d) (p : Fin n → ℝ) -- @realizes \hat{g}_3^\tau(matrix of component values times soft or hard selector weights)
    (tau : ℝ) (G : Fin n → ℝ) : L1Vec d :=
  WithLp.toLp 1 (fun j => ∑ k, (V k).ofLp j *
    (if tau = 0 then hardWeights p G else softmaxWeights p tau G).ofLp k)

-- @node: def:generator-architecture
/-- A [three-part generator](goal) with [a given number of components](hyp:n),
[ambient output dimension](hyp:d), [component intermediate dimensions](hyp:dC),
[first-block width](hyp:W1) and [depth](hyp:L1), [second-block width](hyp:W2) and
[depth](hyp:L2), and [temperature](hyp:tau) stores separate scalar-to-component and
component-to-output ReLU networks, strictly positive mixing weights summing to one,
and a certificate that the temperature is positive. -/
structure ThreePartGenerator (n d : ℕ) (dC : Fin n → ℕ) (W1 L1 W2 L2 : ℕ) (tau : ℝ) where -- @realizes \mathcal{NN}(W_1,L_1,W_2,L_2,\tau)(finite separable component architecture at the supplied width, depth and temperature budgets) -- @realizes W_1(finite separable component architecture at the supplied width, depth and temperature budgets) -- @realizes W_2(finite separable component architecture at the supplied width, depth and temperature budgets) -- @realizes L_1(finite separable component architecture at the supplied width, depth and temperature budgets) -- @realizes L_2(finite separable component architecture at the supplied width, depth and temperature budgets) -- @realizes \hat{g}(finite separable component architecture at the supplied width, depth and temperature budgets) -- @realizes N_C(finite separable component architecture at the supplied width, depth and temperature budgets) -- @realizes d_i^C(finite separable component architecture at the supplied width, depth and temperature budgets)
  g1 : ∀ i, ReLUNet 1 (dC i) W1 L1 -- @realizes \hat{g}_1^i(carrier ReLUNet 1 (dC i) W1 L1; eval restricted to scalar cube inputs) -- @realizes \hat{g}_1(separate one-input component networks) -- @realizes \hat{g}_1^{i,j}(one-input component networks and their output coordinates)
  g2 : ∀ i, ReLUNet (dC i) d W2 L2 -- @realizes \hat{g}_2^{i,j}(component cube-to-ambient networks and their coordinates)
  p : Fin n → ℝ -- @realizes p_i(mixing weights)
  weights : p ∈ stdSimplex ℝ (Fin n) -- @realizes p_i(nonnegative weights of total mass one)
  positiveWeights : ∀ i, 0 < p i -- @realizes p_i(each mixing mass is positive)
  temperature : 0 < tau -- @realizes \tau(positive temperature)
/-- For [a three-part generator](hyp:q), [a component label](hyp:i), and
[a scalar unit-cube input](hyp:u), the [first-block output](goal) is the value of
that component's first network at that input. -/
def ThreePartGenerator.firstBlock {n d : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau)
    (i : Fin n) (u : unitCube 1) : L1Vec (dC i) := -- @realizes \hat{g}_1^i(scalar unit-cube map into the component Euclidean space)
  (q.g1 i).eval u.val

/-- For [a three-part generator](hyp:q) and [paired scalar component inputs and mixing shocks](hyp:z),
the [generator output](goal) passes each scalar input through its two component networks,
then mixes the resulting vectors using the generator's weights, temperature, and supplied shocks. -/
def ThreePartGenerator.eval {n d : ℕ} {dC : Fin n → ℕ} {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) : L1Vec d := -- @realizes U_i(scalar uniform input z.1 i under generatorInputLaw)
  gumbelSoftmaxMix (fun i => (q.g2 i).eval ((q.g1 i).eval (WithLp.toLp 1 (fun _ => z.1 i)))) q.p
    tau z.2

/-- For [a three-part generator](hyp:q), [mixing shocks](hyp:G), and
[a point in the unit cube](hyp:z), the [cube-domain generator output](goal)
feeds the cube coordinates through the component networks and the shocks through the mixing layer. -/
def ThreePartGenerator.cubeMap {n d : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau)
    (G : Fin n → ℝ) (z : unitCube n) : L1Vec d := -- @realizes \hat{g}(random map on the closed uniform-input cube, with independent Gumbel mixing coordinates)
  q.eval (z.val.ofLp, G)

/-- For [a three-part generator](hyp:q) and [one unit-cube input for each component](hyp:x),
the [second-block output family](goal) evaluates each component's second network at its own input. -/
def ThreePartGenerator.secondBlock {n d : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau)
    (x : ∀ i, unitCube (dC i)) : Fin n → L1Vec d := -- @realizes \hat{g}_2(product of component unit cubes mapped by the separate second networks)
  fun i => (q.g2 i).eval (x i).val

/-- For [a number of coordinates](hyp:n), the [Gumbel input law](goal) is the product
of that many independent standard Gumbel laws. -/
def gumbelInputs (n : ℕ) : Measure (Fin n → ℝ) := Measure.pi (fun _ => gumbelLaw) -- @realizes G_k(product of fixed standard Gumbel coordinate laws)

/-- Given [component weights](hyp:p) and [a temperature](hyp:tau), the
[Gumbel-softmax law](goal) is the distribution of the softmax vector obtained from
independent standard Gumbel shocks. -/
def gumbelSoftmaxLaw {n : ℕ} (p : Fin n → ℝ) (tau : ℝ) : Measure (L1Vec n) := -- @realizes \mu^\tau(soft selector push-forward law of the product Gumbel inputs)
  (gumbelInputs n).map (softmaxWeights p tau)
/-- Given [component weights](hyp:p), the [hard Gumbel selector law](goal) is the
distribution of the hard selector vector obtained from independent standard Gumbel shocks. -/
def gumbelHardLaw {n : ℕ} (p : Fin n → ℝ) : Measure (L1Vec n) := -- @realizes \mu^0(hard selector law on the simplex vertices)
  (gumbelInputs n).map (hardWeights p)
/-- The [list of zero-width hidden layers for an input dimension and depth](goal)
is [empty at depth zero](step:1); [at positive depth, its first layer accepts the
given input dimension and has zero outputs, followed by zero-input layers for the remaining depth](step:2). -/
def zeroHidden : ℕ → ℕ → List AffineLayer
  | _, 0 => []
  | din, L+1 => ⟨din, 0, (fun _ _ => 0), (fun _ => 0)⟩ :: zeroHidden 0 L

-- @node: zeroHidden_length
/-- [The list of zero-width hidden layers has exactly the requested depth](goal). -/
lemma zeroHidden_length (din L : ℕ) : (zeroHidden din L).length = L := by
  induction L generalizing din with
  | zero => rfl
  | succ L ih => simp only [zeroHidden, List.length_cons, ih]
-- @node: zeroHidden_widths
/-- [Every layer in the zero-width hidden-layer list satisfies any natural-number width bound](goal). -/
lemma zeroHidden_widths (din L W : ℕ) :
    ∀ l ∈ zeroHidden din L, l.output ≤ W := by
  induction L generalizing din with
  | zero => simp only [zeroHidden, List.not_mem_nil, false_implies, implies_true]
  | succ L ih =>
      intro l hl
      rcases List.mem_cons.mp hl with rfl | hl
      · exact Nat.zero_le W
      · exact ih 0 l hl
-- @node: zeroHidden_firstInput
/-- [Any first layer of the zero-width hidden-layer list has the prescribed input dimension](goal). -/
lemma zeroHidden_firstInput (din L : ℕ) :
    ∀ l, (zeroHidden din L).head? = some l → l.input = din := by
  cases L with
  | zero => simp [zeroHidden]
  | succ L =>
      intro l hl
      have heq : (⟨din, 0, (fun _ _ => 0), (fun _ => 0)⟩ : AffineLayer) = l :=
        Option.some.inj hl
      subst l
      rfl
-- @node: zeroHidden_compatible
/-- [Successive layers of the zero-width hidden-layer list have matching output and input dimensions](goal). -/
lemma zeroHidden_compatible (din L : ℕ) :
    (zeroHidden din L).IsChain (fun l l' => l.output = l'.input) := by
  induction L generalizing din with
  | zero => exact List.isChain_nil
  | succ L ih =>
      apply (ih 0).cons
      intro l hl
      exact (zeroHidden_firstInput 0 L l hl).symm

/-- For [input dimension](hyp:din), [output dimension](hyp:dout), [width bound](hyp:W),
and [hidden depth](hyp:L), the [zero network](goal) uses zero-width hidden layers
and zero output weights and biases, so its output is identically zero. -/
def zeroNet (din dout W L : ℕ) : ReLUNet din dout W L :=
  { hidden := zeroHidden din L, depth := zeroHidden_length din L,
    widths := zeroHidden_widths din L W,
    firstInput := zeroHidden_firstInput din L,
    compatible := zeroHidden_compatible din L,
    outputWeight := fun _ _ => 0, outputBias := fun _ => 0 }
/-- For [any input dimension](hyp:din), [output dimension](hyp:dout),
[width bound](hyp:W), and [hidden depth](hyp:L), the zero network supplies
[an inhabitant of the corresponding ReLU network type](goal). -/
instance reluNetNonempty : Nonempty (ReLUNet din dout W L) := ⟨zeroNet din dout W L⟩

/-- For [a nonnegative box radius](hyp:B) and [a vector](hyp:x), the
[box projection](goal) clips every coordinate to the symmetric interval with that radius,
using a difference of two ReLU terms. -/
def clipBox {d : ℕ} (B : ℝ≥0) (x : L1Vec d) : L1Vec d :=
  WithLp.toLp 1 (fun j => -(B : ℝ) + max (x.ofLp j + B) 0 - max (x.ofLp j - B) 0)

section StructuralApproximation
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)} {C : Fin b → Set (Fin n)}

/-- For [a canonical structural causal model](hyp:M) and [a node](hyp:i), the
[reference structural input](goal) assigns zero to real-valued parent and latent
coordinates and one to categorical parent coordinates. -/
def structuralApproximationAnchor (M : CanonicalSCM kind dims dag G C) (i : Fin n) :
    StructuralInput kind dims dag (canonicalIncidence C) i :=
  WithLp.toLp 1 (fun j => match j with
    | .inl ⟨p, _⟩ => if (kind p.val).isRight then 1 else 0
    | .inr _ => 0)

/-- For [a canonical structural causal model](hyp:M), [a nonnegative regularity bound](hyp:L),
[a nonnegative mechanism bound](hyp:K), and [a nonnegative input radius](hyp:R), the
[structural approximation box radius](goal) is formed by [taking the maximum of one,
the two radius and mechanism bounds, all category counts, and the nonnegative parts of
the norms of continuous mechanisms at their reference inputs](step:1), then
[multiplying this maximum by one plus twice the regularity bound times the largest
structural input dimension, raised to the number of nodes](step:2). -/
def structuralApproximationBox (M : CanonicalSCM kind dims dag G C) (L K R : ℝ≥0) : ℝ≥0 :=
  let B₀ := max (max (max 1 R) K) (Finset.univ.sup (fun i =>
    match kind i with
    | .inr k => (k : ℝ≥0)
    | .inl _ => Real.toNNReal ‖(M.f i (structuralApproximationAnchor M i)).ofLp‖))
  B₀ * (1 + 2 * L * maxInDim M.toEuclideanSCM)^n

/-- For [a canonical structural causal model](hyp:M), [a node](hyp:i), and
[a vector of structural input coordinates](hyp:x), the [interpolated mechanism value](goal)
is constructed by [recording each categorical parent's category count, with zero for
other coordinates](step:1), [choosing lower labels by clamping inputs between one and
their category counts, rounding down, and capping at one below the count](step:2),
[subtracting these lower labels from the clamped coordinates to obtain interpolation
fractions](step:3), and [summing mechanism values at neighboring labels with product
interpolation weights, preserving real inputs and fixing singleton labels at one](step:4). -/
def structuralInterpolant (M : CanonicalSCM kind dims dag G C) (i : Fin n)
    (x : L1Vec (structuralInputSize M.toEuclideanSCM i)) : L1Vec (outputDim (kind i)) :=
  let count : Fin (structuralInputSize M.toEuclideanSCM i) → ℕ := fun r =>
    match (Fintype.equivFin _).symm r with
    | .inl ⟨p, _⟩ => match kind p.val with | .inl _ => 0 | .inr k => k
    | .inr _ => 0
  let lower := fun r => min (count r - 1) ⌊max 1 (min (x.ofLp r) (count r))⌋₊
  let theta := fun r => max 1 (min (x.ofLp r) (count r)) - (lower r : ℝ)
  ∑ beta : Fin (structuralInputSize M.toEuclideanSCM i) → Bool,
    (∏ r, if 1 < count r then (if beta r then theta r else 1 - theta r)
      else (if beta r then (0 : ℝ) else 1)) •
    M.f i (structuralFiniteCoordinates M.toEuclideanSCM i (WithLp.toLp 1 (fun r =>
      if count r = 0 then x.ofLp r else if count r = 1 then 1
      else (lower r : ℝ) + if beta r then 1 else 0)))

/-- For [a canonical structural causal model](hyp:M), [regularity](hyp:L),
[mechanism](hyp:K), and [input-radius](hyp:R) bounds, [a node](hyp:i),
[a proposed target function](hyp:f), [a family of networks indexed by total depth,
using four fewer hidden layers and the prescribed structural width](hyp:q),
[an approximation constant](hyp:Cᵢ), [an error-scale constant](hyp:A), and
[a depth threshold](hyp:N), the [structural approximation certificate](goal) requires
[the target to equal the interpolated mechanism](step:1) and [requires, whenever the
structural input dimension is positive, a positive approximation constant, an error-scale
constant at least both one and the approximation constant times two to the power two
divided by that dimension, and a threshold of at least eight; at every depth at or above the
threshold, coordinate errors throughout the prescribed box are bounded by the approximation
constant times depth minus four to the power negative two divided by the input dimension,
and for categorical nodes the output dimension times the error scale at that depth is
at most one half](step:2). -/
def StructuralApproximantWitness (M : CanonicalSCM kind dims dag G C) (L K R : ℝ≥0)
    (i : Fin n) (f : L1Vec (structuralInputSize M.toEuclideanSCM i) → L1Vec (outputDim (kind i)))
    (q : ∀ ℓ : ℕ, ReLUNet (structuralInputSize M.toEuclideanSCM i) (outputDim (kind i))
      (outputDim (kind i) * (2 * structuralInputSize M.toEuclideanSCM i + 10)) (ℓ - 4))
    (Cᵢ A : ℝ) (N : ℕ) : Prop :=
  f = structuralInterpolant M i ∧
  (0 < structuralInputSize M.toEuclideanSCM i →
    0 < Cᵢ ∧ max 1 ((2 : ℝ)^(2 / (structuralInputSize M.toEuclideanSCM i : ℝ)) * Cᵢ) ≤ A ∧
    8 ≤ N ∧ ∀ ℓ : ℕ, N ≤ ℓ →
      (∀ x, (∀ j, |x.ofLp j| ≤ (structuralApproximationBox M L K R : ℝ)) → ∀ j,
        |((q ℓ).eval x).ofLp j - (f x).ofLp j| ≤
          Cᵢ * ((ℓ : ℝ) - 4)^(-(2 : ℝ) / structuralInputSize M.toEuclideanSCM i)) ∧
      ((kind i).isRight = true →
        outputDim (kind i) * (A * (ℓ : ℝ)^(-(2 : ℝ) / structuralInputSize M.toEuclideanSCM i)) ≤ 1/2))

-- @node: def:corollary-deep-nn-structural-approximants
/-- Given [a canonical structural causal model](hyp:M), [regularity](hyp:L),
[mechanism](hyp:K), and [input-radius](hyp:R) bounds, [a node](hyp:i),
[a target function](hyp:f), [a family of networks with four reserved layers and the
prescribed structural width](hyp:q), [an approximation constant](hyp:Cᵢ),
[an error-scale constant](hyp:A), [a depth threshold](hyp:N),
[a certificate that this target and network family satisfy the structural approximation
requirements](hyp:_hchosen), [a chosen total depth](hyp:L₀), and
[a guarantee that this depth meets the threshold whenever the input dimension is positive](hyp:_hbudget),
the [structural approximant](goal) equals the target at zero input dimension.
Otherwise it [sets the error floor to the error-scale constant times total depth to the
power negative two divided by the input dimension](step:1), [sets the clipping radius
to the structural approximation box radius](step:2), and [evaluates the chosen network
on clipped inputs, additionally flooring every output coordinate at the error floor
for categorical nodes](step:3). -/
def structuralApproximant (M : CanonicalSCM kind dims dag G C) (L K R : ℝ≥0) (i : Fin n)
    (f : L1Vec (structuralInputSize M.toEuclideanSCM i) → L1Vec (outputDim (kind i)))
    (q : ∀ ℓ : ℕ, ReLUNet (structuralInputSize M.toEuclideanSCM i) (outputDim (kind i))
      (outputDim (kind i) * (2 * structuralInputSize M.toEuclideanSCM i + 10)) (ℓ - 4))
    (Cᵢ A : ℝ) (N : ℕ) (_hchosen : StructuralApproximantWitness M L K R i f q Cᵢ A N)
    (L₀ : ℕ) -- @realizes L_0(total structural depth, including four reserved layers)
    (_hbudget : 0 < structuralInputSize M.toEuclideanSCM i → N ≤ L₀) :
    L1Vec (structuralInputSize M.toEuclideanSCM i) → L1Vec (outputDim (kind i)) := -- @realizes \hat{f}_i(certified projected approximant with positive error floor; exact at zero input dimension)
  if structuralInputSize M.toEuclideanSCM i = 0 then f
  else
    let eps := A * (L₀ : ℝ)^(-(2 : ℝ) / structuralInputSize M.toEuclideanSCM i)
    let B := structuralApproximationBox M L K R
    if (kind i).isRight then
      fun x => WithLp.toLp 1 (fun j => max eps (((q L₀).eval (clipBox B x)).ofLp j))
    else (q L₀).eval ∘ clipBox B
end StructuralApproximation

/-- For [a dimension](hyp:d), the [uniform unit-cube law](goal) is the distribution
of a vector with independent coordinates uniform on the closed interval from zero to one. -/
def uniformCubeLaw (d : ℕ) : Measure (L1Vec d) :=
  (Measure.pi (fun _ : Fin d => volume.restrict (Set.Icc (0:ℝ) 1))).map (WithLp.toLp 1)
/-- For [a number of mixture components](hyp:n), the [generator input law](goal)
pairs independent uniform draws on the closed unit interval with independent standard
Gumbel shocks, with one draw of each kind per component and independence between the two families. -/
def generatorInputLaw (n : ℕ) : Measure ((Fin n → ℝ) × (Fin n → ℝ)) := -- @realizes U_i(independent scalar uniform coordinates on the closed unit interval)
  (Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0:ℝ) 1))).prod (gumbelInputs n)
/-- For [a three-part generator](hyp:q), the [generated output law](goal) is the
distribution of its output under independent uniform component inputs and standard Gumbel shocks. -/
def generatorLaw {n d : ℕ} {dC : Fin n → ℕ} {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau) : Measure (L1Vec d) :=
  (generatorInputLaw n).map q.eval

/-- Given [component intermediate dimensions](hyp:dC), [first-block width](hyp:W1)
and [depth](hyp:L1), [second-block width](hyp:W2) and [depth](hyp:L2),
[a mixing temperature](hyp:tau), and [an output clipping level](hyp:K), the
[clipped generator class](goal) consists of all three-part generators with these
architecture budgets followed by coordinatewise output clipping. No Lipschitz restriction is imposed. -/
def clippedGeneratorClass {N d : ℕ} (dC : Fin N → ℕ)
    (W1 L1 W2 L2 : ℕ) (tau K : ℝ) :
    Set (((Fin N → ℝ) × (Fin N → ℝ)) → L1Vec d) := -- @realizes \mathcal{NN}^{\infty,K}(image of the full generator class under final coordinatewise clipping)
  {g | ∃ q : ThreePartGenerator N d dC W1 L1 W2 L2 tau, g = truncK K ∘ q.eval}

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
    {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)} {C : Fin b → Set (Fin n)}

-- @node: def:definition-3
/-- For [node types specifying continuous dimensions or category counts](hyp:kind)
and [latent-block dimensions](hyp:dims), a [neural causal model](goal) consists of
a Euclidean structural causal model with neural propensity maps, independent uniform
latent blocks and standard Gumbel noise. Its continuous mechanisms equal the propensity
maps, its categorical mechanisms select the smallest maximizer of extended log
propensity plus noise with nonnegative propensities of positive total mass, and each
propensity map agrees on admissible inputs with a finite ReLU network after reordering coordinates. -/
structure NeuralCausalModel (kind : Fin n → NodeKind) (dims : Fin b → ℕ) where
  model : EuclideanSCM kind dims
  propensity : MechanismWeights model -- @realizes f_i(chosen categorical propensity maps of the neural specialization)
  continuousEq : ∀ i d, kind i = Sum.inl d → ∀ x ∈ model.domain i,
    propensity i x = model.continuousMap i x
  uniformLatents : model.latentLaw =
    ((Measure.pi (fun j => uniformCubeLaw (dims j))).prod
      (Measure.pi (fun _ : Σ i, Fin (noiseDim (kind i)) => gumbelLaw))).map
        (fun z => WithLp.toLp 1 (fun c => match c with
          | .inl ⟨j,k⟩ => (z.1 j).ofLp k | .inr k => z.2 k))
  categoricalWeights : ∀ i k, kind i = Sum.inr k → ∀ x ∈ model.domain i,
    (∀ j, 0 ≤ (propensity i x).ofLp j) ∧ 0 < ∑ j, (propensity i x).ofLp j
  categoricalMechanism : ∀ i k (h : kind i = Sum.inr k) x,
    x ∈ model.domain i → ∀ g : Fin k → ℝ,
      model.categoricalLabel i k h x (WithLp.toLp 1 g) =
      (firstArgmax (fun j : Fin k =>
        extendedLog ((propensity i x).ofLp (Fin.cast (congrArg outputDim h).symm j)) +
          (g j : EReal))).getD ⟨0, model.categoricalPositive i k h⟩
  structuralNetworks : ∀ i, ∃ W L,
    ∃ q : ReLUNet (Fintype.card
      (Sum (Σ p : {p // p ∈ model.dag.parents i}, Fin (valueDim (kind p)))
        (Σ j : {j // j ∈ model.incidence i}, Fin (dims j)))) (outputDim (kind i)) W L,
      ∃ e : (Fin (Fintype.card
        (Sum (Σ p : {p // p ∈ model.dag.parents i}, Fin (valueDim (kind p)))
          (Σ j : {j // j ∈ model.incidence i}, Fin (dims j))))) ≃
        (Sum (Σ p : {p // p ∈ model.dag.parents i}, Fin (valueDim (kind p)))
          (Σ j : {j // j ∈ model.incidence i}, Fin (dims j))),
        ∀ x ∈ model.domain i, propensity i x = q.eval (WithLp.toLp 1 (fun j => x.ofLp (e j)))

/-- For [node types](hyp:kind), [latent-block dimensions](hyp:dims),
[a directed acyclic causal graph](hyp:dag), and [the nodes sharing each latent block](hyp:C),
an [admissible structural class](goal) assigns to each node a set of functions from
its admissible parent and latent inputs to its output vectors.

Off-domain extensions cannot affect membership. -/
abbrev AdmissibleStructuralClass (kind : Fin n → NodeKind) (dims : Fin b → ℕ)
    (dag : Causalean.Graph.DAG (Fin n)) (C : Fin b → Set (Fin n)) :=
  ∀ i, Set (↥(admissibleStructuralInputs kind dims dag (canonicalIncidence C) i) →
    L1Vec (outputDim (kind i)))

/-- For [a canonical structural causal model](hyp:M) with [node types](hyp:kind),
[latent-block dimensions](hyp:dims), [a directed causal graph](hyp:dag),
[a bidirected graph](hyp:G), and [latent-block node sets](hyp:C), the
[restricted mechanism at a node](goal) evaluates the original mechanism only on
admissible parent and latent inputs to [that node](hyp:i). -/
def CanonicalSCM.restrictedMechanism (M : CanonicalSCM kind dims dag G C) (i : Fin n) :
    ↥(admissibleStructuralInputs kind dims dag (canonicalIncidence C) i) →
      L1Vec (outputDim (kind i)) := -- @realizes f_i(canonical mechanism on its admissible parent and latent inputs)
  fun x => M.f i x.val

/-- For [node types](hyp:kind), [latent-block dimensions](hyp:dims),
[a directed acyclic causal graph](hyp:dag), and [the nodes sharing each latent block](hyp:C),
an [ambient structural class](goal) assigns to each node a set of functions from
its full parent and latent coordinate space to its output vectors.

These ambient representatives store and evaluate finite neural networks;
canonical model classes use `AdmissibleStructuralClass` instead. -/
abbrev StructuralClass (kind : Fin n → NodeKind) (dims : Fin b → ℕ)
    (dag : Causalean.Graph.DAG (Fin n)) (C : Fin b → Set (Fin n)) :=
  ∀ i, Set (StructuralInput kind dims dag (canonicalIncidence C) i → L1Vec (outputDim (kind i)))
/-- For [latent-block output dimensions](hyp:dims) and [mixture component counts
for each block](hyp:counts), a [generator class](goal) assigns to each latent block
a set of functions mapping its paired scalar inputs and mixing shocks to a latent vector. -/
abbrev GeneratorClass (dims : Fin b → ℕ) (counts : Fin b → ℕ) :=
  ∀ j, Set (((Fin (counts j) → ℝ) × (Fin (counts j) → ℝ)) → L1Vec (dims j))
/-- For [node types](hyp:kind) and [mixture component counts for each latent block](hyp:counts),
the [simulation input space](goal) pairs the scalar inputs and mixing shocks of all
latent generators with a categorical noise vector of the appropriate dimension at each node. -/
abbrev SimulationInput (kind : Fin n → NodeKind) (counts : Fin b → ℕ) :=
  ((∀ j, (Fin (counts j) → ℝ) × (Fin (counts j) → ℝ)) ×
    (∀ i, L1Vec (noiseDim (kind i))))
/-- For [node types](hyp:kind) and [mixture component counts for each latent block](hyp:counts),
the [simulation input law](goal) draws all generator inputs independently from their
uniform and Gumbel input laws, independently of node noise vectors whose coordinates
are independent standard Gumbel shocks. -/
def simulationInputLaw (kind : Fin n → NodeKind) (counts : Fin b → ℕ) :
    Measure (SimulationInput kind counts) :=
  (Measure.pi (fun j => generatorInputLaw (counts j))).prod
    (Measure.pi (fun i => (gumbelInputs (noiseDim (kind i))).map (WithLp.toLp 1)))

/-- A [latent generator mapping paired scalar inputs and mixing shocks to an output vector](hyp:g)
has a [finite neural realization](goal) if it is either [an ordinary ReLU network on
the concatenated input coordinates](step:1) or [a three-part generator with a
Gumbel-softmax layer, optionally followed by coordinatewise clipping at a nonnegative level](step:2).

Class membership supplies any further architecture and budget restrictions. -/
def NeuralGeneratorRealizable {N d : ℕ}
    (g : ((Fin N → ℝ) × (Fin N → ℝ)) → L1Vec d) : Prop :=
  (∃ W L, ∃ q : ReLUNet (N + N) d W L,
    ∀ z, g z = q.eval (WithLp.toLp 1 (Fin.addCases z.1 z.2))) ∨
  (∃ dC : Fin N → ℕ, ∃ W1 L1 W2 L2 : ℕ, ∃ tau : ℝ,
    ∃ q : ThreePartGenerator N d dC W1 L1 W2 L2 tau,
      g = q.eval ∨ ∃ K : ℝ≥0, g = truncK K ∘ q.eval)

/-- A network representation whose raw categorical weights are nonnegative with
positive total mass on every admissible structural input. The canonical
propensity agrees with their normalization throughout that domain.
`structuralBound` indexes approximation domains only; it never limits coherence
of the structural equations or confines the generated inputs.
The function classes `F₀` and `F₁` are parameters, exactly as in the paper's
$\text{NCM}_{\mathcal G}(\mathcal F_0,\mathcal F_1)$ (ass:pin-101: all models satisfying the neural
structural equation with $\hat f_i\in\mathcal F_0$ and $\hat g_j\in\mathcal F_1$).
Each raw structural map carries a finite ReLU realization on its whole ambient
input space, independently of the supplied class membership restriction.
Every latent generator has an intrinsic finite neural realization and belongs to F₁.
Specific three-part budgets and output clipping are imposed by the specialized classes. -/
-- @node: def:neural-causal-class
structure NCMIn (kind : Fin n → NodeKind) (dims : Fin b → ℕ) -- @realizes \hat{\mathcal{M}}(network representations with intrinsic membership and population-law fields) -- @realizes \text{NCM}_{\mathcal{G}}(network representations with intrinsic membership and population-law fields)
    (dag : Causalean.Graph.DAG (Fin n)) (G : SimpleGraph (Fin n))
    (C : Fin b → Set (Fin n)) (counts : Fin b → ℕ)
    (F₀ : StructuralClass kind dims dag C) (F₁ : GeneratorClass dims counts)
    (structuralBound : Option (ℝ × ℝ) := none) where
  canonical : CanonicalSCM kind dims dag G C
  rawStructural : ∀ i, StructuralInput kind dims dag (canonicalIncidence C) i → -- @realizes \hat{f}_i(node-specific raw structural functions before categorical normalization) -- @realizes \hat{f}(node-specific raw structural functions before categorical normalization) -- @realizes \mathcal{F}_0(node-specific raw structural functions before categorical normalization)
    L1Vec (outputDim (kind i))
  structuralMem : ∀ i, rawStructural i ∈ F₀ i
  structuralNetworks : ∀ i, ∃ W L,
    ∃ q : ReLUNet (structuralInputSize canonical.toEuclideanSCM i)
      (outputDim (kind i)) W L,
      ∀ x, rawStructural i (structuralFiniteCoordinates canonical.toEuclideanSCM i x) =
        q.eval x -- @realizes \hat{f}_i(raw structural map is a finite ReLU neural function at every input) -- @realizes \mathcal{F}_0(membership is restricted to neurally realizable structural maps)
  continuousEq : ∀ i d, kind i = Sum.inl d → canonical.f i = rawStructural i
  categoricalEq : ∀ i k, kind i = Sum.inr k →
    (∀ x ∈ canonical.domain i,
      (∀ j, 0 ≤ (rawStructural i x).ofLp j) →
      0 < ∑ j, (rawStructural i x).ofLp j →
      canonical.f i x = WithLp.toLp 1 (fun j =>
        (rawStructural i x).ofLp j / ∑ l, (rawStructural i x).ofLp l)) ∧ -- @realizes \hat{f}_i(canonical propensity equals normalized raw weights on every admissible structural input)
    (∀ x ∈ canonical.domain i,
      (∀ j, 0 ≤ (rawStructural i x).ofLp j) ∧ -- @realizes \hat{f}_i(nonnegative raw categorical weights on canonical.domain i)
      0 < ∑ j, (rawStructural i x).ofLp j) -- @realizes \hat{f}_i(positive categorical normalization denominator on canonical.domain i)
  generator : ∀ j, ((Fin (counts j) → ℝ) × (Fin (counts j) → ℝ)) → L1Vec (dims j) -- @realizes \mathcal{F}_1(component-specific map of uniform and Gumbel inputs to a latent vector) -- @realizes Z_{C_j}(component-specific map of uniform and Gumbel inputs to a latent vector) -- @realizes \hat{U}_{C_j}(component-specific map of uniform and Gumbel inputs to a latent vector)
  generatorMem : ∀ j, generator j ∈ F₁ j
  generatorNetworks : ∀ j, NeuralGeneratorRealizable (generator j) -- @realizes \hat{g}(every component generator has a finite neural realization) -- @realizes \mathcal{F}_1(class membership additionally restricted to neural generators)
  blockLaw_eq : ∀ j, (canonical.blockLaw j : Measure (L1Vec (dims j))) =
    (generatorInputLaw (counts j)).map (generator j)

/-- For [a neural causal representation](hyp:R) with [node types](hyp:kind),
[latent-block dimensions](hyp:dims), [a directed causal graph](hyp:dag),
[a bidirected graph](hyp:G), and [latent-block node sets](hyp:C), the
[intervened joint output](goal) applies [an intervention](hyp:t) to the structural
model, using [simulation inputs](hyp:z) to generate its latent blocks and supply
its node-specific categorical noise. -/
def ncmIntervenedEval {counts : Fin b → ℕ} {F₀ : StructuralClass kind dims dag C}
    {F₁ : GeneratorClass dims counts} {structuralBound : Option (ℝ × ℝ)}
    (R : NCMIn kind dims dag G C counts F₀ F₁ structuralBound)
    (t : LawIntervention kind) (z : SimulationInput kind counts) : Joint kind :=
  intervenedEval R.canonical.toEuclideanSCM t.val
    (WithLp.toLp 1 (fun c => match c with
      | .inl ⟨j,k⟩ => (R.generator j (z.1 j)).ofLp k
      | .inr ⟨i,k⟩ => (z.2 i).ofLp k))
/-- For [a neural causal representation](hyp:R) with [node types](hyp:kind),
[latent-block dimensions](hyp:dims), [a directed causal graph](hyp:dag),
[a bidirected graph](hyp:G), and [latent-block node sets](hyp:C), the
[observational joint output](goal) evaluates the model without intervention,
using [simulation inputs](hyp:z) to generate latent blocks and supply node-specific categorical noise.

`NCMIn.generatorNetworks` restricts every
component map to a finite neural realization. `NCMIn.categoricalEq` identifies the canonical
propensity with the normalized raw weights on every admissible input, including
inputs outside the approximation cube. Normalization preserves the extended-log
argmax and its smallest-label tie convention. -/
-- @node: def:eq-structure-equation-hat
def ncmEval {counts : Fin b → ℕ} {F₀ : StructuralClass kind dims dag C}
    {F₁ : GeneratorClass dims counts} {structuralBound : Option (ℝ × ℝ)}
    (R : NCMIn kind dims dag G C counts F₀ F₁ structuralBound)
    (z : SimulationInput kind counts) : Joint kind :=
  ncmIntervenedEval R (noIntervention kind) z

/-- If [a node type has a positive category count whenever it is categorical](hyp:ha)
and [is categorical with the specified number of labels](hyp:h), then
[expressing its canonical selector in that label space gives the smallest label
maximizing extended log weight plus noise, with the first label as fallback](goal). -/
-- @node: canonicalSelector_categoricalLabel
lemma canonicalSelector_categoricalLabel (a : NodeKind)
    (ha : ∀ m, a = Sum.inr m → 0 < m) (k : ℕ) (h : a = Sum.inr k)
    (w : L1Vec (outputDim a)) (g : L1Vec k) :
    cast (congrArg ObservedValue h)
      (canonicalSelector a ha w
        (WithLp.toLp 1 (fun j => g.ofLp (Fin.cast (congrArg noiseDim h) j)))) =
      (firstArgmax (fun j : Fin k =>
        extendedLog (w.ofLp (Fin.cast (congrArg outputDim h).symm j)) +
          (g.ofLp j : EReal))).getD ⟨0, ha k h⟩ := by
  subst a
  rfl

/-- If [the common normalizer is strictly positive](hyp:hs), then
[the extended log of the first normalized weight plus its shock is at most the
corresponding score for the second weight exactly when the same comparison holds
without normalization](goal), including when either weight is zero. -/
-- @node: extendedLog_normalized_score_le_iff
lemma extendedLog_normalized_score_le_iff (a b s g h : ℝ) (hs : 0 < s) :
    extendedLog (a / s) + (g : EReal) ≤ extendedLog (b / s) + (h : EReal) ↔
      extendedLog a + (g : EReal) ≤ extendedLog b + (h : EReal) := by
  by_cases ha : a = 0
  · simp [ha, extendedLog]
  · by_cases hb : b = 0
    · simp [hb, extendedLog, ha, hs.ne']
    · simp only [extendedLog, if_neg ha, if_neg hb,
        if_neg (div_ne_zero ha hs.ne'), if_neg (div_ne_zero hb hs.ne'),
        Real.log_div ha hs.ne', Real.log_div hb hs.ne',
        ← EReal.coe_add, EReal.coe_le_coe_iff]
      constructor <;> intro hab <;> linarith

/-- If [the common weight normalizer is strictly positive](hyp:hs), then
[dividing every weight by it leaves the smallest label maximizing extended log
weight plus its additive shock unchanged](goal). -/
-- @node: firstArgmax_normalized_weights
lemma firstArgmax_normalized_weights {k : ℕ} (w g : Fin k → ℝ)
    (s : ℝ) (hs : 0 < s) :
    firstArgmax (fun j => extendedLog (w j / s) + (g j : EReal)) =
      firstArgmax (fun j => extendedLog (w j) + (g j : EReal)) := by
  have hp (j : Fin k) :
      (∀ l, extendedLog (w l / s) + (g l : EReal) ≤
        extendedLog (w j / s) + (g j : EReal)) ↔
      (∀ l, extendedLog (w l) + (g l : EReal) ≤
        extendedLog (w j) + (g j : EReal)) :=
    forall_congr' fun l => extendedLog_normalized_score_le_iff _ _ _ _ _ hs
  simp only [firstArgmax, hp]

/-- If [a node is categorical with the specified number of labels](hyp:h) and
[its parent and latent input is admissible for the canonical model](hyp:hx), then
[its categorical mechanism selects the smallest label maximizing extended log
raw neural weight plus categorical noise, with the first label as fallback](goal),
for every categorical noise vector. -/
-- @node: NCMIn.categoricalMechanism_eq
lemma NCMIn.categoricalMechanism_eq {counts : Fin b → ℕ}
    {F₀ : StructuralClass kind dims dag C} {F₁ : GeneratorClass dims counts}
    {structuralBound : Option (ℝ × ℝ)}
    (R : NCMIn kind dims dag G C counts F₀ F₁ structuralBound)
    (i : Fin n) (k : ℕ) (h : kind i = Sum.inr k)
    (x : StructuralInput kind dims dag (canonicalIncidence C) i)
    (hx : x ∈ R.canonical.domain i) (g : L1Vec k) :
    R.canonical.toEuclideanSCM.categoricalLabel i k h x g =
      (firstArgmax (fun j : Fin k =>
        extendedLog ((R.rawStructural i x).ofLp
          (Fin.cast (congrArg outputDim h).symm j)) + (g.ofLp j : EReal))).getD
            ⟨0, R.canonical.categoricalPositive i k h⟩ := by
  have hpos := (R.categoricalEq i k h).2 x hx
  have heq := (R.categoricalEq i k h).1 x hx hpos.1 hpos.2
  have hlabel : R.canonical.toEuclideanSCM.categoricalLabel i k h x g =
      (firstArgmax (fun j : Fin k =>
        extendedLog ((R.canonical.f i x).ofLp
          (Fin.cast (congrArg outputDim h).symm j)) + (g.ofLp j : EReal))).getD
            ⟨0, R.canonical.categoricalPositive i k h⟩ := by
    unfold EuclideanSCM.categoricalLabel
    change cast (congrArg ObservedValue h) (canonicalMechanism R.canonical i x _) = _
    have hmech : canonicalMechanism R.canonical i x
        (WithLp.toLp 1 (fun j => g.ofLp (Fin.cast (congrArg noiseDim h) j))) =
        canonicalSelector (kind i) (R.canonical.positive_categories i) (R.canonical.f i x)
          (WithLp.toLp 1 (fun j => g.ofLp (Fin.cast (congrArg noiseDim h) j))) :=
      (canonicalSelector_eq (kind i) (R.canonical.positive_categories i) _ _).symm
    exact (congrArg (cast (congrArg ObservedValue h)) hmech).trans
      (canonicalSelector_categoricalLabel (kind i) (R.canonical.positive_categories i) k h
        (R.canonical.f i x) g)
  rw [hlabel, heq]
  exact congrArg (fun z => z.getD ⟨0, R.canonical.categoricalPositive i k h⟩)
    (firstArgmax_normalized_weights
      (fun j : Fin k => (R.rawStructural i x).ofLp
        (Fin.cast (congrArg outputDim h).symm j)) g.ofLp
      (∑ l, (R.rawStructural i x).ofLp l) hpos.2)

end
end Papers.TbsNeuralCausalPi
