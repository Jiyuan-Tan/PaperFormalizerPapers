module
public import Papers.TbsNeuralCausalPi.Setup.EmpiricalAdmissibility
public import Papers.TbsNeuralCausalPi.Setup.Networks
public import Papers.TbsNeuralCausalPi.Setup.Assumptions.Generators
public import Causalean.Stat.Concentration.VC.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Dirac
/-! # Disclosed cited approximation and concentration gates
The paper assumes these propositions. They are never asserted as proved lemmas.
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

/-- The [Euclidean representation](goal) of [a vector measured with the one-norm](hyp:x) has the same coordinates, equipped with the Euclidean norm. -/
def toEuclidean {d : ℕ} (x : L1Vec d) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 x.ofLp

/-- For [a ReLU network](hyp:Phi) and [a lattice spacing](hyp:mesh), [lattice membership of its parameters](goal) requires [all hidden weights and biases to be integer multiples of that spacing](step:1), [all output weights to be such multiples](step:2), and [all output biases to be such multiples](step:3). -/
def ReLUNet.paramsInLattice {din dout W L : ℕ}
    (Phi : ReLUNet din dout W L) (mesh : ℝ) : Prop :=
  (∀ l ∈ Phi.hidden, (∀ j i, ∃ z : ℤ, l.2.2.1 j i = mesh * z) ∧
    (∀ j, ∃ z : ℤ, l.2.2.2 j = mesh * z)) ∧
  (∀ j i, ∃ z : ℤ, Phi.outputWeight j i = mesh * z) ∧
  (∀ j, ∃ z : ℤ, Phi.outputBias j = mesh * z)

/-- For [a ReLU network](hyp:Phi) and [a mesh size](hyp:mesh), [quantization of its parameters](goal) first [defines an admissible weight as a mesh multiple bounded in absolute value by the reciprocal mesh, or a nonzero weight whose reciprocal satisfies that bound and lattice condition](step:1), then [requires positive mesh and admissible weights and biases in every hidden and output layer](step:2).

This is the parameter convention of source Definition VI.3. -/
def ReLUNet.paramsQuantized {din dout W L : ℕ}
    (Phi : ReLUNet din dout W L) (mesh : ℝ) : Prop :=
  let quantized : ℝ → Prop := fun w =>
    (∃ z : ℤ, w = mesh * z ∧ |w| ≤ mesh⁻¹) ∨
    (w ≠ 0 ∧ ∃ z : ℤ, w⁻¹ = mesh * z ∧ |w⁻¹| ≤ mesh⁻¹)
  0 < mesh ∧
    (∀ l ∈ Phi.hidden, (∀ j i, quantized (l.2.2.1 j i)) ∧
      (∀ j, quantized (l.2.2.2 j))) ∧
    (∀ j i, quantized (Phi.outputWeight j i)) ∧
    (∀ j, quantized (Phi.outputBias j))

/-- The [number of nonzero parameters](goal) in [a ReLU network](hyp:Phi) is the sum of the numbers of nonzero weights and biases across all its hidden layers and its output layer. -/
def ReLUNet.nonzeroParamCount {din dout W L : ℕ} (Phi : ReLUNet din dout W L) : ℕ :=
  (Phi.hidden.map (fun l =>
    (Finset.univ.filter (fun ji : Fin l.output × Fin l.input => l.2.2.1 ji.1 ji.2 ≠ 0)).card +
    (Finset.univ.filter (fun j : Fin l.output => l.2.2.2 j ≠ 0)).card)).sum +
  (Finset.univ.filter (fun ji : Fin dout × Fin (finalWidth din Phi.hidden) =>
    Phi.outputWeight ji.1 ji.2 ≠ 0)).card +
  (Finset.univ.filter (fun j : Fin dout => Phi.outputBias j ≠ 0)).card

/-- The [quantized distribution-generation assumption](goal) asserts that one positive depth multiplier works in every positive component dimension: each Lipschitz chart of a finite-component probability law admits quantized ReLU generators from a uniform scalar input, with depth proportional to dimension, a dimension-dependent minimum width, and Wasserstein error bounded by a chart-dependent constant times width to the negative reciprocal dimension. The refinement is the floor of the dimension-root of scaled width, is at least two, and controls both hidden-layer widths and the prescribed quantization mesh.

D. Perekrestenko, L. Eberhard and H. Bölcskei (2022), Theorem VIII.1,
"High-Dimensional Distribution Generation Through Deep Neural Networks",
arXiv:2107.12466v3, citation handle `perekrestenko2022high`.
This carrier is the paper's component approximation claim at width budget W₁:
the target is the inverse-chart push-forward of the normalized component law,
and the error is O(W₁^(-1/q)) in the paper's one-norm. The dimension-dependent
width threshold uses n = floor((W₁/A)^(1/q)), with integer source depth s = 1
and quantization mesh delta/n (including reciprocal weights). The source's parameter-count and exact Euclidean
error estimates are not assumed by this carrier; the depth multiplier c is one constant for every
dimension q (the source's depth is 4q - 2 at s = 1); the numerical specialization
is recorded separately in Helpers/WideQuantization. Clipping is a host step.
Source: https://arxiv.org/abs/2107.12466v3, Section VIII, Theorem VIII.1
and its following quantization specialization. -/
-- @node: lem:wide-nn-perekrestenko-theorem-viii-1
def PerekrestenkoQuantizedGeneration : Sort 0 := -- @realizes s(natural-number source depth fixed by let s := 1 below; distinct from delta and delta / n)
  ∃ c : ℕ, 0 < c ∧ ∀ q : ℕ, 0 < q → ∃ A : ℝ, 1 ≤ A ∧ -- @realizes \Theta(d_i^C)(depth c * q with one multiplier c for every dimension q; the source's depth (s+3)q-s-1 = 4q-2 at s = 1)
    ∀ (d N : ℕ) (P : ProbabilityMeasure (L1Vec d))
      (S : Fin N → Set (L1Vec d)) (dC : Fin N → ℕ) (L : ℝ≥0),
      SupportFiniteComponents (P : Measure _) S →
      ComponentsLipschitzHomeomorphic S dC L →
      ∀ (i : Fin N), dC i = q →
      ∀ f : homeoClass (unitCube (dC i)) (S i), LipschitzWith L f →
      ∃ B : ℝ, 0 < B ∧ ∀ W₁ : ℕ, A * (2 : ℝ)^q ≤ W₁ → -- @realizes W_1(component width budget above the dimension-dependent threshold)
        let n : ℕ := ⌊((W₁ : ℝ) / A) ^ (1 / (q : ℝ))⌋₊ -- @realizes n(refinement floor chosen from W_1 and the dimension-only width factor A)
        let s : ℕ := 1 -- @realizes s(carrier ℕ and fixed value s = 1; source depth, distinct from quantization delta and mesh delta / n)
        let delta : ℝ := (⌈Real.sqrt q * (q + 1) * n * ((n : ℝ) - 1)⌉₊ : ℝ)⁻¹ -- @realizes \delta(prescribed quantization parameter at the pinned refinement)
        2 ≤ n ∧ A * (n : ℝ)^q ≤ W₁ ∧
        ∃ Phi : ReLUNet 1 (dC i) W₁ (c * q), -- @realizes \hat{g}_1^i(quantized component network of width W_1 and depth proportional to its positive dimension)
          (∀ l ∈ Phi.hidden, (l.output : ℝ) ≤ A * (n : ℝ)^q) ∧
          Phi.paramsQuantized (delta / n) ∧
          wasserstein1 ((ProbabilityTheory.cond (P : Measure _) (S i)).map (chartInverse f))
            ((uniformCubeLaw 1).map Phi.eval) ≤
              ENNReal.ofReal (B * (W₁ : ℝ) ^ (-(1 : ℝ) / q))

/-- The [Euclidean modulus of continuity](goal) of [a scalar function](hyp:f) at [a distance threshold](hyp:r) is the supremum of its absolute differences over pairs in the closed unit cube whose Euclidean distance is at most that threshold. -/
def euclidModulus {d : ℕ} (f : L1Vec d → ℝ) (r : ℝ) : ℝ :=
  sSup {a | ∃ x ∈ unitCube d, ∃ y ∈ unitCube d,
    dist (toEuclidean x) (toEuclidean y) ≤ r ∧ a = |f x - f y|}

/-- The [scalar approximation assumption](goal) asserts that in every positive input dimension there are positive dimension-only constants such that every continuous scalar function on the closed unit cube admits a ReLU approximant of width twice the dimension plus ten at every positive depth, with uniform error bounded by the first constant times its Euclidean modulus at the second constant times depth to the power negative two divided by dimension. -/
def yarotskyScalarModulusApprox : Sort 0 :=
  ∀ d : ℕ, 0 < d → ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
    ∀ f : L1Vec d → ℝ, ContinuousOn f (unitCube d) →
      ∀ depth : ℕ, 1 ≤ depth → ∃ q : ReLUNet d 1 (2*d+10) depth,
        ∀ x ∈ unitCube d,
          |f x - (q.eval x).ofLp 0| ≤
            a * euclidModulus f (c * (depth : ℝ) ^ (-(2 : ℝ) / d))

/-- The [coordinate approximation assumption](goal) asserts that in each positive input dimension, positive dimension-only constants give a scalar ReLU approximation to every coordinate of every Lipschitz homeomorphism from the closed unit cube onto a compact set. At every positive depth, width twelve times the input dimension suffices, with uniform error bounded by the first constant times the coordinate’s Euclidean modulus at the second constant times depth to the power negative two divided by dimension.

D. Yarotsky (2018), Theorem 2(b), arXiv:1802.03620, Section 2,
equations (1) and (2), citation handle `yarotsky2018optimal`.
Dimension-only constants precede every Lipschitz homeomorphic chart and
coordinate. The width 2d+10 is padded to 12d. Stacking, clipping and the
Hölder interpolant graph construction are local proof obligations. -/
-- @node: lem:wide-nn-yarotsky-theorem-2
def YarotskyCoordinateApprox : Sort 0 :=
  ∀ d : ℕ, 0 < d → ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
    ∀ (D : ℕ) (S : Set (L1Vec D)), IsCompact S →
      ∀ (f : homeoClass (unitCube d) S) (L : ℝ≥0), LipschitzWith L f →
        ∀ j : Fin D, ∀ depth : ℕ, 1 ≤ depth →
          ∃ q : ReLUNet d 1 (12*d) depth,
            ∀ x ∈ unitCube d,
              |(if hx : x ∈ unitCube d then (f ⟨x,hx⟩).val.ofLp j else 0) -
                (q.eval x).ofLp 0| ≤
                a * euclidModulus
                  (fun y => if hy : y ∈ unitCube d then (f ⟨y,hy⟩).val.ofLp j else 0)
                  (c * (depth : ℝ) ^ (-(2 : ℝ) / d))

/-- The [structural-map approximation assumption](goal) asserts that in each positive structural input dimension, positive dimension-only constants give scalar ReLU approximations to every coordinate of every canonical structural causal model’s structural map that is Lipschitz on its closed input cube. At every positive depth, width twice the input dimension plus ten suffices, with uniform error bounded by the first constant times the coordinate’s Euclidean modulus at the second constant times depth to the power negative two divided by dimension.

D. Yarotsky (2018), Theorem 2(b), arXiv:1802.03620, Section 2,
equations (1) and (2), citation handle `yarotsky2018optimal`.
This carrier specializes the scalar modulus bound to Lipschitz coordinates
of canonical structural maps on their closed input cubes. It retains the
source width 2d+10, affine output and dimension-only positive constants a,c.
At fixed width the weight count W is linear in hidden depth L₀ and W ≥ L₀;
monotonicity of omega converts `a * omega(c * W^(-2/d))` to the depth form.
The general continuous-function proposition is recorded separately, rather
than assumed. Lipschitz specialization, stacking and clipping remain local. -/
-- @node: lem:deep-nn-yarotsky-theorem-2
def YarotskyStructuralApprox : Sort 0 :=
  ∀ d : ℕ, 0 < d → ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
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
                a * euclidModulus (fun y => (f y).ofLp j)
                  (c * (depth : ℝ) ^ (-(2 : ℝ) / d))

/-- The [packing-bound assumption](goal) asserts that for every nonempty class of functions taking values in $[0,1]$ with pseudo-dimension at most v, every positive sample size, and every tolerance ε in $(0,1]$, its empirical average-distance packing quantity is strictly less than e times (v + 1) times (2e/ε) to the power v.

M. Anthony and P. L. Bartlett (1999), Neural Network Learning:
Theoretical Foundations, Theorem 18.4, printed p.251,
citation handle `anthony1999neural`. Only the finite scalar
pseudo-dimension packing bound is assumed; the cover comparison is local. -/
-- @node: lem:sup-wasserstein-anthony-theorems
def AnthonyBartlettPacking : Sort 0 :=
  ∀ (X : Type) (G : Set (X → ℝ)), G.Nonempty →
    ∀ hG : (∀ g ∈ G, ∀ x, g x ∈ Set.Icc (0:ℝ) 1),
    ∀ v : ℕ,
      Causalean.Stat.Concentration.HasPseudoDimAtMost (fun g : G => g.val) v →
      ∀ (m : ℕ), 1 ≤ m → ∀ eps : ℝ, 0 < eps → eps ≤ 1 →
        (M1avg eps G m hG).toENNReal <
          ENNReal.ofReal (Real.exp 1 * (v+1) * (2 * Real.exp 1 / eps) ^ v)

/-- The [squared-loss concentration assumption](goal) asserts that for every nonempty Borel-parametrized class of measurable functions taking values in $[0,1]$ on a standard Borel input space, every joint input-label law with labels in $[0,1]$, every positive sample size m, and every ε in $(0,1)$, the completed sample-law probability that some function’s empirical squared loss differs from its population squared loss by at least ε is at most four times the class’s average-distance covering quantity at radius ε/16 on 2m points, multiplied by exp(−ε²m/32).

M. Anthony and P. L. Bartlett (1999), Theorem 17.1, printed p. 241,
with the standing measurability caveat on printed p. 15, citation handle
`anthony1999neural`. Source and caveat are transcribed in the retained
`anthony1999neural.txt`. The host uses a jointly measurable standard Borel
parameterization as an explicit sufficient admissibility condition, with
both the input and parameter spaces standard Borel. The source bound is
squared loss on X × [0,1]; it assumes no pseudo-dimension bound. Probabilities are evaluated in the completion of the sample law. -/
-- @node: lem:sup-wasserstein-anthony-theorem-17-1
def AnthonyBartlettSquaredLoss : Sort 0 :=
  ∀ (X : Type) (_mX : MeasurableSpace X) [StandardBorelSpace X]
    (G : Set (X → ℝ)), G.Nonempty → BorelParametrizedClass G →
    ∀ hG : (∀ g ∈ G, Measurable g ∧ ∀ x, g x ∈ Set.Icc (0:ℝ) 1),
    ∀ P : ProbabilityMeasure (X × Set.Icc (0 : ℝ) 1),
      ∀ (m : ℕ), 1 ≤ m → ∀ eps : ℝ, 0 < eps → eps < 1 →
        (Measure.pi (fun _ : Fin m => (P : Measure (X × Set.Icc (0 : ℝ) 1)))).completion
          {z : Fin m → X × Set.Icc (0 : ℝ) 1 | ∃ g ∈ G,
            |(∫ xy : X × Set.Icc (0 : ℝ) 1, (g xy.1 - xy.2.val)^2
                ∂(P : Measure (X × Set.Icc (0 : ℝ) 1))) -
              (m : ℝ)⁻¹ * ∑ i, (g (z i).1 - (z i).2.val)^2| ≥ eps} ≤
          4 * (N1avg (eps/16) G (2*m) (fun g hg => (hG g hg).2)).toENNReal *
            ENNReal.ofReal (Real.exp (-(eps^2 * m)/32))

/-- The [combined covering and concentration assumption](goal) requires both [the finite pseudo-dimension packing bound](step:1) and [the Borel-parametrized squared-loss concentration bound](step:2). -/
def AnthonyBartlettCoveringConcentration : Sort 0 :=
  AnthonyBartlettPacking ∧ AnthonyBartlettSquaredLoss

/-- The [small-deviation concentration assumption](goal) asserts that for each positive Euclidean dimension, exponential-moment power greater than one, positive exponential-moment scale, and prescribed moment value, positive constants can be chosen uniformly over all probability laws with that finite exponential moment. For every positive sample size N and threshold x in $(0,1]$, the probability that empirical Wasserstein distance is at least x is bounded by C exp(−cN times the dimension-dependent rate): x² in dimension one, the square of x/log(2 + 1/x) in dimension two, and x to the dimension in higher dimensions.

N. Fournier and A. Guillin (2015), "On the rate of convergence in
Wasserstein distance of the empirical measure", Theorem 2, condition (1),
p = 1 and 0 < x ≤ 1; citation handle `fournier2015rate`,
arXiv:1312.2128, doi:10.1007/s00440-014-0583-7.
The source's Euclidean ground norm is retained. Its large-deviation term
b(N,x) vanishes in this regime. Constants depend only on dimension,
alpha, gamma and the exponential moment value, before the law and sample
size are quantified. Conditional laws, norm conversion and rate assembly
are local deductions, outside this cited carrier. -/
-- @node: lem:consistency-fournier-theorem-2
def FournierGuillinSmallDeviation : Sort 0 :=
  ∀ d : ℕ, 1 ≤ d → -- @realizes d(positive source Euclidean dimension)
    ∀ alpha gamma e : ℝ, 1 < alpha → 0 < gamma →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ -- @realizes C(positive source prefactor fixed before the law and sample size) -- @realizes c(positive source exponent constant fixed before the law and sample size)
        ∀ mu : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)), -- @realizes \mu(probability law on Euclidean space with the source two-norm)
          Integrable (fun z => Real.exp (gamma * ‖z‖ ^ alpha)) (mu : Measure (EuclideanSpace ℝ (Fin d))) →
          (∫ z, Real.exp (gamma * ‖z‖ ^ alpha) ∂(mu : Measure (EuclideanSpace ℝ (Fin d)))) = e →
          ∀ N : ℕ, 1 ≤ N → -- @realizes n(positive IID source sample size N)
            ∀ x : ℝ, 0 < x → x ≤ 1 →
              (Measure.pi (fun _ : Fin N => (mu : Measure (EuclideanSpace ℝ (Fin d)))))
                {z | ENNReal.ofReal x ≤ wasserstein1
                  ((N : ℝ≥0∞)⁻¹ • ∑ i : Fin N, Measure.dirac (z i)) (mu : Measure (EuclideanSpace ℝ (Fin d)))} ≤
                ENNReal.ofReal (C * Real.exp (-c * N *
                  (if d = 1 then x^2 else if d = 2 then
                    (x / Real.log (2 + x⁻¹))^2 else x^d)))
end
end Papers.TbsNeuralCausalPi
