module
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.MetricSpace.CoveringNumbers
public import Mathlib.Data.Rel.Cover
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Toolkit.Foundations.MeasureTheory.Wasserstein
/-! # Norms, push-forwards and transport distances
The paper uses the one-norm for transport and Lipschitz constants, and the
coordinate supremum norm for uniform approximation.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
open MeasureTheory
open scoped ENNReal NNReal
noncomputable section
-- @node: def:norm-and-index-notation
/-- For [dimension d](hyp:d), [the vector space with the one-norm](goal) consists of d real coordinates, with norm equal to the sum of their absolute values. -/
abbrev L1Vec (d : ℕ) := WithLp 1 (Fin d → ℝ) -- @realizes \|\cdot\|(WithLp 1 finite real coordinate carrier)
  -- @realizes \|\cdot\|(one-norm carrier)

/-- For [a finite coordinate index set](hyp:I), [the measurable structure on real coordinate vectors with the one-norm](goal) is the Borel measurable structure. -/
instance withLpPiMeasurableSpace (I : Type*) [Fintype I] :
    MeasurableSpace (WithLp 1 (I → ℝ)) := borel _

/-- For [a finite coordinate index set](hyp:I), [the measurable sets of real vectors with the one-norm are exactly the Borel sets](goal). -/
instance withLpPiBorelSpace (I : Type*) [Fintype I] :
    BorelSpace (WithLp 1 (I → ℝ)) := ⟨rfl⟩

/-- For [a number n of labels](hyp:n), [the paper's index set](goal) consists of the integers from zero through n minus one. -/
abbrev PaperIndex (n : ℕ) := Fin n -- @realizes n(Fin n represents the first n labels through the one-based shift j.val+1) -- @realizes [n](Fin n represents the first n labels through the one-based shift j.val+1)

/-- On [a domain S](hyp:S), [the directed approximation error](goal) from [a target function class](hyp:F2) to [an approximating function class](hyp:F1) is the supremum over targets of the infimum over approximants of their uniform coordinate supremum distance on S, allowing infinite error. -/
def directedApproximationError {X : Type*} {d : ℕ} (S : Set X) -- @realizes S(domain for the extended nonnegative directed approximation error) -- @realizes \epsilon(directed supremum-infimum approximation error between the two function classes)
    (F1 F2 : Set (X → L1Vec d)) : ℝ≥0∞ :=
  ⨆ f : F2, ⨅ g : F1, ⨆ x : S, ENNReal.ofReal ‖(f.val x - g.val x).ofLp‖

/-- For [an index set I](hyp:I), [nonnegative weights](goal) assign a nonnegative real number to each index, without imposing normalization. -/
abbrev NonnegativeWeights (I : Type*) := I → ℝ≥0 -- @realizes p_i(nonnegative coordinates with no normalization or strict positivity imposed)

/-- In [dimension d](hyp:d), [the unit cube](goal) is the set of vectors whose coordinates all lie in the closed interval from zero to one. -/
def unitCube (d : ℕ) : Set (L1Vec d) := {x | ∀ j, x.ofLp j ∈ Set.Icc 0 1}
/-- In [dimension d](hyp:d), for [a real bound K](hyp:K), [the bounded cube](goal) consists of vectors whose coordinates have absolute value at most K. -/
def boundedCube (d : ℕ) (K : ℝ) : Set (L1Vec d) := {x | ∀ j, |x.ofLp j| ≤ K}
/-- For [a domain S](hyp:S) and [two vector-valued functions f and g](hyp:f,g), [the extended uniform distance](goal) is the supremum on S of the largest absolute coordinate difference, allowing infinity. -/
def supDistOn {X : Type*} {d : ℕ} (S : Set X) (f g : X → L1Vec d) : ℝ≥0∞ := -- @realizes \|\cdot\|_\infty(extended uniform supremum of Mathlib Pi norms)
  ⨆ x : S, ENNReal.ofReal ‖(f x - g x).ofLp‖
  -- @realizes \|\cdot\|_\infty(uniform coordinate supremum)

/-- For [a domain S](hyp:S) and [a vector-valued function f](hyp:f) whose [coordinate supremum norms are bounded above on S](hyp:_hbounded), [the uniform norm](goal) is the nonnegative part of the supremum of these norms on S. -/
def uniformNormOn {X : Type*} {d : ℕ} (S : Set X) (f : X → L1Vec d)
    (_hbounded : BddAbove ((fun x => ‖(f x).ofLp‖) '' S)) : ℝ≥0 := -- @realizes \|\cdot\|_\infty(finite uniform norm of a function bounded on S)
  Real.toNNReal (sSup ((fun x => ‖(f x).ofLp‖) '' S))

-- @node: def:homeomorphisms
/-- For [a domain K₁](hyp:K₁) and [a codomain K₂](hyp:K₂), [the homeomorphism class](goal) consists of continuous bijections between these sets with continuous inverses. -/
abbrev homeoClass {d₁ d₂ : ℕ} (K₁ : Set (L1Vec d₁)) (K₂ : Set (L1Vec d₂)) := -- @realizes \mathcal{H}(Homeomorph between domain and codomain subtypes)
  Homeomorph K₁ K₂ -- @realizes \mathcal{H}(homeomorphisms of the subtypes)

-- @node: def:push-forward
/-- For [a map f between measurable spaces](hyp:f) and [a measure μ on its domain](hyp:μ), [the push-forward measure](goal) is the image of μ under an almost-everywhere measurable representative of f; it is the zero measure if f is not almost-everywhere measurable. -/
abbrev pushForward {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) (μ : Measure X) := Measure.map f μ

-- @node: def:probability-simplex
/-- For [a number n of coordinates](hyp:n), [the probability simplex](goal) consists of nonnegative real coordinate vectors whose entries sum to one. -/
abbrev probabilitySimplex (n : ℕ) := stdSimplex ℝ (Fin n) -- @realizes \Delta_n(finite nonnegative coordinates with sum one) -- @realizes \Delta_m(finite nonnegative coordinates with sum one)
  -- @realizes \Delta_n(nonnegative coordinates of total mass one)

-- @node: def:lipschitz-class
/-- For [a domain K₁](hyp:K₁), [a target set K₂](hyp:K₂), and [a nonnegative Lipschitz bound L](hyp:L), [a Lipschitz map](goal) is a function on the ambient vector space that sends K₁ into K₂ and has one-norm Lipschitz constant at most L on K₁. -/
structure LipMap {d₁ d₂ : ℕ} (K₁ : Set (L1Vec d₁)) (K₂ : Set (L1Vec d₂)) (L : ℝ≥0) where -- @realizes f(map on the indicated domain into the indicated codomain with the intrinsic Lipschitz field) -- @realizes K_1(map on the indicated domain into the indicated codomain with the intrinsic Lipschitz field) -- @realizes K_2(map on the indicated domain into the indicated codomain with the intrinsic Lipschitz field) -- @realizes L(map on the indicated domain into the indicated codomain with the intrinsic Lipschitz field) -- @realizes \mathcal{F}_L(map on the indicated domain into the indicated codomain with the intrinsic Lipschitz field)
  toFun : L1Vec d₁ → L1Vec d₂ -- @realizes f(function carrier)
  mapsTo : Set.MapsTo toFun K₁ K₂ -- @realizes K_1(domain); @realizes K_2(codomain)
  lipschitz : LipschitzOnWith L toFun K₁ -- @realizes \mathcal{F}_L(one-norm Lipschitz bound)

/-- For [two measures μ and ν on the same space](hyp:μ,ν), [their couplings](goal) are joint measures that [are probability measures](step:1), [have first marginal μ](step:2), and [have second marginal ν](step:3). -/
def couplings {X : Type*} [MeasurableSpace X] (μ ν : Measure X) :
    Set (Measure (X × X)) := {π | IsProbabilityMeasure π ∧ π.map Prod.fst = μ ∧ π.map Prod.snd = ν}

-- @node: def:distribution-distances
/-- For [two measures μ and ν on the same metric space](hyp:μ,ν), [the Wasserstein distance of order one](goal) is the infimum of expected ground distances over probability couplings with these marginals, allowing an infinite value. -/
def wasserstein1 {X : Type*} [MeasurableSpace X] [PseudoEMetricSpace X] -- @realizes \mu(coupling-infimum function on laws of the same metric space) -- @realizes \nu(coupling-infimum function on laws of the same metric space) -- @realizes \hat{\mu}(coupling-infimum function on laws of the same metric space) -- @realizes W(coupling-infimum function on laws of the same metric space)
    [BorelSpace X] (μ ν : Measure X) : ℝ≥0∞ :=
  Toolkit.Foundations.MeasureTheory.wasserstein1 μ ν -- @realizes W(reused infimum of one-norm coupling costs)

/-- For [row weights μ](hyp:μ) and [column weights ν](hyp:ν), [transport plans](goal) are matrices for which [μ is a probability vector](step:1), [ν is a probability vector](step:2), [all entries are nonnegative](step:3), [row sums equal μ](step:4), and [column sums equal ν](step:5). -/
def transportPlans {n m : ℕ} (μ : Fin n → ℝ) (ν : Fin m → ℝ) : -- @realizes \mu_i(row marginal coordinates of the supplied probability vector)
    Set (Fin n → Fin m → ℝ) := {T |
      μ ∈ probabilitySimplex n ∧ ν ∈ probabilitySimplex m ∧ -- @realizes \mu_i(nonnegative marginal coordinates of total mass one)
      (∀ i j, 0 ≤ T i j) ∧
      (∀ i, ∑ j, T i j = μ i) ∧ (∀ j, ∑ i, T i j = ν j)}
/-- For [a real matrix T](hyp:T), [plan entropy](goal) is one minus the sum, over all entries, of the entry times the natural logarithm of its absolute value, with a zero entry contributing zero. -/
def planEntropy {n m : ℕ} (T : Fin n → Fin m → ℝ) : ℝ := -- @realizes h(one minus the sum of T log T)
  1 - ∑ i, ∑ j, T i j * Real.log (T i j) -- @realizes h(entropy including the constant one)
/-- For [source locations x](hyp:x), [target locations y](hyp:y), and [a transport matrix T](hyp:T), [transport cost](goal) is the sum of one-norm distances between source and target locations, weighted by the corresponding matrix entries. -/
def transportCost {n m d : ℕ} (x : Fin n → L1Vec d) (y : Fin m → L1Vec d)
    (T : Fin n → Fin m → ℝ) : ℝ := ∑ i, ∑ j, dist (x i) (y j) * T i j

/-- For [source locations x](hyp:x), [target locations y](hyp:y), [source weights μ](hyp:μ), and [target weights ν](hyp:ν), [discrete Wasserstein cost](goal) is the real infimum of the one-norm transport costs of all plans with these marginals. -/
def discreteW1 {n m d : ℕ} (x : Fin n → L1Vec d) (y : Fin m → L1Vec d)
    (μ : Fin n → ℝ) (ν : Fin m → ℝ) : ℝ :=
  sInf (transportCost x y '' transportPlans μ ν)
/-- For [a regularization coefficient λ](hyp:lam), [source locations x](hyp:x), [target locations y](hyp:y), [source weights μ](hyp:μ), and [target weights ν](hyp:ν), [entropic transport cost](goal) is the real infimum over transport plans of the one-norm transport cost minus λ times plan entropy. -/
def entropicW1 {n m d : ℕ} (lam : ℝ) (x : Fin n → L1Vec d) (y : Fin m → L1Vec d) -- @realizes \lambda(infimum of one-norm ground cost minus lambda times entropy) -- @realizes W_{1,\lambda}(infimum of one-norm ground cost minus lambda times entropy)
    (μ : Fin n → ℝ) (ν : Fin m → ℝ) : ℝ :=
  sInf ((fun T => transportCost x y T - lam * planEntropy T) '' transportPlans μ ν)
/-- For [a regularization coefficient λ](hyp:lam), [source locations x](hyp:x), [target locations y](hyp:y), [source weights μ](hyp:μ), and [target weights ν](hyp:ν), [the Sinkhorn divergence](goal) is their entropic transport cost minus half the entropic self-transport cost of each weighted point cloud. -/
def sinkhornDivergence {n m d : ℕ} (lam : ℝ) (x : Fin n → L1Vec d) (y : Fin m → L1Vec d) -- @realizes S_\lambda(entropic cost with half of each self term subtracted)
    (μ : Fin n → ℝ) (ν : Fin m → ℝ) : ℝ :=
  entropicW1 lam x y μ ν - entropicW1 lam x x μ μ / 2 - entropicW1 lam y y ν ν / 2

/-- For [a nonnegative regularization coefficient λ](hyp:lam) and [probability laws μ and ν on real vectors](hyp:mu,nu), [law-level entropic transport cost](goal) is the infimum over their couplings of expected one-norm distance plus λ times relative entropy with respect to the product law. -/
def lawEntropicW1 {d : ℕ} (lam : ℝ≥0) (mu nu : ProbabilityMeasure (L1Vec d)) : ℝ≥0∞ := -- @realizes W_{1,\lambda}(coupling-infimum entropic transport on general probability laws)
  ⨅ pi : couplings (mu : Measure (L1Vec d)) (nu : Measure (L1Vec d)),
    (∫⁻ z, edist z.1 z.2 ∂pi.val) +
      (lam : ℝ≥0∞) * InformationTheory.klDiv pi.val
        ((mu : Measure (L1Vec d)).prod (nu : Measure (L1Vec d)))

-- @node: lawEntropicW1_ne_top
/-- For [a nonnegative regularization coefficient λ](hyp:lam) and [probability laws μ and ν](hyp:mu,nu), if [μ has a finite first moment](hyp:hmu) and [ν has a finite first moment](hyp:hnu), then [their law-level entropic transport cost is finite](goal). -/
lemma lawEntropicW1_ne_top {d : ℕ} (lam : ℝ≥0) (mu nu : ProbabilityMeasure (L1Vec d))
    (hmu : Integrable (fun x => ‖x‖) (mu : Measure (L1Vec d)))
    (hnu : Integrable (fun x => ‖x‖) (nu : Measure (L1Vec d))) :
    lawEntropicW1 lam mu nu ≠ ⊤ := by
  let : BorelSpace (L1Vec d) := ⟨rfl⟩
  let rho : Measure (L1Vec d × L1Vec d) :=
    (mu : Measure (L1Vec d)).prod (nu : Measure (L1Vec d))
  have hrho : rho ∈ couplings (mu : Measure _) (nu : Measure _) := by
    refine ⟨inferInstance, ?_, ?_⟩ <;> simp [rho]
  have hfirst : Integrable (fun z : L1Vec d × L1Vec d => z.1) rho := by
    exact (integrable_norm_iff (by fun_prop)).mp (hmu.comp_fst (nu : Measure (L1Vec d)))
  have hsecond : Integrable (fun z : L1Vec d × L1Vec d => z.2) rho := by
    exact (integrable_norm_iff (by fun_prop)).mp (hnu.comp_snd (mu : Measure (L1Vec d)))
  have hcost : (∫⁻ z : L1Vec d × L1Vec d, edist z.1 z.2 ∂rho) < ⊤ :=
    lintegral_edist_lt_top hfirst hsecond
  apply ne_of_lt
  calc
    lawEntropicW1 lam mu nu ≤ (∫⁻ z, edist z.1 z.2 ∂rho) +
        (lam : ℝ≥0∞) * InformationTheory.klDiv rho rho :=
      iInf_le_of_le ⟨rho, hrho⟩ le_rfl
    _ = ∫⁻ z, edist z.1 z.2 ∂rho := by rw [InformationTheory.klDiv_self]; simp
    _ < ⊤ := hcost

/-- For [a nonnegative regularization coefficient λ](hyp:lam) that [is strictly positive](hyp:_hlam), and [probability laws μ and ν](hyp:mu,nu) with [finite first moment for μ](hyp:_hmu) and [finite first moment for ν](hyp:_hnu), [the law-level Sinkhorn divergence](goal) is their entropic transport cost minus half of each law's entropic self-transport cost, expressed as a real number. -/
def lawSinkhornDivergence {d : ℕ} (lam : ℝ≥0) (_hlam : 0 < lam) -- @realizes \lambda(strictly positive transport regularization)
    (mu nu : ProbabilityMeasure (L1Vec d))
    (_hmu : Integrable (fun x => ‖x‖) (mu : Measure (L1Vec d)))
    (_hnu : Integrable (fun x => ‖x‖) (nu : Measure (L1Vec d))) : ℝ := -- @realizes S_\lambda(general-law entropic comparison with half of each self term removed)
  (lawEntropicW1 lam mu nu).toReal -
    (lawEntropicW1 lam mu mu).toReal / 2 - (lawEntropicW1 lam nu nu).toReal / 2

/-- For [a distance threshold ε](hyp:eps) and [a set A](hyp:A), [the strict internal covering number](goal) is the infimum of the cardinalities of subsets of A whose open ε-balls cover A, with infinity allowed. -/
def strictCoveringNumber {E : Type*} [PseudoEMetricSpace E] -- @realizes \mathcal{N}(least cardinality of a strict internal cover of the indicated set)
    (eps : ℝ≥0∞) (A : Set E) : ℕ∞ := -- @realizes S(set in the ambient metric space to be covered)
  ⨅ C : {C : Set E // C ⊆ A ∧
    SetRel.IsCover {p : E × E | edist p.1 p.2 < eps} A C}, C.val.encard

-- @node: def:lemma-sup-wasserstein-empirical-covering
/-- For [a distance threshold ε](hyp:eps), [a vector-valued function class F](hyp:F), and [a sample size n](hyp:n), [the empirical one-norm covering number](goal) is the supremum over all n-point input samples of the strict internal covering number of the evaluation vectors, using the unnormalized sum of absolute differences across observations and coordinates. -/
def empiricalL1CoveringNumber {X : Type*} {d : ℕ} (eps : ℝ≥0∞) -- @realizes \mathcal{F}(supremum over input samples of unnormalized one-norm evaluation covers) -- @realizes d'(supremum over input samples of unnormalized one-norm evaluation covers) -- @realizes d_1(supremum over input samples of unnormalized one-norm evaluation covers) -- @realizes d_2(supremum over input samples of unnormalized one-norm evaluation covers) -- @realizes \mathcal{N}_1(supremum over input samples of unnormalized one-norm evaluation covers)
    (F : Set (X → L1Vec d)) (n : ℕ) : ℕ∞ :=
  ⨆ x : Fin n → X, strictCoveringNumber eps
    ((fun f : X → L1Vec d =>
      WithLp.toLp 1 (fun ij : Fin n × Fin d => (f (x ij.1)).ofLp ij.2)) '' F)

/-- For [two real evaluation vectors u and w](hyp:u,w), [their averaged one-norm distance](goal) is the sum of absolute coordinate differences divided by their length, with value zero when the length is zero. -/
def averagedL1 {m : ℕ} (u w : Fin m → ℝ) : ℝ := -- @realizes m(averaged one-norm distance on length-m scalar evaluation vectors)
  (m : ℝ)⁻¹ * ∑ i, |u i - w i|

/-- For [a real distance threshold ε](hyp:eps), [a scalar function class G](hyp:G), and [a sample size m](hyp:m), assuming [every function in G takes values between zero and one](hyp:_hG), [the averaged empirical covering number](goal) is the supremum over m-point samples of the smallest cardinality of a strict internal ε-cover of the evaluation vectors in averaged one-norm distance. -/
def N1avg {X : Type*} (eps : ℝ) (G : Set (X → ℝ)) (m : ℕ)
    (_hG : ∀ g ∈ G, ∀ x, g x ∈ Set.Icc (0 : ℝ) 1) : ℕ∞ := -- @realizes \mathcal{G}(class of functions with values in the closed unit interval)
  ⨆ x : Fin m → X,
    ⨅ C : {C : Set (Fin m → ℝ) //
      C ⊆ (fun g : X → ℝ => fun i => g (x i)) '' G ∧
      SetRel.IsCover {p | averagedL1 p.1 p.2 < eps}
        ((fun g : X → ℝ => fun i => g (x i)) '' G) C}, C.val.encard

/-- For [a real separation threshold ε](hyp:eps), [a scalar function class G](hyp:G), and [a sample size m](hyp:m), assuming [every function in G takes values between zero and one](hyp:_hG), [the averaged empirical packing number](goal) is the supremum over m-point samples of the cardinalities of sets of evaluation vectors whose distinct members have averaged one-norm distance at least ε. -/
def M1avg {X : Type*} (eps : ℝ) (G : Set (X → ℝ)) (m : ℕ)
    (_hG : ∀ g ∈ G, ∀ x, g x ∈ Set.Icc (0 : ℝ) 1) : ℕ∞ := -- @realizes \mathcal{G}(class of functions with values in the closed unit interval)
  ⨆ x : Fin m → X,
    ⨆ C : {C : Set (Fin m → ℝ) //
      C ⊆ (fun g : X → ℝ => fun i => g (x i)) '' G ∧
      ∀ u ∈ C, ∀ w ∈ C, u ≠ w → eps ≤ averagedL1 u w}, C.val.encard
end
end Papers.TbsNeuralCausalPi
