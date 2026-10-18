module
public import Papers.TbsNeuralCausalPi.Helpers.NetworkMeasurability
public import Papers.TbsNeuralCausalPi.Setup.EmpiricalAdmissibility
/-! # Standard Borel parameters for all stored network widths

The finite width selector and the real affine coefficients are explicit.
Unused branches of the parameter tree allow ordinary finite products throughout,
so no measurability condition is imposed on an arbitrary subclass of networks.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
noncomputable section

-- @node: networkBorelParameters
/-- For [input dimension](hyp:din), [output dimension](hyp:dout), and [hidden-width bound](hyp:W),
[the network parameter space indexed by depth](goal) consists of [an output weight matrix and
bias vector at depth zero](step:1), and [a finite width selector, padded affine coefficients,
and a continuation parameter for every possible selected width at each positive depth](step:2). -/
abbrev networkBorelParameters (din dout W : ℕ) : ℕ → Type
  | 0 => (Fin dout → Fin din → ℝ) × (Fin dout → ℝ)
  | L + 1 => Fin (W + 1) ×
      ((Fin (W + 1) → Fin din → ℝ) × (Fin (W + 1) → ℝ) ×
        (∀ width : Fin (W + 1), networkBorelParameters width dout W L))

-- @node: networkBorelParameters_measurableSpace
/-- For [input dimension](hyp:din), [output dimension](hyp:dout), [hidden-width bound](hyp:W),
and [depth](hyp:L), [the network parameter space carries the recursively defined product
measurable structure](goal). -/
instance networkBorelParameters_measurableSpace (din dout W L : ℕ) :
    MeasurableSpace (networkBorelParameters din dout W L) := by
  induction L generalizing din with
  | zero => exact inferInstanceAs (MeasurableSpace
      ((Fin dout → Fin din → ℝ) × (Fin dout → ℝ)))
  | succ L ih =>
    letI := fun width : Fin (W + 1) => ih width
    exact inferInstanceAs (MeasurableSpace (Fin (W + 1) ×
      ((Fin (W + 1) → Fin din → ℝ) × (Fin (W + 1) → ℝ) ×
        (∀ width : Fin (W + 1), networkBorelParameters width dout W L))))

-- @node: networkBorelParameters_standardBorelSpace
/-- For [input dimension](hyp:din), [output dimension](hyp:dout), [hidden-width bound](hyp:W),
and [depth](hyp:L), [the network parameter space has a standard Borel structure](goal). -/
instance networkBorelParameters_standardBorelSpace (din dout W L : ℕ) :
    StandardBorelSpace (networkBorelParameters din dout W L) := by
  induction L generalizing din with
  | zero => exact inferInstanceAs (StandardBorelSpace
      ((Fin dout → Fin din → ℝ) × (Fin dout → ℝ)))
  | succ L ih =>
    letI := fun width : Fin (W + 1) => ih width
    exact inferInstanceAs (StandardBorelSpace (Fin (W + 1) ×
      ((Fin (W + 1) → Fin din → ℝ) × (Fin (W + 1) → ℝ) ×
        (∀ width : Fin (W + 1), networkBorelParameters width dout W L))))

-- @node: networkBorelParameters_nonempty
/-- For [input dimension](hyp:din), [output dimension](hyp:dout), [hidden-width bound](hyp:W),
and [depth](hyp:L), [the network parameter space is nonempty](goal). -/
instance networkBorelParameters_nonempty (din dout W L : ℕ) :
    Nonempty (networkBorelParameters din dout W L) := by
  induction L generalizing din with
  | zero => exact ⟨(fun _ _ => 0), (fun _ => 0)⟩
  | succ L ih =>
    exact ⟨⟨0, (fun _ _ => 0), (fun _ => 0),
      (fun width => Classical.choice (ih width))⟩⟩

-- @node: networkBorelDecode
/-- Given [a depth](hyp:L), [the network decoder](goal) turns a parameter tree into a ReLU
network: [at depth zero it uses the stored output weights and biases](step:1), and
[at positive depth it prepends the affine layer of the selected width to the recursively
decoded continuation for that width](step:2). -/
def networkBorelDecode {din dout W : ℕ} :
    (L : ℕ) → networkBorelParameters din dout W L → ReLUNet din dout W L
  | 0, p => {
      hidden := []
      depth := rfl
      widths := by simp
      firstInput := by simp
      compatible := List.isChain_nil
      outputWeight := p.1
      outputBias := p.2 }
  | L + 1, p =>
      prependNet (⟨din, p.1, (fun j i => p.2.1 (Fin.castLE (by omega) j) i),
        (fun j => p.2.2.1 (Fin.castLE (by omega) j))⟩ : AffineLayer)
        rfl (by exact Nat.le_of_lt_succ p.1.isLt)
        (networkBorelDecode L (p.2.2.2 p.1))

-- @node: networkBorelDecode_succ_eval
/-- For a parameter tree and an input vector, [evaluating the decoded network of positive
depth equals evaluating its selected continuation on the coordinatewise ReLU of the
selected affine transformation of the input](goal). -/
lemma networkBorelDecode_succ_eval {din dout W L : ℕ}
    (p : networkBorelParameters din dout W (L + 1)) (x : L1Vec din) :
    (networkBorelDecode (L + 1) p).eval x =
      (networkBorelDecode L (p.2.2.2 p.1)).eval
        (WithLp.toLp 1 (fun j : Fin p.1 => max 0
          ((∑ i : Fin din, p.2.1 (Fin.castLE (by omega) j) i * x.ofLp i) +
            p.2.2.1 (Fin.castLE (by omega) j)))) := by
  rw [networkBorelDecode]
  erw [prependNet_eval]
  congr 1
  simp [layerVector, reluLayer, AffineLayer.apply, AffineLayer.input, AffineLayer.output]
  rfl

-- @node: networkBorelDecode_eval_measurable
/-- [Evaluation of the decoded ReLU network is jointly measurable in its parameter tree
and input vector, for any input dimension, output dimension, width bound, and depth](goal). -/
@[fun_prop] lemma networkBorelDecode_eval_measurable (din dout W L : ℕ) :
    Measurable (fun p : networkBorelParameters din dout W L × L1Vec din =>
      (networkBorelDecode L p.1).eval p.2) := by
  induction L generalizing din with
  | zero =>
    change Measurable (fun p :
      ((Fin dout → Fin din → ℝ) × (Fin dout → ℝ)) × L1Vec din =>
      WithLp.toLp 1 (fun j =>
        (∑ i, p.1.1 j i * (if h : i.val < din then p.2.ofLp ⟨i.val, h⟩ else 0)) +
          p.1.2 j))
    simp only [dif_pos (Fin.isLt _)]
    fun_prop
  | succ L ih =>
    let Rest := (Fin (W + 1) → Fin din → ℝ) × (Fin (W + 1) → ℝ) ×
      (∀ width : Fin (W + 1), networkBorelParameters width dout W L)
    have hbranch : Measurable (fun p : Fin (W + 1) × (Rest × L1Vec din) =>
        (networkBorelDecode (L + 1) (p.1, p.2.1)).eval p.2.2) := by
      apply measurable_from_prod_countable_right
      intro width
      have htail : Measurable (fun y : Rest × L1Vec din => y.1.2.2 width) := by
        dsimp [Rest]
        fun_prop
      have hinput : Measurable (fun y : Rest × L1Vec din =>
          WithLp.toLp 1 (fun j : Fin width => max 0
            ((∑ i : Fin din, y.1.1 (Fin.castLE (by omega) j) i * y.2.ofLp i) +
              y.1.2.1 (Fin.castLE (by omega) j)))) := by
        dsimp [Rest]
        fun_prop
      have h := (ih width).comp (htail.prodMk hinput)
      convert h using 1
      funext y
      exact networkBorelDecode_succ_eval (width, y.1) y.2
    have hmap : Measurable (fun p : networkBorelParameters din dout W (L + 1) ×
        L1Vec din => ((p.1.1, (p.1.2, p.2)) : Fin (W + 1) × (Rest × L1Vec din))) := by
      change Measurable (fun p : (Fin (W + 1) × Rest) × L1Vec din =>
        (p.1.1, (p.1.2, p.2)))
      exact measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)
    have heq : (fun p : networkBorelParameters din dout W (L + 1) × L1Vec din =>
        (networkBorelDecode (L + 1) p.1).eval p.2) =
        (fun p : networkBorelParameters din dout W (L + 1) × L1Vec din =>
          (networkBorelDecode (L + 1) (p.1.1, p.1.2)).eval p.2) := by
      funext ⟨⟨width, rest⟩, x⟩
      rfl
    rw [heq]
    intro s hs
    exact hmap (hbranch hs)

-- @node: networkBorelDecode_eval_surjective
/-- [Every ReLU network with the specified dimensions, hidden-width bound, and depth has
a parameter tree whose decoded network gives exactly the same output at every input](goal). -/
lemma networkBorelDecode_eval_surjective {din dout W L : ℕ}
    (q : ReLUNet din dout W L) :
    ∃ p : networkBorelParameters din dout W L,
      (networkBorelDecode L p).eval = q.eval := by
  classical
  induction L generalizing din with
  | zero =>
    rcases q with ⟨ls, hd, hw, hf, hc, ow, ob⟩
    have hs : ls = [] := List.length_eq_zero_iff.mp hd
    subst ls
    exact ⟨(ow, ob), rfl⟩
  | succ L ih =>
    obtain ⟨⟨a, width, A, B⟩, hl, hw, r, rfl⟩ := exists_relu_head q
    change a = din at hl
    subst a
    change width ≤ W at hw
    obtain ⟨p, hp⟩ := ih r
    let width' : Fin (W + 1) := ⟨width, Nat.lt_succ_of_le hw⟩
    let tails : ∀ v : Fin (W + 1), networkBorelParameters v dout W L :=
      Function.update (fun v => Classical.ofNonempty) width' p
    let weights : Fin (W + 1) → Fin din → ℝ :=
      fun j i => if h : j.val < width then A ⟨j.val, h⟩ i else 0
    let biases : Fin (W + 1) → ℝ :=
      fun j => if h : j.val < width then B ⟨j.val, h⟩ else 0
    refine ⟨(width', weights, biases, tails), ?_⟩
    have ht : tails width' = p := by unfold tails; exact Function.update_self ..
    have hweights : (fun (j : Fin width) (i : Fin din) =>
        weights (Fin.castLE (by omega) j) i) = A := by
      funext j i
      simp [weights]
    have hbiases : (fun j : Fin width => biases (Fin.castLE (by omega) j)) = B := by
      funext j
      simp [biases]
    funext x
    rw [networkBorelDecode_succ_eval]
    change (networkBorelDecode L (tails width')).eval _ = _
    rw [ht]
    erw [hp]
    erw [prependNet_eval]
    congr 1
    simp [layerVector, reluLayer, AffineLayer.apply, AffineLayer.input,
      AffineLayer.output, weights, biases]
    funext j
    have hj : j.val < width := j.isLt
    simp only [if_pos hj]
    rfl

-- @node: reluNetwork_borelParametrizedClass
/-- [The class of functions represented by ReLU networks with fixed input and output
dimensions, hidden-width bound, and depth admits a standard Borel parameter space
with jointly measurable evaluation](goal). -/
lemma reluNetwork_borelParametrizedClass (din dout W L : ℕ) :
    BorelParametrizedClass (NN din dout W L) := by
  have heq : NN din dout W L =
      Set.range (fun p : networkBorelParameters din dout W L =>
        (networkBorelDecode L p).eval) := by
    ext f
    constructor
    · rintro ⟨q, rfl⟩
      exact networkBorelDecode_eval_surjective q
    · rintro ⟨p, rfl⟩
      exact ⟨networkBorelDecode L p, rfl⟩
  rw [heq]
  exact borelParametrizedClass_range _ (networkBorelDecode_eval_measurable din dout W L)

-- @node: positiveSimplexParameters
/-- For [a number of components](hyp:n), [the positive simplex parameter space](goal)
consists of probability weight vectors with every component strictly positive. -/
abbrev positiveSimplexParameters (n : ℕ) :=
  {p : Fin n → ℝ // p ∈ stdSimplex ℝ (Fin n) ∧ ∀ i, 0 < p i}

-- @node: positiveSimplexParameters_measurableSpace
/-- For [a number of components](hyp:n), [the positive simplex parameter space carries
the measurable structure inherited from the real coordinate space](goal). -/
instance positiveSimplexParameters_measurableSpace (n : ℕ) :
    MeasurableSpace (positiveSimplexParameters n) :=
  inferInstanceAs (MeasurableSpace {p : Fin n → ℝ //
    p ∈ stdSimplex ℝ (Fin n) ∧ ∀ i, 0 < p i})

-- @node: positiveSimplexParameters_standardBorelSpace
/-- For [a number of components](hyp:n), [the space of strictly positive probability
weight vectors has a standard Borel structure](goal). -/
instance positiveSimplexParameters_standardBorelSpace (n : ℕ) :
    StandardBorelSpace (positiveSimplexParameters n) := by
  have hpos : MeasurableSet {p : Fin n → ℝ | ∀ i, 0 < p i} := by
    have heq : {p : Fin n → ℝ | ∀ i, 0 < p i} =
        ⋂ i : Fin n, {p : Fin n → ℝ | 0 < p i} := by
      ext p
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
    rw [heq]
    exact MeasurableSet.iInter
      (fun i : Fin n => (show MeasurableSet {p : Fin n → ℝ | 0 < p i} from
        measurableSet_lt measurable_const (measurable_pi_apply i)))
  exact ((isClosed_stdSimplex ℝ (Fin n)).measurableSet.inter hpos).standardBorel

-- @node: generatorBorelParameters
/-- For [a number of mixture components](hyp:n), [an output dimension](hyp:d),
[component chart dimensions](hyp:dC), [a first-stage width bound](hyp:W1) and
[depth](hyp:L1), and [a second-stage width bound](hyp:W2) and [depth](hyp:L2),
[the generator parameter space](goal) is the product of first-stage network parameter
trees, second-stage network parameter trees, and strictly positive mixture weights. -/
abbrev generatorBorelParameters (n d : ℕ) (dC : Fin n → ℕ) (W1 L1 W2 L2 : ℕ) :=
  (∀ i, networkBorelParameters 1 (dC i) W1 L1) ×
    (∀ i, networkBorelParameters (dC i) d W2 L2) × positiveSimplexParameters n

-- @node: generatorBorelDecode
/-- Given [a strictly positive temperature](hyp:htau) and [network parameter trees and
positive mixture weights](hyp:p), [the decoded three-part generator](goal) uses
[the decoded first-stage networks](step:1), [the decoded second-stage networks](step:2),
[the stored mixture weights](step:3), [their unit-simplex constraint](step:4),
[their strict positivity](step:5), and [the positive temperature](step:6). -/
def generatorBorelDecode {n d : ℕ} {dC : Fin n → ℕ} {W1 L1 W2 L2 : ℕ}
    {tau : ℝ} (htau : 0 < tau)
    (p : generatorBorelParameters n d dC W1 L1 W2 L2) :
    ThreePartGenerator n d dC W1 L1 W2 L2 tau where
  g1 := fun i => networkBorelDecode L1 (p.1 i)
  g2 := fun i => networkBorelDecode L2 (p.2.1 i)
  p := p.2.2.val
  weights := p.2.2.property.1
  positiveWeights := p.2.2.property.2
  temperature := htau

-- @node: generatorBorelDecode_eval_measurable
/-- If [the temperature is strictly positive](hyp:htau), [evaluation of the decoded
three-part generator is jointly measurable in its parameters and its two random input
vectors](goal). -/
@[fun_prop] lemma generatorBorelDecode_eval_measurable
    {n d : ℕ} {dC : Fin n → ℕ} {W1 L1 W2 L2 : ℕ}
    {tau : ℝ} (htau : 0 < tau) :
    Measurable (fun p : generatorBorelParameters n d dC W1 L1 W2 L2 ×
        ((Fin n → ℝ) × (Fin n → ℝ)) =>
      (generatorBorelDecode htau p.1).eval p.2) := by
  unfold ThreePartGenerator.eval gumbelSoftmaxMix
  simp only [generatorBorelDecode, if_neg htau.ne']
  have hnz (p : generatorBorelParameters n d dC W1 L1 W2 L2 ×
      ((Fin n → ℝ) × (Fin n → ℝ))) (i : Fin n) : p.1.2.2.val i ≠ 0 :=
    ne_of_gt (p.1.2.2.property.2 i)
  simp only [softmaxWeights, if_neg (hnz _ _)]
  apply scm_toLp_measurable.comp
  apply measurable_pi_lambda
  intro j
  apply Finset.measurable_sum
  intro i _
  apply Measurable.mul
  · have hfirst := (networkBorelDecode_eval_measurable 1 (dC i) W1 L1).comp
      (show Measurable (fun p : generatorBorelParameters n d dC W1 L1 W2 L2 ×
          ((Fin n → ℝ) × (Fin n → ℝ)) =>
        (p.1.1 i, WithLp.toLp 1 (fun _ : Fin 1 => p.2.1 i))) by fun_prop)
    have hsecond := (networkBorelDecode_eval_measurable (dC i) d W2 L2).comp
      ((show Measurable (fun p : generatorBorelParameters n d dC W1 L1 W2 L2 ×
          ((Fin n → ℝ) × (Fin n → ℝ)) => p.1.2.1 i) by fun_prop).prodMk hfirst)
    exact ((measurable_pi_apply j).comp scm_ofLp_measurable).comp hsecond
  · have hexp (k : Fin n) : Measurable (fun p :
        generatorBorelParameters n d dC W1 L1 W2 L2 ×
          ((Fin n → ℝ) × (Fin n → ℝ)) =>
        Real.exp ((Real.log (p.1.2.2.val k) + p.2.2 k) / tau)) := by
      exact (((((measurable_pi_apply k).comp
        (measurable_subtype_coe.comp measurable_fst.snd.snd)).log).add
          ((measurable_pi_apply k).comp measurable_snd.snd)).div_const tau).exp
    exact (hexp i).div (Finset.measurable_sum _ (fun k _ => hexp k))

-- @node: generatorBorelDecode_eval_surjective
/-- At [a strictly positive temperature](hyp:htau), [every three-part generator has
parameters whose decoded generator gives exactly the same output at every input](goal). -/
lemma generatorBorelDecode_eval_surjective {n d : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ} (htau : 0 < tau)
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau) :
    ∃ p : generatorBorelParameters n d dC W1 L1 W2 L2,
      (generatorBorelDecode htau p).eval = q.eval := by
  choose p1 h1 using fun i => networkBorelDecode_eval_surjective (q.g1 i)
  choose p2 h2 using fun i => networkBorelDecode_eval_surjective (q.g2 i)
  refine ⟨(p1, p2, ⟨q.p, q.weights, q.positiveWeights⟩), ?_⟩
  funext z
  simp only [ThreePartGenerator.eval, generatorBorelDecode, h1, h2]

end
end Papers.TbsNeuralCausalPi
