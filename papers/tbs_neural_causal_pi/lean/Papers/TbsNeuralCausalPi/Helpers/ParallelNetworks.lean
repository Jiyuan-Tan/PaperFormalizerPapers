module
public import Papers.TbsNeuralCausalPi.Setup.Networks
/-! # Parallel assembly of finite ReLU networks -/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open scoped NNReal
noncomputable section
set_option linter.style.whitespace false

-- @node: layerVector
/-- For [an affine layer](hyp:l) and [a finite input vector](hyp:x), [the layer's
ReLU output vector](goal) is obtained by extending the input by zeros, applying
the affine layer, and replacing negative entries by zero. -/
def layerVector {k : ℕ} (l : AffineLayer) (x : L1Vec k) : L1Vec l.output :=
  WithLp.toLp 1 (fun j => reluLayer l
    (fun i => if h : i < k then x.ofLp ⟨i, h⟩ else 0) j.val)

-- @node: layerVector_extend
/-- For [an affine layer](hyp:l) and [an input vector](hyp:x), [extending the
finite ReLU output vector by zeros gives the same sequence as applying the ReLU
layer directly to the input extended by zeros](goal). -/
lemma layerVector_extend {k : ℕ} (l : AffineLayer) (x : L1Vec k) :
    (fun i => if h : i < l.output then (layerVector l x).ofLp ⟨i, h⟩ else 0) =
      reluLayer l (fun i => if h : i < k then x.ofLp ⟨i, h⟩ else 0) := by
  funext i
  by_cases hi : i < l.output
  · simp [hi, layerVector]
  · simp [hi, reluLayer, AffineLayer.apply]

-- @node: finalWidth_cons
/-- For [an initial input dimension](hyp:k), [a first affine layer](hyp:l), and
[a list of subsequent layers](hyp:ls), [the final width of the full list equals
the final width of the subsequent layers started at the first layer's output
dimension](goal). -/
lemma finalWidth_cons (k : ℕ) (l : AffineLayer) (ls : List AffineLayer) :
    finalWidth k (l :: ls) = finalWidth l.output ls := by
  induction ls with
  | nil => rfl
  | cons a ls ih =>
    cases ls with
    | nil => rfl
    | cons b bs => exact ih

-- @node: prependNet
/-- Given [an affine layer](hyp:l) whose [input dimension matches the new
network input dimension](hyp:hl) and whose [output dimension is at most the width
budget](hyp:hw), and [a ReLU network accepting that layer's output](hyp:q),
[the network formed by prepending the layer](goal) uses it as one additional
hidden ReLU layer and retains the original network's affine output map. -/
def prependNet {k o W L : ℕ} (l : AffineLayer) (hl : l.input = k)
    (hw : l.output ≤ W) (q : ReLUNet l.output o W L) : ReLUNet k o W (L+1) where
  hidden := l :: q.hidden
  depth := by simp [q.depth]
  widths := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hw
    · exact q.widths a ha
  firstInput := by
    intro a ha
    have heq : l = a := Option.some.inj ha
    exact heq ▸ hl
  compatible := q.compatible.cons (fun a ha => (q.firstInput a ha).symm)
  outputWeight := fun j i => q.outputWeight j (Fin.cast (finalWidth_cons k l q.hidden) i)
  outputBias := q.outputBias

-- @node: prependNet_eval
/-- Given [an affine layer](hyp:l) with [the required input dimension](hyp:hl)
and [output dimension within the width budget](hyp:hw), [a network accepting
its output](hyp:q), and [an input vector](hyp:x), [evaluating the network with
the layer prepended equals evaluating the original network on the layer's ReLU
output](goal). -/
lemma prependNet_eval {k o W L : ℕ} (l : AffineLayer) (hl : l.input = k)
    (hw : l.output ≤ W) (q : ReLUNet l.output o W L) (x : L1Vec k) :
    (prependNet l hl hw q).eval x = q.eval (layerVector l x) := by
  apply PiLp.ext
  intro j
  simp only [ReLUNet.eval, prependNet, List.foldl_cons]
  rw [layerVector_extend]
  exact congrArg (fun a : ℝ => a + q.outputBias j)
    (Finset.sum_equiv (finCongr (finalWidth_cons k l q.hidden))
      (fun _ => ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_univ _⟩) (fun _ _ => by rfl))

-- @node: exists_relu_head
/-- Every [ReLU network with at least one hidden layer](hyp:q) [can be written
as a first affine layer, with matching input dimension and output width within
the original budget, prepended to a network with one fewer hidden layer and the
same output dimension and width budget](goal). -/
lemma exists_relu_head {k o W L : ℕ} (q : ReLUNet k o W (L+1)) :
    ∃ l : AffineLayer, ∃ hl : l.input = k, ∃ hw : l.output ≤ W,
      ∃ r : ReLUNet l.output o W L, q = prependNet l hl hw r := by
  rcases q with ⟨ls, hd, hw, hf, hc, ow, ob⟩
  cases ls with
  | nil => simp at hd
  | cons l ls =>
    have hl : l.input = k := hf l rfl
    have hwidth : l.output ≤ W := hw l (by simp)
    have htail : ls.IsChain (fun a b => a.output = b.input) := hc.tail
    have hfirst : ∀ a, ls.head? = some a → a.input = l.output := by
      cases ls with
      | nil => simp
      | cons a as =>
        intro b hb
        have hab : a = b := Option.some.inj hb
        subst b
        exact ((List.isChain_cons_cons.mp hc).1).symm
    let r : ReLUNet l.output o W L := {
      hidden := ls
      depth := by simpa using hd
      widths := fun a ha => hw a (List.mem_cons_of_mem l ha)
      firstInput := hfirst
      compatible := htail
      outputWeight := fun j i => ow j (Fin.cast (finalWidth_cons k l ls).symm i)
      outputBias := ob }
    refine ⟨l, hl, hwidth, r, ?_⟩
    simp only [prependNet, r]
    congr

-- @node: linearInput
/-- For [a matrix](hyp:A) and [an input vector](hyp:x), [the linearly transformed
input](goal) has each entry equal to the sum of the corresponding matrix row
times the input entries. -/
def linearInput {a k : ℕ} (A : Fin a → Fin k → ℝ) (x : L1Vec k) : L1Vec a :=
  WithLp.toLp 1 (fun i => ∑ j, A i j * x.ofLp j)

-- @node: parallelFirstLayer
/-- Given [a finite family of affine layers](hyp:ls) and [matrices mapping a
common input into each layer's input space](hyp:A), [their parallel first
layer](goal) takes the common input, concatenates the component outputs, composes
each component's weights with its input matrix, and concatenates the component
biases. -/
abbrev parallelFirstLayer {m k : ℕ} (ls : Fin m → AffineLayer)
    (A : ∀ i, Fin (ls i).input → Fin k → ℝ) : AffineLayer :=
  ⟨k, ∑ i, (ls i).output,
    (fun j v => let z := finSigmaFinEquiv.symm j
      ∑ u, (ls z.1).2.2.1 z.2 u * A z.1 u v),
    (fun j => let z := finSigmaFinEquiv.symm j
      (ls z.1).2.2.2 z.2)⟩

-- @node: layerVector_apply
/-- For [an affine layer](hyp:l), [an input vector](hyp:x), and [an output
coordinate](hyp:j), [that coordinate of the ReLU output is the maximum of zero
and the weighted input sum plus the bias, with missing input entries set to
zero](goal). -/
lemma layerVector_apply {k : ℕ} (l : AffineLayer) (x : L1Vec k)
    (j : Fin l.output) :
    (layerVector l x).ofLp j = max 0 ((∑ u : Fin l.input,
      l.2.2.1 j u * (if h : u.val < k then x.ofLp ⟨u.val, h⟩ else 0)) + l.2.2.2 j) := by
  simp only [layerVector, WithLp.ofLp_toLp, reluLayer, AffineLayer.apply, dif_pos j.isLt]
  rfl

-- @node: parallelFirstLayer_eval
/-- Given [a family of affine layers](hyp:ls), [their linear input
maps](hyp:A), [a common input vector](hyp:x), [a component index](hyp:i), and
[an output coordinate within that component](hyp:j), [the corresponding entry
of the parallel layer's ReLU output equals that component's ReLU output after
its linear input map](goal). -/
lemma parallelFirstLayer_eval {m k : ℕ} (ls : Fin m → AffineLayer)
    (A : ∀ i, Fin (ls i).input → Fin k → ℝ)
    (x : L1Vec k) (i : Fin m) (j : Fin (ls i).output) :
    (layerVector (parallelFirstLayer ls A) x).ofLp (finSigmaFinEquiv ⟨i, j⟩) =
      (layerVector (ls i) (linearInput (A i) x)).ofLp j := by
  erw [layerVector_apply (parallelFirstLayer ls A) x (finSigmaFinEquiv ⟨i, j⟩),
    layerVector_apply (ls i) (linearInput (A i) x) j]
  dsimp only [parallelFirstLayer]
  erw [Equiv.symm_apply_apply]
  simp only [dif_pos (Fin.isLt _)]
  congr 2
  simp only [linearInput, WithLp.ofLp_toLp, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  erw [dif_pos v.isLt]
  exact mul_assoc _ _ _

-- @node: parallelProjection
/-- Given [the dimensions of a finite collection of vector blocks](hyp:a) and
[a chosen block index](hyp:i), [the block projection matrix](goal) has entry one
when its column is the concatenated position of its row in the chosen block,
and entry zero otherwise. -/
def parallelProjection {m : ℕ} (a : Fin m → ℕ) (i : Fin m) :
    Fin (a i) → Fin (∑ j, a j) → ℝ :=
  fun u v => if v = finSigmaFinEquiv ⟨i, u⟩ then 1 else 0

-- @node: parallelProjection_eval
/-- For [a collection of block dimensions](hyp:a), [a chosen block](hyp:i),
[a vector in the concatenated space](hyp:x), and [a coordinate within the chosen
block](hyp:u), [applying the block projection returns the original vector's
entry at that coordinate's concatenated position](goal). -/
lemma parallelProjection_eval {m : ℕ} (a : Fin m → ℕ) (i : Fin m)
    (x : L1Vec (∑ j, a j)) (u : Fin (a i)) :
    (linearInput (parallelProjection a i) x).ofLp u =
      x.ofLp (finSigmaFinEquiv ⟨i, u⟩) := by
  classical
  simp [linearInput, parallelProjection]

-- @node: parallelProjection_firstLayer
/-- Given [a family of affine layers](hyp:ls), [their linear input
maps](hyp:A), [a common input vector](hyp:x), and [a chosen component](hyp:i),
[projecting the parallel layer's ReLU output onto that component gives the
component layer's ReLU output evaluated after its linear input map](goal). -/
lemma parallelProjection_firstLayer {m k : ℕ} (ls : Fin m → AffineLayer)
    (A : ∀ i, Fin (ls i).input → Fin k → ℝ) (x : L1Vec k) (i : Fin m) :
    linearInput (parallelProjection (fun j => (ls j).output) i)
      (layerVector (parallelFirstLayer ls A) x) =
        layerVector (ls i) (linearInput (A i) x) := by
  apply PiLp.ext
  intro u
  exact (parallelProjection_eval (fun j => (ls j).output) i
    (layerVector (parallelFirstLayer ls A) x) u).trans
      (parallelFirstLayer_eval ls A x i u)

-- @node: affineNet
/-- For [a weight matrix](hyp:A) and [a bias vector](hyp:b), [the corresponding
zero-hidden-layer ReLU network](goal) has an empty hidden-layer list and uses
the given matrix and bias as its affine output map. -/
def affineNet {k o W : ℕ} (A : Fin o → Fin k → ℝ) (b : Fin o → ℝ) :
    ReLUNet k o W 0 where
  hidden := []
  depth := rfl
  widths := by simp
  firstInput := by simp
  compatible := List.isChain_nil
  outputWeight := A
  outputBias := b

-- @node: affineNet_eval
/-- For [a weight matrix](hyp:A), [a bias vector](hyp:b), [an input
vector](hyp:x), and [an output coordinate](hyp:j), [the affine network's output
at that coordinate is the corresponding matrix row times the input plus the
corresponding bias](goal). -/
lemma affineNet_eval {k o W : ℕ} (A : Fin o → Fin k → ℝ) (b : Fin o → ℝ)
    (x : L1Vec k) (j : Fin o) :
    ((affineNet (W := W) A b).eval x).ofLp j = (∑ i, A j i * x.ofLp i) + b j := by
  change (∑ i : Fin k, A j i * (if h : i.val < k then x.ofLp ⟨i.val, h⟩ else 0)) + b j = _
  simp only [dif_pos (Fin.isLt _)]

-- @node: zeroDepthNet_eval
/-- For [a scalar-output ReLU network with no hidden layers](hyp:q) and [an
input vector](hyp:x), [the scalar output is the sum of its output weights times
the input entries, plus its output bias](goal). -/
lemma zeroDepthNet_eval {a W : ℕ} (q : ReLUNet a 1 W 0) (x : L1Vec a) :
    (q.eval x).ofLp 0 =
      (∑ i : Fin a, q.outputWeight 0 (Fin.cast (by
        rw [List.length_eq_zero_iff.mp q.depth]; rfl) i) * x.ofLp i) + q.outputBias 0 := by
  rcases q with ⟨ls, hd, hw, hf, hc, ow, ob⟩
  have hs : ls = [] := List.length_eq_zero_iff.mp hd
  subst ls
  change (∑ i : Fin a, ow 0 i * (if h : i.val < a then x.ofLp ⟨i.val, h⟩ else 0)) + ob 0 = _
  simp only [dif_pos (Fin.isLt _)]
  rfl

-- @node: relu_parallel_linear_inputs
/-- Given [a common hidden-layer count](hyp:L), [a family of component input
dimensions](hyp:a), [scalar-output ReLU networks with those input dimensions,
the common depth, and a common width budget](hyp:q), and [linear maps from a
shared input space into the component input spaces](hyp:A), [there exists a
network of the same depth, with one output per component and width budget equal
to the number of components times the original budget, whose outputs equal the
component networks evaluated after their linear input maps](goal).

The component input dimensions may differ, allowing the construction to be
applied recursively after each hidden layer. -/
lemma relu_parallel_linear_inputs (L : ℕ) {m k W : ℕ}
    (a : Fin m → ℕ) (q : ∀ i, ReLUNet (a i) 1 W L)
    (A : ∀ i, Fin (a i) → Fin k → ℝ) :
    ∃ Q : ReLUNet k m (m*W) L,
      ∀ x i, (Q.eval x).ofLp i = ((q i).eval (linearInput (A i) x)).ofLp 0 := by
  classical
  induction L generalizing k a with
  | zero =>
    let w : ∀ i, Fin (a i) → ℝ := fun i u =>
      (q i).outputWeight 0 (Fin.cast (by
        rw [List.length_eq_zero_iff.mp (q i).depth]; rfl) u)
    refine ⟨affineNet (fun i v => ∑ u, w i u * A i u v)
      (fun i => (q i).outputBias 0), ?_⟩
    intro x i
    rw [affineNet_eval, zeroDepthNet_eval]
    change (∑ v : Fin k, (∑ u, w i u * A i u v) * x.ofLp v) + _ =
      (∑ u : Fin (a i), w i u * (∑ v, A i u v * x.ofLp v)) + _
    congr 1
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    exact mul_assoc _ _ _
  | succ L ih =>
    choose ls hl hw r hq using fun i => exists_relu_head (q i)
    let A' : ∀ i, Fin (ls i).input → Fin k → ℝ :=
      fun i u v => A i (Fin.cast (hl i) u) v
    let l := parallelFirstLayer ls A'
    obtain ⟨R, hR⟩ := ih (fun i => (ls i).output) r
      (fun i => parallelProjection (fun j => (ls j).output) i)
    have hwidth : l.output ≤ m*W := by
      change (∑ i, (ls i).output) ≤ m*W
      calc
        (∑ i, (ls i).output) ≤ ∑ _i : Fin m, W := Finset.sum_le_sum (fun i _ => hw i)
        _ = m*W := by simp
    refine ⟨prependNet l rfl hwidth R, ?_⟩
    intro x i
    erw [prependNet_eval, hR]
    have hprojection : linearInput (parallelProjection (fun j => (ls j).output) i)
        (layerVector l x) = layerVector (ls i) (linearInput (A' i) x) :=
      parallelProjection_firstLayer ls A' x i
    rw [hprojection, hq i, prependNet_eval]
    have hinput : layerVector (ls i) (linearInput (A' i) x) =
        layerVector (ls i) (linearInput (A i) x) := by
      apply PiLp.ext
      intro j
      rw [layerVector_apply, layerVector_apply]
      congr 2
      apply Finset.sum_congr rfl
      intro u hu
      have hui : u.val < a i := by simpa only [← hl i] using u.isLt
      erw [dif_pos u.isLt, dif_pos hui]
      rfl
    rw [hinput]

-- @node: linearInput_identity
/-- For [a finite input vector](hyp:x), [the linear input map with ones on the
diagonal and zeros elsewhere returns the vector unchanged](goal). -/
lemma linearInput_identity {k : ℕ} (x : L1Vec k) :
    linearInput (fun i j : Fin k => if j = i then 1 else 0) x = x := by
  classical
  apply PiLp.ext
  intro i
  simp [linearInput]

-- @node: relu_parallel_stack_constructed
/-- Given [a finite family of scalar-output ReLU networks with a common input
dimension, width budget, and depth](hyp:q), [there exists a network of the same
depth with one output per component and width budget equal to the number of
components times the original budget, whose outputs simultaneously reproduce
all component outputs on every input](goal). -/
lemma relu_parallel_stack_constructed {k m W L : ℕ} (q : Fin m → ReLUNet k 1 W L) :
    ∃ Q : ReLUNet k m (m*W) L,
      ∀ x j, (Q.eval x).ofLp j = ((q j).eval x).ofLp 0 := by
  obtain ⟨Q, hQ⟩ := relu_parallel_linear_inputs L (fun _ : Fin m => k) q
    (fun _ i j => if j = i then 1 else 0)
  refine ⟨Q, ?_⟩
  intro x j
  simpa only [linearInput_identity] using hQ x j

end
end Papers.TbsNeuralCausalPi
