module
public import Papers.TbsNeuralCausalPi.Helpers.SimulationActivationPolynomials
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.MvPolynomial.Variables
/-! # Polynomial grid comparisons for the actual separable generator

All components share one parameter assignment, with disjoint namespaces for
their stored network weights and for the transformed mixture weights. Fixing
the component activation masks gives an explicit polynomial for every grid
comparison. Final clipping adds only the two fixed boundary comparisons.
The polynomial sign-pattern count remains a separate obligation.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
noncomputable section


-- @node: simulationLayerVariables
/-- For [layer index k](hyp:k), [input width a](hyp:a), and [output width b](hyp:b),
[the layer's parameter indices](goal) consist of all triples with layer index k,
output index below b, and input index from zero through a, including the bias slot. -/
def simulationLayerVariables (k a b : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range b).product (Finset.range (a + 1))).image (fun ji => (k, ji))

-- @node: simulationLayerVariables_mem
/-- [A triple with layer index k, output index j, and input index i belongs to the
parameter set of a layer with input width a and output width b exactly when j is
below b and i is at most a](goal). -/
lemma simulationLayerVariables_mem (k a b j i : ℕ) :
    (k, j, i) ∈ simulationLayerVariables k a b ↔ j < b ∧ i ≤ a := by
  simp [simulationLayerVariables]

-- @node: simulationLayerVariables_card
/-- [The number of parameter indices for a layer with input width a and output
width b is at most b times (a + 1)](goal), counting one bias per output. -/
lemma simulationLayerVariables_card (k a b : ℕ) :
    (simulationLayerVariables k a b).card ≤ b * (a + 1) := by
  exact Finset.card_image_le.trans (by simp)

-- @node: simulationHiddenVariables
/-- The [parameter indices of a sequence of hidden layers](goal) are
[the empty set when there are no layers](step:1), and otherwise
[the union of the first layer's parameter indices and those of the remaining
layers, whose layer numbering starts one higher](step:2). -/
def simulationHiddenVariables : List AffineLayer → ℕ → Finset (ℕ × ℕ × ℕ)
  | [], _ => ∅
  | l :: ls, k => simulationLayerVariables k l.input l.output ∪
      simulationHiddenVariables ls (k + 1)

-- @node: simulationHiddenVariables_card
/-- If [every hidden layer has input and output widths at most w](hyp:hw),
[the number of hidden-layer parameter indices, starting at any layer index k,
is at most the number of layers times w times (w + 1)](goal). -/
lemma simulationHiddenVariables_card (ls : List AffineLayer) (k w : ℕ)
    (hw : ∀ l ∈ ls, l.input ≤ w ∧ l.output ≤ w) :
    (simulationHiddenVariables ls k).card ≤ ls.length * (w * (w + 1)) := by
  induction ls generalizing k with
  | nil => simp [simulationHiddenVariables]
  | cons l ls ih =>
    have hl := hw l (by simp)
    have ht := ih (k + 1) (fun a ha => hw a (by simp [ha]))
    calc
      _ ≤ (simulationLayerVariables k l.input l.output).card +
          (simulationHiddenVariables ls (k + 1)).card := Finset.card_union_le _ _
      _ ≤ w * (w + 1) + ls.length * (w * (w + 1)) :=
        Nat.add_le_add ((simulationLayerVariables_card _ _ _).trans
          (Nat.mul_le_mul hl.2 (Nat.add_le_add_right hl.1 1))) ht
      _ = _ := by simp only [List.length_cons]; ring

/-- If [every input polynomial uses only variables in S](hyp:hz),
[the affine output polynomial at coordinate j uses only this layer's parameter
indices together with S](goal). -/
-- @node: simulationAffinePolynomial_vars
lemma simulationAffinePolynomial_vars (l : AffineLayer) (k : ℕ)
    (z : ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ) (S : Finset (ℕ × ℕ × ℕ))
    (hz : ∀ a, (z a).vars ⊆ S) (j : ℕ) :
    (simulationAffinePolynomial l k z j).vars ⊆
      simulationLayerVariables k l.input l.output ∪ S := by
  classical
  unfold simulationAffinePolynomial
  split_ifs with hj
  · apply (MvPolynomial.vars_add_subset _ _).trans
    apply Finset.union_subset
    · apply (MvPolynomial.vars_sum_subset _ _).trans
      apply Finset.biUnion_subset.mpr
      intro i _
      apply (MvPolynomial.vars_mul _ _).trans
      apply Finset.union_subset
      · simp only [MvPolynomial.vars_X, Finset.singleton_subset_iff]
        apply Finset.mem_union_left
        exact (simulationLayerVariables_mem _ _ _ _ _).mpr ⟨hj, i.isLt⟩
      · exact (hz i.val).trans Finset.subset_union_right
    · simp only [MvPolynomial.vars_X, Finset.singleton_subset_iff]
      apply Finset.mem_union_left
      exact (simulationLayerVariables_mem _ _ _ _ _).mpr ⟨hj, Nat.zero_le _⟩
  · simp

-- @node: simulationReluPolynomial_vars
/-- If [every input polynomial uses only variables in S](hyp:hz),
[the output polynomial at coordinate j of the layer with a fixed activation mask
uses only this layer's parameter indices together with S](goal). -/
lemma simulationReluPolynomial_vars (l : AffineLayer) (k : ℕ) (active : ℕ → Bool)
    (z : ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ) (S : Finset (ℕ × ℕ × ℕ))
    (hz : ∀ a, (z a).vars ⊆ S) (j : ℕ) :
    (simulationReluPolynomial l k active z j).vars ⊆
      simulationLayerVariables k l.input l.output ∪ S := by
  unfold simulationReluPolynomial
  split_ifs
  · exact simulationAffinePolynomial_vars l k z S hz j
  · simp

-- @node: simulationHiddenPolynomial_vars
/-- If [every input polynomial uses only variables in S](hyp:hz),
[each output polynomial of the hidden layers with fixed activation masks uses
only the hidden-layer parameter indices, numbered from k, together with S](goal). -/
lemma simulationHiddenPolynomial_vars (ls : List AffineLayer) (k : ℕ)
    (masks : List (ℕ → Bool)) (z : ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ)
    (S : Finset (ℕ × ℕ × ℕ)) (hz : ∀ a, (z a).vars ⊆ S) (j : ℕ) :
    (simulationHiddenPolynomial ls k masks z j).vars ⊆ simulationHiddenVariables ls k ∪ S := by
  induction ls generalizing k masks z S with
  | nil => simpa [simulationHiddenPolynomial, simulationHiddenVariables] using hz j
  | cons l ls ih =>
    have h := ih (k + 1) masks.tail
      (simulationReluPolynomial l k (masks.headD (fun _ => false)) z)
      (simulationLayerVariables k l.input l.output ∪ S)
      (simulationReluPolynomial_vars l k _ z S hz)
    simpa only [simulationHiddenPolynomial, simulationHiddenVariables,
      Finset.union_assoc, Finset.union_left_comm] using h

-- @node: simulationNetworkVariables
/-- For [a ReLU network q](hyp:q) with [layer numbering starting at k](hyp:k),
[its parameter index set](goal) is the union of the indices of its hidden layers
and its final affine output layer. -/
def simulationNetworkVariables {din dout W L : ℕ} (q : ReLUNet din dout W L)
    (k : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  simulationHiddenVariables q.hidden k ∪
    simulationLayerVariables (k + q.hidden.length) (finalWidth din q.hidden) dout

-- @node: simulationNetworkPolynomialAt_vars
/-- If [every input polynomial uses only variables in S](hyp:hz),
[the network output polynomial at coordinate j with fixed activation masks uses
only the network's parameter indices, numbered from k, together with S](goal). -/
lemma simulationNetworkPolynomialAt_vars {din dout W L : ℕ} (q : ReLUNet din dout W L)
    (k : ℕ) (masks : List (ℕ → Bool)) (z : ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ)
    (S : Finset (ℕ × ℕ × ℕ)) (hz : ∀ a, (z a).vars ⊆ S) (j : Fin dout) :
    (simulationNetworkPolynomialAt q k masks z j).vars ⊆ simulationNetworkVariables q k ∪ S := by
  classical
  unfold simulationNetworkPolynomialAt
  apply (MvPolynomial.vars_add_subset _ _).trans
  apply Finset.union_subset
  · apply (MvPolynomial.vars_sum_subset _ _).trans
    apply Finset.biUnion_subset.mpr
    intro i _
    apply (MvPolynomial.vars_mul _ _).trans
    apply Finset.union_subset
    · simp only [MvPolynomial.vars_X, Finset.singleton_subset_iff]
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact (simulationLayerVariables_mem _ _ _ _ _).mpr ⟨j.isLt, i.isLt⟩
    · exact (simulationHiddenPolynomial_vars _ _ _ z S hz i.val).trans
        (Finset.union_subset_union Finset.subset_union_left (Finset.Subset.refl _))
  · simp only [MvPolynomial.vars_X, Finset.singleton_subset_iff]
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact (simulationLayerVariables_mem _ _ _ _ _).mpr ⟨j.isLt, Nat.zero_le _⟩

/-- Suppose [the initial input width is at most w](hyp:hdin),
[every layer's output width is at most w](hyp:hw),
[the first layer, if present, has the initial input width](hyp:hfirst), and
[each layer's output width equals the next layer's input width](hyp:hchain).
Then [every layer has both input and output widths at most w](goal). -/
-- @node: simulation_layer_width_bounds
lemma simulation_layer_width_bounds (ls : List AffineLayer) (din w : ℕ)
    (hdin : din ≤ w) (hw : ∀ l ∈ ls, l.output ≤ w)
    (hfirst : ∀ l, ls.head? = some l → l.input = din)
    (hchain : ls.IsChain (fun l l' => l.output = l'.input)) :
    ∀ l ∈ ls, l.input ≤ w ∧ l.output ≤ w := by
  induction ls generalizing din with
  | nil => simp
  | cons a ls ih =>
    have ha : a.input ≤ w := (hfirst a rfl).le.trans hdin
    have hac := List.isChain_cons.mp hchain
    have ht := ih a.output (hw a (by simp)) (fun l hl => hw l (by simp [hl]))
      (fun l hl => (hac.1 l hl).symm) hac.2
    intro l hl
    rcases List.mem_cons.mp hl with rfl | hl
    · exact ⟨ha, hw _ (by simp)⟩
    · exact ht l hl

-- @node: simulation_finalWidth_le
/-- If [the initial input width is at most w](hyp:hdin) and
[every hidden layer's output width is at most w](hyp:hw),
[the width entering the final affine layer is at most w](goal). -/
lemma simulation_finalWidth_le (ls : List AffineLayer) (din w : ℕ)
    (hdin : din ≤ w) (hw : ∀ l ∈ ls, l.output ≤ w) : finalWidth din ls ≤ w := by
  unfold finalWidth
  cases he : ls.getLast? with
  | none => simpa [he] using hdin
  | some l =>
    simp only [Option.map_some, Option.getD_some]
    exact hw l (List.mem_of_getLast? he)

/-- If [the input dimension is at most w](hyp:hdin),
[the output dimension is at most w](hyp:hdout), and
[the hidden-width budget is at most w](hyp:hW),
[the network's parameter index set has at most (L + 1) times w times (w + 1)
elements, where L is its number of hidden layers](goal). -/
-- @node: simulationNetworkVariables_card
lemma simulationNetworkVariables_card {din dout W L : ℕ} (q : ReLUNet din dout W L)
    (k w : ℕ) (hdin : din ≤ w) (hdout : dout ≤ w) (hW : W ≤ w) :
    (simulationNetworkVariables q k).card ≤ (L + 1) * (w * (w + 1)) := by
  have hw : ∀ l ∈ q.hidden, l.output ≤ w := fun l hl => (q.widths l hl).trans hW
  have hi := simulation_layer_width_bounds q.hidden din w hdin hw q.firstInput q.compatible
  have hf := simulation_finalWidth_le q.hidden din w hdin hw
  calc
    _ ≤ (simulationHiddenVariables q.hidden k).card +
        (simulationLayerVariables (k + q.hidden.length) (finalWidth din q.hidden) dout).card :=
      Finset.card_union_le _ _
    _ ≤ q.hidden.length * (w * (w + 1)) + w * (w + 1) :=
      Nat.add_le_add (simulationHiddenVariables_card _ _ _ hi)
        ((simulationLayerVariables_card _ _ _).trans
          (Nat.mul_le_mul hdout (Nat.add_le_add_right hf 1)))
    _ = _ := by rw [q.depth]; ring


/-- For [n mixture components](hyp:n), [the generator's variable index type](goal)
has separate indices for mixture amplitudes and for network parameters tagged
with their component and layer, output, and input indices. -/
-- @node: simulationGeneratorVariable
abbrev simulationGeneratorVariable (n : ℕ) := Fin n ⊕ (Fin n × (ℕ × ℕ × ℕ))

/-- For [a three-part generator q](hyp:q), [its polynomial parameter assignment](goal)
assigns [the transformed mixture amplitude to each mixture index](step:1) and
[the stored two-block network parameter to each component parameter index](step:2). -/
-- @node: simulationGeneratorParameters
def simulationGeneratorParameters {n d : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau) :
    simulationGeneratorVariable n → ℝ
  | .inl i => simulationMixtureAmplitude q.p tau i
  | .inr (i, v) => simulationTwoBlockParameters (q.g1 i) (q.g2 i) v

/-- For [a three-part generator q](hyp:q), [component i](hyp:i),
[first-block activation masks](hyp:masks), [scalar input u](hyp:u), and
[intermediate coordinate a](hyp:a), [the intermediate polynomial](goal) is the
first block's output polynomial when a is below the component's intermediate
dimension, and zero otherwise. -/
-- @node: simulationGeneratorIntermediate
def simulationGeneratorIntermediate {n d : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau)
    (i : Fin n) (masks : List (ℕ → Bool)) (u : ℝ) (a : ℕ) :
    MvPolynomial (ℕ × ℕ × ℕ) ℝ :=
  if ha : a < dC i then
    simulationNetworkPolynomialAt (q.g1 i) 0 masks
      (simulationInputPolynomial (WithLp.toLp 1 (fun _ : Fin 1 => u))) ⟨a, ha⟩
  else 0

-- @node: simulationGeneratorComponentPolynomial
/-- For [a three-part generator q](hyp:q), [component i](hyp:i),
[first-block activation masks](hyp:masks1), [second-block activation masks](hyp:masks2),
[scalar input u](hyp:u), and [output coordinate j](hyp:j),
[the component output polynomial](goal) composes the two blocks' polynomial
evaluations and labels every network variable with its component index. -/
def simulationGeneratorComponentPolynomial {n d : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau)
    (i : Fin n) (masks1 masks2 : List (ℕ → Bool)) (u : ℝ) (j : Fin d) :
    MvPolynomial (simulationGeneratorVariable n) ℝ :=
  MvPolynomial.rename (fun v => Sum.inr (i, v))
    (simulationNetworkPolynomialAt (q.g2 i) ((q.g1 i).hidden.length + 1) masks2
      (simulationGeneratorIntermediate q i masks1 u) j)

-- @node: simulationGeneratorIntermediate_degree
/-- [Every intermediate coordinate polynomial for a component with fixed
activation masks and scalar input has total degree at most L1 + 1, where L1
is the first block's hidden depth](goal). -/
lemma simulationGeneratorIntermediate_degree {n d : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau)
    (i : Fin n) (masks : List (ℕ → Bool)) (u : ℝ) (a : ℕ) :
    (simulationGeneratorIntermediate q i masks u a).totalDegree ≤ L1 + 1 := by
  unfold simulationGeneratorIntermediate
  split_ifs
  · simpa using simulationNetworkPolynomialAt_degree (q.g1 i) 0 0 masks
      (simulationInputPolynomial (WithLp.toLp 1 (fun _ : Fin 1 => u)))
      (fun _ => by simp [simulationInputPolynomial]) _
  · simp

/-- [Every component output polynomial with fixed activation masks and scalar
input has total degree at most L1 + L2 + 2, where L1 and L2 are the two blocks'
hidden depths](goal). -/
-- @node: simulationGeneratorComponentPolynomial_degree
lemma simulationGeneratorComponentPolynomial_degree {n d : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau)
    (i : Fin n) (masks1 masks2 : List (ℕ → Bool)) (u : ℝ) (j : Fin d) :
    (simulationGeneratorComponentPolynomial q i masks1 masks2 u j).totalDegree ≤
      L1 + L2 + 2 := by
  apply (MvPolynomial.totalDegree_rename_le _ _).trans
  have h := simulationNetworkPolynomialAt_degree (q.g2 i)
    ((q.g1 i).hidden.length + 1) (L1 + 1) masks2
    (simulationGeneratorIntermediate q i masks1 u)
    (simulationGeneratorIntermediate_degree q i masks1 u) j
  omega

/-- [For any component and scalar input, there exist activation masks of lengths
L1 and L2 for the two blocks that satisfy both blocks' activation-region conditions
at the stored parameters and make every component output polynomial evaluate
to the corresponding coordinate of the two-block network output](goal). -/
-- @node: simulationGeneratorComponentPolynomial_exists
lemma simulationGeneratorComponentPolynomial_exists {n d : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau) (i : Fin n) (u : ℝ) :
    ∃ masks1 masks2 : List (ℕ → Bool),
      masks1.length = L1 ∧ masks2.length = L2 ∧
      simulationActivationRegion (q.g1 i).hidden 0 masks1
        (simulationInputPolynomial (WithLp.toLp 1 (fun _ : Fin 1 => u)))
        (simulationTwoBlockParameters (q.g1 i) (q.g2 i)) ∧
      simulationActivationRegion (q.g2 i).hidden ((q.g1 i).hidden.length + 1) masks2
        (simulationGeneratorIntermediate q i masks1 u)
        (simulationTwoBlockParameters (q.g1 i) (q.g2 i)) ∧
      ∀ j : Fin d,
        MvPolynomial.eval (simulationGeneratorParameters q)
          (simulationGeneratorComponentPolynomial q i masks1 masks2 u j) =
          ((q.g2 i).eval ((q.g1 i).eval (WithLp.toLp 1 (fun _ : Fin 1 => u)))).ofLp j := by
  obtain ⟨m1, m2, h1, h2, hr1, hr2, he⟩ :=
    simulationTwoBlockPolynomial_exists (q.g1 i) (q.g2 i) (WithLp.toLp 1 (fun _ : Fin 1 => u))
  refine ⟨m1, m2, h1, h2, hr1, hr2, ?_⟩
  intro j
  rw [simulationGeneratorComponentPolynomial, MvPolynomial.eval_rename]
  exact (he j).2

/-- For [a three-part generator q](hyp:q),
[first-block masks for every component](hyp:masks1),
[second-block masks for every component](hyp:masks2),
[a draw of scalar component inputs and mixture noise](hyp:z),
[output coordinate j](hyp:j), and [a grid threshold](hyp:threshold),
[the grid comparison polynomial](goal) is the mixture numerator minus the
threshold times the mixture denominator, with the draw fixed in its coefficients. -/
-- @node: simulationGeneratorGridPolynomial
def simulationGeneratorGridPolynomial {n d : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau)
    (masks1 masks2 : Fin n → List (ℕ → Bool))
    (z : (Fin n → ℝ) × (Fin n → ℝ)) (j : Fin d) (threshold : ℝ) :
    MvPolynomial (simulationGeneratorVariable n) ℝ :=
  simulationMixtureComparison Sum.inl (fun i => Real.exp (z.2 i / tau))
    (fun i => simulationGeneratorComponentPolynomial q i (masks1 i) (masks2 i) (z.1 i) j)
    threshold

-- @node: simulationGeneratorGridPolynomial_degree
/-- [Every generator grid comparison polynomial with fixed activation masks,
input draw, coordinate, and threshold has total degree at most L1 + L2 + 3,
where L1 and L2 are the two blocks' hidden depths](goal). -/
lemma simulationGeneratorGridPolynomial_degree {n d : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau)
    (masks1 masks2 : Fin n → List (ℕ → Bool))
    (z : (Fin n → ℝ) × (Fin n → ℝ)) (j : Fin d) (threshold : ℝ) :
    (simulationGeneratorGridPolynomial q masks1 masks2 z j threshold).totalDegree ≤
      L1 + L2 + 3 := by
  exact simulationMixtureComparison_degree _ _ _ _
    (fun i => simulationGeneratorComponentPolynomial_degree q i _ _ _ j)

/-- [For every input and noise draw, there exist first- and second-block masks
of lengths L1 and L2 for every component such that, simultaneously for every
output coordinate and threshold, the generator output is at most the threshold
exactly when the comparison polynomial evaluated at the generator's parameters
is nonpositive, and is strictly below the threshold exactly when that polynomial
is negative](goal). -/
-- @node: simulationGenerator_grid_comparisons
lemma simulationGenerator_grid_comparisons {n d : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    ∃ masks1 masks2 : Fin n → List (ℕ → Bool),
      (∀ i, (masks1 i).length = L1 ∧ (masks2 i).length = L2) ∧
      ∀ (j : Fin d) (threshold : ℝ),
        ((q.eval z).ofLp j ≤ threshold ↔
          MvPolynomial.eval (simulationGeneratorParameters q)
            (simulationGeneratorGridPolynomial q masks1 masks2 z j threshold) ≤ 0) ∧
        ((q.eval z).ofLp j < threshold ↔
          MvPolynomial.eval (simulationGeneratorParameters q)
            (simulationGeneratorGridPolynomial q masks1 masks2 z j threshold) < 0) := by
  classical
  choose m1 m2 h1 h2 hr1 hr2 he using
    (fun i => simulationGeneratorComponentPolynomial_exists q i (z.1 i))
  refine ⟨m1, m2, fun i => ⟨h1 i, h2 i⟩, ?_⟩
  intro j threshold
  constructor
  · exact gumbelSoftmaxMix_le_iff_polynomial Sum.inl _ (simulationGeneratorParameters q)
      _ j q.p q.weights.2 q.temperature.ne' z.2 threshold (fun _ => rfl) (fun i => he i j)
  · exact gumbelSoftmaxMix_lt_iff_polynomial Sum.inl _ (simulationGeneratorParameters q)
      _ j q.p q.weights.2 q.temperature.ne' z.2 threshold (fun _ => rfl) (fun i => he i j)

/-- [For every input and noise draw and clipping level K, there exist component
masks of lengths L1 and L2 such that every coordinate clipped by taking its
minimum with K and then its maximum with −K is at most a threshold exactly
when the threshold is at least −K and either at least K or the evaluated comparison
polynomial is nonpositive; the strict comparison holds exactly when the threshold
is greater than −K and either greater than K or that polynomial is negative](goal). -/
-- @node: simulationGenerator_clipped_grid_comparisons
lemma simulationGenerator_clipped_grid_comparisons {n d : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) (K : ℝ) :
    ∃ masks1 masks2 : Fin n → List (ℕ → Bool),
      (∀ i, (masks1 i).length = L1 ∧ (masks2 i).length = L2) ∧
      ∀ (j : Fin d) (threshold : ℝ),
        ((truncK K (q.eval z)).ofLp j ≤ threshold ↔
          -K ≤ threshold ∧ (K ≤ threshold ∨
            MvPolynomial.eval (simulationGeneratorParameters q)
              (simulationGeneratorGridPolynomial q masks1 masks2 z j threshold) ≤ 0)) ∧
        ((truncK K (q.eval z)).ofLp j < threshold ↔
          -K < threshold ∧ (K < threshold ∨
            MvPolynomial.eval (simulationGeneratorParameters q)
              (simulationGeneratorGridPolynomial q masks1 masks2 z j threshold) < 0)) := by
  obtain ⟨m1, m2, hlen, h⟩ := simulationGenerator_grid_comparisons q z
  refine ⟨m1, m2, hlen, ?_⟩
  intro j threshold
  change (max (-K) (min ((q.eval z).ofLp j) K) ≤ threshold ↔ _) ∧
    (max (-K) (min ((q.eval z).ofLp j) K) < threshold ↔ _)
  rw [max_le_iff, min_le_iff, (h j threshold).1,
    max_lt_iff, min_lt_iff, (h j threshold).2]
  constructor <;> tauto

/-- For [a three-part generator q](hyp:q) and [component i](hyp:i),
[the component's parameter index set](goal) is the union of its two blocks'
parameter indices, with the second block numbered after the first and every
index tagged with the component. -/
-- @node: simulationGeneratorComponentVariables
def simulationGeneratorComponentVariables {n d : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau) (i : Fin n) :
    Finset (simulationGeneratorVariable n) :=
  (simulationNetworkVariables (q.g1 i) 0 ∪
    simulationNetworkVariables (q.g2 i) ((q.g1 i).hidden.length + 1)).image
      (fun v => Sum.inr (i, v))

-- @node: simulationGeneratorComponentPolynomial_vars
/-- [Every component output polynomial, for any fixed masks, scalar input, and
output coordinate, uses only variables in that component's parameter index set](goal). -/
lemma simulationGeneratorComponentPolynomial_vars {n d : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau)
    (i : Fin n) (m1 m2 : List (ℕ → Bool)) (u : ℝ) (j : Fin d) :
    (simulationGeneratorComponentPolynomial q i m1 m2 u j).vars ⊆
      simulationGeneratorComponentVariables q i := by
  classical
  have hz (a : ℕ) : (simulationGeneratorIntermediate q i m1 u a).vars ⊆
      simulationNetworkVariables (q.g1 i) 0 := by
    unfold simulationGeneratorIntermediate
    split_ifs
    · simpa using simulationNetworkPolynomialAt_vars (q.g1 i) 0 m1
        (simulationInputPolynomial (WithLp.toLp 1 (fun _ : Fin 1 => u))) ∅
        (fun _ => by simp [simulationInputPolynomial]) _
    · simp
  apply (MvPolynomial.vars_rename _ _).trans
  apply Finset.image_subset_image
  simpa only [Finset.union_comm] using simulationNetworkPolynomialAt_vars (q.g2 i)
    ((q.g1 i).hidden.length + 1) m2 (simulationGeneratorIntermediate q i m1 u)
    (simulationNetworkVariables (q.g1 i) 0) hz j

-- @node: simulationGeneratorVariables
/-- For [a three-part generator q](hyp:q), [the generator's finite variable set](goal)
is the union of all mixture amplitude indices and all components' network
parameter index sets. -/
def simulationGeneratorVariables {n d : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau) :
    Finset (simulationGeneratorVariable n) :=
  (Finset.univ.image Sum.inl) ∪ Finset.univ.biUnion (simulationGeneratorComponentVariables q)

/-- [Every generator grid comparison polynomial uses only variables in the
generator's finite variable set, for any masks, input and noise draw, output
coordinate, and threshold](goal). -/
-- @node: simulationGeneratorGridPolynomial_vars
lemma simulationGeneratorGridPolynomial_vars {n d : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau)
    (m1 m2 : Fin n → List (ℕ → Bool))
    (z : (Fin n → ℝ) × (Fin n → ℝ)) (j : Fin d) (threshold : ℝ) :
    (simulationGeneratorGridPolynomial q m1 m2 z j threshold).vars ⊆
      simulationGeneratorVariables q := by
  classical
  unfold simulationGeneratorGridPolynomial simulationMixtureComparison
  apply (MvPolynomial.vars_sum_subset _ _).trans
  apply Finset.biUnion_subset.mpr
  intro i _
  apply (MvPolynomial.vars_mul _ _).trans
  apply Finset.union_subset
  · apply (MvPolynomial.vars_mul _ _).trans
    simp only [MvPolynomial.vars_C, MvPolynomial.vars_X, Finset.empty_union,
      Finset.singleton_subset_iff]
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  · apply (MvPolynomial.vars_sub_subset (p := _) (q := _)).trans
    simp only [MvPolynomial.vars_C, Finset.union_empty]
    exact (simulationGeneratorComponentPolynomial_vars q i _ _ _ j).trans
      (fun v hv => Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hv⟩))

-- @node: simulationGeneratorComponentVariables_card
/-- If [w is at least one](hyp:hw), [the output dimension is at most w](hyp:hd),
[component i's intermediate dimension is at most w](hyp:hC),
[the first block's width budget is at most w](hyp:hW1), and
[the second block's width budget is at most w](hyp:hW2),
[component i's parameter index set has at most (L1 + L2 + 2) times w times (w + 1)
elements, where L1 and L2 are the blocks' hidden depths](goal). -/
lemma simulationGeneratorComponentVariables_card {n d : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau) (i : Fin n) (w : ℕ)
    (hw : 1 ≤ w) (hd : d ≤ w) (hC : dC i ≤ w) (hW1 : W1 ≤ w) (hW2 : W2 ≤ w) :
    (simulationGeneratorComponentVariables q i).card ≤ (L1 + L2 + 2) * (w * (w + 1)) := by
  calc
    _ ≤ (simulationNetworkVariables (q.g1 i) 0 ∪
        simulationNetworkVariables (q.g2 i) ((q.g1 i).hidden.length + 1)).card :=
      Finset.card_image_le
    _ ≤ (simulationNetworkVariables (q.g1 i) 0).card +
        (simulationNetworkVariables (q.g2 i) ((q.g1 i).hidden.length + 1)).card :=
      Finset.card_union_le _ _
    _ ≤ (L1 + 1) * (w * (w + 1)) + (L2 + 1) * (w * (w + 1)) :=
      Nat.add_le_add (simulationNetworkVariables_card (q.g1 i) _ w hw hC hW1)
        (simulationNetworkVariables_card (q.g2 i) _ w hC hd hW2)
    _ = _ := by ring

/-- If [w is at least one](hyp:hw), [the output dimension is at most w](hyp:hd),
[every component's intermediate dimension is at most w](hyp:hC),
[the first block's width budget is at most w](hyp:hW1), and
[the second block's width budget is at most w](hyp:hW2),
[the generator's variable set has at most n + n × ((L1 + L2 + 2) × w × (w + 1))
elements, where n is the number of components and L1 and L2 are the blocks'
hidden depths](goal). -/
-- @node: simulationGeneratorVariables_card
lemma simulationGeneratorVariables_card {n d : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau) (w : ℕ)
    (hw : 1 ≤ w) (hd : d ≤ w) (hC : ∀ i, dC i ≤ w) (hW1 : W1 ≤ w) (hW2 : W2 ≤ w) :
    (simulationGeneratorVariables q).card ≤ n + n * ((L1 + L2 + 2) * (w * (w + 1))) := by
  classical
  calc
    _ ≤ (Finset.univ.image (Sum.inl : Fin n → simulationGeneratorVariable n)).card +
        (Finset.univ.biUnion (simulationGeneratorComponentVariables q)).card :=
      Finset.card_union_le _ _
    _ ≤ n + ∑ i : Fin n, (simulationGeneratorComponentVariables q i).card :=
      Nat.add_le_add (Finset.card_image_le.trans (by simp)) Finset.card_biUnion_le
    _ ≤ n + ∑ _i : Fin n, (L1 + L2 + 2) * (w * (w + 1)) :=
      Nat.add_le_add_left (Finset.sum_le_sum fun i _ =>
        simulationGeneratorComponentVariables_card q i w hw hd (hC i) hW1 hW2) n
    _ = _ := by simp

-- @node: simulationParameterBox
/-- For [a layer-count budget depth](hyp:depth) and [a width budget width](hyp:width),
[the parameter box](goal) contains all triples whose layer index is below depth,
output index is below width, and input index is at most width, including biases. -/
def simulationParameterBox (depth width : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range depth).product ((Finset.range width).product (Finset.range (width + 1)))

-- @node: simulationLayerVariables_subset_box
/-- If [the layer index is below the layer-count budget](hyp:hk),
[the layer's input width is at most w](hyp:ha), and
[its output width is at most w](hyp:hb),
[all its parameter indices belong to the parameter box with that layer-count
budget and width w](goal). -/
lemma simulationLayerVariables_subset_box {k a b depth w : ℕ}
    (hk : k < depth) (ha : a ≤ w) (hb : b ≤ w) :
    simulationLayerVariables k a b ⊆ simulationParameterBox depth w := by
  intro v hv
  unfold simulationLayerVariables at hv
  obtain ⟨⟨j, i⟩, hji, rfl⟩ := Finset.mem_image.mp hv
  rcases Finset.mem_product.mp hji with ⟨hj, hi⟩
  exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hk,
    Finset.mem_product.mpr ⟨Finset.mem_range.mpr ((Finset.mem_range.mp hj).trans_le hb),
      Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans_le (Nat.add_le_add_right ha 1))⟩⟩

-- @node: simulationHiddenVariables_subset_box
/-- If [the starting layer index plus the number of hidden layers is at most
the layer-count budget](hyp:hdepth) and
[every hidden layer has input and output widths at most w](hyp:hw),
[all hidden-layer parameter indices belong to the parameter box with that
layer-count budget and width w](goal). -/
lemma simulationHiddenVariables_subset_box (ls : List AffineLayer) (k depth w : ℕ)
    (hdepth : k + ls.length ≤ depth) (hw : ∀ l ∈ ls, l.input ≤ w ∧ l.output ≤ w) :
    simulationHiddenVariables ls k ⊆ simulationParameterBox depth w := by
  induction ls generalizing k with
  | nil => simp [simulationHiddenVariables]
  | cons l ls ih =>
    have hl := hw l (by simp)
    apply Finset.union_subset
    · exact simulationLayerVariables_subset_box
        (by simp only [List.length_cons] at hdepth; omega) hl.1 hl.2
    · exact ih (k + 1) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hdepth)
        (fun a ha => hw a (by simp [ha]))

-- @node: simulationNetworkVariables_subset_box
/-- If [the starting layer index plus the hidden depth is below the layer-count
budget](hyp:hk), [the input dimension is at most w](hyp:hdin),
[the output dimension is at most w](hyp:hdout), and
[the hidden-width budget is at most w](hyp:hW),
[all network parameter indices belong to the parameter box with that layer-count
budget and width w](goal). -/
lemma simulationNetworkVariables_subset_box {din dout W L : ℕ} (q : ReLUNet din dout W L)
    (k depth w : ℕ) (hk : k + L < depth)
    (hdin : din ≤ w) (hdout : dout ≤ w) (hW : W ≤ w) :
    simulationNetworkVariables q k ⊆ simulationParameterBox depth w := by
  have hw : ∀ l ∈ q.hidden, l.output ≤ w := fun l hl => (q.widths l hl).trans hW
  exact Finset.union_subset
    (simulationHiddenVariables_subset_box q.hidden k depth w
      (by simpa [q.depth] using hk.le)
      (simulation_layer_width_bounds q.hidden din w hdin hw q.firstInput q.compatible))
    (simulationLayerVariables_subset_box (by simpa [q.depth] using hk)
      (simulation_finalWidth_le q.hidden din w hdin hw) hdout)

/-- For [n mixture components](hyp:n), [a layer-count budget depth](hyp:depth),
and [a width budget width](hyp:width), [the generator parameter box](goal)
contains all mixture amplitude indices and, for each component, all network
parameter triples in the parameter box with those budgets. -/
-- @node: simulationGeneratorParameterBox
def simulationGeneratorParameterBox (n depth width : ℕ) : Finset (simulationGeneratorVariable n) :=
  Finset.univ.image Sum.inl ∪
    (Finset.univ.product (simulationParameterBox depth width)).image Sum.inr

-- @node: simulationGeneratorGridPolynomial_uniform_vars
/-- If [w is at least one](hyp:hw), [the output dimension is at most w](hyp:hd),
[every component's intermediate dimension is at most w](hyp:hC),
[the first block's width budget is at most w](hyp:hW1), and
[the second block's width budget is at most w](hyp:hW2),
[every grid comparison polynomial, for any masks, draw, coordinate, and threshold,
uses only variables in the generator parameter box with n components,
layer-count budget L1 + L2 + 2, and width w](goal). -/
lemma simulationGeneratorGridPolynomial_uniform_vars {n d : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau) (w : ℕ)
    (hw : 1 ≤ w) (hd : d ≤ w) (hC : ∀ i, dC i ≤ w) (hW1 : W1 ≤ w) (hW2 : W2 ≤ w)
    (m1 m2 : Fin n → List (ℕ → Bool))
    (z : (Fin n → ℝ) × (Fin n → ℝ)) (j : Fin d) (threshold : ℝ) :
    (simulationGeneratorGridPolynomial q m1 m2 z j threshold).vars ⊆
      simulationGeneratorParameterBox n (L1 + L2 + 2) w := by
  apply (simulationGeneratorGridPolynomial_vars q m1 m2 z j threshold).trans
  apply Finset.union_subset
  · exact Finset.subset_union_left
  · apply Finset.biUnion_subset.mpr
    intro i _ v hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨(i, a), Finset.mem_product.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    rcases Finset.mem_union.mp ha with ha | ha
    · exact simulationNetworkVariables_subset_box (q.g1 i) 0 _ w
        (by omega) hw (hC i) hW1 ha
    · exact simulationNetworkVariables_subset_box (q.g2 i) ((q.g1 i).hidden.length + 1) _ w
        (by rw [(q.g1 i).depth]; omega) (hC i) hd hW2 ha

-- @node: simulationGeneratorParameterBox_card
/-- [The generator parameter box for n components, layer-count budget depth,
and width w has at most n + n × (depth × (w × (w + 1))) elements](goal). -/
lemma simulationGeneratorParameterBox_card (n depth w : ℕ) :
    (simulationGeneratorParameterBox n depth w).card ≤ n + n * (depth * (w * (w + 1))) := by
  calc
    _ ≤ (Finset.univ.image (Sum.inl : Fin n → simulationGeneratorVariable n)).card +
        ((Finset.univ.product (simulationParameterBox depth w)).image Sum.inr).card :=
      Finset.card_union_le _ _
    _ ≤ n + (Finset.univ.product (simulationParameterBox depth w)).card :=
      Nat.add_le_add (Finset.card_image_le.trans (by simp)) Finset.card_image_le
    _ = _ := by simp [simulationParameterBox]

end
end Papers.TbsNeuralCausalPi
