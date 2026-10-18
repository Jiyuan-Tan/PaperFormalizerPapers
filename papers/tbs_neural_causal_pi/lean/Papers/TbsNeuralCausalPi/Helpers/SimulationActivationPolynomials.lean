module
public import Papers.TbsNeuralCausalPi.Helpers.SimulationMixtureComparisons
/-! # Polynomial evaluation on fixed ReLU activation regions

Each affine layer introduces one parameter degree. Fixing the activation bits
replaces each ReLU by either its affine input or zero. The region conditions
are actual signs of these polynomials, including zero preactivations. Every
parameter assignment belongs to such a region. These facts supply the ReLU
part of the simulation-grid polynomial comparison construction; counting the
regions remains a separate step.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
noncomputable section

-- @node: simulationAffinePolynomial
/-- For [an affine layer](hyp:l), [a layer index for its parameters](hyp:k),
[polynomial inputs](hyp:z), and [an output coordinate](hyp:j), the
[affine output polynomial](goal) is [the weighted sum of the inputs plus a bias
at a valid output coordinate, and zero otherwise](step:1). -/
def simulationAffinePolynomial (l : AffineLayer) (k : ℕ)
    (z : ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ) (j : ℕ) :
    MvPolynomial (ℕ × ℕ × ℕ) ℝ :=
  if _hj : j < l.output then
    (∑ i : Fin l.input, MvPolynomial.X (k, j, i.val + 1) * z i.val) +
      MvPolynomial.X (k, j, 0) else 0

-- @node: simulationReluPolynomial
/-- For [an affine layer](hyp:l), [its parameter layer index](hyp:k),
[activation bits](hyp:active), [polynomial inputs](hyp:z), and [an output
coordinate](hyp:j), the [masked ReLU polynomial](goal) is [the affine output
when that coordinate is active, and zero otherwise](step:1). -/
def simulationReluPolynomial (l : AffineLayer) (k : ℕ) (active : ℕ → Bool)
    (z : ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ) (j : ℕ) :
    MvPolynomial (ℕ × ℕ × ℕ) ℝ :=
  if active j then simulationAffinePolynomial l k z j else 0

-- @node: simulationAffinePolynomial_degree
/-- If [every input polynomial has total degree at most d](hyp:hz), then
[each affine output polynomial has total degree at most d plus one](goal). -/
lemma simulationAffinePolynomial_degree (l : AffineLayer) (k d : ℕ)
    (z : ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ)
    (hz : ∀ j, (z j).totalDegree ≤ d) (j : ℕ) :
    (simulationAffinePolynomial l k z j).totalDegree ≤ d + 1 := by
  unfold simulationAffinePolynomial
  split_ifs
  · apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le
    · apply MvPolynomial.totalDegree_finsetSum_le
      intro i _
      exact (MvPolynomial.totalDegree_mul _ _).trans (by
        simp only [MvPolynomial.totalDegree_X]
        have := hz i.val
        omega)
    · simp only [MvPolynomial.totalDegree_X]
      omega
  · simp

-- @node: simulationReluPolynomial_degree
/-- If [every input polynomial has total degree at most d](hyp:hz), then
[each output polynomial with a fixed ReLU activation bit has total degree
at most d plus one](goal). -/
lemma simulationReluPolynomial_degree (l : AffineLayer) (k d : ℕ)
    (active : ℕ → Bool) (z : ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ)
    (hz : ∀ j, (z j).totalDegree ≤ d) (j : ℕ) :
    (simulationReluPolynomial l k active z j).totalDegree ≤ d + 1 := by
  unfold simulationReluPolynomial
  split_ifs
  · exact simulationAffinePolynomial_degree l k d z hz j
  · simp

-- @node: simulationLayerParametersMatch
/-- [Matching of a parameter assignment](goal) requires [the assignment](hyp:theta)
at [a layer index](hyp:k) to agree with [the affine layer](hyp:l) in both
[its weights, stored at positive input indices](step:1), and
[its biases, stored at input index zero](step:2). -/
def simulationLayerParametersMatch (theta : (ℕ × ℕ × ℕ) → ℝ)
    (k : ℕ) (l : AffineLayer) : Prop :=
  (∀ (j : Fin l.output) (i : Fin l.input),
    theta (k, j.val, i.val + 1) = l.2.2.1 j i) ∧
  (∀ j : Fin l.output, theta (k, j.val, 0) = l.2.2.2 j)

-- @node: simulationAffinePolynomial_eval
/-- If [the parameter assignment agrees with the affine layer's weights and
biases](hyp:hparam), then [evaluating its affine output polynomial equals
applying that layer to the evaluated input polynomials](goal). -/
lemma simulationAffinePolynomial_eval (l : AffineLayer) (k : ℕ)
    (theta : (ℕ × ℕ × ℕ) → ℝ)
    (hparam : simulationLayerParametersMatch theta k l)
    (z : ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ) (j : ℕ) :
    MvPolynomial.eval theta (simulationAffinePolynomial l k z j) =
      l.apply (fun i => MvPolynomial.eval theta (z i)) j := by
  unfold simulationAffinePolynomial AffineLayer.apply
  split_ifs with hj
  · simp only [map_add, map_sum, map_mul, MvPolynomial.eval_X,
      hparam.1 ⟨j, hj⟩, hparam.2 ⟨j, hj⟩]
    rfl
  · simp

-- @node: simulationReluPolynomial_eval
/-- If [the parameter assignment matches the affine layer](hyp:hparam) and
[each activation bit records whether the evaluated affine output is
nonnegative](hyp:hactive), then [evaluating the masked polynomial equals
the ReLU layer applied to the evaluated input polynomials](goal). -/
lemma simulationReluPolynomial_eval (l : AffineLayer) (k : ℕ)
    (theta : (ℕ × ℕ × ℕ) → ℝ)
    (hparam : simulationLayerParametersMatch theta k l)
    (active : ℕ → Bool) (z : ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ)
    (hactive : ∀ j, active j =
      decide (0 ≤ MvPolynomial.eval theta (simulationAffinePolynomial l k z j))) (j : ℕ) :
    MvPolynomial.eval theta (simulationReluPolynomial l k active z j) =
      reluLayer l (fun i => MvPolynomial.eval theta (z i)) j := by
  rw [simulationReluPolynomial, hactive j]
  simp only [apply_ite, map_zero]
  rw [simulationAffinePolynomial_eval l k theta hparam z j]
  unfold reluLayer
  split_ifs with h
  · exact (max_eq_right (of_decide_eq_true h)).symm
  · exact (max_eq_left (le_of_not_ge (by simpa using h))).symm

-- @node: simulationHiddenPolynomial
/-- The [hidden-layer output polynomials](goal) are computed recursively:
[with no hidden layers, return the input polynomials](step:1); [otherwise,
apply the first affine layer with its activation mask and continue through
the remaining layers, advancing the parameter index and discarding the first
mask](step:2). Missing masks mark every coordinate inactive. -/
def simulationHiddenPolynomial : List AffineLayer → ℕ → List (ℕ → Bool) →
    (ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ) → ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ
  | [], _, _, z => z
  | l :: ls, k, masks, z => simulationHiddenPolynomial ls (k + 1) masks.tail
      (simulationReluPolynomial l k (masks.headD (fun _ => false)) z)

-- @node: simulationActivationRegion
/-- The [activation-region condition](goal) says [there is no restriction for
an empty list of hidden layers](step:1), and [otherwise the first mask records
exactly the nonnegative evaluated affine outputs and the remaining layers
satisfy the same condition after the masked update](step:2). Missing masks
mark every coordinate inactive. -/
def simulationActivationRegion : List AffineLayer → ℕ → List (ℕ → Bool) →
    (ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ) → ((ℕ × ℕ × ℕ) → ℝ) → Prop
  | [], _, _, _, _ => True
  | l :: ls, k, masks, z, theta =>
      (∀ j, masks.headD (fun _ => false) j =
        decide (0 ≤ MvPolynomial.eval theta (simulationAffinePolynomial l k z j))) ∧
      simulationActivationRegion ls (k + 1) masks.tail
        (simulationReluPolynomial l k (masks.headD (fun _ => false)) z) theta

-- @node: simulationHiddenParametersMatch
/-- The [hidden-layer parameter matching condition](goal) is [automatically
satisfied for an empty list of layers](step:1); [for a nonempty list, the
assignment must match the first layer's weights and biases at the current
index and match the remaining layers at successive indices](step:2). -/
def simulationHiddenParametersMatch : List AffineLayer → ℕ →
    ((ℕ × ℕ × ℕ) → ℝ) → Prop
  | [], _, _ => True
  | l :: ls, k, theta => simulationLayerParametersMatch theta k l ∧
      simulationHiddenParametersMatch ls (k + 1) theta

-- @node: simulationActivationRegion_exists
/-- [Every real parameter assignment admits an activation region containing
it, with exactly one mask per hidden layer](goal), for any starting layer
index and polynomial inputs. Zero preactivations are included as active. -/
lemma simulationActivationRegion_exists (ls : List AffineLayer) (k : ℕ)
    (z : ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ) (theta : (ℕ × ℕ × ℕ) → ℝ) :
    ∃ masks : List (ℕ → Bool), masks.length = ls.length ∧
      simulationActivationRegion ls k masks z theta := by
  induction ls generalizing k z with
  | nil => exact ⟨[], rfl, trivial⟩
  | cons l ls ih =>
    let active : ℕ → Bool := fun j =>
      decide (0 ≤ MvPolynomial.eval theta (simulationAffinePolynomial l k z j))
    obtain ⟨masks, hlen, hregion⟩ := ih (k + 1) (simulationReluPolynomial l k active z)
    refine ⟨active :: masks, by simp [hlen], ?_⟩
    exact ⟨fun _ => rfl, hregion⟩

-- @node: simulationHiddenPolynomial_degree
/-- If [all input polynomials have total degree at most d](hyp:hz), then
[each hidden output polynomial has total degree at most d plus the number
of hidden layers](goal), for any fixed activation masks. -/
lemma simulationHiddenPolynomial_degree (ls : List AffineLayer) (k d : ℕ)
    (masks : List (ℕ → Bool)) (z : ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ)
    (hz : ∀ j, (z j).totalDegree ≤ d) (j : ℕ) :
    (simulationHiddenPolynomial ls k masks z j).totalDegree ≤ d + ls.length := by
  induction ls generalizing k d masks z with
  | nil => simpa [simulationHiddenPolynomial] using hz j
  | cons l ls ih =>
    have h := ih (k + 1) (d + 1) masks.tail
      (simulationReluPolynomial l k (masks.headD (fun _ => false)) z)
      (simulationReluPolynomial_degree l k d _ z hz)
    simpa [simulationHiddenPolynomial, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

-- @node: simulationHiddenPolynomial_eval
/-- If [the assignment matches all hidden-layer parameters](hyp:hparam) and
[belongs to the activation region specified by the masks and polynomial
inputs](hyp:hregion), then [evaluating the hidden output polynomials equals
successively applying the actual ReLU layers to the evaluated inputs](goal). -/
lemma simulationHiddenPolynomial_eval (ls : List AffineLayer) (k : ℕ)
    (masks : List (ℕ → Bool)) (z : ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ)
    (theta : (ℕ × ℕ × ℕ) → ℝ)
    (hparam : simulationHiddenParametersMatch ls k theta)
    (hregion : simulationActivationRegion ls k masks z theta) :
    (fun j => MvPolynomial.eval theta (simulationHiddenPolynomial ls k masks z j)) =
      ls.foldl (fun x l => reluLayer l x) (fun j => MvPolynomial.eval theta (z j)) := by
  induction ls generalizing k masks z with
  | nil => rfl
  | cons l ls ih =>
    rw [List.foldl_cons]
    change (fun j => MvPolynomial.eval theta (simulationHiddenPolynomial ls (k + 1)
      masks.tail (simulationReluPolynomial l k (masks.headD (fun _ => false)) z) j)) = _
    rw [ih (k + 1) masks.tail _ hparam.2 hregion.2]
    congr 1
    funext j
    exact simulationReluPolynomial_eval l k theta hparam.1 _ z hregion.1 j

-- @node: simulationHiddenParametersMatch_of_getElem
/-- If [each layer in the list matches the assignment at the starting index
plus its position](hyp:h), then [the recursive hidden-layer parameter
matching condition holds for the entire list](goal). -/
lemma simulationHiddenParametersMatch_of_getElem (ls : List AffineLayer) (k : ℕ)
    (theta : (ℕ × ℕ × ℕ) → ℝ)
    (h : ∀ r : Fin ls.length,
      simulationLayerParametersMatch theta (k + r.val) ls[r.val]) :
    simulationHiddenParametersMatch ls k theta := by
  induction ls generalizing k with
  | nil => trivial
  | cons l ls ih =>
    refine ⟨?_, ih (k + 1) ?_⟩
    · simpa using h ⟨0, by simp⟩
    · intro r
      have hr := h ⟨r.val + 1, by simpa only [List.length_cons] using Nat.succ_lt_succ r.isLt⟩
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hr

-- @node: simulationNetworkParameters
/-- For [a stored ReLU network](hyp:q) and [a triple specifying a layer,
output coordinate, and input index](hyp:v), the [parameter value](goal) is
[the corresponding hidden-layer bias or weight when the layer index is below
the hidden depth](step:1), and [the corresponding output-layer bias or weight
otherwise](step:2). Input index zero denotes a bias; positive indices denote
weights, and invalid coordinates give zero. -/
def simulationNetworkParameters {din dout W L : ℕ} (q : ReLUNet din dout W L)
    (v : ℕ × ℕ × ℕ) : ℝ :=
  if hk : v.1 < q.hidden.length then
    let l := q.hidden[v.1]
    if hj : v.2.1 < l.output then
      if v.2.2 = 0 then l.2.2.2 ⟨v.2.1, hj⟩
      else if hi : v.2.2 - 1 < l.input then l.2.2.1 ⟨v.2.1, hj⟩ ⟨v.2.2 - 1, hi⟩
      else 0
    else 0
  else if hj : v.2.1 < dout then
    if v.2.2 = 0 then q.outputBias ⟨v.2.1, hj⟩
    else if hi : v.2.2 - 1 < finalWidth din q.hidden then
      q.outputWeight ⟨v.2.1, hj⟩ ⟨v.2.2 - 1, hi⟩ else 0
  else 0

-- @node: simulationNetworkParameters_hidden
/-- [The parameter assignment extracted from a stored network matches all
its hidden layers, starting at layer index zero](goal). -/
lemma simulationNetworkParameters_hidden {din dout W L : ℕ} (q : ReLUNet din dout W L) :
    simulationHiddenParametersMatch q.hidden 0 (simulationNetworkParameters q) := by
  apply simulationHiddenParametersMatch_of_getElem
  intro r
  simp only [Nat.zero_add]
  constructor
  · intro j i
    simp [simulationNetworkParameters, r.isLt, j.isLt, i.isLt]
    rfl
  · intro j
    simp [simulationNetworkParameters, r.isLt, j.isLt]
    rfl

-- @node: simulationNetworkParameters_output
/-- [At the layer index equal to the hidden depth, the extracted parameter
assignment equals every stored output weight at its positive input index
and every stored output bias at input index zero](goal). -/
lemma simulationNetworkParameters_output {din dout W L : ℕ} (q : ReLUNet din dout W L) :
    (∀ (j : Fin dout) (i : Fin (finalWidth din q.hidden)),
      simulationNetworkParameters q (q.hidden.length, j.val, i.val + 1) = q.outputWeight j i) ∧
    (∀ j : Fin dout,
      simulationNetworkParameters q (q.hidden.length, j.val, 0) = q.outputBias j) := by
  constructor
  · intro j i
    simp [simulationNetworkParameters, j.isLt, i.isLt]
  · intro j
    simp [simulationNetworkParameters, j.isLt]

-- @node: simulationInputPolynomial
/-- For [an input vector](hyp:x) and [a coordinate index](hyp:j), the
[input polynomial](goal) is the constant equal to that coordinate of the
vector, or zero when the index lies outside the input dimension. -/
def simulationInputPolynomial {din : ℕ} (x : L1Vec din) (j : ℕ) :
    MvPolynomial (ℕ × ℕ × ℕ) ℝ :=
  MvPolynomial.C (if h : j < din then x.ofLp ⟨j, h⟩ else 0)

-- @node: simulationNetworkPolynomial
/-- For [a ReLU network](hyp:q), [fixed hidden-layer activation masks](hyp:masks),
[an input vector](hyp:x), and [an output coordinate](hyp:j), the
[network output polynomial](goal) is the weighted sum of the masked hidden
output polynomials plus the output bias, using formal variables for all
weights and biases. -/
def simulationNetworkPolynomial {din dout W L : ℕ} (q : ReLUNet din dout W L)
    (masks : List (ℕ → Bool)) (x : L1Vec din) (j : Fin dout) :
    MvPolynomial (ℕ × ℕ × ℕ) ℝ :=
  (∑ i : Fin (finalWidth din q.hidden),
    MvPolynomial.X (q.hidden.length, j.val, i.val + 1) *
      simulationHiddenPolynomial q.hidden 0 masks (simulationInputPolynomial x) i.val) +
    MvPolynomial.X (q.hidden.length, j.val, 0)

-- @node: simulationNetworkPolynomial_degree
/-- [Each network output polynomial with fixed input and activation masks
has total degree at most the hidden depth plus one](goal). -/
lemma simulationNetworkPolynomial_degree {din dout W L : ℕ} (q : ReLUNet din dout W L)
    (masks : List (ℕ → Bool)) (x : L1Vec din) (j : Fin dout) :
    (simulationNetworkPolynomial q masks x j).totalDegree ≤ L + 1 := by
  have hh (i : ℕ) := simulationHiddenPolynomial_degree q.hidden 0 0 masks
    (simulationInputPolynomial x) (fun _ => by simp [simulationInputPolynomial]) i
  simp only [zero_add, q.depth] at hh
  unfold simulationNetworkPolynomial
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro i _
    exact (MvPolynomial.totalDegree_mul _ _).trans (by
      simp only [MvPolynomial.totalDegree_X]
      have := hh i.val
      omega)
  · simp only [MvPolynomial.totalDegree_X]
    omega

-- @node: simulationNetworkPolynomial_eval
/-- If [the stored network parameters belong to the activation region of the
chosen masks at the given input](hyp:hregion), then [evaluating the output
polynomial at those parameters gives the actual network output coordinate](goal). -/
lemma simulationNetworkPolynomial_eval {din dout W L : ℕ} (q : ReLUNet din dout W L)
    (masks : List (ℕ → Bool)) (x : L1Vec din)
    (hregion : simulationActivationRegion q.hidden 0 masks (simulationInputPolynomial x)
      (simulationNetworkParameters q)) (j : Fin dout) :
    MvPolynomial.eval (simulationNetworkParameters q) (simulationNetworkPolynomial q masks x j) =
      (q.eval x).ofLp j := by
  have hh := simulationHiddenPolynomial_eval q.hidden 0 masks (simulationInputPolynomial x)
    (simulationNetworkParameters q) (simulationNetworkParameters_hidden q) hregion
  have hout := simulationNetworkParameters_output q
  simp only [simulationInputPolynomial, MvPolynomial.eval_C] at hh
  simp only [simulationNetworkPolynomial, map_add, map_sum, map_mul, MvPolynomial.eval_X,
    hout.1 j, hout.2 j]
  change (∑ i, q.outputWeight j i *
    (fun a => MvPolynomial.eval (simulationNetworkParameters q)
      (simulationHiddenPolynomial q.hidden 0 masks (simulationInputPolynomial x) a)) i.val) +
        q.outputBias j = _
  rw [hh]
  rfl

-- @node: simulationNetworkPolynomial_represents
/-- [For every network and fixed input, there are activation masks, one per
hidden layer, whose region contains the stored parameters and whose output
polynomials have degree at most the hidden depth plus one and evaluate to
the actual network outputs](goal). This includes networks with no hidden layers. -/
lemma simulationNetworkPolynomial_represents {din dout W L : ℕ}
    (q : ReLUNet din dout W L) (x : L1Vec din) :
    ∃ masks : List (ℕ → Bool), masks.length = L ∧
      simulationActivationRegion q.hidden 0 masks (simulationInputPolynomial x)
        (simulationNetworkParameters q) ∧
      ∀ j : Fin dout,
        (simulationNetworkPolynomial q masks x j).totalDegree ≤ L + 1 ∧
        MvPolynomial.eval (simulationNetworkParameters q)
          (simulationNetworkPolynomial q masks x j) =
          (q.eval x).ofLp j := by
  obtain ⟨masks, hlen, hregion⟩ := simulationActivationRegion_exists q.hidden 0
    (simulationInputPolynomial x) (simulationNetworkParameters q)
  refine ⟨masks, hlen.trans q.depth, hregion, fun j => ⟨?_, ?_⟩⟩
  · exact simulationNetworkPolynomial_degree q masks x j
  · exact simulationNetworkPolynomial_eval q masks x hregion j

-- @node: simulationNetworkPolynomialAt
/-- For [a ReLU network](hyp:q), [a starting parameter layer index](hyp:k),
[hidden-layer activation masks](hyp:masks), [polynomial inputs](hyp:z), and
[an output coordinate](hyp:j), the [output polynomial with offset parameter
indices](goal) is the affine output applied to the masked hidden-layer
polynomials, with its parameters indexed after the hidden layers. -/
def simulationNetworkPolynomialAt {din dout W L : ℕ} (q : ReLUNet din dout W L)
    (k : ℕ) (masks : List (ℕ → Bool)) (z : ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ)
    (j : Fin dout) : MvPolynomial (ℕ × ℕ × ℕ) ℝ :=
  (∑ i : Fin (finalWidth din q.hidden),
    MvPolynomial.X (k + q.hidden.length, j.val, i.val + 1) *
      simulationHiddenPolynomial q.hidden k masks z i.val) +
    MvPolynomial.X (k + q.hidden.length, j.val, 0)

-- @node: simulationNetworkPolynomialAt_degree
/-- If [each input polynomial has total degree at most d](hyp:hz), then
[each output polynomial, at any starting parameter index and with fixed
activation masks, has degree at most d plus the hidden depth plus one](goal). -/
lemma simulationNetworkPolynomialAt_degree {din dout W L : ℕ} (q : ReLUNet din dout W L)
    (k d : ℕ) (masks : List (ℕ → Bool)) (z : ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ)
    (hz : ∀ i, (z i).totalDegree ≤ d) (j : Fin dout) :
    (simulationNetworkPolynomialAt q k masks z j).totalDegree ≤ d + L + 1 := by
  have hh (i : ℕ) := simulationHiddenPolynomial_degree q.hidden k d masks z hz i
  rw [q.depth] at hh
  unfold simulationNetworkPolynomialAt
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro i _
    exact (MvPolynomial.totalDegree_mul _ _).trans (by
      simp only [MvPolynomial.totalDegree_X]
      have := hh i.val
      omega)
  · simp only [MvPolynomial.totalDegree_X]
    omega

-- @node: simulationNetworkPolynomialAt_eval
/-- If [the assignment matches the hidden layers at the chosen offset](hyp:hparam),
[matches the output weights and biases after those hidden layers](hyp:hout),
[evaluates the input polynomials to the input vector extended by zeros](hyp:hinput),
and [lies in the masks' activation region](hyp:hregion), then [the evaluated
output polynomial equals the corresponding actual network output](goal). -/
lemma simulationNetworkPolynomialAt_eval {din dout W L : ℕ} (q : ReLUNet din dout W L)
    (k : ℕ) (masks : List (ℕ → Bool)) (z : ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ)
    (theta : (ℕ × ℕ × ℕ) → ℝ) (x : L1Vec din)
    (hparam : simulationHiddenParametersMatch q.hidden k theta)
    (hout : (∀ (j : Fin dout) (i : Fin (finalWidth din q.hidden)),
        theta (k + q.hidden.length, j.val, i.val + 1) = q.outputWeight j i) ∧
      (∀ j : Fin dout, theta (k + q.hidden.length, j.val, 0) = q.outputBias j))
    (hinput : ∀ i, MvPolynomial.eval theta (z i) =
      if hi : i < din then x.ofLp ⟨i, hi⟩ else 0)
    (hregion : simulationActivationRegion q.hidden k masks z theta) (j : Fin dout) :
    MvPolynomial.eval theta (simulationNetworkPolynomialAt q k masks z j) = (q.eval x).ofLp j := by
  have hh := simulationHiddenPolynomial_eval q.hidden k masks z theta hparam hregion
  simp_rw [hinput] at hh
  simp only [simulationNetworkPolynomialAt, map_add, map_sum, map_mul, MvPolynomial.eval_X,
    hout.1 j, hout.2 j]
  change (∑ i, q.outputWeight j i *
    (fun a => MvPolynomial.eval theta (simulationHiddenPolynomial q.hidden k masks z a)) i.val) +
      q.outputBias j = _
  rw [hh]
  rfl

-- @node: simulationTwoBlockPolynomial_represents
/-- If the assignment [matches the first block's hidden layers](hyp:hparam1)
and [output weights and biases](hyp:hout1), and [matches the second block's
hidden layers](hyp:hparam2) and [output weights and biases](hyp:hout2) at their
respective offsets, then [there are masks of the two hidden depths whose
regions contain the assignment and whose composed output polynomials have
degree at most the sum of the hidden depths plus two and evaluate to the
actual composition at the fixed input](goal). The first block's polynomial
outputs, extended by zeros, are the second block's inputs. -/
lemma simulationTwoBlockPolynomial_represents {din dmid dout W1 W2 L1 L2 : ℕ}
    (q1 : ReLUNet din dmid W1 L1) (q2 : ReLUNet dmid dout W2 L2)
    (k1 k2 : ℕ) (theta : (ℕ × ℕ × ℕ) → ℝ) (x : L1Vec din)
    (hparam1 : simulationHiddenParametersMatch q1.hidden k1 theta)
    (hout1 : (∀ (j : Fin dmid) (i : Fin (finalWidth din q1.hidden)),
        theta (k1 + q1.hidden.length, j.val, i.val + 1) = q1.outputWeight j i) ∧
      (∀ j : Fin dmid, theta (k1 + q1.hidden.length, j.val, 0) = q1.outputBias j))
    (hparam2 : simulationHiddenParametersMatch q2.hidden k2 theta)
    (hout2 : (∀ (j : Fin dout) (i : Fin (finalWidth dmid q2.hidden)),
        theta (k2 + q2.hidden.length, j.val, i.val + 1) = q2.outputWeight j i) ∧
      (∀ j : Fin dout, theta (k2 + q2.hidden.length, j.val, 0) = q2.outputBias j)) :
    ∃ masks1 masks2 : List (ℕ → Bool),
      masks1.length = L1 ∧ masks2.length = L2 ∧
      let z2 := fun i => if hi : i < dmid then
        simulationNetworkPolynomialAt q1 k1 masks1 (simulationInputPolynomial x) ⟨i, hi⟩ else 0
      simulationActivationRegion q1.hidden k1 masks1 (simulationInputPolynomial x) theta ∧
      simulationActivationRegion q2.hidden k2 masks2 z2 theta ∧
      ∀ j : Fin dout,
        (simulationNetworkPolynomialAt q2 k2 masks2 z2 j).totalDegree ≤ L1 + L2 + 2 ∧
        MvPolynomial.eval theta (simulationNetworkPolynomialAt q2 k2 masks2 z2 j) =
          (q2.eval (q1.eval x)).ofLp j := by
  obtain ⟨masks1, hlen1, hregion1⟩ := simulationActivationRegion_exists q1.hidden k1
    (simulationInputPolynomial x) theta
  let z2 := fun i => if hi : i < dmid then
    simulationNetworkPolynomialAt q1 k1 masks1 (simulationInputPolynomial x) ⟨i, hi⟩ else 0
  have hinput1 (i : ℕ) : MvPolynomial.eval theta (simulationInputPolynomial x i) =
      if hi : i < din then x.ofLp ⟨i, hi⟩ else 0 := by
    simp [simulationInputPolynomial]
  have heval1 := simulationNetworkPolynomialAt_eval q1 k1 masks1 _ theta x
    hparam1 hout1 hinput1 hregion1
  have hz2 (i : ℕ) : (z2 i).totalDegree ≤ L1 + 1 := by
    dsimp [z2]
    split_ifs
    · simpa using simulationNetworkPolynomialAt_degree q1 k1 0 masks1
        (simulationInputPolynomial x) (fun _ => by simp [simulationInputPolynomial]) _
    · simp
  have hinput2 (i : ℕ) : MvPolynomial.eval theta (z2 i) =
      if hi : i < dmid then (q1.eval x).ofLp ⟨i, hi⟩ else 0 := by
    dsimp [z2]
    split_ifs
    · exact heval1 _
    · simp
  obtain ⟨masks2, hlen2, hregion2⟩ := simulationActivationRegion_exists q2.hidden k2 z2 theta
  refine ⟨masks1, masks2, hlen1.trans q1.depth, hlen2.trans q2.depth,
    hregion1, hregion2, fun j => ⟨?_, ?_⟩⟩
  · change (simulationNetworkPolynomialAt q2 k2 masks2 z2 j).totalDegree ≤ L1 + L2 + 2
    have h := simulationNetworkPolynomialAt_degree q2 k2 (L1 + 1) masks2 z2 hz2 j
    omega
  · exact simulationNetworkPolynomialAt_eval q2 k2 masks2 z2 theta (q1.eval x)
      hparam2 hout2 hinput2 hregion2 j

-- @node: simulationTwoBlockParameters
/-- For [a first network](hyp:q1), [a second network](hyp:q2), and [a parameter
index triple](hyp:v), the [joint parameter assignment](goal) uses [the first
network's parameters through its affine output layer](step:1), and [the second
network's parameters thereafter, shifting layer indices by the first hidden
depth plus one](step:2). -/
def simulationTwoBlockParameters {din dmid dout W1 W2 L1 L2 : ℕ}
    (q1 : ReLUNet din dmid W1 L1) (q2 : ReLUNet dmid dout W2 L2)
    (v : ℕ × ℕ × ℕ) : ℝ :=
  if v.1 ≤ q1.hidden.length then simulationNetworkParameters q1 v
  else simulationNetworkParameters q2 (v.1 - (q1.hidden.length + 1), v.2)

-- @node: simulationTwoBlockParameters_hidden
/-- [The joint parameter assignment matches the first network's hidden layers
starting at zero and the second network's hidden layers starting immediately
after the first network's affine output layer](goal). -/
lemma simulationTwoBlockParameters_hidden {din dmid dout W1 W2 L1 L2 : ℕ}
    (q1 : ReLUNet din dmid W1 L1) (q2 : ReLUNet dmid dout W2 L2) :
    simulationHiddenParametersMatch q1.hidden 0 (simulationTwoBlockParameters q1 q2) ∧
    simulationHiddenParametersMatch q2.hidden (q1.hidden.length + 1)
      (simulationTwoBlockParameters q1 q2) := by
  constructor
  · apply simulationHiddenParametersMatch_of_getElem
    intro r
    simp only [Nat.zero_add]
    have hr := Nat.le_of_lt r.isLt
    constructor
    · intro j i
      simp only [simulationTwoBlockParameters, if_pos hr]
      simp [simulationNetworkParameters, r.isLt, j.isLt, i.isLt]
      rfl
    · intro j
      simp only [simulationTwoBlockParameters, if_pos hr]
      simp [simulationNetworkParameters, r.isLt, j.isLt]
      rfl
  · apply simulationHiddenParametersMatch_of_getElem
    intro r
    have hr : ¬ q1.hidden.length + 1 + r.val ≤ q1.hidden.length := by omega
    constructor
    · intro j i
      simp only [simulationTwoBlockParameters, if_neg hr, Nat.add_sub_cancel_left]
      simp [simulationNetworkParameters, r.isLt, j.isLt, i.isLt]
      rfl
    · intro j
      simp only [simulationTwoBlockParameters, if_neg hr, Nat.add_sub_cancel_left]
      simp [simulationNetworkParameters, r.isLt, j.isLt]
      rfl

-- @node: simulationTwoBlockPolynomial_exists
/-- [For two stored networks and a fixed input, there are masks of their
respective hidden depths whose activation regions contain the joint stored
parameter assignment, and the resulting composed output polynomials have
degree at most the sum of the hidden depths plus two and evaluate to the
actual composed outputs](goal). The second block starts after the first
block's affine output layer and receives its polynomial outputs extended by zeros. -/
lemma simulationTwoBlockPolynomial_exists {din dmid dout W1 W2 L1 L2 : ℕ}
    (q1 : ReLUNet din dmid W1 L1) (q2 : ReLUNet dmid dout W2 L2) (x : L1Vec din) :
    ∃ masks1 masks2 : List (ℕ → Bool),
      masks1.length = L1 ∧ masks2.length = L2 ∧
      let z2 := fun i => if hi : i < dmid then
        simulationNetworkPolynomialAt q1 0 masks1 (simulationInputPolynomial x) ⟨i, hi⟩ else 0
      simulationActivationRegion q1.hidden 0 masks1 (simulationInputPolynomial x)
        (simulationTwoBlockParameters q1 q2) ∧
      simulationActivationRegion q2.hidden (q1.hidden.length + 1) masks2 z2
        (simulationTwoBlockParameters q1 q2) ∧
      ∀ j : Fin dout,
        (simulationNetworkPolynomialAt q2 (q1.hidden.length + 1) masks2 z2 j).totalDegree ≤
          L1 + L2 + 2 ∧
        MvPolynomial.eval (simulationTwoBlockParameters q1 q2)
          (simulationNetworkPolynomialAt q2 (q1.hidden.length + 1) masks2 z2 j) =
            (q2.eval (q1.eval x)).ofLp j := by
  have hhidden := simulationTwoBlockParameters_hidden q1 q2
  refine simulationTwoBlockPolynomial_represents q1 q2 0 (q1.hidden.length + 1)
    (simulationTwoBlockParameters q1 q2) x hhidden.1 ?_ hhidden.2 ?_
  · constructor
    · intro j i
      simpa [simulationTwoBlockParameters] using (simulationNetworkParameters_output q1).1 j i
    · intro j
      simpa [simulationTwoBlockParameters] using (simulationNetworkParameters_output q1).2 j
  · have hr : ¬ q1.hidden.length + 1 + q2.hidden.length ≤ q1.hidden.length := by omega
    constructor
    · intro j i
      simpa [simulationTwoBlockParameters, hr, Nat.add_sub_cancel_left] using
        (simulationNetworkParameters_output q2).1 j i
    · intro j
      simpa [simulationTwoBlockParameters, hr, Nat.add_sub_cancel_left] using
        (simulationNetworkParameters_output q2).2 j

end
end Papers.TbsNeuralCausalPi
