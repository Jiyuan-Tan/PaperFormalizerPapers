module
public import Papers.TbsNeuralCausalPi.Helpers.SimulationLayerPatterns
/-! # Actual ReLU states recovered from counted sign histories

The newest comparison is stored first. Replaying its weak sign bit recovers
all hidden states on a finite sample, using the same weights at every layer.
Zero preactivations are active, and padded coordinates contribute zero.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
noncomputable section

-- @node: simulationHistoryMask
/-- The [activation mask](goal) for [a sample point](hyp:a) and [coordinate](hyp:j)
reads the weak-sign bit from the newest entry of [the comparison history](hyp:s),
defaulting to inactive when the history is empty and to active beyond the recorded width. -/
def simulationHistoryMask {m w : ℕ}
    (s : List (Fin m × Fin w → Bool × Bool)) (a : Fin m) (j : ℕ) : Bool :=
  if hj : j < w then (s.headD (fun _ => (false, false)) (a, ⟨j, hj⟩)).1 else true

-- @node: simulationHistoryState
/-- The [polynomial hidden state](goal) associated with [the affine layers](hyp:layers)
and [initial sample polynomials](hyp:z) is [the initial polynomial at depth zero](step:1),
and [at each positive depth applies the next affine layer and the newest history mask
to the state reconstructed from the remaining history](step:2). -/
def simulationHistoryState {m w : ℕ} (layers : ℕ → AffineLayer)
    (z : Fin m → ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ) :
    ℕ → List (Fin m × Fin w → Bool × Bool) →
      Fin m → ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ
  | 0, _, a, j => z a j
  | k + 1, s, a, j => simulationReluPolynomial (layers k) k
      (simulationHistoryMask s a) (simulationHistoryState layers z k s.tail a) j

-- @node: simulationHistoryTests
/-- The [comparison polynomial](goal) for [affine layers](hyp:layers),
[initial sample polynomials](hyp:z), [layer index](hyp:k), and [past comparison history](hyp:s)
is the negative affine preactivation at [the selected sample point and coordinate](hyp:aj),
using the hidden state reconstructed from that history. -/
def simulationHistoryTests {m w : ℕ} (layers : ℕ → AffineLayer)
    (z : Fin m → ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ)
    (k : ℕ) (s : List (Fin m × Fin w → Bool × Bool))
    (aj : Fin m × Fin w) : MvPolynomial (ℕ × ℕ × ℕ) ℝ :=
  -simulationAffinePolynomial (layers k) k (simulationHistoryState layers z k s aj.1) aj.2

-- @node: simulationHistoryState_degree
/-- If [every initial sample polynomial has degree at most d](hyp:hz), then
[each hidden-state polynomial reconstructed after k layers has degree at most d + k](goal). -/
lemma simulationHistoryState_degree {m w : ℕ} (layers : ℕ → AffineLayer)
    (z : Fin m → ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ)
    (d : ℕ) (hz : ∀ a j, (z a j).totalDegree ≤ d)
    (k : ℕ) (s : List (Fin m × Fin w → Bool × Bool)) (a : Fin m) (j : ℕ) :
    (simulationHistoryState layers z k s a j).totalDegree ≤ d + k := by
  induction k generalizing s j with
  | zero => exact hz a j
  | succ k ih =>
    exact (simulationReluPolynomial_degree (layers k) k (d + k) _ _
      (fun j => ih s.tail j) j).trans (by omega)

-- @node: simulationHistoryState_vars
/-- If [all initial polynomials use variables from S](hyp:hz) and
[every layer before depth t uses only parameters in S](hyp:hl), then
[every hidden-state polynomial reconstructed at depth t uses only variables in S](goal). -/
lemma simulationHistoryState_vars {m w : ℕ} (layers : ℕ → AffineLayer)
    (z : Fin m → ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ)
    (S : Finset (ℕ × ℕ × ℕ)) (hz : ∀ a j, (z a j).vars ⊆ S)
    (t : ℕ) (hl : ∀ k < t, simulationLayerVariables k (layers k).input (layers k).output ⊆ S)
    (s : List (Fin m × Fin w → Bool × Bool)) (a : Fin m) (j : ℕ) :
    (simulationHistoryState layers z t s a j).vars ⊆ S := by
  induction t generalizing s j with
  | zero => exact hz a j
  | succ t ih =>
    apply (simulationReluPolynomial_vars (layers t) t _ _ S
      (fun j => ih (fun k hk => hl k (by omega)) s.tail j) j).trans
    exact Finset.union_subset (hl t (by omega)) Finset.Subset.rfl

-- @node: simulationHistoryTests_degree
/-- If [every initial sample polynomial has degree at most d](hyp:hz), then
[the comparison polynomial at layer k has degree at most d + k + 1](goal). -/
lemma simulationHistoryTests_degree {m w : ℕ} (layers : ℕ → AffineLayer)
    (z : Fin m → ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ)
    (d : ℕ) (hz : ∀ a j, (z a j).totalDegree ≤ d)
    (k : ℕ) (s : List (Fin m × Fin w → Bool × Bool)) (aj : Fin m × Fin w) :
    (simulationHistoryTests layers z k s aj).totalDegree ≤ d + k + 1 := by
  rw [simulationHistoryTests, MvPolynomial.totalDegree_neg]
  exact simulationAffinePolynomial_degree (layers k) k (d + k) _
    (simulationHistoryState_degree layers z d hz k s aj.1) _

-- @node: simulationHistoryTests_vars
/-- If [the initial polynomials use only variables in S](hyp:hz),
[all layers before depth t use only parameters in S](hyp:hl), and
[k is before depth t](hyp:hk), then [the layer-k comparison polynomial uses only variables in S](goal). -/
lemma simulationHistoryTests_vars {m w : ℕ} (layers : ℕ → AffineLayer)
    (z : Fin m → ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ)
    (S : Finset (ℕ × ℕ × ℕ)) (hz : ∀ a j, (z a j).vars ⊆ S)
    (t : ℕ) (hl : ∀ k < t, simulationLayerVariables k (layers k).input (layers k).output ⊆ S)
    (k : ℕ) (hk : k < t) (s : List (Fin m × Fin w → Bool × Bool))
    (aj : Fin m × Fin w) : (simulationHistoryTests layers z k s aj).vars ⊆ S := by
  rw [simulationHistoryTests, MvPolynomial.vars_neg]
  apply (simulationAffinePolynomial_vars (layers k) k _ S
    (simulationHistoryState_vars layers z S hz k (fun r hr => hl r (hr.trans hk)) s aj.1) _).trans
  exact Finset.union_subset (hl k hk) Finset.Subset.rfl

/-- The [sequence of actual hidden states](goal) for [affine layers](hyp:layers)
and [sample inputs](hyp:x) [starts with those inputs at depth zero](step:1)
and [applies the next affine layer followed by ReLU at each subsequent depth](step:2). -/
-- @node: simulationLayerStates
def simulationLayerStates {m : ℕ} (layers : ℕ → AffineLayer)
    (x : Fin m → ℕ → ℝ) : ℕ → Fin m → ℕ → ℝ
  | 0 => x
  | k + 1 => fun a => reluLayer (layers k) (simulationLayerStates layers x k a)

-- @node: simulationHistoryMask_actual
/-- If [layer k has at most w output coordinates](hyp:hw), then
[the mask extracted from the actual comparison history is active exactly when the
evaluated affine preactivation is nonnegative, including padded coordinates](goal). -/
lemma simulationHistoryMask_actual {m w : ℕ} (layers : ℕ → AffineLayer)
    (z : Fin m → ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ)
    (theta : (ℕ × ℕ × ℕ) → ℝ) (k : ℕ)
    (hw : (layers k).output ≤ w) (a : Fin m) (j : ℕ) :
    simulationHistoryMask
      (simulationLayerPatternHistory (simulationHistoryTests (w := w) layers z) theta (k + 1)) a j =
      decide (0 ≤ MvPolynomial.eval theta (simulationAffinePolynomial (layers k) k
        (simulationHistoryState layers z k
          (simulationLayerPatternHistory
            (simulationHistoryTests (w := w) layers z) theta k) a) j)) := by
  by_cases hj : j < w
  · simp [simulationHistoryMask, hj, simulationLayerPatternHistory,
      polynomialComparisonPattern, simulationHistoryTests]
  · have hout : ¬ j < (layers k).output := by omega
    simp [simulationHistoryMask, hj, simulationAffinePolynomial, hout]

/-- If [every layer before depth t has at most w outputs](hyp:hw) and
[the polynomial parameters match the stored weights and biases in those layers](hyp:hparam),
then [evaluating the hidden-state polynomials along the actual comparison history
recovers every actual hidden-state coordinate at depth t](goal). -/
-- @node: simulationHistoryState_actual
lemma simulationHistoryState_actual {m w : ℕ} (layers : ℕ → AffineLayer)
    (z : Fin m → ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ)
    (theta : (ℕ × ℕ × ℕ) → ℝ) (t : ℕ)
    (hw : ∀ k < t, (layers k).output ≤ w)
    (hparam : ∀ k < t, simulationLayerParametersMatch theta k (layers k)) :
    ∀ a j, MvPolynomial.eval theta (simulationHistoryState layers z t
      (simulationLayerPatternHistory (simulationHistoryTests (w := w) layers z) theta t) a j) =
      simulationLayerStates layers (fun a j => MvPolynomial.eval theta (z a j)) t a j := by
  induction t with
  | zero => intro a j; rfl
  | succ t ih =>
    intro a j
    change MvPolynomial.eval theta (simulationReluPolynomial (layers t) t _ _ j) = _
    have htail : (simulationLayerPatternHistory
        (simulationHistoryTests (w := w) layers z) theta (t + 1)).tail =
        simulationLayerPatternHistory (simulationHistoryTests (w := w) layers z) theta t := rfl
    rw [htail]
    rw [simulationReluPolynomial_eval (layers t) t theta (hparam t (by omega)) _ _
      (simulationHistoryMask_actual layers z theta t (hw t (by omega)) a)]
    change reluLayer (layers t) (fun i => MvPolynomial.eval theta
      (simulationHistoryState layers z t
        (simulationLayerPatternHistory
          (simulationHistoryTests (w := w) layers z) theta t) a i)) j = _
    rw [show (fun i => MvPolynomial.eval theta (simulationHistoryState layers z t
        (simulationLayerPatternHistory (simulationHistoryTests (w := w) layers z) theta t) a i)) =
      simulationLayerStates layers (fun a j => MvPolynomial.eval theta (z a j)) t a from
        funext (ih (fun k hk => hw k (by omega)) (fun k hk => hparam k (by omega)) a)]
    rfl

/-- If [two families of comparison polynomials agree for every history at every
layer before t](hyp:h), then [they produce the same comparison history through depth t](goal). -/
-- @node: simulationLayerPatternHistory_congr_prefix
lemma simulationLayerPatternHistory_congr_prefix {I V : Type*}
    (p q : ℕ → List (I → Bool × Bool) → I → MvPolynomial V ℝ)
    (theta : V → ℝ) (t : ℕ) (h : ∀ k < t, ∀ s, p k s = q k s) :
    simulationLayerPatternHistory p theta t = simulationLayerPatternHistory q theta t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [simulationLayerPatternHistory, ih (fun k hk => h k (by omega)),
      h t (by omega)]

-- @node: simulationNetworkHistories_encard_le
/-- If [the initial polynomials use only variables in S](hyp:hz),
[their degrees are at most d](hyp:hdegree), and [all layers before t use only
parameters in S](hyp:hl), then [the number of comparison histories attainable over
all parameter values is at most $(8mw\max(d+t,1)+5)^{(|S|+2)t}$](goal). -/
lemma simulationNetworkHistories_encard_le {m w : ℕ} (layers : ℕ → AffineLayer)
    (z : Fin m → ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ)
    (S : Finset (ℕ × ℕ × ℕ)) (hz : ∀ a j, (z a j).vars ⊆ S)
    (d : ℕ) (hdegree : ∀ a j, (z a j).totalDegree ≤ d)
    (t : ℕ) (hl : ∀ k < t, simulationLayerVariables k (layers k).input (layers k).output ⊆ S) :
    (Set.range (fun theta => simulationLayerPatternHistory
      (simulationHistoryTests (w := w) layers z) theta t)).encard ≤
      ((8 * (m * w) * max (d + t) 1 + 5) ^ ((S.card + 2) * t) : ℕ) := by
  let p : ℕ → List (Fin m × Fin w → Bool × Bool) →
      Fin m × Fin w → MvPolynomial (ℕ × ℕ × ℕ) ℝ :=
    fun k s aj => if k < t then simulationHistoryTests layers z k s aj else 0
  have heq (theta) : simulationLayerPatternHistory p theta t =
      simulationLayerPatternHistory (simulationHistoryTests (w := w) layers z) theta t := by
    apply simulationLayerPatternHistory_congr_prefix
    intro k hk s
    funext aj
    simp only [p, if_pos hk]
  have hc := simulationLayerPatternHistory_supported_encard_le S p
    (by
      intro k s aj
      dsimp only [p]
      split_ifs with hk
      · exact simulationHistoryTests_vars layers z S hz t hl k hk s aj
      · simp)
    (d + t) t (by
      intro k hk s aj
      dsimp only [p]
      rw [if_pos hk]
      exact (simulationHistoryTests_degree layers z d hdegree k s aj).trans (by omega))
  simpa only [heq, Fintype.card_prod, Fintype.card_fin] using hc

/-- The [stored affine layer](goal) of [a ReLU network](hyp:q) at [index k](hyp:k)
is its k-th hidden layer while that layer exists, and otherwise its signed affine
output layer. -/
-- @node: simulationStoredLayers
def simulationStoredLayers {din dout W L : ℕ} (q : ReLUNet din dout W L)
    (k : ℕ) : AffineLayer :=
  if hk : k < q.hidden.length then q.hidden[k]
  else ⟨finalWidth din q.hidden, dout, q.outputWeight, q.outputBias⟩

-- @node: simulationStoredLayers_parameters
/-- For [an index k below the network's hidden depth](hyp:hk),
[the network's parameter encoding matches the weights and biases of its k-th stored layer](goal). -/
lemma simulationStoredLayers_parameters {din dout W L : ℕ}
    (q : ReLUNet din dout W L) (k : ℕ) (hk : k < L) :
    simulationLayerParametersMatch (simulationNetworkParameters q) k
      (simulationStoredLayers q k) := by
  have hk' : k < q.hidden.length := by simpa [q.depth] using hk
  simp only [simulationStoredLayers, dif_pos hk']
  constructor
  · intro j i
    simp [simulationNetworkParameters, hk', j.isLt, i.isLt]
    rfl
  · intro j
    simp [simulationNetworkParameters, hk', j.isLt]
    rfl

-- @node: simulationStoredLayers_width
/-- For [an index k below the hidden depth](hyp:hk),
[the k-th stored layer has at most W output coordinates](goal). -/
lemma simulationStoredLayers_width {din dout W L : ℕ}
    (q : ReLUNet din dout W L) (k : ℕ) (hk : k < L) :
    (simulationStoredLayers q k).output ≤ W := by
  have hk' : k < q.hidden.length := by simpa [q.depth] using hk
  simpa only [simulationStoredLayers, dif_pos hk'] using
    q.widths q.hidden[k] (List.getElem_mem hk')

-- @node: simulationLayerStates_eq_foldl
/-- If [k does not exceed the number of hidden layers](hyp:hk), then
[the recursively evaluated depth-k state equals the result of applying the first
k hidden layers, each followed by ReLU, to the selected sample input](goal). -/
lemma simulationLayerStates_eq_foldl {m din dout W L : ℕ}
    (q : ReLUNet din dout W L) (x : Fin m → ℕ → ℝ)
    (k : ℕ) (hk : k ≤ q.hidden.length) (a : Fin m) :
    simulationLayerStates (simulationStoredLayers q) x k a =
      (q.hidden.take k).foldl (fun z l => reluLayer l z) (x a) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk' : k < q.hidden.length := by omega
    rw [List.take_succ_eq_append_getElem hk', List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    change reluLayer (simulationStoredLayers q k)
      (simulationLayerStates (simulationStoredLayers q) x k a) = _
    rw [ih (by omega)]
    simp only [simulationStoredLayers, dif_pos hk']

/-- The [output polynomial](goal) for [a stored ReLU network](hyp:q),
[an input sample](hyp:sample), [a comparison history](hyp:s),
[a sample index](hyp:a), and [an output coordinate](hyp:j) is the affine readout
of the reconstructed final hidden state, with symbolic output weights and bias. -/
-- @node: simulationHistoryOutputPolynomial
def simulationHistoryOutputPolynomial {din dout W L m : ℕ}
    (q : ReLUNet din dout W L) (sample : Fin m → L1Vec din)
    (s : List (Fin m × Fin W → Bool × Bool)) (a : Fin m) (j : Fin dout) :
    MvPolynomial (ℕ × ℕ × ℕ) ℝ :=
  (∑ i : Fin (finalWidth din q.hidden),
    MvPolynomial.X (L, j.val, i.val + 1) *
      simulationHistoryState (simulationStoredLayers q)
        (fun a => simulationInputPolynomial (sample a)) L s a i.val) +
    MvPolynomial.X (L, j.val, 0)

-- @node: simulationHistoryOutputPolynomial_degree
/-- [The output polynomial for any sample point, output coordinate, and comparison
history has total degree at most the hidden depth plus one](goal). -/
lemma simulationHistoryOutputPolynomial_degree {din dout W L m : ℕ}
    (q : ReLUNet din dout W L) (sample : Fin m → L1Vec din)
    (s : List (Fin m × Fin W → Bool × Bool)) (a : Fin m) (j : Fin dout) :
    (simulationHistoryOutputPolynomial q sample s a j).totalDegree ≤ L + 1 := by
  unfold simulationHistoryOutputPolynomial
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro i _
    have h := simulationHistoryState_degree (simulationStoredLayers q)
      (fun a => simulationInputPolynomial (sample a)) 0
      (fun _ _ => by simp [simulationInputPolynomial]) L s a i.val
    exact (MvPolynomial.totalDegree_mul _ _).trans (by
      simp only [MvPolynomial.totalDegree_X]
      omega)
  · simp only [MvPolynomial.totalDegree_X]
    omega

-- @node: simulationHistoryOutputPolynomial_actual
/-- [Evaluating the output polynomial at the network's stored parameters, with
the comparison history generated by those parameters, gives the network's actual
output at the selected sample point and coordinate](goal). -/
lemma simulationHistoryOutputPolynomial_actual {din dout W L m : ℕ}
    (q : ReLUNet din dout W L) (sample : Fin m → L1Vec din)
    (a : Fin m) (j : Fin dout) :
    MvPolynomial.eval (simulationNetworkParameters q)
      (simulationHistoryOutputPolynomial q sample
        (simulationLayerPatternHistory
          (simulationHistoryTests (w := W) (simulationStoredLayers q)
            (fun a => simulationInputPolynomial (sample a)))
          (simulationNetworkParameters q) L) a j) = (q.eval (sample a)).ofLp j := by
  have h := simulationHistoryState_actual (w := W) (simulationStoredLayers q)
    (fun a => simulationInputPolynomial (sample a)) (simulationNetworkParameters q) L
    (simulationStoredLayers_width q) (simulationStoredLayers_parameters q)
  have hstate (i : ℕ) := (h a i).trans (congrFun
    (simulationLayerStates_eq_foldl q
      (fun a j => MvPolynomial.eval (simulationNetworkParameters q)
        (simulationInputPolynomial (sample a) j)) L q.depth.symm.le a) i)
  simp only [List.take_of_length_le q.depth.le, simulationInputPolynomial, MvPolynomial.eval_C]
    at hstate
  simp only [simulationHistoryOutputPolynomial, map_add, map_sum, map_mul,
    MvPolynomial.eval_X]
  simp_rw [show L = q.hidden.length from q.depth.symm,
    (simulationNetworkParameters_output q).1 j, (simulationNetworkParameters_output q).2 j]
  simp_rw [q.depth, hstate]
  rfl

-- @node: simulationStoredLayers_dimensions
/-- If [the input dimension is at most w](hyp:hdin), [the hidden-width bound is
at most w](hyp:hW), and [k is below the hidden depth](hyp:hk), then
[both the input and output dimensions of the k-th stored layer are at most w](goal). -/
lemma simulationStoredLayers_dimensions {din dout W L : ℕ}
    (q : ReLUNet din dout W L) (w : ℕ) (hdin : din ≤ w) (hW : W ≤ w)
    (k : ℕ) (hk : k < L) :
    (simulationStoredLayers q k).input ≤ w ∧ (simulationStoredLayers q k).output ≤ w := by
  have hk' : k < q.hidden.length := by simpa [q.depth] using hk
  simpa only [simulationStoredLayers, dif_pos hk'] using
    simulation_layer_width_bounds q.hidden din w hdin
      (fun l hl => (q.widths l hl).trans hW) q.firstInput q.compatible
      q.hidden[k] (List.getElem_mem hk')

/-- If [the input dimension is at most w](hyp:hdin), [the output dimension is at
most w](hyp:hdout), and [the hidden-width bound is at most w](hyp:hW), then
[every variable in the output
polynomial belongs to the parameter box for L + 1 layers of width at most w](goal). -/
-- @node: simulationHistoryOutputPolynomial_vars
lemma simulationHistoryOutputPolynomial_vars {din dout W L m : ℕ}
    (q : ReLUNet din dout W L) (sample : Fin m → L1Vec din)
    (s : List (Fin m × Fin W → Bool × Bool)) (a : Fin m) (j : Fin dout)
    (w : ℕ) (hdin : din ≤ w) (hdout : dout ≤ w) (hW : W ≤ w) :
    (simulationHistoryOutputPolynomial q sample s a j).vars ⊆
      simulationParameterBox (L + 1) w := by
  have hs : ∀ i, (simulationHistoryState (simulationStoredLayers q)
      (fun a => simulationInputPolynomial (sample a)) L s a i).vars ⊆
        simulationParameterBox (L + 1) w := by
    intro i
    apply simulationHistoryState_vars
    · intro a j
      simp [simulationInputPolynomial]
    · intro k hk
      have h := simulationStoredLayers_dimensions q w hdin hW k hk
      exact simulationLayerVariables_subset_box (by omega) h.1 h.2
  have ho := simulationLayerVariables_subset_box
    (k := L) (depth := L + 1) (a := finalWidth din q.hidden) (b := dout)
    (by omega) (simulation_finalWidth_le q.hidden din w hdin
      (fun l hl => (q.widths l hl).trans hW)) hdout
  unfold simulationHistoryOutputPolynomial
  apply (MvPolynomial.vars_add_subset _ _).trans
  apply Finset.union_subset
  · apply (MvPolynomial.vars_sum_subset _ _).trans
    apply Finset.biUnion_subset.mpr
    intro i _
    apply (MvPolynomial.vars_mul _ _).trans
    apply Finset.union_subset
    · simp only [MvPolynomial.vars_X, Finset.singleton_subset_iff]
      apply ho
      exact (simulationLayerVariables_mem _ _ _ _ _).mpr ⟨j.isLt, Nat.succ_le_of_lt i.isLt⟩
    · exact hs i.val
  · simp only [MvPolynomial.vars_X, Finset.singleton_subset_iff]
    apply ho
    exact (simulationLayerVariables_mem _ _ _ _ _).mpr ⟨j.isLt, Nat.zero_le _⟩

/-- If [the input dimension is at most w](hyp:hdin) and [the hidden-width bound
is at most w](hyp:hW), then [the number of attainable depth-L comparison histories
on m sample points is at most
$(8mW\max(L,1)+5)^{((L+1)w(w+1)+2)L}$](goal). -/
-- @node: simulationStoredNetwork_histories_encard_le
lemma simulationStoredNetwork_histories_encard_le {din dout W L m : ℕ}
    (q : ReLUNet din dout W L) (sample : Fin m → L1Vec din)
    (w : ℕ) (hdin : din ≤ w) (hW : W ≤ w) :
    (Set.range (fun theta => simulationLayerPatternHistory
      (simulationHistoryTests (w := W) (simulationStoredLayers q)
        (fun a => simulationInputPolynomial (sample a))) theta L)).encard ≤
      ((8 * (m * W) * max L 1 + 5) ^
        (((L + 1) * (w * (w + 1)) + 2) * L) : ℕ) := by
  have h := simulationNetworkHistories_encard_le (w := W) (simulationStoredLayers q)
    (fun a => simulationInputPolynomial (sample a))
    (simulationParameterBox (L + 1) w)
    (fun _ _ => by simp [simulationInputPolynomial]) 0
    (fun _ _ => by simp [simulationInputPolynomial]) L (by
      intro k hk
      have h := simulationStoredLayers_dimensions q w hdin hW k hk
      exact simulationLayerVariables_subset_box (by omega) h.1 h.2)
  simpa [simulationParameterBox, Nat.mul_assoc] using h

end
end Papers.TbsNeuralCausalPi
