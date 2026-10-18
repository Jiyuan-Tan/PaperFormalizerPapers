module
public import Papers.TbsNeuralCausalPi.Helpers.SimulationNetworkComparisons
/-! # Counted activation histories with signed affine bridges

The output of the first generator block is signed and enters the second block
without a ReLU. A flag at each layer retains this affine bridge while using the
same successive polynomial-sign envelope as the hidden ReLU layers.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
noncomputable section

-- @node: simulationBridgeState
/-- Given [a sequence of affine layers](hyp:layers), [flags specifying which
layers apply ReLU](hyp:activate), and [initial polynomials for each sample and
coordinate](hyp:z), the [polynomial state after a given number of layers](goal)
is [the initial state at zero layers](step:1), and [at the next layer applies
the masked ReLU polynomial when flagged, or the signed affine polynomial
otherwise, using the remaining history for the preceding state](step:2). -/
def simulationBridgeState {m w : ℕ} (layers : ℕ → AffineLayer) (activate : ℕ → Bool)
    (z : Fin m → ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ) :
    ℕ → List (Fin m × Fin w → Bool × Bool) →
      Fin m → ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ
  | 0, _, a, j => z a j
  | k + 1, s, a, j =>
    if activate k then simulationReluPolynomial (layers k) k
      (simulationHistoryMask s a) (simulationBridgeState layers activate z k s.tail a) j
    else simulationAffinePolynomial (layers k) k
      (simulationBridgeState layers activate z k s.tail a) j

-- @node: simulationBridgeTests
/-- For [affine layers](hyp:layers), [ReLU flags](hyp:activate), [initial
sample polynomials](hyp:z), [a layer index](hyp:k), [a comparison history](hyp:s),
and [a sample and coordinate pair](hyp:aj), the [bridge comparison polynomial](goal)
is the negative of the next affine output computed from the polynomial state
at that history. -/
def simulationBridgeTests {m w : ℕ} (layers : ℕ → AffineLayer) (activate : ℕ → Bool)
    (z : Fin m → ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ)
    (k : ℕ) (s : List (Fin m × Fin w → Bool × Bool)) (aj : Fin m × Fin w) :
    MvPolynomial (ℕ × ℕ × ℕ) ℝ :=
  -simulationAffinePolynomial (layers k) k
    (simulationBridgeState layers activate z k s aj.1) aj.2

-- @node: simulationBridgeStates
/-- For [affine layers](hyp:layers), [flags selecting ReLU layers](hyp:activate),
and [initial real sample states](hyp:x), the [real state sequence](goal)
[starts at the initial states](step:1) and [advances by applying a ReLU layer
when flagged and a signed affine layer otherwise](step:2). -/
def simulationBridgeStates {m : ℕ} (layers : ℕ → AffineLayer) (activate : ℕ → Bool)
    (x : Fin m → ℕ → ℝ) : ℕ → Fin m → ℕ → ℝ
  | 0 => x
  | k + 1 => fun a => if activate k then reluLayer (layers k)
      (simulationBridgeStates layers activate x k a)
    else (layers k).apply (simulationBridgeStates layers activate x k a)

-- @node: simulationBridgeState_degree
/-- If [all initial sample polynomials have total degree at most d](hyp:hz),
then [every polynomial state after k layers has total degree at most d plus
k](goal), for any comparison history and choice of ReLU flags. -/
lemma simulationBridgeState_degree {m w : ℕ} (layers : ℕ → AffineLayer)
    (activate : ℕ → Bool) (z : Fin m → ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ)
    (d : ℕ) (hz : ∀ a j, (z a j).totalDegree ≤ d)
    (k : ℕ) (s : List (Fin m × Fin w → Bool × Bool)) (a : Fin m) (j : ℕ) :
    (simulationBridgeState layers activate z k s a j).totalDegree ≤ d + k := by
  induction k generalizing s j with
  | zero => exact hz a j
  | succ k ih =>
    simp only [simulationBridgeState]
    split
    · exact (simulationReluPolynomial_degree _ k (d + k) _ _
        (fun j => ih s.tail j) j).trans (by omega)
    · exact (simulationAffinePolynomial_degree _ k (d + k) _
        (fun j => ih s.tail j) j).trans (by omega)

-- @node: simulationBridgeState_vars
/-- If [all initial sample polynomials use only variables in the finite set
S](hyp:hz) and [all weight and bias variables of layers before t belong to
S](hyp:hl), then [every polynomial state after t layers uses only variables
in S](goal), for any comparison history. -/
lemma simulationBridgeState_vars {m w : ℕ} (layers : ℕ → AffineLayer)
    (activate : ℕ → Bool) (z : Fin m → ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ)
    (S : Finset (ℕ × ℕ × ℕ)) (hz : ∀ a j, (z a j).vars ⊆ S)
    (t : ℕ) (hl : ∀ k < t, simulationLayerVariables k (layers k).input (layers k).output ⊆ S)
    (s : List (Fin m × Fin w → Bool × Bool)) (a : Fin m) (j : ℕ) :
    (simulationBridgeState layers activate z t s a j).vars ⊆ S := by
  induction t generalizing s j with
  | zero => exact hz a j
  | succ t ih =>
    have hprev := fun j => ih (fun k hk => hl k (by omega)) s.tail j
    simp only [simulationBridgeState]
    split
    · exact (simulationReluPolynomial_vars _ t _ _ S hprev j).trans
        (Finset.union_subset (hl t (by omega)) Finset.Subset.rfl)
    · exact (simulationAffinePolynomial_vars _ t _ S hprev j).trans
        (Finset.union_subset (hl t (by omega)) Finset.Subset.rfl)

-- @node: simulationBridgeTests_degree
/-- If [all initial sample polynomials have total degree at most d](hyp:hz),
then [each bridge comparison polynomial at layer k has total degree at most
d plus k plus one](goal), for any comparison history. -/
lemma simulationBridgeTests_degree {m w : ℕ} (layers : ℕ → AffineLayer)
    (activate : ℕ → Bool) (z : Fin m → ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ)
    (d : ℕ) (hz : ∀ a j, (z a j).totalDegree ≤ d)
    (k : ℕ) (s : List (Fin m × Fin w → Bool × Bool)) (aj : Fin m × Fin w) :
    (simulationBridgeTests layers activate z k s aj).totalDegree ≤ d + k + 1 := by
  rw [simulationBridgeTests, MvPolynomial.totalDegree_neg]
  exact simulationAffinePolynomial_degree _ k (d + k) _
    (simulationBridgeState_degree layers activate z d hz k s aj.1) _

-- @node: simulationBridgeTests_vars
/-- If [the initial sample polynomials use only variables in S](hyp:hz),
[all weight and bias variables of layers before t belong to S](hyp:hl), and
[the tested layer k precedes t](hyp:hk), then [its bridge comparison polynomial
uses only variables in S](goal), for any history and sample-coordinate pair. -/
lemma simulationBridgeTests_vars {m w : ℕ} (layers : ℕ → AffineLayer)
    (activate : ℕ → Bool) (z : Fin m → ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ)
    (S : Finset (ℕ × ℕ × ℕ)) (hz : ∀ a j, (z a j).vars ⊆ S)
    (t : ℕ) (hl : ∀ k < t, simulationLayerVariables k (layers k).input (layers k).output ⊆ S)
    (k : ℕ) (hk : k < t) (s : List (Fin m × Fin w → Bool × Bool))
    (aj : Fin m × Fin w) : (simulationBridgeTests layers activate z k s aj).vars ⊆ S := by
  rw [simulationBridgeTests, MvPolynomial.vars_neg]
  exact (simulationAffinePolynomial_vars _ k _ S
    (simulationBridgeState_vars layers activate z S hz k
      (fun r hr => hl r (hr.trans hk)) s aj.1) _).trans
    (Finset.union_subset (hl k hk) Finset.Subset.rfl)

-- @node: simulationBridgeMask_actual
/-- If [the layer's output dimension is at most the comparison width](hyp:hw),
then [the activation bit extracted from the actual comparison history through
that layer is true exactly when its affine output polynomial, formed using
the preceding history, evaluates to a nonnegative number](goal), at every
sample and coordinate. -/
lemma simulationBridgeMask_actual {m w : ℕ} (layers : ℕ → AffineLayer)
    (activate : ℕ → Bool) (z : Fin m → ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ)
    (theta : (ℕ × ℕ × ℕ) → ℝ) (k : ℕ)
    (hw : (layers k).output ≤ w) (a : Fin m) (j : ℕ) :
    simulationHistoryMask
      (simulationLayerPatternHistory (simulationBridgeTests (w := w) layers activate z)
        theta (k + 1)) a j =
      decide (0 ≤ MvPolynomial.eval theta (simulationAffinePolynomial (layers k) k
        (simulationBridgeState layers activate z k
          (simulationLayerPatternHistory (simulationBridgeTests (w := w) layers activate z)
            theta k) a) j)) := by
  by_cases hj : j < w
  · simp [simulationHistoryMask, hj, simulationLayerPatternHistory,
      polynomialComparisonPattern, simulationBridgeTests]
  · have hout : ¬ j < (layers k).output := by omega
    simp [simulationHistoryMask, hj, simulationAffinePolynomial, hout]

-- @node: simulationBridgeState_actual
/-- If [every layer before t has output dimension at most the comparison
width](hyp:hw) and [the parameter assignment matches every such layer's
weights and biases](hyp:hparam), then [evaluating the polynomial state along
its actual comparison history gives the real state after t layers, for
every sample and coordinate](goal), starting from the evaluated initial
polynomials and retaining signed affine outputs at unflagged layers. -/
lemma simulationBridgeState_actual {m w : ℕ} (layers : ℕ → AffineLayer)
    (activate : ℕ → Bool) (z : Fin m → ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ)
    (theta : (ℕ × ℕ × ℕ) → ℝ) (t : ℕ)
    (hw : ∀ k < t, (layers k).output ≤ w)
    (hparam : ∀ k < t, simulationLayerParametersMatch theta k (layers k)) :
    ∀ a j, MvPolynomial.eval theta (simulationBridgeState layers activate z t
      (simulationLayerPatternHistory (simulationBridgeTests (w := w) layers activate z)
        theta t) a j) =
      simulationBridgeStates layers activate (fun a j => MvPolynomial.eval theta (z a j)) t a j := by
  induction t with
  | zero => intro a j; rfl
  | succ t ih =>
    intro a j
    have hprev : (fun i => MvPolynomial.eval theta (simulationBridgeState layers activate z t
        (simulationLayerPatternHistory (simulationBridgeTests (w := w) layers activate z)
          theta t) a i)) =
        simulationBridgeStates layers activate (fun a j => MvPolynomial.eval theta (z a j)) t a :=
      funext (ih (fun k hk => hw k (by omega)) (fun k hk => hparam k (by omega)) a)
    have htail : (simulationLayerPatternHistory
        (simulationBridgeTests (w := w) layers activate z) theta (t + 1)).tail =
        simulationLayerPatternHistory (simulationBridgeTests (w := w) layers activate z)
          theta t := rfl
    simp only [simulationBridgeState, simulationBridgeStates, htail]
    split
    · rw [simulationReluPolynomial_eval _ t theta (hparam t (by omega)) _ _
        (simulationBridgeMask_actual layers activate z theta t (hw t (by omega)) a)]
      change reluLayer _ (fun i => MvPolynomial.eval theta (simulationBridgeState layers activate z t
        (simulationLayerPatternHistory (simulationBridgeTests (w := w) layers activate z)
          theta t) a i)) j = _
      rw [hprev]
    · rw [simulationAffinePolynomial_eval _ t theta (hparam t (by omega))]
      change (layers t).apply (fun i => MvPolynomial.eval theta (simulationBridgeState layers activate z t
        (simulationLayerPatternHistory (simulationBridgeTests (w := w) layers activate z)
          theta t) a i)) j = _
      rw [hprev]

-- @node: simulationBridgeHistories_encard_le
/-- If [the initial sample polynomials use only variables in S](hyp:hz),
[have total degree at most d](hyp:hdeg), and [every weight and bias variable
of each layer before t belongs to S](hyp:hl), then [the number of distinct
comparison histories through t layers, as the parameter assignment varies,
is at most the quantity eight times the number of samples times the comparison
width times the larger of d plus t and one, plus five, raised to the power
of t times the sum of the size of S and two](goal). Signed affine layers each count as
one stage, just as ReLU layers do. -/
lemma simulationBridgeHistories_encard_le {m w : ℕ} (layers : ℕ → AffineLayer)
    (activate : ℕ → Bool) (z : Fin m → ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ)
    (S : Finset (ℕ × ℕ × ℕ)) (hz : ∀ a j, (z a j).vars ⊆ S)
    (d : ℕ) (hdeg : ∀ a j, (z a j).totalDegree ≤ d)
    (t : ℕ) (hl : ∀ k < t, simulationLayerVariables k (layers k).input (layers k).output ⊆ S) :
    (Set.range (fun theta => simulationLayerPatternHistory
      (simulationBridgeTests (w := w) layers activate z) theta t)).encard ≤
      ((8 * (m * w) * max (d + t) 1 + 5) ^ ((S.card + 2) * t) : ℕ) := by
  let p := fun k s i => if k < t then
    simulationBridgeTests (w := w) layers activate z k s i else 0
  have heq (theta) : simulationLayerPatternHistory
      (simulationBridgeTests (w := w) layers activate z) theta t =
      simulationLayerPatternHistory p theta t := by
    apply simulationLayerPatternHistory_congr_prefix
    intro k hk s
    funext i
    simp [p, hk]
  have h := simulationLayerPatternHistory_supported_encard_le S p
    (fun k s i => by
      by_cases hk : k < t
      · simpa only [p, if_pos hk] using
          simulationBridgeTests_vars layers activate z S hz t hl k hk s i
      · simp [p, hk]) (d + t) t
    (fun k hk s i => by
      simp only [p, if_pos hk]
      exact (simulationBridgeTests_degree layers activate z d hdeg k s i).trans (by omega))
  simpa only [← heq, Fintype.card_prod, Fintype.card_fin] using h

end
end Papers.TbsNeuralCausalPi
