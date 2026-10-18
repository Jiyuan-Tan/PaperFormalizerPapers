module
public import Papers.TbsNeuralCausalPi.Helpers.SimulationAffineBridge
/-! # Actual two-block generator histories

Both signed affine outputs are retained. The first one is the input to the
second block, and the last one supplies the component values for the mixture.
All parameters use the existing disjoint two-block assignment.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
noncomputable section

-- @node: simulationStoredLayers_parameters_le
/-- If [the layer index is at most the hidden depth](hyp:hk), [the stored layer,
including the final output layer, matches the network's assigned weights and biases](goal). -/
lemma simulationStoredLayers_parameters_le {din dout W L : ℕ}
    (q : ReLUNet din dout W L) (k : ℕ) (hk : k ≤ L) :
    simulationLayerParametersMatch (simulationNetworkParameters q) k
      (simulationStoredLayers q k) := by
  by_cases hlt : k < L
  · exact simulationStoredLayers_parameters q k hlt
  · have he : k = L := by omega
    subst k
    rw [simulationStoredLayers, dif_neg (by rw [q.depth]; omega : ¬ L < q.hidden.length)]
    simpa only [simulationLayerParametersMatch, AffineLayer.input, AffineLayer.output, q.depth] using
      simulationNetworkParameters_output q

-- @node: simulationStoredLayers_dimensions_le
/-- If [the input and output dimensions and the hidden width are at most the
common width bound](hyp:hdin,hdout,hW), and [the layer index
is at most the hidden depth](hyp:hk), [both dimensions of the stored layer are
at most that bound](goal). -/
lemma simulationStoredLayers_dimensions_le {din dout W L : ℕ}
    (q : ReLUNet din dout W L) (w : ℕ) (hdin : din ≤ w) (hdout : dout ≤ w)
    (hW : W ≤ w) (k : ℕ) (hk : k ≤ L) :
    (simulationStoredLayers q k).input ≤ w ∧ (simulationStoredLayers q k).output ≤ w := by
  by_cases hlt : k < L
  · exact simulationStoredLayers_dimensions q w hdin hW k hlt
  · have he : k = L := by omega
    subst k
    rw [simulationStoredLayers, dif_neg (by rw [q.depth]; omega : ¬ L < q.hidden.length)]
    change finalWidth din q.hidden ≤ w ∧ dout ≤ w
    exact ⟨simulation_finalWidth_le q.hidden din w hdin
      (fun l hl => (q.widths l hl).trans hW), hdout⟩

/-- If [the block's layers equal the stored network layers](hyp:hl), [activation
is applied exactly to its hidden layers](hyp:ha), and [its starting states are
the zero-padded sample inputs](hyp:hx), [its ending states are the zero-padded
network evaluations, retaining signed outputs](goal). -/
-- @node: simulationBridgeStates_network_eval
lemma simulationBridgeStates_network_eval {din dout W L m : ℕ}
    (q : ReLUNet din dout W L) (layers : ℕ → AffineLayer) (activate : ℕ → Bool)
    (x : Fin m → ℕ → ℝ) (sample : Fin m → L1Vec din) (offset : ℕ)
    (hl : ∀ k ≤ L, layers (offset + k) = simulationStoredLayers q k)
    (ha : ∀ k ≤ L, activate (offset + k) = decide (k < L))
    (hx : ∀ a j, simulationBridgeStates layers activate x offset a j =
      if hj : j < din then (sample a).ofLp ⟨j, hj⟩ else 0) :
    ∀ a j, simulationBridgeStates layers activate x (offset + L + 1) a j =
      if hj : j < dout then (q.eval (sample a)).ofLp ⟨j, hj⟩ else 0 := by
  have hh (k : ℕ) (hk : k ≤ L) (a : Fin m) :
      simulationBridgeStates layers activate x (offset + k) a =
      (q.hidden.take k).foldl (fun z l => reluLayer l z)
        (fun j => if hj : j < din then (sample a).ofLp ⟨j, hj⟩ else 0) := by
    induction k with
    | zero => exact funext (hx a)
    | succ k ih =>
      have hk' : k < q.hidden.length := by rw [q.depth]; omega
      rw [show offset + (k + 1) = (offset + k) + 1 by omega,
        simulationBridgeStates, ha k (by omega)]
      simp only [decide_eq_true_eq, if_pos (show k < L by omega)]
      rw [hl k (by omega), ih (by omega), List.take_succ_eq_append_getElem hk',
        List.foldl_append]
      simp only [simulationStoredLayers, dif_pos hk', List.foldl_cons, List.foldl_nil]
  intro a j
  rw [simulationBridgeStates, ha L le_rfl]
  simp only [lt_self_iff_false, decide_false, Bool.false_eq_true, if_false]
  rw [hl L le_rfl, hh L le_rfl a]
  rw [simulationStoredLayers, dif_neg (by rw [q.depth]; omega : ¬ L < q.hidden.length),
    List.take_of_length_le q.depth.le]
  change (if hj : j < dout then _ else 0) = _
  split_ifs <;> rfl

-- @node: simulationTwoBlockLayers
/-- For [a first network](hyp:q1), [a second network taking its outputs as
inputs](hyp:q2), and [a layer index](hyp:k), [the concatenated affine layer](goal)
is [the first network's stored layer through its output layer](step:1), or
[the second network's stored layer at the shifted index thereafter](step:2). -/
def simulationTwoBlockLayers {din dmid dout W1 W2 L1 L2 : ℕ}
    (q1 : ReLUNet din dmid W1 L1) (q2 : ReLUNet dmid dout W2 L2) (k : ℕ) :
    AffineLayer :=
  if k ≤ L1 then simulationStoredLayers q1 k
  else simulationStoredLayers q2 (k - (L1 + 1))

-- @node: simulationTwoBlockActivate
/-- For [the first hidden depth](hyp:L1), [the second hidden depth](hyp:L2), and
[a layer index](hyp:k), [the activation indicator](goal) is true exactly when
the index is neither block's affine output layer. -/
def simulationTwoBlockActivate (L1 L2 k : ℕ) : Bool :=
  decide (k ≠ L1 ∧ k ≠ L1 + L2 + 1)

-- @node: simulationTwoBlockLayers_parameters
/-- If [the layer index lies within the two concatenated blocks](hyp:hk),
[the concatenated layer matches the weights and biases in the two-block
parameter assignment](goal). -/
lemma simulationTwoBlockLayers_parameters {din dmid dout W1 W2 L1 L2 : ℕ}
    (q1 : ReLUNet din dmid W1 L1) (q2 : ReLUNet dmid dout W2 L2)
    (k : ℕ) (hk : k < L1 + L2 + 2) :
    simulationLayerParametersMatch (simulationTwoBlockParameters q1 q2) k
      (simulationTwoBlockLayers q1 q2 k) := by
  by_cases h : k ≤ L1
  · have hp := simulationStoredLayers_parameters_le q1 k h
    simp only [simulationTwoBlockLayers, if_pos h]
    constructor
    · intro j i
      simpa only [simulationTwoBlockParameters, q1.depth, if_pos h] using hp.1 j i
    · intro j
      simpa only [simulationTwoBlockParameters, q1.depth, if_pos h] using hp.2 j
  · have hp := simulationStoredLayers_parameters_le q2 (k - (L1 + 1)) (by omega)
    simp only [simulationTwoBlockLayers, if_neg h]
    constructor
    · intro j i
      simpa only [simulationTwoBlockParameters, q1.depth, if_neg h] using hp.1 j i
    · intro j
      simpa only [simulationTwoBlockParameters, q1.depth, if_neg h] using hp.2 j

-- @node: simulationTwoBlockLayers_dimensions
/-- If [the input, intermediate, and output dimensions and both hidden widths
are at most the common width bound](hyp:hdin,hdmid,hdout,hW1,hW2), and [the layer index lies within the two
blocks](hyp:hk), [both dimensions of that layer are at most the bound](goal). -/
lemma simulationTwoBlockLayers_dimensions {din dmid dout W1 W2 L1 L2 : ℕ}
    (q1 : ReLUNet din dmid W1 L1) (q2 : ReLUNet dmid dout W2 L2)
    (w : ℕ) (hdin : din ≤ w) (hdmid : dmid ≤ w) (hdout : dout ≤ w)
    (hW1 : W1 ≤ w) (hW2 : W2 ≤ w) (k : ℕ) (hk : k < L1 + L2 + 2) :
    (simulationTwoBlockLayers q1 q2 k).input ≤ w ∧
      (simulationTwoBlockLayers q1 q2 k).output ≤ w := by
  unfold simulationTwoBlockLayers
  split_ifs with h
  · exact simulationStoredLayers_dimensions_le q1 w hdin hdmid hW1 k h
  · exact simulationStoredLayers_dimensions_le q2 w hdmid hdout hW2 _ (by omega)

-- @node: simulationTwoBlockStates_actual
/-- [After both blocks, every bridge state equals the corresponding coordinate
of the second network evaluated at the first network's output, with zeros
beyond the output dimension](goal). -/
lemma simulationTwoBlockStates_actual {din dmid dout W1 W2 L1 L2 m : ℕ}
    (q1 : ReLUNet din dmid W1 L1) (q2 : ReLUNet dmid dout W2 L2)
    (sample : Fin m → L1Vec din) :
    ∀ a j, simulationBridgeStates (simulationTwoBlockLayers q1 q2)
      (simulationTwoBlockActivate L1 L2)
      (fun a j => if hj : j < din then (sample a).ofLp ⟨j, hj⟩ else 0)
      (L1 + L2 + 2) a j =
      if hj : j < dout then (q2.eval (q1.eval (sample a))).ofLp ⟨j, hj⟩ else 0 := by
  let x : Fin m → ℕ → ℝ := fun a j =>
    if hj : j < din then (sample a).ofLp ⟨j, hj⟩ else 0
  have hfirst := simulationBridgeStates_network_eval q1 (simulationTwoBlockLayers q1 q2)
    (simulationTwoBlockActivate L1 L2) x sample 0
    (by intro k hk; simp [simulationTwoBlockLayers, hk])
    (by
      intro k hk
      simp only [zero_add, simulationTwoBlockActivate, decide_eq_decide]
      omega)
    (by intro a j; rfl)
  have hsecond := simulationBridgeStates_network_eval q2 (simulationTwoBlockLayers q1 q2)
    (simulationTwoBlockActivate L1 L2) x (fun a => q1.eval (sample a)) (L1 + 1)
    (by
      intro k hk
      simp [simulationTwoBlockLayers, show ¬ L1 + 1 + k ≤ L1 by omega])
    (by
      intro k hk
      simp only [simulationTwoBlockActivate, decide_eq_decide]
      omega)
    (by simpa only [zero_add] using hfirst)
  simpa only [show L1 + 1 + L2 + 1 = L1 + L2 + 2 by omega] using hsecond

/-- If [the input, intermediate, and output dimensions and both hidden widths
are at most the common width bound](hyp:hdin,hdmid,hdout,hW1,hW2), [evaluating the final bridge polynomial with the
actual parameters and their sign history recovers the selected coordinate
of the composed networks on the selected sample](goal). -/
-- @node: simulationTwoBlockHistory_actual
lemma simulationTwoBlockHistory_actual {din dmid dout W1 W2 L1 L2 m : ℕ}
    (q1 : ReLUNet din dmid W1 L1) (q2 : ReLUNet dmid dout W2 L2)
    (sample : Fin m → L1Vec din) (w : ℕ)
    (hdin : din ≤ w) (hdmid : dmid ≤ w) (hdout : dout ≤ w)
    (hW1 : W1 ≤ w) (hW2 : W2 ≤ w) (a : Fin m) (j : Fin dout) :
    MvPolynomial.eval (simulationTwoBlockParameters q1 q2)
      (simulationBridgeState (simulationTwoBlockLayers q1 q2)
        (simulationTwoBlockActivate L1 L2) (fun a => simulationInputPolynomial (sample a))
        (L1 + L2 + 2)
        (simulationLayerPatternHistory
          (simulationBridgeTests (w := w) (simulationTwoBlockLayers q1 q2)
            (simulationTwoBlockActivate L1 L2) (fun a => simulationInputPolynomial (sample a)))
          (simulationTwoBlockParameters q1 q2) (L1 + L2 + 2)) a j) =
      (q2.eval (q1.eval (sample a))).ofLp j := by
  rw [simulationBridgeState_actual _ _ _ _ _
    (fun k hk => (simulationTwoBlockLayers_dimensions q1 q2 w
      hdin hdmid hdout hW1 hW2 k hk).2)
    (simulationTwoBlockLayers_parameters q1 q2)]
  simp only [simulationInputPolynomial, MvPolynomial.eval_C]
  rw [simulationTwoBlockStates_actual]
  simp only [j.isLt, dite_true]

-- @node: simulationTwoBlockHistories_encard_le
/-- If [the input, intermediate, and output dimensions and both hidden widths
are at most the common width bound](hyp:hdin,hdmid,hdout,hW1,hW2), [the number of
two-block sign histories is at most $(8mwT+5)^{(Tw(w+1)+2)T}$, where $m$ is
sample size, $w$ is the common width bound, and $T$ is the sum of the two hidden
depths plus two](goal). -/
lemma simulationTwoBlockHistories_encard_le {din dmid dout W1 W2 L1 L2 m : ℕ}
    (q1 : ReLUNet din dmid W1 L1) (q2 : ReLUNet dmid dout W2 L2)
    (sample : Fin m → L1Vec din) (w : ℕ)
    (hdin : din ≤ w) (hdmid : dmid ≤ w) (hdout : dout ≤ w)
    (hW1 : W1 ≤ w) (hW2 : W2 ≤ w) :
    (Set.range (fun theta => simulationLayerPatternHistory
      (simulationBridgeTests (w := w) (simulationTwoBlockLayers q1 q2)
        (simulationTwoBlockActivate L1 L2) (fun a => simulationInputPolynomial (sample a)))
      theta (L1 + L2 + 2))).encard ≤
      ((8 * (m * w) * (L1 + L2 + 2) + 5) ^
        (((L1 + L2 + 2) * (w * (w + 1)) + 2) * (L1 + L2 + 2)) : ℕ) := by
  have h := simulationBridgeHistories_encard_le (w := w) (simulationTwoBlockLayers q1 q2)
    (simulationTwoBlockActivate L1 L2) (fun a => simulationInputPolynomial (sample a))
    (simulationParameterBox (L1 + L2 + 2) w)
    (by intro a j; simp [simulationInputPolynomial])
    0 (by intro a j; simp [simulationInputPolynomial]) (L1 + L2 + 2)
    (by
      intro k hk
      have hd := simulationTwoBlockLayers_dimensions q1 q2 w hdin hdmid hdout hW1 hW2 k hk
      exact simulationLayerVariables_subset_box hk hd.1 hd.2)
  have hcard : (simulationParameterBox (L1 + L2 + 2) w).card =
      (L1 + L2 + 2) * (w * (w + 1)) := by simp [simulationParameterBox]
  simpa only [zero_add, hcard,
    max_eq_left (show 1 ≤ L1 + L2 + 2 by omega)] using h

end
end Papers.TbsNeuralCausalPi
