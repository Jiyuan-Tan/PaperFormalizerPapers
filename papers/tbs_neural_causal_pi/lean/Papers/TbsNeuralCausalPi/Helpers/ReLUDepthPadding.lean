module
public import Papers.TbsNeuralCausalPi.Helpers.NetworkClipping
/-! # Depth padding without measure-theoretic dependencies -/
public section
namespace Papers.TbsNeuralCausalPi
open scoped NNReal

/-- If [a ReLU network has positive depth](hyp:hL), then [a network with the
same input dimension, output dimension, and width bound exists at depth one
greater and computes exactly the same function on every input](goal). -/
-- @node: relu_pad_one
lemma relu_pad_one {k o W L : ℕ} (q : ReLUNet k o W L) (hL : 0 < L) :
    ∃ Q : ReLUNet k o W (L+1), Q.eval = q.eval := by
  classical
  cases L with
  | zero => omega
  | succ L =>
    obtain ⟨l, hl, hw, r, rfl⟩ := exists_relu_head q
    let identityLayer : AffineLayer :=
      ⟨l.output, l.output, diagonalWeight l.output 1, fun _ => 0⟩
    let R := prependNet identityLayer rfl hw r
    refine ⟨prependNet l hl hw R, ?_⟩
    funext x
    change (prependNet l hl hw R).eval x = (prependNet l hl hw r).eval x
    calc
      _ = R.eval (layerVector l x) := prependNet_eval l hl hw R x
      _ = r.eval (layerVector l x) := ?_
      _ = _ := (prependNet_eval l hl hw r x).symm
    change (prependNet identityLayer rfl hw r).eval (layerVector l x) = _
    erw [prependNet_eval]
    congr 1
    apply PiLp.ext
    intro j
    erw [layerVector_apply]
    change max 0 ((∑ i : Fin l.output, diagonalWeight l.output 1 j i *
      (if h : i.val < l.output then (layerVector l x).ofLp ⟨i.val, h⟩ else 0)) + 0) = _
    simp only [dif_pos (Fin.isLt _), add_zero]
    erw [diagonalWeight_sum]
    simp only [one_mul]
    apply max_eq_right
    exact le_max_left _ _

-- @node: relu_pad_depth
/-- If [a ReLU network has positive depth](hyp:hL) and [the desired depth is
at least its current depth](hyp:hle), then [a network at the desired depth
with the same width bound computes exactly the same function on every input](goal). -/
lemma relu_pad_depth {k o W L L' : ℕ} (q : ReLUNet k o W L)
    (hL : 0 < L) (hle : L ≤ L') :
    ∃ Q : ReLUNet k o W L', Q.eval = q.eval := by
  induction L', hle using Nat.le_induction with
  | base => exact ⟨q, rfl⟩
  | succ m hm ih =>
    obtain ⟨R, hR⟩ := ih
    obtain ⟨Q, hQ⟩ := relu_pad_one R (hL.trans_le hm)
    exact ⟨Q, hQ.trans hR⟩

end Papers.TbsNeuralCausalPi
