module
public import Papers.TbsNeuralCausalPi.Helpers.AffineNetworkInputs
public import Papers.TbsNeuralCausalPi.Helpers.StructuralNodalBasis
public import Mathlib.Data.Nat.Log
/-! # Balanced ReLU minimum trees for structural nodal hats

Affine outputs can be absorbed into the next network's first affine map.
The signed binary minimum therefore costs one hidden layer. Balanced trees
realize the nodal finite minimum with logarithmic depth.
-/
@[expose] public section

namespace Papers.TbsNeuralCausalPi
noncomputable section
open scoped BigOperators NNReal
set_option backward.isDefEq.respectTransparency false

/-- Given [a first ReLU network](hyp:q) and [a second ReLU network whose input
dimension matches the first network's output dimension](hyp:r), [their composition
is realized by a ReLU network with width bounded by the larger of their width
budgets and hidden depth equal to the sum of their hidden depths](goal). -/
-- @node: relu_comp_constructed
lemma relu_comp_constructed {a k o W V L H : ℕ}
    (q : ReLUNet k a W L) (r : ReLUNet a o V H) :
    ∃ Q : ReLUNet k o (max W V) (L + H), Q.eval = r.eval ∘ q.eval := by
  classical
  induction L generalizing k with
  | zero =>
    rw [Nat.zero_add]
    rcases q with ⟨ls, hd, hw, hf, hc, ow, ob⟩
    have hs : ls = [] := List.length_eq_zero_iff.mp hd
    subst ls
    change Fin a → Fin k → ℝ at ow
    obtain ⟨Q, hQ⟩ := relu_affine_precomp (r.widen (le_max_right W V)) ow ob
    refine ⟨Q, ?_⟩
    funext x
    rw [hQ, ReLUNet.widen_eval]
    congr 1
    apply PiLp.ext
    intro j
    change (∑ i : Fin k, ow j i * x.ofLp i) + ob j =
      (∑ i : Fin k, ow j i * (if h : i.val < k then x.ofLp ⟨i.val, h⟩ else 0)) + ob j
    simp only [dif_pos (Fin.isLt _)]
  | succ L ih =>
    obtain ⟨l, hl, hw, t, rfl⟩ := exists_relu_head q
    obtain ⟨R, hR⟩ := ih t
    rw [Nat.succ_add]
    refine ⟨prependNet l hl (hw.trans (le_max_left W V)) R, ?_⟩
    funext x
    simp only [prependNet_eval, hR, Function.comp_apply]

/-- For [a real number a](hyp:a) and [a real number b](hyp:b), [the positive part
of a minus the positive part of its negative, minus the positive part of a minus b,
equals the smaller of a and b](goal). -/
-- @node: structural_signed_relu_identity
lemma structural_signed_relu_identity (a b : ℝ) :
    max 0 a - max 0 (-a) - max 0 (a - b) = min a b := by
  have ha : max 0 a - max 0 (-a) = a := by
    by_cases h : 0 ≤ a
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left (le_of_not_ge h), max_eq_right (by linarith)]; ring
  rw [ha]
  by_cases h : a ≤ b
  · rw [max_eq_left (sub_nonpos.mpr h), sub_zero, min_eq_left h]
  · rw [max_eq_right (by linarith), min_eq_right (le_of_not_ge h)]; ring

/-- [There exists a ReLU network with two inputs, one output, width at most three,
and one hidden layer that returns the smaller input for every input pair](goal). -/
-- @node: relu_binary_min
lemma relu_binary_min :
    ∃ Q : ReLUNet 2 1 3 1, ∀ x,
      (Q.eval x).ofLp 0 = min (x.ofLp 0) (x.ofLp 1) := by
  let l : AffineLayer := ⟨2, 3,
    ![![1, 0], ![-1, 0], ![1, -1]], fun _ => 0⟩
  let out : ReLUNet 3 1 3 0 := affineNet (fun _ => ![1, -1, -1]) (fun _ => 0)
  refine ⟨prependNet l rfl le_rfl out, ?_⟩
  intro x
  rw [prependNet_eval, affineNet_eval]
  change (∑ i : Fin 3, (![1, -1, -1] : Fin 3 → ℝ) i *
    (layerVector l x).ofLp i) + 0 = _
  simp only [Fin.sum_univ_three]
  have hl (j : Fin 3) : (layerVector l x).ofLp j =
      max 0 ((∑ i : Fin 2, l.2.2.1 j i * x.ofLp i) + l.2.2.2 j) := by
    erw [layerVector_apply]
    dsimp only [l, AffineLayer.input]
    simp only [dif_pos (Fin.isLt _)]
  simp only [hl, l, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, 
    Fin.isValue, one_mul, zero_mul, neg_mul, add_zero]
  simpa only [sub_eq_add_neg] using
    structural_signed_relu_identity (x.ofLp 0) (x.ofLp 1)


/-- Given [a tree depth h](hyp:h), [an input dimension k](hyp:k),
[coefficient vectors for two to the power h affine functions](hyp:A), and
[their intercepts](hyp:b), [there exists a scalar-output ReLU network with h
hidden layers and width at most three times two to the power h whose output,
at every input, is no larger than any of these affine functions and equals
at least one of them](goal). -/
-- @node: relu_affine_min_tree
lemma relu_affine_min_tree (h k : ℕ)
    (A : Fin (2 ^ h) → Fin k → ℝ) (b : Fin (2 ^ h) → ℝ) :
    ∃ Q : ReLUNet k 1 (3 * 2 ^ h) h, ∀ x,
      (∀ i, (Q.eval x).ofLp 0 ≤ (∑ j, A i j * x.ofLp j) + b i) ∧
      ∃ i, (Q.eval x).ofLp 0 = (∑ j, A i j * x.ofLp j) + b i := by
  classical
  induction h with
  | zero =>
    refine ⟨affineNet (fun _ => A 0) (fun _ => b 0), ?_⟩
    intro x
    rw [affineNet_eval]
    exact ⟨fun i => by fin_cases i; exact le_rfl, 0, rfl⟩
  | succ h ih =>
    let e : Fin (2 ^ h) ⊕ Fin (2 ^ h) ≃ Fin (2 ^ (h+1)) :=
      finSumFinEquiv.trans (finCongr (by rw [pow_succ]; omega))
    obtain ⟨q₀, h₀⟩ := ih (fun i => A (e (Sum.inl i))) (fun i => b (e (Sum.inl i)))
    obtain ⟨q₁, h₁⟩ := ih (fun i => A (e (Sum.inr i))) (fun i => b (e (Sum.inr i)))
    obtain ⟨P, hP⟩ := relu_parallel_stack_constructed ![q₀, q₁]
    obtain ⟨M, hM⟩ := relu_binary_min
    obtain ⟨Q, hQ⟩ := relu_comp_constructed P M
    have hw : max (2 * (3 * 2 ^ h)) 3 ≤ 3 * 2 ^ (h+1) := by
      have hp : 0 < 2 ^ h := by positivity
      rw [pow_succ]
      omega
    refine ⟨Q.widen hw, ?_⟩
    intro x
    have hv : ((Q.widen hw).eval x).ofLp 0 =
        min ((q₀.eval x).ofLp 0) ((q₁.eval x).ofLp 0) := by
      rw [ReLUNet.widen_eval, hQ, Function.comp_apply, hM, hP, hP]
      rfl
    rw [hv]
    refine ⟨?_, ?_⟩
    · intro i
      obtain ⟨j, rfl⟩ := e.surjective i
      rcases j with j | j
      · exact (min_le_left _ _).trans ((h₀ x).1 j)
      · exact (min_le_right _ _).trans ((h₁ x).1 j)
    · by_cases hc : (q₀.eval x).ofLp 0 ≤ (q₁.eval x).ofLp 0
      · obtain ⟨i, hi⟩ := (h₀ x).2
        exact ⟨e (Sum.inl i), (min_eq_left hc).trans hi⟩
      · obtain ⟨i, hi⟩ := (h₁ x).2
        exact ⟨e (Sum.inr i), (min_eq_right (le_of_not_ge hc)).trans hi⟩


/-- Given [a family size n](hyp:n), [an input dimension k](hyp:k),
[with n positive](hyp:hn), [n coefficient vectors](hyp:A), and [n intercepts](hyp:b),
[there exists a scalar-output ReLU network that returns the minimum of the n
affine functions at every input, using the ceiling of the base-two logarithm of n
hidden layers and width at most three times two raised to that ceiling](goal). -/
-- @node: relu_affine_finite_min
lemma relu_affine_finite_min (n k : ℕ) (hn : 0 < n)
    (A : Fin n → Fin k → ℝ) (b : Fin n → ℝ) :
    ∃ Q : ReLUNet k 1 (3 * 2 ^ (Nat.clog 2 n)) (Nat.clog 2 n), ∀ x,
      (∀ i, (Q.eval x).ofLp 0 ≤ (∑ j, A i j * x.ofLp j) + b i) ∧
      ∃ i, (Q.eval x).ofLp 0 = (∑ j, A i j * x.ofLp j) + b i := by
  classical
  let p : Fin (2 ^ (Nat.clog 2 n)) → Fin n :=
    fun i => if hi : i.val < n then ⟨i.val, hi⟩ else ⟨0, hn⟩
  have hp : Function.Surjective p := by
    intro i
    refine ⟨⟨i.val, i.isLt.trans_le (Nat.le_pow_clog (by omega) n)⟩, ?_⟩
    simp [p, i.isLt]
  obtain ⟨Q, hQ⟩ := relu_affine_min_tree (Nat.clog 2 n) k (A ∘ p) (b ∘ p)
  refine ⟨Q, ?_⟩
  intro x
  refine ⟨?_, ?_⟩
  · intro i
    obtain ⟨j, rfl⟩ := hp i
    exact (hQ x).1 j
  · obtain ⟨j, hj⟩ := (hQ x).2
    exact ⟨p j, hj⟩

/-- [There exists a scalar-input, scalar-output ReLU network with width at most
one and one hidden layer that returns the larger of zero and its input](goal). -/
-- @node: relu_positive_part
lemma relu_positive_part :
    ∃ Q : ReLUNet 1 1 1 1, ∀ x, (Q.eval x).ofLp 0 = max 0 (x.ofLp 0) := by
  let l : AffineLayer := ⟨1, 1, fun _ _ => 1, fun _ => 0⟩
  refine ⟨prependNet l rfl le_rfl (affineNet (fun _ _ => 1) (fun _ => 0)), ?_⟩
  intro x
  erw [prependNet_eval, affineNet_eval]
  change (∑ i : Fin 1, 1 * (layerVector l x).ofLp i) + 0 = _
  simp only [Fin.sum_univ_one, one_mul, add_zero]
  erw [layerVector_apply]
  simp [l, AffineLayer.input]

/-- For [an input dimension d](hyp:d), [there exists a coefficient vector for
each pair of augmented coordinate indices such that the corresponding structural
hat term equals its coefficient-weighted input sum plus one at every input](goal). -/
-- @node: structuralHatTerm_affine
lemma structuralHatTerm_affine (d : ℕ) :
    ∃ A : (Fin (d+1) × Fin (d+1)) → Fin d → ℝ,
      ∀ ab (x : L1Vec d), structuralHatTerm x.ofLp ab =
        (∑ j, A ab j * x.ofLp j) + 1 := by
  classical
  let w : Fin (d+1) → Fin d → ℝ :=
    Fin.cases (fun _ => 0) (fun i j => if j = i then 1 else 0)
  have hw (a : Fin (d+1)) (x : L1Vec d) :
      (∑ j, w a j * x.ofLp j) = Fin.cons (α := fun _ => ℝ) 0 x.ofLp a := by
    refine Fin.cases ?_ (fun i => ?_) a
    · simp [w]
    · simp [w]
  refine ⟨fun ab j => w ab.1 j - w ab.2 j, ?_⟩
  intro ab x
  simp only [sub_mul, Finset.sum_sub_distrib, hw, structuralHatTerm]
  ring

/-- For [an input dimension d](hyp:d), [the structural nodal hat is realized
exactly at every input by a scalar-output ReLU network with hidden depth equal
to the ceiling of the base-two logarithm of the square of the sum of d and one, followed
by one additional layer, and width at most three times two raised to that
ceiling](goal). -/
-- @node: structuralNodalHat_network
lemma structuralNodalHat_network (d : ℕ) :
    ∃ Q : ReLUNet d 1 (3 * 2 ^ (Nat.clog 2 ((d+1)*(d+1))))
        (Nat.clog 2 ((d+1)*(d+1)) + 1),
      ∀ x, (Q.eval x).ofLp 0 = structuralNodalHat x.ofLp := by
  classical
  let e : Fin (d+1) × Fin (d+1) ≃ Fin ((d+1)*(d+1)) := finProdFinEquiv
  obtain ⟨A, hA⟩ := structuralHatTerm_affine d
  obtain ⟨q, hq⟩ := relu_affine_finite_min ((d+1)*(d+1)) d (by positivity)
    (fun i => A (e.symm i)) (fun _ => 1)
  have hm (x : L1Vec d) : (q.eval x).ofLp 0 =
      Finset.univ.inf' Finset.univ_nonempty (structuralHatTerm x.ofLp) := by
    apply le_antisymm
    · apply Finset.le_inf'
      intro ab _
      simpa only [e.symm_apply_apply, ← hA] using (hq x).1 (e ab)
    · obtain ⟨i, hi⟩ := (hq x).2
      rw [hi, ← hA]
      exact Finset.inf'_le _ (Finset.mem_univ (e.symm i))
  obtain ⟨r, hr⟩ := relu_positive_part
  obtain ⟨Q, hQ⟩ := relu_comp_constructed q r
  have hw : max (3 * 2 ^ (Nat.clog 2 ((d+1)*(d+1)))) 1 ≤
      3 * 2 ^ (Nat.clog 2 ((d+1)*(d+1))) := by
    have hp : 0 < 2 ^ (Nat.clog 2 ((d+1)*(d+1))) := by positivity
    omega
  refine ⟨Q.widen hw, ?_⟩
  intro x
  rw [ReLUNet.widen_eval, hQ, Function.comp_apply, hr, hm]
  rfl


/-- For [a leaf count n](hyp:n) [that is positive](hyp:hn), [the smallest power
of two at least as large as n is at most twice n](goal). -/
-- @node: structural_min_tree_width
lemma structural_min_tree_width (n : ℕ) (hn : 0 < n) :
    2 ^ (Nat.clog 2 n) ≤ 2*n := by
  by_cases h : n = 1
  · subst n; norm_num
  · have hn' : 1 < n := by omega
    have hc : 0 < Nat.clog 2 n := Nat.clog_pos (by omega) hn'
    have hp := Nat.pow_pred_clog_lt_self (by omega : 1 < 2) hn'
    simp only [Nat.pred_eq_sub_one] at hp
    rw [show Nat.clog 2 n = (Nat.clog 2 n - 1) + 1 by omega, pow_succ]
    omega

/-- For [an input dimension d](hyp:d), [the structural nodal hat is realized
exactly at every input by a scalar-output ReLU network with width at most six
times the square of the sum of d and one and hidden depth equal to the ceiling of the
base-two logarithm of that square plus one additional layer](goal). -/
-- @node: structuralNodalHat_network_quadratic
lemma structuralNodalHat_network_quadratic (d : ℕ) :
    ∃ Q : ReLUNet d 1 (6*((d+1)*(d+1)))
        (Nat.clog 2 ((d+1)*(d+1)) + 1),
      ∀ x, (Q.eval x).ofLp 0 = structuralNodalHat x.ofLp := by
  obtain ⟨Q, hQ⟩ := structuralNodalHat_network d
  have hw := structural_min_tree_width ((d+1)*(d+1)) (by positivity)
  exact ⟨Q.widen (by omega), hQ⟩

/-- For [an input dimension d](hyp:d), [the ceiling of the base-two logarithm
of the square of the sum of d and one, plus one additional layer, is at most twice
the ceiling of the base-two logarithm of the sum of d and one, plus one additional
layer](goal). -/
-- @node: structuralNodalHat_depth_bound
lemma structuralNodalHat_depth_bound (d : ℕ) :
    Nat.clog 2 ((d+1)*(d+1)) + 1 ≤ 2 * Nat.clog 2 (d+1) + 1 := by
  have hp := Nat.le_pow_clog (by omega : 1 < 2) (d+1)
  suffices h : Nat.clog 2 ((d+1)*(d+1)) ≤ 2 * Nat.clog 2 (d+1) by omega
  apply Nat.clog_le_of_le_pow
  calc
    (d+1)*(d+1) ≤ (2 ^ Nat.clog 2 (d+1)) * (2 ^ Nat.clog 2 (d+1)) :=
      Nat.mul_le_mul hp hp
    _ = 2 ^ (2 * Nat.clog 2 (d+1)) := by rw [two_mul, pow_add]

/-- Given [a ReLU network](hyp:q), [coefficients for an affine transformation
of its outputs](hyp:A), and [the transformation's intercepts](hyp:b), [there exists
a ReLU network with the same hidden width budget and depth whose output at every
input is that affine transformation of the original network's output](goal). -/
-- @node: relu_affine_postcomp
lemma relu_affine_postcomp {k a o W L : ℕ} (q : ReLUNet k a W L)
    (A : Fin o → Fin a → ℝ) (b : Fin o → ℝ) :
    ∃ Q : ReLUNet k o W L, ∀ x j,
      (Q.eval x).ofLp j = (∑ i, A j i * (q.eval x).ofLp i) + b j := by
  have hcomp := relu_comp_constructed q (affineNet (W := W) A b)
  simp only [Nat.add_zero] at hcomp
  obtain ⟨Q, hQ⟩ := hcomp
  refine ⟨Q.widen (le_of_eq (Nat.max_self W)), ?_⟩
  intro x j
  rw [ReLUNet.widen_eval, hQ, Function.comp_apply, affineNet_eval]

/-- Given [an input dimension d](hyp:d), [a center v](hyp:v), and [a real scale
h](hyp:h), [there exists a scalar-output ReLU network that evaluates the structural
nodal hat after subtracting v from the input and dividing each coordinate by h,
with width at most six times the square of the sum of d and one and hidden depth equal to
the ceiling of the base-two logarithm of that square plus one additional layer](goal). -/
-- @node: structuralNodalHat_scaled_network
lemma structuralNodalHat_scaled_network (d : ℕ) (v : L1Vec d) (h : ℝ) :
    ∃ Q : ReLUNet d 1 (6*((d+1)*(d+1)))
        (Nat.clog 2 ((d+1)*(d+1)) + 1),
      ∀ x, (Q.eval x).ofLp 0 =
        structuralNodalHat (fun j => (x.ofLp j - v.ofLp j)/h) := by
  obtain ⟨q, hq⟩ := structuralNodalHat_network_quadratic d
  obtain ⟨Q, hQ⟩ := relu_affine_precomp q (diagonalWeight d (1/h))
    (fun j => -v.ofLp j/h)
  refine ⟨Q, ?_⟩
  intro x
  rw [hQ, hq]
  congr 1
  funext j
  simp only [diagonalWeight_sum]
  ring

/-- Given [an input dimension d](hyp:d), [an output dimension k](hyp:k),
[a number m of nodes](hyp:m), [their centers](hyp:v), [their output vectors](hyp:values),
and [a common real scale h](hyp:h), [there exists a ReLU network whose output is
the sum of the output vectors weighted by structural nodal hats centered at the
nodes and scaled by h, with width at most m times six times the square of the sum
of d and one and hidden depth equal to the ceiling of the base-two logarithm of that square
plus one additional layer](goal). -/
-- @node: structuralNodalSum_network
lemma structuralNodalSum_network (d k m : ℕ) (v : Fin m → L1Vec d)
    (values : Fin m → L1Vec k) (h : ℝ) :
    ∃ Q : ReLUNet d k (m * (6*((d+1)*(d+1))))
        (Nat.clog 2 ((d+1)*(d+1)) + 1),
      ∀ x, Q.eval x =
        ∑ i, structuralNodalHat (fun j => (x.ofLp j - (v i).ofLp j)/h) • values i := by
  classical
  choose q hq using fun i => structuralNodalHat_scaled_network d (v i) h
  obtain ⟨P, hP⟩ := relu_parallel_stack_constructed q
  obtain ⟨Q, hQ⟩ := relu_affine_postcomp P (fun j i => (values i).ofLp j) (fun _ => 0)
  refine ⟨Q, ?_⟩
  intro x
  apply PiLp.ext
  intro j
  rw [hQ]
  simp [hP, hq, mul_comm]


/-- Given [a finite set of integer grid points](hyp:s) and [a vector-valued
function to interpolate](hyp:f), [the structural grid interpolant is realized
exactly by a ReLU network with width at most the number of grid points times six
times the square of the sum of the input dimension and one, and hidden depth equal to the
ceiling of the base-two logarithm of that square plus one additional layer](goal). -/
-- @node: structuralGridInterpolant_network
lemma structuralGridInterpolant_network {d k : ℕ} (s : Finset (Fin d → ℤ))
    (f : L1Vec d → L1Vec k) :
    ∃ Q : ReLUNet d k (s.card * (6*((d+1)*(d+1))))
        (Nat.clog 2 ((d+1)*(d+1)) + 1),
      Q.eval = structuralGridInterpolant s f := by
  classical
  let e : Fin s.card ≃ s := s.equivFin.symm
  obtain ⟨Q, hQ⟩ := structuralNodalSum_network d k s.card
    (fun i => structuralGridPoint (e i).val)
    (fun i => f (structuralGridPoint (e i).val)) 1
  refine ⟨Q, ?_⟩
  funext x
  rw [hQ]
  trans ∑ w : s, structuralNodalHat (fun j => x.ofLp j - (w.val j : ℝ)) •
    f (structuralGridPoint w.val)
  · apply Fintype.sum_equiv e
    intro i
    simp [structuralGridPoint]
  · exact Finset.sum_coe_sort s
      (fun w => structuralNodalHat (fun j => x.ofLp j - (w j : ℝ)) •
        f (structuralGridPoint w))

/-- Given [a finite set of integer grid points](hyp:s), [a vector-valued function
to interpolate](hyp:f), [a lower clipping endpoint a](hyp:a), and [an upper clipping
endpoint b](hyp:b), [with a no greater than b](hyp:hab), [there exists a ReLU network
that evaluates the structural grid interpolant after clipping every input coordinate
to the interval from a to b; its width is at most the larger of the input dimension
and the number of grid points times six times the square of the sum of the input
dimension and one, and its hidden depth is the ceiling of the base-two logarithm of that
square plus three](goal). -/
-- @node: structuralGridInterpolant_clamped_network
lemma structuralGridInterpolant_clamped_network {d k : ℕ}
    (s : Finset (Fin d → ℤ)) (f : L1Vec d → L1Vec k)
    (a b : ℝ) (hab : a ≤ b) :
    ∃ Q : ReLUNet d k (max (s.card * (6*((d+1)*(d+1)))) d)
        (Nat.clog 2 ((d+1)*(d+1)) + 1 + 2),
      Q.eval = structuralGridInterpolant s f ∘ coordinateClamp a b := by
  obtain ⟨q, hq⟩ := structuralGridInterpolant_network s f
  obtain ⟨Q, hQ⟩ := relu_clamped_input q a b hab
  exact ⟨Q, by rw [hQ, hq]⟩

end
end Papers.TbsNeuralCausalPi
