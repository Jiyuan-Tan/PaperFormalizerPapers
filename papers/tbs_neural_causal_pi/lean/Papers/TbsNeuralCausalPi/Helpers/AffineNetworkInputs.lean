module
public import Papers.TbsNeuralCausalPi.Helpers.NetworkClipping
public import Papers.TbsNeuralCausalPi.Helpers.StructuralGateCompatibility
/-! # Affine changes and clipped inputs for concrete ReLU networks -/
public section
namespace Papers.TbsNeuralCausalPi
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- [Precomposing a ReLU network with any affine transformation of its inputs can be represented by another ReLU network with the same output dimension, width bound, and depth](goal). -/
-- @node: relu_affine_precomp
lemma relu_affine_precomp {a k o W L : ℕ} (q : ReLUNet a o W L)
    (A : Fin a → Fin k → ℝ) (b : Fin a → ℝ) :
    ∃ Q : ReLUNet k o W L, ∀ x,
      Q.eval x = q.eval (WithLp.toLp 1 (fun j => (∑ i, A j i * x.ofLp i) + b j)) := by
  classical
  cases L with
  | zero =>
    rcases q with ⟨ls, hd, hw, hf, hc, ow, ob⟩
    have hs : ls = [] := List.length_eq_zero_iff.mp hd
    subst ls
    refine ⟨affineNet (fun j i => ∑ u, ow j u * A u i)
      (fun j => (∑ u, ow j u * b u) + ob j), ?_⟩
    intro x
    apply PiLp.ext
    intro j
    rw [affineNet_eval]
    change _ = (∑ u : Fin a, ow j u *
      (if h : u.val < a then ((∑ i, A ⟨u.val,h⟩ i * x.ofLp i) + b ⟨u.val,h⟩) else 0)) + ob j
    simp only [dif_pos (Fin.isLt _), mul_add, Finset.sum_add_distrib,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [Fin.eta, mul_assoc]
    simp only [finalWidth, List.getLast?, Option.map, Option.getD]
    ring
  | succ L =>
    obtain ⟨l, hl, hw, r, rfl⟩ := exists_relu_head q
    let l' : AffineLayer := ⟨k, l.output,
      (fun j i => ∑ u : Fin l.input, l.2.2.1 j u * A (Fin.cast hl u) i),
      (fun j => (∑ u : Fin l.input, l.2.2.1 j u * b (Fin.cast hl u)) + l.2.2.2 j)⟩
    refine ⟨prependNet l' rfl hw r, ?_⟩
    intro x
    erw [prependNet_eval, prependNet_eval]
    congr 1
    apply PiLp.ext
    intro j
    erw [layerVector_apply, layerVector_apply]
    change max 0 _ = max 0 _
    congr 1
    simp only [l', AffineLayer.input, AffineLayer.output, dif_pos (Fin.isLt _)]
    simp only [show ∀ u : Fin l.input, u.val < a from fun u => hl ▸ u.isLt,
      dite_true, WithLp.ofLp_toLp]
    change (∑ i : Fin k, (∑ u : Fin l.input,
      l.2.2.1 j u * A (Fin.cast hl u) i) * x.ofLp i) +
      ((∑ u : Fin l.input, l.2.2.1 j u * b (Fin.cast hl u)) + l.2.2.2 j) =
      (∑ u : Fin l.input, l.2.2.1 j u *
        ((∑ i : Fin k, A (Fin.cast hl u) i * x.ofLp i) + b (Fin.cast hl u))) + l.2.2.2 j
    simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_assoc]
    ring

/-- If [the lower clipping endpoint does not exceed the upper endpoint](hyp:hab),
[applying a ReLU network after clipping each input coordinate to that interval can be represented by a ReLU network with two additional layers and width bounded by the larger of the original width bound and the input dimension](goal). -/
-- @node: relu_clamped_input
lemma relu_clamped_input {k o W L : ℕ} (q : ReLUNet k o W L)
    (a b : ℝ) (hab : a ≤ b) :
    ∃ Q : ReLUNet k o (max W k) (L+2),
      Q.eval = q.eval ∘ coordinateClamp a b := by
  obtain ⟨r, hr⟩ := relu_affine_precomp (q.widen (le_max_left W k))
    (diagonalWeight k (-1)) (fun _ => b)
  let second : AffineLayer := ⟨k, k, diagonalWeight k (-1), fun _ => b-a⟩
  let first : AffineLayer := ⟨k, k, diagonalWeight k 1, fun _ => -a⟩
  refine ⟨prependNet first rfl (le_max_right W k)
    (prependNet second rfl (le_max_right W k) r), ?_⟩
  funext x
  erw [prependNet_eval, prependNet_eval, hr, ReLUNet.widen_eval]
  congr 1
  apply PiLp.ext
  intro j
  simp only [WithLp.ofLp_toLp, diagonalWeight_sum]
  erw [layerVector_apply]
  change -1 * max 0 ((∑ i : Fin k, diagonalWeight k (-1) j i *
    (if h : i.val < k then (layerVector first x).ofLp ⟨i.val,h⟩ else 0)) + (b-a)) + b = _
  simp only [dif_pos (Fin.isLt _), diagonalWeight_sum]
  erw [layerVector_apply]
  change -1 * max 0 (-1 * max 0 ((∑ i : Fin k, diagonalWeight k 1 j i *
    (if h : i.val < k then x.ofLp ⟨i.val,h⟩ else 0)) + -a) + (b-a)) + b = _
  simp only [dif_pos (Fin.isLt _), diagonalWeight_sum, one_mul]
  have h := coordinateClamp_relu_identity a b (x.ofLp j) hab
  change _ = max a (min (x.ofLp j) b)
  convert h using 1 <;> ring

open scoped NNReal

-- @node: box_affine_dist
/-- For [a nonnegative box radius B](hyp:B), [rescaling each coordinate by twice one plus B and then subtracting one plus B multiplies the L1 distance between any two vectors by exactly twice one plus B](goal). -/
lemma box_affine_dist {d : ℕ} (B : ℝ≥0) (x y : L1Vec d) :
    dist (WithLp.toLp 1 (fun j => 2*(B+1 : ℝ)*x.ofLp j-(B+1)))
      (WithLp.toLp 1 (fun j => 2*(B+1 : ℝ)*y.ofLp j-(B+1))) =
      2*(B+1 : ℝ)*dist x y := by
  simp only [PiLp.dist_eq_of_L1, WithLp.ofLp_toLp, Real.dist_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [show 2*(B+1 : ℝ)*x.ofLp j-(B+1) - (2*(B+1 : ℝ)*y.ofLp j-(B+1)) =
    2*(B+1 : ℝ)*(x.ofLp j-y.ofLp j) by ring, abs_mul, abs_of_nonneg (by positivity)]

/-- Assume [the structural Yarotsky approximation property](hyp:hgate) and
[a positive input dimension](hyp:hd). For [a nonnegative Lipschitz bound and box radius](hyp:L,B),
if [the scalar target function is Lipschitz with that bound in L1 distance](hyp:hg),
[there is a positive constant such that every depth budget of at least one admits a scalar ReLU network of width at most twice the dimension plus ten and depth equal to the budget plus two, whose error in approximating the target evaluated at the coordinatewise clipped input is globally bounded by that constant times the budget raised to minus two divided by the dimension](goal). -/
-- @node: yarotsky_scalar_clipped_box
lemma yarotsky_scalar_clipped_box (hgate : YarotskyStructuralApprox)
    {d : ℕ} (hd : 0 < d) (g : L1Vec d → ℝ) (L B : ℝ≥0)
    (hg : LipschitzWith L g) :
    ∃ A : ℝ, 0 < A ∧ ∀ depth : ℕ, 1 ≤ depth →
      ∃ q : ReLUNet d 1 (2*d+10) (depth+2), ∀ x,
        |g (coordinateClamp (-(B : ℝ)) B x)-(q.eval x).ofLp 0| ≤
          A * (depth : ℝ)^(-(2 : ℝ)/d) := by
  obtain ⟨a, c, ha, hc, happ⟩ := yarotskyStructural_scalar_lipschitz_modulus hgate d hd
  let F : L1Vec d → ℝ := fun x =>
    g (WithLp.toLp 1 (fun j => 2*(B+1 : ℝ)*x.ofLp j-(B+1)))
  have hF : LipschitzWith (L*(2*(B+1))) F := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    calc
      dist (F x) (F y) ≤ L * dist
          (WithLp.toLp 1 (fun j => 2*(B+1 : ℝ)*x.ofLp j-(B+1)))
          (WithLp.toLp 1 (fun j => 2*(B+1 : ℝ)*y.ofLp j-(B+1))) := hg.dist_le_mul _ _
      _ = _ := by rw [box_affine_dist]; simp only [NNReal.coe_mul, NNReal.coe_add,
          NNReal.coe_ofNat, NNReal.coe_one]; ring
  let A : ℝ := 1 + a*(L*(2*(B+1 : ℝ)))*d*c
  refine ⟨A, by dsimp [A]; positivity, ?_⟩
  intro depth hdepth
  obtain ⟨q, hq⟩ := happ F (L*(2*(B+1))) hF.lipschitzOnWith depth hdepth
  obtain ⟨r, hr⟩ := relu_affine_precomp q
    (diagonalWeight d (1/(2*(B+1 : ℝ)))) (fun _ => 1/2)
  obtain ⟨Q0, hQ0⟩ := relu_clamped_input r (-(B : ℝ)) B (by linarith [B.coe_nonneg])
  let Q : ReLUNet d 1 (2*d+10) (depth+2) := Q0.widen (max_le le_rfl (by omega))
  have hQ : Q.eval = r.eval ∘ coordinateClamp (-(B : ℝ)) B := hQ0
  refine ⟨Q, ?_⟩
  intro x
  let z := coordinateClamp (-(B : ℝ)) B x
  let y : L1Vec d := WithLp.toLp 1 (fun j => z.ofLp j/(2*(B+1 : ℝ))+1/2)
  have hy : y ∈ unitCube d := by
    intro j
    have hz := coordinateClamp_mapsTo (-(B : ℝ)) B (by linarith [B.coe_nonneg]) x j
    change 0 ≤ z.ofLp j/(2*(B+1 : ℝ))+1/2 ∧ z.ofLp j/(2*(B+1 : ℝ))+1/2 ≤ 1
    have hp : 0 < 2*(B+1 : ℝ) := by positivity
    constructor
    · have := (le_div_iff₀ hp).2 (show (-1/2 : ℝ)*(2*(B+1 : ℝ)) ≤ z.ofLp j by
        change _ ≤ (coordinateClamp (-(B : ℝ)) B x).ofLp j
        linarith [hz.1])
      linarith
    · have := (div_le_iff₀ hp).2 (show z.ofLp j ≤ (1/2 : ℝ)*(2*(B+1 : ℝ)) by
        change (coordinateClamp (-(B : ℝ)) B x).ofLp j ≤ _
        linarith [hz.2])
      linarith
  have hFy : F y = g z := by
    dsimp [F]
    congr 1
    apply PiLp.ext
    intro j
    change 2*(B+1 : ℝ)*(z.ofLp j/(2*(B+1 : ℝ))+1/2)-(B+1) = z.ofLp j
    field_simp
    <;> ring
  have heval : (Q.eval x).ofLp 0 = (q.eval y).ofLp 0 := by
    rw [hQ, Function.comp_apply, hr]
    apply congrArg (fun v => (q.eval v).ofLp 0)
    apply PiLp.ext
    intro j
    simp only [WithLp.ofLp_toLp, diagonalWeight_sum, y, z]
    ring
  rw [heval]
  have hmod := euclidModulus_le_of_lipschitzOn hF.lipschitzOnWith
    (r := c * (depth : ℝ)^(-(2 : ℝ)/d)) (by positivity)
  calc
    |g z - (q.eval y).ofLp 0| ≤ a * euclidModulus F
        (c * (depth : ℝ)^(-(2 : ℝ)/d)) := by simpa only [hFy] using hq y hy
    _ ≤ a * ((L*(2*(B+1 : ℝ)))*d*(c*(depth : ℝ)^(-(2 : ℝ)/d))) := by
      exact mul_le_mul_of_nonneg_left hmod ha.le
    _ ≤ A * (depth : ℝ)^(-(2 : ℝ)/d) := by
      dsimp [A]
      nlinarith [Real.rpow_nonneg (Nat.cast_nonneg depth) (-(2 : ℝ)/d)]

end
end Papers.TbsNeuralCausalPi
