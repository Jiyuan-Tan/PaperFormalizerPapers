module
public import Papers.TbsNeuralCausalPi.Helpers.NetworkClipping
public import Papers.TbsNeuralCausalPi.Helpers.CanonicalNormalization
/-! # Positive floors and categorical approximation error

The floor is implemented with one additional hidden layer. Its uniform error
survives normalization, including when the target has zero coordinates.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.whitespace false
open scoped NNReal ENNReal
noncomputable section

-- @node: structuralPositiveFloor
/-- For [a real floor level ε](hyp:eps) and [a real vector x](hyp:x), the
[floored vector](goal) replaces each coordinate of x by its maximum with ε. -/
def structuralPositiveFloor {d : ℕ} (eps : ℝ) (x : L1Vec d) : L1Vec d :=
  WithLp.toLp 1 (fun j => max eps (x.ofLp j))

-- @node: structuralPositiveFloor_measurable
/-- For [any real floor level ε](hyp:eps), [the map that replaces every vector
coordinate by its maximum with ε is measurable](goal). -/
@[fun_prop] lemma structuralPositiveFloor_measurable {d : ℕ} (eps : ℝ) :
    Measurable (structuralPositiveFloor (d := d) eps) := by
  unfold structuralPositiveFloor
  fun_prop

-- @node: structuralPositiveFloor_coordinate_error
/-- If [the target p is nonnegative](hyp:hp), then [the absolute error of
max{ε, z} relative to p is at most the maximum of ε and the absolute error
of z relative to p](goal). -/
lemma structuralPositiveFloor_coordinate_error {eps z p : ℝ}
    (hp : 0 ≤ p) : |max eps z - p| ≤ max eps |z-p| := by
  by_cases hz : eps ≤ z
  · rw [max_eq_right hz]
    exact le_max_right _ _
  · rw [max_eq_left (le_of_not_ge hz)]
    by_cases hp' : p ≤ eps
    · rw [abs_of_nonneg (sub_nonneg.mpr hp')]
      exact (sub_le_self _ hp).trans (le_max_left _ _)
    · rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge hp'))]
      calc
        -(eps-p) ≤ p-z := by linarith
        _ ≤ |z-p| := by rw [abs_sub_comm]; exact le_abs_self _
        _ ≤ _ := le_max_right _ _

-- @node: structuralPositiveFloor_error_le
/-- If [every target coordinate is nonnegative](hyp:hp) and [every coordinate
of z differs from its target by at most ε](hyp:hz), then [replacing each
coordinate of z by its maximum with ε keeps every coordinate error at most
ε](goal). -/
lemma structuralPositiveFloor_error_le {d : ℕ} {eps : ℝ} {p z : L1Vec d}
    (hp : ∀ j, 0 ≤ p.ofLp j) (hz : ∀ j, |z.ofLp j-p.ofLp j| ≤ eps) :
    ∀ j, |(structuralPositiveFloor eps z).ofLp j-p.ofLp j| ≤ eps := by
  intro j
  exact (structuralPositiveFloor_coordinate_error (hp j)).trans
    (max_le le_rfl (hz j))

-- @node: structural_mass_error_le
/-- If [p is a probability vector with d coordinates](hyp:hp) and [each
coordinate of q differs from p by at most ε](hyp:hq), then [the absolute
difference between the sum of q's coordinates and one is at most dε](goal). -/
lemma structural_mass_error_le {d : ℕ} {eps : ℝ} {p q : Fin d → ℝ}
    (hp : p ∈ probabilitySimplex d) (hq : ∀ j, |q j-p j| ≤ eps) :
    |(∑ j, q j)-1| ≤ d * eps := by
  calc
    _ = |∑ j, (q j-p j)| := by rw [Finset.sum_sub_distrib, hp.2]
    _ ≤ ∑ j, |q j-p j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin d, eps := Finset.sum_le_sum (fun j _ => hq j)
    _ = _ := by simp [mul_comm]

-- @node: structural_mass_ge_half
/-- If [p is a probability vector with d coordinates](hyp:hp), [each
coordinate of q differs from p by at most ε](hyp:hq), and [dε is at most
one half](hyp:hsmall), then [the sum of q's coordinates is at least one
half](goal). -/
lemma structural_mass_ge_half {d : ℕ} {eps : ℝ} {p q : Fin d → ℝ}
    (hp : p ∈ probabilitySimplex d) (hq : ∀ j, |q j-p j| ≤ eps)
    (hsmall : (d : ℝ) * eps ≤ 1/2) :
    1/2 ≤ ∑ j, q j := by
  have hmass := (abs_le.mp (structural_mass_error_le hp hq)).1
  linarith

-- @node: structural_normalized_coordinate_error_le
/-- If [ε is nonnegative](hyp:heps), [p is a probability vector with d
coordinates](hyp:hp), [each coordinate of q differs from p by at most
ε](hyp:hq), and [dε is at most one half](hyp:hsmall), then at [any coordinate
j](hyp:j), [dividing q by the sum of its coordinates gives an absolute error
relative to p of at most 2(d + 1)ε](goal). -/
lemma structural_normalized_coordinate_error_le {d : ℕ} {eps : ℝ}
    {p q : Fin d → ℝ} (heps : 0 ≤ eps)
    (hp : p ∈ probabilitySimplex d) (hq : ∀ j, |q j-p j| ≤ eps)
    (hsmall : (d : ℝ) * eps ≤ 1/2) (j : Fin d) :
    |q j / (∑ l, q l)-p j| ≤ 2 * (d+1) * eps := by
  let a := ∑ l, q l
  have ha : 1/2 ≤ a := structural_mass_ge_half hp hq hsmall
  have ha0 : 0 < a := by linarith
  have hpj : |p j| ≤ 1 := by
    rw [abs_of_nonneg (hp.1 j)]
    exact (Finset.single_le_sum (fun l _ => hp.1 l) (Finset.mem_univ j)).trans_eq hp.2
  have hmass : |1-a| ≤ d * eps := by
    rw [abs_sub_comm]
    exact structural_mass_error_le hp hq
  have hid : q j/a-p j = ((q j-p j) + (1-a)*p j)/a := by
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos ha0]
  apply (div_le_iff₀ ha0).mpr
  calc
    |(q j-p j)+(1-a)*p j| ≤ |q j-p j| + |(1-a)*p j| := abs_add_le _ _
    _ ≤ eps + (d : ℝ) * eps * 1 := by
      rw [abs_mul]
      exact add_le_add (hq j) (mul_le_mul hmass hpj (abs_nonneg _) (by positivity))
    _ ≤ 2 * (d+1) * eps * a := by
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ d+1) heps]

-- @node: structuralPositiveFloor_mass_pos
/-- If [the dimension d is positive](hyp:hd) and [the floor ε is strictly
positive](hyp:heps), then for [any real vector z](hyp:z), [flooring every
coordinate at ε gives nonnegative coordinates and a strictly positive sum](goal). -/
lemma structuralPositiveFloor_mass_pos {d : ℕ} (hd : 0 < d) {eps : ℝ}
    (heps : 0 < eps) (z : L1Vec d) :
    (∀ j, 0 ≤ (structuralPositiveFloor eps z).ofLp j) ∧
      0 < ∑ j, (structuralPositiveFloor eps z).ofLp j := by
  have hpos (j : Fin d) : 0 < (structuralPositiveFloor eps z).ofLp j :=
    heps.trans_le (le_max_left _ _)
  refine ⟨fun j => (hpos j).le, ?_⟩
  exact Finset.sum_pos (fun j _ => hpos j) ⟨⟨0, hd⟩, Finset.mem_univ _⟩

-- @node: relu_affine_structuralPositiveFloor
/-- For [an affine map's coefficient matrix A](hyp:A), [its intercept vector
v](hyp:v), and [a real floor ε](hyp:eps), [there is a ReLU network with one
hidden layer and width d whose output at every input is the coordinatewise
maximum of ε and the affine map's output](goal). -/
lemma relu_affine_structuralPositiveFloor {k d : ℕ}
    (A : Fin d → Fin k → ℝ) (v : Fin d → ℝ) (eps : ℝ) :
    ∃ Q : ReLUNet k d d 1, ∀ x j,
      (Q.eval x).ofLp j = max eps ((∑ i, A j i * x.ofLp i) + v j) := by
  classical
  let l : AffineLayer := ⟨k, d, A, fun j => v j-eps⟩
  let out : ReLUNet d d d 0 := affineNet (diagonalWeight d 1) (fun _ => eps)
  refine ⟨prependNet l rfl le_rfl out, ?_⟩
  intro x j
  erw [prependNet_eval]
  erw [show out = affineNet (diagonalWeight d 1) (fun _ => eps) from rfl,
    affineNet_eval, diagonalWeight_sum, layerVector_apply]
  change 1 * max 0 ((∑ i : Fin k, A j i *
    (if h : i.val < k then x.ofLp ⟨i.val, h⟩ else 0)) + (v j-eps)) + eps = _
  simp only [one_mul, dif_pos (Fin.isLt _)]
  by_cases h : eps ≤ (∑ i, A j i * x.ofLp i) + v j
  · rw [max_eq_right (by linarith), max_eq_right h]
    ring
  · rw [max_eq_left (by linarith), max_eq_left (le_of_not_ge h), zero_add]

-- @node: relu_structuralPositiveFloor
/-- For [a ReLU network q with input dimension k, output dimension d, width W,
and L hidden layers](hyp:q) and [a real floor ε](hyp:eps), [there is a ReLU
network with width max{W, d} and L + 1 hidden layers that evaluates q and
then floors each output coordinate at ε](goal). -/
lemma relu_structuralPositiveFloor {k d W L : ℕ} (q : ReLUNet k d W L)
    (eps : ℝ) :
    ∃ Q : ReLUNet k d (max W d) (L+1),
      Q.eval = structuralPositiveFloor eps ∘ q.eval := by
  classical
  induction L generalizing k with
  | zero =>
    rcases q with ⟨ls, hd, hw, hf, hc, ow, ob⟩
    have hs : ls = [] := List.length_eq_zero_iff.mp hd
    subst ls
    obtain ⟨Q, hQ⟩ := relu_affine_structuralPositiveFloor ow ob eps
    refine ⟨Q.widen (le_max_right W d), ?_⟩
    funext x
    apply PiLp.ext
    intro j
    erw [ReLUNet.widen_eval, hQ]
    change max eps _ = max eps _
    congr 2
    change (∑ i : Fin k, ow j i * x.ofLp i) =
      (∑ i : Fin k, ow j i * (if h : i.val < k then x.ofLp ⟨i.val, h⟩ else 0))
    simp only [dif_pos (Fin.isLt _)]
  | succ L ih =>
    obtain ⟨l, hl, hw, r, hq⟩ := exists_relu_head q
    obtain ⟨R, hR⟩ := ih r
    refine ⟨prependNet l hl (hw.trans (le_max_left W d)) R, ?_⟩
    funext x
    rw [prependNet_eval, hR, hq]
    dsimp only [Function.comp_apply]
    rw [prependNet_eval]

-- @node: relu_structuralPositiveFloor_approximation
/-- For [a ReLU network q of width W and depth L](hyp:q), suppose [ε is
strictly positive](hyp:heps), [the output dimension d is positive](hyp:hd),
[the target p is probability-valued on S](hyp:hp), [q approximates every
coordinate of p on S within ε](hyp:herr), and [dε is at most one half](hyp:hsmall).
Then [there is a network of width max{W, d} and depth L + 1 that floors q
at ε, has nonnegative outputs with positive total mass everywhere, and whose
outputs divided by their total mass are probability vectors everywhere and
approximate each coordinate of p on S within 2(d + 1)ε](goal).

The target may lie on any face of the closed simplex. -/
lemma relu_structuralPositiveFloor_approximation {k d W L : ℕ}
    (q : ReLUNet k d W L) {S : Set (L1Vec k)} {p : L1Vec k → L1Vec d}
    {eps : ℝ} (heps : 0 < eps) (hd : 0 < d)
    (hp : ∀ x ∈ S, (p x).ofLp ∈ probabilitySimplex d)
    (herr : ∀ x ∈ S, ∀ j, |(q.eval x).ofLp j-(p x).ofLp j| ≤ eps)
    (hsmall : (d : ℝ) * eps ≤ 1/2) :
    ∃ Q : ReLUNet k d (max W d) (L+1),
      Q.eval = structuralPositiveFloor eps ∘ q.eval ∧
      (∀ x, (∀ j, 0 ≤ (Q.eval x).ofLp j) ∧ 0 < ∑ j, (Q.eval x).ofLp j) ∧
      (∀ x, (fun j => (Q.eval x).ofLp j / ∑ l, (Q.eval x).ofLp l) ∈ probabilitySimplex d) ∧
      ∀ x ∈ S, ∀ j,
        |(Q.eval x).ofLp j / (∑ l, (Q.eval x).ofLp l)-(p x).ofLp j| ≤
          2 * (d+1) * eps := by
  obtain ⟨Q, hQ⟩ := relu_structuralPositiveFloor q eps
  have hmass (x : L1Vec k) :
      (∀ j, 0 ≤ (Q.eval x).ofLp j) ∧ 0 < ∑ j, (Q.eval x).ofLp j := by
    rw [hQ]
    exact structuralPositiveFloor_mass_pos hd heps (q.eval x)
  refine ⟨Q, hQ, hmass, ?_, ?_⟩
  · intro x
    exact canonical_normalized_mem_simplex _ (hmass x).1 (hmass x).2
  · intro x hx j
    apply structural_normalized_coordinate_error_le heps.le (hp x hx) _ hsmall j
    rw [hQ]
    exact structuralPositiveFloor_error_le (hp x hx).1 (herr x hx)

-- @node: structural_normalized_supDistOn_le
/-- If [ε is nonnegative](hyp:heps), [p is probability-valued on S](hyp:hp),
[every coordinate of q differs from p on S by at most ε](hyp:herr), and
[dε is at most one half](hyp:hsmall), then [the uniform distance on S between
p and q divided by its coordinate sum is at most 2(d + 1)ε](goal). -/
lemma structural_normalized_supDistOn_le {X : Type*} {d : ℕ}
    {S : Set X} {p q : X → L1Vec d} {eps : ℝ} (heps : 0 ≤ eps)
    (hp : ∀ x ∈ S, (p x).ofLp ∈ probabilitySimplex d)
    (herr : ∀ x ∈ S, ∀ j, |(q x).ofLp j-(p x).ofLp j| ≤ eps)
    (hsmall : (d : ℝ) * eps ≤ 1/2) :
    supDistOn S p (fun x => WithLp.toLp 1
      (fun j => (q x).ofLp j / ∑ l, (q x).ofLp l)) ≤
        ENNReal.ofReal (2 * (d+1) * eps) := by
  apply iSup_le
  intro x
  apply ENNReal.ofReal_le_ofReal
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro j
  simpa only [PiLp.sub_apply, WithLp.ofLp_toLp, Real.norm_eq_abs, abs_sub_comm] using
    structural_normalized_coordinate_error_le heps (hp x x.property)
      (herr x x.property) hsmall j

-- @node: structural_normalized_simplex_eq_self
/-- If [p is a probability vector](hyp:hp), then [dividing each coordinate
by the sum of its coordinates leaves p unchanged](goal), including when
some coordinates are zero. -/
lemma structural_normalized_simplex_eq_self {d : ℕ} {p : L1Vec d}
    (hp : p.ofLp ∈ probabilitySimplex d) :
    WithLp.toLp 1 (fun j => p.ofLp j / ∑ l, p.ofLp l) = p := by
  apply PiLp.ext
  intro j
  simp only [WithLp.ofLp_toLp, hp.2, div_one]

end
end Papers.TbsNeuralCausalPi
