module
public import Papers.TbsNeuralCausalPi.Setup.Networks
/-! # Mesh and width choices for the wide first block

These are the numerical steps in the corrected positive-dimensional construction.
The depth parameter of the cited construction stays fixed; its refinement index
is chosen from the width budget.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open scoped NNReal
noncomputable section

-- @node: wideQuantizationParameter
/-- For [dimension q](hyp:q) and [refinement index n](hyp:n) with [n at least two](hyp:_hn),
the [wide quantization mesh](goal) is the reciprocal of the natural-number ceiling of
$\sqrt q(q+1)n(n-1)$. -/
def wideQuantizationParameter (q n : ℕ) (_hn : 2 ≤ n) : ℝ :=
  (⌈Real.sqrt q * (q + 1) * n * ((n : ℝ) - 1)⌉₊ : ℝ)⁻¹

-- @node: wide_mesh_dimension_factor
/-- If [q is positive](hyp:hq), then [the dimension factor $\sqrt q(q+1)$ is at least two](goal). -/
lemma wide_mesh_dimension_factor {q : ℕ} (hq : 0 < q) :
    2 ≤ Real.sqrt q * (q + 1) := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hs : 1 ≤ Real.sqrt q := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg q), Real.sqrt_nonneg (q : ℝ)]
  nlinarith

-- @node: wideQuantizationParameter_bounds
/-- If [q is positive](hyp:hq) and [n is at least two](hyp:hn), then [the wide quantization
mesh is positive, is at most $1/(\sqrt q(q+1)n(n-1))$, and this upper bound is strictly
less than $1/(n(n-1))$](goal). -/
lemma wideQuantizationParameter_bounds {q n : ℕ} (hq : 0 < q) (hn : 2 ≤ n) :
    0 < wideQuantizationParameter q n hn ∧
      wideQuantizationParameter q n hn ≤
        1 / (Real.sqrt q * (q + 1) * n * ((n : ℝ) - 1)) ∧
      1 / (Real.sqrt q * (q + 1) * n * ((n : ℝ) - 1)) <
        1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hf := wide_mesh_dimension_factor hq
  have hn1 : 0 < (n : ℝ) - 1 := by linarith
  have hnpos : 0 < (n : ℝ) * ((n : ℝ) - 1) := by positivity
  have hden : 0 < Real.sqrt q * (q + 1) * n * ((n : ℝ) - 1) := by
    have : 0 < Real.sqrt q * (q + 1) := by linarith
    positivity
  have hceil := Nat.le_ceil (Real.sqrt q * (q + 1) * n * ((n : ℝ) - 1))
  refine ⟨inv_pos.mpr (hden.trans_le hceil), ?_, ?_⟩
  · simpa only [wideQuantizationParameter, one_div] using
      one_div_le_one_div_of_le hden hceil
  · apply one_div_lt_one_div_of_lt hnpos
    nlinarith [mul_le_mul_of_nonneg_right hf hnpos.le]

/-- If [q is positive](hyp:hq) and [n is at least two](hyp:hn), then [the sum of
$\sqrt q/(2n)$, $2\sqrt q/n$, and $q(q+1)(n-1)/2$ times the wide quantization mesh
is at most $3\sqrt q/n$](goal). -/
-- @node: wide_quantization_source_error
lemma wide_quantization_source_error {q n : ℕ} (hq : 0 < q) (hn : 2 ≤ n) :
    Real.sqrt q / (2 * n) + 2 * Real.sqrt q / n +
        (q : ℝ) * (q + 1) / 2 * (n - 1) * wideQuantizationParameter q n hn ≤
      3 * Real.sqrt q / n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.2 hqR
  have hn1 : 0 < (n : ℝ) - 1 := by linarith
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hnm : (n : ℝ) - 1 ≠ 0 := by linarith
  have hqm : (q : ℝ) + 1 ≠ 0 := by positivity
  have hterm := mul_le_mul_of_nonneg_left
    (wideQuantizationParameter_bounds hq hn).2.1
    (show 0 ≤ (q : ℝ) * (q + 1) / 2 * (n - 1) by positivity)
  have hid : (q : ℝ) * (q + 1) / 2 * (n - 1) *
      (1 / (Real.sqrt q * (q + 1) * n * ((n : ℝ) - 1))) =
      Real.sqrt q / (2 * n) := by
    field_simp
    nlinarith [Real.sq_sqrt hqR.le]
  rw [hid] at hterm
  calc
    _ ≤ Real.sqrt q / (2 * n) + 2 * Real.sqrt q / n +
        Real.sqrt q / (2 * n) := add_le_add le_rfl hterm
    _ = _ := by ring

/-- If [q is positive](hyp:hq) and [n is at least two](hyp:hn), then [multiplying
the sum of $\sqrt q/(2n)$, $2\sqrt q/n$, and $q(q+1)(n-1)/2$ times the wide
quantization mesh by $\sqrt q$ gives at most $3q/n$](goal). -/
-- @node: wide_quantization_oneNorm_error
lemma wide_quantization_oneNorm_error {q n : ℕ} (hq : 0 < q) (hn : 2 ≤ n) :
    Real.sqrt q * (Real.sqrt q / (2 * n) + 2 * Real.sqrt q / n +
        (q : ℝ) * (q + 1) / 2 * (n - 1) * wideQuantizationParameter q n hn) ≤
      3 * q / n := by
  calc
    _ ≤ Real.sqrt q * (3 * Real.sqrt q / n) :=
      mul_le_mul_of_nonneg_left (wide_quantization_source_error hq hn)
        (Real.sqrt_nonneg _)
    _ = 3 * (Real.sqrt q * Real.sqrt q) / n := by ring
    _ = _ := by rw [Real.mul_self_sqrt (Nat.cast_nonneg q)]

-- @node: wide_refinement_floor_bounds
/-- If [x is at least two](hyp:hx), then [its nonnegative integer floor is at least
two, at most x, and at least half of x](goal). -/
lemma wide_refinement_floor_bounds {x : ℝ} (hx : 2 ≤ x) :
    2 ≤ ⌊x⌋₊ ∧ (⌊x⌋₊ : ℝ) ≤ x ∧ x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have htwo : 2 ≤ ⌊x⌋₊ := (Nat.le_floor_iff (by linarith)).2 (by simpa using hx)
  have htwoR : (2 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast htwo
  refine ⟨htwo, Nat.floor_le (by linarith), ?_⟩
  linarith [Nat.lt_floor_add_one x]

/-- If [q is positive](hyp:hq), [A is positive](hyp:hA), and [the width budget W
is at least $A2^q$](hyp:hW), then [the integer floor n of $(W/A)^{1/q}$ is at
least two, satisfies $An^q\leq W$, and is at least half of $(W/A)^{1/q}$](goal). -/
-- @node: wide_refinement_budget
lemma wide_refinement_budget {q : ℕ} (hq : 0 < q) {A W : ℝ}
    (hA : 0 < A) (hW : A * (2 : ℝ) ^ q ≤ W) :
    let x := (W / A) ^ (q : ℝ)⁻¹
    2 ≤ ⌊x⌋₊ ∧ A * (⌊x⌋₊ : ℝ) ^ q ≤ W ∧ x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  dsimp only
  have hWA : (2 : ℝ) ^ q ≤ W / A := (le_div_iff₀ hA).2 (by nlinarith [hW])
  have hWApos : 0 < W / A := (pow_pos (by norm_num : (0 : ℝ) < 2) q).trans_le hWA
  have hx : 2 ≤ (W / A) ^ (q : ℝ)⁻¹ := by
    calc
      2 = ((2 : ℝ) ^ q) ^ (q : ℝ)⁻¹ :=
        (Real.pow_rpow_inv_natCast (by norm_num) (Nat.ne_of_gt hq)).symm
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hWA (by positivity)
  have hb := wide_refinement_floor_bounds hx
  refine ⟨hb.1, ?_, hb.2.2⟩
  have hp : (⌊(W / A) ^ (q : ℝ)⁻¹⌋₊ : ℝ) ^ q ≤ W / A := by
    calc
      _ ≤ ((W / A) ^ (q : ℝ)⁻¹) ^ q := by gcongr; exact hb.2.1
      _ = _ := Real.rpow_inv_natCast_pow hWApos.le (Nat.ne_of_gt hq)
  exact (mul_le_mul_of_nonneg_left hp hA.le).trans_eq (mul_div_cancel₀ W hA.ne')

-- @node: wide_refinement_error_rate
/-- If [q is positive](hyp:hq), [A is positive](hyp:hA), and [W is at least
$A2^q$](hyp:hW), then [three q divided by the integer floor of $(W/A)^{1/q}$
is at most $6qA^{1/q}W^{-1/q}$](goal). -/
lemma wide_refinement_error_rate {q : ℕ} (hq : 0 < q) {A W : ℝ}
    (hA : 0 < A) (hW : A * (2 : ℝ) ^ q ≤ W) :
    3 * q / (⌊(W / A) ^ (q : ℝ)⁻¹⌋₊ : ℝ) ≤
      6 * q * A ^ ((q : ℝ)⁻¹) * W ^ (-(1 : ℝ) / q) := by
  have hb := wide_refinement_budget hq hA hW
  have hn : (0 : ℝ) < ⌊(W / A) ^ (q : ℝ)⁻¹⌋₊ := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hb.1)
  have hWp : 0 < W := (mul_pos hA (pow_pos (by norm_num) q)).trans_le hW
  have hx : 0 < (W / A) ^ (q : ℝ)⁻¹ := Real.rpow_pos_of_pos (div_pos hWp hA) _
  calc
    _ ≤ 3 * q / ((W / A) ^ (q : ℝ)⁻¹ / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hb.2.2
    _ = 6 * q * A ^ ((q : ℝ)⁻¹) * W ^ (-(1 : ℝ) / q) := by
      rw [Real.div_rpow hWp.le hA.le]
      rw [show -(1 : ℝ) / q = -((q : ℝ)⁻¹) by simp [div_eq_mul_inv]]
      rw [Real.rpow_neg hWp.le]
      ring_nf
      simp only [inv_inv]
      ring

/-- If [q is positive](hyp:hq), [A is positive](hyp:hA), and [W is at least
$A2^q$](hyp:hW), then [there is an integer refinement n at least two with
$An^q\leq W$, a positive wide quantization mesh smaller than $1/(n(n-1))$,
and a one-norm error bound of $6qA^{1/q}W^{-1/q}$ for the three-term source
error multiplied by $\sqrt q$](goal). -/
-- @node: wide_quantization_budget_error
lemma wide_quantization_budget_error {q : ℕ} (hq : 0 < q) {A W : ℝ}
    (hA : 0 < A) (hW : A * (2 : ℝ) ^ q ≤ W) :
    ∃ n : ℕ, ∃ hn : 2 ≤ n,
      A * (n : ℝ)^q ≤ W ∧
      0 < wideQuantizationParameter q n hn ∧
      wideQuantizationParameter q n hn < 1 / ((n : ℝ) * (n - 1)) ∧
      Real.sqrt q * (Real.sqrt q / (2 * n) + 2 * Real.sqrt q / n +
          (q : ℝ) * (q + 1) / 2 * (n - 1) * wideQuantizationParameter q n hn) ≤
        6 * q * A ^ ((q : ℝ)⁻¹) * W ^ (-(1 : ℝ) / q) := by
  have hb := wide_refinement_budget hq hA hW
  let n := ⌊(W / A) ^ (q : ℝ)⁻¹⌋₊
  have hn : 2 ≤ n := hb.1
  have hm := wideQuantizationParameter_bounds hq hn
  refine ⟨n, hn, hb.2.1, hm.1, hm.2.1.trans_lt hm.2.2, ?_⟩
  exact (wide_quantization_oneNorm_error hq hn).trans
    (wide_refinement_error_rate hq hA hW)

/-- If [q is positive](hyp:hq), [q is at most D](hyp:hqD), [W is at least
one](hyp:hW), and [a is nonnegative](hyp:ha), then [$W^{-a/q}$ is at most
$W^{-a/D}$](goal). -/
-- @node: wide_component_rate_le
lemma wide_component_rate_le {q D : ℕ} (hq : 0 < q) (hqD : q ≤ D)
    {W : ℝ} (hW : 1 ≤ W) {a : ℝ} (ha : 0 ≤ a) :
    W ^ (-a / q) ≤ W ^ (-a / D) := by
  apply Real.rpow_le_rpow_of_exponent_le hW
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hDR : (0 : ℝ) < D := by exact_mod_cast (hq.trans_le hqD)
  have hqDR : (q : ℝ) ≤ D := by exact_mod_cast hqD
  apply (div_le_div_iff₀ hqR hDR).2
  nlinarith

end
end Papers.TbsNeuralCausalPi
