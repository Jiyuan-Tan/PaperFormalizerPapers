module
public import Papers.TbsNeuralCausalPi.Helpers.CausalTableMeshConcentration
public import Papers.TbsNeuralCausalPi.Helpers.SimulationMeshEntropy
/-! # Entropy of the concrete causal-table mesh

The floor grid and rounded simplex alphabet have the dimension-dependent
entropy used in the consistency proof, including the singleton latent cube.
-/
public section
namespace Papers.TbsNeuralCausalPi
open scoped NNReal ENNReal

/-- If [the cube radius is nonnegative](hyp:hK) and [the mesh radius is
positive](hyp:hrho) and [at most one](hyp:hrho1), then [the number of floor
cells in dimension d at spacing rho/(d + 1) is at most
(2K(d + 1) + 1) to the power d times the inverse radius to the power d](goal). -/
-- @node: causalTable_mesh_cells_le
lemma causalTable_mesh_cells_le (d : ℕ) {K rho : ℝ}
    (hK : 0 ≤ K) (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    (((⌊2 * K / (rho / (d + 1))⌋₊ + 1) ^ d : ℕ) : ℝ) ≤
      (2 * K * (d + 1) + 1) ^ d * (rho⁻¹) ^ d := by
  have hf := Nat.floor_le (show 0 ≤ 2 * K / (rho / (d + 1)) by positivity)
  have heq : 2 * K / (rho / (d + 1)) = 2 * K * (d + 1) / rho := by field_simp
  rw [heq] at hf
  have hbase : ((⌊2 * K / (rho / (d + 1))⌋₊ + 1 : ℕ) : ℝ) ≤
      (2 * K * (d + 1) + 1) * rho⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ hrho).mpr
    have h := (le_div_iff₀ hrho).mp hf
    push_cast
    nlinarith
  rw [Nat.cast_pow, ← mul_pow]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) hbase d

/-- For [a positive mesh radius](hyp:hrho), [the logarithm of two plus the
ceiling of its reciprocal is at most twice the logarithm of two plus its
reciprocal](goal). -/
-- @node: causalTable_mesh_resolution_log_le
lemma causalTable_mesh_resolution_log_le {rho : ℝ} (hrho : 0 < rho) :
    Real.log (⌈rho⁻¹⌉₊ + 1 + 1 : ℕ) ≤ 2 * Real.log (2 + rho⁻¹) := by
  have hi : 0 ≤ rho⁻¹ := inv_nonneg.mpr hrho.le
  have hc := Nat.ceil_lt_add_one hi
  have hb : ((⌈rho⁻¹⌉₊ + 1 + 1 : ℕ) : ℝ) ≤ (2 + rho⁻¹) ^ 2 := by
    push_cast
    nlinarith [sq_nonneg (rho⁻¹)]
  have h := Real.log_le_log (by positivity : (0 : ℝ) < (⌈rho⁻¹⌉₊ + 1 + 1 : ℕ)) hb
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

variable {n : ℕ} {kind : Fin n → NodeKind}

/-- For [reference categorical probability vectors](hyp:p0),
[a nonnegative cube radius](hyp:hK), and [a positive mesh radius](hyp:hrho)
[at most one](hyp:hrho1), [the logarithm of the finite propensity-table count
at reciprocal-mesh simplex resolution and spacing rho/(d + 1) is bounded
by twice the total categorical alphabet size over label strata, times
(2K(d + 1) + 1) to the power d, times the inverse radius to the power d,
times the logarithm of two plus the inverse radius](goal). -/
-- @node: causalPropensityTableGrid_mesh_log_card_le
lemma causalPropensityTableGrid_mesh_log_card_le
    (p0 : ∀ i k, kind i = Sum.inr k → probabilitySimplex k)
    (d : ℕ) {K rho : ℝ} (hK : 0 ≤ K) (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    Real.log ((causalPropensityTableGrid p0 (⌈rho⁻¹⌉₊ + 1)
      ((⌊2 * K / (rho / (d + 1))⌋₊ + 1) ^ d)).card : ℝ) ≤
      (2 * (∑ a : CategoricalNodeIndex kind,
        ∑ _c : CategoricalStratum kind, (a.2.val : ℝ)) *
          (2 * K * (d + 1) + 1) ^ d) *
        ((rho⁻¹) ^ d * Real.log (2 + rho⁻¹)) := by
  have hentries : 0 ≤ ∑ a : CategoricalNodeIndex kind,
      ∑ _c : CategoricalStratum kind, (a.2.val : ℝ) := by positivity
  have hlog : 0 ≤ Real.log (⌈rho⁻¹⌉₊ + 1 + 1 : ℕ) :=
    Real.log_nonneg (by norm_cast; omega)
  apply (causalPropensityTableGrid_log_card_le_entries p0 _ _).trans
  have h := mul_le_mul
    (mul_le_mul_of_nonneg_left (causalTable_mesh_cells_le d hK hrho hrho1) hentries)
    (causalTable_mesh_resolution_log_le hrho) hlog (by positivity)
  nlinarith only [h]

/-- For [a nonnegative cube radius](hyp:hK) and [a positive mesh radius](hyp:hrho)
[at most one](hyp:hrho1), [one plus the number of cell-and-label types is at
most the inverse radius to the power d times one plus the number of label
strata times (2K(d + 1) + 1) to the power d](goal). -/
-- @node: causalTable_mesh_types_add_one_le
lemma causalTable_mesh_types_add_one_le (d : ℕ) {K rho : ℝ}
    (hK : 0 ≤ K) (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    (Fintype.card (Fin ((⌊2 * K / (rho / (d + 1))⌋₊ + 1) ^ d) ×
      CategoricalStratum kind) + 1 : ℕ) ≤
      ((Fintype.card (CategoricalStratum kind) : ℝ) *
        (2 * K * (d + 1) + 1) ^ d + 1) * (rho⁻¹) ^ d := by
  have hi : 1 ≤ rho⁻¹ := (one_le_inv₀ hrho).mpr hrho1
  have hip : 1 ≤ (rho⁻¹) ^ d := one_le_pow₀ hi
  have hc := mul_le_mul_of_nonneg_left (causalTable_mesh_cells_le d hK hrho hrho1)
    (Nat.cast_nonneg (Fintype.card (CategoricalStratum kind)) (α := ℝ))
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  nlinarith only [hc, hip]

/-- Suppose [the architecture coefficient E is nonnegative](hyp:hE),
[the comparison constant is positive](hyp:hbase), [the depth H is at least
one](hyp:hH), [the mesh radius is positive](hyp:hrho) and [at most one](hyp:hrho1),
[the integer exponent e is positive](hyp:he), and [e is at most E times H
squared](hyp:hbudget). Then [the logarithm of 2e times base times H divided
by rho and log 2 is at most (log B divided by log 2 plus 3) times
log(2 + H/rho), where B is the maximum of one and 2E times base divided by
log 2](goal). -/
-- @node: causalTable_mesh_shattering_log_le
lemma causalTable_mesh_shattering_log_le {E base H rho : ℝ} {e : ℕ}
    (hE : 0 ≤ E) (hbase : 0 < base) (hH : 1 ≤ H)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (he : 0 < e)
    (hbudget : (e : ℝ) ≤ E * H ^ 2) :
    let B := max 1 (2 * E * base / Real.log 2)
    Real.log (2 * e * (base * H / rho) / Real.log 2) ≤
      (Real.log B / Real.log 2 + 3) * Real.log (2 + H / rho) := by
  intro B
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hB : 1 ≤ B := le_max_left _ _
  have hB0 : 0 < B := by linarith
  have hH0 : 0 < H := by linarith
  have hx : 0 < H / rho := div_pos hH0 hrho
  have hHx : H ≤ H / rho := (le_div_iff₀ hrho).mpr (mul_le_of_le_one_right hH0.le hrho1)
  have harg : 2 * e * (base * H / rho) / Real.log 2 ≤
      B * (2 + H / rho) ^ 3 := by
    calc
      _ ≤ 2 * (E * H ^ 2) * (base * H / rho) / Real.log 2 := by gcongr
      _ = (2 * E * base / Real.log 2) * H ^ 2 * (H / rho) := by ring
      _ ≤ B * (H / rho) ^ 2 * (H / rho) := by
        gcongr
        exact le_max_right _ _
      _ = B * (H / rho) ^ 3 := by ring
      _ ≤ B * (2 + H / rho) ^ 3 := by gcongr; linarith
  have hlog := Real.log_le_log (by positivity :
    0 < 2 * (e : ℝ) * (base * H / rho) / Real.log 2) harg
  rw [Real.log_mul hB0.ne' (by positivity), Real.log_pow] at hlog
  have hl : Real.log 2 ≤ Real.log (2 + H / rho) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hscale := mul_le_mul_of_nonneg_left hl
    (div_nonneg (Real.log_nonneg hB) htwo.le)
  have hid : Real.log B / Real.log 2 * Real.log 2 = Real.log B :=
    div_mul_cancel₀ _ htwo.ne'
  norm_num only [Nat.cast_ofNat] at hlog
  nlinarith only [hlog, hscale, hid]

/-- For [nonnegative table-entropy coefficient T](hyp:hT), [nonnegative
type-count coefficient J](hyp:hJ), [nonnegative architecture coefficient E](hyp:hE),
and [positive comparison constant](hyp:hbase), [there is a positive constant V
such that the integer mesh pseudo-dimension plus one is at most V times the
sum of inverse-radius-to-d times log(2 + inverse radius) and depth squared
times log(2 + depth/radius), whenever the table entropy, augmented type
count, and exponent satisfy their corresponding bounds, depth is at least
one, the exponent is positive, and the radius lies in `(0, 1]`](goal). -/
-- @node: causalTableMeshPseudoDim_entropy_of_counts
lemma causalTableMeshPseudoDim_entropy_of_counts {T J E base : ℝ}
    (hT : 0 ≤ T) (hJ : 0 ≤ J) (hE : 0 ≤ E) (hbase : 0 < base) :
    ∃ V : ℝ, 0 < V ∧ ∀ (tables types e H d : ℕ) (rho : ℝ),
      1 ≤ H → 0 < e → 0 < rho → rho ≤ 1 →
      Real.log (tables : ℝ) ≤ T * ((rho⁻¹) ^ d * Real.log (2 + rho⁻¹)) →
      (types + 1 : ℕ) ≤ J * (rho⁻¹) ^ d →
      (e : ℝ) ≤ E * (H : ℝ) ^ 2 →
      (causalTableMeshPseudoDim tables types e H base rho : ℝ) + 1 ≤
        V * ((rho⁻¹) ^ d * Real.log (2 + rho⁻¹) +
          (H : ℝ) ^ 2 * Real.log (2 + H / rho)) := by
  let B := max 1 (2 * E * base / Real.log 2)
  let a := 2 * (T + J) / Real.log 2
  let c := 2 * E / Real.log 2 * (Real.log B / Real.log 2 + 3)
  let V := a + c + 3 / Real.log 2
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hB : 1 ≤ B := le_max_left _ _
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hc : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg (by positivity) (by positivity [Real.log_nonneg hB])
  have hV : 0 < V := by dsimp [V]; positivity
  refine ⟨V, hV, ?_⟩
  intro tables types e H d rho hH he hrho hrho1 htables htypes hexp
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg _
  let x := (rho⁻¹) ^ d * Real.log (2 + rho⁻¹)
  let y := (H : ℝ) ^ 2 * Real.log (2 + H / rho)
  have hl : Real.log 2 ≤ Real.log (2 + rho⁻¹) :=
    Real.log_le_log (by norm_num) (le_add_of_nonneg_right (by positivity))
  have hlH : Real.log 2 ≤ Real.log (2 + H / rho) :=
    Real.log_le_log (by norm_num) (le_add_of_nonneg_right (by positivity))
  have hx : 0 ≤ x := by dsimp [x]; positivity [htwo.trans_le hl]
  have hy : 0 ≤ y := by dsimp [y]; positivity [htwo.trans_le hlH]
  have ht : 2 * (Real.log (tables : ℝ) + (types + 1 : ℕ) * Real.log 2) /
      Real.log 2 ≤ a * x := by
    have hh := mul_le_mul_of_nonneg_right htypes htwo.le
    have hh' := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ J * (rho⁻¹) ^ d)
    apply (div_le_iff₀ htwo).mpr
    dsimp [a, x] at *
    rw [div_mul_eq_mul_div, div_mul_cancel₀ _ htwo.ne']
    nlinarith only [htables, hh, hh']
  have hs := causalTable_mesh_shattering_log_le hE hbase hHr hrho hrho1 he hexp
  have hn : 2 * e / Real.log 2 *
      Real.log (2 * e * (base * H / rho) / Real.log 2) ≤ c * y := by
    have hcoeff : 2 * (e : ℝ) / Real.log 2 ≤ 2 * E / Real.log 2 * (H : ℝ) ^ 2 := by
      apply (div_le_iff₀ htwo).mpr
      rw [div_mul_eq_mul_div, div_mul_cancel₀ _ htwo.ne']
      nlinarith only [hexp]
    have hu : 0 ≤ (Real.log B / Real.log 2 + 3) * Real.log (2 + H / rho) := by
      exact mul_nonneg (by positivity [Real.log_nonneg hB]) (htwo.trans_le hlH).le
    have hh := (mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * (e : ℝ) / Real.log 2)).trans
      (mul_le_mul_of_nonneg_right hcoeff hu)
    dsimp [c, y]
    nlinarith only [hh]
  let budget := 2 * (Real.log (tables : ℝ) + (types + 1 : ℕ) * Real.log 2) /
    Real.log 2 + 2 * e / Real.log 2 *
      Real.log (2 * e * (base * H / rho) / Real.log 2) + H
  have hb : budget ≤ a * x + c * y + H := by dsimp [budget]; linarith only [ht, hn]
  have hmax : max budget 0 ≤ a * x + c * y + H :=
    max_le hb (by positivity)
  have hround := Nat.ceil_lt_add_one (le_max_right budget 0)
  have hpad : (H : ℝ) + 2 ≤ 3 / Real.log 2 * y := by
    have hsq : (H : ℝ) ≤ (H : ℝ) ^ 2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hlH (sq_nonneg (H : ℝ))
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ htwo).mpr
    dsimp [y]
    nlinarith
  change (⌈max budget 0⌉₊ : ℝ) + 1 ≤ V * (x + y)
  have hcross1 := mul_nonneg ha hy
  have hcross2 := mul_nonneg (show 0 ≤ c + 3 / Real.log 2 by positivity) hx
  dsimp [V]
  nlinarith only [hround, hmax, hpad, hcross1, hcross2]

/-- For [a nonnegative cube radius](hyp:hK) and [positive comparison constant](hyp:hbase),
[there is a positive constant V, uniform over reference probability vectors,
depths at least one and mesh radii in `(0, 1]`, such that the concrete table
mesh pseudo-dimension plus one, with exponent a times depth squared plus
one, is at most V times the sum of inverse-radius-to-d times log(2 + inverse
radius) and depth squared times log(2 + depth/radius)](goal). -/
-- @node: causalTableMeshPseudoDim_mesh_entropy_le
lemma causalTableMeshPseudoDim_mesh_entropy_le (d a : ℕ) {K base : ℝ}
    (hK : 0 ≤ K) (hbase : 0 < base) :
    ∃ V : ℝ, 0 < V ∧
    ∀ (p0 : ∀ i k, kind i = Sum.inr k → probabilitySimplex k)
      (H : ℕ) (rho : ℝ), 1 ≤ H → 0 < rho → rho ≤ 1 →
      let cells := (⌊2 * K / (rho / (d + 1))⌋₊ + 1) ^ d
      let v := causalTableMeshPseudoDim
        (causalPropensityTableGrid p0 (⌈rho⁻¹⌉₊ + 1) cells).card
        (Fintype.card (Fin cells × CategoricalStratum kind))
        (a * H ^ 2 + 1) H base rho
      (v : ℝ) + 1 ≤ V * ((rho⁻¹) ^ d * Real.log (2 + rho⁻¹) +
        (H : ℝ) ^ 2 * Real.log (2 + H / rho)) := by
  let T := 2 * (∑ a : CategoricalNodeIndex kind,
    ∑ _c : CategoricalStratum kind, (a.2.val : ℝ)) * (2 * K * (d + 1) + 1) ^ d
  let J := (Fintype.card (CategoricalStratum kind) : ℝ) *
    (2 * K * (d + 1) + 1) ^ d + 1
  obtain ⟨V, hV, hbound⟩ := causalTableMeshPseudoDim_entropy_of_counts
    (T := T) (J := J) (E := (a : ℝ) + 1) (base := base)
    (by dsimp [T]; positivity) (by dsimp [J]; positivity) (by positivity) hbase
  refine ⟨V, hV, ?_⟩
  intro p0 H rho hH hrho hrho1 cells v
  apply hbound _ _ _ H d rho hH (by positivity) hrho hrho1
    (causalPropensityTableGrid_mesh_log_card_le p0 d hK hrho hrho1)
    (causalTable_mesh_types_add_one_le d hK hrho hrho1)
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  push_cast
  nlinarith

/-- If [the entropy coefficient](hyp:hCt), [decay coefficient](hyp:hc), and
[sample size](hyp:hm) are nonnegative, [the mesh radius is positive](hyp:hrho),
[the smaller tolerance multiplier A is positive](hyp:hA), and [A is at most
B](hyp:hAB), then [the exponential tail expression with multiplier B is
at most the same expression with multiplier A](goal). -/
-- @node: causalTable_mesh_tail_mono
lemma causalTable_mesh_tail_mono {Ct c m rho A B : ℝ} (v : ℕ)
    (hCt : 0 ≤ Ct) (hc : 0 ≤ c) (hm : 0 ≤ m)
    (hrho : 0 < rho) (hA : 0 < A) (hAB : A ≤ B) :
    Real.exp (Ct * ((1 + rho⁻¹) * Real.log (2 + rho⁻¹) +
      (v + 1 : ℕ) * Real.log (2 + (B * rho)⁻¹)) - c * m * (B * rho) ^ 2) ≤
    Real.exp (Ct * ((1 + rho⁻¹) * Real.log (2 + rho⁻¹) +
      (v + 1 : ℕ) * Real.log (2 + (A * rho)⁻¹)) - c * m * (A * rho) ^ 2) := by
  have hB : 0 < B := hA.trans_le hAB
  have hi : (B * rho)⁻¹ ≤ (A * rho)⁻¹ :=
    inv_anti₀ (mul_pos hA hrho) (mul_le_mul_of_nonneg_right hAB hrho.le)
  have hl := Real.log_le_log (by positivity : 0 < 2 + (B * rho)⁻¹) (add_le_add_right hi 2)
  have he := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (v + 1) (α := ℝ))) hCt
  have hs := mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (mul_pos hA hrho).le (by positivity : 0 ≤ B * rho)).mpr
      (mul_le_mul_of_nonneg_right hAB hrho.le)) (mul_nonneg hc hm)
  apply Real.exp_le_exp.mpr
  nlinarith only [he, hs]

/-- For [a nonnegative cube radius](hyp:hK), [positive comparison constant](hyp:hbase),
[nonnegative entropy coefficient](hyp:hCt), and [positive decay coefficient](hyp:hc),
[there is a tolerance multiplier at least one and at least the requested
minimum such that the concrete mesh exponential tail is at most the inverse
cube of sample size](goal), uniformly over reference probability vectors,
depths between one and sample size, and sample sizes at least two with
logarithm at least one, provided the sum of the latent and depth mesh terms
is at most one. -/
-- @node: causalTableMeshPseudoDim_mesh_cubic_tail
lemma causalTableMeshPseudoDim_mesh_cubic_tail (d a : ℕ) {K base Ct c : ℝ}
    (hK : 0 ≤ K) (hbase : 0 < base) (hCt : 0 ≤ Ct) (hc : 0 < c)
    (minimum : ℝ) :
    ∃ mult : ℝ, 1 ≤ mult ∧ minimum ≤ mult ∧
    ∀ (p0 : ∀ i k, kind i = Sum.inr k → probabilitySimplex k)
      (H : ℕ) (m : ℝ), 1 ≤ H → 2 ≤ m → (H : ℝ) ≤ m → 1 ≤ Real.log m →
      let rho := m ^ (-(1 : ℝ) / (max 1 d + 2 : ℕ)) * Real.log m +
        H * Real.log m / Real.sqrt m
      rho ≤ 1 →
      let cells := (⌊2 * K / (rho / (d + 1))⌋₊ + 1) ^ d
      let v := causalTableMeshPseudoDim
        (causalPropensityTableGrid p0 (⌈rho⁻¹⌉₊ + 1) cells).card
        (Fintype.card (Fin cells × CategoricalStratum kind))
        (a * H ^ 2 + 1) H base rho
      Real.exp (Ct * ((1 + rho⁻¹) * Real.log (2 + rho⁻¹) +
        (v + 1 : ℕ) * Real.log (2 + (mult * rho)⁻¹)) -
          c * m * (mult * rho) ^ 2) ≤ m ^ (-(3 : ℝ)) := by
  obtain ⟨V, hV, hdim⟩ := causalTableMeshPseudoDim_mesh_entropy_le
    (kind := kind) d a hK hbase
  obtain ⟨A, hA, htail⟩ := simulation_mesh_pseudodim_cubic_tail hCt hc hV.le
  let mult := max A minimum
  have hAm : A ≤ mult := le_max_left _ _
  refine ⟨mult, hA.trans hAm, le_max_right _ _, ?_⟩
  intro p0 H m hH hm hHm hl rho hrho1 cells v
  have hm1 : 1 ≤ m := by linarith
  have hlatent : m ^ (-(1 : ℝ) / (max 1 d + 2 : ℕ)) * Real.log m ≤ rho := by
    dsimp [rho]
    have hp : 0 ≤ H * Real.log m / Real.sqrt m := by positivity
    linarith
  have hrho : 0 < rho := (mul_pos
    (Real.rpow_pos_of_pos (by linarith : 0 < m) _) (by linarith : 0 < Real.log m)).trans_le hlatent
  have ht := htail m (max 1 d) H d v hm (by exact_mod_cast (le_max_left 1 d))
    (by exact_mod_cast (le_max_right 1 d)) (Nat.cast_nonneg _) hHm hl
  have heq : (max 1 d : ℝ) + 2 = (max 1 d + 2 : ℕ) := by push_cast; rfl
  rw [heq] at ht
  have hv := hdim p0 H rho hH hrho hrho1
  change (v : ℝ) + 1 ≤ V * ((rho⁻¹) ^ d * Real.log (2 + rho⁻¹) +
    (H : ℝ) ^ 2 * Real.log (2 + H / rho)) at hv
  have ht' := ht (by simpa only [rho, Nat.cast_add, Nat.cast_ofNat] using hv)
  apply (causalTable_mesh_tail_mono v hCt hc.le (by linarith) hrho (by linarith) hAm).trans
  simpa only [rho, Nat.cast_add, Nat.cast_one] using ht'

end Papers.TbsNeuralCausalPi
