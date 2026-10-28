module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.AssemblyQuantities

/-! # Uniform numerical estimates for the layered degree embedding

The Hall exponent uses the actual integer bin slack.  Its cutoff is uniform
in the density, the degeneracy bound, the maximum degree, and the layer count.
-/

public section

namespace Papers.OaiGraphDecompositionsIntegral

open scoped BigOperators

/-- If [the layer count t is positive](hyp:ht) and [n is at least 8t](hyp:hn),
then [n is at most eight times the integer layer slack times t](goal). -/
-- @node: degree_layer_slack_lower
lemma degree_layer_slack_lower (n t : ℕ) (ht : 0 < t) (hn : 8 * t ≤ n) :
    (n : ℝ) ≤ 8 * (layerSlack n t ht : ℝ) * t := by
  have ht4 : 0 < 4 * t := by omega
  have hb : 1 ≤ n / (4 * t) := Nat.div_pos (by omega) ht4
  have hrem := Nat.mod_lt n ht4
  have hdiv := Nat.div_add_mod n (4 * t)
  have h : n ≤ 8 * (n / (4 * t)) * t := by nlinarith
  exact_mod_cast h

/-- If [n, r, and s satisfy the transfer parameter conditions](hyp:h), then
[r raised to the power 4s is at least n raised to the power −1/25](goal). -/
-- @node: degree_requirement_power_lower
lemma degree_requirement_power_lower {n s : ℕ} {r : ℝ}
    (h : TransferParameters n r s) :
    (n : ℝ) ^ (-(1 : ℝ) / 25) ≤ r ^ (4 * s) := by
  have hp : ((n : ℝ) ^ (-(1 : ℝ) / 100)) ^ 4 ≤ (r ^ s) ^ 4 := by
    gcongr
    exact h.2.2.2
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n)] at hp
  norm_num at hp
  simpa only [← pow_mul, Nat.mul_comm s 4, neg_div] using hp

/-- Suppose [C is positive](hyp:hC), [the layer count t is positive](hyp:ht),
[n, r, and s satisfy the transfer parameter conditions](hyp:hparams),
[the natural logarithm of n is at least one](hyp:hlog),
[t is at most C times that logarithm squared](hyp:htop),
[n is at least 8C times that logarithm squared](hyp:hn),
[Δ is nonnegative](hyp:hΔ), [Δ is at most n to the power 2/3](hyp:hΔtop),
and [1640C times the fourth power of that logarithm is at most n to the
power 22/75](hyp:hgrowth). Then [the integer layer slack times r to the
power 4s, divided by 1 + 4sΔ, is at least five times the natural logarithm
of n](goal). -/
-- @node: degree_hall_exponent_lower
lemma degree_hall_exponent_lower (C : ℝ) (hC : 0 < C)
    (n t s : ℕ) (r Δ : ℝ) (ht : 0 < t)
    (hparams : TransferParameters n r s)
    (hlog : 1 ≤ naturalLog n)
    (htop : (t : ℝ) ≤ C * naturalLog n ^ 2)
    (hn : 8 * C * naturalLog n ^ 2 ≤ n)
    (hΔ : 0 ≤ Δ) (hΔtop : Δ ≤ (n : ℝ) ^ ((2 : ℝ) / 3))
    (hgrowth : 1640 * C * naturalLog n ^ 4 ≤ (n : ℝ) ^ ((22 : ℝ) / 75)) :
    5 * naturalLog n ≤
      (layerSlack n t ht : ℝ) * r ^ (4 * s) / (1 + 4 * (s : ℝ) * Δ) := by
  have hnpos : (0 : ℝ) < n := by
    have : (0 : ℝ) < 8 * C * naturalLog n ^ 2 := by positivity
    linarith
  have hn8 : 8 * t ≤ n := by
    have : 8 * (t : ℝ) ≤ n := by nlinarith
    exact_mod_cast this
  have hslack := degree_layer_slack_lower n t ht hn8
  have hbin : (n : ℝ) ≤ 8 * (layerSlack n t ht : ℝ) * C * naturalLog n ^ 2 := by
    calc
      (n : ℝ) ≤ 8 * (layerSlack n t ht : ℝ) * t := hslack
      _ ≤ 8 * (layerSlack n t ht : ℝ) * (C * naturalLog n ^ 2) := by
        gcongr
      _ = _ := by ring
  have hpow := degree_requirement_power_lower hparams
  have hnpow : 1 ≤ (n : ℝ) ^ ((2 : ℝ) / 3) := by
    apply Real.one_le_rpow
    · have : 1 ≤ n := by exact_mod_cast hnpos
      exact_mod_cast this
    · norm_num
  have hden : 1 + 4 * (s : ℝ) * Δ ≤
      41 * naturalLog n * (n : ℝ) ^ ((2 : ℝ) / 3) := by
    have hs : (s : ℝ) ≤ 10 * naturalLog n := hparams.2.2.1
    have hmul : (s : ℝ) * Δ ≤ (10 * naturalLog n) * (n : ℝ) ^ ((2 : ℝ) / 3) :=
      mul_le_mul hs hΔtop hΔ (by positivity)
    have hone : 1 ≤ naturalLog n * (n : ℝ) ^ ((2 : ℝ) / 3) :=
      one_le_mul_of_one_le_of_one_le hlog hnpow
    nlinarith
  have hexponents : (n : ℝ) ^ ((2 : ℝ) / 3) * (n : ℝ) ^ ((22 : ℝ) / 75) =
      (n : ℝ) * (n : ℝ) ^ (-(1 : ℝ) / 25) := by
    calc
      _ = (n : ℝ) ^ ((1 : ℝ) + -(1 : ℝ) / 25) := by
        rw [← Real.rpow_add hnpos]
        congr 1
        norm_num
      _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(1 : ℝ) / 25) :=
        Real.rpow_add hnpos _ _
      _ = _ := by rw [Real.rpow_one]
  apply (le_div_iff₀ (by positivity : 0 < 1 + 4 * (s : ℝ) * Δ)).mpr
  have hfirst : 5 * naturalLog n * (1 + 4 * (s : ℝ) * Δ) ≤
      205 * naturalLog n ^ 2 * (n : ℝ) ^ ((2 : ℝ) / 3) := by
    nlinarith
  have hsecond : 1640 * C * naturalLog n ^ 4 * (n : ℝ) ^ ((2 : ℝ) / 3) ≤
      (n : ℝ) * (n : ℝ) ^ (-(1 : ℝ) / 25) := by
    rw [← hexponents]
    nlinarith [Real.rpow_nonneg hnpos.le ((2 : ℝ) / 3)]
  have hthird : (n : ℝ) * (n : ℝ) ^ (-(1 : ℝ) / 25) ≤
      8 * (layerSlack n t ht : ℝ) * C * naturalLog n ^ 2 * r ^ (4 * s) := by
    calc
      _ ≤ (8 * (layerSlack n t ht : ℝ) * C * naturalLog n ^ 2) *
          (n : ℝ) ^ (-(1 : ℝ) / 25) := by gcongr
      _ ≤ _ := by gcongr
  have hfactor : 0 < 8 * C * naturalLog n ^ 2 := by positivity
  have hcombined :
      (8 * C * naturalLog n ^ 2) *
          (205 * naturalLog n ^ 2 * (n : ℝ) ^ ((2 : ℝ) / 3)) ≤
      (8 * C * naturalLog n ^ 2) * ((layerSlack n t ht : ℝ) * r ^ (4 * s)) := by
    nlinarith [hsecond.trans hthird]
  exact hfirst.trans ((mul_le_mul_iff_right₀ hfactor).mp hcombined)

/-- For [positive C](hyp:hC), [there is a cutoff N of at least two such that,
for all n at least N, admissible transfer parameters n, r, s, positive
layer counts t at most C times the squared natural logarithm of n, and
nonnegative Δ at most n to the power 2/3, the integer layer slack times
r to the power 4s divided by 1 + 4sΔ is at least five times the natural
logarithm of n](goal). -/
-- @node: degree_hall_cutoff_exists
lemma degree_hall_cutoff_exists (C : ℝ) (hC : 0 < C) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ (r : ℝ) (s t : ℕ) (Δ : ℝ) (ht : 0 < t),
        TransferParameters n r s →
        (t : ℝ) ≤ C * naturalLog n ^ 2 →
        0 ≤ Δ → Δ ≤ (n : ℝ) ^ ((2 : ℝ) / 3) →
        5 * naturalLog n ≤
          (layerSlack n t ht : ℝ) * r ^ (4 * s) / (1 + 4 * (s : ℝ) * Δ) := by
  have hquad : ∀ᶠ x : ℝ in Filter.atTop,
      Real.log x ^ 2 / x ≤ 1 / (8 * C) := by
    exact (Real.isLittleO_pow_log_id_atTop (n := 2)).tendsto_div_nhds_zero
      |>.eventually_le_const (by positivity)
  have hfour : ∀ᶠ x : ℝ in Filter.atTop,
      Real.log x ^ 4 / x ^ ((22 : ℝ) / 75) ≤ 1 / (1640 * C) := by
    have h := (isLittleO_log_rpow_rpow_atTop (4 : ℝ)
      (by norm_num : (0 : ℝ) < 22 / 75)).tendsto_div_nhds_zero
    simpa using h.eventually_le_const (by positivity : (0 : ℝ) < 1 / (1640 * C))
  have hevent : ∀ᶠ x : ℝ in Filter.atTop,
      1 ≤ Real.log x ∧ 8 * C * Real.log x ^ 2 ≤ x ∧
        1640 * C * Real.log x ^ 4 ≤ x ^ ((22 : ℝ) / 75) := by
    filter_upwards [hquad, hfour, Real.tendsto_log_atTop.eventually_ge_atTop 1,
      Filter.eventually_gt_atTop (0 : ℝ)] with x hq hf hl hx
    refine ⟨hl, ?_, ?_⟩
    · have := (div_le_iff₀ hx).mp hq
      have hq' : Real.log x ^ 2 ≤ x / (8 * C) := by
        simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using this
      have := (le_div_iff₀ (by positivity : 0 < 8 * C)).mp hq'
      nlinarith
    · have := (div_le_iff₀ (Real.rpow_pos_of_pos hx _)).mp hf
      have hf' : Real.log x ^ 4 ≤ x ^ ((22 : ℝ) / 75) / (1640 * C) := by
        simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using this
      have := (le_div_iff₀ (by positivity : 0 < 1640 * C)).mp hf'
      nlinarith
  have hnat := (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ => (n : ℝ))
    Filter.atTop Filter.atTop).eventually hevent
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hnat
  refine ⟨max 2 N, by omega, ?_⟩
  intro n hn r s t Δ ht hp htop hΔ hΔtop
  obtain ⟨hl, hsmall, hgrowth⟩ := hN n (by omega)
  exact degree_hall_exponent_lower C hC n t s r Δ ht hp hl htop hsmall hΔ hΔtop hgrowth

/-- If [n is positive](hyp:hn), then [n to the power 2u times the exponential
of −5u times the natural logarithm of n equals the u-th power of 1/n³](goal). -/
-- @node: degree_hall_summand
lemma degree_hall_summand (n u : ℕ) (hn : 0 < n) :
    (n : ℝ) ^ (2 * u) * Real.exp (-5 * (u : ℝ) * naturalLog n) =
      ((n : ℝ) ^ 3)⁻¹ ^ u := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have he (k : ℕ) : Real.exp ((k : ℝ) * naturalLog n) = (n : ℝ) ^ k := by
    rw [Real.exp_nat_mul, naturalLog, Real.exp_log hnpos]
  calc
    _ = Real.exp (((2 * u : ℕ) : ℝ) * naturalLog n) *
        Real.exp (-5 * (u : ℝ) * naturalLog n) := by rw [he]
    _ = Real.exp ((u : ℝ) * (-(3 * naturalLog n))) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    _ = _ := by
      have he3 := he 3
      norm_num only [Nat.cast_ofNat] at he3
      rw [Real.exp_nat_mul, Real.exp_neg, he3]

/-- If [n is at least two](hyp:hn), then [the sum, for u from zero through
m − 1, of n to the power 2(u + 1) times the exponential of −5(u + 1)
times the natural logarithm of n is at most 2/n³](goal). -/
-- @node: degree_hall_union_bound
lemma degree_hall_union_bound (n m : ℕ) (hn : 2 ≤ n) :
    (∑ u ∈ Finset.range m,
      (n : ℝ) ^ (2 * (u + 1)) * Real.exp (-5 * (u + 1 : ℝ) * naturalLog n)) ≤
        2 / (n : ℝ) ^ 3 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hcube : (2 : ℝ) ≤ (n : ℝ) ^ 3 := by
    calc
      (2 : ℝ) ≤ (2 : ℝ) ^ 3 := by norm_num
      _ ≤ _ := by gcongr
  let q : ℝ := ((n : ℝ) ^ 3)⁻¹
  have hq : 0 ≤ q := by positivity
  have hqhalf : q ≤ 1 / 2 := by
    dsimp [q]
    calc
      _ ≤ (2 : ℝ)⁻¹ := (inv_le_inv₀ (by positivity) (by norm_num)).mpr hcube
      _ = _ := by norm_num
  have hgeom : (∑ u ∈ Finset.range m, q ^ u) ≤ 2 := by
    have hsum : 0 ≤ ∑ u ∈ Finset.range m, q ^ u :=
      Finset.sum_nonneg (fun _ _ => pow_nonneg hq _)
    have heq := geom_sum_mul_neg q m
    have hp := pow_nonneg hq m
    nlinarith
  calc
    _ = ∑ u ∈ Finset.range m, q ^ (u + 1) := by
      apply Finset.sum_congr rfl
      intro u hu
      simpa only [Nat.cast_add, Nat.cast_one] using degree_hall_summand n (u + 1) (by omega)
    _ = q * ∑ u ∈ Finset.range m, q ^ u := by
      simp only [pow_succ, Finset.mul_sum, mul_comm]
    _ ≤ q * 2 := mul_le_mul_of_nonneg_left hgeom hq
    _ = _ := by simp only [q, div_eq_mul_inv, mul_comm]

/-- For [positive C](hyp:hC), [there is a cutoff N of at least two such that,
whenever n is at least N and t is at most C times the squared natural
logarithm of n, the product of t and 2/n³ is at most one half](goal). -/
-- @node: degree_layer_failure_cutoff_exists
lemma degree_layer_failure_cutoff_exists (C : ℝ) (hC : 0 < C) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ t : ℕ, (t : ℝ) ≤ C * naturalLog n ^ 2 →
        (t : ℝ) * (2 / (n : ℝ) ^ 3) ≤ 1 / 2 := by
  have hsmall : ∀ᶠ x : ℝ in Filter.atTop,
      Real.log x ^ 2 / x ^ (3 : ℕ) ≤ 1 / (4 * C) := by
    have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
      (by norm_num : (0 : ℝ) < 3)).tendsto_div_nhds_zero
    simpa using h.eventually_le_const (by positivity : (0 : ℝ) < 1 / (4 * C))
  have hnat := (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ => (n : ℝ))
    Filter.atTop Filter.atTop).eventually hsmall
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hnat
  refine ⟨max 2 N, by omega, ?_⟩
  intro n hn t ht
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsmall := hN n (by omega)
  calc
    (t : ℝ) * (2 / (n : ℝ) ^ 3) ≤
        (C * naturalLog n ^ 2) * (2 / (n : ℝ) ^ 3) := by gcongr
    _ = 2 * C * (Real.log n ^ 2 / (n : ℝ) ^ 3) := by unfold naturalLog; ring
    _ ≤ 2 * C * (1 / (4 * C)) := by gcongr
    _ = 1 / 2 := by field_simp; ring

end Papers.OaiGraphDecompositionsIntegral
