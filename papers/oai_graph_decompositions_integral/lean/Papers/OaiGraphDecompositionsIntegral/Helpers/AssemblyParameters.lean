module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.AssemblyQuantities
public import Papers.OaiGraphDecompositionsIntegral.Helpers.QLower
public import Papers.OaiGraphDecompositionsIntegral.Helpers.HighDegreeClosure
public import Mathlib.Algebra.Order.Floor.Semiring

/-! # Parameters for the large-degeneracy branch

The dense-subgraph lower bound on the expectation threshold supplies the
power constraint needed by both embedding propositions. The ceiling in the
splitting parameter loses at most one, absorbed because d is at least 1000.
-/

public section

namespace Papers.OaiGraphDecompositionsIntegral

/-- If [n is at least one](hyp:hn), [d is positive](hyp:hd), [r is at least
n to the power minus two divided by d](hyp:hlower), and [r is less than
one half](hyp:hr), [d is less than twice the natural logarithm of n divided
by the natural logarithm of two](goal). -/
-- @node: assembly_degeneracy_log_bound
lemma assembly_degeneracy_log_bound (n d : ℕ) (r : ℝ)
    (hn : 1 ≤ n) (hd : 0 < d)
    (hlower : (n : ℝ) ^ (-(2 : ℝ) / (d : ℝ)) ≤ r) (hr : r < 1 / 2) :
    (d : ℝ) < 2 * naturalLog n / naturalLog 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := Real.log_lt_log (Real.rpow_pos_of_pos hnpos _) (hlower.trans_lt hr)
  rw [Real.log_rpow hnpos, Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
    (by norm_num : (2 : ℝ) ≠ 0), Real.log_one, zero_sub] at hlog
  have hmul := (div_lt_iff₀ hdpos).mp
    (show -(2 * Real.log (n : ℝ)) / (d : ℝ) < -Real.log 2 by
      convert hlog using 1
      ring)
  apply (lt_div_iff₀ hlog₂).mpr
  change (d : ℝ) * Real.log 2 < 2 * Real.log (n : ℝ)
  nlinarith

/-- If [d is at least the assembly splitting factor, 1000](hyp:hd), [the
ceiling of twice d divided by 1000 is at least one and at most three d
divided by 1000](goal). -/
-- @node: assembly_split_parameter_bounds
lemma assembly_split_parameter_bounds (d : ℕ) (hd : assemblySplittingFactor ≤ d) :
    1 ≤ ⌈2 * (d : ℝ) / assemblySplittingFactor⌉₊ ∧
      (⌈2 * (d : ℝ) / assemblySplittingFactor⌉₊ : ℝ) ≤
        3 * d / assemblySplittingFactor := by
  have hdreal : (1000 : ℝ) ≤ d := by exact_mod_cast hd
  have hnonneg : 0 ≤ 2 * (d : ℝ) / assemblySplittingFactor := by
    norm_num [assemblySplittingFactor]
    positivity
  have hceil := Nat.le_ceil (2 * (d : ℝ) / assemblySplittingFactor)
  have hceil' := Nat.ceil_lt_add_one hnonneg
  constructor
  · have : (1 : ℝ) ≤ ⌈2 * (d : ℝ) / assemblySplittingFactor⌉₊ := by
      change (1 : ℝ) ≤ ⌈2 * (d : ℝ) / 1000⌉₊
      norm_num [assemblySplittingFactor] at hceil
      linarith
    exact_mod_cast this
  · norm_num [assemblySplittingFactor] at hceil' ⊢
    linarith

/-- If [n is at least one](hyp:hn), [d is positive](hyp:hd), [r is at least
n to the power minus two divided by d](hyp:hlower), and [s is at most three d
divided by the assembly splitting factor](hyp:hs), [n to the power minus
one hundredth is at most r to the power s](goal). -/
-- @node: assembly_split_power_bound
lemma assembly_split_power_bound (n d s : ℕ) (r : ℝ)
    (hn : 1 ≤ n) (hd : 0 < d)
    (hlower : (n : ℝ) ^ (-(2 : ℝ) / (d : ℝ)) ≤ r)
    (hs : (s : ℝ) ≤ 3 * d / assemblySplittingFactor) :
    (n : ℝ) ^ (-(1 : ℝ) / 100) ≤ r ^ s := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hexponent : -(6 : ℝ) / 1000 ≤ (-(2 : ℝ) / (d : ℝ)) * s := by
    norm_num [assemblySplittingFactor] at hs
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hdpos).mpr
    nlinarith
  calc
    (n : ℝ) ^ (-(1 : ℝ) / 100) ≤ (n : ℝ) ^ (-(6 : ℝ) / 1000) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
    _ ≤ (n : ℝ) ^ ((-(2 : ℝ) / (d : ℝ)) * s) :=
      Real.rpow_le_rpow_of_exponent_le hn1 hexponent
    _ = ((n : ℝ) ^ (-(2 : ℝ) / (d : ℝ))) ^ s := by
      rw [Real.rpow_mul hnpos.le, Real.rpow_natCast]
    _ ≤ r ^ s := pow_le_pow_left₀ (Real.rpow_nonneg hnpos.le _) hlower s

/-- If [n is at least one](hyp:hn), [d is at least 1000](hyp:hd), [r is at
least n to the power minus two divided by d](hyp:hlower), and [r is less than
one half](hyp:hr), [r lies strictly between zero and one, and the ceiling s
of twice d divided by 1000 is at most ten times the natural logarithm of n
and satisfies that n to the power minus one hundredth is at most r to the
power s](goal). -/
-- @node: assembly_transfer_parameters
lemma assembly_transfer_parameters (n d : ℕ) (r : ℝ)
    (hn : 1 ≤ n) (hd : assemblySplittingFactor ≤ d)
    (hlower : (n : ℝ) ^ (-(2 : ℝ) / (d : ℝ)) ≤ r) (hr : r < 1 / 2) :
    TransferParameters n r ⌈2 * (d : ℝ) / assemblySplittingFactor⌉₊ := by
  have hdpos : 0 < d := by change 1000 ≤ d at hd; omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hrpos : 0 < r := (Real.rpow_pos_of_pos hnpos _).trans_le hlower
  have hdlog := assembly_degeneracy_log_bound n d r hn hdpos hlower hr
  obtain ⟨_, hs⟩ := assembly_split_parameter_bounds d hd
  refine ⟨hrpos, by linarith, ?_, assembly_split_power_bound n d _ r hn hdpos hlower hs⟩
  have hlog₂ : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hmul := (lt_div_iff₀ (by linarith : 0 < Real.log 2)).mp hdlog
  have hdnonneg : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hdweak : (d : ℝ) < 4 * naturalLog n := by
    change (d : ℝ) * Real.log 2 < 2 * Real.log (n : ℝ) at hmul
    change (d : ℝ) < 4 * Real.log (n : ℝ)
    nlinarith
  norm_num [assemblySplittingFactor] at hs
  change (⌈2 * (d : ℝ) / assemblySplittingFactor⌉₊ : ℝ) ≤ 10 * Real.log (n : ℝ)
  change (d : ℝ) < 4 * Real.log (n : ℝ) at hdweak
  norm_num [assemblySplittingFactor]
  linarith

/-- If [q is less than the reciprocal of twice the star constant A](hyp:hq),
[twice q is less than one half](goal). -/
-- @node: assembly_density_lt_half
lemma assembly_density_lt_half (q : ℝ) (hq : q < 1 / (2 * starConstA)) :
    2 * q < 1 / 2 := by
  have hexp : 1 ≤ Real.exp 4 := Real.one_le_exp_iff.mpr (by norm_num)
  have hA : 2 < starConstA := by unfold starConstA; linarith
  have hquarter : 1 / (2 * starConstA) < (1 / 4 : ℝ) := by
    apply (div_lt_iff₀ (by positivity : 0 < 2 * starConstA)).mpr
    linarith
  linarith

/-- Suppose [the vertex set is finite](hyp:hfinite), [n is at least two](hyp:hn),
[H has at most n vertices](hyp:hV), [H has an edge](hyp:he), [its degeneracy
is at least 1000](hyp:hd), and [its expectation threshold is less than the
reciprocal of twice the star constant A](hyp:hq). Set r to twice that threshold
and s to the ceiling of twice the degeneracy divided by 1000; [s is at least
one and at most three times the degeneracy divided by 1000, the degeneracy
is less than twice the natural logarithm of n divided by the natural logarithm
of two, r is less than one half and positive, s is at most ten times the natural
logarithm of n, and n to the power minus one hundredth is at most r to the power s](goal). -/
-- @node: assembly_graph_parameters
lemma assembly_graph_parameters {V : Type} [Fintype V]
    (H : SimpleGraph V) (n : ℕ) (hfinite : FiniteSimpleGraphs V)
    (hn : 2 ≤ n) (hV : Fintype.card V ≤ n) (he : H.edgeSet.Nonempty)
    (hd : assemblySplittingFactor ≤ degeneracy H)
    (hq : expectationThreshold H n < 1 / (2 * starConstA)) :
    let r := 2 * expectationThreshold H n
    let s := ⌈2 * (degeneracy H : ℝ) / assemblySplittingFactor⌉₊
    1 ≤ s ∧ (s : ℝ) ≤ 3 * degeneracy H / assemblySplittingFactor ∧
      (degeneracy H : ℝ) < 2 * naturalLog n / naturalLog 2 ∧
      r < 1 / 2 ∧ TransferParameters n r s := by
  dsimp only
  have hlower := (q_lower H n hfinite he hV).2
  change (1 / 2 : ℝ) * (n : ℝ) ^ (-(2 : ℝ) / (degeneracy H : ℝ)) ≤
    expectationThreshold H n at hlower
  have hlower' : (n : ℝ) ^ (-(2 : ℝ) / (degeneracy H : ℝ)) ≤
      2 * expectationThreshold H n := by linarith
  have hr := assembly_density_lt_half _ hq
  have hdpos := degeneracy_pos_of_edge H he
  obtain ⟨hspos, hs⟩ := assembly_split_parameter_bounds (degeneracy H) hd
  exact ⟨hspos, hs,
    assembly_degeneracy_log_bound n _ _ (by omega) hdpos hlower' hr, hr,
    assembly_transfer_parameters n _ _ (by omega) hd hlower' hr⟩

open Classical in
/-- Suppose [d is positive](hyp:hdpos), [H has degeneracy at most d](hyp:hd),
[n is positive](hyp:hn), [H has at most n vertices](hyp:hV), [d is less than
twice the natural logarithm of n divided by the natural logarithm of two](hyp:hdlog),
and [eight times the natural logarithm of n divided by the natural logarithm
of two, multiplied by the square root of n, is at most n to the power two thirds](hyp:hcut).
Then [there is a vertex set Y containing every vertex of degree greater than
the square root of n, with at most n to the power two thirds vertices, such
that every vertex outside Y has degree at most the square root of n and at
most twice d neighbors in Y](goal). -/
-- @node: assembly_high_degree_set_small
lemma assembly_high_degree_set_small {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (n d : ℕ)
    (hdpos : 0 < d) (hd : degeneracy H ≤ d) (hn : 0 < n)
    (hV : Fintype.card V ≤ n)
    (hdlog : (d : ℝ) < 2 * naturalLog n / naturalLog 2)
    (hcut : (8 * naturalLog n / naturalLog 2) * Real.sqrt n ≤
      (n : ℝ) ^ ((2 : ℝ) / 3)) :
    ∃ Y : Finset V, initialHighDegreeSet H n ⊆ Y ∧
      (Y.card : ℝ) ≤ (n : ℝ) ^ ((2 : ℝ) / 3) ∧
      ∀ v ∉ Y, (H.degree v : ℝ) ≤ Real.sqrt n ∧
        (H.neighborFinset v ∩ Y).card ≤ 2 * d := by
  obtain ⟨Y, hseed, hsize, hout⟩ := assembly_high_degree_set_exists H d n hdpos hd hn hV
  refine ⟨Y, hseed, hsize.trans (le_trans ?_ hcut), hout⟩
  have hcoeff : 4 * (d : ℝ) ≤ 8 * naturalLog n / naturalLog 2 := by
    calc
      _ ≤ 4 * (2 * naturalLog n / naturalLog 2) :=
        mul_le_mul_of_nonneg_left hdlog.le (by norm_num)
      _ = _ := by ring
  exact mul_le_mul_of_nonneg_right hcoeff (Real.sqrt_nonneg _)

end Papers.OaiGraphDecompositionsIntegral
