module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.Hoeffding
public import Papers.OaiGraphDecompositionsIntegral.Helpers.Compression
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Simultaneous concentration for the transfer tests

The finite union bound ranges over exactly the admissible pairs counted by
`sourceTestCount`. No statistical premise is added to the transfer proposition.
-/

public section

open Causalean.Experimentation.DesignBased Filter Asymptotics
open scoped BigOperators Topology

namespace Papers.OaiGraphDecompositionsIntegral

attribute [local instance] Classical.propDecidable

-- @node: targetDensity_mem_Icc
/-- If [r is nonnegative](hyp:hr0) and [r is at most one](hyp:hr1), then
[the target density 1 − (1 − r)³² lies between zero and one, inclusive](goal). -/
lemma targetDensity_mem_Icc {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    targetDensity r ∈ Set.Icc 0 1 := by
  have hpow : (1 - r) ^ 32 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  constructor
  · dsimp [targetDensity]; linarith
  · dsimp [targetDensity]; linarith [pow_nonneg (show 0 ≤ 1 - r by linarith) 32]

-- @node: targetDensity_le_mul
/-- If [r is nonnegative](hyp:_hr0) and [r is at most one](hyp:hr1), then
[the target density 1 − (1 − r)³² is at most 32r](goal). -/
lemma targetDensity_le_mul {r : ℝ} (_hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    targetDensity r ≤ 32 * r := by
  have h := one_add_mul_le_pow (show -2 ≤ -r by linarith) 32
  norm_num at h
  dsimp [targetDensity]
  convert (show 1 - (1 + -r) ^ 32 ≤ 32 * r by nlinarith [h]) using 1; ring

-- @node: test_mean_lower_bound
/-- If [r is positive](hyp:hr), [p lies strictly between zero and one](hyp:hp),
[r is at most p](hyp:hrp), and [Q is nonempty and every member has between one and s
elements](hyp:hQ), then [an independent random subset with inclusion probability p
contains a member of Q with probability at least r raised to s](goal). -/
lemma test_mean_lower_bound {Y : Type} [Fintype Y] [DecidableEq Y]
    {p r : ℝ} {s : ℕ} (hr : 0 < r) (hp : CompressionDensity p)
    (hrp : r ≤ p) (Q : Finset (Finset Y)) (hQ : CompressionFamily Q s) :
    r ^ s ≤ (productMeasure Y p).Pr (fun z => Satisfies Q (toFinset' z)) := by
  obtain ⟨T, hT⟩ := hQ.1
  calc
    r ^ s ≤ p ^ s := pow_le_pow_left₀ hr.le hrp s
    _ ≤ p ^ T.card := pow_le_pow_of_le_one hp.1.le hp.2.le (hQ.2 T hT).2
    _ = (productMeasure Y p).Pr (fun z => T ⊆ toFinset' z) :=
      (compression_inclusion_probability p hp T).symm
    _ ≤ _ := FiniteDesign.Pr_mono _ _ _ (fun z hz => ⟨T, hT, hz⟩)

-- @node: transfer_test_means_lower
/-- If [r lies strictly between zero and one, s is at most 10 log n, and r raised to s
is at least n to the power −1/100](hyp:hp), and [Q is a nonempty family of sets of sizes
one through s with at most the ceiling of twice r to the power −s members](hyp:hQ), then
[the probabilities of containing a member of Q at densities 1 − (1 − r)² and
1 − (1 − r)³² are both at least n to the power −1/100](goal). -/
lemma transfer_test_means_lower {Y : Type} [Fintype Y] [DecidableEq Y]
    {n s : ℕ} {r : ℝ} (hp : TransferParameters n r s)
    (Q : Finset (Finset Y)) (hQ : AdmissibleTest r s Q) :
    (n : ℝ) ^ (-(1 : ℝ) / 100) ≤ xQ r Q ∧
      (n : ℝ) ^ (-(1 : ℝ) / 100) ≤ xStarQ r Q := by
  have hr0 := hp.1
  have hr1 := hp.2.1
  have hu : CompressionDensity (unionDensity r) := by
    dsimp [CompressionDensity, unionDensity]
    constructor <;> nlinarith [sq_pos_of_pos (show 0 < 1 - r by linarith)]
  have hru : r ≤ unionDensity r := by dsimp [unionDensity]; nlinarith
  have ht : CompressionDensity (targetDensity r) := by
    have hpos : 0 < (1 - r) ^ 32 := pow_pos (by linarith) _
    have hlt : (1 - r) ^ 32 < 1 := pow_lt_one₀ (by linarith) (by linarith) (by norm_num)
    dsimp [CompressionDensity, targetDensity]
    constructor <;> linarith
  have hrt : r ≤ targetDensity r := by
    have h := pow_le_pow_of_le_one (show 0 ≤ 1 - r by linarith)
      (show 1 - r ≤ 1 by linarith) (show 1 ≤ 32 by norm_num)
    simp only [pow_one] at h
    dsimp [targetDensity]; linarith
  exact ⟨hp.2.2.2.trans (test_mean_lower_bound hr0 hu hru Q hQ.1),
    hp.2.2.2.trans (test_mean_lower_bound hr0 ht hrt Q hQ.1)⟩

-- @node: transfer_finite_union_bound
/-- Under a finite probability design D, [the probability that at least one event P indexed
by the finite set A occurs is at most the sum of the probabilities of those events](goal). -/
lemma transfer_finite_union_bound {Ω I : Type} [Fintype Ω]
    (D : FiniteDesign Ω) (A : Finset I) (P : I → Ω → Prop)
    [DecidablePred (fun z => ∃ i ∈ A, P i z)] [∀ i, DecidablePred (P i)] :
    D.Pr (fun z => ∃ i ∈ A, P i z) ≤ ∑ i ∈ A, D.Pr (P i) := by
  unfold FiniteDesign.Pr FiniteDesign.E
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro z _
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (D.p_nonneg z)
  by_cases hz : ∃ i ∈ A, P i z
  · obtain ⟨i, hi, hP⟩ := hz
    have h := Finset.single_le_sum
      (fun j _ => FiniteDesign.ind_nonneg (P j) z) hi
    simpa only [FiniteDesign.ind, if_pos hP,
      if_pos (show ∃ i ∈ A, P i z from ⟨i, hi, hP⟩)] using h
  · simpa [FiniteDesign.ind, hz] using
      (Finset.sum_nonneg (fun i _ => FiniteDesign.ind_nonneg (P i) z))

-- @node: transfer_probability_complement
/-- Under a finite probability design D, [the probability of event P equals one minus
the probability that P does not occur](goal). -/
lemma transfer_probability_complement {Ω : Type} [Fintype Ω]
    (D : FiniteDesign Ω) (P : Ω → Prop) :
    D.Pr P = 1 - D.Pr (fun z => ¬ P z) := by
  have h := D.Pr_split (fun _ => True) P
  have htrue : D.Pr (fun _ => True) = 1 := by
    change D.E (fun _ => (1 : ℝ)) = 1
    exact D.E_const 1
  have hP : D.Pr (fun z => True ∧ P z) = D.Pr P :=
    D.Pr_congr _ _ (by simp)
  have hnP : D.Pr (fun z => True ∧ ¬ P z) = D.Pr (fun z => ¬ P z) :=
    D.Pr_congr _ _ (by simp)
  rw [htrue, hP, hnP] at h
  linarith

-- @node: transfer_simultaneous_failure_bound
/-- Suppose [r lies strictly between zero and one, s is at most 10 log n, and r raised to s
is at least n to the power −1/100](hyp:hp), and [every vertex set of size at most n to the
power 2/3 has at most n/2 vertices](hyp:hhalf). Then [the probability of failing any source
test at density r and the probability of failing any target test at density 1 − (1 − r)³²
are each at most the number of admissible tests times exp(−n to the power 98/100 divided
by 16)](goal). -/
lemma transfer_simultaneous_failure_bound {n s : ℕ} {r : ℝ}
    (hp : TransferParameters n r s)
    (hhalf : ∀ Y : Finset (Fin n),
      (Y.card : ℝ) ≤ (n : ℝ) ^ ((2 : ℝ) / 3) → 2 * Y.card ≤ n) :
    (randomHost n r ⟨hp.1.le, hp.2.1.le⟩).Pr (fun z => toFinset' z ∉ sourceTestFamily n r s) ≤
        sourceTestCount n r s * Real.exp (-(n : ℝ) ^ ((98 : ℝ) / 100) / 16) ∧
    (randomHost n (targetDensity r) (targetDensity_mem_Icc hp.1.le hp.2.1.le)).Pr
      (fun z => ¬ TargetTests n r s (hostGraph z)) ≤
        sourceTestCount n r s * Real.exp (-(n : ℝ) ^ ((98 : ℝ) / 100) / 16) := by
  classical
  let A : Finset ((Y : Finset (Fin n)) × Finset (Finset ↥Y)) :=
    Finset.univ.filter (fun t =>
      (t.1.card : ℝ) ≤ (n : ℝ) ^ ((2 : ℝ) / 3) ∧ AdmissibleTest r s t.2)
  have hcard : A.card = sourceTestCount n r s := rfl
  have hYlt (t : (Y : Finset (Fin n)) × Finset (Finset ↥Y)) (ht : t ∈ A) :
      t.1.card < n := by
    have ht := (Finset.mem_filter.mp ht).2
    obtain ⟨T, hT⟩ := ht.2.1.1
    obtain ⟨y, _⟩ := Finset.card_pos.mp (ht.2.1.2 T hT).1
    have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le y.val.val) y.val.isLt
    have hh := hhalf t.1 ht.1
    omega
  have hbound (t : (Y : Finset (Fin n)) × Finset (Finset ↥Y)) (ht : t ∈ A) :
      (n : ℝ) ^ ((98 : ℝ) / 100) ≤
        2 * ((n : ℝ) - t.1.card) * xQ r t.2 ^ 2 ∧
      (n : ℝ) ^ ((98 : ℝ) / 100) ≤
        2 * ((n : ℝ) - t.1.card) * xStarQ r t.2 ^ 2 := by
    have hnt := hYlt t ht
    have ht := (Finset.mem_filter.mp ht).2
    have hx := transfer_test_means_lower hp t.2 ht.2
    have hn : 0 < (n : ℝ) := by
      exact_mod_cast lt_of_le_of_lt (Nat.zero_le t.1.card) hnt
    have hh : (n : ℝ) ≤ 2 * ((n : ℝ) - t.1.card) := by
      have h := hhalf t.1 ht.1
      have : 2 * (t.1.card : ℝ) ≤ n := by exact_mod_cast h
      linarith
    have heq : (n : ℝ) ^ ((98 : ℝ) / 100) =
        (n : ℝ) * ((n : ℝ) ^ (-(1 : ℝ) / 100)) ^ 2 := by
      calc
        (n : ℝ) ^ ((98 : ℝ) / 100) =
            (n : ℝ) ^ (1 + (-(1 : ℝ) / 100) * (2 : ℕ)) := by congr 1; norm_num
        _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ ((-(1 : ℝ) / 100) * (2 : ℕ)) :=
          Real.rpow_add hn _ _
        _ = _ := by rw [Real.rpow_one, Real.rpow_mul_natCast hn.le]
    rw [heq]
    constructor
    · exact mul_le_mul hh (pow_le_pow_left₀ (by positivity) hx.1 2) (by positivity)
        (by linarith)
    · exact mul_le_mul hh (pow_le_pow_left₀ (by positivity) hx.2 2) (by positivity)
        (by linarith)
  have hsource : ∀ z : KEdge n → Bool, graphOfEdges (toFinset' z) = hostGraph z := by
    intro z
    unfold graphOfEdges
    congr 1
    funext e
    simp [toFinset']
  constructor
  · have hevent : (fun z => toFinset' z ∉ sourceTestFamily n r s) =
        (fun z => ∃ t ∈ A, ¬ SourceTest t.1 r t.2 (hostGraph z)) := by
      funext z
      apply propext
      simp [sourceTestFamily, hsource, A, exists_and_left, and_assoc]
    have hprob := (randomHost n r ⟨hp.1.le, hp.2.1.le⟩).Pr_congr
      (fun z => toFinset' z ∉ sourceTestFamily n r s)
      (fun z => ∃ t ∈ A, ¬ SourceTest t.1 r t.2 (hostGraph z))
      (fun z => Iff.of_eq (congrFun hevent z))
    apply hprob.le.trans
    have hunion := transfer_finite_union_bound (randomHost n r ⟨hp.1.le, hp.2.1.le⟩) A
      (fun t z => ¬ SourceTest t.1 r t.2 (hostGraph z))
    apply hunion.trans
    calc
      _ ≤ ∑ _t ∈ A, Real.exp (-(n : ℝ) ^ ((98 : ℝ) / 100) / 16) := by
        apply Finset.sum_le_sum
        intro t ht
        apply (sourceTest_failure_bound t.1 (hYlt t ht) r hp.1.le hp.2.1.le t.2).trans
        apply Real.exp_le_exp.mpr
        have h := (hbound t ht).1
        have := Real.rpow_nonneg (Nat.cast_nonneg n) ((98 : ℝ) / 100)
        linarith
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hcard]
  · have hevent : (fun z => ¬ TargetTests n r s (hostGraph z)) =
        (fun z => ∃ t ∈ A, ¬ ((3 / 4 : ℝ) * xStarQ r t.2 ≤
          (1 / ((n : ℝ) - t.1.card)) *
            (((Finset.univ \ t.1).filter (fun w =>
              Satisfies t.2 (neighborhoodIn t.1 (hostGraph z) w))).card : ℝ))) := by
      funext z
      apply propext
      simp [TargetTests, A, exists_and_left, and_assoc]
    have hprob :=
      (randomHost n (targetDensity r) (targetDensity_mem_Icc hp.1.le hp.2.1.le)).Pr_congr
      (fun z => ¬ TargetTests n r s (hostGraph z)) _
      (fun z => Iff.of_eq (congrFun hevent z))
    apply hprob.le.trans
    apply (transfer_finite_union_bound _ A _).trans
    calc
      _ ≤ ∑ _t ∈ A, Real.exp (-(n : ℝ) ^ ((98 : ℝ) / 100) / 16) := by
        apply Finset.sum_le_sum
        intro t ht
        apply (targetTest_failure_bound t.1 (hYlt t ht) r ⟨hp.1.le, hp.2.1.le⟩ t.2).trans
        apply Real.exp_le_exp.mpr
        have h := (hbound t ht).2
        linarith
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hcard]

-- @node: transfer_counting_exponent_small
/-- For [positive C](hyp:hC) and [positive ε](hyp:hε), [all sufficiently large real x satisfy
C times the sum of x to the power 2/3 times log x and x to the power 1/100 times
the square of log x being at most ε times x to the power 98/100](goal). -/
lemma transfer_counting_exponent_small (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      C * (x ^ ((2 : ℝ) / 3) * Real.log x +
        x ^ ((1 : ℝ) / 100) * Real.log x ^ 2) ≤ ε * x ^ ((98 : ℝ) / 100) := by
  have hlog := (isLittleO_log_rpow_atTop
    (show 0 < (47 : ℝ) / 150 by norm_num)).def (c := ε / (2 * C)) (by positivity)
  have hlog₂ := (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
    (show 0 < (97 : ℝ) / 100 by norm_num)).def (c := ε / (2 * C)) (by positivity)
  filter_upwards [hlog, hlog₂, eventually_ge_atTop (1 : ℝ)] with x h₁ h₂ hx
  have hx0 : 0 < x := by linarith
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  simp only [Real.norm_eq_abs, abs_of_nonneg hl,
    abs_of_nonneg (Real.rpow_nonneg hx0.le _)] at h₁
  rw [Real.rpow_two] at h₂
  simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log x)),
    abs_of_nonneg (Real.rpow_nonneg hx0.le _)] at h₂
  have heq₁ : x ^ ((2 : ℝ) / 3) * x ^ ((47 : ℝ) / 150) =
      x ^ ((98 : ℝ) / 100) := by rw [← Real.rpow_add hx0]; congr 1; norm_num
  have heq₂ : x ^ ((1 : ℝ) / 100) * x ^ ((97 : ℝ) / 100) =
      x ^ ((98 : ℝ) / 100) := by rw [← Real.rpow_add hx0]; congr 1; norm_num
  have h₁' := mul_le_mul_of_nonneg_left h₁
    (Real.rpow_nonneg hx0.le ((2 : ℝ) / 3))
  have h₂' := mul_le_mul_of_nonneg_left h₂
    (Real.rpow_nonneg hx0.le ((1 : ℝ) / 100))
  rw [mul_left_comm, heq₁] at h₁'
  rw [mul_left_comm, heq₂] at h₂'
  have hdiv : C * (ε / (2 * C)) = ε / 2 := by field_simp [hC.ne']
  have h₁'' := mul_le_mul_of_nonneg_left h₁' hC.le
  have h₂'' := mul_le_mul_of_nonneg_left h₂' hC.le
  simp only [← mul_assoc, hdiv] at h₁'' h₂''
  linarith

-- @node: transfer_concentration_cutoff
/-- [There is an absolute integer cutoff such that, for every host order n above it,
every vertex set of size at most n to the power 2/3 has at most n/2 vertices, and,
uniformly over r strictly between zero and one and s satisfying s ≤ 10 log n and
r raised to s ≥ n to the power −1/100, the number of admissible tests times
exp(−n to the power 98/100 divided by 16) is at most the smaller of 1/K₀ and 1/2](goal). -/
lemma transfer_concentration_cutoff :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∀ Y : Finset (Fin n), (Y.card : ℝ) ≤ (n : ℝ) ^ ((2 : ℝ) / 3) →
        2 * Y.card ≤ n) ∧
      ∀ (r : ℝ) (s : ℕ), TransferParameters n r s →
        sourceTestCount n r s * Real.exp (-(n : ℝ) ^ ((98 : ℝ) / 100) / 16) ≤
          min (1 / (K0 : ℝ)) (1 / 2) := by
  obtain ⟨C, hC, hcount⟩ := sourceTest_count_bound
  have hsmall := transfer_counting_exponent_small C (1 / 32) hC (by norm_num)
  have hhalf := (tendsto_rpow_atTop (show 0 < (1 : ℝ) / 3 by norm_num)).eventually
    (eventually_ge_atTop (2 : ℝ))
  have htail : Tendsto (fun x : ℝ => Real.exp (-(x ^ ((98 : ℝ) / 100) / 32)))
      atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero.comp
        ((tendsto_rpow_atTop (show 0 < (98 : ℝ) / 100 by norm_num)).atTop_div_const
          (by norm_num : (0 : ℝ) < 32))
  have hε : (0 : ℝ) < min (1 / (K0 : ℝ)) (1 / 2) := by
    have : (0 : ℝ) < (K0 : ℝ) := by norm_num [K0]
    exact lt_min (by positivity) (by norm_num)
  have hevent := htail.eventually (eventually_lt_nhds hε)
  have hall : ∀ᶠ n : ℕ in atTop,
      (2 : ℝ) ≤ n ∧
      C * ((n : ℝ) ^ ((2 : ℝ) / 3) * Real.log n +
        (n : ℝ) ^ ((1 : ℝ) / 100) * Real.log n ^ 2) ≤
          (1 / 32 : ℝ) * (n : ℝ) ^ ((98 : ℝ) / 100) ∧
      2 ≤ (n : ℝ) ^ ((1 : ℝ) / 3) ∧
      Real.exp (-((n : ℝ) ^ ((98 : ℝ) / 100) / 32)) <
        min (1 / (K0 : ℝ)) (1 / 2) := by
    exact (tendsto_natCast_atTop_atTop.eventually
      ((eventually_ge_atTop (2 : ℝ)).and (hsmall.and (hhalf.and hevent))))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hall
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨hn₂, hsmall, hhalf, htail⟩ := hN n hn
  have hn0 : (0 : ℝ) < n := by linarith
  constructor
  · intro Y hY
    have heq : (n : ℝ) ^ ((2 : ℝ) / 3) * (n : ℝ) ^ ((1 : ℝ) / 3) = n := by
      rw [← Real.rpow_add hn0]
      norm_num
    have h := mul_le_mul_of_nonneg_left hhalf
      (Real.rpow_nonneg hn0.le ((2 : ℝ) / 3))
    rw [heq] at h
    have : 2 * (Y.card : ℝ) ≤ n := by nlinarith
    exact_mod_cast this
  · intro r s hp
    have hc := hcount n r s (by exact_mod_cast hn₂) hp
    have hlog : Real.log (max 1 (sourceTestCount n r s : ℝ)) ≤
        (1 / 32 : ℝ) * (n : ℝ) ^ ((98 : ℝ) / 100) := hc.trans hsmall
    have hcount' : (sourceTestCount n r s : ℝ) ≤
        Real.exp ((1 / 32 : ℝ) * (n : ℝ) ^ ((98 : ℝ) / 100)) := by
      calc
        _ ≤ max 1 (sourceTestCount n r s : ℝ) := le_max_right _ _
        _ = Real.exp (Real.log (max 1 (sourceTestCount n r s : ℝ))) :=
          (Real.exp_log (by positivity)).symm
        _ ≤ _ := Real.exp_le_exp.mpr hlog
    calc
      _ ≤ Real.exp ((1 / 32 : ℝ) * (n : ℝ) ^ ((98 : ℝ) / 100)) *
          Real.exp (-(n : ℝ) ^ ((98 : ℝ) / 100) / 16) :=
        mul_le_mul_of_nonneg_right hcount' (Real.exp_nonneg _)
      _ = Real.exp (-((n : ℝ) ^ ((98 : ℝ) / 100) / 32)) := by
        rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := htail.le

-- @node: transfer_simultaneous_events
/-- [There is an absolute integer cutoff such that, for every larger host order n and
parameters with r strictly between zero and one, s ≤ 10 log n, and r raised to s ≥
n to the power −1/100, the source test family has probability at least 1 − 1/K₀ at
density r, and all target tests hold simultaneously with probability at least one half
at density 1 − (1 − r)³²](goal). -/
lemma transfer_simultaneous_events :
    ∃ N : ℕ, ∀ (n : ℕ) (r : ℝ) (s : ℕ), N ≤ n → ∀ hp : TransferParameters n r s,
      1 - 1 / (K0 : ℝ) ≤ muMass (KEdge n) r (sourceTestFamily n r s) ∧
      (1 / 2 : ℝ) ≤ (randomHost n (targetDensity r) (targetDensity_mem_Icc hp.1.le hp.2.1.le)).Pr
        (fun z => TargetTests n r s (hostGraph z)) := by
  obtain ⟨N, hN⟩ := transfer_concentration_cutoff
  refine ⟨N, ?_⟩
  intro n r s hn hp
  obtain ⟨hhalf, herror⟩ := hN n hn
  obtain ⟨hsource, htarget⟩ := transfer_simultaneous_failure_bound hp hhalf
  have hs := hsource.trans ((herror r s hp).trans (min_le_left _ _))
  have ht := htarget.trans ((herror r s hp).trans (min_le_right _ _))
  constructor
  · unfold muMass
    rw [transfer_probability_complement]
    change 1 - 1 / (K0 : ℝ) ≤ 1 - (randomHost n r ⟨hp.1.le, hp.2.1.le⟩).Pr
      (fun z => toFinset' z ∉ sourceTestFamily n r s)
    linarith
  · rw [transfer_probability_complement]
    linarith

end Papers.OaiGraphDecompositionsIntegral
