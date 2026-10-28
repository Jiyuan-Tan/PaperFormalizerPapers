module
public import Papers.OaiGraphDecompositionsIntegral.Basic
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Finset.Sigma

/-! # Simultaneous neighborhood tests for transfer

Every smoothing extension has density r. Its union with an independent source
neighborhood has density tau = 1 - (1-r)^2.
-/

@[expose] public section

open Causalean.Experimentation.DesignBased
open scoped BigOperators

namespace Papers.OaiGraphDecompositionsIntegral

variable {n : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]

/-- For [an inclusion parameter r](hyp:r), [the union density](goal) is one
minus the square of one minus r, the density of the union of two independent
subsets with inclusion probability r when r lies in the unit interval.
@realizes \tau(density of the union of two independent Bernoulli-r subsets) -/
def unionDensity (r : ℝ) : ℝ := 1 - (1 - r) ^ 2

/-- For [an inclusion parameter r](hyp:r), [the target density](goal) is one
minus the thirty-second power of the difference between one and r.
@realizes r_*(target density 1-(1-r)^32) -/
def targetDensity (r : ℝ) : ℝ := 1 - (1 - r) ^ 32

/-- On [a finite ground set Y](hyp:Y), for [a source parameter r](hyp:r) and
[a family Q of required subsets](hyp:Q), [the source satisfaction probability](goal)
is the probability that an independent random subset at the union density
contains at least one member of Q.
@realizes x(\calQ)(satisfaction probability under Bernoulli-tau on Y) -/
noncomputable def xQ (r : ℝ) (Q : Finset (Finset Y)) : ℝ := by
  classical
  exact (productMeasure Y (unionDensity r)).Pr (fun z => Satisfies Q (toFinset' z))

/-- On [a finite ground set Y](hyp:Y), for [a source parameter r](hyp:r) and
[a family Q of required subsets](hyp:Q), [the target satisfaction probability](goal)
is the probability that an independent random subset at the target density
contains at least one member of Q.
@realizes x_*(\calQ)(satisfaction probability under Bernoulli-r_* on Y) -/
noncomputable def xStarQ (r : ℝ) (Q : Finset (Finset Y)) : ℝ := by
  classical
  exact (productMeasure Y (targetDensity r)).Pr (fun z => Satisfies Q (toFinset' z))

/-- For [a density parameter r](hyp:r), [a size bound s](hyp:s), and
[a family Q of subsets of the finite ground set Y](hyp:Q,Y), [admissibility](goal)
requires [Q to be nonempty, with every member having between one and s elements](step:1),
and [the number of members to be at most the integer ceiling of twice r raised
to minus s](step:2). -/
def AdmissibleTest (r : ℝ) (s : ℕ) (Q : Finset (Finset Y)) : Prop :=
  CompressionFamily Q s ∧ (Q.card : ℝ) ≤ (⌈2 * r ^ (-(s : ℤ))⌉ : ℤ)

/-- In [a host of order n](hyp:n), for [a vertex set Y](hyp:Y),
[a graph J](hyp:J), and [a vertex w](hyp:w), [the neighborhood in Y](goal)
is the set of vertices of Y adjacent to w in J, regarded as a subset of Y.
@realizes N_J(neighbors in the fixed set Y, regarded as subsets of Y) -/
noncomputable def neighborhoodIn (Y : Finset (Fin n)) (J : SimpleGraph (Fin n))
    (w : Fin n) : Finset ↥Y := by
  classical
  exact Finset.univ.filter (fun y => J.Adj w y.val)

/-- In [a host of order n](hyp:n), for [a vertex set Y](hyp:Y),
[a source density r](hyp:r), [a requirement family Q on Y](hyp:Q), and
[a graph G](hyp:G), [the source test condition](goal) says that the sum of
smoothed test values of the neighborhoods of vertices outside Y, divided by
n minus the size of Y, is at most twice the source satisfaction probability. -/
noncomputable def SourceTest (Y : Finset (Fin n)) (r : ℝ)
    (Q : Finset (Finset ↥Y)) (G : SimpleGraph (Fin n)) : Prop :=
  (1 / ((n : ℝ) - Y.card)) *
      (∑ w ∈ Finset.univ \ Y, smoothedTest ↥Y r Q (neighborhoodIn Y G w)) ≤ 2 * xQ r Q

/-- For [a host order n](hyp:n), [a source density r](hyp:r), and
[a requirement size bound s](hyp:s), [the source test family](goal) consists
of host edge sets whose graphs satisfy the source test for every vertex set
of size at most n to the two-thirds power and every admissible requirement
family on that set. -/
noncomputable def sourceTestFamily (n : ℕ) (r : ℝ) (s : ℕ) :
    Set (Finset (KEdge n)) :=
  {G | ∀ Y : Finset (Fin n), (Y.card : ℝ) ≤ (n : ℝ) ^ ((2 : ℝ) / 3) →
    ∀ Q : Finset (Finset ↥Y), AdmissibleTest r s Q → SourceTest Y r Q (graphOfEdges G)}

/-- For [a host order n](hyp:n), [a source density r](hyp:r),
[a requirement size bound s](hyp:s), and [a target graph Gstar](hyp:Gstar),
[the simultaneous target test condition](goal) requires that, for every vertex
set Y of size at most n to the two-thirds power and every admissible requirement
family Q on Y, the fraction of vertices outside Y whose neighborhoods contain
a member of Q is at least three quarters of the target satisfaction probability.
@realizes G_*(target realization tested simultaneously on the same Y,Q domain) -/
noncomputable def TargetTests (n : ℕ) (r : ℝ) (s : ℕ)
    (Gstar : SimpleGraph (Fin n)) : Prop := by
  classical
  exact ∀ Y : Finset (Fin n), (Y.card : ℝ) ≤ (n : ℝ) ^ ((2 : ℝ) / 3) →
    ∀ Q : Finset (Finset ↥Y), AdmissibleTest r s Q →
      (3 / 4 : ℝ) * xStarQ r Q ≤
        (1 / ((n : ℝ) - Y.card)) *
          (((Finset.univ \ Y).filter
            (fun w => Satisfies Q (neighborhoodIn Y Gstar w))).card : ℝ)


/-- For [a host order n](hyp:n), [a density parameter r](hyp:r), and
[a requirement size bound s](hyp:s), [the source test count](goal) is the
number of pairs consisting of a vertex set of size at most n to the two-thirds
power and an admissible requirement family on that set. -/
noncomputable def sourceTestCount (n : ℕ) (r : ℝ) (s : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter
    (fun test : (Y : Finset (Fin n)) × Finset (Finset ↥Y) =>
      (test.1.card : ℝ) ≤ (n : ℝ) ^ ((2 : ℝ) / 3) ∧
        AdmissibleTest r s test.2)).card

attribute [local instance] Classical.propDecidable

-- @node: testCounting_sum_powers
/-- [The sum of the powers of a from exponent zero through k is at most
the kth power of the sum of a and one](goal), for all natural numbers a and k. -/
lemma testCounting_sum_powers (a k : ℕ) :
    (∑ i ∈ Finset.range (k + 1), a ^ i) ≤ (a + 1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ, pow_succ]
    have hp := Nat.pow_le_pow_left (Nat.le_succ a) k
    nlinarith

-- @node: testCounting_small_subsets
/-- [The number of subsets of a finite set A having at most k elements is
at most the kth power of the sum of the size of A and one](goal). -/
lemma testCounting_small_subsets {α : Type*}
    (A : Finset α) (k : ℕ) :
    (A.powerset.filter (fun T => T.card ≤ k)).card ≤ (A.card + 1) ^ k := by
  classical
  have heq : A.powerset.filter (fun T => T.card ≤ k) =
      (Finset.range (k + 1)).biUnion (fun i => A.powersetCard i) := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion,
      Finset.mem_range, Finset.mem_powersetCard]
    constructor
    · rintro ⟨hT, hk⟩
      exact ⟨T.card, by omega, hT, rfl⟩
    · rintro ⟨i, hi, hT, rfl⟩
      exact ⟨hT, by omega⟩
  rw [heq]
  calc
    _ ≤ ∑ i ∈ Finset.range (k + 1), (A.powersetCard i).card :=
      Finset.card_biUnion_le
    _ = ∑ i ∈ Finset.range (k + 1), A.card.choose i := by
      simp only [Finset.card_powersetCard]
    _ ≤ ∑ i ∈ Finset.range (k + 1), A.card ^ i :=
      Finset.sum_le_sum (fun i _ => Nat.choose_le_pow _ _)
    _ ≤ (A.card + 1) ^ k := testCounting_sum_powers _ _

-- @node: testCounting_admissible_families
/-- [The number of admissible requirement families on a finite ground set Y
is at most one plus the sth power of the sum of the size of Y and one,
with this entire bound raised to the nonnegative integer ceiling of twice r
raised to minus s](goal). -/
lemma testCounting_admissible_families {Y : Type} [Fintype Y]
    (r : ℝ) (s : ℕ) :
    (Finset.univ.filter (fun Q : Finset (Finset Y) => AdmissibleTest r s Q)).card ≤
      ((Fintype.card Y + 1) ^ s + 1) ^ ⌈2 * r ^ (-(s : ℤ))⌉₊ := by
  classical
  let A : Finset (Finset Y) := Finset.univ.powerset.filter (fun T => T.card ≤ s)
  have hA : A.card ≤ (Fintype.card Y + 1) ^ s := by
    simpa only [Finset.card_univ] using testCounting_small_subsets (Finset.univ : Finset Y) s
  have hsub : Finset.univ.filter (fun Q : Finset (Finset Y) => AdmissibleTest r s Q) ⊆
      A.powerset.filter (fun Q => Q.card ≤ ⌈2 * r ^ (-(s : ℤ))⌉₊) := by
    intro Q hQ
    have hQ := (Finset.mem_filter.mp hQ).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr ?_, ?_⟩
    · intro T hT
      simp only [A, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
      exact (hQ.1.2 T hT).2
    · have hi : (Q.card : ℤ) ≤ ⌈2 * r ^ (-(s : ℤ))⌉ := by exact_mod_cast hQ.2
      rw [← Int.ceil_toNat]
      omega
  exact (Finset.card_le_card hsub).trans
    ((testCounting_small_subsets A _).trans (Nat.pow_le_pow_left (Nat.add_le_add_right hA 1) _))

-- @node: testCounting_count_le
/-- [The source test count is at most the product of two factors: the sum
of n and one raised to the nonnegative integer floor of n to the two-thirds
power; and one plus the sth power of the sum of n and one, with this entire
second base raised to the nonnegative integer ceiling of twice r raised
to minus s](goal). -/
lemma testCounting_count_le (n : ℕ) (r : ℝ) (s : ℕ) :
    sourceTestCount n r s ≤
      (n + 1) ^ ⌊(n : ℝ) ^ ((2 : ℝ) / 3)⌋₊ *
        ((n + 1) ^ s + 1) ^ ⌈2 * r ^ (-(s : ℤ))⌉₊ := by
  classical
  let Ys := (Finset.univ : Finset (Finset (Fin n))).filter
    (fun Y => (Y.card : ℝ) ≤ (n : ℝ) ^ ((2 : ℝ) / 3))
  have hcount : sourceTestCount n r s =
      ∑ Y ∈ Ys, (Finset.univ.filter
        (fun Q : Finset (Finset ↥Y) => AdmissibleTest r s Q)).card := by
    unfold sourceTestCount
    rw [← Finset.card_sigma]
    congr 1
    ext ⟨Y, Q⟩
    simp [Ys]
  have hYs : Ys.card ≤ (n + 1) ^ ⌊(n : ℝ) ^ ((2 : ℝ) / 3)⌋₊ := by
    have heq : Ys = (Finset.univ : Finset (Fin n)).powerset.filter
        (fun Y => Y.card ≤ ⌊(n : ℝ) ^ ((2 : ℝ) / 3)⌋₊) := by
      ext Y
      simp [Ys, Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
    rw [heq]
    simpa using testCounting_small_subsets (Finset.univ : Finset (Fin n)) _
  rw [hcount]
  calc
    _ ≤ ∑ _Y ∈ Ys, ((n + 1) ^ s + 1) ^ ⌈2 * r ^ (-(s : ℤ))⌉₊ := by
      apply Finset.sum_le_sum
      intro Y _
      apply (testCounting_admissible_families r s).trans
      apply Nat.pow_le_pow_left
      apply Nat.add_le_add_right
      apply Nat.pow_le_pow_left
      have hcard : Fintype.card ↥Y ≤ n := by
        simpa using Finset.card_le_univ Y
      omega
    _ = Ys.card * (((n + 1) ^ s + 1) ^ ⌈2 * r ^ (-(s : ℤ))⌉₊) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ hYs

-- @node: sourceTest_count_bound
/-- [There is a positive absolute constant C such that, whenever n is at
least two and the transfer parameter conditions hold, the natural logarithm
of the larger of one and the source test count is at most C times the sum
of n to the two-thirds power times the natural logarithm of n, and n to the
one-hundredth power times the square of that logarithm](goal). -/
lemma sourceTest_count_bound :
    ∃ C : ℝ, 0 < C ∧ -- @realizes C(positive absolute counting constant)
      ∀ (n : ℕ) (r : ℝ) (s : ℕ), 2 ≤ n → TransferParameters n r s →
        naturalLog (max 1 (sourceTestCount n r s)) ≤
          C * ((n : ℝ) ^ ((2 : ℝ) / 3) * naturalLog n +
            (n : ℝ) ^ ((1 : ℝ) / 100) * (naturalLog n) ^ 2) := by
  refine ⟨100, by norm_num, ?_⟩
  intro n r s hn hp
  obtain ⟨hr0, _hr1, hsparam, hpower⟩ := hp
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hloghalf : (1 / 2 : ℝ) ≤ Real.log n := by
    have hinv : (n : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := (inv_le_inv₀ hn0 (by norm_num)).mpr hn2
    have := Real.one_sub_inv_le_log_of_pos hn0
    norm_num at hinv
    linarith
  have hlogplus : Real.log ((n : ℝ) + 1) ≤ 2 * Real.log n := by
    calc
      _ ≤ Real.log ((n : ℝ) ^ 2) :=
        Real.log_le_log (by positivity) (by nlinarith)
      _ = _ := by rw [Real.log_pow]; norm_num
  have hN : 1 ≤ (n : ℝ) ^ ((1 : ℝ) / 100) :=
    Real.one_le_rpow hn1 (by norm_num)
  have hinverse : r ^ (-(s : ℤ)) ≤ (n : ℝ) ^ ((1 : ℝ) / 100) := by
    rw [zpow_neg, zpow_natCast]
    have h := (inv_le_inv₀ (pow_pos hr0 s) (Real.rpow_pos_of_pos hn0 _)).mpr hpower
    have heq : -(1 : ℝ) / 100 = -((1 : ℝ) / 100) := by ring
    rw [heq, Real.rpow_neg hn0.le, inv_inv] at h
    exact h
  have hk : (⌈2 * r ^ (-(s : ℤ))⌉₊ : ℝ) ≤
      3 * (n : ℝ) ^ ((1 : ℝ) / 100) := by
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ 2 * r ^ (-(s : ℤ)) by positivity)
    linarith
  have ha : (⌊(n : ℝ) ^ ((2 : ℝ) / 3)⌋₊ : ℝ) ≤
      (n : ℝ) ^ ((2 : ℝ) / 3) := Nat.floor_le (by positivity)
  have hs : (s : ℝ) + 1 ≤ 12 * Real.log n := by
    change (s : ℝ) ≤ 10 * Real.log n at hsparam
    linarith
  have hbase : Real.log (((n : ℝ) + 1) ^ s + 1) ≤
      ((s : ℝ) + 1) * (2 * Real.log n) := by
    have hp1 : 1 ≤ ((n : ℝ) + 1) ^ s := one_le_pow₀ (by linarith)
    calc
      _ ≤ Real.log (((n : ℝ) + 1) ^ (s + 1)) :=
        Real.log_le_log (by positivity) (by rw [pow_succ]; nlinarith)
      _ = ((s : ℝ) + 1) * Real.log ((n : ℝ) + 1) := by
        rw [Real.log_pow, Nat.cast_add, Nat.cast_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left hlogplus (by positivity)
  have hcount := testCounting_count_le n r s
  have hcountR : (sourceTestCount n r s : ℝ) ≤
      ((n : ℝ) + 1) ^ ⌊(n : ℝ) ^ ((2 : ℝ) / 3)⌋₊ *
        (((n : ℝ) + 1) ^ s + 1) ^ ⌈2 * r ^ (-(s : ℤ))⌉₊ := by
    exact_mod_cast hcount
  have hlarge : 1 ≤
      ((n : ℝ) + 1) ^ ⌊(n : ℝ) ^ ((2 : ℝ) / 3)⌋₊ *
        (((n : ℝ) + 1) ^ s + 1) ^ ⌈2 * r ^ (-(s : ℤ))⌉₊ := by
    apply one_le_mul_of_one_le_of_one_le
    · exact one_le_pow₀ (by linarith)
    · exact one_le_pow₀ (by have := pow_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity) s; linarith)
  change Real.log (max 1 (sourceTestCount n r s : ℝ)) ≤ _
  have hmain := Real.log_le_log (show 0 < max 1 (sourceTestCount n r s : ℝ) by positivity)
    (max_le hlarge hcountR)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hmain
  have hfirst := mul_le_mul ha hlogplus (Real.log_nonneg (by linarith))
    (Real.rpow_nonneg hn0.le ((2 : ℝ) / 3))
  have hsecond := mul_le_mul_of_nonneg_left hbase
    (show 0 ≤ (⌈2 * r ^ (-(s : ℤ))⌉₊ : ℝ) by positivity)
  have hks := mul_le_mul hk hs (by positivity : (0 : ℝ) ≤ (s : ℝ) + 1)
    (by positivity : 0 ≤ 3 * (n : ℝ) ^ ((1 : ℝ) / 100))
  have hsecond' := mul_le_mul_of_nonneg_right hks (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hlog0)
  change Real.log (max 1 (sourceTestCount n r s : ℝ)) ≤
    100 * ((n : ℝ) ^ ((2 : ℝ) / 3) * Real.log n +
      (n : ℝ) ^ ((1 : ℝ) / 100) * (Real.log n) ^ 2)
  nlinarith [mul_nonneg (Real.rpow_nonneg hn0.le ((2 : ℝ) / 3)) hlog0,
    mul_nonneg (Real.rpow_nonneg hn0.le ((1 : ℝ) / 100)) (sq_nonneg (Real.log n))]

end Papers.OaiGraphDecompositionsIntegral
