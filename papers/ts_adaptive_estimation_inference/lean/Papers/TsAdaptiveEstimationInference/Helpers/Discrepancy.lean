module
public import Papers.TsAdaptiveEstimationInference.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Floor.Ring
/-! Finite geometric grids and the discrepancy search. -/
@[expose] public section
set_option linter.style.longLine false
namespace Papers.TsAdaptiveEstimationInference
noncomputable section
open MeasureTheory Filter
open scoped Topology
/-- For [a proposition](hyp:p), [a classical decision determines whether it is true or false](goal). -/
local instance classicalDecision (p : Prop) : Decidable p := Classical.propDecidable p
/-- [Classical equality decides whether any two real numbers are equal](goal). -/
local instance : DecidableEq ℝ := Classical.decEq ℝ

/-- For [a geometric grid factor ρ](hyp:ρ) and [sample size n](hyp:n), the
[terminal index](goal) is the nonnegative integer ceiling of log(2n²) divided by log(1/ρ). -/
noncomputable def terminalIndex (ρ : ℝ) (n : ℕ) : ℕ :=
  ⌈Real.log (2 * (n : ℝ) ^ 2) / Real.log (1 / ρ)⌉₊
  -- @realizes K_n(ceiling of the logarithmic terminal index)

/-- For [a geometric grid factor ρ](hyp:ρ) and [index k](hyp:k), the
[grid penalty](goal) is twice ρ raised to the k-th power. -/
def gridValue (ρ : ℝ) (k : ℕ) : ℝ := 2 * ρ ^ k
  -- @realizes \lambda_k(geometric grid parameter)
  -- @realizes \lambda_0(initial value 2)

-- @node: def:grid
/-- For [a grid factor ρ](hyp:ρ) and [sample size n](hyp:n), the
[finite regularization grid](goal) consists of the penalties 2ρᵏ from index zero
through the terminal index, inclusive. -/
noncomputable def regGrid (ρ : ℝ) (n : ℕ) : Finset ℝ :=
  (Finset.range (terminalIndex ρ n + 1)).image (gridValue ρ)
  -- @realizes \Lambda_n(finite geometric regularization grid)

/-- The [grid-domain condition](goal) requires [the geometric factor ρ](hyp:ρ)
to be at least one half and strictly less than one. -/
def GridDomain (ρ : ℝ) : Prop :=
  ρ ∈ Set.Ico (1 / 2 : ℝ) 1 -- @realizes \lambda_k(1/2 <= rho < 1 forces 0 < 2*rho^k <= 2 for natural k)
  -- @realizes \Lambda_n(search factor restricts the geometric grid to (0,2])

-- @node: def:cr-deepiv-confidence
/-- For [a grid factor ρ](hyp:ρ), [total confidence-error budget ξ](hyp:ξ),
and [sample size n](hyp:n), the [per-grid confidence-error allocation](goal)
is ξ divided by the terminal index plus one. -/
noncomputable def gridConfidence (ρ ξ : ℝ) (n : ℕ) : ℝ :=
  ξ / (terminalIndex ρ n + 1 : ℕ)
  -- @realizes \eta_n(per-grid confidence allocation)

-- @node: def:iter-confidence
/-- For [a grid factor ρ](hyp:ρ), [total confidence-error budget ξ](hyp:ξ),
[sample size n](hyp:n), and [iteration count t](hyp:t), the
[per-iteration, per-grid confidence-error allocation](goal) is ξ divided by
the product of t and the number of grid indices (the terminal index plus one). -/
noncomputable def iterGridConfidence (ρ ξ : ℝ) (n t : ℕ) : ℝ :=
  ξ / (t * (terminalIndex ρ n + 1) : ℕ)
  -- @realizes \eta_{n,t}(per-iteration-grid confidence allocation)

-- @node: def:discrepancy
/-- For [a grid factor ρ](hyp:ρ), [sample size n](hyp:n),
[discrepancy function D](hyp:D), and [noise bound A](hyp:A), the
[discrepancy index](goal) is the first index through the terminal index where
D is at most three halves of A at the grid penalty; if no such index exists,
it is the terminal index. -/
noncomputable def discrepancyIndex (ρ : ℝ) (n : ℕ) (D A : ℝ → ℝ) : ℕ :=
  if e : ∃ k, k ≤ terminalIndex ρ n ∧ D (gridValue ρ k) ≤ 3 / 2 * A (gridValue ρ k)
  then Nat.find e else terminalIndex ρ n

/-- For [a grid factor ρ](hyp:ρ), [sample size n](hyp:n),
[discrepancy function D](hyp:D), and [noise bound A](hyp:A), the
[selected penalty](goal) is the grid penalty at the discrepancy index,
including its terminal fallback when no penalty is accepted. -/
noncomputable def selectedPenalty (ρ : ℝ) (n : ℕ) (D A : ℝ → ℝ) : ℝ :=
  gridValue ρ (discrepancyIndex ρ n D A)
  -- @realizes \lambda_{\mathrm{dp}}(first accepted parameter or terminal fallback)

/-- For [a grid factor ρ](hyp:ρ), [sample size n](hyp:n),
[discrepancy function D](hyp:D), and [noise bound A](hyp:A),
[grid acceptance](goal) means there is an index that [does not exceed the
terminal index](step:1) and [has discrepancy at most three halves of the noise
bound at its grid penalty](step:2). -/
noncomputable def Accepts (ρ : ℝ) (n : ℕ) (D A : ℝ → ℝ) : Prop :=
  ∃ k ≤ terminalIndex ρ n, D (gridValue ρ k) ≤ 3 / 2 * A (gridValue ρ k)

-- @node: def:discrepancy-principle
/-- For [a grid factor ρ](hyp:ρ), [penalty λ](hyp:lam),
[discrepancy function D](hyp:D), and [noise bound A](hyp:A), the
[adjacent discrepancy relation](goal) requires [D at λ to be at most three
halves of A at λ](step:1), [D at λ/ρ to exceed three halves of A there](step:2),
[λ to be at most λ/ρ](step:3), and [λ/ρ to be at most twice λ](step:4). -/
def AdjacentDiscrepancyRelation (ρ lam : ℝ) (D A : ℝ → ℝ) : Prop :=
  D lam ≤ 3 / 2 * A lam ∧ 3 / 2 * A (lam / ρ) < D (lam / ρ) ∧
  lam ≤ lam / ρ ∧ lam / ρ ≤ 2 * lam

-- @node: def:common-dp-bias
/-- For [a bias coefficient](hyp:Cb), [power exponent q](hyp:q), and
[penalty λ](hyp:lam), the [generic bias bound](goal) is the coefficient times λ to the power q. -/
noncomputable def genericBias (Cb q lam : ℝ) : ℝ := Cb * lam ^ q
  -- @realizes B_n(power bias bound)

-- @node: ass:common-dp-noise-domain
/-- For [a grid factor ρ](hyp:ρ), [sample size n](hyp:n), and
[noise bound A](hyp:A), [grid nonnegativity](goal) means that A is nonnegative
at every penalty in the regularization grid. -/
def NoiseLevelNonneg (ρ : ℝ) (n : ℕ) (A : ℝ → ℝ) : Prop :=
  ∀ lam ∈ regGrid ρ n, 0 ≤ A lam
  -- @realizes A_n(nonnegative on the grid)

-- @node: ass:common-dp-stability-domain
/-- For [a set S of stable penalties](hyp:S), the [stability-domain restriction](goal)
requires every member of S to be strictly positive and at most two. -/
def StabilityRegionSubset (S : Set ℝ) : Prop := -- @realizes \mathcal S_n(carrier is a set of real penalties)
  S ⊆ Set.Ioc 0 2 -- @realizes \mathcal S_n(stability domain inside (0,2])


-- @node: ass:common-dp-parameters
/-- For [comparison constants C_A](hyp:CA) and [C_V](hyp:CV),
[bias coefficient C_b](hyp:Cb), [noise exponent γ](hyp:γ), and
[bias exponent q](hyp:q), the [generic discrepancy parameter conditions](goal)
require [C_A to be positive](step:1), [C_V to be positive](step:2),
[C_b to be positive](step:3), [γ to be strictly positive and at most one](step:4),
and [q to exceed one](step:5). -/
def GenericDPParameters (CA CV Cb γ q : ℝ) : Prop :=
  0 < CA ∧ -- @realizes C_A(positive comparison constant)
  0 < CV ∧ -- @realizes C_V(positive comparison constant)
  0 < Cb ∧ -- @realizes C_b(positive bias coefficient)
  γ ∈ Set.Ioc 0 1 ∧ -- @realizes \gamma(exponent in the interval from zero to one)
  1 < q -- @realizes q(scalar bias exponent greater than one)

-- @node: ass:common-dp-event-comparisons
/-- For [a measure P](hyp:P), [linear operator T](hyp:T),
[target h₀](hyp:h₀), [grid factor ρ](hyp:ρ), [failure budget ξ](hyp:ξ),
[prediction comparison constant C_A](hyp:CA), [estimation comparison constant C_V](hyp:CV),
[bias coefficient C_b](hyp:Cb), [noise exponent γ](hyp:γ), [bias exponent q](hyp:q),
[sample size n](hyp:n), [stable penalty set S](hyp:S), [event E](hyp:E),
[penalty-indexed candidate estimators](hyp:candidate), [sample-dependent discrepancy D](hyp:D),
and [noise bound A](hyp:A), the [event comparison conditions](goal) require
[E to be measurable](step:1), [its real-valued measure to be at least 1 − ξ](step:2),
and [on E, at every grid penalty λ in S, the discrepancy to be bounded by
A(λ) + C_b λᵠ, the squared prediction error to be bounded by C_A times
the sum of the discrepancy and A(λ), and the squared estimation error to be bounded by
C_V times the sum of that same quantity divided by λ and its γ-th power](step:3). -/
def GenericEventComparisons {Ω H Q : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedAddCommGroup Q] [NormedSpace ℝ H]
    [NormedSpace ℝ Q] (P : Measure Ω) (T : H →L[ℝ] Q) (h₀ : H)
    (ρ ξ CA CV Cb γ q : ℝ) (n : ℕ) (S : Set ℝ) (E : Set Ω)
    (candidate : ℝ → Ω → H) (D : Ω → H → ℝ) (A : ℝ → ℝ) : Prop :=
  MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧
  ∀ ω ∈ E, ∀ lam ∈ regGrid ρ n, lam ∈ S →
    D ω (candidate lam ω) ≤ A lam + genericBias Cb q lam ∧
    ‖T (candidate lam ω - h₀)‖ ^ 2 ≤ CA * (D ω (candidate lam ω) + A lam) ∧
    ‖candidate lam ω - h₀‖ ^ 2 ≤ CV *
      ((D ω (candidate lam ω) + A lam) / lam + (D ω (candidate lam ω) + A lam) ^ γ)

-- @node: ass:common-dp-stable-segment
/-- For [a grid factor ρ](hyp:ρ), [sample size n](hyp:n),
[stable penalty set S](hyp:S), and [oracle penalty λ°](hyp:lamo),
[oracle-segment stability](goal) requires [λ° to belong to the grid](step:1)
and [every grid penalty between λ° and two, inclusive, to belong to S](step:2). -/
def OracleSegmentStable (ρ : ℝ) (n : ℕ) (S : Set ℝ) (lamo : ℝ) : Prop :=
  lamo ∈ regGrid ρ n ∧ (↑(regGrid ρ n) ∩ Set.Icc lamo 2 : Set ℝ) ⊆ S
  -- @realizes \lambda^\circ(oracle point in the stable grid segment)

-- @node: ass:common-dp-monotonicity
/-- For [a grid factor ρ](hyp:ρ), [sample size n](hyp:n),
[noise bound A](hyp:A), and [oracle penalty λ°](hyp:lamo),
[noise monotonicity on the oracle segment](goal) means that A is nonincreasing
as the penalty increases among grid points between λ° and two, inclusive. -/
def NoiseLevelAntitoneOnSegment (ρ : ℝ) (n : ℕ) (A : ℝ → ℝ) (lamo : ℝ) : Prop :=
  AntitoneOn A (↑(regGrid ρ n) ∩ Set.Icc lamo 2)

-- @node: ass:common-dp-oracle-crossing
/-- For [a noise bound A](hyp:A), [bias coefficient C_b](hyp:Cb),
[bias exponent q](hyp:q), and [oracle penalty λ°](hyp:lamo), the
[oracle crossing condition](goal) requires C_b times λ° to the power q to be
at most half of A at λ°. -/
noncomputable def OracleCrossing (A : ℝ → ℝ) (Cb q lamo : ℝ) : Prop :=
  genericBias Cb q lamo ≤ 1 / 2 * A lamo

-- @node: ass:pin-142
/-- For [a linear operator T](hyp:T), [target h₀](hyp:h₀),
[grid factor ρ](hyp:ρ), [noise exponent γ](hyp:γ), [oracle penalty λ°](hyp:lamo),
[error constant C](hyp:C), [sample size n](hyp:n), [event E](hyp:E),
[penalty-indexed candidate estimators](hyp:candidate), [sample-dependent discrepancy D](hyp:D),
and [noise bound A](hyp:A), the [generic discrepancy guarantee on E](goal)
requires, for every outcome in E, [some grid penalty to be accepted](step:1),
[λ° to have an index through the terminal index that is no smaller than the
selected discrepancy index](step:2), [the selected penalty to be at least λ°](step:3),
[the selected estimator's squared prediction error to be at most C A(λ°)](step:4),
and [its squared estimation error to be at most C times the sum of A(λ°)/λ°
and A(λ°) to the power γ](step:5). -/
def PinGenericDPOnEvent {Ω H Q : Type*} [NormedAddCommGroup H]
    [NormedAddCommGroup Q] [NormedSpace ℝ H] [NormedSpace ℝ Q]
    (T : H →L[ℝ] Q) (h₀ : H) (ρ γ lamo C : ℝ) (n : ℕ) (E : Set Ω)
    (candidate : ℝ → Ω → H) (D : Ω → H → ℝ) (A : ℝ → ℝ) : Prop :=
  ∀ ω ∈ E,
    Accepts ρ n (fun lam => D ω (candidate lam ω)) A ∧
    (∃ kOracle ≤ terminalIndex ρ n, lamo = gridValue ρ kOracle ∧
      discrepancyIndex ρ n (fun lam => D ω (candidate lam ω)) A ≤ kOracle) ∧
    lamo ≤ selectedPenalty ρ n (fun lam => D ω (candidate lam ω)) A ∧
    ‖T (candidate (selectedPenalty ρ n (fun lam => D ω (candidate lam ω)) A) ω - h₀)‖ ^ 2 ≤ C * A lamo ∧
    ‖candidate (selectedPenalty ρ n (fun lam => D ω (candidate lam ω)) A) ω - h₀‖ ^ 2 ≤
      C * (A lamo / lamo + A lamo ^ γ)

/-- For [a grid factor ρ](hyp:ρ), [sample size n](hyp:n), and [radius r](hyp:r),
the [oracle index](goal) is the first index through the terminal index whose
grid penalty is at most r, or the terminal index if no such index exists. -/
noncomputable def oracleIndex (ρ : ℝ) (n : ℕ) (r : ℝ) : ℕ :=
  if e : ∃ k, k ≤ terminalIndex ρ n ∧ gridValue ρ k ≤ r then Nat.find e
  else terminalIndex ρ n

/-- For [a grid factor ρ](hyp:ρ), [sample size n](hyp:n), and [radius r](hyp:r),
the [oracle penalty](goal) is the grid value at the oracle index, using the
terminal penalty when the grid never reaches r. -/
noncomputable def oraclePoint (ρ : ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  gridValue ρ (oracleIndex ρ n r)

-- @node: oraclePoint_first_crossing
/-- If [the terminal grid penalty is at most the radius r](hyp:hterminal),
[there is an index through the terminal index whose penalty is at most r,
all earlier penalties exceed r, and the oracle penalty equals the penalty at
that index](goal). -/
lemma oraclePoint_first_crossing (ρ r : ℝ) (n : ℕ)
    (hterminal : gridValue ρ (terminalIndex ρ n) ≤ r) :
    ∃ k ≤ terminalIndex ρ n, gridValue ρ k ≤ r ∧
      (∀ j < k, r < gridValue ρ j) ∧ oraclePoint ρ n r = gridValue ρ k := by
  classical
  let h : ∃ k, k ≤ terminalIndex ρ n ∧ gridValue ρ k ≤ r :=
    ⟨terminalIndex ρ n, le_rfl, hterminal⟩
  refine ⟨Nat.find h, (Nat.find_spec h).1, (Nat.find_spec h).2, ?_, ?_⟩
  · intro j hj
    apply lt_of_not_ge
    intro hle
    exact Nat.find_min h hj ⟨hj.le.trans (Nat.find_spec h).1, hle⟩
  · simp [oraclePoint, oracleIndex, h]

-- @node: oraclePoint_radius_bounds
/-- If [the grid factor ρ is at least one half and strictly less than one](hyp:hρ),
[the radius r is at most two](hyp:hr), and [the terminal grid penalty is at
most r](hyp:hterminal), then [the oracle penalty belongs to the grid and lies
between ρr and r, inclusive](goal). -/
lemma oraclePoint_radius_bounds (ρ r : ℝ) (n : ℕ) (hρ : GridDomain ρ)
    (hr : r ≤ 2) (hterminal : gridValue ρ (terminalIndex ρ n) ≤ r) :
    oraclePoint ρ n r ∈ regGrid ρ n ∧
      ρ * r ≤ oraclePoint ρ n r ∧ oraclePoint ρ n r ≤ r := by
  obtain ⟨k, hk, hkr, hfirst, heq⟩ := oraclePoint_first_crossing ρ r n hterminal
  rw [heq]
  refine ⟨Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩, ?_, hkr⟩
  have hρpos : 0 < ρ := by linarith [hρ.1]
  cases k with
  | zero =>
      have hmul := mul_le_mul_of_nonneg_left hr hρpos.le
      change ρ * r ≤ 2 * ρ ^ 0
      simp only [pow_zero, mul_one]
      linarith [hρ.2]
  | succ k =>
      have hprev := hfirst k (Nat.lt_succ_self k)
      have hmul := mul_le_mul_of_nonneg_left hprev.le hρpos.le
      simpa only [gridValue, pow_succ, mul_comm, mul_left_comm, mul_assoc] using hmul

-- @node: terminalGrid_le
/-- If [the grid factor ρ is at least one half and strictly less than one](hyp:hρ)
and [the sample size n is positive](hyp:hn), then [the terminal grid penalty
is at most the reciprocal of n squared](goal). -/
lemma terminalGrid_le (ρ : ℝ) (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1)
    (n : ℕ) (hn : 0 < n) : gridValue ρ (terminalIndex ρ n) ≤ 1 / (n : ℝ) ^ 2 := by
  have hr : 0 < ρ := by linarith [hρ.1]
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hi : 1 < 1 / ρ := (lt_div_iff₀ hr).2 (by simpa using hρ.2)
  have hl : 0 < Real.log (1 / ρ) := Real.log_pos hi
  have hc := Nat.le_ceil (Real.log (2 * (n : ℝ) ^ 2) / Real.log (1 / ρ))
  have hlog : Real.log (2 * (n : ℝ) ^ 2) ≤
      (terminalIndex ρ n : ℝ) * Real.log (1 / ρ) :=
    (div_le_iff₀ hl).1 hc
  have hp : 2 * (n : ℝ) ^ 2 ≤ (1 / ρ) ^ terminalIndex ρ n := by
    apply (Real.log_le_log_iff (by positivity) (by positivity)).1
    simpa only [Real.log_pow] using hlog
  rw [div_pow, one_pow] at hp
  have hpow : 0 < ρ ^ terminalIndex ρ n := pow_pos hr _
  have hm := (le_div_iff₀ hpow).1 hp
  unfold gridValue
  apply (le_div_iff₀ (sq_pos_of_pos hn')).2
  nlinarith only [hm]

-- @node: terminalIndex_log_bound
/-- If [the grid factor ρ is at least one half and strictly less than one](hyp:hρ),
then [there is a positive constant C such that, for every sample size n at
least two, the terminal index plus one is at most C times the natural
logarithm of n](goal). -/
lemma terminalIndex_log_bound (ρ : ℝ) (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) :
    ∃ C > 0, ∀ n : ℕ, 2 ≤ n →
      (terminalIndex ρ n + 1 : ℕ) ≤ C * Real.log n := by
  have hr : 0 < ρ := by linarith [hρ.1]
  have hi : 1 < 1 / ρ := (lt_div_iff₀ hr).2 (by simpa using hρ.2)
  have hl : 0 < Real.log (1 / ρ) := Real.log_pos hi
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨3 / Real.log (1 / ρ) + 2 / Real.log 2, by positivity, ?_⟩
  intro n hn
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hln : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn2
  have harg : 1 ≤ 2 * (n : ℝ) ^ 2 := by nlinarith
  have hc := Nat.ceil_lt_add_one
    (div_nonneg (Real.log_nonneg harg) hl.le)
  change (terminalIndex ρ n : ℝ) <
    Real.log (2 * (n : ℝ) ^ 2) / Real.log (1 / ρ) + 1 at hc
  rw [Real.log_mul (by norm_num) (ne_of_gt (sq_pos_of_pos hn0)), Real.log_pow] at hc
  have hratio : (Real.log 2 + 2 * Real.log n) / Real.log (1 / ρ) ≤
      3 * Real.log n / Real.log (1 / ρ) := by
    apply (div_le_div_iff_of_pos_right hl).2
    linarith
  have htwo : 2 ≤ 2 / Real.log 2 * Real.log n := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hl2).2
    linarith
  push_cast
  rw [add_mul, div_mul_eq_mul_div]
  linarith

-- @node: discrepancyIndex_first_acceptance
/-- If [the grid factor ρ is at least one half and strictly less than one](hyp:hρ)
and [some grid penalty has discrepancy D at most three halves of its noise
bound A](hyp:hAccept), then [the discrepancy index is at most the terminal
index and is either zero or positive with its selected penalty λ satisfying:
D(λ) is at most three halves of A(λ), D(λ/ρ) exceeds three halves of A(λ/ρ),
and λ ≤ λ/ρ ≤ 2λ](goal). -/
lemma discrepancyIndex_first_acceptance (ρ : ℝ) (n : ℕ) (D A : ℝ → ℝ)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hAccept : Accepts ρ n D A) :
    discrepancyIndex ρ n D A ≤ terminalIndex ρ n ∧
      (discrepancyIndex ρ n D A = 0 ∨
        (0 < discrepancyIndex ρ n D A ∧
          AdjacentDiscrepancyRelation ρ (selectedPenalty ρ n D A) D A)) := by
  have hr : 0 < ρ := by linarith [hρ.1]
  let e : ∃ k, k ≤ terminalIndex ρ n ∧
      D (gridValue ρ k) ≤ 3 / 2 * A (gridValue ρ k) := hAccept
  have heq : discrepancyIndex ρ n D A = Nat.find e := by
    unfold discrepancyIndex
    rw [dif_pos e]
  have hs := Nat.find_spec e
  refine ⟨heq ▸ hs.1, ?_⟩
  by_cases hz : discrepancyIndex ρ n D A = 0
  · exact Or.inl hz
  · have hk : 0 < discrepancyIndex ρ n D A := Nat.pos_of_ne_zero hz
    refine Or.inr ⟨hk, ?_⟩
    have hpred : discrepancyIndex ρ n D A - 1 < Nat.find e := by
      rw [← heq]
      omega
    have hreject : 3 / 2 * A (gridValue ρ (discrepancyIndex ρ n D A - 1)) <
        D (gridValue ρ (discrepancyIndex ρ n D A - 1)) := by
      apply lt_of_not_ge
      intro hle
      apply Nat.find_min e hpred
      exact ⟨by rw [← heq] at hs; omega, hle⟩
    have hsucc : discrepancyIndex ρ n D A - 1 + 1 = discrepancyIndex ρ n D A := by omega
    have hstep : gridValue ρ (discrepancyIndex ρ n D A - 1) =
        selectedPenalty ρ n D A / ρ := by
      apply (eq_div_iff hr.ne').2
      unfold selectedPenalty
      conv_rhs => rw [← hsucc]
      simp only [gridValue, pow_succ, mul_assoc]
    have hpos : 0 < selectedPenalty ρ n D A := by
      exact mul_pos (by norm_num) (pow_pos hr _)
    refine ⟨?_, hstep ▸ hreject, ?_, ?_⟩
    · simpa only [selectedPenalty, ← heq] using hs.2
    · apply (le_div_iff₀ hr).2
      nlinarith [hρ.2]
    · apply (div_le_iff₀ hr).2
      nlinarith [hρ.1]

end
end Papers.TsAdaptiveEstimationInference
