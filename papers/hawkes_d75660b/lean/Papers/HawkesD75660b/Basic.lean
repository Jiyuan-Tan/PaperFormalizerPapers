module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.List.Sort
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.PNat.Defs
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.IdentDistrib

/-! Shared parameter atoms, parking classes, count laws, and Borel masses. -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Papers.HawkesD75660b

-- @env: S1
variable (ρ : ℝ≥0) -- @realizes \rho(nonnegative real carrier; subcritical bounds below)

-- @node: ass:subcritical
/-- For [a nonnegative excitation parameter](hyp:ρ), [subcriticality means that the parameter is strictly less than one](goal). -/
def subcritical (ρ : ℝ≥0) : Prop :=
  ρ < 1 -- @realizes \rho(strict upper bound one)

-- @node: def:markovian-kernel
/-- For [a nonnegative excitation parameter](hyp:ρ) and [a nonnegative elapsed time](hyp:t), [the excitation kernel is the parameter multiplied by the exponential of minus that time](goal).
@realizes g(t maps to rho exp(-t), nonnegative input and output)
@realizes t(nonnegative time argument) -/
def markovianKernel (ρ : ℝ≥0) (t : ℝ≥0) : ℝ≥0 :=
  ρ * Real.toNNReal (Real.exp (-(t : ℝ)))

/-- For [a nonnegative parameter](hyp:ρ) and [a nonnegative integer size](hyp:j), [the Borel mass](goal) is [zero at size zero](step:1) and [otherwise the exponential of minus parameter times size, multiplied by parameter times size raised to size minus one, divided by the factorial of size](step:2). -/
def borelMass (ρ : ℝ≥0) (j : ℕ) : ℝ :=
  if j = 0 then 0 else
    Real.exp (-(ρ : ℝ) * j) * ((ρ : ℝ) * j) ^ (j - 1) / Nat.factorial j

/-- For [a nonnegative parameter](hyp:ρ), [the Borel measure assigns to each nonnegative integer its Borel mass, converted to a nonnegative weight, by summing weighted point masses](goal). -/
def borelMeasure (ρ : ℝ≥0) : Measure ℕ :=
  Measure.sum (fun j => ENNReal.ofReal (borelMass ρ j) • Measure.dirac j)

-- @node: ass:meanidthm1-borel
/-- For [a nonnegative Borel parameter](hyp:ρ), [a measure on an auxiliary sample space](hyp:Q), and [a nonnegative integer valued size variable on that space](hyp:B), [the auxiliary Borel law condition says that the variable has the Borel distribution with that parameter under that measure](goal). -/
def auxiliaryBorelLaw {ΩB : Type*} [MeasurableSpace ΩB]
    (ρ : ℝ≥0) (Q : Measure ΩB)
    (B : ΩB → ℕ) : Prop := -- @realizes B(Nat variable; positive Borel support via HasLaw)
  HasLaw B (borelMeasure ρ) Q

-- @env: S2
variable (m : ℕ) -- @realizes m(Nat length or stage; bounds in the named atoms)
    (n : ℕ) -- @realizes n(Nat length; positive in the named atoms)

/-- For [a vector length](hyp:m), [a preference vector assigns a positive integer preference to each position, with no upper bound on preferences](goal). -/
abbrev PreferenceVector (m : ℕ) := Fin m → ℕ+ -- @realizes \pi(positive-integer vector carrier)

/-- For [a number of coordinates](hyp:n), [a count vector assigns a nonnegative integer count to each coordinate](goal). -/
abbrev CountVector (n : ℕ) := Fin n → ℕ -- @realizes \kappa(Nat vector carrier)
  -- @realizes k_i(realized Nat coordinates)

/-- For [a vector of positive integer preferences](hyp:π), [the sorted preferences are the list of its entries in nondecreasing order, retaining all multiplicities](goal).
@realizes \pi_{(i)}(positive sorted coordinates retaining multiplicity) -/
def sortedPreferences {m : ℕ} (π : PreferenceVector m) : List ℕ :=
  (List.ofFn (fun i => (π i : ℕ))).mergeSort (fun a b => a ≤ b)

-- @node: ass:gpfdef1-parameters
/-- For [a parking length](hyp:m) and [a preference alphabet length](hyp:n), [the generalized parking parameter condition](goal) requires [a strictly positive parking length](step:1), [a strictly positive alphabet length](step:2), and [a parking length no greater than the alphabet length](step:3). -/
def generalizedParkingParameters (m n : ℕ) : Prop :=
  0 < m ∧ -- @realizes m(positive parking length)
  0 < n ∧ -- @realizes n(positive preference alphabet length)
  m ≤ n -- @realizes m(length at most n)

-- @node: ass:gpfdef1-order
/-- For [a preference alphabet length](hyp:n) and [a vector of positive integer preferences](hyp:π), [the generalized parking order condition requires each sorted preference to be at most the alphabet length minus the vector length, using nonnegative integer subtraction, plus its position counted from one](goal). -/
def generalizedParkingOrder {m : ℕ} (n : ℕ) (π : PreferenceVector m) : Prop :=
  ∀ a : Fin m, (sortedPreferences π)[a.val]?.getD 0 ≤ n - m + (a.val + 1)
  -- @realizes \pi_{(i)}(sorted entry at index i at most n-m+i)
  -- @realizes i(positive order index a+1)

-- @node: def:gpfdef1
/-- For [a preference alphabet length](hyp:n) and [a preference vector](hyp:π), [the generalized parking function property](goal) requires [positive vector and alphabet lengths with vector length at most alphabet length](step:1) and [each sorted preference bounded by alphabet length minus vector length plus its position counted from one](step:2). -/
structure GeneralizedParkingFunction {m : ℕ} (n : ℕ) (π : PreferenceVector m) : Prop where
  parameters : generalizedParkingParameters m n
  order : generalizedParkingOrder n π

-- @node: ass:classic-parking-square
/-- For [a parking length](hyp:m) and [a preference alphabet length](hyp:n), [the classic square condition says that the two lengths are equal](goal). -/
def classicParkingSquare (m n : ℕ) : Prop := m = n -- @realizes m(classic length equals n)

-- @node: def:classic-parking-function
/-- For [a preference alphabet length](hyp:n) and [a preference vector](hyp:π), [the classic parking function property](goal) requires [positive vector and alphabet lengths with vector length at most alphabet length](step:1), [the generalized sorted preference bounds](step:2), and [equality of the vector and alphabet lengths](step:3). -/
structure ClassicParkingFunction {m : ℕ} (n : ℕ) (π : PreferenceVector m) : Prop where
  parameters : generalizedParkingParameters m n -- @realizes m(0<m≤n) @realizes n(0<n)
  order : generalizedParkingOrder n π
  square : classicParkingSquare m n

/-- For [a vector of nonnegative integer counts](hyp:k) and [a nonnegative prefix length](hyp:i), [the prefix count is the sum of entries whose positions, counted from zero, are less than that length](goal).
@realizes k_i^+(realized prefix sum including coordinate zero)
@realizes i(nonnegative prefix length; meaningful coordinates have i <= n) -/
def prefixCount {n : ℕ} (k : CountVector n) (i : ℕ) : ℕ :=
  ∑ a : Fin n, if a.val < i then k a else 0

-- @node: ass:prefs-total
/-- For [a count vector](hyp:κ), [the preference total condition says that the sum of its counts equals its number of coordinates](goal). -/
def preferenceTotal {n : ℕ} (κ : CountVector n) : Prop :=
  ∑ a, κ a = n -- @realizes \kappa(count coordinates have total n)
  -- @realizes k_i(full realized counts total n)

-- @node: ass:prefs-prefix
/-- For [a count vector](hyp:κ), [the preference prefix condition says that every prefix of positive length at most the vector length has total count at least its length](goal). -/
def preferencePrefix {n : ℕ} (κ : CountVector n) : Prop :=
  ∀ i : ℕ, 1 ≤ i → i ≤ n → i ≤ prefixCount κ i
  -- @realizes \kappa(each positive prefix dominates its length)
  -- @realizes k_i^+(prefix lower bounds on supported counts)

-- @node: def:prefs
/-- For [a count vector](hyp:κ), [the preference counts property](goal) requires [total count equal to the vector length](step:1) and [total count in every positive prefix at least the prefix length](step:2). -/
structure PreferenceCounts {n : ℕ} (κ : CountVector n) : Prop where
  total : preferenceTotal κ
  «prefix» : preferencePrefix κ

-- @node: ass:prefs-cumulative-order
/-- For [an integer valued vector](hyp:c), [the cumulative order condition](goal) requires [each entry to lie between one and the vector length, inclusively](step:1) and [the entries to be nondecreasing](step:2). -/
def cumulativeOrder {n : ℕ} (c : Fin n → ℤ) : Prop :=
  (∀ a, 1 ≤ c a ∧ c a ≤ n) ∧ -- @realizes \kappa^+(integer coordinates between one and n)
  Monotone c -- @realizes \kappa^+(nondecreasing cumulative coordinates)

-- @node: ass:prefs-cumulative-prefix
/-- For [an integer valued vector](hyp:c), [the cumulative prefix condition says that every entry is at least its position counted from one](goal). -/
def cumulativePrefix {n : ℕ} (c : Fin n → ℤ) : Prop :=
  ∀ a, (a.val + 1 : ℤ) ≤ c a -- @realizes \kappa^+(positive index lower bound)

-- @node: def:prefs-cumulative
/-- For [an integer valued vector](hyp:c), [the cumulative preference counts property](goal) requires [nondecreasing entries between one and the vector length, inclusively](step:1) and [each entry to be at least its position counted from one](step:2). -/
structure CumulativePreferenceCounts {n : ℕ} (c : Fin n → ℤ) : Prop where
  order : cumulativeOrder c
  «prefix» : cumulativePrefix c

-- @node: def:prefs-cumulative-map
/-- For [a vector of nonnegative integer counts](hyp:κ), [the cumulative preference vector has, at each position, the sum of counts up to and including that position, expressed as an integer](goal).
@realizes \kappa^+(integer-valued vector of the positive prefix sums) -/
def cumulativePreferenceCounts {n : ℕ} (κ : CountVector n) : Fin n → ℤ :=
  fun a => prefixCount κ (a.val + 1)

-- @node: def:preference-count-map
/-- For [a number of preference categories](hyp:n) and [a vector of positive integer preferences](hyp:π), [the preference count vector records, for each category counted from one, the number of preferences equal to that category](goal).
@realizes \kappa(the count vector computed from parking preferences)
@realizes \ell(positive preference position represented by Fin m index plus one) -/
def preferenceCountsOfParking {m : ℕ} (n : ℕ) (π : PreferenceVector m) : CountVector n :=
  fun a => (Finset.univ.filter (fun l => (π l : ℕ) = a.val + 1)).card

open Classical in
-- @node: def:kappa-dist
/-- For [a count vector length](hyp:n) and [a count vector of that length](hyp:k), [the preference count mass](goal) is [the factorial of the length divided by the product of the coordinate factorials and the length plus one raised to the length minus one, when the total count equals the length and every positive prefix has count at least its length](step:1), and [zero otherwise](step:2). -/
def preferenceCountMass (n : ℕ) (k : CountVector n) : ℝ :=
  if PreferenceCounts k then
    (Nat.factorial n : ℝ) / ((n + 1 : ℝ) ^ (n - 1) * ∏ a, (Nat.factorial (k a) : ℝ))
  else 0

/-- For [a count vector length](hyp:n), [the preference count measure is the finite sum of point masses at all count vectors with entries between zero and that length, weighted by their preference count masses converted to nonnegative weights](goal). -/
def preferenceCountMeasure (n : ℕ) : Measure (CountVector n) :=
  ∑ k : Fin n → Fin (n + 1),
    ENNReal.ofReal (preferenceCountMass n (fun a => (k a).val)) •
      Measure.dirac (fun a => (k a).val)

-- @node: ass:kappacpmf1-index
/-- For [a count vector length](hyp:n), [the index condition for the count probability mass formula requires that length to be strictly positive](goal). -/
def kappaCPMFIndex (n : ℕ) : Prop := 0 < n -- @realizes n(positive fixed count length)

-- @node: ass:meanrecur1-index
/-- For [a count vector length](hyp:n), [the index condition for the mean recurrence requires that length to be strictly positive](goal). -/
def meanRecurrenceIndex (n : ℕ) : Prop := 0 < n

-- @node: ass:meanrecursolve1-index
/-- For [a count vector length](hyp:n) and [a nonnegative recurrence stage](hyp:m), [the index condition for the recurrence solution](goal) requires [a strictly positive length](step:1) and [a stage strictly below that length](step:2). -/
def meanRecurrenceSolutionIndex (n m : ℕ) : Prop :=
  0 < n ∧ m < n -- @realizes m(stage from zero through n-1)

-- @node: ass:kappacpmf1-law
/-- For [a measure on the sample space](hyp:P) and [a random count vector](hyp:κ), [the law condition for the count probability mass formula says that the vector has the preference count distribution under that measure](goal). -/
def kappaCPMFLaw {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (κ : Ω → CountVector n) : Prop := HasLaw κ (preferenceCountMeasure n) P

-- @node: ass:meanrecur1-law
/-- For [a measure on the sample space](hyp:P) and [a random count vector](hyp:κ), [the mean recurrence law condition says that the vector has the preference count distribution under that measure](goal). -/
def meanRecurrenceLaw {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (κ : Ω → CountVector n) : Prop := HasLaw κ (preferenceCountMeasure n) P

-- @node: ass:meanrecursolve1-law
/-- For [a measure on the sample space](hyp:P) and [a random count vector](hyp:κ), [the recurrence solution law condition says that the vector has the preference count distribution under that measure](goal). -/
def meanRecurrenceSolutionLaw {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (κ : Ω → CountVector n) : Prop := HasLaw κ (preferenceCountMeasure n) P

-- @node: ass:pin-2
/-- [The natural count domain convention says that the integers obtained from nonnegative integers are exactly the integers greater than or equal to zero](goal). -/
def naturalCountDomainConvention : Prop := Set.range (Int.ofNat : ℕ → ℤ) = Set.Ici 0

-- @node: ass:pin-5
/-- [The zero count convention says that the integers obtained from nonnegative integers are exactly the integers greater than or equal to zero](goal). -/
def zeroCountConvention : Prop := Set.range (Int.ofNat : ℕ → ℤ) = Set.Ici 0

-- @node: ass:pin-3
/-- For [a count vector length](hyp:n) and [a nonnegative solution stage](hyp:m), [the solution index convention](goal) requires [a strictly positive length](step:1) and [a stage strictly below that length](step:2). -/
def solutionIndexConvention (n m : ℕ) : Prop := 0 < n ∧ m < n

-- @node: def:meanrecur1-zero
/-- For [a count vector](hyp:κ), [the zeroth cumulative count is the sum over its empty prefix, hence zero](goal). -/
def zeroCumulativeCount {n : ℕ} (κ : CountVector n) : ℕ := prefixCount κ 0

-- @env: S4
variable (j : ℕ) -- @realizes j(nonnegative harmonic index; positive indices in the displayed sum)

-- @node: def:meanidthm1-harmonic
/-- For [a nonnegative integer index](hyp:j), [the harmonic number is the sum of the reciprocals of the positive integers up to that index, expressed as a real number, with value zero at index zero](goal).
@realizes \mathsf{H}_j(Real cast of the rational harmonic sum)
@realizes j(index of the harmonic number) -/
def harmonicNumber (j : ℕ) : ℝ := (harmonic j : ℝ)

end Papers.HawkesD75660b
