module

public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Distributions.Binomial
public import Papers.HawkesD75660b.Helpers.ParkingEnumeration
public import Papers.HawkesD75660b.Helpers.ParkingInitial
public import Papers.HawkesD75660b.Helpers.PrefixEnumeration

/-! Finite-event conditional preference-count laws. -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Papers.HawkesD75660b

/-- For [a count-vector-valued observation κ](hyp:κ), [a prefix length m](hyp:m),
and [a target count vector k](hyp:k), the [prefix event](goal) consists of observations
whose counts agree with k at every position before m. -/
def countPrefixEvent {Ω : Type*} {n : ℕ} (κ : Ω → CountVector n)
    (m : ℕ) (k : CountVector n) : Set Ω :=
  {ω | ∀ a : Fin n, a.val < m → κ ω a = k a}

-- @node: reciprocalProbability_mem
/-- [The reciprocal of r plus one lies between zero and one, inclusive](goal). -/
lemma reciprocalProbability_mem (r : ℕ) :
    1 / ((r : ℝ) + 1) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · positivity
  · apply (div_le_one (by positivity : (0 : ℝ) < r + 1)).2
    exact le_add_of_nonneg_left (Nat.cast_nonneg r)

/-- For [a natural number r](hyp:r), the [reciprocal probability](goal) is one
divided by r plus one, regarded as a number between zero and one. -/
def reciprocalProbability (r : ℕ) : unitInterval :=
  ⟨1 / ((r : ℝ) + 1), reciprocalProbability_mem r⟩

/-- For [a real weight p](hyp:p), the [Bernoulli measure on natural numbers](goal)
assigns the nonnegative part of p to one and the nonnegative part of one minus p to zero. -/
def bernoulliNat (p : ℝ) : Measure ℕ :=
  ENNReal.ofReal p • Measure.dirac 1 + ENNReal.ofReal (1 - p) • Measure.dirac 0

/-- For [a total count n](hyp:n), [a prefix length m](hyp:m), and
[a cumulative count s](hyp:s), the [Bernoulli parameter](goal) is n minus s
divided by the product of n minus m and s minus m plus one. -/
def bernoulliParameter (n m s : ℕ) : ℝ :=
  ((n : ℝ) - s) / (((n : ℝ) - m) * ((s : ℝ) - m + 1))

/-- For [a total count n](hyp:n), [a prefix length m](hyp:m), and
[a cumulative count s](hyp:s), the [auxiliary joint count measure](goal) draws Y
with Bernoulli parameter (n−s)/((n−m)(s−m+1)), then draws X given Y from a
binomial distribution with n−s−Y trials and success probability 1/(n−m+1).
@realizes Y_m(second Nat coordinate, Bernoulli parameter (n-s)/((n-m)(s-m+1)))
@realizes X_m(first Nat coordinate, conditional Bin(n-s-Y,1/(n-m+1))) -/
def auxiliaryCountLaw (n m s : ℕ) : Measure (ℕ × ℕ) :=
  (bernoulliNat (bernoulliParameter n m s)).bind (fun y =>
    (ProbabilityTheory.binomial (n - s - y) (reciprocalProbability (n - m))).map
      (fun x => (x, y)))

-- @node: auxiliaryCountLaw_snd
/-- [The second coordinate of the auxiliary joint count measure has the Bernoulli
measure with parameter (n−s)/((n−m)(s−m+1))](goal). -/
lemma auxiliaryCountLaw_snd (n m s : ℕ) :
    HasLaw Prod.snd (bernoulliNat (bernoulliParameter n m s))
      (auxiliaryCountLaw n m s) := by
  constructor
  · exact measurable_snd.aemeasurable
  · ext A hA
    rw [Measure.map_apply (by fun_prop) hA, auxiliaryCountLaw,
      Measure.bind_apply (Set.to_countable _).measurableSet
        (measurable_of_countable _).aemeasurable]
    have heq (y : ℕ) :
        ((ProbabilityTheory.binomial (n - s - y) (reciprocalProbability (n - m))).map
          (fun x => (x, y))) (Prod.snd ⁻¹' A) = A.indicator (fun _ => 1) y := by
      rw [Measure.map_apply (by fun_prop) (Set.to_countable _).measurableSet]
      by_cases hy : y ∈ A <;> simp [Set.preimage, hy]
    simp_rw [heq]
    exact lintegral_indicator_one hA

-- @node: auxiliaryCountLaw_fiber
/-- [The auxiliary mass of pairs whose first coordinate lies in A and whose second
coordinate equals y is the Bernoulli mass at y times the binomial mass of A,
with n−s−y trials and success probability 1/(n−m+1)](goal). -/
lemma auxiliaryCountLaw_fiber (n m s y : ℕ) (A : Set ℕ) :
    auxiliaryCountLaw n m s {q | q.1 ∈ A ∧ q.2 = y} =
      bernoulliNat (bernoulliParameter n m s) {y} *
        ProbabilityTheory.binomial (n - s - y) (reciprocalProbability (n - m)) A := by
  classical
  rw [auxiliaryCountLaw,
    Measure.bind_apply (Set.to_countable _).measurableSet
      (measurable_of_countable _).aemeasurable]
  have heq (z : ℕ) :
      ((ProbabilityTheory.binomial (n - s - z) (reciprocalProbability (n - m))).map
        (fun x => (x, z))) {q | q.1 ∈ A ∧ q.2 = y} =
      ({y} : Set ℕ).indicator
        (fun _ => ProbabilityTheory.binomial (n - s - y) (reciprocalProbability (n - m)) A) z := by
    rw [Measure.map_apply (by fun_prop) (Set.to_countable _).measurableSet]
    by_cases hz : z = y
    · subst z
      simp
    · simp [Set.preimage, hz]
  simp_rw [heq]
  rw [lintegral_indicator_const (measurableSet_singleton y), mul_comm]

-- @node: auxiliaryCountLaw_cond_fst
/-- If [the event that the second coordinate equals y has positive auxiliary
mass](hyp:hy), then [conditional on that event, the first coordinate has a binomial
distribution with n−s−y trials and success probability 1/(n−m+1)](goal). -/
lemma auxiliaryCountLaw_cond_fst (n m s y : ℕ)
    (hy : 0 < auxiliaryCountLaw n m s {q | q.2 = y}) :
    HasLaw Prod.fst
      (ProbabilityTheory.binomial (n - s - y) (reciprocalProbability (n - m)))
      (ProbabilityTheory.cond (auxiliaryCountLaw n m s) {q | q.2 = y}) := by
  have hmarg : auxiliaryCountLaw n m s {q | q.2 = y} =
      bernoulliNat (bernoulliParameter n m s) {y} :=
    (auxiliaryCountLaw_snd n m s).measure_eq
      (p := fun z => z = y) (measurableSet_singleton y)
  have hpos : bernoulliNat (bernoulliParameter n m s) {y} ≠ 0 := by
    rw [← hmarg]
    exact ne_of_gt hy
  have hfinite : bernoulliNat (bernoulliParameter n m s) {y} ≠ ∞ := by
    simp only [bernoulliNat, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    finiteness
  constructor
  · exact measurable_fst.aemeasurable
  · ext A hA
    rw [Measure.map_apply (by fun_prop) hA,
      ProbabilityTheory.cond_apply (Set.to_countable _).measurableSet]
    have hset : {q : ℕ × ℕ | q.2 = y} ∩ Prod.fst ⁻¹' A =
        {q | q.1 ∈ A ∧ q.2 = y} := by
      ext q
      exact and_comm
    rw [hset, auxiliaryCountLaw_fiber, hmarg, ← mul_assoc,
      ENNReal.inv_mul_cancel hpos hfinite, one_mul]

/-- For [a total count n](hyp:n), [a prefix length m](hyp:m),
[a cumulative count s](hyp:s), and [a next count k](hyp:k), the
[conditional count mass](goal) is (s+k−m)/(s−m+1) times the binomial coefficient
choosing k from n−s, times (n−m) to the power n−s−k−1 divided by
(n−m+1) to the power n−s−1, using signed integer exponents. -/
def conditionalCountMass (n m s k : ℕ) : ℝ :=
  (((s : ℝ) + k - m) / ((s : ℝ) - m + 1)) * (Nat.choose (n - s) k : ℝ) *
    (((n : ℝ) - m) ^ ((n : ℤ) - (s + k : ℕ) - 1) /
      ((n : ℝ) - m + 1) ^ ((n : ℤ) - s - 1))

/-- If [m is less than n](hyp:hm), [s is at least m](hyp:hms), and
[s is at most n](hyp:hsn), then [the Bernoulli parameter lies between zero and
one, inclusive](goal). -/
-- @node: bernoulliParameter_mem
lemma bernoulliParameter_mem {n m s : ℕ} (hm : m < n)
    (hms : m ≤ s) (hsn : s ≤ n) :
    bernoulliParameter n m s ∈ Set.Icc (0 : ℝ) 1 := by
  have ha : (0 : ℝ) < (n : ℝ) - m := by
    have : (m : ℝ) < n := by exact_mod_cast hm
    linarith
  have hd : (1 : ℝ) ≤ (s : ℝ) - m + 1 := by
    have : (m : ℝ) ≤ s := by exact_mod_cast hms
    linarith
  have hr : (0 : ℝ) ≤ (n : ℝ) - s := by
    have : (s : ℝ) ≤ n := by exact_mod_cast hsn
    linarith
  constructor
  · exact div_nonneg hr (le_of_lt (mul_pos ha (by linarith)))
  · apply (div_le_one (mul_pos ha (by linarith))).2
    have : (m : ℝ) ≤ s := by exact_mod_cast hms
    nlinarith

/-- [The auxiliary mass at coordinate sum v is the Bernoulli parameter times
the binomial mass at v−1 with n−s−1 trials, plus one minus that parameter
times the binomial mass at v with n−s trials; both binomials have success
probability 1/(n−m+1), and the first contribution is zero when v is zero](goal). -/
-- @node: auxiliaryCountLaw_sum_apply
lemma auxiliaryCountLaw_sum_apply (n m s v : ℕ) :
    auxiliaryCountLaw n m s {q | q.1 + q.2 = v} =
      ENNReal.ofReal (bernoulliParameter n m s) *
        (if v = 0 then 0 else
          ProbabilityTheory.binomial (n - s - 1) (reciprocalProbability (n - m)) {v - 1}) +
      ENNReal.ofReal (1 - bernoulliParameter n m s) *
        ProbabilityTheory.binomial (n - s) (reciprocalProbability (n - m)) {v} := by
  rw [auxiliaryCountLaw,
    Measure.bind_apply (Set.to_countable _).measurableSet
      (measurable_of_countable _).aemeasurable]
  simp only [bernoulliNat, lintegral_add_measure, lintegral_smul_measure,
    lintegral_dirac, smul_eq_mul, Nat.sub_zero]
  simp only [Measure.map_apply (measurable_of_countable _)
    (Set.to_countable _).measurableSet]
  have hzero : (fun x : ℕ => (x, 0)) ⁻¹' {q | q.1 + q.2 = v} = {v} := by
    ext x; simp
  rw [hzero]
  by_cases hv : v = 0
  · subst v
    have hone : (fun x : ℕ => (x, 1)) ⁻¹' {q | q.1 + q.2 = 0} = ∅ := by
      ext x; simp
    simp
  · have hone : (fun x : ℕ => (x, 1)) ⁻¹' {q | q.1 + q.2 = v} = {v - 1} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      omega
    simp [hone, hv]

/-- If [m is less than n](hyp:hm), [s is at least m](hyp:hms), and
[s is at most n](hyp:hsn), then [the real auxiliary mass at sum v equals
the Bernoulli parameter times the binomial probability at v−1 with n−s−1 trials,
plus its complementary weight times the binomial probability at v with n−s trials;
both success probabilities are 1/(n−m+1), and the first term is zero at v=0](goal). -/
-- @node: auxiliaryCountLaw_sum_real
lemma auxiliaryCountLaw_sum_real {n m s : ℕ} (hm : m < n)
    (hms : m ≤ s) (hsn : s ≤ n) (v : ℕ) :
    (auxiliaryCountLaw n m s).real {q | q.1 + q.2 = v} =
      bernoulliParameter n m s *
        (if v = 0 then 0 else
          (ProbabilityTheory.binomial (n - s - 1) (reciprocalProbability (n - m))).real {v - 1}) +
      (1 - bernoulliParameter n m s) *
        (ProbabilityTheory.binomial (n - s) (reciprocalProbability (n - m))).real {v} := by
  have hq := bernoulliParameter_mem hm hms hsn
  rw [Measure.real, auxiliaryCountLaw_sum_apply, ENNReal.toReal_add]
  · simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hq.1,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hq.2), Measure.real]
    split_ifs <;> simp
  · finiteness
  · finiteness

/-- If [v is at most r](hyp:hv), then [the binomial probability of v successes
in r trials with success probability 1/(a+1) equals the binomial coefficient
choosing v from r times a to the signed power r−v, divided by (a+1) to the power r](goal). -/
-- @node: reciprocalBinomial_real_singleton
lemma reciprocalBinomial_real_singleton (r a v : ℕ) (hv : v ≤ r) :
    (ProbabilityTheory.binomial r (reciprocalProbability a)).real {v} =
      (Nat.choose r v : ℝ) * (a : ℝ) ^ ((r : ℤ) - v) / (a + 1 : ℝ) ^ r := by
  have hb : (a + 1 : ℝ) ≠ 0 := by positivity
  have hc : 1 - 1 / (a + 1 : ℝ) = (a : ℝ) / (a + 1 : ℝ) := by field_simp; ring
  rw [ProbabilityTheory.binomial_real_singleton]
  change (Nat.choose r v : ℝ) * (1 / (a + 1 : ℝ)) ^ v *
    (1 - 1 / (a + 1 : ℝ)) ^ (r - v) = _
  rw [hc, div_pow, div_pow, one_pow]
  have he : (r : ℤ) - v = ((r - v : ℕ) : ℤ) := by
    rw [Nat.cast_sub hv]
  rw [he, zpow_natCast]
  calc
    _ = (Nat.choose r v : ℝ) * (a : ℝ) ^ (r - v) /
        ((a + 1 : ℝ) ^ v * (a + 1 : ℝ) ^ (r - v)) := by ring
    _ = _ := by rw [← pow_add, Nat.add_sub_of_le hv]

/-- If [a is positive](hyp:ha), [r is at most a](hyp:hr), and
[v is at most r](hyp:hv), then [writing d=a−r+1 and q=r/(ad), the mixture
of the binomial probability at v−1 with r−1 trials, weighted by q, and the
binomial probability at v with r trials, weighted by 1−q, equals
((d+v−1)/d) times the binomial coefficient choosing v from r times
a to the signed power r−v−1 divided by (a+1) to the signed power r−1;
both success probabilities are 1/(a+1), and the first mixture term is zero at v=0](goal). -/
-- @node: reciprocalBinomial_mixture
lemma reciprocalBinomial_mixture {a r v : ℕ} (ha : 0 < a) (hr : r ≤ a)
    (hv : v ≤ r) :
    let d : ℝ := (a : ℝ) - r + 1
    let q : ℝ := (r : ℝ) / ((a : ℝ) * d)
    q * (if v = 0 then 0 else
        (ProbabilityTheory.binomial (r - 1) (reciprocalProbability a)).real {v - 1}) +
      (1 - q) * (ProbabilityTheory.binomial r (reciprocalProbability a)).real {v} =
      ((d + v - 1) / d) * (Nat.choose r v : ℝ) *
        ((a : ℝ) ^ ((r : ℤ) - v - 1) / (a + 1 : ℝ) ^ ((r : ℤ) - 1)) := by
  dsimp only
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt ha)
  have hb : (a + 1 : ℝ) ≠ 0 := by positivity
  have hd : (a : ℝ) - r + 1 ≠ 0 := by
    have : (r : ℝ) ≤ a := by exact_mod_cast hr
    linarith
  rw [reciprocalBinomial_real_singleton r a v hv]
  have hscale : (a : ℝ) ^ ((r : ℤ) - v) =
      (a : ℝ) ^ ((r : ℤ) - v - 1) * a := by
    rw [← zpow_add_one₀ ha']
    congr 1
    ring
  have hden : (a + 1 : ℝ) ^ r = (a + 1 : ℝ) ^ ((r : ℤ) - 1) * (a + 1) := by
    rw [← zpow_natCast (a + 1 : ℝ), ← zpow_add_one₀ hb]
    congr 1
    ring
  by_cases hz : v = 0
  · subst v
    simp only [↓reduceIte, mul_zero, zero_add, Nat.choose_zero_right, Nat.cast_one,
      mul_one, Nat.cast_zero, add_zero, sub_zero] at *
    rw [hscale, hden]
    field_simp
    ring
  · have hvpos : 0 < v := Nat.pos_of_ne_zero hz
    have hrpos : 0 < r := lt_of_lt_of_le hvpos hv
    have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hrpos)
    have hc : (r : ℝ) * (Nat.choose (r - 1) (v - 1) : ℝ) =
        (Nat.choose r v : ℝ) * v := by
      have h := Nat.add_one_mul_choose_eq (r - 1) (v - 1)
      rw [Nat.sub_add_cancel hrpos, Nat.sub_add_cancel hvpos] at h
      exact_mod_cast h
    have hc' : (Nat.choose (r - 1) (v - 1) : ℝ) =
        (Nat.choose r v : ℝ) * v / r := by
      apply (eq_div_iff hr').2
      nlinarith [hc]
    rw [if_neg hz, reciprocalBinomial_real_singleton (r - 1) a (v - 1)
      (Nat.sub_le_sub_right hv 1), hc']
    have he : ((r - 1 : ℕ) : ℤ) - (v - 1 : ℕ) = (r : ℤ) - v := by
      rw [Nat.cast_sub hrpos, Nat.cast_sub hvpos]
      ring
    have he' : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by
      rw [Nat.cast_sub hrpos]; rfl
    rw [he, ← zpow_natCast (a + 1 : ℝ), he', hscale, hden]
    field_simp
    ring

/-- If [m is less than n](hyp:hm), [s is at least m](hyp:hms),
[s is at most n](hyp:hsn), and [v is at most n−s](hyp:hv), then
[the real auxiliary mass at coordinate sum v equals the conditional count mass
for total n, prefix length m, cumulative count s, and next count v](goal). -/
-- @node: auxiliaryCountLaw_sum_mass_of_le
lemma auxiliaryCountLaw_sum_mass_of_le {n m s v : ℕ} (hm : m < n)
    (hms : m ≤ s) (hsn : s ≤ n) (hv : v ≤ n - s) :
    (auxiliaryCountLaw n m s).real {q | q.1 + q.2 = v} =
      conditionalCountMass n m s v := by
  rw [auxiliaryCountLaw_sum_real hm hms hsn]
  have h := reciprocalBinomial_mixture (a := n - m) (r := n - s)
    (Nat.sub_pos_of_lt hm) (Nat.sub_le_sub_left hms n) hv
  dsimp only at h
  have ha : ((n - m : ℕ) : ℝ) = (n : ℝ) - m := Nat.cast_sub hm.le
  have hr : ((n - s : ℕ) : ℝ) = (n : ℝ) - s := Nat.cast_sub hsn
  have hd : ((n - m : ℕ) : ℝ) - (n - s : ℕ) + 1 = (s : ℝ) - m + 1 := by
    rw [ha, hr]; ring
  have hq : ((n - s : ℕ) : ℝ) /
      (((n - m : ℕ) : ℝ) * (((n - m : ℕ) : ℝ) - (n - s : ℕ) + 1)) =
      bernoulliParameter n m s := by rw [hd, ha, hr]; rfl
  rw [hq] at h
  rw [h, hd, ha]
  unfold conditionalCountMass
  have he : ((n - s : ℕ) : ℤ) - v - 1 = (n : ℤ) - (s + v : ℕ) - 1 := by
    rw [Nat.cast_sub hsn, Nat.cast_add]
    ring
  have he' : ((n - s : ℕ) : ℤ) - 1 = (n : ℤ) - s - 1 := by
    rw [Nat.cast_sub hsn]
  rw [he, he']
  congr 2
  ring

-- @node: auxiliaryCountLaw_sum_mass
/-- If [m is less than n](hyp:hm), [s is at least m](hyp:hms), and
[s is at most n](hyp:hsn), then [the real auxiliary mass at coordinate sum v
equals the conditional count mass for total n, prefix length m, cumulative count s,
and next count v](goal). -/
lemma auxiliaryCountLaw_sum_mass {n m s v : ℕ} (hm : m < n)
    (hms : m ≤ s) (hsn : s ≤ n) :
    (auxiliaryCountLaw n m s).real {q | q.1 + q.2 = v} =
      conditionalCountMass n m s v := by
  by_cases hv : v ≤ n - s
  · exact auxiliaryCountLaw_sum_mass_of_le hm hms hsn hv
  rw [auxiliaryCountLaw_sum_real hm hms hsn]
  have hz : v ≠ 0 := by omega
  have hc : Nat.choose (n - s) v = 0 := Nat.choose_eq_zero_of_lt (by omega)
  by_cases hs : s = n
  · subst s
    simp [bernoulliParameter, ProbabilityTheory.binomial_real_singleton,
      conditionalCountMass, Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hz)]
  · have hc' : Nat.choose (n - s - 1) (v - 1) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    simp [hz, ProbabilityTheory.binomial_real_singleton, conditionalCountMass, hc, hc']


/-- If [m is less than n](hyp:hm), [s is at least m](hyp:hms), and
[s is at most n](hyp:hsn), then [the auxiliary joint count measure is a
probability measure](goal). -/
-- @node: auxiliaryCountLaw_probability
lemma auxiliaryCountLaw_probability {n m s : ℕ} (hm : m < n)
    (hms : m ≤ s) (hsn : s ≤ n) : IsProbabilityMeasure (auxiliaryCountLaw n m s) := by
  have hq := bernoulliParameter_mem hm hms hsn
  constructor
  rw [auxiliaryCountLaw, Measure.bind_apply MeasurableSet.univ
    (measurable_of_countable _).aemeasurable]
  simp only [Measure.map_apply (measurable_of_countable _) MeasurableSet.univ,
    Set.preimage_univ, measure_univ, lintegral_const, one_mul]
  simp only [bernoulliNat, Measure.add_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hq.1 (sub_nonneg.mpr hq.2)]
  simp

/-- If [f is measurable](hyp:hf), [m is less than n](hyp:hm),
[s is at least m](hyp:hms), [s is at most n](hyp:hsn), and
[the real mass of each value v of f under the finite measure μ equals the
conditional count mass for n, m, s, and v](hyp:hmass), then
[f under μ has the same distribution as the coordinate sum under the auxiliary
joint count measure](goal). -/
-- @node: auxiliaryCountLaw_identDistrib_of_mass
lemma auxiliaryCountLaw_identDistrib_of_mass {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℕ} (hf : Measurable f)
    {n m s : ℕ} (hm : m < n) (hms : m ≤ s) (hsn : s ≤ n)
    (hmass : ∀ v : ℕ, μ.real {x | f x = v} = conditionalCountMass n m s v) :
    IdentDistrib f (fun q : ℕ × ℕ => q.1 + q.2) μ (auxiliaryCountLaw n m s) := by
  have := auxiliaryCountLaw_probability hm hms hsn
  refine ⟨hf.aemeasurable, (by fun_prop), ?_⟩
  apply Measure.ext_of_measureReal_singleton
  intro v
  rw [map_measureReal_apply hf (measurableSet_singleton v),
    map_measureReal_apply (by fun_prop) (measurableSet_singleton v)]
  exact (hmass v).trans (auxiliaryCountLaw_sum_mass hm hms hsn).symm

/-- If [m is less than n](hyp:hm), then [intersecting the event that κ agrees
with k before m with the event that its count at m equals v gives exactly
the prefix event through m, with k updated to v at that position](goal). -/
-- @node: countPrefixEvent_extend
lemma countPrefixEvent_extend {Ω : Type*} {n m : ℕ} (κ : Ω → CountVector n)
    (hm : m < n) (k : CountVector n) (v : ℕ) :
    countPrefixEvent κ m k ∩ {ω | κ ω ⟨m, hm⟩ = v} =
      countPrefixEvent κ (m + 1) (Function.update k ⟨m, hm⟩ v) := by
  classical
  ext ω
  constructor
  · rintro ⟨hprefix, hnext⟩ a ha
    by_cases ham : a = ⟨m, hm⟩
    · subst a
      simpa using hnext
    · rw [Function.update_of_ne ham]
      have hval : a.val ≠ m := fun heq => ham (Fin.ext heq)
      exact hprefix a (by omega)
  · intro h
    constructor
    · intro a ha
      have ham : a ≠ ⟨m, hm⟩ := by
        intro heq
        have hval : a.val = m := congrArg Fin.val heq
        omega
      simpa [Function.update_of_ne ham] using h a (by omega)
    · simpa using h ⟨m, hm⟩ (by simp)

/-- If [m is less than n](hyp:hm), then [under the canonical preference-count
measure, the conditional probability that the count at m is v given agreement
with k before m equals the mass of the prefix extended by v divided by the
mass of the original prefix](goal). -/
-- @node: canonicalCountMass_prefix_ratio
lemma canonicalCountMass_prefix_ratio {n m : ℕ} (hm : m < n)
    (k : CountVector n) (v : ℕ) :
    (ProbabilityTheory.cond (preferenceCountMeasure n) (countPrefixEvent id m k)).real
        {q | q ⟨m, hm⟩ = v} =
      (preferenceCountMeasure n).real
          (countPrefixEvent id (m + 1) (Function.update k ⟨m, hm⟩ v)) /
        (preferenceCountMeasure n).real (countPrefixEvent id m k) := by
  have hext := countPrefixEvent_extend (id : CountVector n → CountVector n) hm k v
  simp only [id_eq] at hext
  rw [Measure.real, ProbabilityTheory.cond_apply (Set.to_countable _).measurableSet,
    hext, ENNReal.toReal_mul, ENNReal.toReal_inv]
  simp only [Measure.real, div_eq_mul_inv, mul_comm]

/-- If [m is less than n](hyp:hm) and [agreement with k before m has positive
canonical preference-count mass](hyp:hk), then [the cumulative count of k
before m lies between m and n, inclusive](goal). -/
-- @node: canonicalPrefix_feasible
lemma canonicalPrefix_feasible {n m : ℕ} (hm : m < n) (k : CountVector n)
    (hk : 0 < preferenceCountMeasure n (countPrefixEvent id m k)) :
    m ≤ prefixCount k m ∧ prefixCount k m ≤ n := by
  have := preferenceCountMeasure_probability n
  have := cond_isProbabilityMeasure (ne_of_gt hk)
  have hs : ∀ᵐ q ∂ProbabilityTheory.cond (preferenceCountMeasure n)
      (countPrefixEvent id m k), PreferenceCounts q :=
    cond_absolutelyContinuous.ae_le (preferenceCountMeasure_supported n)
  obtain ⟨q, hq, hevent⟩ := (hs.and (ae_cond_mem
    ((Set.to_countable (countPrefixEvent id m k)).measurableSet))).exists
  have heq : prefixCount q m = prefixCount k m := by
    apply Finset.sum_congr rfl
    intro a ha
    split_ifs with h
    · exact hevent a h
    · rfl
  rw [← heq]
  constructor
  · by_cases hz : m = 0
    · subst m; simp [prefixCount]
    · exact hq.prefix m (by omega) hm.le
  · calc
      _ ≤ ∑ a, q a := Finset.sum_le_sum (fun a _ => by split_ifs <;> omega)
      _ = n := hq.total

/-- If [q agrees with k at every position before m](hyp:hq), then
[their cumulative counts before m are equal](goal). -/
-- @node: countPrefixEvent_prefixCount
lemma countPrefixEvent_prefixCount {n m : ℕ} {q k : CountVector n}
    (hq : q ∈ countPrefixEvent id m k) : prefixCount q m = prefixCount k m := by
  apply Finset.sum_congr rfl
  intro a ha
  split_ifs with h
  · exact hq a h
  · rfl

/-- If [m is less than n](hyp:hm), [q is a valid preference-count vector](hyp:hq),
[q agrees with k before m](hyp:he), and [its count at m is v](hyp:hv), then
[v is at most n minus the cumulative count before m, and adding v to that
cumulative count gives at least m+1](goal). -/
-- @node: countPrefixEvent_next_bounds
lemma countPrefixEvent_next_bounds {n m v : ℕ} (hm : m < n)
    {q k : CountVector n} (hq : PreferenceCounts q)
    (he : q ∈ countPrefixEvent id m k) (hv : q ⟨m, hm⟩ = v) :
    v ≤ n - prefixCount k m ∧ m + 1 ≤ prefixCount k m + v := by
  have hs := countPrefixEvent_prefixCount he
  have hnext := prefixCount_succ q ⟨m, hm⟩
  simp only at hnext
  rw [hs, hv] at hnext
  have hlower := hq.prefix (m + 1) (by omega) (by omega)
  have hupper : prefixCount q (m + 1) ≤ n := by
    calc
      _ ≤ ∑ a, q a := Finset.sum_le_sum (fun a _ => by split_ifs <;> omega)
      _ = n := hq.total
  rw [hnext] at hlower hupper
  omega

/-- If [m is less than n](hyp:hm) and [v exceeds the remaining total n minus
the cumulative count of k before m, or that cumulative count plus v is less
than m+1](hyp:hv), then [the canonical mass of the prefix extended by v is zero](goal). -/
-- @node: canonicalPrefix_extension_null
lemma canonicalPrefix_extension_null {n m v : ℕ} (hm : m < n)
    (k : CountVector n)
    (hv : ¬ (v ≤ n - prefixCount k m ∧ m + 1 ≤ prefixCount k m + v)) :
    preferenceCountMeasure n
      (countPrefixEvent id (m + 1) (Function.update k ⟨m, hm⟩ v)) = 0 := by
  rw [← countPrefixEvent_extend id hm k v]
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [preferenceCountMeasure_supported n] with q hq he
  exact hv (countPrefixEvent_next_bounds hm hq he.1 he.2)

/-- If [s is at least m](hyp:hms) and [v exceeds n−s or s+v is less
than m+1](hyp:hv), then [the conditional count mass for n, m, s, and v is zero](goal). -/
-- @node: conditionalCountMass_off_support
lemma conditionalCountMass_off_support {n m s v : ℕ} (hms : m ≤ s)
    (hv : ¬ (v ≤ n - s ∧ m + 1 ≤ s + v)) :
    conditionalCountMass n m s v = 0 := by
  by_cases hlarge : v ≤ n - s
  · have htight : s = m ∧ v = 0 := by omega
    rcases htight with ⟨rfl, rfl⟩
    simp [conditionalCountMass]
  · simp [conditionalCountMass, Nat.choose_eq_zero_of_lt (by omega : n - s < v)]

/-- If [m is less than n](hyp:hm), [the prefix specified by k has positive
canonical mass](hyp:hk), and [every valid preference-count vector agreeing with
that prefix has count v at m](hyp:hforce), then [the mass of the prefix extended
by v divided by the original prefix mass is one](goal). -/
-- @node: canonicalPrefix_forced_ratio
lemma canonicalPrefix_forced_ratio {n m v : ℕ} (hm : m < n)
    (k : CountVector n)
    (hk : 0 < preferenceCountMeasure n (countPrefixEvent id m k))
    (hforce : ∀ q : CountVector n, PreferenceCounts q →
      q ∈ countPrefixEvent id m k → q ⟨m, hm⟩ = v) :
    (preferenceCountMeasure n).real
        (countPrefixEvent id (m + 1) (Function.update k ⟨m, hm⟩ v)) /
      (preferenceCountMeasure n).real (countPrefixEvent id m k) = 1 := by
  have := preferenceCountMeasure_probability n
  have heq : preferenceCountMeasure n
      (countPrefixEvent id (m + 1) (Function.update k ⟨m, hm⟩ v)) =
      preferenceCountMeasure n (countPrefixEvent id m k) := by
    rw [← countPrefixEvent_extend id hm k v]
    apply measure_congr
    filter_upwards [preferenceCountMeasure_supported n] with q hq
    apply propext
    change (q ∈ countPrefixEvent id m k ∧ q ⟨m, hm⟩ = v) ↔
      q ∈ countPrefixEvent id m k
    exact ⟨And.left, fun he => ⟨he, hforce q hq he⟩⟩
  have hne : (preferenceCountMeasure n).real (countPrefixEvent id m k) ≠ 0 :=
    (measureReal_ne_zero_iff).2 (ne_of_gt hk)
  simpa only [Measure.real, heq] using div_self hne

/-- If [m is less than n](hyp:hm), [the prefix specified by k has positive
canonical mass](hyp:hk), and [its cumulative count before m equals n](hyp:hs),
then [the mass of the prefix extended by zero divided by the original prefix
mass is one](goal). -/
-- @node: canonicalPrefix_saturated_ratio
lemma canonicalPrefix_saturated_ratio {n m : ℕ} (hm : m < n)
    (k : CountVector n)
    (hk : 0 < preferenceCountMeasure n (countPrefixEvent id m k))
    (hs : prefixCount k m = n) :
    (preferenceCountMeasure n).real
        (countPrefixEvent id (m + 1) (Function.update k ⟨m, hm⟩ 0)) /
      (preferenceCountMeasure n).real (countPrefixEvent id m k) = 1 := by
  apply canonicalPrefix_forced_ratio hm k hk
  intro q hq he
  have hb := countPrefixEvent_next_bounds hm hq he (v := q ⟨m, hm⟩) rfl
  rw [hs] at hb
  omega

/-- If [m is less than n](hyp:hm), [m is the final position](hyp:hlast),
[the prefix specified by k has positive canonical mass](hyp:hk), and
[its cumulative count before m plus v equals n](hyp:hv), then
[the mass of the prefix extended by v divided by the original prefix mass is one](goal). -/
-- @node: canonicalPrefix_terminal_ratio
lemma canonicalPrefix_terminal_ratio {n m v : ℕ} (hm : m < n)
    (hlast : m + 1 = n) (k : CountVector n)
    (hk : 0 < preferenceCountMeasure n (countPrefixEvent id m k))
    (hv : prefixCount k m + v = n) :
    (preferenceCountMeasure n).real
        (countPrefixEvent id (m + 1) (Function.update k ⟨m, hm⟩ v)) /
      (preferenceCountMeasure n).real (countPrefixEvent id m k) = 1 := by
  apply canonicalPrefix_forced_ratio hm k hk
  intro q hq he
  have hs := prefixCount_succ q ⟨m, hm⟩
  have ht : prefixCount q n = n := by
    simpa [prefixCount, preferenceTotal] using hq.total
  have hp := countPrefixEvent_prefixCount he
  change prefixCount q (m + 1) = prefixCount q m + q ⟨m, hm⟩ at hs
  rw [hlast, ht, hp] at hs
  omega

/-- If [m is less than n](hyp:hm), then [the conditional count mass at zero
is one when the cumulative count already equals the total n](goal). -/
-- @node: conditionalCountMass_saturated
lemma conditionalCountMass_saturated {n m : ℕ} (hm : m < n) :
    conditionalCountMass n m n 0 = 1 := by
  rw [← auxiliaryCountLaw_sum_mass hm (Nat.le_of_lt hm) le_rfl,
    auxiliaryCountLaw_sum_real hm (Nat.le_of_lt hm) le_rfl]
  simp [bernoulliParameter]

/-- [For total m+1, prefix length m, and cumulative count m, the conditional
count mass at one is one](goal). -/
-- @node: conditionalCountMass_terminal
lemma conditionalCountMass_terminal (m : ℕ) :
    conditionalCountMass (m + 1) m m 1 = 1 := by
  simp [conditionalCountMass, Nat.cast_add, Nat.cast_one]

/-- If [m is less than n](hyp:hm), [the prefix specified by k has positive
canonical mass](hyp:hk), [v is at most the remaining total](hyp:hv),
[the cumulative count before m plus v is at least m+1](hyp:hlow), and
[either the cumulative count already equals n or m is the final position](hyp:hboundary),
then [the mass of the prefix extended by v divided by its original mass equals
the conditional count mass at v for that cumulative count](goal). -/
-- @node: canonicalPrefix_boundary_mass
lemma canonicalPrefix_boundary_mass {n m v : ℕ} (hm : m < n)
    (k : CountVector n)
    (hk : 0 < preferenceCountMeasure n (countPrefixEvent id m k))
    (hv : v ≤ n - prefixCount k m) (hlow : m + 1 ≤ prefixCount k m + v)
    (hboundary : prefixCount k m = n ∨ m + 1 = n) :
    (preferenceCountMeasure n).real
        (countPrefixEvent id (m + 1) (Function.update k ⟨m, hm⟩ v)) /
      (preferenceCountMeasure n).real (countPrefixEvent id m k) =
        conditionalCountMass n m (prefixCount k m) v := by
  rcases hboundary with hs | hlast
  · have hz : v = 0 := by omega
    subst v
    rw [canonicalPrefix_saturated_ratio hm k hk hs, hs,
      conditionalCountMass_saturated hm]
  · have hb := canonicalPrefix_feasible hm k hk
    by_cases hs : prefixCount k m = n
    · have hz : v = 0 := by omega
      subst v
      rw [canonicalPrefix_saturated_ratio hm k hk hs, hs,
        conditionalCountMass_saturated hm]
    · have hs' : prefixCount k m = m := by omega
      have hv' : v = 1 := by omega
      have htotal : prefixCount k m + v = n := by omega
      rw [canonicalPrefix_terminal_ratio hm hlast k hk htotal, hs', hv', ← hlast,
        conditionalCountMass_terminal]

end Papers.HawkesD75660b
