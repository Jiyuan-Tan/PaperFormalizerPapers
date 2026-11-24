module

public import Papers.HawkesD75660b.Helpers.ConditionalCountsBase

/-! Canonical prefix probabilities and initial count law. -/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Papers.HawkesD75660b

-- @node: canonicalPrefix_all_feasible
/-- If [the prefix length m is at most the vector length n](hyp:hm) and [the
event that the first m counts equal those of k has positive canonical
probability](hyp:hk), then [for every nonnegative integer t at most m, the sum
of the first t entries of k is at least t](goal). -/
lemma canonicalPrefix_all_feasible {n m : ℕ} (hm : m ≤ n) (k : CountVector n)
    (hk : 0 < preferenceCountMeasure n (countPrefixEvent id m k)) :
    ∀ t, t ≤ m → t ≤ prefixCount k t := by
  have := preferenceCountMeasure_probability n
  have := cond_isProbabilityMeasure (ne_of_gt hk)
  have hs : ∀ᵐ q ∂ProbabilityTheory.cond (preferenceCountMeasure n)
      (countPrefixEvent id m k), PreferenceCounts q :=
    cond_absolutelyContinuous.ae_le (preferenceCountMeasure_supported n)
  obtain ⟨q, hq, he⟩ := (hs.and (ae_cond_mem
    ((Set.to_countable (countPrefixEvent id m k)).measurableSet))).exists
  intro t ht
  have heq : prefixCount q t = prefixCount k t := by
    apply Finset.sum_congr rfl
    intro a ha
    split_ifs with h
    · exact he a (lt_of_lt_of_le h ht)
    · rfl
  rw [← heq]
  by_cases hz : t = 0
  · subst t; simp [prefixCount]
  · exact hq.prefix t (by omega) (ht.trans hm)

-- @node: canonicalPrefix_mass
/-- Suppose [the prefix length m is at most the vector length n](hyp:hm), [the
sum s of the first m entries of k is at most n](hyp:hsn), and [the sum of the
first t entries of k is at least t for every nonnegative integer t at most m](hyp:hp).
Then [the canonical probability of matching the first m entries of k equals
n! times a completion factor, divided by the product of (n + 1) to the power
n − 1, (n − s)!, and the factorials of the first m entries of k; the completion
factor is one when s = n and otherwise is (s − m + 1) times (n − m + 1) to the
power n − s − 1](goal). -/
lemma canonicalPrefix_mass {n m : ℕ} (hm : m ≤ n) (k : CountVector n)
    (hsn : prefixCount k m ≤ n)
    (hp : ∀ t, t ≤ m → t ≤ prefixCount k t) :
    (preferenceCountMeasure n).real (countPrefixEvent id m k) =
      ((n.factorial : ℝ) *
        (if n - prefixCount k m = 0 then 1 else
          ((prefixCount k m - m + 1 : ℕ) : ℝ) *
            ((n - m + 1 : ℕ) : ℝ) ^ (n - prefixCount k m - 1))) /
        (((n : ℝ) + 1) ^ (n - 1) * ((n - prefixCount k m).factorial : ℝ) *
          ∏ a : Fin m, ((k ⟨a.val, lt_of_lt_of_le a.isLt hm⟩).factorial : ℝ)) := by
  classical
  let low : Fin m → ℕ := fun a => k ⟨a.val, lt_of_lt_of_le a.isLt hm⟩
  have hsum : (∑ a, low a) = prefixCount k m := by
    simpa [low] using prefixCount_restrict_sum hm k m le_rfl
  have hprefix : ∀ t, t ≤ m →
      t ≤ ∑ a : Fin m, if a.val + 1 ≤ t then low a else 0 := by
    intro t ht
    have heq := prefixCount_restrict_sum hm k t ht
    simp only [Nat.lt_iff_add_one_le] at heq
    rw [show (∑ a : Fin m, if a.val + 1 ≤ t then low a else 0) =
      prefixCount k t from heq]
    exact hp t ht
  have hmass := canonicalPrescribedPrefix_mass_of_total hm low (n - prefixCount k m)
    (by omega) (by rw [hsum]; exact hp m le_rfl) hprefix
  have hevent : countPrefixEvent id m k =
      {q : CountVector n | ∀ a : Fin m,
        q ⟨a.val, lt_of_lt_of_le a.isLt hm⟩ = low a} := by
    ext q
    constructor
    · intro h a; exact h _ a.isLt
    · intro h a ha
      exact h ⟨a.val, ha⟩
  rw [hevent]
  simpa only [hsum, low] using hmass

-- @node: canonicalInitialCount_law
/-- If [the vector length n is positive](hyp:hn), then [under the canonical
count measure, the first count minus one has a binomial distribution with
n − 1 trials and success probability 1/(n + 1)](goal). -/
lemma canonicalInitialCount_law {n : ℕ} (hn : 0 < n) :
    HasLaw (fun q : CountVector n => q ⟨0, hn⟩ - 1)
      (ProbabilityTheory.binomial (n - 1) (reciprocalProbability n))
      (preferenceCountMeasure n) := by
  have := preferenceCountMeasure_probability n
  refine ⟨(measurable_of_countable _).aemeasurable, ?_⟩
  apply Measure.ext_of_measureReal_singleton
  intro v
  rw [map_measureReal_apply (by fun_prop) (measurableSet_singleton v)]
  change (preferenceCountMeasure n).real {q | q ⟨0, hn⟩ - 1 = v} = _
  have hsupport := preferenceCountMeasure_supported n
  have hb : ∀ᵐ q ∂preferenceCountMeasure n, 1 ≤ q ⟨0, hn⟩ ∧ q ⟨0, hn⟩ ≤ n := by
    filter_upwards [hsupport] with q hq
    have hp := hq.prefix 1 (by omega) hn
    have he := prefixCount_succ q ⟨0, hn⟩
    simp only [zero_add] at he
    have hz : prefixCount q 0 = 0 := by simp [prefixCount]
    rw [he, hz, zero_add] at hp
    exact ⟨hp, preferenceCounts_coordinate_bound hq _⟩
  by_cases hv : v ≤ n - 1
  · have hevent : {q : CountVector n | q ⟨0, hn⟩ - 1 = v} =ᵐ[preferenceCountMeasure n]
        {q | q ⟨0, hn⟩ = v + 1} := by
      filter_upwards [hb] with q hq
      change (q ⟨0, hn⟩ - 1 = v) = (q ⟨0, hn⟩ = v + 1)
      apply propext
      omega
    rw [measureReal_congr hevent, reciprocalBinomial_real_singleton (n - 1) n v hv]
    cases n with
    | zero => omega
    | succ t =>
      rw [canonicalInitialShift_mass t v (by simpa using hv)]
      simp only [Nat.add_sub_cancel]
      rw [show (t : ℤ) - v = ((t - v : ℕ) : ℤ) by omega, zpow_natCast]
      push_cast
      congr 2; ring
  · have hnull : (preferenceCountMeasure n) {q | q ⟨0, hn⟩ - 1 = v} = 0 := by
      apply measure_mono_null (t := {q : CountVector n | ¬(1 ≤ q ⟨0, hn⟩ ∧ q ⟨0, hn⟩ ≤ n)})
      · intro q hq
        simp only [Set.mem_ofPred_eq] at *
        omega
      · exact ae_iff.mp hb
    rw [Measure.real, hnull, ENNReal.toReal_zero,
      ProbabilityTheory.binomial_real_singleton, Nat.choose_eq_zero_of_lt (by omega)]
    simp

-- @env: S2
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (κ : Ω → CountVector n)

-- @node: countPrefix_hasLaw
/-- If [the random count vector κ has the canonical count law under the
probability measure P](hyp:hlaw), then [under P conditioned on the first m
counts matching k, κ has the canonical count measure conditioned on the same
prefix event](goal). -/
lemma countPrefix_hasLaw (hlaw : kappaCPMFLaw P κ) (m : ℕ) (k : CountVector n) :
    HasLaw κ
      (ProbabilityTheory.cond (preferenceCountMeasure n) (countPrefixEvent id m k))
      (ProbabilityTheory.cond P (countPrefixEvent κ m k)) := by
  have hA : MeasurableSet (countPrefixEvent (id : CountVector n → CountVector n) m k) := by
    exact (Set.to_countable _).measurableSet
  have hevent : countPrefixEvent κ m k = κ ⁻¹' countPrefixEvent id m k := rfl
  constructor
  · exact hlaw.aemeasurable.mono_ac cond_absolutelyContinuous
  · rw [hevent, ProbabilityTheory.cond, Measure.map_smul,
      ← Measure.restrict_map_of_aemeasurable hlaw.aemeasurable hA,
      hlaw.map_eq, ProbabilityTheory.cond,
      ← hlaw.map_eq, Measure.map_apply_of_aemeasurable hlaw.aemeasurable hA]

end Papers.HawkesD75660b
