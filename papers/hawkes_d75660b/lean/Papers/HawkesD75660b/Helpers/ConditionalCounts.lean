module

public import Papers.HawkesD75660b.Helpers.CanonicalCounts

/-! Assembly of the conditional preference-count law. -/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Papers.HawkesD75660b

-- @env: S2
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (κ : Ω → CountVector n)

-- @node: lem:kappacpmf1
/-- Suppose [the count vector has positive length](hyp:hindex),
[its distribution is the preference-count law under the sampling probability measure](hyp:hlaw),
and [the natural-count and zero-count conventions both identify natural numbers with
the nonnegative integers](hyp:hdomain,hzero). Then [after any positive prefix shorter
than the vector with positive probability, the next count has the specified conditional
count mass at every value satisfying the remaining-total and cumulative-count bounds,
and has the distribution of the sum of two auxiliary counts: the second is Bernoulli
with parameter (n-s)/((n-m)(s-m+1)), and conditional on its value y having positive
probability, the first is binomial with n-s-y trials and success probability 1/(n-m+1);
also, the initial count minus one is binomial with n-1 trials and success probability
1/(n+1), where n is the vector length, m is the prefix length, and s is its total](goal). -/
lemma conditionalPreferenceCountLaw
    (hindex : kappaCPMFIndex n) (hlaw : kappaCPMFLaw P κ)
    (hdomain : naturalCountDomainConvention) (hzero : zeroCountConvention) :
    (∀ m : ℕ, 1 ≤ m → ∀ hm : m < n, -- @realizes m(positive prefix length less than n)
      ∀ k : CountVector n, 0 < P (countPrefixEvent κ m k) →
      let s := prefixCount k m
      (∀ v : ℕ, v ≤ n - s → m + 1 ≤ s + v → -- @realizes k(next count with support bounds)
        (ProbabilityTheory.cond P (countPrefixEvent κ m k)).real
          {ω | κ ω ⟨m, hm⟩ = v} = conditionalCountMass n m s v) ∧
      IdentDistrib (fun ω => κ ω ⟨m, hm⟩) (fun q : ℕ × ℕ => q.1 + q.2)
        (ProbabilityTheory.cond P (countPrefixEvent κ m k)) (auxiliaryCountLaw n m s) ∧
      HasLaw Prod.snd (bernoulliNat (bernoulliParameter n m s)) (auxiliaryCountLaw n m s) ∧
      (∀ y : ℕ, 0 < auxiliaryCountLaw n m s {q | q.2 = y} →
        HasLaw Prod.fst
          (ProbabilityTheory.binomial (n - s - y) (reciprocalProbability (n - m)))
          (ProbabilityTheory.cond (auxiliaryCountLaw n m s) {q | q.2 = y}))) ∧
    HasLaw (fun ω => κ ω ⟨0, hindex⟩ - 1)
      (ProbabilityTheory.binomial (n - 1) (reciprocalProbability n)) P := by
  -- The auxiliary construction's marginal and conditional laws are proved above.
  -- The remaining content is the parking-count transition and initial count law.
  suffices hcounts :
      (∀ m : ℕ, 1 ≤ m → ∀ hm : m < n,
        ∀ k : CountVector n, 0 < P (countPrefixEvent κ m k) →
        let s := prefixCount k m
        (∀ v : ℕ, v ≤ n - s → m + 1 ≤ s + v →
          (ProbabilityTheory.cond P (countPrefixEvent κ m k)).real
            {ω | κ ω ⟨m, hm⟩ = v} = conditionalCountMass n m s v) ∧
        IdentDistrib (fun ω => κ ω ⟨m, hm⟩) (fun q : ℕ × ℕ => q.1 + q.2)
          (ProbabilityTheory.cond P (countPrefixEvent κ m k)) (auxiliaryCountLaw n m s)) ∧
      HasLaw (fun ω => κ ω ⟨0, hindex⟩ - 1)
        (ProbabilityTheory.binomial (n - 1) (reciprocalProbability n)) P by
    refine ⟨?_, hcounts.2⟩
    intro m hm hmn k hk
    obtain ⟨hmass, hsum⟩ := hcounts.1 m hm hmn k hk
    exact ⟨hmass, hsum, auxiliaryCountLaw_snd n m (prefixCount k m),
      auxiliaryCountLaw_cond_fst n m (prefixCount k m)⟩
  -- All remaining counting takes place on the finite-support canonical law.
  suffices hcanonical :
      (∀ m : ℕ, 1 ≤ m → ∀ hm : m < n,
        ∀ k : CountVector n,
        0 < preferenceCountMeasure n (countPrefixEvent id m k) →
        let s := prefixCount k m
        ∀ v : ℕ,
          (preferenceCountMeasure n).real
              (countPrefixEvent id (m + 1) (Function.update k ⟨m, hm⟩ v)) /
            (preferenceCountMeasure n).real (countPrefixEvent id m k) =
              conditionalCountMass n m s v) ∧
      HasLaw (fun q : CountVector n => q ⟨0, hindex⟩ - 1)
        (ProbabilityTheory.binomial (n - 1) (reciprocalProbability n))
        (preferenceCountMeasure n) by
    refine ⟨?_, hcanonical.2.fun_comp hlaw⟩
    intro m hm hmn k hk
    have hprefix : P (countPrefixEvent κ m k) =
        preferenceCountMeasure n (countPrefixEvent id m k) :=
      hlaw.measure_eq (p := fun q => ∀ a : Fin n, a.val < m → q a = k a)
        (Set.to_countable _).measurableSet
    have hpos := hprefix ▸ hk
    have hmass := hcanonical.1 m hm hmn k hpos
    have hbounds := canonicalPrefix_feasible hmn k hpos
    have := preferenceCountMeasure_probability n
    have := cond_isProbabilityMeasure (ne_of_gt hpos)
    have hsum := auxiliaryCountLaw_identDistrib_of_mass
      (μ := ProbabilityTheory.cond (preferenceCountMeasure n) (countPrefixEvent id m k))
      (f := fun q : CountVector n => q ⟨m, hmn⟩) (by fun_prop)
      hmn hbounds.1 hbounds.2 (fun v => by
        rw [canonicalCountMass_prefix_ratio]
        exact hmass v)
    have hcond := countPrefix_hasLaw P κ hlaw m k
    refine ⟨?_, ?_⟩
    · intro v hv hlow
      rw [hcond.measureReal_eq (p := fun q => q ⟨m, hmn⟩ = v)
        (Set.to_countable _).measurableSet]
      rw [canonicalCountMass_prefix_ratio]
      exact hmass v
    · exact ((hcond.identDistrib HasLaw.id).comp
        (by fun_prop : Measurable (fun q : CountVector n => q ⟨m, hmn⟩))).trans hsum
  -- Unsupported extensions and their displayed masses both vanish, so the
  -- enumerative identity is needed only on the actual parking support.
  suffices hsupported :
      (∀ m : ℕ, 1 ≤ m → ∀ hm : m < n,
        ∀ k : CountVector n,
        0 < preferenceCountMeasure n (countPrefixEvent id m k) →
        ∀ v : ℕ, v ≤ n - prefixCount k m → m + 1 ≤ prefixCount k m + v →
          (preferenceCountMeasure n).real
              (countPrefixEvent id (m + 1) (Function.update k ⟨m, hm⟩ v)) /
            (preferenceCountMeasure n).real (countPrefixEvent id m k) =
              conditionalCountMass n m (prefixCount k m) v) ∧
      HasLaw (fun q : CountVector n => q ⟨0, hindex⟩ - 1)
        (ProbabilityTheory.binomial (n - 1) (reciprocalProbability n))
        (preferenceCountMeasure n) by
    refine ⟨?_, hsupported.2⟩
    intro m hm hmn k hk
    dsimp only
    intro v
    by_cases hv : v ≤ n - prefixCount k m ∧ m + 1 ≤ prefixCount k m + v
    · exact hsupported.1 m hm hmn k hk v hv.1 hv.2
    · have hb := canonicalPrefix_feasible hmn k hk
      rw [conditionalCountMass_off_support hb.1 hv, Measure.real,
        canonicalPrefix_extension_null hmn k hv, ENNReal.toReal_zero, zero_div]
  -- Deterministic boundaries are settled by the total-count constraint.
  -- Only nonsaturated prefixes before the final step require enumeration.
  suffices hinterior :
      (∀ m : ℕ, 1 ≤ m → ∀ hm : m < n, m + 1 < n →
        ∀ k : CountVector n,
        0 < preferenceCountMeasure n (countPrefixEvent id m k) →
        prefixCount k m < n →
        ∀ v : ℕ, v ≤ n - prefixCount k m → m + 1 ≤ prefixCount k m + v →
          (preferenceCountMeasure n).real
              (countPrefixEvent id (m + 1) (Function.update k ⟨m, hm⟩ v)) /
            (preferenceCountMeasure n).real (countPrefixEvent id m k) =
              conditionalCountMass n m (prefixCount k m) v) by
    refine ⟨?_, canonicalInitialCount_law hindex⟩
    intro m hm hmn k hk v hv hlow
    by_cases hb : prefixCount k m = n ∨ m + 1 = n
    · exact canonicalPrefix_boundary_mass hmn k hk hv hlow hb
    · have hf := canonicalPrefix_feasible hmn k hk
      exact hinterior m hm hmn (by omega) k hk (by omega) v hv hlow
  intro m hm hmn hinterior k hk hsn v hv hlow
  have hp := canonicalPrefix_all_feasible hmn.le k hk
  have hb := canonicalPrefix_feasible hmn k hk
  have hden := canonicalPrefix_mass hmn.le k hb.2 hp
  let next := Function.update k ⟨m, hmn⟩ v
  have hbefore (t : ℕ) (ht : t ≤ m) : prefixCount next t = prefixCount k t := by
    apply Finset.sum_congr rfl
    intro a ha
    split_ifs with h
    · have hne : a ≠ ⟨m, hmn⟩ := by
        intro he
        have heval : a.val = m := congrArg Fin.val he
        omega
      exact Function.update_of_ne hne v k
    · rfl
  have hnext : prefixCount next (m + 1) = prefixCount k m + v := by
    rw [prefixCount_succ next ⟨m, hmn⟩, hbefore m le_rfl]
    simp [next]
  have hpnext : ∀ t, t ≤ m + 1 → t ≤ prefixCount next t := by
    intro t ht
    by_cases htm : t ≤ m
    · rw [hbefore t htm]
      exact hp t htm
    · have he : t = m + 1 := by omega
      rw [he, hnext]
      exact hlow
  have hnum := canonicalPrefix_mass (by omega : m + 1 ≤ n) next
    (by rw [hnext]; omega) hpnext
  change (preferenceCountMeasure n).real (countPrefixEvent id (m + 1) next) /
    (preferenceCountMeasure n).real (countPrefixEvent id m k) = _
  rw [hnum, hden, hnext]
  -- Cancel successive prefix masses, treating the zero remainder separately
  -- when converting natural powers to the displayed signed powers.

  have hprod : (∏ a : Fin (m + 1), ((next ⟨a.val, by omega⟩).factorial : ℝ)) =
      (∏ a : Fin m, ((k ⟨a.val, by omega⟩).factorial : ℝ)) * (v.factorial : ℝ) := by
    rw [Fin.prod_univ_castSucc]
    congr 1
    · apply Finset.prod_congr rfl
      intro a ha
      have hne : (⟨a.val, by omega⟩ : Fin n) ≠ ⟨m, hmn⟩ := by
        intro he
        have heval : a.val = m := congrArg Fin.val he
        omega
      simp [next, Function.update_of_ne hne]
    · simp [next]
  rw [hprod]
  have hA : (n : ℝ) - m ≠ 0 := by
    have : (m : ℝ) < n := by exact_mod_cast hmn
    linarith
  have hB : (n : ℝ) - m + 1 ≠ 0 := by
    have : (m : ℝ) < n := by exact_mod_cast hmn
    linarith
  have hD : (prefixCount k m : ℝ) - m + 1 ≠ 0 := by
    have : (m : ℝ) ≤ prefixCount k m := by exact_mod_cast hb.1
    linarith
  have hzden : n - prefixCount k m ≠ 0 := by omega
  have heDen : ((n : ℤ) - prefixCount k m - 1) =
      ((n - prefixCount k m - 1 : ℕ) : ℤ) := by omega
  have heBase : ((n - m + 1 : ℕ) : ℝ) = (n : ℝ) - m + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hmn.le]; norm_num
  have heD : ((prefixCount k m - m + 1 : ℕ) : ℝ) =
      (prefixCount k m : ℝ) - m + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hb.1]; norm_num
  have hweight : (if n - (prefixCount k m + v) = 0 then (1 : ℝ)
      else ((prefixCount k m + v - (m + 1) + 1 : ℕ) : ℝ) *
        ((n - (m + 1) + 1 : ℕ) : ℝ) ^ (n - (prefixCount k m + v) - 1)) =
      ((prefixCount k m : ℝ) + v - m) *
        ((n : ℝ) - m) ^ ((n : ℤ) - (prefixCount k m + v : ℕ) - 1) := by
    have ht : prefixCount k m + v ≤ n := by omega
    by_cases hz : n - (prefixCount k m + v) = 0
    · have he : prefixCount k m + v = n := by omega
      have her : (prefixCount k m : ℝ) + v = n := by exact_mod_cast he
      simp only [he, Nat.sub_self, ↓reduceIte, sub_self, zero_sub, zpow_neg, zpow_one]
      rw [show (prefixCount k m : ℝ) + v - m = (n : ℝ) - m by linarith]
      exact (mul_inv_cancel₀ hA).symm
    · have he : (n : ℤ) - (prefixCount k m + v : ℕ) - 1 =
          ((n - (prefixCount k m + v) - 1 : ℕ) : ℤ) := by omega
      have hc : ((prefixCount k m + v - (m + 1) + 1 : ℕ) : ℝ) =
          (prefixCount k m : ℝ) + v - m := by
        rw [Nat.cast_add, Nat.cast_sub hlow, Nat.cast_add, Nat.cast_add]
        norm_num; ring
      have ha : n - (m + 1) + 1 = n - m := by omega
      simp only [hz, ↓reduceIte, hc, ha, Nat.cast_sub hmn.le, he, zpow_natCast]
  rw [hweight, if_neg hzden, heBase, heD]
  unfold conditionalCountMass
  rw [heDen, zpow_natCast]
  have hfac : ((n - prefixCount k m).factorial : ℝ) =
      (Nat.choose (n - prefixCount k m) v : ℝ) * (v.factorial : ℝ) *
        ((n - (prefixCount k m + v)).factorial : ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial hv
    have he : n - prefixCount k m - v = n - (prefixCount k m + v) := by omega
    rw [he] at h
    exact_mod_cast h.symm
  have hnf : (n.factorial : ℝ) ≠ 0 := by positivity
  have hrf : ((n - (prefixCount k m + v)).factorial : ℝ) ≠ 0 := by positivity
  have hvf : (v.factorial : ℝ) ≠ 0 := by positivity
  have hpf : (∏ a : Fin m, ((k ⟨a.val, by omega⟩).factorial : ℝ)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun a ha => by positivity)
  have hpow : ((n : ℝ) + 1) ^ (n - 1) ≠ 0 := by positivity
  have hrem : ((n - prefixCount k m).factorial : ℝ) ≠ 0 := by positivity
  field_simp
  rw [hfac]
  ring

end Papers.HawkesD75660b
