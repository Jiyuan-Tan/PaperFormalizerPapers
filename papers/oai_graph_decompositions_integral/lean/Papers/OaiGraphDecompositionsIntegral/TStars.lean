module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.StarsSetup
public import Papers.OaiGraphDecompositionsIntegral.Helpers.Thresholds
public import Papers.OaiGraphDecompositionsIntegral.Helpers.StarsQuantities
public import Papers.OaiGraphDecompositionsIntegral.Helpers.StarsBinomial
public import Papers.OaiGraphDecompositionsIntegral.Helpers.StarsComponents
public import Papers.OaiGraphDecompositionsIntegral.Helpers.StarsTrialBudget
public import Papers.OaiGraphDecompositionsIntegral.Helpers.StarsCounting
public import Papers.OaiGraphDecompositionsIntegral.Helpers.StarsCopyCover
public import Papers.OaiGraphDecompositionsIntegral.Helpers.StarsFreshRows
public import Papers.OaiGraphDecompositionsIntegral.Helpers.StarsHostRows
public import Papers.OaiGraphDecompositionsIntegral.Helpers.StarsExtraction
public import Papers.OaiGraphDecompositionsIntegral.Helpers.StarsEmbedding
public import Toolkit.Foundations.Probability.BiasedCube
public import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Both star-forest threshold bounds -/

public section

namespace Papers.OaiGraphDecompositionsIntegral

-- @node: containmentThreshold_le_of_trial_count
/-- If [the host order n is positive](hyp:hn), [J has at most n vertices](hyp:hsize),
[p lies between zero and one, inclusive](hyp:hp), [the expected value of the trial counter
T in the random host at density p is at most n/8](hyp:hET), and [every host whose
counter is at most the integer part of n/2 contains a copy of J](hyp:hembed), then
[the containment threshold of J in an n-vertex host is at most p](goal).

The final Markov step applies to a capped trial counter on the actual finite host;
the process construction must prove the expectation and embedding properties locally
before invoking this lemma. -/
lemma containmentThreshold_le_of_trial_count {V : Type} [Fintype V]
    (J : SimpleGraph V) (n : ℕ) (p : ℝ) (hn : 0 < n)
    (hsize : Fintype.card V ≤ n) (hp : p ∈ Set.Icc 0 1)
    (T : (KEdge n → Bool) → ℕ)
    (hET : (randomHost n p hp).E (fun z => (T z : ℝ)) ≤ (n : ℝ) / 8)
    (hembed : ∀ z, T z ≤ n / 2 → ContainsCopy J (hostGraph z)) :
    containmentThreshold J n ≤ p := by
  classical
  by_cases hedge : J.edgeSet = ∅
  · simpa [containmentThreshold, hedge] using hp.1
  have hfinish := star_finish_probability_of_expected_trials (randomHost n p hp) T n hn hET
  have hprob : (1 / 2 : ℝ) ≤ containmentProb J n p := by
    apply hfinish.trans
    exact Causalean.Experimentation.DesignBased.FiniteDesign.Pr_mono _ _ _ hembed
  simpa [containmentThreshold, hedge] using
    (containmentThresholdRaw_isLeast J n hsize).2 ⟨hp, hprob⟩

-- @node: prop:stars
/-- [There is an absolute host-order cutoff such that, for every n above it, every finite
star forest J on at most n vertices with at most n/100 nonisolated vertices has
containment threshold at most twice the absolute star constant A times its integral
expectation threshold; if its expectation threshold is less than 1/(2A), the factor
improves to A](goal). -/
theorem stars :
    ∃ N₃ : ℕ, -- @realizes N_3(absolute vertex cutoff)
      ∀ n : ℕ, StarsOrder N₃ n →
      ∀ (V : Type) [Fintype V] [DecidableEq V]
        (J : SimpleGraph V) [DecidableRel J.Adj],
        FiniteSimpleGraphs V → IsStarForest J → StarsSize V n → StarsSupport J n →
        containmentThreshold J n ≤ 2 * starConstA * expectationThreshold J n ∧
        (StarsSmallQ J n → containmentThreshold J n ≤ starConstA * expectationThreshold J n) :=
  by
  classical
  suffices hsmall : ∃ N₃ : ℕ, ∀ n : ℕ, StarsOrder N₃ n →
      ∀ (V : Type) [Fintype V] [DecidableEq V]
        (J : SimpleGraph V) [DecidableRel J.Adj],
        FiniteSimpleGraphs V → IsStarForest J → StarsSize V n → StarsSupport J n →
        J.edgeSet.Nonempty → StarsSmallQ J n →
        containmentThreshold J n ≤ starConstA * expectationThreshold J n by
    obtain ⟨N₃, hsmall⟩ := hsmall
    refine ⟨N₃, ?_⟩
    intro n hn V _ _ J _ hfinite hstar hsize hsupport
    by_cases hedge : J.edgeSet = ∅
    · simp [containmentThreshold, expectationThreshold, hedge]
    have hA : 0 < starConstA := by unfold starConstA; positivity
    by_cases hq : StarsSmallQ J n
    · have hs := hsmall n hn V J hfinite hstar hsize hsupport
        (Set.nonempty_iff_ne_empty.mpr hedge) hq
      have hnonneg : 0 ≤ expectationThreshold J n := by
        have h := (expectationThresholdRaw_isGreatest J n
          (Set.nonempty_iff_ne_empty.mpr hedge) hsize).1.1.1
        simpa [expectationThreshold, hedge] using h
      refine ⟨hs.trans ?_, fun _ => hs⟩
      nlinarith
    · have hlarge : 1 ≤ 2 * starConstA * expectationThreshold J n := by
        have hl : 1 / (2 * starConstA) ≤ expectationThreshold J n :=
          le_of_not_gt hq
        have := (div_le_iff₀ (by positivity : 0 < 2 * starConstA)).mp hl
        nlinarith
      have hunit : containmentThreshold J n ≤ 1 := by
        simpa [containmentThreshold, hedge] using
          (containmentThresholdRaw_isLeast J n hsize).1.1.2
      exact ⟨hunit.trans hlarge, fun h => (hq h).elim⟩
  refine ⟨2, ?_⟩
  intro n hn V _ _ J _ _ hstar hsize hsupport hedge hsmall
  have hn2 : 2 ≤ n := hn
  have hnpos : 0 < n := by omega
  have hA : 1 ≤ starConstA := by
    have he := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 4)
    unfold starConstA
    nlinarith
  have hq : 0 ≤ expectationThreshold J n := by
    have h := (expectationThresholdRaw_isGreatest J n hedge hsize).1.1.1
    simpa [expectationThreshold, Set.nonempty_iff_ne_empty.mp hedge] using h
  have hp : starConstA * expectationThreshold J n < 1 / 2 := by
    have hb := (lt_div_iff₀ (by positivity : 0 < 2 * starConstA)).mp hsmall
    nlinarith
  have hqunit : expectationThreshold J n < 1 := by nlinarith
  obtain ⟨L, e, hL, hpos, hmult, hsum, hlen⟩ := star_component_demands J hstar
  have hbudget : 100 * L.sum ≤ n := by
    have hr : (L.sum : ℝ) ≤ (nonisolated J).card := by exact_mod_cast hsum
    have hs : ((nonisolated J).card : ℝ) ≤ (n : ℝ) / 100 := hsupport
    have : (100 : ℝ) * L.sum ≤ n := by linarith
    exact_mod_cast this
  obtain ⟨Y, c, hc, hdistinct, hreserve⟩ := star_host_bins n L.sum hn2 hbudget
  let s : StarRowState ↥Y := ⟨L, Finset.univ⟩
  apply star_containmentThreshold_le_of_component_trials J hstar hsize
    (expectationThreshold J n) hn2 hq hp Y c hc s e hL hdistinct
  · simpa [s] using hreserve
  · exact hpos
  · intro ell hell
    have hm : 0 < starMultiplicity J hstar ell (hpos ell hell) := by
      rw [← hmult ell (hpos ell hell)]
      exact List.count_pos_iff.mpr hell
    exact star_occupied_size_le J hstar n ell (hpos ell hell) hsupport hm
  · intro ell hell
    have hm : 0 < starMultiplicity J hstar ell (hpos ell hell) := by
      rw [← hmult ell (hpos ell hell)]
      exact List.count_pos_iff.mpr hell
    simpa only [s, hmult ell (hpos ell hell)] using
      star_count_lower J hstar n ell (hpos ell hell) hedge hsize hnpos hm hqunit
  · have hr : 2 * (L.length : ℝ) ≤ (nonisolated J).card := by exact_mod_cast hlen
    have hs : ((nonisolated J).card : ℝ) ≤ (n : ℝ) / 100 := hsupport
    change (L.length : ℝ) ≤ (n : ℝ) / 200
    linarith

end Papers.OaiGraphDecompositionsIntegral
