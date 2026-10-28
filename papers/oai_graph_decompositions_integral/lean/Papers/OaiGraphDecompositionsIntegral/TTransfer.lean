module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.Compression
public import Papers.OaiGraphDecompositionsIntegral.Helpers.Hoeffding
public import Papers.OaiGraphDecompositionsIntegral.Helpers.Hall
public import Papers.OaiGraphDecompositionsIntegral.Helpers.Thresholds
public import Papers.OaiGraphDecompositionsIntegral.Helpers.TransferEmbedding
public import Toolkit.Foundations.Probability.BiasedCube
public import Mathlib.Combinatorics.Hall.Basic

/-! # Transfer from a typical source family to a denser host -/

public section

namespace Papers.OaiGraphDecompositionsIntegral

-- @node: prop:transfer
/-- [There is an absolute host-order cutoff such that, for every n above it and parameters
with r strictly between zero and one, s ≤ 10 log n, and r raised to s ≥ n to the power
−1/100, the source test family has probability at least 1 − 1/K₀ at density r.
For every Y of size at most n to the power 2/3 and graph J contained in a member of
that family, with every edge crossing Y, at most n/8 nonisolated vertices outside Y,
and degree at most s outside Y, the containment threshold of J is at most
1 − (1 − r)³², which is at most 32r](goal). -/
theorem transfer :
    ∃ N₁ : ℕ, -- @realizes N_1(absolute vertex cutoff, before all varying parameters)
      ∀ (n : ℕ) (r : ℝ) (s : ℕ), FiniteSimpleGraphs (Fin n) →
        TransferOrder N₁ n → TransferParameters n r s →
        let D := sourceTestFamily n r s
        1 - 1 / (K0 : ℝ) ≤ muMass (KEdge n) r D ∧
        ∀ (Y : Finset (Fin n)) (J : SimpleGraph (Fin n)) [DecidableRel J.Adj],
          TransferConfiguration n s D Y J →
          containmentThreshold J n ≤ targetDensity r ∧ targetDensity r ≤ 32 * r := by
  classical
  obtain ⟨Nc, hNc⟩ := transfer_concentration_cutoff
  obtain ⟨Ne, hNe⟩ := transfer_simultaneous_events
  refine ⟨max Nc Ne, ?_⟩
  intro n r s _ hn hp
  have hnc : Nc ≤ n := (le_max_left Nc Ne).trans hn
  have hne : Ne ≤ n := (le_max_right Nc Ne).trans hn
  obtain ⟨hhalf, _⟩ := hNc n hnc
  obtain ⟨hmass, htarget⟩ := hNe n r s hne hp
  refine ⟨hmass, ?_⟩
  intro Y J _ hconfiguration
  have hunit := targetDensity_mem_Icc hp.1.le hp.2.1.le
  refine ⟨?_, targetDensity_le_mul hp.1.le hp.2.1.le⟩
  have hprob : (1 / 2 : ℝ) ≤ containmentProb J n (targetDensity r) := by
    apply htarget.trans
    apply Causalean.Experimentation.DesignBased.FiniteDesign.Pr_mono
    intro z hz
    exact transfer_containsCopy hp Y J hconfiguration
      (hhalf Y hconfiguration.1) (hostGraph z) hz
  unfold containmentThreshold
  split_ifs
  · exact hunit.1
  · exact (containmentThresholdRaw_isLeast J n (by simp)).2 ⟨hunit, hprob⟩

end Papers.OaiGraphDecompositionsIntegral
