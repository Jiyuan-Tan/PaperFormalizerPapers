module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.Thresholds
public import Papers.OaiGraphDecompositionsIntegral.Helpers.DegreeEmbeddingAssembly
public import Papers.OaiGraphDecompositionsIntegral.Helpers.DegreeLayers
public import Papers.OaiGraphDecompositionsIntegral.Helpers.DegreeNumerics
public import Papers.OaiGraphDecompositionsIntegral.Helpers.DegreeLayerSetup
public import Papers.OaiGraphDecompositionsIntegral.Helpers.DegreeHallLayer
public import Papers.OaiGraphDecompositionsIntegral.Helpers.DegreeAdaptiveLayers
public import Toolkit.Foundations.Probability.BiasedCube
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-! # Direct embedding for bounded degeneracy and maximum degree -/

public section

namespace Papers.OaiGraphDecompositionsIntegral

-- @node: prop:degree-embedding
/-- [There is an absolute host-order cutoff such that, for every n above it and parameters
with r strictly between zero and one, s ≤ 10 log n, and r raised to s ≥ n to the power
−1/100, every finite simple graph on at most n vertices, with at most n/4 nonisolated
vertices, degeneracy at most s, and maximum degree at most n to the power 2/3,
has containment threshold at most r](goal). -/
theorem degree_embedding :
    ∃ N₂ : ℕ, -- @realizes N_2(absolute vertex cutoff)
      ∀ (n : ℕ) (r : ℝ) (s : ℕ),
        DegreeEmbeddingOrder N₂ n → TransferParameters n r s →
      ∀ (V : Type) [Fintype V] [DecidableEq V]
        (J : SimpleGraph V) [DecidableRel J.Adj],
        FiniteSimpleGraphs V → DegreeEmbeddingBounds J n s → DegreeEmbeddingSize V n →
        containmentThreshold J n ≤ r := by
  classical
  obtain ⟨N, hN⟩ := degree_embedding_probability
  refine ⟨N, ?_⟩
  intro n r s hn hp V _ _ J _ _ hb hsize
  by_cases hedge : J.edgeSet = ∅
  · simpa only [containmentThreshold, if_pos hedge] using hp.1.le
  · have hhalf := hN n r s hn hp V J hsize hb
      (Set.nonempty_iff_ne_empty.mpr hedge)
    have hleast := containmentThresholdRaw_isLeast J n hsize
    have hle := hleast.2 ⟨⟨hp.1.le, hp.2.1.le⟩, hhalf⟩
    simpa only [containmentThreshold, if_neg hedge] using hle

end Papers.OaiGraphDecompositionsIntegral
