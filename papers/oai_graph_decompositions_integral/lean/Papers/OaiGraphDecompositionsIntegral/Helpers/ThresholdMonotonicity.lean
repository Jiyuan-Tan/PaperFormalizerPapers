module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.Thresholds

/-! # Expectation thresholds under edge deletion

A cover for the containment family of a subgraph also covers the smaller
containment family of the original graph.
-/

public section

namespace Papers.OaiGraphDecompositionsIntegral

variable {V : Type} [Fintype V]

-- @node: expectationThreshold_nonneg
/-- If [the number of vertices of G is at most the host order n](hyp:hsize),
[the expectation threshold for G in an n-vertex host is nonnegative](goal). -/
lemma expectationThreshold_nonneg (G : SimpleGraph V) (n : ℕ)
    (hsize : Fintype.card V ≤ n) : 0 ≤ expectationThreshold G n := by
  classical
  by_cases h : G.edgeSet = ∅
  · simp [expectationThreshold, h]
  · have hmem := (expectationThresholdRaw_isGreatest G n
        (Set.nonempty_iff_ne_empty.mpr h) hsize).1.1.1
    simpa only [expectationThreshold, if_neg h] using hmem

-- @node: containmentFamily_antitone
/-- If [G is a subgraph of H on the same vertex set](hyp:hGH), [every
n-vertex host edge set containing a copy of H also contains a copy of G](goal). -/
lemma containmentFamily_antitone {G H : SimpleGraph V} (hGH : G ≤ H) (n : ℕ) :
    containmentFamily H n ⊆ containmentFamily G n := by
  intro F hF
  exact SimpleGraph.IsContained.mono_left hGH hF

-- @node: expectationThreshold_mono
/-- If [G is a subgraph of H on the same vertex set](hyp:hGH) and
[their common number of vertices is at most the host order n](hyp:hsize),
[the expectation threshold for G is at most that for H in an n-vertex host](goal). -/
lemma expectationThreshold_mono {G H : SimpleGraph V} (hGH : G ≤ H) (n : ℕ)
    (hsize : Fintype.card V ≤ n) : expectationThreshold G n ≤ expectationThreshold H n := by
  classical
  by_cases hG : G.edgeSet = ∅
  · simpa only [expectationThreshold, if_pos hG] using expectationThreshold_nonneg H n hsize
  have hH : H.edgeSet ≠ ∅ := by
    intro hH
    apply hG
    exact Set.eq_empty_iff_forall_notMem.mpr (fun e he => by
      have := SimpleGraph.edgeSet_mono hGH he
      simpa only [hH, Set.mem_empty_iff_false] using this)
  have hGmax := expectationThresholdRaw_isGreatest G n
    (Set.nonempty_iff_ne_empty.mpr hG) hsize
  have hHmax := expectationThresholdRaw_isGreatest H n
    (Set.nonempty_iff_ne_empty.mpr hH) hsize
  obtain ⟨C, hcover, hcost⟩ := hGmax.1.2
  have hcovH : Covers C (containmentFamily H n) :=
    fun F hF => hcover F (containmentFamily_antitone hGH n hF)
  have hle := hHmax.2 ⟨hGmax.1.1, C, hcovH, hcost⟩
  simpa only [expectationThreshold, if_neg hG, if_neg hH] using hle

end Papers.OaiGraphDecompositionsIntegral
