module
public import Papers.OaiGraphDecompositionsIntegral.Basic

/-! # A typical union contains a labelled copy -/

public section

namespace Papers.OaiGraphDecompositionsIntegral

variable {V : Type} [Fintype V]

-- @node: thm:typical-cover
/-- Assuming [the discrete convexity cover principle bounding the covering cost of
exceptional families by one half](hyp:hDC_of_gate), suppose [the vertex set is finite](hyp:hfinite),
[n is at least two](hyp:hn), [H has an edge and at most n vertices](hyp:hH),
[r exceeds the integral expectation threshold of H and is less than one](hyp:hr), and
[D has probability at least 1 − 1/K₀ under independent edge selection at density r](hyp:hD).
Then [there is an injective assignment of the vertices of H to the n host vertices such
that the resulting copy's edges are covered by K₀ members of D](goal). -/
theorem typical_cover (hDC_of_gate : DiscreteConvexityCover)
    (n : ℕ) (H : SimpleGraph V) (r : ℝ) (D : Set (Finset (KEdge n)))
    (hfinite : FiniteSimpleGraphs V) (hn : TypicalCoverOrder n)
    (hH : TypicalCoverGraph H n) (hr : TypicalCoverDensity H n r)
    (hD : TypicalCoverMass n r D) :
    ∃ f : V ↪ Fin n, CoveredByMembers K0 D (copyEdges H f) := by
  classical
  obtain ⟨hedge, hsize⟩ := hH
  have hne : H.edgeSet ≠ ∅ := Set.nonempty_iff_ne_empty.mp hedge
  have hq : expectationThreshold H n = expectationThresholdRaw H n := by
    simp [expectationThreshold, hne]
  have hq0 : 0 ≤ expectationThreshold H n := by
    rw [hq]
    exact Real.sSup_nonneg (fun p hp => hp.1.1)
  have hr0 : 0 < r := lt_of_le_of_lt hq0 hr.1
  have hground : DiscreteGround (KEdge n) := by
    have hn' : 2 ≤ n := hn
    exact ⟨⟨s((⟨0, by omega⟩ : Fin n), (⟨1, by omega⟩ : Fin n)), by simp⟩⟩
  by_contra hnone
  have hexceptional : containmentFamily H n ⊆ exceptionalFamily K0 D := by
    intro G hG hcovered
    obtain ⟨f⟩ := hG
    have hsub : copyEdges H f.toEmbedding ⊆ G := by
      intro e he
      have hemap : e.val ∈ (H.map f.toEmbedding).edgeSet :=
        (Finset.mem_filter.mp he).2
      rw [SimpleGraph.edgeSet_map] at hemap
      obtain ⟨a, ha, hea⟩ := hemap
      have hehost : e.val ∈ (graphOfEdges G).edgeSet := by
        rw [← hea]
        exact f.toHom.map_mem_edgeSet ha
      have hex : ∃ h : ¬ e.val.IsDiag, decide ((⟨e.val, h⟩ : KEdge n) ∈ G) = true := by
        have hh := hehost
        simp only [graphOfEdges, hostGraph, SimpleGraph.edgeSet_fromEdgeSet,
          Set.mem_sdiff, Set.mem_ofPred_eq] at hh
        exact hh.1
      obtain ⟨h, hh⟩ := hex
      exact of_decide_eq_true hh
    apply hnone
    exact ⟨f.toEmbedding, hcovered.imp (fun t ht => ⟨ht.1, hsub.trans ht.2⟩)⟩
  obtain ⟨C, hC, hcost⟩ := hDC_of_gate (KEdge n) r D hground ⟨hr0, hr.2⟩ hD
  have hcover : HasCoverOfCostLe (containmentFamily H n) r (1 / 2) :=
    ⟨C, fun A hA => hC A (hexceptional hA), hcost⟩
  have hrq : r ≤ expectationThresholdRaw H n :=
    le_csSup ⟨1, fun p hp => hp.1.2⟩ ⟨⟨hr0.le, hr.2.le⟩, hcover⟩
  exact (not_le_of_gt hr.1) (hq ▸ hrq)

end Papers.OaiGraphDecompositionsIntegral
