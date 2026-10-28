module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.AssemblyCut
public import Papers.OaiGraphDecompositionsIntegral.Helpers.Thresholds

/-! # Relabelling the deterministic cut pieces for transfer -/

public section

namespace Papers.OaiGraphDecompositionsIntegral

variable {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
open Classical in
-- @node: assembly_map_degree
/-- [Relabelling a graph by an injection preserves the degree of each original vertex](goal). -/
lemma assembly_map_degree {n : ℕ} (J : SimpleGraph V) (f : V ↪ Fin n) (w : V) :
    (J.map f).degree (f w) = J.degree w := by
  classical
  have hset : (J.map f).neighborFinset (f w) = (J.neighborFinset w).map f := by
    ext v
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_map,
      SimpleGraph.map_adj]
    constructor
    · rintro ⟨a, b, hab, ha, hb⟩
      have haw : a = w := f.injective ha
      subst a
      exact ⟨b, hab, hb⟩
    · rintro ⟨b, hab, hb⟩
      exact ⟨w, b, hab, rfl, hb⟩
  simpa only [SimpleGraph.card_neighborFinset_eq_degree, Finset.card_map] using
    congrArg Finset.card hset

open Classical in
-- @node: assembly_map_transfer_configuration
/-- Suppose [the host edge set belongs to the allowed family](hyp:hT),
[the piece lies in the cut of the original graph across the chosen vertex set](hyp:hJG),
and [its injected copy lies in that host](hyp:htypical). If [the chosen set has at most
the host order to the power two-thirds vertices](hyp:hY), [at most c vertices outside
it have positive degree in the piece](hyp:hactive), [c is at most one-eighth of the
host order](hyp:hc), and [every outside vertex has degree at most s](hyp:hdegree),
then [the injected piece and vertex set form a transfer configuration with degree
bound s for the allowed host family](goal). -/
lemma assembly_map_transfer_configuration {n s c : ℕ} (J G : SimpleGraph V)
    (Y : Finset V) (f : V ↪ Fin n) (D : Set (Finset (KEdge n)))
    (T : Finset (KEdge n)) (hT : T ∈ D) (hJG : J ≤ cutSetPiece G Y)
    (htypical : J.map f ≤ graphOfEdges T)
    (hY : (Y.card : ℝ) ≤ (n : ℝ) ^ ((2 : ℝ) / 3))
    (hactive : ((Finset.univ \ Y).filter (fun w => 0 < J.degree w)).card ≤ c)
    (hc : (c : ℝ) ≤ (n : ℝ) / 8)
    (hdegree : ∀ w ∉ Y, J.degree w ≤ s) :
    TransferConfiguration n s D (Y.map f) (J.map f) := by
  classical
  have hpre (w : Fin n) (hw : 0 < (J.map f).degree w) :
      ∃ v, f v = w ∧ 0 < J.degree v := by
    obtain ⟨z, hz⟩ := ((J.map f).degree_pos_iff_exists_adj w).mp hw
    obtain ⟨v, u, hvu, hv, hu⟩ := (SimpleGraph.map_adj f J w z).mp hz
    exact ⟨v, hv, (J.degree_pos_iff_exists_adj v).mpr ⟨u, hvu⟩⟩
  refine ⟨by simpa only [Finset.card_map] using hY, ?_, ⟨T, hT, htypical⟩, ?_, ?_⟩
  · intro u v huv
    obtain ⟨a, b, hab, rfl, rfl⟩ := (SimpleGraph.map_adj f J u v).mp huv
    simpa only [Finset.mem_map, f.injective.eq_iff, exists_eq_right] using (hJG hab).2
  · have hsub : ((Finset.univ \ Y.map f).filter
        (fun w => 0 < (J.map f).degree w)) ⊆
        (((Finset.univ \ Y).filter (fun w => 0 < J.degree w)).map f) := by
      intro w hw
      obtain ⟨v, rfl, hv⟩ := hpre w (Finset.mem_filter.mp hw).2
      have hvY : v ∉ Y := by
        intro hvY
        exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hw).1).2
          (Finset.mem_map.mpr ⟨v, hvY, rfl⟩)
      exact Finset.mem_map.mpr ⟨v, Finset.mem_filter.mpr
        ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hvY⟩, hv⟩, rfl⟩
    have hcard := (Finset.card_le_card hsub).trans
      ((Finset.card_map _).le.trans hactive)
    exact (show (_ : ℝ) ≤ c by exact_mod_cast hcard).trans hc
  · intro w hw
    by_cases hp : 0 < (J.map f).degree w
    · obtain ⟨v, rfl, _⟩ := hpre w hp
      rw [assembly_map_degree]
      apply hdegree v
      intro hv
      exact hw (Finset.mem_map.mpr ⟨v, hv, rfl⟩)
    · omega

omit [DecidableEq V] in
-- @node: containmentThreshold_le_of_copy
/-- If [J embeds as a subgraph of G](hyp:hcopy), [J's vertex set has size at most n](hyp:hJsize),
and [G's vertex set has size at most n](hyp:hGsize), then [the containment threshold
of J in an n-vertex random host is at most that of G](goal). -/
lemma containmentThreshold_le_of_copy {W : Type} [Fintype W]
    (J : SimpleGraph V) (G : SimpleGraph W) (n : ℕ)
    (hcopy : J.IsContained G) (hJsize : Fintype.card V ≤ n)
    (hGsize : Fintype.card W ≤ n) :
    containmentThreshold J n ≤ containmentThreshold G n := by
  classical
  have hnonneg : 0 ≤ containmentThreshold G n := by
    unfold containmentThreshold
    split_ifs
    · rfl
    · exact (containmentThresholdRaw_isLeast G n hGsize).1.1.1
  by_cases heJ : J.edgeSet = ∅
  · simpa only [containmentThreshold, if_pos heJ] using hnonneg
  have heG : G.edgeSet ≠ ∅ := by
    intro heG
    obtain ⟨f⟩ := hcopy
    obtain ⟨e, he⟩ := Set.nonempty_iff_ne_empty.mpr heJ
    have himage := f.toHom.map_mem_edgeSet he
    rw [heG] at himage
    exact himage
  have hprob : containmentProb G n (containmentThresholdRaw G n) ≤
      containmentProb J n (containmentThresholdRaw G n) := by
    apply Causalean.Experimentation.DesignBased.FiniteDesign.Pr_mono
    intro z hz
    exact hcopy.trans hz
  simp only [containmentThreshold, if_neg heJ, if_neg heG]
  exact (containmentThresholdRaw_isLeast J n hJsize).2
    ⟨(containmentThresholdRaw_isLeast G n hGsize).1.1,
      (containmentThresholdRaw_isLeast G n hGsize).1.2.trans hprob⟩

end Papers.OaiGraphDecompositionsIntegral
