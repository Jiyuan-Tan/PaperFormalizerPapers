module
public import Papers.OaiGraphDecompositionsIntegral.TTypicalCover
public import Papers.OaiGraphDecompositionsIntegral.TTransfer
public import Papers.OaiGraphDecompositionsIntegral.TDegreeEmbedding
public import Papers.OaiGraphDecompositionsIntegral.TStars
public import Papers.OaiGraphDecompositionsIntegral.Helpers.QLower
public import Papers.OaiGraphDecompositionsIntegral.Helpers.Degeneracy
public import Papers.OaiGraphDecompositionsIntegral.Helpers.ForestSplitting
public import Papers.OaiGraphDecompositionsIntegral.Helpers.AssemblyQuantities
public import Papers.OaiGraphDecompositionsIntegral.Helpers.AssemblyParameters
public import Papers.OaiGraphDecompositionsIntegral.Helpers.HighDegreeClosure
public import Papers.OaiGraphDecompositionsIntegral.Helpers.BoundedDegeneracy
public import Papers.OaiGraphDecompositionsIntegral.Helpers.AssemblyPartitions
public import Papers.OaiGraphDecompositionsIntegral.Helpers.AssemblyInside
public import Papers.OaiGraphDecompositionsIntegral.Helpers.AssemblyOutside
public import Papers.OaiGraphDecompositionsIntegral.Helpers.AssemblyCover
public import Papers.OaiGraphDecompositionsIntegral.Helpers.AssemblyTransfer
public import Papers.OaiGraphDecompositionsIntegral.Helpers.AssemblyRefine
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-! # An absolute finite edge decomposition with controlled thresholds -/

public section

namespace Papers.OaiGraphDecompositionsIntegral

-- @node: thm:main
/-- Assuming [the discrete convexity cover principle, which bounds the covering cost
of the exceptional family by one half whenever the original family has probability
at least 1 − 1/K₀](hyp:hDC_of_gate), [there exist absolute constants k ≥ 2 and L ≥ 1
such that every finite simple graph H on at most n vertices, with n ≥ 2, admits k
subgraphs whose edges partition those of H and each of whose containment thresholds
in an n-vertex random host is at most L times the integral expectation threshold of H](goal). -/
theorem main (hDC_of_gate : DiscreteConvexityCover) :
    ∃ k : ℕ, 2 ≤ k ∧ -- @realizes k(absolute integer piece count, at least two)
    ∃ L : ℝ, 1 ≤ L ∧ -- @realizes L(absolute comparison constant, at least one)
      ∀ (n : ℕ) (V : Type) [Fintype V] [DecidableEq V]
        (H : SimpleGraph V), -- @realizes H(finite simple target graph)
        FiniteSimpleGraphs V → MainOrder n → MainGraphSize V n →
        ∃ P : Fin k → SimpleGraph V, -- @realizes H_i(deterministic edge pieces on V)
          (∀ i, P i ≤ H) ∧
          (∀ e ∈ H.edgeSet, ∃! i, e ∈ (P i).edgeSet) ∧
          ∀ i, containmentThreshold (P i) n ≤ L * expectationThreshold H n := by
  classical
  obtain ⟨N₁, htransfer⟩ := transfer
  obtain ⟨N₂, hdegree⟩ := degree_embedding
  obtain ⟨N₃, hstars⟩ := stars
  obtain ⟨Nb, hNb, hbounded⟩ := bounded_degeneracy_threshold_partition
  obtain ⟨n₀, hcut⟩ := assembly_cutoff_exists N₁ N₂ (max N₃ Nb)
  let k := 2 * K0 * assemblySplittingFactor * (assemblyBlockCount + 1) ^ 2
  let L : ℝ := max (max (2 * starConstA) 64) ((n₀ : ℝ) ^ 2)
  have hk : 2 ≤ k := by
    norm_num [k, K0, assemblySplittingFactor, assemblyBlockCount]
  have hLA : 2 * starConstA ≤ L := (le_max_left _ _).trans (le_max_left _ _)
  have hL64 : (64 : ℝ) ≤ L := (le_max_right _ _).trans (le_max_left _ _)
  have hLN : (n₀ : ℝ) ^ 2 ≤ L := le_max_right _ _
  have hL : 1 ≤ L := le_trans (by norm_num) hL64
  refine ⟨k, hk, L, hL, ?_⟩
  intro n V _ _ H hfinite hn hsize
  have hsize' : Fintype.card V ≤ n := hsize
  have hn' : 2 ≤ n := hn
  have hqnonneg := expectationThreshold_nonneg H n hsize'
  by_cases he : H.edgeSet = ∅
  · refine ⟨fun _ => ⊥, fun _ => bot_le, ?_, ?_⟩
    · intro e he'
      simp [he] at he'
    · intro i
      simp [containmentThreshold, expectationThreshold, he]
  have hedge : H.edgeSet.Nonempty := Set.nonempty_iff_ne_empty.mpr he
  by_cases hnsmall : n < n₀
  · exact edge_partition_single H n k _ (by omega) hsize'
      (assembly_small_order_comparison H n n₀ L hedge hn' hsize' hnsmall hLN)
  have hnlarge : n₀ ≤ n := by omega
  by_cases hqbig : 1 / (2 * starConstA) ≤ expectationThreshold H n
  · apply edge_partition_single H n k _ (by omega) hsize'
    have hApos : 0 < 2 * starConstA := by unfold starConstA; positivity
    have hunit := (div_le_iff₀ hApos).mp hqbig
    calc
      1 ≤ (2 * starConstA) * expectationThreshold H n := by nlinarith
      _ ≤ L * expectationThreshold H n := mul_le_mul_of_nonneg_right hLA hqnonneg
  have hqsmall : expectationThreshold H n < 1 / (2 * starConstA) := lt_of_not_ge hqbig
  have hdpos : 0 < degeneracy H := degeneracy_pos_of_edge H hedge
  by_cases hdsmall : degeneracy H < assemblySplittingFactor
  · have hNbn : Nb ≤ n := (le_max_right N₃ Nb).trans (hcut.2.2.2.1.trans hnlarge)
    obtain ⟨P, hP, hpart, hbound⟩ := hbounded n hNbn V H (degeneracy H)
      hdpos le_rfl hsize'
    refine edge_partition_pad H n k _ (mul_nonneg (by linarith) hqnonneg) ?_ P hP hpart ?_
    · simp only [Fintype.card_prod, Fintype.card_fin, Sym2.card]
      norm_num [assemblyBlockCount, assemblySplittingFactor, k, K0,
        Nat.choose_two_right] at hdsmall ⊢
      omega
    · intro i
      exact (hbound i).trans (mul_le_mul_of_nonneg_right hLA hqnonneg)
  have hdlarge : assemblySplittingFactor ≤ degeneracy H := by omega
  let r := 2 * expectationThreshold H n
  let s := ⌈2 * (degeneracy H : ℝ) / assemblySplittingFactor⌉₊
  obtain ⟨hspos, hsupper, hdlog, hrhalf, hparameters⟩ :=
    assembly_graph_parameters H n hfinite hn' hsize' hedge hdlarge hqsmall
  obtain ⟨hlogcut, hsupportcut, hblockcut⟩ := hcut.2.2.2.2 n hnlarge
  obtain ⟨Y, hseed, hY, houtside⟩ := assembly_high_degree_set_small H n
    (degeneracy H) hdpos le_rfl (by omega) hsize' hdlog hlogcut
  have hN₁n : N₁ ≤ n := hcut.2.1.trans hnlarge
  have hN₂n : N₂ ≤ n := hcut.2.2.1.trans hnlarge
  obtain ⟨hmass, htrans⟩ := htransfer n r s
    (by change Finite (Fin n); infer_instance) hN₁n hparameters
  have hqpos : 0 < expectationThreshold H n := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hlower := (q_lower H n hfinite hedge hsize').2
    exact (mul_pos (by norm_num : (0 : ℝ) < 1 / 2)
      (Real.rpow_pos_of_pos hnpos _)).trans_le hlower
  obtain ⟨f, hcovered⟩ := typical_cover hDC_of_gate n H r
    (sourceTestFamily n r s) hfinite hn' ⟨hedge, hsize'⟩
    ⟨by dsimp [r]; linarith, hparameters.2.1⟩ hmass
  -- Each initial piece can now have its inside-Y edges processed without
  -- any further random choice or statistical input.
  have hinside (G : SimpleGraph V) (hG : G ≤ H) :
      ∃ P : Fin assemblySplittingFactor → SimpleGraph V,
        (∀ i, P i ≤ insideSetPiece G Y) ∧
        (∀ e ∈ (insideSetPiece G Y).edgeSet, ∃! i, e ∈ (P i).edgeSet) ∧
        ∀ i, containmentThreshold (P i) n ≤ r := by
    obtain ⟨P, hP, hpart, hbounds⟩ :=
      assembly_inside_partition_bounds H G Y n hG hY hsupportcut
    refine ⟨P, hP, hpart, ?_⟩
    intro i
    exact hdegree n r s hN₂n hparameters V (P i)
      (by change Finite V; infer_instance) (hbounds i) hsize'
  obtain ⟨block, hblock⟩ := balanced_vertex_blocks n assemblyBlockCount
    (by norm_num [assemblyBlockCount]) hsize'
  have hblocksmall : (2 : ℝ) * ⌈(n : ℝ) / assemblyBlockCount⌉₊ ≤ (n : ℝ) / 100 := by
    rw [natCast_ceil_eq_intCast_ceil (by positivity)]
    exact hblockcut
  have houtsidePieces (G : SimpleGraph V) (hG : G ≤ H) :
      ∃ P : Sym2 (Fin assemblyBlockCount) × Fin assemblySplittingFactor → SimpleGraph V,
        (∀ i, P i ≤ insideSetPiece G (Finset.univ \ Y)) ∧
        (∀ e ∈ (insideSetPiece G (Finset.univ \ Y)).edgeSet,
          ∃! i, e ∈ (P i).edgeSet) ∧
        ∀ i, containmentThreshold (P i) n ≤ r := by
    obtain ⟨P, hP, hpart, hbounds⟩ := assembly_outside_partition_bounds H G Y n
      assemblyBlockCount _ block hG hblock (fun v hv => (houtside v hv).1)
      (by omega) hblocksmall
    refine ⟨P, hP, hpart, ?_⟩
    intro i
    exact hdegree n r s hN₂n hparameters V (P i)
      (by change Finite V; infer_instance) (hbounds i) hsize'
  obtain ⟨T, G, hT, hG, hGpart, hGlabel⟩ := covered_copy_edge_partition
    (by norm_num [K0]) H f (sourceTestFamily n r s) hcovered
  have hrR : r ≤ L * expectationThreshold H n := by
    dsimp only [r]
    exact mul_le_mul_of_nonneg_right (by linarith : (2 : ℝ) ≤ L) hqnonneg
  have htR : targetDensity r ≤ L * expectationThreshold H n := by
    apply (targetDensity_le_mul hparameters.1.le hparameters.2.1.le).trans
    calc
      32 * (2 * expectationThreshold H n) = 64 * expectationThreshold H n := by ring
      _ ≤ L * expectationThreshold H n := mul_le_mul_of_nonneg_right hL64 hqnonneg
  have hcutPieces (i : Fin K0) :
      ∃ P : Fin assemblyBlockCount × Fin assemblySplittingFactor → SimpleGraph V,
        (∀ j, P j ≤ cutSetPiece (G i) Y) ∧
        (∀ e ∈ (cutSetPiece (G i) Y).edgeSet, ∃! j, e ∈ (P j).edgeSet) ∧
        ∀ j, containmentThreshold (P j) n ≤ L * expectationThreshold H n := by
    obtain ⟨P, hP, hpart, hactive, hdeg⟩ := assembly_cut_partition_bounds H (G i) Y
      assemblyBlockCount assemblySplittingFactor s _ block (hG i)
      (by norm_num [assemblySplittingFactor]) hblock
      (fun w hw => ((houtside w hw).2).trans (assembly_split_capacity _))
    refine ⟨P, hP, hpart, ?_⟩
    intro j
    have hlabel : (P j).map f ≤ graphOfEdges (T i) :=
      ((SimpleGraph.map_monotone f) ((hP j).trans (cutSetPiece_le _ _))).trans (hGlabel i)
    have hconf := assembly_map_transfer_configuration (P j) (G i) Y f
      (sourceTestFamily n r s) (T i) (hT i) (hP j) hlabel hY (hactive j)
      (by linarith [hblocksmall]) (hdeg j)
    have hbound := (htrans (Y.map f) ((P j).map f) hconf).1
    exact ((containmentThreshold_le_of_copy (P j) ((P j).map f) n
      ⟨(SimpleGraph.Embedding.map f (P j)).toCopy⟩ hsize' (by simp)).trans hbound).trans htR
  have hlocal (i : Fin K0) :
      ∃ P : Fin assemblySplittingFactor ⊕
          ((Sym2 (Fin assemblyBlockCount) × Fin assemblySplittingFactor) ⊕
            (Fin assemblyBlockCount × Fin assemblySplittingFactor)) → SimpleGraph V,
        (∀ j, P j ≤ G i) ∧
        (∀ e ∈ (G i).edgeSet, ∃! j, e ∈ (P j).edgeSet) ∧
        ∀ j, containmentThreshold (P j) n ≤ L * expectationThreshold H n := by
    apply edge_partition_regions (G i) Y n (L * expectationThreshold H n)
    · obtain ⟨P, hP, hp, hb⟩ := hinside (G i) (hG i)
      exact ⟨P, hP, hp, fun j => (hb j).trans hrR⟩
    · obtain ⟨P, hP, hp, hb⟩ := houtsidePieces (G i) (hG i)
      exact ⟨P, hP, hp, fun j => (hb j).trans hrR⟩
    · exact hcutPieces i
  choose P hP hpart hb using hlocal
  obtain ⟨Q, hQ, hQpart, hQbound⟩ := edge_partition_refine H n
    (L * expectationThreshold H n) G P hG hGpart hP hpart hb
  apply edge_partition_pad H n k _ (mul_nonneg (by linarith) hqnonneg) _ Q hQ hQpart hQbound
  simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, Sym2.card]
  norm_num [k, K0, assemblySplittingFactor, assemblyBlockCount, Nat.choose_two_right]

end Papers.OaiGraphDecompositionsIntegral
