module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.AssemblyQuantities
public import Papers.OaiGraphDecompositionsIntegral.Helpers.DegreeLayers

/-! # The deterministic high-degree closure in the main decomposition

Adding a vertex with more than twice the degeneracy many neighbors in the
current set preserves an edge-count invariant. A maximal such set is closed,
and the degeneracy edge bound controls its size.
-/

public section

namespace Papers.OaiGraphDecompositionsIntegral

open scoped BigOperators

variable {V : Type} [Fintype V] [DecidableEq V]

/-- If [v does not belong to S](hyp:hv), then [the number of edges induced
by S plus the number of neighbors of v in S is at most the number of
edges induced after adding v to S](goal). -/
-- @node: induced_edges_insert_lower
lemma induced_edges_insert_lower (H : SimpleGraph V) [DecidableRel H.Adj]
    (S : Finset V) (v : V) (hv : v ∉ S) :
    (H.induce (S : Set V)).edgeFinset.card + (H.neighborFinset v ∩ S).card ≤
      (H.induce (↑(insert v S) : Set V)).edgeFinset.card := by
  classical
  let A := H.edgeFinset ∩ S.sym2
  let B := (H.neighborFinset v ∩ S).image (fun w => s(v, w))
  have hA : A.card = (H.induce (S : Set V)).edgeFinset.card := by
    have h := congrArg Finset.card (H.map_edgeFinset_induce (s := (S : Set V)))
    simp at h
    convert h.symm using 1
    congr 1
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
    rfl
  have hB : B.card = (H.neighborFinset v ∩ S).card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb hab
    rcases Sym2.eq_iff.mp hab with h | h
    · exact h.2
    · exact h.2.trans h.1
  have hd : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro e heA heB
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp heB
    have := (Finset.mem_inter.mp heA).2
    exact hv (by simpa using (Finset.mk_mem_sym2_iff.mp this).1)
  have hsub : A ∪ B ⊆ H.edgeFinset ∩ (insert v S).sym2 := by
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨hedge, hs⟩ := Finset.mem_inter.mp he
      exact Finset.mem_inter.mpr ⟨hedge, Finset.sym2_mono (Finset.subset_insert _ _) hs⟩
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hadj, hwS⟩ := Finset.mem_inter.mp hw
      exact Finset.mem_inter.mpr ⟨by simpa using hadj,
        Finset.mk_mem_sym2_iff.mpr ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hwS⟩⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd, hA, hB] at hcard
  have heq := congrArg Finset.card
    (H.map_edgeFinset_induce (s := (↑(insert v S) : Set V)))
  simp at heq
  have h := hcard.trans_eq heq.symm
  convert h using 1
  congr 1
  ext e
  simp only [SimpleGraph.mem_edgeFinset]
  rfl

/-- Suppose [d is positive](hyp:hdpos), [H has degeneracy at most d](hyp:hd),
[Y contains the seed set Y₀](hyp:hsub), and [the number of edges induced
by Y is at least 2d times the number of vertices in Y outside Y₀](hyp:hinv).
Then [Y has at most twice as many vertices as Y₀](goal). -/
-- @node: high_degree_closure_size_of_invariant
lemma high_degree_closure_size_of_invariant (H : SimpleGraph V) [DecidableRel H.Adj]
    (d : ℕ) (hdpos : 0 < d) (hd : degeneracy H ≤ d)
    (Y₀ Y : Finset V) (hsub : Y₀ ⊆ Y)
    (hinv : 2 * d * (Y \ Y₀).card ≤ (H.induce (Y : Set V)).edgeFinset.card) :
    Y.card ≤ 2 * Y₀.card := by
  classical
  have he := degree_edges_supported d Finset.univ (H.induce (Y : Set V))
    ((degeneracy_induce_le H Y).trans hd) (by simp)
  have he' : (H.induce (Y : Set V)).edgeFinset.card ≤ d * Y.card := by
    simp only [Finset.card_univ] at he
    convert he using 1
    · congr 1
      ext e
      simp only [SimpleGraph.mem_edgeFinset]
    · simp
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  nlinarith

/-- If [d is positive](hyp:hdpos) and [H has degeneracy at most d](hyp:hd),
then [any seed set Y₀ can be extended to a set Y of at most twice its
size such that every vertex outside Y has at most 2d neighbors in Y](goal). -/
-- @node: high_degree_closure_exists
lemma high_degree_closure_exists (H : SimpleGraph V) [DecidableRel H.Adj]
    (d : ℕ) (hdpos : 0 < d) (hd : degeneracy H ≤ d) (Y₀ : Finset V) :
    ∃ Y : Finset V, Y₀ ⊆ Y ∧ Y.card ≤ 2 * Y₀.card ∧
      ∀ v ∉ Y, (H.neighborFinset v ∩ Y).card ≤ 2 * d := by
  classical
  let F := Finset.univ.filter (fun Y : Finset V => Y₀ ⊆ Y ∧
    2 * d * (Y \ Y₀).card ≤ (H.induce (Y : Set V)).edgeFinset.card)
  have hF : F.Nonempty := by
    refine ⟨Y₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    simp
  obtain ⟨Y, hY, hmax⟩ := F.exists_max_image Finset.card hF
  obtain ⟨hsub, hinv⟩ := (Finset.mem_filter.mp hY).2
  refine ⟨Y, hsub, high_degree_closure_size_of_invariant H d hdpos hd Y₀ Y hsub hinv, ?_⟩
  intro v hv
  by_contra hlarge
  have hv₀ : v ∉ Y₀ := fun h => hv (hsub h)
  have hdiff : (insert v Y \ Y₀).card = (Y \ Y₀).card + 1 := by
    rw [Finset.insert_sdiff_of_notMem _ hv₀, Finset.card_insert_of_notMem]
    exact fun h => hv (Finset.mem_sdiff.mp h).1
  have hnew : insert v Y ∈ F := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hsub.trans (Finset.subset_insert _ _), ?_⟩
    have he := induced_edges_insert_lower H Y v hv
    rw [hdiff]
    nlinarith
  have hmax' := hmax (insert v Y) hnew
  rw [Finset.card_insert_of_notMem hv] at hmax'
  omega

omit [DecidableEq V] in
/-- If [H has degeneracy at most d](hyp:hd), [n is positive](hyp:hn), and
[H has at most n vertices](hyp:hV), then [the number of vertices of H
with degree greater than the square root of n is at most 2d times the
square root of n](goal). -/
-- @node: initial_high_degree_card_le
lemma initial_high_degree_card_le (H : SimpleGraph V)
    (d n : ℕ) (hd : degeneracy H ≤ d) (hn : 0 < n)
    (hV : Fintype.card V ≤ n) :
    ((initialHighDegreeSet H n).card : ℝ) ≤ 2 * d * Real.sqrt n := by
  classical
  have hsum := degree_sum_le_of_degeneracy H d hd
  have hsum' : (∑ v, (H.degree v : ℝ)) ≤ 2 * d * n := by
    exact_mod_cast hsum.trans (Nat.mul_le_mul_left (2 * d) hV)
  have hlarge : ((initialHighDegreeSet H n).card : ℝ) * Real.sqrt n ≤
      ∑ v ∈ initialHighDegreeSet H n, (H.degree v : ℝ) := by
    calc
      _ = ∑ _v ∈ initialHighDegreeSet H n, Real.sqrt n := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro v hv
        exact (Finset.mem_filter.mp hv).2.le
  have hsub : (∑ v ∈ initialHighDegreeSet H n, (H.degree v : ℝ)) ≤
      ∑ v, (H.degree v : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hsquare := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  have hprod := hlarge.trans (hsub.trans hsum')
  have heq : (2 * (d : ℝ) * Real.sqrt n) * Real.sqrt n = 2 * d * n := by
    nlinarith
  rw [← heq] at hprod
  exact (mul_le_mul_iff_left₀ hsqrt).mp hprod

open Classical in
/-- If [d is positive](hyp:hdpos), [H has degeneracy at most d](hyp:hd),
[n is positive](hyp:hn), and [H has at most n vertices](hyp:hV), then
[there is a set Y containing every vertex of degree greater than the
square root of n, with size at most 4d times that square root, such that
every vertex outside Y has degree at most that square root and at most
2d neighbors in Y](goal). -/
-- @node: assembly_high_degree_set_exists
lemma assembly_high_degree_set_exists (H : SimpleGraph V)
    (d n : ℕ) (hdpos : 0 < d) (hd : degeneracy H ≤ d) (hn : 0 < n)
    (hV : Fintype.card V ≤ n) :
    ∃ Y : Finset V, initialHighDegreeSet H n ⊆ Y ∧
      (Y.card : ℝ) ≤ 4 * d * Real.sqrt n ∧
      ∀ v ∉ Y, (H.degree v : ℝ) ≤ Real.sqrt n ∧
        (H.neighborFinset v ∩ Y).card ≤ 2 * d := by
  classical
  obtain ⟨Y, hsub, hsize, hout⟩ :=
    high_degree_closure_exists H d hdpos hd (initialHighDegreeSet H n)
  refine ⟨Y, hsub, ?_, ?_⟩
  · have hseed := initial_high_degree_card_le H d n hd hn hV
    have hsize' : (Y.card : ℝ) ≤ 2 * (initialHighDegreeSet H n).card := by
      exact_mod_cast hsize
    linarith
  · intro v hv
    refine ⟨?_, hout v hv⟩
    apply le_of_not_gt
    intro hlarge
    apply hv
    exact hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlarge⟩)

end Papers.OaiGraphDecompositionsIntegral
