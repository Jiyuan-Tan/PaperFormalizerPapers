module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.StarsExtraction
public import Papers.OaiGraphDecompositionsIntegral.Helpers.Thresholds
public import Mathlib.Data.Fintype.Sum

/-! # Embedding star components into the extracted host packing -/

public section

namespace Papers.OaiGraphDecompositionsIntegral

attribute [local instance] Classical.propDecidable

/-- Suppose [the source graph is a star forest](hyp:hstar), [a chosen source
component has at least two vertices](hyp:hC), [the host center is outside
the chosen leaf set](hyp:ha), [the component has one more vertex than that
leaf set](hyp:hcard), and [every chosen leaf is adjacent to the host center](hyp:hedges).
Then [there is an injective map from the component into the host center and
leaves that preserves every source edge](goal). -/
-- @node: star_component_embedding
lemma star_component_embedding {V W : Type} [Fintype V] [DecidableEq V] [DecidableEq W]
    (J : SimpleGraph V) (hstar : IsStarForest J) (G : SimpleGraph W)
    (C : J.ConnectedComponent) (hC : 2 ≤ C.supp.ncard)
    (a : W) (L : Finset W) (ha : a ∉ L)
    (hcard : C.supp.ncard = L.card + 1)
    (hedges : ∀ x ∈ L, G.Adj a x) :
    ∃ f : C.supp → W, Function.Injective f ∧
      (∀ v, f v ∈ insert a L) ∧
      ∀ u v, J.Adj u.val v.val → G.Adj (f u) (f v) := by
  classical
  obtain ⟨c, hc, hadj⟩ := hstar.components C
    (Set.one_lt_ncard_iff_nontrivial.mp (by omega))
  have hecard : (C.supp.toFinset.erase c).card = L.card := by
    rw [Finset.card_erase_of_mem (Set.mem_toFinset.mpr hc),
      ← Set.ncard_eq_toFinset_card', hcard]
    omega
  let e := Finset.equivOfCardEq hecard
  let f : C.supp → W := fun v => if h : v.val = c then a
    else (e ⟨v.val, Finset.mem_erase.mpr ⟨h, Set.mem_toFinset.mpr v.property⟩⟩).val
  have hfc (v : C.supp) (hv : v.val = c) : f v = a := by simp [f, hv]
  have hfleaf (v : C.supp) (hv : v.val ≠ c) : f v ∈ L := by
    simpa only [f, dif_neg hv] using
      (e ⟨v.val, Finset.mem_erase.mpr ⟨hv, Set.mem_toFinset.mpr v.property⟩⟩).property
  refine ⟨f, ?_, ?_, ?_⟩
  · intro u v huv
    by_cases hu : u.val = c
    · by_cases hv : v.val = c
      · exact Subtype.ext (hu.trans hv.symm)
      · exact (ha (by rw [← hfc u hu, huv]; exact hfleaf v hv)).elim
    · by_cases hv : v.val = c
      · exact (ha (by rw [← hfc v hv, ← huv]; exact hfleaf u hu)).elim
      · have he : e ⟨u.val, Finset.mem_erase.mpr ⟨hu, Set.mem_toFinset.mpr u.property⟩⟩ =
            e ⟨v.val, Finset.mem_erase.mpr ⟨hv, Set.mem_toFinset.mpr v.property⟩⟩ := by
          apply Subtype.ext
          simpa only [f, dif_neg hu, dif_neg hv] using huv
        exact Subtype.ext (congrArg (fun x : ↥(C.supp.toFinset.erase c) => x.val) (e.injective he))
  · intro v
    by_cases hv : v.val = c
    · simp [hfc v hv]
    · exact Finset.mem_insert_of_mem (hfleaf v hv)
  · intro u v huv
    obtain ⟨hne, hcenter⟩ := (hadj u.val u.property v.val v.property).mp huv
    rcases hcenter with hu | hv
    · rw [hfc u hu]
      exact hedges (f v) (hfleaf v (by intro hv; exact hne (hu.trans hv.symm)))
    · rw [hfc v hv]
      exact (hedges (f u) (hfleaf u (by intro hu; exact hne (hu.trans hv.symm)))).symm

/-- If [a vertex is nonisolated](hyp:hv), then [its connected component has
at least two vertices](goal). -/
-- @node: star_vertex_component_nontrivial
lemma star_vertex_component_nontrivial {V : Type} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) [DecidableRel J.Adj] (v : V) (hv : v ∈ nonisolated J) :
    2 ≤ (J.connectedComponentMk v).supp.ncard := by
  classical
  obtain ⟨w, hw⟩ := (J.degree_pos_iff_exists_adj v).mp (Finset.mem_filter.mp hv).2
  rw [Set.ncard_eq_toFinset_card']
  apply Finset.one_lt_card_iff.mpr
  exact ⟨v, w, Set.mem_toFinset.mpr rfl,
    Set.mem_toFinset.mpr ((J.connectedComponentMk v).mem_supp_of_adj_mem_supp rfl hw), hw.ne⟩

/-- Suppose [the source graph is a star forest](hyp:hstar) and [its vertex
count is at most the host size n](hyp:hsize). Given [an assignment of a host
center and leaf set to each nontrivial source component](hyp:S), if [each
component has one more vertex than its assigned leaf set](hyp:hcard),
[different components receive disjoint vertex supports](hyp:hdis), and
[each assigned center is outside its leaves and adjacent to every leaf](hyp:hstars),
then [the host contains a copy of the entire source graph](goal).

Isolated vertices are included by extending the injection from the
nonisolated vertices. -/
-- @node: star_forest_containsCopy_of_component_packing
lemma star_forest_containsCopy_of_component_packing {V : Type}
    [Fintype V] [DecidableEq V] (J : SimpleGraph V) [DecidableRel J.Adj]
    (hstar : IsStarForest J) {n : ℕ} (hsize : Fintype.card V ≤ n)
    (G : SimpleGraph (Fin n))
    (S : {C : J.ConnectedComponent // 2 ≤ C.supp.ncard} →
      Fin n × Finset (Fin n))
    (hcard : ∀ i, i.val.supp.ncard = (S i).2.card + 1)
    (hdis : ∀ i j, i ≠ j → Disjoint (centeredStarSupport (S i))
      (centeredStarSupport (S j)))
    (hstars : ∀ i, (S i).1 ∉ (S i).2 ∧ ∀ x ∈ (S i).2, G.Adj (S i).1 x) :
    ContainsCopy J G := by
  classical
  let I := {C : J.ConnectedComponent // 2 ≤ C.supp.ncard}
  have hex (i : I) := star_component_embedding J hstar G i.val i.property
    (S i).1 (S i).2 (hstars i).1 (hcard i) (hstars i).2
  choose g hginj hgrange hgadj using hex
  obtain ⟨base⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card V ≤ Fintype.card (Fin n) by simpa using hsize)
  let idx (v : V) (hv : v ∈ nonisolated J) : I :=
    ⟨J.connectedComponentMk v, star_vertex_component_nontrivial J v hv⟩
  let f : V → Fin n := fun v => if hv : v ∈ nonisolated J then
    g (idx v hv) ⟨v, rfl⟩ else base v
  have hfeval (i : I) (v : V) (hv : v ∈ nonisolated J) (hi : v ∈ i.val.supp) :
      f v = g i ⟨v, hi⟩ := by
    have he : idx v hv = i := Subtype.ext hi
    simp only [f, dif_pos hv]
    cases he
    rfl
  have hfinj : Set.InjOn f (nonisolated J : Set V) := by
    intro v hv w hw he
    let i := idx v hv
    let j := idx w hw
    have hvC : v ∈ i.val.supp := rfl
    have hwC : w ∈ j.val.supp := rfl
    by_cases hij : i = j
    · have hwI : w ∈ i.val.supp := hij.symm ▸ hwC
      rw [hfeval i v hv hvC, hfeval i w hw hwI] at he
      exact congrArg Subtype.val (hginj i he)
    · have hr := hgrange i ⟨v, hvC⟩
      have hr' := hgrange j ⟨w, hwC⟩
      rw [← hfeval i v hv hvC] at hr
      rw [← hfeval j w hw hwC, ← he] at hr'
      exact (Finset.disjoint_left.mp (hdis i j hij) hr hr').elim
  obtain ⟨T, hT, hTcard⟩ := Finset.exists_superset_card_eq
    ((Finset.card_image_le.trans (Finset.card_le_univ (nonisolated J))) :
      ((nonisolated J).image f).card ≤ Fintype.card V)
    (show Fintype.card V ≤ Fintype.card (Fin n) by simpa using hsize)
  obtain ⟨F, hF⟩ := Finset.exists_equiv_extend_of_card_eq hTcard.symm hT hfinj
  refine ⟨⟨⟨fun v => (F v).val, ?_⟩, ?_⟩⟩
  · intro v w hvw
    have hv : v ∈ nonisolated J := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hvw.degree_pos_left⟩
    have hw : w ∈ nonisolated J := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hvw.symm.degree_pos_left⟩
    let i := idx v hv
    have hvC : v ∈ i.val.supp := rfl
    have hwC : w ∈ i.val.supp := i.val.mem_supp_of_adj_mem_supp hvC hvw
    rw [hF v hv, hF w hw, hfeval i v hv hvC, hfeval i w hw hwC]
    exact hgadj i ⟨v, hvC⟩ ⟨w, hwC⟩ hvw
  · intro v w he
    exact F.injective (Subtype.ext he)

/-- Suppose [the source graph is a star forest](hyp:hstar), [its vertex
count is at most the host size n](hyp:hsize), and [a bijection assigns the
positions of a demand list to the nontrivial source components](hyp:e),
with [each component having one more vertex than its demand](hyp:htodo).
If [a list of host stars has leaf counts equal to that demand list in
order](hyp:hcards), [their vertex supports are pairwise disjoint](hyp:hpair),
and [each center is outside its leaves and adjacent to every leaf](hyp:hstars),
then [the host contains a copy of the source graph](goal). -/
-- @node: star_forest_containsCopy_of_list_packing
lemma star_forest_containsCopy_of_list_packing {V : Type}
    [Fintype V] [DecidableEq V] (J : SimpleGraph V) [DecidableRel J.Adj]
    (hstar : IsStarForest J) {n : ℕ} (hsize : Fintype.card V ≤ n)
    (G : SimpleGraph (Fin n)) (todo : List ℕ)
    (e : Fin todo.length ≃ {C : J.ConnectedComponent // 2 ≤ C.supp.ncard})
    (htodo : ∀ i : Fin todo.length, (e i).val.supp.ncard = todo[i] + 1)
    (W : List (Fin n × Finset (Fin n)))
    (hcards : W.map (fun a => a.2.card) = todo)
    (hpair : W.Pairwise (fun a b => Disjoint (centeredStarSupport a) (centeredStarSupport b)))
    (hstars : ∀ a ∈ W, a.1 ∉ a.2 ∧ ∀ x ∈ a.2, G.Adj a.1 x) :
    ContainsCopy J G := by
  classical
  have hlen : W.length = todo.length := by simpa using congrArg List.length hcards
  let pick (i : Fin todo.length) := W.get (Fin.cast hlen.symm i)
  have hatcard (i : Fin todo.length) : (pick i).2.card = todo[i] := by
    have hi : i.val < W.length := by omega
    have he := congrArg (fun l : List ℕ => l[i.val]?) hcards
    simpa [List.getElem?_map, List.getElem?_eq_getElem, hi, i.isLt, pick] using he
  have hatmem (i : Fin todo.length) : pick i ∈ W := List.get_mem _ _
  have hatdis (i j : Fin todo.length) (hne : i ≠ j) :
      Disjoint (centeredStarSupport (pick i)) (centeredStarSupport (pick j)) := by
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hij | hji
    · exact List.pairwise_iff_get.mp hpair (Fin.cast hlen.symm i) (Fin.cast hlen.symm j) hij
    · exact (List.pairwise_iff_get.mp hpair (Fin.cast hlen.symm j) (Fin.cast hlen.symm i) hji).symm
  apply star_forest_containsCopy_of_component_packing J hstar hsize G
    (fun i => pick (e.symm i))
  · intro i
    rw [hatcard]
    simpa using htodo (e.symm i)
  · intro i j hij
    exact hatdis _ _ (fun h => hij (e.symm.injective h))
  · intro i
    exact hstars _ (hatmem _)

/-- Suppose [the source graph is a star forest](hyp:hstar), [its vertex count
is at most n](hyp:hsize), [n is at least two](hyp:hn), [q is nonnegative](hyp:hq),
and [the sampling density A times q is below one half](hyp:hp), where A is
the fixed star constant. Assume [all trial centers lie outside the leaf
bin](hyp:hc), [a bijection assigns demand positions to nontrivial source
components](hyp:e), [each component has one more vertex than its assigned
demand](hyp:htodo), [the centers in the first half of the trials are
distinct](hyp:hdistinct), and [the unused reserve contains at least the
designated available-leaf count plus the sum of the demands](hyp:hreserve).
If [every demand is positive](hyp:hell), [every demand is at most n divided
by 100](hyp:hellsize), [for each demanded size ell, ell factorial divided
by n to the power ell plus one, times its multiplicity divided by twice
Euler's number, is at most q to the power ell](hyp:hcount), and [there are
at most n divided by 200 demands](hyp:hcomponents), then [the containment
threshold is at most A times q](goal). -/
-- @node: star_containmentThreshold_le_of_component_trials
lemma star_containmentThreshold_le_of_component_trials {V : Type}
    [Fintype V] [DecidableEq V] (J : SimpleGraph V) [DecidableRel J.Adj]
    (hstar : IsStarForest J) {n : ℕ} (hsize : Fintype.card V ≤ n)
    (q : ℝ) (hn : 2 ≤ n) (hq : 0 ≤ q) (hp : starConstA * q < 1 / 2)
    (Y : Finset (Fin n)) (c : ℕ → Fin n) (hc : ∀ j, c j ∉ Y)
    (s : StarRowState ↥Y)
    (e : Fin s.todo.length ≃ {C : J.ConnectedComponent // 2 ≤ C.supp.ncard})
    (htodo : ∀ i : Fin s.todo.length, (e i).val.supp.ncard = s.todo[i] + 1)
    (hdistinct : ∀ t < n / 2, ∀ j < t, c j ≠ c t)
    (hreserve : availableLeaves n + s.todo.sum ≤ s.unused.card)
    (hell : ∀ ell ∈ s.todo, 1 ≤ ell)
    (hellsize : ∀ ell ∈ s.todo, (ell : ℝ) ≤ (n : ℝ) / 100)
    (hcount : ∀ ell ∈ s.todo, (ell.factorial : ℝ) / (n : ℝ) ^ (ell + 1) *
      ((s.todo.count ell : ℝ) / (2 * Real.exp 1)) ≤ q ^ ell)
    (hcomponents : (s.todo.length : ℝ) ≤ (n : ℝ) / 200) :
    containmentThreshold J n ≤ starConstA * q := by
  classical
  have hA : 0 < starConstA := by unfold starConstA; positivity
  have hpI : starConstA * q ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg hA.le hq, by linarith⟩
  have hpacking := star_host_packing_probability_of_count q hn hq hp Y c hc s
    hdistinct hreserve hell hellsize hcount hcomponents
  have hprob : (1 / 2 : ℝ) ≤ containmentProb J n (starConstA * q) := by
    apply hpacking.trans
    apply Causalean.Experimentation.DesignBased.FiniteDesign.Pr_mono
    intro z hz
    obtain ⟨W, hcards, hpair, hstars⟩ := hz
    exact star_forest_containsCopy_of_list_packing J hstar hsize (hostGraph z)
      s.todo e htodo W hcards hpair hstars
  by_cases hedge : J.edgeSet = ∅
  · simpa [containmentThreshold, hedge] using hpI.1
  · simpa [containmentThreshold, hedge] using
      (containmentThresholdRaw_isLeast J n hsize).2 ⟨hpI, hprob⟩

end Papers.OaiGraphDecompositionsIntegral
