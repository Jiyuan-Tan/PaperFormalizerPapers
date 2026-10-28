module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.DegreeLayers
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-! # Forest pieces in the bounded-degeneracy branch

A cycle has minimum degree two, so it cannot occur in a graph of degeneracy
at most one. Splitting into degeneracy-one pieces therefore gives forests.
-/

public section

namespace Papers.OaiGraphDecompositionsIntegral

variable {V : Type} [Fintype V]

/-- If there is an injective map from H into G preserving adjacency, then
[the degeneracy of H is at most the degeneracy of G](goal). -/
-- @node: degeneracy_le_of_copy
lemma degeneracy_le_of_copy {W : Type} [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (f : H.Copy G) :
    degeneracy H ≤ degeneracy G := by
  classical
  have hle : H ≤ G.comap f := fun _ _ h => f.toHom.map_adj h
  let e : G.comap f ↪g G :=
    { toEmbedding := f.toEmbedding
      map_rel_iff' := by intro a b; rfl }
  exact (degeneracy_mono hle).trans (degeneracy_le_of_embedding G _ e)

open Classical in
/-- [The minimum vertex degree of a finite graph is at most its degeneracy](goal). -/
-- @node: minDegree_le_degeneracy
lemma minDegree_le_degeneracy (G : SimpleGraph V) :
    G.minDegree ≤ degeneracy G := by
  classical
  cases isEmpty_or_nonempty V with
  | inl h => rw [SimpleGraph.minDegree_of_subsingleton]; exact Nat.zero_le _
  | inr h =>
    have hb : (G.induce (Finset.univ : Finset V)).minDegree ≤ degeneracy G := by
      unfold degeneracy
      exact Finset.le_sup (s := Finset.univ.filter (fun S : Finset V => S.Nonempty))
        (b := Finset.univ) (f := fun S : Finset V => (G.induce (S : Set V)).minDegree)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.univ_nonempty⟩)
    let e : G.induce (↑(Finset.univ : Finset V) : Set V) ≃g G := {
      toEquiv := {
        toFun := fun v => v.val
        invFun := fun v => ⟨v, Finset.mem_univ v⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
      map_rel_iff' := by intro a b; rfl }
    exact e.minDegree_eq ▸ hb

/-- [The cycle graph on k + 3 vertices has degeneracy at least two](goal). -/
-- @node: two_le_degeneracy_cycleGraph
lemma two_le_degeneracy_cycleGraph (k : ℕ) :
    2 ≤ degeneracy (SimpleGraph.cycleGraph (k + 3)) := by
  have hmin : 2 ≤ (SimpleGraph.cycleGraph (k + 3)).minDegree :=
    SimpleGraph.le_minDegree_of_forall_le_degree _ 2
      (fun w => (SimpleGraph.cycleGraph_degree_three_le (v := w)).ge)
  have heq : (SimpleGraph.cycleGraph (k + 3)).minDegree =
      @SimpleGraph.minDegree (Fin (k + 3)) (SimpleGraph.cycleGraph (k + 3)) _
        (fun _ _ => Classical.propDecidable _) :=
    congrArg (@SimpleGraph.minDegree (Fin (k + 3)) (SimpleGraph.cycleGraph (k + 3)) _)
      (Subsingleton.elim _ _)
  rw [heq] at hmin
  exact hmin.trans (minDegree_le_degeneracy _)

/-- If [the closed walk p in G is a cycle](hyp:hp), then [G has degeneracy
at least two](goal). -/
-- @node: two_le_degeneracy_of_cycle
lemma two_le_degeneracy_of_cycle (G : SimpleGraph V) {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) : 2 ≤ degeneracy G := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, p.length = k + 3 :=
    ⟨p.length - 3, by have := hp.three_le_length; omega⟩
  obtain ⟨f⟩ := (SimpleGraph.cycleGraph_isContained_iff
    (by omega : 2 < k + 3)).mpr ⟨v, p, hp, hk⟩
  exact (two_le_degeneracy_cycleGraph k).trans (degeneracy_le_of_copy G _ f)

/-- If [G has degeneracy at most one](hyp:hd), then [G has no cycles](goal). -/
-- @node: isAcyclic_of_degeneracy_le_one
lemma isAcyclic_of_degeneracy_le_one (G : SimpleGraph V) (hd : degeneracy G ≤ 1) :
    G.IsAcyclic := by
  intro v p hp
  have := two_le_degeneracy_of_cycle G p hp
  omega

/-- If [d is positive](hyp:hdpos) and [H has degeneracy at most d](hyp:hd),
then [there are d forest subgraphs of H such that every edge of H belongs
to exactly one of them](goal). -/
-- @node: degeneracy_forest_partition
lemma degeneracy_forest_partition (H : SimpleGraph V) (d : ℕ)
    (hdpos : 0 < d) (hd : degeneracy H ≤ d) :
    ∃ P : Fin d → SimpleGraph V,
      (∀ i, P i ≤ H) ∧
      (∀ e ∈ H.edgeSet, ∃! i, e ∈ (P i).edgeSet) ∧
      ∀ i, (P i).IsAcyclic := by
  obtain ⟨P, hP, hpart, hdeg⟩ :=
    degeneracy_split H d d (by change Finite V; infer_instance) hdpos hd
  refine ⟨P, hP, hpart, fun i => isAcyclic_of_degeneracy_le_one (P i) ?_⟩
  have hquot : (d + d - 1) / d = 1 := by
    apply Nat.div_eq_of_lt_le <;> omega
  simpa only [hquot] using hdeg i

omit [Fintype V] in
/-- If [every edge of G joins a designated center to a vertex that is not
a center](hyp:hcross) and [each vertex that is not a center has at most
one neighbor](hyp:hleaf), then [G is a star forest](goal). -/
-- @node: isStarForest_of_unique_leaf_neighbor
lemma isStarForest_of_unique_leaf_neighbor (G : SimpleGraph V) (center : V → Prop)
    (hcross : ∀ {u v}, G.Adj u v →
      (center u ∧ ¬ center v) ∨ (center v ∧ ¬ center u))
    (hleaf : ∀ v, ¬ center v → ∀ a b, G.Adj v a → G.Adj v b → a = b) :
    IsStarForest G := by
  classical
  constructor
  intro C hC
  obtain ⟨a, ha, b, hb, hab⟩ := hC
  have has : a ∈ G.support := SimpleGraph.mem_support_of_reachable hab
    (C.reachable_of_mem_supp ha hb)
  obtain ⟨w, haw⟩ := G.mem_support.mp has
  have hw : w ∈ C.supp := (C.mem_supp_congr_adj haw).mp ha
  have hcenter : ∃ c ∈ C.supp, center c := by
    rcases hcross haw with ⟨hc, _⟩ | ⟨hc, _⟩
    · exact ⟨a, ha, hc⟩
    · exact ⟨w, hw, hc⟩
  obtain ⟨c, hcC, hc⟩ := hcenter
  have hnear : ∀ x ∈ C.supp, x = c ∨ G.Adj c x := by
    intro x hx
    have hr := (SimpleGraph.reachable_iff_reflTransGen c x).mp
      (C.reachable_of_mem_supp hcC hx)
    clear hx
    induction hr with
    | refl => exact Or.inl rfl
    | @tail y z hr hyz ih =>
      rcases ih with rfl | hcy
      · exact Or.inr hyz
      · have hny : ¬ center y := by
          rcases hcross hcy with h | h
          · exact h.2
          · exact (h.2 hc).elim
        exact Or.inl (hleaf y hny z c hyz hcy.symm)
  refine ⟨c, hcC, ?_⟩
  intro u hu v hv
  constructor
  · intro huv
    refine ⟨G.ne_of_adj huv, ?_⟩
    rcases hnear u hu with rfl | hcu
    · exact Or.inl rfl
    · have hnu : ¬ center u := by
        rcases hcross hcu with h | h
        · exact h.2
        · exact (h.2 hc).elim
      exact Or.inr (hleaf u hnu v c huv hcu.symm)
  · rintro ⟨hne, rfl | rfl⟩
    · exact (hnear v hv).resolve_left (Ne.symm hne)
    · exact ((hnear u hu).resolve_left hne).symm

omit [Fintype V] in
/-- Suppose [G has no cycles](hyp:hG), [v is reachable from r](hyp:hr),
[a and b are both neighbors of v](hyp:ha,hb), and [a and b each have
strictly smaller distance from r than v does](hyp:hda,hdb). Then
[a and b are the same vertex](goal). -/
-- @node: forest_lower_neighbor_unique
lemma forest_lower_neighbor_unique (G : SimpleGraph V) (hG : G.IsAcyclic)
    (r v a b : V) (hr : G.Reachable r v) (ha : G.Adj v a) (hb : G.Adj v b)
    (hda : G.dist r a < G.dist r v) (hdb : G.dist r b < G.dist r v) : a = b := by
  classical
  obtain ⟨p, hp, hplen⟩ := hr.exists_path_of_dist
  have hparent : ∀ w, G.Adj v w → G.dist r w < G.dist r v → w = p.penultimate := by
    intro w hvw hdw
    obtain ⟨q, hq, hqlen⟩ := (hr.trans hvw.reachable).exists_path_of_dist
    have hvq : v ∉ q.support := by
      intro hvq
      have hdist := G.dist_le (q.takeUntil v hvq)
      have hlen := q.length_takeUntil_le_length hvq
      omega
    exact hG.eq_penultimate_of_adj_end hp hvw
      (hG.mem_support_of_ne_mem_support_of_adj_of_isPath hp hq hvw hvq)
  exact (hparent a ha hda).trans (hparent b hb hdb).symm

omit [Fintype V] in
/-- If [G has no cycles](hyp:hG), then [one can assign a nonnegative integer
depth to each vertex so that adjacent depths differ by exactly one and
each vertex has at most one neighbor of smaller depth](goal). -/
-- @node: forest_depth_exists
lemma forest_depth_exists (G : SimpleGraph V) (hG : G.IsAcyclic) :
    ∃ depth : V → ℕ,
      (∀ {u v}, G.Adj u v → depth u = depth v + 1 ∨ depth v = depth u + 1) ∧
      ∀ v a b, G.Adj v a → G.Adj v b → depth a < depth v → depth b < depth v → a = b := by
  classical
  let root : G.ConnectedComponent → V := fun C => C.nonempty_supp.some
  have hroot (C : G.ConnectedComponent) : root C ∈ C.supp := C.nonempty_supp.some_mem
  let depth : V → ℕ := fun v => G.dist (root (G.connectedComponentMk v)) v
  have hreach (v : V) : G.Reachable (root (G.connectedComponentMk v)) v :=
    SimpleGraph.ConnectedComponent.exact (hroot _)
  have heq {v w : V} (hvw : G.Adj v w) :
      root (G.connectedComponentMk v) = root (G.connectedComponentMk w) :=
    congrArg root (SimpleGraph.ConnectedComponent.sound hvw.reachable)
  refine ⟨depth, ?_, ?_⟩
  · intro u v huv
    dsimp [depth]
    rw [← heq huv]
    exact hG.dist_eq_dist_add_one_of_adj_of_reachable _ huv (hreach u)
  · intro v a b hva hvb hda hdb
    apply forest_lower_neighbor_unique G hG (root (G.connectedComponentMk v)) v a b
      (hreach v) hva hvb
    · simpa only [depth, ← heq hva] using hda
    · simpa only [depth, ← heq hvb] using hdb

omit [Fintype V] in
/-- If [G has no cycles](hyp:hG), then [there are two star forest subgraphs
of G such that every edge of G belongs to exactly one of them](goal). -/
-- @node: forest_star_partition
lemma forest_star_partition (G : SimpleGraph V) (hG : G.IsAcyclic) :
    ∃ P : Fin 2 → SimpleGraph V,
      (∀ i, P i ≤ G) ∧
      (∀ e ∈ G.edgeSet, ∃! i, e ∈ (P i).edgeSet) ∧
      ∀ i, IsStarForest (P i) := by
  classical
  obtain ⟨depth, hdepth, hparent⟩ := forest_depth_exists G hG
  let P : Fin 2 → SimpleGraph V := fun i => {
    Adj := fun u v => G.Adj u v ∧
      ((depth v = depth u + 1 ∧ depth u % 2 = i.val) ∨
       (depth u = depth v + 1 ∧ depth v % 2 = i.val))
    symm := ⟨by
      intro u v h
      exact ⟨h.1.symm, h.2.elim Or.inr Or.inl⟩⟩
    loopless := ⟨by intro v h; exact G.irrefl h.1⟩ }
  have hpart : ∀ u v, G.Adj u v → ∃! i, (P i).Adj u v := by
    intro u v huv
    rcases hdepth huv with hd | hd
    · let i : Fin 2 := ⟨depth v % 2, Nat.mod_lt _ (by omega)⟩
      refine ⟨i, ⟨huv, Or.inr ⟨hd, rfl⟩⟩, ?_⟩
      intro j hj
      apply Fin.ext
      rcases hj.2 with ⟨hbad, _⟩ | ⟨_, hj⟩
      · omega
      · exact hj.symm
    · let i : Fin 2 := ⟨depth u % 2, Nat.mod_lt _ (by omega)⟩
      refine ⟨i, ⟨huv, Or.inl ⟨hd, rfl⟩⟩, ?_⟩
      intro j hj
      apply Fin.ext
      rcases hj.2 with ⟨_, hj⟩ | ⟨hbad, _⟩
      · exact hj.symm
      · omega
  refine ⟨P, fun i _ _ h => h.1, ?_, ?_⟩
  · intro e he
    induction e using Sym2.inductionOn with
    | hf u v => exact hpart u v he
  · intro i
    apply isStarForest_of_unique_leaf_neighbor (P i) (fun v => depth v % 2 = i.val)
    · intro u v huv
      rcases huv.2 with ⟨hd, hc⟩ | ⟨hd, hc⟩
      · exact Or.inl ⟨hc, by omega⟩
      · exact Or.inr ⟨hc, by omega⟩
    · intro v hv a b hva hvb
      have hda : depth a < depth v := by
        rcases hva.2 with ⟨_, hc⟩ | ⟨hd, _⟩
        · exact (hv hc).elim
        · omega
      have hdb : depth b < depth v := by
        rcases hvb.2 with ⟨_, hc⟩ | ⟨hd, _⟩
        · exact (hv hc).elim
        · omega
      exact hparent v a b hva.1 hvb.1 hda hdb

/-- If [d is positive](hyp:hdpos) and [H has degeneracy at most d](hyp:hd),
then [there are 2d star forest subgraphs of H, indexed by d pairs, such
that every edge of H belongs to exactly one of them](goal). -/
-- @node: degeneracy_star_partition
lemma degeneracy_star_partition (H : SimpleGraph V) (d : ℕ)
    (hdpos : 0 < d) (hd : degeneracy H ≤ d) :
    ∃ P : Fin d × Fin 2 → SimpleGraph V,
      (∀ i, P i ≤ H) ∧
      (∀ e ∈ H.edgeSet, ∃! i, e ∈ (P i).edgeSet) ∧
      ∀ i, IsStarForest (P i) := by
  classical
  obtain ⟨F, hF, hFpart, hforest⟩ := degeneracy_forest_partition H d hdpos hd
  choose P hP hpart hstar using fun i => forest_star_partition (F i) (hforest i)
  refine ⟨fun i => P i.1 i.2, fun i => (hP i.1 i.2).trans (hF i.1), ?_,
    fun i => hstar i.1 i.2⟩
  intro e he
  obtain ⟨i, hei, hi⟩ := hFpart e he
  obtain ⟨j, hej, hj⟩ := hpart i e hei
  refine ⟨(i, j), hej, ?_⟩
  rintro ⟨a, b⟩ hab
  have ha : a = i := hi a ((SimpleGraph.edgeSet_mono (hP a b)) hab)
  subst a
  exact Prod.ext rfl (hj b hab)

omit [Fintype V] in
/-- If [every edge of G is an edge of H](hyp:hGH) and [H is a star
forest](hyp:hH), then [G is a star forest](goal). -/
-- @node: isStarForest_mono
lemma isStarForest_mono {G H : SimpleGraph V} (hGH : G ≤ H) (hH : IsStarForest H) :
    IsStarForest G := by
  classical
  constructor
  intro C hC
  obtain ⟨a, ha, b, hb, hab⟩ := hC
  let D := H.connectedComponentMk a
  have hsub : ∀ x ∈ C.supp, x ∈ D.supp := by
    intro x hx
    change H.connectedComponentMk x = H.connectedComponentMk a
    exact SimpleGraph.ConnectedComponent.sound
      ((C.reachable_of_mem_supp ha hx).mono hGH).symm
  obtain ⟨c, hcD, hstar⟩ := hH.components D ⟨a, hsub a ha, b, hsub b hb, hab⟩
  have hcC : c ∈ C.supp := by
    obtain ⟨w, haw⟩ := G.mem_support.mp
      (SimpleGraph.mem_support_of_reachable hab (C.reachable_of_mem_supp ha hb))
    have hw := (C.mem_supp_congr_adj haw).mp ha
    rcases ((hstar a (hsub a ha) w (hsub w hw)).mp (hGH haw)).2 with hac | hwc
    · exact hac ▸ ha
    · exact hwc ▸ hw
  have hradial : ∀ x ∈ C.supp, x ≠ c → G.Adj x c := by
    intro x hx hxc
    have hother : ∃ y ∈ C.supp, x ≠ y := by
      by_cases hxa : x = a
      · exact ⟨b, hb, by simpa [hxa] using hab⟩
      · exact ⟨a, ha, hxa⟩
    obtain ⟨y, hy, hxy⟩ := hother
    obtain ⟨w, hxw⟩ := G.mem_support.mp
      (SimpleGraph.mem_support_of_reachable hxy (C.reachable_of_mem_supp hx hy))
    have hw := (C.mem_supp_congr_adj hxw).mp hx
    have hwc : w = c :=
      ((hstar x (hsub x hx) w (hsub w hw)).mp (hGH hxw)).2.resolve_left hxc
    exact hwc ▸ hxw
  refine ⟨c, hcC, ?_⟩
  intro u hu v hv
  constructor
  · intro huv
    exact (hstar u (hsub u hu) v (hsub v hv)).mp (hGH huv)
  · rintro ⟨hne, rfl | rfl⟩
    · exact (hradial v hv hne.symm).symm
    · exact hradial u hu hne

end Papers.OaiGraphDecompositionsIntegral
