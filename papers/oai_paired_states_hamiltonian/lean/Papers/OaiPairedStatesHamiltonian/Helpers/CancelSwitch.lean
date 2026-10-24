module

public import Papers.OaiPairedStatesHamiltonian.Helpers.PairPhases
public import Mathlib.GroupTheory.Perm.List

/-! The actual state obtained by reversing a directed opposite-edge cycle. -/

@[expose] public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
open Classical
attribute [local instance] propDecidable

variable (T : SphereMap) (col : T.Face → Bool) (t0 : T.Face)

-- @node: oppositeThirdVertex
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [a distinguished outer face](hyp:t0), and [a sphere triangulation structure](hyp:hT), take [states r and s](hyp:r,s) that [form a pair](hyp:h) and [a black face other than the outer face](hyp:t). The [opposite third vertex](goal) is the vertex of this face different from the vertices selected by r and s. -/
noncomputable def oppositeThirdVertex (hT : IsSphereTriangulation T)
    (r s : State T col t0) (h : IsPair T col t0 r s) (t : blackNonOuter T col t0) :=
  thirdVertex T hT t.val (r.val t).val (s.val t).val
    (r.property.incident t) (s.property.incident t) (pair_vertex_ne T col t0 r s h t)

-- @node: oppositeDart
/-- For [a sphere map](hyp:T), [a face coloring](hyp:col), [a distinguished outer face](hyp:t0), and [a sphere triangulation structure](hyp:hT), take [states r and s](hyp:r,s) that [form a pair](hyp:h) and [a black face other than the outer face](hyp:t). The [opposite dart](goal) is the directed side of this face from the vertex selected by r to the third vertex, different from both state selections. -/
noncomputable def oppositeDart (hT : IsSphereTriangulation T)
    (r s : State T col t0) (h : IsPair T col t0 r s) (t : blackNonOuter T col t0) : T.Dart :=
  faceDart T hT t.val (r.val t).val (oppositeThirdVertex T col t0 hT r s h t).val
    (r.property.incident t) (oppositeThirdVertex T col t0 hT r s h t).property.1
    (Ne.symm (oppositeThirdVertex T col t0 hT r s h t).property.2.1)

-- @node: oppositeDart_spec
/-- In [a sphere triangulation](hyp:hT), for [paired states r and s](hyp:h), [the opposite dart at a black face other than the outer face runs from r's selected vertex to the third vertex and has that face on one of its two sides](goal). -/
lemma oppositeDart_spec (hT : IsSphereTriangulation T)
    (r s : State T col t0) (h : IsPair T col t0 r s) (t : blackNonOuter T col t0) :
    FaceDart T t.val (r.val t).val (oppositeThirdVertex T col t0 hT r s h t).val
      (oppositeDart T col t0 hT r s h t) :=
  Classical.choose_spec (exists_faceDart T hT t.val (r.val t).val
    (oppositeThirdVertex T col t0 hT r s h t).val (r.property.incident t)
    (oppositeThirdVertex T col t0 hT r s h t).property.1
    (Ne.symm (oppositeThirdVertex T col t0 hT r s h t).property.2.1))

-- @node: oppositeDart_tail_injective
/-- In [a sphere triangulation](hyp:hT), for [paired states r and s](hyp:h), if [the opposite darts of two black faces other than the outer face have the same starting vertex](hyp:he), then [the two faces are equal](goal). -/
lemma oppositeDart_tail_injective (hT : IsSphereTriangulation T)
    (r s : State T col t0) (h : IsPair T col t0 r s)
    (t u : blackNonOuter T col t0)
    (he : T.vert (oppositeDart T col t0 hT r s h t) =
      T.vert (oppositeDart T col t0 hT r s h u)) : t = u := by
  apply r.property.bijective.1
  apply Subtype.ext
  simpa only [(oppositeDart_spec T col t0 hT r s h t).1,
    (oppositeDart_spec T col t0 hT r s h u).1] using he

-- @node: cycle_formPerm_head
/-- If [a dart belongs to a simple directed cycle](hyp:hd), then [the cyclic permutation of the cycle's starting vertices sends this dart's starting vertex to its ending vertex](goal). -/
lemma cycle_formPerm_head (C : T.Cycle) (d : T.Dart) (hd : d ∈ C.val) :
    (C.val.map T.vert).formPerm (T.vert d) = T.head d := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hd
  have hp := List.formPerm_apply_getElem (C.val.map T.vert) C.property.2 i
    (by simpa using hi)
  simp only [List.getElem_map, List.length_map] at hp
  exact hp.trans (C.property.1.2.2 ⟨i, hi⟩).symm

-- @node: exists_opposite_cycle_switch
/-- In [a sphere triangulation](hyp:hT), let [r and s be paired states](hyp:h) and suppose [every dart of a simple directed cycle is an opposite dart for this pair](hyp:hC). Then [there is a state q paired with s that selects the third vertex on every face whose opposite dart lies on the cycle and keeps r's selection on every other face](goal). -/
lemma exists_opposite_cycle_switch (hT : IsSphereTriangulation T)
    (r s : State T col t0) (h : IsPair T col t0 r s) (C : T.Cycle)
    (hC : ∀ d ∈ C.val, ∃ t, oppositeDart T col t0 hT r s h t = d) :
    ∃ q : State T col t0, ∃ _hq : IsPair T col t0 q s,
      ∀ t : blackNonOuter T col t0,
        (q.val t).val = if oppositeDart T col t0 hT r s h t ∈ C.val then
          (oppositeThirdVertex T col t0 hT r s h t).val else (r.val t).val := by
  let σ := (C.val.map T.vert).formPerm
  have htail (t : blackNonOuter T col t0) :
      (r.val t).val ∈ C.val.map T.vert ↔ oppositeDart T col t0 hT r s h t ∈ C.val := by
    constructor
    · intro ht
      obtain ⟨d, hd, he⟩ := List.mem_map.mp ht
      obtain ⟨u, rfl⟩ := hC d hd
      have hut : u = t := oppositeDart_tail_injective T col t0 hT r s h u t
        (he.trans (oppositeDart_spec T col t0 hT r s h t).1.symm)
      simpa only [hut] using hd
    · intro ht
      exact List.mem_map.mpr ⟨_, ht, (oppositeDart_spec T col t0 hT r s h t).1⟩
  have hσ (t : blackNonOuter T col t0) :
      σ (r.val t).val = if oppositeDart T col t0 hT r s h t ∈ C.val then
        (oppositeThirdVertex T col t0 hT r s h t).val else (r.val t).val := by
    by_cases ht : oppositeDart T col t0 hT r s h t ∈ C.val
    · rw [if_pos ht]
      exact (congrArg σ (oppositeDart_spec T col t0 hT r s h t).1.symm).trans
        ((cycle_formPerm_head T C _ ht).trans
          (oppositeDart_spec T col t0 hT r s h t).2.1)
    · rw [if_neg ht]
      exact List.formPerm_apply_of_notMem (mt (htail t).mp ht)
  have hnonroot (v : T.Vertex) (hv : v ∈ C.val.map T.vert) : v ∈ nonRoot T t0 := by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hv
    obtain ⟨t, rfl⟩ := hC d hd
    rw [(oppositeDart_spec T col t0 hT r s h t).1]
    exact (r.val t).property
  have hσX (v : nonRoot T t0) : σ v.val ∈ nonRoot T t0 := by
    by_cases hv : v.val ∈ C.val.map T.vert
    · exact hnonroot _ (List.formPerm_apply_mem_of_mem hv)
    · rw [show σ v.val = v.val from List.formPerm_apply_of_notMem hv]
      exact v.property
  let f : nonRoot T t0 → nonRoot T t0 := fun v => ⟨σ v.val, hσX v⟩
  have hf : Function.Bijective f := (Finite.injective_iff_bijective).mp (by
    intro v w he
    exact Subtype.ext (σ.injective (congrArg Subtype.val he)))
  let qval : Assignment T col t0 := f ∘ r.val
  have hqval (t : blackNonOuter T col t0) :
      (qval t).val = if oppositeDart T col t0 hT r s h t ∈ C.val then
        (oppositeThirdVertex T col t0 hT r s h t).val else (r.val t).val := hσ t
  have hqstate : IsState T col t0 qval := by
    refine ⟨hf.comp r.property.bijective, ?_⟩
    intro t
    rw [hqval]
    split_ifs
    · exact (oppositeThirdVertex T col t0 hT r s h t).property.1
    · exact r.property.incident t
  let q : State T col t0 := ⟨qval, hqstate⟩
  have hq : IsPair T col t0 q s := by
    constructor
    intro t he
    have he' := congrArg Subtype.val he
    change (qval t).val = (s.val t).val at he'
    rw [hqval] at he'
    split_ifs at he'
    · exact (oppositeThirdVertex T col t0 hT r s h t).property.2.2 he'
    · exact pair_vertex_ne T col t0 r s h t he'
  exact ⟨q, hq, hqval⟩

end OaiPairedStatesHamiltonian
