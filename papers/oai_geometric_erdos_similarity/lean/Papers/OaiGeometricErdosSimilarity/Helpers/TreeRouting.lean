module
public import Papers.OaiGeometricErdosSimilarity.Helpers.Tables

/-! # Prefix and endpoint invariants for routes inside child subtrees -/

public section

namespace Papers.OaiGeometricErdosSimilarity

open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {q : ℝ} {M d g r0 n0 : ℕ}

-- @node: vertexPath_child
/-- For [internal vertex U](hyp:U) and [child index i](hyp:i),
[the path to child i is the path to U with i appended](goal). -/
lemma vertexPath_child (U : InternalVertex M d) (i : Fin M) :
    vertexPath (child U i) = vertexPath U.val ++ [i] := by
  change List.ofFn (Fin.lastCases i U.val.2) = _
  rw [List.ofFn_succ']
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last, List.concat_eq_append, vertexPath]

-- @node: walkVertices_last_prefix
/-- Assuming [the branching number is at least two](hyp:hM), for
[Boolean edge assignment ξ](hyp:ξ), [step budget fuel](hyp:fuel), and
[starting vertex v](hyp:v), [the path to v is an initial segment of the path
to the last vertex visited by the walk](goal). -/
lemma walkVertices_last_prefix (hM : BranchingDomain M) (ξ : NondefaultEdge M d → Bool)
    (fuel : ℕ) (v : TreeVertex M d) :
    (vertexPath v).IsPrefix
      (vertexPath ((walkVertices hM ξ fuel v).getLast (walkVertices_ne_nil hM ξ fuel v))) := by
  induction fuel generalizing v with
  | zero => simp [walkVertices]
  | succ fuel ih =>
      by_cases hv : v.1.val < d
      · simp only [walkVertices, dif_pos hv]
        rw [List.getLast_cons (walkVertices_ne_nil hM ξ fuel _)]
        exact (show (vertexPath v).IsPrefix
          (vertexPath (child ⟨v, hv⟩ (chooseChild hM ξ ⟨v, hv⟩))) by
            rw [vertexPath_child]
            exact List.prefix_append _ _).trans (ih _)
      · simp [walkVertices, hv]

-- @node: localLeaf_prefix
/-- Assuming [the branching number is at least two](hyp:hM), for
[table outcome ω](hyp:ω), [internal vertex U](hyp:U), [child index i](hyp:i), and
[point z](hyp:z), [the path to child i of U is an initial segment of the path
to the leaf reached by routing z from that child](goal). -/
lemma localLeaf_prefix (hM : BranchingDomain M) (ω : Outcome q M d g r0 n0)
    (U : InternalVertex M d) (i : Fin M) (z : ℝ) :
    (vertexPath (child U i)).IsPrefix (vertexPath (localLeaf hM ω U i z).val) := by
  exact walkVertices_last_prefix hM (exposedValues ω z) d (child U i)

-- @node: child_indices_eq_of_common_leaf
/-- For [internal vertex U](hyp:U), [child indices i and j](hyp:i,j), and
[leaf L](hyp:L), if [the path to child i is an initial segment of the path to L](hyp:hi)
and [the path to child j is also an initial segment of the path to L](hyp:hj),
then [i and j are equal](goal). -/
lemma child_indices_eq_of_common_leaf (U : InternalVertex M d) (i j : Fin M)
    (L : Leaf M d) (hi : (vertexPath (child U i)).IsPrefix (vertexPath L.val))
    (hj : (vertexPath (child U j)).IsPrefix (vertexPath L.val)) : i = j := by
  have hlen : (vertexPath (child U i)).length = (vertexPath (child U j)).length := by
    simp [vertexPath_child]
  have hp := List.prefix_of_prefix_length_le hi hj hlen.le
  have heq := hp.eq_of_length hlen
  rw [vertexPath_child, vertexPath_child] at heq
  simpa using List.append_cancel_left heq

-- @node: preorderLt_of_prefix_ne
/-- For [tree edges e and f](hyp:e,f), if [the path to e is an initial segment
of the path to f](hyp:hp) and [the edges are distinct](hyp:hne), then
[e precedes f in the tree's preorder traversal](goal). -/
lemma preorderLt_of_prefix_ne (e f : TreeEdge M d)
    (hp : (vertexPath e.val).IsPrefix (vertexPath f.val)) (hne : e ≠ f) : preorderLt e f := by
  obtain ⟨s, hs⟩ := hp
  have hsne : s ≠ [] := by
    intro hnil
    apply hne
    apply Subtype.ext
    apply vertexPath_injective
    simpa [hnil] using hs
  change List.Lex (· < ·) _ _
  rw [← hs]
  have hnil : List.Lex (fun a b : Fin M => a < b) [] s := by
    cases s with
    | nil => contradiction
    | cons a s => exact .nil
  simpa only [List.append_nil] using List.Lex.append_left _ hnil (vertexPath e.val)

-- @node: windowEnd_le_of_preorderLt
/-- If [the base window length is positive](hyp:hr), then for
[tree edges e and f](hyp:e,f) such that [e precedes f in preorder](hyp:hef),
[the endpoint of e's window is at most the endpoint of f's window](goal). -/
lemma windowEnd_le_of_preorderLt (hr : BaseLengthDomain r0) (e f : TreeEdge M d)
    (hef : preorderLt e f) :
    windowEnd q M d g r0 n0 e ≤ windowEnd q M d g r0 n0 f := by
  let A := Finset.univ.filter (fun a : TreeEdge M d => preorderLt a e)
  let B := Finset.univ.filter (fun a : TreeEdge M d => preorderLt a f)
  let w := fun a : TreeEdge M d => windowLength M g r0 (sourceHeight a) + g
  have heA : e ∉ A := by
    intro he
    exact List.lex_irrefl (fun a : Fin M => lt_irrefl a) _ (Finset.mem_filter.mp he).2
  have hsub : insert e A ⊆ B := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hef⟩
    · have hae := (Finset.mem_filter.mp ha).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        List.lex_trans (fun hab hbc => lt_trans hab hbc) hae hef⟩
  have hsum := Finset.sum_le_sum_of_subset hsub (f := w)
  rw [Finset.sum_insert heA] at hsum
  have hlen := windowLength_pos M g r0 (sourceHeight f) hr
  change n0 + ∑ a ∈ A, w a + windowLength M g r0 (sourceHeight e) - 1 ≤
    n0 + ∑ a ∈ B, w a + windowLength M g r0 (sourceHeight f) - 1
  change w e + ∑ a ∈ A, w a ≤ ∑ a ∈ B, w a at hsum
  have hw : w e = windowLength M g r0 (sourceHeight e) + g := rfl
  omega

-- @node: windowEnd_le_leafEndpoint_of_prefix
/-- If [the base window length is positive](hyp:hr), then for [tree edge e](hyp:e)
and [leaf L](hyp:L) such that [the path to e is an initial segment of the path
to L](hyp:hp), [the endpoint of e's window is at most the endpoint assigned to L](goal). -/
lemma windowEnd_le_leafEndpoint_of_prefix (hr : BaseLengthDomain r0)
    (e : TreeEdge M d) (L : Leaf M d)
    (hp : (vertexPath e.val).IsPrefix (vertexPath L.val)) :
    windowEnd q M d g r0 n0 e ≤ leafEndpoint q M d g r0 n0 L := by
  have hdepth : 1 ≤ L.val.1.val := by
    have hlen := hp.length_le
    simp only [vertexPath, List.length_ofFn] at hlen
    exact e.property.trans hlen
  rw [leafEndpoint, dif_pos hdepth]
  by_cases he : e = ⟨L.val, hdepth⟩
  · subst e
    exact le_rfl
  · exact windowEnd_le_of_preorderLt hr e ⟨L.val, hdepth⟩
      (preorderLt_of_prefix_ne e ⟨L.val, hdepth⟩ hp he)

end Papers.OaiGeometricErdosSimilarity
