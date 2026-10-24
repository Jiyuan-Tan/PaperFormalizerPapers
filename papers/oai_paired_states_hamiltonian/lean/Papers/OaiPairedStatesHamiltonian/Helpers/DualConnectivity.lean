module

public import Papers.OaiPairedStatesHamiltonian.Helpers.ForestExtension
public import Papers.OaiPairedStatesHamiltonian.Helpers.EulerBound

/-! Connectivity of the dual after deleting a primal forest. Cutting a forest
edge separates its endpoints; facial telescoping rules out a face separation
supported on that edge. This verifies the connectivity step of contraction. -/

public section

namespace OaiPairedStatesHamiltonian
namespace SphereMap

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option backward.isDefEq.respectTransparency false
open Classical
attribute [local instance] propDecidable

-- @node: SphereMap.facialGradient_zero_of_forest
/-- If [a set of primal edges is a spanning forest](hyp:hS) and [a real potential on facial boundary orbits has zero facial gradient on every edge outside that forest](hyp:hb), then [its facial gradient vanishes on every directed edge](goal). -/
lemma facialGradient_zero_of_forest (M : SphereMap) (S : Set M.Edge)
    (hS : IsSpanningForest M S) (b : M.FaceOrbit → ℝ)
    (hb : ∀ d, M.edgeOf d ∉ S → M.facialGradient b d = 0) :
    ∀ d, M.facialGradient b d = 0 := by
  intro d
  by_cases hd : M.edgeOf d ∈ S
  · let G := M.spanningGraph S
    let H := G.deleteEdges {s(M.vert d, M.head d)}
    have hdadj : G.Adj (M.vert d) (M.head d) :=
      ⟨M.forest_no_loop S hS d hd, d, hd, rfl, rfl⟩
    have hsep : ¬ H.Reachable (M.vert d) (M.head d) :=
      SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp
        (M.isAcyclic_spanningGraph S hS) hdadj
    let a : M.Vertex → ℝ := fun v =>
      if H.Reachable (M.vert d) v then 0 else M.facialGradient b d
    have had : M.vertexGradient a d = M.facialGradient b d := by
      simp only [RotationSystem.vertexGradient, a, if_neg hsep,
        if_pos (SimpleGraph.Reachable.rfl), sub_zero]
    have hae (e : M.Dart) (he : M.edgeOf e ∈ S) (hne : M.edgeOf e ≠ M.edgeOf d) :
        M.vertexGradient a e = 0 := by
      have hends : s(M.vert e, M.head e) ≠ s(M.vert d, M.head d) :=
        fun h => hne (M.forest_no_parallel S hS e d he hd h)
      have heH : H.Adj (M.vert e) (M.head e) := by
        apply SimpleGraph.deleteEdges_adj.mpr
        exact ⟨⟨M.forest_no_loop S hS e he, e, he, rfl, rfl⟩,
          by simpa only [Set.mem_singleton_iff] using hends⟩
      have hi : H.Reachable (M.vert d) (M.vert e) ↔
          H.Reachable (M.vert d) (M.head e) :=
        ⟨fun h => h.trans heH.reachable, fun h => h.trans heH.symm.reachable⟩
      simp only [RotationSystem.vertexGradient, a, hi, sub_self]
    have hnonneg (e : M.Dart) : 0 ≤ M.vertexGradient a e * M.facialGradient b e := by
      by_cases he : M.edgeOf e ∈ S
      · by_cases hed : M.edgeOf e = M.edgeOf d
        · rcases (M.edgeOf_eq_iff d e).mp hed.symm with rfl | rfl
          · rw [had]
            exact mul_self_nonneg _
          · rw [M.vertexGradient_inv, M.facialGradient_inv, neg_mul_neg, had]
            exact mul_self_nonneg _
        · rw [hae e he hed, zero_mul]
      · rw [hb e he, mul_zero]
    have hz := M.gradients_orthogonal a b
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun e _ => hnonneg e)).mp hz d
      (Finset.mem_univ _)
    rw [had] at hterm
    exact mul_self_eq_zero.mp hterm
  · exact hb d hd

-- @node: SphereMap.face_potential_constant_of_forest
/-- For a [connected sphere map](hyp:hM), suppose [a set of primal edges is a spanning forest](hyp:hS) and [a real face potential agrees on the two sides of every edge outside the forest](hyp:hb). Then [the potential takes the same value on every pair of faces](goal). -/
lemma face_potential_constant_of_forest (M : SphereMap) (hM : M.IsConnectedMap)
    (S : Set M.Edge) (hS : IsSpanningForest M S) (b : M.Face → ℝ)
    (hb : ∀ d, M.edgeOf d ∉ S → b (M.faceOf d) = b (M.faceOf (M.edgeInv d))) :
    ∀ f g, b f = b g := by
  cases isEmpty_or_nonempty M.Dart with
  | inl hempty =>
    let : IsEmpty M.Dart := hempty
    let : Subsingleton M.Face := M.face_subsingleton_of_no_darts hM
    intro f g
    exact congrArg b (Subsingleton.elim _ _)
  | inr hnonempty =>
    let : Nonempty M.Dart := hnonempty
    obtain ⟨q, hq⟩ := M.exists_faceEquivOrbit hM
    have hqd (d : M.Dart) : q.symm (orbitOf M.facePerm d) = M.faceOf d := by
      rw [← hq d, q.symm_apply_apply]
    let b' : M.FaceOrbit → ℝ := fun f => b (q.symm f)
    have hz : ∀ d, M.facialGradient b' d = 0 := by
      apply M.facialGradient_zero_of_forest S hS b'
      intro d hd
      simp only [RotationSystem.facialGradient, b', hqd, hb d hd, sub_self]
    intro f g
    have hc := M.facialGradient_zero_constant hM b' hz (q f) (q g)
    simpa only [b', q.symm_apply_apply] using hc

-- @node: SphereMap.dual_compl_connected
/-- For a [connected sphere map](hyp:hM), if [a set of primal edges forms a spanning forest](hyp:hS), then [the dual graph retaining precisely the complementary edges is connected](goal). -/
lemma dual_compl_connected (M : SphereMap) (hM : M.IsConnectedMap)
    (S : Set M.Edge) (hS : IsSpanningForest M S) :
    ((M.dual hM).spanningGraph Sᶜ).Connected := by
  let G := (M.dual hM).spanningGraph Sᶜ
  have hface : Nonempty M.Face := by
    obtain ⟨v⟩ := hM.nonempty
    by_cases hd : ∃ d, M.vert d = v
    · exact ⟨M.faceOf (Classical.choose hd)⟩
    · exact ⟨M.boundaryFace (Sum.inr ⟨v, fun d he => hd ⟨d, he⟩⟩)⟩
  let : Nonempty (M.dual hM).Vertex := hface
  refine ⟨?_⟩
  intro f g
  let b : M.Face → ℝ := fun x => if G.connectedComponentMk x = G.connectedComponentMk f
    then 0 else 1
  have hb (d : M.Dart) (hd : M.edgeOf d ∉ S) :
      b (M.faceOf d) = b (M.faceOf (M.edgeInv d)) := by
    have he : G.connectedComponentMk (M.faceOf d) =
        G.connectedComponentMk (M.faceOf (M.edgeInv d)) := by
      by_cases hf : M.faceOf d = M.faceOf (M.edgeInv d)
      · exact congrArg G.connectedComponentMk hf
      · apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        exact ⟨hf, d, hd, rfl, rfl⟩
    simp only [b, he]
  have hc := M.face_potential_constant_of_forest hM S hS b hb g f
  have heq : G.connectedComponentMk g = G.connectedComponentMk f := by
    by_contra hn
    simp only [b, if_neg hn, if_pos rfl] at hc
    norm_num at hc
  exact SimpleGraph.ConnectedComponent.exact heq.symm

end SphereMap
end OaiPairedStatesHamiltonian
