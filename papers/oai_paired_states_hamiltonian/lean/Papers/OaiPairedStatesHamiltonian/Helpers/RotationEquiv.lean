module

public import Papers.OaiPairedStatesHamiltonian.Helpers.EdgeDeletion
public import Papers.OaiPairedStatesHamiltonian.Helpers.FirstReturnCompose

/-! Relabelling rotation systems preserves their componentwise Euler equations. -/

@[expose] public section
namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option backward.isDefEq.respectTransparency false
open Classical
attribute [local instance] propDecidable

-- @node: perm_sameCycle_equiv
/-- If [a bijection intertwines two permutations, meaning that applying the bijection after
the first permutation equals applying the second permutation after the bijection](hyp:he),
then [two elements lie in the same cycle of the first permutation exactly when their images
lie in the same cycle of the second](goal). -/
lemma perm_sameCycle_equiv {A B : Type} [Fintype A] [Fintype B]
    (p : Equiv.Perm A) (q : Equiv.Perm B) (e : A ≃ B)
    (he : ∀ a, e (p a) = q (e a)) (a b : A) :
    p.SameCycle a b ↔ q.SameCycle (e a) (e b) := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast, ← perm_pow_intertwine p q e he, hn]
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast]
    apply e.injective
    rw [perm_pow_intertwine p q e he, hn]

-- @node: permOrbitEquiv
/-- For [a permutation of the first finite set](hyp:p), [a permutation of the second finite
set](hyp:q), and [a bijection between those sets](hyp:e) that [intertwines the two
permutations](hyp:he), the [induced bijection between their sets of permutation cycles](goal)
sends each cycle to the cycle containing the images of its elements. -/
noncomputable def permOrbitEquiv {A B : Type} [Fintype A] [Fintype B]
    (p : Equiv.Perm A) (q : Equiv.Perm B) (e : A ≃ B)
    (he : ∀ a, e (p a) = q (e a)) : orbitType p ≃ orbitType q :=
  Equiv.ofBijective (Quotient.map e (fun {a b} h => (perm_sameCycle_equiv p q e he a b).mp h))
    ⟨by
      intro a b
      induction a using Quotient.inductionOn with
      | h a =>
        induction b using Quotient.inductionOn with
        | h b =>
          intro h
          exact Quotient.sound ((perm_sameCycle_equiv p q e he a b).mpr (Quotient.exact h)), by
      intro b
      induction b using Quotient.inductionOn with
      | h b =>
        exact ⟨orbitOf p (e.symm b), congrArg (orbitOf q) (e.apply_symm_apply b)⟩⟩

namespace RotationSystem
variable (R S : RotationSystem)

/-- Both permutations and the vertex incidence are preserved by relabelling. -/
-- @node: RotationSystem.Relabel
structure Relabel where
  vertex : R.Vertex ≃ S.Vertex
  dart : R.Dart ≃ S.Dart
  vert : ∀ d, vertex (R.vert d) = S.vert (dart d)
  inv : ∀ d, dart (R.edgeInv d) = S.edgeInv (dart d)
  rot : ∀ d, dart (R.rot d) = S.rot (dart d)

variable {R S}

-- @node: RotationSystem.Relabel.graphIso
/-- For [a source rotation system](hyp:R), [a target rotation system](hyp:S), and [a relabelling
preserving vertex incidence, edge reversal, and rotation](hyp:e), the [induced graph
isomorphism](goal) uses [the relabelling's vertex bijection](step:1) and [preserves adjacency
in both directions](step:2). -/
noncomputable def Relabel.graphIso (e : R.Relabel S) : R.toSimpleGraph ≃g S.toSimpleGraph where
  toEquiv := e.vertex
  map_rel_iff' := by
    intro v w
    change (e.vertex v ≠ e.vertex w ∧ ∃ d, S.vert d = e.vertex v ∧ S.head d = e.vertex w) ↔
      (v ≠ w ∧ ∃ d, R.vert d = v ∧ R.head d = w)
    constructor
    · rintro ⟨hne, d, hd, hh⟩
      refine ⟨fun h => hne (congrArg e.vertex h), e.dart.symm d, ?_, ?_⟩
      · apply e.vertex.injective
        rw [e.vert, e.dart.apply_symm_apply, hd]
      · apply e.vertex.injective
        change e.vertex (R.vert (R.edgeInv (e.dart.symm d))) = _
        rw [e.vert, e.inv, e.dart.apply_symm_apply]
        exact hh
    · rintro ⟨hne, d, hd, hh⟩
      refine ⟨fun h => hne (e.vertex.injective h), e.dart d, ?_, ?_⟩
      · rw [← e.vert, hd]
      · change S.vert (S.edgeInv (e.dart d)) = _
        rw [← e.inv, ← e.vert]
        exact congrArg e.vertex hh

-- @node: RotationSystem.Relabel.face
/-- For [a relabelling preserving vertex incidence, edge reversal, and rotation](hyp:e),
[relabelling the next directed edge around a face gives the same result as taking the next
directed edge around the face after relabelling](goal). -/
lemma Relabel.face (e : R.Relabel S) (d : R.Dart) :
    e.dart (R.facePerm d) = S.facePerm (e.dart d) := by
  change e.dart (R.rot (R.edgeInv d)) = S.rot (S.edgeInv (e.dart d))
  rw [e.rot, e.inv]

-- @node: RotationSystem.Relabel.punctureEquiv
/-- For [a source rotation system](hyp:R), [a target rotation system](hyp:S), and [a relabelling
preserving vertex incidence, edge reversal, and rotation](hyp:e), the [induced bijection
between punctures](goal) maps each isolated vertex by the vertex relabelling. -/
noncomputable def Relabel.punctureEquiv (e : R.Relabel S) : R.Puncture ≃ S.Puncture :=
  e.vertex.subtypeEquiv (by
    intro v
    constructor
    · intro hv d hd
      apply hv (e.dart.symm d)
      apply e.vertex.injective
      rw [e.vert, e.dart.apply_symm_apply, hd]
    · intro hv d hd
      apply hv (e.dart d)
      rw [← e.vert, hd])

-- @node: RotationSystem.Relabel.componentEuler
/-- If [two rotation systems are related by a relabelling preserving vertex incidence,
edge reversal, and rotation](hyp:e) and [each source component has its number of vertices
plus local boundaries equal to its number of edges plus two](hyp:hR), then [the same Euler
equation holds for every target component](goal). -/
lemma Relabel.componentEuler (e : R.Relabel S) (hR : R.componentEuler) : S.componentEuler := by
  apply S.componentEuler_of_global_card
  have h := R.componentEuler_global_card hR
  have hv := Nat.card_congr e.vertex
  have he := Nat.card_congr (permOrbitEquiv R.edgeInv S.edgeInv e.dart e.inv)
  have hf := Nat.card_congr (permOrbitEquiv R.facePerm S.facePerm e.dart e.face)
  have hp := Nat.card_congr e.punctureEquiv
  have hc := Nat.card_congr e.graphIso.connectedComponentEquiv
  have hb : Nat.card R.LocalBoundary = Nat.card S.LocalBoundary := by
    change Nat.card (R.FaceOrbit ⊕ R.Puncture) = Nat.card (S.FaceOrbit ⊕ S.Puncture)
    rw [Nat.card_sum, Nat.card_sum, hf, hp]
  rw [← hv, ← hb, ← he, ← hc]
  exact h

end RotationSystem
end OaiPairedStatesHamiltonian
