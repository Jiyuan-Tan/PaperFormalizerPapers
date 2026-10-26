module
public import Papers.OaiSharpThresholdMonotone.Helpers.Restriction

/-! # Permutations within a block and restricted influence orbits -/

@[expose] public section

open scoped BigOperators
open Causalean.Experimentation.DesignBased

namespace Papers.OaiSharpThresholdMonotone

variable {n : ℕ}

/-- If [a vertex permutation fixes every vertex outside B](hyp:hτ) and [an edge
has at least one endpoint in B](hyp:he), [the permuted edge also has at least one
endpoint in B](goal). -/
-- @node: edgePerm_mem_freeEdges
lemma edgePerm_mem_freeEdges (B : Finset (Fin n)) (τ : Equiv.Perm (Fin n))
    (hτ : ∀ v, v ∉ B → τ v = v) (e : GraphEdge n) (he : e ∈ freeEdges B) :
    edgePerm τ e ∈ freeEdges B := by
  classical
  obtain ⟨v, hv⟩ := (Finset.mem_filter.mp he).2
  obtain ⟨hve, hvB⟩ := Finset.mem_inter.mp hv
  have hτv : τ v ∈ B := by
    by_contra h
    have hfix := hτ (τ v) h
    have heq : τ v = v := τ.injective hfix
    exact h (heq.symm ▸ hvB)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, τ v, Finset.mem_inter.mpr ⟨?_, hτv⟩⟩
  exact Finset.mem_map.mpr ⟨v, hve, rfl⟩

-- @node: restrictedEdgePerm
/-- For [a block B of vertices](hyp:B), [a vertex permutation](hyp:τ) that
[fixes every vertex outside B](hyp:hτ), and [an edge meeting B](hyp:e), the
[restricted edge map](goal) sends that edge to its permuted edge, which still meets B. -/
def restrictedEdgePerm (B : Finset (Fin n)) (τ : Equiv.Perm (Fin n))
    (hτ : ∀ v, v ∉ B → τ v = v) (e : {e // e ∈ freeEdges B}) :
    {e // e ∈ freeEdges B} :=
  ⟨edgePerm τ e.val, edgePerm_mem_freeEdges B τ hτ e.val e.property⟩

-- @node: edgePerm_eq_of_not_mem_freeEdges
/-- If [a vertex permutation fixes every vertex outside B](hyp:hτ) and [an edge
has no endpoint in B](hyp:he), [the permutation leaves that edge unchanged](goal). -/
lemma edgePerm_eq_of_not_mem_freeEdges (B : Finset (Fin n))
    (τ : Equiv.Perm (Fin n)) (hτ : ∀ v, v ∉ B → τ v = v)
    (e : GraphEdge n) (he : e ∉ freeEdges B) : edgePerm τ e = e := by
  classical
  apply Subtype.ext
  change e.val.map τ.toEmbedding = e.val
  ext v
  constructor
  · intro hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hv
    have huB : u ∉ B := by
      intro h
      exact he (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, u, Finset.mem_inter.mpr ⟨hu, h⟩⟩)
    simpa only [Equiv.toEmbedding_apply, hτ u huB] using hu
  · intro hv
    have hvB : v ∉ B := by
      intro h
      exact he (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, v, Finset.mem_inter.mpr ⟨hv, h⟩⟩)
    exact Finset.mem_map.mpr ⟨v, hv, hτ v hvB⟩

-- @node: restrictedFunction_invariant
/-- If [a Boolean graph function is invariant under vertex permutations](hyp:hf)
and [a vertex permutation fixes every vertex outside B](hyp:hτ), then for
[an assignment of Boolean values to the edges meeting B](hyp:x), [fixing all edges
that do not meet B leaves a restricted function whose value at this assignment is
unchanged when the assignment is composed with that permutation's edge map](goal). -/
lemma restrictedFunction_invariant (f : GraphConfig n → Bool) (hf : GraphSymmetric f)
    (B : Finset (Fin n)) (y : {e // e ∉ freeEdges B} → Bool)
    (τ : Equiv.Perm (Fin n)) (hτ : ∀ v, v ∉ B → τ v = v)
    (x : {e // e ∈ freeEdges B} → Bool) :
    restrictFn f (freeEdges B) y (fun e => x (restrictedEdgePerm B τ hτ e)) =
      restrictFn f (freeEdges B) y x := by
  classical
  unfold restrictFn
  have hmerge : mergeAssignment (freeEdges B)
      (fun e => x (restrictedEdgePerm B τ hτ e)) y =
      fun e => mergeAssignment (freeEdges B) x y (edgePerm τ e) := by
    funext e
    by_cases he : e ∈ freeEdges B
    · simp [mergeAssignment, he, edgePerm_mem_freeEdges B τ hτ e he,
        restrictedEdgePerm]
    · simp [mergeAssignment, he, edgePerm_eq_of_not_mem_freeEdges B τ hτ e he]
  rw [hmerge]
  exact hf τ (mergeAssignment (freeEdges B) x y)

-- @node: restrictedCoordInfluence_orbit_eq
/-- If [the bias is strictly between zero and one](hyp:hp), [the Boolean graph
function is invariant under vertex permutations](hyp:hf), and [a vertex permutation
fixes every vertex outside B](hyp:hτ), then for [an edge meeting B](hyp:e),
[after fixing all edges that do not meet B, the coordinate influence of this edge
equals that of its permuted edge](goal). -/
lemma restrictedCoordInfluence_orbit_eq (p : ℝ) (hp : BiasInterior p)
    (f : GraphConfig n → Bool) (hf : GraphSymmetric f) (B : Finset (Fin n))
    (y : {e // e ∉ freeEdges B} → Bool) (τ : Equiv.Perm (Fin n))
    (hτ : ∀ v, v ∉ B → τ v = v) (e : {e // e ∈ freeEdges B}) :
    coordInfluence p (restrictFn f (freeEdges B) y) (restrictedEdgePerm B τ hτ e) =
      coordInfluence p (restrictFn f (freeEdges B) y) e := by
  classical
  let J := {e // e ∈ freeEdges B}
  let h := restrictFn f (freeEdges B) y
  have hinj : Function.Injective (restrictedEdgePerm B τ hτ) := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact Finset.map_injective τ.toEmbedding
      (congrArg (fun c => c.val.val) hab)
  let q : Equiv.Perm J := Equiv.ofBijective _ hinj.bijective_of_finite
  let Q : Equiv.Perm (J → Bool) :=
    { toFun := fun x j => x (q j)
      invFun := fun x j => x (q.symm j)
      left_inv := by intro x; funext j; simp
      right_inv := by intro x; funext j; simp }
  have hweight (x : J → Bool) : (biasedLaw J p).p (Q x) = (biasedLaw J p).p x := by
    simp only [biasedLaw_eq_bernoulliDesign p ⟨hp.1.le, hp.2.le⟩,
      bernoulliDesign, prodDesign_p, coinDesign]
    exact Equiv.prod_comp q (fun j => cond (x j) p (1 - p))
  have hinv (x : J → Bool) : h (Q x) = h x :=
    restrictedFunction_invariant f hf B y τ hτ x
  have hreplace (x : J → Bool) (b : Bool) :
      coordinateReplace e (Q x) b = Q (coordinateReplace (q e) x b) := by
    funext j
    simp only [coordinateReplace,
      Causalean.Mathlib.Probability.PoissonAddOnePoincare.coordinateReplace, Q]
    have heq : q j = q e ↔ j = e := q.injective.eq_iff
    simp [Function.update_apply, heq]
  have hdiff (x : J → Bool) : coordDiff h e (Q x) = coordDiff h (q e) x := by
    simp only [coordDiff, coordDiffR, boolValue, hreplace, hinv]
  rw [← difference_secondMoment_eq_influence, ← difference_secondMoment_eq_influence]
  change (biasedLaw J p).E (fun x => coordDiff h (q e) x ^ 2) =
    (biasedLaw J p).E (fun x => coordDiff h e x ^ 2)
  unfold Causalean.Experimentation.DesignBased.FiniteDesign.E
  rw [← Equiv.sum_comp Q (fun x => (biasedLaw J p).p x * coordDiff h e x ^ 2)]
  simp only [hweight, hdiff]

/-- If [w is outside the vertex block B](hyp:hw), [the number of edges containing
w and meeting B equals the number of vertices in B](goal). -/
-- @node: exterior_edge_orbit_card
lemma exterior_edge_orbit_card (B : Finset (Fin n)) (w : Fin n)
    (hw : w ∉ B) : -- @realizes w(exterior vertex)
    (Finset.univ.filter (fun e : GraphEdge n => w ∈ e.val ∧
      (e.val ∩ B).Nonempty)).card = B.card := by
  classical
  have huw (u : Fin n) (hu : u ∈ B) : u ≠ w := by
    intro h
    exact hw (h ▸ hu)
  let edge (u : Fin n) (hu : u ∈ B) : GraphEdge n :=
    ⟨{u, w}, by simp [huw u hu]⟩
  symm
  apply Finset.card_bij edge
  · intro u hu
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, u, ?_⟩
    · simp [edge]
    · simp [edge, hu]
  · intro u hu v hv huv
    have hval := congrArg Subtype.val huv
    change ({u, w} : Finset (Fin n)) = {v, w} at hval
    have humem : u ∈ ({v, w} : Finset (Fin n)) := by
      rw [← hval]
      simp
    simpa [huw u hu] using humem
  · intro e he
    obtain ⟨_, hwe, u, hu⟩ := Finset.mem_filter.mp he
    obtain ⟨hue, huB⟩ := Finset.mem_inter.mp hu
    refine ⟨u, huB, ?_⟩
    apply Subtype.ext
    change {u, w} = e.val
    apply Finset.eq_of_subset_of_card_le
    · simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hue hwe
    · simp [e.property, huw u huB]

/-- If [a belongs to the vertex block B](hyp:ha), [b belongs to B](hyp:hb),
[c belongs to B](hyp:hc), [d belongs to B](hyp:hd), [a and b are distinct](hyp:hab),
and [c and d are distinct](hyp:hcd), [there exists a vertex permutation fixing every
vertex outside B and sending a to c and b to d](goal). -/
-- @node: block_pair_permutation
lemma block_pair_permutation (B : Finset (Fin n)) (a b c d : Fin n)
    (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B) (hd : d ∈ B)
    (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ τ : Equiv.Perm (Fin n), (∀ v, v ∉ B → τ v = v) ∧ τ a = c ∧ τ b = d := by
  classical
  let σ := Equiv.swap a c
  have hσa : σ a = c := Equiv.swap_apply_left _ _
  have hσb : σ b ≠ c := by
    rw [← hσa]
    exact fun h => hab (σ.injective h).symm
  have hσbB : σ b ∈ B := by
    by_cases hba : b = a
    · subst b; simpa [σ] using hc
    · by_cases hbc : b = c
      · subst b; simpa [σ] using ha
      · simpa [σ, Equiv.swap_apply_of_ne_of_ne hba hbc] using hb
  refine ⟨σ.trans (Equiv.swap (σ b) d), ?_, ?_, ?_⟩
  · intro v hv
    have hva : v ≠ a := fun h => hv (h ▸ ha)
    have hvc : v ≠ c := fun h => hv (h ▸ hc)
    have hvb : v ≠ σ b := fun h => hv (h ▸ hσbB)
    have hvd : v ≠ d := fun h => hv (h ▸ hd)
    simp [Equiv.trans_apply, σ, Equiv.swap_apply_of_ne_of_ne, hva, hvc, hvb, hvd]
  · simp only [Equiv.trans_apply, hσa]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hσb) hcd
  · simp

/-- If [the vertex block B has at least three vertices](hyp:hm) and [an edge e
has at least one endpoint in B](hyp:he), [the number of distinct images of e under
vertex permutations fixing every vertex outside B is at least the number of vertices
in B](goal). -/
-- @node: free_edge_orbit_card_ge
lemma free_edge_orbit_card_ge (B : Finset (Fin n)) (hm : 3 ≤ B.card)
    (e : GraphEdge n) (he : e ∈ freeEdges B) :
    B.card ≤ (Finset.univ.filter (fun e' : GraphEdge n =>
      ∃ τ : Equiv.Perm (Fin n), (∀ v, v ∉ B → τ v = v) ∧ edgePerm τ e = e')).card := by
  classical
  let O := Finset.univ.filter (fun e' : GraphEdge n =>
    ∃ τ : Equiv.Perm (Fin n), (∀ v, v ∉ B → τ v = v) ∧ edgePerm τ e = e')
  obtain ⟨a, ha⟩ := (Finset.mem_filter.mp he).2
  obtain ⟨hae, haB⟩ := Finset.mem_inter.mp ha
  obtain ⟨b, hbe, hba⟩ := e.val.exists_mem_ne (by rw [e.property]; omega) a
  have hepair : e.val = {a, b} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hae hbe
    · simp [e.property, hba.symm]
  by_cases hbB : b ∈ B
  · let S := Finset.univ.filter (fun e' : GraphEdge n => e'.val ⊆ B)
    have hcard : S.card = B.card.choose 2 := by
      rw [← Finset.card_powersetCard]
      symm
      apply Finset.card_bij (fun t ht => (⟨t, (Finset.mem_powersetCard.mp ht).2⟩ : GraphEdge n))
      · intro t ht
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_powersetCard.mp ht).1⟩
      · intro t ht u hu h
        exact congrArg Subtype.val h
      · intro e' he'
        exact ⟨e'.val, Finset.mem_powersetCard.mpr
          ⟨(Finset.mem_filter.mp he').2, e'.property⟩, rfl⟩
    have hSO : S ⊆ O := by
      intro e' he'
      have hsub := (Finset.mem_filter.mp he').2
      obtain ⟨c, d, hcd, hpair⟩ := Finset.card_eq_two.mp e'.property
      have hc : c ∈ B := hsub (by simp [hpair])
      have hd : d ∈ B := hsub (by simp [hpair])
      obtain ⟨τ, hfix, hτa, hτb⟩ := block_pair_permutation B a b c d haB hbB hc hd hba.symm hcd
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, τ, hfix, ?_⟩
      apply Subtype.ext
      simp [edgePerm, hepair, hpair, hτa, hτb]
    have hchoose : B.card ≤ B.card.choose 2 := by
      rw [Nat.choose_two_right]
      have hmul := Nat.mul_le_mul_left B.card (show 2 ≤ B.card - 1 by omega)
      omega
    exact hchoose.trans (hcard ▸ Finset.card_le_card hSO)
  · let S := Finset.univ.filter (fun e' : GraphEdge n =>
      b ∈ e'.val ∧ (e'.val ∩ B).Nonempty)
    have hSO : S ⊆ O := by
      intro e' he'
      obtain ⟨_, hbe', c, hc⟩ := Finset.mem_filter.mp he'
      obtain ⟨hce', hcB⟩ := Finset.mem_inter.mp hc
      have hcb : c ≠ b := fun h => hbB (h ▸ hcB)
      have he'pair : e'.val = {c, b} := by
        symm
        apply Finset.eq_of_subset_of_card_le
        · simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using
            And.intro hce' hbe'
        · simp [e'.property, hcb]
      let τ := Equiv.swap a c
      have hfix : ∀ v, v ∉ B → τ v = v := by
        intro v hv
        exact Equiv.swap_apply_of_ne_of_ne (fun h => hv (h ▸ haB))
          (fun h => hv (h ▸ hcB))
      have hτb : τ b = b := hfix b hbB
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, τ, hfix, ?_⟩
      apply Subtype.ext
      simp [edgePerm, hepair, he'pair, hτb, τ]
    calc
      B.card = S.card := (exterior_edge_orbit_card B b hbB).symm
      _ ≤ O.card := Finset.card_le_card hSO

-- @node: restrictedFunction_smallIndividualInfluences
/-- If [the bias is strictly between zero and one](hyp:hp), [the Boolean graph
function is invariant under vertex permutations](hyp:hf), and [the block B contains
at least three vertices](hyp:hm), [after fixing any assignment of edges that do not
meet B, each remaining coordinate influence is at most the total coordinate influence
divided by the number of vertices in B](goal). -/
lemma restrictedFunction_smallIndividualInfluences (p : ℝ) (hp : BiasInterior p)
    (f : GraphConfig n → Bool) (hf : GraphSymmetric f) (B : Finset (Fin n))
    (hm : 3 ≤ B.card) (y : {e // e ∉ freeEdges B} → Bool) :
    SmallIndividualInfluences p (restrictFn f (freeEdges B) y) B.card := by
  classical
  intro i
  let J := {e // e ∈ freeEdges B}
  let h := restrictFn f (freeEdges B) y
  let O := Finset.univ.filter (fun e' : GraphEdge n =>
    ∃ τ : Equiv.Perm (Fin n), (∀ v, v ∉ B → τ v = v) ∧ edgePerm τ i.val = e')
  let F := Finset.univ.filter (fun j : J =>
    ∃ τ : Equiv.Perm (Fin n), (∀ v, v ∉ B → τ v = v) ∧ edgePerm τ i.val = j.val)
  have hfree (e' : GraphEdge n) (he' : e' ∈ O) : e' ∈ freeEdges B := by
    obtain ⟨_, τ, hfix, rfl⟩ := Finset.mem_filter.mp he'
    exact edgePerm_mem_freeEdges B τ hfix i.val i.property
  have hcard : O.card = F.card := by
    apply Finset.card_bij (fun e' he' => (⟨e', hfree e' he'⟩ : J))
    · intro e' he'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp he').2⟩
    · intro e' he' e'' he'' heq
      exact congrArg Subtype.val heq
    · intro j hj
      exact ⟨j.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp hj).2⟩, rfl⟩
  have hsize : B.card ≤ F.card := by
    rw [← hcard]
    exact free_edge_orbit_card_ge B hm i.val i.property
  have hequal (j : J) (hj : j ∈ F) : coordInfluence p h j = coordInfluence p h i := by
    obtain ⟨_, τ, hfix, heq⟩ := Finset.mem_filter.mp hj
    have hsub : restrictedEdgePerm B τ hfix i = j := Subtype.ext heq
    rw [← hsub]
    exact restrictedCoordInfluence_orbit_eq p hp f hf B y τ hfix i
  have hsum : (F.card : ℝ) * coordInfluence p h i = ∑ j ∈ F, coordInfluence p h j := by
    rw [Finset.sum_congr rfl (fun j hj => hequal j hj)]
    simp
  have hbound : (B.card : ℝ) * coordInfluence p h i ≤ totalCoordInfluence p h := by
    calc
      (B.card : ℝ) * coordInfluence p h i ≤ (F.card : ℝ) * coordInfluence p h i :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hsize) (coordInfluence_nonneg_le_one p h i).1
      _ = ∑ j ∈ F, coordInfluence p h j := hsum
      _ ≤ totalCoordInfluence p h :=
        Finset.sum_le_univ_sum_of_nonneg (fun j => (coordInfluence_nonneg_le_one p h j).1)
  have hmpos : (0 : ℝ) < B.card := Nat.cast_pos.mpr (by omega)
  exact (le_div_iff₀ hmpos).mpr (by simpa only [mul_comm] using hbound)

end Papers.OaiSharpThresholdMonotone
