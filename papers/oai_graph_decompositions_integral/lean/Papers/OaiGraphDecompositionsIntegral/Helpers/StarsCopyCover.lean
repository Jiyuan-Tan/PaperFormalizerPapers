module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.StarsCounting
public import Papers.OaiGraphDecompositionsIntegral.Helpers.BernoulliTests
public import Papers.OaiGraphDecompositionsIntegral.Helpers.StarsComponents
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Finset.Powerset

/-! # Finite families of disjoint centered stars

An unordered family of centered stars avoids dividing by automorphism groups.
Taking edge unions can only decrease the number of members, including for
one-edge stars, whose two possible centers give duplicate edge sets.
-/

@[expose] public section

open scoped BigOperators

namespace Papers.OaiGraphDecompositionsIntegral

attribute [local instance] Classical.propDecidable

-- @node: centeredStarSupport
/-- For [a center and a finite set of leaves](hyp:S), the [vertex support of the
centered star](goal) consists of the center together with those leaves. -/
def centeredStarSupport {n : ℕ} (S : Fin n × Finset (Fin n)) : Finset (Fin n) :=
  insert S.1 S.2

-- @node: centeredStarEdges
/-- For [a center and a finite set of leaves](hyp:S), the [edge set of the
centered star](goal) consists of the edges joining the center to a leaf. -/
def centeredStarEdges {n : ℕ} (S : Fin n × Finset (Fin n)) : Finset (KEdge n) :=
  Finset.univ.filter (fun e => ∃ y ∈ S.2, e.val = s(S.1, y))

-- @node: centeredStarUniverse
/-- On [a vertex set of size n](hyp:n), the [universe of centered stars](goal)
contains every choice of a center and [ell leaves](hyp:ell), with the center
excluded from the leaves. -/
def centeredStarUniverse (n ell : ℕ) : Finset (Fin n × Finset (Fin n)) :=
  (Finset.univ.product (Finset.univ.powersetCard ell)).filter (fun S => S.1 ∉ S.2)

-- @node: disjointStarFamilies
/-- On [n vertices](hyp:n), the [families of disjoint centered stars](goal)
are the unordered collections of [m stars](hyp:m), each with [ell leaves](hyp:ell),
whose vertex supports are pairwise disjoint. -/
noncomputable def disjointStarFamilies (n ell m : ℕ) : Finset (Finset (Fin n × Finset (Fin n))) :=
  ((centeredStarUniverse n ell).powersetCard m).filter
    (fun F => (F : Set (Fin n × Finset (Fin n))).PairwiseDisjoint centeredStarSupport)

-- @node: starFamilyEdges
/-- For [a finite family of centered stars](hyp:F), its [combined edge set](goal)
is the union of the edge sets of its stars. -/
def starFamilyEdges {n : ℕ} (F : Finset (Fin n × Finset (Fin n))) : Finset (KEdge n) :=
  F.biUnion centeredStarEdges

-- @node: uniformStarEdgeFamily
/-- On [n vertices](hyp:n), the [uniform star edge family](goal) consists of
all edge sets formed by [m vertex-disjoint stars](hyp:m), each having
[ell leaves](hyp:ell). -/
noncomputable def uniformStarEdgeFamily (n ell m : ℕ) : Finset (Finset (KEdge n)) :=
  (disjointStarFamilies n ell m).image starFamilyEdges

-- @node: mem_centeredStarUniverse
/-- [A centered star belongs to the universe of stars with ell leaves exactly
when its leaf set has size ell and does not contain its center](goal). -/
lemma mem_centeredStarUniverse {n ell : ℕ} (S : Fin n × Finset (Fin n)) :
    S ∈ centeredStarUniverse n ell ↔ S.2.card = ell ∧ S.1 ∉ S.2 := by
  simp [centeredStarUniverse]

-- @node: centered_star_edges_card
/-- If [the center does not belong to the leaf set](hyp:hS), then
[the centered star has exactly as many edges as leaves](goal). -/
lemma centered_star_edges_card {n : ℕ} (S : Fin n × Finset (Fin n))
    (hS : S.1 ∉ S.2) : (centeredStarEdges S).card = S.2.card := by
  classical
  have heq : centeredStarEdges S = Finset.univ.image (neighborhoodEdge S.2 S.1 hS) := by
    ext e
    simp only [centeredStarEdges, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image]
    constructor
    · rintro ⟨y, hy, he⟩
      exact ⟨⟨y, hy⟩, Subtype.ext he.symm⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y.val, y.property, rfl⟩
  rw [heq, Finset.card_image_of_injective _ (neighborhoodEdge_injective _ _ _)]
  simp

-- @node: centered_star_edges_disjoint
/-- If [two centered stars have disjoint vertex supports](hyp:h), then
[their edge sets are disjoint](goal). -/
lemma centered_star_edges_disjoint {n : ℕ} (S T : Fin n × Finset (Fin n))
    (h : Disjoint (centeredStarSupport S) (centeredStarSupport T)) :
    Disjoint (centeredStarEdges S) (centeredStarEdges T) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨y, hy, hey⟩ := (Finset.mem_filter.mp he).2
  obtain ⟨z, hz, hez⟩ := (Finset.mem_filter.mp hf).2
  have heq : s(S.1, y) = s(T.1, z) := hey.symm.trans hez
  have hmem : S.1 ∈ centeredStarSupport S := by simp [centeredStarSupport]
  rcases Sym2.eq_iff.mp heq with heq | heq
  · exact Finset.disjoint_left.mp h hmem
      (by simp [centeredStarSupport, heq.1])
  · exact Finset.disjoint_left.mp h hmem
      (by simp [centeredStarSupport, heq.1, hz])

-- @node: centered_star_universe_card_le
/-- [The number of centered stars with ell leaves on n vertices is at most
n to the power ell plus one, divided by ell factorial](goal). -/
lemma centered_star_universe_card_le (n ell : ℕ) :
    ((centeredStarUniverse n ell).card : ℝ) ≤
      (n : ℝ) ^ (ell + 1) / ell.factorial := by
  have hc : (centeredStarUniverse n ell).card ≤ n * n.choose ell := by
    apply (Finset.card_filter_le _ _).trans
    simp [Finset.card_product, Finset.card_powersetCard]
  calc
    ((centeredStarUniverse n ell).card : ℝ) ≤ (n : ℝ) * n.choose ell := by
      exact_mod_cast hc
    _ ≤ (n : ℝ) * ((n : ℝ) ^ ell / ell.factorial) :=
      mul_le_mul_of_nonneg_left (Nat.choose_le_pow_div ell n) (by positivity)
    _ = _ := by rw [pow_succ]; ring

-- @node: uniform_star_edge_family_card_le
/-- [The number of distinct edge sets formed by m disjoint stars with ell
leaves on n vertices is at most the star copy-count bound](goal). -/
lemma uniform_star_edge_family_card_le (n ell m : ℕ) :
    ((uniformStarEdgeFamily n ell m).card : ℝ) ≤ starCopyCountBound n ell m := by
  classical
  have hc : (uniformStarEdgeFamily n ell m).card ≤
      (centeredStarUniverse n ell).card.choose m := by
    calc
      _ ≤ (disjointStarFamilies n ell m).card := Finset.card_image_le
      _ ≤ ((centeredStarUniverse n ell).powersetCard m).card := Finset.card_filter_le _ _
      _ = _ := Finset.card_powersetCard _ _
  calc
    ((uniformStarEdgeFamily n ell m).card : ℝ) ≤
        ((centeredStarUniverse n ell).card.choose m : ℝ) := by exact_mod_cast hc
    _ ≤ ((centeredStarUniverse n ell).card : ℝ) ^ m / m.factorial :=
      Nat.choose_le_pow_div m _
    _ ≤ ((n : ℝ) ^ (ell + 1) / ell.factorial) ^ m / m.factorial := by
      gcongr
      exact centered_star_universe_card_le n ell
    _ = starCopyCountBound n ell m := by
      unfold starCopyCountBound
      rw [div_pow, ← pow_mul, Nat.mul_comm (ell + 1) m, div_div]

-- @node: uniform_star_edge_family_edge_card
/-- If [an edge set belongs to the family formed by m disjoint stars with
ell leaves each](hyp:hE), then [it has exactly m times ell edges](goal). -/
lemma uniform_star_edge_family_edge_card {n ell m : ℕ} (E : Finset (KEdge n))
    (hE : E ∈ uniformStarEdgeFamily n ell m) : E.card = m * ell := by
  classical
  obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hE
  obtain ⟨hF, hdis⟩ := Finset.mem_filter.mp hF
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hF
  have hd : (F : Set (Fin n × Finset (Fin n))).PairwiseDisjoint centeredStarEdges := by
    intro S hS T hT hne
    exact centered_star_edges_disjoint S T (hdis hS hT hne)
  rw [starFamilyEdges, Finset.card_biUnion hd]
  calc
    ∑ S ∈ F, (centeredStarEdges S).card = ∑ _S ∈ F, ell := by
      apply Finset.sum_congr rfl
      intro S hS
      obtain ⟨hs, hn⟩ := (mem_centeredStarUniverse S).mp (hsub hS)
      exact (centered_star_edges_card S hn).trans hs
    _ = m * ell := by simp [hcard]

/-- If [every chosen leaf is adjacent to the chosen center in the source
graph](hyp:hL), then [transporting that center and its leaves along a copy
produces a centered star whose edges all belong to the host edge set](goal). -/
-- @node: centered_star_edges_subset_of_copy
lemma centered_star_edges_subset_of_copy {V : Type}
    (J : SimpleGraph V) {n : ℕ} (G : Finset (KEdge n))
    (f : J.Copy (graphOfEdges G)) (c : V) (L : Finset V)
    (hL : ∀ y ∈ L, J.Adj c y) :
    centeredStarEdges (f c, L.image f) ⊆ G := by
  intro e he
  obtain ⟨v, hv, heq⟩ := (Finset.mem_filter.mp he).2
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
  have hehost : e.val ∈ (graphOfEdges G).edgeSet := by
    rw [heq]
    exact f.toHom.map_adj (hL y hy)
  have hex : ∃ h : ¬ e.val.IsDiag, decide ((⟨e.val, h⟩ : KEdge n) ∈ G) = true := by
    simp only [graphOfEdges, hostGraph, SimpleGraph.edgeSet_fromEdgeSet,
      Set.mem_sdiff, Set.mem_ofPred_eq] at hehost
    exact hehost.1
  obtain ⟨h, hh⟩ := hex
  exact of_decide_eq_true hh

/-- If [the source graph is a star forest](hyp:hstar) and [ell is at least
one](hyp:hell), then [every host edge set containing a copy of the source
contains a member of the uniform star edge family, with one ell-leaf star
for each source component of size ell plus one](goal). -/
-- @node: uniform_star_edge_family_covers
lemma uniform_star_edge_family_covers {V : Type} [Fintype V]
    (J : SimpleGraph V) (hstar : IsStarForest J)
    (n ell : ℕ) (hell : 1 ≤ ell) :
    Covers (uniformStarEdgeFamily n ell (starMultiplicity J hstar ell hell))
      (containmentFamily J n) := by
  classical
  intro G hG
  obtain ⟨f⟩ := hG
  let I := {C : J.ConnectedComponent // C.supp.toFinset.card = ell + 1}
  have hcenters : ∀ i : I, ∃ c ∈ i.val.supp,
      ∀ u ∈ i.val.supp, ∀ w ∈ i.val.supp,
        J.Adj u w ↔ u ≠ w ∧ (u = c ∨ w = c) := by
    intro i
    apply hstar.components
    apply Set.one_lt_ncard_iff_nontrivial.mp
    rw [Set.ncard_eq_toFinset_card', i.property]
    omega
  choose center hcenter hadj using hcenters
  let S : I → Fin n × Finset (Fin n) := fun i =>
    (f (center i), (i.val.supp.toFinset.erase (center i)).image f)
  have hsupp (i : I) : centeredStarSupport (S i) = i.val.supp.toFinset.image f := by
    change insert (f (center i)) ((i.val.supp.toFinset.erase (center i)).image f) = _
    rw [← Finset.image_insert, Finset.insert_erase (Set.mem_toFinset.mpr (hcenter i))]
  have hSin (i : I) : S i ∈ centeredStarUniverse n ell := by
    apply (mem_centeredStarUniverse _).mpr
    constructor
    · change ((i.val.supp.toFinset.erase (center i)).image f).card = ell
      rw [Finset.card_image_of_injective _
          (show Function.Injective (fun x => f x) from f.injective),
        Finset.card_erase_of_mem (Set.mem_toFinset.mpr (hcenter i)), i.property]
      omega
    · intro hmem
      obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hmem
      exact (Finset.mem_erase.mp hy).1 (f.injective he)
  have hdis (i j : I) (hne : i ≠ j) :
      Disjoint (centeredStarSupport (S i)) (centeredStarSupport (S j)) := by
    rw [hsupp, hsupp]
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, he⟩ := Finset.mem_image.mp hy
    have hab : b = a := f.injective he
    have hcomp : i.val ≠ j.val := fun h => hne (Subtype.ext h)
    exact Set.disjoint_left.mp (J.pairwise_disjoint_supp_connectedComponent hcomp)
      (Set.mem_toFinset.mp ha) (hab ▸ Set.mem_toFinset.mp hb)
  have hS_inj : Function.Injective S := by
    intro i j he
    by_contra hne
    have hm : f (center i) ∈ centeredStarSupport (S i) := by
      change f (center i) ∈ insert (f (center i)) _
      exact Finset.mem_insert_self _ _
    exact Finset.disjoint_left.mp (hdis i j hne) hm (he ▸ hm)
  have hcardI : Fintype.card I = starMultiplicity J hstar ell hell := by
    simp only [I, Fintype.card_subtype, starMultiplicity]
  let F := Finset.univ.image S
  have hF : F ∈ disjointStarFamilies n ell (starMultiplicity J hstar ell hell) := by
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_powersetCard.mpr
      constructor
      · intro T hT
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hT
        exact hSin i
      · rw [Finset.card_image_of_injective _ hS_inj, Finset.card_univ, hcardI]
    · intro T hT U hU hne
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hT
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hU
      exact hdis i j (fun h => hne (congrArg S h))
  refine ⟨starFamilyEdges F, Finset.mem_image.mpr ⟨F, hF, rfl⟩, ?_⟩
  intro e he
  obtain ⟨T, hT, he⟩ := Finset.mem_biUnion.mp he
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hT
  apply centered_star_edges_subset_of_copy J G f (center i)
    (i.val.supp.toFinset.erase (center i)) ?_ he
  intro y hy
  have hy' := Finset.mem_erase.mp hy
  exact (hadj i (center i) (hcenter i) y (Set.mem_toFinset.mp hy'.2)).mpr
    ⟨Ne.symm hy'.1, Or.inl rfl⟩

/-- Suppose [the source graph is a star forest](hyp:hstar), [ell is at least
one](hyp:hell), [the source has an edge](hyp:hedge), [its vertex count is at
most n](hyp:hsize), [n is positive](hyp:hn), [the number m of its components
of size ell plus one is positive](hyp:hm), and [its expectation threshold
on n vertices is below one](hyp:hq). Then [the ell-th power of that threshold
is at least ell factorial divided by n to the power ell plus one, multiplied
by m divided by twice Euler's number](goal). -/
-- @node: star_count_lower
lemma star_count_lower {V : Type} [Fintype V]
    (J : SimpleGraph V) (hstar : IsStarForest J)
    (n ell : ℕ) (hell : 1 ≤ ell)
    (hedge : J.edgeSet.Nonempty) (hsize : Fintype.card V ≤ n)
    (hn : 0 < n) (hm : 0 < starMultiplicity J hstar ell hell)
    (hq : expectationThreshold J n < 1) :
    (ell.factorial : ℝ) / (n : ℝ) ^ (ell + 1) *
        ((starMultiplicity J hstar ell hell : ℝ) / (2 * Real.exp 1)) ≤
      expectationThreshold J n ^ ell := by
  exact star_count_lower_of_cover J n ell (starMultiplicity J hstar ell hell)
    hedge hsize hn hm hq _ (uniform_star_edge_family_covers J hstar n ell hell)
    (uniform_star_edge_family_edge_card) (uniform_star_edge_family_card_le _ _ _)

end Papers.OaiGraphDecompositionsIntegral
