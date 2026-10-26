module
public import Papers.OaiUniformInfluenceHypergraph.Helpers.Fourier
public import Mathlib.Logic.Equiv.Fintype

/-! # Restriction to a vertex block and its permutation orbits

Outside assignments use the same Bernoulli design on the complementary
coordinate type. Restricted invariance and influence bounds are conclusions.
-/

@[expose] public section

open scoped BigOperators
open Causalean.Experimentation.DesignBased

namespace Papers.OaiUniformInfluenceHypergraph

variable {n r : ℕ}

/-- For [a block of vertices](hyp:B) among [n vertices](hyp:n), the
[free coordinates](goal) are the [r-vertex edges](hyp:r) that meet the block. -/
abbrev FreeCoord (B : Finset (Fin n)) := {e : Edge n r // e ∈ freeEdges B}
/-- For [a block of vertices](hyp:B) among [n vertices](hyp:n), the
[assigned coordinates](goal) are the [r-vertex edges](hyp:r) disjoint from the block. -/
abbrev AssignedCoord (B : Finset (Fin n)) := {e : Edge n r // e ∉ freeEdges B}

/-- The [merged edge assignment](goal), on [n vertices](hyp:n) with
[r vertices per edge](hyp:r), uses [the free assignment](hyp:z) on edges meeting
[the block](hyp:B) and [the assigned values](hyp:y) on all other edges. -/
def mergeAssignment (B : Finset (Fin n)) (z : FreeCoord (r := r) B → Bool)
    (y : AssignedCoord (r := r) B → Bool) : Edge n r → Bool := -- @realizes y(paper range)
  fun e => if he : e ∈ freeEdges B then z ⟨e, he⟩ else y ⟨e, he⟩

/-- The [restriction](goal) of [a Boolean hypergraph function](hyp:f) on
[n vertices](hyp:n) with [r vertices per edge](hyp:r) to [a vertex block](hyp:B)
evaluates that function after combining the free edge values with
[fixed values on edges disjoint from the block](hyp:y). -/
def restrictedFunction (f : (Edge n r → Bool) → Bool) (B : Finset (Fin n))
    (y : AssignedCoord (r := r) B → Bool) : (FreeCoord (r := r) B → Bool) → Bool :=
  fun z => f (mergeAssignment B z y) -- @realizes f_y(Boolean function on the free coordinates)

/-- A [permutation of n vertices](hyp:τ,n) is [supported on a block](goal)
if it fixes every vertex outside [that block](hyp:B). -/
def SupportedOn (B : Finset (Fin n)) (τ : Equiv.Perm (Fin n)) : Prop :=
  ∀ v, v ∉ B → τ v = v

-- @node: supportedOn_mem_iff
/-- If [a vertex permutation fixes every vertex outside the block](hyp:hτ),
[a vertex belongs to the block after permutation exactly when it belonged before](goal). -/
lemma supportedOn_mem_iff (B : Finset (Fin n)) (τ : Equiv.Perm (Fin n))
    (hτ : SupportedOn B τ) (v : Fin n) : τ v ∈ B ↔ v ∈ B := by
  constructor
  · intro h
    by_contra hv
    exact hv (hτ v hv ▸ h)
  · intro h
    by_contra hv
    have he : τ (τ v) = τ v := hτ (τ v) hv
    have : τ v = v := τ.injective he
    exact hv (this.symm ▸ h)

-- @node: edgePerm_mem_freeEdges
/-- If [a vertex permutation is supported on the block](hyp:hτ),
[an edge meets the block after permutation exactly when it met the block before](goal). -/
lemma edgePerm_mem_freeEdges (B : Finset (Fin n)) (τ : Equiv.Perm (Fin n))
    (hτ : SupportedOn B τ) (e : Edge n r) :
    edgePerm τ e ∈ freeEdges B ↔ e ∈ freeEdges B := by
  classical
  simp only [freeEdges, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.Nonempty, Finset.mem_inter, edgePerm, Finset.mem_map]
  constructor
  · rintro ⟨w, ⟨v, hv, rfl⟩, hw⟩
    exact ⟨v, hv, (supportedOn_mem_iff B τ hτ v).mp hw⟩
  · rintro ⟨v, hv, hvB⟩
    exact ⟨τ v, ⟨v, hv, rfl⟩, (supportedOn_mem_iff B τ hτ v).mpr hvB⟩

-- @node: edgePerm_eq_of_not_mem_freeEdges
/-- If [a vertex permutation is supported on the block](hyp:hτ) and
[an edge is disjoint from the block](hyp:he), [the permutation leaves that edge unchanged](goal). -/
lemma edgePerm_eq_of_not_mem_freeEdges (B : Finset (Fin n))
    (τ : Equiv.Perm (Fin n)) (hτ : SupportedOn B τ) (e : Edge n r)
    (he : e ∉ freeEdges B) : edgePerm τ e = e := by
  classical
  have hfix : ∀ v ∈ e.val, τ v = v := by
    intro v hv
    apply hτ
    intro hvB
    exact he (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨v, Finset.mem_inter.mpr ⟨hv, hvB⟩⟩⟩)
  apply Subtype.ext
  change e.val.map τ.toEmbedding = e.val
  ext v
  simp only [Finset.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa only [Equiv.coe_toEmbedding, hfix w hw] using hw
  · intro hv
    exact ⟨v, hv, hfix v hv⟩

/-- For [a block](hyp:B) among [n vertices](hyp:n) and [r vertices per edge](hyp:r),
the [permuted free edge](goal) is the image of [an edge meeting the block](hyp:e)
under [a vertex permutation](hyp:τ) that [fixes every vertex outside the block](hyp:hτ). -/
def freeEdgePerm (B : Finset (Fin n)) (τ : Equiv.Perm (Fin n)) (hτ : SupportedOn B τ)
    (e : FreeCoord (r := r) B) : FreeCoord (r := r) B :=
  ⟨edgePerm τ e.val, (edgePerm_mem_freeEdges B τ hτ e.val).mpr e.property⟩

-- @node: restrictedFunction_invariant
/-- If [the Boolean hypergraph function is invariant under vertex relabeling](hyp:hf)
and [a vertex permutation fixes the outside of the block](hyp:hτ),
[permuting the free edge values leaves the restricted function unchanged,
for any fixed assignment on the other edges](goal). -/
lemma restrictedFunction_invariant (f : (Edge n r → Bool) → Bool)
    (hf : IsHypergraphProperty f) (B : Finset (Fin n))
    (y : AssignedCoord (r := r) B → Bool) (τ : Equiv.Perm (Fin n)) (hτ : SupportedOn B τ)
    (z : FreeCoord (r := r) B → Bool) :
    restrictedFunction f B y (fun e => z (freeEdgePerm B τ hτ e)) =
      restrictedFunction f B y z := by
  classical
  have hmerge : mergeAssignment B (fun e => z (freeEdgePerm B τ hτ e)) y =
      fun e => mergeAssignment B z y (edgePerm τ e) := by
    funext e
    by_cases he : e ∈ freeEdges B
    · have hperm := (edgePerm_mem_freeEdges B τ hτ e).mpr he
      simp [mergeAssignment, he, hperm, freeEdgePerm]
    · have hperm : edgePerm τ e ∉ freeEdges B :=
        fun h => he ((edgePerm_mem_freeEdges B τ hτ e).mp h)
      simp [mergeAssignment, he, hperm, edgePerm_eq_of_not_mem_freeEdges B τ hτ e he]
  change f (mergeAssignment B (fun e => z (freeEdgePerm B τ hτ e)) y) =
    f (mergeAssignment B z y)
  rw [hmerge]
  exact hf.invariant τ (mergeAssignment B z y)

/-- The [orbit](goal) of [an r-vertex edge](hyp:e,r) among [n vertices](hyp:n)
consists of all its images under vertex permutations fixing every vertex outside
[the block](hyp:B). -/
noncomputable def edgeOrbit (B : Finset (Fin n)) (e : Edge n r) : Finset (Edge n r) :=
  open scoped Classical in
    Finset.univ.filter (fun e' => ∃ τ : Equiv.Perm (Fin n), SupportedOn B τ ∧ edgePerm τ e = e')

-- @realizes j(number of edge vertices in the block)
/-- The [inside count](goal) is the number of vertices of [an r-vertex edge](hyp:e,r)
that lie in [the block](hyp:B), within [a population of n vertices](hyp:n). -/
def insideCount (B : Finset (Fin n)) (e : Edge n r) : ℕ := (e.val ∩ B).card

-- @node: supportedOn_map_finset_exists
/-- If [the first vertex set lies in the block](hyp:hs),
[the second vertex set also lies in the block](hyp:ht), and
[the two sets have equal size](hyp:hc), [some vertex permutation fixing the outside
of the block maps the first set onto the second](goal). -/
lemma supportedOn_map_finset_exists (B s t : Finset (Fin n))
    (hs : s ⊆ B) (ht : t ⊆ B) (hc : s.card = t.card) :
    ∃ τ : Equiv.Perm (Fin n), SupportedOn B τ ∧ s.map τ.toEmbedding = t := by
  classical
  let P := fun v : Fin n => v ∈ B
  have hsm : (s.subtype P).map (Function.Embedding.subtype P) = s :=
    Finset.subtype_map_of_mem hs
  have htm : (t.subtype P).map (Function.Embedding.subtype P) = t :=
    Finset.subtype_map_of_mem ht
  have hc' : (s.subtype P).card = (t.subtype P).card := by
    simpa only [Finset.card_map] using
      (congrArg Finset.card hsm).trans (hc.trans (congrArg Finset.card htm).symm)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq (s.subtype P) (t.subtype P) hc'
  let τ := σ.extendDomain (Equiv.refl {v : Fin n // P v})
  refine ⟨τ, ?_, ?_⟩
  · intro v hv
    exact Equiv.Perm.extendDomain_apply_not_subtype _ _ hv
  · calc
      s.map τ.toEmbedding =
          ((s.subtype P).map (Function.Embedding.subtype P)).map τ.toEmbedding := by
            rw [hsm]
      _ = ((s.subtype P).map σ.toEmbedding).map (Function.Embedding.subtype P) := by
        simp only [Finset.map_map]
        congr 1
        apply Function.Embedding.ext
        intro v
        change τ v.val = (σ v).val
        exact Equiv.Perm.extendDomain_apply_subtype σ (Equiv.refl _) v.property
      _ = t := by rw [hσ, htm]

-- @node: supportedOn_map_inter
/-- If [a vertex permutation fixes every vertex outside the block](hyp:hτ),
[intersecting a permuted vertex set with the block gives the permutation of
its original intersection with the block](goal). -/
lemma supportedOn_map_inter (B s : Finset (Fin n)) (τ : Equiv.Perm (Fin n))
    (hτ : SupportedOn B τ) :
    s.map τ.toEmbedding ∩ B = (s ∩ B).map τ.toEmbedding := by
  classical
  ext v
  simp only [Finset.mem_inter, Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, hwB⟩
    exact ⟨w, ⟨hw, (supportedOn_mem_iff B τ hτ w).mp hwB⟩, rfl⟩
  · rintro ⟨w, ⟨hw, hwB⟩, rfl⟩
    exact ⟨⟨w, hw, rfl⟩, (supportedOn_mem_iff B τ hτ w).mpr hwB⟩

-- @node: supportedOn_map_sdiff
/-- If [a vertex permutation fixes every vertex outside the block](hyp:hτ),
[the part of a vertex set outside the block is unchanged by permutation](goal). -/
lemma supportedOn_map_sdiff (B s : Finset (Fin n)) (τ : Equiv.Perm (Fin n))
    (hτ : SupportedOn B τ) : s.map τ.toEmbedding \ B = s \ B := by
  classical
  ext v
  simp only [Finset.mem_sdiff, Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, hwB⟩
    have hwB' : w ∉ B := fun h => hwB ((supportedOn_mem_iff B τ hτ w).mpr h)
    simpa only [hτ w hwB'] using And.intro hw hwB'
  · rintro ⟨hv, hvB⟩
    exact ⟨⟨v, hv, hτ v hvB⟩, hvB⟩

-- @node: edgeOrbit_card
/-- [The number of edges obtainable by permuting vertices within the block equals
the number of ways to choose, from the block, as many vertices as the original
edge has inside the block](goal). -/
lemma edgeOrbit_card (B : Finset (Fin n)) (e : Edge n r) :
    (edgeOrbit B e).card = B.card.choose (insideCount B e) := by
  classical
  rw [← Finset.card_powersetCard]
  apply Finset.card_bij (fun e' _ => e'.val ∩ B)
  · intro e' he'
    obtain ⟨τ, hτ, rfl⟩ := (Finset.mem_filter.mp he').2
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.inter_subset_right, ?_⟩
    change (e.val.map τ.toEmbedding ∩ B).card = (e.val ∩ B).card
    rw [supportedOn_map_inter B e.val τ hτ, Finset.card_map]
  · intro e₁ h₁ e₂ h₂ heq
    obtain ⟨τ₁, hτ₁, rfl⟩ := (Finset.mem_filter.mp h₁).2
    obtain ⟨τ₂, hτ₂, rfl⟩ := (Finset.mem_filter.mp h₂).2
    apply Subtype.ext
    have hd : (edgePerm τ₁ e).val \ B = (edgePerm τ₂ e).val \ B := by
      change e.val.map τ₁.toEmbedding \ B = e.val.map τ₂.toEmbedding \ B
      rw [supportedOn_map_sdiff B e.val τ₁ hτ₁,
        supportedOn_map_sdiff B e.val τ₂ hτ₂]
    have hu := congrArg₂ (fun a b : Finset (Fin n) => b ∪ a) heq hd
    simpa only [Finset.sdiff_union_inter] using hu
  · intro s hs
    obtain ⟨hsB, hsc⟩ := Finset.mem_powersetCard.mp hs
    obtain ⟨τ, hτ, hmap⟩ := supportedOn_map_finset_exists B (e.val ∩ B) s
      Finset.inter_subset_right hsB hsc.symm
    refine ⟨edgePerm τ e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, τ, hτ, rfl⟩, ?_⟩
    change e.val.map τ.toEmbedding ∩ B = s
    rw [supportedOn_map_inter B e.val τ hτ, hmap]

-- @node: free_edge_insideCount
/-- [An edge meeting the block has at least one and at most r vertices inside
the block, where r is the edge size](goal). -/
lemma free_edge_insideCount (B : Finset (Fin n)) (e : FreeCoord (r := r) B) :
    1 ≤ insideCount B e.val ∧ insideCount B e.val ≤ r := by
  have hmeet : (e.val.val ∩ B).Nonempty := (Finset.mem_filter.mp e.property).2
  exact ⟨Finset.one_le_card.mpr hmeet,
    (Finset.card_le_card Finset.inter_subset_left).trans_eq e.val.property⟩

-- @node: block_choose_ge_card
/-- If [the number j to be chosen is at least one](hyp:hj) and
[j is smaller than the population size m](hyp:hjm),
[there are at least m distinct j-element subsets of that population](goal). -/
lemma block_choose_ge_card (m j : ℕ) (hj : 1 ≤ j) (hjm : j < m) :
    m ≤ m.choose j := by
  induction m generalizing j with
  | zero => omega
  | succ m ih =>
    rcases j with _ | j
    · omega
    by_cases heq : j + 1 = m
    · rw [heq, ← Nat.choose_symm (Nat.le_succ m)]
      simp
    · have hlt : j + 1 < m := by omega
      rw [Nat.choose_succ_succ]
      have hmain := ih (j + 1) (by omega) hlt
      have hpos := Nat.choose_pos (show j ≤ m by omega)
      change m + 1 ≤ m.choose j + m.choose (j + 1)
      omega

-- @node: free_edgeOrbit_card_ge
/-- If [the block has m vertices](hyp:hB) and [m is at least r plus one](hyp:hm),
[every r-vertex edge meeting the block has at least m distinct images under
permutations fixing the outside of the block](goal). -/
lemma free_edgeOrbit_card_ge (m : ℕ) (B : Finset (Fin n)) (hB : B.card = m)
    (hm : r + 1 ≤ m) (e : FreeCoord (r := r) B) :
    m ≤ (edgeOrbit B e.val).card := by
  rw [edgeOrbit_card, hB]
  obtain ⟨hlo, hhi⟩ := free_edge_insideCount B e
  exact block_choose_ge_card m (insideCount B e.val) hlo (by omega)

-- @node: biasedLaw_E_coordPerm
/-- [Permuting the coordinates of independent Boolean draws with a common bias
does not change the expectation of any real-valued function of those draws](goal). -/
lemma biasedLaw_E_coordPerm {J : Type*} [Fintype J] [DecidableEq J]
    (p : ℝ) (σ : Equiv.Perm J) (g : (J → Bool) → ℝ) :
    (biasedLaw J p).E (fun x => g (fun i => x (σ i))) = (biasedLaw J p).E g := by
  let q : Equiv.Perm (J → Bool) := Equiv.arrowCongr σ.symm (Equiv.refl Bool)
  have hweight (x : J → Bool) :
      (biasedLaw J p).p (q x) = (biasedLaw J p).p x := by
    change (∏ i : J, (coinDesign _ _ _).p (x (σ i))) =
      ∏ i : J, (coinDesign _ _ _).p (x i)
    exact Equiv.prod_comp σ (fun i => (coinDesign _ _ _).p (x i))
  change (∑ x, (biasedLaw J p).p x * g (q x)) = _
  calc
    _ = ∑ x, (biasedLaw J p).p (q x) * g (q x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [hweight]
    _ = _ := Equiv.sum_comp q (fun x => (biasedLaw J p).p x * g x)

-- @node: coordInfluence_eq_of_perm
/-- For [a Boolean function of the coordinates](hyp:h), if
[permuting coordinates leaves its value unchanged for every configuration](hyp:hh),
[each coordinate has the same influence as its image under that permutation](goal). -/
lemma coordInfluence_eq_of_perm {J : Type*} [Fintype J] [DecidableEq J]
    (p : ℝ) (h : (J → Bool) → Bool) (σ : Equiv.Perm J)
    (hh : ∀ x, h (fun i => x (σ i)) = h x) (i : J) :
    coordInfluence p h i = coordInfluence p h (σ i) := by
  classical
  have hupdate (x : J → Bool) (b : Bool) :
      replaceCoord (fun j => x (σ j)) i b =
        fun j => replaceCoord x (σ i) b (σ j) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp
    · have hσ : σ j ≠ σ i := fun h => hj (σ.injective h)
      simp [hj, hσ]
  unfold coordInfluence FiniteDesign.Pr
  rw [← biasedLaw_E_coordPerm p σ]
  apply FiniteDesign.E_congr
  intro x
  simp only [FiniteDesign.ind, hupdate, hh]

-- @node: restrictedInfluence_eq_on_orbit
/-- If [the bias lies strictly between zero and one](hyp:hp),
[the hypergraph function is invariant under vertex relabeling](hyp:hf), and
[the second free edge is an image of the first under a permutation supported
on the block](hyp:he'), [the two edges have equal influence in the restricted
function for any fixed outside assignment](goal). -/
lemma restrictedInfluence_eq_on_orbit (p : ℝ) (hp : BiasInterior p)
    (f : (Edge n r → Bool) → Bool) (hf : IsHypergraphProperty f)
    (B : Finset (Fin n)) (y : AssignedCoord (r := r) B → Bool)
    (e e' : FreeCoord (r := r) B) (he' : e'.val ∈ edgeOrbit B e.val) :
    coordInfluence p (restrictedFunction f B y) e =
      coordInfluence p (restrictedFunction f B y) e' := by
  classical
  obtain ⟨τ, hτ, heq⟩ := (Finset.mem_filter.mp he').2
  have hinj : Function.Injective (freeEdgePerm (r := r) B τ hτ) := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Finset.map_injective τ.toEmbedding
    exact congrArg (fun c : FreeCoord (r := r) B => c.val.val) hab
  let σ : Equiv.Perm (FreeCoord (r := r) B) :=
    Equiv.ofBijective (freeEdgePerm B τ hτ) ⟨hinj, Finite.surjective_of_injective hinj⟩
  have hσ : σ e = e' := Subtype.ext heq
  rw [← hσ]
  exact coordInfluence_eq_of_perm p (restrictedFunction f B y) σ
    (restrictedFunction_invariant f hf B y τ hτ) e

-- @node: restrictedFunction_smallIndividualInfluences
/-- If [the bias lies strictly between zero and one](hyp:hp),
[the hypergraph function is invariant under vertex relabeling](hyp:hf),
[the block has m vertices](hyp:hB), and [m is at least r plus one](hyp:hm),
[each free coordinate's influence in the restricted function is at most its
total coordinate influence divided by m, for any fixed outside assignment](goal). -/
lemma restrictedFunction_smallIndividualInfluences (p : ℝ) (hp : BiasInterior p)
    (f : (Edge n r → Bool) → Bool) (hf : IsHypergraphProperty f)
    (m : ℕ) (B : Finset (Fin n)) (hB : B.card = m) (hm : r + 1 ≤ m)
    (y : AssignedCoord (r := r) B → Bool) :
    SmallIndividualInfluences p (restrictedFunction f B y) m := by
  classical
  intro e
  let O := (edgeOrbit B e.val).subtype (fun a => a ∈ freeEdges B)
  have hfree : ∀ a ∈ edgeOrbit B e.val, a ∈ freeEdges B := by
    intro a ha
    obtain ⟨τ, hτ, rfl⟩ := (Finset.mem_filter.mp ha).2
    exact (edgePerm_mem_freeEdges B τ hτ e.val).mpr e.property
  have hcard : O.card = (edgeOrbit B e.val).card := by
    rw [Finset.card_subtype]
    congr 1
    exact Finset.filter_eq_self.mpr hfree
  have heq : ∀ a ∈ O, coordInfluence p (restrictedFunction f B y) a =
      coordInfluence p (restrictedFunction f B y) e := by
    intro a ha
    exact (restrictedInfluence_eq_on_orbit p hp f hf B y e a
      (Finset.mem_subtype.mp ha)).symm
  have hsum : (O.card : ℝ) * coordInfluence p (restrictedFunction f B y) e ≤
      totalCoordInfluence p (restrictedFunction f B y) := by
    calc
      _ = ∑ a ∈ O, coordInfluence p (restrictedFunction f B y) a := by
        simp_rw [Finset.sum_congr rfl heq]
        simp
      _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg
        (fun a => (coordInfluence_nonneg_le_one p (restrictedFunction f B y) a).1)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  apply (le_div_iff₀ hmpos).mpr
  calc
    _ = (m : ℝ) * coordInfluence p (restrictedFunction f B y) e := mul_comm _ _
    _ ≤ (O.card : ℝ) * coordInfluence p (restrictedFunction f B y) e :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast
        (hcard ▸ free_edgeOrbit_card_ge m B hB hm e))
        (coordInfluence_nonneg_le_one p (restrictedFunction f B y) e).1
    _ ≤ _ := hsum

-- @node: biasedLaw_E_mergeAssignment
/-- [The expectation of a real-valued function under independent edge draws equals
the iterated expectation obtained by drawing the assigned coordinates first,
then drawing the free coordinates independently with the same bias and merging
the two assignments](goal). -/
lemma biasedLaw_E_mergeAssignment (p : ℝ) (B : Finset (Fin n))
    (g : (Edge n r → Bool) → ℝ) :
    (biasedLaw (Edge n r) p).E g =
      (biasedLaw (AssignedCoord (r := r) B) p).E (fun y =>
        (biasedLaw (FreeCoord (r := r) B) p).E (fun z => g (mergeAssignment B z y))) := by
  classical
  let q := Equiv.piEquivPiSubtypeProd (fun e : Edge n r => e ∈ freeEdges B) (fun _ => Bool)
  have hmass (x : Edge n r → Bool) :
      (biasedLaw (Edge n r) p).p x =
        (biasedLaw (FreeCoord (r := r) B) p).p (q x).1 *
        (biasedLaw (AssignedCoord (r := r) B) p).p (q x).2 := by
    simp only [biasedLaw, bernoulliDesign, prodDesign_p]
    convert (Fintype.prod_subtype_mul_prod_subtype
      (fun e : Edge n r => e ∈ freeEdges B)
      (fun e => (coinDesign (max 0 (min p 1)) (le_max_left _ _)
        (max_le zero_le_one (min_le_right _ _))).p (x e))).symm using 1
    congr 2
    ext e
    simp
  have hmerge (v : (FreeCoord (r := r) B → Bool) × (AssignedCoord (r := r) B → Bool)) :
      q.symm v = mergeAssignment B v.1 v.2 := rfl
  unfold FiniteDesign.E
  simp_rw [hmass]
  calc
    _ = ∑ v : (FreeCoord (r := r) B → Bool) × (AssignedCoord (r := r) B → Bool),
        (biasedLaw (FreeCoord (r := r) B) p).p v.1 *
        (biasedLaw (AssignedCoord (r := r) B) p).p v.2 * g (q.symm v) := by
      simpa only [Equiv.symm_apply_apply] using
        (Equiv.sum_comp q (fun v =>
          (biasedLaw (FreeCoord (r := r) B) p).p v.1 *
          (biasedLaw (AssignedCoord (r := r) B) p).p v.2 * g (q.symm v)))
    _ = _ := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp_rw [hmerge, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro z _
      ring

/-- For [a block](hyp:B) among [n vertices](hyp:n) with [r vertices per edge](hyp:r),
the [joined Fourier support](goal) is the union of [a set of free edges](hyp:A)
and [a set of assigned edges](hyp:D), viewed as edges of the original hypergraph. -/
def joinedSupport (B : Finset (Fin n)) (A : Finset (FreeCoord (r := r) B))
    (D : Finset (AssignedCoord (r := r) B)) : Finset (Edge n r) := -- @realizes D(paper range)
  A.image Subtype.val ∪ D.image Subtype.val

-- @node: fourierChar_joinedSupport_merge
/-- [The Fourier character on a joined free and assigned support, evaluated at
the merged configuration, equals the product of the free-support character
and the assigned-support character evaluated on their respective assignments](goal). -/
lemma fourierChar_joinedSupport_merge (p : ℝ) (B : Finset (Fin n))
    (A : Finset (FreeCoord (r := r) B)) (D : Finset (AssignedCoord (r := r) B))
    (z : FreeCoord (r := r) B → Bool) (y : AssignedCoord (r := r) B → Bool) :
    fourierChar p (joinedSupport B A D) (mergeAssignment B z y) =
      fourierChar p A z * fourierChar p D y := by
  classical
  have hd : Disjoint (A.image Subtype.val) (D.image Subtype.val) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨d, _, heq⟩ := Finset.mem_image.mp hf
    exact d.property (heq.symm ▸ a.property)
  unfold fourierChar joinedSupport
  rw [Finset.prod_union hd, Finset.prod_image, Finset.prod_image]
  · congr 1
    · apply Finset.prod_congr rfl
      intro e _
      simp [coordChar, mergeAssignment, e.property]
    · apply Finset.prod_congr rfl
      intro e _
      simp [coordChar, mergeAssignment, e.property]
  · intro a _ b _ hab
    exact Subtype.ext hab
  · intro a _ b _ hab
    exact Subtype.ext hab

-- @node: restricted_fourierCoeffR_assigned
/-- [Taking the Fourier coefficient over outside assignments of a restricted
function's free-support Fourier coefficient gives the original hypergraph
function's Fourier coefficient on the joined free and assigned support](goal). -/
lemma restricted_fourierCoeffR_assigned (p : ℝ) (f : (Edge n r → Bool) → Bool)
    (B : Finset (Fin n)) (A : Finset (FreeCoord (r := r) B))
    (D : Finset (AssignedCoord (r := r) B)) :
    fourierCoeffR p (fun y => fourierCoeff p (restrictedFunction f B y) A) D =
      hyperFourierCoeff p f (joinedSupport B A D) := by
  simp only [hyperFourierCoeff, fourierCoeff, fourierCoeffR]
  rw [biasedLaw_E_mergeAssignment p B]
  apply FiniteDesign.E_congr
  intro y
  rw [← FiniteDesign.E_mul_const]
  apply FiniteDesign.E_congr
  intro z
  rw [fourierChar_joinedSupport_merge]
  exact mul_assoc (boolValue f (mergeAssignment B z y)) _ _

/-- If [the bias lies strictly between zero and one](hyp:hp) and
[the hypergraph function is invariant under vertex relabeling](hyp:hf),
[its restricted Fourier coefficient on a free support equals the sum over all
assigned supports of the original coefficient on the joined support times
the assigned-support character of the outside assignment](goal). -/
lemma restricted_fourierCoeff_expansion (p : ℝ) (hp : BiasInterior p)
    (f : (Edge n r → Bool) → Bool) (hf : IsHypergraphProperty f)
    (B : Finset (Fin n)) (y : AssignedCoord (r := r) B → Bool)
    (A : Finset (FreeCoord (r := r) B)) : -- @realizes A(subset of the free coordinates)
    fourierCoeff p (restrictedFunction f B y) A =
      ∑ D : Finset (AssignedCoord (r := r) B),
        hyperFourierCoeff p f (joinedSupport B A D) * fourierChar p D y := by
  rw [fourier_expansion p hp
    (fun y => fourierCoeff p (restrictedFunction f B y) A) y]
  simp_rw [restricted_fourierCoeffR_assigned]

/-- If [the bias lies strictly between zero and one](hyp:hp) and
[the hypergraph function is invariant under vertex relabeling](hyp:hf),
[the mean squared restricted Fourier coefficient on a fixed free support,
averaged over independent outside assignments, equals the sum of squared
original coefficients over all assigned supports joined to that free support](goal). -/
lemma averaged_restricted_fourierCoeff_sq (p : ℝ) (hp : BiasInterior p)
    (f : (Edge n r → Bool) → Bool) (hf : IsHypergraphProperty f)
    (B : Finset (Fin n)) (A : Finset (FreeCoord (r := r) B)) :
    (biasedLaw (AssignedCoord (r := r) B) p).E
      (fun y => fourierCoeff p (restrictedFunction f B y) A ^ 2) =
        ∑ D : Finset (AssignedCoord (r := r) B),
          hyperFourierCoeff p f (joinedSupport B A D) ^ 2 := by
  classical
  simp_rw [restricted_fourierCoeff_expansion p hp f hf B]
  simp_rw [pow_two, Fintype.sum_mul_sum]
  rw [FiniteDesign.E_sum]
  apply Finset.sum_congr rfl
  intro D _
  rw [FiniteDesign.E_sum]
  have hterm (D' : Finset (AssignedCoord (r := r) B)) :
      (biasedLaw (AssignedCoord (r := r) B) p).E (fun y =>
        (hyperFourierCoeff p f (joinedSupport B A D) * fourierChar p D y) *
        (hyperFourierCoeff p f (joinedSupport B A D') * fourierChar p D' y)) =
      hyperFourierCoeff p f (joinedSupport B A D) *
        hyperFourierCoeff p f (joinedSupport B A D') * (if D = D' then 1 else 0) := by
    calc
      _ = (biasedLaw (AssignedCoord (r := r) B) p).E (fun y =>
          (hyperFourierCoeff p f (joinedSupport B A D) *
            hyperFourierCoeff p f (joinedSupport B A D')) *
            (fourierChar p D y * fourierChar p D' y)) := by
        apply FiniteDesign.E_congr
        intro y
        ring
      _ = _ := by rw [FiniteDesign.E_const_mul, fourierChar_orthonormal p hp]
  simp_rw [hterm]
  simp


-- @node: mergeAssignment_replaceCoord
/-- [Replacing one free edge value before merging with the assigned values gives
the same configuration as merging first and then replacing that edge value](goal). -/
lemma mergeAssignment_replaceCoord (B : Finset (Fin n))
    (z : FreeCoord (r := r) B → Bool) (y : AssignedCoord (r := r) B → Bool)
    (e : FreeCoord (r := r) B) (b : Bool) :
    mergeAssignment B (replaceCoord z e b) y =
      replaceCoord (mergeAssignment B z y) e.val b := by
  classical
  funext a
  by_cases hae : a = e.val
  · subst a
    simp [mergeAssignment, replaceCoord, e.property]
  · by_cases ha : a ∈ freeEdges B
    · have hne : (⟨a, ha⟩ : FreeCoord (r := r) B) ≠ e :=
        fun h => hae (congrArg Subtype.val h)
      simp [mergeAssignment, replaceCoord, ha, hae, hne]
    · simp [mergeAssignment, replaceCoord, ha, hae]

/-- If [the bias lies strictly between zero and one](hyp:hp) and
[the hypergraph function is invariant under vertex relabeling](hyp:hf),
[the influence of a free edge in the restricted function, averaged over
independent outside assignments, equals its influence in the original function](goal). -/
lemma averaged_restricted_influence (p : ℝ) (hp : BiasInterior p)
    (f : (Edge n r → Bool) → Bool) (hf : IsHypergraphProperty f)
    (B : Finset (Fin n)) (e : FreeCoord (r := r) B) :
    (biasedLaw (AssignedCoord (r := r) B) p).E
      (fun y => coordInfluence p (restrictedFunction f B y) e) = edgeInfluence p f e.val := by
  classical
  unfold edgeInfluence coordInfluence FiniteDesign.Pr
  rw [biasedLaw_E_mergeAssignment p B]
  apply FiniteDesign.E_congr
  intro y
  apply FiniteDesign.E_congr
  intro z
  simp only [FiniteDesign.ind, restrictedFunction, mergeAssignment_replaceCoord]


-- @node: edge_meets_block_probability_le
/-- If [the block size m does not exceed the number n of vertices](hyp:hmn),
[the probability that a fixed r-vertex edge meets a uniformly chosen m-vertex
block is at most r times m divided by n](goal). -/
lemma edge_meets_block_probability_le (n r m : ℕ) (hmn : m ≤ n) (e : Edge n r) :
    (blockLaw n m hmn).Pr (fun B => e ∈ freeEdges B.val) ≤ (r : ℝ) * m / n := by
  classical
  let D := blockLaw n m hmn
  have hpoint (B : {B : Finset (Fin n) // B.card = m}) :
      FiniteDesign.ind (fun B => e ∈ freeEdges B.val) B ≤
        ∑ v ∈ e.val, FiniteDesign.ind (fun B => v ∈ B.val) B := by
    by_cases he : e ∈ freeEdges B.val
    · obtain ⟨v, hv⟩ := (Finset.mem_filter.mp he).2
      have hv' := Finset.mem_inter.mp hv
      calc
        _ = 1 := by simp [FiniteDesign.ind, he]
        _ = FiniteDesign.ind (fun B => v ∈ B.val) B := by
          simp [FiniteDesign.ind, hv'.2]
        _ ≤ _ := Finset.single_le_sum
          (f := fun v => FiniteDesign.ind (fun B => v ∈ B.val) B)
          (fun _ _ => FiniteDesign.ind_nonneg _ _) hv'.1
    · simp only [FiniteDesign.ind, he, if_false]
      exact Finset.sum_nonneg (fun _ _ => FiniteDesign.ind_nonneg _ _)
  have hE : D.Pr (fun B => e ∈ freeEdges B.val) ≤
      ∑ v ∈ e.val, D.Pr (fun B => v ∈ B.val) := by
    unfold FiniteDesign.Pr
    rw [← D.E_sum]
    exact Finset.sum_le_sum (fun B _ =>
      mul_le_mul_of_nonneg_left (hpoint B) (D.p_nonneg B))
  have hfirst (v : Fin n) : D.Pr (fun B => v ∈ B.val) = (m : ℝ) / n := by
    simpa [D, blockLaw] using
      Causalean.Experimentation.DesignBased.completeRandomization_incl m
        (by simpa using hmn) v
  simp_rw [hfirst] at hE
  simpa only [Finset.sum_const, nsmul_eq_mul, e.property, mul_div_assoc] using hE

-- @node: averaged_free_totalInfluence_le
/-- If [the block size m does not exceed the number n of vertices](hyp:hmn),
[the bias lies strictly between zero and one](hyp:hp), and
[the hypergraph function is invariant under vertex relabeling](hyp:hf),
[the expected sum of influences of edges meeting a uniformly chosen m-vertex
block is at most r times m divided by n times the total edge influence](goal). -/
lemma averaged_free_totalInfluence_le (n r m : ℕ) (hmn : m ≤ n) (p : ℝ)
    (hp : BiasInterior p) (f : (Edge n r → Bool) → Bool) (hf : IsHypergraphProperty f) :
    (blockLaw n m hmn).E (fun B => ∑ e ∈ freeEdges B.val, edgeInfluence p f e) ≤
      ((r : ℝ) * m / n) * totalEdgeInfluence p f := by
  classical
  let D := blockLaw n m hmn
  have hsum (B : {B : Finset (Fin n) // B.card = m}) :
      (∑ e ∈ freeEdges B.val, edgeInfluence p f e) =
        ∑ e : Edge n r,
          FiniteDesign.ind (fun B => e ∈ freeEdges B.val) B * edgeInfluence p f e := by
    simp [freeEdges, Finset.sum_filter, FiniteDesign.ind]
  calc
    _ = D.E (fun B => ∑ e : Edge n r,
        FiniteDesign.ind (fun B => e ∈ freeEdges B.val) B * edgeInfluence p f e) :=
      D.E_congr hsum
    _ = ∑ e : Edge n r, D.Pr (fun B => e ∈ freeEdges B.val) * edgeInfluence p f e := by
      rw [D.E_sum]
      apply Finset.sum_congr rfl
      intro e _
      exact D.E_mul_const _ _
    _ ≤ ∑ e : Edge n r, ((r : ℝ) * m / n) * edgeInfluence p f e := by
      apply Finset.sum_le_sum
      intro e _
      exact mul_le_mul_of_nonneg_right (edge_meets_block_probability_le n r m hmn e)
        ((biasedLaw (Edge n r) p).Pr_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]

end Papers.OaiUniformInfluenceHypergraph
