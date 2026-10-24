module

public import Papers.OaiPairedStatesHamiltonian.Helpers.Density
public import Mathlib.Combinatorics.Hall.Basic

/-! Existence of pairs from the incidence-flow inequality. -/

public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
open Classical
attribute [local instance] propDecidable


-- @node: regular_incidence_matching
/-- If [the common incidence degree is positive](hyp:hk), [the two finite shores
have equal size](hyp:hcard), [each element on the first shore has the common
degree](hyp:hrow), and [each element on the second shore has the common
degree](hyp:hcol), then [there is a
bijection between the shores using only pairs in the incidence set](goal). -/
lemma regular_incidence_matching {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (E : Finset (α × β)) (k : ℕ) (hk : 0 < k)
    (hcard : Fintype.card α = Fintype.card β)
    (hrow : ∀ a, (E.filter (fun i => i.1 = a)).card = k)
    (hcol : ∀ b, (E.filter (fun i => i.2 = b)).card = k) :
    ∃ f : α → β, Function.Bijective f ∧ ∀ a, (a, f a) ∈ E := by
  classical
  have hall (A : Finset α) :
      A.card ≤ (Finset.univ.filter (fun b => ∃ a ∈ A, (a, b) ∈ E)).card := by
    let N := Finset.univ.filter (fun b => ∃ a ∈ A, (a, b) ∈ E)
    let EA := E.filter (fun i => i.1 ∈ A)
    have hleft : EA.card = A.card * k := by
      have h := Finset.sum_card_fiberwise_eq_card_filter E A Prod.fst
      simpa only [hrow, Finset.sum_const, smul_eq_mul] using h.symm
    have hright : EA.card ≤ N.card * k := by
      have hsum : EA.card = ∑ b ∈ N, (EA.filter (fun i => i.2 = b)).card := by
        apply Finset.card_eq_sum_card_fiberwise
        intro i hi
        obtain ⟨hiE, hiA⟩ := Finset.mem_filter.mp hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.1, hiA, hiE⟩
      rw [hsum]
      calc
        _ ≤ ∑ b ∈ N, k := by
          apply Finset.sum_le_sum
          intro b hb
          rw [← hcol b]
          apply Finset.card_le_card
          intro i hi
          obtain ⟨hiA, hib⟩ := Finset.mem_filter.mp hi
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hiA).1, hib⟩
        _ = N.card * k := by simp
    exact (mul_le_mul_iff_left₀ hk).mp (hleft ▸ hright)
  obtain ⟨f, hf, hE⟩ :=
    (Fintype.all_card_le_filter_rel_iff_exists_injective (fun a b => (a, b) ∈ E)).mp hall
  exact ⟨f, (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩, hE⟩

-- @node: residual_incidence_degrees
/-- If [the matching function is bijective](hyp:hf), [all its matched pairs belong
to the incidence set](hyp:hE), [every row has degree k](hyp:hrow), and [every
column has degree k](hyp:hcol), then [removing its matched pairs leaves every row and column with
degree k minus one, with subtraction truncated at zero](goal). -/
lemma residual_incidence_degrees {α β : Type} [DecidableEq α] [DecidableEq β]
    (E : Finset (α × β)) (k : ℕ) (f : α → β) (hf : Function.Bijective f)
    (hE : ∀ a, (a, f a) ∈ E)
    (hrow : ∀ a, (E.filter (fun i => i.1 = a)).card = k)
    (hcol : ∀ b, (E.filter (fun i => i.2 = b)).card = k) :
    let E' := E.filter (fun i => i.2 ≠ f i.1)
    (∀ a, (E'.filter (fun i => i.1 = a)).card = k - 1) ∧
    (∀ b, (E'.filter (fun i => i.2 = b)).card = k - 1) := by
  classical
  dsimp only
  constructor
  · intro a
    have heq : (E.filter (fun i => i.2 ≠ f i.1)).filter (fun i => i.1 = a) =
        (E.filter (fun i => i.1 = a)).erase (a, f a) := by
      ext ⟨x, y⟩
      by_cases hx : x = a
      · subst x
        simp [Finset.mem_filter, and_comm]
      · simp [Finset.mem_filter, hx]
    rw [heq, Finset.card_erase_of_mem, hrow]
    exact Finset.mem_filter.mpr ⟨hE a, rfl⟩
  · intro b
    obtain ⟨a, rfl⟩ := hf.surjective b
    have heq : (E.filter (fun i => i.2 ≠ f i.1)).filter (fun i => i.2 = f a) =
        (E.filter (fun i => i.2 = f a)).erase (a, f a) := by
      ext ⟨x, y⟩
      by_cases hy : y = f a
      · subst y
        simp [Finset.mem_filter, hf.injective.eq_iff, eq_comm, and_comm]
      · simp [Finset.mem_filter, hy]
    rw [heq, Finset.card_erase_of_mem, hcol]
    exact Finset.mem_filter.mpr ⟨hE a, rfl⟩

-- @node: prop:pairs
/-- If [the map is a sphere triangulation](hyp:hT), [its face coloring is a
partition coloring](hyp:hcol), [it has no separating triangle](hyp:hsep), and
[every graph on a single vertex is an edgeless tree](hyp:hpin), then [there exist
two states relative to the chosen outer face that assign different vertices to
each black nonouter face](goal). -/
lemma exists_pair_of_noSeparatingTriangle (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col)
    (hsep : PairsNoSeparatingTriangle T) (hpin : SingletonTreeEdgeless) (t0 : T.Face) :
    ∃ r s : State T col t0, IsPair T col t0 r s := by
  obtain ⟨E, hinc, hrow, hcolE⟩ := exists_degreeTwo_incidence T hT col hcol t0 hsep
  have hcard : Fintype.card (blackNonOuter T col t0) = Fintype.card (nonRoot T t0) := by
    have hc := stateSetsCard_of_triangulation T hT col hcol t0
    simpa only [Fintype.card_coe] using hc.1.trans hc.2.symm
  obtain ⟨f, hf, hfE⟩ := regular_incidence_matching E 2 (by omega) hcard hrow hcolE
  have hres := residual_incidence_degrees E 2 f hf hfE hrow hcolE
  obtain ⟨g, hg, hgE⟩ := regular_incidence_matching
    (E.filter (fun i => i.2 ≠ f i.1)) 1 (by omega) hcard hres.1 hres.2
  let r : State T col t0 := ⟨f, ⟨hf, fun t => hinc (t, f t) (hfE t)⟩⟩
  let s : State T col t0 :=
    ⟨g, ⟨hg, fun t => hinc (t, g t) (Finset.mem_filter.mp (hgE t)).1⟩⟩
  refine ⟨r, s, ⟨?_⟩⟩
  intro t
  exact Ne.symm (Finset.mem_filter.mp (hgE t)).2


end OaiPairedStatesHamiltonian
