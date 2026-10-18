module
public import Papers.TbsNeuralCausalPi.Helpers.AntipodalGeometry
public import Mathlib.Data.ZMod.Basic
/-! # Mod-two facet incidence on the signed sphere

Facets are complete choices of one sign in every coordinate. Removing one
vertex gives a ridge, with exactly two containing facets. Thus the sum of all
facets has zero boundary over `ZMod 2` at every such ridge.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi.Antipodal
open Finset

-- @node: signedFacet
/-- For [a choice of one sign in each coordinate](hyp:σ), the [signed facet](goal)
is the set containing the chosen signed vertex at every coordinate. -/
def signedFacet {n : ℕ} (σ : Fin n → Bool) : Finset (SignedVertex n) :=
  univ.image (fun i => (i, σ i))

-- @node: mem_signedFacet
/-- [A signed vertex belongs to the facet of a sign choice exactly when its sign
equals the chosen sign at its coordinate](goal). -/
@[simp] lemma mem_signedFacet {n : ℕ} (σ : Fin n → Bool) (v : SignedVertex n) :
    v ∈ signedFacet σ ↔ v.2 = σ v.1 := by
  rcases v with ⟨i, b⟩
  simp [signedFacet, Prod.mk.injEq, eq_comm]

-- @node: signedFacet_noOpposite
/-- [A signed facet contains no pair of opposite vertices](goal). -/
lemma signedFacet_noOpposite {n : ℕ} (σ : Fin n → Bool) : NoOpposite (signedFacet σ) := by
  intro v hv hneg
  have hv' := (mem_signedFacet σ v).mp hv
  have hn := (mem_signedFacet σ (signedAntipode v)).mp hneg
  simp only [signedAntipode] at hn
  rw [hv'] at hn
  cases h : σ v.1 <;> simp [h] at hn

-- @node: signedFacet_card
/-- [A signed facet in n coordinates has exactly n vertices](goal). -/
lemma signedFacet_card {n : ℕ} (σ : Fin n → Bool) : (signedFacet σ).card = n := by
  rw [signedFacet, card_image_of_injective]
  · simp
  · intro i j h
    exact congrArg Prod.fst h

-- @node: signedFacet_injective
/-- [Two sign choices that give the same signed facet must be equal](goal). -/
lemma signedFacet_injective {n : ℕ} : Function.Injective (signedFacet (n := n)) := by
  intro σ τ h
  funext i
  have hm : (i, σ i) ∈ signedFacet τ := h ▸ (mem_signedFacet σ (i, σ i)).mpr rfl
  exact (mem_signedFacet τ _).mp hm

-- @node: signedRidge
/-- For [a sign choice](hyp:σ) and [a coordinate to remove](hyp:i), the
[signed ridge](goal) is the facet with its chosen vertex at that coordinate deleted. -/
def signedRidge {n : ℕ} (σ : Fin n → Bool) (i : Fin n) : Finset (SignedVertex n) :=
  (signedFacet σ).erase (i, σ i)

-- @node: mem_signedRidge
/-- [A vertex belongs to the ridge obtained by deleting a coordinate exactly when
it lies at a different coordinate and has the sign prescribed by the sign choice](goal). -/
@[simp] lemma mem_signedRidge {n : ℕ} (σ : Fin n → Bool) (i : Fin n)
    (v : SignedVertex n) : v ∈ signedRidge σ i ↔ v.1 ≠ i ∧ v.2 = σ v.1 := by
  rcases v with ⟨j, b⟩
  simp only [signedRidge, mem_erase, mem_signedFacet]
  constructor
  · rintro ⟨hne, rfl⟩
    exact ⟨fun h => hne (by simp [h]), rfl⟩
  · rintro ⟨hne, hb⟩
    exact ⟨fun h => hne (congrArg Prod.fst h), hb⟩

-- @node: signedRidge_card
/-- [A signed ridge in n coordinates has n minus one vertices](goal). -/
lemma signedRidge_card {n : ℕ} (σ : Fin n → Bool) (i : Fin n) :
    (signedRidge σ i).card = n - 1 := by
  rw [signedRidge, card_erase_of_mem ((mem_signedFacet σ _).mpr rfl), signedFacet_card]

-- @node: signedRidge_subset_facet_iff
/-- [A ridge from one sign choice lies in the facet of another exactly when
the two choices agree at every coordinate except possibly the deleted one](goal). -/
lemma signedRidge_subset_facet_iff {n : ℕ} (σ τ : Fin n → Bool) (i : Fin n) :
    signedRidge σ i ⊆ signedFacet τ ↔ ∀ j, j ≠ i → τ j = σ j := by
  constructor
  · intro h j hj
    exact ((mem_signedFacet τ _).mp (h ((mem_signedRidge σ i (j, σ j)).mpr ⟨hj, rfl⟩))).symm
  · intro h v hv
    obtain ⟨hi, hv⟩ := (mem_signedRidge σ i v).mp hv
    exact (mem_signedFacet τ v).mpr (hv.trans (h v.1 hi).symm)

-- @node: flipSignAt
/-- Given [a sign choice](hyp:σ) and [a coordinate](hyp:i), the
[modified sign choice](goal) reverses the sign at that coordinate and retains all others. -/
def flipSignAt {n : ℕ} (σ : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  Function.update σ i (!σ i)

-- @node: flipSignAt_ne
/-- [Reversing the sign at one coordinate changes the sign choice](goal). -/
lemma flipSignAt_ne {n : ℕ} (σ : Fin n → Bool) (i : Fin n) : flipSignAt σ i ≠ σ := by
  intro h
  have he := congrFun h i
  simp only [flipSignAt, Function.update_self] at he
  cases hσ : σ i <;> simp [hσ] at he

-- @node: signedRidge_two_facets
/-- [A facet contains a given signed ridge exactly when its sign choice is either
the original choice or that choice with the deleted coordinate's sign reversed](goal). -/
lemma signedRidge_two_facets {n : ℕ} (σ τ : Fin n → Bool) (i : Fin n) :
    signedRidge σ i ⊆ signedFacet τ ↔ τ = σ ∨ τ = flipSignAt σ i := by
  rw [signedRidge_subset_facet_iff]
  constructor
  · intro h
    by_cases hi : τ i = σ i
    · left
      funext j
      by_cases hj : j = i
      · simpa [hj] using hi
      · exact h j hj
    · right
      have hi' : τ i = !σ i := by cases hτ : τ i <;> cases hσ : σ i <;> simp_all
      funext j
      by_cases hj : j = i
      · subst j
        simpa [flipSignAt] using hi'
      · simpa [flipSignAt, hj] using h j hj
  · rintro (rfl | rfl) j hj
    · rfl
    · simp [flipSignAt, hj]

-- @node: signedRidge_containing_facets
/-- [The set of sign choices whose facets contain a signed ridge consists of
the original choice and the choice with the deleted coordinate's sign reversed](goal). -/
lemma signedRidge_containing_facets {n : ℕ} (σ : Fin n → Bool) (i : Fin n) :
    univ.filter (fun τ => signedRidge σ i ⊆ signedFacet τ) = {σ, flipSignAt σ i} := by
  ext τ
  simp only [mem_filter, mem_univ, true_and, signedRidge_two_facets, mem_insert,
    mem_singleton]

-- @node: signedRidge_incidence_card
/-- [Exactly two sign choices have facets containing a given signed ridge](goal). -/
lemma signedRidge_incidence_card {n : ℕ} (σ : Fin n → Bool) (i : Fin n) :
    (univ.filter (fun τ => signedRidge σ i ⊆ signedFacet τ)).card = 2 := by
  rw [signedRidge_containing_facets, card_pair (Ne.symm (flipSignAt_ne σ i))]

-- @node: signedRidge_boundary_modTwo
/-- [The number of facets containing a signed ridge is zero modulo two](goal). -/
lemma signedRidge_boundary_modTwo {n : ℕ} (σ : Fin n → Bool) (i : Fin n) :
    (∑ τ : Fin n → Bool, if signedRidge σ i ⊆ signedFacet τ then (1 : ZMod 2) else 0) = 0 := by
  classical
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, signedRidge_incidence_card]
  simpa only [nsmul_eq_mul, mul_one] using ZMod.natCast_self 2


-- @node: noOpposite_subset_signedFacet
/-- If [a finite set of signed vertices contains no opposite pair](hyp:hs),
[it is contained in the facet of some complete sign choice](goal). -/
lemma noOpposite_subset_signedFacet {n : ℕ} {s : Finset (SignedVertex n)}
    (hs : NoOpposite s) : ∃ σ : Fin n → Bool, s ⊆ signedFacet σ := by
  classical
  let σ : Fin n → Bool := fun i => decide ((i, true) ∈ s)
  refine ⟨σ, ?_⟩
  rintro ⟨i, b⟩ hv
  apply (mem_signedFacet σ _).mpr
  cases b
  · have hn : (i, true) ∉ s := by
      simpa [signedAntipode] using hs (i, false) hv
    simp [σ, hn]
  · simp [σ, hv]

-- @node: noOpposite_top_face_iff
/-- [A finite set of signed vertices contains no opposite pair and has exactly
n vertices if and only if it is the facet of a complete sign choice in n coordinates](goal). -/
lemma noOpposite_top_face_iff {n : ℕ} {s : Finset (SignedVertex n)} :
    NoOpposite s ∧ s.card = n ↔ ∃ σ : Fin n → Bool, s = signedFacet σ := by
  constructor
  · rintro ⟨hs, hc⟩
    obtain ⟨σ, hσ⟩ := noOpposite_subset_signedFacet hs
    exact ⟨σ, eq_of_subset_of_card_le hσ (by rw [signedFacet_card, hc])⟩
  · rintro ⟨σ, rfl⟩
    exact ⟨signedFacet_noOpposite σ, signedFacet_card σ⟩

-- @node: noOpposite_ridge_representation
/-- If [the number of coordinates is positive](hyp:hn), [a finite set of signed
vertices contains no opposite pair](hyp:hs), and [it has n minus one vertices](hyp:hc),
then [it is obtained from some signed facet by deleting one coordinate's vertex](goal). -/
lemma noOpposite_ridge_representation {n : ℕ} (hn : 0 < n)
    {s : Finset (SignedVertex n)} (hs : NoOpposite s) (hc : s.card = n - 1) :
    ∃ σ : Fin n → Bool, ∃ i : Fin n, s = signedRidge σ i := by
  obtain ⟨σ, hσ⟩ := noOpposite_subset_signedFacet hs
  have hlt : s.card < (signedFacet σ).card := by rw [hc, signedFacet_card]; omega
  obtain ⟨⟨i, b⟩, hv, hnot⟩ := exists_mem_notMem_of_card_lt_card hlt
  have hb : b = σ i := (mem_signedFacet σ _).mp hv
  subst b
  refine ⟨σ, i, eq_of_subset_of_card_le ?_ ?_⟩
  · intro v hv
    apply mem_erase.mpr
    exact ⟨fun he => hnot (he ▸ hv), hσ hv⟩
  · rw [signedRidge_card, hc]

-- @node: noOpposite_ridge_incidence_card
/-- If [the number of coordinates is positive](hyp:hn), [a finite set of signed
vertices contains no opposite pair](hyp:hs), and [it has n minus one vertices](hyp:hc),
then [exactly two sign choices have facets containing it](goal). -/
lemma noOpposite_ridge_incidence_card {n : ℕ} (hn : 0 < n)
    {s : Finset (SignedVertex n)} (hs : NoOpposite s) (hc : s.card = n - 1) :
    (univ.filter (fun σ : Fin n → Bool => s ⊆ signedFacet σ)).card = 2 := by
  obtain ⟨σ, i, rfl⟩ := noOpposite_ridge_representation hn hs hc
  exact signedRidge_incidence_card σ i

-- @node: signedSphere_fundamental_boundary_modTwo
/-- If [the number of coordinates is positive](hyp:hn), [a finite set of signed
vertices contains no opposite pair](hyp:hs), and [it has n minus one vertices](hyp:hc),
then [the number of facets containing it is zero modulo two](goal).

This is the incidence step only; it does not assert the odd zero count for a PL map. -/
lemma signedSphere_fundamental_boundary_modTwo {n : ℕ} (hn : 0 < n)
    {s : Finset (SignedVertex n)} (hs : NoOpposite s) (hc : s.card = n - 1) :
    (∑ σ : Fin n → Bool, if s ⊆ signedFacet σ then (1 : ZMod 2) else 0) = 0 := by
  obtain ⟨σ, i, rfl⟩ := noOpposite_ridge_representation hn hs hc
  exact signedRidge_boundary_modTwo σ i


-- @node: signedRidge_weighted_incidence
/-- [The sum modulo two of the weights of all facets containing a signed ridge
equals the weight of the original facet plus that of the facet obtained by reversing
the sign at the deleted coordinate](goal). -/
lemma signedRidge_weighted_incidence {n : ℕ} (σ : Fin n → Bool) (i : Fin n)
    (w : (Fin n → Bool) → ZMod 2) :
    (∑ τ, if signedRidge σ i ⊆ signedFacet τ then w τ else 0) =
      w σ + w (flipSignAt σ i) := by
  classical
  rw [← Finset.sum_filter, signedRidge_containing_facets,
    Finset.sum_pair (Ne.symm (flipSignAt_ne σ i))]

-- @node: signedHemisphere_boundary_modTwo
/-- [The number modulo two of facets containing a given signed ridge and having
positive sign at a designated coordinate is one when that coordinate is the deleted
coordinate of the ridge, and zero otherwise](goal). -/
lemma signedHemisphere_boundary_modTwo {n : ℕ} (σ : Fin n → Bool) (i j : Fin n) :
    (∑ τ : Fin n → Bool, if signedRidge σ i ⊆ signedFacet τ then
      (if τ j then (1 : ZMod 2) else 0) else 0) = if i = j then 1 else 0 := by
  rw [signedRidge_weighted_incidence]
  have htwo : (1 : ZMod 2) + 1 = 0 := ZMod.natCast_self 2
  by_cases hij : i = j
  · subst j
    cases hσ : σ i <;> simp [flipSignAt, hσ]
  · have hji : j ≠ i := Ne.symm hij
    cases hσ : σ j <;> simp [flipSignAt, hji, hij, hσ, htwo]

-- @node: signedFacet_antipode
/-- [Taking the opposite of every vertex in a signed facet gives the facet
whose sign choice reverses every original sign](goal). -/
lemma signedFacet_antipode {n : ℕ} (σ : Fin n → Bool) :
    (signedFacet σ).image signedAntipode = signedFacet (fun i => !σ i) := by
  ext v
  simp only [mem_image, mem_signedFacet]
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa [signedAntipode] using congrArg Bool.not hu
  · intro hv
    refine ⟨signedAntipode v, ?_, signedAntipode_involutive v⟩
    simp [signedAntipode, hv]

-- @node: signedFacet_ne_antipode
/-- If [there is at least one coordinate](hyp:hn), then [a signed facet differs
from the facet obtained by reversing all its signs](goal). -/
lemma signedFacet_ne_antipode {n : ℕ} (hn : 0 < n) (σ : Fin n → Bool) :
    signedFacet σ ≠ signedFacet (fun i => !σ i) := by
  intro h
  have he := congrFun (signedFacet_injective h) ⟨0, hn⟩
  cases hσ : σ ⟨0, hn⟩ <;> simp [hσ] at he

end Papers.TbsNeuralCausalPi.Antipodal
