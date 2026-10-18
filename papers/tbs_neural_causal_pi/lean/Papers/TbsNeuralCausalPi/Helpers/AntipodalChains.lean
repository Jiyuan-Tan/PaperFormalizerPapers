module
public import Papers.TbsNeuralCausalPi.Helpers.AntipodalIncidence
/-! # Rigidity of top-dimensional mod-two signed-sphere chains

The ridge boundary determines a facet chain up to the fundamental cycle.
In particular a chain selecting one facet from each antipodal pair cannot
be a cycle. These are finite chain facts, not the subdivision or homotopy
invariance needed for the PL zero-count theorem.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi.Antipodal
open Finset

/-- For [top-dimensional facet weights modulo two](hyp:w),
[a facet specified by its coordinate signs](hyp:σ), and [a coordinate to omit from that facet](hyp:i),
the [boundary coefficient at the resulting ridge](goal) is the sum of the weights of all facets containing that ridge.

In ambient dimension one, the empty ridge gives the augmented boundary. -/
-- @node: signedTopBoundary
def signedTopBoundary {n : ℕ} (w : (Fin n → Bool) → ZMod 2)
    (σ : Fin n → Bool) (i : Fin n) : ZMod 2 :=
  ∑ τ, if signedRidge σ i ⊆ signedFacet τ then w τ else 0

-- @node: signedTopBoundary_eq
/-- [The boundary coefficient of any top-dimensional chain modulo two at a ridge equals the sum of the weights of its two incident facets, whose signs differ only in the omitted coordinate](goal). -/
lemma signedTopBoundary_eq {n : ℕ} (w : (Fin n → Bool) → ZMod 2)
    (σ : Fin n → Bool) (i : Fin n) :
    signedTopBoundary w σ i = w σ + w (flipSignAt σ i) :=
  signedRidge_weighted_incidence σ i w

-- @node: signedTopBoundary_add
/-- [At every ridge, the boundary coefficient of the sum of two facet chains modulo two equals the sum of their boundary coefficients](goal). -/
lemma signedTopBoundary_add {n : ℕ} (w v : (Fin n → Bool) → ZMod 2)
    (σ : Fin n → Bool) (i : Fin n) :
    signedTopBoundary (fun τ => w τ + v τ) σ i =
      signedTopBoundary w σ i + signedTopBoundary v σ i := by
  simp only [signedTopBoundary_eq]
  ring

/-- If [a function on sign configurations is unchanged whenever a single coordinate sign is flipped](hyp:hw),
[it takes the same value on every pair of sign configurations](goal).

The values may lie in any type; no algebraic structure is required. -/
-- @node: flipSignAt_invariant_constant
lemma flipSignAt_invariant_constant {n : ℕ} {R : Type*}
    (w : (Fin n → Bool) → R)
    (hw : ∀ σ i, w (flipSignAt σ i) = w σ) : ∀ σ τ, w σ = w τ := by
  classical
  have aux : ∀ s : Finset (Fin n), ∀ σ τ : Fin n → Bool,
      (∀ i, i ∉ s → σ i = τ i) → w σ = w τ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro σ τ h
        have he : σ = τ := funext (fun i => h i (notMem_empty i))
        rw [he]
    | @insert i s hi ih =>
        intro σ τ h
        let υ := Function.update σ i (τ i)
        have hu : w σ = w υ := by
          by_cases he : σ i = τ i
          · have heq : υ = σ := by
              funext j
              by_cases hj : j = i
              · subst j; simp [υ, he]
              · simp [υ, hj]
            rw [heq]
          · have he' : τ i = !σ i := by
              cases hs : σ i <;> cases ht : τ i <;> simp_all
            have heq : υ = flipSignAt σ i := by simp [υ, flipSignAt, he']
            rw [heq]
            exact (hw σ i).symm
        apply hu.trans (ih υ τ ?_)
        intro j hj
        by_cases hji : j = i
        · subst j; simp [υ]
        · simpa [υ, hji] using h j (by simp [hji, hj])
  intro σ τ
  exact aux univ σ τ (by simp)

/-- [A top-dimensional facet chain modulo two has zero boundary at every ridge if and only if all its facet weights equal a single constant](goal). -/
-- @node: signedTopCycle_iff_constant
lemma signedTopCycle_iff_constant {n : ℕ} (w : (Fin n → Bool) → ZMod 2) :
    (∀ σ i, signedTopBoundary w σ i = 0) ↔
      ∃ a : ZMod 2, ∀ σ, w σ = a := by
  constructor
  · intro hw
    have hinv : ∀ σ i, w (flipSignAt σ i) = w σ := by
      intro σ i
      have hb := hw σ i
      rw [signedTopBoundary_eq] at hb
      have htwo : w σ + w σ = 0 := ZModModule.add_self _
      exact add_left_cancel (hb.trans htwo.symm)
    exact ⟨w (fun _ => false), fun σ =>
      flipSignAt_invariant_constant w hinv σ (fun _ => false)⟩
  · rintro ⟨a, ha⟩ σ i
    rw [signedTopBoundary_eq, ha, ha]
    exact ZModModule.add_self _

-- @node: signedTopCycle_iff_zero_or_fundamental
/-- [A top-dimensional facet chain modulo two has zero boundary at every ridge if and only if every facet weight is zero or every facet weight is one](goal). -/
lemma signedTopCycle_iff_zero_or_fundamental {n : ℕ}
    (w : (Fin n → Bool) → ZMod 2) :
    (∀ σ i, signedTopBoundary w σ i = 0) ↔
      (∀ σ, w σ = 0) ∨ (∀ σ, w σ = 1) := by
  rw [signedTopCycle_iff_constant]
  constructor
  · rintro ⟨a, ha⟩
    fin_cases a
    · exact Or.inl ha
    · exact Or.inr ha
  · rintro (h | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩

/-- [Two top-dimensional facet chains modulo two have the same boundary at every ridge if and only if the sum of their weights is constant across all facets](goal). -/
-- @node: signedTopBoundary_eq_iff_constant_sum
lemma signedTopBoundary_eq_iff_constant_sum {n : ℕ}
    (w v : (Fin n → Bool) → ZMod 2) :
    (∀ σ i, signedTopBoundary w σ i = signedTopBoundary v σ i) ↔
      ∃ a : ZMod 2, ∀ σ, w σ + v σ = a := by
  rw [← signedTopCycle_iff_constant]
  constructor
  · intro h σ i
    rw [signedTopBoundary_add, h]
    exact ZModModule.add_self _
  · intro h σ i
    have hh := h σ i
    rw [signedTopBoundary_add] at hh
    have he : signedTopBoundary w σ i + signedTopBoundary v σ i =
        signedTopBoundary v σ i + signedTopBoundary v σ i :=
      hh.trans (ZModModule.add_self _).symm
    exact add_right_cancel he

-- @node: signedTopBoundary_eq_iff_eq_or_complement
/-- [Two top-dimensional facet chains modulo two have the same boundary at every ridge if and only if they are equal or one is obtained from the other by adding one to every facet weight](goal). -/
lemma signedTopBoundary_eq_iff_eq_or_complement {n : ℕ}
    (w v : (Fin n → Bool) → ZMod 2) :
    (∀ σ i, signedTopBoundary w σ i = signedTopBoundary v σ i) ↔
      w = v ∨ w = (fun σ => v σ + 1) := by
  rw [signedTopBoundary_eq_iff_constant_sum]
  constructor
  · rintro ⟨a, ha⟩
    have he : ∀ σ, w σ = v σ + a := by
      intro σ
      calc
        w σ = (w σ + v σ) + v σ := by simp [add_assoc, ZModModule.add_self]
        _ = v σ + a := by rw [ha]; exact add_comm _ _
    fin_cases a
    · change ∀ σ, w σ = v σ + (0 : ZMod 2) at he
      exact Or.inl (funext (fun σ => by simpa only [add_zero] using he σ))
    · exact Or.inr (funext he)
  · rintro (rfl | rfl)
    · exact ⟨0, fun σ => ZModModule.add_self _⟩
    · refine ⟨1, fun σ => ?_⟩
      simp [add_right_comm, ZModModule.add_self]

/-- If [the weights of each pair of antipodal facets sum to one modulo two](hyp:hw),
[the top-dimensional facet chain cannot have zero boundary at every ridge](goal). -/
-- @node: antipodal_complementary_topChain_not_cycle
lemma antipodal_complementary_topChain_not_cycle {n : ℕ}
    (w : (Fin n → Bool) → ZMod 2)
    (hw : ∀ σ, w σ + w (fun i => !σ i) = 1) :
    ¬ (∀ σ i, signedTopBoundary w σ i = 0) := by
  intro hcycle
  obtain ⟨a, ha⟩ := (signedTopCycle_iff_constant w).mp hcycle
  have hh := hw (fun _ => false)
  rw [ha, ha, ZModModule.add_self] at hh
  exact zero_ne_one hh

-- @node: antipodal_complementary_topChain_exists_boundary
/-- If [the weights of each pair of antipodal facets sum to one modulo two](hyp:hw),
[there is a ridge at which the boundary coefficient of the top-dimensional facet chain is nonzero](goal). -/
lemma antipodal_complementary_topChain_exists_boundary {n : ℕ}
    (w : (Fin n → Bool) → ZMod 2)
    (hw : ∀ σ, w σ + w (fun i => !σ i) = 1) :
    ∃ σ i, signedTopBoundary w σ i ≠ 0 := by
  classical
  simpa only [not_forall] using antipodal_complementary_topChain_not_cycle w hw

/-- [A top-dimensional facet chain modulo two has boundary coefficient one exactly at ridges omitting a specified coordinate, and zero at all other ridges, if and only if its weights select the facets with positive sign in that coordinate or the complementary set of facets](goal).

These are the two hemisphere fillings of the specified equator; in ambient dimension one the boundary is augmented. -/
-- @node: signedEquator_fillings
lemma signedEquator_fillings {n : ℕ} (j : Fin n)
    (w : (Fin n → Bool) → ZMod 2) :
    (∀ σ i, signedTopBoundary w σ i = if i = j then 1 else 0) ↔
      w = (fun σ => if σ j then 1 else 0) ∨
      w = (fun σ => (if σ j then 1 else 0) + 1) := by
  have heq : (∀ σ i, signedTopBoundary w σ i = if i = j then 1 else 0) ↔
      (∀ σ i, signedTopBoundary w σ i =
        signedTopBoundary (fun τ => if τ j then 1 else 0) σ i) := by
    simp only [signedTopBoundary, signedHemisphere_boundary_modTwo]
  exact heq.trans (signedTopBoundary_eq_iff_eq_or_complement _ _)

end Papers.TbsNeuralCausalPi.Antipodal
