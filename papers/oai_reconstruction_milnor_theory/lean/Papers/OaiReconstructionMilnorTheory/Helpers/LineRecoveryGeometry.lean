module

public import Papers.OaiReconstructionMilnorTheory.Helpers.Isomorphisms
public import Papers.OaiReconstructionMilnorTheory.Helpers.ScalarLine

/-! # The final incidence steps of line recovery -/

public section

namespace Papers.OaiReconstructionMilnorTheory

variable (p : ℕ) {K L : Type*} [Field K] [Field L]

/-- If [every class represented by a nonzero element of W is represented by a nonzero
element of W′](hyp:h), then [W is contained in W′](goal). -/
-- @node: lineRecovery_submodule_le
lemma lineRecovery_submodule_le
    (W W' : Submodule ↥(powSubfield p K) K)
    (h : {x | ∃ f ∈ W, f ≠ 0 ∧ cls p f = x} ⊆
      {x | ∃ f ∈ W', f ≠ 0 ∧ cls p f = x}) : W ≤ W' := by
  intro f hf
  by_cases hf0 : f = 0
  · simpa [hf0] using W'.zero_mem
  obtain ⟨g, hg, hg0, heq⟩ := h ⟨f, hf, hf0, rfl⟩
  exact scalarLine_mem_of_cls_eq p K W' hf0 hg0 heq.symm hg

/-- If [S](hyp:hS) and [T](hyp:hT) are projective lines and [S is contained in T](hyp:hST),
then [S and T are equal](goal). -/
-- @node: lineRecovery_line_eq_of_subset
lemma lineRecovery_line_eq_of_subset {S T : Set (MilnorOne K p)}
    (hS : IsProjLine p K S) (hT : IsProjLine p K T) (hST : S ⊆ T) : S = T := by
  obtain ⟨W, hW, rfl⟩ := hS
  obtain ⟨W', hW', rfl⟩ := hT
  let : FiniteDimensional ↥(powSubfield p K) W' :=
    Module.finite_of_finrank_eq_succ hW'
  have hWW' : W = W' := Submodule.eq_of_le_of_finrank_eq
    (lineRecovery_submodule_le p W W' hST) (hW.trans hW'.symm)
  rw [hWW']

/-- If [the bijection sends each source projective line into a target projective
line](hyp:hf) and [its inverse sends each target projective line into a source
projective line](hyp:hb), then [the image of every source projective line is a
target projective line](goal). -/
-- @node: lineRecovery_exact_images
lemma lineRecovery_exact_images (Ψ : MilnorOne K p ≃ MilnorOne L p)
    (hf : ∀ S, IsProjLine p K S →
      ∃ T, IsProjLine p L T ∧ Ψ '' S ⊆ T)
    (hb : ∀ T, IsProjLine p L T →
      ∃ S, IsProjLine p K S ∧ Ψ.symm '' T ⊆ S) :
    ∀ S, IsProjLine p K S → IsProjLine p L (Ψ '' S) := by
  intro S hS
  obtain ⟨T, hT, hST⟩ := hf S hS
  obtain ⟨S', hS', hTS'⟩ := hb T hT
  have hSS' : S ⊆ S' := by
    intro x hx
    exact hTS' ⟨Ψ x, hST ⟨x, hx, rfl⟩, Ψ.symm_apply_apply x⟩
  have heq := lineRecovery_line_eq_of_subset p hS hS' hSS'
  have himage : Ψ '' S = T := Set.Subset.antisymm hST (by
    intro y hy
    refine ⟨Ψ.symm y, ?_, Ψ.apply_symm_apply y⟩
    rw [heq]
    exact hTS' ⟨y, hy, rfl⟩)
  rwa [himage]

/-- Suppose [p is prime](hyp:hp), [K has characteristic p](hyp:hK), and [K has
a proper power subfield](hyp:himperfect). If [the bijection sends
each source line into a target line](hyp:hf) and [its inverse, multiplied by r,
sends each target line into a source line](hyp:hb), then [r equals one](goal). -/
-- @node: lineRecovery_inverse_scalar_eq_one
lemma lineRecovery_inverse_scalar_eq_one (hp : PrimeChar p) (hK : CharP K p)
    (himperfect : ScalarLineImperfect p K)
    (Ψ : MilnorOne K p ≃ MilnorOne L p) (r : (Coeff p)ˣ)
    (hf : ∀ S, IsProjLine p K S →
      ∃ T, IsProjLine p L T ∧ Ψ '' S ⊆ T)
    (hb : ∀ T, IsProjLine p L T →
      ∃ S, IsProjLine p K S ∧ scalarAct p r Ψ.symm '' T ⊆ S) : r = 1 := by
  apply scalar_eq_one_of_preserves_lines p K r hp hK himperfect
  intro S hS
  obtain ⟨T, hT, hST⟩ := hf S hS
  obtain ⟨S', hS', hTS'⟩ := hb T hT
  refine ⟨S', hS', ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hmem := hTS' ⟨Ψ x, hST ⟨x, hx, rfl⟩, rfl⟩
  simpa only [scalarAct, Equiv.symm_apply_apply] using hmem

/-- Suppose [p is prime](hyp:hp), [K has characteristic p](hyp:hK), and [K has
a proper power subfield](hyp:himperfect). If [the bijection sends
each source line into a target line](hyp:hf) and [its inverse, multiplied by r,
sends each target line into a source line](hyp:hb), then [both the bijection and
its inverse send every projective line onto a projective line](goal). -/
-- @node: lineRecovery_exact_of_corrected_inverse
lemma lineRecovery_exact_of_corrected_inverse (hp : PrimeChar p) (hK : CharP K p)
    (himperfect : ScalarLineImperfect p K)
    (Ψ : MilnorOne K p ≃ MilnorOne L p) (r : (Coeff p)ˣ)
    (hf : ∀ S, IsProjLine p K S →
      ∃ T, IsProjLine p L T ∧ Ψ '' S ⊆ T)
    (hb : ∀ T, IsProjLine p L T →
      ∃ S, IsProjLine p K S ∧ scalarAct p r Ψ.symm '' T ⊆ S) :
    (∀ S, IsProjLine p K S → IsProjLine p L (Ψ '' S)) ∧
    (∀ T, IsProjLine p L T → IsProjLine p K (Ψ.symm '' T)) := by
  have hr := lineRecovery_inverse_scalar_eq_one p hp hK himperfect Ψ r hf hb
  have hb' : ∀ T, IsProjLine p L T →
      ∃ S, IsProjLine p K S ∧ Ψ.symm '' T ⊆ S := by
    have hfun : scalarAct p r Ψ.symm = Ψ.symm := by
      funext x
      simp [scalarAct, hr]
    rwa [hfun] at hb
  exact ⟨lineRecovery_exact_images p Ψ hf hb',
    lineRecovery_exact_images p Ψ.symm hb' hf⟩

/-- If [the inverse bijection sends every target projective line onto a source
projective line](hyp:hb), then [every target projective line is the image of a
source projective line](goal). -/
-- @node: lineRecovery_lines_surjective
lemma lineRecovery_lines_surjective (Ψ : MilnorOne K p ≃ MilnorOne L p)
    (hb : ∀ T, IsProjLine p L T → IsProjLine p K (Ψ.symm '' T)) :
    ∀ T, IsProjLine p L T → ∃ S, IsProjLine p K S ∧ Ψ '' S = T := by
  intro T hT
  refine ⟨Ψ.symm '' T, hb T hT, ?_⟩
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    simpa using hx
  · intro hy
    exact ⟨Ψ.symm y, ⟨y, hy, rfl⟩, Ψ.apply_symm_apply y⟩

/-- Suppose [p is prime](hyp:hp), [L has characteristic p](hyp:hL), and [L has
a proper power subfield](hyp:himperfect). If [every target line is
the image of a source line under the map multiplied by n](hyp:hn) and [the map
multiplied by m sends every source line onto a target line](hyp:hm), then
[m equals n](goal). -/
-- @node: lineRecovery_correction_unique
lemma lineRecovery_correction_unique (hp : PrimeChar p) (hL : CharP L p)
    (himperfect : ScalarLineImperfect p L)
    (Θ : MilnorOne K p → MilnorOne L p)
    (n m : (Coeff p)ˣ)
    (hn : ∀ T, IsProjLine p L T →
      ∃ S, IsProjLine p K S ∧ scalarAct p n Θ '' S = T)
    (hm : ∀ S, IsProjLine p K S → IsProjLine p L (scalarAct p m Θ '' S)) :
    m = n := by
  have hratio : ScalarLinePreservation p L (m * n⁻¹) := by
    intro T hT
    obtain ⟨S, hS, rfl⟩ := hn T hT
    refine ⟨scalarAct p m Θ '' S, hm S hS, ?_⟩
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    simp [scalarAct, smul_smul]
  have hone := scalar_eq_one_of_preserves_lines p L (m * n⁻¹) hp hL himperfect hratio
  have heq := congrArg (fun r => r * n) hone
  simpa [mul_assoc] using heq

end Papers.OaiReconstructionMilnorTheory
