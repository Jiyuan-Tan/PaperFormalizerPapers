module

public import Papers.OaiReconstructionMilnorTheory.Helpers.Isomorphisms
public import Papers.OaiReconstructionMilnorTheory.Helpers.Symbols
public import Papers.OaiReconstructionMilnorTheory.Helpers.Intersection
public import Papers.OaiReconstructionMilnorTheory.Helpers.ScalarLine
public import Papers.OaiReconstructionMilnorTheory.Helpers.FieldReconstruction
public import Papers.OaiReconstructionMilnorTheory.Helpers.LineRecoveryAssembly
public import Papers.OaiReconstructionMilnorTheory.Helpers.LineRecoveryContainment

/-! # Recovery of projective lines up to a unique scalar -/

@[expose] public section

namespace Papers.OaiReconstructionMilnorTheory

variable (p : ℕ) {K L : Type*} [Field K] [Field L]

-- @node: ass:line-recovery-fields
/-- For [a characteristic parameter p](hyp:p) and [subfields k of K](hyp:k) and
[l of L](hyp:l), the [line-recovery field assumptions](goal) require that
[k is algebraically closed and K is finitely generated over k in characteristic p](step:1),
[l is algebraically closed and L is finitely generated over l in characteristic p](step:2),
[K has transcendence degree at least two over k](step:3), and
[L has transcendence degree at least two over l](step:4). -/
def LineRecoveryFields (k : Subfield K) (l : Subfield L) : Prop :=
  GeometricField p ↥k K ∧ GeometricField p ↥l L ∧
    2 ≤ Algebra.trdeg ↥k K ∧ 2 ≤ Algebra.trdeg ↥l L

-- @node: prop:lines
/-- If [p is prime](hyp:hp), [K and L satisfy the line-recovery field assumptions
over k and l](hyp:hfields), and [Θ is a compatible isomorphism of their first
Milnor groups](hyp:hΘ), then [there is a unique nonzero coefficient scalar such
that multiplying Θ by this scalar sends every projective line in K onto a
projective line in L](goal). -/
lemma exists_unique_line_correction (k : Subfield K) (l : Subfield L)
    (hp : PrimeChar p) (hfields : LineRecoveryFields p k l)
    (Θ : MilnorOne K p → MilnorOne L p) (hΘ : IsCompatibleIso p Θ) :
    ∃! n : (Coeff p)ˣ, -- @realizes n(unique nonzero line-correction scalar)
      ∀ S : Set (MilnorOne K p), IsProjLine p K S →
        IsProjLine p L (scalarAct p n Θ '' S) := by
  have hiK : ScalarLineImperfect p K := powSubfield_ne_top_of_finrank p
    (le_trans (by decide : 2 ≤ 4)
      (geometricField_powSubfield_finrank_ge_four p ↥k hp hfields.1 hfields.2.2.1))
  have hiL : ScalarLineImperfect p L := powSubfield_ne_top_of_finrank p
    (le_trans (by decide : 2 ≤ 4)
      (geometricField_powSubfield_finrank_ge_four p ↥l hp hfields.2.1 hfields.2.2.2))
  have hcontain :
      (∃ n : (Coeff p)ˣ, ∀ S, IsProjLine p K S →
        ∃ T, IsProjLine p L T ∧ scalarAct p n Θ '' S ⊆ T) ∧
      (∀ Φ : MilnorOne L p → MilnorOne K p, IsCompatibleIso p Φ →
        ∃ r : (Coeff p)ˣ, ∀ T, IsProjLine p L T →
          ∃ S, IsProjLine p K S ∧ scalarAct p r Φ '' T ⊆ S) := by
    refine ⟨lineRecovery_forward_containment p ↥k ↥l hp hfields.1 hfields.2.1
      hfields.2.2.2 Θ hΘ, ?_⟩
    intro Φ hΦ
    exact lineRecovery_forward_containment p ↥l ↥k hp hfields.2.1 hfields.1
      hfields.2.2.1 Φ hΦ
  exact lineRecovery_unique_of_containment p hp hfields.1.2.1 hfields.2.1.2.1
    hiK hiL Θ hΘ hcontain.1 hcontain.2

end Papers.OaiReconstructionMilnorTheory
