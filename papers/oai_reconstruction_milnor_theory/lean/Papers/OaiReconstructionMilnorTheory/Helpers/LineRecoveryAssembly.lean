module

public import Papers.OaiReconstructionMilnorTheory.Helpers.CompatibleOperations
public import Papers.OaiReconstructionMilnorTheory.Helpers.LineRecoveryGeometry

/-! # Assembling exact and unique line correction from forward containment -/

public section

namespace Papers.OaiReconstructionMilnorTheory

variable (p : ℕ) {K L : Type*} [Field K] [Field L]

/-- Suppose [p is prime](hyp:hp), [K](hyp:hK) and [L](hyp:hL) have characteristic p,
[K has a proper power subfield](hyp:hiK) and [L has a proper power subfield](hyp:hiL), and
[Θ is a compatible Milnor isomorphism](hyp:hΘ). If [some invertible scalar multiple
of Θ sends each source line into a target line](hyp:hf) and [every compatible
isomorphism in the reverse direction admits such a scalar correction](hyp:hb),
then [there is a unique invertible scalar whose multiple of Θ sends every source
projective line onto a target projective line](goal). -/
-- @node: lineRecovery_unique_of_containment
lemma lineRecovery_unique_of_containment (hp : PrimeChar p)
    (hK : CharP K p) (hL : CharP L p)
    (hiK : ScalarLineImperfect p K) (hiL : ScalarLineImperfect p L)
    (Θ : MilnorOne K p → MilnorOne L p) (hΘ : IsCompatibleIso p Θ)
    (hf : ∃ n : (Coeff p)ˣ, ∀ S, IsProjLine p K S →
      ∃ T, IsProjLine p L T ∧ scalarAct p n Θ '' S ⊆ T)
    (hb : ∀ Φ : MilnorOne L p → MilnorOne K p, IsCompatibleIso p Φ →
      ∃ r : (Coeff p)ˣ, ∀ T, IsProjLine p L T →
        ∃ S, IsProjLine p K S ∧ scalarAct p r Φ '' T ⊆ S) :
    ∃! n : (Coeff p)ˣ, ∀ S, IsProjLine p K S →
      IsProjLine p L (scalarAct p n Θ '' S) := by
  obtain ⟨n, hn⟩ := hf
  have hΨ := scalarAct_compatible p hp n Θ hΘ
  let Ψ := compatibleLinearEquiv p (scalarAct p n Θ) hΨ
  have hΨinv : IsCompatibleIso p Ψ.symm :=
    compatibleLinearEquiv_symm_compatible p (scalarAct p n Θ) hΨ
  obtain ⟨r, hr⟩ := hb Ψ.symm hΨinv
  have hlines := lineRecovery_exact_of_corrected_inverse p hp hK hiK
    Ψ.toEquiv r hn hr
  refine ⟨n, hlines.1, ?_⟩
  intro m hm
  exact lineRecovery_correction_unique p hp hL hiL Θ n m
    (lineRecovery_lines_surjective p Ψ.toEquiv hlines.2) hm

end Papers.OaiReconstructionMilnorTheory
