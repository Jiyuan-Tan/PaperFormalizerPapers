module

public import Papers.OaiCloseSeparableCstar.Helpers.SequenceConjugacy

/-! # Proposition 2: convergent-sequence algebras -/

public section

namespace Papers.OaiCloseSeparableCstar

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable (D P Q : StarSubalgebra ℂ (Op L))

-- @node: prop:sequences
/-- Suppose [the Hilbert space is nonzero and separable](hyp:hL), [D is norm closed
and norm separable](hyp:hD), [the center of D consists only of scalar identities](hyp:hcenter),
and [P and Q are norm-closed unital star subalgebras of D](hyp:hPQ). Then [the
sequence algebras with entries in D and limits in P and Q are norm closed and
norm separable, have Kadison–Kastler distance equal to that between P and Q, and
have equal commutants and double commutants; moreover, unitary conjugacy of the
sequence algebras implies that there is one sequence of unitaries normalizing D
such that every element b of Q is a norm limit of conjugates, along this sequence,
of a fixed element of P depending on b](goal). -/
theorem seqAlg_properties (hL : SequencesL L) (hD : SequencesD D)
    (hcenter : SequencesCenter D) (hPQ : SequencesSubalgebras D P Q) :
    (IsClosed (seqAlg D P : Set (Op (SumSpace L))) ∧
      IsClosed (seqAlg D Q : Set (Op (SumSpace L))) ∧
      TopologicalSpace.IsSeparable (seqAlg D P : Set (Op (SumSpace L))) ∧
      TopologicalSpace.IsSeparable (seqAlg D Q : Set (Op (SumSpace L))) ∧
      kkDist (seqAlg D P) (seqAlg D Q) = kkDist P Q) ∧
    (SequencesConjugacy D P Q →
      ∃ U : ℕ → unitary (Op L), -- @realizes U_n(one sequence common to every b)
        (∀ n, conjSet (U n : Op L) D = (D : Set _)) ∧ -- @realizes U_n(normalizes D at every index)
        ∀ b ∈ Q, -- @realizes b(element of Q)
          ∃ p ∈ P, PointwiseNormalizerApprox b U p) ∧ -- @realizes p_b(fixed approximant in P)
    (commutant (seqAlg D P : Set (Op (SumSpace L))) =
        commutant (seqAlg D Q : Set (Op (SumSpace L))) ∧
      commutant (commutant (seqAlg D P : Set (Op (SumSpace L)))) =
        commutant (commutant (seqAlg D Q : Set (Op (SumSpace L))))) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨seqAlg_isClosed D P hD.1 hPQ.2.2.1,
      seqAlg_isClosed D Q hD.1 hPQ.2.2.2, ?_, ?_, ?_⟩
    · exact seqAlg_isSeparable D P hD.2 hPQ.1
    · exact seqAlg_isSeparable D Q hD.2 hPQ.2.1
    · exact seqAlg_kkDist_eq D P Q hPQ.1 hPQ.2.1
  · letI : Nontrivial L := hL.1
    exact fun hc => seqAlg_conjugacy_normalizers D P Q hcenter hPQ.2.1 hc
  · have h := seqAlg_commutant_eq D P Q
    exact ⟨h, congrArg commutant h⟩

end Papers.OaiCloseSeparableCstar
