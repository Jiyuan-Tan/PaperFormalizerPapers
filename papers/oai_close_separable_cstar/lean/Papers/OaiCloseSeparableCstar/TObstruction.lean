module

public import Papers.OaiCloseSeparableCstar.TSequences
public import Papers.OaiCloseSeparableCstar.Helpers.Invariant

/-! # Corollary 4: nonconjugacy from the tensor-norm distinction -/

public section

namespace Papers.OaiCloseSeparableCstar

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable (D P Q : StarSubalgebra ℂ (Op L))

-- @node: norm_unitary_conjugate_sub_le
/-- [Conjugating a bounded operator p by a unitary U changes p in norm by at most
twice the norm of p times the norm distance from U to the identity](goal). -/
lemma norm_unitary_conjugate_sub_le (U : unitary (Op L)) (p : Op L) :
    ‖(U : Op L) * p * star (U : Op L) - p‖ ≤ 2 * ‖p‖ * ‖(U : Op L) - 1‖ := by
  have he : ((U : Op L) * p * star (U : Op L) - p) * (U : Op L) =
      ((U : Op L) - 1) * p - p * ((U : Op L) - 1) := by
    simp only [sub_mul, mul_sub, mul_assoc, Unitary.star_mul_self_of_mem U.prop,
      mul_one, one_mul]
    abel
  calc
    _ = ‖((U : Op L) - 1) * p - p * ((U : Op L) - 1)‖ := by
      rw [← he, CStarRing.norm_mul_coe_unitary]
    _ ≤ ‖((U : Op L) - 1) * p‖ + ‖p * ((U : Op L) - 1)‖ := norm_sub_le _ _
    _ ≤ ‖(U : Op L) - 1‖ * ‖p‖ + ‖p‖ * ‖(U : Op L) - 1‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = _ := by ring

-- @node: kkDist_unitary_conjugate_le
/-- If [the unitary U conjugates P onto Q](hyp:hU), [the Kadison–Kastler distance
between P and Q is at most twice the norm distance from U to the identity](goal). -/
lemma kkDist_unitary_conjugate_le (U : unitary (Op L))
    (hU : conjSet (U : Op L) P = (Q : Set _)) :
    kkDist P Q ≤ 2 * ‖(U : Op L) - 1‖ := by
  have hn (p : Op L) : ‖(U : Op L) * p * star (U : Op L)‖ = ‖p‖ := by
    rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem U.prop),
      CStarRing.norm_coe_unitary_mul]
  have hb (p : Op L) (hp : ‖p‖ ≤ 1) :
      ‖(U : Op L) * p * star (U : Op L) - p‖ ≤ 2 * ‖(U : Op L) - 1‖ := by
    exact (norm_unitary_conjugate_sub_le U p).trans (by
      nlinarith [norm_nonneg ((U : Op L) - 1)])
  apply Metric.hausdorffDist_le_of_mem_dist (by positivity)
  · intro p hp
    refine ⟨(U : Op L) * p * star (U : Op L), ⟨?_, ?_⟩, ?_⟩
    · change (U : Op L) * p * star (U : Op L) ∈ (Q : Set _)
      rw [← hU]
      exact ⟨p, hp.1, rfl⟩
    · exact (hn p).trans_le hp.2
    · simpa only [dist_eq_norm_sub, norm_sub_rev] using hb p hp.2
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := (show q ∈ conjSet (U : Op L) P by rw [hU]; exact hq.1)
    refine ⟨p, ⟨hp, ?_⟩, ?_⟩
    · exact (hn p).symm.trans_le hq.2
    · simpa only [dist_eq_norm_sub] using hb p ((hn p).symm.trans_le hq.2)

-- @node: thm:obstruction
/-- Suppose [the Hilbert space is nonzero and separable](hyp:hL), [D is norm closed
and norm separable](hyp:hD), [the center of D consists only of scalar identities](hyp:hcenter),
[P and Q are norm-closed unital star subalgebras of D](hyp:hPQ), and [P satisfies
the spatial tensor norm identity relative to D whereas Q fails it](hyp:hdistinction).
Then [the sequence algebras with entries in D and limits in P and Q are not
unitarily conjugate, and every unitary W conjugating P onto Q bounds their
Kadison–Kastler distance by twice the norm distance from W to the identity](goal). -/
theorem seqAlg_obstruction (hL : SequencesL L) (hD : SequencesD D)
    (hcenter : SequencesCenter D) (hPQ : SequencesSubalgebras D P Q)
    (hdistinction : ObstructionTensorDistinction D P Q) :
    ¬ SequencesConjugacy D P Q ∧
      ∀ W : Op L, ObstructionUnitary P Q W →
        kkDist (seqAlg D P) (seqAlg D Q) ≤ 2 * ‖W - 1‖ := by
  constructor
  · intro hconj
    obtain ⟨U, hnormal, happ⟩ := (seqAlg_properties D P Q hL hD hcenter hPQ).2.1 hconj
    have hinv : InvariantUnital D P Q :=
      ⟨hD.1, hPQ.2.2.1, hPQ.2.2.2, hPQ.1, hPQ.2.1⟩
    exact hdistinction.2 ((tensorIdentity_invariant D P Q hinv).2 U
      ⟨hnormal, happ⟩ hdistinction.1)
  · intro W hW
    rw [seqAlg_kkDist_eq D P Q hPQ.1 hPQ.2.1]
    exact kkDist_unitary_conjugate_le P Q ⟨W, hW.1⟩ hW.2

end Papers.OaiCloseSeparableCstar
