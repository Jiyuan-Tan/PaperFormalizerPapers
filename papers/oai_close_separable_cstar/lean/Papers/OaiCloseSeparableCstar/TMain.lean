module

public import Papers.OaiCloseSeparableCstar.TObstruction
public import Papers.OaiCloseSeparableCstar.Helpers.GoodInclusion
public import Papers.OaiCloseSeparableCstar.Helpers.BadInclusion

/-! # Theorem 1: arbitrarily close separable C*-algebras that are not unitarily conjugate -/

public section

namespace Papers.OaiCloseSeparableCstar

-- @node: exists_small_deformation
/-- For [any strictly positive tolerance ε](hyp:hε), [there is a deformation
parameter strictly between zero and one for which twice the perturbation bound
is less than ε](goal). -/
lemma exists_small_deformation (ε : ℝ) (hε : 0 < ε) :
    ∃ (t : ℝ) (ht : DeformationRange t), 2 * cBound t ht < ε := by
  let f : ℝ → ℝ := fun t => 2 * (1 - Real.sqrt (1 - t ^ 2)) + t / (1 - t) + t
  have hc : ContinuousAt f 0 := by
    dsimp [f]
    fun_prop (disch := norm_num)
  obtain ⟨δ, hδ, hb⟩ := Metric.continuousAt_iff.mp hc (ε / 2) (by positivity)
  let t := min δ 1 / 2
  have htpos : 0 < t := by dsimp [t]; positivity
  have htd : t < δ := by
    have := min_le_left δ 1
    dsimp [t]
    linarith [lt_min hδ (by norm_num : (0 : ℝ) < 1)]
  have htone : t < 1 := by
    have := min_le_right δ 1
    dsimp [t]
    linarith
  have ht : DeformationRange t := ⟨htpos, htone⟩
  refine ⟨t, ht, ?_⟩
  have hdist : dist t 0 < δ := by simpa [Real.dist_eq, abs_of_pos htpos] using htd
  have h := hb hdist
  have hfzero : f 0 = 0 := by norm_num [f]
  rw [hfzero, dist_zero_right, Real.norm_eq_abs] at h
  have hle := le_abs_self (f t)
  change 2 * f t < ε
  linarith

-- @node: thm:main
/-- For [any strictly positive tolerance ε](hyp:hε), [there exist a separable
complex Hilbert space and two norm-closed, norm-separable unital star subalgebras
of its bounded operators whose Kadison–Kastler distance is less than ε and whose
double commutants coincide, but which no unitary operator conjugates onto one
another](goal). -/
theorem exists_close_not_conjugate
    (ε : ℝ) (hε : 0 < ε) : -- @realizes \varepsilon(arbitrary strictly positive distance tolerance)
    ∃ (H : Type) -- @realizes H(complex Hilbert space witness)
      (hNorm : NormedAddCommGroup H), -- @realizes H(normed additive group)
      letI := hNorm
      ∃ (hInner : InnerProductSpace ℂ H), -- @realizes H(complex inner-product space)
      letI := hInner
      ∃ (hComplete : CompleteSpace H), -- @realizes H(complete, hence Hilbert)
      letI := hComplete
      TopologicalSpace.SeparableSpace H ∧ -- @realizes H(separable)
      ∃ A B : StarSubalgebra ℂ (Op H), -- @realizes A(unital star subalgebra of B(H))
        -- @realizes B(unital star subalgebra of B(H))
        IsClosed (A : Set (Op H)) ∧ -- @realizes A(norm closed)
        IsClosed (B : Set (Op H)) ∧ -- @realizes B(norm closed)
        TopologicalSpace.IsSeparable (A : Set (Op H)) ∧ -- @realizes A(norm separable)
        TopologicalSpace.IsSeparable (B : Set (Op H)) ∧ -- @realizes B(norm separable)
        kkDist A B < ε ∧
        commutant (commutant (A : Set (Op H))) = commutant (commutant (B : Set (Op H))) ∧
        ¬ ∃ u ∈ unitary (Op H), -- @realizes u(potential unitary conjugating A onto B)
          conjSet u A = (B : Set _) := by
  obtain ⟨t, ht, hsmall⟩ := exists_small_deformation ε hε
  obtain ⟨π, hπ⟩ := exists_treeRep.1 t ht
  let D := Dalg π
  let P := Palg piZero
  let Q := Palg π
  have hL := LSp_nonzero_separable
  have hD : SequencesD D := Dalg_closed_separable π
  have hPQ : SequencesSubalgebras D P Q := Palg_inclusions π
  obtain ⟨hcenter, _, W, hW, hconj, hclose⟩ := ambient_properties t ht π hπ
  have hprops := seqAlg_properties D P Q hL hD hcenter hPQ
  have hdist : ObstructionTensorDistinction D P Q :=
    ⟨goodInclusion t ht π hπ, badInclusion t ht π hπ⟩
  have hobs := seqAlg_obstruction D P Q hL hD hcenter hPQ hdist
  have : TopologicalSpace.SeparableSpace LSp := hL.2
  have hsep : TopologicalSpace.SeparableSpace (SumSpace LSp) :=
    separableSpace_hilbertSum ℕ LSp
  refine ⟨SumSpace LSp, inferInstance, inferInstance, inferInstance, hsep,
    seqAlg D P, seqAlg D Q, hprops.1.1, hprops.1.2.1,
    hprops.1.2.2.1, hprops.1.2.2.2.1, ?_, hprops.2.2.2, ?_⟩
  · exact ((hobs.2 W ⟨hW, hconj⟩).trans
      (mul_le_mul_of_nonneg_left hclose (by norm_num))).trans_lt hsmall
  · exact hobs.1

end Papers.OaiCloseSeparableCstar
