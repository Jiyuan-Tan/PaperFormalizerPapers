module

public import Papers.OaiCloseSeparableCstar.Basic

/-! # Lemma 3: invariance of the spatial tensor-norm identity -/

public section

namespace Papers.OaiCloseSeparableCstar

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
open Filter Topology
open scoped BigOperators TensorProduct

variable (D P Q : StarSubalgebra ℂ (Op L))

-- @node: tensorSumNorm_eq_opNorm
/-- For [two finite families of bounded operators](hyp:p,z), [the spatial tensor-sum
norm defined by a supremum equals the operator norm of the sum of their tensor
products](goal). -/
lemma tensorSumNorm_eq_opNorm {m : ℕ} (p z : Fin m → Op L) :
    tensorSumNorm p z = ‖∑ i, TensorProduct.mapL (p i) (z i)‖ := by
  classical
  simpa only [tensorSumNorm, sum_apply, TensorProduct.mapL_apply,
    LinearMap.sum_apply, Metric.closedBall, dist_zero_right] using
    (∑ i, TensorProduct.mapL (p i) (z i)).sSup_unitClosedBall_eq_norm

-- @node: norm_conjugate_contractions
/-- If [the operator A has norm at most one](hyp:hA), [the operator B has norm at
most one](hyp:hB), and [B composed with A is the identity](hyp:hBA), then
[composing any bounded operator T on the left with A and on the right with B
preserves its norm](goal). -/
lemma norm_conjugate_contractions {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (A B T : Op V) (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (hBA : B * A = 1) : ‖A * T * B‖ = ‖T‖ := by
  have hle (C E R : Op V) (hC : ‖C‖ ≤ 1) (hE : ‖E‖ ≤ 1) :
      ‖C * R * E‖ ≤ ‖R‖ := by
    calc
      _ ≤ (‖C‖ * ‖R‖) * ‖E‖ := (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (1 * ‖R‖) * 1 := by gcongr
      _ = ‖R‖ := by ring
  apply le_antisymm (hle A B T hA hB)
  have h := hle B A (A * T * B) hB hA
  simpa only [mul_assoc, ← mul_assoc B A, hBA, one_mul, mul_one] using h

-- @node: normalizer_pullback_commutant
/-- If [conjugation by the unitary U maps D onto itself](hyp:hU) and [z commutes
with every element of D](hyp:hz), then [the operator obtained by composing the
adjoint of U, z, and U also commutes with every element of D](goal). -/
lemma normalizer_pullback_commutant (U : unitary (Op L))
    (hU : conjSet (U : Op L) D = (D : Set _))
    {z : Op L} (hz : z ∈ commutant D) :
    star (U : Op L) * z * (U : Op L) ∈ commutant D := by
  intro d hd
  have hd' : (U : Op L) * d * star (U : Op L) ∈ D := by
    change (U : Op L) * d * star (U : Op L) ∈ (D : Set _)
    rw [← hU]
    exact ⟨d, hd, rfl⟩
  have h := congrArg (fun a : Op L => star (U : Op L) * a * (U : Op L)) (hz _ hd')
  simpa only [mul_assoc, ← mul_assoc (star (U : Op L)) (U : Op L),
    Unitary.star_mul_self_of_mem U.prop, one_mul, mul_one] using h

-- @node: tensorSumNorm_conjugate
/-- For [a unitary operator U](hyp:U) and [two finite families of bounded
operators](hyp:p,z), [conjugating both families by U preserves their spatial
tensor-sum norm](goal). -/
lemma tensorSumNorm_conjugate {m : ℕ} (U : unitary (Op L)) (p z : Fin m → Op L) :
    tensorSumNorm (fun i => (U : Op L) * p i * star (U : Op L))
      (fun i => (U : Op L) * z i * star (U : Op L)) = tensorSumNorm p z := by
  classical
  let A := TensorProduct.mapL (U : Op L) (U : Op L)
  let B := TensorProduct.mapL (star (U : Op L)) (star (U : Op L))
  have hA : ‖A‖ ≤ 1 := by
    exact (TensorProduct.norm_mapL_le _ _).trans
      (by simpa using (mul_le_mul (unitary_norm_le_one U) (unitary_norm_le_one U)
        (norm_nonneg _) zero_le_one))
  have hB : ‖B‖ ≤ 1 := by
    exact (TensorProduct.norm_mapL_le _ _).trans
      (by simpa only [norm_star, one_mul] using
        (mul_le_mul (unitary_norm_le_one U) (unitary_norm_le_one U)
          (norm_nonneg _) zero_le_one))
  have hBA : B * A = 1 := by
    dsimp [A, B]
    rw [← TensorProduct.mapL_mul, Unitary.star_mul_self_of_mem U.prop]
    exact TensorProduct.mapL_id_id
  rw [tensorSumNorm_eq_opNorm, tensorSumNorm_eq_opNorm]
  have he : (∑ i, TensorProduct.mapL ((U : Op L) * p i * star (U : Op L))
      ((U : Op L) * z i * star (U : Op L))) =
      A * (∑ i, TensorProduct.mapL (p i) (z i)) * B := by
    simp only [A, B, TensorProduct.mapL_mul, Finset.mul_sum, Finset.sum_mul]
  rw [he]
  exact norm_conjugate_contractions _ _ _ hA hB hBA

-- @node: tensorIdentity_conjugate
/-- If [conjugation by the unitary U maps D onto itself](hyp:hU) and [the norm of
each finite sum of products from P and the commutant of D equals the corresponding
spatial tensor-sum norm](hyp:hP), then [the same norm identity holds with P replaced
by its conjugate under U](goal). -/
lemma tensorIdentity_conjugate (U : unitary (Op L))
    (hU : conjSet (U : Op L) D = (D : Set _))
    (hP : HasSpatialTensorIdentity D P) : HasSpatialTensorIdentity D (conjAlg U P) := by
  classical
  intro m hm q z hq hz
  change ∀ i, ∃ p ∈ P, (U : Op L) * p * star (U : Op L) = q i at hq
  choose p hp he using hq
  let w := fun i => star (U : Op L) * z i * (U : Op L)
  have hw : ∀ i, w i ∈ commutant D := fun i =>
    normalizer_pullback_commutant D U hU (hz i)
  have hwz (i) : (U : Op L) * w i * star (U : Op L) = z i := by
    simp only [w, mul_assoc, ← mul_assoc (U : Op L) (star (U : Op L)),
      Unitary.mul_star_self_of_mem U.prop, one_mul, mul_one]
  have hprod : (∑ i, q i * z i) =
      (U : Op L) * (∑ i, p i * w i) * star (U : Op L) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [← he i, ← hwz i]
    simp only [mul_assoc, ← mul_assoc (star (U : Op L)) (U : Op L),
      Unitary.star_mul_self_of_mem U.prop, one_mul]
  calc
    ‖∑ i, q i * z i‖ = ‖∑ i, p i * w i‖ := by
      rw [hprod, CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem U.prop),
        CStarRing.norm_coe_unitary_mul]
    _ = tensorSumNorm p w := hP m hm p w hp hw
    _ = tensorSumNorm q z := by
      have h := tensorSumNorm_conjugate U p w
      simpa only [he, hwz] using h.symm

-- @node: tensorMap_left_continuous
/-- For [a fixed bounded operator z](hyp:z), [the tensor product of p with z
depends continuously on p in operator norm](goal). -/
@[fun_prop] lemma tensorMap_left_continuous (z : Op L) :
    Continuous (fun p : Op L => TensorProduct.mapL p z) := by
  apply LipschitzWith.continuous (K := ‖z‖₊)
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have he : TensorProduct.mapL p z - TensorProduct.mapL q z =
      TensorProduct.mapL (p - q) z := by
    have h := TensorProduct.mapL_add_left (p - q) q z
    rw [sub_add_cancel] at h
    exact sub_eq_iff_eq_add.mpr h
  rw [dist_eq_norm_sub, dist_eq_norm_sub, he]
  change ‖TensorProduct.mapL (p - q) z‖ ≤ ‖z‖ * ‖p - q‖
  simpa only [mul_comm] using TensorProduct.norm_mapL_le (p - q) z

-- @node: lem:invariant
/-- Suppose [D, P, and Q are closed operator algebras, with P and Q contained in
D](hyp:hDPQ). Then [the spatial tensor norm identity for P and the commutant of D
passes both to every conjugate of P by a unitary normalizing D and to Q whenever
there is a sequence of such unitaries under which every element of Q is the norm
limit of conjugates of a fixed element of P](goal). -/
lemma tensorIdentity_invariant (hDPQ : InvariantUnital D P Q) :
    (∀ U : unitary (Op L), conjSet (U : Op L) D = (D : Set _) →
      HasSpatialTensorIdentity D P → HasSpatialTensorIdentity D (conjAlg U P)) ∧
    (∀ U : ℕ → unitary (Op L), InvariantApproximation D P Q U →
      HasSpatialTensorIdentity D P → HasSpatialTensorIdentity D Q) := by
  constructor
  · intro U hU hP
    exact tensorIdentity_conjugate D P U hU hP
  · intro U hApprox hP m hm b z hb hz
    classical
    choose p hp happ using fun i => hApprox.2 (b i) (hb i)
    let q : ℕ → Fin m → Op L := fun n i => (U n : Op L) * p i * star (U n : Op L)
    have hc (i : Fin m) : Tendsto (fun n => q n i) atTop (𝓝 (b i)) := by
      rw [tendsto_iff_dist_tendsto_zero]
      simpa only [PointwiseNormalizerApprox, q, dist_eq_norm_sub, norm_sub_rev] using happ i
    have hprod : Tendsto (fun n => ‖∑ i, q n i * z i‖) atTop
        (𝓝 ‖∑ i, b i * z i‖) :=
      (tendsto_finsetSum Finset.univ (fun i _ => (hc i).mul_const (z i))).norm
    have htensor : Tendsto (fun n => ‖∑ i, TensorProduct.mapL (q n i) (z i)‖) atTop
        (𝓝 ‖∑ i, TensorProduct.mapL (b i) (z i)‖) :=
      (tendsto_finsetSum Finset.univ (fun i _ =>
        (tensorMap_left_continuous (z i)).continuousAt.tendsto.comp (hc i))).norm
    have heq (n : ℕ) : ‖∑ i, q n i * z i‖ =
        ‖∑ i, TensorProduct.mapL (q n i) (z i)‖ := by
      have hqn : ∀ i, q n i ∈ conjAlg (U n) P := fun i => ⟨p i, hp i, rfl⟩
      exact (tensorIdentity_conjugate D P (U n) (hApprox.1 n) hP
        m hm (q n) z hqn hz).trans (tensorSumNorm_eq_opNorm (q n) z)
    rw [tensorSumNorm_eq_opNorm]
    exact tendsto_nhds_unique hprod (htensor.congr (fun n => (heq n).symm))

end Papers.OaiCloseSeparableCstar
