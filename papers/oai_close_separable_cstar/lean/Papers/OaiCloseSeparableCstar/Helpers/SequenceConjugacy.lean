module

public import Papers.OaiCloseSeparableCstar.Helpers.SequenceAlgebra
public import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-! # Coordinate projections and spatial conjugacy of sequence algebras -/

@[expose] public section

namespace Papers.OaiCloseSeparableCstar

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable (D P Q : StarSubalgebra ℂ (Op L))

-- @node: seqEntry_mem
/-- If [T belongs to the sequence algebra with entries in D and limit in P](hyp:hT),
[every coordinate entry of T belongs to D](goal). -/
lemma seqEntry_mem {T : Op (SumSpace L)} (hT : T ∈ seqAlg D P) (n : ℕ) :
    seqEntry n T ∈ D := by
  obtain ⟨x, hx, _, hd⟩ := hT
  rw [seqEntry_eq hd]
  exact hx n

-- @node: seqEntry_apply
/-- If [T belongs to the sequence algebra with entries in D and limit in P](hyp:hT),
[the n-th coordinate of T applied to any vector is the n-th entry of T applied to that vector's n-th coordinate](goal). -/
lemma seqEntry_apply {T : Op (SumSpace L)} (hT : T ∈ seqAlg D P)
    (v : SumSpace L) (n : ℕ) : (T v) n = seqEntry n T (v n) := by
  obtain ⟨x, _, _, hd⟩ := hT
  rw [hd, seqEntry_eq hd]

-- @node: seqCentral_entry_scalar
/-- Suppose [every central element of D is a scalar multiple of the identity](hyp:hcenter),
[T belongs to the sequence algebra with entries in D and limit in P](hyp:hT), and
[T commutes with every element of that sequence algebra](hyp:hc).
Then [each coordinate entry of T is a complex scalar multiple of the identity](goal). -/
lemma seqCentral_entry_scalar (hcenter : SequencesCenter D)
    {T : Op (SumSpace L)} (hT : T ∈ seqAlg D P)
    (hc : T ∈ commutant (seqAlg D P : Set (Op (SumSpace L)))) (n : ℕ) :
    ∃ c : ℂ, seqEntry n T = c • (1 : Op L) := by
  apply hcenter _ (seqEntry_mem D P hT n)
  intro a ha
  have he := hc (seqCornerOp n a) (seqCornerOp_mem D P n ha)
  ext v
  have h := congrArg (fun R : Op (SumSpace L) => (R (lp.single 2 n v)) n) he
  change (seqCornerOp n a (T (lp.single 2 n v))) n =
    (T (seqCornerOp n a (lp.single 2 n v))) n at h
  simpa only [seqCornerOp_apply, lp.single_apply_self,
    seqEntry_apply D P hT, ContinuousLinearMap.mul_apply] using h.symm

-- @node: seqProjection_central
/-- [The projection onto any single coordinate commutes with every element of the sequence algebra with entries in D and limit in P](goal). -/
lemma seqProjection_central (n : ℕ) :
    seqCornerOp (L := L) n 1 ∈ commutant (seqAlg D P : Set (Op (SumSpace L))) := by
  intro T hT
  ext v k
  change (T (seqCornerOp n 1 v)) k = (seqCornerOp n 1 (T v)) k
  rw [seqEntry_apply D P hT, seqCornerOp_apply, seqCornerOp_apply]
  by_cases hk : k = n
  · subst k; simp only [lp.single_apply_self, one_apply_eq_self, seqEntry_apply D P hT]
  · simp [lp.single_apply, hk]

-- @node: seqDiagonal_mul_corner
/-- If [T belongs to the sequence algebra with entries in D and limit in P](hyp:hT),
[multiplying T by an operator a supported on coordinate n gives the operator supported on n whose entry is the n-th entry of T times a](goal). -/
lemma seqDiagonal_mul_corner {T : Op (SumSpace L)} (hT : T ∈ seqAlg D P)
    (n : ℕ) (a : Op L) :
    T * seqCornerOp n a = seqCornerOp n (seqEntry n T * a) := by
  ext v k
  change (T (seqCornerOp n a v)) k = (seqCornerOp n (seqEntry n T * a) v) k
  rw [seqEntry_apply D P hT, seqCornerOp_apply, seqCornerOp_apply]
  by_cases hk : k = n
  · subst k; simp [lp.single_apply_self]
  · simp [lp.single_apply, hk]

-- @node: seqCornerOp_smul
/-- [Inserting a scalar multiple of an operator into coordinate n gives the same result as multiplying its coordinate insertion by that scalar](goal). -/
lemma seqCornerOp_smul (n : ℕ) (c : ℂ) (a : Op L) :
    seqCornerOp n (c • a) = c • seqCornerOp n a := by
  ext v k
  simp [seqCornerOp_apply, lp.single_apply]

-- @node: seqProjection_idempotent
/-- [The projection onto any single coordinate equals its own square](goal). -/
lemma seqProjection_idempotent (n : ℕ) :
    seqCornerOp (L := L) n 1 * seqCornerOp n 1 = seqCornerOp n 1 := by
  ext v k
  change (seqCornerOp n 1 (seqCornerOp n 1 v)) k = (seqCornerOp n 1 v) k
  simp only [seqCornerOp_apply, lp.single_apply_self, one_apply_eq_self]

-- @node: seqProjection_ne_zero
/-- When the underlying Hilbert space is nonzero,
[the projection onto any single coordinate is nonzero](goal). -/
lemma seqProjection_ne_zero [Nontrivial L] (n : ℕ) :
    seqCornerOp (L := L) n 1 ≠ 0 := by
  intro he
  have h : seqEntry (L := L) n (seqCornerOp n 1) = 0 := by rw [he]; rfl
  have hi : seqEntry (L := L) n (seqCornerOp n 1) = 1 := by
    ext v
    change (seqCornerOp n 1 (lp.single 2 n v)) n = v
    simp [seqCornerOp_apply]
  exact one_ne_zero (hi.symm.trans h)

-- @node: seqCentral_mul_projection
/-- Suppose [every central element of D is a scalar multiple of the identity](hyp:hcenter),
[T belongs to the sequence algebra with entries in D and limit in P](hyp:hT), and
[T commutes with that entire sequence algebra](hyp:hc).
Then [multiplying T by any coordinate projection gives a complex scalar multiple of that projection](goal). -/
lemma seqCentral_mul_projection (hcenter : SequencesCenter D)
    {T : Op (SumSpace L)} (hT : T ∈ seqAlg D P)
    (hc : T ∈ commutant (seqAlg D P : Set (Op (SumSpace L)))) (n : ℕ) :
    ∃ c : ℂ, T * seqCornerOp n 1 = c • seqCornerOp n 1 := by
  obtain ⟨c, he⟩ := seqCentral_entry_scalar D P hcenter hT hc n
  refine ⟨c, ?_⟩
  rw [seqDiagonal_mul_corner D P hT, he, mul_one, seqCornerOp_smul]

-- @node: seqCentral_idempotent_contains
/-- On a nonzero Hilbert space, suppose [every central element of D is scalar](hyp:hcenter),
[T belongs to the sequence algebra with entries in D and limit in P](hyp:hT),
[T commutes with that sequence algebra](hyp:hc), [T equals its square](hyp:hid), and
[T is nonzero](hyp:hne). Then [there is a coordinate projection that is unchanged by left multiplication by T](goal). -/
lemma seqCentral_idempotent_contains [Nontrivial L] (hcenter : SequencesCenter D)
    {T : Op (SumSpace L)} (hT : T ∈ seqAlg D P)
    (hc : T ∈ commutant (seqAlg D P : Set (Op (SumSpace L))))
    (hid : T * T = T) (hne : T ≠ 0) :
    ∃ n : ℕ, T * seqCornerOp n 1 = seqCornerOp n 1 := by
  have hex : ∃ n, seqEntry n T ≠ 0 := by
    by_contra! hz
    apply hne
    ext v n
    rw [seqEntry_apply D P hT, hz n]
    rfl
  obtain ⟨n, hn⟩ := hex
  obtain ⟨c, he⟩ := seqCentral_entry_scalar D P hcenter hT hc n
  have hc0 : c ≠ 0 := by
    intro hz
    apply hn
    simp only [he, hz, zero_smul]
  have hm : T * seqCornerOp n 1 = c • seqCornerOp n 1 := by
    rw [seqDiagonal_mul_corner D P hT, he, mul_one, seqCornerOp_smul]
  have hh := congrArg (fun A : Op (SumSpace L) => A * seqCornerOp n 1) hid
  rw [mul_assoc, hm, mul_smul_comm, hm, smul_smul] at hh
  have hcc : c * c = c := smul_left_injective ℂ (seqProjection_ne_zero (L := L) n) hh
  have hc1 : c = 1 := mul_left_cancel₀ hc0 (by simpa using hcc)
  exact ⟨n, by simpa only [hc1, one_smul] using hm⟩

-- @node: seqIso_central
/-- If [the star algebra automorphism e carries membership in the sequence algebra with limit in P exactly to membership in the one with limit in Q](hyp:he),
and [T commutes with the sequence algebra with limit in P](hyp:hc),
then [e applied to T commutes with the sequence algebra with limit in Q](goal). -/
lemma seqIso_central (e : Op (SumSpace L) ≃⋆ₐ[ℂ] Op (SumSpace L))
    (he : ∀ T, T ∈ seqAlg D P ↔ e T ∈ seqAlg D Q)
    {T : Op (SumSpace L)}
    (hc : T ∈ commutant (seqAlg D P : Set (Op (SumSpace L)))) :
    e T ∈ commutant (seqAlg D Q : Set (Op (SumSpace L))) := by
  intro A hA
  have h := hc (e.symm A) ((he _).mpr (by simpa using hA))
  have hh := congrArg e h
  simpa only [map_mul, e.apply_symm_apply] using hh

-- @node: seqIso_projection
/-- On a nonzero Hilbert space, suppose [every central element of D is scalar](hyp:hcenter)
and [the star algebra automorphism e carries membership in the sequence algebra with entries in D and limit in P exactly to membership in the one with limit in Q](hyp:he).
Then [e sends the projection onto coordinate n to the projection onto some coordinate m](goal). -/
lemma seqIso_projection [Nontrivial L] (hcenter : SequencesCenter D)
    (e : Op (SumSpace L) ≃⋆ₐ[ℂ] Op (SumSpace L))
    (he : ∀ T, T ∈ seqAlg D P ↔ e T ∈ seqAlg D Q) (n : ℕ) :
    ∃ m : ℕ, e (seqCornerOp n 1) = seqCornerOp m 1 := by
  have hE := seqCornerOp_mem D P n D.one_mem
  have hEc := seqProjection_central D P n
  have hR : e (seqCornerOp n 1) ∈ seqAlg D Q := (he _).mp hE
  have hRc := seqIso_central D P Q e he hEc
  have hRi : e (seqCornerOp n 1) * e (seqCornerOp n 1) = e (seqCornerOp n 1) := by
    rw [← map_mul, seqProjection_idempotent]
  have hRn : e (seqCornerOp n 1) ≠ 0 := by
    intro h
    exact seqProjection_ne_zero (L := L) n (e.injective (h.trans (map_zero e).symm))
  obtain ⟨m, hm⟩ := seqCentral_idempotent_contains D Q hcenter hR hRc hRi hRn
  have hei : ∀ T, T ∈ seqAlg D Q ↔ e.symm T ∈ seqAlg D P := by
    intro T
    simpa using (he (e.symm T)).symm
  have hF : e.symm (seqCornerOp m 1) ∈ seqAlg D P :=
    (hei _).mp (seqCornerOp_mem D Q m D.one_mem)
  have hFc := seqIso_central D Q P e.symm hei (seqProjection_central D Q m)
  obtain ⟨c, hc⟩ := seqCentral_mul_projection D P hcenter hF hFc n
  have hcm := congrArg e hc
  simp only [map_mul, e.apply_symm_apply, map_smul] at hcm
  have hcomm := hRc (seqCornerOp m 1) (seqCornerOp_mem D Q m D.one_mem)
  rw [hcomm] at hcm
  rw [hm] at hcm
  have heq : seqCornerOp m 1 = c • e (seqCornerOp n 1) := hcm
  have hc1 : c = 1 := by
    have h := congrArg (fun A : Op (SumSpace L) => A * seqCornerOp m 1) heq
    rw [seqProjection_idempotent, smul_mul_assoc, hm] at h
    exact (smul_left_injective ℂ (seqProjection_ne_zero (L := L) m)
      (h.symm.trans (one_smul ℂ _).symm))
  exact ⟨m, by simpa only [hc1, one_smul] using heq.symm⟩

-- @node: seqBlock
/-- For [an output coordinate m](hyp:m), [an input coordinate n](hyp:n), and
[a bounded operator S on the square-summable sequences](hyp:S) over [the Hilbert space L](hyp:L),
[the coordinate block of S from n to m](goal) sends a vector to the m-th coordinate
of S applied to the sequence supported at n with that vector as its value. -/
noncomputable def seqBlock (m n : ℕ) (S : Op (SumSpace L)) : Op L :=
  (lp.evalCLM ℂ (fun _ : ℕ => L) 2 m).comp
    (S.comp (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => L) 2 n))

-- @node: seqBlock_single
/-- If [S times the projection onto n equals the projection onto m times S](hyp:h),
then [S sends a vector supported at n to the vector supported at m obtained by applying the coordinate block of S from n to m](goal). -/
lemma seqBlock_single {S : Op (SumSpace L)} {m n : ℕ}
    (h : S * seqCornerOp n 1 = seqCornerOp m 1 * S) (v : L) :
    S (lp.single 2 n v) = lp.single 2 m (seqBlock m n S v) := by
  have he := congrArg (fun A : Op (SumSpace L) => A (lp.single 2 n v)) h
  change S (seqCornerOp n 1 (lp.single 2 n v)) =
    seqCornerOp m 1 (S (lp.single 2 n v)) at he
  simpa [seqCornerOp_apply, seqBlock, lp.evalCLM] using he

-- @node: seqUnitary_intertwine
/-- If [conjugation by the unitary S sends the projection onto n to the projection onto m](hyp:h),
then [S times the projection onto n equals the projection onto m times S](goal). -/
lemma seqUnitary_intertwine (S : unitary (Op (SumSpace L))) {m n : ℕ}
    (h : (S : Op (SumSpace L)) * seqCornerOp n 1 * star (S : Op (SumSpace L)) =
      seqCornerOp m 1) :
    (S : Op (SumSpace L)) * seqCornerOp n 1 = seqCornerOp m 1 * (S : Op (SumSpace L)) := by
  have he := congrArg (fun A : Op (SumSpace L) => A * (S : Op (SumSpace L))) h
  simpa only [mul_assoc, Unitary.coe_star_mul_self, mul_one] using he

-- @node: seqUnitary_inverse_intertwine
/-- If [the unitary S times the projection onto n equals the projection onto m times S](hyp:h),
then [the adjoint of S times the projection onto m equals the projection onto n times the adjoint of S](goal). -/
lemma seqUnitary_inverse_intertwine (S : unitary (Op (SumSpace L))) {m n : ℕ}
    (h : (S : Op (SumSpace L)) * seqCornerOp n 1 = seqCornerOp m 1 * (S : Op (SumSpace L))) :
    star (S : Op (SumSpace L)) * seqCornerOp m 1 = seqCornerOp n 1 * star (S : Op (SumSpace L)) := by
  have he := congrArg (fun A : Op (SumSpace L) =>
    star (S : Op (SumSpace L)) * A * star (S : Op (SumSpace L))) h
  simpa only [mul_assoc, ← mul_assoc (star (S : Op (SumSpace L))) (S : Op (SumSpace L)),
    Unitary.coe_star_mul_self, one_mul, Unitary.mul_star_self_of_mem S.property, mul_one] using he.symm

-- @node: seqBlock_inverse_mul
/-- If [the unitary S times the projection onto n equals the projection onto m times S](hyp:h),
then [the block of the adjoint of S from m to n, multiplied by the block of S from n to m, is the identity](goal). -/
lemma seqBlock_inverse_mul (S : unitary (Op (SumSpace L))) {m n : ℕ}
    (h : (S : Op (SumSpace L)) * seqCornerOp n 1 = seqCornerOp m 1 * (S : Op (SumSpace L))) :
    seqBlock n m (star (S : Op (SumSpace L))) * seqBlock m n (S : Op (SumSpace L)) = 1 := by
  ext v
  have he := congrArg (fun A : Op (SumSpace L) => (A (lp.single 2 n v)) n)
    (Unitary.coe_star_mul_self S)
  simp only [mul_apply_eq_comp, one_apply_eq_self, lp.single_apply_self] at he
  rw [seqBlock_single h, seqBlock_single (seqUnitary_inverse_intertwine S h),
    lp.single_apply_self] at he
  exact he

-- @node: seqBlock_mem_unitary
/-- If [the unitary S times the projection onto n equals the projection onto m times S](hyp:h),
then [the block of S from n to m is a unitary operator on the underlying Hilbert space](goal). -/
lemma seqBlock_mem_unitary (S : unitary (Op (SumSpace L))) {m n : ℕ}
    (h : (S : Op (SumSpace L)) * seqCornerOp n 1 = seqCornerOp m 1 * (S : Op (SumSpace L))) :
    seqBlock m n (S : Op (SumSpace L)) ∈ unitary (Op L) := by
  have hi := seqUnitary_inverse_intertwine S h
  let A := seqBlock m n (S : Op (SumSpace L))
  let B := seqBlock n m (star (S : Op (SumSpace L)))
  have hBA : B * A = 1 := seqBlock_inverse_mul S h
  have hAB : A * B = 1 := by
    simpa only [Unitary.coe_star, star_star] using seqBlock_inverse_mul (star S) hi
  let u : (Op L)ˣ := ⟨A, B, hAB, hBA⟩
  apply IsUnit.mem_unitary_of_star_mul_self (show IsUnit A from ⟨u, rfl⟩)
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply A.norm_map_iff_adjoint_comp_self.mp
  intro v
  have hn := S.val.norm_map_of_mem_unitary S.property (lp.single 2 n v)
  rw [seqBlock_single h, lp.norm_single (by norm_num), lp.norm_single (by norm_num)] at hn
  exact hn

-- @node: seqBlock_star_eq
/-- If [the unitary S times the projection onto n equals the projection onto m times S](hyp:h),
then [the block of the adjoint of S from m to n equals the adjoint of the block of S from n to m](goal). -/
lemma seqBlock_star_eq (S : unitary (Op (SumSpace L))) {m n : ℕ}
    (h : (S : Op (SumSpace L)) * seqCornerOp n 1 = seqCornerOp m 1 * (S : Op (SumSpace L))) :
    seqBlock n m (star (S : Op (SumSpace L))) = star (seqBlock m n (S : Op (SumSpace L))) := by
  have hu := seqBlock_mem_unitary S h
  calc
    _ = seqBlock n m (star (S : Op (SumSpace L))) *
        (seqBlock m n (S : Op (SumSpace L)) * star (seqBlock m n (S : Op (SumSpace L)))) := by
      rw [Unitary.mul_star_self_of_mem hu, mul_one]
    _ = _ := by rw [← mul_assoc, seqBlock_inverse_mul S h, one_mul]

-- @node: seqBlock_conj_entry
/-- Suppose [the unitary S times the projection onto n equals the projection onto m times S](hyp:h)
and [T belongs to the sequence algebra with entries in D and limit in P](hyp:hT).
Then [the m-th entry of T conjugated by S is the n-th entry of T conjugated by the block of S from n to m](goal). -/
lemma seqBlock_conj_entry (S : unitary (Op (SumSpace L))) {m n : ℕ}
    (h : (S : Op (SumSpace L)) * seqCornerOp n 1 = seqCornerOp m 1 * (S : Op (SumSpace L)))
    {T : Op (SumSpace L)} (hT : T ∈ seqAlg D P) :
    seqEntry m ((S : Op (SumSpace L)) * T * star (S : Op (SumSpace L))) =
      seqBlock m n (S : Op (SumSpace L)) * seqEntry n T *
        star (seqBlock m n (S : Op (SumSpace L))) := by
  ext v
  change ((S : Op (SumSpace L)) (T (star (S : Op (SumSpace L)) (lp.single 2 m v)))) m = _
  rw [seqBlock_single (seqUnitary_inverse_intertwine S h)]
  have ht : ∀ w : L, T (lp.single 2 n w) = lp.single 2 n (seqEntry n T w) := by
    intro w
    ext k
    rw [seqEntry_apply D P hT]
    by_cases hk : k = n
    · subst k; simp
    · simp [lp.single_apply, hk]
  rw [ht, seqBlock_single h, lp.single_apply_self, seqBlock_star_eq S h]
  rfl

-- @node: seqEntry_corner_self
/-- [The n-th coordinate entry of the operator obtained by inserting a into coordinate n is a itself](goal). -/
lemma seqEntry_corner_self (n : ℕ) (a : Op L) : seqEntry n (seqCornerOp n a) = a := by
  ext v
  change (seqCornerOp n a (lp.single 2 n v)) n = a v
  simp [seqCornerOp_apply]

-- @node: seqBlock_normalizes
/-- Suppose [conjugation by the unitary S carries membership in the sequence algebra with entries in D and limit in P exactly to membership in the one with limit in Q](hyp:he)
and [S times the projection onto n equals the projection onto m times S](hyp:h).
Then [conjugation by the block of S from n to m maps D onto itself](goal). -/
lemma seqBlock_normalizes (S : unitary (Op (SumSpace L)))
    (he : ∀ T, T ∈ seqAlg D P ↔
      (S : Op (SumSpace L)) * T * star (S : Op (SumSpace L)) ∈ seqAlg D Q)
    {m n : ℕ}
    (h : (S : Op (SumSpace L)) * seqCornerOp n 1 = seqCornerOp m 1 * (S : Op (SumSpace L))) :
    conjSet (seqBlock m n (S : Op (SumSpace L))) D = (D : Set _) := by
  let A := seqBlock m n (S : Op (SumSpace L))
  have hu : A ∈ unitary (Op L) := seqBlock_mem_unitary S h
  have hf : ∀ a ∈ D, A * a * star A ∈ D := by
    intro a ha
    have ht := seqCornerOp_mem D P n ha
    have hc := seqEntry_mem D Q ((he _).mp ht) m
    rw [seqBlock_conj_entry D P S h ht, seqEntry_corner_self] at hc
    exact hc
  have hei : ∀ T, T ∈ seqAlg D Q ↔
      star (S : Op (SumSpace L)) * T * (S : Op (SumSpace L)) ∈ seqAlg D P := by
    intro T
    have hh := he (star (S : Op (SumSpace L)) * T * (S : Op (SumSpace L)))
    simpa only [mul_assoc, ← mul_assoc (S : Op (SumSpace L)) (star (S : Op (SumSpace L))),
      Unitary.mul_star_self_of_mem S.property, one_mul, mul_one] using hh.symm
  have hb : ∀ b ∈ D, star A * b * A ∈ D := by
    intro b hb
    have ht := seqCornerOp_mem D Q m hb
    have hc := seqEntry_mem D P ((hei _).mp ht) n
    have hh := seqBlock_conj_entry D Q (star S) (seqUnitary_inverse_intertwine S h) ht
    simp only [Unitary.coe_star, star_star, seqBlock_star_eq S h] at hh
    rw [hh, seqEntry_corner_self] at hc
    exact hc
  apply Set.Subset.antisymm
  · rintro _ ⟨a, ha, rfl⟩
    exact hf a ha
  · intro b hbD
    refine ⟨star A * b * A, hb b hbD, ?_⟩
    change A * (star A * b * A) * star A = b
    simp only [mul_assoc, ← mul_assoc A (star A),
      Unitary.mul_star_self_of_mem hu, one_mul, mul_one]

-- @node: seqAlg_conjugacy_normalizers
/-- On a nonzero Hilbert space, suppose [every central element of D is scalar](hyp:hcenter),
[Q is contained in D](hyp:hQD), and [the sequence algebras with entries in D and limits in P and Q are unitarily conjugate](hyp:hconj).
Then [there is one sequence of unitaries, each conjugating D onto itself, such that every element b of Q has a fixed approximant p in P whose conjugates along this sequence converge to b in operator norm](goal). -/
lemma seqAlg_conjugacy_normalizers [Nontrivial L] (hcenter : SequencesCenter D)
    (hQD : Q ≤ D) (hconj : SequencesConjugacy D P Q) :
    ∃ U : ℕ → unitary (Op L),
      (∀ n, conjSet (U n : Op L) D = (D : Set _)) ∧
      ∀ b ∈ Q, ∃ p ∈ P, PointwiseNormalizerApprox b U p := by
  classical
  obtain ⟨s, hs, hS⟩ := hconj
  let S : unitary (Op (SumSpace L)) := ⟨s, hs⟩
  let e := Unitary.conjStarAlgAut ℂ (Op (SumSpace L)) S
  have he : ∀ T, T ∈ seqAlg D P ↔ e T ∈ seqAlg D Q := by
    intro T
    change T ∈ (seqAlg D P : Set _) ↔ e T ∈ (seqAlg D Q : Set _)
    rw [← hS]
    constructor
    · intro hT
      exact ⟨T, hT, rfl⟩
    · rintro ⟨R, hR, hRT⟩
      have hr : e R = e T := hRT
      exact e.injective hr ▸ hR
  choose m hm using seqIso_projection D P Q hcenter e he
  have hi (n : ℕ) : (S : Op (SumSpace L)) * seqCornerOp n 1 =
      seqCornerOp (m n) 1 * (S : Op (SumSpace L)) :=
    seqUnitary_intertwine S (hm n)
  let U : ℕ → unitary (Op L) := fun n =>
    ⟨seqBlock (m n) n (S : Op (SumSpace L)), seqBlock_mem_unitary S (hi n)⟩
  refine ⟨U, ?_, ?_⟩
  · intro n
    exact seqBlock_normalizes D P Q S he (hi n)
  · intro b hb
    let B : Op (SumSpace L) := constantDiagOp (I := ℕ) b
    let T : Op (SumSpace L) := star (S : Op (SumSpace L)) * B * (S : Op (SumSpace L))
    have hBT : (S : Op (SumSpace L)) * T * star (S : Op (SumSpace L)) = B := by
      dsimp [T]
      simp only [mul_assoc, ← mul_assoc (S : Op (SumSpace L)) (star (S : Op (SumSpace L))),
        Unitary.mul_star_self_of_mem S.property, one_mul, mul_one]
    have hB : B ∈ seqAlg D Q :=
      ⟨fun _ => b, fun _ => hQD hb, ⟨b, hb, tendsto_const_nhds⟩, fun _ _ => rfl⟩
    have hT : T ∈ seqAlg D P := (he T).mpr (by
      change (S : Op (SumSpace L)) * T * star (S : Op (SumSpace L)) ∈ seqAlg D Q
      rw [hBT]
      exact hB)
    have hTcopy := hT
    obtain ⟨x, hx, ⟨p, hp, hxp⟩, hdiag⟩ := hTcopy
    have hl : Filter.Tendsto (fun n => seqEntry n T) Filter.atTop (nhds p) := by
      simpa only [seqEntry_eq hdiag] using hxp
    have hbentry (n : ℕ) : b = (U n : Op L) * seqEntry n T * star (U n : Op L) := by
      have hh := seqBlock_conj_entry D P S (hi n) hT
      rw [hBT] at hh
      have hbe : seqEntry (m n) B = b := seqEntry_eq (x := fun _ => b) (fun _ _ => rfl) _
      rw [hbe] at hh
      exact hh
    refine ⟨p, hp, ?_⟩
    have hn := (hl.sub_const p).norm
    simp only [sub_self, norm_zero] at hn
    apply hn.congr
    intro n
    change ‖seqEntry n T - p‖ = ‖b - (U n : Op L) * p * star (U n : Op L)‖
    rw [hbentry n, ← sub_mul, ← mul_sub]
    rw [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]

end Papers.OaiCloseSeparableCstar
