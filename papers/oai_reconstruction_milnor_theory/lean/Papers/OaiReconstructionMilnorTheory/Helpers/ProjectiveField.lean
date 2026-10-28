module

public import Papers.OaiReconstructionMilnorTheory.Helpers.ProjectiveFrame

/-! # The field operations recovered from a normalized projective frame

Lines of slope `a` recover multiplication. Parallel translates of the diagonal
recover addition. These arguments use only the common affine coordinate bijection.
-/

public section

namespace Papers.OaiReconstructionMilnorTheory

variable {H C E E' : Type*} [Field H] [Field C]
  [AddCommGroup E] [Module H E] [AddCommGroup E'] [Module C E']

/-- Suppose [ψ is a bijection preserving projective lines](hyp:hψ), [u, v, and w
are nonzero source vectors](hyp:hu,hv,hw), and [u′, v′, and w′ are nonzero target
vectors](hyp:hu',hv',hw'). If [ψ maps the point of u to the point of u′](hyp:hpu),
[the point of v to the point of v′](hyp:hpv), and [the point of w to the point of
w′](hyp:hpw), and [w lies in the span of u and v](hyp:hmem), then [w′ lies in the
span of u′ and v′](goal). -/
-- @node: collineation_mem_span_pair
lemma collineation_mem_span_pair
    {ψ : Projectivization H E → Projectivization C E'}
    (hψ : ProjectiveLiftBijection ψ)
    {u v w : E} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    {u' v' w' : E'} (hu' : u' ≠ 0) (hv' : v' ≠ 0) (hw' : w' ≠ 0)
    (hpu : ψ (Projectivization.mk H u hu) = Projectivization.mk C u' hu')
    (hpv : ψ (Projectivization.mk H v hv) = Projectivization.mk C v' hv')
    (hpw : ψ (Projectivization.mk H w hw) = Projectivization.mk C w' hw')
    (hmem : w ∈ Submodule.span H {u, v}) :
    w' ∈ Submodule.span C {u', v'} := by
  have him : collineationSubmoduleEquiv hψ (Submodule.span H {u, v}) =
      Submodule.span C {u', v'} := by
    rw [show Submodule.span H {u, v} =
      (Projectivization.mk H u hu).submodule ⊔
        (Projectivization.mk H v hv).submodule by
          simp only [Projectivization.submodule_mk,
            ← Submodule.span_union, Set.singleton_union]]
    rw [map_sup, collineationSubmoduleEquiv_point,
      collineationSubmoduleEquiv_point, hpu, hpv]
    simp only [Projectivization.submodule_mk,
      ← Submodule.span_union, Set.singleton_union]
  apply (projective_mk_mem_points _ _ hw').mp
  rw [← hpw, ← him]
  exact (collineation_point_mem_iff hψ _ _).mpr
    ((projective_mk_mem_points _ _ hw).mpr hmem)

section Coordinates

variable {ψ : Projectivization H E → Projectivization C E'}
  (hψ : ProjectiveLiftBijection ψ) {ι : Type*}
  (b : Module.Basis ι H E) (b' : Module.Basis ι C E')
  (hp : ∀ k, ψ (Projectivization.mk H (b k) (b.ne_zero k)) =
    Projectivization.mk C (b' k) (b'.ne_zero k))
  {o i j : ι} (hoi : o ≠ i) (hoj : o ≠ j) (hij : i ≠ j)
  (τ : H ≃ C) (ht0 : τ 0 = 0) (ht1 : τ 1 = 1)
  (hti : ∀ a, ψ (projectiveAxis (projective_basis_pair b hoi) a) =
    projectiveAxis (projective_basis_pair b' hoi) (τ a))
  (htj : ∀ a, ψ (projectiveAxis (projective_basis_pair b hoj) a) =
    projectiveAxis (projective_basis_pair b' hoj) (τ a))

include hψ hp hoi hoj hij ht1 hti htj

/-- Suppose ψ is a bijection preserving projective lines that matches
corresponding source and target basis points, with o distinct from
i, o distinct from j, and i distinct from j.
If the scalar bijection τ fixes one and describes the action of ψ on
affine coordinates on the o–i axis and on the o–j axis, then
[τ maps the product of any scalars a and t to the product of their images](goal). -/
-- @node: projective_coordinates_mul
lemma projective_coordinates_mul (a t : H) : τ (a * t) = τ a * τ t := by
  classical
  let v : H → E := fun s => b o + s • b i + (a * s) • b j
  have hvo (s : H) : b.repr (v s) o = 1 := by
    simp [v, Module.Basis.repr_self, hoi, hoj]
  have hv (s : H) : v s ≠ 0 := by
    intro hz
    have h := hvo s
    rw [hz] at h
    simp at h
  obtain ⟨w₁, hw₁, hw₁o, hp₁⟩ := projective_frame_affine_representative hψ b b' hp
    o (v 1) (hv 1) (by rw [hvo]; exact one_ne_zero)
  obtain ⟨w, hw, hwo, hpw⟩ := projective_frame_affine_representative hψ b b' hp
    o (v t) (hv t) (by rw [hvo]; exact one_ne_zero)
  have hc₁ := projective_two_axis_coordinates hψ b b' hp hoi hoj hij
    τ τ hti htj 1 (a * 1) (hv 1) rfl hw₁ hw₁o hp₁
  have hc := projective_two_axis_coordinates hψ b b' hp hoi hoj hij
    τ τ hti htj t (a * t) (hv t) rfl hw hwo hpw
  have hmem : w ∈ Submodule.span C {b' o, w₁} := by
    apply collineation_mem_span_pair hψ (b.ne_zero o) (hv 1) (hv t)
      (b'.ne_zero o) hw₁ hw (hp o) hp₁ hpw
    apply Submodule.mem_span_pair.mpr
    refine ⟨1 - t, t, ?_⟩
    simp only [v, mul_one, smul_add, smul_smul, sub_smul, one_smul]
    rw [mul_comm t a]
    abel
  obtain ⟨s, r, hsr⟩ := Submodule.mem_span_pair.mp hmem
  have hi := congrArg (fun z => b'.repr z i) hsr
  have hj := congrArg (fun z => b'.repr z j) hsr
  have hr : r = τ t := by
    simpa [Module.Basis.repr_self, hoi.symm, hc₁.1, ht1, hc.1] using hi
  have hm : r * τ a = τ (a * t) := by
    simpa [Module.Basis.repr_self, hoj.symm, hc₁.2, hc.2] using hj
  rw [← hm, hr, mul_comm]

include ht1

/-- Suppose ψ is a bijection preserving projective lines that matches
corresponding source and target basis points, with o distinct from
i, o distinct from j, and i distinct from j.
If the scalar bijection τ fixes one, describes the action of ψ on
affine coordinates on the o–i axis and on the o–j axis, and
[the sum of the i-th and j-th source basis vectors is nonzero](hyp:hd), then
[the chosen representative of the image of its projective point has zero
o-coordinate and equal i- and j-coordinates in the target basis](goal). -/
-- @node: projective_diagonal_direction_coordinates
lemma projective_diagonal_direction_coordinates
    (hd : b i + b j ≠ 0) :
    let d' := (ψ (Projectivization.mk H (b i + b j) hd)).rep
    b'.repr d' o = 0 ∧ b'.repr d' i = b'.repr d' j := by
  classical
  intro d'
  have hdo : b.repr (b i + b j) o = 0 := by
    simp [Module.Basis.repr_self, hoi, hoj]
  have hdo' : b'.repr d' o = 0 := by
    apply (projective_frame_hyperplane_mem b' o d').mp
    have him := collineation_frame_span_image hψ b b' hp {k | o ≠ k}
    have hmem := (collineation_point_mem_iff hψ
      (Submodule.span H (Set.range fun k : {k : ι // o ≠ k} => b k))
      (Projectivization.mk H (b i + b j) hd)).mpr
        ((projective_mk_mem_points _ _ hd).mpr
          ((projective_frame_hyperplane_mem b o _).mpr hdo))
    have him' : collineationSubmoduleEquiv hψ
        (Submodule.span H (Set.range fun k : {k : ι // o ≠ k} => b k)) =
        Submodule.span C (Set.range fun k : {k : ι // o ≠ k} => b' k) := him
    rw [him'] at hmem
    exact hmem (by
      rw [Projectivization.submodule_eq]
      exact Submodule.mem_span_singleton_self _)
  let v := b o + (1 : H) • b i + (1 : H) • b j
  have hvo : b.repr v o = 1 := by
    simp [v, Module.Basis.repr_self, hoi, hoj]
  have hv : v ≠ 0 := by
    intro hz
    rw [hz] at hvo
    simp at hvo
  obtain ⟨w, hw, hwo, hpw⟩ := projective_frame_affine_representative hψ b b' hp
    o v hv (by rw [hvo]; exact one_ne_zero)
  have hc := projective_two_axis_coordinates hψ b b' hp hoi hoj hij
    τ τ hti htj 1 1 hv rfl hw hwo hpw
  have hmem : d' ∈ Submodule.span C {b' o, w} := by
    apply collineation_mem_span_pair hψ (b.ne_zero o) hv hd
      (b'.ne_zero o) hw (Projectivization.rep_nonzero _) (hp o) hpw
      (Projectivization.mk_rep _).symm
    apply Submodule.mem_span_pair.mpr
    exact ⟨-1, 1, by simp [v]; abel⟩
  obtain ⟨s, r, hsr⟩ := Submodule.mem_span_pair.mp hmem
  have hi := congrArg (fun z => b'.repr z i) hsr
  have hj := congrArg (fun z => b'.repr z j) hsr
  have hi' : r = b'.repr d' i := by
    simpa [Module.Basis.repr_self, hoi.symm, hc.1, ht1] using hi
  have hj' : r = b'.repr d' j := by
    simpa [Module.Basis.repr_self, hoj.symm, hc.2, ht1] using hj
  exact ⟨hdo', hi'.symm.trans hj'⟩

include ht0

/-- Suppose ψ is a bijection preserving projective lines that matches
corresponding source and target basis points, with o distinct from
i, o distinct from j, and i distinct from j.
If the scalar bijection τ fixes zero and one and describes
the action of ψ on affine coordinates on the o–i axis and on the o–j
axis, then [τ maps the sum of any scalars t and a to the sum of their
images](goal). -/
-- @node: projective_coordinates_add
lemma projective_coordinates_add (t a : H) : τ (t + a) = τ t + τ a := by
  classical
  let v : H → E := fun s => b o + s • b i + (s + a) • b j
  have hvo (s : H) : b.repr (v s) o = 1 := by
    simp [v, Module.Basis.repr_self, hoi, hoj]
  have hv (s : H) : v s ≠ 0 := by
    intro hz
    have h := hvo s
    rw [hz] at h
    simp at h
  have hd : b i + b j ≠ 0 := by
    intro hz
    have hi := congrArg (fun z => b.repr z i) hz
    simp [Module.Basis.repr_self, hij.symm] at hi
  let d' := (ψ (Projectivization.mk H (b i + b j) hd)).rep
  have hd' : d' ≠ 0 := Projectivization.rep_nonzero _
  have hdc := projective_diagonal_direction_coordinates hψ b b' hp hoi hoj hij
    τ ht1 hti htj hd
  change b'.repr d' o = 0 ∧ b'.repr d' i = b'.repr d' j at hdc
  obtain ⟨w₀, hw₀, hw₀o, hp₀⟩ := projective_frame_affine_representative hψ b b' hp
    o (v 0) (hv 0) (by rw [hvo]; exact one_ne_zero)
  obtain ⟨w, hw, hwo, hpw⟩ := projective_frame_affine_representative hψ b b' hp
    o (v t) (hv t) (by rw [hvo]; exact one_ne_zero)
  have hc₀ := projective_two_axis_coordinates hψ b b' hp hoi hoj hij
    τ τ hti htj 0 (0 + a) (hv 0) rfl hw₀ hw₀o hp₀
  have hc := projective_two_axis_coordinates hψ b b' hp hoi hoj hij
    τ τ hti htj t (t + a) (hv t) rfl hw hwo hpw
  have hmem : w ∈ Submodule.span C {w₀, d'} := by
    apply collineation_mem_span_pair hψ (hv 0) hd (hv t) hw₀ hd' hw
      hp₀ (Projectivization.mk_rep _).symm hpw
    apply Submodule.mem_span_pair.mpr
    refine ⟨1, t, ?_⟩
    simp only [v, zero_smul, add_zero, zero_add, one_smul, smul_add, add_smul]
    abel
  obtain ⟨s, r, hsr⟩ := Submodule.mem_span_pair.mp hmem
  have ho := congrArg (fun z => b'.repr z o) hsr
  have hs : s = 1 := by simpa [hw₀o, hdc.1, hwo] using ho
  have hi := congrArg (fun z => b'.repr z i) hsr
  have hj := congrArg (fun z => b'.repr z j) hsr
  have hi' : r * b'.repr d' i = τ t := by
    simpa [hc₀.1, ht0, hc.1] using hi
  have hj' : τ a + r * b'.repr d' j = τ (t + a) := by
    simpa [hs, hc₀.2, hc.2] using hj
  rw [← hj', ← hdc.2, hi', add_comm]

end Coordinates

/-- Suppose [ψ is a bijection preserving projective lines](hyp:hψ), and the
source basis has indices [o distinct from i](hyp:hoi), [o distinct from j](hyp:hoj),
and [i distinct from j](hyp:hij). Then [there exist a target basis and a field
isomorphism σ such that ψ matches corresponding basis points and transforms
affine coordinates on every axis through o by σ](goal). -/
-- @node: projective_frame_field_equiv
lemma projective_frame_field_equiv
    {ψ : Projectivization H E → Projectivization C E'}
    (hψ : ProjectiveLiftBijection ψ) {ι : Type*}
    (b : Module.Basis ι H E) (o i j : ι)
    (hoi : o ≠ i) (hoj : o ≠ j) (hij : i ≠ j) :
    ∃ b' : Module.Basis ι C E', ∃ σ : H ≃+* C,
      (∀ k, ψ (Projectivization.mk H (b k) (b.ne_zero k)) =
        Projectivization.mk C (b' k) (b'.ne_zero k)) ∧
      ∀ k (hok : o ≠ k) a,
        ψ (projectiveAxis (projective_basis_pair b hok) a) =
          projectiveAxis (projective_basis_pair b' hok) (σ a) := by
  obtain ⟨b', τ, ht0, ht1, _, hp, ht⟩ := projective_common_frame_coordinates hψ b o i hoi
  let σ : H ≃+* C :=
    { τ with
      map_add' := projective_coordinates_add hψ b b' hp hoi hoj hij τ ht0 ht1
        (ht i hoi) (ht j hoj)
      map_mul' := projective_coordinates_mul hψ b b' hp hoi hoj hij τ ht1
        (ht i hoi) (ht j hoj) }
  exact ⟨b', σ, hp, ht⟩

end Papers.OaiReconstructionMilnorTheory
