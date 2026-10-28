module

public import Papers.OaiReconstructionMilnorTheory.Helpers.ProjectiveAffine

/-! # Assembling the semilinear projective lift

Apply the recovered field isomorphism to basis coordinates. Affine coordinate
fibers identify the induced map on finite points; directions of affine lines
identify its action on the hyperplane at infinity.
-/

@[expose] public section

namespace Papers.OaiReconstructionMilnorTheory

variable {H C E E' : Type*} [Field H] [Field C]
  [AddCommGroup E] [Module H E] [AddCommGroup E'] [Module C E']

/-- Given [a source basis b](hyp:b), [a target basis b′ with the same index
set](hyp:b'), and [a field isomorphism σ between their scalar fields](hyp:σ),
[the coordinate lift](goal) is the additive bijection obtained by applying σ to
every source coordinate and reconstructing the vector in the target basis. -/
-- @node: projectiveFrameLift
noncomputable def projectiveFrameLift {ι : Type*}
    (b : Module.Basis ι H E) (b' : Module.Basis ι C E') (σ : H ≃+* C) : E ≃+ E' :=
  b.repr.toAddEquiv.trans
    ((Finsupp.mapRange.addEquiv σ.toAddEquiv).trans b'.repr.symm.toAddEquiv)

/-- [The i-coordinate of the coordinate lift of v in the target basis is σ applied
to the i-coordinate of v in the source basis](goal). -/
-- @node: projectiveFrameLift_coordinate
@[simp] lemma projectiveFrameLift_coordinate {ι : Type*}
    (b : Module.Basis ι H E) (b' : Module.Basis ι C E') (σ : H ≃+* C) (v : E) (i : ι) :
    b'.repr (projectiveFrameLift b b' σ v) i = σ (b.repr v i) := by
  simp [projectiveFrameLift]

/-- [The coordinate lift sends the source basis vector indexed by i to the target
basis vector indexed by i](goal). -/
-- @node: projectiveFrameLift_basis
@[simp] lemma projectiveFrameLift_basis {ι : Type*}
    (b : Module.Basis ι H E) (b' : Module.Basis ι C E') (σ : H ≃+* C) (i : ι) :
    projectiveFrameLift b b' σ (b i) = b' i := by
  classical
  apply b'.repr.injective
  ext j
  simp [Module.Basis.repr_self, Finsupp.single_apply]

/-- [Lifting a times v gives σ of a times the lift of v](goal). -/
-- @node: projectiveFrameLift_smul
lemma projectiveFrameLift_smul {ι : Type*}
    (b : Module.Basis ι H E) (b' : Module.Basis ι C E') (σ : H ≃+* C) (a : H) (v : E) :
    projectiveFrameLift b b' σ (a • v) = σ a • projectiveFrameLift b b' σ v := by
  apply b'.repr.injective
  ext i
  simp

section Incidence

variable {ψ : Projectivization H E → Projectivization C E'}
  (hψ : ProjectiveLiftBijection ψ) {ι : Type*}
  (b : Module.Basis ι H E) (b' : Module.Basis ι C E')
  (hp : ∀ k, ψ (Projectivization.mk H (b k) (b.ne_zero k)) =
    Projectivization.mk C (b' k) (b'.ne_zero k))
  (o : ι) (σ : H ≃+* C)
  (ht : ∀ k (hok : o ≠ k) a,
    ψ (projectiveAxis (projective_basis_pair b hok) a) =
      projectiveAxis (projective_basis_pair b' hok) (σ a))

include hψ hp ht

/-- Suppose ψ is a bijection preserving projective lines, ψ matches
corresponding basis points, and ψ transforms coordinates on every axis
through o by σ. If [v is nonzero](hyp:hv) and [its coordinate at o is
one](hyp:hvo), then [ψ sends the point represented by v to the point represented
by its coordinate lift](goal). -/
-- @node: projectiveFrameLift_affine
lemma projectiveFrameLift_affine {v : E} (hv : v ≠ 0) (hvo : b.repr v o = 1) :
    ψ (Projectivization.mk H v hv) =
      Projectivization.mk C (projectiveFrameLift b b' σ v)
        (fun hz => hv ((projectiveFrameLift b b' σ).injective
          (hz.trans (projectiveFrameLift b b' σ).map_zero.symm))) := by
  obtain ⟨w, hw, hwo, hpw⟩ := projective_frame_affine_representative hψ b b' hp
    o v hv (by rw [hvo]; exact one_ne_zero)
  have hc := projective_affine_all_coordinates hψ b b' hp o σ ht hv hvo hw hwo hpw
  have heq : projectiveFrameLift b b' σ v = w := by
    apply b'.repr.injective
    ext i
    exact (projectiveFrameLift_coordinate b b' σ v i).trans (hc i).symm
  simpa only [heq] using hpw

/-- Suppose ψ is a bijection preserving projective lines, ψ matches
corresponding basis points, and ψ transforms coordinates on every axis
through o by σ. If [v is nonzero](hyp:hv) and [its coordinate at o is
nonzero](hyp:hvo), then [the coordinate lift of v belongs to the one-dimensional
subspace representing the image under ψ of the point represented by v](goal). -/
-- @node: projectiveFrameLift_finite_mem
lemma projectiveFrameLift_finite_mem {v : E} (hv : v ≠ 0) (hvo : b.repr v o ≠ 0) :
    projectiveFrameLift b b' σ v ∈ (ψ (Projectivization.mk H v hv)).submodule := by
  let u := (b.repr v o)⁻¹ • v
  have hu : u ≠ 0 := smul_ne_zero (inv_ne_zero hvo) hv
  have huo : b.repr u o = 1 := by simp [u, hvo]
  have hpu : Projectivization.mk H u hu = Projectivization.mk H v hv := by
    apply (Projectivization.mk_eq_mk_iff' H _ _ hu hv).mpr
    exact ⟨(b.repr v o)⁻¹, rfl⟩
  have him := projectiveFrameLift_affine hψ b b' hp o σ ht hu huo
  have hmem : projectiveFrameLift b b' σ u ∈
      (ψ (Projectivization.mk H v hv)).submodule := by
    rw [← hpu, him, Projectivization.submodule_mk]
    exact Submodule.mem_span_singleton_self _
  have hvu : v = b.repr v o • u := by simp [u, smul_smul, hvo]
  have heq := congrArg (projectiveFrameLift b b' σ) hvu
  rw [projectiveFrameLift_smul] at heq
  rw [heq]
  exact Submodule.smul_mem _ _ hmem

/-- Suppose ψ is a bijection preserving projective lines, ψ matches
corresponding basis points, and ψ transforms coordinates on every axis
through o by σ. If [v is nonzero](hyp:hv) and [its coordinate at o is
zero](hyp:hvo), then [the coordinate lift of v belongs to the one-dimensional
subspace representing the image under ψ of the point represented by v](goal). -/
-- @node: projectiveFrameLift_infinite_mem
lemma projectiveFrameLift_infinite_mem {v : E} (hv : v ≠ 0) (hvo : b.repr v o = 0) :
    projectiveFrameLift b b' σ v ∈ (ψ (Projectivization.mk H v hv)).submodule := by
  classical
  let S := projectiveFrameLift b b' σ
  let x := ψ (Projectivization.mk H v hv)
  have hSo : b'.repr (S v) o = 0 := by simp [S, hvo]
  have hxo : b'.repr x.rep o = 0 := by
    apply (projective_frame_hyperplane_mem b' o x.rep).mp
    have him : collineationSubmoduleEquiv hψ
        (Submodule.span H (Set.range fun k : {k : ι // o ≠ k} => b k)) =
        Submodule.span C (Set.range fun k : {k : ι // o ≠ k} => b' k) :=
      collineation_frame_span_image hψ b b' hp {k | o ≠ k}
    have hmem := (collineation_point_mem_iff hψ _
      (Projectivization.mk H v hv)).mpr
        ((projective_mk_mem_points _ _ hv).mpr
          ((projective_frame_hyperplane_mem b o v).mpr hvo))
    rw [him] at hmem
    exact hmem (by
      rw [Projectivization.submodule_eq]
      exact Submodule.mem_span_singleton_self _)
  let u := b o + v
  have huo : b.repr u o = 1 := by simp [u, Module.Basis.repr_self, hvo]
  have hu : u ≠ 0 := by
    intro hz
    rw [hz] at huo
    simp at huo
  have hSu : S u = b' o + S v := by simp [S, u]
  have hSu0 : S u ≠ 0 := fun hz => hu (S.injective (hz.trans S.map_zero.symm))
  have hpu : ψ (Projectivization.mk H u hu) = Projectivization.mk C (S u) hSu0 :=
    projectiveFrameLift_affine hψ b b' hp o σ ht hu huo
  have hmem : x.rep ∈ Submodule.span C {b' o, S u} := by
    apply collineation_mem_span_pair hψ (b.ne_zero o) hu hv
      (b'.ne_zero o) hSu0 x.rep_nonzero (hp o) hpu (Projectivization.mk_rep x).symm
    apply Submodule.mem_span_pair.mpr
    exact ⟨-1, 1, by simp [u]⟩
  obtain ⟨s, t, hst⟩ := Submodule.mem_span_pair.mp hmem
  have ho := congrArg (fun z => b'.repr z o) hst
  have hst0 : s + t = 0 := by
    simpa [hSu, Module.Basis.repr_self, hSo, hxo] using ho
  have hdir : t • S v = x.rep := by
    calc
      t • S v = (s + t) • b' o + t • S v := by rw [hst0]; simp
      _ = s • b' o + t • S u := by rw [hSu, add_smul, smul_add]; abel
      _ = x.rep := hst
  have ht0 : t ≠ 0 := by
    intro hz
    exact x.rep_nonzero (by simpa [hz] using hdir.symm)
  have hSv : S v = t⁻¹ • x.rep := by rw [← hdir, smul_smul, inv_mul_cancel₀ ht0, one_smul]
  change S v ∈ x.submodule
  rw [hSv]
  apply Submodule.smul_mem
  rw [Projectivization.submodule_eq]
  exact Submodule.mem_span_singleton_self _

/-- Suppose ψ is a bijection preserving projective lines, ψ matches
corresponding basis points, and ψ transforms coordinates on every axis
through o by σ. For [a nonzero vector v](hyp:hv), [the coordinate lift of
v belongs to the one-dimensional subspace representing the image under ψ of the
point represented by v](goal). -/
-- @node: projectiveFrameLift_mem
lemma projectiveFrameLift_mem (v : E) (hv : v ≠ 0) :
    projectiveFrameLift b b' σ v ∈ (ψ (Projectivization.mk H v hv)).submodule := by
  by_cases hvo : b.repr v o = 0
  · exact projectiveFrameLift_infinite_mem hψ b b' hp o σ ht hv hvo
  · exact projectiveFrameLift_finite_mem hψ b b' hp o σ ht hv hvo

end Incidence

end Papers.OaiReconstructionMilnorTheory
