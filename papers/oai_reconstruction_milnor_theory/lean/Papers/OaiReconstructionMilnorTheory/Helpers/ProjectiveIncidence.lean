module

public import Papers.OaiReconstructionMilnorTheory.Helpers.ProjectiveLiftBasic

/-! # Incidence transport for projective collineations

The line-image hypothesis determines the image of every line through two distinct
points. It consequently transports arbitrary spans, so a coordinate construction
can choose frames without assuming any semilinear lift.
-/

@[expose] public section

namespace Papers.OaiReconstructionMilnorTheory

variable {H C E E' : Type*} [Field H] [Field C]
  [AddCommGroup E] [Module H E] [AddCommGroup E'] [Module C E']

/-- For [a linear subspace](hyp:W), its [projective point set](goal) consists of
the one-dimensional linear subspaces contained in it. -/
-- @node: projectivePoints
def projectivePoints (W : Submodule H E) : Set (Projectivization H E) :=
  {x | x.submodule ≤ W}

-- @node: mem_projectivePoints
/-- [A projective point belongs to the projective point set of a linear subspace
if and only if its one-dimensional linear subspace is contained in that subspace](goal). -/
@[simp] lemma mem_projectivePoints (W : Submodule H E) (x : Projectivization H E) :
    x ∈ projectivePoints W ↔ x.submodule ≤ W := Iff.rfl

-- @node: projective_mk_mem_points
/-- For [a nonzero vector](hyp:hv), [its projective point belongs to the
projective point set of a linear subspace if and only if the vector itself
belongs to that subspace](goal). -/
@[simp] lemma projective_mk_mem_points (W : Submodule H E) (v : E) (hv : v ≠ 0) :
    Projectivization.mk H v hv ∈ projectivePoints W ↔ v ∈ W := by
  simp [projectivePoints, Submodule.span_singleton_le_iff_mem]

/-- If [two projective points are distinct](hyp:hxy), [the linear subspace
spanned by their one-dimensional subspaces has dimension two](goal). -/
-- @node: projective_pair_finrank
lemma projective_pair_finrank {x y : Projectivization H E} (hxy : x ≠ y) :
    Module.finrank H ↥(x.submodule ⊔ y.submodule) = 2 := by
  induction x using Projectivization.ind with | h v hv =>
  induction y using Projectivization.ind with | h w hw =>
  have hli : LinearIndependent H ![v, w] := by
    exact (Projectivization.independent_mk_iff_LinearIndependent hv hw).mp
      ((Projectivization.independent_pair_iff_ne _ _).mpr hxy)
  have hspan : (Projectivization.mk H v hv).submodule ⊔
      (Projectivization.mk H w hw).submodule = Submodule.span H (Set.range ![v, w]) := by
    rw [Projectivization.submodule_mk, Projectivization.submodule_mk,
      ← Submodule.span_union, Set.singleton_union, Matrix.range_cons_cons_empty]
  rw [hspan]
  simpa using finrank_span_eq_card hli

/-- If [a projective bijection maps lines onto lines](hyp:hψ) and [two source
points are distinct](hyp:hxy), [the image of their projective line is exactly
the projective line through their images](goal). -/
-- @node: projective_line_image
lemma projective_line_image
    {ψ : Projectivization H E → Projectivization C E'}
    (hψ : ProjectiveLiftBijection ψ) {x y : Projectivization H E} (hxy : x ≠ y) :
    ψ '' projectivePoints (x.submodule ⊔ y.submodule) =
      projectivePoints ((ψ x).submodule ⊔ (ψ y).submodule) := by
  obtain ⟨W, hW, him⟩ := hψ.2 _ (projective_pair_finrank hxy)
  change ψ '' projectivePoints (x.submodule ⊔ y.submodule) = projectivePoints W at him
  have hx : (ψ x).submodule ≤ W := by
    have : ψ x ∈ ψ '' projectivePoints (x.submodule ⊔ y.submodule) :=
      ⟨x, (show x.submodule ≤ _ from le_sup_left), rfl⟩
    rwa [him] at this
  have hy : (ψ y).submodule ≤ W := by
    have : ψ y ∈ ψ '' projectivePoints (x.submodule ⊔ y.submodule) :=
      ⟨y, (show y.submodule ≤ _ from le_sup_right), rfl⟩
    rwa [him] at this
  have hne : ψ x ≠ ψ y := hψ.1.1.ne hxy
  have heq : W = (ψ x).submodule ⊔ (ψ y).submodule :=
    Projectivization.line_unique hne W _ hW (projective_pair_finrank hne)
      ((Submodule.mem_projectivization_iff_submodule_le _ _).mpr hx)
      ((Submodule.mem_projectivization_iff_submodule_le _ _).mpr hy)
      ((Submodule.mem_projectivization_iff_submodule_le _ _).mpr le_sup_left)
      ((Submodule.mem_projectivization_iff_submodule_le _ _).mpr le_sup_right)
  simpa [heq, projectivePoints] using him

/-- If [a projective map is bijective and maps lines onto lines](hyp:hψ),
[its inverse is also bijective and maps lines onto lines](goal). -/
-- @node: projective_inverse_lines
lemma projective_inverse_lines
    {ψ : Projectivization H E → Projectivization C E'}
    (hψ : ProjectiveLiftBijection ψ) :
    ProjectiveLiftBijection (Equiv.ofBijective ψ hψ.1).symm := by
  classical
  let e := Equiv.ofBijective ψ hψ.1
  refine ⟨e.symm.bijective, ?_⟩
  intro W hW
  let : FiniteDimensional C W := Module.finite_of_finrank_eq_succ hW
  let b := Module.finBasis C W
  have hi : 0 < Module.finrank C W := by omega
  have hj : 1 < Module.finrank C W := by omega
  let u : W := b ⟨0, hi⟩
  let v : W := b ⟨1, hj⟩
  have hu : (u : E') ≠ 0 := by
    exact_mod_cast b.ne_zero ⟨0, hi⟩
  have hv : (v : E') ≠ 0 := by
    exact_mod_cast b.ne_zero ⟨1, hj⟩
  let x := Projectivization.mk C (u : E') hu
  let y := Projectivization.mk C (v : E') hv
  have hxy : x ≠ y := by
    intro heq
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' C _ _ hu hv).mp heq
    have haa : a • v = u := Subtype.ext ha
    have hone := congrArg (fun z => b.repr z ⟨0, hi⟩) haa
    simp [u, v, Module.Basis.repr_self] at hone
  have hspan : W = x.submodule ⊔ y.submodule :=
    Projectivization.line_unique hxy W _ hW (projective_pair_finrank hxy)
      (by exact u.property) (by exact v.property)
      ((Submodule.mem_projectivization_iff_submodule_le _ _).mpr le_sup_left)
      ((Submodule.mem_projectivization_iff_submodule_le _ _).mpr le_sup_right)
  have hne : e.symm x ≠ e.symm y := e.symm.injective.ne hxy
  refine ⟨(e.symm x).submodule ⊔ (e.symm y).submodule,
    projective_pair_finrank hne, ?_⟩
  have him := projective_line_image hψ hne
  change e.symm '' projectivePoints W = _
  have him' : e '' projectivePoints ((e.symm x).submodule ⊔ (e.symm y).submodule) =
      projectivePoints W := by
    change e '' projectivePoints ((e.symm x).submodule ⊔ (e.symm y).submodule) =
      projectivePoints ((e (e.symm x)).submodule ⊔ (e (e.symm y)).submodule) at him
    simpa only [e.apply_symm_apply, ← hspan] using him
  rw [← him', ← Set.image_comp]
  simp [projectivePoints]

/-- Given [a projective bijection mapping lines onto lines](hyp:hψ) and
[a target projective subspace](hyp:U), the [inverse-image projective subspace](goal)
consists of source points whose images belong to that target subspace. -/
-- @node: projectiveSubspacePreimage
def projectiveSubspacePreimage
    {ψ : Projectivization H E → Projectivization C E'}
    (hψ : ProjectiveLiftBijection ψ) (U : Projectivization.Subspace C E') :
    Projectivization.Subspace H E where
  carrier := ψ ⁻¹' U
  mem_add' v w hv hw hvw hUv hUw := by
    let x := Projectivization.mk H v hv
    let y := Projectivization.mk H w hw
    by_cases hxy : x = y
    · have hvwspan : v + w ∈ x.submodule :=
        (x.submodule).add_mem
          (Submodule.mem_span_singleton_self v)
          (by rw [hxy]; exact Submodule.mem_span_singleton_self w)
      have heq : Projectivization.mk H (v + w) hvw = x := by
        apply Projectivization.submodule_injective
        exact eq_span_singleton_of_mem_of_finrank_eq_one
          (Projectivization.finrank_submodule x) hvwspan hvw |>.symm
      simpa only [heq] using hUv
    · let T := Projectivization.Subspace.submodule U
      have hx : (ψ x).submodule ≤ T :=
        (Submodule.mem_projectivization_iff_submodule_le _ _).mp (by simpa [T] using hUv)
      have hy : (ψ y).submodule ≤ T :=
        (Submodule.mem_projectivization_iff_submodule_le _ _).mp (by simpa [T] using hUw)
      have hsum : Projectivization.mk H (v + w) hvw ∈
          projectivePoints (x.submodule ⊔ y.submodule) := by
        apply (projective_mk_mem_points _ _ _).mpr
        exact Submodule.add_mem_sup
          (Submodule.mem_span_singleton_self v) (Submodule.mem_span_singleton_self w)
      have him : ψ (Projectivization.mk H (v + w) hvw) ∈
          projectivePoints ((ψ x).submodule ⊔ (ψ y).submodule) := by
        rw [← projective_line_image hψ hxy]
        exact ⟨_, hsum, rfl⟩
      have hle : (ψ (Projectivization.mk H (v + w) hvw)).submodule ≤ T :=
        him.trans (sup_le hx hy)
      have hmem := (Submodule.mem_projectivization_iff_submodule_le _ _).mpr hle
      simpa [T] using hmem

/-- For [a projective bijection mapping lines onto lines](hyp:hψ), [the image
of the projective span of any set of points equals the projective span of their
images](goal). -/
-- @node: projective_span_image
lemma projective_span_image
    {ψ : Projectivization H E → Projectivization C E'}
    (hψ : ProjectiveLiftBijection ψ) (S : Set (Projectivization H E)) :
    ψ '' (Projectivization.Subspace.span S : Set (Projectivization H E)) =
      (Projectivization.Subspace.span (ψ '' S) : Set (Projectivization C E')) := by
  classical
  let e := Equiv.ofBijective ψ hψ.1
  have hfwd : ψ '' (Projectivization.Subspace.span S : Set (Projectivization H E)) ⊆
      (Projectivization.Subspace.span (ψ '' S) : Set (Projectivization C E')) := by
    rintro _ ⟨x, hx, rfl⟩
    have hle : Projectivization.Subspace.span S ≤
        projectiveSubspacePreimage hψ (Projectivization.Subspace.span (ψ '' S)) := by
      apply Projectivization.Subspace.span_le_subspace_iff.mpr
      intro y hy
      exact Projectivization.Subspace.subset_span _ ⟨y, hy, rfl⟩
    exact hle hx
  apply Set.Subset.antisymm hfwd
  intro y hy
  refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
  have hle : Projectivization.Subspace.span (ψ '' S) ≤
      projectiveSubspacePreimage (projective_inverse_lines hψ)
        (Projectivization.Subspace.span S) := by
    apply Projectivization.Subspace.span_le_subspace_iff.mpr
    rintro z ⟨x, hx, rfl⟩
    change e.symm (e x) ∈ Projectivization.Subspace.span S
    simpa using Projectivization.Subspace.subset_span S hx
  exact hle hy

/-- Given [a projective bijection mapping lines onto lines](hyp:hψ), the
[inclusion-preserving correspondence between projective subspaces](goal) sends
each source subspace to its image and each target subspace back to its inverse image. -/
-- @node: projectiveSubspaceEquiv
noncomputable def projectiveSubspaceEquiv
    {ψ : Projectivization H E → Projectivization C E'}
    (hψ : ProjectiveLiftBijection ψ) :
    Projectivization.Subspace H E ≃o Projectivization.Subspace C E' where
  toFun U := projectiveSubspacePreimage (projective_inverse_lines hψ) U
  invFun U := projectiveSubspacePreimage hψ U
  left_inv U := by
    ext x
    change (Equiv.ofBijective ψ hψ.1).symm (ψ x) ∈ U ↔ x ∈ U
    simp
  right_inv U := by
    ext x
    change ψ ((Equiv.ofBijective ψ hψ.1).symm x) ∈ U ↔ x ∈ U
    rw [show ψ ((Equiv.ofBijective ψ hψ.1).symm x) = x from
      (Equiv.ofBijective ψ hψ.1).apply_symm_apply x]
  map_rel_iff' := by
    intro U V
    constructor
    · intro h x hx
      have h' := h (show ψ x ∈ projectiveSubspacePreimage (projective_inverse_lines hψ) U
        from by change (Equiv.ofBijective ψ hψ.1).symm (ψ x) ∈ U; simpa using hx)
      change (Equiv.ofBijective ψ hψ.1).symm (ψ x) ∈ V at h'
      simpa using h'
    · intro h x hx
      exact h hx

/-- Given [a projective bijection mapping lines onto lines](hyp:hψ), the
[inclusion-preserving correspondence between linear subspaces](goal) transports
each subspace by applying the bijection to its projective points and recovering
the associated target linear subspace. -/
-- @node: collineationSubmoduleEquiv
noncomputable def collineationSubmoduleEquiv
    {ψ : Projectivization H E → Projectivization C E'}
    (hψ : ProjectiveLiftBijection ψ) : Submodule H E ≃o Submodule C E' :=
  Submodule.projectivization.trans
    ((projectiveSubspaceEquiv hψ).trans Projectivization.Subspace.submodule)

/-- For [a projective bijection mapping lines onto lines](hyp:hψ), [the
projective points of a transported linear subspace are exactly the images of
the projective points of the original subspace](goal). -/
-- @node: collineationSubmoduleEquiv_points
lemma collineationSubmoduleEquiv_points
    {ψ : Projectivization H E → Projectivization C E'}
    (hψ : ProjectiveLiftBijection ψ) (W : Submodule H E) :
    projectivePoints (collineationSubmoduleEquiv hψ W) = ψ '' projectivePoints W := by
  classical
  let e := Equiv.ofBijective ψ hψ.1
  ext x
  change x.submodule ≤ _ ↔ _
  rw [← Submodule.mem_projectivization_iff_submodule_le]
  simp only [collineationSubmoduleEquiv, OrderIso.trans_apply,
    OrderIso.symm_apply_apply]
  change e.symm x ∈ W.projectivization ↔ _
  constructor
  · intro hx
    exact ⟨e.symm x, (Submodule.mem_projectivization_iff_submodule_le _ _).mp hx,
      e.apply_symm_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    change e.symm (e y) ∈ W.projectivization
    simpa using (Submodule.mem_projectivization_iff_submodule_le W y).mpr hy

/-- For [a projective bijection mapping lines onto lines](hyp:hψ), [the induced
linear-subspace correspondence sends the one-dimensional subspace of any
projective point to the one-dimensional subspace of its image](goal). -/
-- @node: collineationSubmoduleEquiv_point
lemma collineationSubmoduleEquiv_point
    {ψ : Projectivization H E → Projectivization C E'}
    (hψ : ProjectiveLiftBijection ψ) (x : Projectivization H E) :
    collineationSubmoduleEquiv hψ x.submodule = (ψ x).submodule := by
  apply Submodule.projectivization.injective
  ext y
  change y ∈ (collineationSubmoduleEquiv hψ x.submodule).projectivization ↔
    y ∈ (ψ x).submodule.projectivization
  rw [Submodule.mem_projectivization_iff_submodule_le]
  change y ∈ projectivePoints (collineationSubmoduleEquiv hψ x.submodule) ↔ _
  rw [collineationSubmoduleEquiv_points]
  have hpoints : projectivePoints x.submodule = {x} := by
    ext z
    change z.submodule ≤ x.submodule ↔ z = x
    constructor
    · intro h
      apply Projectivization.submodule_injective
      exact Submodule.eq_of_le_of_finrank_eq h
        (by simp only [Projectivization.finrank_submodule])
    · rintro rfl
      exact le_rfl
  rw [hpoints, Set.image_singleton]
  change y = ψ x ↔ y ∈ (ψ x).submodule.projectivization
  rw [Submodule.mem_projectivization_iff_submodule_le]
  constructor
  · rintro rfl
    exact le_rfl
  · intro h
    apply Projectivization.submodule_injective
    exact Submodule.eq_of_le_of_finrank_eq h
      (by simp only [Projectivization.finrank_submodule])

/-- If [a projective bijection maps lines onto lines](hyp:hψ) and [an indexed
family of projective points is independent](hyp:hf), [the family of their images
is independent as well](goal). -/
-- @node: projective_independent_image
lemma projective_independent_image
    {ψ : Projectivization H E → Projectivization C E'}
    (hψ : ProjectiveLiftBijection ψ) {ι : Type*} (f : ι → Projectivization H E)
    (hf : Projectivization.Independent f) : Projectivization.Independent (ψ ∘ f) := by
  apply Projectivization.independent_iff_iSupIndep.mpr
  have h := iSupIndep.map_orderIso (collineationSubmoduleEquiv hψ)
    (Projectivization.independent_iff_iSupIndep.mp hf)
  simpa only [Function.comp_def, collineationSubmoduleEquiv_point] using h

/-- For [a projective bijection mapping lines onto lines](hyp:hψ), [the induced
subspace correspondence sends the linear span of representatives of any indexed
family of projective points to the linear span of representatives of their images](goal). -/
-- @node: collineation_span_reps_image
lemma collineation_span_reps_image
    {ψ : Projectivization H E → Projectivization C E'}
    (hψ : ProjectiveLiftBijection ψ) {ι : Type*} (f : ι → Projectivization H E) :
    collineationSubmoduleEquiv hψ (Submodule.span H (Set.range fun i => (f i).rep)) =
      Submodule.span C (Set.range fun i => (ψ (f i)).rep) := by
  simp_rw [Submodule.span_range_eq_iSup, ← Projectivization.submodule_eq]
  rw [map_iSup]
  simp only [collineationSubmoduleEquiv_point]

/-- For [a projective bijection mapping lines onto lines](hyp:hψ), [the chosen
representatives of the images of the projective points of any source basis are
linearly independent and span the entire target vector space](goal). -/
-- @node: projective_image_basis_vectors
lemma projective_image_basis_vectors
    {ψ : Projectivization H E → Projectivization C E'}
    (hψ : ProjectiveLiftBijection ψ) {ι : Type*} (b : Module.Basis ι H E) :
    let f := fun i => Projectivization.mk H (b i) (b.ne_zero i)
    LinearIndependent C (fun i => (ψ (f i)).rep) ∧
      Submodule.span C (Set.range fun i => (ψ (f i)).rep) = ⊤ := by
  classical
  intro f
  have hf : Projectivization.Independent f :=
    Projectivization.Independent.mk b b.ne_zero b.linearIndependent
  refine ⟨Projectivization.independent_iff.mp (projective_independent_image hψ f hf), ?_⟩
  have hs : Submodule.span H (Set.range fun i => (f i).rep) = ⊤ := by
    simp_rw [Submodule.span_range_eq_iSup, ← Projectivization.submodule_eq]
    change (⨆ i, Submodule.span H {b i}) = ⊤
    rw [← Submodule.span_range_eq_iSup, b.span_eq]
  have him := collineation_span_reps_image hψ f
  rw [hs, map_top] at him
  exact him.symm

end Papers.OaiReconstructionMilnorTheory
