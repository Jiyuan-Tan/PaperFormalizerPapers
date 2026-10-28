module

public import Papers.OaiReconstructionMilnorTheory.Helpers.ProjectiveCoordinates
public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.Algebra.GroupWithZero.Units.Equiv

/-! # Normalizing a projective frame

Rescale the transported basis while keeping its distinguished vector fixed.
The resulting coordinate bijections on all distinguished axes fix zero and one.
Parallel coordinate lines and two-axis diagonals identify all these bijections.
-/

public section

namespace Papers.OaiReconstructionMilnorTheory

variable {H C E E' : Type*} [Field H] [Field C]
  [AddCommGroup E] [Module H E] [AddCommGroup E'] [Module C E']

/-- For [linearly independent origin and direction vectors](hyp:h), with
[the origin vector nonzero](hyp:hu), [the axis point at coordinate zero is the
projective point represented by the origin vector](goal). -/
-- @node: projectiveAxis_zero
@[simp] lemma projectiveAxis_zero {u v : E} (h : LinearIndependent H ![u, v])
    (hu : u ≠ 0) : projectiveAxis h 0 = Projectivization.mk H u hu := by
  simp [projectiveAxis]

/-- If [two basis indices are distinct](hyp:hij), [their basis vectors are
linearly independent](goal). -/
-- @node: projective_basis_pair
lemma projective_basis_pair {ι : Type*} (b : Module.Basis ι H E)
    {i j : ι} (hij : i ≠ j) : LinearIndependent H ![b i, b j] := by
  classical
  apply LinearIndependent.pair_iff.mpr
  intro a c hac
  have hi := congrArg (fun v => b.repr v i) hac
  have hj := congrArg (fun v => b.repr v j) hac
  simpa [Module.Basis.repr_self, hij, hij.symm] using And.intro hi hj

/-- If [an origin vector and a direction vector are linearly independent](hyp:h)
and [a scalar is nonzero](hyp:hc), [multiplying the direction vector by that
scalar preserves their linear independence](goal). -/
-- @node: projective_axis_rescale_independent
lemma projective_axis_rescale_independent {u v : E}
    (h : LinearIndependent H ![u, v]) {c : H} (hc : c ≠ 0) :
    LinearIndependent H ![u, c • v] := by
  simpa only [one_smul] using
    (LinearIndependent.pair_smul_smul_iff (R := H) (x := u) (y := v)
      (isUnit_one) (isUnit_iff_ne_zero.mpr hc)).mpr h

/-- Given [linearly independent origin and direction vectors](hyp:h) and
[a nonzero scalar](hyp:hc), [the axis point with any coordinate after rescaling
the direction equals the original axis point with that coordinate multiplied by
the scalar](goal). -/
-- @node: projectiveAxis_rescale
lemma projectiveAxis_rescale {u v : E} (h : LinearIndependent H ![u, v])
    {c : H} (hc : c ≠ 0) (a : H) :
    projectiveAxis (projective_axis_rescale_independent h hc) a =
      projectiveAxis h (a * c) := by
  simp only [projectiveAxis, smul_smul]

/-- Suppose [the source origin and direction are linearly independent](hyp:h),
[the target origin and direction are linearly independent](hyp:h'),
[both origin vectors are nonzero](hyp:hu,hu'), and [the projective map sends the
source origin to the target origin](hyp:hpu). If [a scalar bijection describes
the map on all axis coordinates](hyp:hτ), [that bijection sends zero to zero](goal). -/
-- @node: projective_axis_coordinate_zero
lemma projective_axis_coordinate_zero
    {ψ : Projectivization H E → Projectivization C E'}
    {u v : E} {u' v' : E'}
    (h : LinearIndependent H ![u, v]) (h' : LinearIndependent C ![u', v'])
    (hu : u ≠ 0) (hu' : u' ≠ 0)
    (hpu : ψ (Projectivization.mk H u hu) = Projectivization.mk C u' hu')
    (τ : H ≃ C) (hτ : ∀ a, ψ (projectiveAxis h a) = projectiveAxis h' (τ a)) :
    τ 0 = 0 := by
  apply projectiveAxis_injective h'
  rw [← hτ, projectiveAxis_zero h hu, hpu, projectiveAxis_zero h' hu']

/-- Suppose [a projective bijection maps lines onto lines](hyp:hψ),
[the source origin and direction are linearly independent](hyp:h),
[the target origin and direction are linearly independent](hyp:h'), and
[all four vectors are nonzero](hyp:hu,hv,hu',hv'). If [the origins correspond](hyp:hpu)
and [the directions correspond as projective points](hyp:hpv), [there exist a
nonzero target scalar and a scalar bijection fixing zero and one that describes
the map on the axis after rescaling the target direction by that scalar](goal). -/
-- @node: projective_axis_normalize
lemma projective_axis_normalize
    {ψ : Projectivization H E → Projectivization C E'}
    (hψ : ProjectiveLiftBijection ψ)
    {u v : E} {u' v' : E'}
    (h : LinearIndependent H ![u, v]) (h' : LinearIndependent C ![u', v'])
    (hu : u ≠ 0) (hv : v ≠ 0) (hu' : u' ≠ 0) (hv' : v' ≠ 0)
    (hpu : ψ (Projectivization.mk H u hu) = Projectivization.mk C u' hu')
    (hpv : ψ (Projectivization.mk H v hv) = Projectivization.mk C v' hv') :
    ∃ c : C, ∃ hc : c ≠ 0, ∃ τ : H ≃ C,
      τ 0 = 0 ∧ τ 1 = 1 ∧
      ∀ a, ψ (projectiveAxis h a) =
        projectiveAxis (projective_axis_rescale_independent h' hc) (τ a) := by
  obtain ⟨t, ht⟩ := projective_axis_coordinate_equiv hψ h h' hu hv hu' hv' hpu hpv
  have ht0 : t 0 = 0 := projective_axis_coordinate_zero h h' hu hu' hpu t ht
  have hc : t 1 ≠ 0 := by
    rw [← ht0]
    exact t.injective.ne one_ne_zero
  let τ : H ≃ C := t.trans (Equiv.mulRight₀ (t 1) hc).symm
  refine ⟨t 1, hc, τ, ?_, ?_, ?_⟩
  · simp [τ, ht0]
  · simp [τ, hc]
  · intro a
    rw [projectiveAxis_rescale h' hc]
    simpa [τ, hc] using ht a

/-- For [a projective bijection mapping lines onto lines](hyp:hψ), [the image of
each projective basis point is represented by the corresponding vector of the
transported basis](goal). -/
-- @node: projectiveImageBasis_point
lemma projectiveImageBasis_point
    {ψ : Projectivization H E → Projectivization C E'}
    (hψ : ProjectiveLiftBijection ψ) {ι : Type*} (b : Module.Basis ι H E) (i : ι) :
    ψ (Projectivization.mk H (b i) (b.ne_zero i)) =
      Projectivization.mk C (projectiveImageBasis hψ b i)
        ((projectiveImageBasis hψ b).ne_zero i) := by
  simp only [projectiveImageBasis_apply, Projectivization.mk_rep]

/-- For [a projective bijection mapping lines onto lines](hyp:hψ), [there is a
target basis whose distinguished vector equals that of the transported basis,
whose projective points are the images of the source basis points, and for which
every axis through the distinguished point is transported by a scalar bijection
fixing zero and one](goal). -/
-- @node: projective_normalized_frame
lemma projective_normalized_frame
    {ψ : Projectivization H E → Projectivization C E'}
    (hψ : ProjectiveLiftBijection ψ) {ι : Type*} (b : Module.Basis ι H E) (o : ι) :
    ∃ b' : Module.Basis ι C E',
      b' o = projectiveImageBasis hψ b o ∧
      (∀ i, ψ (Projectivization.mk H (b i) (b.ne_zero i)) =
        Projectivization.mk C (b' i) (b'.ne_zero i)) ∧
      ∀ i (hi : o ≠ i), ∃ τ : H ≃ C, τ 0 = 0 ∧ τ 1 = 1 ∧
        ∀ a, ψ (projectiveAxis (projective_basis_pair b hi) a) =
          projectiveAxis (projective_basis_pair b' hi) (τ a) := by
  classical
  let d := projectiveImageBasis hψ b
  have hex (i : {i : ι // o ≠ i}) := projective_axis_normalize hψ
    (projective_basis_pair b i.property) (projective_basis_pair d i.property)
    (b.ne_zero o) (b.ne_zero i) (d.ne_zero o) (d.ne_zero i)
    (projectiveImageBasis_point hψ b o) (projectiveImageBasis_point hψ b i)
  choose c hc τ hτ0 hτ1 hτ using hex
  let w : ι → Cˣ := fun i => if hi : o = i then 1 else Units.mk0 (c ⟨i, hi⟩) (hc ⟨i, hi⟩)
  let b' := d.unitsSMul w
  have ho : b' o = d o := by simp [b', Module.Basis.unitsSMul_apply, w]
  have hi (i : ι) (hi : o ≠ i) : b' i = c ⟨i, hi⟩ • d i := by
    simp [b', Module.Basis.unitsSMul_apply, w, hi]
  refine ⟨b', ho, ?_, ?_⟩
  · intro i
    rw [projectiveImageBasis_point hψ b i]
    apply (Projectivization.mk_eq_mk_iff' C _ _ (d.ne_zero i) (b'.ne_zero i)).mpr
    refine ⟨((w i : C)⁻¹), ?_⟩
    rw [show b' i = w i • d i from Module.Basis.unitsSMul_apply i]
    change (w i : C)⁻¹ • ((w i : C) • d i) = d i
    rw [smul_smul, inv_mul_cancel₀ (w i).ne_zero, one_smul]
  · intro i hio
    refine ⟨τ ⟨i, hio⟩, hτ0 _, hτ1 _, ?_⟩
    intro a
    convert hτ ⟨i, hio⟩ a using 1
    simp only [projectiveAxis, ho, hi i hio]

/-- If [a projective bijection maps lines onto lines](hyp:hψ) and [sends every
source basis point to the corresponding target basis point](hyp:hp), [its induced
map on linear subspaces sends the span of any selected source basis vectors to
the span of the target basis vectors with the same indices](goal). -/
-- @node: collineation_frame_span_image
lemma collineation_frame_span_image
    {ψ : Projectivization H E → Projectivization C E'}
    (hψ : ProjectiveLiftBijection ψ) {ι : Type*}
    (b : Module.Basis ι H E) (b' : Module.Basis ι C E')
    (hp : ∀ i, ψ (Projectivization.mk H (b i) (b.ne_zero i)) =
      Projectivization.mk C (b' i) (b'.ne_zero i)) (s : Set ι) :
    collineationSubmoduleEquiv hψ (Submodule.span H (Set.range fun i : s => b i)) =
      Submodule.span C (Set.range fun i : s => b' i) := by
  simp only [Submodule.span_range_eq_iSup, map_iSup]
  congr 1
  funext i
  have h := collineationSubmoduleEquiv_point hψ
    (Projectivization.mk H (b i) (b.ne_zero i))
  simpa only [hp, Projectivization.submodule_mk] using h

/-- For [a projective bijection mapping lines onto lines](hyp:hψ), [the image of
a point belongs to the transported linear subspace if and only if the original
point belongs to the original subspace](goal). -/
-- @node: collineation_point_mem_iff
lemma collineation_point_mem_iff
    {ψ : Projectivization H E → Projectivization C E'}
    (hψ : ProjectiveLiftBijection ψ) (W : Submodule H E)
    (x : Projectivization H E) :
    ψ x ∈ projectivePoints (collineationSubmoduleEquiv hψ W) ↔
      x ∈ projectivePoints W := by
  rw [collineationSubmoduleEquiv_points]
  constructor
  · rintro ⟨y, hy, heq⟩
    exact hψ.1.1 heq ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- [A vector lies in the span of all basis vectors except a distinguished one
if and only if its coordinate at that distinguished index is zero](goal). -/
-- @node: projective_frame_hyperplane_mem
lemma projective_frame_hyperplane_mem {ι : Type*} (b : Module.Basis ι H E)
    (o : ι) (v : E) :
    v ∈ Submodule.span H (Set.range fun i : {i : ι // o ≠ i} => b i) ↔
      b.repr v o = 0 := by
  classical
  have hs : (Set.range fun i : {i : ι // o ≠ i} => b i) = b '' {i | o ≠ i} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, i.property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  rw [hs, b.mem_span_image]
  constructor
  · intro h
    by_contra hn
    exact h (Finsupp.mem_support_iff.mpr hn) rfl
  · intro h i hi hoi
    subst i
    exact Finsupp.mem_support_iff.mp hi h

/-- Suppose [a projective bijection maps lines onto lines](hyp:hψ) and
[sends source basis points to their corresponding target basis points](hyp:hp).
For [a nonzero source vector](hyp:hv) with [nonzero distinguished coordinate](hyp:hvo),
[the chosen representative of its projective image also has nonzero distinguished
coordinate in the target basis](goal). -/
-- @node: projective_frame_affine_image
lemma projective_frame_affine_image
    {ψ : Projectivization H E → Projectivization C E'}
    (hψ : ProjectiveLiftBijection ψ) {ι : Type*}
    (b : Module.Basis ι H E) (b' : Module.Basis ι C E')
    (hp : ∀ i, ψ (Projectivization.mk H (b i) (b.ne_zero i)) =
      Projectivization.mk C (b' i) (b'.ne_zero i))
    (o : ι) (v : E) (hv : v ≠ 0) (hvo : b.repr v o ≠ 0) :
    b'.repr (ψ (Projectivization.mk H v hv)).rep o ≠ 0 := by
  intro hz
  let W := Submodule.span H (Set.range fun i : {i : ι // o ≠ i} => b i)
  have him := collineation_frame_span_image hψ b b' hp {i | o ≠ i}
  have hmem : ψ (Projectivization.mk H v hv) ∈
      projectivePoints (collineationSubmoduleEquiv hψ W) := by
    rw [show collineationSubmoduleEquiv hψ W = _ from him]
    change (ψ (Projectivization.mk H v hv)).submodule ≤ _
    rw [Projectivization.submodule_eq, Submodule.span_singleton_le_iff_mem]
    exact (projective_frame_hyperplane_mem b' o _).mpr hz
  have hsource := (collineation_point_mem_iff hψ W _).mp hmem
  have hvW := (projective_mk_mem_points W v hv).mp hsource
  exact hvo ((projective_frame_hyperplane_mem b o v).mp hvW)

/-- Suppose [a projective bijection maps lines onto lines](hyp:hψ) and
[sends source basis points to their corresponding target basis points](hyp:hp).
For [a nonzero source vector](hyp:hv) with [nonzero distinguished coordinate](hyp:hvo),
[its projective image has a nonzero representative whose distinguished coordinate
in the target basis is one](goal). -/
-- @node: projective_frame_affine_representative
lemma projective_frame_affine_representative
    {ψ : Projectivization H E → Projectivization C E'}
    (hψ : ProjectiveLiftBijection ψ) {ι : Type*}
    (b : Module.Basis ι H E) (b' : Module.Basis ι C E')
    (hp : ∀ i, ψ (Projectivization.mk H (b i) (b.ne_zero i)) =
      Projectivization.mk C (b' i) (b'.ne_zero i))
    (o : ι) (v : E) (hv : v ≠ 0) (hvo : b.repr v o ≠ 0) :
    ∃ w : E', ∃ hw : w ≠ 0, b'.repr w o = 1 ∧
      ψ (Projectivization.mk H v hv) = Projectivization.mk C w hw := by
  let x := ψ (Projectivization.mk H v hv)
  have hc : b'.repr x.rep o ≠ 0 := projective_frame_affine_image hψ b b' hp o v hv hvo
  let w := (b'.repr x.rep o)⁻¹ • x.rep
  have hw : w ≠ 0 := smul_ne_zero (inv_ne_zero hc) x.rep_nonzero
  refine ⟨w, hw, ?_, ?_⟩
  · simp [w, hc]
  · change x = Projectivization.mk C w hw
    rw [← Projectivization.mk_rep x]
    apply (Projectivization.mk_eq_mk_iff' C _ _ x.rep_nonzero hw).mpr
    exact ⟨b'.repr x.rep o, by simp [w, smul_smul, hc]⟩

/-- Suppose [the distinguished index differs from a direction index](hyp:hoi),
[two vectors both have distinguished coordinate one](hyp:hu,hv), and [the second
lies in the span of the first and the basis vector in that direction](hyp:hmem).
Then [the two vectors have equal coordinates at every index other than the
direction index](goal). -/
-- @node: projective_affine_parallel_coordinates
lemma projective_affine_parallel_coordinates {ι : Type*} (b : Module.Basis ι H E)
    {o i : ι} (hoi : o ≠ i) {u v : E}
    (hu : b.repr u o = 1) (hv : b.repr v o = 1)
    (hmem : v ∈ Submodule.span H {u, b i}) :
    ∀ j, j ≠ i → b.repr v j = b.repr u j := by
  classical
  obtain ⟨a, c, hac⟩ := Submodule.mem_span_pair.mp hmem
  have ho := congrArg (fun w => b.repr w o) hac
  have ha : a = 1 := by simpa [Module.Basis.repr_self, hoi, hu, hv] using ho
  intro j hji
  have hj := congrArg (fun w => b.repr w j) hac
  simpa [Module.Basis.repr_self, hji, ha] using hj.symm

/-- If [a direction index differs from the distinguished index](hyp:hoi) and
[a vector has distinguished coordinate one](hyp:hu), [that vector and the basis
vector in the direction are linearly independent](goal). -/
-- @node: projective_affine_direction_independent
lemma projective_affine_direction_independent {ι : Type*} (b : Module.Basis ι H E)
    {o i : ι} (hoi : o ≠ i) {u : E} (hu : b.repr u o = 1) :
    LinearIndependent H ![u, b i] := by
  classical
  apply LinearIndependent.pair_iff.mpr
  intro a c hac
  have ho := congrArg (fun w => b.repr w o) hac
  have ha : a = 0 := by simpa [Module.Basis.repr_self, hoi, hu] using ho
  have hi := congrArg (fun w => b.repr w i) hac
  exact ⟨ha, by simpa [Module.Basis.repr_self, ha] using hi⟩

/-- Suppose [a projective bijection maps lines onto lines](hyp:hψ) and
[matches corresponding basis points](hyp:hp), with [distinct distinguished and
direction indices](hyp:hoi). Let [two nonzero source vectors](hyp:hu,hv) satisfy
[distinguished coordinate one for the first](hyp:huo) and [the second equal to
the first plus a scalar multiple of the direction basis vector](hyp:hvu).
If [two nonzero target vectors](hyp:hu',hv') have [distinguished coordinate one](hyp:huo',hvo')
and [represent the respective projective images of the source vectors](hyp:hpu,hpv),
[their target coordinates agree at every index other than the direction index](goal). -/
-- @node: collineation_affine_parallel_coordinates
lemma collineation_affine_parallel_coordinates
    {ψ : Projectivization H E → Projectivization C E'}
    (hψ : ProjectiveLiftBijection ψ) {ι : Type*}
    (b : Module.Basis ι H E) (b' : Module.Basis ι C E')
    (hp : ∀ i, ψ (Projectivization.mk H (b i) (b.ne_zero i)) =
      Projectivization.mk C (b' i) (b'.ne_zero i))
    {o i : ι} (hoi : o ≠ i) {u v : E} (hu : u ≠ 0) (hv : v ≠ 0)
    (huo : b.repr u o = 1) (a : H) (hvu : v = u + a • b i)
    {u' v' : E'} (hu' : u' ≠ 0) (hv' : v' ≠ 0)
    (huo' : b'.repr u' o = 1) (hvo' : b'.repr v' o = 1)
    (hpu : ψ (Projectivization.mk H u hu) = Projectivization.mk C u' hu')
    (hpv : ψ (Projectivization.mk H v hv) = Projectivization.mk C v' hv') :
    ∀ j, j ≠ i → b'.repr v' j = b'.repr u' j := by
  have hli := projective_affine_direction_independent b hoi huo
  have hne : Projectivization.mk H u hu ≠
      Projectivization.mk H (b i) (b.ne_zero i) :=
    (Projectivization.independent_pair_iff_ne _ _).mp
      ((Projectivization.independent_mk_iff_LinearIndependent hu (b.ne_zero i)).mpr hli)
  have him := projective_line_image hψ hne
  simp only [hpu, hp, Projectivization.submodule_mk,
    ← Submodule.span_union, Set.singleton_union] at him
  have hvline : Projectivization.mk H v hv ∈
      projectivePoints (Submodule.span H {u, b i}) := by
    rw [projective_mk_mem_points, hvu]
    exact Submodule.add_mem _ (Submodule.subset_span (by simp))
      (Submodule.smul_mem _ a (Submodule.subset_span (by simp)))
  have hvimage : Projectivization.mk C v' hv' ∈
      projectivePoints (Submodule.span C {u', b' i}) := by
    rw [← hpv, ← him]
    exact ⟨_, hvline, rfl⟩
  exact projective_affine_parallel_coordinates b' hoi huo' hvo'
    ((projective_mk_mem_points _ _ _).mp hvimage)

/-- Suppose [a projective bijection maps lines onto lines](hyp:hψ) and
[matches corresponding basis points](hyp:hp), with [the origin distinct from
each of two direction indices](hyp:hoi,hoj) and [the directions distinct](hyp:hij).
Assume [the first scalar bijection describes transport on the first axis](hyp:hti)
and [the second describes transport on the second axis](hyp:htj).
For [a nonzero source vector](hyp:hv) [equal to the origin basis vector plus
scalar multiples of the two direction vectors](hyp:hveq), let [a nonzero target
vector](hyp:hw) [have origin coordinate one](hyp:hwo) and [represent its projective
image](hyp:hpw). Then [the two target direction coordinates are the respective
scalar bijections applied to the two source coefficients](goal). -/
-- @node: projective_two_axis_coordinates
lemma projective_two_axis_coordinates
    {ψ : Projectivization H E → Projectivization C E'}
    (hψ : ProjectiveLiftBijection ψ) {ι : Type*}
    (b : Module.Basis ι H E) (b' : Module.Basis ι C E')
    (hp : ∀ k, ψ (Projectivization.mk H (b k) (b.ne_zero k)) =
      Projectivization.mk C (b' k) (b'.ne_zero k))
    {o i j : ι} (hoi : o ≠ i) (hoj : o ≠ j) (hij : i ≠ j)
    (τi τj : H ≃ C)
    (hti : ∀ a, ψ (projectiveAxis (projective_basis_pair b hoi) a) =
      projectiveAxis (projective_basis_pair b' hoi) (τi a))
    (htj : ∀ a, ψ (projectiveAxis (projective_basis_pair b hoj) a) =
      projectiveAxis (projective_basis_pair b' hoj) (τj a))
    (a d : H) {v : E} (hv : v ≠ 0) (hveq : v = b o + a • b i + d • b j)
    {w : E'} (hw : w ≠ 0) (hwo : b'.repr w o = 1)
    (hpw : ψ (Projectivization.mk H v hv) = Projectivization.mk C w hw) :
    b'.repr w i = τi a ∧ b'.repr w j = τj d := by
  classical
  constructor
  · have heq : v = (b o + a • b i) + d • b j := hveq
    have ht := collineation_affine_parallel_coordinates hψ b b' hp hoj
      (projective_axis_ne_zero (projective_basis_pair b hoi) a) hv
      (by simp [Module.Basis.repr_self, hoi]) d heq
      (projective_axis_ne_zero (projective_basis_pair b' hoi) (τi a)) hw
      (by simp [Module.Basis.repr_self, hoi]) hwo (hti a) hpw i hij
    simpa [Module.Basis.repr_self, hoi.symm] using ht
  · have heq : v = (b o + d • b j) + a • b i := by rw [hveq]; abel
    have ht := collineation_affine_parallel_coordinates hψ b b' hp hoi
      (projective_axis_ne_zero (projective_basis_pair b hoj) d) hv
      (by simp [Module.Basis.repr_self, hoj]) a heq
      (projective_axis_ne_zero (projective_basis_pair b' hoj) (τj d)) hw
      (by simp [Module.Basis.repr_self, hoj]) hwo (htj d) hpw j hij.symm
    simpa [Module.Basis.repr_self, hoj.symm] using ht

/-- Suppose [a projective bijection maps lines onto lines](hyp:hψ) and
[matches corresponding basis points](hyp:hp), with [the origin distinct from
each of two direction indices](hyp:hoi,hoj) and [the directions distinct](hyp:hij).
If [both scalar bijections fix one](hyp:hti1,htj1), [the first describes transport
on the first axis](hyp:hti), and [the second describes transport on the second
axis](hyp:htj), [the two scalar bijections are equal](goal). -/
-- @node: projective_axis_coordinates_eq
lemma projective_axis_coordinates_eq
    {ψ : Projectivization H E → Projectivization C E'}
    (hψ : ProjectiveLiftBijection ψ) {ι : Type*}
    (b : Module.Basis ι H E) (b' : Module.Basis ι C E')
    (hp : ∀ k, ψ (Projectivization.mk H (b k) (b.ne_zero k)) =
      Projectivization.mk C (b' k) (b'.ne_zero k))
    {o i j : ι} (hoi : o ≠ i) (hoj : o ≠ j) (hij : i ≠ j)
    (τi τj : H ≃ C) (hti1 : τi 1 = 1) (htj1 : τj 1 = 1)
    (hti : ∀ a, ψ (projectiveAxis (projective_basis_pair b hoi) a) =
      projectiveAxis (projective_basis_pair b' hoi) (τi a))
    (htj : ∀ a, ψ (projectiveAxis (projective_basis_pair b hoj) a) =
      projectiveAxis (projective_basis_pair b' hoj) (τj a)) :
    τi = τj := by
  classical
  let v : H → E := fun a => b o + a • b i + a • b j
  have hvo (a : H) : b.repr (v a) o = 1 := by
    simp [v, Module.Basis.repr_self, hoi, hoj]
  have hv (a : H) : v a ≠ 0 := by
    intro hz
    have h := hvo a
    rw [hz] at h
    simp at h
  obtain ⟨w₁, hw₁, hw₁o, hp₁⟩ := projective_frame_affine_representative hψ b b' hp
    o (v 1) (hv 1) (by rw [hvo]; exact one_ne_zero)
  have hw₁c := projective_two_axis_coordinates hψ b b' hp hoi hoj hij
    τi τj hti htj 1 1 (hv 1) rfl hw₁ hw₁o hp₁
  have hw₁i : b'.repr w₁ i = 1 := hw₁c.1.trans hti1
  have hw₁j : b'.repr w₁ j = 1 := hw₁c.2.trans htj1
  have hne : Projectivization.mk H (b o) (b.ne_zero o) ≠
      Projectivization.mk H (v 1) (hv 1) := by
    intro heq
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' H _ _ (b.ne_zero o) (hv 1)).mp heq
    have hci := congrArg (fun w => b.repr w i) hc
    have hc0 : c = 0 := by
      simpa [v, Module.Basis.repr_self, hoi.symm, hij] using hci
    exact b.ne_zero o (by simpa [hc0] using hc.symm)
  have him := projective_line_image hψ hne
  simp only [hp, hp₁, Projectivization.submodule_mk,
    ← Submodule.span_union, Set.singleton_union] at him
  apply Equiv.ext
  intro a
  obtain ⟨w, hw, hwo, hpw⟩ := projective_frame_affine_representative hψ b b' hp
    o (v a) (hv a) (by rw [hvo]; exact one_ne_zero)
  have hwc := projective_two_axis_coordinates hψ b b' hp hoi hoj hij
    τi τj hti htj a a (hv a) rfl hw hwo hpw
  have hvline : Projectivization.mk H (v a) (hv a) ∈
      projectivePoints (Submodule.span H {b o, v 1}) := by
    apply (projective_mk_mem_points _ _ _).mpr
    apply Submodule.mem_span_pair.mpr
    refine ⟨1 - a, a, ?_⟩
    simp only [v, smul_add, sub_smul, one_smul]
    abel
  have hwline : w ∈ Submodule.span C {b' o, w₁} := by
    apply (projective_mk_mem_points _ _ hw).mp
    rw [← hpw, ← him]
    exact ⟨_, hvline, rfl⟩
  obtain ⟨s, t, hst⟩ := Submodule.mem_span_pair.mp hwline
  have hi := congrArg (fun w => b'.repr w i) hst
  have hj := congrArg (fun w => b'.repr w j) hst
  have hti' : t = τi a := by
    simpa [Module.Basis.repr_self, hoi.symm, hw₁i, hwc.1] using hi
  have htj' : t = τj a := by
    simpa [Module.Basis.repr_self, hoj.symm, hw₁j, hwc.2] using hj
  exact hti'.symm.trans htj'

/-- Given [a projective bijection mapping lines onto lines](hyp:hψ) and [a
direction index distinct from a distinguished origin index](hyp:hoi), [there
exist a target basis and a common scalar bijection fixing zero and one such that
the distinguished vector equals that of the transported basis, corresponding
basis points match, and this same bijection describes transport on every axis
through the distinguished point](goal). -/
-- @node: projective_common_frame_coordinates
lemma projective_common_frame_coordinates
    {ψ : Projectivization H E → Projectivization C E'}
    (hψ : ProjectiveLiftBijection ψ) {ι : Type*}
    (b : Module.Basis ι H E) (o i : ι) (hoi : o ≠ i) :
    ∃ b' : Module.Basis ι C E', ∃ τ : H ≃ C,
      τ 0 = 0 ∧ τ 1 = 1 ∧
      b' o = projectiveImageBasis hψ b o ∧
      (∀ k, ψ (Projectivization.mk H (b k) (b.ne_zero k)) =
        Projectivization.mk C (b' k) (b'.ne_zero k)) ∧
      ∀ j (hoj : o ≠ j) a,
        ψ (projectiveAxis (projective_basis_pair b hoj) a) =
          projectiveAxis (projective_basis_pair b' hoj) (τ a) := by
  classical
  obtain ⟨b', hbo, hp, ht⟩ := projective_normalized_frame hψ b o
  have hex (j : {j : ι // o ≠ j}) := ht j j.property
  choose τ hτ0 hτ1 hτ using hex
  refine ⟨b', τ ⟨i, hoi⟩, hτ0 _, hτ1 _, hbo, hp, ?_⟩
  intro j hoj a
  have heq : τ ⟨i, hoi⟩ = τ ⟨j, hoj⟩ := by
    by_cases hij : i = j
    · subst j
      rfl
    · exact projective_axis_coordinates_eq hψ b b' hp hoi hoj hij
        (τ ⟨i, hoi⟩) (τ ⟨j, hoj⟩) (hτ1 ⟨i, hoi⟩) (hτ1 ⟨j, hoj⟩)
        (hτ ⟨i, hoi⟩) (hτ ⟨j, hoj⟩)
  rw [heq]
  exact hτ ⟨j, hoj⟩ a

end Papers.OaiReconstructionMilnorTheory
