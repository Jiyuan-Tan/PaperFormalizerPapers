module

public import Papers.OaiReconstructionMilnorTheory.Helpers.ProjectiveIncidence
public import Mathlib.LinearAlgebra.Basis.Basic

/-! # Affine coordinates on a projective line

These constructions use only independent vectors and projective incidence, so
they can be used before the field isomorphism and the semilinear lift exist.
-/

@[expose] public section

namespace Papers.OaiReconstructionMilnorTheory

variable {H C E E' : Type*} [Field H] [Field C]
  [AddCommGroup E] [Module H E] [AddCommGroup E'] [Module C E']

/-- Given [a bijection ψ preserving projective lines](hyp:hψ) and [a source
basis b](hyp:b), [the image basis](goal) is the target basis whose vectors are the
chosen representatives of the images under ψ of the source basis points. -/
-- @node: projectiveImageBasis
noncomputable def projectiveImageBasis
    {ψ : Projectivization H E → Projectivization C E'}
    (hψ : ProjectiveLiftBijection ψ) {ι : Type*} (b : Module.Basis ι H E) :
    Module.Basis ι C E' :=
  Module.Basis.mk (projective_image_basis_vectors hψ b).1
    (by rw [(projective_image_basis_vectors hψ b).2])

/-- For [a bijection ψ preserving projective lines](hyp:hψ), [the i-th vector of
the image basis is the chosen representative of the image under ψ of the i-th
source basis point](goal). -/
-- @node: projectiveImageBasis_apply
lemma projectiveImageBasis_apply
    {ψ : Projectivization H E → Projectivization C E'}
    (hψ : ProjectiveLiftBijection ψ) {ι : Type*} (b : Module.Basis ι H E) (i : ι) :
    projectiveImageBasis hψ b i = (ψ (Projectivization.mk H (b i) (b.ne_zero i))).rep :=
  Module.Basis.mk_apply _ _ i

/-- If [u and v are linearly independent](hyp:h), then [u plus a times v is
nonzero for every scalar a](goal). -/
-- @node: projective_axis_ne_zero
lemma projective_axis_ne_zero {u v : E} (h : LinearIndependent H ![u, v]) (a : H) :
    u + a • v ≠ 0 := by
  intro heq
  have hzero : (1 : H) • u + a • v = 0 := by simpa using heq
  have hh := (LinearIndependent.pair_iff.mp h) 1 a hzero
  exact one_ne_zero hh.1

/-- Given [linearly independent vectors u and v](hyp:h) and [a scalar coordinate
a](hyp:a), [the affine axis point at a](goal) is the projective point represented
by u plus a times v. -/
-- @node: projectiveAxis
def projectiveAxis {u v : E} (h : LinearIndependent H ![u, v]) (a : H) :
    Projectivization H E :=
  Projectivization.mk H (u + a • v) (projective_axis_ne_zero h a)

/-- If [u and v are linearly independent](hyp:h), then [distinct scalar
coordinates give distinct affine axis points represented by u plus a scalar
multiple of v](goal). -/
-- @node: projectiveAxis_injective
lemma projectiveAxis_injective {u v : E} (h : LinearIndependent H ![u, v]) :
    Function.Injective (projectiveAxis h) := by
  intro a b hab
  obtain ⟨t, ht⟩ := (Projectivization.mk_eq_mk_iff' H _ _
    (projective_axis_ne_zero h a) (projective_axis_ne_zero h b)).mp hab
  have heq : (t - 1) • u + (t * b - a) • v = 0 := by
    calc
      (t - 1) • u + (t * b - a) • v =
          t • (u + b • v) - (u + a • v) := by
        simp only [smul_add, sub_smul, mul_smul, one_smul]
        abel
      _ = 0 := sub_eq_zero.mpr ht
  obtain ⟨ht1, hta⟩ := LinearIndependent.pair_iff.mp h (t - 1) (t * b - a) heq
  have ht' : t = 1 := sub_eq_zero.mp ht1
  simpa [ht'] using (sub_eq_zero.mp hta).symm

/-- If [u and v are linearly independent](hyp:h) and [v is nonzero](hyp:hv),
then [the affine axis point at any scalar a differs from the point represented
by v](goal). -/
-- @node: projectiveAxis_ne_infinity
lemma projectiveAxis_ne_infinity {u v : E} (h : LinearIndependent H ![u, v])
    (hv : v ≠ 0) (a : H) : projectiveAxis h a ≠ Projectivization.mk H v hv := by
  intro heq
  obtain ⟨t, ht⟩ := (Projectivization.mk_eq_mk_iff' H _ _
    (projective_axis_ne_zero h a) hv).mp heq
  have hz : (1 : H) • u + (a - t) • v = 0 := by
    calc
      (1 : H) • u + (a - t) • v = (u + a • v) - t • v := by
        simp only [one_smul, sub_smul]
        abel
      _ = 0 := sub_eq_zero.mpr ht.symm
  exact one_ne_zero ((LinearIndependent.pair_iff.mp h) 1 (a - t) hz).1

/-- Suppose [u and v are linearly independent](hyp:h) and [v is nonzero](hyp:hv).
If [x lies on the projective line spanned by u and v](hyp:hx) and [x differs from
the point represented by v](hyp:hne), then [there is a unique scalar a whose
affine axis point is x](goal). -/
-- @node: projectiveAxis_surjective_chart
lemma projectiveAxis_surjective_chart {u v : E} (h : LinearIndependent H ![u, v])
    (hv : v ≠ 0) (x : Projectivization H E)
    (hx : x ∈ projectivePoints (Submodule.span H {u, v}))
    (hne : x ≠ Projectivization.mk H v hv) : ∃! a : H, projectiveAxis h a = x := by
  have hrep : x.rep ∈ Submodule.span H {u, v} :=
    hx (by rw [Projectivization.submodule_eq]; exact Submodule.mem_span_singleton_self _)
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hrep
  have ha : a ≠ 0 := by
    intro ha
    apply hne
    rw [← Projectivization.mk_rep x]
    apply (Projectivization.mk_eq_mk_iff' H _ _ x.rep_nonzero hv).mpr
    exact ⟨b, by simpa [ha] using hab⟩
  have hcoord : projectiveAxis h (b / a) = x := by
    rw [← Projectivization.mk_rep x]
    apply (Projectivization.mk_eq_mk_iff' H _ _
      (projective_axis_ne_zero h (b / a)) x.rep_nonzero).mpr
    refine ⟨a⁻¹, ?_⟩
    rw [← hab, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ ha, one_smul]
    simp only [div_eq_mul_inv, mul_comm]
  exact ⟨b / a, hcoord, fun c hc => projectiveAxis_injective h (hc.trans hcoord.symm)⟩

/-- If [u and v are linearly independent](hyp:h), then [the affine axis point at
any scalar a belongs to the projective line arising from the span of u and v](goal). -/
-- @node: projectiveAxis_mem
lemma projectiveAxis_mem {u v : E} (h : LinearIndependent H ![u, v]) (a : H) :
    projectiveAxis h a ∈ projectivePoints (Submodule.span H {u, v}) := by
  apply (projective_mk_mem_points _ _ _).mpr
  exact Submodule.add_mem _ (Submodule.subset_span (by simp))
    (Submodule.smul_mem _ a (Submodule.subset_span (by simp)))

/-- Suppose [ψ is a bijection preserving projective lines](hyp:hψ), [u and v are
linearly independent](hyp:h), [u′ and v′ are linearly independent](hyp:h'),
[u and v are nonzero](hyp:hu,hv), and [u′ and v′ are nonzero](hyp:hu',hv'). If
[ψ sends the point represented by u to that represented by u′](hyp:hpu) and
[ψ sends the point represented by v to that represented by v′](hyp:hpv), then
[there is a bijection τ between the scalar fields such that ψ sends every affine
axis point with coordinate a to the target axis point with coordinate τ of a](goal). -/
-- @node: projective_axis_coordinate_equiv
lemma projective_axis_coordinate_equiv
    {ψ : Projectivization H E → Projectivization C E'}
    (hψ : ProjectiveLiftBijection ψ)
    {u v : E} {u' v' : E'}
    (h : LinearIndependent H ![u, v]) (h' : LinearIndependent C ![u', v'])
    (hu : u ≠ 0) (hv : v ≠ 0) (hu' : u' ≠ 0) (hv' : v' ≠ 0)
    (hpu : ψ (Projectivization.mk H u hu) = Projectivization.mk C u' hu')
    (hpv : ψ (Projectivization.mk H v hv) = Projectivization.mk C v' hv') :
    ∃ τ : H ≃ C, ∀ a, ψ (projectiveAxis h a) = projectiveAxis h' (τ a) := by
  classical
  have hne : Projectivization.mk H u hu ≠ Projectivization.mk H v hv := by
    exact (Projectivization.independent_pair_iff_ne _ _).mp
      ((Projectivization.independent_mk_iff_LinearIndependent hu hv).mpr h)
  have him : ψ '' projectivePoints (Submodule.span H {u, v}) =
      projectivePoints (Submodule.span C {u', v'}) := by
    have ht := projective_line_image hψ hne
    simpa only [hpu, hpv, Projectivization.submodule_mk,
      ← Submodule.span_union, Set.singleton_union] using ht
  have hex (a : H) : ∃! b : C, projectiveAxis h' b = ψ (projectiveAxis h a) := by
    apply projectiveAxis_surjective_chart h' hv'
    · rw [← him]
      exact ⟨_, projectiveAxis_mem h a, rfl⟩
    · rw [← hpv]
      exact hψ.1.1.ne (projectiveAxis_ne_infinity h hv a)
  choose f hf huniq using hex
  have hfi : Function.Injective f := by
    intro a b hab
    apply projectiveAxis_injective h
    apply hψ.1.1
    rw [← hf, ← hf, hab]
  have hfs : Function.Surjective f := by
    intro b
    have hb := projectiveAxis_mem h' b
    rw [← him] at hb
    obtain ⟨x, hx, hpx⟩ := hb
    have hnx : x ≠ Projectivization.mk H v hv := by
      intro heq
      apply projectiveAxis_ne_infinity h' hv' b
      rw [← hpx, heq, hpv]
    obtain ⟨a, ha, _⟩ := projectiveAxis_surjective_chart h hv x hx hnx
    refine ⟨a, ?_⟩
    apply projectiveAxis_injective h'
    rw [hf, ha, hpx]
  exact ⟨Equiv.ofBijective f ⟨hfi, hfs⟩, fun a => (hf a).symm⟩

end Papers.OaiReconstructionMilnorTheory
