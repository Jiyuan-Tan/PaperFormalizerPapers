module
public import Papers.TbsNeuralCausalPi.Helpers.AntipodalRadial
public import Toolkit.Foundations.Topology.SimplicialAction
public import Mathlib.Data.ZMod.Basic
/-! # The free antipodal action on the signed sphere

The cyclic group of order two acts by the identity and negation. Its target
representation is the same sign action, in every real target dimension.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi.Antipodal
noncomputable section
open Toolkit.Foundations.Topology

-- @node: AntipodalGroup
/-- The [antipodal group](goal) is the two-element cyclic group, written multiplicatively. -/
abbrev AntipodalGroup := Multiplicative (ZMod 2)

-- @node: antipodalRepresentation
/-- On [a real vector space](hyp:F), the [antipodal representation](goal)
sends the identity of the two-element group to the identity transformation and its other element to negation. -/
def antipodalRepresentation (F : Type*) [AddCommGroup F] [Module ℝ F] :
    AntipodalGroup →* (F ≃ₗ[ℝ] F) where
  toFun g := if g = 1 then LinearEquiv.refl ℝ F else LinearEquiv.neg ℝ
  map_one' := by
    apply LinearEquiv.ext
    intro x
    simp
  map_mul' := by
    intro g h
    by_cases hg : g = 1
    · subst g
      simp
      rfl
    by_cases hh : h = 1
    · subst h
      simp
      rfl
    have hgh : g * h = 1 :=
      (show ∀ a b : AntipodalGroup, a ≠ 1 → b ≠ 1 → a * b = 1 from by decide) g h hg hh
    simp only [hgh, if_neg hg, if_neg hh]
    apply LinearEquiv.ext
    intro x
    simp

-- @node: antipodalRepresentation_one
/-- [The identity element of the antipodal group fixes every vector in any real vector space under the antipodal representation](goal). -/
lemma antipodalRepresentation_one (F : Type*) [AddCommGroup F] [Module ℝ F] (x : F) :
    antipodalRepresentation F 1 x = x := by
  simp [antipodalRepresentation]

-- @node: antipodalRepresentation_nonidentity
/-- If [a group element is not the identity](hyp:hg),
[its antipodal representation sends every vector in a real vector space to its negative](goal). -/
lemma antipodalRepresentation_nonidentity (F : Type*) [AddCommGroup F] [Module ℝ F]
    {g : AntipodalGroup} (hg : g ≠ 1) (x : F) :
    antipodalRepresentation F g x = -x := by
  simp [antipodalRepresentation, hg]

-- @node: signedAntipodalAction
/-- For [an ambient dimension](hyp:n), the [signed antipodal action](goal)
is the action of the two-element group on the signed geometric complex by identity and coordinatewise negation, preserving faces and acting affinely on each face. -/
def signedAntipodalAction (n : ℕ) :
    SimplicialAction AntipodalGroup (signedGeometricComplex n) where
  action :=
    { toFun := fun g => (antipodalRepresentation (Fin n → ℝ) g).toEquiv
      map_one' := by
        apply Equiv.ext
        intro x
        exact antipodalRepresentation_one _ x
      map_mul' := by
        intro g h
        apply Equiv.ext
        intro x
        exact congrArg (fun e : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) => e x)
          ((antipodalRepresentation (Fin n → ℝ)).map_mul g h) }
  face_image := by
    classical
    intro g s hs
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, LinearEquiv.coe_toEquiv]
    by_cases hg : g = 1
    · subst g
      have he : ⇑(antipodalRepresentation (Fin n → ℝ) 1) = id :=
        funext (antipodalRepresentation_one _)
      rw [he]
      convert hs using 1
      ext x
      simp
    · have he : ⇑(antipodalRepresentation (Fin n → ℝ) g) = Neg.neg :=
        funext (antipodalRepresentation_nonidentity _ hg)
      rw [he]
      convert signedGeometricComplex_neg_face hs using 1
      ext x
      simp only [Finset.mem_image]
  affine_on_face := by
    intro g s hs
    exact ⟨(antipodalRepresentation (Fin n → ℝ) g).toLinearMap.toAffineMap,
      fun _ _ => rfl⟩

-- @node: signedAntipodalAction_onSpace_one
/-- [The identity element of the antipodal group fixes every point of the signed geometric complex](goal). -/
lemma signedAntipodalAction_onSpace_one {n : ℕ} (x : (signedGeometricComplex n).space) :
    (signedAntipodalAction n).onSpace 1 x = x := by
  apply Subtype.ext
  exact antipodalRepresentation_one _ x.val

-- @node: signedAntipodalAction_onSpace_nonidentity
/-- If [an antipodal group element is not the identity](hyp:hg),
[its action on any point of the signed geometric complex is coordinatewise negation](goal). -/
lemma signedAntipodalAction_onSpace_nonidentity {n : ℕ} {g : AntipodalGroup}
    (hg : g ≠ 1) (x : (signedGeometricComplex n).space) :
    (signedAntipodalAction n).onSpace g x =
      ⟨-x.val, signedGeometricComplex_neg_mem x.property⟩ := by
  apply Subtype.ext
  exact antipodalRepresentation_nonidentity _ hg x.val

-- @node: signedAntipodalAction_isFree
/-- [The antipodal action on the signed geometric complex is free in every ambient dimension: only the identity group element can fix a point](goal). -/
lemma signedAntipodalAction_isFree (n : ℕ) : (signedAntipodalAction n).IsFree := by
  intro g x hx
  by_contra hg
  apply signedGeometricComplex_ne_antipode x.property
  have he := congrArg Subtype.val hx
  change antipodalRepresentation (Fin n → ℝ) g x.val = x.val at he
  rw [antipodalRepresentation_nonidentity _ hg] at he
  exact he.symm

-- @node: odd_signedSphere_equivariant
/-- If [a function from the unit sphere to a real normed vector space is odd, sending the negative of each point to the negative of its value](hyp:hodd),
[transporting that function to the signed geometric complex through the sphere homeomorphism gives an equivariant map for the antipodal actions on the domain and target](goal). -/
lemma odd_signedSphere_equivariant {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Metric.sphere (0 : Fin n → ℝ) 1 → F) (hodd : ∀ x, f (-x) = -f x) :
    Equivariant (signedAntipodalAction n) (antipodalRepresentation F)
      (fun x => f (signedSphereHomeomorph n x)) := by
  intro g x
  change f (signedSphereHomeomorph n ((signedAntipodalAction n).onSpace g x)) =
    antipodalRepresentation F g (f (signedSphereHomeomorph n x))
  by_cases hg : g = 1
  · subst g
    rw [signedAntipodalAction_onSpace_one, antipodalRepresentation_one]
  · rw [signedAntipodalAction_onSpace_nonidentity hg, signedSphereHomeomorph_antipode,
      hodd, antipodalRepresentation_nonidentity _ hg]

end
end Papers.TbsNeuralCausalPi.Antipodal
