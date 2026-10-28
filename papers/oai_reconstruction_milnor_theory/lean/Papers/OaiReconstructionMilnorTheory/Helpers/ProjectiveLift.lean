module

public import Papers.OaiReconstructionMilnorTheory.Helpers.ProjectiveAssembly

/-! # Semilinear lifts of projective collineations -/

@[expose] public section

namespace Papers.OaiReconstructionMilnorTheory

variable {H C E E' : Type*} [Field H] [Field C]
  [AddCommGroup E] [Module H E] [AddCommGroup E'] [Module C E']

/-- If [the source and target vector spaces are finite-dimensional and each has
dimension at least three](hyp:hspaces), and [a projective map is bijective and
maps lines onto lines](hyp:hψ), [there exist an isomorphism of the scalar fields
and an additive bijection of the vector spaces that respects scalar
multiplication through that isomorphism and sends every nonzero vector into
the one-dimensional subspace specified by its projective image](goal). -/
-- @node: projective_lift_exists
lemma projective_lift_exists (ψ : Projectivization H E → Projectivization C E')
    (hspaces : ProjectiveLiftSpaces H C E E') (hψ : ProjectiveLiftBijection ψ) :
    ∃ σ : H ≃+* C, ∃ S : E ≃+ E',
      (∀ (a : H) v, S (a • v) = σ a • S v) ∧
      (∀ v (hv : v ≠ 0), S v ∈ (ψ (Projectivization.mk H v hv)).submodule) := by
  let : FiniteDimensional H E := hspaces.1
  have hn : 3 ≤ Module.finrank H E := hspaces.2.2.1
  let b := Module.finBasis H E
  let o : Fin (Module.finrank H E) := ⟨0, by omega⟩
  let i : Fin (Module.finrank H E) := ⟨1, by omega⟩
  let j : Fin (Module.finrank H E) := ⟨2, by omega⟩
  have hoi : o ≠ i := by simp [o, i]
  have hoj : o ≠ j := by simp [o, j]
  have hij : i ≠ j := by simp [i, j]
  obtain ⟨b', σ, hp, ht⟩ := projective_frame_field_equiv hψ b o i j hoi hoj hij
  exact ⟨σ, projectiveFrameLift b b' σ, projectiveFrameLift_smul b b' σ,
    projectiveFrameLift_mem hψ b b' hp o σ ht⟩

-- @node: prop:projective-lift
/-- If [the source and target vector spaces are finite-dimensional and each has
dimension at least three](hyp:hspaces), and [a projective map is bijective and
maps lines onto lines](hyp:hψ), [there exist a scalar-field isomorphism and an
additive bijection respecting scalar multiplication through that isomorphism
and inducing the projective map; every other such pair has the same field
isomorphism and an additive bijection differing by one common nonzero target
scalar](goal). -/
lemma projective_lift (ψ : Projectivization H E → Projectivization C E')
    (hspaces : ProjectiveLiftSpaces H C E E') (hψ : ProjectiveLiftBijection ψ) :
    ∃ σ : H ≃+* C, -- @realizes \sigma(field isomorphism)
    ∃ S : E ≃+ E', -- @realizes S(additive bijection)
      (∀ (a : H) v, S (a • v) = σ a • S v) ∧ -- @realizes S(σ-semilinear)
      (∀ v (hv : v ≠ 0),
        S v ∈ (ψ (Projectivization.mk H v hv)).submodule) ∧ -- @realizes S(induces ψ)
      ∀ (σ' : H ≃+* C) (S' : E ≃+ E'),
        (∀ (a : H) v, S' (a • v) = σ' a • S' v) →
        (∀ v (hv : v ≠ 0), S' v ∈ (ψ (Projectivization.mk H v hv)).submodule) →
        σ' = σ ∧ ∃ c : Cˣ, -- @realizes c(common nonzero target scalar)
          ∀ v, S' v = (c : C) • S v := by
  obtain ⟨σ, S, hS, hproj⟩ := projective_lift_exists ψ hspaces hψ
  let : FiniteDimensional C E' := hspaces.2.1
  refine ⟨σ, S, hS, hproj, ?_⟩
  intro σ' S' hS' hproj'
  exact projective_lift_unique (by have := hspaces.2.2.2; omega)
    ψ σ σ' S S' hS hS' hproj hproj'

end Papers.OaiReconstructionMilnorTheory
