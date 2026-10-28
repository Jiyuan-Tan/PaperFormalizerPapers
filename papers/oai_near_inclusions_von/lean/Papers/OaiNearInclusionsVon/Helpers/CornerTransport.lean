module

public import Papers.OaiNearInclusionsVon.Helpers.CornerFinalization

/-! Transport of commuting unitary approximants across Hilbert space identifications. -/

public section

set_option linter.style.longLine false

namespace Papers.OaiNearInclusionsVon

open Filter
open scoped Topology

-- @node: starAlgEquiv_unitary_commuting_pair
/-- Under [an isomorphism of bounded-operator algebras preserving complex scalars and
adjoints](hyp:f), if [the operator U](hyp:U) [is unitary](hyp:hU), [the operator V](hyp:V)
[is unitary](hyp:hV), and [U and V commute](hyp:hUV), then
[their images are unitary and commute with each other](goal). -/
lemma starAlgEquiv_unitary_commuting_pair
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (f : (E →L[ℂ] E) ≃⋆ₐ[ℂ] (F →L[ℂ] F)) (U V : E →L[ℂ] E)
    (hU : U ∈ unitary _) (hV : V ∈ unitary _) (hUV : Commute U V) :
    f U ∈ unitary _ ∧ f V ∈ unitary _ ∧ Commute (f U) (f V) := by
  exact ⟨Unitary.map_mem f hU, Unitary.map_mem f hV, hUV.map f⟩

-- @node: starAlgEquiv_operator_norm_sub
/-- For [an isomorphism of bounded-operator algebras preserving complex scalars and
adjoints](hyp:f) and [two bounded operators U and V](hyp:U,V),
[the operator-norm distance between their images equals the operator-norm distance
between U and V](goal). -/
lemma starAlgEquiv_operator_norm_sub
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (f : (E →L[ℂ] E) ≃⋆ₐ[ℂ] (F →L[ℂ] F)) (U V : E →L[ℂ] E) :
    ‖f U - f V‖ = ‖U - V‖ := by
  rw [← map_sub, StarAlgEquiv.norm_map]

-- @node: unitary_approximants_transport
/-- Given [a sequence of isometric linear identifications from source Hilbert spaces
to target Hilbert spaces](hyp:e), [target operator sequences C1 and C2 with approximating
sequences R₁ and R₂](hyp:C1,C2,R₁,R₂), and [source operator sequences U and V](hyp:U,V),
suppose [C1 transports back to U at every index](hyp:hC₁),
[C2 transports back to V at every index](hyp:hC₂),
[R₁ and R₂ are commuting unitaries for all sufficiently large indices](hyp:hu),
[R₁ converges to C1 in operator-norm error](hyp:h₁), and
[R₂ converges to C2 in operator-norm error](hyp:h₂).
Then [there are source operator sequences that are commuting unitaries at every index
and whose summed operator-norm errors relative to U and V tend to zero](goal). -/
lemma unitary_approximants_transport
    {K D : ℕ → Type*}
    [∀ k, NormedAddCommGroup (K k)] [∀ k, InnerProductSpace ℂ (K k)]
    [∀ k, CompleteSpace (K k)]
    [∀ k, NormedAddCommGroup (D k)] [∀ k, InnerProductSpace ℂ (D k)]
    [∀ k, CompleteSpace (D k)]
    (e : ∀ k, D k ≃ₗᵢ[ℂ] K k)
    (C1 C2 R₁ R₂ : ∀ k, K k →L[ℂ] K k)
    (U V : ∀ k, D k →L[ℂ] D k)
    (hC₁ : ∀ k, (e k).conjStarAlgEquiv.symm (C1 k) = U k)
    (hC₂ : ∀ k, (e k).conjStarAlgEquiv.symm (C2 k) = V k)
    (hu : ∀ᶠ k in atTop, R₁ k ∈ unitary _ ∧ R₂ k ∈ unitary _ ∧ Commute (R₁ k) (R₂ k))
    (h₁ : Tendsto (fun k => ‖R₁ k - C1 k‖) atTop (𝓝 0))
    (h₂ : Tendsto (fun k => ‖R₂ k - C2 k‖) atTop (𝓝 0)) :
    ∃ Uhat Vhat : ∀ k, D k →L[ℂ] D k,
      (∀ k, Uhat k ∈ unitary _ ∧ Vhat k ∈ unitary _ ∧ Commute (Uhat k) (Vhat k)) ∧
      Tendsto (fun k => ‖Uhat k - U k‖ + ‖Vhat k - V k‖) atTop (𝓝 0) := by
  classical
  let f := fun k => (e k).conjStarAlgEquiv.symm
  let good := fun k => R₁ k ∈ unitary _ ∧ R₂ k ∈ unitary _ ∧ Commute (R₁ k) (R₂ k)
  let Uhat := fun k => if good k then f k (R₁ k) else 1
  let Vhat := fun k => if good k then f k (R₂ k) else 1
  refine ⟨Uhat, Vhat, ?_, ?_⟩
  · intro k
    by_cases hk : good k
    · simp only [Uhat, Vhat, if_pos hk]
      with_reducible exact (starAlgEquiv_unitary_commuting_pair
        (E := K k)
        (F := D k) (f k) (R₁ k) (R₂ k) hk.1 hk.2.1 hk.2.2)
    · simp only [Uhat, Vhat, if_neg hk]
      exact ⟨one_mem _, one_mem _, Commute.one_left _⟩
  · have he₁ (k : ℕ) : ‖f k (R₁ k) - U k‖ =
        ‖R₁ k - C1 k‖ := by
      have hid := hC₁ k
      change f k _ = U k at hid
      refine (congrArg (fun X => ‖f k (R₁ k) - X‖) hid.symm).trans ?_
      with_reducible exact (starAlgEquiv_operator_norm_sub
        (E := K k)
        (F := D k) (f k) _ _)
    have he₂ (k : ℕ) : ‖f k (R₂ k) - V k‖ =
        ‖R₂ k - C2 k‖ := by
      have hid := hC₂ k
      change f k _ = V k at hid
      refine (congrArg (fun X => ‖f k (R₂ k) - X‖) hid.symm).trans ?_
      with_reducible exact (starAlgEquiv_operator_norm_sub
        (E := K k)
        (F := D k) (f k) _ _)
    have he : (fun k => ‖Uhat k - U k‖ + ‖Vhat k - V k‖) =ᶠ[atTop]
        (fun k => ‖R₁ k - C1 k‖ +
          ‖R₂ k - C2 k‖) := by
      filter_upwards [hu] with k hk
      have hU : Uhat k = f k (R₁ k) := if_pos hk
      have hV : Vhat k = f k (R₂ k) := if_pos hk
      exact (congrArg₂ (fun X Y : D k →L[ℂ] D k =>
        ‖X - U k‖ + ‖Y - V k‖) hU hV).trans
          (congrArg₂ (fun x y : ℝ => x + y) (he₁ k) (he₂ k))
    simpa only [add_zero] using (h₁.add h₂).congr' he.symm

-- @node: corner_commuting_approximants_transport
/-- Given [operator sequences E₁ and E₂ defining corners, R₁ and R₂ to be restricted,
and approximants T₁ and T₂](hyp:E₁,E₂,R₁,R₂,T₁,T₂), and
[two sequences of von Neumann algebras A₁ and A₂](hyp:A₁,A₂), assume
[E₁ and E₂ are commuting orthogonal projections at each index](hyp:hE),
[their common ranges are nonzero and finite dimensional](hyp:hD),
[R₁ and R₂ are unitaries commuting with both projections](hyp:hR),
[every element of A₁ commutes with every element of A₂ at each index](hyp:hA), and
[T₁ and T₂ belong to their respective algebras and approximate E₁R₁ and E₂R₂
in operator norm as the index grows](hyp:hT).
For [isometric linear identifications of abstract Hilbert spaces with the common
ranges](hyp:e) and [operator sequences U and V on those abstract spaces](hyp:U,V), if
[the identifications intertwine U with the corner restriction of R₁](hyp:hC₁) and
[intertwine V with the corner restriction of R₂](hyp:hC₂), then
[there exist commuting unitary pairs at every index whose summed operator-norm errors
relative to U and V tend to zero](goal). -/
lemma corner_commuting_approximants_transport
    {H D : ℕ → Type*}
    [∀ k, NormedAddCommGroup (H k)] [∀ k, InnerProductSpace ℂ (H k)]
    [∀ k, CompleteSpace (H k)]
    [∀ k, NormedAddCommGroup (D k)] [∀ k, InnerProductSpace ℂ (D k)]
    [∀ k, CompleteSpace (D k)]
    (E₁ E₂ R₁ R₂ T₁ T₂ : ∀ k, H k →L[ℂ] H k)
    (A₁ A₂ : ∀ k, VonNeumannAlgebra (H k))
    (hE : CornerProjections E₁ E₂) (hD : CornerDimension E₁ E₂)
    (hR : CornerUnitaries E₁ E₂ R₁ R₂) (hA : CornerAlgebras A₁ A₂)
    (hT : CornerApproximation A₁ A₂ T₁ T₂ E₁ E₂ R₁ R₂)
    (e : ∀ k, D k ≃ₗᵢ[ℂ] cornerRange E₁ E₂ k)
    (U V : ∀ k, D k →L[ℂ] D k)
    (hC₁ : ∀ k x, cornerRestrict E₁ E₂ R₁ k (e k x) = e k (U k x))
    (hC₂ : ∀ k x, cornerRestrict E₁ E₂ R₂ k (e k x) = e k (V k x)) :
    ∃ Uhat Vhat : ∀ k, D k →L[ℂ] D k,
      (∀ k, Uhat k ∈ unitary _ ∧ Vhat k ∈ unitary _ ∧ Commute (Uhat k) (Vhat k)) ∧
      Tendsto (fun k => ‖Uhat k - U k‖ + ‖Vhat k - V k‖) atTop (𝓝 0) := by
  letI : ∀ k, FiniteDimensional ℂ (cornerRange E₁ E₂ k) := fun k => (hD k).2
  obtain ⟨S₁, S₂, hu, h₁, h₂⟩ :=
    corner_commuting_approximants E₁ E₂ R₁ R₂ T₁ T₂ A₁ A₂ hE hD hR hA hT
  letI : ∀ k, CompleteSpace (cornerRange E₁ E₂ k) := fun k =>
    (e k).toIsometryEquiv.completeSpace_iff.mp inferInstance
  have hc₁ (k : ℕ) : (e k).conjStarAlgEquiv.symm (cornerRestrict E₁ E₂ R₁ k) = U k := by
    ext x
    apply (e k).injective
    simp only [LinearIsometryEquiv.symm_conjStarAlgEquiv_apply_apply,
      LinearIsometryEquiv.apply_symm_apply]
    exact hC₁ k x
  have hc₂ (k : ℕ) : (e k).conjStarAlgEquiv.symm (cornerRestrict E₁ E₂ R₂ k) = V k := by
    ext x
    apply (e k).injective
    simp only [LinearIsometryEquiv.symm_conjStarAlgEquiv_apply_apply,
      LinearIsometryEquiv.apply_symm_apply]
    exact hC₂ k x
  exact unitary_approximants_transport (K := fun k => cornerRange E₁ E₂ k) (D := D) e
    (cornerRestrict E₁ E₂ R₁) (cornerRestrict E₁ E₂ R₂) S₁ S₂ U V hc₁ hc₂ hu h₁ h₂

end Papers.OaiNearInclusionsVon
