module

public import Papers.OaiCloseSeparableCstar.Helpers.Tree
public import Papers.OaiCloseSeparableCstar.Helpers.LpOperators
public import Papers.OaiCloseSeparableCstar.Helpers.AmbientCenter
public import Mathlib.SetTheory.Cardinal.Free
public import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-! # Lemma 7: the common ambient algebra and the close conjugating unitary -/

public section

open scoped Pointwise

namespace Papers.OaiCloseSeparableCstar

/-- If [a unitary conjugates every tensor generator of one representation to the
corresponding generator of another](hyp:hU), then [it conjugates their norm-closed
generated star algebras onto one another](goal). -/
-- @node: Palg_conj_of_generators
lemma Palg_conj_of_generators (σ τ : FG →* unitary (Op KSp))
    (U : unitary (Op LSp))
    (hU : ∀ g, (U : Op LSp) * Qop σ g * star (U : Op LSp) = Qop τ g) :
    conjSet (U : Op LSp) (Palg σ) = (Palg τ : Set _) := by
  let e := Unitary.conjStarAlgAut ℂ (Op LSp) U
  have hc : Continuous e := by
    change Continuous (fun x : Op LSp => (U : Op LSp) * x * star (U : Op LSp))
    fun_prop
  have hci : Continuous e.symm := by
    change Continuous (fun x : Op LSp => star (U : Op LSp) * x * (U : Op LSp))
    fun_prop
  let h : Op LSp ≃ₜ Op LSp :=
    { e.toEquiv with continuous_toFun := hc, continuous_invFun := hci }
  have he : IsClosedMap e := h.isClosedMap
  have hr : e '' Set.range (Qop σ) = Set.range (Qop τ) := by
    ext y
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, (hU g).symm⟩
    · rintro ⟨g, rfl⟩
      exact ⟨Qop σ g, ⟨g, rfl⟩, hU g⟩
  change ((Palg σ).map e.toStarAlgHom : Set (Op LSp)) = (Palg τ : Set (Op LSp))
  rw [Palg, ← StarSubalgebra.topologicalClosure_map _ _ he hc,
    StarAlgHom.map_adjoin]
  change ((StarAlgebra.adjoin ℂ (e '' Set.range (Qop σ))).topologicalClosure : Set (Op LSp)) = _
  rw [hr]
  rfl

/-- [The square-summable Hilbert space of the free group is nonzero](goal). -/
-- @node: KSp_nontrivial
lemma KSp_nontrivial : Nontrivial KSp := by
  refine ⟨⟨delta 1, 0, ?_⟩⟩
  intro h
  have he := congrArg (fun v : KSp => v 1) h
  simp [delta] at he

/-- [Conjugation by the absorption operator for a representation times the adjoint
of the zero-parameter absorption operator sends each zero-parameter tensor
generator to the corresponding generator of that representation](goal). -/
-- @node: absorption_relative_conjugates
lemma absorption_relative_conjugates (π : FG →* unitary (Op KSp)) (g : FG) :
    (absorptionOp π * star (absorptionOp piZero)) * Qop piZero g *
      star (absorptionOp π * star (absorptionOp piZero)) = Qop π g := by
  have h0 := absorption piZero KSp_nontrivial
  have hπ := absorption π KSp_nontrivial
  have h0g : Qop piZero g = absorptionOp piZero * shiftOp g *
      star (absorptionOp piZero) := (h0.2 g).symm
  rw [h0g, star_mul, star_star]
  simp only [mul_assoc, ← mul_assoc (star (absorptionOp piZero)) (absorptionOp piZero),
    Unitary.star_mul_self_of_mem h0.1, one_mul]
  exact hπ.2 g

/-- If [the bound C is nonnegative](hyp:hC) and [two unitary representations differ
in operator norm by at most C at every group element](hyp:hb), then [their absorption
operators differ in norm by at most C](goal). -/
-- @node: absorption_difference_norm_le
lemma absorption_difference_norm_le (π σ : FG →* unitary (Op KSp))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ g, ‖(π g : Op KSp) - (σ g : Op KSp)‖ ≤ C) :
    ‖absorptionOp π - absorptionOp σ‖ ≤ C := by
  have he : absorptionOp π - absorptionOp σ =
      diagOp (fun g => (π g : Op KSp) - (σ g : Op KSp)) C hb := by
    ext v g
    rfl
  rw [he]
  exact LinearMap.mkContinuous_norm_le _ hC _

/-- If [the deformation parameter t lies strictly between zero and one](hyp:ht) and
[the representation has generator coefficients t and the prescribed uniform
distance bound from the left regular representation](hyp:hπ), then [there is a
unitary conjugating the zero-parameter generated algebra onto the deformed one
whose distance from the identity is at most c(t)](goal). -/
-- @node: ambient_close_conjugating_unitary
lemma ambient_close_conjugating_unitary (t : ℝ) (ht : DeformationRange t)
    (π : FG →* unitary (Op KSp)) (hπ : IsTreeRep t ht π) :
    ∃ W ∈ unitary (Op LSp), conjSet W (Palg piZero) = (Palg π : Set _) ∧
      ‖W - 1‖ ≤ cBound t ht := by
  have h0 := (absorption piZero KSp_nontrivial).1
  have hπu := (absorption π KSp_nontrivial).1
  let W : unitary (Op LSp) := ⟨absorptionOp π * star (absorptionOp piZero),
    mul_mem hπu (Unitary.star_mem h0)⟩
  refine ⟨(W : Op LSp), W.property, Palg_conj_of_generators piZero π W
    (absorption_relative_conjugates π), ?_⟩
  have hC : 0 ≤ cBound t ht := (norm_nonneg _).trans (hπ.2 1)
  have he : (W : Op LSp) - 1 =
      (absorptionOp π - absorptionOp piZero) * star (absorptionOp piZero) := by
    rw [sub_mul, Unitary.mul_star_self_of_mem h0]
  rw [he, CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem h0)]
  exact absorption_difference_norm_le π piZero hC hπ.2

-- @node: lem:ambient
/-- If [t lies strictly between zero and one](hyp:ht) and [the representation has
generator coefficients t and the prescribed uniform distance bound from the left
regular representation](hyp:hπ), then [the ambient algebra has only scalar central
elements, its commutant consists exactly of first-factor operators commuting with
all left regular translations, and a unitary within c(t) of the identity conjugates
the zero-parameter generated algebra onto the deformed one](goal). -/
lemma ambient_properties (t : ℝ) (ht : DeformationRange t)
    (π : FG →* unitary (Op KSp)) (hπ : IsTreeRep t ht π) :
    SequencesCenter (Dalg π) ∧
    commutant (Dalg π) =
      {T | ∃ Y ∈ commutant (Set.range (fun g => (leftReg g : Op KSp))),
        T = flipOp * constantDiagOp Y * flipOp} ∧
    ∃ W ∈ unitary (Op LSp), -- @realizes W(unitary on the concrete space K⊗K)
      conjSet W (Palg piZero) = (Palg π : Set _) ∧ -- @realizes W(conjugates P_0 onto P_t)
      ‖W - 1‖ ≤ cBound t ht := by -- @realizes W(within c(t) of the ambient identity)
  refine ⟨?_, Dalg_commutant_eq π, ambient_close_conjugating_unitary t ht π hπ⟩
  exact Dalg_scalar_center π

/-- If [a set of bounded operators is countable](hyp:hs), then [the norm closure of
the complex star algebra it generates is separable](goal). -/
-- @node: countableStarAdjoin_isSeparable
lemma countableStarAdjoin_isSeparable (s : Set (Op LSp)) (hs : s.Countable) :
    TopologicalSpace.IsSeparable
      ((StarAlgebra.adjoin ℂ s).topologicalClosure : Set (Op LSp)) := by
  have hs' : (s ∪ star s).Countable :=
    hs.union (by simpa only [Set.image_star] using hs.image star)
  have := hs'.to_subtype
  have hm : (Submonoid.closure (s ∪ star s) : Set (Op LSp)).Countable := by
    rw [Submonoid.closure_eq_mrange, MonoidHom.coe_mrange]
    exact Set.countable_range _
  change TopologicalSpace.IsSeparable
    (closure (((StarAlgebra.adjoin ℂ s).toSubalgebra.toSubmodule) : Set (Op LSp)))
  rw [StarAlgebra.adjoin_eq_span]
  exact (hm.isSeparable.span (R := ℂ)).closure

/-- [The square-summable direct sum of a separable complex normed space over a
countable index set is separable](goal). -/
-- @node: separableSpace_hilbertSum
lemma separableSpace_hilbertSum (I V : Type*) [Countable I]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace.SeparableSpace V] :
    TopologicalSpace.SeparableSpace (lp (fun _ : I => V) 2) := by
  classical
  let F : Set (lp (fun _ : I => V) 2) := ⋃ i : I, Set.range (lp.single 2 i)
  have hF : TopologicalSpace.IsSeparable F := by
    apply TopologicalSpace.IsSeparable.iUnion
    intro i
    exact TopologicalSpace.isSeparable_range
      (lp.singleContinuousLinearMap ℂ (fun _ : I => V) 2 i).continuous
  apply TopologicalSpace.isSeparable_univ_iff.mp
  apply (hF.span (R := ℂ)).closure.mono
  intro v _
  apply isClosed_closure.mem_of_tendsto (lp.hasSum_single (by norm_num) v)
  apply Filter.Eventually.of_forall
  intro s
  apply subset_closure
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.subset_span
  exact Set.mem_iUnion.mpr ⟨i, v i, rfl⟩

/-- [The ambient algebra generated by a unitary representation is norm closed and
norm separable](goal). -/
-- @node: Dalg_closed_separable
lemma Dalg_closed_separable (π : FG →* unitary (Op KSp)) : SequencesD (Dalg π) := by
  refine ⟨StarSubalgebra.isClosed_topologicalClosure _, ?_⟩
  apply countableStarAdjoin_isSeparable
  exact (((Set.countable_range _).union (Set.countable_range _)).union
    (Set.countable_range _)).union (Set.countable_range _)

/-- [The zero-parameter and deformed generated algebras are both norm-closed
subalgebras of the common ambient algebra](goal). -/
-- @node: Palg_inclusions
lemma Palg_inclusions (π : FG →* unitary (Op KSp)) :
    SequencesSubalgebras (Dalg π) (Palg piZero) (Palg π) := by
  have hgen (σ : FG →* unitary (Op KSp))
      (hσ : ∀ g, constantDiagOp (σ g : Op KSp) ∈ Dalg π) : Palg σ ≤ Dalg π := by
    apply StarSubalgebra.topologicalClosure_minimal
    · apply StarAlgebra.adjoin_le
      rintro _ ⟨g, rfl⟩
      change shiftOp g * constantDiagOp (σ g : Op KSp) ∈ Dalg π
      apply (Dalg π).mul_mem _ (hσ g)
      apply StarSubalgebra.le_topologicalClosure
      apply StarAlgebra.subset_adjoin
      exact Or.inl (Or.inl (Or.inl ⟨g, rfl⟩))
    · exact StarSubalgebra.isClosed_topologicalClosure _
  refine ⟨hgen piZero ?_, hgen π ?_,
    StarSubalgebra.isClosed_topologicalClosure _,
    StarSubalgebra.isClosed_topologicalClosure _⟩
  · intro g
    apply StarSubalgebra.le_topologicalClosure
    apply StarAlgebra.subset_adjoin
    exact Or.inl (Or.inl (Or.inr ⟨g, rfl⟩))
  · intro g
    apply StarSubalgebra.le_topologicalClosure
    apply StarAlgebra.subset_adjoin
    exact Or.inl (Or.inr ⟨g, rfl⟩)

/-- [The concrete Hilbert space of square-summable, square-summable-vector-valued
functions on the free group is nonzero and separable](goal). -/
-- @node: LSp_nonzero_separable
lemma LSp_nonzero_separable : SequencesL LSp := by
  have hne : (lp.single 2 (1 : FG) (delta 1) : LSp) ≠ 0 := by
    intro h
    have he := congrArg (fun v : LSp => v 1 1) h
    simp [delta] at he
  refine ⟨⟨⟨_, 0, hne⟩⟩, ?_⟩
  have : TopologicalSpace.SeparableSpace KSp := separableSpace_hilbertSum FG ℂ
  exact separableSpace_hilbertSum FG KSp

end Papers.OaiCloseSeparableCstar
