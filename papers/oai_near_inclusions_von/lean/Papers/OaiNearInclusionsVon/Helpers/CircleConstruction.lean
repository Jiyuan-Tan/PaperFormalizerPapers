module

public import Papers.OaiNearInclusionsVon.Helpers.MainJointLimits
public import Papers.OaiNearInclusionsVon.ReusedTree.Helpers.TreePerturbation

/-! The circle twist of the real tree representation and its generator limit. -/

@[expose] public section

namespace Papers.OaiNearInclusionsVon

open Filter

open scoped Topology

-- @node: circle_deformation_range
/-- [The fixed deformation parameter lies strictly between zero and one](goal). -/
lemma circle_deformation_range :
    Papers.OaiNearInclusionsVon.ReusedTree.DeformationRange tParam := by
  norm_num [Papers.OaiNearInclusionsVon.ReusedTree.DeformationRange, tParam]

-- @node: circleCharacter
/-- For [a point z on the unit circle](hyp:z), the [circle character](goal) is the
group homomorphism from the free group to the unit circle that sends every free
generator to z. -/
noncomputable def circleCharacter (z : Circle) : FreeGrp →* Circle :=
  FreeGroup.lift (fun _ : ℕ => z)

-- @node: circleCharacter_gen
/-- For [a point z on the unit circle](hyp:z) and [a generator index j](hyp:j),
[the circle character evaluated at the j-th generator equals z](goal). -/
@[simp] lemma circleCharacter_gen (z : Circle) (j : ℕ) :
    circleCharacter z (gen j) = z := FreeGroup.lift_apply_of

-- @node: circleScalarUnitary
/-- For [a complex Hilbert space E](hyp:E) and [a point z on the unit circle](hyp:z),
the [scalar unitary](goal) is the unitary operator on E given by multiplication by z. -/
noncomputable def circleScalarUnitary
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (z : Circle) :
    unitary (E →L[ℂ] E) := by
  refine ⟨(z : ℂ) • 1, ?_⟩
  rw [Unitary.mem_iff]
  have hz : star (z : ℂ) = (z : ℂ)⁻¹ := (Circle.coe_inv_eq_conj z).symm
  constructor <;>
    simp [star_smul, hz, smul_smul]

-- @node: circleDiagonal
/-- For [a point z on the unit circle](hyp:z), the [circle diagonal unitary](goal)
multiplies the coordinate at each free-group element by the inverse of its circle
character value. -/
noncomputable def circleDiagonal (z : Circle) : unitary (TreeSpace →L[ℂ] TreeSpace) :=
  ⟨Papers.OaiNearInclusionsVon.ReusedTree.diagUnitaryOp
    (fun x : FreeGrp => circleScalarUnitary ℂ (circleCharacter z x)⁻¹),
    Papers.OaiNearInclusionsVon.ReusedTree.diagUnitaryOp_mem_unitary _⟩

-- @node: circleDiagonal_apply
/-- For [a circle point z](hyp:z), [a vector v in the tree Hilbert space](hyp:v), and
[a free-group element x](hyp:x), [the x-coordinate of the circle diagonal applied
to v is the x-coordinate of v multiplied by the inverse character value at x](goal). -/
lemma circleDiagonal_apply (z : Circle) (v : TreeSpace) (x : FreeGrp) :
    (circleDiagonal z : TreeSpace →L[ℂ] TreeSpace) v x =
      ((circleCharacter z x : Circle) : ℂ)⁻¹ * v x := rfl

-- @node: circleDiagonal_basis
/-- For [a circle point z](hyp:z) and [a free-group element x](hyp:x), [the circle
diagonal multiplies the basis vector at x by the inverse character value at x](goal). -/
lemma circleDiagonal_basis (z : Circle) (x : FreeGrp) :
    (circleDiagonal z : TreeSpace →L[ℂ] TreeSpace) (treeBasis x) =
      ((circleCharacter z x : Circle) : ℂ)⁻¹ • treeBasis x := by
  classical
  ext y
  rw [circleDiagonal_apply]
  by_cases h : x = y <;> simp [treeBasis, lp.single_apply, h]

-- @node: circleDiagonal_inv_basis
/-- For [a circle point z](hyp:z) and [a free-group element x](hyp:x), [the adjoint
of the circle diagonal multiplies the basis vector at x by the character value at x](goal). -/
lemma circleDiagonal_inv_basis (z : Circle) (x : FreeGrp) :
    star (circleDiagonal z : TreeSpace →L[ℂ] TreeSpace) (treeBasis x) =
      ((circleCharacter z x : Circle) : ℂ) • treeBasis x := by
  have h := congrArg (fun U : TreeSpace →L[ℂ] TreeSpace => U (treeBasis x))
    (Unitary.coe_star_mul_self (circleDiagonal z))
  change star (circleDiagonal z : TreeSpace →L[ℂ] TreeSpace)
    ((circleDiagonal z : TreeSpace →L[ℂ] TreeSpace) (treeBasis x)) = treeBasis x at h
  rw [circleDiagonal_basis, map_smul] at h
  have h' := congrArg (fun v : TreeSpace => ((circleCharacter z x : Circle) : ℂ) • v) h
  simpa only [smul_smul, mul_inv_cancel₀ (Circle.coe_ne_zero _), one_smul] using h'

-- @node: circleTreeRep
/-- The [circle tree representation](goal) assigns to each circle point the unitary
representation obtained by conjugating the fixed real tree representation by the
circle diagonal and multiplying each group operator by its circle character value. -/
noncomputable def circleTreeRep : CircleRep := fun z =>
  { toFun := fun g => circleScalarUnitary TreeSpace (circleCharacter z g) *
      circleDiagonal z *
      Papers.OaiNearInclusionsVon.ReusedTree.treeUnitaryRep tParam circle_deformation_range g *
      (circleDiagonal z)⁻¹
    map_one' := by
      apply Subtype.ext
      simp [circleScalarUnitary]
    map_mul' := by
      intro g h
      apply Subtype.ext
      simp only [map_mul, Submonoid.coe_mul, circleScalarUnitary,
        Circle.coe_mul, mul_smul, smul_mul_assoc, mul_smul_comm, one_mul]
      simp only [← Unitary.star_eq_inv, Unitary.coe_star, mul_assoc]
      rw [← mul_assoc (star (circleDiagonal z : TreeSpace →L[ℂ] TreeSpace))
        (circleDiagonal z : TreeSpace →L[ℂ] TreeSpace),
        Unitary.coe_star_mul_self, one_mul]
      exact smul_comm _ _ _ }

-- @node: circleTreeRep_apply
/-- For [a circle point z](hyp:z), [a free-group element g](hyp:g), and [a tree-space
vector v](hyp:v), [the circle tree operator at g sends v through the adjoint circle
diagonal, then the real tree operator at g, then the circle diagonal, and multiplies
the result by the character value at g](goal). -/
lemma circleTreeRep_apply (z : Circle) (g : FreeGrp) (v : TreeSpace) :
    (circleTreeRep z g : TreeSpace →L[ℂ] TreeSpace) v =
      ((circleCharacter z g : Circle) : ℂ) •
        (circleDiagonal z : TreeSpace →L[ℂ] TreeSpace)
          ((Papers.OaiNearInclusionsVon.ReusedTree.treeUnitaryRep tParam circle_deformation_range g :
            TreeSpace →L[ℂ] TreeSpace)
            (star (circleDiagonal z : TreeSpace →L[ℂ] TreeSpace) v)) := rfl

-- @node: realTreeRep_basis_identity
/-- For [a generator index j](hyp:j), [the real tree operator at the j-th generator
sends the identity basis vector to the deformation parameter times that vector
plus the complementary parameter times the basis vector at the j-th generator](goal). -/
lemma realTreeRep_basis_identity (j : ℕ) :
    (Papers.OaiNearInclusionsVon.ReusedTree.treeUnitaryRep tParam circle_deformation_range (gen j) :
      TreeSpace →L[ℂ] TreeSpace) (treeBasis 1) =
        (tParam : ℂ) • treeBasis 1 + (rParam : ℂ) • treeBasis (gen j) := by
  have h := Papers.OaiNearInclusionsVon.ReusedTree.treeUnitaryRep_treeVector
    tParam circle_deformation_range (gen j) 1
  simpa [Papers.OaiNearInclusionsVon.ReusedTree.treeVector_one,
    Papers.OaiNearInclusionsVon.ReusedTree.treeVector,
    Papers.OaiNearInclusionsVon.ReusedTree.treeWordVector,
    Papers.OaiNearInclusionsVon.ReusedTree.rValue, gen, treeBasis,
    Papers.OaiNearInclusionsVon.ReusedTree.delta, rParam, FreeGroup.of] using h

-- @node: circleTreeRep_gen_basis_identity
/-- For [a circle point z](hyp:z) and [a generator index j](hyp:j), [the circle tree
operator at the j-th generator sends the identity basis vector to the deformation
parameter times z times that vector plus the complementary parameter times the
basis vector at the j-th generator](goal). -/
lemma circleTreeRep_gen_basis_identity (z : Circle) (j : ℕ) :
    (circleTreeRep z (gen j) : TreeSpace →L[ℂ] TreeSpace) (treeBasis 1) =
      ((tParam : ℂ) * (z : ℂ)) • treeBasis 1 + (rParam : ℂ) • treeBasis (gen j) := by
  rw [circleTreeRep_apply, circleDiagonal_inv_basis]
  simp only [map_one, Circle.coe_one, one_smul, realTreeRep_basis_identity,
    map_add, map_smul, circleDiagonal_basis, circleCharacter_gen, smul_add, smul_smul]
  congr 1 <;> congr 1 <;> field_simp

-- @node: realTreeRep_gen_basis_off_path
/-- For [a generator index j](hyp:j) and [a free-group element x](hyp:x), if
[the product of the j-th generator with x is not the identity](hyp:h₁) and
[is not the j-th generator](hyp:h₂), then [the real tree operator at that generator
sends the basis vector at x to the basis vector at their product](goal). -/
lemma realTreeRep_gen_basis_off_path (j : ℕ) (x : FreeGrp)
    (h₁ : gen j * x ≠ 1) (h₂ : gen j * x ≠ gen j) :
    (Papers.OaiNearInclusionsVon.ReusedTree.treeUnitaryRep tParam circle_deformation_range (gen j) :
      TreeSpace →L[ℂ] TreeSpace) (treeBasis x) = treeBasis (gen j * x) := by
  have hp : ¬ (gen j * x).toWord.IsPrefix (gen j).toWord := by
    intro hp
    have hw : (gen j).toWord = [(j, true)] := by simp [gen]
    rw [hw] at hp
    rcases List.prefix_cons_iff.mp hp with h | ⟨w, he, hw⟩
    · apply h₁
      simpa only [FreeGroup.mk_toWord, ← FreeGroup.one_eq_mk] using congrArg FreeGroup.mk h
    · have : w = [] := List.prefix_nil.mp hw
      apply h₂
      simpa only [this, FreeGroup.mk_toWord, gen, FreeGroup.of] using congrArg FreeGroup.mk he
  have h := Papers.OaiNearInclusionsVon.ReusedTree.treePerturbation_delta_of_not_prefix
    tParam circle_deformation_range (gen j) (gen j * x) hp
  change (Papers.OaiNearInclusionsVon.ReusedTree.treeUnitaryRep tParam circle_deformation_range
    (gen j) : TreeSpace →L[ℂ] TreeSpace)
    ((Papers.OaiNearInclusionsVon.ReusedTree.leftReg (gen j)⁻¹ : TreeSpace →L[ℂ] TreeSpace)
      (Papers.OaiNearInclusionsVon.ReusedTree.delta (gen j * x))) = _ at h
  rw [Papers.OaiNearInclusionsVon.ReusedTree.leftReg_delta, inv_mul_cancel_left] at h
  exact h

-- @node: circleTreeRep_gen_basis_off_path
/-- For [a circle point z](hyp:z), [a generator index j](hyp:j), and [a free-group
element x](hyp:x), if [the product of the j-th generator with x is not the identity](hyp:h₁)
and [is not the j-th generator](hyp:h₂), then [the circle tree operator at that
generator sends the basis vector at x to the basis vector at their product](goal). -/
lemma circleTreeRep_gen_basis_off_path (z : Circle) (j : ℕ) (x : FreeGrp)
    (h₁ : gen j * x ≠ 1) (h₂ : gen j * x ≠ gen j) :
    (circleTreeRep z (gen j) : TreeSpace →L[ℂ] TreeSpace) (treeBasis x) =
      treeBasis (gen j * x) := by
  rw [circleTreeRep_apply, circleDiagonal_inv_basis, map_smul,
    realTreeRep_gen_basis_off_path j x h₁ h₂, map_smul, circleDiagonal_basis]
  simp only [smul_smul, map_mul, circleCharacter_gen, Circle.coe_mul]
  field_simp
  simp

-- @node: circle_gen_mul_eventually_ne
/-- For [fixed free-group elements x and y](hyp:x,y), [the product of the j-th
generator with x differs from y for all sufficiently large j](goal). -/
lemma circle_gen_mul_eventually_ne (x y : FreeGrp) :
    ∀ᶠ j : ℕ in atTop, gen j * x ≠ y := by
  by_cases h : ∃ k, gen k * x = y
  · obtain ⟨k, hk⟩ := h
    filter_upwards [eventually_gt_atTop k] with j hj
    intro he
    have heq : gen j = gen k := mul_right_cancel (he.trans hk.symm)
    have : j = k := FreeGroup.of_injective heq
    omega
  · exact Eventually.of_forall (fun j hj => h ⟨j, hj⟩)

-- @node: circleTreeRep_gen_basis_limit
/-- For [a circle point z](hyp:z) and [free-group elements x and y](hyp:x,y),
[the matrix coefficient between their basis vectors of the circle tree operator
at the j-th generator converges, as j tends to infinity, to that of the projection
onto the identity basis vector multiplied by the deformation parameter times z](goal). -/
lemma circleTreeRep_gen_basis_limit (z : Circle) (x y : FreeGrp) :
    Tendsto (fun j => inner ℂ (treeBasis x)
      ((circleTreeRep z (gen j) : TreeSpace →L[ℂ] TreeSpace) (treeBasis y)))
      atTop (𝓝 (inner ℂ (treeBasis x)
        ((((tParam : ℂ) * (z : ℂ)) • projE) (treeBasis y)))) := by
  classical
  apply tendsto_const_nhds.congr'
  by_cases hy : y = 1
  · subst y
    filter_upwards [circle_gen_mul_eventually_ne 1 x] with j hj
    have hjx : gen j ≠ x := by simpa using hj
    rw [circleTreeRep_gen_basis_identity, inner_add_right, inner_smul_right, inner_smul_right]
    simp [projE_apply_coordinate, treeBasis,
      lp.inner_single_left, lp.single_apply, Ne.symm hjx]
  · have h₂ (j : ℕ) : gen j * y ≠ gen j := by
      intro h
      apply hy
      exact mul_left_cancel (by simpa using h : gen j * y = gen j * 1)
    filter_upwards [circle_gen_mul_eventually_ne y 1,
      circle_gen_mul_eventually_ne y x] with j h₁ hjx
    rw [circleTreeRep_gen_basis_off_path z j y h₁ (h₂ j)]
    simp [projE_apply_coordinate, treeBasis, lp.inner_single_left,
      lp.single_apply, hy, Ne.symm hjx]

-- @node: circleTreeRep_gen_tendsto_wot
/-- For [a circle point z](hyp:z) and [tree-space vectors ξ and η](hyp:ξ,η),
[the matrix coefficient between ξ and η of the circle tree operator at the j-th
generator converges, as j tends to infinity, to that of the projection onto the
identity basis vector multiplied by the deformation parameter times z](goal). -/
lemma circleTreeRep_gen_tendsto_wot (z : Circle) (ξ η : TreeSpace) :
    Tendsto (fun j => inner ℂ ξ
      ((circleTreeRep z (gen j) : TreeSpace →L[ℂ] TreeSpace) η)) atTop
      (𝓝 (inner ℂ ξ ((((tParam : ℂ) * (z : ℂ)) • projE) η))) := by
  classical
  apply lp_bounded_wot_of_single_tests _ _ 1
    (fun j => Papers.OaiNearInclusionsVon.ReusedTree.unitary_norm_le_one (circleTreeRep z (gen j))) ?_ ξ η
  intro x y v w
  have hs (a : FreeGrp) (c : ℂ) : (lp.single 2 a c : TreeSpace) = c • treeBasis a := by
    simp [treeBasis, ← lp.single_smul]
  simp only [hs, map_smul, inner_smul_left, inner_smul_right]
  exact ((circleTreeRep_gen_basis_limit z x y).const_mul (starRingEnd ℂ v)).const_mul w

end Papers.OaiNearInclusionsVon
