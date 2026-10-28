module

public import Papers.OaiNearInclusionsVon.Helpers.CircleConstruction
public import Papers.OaiNearInclusionsVon.ReusedTree.Helpers.TreePathOperators

/-! Finite path matrices and the Laurent expansion of the circle twist. -/

@[expose] public section

namespace Papers.OaiNearInclusionsVon

open scoped BigOperators

local notation "Op" => TreeSpace →L[ℂ] TreeSpace

-- @node: circle_delta_eq
/-- [The point mass at any group element equals the corresponding tree basis vector](goal). -/
lemma circle_delta_eq (x : FreeGrp) :
    Papers.OaiNearInclusionsVon.ReusedTree.delta x = treeBasis x := rfl

-- @node: circle_matUnit_basis
/-- [A matrix unit sends the basis vector at its column index to the basis vector at its
row index, and sends every other basis vector to zero](goal). -/
lemma circle_matUnit_basis (x y a : FreeGrp) :
    Papers.OaiNearInclusionsVon.ReusedTree.matUnit x y (treeBasis a) =
      if a = y then treeBasis x else 0 := by
  simpa only [circle_delta_eq] using
    Papers.OaiNearInclusionsVon.ReusedTree.matUnit_delta x y a

-- @node: circle_leftReg_basis
/-- [Left translation by a group element sends the basis vector at any vertex to the
basis vector at the left-translated vertex](goal). -/
lemma circle_leftReg_basis (g x : FreeGrp) :
    (Papers.OaiNearInclusionsVon.ReusedTree.leftReg g : Op) (treeBasis x) =
      treeBasis (g * x) := by
  simpa only [circle_delta_eq] using Papers.OaiNearInclusionsVon.ReusedTree.leftReg_delta g x

-- @node: circleExponent
/-- For [a free-group element](hyp:g), its [circle exponent](goal) is the signed total
number of generator occurrences, counting a generator as one and its inverse as minus one. -/
noncomputable def circleExponent (g : FreeGrp) : ℤ :=
  Multiplicative.toAdd (FreeGroup.lift (fun _ : ℕ => Multiplicative.ofAdd (1 : ℤ)) g)

-- @node: circleExponent_mul
/-- [The circle exponent of a product is the sum of the circle exponents of its factors](goal). -/
lemma circleExponent_mul (g h : FreeGrp) :
    circleExponent (g * h) = circleExponent g + circleExponent h := by
  exact congrArg Multiplicative.toAdd (map_mul
    (FreeGroup.lift (fun _ : ℕ => Multiplicative.ofAdd (1 : ℤ))) g h)

-- @node: circleCharacter_eq_zpow
/-- [The circle character of a group element is the circle parameter raised to that
element's integer circle exponent](goal). -/
lemma circleCharacter_eq_zpow (z : Circle) (g : FreeGrp) :
    circleCharacter z g = z ^ circleExponent g := by
  induction g using FreeGroup.induction_on with
  | C1 => simp [circleCharacter, circleExponent]
  | of j => simp [circleCharacter, circleExponent]
  | inv_of j ih =>
    simpa [circleExponent, map_inv] using congrArg Inv.inv ih
  | mul g h hg hh =>
    rw [map_mul, hg, hh, circleExponent_mul, zpow_add]

-- @node: circleDiagonal_conjugate_leftReg
/-- [Conjugating left translation by the circle diagonal unitary multiplies that
translation by the reciprocal of its circle character](goal). -/
lemma circleDiagonal_conjugate_leftReg (z : Circle) (g : FreeGrp) :
    (circleDiagonal z : Op) *
      (Papers.OaiNearInclusionsVon.ReusedTree.leftReg g : Op) * star (circleDiagonal z : Op) =
      (((circleCharacter z g : Circle) : ℂ)⁻¹) •
        (Papers.OaiNearInclusionsVon.ReusedTree.leftReg g : Op) := by
  apply Papers.OaiNearInclusionsVon.ReusedTree.treeOp_ext_delta
  intro x
  simp only [circle_delta_eq]
  change (circleDiagonal z : Op)
    ((Papers.OaiNearInclusionsVon.ReusedTree.leftReg g : Op)
      (star (circleDiagonal z : Op) (treeBasis x))) = _
  rw [circleDiagonal_inv_basis, map_smul,
    circle_leftReg_basis, map_smul, circleDiagonal_basis]
  simp only [map_mul, Circle.coe_mul, mul_inv_rev, _root_.smul_apply,
    circle_leftReg_basis, smul_smul]
  congr 1
  field_simp

-- @node: circleDiagonal_conjugate_matUnit
/-- [Conjugating a matrix unit by the circle diagonal unitary multiplies it by the
circle parameter raised to the column exponent minus the row exponent](goal). -/
lemma circleDiagonal_conjugate_matUnit (z : Circle) (x y : FreeGrp) :
    (circleDiagonal z : Op) * Papers.OaiNearInclusionsVon.ReusedTree.matUnit x y *
      star (circleDiagonal z : Op) =
      ((z : ℂ) ^ (circleExponent y - circleExponent x)) •
        Papers.OaiNearInclusionsVon.ReusedTree.matUnit x y := by
  apply Papers.OaiNearInclusionsVon.ReusedTree.treeOp_ext_delta
  intro a
  simp only [circle_delta_eq]
  change (circleDiagonal z : Op)
    (Papers.OaiNearInclusionsVon.ReusedTree.matUnit x y
      (star (circleDiagonal z : Op) (treeBasis a))) = _
  rw [circleDiagonal_inv_basis, map_smul,
    circle_matUnit_basis]
  by_cases ha : a = y
  · subst a
    simp only [map_smul, _root_.smul_apply, circle_matUnit_basis,
      circleCharacter_eq_zpow, Circle.coe_zpow]
    rw [zpow_sub₀ (Circle.coe_ne_zero _)]
    simp [div_eq_mul_inv, circleDiagonal_basis,
      circleCharacter_eq_zpow, smul_smul]
  · simp [ha, circle_matUnit_basis]

-- @node: circlePathRemainder
/-- For [a free-group element](hyp:g), the [path remainder](goal) is its tree
perturbation operator at deformation parameter one half minus the identity operator. -/
noncomputable def circlePathRemainder (g : FreeGrp) : Op :=
  Papers.OaiNearInclusionsVon.ReusedTree.treePerturbation tParam circle_deformation_range g - 1

-- @node: circlePathEntry
/-- For [a free-group element](hyp:g), [a row vertex](hyp:x), and [a column vertex](hyp:y),
the [path entry](goal) is the coordinate at the row vertex of the path remainder
applied to the column basis vector. -/
noncomputable def circlePathEntry (g x y : FreeGrp) : ℂ :=
  circlePathRemainder g (treeBasis y) x

-- @node: circlePathEntry_off_path
/-- If [the row vertex lies outside the path from the identity to the group element](hyp:hx),
then [the corresponding path entry is zero for every column vertex](goal). -/
lemma circlePathEntry_off_path (g x y : FreeGrp)
    (hx : x ∉ Papers.OaiNearInclusionsVon.ReusedTree.treePathVertices g) :
    circlePathEntry g x y = 0 := by
  have h := congrArg (fun A : Op => A (treeBasis y) x)
    (Papers.OaiNearInclusionsVon.ReusedTree.treePathProjection_mul_treePerturbation_sub_one
      tParam circle_deformation_range g)
  change Papers.OaiNearInclusionsVon.ReusedTree.treePathProjection g
    (circlePathRemainder g (treeBasis y)) x = circlePathEntry g x y at h
  rw [Papers.OaiNearInclusionsVon.ReusedTree.treePathProjection,
    Papers.OaiNearInclusionsVon.ReusedTree.treeCoordinateProjection_apply] at h
  simp only [Set.mem_ofPred_eq] at h
  rw [if_neg (fun hp => hx
    ((Papers.OaiNearInclusionsVon.ReusedTree.mem_treePathVertices g x).mpr hp))] at h
  exact h.symm

-- @node: circlePathRemainder_matrix
/-- [The path remainder equals the finite sum of its matrix entries times the
corresponding matrix units, with both indices on the path from the identity to the
group element](goal). -/
lemma circlePathRemainder_matrix (g : FreeGrp) :
    circlePathRemainder g =
      ∑ x ∈ Papers.OaiNearInclusionsVon.ReusedTree.treePathVertices g,
        ∑ y ∈ Papers.OaiNearInclusionsVon.ReusedTree.treePathVertices g,
          circlePathEntry g x y • Papers.OaiNearInclusionsVon.ReusedTree.matUnit x y := by
  classical
  apply Papers.OaiNearInclusionsVon.ReusedTree.treeOp_ext_delta
  intro a
  simp only [circle_delta_eq]
  by_cases ha : a ∈ Papers.OaiNearInclusionsVon.ReusedTree.treePathVertices g
  · have hs (x : FreeGrp) :
        (∑ y ∈ Papers.OaiNearInclusionsVon.ReusedTree.treePathVertices g,
          circlePathEntry g x y • Papers.OaiNearInclusionsVon.ReusedTree.matUnit x y) (treeBasis a) =
          circlePathEntry g x a • treeBasis x := by
      simp only [_root_.sum_apply, _root_.smul_apply,
        circle_matUnit_basis, smul_ite, smul_zero]
      simp [ha]
    simp only [_root_.sum_apply, hs]
    ext b
    simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
      treeBasis, lp.single_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    by_cases hb : b ∈ Papers.OaiNearInclusionsVon.ReusedTree.treePathVertices g
    · simp [hb, circlePathEntry, treeBasis]
    · simpa [hb, circlePathEntry, treeBasis] using circlePathEntry_off_path g b a hb
  · have hp : ¬ a.toWord.IsPrefix g.toWord :=
      fun h => ha ((Papers.OaiNearInclusionsVon.ReusedTree.mem_treePathVertices g a).mpr h)
    have hz : circlePathRemainder g (treeBasis a) = 0 := by
      have h := Papers.OaiNearInclusionsVon.ReusedTree.treePerturbation_delta_of_not_prefix
        tParam circle_deformation_range g a hp
      simp only [circle_delta_eq] at h
      simpa [circlePathRemainder] using sub_eq_zero.mpr h
    rw [hz]
    simp only [_root_.sum_apply, _root_.smul_apply,
      circle_matUnit_basis, smul_ite, smul_zero]
    simp [ha]

-- @node: circleTreeRep_eq_perturbation
/-- [The circle tree representation equals the tree perturbation conjugated by the
circle diagonal unitary, followed by left translation by the group element](goal). -/
lemma circleTreeRep_eq_perturbation (z : Circle) (g : FreeGrp) :
    (circleTreeRep z g : Op) =
      ((circleDiagonal z : Op) *
        Papers.OaiNearInclusionsVon.ReusedTree.treePerturbation tParam circle_deformation_range g *
        star (circleDiagonal z : Op)) *
          (Papers.OaiNearInclusionsVon.ReusedTree.leftReg g : Op) := by
  have hr :
      (Papers.OaiNearInclusionsVon.ReusedTree.treeUnitaryRep tParam circle_deformation_range g : Op) =
        Papers.OaiNearInclusionsVon.ReusedTree.treePerturbation tParam circle_deformation_range g *
          (Papers.OaiNearInclusionsVon.ReusedTree.leftReg g : Op) := by
    apply Papers.OaiNearInclusionsVon.ReusedTree.treeOp_ext_delta
    intro x
    simp only [circle_delta_eq]
    change _ = (Papers.OaiNearInclusionsVon.ReusedTree.treeUnitaryRep
      tParam circle_deformation_range g : Op)
        ((Papers.OaiNearInclusionsVon.ReusedTree.leftReg g⁻¹ : Op)
          ((Papers.OaiNearInclusionsVon.ReusedTree.leftReg g : Op) (treeBasis x)))
    rw [circle_leftReg_basis, circle_leftReg_basis, inv_mul_cancel_left]
  change ((circleCharacter z g : Circle) : ℂ) •
    ((circleDiagonal z : Op) *
      (Papers.OaiNearInclusionsVon.ReusedTree.treeUnitaryRep tParam circle_deformation_range g : Op) *
      star (circleDiagonal z : Op)) = _
  rw [hr]
  have hd := Unitary.coe_star_mul_self (circleDiagonal z)
  have hprod (T L : Op) :
      (circleDiagonal z : Op) * (T * L) * star (circleDiagonal z : Op) =
        ((circleDiagonal z : Op) * T * star (circleDiagonal z : Op)) *
          ((circleDiagonal z : Op) * L * star (circleDiagonal z : Op)) := by
    simp only [mul_assoc]
    rw [← mul_assoc (star (circleDiagonal z : Op)), hd, one_mul]
  rw [hprod, circleDiagonal_conjugate_leftReg, mul_smul_comm, smul_smul,
    mul_inv_cancel₀ (Circle.coe_ne_zero _), one_smul]

-- @node: circleTreeRep_finite_matrix
/-- [The circle tree representation equals the identity plus a finite path matrix,
followed by left translation; each matrix entry is the path remainder entry times
the circle parameter raised to the column exponent minus the row exponent](goal). -/
lemma circleTreeRep_finite_matrix (z : Circle) (g : FreeGrp) :
    (circleTreeRep z g : Op) =
      (1 + ∑ x ∈ Papers.OaiNearInclusionsVon.ReusedTree.treePathVertices g,
        ∑ y ∈ Papers.OaiNearInclusionsVon.ReusedTree.treePathVertices g,
          ((z : ℂ) ^ (circleExponent y - circleExponent x)) •
            (circlePathEntry g x y • Papers.OaiNearInclusionsVon.ReusedTree.matUnit x y)) *
              (Papers.OaiNearInclusionsVon.ReusedTree.leftReg g : Op) := by
  rw [circleTreeRep_eq_perturbation]
  congr 1
  have ht : Papers.OaiNearInclusionsVon.ReusedTree.treePerturbation
      tParam circle_deformation_range g = 1 + circlePathRemainder g := by
    simp [circlePathRemainder]
  rw [ht, circlePathRemainder_matrix]
  simp only [mul_add, add_mul, mul_one,
    Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
  rw [show (circleDiagonal z : Op) * star (circleDiagonal z : Op) = 1 from
    Unitary.coe_mul_star_self (circleDiagonal z)]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [circleDiagonal_conjugate_matUnit, smul_comm]

/-- For [an integer Laurent index](hyp:k) and [a free-group element](hyp:g), the
[Laurent core coefficient](goal) is the identity at index zero and zero otherwise,
plus the sum of path entries times matrix units whose column exponent minus row
exponent equals the index. -/
-- @node: circleLaurentCore
noncomputable def circleLaurentCore (k : ℤ) (g : FreeGrp) : Op := by
  classical
  exact (if k = 0 then 1 else 0) +
    ∑ x ∈ Papers.OaiNearInclusionsVon.ReusedTree.treePathVertices g,
      ∑ y ∈ Papers.OaiNearInclusionsVon.ReusedTree.treePathVertices g,
        if k = circleExponent y - circleExponent x then
          circlePathEntry g x y • Papers.OaiNearInclusionsVon.ReusedTree.matUnit x y else 0

-- @node: circleLaurentCoefficients
/-- The [Laurent coefficient family](goal) assigns to each integer index and group
element the corresponding Laurent core coefficient followed by left translation
by that group element. -/
noncomputable def circleLaurentCoefficients : LaurentData := fun k g =>
  circleLaurentCore k g * (Papers.OaiNearInclusionsVon.ReusedTree.leftReg g : Op)

-- @node: circleLaurentCore_hasSum
/-- [The Laurent series of core coefficients at a circle parameter sums to the
identity plus the finite path matrix whose entries are weighted by that parameter
raised to the column exponent minus the row exponent](goal). -/
lemma circleLaurentCore_hasSum (z : Circle) (g : FreeGrp) :
    HasSum (fun k : ℤ => ((z : ℂ) ^ k) • circleLaurentCore k g)
      (1 + ∑ x ∈ Papers.OaiNearInclusionsVon.ReusedTree.treePathVertices g,
        ∑ y ∈ Papers.OaiNearInclusionsVon.ReusedTree.treePathVertices g,
          ((z : ℂ) ^ (circleExponent y - circleExponent x)) •
            (circlePathEntry g x y • Papers.OaiNearInclusionsVon.ReusedTree.matUnit x y)) := by
  classical
  have hs (n : ℤ) (E : Op) :
      HasSum (fun k : ℤ => ((z : ℂ) ^ k) • (if k = n then E else 0))
        (((z : ℂ) ^ n) • E) := by
    convert hasSum_ite_eq n (((z : ℂ) ^ n) • E) using 1
    funext k
    by_cases hk : k = n <;> simp [hk]
  have hzero : HasSum (fun k : ℤ => ((z : ℂ) ^ k) • (if k = 0 then (1 : Op) else 0)) 1 := by
    simpa using hs 0 1
  convert hzero.add (hasSum_sum (s := Papers.OaiNearInclusionsVon.ReusedTree.treePathVertices g)
    (fun x hx => hasSum_sum (s := Papers.OaiNearInclusionsVon.ReusedTree.treePathVertices g)
      (fun y hy => hs (circleExponent y - circleExponent x)
        (circlePathEntry g x y • Papers.OaiNearInclusionsVon.ReusedTree.matUnit x y)))) using 1
  funext k
  simp [circleLaurentCore, smul_add, Finset.smul_sum]

-- @node: circleLaurentCoefficients_hasSum
/-- [The Laurent series formed from the circle Laurent coefficients converges to
the circle tree representation at every circle parameter and group element](goal). -/
lemma circleLaurentCoefficients_hasSum (z : Circle) (g : FreeGrp) :
    HasSum (fun k : ℤ => ((z : ℂ) ^ k) • circleLaurentCoefficients k g)
      (circleTreeRep z g : Op) := by
  rw [circleTreeRep_finite_matrix]
  simpa only [circleLaurentCoefficients, smul_mul_assoc] using
    (circleLaurentCore_hasSum z g).mul_right
      (Papers.OaiNearInclusionsVon.ReusedTree.leftReg g : Op)

/-- [For each group element, there is a finite set of integer indices outside
which all its circle Laurent coefficients vanish](goal). -/
-- @node: circleLaurentCoefficients_finite_support
lemma circleLaurentCoefficients_finite_support (g : FreeGrp) :
    ∃ s : Finset ℤ, ∀ k ∉ s, circleLaurentCoefficients k g = 0 := by
  classical
  let p := Papers.OaiNearInclusionsVon.ReusedTree.treePathVertices g
  refine ⟨insert 0 ((p ×ˢ p).image
    (fun xy => circleExponent xy.2 - circleExponent xy.1)), ?_⟩
  intro k hk
  have hk0 : k ≠ 0 := fun h => hk (by simp [h])
  have hdiff (x : FreeGrp) (hx : x ∈ p) (y : FreeGrp) (hy : y ∈ p) :
      k ≠ circleExponent y - circleExponent x := by
    intro h
    apply hk
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, h.symm⟩
  have hz : circleLaurentCore k g = 0 := by
    rw [circleLaurentCore, if_neg hk0, zero_add]
    apply Finset.sum_eq_zero
    intro x hx
    apply Finset.sum_eq_zero
    intro y hy
    exact if_neg (hdiff x hx y hy)
  simp [circleLaurentCoefficients, hz]

end Papers.OaiNearInclusionsVon
