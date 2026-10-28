module

public import Papers.OaiCloseSeparableCstar.Basic

/-! # Lemma 6: Fell absorption on ℓ²(G;J) -/

public section

namespace Papers.OaiCloseSeparableCstar

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

-- @node: leftReg_delta
/-- For [group elements g and x](hyp:g,x), [left translation by g sends the basis
vector at x to the basis vector at g times x](goal). -/
@[simp] lemma leftReg_delta (g x : FG) :
    (leftReg g : Op KSp) (delta x) = delta (g * x) := by
  classical
  ext y
  change (delta x) (g⁻¹ * y) = (delta (g * x)) y
  simp only [delta, lp.single_apply, Pi.single_apply]
  simp only [inv_mul_eq_iff_eq_mul]

-- @node: rightReg_delta
/-- For [group elements g and x](hyp:g,x), [right translation by g sends the basis
vector at x to the basis vector at x times the inverse of g](goal). -/
@[simp] lemma rightReg_delta (g x : FG) :
    (rightReg g : Op KSp) (delta x) = delta (x * g⁻¹) := by
  classical
  ext y
  change (delta x) (y * g) = (delta (x * g⁻¹)) y
  simp only [delta, lp.single_apply, Pi.single_apply]
  simp only [eq_mul_inv_iff_mul_eq]

-- @node: matUnit_delta
/-- For [group elements x, y, and z](hyp:x,y,z), [the matrix unit with row x and
column y sends the basis vector at z to the basis vector at x when z equals y,
and to zero otherwise](goal). -/
@[simp] lemma matUnit_delta (x y z : FG) :
    matUnit x y (delta z) = if z = y then delta x else 0 := by
  classical
  by_cases h : z = y
  · subst z
    change (delta y) y • delta x = _
    simp [delta]
  · have hz : (delta z) y = 0 := by simp [delta, lp.single_apply, Ne.symm h]
    change (delta z) y • delta x = _
    simp [hz, h]

-- @node: lem:absorption
/-- For [a unitary representation σ of the free group](hyp:σ) on [a nonzero
Hilbert space](hyp:hσ), [the operator applying σ at each group coordinate is
unitary, and its conjugation of every left shift equals that shift followed by
the constant diagonal action of σ at the shifting group element](goal). -/
lemma absorption (σ : FG →* unitary (Op J)) (hσ : AbsorptionRepresentation J) :
    absorptionOp σ ∈ unitary (Op (lp (fun _ : FG => J) 2)) ∧
      ∀ g : FG, absorptionOp σ * shiftOp g * star (absorptionOp σ) =
        shiftOp g * diagUnitaryOp (fun _ : FG => σ g) := by
  refine ⟨diagUnitaryOp_mem_unitary _, ?_⟩
  intro g
  ext v x
  change (σ x : Op J) ((star (diagUnitaryOp (fun x => σ x)) v) (g⁻¹ * x)) =
    (σ g : Op J) (v (g⁻¹ * x))
  rw [diagUnitaryOp_star_apply]
  have hx : σ x = σ g * σ (g⁻¹ * x) := by
    rw [← map_mul]
    simp
  rw [hx]
  change (((σ g : Op J) * (σ (g⁻¹ * x) : Op J)) *
    star (σ (g⁻¹ * x) : Op J)) (v (g⁻¹ * x)) = _
  rw [mul_assoc, Unitary.mul_star_self_of_mem (σ (g⁻¹ * x)).property, mul_one]

end Papers.OaiCloseSeparableCstar
