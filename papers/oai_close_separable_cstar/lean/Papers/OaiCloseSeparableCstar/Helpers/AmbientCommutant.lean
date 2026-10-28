module

public import Papers.OaiCloseSeparableCstar.Helpers.LpOperators

/-! # Matrix units and the commutant of the common ambient algebra

Matrix units identify the common first-factor block. Commutation with translations
then imposes the regular commutant condition, independently of the deformation.
-/

public section

namespace Papers.OaiCloseSeparableCstar

/-- [Exchanging the two Hilbert coordinates twice gives the identity operator](goal). -/
-- @node: flipOp_mul_self
lemma flipOp_mul_self : flipOp * flipOp = 1 := by
  ext v x y
  rfl

/-- [Applying the matrix unit from y to x on the first tensor factor sends any
vector to the vector supported only at outer coordinate x, with value equal to
the original vector's value at outer coordinate y](goal). -/
-- @node: flip_matrixUnit_apply
lemma flip_matrixUnit_apply (x y : FG) (v : LSp) :
    ((flipOp * constantDiagOp (matUnit x y) * flipOp : Op LSp) v) = lp.single 2 x (v y) := by
  classical
  ext i j
  change (v y j) • (delta x i) = (lp.single 2 x (v y) : LSp) i j
  by_cases hi : i = x
  · subst i
    simp [delta]
  · simp [delta, lp.single_apply, hi]

/-- If [a bounded operator on the tensor Hilbert space commutes with every matrix
unit acting on the second factor](hyp:hT), then [it is the extension to the first
factor of a bounded operator on the single-factor Hilbert space](goal).

The single-factor operator is obtained by exchanging the factors and compressing
to the identity coordinate. -/
-- @node: matrixUnit_commutant_factorization
lemma matrixUnit_commutant_factorization (T : Op LSp)
    (hT : ∀ x y, constantDiagOp (matUnit x y) * T =
      T * constantDiagOp (matUnit x y)) :
    ∃ Y : Op KSp, T = flipOp * constantDiagOp Y * flipOp := by
  let B := flipOp * T * flipOp
  let Y : Op KSp := (lp.evalCLM ℂ (fun _ : FG => KSp) 2 1).comp
    (B.comp (lp.singleContinuousLinearMap ℂ (fun _ : FG => KSp) 2 1))
  have hB (x y : FG) :
      (flipOp * constantDiagOp (matUnit x y) * flipOp) * B =
        B * (flipOp * constantDiagOp (matUnit x y) * flipOp) := by
    dsimp [B]
    simp only [mul_assoc, ← mul_assoc flipOp flipOp, flipOp_mul_self, one_mul]
    have h := congrArg (fun A : Op LSp => flipOp * A * flipOp) (hT x y)
    simpa only [mul_assoc] using h
  have he : B = constantDiagOp Y := by
    ext v y i
    have h := congrArg (fun A : Op LSp => (A v) 1 i) (hB 1 y)
    change (((flipOp * constantDiagOp (matUnit 1 y) * flipOp : Op LSp) (B v))) 1 i =
      (B (((flipOp * constantDiagOp (matUnit 1 y) * flipOp : Op LSp) v))) 1 i at h
    rw [flip_matrixUnit_apply, flip_matrixUnit_apply, lp.single_apply_self] at h
    exact h
  refine ⟨Y, ?_⟩
  have h := congrArg (fun A : Op LSp => flipOp * A * flipOp) he
  simpa only [B, mul_assoc, ← mul_assoc flipOp flipOp, flipOp_mul_self,
    one_mul, mul_one] using h

/-- [Applying the first-factor extension of a bounded operator to a vector with
value w only at outer coordinate x gives, at coordinate i, the vector w multiplied
by the i-th coefficient of the operator applied to the basis vector at x](goal). -/
-- @node: firstFactor_single_apply
lemma firstFactor_single_apply (Y : Op KSp) (x : FG) (w : KSp) (i : FG) :
    ((flipOp * constantDiagOp Y * flipOp : Op LSp) (lp.single 2 x w)) i =
      (Y (delta x)) i • w := by
  classical
  have hc (j : FG) : (flipOp (lp.single 2 x w)) j = w j • delta x := by
    ext k
    change (lp.single 2 x w : LSp) k j = w j • delta x k
    by_cases hk : k = x
    · subst k
      simp [delta]
    · simp [delta, lp.single_apply, hk]
  ext j
  change (Y ((flipOp (lp.single 2 x w)) j)) i = _
  rw [hc, map_smul]
  change w j * Y (delta x) i = Y (delta x) i * w j
  exact mul_comm _ _

/-- [The constant diagonal action of one bounded operator on the second tensor
factor commutes with the extension of any bounded operator to the first
factor](goal). -/
-- @node: firstFactor_commutes_constant
lemma firstFactor_commutes_constant (Y Z : Op KSp) :
    constantDiagOp Z * (flipOp * constantDiagOp Y * flipOp) =
      (flipOp * constantDiagOp Y * flipOp) * constantDiagOp Z := by
  apply lp.ext_continuousLinearMap (by norm_num)
  intro x
  ext w i j
  have hc : constantDiagOp (I := FG) Z (lp.single 2 x w) = lp.single 2 x (Z w) := by
    ext k
    by_cases hk : k = x
    · subst k; simp [constantDiagOp, diagOp]
    · simp [constantDiagOp, diagOp, lp.single_apply, hk]
  change (Z (((flipOp * constantDiagOp Y * flipOp : Op LSp) (lp.single 2 x w)) i)) j =
    (((flipOp * constantDiagOp Y * flipOp : Op LSp)
      (constantDiagOp Z (lp.single 2 x w))) i) j
  rw [hc, firstFactor_single_apply, firstFactor_single_apply, map_smul]

/-- [Conjugating translation of the outer group coordinate by the factor exchange
gives the constant diagonal action of the same left regular translation on every
fiber](goal). -/
-- @node: flip_shiftOp_flip
lemma flip_shiftOp_flip (g : FG) :
    flipOp * (shiftOp g : Op LSp) * flipOp = constantDiagOp (leftReg g : Op KSp) := by
  ext v x y
  rfl

/-- [The first-factor extension of a bounded operator commutes with outer
translation by a group element if and only if the original operator commutes
with left regular translation by that element](goal). -/
-- @node: firstFactor_commutes_shift_iff
lemma firstFactor_commutes_shift_iff (Y : Op KSp) (g : FG) :
    (shiftOp g : Op LSp) * (flipOp * constantDiagOp Y * flipOp) =
      (flipOp * constantDiagOp Y * flipOp) * shiftOp g ↔
    (leftReg g : Op KSp) * Y = Y * (leftReg g : Op KSp) := by
  have he : (shiftOp g : Op LSp) =
      flipOp * constantDiagOp (leftReg g : Op KSp) * flipOp := by
    rw [← flip_shiftOp_flip]
    simp only [mul_assoc, ← mul_assoc flipOp flipOp, flipOp_mul_self, one_mul, mul_one]
  rw [he]
  constructor
  · intro h
    have h := congrArg (fun A : Op LSp => flipOp * A * flipOp) h
    simp only [mul_assoc, ← mul_assoc flipOp flipOp, flipOp_mul_self,
      one_mul, mul_one] at h
    ext w i
    exact congrArg (fun A : Op LSp => (A (lp.single 2 (1 : FG) w)) 1 i) h
  · intro h
    have hc : constantDiagOp (I := FG) (leftReg g : Op KSp) * constantDiagOp Y =
        constantDiagOp Y * constantDiagOp (leftReg g : Op KSp) := by
      ext v i j
      exact congrArg (fun A : Op KSp => A (v i) j) h
    simpa only [mul_assoc, ← mul_assoc flipOp flipOp, flipOp_mul_self,
      one_mul] using congrArg (fun A : Op LSp => flipOp * A * flipOp) hc

/-- [The adjoint of the constant diagonal extension of a bounded operator is the
constant diagonal extension of its adjoint](goal). -/
-- @node: constantDiagOp_star
lemma constantDiagOp_star (Y : Op KSp) :
    star (constantDiagOp (I := FG) Y) = constantDiagOp (star Y) := by
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext i
  exact diagonal_star_apply _ (fun _ => Y) (fun _ _ => rfl) v i

/-- [The adjoint of translation of the outer group coordinate by an element is
translation by its inverse](goal). -/
-- @node: shiftOp_star
lemma shiftOp_star (g : FG) : star (shiftOp g : Op LSp) = shiftOp g⁻¹ := by
  have hu : (shiftOp g : Op LSp) ∈ unitary (Op LSp) := reindexOp_mem_unitary _
  have hi : (shiftOp g : Op LSp) * shiftOp g⁻¹ = 1 := by
    apply ContinuousLinearMap.ext
    intro v
    apply lp.ext
    funext x
    change v ((g⁻¹)⁻¹ * (g⁻¹ * x)) = v x
    simp
  calc
    star (shiftOp g : Op LSp) = star (shiftOp g : Op LSp) *
        ((shiftOp g : Op LSp) * shiftOp g⁻¹) := by rw [hi, mul_one]
    _ = shiftOp g⁻¹ := by rw [← mul_assoc, Unitary.star_mul_self_of_mem hu, one_mul]

/-- [The operators commuting with the ambient algebra are exactly the first-factor
extensions of bounded operators that commute with every left regular
translation](goal). -/
-- @node: Dalg_commutant_eq
lemma Dalg_commutant_eq (π : FG →* unitary (Op KSp)) :
    commutant (Dalg π) =
      {T | ∃ Y ∈ commutant (Set.range (fun g => (leftReg g : Op KSp))),
        T = flipOp * constantDiagOp Y * flipOp} := by
  let s : Set (Op LSp) :=
    Set.range (fun g : FG => (shiftOp g : Op LSp)) ∪
      Set.range (fun g => (constantDiagOp (piZero g : Op KSp) : Op LSp)) ∪
      Set.range (fun g => (constantDiagOp (π g : Op KSp) : Op LSp)) ∪
      Set.range (fun xy : FG × FG =>
        (constantDiagOp (matUnit xy.1 xy.2) : Op LSp))
  have hgen {a : Op LSp} (ha : a ∈ s) : a ∈ Dalg π :=
    StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ s ha)
  ext T
  constructor
  · intro hT
    obtain ⟨Y, hY⟩ := matrixUnit_commutant_factorization T (fun x y =>
      hT _ (hgen (Or.inr ⟨(x, y), rfl⟩)))
    refine ⟨Y, ?_, hY⟩
    rintro _ ⟨g, rfl⟩
    apply (firstFactor_commutes_shift_iff Y g).mp
    rw [← hY]
    exact hT _ (hgen (Or.inl (Or.inl (Or.inl ⟨g, rfl⟩))))
  · rintro ⟨Y, hY, rfl⟩
    let A := flipOp * constantDiagOp Y * flipOp
    have hs : A ∈ StarSubalgebra.centralizer ℂ s := by
      rw [StarSubalgebra.mem_centralizer_iff]
      intro a ha
      rcases ha with ((⟨g, rfl⟩ | ⟨g, rfl⟩) | ⟨g, rfl⟩) | ⟨⟨x, y⟩, rfl⟩
      · constructor
        · exact (firstFactor_commutes_shift_iff Y g).mpr (hY _ ⟨g, rfl⟩)
        · rw [shiftOp_star]
          exact (firstFactor_commutes_shift_iff Y g⁻¹).mpr (hY _ ⟨g⁻¹, rfl⟩)
      all_goals
        exact ⟨firstFactor_commutes_constant _ _, by
          rw [constantDiagOp_star]
          exact firstFactor_commutes_constant _ _⟩
    intro a ha
    have hd := StarSubalgebra.topologicalClosure_adjoin_le_centralizer_centralizer ℂ s ha
    exact (((StarSubalgebra.mem_centralizer_iff ℂ).mp hd) A hs).1.symm

end Papers.OaiCloseSeparableCstar
