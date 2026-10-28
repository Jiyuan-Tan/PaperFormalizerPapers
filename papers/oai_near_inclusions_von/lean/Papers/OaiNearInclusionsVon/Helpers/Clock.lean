module

public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.Topology.Separation.Lemmas
public import Toolkit.Foundations.Analysis.Normed.CStarNormBounds
public import Toolkit.Foundations.Analysis.Normed.FiniteDimensionalOperators
public import Toolkit.Foundations.Analysis.SpecialFunctions.ComplexExpLevelSet

/-! The clock–shift sequence and its obstruction to commuting approximation. -/

@[expose] public section

set_option linter.style.longLine false

namespace Papers.OaiNearInclusionsVon


open Filter
open scoped Topology Matrix.Norms.Operator

-- @env: S4
variable (n : ℕ)

-- @node: ass:clock-index
/-- For [a natural number n](hyp:n), [the admissible-dimension condition](goal) means that n is at least three. -/
noncomputable def ClockIndex (n : ℕ) : Prop := 3 ≤ n

/-- [Admissible clock dimensions](goal) are natural numbers that are at least three. -/
abbrev ClockNat := {n : ℕ // ClockIndex n}
/-- For [an admissible dimension n](hyp:n), [the clock space](goal) is complex Euclidean space of dimension n. -/
noncomputable abbrev ClockSpace (n : ClockNat) := EuclideanSpace ℂ (Fin n.val)
/-- In [admissible dimension n](hyp:n), for [a coordinate j](hyp:j),
[the standard basis vector at j](goal) has entry one at j and zero at every other coordinate. -/
noncomputable def clockBasis (n : ClockNat) (j : Fin n.val) : ClockSpace n :=
  EuclideanSpace.single j 1 -- @realizes e_j(standard basis of complex n-space)

/-- For [an admissible dimension n](hyp:n), [the clock phase](goal) is the complex exponential of 2πi divided by n. -/
noncomputable def omegaN (n : ClockNat) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (n.val : ℂ)) -- @realizes \omega_n(exp of two pi i over n)

-- @node: def:clock-pair
/-- For [an admissible dimension n](hyp:n), [the clock operator](goal) multiplies coordinate j
by the j-th power of the clock phase. -/
noncomputable def clockU (n : ClockNat) : ClockSpace n →L[ℂ] ClockSpace n :=
  (EuclideanSpace.equiv (Fin n.val) ℂ).symm.toContinuousLinearMap ∘L
    (ContinuousLinearMap.pi (fun j : Fin n =>
      (omegaN n ^ j.val) • ContinuousLinearMap.proj j)) ∘L
    (EuclideanSpace.equiv (Fin n.val) ℂ).toContinuousLinearMap -- @realizes U_n(clock diagonal operator)
/-- For [an admissible dimension n](hyp:n), [the cyclic forward shift](goal) moves each coordinate
one position forward, sending the last coordinate to the first. -/
noncomputable def shiftV (n : ClockNat) : ClockSpace n →L[ℂ] ClockSpace n :=
  (EuclideanSpace.equiv (Fin n.val) ℂ).symm.toContinuousLinearMap ∘L
    (ContinuousLinearMap.pi (fun j : Fin n =>
      ContinuousLinearMap.proj ((finRotate n.val).symm j))) ∘L
    (EuclideanSpace.equiv (Fin n.val) ℂ).toContinuousLinearMap -- @realizes V_n(cyclic forward shift)
/-- For [an admissible dimension n](hyp:n), [the clock–shift commutator norm](goal) is the operator
norm of the product of the clock and shift minus their product in the reverse order. -/
noncomputable def nuN (n : ClockNat) : ℝ :=
  ‖clockU n * shiftV n - shiftV n * clockU n‖ -- @realizes \nu_n(commutator norm)

-- @node: omegaN_norm
/-- For [an admissible dimension n](hyp:n), [the clock phase has absolute value one](goal). -/
lemma omegaN_norm (n : ClockNat) : ‖omegaN n‖ = 1 := by
  simp [omegaN, Complex.norm_exp, Complex.div_re, Complex.mul_re, Complex.mul_im]

-- @node: clockU_apply
/-- In [admissible dimension n](hyp:n), for [a vector x](hyp:x) and [a coordinate j](hyp:j),
[the j-th coordinate of the clock applied to x is the j-th power of the clock phase times the j-th coordinate of x](goal). -/
lemma clockU_apply (n : ClockNat) (x : ClockSpace n) (j : Fin n.val) :
    clockU n x j = omegaN n ^ j.val * x j := by
  rfl

-- @node: shiftV_apply
/-- In [admissible dimension n](hyp:n), for [a vector x](hyp:x) and [a coordinate j](hyp:j),
[the j-th coordinate of the shifted vector is the coordinate of x immediately preceding j, with cyclic wraparound](goal). -/
lemma shiftV_apply (n : ClockNat) (x : ClockSpace n) (j : Fin n.val) :
    shiftV n x j = x ((finRotate n.val).symm j) := by
  rfl

-- @node: clockU_mem_unitary
/-- For [an admissible dimension n](hyp:n), [the clock operator is unitary](goal). -/
lemma clockU_mem_unitary (n : ClockNat) :
    clockU n ∈ unitary (ClockSpace n →L[ℂ] ClockSpace n) := by
  apply Toolkit.Foundations.Analysis.Normed.mem_unitary_of_forall_norm_apply_eq
  intro x
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp only [clockU_apply, norm_mul, norm_pow, omegaN_norm, one_pow, one_mul]

-- @node: shiftV_mem_unitary
/-- For [an admissible dimension n](hyp:n), [the cyclic shift is unitary](goal). -/
lemma shiftV_mem_unitary (n : ClockNat) :
    shiftV n ∈ unitary (ClockSpace n →L[ℂ] ClockSpace n) := by
  apply Toolkit.Foundations.Analysis.Normed.mem_unitary_of_forall_norm_apply_eq
  intro x
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp only [shiftV_apply]
  exact congrArg Real.sqrt ((finRotate n.val).symm.sum_comp (fun j => ‖x j‖ ^ 2))

-- @node: omegaN_pow_dimension
/-- For [an admissible dimension n](hyp:n), [the n-th power of the clock phase is one](goal). -/
lemma omegaN_pow_dimension (n : ClockNat) : omegaN n ^ n.val = 1 := by
  have hn : (n.val : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := n.property; unfold ClockIndex at this; omega)
  rw [omegaN, ← Complex.exp_nat_mul, mul_div_cancel₀ _ hn, Complex.exp_two_pi_mul_I]

-- @node: omegaN_pow_rotate
/-- For [an admissible dimension n](hyp:n) and [a coordinate j](hyp:j),
[the clock phase raised to the cyclic successor of j equals the clock phase times its j-th power](goal). -/
lemma omegaN_pow_rotate (n : ClockNat) (j : Fin n.val) :
    omegaN n ^ (finRotate n.val j).val = omegaN n * omegaN n ^ j.val := by
  let : NeZero n.val := ⟨by have := n.property; unfold ClockIndex at this; omega⟩
  have hn : 1 < n.val := by have := n.property; unfold ClockIndex at this; omega
  rw [finRotate_apply]
  change omegaN n ^ ((j.val + (1 % n.val)) % n.val) = _
  rw [Nat.mod_eq_of_lt hn, ← pow_eq_pow_mod _ (omegaN_pow_dimension n), pow_succ, mul_comm]

-- @node: clock_shift_relation
/-- For [an admissible dimension n](hyp:n), [the product of the clock and shift equals the clock
phase times their product in the reverse order](goal). -/
lemma clock_shift_relation (n : ClockNat) :
    clockU n * shiftV n = omegaN n • (shiftV n * clockU n) := by
  ext x j
  obtain ⟨i, rfl⟩ := (finRotate n.val).surjective j
  change omegaN n ^ (finRotate n.val i).val * x ((finRotate n.val).symm (finRotate n.val i)) =
    omegaN n * (omegaN n ^ ((finRotate n.val).symm (finRotate n.val i)).val *
      x ((finRotate n.val).symm (finRotate n.val i)))
  rw [Equiv.symm_apply_apply, omegaN_pow_rotate, mul_assoc]

-- @node: nuN_eq
/-- For [an admissible dimension n](hyp:n), [the clock–shift commutator norm equals the absolute
value of the clock phase minus one](goal). -/
lemma nuN_eq (n : ClockNat) : nuN n = ‖omegaN n - 1‖ := by
  let : NeZero n.val := ⟨by have := n.property; unfold ClockIndex at this; omega⟩
  have hdiff : clockU n * shiftV n - shiftV n * clockU n =
      (omegaN n - 1) • (shiftV n * clockU n) := by
    rw [sub_smul, one_smul, clock_shift_relation]
  rw [nuN, hdiff, norm_smul, CStarRing.norm_of_mem_unitary
      ((unitary _).mul_mem (shiftV_mem_unitary n) (clockU_mem_unitary n)), mul_one]

-- @node: omegaN_tendsto_one
/-- [The clock phase converges to one as the admissible dimension tends to infinity](goal). -/
lemma omegaN_tendsto_one : Tendsto omegaN atTop (𝓝 1) := by
  let : Nonempty ClockNat := ⟨⟨3, le_rfl⟩⟩
  have hval : Tendsto (fun n : ClockNat => n.val) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    refine eventually_atTop.2 ⟨⟨max 3 b, le_max_left _ _⟩, ?_⟩
    intro n hn
    exact le_trans (le_max_right _ _) hn
  have hinv : Tendsto (fun n : ClockNat => ((n.val : ℝ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hval)
  have harg : Tendsto (fun n : ClockNat => 2 * Real.pi * Complex.I / (n.val : ℂ))
      atTop (𝓝 0) := by
    simpa only [Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_zero,
      mul_zero, div_eq_mul_inv] using hinv.ofReal.const_mul (2 * Real.pi * Complex.I)
  unfold omegaN
  simpa only [Function.comp_def, Complex.exp_zero, Complex.ofReal_mul,
    Complex.ofReal_ofNat] using Complex.continuous_exp.continuousAt.tendsto.comp harg

-- @node: nuN_tendsto_zero
/-- [The clock–shift commutator norm converges to zero as the admissible dimension tends to infinity](goal). -/
lemma nuN_tendsto_zero : Tendsto nuN atTop (𝓝 0) := by
  simpa only [← nuN_eq, sub_self, norm_zero] using (omegaN_tendsto_one.sub_const 1).norm

-- @node: unitary_commutator_difference_norm_le
/-- In [a normed ring B with an adjoint satisfying the C-star norm identity](hyp:B), take
[elements U, V, U′, and V′](hyp:U,V,U',V'). If [U is unitary](hyp:hU), [V is unitary](hyp:hV),
[U′ is unitary](hyp:hU'), and [V′ is unitary](hyp:hV'), then [the distance between their multiplicative
commutators is at most twice the distance from U′ to U plus twice the distance from V′ to V](goal). -/
lemma unitary_commutator_difference_norm_le
    {B : Type*} [NormedRing B] [StarRing B] [CStarRing B]
    (U V U' V' : B) (hU : U ∈ unitary B) (hV : V ∈ unitary B)
    (hU' : U' ∈ unitary B) (hV' : V' ∈ unitary B) :
    ‖U' * V' * star U' * star V' - U * V * star U * star V‖ ≤
      2 * ‖U' - U‖ + 2 * ‖V' - V‖ := by
  have h₁ := Toolkit.Foundations.Analysis.Normed.norm_mul_sub_mul_le_of_mem_unitary U' V' U V hU' hV
  have h₂ := Toolkit.Foundations.Analysis.Normed.norm_mul_sub_mul_le_of_mem_unitary (star U') (star V') (star U) (star V)
    (Unitary.star_mem hU') (Unitary.star_mem hV)
  have h₃ := Toolkit.Foundations.Analysis.Normed.norm_mul_sub_mul_le_of_mem_unitary (U' * V') (star U' * star V')
    (U * V) (star U * star V) ((unitary B).mul_mem hU' hV')
    ((unitary B).mul_mem (Unitary.star_mem hU) (Unitary.star_mem hV))
  simp only [← star_sub, norm_star] at h₂
  simpa only [mul_assoc] using h₃.trans ((add_le_add h₁ h₂).trans_eq (by ring))

-- @node: clock_multiplicative_commutator
/-- For [an admissible dimension n](hyp:n), [the product of the clock, the shift, the clock's
adjoint, and the shift's adjoint equals the clock phase times the identity operator](goal). -/
lemma clock_multiplicative_commutator (n : ClockNat) :
    clockU n * shiftV n * star (clockU n) * star (shiftV n) =
      omegaN n • (1 : ClockSpace n →L[ℂ] ClockSpace n) := by
  rw [clock_shift_relation, smul_mul_assoc, smul_mul_assoc]
  congr 1
  rw [mul_assoc (shiftV n) (clockU n) (star (clockU n)),
    Unitary.mul_star_self_of_mem (clockU_mem_unitary n), mul_one,
    Unitary.mul_star_self_of_mem (shiftV_mem_unitary n)]

-- @node: clock_path_commutator_bound
/-- In [admissible dimension n](hyp:n), take [operators U and V](hyp:U,V) such that
[U is unitary](hyp:hU) and [V is unitary](hyp:hV). Then [the norm of their multiplicative
commutator minus the identity is at most the clock–shift commutator norm plus twice the distance
from U to the clock and twice the distance from V to the shift](goal). -/
lemma clock_path_commutator_bound (n : ClockNat)
    (U V : ClockSpace n →L[ℂ] ClockSpace n)
    (hU : U ∈ unitary _) (hV : V ∈ unitary _) :
    ‖U * V * star U * star V - 1‖ ≤
      nuN n + 2 * ‖U - clockU n‖ + 2 * ‖V - shiftV n‖ := by
  have hdiff := unitary_commutator_difference_norm_le
    (clockU n) (shiftV n) U V (clockU_mem_unitary n) (shiftV_mem_unitary n) hU hV
  have hn : ‖clockU n * shiftV n * star (clockU n) * star (shiftV n) - 1‖ = nuN n :=
    Toolkit.Foundations.Analysis.Normed.norm_mul_mul_star_mul_star_sub_one_eq_norm_commutator _ _ (clockU_mem_unitary n) (shiftV_mem_unitary n)
  calc
    _ ≤ ‖U * V * star U * star V -
        clockU n * shiftV n * star (clockU n) * star (shiftV n)‖ +
        ‖clockU n * shiftV n * star (clockU n) * star (shiftV n) - 1‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (2 * ‖U - clockU n‖ + 2 * ‖V - shiftV n‖) + nuN n :=
      add_le_add hdiff hn.le
    _ = _ := by ring

-- @node: clock_angle_bounds
/-- For [an admissible dimension n](hyp:n), [the angle 2π divided by n is strictly between zero and π](goal). -/
lemma clock_angle_bounds (n : ClockNat) :
    0 < 2 * Real.pi / (n.val : ℝ) ∧ 2 * Real.pi / (n.val : ℝ) < Real.pi := by
  have hn : (2 : ℝ) < n.val := by
    exact_mod_cast (show 2 < n.val from lt_of_lt_of_le (by decide) n.property)
  constructor
  · positivity
  · apply (div_lt_iff₀ (by positivity : (0 : ℝ) < n.val)).2
    nlinarith [Real.pi_pos]

-- @node: clock_principal_log
/-- For [an admissible dimension n](hyp:n), [the principal complex logarithm of the clock phase
equals 2πi divided by n](goal). -/
lemma clock_principal_log (n : ClockNat) :
    Complex.log (omegaN n) = 2 * Real.pi * Complex.I / (n.val : ℂ) := by
  apply Complex.log_exp
  · simpa [Complex.div_natCast, Complex.mul_re, Complex.mul_im] using
      lt_trans (neg_neg_of_pos Real.pi_pos) (clock_angle_bounds n).1
  · simpa [Complex.div_natCast, Complex.mul_re, Complex.mul_im] using
      (clock_angle_bounds n).2.le

-- @node: clock_logarithmic_trace
/-- For [an admissible dimension n](hyp:n), [the sum of n copies of the principal logarithm of
the clock phase equals 2πi](goal). -/
lemma clock_logarithmic_trace (n : ClockNat) :
    (∑ _j : Fin n.val, Complex.log (omegaN n)) = 2 * Real.pi * Complex.I := by
  have hn : (n.val : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by
    have := n.property
    unfold ClockIndex at this
    omega)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    clock_principal_log, mul_div_cancel₀ _ hn]


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

-- @node: finiteOperatorMatrix
/-- On [a finite-dimensional complex Hilbert space E](hyp:E), for [a finite coordinate index set](hyp:ι)
and [a basis b indexed by that set](hyp:b), [the operator-to-matrix map](goal) sends each continuous
linear operator to its matrix in b and preserves complex scalars, sums, products, and the identity. -/
noncomputable def finiteOperatorMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ E) : (E →L[ℂ] E) →ₐ[ℂ] Matrix ι ι ℂ where
  toFun T := LinearMap.toMatrix b b T.toLinearMap
  map_one' := by simp
  map_mul' T S := by simp [LinearMap.toMatrix_mul]
  map_zero' := by simp
  map_add' T S := by simp
  commutes' z := by
    classical
    ext i j
    simp [LinearMap.toMatrix_apply, Algebra.algebraMap_eq_smul_one, Matrix.one_apply, Finsupp.single_apply, eq_comm]

-- @node: finiteOperatorMatrix_continuous
/-- On a finite-dimensional complex Hilbert space E, for [a finite coordinate index set](hyp:ι)
and [a basis b indexed by that set](hyp:b), [the map sending an operator to its matrix in b is continuous](goal). -/
@[fun_prop] lemma finiteOperatorMatrix_continuous {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ E) : Continuous (finiteOperatorMatrix b) := by
  exact (finiteOperatorMatrix b).toLinearMap.continuous_of_finiteDimensional

-- @node: finiteOperatorTrace
/-- On [a finite-dimensional complex Hilbert space E](hyp:E), [the operator trace functional](goal)
is the continuous complex-linear map assigning to an operator its usual linear algebra trace. -/
noncomputable def finiteOperatorTrace : (E →L[ℂ] E) →L[ℂ] ℂ :=
  ((LinearMap.trace ℂ E).comp (ContinuousLinearMap.coeLM ℂ)).toContinuousLinearMap

-- @node: finiteOperatorTrace_apply
/-- For [a continuous linear operator T](hyp:T) on a finite-dimensional complex Hilbert space E,
[the operator trace functional equals the usual trace of T as a linear map](goal). -/
lemma finiteOperatorTrace_apply (T : E →L[ℂ] E) :
    finiteOperatorTrace T = LinearMap.trace ℂ E T.toLinearMap := rfl

set_option backward.isDefEq.respectTransparency false in
-- @node: selfAdjoint_exp_det_trace
/-- For [a self-adjoint operator A](hyp:A) on a finite-dimensional complex Hilbert space E,
[the determinant of the exponential of i times A equals the complex exponential of i times the trace of A](goal). -/
lemma selfAdjoint_exp_det_trace (A : selfAdjoint (E →L[ℂ] E)) :
    LinearMap.det (NormedSpace.exp (Complex.I • (A : E →L[ℂ] E))).toLinearMap =
      Complex.exp (Complex.I * finiteOperatorTrace (A : E →L[ℂ] E)) := by
  classical
  let : NormedAlgebra ℚ (E →L[ℂ] E) := .restrictScalars ℚ ℂ _
  have hA := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp A.property
  let b := (hA.eigenvectorBasis rfl).toBasis
  have hdiag : finiteOperatorMatrix b (A : E →L[ℂ] E) =
      Matrix.diagonal (fun i => (hA.eigenvalues rfl i : ℂ)) := by
    exact hA.toMatrix_eigenvectorBasis rfl
  have hexp := NormedSpace.map_exp (finiteOperatorMatrix b)
    (finiteOperatorMatrix_continuous b) (Complex.I • (A : E →L[ℂ] E))
  have hdet := LinearMap.det_toMatrix b (NormedSpace.exp (Complex.I • (A : E →L[ℂ] E))).toLinearMap
  rw [← hdet]
  change Matrix.det (finiteOperatorMatrix b (NormedSpace.exp (Complex.I • (A : E →L[ℂ] E)))) = _
  rw [hexp, map_smul, hdiag, ← Matrix.diagonal_smul, Matrix.exp_diagonal, Matrix.det_diagonal]
  simp only [Pi.coe_exp, Pi.smul_apply, smul_eq_mul, ← Complex.exp_eq_exp_ℂ]
  rw [← Complex.exp_sum]
  congr 1
  rw [finiteOperatorTrace_apply, hA.trace_eq_sum_eigenvalues rfl, ← Finset.mul_sum]
  simp

-- @node: unitaryLogTrace
/-- For [a unitary operator u](hyp:u) on [a finite-dimensional complex Hilbert space E](hyp:E),
[the logarithmic trace](goal) is i times the trace of the self-adjoint argument of u. -/
noncomputable def unitaryLogTrace (u : unitary (E →L[ℂ] E)) : ℂ :=
  Complex.I * finiteOperatorTrace (Unitary.argSelfAdjoint u : E →L[ℂ] E)

-- @node: unitaryLogTrace_exp
/-- For [a unitary operator u](hyp:u) on a finite-dimensional complex Hilbert space E,
if [its operator norm distance from the identity is less than two](hyp:hu), then
[the complex exponential of its logarithmic trace equals its determinant](goal). -/
lemma unitaryLogTrace_exp (u : unitary (E →L[ℂ] E))
    (hu : ‖(u : E →L[ℂ] E) - 1‖ < 2) :
    Complex.exp (unitaryLogTrace u) = LinearMap.det (u : E →L[ℂ] E).toLinearMap := by
  have heq : NormedSpace.exp (Complex.I • (Unitary.argSelfAdjoint u : E →L[ℂ] E)) =
      (u : E →L[ℂ] E) :=
    congrArg Subtype.val (expUnitary_argSelfAdjoint hu)
  rw [unitaryLogTrace, ← selfAdjoint_exp_det_trace, heq]

-- @node: unitaryLogTrace_continuousOn
/-- On a finite-dimensional complex Hilbert space E, [the logarithmic trace is continuous
on the open ball of radius two about the identity in the unitary group](goal). -/
@[fun_prop] lemma unitaryLogTrace_continuousOn :
    ContinuousOn (unitaryLogTrace (E := E)) (Metric.ball 1 2) := by
  unfold unitaryLogTrace
  exact continuousOn_const.mul (finiteOperatorTrace.continuous.comp_continuousOn
    (continuous_subtype_val.comp_continuousOn Unitary.continuousOn_argSelfAdjoint))

-- @node: unitaryLogTrace_one
/-- On a finite-dimensional complex Hilbert space E, [the logarithmic trace of the identity is zero](goal). -/
lemma unitaryLogTrace_one : unitaryLogTrace (1 : unitary (E →L[ℂ] E)) = 0 := by
  simp [unitaryLogTrace, Unitary.argSelfAdjoint]

-- @node: unitary_commutator_det_one
/-- For [unitary operators U and V](hyp:U,V) on a finite-dimensional complex Hilbert space E,
[the determinant of the product of U, V, the adjoint of U, and the adjoint of V is one](goal). -/
lemma unitary_commutator_det_one (U V : unitary (E →L[ℂ] E)) :
    LinearMap.det ((U * V * star U * star V : unitary (E →L[ℂ] E)) : E →L[ℂ] E).toLinearMap = 1 := by
  have hU : LinearMap.det (U : E →L[ℂ] E).toLinearMap *
      LinearMap.det (star (U : E →L[ℂ] E)).toLinearMap = 1 := by
    rw [← map_mul]
    change LinearMap.det ((U : E →L[ℂ] E) * star (U : E →L[ℂ] E)).toLinearMap = 1
    rw [Unitary.mul_star_self_of_mem U.property]
    exact map_one _
  have hV : LinearMap.det (V : E →L[ℂ] E).toLinearMap *
      LinearMap.det (star (V : E →L[ℂ] E)).toLinearMap = 1 := by
    rw [← map_mul]
    change LinearMap.det ((V : E →L[ℂ] E) * star (V : E →L[ℂ] E)).toLinearMap = 1
    rw [Unitary.mul_star_self_of_mem V.property]
    exact map_one _
  change LinearMap.det ((U : E →L[ℂ] E).toLinearMap * (V : E →L[ℂ] E).toLinearMap *
    (star (U : E →L[ℂ] E)).toLinearMap * (star (V : E →L[ℂ] E)).toLinearMap) = 1
  simp only [map_mul]
  calc
    _ = (LinearMap.det (U : E →L[ℂ] E).toLinearMap *
          LinearMap.det (star (U : E →L[ℂ] E)).toLinearMap) *
        (LinearMap.det (V : E →L[ℂ] E).toLinearMap *
          LinearMap.det (star (V : E →L[ℂ] E)).toLinearMap) := by ring
    _ = 1 := by rw [hU, hV, one_mul]

-- @node: unitaryLogTrace_path_constant
/-- On a finite-dimensional complex Hilbert space E, take [two continuous paths P and Q
of unitary operators, parametrized from zero to one](hyp:P,Q). If [their multiplicative commutator
stays at operator norm distance less than two from the identity throughout the paths](hyp:hsmall), then
[the logarithmic trace of that commutator is the same at the two endpoints](goal). -/
lemma unitaryLogTrace_path_constant
    (P Q : C(unitInterval, unitary (E →L[ℂ] E)))
    (hsmall : ∀ s, ‖((P s * Q s * star (P s) * star (Q s) : unitary (E →L[ℂ] E)) :
      E →L[ℂ] E) - 1‖ < 2) :
    unitaryLogTrace (P 0 * Q 0 * star (P 0) * star (Q 0)) =
      unitaryLogTrace (P 1 * Q 1 * star (P 1) * star (Q 1)) := by
  let W : C(unitInterval, unitary (E →L[ℂ] E)) :=
    ⟨fun s => P s * Q s * star (P s) * star (Q s), by fun_prop⟩
  have hW : Set.MapsTo W Set.univ (Metric.ball 1 2) := by
    intro s _
    simpa [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm, W] using hsmall s
  have hL : ContinuousOn (fun s => unitaryLogTrace (W s)) Set.univ :=
    unitaryLogTrace_continuousOn.comp W.continuous.continuousOn hW
  apply Toolkit.Foundations.Analysis.SpecialFunctions.eq_of_cexp_eq_one_of_isPreconnected isPreconnected_univ hL _ (Set.mem_univ 0) (Set.mem_univ 1)
  intro s _
  exact (unitaryLogTrace_exp (W s) (hsmall s)).trans (unitary_commutator_det_one (P s) (Q s))

-- @node: clock_commutator_log_trace
/-- For [a dimension n of at least three](hyp:n), [the logarithmic trace of the multiplicative
commutator of the clock and cyclic shift operators equals 2πi](goal). -/
lemma clock_commutator_log_trace (n : ClockNat) :
    unitaryLogTrace (⟨clockU n, clockU_mem_unitary n⟩ *
      ⟨shiftV n, shiftV_mem_unitary n⟩ * star ⟨clockU n, clockU_mem_unitary n⟩ *
      star ⟨shiftV n, shiftV_mem_unitary n⟩) = 2 * Real.pi * Complex.I := by
  change Complex.I * finiteOperatorTrace
    (cfc (fun z : ℂ => (z.arg : ℂ))
      (clockU n * shiftV n * star (clockU n) * star (shiftV n))) = _
  rw [clock_multiplicative_commutator]
  rw [← Algebra.algebraMap_eq_smul_one, cfc_algebraMap, Algebra.algebraMap_eq_smul_one]
  rw [map_smul, finiteOperatorTrace_apply, show
    (1 : ClockSpace n →L[ℂ] ClockSpace n).toLinearMap = 1 from rfl, LinearMap.trace_one]
  have hlog : Complex.I * (Complex.arg (omegaN n) : ℂ) = Complex.log (omegaN n) := by
    apply Complex.ext <;> simp [Complex.log_re, Complex.log_im, omegaN_norm]
  rw [smul_eq_mul, ← mul_assoc, hlog]
  have hdim : Module.finrank ℂ (ClockSpace n) = n.val := by simp [ClockSpace]
  rw [hdim, mul_comm]
  simpa using clock_logarithmic_trace n

-- @node: unitary_path_distance_le
/-- In [a C*-algebra B](hyp:B), take [two unitary elements u and v](hyp:u,v) whose
[norm distance is less than two](hyp:huv). At [any time s between zero and one](hyp:s),
[the canonical unitary path from u to v is no farther from u than v is](goal). -/
lemma unitary_path_distance_le {B : Type*} [CStarAlgebra B]
    (u v : unitary B) (huv : ‖(v : B) - (u : B)‖ < 2) (s : unitInterval) :
    ‖(Unitary.path u v huv s : B) - (u : B)‖ ≤ ‖(v : B) - (u : B)‖ := by
  have hsmall : ‖((v * star u : unitary B) : B) - 1‖ < 2 :=
    (Unitary.norm_sub_eq v u) ▸ huv
  calc
    _ = ‖((selfAdjoint.expUnitary ((s : ℝ) • Unitary.argSelfAdjoint (v * star u)) : B) - 1) *
        (u : B)‖ := by simp only [sub_mul, one_mul]; rfl
    _ = ‖(selfAdjoint.expUnitary ((s : ℝ) • Unitary.argSelfAdjoint (v * star u)) : B) - 1‖ :=
      CStarRing.norm_mul_mem_unitary _ u.property
    _ ≤ ‖((v * star u : unitary B) : B) - 1‖ :=
      Unitary.norm_expUnitary_smul_argSelfAdjoint_sub_one_le (v * star u) s.property hsmall
    _ = _ := (Unitary.norm_sub_eq v u).symm

-- @node: clock_no_close_commuting_pair
/-- In [a dimension n of at least three](hyp:n), take [operators Uhat and Vhat on complex
Euclidean space](hyp:Uhat,Vhat) such that [Uhat is unitary](hyp:hUhat),
[Vhat is unitary](hyp:hVhat), and [the two operators commute](hyp:hcomm).
If [the clock–shift commutator norm plus twice the norm distance from Uhat to the clock
operator plus twice the norm distance from Vhat to the cyclic shift is less than two](hyp:hbudget),
[these commuting unitary approximations yield a contradiction](goal). -/
lemma clock_no_close_commuting_pair (n : ClockNat)
    (Uhat Vhat : ClockSpace n →L[ℂ] ClockSpace n)
    (hUhat : Uhat ∈ unitary _) (hVhat : Vhat ∈ unitary _) (hcomm : Commute Uhat Vhat)
    (hbudget : nuN n + 2 * ‖Uhat - clockU n‖ + 2 * ‖Vhat - shiftV n‖ < 2) : False := by
  have hnu : 0 ≤ nuN n := norm_nonneg _
  have hUdist : ‖Uhat - clockU n‖ < 2 := by nlinarith [norm_nonneg (Vhat - shiftV n)]
  have hVdist : ‖Vhat - shiftV n‖ < 2 := by nlinarith [norm_nonneg (Uhat - clockU n)]
  let u : unitary (ClockSpace n →L[ℂ] ClockSpace n) := ⟨clockU n, clockU_mem_unitary n⟩
  let v : unitary (ClockSpace n →L[ℂ] ClockSpace n) := ⟨shiftV n, shiftV_mem_unitary n⟩
  let uh : unitary (ClockSpace n →L[ℂ] ClockSpace n) := ⟨Uhat, hUhat⟩
  let vh : unitary (ClockSpace n →L[ℂ] ClockSpace n) := ⟨Vhat, hVhat⟩
  let P := Unitary.path u uh hUdist
  let Q := Unitary.path v vh hVdist
  have hP (s : unitInterval) : ‖(P s : ClockSpace n →L[ℂ] ClockSpace n) - clockU n‖ ≤
      ‖Uhat - clockU n‖ := unitary_path_distance_le u uh hUdist s
  have hQ (s : unitInterval) : ‖(Q s : ClockSpace n →L[ℂ] ClockSpace n) - shiftV n‖ ≤
      ‖Vhat - shiftV n‖ := unitary_path_distance_le v vh hVdist s
  have hsmall (s : unitInterval) :
      ‖((P s * Q s * star (P s) * star (Q s) : unitary (ClockSpace n →L[ℂ] ClockSpace n)) :
        ClockSpace n →L[ℂ] ClockSpace n) - 1‖ < 2 := by
    have hb := clock_path_commutator_bound n (P s) (Q s) (P s).property (Q s).property
    exact hb.trans_lt (lt_of_le_of_lt (by linarith [hP s, hQ s]) hbudget)
  have hconst := unitaryLogTrace_path_constant P.toContinuousMap Q.toContinuousMap hsmall
  have hW : uh * vh * star uh * star vh = 1 := by
    apply Subtype.ext
    change Uhat * Vhat * star Uhat * star Vhat = 1
    rw [hcomm.eq, mul_assoc Vhat Uhat (star Uhat), Unitary.mul_star_self_of_mem hUhat,
      mul_one, Unitary.mul_star_self_of_mem hVhat]
  have hends : unitaryLogTrace (u * v * star u * star v) = 0 := by
    change unitaryLogTrace (P 0 * Q 0 * star (P 0) * star (Q 0)) =
      unitaryLogTrace (P 1 * Q 1 * star (P 1) * star (Q 1)) at hconst
    simpa only [P.source, Q.source, P.target, Q.target, hW, unitaryLogTrace_one] using hconst
  have hindex : unitaryLogTrace (u * v * star u * star v) = 2 * Real.pi * Complex.I :=
    clock_commutator_log_trace n
  have hnonzero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  exact hnonzero (hindex.symm.trans hends)

-- @node: lem:clock
/-- [In every dimension of at least three, the clock–shift commutator norm equals the distance
of the clock phase from one; these commutator norms tend to zero as the dimension increases,
yet along no strictly increasing sequence of admissible dimensions can commuting unitary pairs
approximate the clock and cyclic shift with the sum of their operator norm errors tending to zero](goal). -/
lemma clock_shift_not_near_commuting :
    (∀ (n : ℕ) (hn : ClockIndex n), nuN ⟨n, hn⟩ = ‖omegaN ⟨n, hn⟩ - 1‖) ∧
    Tendsto nuN atTop (𝓝 0) ∧
    ¬ ∃ (φ : ℕ → ClockNat)
      (Uhat Vhat : ∀ k, ClockSpace (φ k) →L[ℂ] ClockSpace (φ k)),
      StrictMono φ ∧
      (∀ k, Uhat k ∈ unitary _ ∧ Vhat k ∈ unitary _ ∧ Commute (Uhat k) (Vhat k)) ∧ -- @realizes \widehat U_n(first hypothetical commuting unitary) @realizes \widehat V_n(second hypothetical commuting unitary)
      Tendsto (fun k => ‖Uhat k - clockU (φ k)‖ + ‖Vhat k - shiftV (φ k)‖)
        atTop (𝓝 0) := by
  refine ⟨fun n hn => nuN_eq ⟨n, hn⟩, nuN_tendsto_zero, ?_⟩
  rintro ⟨φ, Uhat, Vhat, hφ, hunit, herr⟩
  have hφnat : StrictMono (fun k => (φ k).val) := hφ
  have ht : Filter.Tendsto φ Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    exact hφnat.tendsto_atTop.eventually (Filter.eventually_ge_atTop b.val)
  have hb : Filter.Tendsto
      (fun k => nuN (φ k) + 2 * (‖Uhat k - clockU (φ k)‖ + ‖Vhat k - shiftV (φ k)‖))
      Filter.atTop (𝓝 0) := by
    simpa using (nuN_tendsto_zero.comp ht).add (herr.const_mul 2)
  obtain ⟨k, hk⟩ := ((tendsto_order.1 hb).2 2 (by norm_num)).exists
  apply clock_no_close_commuting_pair (φ k) (Uhat k) (Vhat k)
    (hunit k).1 (hunit k).2.1 (hunit k).2.2
  linarith

end Papers.OaiNearInclusionsVon
