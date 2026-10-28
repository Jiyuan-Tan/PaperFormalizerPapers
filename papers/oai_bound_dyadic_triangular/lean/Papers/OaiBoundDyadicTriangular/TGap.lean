module

public import Papers.OaiBoundDyadicTriangular.Helpers.GapPath

/-! # The matrix-energy midpoint gap -/

public section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace MatrixOrder

namespace Papers.OaiBoundDyadicTriangular

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- @node: thm:gap
/-- If [T is positive semidefinite](hyp:hPositive), [U is symmetric](hyp:hSymmetry),
and [both T minus U and T plus U are positive semidefinite](hyp:hOrder), then
[U annihilates the kernel of T, and the average matrix energy at T plus U and
T minus U, less the energy at T, is at least the supported Hessian form at T
in direction U divided by twice the square root of two](goal). -/
theorem matrixEnergy_midpoint_gap (T U : Matrix ι ι ℝ)
    (hPositive : GapPositive T) (hSymmetry : GapSymmetry U) (hOrder : GapOrder T U) :
    SupportedOn T U ∧
    1 / (2 * Real.sqrt 2) * hessForm T hPositive.isHermitian U ≤
      (matrixEnergy (T + U) + matrixEnergy (T - U)) / 2 - matrixEnergy T := by
  have hSupport := gap_supportedOn T U hOrder
  refine ⟨hSupport, ?_⟩
  let E := supportedTangent T
  let p : E := ⟨T, base_mem_supportedTangent T hPositive⟩
  let d : E := ⟨U, (mem_supportedTangent T U).mpr ⟨hSymmetry, hSupport.annihilates⟩⟩
  let Φ : E → ℝ := fun Q => matrixEnergy Q.val
  let f : ℝ → ℝ := fun t => Φ (p + t • d)
  let f' : ℝ → ℝ := fun t => fderiv ℝ Φ (p + t • d) d
  let f'' : ℝ → ℝ := fun t => fderiv ℝ (fderiv ℝ Φ) (p + t • d) d d
  obtain ⟨_, ho, hsmooth, hform, _⟩ :=
    matrixEnergy_hessian T U hPositive ⟨hSymmetry, hSupport.annihilates⟩
  have hlocus (t : ℝ) (ht : t ∈ Set.Ioo (-1) 1) :
      p + t • d ∈ positiveSupportLocus T :=
    gap_path_mem_locus T U hPositive hSymmetry hOrder t (abs_lt.mpr ht)
  have hderiv (t : ℝ) (ht : t ∈ Set.Ioo (-1) 1) :
      HasDerivAt f (f' t) t ∧ HasDerivAt f' (f'' t) t :=
    supported_line_hasDerivAt Φ p d _ ho hsmooth t (hlocus t ht)
  have hbound (t : ℝ) (ht : t ∈ Set.Ioo (-1) 1) :
      (Real.sqrt 2)⁻¹ * hessForm T hPositive.isHermitian U ≤ f'' t := by
    have ht' : |t| < 1 := abs_lt.mpr ht
    have hPos := gap_path_positive T U hPositive hOrder t ht'.le
    have hDir : OrderDirection (T + t • U) U :=
      ⟨hSymmetry, fun x hx => hSupport.annihilates x
        (gap_path_kernel T U hPositive hOrder t ht' x hx)⟩
    have hb := (hessForm_order (T + t • U) T U 2 ⟨hPos, hPositive⟩
      (by norm_num [OrderFactor]) (gap_path_upper T U hPositive hOrder t ht'.le) hDir).2
    have hp : (2 : ℝ) ^ (-1 / 2 : ℝ) = (Real.sqrt 2)⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      norm_num
    rw [hp] at hb
    change _ ≤ fderiv ℝ (fderiv ℝ Φ) (p + t • d) d d
    rw [(hform (p + t • d) (hlocus t ht) d).2]
    exact hb
  have hg := midpoint_gap_of_second_derivative f f' f''
    ((Real.sqrt 2)⁻¹ * hessForm T hPositive.isHermitian U)
    (matrixEnergy_line_continuous T U hPositive.isHermitian
      (Matrix.isHermitian_iff_isSymm.mpr hSymmetry)).continuousOn
    (fun t ht => (hderiv t ht).1) (fun t ht => (hderiv t ht).2) hbound
  have he : (Real.sqrt 2)⁻¹ * hessForm T hPositive.isHermitian U / 2 =
      1 / (2 * Real.sqrt 2) * hessForm T hPositive.isHermitian U := by ring
  rw [he] at hg
  simpa [f, Φ, p, d, E, sub_eq_add_neg] using hg

end Papers.OaiBoundDyadicTriangular
