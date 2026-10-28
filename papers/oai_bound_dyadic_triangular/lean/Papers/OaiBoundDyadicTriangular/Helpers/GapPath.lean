module

public import Papers.OaiBoundDyadicTriangular.Helpers.MatrixHessian
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

/-! # Supported positive paths for the midpoint gap -/

public section

open Matrix Filter
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace MatrixOrder Topology

namespace Papers.OaiBoundDyadicTriangular

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- @node: gap_supportedOn
/-- If [both T + U and T − U are positive semidefinite](hyp:hOrder), then
[U annihilates every vector in the kernel of T](goal). -/
lemma gap_supportedOn (T U : Matrix ι ι ℝ) (hOrder : GapOrder T U) :
    SupportedOn T U := by
  have hc : OrderComparison (T + U) T 2 := by
    unfold OrderComparison
    convert hOrder.2 using 1 <;> module
  have h := annihilatesKernel_of_orderComparison (T + U) T 2 hOrder.1 hc
  refine ⟨fun x hx => ?_⟩
  have he := h x hx
  simpa only [Matrix.add_mulVec, hx, zero_add] using he

-- @node: gap_path_lower
/-- If [T + U and T − U are positive semidefinite](hyp:hOrder), then, for every
real t, [T + tU is at least (1 − |t|)T in the positive semidefinite order](goal). -/
lemma gap_path_lower (T U : Matrix ι ι ℝ) (hOrder : GapOrder T U)
    (t : ℝ) : (T + t • U - (1 - |t|) • T).PosSemidef := by
  by_cases ht : 0 ≤ t
  · have he : T + t • U - (1 - |t|) • T = t • (T + U) := by
      rw [abs_of_nonneg ht]
      module
    rw [he]
    exact hOrder.1.smul ht
  · have he : T + t • U - (1 - |t|) • T = (-t) • (T - U) := by
      rw [abs_of_neg (lt_of_not_ge ht)]
      module
    rw [he]
    exact hOrder.2.smul (neg_nonneg.mpr (le_of_not_ge ht))

-- @node: gap_path_positive
/-- If [T is positive semidefinite](hyp:hT), [T + U and T − U are positive
semidefinite](hyp:hOrder), and [|t| ≤ 1](hyp:ht), then
[T + tU is positive semidefinite](goal). -/
lemma gap_path_positive (T U : Matrix ι ι ℝ) (hT : T.PosSemidef)
    (hOrder : GapOrder T U) (t : ℝ) (ht : |t| ≤ 1) :
    (T + t • U).PosSemidef := by
  have h := ((hT.smul (sub_nonneg.mpr ht)).add (gap_path_lower T U hOrder t))
  convert h using 1 <;> module

-- @node: gap_path_upper
/-- If [T is positive semidefinite](hyp:hT), [T + U and T − U are positive
semidefinite](hyp:hOrder), and [|t| ≤ 1](hyp:ht), then
[T + tU is at most 2T in the positive semidefinite order](goal). -/
lemma gap_path_upper (T U : Matrix ι ι ℝ) (hT : T.PosSemidef)
    (hOrder : GapOrder T U) (t : ℝ) (ht : |t| ≤ 1) :
    OrderComparison (T + t • U) T 2 := by
  have h := gap_path_positive T U hT hOrder (-t) (by simpa using ht)
  change ((2 : ℝ) • T - (T + t • U)).PosSemidef
  have he : (2 : ℝ) • T - (T + t • U) = T + (-t) • U := by module
  rw [he]
  exact h

-- @node: gap_path_kernel
/-- If [T is positive semidefinite](hyp:hT), [T + U and T − U are positive
semidefinite](hyp:hOrder), and [|t| < 1](hyp:ht), then
[every vector annihilated by T + tU is also annihilated by T](goal). -/
lemma gap_path_kernel (T U : Matrix ι ι ℝ) (hT : T.PosSemidef)
    (hOrder : GapOrder T U) (t : ℝ) (ht : |t| < 1) :
    AnnihilatesKernel (T + t • U) T := by
  have hLower := gap_path_lower T U hOrder t
  have hKer := annihilatesKernel_of_orderComparison ((1 - |t|) • T)
    (T + t • U) 1 (hT.smul (by linarith)) (by simpa [OrderComparison] using hLower)
  intro x hx
  have he := hKer x hx
  rw [Matrix.smul_mulVec] at he
  exact (smul_eq_zero.mp he).resolve_left (by linarith)

-- @node: gap_path_mem_locus
/-- If [T is positive semidefinite](hyp:hT), [U is symmetric](hyp:hU),
[T + U and T − U are positive semidefinite](hyp:hOrder), and [|t| < 1](hyp:ht),
then [T + tU, viewed as a symmetric matrix supported on T, is strictly positive
on every nonzero vector orthogonal to the kernel of T](goal). -/
lemma gap_path_mem_locus (T U : Matrix ι ι ℝ) (hT : T.PosSemidef)
    (hU : U.IsSymm) (hOrder : GapOrder T U) (t : ℝ) (ht : |t| < 1) :
    let p : supportedTangent T := ⟨T, base_mem_supportedTangent T hT⟩
    let d : supportedTangent T :=
      ⟨U, (mem_supportedTangent T U).mpr ⟨hU, (gap_supportedOn T U hOrder).annihilates⟩⟩
    p + t • d ∈ positiveSupportLocus T := by
  intro p d x hx
  have hPos := gap_path_positive T U hT hOrder t ht.le
  have hi : inner ℝ x.val (Matrix.toEuclideanLin (T + t • U) x.val) =
      star (WithLp.ofLp x.val) ⬝ᵥ (T + t • U) *ᵥ WithLp.ofLp x.val := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanLin_apply,
      dotProduct_comm]
  change 0 < inner ℝ x.val (Matrix.toEuclideanLin (T + t • U) x.val)
  rw [hi]
  apply lt_of_le_of_ne (hPos.dotProduct_mulVec_nonneg _)
  intro he
  have hzero := (hPos.dotProduct_mulVec_zero_iff _).mp he.symm
  have hTx := gap_path_kernel T U hT hOrder t ht _ hzero
  have hker : x.val ∈ LinearMap.ker (Matrix.toEuclideanLin T) := by
    rw [LinearMap.mem_ker, Matrix.toEuclideanLin_apply, hTx]
    rfl
  exact hx (Subtype.ext (inner_self_eq_zero.mp (x.property x.val hker)))


-- @node: midpoint_gap_of_second_derivative
/-- If [f is continuous on the closed interval from −1 to 1](hyp:hf),
[its derivative on the interior is f′](hyp:hd), [the derivative of f′ there is
f″](hyp:hdd), and [f″ is bounded below by c there](hyp:hb), then
[the average of f(1) and f(−1), minus f(0), is at least c/2](goal). -/
lemma midpoint_gap_of_second_derivative (f f' f'' : ℝ → ℝ) (c : ℝ)
    (hf : ContinuousOn f (Set.Icc (-1) 1))
    (hd : ∀ t ∈ Set.Ioo (-1) 1, HasDerivAt f (f' t) t)
    (hdd : ∀ t ∈ Set.Ioo (-1) 1, HasDerivAt f' (f'' t) t)
    (hb : ∀ t ∈ Set.Ioo (-1) 1, c ≤ f'' t) :
    c / 2 ≤ (f 1 + f (-1)) / 2 - f 0 := by
  let g := fun t => f t - c / 2 * t ^ 2
  let g' := fun t => f' t - c * t
  have hg (t : ℝ) (ht : t ∈ Set.Ioo (-1) 1) : HasDerivAt g (g' t) t := by
    convert (hd t ht).sub (((hasDerivAt_id t).pow 2).const_mul (c / 2)) using 1 <;>
      first | rfl | (dsimp [g, g']; ring)
  have hgg (t : ℝ) (ht : t ∈ Set.Ioo (-1) 1) :
      HasDerivAt (deriv g) (f'' t - c) t := by
    have he : deriv g =ᶠ[𝓝 t] g' := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact (hg s hs).deriv
    simpa using ((hdd t ht).sub ((hasDerivAt_id t).const_mul c)).congr_of_eventuallyEq he
  have hconv : ConvexOn ℝ (Set.Icc (-1) 1) g := by
    apply convexOn_of_deriv2_nonneg (convex_Icc _ _)
    · exact hf.sub (by fun_prop)
    · intro t ht
      exact (hg t (by simpa using ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      exact (hgg t (by simpa using ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      change 0 ≤ deriv (deriv g) t
      rw [(hgg t (by simpa using ht)).deriv]
      exact sub_nonneg.mpr (hb t (by simpa using ht))
  have hm := (hconv.2) (show (-1 : ℝ) ∈ Set.Icc (-1) 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Set.Icc (-1) 1 by constructor <;> norm_num)
    (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  norm_num [g, smul_eq_mul] at hm
  linarith

end Papers.OaiBoundDyadicTriangular
