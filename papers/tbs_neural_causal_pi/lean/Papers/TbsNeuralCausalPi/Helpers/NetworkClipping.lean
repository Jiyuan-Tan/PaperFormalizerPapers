module
public import Papers.TbsNeuralCausalPi.Helpers.WideChartApprox
/-! # Coordinate clipping inside the ReLU architecture

Two extra hidden layers implement clipping into a fixed interval. Clipping
fixes the target box and does not increase coordinate or one-norm error.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open scoped NNReal
noncomputable section

-- @node: coordinateClamp
/-- For [a lower bound](hyp:a), [an upper bound](hyp:b), and [an input vector](hyp:x),
[coordinatewise clamping](goal) first caps each coordinate at the upper bound and then
raises it to at least the lower bound. -/
def coordinateClamp {d : ℕ} (a b : ℝ) (x : L1Vec d) : L1Vec d :=
  WithLp.toLp 1 (fun j => max a (min (x.ofLp j) b))

-- @node: coordinateClamp_relu_identity
/-- If [the lower bound does not exceed the upper bound](hyp:hab), [clamping a real
number to this interval equals the upper bound minus the ReLU of the interval length
minus the ReLU of the number minus the lower bound](goal). -/
lemma coordinateClamp_relu_identity (a b x : ℝ) (hab : a ≤ b) :
    b - max 0 (b-a-max 0 (x-a)) = max a (min x b) := by
  by_cases hxa : x ≤ a
  · rw [max_eq_left (by linarith : x-a ≤ 0), sub_zero,
      max_eq_right (sub_nonneg.mpr hab), min_eq_left (hxa.trans hab), max_eq_left hxa]
    ring
  · have hax : a ≤ x := (lt_of_not_ge hxa).le
    rw [max_eq_right (sub_nonneg.mpr hax)]
    by_cases hxb : x ≤ b
    · rw [max_eq_right (by linarith : 0 ≤ b-a-(x-a)), min_eq_left hxb,
        max_eq_right hax]
      ring
    · rw [max_eq_left (by linarith : b-a-(x-a) ≤ 0), min_eq_right (le_of_not_ge hxb),
        max_eq_right hab, sub_zero]

-- @node: diagonalWeight
/-- For [a matrix dimension](hyp:d) and [a scalar](hyp:c), [the diagonal weight matrix](goal)
has that scalar on its diagonal and zero elsewhere. -/
def diagonalWeight (d : ℕ) (c : ℝ) : Fin d → Fin d → ℝ :=
  fun j i => if i = j then c else 0

-- @node: diagonalWeight_sum
/-- [Multiplying a vector by a diagonal matrix with a common diagonal entry gives,
at any chosen coordinate, that entry times the corresponding vector coordinate](goal). -/
lemma diagonalWeight_sum {d : ℕ} (c : ℝ) (x : Fin d → ℝ) (j : Fin d) :
    (∑ i, diagonalWeight d c j i * x i) = c * x j := by
  classical
  simp [diagonalWeight]

-- @node: relu_affine_coordinateClamp
/-- If [the lower clipping bound does not exceed the upper bound](hyp:hab),
[any affine map followed by coordinatewise clipping to these bounds is exactly
represented by a ReLU network with two hidden layers and width bounded by the
output dimension](goal). -/
lemma relu_affine_coordinateClamp {k d : ℕ}
    (A : Fin d → Fin k → ℝ) (v : Fin d → ℝ)
    (a b : ℝ) (hab : a ≤ b) :
    ∃ Q : ReLUNet k d d 2, ∀ x j,
      (Q.eval x).ofLp j = max a (min ((∑ i, A j i * x.ofLp i) + v j) b) := by
  classical
  let first : AffineLayer := ⟨k, d, A, fun j => v j-a⟩
  let second : AffineLayer := ⟨d, d, diagonalWeight d (-1), fun _ => b-a⟩
  let out : ReLUNet d d d 0 := affineNet (diagonalWeight d (-1)) (fun _ => b)
  let tail : ReLUNet d d d 1 := prependNet second rfl le_rfl out
  let Q : ReLUNet k d d 2 := prependNet first rfl le_rfl tail
  refine ⟨Q, ?_⟩
  intro x j
  erw [show Q = prependNet first rfl le_rfl tail from rfl, prependNet_eval]
  erw [show tail = prependNet second rfl le_rfl out from rfl, prependNet_eval]
  erw [show out = affineNet (diagonalWeight d (-1)) (fun _ => b) from rfl, affineNet_eval]
  erw [diagonalWeight_sum, layerVector_apply]
  change -1 * max 0 ((∑ i : Fin d, diagonalWeight d (-1) j i *
    (if h : i.val < d then (layerVector first x).ofLp ⟨i.val, h⟩ else 0)) + (b-a)) + b = _
  simp only [dif_pos (Fin.isLt _)]
  erw [diagonalWeight_sum, layerVector_apply]
  change -1 * max 0 (-1 * max 0 ((∑ i : Fin k, A j i *
    (if h : i.val < k then x.ofLp ⟨i.val, h⟩ else 0)) + (v j-a)) + (b-a)) + b = _
  simp only [dif_pos (Fin.isLt _)]
  have h := coordinateClamp_relu_identity a b ((∑ i, A j i * x.ofLp i) + v j) hab
  ring_nf at h ⊢
  exact h

-- @node: relu_coordinateClamp
/-- If [the lower clipping bound does not exceed the upper bound](hyp:hab),
[clipping the output of any ReLU network is exactly represented by a ReLU network
with two additional hidden layers and width bounded by the larger of the original
width bound and the output dimension](goal). -/
lemma relu_coordinateClamp {k d W L : ℕ} (q : ReLUNet k d W L)
    (a b : ℝ) (hab : a ≤ b) :
    ∃ Q : ReLUNet k d (max W d) (L+2), Q.eval = coordinateClamp a b ∘ q.eval := by
  classical
  induction L generalizing k with
  | zero =>
    rcases q with ⟨ls, hd, hw, hf, hc, ow, ob⟩
    have hs : ls = [] := List.length_eq_zero_iff.mp hd
    subst ls
    obtain ⟨Q, hQ⟩ := relu_affine_coordinateClamp ow ob a b hab
    refine ⟨Q.widen (le_max_right W d), ?_⟩
    funext x
    apply PiLp.ext
    intro j
    erw [ReLUNet.widen_eval, hQ]
    change max a (min _ b) = max a (min _ b)
    congr 2
    change (∑ i : Fin k, ow j i * x.ofLp i) + ob j =
      (∑ i : Fin k, ow j i * (if h : i.val < k then x.ofLp ⟨i.val, h⟩ else 0)) + ob j
    simp only [dif_pos (Fin.isLt _)]
  | succ L ih =>
    obtain ⟨l, hl, hw, r, hq⟩ := exists_relu_head q
    obtain ⟨R, hR⟩ := ih r
    refine ⟨prependNet l hl (hw.trans (le_max_left W d)) R, ?_⟩
    funext x
    rw [prependNet_eval, hR, hq]
    dsimp only [Function.comp_apply]
    rw [prependNet_eval]

-- @node: coordinateClamp_mapsTo
/-- If [the lower bound does not exceed the upper bound](hyp:hab), [every coordinate
of every clamped vector lies in the closed interval between these bounds](goal). -/
lemma coordinateClamp_mapsTo {d : ℕ} (a b : ℝ) (hab : a ≤ b) :
    ∀ x : L1Vec d, ∀ j, (coordinateClamp a b x).ofLp j ∈ Set.Icc a b := by
  intro x j
  exact ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩

-- @node: coordinateClamp_fixes
/-- If [every coordinate of a vector lies between the clipping bounds](hyp:hx),
[coordinatewise clamping leaves that vector unchanged](goal). -/
lemma coordinateClamp_fixes {d : ℕ} (a b : ℝ) (x : L1Vec d)
    (hx : ∀ j, x.ofLp j ∈ Set.Icc a b) : coordinateClamp a b x = x := by
  apply PiLp.ext
  intro j
  change max a (min (x.ofLp j) b) = x.ofLp j
  rw [min_eq_left (hx j).2, max_eq_right (hx j).1]

-- @node: coordinateClamp_coordinate_dist
/-- [Applying the same upper cap and lower floor to two real numbers cannot increase
their absolute difference](goal). -/
lemma coordinateClamp_coordinate_dist (a b x y : ℝ) :
    |max a (min x b) - max a (min y b)| ≤ |x-y| := by
  have h : LipschitzWith 1 (fun x : ℝ => max a (min x b)) :=
    (LipschitzWith.id.min_const b).const_max a
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using h.dist_le_mul x y

-- @node: coordinateClamp_lipschitz
/-- [Coordinatewise clamping is Lipschitz with constant one under the sum-of-absolute-values
norm, for any lower and upper bounds](goal). -/
lemma coordinateClamp_lipschitz {d : ℕ} (a b : ℝ) :
    LipschitzWith 1 (coordinateClamp (d := d) a b) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, PiLp.dist_eq_of_L1, Real.dist_eq]
  exact Finset.sum_le_sum (fun j _ => coordinateClamp_coordinate_dist a b (x.ofLp j) (y.ofLp j))

-- @node: coordinateClamp_coordinate_error
/-- If [every coordinate of the target vector lies between the clipping bounds](hyp:hy),
[clamping an approximating vector cannot increase its absolute error at any chosen
coordinate](goal). -/
lemma coordinateClamp_coordinate_error {d : ℕ} (a b : ℝ) (x y : L1Vec d)
    (hy : ∀ j, y.ofLp j ∈ Set.Icc a b) (j : Fin d) :
    |(coordinateClamp a b x).ofLp j - y.ofLp j| ≤ |x.ofLp j-y.ofLp j| := by
  have h := coordinateClamp_coordinate_dist a b (x.ofLp j) (y.ofLp j)
  simpa only [coordinateClamp, WithLp.ofLp_toLp, min_eq_left (hy j).2,
    max_eq_right (hy j).1] using h

-- @node: coordinateClamp_norm_error
/-- If [every coordinate of the target vector lies between the clipping bounds](hyp:hy),
[clamping an approximating vector cannot increase its error in the sum-of-absolute-values
norm](goal). -/
lemma coordinateClamp_norm_error {d : ℕ} (a b : ℝ) (x y : L1Vec d)
    (hy : ∀ j, y.ofLp j ∈ Set.Icc a b) :
    ‖coordinateClamp a b x-y‖ ≤ ‖x-y‖ := by
  simpa only [NNReal.coe_one, one_mul, dist_eq_norm, coordinateClamp_fixes a b y hy] using
    (coordinateClamp_lipschitz (d := d) a b).dist_le_mul x y

-- @node: relu_truncK
/-- For [a nonnegative truncation radius](hyp:hK), [any ReLU network can be truncated
coordinatewise to the symmetric box of that radius using two additional hidden layers,
with width bounded by the larger of the original width bound and the output dimension;
the resulting network takes all inputs into that box](goal). -/
lemma relu_truncK {k d W L : ℕ} (q : ReLUNet k d W L) (K : ℝ) (hK : 0 ≤ K) :
    ∃ Q : ReLUNet k d (max W d) (L+2), Q.eval = truncK K ∘ q.eval ∧
      ∀ x, Q.eval x ∈ boundedCube d K := by
  obtain ⟨Q, hQ⟩ := relu_coordinateClamp q (-K) K (by linarith)
  refine ⟨Q, hQ, ?_⟩
  intro x j
  rw [hQ]
  exact abs_le.mpr (coordinateClamp_mapsTo (-K) K (by linarith) (q.eval x) j)

-- @node: relu_unitCube_clipping
/-- [Any ReLU network can be clipped coordinatewise to the unit interval using two
additional hidden layers, with width bounded by the larger of the original width bound
and the output dimension; the resulting network takes all inputs into the unit cube](goal). -/
lemma relu_unitCube_clipping {k d W L : ℕ} (q : ReLUNet k d W L) :
    ∃ Q : ReLUNet k d (max W d) (L+2),
      Q.eval = coordinateClamp 0 1 ∘ q.eval ∧ ∀ x, Q.eval x ∈ unitCube d := by
  obtain ⟨Q, hQ⟩ := relu_coordinateClamp q 0 1 zero_le_one
  refine ⟨Q, hQ, ?_⟩
  intro x j
  rw [hQ]
  exact coordinateClamp_mapsTo 0 1 zero_le_one (q.eval x) j

-- @node: yarotsky_vector_chart_approx_bounded
/-- Assume [the scalar Yarotsky approximation property](hyp:hgate), [a positive chart
dimension d](hyp:hd), a chart homeomorphism with [Lipschitz constant L](hyp:L)
that [satisfies this Lipschitz bound](hyp:hLip), [a nonnegative box radius K](hyp:hK),
and [a chart image contained in the symmetric box of radius K](hyp:hbox).
[There are a positive integer c and a positive constant A such that every integer
depth at least one admits a ReLU approximant with depth plus two hidden layers and
width bounded by max(Dcd, D), taking all inputs into that box, with uniform coordinate
error at most A times depth to the power −2/d and uniform sum-of-absolute-values error
at most D times that bound](goal). -/
lemma yarotsky_vector_chart_approx_bounded
    (hgate : YarotskyCoordinateApprox) {D d : ℕ} (hd : 0 < d)
    {C : Set (L1Vec D)} (f : homeoClass (unitCube d) C)
    (L : ℝ≥0) (hLip : LipschitzWith L f) (K : ℝ) (hK : 0 ≤ K)
    (hbox : C ⊆ boundedCube D K) :
    ∃ c : ℕ, 0 < c ∧ ∃ A : ℝ, 0 < A ∧
      ∀ depth : ℕ, 1 ≤ depth →
        ∃ q : ReLUNet d D (max (D * (c*d)) D) (depth+2),
          (∀ x, q.eval x ∈ boundedCube D K) ∧
          (∀ x : unitCube d, ∀ j : Fin D,
            |(f x).val.ofLp j - (q.eval x.val).ofLp j| ≤
              A * (depth : ℝ) ^ (-(2 : ℝ) / d)) ∧
          ∀ x : unitCube d, ‖(f x).val-q.eval x.val‖ ≤
            (D : ℝ) * A * (depth : ℝ) ^ (-(2 : ℝ) / d) := by
  obtain ⟨c, hc, A, hA, happrox⟩ := yarotsky_vector_chart_approx hgate hd f L hLip
  refine ⟨c, hc, A, hA, ?_⟩
  intro depth hdepth
  obtain ⟨q, hcoord, hnorm⟩ := happrox depth hdepth
  obtain ⟨Q, hQ, hbounded⟩ := relu_truncK q K hK
  have htarget (x : unitCube d) : ∀ j, (f x).val.ofLp j ∈ Set.Icc (-K) K :=
    fun j => abs_le.mp (hbox (f x).property j)
  refine ⟨Q, hbounded, ?_, ?_⟩
  · intro x j
    rw [hQ, Function.comp_apply, abs_sub_comm]
    exact (coordinateClamp_coordinate_error (-K) K (q.eval x.val) (f x).val
      (htarget x) j).trans (by simpa only [abs_sub_comm] using hcoord x j)
  · intro x
    rw [hQ, Function.comp_apply, norm_sub_rev]
    exact (coordinateClamp_norm_error (-K) K (q.eval x.val) (f x).val
      (htarget x)).trans (by simpa only [norm_sub_rev] using hnorm x)


/-- Assume [the scalar Yarotsky approximation property](hyp:hgate), [a positive chart
dimension d](hyp:hd), a chart homeomorphism with [Lipschitz constant L](hyp:L)
that [satisfies this Lipschitz bound](hyp:hLip), [a nonnegative box radius K](hyp:hK),
and [a chart image contained in the symmetric box of radius K](hyp:hbox).
[There is a positive constant A such that every integer depth at least one admits a
ReLU approximant with depth plus two hidden layers and width bounded by the larger
of D times the fixed first-layer width factor times d and D, taking all inputs into
that box, with uniform coordinate error at most A times depth to the power −2/d and
uniform sum-of-absolute-values error at most D times that bound](goal). -/
lemma yarotsky_vector_chart_approx_bounded_explicit
    (hgate : YarotskyCoordinateApprox) {D d : ℕ} (hd : 0 < d)
    {C : Set (L1Vec D)} (f : homeoClass (unitCube d) C)
    (L : ℝ≥0) (hLip : LipschitzWith L f) (K : ℝ) (hK : 0 ≤ K)
    (hbox : C ⊆ boundedCube D K) :
    ∃ A : ℝ, 0 < A ∧
      ∀ depth : ℕ, 1 ≤ depth →
        ∃ q : ReLUNet d D (max (D * (deepFirstWidthFactor*d)) D) (depth+2),
          (∀ x, q.eval x ∈ boundedCube D K) ∧
          (∀ x : unitCube d, ∀ j : Fin D,
            |(f x).val.ofLp j - (q.eval x.val).ofLp j| ≤
              A * (depth : ℝ) ^ (-(2 : ℝ) / d)) ∧
          ∀ x : unitCube d, ‖(f x).val-q.eval x.val‖ ≤
            (D : ℝ) * A * (depth : ℝ) ^ (-(2 : ℝ) / d) := by
  obtain ⟨A, hA, happrox⟩ := yarotsky_vector_chart_approx_explicit hgate hd f L hLip
  refine ⟨A, hA, ?_⟩
  intro depth hdepth
  obtain ⟨q, hcoord, hnorm⟩ := happrox depth hdepth
  obtain ⟨Q, hQ, hbounded⟩ := relu_truncK q K hK
  have htarget (x : unitCube d) : ∀ j, (f x).val.ofLp j ∈ Set.Icc (-K) K :=
    fun j => abs_le.mp (hbox (f x).property j)
  refine ⟨Q, hbounded, ?_, ?_⟩
  · intro x j
    rw [hQ, Function.comp_apply, abs_sub_comm]
    exact (coordinateClamp_coordinate_error (-K) K (q.eval x.val) (f x).val
      (htarget x) j).trans (by simpa only [abs_sub_comm] using hcoord x j)
  · intro x
    rw [hQ, Function.comp_apply, norm_sub_rev]
    exact (coordinateClamp_norm_error (-K) K (q.eval x.val) (f x).val
      (htarget x)).trans (by simpa only [norm_sub_rev] using hnorm x)

end
end Papers.TbsNeuralCausalPi
