module

public import Papers.OaiSmoothNonquadraticAffine.Helpers.ReductionFrame

/-! # The Hessian quadratic form of the square-root graph -/

@[expose] public section

noncomputable section

open Set Filter Matrix
open scoped Topology ContDiff BigOperators

namespace OaiSmoothNonquadraticAffine

-- @node: xProjection
/-- For [a spatial dimension m](hyp:m), the [spatial projection](goal) is the
continuous linear map that retains the first m coordinates and drops the last coordinate. -/
def xProjection (m : ℕ) :
    EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => EuclideanSpace.proj i.castSucc)

-- @node: xProjection_apply
/-- [Applying the spatial projection to z gives its spatial coordinates](goal). -/
lemma xProjection_apply {m : ℕ} (z : EuclideanSpace ℝ (Fin (m + 1))) :
    xProjection m z = xPart z := rfl

-- @node: tProjection_apply
/-- [Projecting z onto its last coordinate gives its time coordinate](goal). -/
lemma tProjection_apply {m : ℕ} (z : EuclideanSpace ℝ (Fin (m + 1))) :
    EuclideanSpace.proj (Fin.last m) z = tPart z := rfl

-- @node: secondDifferential
/-- For [a real-valued function f](hyp:f), [an evaluation point z](hyp:z), and
[directions v](hyp:v) and [w](hyp:w), the [bilinear second differential](goal)
is the derivative in direction v of the derivative of f, evaluated in direction w. -/
def secondDifferential {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (z v w : E) : ℝ :=
  fderiv ℝ (fderiv ℝ f) z v w

-- @node: secondDifferential_eq
/-- If [f is twice continuously differentiable at z](hyp:hf), then
[its second differential in directions v and w equals the derivative in direction v
of its directional derivative in direction w](goal). -/
lemma secondDifferential_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) (v w : E) :
    secondDifferential f z v w = fderiv ℝ (fun y => fderiv ℝ f y w) z v := by
  rw [fderiv_clm_apply (hf.fderiv_right (by norm_num)).differentiableAt_one
    (differentiableAt_const w)]
  simp [secondDifferential]

-- @node: secondDifferential_mul
/-- If [f is twice continuously differentiable at z](hyp:hf) and
[g is twice continuously differentiable at z](hyp:hg), then
[the second differential of their product in directions v and w is f times the
second differential of g, plus g times that of f, plus the two products of first
directional derivatives obtained by assigning v and w to different factors](goal),
with all values and derivatives evaluated at z. -/
lemma secondDifferential_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z)
    (v w : E) :
    secondDifferential (fun y => f y * g y) z v w =
      f z * secondDifferential g z v w + g z * secondDifferential f z v w +
        fderiv ℝ f z v * fderiv ℝ g z w + fderiv ℝ g z v * fderiv ℝ f z w := by
  have heq : (fun y => fderiv ℝ (fun a => f a * g a) y w) =ᶠ[𝓝 z]
      (fun y => f y * fderiv ℝ g y w + g y * fderiv ℝ f y w) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hy hy'
    rw [fderiv_fun_mul (hy.differentiableAt (by norm_num)) (hy'.differentiableAt (by norm_num))]
    simp
  rw [secondDifferential_eq (hf.mul hg), heq.fderiv_eq]
  have hdf := (hf.fderiv_right (by norm_num)).differentiableAt_one
  have hdg := (hg.fderiv_right (by norm_num)).differentiableAt_one
  have hfw := hdf.clm_apply (differentiableAt_const w)
  have hgw := hdg.clm_apply (differentiableAt_const w)
  rw [fderiv_fun_add (f := fun y => f y * fderiv ℝ g y w)
    (g := fun y => g y * fderiv ℝ f y w) ((hf.differentiableAt (by norm_num)).mul hgw)
    ((hg.differentiableAt (by norm_num)).mul hfw),
    fderiv_fun_mul (hf.differentiableAt (by norm_num)) hgw,
    fderiv_fun_mul (hg.differentiableAt (by norm_num)) hfw]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul,
    ← secondDifferential_eq hf, ← secondDifferential_eq hg]
  ring

-- @node: secondDifferential_add
/-- If [f is twice continuously differentiable at z](hyp:hf) and
[g is twice continuously differentiable at z](hyp:hg), then
[the second differential of their sum in directions v and w is the sum of their
second differentials in those directions](goal). -/
lemma secondDifferential_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z)
    (v w : E) :
    secondDifferential (fun y => f y + g y) z v w =
      secondDifferential f z v w + secondDifferential g z v w := by
  have heq : (fun y => fderiv ℝ (fun a => f a + g a) y w) =ᶠ[𝓝 z]
      (fun y => fderiv ℝ f y w + fderiv ℝ g y w) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hy hy'
    rw [fderiv_fun_add (hy.differentiableAt (by norm_num)) (hy'.differentiableAt (by norm_num))]
    rfl
  rw [secondDifferential_eq (hf.add hg), heq.fderiv_eq,
    fderiv_fun_add
      ((hf.fderiv_right (by norm_num)).differentiableAt_one.clm_apply (differentiableAt_const w))
      ((hg.fderiv_right (by norm_num)).differentiableAt_one.clm_apply (differentiableAt_const w))]
  simp [← secondDifferential_eq hf, ← secondDifferential_eq hg]

-- @node: sqrtPair_contDiffAt
/-- If [f is twice continuously differentiable at z](hyp:hf),
[g is twice continuously differentiable at z](hyp:hg), and
[the sum of their squared values at z is positive](hyp:hpos), then
[the square root of the sum of their squares is twice continuously differentiable at z](goal). -/
@[fun_prop] lemma sqrtPair_contDiffAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z)
    (hpos : 0 < f z ^ 2 + g z ^ 2) :
    ContDiffAt ℝ 2 (fun y => Real.sqrt (f y ^ 2 + g y ^ 2)) z := by
  fun_prop (disch := positivity)

-- @node: sqrtPair_secondDifferential
/-- Suppose [f is twice continuously differentiable at z](hyp:hf),
[g is twice continuously differentiable at z](hyp:hg), and
[their squared values at z have positive sum](hyp:hpos); write u for the square root
of that sum as a function of the evaluation point. Then [the second differential
of u in directions v and w equals f/u times the second differential of f, plus
g/u times the second differential of g, plus the product of the two directional
expressions g times the derivative of f minus f times the derivative of g,
divided by u cubed](goal), all evaluated at z. -/
lemma sqrtPair_secondDifferential {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z)
    (hpos : 0 < f z ^ 2 + g z ^ 2) (v w : E) :
    let u := fun y => Real.sqrt (f y ^ 2 + g y ^ 2)
    secondDifferential u z v w =
      f z / u z * secondDifferential f z v w +
      g z / u z * secondDifferential g z v w +
      (g z * fderiv ℝ f z v - f z * fderiv ℝ g z v) *
        (g z * fderiv ℝ f z w - f z * fderiv ℝ g z w) / u z ^ 3 := by
  let u := fun y => Real.sqrt (f y ^ 2 + g y ^ 2)
  have hu : ContDiffAt ℝ 2 u z := sqrtPair_contDiffAt hf hg hpos
  have hu0 : u z ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  have husq : u z ^ 2 = f z ^ 2 + g z ^ 2 := Real.sq_sqrt hpos.le
  have hd := (((hf.differentiableAt (by norm_num)).hasFDerivAt.pow 2).add
    ((hg.differentiableAt (by norm_num)).hasFDerivAt.pow 2)).sqrt (ne_of_gt hpos)
  have hdval (a : E) : fderiv ℝ u z a =
      (f z * fderiv ℝ f z a + g z * fderiv ℝ g z a) / u z := by
    rw [show fderiv ℝ u z = _ from hd.fderiv]
    simp only [_root_.smul_apply, _root_.add_apply, smul_eq_mul]
    dsimp [u]
    ring
  have heq : (fun y => u y * u y) =
      (fun y => f y * f y + g y * g y) := by
    funext y
    simpa [u, ← pow_two] using Real.sq_sqrt (show 0 ≤ f y ^ 2 + g y ^ 2 by positivity)
  have hsecond := congrArg (fun a => secondDifferential a z v w) heq
  rw [secondDifferential_mul hu hu,
    secondDifferential_add (hf.mul hf) (hg.mul hg),
    secondDifferential_mul hf hf, secondDifferential_mul hg hg,
    hdval v, hdval w] at hsecond
  change secondDifferential u z v w =
    f z / u z * secondDifferential f z v w +
    g z / u z * secondDifferential g z v w +
    (g z * fderiv ℝ f z v - f z * fderiv ℝ g z v) *
      (g z * fderiv ℝ f z w - f z * fderiv ℝ g z w) / u z ^ 3
  field_simp [hu0] at hsecond ⊢
  linear_combination hsecond / 2 +
    (fderiv ℝ f z v * fderiv ℝ f z w + fderiv ℝ g z v * fderiv ℝ g z w) * husq

-- @node: secondDifferential_comp_clm
/-- If [f is twice continuously differentiable at the image of z under the
continuous linear map L](hyp:hf), then [the second differential of f composed with L
at z in directions v and w equals the second differential of f at that image,
in directions L applied to v and L applied to w](goal). -/
lemma secondDifferential_comp_clm {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : E →L[ℝ] V) {f : V → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f (L z)) (v w : E) :
    secondDifferential (fun y => f (L y)) z v w =
      secondDifferential f (L z) (L v) (L w) := by
  have hcomp : ContDiffAt ℝ 2 (fun y => f (L y)) z := hf.comp z L.contDiff.contDiffAt
  have heq : (fun y => fderiv ℝ (fun a => f (L a)) y w) =ᶠ[𝓝 z]
      (fun y => fderiv ℝ f (L y) (L w)) := by
    have he := L.continuous.continuousAt.eventually (hf.eventually (by norm_num))
    filter_upwards [he] with y hy
    change (fderiv ℝ (f ∘ L) y) w = _
    rw [fderiv_comp y (hy.differentiableAt (by norm_num)) L.differentiableAt, L.fderiv]
    rfl
  have hdf := (hf.fderiv_right (by norm_num)).differentiableAt_one.clm_apply
    (differentiableAt_const (L w))
  rw [secondDifferential_eq hcomp, heq.fderiv_eq]
  change (fderiv ℝ ((fun y => fderiv ℝ f y (L w)) ∘ L) z) v = _
  rw [fderiv_comp z hdf L.differentiableAt, L.fderiv, secondDifferential_eq hf]
  rfl

-- @node: secondDifferential_clm
/-- [The second differential of a continuous linear real-valued map L is zero
at every point z and in any directions v and w](goal). -/
lemma secondDifferential_clm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) (z v w : E) : secondDifferential L z v w = 0 := by
  have heq : fderiv ℝ L = fun _ => L := funext fun y => L.fderiv
  simp [secondDifferential, heq]

-- @node: xPart_contDiff
/-- [Taking the spatial coordinates in dimension m + 1 is infinitely
continuously differentiable](goal). -/
@[fun_prop] lemma xPart_contDiff (m : ℕ) :
    ContDiff ℝ ∞ (@xPart m) := (xProjection m).contDiff

-- @node: tPart_contDiff
/-- [Taking the time coordinate in dimension m + 1 is infinitely
continuously differentiable](goal). -/
@[fun_prop] lemma tPart_contDiff (m : ℕ) :
    ContDiff ℝ ∞ (@tPart m) := by
  change ContDiff ℝ ∞ (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last m))
  exact ContinuousLinearMap.contDiff _

-- @node: reductionGraph_contDiffAt
/-- If [Ω is open and F and P are smooth and positive on Ω](hyp:hFP), and
[the spatial part of z belongs to Ω](hyp:hz), then [the graph function given by
the square root of F squared plus the time coordinate squared is infinitely
continuously differentiable at z](goal). -/
@[fun_prop] lemma reductionGraph_contDiffAt {m : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin m))} {F P : EuclideanSpace ℝ (Fin m) → ℝ}
    (hFP : ReductionFunctions Ω F P) {z : EuclideanSpace ℝ (Fin (m + 1))}
    (hz : xPart z ∈ Ω) : ContDiffAt ℝ ∞ (reductionGraph F) z := by
  have hf := hFP.2.1.contDiffAt (hFP.1.mem_nhds hz)
  have hF := (hFP.2.2.2 _ hz).1
  unfold reductionGraph
  fun_prop (disch := positivity)

-- @node: reductionGraph_secondDifferential
/-- Suppose [Ω is open and F and P are smooth and positive on Ω](hyp:hFP) and
[the spatial part of z belongs to Ω](hyp:hz). Writing x and t for the spatial and
time parts of z and u for the square root of F(x) squared plus t squared,
[the graph's second differential in directions v and w equals F(x)/u times the
second differential of F on their spatial parts, plus F(x) squared divided by u cubed
times the product of their adjusted time components, where each adjusted component
is its time component minus t/F(x) times the directional derivative of F on its
spatial component](goal). -/
lemma reductionGraph_secondDifferential {m : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin m))} {F P : EuclideanSpace ℝ (Fin m) → ℝ}
    (hFP : ReductionFunctions Ω F P) {z : EuclideanSpace ℝ (Fin (m + 1))}
    (hz : xPart z ∈ Ω) (v w : EuclideanSpace ℝ (Fin (m + 1))) :
    secondDifferential (reductionGraph F) z v w =
      F (xPart z) / reductionGraph F z * secondDifferential F (xPart z) (xPart v) (xPart w) +
      F (xPart z) ^ 2 / reductionGraph F z ^ 3 *
        (tPart v - tPart z / F (xPart z) * fderiv ℝ F (xPart z) (xPart v)) *
        (tPart w - tPart z / F (xPart z) * fderiv ℝ F (xPart z) (xPart w)) := by
  have hf : ContDiffAt ℝ 2 F (xPart z) :=
    (hFP.2.1.contDiffAt (hFP.1.mem_nhds hz)).of_le (by decide)
  have hF := (hFP.2.2.2 _ hz).1
  let L := xProjection m
  let T := EuclideanSpace.proj (Fin.last m) (𝕜 := ℝ)
  have hfc : ContDiffAt ℝ 2 (fun y => F (L y)) z := hf.comp z L.contDiff.contDiffAt
  have hpos : 0 < F (L z) ^ 2 + T z ^ 2 := by
    change 0 < F (xPart z) ^ 2 + tPart z ^ 2
    positivity
  have h := sqrtPair_secondDifferential hfc T.contDiff.contDiffAt hpos v w
  have hd : fderiv ℝ (fun y => F (L y)) z = (fderiv ℝ F (L z)).comp L :=
    (hf.differentiableAt (by norm_num)).hasFDerivAt.comp z L.hasFDerivAt |>.fderiv
  rw [secondDifferential_comp_clm L hf, secondDifferential_clm, hd, T.fderiv] at h
  change secondDifferential (reductionGraph F) z v w = _ at h
  rw [h]
  simp only [mul_zero, add_zero, ContinuousLinearMap.comp_apply]
  change F (xPart z) / reductionGraph F z *
      secondDifferential F (xPart z) (xPart v) (xPart w) +
    (tPart z * fderiv ℝ F (xPart z) (xPart v) - F (xPart z) * tPart v) *
      (tPart z * fderiv ℝ F (xPart z) (xPart w) - F (xPart z) * tPart w) /
        reductionGraph F z ^ 3 = _
  have hu : reductionGraph F z ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  field_simp
  ring

-- @node: hessianMatrix_eq_secondDifferential
/-- If [f is twice continuously differentiable at z](hyp:hf), then
[entry i,j of its Hessian at z equals its second differential on the i-th and
j-th coordinate unit vectors](goal). -/
lemma hessianMatrix_eq_secondDifferential {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {z : EuclideanSpace ℝ (Fin n)}
    (hf : ContDiffAt ℝ 2 f z) (i j : Fin n) :
    hessianMatrix f z i j =
      secondDifferential f z (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  exact (secondDifferential_eq hf _ _).symm

-- @node: euclidean_sum_single
/-- [Every vector v is the sum of its coordinates multiplied by the corresponding
coordinate unit vectors](goal). -/
lemma euclidean_sum_single {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) :
    ∑ i, v i • EuclideanSpace.single i 1 = v := by
  ext j
  simp [Pi.single_apply]

-- @node: secondDifferential_eq_dotProduct
/-- If [f is twice continuously differentiable at z](hyp:hf), then
[its second differential in directions v and w is the dot product of v with
the Hessian of f at z multiplied by w](goal). -/
lemma secondDifferential_eq_dotProduct {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {z : EuclideanSpace ℝ (Fin n)}
    (hf : ContDiffAt ℝ 2 f z) (v w : EuclideanSpace ℝ (Fin n)) :
    secondDifferential f z v w = (fun i => v i) ⬝ᵥ (hessianMatrix f z *ᵥ (fun i => w i)) := by
  simp only [dotProduct, Matrix.mulVec, hessianMatrix_eq_secondDifferential hf]
  conv_lhs => rw [← euclidean_sum_single v, ← euclidean_sum_single w]
  simp only [secondDifferential, map_sum, map_smul, _root_.sum_apply,
    _root_.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

-- @node: hessianMatrix_isHermitian
/-- If [f is twice continuously differentiable at z](hyp:hf), then
[its real Hessian matrix at z is symmetric](goal). -/
lemma hessianMatrix_isHermitian {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {z : EuclideanSpace ℝ (Fin n)}
    (hf : ContDiffAt ℝ 2 f z) : (hessianMatrix f z).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial,
    hessianMatrix_eq_secondDifferential hf, secondDifferential]
  exact hf.isSymmSndFDerivAt (by norm_num) _ _

-- @node: secondDifferential_pos
/-- If [f is twice continuously differentiable at z](hyp:hf),
[its Hessian at z is positive definite](hyp:hH), and [v is nonzero](hyp:hv), then
[the second differential of f at z applied twice to v is strictly positive](goal). -/
lemma secondDifferential_pos {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {z : EuclideanSpace ℝ (Fin n)}
    (hf : ContDiffAt ℝ 2 f z) (hH : (hessianMatrix f z).PosDef)
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ≠ 0) :
    0 < secondDifferential f z v v := by
  rw [secondDifferential_eq_dotProduct hf]
  have hv' : (fun i => v i) ≠ 0 := by
    intro h
    apply hv
    ext i
    exact congrFun h i
  simpa only [star_trivial] using hH.dotProduct_mulVec_pos hv'

-- @node: xPart_tPart_eq_zero
/-- If [the spatial part of v is zero](hyp:hx) and [its time coordinate is
zero](hyp:ht), then [v is the zero vector](goal). -/
lemma xPart_tPart_eq_zero {m : ℕ} {v : EuclideanSpace ℝ (Fin (m + 1))}
    (hx : xPart v = 0) (ht : tPart v = 0) : v = 0 := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact ht
  · exact congrArg (fun a : EuclideanSpace ℝ (Fin m) => a j) hx

-- @node: reductionGraph_hessianPositive
/-- If [Ω is open and F and P are smooth and positive on Ω](hyp:hFP) and
[the Hessian of F is positive definite throughout Ω](hyp:hH), then
[the graph function given by the square root of F squared plus the time coordinate
squared has a positive definite Hessian at every point whose spatial part lies in Ω](goal). -/
lemma reductionGraph_hessianPositive {m : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin m))} {F P : EuclideanSpace ℝ (Fin m) → ℝ}
    (hFP : ReductionFunctions Ω F P) (hH : ReductionHessianPosDef Ω F) :
    HessianPositive (reductionGraph F) {z | xPart z ∈ Ω} := by
  intro z hz
  have hf : ContDiffAt ℝ 2 F (xPart z) :=
    (hFP.2.1.contDiffAt (hFP.1.mem_nhds hz)).of_le (by decide)
  have hu : ContDiffAt ℝ 2 (reductionGraph F) z :=
    (reductionGraph_contDiffAt hFP hz).of_le (by decide)
  have hF := (hFP.2.2.2 _ hz).1
  have hup : 0 < reductionGraph F z := by
    unfold reductionGraph
    positivity
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (hessianMatrix_isHermitian hu) ?_
  intro a ha
  let v : EuclideanSpace ℝ (Fin (m + 1)) := WithLp.toLp 2 a
  have hv : v ≠ 0 := by
    intro h
    apply ha
    exact congrArg WithLp.ofLp h
  suffices 0 < secondDifferential (reductionGraph F) z v v by
    simpa only [secondDifferential_eq_dotProduct hu, star_trivial] using this
  rw [reductionGraph_secondDifferential hFP hz]
  by_cases hx : xPart v = 0
  · have ht : tPart v ≠ 0 := fun ht => hv (xPart_tPart_eq_zero hx ht)
    simp only [hx, secondDifferential, map_zero, mul_zero, sub_zero, zero_add]
    have hc : 0 < F (xPart z) ^ 2 / reductionGraph F z ^ 3 := by positivity
    nlinarith [sq_pos_of_ne_zero ht]
  · have hsp := secondDifferential_pos hf (hH _ hz) hx
    have hfirst : 0 < F (xPart z) / reductionGraph F z *
        secondDifferential F (xPart z) (xPart v) (xPart v) := mul_pos (div_pos hF hup) hsp
    have hlast : 0 ≤ F (xPart z) ^ 2 / reductionGraph F z ^ 3 *
        (tPart v - tPart z / F (xPart z) * fderiv ℝ F (xPart z) (xPart v)) ^ 2 := by
      positivity
    nlinarith

-- @node: xPart_spatialBasis
/-- [The spatial part of the i-th spatial basis vector is the i-th coordinate
unit vector in the spatial space](goal). -/
lemma xPart_spatialBasis {m : ℕ} (i : Fin m) :
    xPart (spatialBasis m i) = EuclideanSpace.single i 1 := by
  ext j
  simp [xPart, spatialBasis]

-- @node: xPart_timeBasis
/-- [The spatial part of the time basis vector is zero](goal). -/
lemma xPart_timeBasis (m : ℕ) : xPart (timeBasis m) = 0 := by
  ext j
  simp [xPart, timeBasis]

-- @node: tPart_spatialBasis
/-- [The time coordinate of each spatial basis vector is zero](goal). -/
lemma tPart_spatialBasis {m : ℕ} (i : Fin m) : tPart (spatialBasis m i) = 0 := by
  simp [tPart, spatialBasis]

-- @node: tPart_timeBasis
/-- [The time coordinate of the time basis vector is one](goal). -/
lemma tPart_timeBasis (m : ℕ) : tPart (timeBasis m) = 1 := by
  simp [tPart, timeBasis]

-- @node: xPart_adaptedSpatialBasis
/-- If [F is positive at the spatial part of z](hyp:hF), then
[the spatial part of the i-th adapted spatial basis vector is the i-th spatial
coordinate unit vector](goal). -/
lemma xPart_adaptedSpatialBasis {m : ℕ} (F : EuclideanSpace ℝ (Fin m) → ℝ)
    (z : EuclideanSpace ℝ (Fin (m + 1))) (hF : 0 < F (xPart z)) (i : Fin m) :
    xPart (adaptedSpatialBasis F z hF i) = EuclideanSpace.single i 1 := by
  change xProjection m (_ + _ • _) = _
  rw [map_add, map_smul]
  change xPart (spatialBasis m i) + _ • xPart (timeBasis m) = _
  rw [xPart_spatialBasis, xPart_timeBasis, smul_zero, add_zero]

-- @node: tPart_adaptedSpatialBasis
/-- If [F is positive at the spatial part of z](hyp:hF), then
[the time coordinate of the i-th adapted spatial basis vector equals the time
coordinate of z divided by F at its spatial part, multiplied by the derivative
of F in the i-th spatial coordinate direction there](goal). -/
lemma tPart_adaptedSpatialBasis {m : ℕ} (F : EuclideanSpace ℝ (Fin m) → ℝ)
    (z : EuclideanSpace ℝ (Fin (m + 1))) (hF : 0 < F (xPart z)) (i : Fin m) :
    tPart (adaptedSpatialBasis F z hF i) =
      tPart z / F (xPart z) * fderiv ℝ F (xPart z) (EuclideanSpace.single i 1) := by
  change EuclideanSpace.proj (𝕜 := ℝ) (Fin.last m) (_ + (_ : ℝ) • _) = _
  rw [map_add, map_smul]
  change tPart (spatialBasis m i) + _ * tPart (timeBasis m) = _
  rw [tPart_spatialBasis, tPart_timeBasis, mul_one, zero_add]
  rfl

-- @node: reductionGraph_adapted_spatial
/-- If [Ω is open and F and P are smooth and positive on Ω](hyp:hFP),
[the spatial part of z belongs to Ω](hyp:hz), and [F is positive there](hyp:hF), then
[the second differential of the square-root graph on adapted spatial basis vectors
i and j equals entry i,j of the spatial Hessian of F, multiplied by F divided by
the graph value at z](goal). -/
lemma reductionGraph_adapted_spatial {m : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin m))} {F P : EuclideanSpace ℝ (Fin m) → ℝ}
    (hFP : ReductionFunctions Ω F P) {z : EuclideanSpace ℝ (Fin (m + 1))}
    (hz : xPart z ∈ Ω) (hF : 0 < F (xPart z)) (i j : Fin m) :
    secondDifferential (reductionGraph F) z
      (adaptedSpatialBasis F z hF i) (adaptedSpatialBasis F z hF j) =
      F (xPart z) / reductionGraph F z * hessianMatrix F (xPart z) i j := by
  rw [reductionGraph_secondDifferential hFP hz]
  simp only [xPart_adaptedSpatialBasis, tPart_adaptedSpatialBasis, sub_self,
    mul_zero, add_zero]
  rw [hessianMatrix_eq_secondDifferential
    ((hFP.2.1.contDiffAt (hFP.1.mem_nhds hz)).of_le (by decide))]

-- @node: reductionGraph_adapted_mixed
/-- If [Ω is open and F and P are smooth and positive on Ω](hyp:hFP),
[the spatial part of z belongs to Ω](hyp:hz), and [F is positive there](hyp:hF), then
[the second differential of the square-root graph at z on the i-th adapted spatial
basis vector and the time basis vector is zero](goal). -/
lemma reductionGraph_adapted_mixed {m : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin m))} {F P : EuclideanSpace ℝ (Fin m) → ℝ}
    (hFP : ReductionFunctions Ω F P) {z : EuclideanSpace ℝ (Fin (m + 1))}
    (hz : xPart z ∈ Ω) (hF : 0 < F (xPart z)) (i : Fin m) :
    secondDifferential (reductionGraph F) z (adaptedSpatialBasis F z hF i) (timeBasis m) =
      0 := by
  rw [reductionGraph_secondDifferential hFP hz]
  simp [xPart_adaptedSpatialBasis, tPart_adaptedSpatialBasis, xPart_timeBasis,
    secondDifferential]

-- @node: reductionGraph_time_time
/-- If [Ω is open and F and P are smooth and positive on Ω](hyp:hFP) and
[the spatial part of z belongs to Ω](hyp:hz), then
[the second differential of the square-root graph at z on two copies of the time
basis vector equals F at the spatial part squared divided by the graph value cubed](goal). -/
lemma reductionGraph_time_time {m : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin m))} {F P : EuclideanSpace ℝ (Fin m) → ℝ}
    (hFP : ReductionFunctions Ω F P) {z : EuclideanSpace ℝ (Fin (m + 1))}
    (hz : xPart z ∈ Ω) :
    secondDifferential (reductionGraph F) z (timeBasis m) (timeBasis m) =
      F (xPart z) ^ 2 / reductionGraph F z ^ 3 := by
  rw [reductionGraph_secondDifferential hFP hz]
  simp [xPart_timeBasis, tPart_timeBasis, secondDifferential]

end OaiSmoothNonquadraticAffine
