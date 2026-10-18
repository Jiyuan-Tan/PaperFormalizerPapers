module
public import Papers.TbsNeuralCausalPi.Setup.CitedResults
public import Papers.TbsNeuralCausalPi.Helpers.ParallelNetworks
public import Papers.TbsNeuralCausalPi.Helpers.EuclideanModulus
public import Papers.TbsNeuralCausalPi.Helpers.ComponentLaws
public import Mathlib.Analysis.Convex.Hull
public import Causalean.Mathlib.Analysis.PiecewiseLipschitz
/-! # Paper-owned deep ReLU approximation constructions -/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
open scoped NNReal
attribute [local instance] Classical.propDecidable
/-- Assuming [the Yarotsky coordinate approximation result](hyp:hgate),
[the width multiplier can be chosen as 12, and every coordinate of a Lipschitz
chart from a positive-dimensional unit cube has scalar ReLU approximations of
width 12 times the input dimension and any positive depth, with uniform error
at most a positive chart-dependent constant times depth to the power minus two
divided by the input dimension](goal). -/
-- @node: yarotskyCoordinate_chart
lemma yarotskyCoordinate_chart (hgate : YarotskyCoordinateApprox) :
    ∃ c : ℕ, c = 12 ∧ 0 < c ∧
      ∀ (D d : ℕ) (_hd : 0 < d) (C : Set (L1Vec D))
        (f : homeoClass (unitCube d) C) (L : ℝ≥0), LipschitzWith L f →
        ∀ j : Fin D, ∃ A : ℝ, 0 < A ∧
          ∀ depth : ℕ, 1 ≤ depth → ∃ q : ReLUNet d 1 (c * d) depth,
            ∀ x : unitCube d,
              |(f x).val.ofLp j - (q.eval x.val).ofLp 0| ≤
                A * (depth : ℝ) ^ (-(2 : ℝ) / d) := by
  classical
  refine ⟨12, rfl, by norm_num, ?_⟩
  intro D d hd C f L hLip j
  let F : L1Vec d → ℝ := fun x => if hx : x ∈ unitCube d then
    (f ⟨x, hx⟩).val.ofLp j else 0
  have hF (x : unitCube d) : F x.val = (f x).val.ofLp j := by
    simp [F, x.property]
  have hFLip : LipschitzOnWith L F (unitCube d) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [hF ⟨x,hx⟩, hF ⟨y,hy⟩]
    exact (PiLp.dist_apply_le (f ⟨x,hx⟩).val (f ⟨y,hy⟩).val j).trans
      (hLip.dist_le_mul ⟨x,hx⟩ ⟨y,hy⟩)
  obtain ⟨a, c, ha, hc, happ⟩ := hgate d hd
  have hcompact : IsCompact C := by
    let : CompactSpace (unitCube d) := isCompact_iff_compactSpace.mp (unitCube_isCompact d)
    let : CompactSpace C := f.compactSpace
    exact isCompact_iff_compactSpace.mpr inferInstance
  refine ⟨a * L * d * c + 1, by positivity, ?_⟩
  intro depth hdepth
  obtain ⟨q, hq⟩ := happ D C hcompact f L hLip j depth hdepth
  let Q : ReLUNet d 1 (12*d) depth :=
    { q with widths := fun l hl => (q.widths l hl).trans (by omega) }
  refine ⟨Q, ?_⟩
  intro x
  have hmod := euclidModulus_le_of_lipschitzOn hFLip
    (r := c * (depth : ℝ) ^ (-(2 : ℝ) / d)) (by positivity)
  calc
    _ = |F x.val - (q.eval x.val).ofLp 0| := by rw [hF]
    _ ≤ a * euclidModulus F (c * (depth : ℝ) ^ (-(2 : ℝ) / d)) := hq x.val x.property
    _ ≤ a * (L * d * (c * (depth : ℝ) ^ (-(2 : ℝ) / d))) :=
      mul_le_mul_of_nonneg_left hmod ha.le
    _ ≤ (a * L * d * c + 1) * (depth : ℝ) ^ (-(2 : ℝ) / d) := by
      nlinarith [Real.rpow_nonneg (Nat.cast_nonneg depth) (-(2 : ℝ) / d)]

/-- For [a scalar function on the line](hyp:f), [a number of grid cells](hyp:N)
that [is positive](hyp:_hN), and [an evaluation point](hyp:x), the
[uniform-grid interpolant](goal) is computed by [clamping the point to the unit
interval](step:1), [selecting its grid cell, using the final cell at the right
endpoint](step:2), [computing its fractional position in that cell](step:3),
and [taking the corresponding weighted average of the two endpoint values](step:4). -/
noncomputable def holderGridInterpolant (f : L1Vec 1 → ℝ) (N : ℕ)
    (_hN : 0 < N) (x : L1Vec 1) : ℝ :=
  let t := max 0 (min (x.ofLp 0) 1)
  let i := min ⌊t * N⌋₊ (N-1)
  let w := t * N - i
  (1-w) * f (WithLp.toLp 1 (fun _ => (i : ℝ) / N)) +
    w * f (WithLp.toLp 1 (fun _ => ((i : ℝ)+1) / N))

/-- If [a real number is nonnegative](hyp:ht0) and [at most one](hyp:ht1),
and [the number of grid cells is positive](hyp:hN), then [its selected cell
index is no greater than the number times the grid size, that product is no
greater than the index plus one, and the index is less than the grid size](goal). -/
-- @node: holderGridIndex_bounds
lemma holderGridIndex_bounds (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (N : ℕ) (hN : 0 < N) :
    let i := min ⌊t * N⌋₊ (N-1)
    (i : ℝ) ≤ t*N ∧ t*N ≤ (i : ℝ)+1 ∧ i < N := by
  dsimp
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨le_trans (by exact_mod_cast min_le_left ⌊t*N⌋₊ (N-1))
    (Nat.floor_le (mul_nonneg ht0 hNreal.le)), ?_, by omega⟩
  by_cases hi : ⌊t*N⌋₊ ≤ N-1
  · rw [min_eq_left hi]
    exact (Nat.lt_floor_add_one (t*N)).le
  · rw [min_eq_right (by omega)]
    have hsub : ((N-1 : ℕ) : ℝ)+1 = N := by
      exact_mod_cast (Nat.sub_add_cancel hN)
    rw [hsub]
    nlinarith

/-- If [the Hölder exponent is positive](hyp:halpha), [the modulus constant
is nonnegative](hyp:hA), [function differences on the unit interval are bounded
by that constant times distance to that exponent](hyp:hf), and [the grid size
is positive](hyp:hN), then [the uniform interpolation error on the unit interval
is at most twice the modulus constant times the grid size to the negative
Hölder exponent](goal). -/
-- @node: holderGridInterpolant_error
lemma holderGridInterpolant_error {alpha A : ℝ} (halpha : 0 < alpha)
    (hA : 0 ≤ A) (f : L1Vec 1 → ℝ)
    (hf : ∀ x ∈ unitCube 1, ∀ y ∈ unitCube 1,
      |f x - f y| ≤ A * ‖x-y‖ ^ alpha)
    (N : ℕ) (hN : 0 < N) :
    ∀ x ∈ unitCube 1, |f x - holderGridInterpolant f N hN x| ≤
      2*A*(N : ℝ)^(-alpha) := by
  intro x hx
  have ht := hx 0
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  let i := min ⌊x.ofLp 0 * N⌋₊ (N-1)
  let w : ℝ := x.ofLp 0 * N - i
  obtain ⟨hlo, hhi, hi⟩ := holderGridIndex_bounds (x.ofLp 0) ht.1 ht.2 N hN
  change (i : ℝ) ≤ x.ofLp 0 * N at hlo
  change x.ofLp 0 * N ≤ (i : ℝ)+1 at hhi
  change i < N at hi
  have hw0 : 0 ≤ w := sub_nonneg.mpr hlo
  have hw1 : w ≤ 1 := by dsimp [w]; linarith
  let a : L1Vec 1 := WithLp.toLp 1 (fun _ => (i : ℝ)/N)
  let b : L1Vec 1 := WithLp.toLp 1 (fun _ => ((i : ℝ)+1)/N)
  have ha : a ∈ unitCube 1 := by
    intro j
    change (i : ℝ)/N ∈ Set.Icc 0 1
    refine ⟨by positivity, (div_le_one hNreal).mpr ?_⟩
    exact_mod_cast hi.le
  have hb : b ∈ unitCube 1 := by
    intro j
    change ((i : ℝ)+1)/N ∈ Set.Icc 0 1
    refine ⟨by positivity, (div_le_one hNreal).mpr ?_⟩
    exact_mod_cast hi
  have hd (z : L1Vec 1) : ‖x-z‖ = |x.ofLp 0-z.ofLp 0| := by
    simp [PiLp.norm_eq_of_L1, Real.norm_eq_abs]
  have hda : ‖x-a‖ ≤ (N : ℝ)⁻¹ := by
    rw [hd, abs_of_nonneg (sub_nonneg.mpr ((div_le_iff₀ hNreal).mpr hlo))]
    rw [← one_div]
    apply (le_div_iff₀ hNreal).mpr
    field_simp
    nlinarith
  have hdb : ‖x-b‖ ≤ (N : ℝ)⁻¹ := by
    rw [hd, abs_of_nonpos (sub_nonpos.mpr ((le_div_iff₀ hNreal).mpr hhi))]
    rw [← one_div]
    apply (le_div_iff₀ hNreal).mpr
    field_simp
    nlinarith
  have hp : ((N : ℝ)⁻¹)^alpha = (N : ℝ)^(-alpha) := by
    rw [Real.inv_rpow hNreal.le, Real.rpow_neg hNreal.le]
  have herr (z : L1Vec 1) (hz : z ∈ unitCube 1) (hdz : ‖x-z‖ ≤ (N : ℝ)⁻¹) :
      |f x-f z| ≤ A*(N : ℝ)^(-alpha) := by
    apply (hf x hx z hz).trans
    rw [← hp]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hdz halpha.le) hA
  have haerr := herr a ha hda
  have hberr := herr b hb hdb
  have hform : holderGridInterpolant f N hN x = (1-w)*f a + w*f b := by
    simp only [holderGridInterpolant, min_eq_left ht.2, max_eq_right ht.1]
    rfl
  rw [hform]
  calc
    _ = |(1-w)*(f x-f a) + w*(f x-f b)| := by congr 1; ring
    _ ≤ |(1-w)*(f x-f a)| + |w*(f x-f b)| := abs_add_le _ _
    _ = (1-w)*|f x-f a| + w*|f x-f b| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg hw0]
    _ ≤ (1-w)*(A*(N : ℝ)^(-alpha)) + w*(A*(N : ℝ)^(-alpha)) :=
      add_le_add (mul_le_mul_of_nonneg_left haerr (by linarith))
        (mul_le_mul_of_nonneg_left hberr hw0)
    _ ≤ 2*A*(N : ℝ)^(-alpha) := by
      nlinarith [mul_nonneg hA (Real.rpow_nonneg hNreal.le (-alpha))]

/-- If [the Hölder exponent is positive](hyp:halpha) and [at most one](hyp:halpha1),
[the modulus constant is nonnegative](hyp:hA), [the function satisfies that
Hölder bound on the unit interval](hyp:hf), and [the grid size is positive](hyp:hN),
then [the uniform interpolant has error at most twice the modulus constant
times the grid size to the negative exponent, and is Lipschitz on the unit
interval with constant equal to the modulus constant times the grid size to
the power one minus the exponent](goal). -/
-- @node: holderGridInterpolant_bounds
lemma holderGridInterpolant_bounds {alpha A : ℝ} (halpha : 0 < alpha)
    (halpha1 : alpha ≤ 1) (hA : 0 ≤ A) (f : L1Vec 1 → ℝ)
    (hf : ∀ x ∈ unitCube 1, ∀ y ∈ unitCube 1,
      |f x - f y| ≤ A * ‖x-y‖ ^ alpha)
    (N : ℕ) (hN : 0 < N) :
    (∀ x ∈ unitCube 1, |f x - holderGridInterpolant f N hN x| ≤
      2*A*(N : ℝ)^(-alpha)) ∧
    LipschitzOnWith (Real.toNNReal (A*(N : ℝ)^(1-alpha)))
      (holderGridInterpolant f N hN) (unitCube 1) := by
  refine ⟨holderGridInterpolant_error halpha hA f hf N hN, ?_⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let v (i : ℕ) : L1Vec 1 := WithLp.toLp 1 (fun _ => (i : ℝ)/N)
  let F (i : ℕ) (u : ℝ) := (1-u)*f (v i) + u*f (v (i+1))
  let C := A*(N : ℝ)^(-alpha)
  have hvertex (i : ℕ) (hi : i ≤ N) : v i ∈ unitCube 1 := by
    intro j
    change (i : ℝ)/N ∈ Set.Icc 0 1
    exact ⟨by positivity, (div_le_one hNr).mpr (by exact_mod_cast hi)⟩
  have hslope (i : ℕ) (hi : i < N) : |f (v i)-f (v (i+1))| ≤ C := by
    have hd : ‖v i-v (i+1)‖ = (N : ℝ)⁻¹ := by
      simp only [v, PiLp.norm_eq_of_L1, PiLp.sub_apply,
        Fin.sum_univ_one, Real.norm_eq_abs, Nat.cast_add, Nat.cast_one]
      have he : (i : ℝ)/N - ((i : ℝ)+1)/N = -(N : ℝ)⁻¹ := by ring
      rw [he, abs_neg, abs_of_pos (inv_pos.mpr hNr)]
    have hh := hf (v i) (hvertex i hi.le) (v (i+1)) (hvertex (i+1) hi)
    simpa only [hd, Real.inv_rpow hNr.le, ← Real.rpow_neg hNr.le] using hh
  have hlocal (i : ℕ) (hi : i < N) (u : ℝ) (hu : u ∈ Set.Icc 0 1)
      (w : ℝ) (hw : w ∈ Set.Icc 0 1) : |F i u-F i w| ≤ C*|u-w| := by
    have he : F i u-F i w = (u-w)*(f (v (i+1))-f (v i)) := by dsimp [F]; ring
    rw [he, abs_mul, abs_sub_comm (f (v (i+1))) (f (v i)), mul_comm]
    exact mul_le_mul_of_nonneg_right (hslope i hi) (abs_nonneg _)
  have hend (i : ℕ) (_hi : i+1 < N) : F i 1 = F (i+1) 0 := by simp [F]
  have hordered (x y : L1Vec 1) (hx : x ∈ unitCube 1) (hy : y ∈ unitCube 1)
      (hxy : x.ofLp 0 ≤ y.ofLp 0) :
      |holderGridInterpolant f N hN x-holderGridInterpolant f N hN y| ≤
        (A*(N : ℝ)^(1-alpha))*‖x-y‖ := by
    let i := min ⌊x.ofLp 0*N⌋₊ (N-1)
    let j := min ⌊y.ofLp 0*N⌋₊ (N-1)
    let u := x.ofLp 0*N-i
    let w := y.ofLp 0*N-j
    obtain ⟨hix, hxi, hi⟩ := holderGridIndex_bounds _ (hx 0).1 (hx 0).2 N hN
    obtain ⟨hjy, hyj, hj⟩ := holderGridIndex_bounds _ (hy 0).1 (hy 0).2 N hN
    change (i : ℝ) ≤ x.ofLp 0*N at hix
    change x.ofLp 0*N ≤ (i : ℝ)+1 at hxi
    change (j : ℝ) ≤ y.ofLp 0*N at hjy
    change y.ofLp 0*N ≤ (j : ℝ)+1 at hyj
    have hij : i ≤ j := min_le_min_right _ (Nat.floor_mono (mul_le_mul_of_nonneg_right hxy hNr.le))
    have hu : u ∈ Set.Icc 0 1 := by dsimp [u]; constructor <;> linarith
    have hw : w ∈ Set.Icc 0 1 := by dsimp [w]; constructor <;> linarith
    have ho : (i : ℝ)+u ≤ (j : ℝ)+w := by
      dsimp [u, w]; nlinarith
    have hb := Causalean.Mathlib.Analysis.piecewiseLipschitz_chain_bound
      N F C hlocal hend i j hij hj u w hu hw ho
    have hform (z : L1Vec 1) (hz : z ∈ unitCube 1) :
        holderGridInterpolant f N hN z =
        F (min ⌊z.ofLp 0*N⌋₊ (N-1))
          (z.ofLp 0*N-(min ⌊z.ofLp 0*N⌋₊ (N-1) : ℕ)) := by
      simp [holderGridInterpolant, min_eq_left (hz 0).2, max_eq_right (hz 0).1,
        F, v, Nat.cast_add, Nat.cast_one]
    rw [hform x hx, hform y hy]
    have hd : ‖x-y‖ = y.ofLp 0-x.ofLp 0 := by
      simp [PiLp.norm_eq_of_L1, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hxy)]
    have hc : C*(N : ℝ) = A*(N : ℝ)^(1-alpha) := by
      dsimp [C]
      calc
        A*(N : ℝ)^(-alpha)*(N : ℝ) = A*((N : ℝ)^(-alpha)*(N : ℝ)^(1 : ℝ)) := by
          rw [Real.rpow_one]; ring
        _ = A*(N : ℝ)^(-alpha+1) := by rw [Real.rpow_add hNr]
        _ = A*(N : ℝ)^(1-alpha) := by congr 2; ring
    calc
      _ ≤ C*((j : ℝ)-(i : ℝ)+w-u) := hb
      _ = (C*(N : ℝ))*(y.ofLp 0-x.ofLp 0) := by dsimp [u, w]; ring
      _ = _ := by rw [hc, hd]
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [Real.dist_eq, Real.coe_toNNReal _ (by positivity), dist_eq_norm]
  rcases le_total (x.ofLp 0) (y.ofLp 0) with hxy | hyx
  · exact hordered x y hx hy hxy
  · rw [abs_sub_comm, norm_sub_rev]
    exact hordered y x hy hx hyx

/-- For [a nonnegative Lipschitz constant](hyp:B), if [a scalar function is
Lipschitz with that constant on the unit interval](hyp:hp), then [its graph is
a compact subset of the plane with a homeomorphic parametrization whose
coordinates are the input and the function value, whose Lipschitz constant is
one plus the given constant, and whose second-coordinate Euclidean modulus
at every nonnegative radius is at most the given constant times that radius](goal). -/
-- @node: exists_lipschitz_graph_chart
lemma exists_lipschitz_graph_chart (p : L1Vec 1 → ℝ) (B : ℝ≥0)
    (hp : LipschitzOnWith B p (unitCube 1)) :
    ∃ S : Set (L1Vec 2), IsCompact S ∧
      ∃ phi : homeoClass (unitCube 1) S,
        LipschitzWith (1+B) phi ∧
        (∀ x : unitCube 1, (phi x).val.ofLp 0 = x.val.ofLp 0 ∧
          (phi x).val.ofLp 1 = p x.val) ∧
        ∀ r : ℝ, 0 ≤ r →
          euclidModulus (fun x => if hx : x ∈ unitCube 1 then
            (phi ⟨x,hx⟩).val.ofLp 1 else 0) r ≤ B*r := by
  classical
  let g : unitCube 1 → L1Vec 2 := fun x =>
    WithLp.toLp 1 (fun j => if j = 0 then x.val.ofLp 0 else p x.val)
  have hdist (x y : unitCube 1) :
      dist (g x) (g y) = dist x y + dist (p x.val) (p y.val) := by
    change dist (g x) (g y) = dist x.val y.val + _
    simp [g, PiLp.dist_eq_of_L1, Fin.sum_univ_two]
  have hg : LipschitzWith (1+B) g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [hdist]
    have h := hp.dist_le_mul x.val x.property y.val y.property
    change dist (p x.val) (p y.val) ≤ (B : ℝ) * dist x y at h
    simpa only [NNReal.coe_add, NNReal.coe_one, add_mul, one_mul] using
      add_le_add_right h (dist x y)
  have hinj : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    apply WithLp.ofLp_injective
    funext j
    have h0 := congrArg (fun z : L1Vec 2 => z.ofLp 0) h
    fin_cases j
    simpa [g] using h0
  let : CompactSpace (unitCube 1) := isCompact_iff_compactSpace.mp (unitCube_isCompact 1)
  let phi : homeoClass (unitCube 1) (Set.range g) :=
    (hg.continuous.isClosedEmbedding hinj).isEmbedding.toHomeomorph
  have hcoords (x : unitCube 1) :
      (phi x).val.ofLp 0 = x.val.ofLp 0 ∧ (phi x).val.ofLp 1 = p x.val := by
    constructor <;> rfl
  refine ⟨Set.range g, isCompact_range hg.continuous, phi, ?_, hcoords, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    exact hg.dist_le_mul x y
  · intro r hr
    have hF : LipschitzOnWith B (fun x => if hx : x ∈ unitCube 1 then
        (phi ⟨x,hx⟩).val.ofLp 1 else 0) (unitCube 1) := by
      apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      simp only [dif_pos hx, dif_pos hy, (hcoords ⟨x,hx⟩).2, (hcoords ⟨y,hy⟩).2]
      exact hp.dist_le_mul x hx y hy
    simpa using euclidModulus_le_sqrt_of_lipschitzOn hF hr

/-- Assuming [the Yarotsky coordinate approximation result](hyp:hgate),
[there is a positive universal constant such that every scalar Hölder function
on the unit interval, with exponent between zero and one and a nonnegative
modulus constant, has a width-12 ReLU approximation at each positive depth,
with uniform error at most the universal constant times the modulus constant
times depth to the power minus twice the exponent](goal). -/
-- @node: relu_holder_curve_coord
lemma relu_holder_curve_coord (hgate : YarotskyCoordinateApprox) :
    ∃ c : ℝ, 0 < c ∧ ∀ (alpha A : ℝ), 0 < alpha → alpha ≤ 1 → 0 ≤ A →
      ∀ f : L1Vec 1 → ℝ,
        (∀ x ∈ unitCube 1, ∀ y ∈ unitCube 1,
          |f x - f y| ≤ A * ‖x-y‖ ^ alpha) →
        ∀ L : ℕ, 1 ≤ L → ∃ q : ReLUNet 1 1 12 L,
          ∀ x ∈ unitCube 1,
            |(q.eval x).ofLp 0-f x| ≤ c*A*(L : ℝ)^(-(2*alpha)) := by
  obtain ⟨a, c, ha, hc, happ⟩ := hgate 1 (by omega)
  refine ⟨2 + 2*a*c, by positivity, ?_⟩
  intro alpha A halpha halpha1 hA f hf L hL
  let N : ℕ := ⌈(L : ℝ)^2⌉₊
  have hN : 0 < N := by
    dsimp [N]
    exact Nat.ceil_pos.mpr (by positivity)
  obtain ⟨herror, hLip⟩ := holderGridInterpolant_bounds halpha halpha1 hA f hf N hN
  obtain ⟨S, hS, phi, hphi, hcoords, hmod⟩ :=
    exists_lipschitz_graph_chart _ _ hLip
  obtain ⟨q, hq⟩ := happ 2 S hS phi _ hphi 1 L hL
  refine ⟨q, ?_⟩
  intro x hx
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hNcast : (N : ℝ) = (L : ℝ)^2 := by
    have hNeq : N = L^2 := by
      dsimp [N]
      rw [← Nat.cast_pow, Nat.ceil_natCast]
    rw [hNeq, Nat.cast_pow]
  have hpow (b : ℝ) : (N : ℝ)^b = (L : ℝ)^(2*b) := by
    rw [hNcast, Real.rpow_mul hLpos.le, Real.rpow_two]
  have hinterp : (N : ℝ)^(-alpha) = (L : ℝ)^(-(2*alpha)) := by
    rw [hpow]
    congr 1
    ring
  have hslope : (N : ℝ)^(1-alpha) * (L : ℝ)^(-(2 : ℝ)) =
      (L : ℝ)^(-(2*alpha)) := by
    rw [hpow, ← Real.rpow_add hLpos]
    congr 1
    ring
  have herr := hq x hx
  simp only [dif_pos hx, (hcoords ⟨x,hx⟩).2, Nat.cast_one, div_one] at herr
  have hmodulus := hmod (c * (L : ℝ)^(-(2 : ℝ))) (by positivity)
  rw [Real.coe_toNNReal _ (mul_nonneg hA (Real.rpow_nonneg (Nat.cast_nonneg N) _))] at hmodulus
  have hnet : |holderGridInterpolant f N hN x - (q.eval x).ofLp 0| ≤
      a*c*A*(L : ℝ)^(-(2*alpha)) := by
    calc
      _ ≤ a * _ := herr
      _ ≤ a * (A*(N : ℝ)^(1-alpha) * (c*(L : ℝ)^(-(2 : ℝ)))) :=
        mul_le_mul_of_nonneg_left hmodulus ha.le
      _ = _ := by rw [show A*(N : ℝ)^(1-alpha) * (c*(L : ℝ)^(-(2 : ℝ))) =
          c*A*((N : ℝ)^(1-alpha) * (L : ℝ)^(-(2 : ℝ))) by ring, hslope]; ring
  calc
    _ ≤ |(q.eval x).ofLp 0 - holderGridInterpolant f N hN x| +
        |holderGridInterpolant f N hN x - f x| := abs_sub_le _ _ _
    _ = |holderGridInterpolant f N hN x - (q.eval x).ofLp 0| +
        |f x - holderGridInterpolant f N hN x| := by
      exact congrArg₂ (· + ·) (abs_sub_comm _ _) (abs_sub_comm _ _)
    _ ≤ a*c*A*(L : ℝ)^(-(2*alpha)) + 2*A*(N : ℝ)^(-alpha) :=
      add_le_add hnet (herror x hx)
    _ ≤ (2 + 2*a*c)*A*(L : ℝ)^(-(2*alpha)) := by
      rw [hinterp]
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg ha.le hc.le) hA)
        (Real.rpow_nonneg hLpos.le (-(2*alpha)))]

/-- Assuming [the Yarotsky coordinate approximation result](hyp:hgate) and
[an input dimension equal to one](hyp:hk), [there is a positive constant such
that every scalar Hölder function on the unit cube, with exponent between zero
and one and nonnegative modulus constant, admits a ReLU approximation of
width twice the dimension plus ten at every positive depth, with uniform error
bounded by that constant times the modulus constant times depth to the power
minus twice the exponent divided by the dimension](goal). -/
-- @node: relu_deep_approx_holder
lemma relu_deep_approx_holder (hgate : YarotskyCoordinateApprox)
    (k : ℕ) (hk : k = 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ (alpha A : ℝ), 0 < alpha → alpha ≤ 1 → 0 ≤ A →
      ∀ f : L1Vec k → ℝ,
        (∀ x ∈ unitCube k, ∀ y ∈ unitCube k,
          |f x - f y| ≤ A * ‖x-y‖ ^ alpha) →
        ∀ L : ℕ, 1 ≤ L → ∃ q : ReLUNet k 1 (2*k+10) L,
          ∀ x ∈ unitCube k,
            |(q.eval x).ofLp 0-f x| ≤ c * A * (L : ℝ) ^ (-(2*alpha)/k) := by
  subst k
  simpa using relu_holder_curve_coord hgate
-- @node: relu_parallel_stack
/-- [Any family of scalar-output ReLU networks with common input dimension,
width bound, and depth can be combined into one vector-output network with the
same depth and width bound multiplied by the number of outputs, reproducing
each component network exactly on every input](goal). -/
lemma relu_parallel_stack {k m W L : ℕ} (q : Fin m → ReLUNet k 1 W L) :
    ∃ Q : ReLUNet k m (m*W) L,
      ∀ x j, (Q.eval x).ofLp j = ((q j).eval x).ofLp 0 := by
  exact relu_parallel_stack_constructed q
-- @node: clampDiagonalLayer
/-- For [a dimension](hyp:k), [a common diagonal coefficient](hyp:a), and
[a common intercept](hyp:b), the [diagonal affine layer](goal) has that many
inputs and outputs, multiplies each input coordinate by the coefficient, and
adds the intercept. -/
def clampDiagonalLayer (k : ℕ) (a b : ℝ) : AffineLayer :=
  ⟨k, k, (fun j i => if i = j then a else 0), (fun _ => b)⟩

-- @node: clampDiagonalLayer_apply
/-- [At every coordinate within the layer's dimension, applying the diagonal
affine layer gives the diagonal coefficient times the corresponding input
coordinate plus the common intercept](goal). -/
lemma clampDiagonalLayer_apply (k : ℕ) (a b : ℝ) (x : ℕ → ℝ) (j : Fin k) :
    (clampDiagonalLayer k a b).apply x j.val = a * x j.val + b := by
  classical
  change (if h : j.val < k then
    (∑ i : Fin k, (if i = ⟨j.val,h⟩ then a else 0) * x i.val) + b else 0) = _
  simp [j.isLt, ite_mul]

-- @node: cubeClampNet
/-- For [a dimension](hyp:k), the [cube-clamping ReLU network](goal) has
that input and output dimension, two hidden layers, and width bound twice the
dimension; it applies a diagonal identity layer followed by a diagonal
coefficient of minus one and intercept one, then subtracts each resulting
coordinate from one. -/
noncomputable def cubeClampNet (k : ℕ) : ReLUNet k k (2*k) 2 where
  hidden := [clampDiagonalLayer k 1 0, clampDiagonalLayer k (-1) 1]
  depth := rfl
  widths := by
    intro l hl
    rcases List.mem_cons.mp hl with rfl | hl
    · change k ≤ 2*k; omega
    · rcases List.mem_cons.mp hl with rfl | hl
      · change k ≤ 2*k; omega
      · simp at hl
  firstInput := by
    intro l hl
    have heq := Option.some.inj hl
    subst l
    rfl
  compatible := by simp [List.isChain_cons_cons, clampDiagonalLayer,
    AffineLayer.input, AffineLayer.output]
  outputWeight := fun j i => if i.val = j.val then -1 else 0
  outputBias := fun _ => 1

-- @node: cubeClampNet_eval
/-- [Each output coordinate of the cube-clamping network equals its input
coordinate truncated below at zero and above at one](goal). -/
lemma cubeClampNet_eval (k : ℕ) (x : L1Vec k) (j : Fin k) :
    ((cubeClampNet k).eval x).ofLp j = max 0 (min (x.ofLp j) 1) := by
  classical
  have hout : ((cubeClampNet k).eval x).ofLp j =
      1 - max 0 (1 - max 0 (x.ofLp j)) := by
    let input : ℕ → ℝ := fun i => if h : i < k then x.ofLp ⟨i,h⟩ else 0
    let z := reluLayer (clampDiagonalLayer k 1 0) input
    let w := reluLayer (clampDiagonalLayer k (-1) 1) z
    have hz (i : Fin k) : z i.val = max 0 (x.ofLp i) := by
      dsimp [z, reluLayer]
      rw [clampDiagonalLayer_apply]
      simp [input, i.isLt]
    have hw (i : Fin k) : w i.val = max 0 (1 - max 0 (x.ofLp i)) := by
      dsimp [w, reluLayer]
      rw [clampDiagonalLayer_apply, hz]
      congr 1
      ring
    change (∑ i : Fin k, (if i.val = j.val then -1 else 0) * w i.val) + 1 = _
    simp only [Fin.val_inj, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, hw]
    ring
  rw [hout]
  by_cases h0 : x.ofLp j ≤ 0
  · rw [max_eq_left h0, max_eq_right (by norm_num),
      min_eq_left (by linarith), max_eq_left h0]
    norm_num
  · have hp : 0 ≤ x.ofLp j := le_of_lt (lt_of_not_ge h0)
    rw [max_eq_right hp]
    by_cases h1 : x.ofLp j ≤ 1
    · rw [max_eq_right (by linarith), min_eq_left h1, max_eq_right hp]
      ring
    · rw [max_eq_left (by linarith), min_eq_right (le_of_not_ge h1)]
      norm_num

-- @node: relu_clamp_cube
/-- [In every dimension there is a ReLU network with two hidden layers and
width bound twice the dimension that clamps every coordinate to the unit
interval, is Lipschitz with constant one, and maps every input into the unit
cube](goal). -/
lemma relu_clamp_cube (k : ℕ) :
    ∃ q : ReLUNet k k (2*k) 2,
      (∀ x j, (q.eval x).ofLp j = max 0 (min (x.ofLp j) 1)) ∧
      LipschitzWith 1 q.eval ∧ Set.MapsTo q.eval Set.univ (unitCube k) := by
  refine ⟨cubeClampNet k, cubeClampNet_eval k, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul, PiLp.dist_eq_of_L1]
    apply Finset.sum_le_sum
    intro j _
    change dist (((cubeClampNet k).eval x).ofLp j)
      (((cubeClampNet k).eval y).ofLp j) ≤ dist (x.ofLp j) (y.ofLp j)
    rw [cubeClampNet_eval, cubeClampNet_eval]
    simpa only [NNReal.coe_one, one_mul, id_eq] using
      (((LipschitzWith.id (α := ℝ)).min_const 1).const_max 0).dist_le_mul
        (x.ofLp j) (y.ofLp j)
  · intro x _ j
    rw [cubeClampNet_eval]
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩
end Papers.TbsNeuralCausalPi
