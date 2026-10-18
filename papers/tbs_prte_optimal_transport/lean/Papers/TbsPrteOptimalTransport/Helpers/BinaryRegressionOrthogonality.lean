module
public import Papers.TbsPrteOptimalTransport.Helpers.BinaryScoreRemainder
/-! Integrated binary branch cancellation for simultaneous regression directions. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory
open scoped Topology

-- The fitted branch is allowed to differ from the population branch. The
-- margin and the L2 envelope control that event without a uniform direction bound.
-- @node: binary_affine_debiased_integrated_remainder
/-- Suppose [the gap constant is positive](hyp:hc), [the upper](hyp:hq),
[lower](hyp:hl), and [boundary functions](hyp:hb) and [the upper](hyp:hdq),
[lower](hyp:hdl), and [boundary directions are measurable](hyp:hdb), and
[the direction envelope is square integrable](hyp:herr). If [the original
upper-minus-lower gap and both boundary distances exceed or equal the gap
constant almost everywhere](hyp:hgap) and [all three directions are bounded
in absolute value by the envelope almost everywhere](hyp:herrors), then
[the hinge change along the affine path, minus the path increments weighted
by the fitted branch indicators, is integrable and its integral has absolute
value at most twenty-six divided by the gap constant times the integrated
squared envelope times the squared path parameter](goal). -/
lemma binary_affine_debiased_integrated_remainder {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (q l b dq dl db err : X → ℝ) (c t : ℝ)
    (hc : 0 < c)
    (hq : Measurable q) (hl : Measurable l) (hb : Measurable b)
    (hdq : Measurable dq) (hdl : Measurable dl) (hdb : Measurable db)
    (herr : MemLp err 2 μ)
    (hgap : ∀ᵐ x ∂μ, c ≤ q x - l x ∧ c ≤ |b x - l x| ∧ c ≤ |b x - q x|)
    (herrors : ∀ᵐ x ∂μ, |dq x| ≤ err x ∧ |dl x| ≤ err x ∧ |db x| ≤ err x) :
    let R := fun x => max 0 (q x + t * dq x - max (l x + t * dl x) (b x + t * db x)) -
      max 0 (q x - max (l x) (b x)) -
      (indicator (q x + t * dq x > max (l x + t * dl x) (b x + t * db x)) * (t * dq x) -
        indicator (l x + t * dl x < b x + t * db x ∧ b x + t * db x < q x + t * dq x) *
          (t * db x) -
        indicator (l x + t * dl x > b x + t * db x) *
          indicator (q x + t * dq x > max (l x + t * dl x) (b x + t * db x)) * (t * dl x))
    Integrable R μ ∧ |∫ x, R x ∂μ| ≤ ((26 / c) * ∫ x, err x ^ 2 ∂μ) * t ^ 2 := by
  have hscaled : ∀ᵐ x ∂μ, |t * dq x| ≤ |t| * err x ∧
      |t * dl x| ≤ |t| * err x ∧ |t * db x| ≤ |t| * err x := by
    filter_upwards [herrors] with x hx
    simp only [abs_mul]
    exact ⟨mul_le_mul_of_nonneg_left hx.1 (abs_nonneg t),
      mul_le_mul_of_nonneg_left hx.2.1 (abs_nonneg t),
      mul_le_mul_of_nonneg_left hx.2.2 (abs_nonneg t)⟩
  have h := binary_hinge_fitted_score_integrated_remainder μ q l b
    (fun x => t * dq x) (fun x => t * dl x) (fun x => t * db x)
    (fun x => |t| * err x) c hc hq hl hb
    (by fun_prop) (by fun_prop) (by fun_prop) (herr.const_mul |t|) hgap hscaled
  dsimp only at h ⊢
  refine ⟨h.1, h.2.trans_eq ?_⟩
  simp only [mul_pow, integral_const_mul, sq_abs]
  ring

-- This proves the derivative after integration from a global quadratic
-- remainder, rather than exchanging an integral with moving indicators.
-- @node: binary_affine_debiased_integrated_orthogonality
/-- If [the gap constant is positive](hyp:hc), [the upper](hyp:hq), [lower](hyp:hl),
and [boundary functions](hyp:hb) and [the upper](hyp:hdq), [lower](hyp:hdl),
and [boundary directions are measurable](hyp:hdb), [the direction envelope
is square integrable](hyp:herr), [the upper-minus-lower gap and both boundary
distances are at least the gap constant almost everywhere](hyp:hgap), and
[all directions are bounded in absolute value by the envelope almost
everywhere](hyp:herrors), then [the integral of the affine hinge change minus
the path increments weighted by the fitted branch indicators has derivative
zero at path parameter zero](goal). -/
lemma binary_affine_debiased_integrated_orthogonality {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (q l b dq dl db err : X → ℝ) (c : ℝ)
    (hc : 0 < c)
    (hq : Measurable q) (hl : Measurable l) (hb : Measurable b)
    (hdq : Measurable dq) (hdl : Measurable dl) (hdb : Measurable db)
    (herr : MemLp err 2 μ)
    (hgap : ∀ᵐ x ∂μ, c ≤ q x - l x ∧ c ≤ |b x - l x| ∧ c ≤ |b x - q x|)
    (herrors : ∀ᵐ x ∂μ, |dq x| ≤ err x ∧ |dl x| ≤ err x ∧ |db x| ≤ err x) :
    HasDerivAt (fun t : ℝ => ∫ x,
      max 0 (q x + t * dq x - max (l x + t * dl x) (b x + t * db x)) -
      max 0 (q x - max (l x) (b x)) -
      (indicator (q x + t * dq x > max (l x + t * dl x) (b x + t * db x)) * (t * dq x) -
        indicator (l x + t * dl x < b x + t * db x ∧ b x + t * db x < q x + t * dq x) *
          (t * db x) -
        indicator (l x + t * dl x > b x + t * db x) *
          indicator (q x + t * dq x > max (l x + t * dl x) (b x + t * db x)) * (t * dl x))
      ∂μ) 0 0 := by
  let F := fun t : ℝ => ∫ x,
    max 0 (q x + t * dq x - max (l x + t * dl x) (b x + t * db x)) -
    max 0 (q x - max (l x) (b x)) -
    (indicator (q x + t * dq x > max (l x + t * dl x) (b x + t * db x)) * (t * dq x) -
      indicator (l x + t * dl x < b x + t * db x ∧ b x + t * db x < q x + t * dq x) *
        (t * db x) -
      indicator (l x + t * dl x > b x + t * db x) *
        indicator (q x + t * dq x > max (l x + t * dl x) (b x + t * db x)) * (t * dl x)) ∂μ
  change HasDerivAt F 0 0
  have hbound : ∀ t : ℝ, |F t| ≤ ((26 / c) * ∫ x, err x ^ 2 ∂μ) * t ^ 2 :=
    fun t => (binary_affine_debiased_integrated_remainder μ q l b dq dl db err c t
      hc hq hl hb hdq hdl hdb herr hgap herrors).2
  have hz : F 0 = 0 := by
    have h := hbound 0
    exact abs_nonpos_iff.mp (by simpa using h)
  have ho : F =O[nhds 0] (fun t : ℝ => t ^ 2) := by
    apply Asymptotics.IsBigO.of_bound ((26 / c) * ∫ x, err x ^ 2 ∂μ)
    exact Filter.Eventually.of_forall fun t => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)] using hbound t
  apply HasDerivAt.of_isLittleO
  simpa only [hz, sub_zero, smul_zero] using
    ho.trans_isLittleO (Asymptotics.isLittleO_pow_id (𝕜 := ℝ) (by norm_num : 1 < 2))

universe v

-- The zero boundary and invalid indices have zero direction automatically.
-- @node: binary_regression_boundary_path
/-- [Perturbing only the treated regressions along an affine direction changes
the propensity-minus-regression-increment boundary by minus the path parameter
times the difference between the upper and lower regression directions,
with zero extension at invalid or zero indices](goal). -/
lemma binary_regression_boundary_path {X Z : Type v} (L : LevelData Z X)
    (e : NuisanceBin L) (d : PositiveIndex L.K → X → ℝ) (k : ℕ) (x : X) (t : ℝ) :
    let et := {e with P1 := fun a x => e.P1 a x + t * d a x}
    positiveValue et.pLev (k + 1) x - binFullJ L et k x =
      (positiveValue e.pLev (k + 1) x - binFullJ L e k x) +
        t * (-(positiveValue d (k + 1) x - positiveValue d k x)) := by
  dsimp only
  simp only [binFullJ, positiveValue]
  split_ifs <;> ring

-- The correction is the conditional mean of Dbd * (RP_{k+1} - RP_k)
-- under a P1-only perturbation. Thus this is the actual regression cancellation
-- for hMinus, including simultaneous changes at both positive levels.
-- @node: binary_hMinus_regression_integrated_orthogonality
/-- Suppose [the gap constant is positive](hyp:hc), [the upper](hyp:hq) and
[lower pooled policy values are measurable](hyp:hl), [the adjusted boundary
is measurable](hyp:hb), [the difference between upper and lower regression
directions is measurable](hyp:hd), and [its envelope is square integrable](hyp:herr).
If [the pooled-value gap and both adjusted-boundary distances are at least
the gap constant almost everywhere](hyp:hgap) and [the regression direction
difference is bounded in absolute value by the envelope almost everywhere](hyp:herrors),
then [the integral of the binary hinge change along the regression-only affine
path, minus the fitted boundary indicator times the path parameter and the
regression direction difference, has derivative zero at zero](goal). -/
lemma binary_hMinus_regression_integrated_orthogonality {X Z : Type v} [MeasurableSpace X]
    (μ : Measure X) (phi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e : NuisanceBin L) (d : PositiveIndex L.K → X → ℝ) (k j : ℕ)
    (err : X → ℝ) (c : ℝ) (hc : 0 < c)
    (hq : Measurable (pooledQBin phi L e k j))
    (hl : Measurable (pooledQBin phi L e k (j - 1)))
    (hb : Measurable (fun x => positiveValue e.pLev (k + 1) x - binFullJ L e k x))
    (hd : Measurable (fun x => positiveValue d (k + 1) x - positiveValue d k x))
    (herr : MemLp err 2 μ)
    (hgap : ∀ᵐ x ∂μ,
      c ≤ pooledQBin phi L e k j x - pooledQBin phi L e k (j - 1) x ∧
      c ≤ |positiveValue e.pLev (k + 1) x - binFullJ L e k x - pooledQBin phi L e k (j - 1) x| ∧
      c ≤ |positiveValue e.pLev (k + 1) x - binFullJ L e k x - pooledQBin phi L e k j x|)
    (herrors : ∀ᵐ x ∂μ, |positiveValue d (k + 1) x - positiveValue d k x| ≤ err x) :
    HasDerivAt (fun t : ℝ => ∫ x,
      let et := {e with P1 := fun a x => e.P1 a x + t * d a x}
      hMinus phi L et k j x - hMinus phi L e k j x -
        Dbd phi L et k j x * (t * (positiveValue d (k + 1) x - positiveValue d k x)) ∂μ) 0 0 := by
  have he : ∀ᵐ x ∂μ, |(0 : ℝ)| ≤ err x ∧ |(0 : ℝ)| ≤ err x ∧
      |-(positiveValue d (k + 1) x - positiveValue d k x)| ≤ err x := by
    filter_upwards [herrors] with x hx
    have he0 := (abs_nonneg _).trans hx
    simpa only [abs_zero, abs_neg] using And.intro he0 (And.intro he0 hx)
  have h := binary_affine_debiased_integrated_orthogonality μ
    (pooledQBin phi L e k j) (pooledQBin phi L e k (j - 1))
    (fun x => positiveValue e.pLev (k + 1) x - binFullJ L e k x)
    (fun _ => 0) (fun _ => 0)
    (fun x => -(positiveValue d (k + 1) x - positiveValue d k x)) err c
    hc hq hl hb (by fun_prop) (by fun_prop) (by fun_prop) herr hgap he
  convert h using 1
  funext t
  apply integral_congr_ae
  filter_upwards [] with x
  have hq' : ∀ a, pooledQBin phi L {e with P1 := fun a x => e.P1 a x + t * d a x} k a x =
      pooledQBin phi L e k a x := fun _ => rfl
  have hb' : positiveValue e.pLev (k + 1) x -
      binFullJ L {e with P1 := fun a x => e.P1 a x + t * d a x} k x =
      (positiveValue e.pLev (k + 1) x - binFullJ L e k x) +
        t * (-(positiveValue d (k + 1) x - positiveValue d k x)) :=
    binary_regression_boundary_path L e d k x t
  simp only [hMinus, Dbd, hq', hb', mul_zero, add_zero]
  ring

-- @node: binary_RP_regression_path
/-- [Along an affine perturbation of the treated regressions, the treated
regression residual equals its original value minus the path parameter times
the regression direction weighted by membership in the level's instrument
set and divided by that set's conditional probability](goal). -/
lemma binary_RP_regression_path {X Z : Type v}
    (L : LevelData Z X) (e : NuisanceBin L) (d : PositiveIndex L.K → X → ℝ)
    (k : ℕ) (o : Obs X Z) (t : ℝ) :
    RP L {e with P1 := fun a x => e.P1 a x + t * d a x} k o =
      RP L e k o - t * (indicator (o.2.1 ∈ L.S k) / positiveValue e.piLev k o.1 *
        positiveValue d k o.1) := by
  by_cases hk : k = 0
  · subst k
    simp [RP, positiveValue]
  · simp only [RP, if_neg hk, positiveValue]
    split_ifs <;> ring

-- Every other residual is unchanged. Keeping the fitted branch coefficients
-- here makes this identity valid even when the regression perturbation crosses
-- a branch, so the integrated quadratic lemma can control that event.
-- @node: binary_regression_score_path_decomposition
/-- [Under an affine perturbation of the treated regressions, the binary
component score equals the perturbed hinge plus the original regression,
propensity, and policy residuals with their usual signs and fitted branch
weights, minus the fitted boundary indicator times the path parameter times
the difference of the upper and lower instrument-membership-weighted,
inverse-probability-weighted regression directions](goal). -/
lemma binary_regression_score_path_decomposition {X Z : Type v}
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e : NuisanceBin L)
    (d : PositiveIndex L.K → X → ℝ) (k j : ℕ) (o : Obs X Z) (t : ℝ) :
    let et := {e with P1 := fun a x => e.P1 a x + t * d a x}
    binScoreComponents phi dphi L et k j o =
      hMinus phi L et k j o.1 + Dbd phi L et k j o.1 * (RP L e (k + 1) o - RP L e k o) -
      Dbd phi L et k j o.1 * Rp L e (k + 1) o -
      (if j = 1 then Edom phi L et k j o.1 * Iact phi L et k j o.1 * Rp L e k o else 0) +
      Iact phi L et k j o.1 * RqBin dphi L e k j o -
      Edom phi L et k j o.1 * Iact phi L et k j o.1 * RqBin dphi L e k (j - 1) o -
      Dbd phi L et k j o.1 * t *
        (indicator (o.2.1 ∈ L.S (k + 1)) / positiveValue e.piLev (k + 1) o.1 *
          positiveValue d (k + 1) o.1 -
        indicator (o.2.1 ∈ L.S k) / positiveValue e.piLev k o.1 * positiveValue d k o.1) := by
  dsimp only
  have hp : ∀ a, Rp L {e with P1 := fun a x => e.P1 a x + t * d a x} a o =
      Rp L e a o := fun _ => rfl
  have hq : ∀ a, RqBin dphi L {e with P1 := fun a x => e.P1 a x + t * d a x} k a o =
      RqBin dphi L e k a o := fun _ => rfl
  simp only [binScoreComponents, binary_RP_regression_path, hp, hq]
  ring

end Papers.TbsPrteOptimalTransport
