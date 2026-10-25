module
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVSetup
public import Causalean.Stat.Minimax.SharpHellinger
/-! Deterministic density and loss perturbation steps for `t_err_dp`.

The density comparisons use the paper's unhalved squared Hellinger convention.
They apply to each frozen preliminary fit; no sampling independence is needed.
-/
public section

namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory

variable {A : Type*} [MeasurableSpace A]

/-- If [the density class has common-support lower and upper bounds c₀ and
CG](hyp:hBounds), [the true density belongs to the class](hyp:hg₀), and [g
belongs to the class](hyp:hg), [g is everywhere at most CG/c₀ times the true
density](goal). -/
-- @node: rdiv_density_ratio_of_bounds
lemma rdiv_density_ratio_of_bounds {Z : Type*}
    (G : Set (A → Z → ℝ)) (g₀ g : A → Z → ℝ)
    (support : Set (A × Z)) (c₀ CG : ℝ)
    (hBounds : DensityBounds G g₀ support c₀ CG) (hg₀ : g₀ ∈ G) (hg : g ∈ G) :
    ∀ x z, g x z ≤ (CG / c₀) * g₀ x z := by
  intro x z
  by_cases hs : (x, z) ∈ support
  · calc
      g x z ≤ CG := hBounds.2.2.2.1 g hg (x, z) hs
      _ = (CG / c₀) * c₀ := by field_simp [ne_of_gt hBounds.1]
      _ ≤ (CG / c₀) * g₀ x z := mul_le_mul_of_nonneg_left
        (hBounds.2.2.1 (x, z) hs) (div_nonneg hBounds.2.1.le hBounds.1.le)
  · rw [hBounds.2.2.2.2 g hg (x, z) hs, hBounds.2.2.2.2 g₀ hg₀ (x, z) hs,
      mul_zero]

/-- If [the class consists of realizable conditional densities with true density
g₀](hyp:hDensity) and [g belongs to that class](hyp:hg), [g is integrable with
respect to the reference measure for almost every instrument value under its
population distribution](goal). -/
-- @node: rdiv_density_integrable_of_realizable
lemma rdiv_density_integrable_of_realizable {𝒲 Z : Type*}
    [MeasurableSpace 𝒲] [MeasurableSpace Z] (V : IVWorld 𝒲 A Z)
    (μ : Measure A) (G : Set (A → Z → ℝ)) (g₀ g : A → Z → ℝ)
    (hDensity : DensityRealizable V μ G g₀) (hg : g ∈ G) :
    ∀ᵐ z ∂V.law.map V.zOf, Integrable (fun x => g x z) μ := by
  filter_upwards [(hDensity.2 g hg).2.2] with z hz
  by_contra hi
  rw [integral_undef hi] at hz
  norm_num at hz

/-- Suppose [f is integrable](hyp:hf), [g is integrable](hyp:hg), [f is
nonnegative everywhere](hyp:hf0), [g is nonnegative everywhere](hyp:hg0),
[f integrates to one](hyp:hf1), [g integrates to one](hyp:hg1), [the test
function u is measurable up to a null set](hyp:hu), [B is nonnegative](hyp:hB),
and [the absolute value of u is at most B almost everywhere](hyp:huB).
Then [the squared difference between the f-weighted and g-weighted integrals
of u is at most four times B squared times their squared Hellinger distance](goal). -/
-- @node: rdiv_density_test_hellinger_sq
lemma rdiv_density_test_hellinger_sq (μ : Measure A) (f g u : A → ℝ) (B : ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf1 : ∫ x, f x ∂μ = 1) (hg1 : ∫ x, g x ∂μ = 1)
    (hu : AEStronglyMeasurable u μ) (hB : 0 ≤ B)
    (huB : ∀ᵐ x ∂μ, |u x| ≤ B) :
    ((∫ x, u x * f x ∂μ) - ∫ x, u x * g x ∂μ) ^ 2 ≤
      4 * B ^ 2 * hellingerSqDensity μ f g := by
  have huf : Integrable (fun x => u x * f x) μ := by
    apply (hf.mul_const B).mono' (hu.mul hf.aestronglyMeasurable)
    filter_upwards [huB] with x hx
    simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hf0 x), mul_comm] using
      mul_le_mul_of_nonneg_right hx (hf0 x)
  have hug : Integrable (fun x => u x * g x) μ := by
    apply (hg.mul_const B).mono' (hu.mul hg.aestronglyMeasurable)
    filter_upwards [huB] with x hx
    simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hg0 x), mul_comm] using
      mul_le_mul_of_nonneg_right hx (hg0 x)
  have hint : |(∫ x, u x * f x ∂μ) - ∫ x, u x * g x ∂μ| ≤
      B * ∫ x, |f x - g x| ∂μ := by
    rw [← integral_sub huf hug, ← integral_const_mul]
    apply abs_integral_le_integral_abs.trans
    apply integral_mono_ae (huf.sub hug).abs ((hf.sub hg).abs.const_mul B)
    filter_upwards [huB] with x hx
    change |u x * f x - u x * g x| ≤ B * |f x - g x|
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
  have hH := Causalean.Stat.Minimax.hellingerSqDensity_bounds μ f g
    hf hg hf0 hg0 hf1 hg1
  have hTV := Causalean.Stat.Minimax.integral_abs_sub_le_sqrt_hellinger_energy
    μ f g hf hg hf0 hg0 hf1 hg1
  have hbound := hint.trans (mul_le_mul_of_nonneg_left hTV hB)
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hbound 2
  rw [sq_abs, mul_pow, Real.sq_sqrt (mul_nonneg hH.1 (by linarith :
    0 ≤ 4 - Causalean.Stat.hellingerSqDensity μ f g))] at hsq
  change _ ≤ 4 * B ^ 2 * Causalean.Stat.hellingerSqDensity μ f g
  exact hsq.trans (by
    nlinarith [mul_nonneg (sq_nonneg B)
      (sq_nonneg (Causalean.Stat.hellingerSqDensity μ f g))])

/-- Suppose [u is measurable up to a null set](hyp:hu), [B is
nonnegative](hyp:hB), [the absolute value of u is at most B almost
everywhere](hyp:huB), [f and g are integrable, nonnegative, normalized densities
for almost every instrument value](hyp:hDensities), [their induced operator
difference is measurable up to a null set](hyp:hError), and [their conditional
squared Hellinger distance is integrable over instrument values](hyp:hH).
Then [the L2 norm of their operator difference applied to u is at most twice B
times the square root of the integrated squared Hellinger distance](goal). -/
-- @node: rdiv_density_operator_global_bound
lemma rdiv_density_operator_global_bound {Z : Type*} [MeasurableSpace Z]
    (μ : Measure A) (ν : Measure Z) (f g : A → Z → ℝ) (u : A → ℝ) (B : ℝ)
    (hu : AEStronglyMeasurable u μ) (hB : 0 ≤ B)
    (huB : ∀ᵐ x ∂μ, |u x| ≤ B)
    (hDensities : ∀ᵐ z ∂ν, Integrable (fun x => f x z) μ ∧
      Integrable (fun x => g x z) μ ∧
      (∀ x, 0 ≤ f x z) ∧ (∀ x, 0 ≤ g x z) ∧
      (∫ x, f x z ∂μ) = 1 ∧ (∫ x, g x z ∂μ) = 1)
    (hError : AEStronglyMeasurable (densityOperator μ f u - densityOperator μ g u) ν)
    (hH : Integrable (fun z => hellingerSqDensity μ (fun x => f x z) (fun x => g x z)) ν) :
    inputL2Norm ν (densityOperator μ f u - densityOperator μ g u) ≤
      2 * B * Real.sqrt (∫ z, hellingerSqDensity μ (fun x => f x z) (fun x => g x z) ∂ν) := by
  let e := densityOperator μ f u - densityOperator μ g u
  have hpoint : ∀ᵐ z ∂ν, e z ^ 2 ≤
      4 * B ^ 2 * hellingerSqDensity μ (fun x => f x z) (fun x => g x z) := by
    filter_upwards [hDensities] with z hz
    exact rdiv_density_test_hellinger_sq μ (fun x => f x z) (fun x => g x z) u B
      hz.1 hz.2.1 hz.2.2.1 hz.2.2.2.1 hz.2.2.2.2.1 hz.2.2.2.2.2 hu hB huB
  have he : Integrable (fun z => e z ^ 2) ν := by
    apply (hH.const_mul (4 * B ^ 2)).mono' (hError.pow 2)
    filter_upwards [hpoint] with z hz
    change ‖e z ^ 2‖ ≤ _
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (e z))] using hz
  have henergy : (∫ z, e z ^ 2 ∂ν) ≤
      4 * B ^ 2 * ∫ z, hellingerSqDensity μ (fun x => f x z) (fun x => g x z) ∂ν := by
    rw [← integral_const_mul]
    exact integral_mono_ae he (hH.const_mul _) hpoint
  have hH0 : 0 ≤ ∫ z, hellingerSqDensity μ (fun x => f x z) (fun x => g x z) ∂ν :=
    integral_nonneg fun z => integral_nonneg fun x => sq_nonneg _
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg (mul_nonneg (by norm_num) hB) (Real.sqrt_nonneg _), ?_⟩
  change (∫ z, e z ^ 2 ∂ν) ≤ _
  rw [mul_pow, Real.sq_sqrt hH0]
  nlinarith only [henergy]

/-- Suppose [f is integrable](hyp:hf), [g is integrable](hyp:hg), [f is
nonnegative everywhere](hyp:hf0), [g is nonnegative everywhere](hyp:hg0),
[u is measurable up to a null set](hyp:hu), [f is at most R times g almost
everywhere](hyp:hRatio), and [u squared times g is integrable](hyp:hMoment).
Then [the squared integral of the absolute value of u times the absolute density
difference is at most 2(R+1) times the g-weighted second moment of u times the
squared Hellinger distance](goal). -/
-- @node: rdiv_density_relative_hellinger_sq
lemma rdiv_density_relative_hellinger_sq (μ : Measure A) (f g u : A → ℝ) (R : ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hu : AEStronglyMeasurable u μ)
    (hRatio : ∀ᵐ x ∂μ, f x ≤ R * g x)
    (hMoment : Integrable (fun x => u x ^ 2 * g x) μ) :
    (∫ x, |u x| * |f x - g x| ∂μ) ^ 2 ≤
      2 * (R + 1) * (∫ x, u x ^ 2 * g x ∂μ) * hellingerSqDensity μ f g := by
  let v := fun x => u x * (Real.sqrt (f x) + Real.sqrt (g x))
  let w := fun x => Real.sqrt (f x) - Real.sqrt (g x)
  have hvm : AEStronglyMeasurable v μ := by
    fun_prop
  have hvBound : ∀ᵐ x ∂μ, v x ^ 2 ≤ 2 * (R + 1) * (u x ^ 2 * g x) := by
    filter_upwards [hRatio] with x hx
    have hs : (Real.sqrt (f x) + Real.sqrt (g x)) ^ 2 ≤
        2 * (R + 1) * g x := by
      nlinarith [Real.sq_sqrt (hf0 x), Real.sq_sqrt (hg0 x),
        sq_nonneg (Real.sqrt (f x) - Real.sqrt (g x))]
    have := mul_le_mul_of_nonneg_left hs (sq_nonneg (u x))
    dsimp [v]
    nlinarith only [this]
  have hvSq : Integrable (fun x => v x ^ 2) μ := by
    apply (hMoment.const_mul (2 * (R + 1))).mono' (hvm.pow 2)
    filter_upwards [hvBound] with x hx
    change ‖v x ^ 2‖ ≤ _
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (v x))] using hx
  have hv : MemLp v 2 μ := (memLp_two_iff_integrable_sq hvm).2 hvSq
  have hw : MemLp w 2 μ :=
    (Causalean.Stat.Minimax.sqrt_density_memLp μ f hf hf0).sub
      (Causalean.Stat.Minimax.sqrt_density_memLp μ g hg hg0)
  have hfact : (fun x => |u x| * |f x - g x|) = fun x => |v x| * |w x| := by
    funext x
    rw [← abs_mul, ← abs_mul]
    congr 1
    dsimp [v, w]
    have hsf := Real.sq_sqrt (hf0 x)
    have hsg := Real.sq_sqrt (hg0 x)
    calc
      u x * (f x - g x) = u x * (Real.sqrt (f x) ^ 2 - Real.sqrt (g x) ^ 2) := by
        rw [hsf, hsg]
      _ = _ := by ring
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun x => abs_nonneg (v x))
    (Filter.Eventually.of_forall fun x => abs_nonneg (w x))
    (by norm_num; exact hv.abs) (by norm_num; exact hw.abs)
  simp only [Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow] at hholder
  rw [hfact]
  have hsq := pow_le_pow_left₀
    (integral_nonneg fun x => mul_nonneg (abs_nonneg (v x)) (abs_nonneg (w x)))
    hholder 2
  rw [mul_pow, Real.sq_sqrt (integral_nonneg fun x => sq_nonneg (v x)),
    Real.sq_sqrt (integral_nonneg fun x => sq_nonneg (w x))] at hsq
  have henergy : (∫ x, v x ^ 2 ∂μ) ≤ 2 * (R + 1) * ∫ x, u x ^ 2 * g x ∂μ := by
    rw [← integral_const_mul]
    exact integral_mono_ae hvSq (hMoment.const_mul _) hvBound
  exact hsq.trans (mul_le_mul_of_nonneg_right henergy
    (integral_nonneg fun x => sq_nonneg (w x)))

/-- Suppose [R is nonnegative](hyp:hR), [u is measurable up to a null set](hyp:hu),
[for almost every instrument value, f and g are integrable and nonnegative,
f is at most R times g almost everywhere, and u squared times g is
integrable](hyp:hDensities), [the operator difference is measurable up to a
null set](hyp:hError), [the conditional g-weighted second moment is integrable
over instruments](hyp:hMoment), and [the conditional squared Hellinger distance
is integrable over instruments](hyp:hH). Then [the L1 norm of the operator
difference applied to u is at most the product of the square roots of 2(R+1),
the integrated g-weighted second moment, and the integrated squared Hellinger
distance](goal). -/
-- @node: rdiv_density_operator_relative_bound
lemma rdiv_density_operator_relative_bound {Z : Type*} [MeasurableSpace Z]
    (μ : Measure A) (ν : Measure Z) (f g : A → Z → ℝ) (u : A → ℝ) (R : ℝ)
    (hR : 0 ≤ R) (hu : AEStronglyMeasurable u μ)
    (hDensities : ∀ᵐ z ∂ν, Integrable (fun x => f x z) μ ∧
      Integrable (fun x => g x z) μ ∧
      (∀ x, 0 ≤ f x z) ∧ (∀ x, 0 ≤ g x z) ∧
      (∀ᵐ x ∂μ, f x z ≤ R * g x z) ∧
      Integrable (fun x => u x ^ 2 * g x z) μ)
    (hError : AEStronglyMeasurable (densityOperator μ f u - densityOperator μ g u) ν)
    (hMoment : Integrable (fun z => ∫ x, u x ^ 2 * g x z ∂μ) ν)
    (hH : Integrable (fun z => hellingerSqDensity μ (fun x => f x z) (fun x => g x z)) ν) :
    inputL1Norm ν (densityOperator μ f u - densityOperator μ g u) ≤
      Real.sqrt (2 * (R + 1)) *
        Real.sqrt (∫ z, ∫ x, u x ^ 2 * g x z ∂μ ∂ν) *
        Real.sqrt (∫ z, hellingerSqDensity μ (fun x => f x z) (fun x => g x z) ∂ν) := by
  let M := fun z => ∫ x, u x ^ 2 * g x z ∂μ
  let H := fun z => hellingerSqDensity μ (fun x => f x z) (fun x => g x z)
  let a := fun z => Real.sqrt (M z)
  let b := fun z => Real.sqrt (H z)
  have hM0 : ∀ᵐ z ∂ν, 0 ≤ M z := by
    filter_upwards [hDensities] with z hz
    exact integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hz.2.2.2.1 x)
  have hH0 : ∀ z, 0 ≤ H z := fun z =>
    integral_nonneg fun x => sq_nonneg _
  have ha : MemLp a 2 ν := by
    apply (memLp_two_iff_integrable_sq (by fun_prop : AEStronglyMeasurable a ν)).2
    apply hMoment.congr
    filter_upwards [hM0] with z hz
    exact (Real.sq_sqrt hz).symm
  have hb : MemLp b 2 ν := by
    apply (memLp_two_iff_integrable_sq (by fun_prop : AEStronglyMeasurable b ν)).2
    exact hH.congr (Filter.Eventually.of_forall fun z => (Real.sq_sqrt (hH0 z)).symm)
  have hab : Integrable (fun z => a z * b z) ν := ha.integrable_mul hb
  have hdom : ∀ᵐ z ∂ν,
      |(densityOperator μ f u - densityOperator μ g u) z| ≤
        Real.sqrt (2 * (R + 1)) * (a z * b z) := by
    filter_upwards [hDensities] with z hz
    have hMg : Integrable (fun x => u x ^ 2 * g x z) μ := hz.2.2.2.2.2
    have hMf : Integrable (fun x => u x ^ 2 * f x z) μ := by
      apply (hMg.const_mul R).mono' (hu.pow 2 |>.mul hz.1.aestronglyMeasurable)
      filter_upwards [hz.2.2.2.2.1] with x hx
      change ‖u x ^ 2 * f x z‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hz.2.2.1 x))]
      nlinarith only [mul_le_mul_of_nonneg_left hx (sq_nonneg (u x))]
    have hweighted (v : A → ℝ) (hv : Integrable v μ) (hv0 : ∀ x, 0 ≤ v x)
        (hMv : Integrable (fun x => u x ^ 2 * v x) μ) :
        Integrable (fun x => u x * v x) μ := by
      have hs : AEStronglyMeasurable (fun x => u x * Real.sqrt (v x)) μ := by
        fun_prop
      have hs2 : MemLp (fun x => u x * Real.sqrt (v x)) 2 μ := by
        apply (memLp_two_iff_integrable_sq hs).2
        apply hMv.congr
        filter_upwards [] with x
        rw [mul_pow, Real.sq_sqrt (hv0 x)]
      have hp := (Causalean.Stat.Minimax.sqrt_density_memLp μ v hv hv0).integrable_mul hs2
      apply hp.congr
      filter_upwards [] with x
      change Real.sqrt (v x) * (u x * Real.sqrt (v x)) = _
      calc
        _ = u x * (Real.sqrt (v x)) ^ 2 := by ring
        _ = _ := by rw [Real.sq_sqrt (hv0 x)]
    have huf := hweighted (fun x => f x z) hz.1 hz.2.2.1 hMf
    have hug := hweighted (fun x => g x z) hz.2.1 hz.2.2.2.1 hMg
    have hcs := rdiv_density_relative_hellinger_sq μ (fun x => f x z)
      (fun x => g x z) u R hz.1 hz.2.1 hz.2.2.1 hz.2.2.2.1 hu
      hz.2.2.2.2.1 hMg
    have hM : 0 ≤ M z := integral_nonneg fun x =>
      mul_nonneg (sq_nonneg _) (hz.2.2.2.1 x)
    have hsq : (Real.sqrt (2 * (R + 1)) * (a z * b z)) ^ 2 =
        2 * (R + 1) * M z * H z := by
      dsimp [a, b]
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity),
        Real.sq_sqrt hM, Real.sq_sqrt (hH0 z)]
      ring
    have hi : |(densityOperator μ f u - densityOperator μ g u) z| ≤
        ∫ x, |u x| * |f x z - g x z| ∂μ := by
      change |(∫ x, u x * f x z ∂μ) - ∫ x, u x * g x z ∂μ| ≤ _
      rw [← integral_sub huf hug]
      convert (abs_integral_le_integral_abs (f := fun x => u x * f x z - u x * g x z)) using 1
      congr 1
      funext x
      rw [← mul_sub, abs_mul]
    have hi0 : 0 ≤ ∫ x, |u x| * |f x z - g x z| ∂μ :=
      integral_nonneg fun x => mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hsqrt : 0 ≤ Real.sqrt (2 * (R + 1)) * (a z * b z) := by
      dsimp [a, b]; positivity
    nlinarith only [hi, hi0, hcs, hsq, hsqrt]
  have he : Integrable (fun z => |(densityOperator μ f u - densityOperator μ g u) z|) ν := by
    apply (hab.const_mul (Real.sqrt (2 * (R + 1)))).mono' (by fun_prop)
    filter_upwards [hdom] with z hz
    simpa only [Real.norm_eq_abs, abs_abs] using hz
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun z => Real.sqrt_nonneg (M z))
    (Filter.Eventually.of_forall fun z => Real.sqrt_nonneg (H z))
    (by norm_num; exact ha) (by norm_num; exact hb)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hcs
  have hia : (∫ z, a z ^ 2 ∂ν) = ∫ z, M z ∂ν := by
    apply integral_congr_ae
    filter_upwards [hM0] with z hz
    exact Real.sq_sqrt hz
  have hib : (∫ z, b z ^ 2 ∂ν) = ∫ z, H z ∂ν := by
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => Real.sq_sqrt (hH0 z))
  rw [hia, hib] at hcs
  calc
    _ ≤ ∫ z, Real.sqrt (2 * (R + 1)) * (a z * b z) ∂ν :=
      integral_mono_ae he (hab.const_mul _) hdom
    _ = Real.sqrt (2 * (R + 1)) * ∫ z, a z * b z ∂ν := integral_const_mul _ _
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcs (Real.sqrt_nonneg _)

/-- [The difference between the squared-loss contrast for predictions a and a′
and that for b and b′ equals minus the difference of their perturbations times
2y−a−a′, plus b−b′ times the sum of their perturbations](goal). -/
-- @node: rdiv_loss_perturbation_identity
lemma rdiv_loss_perturbation_identity (y a a' b b' : ℝ) :
    ((y - a) ^ 2 - (y - a') ^ 2) - ((y - b) ^ 2 - (y - b') ^ 2) =
      -((a - b) - (a' - b')) * (2 * y - a - a') +
        (b - b') * ((a - b) + (a' - b')) := by
  ring

/-- Suppose [y is square integrable](hyp:hy), [a is square integrable](hyp:ha),
[a′ is square integrable](hyp:ha'), [b is square integrable](hyp:hb), [b′ is
square integrable](hyp:hb'), [the absolute value of y is at most B almost
everywhere](hyp:hyB), [the absolute value of a is at most B almost
everywhere](hyp:haB), and [the absolute value of a′ is at most B almost
everywhere](hyp:ha'B). Then [the absolute change in the integrated squared-loss
contrast is at most four times B times the L1 norm of the difference of the
prediction perturbations, plus the L2 norm of b−b′ times the sum of the L2
norms of a−b and a′−b′](goal). -/
-- @node: rdiv_loss_perturbation_bound
lemma rdiv_loss_perturbation_bound (μ : Measure A) [IsFiniteMeasure μ]
    (y a a' b b' : A → ℝ) (B : ℝ)
    (hy : MemLp y 2 μ) (ha : MemLp a 2 μ) (ha' : MemLp a' 2 μ)
    (hb : MemLp b 2 μ) (hb' : MemLp b' 2 μ)
    (hyB : ∀ᵐ x ∂μ, |y x| ≤ B) (haB : ∀ᵐ x ∂μ, |a x| ≤ B)
    (ha'B : ∀ᵐ x ∂μ, |a' x| ≤ B) :
    |((∫ x, (y x - a x) ^ 2 ∂μ) - ∫ x, (y x - a' x) ^ 2 ∂μ) -
      ((∫ x, (y x - b x) ^ 2 ∂μ) - ∫ x, (y x - b' x) ^ 2 ∂μ)| ≤
      4 * B * inputL1Norm μ ((a - b) - (a' - b')) +
        inputL2Norm μ (b - b') * (inputL2Norm μ (a - b) + inputL2Norm μ (a' - b')) := by
  have hrel := (ha.sub hb).sub (ha'.sub hb')
  have hprod : Integrable (fun x => |(b - b') x| * |(a - b) x|) μ :=
    (hb.sub hb').abs.integrable_mul (ha.sub hb).abs
  have hprod' : Integrable (fun x => |(b - b') x| * |(a' - b') x|) μ :=
    (hb.sub hb').abs.integrable_mul (ha'.sub hb').abs
  have hlin : Integrable (fun x => |((a - b) - (a' - b')) x|) μ :=
    (hrel.integrable (by norm_num)).abs
  have hlin' : Integrable (fun x => 4 * B * |((a - b) - (a' - b')) x|) μ :=
    hlin.const_mul _
  have hsum : Integrable (fun x => 4 * B * |((a - b) - (a' - b')) x| +
      |(b - b') x| * |(a - b) x|) μ := hlin'.add hprod
  have hCS (f g : A → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
      (∫ x, |f x| * |g x| ∂μ) ≤ inputL2Norm μ f * inputL2Norm μ g := by
    have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall fun x => abs_nonneg (f x))
      (Filter.Eventually.of_forall fun x => abs_nonneg (g x))
      (by norm_num; exact hf.abs) (by norm_num; exact hg.abs)
    simpa only [Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow, inputL2Norm] using hh
  have hdom : ∀ᵐ x ∂μ,
      |((y x - a x) ^ 2 - (y x - a' x) ^ 2) -
        ((y x - b x) ^ 2 - (y x - b' x) ^ 2)| ≤
      4 * B * |((a - b) - (a' - b')) x| +
        |(b - b') x| * |(a - b) x| + |(b - b') x| * |(a' - b') x| := by
    filter_upwards [hyB, haB, ha'B] with x hyx hax ha'x
    have hcoef : |2 * y x - a x - a' x| ≤ 4 * B := by
      calc
        _ ≤ |2 * y x - a x| + |a' x| := abs_sub _ _
        _ ≤ (|2 * y x| + |a x|) + |a' x| := by
          linarith only [abs_sub (2 * y x) (a x)]
        _ ≤ 4 * B := by rw [abs_mul]; norm_num; linarith
    rw [rdiv_loss_perturbation_identity]
    calc
      _ ≤ |-((a x - b x) - (a' x - b' x)) * (2 * y x - a x - a' x)| +
          |(b x - b' x) * ((a x - b x) + (a' x - b' x))| := abs_add_le _ _
      _ ≤ 4 * B * |(a x - b x) - (a' x - b' x)| +
          |b x - b' x| * (|a x - b x| + |a' x - b' x|) := by
        simp only [abs_mul, abs_neg]
        exact add_le_add (by simpa [mul_comm] using
          mul_le_mul_of_nonneg_left hcoef (abs_nonneg ((a x - b x) - (a' x - b' x))))
          (mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _))
      _ = _ := by dsimp; ring
  have hya : Integrable (fun x => (y x - a x) ^ 2) μ := (hy.sub ha).integrable_sq
  have hya' : Integrable (fun x => (y x - a' x) ^ 2) μ := (hy.sub ha').integrable_sq
  have hyb : Integrable (fun x => (y x - b x) ^ 2) μ := (hy.sub hb).integrable_sq
  have hyb' : Integrable (fun x => (y x - b' x) ^ 2) μ := (hy.sub hb').integrable_sq
  have hdiff : Integrable (fun x => (y x - a x) ^ 2 - (y x - a' x) ^ 2) μ :=
    hya.sub hya'
  have hdiff' : Integrable (fun x => (y x - b x) ^ 2 - (y x - b' x) ^ 2) μ :=
    hyb.sub hyb'
  rw [← integral_sub hya hya', ← integral_sub hyb hyb',
    ← integral_sub hdiff hdiff']
  have hi := ((hya.sub hya').sub (hyb.sub hyb')).abs
  calc
    _ ≤ ∫ x, |((y x - a x) ^ 2 - (y x - a' x) ^ 2) -
        ((y x - b x) ^ 2 - (y x - b' x) ^ 2)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, 4 * B * |((a - b) - (a' - b')) x| +
        |(b - b') x| * |(a - b) x| + |(b - b') x| * |(a' - b') x| ∂μ :=
      integral_mono_ae hi (((hrel.integrable (by norm_num)).abs.const_mul _).add
        hprod |>.add hprod') hdom
    _ = 4 * B * inputL1Norm μ ((a - b) - (a' - b')) +
        (∫ x, |(b - b') x| * |(a - b) x| ∂μ) +
        ∫ x, |(b - b') x| * |(a' - b') x| ∂μ := by
      unfold inputL1Norm
      integral_linearity
    _ ≤ _ := by
      have h₁ := hCS (b - b') (a - b) (hb.sub hb') (ha.sub hb)
      have h₂ := hCS (b - b') (a' - b') (hb.sub hb') (ha'.sub hb')
      nlinarith only [h₁, h₂]

/-- If [the absolute value of u is at most B on the support](hyp:huB) and
[g vanishes outside that support](hyp:hg), [clipping u between −B and B leaves
its density-induced operator unchanged](goal). -/
-- @node: rdiv_density_operator_clip
lemma rdiv_density_operator_clip {Z : Type*}
    (μ : Measure A) (g : A → Z → ℝ) (u : A → ℝ) (B : ℝ)
    (support : Set (A × Z))
    (huB : ∀ p ∈ support, |u p.1| ≤ B)
    (hg : ∀ p ∉ support, g p.1 p.2 = 0) :
    densityOperator μ g (fun x => max (-B) (min B (u x))) =
      densityOperator μ g u := by
  funext z
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hs : (x, z) ∈ support
  · have hx := abs_le.mp (huB (x, z) hs)
    rw [min_eq_right hx.2, max_eq_right hx.1]
  · rw [hg (x, z) hs, mul_zero, mul_zero]

/-- Suppose [B is nonnegative](hyp:hB), [u is measurable](hyp:hu), [the absolute
value of u is at most B on the support](hyp:huB), [g vanishes outside the
support](hyp:hg), and, at the chosen instrument value, [g is integrable](hyp:hgz),
[nonnegative everywhere](hyp:hg0), and [integrates to one](hyp:hg1). Then
[the absolute value of the density-induced operator applied to u at that
instrument value is at most B](goal). -/
-- @node: rdiv_density_operator_support_bound
lemma rdiv_density_operator_support_bound {Z : Type*}
    (μ : Measure A) (g : A → Z → ℝ) (u : A → ℝ) (B : ℝ)
    (support : Set (A × Z)) (hB : 0 ≤ B) (hu : Measurable u)
    (huB : ∀ p ∈ support, |u p.1| ≤ B)
    (hg : ∀ p ∉ support, g p.1 p.2 = 0)
    (z : Z) (hgz : Integrable (fun x => g x z) μ)
    (hg0 : ∀ x, 0 ≤ g x z) (hg1 : ∫ x, g x z ∂μ = 1) :
    |densityOperator μ g u z| ≤ B := by
  let v := fun x => max (-B) (min B (u x))
  have hv : Measurable v := by fun_prop
  have hvB (x : A) : |v x| ≤ B := by
    apply abs_le.mpr
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hvg : Integrable (fun x => v x * g x z) μ := by
    apply (hgz.const_mul B).mono' (hv.aestronglyMeasurable.mul hgz.aestronglyMeasurable)
    filter_upwards [] with x
    simpa only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hg0 x)] using
      mul_le_mul_of_nonneg_right (hvB x) (hg0 x)
  rw [← rdiv_density_operator_clip μ g u B support huB hg]
  calc
    |∫ x, v x * g x z ∂μ| ≤ ∫ x, |v x * g x z| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x, B * g x z ∂μ := by
      apply integral_mono_ae hvg.abs (hgz.const_mul B)
      filter_upwards [] with x
      rw [abs_mul, abs_of_nonneg (hg0 x)]
      exact mul_le_mul_of_nonneg_right (hvB x) (hg0 x)
    _ = B := by rw [integral_const_mul, hg1, mul_one]

/-- Suppose [u is measurable](hyp:hu), [B is nonnegative](hyp:hB), [the absolute
value of u is at most B on the common support](hyp:huB), [f vanishes outside
the support](hyp:hf), [g vanishes outside the support](hyp:hg), [both are
integrable, nonnegative, normalized densities for almost every instrument
value](hyp:hDensities), [their operator difference is measurable up to a null
set](hyp:hError), and [their conditional squared Hellinger distance is integrable
over instruments](hyp:hH). Then [the L2 norm of the operator difference applied
to u is at most twice B times the square root of the integrated squared
Hellinger distance](goal). -/
-- @node: rdiv_density_operator_global_support_bound
lemma rdiv_density_operator_global_support_bound {Z : Type*} [MeasurableSpace Z]
    (μ : Measure A) (ν : Measure Z) (f g : A → Z → ℝ) (u : A → ℝ) (B : ℝ)
    (support : Set (A × Z)) (hu : Measurable u) (hB : 0 ≤ B)
    (huB : ∀ p ∈ support, |u p.1| ≤ B)
    (hf : ∀ p ∉ support, f p.1 p.2 = 0)
    (hg : ∀ p ∉ support, g p.1 p.2 = 0)
    (hDensities : ∀ᵐ z ∂ν, Integrable (fun x => f x z) μ ∧
      Integrable (fun x => g x z) μ ∧
      (∀ x, 0 ≤ f x z) ∧ (∀ x, 0 ≤ g x z) ∧
      (∫ x, f x z ∂μ) = 1 ∧ (∫ x, g x z ∂μ) = 1)
    (hError : AEStronglyMeasurable (densityOperator μ f u - densityOperator μ g u) ν)
    (hH : Integrable (fun z => hellingerSqDensity μ (fun x => f x z) (fun x => g x z)) ν) :
    inputL2Norm ν (densityOperator μ f u - densityOperator μ g u) ≤
      2 * B * Real.sqrt (∫ z, hellingerSqDensity μ (fun x => f x z) (fun x => g x z) ∂ν) := by
  let v := fun x => max (-B) (min B (u x))
  have hv : Measurable v := by fun_prop
  have hvB : ∀ᵐ x ∂μ, |v x| ≤ B := by
    filter_upwards [] with x
    apply abs_le.mpr
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hfv : densityOperator μ f v = densityOperator μ f u :=
    rdiv_density_operator_clip μ f u B support huB hf
  have hgv : densityOperator μ g v = densityOperator μ g u :=
    rdiv_density_operator_clip μ g u B support huB hg
  have hev : AEStronglyMeasurable (densityOperator μ f v - densityOperator μ g v) ν := by
    rw [hfv, hgv]
    exact hError
  have hbound := rdiv_density_operator_global_bound μ ν f g v B
    hv.aestronglyMeasurable hB hvB hDensities hev hH
  simpa only [hfv, hgv] using hbound

/-- Suppose [the conditional-density class is realizable](hyp:hDensity), [it has
common-support bounds c₀ and CG](hyp:hBounds), [the hypothesis class is bounded
in absolute value by B on that support](hyp:hHyp), [B is nonnegative](hyp:hB),
[g belongs to the density class](hyp:hg), and [a candidate h in the closed
linear hypothesis space](hyp:h) [belongs to the hypothesis class](hyp:hh).
If [the operator difference applied to h is measurable up to
a null set under the instrument distribution](hyp:hError) and [the conditional
squared Hellinger distance between g and the true density is integrable under
that distribution](hyp:hH), [the L2 operator error for h is at most twice B
times the square root of the integrated squared Hellinger distance](goal). -/
-- @node: rdiv_hypothesis_operator_global_bound
lemma rdiv_hypothesis_operator_global_bound {𝒲 Z : Type*}
    [MeasurableSpace 𝒲] [MeasurableSpace Z] (V : IVWorld 𝒲 A Z)
    (μ : Measure A) (G : Set (A → Z → ℝ)) (g₀ g : A → Z → ℝ)
    (support : Set (A × Z)) (B c₀ CG : ℝ)
    (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hHyp : HypothesisClassBounded V support B) (hB : 0 ≤ B)
    (hg : g ∈ G) (h : V.Hbar.toSubmodule) (hh : h ∈ V.H)
    (hError : AEStronglyMeasurable
      (densityOperator μ g (primalVersion V h) - densityOperator μ g₀ (primalVersion V h))
      (V.law.map V.zOf))
    (hH : Integrable (fun z => hellingerSqDensity μ (fun x => g x z) (fun x => g₀ x z))
      (V.law.map V.zOf)) :
    inputL2Norm (V.law.map V.zOf)
      (densityOperator μ g (primalVersion V h) - densityOperator μ g₀ (primalVersion V h)) ≤
      2 * B * Real.sqrt (∫ z, hellingerSqDensity μ (fun x => g x z) (fun x => g₀ x z)
        ∂V.law.map V.zOf) := by
  apply rdiv_density_operator_global_support_bound μ (V.law.map V.zOf)
    g g₀ (primalVersion V h) B support (V.primal_measurable h) hB
    (hHyp h hh) (hBounds.2.2.2.2 g hg) (hBounds.2.2.2.2 g₀ hDensity.1)
    ?_ hError hH
  filter_upwards [rdiv_density_integrable_of_realizable V μ G g₀ g hDensity hg,
    rdiv_density_integrable_of_realizable V μ G g₀ g₀ hDensity hDensity.1,
    (hDensity.2 g hg).2.2, (hDensity.2 g₀ hDensity.1).2.2] with z hgz hg₀z hgn hg₀n
  exact ⟨hgz, hg₀z, (fun x => (hDensity.2 g hg).2.1 x z),
    (fun x => (hDensity.2 g₀ hDensity.1).2.1 x z), hgn, hg₀n⟩

end Papers.TsAdaptiveEstimationInference
