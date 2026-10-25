module
public import Papers.TsAdaptiveEstimationInference.Helpers.SpectralRegularization
public import Papers.TsAdaptiveEstimationInference.Helpers.SpectralTransfer
public import Toolkit.Foundations.Analysis.SpecialFunctions.TikhonovFilter
/-! Iterated population residual identities, qualification bounds, and source interpolation. -/
public section
set_option linter.style.longLine false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory
open Causalean.Estimation.NPIV.Complexification
open scoped InnerProductSpace
attribute [local instance 2000] instAlgebraRealLpCLM
variable {𝒲 𝒳 𝒵 : Type*} [MeasurableSpace 𝒲]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒵] (V : IVWorld 𝒲 𝒳 𝒵)

-- @node: ambientNormalOp_commute_projection
/-- [The ambient normal operator commutes with orthogonal projection onto the closed primal space](goal). -/
lemma ambientNormalOp_commute_projection :
    Commute (ambientNormalOp V) V.Hbar.toSubmodule.starProjection := by
  apply ContinuousLinearMap.ext
  intro u
  change ((normalOp V) (V.Hbar.toSubmodule.orthogonalProjectionOnto
    (V.Hbar.toSubmodule.orthogonalProjectionOnto u : Lp ℝ 2 V.law)) : Lp ℝ 2 V.law) =
    (V.Hbar.toSubmodule.orthogonalProjectionOnto
      (normalOp V (V.Hbar.toSubmodule.orthogonalProjectionOnto u) : Lp ℝ 2 V.law) : Lp ℝ 2 V.law)
  simp only [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

-- @node: spectralOp_coe
/-- If [the real spectral weight is continuous](hyp:hf), [applying its spectral operator to a vector in the closed primal space agrees, in the ambient square-integrable space, with applying the real continuous functional calculus of the ambient normal operator](goal). -/
lemma spectralOp_coe (f : ℝ → ℝ) (hf : Continuous f) (u : V.Hbar.toSubmodule) :
    (spectralOp V f u : Lp ℝ 2 V.law) = realCFC (ambientNormalOp V) f u := by
  have hc := realCFC_commute (ambientNormalOp V) V.Hbar.toSubmodule.starProjection
    (ambientNormalOp_isPositive V).isSelfAdjoint (ambientNormalOp_commute_projection V) f hf
  have he := congrArg (fun T : Lp ℝ 2 V.law →L[ℝ] Lp ℝ 2 V.law =>
    T (u : Lp ℝ 2 V.law)) hc.eq
  simpa only [spectralOp, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    ContinuousLinearMap.mul_apply, Submodule.starProjection_apply,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self] using he.symm

-- @node: spectralOp_mul
/-- If [the first spectral weight is continuous](hyp:hf) and [the second spectral weight is continuous](hyp:hg), [the spectral operator of their pointwise product equals the composition of their spectral operators](goal). -/
lemma spectralOp_mul (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    spectralOp V (fun x => f x * g x) = spectralOp V f * spectralOp V g := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  change (spectralOp V (fun x => f x * g x) u : Lp ℝ 2 V.law) =
    (spectralOp V f (spectralOp V g u) : Lp ℝ 2 V.law)
  rw [spectralOp_coe V (fun x => f x * g x) (by fun_prop), spectralOp_coe V _ hf, spectralOp_coe V _ hg]
  rw [realCFC_mul _ (ambientNormalOp_isPositive V).isSelfAdjoint _ _ hf hg]
  rfl

-- @node: spectralOp_one
/-- [The constant unit spectral weight gives the identity operator on the closed primal space](goal). -/
lemma spectralOp_one : spectralOp V (fun _ => 1) = 1 := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  rw [spectralOp_coe V _ continuous_const, realCFC_one_apply _
    (ambientNormalOp_isPositive V).isSelfAdjoint]
  rfl

-- @node: spectralOp_congr
/-- If [two spectral weights agree at every point in the spectrum of the ambient normal operator](hyp:hfg), [their spectral operators on the closed primal space are equal](goal). -/
lemma spectralOp_congr (f g : ℝ → ℝ)
    (hfg : ∀ x ∈ spectrum ℝ (ambientNormalOp V), f x = g x) :
    spectralOp V f = spectralOp V g := by
  unfold spectralOp
  rw [realCFC_congr_spectrum _ (ambientNormalOp_isPositive V).isSelfAdjoint f g hfg]

-- @node: spectralOp_const
/-- [A constant spectral weight gives that constant times the identity operator on the closed primal space](goal). -/
lemma spectralOp_const (c : ℝ) : spectralOp V (fun _ => c) = c • 1 := by
  apply ContinuousLinearMap.ext
  intro u
  change V.Hbar.toSubmodule.orthogonalProjectionOnto
    (reLp (cfc (fun _ : ℂ => (c : ℂ)) (complexLift (ambientNormalOp V)) (ιLp u))) = _
  rw [cfc_const _ _ (complexLift_isSelfAdjoint (ambientNormalOp_isPositive V).isSelfAdjoint).isStarNormal]
  change V.Hbar.toSubmodule.orthogonalProjectionOnto (reLp ((c : ℂ) • ιLp u)) = c • u
  rw [reLp_ofReal_smul, reLp_comp_ιLp, map_smul,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

-- @node: residualFilter_safe
/-- For [a positive penalty](hyp:hlam), [the residual filter is the spectral operator with weight equal to the penalty divided by the sum of the penalty and the nonnegative part of the spectral value](goal). -/
lemma residualFilter_safe (lam : ℝ) (hlam : 0 < lam) :
    residualFilter V lam = spectralOp V (fun x => lam / (max x 0 + lam)) := by
  apply spectralOp_congr
  intro x hx
  rw [max_eq_left (ambientNormalOp_spectrum V x hx).1]

-- @node: residualFilter_eq_smul_resolvent
/-- For [a positive penalty](hyp:hlam), [the residual filter equals the penalty times the resolvent](goal). -/
lemma residualFilter_eq_smul_resolvent (lam : ℝ) (hlam : 0 < lam) :
    residualFilter V lam = lam • resolvent V lam := by
  have hf : Continuous (fun x : ℝ => (max x 0 + lam)⁻¹) := by
    fun_prop (disch := intro x; positivity)
  have hr : resolvent V lam = spectralOp V (fun x => (max x 0 + lam)⁻¹) := by
    apply spectralOp_congr
    intro x hx
    rw [max_eq_left (ambientNormalOp_spectrum V x hx).1]
  rw [residualFilter_safe V lam hlam, hr]
  have hm := spectralOp_mul V (fun _ => lam) (fun x => (max x 0 + lam)⁻¹)
    continuous_const hf
  rw [spectralOp_const] at hm
  simpa only [div_eq_mul_inv, Algebra.smul_mul_assoc, one_mul] using hm

-- @node: shiftedNormal_injective
/-- For [a positive penalty](hyp:hlam), [adding the penalty times the identity to the normal operator gives an injective map on the closed primal space](goal). -/
lemma shiftedNormal_injective (lam : ℝ) (hlam : 0 < lam) :
    Function.Injective (fun u : V.Hbar.toSubmodule => normalOp V u + lam • u) := by
  intro u v huv
  have he : normalOp V (u - v) + lam • (u - v) = 0 := by
    rw [map_sub, smul_sub]
    change normalOp V u + lam • u = normalOp V v + lam • v at huv
    rw [sub_add_sub_comm, sub_eq_zero]
    exact huv
  have hi := congrArg (fun z => inner ℝ z (u - v)) he
  simp only [inner_add_left, real_inner_smul_left, inner_zero_left,
    normalOp, adjointOp, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq] at hi
  have hs : ‖u - v‖ ^ 2 ≤ 0 := by
    apply (mul_le_mul_iff_right₀ hlam).mp
    nlinarith [sq_nonneg (‖projCondExpOp V (u - v)‖)]
  have hz : ‖u - v‖ = 0 := by nlinarith [norm_nonneg (u - v)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

-- @node: populationIterate_residual_identity
/-- Under [the range condition](hyp:hRange), for [a positive penalty](hyp:hlam), [the minimum-norm solution minus the population iterate equals the residual filter raised to the iteration count and applied to the minimum-norm solution](goal). -/
lemma populationIterate_residual_identity (hRange : RangeCondition V)
    (lam : ℝ) (hlam : 0 < lam) (j : ℕ) :
    minNormSolution V - populationIterate V lam j =
      (residualFilter V lam ^ j) (minNormSolution V) := by
  induction j with
  | zero => simp [populationIterate]
  | succ j ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, ← ih]
    apply shiftedNormal_injective V lam hlam
    have hn := resolvent_normalEquation V lam hlam
      (adjointOp V (momentRepresenter V) + lam • populationIterate V lam j)
    have hr := resolvent_normalEquation V lam hlam
      (minNormSolution V - populationIterate V lam j)
    rw [residualFilter_eq_smul_resolvent V lam hlam]
    simp only [ContinuousLinearMap.smul_apply, map_smul]
    rw [← smul_add, hr]
    simp only [map_sub, smul_sub]
    change normalOp V (minNormSolution V) - normalOp V (populationIterate V lam (j + 1)) +
      (lam • minNormSolution V - lam • populationIterate V lam (j + 1)) = _
    have hsol := (minNormSolution_spec V hRange).1
    have ha : normalOp V (minNormSolution V) = adjointOp V (momentRepresenter V) := by
      change adjointOp V (projCondExpOp V (minNormSolution V)) = _
      rw [hsol]
    rw [ha]
    change normalOp V (populationIterate V lam (j + 1)) +
      lam • populationIterate V lam (j + 1) = _ at hn
    rw [eq_sub_of_add_eq hn]
    abel

-- @node: residualFilter_pow_symbol
/-- For [a positive penalty](hyp:hlam), [any nonnegative integer power of the residual filter equals the spectral operator whose weight is the same power of the penalty divided by the sum of the penalty and the nonnegative part of the spectral value](goal). -/
lemma residualFilter_pow_symbol (lam : ℝ) (hlam : 0 < lam) (j : ℕ) :
    residualFilter V lam ^ j = spectralOp V (fun x => (lam / (max x 0 + lam)) ^ j) := by
  have hc : Continuous (fun x : ℝ => lam / (max x 0 + lam)) := by
    fun_prop (disch := intro x; positivity)
  induction j with
  | zero => simpa using (spectralOp_one V).symm
  | succ j ih =>
    rw [pow_succ, ih, residualFilter_safe V lam hlam, ← spectralOp_mul V (fun x => (lam / (max x 0 + lam)) ^ j)
      (fun x => lam / (max x 0 + lam)) (by fun_prop) hc]
    congr 1

-- @node: residualFilter_source_commute
/-- If [the minimum-norm solution satisfies the beta source condition with source vector w₀](hyp:hSource) and [the penalty is positive](hyp:hlam), [applying a power of the residual filter to the solution equals applying the spectral source power to the correspondingly filtered source vector](goal). -/
lemma residualFilter_source_commute (β : ℝ) (w₀ : V.Hbar.toSubmodule)
    (hSource : BetaSourceCondition V β w₀) (lam : ℝ) (hlam : 0 < lam) (j : ℕ) :
    (residualFilter V lam ^ j) (minNormSolution V) =
      spectralOp V (fun x => (max x 0) ^ (β / 2)) ((residualFilter V lam ^ j) w₀) := by
  have hp : Continuous (fun x : ℝ => (max x 0) ^ (β / 2)) := by
    fun_prop (disch := linarith [hSource.1])
  have hr : Continuous (fun x : ℝ => (lam / (max x 0 + lam)) ^ j) := by
    fun_prop (disch := intro x; positivity)
  rw [hSource.2, residualFilter_pow_symbol V lam hlam j]
  change (spectralOp V (fun x => (lam / (max x 0 + lam)) ^ j) *
      spectralOp V (fun x => (max x 0) ^ (β / 2))) w₀ =
    (spectralOp V (fun x => (max x 0) ^ (β / 2)) *
      spectralOp V (fun x => (lam / (max x 0 + lam)) ^ j)) w₀
  rw [← spectralOp_mul V (fun x => (lam / (max x 0 + lam)) ^ j)
    (fun x => (max x 0) ^ (β / 2)) hr hp,
    ← spectralOp_mul V (fun x => (max x 0) ^ (β / 2))
      (fun x => (lam / (max x 0 + lam)) ^ j) hp hr]
  have he : (fun x : ℝ => (lam / (max x 0 + lam)) ^ j * (max x 0) ^ (β / 2)) =
      (fun x : ℝ => (max x 0) ^ (β / 2) * (lam / (max x 0 + lam)) ^ j) := by
    funext x
    exact mul_comm _ _
  rw [he]

-- @node: residualFilter_pow_norm_le
/-- For [a positive penalty](hyp:hlam), [every nonnegative integer power of the residual filter weakly decreases the norm of every vector in the closed primal space](goal). -/
lemma residualFilter_pow_norm_le (lam : ℝ) (hlam : 0 < lam) (j : ℕ)
    (u : V.Hbar.toSubmodule) : ‖(residualFilter V lam ^ j) u‖ ≤ ‖u‖ := by
  rw [residualFilter_pow_symbol V lam hlam j, ← Submodule.norm_coe,
    spectralOp_coe V _ (by fun_prop (disch := intro x; positivity))]
  have hb := realCFC_norm_le (ambientNormalOp V) (ambientNormalOp_isPositive V).isSelfAdjoint
    (fun x => (lam / (max x 0 + lam)) ^ j) (by fun_prop (disch := intro x; positivity))
    1 zero_le_one (fun x hx => ?_) (u : Lp ℝ 2 V.law)
  · simpa only [one_mul, Submodule.norm_coe] using hb
  · rw [abs_of_nonneg (by positivity)]
    exact pow_le_one₀ (by positivity) ((div_le_one (by positivity)).mpr (by
      have := le_max_right x 0
      linarith))

-- @node: spectralOp_image_norm_sq
/-- For [a continuous spectral weight](hyp:hf), [the squared norm of the conditional-expectation image of a spectrally transformed vector equals its quadratic form under the ambient spectral operator with weight equal to the spectral value times the square of the original weight](goal). -/
lemma spectralOp_image_norm_sq (f : ℝ → ℝ) (hf : Continuous f) (u : V.Hbar.toSubmodule) :
    ‖projCondExpOp V (spectralOp V f u)‖ ^ 2 =
      inner ℝ (realCFC (ambientNormalOp V) (fun x => x * (f x * f x)) u)
        (u : Lp ℝ 2 V.law) := by
  have hA := (ambientNormalOp_isPositive V).isSelfAdjoint
  rw [← ambientNormalOp_inner V, spectralOp_coe V f hf]
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (realCFC_isSelfAdjoint (ambientNormalOp V) hA f hf)
  have h1 : realCFC (ambientNormalOp V) (fun x => x * f x) u =
      ambientNormalOp V (realCFC (ambientNormalOp V) f u) := by
    have hm := congrArg (fun T : Lp ℝ 2 V.law →L[ℝ] Lp ℝ 2 V.law => T u)
      (realCFC_mul (ambientNormalOp V) hA id f continuous_id hf)
    simpa only [id_eq, ContinuousLinearMap.comp_apply, realCFC_id _ hA] using hm
  have h2 : realCFC (ambientNormalOp V) (fun x => f x * (x * f x)) u =
      realCFC (ambientNormalOp V) f (ambientNormalOp V (realCFC (ambientNormalOp V) f u)) := by
    rw [realCFC_mul _ hA f (fun x => x * f x) hf (by fun_prop),
      ContinuousLinearMap.comp_apply, h1]
  have he := hs (ambientNormalOp V (realCFC (ambientNormalOp V) f u)) (u : Lp ℝ 2 V.law)
  change inner ℝ (realCFC (ambientNormalOp V) f
    (ambientNormalOp V (realCFC (ambientNormalOp V) f u))) (u : Lp ℝ 2 V.law) =
      inner ℝ (ambientNormalOp V (realCFC (ambientNormalOp V) f u))
        (realCFC (ambientNormalOp V) f u) at he
  rw [← he, ← h2]
  congr 3
  funext x
  ring

-- @node: realCFC_inner_le_const
/-- If [a spectral weight is continuous](hyp:hf) and [is bounded above by c on the spectrum of the ambient normal operator](hyp:hb), [its spectral quadratic form at any vector in the closed primal space is at most c times that vector's squared norm](goal). -/
lemma realCFC_inner_le_const (f : ℝ → ℝ) (hf : Continuous f) (c : ℝ)
    (hb : ∀ x ∈ spectrum ℝ (ambientNormalOp V), f x ≤ c) (u : V.Hbar.toSubmodule) :
    inner ℝ (realCFC (ambientNormalOp V) f u) (u : Lp ℝ 2 V.law) ≤ c * ‖u‖ ^ 2 := by
  have hA := (ambientNormalOp_isPositive V).isSelfAdjoint
  have hi := realCFC_inner_mono_real (ambientNormalOp V) hA f (fun _ => c) hf
    continuous_const hb (u : Lp ℝ 2 V.law)
  have he : realCFC (ambientNormalOp V) (fun _ => c) u = c • (u : Lp ℝ 2 V.law) := by
    rw [← spectralOp_coe V _ continuous_const, spectralOp_const]
    rfl
  simpa only [he, real_inner_smul_left, real_inner_self_eq_norm_sq, Submodule.norm_coe] using hi

-- @node: sourceResidual_symbol_sq
/-- For [a nonnegative spectral value x](hyp:hx) and [a positive source exponent β](hyp:hβ), [the square of x to the power β/2 times q to the iteration count equals x to the power β times q to twice that count](goal). -/
lemma sourceResidual_symbol_sq {x β q : ℝ} (hx : 0 ≤ x) (hβ : 0 < β) (j : ℕ) :
    (x ^ (β / 2) * q ^ j) * (x ^ (β / 2) * q ^ j) = x ^ β * q ^ (2 * j) := by
  calc
    _ = (x ^ (β / 2) * x ^ (β / 2)) * (q ^ j * q ^ j) := by ring
    _ = x ^ β * q ^ (2 * j) := by
      rw [← Real.rpow_add_of_nonneg hx (by linarith) (by linarith), ← pow_add]
      congr 1 <;> congr 1 <;> ring

-- @node: iteratedSource_bounds
/-- For [a positive source exponent β](hyp:hβ) and [a positive penalty λ](hyp:hlam), form a vector by applying the source weight and j residual-filter factors to u. [Its squared norm is at most the squared norm of u times λ to the minimum of β and 2j, and its conditional-expectation image has squared norm at most the squared norm of u times λ to the minimum of β+1 and 2j](goal). -/
lemma iteratedSource_bounds (β : ℝ) (hβ : 0 < β) (lam : ℝ) (hlam : 0 < lam)
    (j : ℕ) (u : V.Hbar.toSubmodule) :
    let v := spectralOp V (fun x => (max x 0) ^ (β / 2) *
      (lam / (max x 0 + lam)) ^ j) u
    ‖v‖ ^ 2 ≤ ‖u‖ ^ 2 * lam ^ min β (2 * (j : ℝ)) ∧
      ‖projCondExpOp V v‖ ^ 2 ≤ ‖u‖ ^ 2 * lam ^ min (β + 1) (2 * (j : ℝ)) := by
  dsimp only
  let f := fun x : ℝ => (max x 0) ^ (β / 2) * (lam / (max x 0 + lam)) ^ j
  have hf : Continuous f := by fun_prop (disch := first | positivity | (intro x; positivity))
  have hsq (x : ℝ) : f x * f x = (max x 0) ^ β * (lam / (max x 0 + lam)) ^ (2 * j) :=
    sourceResidual_symbol_sq (le_max_right x 0) hβ j
  constructor
  · rw [← Submodule.norm_coe, spectralOp_coe V f hf,
      realCFC_norm_sq _ (ambientNormalOp_isPositive V).isSelfAdjoint f hf]
    have hi := realCFC_inner_le_const V (fun x => f x * f x) (by fun_prop)
      (lam ^ min β (2 * (j : ℝ))) (fun x hx => ?_) u
    · simpa only [mul_comm] using hi
    · rw [hsq, max_eq_left (ambientNormalOp_spectrum V x hx).1]
      exact Toolkit.Foundations.Analysis.SpecialFunctions.rpow_mul_div_add_pow_le_rpow_min (ambientNormalOp_spectrum V x hx) hlam hβ j
  · rw [spectralOp_image_norm_sq V f hf]
    have hi := realCFC_inner_le_const V (fun x => x * (f x * f x)) (by fun_prop)
      (lam ^ min (β + 1) (2 * (j : ℝ))) (fun x hx => ?_) u
    · simpa only [mul_comm] using hi
    · have hx0 := (ambientNormalOp_spectrum V x hx).1
      rw [hsq, max_eq_left hx0, ← mul_assoc]
      have he : x * x ^ β = x ^ (β + 1) := by
        rw [Real.rpow_add_of_nonneg hx0 hβ.le zero_le_one, Real.rpow_one, mul_comm]
      rw [he]
      exact Toolkit.Foundations.Analysis.SpecialFunctions.rpow_mul_div_add_pow_le_rpow_min (ambientNormalOp_spectrum V x hx) hlam (by linarith) j

-- @node: spectralSource_image_moment
/-- For [a positive source exponent β](hyp:hβ), [the squared conditional-expectation image norm of the spectral source transform of u equals the quadratic form at u with spectral weight given by the nonnegative part of the spectral value raised to β+1](goal). -/
lemma spectralSource_image_moment (β : ℝ) (hβ : 0 < β) (u : V.Hbar.toSubmodule) :
    ‖projCondExpOp V (spectralOp V (fun x => (max x 0) ^ (β / 2)) u)‖ ^ 2 =
      inner ℝ (realCFC (ambientNormalOp V) (fun x => (max x 0) ^ (β + 1)) u)
        (u : Lp ℝ 2 V.law) := by
  rw [spectralOp_image_norm_sq V _ (by fun_prop (disch := positivity))]
  have he := realCFC_congr_spectrum (ambientNormalOp V) (ambientNormalOp_isPositive V).isSelfAdjoint
    (fun x => x * ((max x 0) ^ (β / 2) * (max x 0) ^ (β / 2)))
    (fun x => (max x 0) ^ (β + 1)) (fun x hx => ?_)
  · rw [he]
  · have hx0 := (ambientNormalOp_spectrum V x hx).1
    rw [max_eq_left hx0, ← Real.rpow_add_of_nonneg hx0 (by positivity) (by positivity)]
    rw [show β / 2 + β / 2 = β by ring,
      Real.rpow_add_of_nonneg hx0 hβ.le zero_le_one, Real.rpow_one, mul_comm]

-- @node: spectralSource_interpolation
/-- For [a positive source exponent β](hyp:hβ), let v be the spectral source transform of u with exponent β/2. [The squared norm of v is at most the norm of u to the power 2/(β+1) times the conditional-expectation image norm of v to the power 2β/(β+1)](goal). -/
lemma spectralSource_interpolation (β : ℝ) (hβ : 0 < β) (u : V.Hbar.toSubmodule) :
    let v := spectralOp V (fun x => (max x 0) ^ (β / 2)) u
    ‖v‖ ^ 2 ≤ ‖u‖ ^ (2 / (β + 1)) * ‖projCondExpOp V v‖ ^ (2 * β / (β + 1)) := by
  dsimp only
  have hA := (ambientNormalOp_isPositive V).isSelfAdjoint
  have hf : Continuous (fun x : ℝ => (max x 0) ^ (β + 1)) := by
    fun_prop (disch := positivity)
  have hθ : β / (β + 1) ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · positivity
    · exact (div_lt_one (by positivity)).mpr (by linarith)
  have hh := realCFC_inner_holder (ambientNormalOp V) hA
    (fun x => (max x 0) ^ (β + 1)) (fun _ => 1) hf continuous_const
    (fun x _ => Real.rpow_nonneg (le_max_right x 0) _) (fun _ _ => zero_le_one) hθ
    (u : Lp ℝ 2 V.law)
  have he : (fun x : ℝ => (max ((max x 0) ^ (β + 1)) 0) ^ (β / (β + 1)) *
      (max (1 : ℝ) 0) ^ (1 - β / (β + 1))) = (fun x => (max x 0) ^ β) := by
    funext x
    rw [max_eq_left (Real.rpow_nonneg (le_max_right x 0) _), max_eq_left zero_le_one,
      Real.one_rpow, mul_one, ← Real.rpow_mul (le_max_right x 0)]
    congr 1
    field_simp
  rw [he, realCFC_one_apply _ hA, real_inner_self_eq_norm_sq,
    ← spectralSource_image_moment V β hβ u, Submodule.norm_coe] at hh
  have hn : ‖spectralOp V (fun x => (max x 0) ^ (β / 2)) u‖ ^ 2 =
      inner ℝ (realCFC (ambientNormalOp V) (fun x => (max x 0) ^ β) u)
        (u : Lp ℝ 2 V.law) := by
    rw [← Submodule.norm_coe, spectralOp_coe V _ (by fun_prop (disch := positivity)),
      realCFC_power_norm_sq _ hA hβ.le]
  rw [hn]
  refine hh.trans_eq ?_
  have hp (a : ℝ) (ha : 0 ≤ a) (b : ℝ) : (a ^ 2) ^ b = a ^ ((2 : ℝ) * b) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
    norm_num
  rw [hp _ (norm_nonneg _) _, hp _ (norm_nonneg _) _, mul_comm]
  congr 1
  · congr 1
    field_simp
    <;> ring
  · congr 1
    ring

/-- Under [the range condition](hyp:hRange) and [the beta source condition with source vector w₀](hyp:hSource), for [a positive penalty λ](hyp:hlam), [the squared conditional-expectation image norm of the population iteration error is at most the squared norm of w₀ times λ to the qualification exponent, the minimum of β+1 and twice the iteration count](goal). -/
lemma iter_bias_projected_le (β : ℝ) (w₀ : V.Hbar.toSubmodule)
    (hRange : RangeCondition V) (hSource : BetaSourceCondition V β w₀)
    (lam : ℝ) (hlam : 0 < lam) (j : ℕ) :
    ‖projCondExpOp V (populationIterate V lam j - minNormSolution V)‖ ^ 2 ≤
      ‖w₀‖ ^ 2 * lam ^ qualificationExponent β j := by
  have hi := populationIterate_residual_identity V hRange lam hlam j
  have hc := residualFilter_source_commute V β w₀ hSource lam hlam j
  have hp : Continuous (fun x : ℝ => (max x 0) ^ (β / 2)) := by
    fun_prop (disch := linarith [hSource.1])
  have hr : Continuous (fun x : ℝ => (lam / (max x 0 + lam)) ^ j) := by
    fun_prop (disch := intro x; positivity)
  have hprod : spectralOp V (fun x => (max x 0) ^ (β / 2))
      ((residualFilter V lam ^ j) w₀) =
      spectralOp V (fun x => (max x 0) ^ (β / 2) *
        (lam / (max x 0 + lam)) ^ j) w₀ := by
    rw [residualFilter_pow_symbol V lam hlam j]
    change (spectralOp V (fun x => (max x 0) ^ (β / 2)) *
      spectralOp V (fun x => (lam / (max x 0 + lam)) ^ j)) w₀ = _
    rw [← spectralOp_mul V _ _ hp hr]
  have he : populationIterate V lam j - minNormSolution V =
      -(spectralOp V (fun x => (max x 0) ^ (β / 2)) ((residualFilter V lam ^ j) w₀)) := by
    rw [← hc, ← hi, neg_sub]
  have hb := iteratedSource_bounds V β hSource.1 lam hlam j w₀
  simpa only [he, hprod, map_neg, norm_neg, qualificationExponent] using hb.2

-- @node: lem:iter-bias
/-- Under [the range condition](hyp:hRange) and [the beta source condition with source vector w₀](hyp:hSource), with [at least one iteration](hyp:hj), [there is a positive constant, uniform over positive penalties, such that the population bias is the iterated residual applied to the minimum-norm solution and also the source transform of the filtered source vector; its squared norm and squared image norm are bounded by that constant times the squared source norm times the penalty to the respective exponents min(β, 2j) and min(β+1, 2j), the filtered source norm does not exceed the source norm, and the squared bias obeys source interpolation with exponents 2/(β+1) and 2β/(β+1)](goal). -/
lemma iter_bias (β : ℝ) (w₀ : V.Hbar.toSubmodule)
    (hRange : RangeCondition V) (hSource : BetaSourceCondition V β w₀)
    (j : ℕ) (hj : 1 ≤ j) :
    ∃ C > 0, ∀ lam : ℝ, 0 < lam →
      minNormSolution V - populationIterate V lam j =
        (residualFilter V lam ^ j) (minNormSolution V) ∧
      (residualFilter V lam ^ j) (minNormSolution V) =
        spectralOp V (fun x => (max x 0) ^ (β / 2)) ((residualFilter V lam ^ j) w₀) ∧
      ‖populationIterate V lam j - minNormSolution V‖ ^ 2 ≤
        C * ‖w₀‖ ^ 2 * lam ^ min β (2 * (j : ℝ)) ∧
      ‖projCondExpOp V (populationIterate V lam j - minNormSolution V)‖ ^ 2 ≤
        C * ‖w₀‖ ^ 2 * lam ^ min (β + 1) (2 * (j : ℝ)) ∧
      ‖(residualFilter V lam ^ j) w₀‖ ≤ ‖w₀‖ ∧
      ‖populationIterate V lam j - minNormSolution V‖ ^ 2 ≤
        ‖w₀‖ ^ (2 / (β + 1)) *
          ‖projCondExpOp V (populationIterate V lam j - minNormSolution V)‖ ^ (2 * β / (β + 1)) := by
  have hβ := hSource.1
  refine ⟨1, zero_lt_one, ?_⟩
  intro lam hlam
  have hi := populationIterate_residual_identity V hRange lam hlam j
  have hc := residualFilter_source_commute V β w₀ hSource lam hlam j
  have hz := residualFilter_pow_norm_le V lam hlam j w₀
  have hp : Continuous (fun x : ℝ => (max x 0) ^ (β / 2)) := by
    fun_prop (disch := linarith [hSource.1])
  have hr : Continuous (fun x : ℝ => (lam / (max x 0 + lam)) ^ j) := by
    fun_prop (disch := intro x; positivity)
  have hprod : spectralOp V (fun x => (max x 0) ^ (β / 2))
      ((residualFilter V lam ^ j) w₀) =
      spectralOp V (fun x => (max x 0) ^ (β / 2) *
        (lam / (max x 0 + lam)) ^ j) w₀ := by
    rw [residualFilter_pow_symbol V lam hlam j]
    change (spectralOp V (fun x => (max x 0) ^ (β / 2)) *
      spectralOp V (fun x => (lam / (max x 0 + lam)) ^ j)) w₀ = _
    rw [← spectralOp_mul V _ _ hp hr]
  have he : populationIterate V lam j - minNormSolution V =
      -(spectralOp V (fun x => (max x 0) ^ (β / 2)) ((residualFilter V lam ^ j) w₀)) := by
    rw [← hc, ← hi, neg_sub]
  have hb := iteratedSource_bounds V β hSource.1 lam hlam j w₀
  refine ⟨hi, hc, ?_, ?_, hz, ?_⟩
  · simpa only [he, hprod, norm_neg, one_mul] using hb.1
  · simpa only [he, hprod, map_neg, norm_neg, one_mul] using hb.2
  · have hs := spectralSource_interpolation V β hSource.1 ((residualFilter V lam ^ j) w₀)
    dsimp only at hs
    simp only [he, map_neg, norm_neg]
    refine hs.trans ?_
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (norm_nonneg _) hz (by positivity)) (by positivity)

end Papers.TsAdaptiveEstimationInference
