module
public import Papers.TsAdaptiveEstimationInference.Helpers.SourceYoung
public import Papers.TsAdaptiveEstimationInference.Helpers.SpectralMoments
public import Toolkit.Foundations.Analysis.SpecialFunctions.TikhonovFilter
/-! Spectral regularization and the paper's deterministic source inequalities. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.unnecessarySeqFocus false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory
open scoped InnerProductSpace
-- Use the complex-to-real algebra instance required by Mathlib's real CFC.
attribute [local instance 2000]
  Causalean.Estimation.NPIV.Complexification.instAlgebraRealLpCLM
variable {𝒲 𝒳 𝒵 : Type*} [MeasurableSpace 𝒲]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒵] (V : IVWorld 𝒲 𝒳 𝒵)

/-- For [the population problem](hyp:V) and [a real penalty parameter](hyp:lam),
[the resolvent on the closed primal subspace](goal) applies the reciprocal of the
sum of the spectral argument and the penalty through the spectral operator. -/
noncomputable def resolvent (lam : ℝ) : V.Hbar.toSubmodule →L[ℝ] V.Hbar.toSubmodule :=
  spectralOp V (fun u => (u + lam)⁻¹)

-- @node: ambientNormalOp_isPositive
/-- [The ambient normal operator is positive: its quadratic form is nonnegative
at every vector](goal). -/
lemma ambientNormalOp_isPositive : (ambientNormalOp V).IsPositive := by
  have heq : ambientNormalOp V =
      ((projCondExpOp V).comp V.Hbar.toSubmodule.orthogonalProjectionOnto).adjoint.comp
        ((projCondExpOp V).comp V.Hbar.toSubmodule.orthogonalProjectionOnto) := by
    simp only [ContinuousLinearMap.adjoint_comp, Submodule.adjoint_orthogonalProjectionOnto]
    rfl
  rw [heq]
  exact ContinuousLinearMap.isPositive_adjoint_comp_self _

-- @node: ambientNormalOp_affineCFC
/-- [Applying the real functional calculus to the spectral argument plus a real
shift gives the ambient normal operator plus that shift times the identity](goal). -/
lemma ambientNormalOp_affineCFC (lam : ℝ) :
    Causalean.Estimation.NPIV.Complexification.realCFC (ambientNormalOp V)
      (fun x => lam + x) = lam • ContinuousLinearMap.id ℝ _ + ambientNormalOp V := by
  let A := ambientNormalOp V
  have hA : IsSelfAdjoint A := (ambientNormalOp_isPositive V).isSelfAdjoint
  have hcl := Causalean.Estimation.NPIV.Complexification.complexLift_isSelfAdjoint hA
  apply ContinuousLinearMap.ext
  intro v
  change Causalean.Estimation.NPIV.Complexification.reLp
    (cfc (fun z : ℂ => ((lam + z.re : ℝ) : ℂ))
      (Causalean.Estimation.NPIV.Complexification.complexLift A)
      (Causalean.Estimation.NPIV.Complexification.ιLp v)) = lam • v + A v
  rw [show (fun z : ℂ => ((lam + z.re : ℝ) : ℂ)) =
    (fun z : ℂ => (lam : ℂ) + (z.re : ℂ)) by funext z; simp]
  rw [cfc_const_add (lam : ℂ) (fun z : ℂ => (z.re : ℂ))
    (Causalean.Estimation.NPIV.Complexification.complexLift A)
    (hf := (Complex.continuous_ofReal.comp Complex.continuous_re).continuousOn)
    (ha := hcl.isStarNormal)]
  change Causalean.Estimation.NPIV.Complexification.reLp
    (((algebraMap ℂ _ (lam : ℂ)) + cfc (fun z : ℂ => ((id z.re : ℝ) : ℂ))
      (Causalean.Estimation.NPIV.Complexification.complexLift A))
      (Causalean.Estimation.NPIV.Complexification.ιLp v)) = lam • v + A v
  rw [← cfc_real_eq_complex (a := Causalean.Estimation.NPIV.Complexification.complexLift A)
    (f := id) (ha := hcl)]
  rw [cfc_id ℝ _ hcl]
  simp only [add_apply, Algebra.algebraMap_eq_smul_one,
    smul_apply, one_apply_eq_self, map_add]
  rw [Causalean.Estimation.NPIV.Complexification.reLp_ofReal_smul,
    Causalean.Estimation.NPIV.Complexification.reLp_comp_ιLp,
    Causalean.Estimation.NPIV.Complexification.reLp_complexLift_real]

-- @node: resolvent_normalEquation
/-- If [the penalty is strictly positive](hyp:hlam), then [the normal operator
applied to the resolvent of any primal vector, plus the penalty times that resolvent,
equals the original vector](goal). -/
lemma resolvent_normalEquation (lam : ℝ) (hlam : 0 < lam)
    (v : V.Hbar.toSubmodule) :
    normalOp V (resolvent V lam v) + lam • resolvent V lam v = v := by
  have hpos := ambientNormalOp_isPositive V
  have hspec : ∀ x ∈ spectrum ℝ (ambientNormalOp V), 0 ≤ x := by
    intro x hx
    exact spectrum_nonneg_of_nonneg (a := ambientNormalOp V) (by
      rw [ContinuousLinearMap.nonneg_iff_isPositive]
      exact hpos) hx
  have hid := Causalean.Estimation.NPIV.Complexification.realCFC_resolvent_mul_self
    (ambientNormalOp V) hpos.isSelfAdjoint hspec lam hlam
  rw [ambientNormalOp_affineCFC] at hid
  have hv := congrArg (fun f : Lp ℝ 2 V.law →L[ℝ] Lp ℝ 2 V.law =>
    V.Hbar.toSubmodule.orthogonalProjectionOnto
    (f (v : Lp ℝ 2 V.law))) hid
  simp only [ContinuousLinearMap.comp_apply, add_apply,
    smul_apply, ContinuousLinearMap.id_apply, map_add, map_smul,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self] at hv
  have hsymbol : (fun x : ℝ => (lam + x)⁻¹) = (fun x : ℝ => (x + lam)⁻¹) := by
    funext x
    rw [add_comm]
  rw [hsymbol] at hv
  have hp (y : Lp ℝ 2 V.law) :
      V.Hbar.toSubmodule.orthogonalProjectionOnto (ambientNormalOp V y) =
        normalOp V (V.Hbar.toSubmodule.orthogonalProjectionOnto y) :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
  rw [hp] at hv
  change lam • resolvent V lam v + normalOp V (resolvent V lam v) = v at hv
  simpa only [add_comm] using hv

-- @node: ambientNormalOp_spectrum
/-- [Every point in the real spectrum of the ambient normal operator lies between
zero and one, inclusive](goal). -/
lemma ambientNormalOp_spectrum :
    ∀ x ∈ spectrum ℝ (ambientNormalOp V), x ∈ Set.Icc (0 : ℝ) 1 := by
  nontriviality (Lp ℝ 2 V.law)
  let B := (projCondExpOp V).comp V.Hbar.toSubmodule.orthogonalProjectionOnto
  have heq : ambientNormalOp V = B.adjoint.comp B := by
    simp only [B, ContinuousLinearMap.adjoint_comp, Submodule.adjoint_orthogonalProjectionOnto]
    rfl
  have hB : ‖B‖ ≤ 1 := by
    apply B.opNorm_le_bound zero_le_one
    intro u
    change ‖projCondExpOp V (V.Hbar.toSubmodule.orthogonalProjectionOnto u)‖ ≤ 1 * ‖u‖
    have h := (projCondExpOp V).le_opNorm
      (V.Hbar.toSubmodule.orthogonalProjectionOnto u)
    calc
      _ ≤ 1 * ‖V.Hbar.toSubmodule.orthogonalProjectionOnto u‖ :=
        h.trans (mul_le_mul_of_nonneg_right (projCondExpOp_norm_le_one V) (norm_nonneg _))
      _ ≤ 1 * ‖u‖ := by
        gcongr
        exact V.Hbar.toSubmodule.norm_orthogonalProjectionOnto_apply_le u
  have hnorm : ‖ambientNormalOp V‖ ≤ 1 := by
    rw [heq, ContinuousLinearMap.norm_adjoint_comp_self]
    nlinarith [norm_nonneg B]
  intro x hx
  have hx0 := spectrum_nonneg_of_nonneg (a := ambientNormalOp V) (by
    rw [ContinuousLinearMap.nonneg_iff_isPositive]
    exact ambientNormalOp_isPositive V) hx
  refine ⟨hx0, ?_⟩
  have hn := spectrum.norm_le_norm_of_mem hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg hx0] using hn.trans hnorm

-- @node: ambientNormalOp_inner
/-- [The ambient normal operator's quadratic form at any vector in the closed primal
subspace equals the squared norm of its projected conditional-expectation image](goal). -/
lemma ambientNormalOp_inner (u : V.Hbar.toSubmodule) :
    inner ℝ (ambientNormalOp V (u : Lp ℝ 2 V.law)) (u : Lp ℝ 2 V.law) =
      ‖projCondExpOp V u‖ ^ 2 := by
  simp only [ambientNormalOp, ContinuousLinearMap.comp_apply,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    Submodule.subtypeL_apply, ← Submodule.coe_inner, normalOp, adjointOp,
    ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]

-- @node: ambientSourcePower_norm_le
/-- If [the source exponent is positive](hyp:hβ), then [the norm of the ambient
positive-part spectral power with half that exponent, applied to a primal vector,
is at most its projected conditional-expectation image norm to the smaller of the
exponent and one, times its own norm to the complementary power](goal). -/
lemma ambientSourcePower_norm_le {β : ℝ} (hβ : 0 < β) (u : V.Hbar.toSubmodule) :
    ‖Causalean.Estimation.NPIV.Complexification.realCFC (ambientNormalOp V)
      (fun x => (max x 0) ^ (β / 2)) (u : Lp ℝ 2 V.law)‖ ≤
      ‖projCondExpOp V u‖ ^ min β 1 * ‖u‖ ^ (1 - min β 1) := by
  open Causalean.Estimation.NPIV.Complexification in
  have hA := (ambientNormalOp_isPositive V).isSelfAdjoint
  have hs := ambientNormalOp_spectrum V
  have hpos : ∀ x ∈ spectrum ℝ (ambientNormalOp V), 0 ≤ x := fun x hx => (hs x hx).1
  have hsq (b : ℝ) : (‖projCondExpOp V u‖ ^ b * ‖u‖ ^ (1 - b)) ^ 2 =
      (‖projCondExpOp V u‖ ^ 2) ^ b * (‖u‖ ^ 2) ^ (1 - b) := by
    rw [mul_pow]
    congr 1 <;> rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _),
      ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)] <;> congr 1 <;> ring
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [hsq]
  by_cases hb : β < 1
  · rw [min_eq_left hb.le]
    have hi := realCFC_fractional_norm_sq (ambientNormalOp V) hA hpos ⟨hβ, hb⟩
      (u : Lp ℝ 2 V.law)
    simpa only [ambientNormalOp_inner V, Submodule.norm_coe] using hi
  · have hb1 : 1 ≤ β := le_of_not_gt hb
    rw [min_eq_right hb1]
    simp only [Real.rpow_one, sub_self, Real.rpow_zero, mul_one]
    rw [realCFC_power_norm_sq _ hA hβ.le]
    have hi := realCFC_inner_mono_real (ambientNormalOp V) hA
      (fun x => (max x 0) ^ β) id (by fun_prop (disch := positivity)) continuous_id
      (fun x hx => ?_) (u : Lp ℝ 2 V.law)
    · simpa only [realCFC_id _ hA, ambientNormalOp_inner V] using hi
    · rw [max_eq_left (hpos x hx)]
      simpa only [id_eq, Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_ge' (hs x hx).1 (hs x hx).2 zero_le_one hb1

-- @env: S3
variable (rδ : V.Qbar.toSubmodule) (δ : ℝ) -- @realizes r_\delta(right-hand side in the closed dual subspace)

-- @node: def:tikh-sol
/-- For [the population problem](hyp:V), [a perturbed dual right-hand side](hyp:rδ),
and [a positive finite penalty or infinity](hyp:lam), [the classical Tikhonov solution](goal)
is [zero at an infinite penalty](step:1) and [the resolvent applied to the adjoint
image of the right-hand side at a finite penalty](step:2). -/
noncomputable def classicalTikhonov (lam : WithTop {x : ℝ // 0 < x}) : V.Hbar.toSubmodule :=
  @dite _ (lam = ⊤) (Classical.propDecidable _) (fun _ => 0)
    (fun h => resolvent V (lam.untop h).1 (adjointOp V rδ))
  -- @realizes h_\lambda^\delta(positive finite penalty or the zero solution at infinity)
  -- @realizes \lambda(positive finite parameter with the infinity convention)

-- @node: def:dp
/-- For [the population problem](hyp:V), [a perturbed dual right-hand side](hyp:rδ),
[a noise bound](hyp:δ), [a bracketing factor](hyp:ell), [a noise safety factor](hyp:κ),
and [a positive finite penalty or infinity](hyp:lam), [the classical discrepancy-choice
condition](goal) requires [a nonnegative noise bound](step:1), [a perturbation norm
no larger than that bound](step:2), [a bracketing factor greater than one](step:3),
[a safety factor greater than one](step:4), and [an infinite penalty when the
right-hand side norm is at most the safety factor times the noise bound; otherwise,
a finite penalty whose residual is below that threshold and a second penalty between
it and its bracketing-factor multiple whose residual is above the threshold](step:5). -/
noncomputable def IsClassicalDiscrepancyChoice (ell κ : ℝ)
    (lam : WithTop {x : ℝ // 0 < x}) : Prop :=
  0 ≤ δ ∧ ‖rδ - momentRepresenter V‖ ≤ δ ∧ -- @realizes \delta(nonnegative perturbation bound)
  1 < ell ∧ -- @realizes \ell(bracketing factor greater than one)
  1 < κ ∧ -- @realizes \kappa(noise safety factor greater than one)
  if ‖rδ‖ ≤ κ * δ then lam = ⊤ else
    ∃ a : {x : ℝ // 0 < x}, lam = (a : WithTop {x : ℝ // 0 < x}) ∧
      ∃ a' : {x : ℝ // 0 < x}, (a' : ℝ) ∈ Set.Icc (a : ℝ) (ell * (a : ℝ)) ∧
        ‖projCondExpOp V (classicalTikhonov V rδ (a : WithTop {x : ℝ // 0 < x})) - rδ‖ ≤ κ * δ ∧
        κ * δ ≤ ‖projCondExpOp V (classicalTikhonov V rδ (a' : WithTop {x : ℝ // 0 < x})) - rδ‖

/-- For [the population problem](hyp:V) and [a real penalty](hyp:lam), [the population
iterate sequence](goal) [starts at zero](step:1) and [at each subsequent step applies
the resolvent to the adjoint image of the population moment representer plus the
penalty times the preceding iterate](step:2). -/
noncomputable def populationIterate (lam : ℝ) : ℕ → V.Hbar.toSubmodule
  | 0 => 0
  | j + 1 => resolvent V lam -- @realizes \ell(local natural iteration index in the population recursion)
      (adjointOp V (momentRepresenter V) + lam • populationIterate lam j)
  -- @realizes h_{j,\lambda}^*(structural population recursion)

/-- For [the population problem](hyp:V), [a sample-dependent fitting loss](hyp:loss),
[a sample-dependent squared distance between primal vectors](hyp:normsq),
[a candidate sample-dependent iterate sequence](hyp:candidate), [an iteration horizon](hyp:t),
and [a real penalty](hyp:lam), [the empirical-iterate condition](goal) requires
[zero initialization for every sample](step:1) and [at every step from one through
the horizon and every sample, membership in the primal hypothesis class and
minimization over that class of loss plus the penalty times squared distance to
the preceding iterate](step:2). -/
def IsEmpiricalIterate {Ω : Type*} (loss : Ω → V.Hbar.toSubmodule → ℝ)
    (normsq : Ω → V.Hbar.toSubmodule → V.Hbar.toSubmodule → ℝ) (candidate : ℕ → Ω → V.Hbar.toSubmodule)
    (t : ℕ) (lam : ℝ) : Prop :=
  (∀ ω, candidate 0 ω = 0) ∧ -- @realizes \hat h_{j,\lambda}(empirical zero initialization and selected recursion)
 ∀ j, 1 ≤ j → j ≤ t → ∀ ω, -- @realizes \ell(local integer iteration index from one through the prescribed horizon)
    candidate j ω ∈ V.H ∧ ∀ h ∈ V.H,
      loss ω (candidate j ω) + lam * normsq ω (candidate j ω) (candidate (j - 1) ω) ≤
        loss ω h + lam * normsq ω h (candidate (j - 1) ω)

/-- For [the population problem](hyp:V), [a sample-dependent fitting loss](hyp:loss),
[a sample-dependent squared distance between primal vectors](hyp:normsq),
[a positive iteration horizon](hyp:t), and [a positive penalty](hyp:lam),
[the joint iterative construction](goal) pairs the population iterate sequence with
the condition that a candidate empirical sequence starts at zero and minimizes the
penalized fitting objective at every step through the horizon. -/
noncomputable def genericIterativeRecursion {Ω : Type*}
    (loss : Ω → V.Hbar.toSubmodule → ℝ)
    (normsq : Ω → V.Hbar.toSubmodule → V.Hbar.toSubmodule → ℝ)
    (t : {j : ℕ // 1 ≤ j}) (lam : {r : ℝ // 0 < r}) :
    (ℕ → V.Hbar.toSubmodule) × ((ℕ → Ω → V.Hbar.toSubmodule) → Prop) :=
  (populationIterate V lam.1, -- @realizes h_{j,\lambda}^*(computed population component of the joint recursion)
    fun candidate => IsEmpiricalIterate V loss normsq candidate t.1 lam.1)
    -- @realizes \hat h_{j,\lambda}(zero initialization and all empirical minimizing steps of the joint recursion)

-- @node: populationIterate_minimizes
/-- If [the penalty is positive](hyp:hlam), then [each next population iterate
minimizes, over the closed primal subspace, the squared population fitting error
plus the penalty times squared distance to the preceding iterate](goal). -/
lemma populationIterate_minimizes (lam : ℝ) (hlam : 0 < lam) (j : ℕ) :
    ∀ h : V.Hbar.toSubmodule,
      ‖projCondExpOp V (populationIterate V lam (j + 1)) - momentRepresenter V‖ ^ 2 +
          lam * ‖populationIterate V lam (j + 1) - populationIterate V lam j‖ ^ 2 ≤
        ‖projCondExpOp V h - momentRepresenter V‖ ^ 2 +
          lam * ‖h - populationIterate V lam j‖ ^ 2 := by
  intro h
  let a := populationIterate V lam (j + 1)
  let c := populationIterate V lam j
  have hnormal : normalOp V a + lam • a =
      adjointOp V (momentRepresenter V) + lam • c :=
    resolvent_normalEquation V lam hlam _
  have hcross : inner ℝ (projCondExpOp V a - momentRepresenter V)
      (projCondExpOp V (h - a)) + lam * inner ℝ (a - c) (h - a) = 0 := by
    have hi := congrArg (fun x => inner ℝ x (h - a)) hnormal
    have hia : inner ℝ (lam • a) (h - a) = lam * inner ℝ a (h - a) := by
      exact real_inner_smul_left a (h - a) lam
    have hic : inner ℝ (lam • c) (h - a) = lam * inner ℝ c (h - a) := by
      exact real_inner_smul_left c (h - a) lam
    simp only [inner_add_left, hia, hic] at hi
    simp only [normalOp,
      ContinuousLinearMap.comp_apply, adjointOp, ContinuousLinearMap.adjoint_inner_left,
      inner_sub_left] at hi ⊢
    linarith
  have hT : projCondExpOp V h - momentRepresenter V =
      (projCondExpOp V a - momentRepresenter V) + projCondExpOp V (h - a) := by
    rw [map_sub]
    abel
  have hc : h - c = (a - c) + (h - a) := by abel
  change ‖projCondExpOp V a - momentRepresenter V‖ ^ 2 + lam * ‖a - c‖ ^ 2 ≤
    ‖projCondExpOp V h - momentRepresenter V‖ ^ 2 + lam * ‖h - c‖ ^ 2
  rw [hT, hc, norm_add_sq_real, norm_add_sq_real]
  have hnn := mul_nonneg hlam.le (sq_nonneg ‖h - a‖)
  nlinarith [sq_nonneg ‖projCondExpOp V (h - a)‖]

/-- For [a positive penalty](hyp:lam) and [a nonnegative spectral argument](hyp:u),
[the scalar residual filter](goal) is the penalty divided by the sum of the spectral
argument and the penalty. -/
noncomputable def scalarResidualFilter (lam : {x : ℝ // 0 < x}) (u : NNReal) : ℝ :=
  lam.1 / (u.1 + lam.1) -- @realizes r_\lambda(scalar filter on nonnegative spectral arguments)

/-- For [the population problem](hyp:V) and [a real penalty](hyp:lam), [the residual
filter operator](goal) applies the spectral symbol given by the penalty divided by
the sum of the spectral argument and the penalty on the closed primal subspace. -/
noncomputable def residualFilter (lam : ℝ) : V.Hbar.toSubmodule →L[ℝ] V.Hbar.toSubmodule :=
  spectralOp V (fun u => lam / (u + lam))

/-- For [a source exponent](hyp:β), [the one-step bias exponent](goal) is the smaller
of the source exponent plus one and two. -/
noncomputable def biasExponent (β : ℝ) : ℝ := min (β + 1) 2 -- @realizes p(one-step bias exponent)
/-- For [a source exponent](hyp:β), [the truncated source exponent](goal) is the
smaller of that exponent and one. -/
noncomputable def truncatedSource (β : ℝ) : ℝ := min β 1 -- @realizes b(truncated source exponent)
/-- For [a real source exponent](hyp:β), [the source-exponent domain condition](goal)
requires that the exponent be strictly positive. -/
def SourceExponentDomain (β : ℝ) : Prop := 0 < β -- @realizes b(positive input source exponent)
/-- For [a source exponent](hyp:β), [the interpolation exponent](goal) is the truncated
source exponent divided by one plus the truncated source exponent. -/
noncomputable def interpolationExponent (β : ℝ) : ℝ :=
  truncatedSource β / (1 + truncatedSource β) -- @realizes \alpha(source interpolation exponent)
/-- For [a source exponent](hyp:β) and [an iteration count](hyp:t), [the qualification
exponent](goal) is the smaller of the source exponent plus one and twice the iteration count. -/
noncomputable def qualificationExponent (β : ℝ) (t : ℕ) : ℝ :=
  min (β + 1) (2 * (t : ℝ)) -- @realizes q_t(iterative qualification exponent)

-- @node: variational_source_inner
/-- If [the exponent is positive and the minimum-norm solution is the source witness
transformed by the positive-part spectral power with half that exponent](hyp:hSource),
then [the absolute inner product of the solution with any primal vector is at most
the witness norm times the vector's projected conditional-expectation image norm
to the truncated source exponent, times its own norm to the complementary power](goal). -/
lemma variational_source_inner (β : ℝ) (w₀ : V.Hbar.toSubmodule)
    (hSource : BetaSourceCondition V β w₀) (u : V.Hbar.toSubmodule) :
    |inner ℝ (minNormSolution V) u| ≤
      ‖w₀‖ * ‖projCondExpOp V u‖ ^ truncatedSource β * ‖u‖ ^ (1 - truncatedSource β) := by
  open Causalean.Estimation.NPIV.Complexification in
  have hβ : 0 ≤ β / 2 := by linarith [hSource.1]
  have hf : Continuous (fun x : ℝ => (max x 0) ^ (β / 2)) := by fun_prop
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (realCFC_isSelfAdjoint (ambientNormalOp V)
      (ambientNormalOp_isPositive V).isSelfAdjoint _ hf)
  rw [hSource.2]
  change |inner ℝ (V.Hbar.toSubmodule.orthogonalProjectionOnto
    (realCFC (ambientNormalOp V) (fun x => (max x 0) ^ (β / 2))
      (w₀ : Lp ℝ 2 V.law))) u| ≤ _
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  have he := hs (w₀ : Lp ℝ 2 V.law) (u : Lp ℝ 2 V.law)
  change inner ℝ _ _ = inner ℝ _ _ at he
  calc
    _ = |inner ℝ (w₀ : Lp ℝ 2 V.law)
        (realCFC (ambientNormalOp V) (fun x => (max x 0) ^ (β / 2))
          (u : Lp ℝ 2 V.law))| := congrArg abs he
    _ ≤ ‖(w₀ : Lp ℝ 2 V.law)‖ *
        ‖realCFC (ambientNormalOp V) (fun x => (max x 0) ^ (β / 2))
          (u : Lp ℝ 2 V.law)‖ := abs_real_inner_le_norm _ _
    _ ≤ _ := by
      simpa only [Submodule.norm_coe, truncatedSource, mul_assoc] using
        mul_le_mul_of_nonneg_left (ambientSourcePower_norm_le V hSource.1 u) (norm_nonneg w₀)

/-- For [a real tolerance](hyp:ε), [the variational inequality constant](goal) is four
divided by that tolerance. -/
noncomputable def variationalConst (ε : ℝ) : ℝ := 4 / ε

/-- Suppose [the source exponent is positive and the minimum-norm solution is the
source witness transformed by the positive-part spectral power with half that
exponent](hyp:hSource). Writing b for the smaller of the exponent and one and p for
the smaller of the exponent plus one and two, [the absolute inner product of the
solution with any primal vector is bounded by the witness norm times the image norm
to power b times the vector norm to power one minus b; moreover, for every tolerance
strictly between zero and one there is a positive constant, common to all primal
vectors, giving both of the following bounds: for every penalty in `(0, 2]`, twice
the penalty times that absolute inner product is at most the tolerance times the sum
of the squared image norm and the penalty times the squared vector norm, plus the
constant times the squared witness norm times the penalty to power p; and twice
the absolute inner product is at most the tolerance times the squared vector norm,
plus the constant times the witness norm to power two divided by one plus b times
the image norm to power twice b divided by one plus b](goal).

The image norm is the norm of the projected conditional expectation of the vector. -/
lemma variational_source (β : ℝ) (w₀ : V.Hbar.toSubmodule)
    (hSource : BetaSourceCondition V β w₀) :
    (∀ u : V.Hbar.toSubmodule,
      |inner ℝ (minNormSolution V) u| ≤
        ‖w₀‖ * ‖projCondExpOp V u‖ ^ truncatedSource β * ‖u‖ ^ (1 - truncatedSource β)) ∧
    ∀ ε ∈ Set.Ioo (0 : ℝ) 1, ∃ Cε > 0, ∀ u : V.Hbar.toSubmodule,
      (∀ lam ∈ Set.Ioc (0 : ℝ) 2,
        2 * lam * |inner ℝ (minNormSolution V) u| ≤
          ε * (‖projCondExpOp V u‖ ^ 2 + lam * ‖u‖ ^ 2) +
            Cε * ‖w₀‖ ^ 2 * lam ^ biasExponent β) ∧
      2 * |inner ℝ (minNormSolution V) u| ≤ ε * ‖u‖ ^ 2 +
        Cε * ‖w₀‖ ^ (2 / (1 + truncatedSource β)) *
          ‖projCondExpOp V u‖ ^ (2 * truncatedSource β / (1 + truncatedSource β)) := by
  have hi := variational_source_inner V β w₀ hSource
  refine ⟨hi, ?_⟩
  intro ε hε
  have hε0 := hε.1
  let c := ε * (2 / ε) ^ (2 / (1 + truncatedSource β))
  let C := 4 / ε
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro u
  have hb : truncatedSource β ∈ Set.Ioc (0 : ℝ) 1 :=
    ⟨lt_min hSource.1 zero_lt_one, min_le_right _ _⟩
  have hp : biasExponent β = 1 + truncatedSource β := by
    dsimp [biasExponent, truncatedSource]
    by_cases h : β ≤ 1
    · rw [min_eq_left h, min_eq_left (by linarith : β + 1 ≤ 2)]
      ring
    · rw [min_eq_right (le_of_not_ge h), min_eq_right (by linarith : 2 ≤ β + 1)]
      norm_num
  constructor
  · intro lam hlam
    have hlam0 := hlam.1
    have hsq := source_scalar_energy_sq hb hlam.1
      (norm_nonneg (projCondExpOp V u)) (norm_nonneg u)
    have hz : (lam * (‖w₀‖ * ‖projCondExpOp V u‖ ^ truncatedSource β *
        ‖u‖ ^ (1 - truncatedSource β))) ^ 2 ≤
        (‖projCondExpOp V u‖ ^ 2 + lam * ‖u‖ ^ 2) *
          (‖w₀‖ ^ 2 * lam ^ biasExponent β) := by
      rw [hp]
      calc
        _ = ‖w₀‖ ^ 2 * (lam * ‖projCondExpOp V u‖ ^ truncatedSource β *
            ‖u‖ ^ (1 - truncatedSource β)) ^ 2 := by ring
        _ ≤ ‖w₀‖ ^ 2 * (lam ^ (1 + truncatedSource β) *
            (‖projCondExpOp V u‖ ^ 2 + lam * ‖u‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
        _ = _ := by ring
    have hy := source_scalar_energy_young hε.1 (by positivity) (by positivity)
      (by positivity) hz
    calc
      _ ≤ 2 * (lam * (‖w₀‖ * ‖projCondExpOp V u‖ ^ truncatedSource β *
          ‖u‖ ^ (1 - truncatedSource β))) := by
        nlinarith [mul_le_mul_of_nonneg_left (hi u) (by positivity : 0 ≤ 2 * lam)]
      _ ≤ _ := hy
      _ ≤ _ := by
        have hc : ε⁻¹ ≤ C := by
          dsimp [C]
          rw [div_eq_mul_inv]
          nlinarith [inv_pos.mpr hε.1]
        apply add_le_add le_rfl
        rw [mul_assoc C]
        exact mul_le_mul_of_nonneg_right hc (by positivity)
  · have hy := source_scalar_young
      (a := ‖w₀‖ * ‖projCondExpOp V u‖ ^ truncatedSource β) (u := ‖u‖) hb hε.1
      (mul_nonneg (norm_nonneg w₀) (Real.rpow_nonneg (norm_nonneg _) _)) (norm_nonneg u)
    have he : (‖w₀‖ * ‖projCondExpOp V u‖ ^ truncatedSource β) ^
        (2 / (1 + truncatedSource β)) =
        ‖w₀‖ ^ (2 / (1 + truncatedSource β)) *
          ‖projCondExpOp V u‖ ^ (2 * truncatedSource β / (1 + truncatedSource β)) := by
      rw [Real.mul_rpow (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _),
        ← Real.rpow_mul (norm_nonneg _)]
      congr 2
      ring
    rw [he] at hy
    calc
      _ ≤ 2 * (‖w₀‖ * ‖projCondExpOp V u‖ ^ truncatedSource β) *
          ‖u‖ ^ (1 - truncatedSource β) := by nlinarith [hi u]
      _ ≤ _ := hy
      _ ≤ _ := by
        have hc : c ≤ C := by
          have hd : 0 < 1 + truncatedSource β := by linarith [hb.1]
          have hbase : 1 ≤ 2 / ε := (le_div_iff₀ hε.1).mpr (by linarith [hε.2])
          have he : 2 / (1 + truncatedSource β) ≤ 2 :=
            (div_le_iff₀ hd).mpr (by linarith [hb.1])
          calc
            c ≤ ε * (2 / ε) ^ (2 : ℝ) := mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le hbase he) hε.1.le
            _ = C := by
              rw [Real.rpow_two]
              dsimp [C]
              field_simp
              <;> ring
        apply add_le_add le_rfl
        change c * (_ * _) ≤ _
        rw [mul_assoc C]
        exact mul_le_mul_of_nonneg_right hc (by positivity)


-- @node: lem:variational-source
/-- Suppose [the source exponent is positive and the minimum-norm solution is the
source witness transformed by the positive-part spectral power with half that
exponent](hyp:hSource). Writing b for the smaller of the exponent and one and p for
the smaller of the exponent plus one and two, [the absolute inner product of the
solution with any primal vector is bounded by the witness norm times the image norm
to power b times the vector norm to power one minus b; moreover, for every tolerance
strictly between zero and one, the variational constant, four divided by the tolerance,
is positive and gives both of the following bounds uniformly over primal vectors:
for every penalty in `(0, 2]`, twice the penalty times that absolute inner product is
at most the tolerance times the sum of the squared image norm and the penalty times
the squared vector norm, plus the variational constant times the squared witness norm
times the penalty to power p; and twice the absolute inner product is at most the
tolerance times the squared vector norm, plus the variational constant times the
witness norm to power two divided by one plus b times the image norm to power twice
b divided by one plus b](goal).

The image norm is the norm of the projected conditional expectation of the vector. -/
lemma variational_source_uniform (β : ℝ) (w₀ : V.Hbar.toSubmodule)
    (hSource : BetaSourceCondition V β w₀) :
    (∀ u : V.Hbar.toSubmodule,
      |inner ℝ (minNormSolution V) u| ≤
        ‖w₀‖ * ‖projCondExpOp V u‖ ^ truncatedSource β * ‖u‖ ^ (1 - truncatedSource β)) ∧
    ∀ ε ∈ Set.Ioo (0 : ℝ) 1, 0 < variationalConst ε ∧ ∀ u : V.Hbar.toSubmodule,
      (∀ lam ∈ Set.Ioc (0 : ℝ) 2,
        2 * lam * |inner ℝ (minNormSolution V) u| ≤
          ε * (‖projCondExpOp V u‖ ^ 2 + lam * ‖u‖ ^ 2) +
            variationalConst ε * ‖w₀‖ ^ 2 * lam ^ biasExponent β) ∧
      2 * |inner ℝ (minNormSolution V) u| ≤ ε * ‖u‖ ^ 2 +
        variationalConst ε * ‖w₀‖ ^ (2 / (1 + truncatedSource β)) *
          ‖projCondExpOp V u‖ ^ (2 * truncatedSource β / (1 + truncatedSource β)) := by
  have hi := variational_source_inner V β w₀ hSource
  refine ⟨hi, ?_⟩
  intro ε hε
  have hε0 := hε.1
  let c := ε * (2 / ε) ^ (2 / (1 + truncatedSource β))
  let C := variationalConst ε
  have hC : 0 < C := by dsimp [C, variationalConst]; positivity
  refine ⟨hC, ?_⟩
  intro u
  have hb : truncatedSource β ∈ Set.Ioc (0 : ℝ) 1 :=
    ⟨lt_min hSource.1 zero_lt_one, min_le_right _ _⟩
  have hp : biasExponent β = 1 + truncatedSource β := by
    dsimp [biasExponent, truncatedSource]
    by_cases h : β ≤ 1
    · rw [min_eq_left h, min_eq_left (by linarith : β + 1 ≤ 2)]
      ring
    · rw [min_eq_right (le_of_not_ge h), min_eq_right (by linarith : 2 ≤ β + 1)]
      norm_num
  constructor
  · intro lam hlam
    have hlam0 := hlam.1
    have hsq := source_scalar_energy_sq hb hlam.1
      (norm_nonneg (projCondExpOp V u)) (norm_nonneg u)
    have hz : (lam * (‖w₀‖ * ‖projCondExpOp V u‖ ^ truncatedSource β *
        ‖u‖ ^ (1 - truncatedSource β))) ^ 2 ≤
        (‖projCondExpOp V u‖ ^ 2 + lam * ‖u‖ ^ 2) *
          (‖w₀‖ ^ 2 * lam ^ biasExponent β) := by
      rw [hp]
      calc
        _ = ‖w₀‖ ^ 2 * (lam * ‖projCondExpOp V u‖ ^ truncatedSource β *
            ‖u‖ ^ (1 - truncatedSource β)) ^ 2 := by ring
        _ ≤ ‖w₀‖ ^ 2 * (lam ^ (1 + truncatedSource β) *
            (‖projCondExpOp V u‖ ^ 2 + lam * ‖u‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
        _ = _ := by ring
    have hy := source_scalar_energy_young hε.1 (by positivity) (by positivity)
      (by positivity) hz
    calc
      _ ≤ 2 * (lam * (‖w₀‖ * ‖projCondExpOp V u‖ ^ truncatedSource β *
          ‖u‖ ^ (1 - truncatedSource β))) := by
        nlinarith [mul_le_mul_of_nonneg_left (hi u) (by positivity : 0 ≤ 2 * lam)]
      _ ≤ _ := hy
      _ ≤ _ := by
        have hc : ε⁻¹ ≤ C := by
          dsimp [C, variationalConst]
          rw [div_eq_mul_inv]
          nlinarith [inv_pos.mpr hε.1]
        apply add_le_add le_rfl
        rw [mul_assoc C]
        exact mul_le_mul_of_nonneg_right hc (by positivity)
  · have hy := source_scalar_young
      (a := ‖w₀‖ * ‖projCondExpOp V u‖ ^ truncatedSource β) (u := ‖u‖) hb hε.1
      (mul_nonneg (norm_nonneg w₀) (Real.rpow_nonneg (norm_nonneg _) _)) (norm_nonneg u)
    have he : (‖w₀‖ * ‖projCondExpOp V u‖ ^ truncatedSource β) ^
        (2 / (1 + truncatedSource β)) =
        ‖w₀‖ ^ (2 / (1 + truncatedSource β)) *
          ‖projCondExpOp V u‖ ^ (2 * truncatedSource β / (1 + truncatedSource β)) := by
      rw [Real.mul_rpow (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _),
        ← Real.rpow_mul (norm_nonneg _)]
      congr 2
      ring
    rw [he] at hy
    calc
      _ ≤ 2 * (‖w₀‖ * ‖projCondExpOp V u‖ ^ truncatedSource β) *
          ‖u‖ ^ (1 - truncatedSource β) := by nlinarith [hi u]
      _ ≤ _ := hy
      _ ≤ _ := by
        have hc : c ≤ C := by
          have hd : 0 < 1 + truncatedSource β := by linarith [hb.1]
          have hbase : 1 ≤ 2 / ε := (le_div_iff₀ hε.1).mpr (by linarith [hε.2])
          have he : 2 / (1 + truncatedSource β) ≤ 2 :=
            (div_le_iff₀ hd).mpr (by linarith [hb.1])
          calc
            c ≤ ε * (2 / ε) ^ (2 : ℝ) := mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le hbase he) hε.1.le
            _ = C := by
              rw [Real.rpow_two]
              dsimp [C, variationalConst]
              field_simp
              <;> ring
        apply add_le_add le_rfl
        change c * (_ * _) ≤ _
        rw [mul_assoc C]
        exact mul_le_mul_of_nonneg_right hc (by positivity)

end Papers.TsAdaptiveEstimationInference
