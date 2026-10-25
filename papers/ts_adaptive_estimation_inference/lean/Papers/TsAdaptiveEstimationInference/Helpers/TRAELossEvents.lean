module
public import Papers.TsAdaptiveEstimationInference.Helpers.TRAEDeviations
/-! Population games and measurable TRAE loss events. -/
@[expose] public section
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter
open scoped Topology
variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]
  (V : IVWorld 𝒲 𝒳 𝒵) (P : Measure Ω) [IsProbabilityMeasure P]
  (sample : AnalysisSample V P) (split : SampleSplit)
variable (ρ ξ B β : ℝ) (w₀ : V.Hbar.toSubmodule)
  (δ ν baseδ baseν : ℕ → ℝ) (δG δH δr tildeδ : ℕ → ℝ → ℝ)
  (κδ κν required c₀ CG Cm : ℝ) (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ)
  (mu : Measure 𝒳) (G : Set (𝒳 → 𝒵 → ℝ)) (g₀ : 𝒳 → 𝒵 → ℝ)
  (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (rHat : ℕ → Ω → 𝒵 → ℝ)
  (support : Set (𝒳 × 𝒵)) (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
  (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule)
  (a b c : ℝ) (t : ℕ)
/-- [Pairing the projected conditional expectation of a hypothesis with a dual
element gives the same inner product as pairing their original population L²
representatives](goal). -/
-- @node: trae_operator_inner
lemma trae_operator_inner (h : V.Hbar.toSubmodule) (f : V.Qbar.toSubmodule) :
    inner ℝ (projCondExpOp V h) f =
      inner ℝ (h : Lp ℝ 2 V.law) (f : Lp ℝ 2 V.law) := by
  unfold projCondExpOp
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  exact inner_condExpL2_eq_inner_fun V.measurable_z.comap_le _ _
    (mem_lpMeas_iff_aestronglyMeasurable.mp (V.Qmeas f.property))

/-- Under [the range condition for the moment equation](hyp:hRange), [the
population mean of the TRAE integrand equals twice the inner product of the
projected minimum-norm-solution residual with the critic, minus the critic's
squared norm](goal). -/
-- @node: trae_integrand_mean
lemma trae_integrand_mean (hRange : RangeCondition V)
    (h : V.Hbar.toSubmodule) (f : V.Qbar.toSubmodule) :
    (∫ w, traeIntegrand V h f w ∂V.law) =
      2 * inner ℝ (projCondExpOp V (minNormSolution V - h)) f - ‖f‖ ^ 2 := by
  have hprod : (fun w => primalVersion V h (V.xOf w) * dualVersion V f (V.zOf w))
      =ᵐ[V.law] (fun w => (h : Lp ℝ 2 V.law) w * (f : Lp ℝ 2 V.law) w) :=
    (V.primal_coherent h).mul (V.dual_coherent f)
  have hsquare : (fun w => dualVersion V f (V.zOf w) ^ 2)
      =ᵐ[V.law] (fun w => (f : Lp ℝ 2 V.law) w ^ 2) :=
    (V.dual_coherent f).mono fun w hw => congrArg (fun x : ℝ => x ^ 2) hw
  have hp : Integrable (fun w => primalVersion V h (V.xOf w) *
      dualVersion V f (V.zOf w)) V.law := by
    apply Integrable.congr _ hprod.symm
    simpa only [RCLike.inner_apply, conj_trivial, mul_comm] using
      (L2.integrable_inner (𝕜 := ℝ) (h : Lp ℝ 2 V.law) (f : Lp ℝ 2 V.law))
  have hq : Integrable (fun w => dualVersion V f (V.zOf w) ^ 2) V.law := by
    apply Integrable.congr _ hsquare.symm
    simpa only [RCLike.inner_apply, conj_trivial, pow_two] using
      (L2.integrable_inner (𝕜 := ℝ) (f : Lp ℝ 2 V.law) (f : Lp ℝ 2 V.law))
  have hip : (∫ w, primalVersion V h (V.xOf w) * dualVersion V f (V.zOf w) ∂V.law) =
      inner ℝ (projCondExpOp V h) f := by
    rw [trae_operator_inner, L2.inner_def]
    simpa only [RCLike.inner_apply, conj_trivial, mul_comm] using integral_congr_ae hprod
  have hiq : (∫ w, dualVersion V f (V.zOf w) ^ 2 ∂V.law) = ‖f‖ ^ 2 := by
    rw [integral_congr_ae hsquare]
    change (∫ w, (f : Lp ℝ 2 V.law) w ^ 2 ∂V.law) = ‖(f : Lp ℝ 2 V.law)‖ ^ 2
    simpa only [L2.inner_def, RCLike.inner_apply, conj_trivial, pow_two] using
      (real_inner_self_eq_norm_sq (f : Lp ℝ 2 V.law))
  have him : (∫ w, V.m f w ∂V.law) =
      inner ℝ (projCondExpOp V (minNormSolution V)) f := by
    rw [(minNormSolution_spec V hRange).1]
    exact (V.momentFunctional_eq f).symm.trans
      (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := f) (y := V.momentFunctional)).symm
  unfold traeIntegrand
  simp_rw [show ∀ w, 2 * primalVersion V h (V.xOf w) * dualVersion V f (V.zOf w) =
    2 * (primalVersion V h (V.xOf w) * dualVersion V f (V.zOf w)) by intro w; ring]
  have hsub := integral_sub ((V.integrable_m f).const_mul 2 |>.sub (hp.const_mul 2)) hq
  simp only [Pi.sub_apply] at hsub
  rw [hsub, integral_sub ((V.integrable_m f).const_mul 2) (hp.const_mul 2),
    integral_const_mul, integral_const_mul, hip, hiq, him, map_sub, inner_sub_left]
  ring

/-- Under [the range condition](hyp:hRange) and [closure of projected solution
residuals in the critic class](hyp:hClose), [an admissible hypothesis](hyp:hh)
has [population TRAE loss equal to the squared norm of its projected difference
from the minimum-norm solution](goal). -/
-- @node: traePopulationLoss_eq
lemma traePopulationLoss_eq (hRange : RangeCondition V) (hClose : ClosenessCondition V)
    (h : V.Hbar.toSubmodule) (hh : h ∈ V.H) :
    traePopulationLoss V h = ‖projCondExpOp V (h - minNormSolution V)‖ ^ 2 := by
  let r := projCondExpOp V (minNormSolution V - h)
  have hr : r ∈ V.F := hClose h hh
  haveI : Nonempty V.F := ⟨⟨r, hr⟩⟩
  have hquad (f : V.Qbar.toSubmodule) :
      (∫ w, traeIntegrand V h f w ∂V.law) = ‖r‖ ^ 2 - ‖r - f‖ ^ 2 := by
    rw [trae_integrand_mean V hRange]
    dsimp [r]
    rw [norm_sub_sq_real]
    ring
  have hb : BddAbove (Set.range (fun f : V.F => ∫ w, traeIntegrand V h f w ∂V.law)) := by
    refine ⟨‖r‖ ^ 2, ?_⟩
    rintro _ ⟨f, rfl⟩
    dsimp only
    rw [hquad]
    exact sub_le_self _ (sq_nonneg _)
  have heq : traePopulationLoss V h = ‖r‖ ^ 2 := by
    unfold traePopulationLoss
    apply le_antisymm
    · apply ciSup_le
      intro f
      rw [hquad]
      exact sub_le_self _ (sq_nonneg _)
    · have hl := le_ciSup hb (⟨r, hr⟩ : V.F)
      calc
        ‖r‖ ^ 2 = (∫ w, traeIntegrand V h r w ∂V.law) := by
          rw [hquad, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero]
        _ ≤ _ := hl
  rw [heq]
  have hneg : projCondExpOp V (h - minNormSolution V) = -r := by
    dsimp [r]
    rw [← map_neg, neg_sub]
  rw [hneg, norm_neg]

/-- Given [localized TRAE concentration](hyp:hBennett_of_gate), [mean-square
continuity of the moment map](hyp:hMSC), [the TRAE boundedness and
process-measurability assumptions](hyp:hBound), [simultaneous common-null-set
bounds](hyp:hCommon), and [critical radius bounds](hyp:hComplexity), [there is
a positive constant, chosen before the accuracy and allocation curves, such
that under the range, closeness, and scale-calibration conditions, every positive
sample size with allocation between zero and one admits a measurable event of
probability at least one minus half the allocation on which all admissible
empirical losses lie between one half and five quarters of their population
losses, with additive error equal to the constant times accuracy squared](goal). -/
-- @node: traeLossEventAtAllocationUniform
lemma traeLossEventAtAllocationUniform
    (hBennett_of_gate : TRAELocalizedConcentration V)
    (B : ℝ) (tildeδ : ℕ → ℝ → ℝ)
    (hMSC : MeanSquareContinuity V) (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B)
    (hComplexity : TRAECriticalRadiusBound V tildeδ) :
    ∃ C > 0, ∀ (δ allocation : ℕ → ℝ),
      RangeCondition V → ClosenessCondition V →
      TRAEScaleCalibration δ tildeδ allocation →
      ∀ n : ℕ, 0 < n → allocation n ∈ Set.Ioo (0 : ℝ) 1 →
      ∃ E : Set Ω, MeasurableSet E ∧ 1 - allocation n / 2 ≤ P.real E ∧
        ∀ ω ∈ E, ∀ h ∈ V.H,
          (1 / 2 : ℝ) * traePopulationLoss V h - C * δ n ^ 2 ≤
            traeEmpiricalLoss V P sample split n ω h ∧
          traeEmpiricalLoss V P sample split n ω h ≤
            (5 / 4 : ℝ) * traePopulationLoss V h + C * δ n ^ 2 := by
  obtain ⟨D, hD, hBoth⟩ := trae_calibrated_deviation_at_allocation
    V P sample split hBennett_of_gate B tildeδ hBound hCommon hMSC hComplexity
  let Cf := D
  have hCf : 0 < Cf := by dsimp [Cf]; positivity
  let C := Cf + 2 * Cf ^ 2 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hCfC : Cf + 2 * Cf ^ 2 ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro δ allocation hRange hClose hScale n hn hValid
  obtain ⟨E, hE, hprob, hboth⟩ :=
    hBoth δ allocation hRange hClose hScale n hn hValid
  have hd : 0 ≤ δ n :=
    (show 0 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) by positivity).trans
      ((le_max_right _ _).trans (hScale.1 n hn))
  have hdev (ω : Ω) (hω : ω ∈ E) (h : V.Hbar.toSubmodule) (hh : h ∈ V.H)
      (f : V.Qbar.toSubmodule) (hff : f ∈ V.F) :
      |blockAverage V P sample (split.fit n) (traeIntegrand V h f) ω -
        (∫ w, traeIntegrand V h f w ∂V.law)| ≤ Cf * (δ n ^ 2 + δ n * ‖f‖) := by
    exact hboth ω hω h hh f hff
  have hforward (ω : Ω) (hω : ω ∈ E) (h : V.Hbar.toSubmodule) (hh : h ∈ V.H)
      (f : V.Qbar.toSubmodule) (hff : f ∈ V.F) :
      (∫ w, traeIntegrand V h f w ∂V.law) ≤
        blockAverage V P sample (split.fit n) (traeIntegrand V h f) ω +
          Cf * (δ n ^ 2 + δ n * ‖f‖) := by
    linarith only [(abs_le.mp (hdev ω hω h hh f hff)).1]
  have hreverse (ω : Ω) (hω : ω ∈ E) (h : V.Hbar.toSubmodule) (hh : h ∈ V.H)
      (f : V.Qbar.toSubmodule) (hff : f ∈ V.F) :
      blockAverage V P sample (split.fit n) (traeIntegrand V h f) ω ≤
        (∫ w, traeIntegrand V h f w ∂V.law) + Cf * (δ n ^ 2 + δ n * ‖f‖) := by
    linarith only [(abs_le.mp (hdev ω hω h hh f hff)).2]
  refine ⟨E, hE, hprob, ?_⟩
  intro ω hω h hh
  let r := projCondExpOp V (minNormSolution V - h)
  have hr : r ∈ V.F := hClose h hh
  have : Nonempty V.F := ⟨⟨r, hr⟩⟩
  have hpop : traePopulationLoss V h = ‖r‖ ^ 2 := by
    rw [traePopulationLoss_eq V hRange hClose h hh]
    have heq : projCondExpOp V (h - minNormSolution V) = -r := by
      dsimp [r]
      rw [← map_neg, neg_sub]
    rw [heq, norm_neg]
  have hUpper (f : V.F) :
      blockAverage V P sample (split.fit n) (traeIntegrand V h f) ω ≤
        (5 / 4 : ℝ) * ‖r‖ ^ 2 + C * δ n ^ 2 := by
    have hb := hreverse ω hω h hh f f.property
    rw [trae_integrand_mean V hRange] at hb
    have hi : inner ℝ r (f : V.Qbar.toSubmodule) ≤ ‖r‖ * ‖(f : V.Qbar.toSubmodule)‖ :=
      real_inner_le_norm _ _
    have hs1 := sq_nonneg (‖(f : V.Qbar.toSubmodule)‖ - ‖r‖ - Cf * δ n / 2)
    have hs2 := sq_nonneg (‖r‖ / 2 - Cf * δ n)
    have hc := mul_le_mul_of_nonneg_right hCfC (sq_nonneg (δ n))
    change _ ≤ 2 * inner ℝ r (f : V.Qbar.toSubmodule) -
      ‖(f : V.Qbar.toSubmodule)‖ ^ 2 +
      Cf * (δ n ^ 2 + δ n * ‖(f : V.Qbar.toSubmodule)‖) at hb
    nlinarith
  have hbdd : BddAbove (Set.range (fun f : V.F =>
      blockAverage V P sample (split.fit n) (traeIntegrand V h f) ω)) := by
    refine ⟨(5 / 4 : ℝ) * ‖r‖ ^ 2 + C * δ n ^ 2, ?_⟩
    rintro _ ⟨f, rfl⟩
    exact hUpper f
  rw [hpop]
  constructor
  · have hf := hforward ω hω h hh r hr
    rw [trae_integrand_mean V hRange] at hf
    change 2 * inner ℝ r r - ‖r‖ ^ 2 ≤ _ at hf
    rw [real_inner_self_eq_norm_sq] at hf
    have hle := le_ciSup hbdd (⟨r, hr⟩ : V.F)
    have hs := sq_nonneg (‖r‖ - Cf * δ n)
    have hc := mul_le_mul_of_nonneg_right hCfC (sq_nonneg (δ n))
    change _ ≤ traeEmpiricalLoss V P sample split n ω h at hle
    nlinarith
  · exact ciSup_le hUpper

/-- Assume [the range condition](hyp:hRange), [closure of projected solution
residuals in the critic class](hyp:hClose), [a nonnegative deviation constant
D](hyp:hD), [a nonnegative radius r](hyp:hr0), and [a comparison constant C at
least D plus twice D squared](hyp:hDC). If [every admissible hypothesis-critic
integrand has absolute empirical deviation at most D times the sum of r squared
and r times the critic norm at this sample](hyp:hdev), then [every admissible
empirical loss lies between one half and five quarters of its population loss,
with additive error C times r squared](goal). -/
lemma trae_loss_comparison_of_deviation
    (hRange : RangeCondition V) (hClose : ClosenessCondition V)
    (n : ℕ) (ω : Ω) (r D C : ℝ) (hD : 0 ≤ D) (hr0 : 0 ≤ r)
    (hDC : D + 2 * D ^ 2 ≤ C)
    (hdev : ∀ h ∈ V.H, ∀ f ∈ V.F,
      |blockAverage V P sample (split.fit n) (traeIntegrand V h f) ω -
        (∫ w, traeIntegrand V h f w ∂V.law)| ≤ D * (r ^ 2 + r * ‖f‖)) :
    ∀ h ∈ V.H,
      (1 / 2 : ℝ) * traePopulationLoss V h - C * r ^ 2 ≤
        traeEmpiricalLoss V P sample split n ω h ∧
      traeEmpiricalLoss V P sample split n ω h ≤
        (5 / 4 : ℝ) * traePopulationLoss V h + C * r ^ 2 := by
  have hforward (h : V.Hbar.toSubmodule) (hh : h ∈ V.H)
      (f : V.Qbar.toSubmodule) (hf : f ∈ V.F) :
      (∫ w, traeIntegrand V h f w ∂V.law) ≤
        blockAverage V P sample (split.fit n) (traeIntegrand V h f) ω +
          D * (r ^ 2 + r * ‖f‖) := by
    linarith only [(abs_le.mp (hdev h hh f hf)).1]
  have hreverse (h : V.Hbar.toSubmodule) (hh : h ∈ V.H)
      (f : V.Qbar.toSubmodule) (hf : f ∈ V.F) :
      blockAverage V P sample (split.fit n) (traeIntegrand V h f) ω ≤
        (∫ w, traeIntegrand V h f w ∂V.law) + D * (r ^ 2 + r * ‖f‖) := by
    linarith only [(abs_le.mp (hdev h hh f hf)).2]
  intro h hh
  let residual := projCondExpOp V (minNormSolution V - h)
  have hr : residual ∈ V.F := hClose h hh
  have : Nonempty V.F := ⟨⟨residual, hr⟩⟩
  have hpop : traePopulationLoss V h = ‖residual‖ ^ 2 := by
    rw [traePopulationLoss_eq V hRange hClose h hh]
    have heq : projCondExpOp V (h - minNormSolution V) = -residual := by
      dsimp [residual]
      rw [← map_neg, neg_sub]
    rw [heq, norm_neg]
  have hUpper (f : V.F) :
      blockAverage V P sample (split.fit n) (traeIntegrand V h f) ω ≤
        (5 / 4 : ℝ) * ‖residual‖ ^ 2 + C * r ^ 2 := by
    have hb := hreverse h hh f f.property
    rw [trae_integrand_mean V hRange] at hb
    have hi : inner ℝ residual (f : V.Qbar.toSubmodule) ≤ ‖residual‖ * ‖(f : V.Qbar.toSubmodule)‖ :=
      real_inner_le_norm _ _
    have hs1 := sq_nonneg (‖(f : V.Qbar.toSubmodule)‖ - ‖residual‖ - D * r / 2)
    have hs2 := sq_nonneg (‖residual‖ / 2 - D * r)
    have hc := mul_le_mul_of_nonneg_right hDC (sq_nonneg (r))
    change _ ≤ 2 * inner ℝ residual (f : V.Qbar.toSubmodule) -
      ‖(f : V.Qbar.toSubmodule)‖ ^ 2 +
      D * (r ^ 2 + r * ‖(f : V.Qbar.toSubmodule)‖) at hb
    nlinarith
  have hbdd : BddAbove (Set.range (fun f : V.F =>
      blockAverage V P sample (split.fit n) (traeIntegrand V h f) ω)) := by
    refine ⟨(5 / 4 : ℝ) * ‖residual‖ ^ 2 + C * r ^ 2, ?_⟩
    rintro _ ⟨f, rfl⟩
    exact hUpper f
  rw [hpop]
  constructor
  · have hf := hforward h hh residual hr
    rw [trae_integrand_mean V hRange] at hf
    change 2 * inner ℝ residual residual - ‖residual‖ ^ 2 ≤ _ at hf
    rw [real_inner_self_eq_norm_sq] at hf
    have hle := le_ciSup hbdd (⟨residual, hr⟩ : V.F)
    have hs := sq_nonneg (‖residual‖ - D * r)
    have hc := mul_le_mul_of_nonneg_right hDC (sq_nonneg (r))
    change _ ≤ traeEmpiricalLoss V P sample split n ω h at hle
    nlinarith
  · exact ciSup_le hUpper


/-- Under [localized TRAE concentration](hyp:hBennett_of_gate), [the range
condition](hyp:hRange), [closure of projected solution residuals in the critic
class](hyp:hClose), [mean-square continuity](hyp:hMSC), [TRAE boundedness and
process measurability](hyp:hBound), [common-null-set bounds](hyp:hCommon),
[critical radius bounds](hyp:hComplexity), and [calibration of accuracy to the
critical radii and allocation](hyp:hScale), [a positive constant works at every
positive sample size with allocation between zero and one: a measurable event
of probability at least one minus half the allocation simultaneously bounds
each admissible empirical loss between one half and five quarters of its
population loss, up to the constant times accuracy squared](goal). -/
-- @node: traeLossEventAtAllocation
lemma traeLossEventAtAllocation
    (hBennett_of_gate : TRAELocalizedConcentration V)
    (B : ℝ) (δ : ℕ → ℝ) (tildeδ : ℕ → ℝ → ℝ) (allocation : ℕ → ℝ)
    (hRange : RangeCondition V) (hClose : ClosenessCondition V) (hMSC : MeanSquareContinuity V)
    (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B) (hComplexity : TRAECriticalRadiusBound V tildeδ)
    (hScale : TRAEScaleCalibration δ tildeδ allocation) :
    ∃ C > 0, ∀ n : ℕ, 0 < n → allocation n ∈ Set.Ioo (0 : ℝ) 1 →
      ∃ E : Set Ω, MeasurableSet E ∧ 1 - allocation n / 2 ≤ P.real E ∧
        ∀ ω ∈ E, ∀ h ∈ V.H,
          (1 / 2 : ℝ) * traePopulationLoss V h - C * δ n ^ 2 ≤
            traeEmpiricalLoss V P sample split n ω h ∧
          traeEmpiricalLoss V P sample split n ω h ≤
            (5 / 4 : ℝ) * traePopulationLoss V h + C * δ n ^ 2 := by
  obtain ⟨C, hC, hevent⟩ := traeLossEventAtAllocationUniform V P sample split
    hBennett_of_gate B tildeδ hMSC hBound hCommon hComplexity
  exact ⟨C, hC, hevent δ allocation hRange hClose hScale⟩

/-- If [the overall failure budget lies strictly between zero and one](hyp:hξ),
then [its grid allocation also lies strictly between zero and one at every
sample size](goal). -/
lemma trae_grid_allocation_valid (ρ ξ : ℝ) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1) (n : ℕ) :
    gridConfidence ρ ξ n ∈ Set.Ioo (0 : ℝ) 1 := by
  have hk : (1 : ℝ) ≤ (terminalIndex ρ n + 1 : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  constructor
  · unfold gridConfidence; positivity [hξ.1]
  · unfold gridConfidence
    apply (div_lt_iff₀ (by positivity)).2
    norm_num only [Nat.cast_add, Nat.cast_one, one_mul]
    linarith only [hk, hξ.2]

section SharedEvent
variable (hBennett_of_gate : TRAELocalizedConcentration V)
  (hRange : RangeCondition V) (hClose : ClosenessCondition V)
  (hMSC : MeanSquareContinuity V) (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B)
  (hComplexity : TRAECriticalRadiusBound V tildeδ)

/-- For [the instrumental-variable model](hyp:V), [the sampling law](hyp:P),
[the analysis sample](hyp:sample), [the sample split](hyp:split), [the envelope
bound](hyp:B), and [the critical-radius curve](hyp:tildeδ), given [localized
TRAE concentration](hyp:hBennett_of_gate), [mean-square continuity](hyp:hMSC),
[TRAE boundedness and process measurability](hyp:hBound), [common-null-set
bounds](hyp:hCommon), and [critical radius bounds for that curve](hyp:hComplexity),
the [loss comparison constant](goal) is the positive witness chosen from the
uniform loss-event theorem, before confidence, accuracy, or sample size is fixed. -/
noncomputable def traeLossComparisonConstant : ℝ :=
  Classical.choose (traeLossEventAtAllocationUniform V P sample split
    hBennett_of_gate B tildeδ hMSC hBound hCommon hComplexity)

/-- For [the model](hyp:V), [sampling law](hyp:P), [analysis sample](hyp:sample),
[sample split](hyp:split), [grid ratio](hyp:ρ), [failure budget](hyp:ξ),
[envelope bound](hyp:B), [accuracy curve](hyp:δ), and [critical-radius
curve](hyp:tildeδ), assume [localized TRAE concentration](hyp:hBennett_of_gate),
[the range condition](hyp:hRange), [closure of projected residuals in the critic
class](hyp:hClose), [mean-square continuity](hyp:hMSC), [TRAE boundedness and
process measurability](hyp:hBound), [common-null-set bounds](hyp:hCommon), and
[critical radius bounds](hyp:hComplexity). Given [a failure budget strictly
between zero and one](hyp:hξ), [scale calibration to the grid allocation](hyp:hScale),
and [a sample size](hyp:n) [that is positive](hyp:hn), the [loss sample event](goal)
is the measurable witness selected from the uniform loss comparison at that
sample size and grid allocation. -/
noncomputable def traeLossSampleEvent (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (hScale : TRAEScaleCalibration δ tildeδ (fun n => gridConfidence ρ ξ n))
    (n : ℕ) (hn : 0 < n) : Set Ω :=
  Classical.choose ((Classical.choose_spec (traeLossEventAtAllocationUniform V P sample split
    hBennett_of_gate B tildeδ hMSC hBound hCommon hComplexity)).2
      δ (fun n => gridConfidence ρ ξ n) hRange hClose hScale n hn
        (trae_grid_allocation_valid ρ ξ hξ n))

/-- For [the model](hyp:V), [sampling law](hyp:P), [analysis sample](hyp:sample),
[sample split](hyp:split), [grid ratio](hyp:ρ), [failure budget](hyp:ξ),
[envelope bound](hyp:B), [accuracy curve](hyp:δ), and [critical-radius
curve](hyp:tildeδ), assume [localized TRAE concentration](hyp:hBennett_of_gate),
[the range condition](hyp:hRange), [closure of projected residuals in the critic
class](hyp:hClose), [mean-square continuity](hyp:hMSC), [TRAE boundedness and
process measurability](hyp:hBound), [common-null-set bounds](hyp:hCommon), and
[critical radius bounds](hyp:hComplexity). Given [a failure budget strictly
between zero and one](hyp:hξ), [scale calibration to the grid allocation](hyp:hScale),
[a sample size](hyp:n) [that is positive](hyp:hn), and [a squared-norm
event](hyp:normEvent), the [common sample event](goal) is the intersection of
the selected loss sample event with that squared-norm event. -/
noncomputable def traeCommonSampleEvent (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (hScale : TRAEScaleCalibration δ tildeδ (fun n => gridConfidence ρ ξ n))
    (n : ℕ) (hn : 0 < n) (normEvent : Set Ω) : Set Ω := -- @realizes \mathcal E_n(the shared loss and squared-norm event intersection)
  traeLossSampleEvent V P sample split ρ ξ B δ tildeδ hBennett_of_gate
    hRange hClose hMSC hBound hCommon hComplexity hξ hScale n hn ∩ normEvent

/-- Under localized TRAE concentration, the range
condition, closure of projected residuals in the critic class,
mean-square continuity, TRAE boundedness and process measurability,
common-null-set bounds, and critical radius bounds,
if [the failure budget lies strictly between zero and one](hyp:hξ), [the accuracy
is calibrated to the grid allocation](hyp:hScale), and [the sample size is
positive](hyp:hn), then [the selected loss sample event is measurable, has
probability at least one minus half the grid allocation, and simultaneously
bounds every admissible empirical loss between one half and five quarters of
its population loss, up to the selected comparison constant times accuracy
squared](goal). -/
lemma traeLossSampleEvent_spec (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (hScale : TRAEScaleCalibration δ tildeδ (fun n => gridConfidence ρ ξ n))
    (n : ℕ) (hn : 0 < n) :
    let E := traeLossSampleEvent V P sample split ρ ξ B δ tildeδ hBennett_of_gate
      hRange hClose hMSC hBound hCommon hComplexity hξ hScale n hn
    let C := traeLossComparisonConstant V P sample split B tildeδ hBennett_of_gate
      hMSC hBound hCommon hComplexity
    MeasurableSet E ∧ 1 - gridConfidence ρ ξ n / 2 ≤ P.real E ∧
      ∀ ω ∈ E, ∀ h ∈ V.H,
        (1 / 2 : ℝ) * traePopulationLoss V h - C * δ n ^ 2 ≤
          traeEmpiricalLoss V P sample split n ω h ∧
        traeEmpiricalLoss V P sample split n ω h ≤
          (5 / 4 : ℝ) * traePopulationLoss V h + C * δ n ^ 2 := by
  exact Classical.choose_spec ((Classical.choose_spec (traeLossEventAtAllocationUniform
    V P sample split hBennett_of_gate B tildeδ hMSC hBound hCommon hComplexity)).2
      δ (fun n => gridConfidence ρ ξ n) hRange hClose hScale n hn
        (trae_grid_allocation_valid ρ ξ hξ n))
end SharedEvent

/-- Under [localized TRAE concentration](hyp:hBennett_of_gate), [a grid ratio
at least one half and less than one](hyp:hρ), [the range condition](hyp:hRange),
[closure of projected residuals in the critic class](hyp:hClose), [mean-square
continuity](hyp:hMSC), [TRAE boundedness and process measurability](hyp:hBound),
[common-null-set bounds](hyp:hCommon), and [critical radius bounds](hyp:hComplexity),
[a positive constant works for every valid failure budget, calibrated accuracy
curve, positive sample size, and squared-norm event: on the common sample
event, all admissible empirical losses lie between one half and five quarters
of their population losses, up to that constant times accuracy squared](goal). -/
-- @node: lem:concentrate-l
lemma concentrate_l
    (hBennett_of_gate : TRAELocalizedConcentration V)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hRange : RangeCondition V) (hClose : ClosenessCondition V)
    (hMSC : MeanSquareContinuity V) (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B)
    (hComplexity : TRAECriticalRadiusBound V tildeδ) :
    ∃ C > 0, ∀ (ξ : ℝ) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1) (δ : ℕ → ℝ)
      (hScale : TRAEScaleCalibration δ tildeδ (fun n => gridConfidence ρ ξ n))
      (n : ℕ) (hn : 0 < n) (normEvent : Set Ω),
        ∀ ω ∈ traeCommonSampleEvent V P sample split ρ ξ B δ tildeδ hBennett_of_gate
          hRange hClose hMSC hBound hCommon hComplexity hξ hScale n hn normEvent,
          ∀ h ∈ V.H,
            (1 / 2 : ℝ) * traePopulationLoss V h - C * δ n ^ 2 ≤
              traeEmpiricalLoss V P sample split n ω h ∧
            traeEmpiricalLoss V P sample split n ω h ≤
              (5 / 4 : ℝ) * traePopulationLoss V h + C * δ n ^ 2 := by
  refine ⟨traeLossComparisonConstant V P sample split B tildeδ hBennett_of_gate
    hMSC hBound hCommon hComplexity,
    (Classical.choose_spec (traeLossEventAtAllocationUniform V P sample split
      hBennett_of_gate B tildeδ hMSC hBound hCommon hComplexity)).1, ?_⟩
  intro ξ hξ δ hScale n hn normEvent ω hω
  exact (traeLossSampleEvent_spec V P sample split ρ ξ B δ tildeδ hBennett_of_gate
    hRange hClose hMSC hBound hCommon hComplexity hξ hScale n hn).2.2 ω hω.1

/-- Assume [localized TRAE concentration](hyp:hBennett_of_gate), [localized
squared-norm comparisons](hyp:hNorm_of_gate), [a grid ratio at least one half
and less than one](hyp:hρ), [a failure budget strictly between zero and one](hyp:hξ),
[the range condition](hyp:hRange), [admissibility of the minimum-norm solution](hyp:hRealizable),
[closure of projected residuals in the critic class](hyp:hClose), [mean-square
continuity](hyp:hMSC), [TRAE boundedness and process measurability](hyp:hBound),
[common-null-set bounds](hyp:hCommon), [critical radius bounds](hyp:hComplexity),
and [scale calibration to the grid allocation](hyp:hScale). Then [there is a
positive constant such that, for every positive sample size, a squared-norm
event can be chosen whose intersection with the selected loss event is
measurable, has probability at least one minus the failure budget, and supports
the simultaneous TRAE loss, squared-norm, and zero-representative comparisons
with that constant](goal). -/
lemma traeCommonEvent_constructed
    (hBennett_of_gate : TRAELocalizedConcentration V)
    (hNorm_of_gate : SquaredNormLocalizedComparison V P sample split)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (hRange : RangeCondition V) (hRealizable : H0MemHypothesisClass V)
    (hClose : ClosenessCondition V) (hMSC : MeanSquareContinuity V)
    (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B) (hComplexity : TRAECriticalRadiusBound V tildeδ)
    (hScale : TRAEScaleCalibration δ tildeδ (fun n => gridConfidence ρ ξ n)) :
    ∃ C > 0, ∀ (n : ℕ) (hn : 0 < n), ∃ normEvent : Set Ω,
      let E := traeCommonSampleEvent V P sample split ρ ξ B δ tildeδ hBennett_of_gate
        hRange hClose hMSC hBound hCommon hComplexity hξ hScale n hn normEvent
      MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧ TRAEComparisonsOn V P sample split δ n E C := by
  obtain ⟨Cf, hCf, hLossOnCommon⟩ := concentrate_l V P sample split ρ B tildeδ
    hBennett_of_gate hρ hRange hClose hMSC hBound hCommon hComplexity
  obtain ⟨Cn, hCn, hNormEvents⟩ := trae_squared_norm_at_allocation V P sample split
    hNorm_of_gate B tildeδ δ (fun n => gridConfidence ρ ξ n)
    hBound hCommon hRealizable hComplexity hScale
  let C := Cf + Cn + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hCfC : Cf ≤ C := by dsimp [C]; linarith
  have hCnC : Cn ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro n hn
  have hk : (1 : ℝ) ≤ (terminalIndex ρ n + 1 : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have hValid : gridConfidence ρ ξ n ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · unfold gridConfidence; positivity [hξ.1]
    · unfold gridConfidence
      apply (div_lt_iff₀ (by positivity)).2
      norm_num only [Nat.cast_add, Nat.cast_one, one_mul]
      linarith only [hk, hξ.2]
  let El := traeLossSampleEvent V P sample split ρ ξ B δ tildeδ hBennett_of_gate
    hRange hClose hMSC hBound hCommon hComplexity hξ hScale n hn
  obtain ⟨hEl, hpl, _⟩ := traeLossSampleEvent_spec V P sample split ρ ξ B δ tildeδ
    hBennett_of_gate hRange hClose hMSC hBound hCommon hComplexity hξ hScale n hn
  change MeasurableSet El at hEl
  change 1 - gridConfidence ρ ξ n / 2 ≤ P.real El at hpl
  obtain ⟨En, hEn, hpn, hnorm⟩ := hNormEvents n hn hValid
  let E := traeCommonSampleEvent V P sample split ρ ξ B δ tildeδ hBennett_of_gate
    hRange hClose hMSC hBound hCommon hComplexity hξ hScale n hn En
  have hE : MeasurableSet E := hEl.inter hEn
  have hprob : 1 - ξ ≤ P.real E := by
    have hρpos : 0 < ρ := by linarith only [hρ.1]
    have hlogden : 0 < Real.log (1 / ρ) :=
      Real.log_pos ((lt_div_iff₀ hρpos).2 (by linarith only [hρ.2]))
    have hnone : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hkpos : 0 < terminalIndex ρ n := by
      apply Nat.ceil_pos.mpr
      exact div_pos (Real.log_pos (by nlinarith only [hnone])) hlogden
    have hk2 : (2 : ℝ) ≤ (terminalIndex ρ n + 1 : ℝ) := by
      exact_mod_cast (show 2 ≤ terminalIndex ρ n + 1 by omega)
    have hbudget : 2 * gridConfidence ρ ξ n ≤ ξ := by
      unfold gridConfidence
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity)).2
      norm_num only [Nat.cast_add, Nat.cast_one]
      nlinarith only [hk2, hξ.1]
    have hu := measureReal_union_le (μ := P) Elᶜ Enᶜ
    rw [← Set.compl_inter] at hu
    change P.real Eᶜ ≤ P.real Elᶜ + P.real Enᶜ at hu
    linarith [hValid.1, probReal_add_probReal_compl (μ := P) hEl,
      probReal_add_probReal_compl (μ := P) hEn,
      probReal_add_probReal_compl (μ := P) hE]
  have hd : 0 ≤ δ n :=
    (show 0 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) by positivity).trans
      ((le_max_right _ _).trans (hScale.1 n hn))
  have hloss (ω : Ω) (hω : ω ∈ E) (h : V.Hbar.toSubmodule) (hh : h ∈ V.H) :
      (1 / 2 : ℝ) * traePopulationLoss V h - C * δ n ^ 2 ≤
        traeEmpiricalLoss V P sample split n ω h ∧
      traeEmpiricalLoss V P sample split n ω h ≤
        (5 / 4 : ℝ) * traePopulationLoss V h + C * δ n ^ 2 := by
    have hb := hLossOnCommon ξ hξ δ hScale n hn En ω hω h hh
    have hc := mul_le_mul_of_nonneg_right hCfC (sq_nonneg (δ n))
    constructor <;> linarith only [hb.1, hb.2, hc]
  refine ⟨En, hE, hprob, ?_⟩
  intro ω hω
  refine ⟨hloss ω hω, ?_, ?_⟩
  · intro h hh
    exact ((hnorm ω hω.2).2 h hh).trans (mul_le_mul_of_nonneg_right hCnC
      (add_nonneg (mul_nonneg hd (norm_nonneg _)) (sq_nonneg _)))
  · refine ⟨?_, (hnorm ω hω.2).1⟩
    have hz := (hloss ω hω (minNormSolution V) hRealizable).2
    simpa only [traePopulationLoss_eq V hRange hClose _ hRealizable,
      sub_self, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
      zero_add] using hz

/-- Assume [localized TRAE concentration](hyp:hBennett_of_gate), [localized
squared-norm comparisons](hyp:hNorm_of_gate), [a grid ratio at least one half
and less than one](hyp:hρ), [a failure budget strictly between zero and one](hyp:hξ),
[the range condition](hyp:hRange), [admissibility of the minimum-norm solution](hyp:hRealizable),
[closure of projected residuals in the critic class](hyp:hClose), [mean-square
continuity](hyp:hMSC), [TRAE boundedness and process measurability](hyp:hBound),
[common-null-set bounds](hyp:hCommon), [critical radius bounds](hyp:hComplexity),
and [scale calibration to the grid allocation](hyp:hScale). Then [a single
positive constant works for every positive sample size, with a measurable event
of probability at least one minus the failure budget on which all TRAE loss,
squared-norm, and zero-representative comparisons hold](goal). -/
-- @node: traeCommonEvent
lemma traeCommonEvent
    (hBennett_of_gate : TRAELocalizedConcentration V)
    (hNorm_of_gate : SquaredNormLocalizedComparison V P sample split)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (hRange : RangeCondition V) (hRealizable : H0MemHypothesisClass V)
    (hClose : ClosenessCondition V) (hMSC : MeanSquareContinuity V)
    (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B) (hComplexity : TRAECriticalRadiusBound V tildeδ)
    (hScale : TRAEScaleCalibration δ tildeδ (fun n => gridConfidence ρ ξ n)) :
    ∃ C > 0, ∀ n : ℕ, 0 < n → ∃ E : Set Ω,
      MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧ TRAEComparisonsOn V P sample split δ n E C := by
  obtain ⟨C, hC, hevents⟩ := traeCommonEvent_constructed V P sample split ρ ξ B δ tildeδ
    hBennett_of_gate hNorm_of_gate hρ hξ hRange hRealizable hClose hMSC hBound hCommon hComplexity hScale
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨normEvent, hE, hp, hcomp⟩ := hevents n hn
  exact ⟨traeCommonSampleEvent V P sample split ρ ξ B δ tildeδ hBennett_of_gate
    hRange hClose hMSC hBound hCommon hComplexity hξ hScale n hn normEvent, hE, hp, hcomp⟩

end Papers.TsAdaptiveEstimationInference
