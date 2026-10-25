module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAEStrong
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAEPropagation
/-! Accepted stability from explicit strong variance propagation. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter
open scoped Topology
variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]
  (V : IVWorld 𝒲 𝒳 𝒵) (P : Measure Ω) [IsProbabilityMeasure P]
  (sample : AnalysisSample V P) (split : SampleSplit)
variable (ρ ξ B β : ℝ) (w₀ : V.Hbar.toSubmodule)
  (δ ν baseδ baseν : ℕ → ℝ) (tildeδ : ℕ → ℝ → ℝ)
  (κδ κν c₀ CG Cm : ℝ) (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ)
  (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
  (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule)
  (c : ℝ) (t : ℕ)
/-- Suppose [the grid is admissible](hyp:hρ), [the horizon is positive](hyp:ht),
[the oracle multiplier is at least two](hyp:hb), [the range condition](hyp:hRange),
[the source condition with the given exponent and witness](hyp:hSource),
[realizability of the minimum-norm solution](hyp:hRealizable), [closeness](hyp:hClose),
[boundedness](hyp:hBound), and [a common almost-sure envelope](hyp:hCommon) hold.
If [the concentration constant is positive](hyp:hCevent), [the preliminary radius
is nonnegative at positive sample sizes](hyp:hradius), [that radius is dominated
by the accuracy curve](hyp:hdom), [population iterates are realizable](hyp:hIterRealizable),
and [empirical iterative minima are attained](hyp:hIterMinima), [one positive
constant, uniform in confidence, sample size, event and penalty, gives all five
stability bounds on any concentration event whose oracle is above the grid floor:
projected estimation error, strong estimation error, combined empirical-to-population
error, population projected error, and empirical-to-population norm error are
controlled by empirical loss plus noise, with the stated penalty factors and source exponent](goal). -/
-- @node: iter_trae_accepted_stability_local
lemma iter_trae_accepted_stability_local
    (ρ c b β B Cevent : ℝ) (t : ℕ) (δ radius : ℕ → ℝ)
    (w₀ : V.Hbar.toSubmodule)
    (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (hρ : GridDomain ρ) (ht : 1 ≤ t) (hb : 2 ≤ b)
    (hRange : RangeCondition V) (hSource : BetaSourceCondition V β w₀)
    (hRealizable : H0MemHypothesisClass V) (hClose : ClosenessCondition V)
    (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B) (hCevent : 0 < Cevent)
    (hradius : ∀ n, 0 < n → 0 ≤ radius n)
    (hdom : ∀ n, 0 < n → radius n ≤ δ n)
    (hIterRealizable : IterRealizableTRAE V ρ c b β t δ)
    (hIterMinima : IterTRAEMinimaAttained V P sample split ρ t iter) :
      ∃ C > 0, ∀ ξ : ℝ, ∀ n : ℕ, 0 < n →
      (hOracleDefined : gridValue ρ (terminalIndex ρ n) ≤
        c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))) →
      ∀ E : Set Ω, MeasurableSet E → 1 - ξ ≤ P.real E →
      IterTRAEConcentrationOn V P sample split ρ c b β t δ radius iter n E Cevent →
      ∀ ω ∈ E,
      ∀ lam : ℝ, IterTRAEStableBranch ρ c b β t δ n lam →
        ‖projCondExpOp V (iter n t lam ω - minNormSolution V)‖ ^ 2 ≤ C * (traeEmpiricalLoss V P sample split n ω (iter n t lam ω) + iterTraeNoiseLevel b (δ n) lam) ∧
        ‖iter n t lam ω - minNormSolution V‖ ^ 2 ≤ C * ((traeEmpiricalLoss V P sample split n ω (iter n t lam ω) + iterTraeNoiseLevel b (δ n) lam) / lam + (traeEmpiricalLoss V P sample split n ω (iter n t lam ω) + iterTraeNoiseLevel b (δ n) lam) ^ (β / (β + 1))) ∧
        lam * ‖iter n t lam ω - populationIterate V lam t‖ ^ 2 +
          ‖projCondExpOp V (iter n t lam ω - populationIterate V lam t)‖ ^ 2 ≤ C * (traeEmpiricalLoss V P sample split n ω (iter n t lam ω) + iterTraeNoiseLevel b (δ n) lam) ∧
        ‖projCondExpOp V (populationIterate V lam t - minNormSolution V)‖ ^ 2 ≤ C * (traeEmpiricalLoss V P sample split n ω (iter n t lam ω) + iterTraeNoiseLevel b (δ n) lam) ∧
        ‖iter n t lam ω - populationIterate V lam t‖ ^ 2 ≤ C / lam * (traeEmpiricalLoss V P sample split n ω (iter n t lam ω) + iterTraeNoiseLevel b (δ n) lam) := by
  let A := 16 * ((Cevent ^ 2 + 2 * Cevent + 1) * (B + 1) + 2 * Cevent + 1) ^ 2
  let Dp := 2 * A + 1
  let Cp := Dp ^ t + 1
  have hDp : 1 ≤ Dp := by
    have : 0 ≤ A := by dsimp [A]; positivity
    dsimp [Dp]; linarith
  have hCp : 0 < Cp := by dsimp [Cp, Dp, A]; positivity
  obtain ⟨Cb, hCb, hbias⟩ := iter_bias V β w₀ hRange hSource t ht
  let a := β / (β + 1)
  let K := 8 * Cevent ^ 2 + 6 * Cevent + 1
  let D := 2 * (Cevent + 1) + K * (Cp + 1) + 1
  let S := ‖w₀‖ ^ (2 / (β + 1)) * (8 * D) ^ a
  let C := 16 * D + 2 * S + 1
  have ha : 0 ≤ a := by dsimp [a]; positivity [hSource.1]
  have hK : 0 < K := by dsimp [K]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hDC : 8 * D ≤ C := by dsimp [C]; linarith only [hD, hS]
  refine ⟨C, hC, ?_⟩
  intro ξ n hn hOracle E hE hprob hEvent ω hω lam hbranch
  obtain ⟨hl, hs, hstable⟩ := hbranch
  have hlam : 0 < lam := by
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hl
    exact mul_pos (by norm_num) (pow_pos (by linarith only [hρ.1]) k)
  have hEst := (hIterMinima n hn lam hl).1
  have hh := (hEst.2 t ht le_rfl ω).1
  have hStar := hIterRealizable n hOracle t ht le_rfl lam hl hs
  have hr : 0 ≤ radius n := hradius n hn
  have hδ : radius n ≤ δ n := hdom n hn
  have hrsq := pow_le_pow_left₀ hr hδ 2
  have hp : iterStrongVariance V (t - 1) lam (iter n (t - 1) lam ω) ^ 2 ≤
      Cp * b * δ n ^ 2 / lam ^ 2 := by
    have hi := iter_trae_strong_variance_explicit V P sample split ρ c b β B Cevent t
      δ radius iter hρ hRange hClose hBound hCommon hCevent hIterRealizable hIterMinima
      n hn hr hOracle E hEvent ω hω lam hl hs (t - 1) (by omega)
    change _ ≤ Dp ^ (t - 1) * (radius n ^ 2 / lam ^ 2) at hi
    have hpow : Dp ^ (t - 1) ≤ Dp ^ t := pow_le_pow_right₀ hDp (by omega)
    have hcoef : Dp ^ (t - 1) ≤ Cp * b := by
      have hnonneg : 0 ≤ Dp ^ t := by positivity
      dsimp only [Cp]
      nlinarith only [hpow, hb, hnonneg, mul_nonneg hnonneg (show 0 ≤ b - 1 by linarith)]
    calc
      _ ≤ Dp ^ (t - 1) * (radius n ^ 2 / lam ^ 2) := hi
      _ ≤ Cp * b * (δ n ^ 2 / lam ^ 2) :=
        mul_le_mul hcoef (div_le_div_of_nonneg_right hrsq (sq_nonneg lam))
          (by positivity) (by positivity)
      _ = _ := by ring
  have hp' : lam * iterStrongVariance V (t - 1) lam (iter n (t - 1) lam ω) ^ 2 ≤
      Cp * (b * δ n ^ 2 / lam) := by
    have hi := mul_le_mul_of_nonneg_left hp hlam.le
    have he : lam * (Cp * b * δ n ^ 2 / lam ^ 2) = Cp * (b * δ n ^ 2 / lam) := by
      field_simp
    rwa [he] at hi
  have hnoise : iterTraeNoiseLevel b (δ n) lam = δ n ^ 2 + b * δ n ^ 2 / lam := by
    dsimp only [iterTraeNoiseLevel, iterTraeScale]
    rw [min_eq_right]
    apply (div_le_iff₀ hlam).2
    have hi := (Real.sqrt_le_iff).1 hstable |>.2
    nlinarith only [hi]
  let Q := traeEmpiricalLoss V P sample split n ω (iter n t lam ω) +
    iterTraeNoiseLevel b (δ n) lam
  have hL : 0 ≤ traeEmpiricalLoss V P sample split n ω (iter n t lam ω) :=
    traeEmpiricalLoss_nonneg V P sample split hRealizable hClose n ω _ ((hEvent.1 ω hω).2.2.2)
  have hb' : 0 ≤ b := hb.trans' (by norm_num)
  have hN : 0 ≤ b * δ n ^ 2 / lam := by positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; rw [hnoise]; positivity
  have htotal : ‖projCondExpOp V (iter n t lam ω - minNormSolution V)‖ ^ 2 ≤ D * Q := by
    have hi := ((hEvent.1 ω hω).1 _ hh).1
    rw [traePopulationLoss_eq V hRange hClose _ hh] at hi
    have hcoeff : 2 * (Cevent + 1) ≤ D := by
      dsimp [D]; nlinarith only [mul_nonneg hK.le (show 0 ≤ Cp + 1 by positivity)]
    have hc := mul_le_mul_of_nonneg_right hcoeff hQ
    dsimp only [Q] at hc
    rw [hnoise] at hc
    dsimp only [Q]
    rw [hnoise]
    nlinarith only [hi, hrsq, hc, hL, hN,
      mul_le_mul_of_nonneg_left hrsq hCevent.le,
      mul_nonneg hCevent.le hL, mul_nonneg (show 0 ≤ 2 * (Cevent + 1) by positivity) hN]
  have href := iter_trae_refined_curvature V P sample split ρ c b β Cevent t n δ radius
    iter E hRange hClose hCevent.le hOracle hEvent ω hω lam hl hs hlam ht hStar hEst
  have href' : (3 / 4 : ℝ) * lam * iterStrongVariance V t lam (iter n t lam ω) ^ 2 +
      iterWeakVariance V t lam (iter n t lam ω) ^ 2 ≤ iterWeakBias V t lam ^ 2 / 4 + D * Q := by
    have hi := mul_le_mul_of_nonneg_left (add_le_add hrsq hp') hK.le
    have hcoeff : 1 + K * (Cp + 1) ≤ D := by dsimp [D]; linarith only [hCevent]
    have hc := mul_le_mul_of_nonneg_right hcoeff hQ
    dsimp only [Q] at hc
    rw [hnoise] at hc
    change _ ≤ _ + _ + K * _ at href
    dsimp only [Q]
    rw [hnoise]
    nlinarith only [href, hi, hc, hL, hN, sq_nonneg (δ n),
      mul_nonneg (mul_nonneg hK.le hCp.le) (sq_nonneg (δ n)), mul_nonneg hK.le hL,
      mul_nonneg (mul_nonneg hK.le hCp.le) hL, mul_nonneg hK.le hN]
  have htri : iterWeakBias V t lam ^ 2 ≤
      2 * ‖projCondExpOp V (iter n t lam ω - minNormSolution V)‖ ^ 2 +
      2 * iterWeakVariance V t lam (iter n t lam ω) ^ 2 := by
    have he : projCondExpOp V (populationIterate V lam t - minNormSolution V) =
        projCondExpOp V (iter n t lam ω - minNormSolution V) -
          projCondExpOp V (iter n t lam ω - populationIterate V lam t) := by
      simp only [map_sub]; abel
    dsimp only [iterWeakBias, iterWeakVariance]
    rw [he]
    simpa only [mul_add] using
      (pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 2).trans add_sq_le
  have hv : iterWeakBias V t lam ^ 2 ≤ 8 * D * Q := by
    nlinarith only [htri, htotal, href', mul_nonneg hlam.le
      (sq_nonneg (iterStrongVariance V t lam (iter n t lam ω)))]
  have hvar : lam * iterStrongVariance V t lam (iter n t lam ω) ^ 2 +
      iterWeakVariance V t lam (iter n t lam ω) ^ 2 ≤ 8 * D * Q := by
    nlinarith only [href', hv, sq_nonneg (iterWeakVariance V t lam (iter n t lam ω)),
      mul_nonneg hD.le hQ]
  have he : iterStrongVariance V t lam (iter n t lam ω) ^ 2 ≤ 8 * D * Q / lam := by
    apply (le_div_iff₀ hlam).2
    nlinarith only [hvar, sq_nonneg (iterWeakVariance V t lam (iter n t lam ω))]
  have hsb : ‖populationIterate V lam t - minNormSolution V‖ ^ 2 ≤ S * Q ^ a := by
    have hi := (hbias lam hlam).2.2.2.2.2
    have heq : ‖projCondExpOp V (populationIterate V lam t - minNormSolution V)‖ ^
        (2 * β / (β + 1)) = (iterWeakBias V t lam ^ 2) ^ a := by
      dsimp only [iterWeakBias]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
      congr 1
      dsimp [a]; ring
    rw [heq] at hi
    have hm := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (sq_nonneg _) hv ha)
      (show 0 ≤ ‖w₀‖ ^ (2 / (β + 1)) by positivity)
    rw [Real.mul_rpow (by positivity : 0 ≤ 8 * D) hQ] at hm
    exact hi.trans (by simpa only [S, mul_assoc] using hm)
  have hstrongTotal : ‖iter n t lam ω - minNormSolution V‖ ^ 2 ≤ C * (Q / lam + Q ^ a) := by
    have heq : iter n t lam ω - minNormSolution V =
        (iter n t lam ω - populationIterate V lam t) +
          (populationIterate V lam t - minNormSolution V) := by abel
    have htri' : ‖iter n t lam ω - minNormSolution V‖ ^ 2 ≤
        2 * iterStrongVariance V t lam (iter n t lam ω) ^ 2 +
          2 * ‖populationIterate V lam t - minNormSolution V‖ ^ 2 := by
      rw [heq]
      simpa only [mul_add, iterStrongVariance] using
        (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2).trans add_sq_le
    have hc₁ := mul_le_mul_of_nonneg_right
      (show 16 * D ≤ C by dsimp [C]; linarith only [hS]) (show 0 ≤ Q / lam by positivity)
    have hc₂ := mul_le_mul_of_nonneg_right
      (show 2 * S ≤ C by dsimp [C]; linarith only [hD]) (Real.rpow_nonneg hQ a)
    have he' : iterStrongVariance V t lam (iter n t lam ω) ^ 2 ≤ 8 * D * (Q / lam) := by
      simpa only [mul_div_assoc] using he
    nlinarith only [htri', he', hsb, hc₁, hc₂]
  have hc := mul_le_mul_of_nonneg_right hDC hQ
  have hc' := div_le_div_of_nonneg_right hc hlam.le
  dsimp only [iterStrongVariance, iterWeakVariance, iterWeakBias] at hvar hv he
  refine ⟨htotal.trans ?_, hstrongTotal, hvar.trans hc, hv.trans hc, ?_⟩
  · nlinarith only [hc, mul_nonneg hD.le hQ]
  · simpa only [div_mul_eq_mul_div] using he.trans hc'




/-- For [grid ratio](hyp:ρ), [oracle scale](hyp:c), [oracle multiplier](hyp:b),
[source exponent](hyp:β), [iteration horizon](hyp:t), [accuracy curve](hyp:δ), and
[a family of error constants indexed by sample size and penalty](hyp:constants),
[the constant-uniformity requirement](goal) says that any two positive sample
sizes whose oracles are above their grid floors, and any penalties on their stable
branches, have equal error constants. -/
-- @node: ass:pin-203
noncomputable def PinIterTRAEAcceptedConstant (b : ℝ)
    (constants : ℕ → ℝ → ℝ) : Prop :=
  ∀ n n' : ℕ, 0 < n → 0 < n' →
    gridValue ρ (terminalIndex ρ n) ≤
      c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1)) →
    gridValue ρ (terminalIndex ρ n') ≤
      c * (b * δ n' ^ 2) ^ (1 / (qualificationExponent β t + 1)) →
    ∀ lam lam' : ℝ,
      IterTRAEStableBranch ρ c b β t δ n lam →
      IterTRAEStableBranch ρ c b β t δ n' lam' →
      constants n lam = constants n' lam'

/-- For [the instrumental-variable world](hyp:V), [sampling law](hyp:P),
[analysis sample](hyp:sample), [sample split](hyp:split), [grid ratio](hyp:ρ),
[failure budget](hyp:ξ), [source exponent](hyp:β), [oracle scale](hyp:c),
[iteration horizon](hyp:t), [accuracy curve](hyp:δ), [preliminary radius](hyp:baseδ),
[empirical iterates](hyp:iter), [oracle multiplier](hyp:b), [concentration constant](hyp:Cevent),
and [error constant](hyp:C), [the accepted stability requirement](goal) demands,
at every positive sample size and every [oracle above the grid floor](hyp:hOracleDefined),
on each measurable concentration event of the prescribed probability and every stable
penalty, [a projected estimation-error bound by empirical loss plus noise](step:1),
[a norm-error bound using its penalty-scaled and source-power terms](step:2),
[a combined penalty-weighted norm and projected error bound relative to the population iterate](step:3),
[a population-iterate projected error bound](step:4), and
[a norm-error bound relative to the population iterate scaled by inverse penalty](step:5). -/
noncomputable def IterTRAEAcceptedBounds (b Cevent C : ℝ) : Prop :=
      ∀ n : ℕ, 0 < n →
      (hOracleDefined : gridValue ρ (terminalIndex ρ n) ≤
        c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))) →
      ∀ E : Set Ω, MeasurableSet E → 1 - ξ ≤ P.real E →
      IterTRAEConcentrationOn V P sample split ρ c b β t δ baseδ iter n E Cevent →
      ∀ ω ∈ E,
      ∀ lam : ℝ, IterTRAEStableBranch ρ c b β t δ n lam →
        ‖projCondExpOp V (iter n t lam ω - minNormSolution V)‖ ^ 2 ≤ C * (traeEmpiricalLoss V P sample split n ω (iter n t lam ω) + iterTraeNoiseLevel b (δ n) lam) ∧
        ‖iter n t lam ω - minNormSolution V‖ ^ 2 ≤ C * ((traeEmpiricalLoss V P sample split n ω (iter n t lam ω) + iterTraeNoiseLevel b (δ n) lam) / lam + (traeEmpiricalLoss V P sample split n ω (iter n t lam ω) + iterTraeNoiseLevel b (δ n) lam) ^ (β / (β + 1))) ∧
        lam * ‖iter n t lam ω - populationIterate V lam t‖ ^ 2 +
          ‖projCondExpOp V (iter n t lam ω - populationIterate V lam t)‖ ^ 2 ≤ C * (traeEmpiricalLoss V P sample split n ω (iter n t lam ω) + iterTraeNoiseLevel b (δ n) lam) ∧
        ‖projCondExpOp V (populationIterate V lam t - minNormSolution V)‖ ^ 2 ≤ C * (traeEmpiricalLoss V P sample split n ω (iter n t lam ω) + iterTraeNoiseLevel b (δ n) lam) ∧
        ‖iter n t lam ω - populationIterate V lam t‖ ^ 2 ≤ C / lam * (traeEmpiricalLoss V P sample split n ω (iter n t lam ω) + iterTraeNoiseLevel b (δ n) lam)

/-- Under [localized scalar concentration](hyp:hBennett_of_gate),
[anchored concentration](hyp:hAnchored_of_gate), [fixed-center squared-loss concentration](hyp:hFixedSq_of_gate),
[a grid ratio in $[1/2,1)$](hyp:hρ), [a positive iteration horizon](hyp:ht),
[a positive oracle scale](hyp:hc), [integrable squared moments bounded by the
given continuity constant times squared critic norm](hyp:hMSCAt),
[the analogous bound for critic increments](hyp:hIterMSCAt), and
[a positive concentration constant](hyp:hCevent), [a positive inflation threshold
exists that ensures all five accepted stability bounds with the terminal multiplier,
uniformly in confidence after calibration, provided the range condition,
the source condition, solution realizability,
closeness, boundedness, a common envelope,
critical-radius control, attainment of candidate minima,
sufficient calibrated inflation, deterministic calibration,
iterative population realizability, attainment of iterative minima,
anchored-loss process measurability, boundedness along the iterative oracle segment,
and calibration of the preliminary radius to iteration-grid confidence hold](goal). -/
-- @node: lem:iter-trae-accepted-stability
lemma iter_trae_accepted_stability
    (hBennett_of_gate : TRAELocalizedConcentration V)
    (hAnchored_of_gate : IterTRAEAnchoredLocalizedConcentration V)
    (hFixedSq_of_gate : IterTRAEFixedCenterSquaredLossConcentration V)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1)
    (ht : 1 ≤ t)
    (hc : 0 < c)
    (C_m C_iter : ℝ)
    (hMSCAt : ∀ f ∈ V.F, Integrable (fun w => V.m f w ^ 2) V.law ∧
      (∫ w, V.m f w ^ 2 ∂V.law) ≤ C_m * ‖f‖ ^ 2)
    (hIterMSCAt : ∀ f ∈ V.F, ∀ f' ∈ V.F,
      Integrable (fun w => V.m (f - f') w ^ 2) V.law ∧
      (∫ w, V.m (f - f') w ^ 2 ∂V.law) ≤ C_iter * ‖f - f'‖ ^ 2)
    (Cevent : ℝ) (hCevent : 0 < Cevent)
    : ∃ required > 0, ∀ (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ),
      ∀ (β : ℝ) (w₀ : V.Hbar.toSubmodule)
      (δ ν : ℕ → ℝ),
      (hRange : RangeCondition V) →
      (hSource : BetaSourceCondition V β w₀) →
      (hRealizable : H0MemHypothesisClass V) →
      (hClose : ClosenessCondition V) →
      (hBound : TRAEBoundedness V B) → (hCommon : TRAECommonNullSetBoundedness V B) →
      (hComplexity : TRAECriticalRadiusBound V tildeδ) →
      (hMinima : TRAEMinimaAttained V P sample split ρ candidate) →
      (hInflation : CalibratedValidBounds δ ν baseδ baseν (κ₀ B c₀ CG Cm).1 (κ₀ B c₀ CG Cm).2 required) →
      (hDeterministic : CalibrationDeterministic δ ν) →
      (hIterRealizable : IterRealizableTRAE V ρ c (iterTraeMultipliers 𝒲 𝒳 𝒵 Ω B C_m C_iter t) β t δ) →
      (hIterMinima : IterTRAEMinimaAttained V P sample split ρ t iter) →
      (hProcesses : IterTRAEAnchoredLossProcessesMeasurable V B ρ t (fun n => c * ((iterTraeMultipliers 𝒲 𝒳 𝒵 Ω B C_m C_iter t) * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1)))) →
      (hIterBound : TRAEBoundedness V B (some (ρ, t, (fun n => c * ((iterTraeMultipliers 𝒲 𝒳 𝒵 Ω B C_m C_iter t) * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1)))))) →
      ∃ C > 0, ∀ ξ : ℝ, ξ ∈ Set.Ioo (0 : ℝ) 1 →
      (hScale : TRAEScaleCalibration baseδ tildeδ (fun n => iterGridConfidence ρ ξ n t)) →
      IterTRAEAcceptedBounds (V := V) (P := P) (sample := sample)
        (split := split) (ρ := ρ) (ξ := ξ) (β := β) (c := c) (t := t)
        (δ := δ) (baseδ := baseδ) (iter := iter) (iterTraeMultipliers 𝒲 𝒳 𝒵 Ω B C_m C_iter t) Cevent C := by
  classical
  let b := iterTraeMultipliers 𝒲 𝒳 𝒵 Ω B C_m C_iter t
  have hb : 2 ≤ b :=
    (Classical.choose_spec (iter_trae_strong_propagation
      (𝒲 := 𝒲) (𝒳 := 𝒳) (𝒵 := 𝒵) (Ω := Ω)) V B C_m C_iter
        hMSCAt hIterMSCAt).2.2.1 t ht
  refine ⟨1, zero_lt_one, ?_⟩
  intro κ₀
  let κδ := (κ₀ B c₀ CG Cm).1
  let κν := (κ₀ B c₀ CG Cm).2
  intro β w₀ δ ν hRange hSource hRealizable hClose hBound hCommon hComplexity
    hMinima hInflation hDeterministic hIterRealizable hIterMinima hProcesses hIterBound
  by_cases hRadius : ∀ n : ℕ, 0 < n → 0 ≤ baseδ n
  · have hdom : ∀ n : ℕ, 0 < n → baseδ n ≤ δ n := by
      intro n hn
      rw [hInflation.2.2.2.2.1 n]
      exact le_mul_of_one_le_left (hRadius n hn) hInflation.1
    obtain ⟨C, hC, hlocal⟩ := iter_trae_accepted_stability_local V P sample split
      ρ c b β B Cevent t δ baseδ w₀ iter hρ ht hb hRange hSource hRealizable
      hClose hBound hCommon hCevent hRadius hdom hIterRealizable hIterMinima
    exact ⟨C, hC, fun ξ _ _ => hlocal ξ⟩
  · refine ⟨1, zero_lt_one, ?_⟩
    intro ξ hξ hScale
    exact (hRadius fun n hn => (Real.rpow_nonneg (by positivity) _).trans
      ((le_max_right _ _).trans (hScale.1 n hn))).elim


end Papers.TsAdaptiveEstimationInference
