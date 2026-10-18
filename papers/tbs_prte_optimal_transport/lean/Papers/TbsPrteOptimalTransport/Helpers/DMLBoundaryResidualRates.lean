module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRegularBiasAssembly
public import Papers.TbsPrteOptimalTransport.Helpers.DMLFullProductAssembly
/-! Integrated quadratic control of the binary boundary regression residual.
The envelope includes both adjacent success regressions and the treatment regression,
with the structural zero represented by `positiveValue`. -/
@[expose] public section
set_option linter.style.whitespace false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- Clipping supplies these moments also at the fixed zero and unused indices.
-- @node: fitted_positive_treatment_assignment_memLp
/-- For [an admissible binary nuisance specification](hyp:he), [the treatment
regression and assignment probability at any index, extended by zero outside
positive levels, both have finite second moments under the covariate law](goal). -/
lemma fitted_positive_treatment_assignment_memLp (L : LevelData Z X)
    (e : NuisanceBin L) (he : BinAdmissible M L e) (i : ℕ) :
    MemLp (positiveValue e.pLev i) 2 (xLaw M) ∧
      MemLp (positiveValue e.piLev i) 2 (xLaw M) := by
  have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  change MemLp (fun x => positiveValue e.pLev i x) 2 (xLaw M) ∧
    MemLp (fun x => positiveValue e.piLev i x) 2 (xLaw M)
  by_cases hi : 1 ≤ i ∧ i ≤ L.K
  · have hm := he.2.2.2.1 ⟨i, hi⟩
    simp only [positiveValue, dif_pos hi]
    constructor
    · apply MemLp.of_bound (by first | fun_prop | exact hm.1.aestronglyMeasurable) 1
      filter_upwards [he.2.2.1 ⟨i, hi⟩] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg hx.1.1]
      exact hx.1.2
    · apply MemLp.of_bound (by first | fun_prop | exact hm.2.2.aestronglyMeasurable) 1
      filter_upwards [he.2.2.1 ⟨i, hi⟩] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg hx.2.2.1]
      exact hx.2.2.2
  · simp only [positiveValue, dif_neg hi]
    exact ⟨MemLp.zero, MemLp.zero⟩

-- @node: binaryBoundaryResidualEnvelope
/-- For [a propensity-level structure](hyp:L), [reference and fitted binary
nuisances](hyp:e0,e), [a denominator scale](hyp:c), [a boundary index](hyp:k), and
[a covariate value](hyp:x), the [binary boundary residual envelope](goal) is the
sum of the next-level assignment-probability error times the sum of the next-level
success and treatment regression errors, and the current-level assignment error
times the current-level success regression error, all divided by the denominator
scale; every error is absolute and coordinates outside positive levels are zero. -/
noncomputable def binaryBoundaryResidualEnvelope (L : LevelData Z X)
    (e0 e : NuisanceBin L) (c : ℝ) (k : ℕ) (x : X) : ℝ :=
  |positiveValue e.piLev (k+1) x - positiveValue e0.piLev (k+1) x| *
    (|positiveValue e.P1 (k+1) x - positiveValue e0.P1 (k+1) x| +
      |positiveValue e.pLev (k+1) x - positiveValue e0.pLev (k+1) x|) / c +
  |positiveValue e.piLev k x - positiveValue e0.piLev k x| *
    |positiveValue e.P1 k x - positiveValue e0.P1 k x| / c

-- This is the EB input of the fractional-score bias envelope, derived from
-- the fitted denominator cancellation rather than imposed as a bias gate.
-- @node: binary_boundary_residual_envelope_ae
/-- If [the denominator bound is positive](hyp:hc) and [all fitted assignment
probabilities exceed it almost everywhere](hyp:hclip), [the absolute discrepancy
between the adjacent inverse-weighted success residuals minus the next treatment
residual and the fitted-minus-reference boundary displacement is almost everywhere
bounded by the binary boundary residual envelope](goal). -/
lemma binary_boundary_residual_envelope_ae (L : LevelData Z X)
    (e0 e : NuisanceBin L) (c : ℝ) (hc : 0 < c) (k : ℕ)
    (hclip : ∀ i, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) :
    ∀ᵐ x ∂xLaw M,
      let rP := fun i => positiveValue e0.piLev i x *
        (positiveValue e0.P1 i x - positiveValue e.P1 i x) / positiveValue e.piLev i x
      let rp := fun i => positiveValue e0.piLev i x *
        (positiveValue e0.pLev i x - positiveValue e.pLev i x) / positiveValue e.piLev i x
      |(rP (k+1) - rP k - rp (k+1)) -
        ((positiveValue e.pLev (k+1) x - binFullJ L e k x) -
          (positiveValue e0.pLev (k+1) x - binFullJ L e0 k x))| ≤
        binaryBoundaryResidualEnvelope L e0 e c k x := by
  filter_upwards [ae_all_iff.mpr hclip] with x hx
  exact fitted_regular_boundary_residual_error_bound L e0 e x c hc hx k

-- Cauchy-Schwarz turns all three denominator/regression products into L2 errors.
-- @node: binary_boundary_residual_envelope_integrated_bound
/-- For [admissible reference](hyp:he0) and [fitted binary nuisances](hyp:he),
assume [a positive denominator scale](hyp:hc), [a nonnegative regression-error
bound](hyp:hreg), and [a nonnegative assignment-error bound](hyp:hwt). If the
L2 errors of [next-level success are at most the regression bound](hyp:hPnext),
[current-level success are at most the regression bound](hyp:hPprev), and
[next-level treatment are at most the regression bound](hyp:hpnext), while
[next-level assignment errors are at most the assignment bound](hyp:hpinext) and
[current-level assignment errors are at most the assignment bound](hyp:hpiprev),
[the boundary residual envelope is integrable
and its expectation is at most three times the product of these error bounds
divided by the denominator scale](goal). -/
lemma binary_boundary_residual_envelope_integrated_bound (L : LevelData Z X)
    (e0 e : NuisanceBin L) (he0 : BinAdmissible M L e0) (he : BinAdmissible M L e)
    (c reg wt : ℝ) (hc : 0 < c) (hreg : 0 ≤ reg) (hwt : 0 ≤ wt) (k : ℕ)
    (hPnext : finiteL2Error M (positiveValue e.P1 (k+1)) (positiveValue e0.P1 (k+1)) ≤ reg)
    (hPprev : finiteL2Error M (positiveValue e.P1 k) (positiveValue e0.P1 k) ≤ reg)
    (hpnext : finiteL2Error M (positiveValue e.pLev (k+1)) (positiveValue e0.pLev (k+1)) ≤ reg)
    (hpinext : finiteL2Error M (positiveValue e.piLev (k+1)) (positiveValue e0.piLev (k+1)) ≤ wt)
    (hpiprev : finiteL2Error M (positiveValue e.piLev k) (positiveValue e0.piLev k) ≤ wt) :
    Integrable (binaryBoundaryResidualEnvelope L e0 e c k) (xLaw M) ∧
      (∫ x, binaryBoundaryResidualEnvelope L e0 e c k x ∂xLaw M) ≤
        (3 / c) * (reg * wt) := by
  let dPi := fun i x => positiveValue e.piLev i x - positiveValue e0.piLev i x
  let dP := fun i x => positiveValue e.P1 i x - positiveValue e0.P1 i x
  let dp := fun i x => positiveValue e.pLev i x - positiveValue e0.pLev i x
  have hPi (i : ℕ) : MemLp (dPi i) 2 (xLaw M) :=
    ((fitted_positive_treatment_assignment_memLp M L e he i).2).sub
      (fitted_positive_treatment_assignment_memLp M L e0 he0 i).2
  have hS (i : ℕ) : MemLp (dP i) 2 (xLaw M) :=
    (fitted_positive_success_memLp M L e he i).sub
      (fitted_positive_success_memLp M L e0 he0 i)
  have hT (i : ℕ) : MemLp (dp i) 2 (xLaw M) :=
    ((fitted_positive_treatment_assignment_memLp M L e he i).1).sub
      (fitted_positive_treatment_assignment_memLp M L e0 he0 i).1
  have iS (i : ℕ) : Integrable (fun x => |dPi i x| * |dP i x|) (xLaw M) := by
    simpa only [Pi.mul_apply, abs_mul] using ((hPi i).integrable_mul (hS i)).abs
  have iT (i : ℕ) : Integrable (fun x => |dPi i x| * |dp i x|) (xLaw M) := by
    simpa only [Pi.mul_apply, abs_mul] using ((hPi i).integrable_mul (hT i)).abs
  have bS (i : ℕ)
      (hiPi : finiteL2Error M (positiveValue e.piLev i) (positiveValue e0.piLev i) ≤ wt)
      (hiP : finiteL2Error M (positiveValue e.P1 i) (positiveValue e0.P1 i) ≤ reg) :
      (∫ x, |dPi i x| * |dP i x| ∂xLaw M) ≤ wt * reg := by
    have hb := Causalean.Stat.integral_abs_mul_le_eLpNorm_mul_eLpNorm (hPi i) (hS i)
    rw [← l2Error_eq_eLpNorm M _ _ (hPi i), ← l2Error_eq_eLpNorm M _ _ (hS i)] at hb
    simpa only [abs_mul] using hb.trans
      (mul_le_mul hiPi hiP (Real.sqrt_nonneg _) hwt)
  have bT (i : ℕ)
      (hiPi : finiteL2Error M (positiveValue e.piLev i) (positiveValue e0.piLev i) ≤ wt)
      (hip : finiteL2Error M (positiveValue e.pLev i) (positiveValue e0.pLev i) ≤ reg) :
      (∫ x, |dPi i x| * |dp i x| ∂xLaw M) ≤ wt * reg := by
    have hb := Causalean.Stat.integral_abs_mul_le_eLpNorm_mul_eLpNorm (hPi i) (hT i)
    rw [← l2Error_eq_eLpNorm M _ _ (hPi i), ← l2Error_eq_eLpNorm M _ _ (hT i)] at hb
    simpa only [abs_mul] using hb.trans
      (mul_le_mul hiPi hip (Real.sqrt_nonneg _) hwt)
  have hid : binaryBoundaryResidualEnvelope L e0 e c k =
      (fun x => |dPi (k+1) x| * |dP (k+1) x| / c +
        |dPi (k+1) x| * |dp (k+1) x| / c + |dPi k x| * |dP k x| / c) := by
    funext x
    dsimp only [binaryBoundaryResidualEnvelope, dPi, dP, dp]
    ring
  rw [hid]
  refine ⟨(((iS (k+1)).div_const c).fun_add ((iT (k+1)).div_const c)).fun_add
    ((iS k).div_const c), ?_⟩
  rw [integral_add (((iS (k+1)).div_const c).fun_add ((iT (k+1)).div_const c))
    ((iS k).div_const c), integral_add ((iS (k+1)).div_const c)
    ((iT (k+1)).div_const c)]
  simp only [integral_div]
  calc
    _ ≤ wt * reg / c + wt * reg / c + wt * reg / c := by
      gcongr <;> first | exact bS (k+1) hpinext hPnext |
        exact bT (k+1) hpinext hpnext | exact bS k hpiprev hPprev
    _ = _ := by ring

-- The fixed zero and invalid indices inherit a zero error; rates need only
-- be supplied for the genuine positive nuisance coordinates.
-- @node: nuisanceRates_positiveValue
/-- If [the fitted positive-level coordinates satisfy the finite nuisance
quarter-rate bounds relative to their reference values](hyp:h), [extending those
coordinates by zero at zero and invalid indices preserves the same finite
nuisance rates](goal). -/
lemma nuisanceRates_positiveValue {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (K : ℕ)
    (fit : ℕ → A → PositiveIndex K → X → ℝ) (truth : PositiveIndex K → X → ℝ)
    (h : FiniteNuisanceRates M μ fit truth) :
    FiniteNuisanceRates M μ (fun n a i => positiveValue (fit n a) i)
      (fun i => positiveValue truth i) := by
  intro i
  by_cases hi : 1 ≤ i ∧ i ≤ K
  · have hv (f : PositiveIndex K → X → ℝ) : positiveValue f i = f ⟨i, hi⟩ := by
      funext x
      simp only [positiveValue, dif_pos hi]
    simpa only [hv] using h ⟨i, hi⟩
  · have hz := maxErrors_isLittleOp μ ([] : List Unit) (fun _ _ _ => (0 : ℝ))
      (fun n => ((2*(n+1) : ℕ) : ℝ) ^ (-1/4 : ℝ))
      (fun _ => Real.rpow_pos_of_pos (by positivity) _) (by simp)
    simpa only [positiveValue, dif_neg hi, finiteL2Error, sub_self, zero_pow (by norm_num : 2 ≠ 0),
      integral_zero, Real.sqrt_zero, List.map_nil, maxErrors, List.foldr_nil] using hz

-- Rates of the nuisance components, not an assumed residual rate, drive this step.
-- @node: binary_boundary_residual_envelope_root_n_negligible
/-- For [admissible reference nuisances](hyp:he0), [admissible fitted
nuisances at every sample size and realization](hyp:heh), and [a positive
denominator scale](hyp:hc), if [success regressions satisfy quarter-rate
control](hyp:hrP), [treatment regressions satisfy quarter-rate control](hyp:hrp),
and [assignment probabilities satisfy quarter-rate control](hyp:hrpi),
[the expected boundary residual envelope
at even sample sizes, multiplied by the square root of the evaluation sample
size, converges to zero in probability](goal). -/
lemma binary_boundary_residual_envelope_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (c : ℝ) (hc : 0 < c) (k : ℕ)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        ∫ x, binaryBoundaryResidualEnvelope L e0 (eh (2*(n+1)) a) c k x ∂xLaw M)
      atTop (fun _ _ => 0) := by
  have hrP := nuisanceRates_positiveValue M μ L.K _ _ hrP
  have hrp := nuisanceRates_positiveValue M μ L.K _ _ hrp
  have hrpi := nuisanceRates_positiveValue M μ L.K _ _ hrpi
  let rP := fun n a i => finiteL2Error M (positiveValue (eh (2*(n+1)) a).P1 i)
    (positiveValue e0.P1 i)
  let rp := fun n a i => finiteL2Error M (positiveValue (eh (2*(n+1)) a).pLev i)
    (positiveValue e0.pLev i)
  let rpi := fun n a i => finiteL2Error M (positiveValue (eh (2*(n+1)) a).piLev i)
    (positiveValue e0.piLev i)
  let reg := fun n a => rP n a (k+1) + rP n a k + rp n a (k+1)
  let wt := fun n a => rpi n a (k+1) + rpi n a k
  have hrnonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ ((2*(n+1) : ℕ) : ℝ) ^ (-1/4 : ℝ) :=
    Eventually.of_forall (fun _ => Real.rpow_nonneg (by positivity) _)
  have hr := ((hrP (k+1)).add_eventually_nonneg_rate hrnonneg
    (hrP k)).add_eventually_nonneg_rate hrnonneg (hrp (k+1))
  have hw := (hrpi (k+1)).add_eventually_nonneg_rate hrnonneg (hrpi k)
  apply dml_quadratic_bias_root_n_negligible μ _ reg wt (3 / c) (by positivity) hr hw
  intro n a
  have hnP : ∀ i, 0 ≤ rP n a i := fun _ => Real.sqrt_nonneg _
  have hnp : ∀ i, 0 ≤ rp n a i := fun _ => Real.sqrt_nonneg _
  have hnpi : ∀ i, 0 ≤ rpi n a i := fun _ => Real.sqrt_nonneg _
  have hreg : 0 ≤ reg n a := add_nonneg (add_nonneg (hnP (k+1)) (hnP k)) (hnp (k+1))
  have hwt : 0 ≤ wt n a := add_nonneg (hnpi (k+1)) (hnpi k)
  obtain ⟨hi, hb⟩ := binary_boundary_residual_envelope_integrated_bound M L e0
    (eh (2*(n+1)) a) he0 (heh _ a) c (reg n a) (wt n a) hc hreg hwt k
    (by change rP n a (k+1) ≤ reg n a; dsimp only [reg]; linarith [hnP k, hnp (k+1)])
    (by change rP n a k ≤ reg n a; dsimp only [reg]; linarith [hnP (k+1), hnp (k+1)])
    (by change rp n a (k+1) ≤ reg n a; dsimp only [reg]; linarith [hnP (k+1), hnP k])
    (by change rpi n a (k+1) ≤ wt n a; exact le_add_of_nonneg_right (hnpi k))
    (by change rpi n a k ≤ wt n a; exact le_add_of_nonneg_left (hnpi (k+1)))
  have henv : 0 ≤ ∫ x, binaryBoundaryResidualEnvelope L e0
      (eh (2*(n+1)) a) c k x ∂xLaw M := by
    apply integral_nonneg
    intro x
    dsimp only [binaryBoundaryResidualEnvelope]
    positivity
  rw [abs_of_nonneg henv]
  exact hb.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (sq_nonneg _))
    (by positivity))

end Papers.TbsPrteOptimalTransport
