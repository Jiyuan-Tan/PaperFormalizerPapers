module
public import Papers.TsAdaptiveEstimationInference.Helpers.Selection
public import Papers.TsAdaptiveEstimationInference.Helpers.Acceptance
/-! TExistLambdaIterTrae for adaptive inverse problems. -/
@[expose] public section
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
/-- For [the IV model](hyp:V), [sampling law](hyp:P), [analysis sample](hyp:sample),
[sample split](hyp:split), [grid factor](hyp:ρ), [failure level](hyp:ξ), [boundedness
scale](hyp:B), [base accuracy curve](hyp:baseδ), [critical-radius curve](hyp:tildeδ),
and [iteration count](hyp:t), use [localized TRAE concentration](hyp:hBennett_of_gate),
[the squared-norm comparison](hyp:hNorm_of_gate), [the admissible grid factor](hyp:hρ),
[the per-iteration failure level strictly between zero and one](hyp:hη), [the range
condition](hyp:hRange), [solution realizability](hyp:hRealizable), [closeness](hyp:hClose),
[mean-square continuity](hyp:hMSC), [boundedness](hyp:hBound), [common-null-set
boundedness](hyp:hCommon), [critical-radius control](hyp:hComplexity), and [allocated
scale calibration](hyp:hScale) to define [the base selection event](goal) at
[sample size n](hyp:n): [for positive sample size, intersect the constructed
loss-and-norm event with the almost-sure sample boundedness event](step:1);
[at size zero, use the empty event](step:2).

The loss/norm event used to prove selection under the proposition's minimal
hypotheses. It is not the full recursive iteration-grid concentration event.
Selection on that stronger shared event is proved by the eventwise helper below. -/
noncomputable def iterTraeSelectionBaseEvent
    (hBennett_of_gate : TRAELocalizedConcentration V)
    (hNorm_of_gate : SquaredNormLocalizedComparison V P sample split)
    (hρ : GridDomain ρ) (hη : ξ / t ∈ Set.Ioo (0 : ℝ) 1)
    (hRange : RangeCondition V) (hRealizable : H0MemHypothesisClass V)
    (hClose : ClosenessCondition V) (hMSC : MeanSquareContinuity V)
    (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B)
    (hComplexity : TRAECriticalRadiusBound V tildeδ)
    (hScale : TRAEScaleCalibration baseδ tildeδ
      (fun n => gridConfidence ρ (ξ / t) n)) (n : ℕ) : Set Ω :=
  if hn : 0 < n then
    let construction := traeCommonEvent_constructed V P sample split ρ (ξ / t) B
      baseδ tildeδ hBennett_of_gate hNorm_of_gate hρ hη hRange hRealizable hClose
      hMSC hBound hCommon hComplexity hScale
    let normEvent := Classical.choose ((Classical.choose_spec construction).2 n hn)
    traeCommonSampleEvent V P sample split ρ (ξ / t) B baseδ tildeδ hBennett_of_gate
      hRange hClose hMSC hBound hCommon hComplexity hη hScale n hn normEvent ∩
        Classical.choose (trae_sample_bounded_event V P sample B hBound hCommon)
  else ∅

/-- For [the IV model](hyp:V), [sampling law](hyp:P), [analysis sample](hyp:sample),
[sample split](hyp:split), [grid factor](hyp:ρ), [failure level](hyp:ξ), [boundedness
scale](hyp:B), [accuracy curve](hyp:δ), [iterative estimator family](hyp:iter),
[noise multiplier](hyp:b), [iteration count](hyp:t), and [sample-size-indexed
events](hyp:events), [selection on that event family](goal) means that each
eligible sample size has the iterative TRAE selection guarantee on its specified event.

Selection on the specified event family, retaining the exact event used
by each constructed-event consumer. This is a conclusion, never a premise. -/
noncomputable def IterTRAESelectionOnFamily (events : ℕ → Set Ω) : Prop :=
  ∀ n : ℕ, iterTraeMinSampleSize B ≤ n →
    IterTRAESelectionOnEvent (V := V) (P := P) (sample := sample) (split := split)
      (ρ := ρ) (ξ := ξ) (δ := δ) (iter := iter) (b := b) (t := t) events n

/-- For [the IV model](hyp:V), [sampling law](hyp:P), [analysis sample](hyp:sample),
[sample split](hyp:split), [grid factor](hyp:ρ), [failure level](hyp:ξ), [boundedness
scale](hyp:B), [accuracy curve](hyp:δ), [iterative estimator family](hyp:iter),
[noise multiplier](hyp:b), [iteration count](hyp:t), and [event family](hyp:events),
[the joint iterative selection property](goal) requires, at each eligible size,
measurability and the probability guarantee for that event together with acceptance,
the fit-count bound, and the initial-or-adjacent return alternative on it.

At every eligible size and the prescribed iteration count, acceptance, the
minimax cost bound and both return alternatives hold jointly on the prescribed
common event `events n`, with its measurability and probability certificate.
Constructors supply this same family; this is a conclusion, never a premise. -/
-- @node: ass:pin-195
noncomputable def PinExistLambdaIterTraeOnEvent (events : ℕ → Set Ω) : Prop :=
  ∀ n : ℕ, iterTraeMinSampleSize B ≤ n →
    IterTRAESelectionOnEvent (V := V) (P := P) (sample := sample) (split := split)
      (ρ := ρ) (ξ := ξ) (δ := δ) (iter := iter) (b := b) (t := t) events n

omit [IsProbabilityMeasure P] in
/-- If [iterative TRAE selection holds on the specified event family](hyp:h), then
[both selection on that family and its joint selection property hold](goal).

The tagged reading retains precisely the prescribed constructed family;
no event is existentially replaced and no probability budget is introduced. -/
lemma iterTRAESelectionOnFamily_and_pin (events : ℕ → Set Ω)
    (h : IterTRAESelectionOnFamily V P sample split ρ ξ B δ iter b t events) :
    IterTRAESelectionOnFamily V P sample split ρ ξ B δ iter b t events ∧
      PinExistLambdaIterTraeOnEvent V P sample split ρ ξ B δ iter b t events := by
  refine ⟨h, ?_⟩
  intro n hn
  exact h n hn

-- @node: prop:exist-lambda-iter-trae
/-- With [localized TRAE concentration](hyp:hBennett_of_gate), [the squared-norm
comparison](hyp:hNorm_of_gate), [a grid factor between one-half inclusive and one
exclusive](hyp:hρ), [a failure level strictly between zero and one](hyp:hξ),
[at least one iteration](hyp:ht), and [a noise multiplier at least two](hyp:hprop),
[a positive calibration threshold ensures that the range and source conditions,
solution realizability, closeness, mean-square
continuity, boundedness and common-null-set boundedness,
critical-radius control, iteration scale calibration,
attained one-step and iterative minima, sufficient
inflation, and deterministic accuracy curves
yield an iteration-times-logarithmic fit bound and both selection properties
on the constructed base event family at every eligible sample size](goal). -/
theorem exist_lambda_iter_trae
    -- Scope audit: pin-195 requires the selection clauses jointly on the named
    -- event; the accepted E^{IT} symbol scopes its EXTRA recursive/oracle-segment
    -- comparisons to propagation, discrepancy and stability, not this minimal
    -- proposition. This event proves the requisite uniform loss/norm comparisons
    -- at eta=xi/[t(K_n+1)] under the proposition's own hypotheses. It is not the
    -- full recursive event. The discrepancy AND rate theorems separately return
    -- this SAME eventwise pin on their actual constructed full intersection,
    -- proving acceptance/complexity/alternatives there via the bounded-common-
    -- event lemma. Check those public conjunctions before demanding extra
    -- recursive-realizability premises in this minimal selection theorem.
    (hBennett_of_gate : TRAELocalizedConcentration V)
    (hNorm_of_gate : SquaredNormLocalizedComparison V P sample split)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (ht : 1 ≤ t)
    (hprop : 2 ≤ b)
    : ∃ required > 0, ∀ (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ),
      ∀ (β : ℝ) (w₀ : V.Hbar.toSubmodule)
      (δ ν : ℕ → ℝ),
      (hRange : RangeCondition V) →
      (hSource : BetaSourceCondition V β w₀) →
      (hRealizable : H0MemHypothesisClass V) →
      (hClose : ClosenessCondition V) →
      (hMSC : MeanSquareContinuity V) →
      (hBound : TRAEBoundedness V B) → (hCommon : TRAECommonNullSetBoundedness V B) →
      (hComplexity : TRAECriticalRadiusBound V tildeδ) →
      (hScale : TRAEScaleCalibration baseδ tildeδ (fun n => iterGridConfidence ρ ξ n t)) →
      (hMinima : TRAEMinimaAttained V P sample split ρ candidate) →
      (hInflation : CalibratedValidBounds δ ν baseδ baseν (κ₀ B c₀ CG Cm).1 (κ₀ B c₀ CG Cm).2 required) →
      (hDeterministic : CalibrationDeterministic δ ν) →
      (hIterMinima : IterTRAEMinimaAttained V P sample split ρ t iter) →
      (∃ Clog > 0, ∀ n : ℕ, iterTraeMinSampleSize B ≤ n →
        (t * (terminalIndex ρ n + 1) : ℕ) ≤ Clog * t * Real.log n) ∧
      let hη : ξ / t ∈ Set.Ioo (0 : ℝ) 1 := by
          constructor
          · exact div_pos hξ.1 (by exact_mod_cast (show 0 < t by omega))
          · apply (div_lt_iff₀ (by exact_mod_cast (show 0 < t by omega))).2
            have : (1 : ℝ) ≤ t := by exact_mod_cast ht
            linarith [hξ.2]
        let hScale' : TRAEScaleCalibration baseδ tildeδ
            (fun n => gridConfidence ρ (ξ / t) n) := by
          have halloc : (fun n => iterGridConfidence ρ ξ n t) =
              (fun n => gridConfidence ρ (ξ / t) n) := by
            funext n
            simp only [iterGridConfidence, gridConfidence, Nat.cast_mul, div_div]
          exact halloc ▸ hScale
        IterTRAESelectionOnFamily V P sample split ρ ξ B δ iter b t
          (iterTraeSelectionBaseEvent V P sample split ρ ξ B baseδ tildeδ t
            hBennett_of_gate hNorm_of_gate hρ hη hRange hRealizable hClose hMSC
            hBound hCommon hComplexity hScale') ∧
        PinExistLambdaIterTraeOnEvent V P sample split ρ ξ B δ iter b t
          (iterTraeSelectionBaseEvent V P sample split ρ ξ B baseδ tildeδ t
            hBennett_of_gate hNorm_of_gate hρ hη hRange hRealizable hClose hMSC
            hBound hCommon hComplexity hScale') := by
  classical
  have ht' : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hη : ξ / t ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · exact div_pos hξ.1 ht'
    · apply (div_lt_iff₀ ht').2
      have : (1 : ℝ) ≤ t := by exact_mod_cast ht
      linarith [hξ.2]
  have halloc : (fun n => iterGridConfidence ρ ξ n t) =
      (fun n => gridConfidence ρ (ξ / t) n) := by
    funext n
    simp only [iterGridConfidence, gridConfidence, Nat.cast_mul, div_div]
  by_cases hSetup : RangeCondition V ∧ H0MemHypothesisClass V ∧ ClosenessCondition V ∧
      MeanSquareContinuity V ∧ TRAEBoundedness V B ∧ TRAECommonNullSetBoundedness V B ∧ TRAECriticalRadiusBound V tildeδ ∧
      TRAEScaleCalibration baseδ tildeδ (fun n => iterGridConfidence ρ ξ n t)
  · obtain ⟨hr, hh0, hcl, hm, hb, hcb, hcx, hsc⟩ := hSetup
    have hsc' := hsc
    rw [halloc] at hsc'
    let construction := traeCommonEvent_constructed V P sample split ρ (ξ / t) B
      baseδ tildeδ hBennett_of_gate hNorm_of_gate hρ hη hr hh0 hcl hm hb hcb hcx hsc'
    let Ce := Classical.choose construction
    have hCe := (Classical.choose_spec construction).1
    have hevent := (Classical.choose_spec construction).2
    refine ⟨Ce + 1, by positivity, ?_⟩
    intro κ₀
    let κδ := (κ₀ B c₀ CG Cm).1
    let κν := (κ₀ B c₀ CG Cm).2
    intro β w₀ δ ν hRange hSource hRealizable hClose hMSC hBound hCommon
      hComplexity hScale hMinima hInflation hDeterministic hIterMinima
    constructor
    · obtain ⟨Clog, hClog, hlog⟩ := terminalIndex_log_bound ρ hρ
      refine ⟨Clog, hClog, ?_⟩
      intro n hn
      have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
      have hx := mul_le_mul_of_nonneg_left (hlog n hn2) (Nat.cast_nonneg t : (0 : ℝ) ≤ t)
      simpa only [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using hx
    · dsimp only
      apply iterTRAESelectionOnFamily_and_pin
      intro n hn
      have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
      have hn0 : 0 < n := by omega
      let normEvent := Classical.choose (hevent n hn0)
      obtain ⟨hE, hp, hcomp⟩ := Classical.choose_spec (hevent n hn0)
      let E := traeCommonSampleEvent V P sample split ρ (ξ / t) B baseδ tildeδ hBennett_of_gate
        hr hcl hm hb hcb hcx hη hsc' n hn0 normEvent
      let S := Classical.choose (trae_sample_bounded_event V P sample B hBound hCommon)
      obtain ⟨hS, hSae, hSbound⟩ :=
        Classical.choose_spec (trae_sample_bounded_event V P sample B hBound hCommon)
      simp only [IterTRAESelectionOnEvent, iterTraeSelectionBaseEvent, dif_pos hn0]
      change IterTRAESelectionOnEvent (V := V) (P := P) (sample := sample)
        (split := split) (ρ := ρ) (ξ := ξ) (δ := δ) (iter := iter) (b := b)
        (t := t) (fun _ => E ∩ S) n
      refine ⟨hE.inter hS, ?_, ?_⟩
      · have heq : (E ∩ S : Set Ω) =ᵐ[P] E := by
          filter_upwards [hSae] with ω hω
          apply propext
          exact ⟨fun h => h.1, fun h => ⟨h, hω⟩⟩
        rw [measureReal_congr heq]
        have hηξ : ξ / t ≤ ξ := by
          apply (div_le_iff₀ ht').2
          have : (1 : ℝ) ≤ t := by exact_mod_cast ht
          nlinarith [hξ.1]
        linarith
      · intro ω hω
        let lam := gridValue ρ (terminalIndex ρ n)
        have hlam : lam ∈ regGrid ρ n := by
          apply Finset.mem_image.mpr
          exact ⟨terminalIndex ρ n, Finset.mem_range.mpr (Nat.lt_succ_self _), rfl⟩
        have hlpos : 0 < lam := mul_pos (by norm_num) (pow_pos (by linarith [hρ.1]) _)
        have hiter := (hIterMinima n hn0 lam hlam).1
        have hlast := hiter.2 t ht le_rfl ω
        have hprev : ∀ i, |primalVersion V (iter n (t - 1) lam ω)
            (V.xOf (sample.Z i ω))| ≤ B := by
          intro i
          by_cases hz : t - 1 = 0
          · have hzero := hiter.1 ω
            simp only [hz, hzero,
              (sampleZeroEvent_spec V P sample ((hcomp ω hω.1).2.2.2) i).1, abs_zero]
            exact hBound.1
          · have hj : 1 ≤ t - 1 := by omega
            exact hSbound ω hω.2 i _ (hiter.2 (t - 1) hj (by omega) ω).1
        have hdist := primalEmpDistanceSq_le_four V P sample split B hBound.1 n hn0 ω
          (minNormSolution V) (iter n (t - 1) lam ω)
          (fun i => hSbound ω hω.2 i _ hRealizable) hprev
        have hopt := hlast.2 (minNormSolution V) hRealizable
        have hnonneg := mul_nonneg hlpos.le
          (primalEmpDistanceSq_nonneg V P sample split n ω
            (iter n t lam ω) (iter n (t - 1) lam ω))
        have hfit : traeEmpiricalLoss V P sample split n ω (iter n t lam ω) ≤
            traeEmpiricalLoss V P sample split n ω (minNormSolution V) + lam * (4 * B ^ 2) := by
          have hd := mul_le_mul_of_nonneg_left hdist hlpos.le
          linarith only [hopt, hnonneg, hd]
        have hk : Ce ≤ κδ ^ 2 := by
          have hk1 := hInflation.1
          have hkCe := hInflation.2.2.1
          nlinarith
        have hnoise : Ce * baseδ n ^ 2 ≤ δ n ^ 2 := by
          rw [hInflation.2.2.2.2.1 n]
          nlinarith [mul_le_mul_of_nonneg_right hk (sq_nonneg (baseδ n))]
        have hzero := ((hcomp ω hω.1).2.2.1).trans hnoise
        have hfloor := trae_calibrated_square_floor baseδ δ tildeδ
          (fun n => iterGridConfidence ρ ξ n t) ν baseν κδ κν (Ce + 1)
          hScale hInflation n hn0
        have hsize : 2 * (4 * B ^ 2) ≤ (n : ℝ) := by
          have hc := Nat.le_ceil (8 * B ^ 2)
          have hnceil : ⌈8 * B ^ 2⌉₊ ≤ n := (le_max_right _ _).trans hn
          have hnceil' : (⌈8 * B ^ 2⌉₊ : ℝ) ≤ n := by exact_mod_cast hnceil
          linarith
        have hrem := terminal_remainder_le_half (4 * B ^ 2) lam (δ n ^ 2) n
          (by positivity) hn0 hsize (terminalGrid_le ρ hρ n hn0) hfloor
        have hA : δ n ^ 2 ≤ iterTraeNoiseLevel b (δ n) lam := by
          unfold iterTraeNoiseLevel iterTraeScale
          have : 0 ≤ min lam (b * δ n ^ 2 / lam) := by
            apply le_min hlpos.le
            exact div_nonneg (mul_nonneg (by linarith [hprop]) (sq_nonneg _)) hlpos.le
          linarith
        have hAccept : Accepts ρ n
            (fun l => traeEmpiricalLoss V P sample split n ω (iter n t l ω))
            (iterTraeNoiseLevel b (δ n)) := by
          refine ⟨terminalIndex ρ n, le_rfl, ?_⟩
          change traeEmpiricalLoss V P sample split n ω (iter n t lam ω) ≤ _
          linarith only [hfit, hzero, hrem, hA]
        obtain ⟨hindex, hcases⟩ := discrepancyIndex_first_acceptance ρ n _ _ hρ hAccept
        exact ⟨hAccept, Nat.mul_le_mul_left t (Nat.add_le_add_right hindex 1), hcases⟩
  · refine ⟨1, zero_lt_one, ?_⟩
    intro κ₀
    let κδ := (κ₀ B c₀ CG Cm).1
    let κν := (κ₀ B c₀ CG Cm).2
    intro β w₀ δ ν hRange hSource hRealizable hClose hMSC hBound hCommon
      hComplexity hScale hMinima hInflation hDeterministic hIterMinima
    exact (hSetup ⟨hRange, hRealizable, hClose, hMSC, hBound, hCommon, hComplexity, hScale⟩).elim


/-- Suppose [the grid factor is admissible](hyp:hρ), [there is at least one
iteration](hyp:ht), [the noise multiplier is at least two](hyp:hb), [the bound
is nonnegative](hyp:hB), [the solution is realizable](hyp:hRealizable), [iterative
minima are attained](hyp:hMinima), [the sample size is eligible](hyp:hn), [the
event is measurable](hyp:hE) and [has probability at least one minus the failure
level](hyp:hp), [the TRAE comparisons hold on it](hyp:hcomp), [every fitted
hypothesis value is bounded there](hyp:hbounded), [the comparison noise is
absorbed by squared accuracy](hyp:hnoise), and [squared accuracy exceeds the
reciprocal sample size](hyp:hfloor); then [iterative TRAE selection holds on
that same event, including acceptance, the fit-count bound, and return alternatives](goal).

Selection is deterministic on the constructed common event. Its fitting
bound is retained from that construction, so no new event or probability budget
is used to prove acceptance and the first-index alternative. -/
lemma iter_trae_selection_on_bounded_common_event
    (ρ ξ B b : ℝ) (t n : ℕ) (δ radius : ℕ → ℝ)
    (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule) (E : Set Ω) (Ce : ℝ)
    (hρ : GridDomain ρ) (ht : 1 ≤ t) (hb : 2 ≤ b) (hB : 0 ≤ B)
    (hRealizable : H0MemHypothesisClass V)
    (hMinima : IterTRAEMinimaAttained V P sample split ρ t iter)
    (hn : iterTraeMinSampleSize B ≤ n) (hE : MeasurableSet E) (hp : 1 - ξ ≤ P.real E)
    (hcomp : TRAEComparisonsOn V P sample split radius n E Ce)
    (hbounded : ∀ ω ∈ E, ∀ i ∈ split.fit n, ∀ h ∈ V.H,
      |primalVersion V h (V.xOf (sample.Z i ω))| ≤ B)
    (hnoise : Ce * radius n ^ 2 ≤ δ n ^ 2) (hfloor : 1 / (n : ℝ) ≤ δ n ^ 2) :
    IterTRAESelectionOnEvent (V := V) (P := P) (sample := sample) (split := split)
      (ρ := ρ) (ξ := ξ) (δ := δ) (iter := iter) (b := b) (t := t) (fun _ => E) n := by
  classical
  refine ⟨hE, hp, ?_⟩
  intro ω hω
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hn0 : 0 < n := by omega
  let lam := gridValue ρ (terminalIndex ρ n)
  have hlam : lam ∈ regGrid ρ n := Finset.mem_image.mpr
    ⟨terminalIndex ρ n, Finset.mem_range.mpr (Nat.lt_succ_self _), rfl⟩
  have hlpos : 0 < lam := mul_pos (by norm_num) (pow_pos (by linarith [hρ.1]) _)
  have hiter := (hMinima n hn0 lam hlam).1
  have hlast := hiter.2 t ht le_rfl ω
  have hprev : ∀ i ∈ split.fit n,
      |primalVersion V (iter n (t - 1) lam ω) (V.xOf (sample.Z i ω))| ≤ B := by
    intro i hi
    by_cases hz : t - 1 = 0
    · simp only [hz, hiter.1 ω,
        (sampleZeroEvent_spec V P sample ((hcomp ω hω).2.2.2) i).1, abs_zero]
      exact hB
    · exact hbounded ω hω i hi _ (hiter.2 (t - 1) (by omega) (by omega) ω).1
  have hdist : primalEmpDistanceSq V P sample split n ω (minNormSolution V)
      (iter n (t - 1) lam ω) ≤ 4 * B ^ 2 := by
    unfold primalEmpDistanceSq blockAverage
    rw [split.card_fit]
    apply (inv_mul_le_iff₀ (by positivity : (0 : ℝ) < n)).2
    calc
      _ ≤ ∑ _i ∈ split.fit n, (4 * B ^ 2) := by
        apply Finset.sum_le_sum
        intro i hi
        have ha := abs_le.mp (hbounded ω hω i hi _ hRealizable)
        have hb := abs_le.mp (hprev i hi)
        nlinarith [sq_nonneg (2 * B -
          (primalVersion V (minNormSolution V) (V.xOf (sample.Z i ω)) -
            primalVersion V (iter n (t - 1) lam ω) (V.xOf (sample.Z i ω)))),
          sq_nonneg (2 * B +
          (primalVersion V (minNormSolution V) (V.xOf (sample.Z i ω)) -
            primalVersion V (iter n (t - 1) lam ω) (V.xOf (sample.Z i ω))))]
      _ = _ := by simp [split.card_fit]
  have hopt := hlast.2 (minNormSolution V) hRealizable
  have hnonneg := mul_nonneg hlpos.le
    (primalEmpDistanceSq_nonneg V P sample split n ω
      (iter n t lam ω) (iter n (t - 1) lam ω))
  have hfit : traeEmpiricalLoss V P sample split n ω (iter n t lam ω) ≤
      traeEmpiricalLoss V P sample split n ω (minNormSolution V) + lam * (4 * B ^ 2) := by
    linarith only [hopt, hnonneg, mul_le_mul_of_nonneg_left hdist hlpos.le]
  have hzero := ((hcomp ω hω).2.2.1).trans hnoise
  have hsize : 2 * (4 * B ^ 2) ≤ (n : ℝ) := by
    have hc := Nat.le_ceil (8 * B ^ 2)
    have hnceil : ⌈8 * B ^ 2⌉₊ ≤ n := (le_max_right _ _).trans hn
    have hnceil' : (⌈8 * B ^ 2⌉₊ : ℝ) ≤ n := by exact_mod_cast hnceil
    linarith
  have hrem := terminal_remainder_le_half (4 * B ^ 2) lam (δ n ^ 2) n
    (by positivity) hn0 hsize (terminalGrid_le ρ hρ n hn0) hfloor
  have hb0 : 0 ≤ b := by linarith only [hb]
  have hA : δ n ^ 2 ≤ iterTraeNoiseLevel b (δ n) lam := by
    unfold iterTraeNoiseLevel iterTraeScale
    have : 0 ≤ min lam (b * δ n ^ 2 / lam) :=
      le_min hlpos.le (by positivity)
    linarith
  have hAccept : Accepts ρ n
      (fun l => traeEmpiricalLoss V P sample split n ω (iter n t l ω))
      (iterTraeNoiseLevel b (δ n)) := by
    refine ⟨terminalIndex ρ n, le_rfl, ?_⟩
    change traeEmpiricalLoss V P sample split n ω (iter n t lam ω) ≤ _
    linarith only [hfit, hzero, hrem, hA]
  obtain ⟨hindex, hcases⟩ := discrepancyIndex_first_acceptance ρ n _ _ hρ hAccept
  exact ⟨hAccept, Nat.mul_le_mul_left t (Nat.add_le_add_right hindex 1), hcases⟩

end Papers.TsAdaptiveEstimationInference
