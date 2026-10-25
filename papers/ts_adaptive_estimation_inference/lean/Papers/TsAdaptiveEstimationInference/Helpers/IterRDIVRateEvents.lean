module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVRateAssembly
/-! Event-preserving final steps of the iterative RDIV rate argument.

The finite-prefix extension uses bounded errors and strictly positive rate
scales. The qualified-rate conversion reuses each supplied event unchanged;
neither deduction constructs or assumes a concentration event.
-/
public section

namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter
open scoped Topology

/-- If [the accuracy and noise curves are valid fixed inflations of their
base curves](hyp:hInflation), [both inflated curves are nonnegative](hyp:hNonneg),
and [the sum of the base curves converges to zero](hyp:hlim), then
[both inflated curves converge to zero](goal). -/
-- @node: iter_rdiv_inflated_scales_tendsto
lemma iter_rdiv_inflated_scales_tendsto
    (δ ν baseδ baseν : ℕ → ℝ) (κδ κν required : ℝ)
    (hInflation : CalibratedValidBounds δ ν baseδ baseν κδ κν required)
    (hNonneg : CalibrationDeterministic δ ν)
    (hlim : Tendsto (fun n => baseδ n + baseν n) atTop (𝓝 0)) :
    Tendsto δ atTop (𝓝 0) ∧ Tendsto ν atTop (𝓝 0) := by
  obtain ⟨hkδ, hkν, _, _, hδeq, hνeq⟩ := hInflation
  have hkδpos : 0 < κδ := by linarith only [hkδ]
  have hkνpos : 0 < κν := by linarith only [hkν]
  have hd (n : ℕ) : 0 ≤ baseδ n := by
    apply (mul_nonneg_iff_of_pos_left hkδpos).1
    simpa only [hδeq n] using hNonneg.1 n
  have hv (n : ℕ) : 0 ≤ baseν n := by
    apply (mul_nonneg_iff_of_pos_left hkνpos).1
    simpa only [hνeq n] using hNonneg.2 n
  have hdl := squeeze_zero hd (fun n => le_add_of_nonneg_right (hv n)) hlim
  have hvl := squeeze_zero hv (fun n => le_add_of_nonneg_left (hd n)) hlim
  constructor
  · rw [show δ = (fun n => κδ * baseδ n) from funext hδeq]
    simpa only [mul_zero] using hdl.const_mul κδ
  · rw [show ν = (fun n => κν * baseν n) from funext hνeq]
    simpa only [mul_zero] using hvl.const_mul κν

/-- If [the propagation multiplier is positive](hyp:ha) and [the accuracy is
nonzero](hyp:hd), then [both the iterative weak-error rate scale and the sum
of the strong variance scale and the weak scale raised to β divided by
β + 1 are strictly positive](goal). -/
-- @node: iter_rdiv_rate_scales_pos
lemma iter_rdiv_rate_scales_pos (a β d v : ℝ) (t : ℕ)
    (ha : 0 < a) (hd : d ≠ 0) :
    0 < iterRdivErrorScale β a d v t ∧
      0 < (a * d ^ 2) ^ ((qualificationExponent β t - 1) /
          (qualificationExponent β t + 1)) +
        iterRdivErrorScale β a d v t ^ (β / (β + 1)) := by
  have hs : 0 < a * d ^ 2 := mul_pos ha (sq_pos_of_ne_zero hd)
  have he : 0 < iterRdivErrorScale β a d v t :=
    add_pos_of_pos_of_nonneg (Real.rpow_pos_of_pos hs _) (sq_nonneg v)
  exact ⟨he, add_pos_of_pos_of_nonneg (Real.rpow_pos_of_pos hs _)
    (Real.rpow_nonneg he.le _)⟩

/-- For [a target element](hyp:h₀), suppose [the failure probability is
nonnegative](hyp:hξ), [the weak rate scale is positive from the starting
sample size onward](hyp:hweak), [the strong rate scale is positive there](hyp:hstrong),
and [both squared estimation errors are uniformly bounded there for every
sample outcome](hyp:hbounded). If [eventually both errors satisfy their rate
bounds with one positive constant on measurable events of probability at
least one minus the failure probability](hyp:htail), then [one positive
constant makes those eventwise bounds hold at every sample size from the
starting size onward](goal). -/
-- @node: iter_rdiv_rate_events_of_eventual
lemma iter_rdiv_rate_events_of_eventual
    {Ω H Q : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedAddCommGroup Q]
    [NormedSpace ℝ H] [NormedSpace ℝ Q]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : H →L[ℝ] Q) (h₀ : H) (fit : ℕ → Ω → H)
    (ξ M : ℝ) (weak strong : ℕ → ℝ) (N₀ : ℕ)
    (hξ : 0 ≤ ξ)
    (hweak : ∀ n, N₀ ≤ n → 0 < weak n)
    (hstrong : ∀ n, N₀ ≤ n → 0 < strong n)
    (hbounded : ∀ n, N₀ ≤ n → ∀ ω,
      ‖T (fit n ω - h₀)‖ ^ 2 ≤ M ∧ ‖fit n ω - h₀‖ ^ 2 ≤ M)
    (htail : ∃ C > 0, ∀ᶠ n in atTop, N₀ ≤ n → ∃ E : Set Ω,
      MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧ ∀ ω ∈ E,
        ‖T (fit n ω - h₀)‖ ^ 2 ≤ C * weak n ∧
        ‖fit n ω - h₀‖ ^ 2 ≤ C * strong n) :
    ∃ C > 0, ∀ n, N₀ ≤ n → ∃ E : Set Ω,
      MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧ ∀ ω ∈ E,
        ‖T (fit n ω - h₀)‖ ^ 2 ≤ C * weak n ∧
        ‖fit n ω - h₀‖ ^ 2 ≤ C * strong n := by
  obtain ⟨C, hC, htail⟩ := htail
  obtain ⟨N, hN⟩ := eventually_atTop.1 htail
  let S : ℝ := ∑ n ∈ Finset.range N, (|M / weak n| + |M / strong n|)
  have hS : 0 ≤ S := Finset.sum_nonneg fun n _ =>
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  let K := C + S + 1
  have hK : 0 < K := by dsimp [K]; linarith only [hC, hS]
  have hCK : C ≤ K := by dsimp [K]; linarith only [hS]
  refine ⟨K, hK, ?_⟩
  intro n hn
  by_cases hnN : N ≤ n
  · obtain ⟨E, hE, hpE, herror⟩ := hN n hnN hn
    refine ⟨E, hE, hpE, ?_⟩
    intro ω hω
    exact ⟨(herror ω hω).1.trans
      (mul_le_mul_of_nonneg_right hCK (hweak n hn).le),
      (herror ω hω).2.trans
      (mul_le_mul_of_nonneg_right hCK (hstrong n hn).le)⟩
  · have hterm : |M / weak n| + |M / strong n| ≤ S :=
      Finset.single_le_sum (fun k _ =>
        add_nonneg (abs_nonneg (M / weak k)) (abs_nonneg (M / strong k)))
        (Finset.mem_range.2 (Nat.lt_of_not_ge hnN))
    have hw : M / weak n ≤ K := by
      dsimp only [K]
      linarith only [le_abs_self (M / weak n), abs_nonneg (M / strong n), hterm, hC]
    have hs : M / strong n ≤ K := by
      dsimp only [K]
      linarith only [le_abs_self (M / strong n), abs_nonneg (M / weak n), hterm, hC]
    refine ⟨Set.univ, MeasurableSet.univ, ?_, ?_⟩
    · simpa only [probReal_univ] using (sub_le_self (1 : ℝ) hξ)
    · intro ω _
      exact ⟨(hbounded n hn ω).1.trans ((div_le_iff₀ (hweak n hn)).1 hw),
        (hbounded n hn ω).2.trans ((div_le_iff₀ (hstrong n hn)).1 hs)⟩

/-- For [a target element](hyp:h₀), suppose [the multiplier is nonnegative](hyp:ha),
[the source exponent β is positive](hyp:hβ), [accuracy is eventually
nonnegative](hyp:hδ), [noise is eventually nonnegative](hyp:hν), [accuracy
converges to zero](hyp:hδlim), [noise is asymptotically bounded by a constant
times accuracy](hyp:hnoise), and [β + 1 is at most twice the iteration
horizon](hyp:hqual). If [the general weak and strong iterative rate bounds
eventually hold with one positive constant on measurable events of probability
at least one minus the failure probability](hyp:hrate), then [eventually such
events support squared strong error bounded by a constant times accuracy to
the power 2β/(β + 2) and squared weak error bounded by the same constant
times accuracy to the power 2(β + 1)/(β + 2)](goal). -/
-- @node: iter_rdiv_qualified_rate_events
lemma iter_rdiv_qualified_rate_events
    {Ω H Q : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedAddCommGroup Q]
    [NormedSpace ℝ H] [NormedSpace ℝ Q]
    (P : Measure Ω) (T : H →L[ℝ] Q) (h₀ : H) (fit : ℕ → Ω → H)
    (ξ a β : ℝ) (t : ℕ) (δ ν : ℕ → ℝ)
    (ha : 0 ≤ a) (hβ : 0 < β)
    (hδ : ∀ᶠ n in atTop, 0 ≤ δ n) (hν : ∀ᶠ n in atTop, 0 ≤ ν n)
    (hδlim : Tendsto δ atTop (𝓝 0))
    (hnoise : ComparableNoise δ ν) (hqual : IterQualificationRDIV β t)
    (hrate : ∃ C > 0, ∀ᶠ n in atTop, ∃ E : Set Ω,
      MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧ ∀ ω ∈ E,
        ‖T (fit n ω - h₀)‖ ^ 2 ≤ C * iterRdivErrorScale β a (δ n) (ν n) t ∧
        ‖fit n ω - h₀‖ ^ 2 ≤ C *
          ((a * δ n ^ 2) ^ ((qualificationExponent β t - 1) /
            (qualificationExponent β t + 1)) +
            iterRdivErrorScale β a (δ n) (ν n) t ^ (β / (β + 1)))) :
    ∃ Cs > 0, ∀ᶠ n in atTop, ∃ E : Set Ω,
      MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧ ∀ ω ∈ E,
        ‖fit n ω - h₀‖ ^ 2 ≤ Cs * δ n ^ (2 * β / (β + 2)) ∧
        ‖T (fit n ω - h₀)‖ ^ 2 ≤ Cs * δ n ^ (2 * (β + 1) / (β + 2)) := by
  obtain ⟨M, hM⟩ := hnoise.bound
  obtain ⟨C, hC, hrate⟩ := hrate
  let W := a ^ ((β + 1) / (β + 2)) + M ^ 2
  let S := a ^ (β / (β + 2)) + W ^ (β / (β + 1))
  let Cs := C * (W + S + 1)
  have hW : 0 ≤ W := add_nonneg (Real.rpow_nonneg ha _) (sq_nonneg M)
  have hS : 0 ≤ S := add_nonneg (Real.rpow_nonneg ha _) (Real.rpow_nonneg hW _)
  have hCs : 0 < Cs := by dsimp [Cs]; positivity
  have hCW : C * W ≤ Cs := by
    dsimp only [Cs]
    exact mul_le_mul_of_nonneg_left (by linarith only [hS]) hC.le
  have hCS : C * S ≤ Cs := by
    dsimp only [Cs]
    exact mul_le_mul_of_nonneg_left (by linarith only [hW]) hC.le
  refine ⟨Cs, hCs, ?_⟩
  filter_upwards [hδ, hν, (tendsto_order.1 hδlim).2 1 zero_lt_one, hM, hrate]
    with n hdn hvn hd1 hMn hrateN
  have hnoiseN : ν n ≤ M * δ n := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hdn, abs_of_nonneg hvn] using hMn
  have hr := iter_rdiv_qualified_rate_simplification a β M (δ n) (ν n) t
    ha hβ hdn hd1.le hvn hnoiseN hqual
  obtain ⟨E, hE, hpE, hgood⟩ := hrateN
  refine ⟨E, hE, hpE, ?_⟩
  intro ω hω
  constructor
  · calc
      ‖fit n ω - h₀‖ ^ 2 ≤ C * _ := (hgood ω hω).2
      _ ≤ C * (S * δ n ^ (2 * β / (β + 2))) :=
        mul_le_mul_of_nonneg_left hr.2 hC.le
      _ = (C * S) * δ n ^ (2 * β / (β + 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hCS (Real.rpow_nonneg hdn _)
  · calc
      ‖T (fit n ω - h₀)‖ ^ 2 ≤ C * _ := (hgood ω hω).1
      _ ≤ C * (W * δ n ^ (2 * (β + 1) / (β + 2))) :=
        mul_le_mul_of_nonneg_left hr.1 hC.le
      _ = (C * W) * δ n ^ (2 * (β + 1) / (β + 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hCW (Real.rpow_nonneg hdn _)

/-- Assume [the RDIV model conditions](hyp:hIV), [realizability of the density
ratio](hyp:hDensity), [the density bounds on the support](hyp:hBounds),
[a uniform bound B on the hypothesis class](hyp:hBound), [nonnegative B](hyp:hB),
[membership of the minimum-norm solution in the hypothesis class](hyp:hRealizable),
[a positive iteration horizon](hyp:ht), and [attained empirical minima with
the required selection measurability](hyp:hMinima). At [a positive sample
size](hyp:hn), [both the squared projected error and squared norm error of
the discrepancy-selected terminal iterate are at most four times B squared,
for every sample outcome](goal). -/
-- @node: iter_rdiv_selected_bounded_errors
lemma iter_rdiv_selected_bounded_errors
    {W X Z Ω : Type*} [MeasurableSpace W] [MeasurableSpace X]
    [MeasurableSpace Z] [MeasurableSpace Ω]
    (V : IVWorld W X Z) (P : Measure Ω) (sample : AnalysisSample V P)
    (split : SampleSplit) (mu : Measure X) (G : Set (X → Z → ℝ))
    (g₀ : X → Z → ℝ) (gHat : ℕ → Ω → X → Z → ℝ)
    (rHat : ℕ → Ω → Z → ℝ) (support : Set (X × Z))
    (B c₀ CG ρ a : ℝ) (t : ℕ) (δ ν : ℕ → ℝ)
    (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (hIV : RDIVSetting V mu g₀) (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hBound : HypothesisClassBounded V support B) (hB : 0 ≤ B)
    (hRealizable : H0MemHypothesisClass V) (ht : 1 ≤ t)
    (hMinima : IterRDIVMinimaAttained V P sample split mu gHat ρ t iter)
    (n : ℕ) (hn : 0 < n) (ω : Ω) :
    let fit := iter n t (iterRdivSelected V P sample split mu gHat rHat
      ρ a t δ ν iter n ω) ω
    ‖projCondExpOp V (fit - minNormSolution V)‖ ^ 2 ≤ 4 * B ^ 2 ∧
      ‖fit - minNormSolution V‖ ^ 2 ≤ 4 * B ^ 2 := by
  classical
  let D := fun lam => rdivCalibrationStat V P sample split mu gHat rHat n ω
    (iter n t lam ω)
  let A := iterRdivNoiseLevel a (δ n) (ν n)
  have hindex : discrepancyIndex ρ n D A ≤ terminalIndex ρ n := by
    unfold discrepancyIndex
    split
    · exact (Nat.find_spec ‹∃ k, k ≤ terminalIndex ρ n ∧
        D (gridValue ρ k) ≤ 3 / 2 * A (gridValue ρ k)›).1
    · exact le_rfl
  have hgrid : iterRdivSelected V P sample split mu gHat rHat
      ρ a t δ ν iter n ω ∈ regGrid ρ n :=
    Finset.mem_image.mpr ⟨discrepancyIndex ρ n D A,
      Finset.mem_range.mpr (Nat.lt_succ_of_le hindex), rfl⟩
  have hmem := ((hMinima n hn _ hgrid).1.2 t ht le_rfl ω).1
  have hfit := rdiv_hypothesis_norm_le V mu G g₀ support B c₀ CG
    hIV hDensity hBounds hBound hB _ hmem
  have hzero := rdiv_hypothesis_norm_le V mu G g₀ support B c₀ CG
    hIV hDensity hBounds hBound hB _ hRealizable
  have hdiff := (norm_sub_le (iter n t (iterRdivSelected V P sample split
    mu gHat rHat ρ a t δ ν iter n ω) ω) (minNormSolution V)).trans
    (add_le_add hfit hzero)
  have hsquare : ‖iter n t (iterRdivSelected V P sample split mu gHat rHat
      ρ a t δ ν iter n ω) ω - minNormSolution V‖ ^ 2 ≤ 4 * B ^ 2 := by
    nlinarith only [hdiff, norm_nonneg (iter n t (iterRdivSelected V P sample split
      mu gHat rHat ρ a t δ ν iter n ω) ω - minNormSolution V), hB]
  have hcontract := (projCondExpOp V).le_of_opNorm_le
    (projCondExpOp_norm_le_one V)
    (iter n t (iterRdivSelected V P sample split mu gHat rHat
      ρ a t δ ν iter n ω) ω - minNormSolution V)
  simp only [one_mul] at hcontract
  exact ⟨(pow_le_pow_left₀ (norm_nonneg _) hcontract 2).trans hsquare, hsquare⟩

/-- Assume [the RDIV model conditions](hyp:hIV), [density-ratio realizability](hyp:hDensity),
[the density bounds on the support](hyp:hBounds), [a uniform hypothesis-class
bound B](hyp:hBound), [nonnegative B](hyp:hB), [realizability of the minimum-norm
solution](hyp:hRealizable), [a positive iteration horizon](hyp:ht), and
[attained empirical minima with selection measurability](hyp:hMinima).
If [the propagation multiplier is positive](hyp:ha), [the failure probability
is nonnegative](hyp:hξ), [accuracy is nonzero at every admissible sample
size](hyp:hδ), and [the selected estimators eventually satisfy the iterative
eventwise rate bounds with one positive constant](hyp:htail), then [one
positive constant gives those rate bounds at every sample size at least the
minimum size determined by B](goal). -/
-- @node: iter_rdiv_selected_rate_of_eventual
lemma iter_rdiv_selected_rate_of_eventual
    {W X Z Ω : Type*} [MeasurableSpace W] [MeasurableSpace X]
    [MeasurableSpace Z] [MeasurableSpace Ω]
    (V : IVWorld W X Z) (P : Measure Ω) [IsProbabilityMeasure P]
    (sample : AnalysisSample V P) (split : SampleSplit)
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (gHat : ℕ → Ω → X → Z → ℝ) (rHat : ℕ → Ω → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG ρ ξ a β : ℝ) (t : ℕ)
    (δ ν : ℕ → ℝ) (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (hIV : RDIVSetting V mu g₀) (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hBound : HypothesisClassBounded V support B) (hB : 0 ≤ B)
    (hRealizable : H0MemHypothesisClass V) (ht : 1 ≤ t)
    (hMinima : IterRDIVMinimaAttained V P sample split mu gHat ρ t iter)
    (ha : 0 < a) (hξ : 0 ≤ ξ)
    (hδ : ∀ n, rdivMinSampleSize B ≤ n → δ n ≠ 0)
    (htail : ∃ C > 0, ∀ᶠ n in atTop, rdivMinSampleSize B ≤ n →
      IterRDIVRateOnEvent V P sample split ρ ξ β a δ ν mu gHat rHat iter t n C) :
    ∃ C > 0, ∀ n, rdivMinSampleSize B ≤ n →
      IterRDIVRateOnEvent V P sample split ρ ξ β a δ ν mu gHat rHat iter t n C := by
  apply iter_rdiv_rate_events_of_eventual P (projCondExpOp V) (minNormSolution V)
    (fun n ω => iter n t (iterRdivSelected V P sample split mu gHat rHat
      ρ a t δ ν iter n ω) ω) ξ (4 * B ^ 2)
    (fun n => iterRdivErrorScale β a (δ n) (ν n) t)
    (fun n => (a * δ n ^ 2) ^ ((qualificationExponent β t - 1) /
      (qualificationExponent β t + 1)) +
      iterRdivErrorScale β a (δ n) (ν n) t ^ (β / (β + 1)))
    (rdivMinSampleSize B) hξ
    (fun n hn => (iter_rdiv_rate_scales_pos a β (δ n) (ν n) t ha (hδ n hn)).1)
    (fun n hn => (iter_rdiv_rate_scales_pos a β (δ n) (ν n) t ha (hδ n hn)).2)
    _ htail
  intro n hn ω
  have hn0 : 0 < n := lt_of_lt_of_le (by
    unfold rdivMinSampleSize
    exact lt_of_lt_of_le (by norm_num : 0 < (2 : ℕ)) (le_max_left _ _)) hn
  exact iter_rdiv_selected_bounded_errors V P sample split mu G g₀ gHat rHat
    support B c₀ CG ρ a t δ ν iter hIV hDensity hBounds hBound hB hRealizable
    ht hMinima n hn0 ω

end Papers.TsAdaptiveEstimationInference
