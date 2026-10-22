module
public import Papers.TbsExtremeEffects.Helpers.Hill.Selection
public import Papers.TbsExtremeEffects.Helpers.Hill.Maximal
public import Papers.TbsExtremeEffects.Helpers.Hill.Exponential
public import Papers.TbsExtremeEffects.Helpers.Hill.ExponentialLaw
public import Papers.TbsExtremeEffects.Helpers.Hill.PartialMoments
public import Papers.TbsExtremeEffects.Helpers.Hill.IncrementLaw
public import Papers.TbsExtremeEffects.Helpers.Hill.SpacingProcess
public import Papers.TbsExtremeEffects.Helpers.Hill.SpacingAverage
public import Papers.TbsExtremeEffects.Helpers.Hill.Threshold
public import Papers.TbsExtremeEffects.Helpers.Hill.OrderStatistics
public import Papers.TbsExtremeEffects.Helpers.Hill.OracleEnvelope
public import Papers.TbsExtremeEffects.Helpers.Hill.TailRatio
public import Papers.TbsExtremeEffects.Helpers.Hill.NumericalBudget
public import Papers.TbsExtremeEffects.Helpers.Hill.TailCalibration
public import Papers.TbsExtremeEffects.Helpers.Hill.SurvivalFromDensity
public import Papers.TbsExtremeEffects.Helpers.Hill.QuantileLower
public import Papers.TbsExtremeEffects.Helpers.Hill.TailDerivative
public import Papers.TbsExtremeEffects.Helpers.Hill.DensityContinuity
public import Papers.TbsExtremeEffects.Helpers.Hill.QuantileDerivative
public import Papers.TbsExtremeEffects.Helpers.Hill.QuantileConstruction
public import Papers.TbsExtremeEffects.Helpers.Hill.DensityPositivity
public import Papers.TbsExtremeEffects.Helpers.Hill.Slice
public import Papers.TbsExtremeEffects.Helpers.Hill.SurvivalCoordinate
public import Papers.TbsExtremeEffects.Helpers.Hill.SurvivalLaw
public import Papers.TbsExtremeEffects.Helpers.Hill.OrderedSpacings
public import Papers.TbsExtremeEffects.Helpers.Hill.SortedDensity

/-! Adaptive Hill rate for the full input sample, with radial density calibration. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
variable {q d m : ℕ}

/-- If [the noise distribution is regularly varying](hyp:hRV), [the noise is independent](hyp:hNoise),
and [a Pareto tail model exists](hyp:hTail), then [the experiment satisfies the adaptive Hill rate guarantee](goal).
@node: lem:mu-rate -/
lemma adaptive_hill_rate (M : ExtremeModel q d) (E : NeteExperiment M)
    (tp : TailParams)
    (hRV : NoiseRegularlyVarying M)
    (hNoise : NoiseIndependent M)
    (hTail : Nonempty (ParetoTailModel M m tp)) :
    HillRateGuarantee E := by
  intro delta hd
  obtain ⟨model⟩ := hTail
  obtain ⟨componentIndex, hComponentIndex, kappa, hkappa, hTransferMeasure⟩ :=
    hill_radial_tail_transfer M tp model
  let radialCutoff := tp.u *
    (tp.zeta * (componentIndex : ℝ) ^ ((1 - 2 * tp.s) / M.beta))
  let nominalSurvival : ℝ → ℝ := fun r =>
    ((hillNominalComponentLaw M.beta m).map
      (fun z => l1Norm (model.A.mulVec z))).real (Set.Ioi r)
  have hTransfer : ∀ r > radialCutoff, tailProb M r = kappa * nominalSurvival r := by
    intro r hr
    have hmass := hTransferMeasure (Set.Ioi r) measurableSet_Ioi
      (fun x hx => hr.trans hx)
    rw [Measure.map_apply (measurable_radius M) measurableSet_Ioi] at hmass
    change M.mu {w | r < radius M w} = _ at hmass
    unfold tailProb
    dsimp [nominalSurvival, Measure.real]
    rw [hmass, ENNReal.toReal_mul, ENNReal.toReal_ofReal hkappa.le]
  let C₀ := kappa * ∑ i : Fin m, (l1Norm (fun r => model.A r i)) ^ M.beta
  have hC₀ : 0 < C₀ := hill_radial_leading_constant_pos M tp model hkappa
  suffices hRemaining : ∃ n0 : ℕ, ∃ a : ℝ, 0 < a ∧
      ∀ n, n0 ≤ n → IIDSampling E n →
      ∃ (k : ℕ) (hklt : k < n) (A B : ℕ → E.Om → ℝ) (T : Set E.Om)
        (V : Fin n → E.Om → ℝ) (Yorder : E.Om → Fin n → ℝ)
        (ℱ : Filtration ℕ E.measurableSpace),
        (∀ i, Measurable (B i)) ∧
        (∀ w i, B i w = (i : ℝ) * (A i w - 1)) ∧
        StronglyAdapted ℱ B ∧
        (∀ i, n ≤ i → ∀ w, B i w = B n w) ∧
        (∀ lam : ℝ, 0 < lam → lam < 1 →
          (∀ i ≤ n, Integrable (fun w => Real.exp
              (lam * B i w - (i : ℝ) * (lam ^ 2 / (2 * (1 - lam))))) E.P ∧
            Integrable (fun w => Real.exp
              (lam * (-B i w) - (i : ℝ) * (lam ^ 2 / (2 * (1 - lam))))) E.P) ∧
          (∀ i < n, Integrable (fun w => Real.exp (lam * (B (i + 1) w - B i w))) E.P ∧
            Integrable (fun w => Real.exp (-lam * (B (i + 1) w - B i w))) E.P) ∧
          (∀ i < n, E.P[(fun w => Real.exp (lam * (B (i + 1) w - B i w))) | ℱ i]
              =ᵐ[E.P] (fun _ => Real.exp (-lam) / (1 - lam)) ∧
            E.P[(fun w => Real.exp (-lam * (B (i + 1) w - B i w))) | ℱ i]
              =ᵐ[E.P] (fun _ => Real.exp lam / (1 + lam)))) ∧
        MeasurableSet T ∧
        (∀ i, Measurable (V i)) ∧ iIndepFun V E.P ∧
        (∀ w, Antitone (Yorder w)) ∧
        (∀ w, ∃ σ : Equiv.Perm (Fin n), ∀ i, Yorder w i = V (σ i) w) ∧
        Measurable (fun w => Yorder w ⟨k, hklt⟩) ∧
        (∀ i, (∫ w, if Real.log ((n : ℝ) / (2 * k)) < V i w then (1 : ℝ)
          else 0 ∂E.P) = 2 * (k : ℝ) / n) ∧
        (∀ w, Real.log ((n : ℝ) / (2 * k)) ≤ Yorder w ⟨k, hklt⟩ → w ∈ T) ∧
        (∀ w ∈ T, 0 < orderedRadius E n w (k + 1) ∧
          ∃ (Y : ℕ → ℝ) (Q Q' eta : ℝ → ℝ),
            (∀ i ∈ Finset.Icc (hillLower n) k,
              A i w = (i : ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 i,
                (j : ℝ) * (Y j - Y (j + 1))) ∧
            (∀ j ∈ Finset.Icc 1 k,
              Y (j + 1) ≤ Y j ∧ Y (k + 1) ≤ Y (j + 1)) ∧
            (∀ j ∈ Finset.Icc 1 (k + 1),
              orderedRadius E n w j = Q (Real.exp (Y j))) ∧
            (∀ u ≥ Y (k + 1),
              0 < Q (Real.exp u) ∧ HasDerivAt Q (Q' (Real.exp u)) (Real.exp u) ∧
              Real.exp u * Q' (Real.exp u) / Q (Real.exp u) - gamma M = eta (Real.exp u) ∧
              |eta (Real.exp u)| ≤ gamma M * hillDeviation n delta / Real.sqrt k)) ∧
        ⌊a * hillOracleScale M.beta n (hillDeviation n delta)⌋₊ ≤ k by
    obtain ⟨n0, a, ha, h⟩ := hRemaining
    obtain ⟨nCut, hCut⟩ := eventually_atTop.mp
      (hill_oracle_candidate_eventually_ge_lower hRV.1 hd ha)
    let F := Real.sqrt (2 / a) * (18 : ℝ) ^
      (min 1 (1 / M.beta) / (1 + 2 * min 1 (1 / M.beta)))
    let C := 27 * gamma M * F
    obtain ⟨nCalc, hCalc⟩ := eventually_atTop.mp
      ((hillLower_eventually_ge 2).and (hill_oracle_penalty_rate hRV.1 hd ha))
    obtain ⟨nThreshold, hThresholdSize⟩ := eventually_atTop.mp
      (hillLower_eventually_ge (4 * Real.log (2 / delta)))
    obtain ⟨nSmall, hSmall⟩ := eventually_atTop.mp (hillDeviation_eventually_small hd)
    refine ⟨max (max (max (max n0 nCut) nThreshold) nSmall) nCalc, C, ?_⟩
    intro n hnAll hiid
    have hn : max (max (max n0 nCut) nThreshold) nSmall ≤ n := (le_max_left _ _).trans hnAll
    obtain ⟨k, hklt, A, B, T, V, Yorder, ℱ, hB, hcenter, hAdapt, hStopped, hMoments,
      hT, hV, hVind, hYorder, hSort, hYmeas, hTailMean,
      hThresholdImp, hincrements, hCandidateOracle⟩ :=
      h n (by omega) hiid
    have hCandidateLower := hCut n (by omega)
    have hL2 := (hCalc n ((le_max_right _ _).trans hnAll)).1
    have hL2nat : 2 ≤ hillLower n := by exact_mod_cast hL2
    have hL : 1 ≤ hillLower n := by omega
    have hk : k ∈ Finset.Icc (hillLower n) (n - 1) :=
      Finset.mem_Icc.mpr ⟨hCandidateLower.trans hCandidateOracle, by omega⟩
    have hThresholdBudget : 4 * Real.log (2 / delta) ≤ (k : ℝ) :=
      (hThresholdSize n (by omega)).trans
        (by exact_mod_cast (Finset.mem_Icc.mp hk).1)
    have hThreshold := hill_quantile_threshold_probability E.P hklt V Yorder
      hV hVind hYorder hSort (Real.log ((n : ℝ) / (2 * k))) hYmeas
      hTailMean hd.1 hThresholdBudget
    have hTprob : 1 - delta / 2 ≤ E.P.real T :=
      hThreshold.2.trans (measureReal_mono (h₂ := measure_ne_top E.P _)
        (fun w hw => hThresholdImp w hw))
    have hSuper : ∀ lam : ℝ, 0 < lam → lam < 1 →
        Supermartingale (fun i w => Real.exp
          (lam * B i w - (i : ℝ) * (lam ^ 2 / (2 * (1 - lam))))) ℱ E.P ∧
        Supermartingale (fun i w => Real.exp
          (lam * (-B i w) - (i : ℝ) * (lam ^ 2 / (2 * (1 - lam))))) ℱ E.P := by
      intro lam hlam hlamone
      obtain ⟨hInt, hInc, hMoment⟩ := hMoments lam hlam hlamone
      exact hill_supermartingales_of_finite_exponential_increment_moments E.P B ℱ n hAdapt
        hStopped hlam hlamone hInt hInc hMoment
    have hzero : ∀ w, B 0 w = 0 := by intro w; simp [hcenter w 0]
    have hnpos : 1 ≤ n := by
      obtain ⟨hkl, hku⟩ := Finset.mem_Icc.mp hk
      omega
    have hmax : ∀ a < hillGridSize n,
        E.P.real {w | ∃ i ≤ min n (2 ^ (a + 1)),
          Real.sqrt (2 * (min n (2 ^ (a + 1)) : ℕ) * hillLogBudget n delta) +
            hillLogBudget n delta < |B i w|} ≤
          2 * Real.exp (-hillLogBudget n delta) := by
      intro a _
      exact hill_spacing_maximal_probability E.P B ℱ hzero hSuper
        (le_min hnpos (Nat.one_le_pow _ _ (by norm_num))) (hill_logBudget_pos n hd)
    let S := {w | ∀ i ∈ Finset.Icc (hillLower n) n,
      |A i w - 1| ≤ hillDeviation n delta / Real.sqrt i}
    have hSprob := hill_average_simultaneous_probability E.P A B hB hL hcenter hd hmax
    have hspacing : ∀ w ∈ S, ∀ i ∈ Finset.Icc (hillLower n) k,
        |A i w - 1| ≤ hillDeviation n delta / Real.sqrt i := by
      intro w hw i hi
      exact hw i (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1,
        (Finset.mem_Icc.mp hi).2.trans ((Finset.mem_Icc.mp hk).2.trans (Nat.sub_le n 1))⟩)
    have hbias : ∀ w ∈ T, ∀ i ∈ Finset.Icc (hillLower n) k,
        |hillStat E n i w - gamma M * A i w| ≤
          (gamma M * hillDeviation n delta / Real.sqrt k) * A i w := by
      intro w hw
      obtain ⟨hpos, Y, Q, Q', eta, hA, hY, hR, hTail⟩ := hincrements w hw
      have herror := hill_spacing_errors_of_quantile_derivative M E n k w Y Q Q' eta
        (gamma M) (gamma M * hillDeviation n delta / Real.sqrt k) hY hR hTail
      exact hill_prefix_bias_of_log_increment_control M E n (hillLower n) k w
        Y (fun i => A i w) (gamma M) (gamma M * hillDeviation n delta / Real.sqrt k)
        hL (by obtain ⟨hkl, hku⟩ := Finset.mem_Icc.mp hk; omega) hpos hA herror
    have hround : 2 ≤ a * hillOracleScale M.beta n (hillDeviation n delta) := by
      apply (Nat.le_floor_iff' (by norm_num : (2 : ℕ) ≠ 0)).mp
      exact hL2nat.trans hCandidateLower
    have hpenalty := (hCalc n ((le_max_right _ _).trans hnAll)).2 k hround hCandidateOracle
    have hg : 0 ≤ gamma M := by unfold gamma; exact div_nonneg (by norm_num) hRV.1.le
    have hrate : 27 * gamma M * hillDeviation n delta / Real.sqrt k ≤
        C * hillRateShape M.beta n (8 / delta) := by
      calc
        _ = (27 * gamma M) * (hillDeviation n delta / Real.sqrt k) := by ring
        _ ≤ (27 * gamma M) * (F * hillRateShape M.beta n (8 / delta)) :=
          mul_le_mul_of_nonneg_left hpenalty (by positivity)
        _ = _ := by dsimp [C]; ring
    exact hill_adaptive_probability_of_oracle_events M E n k delta
      (C * hillRateShape M.beta n (8 / delta)) A S T hT hSprob hTprob
      hg
      (hillDeviation_nonneg n hd) hL hk (hSmall n ((le_max_right _ _).trans hn))
      hspacing hbias hrate
  let f : ℝ → ℝ := fun r => kappa * ∑ i, ∫ z,
    hillLargestSummandIntegrand (fun i => l1Norm (fun r => model.A r i))
      M.beta r (fun j => l1Norm (fun r => model.A r j) * z j) i
        ∂hillNominalComponentLaw M.beta m
  have hfmeas : Measurable f := hill_nominal_partition_density_measurable _ hRV.1 kappa
  have hfContinuous : ∀ r > 0, ContinuousAt f r := by
    intro r hr
    exact hill_nominal_partition_density_continuousAt _ hRV.1
      (fun i => model.constants.2.1.trans_le (model.matrix.2.1 i).1) hr kappa
  let representation (Q : ℝ → ℝ) (v₀ : ℝ) : Prop :=
    ∃ n0 : ℕ, ∀ n, n0 ≤ n → IIDSampling E n →
      ∀ (k : ℕ) (hklt : k < n), 0 < k → v₀ ≤ (n : ℝ) / (2 * k) →
      ∃ (T : Set E.Om) (V : Fin n → E.Om → ℝ)
        (S : Fin n → E.Om → ℝ),
      (∀ j, Measurable (S j)) ∧ iIndepFun S E.P ∧
      (∀ j, E.P.map (S j) = expMeasure 1) ∧
      MeasurableSet T ∧
      (∀ i, Measurable (V i)) ∧ iIndepFun V E.P ∧
      (∀ i, E.P.map (V i) = expMeasure 1) ∧
      (∀ w, Real.log ((n : ℝ) / (2 * k)) ≤ hillDecreasingOrder V w ⟨k, hklt⟩ → w ∈ T) ∧
      (∀ w ∈ T, 0 < orderedRadius E n w (k + 1) ∧
        ∃ (Y : ℕ → ℝ),
          (∀ j : Fin n, (j : ℕ) < k →
            S j w = ((j : ℕ) + 1 : ℝ) *
              (Y ((j : ℕ) + 1) - Y ((j : ℕ) + 2))) ∧
          (∀ j ∈ Finset.Icc 1 k,
            Y (j + 1) ≤ Y j ∧ Y (k + 1) ≤ Y (j + 1)) ∧
          (∀ j ∈ Finset.Icc 1 (k + 1),
            orderedRadius E n w j = Q (Real.exp (Y j))) ∧
          (n : ℝ) / (2 * k) ≤ Real.exp (Y (k + 1)))
  suffices hConstruction : ∃ (eta Q : ℝ → ℝ) (v₀ : ℝ),
      1 < v₀ ∧
      (∀ r > radialCutoff, (M.mu.map (radius M)) (Set.Ioi r) =
        (volume.withDensity (fun x => ENNReal.ofReal (f x))) (Set.Ioi r)) ∧
      (∀ v ≥ v₀, ∀ w ≥ v,
        (∀ x > Q w, ∃ z ≥ w, Q z = x) ∧
          tailProb M (Q w) = w⁻¹ ∧
          eta w = tailProb M (Q w) / (Q w * f (Q w)) - gamma M) ∧
      representation Q v₀ by
    obtain ⟨eta, Q, vRaw, hvRaw, hfLaw, hRawQuantile, n0, hRep⟩ := hConstruction
    obtain ⟨vBase, hRawStrict, hvBase, hCutoff⟩ :=
      hill_tail_quantile_eventually_above M hRV Q (vBase := vRaw + 1)
        (fun v hv => (hRawQuantile v (by linarith) v le_rfl).2.1)
        (max radialCutoff tp.u)
    have hRawBase : vRaw ≤ vBase := by linarith
    have hRadialRawQuantile : ∀ v ≥ vBase, ∀ w ≥ v,
        (∀ x > Q w, ∃ z ≥ w, Q z = x) ∧
          radialCutoff < Q w ∧ tp.u ≤ Q w ∧ tailProb M (Q w) = w⁻¹ ∧
          f (Q w) = kappa * ∑ i, ∫ z,
            hillLargestSummandIntegrand (fun i => l1Norm (fun r => model.A r i))
              M.beta (Q w) (fun j => l1Norm (fun r => model.A r j) * z j) i
                ∂hillNominalComponentLaw M.beta m ∧
          eta w = tailProb M (Q w) / (Q w * f (Q w)) - gamma M := by
      intro v hv w hw
      obtain ⟨hsurj, hrecip, heta⟩ :=
        hRawQuantile v (hRawBase.trans hv) w hw
      have hlarge := hCutoff w (hv.trans hw)
      exact ⟨hsurj, (le_max_left _ _).trans_lt hlarge,
        ((le_max_right _ _).trans_lt hlarge).le, hrecip, rfl, heta⟩
    have hm : 0 < m := by
      obtain ⟨hdim, hdim'⟩ := model.constants.1
      omega
    let i : Fin m := ⟨0, hm⟩
    let Cq := kappa * (l1Norm (fun r => model.A r i) / 2) ^ M.beta
    have hCq : 0 < Cq := mul_pos hkappa
      (Real.rpow_pos_of_pos (by
        have := model.constants.2.1.trans_le (model.matrix.2.1 i).1
        positivity) _)
    let c := min 1 (Cq ^ (1 / M.beta))
    have hc : 0 < c := lt_min (by norm_num) (Real.rpow_pos_of_pos hCq _)
    have hc1 : c ≤ 1 := min_le_left _ _
    have hRadialQuantile : ∀ v ≥ vBase, ∀ w ≥ v,
        (∀ x > Q w, ∃ z ≥ w, Q z = x) ∧
          c * v ^ (1 / M.beta) ≤ Q w ∧
          f (Q w) = kappa * ∑ i, ∫ z,
            hillLargestSummandIntegrand (fun i => l1Norm (fun r => model.A r i))
              M.beta (Q w) (fun j => l1Norm (fun r => model.A r j) * z j) i
                ∂hillNominalComponentLaw M.beta m ∧
          eta w = tailProb M (Q w) / (Q w * f (Q w)) - gamma M := by
      intro v hv w hw
      obtain ⟨hsurj, hcut, hlarge, hrecip, hpartition, heta⟩ :=
        hRadialRawQuantile v hv w hw
      have hvpos : 0 < v := hvBase.trans_le hv
      have hwpos : 0 < w := hvpos.trans_le hw
      have hQpos : 0 < Q w :=
        (zero_lt_one.trans model.constants.2.2.2.1).trans_le hlarge
      have htail : Cq * (Q w) ^ (-M.beta) ≤ v⁻¹ := by
        calc
          _ ≤ kappa * nominalSurvival (Q w) := by
            simpa only [Cq, mul_assoc] using mul_le_mul_of_nonneg_left
              (hill_nominal_matrix_tail_lower hRV.1 model.A model.matrix.1
                (fun j => model.constants.2.1.trans_le (model.matrix.2.1 j).1) i
                ((model.matrix.2.1 i).2.trans hlarge)) hkappa.le
          _ = tailProb M (Q w) := (hTransfer (Q w) hcut).symm
          _ = w⁻¹ := hrecip
          _ ≤ v⁻¹ := inv_anti₀ hvpos hw
      refine ⟨hsurj, ?_, hpartition, heta⟩
      exact (mul_le_mul_of_nonneg_right (min_le_right _ _)
        (Real.rpow_nonneg hvpos.le _)).trans
        (hill_quantile_lower_of_polynomial_tail hRV.1 hCq hvpos hQpos htail)
    have hShiftNonneg : 0 ≤ ((M.beta + 1) * tp.u) * (c ^ (-M.beta) + c⁻¹) := by
      apply mul_nonneg
      · exact mul_nonneg (by linarith [hRV.1])
          (zero_lt_one.trans model.constants.2.2.2.1).le
      · positivity
    obtain ⟨Ctail, hCtail, hBudgetConstant, hShiftConstant⟩ :=
      hill_tail_coefficient_exists
        (A := hillNumericalBudgetCoefficient
          (fun i => l1Norm (fun r => model.A r i)) M.beta kappa *
            (c ^ (-M.beta) + c⁻¹))
        (mul_pos hRV.1 hC₀) hShiftNonneg
    obtain ⟨V, hV⟩ := eventually_atTop.mp
      ((hill_tail_envelope_eventually_small hRV.1 Ctail).and
        ((hill_quantile_lower_eventually_large hRV.1 hc).and
          (hill_quantile_lower_eventually_above_cutoff hRV.1 hc radialCutoff)))
    let v₀ := max vBase V
    have hv : 0 < v₀ := hvBase.trans_le (le_max_left _ _)
    have ha : ∀ i, 0 < l1Norm (fun r => model.A r i) :=
      fun i => model.constants.2.1.trans_le (model.matrix.2.1 i).1
    have hBudgetNonneg := hill_numerical_budget_coefficient_nonneg
      (fun i => l1Norm (fun r => model.A r i)) hRV.1 hkappa.le ha
    have hRadialRaw : ∀ v ≥ v₀, ∀ w ≥ v,
        let b := if M.beta = 1 then Ctail * v ^ (-1 : ℝ) * Real.log v
          else Ctail * v ^ (-min 1 (1 / M.beta))
        radialCutoff < Q w ∧ 0 < Q w ∧
          (∀ x > Q w, ∃ z ≥ w, Q z = x) ∧
          HillNominalLargestSummandData (fun i => l1Norm (fun r => model.A r i))
            M.beta (Q w) kappa (f (Q w))
            ((M.beta * C₀ * (Q w) ^ (-M.beta - 1)) * (b / 2)) ∧
          (M.beta + 1) * tp.u / Q w ≤ b / 2 ∧ b ≤ 1 / 2 ∧
          eta w = tailProb M (Q w) / (Q w * f (Q w)) - gamma M := by
      intro v hv' w hw
      obtain ⟨hsurj, hQ, hpartition, heta⟩ :=
        hRadialQuantile v ((le_max_left vBase V).trans hv') w hw
      obtain ⟨hsmall, ⟨hv1, hbase⟩, hcutBase⟩ :=
        hV v ((le_max_right vBase V).trans hv')
      have hcut : radialCutoff < Q w := hcutBase.trans_le hQ
      have hpos : 0 < Q w := ((Real.exp_pos 1).trans_le hbase).trans_le hQ
      let z := if M.beta = 1 then v ^ (-1 : ℝ) * Real.log v
        else v ^ (-min 1 (1 / M.beta))
      have hvlog : 0 ≤ Real.log v := Real.log_nonneg hv1
      have hz : 0 ≤ z := by
        dsimp [z]
        split_ifs <;> positivity
      have hb : (if M.beta = 1 then Ctail * v ^ (-1 : ℝ) * Real.log v
          else Ctail * v ^ (-min 1 (1 / M.beta))) = Ctail * z := by
        dsimp [z]; split_ifs <;> ring
      have hshape := hill_radial_remainder_quantile_bound hRV.1 hc hc1 hv1 hbase hQ
      have hinv := hill_inverse_radius_quantile_bound hRV.1 hc hc1 hv1 hbase hQ
      obtain ⟨hlarge, hlog⟩ := hill_radius_large_of_quantile_lower hbase hQ
      refine ⟨hcut, hpos, hsurj, ?_, ?_, hsmall, heta⟩
      · apply hill_nominal_data_of_partition_and_radial_bound
          (fun i => l1Norm (fun r => model.A r i)) hRV.1 ha hkappa.le hlarge hlog hpartition
        calc
          _ ≤ hillNumericalBudgetCoefficient (fun i => l1Norm (fun r => model.A r i))
              M.beta kappa * ((c ^ (-M.beta) + c⁻¹) * z) :=
            mul_le_mul_of_nonneg_left hshape hBudgetNonneg
          _ ≤ ((M.beta * C₀) * (Ctail / 2)) * z := by
            rw [← mul_assoc]
            exact mul_le_mul_of_nonneg_right hBudgetConstant hz
          _ = _ := by rw [hb]; ring
      · have hshiftpos : 0 ≤ (M.beta + 1) * tp.u := by
          exact mul_nonneg (by linarith [hRV.1])
            (zero_lt_one.trans model.constants.2.2.2.1).le
        calc
          _ = ((M.beta + 1) * tp.u) * (Q w)⁻¹ := by rw [div_eq_mul_inv]
          _ ≤ ((M.beta + 1) * tp.u) * ((c ^ (-M.beta) + c⁻¹) * z) :=
            mul_le_mul_of_nonneg_left hinv hshiftpos
          _ ≤ (Ctail / 2) * z := by
            rw [← mul_assoc]
            exact mul_le_mul_of_nonneg_right hShiftConstant hz
          _ = _ := by rw [hb]; ring
    have hRadialPareto : ∀ v ≥ v₀, ∀ w ≥ v,
        let b := if M.beta = 1 then Ctail * v ^ (-1 : ℝ) * Real.log v
          else Ctail * v ^ (-min 1 (1 / M.beta))
        radialCutoff < Q w ∧ 0 < Q w ∧
          (∀ x > Q w, ∃ z ≥ w, Q z = x) ∧
          HillLargestSummandParetoData (fun i => l1Norm (fun r => model.A r i))
            M.beta (Q w) kappa (f (Q w))
            ((M.beta * C₀ * (Q w) ^ (-M.beta - 1)) * (b / 2)) ∧
          (M.beta + 1) * tp.u / Q w ≤ b / 2 ∧ b ≤ 1 / 2 ∧
          eta w = tailProb M (Q w) / (Q w * f (Q w)) - gamma M := by
      intro v hv' w hw
      obtain ⟨hcut, hpos, hsurj, hconv, hshift, hsmall, heta⟩ := hRadialRaw v hv' w hw
      refine ⟨hcut, hpos, hsurj, ?_, hshift, hsmall, heta⟩
      exact hill_pareto_data_of_nominal_data
        (fun i => l1Norm (fun r => model.A r i)) hRV.1
        (fun i => model.constants.2.1.trans_le (model.matrix.2.1 i).1) hconv
    have hDensity : ∀ v ≥ v₀, ∀ w ≥ v,
        let b := if M.beta = 1 then Ctail * v ^ (-1 : ℝ) * Real.log v
          else Ctail * v ^ (-min 1 (1 / M.beta))
        radialCutoff < Q w ∧ 0 < Q w ∧
          (∀ x > Q w, ∃ z ≥ w, Q z = x) ∧
          |f (Q w) / (M.beta * C₀ * (Q w) ^ (-M.beta - 1)) - 1| ≤ b ∧
          b ≤ 1 / 2 ∧
          eta w = tailProb M (Q w) / (Q w * f (Q w)) - gamma M := by
      intro v hv' w hw
      obtain ⟨hcut, hpos, hsurj, hconv, hshift, hsmall, heta⟩ := hRadialPareto v hv' w hw
      have hsum : 0 < ∑ i : Fin m, (l1Norm (fun r => model.A r i)) ^ M.beta :=
        (mul_pos_iff_of_pos_left hkappa).mp hC₀
      refine ⟨hcut, hpos, hsurj, ?_, hsmall, heta⟩
      have hconvData := hill_convolution_data_of_largest_summand
        (fun i => l1Norm (fun r => model.A r i)) hRV.1 hpos
        (fun i => model.constants.2.1.trans_le (model.matrix.2.1 i).1)
        (hill_largest_summand_data_of_component_data
          (fun i => l1Norm (fun r => model.A r i)) hRV.1 hpos
          (fun i => model.constants.2.1.trans_le (model.matrix.2.1 i).1) hkappa.le
          (hill_component_data_of_polynomial_data
            (fun i => l1Norm (fun r => model.A r i)) hRV.1 hpos
            (fun i => model.constants.2.1.trans_le (model.matrix.2.1 i).1) hkappa.le
            (hill_polynomial_data_of_pareto_data
              (fun i => l1Norm (fun r => model.A r i))
              (fun i => model.constants.2.1.trans_le (model.matrix.2.1 i).1) hconv)))
      have hconvError := hill_convolution_error_of_remainder_data
        (fun i => l1Norm (fun r => model.A r i)) hRV.1 hpos
        (fun i => model.constants.2.1.trans_le (model.matrix.2.1 i).1) hkappa.le hconvData
      exact hill_density_relative_error_of_convolution
        (fun i => l1Norm (fun r => model.A r i)) hRV.1 hpos
        (fun i => model.constants.2.1.trans_le (model.matrix.2.1 i).1)
        (fun i => (model.matrix.2.1 i).2) hkappa hsum hconvError hshift
    have hRadial : ∀ v ≥ v₀, ∀ w ≥ v,
        let b := if M.beta = 1 then Ctail * v ^ (-1 : ℝ) * Real.log v
          else Ctail * v ^ (-min 1 (1 / M.beta))
        radialCutoff < Q w ∧ 0 < Q w ∧
          |kappa * nominalSurvival (Q w) / (C₀ * (Q w) ^ (-M.beta)) - 1| ≤ b ∧
          |f (Q w) / (M.beta * C₀ * (Q w) ^ (-M.beta - 1)) - 1| ≤ b ∧
          b ≤ 1 / 2 ∧
          eta w = tailProb M (Q w) / (Q w * f (Q w)) - gamma M := by
      intro v hv' w hw
      obtain ⟨hcut, hpos, hsurj, hdensity, hsmall, heta⟩ := hDensity v hv' w hw
      have hAllDensity : ∀ x > Q w,
          |f x / (M.beta * C₀ * x ^ (-M.beta - 1)) - 1| ≤
            (if M.beta = 1 then Ctail * v ^ (-1 : ℝ) * Real.log v
              else Ctail * v ^ (-min 1 (1 / M.beta))) := by
        intro x hx
        obtain ⟨z, hz, hQz⟩ := hsurj x hx
        have h := (hDensity v hv' z (hw.trans hz)).2.2.2.1
        simpa only [hQz] using h
      have hIntegral : kappa * nominalSurvival (Q w) =
          ∫ x : ℝ in Set.Ioi (Q w), f x := by
        have hS := hill_tail_mass_eq_density_integral (M.mu.map (radius M)) f hfmeas
          (fun x hx => (hill_density_pos_of_relative_error hRV.1 hC₀ (hpos.trans hx)
            (hAllDensity x hx) (by linarith)).le) (hfLaw (Q w) hcut)
        rw [Measure.real, Measure.map_apply (measurable_radius M) measurableSet_Ioi] at hS
        change tailProb M (Q w) = _ at hS
        rw [hTransfer (Q w) hcut] at hS
        exact hS
      refine ⟨hcut, hpos, ?_, hdensity, hsmall, heta⟩
      exact hill_survival_relative_error_of_density f hRV.1 hC₀ hpos hfmeas hIntegral
        hAllDensity
    let C := 4 * Ctail / M.beta
    have hC : 0 ≤ C := div_nonneg (mul_nonneg (by norm_num) hCtail) hRV.1.le
    have hRawEnvelope : ∀ v ≥ v₀, ∀ w ≥ v, |eta w| ≤
        if M.beta = 1 then C * v ^ (-1 : ℝ) * Real.log v
        else C * v ^ (-min 1 (1 / M.beta)) := by
      intro v hv' w hw
      obtain ⟨hQcut, hQpos, hNominalSurvival, hDensity, hSmall, hEta⟩ := hRadial v hv' w hw
      have hSurvival : |tailProb M (Q w) / (C₀ * (Q w) ^ (-M.beta)) - 1| ≤
          (if M.beta = 1 then Ctail * v ^ (-1 : ℝ) * Real.log v
            else Ctail * v ^ (-min 1 (1 / M.beta))) := by
        rw [hTransfer (Q w) hQcut]
        exact hNominalSurvival
      have hratio := hill_radial_ratio_bound hQpos hC₀ hRV.1 hSurvival hDensity hSmall
      rw [hEta]
      calc
        _ ≤ 4 * (if M.beta = 1 then Ctail * v ^ (-1 : ℝ) * Real.log v
          else Ctail * v ^ (-min 1 (1 / M.beta))) / M.beta := by
            simpa only [gamma] using hratio.2
        _ = _ := by dsimp [C]; split_ifs <;> ring
    have hBdd : BddAbove ((fun v => |eta v|) '' Set.Ici v₀) := by
      refine ⟨if M.beta = 1 then C * v₀ ^ (-1 : ℝ) * Real.log v₀
        else C * v₀ ^ (-min 1 (1 / M.beta)), ?_⟩
      rintro z ⟨v, hv, rfl⟩
      exact hRawEnvelope v₀ le_rfl v hv
    have hEnvelope : ∀ v ≥ v₀, hillTailBiasEnvelope eta v₀ v ≤
        if M.beta = 1 then C * v ^ (-1 : ℝ) * Real.log v
        else C * v ^ (-min 1 (1 / M.beta)) := by
      intro v hv
      apply hillTailBiasEnvelope_le
      intro w hw
      exact hRawEnvelope v hv w ((le_max_left v v₀).trans hw)
    let etaBar := hillTailBiasEnvelope eta v₀
    have hmono : AntitoneOn etaBar (Set.Ici v₀) :=
      (hillTailBiasEnvelope_antitone eta hBdd).antitoneOn (Set.Ici v₀)
    have heta : ∀ v ≥ v₀, |eta v| ≤ etaBar v :=
      fun _ hv => abs_bias_le_hillTailBiasEnvelope eta hBdd hv
    obtain ⟨a, ha, hCandidate⟩ :=
      hill_envelope_candidate_eventually etaBar hRV.1 hd hC hv hEnvelope
    obtain ⟨nCand, hnCand⟩ := eventually_atTop.mp hCandidate
    refine ⟨max n0 nCand, a, ha, ?_⟩
    intro n hn hiid
    let k := ⌊a * hillOracleScale M.beta n (hillDeviation n delta)⌋₊
    obtain ⟨hkpos, hk, hdomain, hbudget⟩ := hnCand n ((le_max_right _ _).trans hn)
    have hklt : k < n := by
      have := (Finset.mem_Icc.mp hk).2
      omega
    obtain ⟨T, V, S, hS, hSind, hSlaw,
      hT, hV, hVind, hVlaw, hThresholdImp, hIncrements⟩ :=
      hRep n ((le_max_left _ _).trans hn) hiid k hklt (by omega)
        (hRawBase.trans ((le_max_left vBase V).trans hdomain))
    let Yorder := hillDecreasingOrder V
    obtain ⟨hYorder, hSort⟩ := hill_decreasing_order_data V
    have hYmeas : Measurable (fun w => Yorder w ⟨k, hklt⟩) := by
      exact hill_decreasing_order_measurable V hV ⟨k, hklt⟩
    obtain ⟨A, B, hBsum, hcenter, hAverage⟩ := hill_spacing_average_data S
    obtain ⟨ℱ, hB, hAdapt, hStopped, hMoments⟩ :=
      hill_spacing_process_data E.P S hS hSind hSlaw B hBsum
    have hFiniteMoments : ∀ lam : ℝ, 0 < lam → lam < 1 →
        (∀ i ≤ n, Integrable (fun w => Real.exp
            (lam * B i w - (i : ℝ) * (lam ^ 2 / (2 * (1 - lam))))) E.P ∧
          Integrable (fun w => Real.exp
            (lam * (-B i w) - (i : ℝ) * (lam ^ 2 / (2 * (1 - lam))))) E.P) ∧
        (∀ i < n, Integrable (fun w => Real.exp (lam * (B (i + 1) w - B i w))) E.P ∧
          Integrable (fun w => Real.exp (-lam * (B (i + 1) w - B i w))) E.P) ∧
        (∀ i < n, E.P[(fun w => Real.exp (lam * (B (i + 1) w - B i w))) | ℱ i]
            =ᵐ[E.P] (fun _ => Real.exp (-lam) / (1 - lam)) ∧
          E.P[(fun w => Real.exp (-lam * (B (i + 1) w - B i w))) | ℱ i]
            =ᵐ[E.P] (fun _ => Real.exp lam / (1 + lam))) := by
      intro lam hlam hlamone
      have hMoment := hill_spacing_conditional_moments_of_increment_laws
        E.P B ℱ hB n hMoments hlam hlamone
      have hzero : ∀ w, B 0 w = 0 := by intro w; simp [hcenter w 0]
      have hInt := hill_compensated_integrable_of_exact_moments E.P B ℱ hAdapt
        hzero n hlam hlamone hMoment
      exact ⟨hInt, fun i hi => hill_increment_integrable_of_exact_moments E.P B ℱ
        hlam hlamone i (hMoment i hi), hMoment⟩
    have hTwoK : 2 * k ≤ n := by
      have hkR : 0 < (k : ℝ) := by exact_mod_cast hkpos
      have hratio : 1 ≤ (n : ℝ) / (2 * k) :=
        hvRaw.le.trans ((hRawBase.trans (show vBase ≤ v₀ from le_max_left _ _)).trans hdomain)
      have hreal := (le_div_iff₀ (by positivity : 0 < 2 * (k : ℝ))).mp hratio
      norm_num only [one_mul] at hreal
      exact_mod_cast hreal
    have hTailMean : ∀ i, (∫ w, if Real.log ((n : ℝ) / (2 * k)) < V i w
        then (1 : ℝ) else 0 ∂E.P) = 2 * (k : ℝ) / n :=
      fun i => hill_exponential_threshold_mean E.P (V i) (hV i) (hVlaw i) hkpos hTwoK
    refine ⟨k, hklt, A, B, T, V, Yorder, ℱ, hB, hcenter, hAdapt, hStopped, hFiniteMoments,
      hT, hV, hVind, hYorder, hSort, hYmeas, hTailMean, hThresholdImp, ?_, le_rfl⟩
    intro w hw
    obtain ⟨hpos, Y, hSpacing, hY, hR, hThreshold⟩ := hIncrements w hw
    let Q' : ℝ → ℝ := fun v => (v ^ 2 * f (Q v))⁻¹
    have hA : ∀ i ∈ Finset.Icc (hillLower n) k,
        A i w = (i : ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 i,
          (j : ℝ) * (Y j - Y (j + 1)) := by
      intro i hi
      have hik := (Finset.mem_Icc.mp hi).2
      exact hAverage i (by omega) w Y (fun j hj => hSpacing j (hj.trans_le hik))
    refine ⟨hpos, Y, Q, Q', eta, hA, hY, hR, ?_⟩
    intro u hu
    have hvu : v₀ ≤ Real.exp u :=
      hdomain.trans (hThreshold.trans (Real.exp_le_exp.mpr hu))
    have hInterior : vRaw < Real.exp u := by
      have hbase : vBase ≤ Real.exp u := (le_max_left _ _).trans hvu
      linarith
    have hRawInverse : ∀ v ≥ vRaw, tailProb M (Q v) = v⁻¹ :=
      fun v hv => (hRawQuantile v hv v le_rfl).2.1
    have hQcontinuous := hill_quantile_continuousAt_of_tail_range (tailProb M) Q
      (zero_lt_one.trans hvRaw) (tailProb_antitone M) hRawInverse
      (hRawQuantile vRaw le_rfl vRaw le_rfl).1 hInterior
    have hInverse := hill_quantile_eventually_reciprocal_survival
      (tailProb M) Q hRawInverse hInterior
    obtain ⟨hQcut, hQpos', hNominalSurvival, hDensity, hSmall, hEta⟩ :=
      hRadial v₀ le_rfl (Real.exp u) hvu
    have hfContinuous := hfContinuous (Q (Real.exp u)) hQpos'
    have hSurvival :
        |tailProb M (Q (Real.exp u)) / (C₀ * (Q (Real.exp u)) ^ (-M.beta)) - 1| ≤
          (if M.beta = 1 then Ctail * v₀ ^ (-1 : ℝ) * Real.log v₀
            else Ctail * v₀ ^ (-min 1 (1 / M.beta))) := by
      rw [hTransfer (Q (Real.exp u)) hQcut]
      exact hNominalSurvival
    have hfpos := (hill_radial_ratio_bound hQpos' hC₀ hRV.1
      hSurvival hDensity hSmall).1
    have hSurvivalDeriv : HasDerivAt (tailProb M) (-f (Q (Real.exp u)))
        (Q (Real.exp u)) := by
      convert hill_survival_hasDerivAt_of_tail_density (M.mu.map (radius M)) f hfmeas
        hfLaw hQcut hfContinuous hfpos.le using 1
      ext y
      rw [map_measureReal_apply (by fun_prop) measurableSet_Ioi]
      rfl
    obtain ⟨hQderiv, hRatio⟩ := hill_continuous_quantile_derivative_and_ratio (tailProb M) Q
      (Real.exp_pos u) hfpos.ne' hQpos'.ne' hSurvivalDeriv hQcontinuous hInverse
    have hQeta : Real.exp u * Q' (Real.exp u) / Q (Real.exp u) - gamma M =
        eta (Real.exp u) := by rw [hRatio, hEta]
    refine ⟨hQpos', hQderiv, hQeta, ?_⟩
    exact hill_tail_envelope_above_threshold eta etaBar (by omega) hmono heta
      hdomain hThreshold hu (by simpa only [gamma] using hbudget)
  obtain ⟨a, hapos, hacut, hPositive⟩ := hill_nominal_partition_density_positive_tail
    (fun i => l1Norm (fun r => model.A r i)) hRV.1 hkappa
    (fun i => model.constants.2.1.trans_le (model.matrix.2.1 i).1)
    (fun i => (model.matrix.2.1 i).2)
    ((mul_pos_iff_of_pos_left hkappa).mp hC₀) radialCutoff
  suffices hDensityAndRepresentation :
      (∀ r > radialCutoff, (M.mu.map (radius M)) (Set.Ioi r) =
        (volume.withDensity (fun x => ENNReal.ofReal (f x))) (Set.Ioi r)) ∧
      (∀ (Q : ℝ → ℝ) (v₀ : ℝ), 1 < v₀ →
        (∀ w ≥ v₀, a + 1 ≤ Q w ∧ tailProb M (Q w) = w⁻¹ ∧
          (∀ x > Q w, ∃ z ≥ w, Q z = x)) → representation Q v₀) by
    obtain ⟨hLaw, hRep⟩ := hDensityAndRepresentation
    obtain ⟨Q, v₀, hv₀, hQ⟩ := hill_exists_quantile_of_positive_tail_density
      (M.mu.map (radius M)) f hfmeas hLaw (by linarith : radialCutoff < a + 1)
      (fun r hr => hfContinuous r (by linarith))
      (fun r hr => hPositive r (by linarith))
    have hQtail : ∀ w ≥ v₀, a + 1 ≤ Q w ∧ tailProb M (Q w) = w⁻¹ ∧
        (∀ x > Q w, ∃ z ≥ w, Q z = x) := by
      intro w hw
      obtain ⟨hqa, hInv, hRange⟩ := hQ w hw
      refine ⟨hqa, ?_, hRange⟩
      rw [map_measureReal_apply (measurable_radius M) measurableSet_Ioi] at hInv
      exact hInv
    let eta : ℝ → ℝ := fun v => tailProb M (Q v) / (Q v * f (Q v)) - gamma M
    refine ⟨eta, Q, v₀, hv₀, hLaw, ?_, hRep Q v₀ hv₀ hQtail⟩
    intro v hv w hw
    obtain ⟨_, hInv, hRange⟩ := hQtail w (hv.trans hw)
    exact ⟨hRange, hInv, rfl⟩
  have hLaw : ∀ r > radialCutoff, (M.mu.map (radius M)) (Set.Ioi r) =
      (volume.withDensity (fun x => ENNReal.ofReal (f x))) (Set.Ioi r) := by
    intro r hr
    have hm : 0 < m := by
      obtain ⟨hdim, hdim'⟩ := model.constants.1
      omega
    have hcutpos : 0 < radialCutoff := by
      dsimp [radialCutoff]
      have hu : 0 < tp.u := zero_lt_one.trans model.constants.2.2.2.1
      obtain ⟨_, _, _, _, _, _, _, _, _, hz⟩ := model.constants
      have hi : 0 < (componentIndex : ℝ) := by exact_mod_cast hComponentIndex
      positivity
    have ha : ∀ i, 0 < l1Norm (fun r => model.A r i) :=
      fun i => model.constants.2.1.trans_le (model.matrix.2.1 i).1
    calc
      _ = ENNReal.ofReal kappa *
          ((hillNominalComponentLaw M.beta m).map
            (fun z => l1Norm (model.A.mulVec z))) (Set.Ioi r) :=
        hTransferMeasure _ measurableSet_Ioi (fun x hx => hr.trans hx)
      _ = _ := hill_nominal_density_tail_of_slices hm model.A hRV.1 model.matrix.1
        ha kappa hkappa.le r (hcutpos.trans hr)
        (hill_nominal_partition_slice _ hRV.1 ha (hcutpos.trans hr))
  refine ⟨hLaw, ?_⟩
  -- Construct the survival coordinates explicitly. The marginal exponential
  -- law follows from the continuous probability transform; the ordered-density
  -- change of variables supplies their independent spacing law.
  intro Q v₀ hv₀ hQ
  let V : (n : ℕ) → Fin n → E.Om → ℝ := fun n i w =>
    -Real.log (tailProb M (l1Norm (E.Zraw i.val w).2.2.2))
  let Y : ℕ → E.Om → ℕ → ℝ := fun n w j =>
    -Real.log (tailProb M (orderedRadius E n w j))
  have hInv : ∀ v ≥ v₀, tailProb M (Q v) = v⁻¹ := fun v hv => (hQ v hv).2.1
  have hRange := (hQ v₀ le_rfl).2.2
  have hQpos : 0 < Q v₀ := by linarith [(hQ v₀ le_rfl).1]
  have hSurvivalPos := hill_survival_positive_of_quantile_range (tailProb M) Q
    (zero_lt_one.trans hv₀) (tailProb_antitone M) hInv hRange
  have hCoordinateMono := hill_log_survival_monotone (tailProb M)
    (tailProb_antitone M) hSurvivalPos
  obtain ⟨_, hStrict⟩ := hill_survival_strictAntiOn_of_positive_tail_density
    (M.mu.map (radius M)) f hfmeas hLaw hacut
    (fun r hr => hfContinuous r (hapos.trans_le hr)) hPositive
  have hStrictTail : StrictAntiOn (tailProb M) (Set.Ici a) := by
    convert hStrict using 1
    ext r
    rw [map_measureReal_apply (measurable_radius M) measurableSet_Ioi]
    rfl
  suffices hJoint : ∀ n, IIDSampling E n →
      iIndepFun (hillOrderedSpacing (V n)) E.P ∧
        (∀ j, E.P.map (hillOrderedSpacing (V n) j) = expMeasure 1) by
    refine ⟨0, ?_⟩
    intro n _ hiid k hklt hkpos hv
    obtain ⟨hV, hVind, hSort⟩ := hill_raw_survival_coordinates_data E hiid
      (tailProb M) (measurable_tailProb M) hCoordinateMono
    obtain ⟨hSind, hSlaw⟩ := hJoint n hiid
    let T : Set E.Om := {w | Real.log ((n : ℝ) / (2 * k)) ≤
      hillDecreasingOrder (V n) w ⟨k, hklt⟩}
    have hT : MeasurableSet T := by
      exact measurableSet_le measurable_const
        (hill_decreasing_order_measurable (V n) hV ⟨k, hklt⟩)
    have hVlaw : ∀ i, E.P.map (V n i) = expMeasure 1 := fun i =>
      hill_raw_survival_coordinates_exponential M E tp model hiid i
    refine ⟨T, V n, hillOrderedSpacing (V n),
      hill_ordered_spacing_measurable (V n) hV, hSind, hSlaw,
      hT, hV, hVind, hVlaw, fun _ hw => hw, ?_⟩
    intro w hw
    have hthreshold : Q ((n : ℝ) / (2 * k)) ≤ orderedRadius E n w (k + 1) := by
      apply hill_radius_above_quantile_of_log_survival (tailProb M)
        (tailProb_antitone M) hStrictTail hSurvivalPos
        (by linarith [(hQ _ hv).1]) (hInv _ hv)
      exact (hSort w ⟨k, hklt⟩) ▸ hw
    obtain ⟨hpos, hOrder, hRecovery, hThreshold⟩ := hill_survival_coordinate_prefix E
      (tailProb M) Q w (zero_lt_one.trans hv₀) (tailProb_antitone M) hInv hRange
      hQpos hklt hv hthreshold
    refine ⟨hpos, Y n w, ?_, hOrder, hRecovery, hThreshold⟩
    intro j hj
    exact hill_ordered_spacing_agreement (V n) (Y n w) w hklt (hSort w) j hj
  intro n hiid
  obtain ⟨hV, hVind, _⟩ := hill_raw_survival_coordinates_data E hiid
    (tailProb M) (measurable_tailProb M) hCoordinateMono
  exact hill_independent_exponential_spacing_law E.P (V n) hV hVind
    (fun i => hill_raw_survival_coordinates_exponential M E tp model hiid i)
end Papers.TbsExtremeEffects
