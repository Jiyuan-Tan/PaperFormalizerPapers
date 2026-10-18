module
public import Papers.TbsExtremeEffects.Helpers.RateAssembly
public import Papers.TbsExtremeEffects.Helpers.AngularRates

/-! Fixed-threshold NETE bounds under the supplied angular rate and an enlarged cutoff. -/

public section
set_option linter.style.longLine false
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
variable {q d m : ℕ}

/-- [The extreme model $M$](hyp:M), [tail parameters](hyp:tp), [noise regular variation](hyp:hRV), [asymptotic homogeneity](hyp:hHom), [an admissible Pareto tail model](hyp:hTail), and [the three requested onset thresholds](hyp:tMin,tDR,tIPW) imply [the existence of a common sufficiently large cutoff](goal) that dominates $t_{min}$ and satisfies the required tail controls. -/
-- @node: exists_rateCutoffLarge
lemma exists_rateCutoffLarge (M : ExtremeModel q d) (tp : TailParams)
    (hRV : NoiseRegularlyVarying M) (hHom : AsymptoticHomogeneity M)
    (hTail : Nonempty (ParetoTailModel M m tp)) (tMin tDR tIPW : ℝ) :
    ∃ tW : ℝ, tMin ≤ tW ∧ RateCutoffLarge M tW tDR tIPW := by
  classical
  obtain ⟨model⟩ := hTail
  obtain ⟨k, hk, kappa, hkappa, hTransfer⟩ := hill_radial_tail_transfer M tp model
  let cutoff := tp.u * (tp.zeta * (k : ℝ) ^ ((1 - 2 * tp.s) / M.beta))
  let a : Fin m → ℝ := fun i => l1Norm (fun r => model.A r i)
  have ha : ∀ i, 0 < a i := fun i =>
    model.constants.2.1.trans_le (model.matrix.2.1 i).1
  have hm : 0 < m := by
    obtain ⟨hd, hdm⟩ := model.constants.1
    omega
  have hsum : 0 < ∑ i, (a i) ^ M.beta :=
    Finset.sum_pos (fun i _ => Real.rpow_pos_of_pos (ha i) _)
      ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  let C := kappa * ∑ i, (a i) ^ M.beta
  have hC : 0 < C := mul_pos hkappa hsum
  let f : ℝ → ℝ := fun r => kappa * ∑ i, ∫ z,
    hillLargestSummandIntegrand a M.beta r (fun j => a j * z j) i
      ∂hillNominalComponentLaw M.beta m
  have hf : Measurable f := hill_nominal_partition_density_measurable a hRV.1 kappa
  obtain ⟨T, hDensity⟩ := eventually_atTop.mp
    (hill_nominal_partition_relative_error_eventually a hRV.1 hkappa ha
      (fun i => (model.matrix.2.1 i).2) hsum)
  have hSurvival : ∀ r, max 1 (max (cutoff + 1) T) ≤ r →
      |tailProb M r / (C * r ^ (-M.beta)) - 1| ≤ 1 / 2 := by
    intro r hr
    have hrpos : 0 < r := zero_lt_one.trans_le ((le_max_left _ _).trans hr)
    have hrT : T ≤ r := (le_max_right _ _).trans ((le_max_right _ _).trans hr)
    have hrCut : cutoff < r := by
      have := (le_max_left (cutoff + 1) T).trans ((le_max_right _ _).trans hr)
      linarith
    have hError : ∀ x > r, |f x / (M.beta * C * x ^ (-M.beta - 1)) - 1| ≤ 1 / 2 :=
      fun x hx => hDensity x (hrT.trans hx.le)
    have hLaw : (M.mu.map (radius M)) (Set.Ioi r) =
        (volume.withDensity (fun x => ENNReal.ofReal (f x))) (Set.Ioi r) := by
      calc
        _ = ENNReal.ofReal kappa *
            ((hillNominalComponentLaw M.beta m).map
              (fun z => l1Norm (model.A.mulVec z))) (Set.Ioi r) :=
          hTransfer _ measurableSet_Ioi (fun x hx => hrCut.trans hx)
        _ = _ := hill_nominal_density_tail_of_slices hm model.A hRV.1 model.matrix.1
          ha kappa hkappa.le r hrpos (hill_nominal_partition_slice a hRV.1 ha hrpos)
    have hIntegral := hill_tail_mass_eq_density_integral (M.mu.map (radius M)) f hf
      (fun x hx => (hill_density_pos_of_relative_error hRV.1 hC (hrpos.trans hx)
        (hError x hx) (by norm_num)).le) hLaw
    rw [map_measureReal_apply (measurable_radius M) measurableSet_Ioi] at hIntegral
    exact hill_survival_relative_error_of_density f hRV.1 hC hrpos hf hIntegral hError
  obtain ⟨Te, he⟩ := eventually_atTop.mp ((tendsto_order.mp hHom.2.1).2 1 (by norm_num))
  let tW := max tMin (max tDR (max tIPW (max Te (max 1 (max (cutoff + 1) T)))))
  have hLower : max 1 (max (cutoff + 1) T) ≤ tW := by dsimp [tW]; order
  refine ⟨tW, le_max_left _ _, ?_⟩
  refine ⟨(le_max_left _ _).trans hLower, ?_, ?_, ?_, ?_⟩
  · dsimp [tW]; order
  · dsimp [tW]; order
  · intro r hr
    apply (he r _).le
    exact (show Te ≤ tW by dsimp [tW]; order).trans hr
  · intro t ht r hr
    have htpos : 0 < t := zero_lt_one.trans_le ((le_max_left _ _).trans (hLower.trans ht))
    have htr : t ≤ t * r := by nlinarith
    have hden := tailProb_pos_of_regularVariation M hRV t
    have hscale : 0 < C * t ^ (-M.beta) := by positivity
    have hLow := (abs_le.mp (hSurvival t (hLower.trans ht))).1
    have hHigh := (abs_le.mp (hSurvival (t * r) ((hLower.trans ht).trans htr))).2
    have hLow' : C * t ^ (-M.beta) / 2 ≤ tailProb M t := by
      have := (le_div_iff₀ hscale).mp (show 1 / 2 ≤ tailProb M t / (C * t ^ (-M.beta)) by linarith)
      linarith
    have hHigh' : tailProb M (t * r) ≤ 3 / 2 * (C * (t * r) ^ (-M.beta)) := by
      exact (div_le_iff₀ (by positivity)).mp (by linarith)
    rw [Real.mul_rpow htpos.le (by linarith : 0 ≤ r)] at hHigh'
    apply (div_le_iff₀ hden).mpr
    have hp : 0 < r ^ (-M.beta) := Real.rpow_pos_of_pos (by linarith) _
    nlinarith [mul_le_mul_of_nonneg_right hLow' hp.le]


-- @node: thm:rate
/-- [The extreme model $M$](hyp:M), [tail parameters](hyp:tp), [consistency](hyp:hConsistency), [exogeneity](hyp:hExogeneity), [noise regular variation](hyp:hRV), [noise independence](hyp:hNoise), [bounded covariates](hyp:hX), [asymptotic homogeneity](hyp:hHomogeneity), [an admissible Pareto tail model](hyp:hTail), [an outcome exponent below the tail index](hyp:hAlpha), [a conditional-mean version](hyp:hMean), [identification side conditions](hyp:hSide), [the $G$-bound constant and bound](hyp:Cgb,hGBound), [a positive admissible rate exponent](hyp:a0,ha0,ha0beta), and [the angular-rate inputs](hyp:CW,k,tW0,hAngular) imply [a common cutoff together with doubly robust and inverse-probability-weighted fixed-threshold rate and variance guarantees, and their adaptive product-success guarantee](goal). -/
theorem nete_rate (M : ExtremeModel q d)
    (tp : TailParams)
    (hConsistency : Consistency M) (hExogeneity : Exogeneity M)
    (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M)
    (hX : CovariateBounded M) (hHomogeneity : AsymptoticHomogeneity M)
    (hTail : Nonempty (ParetoTailModel M m tp))
    (hAlpha : AlphaLtBeta M)
    (hMean : ConditionalMeanVersion M)
    (hSide : IdentificationSideConditions M)
    (Cgb : ℝ) (hGBound : GBound M Cgb)
    (a0 : ℝ) (ha0 : 0 < a0) (ha0beta : a0 < M.beta)
    (CW k tW0 : ℝ) (hAngular : AngularRateBound M tp CW k tW0) :
    ∃ t0 : ℝ, tW0 ≤ t0 ∧
      (∃ Kd Td Ki Ti : ℝ, 0 < Kd ∧ 1 ≤ Td ∧ 0 < Ki ∧ 1 ≤ Ti ∧
        RateCutoffLarge M t0 Td Ti ∧
        ∀ (E : NeteExperiment M) (c : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ),
          EstimatedOverlap E c →
          (EtaRateConclusion E .dr c Cgb Kd Td a0 Rp Rg Ralpha ∧
            EtaVarianceConclusion E .dr c Cgb Kd Td a0 Rp Rg Ralpha) ∧
          (EtaRateConclusion E .ipw c Cgb Ki Ti a0 Rp Rg Ralpha ∧
            EtaVarianceConclusion E .ipw c Cgb Ki Ti a0 Rp Rg Ralpha)) ∧
      ∀ E : NeteExperiment M,
        let Cg := sourceHillConstant M E tp hRV hNoise hTail
        ∀ (c : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ),
        EstimatedOverlap E c →
        (∀ n, EvenSampleSize n → NuisanceErrorBounds E n Rp Rg Ralpha) →
        (∀ n, EvenSampleSize n → NuisanceIntegrability E n Rp Rg Ralpha) →
        ∀ V : ℝ, GenericRateConstant (fun C =>
          ∀ delta : ℝ, 0 < delta → delta < 1 / 2 →
            ∃ n0 : ℕ, HillConstantAt E (delta / 6) n0 (Cg (delta / 6)) ∧
              ∀ n, n0 ≤ n → EvenSampleSize n → IIDSampling E n → ExponentTraining E n →
                ∀ t, t0 ≤ t →
                  Ralpha n (delta / 12) ≤ a0 →
                  (n : ℝ) * tailProb M t ≥ 16 * Real.log (12 / delta) →
                  ∀ Bdr Bipw : E.Om → ℝ,
                    Measurable[trainSigma E n] Bdr → Measurable[trainSigma E n] Bipw →
                    (∀ w, 0 < Bdr w) → (∀ w, 0 < Bipw w) →
                    (E.P {w | ProductSuccessAngular E tp CW k c Cgb a0 C (Cg (delta / 6)) V delta Rp Rg Ralpha
                      n t Bdr Bipw w}).toReal ≥ 1 - delta) := by
  obtain ⟨T, hT, hRates⟩ := nete_rate_wasserstein M tp hConsistency hExogeneity
    hRV hNoise hX hHomogeneity hTail hAlpha hMean hSide Cgb hGBound a0 ha0 ha0beta
  obtain ⟨Td, hTd, hDR⟩ := eta_dr_rate M tp hConsistency hExogeneity
    hRV hNoise hX hHomogeneity hTail hAlpha hMean hSide Cgb hGBound a0 ha0 ha0beta
  obtain ⟨Ti, hTi, hIPW⟩ := eta_ipw_rate M tp hConsistency hExogeneity
    hRV hNoise hX hHomogeneity hTail hAlpha hMean hSide Cgb hGBound a0 ha0 ha0beta
  let Kd : ℝ := 4 / (M.beta - a0)
  let Ki : ℝ := 4 / (M.beta - a0)
  have hKd : 0 < Kd := by dsimp [Kd]; positivity
  have hKi : 0 < Ki := by dsimp [Ki]; positivity
  obtain ⟨tW, hLower, hCutoff⟩ := exists_rateCutoffLarge M tp hRV hHomogeneity hTail
    (max tW0 (max T (max Td Ti))) Td Ti
  have hW0 : tW0 ≤ tW := (le_max_left _ _).trans hLower
  have hWT : T ≤ tW := (le_max_left _ _).trans ((le_max_right _ _).trans hLower)
  refine ⟨tW, hW0, ⟨Kd, Td, Ki, Ti, hKd, hTd, hKi, hTi, hCutoff, ?_⟩, ?_⟩
  · intro E c Rp Rg Ralpha hOverlap
    exact ⟨hDR E c Rp Rg Ralpha hOverlap, hIPW E c Rp Rg Ralpha hOverlap⟩
  · intro E
    dsimp only
    intro c Rp Rg Ralpha hOverlap hNuisance hInt V
    obtain ⟨C, hC, hProb⟩ := hRates E c Rp Rg Ralpha hOverlap hNuisance hInt V
    refine ⟨C, hC, ?_⟩
    intro delta hd hd1
    obtain ⟨n0, hHill, hProbN⟩ := hProb delta hd hd1
    refine ⟨n0, hHill, ?_⟩
    intro n hn hnEven hIID hTraining t ht ha hbudget Bdr Bipw hBdr hBipw hBdpos hBipos
    apply (hProbN n hn hnEven hIID hTraining t (hWT.trans ht) ha hbudget
      Bdr Bipw hBdr hBipw hBdpos hBipos).trans
    apply measureReal_mono (h₂ := measure_ne_top E.P _)
    intro w hw
    exact productSuccess_angular E tp CW k c Cgb a0 C _ V delta Rp Rg Ralpha
      n t Bdr Bipw w hC (angular_term_bound M tp hHomogeneity hAngular (hW0.trans ht)) hw

end Papers.TbsExtremeEffects
