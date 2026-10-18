module
public import Papers.TbsExtremeEffects.Helpers.JointScoreSampling
public import Papers.TbsExtremeEffects.Helpers.ProductSimplification

/-! Assembly of NETE first-factor rates from shared conditional-mean bounds. -/

@[expose] public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
variable {q d : ℕ} {M : ExtremeModel q d}

/-- For [an experiment](hyp:E), [overlap, tail, variance, and confidence constants](hyp:c,Cgb,a0,V,delta), [nuisance rates](hyp:Rp,Rg,Ralpha), [sample size](hyp:n), and [threshold](hyp:t), [the shared-mean data condition](goal) says that there is a measurable high-probability training event on which exponent accuracy and both conditional score-mean bounds hold, with conditional second-moment control. The existence/event, exponent, score-mean, and conditional moment requirements are [clauses 1](step:1), [2](step:2), [3](step:3), and [4](step:4). -/
-- @node: ProductSharedMeanData
def ProductSharedMeanData (E : NeteExperiment M)
    (c Cgb a0 V delta : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) : Prop :=
  ∃ G : Set E.Om, MeasurableSet[trainSigma E n] G ∧ 1 - delta / 12 ≤ E.P.real G ∧
    (∀ w ∈ G, |E.alphaHat n w - M.alpha| ≤ Ralpha n (delta / 12)) ∧
    (∀ kind, ∀ᵐ w ∂E.P, w ∈ G →
      Integrable (score E kind n w) (obsTailLaw M t) ∧
      |(∫ z, score E kind n w z ∂obsTailLaw M t) - etaTarget M| ≤
        etaRemainder E kind c Cgb (4 / (M.beta - a0)) Rp Rg Ralpha n t (delta / 12) w) ∧
    (secondMomentsOnNuisance E n t (delta / 12) Rp Rg Ralpha V →
      ∀ kind, ∀ᵐ w ∂E.P, w ∈ G →
        MemLp (score E kind n w) 2 (obsTailLaw M t) ∧
          (scoreVariance E kind n t w).toReal ≤ V)

/-- For [an experiment](hyp:E), [overlap, tail, simplification, variance, and confidence constants](hyp:c,Cgb,a0,D,Cg,V,delta), [nuisance rates](hyp:Rp,Rg,Ralpha), [sample size](hyp:n), and [threshold](hyp:t), [the mean-simplification condition](goal) says that the listed moment, threshold, logarithmic, and denominator conditions imply uniform simplified bounds for each estimator and outcome. The two resulting bounds are [clause 1](step:1) and [clause 2](step:2). -/
-- @node: ProductMeanSimplification
def ProductMeanSimplification (E : NeteExperiment M)
    (c Cgb a0 D Cg V delta : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (n : ℕ) (t : ℝ) : Prop :=
  secondMomentsOnNuisance E n t (delta / 12) Rp Rg Ralpha V → Real.exp 1 ≤ t →
    Ralpha n (delta / 12) * Real.log t ≤ 1 →
    radialQ M Cg delta Ralpha n ≤ radialH M / 2 →
    0 ≤ hillErrorBound M Cg delta n →
    ∀ w, (n : ℝ) * tailProb M t / 4 ≤ evalCount E n t w → ∀ kind,
      Real.sqrt (12 * V / (delta * evalCount E n t w)) +
          etaRemainder E kind c Cgb (4 / (M.beta - a0)) Rp Rg Ralpha n t (delta / 12) w ≤
        D * simplifiedRate E kind V Cg delta Rp Rg Ralpha n t w ∧
      Ralpha n (delta / 12) * Real.log t + hillErrorBound M Cg delta n ≤
        simplifiedRate E kind V Cg delta Rp Rg Ralpha n t w

-- @node: product_first_factor_probability_of_shared_means
/-- Given [an experiment](hyp:E), [overlap, tail, simplification, variance, and confidence constants](hyp:c,Cgb,a0,D,Cg,V,delta), [nuisance rates](hyp:Rp,Rg,Ralpha), [sample size](hyp:n), [an even-sample condition](hyp:hn), [IID sampling](hyp:hIID), [regularly varying noise](hyp:hRV), [exponent training](hyp:hTraining), [threshold](hyp:t), [a positive tolerance](hyp:hd), [a tolerance below one half](hyp:hd1), [the effective-sample budget](hyp:hbudget), [the Hill-event probability bound](hyp:hHill), [shared mean data](hyp:hMean), [the deterministic simplification](hyp:hSimple), [DR and IPW truncation bounds](hyp:Bdr,Bipw), [their training measurability](hyp:hBdr,hBipw), and [their strict positivity](hyp:hBdpos,hBipos), then [the first-factor-rate event has probability at least one minus the tolerance](goal). -/
lemma product_first_factor_probability_of_shared_means (E : NeteExperiment M)
    (c Cgb a0 D Cg V delta : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ)
    (n : ℕ) (hn : EvenSampleSize n) (hIID : IIDSampling E n)
    (hRV : NoiseRegularlyVarying M) (hTraining : ExponentTraining E n)
    (t : ℝ) (hd : 0 < delta) (hd1 : delta < 1 / 2)
    (hbudget : 16 * Real.log (12 / delta) ≤ (n : ℝ) * tailProb M t)
    (hHill : 1 - delta / 6 ≤ E.P.real {w |
      |hillAdaptive E n (delta / 6) w - gamma M| ≤ hillErrorBound M Cg delta n})
    (hMean : ProductSharedMeanData E c Cgb a0 V delta Rp Rg Ralpha n t)
    (hSimple : ProductMeanSimplification E c Cgb a0 D Cg V delta Rp Rg Ralpha n t)
    (Bdr Bipw : E.Om → ℝ)
    (hBdr : Measurable[trainSigma E n] Bdr) (hBipw : Measurable[trainSigma E n] Bipw)
    (hBdpos : ∀ w, 0 < Bdr w) (hBipos : ∀ w, 0 < Bipw w) :
    1 - delta ≤ E.P.real {w |
      ProductFirstFactorRates E c Cgb a0 D Cg V delta Rp Rg Ralpha n t Bdr Bipw w} := by
  classical
  obtain ⟨G, hG, hGprob, hAlpha, hMeans, hMoments⟩ := hMean
  let N := {w | (n : ℝ) * tailProb M t / 4 ≤ (evalCount E n t w : ℝ)}
  let H := {w | |hillAdaptive E n (delta / 6) w - gamma M| ≤ hillErrorBound M Cg delta n}
  let B : EstimatorKind → E.Om → ℝ := fun kind => match kind with
    | .dr => Bdr
    | .ipw => Bipw
  have hcal : 4 / (delta / 3) = 12 / delta := by field_simp; ring
  have htol : (delta / 3) / 4 = delta / 12 := by ring
  obtain ⟨hN, hNprob, hcount⟩ := evaluation_count_event E n t hn hIID
    (delta := delta / 3) (by positivity) (by linarith)
    (by simpa only [hcal] using hbudget)
  have hB kind : Measurable[trainSigma E n] (B kind) := by
    cases kind
    · exact hBipw
    · exact hBdr
  have hBpos kind w : 0 ≤ B kind w := by
    cases kind
    · exact (hBipos w).le
    · exact (hBdpos w).le
  have hf kind : ∀ᵐ w ∂E.P, w ∈ G → Integrable (score E kind n w) (obsTailLaw M t) := by
    filter_upwards [hMeans kind] with w hw hwG
    exact (hw hwG).1
  have hMem (hm : secondMomentsOnNuisance E n t (delta / 12) Rp Rg Ralpha V) kind :
      ∀ᵐ w ∂E.P, w ∈ G → MemLp (score E kind n w) 2 (obsTailLaw M t) := by
    filter_upwards [hMoments hm kind] with w hw hwG
    exact (hw hwG).1
  have hSampling := joint_score_sampling_probability E n hn hIID hRV hTraining t G N H
    hG hN B hB hBpos hd hGprob (by simpa only [htol] using hNprob) hHill
    hcount hf (secondMomentsOnNuisance E n t (delta / 12) Rp Rg Ralpha V) hMem
  apply (show 1 - delta ≤ 1 - 5 * delta / 6 by linarith).trans
  apply hSampling.trans
  apply ENNReal.toReal_mono (measure_ne_top E.P _)
  apply measure_mono_ae
  have hAllMeans : ∀ᵐ w ∂E.P, ∀ kind, w ∈ G →
      |(∫ z, score E kind n w z ∂obsTailLaw M t) - etaTarget M| ≤
        etaRemainder E kind c Cgb (4 / (M.beta - a0)) Rp Rg Ralpha n t (delta / 12) w := by
    filter_upwards [hMeans .dr, hMeans .ipw] with w hdr hipw kind hwG
    cases kind
    · exact (hipw hwG).2
    · exact (hdr hwG).2
  have hAllVariance : ∀ᵐ w ∂E.P,
      secondMomentsOnNuisance E n t (delta / 12) Rp Rg Ralpha V →
      ∀ kind, w ∈ G → (scoreVariance E kind n t w).toReal ≤ V := by
    by_cases hm : secondMomentsOnNuisance E n t (delta / 12) Rp Rg Ralpha V
    · have hAll : ∀ᵐ w ∂E.P, ∀ kind, w ∈ G → (scoreVariance E kind n t w).toReal ≤ V := by
        filter_upwards [hMoments hm .dr, hMoments hm .ipw] with w hdr hipw kind hwG
        cases kind
        · exact (hipw hwG).2
        · exact (hdr hwG).2
      filter_upwards [hAll] with w hw _
      exact hw
    · exact Eventually.of_forall (fun _ hm' => (hm hm').elim)
  filter_upwards [hAllMeans, hAllVariance] with w hwMean hwVar
  rintro ⟨hwG, hwN, hwH, hwTrunc, hwFinite⟩
  have hc : evalCount E n t w ≠ 0 := hcount w hwN
  have hcpos : 0 < (evalCount E n t w : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hc
  have hmax : max (evalCount E n t w) 1 = evalCount E n t w :=
    max_eq_left (Nat.one_le_iff_ne_zero.mpr hc)
  have hRadius kind : scoreSamplingRadius (obsTailLaw M t) (score E kind n w)
      (evalCount E n t w) (B kind w) (delta / 3) =
        rateSamplingError E kind n t delta (B kind) w := by
    unfold scoreSamplingRadius rateSamplingError truncatedSecondMoment scoreTailMoment
    rw [hmax, hcal]
    congr 2
    field_simp
    <;> ring
  have hGeneral kind : |etaEstimate E kind n t w - etaTarget M| ≤
      rateFirstFactorError E kind c Cgb a0 Rp Rg Ralpha n t delta (B kind) w := by
    calc
      _ ≤ |etaEstimate E kind n t w - ∫ z, score E kind n w z ∂obsTailLaw M t| +
          |(∫ z, score E kind n w z ∂obsTailLaw M t) - etaTarget M| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add (hwTrunc kind) (hwMean kind hwG)
      _ = _ := by rw [hRadius]; rfl
  refine ⟨hwN, hAlpha w hwG, hwH, hGeneral .dr, hGeneral .ipw, ?_⟩
  intro hm ht hz hQ kind
  obtain ⟨hS, hR⟩ := hSimple hm ht hz hQ ((abs_nonneg _).trans hwH) w hwN kind
  refine ⟨?_, hR⟩
  have hVarRadius : Real.sqrt (4 * (scoreVariance E kind n t w).toReal /
      ((delta / 3) * evalCount E n t w)) ≤
        Real.sqrt (12 * V / (delta * evalCount E n t w)) := by
    apply Real.sqrt_le_sqrt
    have heq : 4 * (scoreVariance E kind n t w).toReal /
        ((delta / 3) * evalCount E n t w) =
      12 * (scoreVariance E kind n t w).toReal / (delta * evalCount E n t w) := by
      field_simp
      <;> ring
    rw [heq]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hwVar hm kind hwG) (by norm_num)) (by positivity)
  exact ((abs_sub_le _ _ _).trans
    (add_le_add ((hwFinite hm kind).trans hVarRadius) (hwMean kind hwG))).trans hS

end Papers.TbsExtremeEffects
