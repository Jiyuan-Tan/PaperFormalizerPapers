module
public import Papers.TbsExtremeEffects.TId
public import Papers.TbsExtremeEffects.Helpers.EtaDR
public import Papers.TbsExtremeEffects.Helpers.EtaIPW
public import Papers.TbsExtremeEffects.Helpers.HillRate
public import Papers.TbsExtremeEffects.Helpers.ProductSimplification
public import Papers.TbsExtremeEffects.Helpers.ProductJointSampling
public import Papers.TbsExtremeEffects.Helpers.JointScoreMeans

/-! Fixed-threshold NETE bounds and the simultaneous simplified alternatives. -/

@[expose] public section
set_option linter.style.longLine false
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
variable {q d m : ℕ}

/-- The [model](hyp:M), [experiment](hyp:E), [tail parameters](hyp:tp), [regularly varying noise](hyp:hRV), [noise independence](hyp:hNoise), [existence of a Pareto-tail model](hyp:hTail), and [confidence tolerance](hyp:eps) determine [the source Hill coefficient](goal) selected from the adaptive Hill guarantee when the tolerance is in its confidence domain, and zero otherwise. -/
noncomputable def sourceHillConstant (M : ExtremeModel q d) (E : NeteExperiment M)
    (tp : TailParams) (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M)
    (hTail : Nonempty (ParetoTailModel M m tp)) (eps : ℝ) : ℝ :=
  open scoped Classical in
  if h : ConfidenceDomain eps then
    Classical.choose (Classical.choose_spec
      (adaptive_hill_rate M E tp hRV hNoise hTail eps h))
  else 0

-- @node: sourceHillConstant_spec
/-- Given [a model](hyp:M), [experiment](hyp:E), [tail parameters](hyp:tp), [regularly varying noise](hyp:hRV), [noise independence](hyp:hNoise), [a Pareto-tail model](hyp:hTail), [a tolerance](hyp:eps), and [proof that the tolerance is in the confidence domain](hyp:hd), [there is a starting sample size for which the source Hill coefficient satisfies its guarantee](goal). -/
lemma sourceHillConstant_spec (M : ExtremeModel q d) (E : NeteExperiment M)
    (tp : TailParams) (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M)
    (hTail : Nonempty (ParetoTailModel M m tp)) (eps : ℝ) (hd : ConfidenceDomain eps) :
    ∃ n0, HillConstantAt E eps n0 (sourceHillConstant M E tp hRV hNoise hTail eps) := by
  have hGuarantee := adaptive_hill_rate M E tp hRV hNoise hTail eps hd
  refine ⟨Classical.choose hGuarantee, ?_⟩
  simpa only [sourceHillConstant, dif_pos hd, HillConstantAt] using
    Classical.choose_spec (Classical.choose_spec hGuarantee)

-- @node: angularW1_nonneg
/-- For [a model](hyp:M) and [threshold](hyp:t), [the angular Wasserstein discrepancy is nonnegative](goal). -/
lemma angularW1_nonneg (M : ExtremeModel q d) (t : ℝ) : 0 ≤ angularW1 M t := by
  apply Real.sSup_nonneg
  rintro a ⟨phi, hphi, rfl⟩
  exact abs_nonneg _

-- @node: secondMomentsOnNuisance_nonneg
/-- Given [an experiment](hyp:E), [sample size](hyp:n), [threshold and tolerance](hyp:t,eps), [nuisance rates](hyp:Rp,Rg,Ralpha), and [a variance cap](hyp:V), if [the tolerance is below one](hyp:heps) and [the second-moment nuisance condition holds](hyp:hMom), then [the variance cap is nonnegative](goal). -/
lemma secondMomentsOnNuisance_nonneg (E : NeteExperiment M) (n : ℕ) (t eps : ℝ)
    (Rp Rg Ralpha : ℕ → ℝ → ℝ) (V : ℝ) (heps : eps < 1)
    (hMom : secondMomentsOnNuisance E n t eps Rp Rg Ralpha V) : 0 ≤ V := by
  obtain ⟨reg, hreg, G, hG, hprob, hInt, hNuisance⟩ := hMom
  have hne : G.Nonempty := by
    by_contra hempty
    have hzero : G = ∅ := Set.not_nonempty_iff_eq_empty.mp hempty
    rw [hzero] at hprob
    simp only [measure_empty, ENNReal.toReal_zero] at hprob
    linarith
  obtain ⟨w, hw⟩ := hne
  have hsq : 0 ≤ scoreSecondMoment E .dr n t w :=
    integral_nonneg (fun _ => sq_nonneg _)
  exact hsq.trans ((hNuisance w hw).2 .dr).2

-- @node: rate_weighted_sum_bound
/-- If [each of the six components is nonnegative](hyp:hS,hN,hE,hA,hZ,hB), [the sampling coefficient is bounded by the common constant](hyp:hcs), [the nuisance coefficient is bounded by it](hyp:hcn), [that constant is at least two](hyp:hce), [at least one](hyp:hca), and [the logarithmic coefficient is bounded by it](hyp:hcz), then [the weighted sum is bounded by that constant times the total components](goal). -/
lemma rate_weighted_sum_bound {S N E A Z B cs cn cz D : ℝ}
    (hS : 0 ≤ S) (hN : 0 ≤ N) (hE : 0 ≤ E) (hA : 0 ≤ A)
    (hZ : 0 ≤ Z) (hB : 0 ≤ B) (hcs : cs ≤ D) (hcn : cn ≤ D)
    (hce : 2 ≤ D) (hca : 1 ≤ D) (hcz : cz ≤ D) :
    cs * S + cn * N + 2 * E + A + cz * Z ≤ D * (S + N + E + A + Z + B) := by
  have hs := mul_le_mul_of_nonneg_right hcs hS
  have hn := mul_le_mul_of_nonneg_right hcn hN
  have he := mul_le_mul_of_nonneg_right hce hE
  have ha := mul_le_mul_of_nonneg_right hca hA
  have hz := mul_le_mul_of_nonneg_right hcz hZ
  have hb : 0 ≤ D * B := mul_nonneg (by linarith) hB
  nlinarith only [hs, hn, he, ha, hz, hb]

/-- Given [an experiment](hyp:E), [overlap constants](hyp:c,Cgb), and [an exponent margin](hyp:a0), if [the overlap constant is positive](hyp:hc), [the homogeneity bound is nonnegative](hyp:hCgb), [the model's Lipschitz constant is nonnegative](hyp:hL), and [the exponent margin is below the tail index](hyp:ha0beta), then [there is a positive simplification coefficient with the stated uniform mean-simplification property](goal). -/
-- @node: product_mean_simplification
lemma product_mean_simplification (E : NeteExperiment M) (c Cgb a0 : ℝ)
    (hc : 0 < c) (hCgb : 0 ≤ Cgb) (hL : 0 ≤ M.L) (ha0beta : a0 < M.beta) :
    ∃ D > 0, ∀ (Cg V delta : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ),
      0 < delta → delta < 1 / 2 → NuisanceErrorBounds E n Rp Rg Ralpha →
      0 ≤ eBar M t → eBar M t ≤ 1 →
      16 * Real.log (12 / delta) ≤ (n : ℝ) * tailProb M t →
      ProductMeanSimplification E c Cgb a0 D Cg V delta Rp Rg Ralpha n t := by
  let K := 4 / (M.beta - a0)
  let H := 2 * (Cgb + 1) / c
  let J := Real.exp 1 - 1 + K * Real.exp 1
  let D := 3 + Real.sqrt 48 + 2 / c + H + H * J
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hJ : 0 ≤ J := by
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    dsimp [J]
    positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hcs : Real.sqrt 48 ≤ D := by
    dsimp [D]
    nlinarith [div_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hc.le, mul_nonneg hH hJ]
  have hcn : 2 / c ≤ D := by
    dsimp [D]
    nlinarith [Real.sqrt_nonneg 48, mul_nonneg hH hJ]
  have hcn' : H ≤ D := by
    dsimp [D]
    nlinarith [Real.sqrt_nonneg 48, div_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hc.le,
      mul_nonneg hH hJ]
  have hce : 2 ≤ D := by
    dsimp [D]
    nlinarith [Real.sqrt_nonneg 48, div_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hc.le,
      mul_nonneg hH hJ]
  have hca : 1 ≤ D := by linarith
  have hcz : H * J ≤ D := by
    dsimp [D]
    nlinarith [Real.sqrt_nonneg 48, div_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hc.le]
  refine ⟨D, hD, ?_⟩
  intro Cg V delta Rp Rg Ralpha n t hd hd1 hErr he0 he1 hbudget hMom ht hz hQ hb w hcount kind
  have hErrors := (nuisanceErrorBounds_components _ _ _ _ _ hErr).1 (delta / 12) (by positivity) (by linarith)
  have hp := hErrors.1.1 (n / 2)
  have hg := hErrors.2.1.1 (trainCount E n t w)
  have ha := hErrors.2.2.1 n
  have hV := secondMomentsOnNuisance_nonneg E n t (delta / 12) Rp Rg Ralpha V
    (by linarith) hMom
  have hmass : 0 < (n : ℝ) * tailProb M t := by
    have hratio : 1 < 12 / delta := (lt_div_iff₀ hd).2 (by linarith)
    exact (mul_pos (by norm_num) (Real.log_pos hratio)).trans_le hbudget
  have hsampling := variance_sampling_radius_of_count hV hd hmass hcount
  have hsampling' : Real.sqrt (12 * V / (delta * evalCount E n t w)) ≤
      Real.sqrt 48 * Real.sqrt (V / (delta * n * tailProb M t)) := by
    simpa only [mul_assoc] using hsampling
  have hlog : 1 ≤ Real.log t := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) ht
  have hz0 : 0 ≤ Ralpha n (delta / 12) * Real.log t := by positivity
  have hangular : 0 ≤ 2 * M.L * angularW1 M t := by
    positivity [angularW1_nonneg M t]
  have hinc := radial_increment_log_bound ht ha hK hz
  have hcoef : 2 * (Cgb + eBar M t) / c ≤ H := by
    apply div_le_div_of_nonneg_right _ hc.le
    linarith
  have hcoef0 : 0 ≤ 2 * (Cgb + eBar M t) / c := by positivity
  have hperturb : (2 * (Cgb + eBar M t) / c) *
      (t ^ Ralpha n (delta / 12) - 1 + K * Ralpha n (delta / 12) * t ^ Ralpha n (delta / 12)) ≤
      H * J * (Ralpha n (delta / 12) * Real.log t) := by
    calc
      _ ≤ (2 * (Cgb + eBar M t) / c) * (J * (Ralpha n (delta / 12) * Real.log t)) :=
        mul_le_mul_of_nonneg_left hinc hcoef0
      _ ≤ H * (J * (Ralpha n (delta / 12) * Real.log t)) :=
        mul_le_mul_of_nonneg_right hcoef (mul_nonneg hJ hz0)
      _ = _ := by ring
  constructor
  · cases kind
    · have hnuisance := mul_le_mul_of_nonneg_right hcoef hp
      have hsum := rate_weighted_sum_bound
        (Real.sqrt_nonneg (V / (delta * n * tailProb M t))) hp he0 hangular hz0 hb
        hcs hcn' hce hca hcz
      unfold etaRemainder simplifiedRate
      dsimp only
      dsimp [K] at hperturb
      nlinarith only [hsampling', hnuisance, hperturb, hsum]
    · have hprod : 0 ≤ Rp (n / 2) (delta / 12) * Rg (trainCount E n t w) (delta / 12) :=
        mul_nonneg hp hg
      have hsum := rate_weighted_sum_bound
        (Real.sqrt_nonneg (V / (delta * n * tailProb M t))) hprod he0 hangular hz0 hb
        hcs hcn hce hca hcz
      unfold etaRemainder simplifiedRate
      dsimp only
      dsimp [K] at hperturb
      nlinarith only [hsampling', hperturb, hsum]
  · have hnuisance : 0 ≤ (match kind with
        | .dr => Rp (n / 2) (delta / 12) * Rg (trainCount E n t w) (delta / 12)
        | .ipw => Rp (n / 2) (delta / 12)) := by
      cases kind
      · exact hp
      · exact mul_nonneg hp hg
    unfold simplifiedRate
    cases kind <;> dsimp only at hnuisance ⊢ <;>
      linarith [Real.sqrt_nonneg (V / (delta * n * tailProb M t))]

-- @node: product_shared_mean_data_of_decompositions
/-- Given [an experiment](hyp:E), [regularly varying noise](hyp:hRV), [bounded covariates](hyp:hX), [asymptotic homogeneity](hyp:hHom), [an even sample size](hyp:hn), [threshold, tolerance, overlap, tail, and variance constants](hyp:t,delta,c,Cgb,a0,V), [estimated overlap](hyp:hOverlap), [the model's G bound](hyp:hG), [a positive threshold](hyp:ht), [bounded tail errors](hyp:hb), [nuisance rates](hyp:Rp,Rg,Ralpha), [nuisance error bounds](hyp:hNuisance), [a positive tolerance below one half](hyp:hd,hd1), [an exponent-rate cap](hyp:ha), [the exponent mean bound](hyp:hExponent), [the target approximation bound](hyp:hTarget), [a regression function and training event](hyp:reg,G), [measurability and probability of that event](hyp:hGmeas,hGprob), [nuisance control on it](hyp:hGNuisance), [score integrability](hyp:hInt), [DR and IPW mean decompositions](hyp:hDR,hIPW), and [conditional score-moment control](hyp:hMom), then [the shared-mean data condition holds](goal). -/
lemma product_shared_mean_data_of_decompositions (E : NeteExperiment M)
    (hRV : NoiseRegularlyVarying M) (hX : CovariateBounded M)
    (hHom : AsymptoticHomogeneity M) {n : ℕ} (hn : EvenSampleSize n)
    {t delta c Cgb a0 V : ℝ} (hOverlap : EstimatedOverlap E c)
    (hG : GBound M Cgb) (ht : 0 < t) (hb : BddAbove (M.e '' Set.Ici t))
    (Rp Rg Ralpha : ℕ → ℝ → ℝ) (hNuisance : NuisanceErrorBounds E n Rp Rg Ralpha)
    (hd : 0 < delta) (hd1 : delta < 1 / 2) (ha : Ralpha n (delta / 12) ≤ a0)
    (hExponent : ∀ w a, 0 ≤ a → a ≤ a0 → |M.alpha - E.alphaHat n w| ≤ a →
      |∫ v, exponentMeanIntegrand E n w v ∂tailLaw M t| ≤
        (2 * (Cgb + eBar M t) / c) *
          (t ^ a - 1 + (4 / (M.beta - a0)) * a * t ^ a))
    (hTarget : |(∫ v, normalizedRegressionContrast M v ∂tailLaw M t) - etaTarget M| ≤
      2 * eBar M t + 2 * M.L * angularW1 M t)
    (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ) (G : Set E.Om)
    (hGmeas : MeasurableSet[trainSigma E n] G) (hGprob : 1 - delta / 12 ≤ E.P.real G)
    (hGNuisance : ∀ w ∈ G, NuisanceAt E n t (delta / 12) Rp Rg Ralpha reg w)
    (hInt : ∀ kind, ∀ᵐ w ∂E.P, w ∈ G → Integrable (score E kind n w) (obsTailLaw M t))
    (hDR : ∀ᵐ w ∂E.P, w ∈ G → DrMeanDecomposition E n t reg w)
    (hIPW : ∀ᵐ w ∂E.P, w ∈ G → IpwMeanDecomposition E n t w)
    (hMom : secondMomentsOnNuisance E n t (delta / 12) Rp Rg Ralpha V →
      ∀ kind, ∀ᵐ w ∂E.P, w ∈ G →
        MemLp (score E kind n w) 2 (obsTailLaw M t) ∧
          (scoreVariance E kind n t w).toReal ≤ V) :
    ProductSharedMeanData E c Cgb a0 V delta Rp Rg Ralpha n t := by
  have hErrors := (nuisanceErrorBounds_components _ _ _ _ _ hNuisance).1 (delta / 12) (by positivity) (by linarith)
  have hDrProvider := dr_mean_bound_provider E hRV hn hOverlap Rp Rg Ralpha
    hErrors.1.2 (hErrors.2.2.1 n) ha hExponent hTarget
  have hIpwProvider := ipw_mean_bound_provider E hRV hX hHom hn hOverlap hG ht hb
    Rp Rg Ralpha hErrors.1.2 (hErrors.2.2.1 n) ha hExponent hTarget
  refine ⟨G, hGmeas, hGprob, fun w hw => (hGNuisance w hw).1, ?_, hMom⟩
  intro kind
  cases kind with
  | dr =>
    filter_upwards [hInt .dr, hDR] with w hi hm hw
    exact ⟨hi hw, hDrProvider reg w (hGNuisance w hw) (hm hw)⟩
  | ipw =>
    filter_upwards [hInt .ipw, hIPW] with w hi hm hw
    exact ⟨hi hw, hIpwProvider reg w (hGNuisance w hw) (hm hw)⟩

/-- Given [a model](hyp:M), [tail parameters](hyp:tp), [consistency](hyp:hConsistency), [exogeneity](hyp:hExogeneity), [regularly varying noise](hyp:hRV), [noise independence](hyp:hNoise), [bounded covariates](hyp:hX), [asymptotic homogeneity](hyp:hHomogeneity), [a Pareto-tail model](hyp:hTail), [an exponent below the tail index](hyp:hAlpha), [a conditional-mean version](hyp:hMean), [identification side conditions](hyp:hSide), [a G-bound constant](hyp:Cgb), [the corresponding G bound](hyp:hGBound), [an exponent margin](hyp:a0), [its positivity](hyp:ha0), and [its being below the tail index](hyp:ha0beta), then [there is a threshold beyond which the stated fixed-threshold NETE product-success guarantee holds](goal). -/
lemma nete_rate_wasserstein (M : ExtremeModel q d)
    (tp : TailParams)
    (hConsistency : Consistency M) (hExogeneity : Exogeneity M)
    (hRV : NoiseRegularlyVarying M) (hNoise : NoiseIndependent M)
    (hX : CovariateBounded M) (hHomogeneity : AsymptoticHomogeneity M)
    (hTail : Nonempty (ParetoTailModel M m tp))
    (hAlpha : AlphaLtBeta M)
    (hMean : ConditionalMeanVersion M)
    (hSide : IdentificationSideConditions M)
    (Cgb : ℝ) (hGBound : GBound M Cgb)
    (a0 : ℝ) (ha0 : 0 < a0) (ha0beta : a0 < M.beta) :
    ∃ t0 : ℝ, 1 ≤ t0 ∧
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
                    (E.P {w | ProductSuccess E c Cgb a0 C (Cg (delta / 6)) V delta Rp Rg Ralpha
                      n t Bdr Bipw w}).toReal ≥ 1 - delta) := by
  have hh : 0 < radialH M := radialH_pos hRV.1 hAlpha
  have hg : 0 ≤ gamma M := (one_div_pos.mpr hRV.1).le
  have hTarget : thetaNETE M = etaTarget M * (1 / radialH M) := by
    have hId := nete_identification M hRV hConsistency hExogeneity hRV hNoise hX
      hHomogeneity hMean hAlpha hSide
    have hValue := hId.2.2.1.limUnder_eq
    change thetaNETE M = _ at hValue
    rw [hValue, radial_target_eq_inv_h hRV.1 hAlpha]
  suffices hRemaining :
    ∃ t0 : ℝ, 1 ≤ t0 ∧
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
                    (E.P {w | ProductFirstFactorRates E c Cgb a0 C (Cg (delta / 6)) V delta Rp Rg Ralpha
                      n t Bdr Bipw w}).toReal ≥ 1 - delta) by
    obtain ⟨t0, ht0, hRates⟩ := hRemaining
    refine ⟨t0, ht0, ?_⟩
    intro E
    dsimp only
    intro c Rp Rg Ralpha hOverlap hNuisance hInt V
    obtain ⟨D, hD, hRatesD⟩ := hRates E c Rp Rg Ralpha hOverlap hNuisance hInt V
    let C := 2 / radialH M * D + |etaTarget M| * (2 / radialH M ^ 2) *
      (gamma M + a0 + |M.alpha|)
    have hC : 0 < C := by
      have hCq : 0 ≤ gamma M + a0 + |M.alpha| := by positivity
      have hmain : 0 < 2 / radialH M * D := mul_pos (by positivity) hD
      have hrest : 0 ≤ |etaTarget M| * (2 / radialH M ^ 2) *
          (gamma M + a0 + |M.alpha|) := by positivity
      exact add_pos_of_pos_of_nonneg hmain hrest
    refine ⟨C, hC, ?_⟩
    intro delta hd hd1
    obtain ⟨n0, hHillConstant, hProb⟩ := hRatesD delta hd hd1
    refine ⟨n0, hHillConstant, ?_⟩
    intro n hn hnEven hIID hTraining t ht ha hbudget Bdr Bipw hBdr hBipw hBdpos hBipos
    have hp := hProb n hn hnEven hIID hTraining t ht ha hbudget Bdr Bipw
      hBdr hBipw hBdpos hBipos
    apply hp.trans
    apply measureReal_mono (h₂ := measure_ne_top E.P _)
    intro w hw
    have hFactors := productRateFactors_of_first_factor_rates E c Cgb a0 D _ V delta
      Rp Rg Ralpha n t Bdr Bipw w hTarget hh hg hD ha hw
    exact productSuccess_of_rate_factors E c Cgb a0 C _ V delta Rp Rg Ralpha
      n t Bdr Bipw w hTarget hh hg hFactors
  suffices hShared :
    ∃ t0 : ℝ, 1 ≤ t0 ∧ ∀ E : NeteExperiment M,
      ∀ (c : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ),
      EstimatedOverlap E c →
      (∀ n, EvenSampleSize n → NuisanceErrorBounds E n Rp Rg Ralpha) →
      (∀ n, EvenSampleSize n → NuisanceIntegrability E n Rp Rg Ralpha) →
      ∀ V : ℝ, GenericRateConstant (fun D =>
        ∀ delta : ℝ, 0 < delta → delta < 1 / 2 →
          ∀ n, EvenSampleSize n → IIDSampling E n → ExponentTraining E n →
            ∀ t, t0 ≤ t → Ralpha n (delta / 12) ≤ a0 →
              (n : ℝ) * tailProb M t ≥ 16 * Real.log (12 / delta) →
              ProductSharedMeanData E c Cgb a0 V delta Rp Rg Ralpha n t ∧
              ProductMeanSimplification E c Cgb a0 D
                (sourceHillConstant M E tp hRV hNoise hTail (delta / 6)) V delta
                  Rp Rg Ralpha n t) by
    obtain ⟨t0, ht0, hData⟩ := hShared
    refine ⟨t0, ht0, ?_⟩
    intro E
    dsimp only
    intro c Rp Rg Ralpha hOverlap hNuisance hInt V
    obtain ⟨D, hD, hDataD⟩ := hData E c Rp Rg Ralpha hOverlap hNuisance hInt V
    refine ⟨D, hD, ?_⟩
    intro delta hd hd1
    obtain ⟨n0, hHill⟩ := sourceHillConstant_spec M E tp hRV hNoise hTail
      (delta / 6) ⟨by positivity, by linarith⟩
    refine ⟨n0, hHill, ?_⟩
    intro n hn hnEven hIID hTraining t ht ha hbudget Bdr Bipw hBdr hBipw hBdpos hBipos
    obtain ⟨hMeanData, hSimple⟩ := hDataD delta hd hd1 n hnEven hIID hTraining t ht ha hbudget
    have hcal : 8 / (delta / 6) = 48 / delta := by field_simp; ring
    have hHillProb : 1 - delta / 6 ≤ E.P.real {w |
        |hillAdaptive E n (delta / 6) w - gamma M| ≤
          hillErrorBound M (sourceHillConstant M E tp hRV hNoise hTail (delta / 6)) delta n} := by
      simpa only [hillErrorBound, hcal, abs_sub_comm, Measure.real] using hHill n hn hIID
    exact product_first_factor_probability_of_shared_means E c Cgb a0 D _ V delta
      Rp Rg Ralpha n hnEven hIID hRV hTraining t hd hd1 hbudget hHillProb
      hMeanData hSimple Bdr Bipw hBdr hBipw hBdpos hBipos
  suffices hSharedMeans :
    ∃ t0 : ℝ, 1 ≤ t0 ∧ ∀ E : NeteExperiment M,
      ∀ (c : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ),
      EstimatedOverlap E c →
      (∀ n, EvenSampleSize n → NuisanceErrorBounds E n Rp Rg Ralpha) →
      (∀ n, EvenSampleSize n → NuisanceIntegrability E n Rp Rg Ralpha) →
      ∀ (V delta : ℝ), 0 < delta → delta < 1 / 2 →
        ∀ n, EvenSampleSize n → IIDSampling E n → ExponentTraining E n →
          ∀ t, t0 ≤ t → Ralpha n (delta / 12) ≤ a0 →
            (n : ℝ) * tailProb M t ≥ 16 * Real.log (12 / delta) →
            ProductSharedMeanData E c Cgb a0 V delta Rp Rg Ralpha n t by
    obtain ⟨T, hT, hMeanData⟩ := hSharedMeans
    have hsmall : ∀ᶠ t in atTop, eBar M t ≤ 1 :=
      ((tendsto_order.mp (eBar_tendsto_zero M hHomogeneity)).2 1 (by norm_num)).mono
        (fun _ h => h.le)
    obtain ⟨Te, hTe⟩ := eventually_atTop.mp hsmall
    obtain ⟨Tb, hTb⟩ := eventually_atTop.mp (eBar_eventually_bddAbove M hHomogeneity)
    let t0 := max T (max Te Tb)
    have hT0 : T ≤ t0 := le_max_left _ _
    have hTe0 : Te ≤ t0 := (le_max_left _ _).trans (le_max_right _ _)
    have hTb0 : Tb ≤ t0 := (le_max_right _ _).trans (le_max_right _ _)
    refine ⟨t0, hT.trans hT0, ?_⟩
    intro E c Rp Rg Ralpha hOverlap hNuisance hInt V
    obtain ⟨D, hD, hSimplify⟩ := product_mean_simplification E c Cgb a0
      hOverlap.1 hGBound.1 hHomogeneity.2.2.2.1 ha0beta
    refine ⟨D, hD, ?_⟩
    intro delta hd hd1 n hn hIID hTraining t ht ha hbudget
    refine ⟨hMeanData E c Rp Rg Ralpha hOverlap hNuisance hInt V delta hd hd1 n hn
      hIID hTraining t (hT0.trans ht) ha hbudget, ?_⟩
    exact hSimplify _ V delta Rp Rg Ralpha n t hd hd1 (hNuisance n hn)
      (eBar_nonneg M hHomogeneity (zero_lt_one.trans_le (hT.trans (hT0.trans ht)))
        (hTb t (hTb0.trans ht))) (hTe t (hTe0.trans ht)) hbudget
  obtain ⟨Tx, hTx, hExponent⟩ :=
    dr_exponent_mean_explicit_bound M hRV hX hHomogeneity hGBound ha0 ha0beta
  obtain ⟨Tb, hTb⟩ := eventually_atTop.mp (eBar_eventually_bddAbove M hHomogeneity)
  suffices hPopulation :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ E : NeteExperiment M,
      ∀ (c : ℝ) (Rp Rg Ralpha : ℕ → ℝ → ℝ),
      EstimatedOverlap E c →
      (∀ n, EvenSampleSize n → NuisanceErrorBounds E n Rp Rg Ralpha) →
      (∀ n, EvenSampleSize n → NuisanceIntegrability E n Rp Rg Ralpha) →
      ∀ (V delta : ℝ), 0 < delta → delta < 1 / 2 →
        ∀ n, EvenSampleSize n → IIDSampling E n → ExponentTraining E n →
          ∀ t, T ≤ t → Ralpha n (delta / 12) ≤ a0 →
            (n : ℝ) * tailProb M t ≥ 16 * Real.log (12 / delta) →
            ∃ (reg : ((Fin q → ℝ) × Bool × (Fin d → ℝ)) → ℝ) (G : Set E.Om),
              MeasurableSet[trainSigma E n] G ∧ 1 - delta / 12 ≤ E.P.real G ∧
              (∀ w ∈ G, NuisanceAt E n t (delta / 12) Rp Rg Ralpha reg w) ∧
              (∀ kind, ∀ᵐ w ∂E.P, w ∈ G →
                Integrable (score E kind n w) (obsTailLaw M t)) ∧
              (∀ᵐ w ∂E.P, w ∈ G → DrMeanDecomposition E n t reg w) ∧
              (∀ᵐ w ∂E.P, w ∈ G → IpwMeanDecomposition E n t w) ∧
              (secondMomentsOnNuisance E n t (delta / 12) Rp Rg Ralpha V →
                ∀ kind, ∀ᵐ w ∂E.P, w ∈ G →
                  MemLp (score E kind n w) 2 (obsTailLaw M t) ∧
                    (scoreVariance E kind n t w).toReal ≤ V) by
    obtain ⟨T, hT, hData⟩ := hPopulation
    let t0 := max T (max Tx Tb)
    have hT0 : T ≤ t0 := le_max_left _ _
    have hTx0 : Tx ≤ t0 := (le_max_left _ _).trans (le_max_right _ _)
    have hTb0 : Tb ≤ t0 := (le_max_right _ _).trans (le_max_right _ _)
    refine ⟨t0, hT.trans hT0, ?_⟩
    intro E c Rp Rg Ralpha hOverlap hNuisance hInt V delta hd hd1 n hn hIID hTraining t ht ha hbudget
    obtain ⟨reg, G, hG, hGprob, hGNuisance, hScoreInt, hDR, hIPW, hMom⟩ :=
      hData E c Rp Rg Ralpha hOverlap hNuisance hInt V delta hd hd1 n hn hIID
        hTraining t (hT0.trans ht) ha hbudget
    have htpos : 0 < t := zero_lt_one.trans_le (hT.trans (hT0.trans ht))
    have hb := hTb t (hTb0.trans ht)
    have hTargetBound := normalized_contrast_target_bound M hRV hX hHomogeneity
      hMean hGBound htpos hb
      (angularFactor_target_wasserstein_bound M hRV hNoise hX hHomogeneity htpos)
    exact product_shared_mean_data_of_decompositions E hRV hX hHomogeneity hn
      hOverlap hGBound htpos hb Rp Rg Ralpha (hNuisance n hn) hd hd1 ha
      (hExponent t (hTx0.trans ht) E c hOverlap n hn) hTargetBound
      reg G hG hGprob hGNuisance hScoreInt hDR hIPW hMom
  obtain ⟨Kr, Tr, hKr, hTr, hPower⟩ :=
    tail_power_increment_uniform_bound M hRV ha0 ha0beta
  refine ⟨max Tr Tb, hTr.trans (le_max_left _ _), ?_⟩
  intro E c Rp Rg Ralpha hOverlap hNuisance hInt V delta hd hd1 n hn
    hIID hTraining t ht ha hbudget
  have hTrt : Tr ≤ t := (le_max_left _ _).trans ht
  have hTbt : Tb ≤ t := (le_max_right _ _).trans ht
  have heps : 0 < delta / 12 := by positivity
  have heps1 : delta / 12 < 1 := by linarith
  have hRad := (hPower t hTrt (Ralpha n (delta / 12))
    (((nuisanceErrorBounds_components _ _ _ _ _ (hNuisance n hn)).1 (delta / 12) heps heps1).2.2.1 n) ha).1
  exact product_population_nuisance_event E hRV hNoise hX hHomogeneity hMean hSide
    hn hOverlap hGBound (hTr.trans hTrt) (hTb t hTbt) Rp Rg Ralpha
    (hNuisance n hn) (hInt n hn) heps heps1 V hRad

end Papers.TbsExtremeEffects
