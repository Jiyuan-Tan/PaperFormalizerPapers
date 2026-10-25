module
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVShiftedGeometry
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVPreliminaryEvent
/-! The half-confidence preliminary density event, with an arbitrary reference measure. -/
public section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory ProbabilityTheory Filter
variable {𝒲 X Z Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace X]
  [MeasurableSpace Z] [MeasurableSpace Ω]
  (V : IVWorld 𝒲 X Z) (P : Measure Ω) [IsProbabilityMeasure P]
  (sample : AnalysisSample V P) (split : SampleSplit)

/-- If [the true density values are positive at every index in the finite
sample](hyp:h₀), [the fitted density values are nonnegative there](hyp:hg), and
[the fitted likelihood product is at least the true likelihood product](hyp:hopt),
[the sum of negative logarithms of the square roots of the fitted-plus-true
density values divided by twice the true density values is nonpositive](goal). -/
-- @node: rdiv_shifted_log_sum_of_likelihood
lemma rdiv_shifted_log_sum_of_likelihood {ι : Type*} (s : Finset ι)
    (g g₀ : ι → ℝ) (h₀ : ∀ i ∈ s, 0 < g₀ i) (hg : ∀ i ∈ s, 0 ≤ g i)
    (hopt : ∏ i ∈ s, g₀ i ≤ ∏ i ∈ s, g i) :
    (∑ i ∈ s, -Real.log (Real.sqrt ((g i + g₀ i) / (2 * g₀ i)))) ≤ 0 := by
  have hp₀ : 0 < ∏ i ∈ s, g₀ i := Finset.prod_pos h₀
  have hp : 0 < ∏ i ∈ s, g i := hp₀.trans_le hopt
  have hgp : ∀ i ∈ s, 0 < g i := by
    intro i hi
    exact lt_of_le_of_ne (hg i hi) (Ne.symm ((Finset.prod_ne_zero_iff.mp hp.ne') i hi))
  have hlogs : (∑ i ∈ s, Real.log (g₀ i)) ≤ ∑ i ∈ s, Real.log (g i) := by
    rw [← Real.log_prod (fun i hi => (h₀ i hi).ne'),
      ← Real.log_prod (fun i hi => (hgp i hi).ne')]
    exact Real.log_le_log hp₀ hopt
  have hpoint : ∀ i ∈ s,
      (Real.log (g i) - Real.log (g₀ i)) / 4 ≤
        Real.log (Real.sqrt ((g i + g₀ i) / (2 * g₀ i))) := by
    intro i hi
    let r := g i / g₀ i
    have hr : 0 < r := div_pos (hgp i hi) (h₀ i hi)
    have hs := Real.sq_sqrt hr.le
    have ham : Real.sqrt r ≤ (r + 1) / 2 := by
      nlinarith only [sq_nonneg (Real.sqrt r - 1), hs]
    have hl := Real.log_le_log (Real.sqrt_pos.2 hr) ham
    rw [Real.log_sqrt hr.le, Real.log_div (hgp i hi).ne' (h₀ i hi).ne'] at hl
    have heq : (g i + g₀ i) / (2 * g₀ i) = (r + 1) / 2 := by
      dsimp [r]
      field_simp [(h₀ i hi).ne']
      <;> ring
    rw [Real.log_sqrt (div_nonneg (add_nonneg (hg i hi) (h₀ i hi).le)
      (mul_nonneg (by norm_num) (h₀ i hi).le)), heq]
    linarith only [hl]
  have hsum := Finset.sum_le_sum hpoint
  rw [← Finset.sum_div, Finset.sum_sub_distrib] at hsum
  rw [Finset.sum_neg_distrib]
  linarith only [hlogs, hsum]

/-- If [A is nonnegative](hyp:hA), [the empirical loss m is nonpositive](hyp:hm),
[the absolute difference between m and population loss L is at most A times
the sum of r times u and r squared](hyp:hdev), [u squared is at most twice
L](hyp:hcurvature), and [H is at most sixteen times u squared](hyp:hH),
[H is at most 64(A squared plus A) plus one, multiplied by r squared](goal). -/
-- @node: rdiv_hellinger_rate_of_shifted_moments
lemma rdiv_hellinger_rate_of_shifted_moments (H L u r A m : ℝ)
    (hA : 0 ≤ A) (hm : m ≤ 0)
    (hdev : |m - L| ≤ A * (r * u + r ^ 2))
    (hcurvature : u ^ 2 ≤ 2 * L) (hH : H ≤ 16 * u ^ 2) :
    H ≤ (64 * (A ^ 2 + A) + 1) * r ^ 2 := by
  have hl := (abs_le.mp hdev).1
  have henergy : u ^ 2 ≤ 2 * A * (r * u + r ^ 2) := by
    linarith only [hl, hm, hcurvature]
  have hu : u ^ 2 ≤ 4 * (A ^ 2 + A) * r ^ 2 := by
    nlinarith only [henergy, sq_nonneg (u - 2 * A * r)]
  nlinarith only [hu, hH, sq_nonneg r]

/-- If [the IV model has the specified joint density and conditional-mean
representation](hyp:hIV) and [the conditional-density class is
realizable](hyp:hDensity), [almost surely the true conditional density is
strictly positive at every sampled input–instrument pair](goal). -/
-- @node: rdiv_true_density_positive_observations
lemma rdiv_true_density_positive_observations
    (μ : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (hIV : RDIVSetting V μ g₀) (hDensity : DensityRealizable V μ G g₀) :
    ∀ᵐ ω ∂P, ∀ i : ℕ, 0 < g₀ (V.xOf (sample.Z i ω)) (V.zOf (sample.Z i ω)) := by
  have hjoint : ∀ᵐ p ∂V.law.map (fun w => (V.xOf w, V.zOf w)), 0 < g₀ p.1 p.2 := by
    rw [hIV.2.1]
    apply (ae_withDensity_iff (hDensity.2 g₀ hDensity.1).1.ennreal_ofReal).2
    exact Filter.Eventually.of_forall fun p hp =>
      lt_of_not_ge (fun h => hp (ENNReal.ofReal_eq_zero.mpr h))
  have hw := ae_of_ae_map (V.measurable_x.prodMk V.measurable_z).aemeasurable hjoint
  apply ae_all_iff.mpr
  intro i
  have hi : P.map (sample.Z i) = V.law := by
    rw [← (sample.identDist i).map_eq, sample.law]
  rw [← hi] at hw
  exact ae_of_ae_map (sample.meas i).aemeasurable hw

/-- If [the IV model has the specified density and conditional-mean
representation](hyp:hIV), [the density class is realizable](hyp:hDensity),
[the selected estimator maximizes likelihood over that class on each preliminary
block](hyp:hMLE), and [n is positive](hyp:hn), [almost surely the fitted density
belongs to the class and its preliminary-block average shifted square-root
negative-log likelihood loss relative to the true density is nonpositive](goal). -/
-- @node: rdiv_mle_shifted_empirical_loss
lemma rdiv_mle_shifted_empirical_loss
    (μ : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (gHat : ℕ → Ω → X → Z → ℝ)
    (hIV : RDIVSetting V μ g₀) (hDensity : DensityRealizable V μ G g₀)
    (hMLE : MLEMaximizerSelected V P sample split G gHat)
    (n : ℕ) (hn : 0 < n) :
    ∀ᵐ ω ∂P, gHat n ω ∈ G ∧
      blockAverage V P sample (split.pre n) (fun w =>
        -Real.log (Real.sqrt ((gHat n ω (V.xOf w) (V.zOf w) +
          g₀ (V.xOf w) (V.zOf w)) / (2 * g₀ (V.xOf w) (V.zOf w))))) ω ≤ 0 := by
  filter_upwards [(hMLE n hn).1,
    rdiv_true_density_positive_observations V P sample μ G g₀ hIV hDensity]
    with ω hω hpos
  refine ⟨hω.1, ?_⟩
  have hb := rdiv_shifted_log_sum_of_likelihood (split.pre n)
    (fun i => gHat n ω (V.xOf (sample.Z i ω)) (V.zOf (sample.Z i ω)))
    (fun i => g₀ (V.xOf (sample.Z i ω)) (V.zOf (sample.Z i ω)))
    (fun i _ => hpos i)
    (fun i _ => (hDensity.2 _ hω.1).2.1 _ _) (hω.2 g₀ hDensity.1)
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hb


/-- Suppose [the IV model has the specified density and conditional-mean
representation](hyp:hIV), [the density class is realizable](hyp:hDensity), [the
class has the common-support density bounds](hyp:hBounds), [the selected density
has a jointly measurable preliminary-data version agreeing almost surely on
sections](hyp:hSelectedDensityVersion), [the selected estimator maximizes
preliminary likelihood](hyp:hMLE), and [n is positive](hyp:hn). Then [the squared
Hellinger distance between the fitted and true conditional densities, integrated
over the instrument distribution, is measurable up to a probability-zero set](goal). -/
-- @node: rdiv_fitted_hellinger_aemeasurable
@[fun_prop] lemma rdiv_fitted_hellinger_aemeasurable
    (μ : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (gHat : ℕ → Ω → X → Z → ℝ) (support : Set (X × Z)) (c₀ CG : ℝ)
    (hIV : RDIVSetting V μ g₀) (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hSelectedDensityVersion : RDIVSelectedDensityVersion V P sample split μ gHat)
    (hMLE : MLEMaximizerSelected V P sample split G gHat) (n : ℕ) (hn : 0 < n) :
    AEMeasurable (fun ω => ∫ z,
      hellingerSqDensity μ (fun x => gHat n ω x z) (fun x => g₀ x z)
        ∂V.law.map V.zOf) P := by
  obtain ⟨s, hs, hsf, hz⟩ := rdiv_true_density_sigmaFinite_restriction V μ G g₀ hIV hDensity
  have : SigmaFinite (μ.restrict s) := hsf
  have : IsProbabilityMeasure (V.law.map V.zOf) :=
    Measure.isProbabilityMeasure_map V.measurable_z.aemeasurable
  obtain ⟨gBar, hgBar, _, hsections, _⟩ := hSelectedDensityVersion n hn
  have hgm : Measurable gBar := hgBar.comp
    ((measurable_fst.mono le_rfl
      (rdiv_preliminarySigma_le V P sample split n)).prodMk measurable_snd)
  have hg₀m := (hDensity.2 g₀ hDensity.1).1
  have hm : Measurable (fun p : (Ω × Z) × X =>
      (Real.sqrt (gBar (p.1.1, (p.2, p.1.2))) - Real.sqrt (g₀ p.2 p.1.2)) ^ 2) := by
    fun_prop
  have hm' : Measurable (fun ω => ∫ z, ∫ x in s,
      (Real.sqrt (gBar (ω, (x, z))) - Real.sqrt (g₀ x z)) ^ 2 ∂μ ∂V.law.map V.zOf) := by
    exact hm.stronglyMeasurable.integral_prod_right'.integral_prod_right.measurable
  have hselected : AEMeasurable (fun ω => ∫ z, ∫ x in s,
      (Real.sqrt (gHat n ω x z) - Real.sqrt (g₀ x z)) ^ 2 ∂μ ∂V.law.map V.zOf) P := by
    apply hm'.aemeasurable.congr
    filter_upwards [hsections] with ω hω
    apply integral_congr_ae
    filter_upwards [hω] with z hz
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hz] with x hx
    rw [hx]
  apply hselected.congr
  filter_upwards [(hMLE n hn).1] with ω hω
  apply integral_congr_ae
  filter_upwards [hz] with z hz
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  filter_upwards [(ae_restrict_iff' hs.compl).1 hz.2] with x hx
  intro hxs
  have hx0 : g₀ x z = 0 := hx hxs
  have hg0 : gHat n ω x z = 0 := by
    have hd := rdiv_density_ratio_of_bounds G g₀ (gHat n ω) support c₀ CG
      hBounds hDensity.1 hω.1 x z
    rw [hx0, mul_zero] at hd
    exact le_antisymm hd ((hDensity.2 _ hω.1).2.1 x z)
  simp [hx0, hg0]

/-- Suppose [the localized likelihood concentration bound is available](hyp:hLi_of_gate),
[the IV model has the specified density and conditional-mean representation](hyp:hIV),
[the density class is realizable](hyp:hDensity), [the common-support density
bounds hold](hyp:hBounds), [the selected estimator maximizes preliminary
likelihood](hyp:hMLE), [the hypothesis and fixed-density image processes are
measurable up to null sets](hyp:hMeas), [the likelihood supremum processes are
measurable](hyp:hLikMeas), [δG bounds the density critical radius](hyp:hRadius),
and [the calibrated radii satisfy the grid and sample-size floor
conditions](hyp:hFloor). Then [there is a positive constant C such that, for
every positive sample size and every ξ strictly between zero and one, the
integrated squared Hellinger error is at most C times δG(n,ξ/2) squared with
probability at least 1−ξ/2](goal). -/
lemma rdiv_mle_hellinger_rate_local
    (hLi_of_gate : LiLocalizedConcentration V)
    (μ : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (gHat : ℕ → Ω → X → Z → ℝ) (support : Set (X × Z)) (c₀ CG : ℝ)
    (hIV : RDIVSetting V μ g₀) (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hMLE : MLEMaximizerSelected V P sample split G gHat)
    (hMeas : RDIVClassesMeasurable V P sample split μ G g₀ gHat)
    (hLikMeas : RDIVLikelihoodProcessesMeasurable V G g₀)
    (δG δH : ℕ → ℝ → ℝ) (ρ : ℝ)
    (hRadius : DensityCriticalRadiusBound V G g₀ δG)
    (hFloor : RDIVRadiusFloor δG δH ρ) :
    ∃ C > 0, ∀ n : ℕ, 0 < n → ∀ ξ ∈ Set.Ioo (0 : ℝ) 1,
      1 - ξ / 2 ≤ P.real {ω | (∫ z,
        hellingerSqDensity μ (fun x => gHat n ω x z) (fun x => g₀ x z)
          ∂V.law.map V.zOf) ≤ C * δG n (ξ / 2) ^ 2} := by
  classical
  obtain ⟨c, hc, hfloor⟩ := hFloor
  obtain ⟨A, hA, hconcentration⟩ := hLi_of_gate μ G g₀ support c₀ CG
    hIV hDensity hBounds (rdiv_likelihood_processes_aemeasurable V G g₀ hLikMeas) δG hRadius
    ⟨c, hc, fun n hn ξ hξ => (hfloor n hn ξ hξ).1⟩
  -- Normalize the shifted ratio locally, compare its Hellinger geometry,
  -- and absorb the transformed norm by Young before transporting the event.
  have hpopulation : ∃ C > 0, ∀ g ∈ G, ∀ r : ℝ, 0 ≤ r → ∀ m : ℝ, m ≤ 0 →
      let f := fun y : X × Z =>
        Real.sqrt ((g y.1 y.2 + g₀ y.1 y.2) / (2 * g₀ y.1 y.2))
      |m - (∫ y, -Real.log (f y) ∂V.law.map (fun w => (V.xOf w, V.zOf w)))| ≤
        A * (r * inputL2Norm (V.law.map (fun w => (V.xOf w, V.zOf w)))
          (f - fun _ => 1) + r ^ 2) →
      (∫ z, hellingerSqDensity μ (fun x => g x z) (fun x => g₀ x z)
        ∂V.law.map V.zOf) ≤ C * r ^ 2 := by
    refine ⟨64 * (A ^ 2 + A) + 1, by positivity, ?_⟩
    intro g hg r hr m hm
    dsimp only
    intro hdev
    let f := fun y : X × Z =>
      Real.sqrt ((g y.1 y.2 + g₀ y.1 y.2) / (2 * g₀ y.1 y.2))
    let L := ∫ y, -Real.log (f y) ∂V.law.map (fun w => (V.xOf w, V.zOf w))
    let u := inputL2Norm (V.law.map (fun w => (V.xOf w, V.zOf w))) (f - fun _ => 1)
    let H := ∫ z, hellingerSqDensity μ (fun x => g x z) (fun x => g₀ x z)
      ∂V.law.map V.zOf
    have hgeometry : u ^ 2 ≤ 2 * L ∧ H ≤ 16 * u ^ 2 := by
      exact rdiv_shifted_density_geometry V μ G g₀ g support c₀ CG
        hIV hDensity hBounds hg
    exact rdiv_hellinger_rate_of_shifted_moments H L u r A m hA.le hm hdev
      hgeometry.1 hgeometry.2
  obtain ⟨C, hC, hpopulation⟩ := hpopulation
  refine ⟨C, hC, ?_⟩
  intro n hn ξ hξ
  obtain ⟨E, hE, hpE, hgood⟩ := hconcentration n hn ξ hξ
  let pre : Ω → Fin n → X × Z := fun ω i =>
    (V.xOf (sample.Z ((Finset.equivFinOfCardEq (split.card_pre n)).symm i) ω),
      V.zOf (sample.Z ((Finset.equivFinOfCardEq (split.card_pre n)).symm i) ω))
  have hpre : Measurable pre := measurable_pi_lambda _ fun i =>
    (V.measurable_x.comp (sample.meas _)).prodMk
      (V.measurable_z.comp (sample.meas _))
  have hpreLaw : P.map pre = Measure.pi (fun _ : Fin n =>
      V.law.map (fun w => (V.xOf w, V.zOf w))) := by
    have hinj : Function.Injective (fun i : Fin n =>
        ((Finset.equivFinOfCardEq (split.card_pre n)).symm i : ℕ)) :=
      Subtype.val_injective.comp (Equiv.injective _)
    have hi := (sample.indep.precomp hinj).comp
      (fun _ w => (V.xOf w, V.zOf w))
      (fun _ => V.measurable_x.prodMk V.measurable_z)
    have he := (iIndepFun_iff_map_fun_eq_pi_map
      (fun i : Fin n => ((V.measurable_x.comp (sample.meas _)).prodMk
        (V.measurable_z.comp (sample.meas _))).aemeasurable)).mp hi
    change P.map pre = _ at he
    rw [he]
    congr 1
    funext i
    change P.map ((fun w => (V.xOf w, V.zOf w)) ∘ sample.Z _) = _
    rw [← Measure.map_map (V.measurable_x.prodMk V.measurable_z)
      (sample.meas _), sample.map_eq]
  have hp : 1 - ξ / 2 ≤ P.real (pre ⁻¹' E) := by
    change 1 - ξ / 2 ≤ (P (pre ⁻¹' E)).toReal
    rw [← Measure.map_apply hpre hE, hpreLaw]
    exact hpE
  have hhalf : ξ / 2 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hξ.1, hξ.2]
  have hr : 0 ≤ δG n (ξ / 2) := (hRadius n hn (ξ / 2) hhalf).1.le
  apply hp.trans
  apply ENNReal.toReal_mono (measure_ne_top P _)
  apply measure_mono_ae
  filter_upwards [rdiv_mle_shifted_empirical_loss V P sample split
    μ G g₀ gHat hIV hDensity hMLE n hn] with ω hω
  intro hωE
  have hd := hgood (pre ω) hωE (gHat n ω) hω.1
  have havg (q : X × Z → ℝ) : (n : ℝ)⁻¹ * ∑ i, q (pre ω i) =
      blockAverage V P sample (split.pre n) (fun w => q (V.xOf w, V.zOf w)) ω := by
    unfold blockAverage
    rw [split.card_pre]
    congr 1
    rw [← Finset.sum_coe_sort (split.pre n)]
    exact Equiv.sum_comp (Finset.equivFinOfCardEq (split.card_pre n)).symm
      (fun i : split.pre n => q (V.xOf (sample.Z i ω), V.zOf (sample.Z i ω)))
  dsimp only at hd
  rw [havg (fun y => -Real.log (Real.sqrt
    ((gHat n ω y.1 y.2 + g₀ y.1 y.2) / (2 * g₀ y.1 y.2))))] at hd
  exact hpopulation (gHat n ω) hω.1 (δG n (ξ / 2)) hr _ hω.2 hd


/-- Suppose [localized likelihood concentration is available](hyp:hLi_of_gate),
[the IV model has the specified density and conditional-mean representation](hyp:hIV),
[the density class is realizable](hyp:hDensity), [the common-support density
bounds hold](hyp:hBounds), [the selected density has a jointly measurable
preliminary-data version agreeing almost surely on sections](hyp:hSelectedDensityVersion),
[the selected estimator maximizes preliminary likelihood](hyp:hMLE), [the
hypothesis and fixed-density image processes are measurable up to null
sets](hyp:hMeas), [the likelihood supremum processes are measurable](hyp:hLikMeas),
[δG bounds the density critical radius](hyp:hRadius), and [the calibrated radii
satisfy the grid and sample-size floor conditions](hyp:hFloor). Then [one
positive constant C works for every ξ strictly between zero and one and every
positive sample size: there is a measurable event of probability at least
1−ξ/2 on which the fitted density belongs to the class and its integrated
squared Hellinger error is at most C times δG(n,ξ/2) squared](goal). -/
-- @node: rdiv_density_event_uniform_confidence
lemma rdiv_density_event_uniform_confidence
    (hLi_of_gate : LiLocalizedConcentration V)
    (μ : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (gHat : ℕ → Ω → X → Z → ℝ) (support : Set (X × Z)) (c₀ CG : ℝ)
    (δG δH : ℕ → ℝ → ℝ) (ρ : ℝ)
    (hIV : RDIVSetting V μ g₀) (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hSelectedDensityVersion : RDIVSelectedDensityVersion V P sample split μ gHat)
    (hMLE : MLEMaximizerSelected V P sample split G gHat)
    (hMeas : RDIVClassesMeasurable V P sample split μ G g₀ gHat)
    (hLikMeas : RDIVLikelihoodProcessesMeasurable V G g₀)
    (hRadius : DensityCriticalRadiusBound V G g₀ δG)
    (hFloor : RDIVRadiusFloor δG δH ρ) :
    ∃ C > 0, ∀ ξ ∈ Set.Ioo (0 : ℝ) 1, ∀ n : ℕ, 0 < n → ∃ E : Set Ω,
      MeasurableSet E ∧ 1 - ξ / 2 ≤ P.real E ∧ ∀ ω ∈ E,
        gHat n ω ∈ G ∧ (∫ z,
          hellingerSqDensity μ (fun x => gHat n ω x z) (fun x => g₀ x z)
            ∂V.law.map V.zOf) ≤ C * δG n (ξ / 2) ^ 2 := by
  obtain ⟨C, hC, hrate⟩ := rdiv_mle_hellinger_rate_local
    (hLi_of_gate := hLi_of_gate) V P sample split
    μ G g₀ gHat support c₀ CG hIV hDensity hBounds hMLE hMeas hLikMeas
    δG δH ρ hRadius hFloor
  refine ⟨C, hC, ?_⟩
  intro ξ hξ n hn
  have hp := hrate n hn ξ hξ
  let H := fun ω => ∫ z,
    hellingerSqDensity μ (fun x => gHat n ω x z) (fun x => g₀ x z) ∂V.law.map V.zOf
  have hHm := rdiv_fitted_hellinger_aemeasurable V P sample split μ G g₀ gHat support
    c₀ CG hIV hDensity hBounds hSelectedDensityVersion hMLE n hn
  let Hm := hHm.mk H
  have he : H =ᵐ[P] Hm := hHm.ae_eq_mk
  have hgood : ∀ᵐ ω ∂P, gHat n ω ∈ G ∧ H ω = Hm ω := by
    filter_upwards [(hMLE n hn).1, he] with ω hg he
    exact ⟨hg.1, he⟩
  obtain ⟨N, hsub, hN, hN0⟩ := exists_measurable_superset_of_null hgood
  let D := {ω | Hm ω ≤ C * δG n (ξ / 2) ^ 2}
  have hD : MeasurableSet D := measurableSet_le hHm.measurable_mk measurable_const
  have hpD : 1 - ξ / 2 ≤ P.real D := by
    have hevent : {ω | H ω ≤ C * δG n (ξ / 2) ^ 2} =ᵐ[P] D := by
      filter_upwards [he] with ω hω
      apply propext
      change (H ω ≤ _) ↔ (Hm ω ≤ _)
      rw [hω]
    change 1 - ξ / 2 ≤ P.real {ω | H ω ≤ C * δG n (ξ / 2) ^ 2} at hp
    rwa [measureReal_def, measure_congr hevent] at hp
  refine ⟨D \ N, hD.diff hN, ?_, ?_⟩
  · simpa only [measureReal_def, measure_sdiff_null hN0] using hpD
  · intro ω hω
    have hg : gHat n ω ∈ G ∧ H ω = Hm ω := by
      by_contra h
      exact hω.2 (hsub h)
    refine ⟨hg.1, ?_⟩
    change H ω ≤ _
    rw [hg.2]
    exact hω.1


/-- Suppose [localized likelihood concentration is available](hyp:hLi_of_gate),
[the IV model has the specified density and conditional-mean representation](hyp:hIV),
[the density class is realizable](hyp:hDensity), [the common-support density
bounds hold](hyp:hBounds), [the selected density has a jointly measurable
preliminary-data version agreeing almost surely on sections](hyp:hSelectedDensityVersion),
[the selected estimator maximizes preliminary likelihood](hyp:hMLE), [the
hypothesis and fixed-density image processes are measurable up to null
sets](hyp:hMeas), [the likelihood supremum processes are measurable](hyp:hLikMeas),
[δG bounds the density critical radius](hyp:hRadius), [the calibrated radii
satisfy the grid and sample-size floor conditions](hyp:hFloor), and [ξ lies
strictly between zero and one](hyp:hξ). Then [there is a positive constant C
such that at every positive sample size a measurable event has probability at
least 1−ξ/2 and, throughout that event, the fitted density belongs to the class
and its integrated squared Hellinger error is at most C times δG(n,ξ/2)
squared](goal). -/
-- @node: rdiv_density_half_confidence_event
lemma rdiv_density_half_confidence_event
    (hLi_of_gate : LiLocalizedConcentration V)
    (μ : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (gHat : ℕ → Ω → X → Z → ℝ) (support : Set (X × Z)) (c₀ CG : ℝ)
    (δG δH : ℕ → ℝ → ℝ) (ρ ξ : ℝ)
    (hIV : RDIVSetting V μ g₀) (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hSelectedDensityVersion : RDIVSelectedDensityVersion V P sample split μ gHat)
    (hMLE : MLEMaximizerSelected V P sample split G gHat)
    (hMeas : RDIVClassesMeasurable V P sample split μ G g₀ gHat)
    (hLikMeas : RDIVLikelihoodProcessesMeasurable V G g₀)
    (hRadius : DensityCriticalRadiusBound V G g₀ δG)
    (hFloor : RDIVRadiusFloor δG δH ρ) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C > 0, ∀ n : ℕ, 0 < n → ∃ E : Set Ω,
      MeasurableSet E ∧ 1 - ξ / 2 ≤ P.real E ∧ ∀ ω ∈ E,
        gHat n ω ∈ G ∧ (∫ z,
          hellingerSqDensity μ (fun x => gHat n ω x z) (fun x => g₀ x z)
            ∂V.law.map V.zOf) ≤ C * δG n (ξ / 2) ^ 2 := by
  obtain ⟨C, hC, hrate⟩ := rdiv_density_event_uniform_confidence
    (hLi_of_gate := hLi_of_gate) V P sample split μ G g₀ gHat support c₀ CG
    δG δH ρ hIV hDensity hBounds hSelectedDensityVersion hMLE hMeas hLikMeas
    hRadius hFloor
  exact ⟨C, hC, hrate ξ hξ⟩


/-- Suppose [localized likelihood concentration is available](hyp:hLi_of_gate),
[the IV model has the specified density and conditional-mean representation](hyp:hIV),
[the density class is realizable](hyp:hDensity), [the common-support density
bounds hold](hyp:hBounds), [the pilot satisfies its preliminary selection and
confidence-rate conditions](hyp:hPilot), [the outcome is bounded in absolute
value by B](hyp:hOutcome), [the hypothesis class is bounded by B on the
support](hyp:hHyp), [the selected density has a jointly measurable preliminary-data
version agreeing almost surely on sections](hyp:hSelectedDensityVersion), [the
selected estimator maximizes preliminary likelihood](hyp:hMLE), [the hypothesis
and fixed-density image processes are measurable up to null sets](hyp:hMeas),
[the likelihood supremum processes are measurable](hyp:hLikMeas), [δG bounds
the density critical radius](hyp:hRadius), [the calibrated radii satisfy the grid
and sample-size floor conditions](hyp:hFloor), and [ξ lies strictly between
zero and one](hyp:hξ). Then [one positive constant C works at every positive
sample size on a measurable event of probability at least 1−ξ/2: the fitted
density belongs to the class, and the density error, pilot L2 membership and
error, global and relative operator comparisons, and population-loss comparison
all satisfy the preliminary bounds calibrated at ξ/4](goal). -/
-- @node: rdiv_preliminary_comparison_event
lemma rdiv_preliminary_comparison_event
    (hLi_of_gate : LiLocalizedConcentration V)
    (μ : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (gHat : ℕ → Ω → X → Z → ℝ) (rHat : ℕ → Ω → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG ρ ξ : ℝ)
    (δG δH δr : ℕ → ℝ → ℝ)
    (hIV : RDIVSetting V μ g₀) (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hPilot : PilotRegressionRate V P sample split rHat δr)
    (hOutcome : OutcomeBounded V B) (hHyp : HypothesisClassBounded V support B)
    (hSelectedDensityVersion : RDIVSelectedDensityVersion V P sample split μ gHat)
    (hMLE : MLEMaximizerSelected V P sample split G gHat)
    (hMeas : RDIVClassesMeasurable V P sample split μ G g₀ gHat)
    (hLikMeas : RDIVLikelihoodProcessesMeasurable V G g₀)
    (hRadius : DensityCriticalRadiusBound V G g₀ δG)
    (hFloor : RDIVRadiusFloor δG δH ρ) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C > 0, ∀ n : ℕ, 0 < n → ∃ E : Set Ω,
      MeasurableSet E ∧ 1 - ξ / 2 ≤ P.real E ∧ ∀ ω ∈ E,
        gHat n ω ∈ G ∧ RDIVPreliminaryOn V μ g₀ gHat rHat ξ δG δr n ω C := by
  have hhalf : ξ / 2 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hξ.1, hξ.2]
  have hquarter : ξ / 4 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hξ.1, hξ.2]
  obtain ⟨Cd, hCd, hdensity⟩ := rdiv_density_half_confidence_event
    (hLi_of_gate := hLi_of_gate) V P sample split
    μ G g₀ gHat support c₀ CG δG δH ρ (ξ / 2) hIV hDensity
    hBounds hSelectedDensityVersion hMLE hMeas hLikMeas hRadius hFloor hhalf
  have heq : ξ / 2 / 2 = ξ / 4 := by ring
  simp only [heq] at hdensity
  let Cg := 2 * B * Real.sqrt Cd
  let Cr := Real.sqrt (2 * (CG / c₀ + 1)) * Real.sqrt Cd
  let Cl := 4 * B * Cr + 2 * Cg
  let C := Cd + Cg + Cr + Cl + 1
  have hB := hOutcome.1
  have hCg : 0 ≤ Cg := by dsimp [Cg]; positivity
  have hCr : 0 ≤ Cr := by dsimp [Cr]; positivity
  have hCl : 0 ≤ Cl := by dsimp [Cl]; positivity
  have hdC : Cd ≤ C := by dsimp [C]; linarith
  have hgC : Cg ≤ C := by dsimp [C]; linarith
  have hrC : Cr ≤ C := by dsimp [C]; linarith
  have hlC : Cl ≤ C := by dsimp [C]; linarith
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro n hn
  obtain ⟨D, hD, hpD, hlocal⟩ := hdensity n hn
  obtain ⟨E, hE, hpE, hpre⟩ := rdiv_preliminary_event_of_density_event V P sample split
    rHat δr hPilot (ξ / 2) hhalf n hn D hD (by simpa only [heq] using hpD)
  simp only [heq] at hpre
  obtain ⟨N, hsub, hN, hN0⟩ := exists_measurable_superset_of_null
    (hPilot.2 n hn (ξ / 4) hquarter).2.1
  refine ⟨E \ N, hE.diff hN, ?_, ?_⟩
  · simpa only [measureReal_def, measure_sdiff_null hN0] using hpE
  intro ω hω
  obtain ⟨hωD, hpilot⟩ := hpre ω hω.1
  obtain ⟨hg, hrate⟩ := hlocal ω hωD
  have hmem : MemLp (rHat n ω) 2 (V.law.map V.zOf) := by
    by_contra h
    exact hω.2 (hsub h)
  have hδ : 0 ≤ δG n (ξ / 4) := (hRadius n hn (ξ / 4) hquarter).1.le
  refine ⟨hg, hrate.trans (mul_le_mul_of_nonneg_right hdC (sq_nonneg _)),
    hmem, hpilot, ?_, ?_, ?_⟩
  · intro h hh
    exact (rdiv_estimated_operator_global_rate V μ G g₀ gHat support B c₀ CG Cd
      (δG n (ξ / 4)) n ω hIV hDensity hBounds hHyp hB hg hCd.le hδ hrate h hh).trans
      (mul_le_mul_of_nonneg_right hgC hδ)
  · intro h hh h' hh'
    exact (rdiv_estimated_operator_relative_rate V μ G g₀ gHat support c₀ CG Cd
      (δG n (ξ / 4)) n ω hIV hDensity hBounds hg hCd.le hδ hrate (h - h')).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hrC hδ) (norm_nonneg _))
  · intro h hh h' hh'
    exact (rdiv_conditional_population_loss_rate V μ G g₀ gHat support B c₀ CG Cd
      (δG n (ξ / 4)) n ω hIV hDensity hBounds hHyp hOutcome hg hCd.le hδ hrate
      h hh h' hh').trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlC hδ) (norm_nonneg _))

/-- If [the density accuracy δG(n,ξ/4) is nonnegative](hyp:hδ), [C is at most
A](hyp:hCA), and [the preliminary density, pilot, operator, and loss comparison
bounds hold with common constant C](hyp:hpre), [those preliminary bounds also
hold with common constant A](goal). -/
-- @node: rdiv_preliminaryOn_mono
lemma rdiv_preliminaryOn_mono
    (μ : Measure X) (g₀ : X → Z → ℝ)
    (gHat : ℕ → Ω → X → Z → ℝ) (rHat : ℕ → Ω → Z → ℝ)
    (ξ C A : ℝ) (δG δr : ℕ → ℝ → ℝ) (n : ℕ) (ω : Ω)
    (hδ : 0 ≤ δG n (ξ / 4)) (hCA : C ≤ A)
    (hpre : RDIVPreliminaryOn V μ g₀ gHat rHat ξ δG δr n ω C) :
    RDIVPreliminaryOn V μ g₀ gHat rHat ξ δG δr n ω A := by
  refine ⟨hpre.1.trans (mul_le_mul_of_nonneg_right hCA (sq_nonneg _)),
    hpre.2.1, hpre.2.2.1, ?_, ?_, ?_⟩
  · intro h hh
    exact (hpre.2.2.2.1 h hh).trans (mul_le_mul_of_nonneg_right hCA hδ)
  · intro h hh h' hh'
    exact (hpre.2.2.2.2.1 h hh h' hh').trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCA hδ) (norm_nonneg _))
  · intro h hh h' hh'
    exact (hpre.2.2.2.2.2 h hh h' hh').trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCA hδ) (norm_nonneg _))

end Papers.TsAdaptiveEstimationInference
