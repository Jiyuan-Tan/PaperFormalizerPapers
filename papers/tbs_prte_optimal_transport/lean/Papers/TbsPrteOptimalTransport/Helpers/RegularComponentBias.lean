module
public import Papers.TbsPrteOptimalTransport.Helpers.RegularComponentRemainder
public import Papers.TbsPrteOptimalTransport.Helpers.ProductScoreMoments
/-! Integrated binary regular-score bias, retaining all six fitted corrections. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false
set_option linter.style.longLine false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

-- A bounded, possibly signed product weight preserves the component envelope.
-- @node: weighted_quadratic_envelope_integral_bound
/-- Suppose [G is nonnegative](hyp:hG), [the weight](hyp:hw) and [remainder](hyp:hR)
are almost everywhere strongly measurable, [err is square integrable](hyp:herr), and
[EB](hyp:hEB), [EQ](hyp:hEQ), and [EL](hyp:hEL) are integrable. If [the absolute weight
is at most G almost everywhere](hyp:hbw) and [the absolute remainder is bounded by C
times err squared plus the three envelopes almost everywhere](hyp:hb), [the weighted
remainder is integrable and its absolute integral is at most G times the sum of C times
the integral of err squared and the three envelope integrals](goal). -/
lemma weighted_quadratic_envelope_integral_bound {B : Type*} [MeasurableSpace B]
    (ν : Measure B) (w R err EB EQ EL : B → ℝ) (G C : ℝ)
    (hG : 0 ≤ G) (hw : AEStronglyMeasurable w ν)
    (hR : AEStronglyMeasurable R ν) (herr : MemLp err 2 ν)
    (hEB : Integrable EB ν) (hEQ : Integrable EQ ν) (hEL : Integrable EL ν)
    (hbw : ∀ᵐ x ∂ν, |w x| ≤ G)
    (hb : ∀ᵐ x ∂ν, |R x| ≤ C * err x ^ 2 + EB x + EQ x + EL x) :
    Integrable (fun x => w x * R x) ν ∧
    |∫ x, w x * R x ∂ν| ≤ G *
      (C * (∫ x, err x ^ 2 ∂ν) + (∫ x, EB x ∂ν) +
        (∫ x, EQ x ∂ν) + (∫ x, EL x ∂ν)) := by
  have hs := herr.integrable_sq.const_mul C
  have hd := ((hs.fun_add hEB).fun_add hEQ).fun_add hEL
  have hb' : ∀ᵐ x ∂ν, |w x * R x| ≤
      G * (C * err x ^ 2 + EB x + EQ x + EL x) := by
    filter_upwards [hbw, hb] with x hx hr
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right hx (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hr hG)
  have hi := (hd.const_mul G).mono' (hw.mul hR)
    (by simpa only [Real.norm_eq_abs, Pi.mul_apply] using hb')
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x, |w x * R x| ∂ν := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun x => w x * R x)
    _ ≤ ∫ x, G * (C * err x ^ 2 + EB x + EQ x + EL x) ∂ν :=
      integral_mono_ae hi.abs (hd.const_mul G) hb'
    _ = _ := by
      rw [integral_const_mul, integral_add ((hs.fun_add hEB).fun_add hEQ) hEL,
        integral_add (hs.fun_add hEB) hEQ, integral_add hs hEB, integral_const_mul]

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- Null-set clipping provides a measurable version of the fitted hinge itself.
-- @node: binary_hMinus_measurable_version
/-- For [an admissible policy map](hyp:hphi) and [an admissible binary nuisance](hyp:he),
[the fitted negative hinge at any pair of indices has a measurable version equal to it
almost everywhere under the covariate law](goal). -/
lemma binary_hMinus_measurable_version
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e) (k j : ℕ) :
    ∃ H : X → ℝ, Measurable H ∧ H =ᵐ[xLaw M] hMinus phi L e k j := by
  let pc := fun z x => max 0 (min 1 (e.prop z x))
  let ep : NuisanceBin L := {e with prop := pc}
  have hpc z : Measurable (pc z) := by
    have hm := he.2.1 z
    dsimp only [pc]
    fun_prop
  have hpcR : ∀ z x, pc z x ∈ Icc (0 : ℝ) 1 := fun z x =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hq i := binary_pooledQBin_measurable_of_pointwise_range phi hphi L ep
    hpc hpcR (fun a => (he.2.2.2.1 a).1) (he.2.2.2.2.2.2.2.1) k i
  have hpos i : Measurable (positiveValue ep.pLev i) := by
    unfold positiveValue
    split_ifs
    · exact (he.2.2.2.1 _).1
    · fun_prop
  have hP i : Measurable (positiveValue ep.P1 i) := by
    unfold positiveValue
    split_ifs
    · exact (he.2.2.2.1 _).2.1
    · fun_prop
  refine ⟨hMinus phi L ep k j, ?_, ?_⟩
  · unfold hMinus binFullJ
    exact measurable_const.max ((hq j).sub ((hq (j-1)).max
      ((hpos (k+1)).sub ((hP (k+1)).sub (hP k)))))
  · filter_upwards [ae_all_iff.mpr he.1] with x hx
    have hqeq (i : ℕ) : pooledQBin phi L ep k i x = pooledQBin phi L e k i x := by
      simp only [pooledQBin, ep]
      split_ifs
      · rfl
      · rfl
      · apply Finset.sum_congr rfl
        intro z hz
        simp only [pc, min_eq_right (hx z).2, max_eq_right (hx z).1]
      · simp only [zero_mul, Finset.sum_const_zero]
    simp only [hMinus, hqeq j, hqeq (j-1)]
    rfl

-- All integrability here comes from the bounded admissible construction.
-- @node: binary_weighted_hMinus_integrable_of_admissible
/-- For [an admissible policy](hyp:hphi) and [an admissible binary nuisance](hyp:he),
with [k below the last treatment level](hyp:hk) and [j a positive policy index in that
interval](hyp:hj), if [the covariate weight is measurable](hyp:hw) and [its norm is
bounded by G almost everywhere](hyp:hwB), [the weight times the fitted negative hinge
is integrable under the observation law](goal). -/
lemma binary_weighted_hMinus_integrable_of_admissible
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e)
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (w : X → ℝ) (hw : Measurable w) (G : ℝ)
    (hwB : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ G) :
    Integrable (fun o : Obs X Z => w o.1 * hMinus phi L e k j o.1)
      (observationLaw M) := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  obtain ⟨H, hH, hHe⟩ := binary_hMinus_measurable_version M phi hphi L e he k j
  have heq := observationLaw_covariate_ae M _ hHe
  have hi : Integrable (fun o : Obs X Z => w o.1 * H o.1) (observationLaw M) := by
    apply Integrable.of_bound ((hw.mul hH).comp measurable_fst).aestronglyMeasurable G
    filter_upwards [heq, observationLaw_covariate_ae M _ hwB,
      observationLaw_covariate_ae M _ (binary_auxiliary_ranges M phi L e hphi he k hk j hj.1 hj.2)]
      with o ho hw' hr
    change ‖w o.1 * H o.1‖ ≤ G
    rw [ho, norm_mul]
    have hh : ‖hMinus phi L e k j o.1‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg hr.1.1]
      exact hr.1.2
    exact (mul_le_mul_of_nonneg_left hh (norm_nonneg _)).trans (by simpa using hw')
  exact hi.congr (heq.mono (fun o ho => by dsimp only; rw [ho]))

-- The tower calculation identifies the actual fitted-score bias, rather than
-- the plug-in bias. The three residual errors are still explicit inputs so
-- regression/denominator and pooled-policy bounds can be substituted separately.
-- @node: population_binary_regular_component_bias_envelope
/-- Under [threshold crossing](hyp:h), [an admissible policy](hyp:hphi),
[differentiability with derivative dphi](hyp:hDiff), [a bounded Lipschitz policy derivative](hyp:hDerivative),
[invariant level ordering](hyp:hOrder), [baseline overlap with constant cpi](hyp:hov),
[binary outcomes almost surely](hyp:hy), and [admissibility of the true](hyp:he0) and
[fitted binary nuisances](hyp:he), suppose [c is positive](hyp:hc), [fitted assignment
masses](hyp:hpi) and [policy pooling denominators](hyp:htau) are at least c almost everywhere.
For [k below the last treatment level](hyp:hk) and [a positive policy index j in that
interval](hyp:hj), assume [the weight is measurable](hyp:hw), [G is nonnegative](hyp:hG),
[the weight norm is bounded by G almost everywhere](hyp:hwB), [sep is positive](hyp:hsep),
[err is square integrable under the observation law](hyp:herr), and [EB](hyp:hEB),
[EQ](hyp:hEQ), and [EL](hyp:hEL) are integrable there. If [the true endpoint gap and
both boundary distances are at least sep almost everywhere](hyp:hgap), [the two pooled
endpoint errors and boundary error are bounded by err almost everywhere](hyp:herrors),
and [the regression and two policy residual centering errors are bounded by EB, EQ,
and EL almost everywhere](hyp:hres), [the weighted fitted component score is integrable
and its mean differs from the weighted true hinge mean by at most G times the sum of
26 divided by sep times the integrated squared error and the three envelope integrals](goal). -/
lemma population_binary_regular_component_bias_envelope
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hy : OutcomeBinaryAE M)
    (he0 : BinAdmissible M L (eta0Bin M L)) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (c : ℝ) (hc : 0 < c)
    (hpi : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ e.piLev a x)
    (htau : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev a x)
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (w : X → ℝ) (hw : Measurable w)
    (G : ℝ) (hG : 0 ≤ G) (hwB : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ G)
    (err EB EQ EL : X → ℝ) (sep : ℝ) (hsep : 0 < sep)
    (herr : MemLp (fun o : Obs X Z => err o.1) 2 (observationLaw M))
    (hEB : Integrable (fun o : Obs X Z => EB o.1) (observationLaw M))
    (hEQ : Integrable (fun o : Obs X Z => EQ o.1) (observationLaw M))
    (hEL : Integrable (fun o : Obs X Z => EL o.1) (observationLaw M))
    (hgap : ∀ᵐ x ∂xLaw M,
      sep ≤ pooledQBin phi L (eta0Bin M L) k j x - pooledQBin phi L (eta0Bin M L) k (j-1) x ∧
      sep ≤ |positiveValue (eta0Bin M L).pLev (k+1) x - binFullJ L (eta0Bin M L) k x -
        pooledQBin phi L (eta0Bin M L) k (j-1) x| ∧
      sep ≤ |positiveValue (eta0Bin M L).pLev (k+1) x - binFullJ L (eta0Bin M L) k x -
        pooledQBin phi L (eta0Bin M L) k j x|)
    (herrors : ∀ᵐ x ∂xLaw M,
      |pooledQBin phi L e k j x - pooledQBin phi L (eta0Bin M L) k j x| ≤ err x ∧
      |pooledQBin phi L e k (j-1) x - pooledQBin phi L (eta0Bin M L) k (j-1) x| ≤ err x ∧
      |(positiveValue e.pLev (k+1) x - binFullJ L e k x) -
        (positiveValue (eta0Bin M L).pLev (k+1) x - binFullJ L (eta0Bin M L) k x)| ≤ err x)
    (hres : ∀ᵐ x ∂xLaw M,
      let rP := fun i => positiveValue (eta0Bin M L).piLev i x *
        (positiveValue (eta0Bin M L).P1 i x - positiveValue e.P1 i x) / positiveValue e.piLev i x
      let rp := fun i => positiveValue (eta0Bin M L).piLev i x *
        (positiveValue (eta0Bin M L).pLev i x - positiveValue e.pLev i x) / positiveValue e.piLev i x
      let Q := fun i => ∑ z, instProb M z x * RqBin dphi L e k i (x,z,M.prop z x,0)
      |(rP (k+1) - rP k - rp (k+1)) -
        ((positiveValue e.pLev (k+1) x - binFullJ L e k x) -
          (positiveValue (eta0Bin M L).pLev (k+1) x - binFullJ L (eta0Bin M L) k x))| ≤ EB x ∧
      |Q j + (pooledQBin phi L e k j x - pooledQBin phi L (eta0Bin M L) k j x)| ≤ EQ x ∧
      |(if j = 1 then rp k else 0) + Q (j-1) +
        (pooledQBin phi L e k (j-1) x - pooledQBin phi L (eta0Bin M L) k (j-1) x)| ≤ EL x) :
    Integrable (fun o : Obs X Z => w o.1 * binScoreComponents phi dphi L e k j o)
      (observationLaw M) ∧
    |(∫ o : Obs X Z, w o.1 * binScoreComponents phi dphi L e k j o ∂observationLaw M) -
      (∫ o : Obs X Z, w o.1 * hMinus phi L (eta0Bin M L) k j o.1 ∂observationLaw M)| ≤
      G * ((26 / sep) * (∫ o : Obs X Z, err o.1 ^ 2 ∂observationLaw M) +
        (∫ o : Obs X Z, EB o.1 ∂observationLaw M) +
        (∫ o : Obs X Z, EQ o.1 ∂observationLaw M) +
        (∫ o : Obs X Z, EL o.1 ∂observationLaw M)) := by
  have ht := population_binary_regular_component_correction_fitted_mean M h phi dphi
    hphi hDiff hDerivative L hOrder cpi hov hy he0 e he c hc hpi htau k j hk.le w hw G hwB
  have hplug := binary_weighted_hMinus_integrable_of_admissible M phi hphi L e he
    k j hk hj w hw G hwB
  have htrue := binary_weighted_hMinus_integrable_of_admissible M phi hphi L (eta0Bin M L) he0
    k j hk hj w hw G hwB
  let R := fun o : Obs X Z => w o.1 *
    (hMinus phi L e k j o.1 + binaryRegularRegressionMean phi L (eta0Bin M L) e k j o.1 +
      binaryRegularPolicyMean M phi dphi L e k j o.1 - hMinus phi L (eta0Bin M L) k j o.1)
  have hiR : Integrable R (observationLaw M) := by
    convert! (hplug.fun_add ht.2.1).sub' htrue using 1
    funext o
    dsimp only [R]
    ring
  have hiscore : Integrable (fun o : Obs X Z => w o.1 * binScoreComponents phi dphi L e k j o)
      (observationLaw M) := by
    convert! hplug.fun_add ht.1 using 1
    funext o
    ring
  have hb : ∀ᵐ o ∂observationLaw M, |R o| ≤
      G * ((26 / sep) * err o.1 ^ 2 + EB o.1 + EQ o.1 + EL o.1) := by
    filter_upwards [observationLaw_covariate_ae M _ hgap,
      observationLaw_covariate_ae M _ herrors, observationLaw_covariate_ae M _ hres,
      observationLaw_covariate_ae M _ hwB] with o hg he' hr hw'
    have hb := binary_regular_component_mean_remainder_bound M phi dphi L (eta0Bin M L) e
      k j o.1 (err o.1) sep (EB o.1) (EQ o.1) (EL o.1) hsep hg.1 hg.2.1 hg.2.2
      he'.1 he'.2.1 he'.2.2 hr.1 hr.2.1 hr.2.2
    dsimp only [R]
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hw')
      (abs_nonneg _)).trans (mul_le_mul_of_nonneg_left hb hG)
  have heq : (∫ o : Obs X Z, w o.1 * binScoreComponents phi dphi L e k j o ∂observationLaw M) -
      (∫ o : Obs X Z, w o.1 * hMinus phi L (eta0Bin M L) k j o.1 ∂observationLaw M) =
      ∫ o, R o ∂observationLaw M := by
    have hs : (fun o : Obs X Z => w o.1 * binScoreComponents phi dphi L e k j o) =
        (fun o => w o.1 * hMinus phi L e k j o.1 +
          w o.1 * (binScoreComponents phi dphi L e k j o - hMinus phi L e k j o.1)) := by
      funext o
      ring
    rw [hs, integral_add hplug ht.1, ht.2.2, ← integral_add hplug ht.2.1,
      ← integral_sub (hplug.fun_add ht.2.1) htrue]
    apply integral_congr_ae
    exact Eventually.of_forall (fun o => by dsimp only [R]; ring)
  refine ⟨hiscore, ?_⟩
  rw [heq]
  have hs := herr.integrable_sq.const_mul (26 / sep)
  have hd := ((hs.fun_add hEB).fun_add hEQ).fun_add hEL
  calc
    _ ≤ ∫ o, |R o| ∂observationLaw M := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm R
    _ ≤ ∫ o, G * ((26 / sep) * err o.1 ^ 2 + EB o.1 + EQ o.1 + EL o.1)
        ∂observationLaw M := integral_mono_ae hiR.abs (hd.const_mul G) hb
    _ = _ := by
      rw [integral_const_mul, integral_add ((hs.fun_add hEB).fun_add hEQ) hEL,
        integral_add (hs.fun_add hEB) hEQ, integral_add hs hEB, integral_const_mul]

end Papers.TbsPrteOptimalTransport
