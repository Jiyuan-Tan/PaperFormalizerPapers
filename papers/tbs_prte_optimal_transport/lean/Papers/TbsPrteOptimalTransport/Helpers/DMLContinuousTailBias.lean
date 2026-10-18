module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousTailConvergence
/-! Quadratic conditional bias of the fitted continuous terminal score.
The policy Taylor remainder and the two IPW cross-products are controlled
by the original nuisance L2 errors, without a binary-outcome assumption. -/
public section
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: fitted_continuous_tail_bias_L2_bound
/-- Under [threshold crossing](hyp:h), take [a valid policy](hyp:hphi) [with the specified derivative](hyp:hd),
[a bounded, Lipschitz derivative](hyp:hDerivative), and [a nonnegative Lipschitz constant](hyp:hLip)
[bounding changes in that derivative on the unit interval](hyp:hlip).
Suppose [there is at least one positive level](hyp:hK), [level order is policy invariant](hyp:hOrder),
[fitted nuisances](hyp:he) and [true nuisances](hyp:he0) are admissible,
[baseline overlap holds](hyp:hov), [the fitted clipping threshold is positive](hyp:hc),
and [the terminal assignment probability exceeds it almost everywhere](hyp:hclip).
Then [the absolute terminal-score mean bias is bounded by the absolute lower outcome endpoint times the sum of the Lipschitz constant times squared propensity L2 errors over the terminal policy union, and the terminal level-probability L2 error times the sum of assignment-probability and terminal-weight L2 errors divided by the clipping threshold](goal). -/
lemma fitted_continuous_tail_bias_L2_bound (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (Lip : ℝ) (hLip : 0 ≤ Lip)
    (hlip : ∀ z x a b, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 →
      |dphi z x a - dphi z x b| ≤ Lip * |a - b|)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (e : NuisanceCont L) (he : ContAdmissible M L e)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (cpi c : ℝ) (hov : BaselineOverlapWitness M L cpi) (hc : 0 < c)
    (hclip : ∀ᵐ x ∂xLaw M, c ≤ positiveValue e.piLev L.K x) :
    let err := fun z x => e.prop z x - M.prop z x
    let ep := fun x => positiveValue e.pLev L.K x - L.pLev L.K x
    let et := fun x => positiveValue e.piLev L.K x - (levelSetProb M L).1 L.K x
    let eg := fun x => e.gammaTail x - gammaTail M L x
    |(∫ o, commonTailScore M phi dphi L e.prop e.pLev e.piLev e.gammaTail o
        ∂observationLaw M) -
      (∫ o, commonTailScore M phi dphi L (trueNuisance M L).prop (trueNuisance M L).pLev
        (trueNuisance M L).piLev (trueNuisance M L).gammaTail o ∂observationLaw M)| ≤
      |M.yMin| * (Lip * (∑ z ∈ policyUnion L L.K 1, (eLpNorm (err z) 2 (xLaw M)).toReal ^ 2) +
        (eLpNorm ep 2 (xLaw M)).toReal *
          ((eLpNorm et 2 (xLaw M)).toReal + (eLpNorm eg 2 (xLaw M)).toReal) / c) := by
  have heb := continuousTailCoordinates_admissible M L e he
  have he0b := continuousTailCoordinates_admissible M L (trueNuisance M L) he0
  dsimp only
  let err := fun z x => e.prop z x - M.prop z x
  let ep := fun x => positiveValue e.pLev L.K x - L.pLev L.K x
  let et := fun x => positiveValue e.piLev L.K x - (levelSetProb M L).1 L.K x
  let eg := fun x => e.gammaTail x - gammaTail M L x
  let F := fun (e' : NuisanceCont L) x => ∑ z, instProb M z x * commonTailScore M phi dphi L
    e'.prop e'.pLev e'.piLev e'.gammaTail (x, z, M.prop z x, 0)
  let E := fun x => |M.yMin| * (Lip * (∑ z ∈ policyUnion L L.K 1, (err z x)^2) +
    (|ep x * et x| + |ep x * eg x|) / c)
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  haveI := M.instKernel_markov
  have hi : 1 ≤ L.K ∧ L.K ≤ L.K := ⟨hK, le_rfl⟩
  have hunit (f : X → ℝ) (hf : Measurable f)
      (hb : ∀ᵐ x ∂xLaw M, f x ∈ Icc (0 : ℝ) 1) : MemLp f 2 (xLaw M) := by
    apply MemLp.of_bound hf.aestronglyMeasurable 1
    filter_upwards [hb] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
    exact hx.2
  have hp : ∀ z, MemLp (err z) 2 (xLaw M) := by
    intro z
    exact (hunit _ (heb.2.1 z) (heb.1 z)).sub
      (hunit _ (h.2.1.comp (measurable_const.prodMk measurable_id))
        (Filter.Eventually.of_forall (M.rangeProp z)))
  have hep : MemLp ep 2 (xLaw M) := by
    simpa only [ep, positiveValue, dif_pos hi, continuousTailCoordinates, trueNuisance, Pi.sub_def] using
      (hunit _ (heb.2.2.2.1 ⟨L.K,hi⟩).1
        ((heb.2.2.1 ⟨L.K,hi⟩).mono (fun _ hx => hx.1))).sub
      (hunit _ (he0b.2.2.2.1 ⟨L.K,hi⟩).1
        ((he0b.2.2.1 ⟨L.K,hi⟩).mono (fun _ hx => hx.1)))
  have het : MemLp et 2 (xLaw M) := by
    simpa only [et, positiveValue, dif_pos hi, continuousTailCoordinates, trueNuisance, Pi.sub_def] using
      (hunit _ (heb.2.2.2.1 ⟨L.K,hi⟩).2.2
        ((heb.2.2.1 ⟨L.K,hi⟩).mono (fun _ hx => hx.2.2))).sub
      (hunit _ (he0b.2.2.2.1 ⟨L.K,hi⟩).2.2
        ((he0b.2.2.1 ⟨L.K,hi⟩).mono (fun _ hx => hx.2.2)))
  have heg : MemLp eg 2 (xLaw M) :=
    (hunit _ heb.2.2.2.2.2.2.2.2.2.2.2.2 heb.2.2.2.2.2.2.2.2.2.2.2.1).sub
      (hunit _ he0b.2.2.2.2.2.2.2.2.2.2.2.2 he0b.2.2.2.2.2.2.2.2.2.2.2.1)
  have isq (z : Z) : Integrable (fun x => (err z x)^2) (xLaw M) := (hp z).integrable_sq
  have ipt : Integrable (fun x => |ep x * et x|) (xLaw M) := (hep.integrable_mul het).abs
  have ipg : Integrable (fun x => |ep x * eg x|) (xLaw M) := (hep.integrable_mul heg).abs
  have iE : Integrable E (xLaw M) :=
    (((integrable_finsetSum _ (fun z _ => isq z)).const_mul Lip).fun_add
      ((ipt.fun_add ipg).div_const c)).const_mul |M.yMin|
  have hclip0 : ∀ᵐ x ∂xLaw M, cpi ≤ positiveValue (trueNuisance M L).piLev L.K x := by
    exact Filter.Eventually.of_forall (fun x => by
      simpa only [positiveValue, dif_pos hi, trueNuisance] using hov.2 x L.K hK le_rfl)
  have ifit := fitted_tail_finite_mean_integrable M h phi dphi hphi hd hDerivative
    L hK (continuousTailCoordinates L e) heb c hc hclip
  have i0 := fitted_tail_finite_mean_integrable M h phi dphi hphi hd hDerivative
    L hK (continuousTailCoordinates L (trueNuisance M L)) he0b cpi hov.1 hclip0
  have h0 (x : X) : F (trueNuisance M L) x = M.yMin *
      ((∑ z ∈ policyUnion L L.K 1, instProb M z x * phi z x (M.prop z x)) -
        L.pLev L.K x * gammaTail M L x) := by
    simpa only [F, continuousTailCoordinates, trueNuisance, sub_self, mul_zero, zero_mul, add_zero, positiveValue, dif_pos hi]
      using fitted_tail_finite_mean M phi dphi L hK hOrder
        (continuousTailCoordinates L (trueNuisance M L)) x
  have hbound : ∀ᵐ x ∂xLaw M, |F e x - F (trueNuisance M L) x| ≤ E x := by
    filter_upwards [hclip, ae_all_iff.mpr heb.1, he0b.2.2.1 ⟨L.K,hi⟩,
      he0b.2.2.2.2.2.2.2.2.2.2.2.1] with x hcx hpx h0x hgx
    rw [h0]
    have hb := fitted_tail_conditional_bias_bound M phi dphi hd Lip hLip hlip
      L hK hOrder (continuousTailCoordinates L e) x c hc hcx (fun z _ => hpx z)
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply add_le_add
    · rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro z hz
      have hm : instProb M z x ≤ 1 := measureReal_le_one
      simpa only [one_mul, err, continuousTailCoordinates] using
        mul_le_mul_of_nonneg_right hm (mul_nonneg hLip (sq_nonneg (err z x)))
    · apply div_le_div_of_nonneg_right _ hc.le
      have hgb : |gammaTail M L x| ≤ 1 := by
        change gammaTail M L x ∈ Icc (0 : ℝ) 1 at hgx
        rw [abs_of_nonneg hgx.1]
        exact hgx.2
      have ht0 : (levelSetProb M L).1 L.K x ∈ Icc (0 : ℝ) 1 := h0x.2.2
      have htb : |(levelSetProb M L).1 L.K x| ≤ 1 := by
        rw [abs_of_nonneg ht0.1]
        exact ht0.2
      change |ep x| * (|gammaTail M L x| * |et x| +
        |eg x| * |(levelSetProb M L).1 L.K x|) ≤ |ep x * et x| + |ep x * eg x|
      calc
        _ ≤ |ep x| * (|et x| + |eg x|) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact add_le_add (by simpa using mul_le_mul_of_nonneg_right hgb (abs_nonneg (et x)))
            (by simpa using mul_le_mul_of_nonneg_left htb (abs_nonneg (eg x)))
        _ = _ := by rw [abs_mul, abs_mul]; ring
  have hfit := population_commonTailScore_finite_mean_of_binary_admissible M h
    phi dphi hphi hd hDerivative L hK (continuousTailCoordinates L e) heb c hc hclip
  have htrue := population_commonTailScore_finite_mean_of_binary_admissible M h
    phi dphi hphi hd hDerivative L hK
    (continuousTailCoordinates L (trueNuisance M L)) he0b cpi hov.1 hclip0
  simp only [continuousTailCoordinates] at hfit htrue
  rw [hfit, htrue]
  change |(∫ x, F e x ∂xLaw M) - (∫ x, F (trueNuisance M L) x ∂xLaw M)| ≤ _
  simp only [continuousTailCoordinates] at ifit i0
  rw [← integral_sub ifit i0]
  have hsq (z : Z) : (∫ x, (err z x)^2 ∂xLaw M) ≤
      (eLpNorm (err z) 2 (xLaw M)).toReal ^ 2 := by
    simpa only [← sq, abs_sq] using
      Causalean.Stat.integral_abs_mul_le_eLpNorm_mul_eLpNorm (hp z) (hp z)
  calc
    _ ≤ ∫ x, |F e x - F (trueNuisance M L) x| ∂xLaw M := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x => F e x - F (trueNuisance M L) x)
    _ ≤ ∫ x, E x ∂xLaw M := integral_mono_ae (ifit.sub' i0).abs iE hbound
    _ = |M.yMin| * (Lip * (∑ z ∈ policyUnion L L.K 1, ∫ x, (err z x)^2 ∂xLaw M) +
        ((∫ x, |ep x * et x| ∂xLaw M) + (∫ x, |ep x * eg x| ∂xLaw M)) / c) := by
      dsimp only [E]
      rw [integral_const_mul, integral_add
        ((integrable_finsetSum _ (fun z _ => isq z)).const_mul Lip)
        ((ipt.fun_add ipg).div_const c), integral_const_mul,
        integral_finsetSum _ (fun z _ => isq z), integral_div, integral_add ipt ipg]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun z _ => hsq z)) hLip
      · apply div_le_div_of_nonneg_right _ hc.le
        rw [mul_add]
        exact add_le_add (Causalean.Stat.integral_abs_mul_le_eLpNorm_mul_eLpNorm hep het)
          (Causalean.Stat.integral_abs_mul_le_eLpNorm_mul_eLpNorm hep heg)

-- Uniform component errors assemble the Taylor and denominator cross-errors
-- of the actual score, retaining its fitted residual correction.
-- @node: fitted_continuous_tail_quadratic_bias_bound
/-- Under [threshold crossing](hyp:h), assume [a valid policy](hyp:hphi) [with the specified derivative](hyp:hd),
[a bounded, Lipschitz derivative](hyp:hDerivative), [a nonnegative Lipschitz constant](hyp:hLip)
[controlling derivative differences on the unit interval](hyp:hlip), [a positive number of levels](hyp:hK),
and [policy-invariant level order](hyp:hOrder).
Suppose [fitted nuisances](hyp:he) and [true nuisances](hyp:he0) are admissible,
[baseline overlap holds](hyp:hov), [the clipping threshold is positive](hyp:hc),
[the regression error bound is nonnegative](hyp:hreg), [the weight error bound is nonnegative](hyp:_hwt),
and [the fitted terminal assignment probability exceeds the clipping threshold almost everywhere](hyp:hclip).
If [propensity L2 errors in the terminal policy union](hyp:hp) and [the terminal level-probability L2 error](hyp:hlev)
are bounded by the regression error bound, while [the terminal assignment-probability L2 error](hyp:hpi)
and [terminal-weight L2 error](hyp:hg) are bounded by the weight error bound, then
[the absolute terminal-score mean bias is at most the absolute lower outcome endpoint times the Lipschitz constant times the terminal union's size times the squared regression bound, plus twice the regression-weight product divided by the clipping threshold](goal). -/
lemma fitted_continuous_tail_quadratic_bias_bound (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (Lip : ℝ) (hLip : 0 ≤ Lip)
    (hlip : ∀ z x a b, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 →
      |dphi z x a - dphi z x b| ≤ Lip * |a - b|)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (e : NuisanceCont L) (he : ContAdmissible M L e)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (cpi c reg wt : ℝ) (hov : BaselineOverlapWitness M L cpi) (hc : 0 < c)
    (hreg : 0 ≤ reg) (_hwt : 0 ≤ wt)
    (hclip : ∀ᵐ x ∂xLaw M, c ≤ positiveValue e.piLev L.K x)
    (hp : ∀ z ∈ policyUnion L L.K 1,
      (eLpNorm (fun x => e.prop z x - M.prop z x) 2 (xLaw M)).toReal ≤ reg)
    (hlev : (eLpNorm (fun x => positiveValue e.pLev L.K x - L.pLev L.K x)
      2 (xLaw M)).toReal ≤ reg)
    (hpi : (eLpNorm (fun x => positiveValue e.piLev L.K x -
      (levelSetProb M L).1 L.K x) 2 (xLaw M)).toReal ≤ wt)
    (hg : (eLpNorm (fun x => e.gammaTail x - gammaTail M L x)
      2 (xLaw M)).toReal ≤ wt) :
    |(∫ o, commonTailScore M phi dphi L e.prop e.pLev e.piLev e.gammaTail o
        ∂observationLaw M) -
      (∫ o, commonTailScore M phi dphi L (trueNuisance M L).prop (trueNuisance M L).pLev
        (trueNuisance M L).piLev (trueNuisance M L).gammaTail o ∂observationLaw M)| ≤
      |M.yMin| * (Lip * ((policyUnion L L.K 1).card : ℝ) * reg ^ 2 +
        (2 / c) * (reg * wt)) := by
  have hb := fitted_continuous_tail_bias_L2_bound M h phi dphi hphi hd hDerivative Lip hLip hlip
    L hK hOrder e he he0 cpi c hov hc hclip
  dsimp only at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply add_le_add
  · calc
      _ ≤ Lip * (∑ _z ∈ policyUnion L L.K 1, reg ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hLip
        apply Finset.sum_le_sum
        intro z hz
        exact pow_le_pow_left₀ ENNReal.toReal_nonneg (hp z hz) 2
      _ = _ := by simp; ring
  · calc
      _ ≤ reg * (wt + wt) / c := by
        gcongr
      _ = _ := by ring

-- Both regression and weight errors have the paper's quarter-power rate.
-- The score-mean rate is derived from the expansion above.
-- @node: fitted_continuous_tail_root_n_bias_negligible
/-- Under [threshold crossing](hyp:h), assume [a valid policy](hyp:hphi) [with the specified derivative](hyp:hd),
[a bounded, Lipschitz derivative](hyp:hDerivative), [a nonnegative Lipschitz constant](hyp:hLip)
[controlling derivative differences on the unit interval](hyp:hlip), [at least one positive level](hyp:hK),
and [policy-invariant level order](hyp:hOrder).
Suppose [all fitted nuisances](hyp:he) and [the true nuisances](hyp:he0) are admissible,
[baseline overlap holds](hyp:hov), [the clipping threshold is positive](hyp:hc),
[regression error envelopes](hyp:hreg) and [weight error envelopes](hyp:hwt) are nonnegative,
and [fitted terminal assignment probabilities exceed the threshold almost everywhere](hyp:hclip).
If [terminal-union propensity L2 errors](hyp:hp) and [terminal level-probability L2 errors](hyp:hlev)
are bounded by the regression envelope, [terminal assignment-probability L2 errors](hyp:hpi)
and [terminal-weight L2 errors](hyp:hg) are bounded by the weight envelope, and
[the regression envelope](hyp:hr) and [the weight envelope](hyp:hw) are little-o in probability of the inverse fourth root of twice the evaluation-half size, then
[the terminal-score mean bias multiplied by the square root of the evaluation-half size converges in probability to zero](goal). -/
lemma fitted_continuous_tail_root_n_bias_negligible {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (Lip : ℝ) (hLip : 0 ≤ Lip)
    (hlip : ∀ z x a b, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 →
      |dphi z x a - dphi z x b| ≤ Lip * |a - b|)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (eh : ℕ → A → NuisanceCont L) (he : ∀ n a, ContAdmissible M L (eh n a))
    (he0 : ContAdmissible M L (trueNuisance M L))
    (cpi c : ℝ) (reg wt : ℕ → A → ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hc : 0 < c)
    (hreg : ∀ n a, 0 ≤ reg n a) (hwt : ∀ n a, 0 ≤ wt n a)
    (hclip : ∀ n a, ∀ᵐ x ∂xLaw M, c ≤ positiveValue (eh n a).piLev L.K x)
    (hp : ∀ n a z, z ∈ policyUnion L L.K 1 →
      (eLpNorm (fun x => (eh n a).prop z x - M.prop z x) 2 (xLaw M)).toReal ≤ reg n a)
    (hlev : ∀ n a, (eLpNorm (fun x => positiveValue (eh n a).pLev L.K x - L.pLev L.K x)
      2 (xLaw M)).toReal ≤ reg n a)
    (hpi : ∀ n a, (eLpNorm (fun x => positiveValue (eh n a).piLev L.K x -
      (levelSetProb M L).1 L.K x) 2 (xLaw M)).toReal ≤ wt n a)
    (hg : ∀ n a, (eLpNorm (fun x => (eh n a).gammaTail x - gammaTail M L x)
      2 (xLaw M)).toReal ≤ wt n a)
    (hr : Causalean.Stat.IsLittleOp reg
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ)
    (hw : Causalean.Stat.IsLittleOp wt
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        ((∫ o, commonTailScore M phi dphi L (eh n a).prop (eh n a).pLev
            (eh n a).piLev (eh n a).gammaTail o ∂observationLaw M) -
          (∫ o, commonTailScore M phi dphi L (trueNuisance M L).prop (trueNuisance M L).pLev
            (trueNuisance M L).piLev (trueNuisance M L).gammaTail o ∂observationLaw M)))
      atTop (fun _ _ => 0) := by
  let C := |M.yMin| * (Lip * ((policyUnion L L.K 1).card : ℝ) + 2 / c) + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  apply dml_quadratic_bias_root_n_negligible μ _ reg wt C hC hr hw
  intro n a
  have hb := fitted_continuous_tail_quadratic_bias_bound M h phi dphi hphi hd hDerivative Lip hLip hlip
    L hK hOrder (eh n a) (he n a) he0 cpi c (reg n a) (wt n a) hov hc
    (hreg n a) (hwt n a) (hclip n a) (hp n a) (hlev n a) (hpi n a) (hg n a)
  apply hb.trans
  have hn : 0 ≤ reg n a * wt n a := mul_nonneg (hreg n a) (hwt n a)
  calc
    _ ≤ |M.yMin| * ((Lip * ((policyUnion L L.K 1).card : ℝ) + 2 / c) *
        (reg n a ^ 2 + reg n a * wt n a)) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      nlinarith [mul_nonneg (by positivity : 0 ≤ 2 / c) (sq_nonneg (reg n a)),
        mul_nonneg (by positivity : 0 ≤ Lip * ((policyUnion L L.K 1).card : ℝ)) hn]
    _ = (C - 1) * (reg n a ^ 2 + reg n a * wt n a) := by dsimp only [C]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (add_nonneg (sq_nonneg _) hn)

-- Clipped propensity and terminal-weight coordinates have finite second moments.
-- @node: fitted_continuous_prop_gammaTail_memLp
/-- If [the continuous nuisance functions are admissible](hyp:he), then
[each fitted instrument-specific propensity and the fitted terminal weight have finite second moments under the covariate law](goal). -/
lemma fitted_continuous_prop_gammaTail_memLp (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) :
    (∀ z, MemLp (e.prop z) 2 (xLaw M)) ∧ MemLp e.gammaTail 2 (xLaw M) := by
  exact fitted_prop_gammaTail_memLp M L (continuousTailCoordinates L e)
    (continuousTailCoordinates_admissible M L e he)

-- Construct the finite envelopes directly from the componentwise rates.
-- No rate for the score bias is supplied as an assumption.
-- @node: nuisanceRates_continuous_tail_root_n_bias_negligible
/-- Under [threshold crossing](hyp:h), assume [a valid policy](hyp:hphi) [with the specified derivative](hyp:hd),
[a bounded, Lipschitz derivative](hyp:hDerivative), [a nonnegative Lipschitz constant](hyp:hLip)
[controlling derivative differences on the unit interval](hyp:hlip), [at least one positive level](hyp:hK),
and [policy-invariant level order](hyp:hOrder).
Suppose [all fitted nuisances](hyp:he) and [the true nuisances](hyp:he0) are admissible,
[baseline overlap holds](hyp:hov), [the clipping threshold is positive](hyp:hc),
and [fitted terminal assignment probabilities exceed it almost everywhere](hyp:hclip).
If [propensities](hyp:hrp), [level probabilities](hyp:hrlev), [level assignment probabilities](hyp:hrpi),
and [terminal weights](hyp:hrg) satisfy the finite-coordinate nuisance rate conditions, then
[the fitted-minus-true terminal-score population mean, multiplied by the square root of the evaluation-half size, converges in probability to zero along even sample sizes](goal). -/
lemma nuisanceRates_continuous_tail_root_n_bias_negligible {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (Lip : ℝ) (hLip : 0 ≤ Lip)
    (hlip : ∀ z x a b, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 →
      |dphi z x a - dphi z x b| ≤ Lip * |a - b|)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (eh : ℕ → A → NuisanceCont L) (he : ∀ n a, ContAdmissible M L (eh n a))
    (he0 : ContAdmissible M L (trueNuisance M L))
    (cpi c : ℝ) (hov : BaselineOverlapWitness M L cpi) (hc : 0 < c)
    (hclip : ∀ n a, ∀ᵐ x ∂xLaw M, c ≤ positiveValue (eh n a).piLev L.K x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) (trueNuisance M L).prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) (trueNuisance M L).pLev)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) (trueNuisance M L).piLev)
    (hrg : FiniteNuisanceRates M μ (fun n a (_ : Unit) => (eh n a).gammaTail)
      (fun _ => (trueNuisance M L).gammaTail)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        ((∫ o, commonTailScore M phi dphi L (eh (2*(n+1)) a).prop
            (eh (2*(n+1)) a).pLev (eh (2*(n+1)) a).piLev
            (eh (2*(n+1)) a).gammaTail o ∂observationLaw M) -
          (∫ o, commonTailScore M phi dphi L (trueNuisance M L).prop (trueNuisance M L).pLev
            (trueNuisance M L).piLev (trueNuisance M L).gammaTail o ∂observationLaw M)))
      atTop (fun _ _ => 0) := by
  let zs := (Finset.univ : Finset Z).toList
  let dp := fun n a z => finiteL2Error M ((eh (2*(n+1)) a).prop z) ((trueNuisance M L).prop z)
  let dl := fun n a => finiteL2Error M (positiveValue (eh (2*(n+1)) a).pLev L.K)
    (positiveValue (trueNuisance M L).pLev L.K)
  let dt := fun n a => finiteL2Error M (positiveValue (eh (2*(n+1)) a).piLev L.K)
    (positiveValue (trueNuisance M L).piLev L.K)
  let dg := fun n a => finiteL2Error M (eh (2*(n+1)) a).gammaTail (trueNuisance M L).gammaTail
  let reg := fun n a => maxErrors (zs.map (dp n a)) + dl n a
  let wt := fun n a => dt n a + dg n a
  have hl := nuisanceRates_positiveValue M μ L.K _ _ hrlev L.K
  have ht := nuisanceRates_positiveValue M μ L.K _ _ hrpi L.K
  have hp := nuisanceRates_finite_maxErrors M μ _ _ zs hrp
  have hr := hp.add_eventually_nonneg_rate
    (Eventually.of_forall (fun _ => Real.rpow_nonneg (by positivity) _)) hl
  have hw := ht.add_eventually_nonneg_rate
    (Eventually.of_forall (fun _ => Real.rpow_nonneg (by positivity) _)) (hrg ())
  have hi : 1 ≤ L.K ∧ L.K ≤ L.K := ⟨hK, le_rfl⟩
  have hreg : ∀ n a, 0 ≤ reg n a := fun _ _ =>
    add_nonneg (maxErrors_nonneg _) (Real.sqrt_nonneg _)
  have hwt : ∀ n a, 0 ≤ wt n a := fun _ _ =>
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  apply fitted_continuous_tail_root_n_bias_negligible M μ h phi dphi hphi hd hDerivative
    Lip hLip hlip L hK hOrder (fun n a => eh (2*(n+1)) a)
    (fun n a => he _ a) he0 cpi c reg wt hov hc hreg hwt (fun n a => hclip _ a)
  · intro n a z _hz
    change (eLpNorm (fun x => (eh (2*(n+1)) a).prop z x -
      (trueNuisance M L).prop z x) 2 (xLaw M)).toReal ≤ reg n a
    rw [← l2Error_eq_eLpNorm M _ _
      (((fitted_continuous_prop_gammaTail_memLp M L (eh (2*(n+1)) a) (he _ a)).1 z).sub
        ((fitted_continuous_prop_gammaTail_memLp M L (trueNuisance M L) he0).1 z))]
    have hb : dp n a z ≤ maxErrors (zs.map (dp n a)) := by
      apply le_maxErrors_of_mem
      exact List.mem_map.mpr ⟨z, by simp [zs], rfl⟩
    exact hb.trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  · intro n a
    have hm := ((fitted_continuous_treatment_assignment_memLp M L
      (eh (2*(n+1)) a) (he _ a) L.K).1).sub
        (fitted_continuous_treatment_assignment_memLp M L (trueNuisance M L) he0 L.K).1
    have hb : dl n a ≤ reg n a := le_add_of_nonneg_left (maxErrors_nonneg _)
    dsimp only [dl] at hb
    rw [l2Error_eq_eLpNorm M _ _ hm] at hb
    simpa only [trueNuisance, positiveValue, dif_pos hi] using hb
  · intro n a
    have hm := ((fitted_continuous_treatment_assignment_memLp M L
      (eh (2*(n+1)) a) (he _ a) L.K).2).sub
        (fitted_continuous_treatment_assignment_memLp M L (trueNuisance M L) he0 L.K).2
    have hb : dt n a ≤ wt n a := le_add_of_nonneg_right (Real.sqrt_nonneg _)
    dsimp only [dt] at hb
    rw [l2Error_eq_eLpNorm M _ _ hm] at hb
    simpa only [trueNuisance, positiveValue, dif_pos hi] using hb
  · intro n a
    have hm := (fitted_continuous_prop_gammaTail_memLp M L (eh (2*(n+1)) a) (he _ a)).2.sub
      (fitted_continuous_prop_gammaTail_memLp M L (trueNuisance M L) he0).2
    have hb : dg n a ≤ wt n a := le_add_of_nonneg_left (Real.sqrt_nonneg _)
    dsimp only [dg] at hb
    rw [l2Error_eq_eLpNorm M _ _ hm] at hb
    exact hb
  · exact hr
  · exact hw


-- At the true nuisances the fitted residual corrections vanish, leaving
-- precisely the terminal contribution to the lower-bound target.
-- @node: true_continuous_tail_score_mean
/-- Under [threshold crossing](hyp:h), assume [a valid policy](hyp:hphi) [with the specified derivative](hyp:hd),
[a bounded, Lipschitz derivative](hyp:hDerivative), [at least one positive level](hyp:hK),
[policy-invariant level order](hyp:hOrder), [admissible true nuisances](hyp:he0), and [baseline overlap](hyp:hov).
Then [the true terminal score is integrable, and its mean equals the covariate average of the lower outcome endpoint times the difference between the instrument-probability-weighted policy propensity over the terminal union and the terminal baseline level probability times the terminal weight](goal). -/
lemma true_continuous_tail_score_mean (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) :
    Integrable (commonTailScore M phi dphi L (trueNuisance M L).prop
      (trueNuisance M L).pLev (trueNuisance M L).piLev (trueNuisance M L).gammaTail)
      (observationLaw M) ∧
    (∫ o, commonTailScore M phi dphi L (trueNuisance M L).prop (trueNuisance M L).pLev
        (trueNuisance M L).piLev (trueNuisance M L).gammaTail o ∂observationLaw M) =
      ∫ x, M.yMin * ((∑ z ∈ policyUnion L L.K 1,
        instProb M z x * phi z x (M.prop z x)) -
        L.pLev L.K x * gammaTail M L x) ∂xLaw M := by
  have hi : 1 ≤ L.K ∧ L.K ≤ L.K := ⟨hK, le_rfl⟩
  have hclip : ∀ᵐ x ∂xLaw M, cpi ≤ positiveValue (trueNuisance M L).piLev L.K x :=
    Eventually.of_forall (fun x => by
      simpa only [positiveValue, dif_pos hi, trueNuisance] using hov.2 x L.K hK le_rfl)
  have hm := fitted_tail_population_mean M h phi dphi hphi hd hDerivative
    L hK hOrder (continuousTailCoordinates L (trueNuisance M L))
      (continuousTailCoordinates_admissible M L (trueNuisance M L) he0) cpi hov.1 hclip
  refine ⟨hm.1, ?_⟩
  simpa only [continuousTailCoordinates, trueNuisance, positiveValue, dif_pos hi, sub_self, mul_zero,
    zero_mul, add_zero] using hm.2

end Papers.TbsPrteOptimalTransport
