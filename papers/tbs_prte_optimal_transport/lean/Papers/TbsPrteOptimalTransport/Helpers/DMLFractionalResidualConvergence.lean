module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLFractionalBranchRates
public import Papers.TbsPrteOptimalTransport.Helpers.DMLTailBaselineConvergence
/-! Fractional binary score corrections under the observation law.
Measurable versions of the clipped hinge arguments supply branch moments.
The branch gap and nuisance rates control the actual branch-weighted residuals. -/
public section
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

-- The policy is measurable on its clipped domain only, so its actual fitted
-- branches need almost-everywhere strong measurability rather than global measurability.
-- @node: dml_ae_weighted_residual_integrated_sq_bound
/-- If [the reference and fitted weights are almost everywhere strongly measurable](hyp:hw,hwh),
[the reference and fitted residuals are almost everywhere strongly measurable](hyp:hf,hfh),
[the weight error is square-integrable](hyp:hew), [the residual error is square-integrable](hyp:hef),
[the fitted weight is bounded in absolute value by W almost everywhere](hyp:hwb), and
[the reference residual is bounded in absolute value by R almost everywhere](hyp:hfb), then
[the squared error of the weighted residual is integrable and its integral is at most twice W squared times the integrated squared residual error plus twice R squared times the integrated squared weight error](goal). -/
lemma dml_ae_weighted_residual_integrated_sq_bound {B : Type*} [MeasurableSpace B]
    (ν : Measure B) (w wh f fh : B → ℝ) (W R : ℝ)
    (hw : AEStronglyMeasurable w ν) (hwh : AEStronglyMeasurable wh ν)
    (hf : AEStronglyMeasurable f ν) (hfh : AEStronglyMeasurable fh ν)
    (hew : MemLp (fun x => wh x - w x) 2 ν)
    (hef : MemLp (fun x => fh x - f x) 2 ν)
    (hwb : ∀ᵐ x ∂ν, |wh x| ≤ W) (hfb : ∀ᵐ x ∂ν, |f x| ≤ R) :
    Integrable (fun x => (wh x * fh x - w x * f x)^2) ν ∧
      (∫ x, (wh x * fh x - w x * f x)^2 ∂ν) ≤
        2 * W^2 * (∫ x, (fh x - f x)^2 ∂ν) +
          2 * R^2 * (∫ x, (wh x - w x)^2 ∂ν) := by
  have hm : AEStronglyMeasurable (fun x => (wh x * fh x - w x * f x)^2) ν := by
    fun_prop
  have hb : ∀ᵐ x ∂ν, (wh x * fh x - w x * f x)^2 ≤
      2 * W^2 * (fh x - f x)^2 + 2 * R^2 * (wh x - w x)^2 := by
    filter_upwards [hwb, hfb] with x hx hy
    exact clipped_weighted_residual_sq_difference_bound hx hy
  have hd := (hef.integrable_sq.const_mul (2*W^2)).add
    (hew.integrable_sq.const_mul (2*R^2))
  have hi := hd.mono' hm (by
    filter_upwards [hb] with x hx
    simpa only [Real.norm_eq_abs, Pi.add_apply,
      abs_of_nonneg (sq_nonneg (wh x * fh x - w x * f x))] using hx)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x, 2*W^2 * (fh x-f x)^2 + 2*R^2 * (wh x-w x)^2 ∂ν :=
      integral_mono_ae hi hd hb
    _ = _ := by
      rw [integral_add (hef.integrable_sq.const_mul _) (hew.integrable_sq.const_mul _),
        integral_const_mul, integral_const_mul]

-- @node: dml_ae_weighted_residual_sq_tendsto_probability_zero
/-- Suppose [the reference weight and residual are almost everywhere strongly measurable](hyp:hw,hf),
[every fitted weight and residual is almost everywhere strongly measurable](hyp:hwh,hfh),
[every weight error and residual error is square-integrable](hyp:hew,hef),
[all fitted weights are bounded in absolute value by W almost everywhere](hyp:hwb), and
[the reference residual is bounded in absolute value by R almost everywhere for every fit](hyp:hfb).
If [the integrated squared weight errors converge in probability to zero](hyp:hrw) and
[the integrated squared residual errors converge in probability to zero](hyp:hrf), then
[the integrated squared errors of the weighted residuals converge in probability to zero](goal). -/
lemma dml_ae_weighted_residual_sq_tendsto_probability_zero {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] (μ : Measure A) (ν : Measure B)
    (w f : B → ℝ) (wh fh : ℕ → A → B → ℝ) (W R : ℝ)
    (hw : AEStronglyMeasurable w ν) (hf : AEStronglyMeasurable f ν)
    (hwh : ∀ n a, AEStronglyMeasurable (wh n a) ν)
    (hfh : ∀ n a, AEStronglyMeasurable (fh n a) ν)
    (hew : ∀ n a, MemLp (fun x => wh n a x - w x) 2 ν)
    (hef : ∀ n a, MemLp (fun x => fh n a x - f x) 2 ν)
    (hwb : ∀ n a, ∀ᵐ x ∂ν, |wh n a x| ≤ W)
    (hfb : ∀ (_n : ℕ) (_a : A), ∀ᵐ x ∂ν, |f x| ≤ R)
    (hrw : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, (wh n a x - w x)^2 ∂ν) atTop (fun _ _ => 0))
    (hrf : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, (fh n a x - f x)^2 ∂ν) atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, (wh n a x * fh n a x - w x * f x)^2 ∂ν)
      atTop (fun _ _ => 0) := by
  have hcf : Continuous (fun t : ℝ => 2*W^2*t) := by fun_prop
  have hcw : Continuous (fun t : ℝ => -(2*R^2*t)) := by fun_prop
  have hF := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    hcf.continuousAt hrf
  have hW := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    hcw.continuousAt hrw
  simp only [mul_zero, neg_zero] at hF hW
  have hs := hF.sub hW
  simp only [sub_neg_eq_add, sub_zero] at hs
  apply probability_zero_of_nonneg_le μ _ _ hs
  intro n
  apply Eventually.of_forall
  intro a
  exact ⟨integral_nonneg (fun x => sq_nonneg _),
    (dml_ae_weighted_residual_integrated_sq_bound ν w (wh n a) f (fh n a) W R
      hw (hwh n a) hf (hfh n a) (hew n a) (hef n a) (hwb n a) (hfb n a)).2⟩

-- @node: dml_hinge_branch_memLp
/-- Under a finite measure, if [the upper hinge argument is square-integrable](hyp:hq),
[the lower hinge argument is square-integrable](hyp:hl), and [the threshold is square-integrable](hyp:hb),
then [all three branch indicators are square-integrable: the upper argument exceeds both the lower argument and threshold, the threshold lies strictly between the two arguments, and the lower argument exceeds the threshold](goal). -/
lemma dml_hinge_branch_memLp {B : Type*} [MeasurableSpace B]
    (ν : Measure B) [IsFiniteMeasure ν] (q l b : B → ℝ)
    (hq : MemLp q 2 ν) (hl : MemLp l 2 ν) (hb : MemLp b 2 ν) :
    MemLp (fun x => indicator (q x > max (l x) (b x))) 2 ν ∧
    MemLp (fun x => indicator (l x < b x ∧ b x < q x)) 2 ν ∧
    MemLp (fun x => indicator (l x > b x)) 2 ν := by
  let Q := hq.1.mk q
  let L := hl.1.mk l
  let B := hb.1.mk b
  have hQ : Measurable Q := hq.1.stronglyMeasurable_mk.measurable
  have hL : Measurable L := hl.1.stronglyMeasurable_mk.measurable
  have hB : Measurable B := hb.1.stronglyMeasurable_mk.measurable
  have hI : MemLp (fun x => indicator (Q x > max (L x) (B x))) 2 ν := by
    apply MemLp.of_bound (by
      unfold indicator
      exact (Measurable.ite (measurableSet_lt (hL.max hB) hQ)
        measurable_const measurable_const).aestronglyMeasurable) 1
    exact Eventually.of_forall (fun x => by unfold indicator; split_ifs <;> norm_num)
  have hD : MemLp (fun x => indicator (L x < B x ∧ B x < Q x)) 2 ν := by
    apply MemLp.of_bound (by
      unfold indicator
      exact (Measurable.ite ((measurableSet_lt hL hB).inter (measurableSet_lt hB hQ))
        measurable_const measurable_const).aestronglyMeasurable) 1
    exact Eventually.of_forall (fun x => by unfold indicator; split_ifs <;> norm_num)
  have hE : MemLp (fun x => indicator (L x > B x)) 2 ν := by
    apply MemLp.of_bound (by
      unfold indicator
      exact (Measurable.ite (measurableSet_lt hB hL)
        measurable_const measurable_const).aestronglyMeasurable) 1
    exact Eventually.of_forall (fun x => by unfold indicator; split_ifs <;> norm_num)
  refine ⟨hI.ae_eq ?_, hD.ae_eq ?_, hE.ae_eq ?_⟩ <;>
    filter_upwards [hq.1.ae_eq_mk, hl.1.ae_eq_mk, hb.1.ae_eq_mk] with x h1 h2 h3 <;>
    simp only [← h1, ← h2, ← h3, Q, L, B]

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: fitted_fractional_branches_memLp
/-- If [the policy map satisfies the policy restrictions](hyp:hphi) and
[the binary nuisance functions are admissible](hyp:he), then
[the active, interior, and dominance branch indicators for any chosen interval and band are square-integrable under the covariate law](goal). -/
lemma fitted_fractional_branches_memLp (phi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (L : LevelData Z X) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (k j : ℕ) :
    MemLp (Iact phi L e k j) 2 (xLaw M) ∧
    MemLp (Dbd phi L e k j) 2 (xLaw M) ∧
    MemLp (Edom phi L e k j) 2 (xLaw M) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  exact dml_hinge_branch_memLp (xLaw M) _ _ _
    (fitted_pooledQBin_memLp M phi hphi L e he k j)
    (fitted_pooledQBin_memLp M phi hphi L e he k (j-1))
    (((fitted_positive_treatment_assignment_memLp M L e he (k+1)).1).sub
      ((fitted_positive_success_memLp M L e he (k+1)).sub
        (fitted_positive_success_memLp M L e he k)))

-- The aggregate branch energy is transported to the observed covariate;
-- no global measurability of the unmodified fitted policy is required.
-- @node: nuisanceRates_fractional_branch_observation_sq_tendsto_probability_zero
/-- Suppose [the policy satisfies the policy restrictions](hyp:hphi),
[its derivative is the specified derivative map](hyp:hd), [that derivative is bounded and Lipschitz](hyp:hDerivative),
[the reference nuisance functions are admissible](hyp:he0), and [every fitted nuisance vector is admissible](hyp:heh).
If [the instrument propensity, treatment-level probability, and success components satisfy the finite nuisance rates](hyp:hrp,hrlev,hrP),
[each regular share component satisfies those rates](hyp:hrs), [the separation constant is positive](hyp:hsep), and
[almost everywhere the reference upper and lower pooled policy values are separated by that constant and the branch threshold is at least that far from both values](hyp:hgap), then
[the observation-law integral of the sum of squared errors of the active, interior, and dominance indicators, evaluated at sample sizes twice n plus two, converges in probability to zero](goal). -/
lemma nuisanceRates_fractional_branch_observation_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1)
    (hrs : ∀ a : RegularIndex L,
      FiniteNuisanceRates M μ (fun n t => (eh n t).share a) (e0.share a))
    (k j : ℕ) (sep : ℝ) (hsep : 0 < sep)
    (hgap : ∀ᵐ x ∂xLaw M,
      sep ≤ pooledQBin phi L e0 k j x - pooledQBin phi L e0 k (j-1) x ∧
      sep ≤ |positiveValue e0.pLev (k+1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k (j-1) x| ∧
      sep ≤ |positiveValue e0.pLev (k+1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k j x|) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        (Iact phi L (eh (2*(n+1)) a) k j o.1 - Iact phi L e0 k j o.1)^2 +
        (Dbd phi L (eh (2*(n+1)) a) k j o.1 - Dbd phi L e0 k j o.1)^2 +
        (Edom phi L (eh (2*(n+1)) a) k j o.1 - Edom phi L e0 k j o.1)^2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  have hl := nuisanceRates_fractional_branch_l2_tendsto_probability_zero M μ
    phi dphi hphi hd hDerivative L e0 eh he0 heh hrp hrlev hrP hrs k j sep hsep hgap
  have hc : Continuous (fun t : ℝ => t^2) := by fun_prop
  have hs := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    hc.continuousAt hl
  simp only [Real.sq_sqrt (integral_nonneg fun x =>
    add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)),
    zero_pow (by norm_num : 2 ≠ 0)] at hs
  have heq (n : ℕ) (a : A) :
      (∫ o : Obs X Z,
        (Iact phi L (eh (2*(n+1)) a) k j o.1 - Iact phi L e0 k j o.1)^2 +
        (Dbd phi L (eh (2*(n+1)) a) k j o.1 - Dbd phi L e0 k j o.1)^2 +
        (Edom phi L (eh (2*(n+1)) a) k j o.1 - Edom phi L e0 k j o.1)^2
        ∂observationLaw M) =
      ∫ x,
        (Iact phi L (eh (2*(n+1)) a) k j x - Iact phi L e0 k j x)^2 +
        (Dbd phi L (eh (2*(n+1)) a) k j x - Dbd phi L e0 k j x)^2 +
        (Edom phi L (eh (2*(n+1)) a) k j x - Edom phi L e0 k j x)^2 ∂xLaw M := by
    obtain ⟨hi, hd, he⟩ := fitted_fractional_branches_memLp M phi hphi L e0 he0 k j
    obtain ⟨hi', hd', he'⟩ := fitted_fractional_branches_memLp M phi hphi L _ (heh _ a) k j
    have hm := (((hi'.sub hi).1.pow 2).add ((hd'.sub hd).1.pow 2)).add
      ((he'.sub he).1.pow 2)
    have hmp := observationLaw_fst_measurePreserving M
    rw [← hmp.map_eq]
    exact (integral_map hmp.aemeasurable (by rw [hmp.map_eq]; exact hm)).symm
  simpa only [heq] using hs

-- Both terms in the weighted-residual bound are derived: branch energy from
-- the separation, residual energy from P1 and the clipped denominators.
-- @node: nuisanceRates_Dbd_RP_sq_tendsto_probability_zero
/-- Suppose [the policy satisfies the policy restrictions](hyp:hphi),
[the given derivative differentiates it](hyp:hd), [the derivative is bounded and Lipschitz](hyp:hDerivative),
[the reference nuisance vector is admissible](hyp:he0), [all fitted nuisance vectors are admissible](hyp:heh),
and [the outcome is binary almost surely](hyp:hy). Assume [a positive clipping constant](hyp:hc),
[reference and fitted assignment probabilities bounded below by that constant almost everywhere](hyp:hclip),
[finite nuisance rates for instrument propensities, treatment-level probabilities, success probabilities, and assignment probabilities](hyp:hrp,hrlev,hrP,hrpi),
[finite nuisance rates for every regular share](hyp:hrs), and [a residual index no larger than the number of levels](hyp:hi).
With [a positive separation constant](hyp:hsep) and
[reference pooled policy endpoints separated by that constant and the branch threshold at least that far from both endpoints almost everywhere](hyp:hgap),
[the integrated squared error of the interior-branch indicator times the success residual, evaluated at sample sizes twice n plus two, converges in probability to zero](goal). -/
lemma nuisanceRates_Dbd_RP_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hy : OutcomeBinaryAE M) (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrs : ∀ a : RegularIndex L,
      FiniteNuisanceRates M μ (fun n t => (eh n t).share a) (e0.share a))
    (k j i : ℕ) (hi : i ≤ L.K) (sep : ℝ) (hsep : 0 < sep)
    (hgap : ∀ᵐ x ∂xLaw M,
      sep ≤ pooledQBin phi L e0 k j x - pooledQBin phi L e0 k (j-1) x ∧
      sep ≤ |positiveValue e0.pLev (k+1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k (j-1) x| ∧
      sep ≤ |positiveValue e0.pLev (k+1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k j x|) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o,
        (Dbd phi L (eh (2*(n+1)) a) k j o.1 * RP L (eh (2*(n+1)) a) i o -
          Dbd phi L e0 k j o.1 * RP L e0 i o)^2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  have hmp := observationLaw_fst_measurePreserving M
  have hD (e : NuisanceBin L) (he : BinAdmissible M L e) :=
    ((fitted_fractional_branches_memLp M phi hphi L e he k j).2.1).comp_measurePreserving hmp
  have hr := nuisanceRates_fractional_branch_observation_sq_tendsto_probability_zero
    M μ phi dphi hphi hd hDerivative L e0 eh he0 heh hrp hrlev hrP hrs k j sep hsep hgap
  have hrD : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        (Dbd phi L (eh (2*(n+1)) a) k j o.1 - Dbd phi L e0 k j o.1)^2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
    apply probability_zero_of_nonneg_le μ _ _ hr
    intro n
    apply Eventually.of_forall
    intro a
    refine ⟨integral_nonneg (fun o => sq_nonneg _), ?_⟩
    have h0 := fitted_fractional_branches_memLp M phi hphi L e0 he0 k j
    have hh := fitted_fractional_branches_memLp M phi hphi L _ (heh (2*(n+1)) a) k j
    have hI := ((hh.1.sub h0.1).comp_measurePreserving hmp).integrable_sq
    have hD' := ((hh.2.1.sub h0.2.1).comp_measurePreserving hmp).integrable_sq
    have hE := ((hh.2.2.sub h0.2.2).comp_measurePreserving hmp).integrable_sq
    apply integral_mono hD' ((hI.add hD').add hE)
    intro o
    dsimp only [Pi.sub_apply, Pi.add_apply, Function.comp_apply]
    linarith [sq_nonneg (Iact phi L (eh (2*(n+1)) a) k j o.1 - Iact phi L e0 k j o.1),
      sq_nonneg (Edom phi L (eh (2*(n+1)) a) k j o.1 - Edom phi L e0 k j o.1)]
  apply dml_ae_weighted_residual_sq_tendsto_probability_zero μ (observationLaw M)
    (fun o => Dbd phi L e0 k j o.1) (RP L e0 i)
    (fun n a o => Dbd phi L (eh (2*(n+1)) a) k j o.1)
    (fun n a => RP L (eh (2*(n+1)) a) i) 1 (1/c)
    (hD e0 he0).1 (by fun_prop) (fun n a => (hD _ (heh _ a)).1)
    (by intro n a; first | fun_prop | exact (fitted_RP_measurable M L _ (heh _ a) i).aestronglyMeasurable)
  · exact fun n a => (hD _ (heh _ a)).sub (hD e0 he0)
  · intro n a
    exact (fitted_RP_memLp M L _ (heh _ a) hy c hc
      (fun t => (hclip _ a t).mono (fun _ hx => hx.2)) i hi).sub
      (fitted_RP_memLp M L e0 he0 hy c hc
        (fun t => (hclip (2*(n+1)) a t).mono (fun _ hx => hx.1)) i hi)
  · intro n a
    exact Eventually.of_forall (fun o => by unfold Dbd indicator; split_ifs <;> norm_num)
  · exact fun n a => fitted_RP_abs_bound M L e0 he0 hy c hc
      (fun t => (hclip n a t).mono (fun _ hx => hx.1)) i hi
  · exact hrD
  · exact nuisanceRates_RP_sq_tendsto_probability_zero M μ L e0 eh he0 heh
      hy c hc hclip hrP hrpi i hi

-- The actual interior-branch correction has a second moment even when the
-- fitted propensity lies in its clipped domain only almost everywhere.
-- @node: fitted_Dbd_RP_memLp
/-- If [the policy satisfies the policy restrictions](hyp:hphi), [the binary nuisance vector is admissible](hyp:he),
[the outcome is binary almost surely](hyp:hy), [the clipping constant is positive](hyp:hc),
[all positive-level assignment probabilities are at least that constant almost everywhere](hyp:hclip), and
[the residual index is no larger than the number of levels](hyp:hi), then
[the interior-branch indicator times the success residual is square-integrable under the observation law](goal). -/
lemma fitted_Dbd_RP_memLp (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e)
    (hy : OutcomeBinaryAE M) (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (k j i : ℕ) (hi : i ≤ L.K) :
    MemLp (fun o => Dbd phi L e k j o.1 * RP L e i o) 2 (observationLaw M) := by
  have hD := ((fitted_fractional_branches_memLp M phi hphi L e he k j).2.1).comp_measurePreserving
    (observationLaw_fst_measurePreserving M)
  have hr := fitted_RP_memLp M L e he hy c hc hclip i hi
  apply hr.norm.mono' (by first | fun_prop | exact hD.1.mul hr.1)
  apply Eventually.of_forall
  intro o
  rw [norm_mul]
  have hb : ‖Dbd phi L e k j o.1‖ ≤ 1 := by
    unfold Dbd indicator
    split_ifs <;> norm_num
  exact mul_le_of_le_one_left (norm_nonneg _) hb

end Papers.TbsPrteOptimalTransport
