module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationContinuousFullRegressions
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousFullMeanOverlap
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationFullJointMean
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationFullJointDerivative
/-! Exact full-interval bias with simultaneous continuous regressions and denominators. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

-- The propensity/outcome coefficient is quadratic along an affine path.
-- Its assignment defect supplies the second error factor.
-- @node: continuous_full_affine_coefficient_defect
/-- If [the affine assignment denominator is nonzero](hyp:hpi), then [the change in
the product of two affine regression components, multiplied by the reciprocal
assignment defect, equals the squared path displacement times the product of the
assignment direction and the regression increment coefficient, divided by the
affine denominator](goal). -/
lemma continuous_full_affine_coefficient_defect (p j pi dp dj dpi t : ℝ)
    (hpi : pi + t * dpi ≠ 0) :
    ((p + t * dp) * (j + t * dj) - p * j) * (1 - pi / (pi + t * dpi)) =
      t^2 * ((p * dj + dp * j + t * dp * dj) * dpi / (pi + t * dpi)) := by
  field_simp [hpi]
  <;> ring

-- @node: continuous_full_affine_coefficient_defect_bound
/-- If [the denominator floor c is positive](hyp:hc), [the affine denominator is
at least c](hyp:hpi), and [the absolute path displacement is at most one](hyp:ht),
then [the absolute product of the regression product increment and reciprocal
assignment defect is at most the squared displacement times
(|p| |dj| + |dp| |j| + |dp| |dj|) |dpi| / c](goal). -/
lemma continuous_full_affine_coefficient_defect_bound (p j pi dp dj dpi t c : ℝ)
    (hc : 0 < c) (hpi : c ≤ pi + t * dpi) (ht : |t| ≤ 1) :
    |((p + t * dp) * (j + t * dj) - p * j) * (1 - pi / (pi + t * dpi))| ≤
      t^2 * ((|p| * |dj| + |dp| * |j| + |dp| * |dj|) * |dpi| / c) := by
  have hpos : 0 < pi + t * dpi := hc.trans_le hpi
  rw [continuous_full_affine_coefficient_defect p j pi dp dj dpi t hpos.ne',
    abs_mul, abs_of_nonneg (sq_nonneg t), abs_div, abs_mul, abs_of_pos hpos]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg t)
  have hnum : |p * dj + dp * j + t * dp * dj| ≤
      |p| * |dj| + |dp| * |j| + |dp| * |dj| := by
    calc
      _ ≤ |p * dj + dp * j| + |t * dp * dj| := abs_add_le _ _
      _ ≤ (|p * dj| + |dp * j|) + |t * dp * dj| := by
        gcongr
        exact abs_add_le _ _
      _ = (|p| * |dj| + |dp| * |j|) + |t| * |dp| * |dj| := by
        simp only [abs_mul]
      _ ≤ _ := by nlinarith [mul_nonneg (abs_nonneg dp) (abs_nonneg dj)]
  calc
    _ ≤ (|p| * |dj| + |dp| * |j| + |dp| * |dj|) * |dpi| / (pi + t * dpi) := by
      gcongr
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hc hpi

-- @node: continuous_full_coefficient_reciprocal_defect_bound
/-- Suppose [c is positive](hyp:hc), [the fitted denominator is at least c](hyp:hpi),
[the coefficient error is at most D times the absolute displacement](hyp:ha),
[the denominator error is at most C times the absolute displacement](hyp:hd),
[the weight has absolute value at most B](hyp:hw), and [D and C are
nonnegative](hyp:hD,hC). Then [the absolute weighted coefficient error times the
reciprocal denominator defect is at most B D C / c times the squared displacement](goal). -/
lemma continuous_full_coefficient_reciprocal_defect_bound
    (a a0 pi pi0 w D C B t c : ℝ) (hc : 0 < c) (hpi : c ≤ pi)
    (ha : |a - a0| ≤ D * |t|) (hd : |pi - pi0| ≤ C * |t|)
    (hw : |w| ≤ B) (hD : 0 ≤ D) (hC : 0 ≤ C) :
    |(w * (a - a0)) * (1 - pi0 / pi)| ≤ (B * D * C / c) * t^2 := by
  have hpos := hc.trans_le hpi
  have hB : 0 ≤ B := (abs_nonneg w).trans hw
  have hid : 1 - pi0 / pi = (pi - pi0) / pi := by
    field_simp
    <;> ring
  rw [hid, abs_mul, abs_mul, abs_div, abs_of_pos hpos]
  calc
    _ ≤ (B * (D * |t|)) * (C * |t| / pi) := by
      gcongr <;> positivity
    _ ≤ (B * (D * |t|)) * (C * |t| / c) := by
      gcongr
    _ = (B * D * C / c) * t^2 := by
      rw [← sq_abs t]
      ring

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- Centering a fitted assignment denominator leaves its exact reciprocal defect.
-- @node: population_fitted_normalized_assignment_defect
/-- For [a measurable fitted assignment denominator](hyp:hpi) and [a measurable
covariate weight](hyp:hw), suppose [c is positive](hyp:hc), [the denominator is at
least c almost surely](hyp:hclip), and [the weight has magnitude at most B almost
surely](hyp:hb). Then [the weighted normalized assignment defect and its version
with the assignment indicator replaced by its conditional probability are both
integrable and have equal population means](goal). -/
lemma population_fitted_normalized_assignment_defect (C : Finset Z)
    (pi w : X → ℝ) (hpi : Measurable pi) (hw : Measurable w)
    (c B : ℝ) (hc : 0 < c) (hclip : ∀ᵐ x ∂xLaw M, c ≤ pi x)
    (hb : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ B) :
    Integrable (fun o : Obs X Z => w o.1 *
      (1 - indicator (o.2.1 ∈ C) / pi o.1)) (observationLaw M) ∧
    Integrable (fun o : Obs X Z => w o.1 *
      (1 - (∑ z ∈ C, instProb M z o.1) / pi o.1)) (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 * (1 - indicator (o.2.1 ∈ C) / pi o.1)
      ∂observationLaw M) =
      ∫ o : Obs X Z, w o.1 * (1 - (∑ z ∈ C, instProb M z o.1) / pi o.1)
        ∂observationLaw M := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  have iw : Integrable (fun o : Obs X Z => w o.1) (observationLaw M) :=
    Integrable.of_bound (hw.comp measurable_fst).aestronglyMeasurable B
      (observationLaw_covariate_ae M _ hb)
  obtain ⟨iz, ip, hz⟩ := population_fitted_assignment_weighted_mean M C pi w
    hpi hw c B hc hclip hb
  have hid (a b d : ℝ) : a * (1 - b / d) = a - a * b / d := by ring
  simp_rw [hid]
  exact ⟨iw.sub' iz, iw.sub' ip, by rw [integral_sub iw iz, integral_sub iw ip, hz]⟩

-- Compare against the truth with the same fitted denominator. This isolates
-- regression times denominator error and retains simultaneous propensity changes.
-- @node: continuous_full_joint_regression_denominator_difference
/-- [The fitted full-interval score minus the score with true regressions and the
same fitted denominators equals the upper regression coefficient error times its
normalized assignment defect, minus the corresponding lower product](goal). -/
lemma continuous_full_joint_regression_denominator_difference
    (L : LevelData Z X) (e : NuisanceCont L) (k : ℕ) (o : Obs X Z) :
    psiFullJ L e k o - psiFullJ L {trueNuisance M L with piLev := e.piLev} k o =
      (continuousFullRegressionCoefficient L e true k o.1 -
        continuousFullRegressionCoefficient L (trueNuisance M L) true k o.1) *
        (1 - indicator (o.2.1 ∈ L.S (k + 1)) / positiveValue e.piLev (k + 1) o.1) -
      (continuousFullRegressionCoefficient L e false k o.1 -
        continuousFullRegressionCoefficient L (trueNuisance M L) false k o.1) *
        (1 - indicator (o.2.1 ∈ L.S k) / positiveValue e.piLev k o.1) := by
  exact continuous_full_fixed_denominator_difference L e
    {trueNuisance M L with piLev := e.piLev} rfl k o

-- All residual centering is derived from the constructed population laws.
-- Bounds here concern primitive fitted coefficients, not the score bias.
-- @node: population_continuous_full_joint_fitted_bias
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
and [invariant baseline and policy level ordering](hyp:hL), suppose [the fitted
assignment denominators are measurable](hyp:hpi), [c is positive](hyp:hc), and
[all fitted denominators are at least c almost surely](hyp:hclip). If [the
covariate weight is measurable](hyp:hw) and [integrable](hyp:hwi), [its products
with the upper and lower regression coefficient errors are measurable](hyp:hp,hm),
and [these products are bounded in magnitude by Bp and Bm, respectively, almost
surely](hyp:hBp,hBm), then [the weighted fitted full-interval score is integrable
and its mean equals the weighted true regression contrast plus the mean upper
weighted coefficient error times the reciprocal denominator defect, minus the
corresponding lower mean](goal). -/
lemma population_continuous_full_joint_fitted_bias
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (e : NuisanceCont L) (hpi : ∀ a, Measurable (e.piLev a))
    (c : ℝ) (hc : 0 < c) (hclip : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ e.piLev a x)
    (k : Fin L.K) (w : X → ℝ) (hw : Measurable w) (hwi : Integrable w (xLaw M))
    (hp : Measurable (fun x => w x *
      (continuousFullRegressionCoefficient L e true k x -
        continuousFullRegressionCoefficient L (trueNuisance M L) true k x)))
    (hm : Measurable (fun x => w x *
      (continuousFullRegressionCoefficient L e false k x -
        continuousFullRegressionCoefficient L (trueNuisance M L) false k x)))
    (Bp Bm : ℝ)
    (hBp : ∀ᵐ x ∂xLaw M, ‖w x *
      (continuousFullRegressionCoefficient L e true k x -
        continuousFullRegressionCoefficient L (trueNuisance M L) true k x)‖ ≤ Bp)
    (hBm : ∀ᵐ x ∂xLaw M, ‖w x *
      (continuousFullRegressionCoefficient L e false k x -
        continuousFullRegressionCoefficient L (trueNuisance M L) false k x)‖ ≤ Bm) :
    Integrable (fun o : Obs X Z => w o.1 * psiFullJ L e k o) (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 * psiFullJ L e k o ∂observationLaw M) =
      (∫ o : Obs X Z, w o.1 * contFullJ L (trueNuisance M L) k o.1 ∂observationLaw M) +
      (∫ o : Obs X Z, (w o.1 *
        (continuousFullRegressionCoefficient L e true k o.1 -
          continuousFullRegressionCoefficient L (trueNuisance M L) true k o.1)) *
        (1 - positiveValue (trueNuisance M L).piLev (k + 1) o.1 /
          positiveValue e.piLev (k + 1) o.1) ∂observationLaw M) -
      (∫ o : Obs X Z, (w o.1 *
        (continuousFullRegressionCoefficient L e false k o.1 -
          continuousFullRegressionCoefficient L (trueNuisance M L) false k o.1)) *
        (1 - positiveValue (trueNuisance M L).piLev k o.1 /
          positiveValue e.piLev k o.1) ∂observationLaw M) := by
  let vp : X → ℝ := fun x => w x *
    (continuousFullRegressionCoefficient L e true k x -
      continuousFullRegressionCoefficient L (trueNuisance M L) true k x)
  let vm : X → ℝ := fun x => w x *
    (continuousFullRegressionCoefficient L e false k x -
      continuousFullRegressionCoefficient L (trueNuisance M L) false k x)
  have hpos : 1 ≤ k.val + 1 ∧ k.val + 1 ≤ L.K := by omega
  obtain ⟨ip, ipp, zp⟩ := population_fitted_normalized_assignment_defect M (L.S (k+1))
    (e.piLev ⟨k+1,hpos⟩) vp (hpi _) hp c Bp hc (hclip _) hBp
  have hpden (x : X) : positiveValue (trueNuisance M L).piLev (k+1) x =
      ∑ z ∈ L.S (k+1), instProb M z x := by
    simp only [positiveValue, dif_pos hpos, trueNuisance, levelSetProb]
  have hepos : positiveValue e.piLev (k+1) = e.piLev ⟨k+1,hpos⟩ := by
    funext x
    simp only [positiveValue, dif_pos hpos]
  rw [← hepos] at ip ipp zp
  simp only [← hpden] at ipp zp
  have hminus : Integrable (fun o : Obs X Z => vm o.1 *
      (1 - indicator (o.2.1 ∈ L.S k) / positiveValue e.piLev k o.1)) (observationLaw M) ∧
    (∫ o : Obs X Z, vm o.1 *
      (1 - indicator (o.2.1 ∈ L.S k) / positiveValue e.piLev k o.1) ∂observationLaw M) =
    ∫ o : Obs X Z, vm o.1 * (1 - positiveValue (trueNuisance M L).piLev k o.1 /
      positiveValue e.piLev k o.1) ∂observationLaw M := by
    by_cases hk0 : k.val = 0
    · have hz : vm = fun _ => (0 : ℝ) := by
        funext x
        simp [vm, continuousFullRegressionCoefficient, hk0]
      simp only [hz, zero_mul, integral_zero]
      exact ⟨integrable_zero _ _ _, True.intro⟩
    · have hi : 1 ≤ k.val ∧ k.val ≤ L.K := by omega
      obtain ⟨im, imp, zm⟩ := population_fitted_normalized_assignment_defect M (L.S k)
        (e.piLev ⟨k,hi⟩) vm (hpi _) hm c Bm hc (hclip _) hBm
      have hden (x : X) : positiveValue (trueNuisance M L).piLev k x =
          ∑ z ∈ L.S k, instProb M z x := by
        simp only [positiveValue, dif_pos hi, trueNuisance, levelSetProb]
      have heden : positiveValue e.piLev k = e.piLev ⟨k,hi⟩ := by
        funext x
        simp only [positiveValue, dif_pos hi]
      rw [← heden] at im zm
      simp only [← hden] at zm
      exact ⟨im, zm⟩
  obtain ⟨ib, zb⟩ := population_continuous_full_mean_of_clipped_denominator M h he q L hL
    e.piLev hpi c hc hclip k k.isLt w hw hwi
  have hid : (fun o : Obs X Z => w o.1 * psiFullJ L e k o) =
      (fun o => w o.1 * psiFullJ L {trueNuisance M L with piLev := e.piLev} k o +
        vp o.1 * (1 - indicator (o.2.1 ∈ L.S (k+1)) / positiveValue e.piLev (k+1) o.1) -
        vm o.1 * (1 - indicator (o.2.1 ∈ L.S k) / positiveValue e.piLev k o.1)) := by
    funext o
    have hd := continuous_full_joint_regression_denominator_difference M L e k o
    dsimp only [vp, vm]
    linear_combination w o.1 * hd
  rw [hid]
  refine ⟨(ib.fun_add ip).sub' hminus.1, ?_⟩
  rw [integral_sub (ib.fun_add ip) hminus.1, integral_add ib ip, zb, zp, hminus.2]

-- Primitive Lipschitz path bounds produce a quadratic integrated remainder.
-- The path may change both regressions, propensities, and denominators together.
-- @node: population_continuous_full_joint_regression_denominator_orthogonality
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
and [invariant baseline and policy level ordering](hyp:hL), consider [a nuisance
path starting at the truth](hyp:he0) and [a measurable covariate weight](hyp:hw).
Suppose [B, D, and C are nonnegative](hyp:hB,hD,hC), [c is positive](hyp:hc),
[the weight is bounded in magnitude by B almost surely](hyp:hwB), and [near zero
the denominators and regression coefficients are measurable, the denominators
are at least c almost surely, and the coefficient and denominator errors are
bounded almost surely by D and C times the absolute path displacement,
respectively](hyp:hlocal). Then [the population mean of the weighted fitted
full-interval score has derivative zero at zero](goal). -/
lemma population_continuous_full_joint_regression_denominator_orthogonality
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (e : ℝ → NuisanceCont L) (he0 : e 0 = trueNuisance M L)
    (k : Fin L.K) (w : X → ℝ) (hw : Measurable w)
    (B D C c : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D) (hC : 0 ≤ C) (hc : 0 < c)
    (hwB : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ B)
    (hlocal : ∀ᶠ t : ℝ in 𝓝 0,
      (∀ a, Measurable ((e t).piLev a)) ∧
      (∀ a, ∀ᵐ x ∂xLaw M, c ≤ (e t).piLev a x) ∧
      (∀ plus, Measurable (continuousFullRegressionCoefficient L (e t) plus k)) ∧
      (∀ plus, ∀ᵐ x ∂xLaw M,
        |continuousFullRegressionCoefficient L (e t) plus k x -
          continuousFullRegressionCoefficient L (trueNuisance M L) plus k x| ≤ D * |t|) ∧
      (∀ a, ∀ᵐ x ∂xLaw M,
        |(e t).piLev a x - (trueNuisance M L).piLev a x| ≤ C * |t|)) :
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z, w o.1 * psiFullJ L (e t) k o
      ∂observationLaw M) 0 0 := by
  haveI : IsProbabilityMeasure (observationLaw M) := by
    unfold observationLaw
    exact Measure.isProbabilityMeasure_map
      (M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))).aemeasurable
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  have iw : Integrable w (xLaw M) :=
    Integrable.of_bound hw.aestronglyMeasurable B hwB
  have ht0 := hlocal.self_of_nhds
  have hm0 (plus : Bool) : Measurable
      (continuousFullRegressionCoefficient L (trueNuisance M L) plus k) := by
    rw [← he0]
    exact ht0.2.2.1 plus
  have hpim (t : ℝ) (ht : ∀ a, Measurable ((e t).piLev a)) (i : ℕ) :
      Measurable (positiveValue (e t).piLev i) := by
    first | fun_prop | skip
    unfold positiveValue
    split_ifs
    · exact ht _
    · fun_prop
  have hpi0 (i : ℕ) : Measurable (positiveValue (trueNuisance M L).piLev i) := by
    rw [← he0]
    exact hpim 0 ht0.1 i
  let F : ℝ → Obs X Z → ℝ := fun t o =>
    w o.1 * contFullJ L (trueNuisance M L) k o.1 +
      (w o.1 * (continuousFullRegressionCoefficient L (e t) true k o.1 -
        continuousFullRegressionCoefficient L (trueNuisance M L) true k o.1)) *
        (1 - positiveValue (trueNuisance M L).piLev (k+1) o.1 /
          positiveValue (e t).piLev (k+1) o.1) -
      (w o.1 * (continuousFullRegressionCoefficient L (e t) false k o.1 -
        continuousFullRegressionCoefficient L (trueNuisance M L) false k o.1)) *
        (1 - positiveValue (trueNuisance M L).piLev k o.1 /
          positiveValue (e t).piLev k o.1)
  have hF0 : F 0 = fun o => w o.1 * contFullJ L (trueNuisance M L) k o.1 := by
    funext o
    simp only [F, he0, sub_self, mul_zero, zero_mul, add_zero, sub_zero]
  have iF0 : Integrable (F 0) (observationLaw M) := by
    rw [hF0]
    exact population_contFullJ_weighted_integrable M h he q L hL k w hw iw
  have hnear : ∀ᶠ t : ℝ in 𝓝 0,
      AEStronglyMeasurable (F t) (observationLaw M) ∧
      ∀ᵐ o ∂observationLaw M, |F t o - F 0 o| ≤ (2 * (B * D * C / c)) * t^2 := by
    filter_upwards [hlocal] with t ht
    have hmt (plus : Bool) := ht.2.2.1 plus
    have hpit (i : ℕ) := hpim t ht.1 i
    have hj := population_continuous_full_J_measurable M h.2.2.2.1 q L hL k
    have hFm : Measurable (F t) := by
      dsimp only [F]
      fun_prop
    refine ⟨hFm.aestronglyMeasurable, ?_⟩
    have hbound (plus : Bool) (i : ℕ) (hi : 1 ≤ i ∧ i ≤ L.K) :
        ∀ᵐ x ∂xLaw M, |(w x *
          (continuousFullRegressionCoefficient L (e t) plus k x -
            continuousFullRegressionCoefficient L (trueNuisance M L) plus k x)) *
          (1 - positiveValue (trueNuisance M L).piLev i x /
            positiveValue (e t).piLev i x)| ≤ (B * D * C / c) * t^2 := by
      filter_upwards [hwB, ht.2.1 ⟨i,hi⟩, ht.2.2.2.1 plus,
        ht.2.2.2.2 ⟨i,hi⟩] with x hx hclip ha hd
      simp only [positiveValue, dif_pos hi]
      exact continuous_full_coefficient_reciprocal_defect_bound _ _ _ _ _ D C B t c
        hc hclip ha hd (by simpa only [Real.norm_eq_abs] using hx) hD hC
    have hp := hbound true (k+1) (by omega)
    have hm : ∀ᵐ x ∂xLaw M, |(w x *
        (continuousFullRegressionCoefficient L (e t) false k x -
          continuousFullRegressionCoefficient L (trueNuisance M L) false k x)) *
        (1 - positiveValue (trueNuisance M L).piLev k x /
          positiveValue (e t).piLev k x)| ≤ (B * D * C / c) * t^2 := by
      by_cases hk0 : k.val = 0
      · simp only [continuousFullRegressionCoefficient, Bool.false_eq_true, if_false,
          if_pos hk0, sub_self, mul_zero, zero_mul, abs_zero]
        exact Eventually.of_forall (fun _ => by positivity)
      · exact hbound false k (by omega)
    filter_upwards [observationLaw_covariate_ae M _ hp,
      observationLaw_covariate_ae M _ hm] with o hoP hoM
    rw [hF0]
    dsimp only [F]
    have hid (a b d : ℝ) : a + b - d - a = b - d := by ring
    rw [hid]
    exact (abs_sub _ _).trans (by linarith)
  have hder := integral_local_quadratic_orthogonality (observationLaw M) F
    (2 * (B * D * C / c)) iF0 hnear
  apply hder.congr_of_eventuallyEq
  filter_upwards [hlocal] with t ht
  have hwp (plus : Bool) : Measurable (fun x => w x *
      (continuousFullRegressionCoefficient L (e t) plus k x -
        continuousFullRegressionCoefficient L (trueNuisance M L) plus k x)) := by
    first | fun_prop | exact hw.mul ((ht.2.2.1 plus).sub (hm0 plus))
  have hwbound (plus : Bool) : ∀ᵐ x ∂xLaw M, ‖w x *
      (continuousFullRegressionCoefficient L (e t) plus k x -
        continuousFullRegressionCoefficient L (trueNuisance M L) plus k x)‖ ≤ B * (D * |t|) := by
    filter_upwards [hwB, ht.2.2.2.1 plus] with x hx ha
    simp only [norm_mul, Real.norm_eq_abs] at hx ⊢
    exact mul_le_mul hx ha (abs_nonneg _) hB
  obtain ⟨is, hs⟩ := population_continuous_full_joint_fitted_bias M h he q L hL
    (e t) ht.1 c hc ht.2.1 k w hw iw (hwp true) (hwp false)
    (B * (D * |t|)) (B * (D * |t|)) (hwbound true) (hwbound false)
  have ip (plus : Bool) (i : ℕ) : Integrable (fun o : Obs X Z =>
      (w o.1 * (continuousFullRegressionCoefficient L (e t) plus k o.1 -
        continuousFullRegressionCoefficient L (trueNuisance M L) plus k o.1)) *
        (1 - positiveValue (trueNuisance M L).piLev i o.1 /
          positiveValue (e t).piLev i o.1)) (observationLaw M) := by
    by_cases hi : 1 ≤ i ∧ i ≤ L.K
    · obtain ⟨iz, ir, hz⟩ := population_fitted_normalized_assignment_defect M (L.S i)
        ((e t).piLev ⟨i,hi⟩) _ (ht.1 _) (hwp plus) c (B * (D * |t|)) hc
        (ht.2.1 _) (hwbound plus)
      simpa only [positiveValue, dif_pos hi, trueNuisance, levelSetProb] using ir
    · have hm : Measurable (fun o : Obs X Z => w o.1 *
          (continuousFullRegressionCoefficient L (e t) plus k o.1 -
            continuousFullRegressionCoefficient L (trueNuisance M L) plus k o.1)) :=
        (hwp plus).comp measurable_fst
      simpa only [positiveValue, dif_neg hi, zero_div, sub_zero, mul_one] using
        Integrable.of_bound hm.aestronglyMeasurable (B * (D * |t|))
          (observationLaw_covariate_ae M _ (hwbound plus))
  dsimp only [F]
  have ib : Integrable (fun o : Obs X Z => w o.1 *
      contFullJ L (trueNuisance M L) k o.1) (observationLaw M) := by
    simpa only [hF0] using iF0
  rw [integral_sub (ib.fun_add (ip true (k+1))) (ip false k),
    integral_add ib (ip true (k+1))]
  exact hs

end Papers.TbsPrteOptimalTransport
