module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousBandProductBias
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationAssignmentResidual
/-! Population means of continuous band product corrections.
The finite instrument tower identity removes the centered assignment event.
With a common fitted gamma, changes of the band target leave only a product
of nuisance errors in addition to the weighted component-score difference. -/
public section
set_option linter.style.haveILetI false
set_option linter.style.openClassical false
set_option linter.unusedFintypeInType false
set_option linter.unusedTactic false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: fitted_continuous_band_event_mean
/-- For [an admissible nuisance](hyp:he), [the policy-event indicator times a
fitted band target is integrable, and its observation mean equals the covariate
mean of the true policy-event probability times that target](goal). -/
lemma fitted_continuous_band_event_mean (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e) (k j b : ℕ) :
    Integrable (fun o : Obs X Z => indicator (o.2.1 ∈ policyUnion L k j) *
      contJ L e k b o.1) (observationLaw M) ∧
    (∫ o : Obs X Z, indicator (o.2.1 ∈ policyUnion L k j) *
      contJ L e k b o.1 ∂observationLaw M) =
      ∫ x, gamma M L k j x * contJ L e k b x ∂xLaw M := by
  cases Subsingleton.elim ‹DecidableEq Z› (fun a b => Classical.propDecidable (a = b))
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  have hi := (fitted_continuous_band_event_memLp M L e he k j b).integrable (by norm_num)
  have hj := fitted_contJ_measurable M L e he k b
  let f : Z × X → ℝ := fun zx =>
    indicator (zx.1 ∈ policyUnion L k j) * contJ L e k b zx.2
  have hf : Measurable f := by
    dsimp only [f]
    fun_prop
  have hs (x : X) : (∑ z, instProb M z x * f (z, x)) =
      gamma M L k j x * contJ L e k b x := by
    simp only [f, ← mul_assoc, ← Finset.sum_mul, indicator, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    rfl
  exact ⟨hi, by simpa only [hs, f] using population_instrument_integral M f hf hi⟩

-- @node: fitted_continuous_band_share_correction_mean
/-- For [an admissible nuisance](hyp:he), [a treatment index no larger than the
maximum level](hyp:hk), and [a band index between one and the number of bands
at that level](hyp:hj), [the fitted band target times the policy-event indicator
minus the fitted assignment share is integrable, and its mean equals the
covariate mean of that target times the true share minus the fitted share](goal). -/
lemma fitted_continuous_band_share_correction_mean (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e) (k j : ℕ)
    (hk : k ≤ L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    Integrable (fun o : Obs X Z => contJ L e k (j-1) o.1 *
      (indicator (o.2.1 ∈ policyUnion L k j) - regularValue e.gamma k j o.1))
      (observationLaw M) ∧
    (∫ o : Obs X Z, contJ L e k (j-1) o.1 *
      (indicator (o.2.1 ∈ policyUnion L k j) - regularValue e.gamma k j o.1)
      ∂observationLaw M) =
      ∫ x, contJ L e k (j-1) x *
        (gamma M L k j x - regularValue e.gamma k j x) ∂xLaw M := by
  cases Subsingleton.elim ‹DecidableEq Z› (fun a b => Classical.propDecidable (a = b))
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  let g : RegularIndex L := ⟨(k,j), hk, hj⟩
  obtain ⟨hi, hm⟩ := fitted_continuous_band_event_mean M L e he k j (j-1)
  have hw := (fitted_continuous_gamma_contJ_memLp M L e he g k (j-1)).integrable
    (by norm_num)
  have hjm := fitted_contJ_measurable M L e he k (j-1)
  have hgm : Measurable (e.gamma g) := by
    first | fun_prop | skip
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hm, _⟩
    exact hm g
  have htrue : MemLp (gamma M L k j) 2 (xLaw M) := by
    apply MemLp.of_bound (by
      first | fun_prop | exact (population_instrument_set_probability_measurable M
        (policyUnion L k j)).aestronglyMeasurable) 1
    filter_upwards [] with x
    change ‖∑ z ∈ policyUnion L k j, instProb M z x‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg
      (population_instrument_set_probability_range M (policyUnion L k j) x).1]
    exact (population_instrument_set_probability_range M (policyUnion L k j) x).2
  have htg : Integrable (fun x => gamma M L k j x * contJ L e k (j-1) x) (xLaw M) :=
    htrue.integrable_mul (fitted_contJ_memLp M L e he k (j-1))
  have hfg : Integrable (fun x => e.gamma g x * contJ L e k (j-1) x) (xLaw M) := by
    exact (observationLaw_fst_measurePreserving M).integrable_comp
      (hgm.mul hjm).aestronglyMeasurable |>.mp hw
  have hwi := observationLaw_covariate_integral M
    (fun x => e.gamma g x * contJ L e k (j-1) x) (by fun_prop)
  have hidx : regularValue e.gamma k j = e.gamma g := by
    funext x
    simp only [regularValue, dif_pos (show k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from ⟨hk,hj⟩)]
    rfl
  rw [hidx]
  have hid : (fun o : Obs X Z => contJ L e k (j-1) o.1 *
      (indicator (o.2.1 ∈ policyUnion L k j) - e.gamma g o.1)) =
      (fun o => indicator (o.2.1 ∈ policyUnion L k j) * contJ L e k (j-1) o.1 -
        e.gamma g o.1 * contJ L e k (j-1) o.1) := by
    funext o; ring
  refine ⟨by rw [hid]; exact hi.sub' hw, ?_⟩
  rw [hid, integral_sub hi hw, hm, hwi, ← integral_sub htg hfg]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

-- @node: continuous_band_product_fixed_gamma_difference_mean
/-- Suppose [both nuisances are admissible](hyp:he,hb), [their assignment shares
coincide](hyp:hg), [the treatment index does not exceed the maximum](hyp:hk),
and [the band index lies between one and the level's band count](hyp:hj).
If [the common-share-weighted component-score difference is integrable](hyp:hi),
then [the product-score difference is integrable and its mean equals the mean
of that weighted component-score difference plus the covariate mean of the
band-target difference times the true share minus the common fitted share](goal). -/
lemma continuous_band_product_fixed_gamma_difference_mean
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e b : NuisanceCont L)
    (he : ContAdmissible M L e) (hb : ContAdmissible M L b)
    (hg : e.gamma = b.gamma) (k j : ℕ)
    (hk : k ≤ L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (hi : Integrable (fun o : Obs X Z => regularValue e.gamma k j o.1 *
      (contScoreComponents M phi dphi L e k (j-1) o -
        contScoreComponents M phi dphi L b k (j-1) o)) (observationLaw M)) :
    Integrable (fun o => psiProd M phi dphi L e k j o -
      psiProd M phi dphi L b k j o) (observationLaw M) ∧
    (∫ o, psiProd M phi dphi L e k j o - psiProd M phi dphi L b k j o
      ∂observationLaw M) =
      (∫ o : Obs X Z, regularValue e.gamma k j o.1 *
        (contScoreComponents M phi dphi L e k (j-1) o -
          contScoreComponents M phi dphi L b k (j-1) o) ∂observationLaw M) +
      ∫ x, (contJ L e k (j-1) x - contJ L b k (j-1) x) *
        (gamma M L k j x - regularValue e.gamma k j x) ∂xLaw M := by
  cases Subsingleton.elim ‹DecidableEq Z› (fun a b => Classical.propDecidable (a = b))
  obtain ⟨ie, me⟩ := fitted_continuous_band_share_correction_mean M L e he k j hk hj
  obtain ⟨ib, mb⟩ := fitted_continuous_band_share_correction_mean M L b hb k j hk hj
  rw [← hg] at ib mb
  have hres := ie.sub' ib
  have heq (o : Obs X Z) := continuous_band_product_fixed_gamma_difference
    M phi dphi L e b hg k j o
  have hid : (fun o : Obs X Z => psiProd M phi dphi L e k j o -
      psiProd M phi dphi L b k j o) =
      (fun o => regularValue e.gamma k j o.1 *
        (contScoreComponents M phi dphi L e k (j-1) o -
          contScoreComponents M phi dphi L b k (j-1) o) +
        (contJ L e k (j-1) o.1 *
          (indicator (o.2.1 ∈ policyUnion L k j) - regularValue e.gamma k j o.1) -
        contJ L b k (j-1) o.1 *
          (indicator (o.2.1 ∈ policyUnion L k j) - regularValue e.gamma k j o.1))) := by
    funext o
    rw [heq]
    ring
  have hgmeas : Measurable (regularValue e.gamma k j) := by
    first | fun_prop | skip
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hm, _⟩
    change Measurable (fun x => regularValue e.gamma k j x)
    simpa only [regularValue, dif_pos (show k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from ⟨hk,hj⟩)]
      using hm ⟨(k,j),hk,hj⟩
  have hgb : ∀ᵐ x ∂xLaw M, ‖gamma M L k j x - regularValue e.gamma k j x‖ ≤ 2 := by
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hb, _⟩
    filter_upwards [hb ⟨(k,j),hk,hj⟩] with x hx
    have ht : gamma M L k j x ∈ Icc (0 : ℝ) 1 :=
      population_instrument_set_probability_range M (policyUnion L k j) x
    rw [Real.norm_eq_abs, regularValue, dif_pos (show k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from ⟨hk,hj⟩)]
    exact (abs_sub _ _).trans (by
      rw [abs_of_nonneg ht.1, abs_of_nonneg hx.1]; change _ ≤ _; linarith [ht.2, hx.2])
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  have iw (a : NuisanceCont L) (ha : ContAdmissible M L a) :=
    ((fitted_contJ_memLp M L a ha k (j-1)).integrable (by norm_num)).mul_bdd
      (by
        first | fun_prop | exact ((population_instrument_set_probability_measurable M
          (policyUnion L k j)).sub hgmeas).aestronglyMeasurable) hgb
  rw [hid]
  refine ⟨hi.fun_add hres, ?_⟩
  rw [integral_add hi hres, integral_sub ie ib, me, mb,
    ← integral_sub (iw e he) (iw b hb)]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  ring

-- @node: continuous_band_product_target_difference_cross_bound
/-- If [the true nuisance is admissible](hyp:he0), [both comparison nuisances
are admissible](hyp:he,hb), [the treatment index is at most the maximum](hyp:hk),
and [the band index is between one and the level's band count](hyp:hj), then
[the band-target difference times the true share minus the first fitted share
is integrable, and its absolute mean is at most the first share's L² error
times the L² norm of the band-target difference](goal). -/
lemma continuous_band_product_target_difference_cross_bound
    (L : LevelData Z X) (e b : NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (he : ContAdmissible M L e) (hb : ContAdmissible M L b)
    (k j : ℕ) (hk : k ≤ L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    Integrable (fun x => (contJ L e k (j-1) x - contJ L b k (j-1) x) *
      (gamma M L k j x - regularValue e.gamma k j x)) (xLaw M) ∧
    |∫ x, (contJ L e k (j-1) x - contJ L b k (j-1) x) *
      (gamma M L k j x - regularValue e.gamma k j x) ∂xLaw M| ≤
      finiteL2Error M (regularValue e.gamma k j) (regularValue (trueNuisance M L).gamma k j) *
        finiteL2Error M (fun x => contJ L e k (j-1) x - contJ L b k (j-1) x) (fun _ => 0) := by
  cases Subsingleton.elim ‹DecidableEq Z› (fun a b => Classical.propDecidable (a = b))
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  have hg (a : NuisanceCont L) (ha : ContAdmissible M L a) :
      MemLp (regularValue a.gamma k j) 2 (xLaw M) := by
    have hm : Measurable (regularValue a.gamma k j) := by
      first | fun_prop | skip
      rcases ha with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hm, _⟩
      change Measurable (fun x => regularValue a.gamma k j x)
      simpa only [regularValue, dif_pos (show k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from ⟨hk,hj⟩)]
        using hm ⟨(k,j),hk,hj⟩
    apply MemLp.of_bound hm.aestronglyMeasurable 1
    rcases ha with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hb, _⟩
    filter_upwards [hb ⟨(k,j),hk,hj⟩] with x hx
    simp only [regularValue, dif_pos (show k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from ⟨hk,hj⟩)]
    rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
    exact hx.2
  have hgd := (hg e he).sub (hg _ he0)
  have hJ := (fitted_contJ_memLp M L e he k (j-1)).sub
    (fitted_contJ_memLp M L b hb k (j-1))
  have htrue (x : X) : regularValue (trueNuisance M L).gamma k j x =
      gamma M L k j x := by
    simp only [regularValue, trueNuisance,
      dif_pos (show k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from ⟨hk,hj⟩)]
  have hid : (fun x => (contJ L e k (j-1) x - contJ L b k (j-1) x) *
      (gamma M L k j x - regularValue e.gamma k j x)) =
      (fun x => -((regularValue e.gamma k j x -
        regularValue (trueNuisance M L).gamma k j x) *
        (contJ L e k (j-1) x - contJ L b k (j-1) x))) := by
    funext x
    rw [htrue]
    ring
  rw [hid]
  refine ⟨(hgd.integrable_mul hJ).neg, ?_⟩
  rw [integral_neg, abs_neg, l2Error_eq_eLpNorm M _ _ hgd]
  have hJ0 : MemLp (fun x => (contJ L e k (j-1) x - contJ L b k (j-1) x) - 0)
      2 (xLaw M) := by simpa only [sub_zero, Pi.sub_def] using hJ
  rw [l2Error_eq_eLpNorm M _ _ hJ0]
  simp only [sub_zero]
  calc
    _ ≤ ∫ x, |(regularValue e.gamma k j x -
        regularValue (trueNuisance M L).gamma k j x) *
        (contJ L e k (j-1) x - contJ L b k (j-1) x)| ∂xLaw M := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x => (regularValue e.gamma k j x -
          regularValue (trueNuisance M L).gamma k j x) *
          (contJ L e k (j-1) x - contJ L b k (j-1) x))
    _ ≤ _ := by
      simpa only [Pi.sub_def] using
        Causalean.Stat.integral_abs_mul_le_eLpNorm_mul_eLpNorm hgd hJ

-- The hybrid band target has the same population limit as the fitted target.
-- Its difference therefore has a quarter-power rate, and the remaining
-- assignment correction is a second-order product at root-n scale.
-- @node: encoded_continuous_band_target_difference_cross_root_n_negligible
/-- Suppose [the true nuisance is admissible](hyp:he0), [every fit in each of
the two sequences is admissible](hyp:heh,hbh), and [both sequences have encoded
little-o fourth-root error rates relative to truth](hyp:hre,hrb). For [a
treatment index at most the maximum](hyp:hk) and [a band index between one and
the level's band count](hyp:hj), [the covariate mean of the two fitted targets'
difference times the true share minus the first fitted share, using fits at
size twice n plus two and scaled by the square root of n plus one, converges
to zero in probability](goal). -/
lemma encoded_continuous_band_target_difference_cross_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (eh bh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hbh : ∀ n a, ContAdmissible M L (bh n a))
    (hre : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (hrb : FiniteNuisanceRates M μ (fun n a => contComponent M L (bh n a))
      (contComponent M L (trueNuisance M L)))
    (k j : ℕ) (hk : k ≤ L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        ∫ x, (contJ L (eh (2*(n+1)) a) k (j-1) x -
          contJ L (bh (2*(n+1)) a) k (j-1) x) *
          (gamma M L k j x - regularValue (eh (2*(n+1)) a).gamma k j x) ∂xLaw M)
      atTop (fun _ _ => 0) := by
  let J := fun (e : NuisanceCont L) (_ : Unit) => contJ L e k (j-1)
  have hrJ (fh : ℕ → A → NuisanceCont L) (hf : ∀ n a, ContAdmissible M L (fh n a))
      (hrf : FiniteNuisanceRates M μ (fun n a => contComponent M L (fh n a))
        (contComponent M L (trueNuisance M L))) :
      FiniteNuisanceRates M μ (fun n a => J (fh n a)) (J (trueNuisance M L)) := by
    intro i
    exact encoded_continuous_contJ_quarter_rate M μ L _ fh he0 hf hrf (k,j-1)
  have hm (e : NuisanceCont L) (he : ContAdmissible M L e) (_ : Unit) :=
    fitted_contJ_memLp M L e he k (j-1)
  have hdiff := nuisanceRates_sub M μ
    (fun n a => J (eh n a)) (fun n a => J (bh n a))
    (J (trueNuisance M L)) (J (trueNuisance M L))
    (fun n a => hm _ (heh n a)) (fun n a => hm _ (hbh n a))
    (hm _ he0) (hm _ he0) (hrJ eh heh hre) (hrJ bh hbh hrb)
  have hrD : Causalean.Stat.IsLittleOp
      (fun n a => finiteL2Error M
        (fun x => contJ L (eh (2*(n+1)) a) k (j-1) x -
          contJ L (bh (2*(n+1)) a) k (j-1) x) (fun _ => 0))
      (fun n => ((2*(n+1) : ℕ) : ℝ)^(-1/4 : ℝ)) μ := by
    simpa only [J, finiteL2Error, sub_self] using hdiff ()
  let z0 : Z := Classical.choice inferInstance
  have hrG : Causalean.Stat.IsLittleOp
      (fun n a => finiteL2Error M (regularValue (eh (2*(n+1)) a).gamma k j)
        (regularValue (trueNuisance M L).gamma k j))
      (fun n => ((2*(n+1) : ℕ) : ℝ)^(-1/4 : ℝ)) μ := by
    simpa only [finiteL2Error, contComponent] using hre (6,k,j,z0)
  apply dml_root_n_bias_tendsto_probability μ
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul one_pos
    (dml_quarter_rate_product μ _ _ hrG hrD)
  intro n a
  rw [one_mul]
  exact (continuous_band_product_target_difference_cross_bound M L _ _ he0
    (heh _ a) (hbh _ a) k j hk hj).2.trans (le_abs_self _)

end Papers.TbsPrteOptimalTransport
