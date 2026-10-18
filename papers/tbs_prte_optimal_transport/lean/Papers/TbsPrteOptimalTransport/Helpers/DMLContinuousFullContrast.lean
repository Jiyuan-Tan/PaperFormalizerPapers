module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousComponentBridge
public import Papers.TbsPrteOptimalTransport.Helpers.DMLFiniteFullScoreConvergence
/-! Second moments and convergence of the fitted continuous full-interval contrast.
The two propensity times outcome-mean products are controlled separately by
clipping and the original componentwise nuisance rates. -/
public section
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.unnecessarySimpa false
set_option linter.unreachableTactic false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
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

-- @node: fitted_continuous_full_coordinates
/-- For [admissible continuous nuisances](hyp:he), [the extended treatment
probability and the two full-interval outcome means are measurable; almost
everywhere under the covariate distribution, the probability has absolute value
at most one and each mean has absolute value at most the larger absolute outcome
endpoint](goal). -/
lemma fitted_continuous_full_coordinates (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e) (k : ℕ) :
    (Measurable (fun x => positiveValue e.pLev k x) ∧
      ∀ᵐ x ∂xLaw M, |positiveValue e.pLev k x| ≤ 1) ∧
    (Measurable (fun x => fullValue e.JfullPlus k x) ∧
      ∀ᵐ x ∂xLaw M, |fullValue e.JfullPlus k x| ≤ max |M.yMin| |M.yMax|) ∧
    (Measurable (fun x => minusFullValue e k x) ∧
      ∀ᵐ x ∂xLaw M, |minusFullValue e k x| ≤ max |M.yMin| |M.yMax|) := by
  rcases he with ⟨_, _, hp, hpm, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, hjp, hjpm, hjm, hjmm, _⟩
  have hb {r : ℝ} (hr : r ∈ Icc M.yMin M.yMax) :
      |r| ≤ max |M.yMin| |M.yMax| := by
    apply abs_le.mpr
    constructor
    · exact (neg_le_neg (le_max_left _ _)).trans ((neg_abs_le _).trans hr.1)
    · exact hr.2.trans ((le_abs_self _).trans (le_max_right _ _))
  have hB : 0 ≤ max |M.yMin| |M.yMax| := (abs_nonneg _).trans (le_max_left _ _)
  refine ⟨?_, ?_, ?_⟩
  · by_cases hk : 1 ≤ k ∧ k ≤ L.K
    · simp only [positiveValue, dif_pos hk]
      refine ⟨?_, ?_⟩
      · first | fun_prop | exact hpm ⟨k, hk⟩
      · filter_upwards [hp ⟨k, hk⟩] with x hx
        rw [abs_of_nonneg hx.1]
        exact hx.2
    · simp only [positiveValue, dif_neg hk]
      exact ⟨by fun_prop, Eventually.of_forall (fun _ => by norm_num)⟩
  · by_cases hk : k < L.K
    · simp only [fullValue, dif_pos hk]
      exact ⟨by first | fun_prop | exact hjpm ⟨k, hk⟩,
        (hjp ⟨k, hk⟩).mono (fun _ hx => hb hx)⟩
    · simp only [fullValue, dif_neg hk]
      exact ⟨by fun_prop, Eventually.of_forall (fun _ => by simpa using hB)⟩
  · by_cases hk : 1 ≤ k ∧ k < L.K
    · simp only [minusFullValue, dif_pos hk]
      exact ⟨by first | fun_prop | exact hjmm ⟨k, hk⟩,
        (hjm ⟨k, hk⟩).mono (fun _ hx => hb hx)⟩
    · simp only [minusFullValue, dif_neg hk]
      exact ⟨by fun_prop, Eventually.of_forall (fun _ => by simpa using hB)⟩

-- @node: fitted_continuous_full_product_memLp
/-- For [admissible continuous nuisances](hyp:he), [the product of the extended
treatment probability and the full-interval outcome mean on the selected upper
or lower side has a finite second moment under the covariate distribution](goal). -/
lemma fitted_continuous_full_product_memLp (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e) (plus : Bool) (k : ℕ) :
    MemLp (fun x => positiveValue e.pLev (if plus then k + 1 else k) x *
      (if plus then fullValue e.JfullPlus k x else minusFullValue e k x))
      2 (xLaw M) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  have hp := (fitted_continuous_full_coordinates M L e he (if plus then k + 1 else k)).1
  have hj := (fitted_continuous_full_coordinates M L e he k).2
  have hm : Measurable (fun x => if plus then fullValue e.JfullPlus k x
      else minusFullValue e k x) := by cases plus <;> simp only [Bool.false_eq_true,
        Bool.true_eq, if_false, if_true] <;> first | fun_prop | exact hj.2.1 | exact hj.1.1
  apply MemLp.of_bound (by first | fun_prop | exact (hp.1.mul hm).aestronglyMeasurable) (max |M.yMin| |M.yMax|)
  have hb : ∀ᵐ x ∂xLaw M, |if plus then fullValue e.JfullPlus k x
      else minusFullValue e k x| ≤ max |M.yMin| |M.yMax| := by
    cases plus
    · simpa using hj.2.2
    · simpa using hj.1.2
  filter_upwards [hp.2, hb] with x hx hy
  rw [Real.norm_eq_abs, abs_mul]
  exact (mul_le_mul hx hy (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

-- @node: fitted_contFullJ_memLp
/-- For [admissible continuous nuisances](hyp:he), [the full-interval contrast
between the upper and lower treatment-probability-weighted outcome means has a
finite second moment under the covariate distribution](goal). -/
lemma fitted_contFullJ_memLp (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e) (k : ℕ) :
    MemLp (fun x => contFullJ L e k x) 2 (xLaw M) := by
  convert (fitted_continuous_full_product_memLp M L e he true k).sub
    (fitted_continuous_full_product_memLp M L e he false k) using 1
  funext x
  simp only [contFullJ, Pi.sub_apply, Bool.true_eq, Bool.false_eq_true, if_true, if_false]


-- @node: nuisanceRates_continuous_full_values
/-- If [the fitted treatment probabilities satisfy the componentwise nuisance
rates](hyp:hrp), as do [the upper full-interval means](hyp:hrplus) and [the lower
full-interval means](hyp:hrminus), then [the corresponding extended treatment
probabilities and upper and lower full-interval means satisfy those same rates
relative to their reference values](goal). -/
lemma nuisanceRates_continuous_full_values {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (L : LevelData Z X) (e0 : NuisanceCont L)
    (eh : ℕ → A → NuisanceCont L)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrplus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullPlus) e0.JfullPlus)
    (hrminus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullMinus) e0.JfullMinus) :
    FiniteNuisanceRates M μ (fun n a k => positiveValue (eh n a).pLev k)
      (fun k => positiveValue e0.pLev k) ∧
    FiniteNuisanceRates M μ (fun n a k x => fullValue (eh n a).JfullPlus k x)
      (fun k x => fullValue e0.JfullPlus k x) ∧
    FiniteNuisanceRates M μ (fun n a k x => minusFullValue (eh n a) k x)
      (fun k x => minusFullValue e0 k x) := by
  have hz := maxErrors_isLittleOp μ ([] : List Unit) (fun _ _ _ => (0 : ℝ))
    (fun n => ((2*(n+1) : ℕ) : ℝ) ^ (-1/4 : ℝ))
    (fun _ => Real.rpow_pos_of_pos (by positivity) _) (by simp)
  refine ⟨nuisanceRates_positiveValue M μ L.K _ _ hrp, ?_, ?_⟩
  · intro k
    by_cases hk : k < L.K
    · simpa only [fullValue, dif_pos hk] using hrplus ⟨k, hk⟩
    · simpa only [fullValue, dif_neg hk, finiteL2Error, sub_self, zero_pow (by norm_num : 2 ≠ 0),
        integral_zero, Real.sqrt_zero, List.map_nil, maxErrors, List.foldr_nil] using hz
  · intro k
    by_cases hk : 1 ≤ k ∧ k < L.K
    · simpa only [minusFullValue, dif_pos hk] using hrminus ⟨k, hk⟩
    · simpa only [minusFullValue, dif_neg hk, finiteL2Error, sub_self, zero_pow (by norm_num : 2 ≠ 0),
        integral_zero, Real.sqrt_zero, List.map_nil, maxErrors, List.foldr_nil] using hz

-- @node: nuisanceRates_xLaw_sq_tendsto_probability_zero
/-- If [the fitted covariate functions satisfy the componentwise nuisance rates
relative to their reference functions](hyp:hr), then [for the selected coordinate,
the covariate-integrated squared error at sample sizes twice the half-sample
size converges in probability to zero](goal). -/
lemma nuisanceRates_xLaw_sq_tendsto_probability_zero {A C : Type*}
    [MeasurableSpace A] (μ : Measure A) (fit : ℕ → A → C → X → ℝ)
    (truth : C → X → ℝ) (hr : FiniteNuisanceRates M μ fit truth) (c : C) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, (fit (2 * (n + 1)) a c x - truth c x) ^ 2 ∂xLaw M)
      atTop (fun _ _ => 0) := by
  have hs : Continuous (fun t : ℝ => t ^ 2) := by fun_prop
  have hh := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    hs.continuousAt (dml_quarter_rate_tendsto_probability_zero μ _ (hr c))
  simpa only [finiteL2Error, Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _),
    zero_pow (by norm_num : 2 ≠ 0)] using hh

-- @node: nuisanceRates_contFullJ_sq_tendsto_probability_zero
/-- If [the reference nuisances are admissible](hyp:he0), [all fitted nuisances
are admissible](hyp:heh), and the componentwise nuisance rates hold for [treatment
probabilities](hyp:hrp), [upper full-interval means](hyp:hrplus), and [lower
full-interval means](hyp:hrminus), then [the covariate-integrated squared error
of the fitted full-interval contrast at twice the half-sample size converges in
probability to zero](goal). -/
lemma nuisanceRates_contFullJ_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrplus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullPlus) e0.JfullPlus)
    (hrminus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullMinus) e0.JfullMinus)
    (k : ℕ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, (contFullJ L (eh (2 * (n + 1)) a) k x -
        contFullJ L e0 k x) ^ 2 ∂xLaw M) atTop (fun _ _ => 0) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  obtain ⟨hp, hjp, hjm⟩ := nuisanceRates_continuous_full_values M μ L e0 eh hrp hrplus hrminus
  let P := fun (e : NuisanceCont L) (b : Bool) x =>
    positiveValue e.pLev (if b then k + 1 else k) x
  let J := fun (e : NuisanceCont L) (b : Bool) x =>
    if b then fullValue e.JfullPlus k x else minusFullValue e k x
  have hP (e : NuisanceCont L) (he : ContAdmissible M L e) (b : Bool) :
      Measurable (P e b) ∧ ∀ᵐ x ∂xLaw M, |P e b x| ≤ 1 :=
    (fitted_continuous_full_coordinates M L e he (if b then k + 1 else k)).1
  have hJ (e : NuisanceCont L) (he : ContAdmissible M L e) (b : Bool) :
      Measurable (J e b) ∧ ∀ᵐ x ∂xLaw M, |J e b x| ≤ max |M.yMin| |M.yMax| := by
    have hh := (fitted_continuous_full_coordinates M L e he k).2
    cases b
    · simpa only [J, Bool.false_eq_true, if_false] using hh.2
    · simpa only [J, Bool.true_eq, if_true] using hh.1
  have hPLp (e : NuisanceCont L) (he : ContAdmissible M L e) (b : Bool) :
      MemLp (P e b) 2 (xLaw M) :=
    MemLp.of_bound (hP e he b).1.aestronglyMeasurable 1 (by
      simpa only [Real.norm_eq_abs] using (hP e he b).2)
  have hJLp (e : NuisanceCont L) (he : ContAdmissible M L e) (b : Bool) :
      MemLp (J e b) 2 (xLaw M) :=
    MemLp.of_bound (hJ e he b).1.aestronglyMeasurable _ (by
      simpa only [Real.norm_eq_abs] using (hJ e he b).2)
  have hprod (b : Bool) : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, (P (eh (2 * (n + 1)) a) b x * J (eh (2 * (n + 1)) a) b x -
        P e0 b x * J e0 b x) ^ 2 ∂xLaw M) atTop (fun _ _ => 0) := by
    apply dml_weighted_residual_sq_tendsto_probability_zero μ (xLaw M)
      (P e0 b) (J e0 b) (fun n a => P (eh (2 * (n + 1)) a) b)
      (fun n a => J (eh (2 * (n + 1)) a) b) 1 (max |M.yMin| |M.yMax|)
      (hP e0 he0 b).1 (hJ e0 he0 b).1
      (fun n a => (hP _ (heh _ a) b).1) (fun n a => (hJ _ (heh _ a) b).1)
      (fun n a => (hPLp _ (heh _ a) b).sub (hPLp e0 he0 b))
      (fun n a => (hJLp _ (heh _ a) b).sub (hJLp e0 he0 b))
      (fun n a => (hP _ (heh _ a) b).2) (fun _ _ => (hJ e0 he0 b).2)
    · exact nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hp
        (if b then k + 1 else k)
    · cases b
      · exact nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hjm k
      · exact nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hjp k
  have hs := dml_three_term_sq_tendsto_probability_zero μ (xLaw M)
    (fun n a x => P (eh (2 * (n + 1)) a) true x * J (eh (2 * (n + 1)) a) true x -
      P e0 true x * J e0 true x) (fun _ _ _ => 0)
    (fun n a x => P (eh (2 * (n + 1)) a) false x * J (eh (2 * (n + 1)) a) false x -
      P e0 false x * J e0 false x)
    (fun n a => (fitted_continuous_full_product_memLp M L _ (heh _ a) true k).sub
      (fitted_continuous_full_product_memLp M L e0 he0 true k))
    (fun _ _ => MemLp.zero')
    (fun n a => (fitted_continuous_full_product_memLp M L _ (heh _ a) false k).sub
      (fitted_continuous_full_product_memLp M L e0 he0 false k))
    (hprod true) (by
      simpa [positiveValue] using (nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _
        (nuisanceRates_positiveValue M μ L.K _ _ hrp) 0)) (hprod false)
  have hid (n : ℕ) (a : A) (x : X) :
      contFullJ L (eh (2 * (n + 1)) a) k x - contFullJ L e0 k x =
      (P (eh (2 * (n + 1)) a) true x * J (eh (2 * (n + 1)) a) true x -
        P e0 true x * J e0 true x) + 0 -
      (P (eh (2 * (n + 1)) a) false x * J (eh (2 * (n + 1)) a) false x -
        P e0 false x * J e0 false x) := by
    simp only [contFullJ, P, J, Bool.true_eq, Bool.false_eq_true, if_true, if_false]
    ring
  simpa only [hid] using hs

-- @node: nuisanceRates_contFullJ_l2_tendsto_probability_zero
/-- Under [admissibility of the reference nuisances](hyp:he0) and [every fitted
nuisance vector](hyp:heh), and componentwise nuisance rates for [treatment
probabilities](hyp:hrp), [upper full-interval means](hyp:hrplus), and [lower
full-interval means](hyp:hrminus), [the root mean squared covariate error of the
fitted full-interval contrast at twice the half-sample size converges in
probability to zero](goal). -/
lemma nuisanceRates_contFullJ_l2_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrplus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullPlus) e0.JfullPlus)
    (hrminus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullMinus) e0.JfullMinus)
    (k : ℕ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => finiteL2Error M (contFullJ L (eh (2 * (n + 1)) a) k)
        (contFullJ L e0 k)) atTop (fun _ _ => 0) := by
  have hs := nuisanceRates_contFullJ_sq_tendsto_probability_zero M μ L e0 eh
    he0 heh hrp hrplus hrminus k
  have hc : Continuous (fun t : ℝ => Real.sqrt t) := by fun_prop
  simpa only [finiteL2Error, Real.sqrt_zero] using
    Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt hc.continuousAt hs


-- @node: fitted_contFullJ_measurable
/-- For [admissible continuous nuisances](hyp:he), [the full-interval contrast
between the upper and lower treatment-probability-weighted outcome means is a
measurable function of covariates](goal). -/
@[fun_prop] lemma fitted_contFullJ_measurable (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e) (k : ℕ) :
    Measurable (contFullJ L e k) := by
  first | fun_prop | skip
  have hp := fitted_continuous_full_coordinates M L e he (k + 1)
  have hm := fitted_continuous_full_coordinates M L e he k
  exact (hp.1.1.mul hm.2.1.1).sub (hm.1.1.mul hm.2.2.1)

-- The assignment-event contrast is bounded by one even for signed weights.
-- @node: fitted_continuous_full_event_memLp
/-- For [admissible continuous nuisances](hyp:he), [the full-interval contrast
multiplied by the difference between the higher-policy and higher-baseline
instrument-event indicators has a finite second moment under the observation
distribution](goal). -/
lemma fitted_continuous_full_event_memLp (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e) (k : ℕ) :
    MemLp (fun o : Obs X Z =>
      (indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k)) *
        contFullJ L e k o.1) 2 (observationLaw M) := by
  have hd := (fitted_contFullJ_memLp M L e he k).comp_measurePreserving
    (observationLaw_fst_measurePreserving M)
  have hj := fitted_contFullJ_measurable M L e he k
  have hev : Measurable (fun o : Obs X Z =>
      indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k)) := by
    fun_prop
  apply hd.norm.mono' (by
    first | fun_prop | exact (hev.mul (hj.comp measurable_fst)).aestronglyMeasurable)
  apply Eventually.of_forall
  intro o
  rw [norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  simp only [Real.norm_eq_abs, indicator]
  split_ifs <;> norm_num

-- @node: nuisanceRates_continuous_full_event_sq_tendsto_probability_zero
/-- If [the reference nuisances are admissible](hyp:he0), [every fitted nuisance
vector is admissible](hyp:heh), and componentwise nuisance rates hold for [treatment
probabilities](hyp:hrp), [upper full-interval means](hyp:hrplus), and [lower
full-interval means](hyp:hrminus), then [the observation-integrated squared error
of the full-interval contrast multiplied by the policy-minus-baseline instrument
indicator converges in probability to zero, with fits evaluated at twice the
half-sample size](goal). -/
lemma nuisanceRates_continuous_full_event_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrplus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullPlus) e0.JfullPlus)
    (hrminus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullMinus) e0.JfullMinus)
    (k : ℕ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        ((indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k)) *
          (contFullJ L (eh (2*(n+1)) a) k o.1 - contFullJ L e0 k o.1)) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  have hs := nuisanceRates_contFullJ_sq_tendsto_probability_zero M μ L e0 eh
    he0 heh hrp hrplus hrminus k
  have hj0 := fitted_contFullJ_measurable M L e0 he0 k
  have hjh (n : ℕ) (a : A) := fitted_contFullJ_measurable M L (eh n a) (heh n a) k
  have hi (n : ℕ) (a : A) := observationLaw_covariate_integral M
    (fun x => (contFullJ L (eh (2*(n+1)) a) k x - contFullJ L e0 k x)^2)
    (by first | fun_prop | exact ((hjh (2*(n+1)) a).sub hj0).pow_const 2)
  have hs' : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        (contFullJ L (eh (2*(n+1)) a) k o.1 - contFullJ L e0 k o.1)^2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
    simpa only [hi] using hs
  apply probability_zero_of_nonneg_le μ _ _ hs'
  intro n
  apply Eventually.of_forall
  intro a
  have hd := ((fitted_contFullJ_memLp M L (eh (2*(n+1)) a) (heh (2*(n+1)) a) k).sub
    (fitted_contFullJ_memLp M L e0 he0 k)).comp_measurePreserving
      (observationLaw_fst_measurePreserving M)
  have hw := (fitted_continuous_full_event_memLp M L (eh (2*(n+1)) a) (heh (2*(n+1)) a) k).sub
    (fitted_continuous_full_event_memLp M L e0 he0 k)
  have hw' : MemLp (fun o : Obs X Z =>
      (indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k)) *
        (contFullJ L (eh (2*(n+1)) a) k o.1 - contFullJ L e0 k o.1))
      2 (observationLaw M) := by
    convert hw using 1
    funext o
    simp only [Pi.sub_apply]
    ring
  refine ⟨integral_nonneg (fun o => sq_nonneg _), ?_⟩
  apply integral_mono hw'.integrable_sq hd.integrable_sq
  intro o
  dsimp only [Function.comp_apply, Pi.sub_apply]
  rw [mul_pow]
  have hb : (indicator (o.2.1 ∈ higherPolicy L k) -
      indicator (o.2.1 ∈ higherBaseline L k)) ^ 2 ≤ 1 := by
    simp only [indicator]
    split_ifs <;> norm_num
  exact mul_le_of_le_one_left (sq_nonneg _) hb

-- @node: nuisanceRates_continuous_full_event_block_sq_tendsto_probability_zero
/-- Under [admissibility of the reference nuisances](hyp:he0) and [all fitted
nuisances](hyp:heh), and componentwise nuisance rates for [treatment
probabilities](hyp:hrp), [upper full-interval means](hyp:hrplus), and [lower
full-interval means](hyp:hrminus), [the observation-integrated square of the sum
across levels of the policy-minus-baseline instrument indicators times the
full-interval contrast errors converges in probability to zero, using fits at
twice the half-sample size](goal). -/
lemma nuisanceRates_continuous_full_event_block_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrplus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullPlus) e0.JfullPlus)
    (hrminus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullMinus) e0.JfullMinus) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        (∑ k ∈ Finset.range L.K,
          (indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k)) *
            (contFullJ L (eh (2*(n+1)) a) k o.1 - contFullJ L e0 k o.1)) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  apply dml_finset_sum_sq_tendsto_probability_zero
  · intro k hk n a
    have hm := (fitted_continuous_full_event_memLp M L _ (heh (2*(n+1)) a) k).sub
      (fitted_continuous_full_event_memLp M L e0 he0 k)
    convert hm using 1
    funext o
    simp only [Pi.sub_apply]
    ring
  · intro k hk
    exact nuisanceRates_continuous_full_event_sq_tendsto_probability_zero M μ L e0 eh
      he0 heh hrp hrplus hrminus k

end Papers.TbsPrteOptimalTransport
