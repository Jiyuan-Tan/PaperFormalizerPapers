module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousFullContrast
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationContinuousFullMean
public import Papers.TbsPrteOptimalTransport.Helpers.DMLTailBaselineConvergence
/-! Second moments and L2 convergence of the continuous full-interval outcome
residuals. Clipping bounds the regressions, overlap bounds the reciprocals,
and the component nuisance rates control the actual observed residual errors. -/
public section
set_option linter.style.haveILetI false
set_option linter.style.openClassical false
set_option linter.unnecessarySeqFocus false
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

-- @node: observationLaw_outcome_abs_bound
/-- Under [potential-outcome support restrictions](hyp:hp), [consistency](hyp:hc),
and [known outcome endpoints](hyp:he), [the observed outcome is almost surely
bounded in absolute value by the larger absolute endpoint](goal). -/
lemma observationLaw_outcome_abs_bound (hp : PotentialSupport M)
    (hc : Consistency M) (he : OutcomeEndpointsKnown M) :
    ∀ᵐ o : Obs X Z ∂observationLaw M, |o.2.2.2| ≤ max |M.yMin| |M.yMax| := by
  have hm : Measurable (fun s => (M.Xv s, M.Zv s, M.W s, M.Y s)) := by
    first | fun_prop | exact M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
  apply (ae_map_iff hm.aemeasurable
    (measurableSet_le (by fun_prop) measurable_const)).2
  filter_upwards [hp.1, hp.2, hc] with s h0 h1 hs
  have hy : M.Y s ∈ M.Yset := by
    rcases M.rangeW s with hw | hw <;> rw [hs, hw] <;> simpa using (by assumption)
  apply abs_le.mpr
  exact ⟨(neg_le_neg (le_max_left _ _)).trans ((neg_abs_le _).trans (he.1.2 hy)),
    (he.2.2 hy).trans ((le_abs_self _).trans (le_max_right _ _))⟩

-- @node: fitted_continuous_assignment_coordinates
/-- If [the fitted continuous nuisance is admissible](hyp:he), then [its assignment
probability at any index, extended by zero outside the positive levels, is
measurable and almost surely bounded in absolute value by one](goal). -/
lemma fitted_continuous_assignment_coordinates (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e) (i : ℕ) :
    Measurable (positiveValue e.piLev i) ∧
      ∀ᵐ x ∂xLaw M, |positiveValue e.piLev i x| ≤ 1 := by
  change Measurable (fun x => positiveValue e.piLev i x) ∧ _
  by_cases hi : 1 ≤ i ∧ i ≤ L.K
  · simp only [positiveValue, dif_pos hi]
    refine ⟨?_, ?_⟩
    · first | fun_prop | exact he.2.2.2.2.2.1 ⟨i, hi⟩
    · filter_upwards [he.2.2.2.2.1 ⟨i, hi⟩] with x hx
      rw [abs_of_nonneg hx.1]
      exact hx.2
  · simp only [positiveValue, dif_neg hi]
    exact ⟨by fun_prop, Eventually.of_forall (fun _ => by norm_num)⟩

-- @node: fitted_continuous_full_residual_measurable
/-- If [the fitted continuous nuisance is admissible](hyp:he), then [the
full-interval outcome residual is a measurable function of the observation,
for either endpoint and any index](goal). -/
@[fun_prop] lemma fitted_continuous_full_residual_measurable (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e) (plus : Bool) (k : ℕ) :
    Measurable (continuousFullOutcomeResidual L e plus k) := by
  first | fun_prop | skip
  have hpi := (fitted_continuous_assignment_coordinates M L e he
    (if plus then k+1 else k)).1
  have hj := (fitted_continuous_full_coordinates M L e he k).2
  have hm : Measurable (fun x => if plus then fullValue e.JfullPlus k x
      else minusFullValue e k x) := by
    cases plus <;> simp only [Bool.false_eq_true, Bool.true_eq, if_false, if_true] <;>
      first | fun_prop | exact hj.2.1 | exact hj.1.1
  have ha : Measurable (fun o : Obs X Z =>
      indicator (o.2.1 ∈ L.S (if plus then k+1 else k))) := by
    first
    | fun_prop
    | unfold indicator
      exact Measurable.ite ((L.S _).finite_toSet.measurableSet.preimage measurable_snd.fst)
        measurable_const measurable_const
  unfold continuousFullOutcomeResidual
  split
  · fun_prop
  · exact ((ha.mul measurable_snd.snd.fst).div (hpi.comp measurable_fst)).mul
      (measurable_snd.snd.snd.sub (hm.comp measurable_fst))

-- @node: fitted_continuous_full_residual_abs_bound
/-- Assume [the fitted nuisance is admissible](hyp:he), [potential outcomes lie in
their support](hyp:hp), [observed outcomes satisfy consistency](hyp:hcons), and
[the outcome endpoints are known](hyp:hend). If [the overlap bound is positive](hyp:hc),
[every positive-level fitted assignment probability is almost surely at least
that bound](hyp:hclip), and [the index is below the number of levels](hyp:hk), then
[either full-interval outcome residual is almost surely bounded in absolute value
by twice the largest absolute outcome endpoint divided by the overlap bound](goal). -/
lemma fitted_continuous_full_residual_abs_bound (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e)
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (plus : Bool) (k : ℕ) (hk : k < L.K) :
    ∀ᵐ o ∂observationLaw M, |continuousFullOutcomeResidual L e plus k o| ≤
      2 * max |M.yMin| |M.yMax| / c := by
  by_cases hz : !plus ∧ k = 0
  · simp only [continuousFullOutcomeResidual, if_pos hz, abs_zero]
    exact Eventually.of_forall (fun _ => by positivity)
  have hi : 1 ≤ (if plus then k+1 else k) ∧ (if plus then k+1 else k) ≤ L.K := by
    cases plus <;> simp_all <;> omega
  have hcl : ∀ᵐ x ∂xLaw M, c ≤ positiveValue e.piLev (if plus then k+1 else k) x := by
    simpa only [positiveValue, dif_pos hi] using hclip ⟨_, hi⟩
  have hj : ∀ᵐ x ∂xLaw M,
      |if plus then fullValue e.JfullPlus k x else minusFullValue e k x| ≤
        max |M.yMin| |M.yMax| := by
    have hh := (fitted_continuous_full_coordinates M L e he k).2
    cases plus
    · simpa using hh.2.2
    · simpa using hh.1.2
  filter_upwards [observationLaw_outcome_abs_bound M hp hcons hend,
    observationLaw_treatment_range M, observationLaw_covariate_ae M _ hcl,
    observationLaw_covariate_ae M _ hj] with o hy hw hpi hm
  have ha : |indicator (o.2.1 ∈ L.S (if plus then k+1 else k)) * o.2.2.1| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hw.1]
    have hb : |indicator (o.2.1 ∈ L.S (if plus then k+1 else k))| ≤ 1 := by
      unfold indicator; split_ifs <;> norm_num
    exact (mul_le_mul hb hw.2 hw.1 zero_le_one).trans_eq (one_mul _)
  have hr : |o.2.2.2 - (if plus then fullValue e.JfullPlus k o.1 else minusFullValue e k o.1)| ≤
      2 * max |M.yMin| |M.yMax| := (abs_sub _ _).trans (by linarith)
  rw [continuousFullOutcomeResidual, if_neg hz, abs_mul, abs_div,
    abs_of_pos (hc.trans_le hpi)]
  calc
    _ ≤ (1 / c) * (2 * max |M.yMin| |M.yMax|) := by
      apply mul_le_mul _ hr (abs_nonneg _) (by positivity)
      exact (div_le_div_of_nonneg_right ha (hc.trans_le hpi).le).trans
        (div_le_div_of_nonneg_left zero_le_one hc hpi)
    _ = _ := by ring

-- @node: fitted_continuous_full_residual_memLp
/-- Under [admissibility of the fitted nuisance](hyp:he), [potential-outcome support
restrictions](hyp:hp), [consistency](hyp:hcons), and [known outcome endpoints](hyp:hend),
if [the overlap bound is positive](hyp:hc), [fitted assignment probabilities are
almost surely bounded below by it](hyp:hclip), and [the index is below the number
of levels](hyp:hk), then [either full-interval outcome residual is square-integrable
under the observation distribution](goal). -/
lemma fitted_continuous_full_residual_memLp (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e)
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (plus : Bool) (k : ℕ) (hk : k < L.K) :
    MemLp (continuousFullOutcomeResidual L e plus k) 2 (observationLaw M) := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  apply MemLp.of_bound (by fun_prop) (2 * max |M.yMin| |M.yMax| / c)
  simpa only [Real.norm_eq_abs] using fitted_continuous_full_residual_abs_bound M L e he
    hp hcons hend c hc hclip plus k hk

-- @node: nuisanceRates_continuous_full_residual_sq_tendsto_probability_zero
/-- Suppose [the reference nuisance is admissible](hyp:he0), [every fitted nuisance
is admissible](hyp:heh), [potential outcomes satisfy their support restrictions](hyp:hp),
[consistency holds](hyp:hcons), and [outcome endpoints are known](hyp:hend). With
[a positive overlap bound](hyp:hc), [reference and fitted assignment probabilities
almost surely above that bound](hyp:hclip), inverse-fourth-root little-order L2
rates for [assignment probabilities](hyp:hrpi), [upper outcome means](hyp:hrplus),
and [lower outcome means](hyp:hrminus), and [an index below the number of levels](hyp:hk),
[the integrated squared difference between fitted and reference full-interval
outcome residuals converges in probability to zero along even sample sizes](goal). -/
lemma nuisanceRates_continuous_full_residual_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrplus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullPlus) e0.JfullPlus)
    (hrminus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullMinus) e0.JfullMinus)
    (plus : Bool) (k : ℕ) (hk : k < L.K) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o,
        (continuousFullOutcomeResidual L (eh (2*(n+1)) a) plus k o -
          continuousFullOutcomeResidual L e0 plus k o)^2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  by_cases hz : !plus ∧ k = 0
  · rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
    intro eps heps
    simpa [continuousFullOutcomeResidual, hz, not_le_of_gt heps] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  let i := if plus then k+1 else k
  have hi : 1 ≤ i ∧ i ≤ L.K := by
    dsimp only [i]
    cases plus <;> simp_all <;> omega
  let J := fun (e : NuisanceCont L) x =>
    if plus then fullValue e.JfullPlus k x else minusFullValue e k x
  have hJ (e : NuisanceCont L) (he : ContAdmissible M L e) :
      Measurable (J e) ∧ ∀ᵐ x ∂xLaw M, |J e x| ≤ max |M.yMin| |M.yMax| := by
    have hh := (fitted_continuous_full_coordinates M L e he k).2
    cases plus
    · simpa only [J, Bool.false_eq_true, if_false] using hh.2
    · simpa only [J, Bool.true_eq, if_true] using hh.1
  have hJLp (e : NuisanceCont L) (he : ContAdmissible M L e) :
      MemLp (J e) 2 (xLaw M) :=
    MemLp.of_bound (hJ e he).1.aestronglyMeasurable _ (by
      simpa only [Real.norm_eq_abs] using (hJ e he).2)
  have hPiLp (e : NuisanceCont L) (he : ContAdmissible M L e) :
      MemLp (positiveValue e.piLev i) 2 (xLaw M) :=
    MemLp.of_bound (fitted_continuous_assignment_coordinates M L e he i).1.aestronglyMeasurable
      1 (by simpa only [Real.norm_eq_abs] using
        (fitted_continuous_assignment_coordinates M L e he i).2)
  have hrJ : Causalean.Stat.IsLittleOp
      (fun n a => finiteL2Error M (J (eh (2*(n+1)) a)) (J e0))
      (fun n => ((2*(n+1) : ℕ) : ℝ)^(-1/4 : ℝ)) μ := by
    cases plus
    · have hk1 : 1 ≤ k ∧ k < L.K := by simp_all; omega
      simpa only [J, Bool.false_eq_true, if_false, minusFullValue, dif_pos hk1] using
        hrminus ⟨k, hk1⟩
    · simpa only [J, Bool.true_eq, if_true, fullValue, dif_pos hk] using hrplus ⟨k, hk⟩
  have hres : ∀ᵐ o : Obs X Z ∂observationLaw M,
      |o.2.2.2 - J e0 o.1| ≤ 2 * max |M.yMin| |M.yMax| := by
    filter_upwards [observationLaw_outcome_abs_bound M hp hcons hend,
      observationLaw_covariate_ae M _ (hJ e0 he0).2] with o hy hj
    exact (abs_sub _ _).trans (by linarith)
  have hr := dml_observation_ipw_residual_sq_tendsto_probability_zero M μ
    (positiveValue e0.piLev i) (J e0) (fun o => o.2.2.2)
    (fun o => indicator (o.2.1 ∈ L.S i) * o.2.2.1)
    (fun n a => positiveValue (eh (2*(n+1)) a).piLev i)
    (fun n a => J (eh (2*(n+1)) a)) c (2 * max |M.yMin| |M.yMax|) hc
    (fitted_continuous_assignment_coordinates M L e0 he0 i).1 (hJ e0 he0).1
    (by fun_prop) (by fun_prop)
    (fun n a => (fitted_continuous_assignment_coordinates M L _ (heh _ a) i).1)
    (fun n a => (hJ _ (heh _ a)).1)
    (fun n a => (hJLp _ (heh _ a)).sub (hJLp e0 he0))
    (fun n a => (hPiLp _ (heh _ a)).sub (hPiLp e0 he0))
    (fun n a => by simpa only [positiveValue, dif_pos hi] using hclip _ a ⟨i, hi⟩)
    (by
      filter_upwards [observationLaw_treatment_range M] with o hw
      rw [abs_mul, abs_of_nonneg hw.1]
      have ha : |indicator (o.2.1 ∈ L.S i)| ≤ 1 := by
        unfold indicator; split_ifs <;> norm_num
      exact (mul_le_mul ha hw.2 hw.1 zero_le_one).trans_eq (one_mul _))
    hres hrJ (nuisanceRates_positiveValue M μ L.K _ _ hrpi i)
  simpa only [continuousFullOutcomeResidual, if_neg hz, i, J] using hr

-- @node: nuisanceRates_continuous_full_residual_l2_tendsto_probability_zero
/-- If [the reference nuisance is admissible](hyp:he0), [all fitted nuisances are
admissible](hyp:heh), [potential outcomes satisfy their support restrictions](hyp:hp),
[consistency holds](hyp:hcons), and [outcome endpoints are known](hyp:hend), then,
under [a positive overlap bound](hyp:hc), [that common lower bound on reference
and fitted assignment probabilities](hyp:hclip), inverse-fourth-root little-order
L2 rates for [assignment probabilities](hyp:hrpi), [upper means](hyp:hrplus), and
[lower means](hyp:hrminus), and [an index below the number of levels](hyp:hk),
[the L2 distance between fitted and reference full-interval outcome residuals
converges in probability to zero along even sample sizes](goal). -/
lemma nuisanceRates_continuous_full_residual_l2_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrplus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullPlus) e0.JfullPlus)
    (hrminus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullMinus) e0.JfullMinus)
    (plus : Bool) (k : ℕ) (hk : k < L.K) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt (∫ o,
        (continuousFullOutcomeResidual L (eh (2*(n+1)) a) plus k o -
          continuousFullOutcomeResidual L e0 plus k o)^2 ∂observationLaw M))
      atTop (fun _ _ => 0) := by
  have hs := nuisanceRates_continuous_full_residual_sq_tendsto_probability_zero M μ L e0 eh
    he0 heh hp hcons hend c hc hclip hrpi hrplus hrminus plus k hk
  have hcont : Continuous (fun t : ℝ => Real.sqrt t) := by fun_prop
  simpa only [Real.sqrt_zero] using
    Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt hcont.continuousAt hs

end Papers.TbsPrteOptimalTransport
