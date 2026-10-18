module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousWeightedFullResidual
/-! Moments and L2 convergence of continuous full-interval product scores.
Clipping and component nuisance rates control the treatment residual and its
signed regression weights. The five score terms then assemble over all levels. -/
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

-- @node: fitted_continuous_treatment_range
/-- If [the fitted continuous nuisances are admissible](hyp:he), then [the fitted
treatment probability at any index, extended by zero outside the positive levels,
lies between zero and one almost surely under the covariate distribution](goal). -/
lemma fitted_continuous_treatment_range (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (i : ℕ) :
    ∀ᵐ x ∂xLaw M, positiveValue e.pLev i x ∈ Icc (0 : ℝ) 1 := by
  by_cases hi : 1 ≤ i ∧ i ≤ L.K
  · simpa only [positiveValue, dif_pos hi] using he.2.2.1 ⟨i, hi⟩
  · simp only [positiveValue, dif_neg hi]
    exact Eventually.of_forall (fun _ => ⟨le_rfl, zero_le_one⟩)

-- @node: fitted_continuous_treatment_assignment_memLp
/-- Under [admissibility of the fitted continuous nuisances](hyp:he), [both the
fitted treatment probability and the fitted assignment probability at any index,
extended by zero outside the positive levels, have finite second moments under
the covariate distribution](goal). -/
lemma fitted_continuous_treatment_assignment_memLp (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e) (i : ℕ) :
    MemLp (positiveValue e.pLev i) 2 (xLaw M) ∧
      MemLp (positiveValue e.piLev i) 2 (xLaw M) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  constructor
  · apply MemLp.of_bound (by
      first | fun_prop | exact
        (fitted_continuous_full_coordinates M L e he i).1.1.aestronglyMeasurable) 1
    simpa only [Real.norm_eq_abs] using (fitted_continuous_full_coordinates M L e he i).1.2
  · apply MemLp.of_bound (by
      first | fun_prop | exact
        (fitted_continuous_assignment_coordinates M L e he i).1.aestronglyMeasurable) 1
    simpa only [Real.norm_eq_abs] using (fitted_continuous_assignment_coordinates M L e he i).2

-- @node: fitted_RpCont_measurable
/-- If [the fitted continuous nuisances are admissible](hyp:he), then [the
inverse-assignment-weighted treatment residual at any level is measurable as a
function of the observation](goal). -/
@[fun_prop] lemma fitted_RpCont_measurable (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (i : ℕ) : Measurable (RpCont L e i) := by
  first | fun_prop | skip
  have hp := (fitted_continuous_full_coordinates M L e he i).1.1
  have hpi := (fitted_continuous_assignment_coordinates M L e he i).1
  unfold RpCont
  split_ifs <;> fun_prop

-- Clipping bounds the treatment residual independently of the outcome law.
-- @node: fitted_RpCont_abs_bound
/-- Suppose [the fitted continuous nuisances are admissible](hyp:he), [the clipping
constant is positive](hyp:hc), and [all fitted assignment probabilities are almost
surely at least that constant](hyp:hclip). For [an index no larger than the terminal
level](hyp:hi), [the inverse-assignment-weighted treatment residual has absolute
value at most the reciprocal clipping constant almost surely under the observation
distribution](goal). -/
lemma fitted_RpCont_abs_bound (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (i : ℕ) (hi : i ≤ L.K) :
    ∀ᵐ o ∂observationLaw M, |RpCont L e i o| ≤ 1 / c := by
  by_cases hi0 : i = 0
  · subst i
    exact Eventually.of_forall (fun o => by simp only [RpCont, ↓reduceIte, abs_zero]; positivity)
  have hip : 1 ≤ i ∧ i ≤ L.K := ⟨by omega, hi⟩
  have hcl : ∀ᵐ x ∂xLaw M, c ≤ positiveValue e.piLev i x := by
    simpa only [positiveValue, dif_pos hip] using hclip ⟨i, hip⟩
  filter_upwards [observationLaw_treatment_range M,
    observationLaw_covariate_ae M _ (fitted_continuous_treatment_range M L e he i),
    observationLaw_covariate_ae M _ hcl] with o ho hj hp
  have hr : |o.2.2.1 - positiveValue e.pLev i o.1| ≤ 1 :=
    abs_le.mpr ⟨by linarith [ho.1, hj.2], by linarith [ho.2, hj.1]⟩
  have ha : |indicator (o.2.1 ∈ L.S i)| ≤ 1 := by
    unfold indicator
    split_ifs <;> norm_num
  rw [RpCont, if_neg hi0, abs_mul, abs_div, abs_of_pos (hc.trans_le hp)]
  calc
    _ ≤ (1 / positiveValue e.piLev i o.1) * 1 := by
      have hp0 := hc.trans_le hp
      gcongr
    _ ≤ 1 / c := by
      rw [mul_one]
      exact div_le_div_of_nonneg_left zero_le_one hc hp

-- @node: fitted_RpCont_memLp
/-- Under [admissibility of the fitted nuisances](hyp:he), [a positive clipping
constant](hyp:hc), and [an almost-sure lower bound by that constant on every fitted
assignment probability](hyp:hclip), [the inverse-assignment-weighted treatment
residual has a finite second moment under the observation distribution](goal)
for [every index no larger than the terminal level](hyp:hi). -/
lemma fitted_RpCont_memLp (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (i : ℕ) (hi : i ≤ L.K) : MemLp (RpCont L e i) 2 (observationLaw M) := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  apply MemLp.of_bound (by fun_prop) (1 / c)
  simpa only [Real.norm_eq_abs] using fitted_RpCont_abs_bound M L e he c hc hclip i hi

-- @node: nuisanceRates_RpCont_sq_tendsto_probability_zero
/-- For [a sequence of fitted continuous nuisances](hyp:eh), assume [the reference
nuisances are admissible](hyp:he0), [every fit is admissible](hyp:heh), [the clipping
constant is positive](hyp:hc), and [reference and fitted assignment probabilities
are almost surely bounded below by it uniformly over fits and levels](hyp:hclip).
If [treatment probabilities](hyp:hrp) and [assignment probabilities](hyp:hrpi)
satisfy their finite nuisance rate conditions, then, for [any index no larger than
the terminal level](hyp:hk), [the observation-integrated squared error of the
inverse-assignment-weighted treatment residual converges in probability to zero,
using fits at sample sizes twice one plus the sequence index](goal). -/
lemma nuisanceRates_RpCont_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (k : ℕ) (hk : k ≤ L.K) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, (RpCont L (eh (2*(n+1)) a) k o - RpCont L e0 k o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  by_cases hk0 : k = 0
  · subst k
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
    intro eps heps
    simpa [RpCont, not_le_of_gt heps] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
  have hk : 1 ≤ k ∧ k ≤ L.K := ⟨by omega, hk⟩
  have hp := (fitted_continuous_assignment_coordinates M L e0 he0 k).1
  have hj := (fitted_continuous_full_coordinates M L e0 he0 k).1.1
  have hph (n : ℕ) (a : A) :=
    (fitted_continuous_assignment_coordinates M L (eh (2*(n+1)) a) (heh _ a) k).1
  have hjh (n : ℕ) (a : A) :=
    (fitted_continuous_full_coordinates M L (eh (2*(n+1)) a) (heh _ a) k).1.1
  have hsel : Measurable (fun o : Obs X Z => indicator (o.2.1 ∈ L.S k)) := by fun_prop
  have hW : ∀ᵐ o : Obs X Z ∂observationLaw M, o.2.2.1 ∈ Icc (0 : ℝ) 1 := by
    have hm : Measurable (fun s => (M.Xv s, M.Zv s, M.W s, M.Y s)) := by
      first | fun_prop | exact M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
    apply (ae_map_iff hm.aemeasurable (measurableSet_Icc.preimage (by fun_prop))).2
    exact Eventually.of_forall (fun s => by rcases M.rangeW s with h | h <;> simp [h])
  have hres : ∀ᵐ o : Obs X Z ∂observationLaw M,
      |o.2.2.1 - positiveValue e0.pLev k o.1| ≤ 1 := by
    have hr : ∀ᵐ x ∂xLaw M, positiveValue e0.pLev k x ∈ Icc (0 : ℝ) 1 := by
      simpa only [positiveValue, dif_pos hk] using
        he0.2.2.1 ⟨k, hk⟩
    filter_upwards [hW, observationLaw_covariate_ae M _ hr] with o ho hj
    exact abs_le.mpr ⟨by linarith [ho.1, hj.2], by linarith [ho.2, hj.1]⟩
  have hr := dml_observation_ipw_residual_sq_tendsto_probability_zero M μ
    (positiveValue e0.piLev k) (positiveValue e0.pLev k)
    (fun o => o.2.2.1) (fun o => indicator (o.2.1 ∈ L.S k))
    (fun n a => positiveValue (eh (2*(n+1)) a).piLev k)
    (fun n a => positiveValue (eh (2*(n+1)) a).pLev k) c 1 hc hp hj
    (by fun_prop) hsel hph hjh
    (fun n a => (fitted_continuous_treatment_assignment_memLp M L _ (heh _ a) k).1.sub
      (fitted_continuous_treatment_assignment_memLp M L e0 he0 k).1)
    (fun n a => (fitted_continuous_treatment_assignment_memLp M L _ (heh _ a) k).2.sub
      (fitted_continuous_treatment_assignment_memLp M L e0 he0 k).2)
    (fun n a => by simpa only [positiveValue, dif_pos hk] using hclip _ a ⟨k, hk⟩)
    (Eventually.of_forall (fun o => by unfold indicator; split_ifs <;> norm_num)) hres
    (nuisanceRates_positiveValue M μ L.K _ _ hrp k)
    (nuisanceRates_positiveValue M μ L.K _ _ hrpi k)
  simpa only [RpCont, if_neg (show k ≠ 0 by omega)] using hr

-- @node: nuisanceRates_RpCont_l2_tendsto_probability_zero
/-- For [a sequence of fitted continuous nuisances](hyp:eh), suppose [the reference
nuisances are admissible](hyp:he0), [all fitted nuisances are admissible](hyp:heh),
[the clipping constant is positive](hyp:hc), and [reference and fitted assignment
probabilities share that almost-sure lower bound](hyp:hclip). Under finite nuisance
rate conditions for [treatment probabilities](hyp:hrp) and [assignment probabilities](hyp:hrpi),
for [each index at most the terminal level](hyp:hk), [the square root of the
observation-integrated squared treatment-residual error converges in probability
to zero, using fits at sample sizes twice one plus the sequence index](goal). -/
lemma nuisanceRates_RpCont_l2_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (k : ℕ) (hk : k ≤ L.K) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt (∫ o,
        (RpCont L (eh (2*(n+1)) a) k o - RpCont L e0 k o)^2
        ∂observationLaw M)) atTop (fun _ _ => 0) := by
  have hs := nuisanceRates_RpCont_sq_tendsto_probability_zero M μ L e0 eh
    he0 heh c hc hclip hrp hrpi k hk
  have hcont : Continuous (fun t : ℝ => Real.sqrt t) := by fun_prop
  simpa only [Real.sqrt_zero] using
    Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt hcont.continuousAt hs

-- @node: fitted_continuous_full_treatment_weight_coordinates
/-- If [the fitted continuous nuisances are admissible](hyp:he), then [the product
of the full-interval signed weight and the selected upper or lower outcome
regression is measurable and is bounded in absolute value almost surely by the
larger absolute outcome endpoint under the covariate distribution](goal). -/
lemma fitted_continuous_full_treatment_weight_coordinates (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e) (plus : Bool) (k : Fin L.K) :
    Measurable (fun x => e.gammaFull k x *
      (if plus then fullValue e.JfullPlus k x else minusFullValue e k x)) ∧
    ∀ᵐ x ∂xLaw M, |e.gammaFull k x *
      (if plus then fullValue e.JfullPlus k x else minusFullValue e k x)| ≤
        max |M.yMin| |M.yMax| := by
  have hg := fitted_continuous_gammaFull_coordinates M L e he k
  have hj := (fitted_continuous_full_coordinates M L e he k).2
  have hJ : Measurable (fun x => if plus then fullValue e.JfullPlus k x
      else minusFullValue e k x) ∧
      ∀ᵐ x ∂xLaw M, |if plus then fullValue e.JfullPlus k x
        else minusFullValue e k x| ≤ max |M.yMin| |M.yMax| := by
    cases plus
    · simpa using hj.2
    · simpa using hj.1
  refine ⟨by first | fun_prop | exact hg.1.mul hJ.1, ?_⟩
  filter_upwards [hg.2, hJ.2] with x hx hy
  rw [abs_mul]
  exact (mul_le_mul hx hy (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

-- @node: fitted_continuous_full_treatment_weight_memLp
/-- Under [admissibility of the fitted continuous nuisances](hyp:he), [the product
of the signed full-interval weight and either the upper or lower outcome regression
has a finite second moment under the covariate distribution](goal). -/
lemma fitted_continuous_full_treatment_weight_memLp (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e) (plus : Bool) (k : Fin L.K) :
    MemLp (fun x => e.gammaFull k x *
      (if plus then fullValue e.JfullPlus k x else minusFullValue e k x))
      2 (xLaw M) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  have hw := fitted_continuous_full_treatment_weight_coordinates M L e he plus k
  apply MemLp.of_bound (by first | fun_prop | exact hw.1.aestronglyMeasurable)
    (max |M.yMin| |M.yMax|)
  simpa only [Real.norm_eq_abs] using hw.2

-- @node: nuisanceRates_continuous_full_treatment_weight_sq_tendsto_probability_zero
/-- For [a sequence of fitted continuous nuisances](hyp:eh), assume [admissibility
of the reference nuisances](hyp:he0) and [all fitted nuisances](hyp:heh), together
with finite nuisance rate conditions for [upper full-interval regressions](hyp:hrplus),
[lower full-interval regressions](hyp:hrminus), and [signed full-interval weights](hyp:hrg).
Then [the covariate-integrated squared error of the product of the signed weight
and the selected upper or lower regression converges in probability to zero for
each full interval, using fits at sample sizes twice one plus the sequence index](goal). -/
lemma nuisanceRates_continuous_full_treatment_weight_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hrplus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullPlus) e0.JfullPlus)
    (hrminus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullMinus) e0.JfullMinus)
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gammaFull) e0.gammaFull)
    (plus : Bool) (k : Fin L.K) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x,
        ((eh (2*(n+1)) a).gammaFull k x *
            (if plus then fullValue (eh (2*(n+1)) a).JfullPlus k x
              else minusFullValue (eh (2*(n+1)) a) k x) -
          e0.gammaFull k x *
            (if plus then fullValue e0.JfullPlus k x else minusFullValue e0 k x))^2
        ∂xLaw M) atTop (fun _ _ => 0) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
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
  have hrJ : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, (J (eh (2*(n+1)) a) x - J e0 x)^2 ∂xLaw M)
      atTop (fun _ _ => 0) := by
    cases plus
    · by_cases hk : 1 ≤ k.val ∧ k.val < L.K
      · simpa only [J, Bool.false_eq_true, if_false, minusFullValue, dif_pos hk] using
          nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hrminus ⟨k, hk⟩
      · have hk' : ¬1 ≤ k.val := fun h => hk ⟨h, k.isLt⟩
        rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
        intro eps heps
        simpa [J, minusFullValue, hk', not_le_of_gt heps] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
    · simpa only [J, Bool.true_eq, if_true, fullValue, dif_pos k.isLt] using
        nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hrplus k
  apply dml_weighted_residual_sq_tendsto_probability_zero μ (xLaw M)
    (e0.gammaFull k) (J e0) (fun n a => (eh (2*(n+1)) a).gammaFull k)
    (fun n a => J (eh (2*(n+1)) a)) 1 (max |M.yMin| |M.yMax|)
    (fitted_continuous_gammaFull_coordinates M L e0 he0 k).1 (hJ e0 he0).1
    (fun n a => (fitted_continuous_gammaFull_coordinates M L _ (heh _ a) k).1)
    (fun n a => (hJ _ (heh _ a)).1)
    (fun n a => (fitted_continuous_gammaFull_memLp M L _ (heh _ a) k).sub
      (fitted_continuous_gammaFull_memLp M L e0 he0 k))
    (fun n a => (hJLp _ (heh _ a)).sub (hJLp e0 he0))
    (fun n a => (fitted_continuous_gammaFull_coordinates M L _ (heh _ a) k).2)
    (fun _ _ => (hJ e0 he0).2)
    (nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hrg k) hrJ

-- @node: fitted_continuous_full_treatment_correction_memLp
/-- Suppose [the fitted continuous nuisances are admissible](hyp:he), [the clipping
constant is positive](hyp:hc), and [every fitted assignment probability is almost
surely at least that constant](hyp:hclip). Then [the treatment correction obtained
by multiplying the signed full-interval weight, the selected upper or lower
regression, and the treatment residual at the corresponding upper or lower level
has a finite second moment under the observation distribution](goal). -/
lemma fitted_continuous_full_treatment_correction_memLp (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (plus : Bool) (k : Fin L.K) :
    MemLp (fun o => (e.gammaFull k o.1 *
      (if plus then fullValue e.JfullPlus k o.1 else minusFullValue e k o.1)) *
        RpCont L e (if plus then k.val+1 else k.val) o) 2 (observationLaw M) := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  have hw := fitted_continuous_full_treatment_weight_coordinates M L e he plus k
  have hr := fitted_RpCont_measurable M L e he (if plus then k.val+1 else k.val)
  apply MemLp.of_bound (by first | fun_prop | exact
    ((hw.1.comp measurable_fst).mul hr).aestronglyMeasurable)
    (max |M.yMin| |M.yMax| * (1 / c))
  have hi : (if plus then k.val+1 else k.val) ≤ L.K := by cases plus <;> simp <;> omega
  filter_upwards [observationLaw_covariate_ae M _ hw.2,
    fitted_RpCont_abs_bound M L e he c hc hclip _ hi] with o hw hr
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul hw hr (abs_nonneg _) (by positivity)

-- @node: nuisanceRates_continuous_full_treatment_correction_sq_tendsto_probability_zero
/-- For [a sequence of fitted continuous nuisances](hyp:eh), suppose [the reference
nuisances are admissible](hyp:he0), [all fitted nuisances are admissible](hyp:heh),
[the clipping constant is positive](hyp:hc), and [reference and fitted assignment
probabilities are uniformly bounded below by it almost surely](hyp:hclip). Under
finite nuisance rate conditions for [treatment probabilities](hyp:hrp), [assignment
probabilities](hyp:hrpi), [upper regressions](hyp:hrplus), [lower regressions](hyp:hrminus),
and [signed weights](hyp:hrg), [the observation-integrated squared error of the
full-interval treatment correction converges in probability to zero for either
sign and each interval, using fits at sample sizes twice one plus the sequence
index](goal). -/
lemma nuisanceRates_continuous_full_treatment_correction_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrplus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullPlus) e0.JfullPlus)
    (hrminus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullMinus) e0.JfullMinus)
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gammaFull) e0.gammaFull)
    (plus : Bool) (k : Fin L.K) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o,
        (((eh (2*(n+1)) a).gammaFull k o.1 *
            (if plus then fullValue (eh (2*(n+1)) a).JfullPlus k o.1
              else minusFullValue (eh (2*(n+1)) a) k o.1)) *
            RpCont L (eh (2*(n+1)) a) (if plus then k.val+1 else k.val) o -
          (e0.gammaFull k o.1 *
            (if plus then fullValue e0.JfullPlus k o.1 else minusFullValue e0 k o.1)) *
            RpCont L e0 (if plus then k.val+1 else k.val) o)^2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  let w := fun (e : NuisanceCont L) x => e.gammaFull k x *
    (if plus then fullValue e.JfullPlus k x else minusFullValue e k x)
  let i : ℕ := if plus then k.val+1 else k.val
  have hi : i ≤ L.K := by dsimp only [i]; cases plus <;> simp <;> omega
  have hw (e : NuisanceCont L) (he : ContAdmissible M L e) :=
    fitted_continuous_full_treatment_weight_coordinates M L e he plus k
  have hrs := nuisanceRates_continuous_full_treatment_weight_sq_tendsto_probability_zero
    M μ L e0 eh he0 heh hrplus hrminus hrg plus k
  have hint n a := observationLaw_covariate_integral M
    (fun x => (w (eh (2*(n+1)) a) x - w e0 x)^2) (by
      first | fun_prop | exact ((hw _ (heh _ a)).1.sub (hw e0 he0).1).pow_const 2)
  apply dml_weighted_residual_sq_tendsto_probability_zero μ (observationLaw M)
    (fun o => w e0 o.1) (RpCont L e0 i)
    (fun n a o => w (eh (2*(n+1)) a) o.1)
    (fun n a => RpCont L (eh (2*(n+1)) a) i)
    (max |M.yMin| |M.yMax|) (1 / c)
    (by first | fun_prop | exact (hw e0 he0).1.comp measurable_fst)
    (by fun_prop)
    (by intro n a; first | fun_prop | exact (hw _ (heh _ a)).1.comp measurable_fst)
    (by intro n a; first | fun_prop | exact fitted_RpCont_measurable M L _ (heh _ a) i)
  · intro n a
    exact ((fitted_continuous_full_treatment_weight_memLp M L _ (heh _ a) plus k).sub
      (fitted_continuous_full_treatment_weight_memLp M L e0 he0 plus k)).comp_measurePreserving
        (observationLaw_fst_measurePreserving M)
  · intro n a
    exact (fitted_RpCont_memLp M L _ (heh _ a) c hc
      (fun j => (hclip _ a j).mono (fun _ hx => hx.2)) i hi).sub
        (fitted_RpCont_memLp M L e0 he0 c hc
          (fun j => (hclip (2*(n+1)) a j).mono (fun _ hx => hx.1)) i hi)
  · intro n a
    exact observationLaw_covariate_ae M _ (hw _ (heh _ a)).2
  · intro n a
    exact fitted_RpCont_abs_bound M L e0 he0 c hc
      (fun j => (hclip n a j).mono (fun _ hx => hx.1)) i hi
  · simpa only [hint] using hrs
  · exact nuisanceRates_RpCont_sq_tendsto_probability_zero M μ L e0 eh
      he0 heh c hc hclip hrp hrpi i hi

-- The fitted product weight cancels in the plug-in term. The remaining four
-- corrections retain their fitted signed weights.
-- @node: continuous_full_product_correction_decomposition
/-- [The full-interval product score equals the policy-minus-baseline higher-level
indicator times the fitted full-interval integral, plus the signed-weighted upper
outcome residual, minus the signed-weighted lower outcome residual, plus the
signed-weighted upper regression times the next-level treatment residual, minus
the signed-weighted lower regression times the current-level treatment residual](goal). -/
lemma continuous_full_product_correction_decomposition (L : LevelData Z X)
    (e : NuisanceCont L) (k : Fin L.K) (o : Obs X Z) :
    psiFullProd L e k o =
      (indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k)) *
        contFullJ L e k o.1 +
      e.gammaFull k o.1 * continuousFullOutcomeResidual L e true k o -
      e.gammaFull k o.1 * continuousFullOutcomeResidual L e false k o +
      (e.gammaFull k o.1 * fullValue e.JfullPlus k o.1) * RpCont L e (k.val+1) o -
      (e.gammaFull k o.1 * minusFullValue e k o.1) * RpCont L e k o := by
  have hg : fullValue e.gammaFull k o.1 = e.gammaFull k o.1 := by
    simp only [fullValue, dif_pos k.isLt]
  rw [psiFullProd, hg]
  linear_combination e.gammaFull k o.1 *
    continuous_full_score_correction_decomposition L e k o

-- @node: fitted_continuous_full_score_product_memLp
/-- Assume [admissibility of the fitted nuisances](hyp:he), [the potential-outcome
support restriction](hyp:hp), [consistency](hyp:hcons), and [known outcome endpoints](hyp:hend).
If [the clipping constant is positive](hyp:hc) and [all fitted assignment
probabilities are almost surely at least that constant](hyp:hclip), then [each
fitted full-interval product score has a finite second moment under the observation
distribution](goal). -/
lemma fitted_continuous_full_score_product_memLp (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e)
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (k : Fin L.K) : MemLp (psiFullProd L e k) 2 (observationLaw M) := by
  have hm := ((((fitted_continuous_full_event_memLp M L e he k).add
    (fitted_continuous_weighted_full_residual_memLp M L e he hp hcons hend
      c hc hclip true k)).sub
    (fitted_continuous_weighted_full_residual_memLp M L e he hp hcons hend
      c hc hclip false k)).add
    (fitted_continuous_full_treatment_correction_memLp M L e he c hc hclip true k)).sub
    (fitted_continuous_full_treatment_correction_memLp M L e he c hc hclip false k)
  convert hm using 1
  funext o
  simp only [Pi.sub_apply, Pi.add_apply,
    continuous_full_product_correction_decomposition, Bool.true_eq, Bool.false_eq_true,
    if_true, if_false]

-- @node: nuisanceRates_continuous_full_score_product_sq_tendsto_probability_zero
/-- For [a sequence of fitted continuous nuisances](hyp:eh), assume [reference
admissibility](hyp:he0), [admissibility of every fit](hyp:heh), [the potential-outcome
support restriction](hyp:hp), [consistency](hyp:hcons), and [known outcome endpoints](hyp:hend).
Under [a positive clipping constant](hyp:hc), [a common almost-sure lower bound
on reference and fitted assignment probabilities](hyp:hclip), and finite nuisance
rate conditions for [treatment probabilities](hyp:hrp), [assignment probabilities](hyp:hrpi),
[upper regressions](hyp:hrplus), [lower regressions](hyp:hrminus), and [signed
weights](hyp:hrg), [the observation-integrated squared error of each full-interval
product score converges in probability to zero, using fits at sample sizes twice
one plus the sequence index](goal). -/
lemma nuisanceRates_continuous_full_score_product_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrplus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullPlus) e0.JfullPlus)
    (hrminus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullMinus) e0.JfullMinus)
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gammaFull) e0.gammaFull)
    (k : Fin L.K) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o,
        (psiFullProd L (eh (2*(n+1)) a) k o - psiFullProd L e0 k o)^2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  let piece := fun (e : NuisanceCont L) (i : Fin 5) (o : Obs X Z) =>
    match i.val with
    | 0 => (indicator (o.2.1 ∈ higherPolicy L k) -
        indicator (o.2.1 ∈ higherBaseline L k)) * contFullJ L e k o.1
    | 1 => e.gammaFull k o.1 * continuousFullOutcomeResidual L e true k o
    | 2 => -(e.gammaFull k o.1 * continuousFullOutcomeResidual L e false k o)
    | 3 => (e.gammaFull k o.1 * fullValue e.JfullPlus k o.1) * RpCont L e (k.val+1) o
    | _ => -((e.gammaFull k o.1 * minusFullValue e k o.1) * RpCont L e k o)
  have hm (e : NuisanceCont L) (he : ContAdmissible M L e)
      (hcl : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
      (i : Fin 5) : MemLp (piece e i) 2 (observationLaw M) := by
    fin_cases i
    · exact fitted_continuous_full_event_memLp M L e he k
    · exact fitted_continuous_weighted_full_residual_memLp M L e he hp hcons hend
        c hc hcl true k
    · exact (fitted_continuous_weighted_full_residual_memLp M L e he hp hcons hend
        c hc hcl false k).neg
    · exact fitted_continuous_full_treatment_correction_memLp M L e he c hc hcl true k
    · exact (fitted_continuous_full_treatment_correction_memLp M L e he c hc hcl false k).neg
  have hr (i : Fin 5) :
      Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
        (fun n a => ∫ o, (piece (eh (2*(n+1)) a) i o - piece e0 i o)^2
          ∂observationLaw M) atTop (fun _ _ => 0) := by
    fin_cases i
    · simpa only [piece, mul_sub] using
        nuisanceRates_continuous_full_event_sq_tendsto_probability_zero M μ L e0 eh
          he0 heh hrp hrplus hrminus k
    · exact nuisanceRates_continuous_weighted_full_residual_sq_tendsto_probability_zero
        M μ L e0 eh he0 heh hp hcons hend c hc hclip hrpi hrplus hrminus hrg true k
    · simpa only [piece, Bool.false_eq_true, if_false, neg_sub_neg, sub_sq_comm] using
        nuisanceRates_continuous_weighted_full_residual_sq_tendsto_probability_zero
          M μ L e0 eh he0 heh hp hcons hend c hc hclip hrpi hrplus hrminus hrg false k
    · exact nuisanceRates_continuous_full_treatment_correction_sq_tendsto_probability_zero
        M μ L e0 eh he0 heh c hc hclip hrp hrpi hrplus hrminus hrg true k
    · simpa only [piece, Bool.false_eq_true, if_false, neg_sub_neg, sub_sq_comm] using
        nuisanceRates_continuous_full_treatment_correction_sq_tendsto_probability_zero
          M μ L e0 eh he0 heh c hc hclip hrp hrpi hrplus hrminus hrg false k
  have hs := dml_finset_sum_sq_tendsto_probability_zero μ (observationLaw M)
    Finset.univ (fun i n a o => piece (eh (2*(n+1)) a) i o - piece e0 i o)
    (fun i _ n a => (hm _ (heh _ a)
      (fun j => (hclip _ a j).mono (fun _ hx => hx.2)) i).sub
      (hm e0 he0 (fun j => (hclip (2*(n+1)) a j).mono (fun _ hx => hx.1)) i))
    (fun i _ => hr i)
  have hsum (e : NuisanceCont L) (o : Obs X Z) :
      (∑ i : Fin 5, piece e i o) = psiFullProd L e k o := by
    rw [continuous_full_product_correction_decomposition]
    simp [Fin.sum_univ_succ, piece]
    <;> ring
  simpa only [Finset.sum_sub_distrib, hsum] using hs


-- @node: fitted_continuous_full_score_block_memLp
/-- Under [admissibility of the fitted nuisances](hyp:he), [the potential-outcome
support restriction](hyp:hp), [consistency](hyp:hcons), [known outcome endpoints](hyp:hend),
[a positive clipping constant](hyp:hc), and [an almost-sure lower bound by that
constant on all fitted assignment probabilities](hyp:hclip), [the sum of fitted
full-interval product scores over all nonterminal levels has a finite second
moment under the observation distribution](goal). -/
lemma fitted_continuous_full_score_block_memLp (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e)
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) :
    MemLp (fun o => ∑ k ∈ Finset.range L.K, psiFullProd L e k o)
      2 (observationLaw M) := by
  apply memLp_finsetSum
  intro k hk
  exact fitted_continuous_full_score_product_memLp M L e he hp hcons hend c hc hclip
    ⟨k, Finset.mem_range.mp hk⟩

-- @node: nuisanceRates_continuous_full_score_block_sq_tendsto_probability_zero
/-- For [a sequence of fitted continuous nuisances](hyp:eh), suppose [the reference
nuisances are admissible](hyp:he0), [all fits are admissible](hyp:heh), [potential
outcomes obey the support restriction](hyp:hp), [consistency holds](hyp:hcons), and
[the outcome endpoints are known](hyp:hend). If [the clipping constant is positive](hyp:hc),
[reference and fitted assignment probabilities share that almost-sure lower bound](hyp:hclip),
and [treatment probabilities](hyp:hrp), [assignment probabilities](hyp:hrpi),
[upper regressions](hyp:hrplus), [lower regressions](hyp:hrminus), and [signed
weights](hyp:hrg) satisfy their finite nuisance rate conditions, then [the
observation-integrated squared error of the sum of full-interval product scores
over all nonterminal levels converges in probability to zero, using fits at sample
sizes twice one plus the sequence index](goal). -/
lemma nuisanceRates_continuous_full_score_block_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrplus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullPlus) e0.JfullPlus)
    (hrminus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullMinus) e0.JfullMinus)
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gammaFull) e0.gammaFull) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o,
        ((∑ k ∈ Finset.range L.K, psiFullProd L (eh (2*(n+1)) a) k o) -
          ∑ k ∈ Finset.range L.K, psiFullProd L e0 k o)^2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  have hs := dml_finset_sum_sq_tendsto_probability_zero μ (observationLaw M)
    (Finset.range L.K) (fun k n a o =>
      psiFullProd L (eh (2*(n+1)) a) k o - psiFullProd L e0 k o)
    (fun k hk n a =>
      (fitted_continuous_full_score_product_memLp M L _ (heh _ a) hp hcons hend c hc
        (fun i => (hclip _ a i).mono (fun _ hx => hx.2))
        ⟨k, Finset.mem_range.mp hk⟩).sub
      (fitted_continuous_full_score_product_memLp M L e0 he0 hp hcons hend c hc
        (fun i => (hclip (2*(n+1)) a i).mono (fun _ hx => hx.1))
        ⟨k, Finset.mem_range.mp hk⟩))
    (fun k hk => nuisanceRates_continuous_full_score_product_sq_tendsto_probability_zero
      M μ L e0 eh he0 heh hp hcons hend c hc hclip hrp hrpi hrplus hrminus hrg
        ⟨k, Finset.mem_range.mp hk⟩)
  simpa only [Finset.sum_sub_distrib] using hs

-- @node: nuisanceRates_continuous_full_score_block_l2_tendsto_probability_zero
/-- For [a sequence of fitted continuous nuisances](hyp:eh), assume [reference
admissibility](hyp:he0), [admissibility of every fit](hyp:heh), [the potential-outcome
support restriction](hyp:hp), [consistency](hyp:hcons), and [known outcome endpoints](hyp:hend).
Under [a positive clipping constant](hyp:hc), [a common almost-sure lower bound
on reference and fitted assignment probabilities](hyp:hclip), and finite nuisance
rate conditions for [treatment probabilities](hyp:hrp), [assignment probabilities](hyp:hrpi),
[upper regressions](hyp:hrplus), [lower regressions](hyp:hrminus), and [signed
weights](hyp:hrg), [the square root of the observation-integrated squared error
of the sum of full-interval product scores over all nonterminal levels converges
in probability to zero, using fits at sample sizes twice one plus the sequence
index](goal). -/
lemma nuisanceRates_continuous_full_score_block_l2_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hp : PotentialSupport M) (hcons : Consistency M) (hend : OutcomeEndpointsKnown M)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrplus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullPlus) e0.JfullPlus)
    (hrminus : FiniteNuisanceRates M μ (fun n a => (eh n a).JfullMinus) e0.JfullMinus)
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gammaFull) e0.gammaFull) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt (∫ o,
        ((∑ k ∈ Finset.range L.K, psiFullProd L (eh (2*(n+1)) a) k o) -
          ∑ k ∈ Finset.range L.K, psiFullProd L e0 k o)^2
        ∂observationLaw M)) atTop (fun _ _ => 0) := by
  have hs := nuisanceRates_continuous_full_score_block_sq_tendsto_probability_zero
    M μ L e0 eh he0 heh hp hcons hend c hc hclip hrp hrpi hrplus hrminus hrg
  have hcont : Continuous (fun t : ℝ => Real.sqrt t) := by fun_prop
  simpa only [Real.sqrt_zero] using
    Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt hcont.continuousAt hs


end Papers.TbsPrteOptimalTransport
