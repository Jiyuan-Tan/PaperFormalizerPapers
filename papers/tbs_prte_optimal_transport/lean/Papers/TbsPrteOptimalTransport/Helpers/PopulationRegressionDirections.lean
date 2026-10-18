module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationAssignmentResidual
/-! Regression-direction regularity and full-product cancellation derived from admissibility. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set
open scoped Classical
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- Two admissible points of one affine path control every regression direction.
-- @node: binary_regression_direction_regular
/-- If [a binary nuisance direction admits a local admissible path from the given nuisance](hyp:hd),
[all its positive-level treated-success regression directions are measurable and share a
nonnegative almost-sure bound under the covariate distribution](goal). -/
lemma binary_regression_direction_regular (L : LevelData Z X) (eta del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr eta) (.inr del)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : PositiveIndex L.K,
      Measurable (del.P1 a) ∧ ∀ᵐ x ∂xLaw M, ‖del.P1 a x‖ ≤ C := by
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  have h0 := hpath 0 (by simpa using hr)
  have ht := hpath (r / 2) (by rw [abs_of_pos (by positivity)]; linarith)
  refine ⟨2 / r, by positivity, ?_⟩
  intro a
  have hm0 : Measurable (eta.P1 a) := by
    have hm : Measurable (fun x => eta.P1 a x + 0 * del.P1 a x) :=
      (h0.2.2.2.1 a).2.1
    simpa only [zero_mul, add_zero] using hm
  have hmt : Measurable (fun x => eta.P1 a x + (r / 2) * del.P1 a x) :=
    (ht.2.2.2.1 a).2.1
  constructor
  · have hid : del.P1 a = fun x =>
        ((eta.P1 a x + (r / 2) * del.P1 a x) - eta.P1 a x) / (r / 2) := by
      funext x
      field_simp
      <;> ring
    rw [hid]
    exact (hmt.sub hm0).div_const _
  · filter_upwards [h0.2.2.1 a, ht.2.2.1 a] with x hx0 hxt
    have hb0 : eta.P1 a x + 0 * del.P1 a x ∈ Icc (0 : ℝ) 1 := hx0.2.1
    have hbt : eta.P1 a x + (r / 2) * del.P1 a x ∈ Icc (0 : ℝ) 1 := hxt.2.1
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · rw [← neg_div, div_le_iff₀ hr]
      nlinarith [hb0.1, hb0.2, hbt.1, hbt.2]
    · apply (le_div_iff₀ hr).2
      nlinarith [hb0.1, hb0.2, hbt.1, hbt.2]

-- The structural zero boundary is included without introducing a P1_0 direction.
-- @node: binary_positive_regression_direction_regular
/-- If [the common bound is nonnegative](hyp:hC) and [each positive-level direction is
measurable and almost surely bounded by it](hyp:hd), then [the direction extended by zero
outside the positive levels is measurable and obeys the same bound at every index](goal). -/
lemma binary_positive_regression_direction_regular (L : LevelData Z X)
    (d : PositiveIndex L.K → X → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hd : ∀ a, Measurable (d a) ∧ ∀ᵐ x ∂xLaw M, ‖d a x‖ ≤ C) (k : ℕ) :
    Measurable (positiveValue d k) ∧
      ∀ᵐ x ∂xLaw M, ‖positiveValue d k x‖ ≤ C := by
  change Measurable (fun x => positiveValue d k x) ∧ _
  by_cases hk : 1 ≤ k ∧ k ≤ L.K
  · simpa only [positiveValue, dif_pos hk] using hd ⟨k, hk⟩
  · simp only [positiveValue, dif_neg hk]
    exact ⟨measurable_const, Filter.Eventually.of_forall (fun _ => by simpa using hC)⟩

-- Overlap bounds the reciprocal assignment probability. This is an analytic
-- prerequisite, derived here rather than imposed on the orthogonality theorem.
-- @node: population_normalized_assignment_integrable
/-- If [the overlap constant is positive](hyp:hc), [the conditional probability of the
instrument set is everywhere at least that constant](hyp:hp), [the covariate weight is
measurable](hyp:hw), and [its absolute value is almost surely bounded by a fixed
constant](hyp:hb), then [the weight times one minus the instrument-set indicator divided
by its conditional probability is integrable under the observation distribution](goal). -/
lemma population_normalized_assignment_integrable (C : Finset Z) (c : ℝ) (hc : 0 < c)
    (hp : ∀ x, c ≤ ∑ z ∈ C, instProb M z x)
    (w : X → ℝ) (hw : Measurable w) (B : ℝ)
    (hb : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ B) :
    Integrable (fun o : Obs X Z => w o.1 *
      (1 - indicator (o.2.1 ∈ C) / (∑ z ∈ C, instProb M z o.1)))
      (observationLaw M) := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  let p := fun x => ∑ z ∈ C, instProb M z x
  have hpm : Measurable p := by fun_prop
  have hC : MeasurableSet (C : Set Z) := C.finite_toSet.measurableSet
  have hi : Measurable (fun o : Obs X Z => indicator (o.2.1 ∈ C)) := by
    unfold indicator
    exact Measurable.ite (hC.preimage measurable_snd.fst) measurable_const measurable_const
  have hm : Measurable (fun o : Obs X Z => 1 - indicator (o.2.1 ∈ C) / p o.1) := by
    fun_prop
  have hbase : Integrable (fun o : Obs X Z => 1 - indicator (o.2.1 ∈ C) / p o.1)
      (observationLaw M) := by
    apply (integrable_const (1 + 1 / c : ℝ)).mono' hm.aestronglyMeasurable
    filter_upwards [] with o
    have hp0 : 0 < p o.1 := hc.trans_le (hp o.1)
    have hib : |indicator (o.2.1 ∈ C)| ≤ 1 := by
      unfold indicator
      split_ifs <;> norm_num
    rw [Real.norm_eq_abs]
    calc
      |1 - indicator (o.2.1 ∈ C) / p o.1| ≤ 1 + |indicator (o.2.1 ∈ C) / p o.1| := by
        simpa only [Real.norm_eq_abs, abs_one] using
          norm_sub_le (1 : ℝ) (indicator (o.2.1 ∈ C) / p o.1)
      _ ≤ 1 + 1 / p o.1 := by
        rw [abs_div, abs_of_pos hp0]
        gcongr
      _ ≤ 1 + 1 / c := by gcongr; exact hp o.1
  exact hbase.bdd_mul (hw.comp measurable_fst).aestronglyMeasurable
    (observationLaw_covariate_ae M _ hb)

-- @node: population_assignment_residual_integrable
/-- If [a covariate weight is measurable](hyp:hw) and [almost surely bounded in absolute
value by a fixed constant](hyp:hb), then [its product with the instrument-set indicator
minus that set's conditional probability is integrable under the observation distribution](goal). -/
lemma population_assignment_residual_integrable (C : Finset Z)
    (w : X → ℝ) (hw : Measurable w) (B : ℝ)
    (hb : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ B) :
    Integrable (fun o : Obs X Z => w o.1 *
      (indicator (o.2.1 ∈ C) - ∑ z ∈ C, instProb M z o.1)) (observationLaw M) := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  have hC : MeasurableSet (C : Set Z) := C.finite_toSet.measurableSet
  have hi : Measurable (fun o : Obs X Z => indicator (o.2.1 ∈ C)) := by
    unfold indicator
    exact Measurable.ite (hC.preimage measurable_snd.fst) measurable_const measurable_const
  have hp := population_instrument_set_probability_measurable M C
  have hm : Measurable (fun o : Obs X Z => indicator (o.2.1 ∈ C) -
      ∑ z ∈ C, instProb M z o.1) := hi.sub (hp.comp measurable_fst)
  have hbase : Integrable (fun o : Obs X Z => indicator (o.2.1 ∈ C) -
      ∑ z ∈ C, instProb M z o.1) (observationLaw M) := by
    apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    filter_upwards [] with o
    have hp := population_instrument_set_probability_range M C o.1
    rw [Real.norm_eq_abs, abs_le]
    unfold indicator
    split_ifs <;> constructor <;> linarith [hp.1, hp.2]
  exact hbase.bdd_mul (hw.comp measurable_fst).aestronglyMeasurable
    (observationLaw_covariate_ae M _ hb)

-- Every analytic premise of the full-product regression cancellation is now
-- supplied by overlap, the binary outcome, and the admissible local path.
-- @node: population_binary_full_product_regression_orthogonality_of_admissible
/-- Under [baseline overlap](hyp:hov) and [an almost surely binary outcome](hyp:hy),
if [the binary nuisance direction is admissible at the population nuisance](hyp:hd),
then [the population mean of the full-interval binary product score has derivative zero
at zero along the path perturbing only the treated-success regressions](goal). -/
lemma population_binary_full_product_regression_orthogonality_of_admissible
    (L : LevelData Z X) (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hy : OutcomeBinaryAE M) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del)) (k : Fin L.K) :
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
      psiFullProdBin L {eta0Bin M L with
        P1 := fun a x => (eta0Bin M L).P1 a x + t * del.P1 a x} k o ∂observationLaw M) 0 0 := by
  have he := binary_admissible_direction_origin M L (eta0Bin M L) del hd
  obtain ⟨C, hC, hdreg⟩ := binary_regression_direction_regular M L (eta0Bin M L) del hd
  have hpos (i : ℕ) := binary_positive_regression_direction_regular M L del.P1 C hC hdreg i
  have hg : Measurable (gammaFull M L k) := he.2.2.2.2.2.2.2.2.2.2.1 k
  have hgb : ∀ᵐ x ∂xLaw M, ‖gammaFull M L k x‖ ≤ 1 := by
    filter_upwards [he.2.2.2.2.2.2.2.2.2.1 k] with x hx
    simpa only [eta0Bin, Set.mem_Icc, Real.norm_eq_abs, abs_le] using hx
  have hgdir (i : ℕ) : ∀ᵐ x ∂xLaw M,
      ‖gammaFull M L k x * positiveValue del.P1 i x‖ ≤ C := by
    filter_upwards [hgb, (hpos i).2] with x hx hd
    rw [norm_mul]
    calc
      _ ≤ 1 * C := mul_le_mul hx hd (norm_nonneg _) (by norm_num)
      _ = C := one_mul C
  have hnorm (i : ℕ) (hi : 1 ≤ i ∧ i ≤ L.K) :
      Integrable (fun o : Obs X Z => (gammaFull M L k o.1 * positiveValue del.P1 i o.1) *
        (1 - indicator (o.2.1 ∈ L.S i) / positiveValue (eta0Bin M L).piLev i o.1))
        (observationLaw M) := by
    have hpdef : ∀ x, positiveValue (eta0Bin M L).piLev i x =
        ∑ z ∈ L.S i, instProb M z x := by
      intro x
      simp only [positiveValue, dif_pos hi, eta0Bin, levelSetProb]
    simp_rw [hpdef]
    exact population_normalized_assignment_integrable M (L.S i) cpi hov.1
      (fun x => hov.2 x i hi.1 hi.2) _ (hg.mul (hpos i).1) C (hgdir i)
  have ip := hnorm (k+1) (by omega)
  have im : Integrable (fun o : Obs X Z => (gammaFull M L k o.1 * positiveValue del.P1 k o.1) *
      (1 - (if k.val = 0 then 1 else indicator (o.2.1 ∈ L.S k) /
        positiveValue (eta0Bin M L).piLev k o.1))) (observationLaw M) := by
    by_cases hk : k.val = 0
    · simp only [hk, if_true, sub_self, mul_zero]
      haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
      exact integrable_const (0 : ℝ)
    · simpa only [if_neg hk] using hnorm k (by omega)
  have iJ := population_binary_full_contrast_integrable M L he k
  have iRp := population_binary_RP_integrable M L cpi hov hy he (k+1)
  have iRm := population_binary_RP_integrable M L cpi hov hy he k
  have iscore : Integrable (fun o : Obs X Z => gammaFull M L k o.1 *
      (binFullJ L (eta0Bin M L) k o.1 + RP L (eta0Bin M L) (k+1) o -
        RP L (eta0Bin M L) k o)) (observationLaw M) :=
    ((iJ.add iRp).sub' iRm).bdd_mul (hg.comp measurable_fst).aestronglyMeasurable
      (observationLaw_covariate_ae M _ hgb)
  let r : Obs X Z → ℝ := fun o => indicator (o.2.1 ∈ higherPolicy L k) -
    indicator (o.2.1 ∈ higherBaseline L k) - gammaFull M L k o.1
  have hr : Measurable r := by
    have hA : Measurable (fun o : Obs X Z => indicator (o.2.1 ∈ higherPolicy L k)) := by
      unfold indicator
      exact Measurable.ite ((higherPolicy L k).finite_toSet.measurableSet.preimage
        measurable_snd.fst) measurable_const measurable_const
    have hB : Measurable (fun o : Obs X Z => indicator (o.2.1 ∈ higherBaseline L k)) := by
      unfold indicator
      exact Measurable.ite ((higherBaseline L k).finite_toSet.measurableSet.preimage
        measurable_snd.fst) measurable_const measurable_const
    exact (hA.sub hB).sub (hg.comp measurable_fst)
  have hrb : ∀ᵐ o ∂observationLaw M, ‖r o‖ ≤ 3 := by
    filter_upwards [observationLaw_covariate_ae M _ hgb] with o ho
    have hA : ‖indicator (o.2.1 ∈ higherPolicy L k)‖ ≤ 1 := by
      unfold indicator
      split_ifs <;> norm_num
    have hB : ‖indicator (o.2.1 ∈ higherBaseline L k)‖ ≤ 1 := by
      unfold indicator
      split_ifs <;> norm_num
    calc
      ‖r o‖ ≤ ‖indicator (o.2.1 ∈ higherPolicy L k) -
        indicator (o.2.1 ∈ higherBaseline L k)‖ + ‖gammaFull M L k o.1‖ := norm_sub_le _ _
      _ ≤ (‖indicator (o.2.1 ∈ higherPolicy L k)‖ +
        ‖indicator (o.2.1 ∈ higherBaseline L k)‖) + ‖gammaFull M L k o.1‖ := by
          gcongr; exact norm_sub_le _ _
      _ ≤ 3 := by linarith
  have ibase := iJ.mul_bdd hr.aestronglyMeasurable hrb
  have hdm : Measurable (fun x => positiveValue del.P1 (k+1) x - positiveValue del.P1 k x) :=
    (hpos (k+1)).1.sub (hpos k).1
  have hdb : ∀ᵐ x ∂xLaw M,
      ‖positiveValue del.P1 (k+1) x - positiveValue del.P1 k x‖ ≤ 2 * C := by
    filter_upwards [(hpos (k+1)).2, (hpos k).2] with x hp hm
    calc
      _ ≤ ‖positiveValue del.P1 (k+1) x‖ + ‖positiveValue del.P1 k x‖ := norm_sub_le _ _
      _ ≤ 2 * C := by linarith
  have iA := population_assignment_residual_integrable M (higherPolicy L k) _ hdm (2*C) hdb
  have iB := population_assignment_residual_integrable M (higherBaseline L k) _ hdm (2*C) hdb
  exact population_binary_full_product_regression_orthogonality M L cpi hov del.P1 k
    (fun a => (hdreg a).1) iscore ip im ibase iA iB

end Papers.TbsPrteOptimalTransport
