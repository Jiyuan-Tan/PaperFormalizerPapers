module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationBinaryDenominatorProducts
public import Papers.TbsPrteOptimalTransport.Helpers.JointFullRegressionWeights
/-! Local denominator orthogonality with regularity derived from admissibility. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: binary_assignment_denominator_direction_regular
/-- If [a binary nuisance direction is admissible at the given nuisance value](hyp:hd),
[all its assignment-probability components are measurable and share a finite nonnegative bound in absolute value almost everywhere under the covariate law](goal). -/
lemma binary_assignment_denominator_direction_regular (L : LevelData Z X)
    (eta del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr eta) (.inr del)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : PositiveIndex L.K,
      Measurable (del.piLev a) ∧ ∀ᵐ x ∂xLaw M, ‖del.piLev a x‖ ≤ C := by
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  have h0 := hpath 0 (by simpa using hr)
  have ht := hpath (r / 2) (by rw [abs_of_pos (by positivity)]; linarith)
  refine ⟨2 / r, by positivity, ?_⟩
  intro a
  have hm0 : Measurable (eta.piLev a) := by
    have hm : Measurable (fun x => eta.piLev a x + 0 * del.piLev a x) :=
      (h0.2.2.2.1 a).2.2
    simpa only [zero_mul, add_zero] using hm
  have hmt : Measurable (fun x => eta.piLev a x + (r / 2) * del.piLev a x) :=
    (ht.2.2.2.1 a).2.2
  constructor
  · have hid : del.piLev a = fun x =>
        ((eta.piLev a x + (r / 2) * del.piLev a x) - eta.piLev a x) / (r / 2) := by
      funext x
      field_simp
      <;> ring
    rw [hid]
    exact (hmt.sub hm0).div_const _
  · filter_upwards [h0.2.2.1 a, ht.2.2.1 a] with x hx0 hxt
    have hb0 : eta.piLev a x + 0 * del.piLev a x ∈ Icc (0 : ℝ) 1 := hx0.2.2
    have hbt : eta.piLev a x + (r / 2) * del.piLev a x ∈ Icc (0 : ℝ) 1 := hxt.2.2
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · rw [← neg_div, div_le_iff₀ hr]
      nlinarith [hb0.1, hb0.2, hbt.1, hbt.2]
    · apply (le_div_iff₀ hr).2
      nlinarith [hb0.1, hb0.2, hbt.1, hbt.2]

-- A bounded reciprocal transfers integrability from the population residual.
-- @node: population_binary_RP_fitted_denominator_integrable
/-- Assume [baseline overlap with the specified bound](hyp:hov), [an almost surely binary outcome](hyp:hy),
and [admissibility of the true binary nuisance](hyp:he). If [each fitted assignment probability is measurable](hyp:hpi)
and [the common lower bound is positive](hyp:hc) and [bounds every fitted probability from below almost everywhere](hyp:hp),
[the population assignment residual using those fitted denominators is integrable at every level index](goal). -/
lemma population_binary_RP_fitted_denominator_integrable
    (L : LevelData Z X) (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hy : OutcomeBinaryAE M) (he : BinAdmissible M L (eta0Bin M L))
    (pi : PositiveIndex L.K → X → ℝ) (hpi : ∀ a, Measurable (pi a))
    (c : ℝ) (hc : 0 < c) (hp : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ pi a x) (i : ℕ) :
    Integrable (RP L {eta0Bin M L with piLev := pi} i) (observationLaw M) := by
  by_cases hi : 1 ≤ i ∧ i ≤ L.K
  · let a : PositiveIndex L.K := ⟨i, hi⟩
    let w : X → ℝ := fun x => (eta0Bin M L).piLev a x / pi a x
    have hw : Measurable w := (he.2.2.2.1 a).2.2.div (hpi a)
    have hb : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ 1 / c := by
      filter_upwards [hp a, he.2.2.1 a] with x hx heX
      have htrue : (eta0Bin M L).piLev a x ∈ Icc (0 : ℝ) 1 := heX.2.2
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg htrue.1, abs_of_pos (hc.trans_le hx)]
      exact (div_le_div_of_nonneg_right htrue.2 (hc.trans_le hx).le).trans
        (div_le_div_of_nonneg_left zero_le_one hc hx)
    have iw := (population_binary_RP_integrable M L cpi hov hy he i).bdd_mul
      (hw.comp measurable_fst).aestronglyMeasurable (observationLaw_covariate_ae M _ hb)
    apply iw.congr
    filter_upwards [observationLaw_covariate_ae M _ (hp a)] with o ho
    have ht : 0 < positiveValue (eta0Bin M L).piLev i o.1 := by
      simpa only [positiveValue, dif_pos hi, eta0Bin] using
        hov.1.trans_le (hov.2 o.1 i hi.1 hi.2)
    have hf : 0 < pi a o.1 := hc.trans_le ho
    dsimp only [Function.comp_apply, w]
    simp only [RP, if_neg (show i ≠ 0 by omega), positiveValue, dif_pos hi]
    simp only [positiveValue, dif_pos hi] at ht
    change 0 < pi ⟨i, hi⟩ o.1 at hf
    dsimp only [a]
    field_simp [ne_of_gt ht, ne_of_gt hf]
  · have hz : RP L {eta0Bin M L with piLev := pi} i = fun _ => (0 : ℝ) := by
      funext o
      by_cases hi0 : i = 0 <;> simp [RP, hi0, positiveValue, hi]
    rw [hz]
    exact integrable_zero _ _ _

-- The complete full-product expectation is unchanged under any such update.
-- @node: population_binary_full_product_fitted_denominator_mean
/-- Under [baseline overlap](hyp:hov), [an almost surely binary outcome](hyp:hy),
and [admissibility of the true binary nuisance](hyp:he), suppose
[the fitted assignment probabilities are measurable](hyp:hpi) and
[have a positive common lower bound](hyp:hc) [almost everywhere for every level](hyp:hp).
Then [each full-product score with those fitted denominators is integrable and has the same population mean as the score at the true nuisance](goal). -/
lemma population_binary_full_product_fitted_denominator_mean
    (L : LevelData Z X) (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hy : OutcomeBinaryAE M) (he : BinAdmissible M L (eta0Bin M L))
    (pi : PositiveIndex L.K → X → ℝ) (hpi : ∀ a, Measurable (pi a))
    (c : ℝ) (hc : 0 < c) (hp : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ pi a x) (k : Fin L.K) :
    Integrable (psiFullProdBin L {eta0Bin M L with piLev := pi} k) (observationLaw M) ∧
    (∫ o, psiFullProdBin L {eta0Bin M L with piLev := pi} k o ∂observationLaw M) =
      ∫ o, psiFullProdBin L (eta0Bin M L) k o ∂observationLaw M := by
  have hg : Measurable (fullValue (eta0Bin M L).gammaFull k) := by
    change Measurable (fun x => fullValue (eta0Bin M L).gammaFull k x)
    simpa only [fullValue, dif_pos k.isLt] using he.2.2.2.2.2.2.2.2.2.2.1 k
  have hb : ∀ᵐ x ∂xLaw M, ‖fullValue (eta0Bin M L).gammaFull k x‖ ≤ 1 := by
    filter_upwards [he.2.2.2.2.2.2.2.2.2.1 k] with x hx
    simpa only [fullValue, dif_pos k.isLt, Real.norm_eq_abs, abs_le, mem_Icc] using hx
  have ip i := (population_binary_RP_fitted_denominator_integrable M L cpi hov hy he
    pi hpi c hc hp i).bdd_mul (hg.comp measurable_fst).aestronglyMeasurable
      (observationLaw_covariate_ae M _ hb)
  obtain ⟨ic, zc⟩ := population_binary_full_denominator_correction_zero M L pi hpi k
    (fullValue (eta0Bin M L).gammaFull k) hg (ip (k+1)) (ip k)
  have ip0 i := population_binary_weighted_RP_integrable M L cpi hov hy he i
    (fullValue (eta0Bin M L).gammaFull k) hg 1 hb
  obtain ⟨ic0, zc0⟩ := population_binary_full_denominator_correction_zero M L
    (eta0Bin M L).piLev (fun a => (he.2.2.2.1 a).2.2) k
    (fullValue (eta0Bin M L).gammaFull k) hg (ip0 (k+1)) (ip0 k)
  change Integrable (fun o : Obs X Z => fullValue (eta0Bin M L).gammaFull k o.1 *
    (RP L (eta0Bin M L) (k+1) o - RP L (eta0Bin M L) k o)) (observationLaw M) at ic0
  change (∫ o : Obs X Z, fullValue (eta0Bin M L).gammaFull k o.1 *
    (RP L (eta0Bin M L) (k+1) o - RP L (eta0Bin M L) k o) ∂observationLaw M) = 0 at zc0
  have ib := population_binary_full_product_integrable_of_overlap M L cpi hov hy he k
  have hid : (fun o => psiFullProdBin L {eta0Bin M L with piLev := pi} k o) =
      (fun o => psiFullProdBin L (eta0Bin M L) k o +
        fullValue (eta0Bin M L).gammaFull k o.1 *
          (RP L {eta0Bin M L with piLev := pi} (k+1) o -
            RP L {eta0Bin M L with piLev := pi} k o) -
        fullValue (eta0Bin M L).gammaFull k o.1 *
          (RP L (eta0Bin M L) (k+1) o - RP L (eta0Bin M L) k o)) := by
    funext o
    dsimp only [psiFullProdBin, binFullJ]
    ring
  constructor
  · change Integrable (fun o => psiFullProdBin L _ k o) _
    rw [hid]
    exact (ib.fun_add ic).sub' ic0
  · rw [hid, integral_sub (ib.fun_add ic) ic0, integral_add ib ic, zc, zc0,
      add_zero, sub_zero]

-- @node: population_binary_full_product_denominator_orthogonality_of_admissible
/-- Under [baseline overlap](hyp:hov) and [an almost surely binary outcome](hyp:hy),
if [the nuisance direction is admissible at the true binary nuisance](hyp:hd),
[the population mean of each full-product score has derivative zero at zero when only its assignment denominators move linearly along that direction](goal). -/
lemma population_binary_full_product_denominator_orthogonality_of_admissible
    (L : LevelData Z X) (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hy : OutcomeBinaryAE M) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del)) (k : Fin L.K) :
    HasDerivAt (fun t : ℝ => ∫ o, psiFullProdBin L {eta0Bin M L with
      piLev := fun a x => (eta0Bin M L).piLev a x + t * del.piLev a x} k o
      ∂observationLaw M) 0 0 := by
  have he := binary_admissible_direction_origin M L (eta0Bin M L) del hd
  obtain ⟨C, hC, hr⟩ := binary_assignment_denominator_direction_regular M L
    (eta0Bin M L) del hd
  have hcpi := hov.1
  have radius : 0 < cpi / (2 * (C+1)) := by positivity
  apply (hasDerivAt_const (0 : ℝ)
    (∫ o, psiFullProdBin L (eta0Bin M L) k o ∂observationLaw M)).congr_of_eventuallyEq
  filter_upwards [continuousAt_id.abs.eventually_lt_const (by simpa using radius)] with t ht
  apply (population_binary_full_product_fitted_denominator_mean M L cpi hov hy he
    (fun a x => (eta0Bin M L).piLev a x + t * del.piLev a x)
    (fun a => ((he.2.2.2.1 a).2.2).add ((hr a).1.const_mul t))
    (cpi / 2) (by linarith [hov.1]) ?_ k).2
  intro a
  filter_upwards [(hr a).2] with x hx
  have hp : cpi ≤ (eta0Bin M L).piLev a x := hov.2 x a.val a.property.1 a.property.2
  have heprod : |t * del.piLev a x| ≤ |t| * C := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hx) (abs_nonneg t)
  have ht' : |t| * (2 * (C+1)) < cpi := (lt_div_iff₀ (by positivity)).mp ht
  have hlow := neg_abs_le (t * del.piLev a x)
  nlinarith [abs_nonneg t]

-- @node: population_binary_full_sum_denominator_orthogonality_of_admissible
/-- Under [baseline overlap](hyp:hov) and [an almost surely binary outcome](hyp:hy),
if [the nuisance direction is admissible at the true binary nuisance](hyp:hd),
[the population mean of the sum of all full-product scores has derivative zero at zero when only the assignment denominators move linearly along that direction](goal). -/
lemma population_binary_full_sum_denominator_orthogonality_of_admissible
    (L : LevelData Z X) (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hy : OutcomeBinaryAE M) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del)) :
    HasDerivAt (fun t : ℝ => ∫ o, ∑ k ∈ Finset.range L.K,
      psiFullProdBin L {eta0Bin M L with
        piLev := fun a x => (eta0Bin M L).piLev a x + t * del.piLev a x} k o
      ∂observationLaw M) 0 0 := by
  have he := binary_admissible_direction_origin M L (eta0Bin M L) del hd
  obtain ⟨C, hC, hr⟩ := binary_assignment_denominator_direction_regular M L
    (eta0Bin M L) del hd
  have hcpi := hov.1
  have radius : 0 < cpi / (2 * (C+1)) := by positivity
  apply (hasDerivAt_const (0 : ℝ)
    (∫ o, ∑ k ∈ Finset.range L.K, psiFullProdBin L (eta0Bin M L) k o
      ∂observationLaw M)).congr_of_eventuallyEq
  filter_upwards [continuousAt_id.abs.eventually_lt_const (by simpa using radius)] with t ht
  have hlocal : ∀ a, ∀ᵐ x ∂xLaw M,
      cpi / 2 ≤ (eta0Bin M L).piLev a x + t * del.piLev a x := by
    intro a
    filter_upwards [(hr a).2] with x hx
    have hp : cpi ≤ (eta0Bin M L).piLev a x := hov.2 x a.val a.property.1 a.property.2
    have heprod : |t * del.piLev a x| ≤ |t| * C := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hx) (abs_nonneg t)
    have ht' : |t| * (2 * (C+1)) < cpi := (lt_div_iff₀ (by positivity)).mp ht
    have hlow := neg_abs_le (t * del.piLev a x)
    nlinarith [abs_nonneg t]
  have hm a := ((he.2.2.2.1 a).2.2).add ((hr a).1.const_mul t)
  have hpart k := population_binary_full_product_fitted_denominator_mean M L cpi hov hy he
    (fun a x => (eta0Bin M L).piLev a x + t * del.piLev a x) hm
    (cpi / 2) (by positivity) hlocal k
  rw [integral_finsetSum _ (fun k hk => (hpart ⟨k, Finset.mem_range.mp hk⟩).1),
    integral_finsetSum _ (fun k hk => population_binary_full_product_integrable_of_overlap M
      L cpi hov hy he ⟨k, Finset.mem_range.mp hk⟩)]
  apply Finset.sum_congr rfl
  intro k hk
  exact (hpart ⟨k, Finset.mem_range.mp hk⟩).2

-- Both the denominator and signed product weight may be fitted. The weight
-- update multiplies a centered residual with the fitted denominator, so the
-- mean is unchanged even when the two updates occur simultaneously.
-- @node: population_binary_full_product_fitted_denominator_weight_mean
/-- Under [baseline overlap](hyp:hov), [an almost surely binary outcome](hyp:hy),
and [admissibility of the true binary nuisance](hyp:he), suppose
[the fitted assignment probabilities are measurable](hyp:hpi), [their common lower bound is positive](hyp:hc),
and [each fitted probability exceeds that bound almost everywhere](hyp:hp).
If [the fitted product weight for the selected interval is measurable](hyp:hg) and
[its absolute value is almost everywhere bounded by the given constant](hyp:hb),
[the full-product score with both fitted denominators and fitted weight is integrable and has the same population mean as the score at the true nuisance](goal). -/
lemma population_binary_full_product_fitted_denominator_weight_mean
    (L : LevelData Z X) (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hy : OutcomeBinaryAE M) (he : BinAdmissible M L (eta0Bin M L))
    (pi : PositiveIndex L.K → X → ℝ) (hpi : ∀ a, Measurable (pi a))
    (c : ℝ) (hc : 0 < c) (hp : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ pi a x)
    (g : Fin L.K → X → ℝ) (k : Fin L.K)
    (hg : Measurable (g k)) (B : ℝ) (hb : ∀ᵐ x ∂xLaw M, ‖g k x‖ ≤ B) :
    Integrable (psiFullProdBin L {eta0Bin M L with piLev := pi, gammaFull := g} k)
      (observationLaw M) ∧
    (∫ o, psiFullProdBin L {eta0Bin M L with piLev := pi, gammaFull := g} k o
      ∂observationLaw M) =
      ∫ o, psiFullProdBin L (eta0Bin M L) k o ∂observationLaw M := by
  have hbase := population_binary_full_product_fitted_denominator_mean M L cpi hov hy he
    pi hpi c hc hp k
  have hg0 : Measurable ((eta0Bin M L).gammaFull k) := he.2.2.2.2.2.2.2.2.2.2.1 k
  have hb0 : ∀ᵐ x ∂xLaw M, ‖(eta0Bin M L).gammaFull k x‖ ≤ 1 := by
    filter_upwards [he.2.2.2.2.2.2.2.2.2.1 k] with x hx
    simpa only [Real.norm_eq_abs, abs_le, mem_Icc] using hx
  let w : X → ℝ := fun x => g k x - (eta0Bin M L).gammaFull k x
  have hw : Measurable w := hg.sub hg0
  have hwb : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ B + 1 := by
    filter_upwards [hb, hb0] with x hx hx0
    exact (norm_sub_le _ _).trans (add_le_add hx hx0)
  have ip i := (population_binary_RP_fitted_denominator_integrable M L cpi hov hy he
    pi hpi c hc hp i).bdd_mul (hw.comp measurable_fst).aestronglyMeasurable
      (observationLaw_covariate_ae M _ hwb)
  obtain ⟨ic, zc⟩ := population_binary_full_denominator_correction_zero M L pi hpi k
    w hw (ip (k+1)) (ip k)
  have hid : (fun o => psiFullProdBin L {eta0Bin M L with
      piLev := pi, gammaFull := g} k o) =
      (fun o => psiFullProdBin L {eta0Bin M L with piLev := pi} k o +
        w o.1 * (RP L {eta0Bin M L with piLev := pi} (k+1) o -
          RP L {eta0Bin M L with piLev := pi} k o)) := by
    funext o
    simp only [psiFullProdBin, fullValue, dif_pos k.isLt, binFullJ, RP, w]
    ring
  constructor
  · change Integrable (fun o => psiFullProdBin L _ k o) _
    rw [hid]
    exact hbase.1.fun_add ic
  · rw [hid, integral_add hbase.1 ic, zc, add_zero]
    exact hbase.2

-- @node: population_binary_full_joint_denominator_weight_orthogonality_of_admissible
/-- Under [baseline overlap](hyp:hov) and [an almost surely binary outcome](hyp:hy),
if [the nuisance direction is admissible at the true binary nuisance](hyp:hd),
[the population mean of each full-product score has derivative zero at zero when its assignment denominators and product weights move jointly and linearly along that direction](goal). -/
lemma population_binary_full_joint_denominator_weight_orthogonality_of_admissible
    (L : LevelData Z X) (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hy : OutcomeBinaryAE M) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del)) (k : Fin L.K) :
    HasDerivAt (fun t : ℝ => ∫ o, psiFullProdBin L {eta0Bin M L with
      piLev := fun a x => (eta0Bin M L).piLev a x + t * del.piLev a x
      gammaFull := fun a x => (eta0Bin M L).gammaFull a x + t * del.gammaFull a x}
      k o ∂observationLaw M) 0 0 := by
  have he := binary_admissible_direction_origin M L (eta0Bin M L) del hd
  obtain ⟨C, hC, hr⟩ := binary_assignment_denominator_direction_regular M L
    (eta0Bin M L) del hd
  obtain ⟨G, hG, hgr⟩ := binary_full_weight_direction_regular M L (eta0Bin M L) del hd
  have hg0 : Measurable ((eta0Bin M L).gammaFull k) := he.2.2.2.2.2.2.2.2.2.2.1 k
  have hb0 : ∀ᵐ x ∂xLaw M, ‖(eta0Bin M L).gammaFull k x‖ ≤ 1 := by
    filter_upwards [he.2.2.2.2.2.2.2.2.2.1 k] with x hx
    simpa only [Real.norm_eq_abs, abs_le, mem_Icc] using hx
  have hcpi := hov.1
  have radius : 0 < cpi / (2 * (C+1)) := by positivity
  apply (hasDerivAt_const (0 : ℝ)
    (∫ o, psiFullProdBin L (eta0Bin M L) k o ∂observationLaw M)).congr_of_eventuallyEq
  filter_upwards [continuousAt_id.abs.eventually_lt_const (by simpa using radius)] with t ht
  have hlocal : ∀ a, ∀ᵐ x ∂xLaw M,
      cpi / 2 ≤ (eta0Bin M L).piLev a x + t * del.piLev a x := by
    intro a
    filter_upwards [(hr a).2] with x hx
    have hp : cpi ≤ (eta0Bin M L).piLev a x := hov.2 x a.val a.property.1 a.property.2
    have heprod : |t * del.piLev a x| ≤ |t| * C := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hx) (abs_nonneg t)
    have ht' : |t| * (2 * (C+1)) < cpi := (lt_div_iff₀ (by positivity)).mp ht
    have hlow := neg_abs_le (t * del.piLev a x)
    nlinarith [abs_nonneg t]
  apply (population_binary_full_product_fitted_denominator_weight_mean M L cpi hov hy he
    (fun a x => (eta0Bin M L).piLev a x + t * del.piLev a x)
    (fun a => ((he.2.2.2.1 a).2.2).add ((hr a).1.const_mul t))
    (cpi / 2) (by positivity) hlocal
    (fun a x => (eta0Bin M L).gammaFull a x + t * del.gammaFull a x) k
    (hg0.add ((hgr k).1.const_mul t)) (1 + |t| * G) ?_).2
  filter_upwards [hb0, (hgr k).2] with x hx hgx
  calc
    _ ≤ ‖(eta0Bin M L).gammaFull k x‖ + ‖t * del.gammaFull k x‖ := norm_add_le _ _
    _ ≤ 1 + |t| * G := by
      rw [norm_mul, Real.norm_eq_abs t]
      exact add_le_add hx (mul_le_mul_of_nonneg_left hgx (abs_nonneg t))

-- A common neighborhood controls all denominators and all signed weights.
-- Finite linearity then transfers the exact population cancellation to the sum.
-- @node: population_binary_full_sum_joint_denominator_weight_orthogonality
/-- Under [baseline overlap](hyp:hov) and [an almost surely binary outcome](hyp:hy),
if [the nuisance direction is admissible at the true binary nuisance](hyp:hd),
[the population mean of the sum of all full-product scores has derivative zero at zero when assignment denominators and product weights move jointly and linearly along that direction](goal). -/
lemma population_binary_full_sum_joint_denominator_weight_orthogonality
    (L : LevelData Z X) (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hy : OutcomeBinaryAE M) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del)) :
    HasDerivAt (fun t : ℝ => ∫ o, ∑ k ∈ Finset.range L.K,
      psiFullProdBin L {eta0Bin M L with
        piLev := fun a x => (eta0Bin M L).piLev a x + t * del.piLev a x
        gammaFull := fun a x => (eta0Bin M L).gammaFull a x + t * del.gammaFull a x}
        k o ∂observationLaw M) 0 0 := by
  have he := binary_admissible_direction_origin M L (eta0Bin M L) del hd
  obtain ⟨C, hC, hr⟩ := binary_assignment_denominator_direction_regular M L
    (eta0Bin M L) del hd
  obtain ⟨G, hG, hgr⟩ := binary_full_weight_direction_regular M L (eta0Bin M L) del hd
  have hcpi := hov.1
  have radius : 0 < cpi / (2 * (C+1)) := by positivity
  apply (hasDerivAt_const (0 : ℝ)
    (∫ o, ∑ k ∈ Finset.range L.K, psiFullProdBin L (eta0Bin M L) k o
      ∂observationLaw M)).congr_of_eventuallyEq
  filter_upwards [continuousAt_id.abs.eventually_lt_const (by simpa using radius)] with t ht
  have hlocal : ∀ a, ∀ᵐ x ∂xLaw M,
      cpi / 2 ≤ (eta0Bin M L).piLev a x + t * del.piLev a x := by
    intro a
    filter_upwards [(hr a).2] with x hx
    have hp : cpi ≤ (eta0Bin M L).piLev a x := hov.2 x a.val a.property.1 a.property.2
    have heprod : |t * del.piLev a x| ≤ |t| * C := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hx) (abs_nonneg t)
    have ht' : |t| * (2 * (C+1)) < cpi := (lt_div_iff₀ (by positivity)).mp ht
    have hlow := neg_abs_le (t * del.piLev a x)
    nlinarith [abs_nonneg t]
  have hg0 (k : Fin L.K) : Measurable ((eta0Bin M L).gammaFull k) :=
    he.2.2.2.2.2.2.2.2.2.2.1 k
  have hgb (k : Fin L.K) : ∀ᵐ x ∂xLaw M,
      ‖(eta0Bin M L).gammaFull k x + t * del.gammaFull k x‖ ≤ 1 + |t| * G := by
    filter_upwards [he.2.2.2.2.2.2.2.2.2.1 k, (hgr k).2] with x hx hgx
    have hb0 : ‖(eta0Bin M L).gammaFull k x‖ ≤ 1 := by
      simpa only [Real.norm_eq_abs, abs_le, mem_Icc] using hx
    calc
      _ ≤ ‖(eta0Bin M L).gammaFull k x‖ + ‖t * del.gammaFull k x‖ := norm_add_le _ _
      _ ≤ 1 + |t| * G := by
        rw [norm_mul, Real.norm_eq_abs t]
        exact add_le_add hb0 (mul_le_mul_of_nonneg_left hgx (abs_nonneg t))
  have hpart (k : Fin L.K) :=
    population_binary_full_product_fitted_denominator_weight_mean M L cpi hov hy he
      (fun a x => (eta0Bin M L).piLev a x + t * del.piLev a x)
      (fun a => ((he.2.2.2.1 a).2.2).add ((hr a).1.const_mul t))
      (cpi / 2) (by positivity) hlocal
      (fun a x => (eta0Bin M L).gammaFull a x + t * del.gammaFull a x) k
      ((hg0 k).add ((hgr k).1.const_mul t)) (1 + |t| * G) (hgb k)
  rw [integral_finsetSum _ (fun k hk => (hpart ⟨k, Finset.mem_range.mp hk⟩).1),
    integral_finsetSum _ (fun k hk => population_binary_full_product_integrable_of_overlap M
      L cpi hov hy he ⟨k, Finset.mem_range.mp hk⟩)]
  apply Finset.sum_congr rfl
  intro k hk
  exact (hpart ⟨k, Finset.mem_range.mp hk⟩).2

end Papers.TbsPrteOptimalTransport
