module
public import Papers.TbsPrteOptimalTransport.Helpers.ConnectedIV
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
/-!
# Support, boundary, LIV and tail steps for the connected-instrument reduction

Continuity and connectedness identify the conditional propensity support as an
interval. Above its upper endpoint the baseline selection indicator vanishes;
Fubini then identifies the remaining tail integral with the policy's positive
excess over that endpoint. The fundamental theorem of calculus identifies the
LIV term with the clipped policy regression difference, and Fubini rewrites the
lower boundary's weighted integral as a negative truncated integral.
-/
public section
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false
set_option linter.style.haveILetI false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)

-- @node: propensity_between_support_endpoints
/-- [Every instrument-specific propensity at any covariate value lies between the
lower and upper endpoints of its conditional propensity range](goal). -/
lemma propensity_between_support_endpoints (z : Z) (x : X) :
    M.prop z x ∈ Icc (pLow M.prop x) (pHigh M.prop x) := by
  have hlo : BddBelow (range (fun z => M.prop z x)) :=
    ⟨0, by rintro _ ⟨z, rfl⟩; exact (M.rangeProp z x).1⟩
  have hhi : BddAbove (range (fun z => M.prop z x)) :=
    ⟨1, by rintro _ ⟨z, rfl⟩; exact (M.rangeProp z x).2⟩
  exact ⟨csInf_le hlo (mem_range_self z), le_csSup hhi (mem_range_self z)⟩

-- @node: connected_propensity_support_interval
/-- If [the domains satisfy the compact Borel conditions](hyp:hD), [propensity is
continuous on instrument components](hyp:hc), [there are finitely many instrument
components](hyp:hfin), and [the instrument space is connected](hyp:hconn), then
[for almost every covariate value the propensity range is the closed interval
between its lower and upper endpoints](goal). -/
lemma connected_propensity_support_interval (hD : DomainsCompactBorel M)
    (hc : PropensityContinuousOnComponents M) (hfin : FiniteInstrumentComponents Z)
    (hconn : InstrumentConnectedReduction Z) :
    ∀ᵐ x ∂xLaw M, range (fun z => M.prop z x) =
      Icc (pLow M.prop x) (pHigh M.prop x) := by
  letI : CompactSpace Z := hD.2.2.2.1
  letI : ConnectedSpace Z := hconn
  letI : Finite (ConnectedComponents Z) := hfin
  filter_upwards [hc] with x hx
  have hcont := continuous_of_finite_components (fun z => M.prop z x) hx
  exact eq_Icc_of_connected_compact (isConnected_range hcont) (isCompact_range hcont)

-- @node: rangeData_connected_count
/-- If [a finite interval decomposition validly represents a real set](hyp:hv)
that is [nonempty](hyp:hne) and [contains every point between any two of its
points](hyp:hR), then [the decomposition has exactly one interval](goal). -/
lemma rangeData_connected_count (D : RangeData) (R : Set ℝ) (hv : D.Valid R)
    (hne : R.Nonempty) (hR : OrdConnected R) : D.count = 1 := by
  have hpos : 0 < D.count := by
    obtain ⟨r, hr⟩ := hne
    rw [hv.2.2] at hr
    obtain ⟨i, _⟩ := mem_iUnion.mp hr
    exact Nat.zero_lt_of_lt i.isLt
  by_contra hn
  have htwo : 1 < D.count := by omega
  let i : Fin D.count := ⟨0, hpos⟩
  let j : Fin D.count := ⟨1, htwo⟩
  have hij : i < j := by change (0 : ℕ) < 1; exact Nat.zero_lt_one
  have hgap := hv.2.1 i j hij
  let a := D.2.2 i
  let b := D.2.1 j
  have ha : a ∈ R := by
    rw [hv.2.2]
    exact mem_iUnion.mpr ⟨i, (show a ∈ Icc (D.2.1 i) (D.2.2 i) from ⟨(hv.1 i).2.1, le_rfl⟩)⟩
  have hb : b ∈ R := by
    rw [hv.2.2]
    exact mem_iUnion.mpr ⟨j, (show b ∈ Icc (D.2.1 j) (D.2.2 j) from ⟨le_rfl, (hv.1 j).2.1⟩)⟩
  have ham : a < (a + b) / 2 := by dsimp [a, b]; linarith
  have hmb : (a + b) / 2 < b := by dsimp [a, b]; linarith
  have hm : (a + b) / 2 ∈ R := hR.out ha hb ⟨ham.le, hmb.le⟩
  rw [hv.2.2] at hm
  obtain ⟨k, hk⟩ := mem_iUnion.mp hm
  by_cases hk0 : k = i
  · rw [hk0] at hk
    exact (not_le.mpr ham) hk.2
  · have hik : i < k := by
      apply Fin.lt_def.mpr
      have : k.val ≠ 0 := fun he => hk0 (Fin.ext he)
      exact Nat.pos_of_ne_zero this
    have hjk : j ≤ k := by
      apply Fin.le_iff_val_le_val.mpr
      exact hik
    have hbkle : b ≤ D.2.1 k := by
      rcases lt_or_eq_of_le hjk with hjk | hjk
      · exact (hv.1 j).2.1.trans (hv.2.1 j k hjk).le
      · rw [← hjk]
    exact (not_le.mpr hmb) (hbkle.trans hk.1)

-- @node: connected_range_decomposition_count
/-- Under [the structural model assumptions](hyp:h), [continuity of propensity
on instrument components](hyp:hc), [finitely many instrument components](hyp:hfin),
and [connectedness of the instrument space](hyp:hconn), [the conditional propensity
range decomposition has exactly one interval for almost every covariate value](goal). -/
lemma connected_range_decomposition_count (h : StructuralAssumptions M)
    (hc : PropensityContinuousOnComponents M) (hfin : FiniteInstrumentComponents Z)
    (hconn : InstrumentConnectedReduction Z) :
    ∀ᵐ x ∂xLaw M, (CondRangeDecomposition M x).count = 1 := by
  filter_upwards [range_decomposition_valid M h hfin hc,
    connected_propensity_support_interval M h.2.2.2.2.2.2 hc hfin hconn] with x hv hs
  apply rangeData_connected_count _ _ hv (range_nonempty _)
  rw [hs]
  infer_instance

-- @node: rangeData_single_interval
/-- If [a finite interval decomposition validly represents a real set](hyp:hv)
and [has exactly one interval](hyp:hc), then [the set is the closed interval
between the first interval's lower and upper endpoints](goal). -/
lemma rangeData_single_interval (D : RangeData) (R : Set ℝ)
    (hv : D.Valid R) (hc : D.count = 1) : R = Icc (D.low 0) (D.high 0) := by
  have hpos : 0 < D.1 := by change D.1 = 1 at hc; omega
  rw [hv.2.2]
  ext y
  simp only [mem_iUnion, RangeData.low, RangeData.high, dif_pos hpos]
  constructor
  · rintro ⟨i, hi⟩
    have he : i = ⟨0, hpos⟩ := by
      apply Fin.ext
      have := i.isLt
      change D.1 = 1 at hc
      omega
    simpa only [he] using hi
  · intro hy
    exact ⟨⟨0, hpos⟩, hy⟩

-- @node: connected_range_decomposition_endpoints
/-- Under [the structural model assumptions](hyp:h), [componentwise continuity of
propensity](hyp:hc), [finitely many instrument components](hyp:hfin), and
[connectedness of the instrument space](hyp:hconn), [almost every conditional
range decomposition has first endpoints equal to the propensity infimum and
supremum, and its tail runs from strictly above that supremum through one](goal). -/
lemma connected_range_decomposition_endpoints (h : StructuralAssumptions M)
    (hc : PropensityContinuousOnComponents M) (hfin : FiniteInstrumentComponents Z)
    (hconn : InstrumentConnectedReduction Z) :
    ∀ᵐ x ∂xLaw M, (CondRangeDecomposition M x).low 0 = pLow M.prop x ∧
      (CondRangeDecomposition M x).high 0 = pHigh M.prop x ∧
      (CondRangeDecomposition M x).tail = Ioc (pHigh M.prop x) 1 := by
  filter_upwards [range_decomposition_valid M h hfin hc,
    connected_range_decomposition_count M h hc hfin hconn] with x hv hn
  have hpos : 0 < (CondRangeDecomposition M x).1 := by
    change (CondRangeDecomposition M x).1 = 1 at hn
    omega
  have hlh : (CondRangeDecomposition M x).low 0 ≤ (CondRangeDecomposition M x).high 0 := by
    simpa only [RangeData.low, RangeData.high, dif_pos hpos] using (hv.1 ⟨0, hpos⟩).2.1
  have hs := rangeData_single_interval _ _ hv hn
  have hlo : (CondRangeDecomposition M x).low 0 = pLow M.prop x := by
    unfold pLow
    rw [hs, csInf_Icc hlh]
  have hhi : (CondRangeDecomposition M x).high 0 = pHigh M.prop x := by
    unfold pHigh
    rw [hs, csSup_Icc hlh]
  refine ⟨hlo, hhi, ?_⟩
  simp only [RangeData.tail, RangeData.tailLo, hn, one_ne_zero, if_false,
    Nat.sub_self, hhi]

-- @node: policyWeight_above_support
/-- At [a resistance threshold strictly above the upper propensity endpoint](hyp:hu),
[the policy weight equals the conditional probability that the policy propensity
reaches or exceeds that threshold](goal). -/
lemma policyWeight_above_support (q : Z → X → ℝ) (x : X) (u : ℝ)
    (hu : pHigh M.prop x < u) :
    policyWeight M q x u = ∫ z, (if u ≤ q z x then 1 else 0 : ℝ) ∂M.instKernel x := by
  unfold policyWeight
  apply integral_congr_ae
  filter_upwards [] with z
  have hp : ¬ u ≤ M.prop z x :=
    not_le.mpr ((propensity_between_support_endpoints M z x).2.trans_lt hu)
  simp only [if_neg hp, sub_zero]

-- @node: policyWeight_tail_nonneg
/-- At [a resistance threshold strictly above the upper propensity endpoint](hyp:hu),
[the policy weight is nonnegative](goal). -/
lemma policyWeight_tail_nonneg (q : Z → X → ℝ) (x : X) (u : ℝ)
    (hu : pHigh M.prop x < u) : 0 ≤ policyWeight M q x u := by
  rw [policyWeight_above_support M q x u hu]
  apply integral_nonneg
  intro z
  change 0 ≤ (if u ≤ q z x then 1 else 0 : ℝ)
  split <;> norm_num

-- @node: threshold_tail_integral
/-- If [a threshold is at most one](hyp:hr), then [the integral from strictly above
a lower endpoint through one of the indicator that resistance does not exceed
the threshold equals the positive part of the threshold minus that endpoint](goal). -/
lemma threshold_tail_integral (b r : ℝ) (hr : r ≤ 1) :
    (∫ u in Ioc b 1, (if u ≤ r then 1 else 0 : ℝ)) = max 0 (r - b) := by
  have he : Iic r ∩ Ioc b 1 = Ioc b r := by
    ext u
    simp only [mem_inter_iff, mem_Iic, mem_Ioc]
    constructor
    · exact fun h => ⟨h.2.1, h.1⟩
    · exact fun h => ⟨h.2, h.1, h.2.trans hr⟩
  change (∫ u, (Iic r).indicator (1 : ℝ → ℝ) u ∂volume.restrict (Ioc b 1)) = _
  rw [integral_indicator_one measurableSet_Iic, measureReal_def,
    Measure.restrict_apply measurableSet_Iic, he, Real.volume_Ioc]
  by_cases h : 0 ≤ r - b
  · rw [ENNReal.toReal_ofReal h, max_eq_right h]
  · rw [ENNReal.ofReal_eq_zero.mpr (le_of_not_ge h), ENNReal.toReal_zero,
      max_eq_left (le_of_not_ge h)]

-- @node: policyWeight_tail_integral
/-- If [the policy propensity is jointly measurable](hyp:hq) and [never exceeds
one](hyp:hr), then [its policy weight integrated above the upper support endpoint
through one equals the conditional mean of its positive excess over that endpoint](goal). -/
lemma policyWeight_tail_integral (q : Z → X → ℝ)
    (hq : Measurable (Function.uncurry q)) (hr : ∀ z x, q z x ≤ 1) (x : X) :
    (∫ u in Ioc (pHigh M.prop x) 1, policyWeight M q x u) =
      ∫ z, max 0 (q z x - pHigh M.prop x) ∂M.instKernel x := by
  let b := pHigh M.prop x
  letI : IsMarkovKernel M.instKernel := M.instKernel_markov
  have hqx : Measurable (fun a : ℝ × Z => q a.2 x) :=
    hq.comp (measurable_snd.prodMk measurable_const)
  have hm : Measurable (fun a : ℝ × Z => (if a.1 ≤ q a.2 x then 1 else 0 : ℝ)) := by
    exact Measurable.ite (measurableSet_le measurable_fst hqx) measurable_const measurable_const
  have hi : Integrable (fun a : ℝ × Z => (if a.1 ≤ q a.2 x then 1 else 0 : ℝ))
      ((volume.restrict (Ioc b 1)).prod (M.instKernel x)) := by
    apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    filter_upwards [] with a
    split <;> norm_num
  calc
    (∫ u in Ioc b 1, policyWeight M q x u) =
        ∫ u in Ioc b 1, ∫ z, (if u ≤ q z x then 1 else 0 : ℝ) ∂M.instKernel x := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro u hu
      exact policyWeight_above_support M q x u hu.1
    _ = ∫ z, (∫ u in Ioc b 1, (if u ≤ q z x then 1 else 0 : ℝ)) ∂M.instKernel x :=
      integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact threshold_tail_integral b (q z x) (hr z x)

-- @node: policy_propensity_jointly_measurable
/-- Under [the threshold-crossing assumptions](hyp:h), [a measurable policy map
that preserves the unit propensity interval](hyp:hp) yields [a policy propensity
jointly measurable in instruments and covariates](goal). -/
@[fun_prop] lemma policy_propensity_jointly_measurable
    (h : ThresholdCrossing M) (phi : Z → X → ℝ → ℝ) (hp : IsPolicyMap phi) :
    Measurable (Function.uncurry (policyProp phi M.prop)) := by
  have hm := h.2.1
  have hs : Measurable (fun zx : Z × X =>
      (⟨M.prop zx.1 zx.2, M.rangeProp zx.1 zx.2⟩ : Icc (0 : ℝ) 1)) := by
    fun_prop
  exact hp.1.comp (measurable_fst.prodMk (measurable_snd.prodMk hs))

-- @node: connected_policy_tail_bound
/-- Under [the threshold-crossing assumptions](hyp:h), for [a measurable policy
map preserving the unit interval](hyp:hp), [the upper or lower outcome-weighted
tail integral equals the corresponding maximum or minimum outcome times the
conditional mean positive policy excess above the upper propensity endpoint](goal). -/
lemma connected_policy_tail_bound (h : ThresholdCrossing M)
    (phi : Z → X → ℝ → ℝ) (hp : IsPolicyMap phi) (upper : Bool) (x : X) :
    (∫ u in Ioc (pHigh M.prop x) 1,
      (if upper then M.yMax else M.yMin) * max 0 (policyWeight M (policyProp phi M.prop) x u) +
      (if upper then M.yMin else M.yMax) * min 0 (policyWeight M (policyProp phi M.prop) x u)) =
    (if upper then M.yMax else M.yMin) *
      ∫ z, max 0 (policyProp phi M.prop z x - pHigh M.prop x) ∂M.instKernel x := by
  calc
    _ = ∫ u in Ioc (pHigh M.prop x) 1,
        (if upper then M.yMax else M.yMin) * policyWeight M (policyProp phi M.prop) x u := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro u hu
      have hn := policyWeight_tail_nonneg M (policyProp phi M.prop) x u hu.1
      dsimp only
      rw [max_eq_right hn, min_eq_left hn, mul_zero, add_zero]
    _ = _ := by
      rw [integral_const_mul, policyWeight_tail_integral M _
        (policy_propensity_jointly_measurable M h phi hp)
        (fun z x => (hp.2 z x (M.prop z x) (M.rangeProp z x)).2)]

-- @node: connected_decomposition_tail_bound
/-- Under [the structural assumptions](hyp:h), [componentwise propensity
continuity](hyp:hc), [finitely many instrument components](hyp:hfin),
[connected instruments](hyp:hconn), and [a measurable policy map preserving the
unit interval](hyp:hp), [almost every decomposition tail bound equals the selected
outcome endpoint times the conditional mean positive policy excess above the
upper propensity endpoint](goal). -/
lemma connected_decomposition_tail_bound (h : StructuralAssumptions M)
    (hc : PropensityContinuousOnComponents M) (hfin : FiniteInstrumentComponents Z)
    (hconn : InstrumentConnectedReduction Z)
    (phi : Z → X → ℝ → ℝ) (hp : IsPolicyMap phi) (upper : Bool) :
    ∀ᵐ x ∂xLaw M,
      (∫ u in (CondRangeDecomposition M x).tail,
        (if upper then M.yMax else M.yMin) * max 0 (policyWeight M (policyProp phi M.prop) x u) +
        (if upper then M.yMin else M.yMax) * min 0 (policyWeight M (policyProp phi M.prop) x u)) =
      (if upper then M.yMax else M.yMin) *
        ∫ z, max 0 (policyProp phi M.prop z x - pHigh M.prop x) ∂M.instKernel x := by
  filter_upwards [connected_range_decomposition_endpoints M h hc hfin hconn] with x hx
  rw [hx.2.2]
  exact connected_policy_tail_bound M h.2.2.2.1 phi hp upper x

-- @node: clipped_derivative_threshold_integral
/-- For [ordered interval endpoints](hyp:hab) and [a function absolutely continuous
on that interval](hyp:hf), [integrating its derivative times the indicator that
resistance does not exceed a threshold gives its value at the threshold clipped
to the interval minus its value at the lower endpoint](goal). -/
lemma clipped_derivative_threshold_integral (f : ℝ → ℝ) (a b r : ℝ)
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b) :
    (∫ u in Ioc a b, deriv f u * (if u ≤ r then 1 else 0 : ℝ)) =
      f (min b (max a r)) - f a := by
  by_cases hra : r ≤ a
  · have he : min b (max a r) = a := by
      rw [max_eq_left hra, min_eq_right hab]
    rw [he, sub_self]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro u hu
    simp only [if_neg (not_le.mpr (hra.trans_lt hu.1)), mul_zero]
  · have har : a ≤ r := (lt_of_not_ge hra).le
    have hac : a ≤ min b r := le_min hab har
    have hs : Iic r ∩ Ioc a b = Ioc a (min b r) := by
      ext u
      simp only [mem_inter_iff, mem_Iic, mem_Ioc, le_min_iff]
      constructor
      · exact fun h => ⟨h.2.1, h.2.2, h.1⟩
      · exact fun h => ⟨h.2.2, h.1, h.2.1⟩
    have hfc : AbsolutelyContinuousOnInterval f a (min b r) := by
      apply hf.mono
      rw [uIcc_of_le hab, uIcc_of_le hac]
      exact Icc_subset_Icc le_rfl (min_le_left _ _)
    calc
      _ = ∫ u, (Iic r).indicator (deriv f) u ∂volume.restrict (Ioc a b) := by
        apply integral_congr_ae
        filter_upwards [] with u
        by_cases hur : u ≤ r <;> simp [hur]
      _ = ∫ u in Ioc a (min b r), deriv f u := by
        rw [integral_indicator measurableSet_Iic,
          Measure.restrict_restrict measurableSet_Iic, hs]
      _ = f (min b r) - f a := by
        rw [← intervalIntegral.integral_of_le hac]
        exact hfc.integral_deriv_eq_sub
      _ = _ := by rw [max_eq_right har]

-- @node: policyWeight_derivative_integral
/-- Under [the threshold-crossing assumptions](hyp:h), let [the policy propensity
be jointly measurable](hyp:hq), [the interval endpoints be ordered](hyp:hab),
[the regression function be absolutely continuous on that interval](hyp:hf), and
[all baseline propensities at the covariate value lie in the interval](hyp:hp).
Then [the policy-weighted derivative integral equals the conditional mean of the
regression at the clipped policy propensity minus its baseline value](goal). -/
lemma policyWeight_derivative_integral (h : ThresholdCrossing M)
    (q : Z → X → ℝ) (hq : Measurable (Function.uncurry q))
    (x : X) (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hp : ∀ z, M.prop z x ∈ Icc a b) :
    (∫ u in Ioc a b, deriv f u * policyWeight M q x u) =
      ∫ z, f (min b (max a (q z x))) - f (M.prop z x) ∂M.instKernel x := by
  letI : IsMarkovKernel M.instKernel := M.instKernel_markov
  let μ := volume.restrict (Ioc a b)
  have hi : Integrable (deriv f) μ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hf.intervalIntegrable_deriv
  have hqm : Measurable (fun uz : ℝ × Z => q uz.2 x) := by
    fun_prop
  have hpm : Measurable (fun uz : ℝ × Z => M.prop uz.2 x) := by
    exact h.2.1.comp (measurable_snd.prodMk measurable_const)
  have hm : Measurable (fun uz : ℝ × Z =>
      (if uz.1 ≤ q uz.2 x then 1 else 0 : ℝ) -
        (if uz.1 ≤ M.prop uz.2 x then 1 else 0 : ℝ)) := by
    exact (Measurable.ite (measurableSet_le measurable_fst hqm)
      measurable_const measurable_const).sub
      (Measurable.ite (measurableSet_le measurable_fst hpm)
        measurable_const measurable_const)
  have hbound : ∀ᵐ uz ∂μ.prod (M.instKernel x),
      ‖(if uz.1 ≤ q uz.2 x then 1 else 0 : ℝ) -
        (if uz.1 ≤ M.prop uz.2 x then 1 else 0 : ℝ)‖ ≤ (1 : ℝ) := by
    filter_upwards [] with uz
    split_ifs <;> norm_num
  have hiProd := (hi.comp_fst (M.instKernel x)).mul_bdd hm.aestronglyMeasurable hbound
  have hiThreshold (r : ℝ) :
      Integrable (fun u => deriv f u * (if u ≤ r then 1 else 0 : ℝ)) μ := by
    apply hi.mul_bdd (c := 1)
    · exact (Measurable.ite measurableSet_Iic measurable_const
        measurable_const).aestronglyMeasurable
    · filter_upwards [] with u
      split_ifs <;> norm_num
  calc
    _ = ∫ u in Ioc a b, ∫ z, deriv f u *
        ((if u ≤ q z x then 1 else 0 : ℝ) -
          (if u ≤ M.prop z x then 1 else 0 : ℝ)) ∂M.instKernel x := by
      simp only [integral_const_mul, policyWeight]
    _ = ∫ z, (∫ u in Ioc a b, deriv f u *
        ((if u ≤ q z x then 1 else 0 : ℝ) -
          (if u ≤ M.prop z x then 1 else 0 : ℝ))) ∂M.instKernel x :=
      integral_integral_swap hiProd
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [mul_sub]
      rw [integral_sub (hiThreshold (q z x)) (hiThreshold (M.prop z x)),
        clipped_derivative_threshold_integral f a b (q z x) hab hf,
        clipped_derivative_threshold_integral f a b (M.prop z x) hab hf,
        max_eq_right (hp z).1, min_eq_right (hp z).2]
      ring

-- @node: connected_regression_ac
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[componentwise propensity continuity](hyp:hc), [finitely many instrument
components](hyp:hfin), and [connected instruments](hyp:hconn), [the canonical
treated-outcome regression is absolutely continuous between the conditional
propensity endpoints for almost every covariate value](goal). -/
lemma connected_regression_ac (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (hc : PropensityContinuousOnComponents M)
    (hfin : FiniteInstrumentComponents Z) (hconn : InstrumentConnectedReduction Z) :
    ∀ᵐ x ∂xLaw M, AbsolutelyContinuousOnInterval (fun p => g1Canon M p x)
      (pLow M.prop x) (pHigh M.prop x) := by
  filter_upwards [canonical_regression_ac M h he hc hfin,
    connected_range_decomposition_count M h hc hfin hconn,
    connected_range_decomposition_endpoints M h hc hfin hconn] with x hx hn heq
  have hz : 0 < (CondRangeDecomposition M x).count := by omega
  simpa only [heq.1, heq.2.1] using hx 0 hz

-- @node: connected_policy_liv_integral
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[componentwise propensity continuity](hyp:hc), [finitely many instrument
components](hyp:hfin), [connected instruments](hyp:hconn), and [a measurable
policy map preserving the unit interval](hyp:hp), [the conditional local
instrumental-variable integral equals the conditional mean regression change
from baseline to the policy propensity clipped to the support, almost everywhere
in covariates](goal). -/
lemma connected_policy_liv_integral (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (hc : PropensityContinuousOnComponents M)
    (hfin : FiniteInstrumentComponents Z) (hconn : InstrumentConnectedReduction Z)
    (phi : Z → X → ℝ → ℝ) (hp : IsPolicyMap phi) :
    ∀ᵐ x ∂xLaw M,
      (∫ u in Ioc (pLow M.prop x) (pHigh M.prop x),
        deriv (fun p => g1Canon M p x) u * policyWeight M (policyProp phi M.prop) x u) =
      ∫ z, g1 M (clampPolicy M.prop (policyProp phi M.prop) z x) x -
        g1 M (M.prop z x) x ∂M.instKernel x := by
  filter_upwards [connected_regression_ac M h he hc hfin hconn] with x hx
  exact policyWeight_derivative_integral M h.2.2.2.1 _
    (policy_propensity_jointly_measurable M h.2.2.2.1 phi hp) x _ _ _
    (propensity_support_endpoints M.prop M.rangeProp x).2.2 hx
    (fun z => propensity_between_support_endpoints M z x)

-- @node: connected_decomposition_liv_integral
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[componentwise propensity continuity](hyp:hc), [finitely many instrument
components](hyp:hfin), [connected instruments](hyp:hconn), and [a measurable
policy map preserving the unit interval](hyp:hp), [the sum of local
instrumental-variable integrals over the range decomposition equals the
conditional mean regression change from baseline to the clipped policy
propensity, for almost every covariate value](goal). -/
lemma connected_decomposition_liv_integral (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (hc : PropensityContinuousOnComponents M)
    (hfin : FiniteInstrumentComponents Z) (hconn : InstrumentConnectedReduction Z)
    (phi : Z → X → ℝ → ℝ) (hp : IsPolicyMap phi) :
    ∀ᵐ x ∂xLaw M,
      (∑ k ∈ Finset.range (CondRangeDecomposition M x).count,
        ∫ u in (CondRangeDecomposition M x).liv k,
          deriv (fun p => g1Canon M p x) u * policyWeight M (policyProp phi M.prop) x u) =
      ∫ z, g1 M (clampPolicy M.prop (policyProp phi M.prop) z x) x -
        g1 M (M.prop z x) x ∂M.instKernel x := by
  filter_upwards [connected_range_decomposition_count M h hc hfin hconn,
    connected_range_decomposition_endpoints M h hc hfin hconn,
    connected_policy_liv_integral M h he hc hfin hconn phi hp] with x hn heq hi
  rw [hn, Finset.sum_range_one, RangeData.liv, heq.1, heq.2.1,
    ← restrict_Ioc_eq_restrict_Icc]
  exact hi

-- @node: connected_gap_law_eq_boundary
/-- For [any covariate-indexed fallback probability distribution supported on the outcome domain](hyp:zeroLaw), under [the structural assumptions](hyp:h),
[componentwise propensity continuity](hyp:hc), [finitely many instrument
components](hyp:hfin), and [connected instruments](hyp:hconn), [almost every
covariate value with a strictly positive lower propensity endpoint has its first
gap outcome distribution equal to its lower-boundary outcome distribution](goal). -/
lemma connected_gap_law_eq_boundary
    (zeroLaw : X → {ν : ProbabilityMeasure ℝ // ν.toMeasure M.Ysetᶜ = 0})
    (h : StructuralAssumptions M) (hc : PropensityContinuousOnComponents M)
    (hfin : FiniteInstrumentComponents Z) (hconn : InstrumentConnectedReduction Z) :
    ∀ᵐ x ∂xLaw M, 0 < pLow M.prop x →
      gapLaw M x 0 = boundaryLaw M zeroLaw x := by
  filter_upwards [connected_range_decomposition_endpoints M h hc hfin hconn] with x heq
  intro hl
  have hg : (CondRangeDecomposition M x).gapLo 0 = 0 := by
    simp only [RangeData.gapLo, ↓reduceIte]
  have hh : (CondRangeDecomposition M x).gapHi 0 = pLow M.prop x := heq.1
  have hz : canonSubmeasure M true x 0 = 0 := by
    simp [canonSubmeasure, selRegion]
  rw [gapLaw, hg, hh, if_pos hl, sub_zero, hz, Measure.sub_zero,
    boundaryLaw, if_pos hl]

-- @node: connected_gap_quantile_eq_boundary
/-- For [any covariate-indexed fallback probability distribution supported on the outcome domain](hyp:zeroLaw), under [the structural assumptions](hyp:h), [componentwise propensity
continuity](hyp:hc), [finitely many instrument components](hyp:hfin), and
[connected instruments](hyp:hconn), [for almost every covariate value with a
positive lower propensity endpoint, the first gap's outcome quantile equals
the boundary outcome quantile at every quantile rank strictly between zero and
one, for any weight function](goal). -/
lemma connected_gap_quantile_eq_boundary
    (zeroLaw : X → {ν : ProbabilityMeasure ℝ // ν.toMeasure M.Ysetᶜ = 0})
    (h : StructuralAssumptions M) (hc : PropensityContinuousOnComponents M)
    (hfin : FiniteInstrumentComponents Z) (hconn : InstrumentConnectedReduction Z)
    (om : X → ℝ → ℝ) :
    ∀ᵐ x ∂xLaw M, 0 < pLow M.prop x → ∀ t ∈ Ioo (0 : ℝ) 1,
      (gapQuantiles M om x 0).1 t = boundaryQuantile M zeroLaw x t := by
  filter_upwards [connected_gap_law_eq_boundary M zeroLaw h hc hfin hconn] with x hx
  intro hl t ht
  simp only [gapQuantiles, endpointGapQuantile, if_neg (ne_of_gt ht.1),
    if_neg (ne_of_lt ht.2), boundaryQuantile_eq_quantile_of_mem_Ioo M zeroLaw x ht, hx hl]

-- @node: connected_conditional_bound_three_terms
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[componentwise propensity continuity](hyp:hc), [finitely many instrument
components](hyp:hfin), [connected instruments](hyp:hconn), and [a measurable
policy map preserving the unit interval](hyp:hp), [the conditional bound is almost
everywhere the sum of three terms: the positive lower endpoint times the first
gap's outcome-weight quantile pairing, the conditional regression change at the
clipped policy propensity, and the selected outcome endpoint times the mean
positive policy excess above the upper endpoint; the quantile pairing uses equal
ranks for the upper bound and reversed weight ranks for the lower bound](goal). -/
lemma connected_conditional_bound_three_terms (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (hc : PropensityContinuousOnComponents M)
    (hfin : FiniteInstrumentComponents Z) (hconn : InstrumentConnectedReduction Z)
    (phi : Z → X → ℝ → ℝ) (hp : IsPolicyMap phi) (upper : Bool) :
    ∀ᵐ x ∂xLaw M,
      conditionalBoundIntegrand M upper (policyWeight M (policyProp phi M.prop)) x =
      max 0 (pLow M.prop x) *
        (∫ t in Ioo (0 : ℝ) 1,
          (gapQuantiles M (policyWeight M (policyProp phi M.prop)) x 0).1 t *
          (gapQuantiles M (policyWeight M (policyProp phi M.prop)) x 0).2
            (if upper then t else 1-t)) +
      (∫ z, g1 M (clampPolicy M.prop (policyProp phi M.prop) z x) x -
        g1 M (M.prop z x) x ∂M.instKernel x) +
      (if upper then M.yMax else M.yMin) *
        ∫ z, max 0 (policyProp phi M.prop z x - pHigh M.prop x) ∂M.instKernel x := by
  filter_upwards [connected_range_decomposition_count M h hc hfin hconn,
    connected_range_decomposition_endpoints M h hc hfin hconn,
    connected_decomposition_liv_integral M h he hc hfin hconn phi hp,
    connected_decomposition_tail_bound M h hc hfin hconn phi hp upper]
      with x hn heq hi ht
  unfold conditionalBoundIntegrand
  dsimp only
  rw [hi, ht, hn, Finset.sum_range_one, RangeData.gapLo, RangeData.gapHi,
    if_pos rfl, heq.1, sub_zero]

-- @node: policyWeight_below_support
/-- At [a resistance threshold no greater than the lower propensity endpoint](hyp:hu),
[the policy weight equals the conditional mean of the policy selection indicator
minus one](goal). -/
lemma policyWeight_below_support (q : Z → X → ℝ) (x : X) (u : ℝ)
    (hu : u ≤ pLow M.prop x) :
    policyWeight M q x u =
      ∫ z, (if u ≤ q z x then 1 else 0 : ℝ) - 1 ∂M.instKernel x := by
  unfold policyWeight
  apply integral_congr_ae
  filter_upwards [] with z
  have hp := hu.trans (propensity_between_support_endpoints M z x).1
  simp only [if_pos hp]

-- @node: policyWeight_boundary_nonpos
/-- At [a resistance threshold no greater than the lower propensity endpoint](hyp:hu),
[the policy weight is nonpositive](goal). -/
lemma policyWeight_boundary_nonpos (q : Z → X → ℝ) (x : X) (u : ℝ)
    (hu : u ≤ pLow M.prop x) : policyWeight M q x u ≤ 0 := by
  rw [policyWeight_below_support M q x u hu]
  apply integral_nonpos
  intro z
  dsimp only
  split_ifs <;> norm_num

-- @node: threshold_complement_integral
/-- For [a nonnegative selection threshold](hyp:hr), [integrating any function
from strictly above zero through an endpoint against the selection indicator
minus one equals the negative integral from strictly above the smaller of the
threshold and endpoint through the endpoint](goal). -/
lemma threshold_complement_integral (f : ℝ → ℝ) (a r : ℝ) (hr : 0 ≤ r) :
    (∫ u in Ioc 0 a, f u * ((if u ≤ r then 1 else 0 : ℝ) - 1)) =
      -(∫ u in Ioc (min a r) a, f u) := by
  have hs : Ioi r ∩ Ioc 0 a = Ioc (min a r) a := by
    by_cases har : a ≤ r
    · rw [min_eq_left har]
      ext u
      simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
      constructor
      · rintro ⟨hru, h0u, hua⟩
        exact False.elim ((not_lt_of_ge (hua.trans har)) hru)
      · rintro ⟨hau, hua⟩
        exact False.elim ((not_lt_of_ge hua) hau)
    · rw [min_eq_right (le_of_not_ge har)]
      ext u
      simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hr.trans_lt h.1, h.2⟩⟩
  calc
    _ = ∫ u, -((Ioi r).indicator f u) ∂volume.restrict (Ioc 0 a) := by
      apply integral_congr_ae
      filter_upwards [] with u
      by_cases hur : u ≤ r
      · simp [hur, not_lt.mpr hur]
      · simp [hur, lt_of_not_ge hur]
    _ = _ := by
      rw [integral_neg, integral_indicator measurableSet_Ioi,
        Measure.restrict_restrict measurableSet_Ioi, hs]

-- @node: policyWeight_boundary_integral
/-- If [the policy propensity is jointly measurable](hyp:hq) and [nonnegative](hyp:hr),
and [the weighting function is integrable from strictly above zero through the
lower propensity endpoint](hyp:hi), then [its policy-weighted integral over that
region equals the negative conditional mean of its integral from the smaller of
the policy propensity and lower endpoint through the lower endpoint](goal). -/
lemma policyWeight_boundary_integral (q : Z → X → ℝ)
    (hq : Measurable (Function.uncurry q)) (hr : ∀ z x, 0 ≤ q z x)
    (x : X) (f : ℝ → ℝ) (hi : IntegrableOn f (Ioc 0 (pLow M.prop x))) :
    (∫ u in Ioc 0 (pLow M.prop x), f u * policyWeight M q x u) =
      -(∫ z, (∫ u in Ioc (min (pLow M.prop x) (q z x)) (pLow M.prop x), f u)
        ∂M.instKernel x) := by
  letI : IsMarkovKernel M.instKernel := M.instKernel_markov
  let μ := volume.restrict (Ioc 0 (pLow M.prop x))
  have hqm : Measurable (fun uz : ℝ × Z => q uz.2 x) := by fun_prop
  have hm : Measurable (fun uz : ℝ × Z =>
      (if uz.1 ≤ q uz.2 x then 1 else 0 : ℝ) - 1) := by
    exact (Measurable.ite (measurableSet_le measurable_fst hqm)
      measurable_const measurable_const).sub_const 1
  have hb : ∀ᵐ uz ∂μ.prod (M.instKernel x),
      ‖(if uz.1 ≤ q uz.2 x then 1 else 0 : ℝ) - 1‖ ≤ (1 : ℝ) := by
    filter_upwards [] with uz
    split_ifs <;> norm_num
  have hiProd := (hi.comp_fst (M.instKernel x)).mul_bdd hm.aestronglyMeasurable hb
  calc
    _ = ∫ u in Ioc 0 (pLow M.prop x), f u *
        (∫ z, (if u ≤ q z x then 1 else 0 : ℝ) - 1 ∂M.instKernel x) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro u hu
      dsimp only
      rw [policyWeight_below_support M q x u hu.2]
    _ = ∫ u in Ioc 0 (pLow M.prop x), ∫ z,
        f u * ((if u ≤ q z x then 1 else 0 : ℝ) - 1) ∂M.instKernel x := by
      simp only [integral_const_mul]
    _ = ∫ z, (∫ u in Ioc 0 (pLow M.prop x),
        f u * ((if u ≤ q z x then 1 else 0 : ℝ) - 1)) ∂M.instKernel x :=
      integral_integral_swap hiProd
    _ = _ := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [] with z
      exact threshold_complement_integral f _ (q z x) (hr z x)

end Papers.TbsPrteOptimalTransport
