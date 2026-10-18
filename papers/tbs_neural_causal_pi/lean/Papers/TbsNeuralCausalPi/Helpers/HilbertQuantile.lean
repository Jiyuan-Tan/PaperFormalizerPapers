module
public import StatLean.HypothesisTesting.ForMathlib.QuantileFunction
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.Holder
public import Mathlib.MeasureTheory.Integral.IntegrableOn
/-! # Quantile reparameterization of a dominated interval law

The endpoint at zero is fixed explicitly, so the reparameterization is continuous
on the closed interval even when the target law has atoms.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

-- @node: hilbertIntervalQuantile
/-- For [a real-valued measure rho](hyp:rho) and [a probability level t](hyp:t),
the [endpoint-adjusted quantile](goal) is [zero when t is nonpositive](step:1)
and [the generalized inverse of rho's cumulative distribution function otherwise](step:2). -/
noncomputable def hilbertIntervalQuantile (rho : Measure ℝ) (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else StatLean.HypothesisTesting.quantile (cdf rho) t

-- @node: intervalLaw_cdf_one
/-- If [a probability law rho](hyp:rho) [assigns mass one to the closed unit interval](hyp:hmass),
[its cumulative distribution function equals one at one](goal). -/
lemma intervalLaw_cdf_one (rho : Measure ℝ) [IsProbabilityMeasure rho]
    (hmass : rho (Set.Icc (0 : ℝ) 1) = 1) : cdf rho 1 = 1 := by
  have h : rho (Set.Iic 1) = 1 := le_antisymm (prob_le_one) (by
    rw [← hmass]
    exact measure_mono (fun x hx => hx.2))
  rw [cdf_eq_real, measureReal_def, h, ENNReal.toReal_one]

-- @node: intervalLaw_cdf_zero_of_neg
/-- If [a probability law rho](hyp:rho) [assigns mass one to the closed unit interval](hyp:hmass)
and [x is negative](hyp:hx), [its cumulative distribution function is zero at x](goal). -/
lemma intervalLaw_cdf_zero_of_neg (rho : Measure ℝ) [IsProbabilityMeasure rho]
    (hmass : rho (Set.Icc (0 : ℝ) 1) = 1) {x : ℝ} (hx : x < 0) :
    cdf rho x = 0 := by
  have hc : rho (Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
    rw [measure_compl measurableSet_Icc (measure_ne_top _ _), measure_univ, hmass]
    simp
  have hz : rho (Set.Iic x) = 0 := measure_mono_null (by
    intro y hy hmem
    exact (not_le_of_gt hx) (hmem.1.trans hy)) hc
  rw [cdf_eq_real, measureReal_def, hz, ENNReal.toReal_zero]

-- @node: intervalLaw_quantile_le_iff
/-- For [a probability law rho](hyp:rho) [assigning mass one to the closed unit interval](hyp:hmass)
and a level t that [is positive](hyp:ht) and [is at most one](hyp:ht1),
[the endpoint-adjusted t-quantile is at most x if and only if the cumulative
distribution function at x is at least t](goal). -/
lemma intervalLaw_quantile_le_iff (rho : Measure ℝ) [IsProbabilityMeasure rho]
    (hmass : rho (Set.Icc (0 : ℝ) 1) = 1) {t x : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) :
    hilbertIntervalQuantile rho t ≤ x ↔ t ≤ cdf rho x := by
  rw [hilbertIntervalQuantile, if_neg (not_le_of_gt ht)]
  apply StatLean.HypothesisTesting.quantile_le_iff (monotone_cdf rho)
    (fun y => (cdf rho).right_continuous y)
  · exact ⟨1, by simpa [intervalLaw_cdf_one rho hmass] using ht1⟩
  · refine ⟨0, fun y hy => ?_⟩
    by_contra h
    have hy0 : y < 0 := lt_of_not_ge h
    have hz := intervalLaw_cdf_zero_of_neg rho hmass hy0
    change t ≤ cdf rho y at hy
    linarith

-- @node: hilbertIntervalQuantile_mem
/-- If [a probability law rho](hyp:rho) [assigns mass one to the closed unit interval](hyp:hmass)
and [t belongs to that interval](hyp:ht), [its endpoint-adjusted t-quantile also belongs
to the closed unit interval](goal). -/
lemma hilbertIntervalQuantile_mem (rho : Measure ℝ) [IsProbabilityMeasure rho]
    (hmass : rho (Set.Icc (0 : ℝ) 1) = 1) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    hilbertIntervalQuantile rho t ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases h0 : t ≤ 0
  · simp [hilbertIntervalQuantile, h0]
  · have hp : 0 < t := lt_of_not_ge h0
    have hle := (intervalLaw_quantile_le_iff rho hmass hp ht.2 (x := 1)).2
      (by simpa [intervalLaw_cdf_one rho hmass] using ht.2)
    refine ⟨?_, hle⟩
    by_contra hn
    have hneg : hilbertIntervalQuantile rho t < 0 := lt_of_not_ge hn
    have ha := (intervalLaw_quantile_le_iff rho hmass hp ht.2).1 le_rfl
    rw [intervalLaw_cdf_zero_of_neg rho hmass hneg] at ha
    linarith

-- @node: hilbertIntervalQuantile_map
/-- For [any probability law rho on the real line](hyp:rho), [applying its
endpoint-adjusted quantile to uniform time on the closed unit interval produces rho](goal). -/
lemma hilbertIntervalQuantile_map (rho : Measure ℝ) [IsProbabilityMeasure rho] :
    (volume.restrict (Set.Icc (0 : ℝ) 1)).map (hilbertIntervalQuantile rho) = rho := by
  have heq : hilbertIntervalQuantile rho =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
      StatLean.HypothesisTesting.quantile (cdf rho) := by
    rw [Measure.restrict_congr_set Ioo_ae_eq_Icc.symm]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp [hilbertIntervalQuantile, not_le_of_gt ht.1]
  rw [Measure.map_congr heq]
  exact StatLean.HypothesisTesting.map_quantile_uniform rho (cdf rho)
    (fun x => cdf_eq_real rho x)

-- @node: dominatedInterval_cdf_increment
/-- For [a probability law rho](hyp:rho) and [a nonnegative constant c](hyp:c), suppose
[rho dominates c times Lebesgue measure restricted to the unit interval](hyp:hdom).
If [a is nonnegative](hyp:ha), [b is at most one](hyp:hb), and [a is at most b](hyp:hab),
[the increase in the cumulative distribution function from a to b is at least c times the length of that interval](goal). -/
lemma dominatedInterval_cdf_increment (rho : Measure ℝ) [IsProbabilityMeasure rho]
    (c : ℝ≥0) (hdom : c • volume.restrict (Set.Icc (0 : ℝ) 1) ≤ rho)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    (c : ℝ) * (b-a) ≤ cdf rho b - cdf rho a := by
  have h := hdom (Set.Ioc a b)
  have hsub : Set.Ioc a b ⊆ Set.Icc (0 : ℝ) 1 :=
    fun x hx => ⟨ha.trans hx.1.le, hx.2.trans hb⟩
  rw [Measure.smul_apply, Measure.restrict_apply measurableSet_Ioc,
    Set.inter_eq_left.mpr hsub, Real.volume_Ioc, ← measure_cdf rho,
    StieltjesFunction.measure_Ioc] at h
  have hn : 0 ≤ cdf rho b - cdf rho a := sub_nonneg.mpr (monotone_cdf rho hab)
  have hreal := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) h
  simpa [ENNReal.toReal_smul, ENNReal.toReal_ofReal, sub_nonneg.mpr hab, hn,
    NNReal.smul_def, smul_eq_mul] using hreal

-- @node: hilbertIntervalQuantile_cdf_ge
/-- For [a probability law rho](hyp:rho) [assigning mass one to the closed unit interval](hyp:hmass)
and [a level t in that interval](hyp:ht), [the cumulative distribution function
evaluated at the endpoint-adjusted t-quantile is at least t](goal). -/
lemma hilbertIntervalQuantile_cdf_ge (rho : Measure ℝ) [IsProbabilityMeasure rho]
    (hmass : rho (Set.Icc (0 : ℝ) 1) = 1) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    t ≤ cdf rho (hilbertIntervalQuantile rho t) := by
  by_cases h0 : t ≤ 0
  · exact h0.trans (cdf_nonneg rho _)
  · exact (intervalLaw_quantile_le_iff rho hmass (lt_of_not_ge h0) ht.2).1 le_rfl

-- @node: hilbertIntervalQuantile_monoOn
/-- If [a probability law rho](hyp:rho) [assigns mass one to the closed unit interval](hyp:hmass),
[its endpoint-adjusted quantile is nondecreasing on that interval](goal). -/
lemma hilbertIntervalQuantile_monoOn (rho : Measure ℝ) [IsProbabilityMeasure rho]
    (hmass : rho (Set.Icc (0 : ℝ) 1) = 1) :
    MonotoneOn (hilbertIntervalQuantile rho) (Set.Icc (0 : ℝ) 1) := by
  intro u hu v hv huv
  by_cases h0 : u ≤ 0
  · simpa [hilbertIntervalQuantile, h0] using (hilbertIntervalQuantile_mem rho hmass hv).1
  · exact (intervalLaw_quantile_le_iff rho hmass (lt_of_not_ge h0) hu.2).2
      (huv.trans (hilbertIntervalQuantile_cdf_ge rho hmass hv))

-- @node: hilbertIntervalQuantile_increment
/-- Let [rho be a probability law](hyp:rho) [assigning mass one to the closed unit interval](hyp:hmass),
and let [c be a nonnegative constant](hyp:c) that [is positive](hyp:hc).
If [rho dominates c times uniform unit-interval measure](hyp:hdom), [u lies in the unit interval](hyp:hu),
[v lies there too](hyp:hv), and [u is at most v](hyp:huv), [c times the increase in the
endpoint-adjusted quantile from u to v is at most v minus u](goal). -/
lemma hilbertIntervalQuantile_increment (rho : Measure ℝ) [IsProbabilityMeasure rho]
    (hmass : rho (Set.Icc (0 : ℝ) 1) = 1)
    (c : ℝ≥0) (hc : 0 < c)
    (hdom : c • volume.restrict (Set.Icc (0 : ℝ) 1) ≤ rho)
    {u v : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ Set.Icc (0 : ℝ) 1)
    (huv : u ≤ v) :
    (c : ℝ) * (hilbertIntervalQuantile rho v - hilbertIntervalQuantile rho u) ≤ v-u := by
  have hcR : 0 < (c : ℝ) := hc
  have hqu := hilbertIntervalQuantile_mem rho hmass hu
  have hqv := hilbertIntervalQuantile_mem rho hmass hv
  have hq := hilbertIntervalQuantile_monoOn rho hmass hu hv huv
  by_cases heq : hilbertIntervalQuantile rho u = hilbertIntervalQuantile rho v
  · rw [← heq, sub_self, mul_zero]
    exact sub_nonneg.mpr huv
  · have hlt : hilbertIntervalQuantile rho u < hilbertIntervalQuantile rho v :=
      lt_of_le_of_ne hq heq
    have hvpos : 0 < v := by
      by_contra h
      have hz : hilbertIntervalQuantile rho v = 0 := by
        simp [hilbertIntervalQuantile, le_of_not_gt h]
      linarith [hqu.1]
    apply le_of_forall_pos_le_add
    intro e he
    obtain ⟨b, hb0, hb1⟩ := exists_between
      (show max (hilbertIntervalQuantile rho u)
        (hilbertIntervalQuantile rho v - e / (c : ℝ)) < hilbertIntervalQuantile rho v by
          exact max_lt hlt (sub_lt_self _ (div_pos he hcR)))
    have hub : hilbertIntervalQuantile rho u < b := (le_max_left _ _).trans_lt hb0
    have heb : hilbertIntervalQuantile rho v - e / (c : ℝ) < b :=
      (le_max_right _ _).trans_lt hb0
    have hcb : cdf rho b < v := lt_of_not_ge (fun h =>
      (not_le_of_gt hb1) ((intervalLaw_quantile_le_iff rho hmass hvpos hv.2).2 h))
    have hinc := dominatedInterval_cdf_increment rho c hdom hqu.1
      (hb1.le.trans hqv.2) hub.le
    have hcu := hilbertIntervalQuantile_cdf_ge rho hmass hu
    have hecb : (c : ℝ) * (hilbertIntervalQuantile rho v - b) < e := by
      have := (lt_div_iff₀ hcR).1 (show hilbertIntervalQuantile rho v - b < e / (c : ℝ) by linarith)
      nlinarith
    nlinarith

-- @node: hilbertIntervalQuantile_lipschitzOn
/-- For [a probability law rho](hyp:rho) [assigning mass one to the closed unit interval](hyp:hmass)
and [a nonnegative constant c](hyp:c) that [is positive](hyp:hc), if
[rho dominates c times uniform unit-interval measure](hyp:hdom), [its endpoint-adjusted
quantile is Lipschitz on the unit interval with constant 1/c](goal). -/
lemma hilbertIntervalQuantile_lipschitzOn (rho : Measure ℝ) [IsProbabilityMeasure rho]
    (hmass : rho (Set.Icc (0 : ℝ) 1) = 1)
    (c : ℝ≥0) (hc : 0 < c)
    (hdom : c • volume.restrict (Set.Icc (0 : ℝ) 1) ≤ rho) :
    LipschitzOnWith c⁻¹ (hilbertIntervalQuantile rho) (Set.Icc (0 : ℝ) 1) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu v hv
  have hcR : 0 < (c : ℝ) := hc
  have hordered : ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1, a ≤ b →
      dist (hilbertIntervalQuantile rho a) (hilbertIntervalQuantile rho b) ≤
        (c⁻¹ : ℝ≥0) * dist a b := by
    intro a ha b hb hab
    have hinc := hilbertIntervalQuantile_increment rho hmass c hc hdom ha hb hab
    have hq := hilbertIntervalQuantile_monoOn rho hmass ha hb hab
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hq),
      abs_of_nonpos (sub_nonpos.mpr hab), NNReal.coe_inv]
    have hbound := (le_div_iff₀ hcR).2 (by nlinarith :
      (hilbertIntervalQuantile rho b - hilbertIntervalQuantile rho a) * (c : ℝ) ≤ b-a)
    simpa [div_eq_mul_inv, mul_comm] using hbound
  rcases le_total u v with h | h
  · exact hordered u hu v hv h
  · simpa only [dist_comm] using hordered v hv u hu h

-- @node: hilbertIntervalQuantile_one
/-- For [a probability law rho](hyp:rho) [assigning mass one to the closed unit interval](hyp:hmass)
and [a nonnegative constant c](hyp:c) that [is positive](hyp:hc), if
[rho dominates c times uniform unit-interval measure](hyp:hdom), [its endpoint-adjusted
quantile equals one at probability level one](goal). -/
lemma hilbertIntervalQuantile_one (rho : Measure ℝ) [IsProbabilityMeasure rho]
    (hmass : rho (Set.Icc (0 : ℝ) 1) = 1)
    (c : ℝ≥0) (hc : 0 < c)
    (hdom : c • volume.restrict (Set.Icc (0 : ℝ) 1) ≤ rho) :
    hilbertIntervalQuantile rho 1 = 1 := by
  have hq := hilbertIntervalQuantile_mem rho hmass (t := 1) ⟨zero_le_one, le_rfl⟩
  apply le_antisymm hq.2
  by_contra h
  obtain ⟨b, hb0, hb1⟩ := exists_between (lt_of_not_ge h)
  have hcb : cdf rho b < 1 := by
    have hi := dominatedInterval_cdf_increment rho c hdom (hq.1.trans hb0.le)
      (b := 1) le_rfl hb1.le
    rw [intervalLaw_cdf_one rho hmass] at hi
    have hp : 0 < (c : ℝ) * (1-b) := mul_pos hc (sub_pos.mpr hb1)
    linarith
  have hge := (intervalLaw_quantile_le_iff rho hmass zero_lt_one le_rfl).1 hb0.le
  linarith

-- @node: exists_dominated_interval_reparameterization
/-- For [a probability law rho](hyp:rho) [assigning mass one to the closed unit interval](hyp:hmass)
and [a nonnegative constant c](hyp:c) that [is positive](hyp:hc), suppose
[rho dominates c times uniform unit-interval measure](hyp:hdom). Then [there exists
a continuous time change mapping the unit interval into itself, fixing zero and one,
with Lipschitz constant 1/c, that sends uniform time to rho](goal). -/
lemma exists_dominated_interval_reparameterization (rho : Measure ℝ)
    [IsProbabilityMeasure rho] (hmass : rho (Set.Icc (0 : ℝ) 1) = 1)
    (c : ℝ≥0) (hc : 0 < c)
    (hdom : c • volume.restrict (Set.Icc (0 : ℝ) 1) ≤ rho) :
    ∃ Q : ℝ → ℝ, LipschitzOnWith c⁻¹ Q (Set.Icc (0 : ℝ) 1) ∧
      ContinuousOn Q (Set.Icc (0 : ℝ) 1) ∧
      Set.MapsTo Q (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1) ∧
      Q 0 = 0 ∧ Q 1 = 1 ∧
      (volume.restrict (Set.Icc (0 : ℝ) 1)).map Q = rho := by
  have hLip := hilbertIntervalQuantile_lipschitzOn rho hmass c hc hdom
  exact ⟨hilbertIntervalQuantile rho, hLip, hLip.continuousOn,
    fun _ ht => hilbertIntervalQuantile_mem rho hmass ht,
    by simp [hilbertIntervalQuantile], hilbertIntervalQuantile_one rho hmass c hc hdom,
    hilbertIntervalQuantile_map rho⟩

-- @node: exists_holder_quantile_reparameterization
/-- Let [rho be a probability law](hyp:rho) [assigning mass one to the closed unit interval](hyp:hmass),
and let [c be a nonnegative constant](hyp:c) that [is positive](hyp:hc), with
[rho dominating c times uniform unit-interval measure](hyp:hdom).
For [a curve H](hyp:H), [nonnegative Hölder constant A and exponent r](hyp:A,r),
[positive r](hyp:hr), and [a Hölder bound with constant A and exponent r on the unit interval](hyp:hH),
[there exists a continuous curve whose uniform-time law equals the image of rho under H
and whose Hölder exponent is r and constant is A times c to the power minus r](goal). -/
lemma exists_holder_quantile_reparameterization {Y : Type*}
    [PseudoEMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (rho : Measure ℝ) [IsProbabilityMeasure rho]
    (hmass : rho (Set.Icc (0 : ℝ) 1) = 1) (c : ℝ≥0) (hc : 0 < c)
    (hdom : c • volume.restrict (Set.Icc (0 : ℝ) 1) ≤ rho)
    (H : ℝ → Y) (A r : ℝ≥0) (hr : 0 < r)
    (hH : HolderOnWith A r H (Set.Icc (0 : ℝ) 1)) :
    ∃ gamma : ℝ → Y,
      ContinuousOn gamma (Set.Icc (0 : ℝ) 1) ∧
      HolderOnWith (A * c⁻¹ ^ (r : ℝ)) r gamma (Set.Icc (0 : ℝ) 1) ∧
      (volume.restrict (Set.Icc (0 : ℝ) 1)).map gamma = rho.map H := by
  obtain ⟨Q, hLip, hcont, hmem, hzero, hone, hmap⟩ :=
    exists_dominated_interval_reparameterization rho hmass c hc hdom
  have hholder : HolderOnWith (A * c⁻¹ ^ (r : ℝ)) r (H ∘ Q) (Set.Icc (0 : ℝ) 1) := by
    simpa only [mul_one] using hH.comp hLip.holderOnWith hmem
  refine ⟨H ∘ Q, hholder.continuousOn hr, hholder, ?_⟩
  have hQmeas : AEMeasurable Q (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    first | fun_prop | exact hcont.aemeasurable measurableSet_Icc
  have hHmeas : AEMeasurable H rho := by
    have hrestrict : rho.restrict (Set.Icc (0 : ℝ) 1) = rho :=
      Measure.restrict_eq_self_of_ae_mem
        ((mem_ae_iff_prob_eq_one measurableSet_Icc).2 hmass)
    rw [← hrestrict]
    exact (hH.continuousOn hr).aemeasurable measurableSet_Icc
  rw [← AEMeasurable.map_map_of_aemeasurable (by rwa [hmap]) hQmeas, hmap]

end Papers.TbsNeuralCausalPi
