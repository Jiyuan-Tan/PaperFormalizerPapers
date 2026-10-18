module
public import Papers.TbsPrteOptimalTransport.Helpers.ConnectedReduction
/-!
# The boundary transport term for a connected instrument

On the lower propensity gap the policy weight decreases with resistance.
Reflection of the uniform resistance coordinate therefore supplies a quantile
version of its law, including when that law has atoms.
-/
public section
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false
set_option linter.style.haveILetI false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal Topology

-- @node: uniformInterval_zero_map
/-- For a [scale b](hyp:b) that [is positive](hyp:hb), [multiplying a uniform
unit-interval draw by b gives the uniform distribution between zero and b](goal). -/
lemma uniformInterval_zero_map (b : ℝ) (hb : 0 < b) :
    Causalean.Stat.unifOI.map (fun t => b * t) = uniformInterval 0 b := by
  have he : (fun t : ℝ => b * t) ⁻¹' Ioo 0 b = Ioo 0 1 := by
    ext t
    simp only [mem_preimage, mem_Ioo]
    constructor
    · intro ht
      constructor <;> nlinarith
    · intro ht
      constructor <;> nlinarith
  rw [Causalean.Stat.unifOI, ← he, ← Measure.restrict_map (by fun_prop) measurableSet_Ioo,
    Real.map_volume_mul_left hb.ne', Measure.restrict_smul]
  simp only [abs_of_pos (inv_pos.mpr hb), uniformInterval, sub_zero]
  rw [ENNReal.ofReal_inv_of_pos hb]

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)

-- @node: policyWeight_boundary_antitone
/-- In the latent instrumental-variable model, for a [policy propensity
function](hyp:q) that [is jointly measurable](hyp:hq) and a [covariate value](hyp:x),
[the policy weight is nonincreasing in resistance at or below the infimum of baseline
propensity values](goal). -/
lemma policyWeight_boundary_antitone (q : Z → X → ℝ)
    (hq : Measurable (Function.uncurry q)) (x : X) :
    AntitoneOn (policyWeight M q x) (Iic (pLow M.prop x)) := by
  intro a ha b hb hab
  rw [policyWeight_below_support M q x b hb, policyWeight_below_support M q x a ha]
  letI := M.instKernel_markov
  have hi (r : ℝ) : Integrable (fun z => (if r ≤ q z x then 1 else 0 : ℝ) - 1)
      (M.instKernel x) := by
    apply Integrable.of_bound (C := 1)
    · apply Measurable.aestronglyMeasurable
      have hqm : Measurable (fun z => q z x) := by fun_prop
      exact (Measurable.ite (measurableSet_le measurable_const hqm)
        measurable_const measurable_const).sub_const 1
    · filter_upwards [] with z
      split_ifs <;> norm_num
  apply integral_mono (hi b) (hi a)
  · intro z
    by_cases hq' : b ≤ q z x
    · simp only [if_pos hq', if_pos (hab.trans hq')]; exact le_rfl
    · simp only [if_neg hq']
      split_ifs <;> norm_num

-- @node: antitone_uniform_quantile_reflection
/-- For a [real-valued function](hyp:f) that [is nonincreasing on the open unit
interval](hyp:hf), [evaluating the function at one minus a uniform draw agrees almost
surely with the quantile at that draw of the function's distribution under uniform
sampling](goal). -/
lemma antitone_uniform_quantile_reflection (f : ℝ → ℝ)
    (hf : AntitoneOn f (Ioo (0 : ℝ) 1)) :
    (fun t => f (1 - t)) =ᵐ[Causalean.Stat.unifOI]
      Causalean.Stat.quantile (Causalean.Stat.unifOI.map f) := by
  have hm : AEMeasurable f Causalean.Stat.unifOI :=
    aemeasurable_restrict_of_antitoneOn measurableSet_Ioo hf
  letI : IsProbabilityMeasure (Causalean.Stat.unifOI.map f) :=
    Measure.isProbabilityMeasure_map hm
  have hr : MonotoneOn (fun t => f (1 - t)) (Ioo (0 : ℝ) 1) := by
    intro a ha b hb hab
    apply hf (show 1 - b ∈ Ioo (0 : ℝ) 1 by constructor <;> linarith [hb.1, hb.2])
      (show 1 - a ∈ Ioo (0 : ℝ) 1 by constructor <;> linarith [ha.1, ha.2])
    linarith
  have hlaw : Causalean.Stat.unifOI.map (fun t => f (1 - t)) =
      Causalean.Stat.unifOI.map f := by
    change Causalean.Stat.unifOI.map (f ∘ (fun t : ℝ => 1 - t)) = _
    have hm' : AEMeasurable f (Causalean.Stat.unifOI.map (fun t : ℝ => 1 - t)) := by
      rw [Causalean.Stat.map_one_sub_unifOI]; exact hm
    rw [← AEMeasurable.map_map_of_aemeasurable hm' (by fun_prop),
      Causalean.Stat.map_one_sub_unifOI]
  have hc := Toolkit.Tricks.Probability.Moments.countable_ne_quantile_of_monotoneOn_of_map_eq
    _ (fun t => f (1 - t)) hr hlaw
  apply (ae_restrict_iff' measurableSet_Ioo).mpr
  filter_upwards [hc.ae_notMem volume] with t ht hmem
  exact not_ne_iff.mp (fun hn => ht ⟨hmem, hn⟩)

-- @node: policyWeight_boundary_quantile
/-- In the latent instrumental-variable model, consider a [policy propensity
function](hyp:q) that [is jointly measurable](hyp:hq), a [covariate value](hyp:x), and
a [boundary length b](hyp:b) that [is positive](hyp:hb) and [does not exceed the
infimum of baseline propensity values at those covariates](hyp:hbl). Then [the policy
weight at b times one minus a uniform unit-interval draw equals almost surely the
quantile, at that draw, of the policy-weight distribution under uniform resistance
between zero and b](goal). -/
lemma policyWeight_boundary_quantile (q : Z → X → ℝ)
    (hq : Measurable (Function.uncurry q)) (x : X) (b : ℝ)
    (hb : 0 < b) (hbl : b ≤ pLow M.prop x) :
    (fun t => policyWeight M q x (b * (1 - t))) =ᵐ[Causalean.Stat.unifOI]
      Causalean.Stat.quantile ((uniformInterval 0 b).map (policyWeight M q x)) := by
  let f := fun t => policyWeight M q x (b * t)
  have hf : AntitoneOn f (Ioo (0 : ℝ) 1) := by
    intro a ha c hc hac
    apply policyWeight_boundary_antitone M q hq x
    · change b * a ≤ pLow M.prop x
      exact (mul_le_of_le_one_right hb.le ha.2.le).trans hbl
    · change b * c ≤ pLow M.prop x
      exact (mul_le_of_le_one_right hb.le hc.2.le).trans hbl
    · exact mul_le_mul_of_nonneg_left hac hb.le
  have hm : AEMeasurable (policyWeight M q x) (uniformInterval 0 b) := by
    apply AEMeasurable.smul_measure
    apply aemeasurable_restrict_of_antitoneOn measurableSet_Ioo
    exact (policyWeight_boundary_antitone M q hq x).mono
      (fun a ha => ha.2.le.trans hbl)
  have hlaw : Causalean.Stat.unifOI.map f =
      (uniformInterval 0 b).map (policyWeight M q x) := by
    change Causalean.Stat.unifOI.map (policyWeight M q x ∘ (fun t => b * t)) = _
    have hm' : AEMeasurable (policyWeight M q x)
        (Causalean.Stat.unifOI.map (fun t => b * t)) := by
      rw [uniformInterval_zero_map b hb]; exact hm
    rw [← AEMeasurable.map_map_of_aemeasurable hm' (by fun_prop),
      uniformInterval_zero_map b hb]
  have hr := antitone_uniform_quantile_reflection f hf
  rw [hlaw] at hr
  exact hr

-- @node: unit_integral_reflection
/-- For any [real-valued function](hyp:f), [its Lebesgue integral over the open unit
interval is unchanged when its argument is replaced by one minus that argument](goal). -/
lemma unit_integral_reflection (f : ℝ → ℝ) :
    (∫ t in Ioo (0 : ℝ) 1, f (1 - t)) = ∫ t in Ioo (0 : ℝ) 1, f t := by
  simp only [restrict_Ioo_eq_restrict_Ioc]
  rw [← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_sub_left]
  norm_num
  exact intervalIntegral.integral_of_le zero_le_one

-- @node: boundary_quantile_product_identity
/-- In the latent instrumental-variable model, take a [policy propensity
function](hyp:q) that [is jointly measurable](hyp:hq), a [covariate value](hyp:x), a
[boundary length b](hyp:b) that [is positive](hyp:hb) and [does not exceed the
infimum of baseline propensity values](hyp:hbl), a [real-valued factor Q](hyp:Q), and
an [upper-versus-lower choice](hyp:upper). Then [the unit-interval integral of Q times
the boundary policy-weight quantile equals the integral of the policy weight at b
times the integration coordinate multiplied by Q at the reflected coordinate for the
upper choice and the original coordinate for the lower choice; the quantile on the
left uses the original coordinate for the upper choice and its reflection for the
lower choice](goal). -/
lemma boundary_quantile_product_identity (q : Z → X → ℝ)
    (hq : Measurable (Function.uncurry q)) (x : X) (b : ℝ)
    (hb : 0 < b) (hbl : b ≤ pLow M.prop x) (Q : ℝ → ℝ) (upper : Bool) :
    (∫ t in Ioo (0 : ℝ) 1, Q t *
      Causalean.Stat.quantile ((uniformInterval 0 b).map (policyWeight M q x))
        (if upper then t else 1 - t)) =
    ∫ t in Ioo (0 : ℝ) 1, Q (if upper then 1 - t else t) *
      policyWeight M q x (b * t) := by
  have he := policyWeight_boundary_quantile M q hq x b hb hbl
  cases upper with
  | true =>
    simp only [↓reduceIte]
    calc
      _ = ∫ t in Ioo (0 : ℝ) 1, Q t * policyWeight M q x (b * (1 - t)) :=
        integral_congr_ae (he.mono fun t ht => congrArg (Q t * ·) ht.symm)
      _ = _ := by
        have hh := unit_integral_reflection
          (fun t => Q (1 - t) * policyWeight M q x (b * t))
        simpa only [sub_sub_cancel] using hh
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have her : (fun t => policyWeight M q x (b * t)) =ᵐ[Causalean.Stat.unifOI]
        (fun t => Causalean.Stat.quantile
          ((uniformInterval 0 b).map (policyWeight M q x)) (1 - t)) := by
      have hh : ∀ᵐ t ∂Causalean.Stat.unifOI.map (fun t : ℝ => 1 - t),
          policyWeight M q x (b * (1 - t)) =
            Causalean.Stat.quantile ((uniformInterval 0 b).map (policyWeight M q x)) t := by
        rw [Causalean.Stat.map_one_sub_unifOI]; exact he
      have hp := ae_of_ae_map (f := fun t : ℝ => 1 - t) (by fun_prop) hh
      filter_upwards [hp] with t ht
      simpa only [sub_sub_cancel] using ht
    exact integral_congr_ae (her.mono fun t ht => congrArg (Q t * ·) ht.symm)

-- @node: boundary_integral_rescale
/-- For a [boundary length b](hyp:b) that [is positive](hyp:hb), a [real-valued
factor Q](hyp:Q), and a [real-valued weight w](hyp:w), [b times the unit-interval
integral of Q at t multiplied by w at b times t equals the integral from zero
(excluded) to b (included) of Q at u divided by b multiplied by w at u](goal). -/
lemma boundary_integral_rescale (b : ℝ) (hb : 0 < b) (Q w : ℝ → ℝ) :
    b * (∫ t in Ioo (0 : ℝ) 1, Q t * w (b * t)) =
      ∫ u in Ioc 0 b, Q (u / b) * w u := by
  simp only [restrict_Ioo_eq_restrict_Ioc]
  rw [← intervalIntegral.integral_of_le zero_le_one,
    ← intervalIntegral.integral_of_le hb.le]
  have he := intervalIntegral.smul_integral_comp_mul_left
    (fun u => Q (u / b) * w u) (a := 0) (b := 1) b
  simpa only [smul_eq_mul, mul_zero, mul_one, mul_div_cancel_left₀ _ hb.ne'] using he

-- @node: boundary_transport_truncated_integral
/-- In the latent instrumental-variable model, let a [policy propensity
function](hyp:q) be [jointly measurable](hyp:hq) and [nonnegative everywhere](hyp:hr).
Fix a [covariate value](hyp:x), a [boundary length b](hyp:b) that [is positive](hyp:hb)
and [equals the infimum of baseline propensity values](hyp:hbl), a [real-valued
factor Q](hyp:Q), and an [upper-versus-lower choice](hyp:upper). If [Q evaluated at
one minus resistance divided by b for the upper choice, or resistance divided by b
for the lower choice, is integrable from zero to b](hyp:hi), then [b times the
unit-interval product integral of Q and the boundary policy-weight quantile, using
the original rank for the upper quantile and its reflection for the lower quantile,
equals minus the conditional instrument average of the integral of that rescaled Q
from the smaller of b and policy propensity to b](goal). -/
lemma boundary_transport_truncated_integral (q : Z → X → ℝ)
    (hq : Measurable (Function.uncurry q)) (hr : ∀ z x, 0 ≤ q z x)
    (x : X) (b : ℝ) (hb : 0 < b) (hbl : b = pLow M.prop x)
    (Q : ℝ → ℝ) (upper : Bool)
    (hi : IntegrableOn (fun u => Q (if upper then 1 - u / b else u / b)) (Ioc 0 b)) :
    b * (∫ t in Ioo (0 : ℝ) 1, Q t *
      Causalean.Stat.quantile ((uniformInterval 0 b).map (policyWeight M q x))
        (if upper then t else 1 - t)) =
    -(∫ z, (∫ v in Ioc (min b (q z x)) b,
      Q (if upper then 1 - v / b else v / b)) ∂M.instKernel x) := by
  rw [boundary_quantile_product_identity M q hq x b hb hbl.le Q upper,
    boundary_integral_rescale b hb
      (fun t => Q (if upper then 1 - t else t)) (policyWeight M q x)]
  subst b
  exact policyWeight_boundary_integral M q hq hr x _ hi

-- @node: supported_quantile_resistance_integrable
/-- For a [probability distribution on the real line](hyp:ν), [lower and upper
bounds a and c](hyp:a,c), a [boundary length b](hyp:b) that [is positive](hyp:hb),
and an [upper-versus-lower choice](hyp:upper), suppose [every quantile at an interior
unit-interval rank lies between a and c](hyp:hs). Then [the quantile evaluated at
one minus resistance divided by b for the upper choice, or resistance divided by b
for the lower choice, is integrable from zero (excluded) to b (included)](goal). -/
lemma supported_quantile_resistance_integrable (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (a c b : ℝ) (hb : 0 < b)
    (hs : ∀ t ∈ Ioo (0 : ℝ) 1, Causalean.Stat.quantile ν t ∈ Icc a c)
    (upper : Bool) :
    IntegrableOn (fun v => Causalean.Stat.quantile ν
      (if upper then 1 - v / b else v / b)) (Ioc 0 b) := by
  have hdiv {v : ℝ} (hv : v ∈ Ioo 0 b) : v / b ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos hv.1 hb, (div_lt_one hb).mpr hv.2⟩
  have href {v : ℝ} (hv : v ∈ Ioo 0 b) : 1 - v / b ∈ Ioo (0 : ℝ) 1 := by
    have ht := hdiv hv
    constructor <;> linarith [ht.1, ht.2]
  have hm : AEMeasurable (fun v => Causalean.Stat.quantile ν
      (if upper then 1 - v / b else v / b)) (volume.restrict (Ioo 0 b)) := by
    cases upper with
    | false =>
      apply aemeasurable_restrict_of_monotoneOn measurableSet_Ioo
      intro v hv w hw hvw
      exact Causalean.Stat.monotoneOn_quantile ν (hdiv hv) (hdiv hw)
        (div_le_div_of_nonneg_right hvw hb.le)
    | true =>
      apply aemeasurable_restrict_of_antitoneOn measurableSet_Ioo
      intro v hv w hw hvw
      apply Causalean.Stat.monotoneOn_quantile ν (href hw) (href hv)
      exact sub_le_sub_left (div_le_div_of_nonneg_right hvw hb.le) 1
  have hi : Integrable (fun v => Causalean.Stat.quantile ν
      (if upper then 1 - v / b else v / b)) (volume.restrict (Ioo 0 b)) := by
    apply Integrable.of_bound hm.aestronglyMeasurable (max |a| |c|)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    have ht : (if upper then 1 - v / b else v / b) ∈ Ioo (0 : ℝ) 1 := by
      cases upper <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · exact hdiv hv
      · exact href hv
    have hvq := hs _ ht
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · exact (neg_le_neg (le_max_left |a| |c|)).trans ((neg_abs_le a).trans hvq.1)
    · exact hvq.2.trans ((le_abs_self c).trans (le_max_right |a| |c|))
  change Integrable _ (volume.restrict (Ioc 0 b))
  rw [restrict_Ioo_eq_restrict_Ioc] at hi
  exact hi

-- @node: connected_boundary_transport_integral
/-- For the latent instrumental-variable model, choose [a covariate-indexed
fallback probability distribution supported on the outcome domain](hyp:zeroLaw).
Assume [the structural conditions of potential-outcome support, consistency,
conditional instrument exogeneity, threshold crossing, uniform resistance, common
instrument support, and compact domains](hyp:h), [known outcome endpoints](hyp:he),
[propensity continuity on each instrument component](hyp:hc), [finitely many
instrument components](hyp:hfin), and [a connected instrument domain](hyp:hconn).
For a [policy transformation](hyp:phi) that [is jointly measurable on unit-interval
propensities and preserves that interval](hyp:hp), and an [upper-versus-lower
choice](hyp:upper), [at almost every covariate value with positive minimum propensity,
the minimum propensity times the lower-gap product integral of outcome and
policy-weight quantiles equals minus the conditional instrument average of the
boundary-outcome quantile integrated from the smaller of policy propensity and
minimum propensity to minimum propensity; the upper choice pairs equal ranks and
uses one minus resistance divided by minimum propensity on the right, while the
lower choice pairs opposite ranks and uses resistance divided by minimum
propensity](goal). -/
lemma connected_boundary_transport_integral
    (zeroLaw : X → {ν : ProbabilityMeasure ℝ // ν.toMeasure M.Ysetᶜ = 0})
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (hc : PropensityContinuousOnComponents M) (hfin : FiniteInstrumentComponents Z)
    (hconn : InstrumentConnectedReduction Z) (phi : Z → X → ℝ → ℝ)
    (hp : IsPolicyMap phi) (upper : Bool) :
    ∀ᵐ x ∂xLaw M, 0 < pLow M.prop x →
      pLow M.prop x *
        (∫ t in Ioo (0 : ℝ) 1,
          (gapQuantiles M (policyWeight M (policyProp phi M.prop)) x 0).1 t *
          (gapQuantiles M (policyWeight M (policyProp phi M.prop)) x 0).2
            (if upper then t else 1 - t)) =
      -(∫ z, (∫ v in Ioc (min (pLow M.prop x) (policyProp phi M.prop z x))
        (pLow M.prop x), boundaryQuantile M zeroLaw x
          (if upper then 1 - v / pLow M.prop x else v / pLow M.prop x))
        ∂M.instKernel x) := by
  filter_upwards [connected_gap_quantile_eq_boundary M zeroLaw h hc hfin hconn
      (policyWeight M (policyProp phi M.prop)),
    connected_gap_law_eq_boundary M zeroLaw h hc hfin hconn,
    connected_range_decomposition_endpoints M h hc hfin hconn,
    connected_range_decomposition_count M h hc hfin hconn,
    gap_law_isProbability M h hc hfin, boundary_quantile_supported M zeroLaw h he]
      with x hQ hLaw hEnd hCount hProb hs
  intro hb
  have hgap : (CondRangeDecomposition M x).gapLo 0 < (CondRangeDecomposition M x).gapHi 0 := by
    simpa only [RangeData.gapLo, ↓reduceIte, RangeData.gapHi, hEnd.1] using hb
  have hk : 0 < (CondRangeDecomposition M x).count := by omega
  letI : IsProbabilityMeasure (boundaryLaw M zeroLaw x) := by
    rw [← hLaw hb]
    exact hProb 0 hk hgap
  have hW : weightLaw M (policyWeight M (policyProp phi M.prop)) x 0 =
      (uniformInterval 0 (pLow M.prop x)).map (policyWeight M (policyProp phi M.prop) x) := by
    simp only [weightLaw, gapUnif, RangeData.gapLo, ↓reduceIte, RangeData.gapHi, hEnd.1]
  have hInt := supported_quantile_resistance_integrable (boundaryLaw M zeroLaw x)
    M.yMin M.yMax (pLow M.prop x) hb
    (fun t ht => by
      rw [← boundaryQuantile_eq_quantile_of_mem_Ioo M zeroLaw x ht]
      exact ⟨he.1.2 (hs t ht), he.2.2 (hs t ht)⟩) upper
  have hIntBoundary : Integrable (fun v => boundaryQuantile M zeroLaw x
      (if upper then 1 - v / pLow M.prop x else v / pLow M.prop x))
      (volume.restrict (Ioc 0 (pLow M.prop x))) := by
    change Integrable _ _ at hInt
    rw [← restrict_Ioo_eq_restrict_Ioc] at hInt ⊢
    apply hInt.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    have hvr : v / pLow M.prop x ∈ Ioo (0 : ℝ) 1 :=
      ⟨div_pos hv.1 hb, (div_lt_one hb).mpr hv.2⟩
    apply (boundaryQuantile_eq_quantile_of_mem_Ioo M zeroLaw x _).symm
    cases upper
    · exact hvr
    · exact ⟨sub_pos.mpr hvr.2, sub_lt_self 1 hvr.1⟩
  have hEq := boundary_transport_truncated_integral M (policyProp phi M.prop)
    (policy_propensity_jointly_measurable M h.2.2.2.1 phi hp)
    (fun z x => (hp.2 z x (M.prop z x) (M.rangeProp z x)).1) x
    (pLow M.prop x) hb rfl (boundaryQuantile M zeroLaw x) upper hIntBoundary
  rw [← hEq]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  dsimp only
  rw [hQ hb t ht]
  simp only [gapQuantiles, hW]

-- @node: boundary_truncated_integrable
/-- In the latent instrumental-variable model, let a [policy propensity
function](hyp:q) be [jointly measurable](hyp:hq) and [nonnegative everywhere](hyp:hr).
For a [covariate value](hyp:x), a [boundary endpoint b](hyp:b), and a [real-valued
function](hyp:f) that [is integrable from zero (excluded) to b (included)](hyp:hi),
[the negative integral of that function from the smaller of b and policy propensity
to b is integrable under the conditional instrument distribution](goal). -/
lemma boundary_truncated_integrable (q : Z → X → ℝ)
    (hq : Measurable (Function.uncurry q)) (hr : ∀ z x, 0 ≤ q z x)
    (x : X) (b : ℝ) (f : ℝ → ℝ) (hi : IntegrableOn f (Ioc 0 b)) :
    Integrable (fun z => -(∫ v in Ioc (min b (q z x)) b, f v)) (M.instKernel x) := by
  letI := M.instKernel_markov
  let μ := volume.restrict (Ioc 0 b)
  have hqm : Measurable (fun uz : ℝ × Z => q uz.2 x) := by fun_prop
  have hm : Measurable (fun uz : ℝ × Z =>
      (if uz.1 ≤ q uz.2 x then 1 else 0 : ℝ) - 1) := by
    exact (Measurable.ite (measurableSet_le measurable_fst hqm)
      measurable_const measurable_const).sub_const 1
  have hb : ∀ᵐ uz ∂μ.prod (M.instKernel x),
      ‖(if uz.1 ≤ q uz.2 x then 1 else 0 : ℝ) - 1‖ ≤ (1 : ℝ) := by
    filter_upwards [] with uz
    split_ifs <;> norm_num
  have hp := (hi.comp_fst (M.instKernel x)).mul_bdd hm.aestronglyMeasurable hb
  apply hp.integral_prod_right.congr
  filter_upwards [] with z
  exact threshold_complement_integral f b (q z x) (hr z x)

-- @node: clipped_regression_difference_integrable
/-- In the latent instrumental-variable model, assume [treatment follows
threshold crossing with measurable unit-interval propensity equal to conditional mean
treatment](hyp:h). Take a [policy propensity function](hyp:q) that [is jointly
measurable](hyp:hq), a [covariate value](hyp:x), a [real-valued regression
function](hyp:f), and [interval endpoints a and b](hyp:a,b) with [a no greater than
b](hyp:hab). If [the regression function is absolutely continuous on that
interval](hyp:hf) and [every baseline propensity at those covariates lies in the
closed interval](hyp:hp), then [the regression at policy propensity clipped to the
interval minus the regression at baseline propensity is integrable under the
conditional instrument distribution](goal). -/
lemma clipped_regression_difference_integrable (h : ThresholdCrossing M)
    (q : Z → X → ℝ) (hq : Measurable (Function.uncurry q))
    (x : X) (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hp : ∀ z, M.prop z x ∈ Icc a b) :
    Integrable (fun z => f (min b (max a (q z x))) - f (M.prop z x))
      (M.instKernel x) := by
  letI := M.instKernel_markov
  let μ := volume.restrict (Ioc a b)
  have hi : Integrable (deriv f) μ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hf.intervalIntegrable_deriv
  have hqm : Measurable (fun uz : ℝ × Z => q uz.2 x) := by fun_prop
  have hpm : Measurable (fun uz : ℝ × Z => M.prop uz.2 x) := by
    exact h.2.1.comp (measurable_snd.prodMk measurable_const)
  have hm : Measurable (fun uz : ℝ × Z =>
      (if uz.1 ≤ q uz.2 x then 1 else 0 : ℝ) -
        (if uz.1 ≤ M.prop uz.2 x then 1 else 0 : ℝ)) := by
    exact (Measurable.ite (measurableSet_le measurable_fst hqm)
      measurable_const measurable_const).sub
      (Measurable.ite (measurableSet_le measurable_fst hpm)
        measurable_const measurable_const)
  have hb : ∀ᵐ uz ∂μ.prod (M.instKernel x),
      ‖(if uz.1 ≤ q uz.2 x then 1 else 0 : ℝ) -
        (if uz.1 ≤ M.prop uz.2 x then 1 else 0 : ℝ)‖ ≤ (1 : ℝ) := by
    filter_upwards [] with uz
    split_ifs <;> norm_num
  have hiProd := (hi.comp_fst (M.instKernel x)).mul_bdd hm.aestronglyMeasurable hb
  have hiThreshold (r : ℝ) : Integrable
      (fun u => deriv f u * (if u ≤ r then 1 else 0 : ℝ)) μ := by
    apply hi.mul_bdd (c := 1)
    · exact (Measurable.ite measurableSet_Iic measurable_const
        measurable_const).aestronglyMeasurable
    · filter_upwards [] with u
      split_ifs <;> norm_num
  apply hiProd.integral_prod_right.congr
  filter_upwards [] with z
  simp only [mul_sub]
  rw [integral_sub (hiThreshold (q z x)) (hiThreshold (M.prop z x)),
    clipped_derivative_threshold_integral f a b (q z x) hab hf,
    clipped_derivative_threshold_integral f a b (M.prop z x) hab hf,
    max_eq_right (hp z).1, min_eq_right (hp z).2]
  ring

-- @node: connected_conditional_formula
/-- For the latent instrumental-variable model, choose [a covariate-indexed
fallback probability distribution supported on the outcome domain](hyp:zeroLaw).
Assume [the structural conditions of potential-outcome support, consistency,
conditional instrument exogeneity, threshold crossing, uniform resistance, common
instrument support, and compact domains](hyp:h), [known outcome endpoints](hyp:he),
[propensity continuity on each instrument component](hyp:hc), [finitely many
instrument components](hyp:hfin), and [a connected instrument domain](hyp:hconn).
For a [policy transformation](hyp:phi) that [is jointly measurable on unit-interval
propensities and preserves that interval](hyp:hp), and an [upper-versus-lower
choice](hyp:upper), [the conditional bound integrand for the policy weight equals,
at almost every covariate value, the conditional instrument average of the connected
formula combining the lower-boundary quantile term, the clipped treated-regression
change, and the upper-tail outcome-endpoint term](goal). -/
lemma connected_conditional_formula
    (zeroLaw : X → {ν : ProbabilityMeasure ℝ // ν.toMeasure M.Ysetᶜ = 0})
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (hc : PropensityContinuousOnComponents M) (hfin : FiniteInstrumentComponents Z)
    (hconn : InstrumentConnectedReduction Z) (phi : Z → X → ℝ → ℝ)
    (hp : IsPolicyMap phi) (upper : Bool) :
    ∀ᵐ x ∂xLaw M,
      conditionalBoundIntegrand M upper (policyWeight M (policyProp phi M.prop)) x =
        ∫ z, connectedInt M zeroLaw upper (policyProp phi M.prop) (z, x) ∂M.instKernel x := by
  let q := policyProp phi M.prop
  have hqm : Measurable (Function.uncurry q) :=
    policy_propensity_jointly_measurable M h.2.2.2.1 phi hp
  have hqr : ∀ z x, q z x ∈ Icc (0 : ℝ) 1 :=
    fun z x => hp.2 z x (M.prop z x) (M.rangeProp z x)
  letI := M.instKernel_markov
  filter_upwards [connected_conditional_bound_three_terms M h he hc hfin hconn phi hp upper,
    connected_boundary_transport_integral M zeroLaw h he hc hfin hconn phi hp upper,
    connected_regression_ac M h he hc hfin hconn,
    connected_gap_law_eq_boundary M zeroLaw h hc hfin hconn,
    connected_range_decomposition_endpoints M h hc hfin hconn,
    connected_range_decomposition_count M h hc hfin hconn,
    gap_law_isProbability M h hc hfin, boundary_quantile_supported M zeroLaw h he]
      with x hthree hboundary hac hLaw hEnd hCount hProb hs
  have hliv : Integrable (fun z => g1 M (clampPolicy M.prop q z x) x -
      g1 M (M.prop z x) x) (M.instKernel x) :=
    clipped_regression_difference_integrable M h.2.2.2.1 q hqm x _ _ _
      (propensity_support_endpoints M.prop M.rangeProp x).2.2 hac
      (fun z => propensity_between_support_endpoints M z x)
  have htail : Integrable (fun z => (if upper then M.yMax else M.yMin) *
      max 0 (q z x - pHigh M.prop x)) (M.instKernel x) := by
    apply Integrable.const_mul
    apply Integrable.of_bound (C := 1)
    · apply Measurable.aestronglyMeasurable
      fun_prop
    · filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
      exact max_le zero_le_one (by
        have hh := (population_support_endpoints M x).2.1.1
        linarith [(hqr z x).2])
  have hlow := (population_support_endpoints M x).1.1
  rw [hthree]
  by_cases hb : 0 < pLow M.prop x
  · have hgap : (CondRangeDecomposition M x).gapLo 0 <
        (CondRangeDecomposition M x).gapHi 0 := by
      simpa only [RangeData.gapLo, ↓reduceIte, RangeData.gapHi, hEnd.1] using hb
    have hk : 0 < (CondRangeDecomposition M x).count := by omega
    letI : IsProbabilityMeasure (boundaryLaw M zeroLaw x) := by
      rw [← hLaw hb]
      exact hProb 0 hk hgap
    have hi := supported_quantile_resistance_integrable (boundaryLaw M zeroLaw x)
      M.yMin M.yMax (pLow M.prop x) hb
      (fun t ht => by
        rw [← boundaryQuantile_eq_quantile_of_mem_Ioo M zeroLaw x ht]
        exact ⟨he.1.2 (hs t ht), he.2.2 (hs t ht)⟩) upper
    have hiBoundary : IntegrableOn (fun v => boundaryQuantile M zeroLaw x
        (if upper then 1 - v / pLow M.prop x else v / pLow M.prop x))
        (Ioc 0 (pLow M.prop x)) := by
      rw [IntegrableOn, ← restrict_Ioo_eq_restrict_Ioc] at hi ⊢
      apply hi.congr
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
      have hvr : v / pLow M.prop x ∈ Ioo (0 : ℝ) 1 :=
        ⟨div_pos hv.1 hb, (div_lt_one hb).mpr hv.2⟩
      apply (boundaryQuantile_eq_quantile_of_mem_Ioo M zeroLaw x _).symm
      cases upper
      · exact hvr
      · exact ⟨sub_pos.mpr hvr.2, sub_lt_self 1 hvr.1⟩
    have hbInt := boundary_truncated_integrable M q hqm (fun z x => (hqr z x).1)
      x (pLow M.prop x) _ hiBoundary
    rw [max_eq_right hlow, hboundary hb]
    simp only [connectedInt, if_pos hb]
    have hsplit := integral_add (hbInt.add hliv) htail
    simp only [Pi.add_apply] at hsplit
    rw [integral_add hbInt hliv] at hsplit
    simp only [integral_neg, integral_const_mul] at hsplit
    calc
      _ = ∫ z, -(∫ v in Ioc (min (pLow M.prop x) (q z x)) (pLow M.prop x),
          boundaryQuantile M zeroLaw x (if upper then 1 - v / pLow M.prop x
            else v / pLow M.prop x)) +
          (g1 M (clampPolicy M.prop q z x) x - g1 M (M.prop z x) x) +
          (if upper then M.yMax else M.yMin) * max 0 (q z x - pHigh M.prop x)
          ∂M.instKernel x := hsplit.symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with z
        ring
  · have hz : pLow M.prop x = 0 := le_antisymm (le_of_not_gt hb) hlow
    rw [hz, max_self, zero_mul, zero_add]
    simp only [connectedInt, if_neg hb, zero_add]
    rw [integral_add hliv htail, integral_const_mul]

-- @node: policyWeight_jointly_measurable
/-- In the latent instrumental-variable model, assume [treatment follows
threshold crossing with measurable unit-interval propensity equal to conditional mean
treatment](hyp:h). For a [policy propensity function](hyp:q) that [is jointly
measurable](hyp:hq), [the policy weight is jointly measurable in covariates and
resistance](goal). -/
@[fun_prop] lemma policyWeight_jointly_measurable (h : ThresholdCrossing M)
    (q : Z → X → ℝ) (hq : Measurable (Function.uncurry q)) :
    Measurable (Function.uncurry (policyWeight M q)) := by
  let K : Kernel (X × ℝ) Z := M.instKernel.comap (fun xu : X × ℝ => xu.1) measurable_fst
  letI := M.instKernel_markov
  haveI : IsMarkovKernel K := inferInstanceAs (IsMarkovKernel (M.instKernel.comap _ _))
  have hq' : Measurable (fun a : (X × ℝ) × Z => q a.2 a.1.1) := by fun_prop
  have hp' : Measurable (fun a : (X × ℝ) × Z => M.prop a.2 a.1.1) := by
    exact h.2.1.comp (measurable_snd.prodMk measurable_fst.fst)
  have hm : Measurable (fun a : (X × ℝ) × Z =>
      (if a.1.2 ≤ q a.2 a.1.1 then 1 else 0 : ℝ) -
        (if a.1.2 ≤ M.prop a.2 a.1.1 then 1 else 0 : ℝ)) := by
    exact (Measurable.ite (measurableSet_le measurable_fst.snd hq')
      measurable_const measurable_const).sub
      (Measurable.ite (measurableSet_le measurable_fst.snd hp')
        measurable_const measurable_const)
  exact (hm.stronglyMeasurable.integral_kernel_prod_right' (κ := K)).measurable

-- @node: policyWeight_norm_le_one
/-- In the latent instrumental-variable model, for any [policy propensity
function](hyp:q), [covariate value](hyp:x), and [resistance value](hyp:u), [the
absolute value of the policy weight is at most one](goal). -/
lemma policyWeight_norm_le_one (q : Z → X → ℝ) (x : X) (u : ℝ) :
    ‖policyWeight M q x u‖ ≤ 1 := by
  letI := M.instKernel_markov
  have hb : ∀ᵐ z ∂M.instKernel x,
      ‖(if u ≤ q z x then 1 else 0 : ℝ) -
        (if u ≤ M.prop z x then 1 else 0 : ℝ)‖ ≤ (1 : ℝ) := by
    filter_upwards [] with z
    split_ifs <;> norm_num
  simpa [policyWeight, measureReal_def] using norm_integral_le_of_norm_le_const hb

-- @node: policyWeight_target_regular
/-- In the latent instrumental-variable model, assume [treatment follows
threshold crossing with measurable unit-interval propensity equal to conditional mean
treatment](hyp:h). For a [policy propensity function](hyp:q) that [is jointly
measurable](hyp:hq), [the policy weight is jointly measurable on covariates and
unit-interval resistance and is integrable under the product of the covariate law
and Lebesgue measure on the closed unit interval](goal). -/
lemma policyWeight_target_regular (h : ThresholdCrossing M)
    (q : Z → X → ℝ) (hq : Measurable (Function.uncurry q)) :
    TargetWeightMeasurable (policyWeight M q) ∧
      TargetWeightIntegrable M (policyWeight M q) := by
  have hm := policyWeight_jointly_measurable M h q hq
  haveI : IsProbabilityMeasure (xLaw M) := Measure.isProbabilityMeasure_map M.measX.aemeasurable
  constructor
  · exact hm.comp (measurable_fst.prodMk measurable_snd.subtype_val)
  · apply Integrable.of_bound hm.aestronglyMeasurable (1 : ℝ)
    filter_upwards [] with xu
    exact policyWeight_norm_le_one M q xu.1 xu.2

-- @node: instrument_kernel_outer_integral
/-- In the latent instrumental-variable model, for a [real-valued function
of the instrument and covariates](hyp:f) that [is integrable under their joint
law](hyp:hf), [averaging first over the conditional instrument distribution and then
over the covariate distribution equals integration under the joint instrument–covariate
law](goal). -/
lemma instrument_kernel_outer_integral (f : Z × X → ℝ)
    (hf : Integrable f (zxLaw M)) :
    (∫ x, (∫ z, f (z, x) ∂M.instKernel x) ∂xLaw M) = ∫ zx, f zx ∂zxLaw M := by
  letI := M.instKernel_markov
  haveI : IsProbabilityMeasure (xLaw M) := Measure.isProbabilityMeasure_map M.measX.aemeasurable
  have hmap : ((xLaw M) ⊗ₘ M.instKernel).map Prod.swap = zxLaw M := by
    have hv : M.instKernel =ᵐ[xLaw M] condDistrib M.Zv M.Xv M.law.toMeasure := M.instKernel_version
    rw [Measure.compProd_congr hv]
    change ((M.law.toMeasure.map M.Xv) ⊗ₘ condDistrib M.Zv M.Xv M.law.toMeasure).map Prod.swap = _
    rw [compProd_map_condDistrib M.measZ.aemeasurable,
      Measure.map_map measurable_swap (M.measX.prodMk M.measZ)]
    rfl
  have hf' : Integrable f (((xLaw M) ⊗ₘ M.instKernel).map Prod.swap) := by
    rwa [hmap]
  have hi := hf'.comp_aemeasurable measurable_swap.aemeasurable
  have he := Measure.integral_compProd hi
  simp only [Function.comp_def, Prod.swap_prod_mk] at he
  rw [← he, ← integral_map measurable_swap.aemeasurable hf'.aestronglyMeasurable, hmap]

end Papers.TbsPrteOptimalTransport
