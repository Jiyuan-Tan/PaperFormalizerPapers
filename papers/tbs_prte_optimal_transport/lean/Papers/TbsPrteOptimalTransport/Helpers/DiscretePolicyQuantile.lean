module
public import Papers.TbsPrteOptimalTransport.Helpers.DiscretePolicyInterior
/-! Quantile versions of the antitone policy weight on finite baseline gaps. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

-- @node: uniformInterval_affine_map
/-- If [the lower endpoint is strictly below the upper endpoint](hyp:hab), then
[rescaling a uniform draw on the open unit interval by the interval width and
adding the lower endpoint gives the uniform probability law on that interval](goal). -/
lemma uniformInterval_affine_map (a b : ℝ) (hab : a < b) :
    Causalean.Stat.unifOI.map (fun t => a + (b-a) * t) = uniformInterval a b := by
  have he : (fun t : ℝ => a + t) ⁻¹' Ioo a b = Ioo 0 (b-a) := by
    ext t
    simp only [mem_preimage, mem_Ioo]
    constructor <;> intro ht <;> constructor <;> linarith [ht.1, ht.2]
  change Causalean.Stat.unifOI.map ((fun t : ℝ => a + t) ∘ (fun t => (b-a)*t)) = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop),
    uniformInterval_zero_map (b-a) (sub_pos.mpr hab)]
  rw [uniformInterval, Measure.map_smul, sub_zero, ← he,
    ← Measure.restrict_map (by fun_prop) measurableSet_Ioo,
    Measure.IsAddLeftInvariant.map_add_left_eq_self]
  rfl

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: normalized_policy_weight_antitone
/-- If [the baseline and policy levels obey the common ordering and class
structure](hyp:hL) and [the bin precedes the final baseline level](hyp:hk), then
[the policy weight evaluated at the affine rescaling of the unit interval to
the baseline gap is nonincreasing on the open unit interval](goal). -/
lemma normalized_policy_weight_antitone (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (x : X) (k : ℕ) (hk : k < L.K) :
    AntitoneOn (fun t => policyWeight M q x
      (L.pLev k x + (L.pLev (k+1) x - L.pLev k x) * t)) (Ioo (0 : ℝ) 1) := by
  have hw : 0 < L.pLev (k+1) x - L.pLev k x :=
    sub_pos.mpr (hL.2.2.2.2.2.2.2.1 x k (k+1) (by omega) (by omega))
  have hmem (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      L.pLev k x + (L.pLev (k+1) x - L.pLev k x) * t ∈
        Ioo (L.pLev k x) (L.pLev (k+1) x) := by
    constructor <;> nlinarith [ht.1, ht.2]
  intro s hs t ht hst
  exact finite_policy_weight_antitone_on_gap M q L hL x k hk
    (hmem s hs) (hmem t ht) (by nlinarith)

-- @node: finite_policy_weight_quantile_reflection
/-- If [the baseline and policy levels obey the common ordering and class
structure](hyp:hL) and [the bin precedes the final baseline level](hyp:hk), then
[evaluating the policy weight at the reflected normalized resistance rank agrees
almost everywhere under the uniform unit-interval law with the conditional
policy-weight quantile for that bin](goal). -/
lemma finite_policy_weight_quantile_reflection (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (x : X) (k : ℕ) (hk : k < L.K) :
    (fun t => policyWeight M q x
      (L.pLev k x + (L.pLev (k+1) x - L.pLev k x) * (1-t)))
      =ᵐ[Causalean.Stat.unifOI] (conditionalIntervalQuantiles M (policyWeight M q) x k).2 := by
  let f := fun t => policyWeight M q x
    (L.pLev k x + (L.pLev (k+1) x - L.pLev k x) * t)
  have hab : L.pLev k x < L.pLev (k+1) x :=
    hL.2.2.2.2.2.2.2.1 x k (k+1) (by omega) (by omega)
  have hm : AEMeasurable (policyWeight M q x)
      (uniformInterval (L.pLev k x) (L.pLev (k+1) x)) := by
    apply AEMeasurable.smul_measure
    exact aemeasurable_restrict_of_antitoneOn measurableSet_Ioo
      (finite_policy_weight_antitone_on_gap M q L hL x k hk)
  have hlaw : Causalean.Stat.unifOI.map f = weightLawInt M (policyWeight M q) x k := by
    change Causalean.Stat.unifOI.map (policyWeight M q x ∘
      (fun t => L.pLev k x + (L.pLev (k+1) x - L.pLev k x) * t)) = _
    have hm' : AEMeasurable (policyWeight M q x) (Causalean.Stat.unifOI.map
        (fun t => L.pLev k x + (L.pLev (k+1) x - L.pLev k x) * t)) := by
      rw [uniformInterval_affine_map _ _ hab]
      exact hm
    rw [← AEMeasurable.map_map_of_aemeasurable hm' (by fun_prop),
      uniformInterval_affine_map _ _ hab]
    simp only [weightLawInt, ← hL.1 x k (by omega), ← hL.1 x (k+1) (by omega)]
  have hr := antitone_uniform_quantile_reflection f
    (normalized_policy_weight_antitone M q L hL x k hk)
  rw [hlaw] at hr
  exact hr

-- @node: finite_policy_quantile_product_integral
/-- If [the baseline and policy levels obey the common ordering and class
structure](hyp:hL) and [the bin precedes the final baseline level](hyp:hk), then
[the unit-interval integral of any function times the oriented policy-weight
quantile equals its integral against the policy weight in normalized gap
coordinates, with the function reflected for the upper orientation and unchanged
for the lower orientation](goal). -/
lemma finite_policy_quantile_product_integral (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (x : X) (k : ℕ) (hk : k < L.K)
    (Q : ℝ → ℝ) (upper : Bool) :
    (∫ t in Ioo (0 : ℝ) 1,
      Q t * (conditionalIntervalQuantiles M (policyWeight M q) x k).2
        (if upper then t else 1-t)) =
    ∫ t in Ioo (0 : ℝ) 1, Q (if upper then 1-t else t) *
      policyWeight M q x (L.pLev k x + (L.pLev (k+1) x - L.pLev k x) * t) := by
  have he := finite_policy_weight_quantile_reflection M q L hL x k hk
  cases upper with
  | true =>
    simp only [↓reduceIte]
    calc
      _ = ∫ t in Ioo (0 : ℝ) 1, Q t * policyWeight M q x
          (L.pLev k x + (L.pLev (k+1) x - L.pLev k x) * (1-t)) :=
        integral_congr_ae (he.mono fun t ht => congrArg (Q t * ·) ht.symm)
      _ = _ := by
        have hh := unit_integral_reflection (fun t => Q (1-t) * policyWeight M q x
          (L.pLev k x + (L.pLev (k+1) x - L.pLev k x) * t))
        simpa only [sub_sub_cancel] using hh
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hh : ∀ᵐ t ∂Causalean.Stat.unifOI.map (fun t : ℝ => 1-t),
        policyWeight M q x (L.pLev k x + (L.pLev (k+1) x - L.pLev k x) * (1-t)) =
          (conditionalIntervalQuantiles M (policyWeight M q) x k).2 t := by
      rw [Causalean.Stat.map_one_sub_unifOI]
      exact he
    have hp := ae_of_ae_map (f := fun t : ℝ => 1-t) (by fun_prop) hh
    apply integral_congr_ae
    filter_upwards [hp] with t ht
    simpa only [sub_sub_cancel] using congrArg (Q t * ·) ht.symm

end Papers.TbsPrteOptimalTransport
