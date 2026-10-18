module
public import Papers.TbsPrteOptimalTransport.Helpers.DiscretePolicyQuantile
public import Papers.TbsPrteOptimalTransport.Helpers.JQuantileBands
/-! Finite partition assembly of the observable policy-weight integrals. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

-- @node: finite_open_slice_integral_sum
/-- If [the partition points are nondecreasing through the final index](hyp:ha)
and [the function is integrable on every adjacent open slice](hyp:hf), then
[the sum of the slice integrals equals the integral over the open interval from
the first partition point to the last](goal). -/
lemma finite_open_slice_integral_sum (a : ℕ → ℝ) (n : ℕ) (f : ℝ → ℝ)
    (ha : ∀ i j, i ≤ j → j ≤ n → a i ≤ a j)
    (hf : ∀ i < n, IntegrableOn f (Ioo (a i) (a (i+1)))) :
    (∑ i ∈ Finset.range n, ∫ t in Ioo (a i) (a (i+1)), f t) =
      ∫ t in Ioo (a 0) (a n), f t := by
  have hi (i : ℕ) (h : i < n) : IntervalIntegrable f volume (a i) (a (i+1)) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le
      (ha i (i+1) (by omega) (by omega))).mpr (hf i h)
  have hs := intervalIntegral.sum_integral_adjacent_intervals hi
  rw [intervalIntegral.integral_of_le (ha 0 n (by omega) le_rfl),
    integral_Ioc_eq_integral_Ioo] at hs
  rw [← hs]
  apply Finset.sum_congr rfl
  intro i hi
  rw [intervalIntegral.integral_of_le
    (ha i (i+1) (by omega) (by have := Finset.mem_range.mp hi; omega)),
    integral_Ioc_eq_integral_Ioo]

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: normalized_policy_partition_endpoints
/-- If [the baseline and policy levels obey the common ordering and class
structure](hyp:hL) and [the bin precedes the final baseline level](hyp:hk), then
[the first normalized policy partition point is zero and the last is one](goal). -/
lemma normalized_policy_partition_endpoints (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (x : X) (k : ℕ) (hk : k < L.K) :
    kappa L k 0 x = 0 ∧ kappa L k (L.l k+1) x = 1 := by
  have hw : L.pLev (k+1) x - L.pLev k x ≠ 0 := ne_of_gt
    (sub_pos.mpr (hL.2.2.2.2.2.2.2.1 x k (k+1) (by omega) (by omega)))
  constructor
  · rw [kappa, hL.2.1 x k 0 hk.le (by omega), if_pos rfl, sub_self, zero_div]
  · rw [kappa, hL.2.1 x k (L.l k+1) hk.le le_rfl,
      if_neg (by omega), if_neg (by omega), div_self hw]

-- @node: normalized_policy_partition_monotone
/-- If [the baseline and policy levels obey the common ordering and class
structure](hyp:hL), [the bin precedes the final baseline level](hyp:hk),
[the first partition index is no larger than the second](hyp:hij), and
[the second index is at most the terminal partition index](hyp:hj), then
[the corresponding normalized partition points are ordered the same way](goal). -/
lemma normalized_policy_partition_monotone (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (x : X) (k : ℕ) (hk : k < L.K)
    (i j : ℕ) (hij : i ≤ j) (hj : j ≤ L.l k+1) :
    kappa L k i x ≤ kappa L k j x := by
  have hw := sub_pos.mpr (hL.2.2.2.2.2.2.2.1 x k (k+1) (by omega) (by omega))
  apply div_le_div_of_nonneg_right _ hw.le
  apply sub_le_sub_right
  by_cases hi0 : i = 0
  · rw [hi0, hL.2.1 x k 0 hk.le (by omega), if_pos rfl]
    exact (policy_level_bin_bounds M q L hL x k j hk.le hj).1
  by_cases hjl : j ≤ L.l k
  · rcases hij.eq_or_lt with rfl | hij
    · exact le_rfl
    · exact (hL.2.2.2.2.2.2.2.2.1 x k i j hk.le (by omega) hij hjl).le
  · have he : j = L.l k+1 := by omega
    rw [he, hL.2.1 x k (L.l k+1) hk.le le_rfl,
      if_neg (by omega), if_neg (by omega)]
    exact (policy_level_bin_bounds M q L hL x k i hk.le (by omega)).2

-- @node: final_policy_slice_gamma_zero
/-- [The additional current-bin coefficient on the final policy slice is zero](goal). -/
lemma final_policy_slice_gamma_zero (L : LevelData Z X) (x : X) (k : ℕ) :
    gamma M L k (L.l k+1) x = 0 := by
  have he : policyUnion L k (L.l k+1) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨i, hi, hzi⟩ := Finset.mem_biUnion.mp hz
    have hi' := Finset.mem_range.mp hi
    simp only [if_neg (show ¬ L.l k+1 ≤ i by omega), Finset.notMem_empty] at hzi
  simp only [gamma, he, Finset.sum_empty]

-- @node: normalized_policy_integral_assembly
/-- If [the baseline and policy levels obey the common ordering and class
structure](hyp:hL), [the bin precedes the final baseline level](hyp:hk), and
[the function is integrable over the open unit interval](hyp:hQ), then
[its integral against the policy weight in normalized gap coordinates equals
the full-gap coefficient times its unit-interval integral plus the sum of the
current-bin coefficients times its integrals over the corresponding normalized slices](goal). -/
lemma normalized_policy_integral_assembly (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (x : X) (k : ℕ) (hk : k < L.K)
    (Q : ℝ → ℝ) (hQ : IntegrableOn Q (Ioo (0 : ℝ) 1)) :
    (∫ t in Ioo (0 : ℝ) 1, Q t * policyWeight M q x
      (L.pLev k x + (L.pLev (k+1) x - L.pLev k x) * t)) =
      gammaFull M L k x * (∫ t in Ioo (0 : ℝ) 1, Q t) +
      ∑ j ∈ Finset.Icc 1 (L.l k), gamma M L k j x *
        ∫ t in Ioo (kappa L k (j-1) x) (kappa L k j x), Q t := by
  let a := fun j => kappa L k j x
  let w := fun t => policyWeight M q x
    (L.pLev k x + (L.pLev (k+1) x - L.pLev k x) * t)
  have ha := normalized_policy_partition_monotone M q L hL x k hk
  have he := normalized_policy_partition_endpoints M q L hL x k hk
  have hQi (i : ℕ) (hi : i < L.l k+1) : IntegrableOn Q (Ioo (a i) (a (i+1))) := by
    apply hQ.mono_set
    intro t ht
    have hl := ha 0 i (by omega) (by omega)
    have hu := ha (i+1) (L.l k+1) (by omega) le_rfl
    rw [he.1] at hl
    rw [he.2] at hu
    exact ⟨hl.trans_lt ht.1, ht.2.trans_le hu⟩
  have hWi (i : ℕ) (hi : i < L.l k+1) :
      IntegrableOn (fun t => Q t * w t) (Ioo (a i) (a (i+1))) := by
    apply ((hQi i hi).mul_const (gammaFull M L k x + gamma M L k (i+1) x)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    dsimp only [w]
    rw [normalized_policy_weight_slice_value M q L hL x k (i+1) hk
      (by omega) (by omega) t (by simpa only [Nat.add_sub_cancel] using ht)]
  have hsum := finite_open_slice_integral_sum a (L.l k+1) (fun t => Q t * w t) ha hWi
  have hsumQ := finite_open_slice_integral_sum a (L.l k+1) Q ha hQi
  dsimp only [a] at hsum hsumQ
  rw [he.1, he.2] at hsum hsumQ
  rw [← hsum]
  have hterms : (∑ i ∈ Finset.range (L.l k+1),
      ∫ t in Ioo (kappa L k i x) (kappa L k (i+1) x), Q t * w t) =
      ∑ i ∈ Finset.range (L.l k+1), (gammaFull M L k x + gamma M L k (i+1) x) *
        ∫ t in Ioo (kappa L k i x) (kappa L k (i+1) x), Q t := by
    apply Finset.sum_congr rfl
    intro i hi
    exact normalized_policy_slice_integral M q L hL x k (i+1) hk
      (by omega) (by have := Finset.mem_range.mp hi; omega) Q
  rw [hterms]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsumQ, Finset.sum_range_succ,
    final_policy_slice_gamma_zero M L x k, zero_mul, add_zero]
  congr 1
  rw [show Finset.Icc 1 (L.l k) = Finset.Ico 1 (L.l k+1) by
    ext j; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega,
    Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.add_sub_cancel_left, Nat.add_comm 1]

-- @node: conditional_interval_law_eq_discrete_gap
/-- If [the baseline and policy levels obey the common ordering and class
structure](hyp:hL) and [the bin precedes the final baseline level](hyp:hk), then
[the conditional outcome law on the baseline interval equals the discrete gap law](goal). -/
lemma conditional_interval_law_eq_discrete_gap (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (x : X) (k : ℕ) (hk : k < L.K) :
    conditionalIntervalLaw M x k = discreteGapLaw M L k x := by
  simp only [conditionalIntervalLaw, discreteGapLaw,
    ← hL.1 x k (by omega), ← hL.1 x (k+1) (by omega)]

-- @node: finite_policy_full_quantile_integral
/-- If [the baseline and policy levels obey the common ordering and class
structure](hyp:hL) and [the bin precedes the final baseline level](hyp:hk), then
[the gap width times the integral of its conditional outcome quantile over the
open unit interval equals the observable full-gap outcome integral, for either
the direct or reflected quantile orientation](goal). -/
lemma finite_policy_full_quantile_integral (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (x : X) (k : ℕ) (hk : k < L.K)
    (upper : Bool) :
    (L.pLev (k+1) x - L.pLev k x) *
      (∫ t in Ioo (0 : ℝ) 1,
        (conditionalIntervalQuantiles M (policyWeight M q) x k).1
          (if upper then 1-t else t)) = Jfull M L k x := by
  letI := discrete_gap_law_probability M M.prop q L hL k hk x
  simp only [conditionalIntervalQuantiles,
    conditional_interval_law_eq_discrete_gap M q L hL x k hk, Jfull]
  congr 1
  have href : (∫ t in Ioo (0 : ℝ) 1,
      Causalean.Stat.quantile (discreteGapLaw M L k x) (if upper then 1-t else t)) =
      ∫ t in Ioo (0 : ℝ) 1, Causalean.Stat.quantile (discreteGapLaw M L k x) t := by
    cases upper
    · rfl
    · exact unit_integral_reflection _
  rw [href]
  have hmap := integral_map (Causalean.Stat.aemeasurable_quantile_unifOI
    (discreteGapLaw M L k x)) (show AEStronglyMeasurable (fun y : ℝ => y)
      (Causalean.Stat.unifOI.map (Causalean.Stat.quantile (discreteGapLaw M L k x))) by
        fun_prop)
  rw [Causalean.Stat.quantile_map_uniform] at hmap
  exact hmap.symm

-- @node: finite_policy_band_quantile_integral
/-- If [the baseline and policy levels obey the common ordering and class
structure](hyp:hL), [the bin precedes the final baseline level](hyp:hk),
[the policy-class index is at least one](hyp:hj0), and [it is no larger than the
number of policy classes in the bin](hyp:hj), then [the gap width times the
conditional outcome-quantile integral over that normalized slice equals the
corresponding observable band integral, with the selected direct or reflected orientation](goal). -/
lemma finite_policy_band_quantile_integral (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (x : X) (k j : ℕ)
    (hk : k < L.K) (hj0 : 1 ≤ j) (hj : j ≤ L.l k) (upper : Bool) :
    (L.pLev (k+1) x - L.pLev k x) *
      (∫ t in Ioo (kappa L k (j-1) x) (kappa L k j x),
        (conditionalIntervalQuantiles M (policyWeight M q) x k).1
          (if upper then 1-t else t)) = Jband M upper L k (j-1) x := by
  have he := normalized_policy_partition_endpoints M q L hL x k hk
  have ha := normalized_policy_partition_monotone M q L hL x k hk
  simp only [Jband, show j-1+1 = j by omega, integral_Ioc_eq_integral_Ioo,
    conditionalIntervalQuantiles, conditional_interval_law_eq_discrete_gap M q L hL x k hk]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have hlo := ha 0 (j-1) (by omega) (by omega)
  have hhi := ha j (L.l k+1) (by omega) le_rfl
  rw [he.1] at hlo
  rw [he.2] at hhi
  have ht' : t ∈ Ioo (0 : ℝ) 1 := ⟨hlo.trans_lt ht.1, ht.2.trans_le hhi⟩
  have hs : (if upper then 1-t else t) ∈ Ioo (0 : ℝ) 1 := by
    cases upper <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact ht'
    · constructor <;> linarith [ht'.1, ht'.2]
  simp only [levelGapQuantile, if_neg (ne_of_gt hs.1), if_neg (ne_of_lt hs.2)]

-- @node: finite_policy_outcome_quantile_integrable
/-- Under [the model's structural assumptions](hyp:h), [known lower and upper
outcome endpoints](hyp:he), and [a common ordering and class structure for the
baseline and policy levels](hyp:hL), [for almost every covariate value, the
conditional outcome quantile on every bin before the final baseline level is
integrable on the open unit interval in both direct and reflected orientations](goal). -/
lemma finite_policy_outcome_quantile_integrable (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) :
    ∀ᵐ x ∂xLaw M, ∀ k < L.K, ∀ upper : Bool,
      IntegrableOn (fun t =>
        (conditionalIntervalQuantiles M (policyWeight M q) x k).1
          (if upper then 1-t else t)) (Ioo (0 : ℝ) 1) := by
  filter_upwards [discrete_gap_law_supported M h M.prop q L hL] with x hx
  intro k hk upper
  letI := discrete_gap_law_probability M M.prop q L hL k hk x
  have hs : ∀ t ∈ Ioo (0 : ℝ) 1,
      Causalean.Stat.quantile (discreteGapLaw M L k x) t ∈ Icc M.yMin M.yMax := by
    intro t ht
    have hm := quantile_mem_closed_of_supported (discreteGapLaw M L k x)
      M.Yset h.2.2.2.2.2.2.1.isClosed (hx k hk) t ht
    exact ⟨he.1.2 hm, he.2.2 hm⟩
  have hi := supported_quantile_resistance_integrable (discreteGapLaw M L k x)
    M.yMin M.yMax 1 (by norm_num) hs upper
  simpa only [div_one, conditionalIntervalQuantiles,
    conditional_interval_law_eq_discrete_gap M q L hL x k hk,
    restrict_Ioo_eq_restrict_Ioc, IntegrableOn] using hi

-- @node: finite_policy_observable_integral
/-- Under [the model's structural assumptions](hyp:h), [known lower and upper
outcome endpoints](hyp:he), and [a common ordering and class structure for the
baseline and policy levels](hyp:hL), [for almost every covariate value and every
bin before the final baseline level, the gap width times the oriented outcome-quantile
integral against the normalized policy weight equals the full-gap coefficient
times the observable full-gap integral plus the sum of current-bin coefficients
times their observable band integrals](goal). -/
lemma finite_policy_observable_integral (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (upper : Bool) :
    ∀ᵐ x ∂xLaw M, ∀ k < L.K,
      (L.pLev (k+1) x - L.pLev k x) *
        (∫ t in Ioo (0 : ℝ) 1,
          (conditionalIntervalQuantiles M (policyWeight M q) x k).1
            (if upper then 1-t else t) * policyWeight M q x
              (L.pLev k x + (L.pLev (k+1) x - L.pLev k x) * t)) =
      gammaFull M L k x * Jfull M L k x +
        ∑ j ∈ Finset.Icc 1 (L.l k), gamma M L k j x * Jband M upper L k (j-1) x := by
  filter_upwards [finite_policy_outcome_quantile_integrable M h he q L hL] with x hx
  intro k hk
  rw [normalized_policy_integral_assembly M q L hL x k hk _ (hx k hk upper),
    mul_add, Finset.mul_sum]
  congr 1
  · rw [mul_left_comm, finite_policy_full_quantile_integral M q L hL x k hk upper]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [mul_left_comm, finite_policy_band_quantile_integral M q L hL x k j hk
      (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 upper]

end Papers.TbsPrteOptimalTransport
