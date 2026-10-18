module
public import Papers.TbsPrteOptimalTransport.Helpers.LevelGraphRecovery
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationContinuousBoundaries
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationBinaryAdmissibility
/-! Marginal separation for exact level recovery. Averaging preserves the
uniform gaps between ordered population levels and their equality classes. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open scoped Classical

-- @node: ordered_marginal_gap
/-- Under a probability distribution, if [the first function is integrable](hyp:hf),
[the second is integrable](hyp:hg), and [the second exceeds the first by at least
a fixed gap almost everywhere](hyp:hgap), then [its mean exceeds the first
function's mean by at least that gap](goal). -/
lemma ordered_marginal_gap {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f g : X → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) (gap : ℝ)
    (hgap : ∀ᵐ x ∂μ, gap ≤ g x - f x) :
    gap ≤ (∫ x, g x ∂μ) - ∫ x, f x ∂μ := by
  have h := integral_mono_ae (integrable_const gap) (hg.sub hf) hgap
  change (∫ x, gap ∂μ) ≤ ∫ x, g x - f x ∂μ at h
  simpa only [integral_const, probReal_univ, one_smul, integral_sub hg hf] using h

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: population_baseline_marginal_gap
/-- Under [the threshold-crossing model](hyp:h), [invariant baseline and policy
level ordering](hyp:hL), and [uniform positive separation of distinct
propensities](hyp:hgap), if [the first baseline index is positive](hyp:hi),
[the second index is larger](hyp:hij), and [the second does not exceed the
number of baseline levels](hyp:hj), then [the second baseline-level mean
exceeds the first by at least the separation gap](goal). -/
lemma population_baseline_marginal_gap (h : ThresholdCrossing M)
    (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (gap : ℝ)
    (hgap : PropensityGapSeparationWitness M.prop q gap)
    (i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ L.K) :
    gap ≤ (∫ x, L.pLev j x ∂xLaw M) - ∫ x, L.pLev i x ∂xLaw M := by
  haveI : IsProbabilityMeasure (xLaw M) := Measure.isProbabilityMeasure_map M.measX.aemeasurable
  obtain ⟨z, hz⟩ := ordered_baseline_level_nonempty M q L hL i ⟨hi, by omega⟩
  obtain ⟨w, hw⟩ := ordered_baseline_level_nonempty M q L hL j ⟨by omega, hj⟩
  have hr := hL.2.2.2.2.2.2.2.2.2.2.1
  have hstrict := hL.2.2.2.2.2.2.2.1
  have hmi := ordered_baseline_level_measurable M h q L hL i ⟨hi, by omega⟩
  have hmj := ordered_baseline_level_measurable M h q L hL j ⟨by omega, hj⟩
  have hbi : ∀ x, ‖L.pLev i x‖ ≤ 1 := by
    intro x
    exact (abs_le.mpr ⟨by linarith [(hr x i (by omega)).1], (hr x i (by omega)).2⟩)
  have hbj : ∀ x, ‖L.pLev j x‖ ≤ 1 := by
    intro x
    exact (abs_le.mpr ⟨by linarith [(hr x j (by omega)).1], (hr x j (by omega)).2⟩)
  apply ordered_marginal_gap (xLaw M) _ _
    ((MemLp.of_bound hmi.aestronglyMeasurable 1 (Eventually.of_forall hbi) :
      MemLp (L.pLev i) 2 (xLaw M)).integrable (by norm_num))
    ((MemLp.of_bound hmj.aestronglyMeasurable 1 (Eventually.of_forall hbj) :
      MemLp (L.pLev j) 2 (xLaw M)).integrable (by norm_num)) gap
  apply Eventually.of_forall
  intro x
  have hz' := (hL.2.2.2.2.2.1 x i z (by omega)).mp hz
  have hw' := (hL.2.2.2.2.2.1 x j w hj).mp hw
  have hs := hstrict x i j hij hj
  have hg := hgap.2 x (M.prop z x) (Or.inl ⟨z, rfl⟩)
    (M.prop w x) (Or.inl ⟨w, rfl⟩)
  rw [hz', hw'] at hg
  rcases hg with he | hg
  · exact False.elim (hs.ne he.symm)
  · rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hs)] at hg
    exact hg.le

-- @node: population_baseline_marginal_equal_iff
/-- Given [the threshold-crossing model](hyp:h), [invariant baseline and policy
level ordering](hyp:hL), and [uniform positive separation of distinct
propensities](hyp:hgap), for [a positive valid first baseline index](hyp:hi)
and [a positive valid second baseline index](hyp:hj), [the baseline-level means
are equal exactly when their indices are equal](goal). -/
lemma population_baseline_marginal_equal_iff (h : ThresholdCrossing M)
    (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (gap : ℝ)
    (hgap : PropensityGapSeparationWitness M.prop q gap)
    (i j : ℕ) (hi : 1 ≤ i ∧ i ≤ L.K) (hj : 1 ≤ j ∧ j ≤ L.K) :
    (∫ x, L.pLev i x ∂xLaw M) = (∫ x, L.pLev j x ∂xLaw M) ↔ i = j := by
  constructor
  · intro he
    rcases lt_trichotomy i j with hij | hij | hij
    · have hg := population_baseline_marginal_gap M h q L hL gap hgap i j hi.1 hij hj.2
      rw [← he, sub_self] at hg
      exact False.elim (not_le_of_gt hgap.1 hg)
    · exact hij
    · have hg := population_baseline_marginal_gap M h q L hL gap hgap j i hj.1 hij hi.2
      rw [he, sub_self] at hg
      exact False.elim (not_le_of_gt hgap.1 hg)
  · rintro rfl
    rfl

-- @node: population_baseline_class_marginal_equal_iff
/-- Under [the threshold-crossing model](hyp:h), [invariant baseline and policy
level ordering](hyp:hL), and [uniform positive separation of distinct
propensities](hyp:hgap), take [a positive valid first baseline index](hyp:hi),
[a positive valid second index](hyp:hj), [an instrument in the first baseline
class](hyp:hz), and [an instrument in the second](hyp:hw). Then [the two
baseline-propensity means coincide exactly when the class indices coincide](goal). -/
lemma population_baseline_class_marginal_equal_iff (h : ThresholdCrossing M)
    (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (gap : ℝ)
    (hgap : PropensityGapSeparationWitness M.prop q gap)
    (i j : ℕ) (hi : 1 ≤ i ∧ i ≤ L.K) (hj : 1 ≤ j ∧ j ≤ L.K)
    (z w : Z) (hz : z ∈ L.S i) (hw : w ∈ L.S j) :
    (∫ x, M.prop z x ∂xLaw M) = (∫ x, M.prop w x ∂xLaw M) ↔ i = j := by
  have hz' : M.prop z = L.pLev i := by
    funext x
    exact (hL.2.2.2.2.2.1 x i z hi.2).mp hz
  have hw' : M.prop w = L.pLev j := by
    funext x
    exact (hL.2.2.2.2.2.1 x j w hj.2).mp hw
  rw [hz', hw']
  exact population_baseline_marginal_equal_iff M h q L hL gap hgap i j hi hj

-- @node: population_policy_marginal_gap
/-- If [policy propensities are jointly measurable](hyp:hq), [level ordering is
invariant](hyp:hL), [baseline levels are measurable](hyp:hlev), and [distinct
propensities are uniformly positively separated](hyp:hgap), take [a valid
baseline bin](hyp:hk), [a positive first policy index](hyp:hi), [a larger second
policy index](hyp:hij), and [a second index within the bin's policy-level
count](hyp:hj). Then [the second policy-level mean exceeds the first by at
least the separation gap](goal). -/
lemma population_policy_marginal_gap
    (q : Z → X → ℝ) (hq : Measurable (Function.uncurry q))
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (hlev : ∀ k, Measurable (L.pLev k)) (gap : ℝ)
    (hgap : PropensityGapSeparationWitness M.prop q gap)
    (k i j : ℕ) (hk : k ≤ L.K) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ L.l k) :
    gap ≤ (∫ x, L.qLev k j x ∂xLaw M) - ∫ x, L.qLev k i x ∂xLaw M := by
  haveI : IsProbabilityMeasure (xLaw M) := Measure.isProbabilityMeasure_map M.measX.aemeasurable
  obtain ⟨z, hz⟩ := ordered_policy_level_nonempty M q L hL k i hk hi (by omega)
  obtain ⟨w, hw⟩ := ordered_policy_level_nonempty M q L hL k j hk (by omega) hj
  have hr := hL.2.2.2.2.2.2.2.2.2.2.2
  have hstrict := hL.2.2.2.2.2.2.2.2.1
  have hmi := ordered_policy_level_measurable M q hq L hL hlev k i hk (by omega)
  have hmj := ordered_policy_level_measurable M q hq L hL hlev k j hk hj
  have hbi : ∀ x, ‖L.qLev k i x‖ ≤ 1 := by
    intro x
    exact abs_le.mpr ⟨by linarith [(hr x k i hk (by omega)).1],
      (hr x k i hk (by omega)).2⟩
  have hbj : ∀ x, ‖L.qLev k j x‖ ≤ 1 := by
    intro x
    exact abs_le.mpr ⟨by linarith [(hr x k j hk (by omega)).1],
      (hr x k j hk (by omega)).2⟩
  apply ordered_marginal_gap (xLaw M) _ _
    ((MemLp.of_bound hmi.aestronglyMeasurable 1 (Eventually.of_forall hbi) :
      MemLp (L.qLev k i) 2 (xLaw M)).integrable (by norm_num))
    ((MemLp.of_bound hmj.aestronglyMeasurable 1 (Eventually.of_forall hbj) :
      MemLp (L.qLev k j) 2 (xLaw M)).integrable (by norm_num)) gap
  apply Eventually.of_forall
  intro x
  have hz' := (hL.2.2.2.2.2.2.1 x k i z hk hi (by omega)).mp hz
  have hw' := (hL.2.2.2.2.2.2.1 x k j w hk (by omega) hj).mp hw
  have hs := hstrict x k i j hk hi hij hj
  have hg := hgap.2 x (q z x) (Or.inr ⟨z, rfl⟩) (q w x) (Or.inr ⟨w, rfl⟩)
  rw [hz', hw'] at hg
  rcases hg with he | hg
  · exact False.elim (hs.ne he.symm)
  · rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hs)] at hg
    exact hg.le

-- @node: population_policy_marginal_equal_iff
/-- With [jointly measurable policy propensities](hyp:hq), [invariant level
ordering](hyp:hL), [measurable baseline levels](hyp:hlev), and [uniform positive
separation of distinct propensities](hyp:hgap), for [a valid bin](hyp:hk),
[a valid first policy index](hyp:hi), and [a valid second policy index](hyp:hj),
[the two policy-level means are equal exactly when their within-bin indices
are equal](goal). -/
lemma population_policy_marginal_equal_iff
    (q : Z → X → ℝ) (hq : Measurable (Function.uncurry q))
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (hlev : ∀ k, Measurable (L.pLev k)) (gap : ℝ)
    (hgap : PropensityGapSeparationWitness M.prop q gap)
    (k i j : ℕ) (hk : k ≤ L.K)
    (hi : 1 ≤ i ∧ i ≤ L.l k) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    (∫ x, L.qLev k i x ∂xLaw M) = (∫ x, L.qLev k j x ∂xLaw M) ↔ i = j := by
  constructor
  · intro he
    rcases lt_trichotomy i j with hij | hij | hij
    · have hg := population_policy_marginal_gap M q hq L hL hlev gap hgap
        k i j hk hi.1 hij hj.2
      rw [← he, sub_self] at hg
      exact False.elim (not_le_of_gt hgap.1 hg)
    · exact hij
    · have hg := population_policy_marginal_gap M q hq L hL hlev gap hgap
        k j i hk hj.1 hij hi.2
      rw [he, sub_self] at hg
      exact False.elim (not_le_of_gt hgap.1 hg)
  · rintro rfl
    rfl

-- @node: baseline_recovery_close_iff_same_level
/-- Assume [the threshold-crossing model](hyp:h), [invariant level ordering](hyp:hL),
and [uniform positive separation of distinct propensities](hyp:hgap). For
[a positive valid first baseline index](hyp:hi), [a positive valid second
index](hyp:hj), [an instrument in the first class](hyp:hz), and [an instrument
in the second class](hyp:hw), if [the first fitted baseline mean has error
below a quarter of the gap](hyp:hpz) and [the second has error below a quarter
of the gap](hyp:hpw), then [their fitted means differ by less than half the gap
exactly when the baseline class indices coincide](goal). -/
lemma baseline_recovery_close_iff_same_level (h : ThresholdCrossing M)
    (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (gap : ℝ)
    (hgap : PropensityGapSeparationWitness M.prop q gap)
    (i j : ℕ) (hi : 1 ≤ i ∧ i ≤ L.K) (hj : 1 ≤ j ∧ j ≤ L.K)
    (z w : Z) (hz : z ∈ L.S i) (hw : w ∈ L.S j) (pb : Z → ℝ)
    (hpz : |pb z - ∫ x, M.prop z x ∂xLaw M| < gap / 4)
    (hpw : |pb w - ∫ x, M.prop w x ∂xLaw M| < gap / 4) :
    |pb z - pb w| < gap / 2 ↔ i = j := by
  have hz' : M.prop z = L.pLev i := by
    funext x
    exact (hL.2.2.2.2.2.1 x i z hi.2).mp hz
  have hw' : M.prop w = L.pLev j := by
    funext x
    exact (hL.2.2.2.2.2.1 x j w hj.2).mp hw
  have hsep : (∫ x, M.prop z x ∂xLaw M) = (∫ x, M.prop w x ∂xLaw M) ∨
      gap ≤ |(∫ x, M.prop z x ∂xLaw M) - ∫ x, M.prop w x ∂xLaw M| := by
    rw [hz', hw']
    rcases lt_trichotomy i j with hij | hij | hij
    · right
      rw [abs_sub_comm]
      exact (population_baseline_marginal_gap M h q L hL gap hgap i j hi.1 hij hj.2).trans
        (le_abs_self _)
    · subst j
      exact Or.inl rfl
    · right
      exact (population_baseline_marginal_gap M h q L hL gap hgap j i hj.1 hij hi.2).trans
        (le_abs_self _)
  exact (separated_values_close_iff_equal _ _ _ _ gap hpz hpw hsep).trans
    (population_baseline_class_marginal_equal_iff M h q L hL gap hgap i j hi hj z w hz hw)

-- @node: policy_recovery_close_iff_same_level
/-- Under [joint measurability of policy propensities](hyp:hq), [invariant level
ordering](hyp:hL), [measurable baseline levels](hyp:hlev), and [uniform positive
separation](hyp:hgap), take [a valid bin](hyp:hk), [a valid first policy
index](hyp:hi), [a valid second policy index](hyp:hj), [an instrument in the
first policy class](hyp:hz), and [an instrument in the second](hyp:hw). If
[the first fitted policy mean has error below a quarter of the gap](hyp:hqz)
and [the second has error below a quarter of the gap](hyp:hqw), then [their
fitted means differ by less than half the gap exactly when the within-bin
policy indices coincide](goal). -/
lemma policy_recovery_close_iff_same_level
    (q : Z → X → ℝ) (hq : Measurable (Function.uncurry q))
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (hlev : ∀ k, Measurable (L.pLev k)) (gap : ℝ)
    (hgap : PropensityGapSeparationWitness M.prop q gap)
    (k i j : ℕ) (hk : k ≤ L.K)
    (hi : 1 ≤ i ∧ i ≤ L.l k) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (z w : Z) (hz : z ∈ L.T k i) (hw : w ∈ L.T k j) (qb : Z → ℝ)
    (hqz : |qb z - ∫ x, q z x ∂xLaw M| < gap / 4)
    (hqw : |qb w - ∫ x, q w x ∂xLaw M| < gap / 4) :
    |qb z - qb w| < gap / 2 ↔ i = j := by
  have hz' : q z = L.qLev k i := by
    funext x
    exact (hL.2.2.2.2.2.2.1 x k i z hk hi.1 hi.2).mp hz
  have hw' : q w = L.qLev k j := by
    funext x
    exact (hL.2.2.2.2.2.2.1 x k j w hk hj.1 hj.2).mp hw
  have hsep : (∫ x, q z x ∂xLaw M) = (∫ x, q w x ∂xLaw M) ∨
      gap ≤ |(∫ x, q z x ∂xLaw M) - ∫ x, q w x ∂xLaw M| := by
    rw [hz', hw']
    rcases lt_trichotomy i j with hij | hij | hij
    · right
      rw [abs_sub_comm]
      exact (population_policy_marginal_gap M q hq L hL hlev gap hgap
        k i j hk hi.1 hij hj.2).trans (le_abs_self _)
    · subst j
      exact Or.inl rfl
    · right
      exact (population_policy_marginal_gap M q hq L hL hlev gap hgap
        k j i hk hj.1 hij hi.2).trans (le_abs_self _)
  have hc := separated_values_close_iff_equal _ _ _ _ gap hqz hqw hsep
  rw [hz', hw'] at hc
  exact hc.trans (population_policy_marginal_equal_iff M q hq L hL hlev gap hgap
    k i j hk hi hj)

-- Positive baseline levels need no uniform separation from zero. Their
-- strictly positive marginal means suffice because the threshold tends to zero.
-- @node: population_baseline_marginal_pos
/-- Under [the threshold-crossing model](hyp:h) and [invariant baseline and
policy level ordering](hyp:hL), [a positive baseline index no larger than the
number of baseline levels](hyp:hk) [has a strictly positive population
baseline-level mean](goal). -/
lemma population_baseline_marginal_pos (h : ThresholdCrossing M)
    (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (k : ℕ) (hk : 1 ≤ k ∧ k ≤ L.K) :
    0 < ∫ x, L.pLev k x ∂xLaw M := by
  haveI : IsProbabilityMeasure (xLaw M) := Measure.isProbabilityMeasure_map M.measX.aemeasurable
  have hr := hL.2.2.2.2.2.2.2.2.2.2.1
  have hm := ordered_baseline_level_measurable M h q L hL k hk
  have hb : ∀ x, ‖L.pLev k x‖ ≤ 1 := by
    intro x
    exact abs_le.mpr ⟨by linarith [(hr x k (by omega)).1], (hr x k (by omega)).2⟩
  have hf : Integrable (L.pLev k) (xLaw M) :=
    (MemLp.of_bound hm.aestronglyMeasurable 1 (Eventually.of_forall hb) :
      MemLp (L.pLev k) 2 (xLaw M)).integrable (by norm_num)
  have hp : ∀ x, 0 < L.pLev k x := by
    intro x
    have hz : L.pLev 0 x = 0 := by rw [hL.1 x 0 (by omega)]; simp [pLevel]
    have hs := hL.2.2.2.2.2.2.2.1 x 0 k (by omega) hk.2
    rwa [hz] at hs
  apply (integral_pos_iff_support_of_nonneg (fun x => (hp x).le) hf).2
  have hs : Function.support (L.pLev k) = univ := by
    ext x
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (hp x).ne'
  rw [hs]
  simp

end Papers.TbsPrteOptimalTransport
