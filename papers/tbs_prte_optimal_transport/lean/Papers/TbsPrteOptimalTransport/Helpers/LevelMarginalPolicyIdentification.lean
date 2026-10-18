module
public import Papers.TbsPrteOptimalTransport.Helpers.LevelMarginalBaselineIdentification
public import Papers.TbsPrteOptimalTransport.Helpers.LevelRecoveryProbability
/-! Identification of policy equality classes by marginal means.
The baseline-bin index and the within-bin policy index give the global order;
averaging preserves this order and therefore every policy equality class. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set
open scoped Classical

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: population_policy_level_lex_strict_order
/-- Under [an invariant ordering of baseline and policy levels](hyp:hL), if
[both baseline-bin indices are valid](hyp:hk,hr), [the first policy index is valid
in its bin](hyp:hi), [the second policy index is valid in its bin](hyp:hj), and
[the first bin-index and policy-index pair precedes the second lexicographically](hyp:hij),
then [the first policy level is strictly smaller at every covariate value](goal). -/
lemma population_policy_level_lex_strict_order
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (x : X) (k r i j : ℕ) (hk : k ≤ L.K) (hr : r ≤ L.K)
    (hi : 1 ≤ i ∧ i ≤ L.l k) (hj : 1 ≤ j ∧ j ≤ L.l r)
    (hij : k < r ∨ k = r ∧ i < j) :
    L.qLev k i x < L.qLev r j x := by
  rcases hij with hkr | ⟨rfl, hij⟩
  · have hu := interior_policy_level_strict_upper M q L hL x k i
      (hkr.trans_le hr) hi.1 hi.2
    have hm := canonical_baseline_levels_monotone M q L hL x (k + 1) r
      (by omega) (by omega)
    have hl := (policy_level_bin_bounds M q L hL x r j hr (by omega)).1
    exact hu.trans_le (hm.trans hl)
  · exact hL.2.2.2.2.2.2.2.2.1 x k i j hk hi.1 hij hj.2

-- @node: population_policy_marginal_lex_gap
/-- If [the policy propensity is jointly measurable](hyp:hq), [level ordering is
invariant across covariates](hyp:hL), [baseline levels are measurable](hyp:hlev),
and [distinct baseline or policy propensities have a uniform positive separation](hyp:hgap),
then, for [valid baseline-bin indices](hyp:hk,hr), [a valid first policy index](hyp:hi)
and [a valid second policy index](hyp:hj) whose [index pairs are in increasing
lexicographic order](hyp:hij), [the second policy-level mean exceeds the first
by at least the separation gap](goal). -/
lemma population_policy_marginal_lex_gap
    (q : Z → X → ℝ) (hq : Measurable (Function.uncurry q))
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (hlev : ∀ k, Measurable (L.pLev k)) (gap : ℝ)
    (hgap : PropensityGapSeparationWitness M.prop q gap)
    (k r i j : ℕ) (hk : k ≤ L.K) (hr : r ≤ L.K)
    (hi : 1 ≤ i ∧ i ≤ L.l k) (hj : 1 ≤ j ∧ j ≤ L.l r)
    (hij : k < r ∨ k = r ∧ i < j) :
    gap ≤ (∫ x, L.qLev r j x ∂xLaw M) - ∫ x, L.qLev k i x ∂xLaw M := by
  have : IsProbabilityMeasure (xLaw M) :=
    Measure.isProbabilityMeasure_map M.measX.aemeasurable
  obtain ⟨z, hz⟩ := ordered_policy_level_nonempty M q L hL k i hk hi.1 hi.2
  obtain ⟨w, hw⟩ := ordered_policy_level_nonempty M q L hL r j hr hj.1 hj.2
  have hmi := ordered_policy_level_measurable M q hq L hL hlev k i hk hi.2
  have hmj := ordered_policy_level_measurable M q hq L hL hlev r j hr hj.2
  have hrange := hL.2.2.2.2.2.2.2.2.2.2.2
  have hbi : ∀ x, ‖L.qLev k i x‖ ≤ 1 := by
    intro x
    exact abs_le.mpr ⟨by linarith [(hrange x k i hk (by omega)).1],
      (hrange x k i hk (by omega)).2⟩
  have hbj : ∀ x, ‖L.qLev r j x‖ ≤ 1 := by
    intro x
    exact abs_le.mpr ⟨by linarith [(hrange x r j hr (by omega)).1],
      (hrange x r j hr (by omega)).2⟩
  apply ordered_marginal_gap (xLaw M) _ _
    ((MemLp.of_bound hmi.aestronglyMeasurable 1 (Filter.Eventually.of_forall hbi) :
      MemLp (L.qLev k i) 2 (xLaw M)).integrable (by norm_num))
    ((MemLp.of_bound hmj.aestronglyMeasurable 1 (Filter.Eventually.of_forall hbj) :
      MemLp (L.qLev r j) 2 (xLaw M)).integrable (by norm_num)) gap
  apply Filter.Eventually.of_forall
  intro x
  have hz' := (hL.2.2.2.2.2.2.1 x k i z hk hi.1 hi.2).mp hz
  have hw' := (hL.2.2.2.2.2.2.1 x r j w hr hj.1 hj.2).mp hw
  have hs := population_policy_level_lex_strict_order M q L hL x k r i j hk hr hi hj hij
  have hg := hgap.2 x (q z x) (Or.inr ⟨z, rfl⟩) (q w x) (Or.inr ⟨w, rfl⟩)
  rw [hz', hw'] at hg
  rcases hg with he | hg
  · exact False.elim (hs.ne he.symm)
  · rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hs)] at hg
    exact hg.le

-- @node: population_policy_marginal_lex_order_iff
/-- Given [joint measurability of policy propensities](hyp:hq), [invariant level
ordering](hyp:hL), [measurable baseline levels](hyp:hlev), and [uniform positive
separation of distinct propensities](hyp:hgap), for [valid bin indices](hyp:hk,hr)
and [valid policy indices in the first](hyp:hi) and [second bin](hyp:hj),
[the first policy-level mean is smaller exactly when its bin-index and
policy-index pair precedes the second lexicographically](goal). -/
lemma population_policy_marginal_lex_order_iff
    (q : Z → X → ℝ) (hq : Measurable (Function.uncurry q))
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (hlev : ∀ k, Measurable (L.pLev k)) (gap : ℝ)
    (hgap : PropensityGapSeparationWitness M.prop q gap)
    (k r i j : ℕ) (hk : k ≤ L.K) (hr : r ≤ L.K)
    (hi : 1 ≤ i ∧ i ≤ L.l k) (hj : 1 ≤ j ∧ j ≤ L.l r) :
    (∫ x, L.qLev k i x ∂xLaw M) < (∫ x, L.qLev r j x ∂xLaw M) ↔
      k < r ∨ k = r ∧ i < j := by
  have forward : ∀ k r i j, k ≤ L.K → r ≤ L.K →
      (1 ≤ i ∧ i ≤ L.l k) → (1 ≤ j ∧ j ≤ L.l r) →
      (k < r ∨ k = r ∧ i < j) →
      (∫ x, L.qLev k i x ∂xLaw M) < (∫ x, L.qLev r j x ∂xLaw M) := by
    intro k r i j hk hr hi hj hij
    have hg := population_policy_marginal_lex_gap M q hq L hL hlev gap hgap
      k r i j hk hr hi hj hij
    linarith [hgap.1]
  constructor
  · intro hlt
    by_contra hn
    by_cases hkr : k = r
    · subst r
      have hji : j ≤ i := by omega
      rcases hji.eq_or_lt with rfl | hji
      · exact lt_irrefl _ hlt
      · exact lt_asymm hlt (forward k k j i hk hk hj hi (Or.inr ⟨rfl, hji⟩))
    · have hrk : r < k := by omega
      exact lt_asymm hlt (forward r k j i hr hk hj hi (Or.inl hrk))
  · exact forward k r i j hk hr hi hj

-- @node: population_policy_marginal_indices_iff
/-- With [jointly measurable policy propensities](hyp:hq), [invariant level
ordering](hyp:hL), [measurable baseline levels](hyp:hlev), and [uniform positive
separation of distinct propensities](hyp:hgap), for [valid bins](hyp:hk,hr),
[a valid policy index in the first bin](hyp:hi), and [a valid policy index in
the second](hyp:hj), [the two policy-level means coincide exactly when both
their bin indices and their within-bin indices coincide](goal). -/
lemma population_policy_marginal_indices_iff
    (q : Z → X → ℝ) (hq : Measurable (Function.uncurry q))
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (hlev : ∀ k, Measurable (L.pLev k)) (gap : ℝ)
    (hgap : PropensityGapSeparationWitness M.prop q gap)
    (k r i j : ℕ) (hk : k ≤ L.K) (hr : r ≤ L.K)
    (hi : 1 ≤ i ∧ i ≤ L.l k) (hj : 1 ≤ j ∧ j ≤ L.l r) :
    (∫ x, L.qLev k i x ∂xLaw M) = (∫ x, L.qLev r j x ∂xLaw M) ↔
      k = r ∧ i = j := by
  constructor
  · intro heq
    have hnot := (population_policy_marginal_lex_order_iff M q hq L hL hlev
      gap hgap k r i j hk hr hi hj).not.mp (by rw [heq]; exact lt_irrefl _)
    have hnot' := (population_policy_marginal_lex_order_iff M q hq L hL hlev
      gap hgap r k j i hr hk hj hi).not.mp (by rw [heq]; exact lt_irrefl _)
    omega
  · rintro ⟨rfl, rfl⟩
    rfl

-- @node: population_policy_class_eq_marginal_fiber
/-- Assuming [joint measurability of policy propensities](hyp:hq), [invariant
level ordering](hyp:hL), [measurable baseline levels](hyp:hlev), and [uniform
positive separation of distinct propensities](hyp:hgap), for [a valid bin](hyp:hk)
and [a valid policy level within it](hyp:hi), [the policy equality class consists
exactly of the instrument values whose policy-propensity mean equals that
level's mean](goal). -/
lemma population_policy_class_eq_marginal_fiber
    (q : Z → X → ℝ) (hq : Measurable (Function.uncurry q))
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (hlev : ∀ k, Measurable (L.pLev k)) (gap : ℝ)
    (hgap : PropensityGapSeparationWitness M.prop q gap)
    (k i : ℕ) (hk : k ≤ L.K) (hi : 1 ≤ i ∧ i ≤ L.l k) :
    L.T k i = Finset.univ.filter (fun z =>
      (∫ x, q z x ∂xLaw M) = ∫ x, L.qLev k i x ∂xLaw M) := by
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hz
    have heq : q z = L.qLev k i := by
      funext x
      exact (hL.2.2.2.2.2.2.1 x k i z hk hi.1 hi.2).mp hz
    rw [heq]
  · intro hz
    let x₀ : X := Classical.choice inferInstance
    obtain ⟨r, hr, j, hj0, hj, hm, _, _⟩ := finite_policy_level_cover M q L hL x₀ z
    have heq : q z = L.qLev r j := by
      funext x
      exact (hL.2.2.2.2.2.2.1 x r j z hr hj0 hj).mp hm
    rw [heq] at hz
    obtain ⟨rfl, rfl⟩ := (population_policy_marginal_indices_iff M q hq L hL hlev
      gap hgap r k j i hr hk ⟨hj0, hj⟩ hi).mp hz
    exact hm

-- @node: population_policy_marginal_eq_iff_pointwise
/-- If [policy propensities are jointly measurable](hyp:hq), [their level
ordering is invariant](hyp:hL), [baseline levels are measurable](hyp:hlev), and
[distinct propensities are uniformly positively separated](hyp:hgap), then
[two instrument values have equal policy-propensity means exactly when their
policy propensities agree at any given covariate value](goal). -/
lemma population_policy_marginal_eq_iff_pointwise
    (q : Z → X → ℝ) (hq : Measurable (Function.uncurry q))
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (hlev : ∀ k, Measurable (L.pLev k)) (gap : ℝ)
    (hgap : PropensityGapSeparationWitness M.prop q gap)
    (x : X) (z w : Z) :
    (∫ t, q z t ∂xLaw M) = (∫ t, q w t ∂xLaw M) ↔ q z x = q w x := by
  obtain ⟨k, hk, i, hi0, hi, hw, _, _⟩ := finite_policy_level_cover M q L hL x w
  have heq : q w = L.qLev k i := by
    funext t
    exact (hL.2.2.2.2.2.2.1 t k i w hk hi0 hi).mp hw
  rw [heq]
  have hfiber := population_policy_class_eq_marginal_fiber M q hq L hL hlev
    gap hgap k i hk ⟨hi0, hi⟩
  have hz : z ∈ L.T k i ↔
      (∫ t, q z t ∂xLaw M) = ∫ t, L.qLev k i t ∂xLaw M := by
    rw [hfiber]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hz.symm.trans (hL.2.2.2.2.2.2.1 x k i z hk hi0 hi)

-- @node: population_policy_marginal_lt_iff_pointwise
/-- Under [joint measurability of policy propensities](hyp:hq), [invariant level
ordering](hyp:hL), [measurability of baseline levels](hyp:hlev), and [uniform
positive separation of distinct propensities](hyp:hgap), [the policy-propensity
mean at the first instrument value is smaller than at the second exactly when
the same strict inequality holds at any given covariate value](goal). -/
lemma population_policy_marginal_lt_iff_pointwise
    (q : Z → X → ℝ) (hq : Measurable (Function.uncurry q))
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (hlev : ∀ k, Measurable (L.pLev k)) (gap : ℝ)
    (hgap : PropensityGapSeparationWitness M.prop q gap)
    (x : X) (z w : Z) :
    (∫ t, q z t ∂xLaw M) < (∫ t, q w t ∂xLaw M) ↔ q z x < q w x := by
  obtain ⟨k, hk, i, hi0, hi, hz, _, _⟩ := finite_policy_level_cover M q L hL x z
  obtain ⟨r, hr, j, hj0, hj, hw, _, _⟩ := finite_policy_level_cover M q L hL x w
  have hez : q z = L.qLev k i := by
    funext t
    exact (hL.2.2.2.2.2.2.1 t k i z hk hi0 hi).mp hz
  have hew : q w = L.qLev r j := by
    funext t
    exact (hL.2.2.2.2.2.2.1 t r j w hr hj0 hj).mp hw
  rw [hez, hew, population_policy_marginal_lex_order_iff M q hq L hL hlev
    gap hgap k r i j hk hr ⟨hi0, hi⟩ ⟨hj0, hj⟩]
  constructor
  · exact population_policy_level_lex_strict_order M q L hL x k r i j
      hk hr ⟨hi0, hi⟩ ⟨hj0, hj⟩
  · intro hlt
    by_contra hn
    by_cases hkr : k = r
    · subst r
      have hji : j ≤ i := by omega
      rcases hji.eq_or_lt with rfl | hji
      · exact lt_irrefl _ hlt
      · exact lt_asymm hlt (population_policy_level_lex_strict_order M q L hL
          x k k j i hk hk ⟨hj0, hj⟩ ⟨hi0, hi⟩ (Or.inr ⟨rfl, hji⟩))
    · have hrk : r < k := by omega
      exact lt_asymm hlt (population_policy_level_lex_strict_order M q L hL
        x r k j i hr hk ⟨hj0, hj⟩ ⟨hi0, hi⟩ (Or.inl hrk))

-- @node: interior_policy_level_strict_lower
/-- If [level ordering is invariant](hyp:hL) and [policy levels avoid baseline
boundaries](hyp:hOff), then, for [a bin below the final bin](hyp:hk) and
[a valid policy index in it](hyp:hj), [the policy level is strictly above the
bin's lower baseline level at every covariate value](goal). -/
lemma interior_policy_level_strict_lower
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (hOff : PolicyLevelOffBoundary L) (x : X) (k j : ℕ)
    (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    L.pLev k x < L.qLev k j x := by
  have hb := (policy_level_bin_bounds M q L hL x k j hk.le (by omega)).1
  have hn := hOff k hk j hj.1 hj.2
    (ordered_policy_level_nonempty M q L hL k j hk.le hj.1 hj.2) x
  exact lt_of_le_of_ne hb hn.symm

-- @node: population_baseline_policy_pointwise_order
/-- Under [invariant level ordering](hyp:hL) and [avoidance of baseline
boundaries by policy levels](hyp:hOff), take [a valid baseline index](hyp:hi),
[a policy bin below the final bin](hyp:hk), and [a valid policy index in that
bin](hyp:hj). Then [the baseline level is below the policy level exactly when
its index is no larger than the policy bin index, and the policy level is below
the baseline level exactly when the policy bin index is smaller](goal). -/
lemma population_baseline_policy_pointwise_order
    (q : Z → X → ℝ) (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (hOff : PolicyLevelOffBoundary L) (x : X) (i k j : ℕ)
    (hi : i ≤ L.K) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    (L.pLev i x < L.qLev k j x ↔ i ≤ k) ∧
    (L.qLev k j x < L.pLev i x ↔ k < i) := by
  have lower (hik : i ≤ k) : L.pLev i x < L.qLev k j x :=
    (canonical_baseline_levels_monotone M q L hL x i k hik (by omega)).trans_lt
      (interior_policy_level_strict_lower M q L hL hOff x k j hk hj)
  have upper (hki : k < i) : L.qLev k j x < L.pLev i x :=
    (interior_policy_level_strict_upper M q L hL x k j hk hj.1 hj.2).trans_le
      (canonical_baseline_levels_monotone M q L hL x (k + 1) i (by omega) (by omega))
  constructor
  · constructor
    · intro hlt
      by_contra hn
      exact lt_asymm hlt (upper (Nat.lt_of_not_ge hn))
    · exact lower
  · constructor
    · intro hlt
      by_contra hn
      exact lt_asymm hlt (lower (Nat.le_of_not_gt hn))
    · exact upper

-- @node: population_baseline_policy_marginal_gaps
/-- Assume [jointly measurable policy propensities](hyp:hq), [invariant level
ordering](hyp:hL), [policy levels off baseline boundaries](hyp:hOff), [measurable
baseline levels](hyp:hlev), and [uniform positive separation of distinct
propensities](hyp:hgap). For [a positive valid baseline index](hyp:hi), [a policy
bin below the final bin](hyp:hk), and [a valid policy index](hyp:hj), [the policy
mean exceeds the baseline mean by at least the gap when the baseline index is
no larger than the bin index, and the reverse difference is at least the gap
when the bin index is smaller](goal). -/
lemma population_baseline_policy_marginal_gaps
    (q : Z → X → ℝ) (hq : Measurable (Function.uncurry q))
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (hOff : PolicyLevelOffBoundary L) (hlev : ∀ k, Measurable (L.pLev k))
    (gap : ℝ) (hgap : PropensityGapSeparationWitness M.prop q gap)
    (i k j : ℕ) (hi : 1 ≤ i ∧ i ≤ L.K)
    (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    (i ≤ k → gap ≤ (∫ x, L.qLev k j x ∂xLaw M) - ∫ x, L.pLev i x ∂xLaw M) ∧
    (k < i → gap ≤ (∫ x, L.pLev i x ∂xLaw M) - ∫ x, L.qLev k j x ∂xLaw M) := by
  have : IsProbabilityMeasure (xLaw M) :=
    Measure.isProbabilityMeasure_map M.measX.aemeasurable
  obtain ⟨z, hz⟩ := ordered_baseline_level_nonempty M q L hL i hi
  obtain ⟨w, hw⟩ := ordered_policy_level_nonempty M q L hL k j hk.le hj.1 hj.2
  have hp : Integrable (L.pLev i) (xLaw M) := by
    apply (MemLp.of_bound (hlev i).aestronglyMeasurable 1
      (Filter.Eventually.of_forall ?_) : MemLp (L.pLev i) 2 (xLaw M)).integrable
      (by norm_num)
    intro x
    have hr := hL.2.2.2.2.2.2.2.2.2.2.1 x i (by omega)
    exact abs_le.mpr ⟨by linarith [hr.1], hr.2⟩
  have hm := ordered_policy_level_measurable M q hq L hL hlev k j hk.le hj.2
  have hqj : Integrable (L.qLev k j) (xLaw M) := by
    apply (MemLp.of_bound hm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall ?_) : MemLp (L.qLev k j) 2 (xLaw M)).integrable
      (by norm_num)
    intro x
    have hr := hL.2.2.2.2.2.2.2.2.2.2.2 x k j hk.le (by omega)
    exact abs_le.mpr ⟨by linarith [hr.1], hr.2⟩
  have hg (x : X) := hgap.2 x (M.prop z x) (Or.inl ⟨z, rfl⟩)
    (q w x) (Or.inr ⟨w, rfl⟩)
  have hz' (x : X) := (hL.2.2.2.2.2.1 x i z hi.2).mp hz
  have hw' (x : X) := (hL.2.2.2.2.2.2.1 x k j w hk.le hj.1 hj.2).mp hw
  constructor
  · intro hik
    apply ordered_marginal_gap (xLaw M) _ _ hp hqj gap
    apply Filter.Eventually.of_forall
    intro x
    have hs := (population_baseline_policy_pointwise_order M q L hL hOff
      x i k j hi.2 hk hj).1.mpr hik
    have hgx := hg x
    rw [hz' x, hw' x] at hgx
    rcases hgx with he | he
    · exact False.elim (hs.ne he.symm)
    · rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hs)] at he
      exact he.le
  · intro hki
    apply ordered_marginal_gap (xLaw M) _ _ hqj hp gap
    apply Filter.Eventually.of_forall
    intro x
    have hs := (population_baseline_policy_pointwise_order M q L hL hOff
      x i k j hi.2 hk hj).2.mpr hki
    have hgx := hg x
    rw [hz' x, hw' x] at hgx
    rcases hgx with he | he
    · exact False.elim (hs.ne he)
    · rw [abs_of_pos (sub_pos.mpr hs)] at he
      exact he.le

-- @node: population_baseline_policy_marginal_order
/-- Given [jointly measurable policy propensities](hyp:hq), [invariant level
ordering](hyp:hL), [policy levels off baseline boundaries](hyp:hOff), [measurable
baseline levels](hyp:hlev), and [uniform positive separation of distinct
propensities](hyp:hgap), take [a positive valid baseline index](hyp:hi), [a policy
bin below the final bin](hyp:hk), and [a valid policy index](hyp:hj). Then
[the baseline mean is smaller than the policy mean exactly when its index is
no larger than the bin index, and the policy mean is smaller exactly when the
bin index is smaller than the baseline index](goal). -/
lemma population_baseline_policy_marginal_order
    (q : Z → X → ℝ) (hq : Measurable (Function.uncurry q))
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (hOff : PolicyLevelOffBoundary L) (hlev : ∀ k, Measurable (L.pLev k))
    (gap : ℝ) (hgap : PropensityGapSeparationWitness M.prop q gap)
    (i k j : ℕ) (hi : 1 ≤ i ∧ i ≤ L.K)
    (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    ((∫ x, L.pLev i x ∂xLaw M) < (∫ x, L.qLev k j x ∂xLaw M) ↔ i ≤ k) ∧
    ((∫ x, L.qLev k j x ∂xLaw M) < (∫ x, L.pLev i x ∂xLaw M) ↔ k < i) := by
  have hg := population_baseline_policy_marginal_gaps M q hq L hL hOff hlev
    gap hgap i k j hi hk hj
  have lower (hik : i ≤ k) :
      (∫ x, L.pLev i x ∂xLaw M) < ∫ x, L.qLev k j x ∂xLaw M := by
    linarith [hg.1 hik, hgap.1]
  have upper (hki : k < i) :
      (∫ x, L.qLev k j x ∂xLaw M) < ∫ x, L.pLev i x ∂xLaw M := by
    linarith [hg.2 hki, hgap.1]
  constructor
  · constructor
    · intro hlt
      by_contra hn
      exact lt_asymm hlt (upper (Nat.lt_of_not_ge hn))
    · exact lower
  · constructor
    · intro hlt
      by_contra hn
      exact lt_asymm hlt (lower (Nat.le_of_not_gt hn))
    · exact upper

-- @node: population_baseline_policy_marginal_separation
/-- Suppose [policy propensities are jointly measurable](hyp:hq), [level ordering
is invariant](hyp:hL), [policy levels avoid baseline boundaries](hyp:hOff),
[baseline levels are measurable](hyp:hlev), and [distinct propensities have a
uniform positive gap](hyp:hgap). For [a positive valid baseline index](hyp:hi),
[a bin below the final bin](hyp:hk), [a valid policy index](hyp:hj), [an instrument
in that baseline class](hyp:hz), and [an instrument in that policy class](hyp:hw),
[the absolute difference between their baseline and policy means is at least
the gap](goal). -/
lemma population_baseline_policy_marginal_separation
    (q : Z → X → ℝ) (hq : Measurable (Function.uncurry q))
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (hOff : PolicyLevelOffBoundary L) (hlev : ∀ k, Measurable (L.pLev k))
    (gap : ℝ) (hgap : PropensityGapSeparationWitness M.prop q gap)
    (i k j : ℕ) (hi : 1 ≤ i ∧ i ≤ L.K)
    (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (z w : Z) (hz : z ∈ L.S i) (hw : w ∈ L.T k j) :
    gap ≤ |(∫ x, M.prop z x ∂xLaw M) - ∫ x, q w x ∂xLaw M| := by
  have hez : M.prop z = L.pLev i :=
    funext (fun x => (hL.2.2.2.2.2.1 x i z hi.2).mp hz)
  have hew : q w = L.qLev k j :=
    funext (fun x => (hL.2.2.2.2.2.2.1 x k j w hk.le hj.1 hj.2).mp hw)
  rw [hez, hew]
  have hg := population_baseline_policy_marginal_gaps M q hq L hL hOff hlev
    gap hgap i k j hi hk hj
  rcases le_or_gt i k with hik | hki
  · rw [abs_sub_comm]
    exact (hg.1 hik).trans (le_abs_self _)
  · exact (hg.2 hki).trans (le_abs_self _)

-- @node: baseline_policy_recovery_no_cross_edge
/-- Under [joint measurability of policy propensities](hyp:hq), [invariant level
ordering](hyp:hL), [policy levels off baseline boundaries](hyp:hOff), [measurable
baseline levels](hyp:hlev), and [uniform positive separation](hyp:hgap), consider
[a positive valid baseline index](hyp:hi), [a bin below the final bin](hyp:hk),
[a valid policy index](hyp:hj), [an instrument in the baseline class](hyp:hz),
and [an instrument in the policy class](hyp:hw). If [the fitted baseline mean
has error less than a quarter of the gap](hyp:hpz) and [the fitted policy mean
has error less than a quarter of the gap](hyp:hqw), [their fitted means cannot
differ by less than half the gap](goal). -/
lemma baseline_policy_recovery_no_cross_edge
    (q : Z → X → ℝ) (hq : Measurable (Function.uncurry q))
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (hOff : PolicyLevelOffBoundary L) (hlev : ∀ k, Measurable (L.pLev k))
    (gap : ℝ) (hgap : PropensityGapSeparationWitness M.prop q gap)
    (i k j : ℕ) (hi : 1 ≤ i ∧ i ≤ L.K)
    (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (z w : Z) (hz : z ∈ L.S i) (hw : w ∈ L.T k j)
    (pb qb : Z → ℝ)
    (hpz : |pb z - ∫ x, M.prop z x ∂xLaw M| < gap / 4)
    (hqw : |qb w - ∫ x, q w x ∂xLaw M| < gap / 4) :
    ¬ |pb z - qb w| < gap / 2 := by
  have hs := population_baseline_policy_marginal_separation M q hq L hL hOff hlev
    gap hgap i k j hi hk hj z w hz hw
  have hn : (∫ x, M.prop z x ∂xLaw M) ≠ ∫ x, q w x ∂xLaw M := by
    intro he
    rw [he, sub_self, abs_zero] at hs
    exact (not_le_of_gt hgap.1) hs
  have hc := separated_values_close_iff_equal
    (∫ x, M.prop z x ∂xLaw M) (∫ x, q w x ∂xLaw M)
    (pb z) (qb w) gap hpz hqw (Or.inr hs)
  exact fun hclose => hn (hc.mp hclose)

-- @node: population_policy_class_marginal_separation
/-- With [jointly measurable policy propensities](hyp:hq), [invariant level
ordering](hyp:hL), [measurable baseline levels](hyp:hlev), and [uniform positive
separation of distinct propensities](hyp:hgap), take [valid bins](hyp:hk,hr),
[a valid policy index in the first](hyp:hi), [a valid policy index in the
second](hyp:hj), and [instruments belonging to the respective policy
classes](hyp:hz,hw). Then [their policy-propensity means either coincide or
differ in absolute value by at least the gap](goal). -/
lemma population_policy_class_marginal_separation
    (q : Z → X → ℝ) (hq : Measurable (Function.uncurry q))
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (hlev : ∀ k, Measurable (L.pLev k)) (gap : ℝ)
    (hgap : PropensityGapSeparationWitness M.prop q gap)
    (k r i j : ℕ) (hk : k ≤ L.K) (hr : r ≤ L.K)
    (hi : 1 ≤ i ∧ i ≤ L.l k) (hj : 1 ≤ j ∧ j ≤ L.l r)
    (z w : Z) (hz : z ∈ L.T k i) (hw : w ∈ L.T r j) :
    (∫ x, q z x ∂xLaw M) = (∫ x, q w x ∂xLaw M) ∨
      gap ≤ |(∫ x, q z x ∂xLaw M) - ∫ x, q w x ∂xLaw M| := by
  have hez : q z = L.qLev k i :=
    funext (fun x => (hL.2.2.2.2.2.2.1 x k i z hk hi.1 hi.2).mp hz)
  have hew : q w = L.qLev r j :=
    funext (fun x => (hL.2.2.2.2.2.2.1 x r j w hr hj.1 hj.2).mp hw)
  rw [hez, hew]
  by_cases heq : k = r ∧ i = j
  · rcases heq with ⟨rfl, rfl⟩
    exact Or.inl rfl
  · right
    have horder : (k < r ∨ k = r ∧ i < j) ∨ (r < k ∨ r = k ∧ j < i) := by
      omega
    rcases horder with hkr | hrk
    · rw [abs_sub_comm]
      exact (population_policy_marginal_lex_gap M q hq L hL hlev gap hgap
        k r i j hk hr hi hj hkr).trans (le_abs_self _)
    · exact (population_policy_marginal_lex_gap M q hq L hL hlev gap hgap
        r k j i hr hk hj hi hrk).trans (le_abs_self _)

-- @node: population_policy_marginals_separated
/-- If [policy propensities are jointly measurable](hyp:hq), [level ordering is
invariant](hyp:hL), [baseline levels are measurable](hyp:hlev), and [distinct
propensities are uniformly positively separated](hyp:hgap), then [any two
instrument values have policy-propensity means that either coincide or differ
in absolute value by at least the separation gap](goal). -/
lemma population_policy_marginals_separated
    (q : Z → X → ℝ) (hq : Measurable (Function.uncurry q))
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (hlev : ∀ k, Measurable (L.pLev k)) (gap : ℝ)
    (hgap : PropensityGapSeparationWitness M.prop q gap) (z w : Z) :
    (∫ x, q z x ∂xLaw M) = (∫ x, q w x ∂xLaw M) ∨
      gap ≤ |(∫ x, q z x ∂xLaw M) - ∫ x, q w x ∂xLaw M| := by
  let x₀ : X := Classical.choice inferInstance
  obtain ⟨k, hk, i, hi0, hi, hz, _, _⟩ := finite_policy_level_cover M q L hL x₀ z
  obtain ⟨r, hr, j, hj0, hj, hw, _, _⟩ := finite_policy_level_cover M q L hL x₀ w
  exact population_policy_class_marginal_separation M q hq L hL hlev gap hgap
    k r i j hk hr ⟨hi0, hi⟩ ⟨hj0, hj⟩ z w hz hw

-- @node: policy_recovery_close_iff_pointwise_equal
/-- Assuming [jointly measurable policy propensities](hyp:hq), [invariant level
ordering](hyp:hL), [measurable baseline levels](hyp:hlev), and [uniform positive
separation](hyp:hgap), if [the first fitted policy mean has error below a quarter
of the gap](hyp:hqz) and [the second has error below a quarter of the gap](hyp:hqw),
then [the fitted means differ by less than half the gap exactly when the two
policy propensities agree at any given covariate value](goal). -/
lemma policy_recovery_close_iff_pointwise_equal
    (q : Z → X → ℝ) (hq : Measurable (Function.uncurry q))
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (hlev : ∀ k, Measurable (L.pLev k)) (gap : ℝ)
    (hgap : PropensityGapSeparationWitness M.prop q gap)
    (qb : Z → ℝ) (x : X) (z w : Z)
    (hqz : |qb z - ∫ t, q z t ∂xLaw M| < gap / 4)
    (hqw : |qb w - ∫ t, q w t ∂xLaw M| < gap / 4) :
    |qb z - qb w| < gap / 2 ↔ q z x = q w x := by
  exact (separated_values_close_iff_equal _ _ _ _ gap hqz hqw
    (population_policy_marginals_separated M q hq L hL hlev gap hgap z w)).trans
    (population_policy_marginal_eq_iff_pointwise M q hq L hL hlev gap hgap x z w)

-- @node: policy_recoveryEdge_iff_pointwise_equal
/-- Under [joint measurability of policy propensities](hyp:hq), [invariant level
ordering](hyp:hL), [measurable baseline levels](hyp:hlev), and [uniform positive
separation](hyp:hgap), if [the first fitted policy mean has error below a quarter
of the gap](hyp:hqz) and [the second has error below a quarter of the gap](hyp:hqw),
[a recovery edge joins the two policy vertices exactly when their instrument
values are distinct and their policy propensities agree at the given covariate
value](goal). -/
lemma policy_recoveryEdge_iff_pointwise_equal
    (q : Z → X → ℝ) (hq : Measurable (Function.uncurry q))
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (hlev : ∀ k, Measurable (L.pLev k)) (gap : ℝ)
    (hgap : PropensityGapSeparationWitness M.prop q gap)
    (pb qb : Z → ℝ) (rho : ℝ) (x : X) (z w : Z)
    (hqz : |qb z - ∫ t, q z t ∂xLaw M| < gap / 4)
    (hqw : |qb w - ∫ t, q w t ∂xLaw M| < gap / 4) :
    recoveryEdge pb qb rho gap (true, z) (true, w) ↔ z ≠ w ∧ q z x = q w x := by
  have hc := policy_recovery_close_iff_pointwise_equal M q hq L hL hlev
    gap hgap qb x z w hqz hqw
  have hn : (true, z) ≠ (true, w) ↔ z ≠ w :=
    ⟨fun h he => h (congrArg (fun t : Z => (true, t)) he),
      fun h he => h (congrArg Prod.snd he)⟩
  simpa only [recoveryEdge, recoveryActive, Finset.mem_filter, Finset.mem_univ,
    true_or, true_and, hn, vertexValue, if_true]
    using and_congr_right (fun _ : z ≠ w => hc)

-- @node: policy_recovery_path_iff_pointwise_equal
/-- With [jointly measurable policy propensities](hyp:hq), [invariant level
ordering](hyp:hL), [measurable baseline levels](hyp:hlev), [uniform positive
separation](hyp:hgap), and [all fitted policy means accurate to less than a
quarter of the gap](hyp:herr), [two instruments are connected by a path using
only policy vertices, allowing a path of length zero, exactly when their
policy propensities agree at the given covariate value](goal). -/
lemma policy_recovery_path_iff_pointwise_equal
    (q : Z → X → ℝ) (hq : Measurable (Function.uncurry q))
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (hlev : ∀ k, Measurable (L.pLev k)) (gap : ℝ)
    (hgap : PropensityGapSeparationWitness M.prop q gap)
    (pb qb : Z → ℝ) (rho : ℝ) (x : X)
    (herr : ∀ z, |qb z - ∫ t, q z t ∂xLaw M| < gap / 4) (z w : Z) :
    Relation.ReflTransGen (fun a b => recoveryEdge pb qb rho gap (true, a) (true, b))
      z w ↔ q z x = q w x := by
  constructor
  · intro hp
    induction hp with
    | refl => rfl
    | @tail b c _ hbc ih =>
      exact ih.trans ((policy_recoveryEdge_iff_pointwise_equal M q hq L hL hlev
        gap hgap pb qb rho x b c (herr b) (herr c)).mp hbc).2
  · intro heq
    by_cases hzw : z = w
    · subst w
      exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single
        ((policy_recoveryEdge_iff_pointwise_equal M q hq L hL hlev gap hgap
          pb qb rho x z w (herr z) (herr w)).mpr ⟨hzw, heq⟩)

-- The policy-only subgraph has precisely the population T classes, including
-- classes in the final bin. This assertion does not use fitted baseline levels.
-- @node: policy_recovery_path_class_eq
/-- Suppose [policy propensities are jointly measurable](hyp:hq), [level ordering
is invariant](hyp:hL), [baseline levels are measurable](hyp:hlev), [distinct
propensities are uniformly positively separated](hyp:hgap), and [every fitted
policy mean has error below a quarter of the gap](hyp:herr). For [a valid
bin](hyp:hk), [a valid policy index](hyp:hi), and [an instrument in that policy
class](hyp:hz), [the instruments reachable from it through policy vertices are
exactly its population policy class](goal). -/
lemma policy_recovery_path_class_eq
    (q : Z → X → ℝ) (hq : Measurable (Function.uncurry q))
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (hlev : ∀ k, Measurable (L.pLev k)) (gap : ℝ)
    (hgap : PropensityGapSeparationWitness M.prop q gap)
    (pb qb : Z → ℝ) (rho : ℝ)
    (herr : ∀ z, |qb z - ∫ t, q z t ∂xLaw M| < gap / 4)
    (k i : ℕ) (hk : k ≤ L.K) (hi : 1 ≤ i ∧ i ≤ L.l k)
    (z : Z) (hz : z ∈ L.T k i) :
    Finset.univ.filter (fun w => Relation.ReflTransGen
      (fun a b => recoveryEdge pb qb rho gap (true, a) (true, b)) z w) = L.T k i := by
  let x₀ : X := Classical.choice inferInstance
  have hez := (hL.2.2.2.2.2.2.1 x₀ k i z hk hi.1 hi.2).mp hz
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [policy_recovery_path_iff_pointwise_equal M q hq L hL hlev
    gap hgap pb qb rho x₀ herr z w, hez]
  exact eq_comm.trans (hL.2.2.2.2.2.2.1 x₀ k i w hk hi.1 hi.2).symm

-- @node: policy_recovery_path_classes_failure_tendsto_zero
/-- For [a sampling measure](hyp:μ), assume [joint measurability of policy
propensities](hyp:hq), [invariant level ordering](hyp:hL), [measurable baseline
levels](hyp:hlev), [uniform positive separation of distinct propensities](hyp:hgap),
and [convergence in probability of every fitted policy mean to its population
mean](hyp:hconv). Then [the measure of samples on which some policy-only
reachable class fails to equal its population policy class tends to zero](goal). -/
lemma policy_recovery_path_classes_failure_tendsto_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (q : Z → X → ℝ) (hq : Measurable (Function.uncurry q))
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (hlev : ∀ k, Measurable (L.pLev k)) (gap : ℝ)
    (hgap : PropensityGapSeparationWitness M.prop q gap)
    (pb qb : ℕ → A → Z → ℝ) (rho : ℕ → ℝ)
    (hconv : ∀ z, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => qb n a z) Filter.atTop
      (fun _ _ => ∫ t, q z t ∂xLaw M)) :
    Filter.Tendsto (fun n => μ {a | ¬ (∀ k, k ≤ L.K →
      ∀ i, (1 ≤ i ∧ i ≤ L.l k) → ∀ z ∈ L.T k i,
        Finset.univ.filter (fun w => Relation.ReflTransGen
          (fun v u => recoveryEdge (pb n a) (qb n a) (rho n) gap
            (true, v) (true, u)) z w) = L.T k i)}) Filter.atTop (nhds 0) := by
  have herr := finite_marginal_errors_tendsto_zero μ qb
    (fun z => ∫ t, q z t ∂xLaw M) hconv (gap / 4) (by linarith [hgap.1])
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds herr
    (fun _ => zero_le)
  intro n
  apply measure_mono
  intro a hbad
  by_contra hn
  have he : ∀ z, |qb n a z - ∫ t, q z t ∂xLaw M| < gap / 4 := by
    intro z
    exact lt_of_not_ge (fun hz => hn ⟨z, hz⟩)
  apply hbad
  intro k hk i hi z hz
  exact policy_recovery_path_class_eq M q hq L hL hlev gap hgap
    (pb n a) (qb n a) (rho n) he k i hk hi z hz

end Papers.TbsPrteOptimalTransport
