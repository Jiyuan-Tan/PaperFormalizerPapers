module
public import Papers.TbsPrteOptimalTransport.Helpers.DiscretePolicyTail
/-! Ordered baseline gaps and the policy weight on their finite slices. -/
public section
set_option linter.style.openClassical false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: finite_baseline_level_exists
/-- If [the baseline and policy levels obey the common ordering and class
structure](hyp:hL), then [each instrument's baseline propensity equals a canonical
baseline level with index between zero and the final baseline index](goal). -/
lemma finite_baseline_level_exists (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (x : X) (z : Z) :
    ∃ i ≤ L.K, M.prop z x = L.pLev i x := by
  by_cases hz : M.prop z x = 0
  · refine ⟨0, Nat.zero_le _, ?_⟩
    rw [hz, hL.1 x 0 (by omega)]
    simp [pLevel]
  · have hm : M.prop z x ∈ finiteLevels (fun z => M.prop z x) :=
      (finiteLevels_mem_iff _ (inferInstance : Finite Z) _).mpr
        ⟨mem_range_self z, lt_of_le_of_ne (M.rangeProp z x).1 (Ne.symm hz)⟩
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hm
    have hiK : i + 1 ≤ L.K := by rw [hL.2.2.2.1 x] at hi; omega
    refine ⟨i + 1, hiK, ?_⟩
    rw [hL.1 x (i + 1) (by omega)]
    simpa only [pLevel, Nat.succ_ne_zero, if_false, if_pos hi,
      if_pos (show i + 1 ≤ (finiteLevels (fun z => M.prop z x)).length by omega),
      Nat.add_sub_cancel, List.getD_eq_getElem _ _ hi] using he.symm

-- @node: interior_baseline_superlevel_membership
/-- If [the baseline and policy levels obey the common ordering and class
structure](hyp:hL), [the bin precedes the final baseline level](hyp:hk), and
[the resistance rank lies strictly between this bin's baseline endpoints](hyp:hu),
then [an instrument's baseline propensity is at least that rank exactly when the
instrument belongs to a strictly higher baseline class](goal). -/
lemma interior_baseline_superlevel_membership (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (x : X) (k : ℕ) (hk : k < L.K)
    (u : ℝ) (hu : u ∈ Ioo (L.pLev k x) (L.pLev (k+1) x)) (z : Z) :
    u ≤ M.prop z x ↔ z ∈ higherBaseline L k := by
  have hs := hL.2.2.2.2.2.2.2.1
  have hS := hL.2.2.2.2.2.1
  obtain ⟨i, hi, he⟩ := finite_baseline_level_exists M q L hL x z
  have hcmp : u ≤ M.prop z x ↔ k < i := by
    rw [he]
    constructor
    · intro hui
      by_contra hki
      have hik : i ≤ k := Nat.le_of_not_gt hki
      have hle : L.pLev i x ≤ L.pLev k x := by
        rcases hik.eq_or_lt with rfl | hik
        · exact le_rfl
        · exact (hs x i k hik hk.le).le
      exact (not_le_of_gt hu.1) (hui.trans hle)
    · intro hki
      have hle : L.pLev (k+1) x ≤ L.pLev i x := by
        rcases (Nat.succ_le_of_lt hki).eq_or_lt with hki | hki
        · exact le_of_eq (congrArg (fun j => L.pLev j x) hki)
        · exact (hs x (k+1) i hki hi).le
      exact hu.2.le.trans hle
  rw [hcmp]
  constructor
  · intro hki
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_range.mpr (by omega), ?_⟩
    rw [if_pos hki]
    exact (hS x i z hi).mpr he
  · intro hz
    obtain ⟨j, hj, hzj⟩ := Finset.mem_biUnion.mp hz
    have hjK : j ≤ L.K := by have := Finset.mem_range.mp hj; omega
    by_cases hkj : k < j
    · rw [if_pos hkj] at hzj
      have hej := (hS x j z hjK).mp hzj
      have hij : i = j := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hij | hji
        · have := hs x i j hij hjK
          rw [← he, ← hej] at this
          exact lt_irrefl _ this
        · have := hs x j i hji hi
          rw [← he, ← hej] at this
          exact lt_irrefl _ this
      simpa only [hij] using hkj
    · simp only [if_neg hkj, Finset.notMem_empty] at hzj

-- @node: finite_policy_weight_antitone_on_gap
/-- If [the baseline and policy levels obey the common ordering and class
structure](hyp:hL) and [the bin precedes the final baseline level](hyp:hk), then
[the policy weight is nonincreasing in the resistance rank on the open baseline gap](goal). -/
lemma finite_policy_weight_antitone_on_gap (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (x : X) (k : ℕ) (hk : k < L.K) :
    AntitoneOn (policyWeight M q x) (Ioo (L.pLev k x) (L.pLev (k+1) x)) := by
  intro s hs t ht hst
  rw [finite_policy_weight_sum, finite_policy_weight_sum]
  apply Finset.sum_le_sum
  intro z _
  have he : (s ≤ M.prop z x) ↔ (t ≤ M.prop z x) :=
    (interior_baseline_superlevel_membership M q L hL x k hk s hs z).trans
      (interior_baseline_superlevel_membership M q L hL x k hk t ht z).symm
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  have hi : (if t ≤ q z x then (1 : ℝ) else 0) ≤
      (if s ≤ q z x then (1 : ℝ) else 0) := by
    by_cases htq : t ≤ q z x
    · rw [if_pos htq, if_pos (hst.trans htq)]
    · rw [if_neg htq]
      split_ifs <;> norm_num
  simpa only [he] using sub_le_sub_right hi (if t ≤ M.prop z x then 1 else 0)

-- @node: canonical_baseline_levels_monotone
/-- If [the baseline and policy levels obey the common ordering and class
structure](hyp:hL), [the first baseline index is no larger than the second](hyp:hij),
and [the second is at most the final baseline index plus one](hyp:hj), then
[the first canonical baseline level is no larger than the second](goal). -/
lemma canonical_baseline_levels_monotone (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (x : X) (i j : ℕ)
    (hij : i ≤ j) (hj : j ≤ L.K + 1) : L.pLev i x ≤ L.pLev j x := by
  by_cases hjK : j ≤ L.K
  · rcases hij.eq_or_lt with rfl | hij
    · exact le_rfl
    · exact (hL.2.2.2.2.2.2.2.1 x i j hij hjK).le
  · have he : j = L.K + 1 := by omega
    subst j
    have hend : L.pLev (L.K+1) x = 1 := by
      rw [hL.1 x (L.K+1) le_rfl]
      simp [pLevel, hL.2.2.2.1 x]
    rw [hend]
    exact (hL.2.2.2.2.2.2.2.2.2.2.1 x i hij).2

-- @node: policy_level_bin_bounds
/-- If [the baseline and policy levels obey the common ordering and class
structure](hyp:hL), [the bin index is at most the final baseline index](hyp:hk),
and [the policy index is at most the bin's terminal threshold index](hyp:hj), then
[that policy threshold lies between the bin's baseline endpoints, inclusively](goal). -/
lemma policy_level_bin_bounds (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (x : X) (k j : ℕ)
    (hk : k ≤ L.K) (hj : j ≤ L.l k + 1) :
    L.pLev k x ≤ L.qLev k j x ∧ L.qLev k j x ≤ L.pLev (k+1) x := by
  rw [hL.2.1 x k j hk hj]
  by_cases hz : j = 0
  · rw [if_pos hz]
    exact ⟨le_rfl, canonical_baseline_levels_monotone M q L hL x k (k+1) (by omega) (by omega)⟩
  rw [if_neg hz]
  by_cases hji : j ≤ L.l k
  · rw [if_pos hji]
    have hidx : j - 1 < (policyLevelsAt M.prop q x k).length := by
      rw [hL.2.2.2.2.1 x k hk]; omega
    have hm : (policyLevelsAt M.prop q x k).getD (j-1) 0 ∈
        policyLevelsAt M.prop q x k := by
      rw [List.getD_eq_getElem _ _ hidx]
      exact List.getElem_mem hidx
    have hb := policyLevelsAt_mem_bounds M.prop q x k hm
    rw [← hL.1 x k (by omega), ← hL.1 x (k+1) (by omega)] at hb
    exact hb
  · rw [if_neg hji]
    exact ⟨canonical_baseline_levels_monotone M q L hL x k (k+1) (by omega) (by omega), le_rfl⟩

-- @node: interior_policy_level_exists
/-- If [the baseline and policy levels obey the common ordering and class
structure](hyp:hL), [the bin precedes the final baseline level](hyp:hk), and
[an instrument's policy propensity is at least the lower baseline endpoint and
strictly below the upper endpoint](hyp:hz), then [that propensity equals one of
the bin's policy levels with index from one through its number of policy classes](goal). -/
lemma interior_policy_level_exists (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (x : X) (k : ℕ) (hk : k < L.K)
    (z : Z) (hz : q z x ∈ Ico (L.pLev k x) (L.pLev (k+1) x)) :
    ∃ i, 1 ≤ i ∧ i ≤ L.l k ∧ q z x = L.qLev k i x := by
  have hm : q z x ∈ policyLevelsAt M.prop q x k := by
    simp only [policyLevelsAt, Finset.mem_sort, Finset.mem_filter,
      Finset.mem_image, Finset.mem_univ, true_and, hL.2.2.2.1 x, if_pos hk]
    rw [← hL.1 x k (by omega), ← hL.1 x (k+1) (by omega)]
    exact ⟨⟨z, rfl⟩, hz⟩
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hm
  have hil : i + 1 ≤ L.l k := by
    rw [hL.2.2.2.2.1 x k hk.le] at hi; omega
  refine ⟨i + 1, by omega, hil, ?_⟩
  rw [hL.2.1 x k (i+1) hk.le (by omega), if_neg (by omega), if_pos hil,
    Nat.add_sub_cancel, List.getD_eq_getElem _ _ hi]
  exact he.symm

-- @node: no_policy_level_between_adjacent
/-- If [the baseline and policy levels obey the common ordering and class
structure](hyp:hL), [the bin precedes the final baseline level](hyp:hk),
[the slice index is at least one](hyp:hj0), and [it is at most the bin's terminal
threshold index](hyp:hj), then [no instrument's policy propensity lies strictly
between the two policy thresholds bounding that slice](goal). -/
lemma no_policy_level_between_adjacent (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (x : X) (k j : ℕ)
    (hk : k < L.K) (hj0 : 1 ≤ j) (hj : j ≤ L.l k + 1) (z : Z) :
    q z x ∉ Ioo (L.qLev k (j-1) x) (L.qLev k j x) := by
  intro hz
  have hlo := policy_level_bin_bounds M q L hL x k (j-1) hk.le (by omega)
  have hhi := policy_level_bin_bounds M q L hL x k j hk.le hj
  obtain ⟨i, hi0, hi, he⟩ := interior_policy_level_exists M q L hL x k hk z
    ⟨(hlo.1.trans hz.1.le), hz.2.trans_le hhi.2⟩
  have hs := hL.2.2.2.2.2.2.2.2.1
  by_cases hij : i < j
  · have hj1 : 1 ≤ j - 1 := by omega
    have hjl : j - 1 ≤ L.l k := by omega
    have hle : L.qLev k i x ≤ L.qLev k (j-1) x := by
      rcases (show i ≤ j - 1 by omega).eq_or_lt with heq | hlt
      · rw [heq]
      · exact (hs x k i (j-1) hk.le hi0 hlt hjl).le
    rw [he] at hz
    exact (not_le_of_gt hz.1) hle
  · have hji : j ≤ i := by omega
    have hle : L.qLev k j x ≤ L.qLev k i x := by
      rcases hji.eq_or_lt with heq | hlt
      · rw [heq]
      · exact (hs x k j i hk.le hj0 hlt hi).le
    rw [he] at hz
    exact (not_le_of_gt hz.2) hle

-- @node: finite_policy_weight_constant_on_slice
/-- If [the baseline and policy levels obey the common ordering and class
structure](hyp:hL), [the bin precedes the final baseline level](hyp:hk),
[the slice index is at least one](hyp:hj0), and [it is at most the bin's terminal
threshold index](hyp:hj), then for [a first resistance rank strictly inside that
policy slice](hyp:hs) and [a second rank strictly inside the same slice](hyp:ht),
[the policy weights at the two ranks are equal](goal). -/
lemma finite_policy_weight_constant_on_slice (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (x : X) (k j : ℕ)
    (hk : k < L.K) (hj0 : 1 ≤ j) (hj : j ≤ L.l k + 1)
    (s t : ℝ) (hs : s ∈ Ioo (L.qLev k (j-1) x) (L.qLev k j x))
    (ht : t ∈ Ioo (L.qLev k (j-1) x) (L.qLev k j x)) :
    policyWeight M q x s = policyWeight M q x t := by
  have hlo := policy_level_bin_bounds M q L hL x k (j-1) hk.le (by omega)
  have hhi := policy_level_bin_bounds M q L hL x k j hk.le hj
  have hs' : s ∈ Ioo (L.pLev k x) (L.pLev (k+1) x) :=
    ⟨hlo.1.trans_lt hs.1, hs.2.trans_le hhi.2⟩
  have ht' : t ∈ Ioo (L.pLev k x) (L.pLev (k+1) x) :=
    ⟨hlo.1.trans_lt ht.1, ht.2.trans_le hhi.2⟩
  rw [finite_policy_weight_sum, finite_policy_weight_sum]
  apply Finset.sum_congr rfl
  intro z _
  have he : (s ≤ M.prop z x) ↔ (t ≤ M.prop z x) :=
    (interior_baseline_superlevel_membership M q L hL x k hk s hs' z).trans
      (interior_baseline_superlevel_membership M q L hL x k hk t ht' z).symm
  have hq : (s ≤ q z x) ↔ (t ≤ q z x) := by
    have hn := no_policy_level_between_adjacent M q L hL x k j hk hj0 hj z
    constructor
    · intro hsq
      by_contra htq
      exact hn ⟨hs.1.trans_le hsq, (lt_of_not_ge htq).trans ht.2⟩
    · intro htq
      by_contra hsq
      exact hn ⟨ht.1.trans_le htq, (lt_of_not_ge hsq).trans hs.2⟩
  simp only [he, hq]

-- @node: finite_policy_level_cover
/-- If [the baseline and policy levels obey the common ordering and class
structure](hyp:hL), then [every instrument belongs to a policy equality class
with a positive valid class index in some bin at or below the final baseline
index; its policy propensity is at least that bin's lower baseline endpoint and,
if the bin precedes the final baseline level, strictly below its upper endpoint](goal). -/
lemma finite_policy_level_cover (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (x : X) (z : Z) :
    ∃ i ≤ L.K, ∃ j, 1 ≤ j ∧ j ≤ L.l i ∧ z ∈ L.T i j ∧
      L.pLev i x ≤ q z x ∧ (i < L.K → q z x < L.pLev (i+1) x) := by
  let P := fun i => L.pLev i x ≤ q z x
  let i := Nat.findGreatest P L.K
  have hi : i ≤ L.K := Nat.findGreatest_le L.K
  have hzero : P 0 := by
    dsimp only [P]
    rw [hL.1 x 0 (by omega)]
    simpa [pLevel] using
      (hL.2.2.2.2.2.2.2.2.2.1 z x).2.1
  have hlo : L.pLev i x ≤ q z x := Nat.findGreatest_spec (Nat.zero_le _) hzero
  have hhi (hiK : i < L.K) : q z x < L.pLev (i+1) x := by
    exact lt_of_not_ge (Nat.findGreatest_is_greatest (show i < i+1 by omega) (by omega))
  have hm : q z x ∈ policyLevelsAt M.prop q x i := by
    simp only [policyLevelsAt, Finset.mem_sort, Finset.mem_filter,
      Finset.mem_image, Finset.mem_univ, true_and, hL.2.2.2.1 x]
    rw [← hL.1 x i (by omega), ← hL.1 x (i+1) (by omega)]
    refine ⟨⟨z, rfl⟩, hlo, ?_⟩
    split_ifs with hiK
    · exact hhi hiK
    · have he : i = L.K := by omega
      rw [he, hL.1 x (L.K+1) le_rfl]
      simpa [pLevel, hL.2.2.2.1 x] using (hL.2.2.2.2.2.2.2.2.2.1 z x).2.2
  obtain ⟨r, hr, he⟩ := List.mem_iff_getElem.mp hm
  have hrj : r+1 ≤ L.l i := by rw [hL.2.2.2.2.1 x i hi] at hr; omega
  have heq : q z x = L.qLev i (r+1) x := by
    rw [hL.2.1 x i (r+1) hi (by omega), if_neg (by omega), if_pos hrj,
      Nat.add_sub_cancel, List.getD_eq_getElem _ _ hr]
    exact he.symm
  exact ⟨i, hi, r+1, by omega, hrj,
    (hL.2.2.2.2.2.2.1 x i (r+1) z hi (by omega) hrj).mpr heq, hlo, hhi⟩

-- @node: higher_policy_superlevel_membership
/-- If [the baseline and policy levels obey the common ordering and class
structure](hyp:hL) and [the bin precedes the final baseline level](hyp:hk), then
[an instrument belongs to the union of higher-bin policy classes exactly when
its policy propensity is at least the bin's upper baseline endpoint](goal). -/
lemma higher_policy_superlevel_membership (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (x : X) (k : ℕ) (hk : k < L.K) (z : Z) :
    z ∈ higherPolicy L k ↔ L.pLev (k+1) x ≤ q z x := by
  constructor
  · intro hz
    obtain ⟨i, hi, hzi⟩ := Finset.mem_biUnion.mp hz
    have hiK : i ≤ L.K := by have := Finset.mem_range.mp hi; omega
    by_cases hki : k < i
    · rw [if_pos hki] at hzi
      obtain ⟨j, hj, hzj⟩ := Finset.mem_biUnion.mp hzi
      have hjl : j ≤ L.l i := by have := Finset.mem_range.mp hj; omega
      have hj0 : 1 ≤ j := by
        by_contra hn
        have he : j = 0 := by omega
        rw [he, (hL.2.2.1 i hiK).1] at hzj
        exact Finset.notMem_empty z hzj
      have he := (hL.2.2.2.2.2.2.1 x i j z hiK hj0 hjl).mp hzj
      rw [he]
      exact (canonical_baseline_levels_monotone M q L hL x (k+1) i (by omega) (by omega)).trans
        (policy_level_bin_bounds M q L hL x i j hiK (by omega)).1
    · simp only [if_neg hki, Finset.notMem_empty] at hzi
  · intro hq
    obtain ⟨i, hi, j, hj0, hj, hzj, hlo, hhi⟩ := finite_policy_level_cover M q L hL x z
    have hki : k < i := by
      by_contra hn
      have hik : i ≤ k := by omega
      have hiK : i < L.K := hik.trans_lt hk
      have hle := canonical_baseline_levels_monotone M q L hL x (i+1) (k+1)
        (by omega) (by omega)
      exact (not_lt_of_ge hq) ((hhi hiK).trans_le hle)
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_range.mpr (by omega), ?_⟩
    rw [if_pos hki]
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr (by omega), hzj⟩

-- @node: interior_policy_level_strict_upper
/-- If [the baseline and policy levels obey the common ordering and class
structure](hyp:hL), [the bin precedes the final baseline level](hyp:hk),
[the policy-class index is at least one](hyp:hj0), and [it is no larger than the
number of policy classes in the bin](hyp:hj), then [that policy level is strictly
below the bin's upper baseline endpoint](goal). -/
lemma interior_policy_level_strict_upper (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (x : X) (k j : ℕ)
    (hk : k < L.K) (hj0 : 1 ≤ j) (hj : j ≤ L.l k) :
    L.qLev k j x < L.pLev (k+1) x := by
  have hidx : j-1 < (policyLevelsAt M.prop q x k).length := by
    rw [hL.2.2.2.2.1 x k hk.le]; omega
  have hm : L.qLev k j x ∈ policyLevelsAt M.prop q x k := by
    rw [hL.2.1 x k j hk.le (by omega), if_neg (by omega), if_pos hj,
      List.getD_eq_getElem _ _ hidx]
    exact List.getElem_mem hidx
  simp only [policyLevelsAt, Finset.mem_sort, Finset.mem_filter,
    hL.2.2.2.1 x, if_pos hk] at hm
  rw [hL.1 x (k+1) (by omega)]
  exact hm.2.2

-- @node: interior_policy_union_membership
/-- If [the baseline and policy levels obey the common ordering and class
structure](hyp:hL), [the bin precedes the final baseline level](hyp:hk),
[the slice index is at least one](hyp:hj0), [it is at most the bin's terminal
threshold index](hyp:hj), and [the resistance rank lies strictly inside that
policy slice](hyp:hu), then [an instrument belongs to the current-bin union of
policy classes at or above the slice index exactly when its policy propensity
is at least that rank and strictly below the upper baseline endpoint](goal). -/
lemma interior_policy_union_membership (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (x : X) (k j : ℕ)
    (hk : k < L.K) (hj0 : 1 ≤ j) (hj : j ≤ L.l k + 1)
    (u : ℝ) (hu : u ∈ Ioo (L.qLev k (j-1) x) (L.qLev k j x)) (z : Z) :
    z ∈ policyUnion L k j ↔ u ≤ q z x ∧ q z x < L.pLev (k+1) x := by
  have hs := hL.2.2.2.2.2.2.2.2.1
  constructor
  · intro hz
    obtain ⟨i, hi, hzi⟩ := Finset.mem_biUnion.mp hz
    have hil : i ≤ L.l k := by have := Finset.mem_range.mp hi; omega
    by_cases hji : j ≤ i
    · rw [if_pos hji] at hzi
      have hi0 : 1 ≤ i := hj0.trans hji
      have he := (hL.2.2.2.2.2.2.1 x k i z hk.le hi0 hil).mp hzi
      rw [he]
      have hle : L.qLev k j x ≤ L.qLev k i x := by
        rcases hji.eq_or_lt with heq | hlt
        · rw [heq]
        · exact (hs x k j i hk.le hj0 hlt hil).le
      exact ⟨hu.2.le.trans hle, interior_policy_level_strict_upper M q L hL x k i hk hi0 hil⟩
    · simp only [if_neg hji, Finset.notMem_empty] at hzi
  · intro hz
    have hlo := policy_level_bin_bounds M q L hL x k (j-1) hk.le (by omega)
    obtain ⟨i, hi0, hi, he⟩ := interior_policy_level_exists M q L hL x k hk z
      ⟨hlo.1.trans (hu.1.le.trans hz.1), hz.2⟩
    have hji : j ≤ i := by
      by_contra hn
      have hij : i < j := by omega
      have hj1 : 1 ≤ j-1 := by omega
      have hle : L.qLev k i x ≤ L.qLev k (j-1) x := by
        rcases (show i ≤ j-1 by omega).eq_or_lt with heq | hlt
        · rw [heq]
        · exact (hs x k i (j-1) hk.le hi0 hlt (by omega)).le
      rw [he] at hz
      exact (not_le_of_gt hu.1) (hz.1.trans hle)
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_range.mpr (by omega), ?_⟩
    rw [if_pos hji]
    exact (hL.2.2.2.2.2.2.1 x k i z hk.le hi0 hi).mpr he

-- @node: finite_policy_weight_slice_value
/-- If [the baseline and policy levels obey the common ordering and class
structure](hyp:hL), [the bin precedes the final baseline level](hyp:hk),
[the slice index is at least one](hyp:hj0), [it is at most the bin's terminal
threshold index](hyp:hj), and [the resistance rank lies strictly inside that
policy slice](hyp:hu), then [the policy weight equals the full-gap coefficient
plus that slice's additional current-bin coefficient](goal). -/
lemma finite_policy_weight_slice_value (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (x : X) (k j : ℕ)
    (hk : k < L.K) (hj0 : 1 ≤ j) (hj : j ≤ L.l k + 1)
    (u : ℝ) (hu : u ∈ Ioo (L.qLev k (j-1) x) (L.qLev k j x)) :
    policyWeight M q x u = gammaFull M L k x + gamma M L k j x := by
  have hlo := policy_level_bin_bounds M q L hL x k (j-1) hk.le (by omega)
  have hhi := policy_level_bin_bounds M q L hL x k j hk.le hj
  have hu' : u ∈ Ioo (L.pLev k x) (L.pLev (k+1) x) :=
    ⟨hlo.1.trans_lt hu.1, hu.2.trans_le hhi.2⟩
  have hpolicy (z : Z) :
      (if u ≤ q z x then (1 : ℝ) else 0) =
      (if z ∈ higherPolicy L k then 1 else 0) +
        (if z ∈ policyUnion L k j then 1 else 0) := by
    have hh := higher_policy_superlevel_membership M q L hL x k hk z
    have hc := interior_policy_union_membership M q L hL x k j hk hj0 hj u hu z
    by_cases hq : L.pLev (k+1) x ≤ q z x
    · have hh' := hh.mpr hq
      have hc' : z ∉ policyUnion L k j := fun hz => not_lt_of_ge hq (hc.mp hz).2
      rw [if_pos hh', if_neg hc', if_pos (hu'.2.le.trans hq)]
      norm_num
    · have hh' : z ∉ higherPolicy L k := fun hz => hq (hh.mp hz)
      rw [if_neg hh']
      by_cases huq : u ≤ q z x
      · rw [if_pos huq, if_pos (hc.mpr ⟨huq, lt_of_not_ge hq⟩)]
        norm_num
      · rw [if_neg huq, if_neg (fun hz => huq (hc.mp hz).1)]
        norm_num
  have hbase (z : Z) := interior_baseline_superlevel_membership M q L hL x k hk u hu' z
  rw [finite_policy_weight_sum]
  simp only [hpolicy, hbase, mul_sub, mul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_mem, Finset.inter_univ, Finset.univ_inter,
    gammaFull, gamma]
  ring

-- @node: normalized_policy_weight_slice_value
/-- If [the baseline and policy levels obey the common ordering and class
structure](hyp:hL), [the bin precedes the final baseline level](hyp:hk),
[the slice index is at least one](hyp:hj0), [it is at most the bin's terminal
threshold index](hyp:hj), and [the normalized rank lies strictly between the
slice's normalized partition points](hyp:ht), then [the policy weight at the
corresponding resistance rank equals the full-gap coefficient plus the slice's
additional current-bin coefficient](goal). -/
lemma normalized_policy_weight_slice_value (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (x : X) (k j : ℕ)
    (hk : k < L.K) (hj0 : 1 ≤ j) (hj : j ≤ L.l k + 1)
    (t : ℝ) (ht : t ∈ Ioo (kappa L k (j-1) x) (kappa L k j x)) :
    policyWeight M q x (L.pLev k x + (L.pLev (k+1) x - L.pLev k x) * t) =
      gammaFull M L k x + gamma M L k j x := by
  have hw : 0 < L.pLev (k+1) x - L.pLev k x :=
    sub_pos.mpr (hL.2.2.2.2.2.2.2.1 x k (k+1) (by omega) (by omega))
  apply finite_policy_weight_slice_value M q L hL x k j hk hj0 hj
  change (L.qLev k (j-1) x - L.pLev k x) / (L.pLev (k+1) x - L.pLev k x) < t ∧
    t < (L.qLev k j x - L.pLev k x) / (L.pLev (k+1) x - L.pLev k x) at ht
  have hlo := (div_lt_iff₀ hw).mp ht.1
  have hhi := (lt_div_iff₀ hw).mp ht.2
  constructor <;> nlinarith

-- @node: normalized_policy_slice_integral
/-- If [the baseline and policy levels obey the common ordering and class
structure](hyp:hL), [the bin precedes the final baseline level](hyp:hk),
[the slice index is at least one](hyp:hj0), and [it is at most the bin's terminal
threshold index](hyp:hj), then [the integral of any function times the policy
weight over that normalized slice equals the sum of the full-gap and current-bin
coefficients times the integral of the function over the same slice](goal). -/
lemma normalized_policy_slice_integral (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (x : X) (k j : ℕ)
    (hk : k < L.K) (hj0 : 1 ≤ j) (hj : j ≤ L.l k + 1) (Q : ℝ → ℝ) :
    (∫ t in Ioo (kappa L k (j-1) x) (kappa L k j x),
      Q t * policyWeight M q x (L.pLev k x + (L.pLev (k+1) x - L.pLev k x) * t)) =
      (gammaFull M L k x + gamma M L k j x) *
        ∫ t in Ioo (kappa L k (j-1) x) (kappa L k j x), Q t := by
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  dsimp only
  rw [normalized_policy_weight_slice_value M q L hL x k j hk hj0 hj t ht, mul_comm]

end Papers.TbsPrteOptimalTransport
