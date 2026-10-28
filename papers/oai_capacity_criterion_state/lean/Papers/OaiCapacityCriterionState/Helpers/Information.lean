module

public import Papers.OaiCapacityCriterionState.Helpers.Broadcast
public import Papers.OaiCapacityCriterionState.Helpers.PosteriorLaws
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # Comparing total variation with quadratic information

The finite-level quadratic statistic stays uniformly positive exactly when the
limiting total variation does. These comparisons connect the broadcast experiment
to the moment estimates used in the capacity argument.
-/

@[expose] public section

open Filter Topology
open scoped BigOperators

namespace OaiCapacityCriterionState

-- @node: quadStat_eq_centered_sq
/-- If [the four coordinates of a real vector sum to one](hyp:hsum), [its quadratic
statistic equals four times the sum of squared deviations from one quarter](goal). -/
lemma quadStat_eq_centered_sq (p : Fin 4 → ℝ) (hsum : ∑ i, p i = 1) :
    quadStat p = 4 * ∑ i : Fin 4, (p i - 1 / 4) ^ 2 := by
  have hs : p 3 = 1 - p 0 - p 1 - p 2 := by
    simp [Fin.sum_univ_succ] at hsum
    linarith
  simp [quadStat, postCoords, coordMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, hs]
  ring

-- @node: tvToUnif_sq_le_quadStat
/-- If [the four coordinates of a real vector sum to one](hyp:hsum), [the square of
its total variation distance from uniform is at most its quadratic statistic](goal). -/
lemma tvToUnif_sq_le_quadStat (p : Fin 4 → ℝ) (hsum : ∑ i, p i = 1) :
    tvToUnif p ^ 2 ≤ quadStat p := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 4))
    (fun _ => (1 : ℝ)) (fun i => |p i - 1 / 4|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, sq_abs] at h
  rw [quadStat_eq_centered_sq p hsum]
  unfold tvToUnif
  nlinarith

-- @node: quadStat_le_eight_tvToUnif
/-- If [a four-state vector is a probability distribution](hyp:hp), [its quadratic
statistic is at most eight times its total variation distance from uniform](goal). -/
lemma quadStat_le_eight_tvToUnif (p : Fin 4 → ℝ)
    (hp : p ∈ stdSimplex ℝ (Fin 4)) : quadStat p ≤ 8 * tvToUnif p := by
  have hterm (i : Fin 4) : (p i - 1 / 4) ^ 2 ≤ |p i - 1 / 4| := by
    have hpi : p i ≤ 1 := by
      have := Finset.single_le_sum (s := Finset.univ) (f := p)
        (fun j _ => hp.1 j) (Finset.mem_univ i)
      simpa [hp.2] using this
    have habs : |p i - 1 / 4| ≤ 1 := abs_le.mpr ⟨by linarith [hp.1 i], by linarith⟩
    have := mul_nonneg (abs_nonneg (p i - 1 / 4)) (sub_nonneg.mpr habs)
    nlinarith [sq_abs (p i - 1 / 4)]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm i)
  rw [quadStat_eq_centered_sq p hp.2]
  unfold tvToUnif
  linarith

-- @node: rootPosterior_mem_simplex
/-- If [the channel parameter lies between zero and one, inclusive](hyp:hlam),
[the root posterior given any observed assignment at any level is a probability
distribution on the four states](goal). -/
lemma rootPosterior_mem_simplex {B : ℕ} (T : BoundedTree B) (lam : ℝ)
    (hlam : lam ∈ Set.Icc 0 1) (n : ℕ) (obs : T.level n → Fin 4) :
    rootPosterior T lam n obs ∈ stdSimplex ℝ (Fin 4) := by
  classical
  unfold rootPosterior
  split_ifs with hpos
  · constructor
    · intro i
      exact div_nonneg (levelJoint_nonneg T lam hlam n i obs) hpos.le
    · rw [← Finset.sum_div]
      exact div_self (ne_of_gt hpos)
  · constructor
    · intro i
      norm_num [unifVec]
    · norm_num [unifVec]

-- @node: levelQuadInfo
/-- For [a bounded tree](hyp:T), [a channel parameter](hyp:lam), and [a depth](hyp:n),
[the level's quadratic information](goal) is the expected quadratic statistic of
the root posterior, weighting each observed level assignment by its marginal probability. -/
noncomputable def levelQuadInfo {B : ℕ} (T : BoundedTree B) (lam : ℝ) (n : ℕ) : ℝ :=
  ∑ obs : T.level n → Fin 4,
    levelMarginal T lam n obs * quadStat (rootPosterior T lam n obs)

-- @node: levelInfo_sq_le_levelQuadInfo
/-- If [the channel parameter lies strictly between zero and one](hyp:hlam),
[the square of the expected total variation distance of the root posterior from
uniform at any level is at most that level's quadratic information](goal). -/
lemma levelInfo_sq_le_levelQuadInfo {B : ℕ} (T : BoundedTree B) (lam : ℝ)
    (hlam : MainLambda lam) (n : ℕ) : levelInfo T lam n ^ 2 ≤ levelQuadInfo T lam n := by
  classical
  have hlam' : lam ∈ Set.Icc 0 1 := ⟨hlam.1.le, hlam.2.le⟩
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun obs => levelMarginal T lam n obs * tvToUnif (rootPosterior T lam n obs))
    (f := fun obs => levelMarginal T lam n obs)
    (g := fun obs => levelMarginal T lam n obs * tvToUnif (rootPosterior T lam n obs) ^ 2)
    (fun obs _ => levelMarginal_nonneg T lam hlam' n obs)
    (fun obs _ => mul_nonneg (levelMarginal_nonneg T lam hlam' n obs) (sq_nonneg _))
    (fun obs _ => by ring_nf; exact le_rfl)
  rw [levelMarginal_sum T lam hlam' n, one_mul] at h
  exact h.trans (Finset.sum_le_sum fun obs _ =>
    mul_le_mul_of_nonneg_left
      (tvToUnif_sq_le_quadStat _ (rootPosterior_mem_simplex T lam hlam' n obs).2)
      (levelMarginal_nonneg T lam hlam' n obs))

-- @node: levelQuadInfo_le_eight_levelInfo
/-- If [the channel parameter lies strictly between zero and one](hyp:hlam),
[quadratic information at any level is at most eight times the expected total
variation distance of the root posterior from uniform at that level](goal). -/
lemma levelQuadInfo_le_eight_levelInfo {B : ℕ} (T : BoundedTree B) (lam : ℝ)
    (hlam : MainLambda lam) (n : ℕ) : levelQuadInfo T lam n ≤ 8 * levelInfo T lam n := by
  classical
  have hlam' : lam ∈ Set.Icc 0 1 := ⟨hlam.1.le, hlam.2.le⟩
  unfold levelQuadInfo levelInfo
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro obs _
  calc
    _ ≤ levelMarginal T lam n obs * (8 * tvToUnif (rootPosterior T lam n obs)) :=
      mul_le_mul_of_nonneg_left
        (quadStat_le_eight_tvToUnif _ (rootPosterior_mem_simplex T lam hlam' n obs))
        (levelMarginal_nonneg T lam hlam' n obs)
    _ = _ := by ring

-- @node: limitInfo_le_levelInfo
/-- If [the channel parameter lies strictly between zero and one](hyp:hlam),
[the limiting expected total variation distance of the root posterior from uniform
is at most its value at every finite level](goal). -/
lemma limitInfo_le_levelInfo {B : ℕ} (T : BoundedTree B) (lam : ℝ)
    (hlam : MainLambda lam) (n : ℕ) : limitInfo T lam ≤ levelInfo T lam n := by
  exact le_of_tendsto (levelInfo_tendsto T lam hlam)
    (eventually_atTop.2 ⟨n, fun m hm => levelInfo_antitone T lam hlam hm⟩)

-- @node: reconstructs_iff_levelQuadInfo_uniform_pos
/-- If [the channel parameter lies strictly between zero and one](hyp:hlam),
[the limiting expected total variation distance from uniform is positive exactly
when a single positive constant bounds quadratic information from below at every level](goal). -/
theorem reconstructs_iff_levelQuadInfo_uniform_pos {B : ℕ} (T : BoundedTree B)
    (lam : ℝ) (hlam : MainLambda lam) :
    0 < limitInfo T lam ↔ ∃ c : ℝ, 0 < c ∧ ∀ n, c ≤ levelQuadInfo T lam n := by
  constructor
  · intro hpos
    refine ⟨limitInfo T lam ^ 2, sq_pos_of_pos hpos, fun n => ?_⟩
    exact (pow_le_pow_left₀ hpos.le (limitInfo_le_levelInfo T lam hlam n) 2).trans
      (levelInfo_sq_le_levelQuadInfo T lam hlam n)
  · rintro ⟨c, hc, hbound⟩
    have hlevel (n : ℕ) : c / 8 ≤ levelInfo T lam n := by
      have := (hbound n).trans (levelQuadInfo_le_eight_levelInfo T lam hlam n)
      linarith
    have hlim : c / 8 ≤ limitInfo T lam :=
      ge_of_tendsto (levelInfo_tendsto T lam hlam) (Eventually.of_forall hlevel)
    exact (div_pos hc (by norm_num)).trans_le hlim

-- @node: levelMarginal_mul_rootPosterior
/-- If [the channel parameter lies between zero and one, inclusive](hyp:hlam),
[the marginal probability of a level assignment times the posterior probability
of a root state equals their joint probability](goal). -/
lemma levelMarginal_mul_rootPosterior {B : ℕ} (T : BoundedTree B) (lam : ℝ)
    (hlam : lam ∈ Set.Icc 0 1) (n : ℕ) (obs : T.level n → Fin 4) (i : Fin 4) :
    levelMarginal T lam n obs * rootPosterior T lam n obs i =
      levelJoint T lam n i obs := by
  classical
  by_cases hpos : 0 < levelMarginal T lam n obs
  · simp only [rootPosterior, if_pos hpos]
    exact mul_div_cancel₀ _ (ne_of_gt hpos)
  · have hm : levelMarginal T lam n obs = 0 :=
      le_antisymm (le_of_not_gt hpos) (levelMarginal_nonneg T lam hlam n obs)
    have hj := Finset.single_le_sum (s := Finset.univ)
      (fun j _ => levelJoint_nonneg T lam hlam n j obs) (Finset.mem_univ i)
    change levelJoint T lam n i obs ≤ levelMarginal T lam n obs at hj
    have hz : levelJoint T lam n i obs = 0 :=
      le_antisymm (hj.trans_eq hm) (levelJoint_nonneg T lam hlam n i obs)
    rw [hm, hz, zero_mul]

-- @node: rootPosterior_centered_step
/-- If [the channel parameter lies between zero and one, inclusive](hyp:hlam),
[the marginal probability of a next-level assignment times its root posterior
deviation from one quarter equals the sum of the current-level posterior deviations,
weighted by the current assignment probabilities and transition probabilities to
that next-level assignment](goal). -/
lemma rootPosterior_centered_step {B : ℕ} (T : BoundedTree B) (lam : ℝ)
    (hlam : lam ∈ Set.Icc 0 1) (n : ℕ) (next : T.level (n + 1) → Fin 4)
    (i : Fin 4) :
    levelMarginal T lam (n + 1) next * (rootPosterior T lam (n + 1) next i - 1 / 4) =
      ∑ obs : T.level n → Fin 4,
        (levelMarginal T lam n obs * levelTransition T lam n obs next) *
          (rootPosterior T lam n obs i - 1 / 4) := by
  classical
  rw [mul_sub, levelMarginal_mul_rootPosterior T lam hlam]
  rw [levelJoint_step, levelMarginal_step, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro obs _
  rw [← levelMarginal_mul_rootPosterior T lam hlam n obs i]
  ring

-- @node: rootPosterior_centered_sq_step
/-- If [the channel parameter lies between zero and one, inclusive](hyp:hlam),
[the marginal probability of a next-level assignment times its squared root posterior
deviation from one quarter is at most the sum of the current-level squared deviations,
weighted by current assignment probabilities and transition probabilities to that
next-level assignment](goal). -/
lemma rootPosterior_centered_sq_step {B : ℕ} (T : BoundedTree B) (lam : ℝ)
    (hlam : lam ∈ Set.Icc 0 1) (n : ℕ) (next : T.level (n + 1) → Fin 4)
    (i : Fin 4) :
    levelMarginal T lam (n + 1) next * (rootPosterior T lam (n + 1) next i - 1 / 4) ^ 2 ≤
      ∑ obs : T.level n → Fin 4,
        (levelMarginal T lam n obs * levelTransition T lam n obs next) *
          (rootPosterior T lam n obs i - 1 / 4) ^ 2 := by
  classical
  let w := fun obs : T.level n → Fin 4 =>
    levelMarginal T lam n obs * levelTransition T lam n obs next
  let x := fun obs : T.level n → Fin 4 => rootPosterior T lam n obs i - 1 / 4
  have hw (obs) : 0 ≤ w obs :=
    mul_nonneg (levelMarginal_nonneg T lam hlam n obs)
      (levelTransition_nonneg T lam hlam n obs next)
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun obs => w obs * x obs) (f := w) (g := fun obs => w obs * x obs ^ 2)
    (fun obs _ => hw obs) (fun obs _ => mul_nonneg (hw obs) (sq_nonneg _))
    (fun obs _ => by ring_nf; exact le_rfl)
  have hsum : ∑ obs, w obs = levelMarginal T lam (n + 1) next :=
    (levelMarginal_step T lam n next).symm
  have hcenter : ∑ obs, w obs * x obs =
      levelMarginal T lam (n + 1) next * (rootPosterior T lam (n + 1) next i - 1 / 4) :=
    (rootPosterior_centered_step T lam hlam n next i).symm
  rw [hsum, hcenter, mul_pow] at hcs
  by_cases hpos : 0 < levelMarginal T lam (n + 1) next
  · apply (mul_le_mul_iff_right₀ hpos).mp
    nlinarith [hcs]
  · have hz : levelMarginal T lam (n + 1) next = 0 :=
      le_antisymm (le_of_not_gt hpos) (levelMarginal_nonneg T lam hlam (n + 1) next)
    rw [hz, zero_mul]
    exact Finset.sum_nonneg fun obs _ => mul_nonneg (hw obs) (sq_nonneg _)

-- @node: levelQuadInfo_succ_le
/-- If [the channel parameter lies strictly between zero and one](hyp:hlam),
[quadratic information at the next level is at most quadratic information at the
current level](goal). -/
lemma levelQuadInfo_succ_le {B : ℕ} (T : BoundedTree B) (lam : ℝ)
    (hlam : MainLambda lam) (n : ℕ) :
    levelQuadInfo T lam (n + 1) ≤ levelQuadInfo T lam n := by
  classical
  have ht : lam ∈ Set.Icc 0 1 := ⟨hlam.1.le, hlam.2.le⟩
  have hcenter (k : ℕ) : levelQuadInfo T lam k =
      4 * ∑ obs : T.level k → Fin 4, ∑ i : Fin 4,
        levelMarginal T lam k obs * (rootPosterior T lam k obs i - 1 / 4) ^ 2 := by
    unfold levelQuadInfo
    simp_rw [quadStat_eq_centered_sq _ (rootPosterior_mem_simplex T lam ht k _).2]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro obs _
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hcenter (n + 1), hcenter n]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ ≤ ∑ next : T.level (n + 1) → Fin 4, ∑ i : Fin 4,
        ∑ obs : T.level n → Fin 4,
          (levelMarginal T lam n obs * levelTransition T lam n obs next) *
            (rootPosterior T lam n obs i - 1 / 4) ^ 2 := by
      apply Finset.sum_le_sum
      intro next _
      exact Finset.sum_le_sum fun i _ => rootPosterior_centered_sq_step T lam ht n next i
    _ = _ := by
      conv_lhs =>
        enter [2, next]
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro obs _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      conv_lhs =>
        enter [2, next]
        rw [mul_right_comm]
      rw [← Finset.mul_sum, levelTransition_sum, mul_one]

-- @node: levelQuadInfo_antitone
/-- If [the channel parameter lies strictly between zero and one](hyp:hlam),
[quadratic information is nonincreasing as the observed level moves away from the root](goal). -/
lemma levelQuadInfo_antitone {B : ℕ} (T : BoundedTree B) (lam : ℝ)
    (hlam : MainLambda lam) : Antitone (levelQuadInfo T lam) :=
  antitone_nat_of_succ_le (levelQuadInfo_succ_le T lam hlam)

-- @node: levelQuadInfo_mem_Icc
/-- If [the channel parameter lies strictly between zero and one](hyp:hlam),
[quadratic information at every level lies between zero and three, inclusive](goal). -/
lemma levelQuadInfo_mem_Icc {B : ℕ} (T : BoundedTree B) (lam : ℝ)
    (hlam : MainLambda lam) (n : ℕ) : levelQuadInfo T lam n ∈ Set.Icc 0 3 := by
  classical
  have ht : lam ∈ Set.Icc 0 1 := ⟨hlam.1.le, hlam.2.le⟩
  have hp (obs : T.level n → Fin 4) :=
    quadStat_mem_Icc _ (rootPosterior_mem_simplex T lam ht n obs)
  constructor
  · exact Finset.sum_nonneg fun obs _ =>
      mul_nonneg (levelMarginal_nonneg T lam ht n obs) (hp obs).1
  · calc
      _ ≤ ∑ obs : T.level n → Fin 4, levelMarginal T lam n obs * 3 :=
        Finset.sum_le_sum fun obs _ => mul_le_mul_of_nonneg_left (hp obs).2
          (levelMarginal_nonneg T lam ht n obs)
      _ = 3 := by rw [← Finset.sum_mul, levelMarginal_sum T lam ht n]; ring

-- @node: limitQuadInfo
/-- For [a bounded tree](hyp:T) and [a channel parameter](hyp:lam), [limiting quadratic
information](goal) is the limit of the level quadratic information as depth tends to infinity. -/
noncomputable def limitQuadInfo {B : ℕ} (T : BoundedTree B) (lam : ℝ) : ℝ :=
  Filter.limUnder Filter.atTop (levelQuadInfo T lam)

-- @node: levelQuadInfo_tendsto
/-- If [the channel parameter lies strictly between zero and one](hyp:hlam),
[level quadratic information converges to limiting quadratic information as depth
tends to infinity](goal). -/
lemma levelQuadInfo_tendsto {B : ℕ} (T : BoundedTree B) (lam : ℝ)
    (hlam : MainLambda lam) :
    Tendsto (levelQuadInfo T lam) atTop (𝓝 (limitQuadInfo T lam)) := by
  have hb : BddBelow (Set.range (levelQuadInfo T lam)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (levelQuadInfo_mem_Icc T lam hlam n).1
  have hc := tendsto_atTop_ciInf (levelQuadInfo_antitone T lam hlam) hb
  unfold limitQuadInfo
  rw [hc.limUnder_eq]
  exact hc

-- @node: limitQuadInfo_mem_Icc
/-- If [the channel parameter lies strictly between zero and one](hyp:hlam),
[limiting quadratic information lies between zero and three, inclusive](goal). -/
lemma limitQuadInfo_mem_Icc {B : ℕ} (T : BoundedTree B) (lam : ℝ)
    (hlam : MainLambda lam) : limitQuadInfo T lam ∈ Set.Icc 0 3 :=
  isClosed_Icc.mem_of_tendsto (levelQuadInfo_tendsto T lam hlam)
    (Eventually.of_forall (levelQuadInfo_mem_Icc T lam hlam))

-- @node: limitQuadInfo_le_levelQuadInfo
/-- If [the channel parameter lies strictly between zero and one](hyp:hlam),
[limiting quadratic information is at most quadratic information at every finite level](goal). -/
lemma limitQuadInfo_le_levelQuadInfo {B : ℕ} (T : BoundedTree B) (lam : ℝ)
    (hlam : MainLambda lam) (n : ℕ) : limitQuadInfo T lam ≤ levelQuadInfo T lam n :=
  le_of_tendsto (levelQuadInfo_tendsto T lam hlam)
    (eventually_atTop.2 ⟨n, fun _ hm => levelQuadInfo_antitone T lam hlam hm⟩)

-- @node: limitInfo_sq_le_limitQuadInfo
/-- If [the channel parameter lies strictly between zero and one](hyp:hlam),
[the square of the limiting expected total variation distance from uniform is at
most limiting quadratic information](goal). -/
lemma limitInfo_sq_le_limitQuadInfo {B : ℕ} (T : BoundedTree B) (lam : ℝ)
    (hlam : MainLambda lam) : limitInfo T lam ^ 2 ≤ limitQuadInfo T lam :=
  le_of_tendsto_of_tendsto ((levelInfo_tendsto T lam hlam).pow 2)
    (levelQuadInfo_tendsto T lam hlam)
    (Eventually.of_forall (levelInfo_sq_le_levelQuadInfo T lam hlam))

-- @node: limitQuadInfo_le_eight_limitInfo
/-- If [the channel parameter lies strictly between zero and one](hyp:hlam),
[limiting quadratic information is at most eight times the limiting expected total
variation distance from uniform](goal). -/
lemma limitQuadInfo_le_eight_limitInfo {B : ℕ} (T : BoundedTree B) (lam : ℝ)
    (hlam : MainLambda lam) : limitQuadInfo T lam ≤ 8 * limitInfo T lam :=
  le_of_tendsto_of_tendsto (levelQuadInfo_tendsto T lam hlam)
    (tendsto_const_nhds.mul (levelInfo_tendsto T lam hlam))
    (Eventually.of_forall (levelQuadInfo_le_eight_levelInfo T lam hlam))

-- @node: reconstructs_iff_limitQuadInfo_pos
/-- If [the channel parameter lies strictly between zero and one](hyp:hlam),
[the limiting expected total variation distance from uniform is positive exactly
when limiting quadratic information is positive](goal). -/
theorem reconstructs_iff_limitQuadInfo_pos {B : ℕ} (T : BoundedTree B) (lam : ℝ)
    (hlam : MainLambda lam) : 0 < limitInfo T lam ↔ 0 < limitQuadInfo T lam := by
  constructor
  · intro hpos
    exact (sq_pos_of_pos hpos).trans_le (limitInfo_sq_le_limitQuadInfo T lam hlam)
  · intro hpos
    have hbound := limitQuadInfo_le_eight_limitInfo T lam hlam
    linarith

end OaiCapacityCriterionState
