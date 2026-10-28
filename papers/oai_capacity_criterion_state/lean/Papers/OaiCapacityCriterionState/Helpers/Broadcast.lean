module

public import Papers.OaiCapacityCriterionState.Basic
public import Papers.OaiCapacityCriterionState.Helpers.Trees
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Order.MonotoneConvergence

/-! # Finite-depth four-state broadcasting

A configuration is a spin assignment on the finite ball. Its joint mass is the
uniform root mass times the edge transition factors. Finite sums give the joint
law of the root and level observation, and hence the expected posterior distance.
-/

@[expose] public section

open Filter Topology
open scoped BigOperators

namespace OaiCapacityCriterionState

-- @env: S2
variable {B : ℕ}

open Classical in
/-- For [a bounded tree](hyp:T), [a depth](hyp:n), [a four-state assignment on the ball
through that depth](hyp:config), and [a vertex](hyp:v), the [extended spin](goal) is
[the assigned state when the vertex is in the ball](step:1) and [state zero otherwise](step:2).
@realizes \sigma_v(a spin in Fin 4 for every vertex in the finite experiment) -/
noncomputable def configSpin (T : BoundedTree B) (n : ℕ)
    (config : (T.ball n) → Fin 4) (v : List (Fin B)) : Fin 4 :=
  if hv : v ∈ T.ball n then config ⟨v, hv⟩ else 0

-- @node: def:channel
/-- For [a bounded tree](hyp:T), [a real channel parameter](hyp:lam), [a depth](hyp:n),
and [a four-state assignment on the ball through that depth](hyp:config), the
[broadcast joint mass](goal) is one quarter times the product of the channel transition
weights along all edges in the ball. -/
noncomputable def broadcastJoint (T : BoundedTree B) (lam : ℝ) (n : ℕ)
    (config : (T.ball n) → Fin 4) : ℝ :=
  (1 / 4) * ∏ w ∈ (T.ball n).erase [],
    channel lam (configSpin T n config w.tail) (configSpin T n config w)

-- @node: broadcastJoint_nonneg
/-- For [a bounded tree](hyp:T), [a channel parameter](hyp:lam) that [lies between zero
and one, inclusive](hyp:hlam), [a depth](hyp:n), and [a configuration on its ball](hyp:config),
[the broadcast joint mass is nonnegative](goal). -/
lemma broadcastJoint_nonneg (T : BoundedTree B) (lam : ℝ)
    (hlam : lam ∈ Set.Icc 0 1) (n : ℕ) (config : (T.ball n) → Fin 4) :
    0 ≤ broadcastJoint T lam n config := by
  classical
  unfold broadcastJoint
  apply mul_nonneg (by norm_num)
  apply Finset.prod_nonneg
  intro w _
  unfold channel
  apply add_nonneg
  · exact mul_nonneg hlam.1 (by split_ifs <;> norm_num)
  · exact div_nonneg (sub_nonneg.mpr hlam.2) (by norm_num)

-- @node: channel_row_sum
/-- For [any real channel parameter](hyp:lam) and [any initial state among the four
states](hyp:i), [the transition weights summed over all destination states equal one](goal). -/
lemma channel_row_sum (lam : ℝ) (i : Fin 4) :
    ∑ j : Fin 4, channel lam i j = 1 := by
  classical
  simp [channel, Finset.sum_add_distrib]
  ring

-- @node: ball_level_disjoint
/-- For [a bounded tree](hyp:T) and [a depth](hyp:n), [the ball through that depth and
the level at the next depth have no vertices in common](goal). -/
lemma ball_level_disjoint (T : BoundedTree B) (n : ℕ) :
    Disjoint (T.ball n) (T.level (n + 1)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hv hw
  have hle := (T.mem_ball_iff v n).mp hv
  have heq := (T.mem_level_iff v (n + 1)).mp hw
  omega

-- @node: level_parent_mem_ball
/-- In [a bounded tree](hyp:T), for [a depth](hyp:n) and [a vertex](hyp:v) that
[belongs to the next level](hyp:hv), [the vertex's parent belongs to the ball through
the given depth](goal). -/
lemma level_parent_mem_ball (T : BoundedTree B) (n : ℕ)
    (v : List (Fin B)) (hv : v ∈ T.level (n + 1)) : v.tail ∈ T.ball n := by
  have h := (T.mem_level_iff v (n + 1)).mp hv
  cases v with
  | nil => simp at h
  | cons a v =>
    apply (T.mem_ball_iff v n).mpr
    exact ⟨T.prefix_closed a v h.1, by simpa using h.2.le⟩

-- @node: ballConfigEquiv
/-- For [a bounded tree](hyp:T) and [a depth](hyp:n), [the configuration
correspondence](goal) bijectively identifies assignments on the ball through the next
depth with pairs consisting of an assignment on the current ball and an assignment
on the next level, by restriction and recombination. -/
noncomputable def ballConfigEquiv (T : BoundedTree B) (n : ℕ) :
    ((T.ball (n + 1)) → Fin 4) ≃
      (((T.ball n) → Fin 4) × ((T.level (n + 1)) → Fin 4)) := by
  classical
  refine
    { toFun := fun c =>
        (fun v => c ⟨v, Finset.mem_union_left _ v.property⟩,
         fun v => c ⟨v, Finset.mem_union_right _ v.property⟩)
      invFun := fun cd v => if h : v.val ∈ T.ball n then cd.1 ⟨v, h⟩
        else cd.2 ⟨v, (Finset.mem_union.mp v.property).resolve_left h⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro c
    funext v
    dsimp
    split_ifs <;> rfl
  · intro cd
    apply Prod.ext
    · funext v
      simp
    · funext v
      have hnot : v.val ∉ T.ball n := fun h =>
        Finset.disjoint_left.mp (ball_level_disjoint T n) h v.property
      simp [hnot]

-- @node: configSpin_ballConfigEquiv_old
/-- For [a bounded tree](hyp:T), [a depth](hyp:n), [an assignment on the current
ball](hyp:c), [an assignment on the next level](hyp:d), and [a vertex](hyp:v)
[in the current ball](hyp:hv), [combining the two assignments leaves the vertex's
spin equal to its spin in the current assignment](goal). -/
lemma configSpin_ballConfigEquiv_old (T : BoundedTree B) (n : ℕ)
    (c : (T.ball n) → Fin 4) (d : (T.level (n + 1)) → Fin 4)
    (v : List (Fin B)) (hv : v ∈ T.ball n) :
    configSpin T (n + 1) ((ballConfigEquiv T n).symm (c, d)) v =
      configSpin T n c v := by
  classical
  have hv' : v ∈ T.ball (n + 1) := Finset.mem_union_left _ hv
  simp only [configSpin, dif_pos hv', dif_pos hv]
  change (if h : v ∈ T.ball n then c ⟨v, h⟩ else _) = c ⟨v, hv⟩
  rw [dif_pos hv]

-- @node: configSpin_ballConfigEquiv_new
/-- For [a bounded tree](hyp:T), [a depth](hyp:n), [an assignment on the current
ball](hyp:c), [an assignment on the next level](hyp:d), and [a vertex on that next
level](hyp:v), [the combined assignment gives the vertex exactly its assigned
next-level spin](goal). -/
lemma configSpin_ballConfigEquiv_new (T : BoundedTree B) (n : ℕ)
    (c : (T.ball n) → Fin 4) (d : (T.level (n + 1)) → Fin 4)
    (v : T.level (n + 1)) :
    configSpin T (n + 1) ((ballConfigEquiv T n).symm (c, d)) v = d v := by
  classical
  have hnot : v.val ∉ T.ball n := fun h =>
    Finset.disjoint_left.mp (ball_level_disjoint T n) h v.property
  have hv : v.val ∈ T.ball (n + 1) := Finset.mem_union_right _ v.property
  simp [configSpin, ballConfigEquiv, hv, hnot]

-- @node: broadcastJoint_split
/-- For [a bounded tree](hyp:T), [a real channel parameter](hyp:lam), [a depth](hyp:n),
[an assignment on the current ball](hyp:c), and [an assignment on the next level](hyp:d),
[the joint mass of their combined configuration equals the current ball's joint mass
times the product of the transition weights from each next-level vertex's parent
spin to its assigned spin](goal). -/
lemma broadcastJoint_split (T : BoundedTree B) (lam : ℝ) (n : ℕ)
    (c : (T.ball n) → Fin 4) (d : (T.level (n + 1)) → Fin 4) :
    broadcastJoint T lam (n + 1) ((ballConfigEquiv T n).symm (c, d)) =
      broadcastJoint T lam n c *
        ∏ v : T.level (n + 1), channel lam (configSpin T n c v.val.tail) (d v) := by
  classical
  have hroot : [] ∈ T.ball n := (T.mem_ball_iff [] n).mpr ⟨T.nil_mem, by simp⟩
  have hrootlevel : [] ∉ T.level (n + 1) := by
    simp [T.mem_level_iff]
  have herase : (T.ball (n + 1)).erase [] =
      (T.ball n).erase [] ∪ T.level (n + 1) := by
    simp [BoundedTree.ball, Finset.erase_union_distrib, Finset.erase_eq_of_notMem hrootlevel]
  have hdis : Disjoint ((T.ball n).erase []) (T.level (n + 1)) :=
    (ball_level_disjoint T n).mono_left (Finset.erase_subset _ _)
  unfold broadcastJoint
  rw [herase, Finset.prod_union hdis, mul_assoc]
  congr 1
  congr 1
  · apply Finset.prod_congr rfl
    intro v hv
    have hmem := Finset.mem_of_mem_erase hv
    have hne := Finset.ne_of_mem_erase hv
    have hparent : v.tail ∈ T.ball n := by
      have h := (T.mem_ball_iff v n).mp hmem
      cases v with
      | nil => exact (hne rfl).elim
      | cons a v =>
        exact (T.mem_ball_iff v n).mpr
          ⟨T.prefix_closed a v h.1, by simpa using (Nat.le_of_succ_le h.2)⟩
    rw [configSpin_ballConfigEquiv_old T n c d _ hparent,
      configSpin_ballConfigEquiv_old T n c d _ hmem]
  · rw [← Finset.prod_attach]
    apply Finset.prod_congr rfl
    intro v _
    rw [configSpin_ballConfigEquiv_old T n c d _
      (level_parent_mem_ball T n v.val v.property), configSpin_ballConfigEquiv_new]

-- @node: broadcastJoint_sum
/-- For [a bounded tree](hyp:T), [a channel parameter](hyp:lam) that [lies between zero
and one, inclusive](hyp:hlam), and [a depth](hyp:n), [the broadcast joint masses summed
over all configurations on the ball equal one](goal). -/
lemma broadcastJoint_sum (T : BoundedTree B) (lam : ℝ)
    (hlam : lam ∈ Set.Icc 0 1) (n : ℕ) :
    ∑ config : (T.ball n) → Fin 4, broadcastJoint T lam n config = 1 := by
  classical
  induction n with
  | zero =>
    norm_num [broadcastJoint, BoundedTree.ball, Finset.card_univ, Fintype.card_fun,
      Fintype.card_coe]
  | succ n ih =>
    rw [← (ballConfigEquiv T n).symm.sum_comp]
    rw [Fintype.sum_prod_type]
    simp_rw [broadcastJoint_split]
    simp_rw [← Finset.mul_sum, ← Fintype.prod_sum, channel_row_sum]
    simpa using ih

open Classical in
/-- For [a bounded tree](hyp:T), [a real channel parameter](hyp:lam), [a depth](hyp:n),
[a root state](hyp:i), and [an observed assignment on that level](hyp:obs), the
[root-and-level joint mass](goal) is the sum of the broadcast masses of all ball
configurations having that root state and that level assignment.
@realizes \sigma_{L_n}(the restriction of the spin assignment to the finite level) -/
noncomputable def levelJoint (T : BoundedTree B) (lam : ℝ) (n : ℕ)
    (i : Fin 4) (obs : (T.level n) → Fin 4) : ℝ :=
  ∑ config : (T.ball n) → Fin 4,
    if configSpin T n config [] = i ∧
        (∀ v : T.level n, configSpin T n config v = obs v) then
      broadcastJoint T lam n config else 0

/-- For [a bounded tree](hyp:T), [a real channel parameter](hyp:lam), [a depth](hyp:n),
and [an observed assignment on that level](hyp:obs), the [level marginal mass](goal)
is the sum of the root-and-level joint masses over the four possible root states. -/
noncomputable def levelMarginal (T : BoundedTree B) (lam : ℝ) (n : ℕ)
    (obs : (T.level n) → Fin 4) : ℝ := ∑ i : Fin 4, levelJoint T lam n i obs

open Classical in
/-- For [a bounded tree](hyp:T), [a real channel parameter](hyp:lam), [a depth](hyp:n),
and [an observed assignment on that level](hyp:obs), the [root posterior vector](goal)
uses [each root-and-level joint mass divided by the level marginal when that marginal
is positive](step:1), and [the uniform four-state vector otherwise](step:2). -/
noncomputable def rootPosterior (T : BoundedTree B) (lam : ℝ) (n : ℕ)
    (obs : (T.level n) → Fin 4) : Fin 4 → ℝ :=
  if 0 < levelMarginal T lam n obs then
    fun i => levelJoint T lam n i obs / levelMarginal T lam n obs
  else unifVec

/-- For [a real vector indexed by the four states](hyp:p), its [total variation
distance from uniform](goal) is half the sum of the absolute differences between its
coordinates and one quarter.
@realizes \TV(half the sum of coordinatewise absolute differences from uniform) -/
noncomputable def tvToUnif (p : Fin 4 → ℝ) : ℝ :=
  (1 / 2) * ∑ i : Fin 4, |p i - 1 / 4|

-- @node: levelJoint_nonneg
/-- For [a bounded tree](hyp:T), [a channel parameter](hyp:lam) that [lies between zero
and one, inclusive](hyp:hlam), [a depth](hyp:n), [a root state](hyp:i), and [an observed
assignment on that level](hyp:obs), [the root-and-level joint mass is nonnegative](goal). -/
lemma levelJoint_nonneg (T : BoundedTree B) (lam : ℝ)
    (hlam : lam ∈ Set.Icc 0 1) (n : ℕ) (i : Fin 4)
    (obs : (T.level n) → Fin 4) : 0 ≤ levelJoint T lam n i obs := by
  classical
  unfold levelJoint
  exact Finset.sum_nonneg fun config _ => by
    split_ifs
    · exact broadcastJoint_nonneg T lam hlam n config
    · exact le_rfl

-- @node: levelMarginal_nonneg
/-- For [a bounded tree](hyp:T), [a channel parameter](hyp:lam) that [lies between zero
and one, inclusive](hyp:hlam), [a depth](hyp:n), and [an observed assignment on that
level](hyp:obs), [the level marginal mass is nonnegative](goal). -/
lemma levelMarginal_nonneg (T : BoundedTree B) (lam : ℝ)
    (hlam : lam ∈ Set.Icc 0 1) (n : ℕ) (obs : (T.level n) → Fin 4) :
    0 ≤ levelMarginal T lam n obs := by
  exact Finset.sum_nonneg fun i _ => levelJoint_nonneg T lam hlam n i obs

-- @node: levelMarginal_sum
/-- For [a bounded tree](hyp:T), [a channel parameter](hyp:lam) that [lies between zero
and one, inclusive](hyp:hlam), and [a depth](hyp:n), [the marginal masses summed over
all assignments on that level equal one](goal). -/
lemma levelMarginal_sum (T : BoundedTree B) (lam : ℝ)
    (hlam : lam ∈ Set.Icc 0 1) (n : ℕ) :
    ∑ obs : (T.level n) → Fin 4, levelMarginal T lam n obs = 1 := by
  classical
  unfold levelMarginal levelJoint
  calc
    _ = ∑ config : (T.ball n) → Fin 4,
        ∑ obs : (T.level n) → Fin 4, ∑ i : Fin 4,
          if configSpin T n config [] = i ∧
              (∀ v : T.level n, configSpin T n config v = obs v) then
            broadcastJoint T lam n config else 0 := by
      conv_lhs =>
        enter [2, obs]
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
    _ = ∑ config : (T.ball n) → Fin 4, broadcastJoint T lam n config := by
      apply Finset.sum_congr rfl
      intro config _
      simp [ite_and, ← funext_iff]
    _ = 1 := broadcastJoint_sum T lam hlam n

-- @node: tvToUnif_mem_Icc
/-- If [a real vector on the four states](hyp:p) [has nonnegative coordinates](hyp:hp)
and [its coordinates sum to one](hyp:hsum), [its total variation distance from uniform
lies between zero and one, inclusive](goal). -/
lemma tvToUnif_mem_Icc (p : Fin 4 → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) : tvToUnif p ∈ Set.Icc 0 1 := by
  constructor
  · exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => abs_nonneg _)
  · have hterm (i : Fin 4) : |p i - 1 / 4| ≤ p i + 1 / 4 := by
      exact abs_sub_le_iff.mpr ⟨by linarith, by linarith [hp i]⟩
    have hbound := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm i)
    simp only [Finset.sum_add_distrib, hsum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hbound
    unfold tvToUnif
    linarith

-- @node: rootPosterior_tv_mem_Icc
/-- For [a bounded tree](hyp:T), [a channel parameter](hyp:lam) that [lies between zero
and one, inclusive](hyp:hlam), [a depth](hyp:n), and [an observed assignment on that
level](hyp:obs), [the root posterior's total variation distance from uniform lies
between zero and one, inclusive](goal). -/
lemma rootPosterior_tv_mem_Icc (T : BoundedTree B) (lam : ℝ)
    (hlam : lam ∈ Set.Icc 0 1) (n : ℕ) (obs : (T.level n) → Fin 4) :
    tvToUnif (rootPosterior T lam n obs) ∈ Set.Icc 0 1 := by
  classical
  unfold rootPosterior
  split_ifs with hpos
  · apply tvToUnif_mem_Icc
    · intro i
      exact div_nonneg (levelJoint_nonneg T lam hlam n i obs) hpos.le
    · rw [← Finset.sum_div]
      exact div_self (ne_of_gt hpos)
  · apply tvToUnif_mem_Icc
    · intro i
      norm_num [unifVec]
    · norm_num [unifVec]

-- @node: def:level-information
/-- For [a bounded tree](hyp:T), [a real channel parameter](hyp:lam), and [a depth](hyp:n),
the [level information](goal) is the sum over all observations at that depth of their
marginal masses times the root posterior's total variation distance from uniform.
@realizes a_n(expected root posterior total variation at depth n, in [0,1]) -/
noncomputable def levelInfo (T : BoundedTree B) (lam : ℝ) (n : ℕ) : ℝ :=
  ∑ obs : (T.level n) → Fin 4,
    levelMarginal T lam n obs * tvToUnif (rootPosterior T lam n obs)

-- @node: levelInfo_mem_Icc
/-- For [a bounded tree](hyp:T), [a channel parameter](hyp:lam) that [lies strictly
between zero and one](hyp:hlam), and [a depth](hyp:n), [the level information lies
between zero and one, inclusive](goal). -/
lemma levelInfo_mem_Icc (T : BoundedTree B) (lam : ℝ) (hlam : MainLambda lam) (n : ℕ) :
    levelInfo T lam n ∈ Set.Icc 0 1 := by
  classical
  have hlam' : lam ∈ Set.Icc 0 1 := ⟨hlam.1.le, hlam.2.le⟩
  constructor
  · exact Finset.sum_nonneg fun obs _ =>
      mul_nonneg (levelMarginal_nonneg T lam hlam' n obs)
        (rootPosterior_tv_mem_Icc T lam hlam' n obs).1
  · calc
      levelInfo T lam n ≤ ∑ obs : (T.level n) → Fin 4,
          levelMarginal T lam n obs := by
        apply Finset.sum_le_sum
        intro obs _
        exact mul_le_of_le_one_right (levelMarginal_nonneg T lam hlam' n obs)
          (rootPosterior_tv_mem_Icc T lam hlam' n obs).2
      _ = 1 := levelMarginal_sum T lam hlam' n

-- @node: levelParent
/-- For [a bounded tree](hyp:T), [a depth](hyp:n), and [a vertex on the next
level](hyp:v), the [level parent](goal) is the parent vertex, regarded as a vertex
on the current level. -/
def levelParent (T : BoundedTree B) (n : ℕ) (v : T.level (n + 1)) : T.level n :=
  ⟨v.val.tail, by
    have h := (T.mem_level_iff v.val (n + 1)).mp v.property
    rcases v with ⟨v, hv⟩
    cases v with
    | nil => simp at h
    | cons a v =>
      exact (T.mem_level_iff v n).mpr
        ⟨T.prefix_closed a v h.1, by simpa using h.2⟩⟩

-- @node: levelTransition
/-- For [a bounded tree](hyp:T), [a real channel parameter](hyp:lam), [a depth](hyp:n),
[an assignment on the current level](hyp:obs), and [an assignment on the next
level](hyp:next), the [level transition weight](goal) is the product over next-level
vertices of the channel weights from their parents' current spins to their next spins. -/
noncomputable def levelTransition (T : BoundedTree B) (lam : ℝ) (n : ℕ)
    (obs : T.level n → Fin 4) (next : T.level (n + 1) → Fin 4) : ℝ :=
  ∏ v, channel lam (obs (levelParent T n v)) (next v)

-- @node: levelTransition_nonneg
/-- For [a bounded tree](hyp:T), [a channel parameter](hyp:lam) that [lies between zero
and one, inclusive](hyp:hlam), [a depth](hyp:n), [a current-level assignment](hyp:obs),
and [a next-level assignment](hyp:next), [the level transition weight is nonnegative](goal). -/
lemma levelTransition_nonneg (T : BoundedTree B) (lam : ℝ)
    (hlam : lam ∈ Set.Icc 0 1) (n : ℕ)
    (obs : T.level n → Fin 4) (next : T.level (n + 1) → Fin 4) :
    0 ≤ levelTransition T lam n obs next := by
  classical
  apply Finset.prod_nonneg
  intro v _
  unfold channel
  apply add_nonneg
  · exact mul_nonneg hlam.1 (by split_ifs <;> norm_num)
  · exact div_nonneg (sub_nonneg.mpr hlam.2) (by norm_num)

-- @node: levelTransition_sum
/-- For [a bounded tree](hyp:T), [any real channel parameter](hyp:lam), [a depth](hyp:n),
and [a current-level assignment](hyp:obs), [the transition weights summed over all
next-level assignments equal one](goal). -/
lemma levelTransition_sum (T : BoundedTree B) (lam : ℝ) (n : ℕ)
    (obs : T.level n → Fin 4) :
    ∑ next, levelTransition T lam n obs next = 1 := by
  classical
  unfold levelTransition
  rw [← Fintype.prod_sum]
  simp only [channel_row_sum, Finset.prod_const_one]

-- @node: levelJoint_step
/-- For [a bounded tree](hyp:T), [a real channel parameter](hyp:lam), [a depth](hyp:n),
[a root state](hyp:i), and [a next-level assignment](hyp:next), [the joint mass of
that root state and next-level assignment equals the sum over current-level assignments
of their joint masses with the root state times their transition weights to the
next-level assignment](goal). -/
lemma levelJoint_step (T : BoundedTree B) (lam : ℝ) (n : ℕ)
    (i : Fin 4) (next : T.level (n + 1) → Fin 4) :
    levelJoint T lam (n + 1) i next =
      ∑ obs, levelJoint T lam n i obs * levelTransition T lam n obs next := by
  classical
  have hroot : [] ∈ T.ball n := (T.mem_ball_iff [] n).mpr ⟨T.nil_mem, by simp⟩
  unfold levelJoint
  rw [← (ballConfigEquiv T n).symm.sum_comp, Fintype.sum_prod_type]
  simp_rw [configSpin_ballConfigEquiv_old T n _ _ [] hroot]
  simp_rw [configSpin_ballConfigEquiv_new, broadcastJoint_split]
  simp only [← funext_iff, ite_and]
  simp_rw [Finset.sum_ite_irrel]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  simp only [ite_mul, zero_mul, Finset.sum_ite_irrel]
  split_ifs with hi
  · simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rfl
  · simp

-- @node: levelMarginal_step
/-- For [a bounded tree](hyp:T), [a real channel parameter](hyp:lam), [a depth](hyp:n),
and [a next-level assignment](hyp:next), [its marginal mass equals the sum over
current-level assignments of their marginal masses times their transition weights
to the next-level assignment](goal). -/
lemma levelMarginal_step (T : BoundedTree B) (lam : ℝ) (n : ℕ)
    (next : T.level (n + 1) → Fin 4) :
    levelMarginal T lam (n + 1) next =
      ∑ obs, levelMarginal T lam n obs * levelTransition T lam n obs next := by
  classical
  simp only [levelMarginal, levelJoint_step, Finset.sum_mul]
  rw [Finset.sum_comm]

-- @node: levelInfo_joint
/-- For [a bounded tree](hyp:T), [a channel parameter](hyp:lam) that [lies between zero
and one, inclusive](hyp:hlam), and [a depth](hyp:n), [the level information equals
half the sum over all level observations and root states of the absolute difference
between their joint mass and one quarter of the observation's marginal mass](goal). -/
lemma levelInfo_joint (T : BoundedTree B) (lam : ℝ)
    (hlam : lam ∈ Set.Icc 0 1) (n : ℕ) :
    levelInfo T lam n = (1 / 2) * ∑ obs : T.level n → Fin 4,
      ∑ i : Fin 4, |levelJoint T lam n i obs - levelMarginal T lam n obs / 4| := by
  classical
  unfold levelInfo
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro obs _
  have hm := levelMarginal_nonneg T lam hlam n obs
  by_cases hpos : 0 < levelMarginal T lam n obs
  · simp only [rootPosterior, if_pos hpos, tvToUnif]
    rw [mul_left_comm, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = |levelMarginal T lam n obs| *
          |levelJoint T lam n i obs / levelMarginal T lam n obs - 1 / 4| := by
        rw [abs_of_nonneg hm]
      _ = |levelMarginal T lam n obs *
          (levelJoint T lam n i obs / levelMarginal T lam n obs - 1 / 4)| :=
        (abs_mul _ _).symm
      _ = _ := by
        congr 1
        field_simp [ne_of_gt hpos]
  · have hz : levelMarginal T lam n obs = 0 := le_antisymm (le_of_not_gt hpos) hm
    have hj (i : Fin 4) : levelJoint T lam n i obs = 0 := by
      have hle : levelJoint T lam n i obs ≤ levelMarginal T lam n obs :=
        Finset.single_le_sum (fun j _ => levelJoint_nonneg T lam hlam n j obs)
          (Finset.mem_univ i)
      exact le_antisymm (hz ▸ hle) (levelJoint_nonneg T lam hlam n i obs)
    simp [hz, hj]

-- @node: levelInfo_succ_le
/-- For [a bounded tree](hyp:T), [a channel parameter](hyp:lam) that [lies between zero
and one, inclusive](hyp:hlam), and [a depth](hyp:n), [the expected posterior distance
from uniform at the next depth is at most that at the current depth](goal). -/
lemma levelInfo_succ_le (T : BoundedTree B) (lam : ℝ)
    (hlam : lam ∈ Set.Icc 0 1) (n : ℕ) :
    levelInfo T lam (n + 1) ≤ levelInfo T lam n := by
  classical
  rw [levelInfo_joint T lam hlam (n + 1), levelInfo_joint T lam hlam n]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ ≤ ∑ next : T.level (n + 1) → Fin 4, ∑ i : Fin 4,
        ∑ obs : T.level n → Fin 4,
          |levelJoint T lam n i obs - levelMarginal T lam n obs / 4| *
            levelTransition T lam n obs next := by
      apply Finset.sum_le_sum
      intro next _
      apply Finset.sum_le_sum
      intro i _
      have heq : levelJoint T lam (n + 1) i next -
          levelMarginal T lam (n + 1) next / 4 =
          ∑ obs, (levelJoint T lam n i obs - levelMarginal T lam n obs / 4) *
            levelTransition T lam n obs next := by
        rw [levelJoint_step, levelMarginal_step, Finset.sum_div, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro obs _
        ring
      rw [heq]
      calc
        _ ≤ ∑ obs, |(levelJoint T lam n i obs - levelMarginal T lam n obs / 4) *
            levelTransition T lam n obs next| := Finset.abs_sum_le_sum_abs _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro obs _
          rw [abs_mul, abs_of_nonneg (levelTransition_nonneg T lam hlam n obs next)]
    _ = ∑ obs : T.level n → Fin 4,
        ∑ i : Fin 4, |levelJoint T lam n i obs - levelMarginal T lam n obs / 4| := by
      conv_lhs =>
        enter [2, next]
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro obs _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.mul_sum, levelTransition_sum, mul_one]

-- @node: levelInfo_antitone
/-- For [a bounded tree](hyp:T) and [a channel parameter](hyp:lam) that [lies strictly
between zero and one](hyp:hlam), [level information is nonincreasing as depth
increases](goal). -/
lemma levelInfo_antitone (T : BoundedTree B) (lam : ℝ) (hlam : MainLambda lam) :
    Antitone (levelInfo T lam) := by
  apply antitone_nat_of_succ_le
  exact levelInfo_succ_le T lam ⟨hlam.1.le, hlam.2.le⟩

-- @node: def:reconstruction
/-- For [a bounded tree](hyp:T) and [a real channel parameter](hyp:lam), the
[limiting information](goal) is the selected limit of the level-information sequence
as depth tends to infinity.

When the sequence does not converge, the limit operator returns its default value.
@realizes a_\infty(limit of the decreasing bounded level-information sequence) -/
noncomputable def limitInfo (T : BoundedTree B) (lam : ℝ) : ℝ :=
  Filter.limUnder Filter.atTop (levelInfo T lam)

-- keep: Public predicate for the paper's definition of reconstruction; the main theorem unfolds it as 0 < limitInfo.
/-- For [a bounded tree](hyp:T) and [a real channel parameter](hyp:lam),
[reconstruction](goal) means that the limiting information is strictly positive. -/
def Reconstructs (T : BoundedTree B) (lam : ℝ) : Prop := 0 < limitInfo T lam

-- @node: levelInfo_tendsto
/-- For [a bounded tree](hyp:T) and [a channel parameter](hyp:lam) that [lies strictly
between zero and one](hyp:hlam), [level information converges to the limiting
information as depth tends to infinity](goal). -/
lemma levelInfo_tendsto (T : BoundedTree B) (lam : ℝ) (hlam : MainLambda lam) :
    Tendsto (levelInfo T lam) atTop (𝓝 (limitInfo T lam)) := by
  have hbounded : BddBelow (Set.range (levelInfo T lam)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (levelInfo_mem_Icc T lam hlam n).1
  have hconv := tendsto_atTop_ciInf (levelInfo_antitone T lam hlam) hbounded
  unfold limitInfo
  rw [hconv.limUnder_eq]
  exact hconv

-- @node: limitInfo_mem_Icc
/-- For [a bounded tree](hyp:T) and [a channel parameter](hyp:lam) that [lies strictly
between zero and one](hyp:hlam), [the limiting information lies between zero and one,
inclusive](goal). -/
lemma limitInfo_mem_Icc (T : BoundedTree B) (lam : ℝ) (hlam : MainLambda lam) :
    limitInfo T lam ∈ Set.Icc 0 1 := by
  exact isClosed_Icc.mem_of_tendsto (levelInfo_tendsto T lam hlam)
    (Filter.Eventually.of_forall (levelInfo_mem_Icc T lam hlam))

end OaiCapacityCriterionState
