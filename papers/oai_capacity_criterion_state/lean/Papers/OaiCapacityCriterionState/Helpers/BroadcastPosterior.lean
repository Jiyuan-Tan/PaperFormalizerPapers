module

public import Papers.OaiCapacityCriterionState.Helpers.Information

/-! # Posterior laws of the finite broadcast experiment

The root marginal stays uniform under the level transition. Thus the finite
broadcast likelihood defines a posterior law whose quadratic information is
exactly the finite-level quadratic information.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace OaiCapacityCriterionState

variable {B : ℕ}

-- @node: levelJoint_sum_observations
/-- For any bounded tree, channel parameter, depth, and root state, [summing the
joint weights over all observations at that depth gives one quarter](goal). -/
lemma levelJoint_sum_observations (T : BoundedTree B) (lam : ℝ) (n : ℕ)
    (i : Fin 4) : ∑ obs : T.level n → Fin 4, levelJoint T lam n i obs = 1 / 4 := by
  classical
  induction n with
  | zero =>
      simp only [levelJoint]
      rw [Finset.sum_comm]
      simp only [← funext_iff, ite_and, Finset.sum_ite_irrel]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const_zero]
      let : Unique (T.ball 0) := by
        change Unique ({[]} : Finset (List (Fin B)))
        infer_instance
      rw [← (Equiv.piUnique (fun _ : T.ball 0 => Fin 4)).symm.sum_comp]
      simp only [broadcastJoint, configSpin, BoundedTree.ball, Finset.mem_singleton,
        Finset.erase_singleton, Finset.prod_empty, mul_one]
      change (∑ x : Fin 4, if x = i then (1 / 4 : ℝ) else 0) = 1 / 4
      simp
  | succ n ih =>
      simp_rw [levelJoint_step]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, levelTransition_sum, mul_one]
      exact ih

-- @node: broadcastLikelihood
/-- On [a tree](hyp:T) with [branching bound B](hyp:B), for [channel parameter
λ](hyp:lam), [depth n](hyp:n), [root state i](hyp:i), and [level observation](hyp:obs),
the [broadcast likelihood is four times the joint weight of that root state and
observation](goal). -/
noncomputable def broadcastLikelihood (T : BoundedTree B) (lam : ℝ) (n : ℕ)
    (i : Fin 4) (obs : T.level n → Fin 4) : ℝ :=
  4 * levelJoint T lam n i obs

-- @node: broadcastLikelihood_nonneg
/-- If [the channel parameter lies between zero and one, inclusive](hyp:hlam),
then [the broadcast likelihood of any level observation conditional on any root
state is nonnegative](goal). -/
lemma broadcastLikelihood_nonneg (T : BoundedTree B) (lam : ℝ)
    (hlam : lam ∈ Set.Icc 0 1) (n : ℕ) (i : Fin 4) (obs : T.level n → Fin 4) :
    0 ≤ broadcastLikelihood T lam n i obs :=
  mul_nonneg (by norm_num) (levelJoint_nonneg T lam hlam n i obs)

-- @node: broadcastLikelihood_sum
/-- For any bounded tree, channel parameter, depth, and root state, [the broadcast
likelihood sums to one over all observations at that depth](goal). -/
lemma broadcastLikelihood_sum (T : BoundedTree B) (lam : ℝ) (n : ℕ) (i : Fin 4) :
    ∑ obs, broadcastLikelihood T lam n i obs = 1 := by
  unfold broadcastLikelihood
  rw [← Finset.mul_sum, levelJoint_sum_observations]
  norm_num

-- @node: broadcastLikelihood_marginal
/-- For any level observation, [its marginal weight in the experiment defined by
the broadcast likelihood equals its broadcast level marginal weight](goal). -/
lemma broadcastLikelihood_marginal (T : BoundedTree B) (lam : ℝ) (n : ℕ)
    (obs : T.level n → Fin 4) :
    experimentMarginal (broadcastLikelihood T lam n) obs = levelMarginal T lam n obs := by
  unfold experimentMarginal broadcastLikelihood levelMarginal
  rw [← Finset.mul_sum]
  ring

-- @node: broadcastLikelihood_posterior
/-- For any level observation, [the posterior from the broadcast likelihood
experiment equals the broadcast posterior distribution of the root state](goal). -/
lemma broadcastLikelihood_posterior (T : BoundedTree B) (lam : ℝ) (n : ℕ)
    (obs : T.level n → Fin 4) :
    experimentPosterior (broadcastLikelihood T lam n) obs = rootPosterior T lam n obs := by
  classical
  unfold experimentPosterior
  rw [broadcastLikelihood_marginal]
  unfold rootPosterior broadcastLikelihood
  split_ifs
  · funext i
    congr 1
    ring
  · rfl

-- @node: broadcastPosteriorLaw
/-- For [a tree](hyp:T) with [branching bound B](hyp:B), [channel parameter
λ](hyp:lam), and [observation depth n](hyp:n), the [broadcast posterior law is the
distribution of posterior beliefs in the broadcast likelihood experiment](goal). -/
noncomputable def broadcastPosteriorLaw (T : BoundedTree B) (lam : ℝ) (n : ℕ) :
    Measure (Fin 4 → ℝ) := experimentLaw (broadcastLikelihood T lam n)

-- @node: broadcastPosteriorLaw_isPosteriorLaw
/-- If [the channel parameter lies between zero and one, inclusive](hyp:hlam),
then [the broadcast posterior law at every depth is a probability law on
four-state beliefs whose mean is the uniform prior](goal). -/
lemma broadcastPosteriorLaw_isPosteriorLaw (T : BoundedTree B) (lam : ℝ)
    (hlam : lam ∈ Set.Icc 0 1) (n : ℕ) :
    IsPosteriorLaw (broadcastPosteriorLaw T lam n) :=
  experimentLaw_isPosteriorLaw _ (broadcastLikelihood_nonneg T lam hlam n)
    (broadcastLikelihood_sum T lam n)

-- @node: broadcastPosteriorLaw_eq_sum
/-- At any depth, [the broadcast posterior law is the sum of point masses at the
root posteriors for all level observations, weighted by the nonnegative parts of
their marginal weights](goal). -/
lemma broadcastPosteriorLaw_eq_sum (T : BoundedTree B) (lam : ℝ) (n : ℕ) :
    broadcastPosteriorLaw T lam n =
      ∑ obs : T.level n → Fin 4, ENNReal.ofReal (levelMarginal T lam n obs) •
        Measure.dirac (rootPosterior T lam n obs) := by
  simp only [broadcastPosteriorLaw, experimentLaw, broadcastLikelihood_marginal,
    broadcastLikelihood_posterior]

-- @node: integral_broadcastPosteriorLaw
/-- If [the channel parameter lies between zero and one, inclusive](hyp:hlam),
then [the integral of any real-valued function of beliefs under the broadcast
posterior law equals the sum of its values at the root posteriors, weighted by
the level observations' marginal probabilities](goal). -/
lemma integral_broadcastPosteriorLaw (T : BoundedTree B) (lam : ℝ)
    (hlam : lam ∈ Set.Icc 0 1) (n : ℕ) (f : (Fin 4 → ℝ) → ℝ) :
    ∫ p, f p ∂(broadcastPosteriorLaw T lam n) =
      ∑ obs : T.level n → Fin 4,
        levelMarginal T lam n obs * f (rootPosterior T lam n obs) := by
  rw [broadcastPosteriorLaw_eq_sum, integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac,
      ENNReal.toReal_ofReal (levelMarginal_nonneg T lam hlam n _), smul_eq_mul]
  · intro obs _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

-- @node: quadInfo_broadcastPosteriorLaw
/-- If [the channel parameter lies between zero and one, inclusive](hyp:hlam),
then [the quadratic information of the broadcast posterior law equals the
finite-level quadratic information](goal). -/
lemma quadInfo_broadcastPosteriorLaw (T : BoundedTree B) (lam : ℝ)
    (hlam : lam ∈ Set.Icc 0 1) (n : ℕ) :
    quadInfo (broadcastPosteriorLaw T lam n) = levelQuadInfo T lam n :=
  integral_broadcastPosteriorLaw T lam hlam n quadStat

-- @node: quadInfo_broadcastPosteriorLaw_tendsto
/-- If [the channel parameter lies strictly between zero and one](hyp:hlam), then
[the quadratic information of the broadcast posterior laws converges to the
limiting quadratic information as the observation depth tends to infinity](goal). -/
lemma quadInfo_broadcastPosteriorLaw_tendsto (T : BoundedTree B) (lam : ℝ)
    (hlam : MainLambda lam) :
    Filter.Tendsto (fun n => quadInfo (broadcastPosteriorLaw T lam n))
      Filter.atTop (nhds (limitQuadInfo T lam)) := by
  simp_rw [quadInfo_broadcastPosteriorLaw T lam ⟨hlam.1.le, hlam.2.le⟩]
  exact levelQuadInfo_tendsto T lam hlam

-- @node: reconstructs_iff_broadcastPosteriorLaw_uniform_pos
/-- If [the channel parameter lies strictly between zero and one](hyp:hlam), then
[the limiting information is positive if and only if a single strictly positive
constant bounds below the quadratic information of every finite-depth broadcast
posterior law](goal). -/
theorem reconstructs_iff_broadcastPosteriorLaw_uniform_pos (T : BoundedTree B) (lam : ℝ)
    (hlam : MainLambda lam) :
    0 < limitInfo T lam ↔
      ∃ c : ℝ, 0 < c ∧ ∀ n, c ≤ quadInfo (broadcastPosteriorLaw T lam n) := by
  simp_rw [quadInfo_broadcastPosteriorLaw T lam ⟨hlam.1.le, hlam.2.le⟩]
  exact reconstructs_iff_levelQuadInfo_uniform_pos T lam hlam

-- @node: levelJoint_zero
/-- At depth zero, [the joint weight of a root state and an observation is one
quarter when the observed root state matches that state, and zero otherwise](goal). -/
lemma levelJoint_zero (T : BoundedTree B) (lam : ℝ) (i : Fin 4)
    (obs : T.level 0 → Fin 4) :
    levelJoint T lam 0 i obs =
      if obs ⟨[], by simp [BoundedTree.level]⟩ = i then 1 / 4 else 0 := by
  classical
  let : Unique (T.ball 0) := by
    change Unique ({[]} : Finset (List (Fin B)))
    infer_instance
  unfold levelJoint
  rw [← (Equiv.piUnique (fun _ : T.ball 0 => Fin 4)).symm.sum_comp]
  have hobs (j : Fin 4) :
      (∀ v : T.level 0, configSpin T 0
        ((Equiv.piUnique (fun _ : T.ball 0 => Fin 4)).symm j) v = obs v) ↔
        j = obs ⟨[], by simp [BoundedTree.level]⟩ := by
    constructor
    · intro h
      have hh := h ⟨[], by simp [BoundedTree.level]⟩
      simp only [configSpin, BoundedTree.ball, Finset.mem_singleton] at hh
      exact hh
    · intro h v
      have hv : v.val = [] := by simpa [BoundedTree.level] using v.property
      subst h
      have heq : v = ⟨[], by simp [BoundedTree.level]⟩ := Subtype.ext hv
      subst v
      rfl
  simp_rw [hobs]
  simp only [configSpin, BoundedTree.ball, Finset.mem_singleton,
    broadcastJoint, Finset.erase_singleton, Finset.prod_empty, mul_one]
  change (∑ j : Fin 4, if j = i ∧ j = obs ⟨[], _⟩ then (1 / 4 : ℝ) else 0) = _
  simp [ite_and, eq_comm]

-- @node: levelMarginal_zero
/-- For any bounded tree and channel parameter, [each depth-zero observation has
marginal weight one quarter](goal). -/
lemma levelMarginal_zero (T : BoundedTree B) (lam : ℝ) (obs : T.level 0 → Fin 4) :
    levelMarginal T lam 0 obs = 1 / 4 := by
  classical
  simp [levelMarginal, levelJoint_zero]

-- @node: rootPosterior_zero
/-- At depth zero, [the root posterior assigns probability one to the observed
root state and zero to every other state](goal). -/
lemma rootPosterior_zero (T : BoundedTree B) (lam : ℝ) (obs : T.level 0 → Fin 4) :
    rootPosterior T lam 0 obs = Pi.single (obs ⟨[], by simp [BoundedTree.level]⟩) 1 := by
  classical
  ext i
  simp only [rootPosterior, levelMarginal_zero, show (0 : ℝ) < 1 / 4 by norm_num,
    if_true, levelJoint_zero, Pi.single_apply]
  split_ifs <;> simp_all [eq_comm]

-- @node: broadcastPosteriorLaw_zero
/-- For any bounded tree and channel parameter, [the depth-zero broadcast
posterior law is the fully revealing law](goal). -/
lemma broadcastPosteriorLaw_zero (T : BoundedTree B) (lam : ℝ) :
    broadcastPosteriorLaw T lam 0 = revealingLaw := by
  classical
  let : Unique (T.level 0) := by
    change Unique ({[]} : Finset (List (Fin B)))
    infer_instance
  rw [broadcastPosteriorLaw_eq_sum,
    ← (Equiv.piUnique (fun _ : T.level 0 => Fin 4)).symm.sum_comp]
  simp only [levelMarginal_zero, rootPosterior_zero]
  change (∑ i : Fin 4, ENNReal.ofReal (1 / 4 : ℝ) • Measure.dirac (Pi.single i 1)) = _
  simp [revealingLaw]

end OaiCapacityCriterionState
