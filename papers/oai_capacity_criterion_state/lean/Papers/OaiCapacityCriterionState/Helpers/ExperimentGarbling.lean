module

public import Papers.OaiCapacityCriterionState.Helpers.FiniteExperiments
public import Papers.OaiCapacityCriterionState.Helpers.Information

/-! # Quadratic information under finite observation channels

Postprocessing an observation averages its centered posterior coordinates.
Weighted Cauchy--Schwarz therefore gives data processing for quadratic information,
including observations of zero marginal probability.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace OaiCapacityCriterionState

variable {O O' : Type} [Fintype O] [Fintype O']

-- @node: garbledLikelihood
/-- Given [an experiment's likelihoods](hyp:lik), [postprocessing weights from original to
new observations](hyp:K), [a state](hyp:i), and [a new observation](hyp:o') in
[the new observation space](hyp:O'), the
[postprocessed likelihood](goal) is the sum over [the finite original observation
space](hyp:O) of the original likelihood times the postprocessing weight. -/
noncomputable def garbledLikelihood (lik : Fin 4 → O → ℝ) (K : O → O' → ℝ)
    (i : Fin 4) (o' : O') : ℝ := ∑ o, lik i o * K o o'

omit [Fintype O'] in
-- @node: garbledLikelihood_nonneg
/-- If [the original likelihoods are nonnegative](hyp:hlik) and [all postprocessing
weights are nonnegative](hyp:hK), then [every postprocessed likelihood is
nonnegative](goal). -/
lemma garbledLikelihood_nonneg (lik : Fin 4 → O → ℝ) (K : O → O' → ℝ)
    (hlik : ∀ i o, 0 ≤ lik i o) (hK : ∀ o o', 0 ≤ K o o') :
    ∀ i o', 0 ≤ garbledLikelihood lik K i o' := by
  intro i o'
  exact Finset.sum_nonneg fun o _ => mul_nonneg (hlik i o) (hK o o')

-- @node: garbledLikelihood_sum
/-- If [the original likelihoods sum to one for each state](hyp:hlik) and
[postprocessing weights sum to one for each original observation](hyp:hK), then
[the postprocessed likelihoods sum to one for each state](goal). -/
lemma garbledLikelihood_sum (lik : Fin 4 → O → ℝ) (K : O → O' → ℝ)
    (hlik : ∀ i, ∑ o, lik i o = 1) (hK : ∀ o, ∑ o', K o o' = 1) :
    ∀ i, ∑ o', garbledLikelihood lik K i o' = 1 := by
  intro i
  simp only [garbledLikelihood]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hK, mul_one]
  exact hlik i

omit [Fintype O'] in
-- @node: experimentMarginal_garbledLikelihood
/-- Under the uniform prior on four states, [the marginal mass of a postprocessed
observation equals the sum of original observation masses times their
postprocessing weights to that observation](goal). -/
lemma experimentMarginal_garbledLikelihood (lik : Fin 4 → O → ℝ)
    (K : O → O' → ℝ) (o' : O') :
    experimentMarginal (garbledLikelihood lik K) o' =
      ∑ o, experimentMarginal lik o * K o o' := by
  simp only [experimentMarginal, garbledLikelihood]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro o _
  rw [← Finset.sum_mul]
  ring

omit [Fintype O'] in
-- @node: experimentPosterior_centered_garbledLikelihood
/-- If [the original likelihoods are nonnegative](hyp:hlik) and [postprocessing
weights are nonnegative](hyp:hK), then [a postprocessed observation's marginal mass
times the deviation of a state's posterior probability from one quarter equals the
sum of the original centered posterior probabilities weighted by their marginal
masses and postprocessing weights](goal). -/
lemma experimentPosterior_centered_garbledLikelihood
    (lik : Fin 4 → O → ℝ) (K : O → O' → ℝ)
    (hlik : ∀ i o, 0 ≤ lik i o) (hK : ∀ o o', 0 ≤ K o o')
    (o' : O') (i : Fin 4) :
    experimentMarginal (garbledLikelihood lik K) o' *
        (experimentPosterior (garbledLikelihood lik K) o' i - 1 / 4) =
      ∑ o, (experimentMarginal lik o * K o o') *
        (experimentPosterior lik o i - 1 / 4) := by
  rw [mul_sub, experimentMarginal_mul_posterior _
    (garbledLikelihood_nonneg lik K hlik hK), experimentMarginal_garbledLikelihood,
    Finset.sum_mul]
  simp only [garbledLikelihood, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro o _
  rw [← mul_assoc, ← experimentMarginal_mul_posterior lik hlik o i]
  ring

omit [Fintype O'] in
-- @node: experimentPosterior_centered_sq_garbledLikelihood
/-- If [the original likelihoods are nonnegative](hyp:hlik) and [postprocessing
weights are nonnegative](hyp:hK), then [a postprocessed observation's marginal mass
times the squared deviation of a state's posterior probability from one quarter
is at most the sum of the original squared deviations weighted by their marginal
masses and postprocessing weights](goal). -/
lemma experimentPosterior_centered_sq_garbledLikelihood
    (lik : Fin 4 → O → ℝ) (K : O → O' → ℝ)
    (hlik : ∀ i o, 0 ≤ lik i o) (hK : ∀ o o', 0 ≤ K o o')
    (o' : O') (i : Fin 4) :
    experimentMarginal (garbledLikelihood lik K) o' *
        (experimentPosterior (garbledLikelihood lik K) o' i - 1 / 4) ^ 2 ≤
      ∑ o, (experimentMarginal lik o * K o o') *
        (experimentPosterior lik o i - 1 / 4) ^ 2 := by
  let w := fun o => experimentMarginal lik o * K o o'
  let x := fun o => experimentPosterior lik o i - 1 / 4
  have hw (o) : 0 ≤ w o := mul_nonneg
    (mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ => hlik j o)) (hK o o')
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun o => w o * x o) (f := w) (g := fun o => w o * x o ^ 2)
    (fun o _ => hw o) (fun o _ => mul_nonneg (hw o) (sq_nonneg _))
    (fun o _ => by ring_nf; exact le_rfl)
  have hsum : ∑ o, w o = experimentMarginal (garbledLikelihood lik K) o' :=
    (experimentMarginal_garbledLikelihood lik K o').symm
  have hcenter : ∑ o, w o * x o =
      experimentMarginal (garbledLikelihood lik K) o' *
        (experimentPosterior (garbledLikelihood lik K) o' i - 1 / 4) :=
    (experimentPosterior_centered_garbledLikelihood lik K hlik hK o' i).symm
  rw [hsum, hcenter, mul_pow] at hcs
  have hm : 0 ≤ experimentMarginal (garbledLikelihood lik K) o' := by
    rw [← hsum]
    exact Finset.sum_nonneg fun o _ => hw o
  by_cases hpos : 0 < experimentMarginal (garbledLikelihood lik K) o'
  · apply (mul_le_mul_iff_right₀ hpos).mp
    nlinarith [hcs]
  · have hz : experimentMarginal (garbledLikelihood lik K) o' = 0 :=
      le_antisymm (le_of_not_gt hpos) hm
    rw [hz, zero_mul]
    exact Finset.sum_nonneg fun o _ => mul_nonneg (hw o) (sq_nonneg _)

-- @node: quadInfo_experimentLaw_centered
/-- For [nonnegative likelihoods](hyp:hlik), [quadratic information in the posterior
law equals four times the sum, over observations and states, of the observation's
marginal mass times the squared deviation of the posterior probability from one
quarter](goal). -/
lemma quadInfo_experimentLaw_centered (lik : Fin 4 → O → ℝ)
    (hlik : ∀ i o, 0 ≤ lik i o) :
    quadInfo (experimentLaw lik) =
      4 * ∑ o, ∑ i : Fin 4,
        experimentMarginal lik o * (experimentPosterior lik o i - 1 / 4) ^ 2 := by
  rw [quadInfo, integral_experimentLaw lik hlik]
  simp_rw [quadStat_eq_centered_sq _ (experimentPosterior_mem_simplex lik hlik _).2]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro o _
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

-- @node: quadInfo_garbledLikelihood_le
/-- If [the original likelihoods are nonnegative](hyp:hlik), [postprocessing weights
are nonnegative](hyp:hK), and [these weights sum to one for each original
observation](hyp:hKsum), then [postprocessing cannot increase quadratic information
in the posterior law](goal). -/
theorem quadInfo_garbledLikelihood_le (lik : Fin 4 → O → ℝ) (K : O → O' → ℝ)
    (hlik : ∀ i o, 0 ≤ lik i o) (hK : ∀ o o', 0 ≤ K o o')
    (hKsum : ∀ o, ∑ o', K o o' = 1) :
    quadInfo (experimentLaw (garbledLikelihood lik K)) ≤ quadInfo (experimentLaw lik) := by
  rw [quadInfo_experimentLaw_centered _ (garbledLikelihood_nonneg lik K hlik hK),
    quadInfo_experimentLaw_centered lik hlik]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ ≤ ∑ o', ∑ i : Fin 4, ∑ o,
        (experimentMarginal lik o * K o o') *
          (experimentPosterior lik o i - 1 / 4) ^ 2 := by
      apply Finset.sum_le_sum
      intro o' _
      exact Finset.sum_le_sum fun i _ =>
        experimentPosterior_centered_sq_garbledLikelihood lik K hlik hK o' i
    _ = _ := by
      conv_lhs =>
        enter [2, o']
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro o _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      conv_lhs =>
        enter [2, o']
        rw [mul_right_comm]
      rw [← Finset.mul_sum, hKsum, mul_one]

-- @node: experimentLaw_estimator_correlation_sq_le
/-- For [nonnegative likelihoods](hyp:hlik), [the squared marginal-weighted sum of
an observation statistic times a state's posterior deviation from one quarter is
at most one quarter of the posterior law's quadratic information times the
statistic's marginal-weighted second moment](goal). -/
lemma experimentLaw_estimator_correlation_sq_le (lik : Fin 4 → O → ℝ)
    (hlik : ∀ i o, 0 ≤ lik i o) (f : O → ℝ) (i : Fin 4) :
    (∑ o, ((1 / 4) * lik i o - experimentMarginal lik o / 4) * f o) ^ 2 ≤
      (quadInfo (experimentLaw lik) / 4) * ∑ o, experimentMarginal lik o * f o ^ 2 := by
  have hm (o : O) : 0 ≤ experimentMarginal lik o :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ => hlik j o)
  let x := fun o => experimentPosterior lik o i - 1 / 4
  have hcenter : ∀ o, ((1 / 4) * lik i o - experimentMarginal lik o / 4) * f o =
      experimentMarginal lik o * x o * f o := by
    intro o
    rw [← experimentMarginal_mul_posterior lik hlik o i]
    dsimp [x]
    ring
  simp_rw [hcenter]
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun o => experimentMarginal lik o * x o * f o)
    (f := fun o => experimentMarginal lik o * x o ^ 2)
    (g := fun o => experimentMarginal lik o * f o ^ 2)
    (fun o _ => mul_nonneg (hm o) (sq_nonneg _))
    (fun o _ => mul_nonneg (hm o) (sq_nonneg _))
    (fun o _ => by ring_nf; exact le_rfl)
  have hcoord : (∑ o, experimentMarginal lik o * x o ^ 2) ≤
      quadInfo (experimentLaw lik) / 4 := by
    rw [quadInfo_experimentLaw_centered lik hlik]
    simp only [mul_div_cancel_left₀ _ (by norm_num : (4 : ℝ) ≠ 0)]
    apply Finset.sum_le_sum
    intro o _
    exact Finset.single_le_sum
      (fun j _ => mul_nonneg (hm o) (sq_nonneg (experimentPosterior lik o j - 1 / 4)))
      (Finset.mem_univ i)
  exact hcs.trans (mul_le_mul_of_nonneg_right hcoord
    (Finset.sum_nonneg fun o _ => mul_nonneg (hm o) (sq_nonneg _)))

end OaiCapacityCriterionState
