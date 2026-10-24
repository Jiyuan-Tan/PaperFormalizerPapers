module

public import Papers.OaiLinearVarianceRandom.Helpers.RootExposure
public import Papers.OaiLinearVarianceRandom.Helpers.Potential
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Pathwise bounds for the occupation argument

The potential increments are nonnegative at every step, so their sum over
ordinary steps is bounded by the full telescoping sum. Nonordinary steps
are charged injectively to the root incidences in the capped exposure.
These are the deterministic bounds used after the conditional drift estimate.
-/

public section

noncomputable section
namespace Papers.OaiLinearVarianceRandom
open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {n : ℕ} {Ω : Type} [MeasurableSpace Ω]
set_option linter.unusedSectionVars false

-- @node: occupationTerm_bounds
/-- If [there are at least six variables](hyp:hn), then [the occupation term
lies between zero and one for every clause sequence, omitted index, time,
and outcome](goal). -/
lemma occupationTerm_bounds (hn : OmissionN n) (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i s : ℕ) (ω : Ω) :
    0 ≤ occupationTerm c0 Cseq i s ω ∧ occupationTerm c0 Cseq i s ω ≤ 1 := by
  classical
  have hp := killProcess_bounds hn c0 Cseq i s ω
  have hpow0 := Real.rpow_nonneg hp.1 beta
  have hpow1 := Real.rpow_le_one hp.1 hp.2 (show 0 ≤ beta by norm_num [beta])
  simp only [occupationTerm]
  split_ifs <;> simp_all

open Classical in
/-- If [the assignment dimension is at least three](hyp:hu) and [the integer
potential length is at least one](hyp:hd), then [the indicator that the
assignment set is nonempty times its killing probability to the three-halves
power is at most three times the square root of the potential length times
the expected potential increase from a uniform proper three-clause, plus
the potential length to the three-halves power divided by the cube of the
assignment dimension](goal). -/
-- @node: occupation_uniform_drift
lemma occupation_uniform_drift {u : ℕ} (hu : OneU u) (d : ℕ)
    (hd : PotentialD d) (S : Finset (Fin u → Bool)) :
    (if S.Nonempty then (1 : ℝ) else 0) * (killProb d S) ^ beta ≤
      3 * (d : ℝ) ^ (beta - 1) *
        (∫ C, potential d (survivors S C) - potential d S
          ∂(uniformClauseMeasure u 3)) +
      (d : ℝ) ^ beta * (u : ℝ) ^ (-3 : ℝ) := by
  let νj := fun j => Measure.pi (fun _ : Fin j => uniformClauseMeasure u 2)
  have hp := (potential_drift hu (uniformClauseMeasure u)
    (fun _ _ => rfl) d hd S νj (fun _ => rfl)
    (fun j => (νj j).prod (uniformClauseMeasure u 3)) ⟨rfl, fun _ => rfl⟩).2.2
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d from hd)
  have hid : (d : ℝ) ^ (beta - 1) * d = (d : ℝ) ^ beta := by
    rw [Real.rpow_sub hdpos, Real.rpow_one, div_mul_cancel₀ _ hdpos.ne']
  calc
    _ ≤ _ := hp
    _ = _ := by rw [← hid]; ring

-- @node: occupation_potential_monotone
/-- [For every fixed root clause, clause sequence, omitted index, and outcome,
the potential of the surviving nonroot assignments is nondecreasing in time
when evaluated at the fixed incidence parameter](goal). -/
lemma occupation_potential_monotone (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i : ℕ) (ω : Ω) :
    Monotone (fun s => potential (incidenceParam c0 Cseq i ω)
      (nonrootSolutions c0 Cseq i s ω)) := by
  intro a b hab
  exact potential_antitone _ (nonrootSolutions_antitone c0 Cseq i ω hab)

open Classical in
-- @node: occupation_ordinary_increments_le
/-- If [the starting time does not exceed the cap](hyp:hm), then [the sum of
potential increases at ordinary steps from that time up to the cap is at
most the incidence parameter](goal). -/
lemma occupation_ordinary_increments_le (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i m : ℕ) (hm : m ≤ capL n) (ω : Ω) :
    (∑ s ∈ (Finset.Ico m (capL n)).filter
        (fun s => isOrdinary c0 (Cseq (s + 1) ω)),
      (potential (incidenceParam c0 Cseq i ω) (nonrootSolutions c0 Cseq i (s + 1) ω) -
        potential (incidenceParam c0 Cseq i ω) (nonrootSolutions c0 Cseq i s ω))) ≤
      incidenceParam c0 Cseq i ω := by
  classical
  let P := fun s => potential (incidenceParam c0 Cseq i ω)
    (nonrootSolutions c0 Cseq i s ω)
  have hmono : Monotone P := occupation_potential_monotone c0 Cseq i ω
  calc
    _ ≤ ∑ s ∈ Finset.Ico m (capL n), (P (s + 1) - P s) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro s _ _
      exact sub_nonneg.mpr (hmono (Nat.le_succ s))
    _ = P (capL n) - P m := Finset.sum_Ico_sub P hm
    _ ≤ incidenceParam c0 Cseq i ω := by
      have hfinal := (potential_bounds (incidenceParam c0 Cseq i ω)
        (nonrootSolutions c0 Cseq i (capL n) ω)).2
      have hinitial := (potential_bounds (incidenceParam c0 Cseq i ω)
        (nonrootSolutions c0 Cseq i m ω)).1
      dsimp [P]
      linarith

open Classical in
-- @node: occupation_nonordinary_card_le
/-- If [the omitted index is no later than the starting time](hyp:him), then
[the number of nonordinary steps from that time up to the cap is at most
the total root-incidence count excluding the omitted clause](goal). -/
lemma occupation_nonordinary_card_le (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i m : ℕ) (him : i ≤ m) (ω : Ω) :
    ((Finset.Ico m (capL n)).filter
      (fun s => ¬ isOrdinary c0 (Cseq (s + 1) ω))).card ≤
      incidenceCount c0 Cseq i ω := by
  classical
  apply Finset.card_le_card_of_injOn (fun s => s + 1)
  · intro s hs
    dsimp only at *
    obtain ⟨hs, hnon⟩ := Finset.mem_filter.mp hs
    obtain ⟨hms, hsL⟩ := Finset.mem_Ico.mp hs
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, hsL⟩⟩, ?_⟩
    exact Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hnon)
  · intro a _ b _ hab
    dsimp only at hab
    omega

open Classical in
-- @node: occupation_nonordinary_sum_le
/-- If [there are at least six variables](hyp:hn) and [the omitted index is
no later than the starting time](hyp:him), then [the sum of occupation terms
at nonordinary steps from that time up to the cap is at most the total
root-incidence count excluding the omitted clause](goal). -/
lemma occupation_nonordinary_sum_le (hn : OmissionN n) (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i m : ℕ) (him : i ≤ m) (ω : Ω) :
    (∑ s ∈ (Finset.Ico m (capL n)).filter
      (fun s => ¬ isOrdinary c0 (Cseq (s + 1) ω)), occupationTerm c0 Cseq i s ω) ≤
      incidenceCount c0 Cseq i ω := by
  classical
  calc
    _ ≤ ∑ _s ∈ (Finset.Ico m (capL n)).filter
        (fun s => ¬ isOrdinary c0 (Cseq (s + 1) ω)), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro s _
      exact (occupationTerm_bounds hn c0 Cseq i s ω).2
    _ = (((Finset.Ico m (capL n)).filter
        (fun s => ¬ isOrdinary c0 (Cseq (s + 1) ω))).card : ℝ) := by simp
    _ ≤ incidenceCount c0 Cseq i ω := by
      exact_mod_cast occupation_nonordinary_card_le c0 Cseq i m him ω

-- @node: occupation_cap_error_le
/-- If [there are at least six variables](hyp:hn), then [the cap divided by
the cube of the number of nonroot variables is at most three](goal). -/
lemma occupation_cap_error_le (hn : OmissionN n) :
    (capL n : ℝ) * (nonrootCount n : ℝ) ^ (-3 : ℝ) ≤ 3 := by
  have hn6 : 6 ≤ n := hn
  have hu3 : (3 : ℝ) ≤ nonrootCount n := by
    exact_mod_cast (show 3 ≤ nonrootCount n by unfold nonrootCount; omega)
  have hnu : (n : ℝ) ≤ 2 * nonrootCount n := by
    exact_mod_cast (show n ≤ 2 * nonrootCount n by unfold nonrootCount; omega)
  have hu0 : 0 < (nonrootCount n : ℝ) := by linarith
  have hu2 : (9 : ℝ) ≤ (nonrootCount n : ℝ) ^ 2 := by nlinarith
  have hu3' : 9 * (nonrootCount n : ℝ) ≤ (nonrootCount n : ℝ) ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu2) hu0.le]
  rw [Real.rpow_neg hu0.le]
  norm_num only [Real.rpow_ofNat]
  apply (mul_inv_le_iff₀ (pow_pos hu0 3)).mpr
  have hcap : (capL n : ℝ) = 10 * n := by simp [capL]
  rw [hcap]
  nlinarith

-- @node: incidenceCount_le_rpow_beta
/-- [The root-incidence count is at most the three-halves power of the
incidence parameter, which is the larger of one and that count](goal). -/
lemma incidenceCount_le_rpow_beta (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i : ℕ) (ω : Ω) :
    (incidenceCount c0 Cseq i ω : ℝ) ≤ (incidenceParam c0 Cseq i ω : ℝ) ^ beta := by
  have hd : (1 : ℝ) ≤ incidenceParam c0 Cseq i ω := by
    exact_mod_cast (le_max_left 1 (incidenceCount c0 Cseq i ω))
  have hz : (incidenceCount c0 Cseq i ω : ℝ) ≤ incidenceParam c0 Cseq i ω := by
    exact_mod_cast (le_max_right 1 (incidenceCount c0 Cseq i ω))
  have hp := Real.rpow_le_rpow_of_exponent_le hd (show (1 : ℝ) ≤ beta by norm_num [beta])
  rw [Real.rpow_one] at hp
  exact hz.trans hp

-- @node: occupation_constant_bound
/-- If [there are at least six variables](hyp:hn), then [three times the
three-halves power of the incidence parameter, plus the cap times that power
divided by the cube of the nonroot count, plus the root-incidence count,
is at most seven times that power](goal). -/
lemma occupation_constant_bound (hn : OmissionN n) (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (i : ℕ) (ω : Ω) :
    3 * (incidenceParam c0 Cseq i ω : ℝ) ^ beta +
      (capL n : ℝ) * (incidenceParam c0 Cseq i ω : ℝ) ^ beta *
        (nonrootCount n : ℝ) ^ (-3 : ℝ) + incidenceCount c0 Cseq i ω ≤
      occupationK * (incidenceParam c0 Cseq i ω : ℝ) ^ beta := by
  have hc := occupation_cap_error_le hn
  have hz := incidenceCount_le_rpow_beta c0 Cseq i ω
  have hd0 := Real.rpow_nonneg (Nat.cast_nonneg (incidenceParam c0 Cseq i ω)) beta
  have hmul := mul_le_mul_of_nonneg_right hc hd0
  unfold occupationK
  nlinarith

end Papers.OaiLinearVarianceRandom
