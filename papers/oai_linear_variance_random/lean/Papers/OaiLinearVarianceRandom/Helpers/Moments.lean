module

public import Papers.OaiLinearVarianceRandom.Helpers.ClauseCounting
public import Papers.OaiLinearVarianceRandom.Helpers.MomentLaws
public import Mathlib.Probability.ProbabilityMassFunction.Binomial
public import Causalean.Mathlib.Probability.BernoulliMeasure

/-! # Uniform incidence and collision moments -/

@[expose] public section

noncomputable section
namespace Papers.OaiLinearVarianceRandom
open MeasureTheory ProbabilityTheory
open scoped BigOperators
set_option linter.unusedVariables false

open Classical in
/-- For [a fixed root clause](hyp:c0), [a sequence of random clauses](hyp:Cseq),
and [a clause index](hyp:j), the [collision event consists of outcomes where
that indexed clause contains literals on at least two root variables](goal). -/
def collisionEvent {n : ℕ} {Ω : Type} (c0 : ProperClause n)
    (Cseq : ℕ → Ω → ProperClause n) (j : ℕ) : Set Ω :=
  {ω | 2 ≤ (rootLiterals c0 (Cseq j ω)).card} -- @realizes J_j(event of meeting at least two roots)

open Classical in
/-- For [a fixed root clause](hyp:c0), the [root-incidence probability is the
probability that a uniformly sampled proper three-clause meets at least one
of its root variables](goal). -/
def hitProbability {n : ℕ} (c0 : ProperClause n) : ℝ :=
  (uniformClauseMeasure n 3).real {c | 1 ≤ (rootLiterals c0 c).card}
  -- @realizes p_{\rm hit}(uniform probability of meeting one or more roots)

open Classical in
/-- For [a fixed root clause](hyp:c0), the [root-collision probability is the
probability that a uniformly sampled proper three-clause meets at least two
of its root variables](goal). -/
def collisionProbability {n : ℕ} (c0 : ProperClause n) : ℝ :=
  (uniformClauseMeasure n 3).real {c | 2 ≤ (rootLiterals c0 c).card}
  -- @realizes p_{\rm coll}(uniform probability of meeting two or more roots)

-- @node: max_one_cube_le_exp
/-- For any nonnegative integer count, [the cube of the larger of one and
that count is at most six times the exponential of one times the exponential
of the count](goal). -/
lemma max_one_cube_le_exp (Z : ℕ) :
    ((max 1 Z : ℕ) : ℝ) ^ 3 ≤ 6 * Real.exp 1 * Real.exp (Z : ℝ) := by
  have hd : 0 ≤ ((max 1 Z : ℕ) : ℝ) := by positivity
  have hp := Real.pow_div_factorial_le_exp _ hd 3
  norm_num [Nat.factorial] at hp
  have hmax : ((max 1 Z : ℕ) : ℝ) ≤ 1 + (Z : ℝ) := by
    exact_mod_cast (show max 1 Z ≤ 1 + Z by omega)
  have he := Real.exp_le_exp.mpr hmax
  rw [Real.exp_add] at he
  simp only [Nat.cast_max, Nat.cast_one] at *
  nlinarith

open Classical in
/-- If [there are at least six variables](hyp:hn), [the positive-index clauses
are measurable, independent, and uniformly distributed](hyp:hlaw), and [the
fixed clause index is positive](hyp:hi), then [conditional on that clause
being the chosen root clause, the probability of at least two collisions
among the other clauses up to the cap is at most 810000 divided by the square
of the number of variables](goal). -/
-- @node: collisionCount_ge_two_le
lemma collisionCount_ge_two_le {n : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (hn : OmissionN n) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Cseq : ℕ → Ω → ProperClause n) (hlaw : IsUniformClauseProcess μ Cseq)
    (i : ℕ) (hi : 1 ≤ i) (c0 : ProperClause n) :
    (fixedClauseMeasure μ Cseq i c0).real {ω | 2 ≤ collisionCount c0 Cseq i ω} ≤
      810000 / (n : ℝ) ^ 2 := by
  classical
  let J := (Finset.Icc 1 (capL n)).erase i
  let ν := fixedClauseMeasure μ Cseq i c0
  haveI : IsProbabilityMeasure ν := fixedClauseMeasure_isProbabilityMeasure μ Cseq hlaw i hi c0
  let Q := fun c : ProperClause n => 2 ≤ (rootLiterals c0 c).card
  let q := (uniformClauseMeasure n 3).real {c | Q c}
  let F := fun a b : ℕ => if a = b then (∅ : Set Ω) else
    {ω | Q (Cseq a ω) ∧ Q (Cseq b ω)}
  have hJ : ∀ j ∈ J, 1 ≤ j ∧ j ≠ i := by
    intro j hj
    obtain ⟨hji, hj⟩ := Finset.mem_erase.mp hj
    exact ⟨(Finset.mem_Icc.mp hj).1, hji⟩
  have hsub : {ω | 2 ≤ collisionCount c0 Cseq i ω} ⊆
      ⋃ a ∈ J, ⋃ b ∈ J, F a b := by
    intro ω hω
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp
      (show 1 < (J.filter (fun j => Q (Cseq j ω))).card from hω)
    exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨(Finset.mem_filter.mp ha).1,
      Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨(Finset.mem_filter.mp hb).1,
        by simpa [F, hab] using
          And.intro (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2⟩⟩⟩⟩
  have hpair (a : ℕ) (ha : a ∈ J) (b : ℕ) (hb : b ∈ J) :
      ν.real (F a b) ≤ q ^ 2 := by
    by_cases hab : a = b
    · simp only [F, hab, if_true, measureReal_empty]
      positivity
    · exact le_of_eq (by
        dsimp [F]
        rw [if_neg hab]
        exact fixedClauseMeasure_pair_event μ Cseq hlaw i hi c0 a b (hJ a ha) (hJ b hb) hab Q)
  have hpairs : ν.real {ω | 2 ≤ collisionCount c0 Cseq i ω} ≤
      (J.card : ℝ) ^ 2 * q ^ 2 := by
    calc
      _ ≤ ν.real (⋃ a ∈ J, ⋃ b ∈ J, F a b) := measureReal_mono hsub (measure_ne_top ν _)
      _ ≤ ∑ a ∈ J, ν.real (⋃ b ∈ J, F a b) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ a ∈ J, ∑ b ∈ J, ν.real (F a b) := by
        apply Finset.sum_le_sum
        intro a ha
        exact measureReal_biUnion_finset_le _ _
      _ ≤ ∑ a ∈ J, ∑ b ∈ J, q ^ 2 := by
        apply Finset.sum_le_sum
        intro a ha
        exact Finset.sum_le_sum (fun b hb => hpair a ha b hb)
      _ = _ := by simp; ring
  have hN : (J.card : ℝ) ≤ 10 * (n : ℝ) := by
    exact_mod_cast ((Finset.card_erase_le).trans (by simp [capL] :
      (Finset.Icc 1 (capL n)).card ≤ 10 * n))
  have hq : q ≤ 90 / (n : ℝ) ^ 2 := root_collision_probability_le hn c0
  have hq0 : 0 ≤ q := measureReal_nonneg
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by unfold OmissionN at hn; omega : n ≠ 0)
  calc
    _ ≤ (J.card : ℝ) ^ 2 * q ^ 2 := hpairs
    _ ≤ (10 * (n : ℝ)) ^ 2 * (90 / (n : ℝ) ^ 2) ^ 2 := by
      gcongr
    _ = _ := by field_simp; ring

open Classical in
/-- If [there are at least six variables](hyp:hn), [the positive-index clauses
are measurable, independent, and uniformly distributed](hyp:hlaw), and [the
fixed clause index lies between one and the cap](hyp:hi), then, conditional on
that clause being the chosen root clause, [the third moment of the incidence
parameter is at most $6e\exp(720(e-1))$, and its three-halves moment restricted
to outcomes with a collision is at most $5400e^2\exp(720(e-1))/n$, where $n$ is
the number of variables](goal). -/
-- @node: incidence_integral_bounds
lemma incidence_integral_bounds {n : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (hn : OmissionN n) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Cseq : ℕ → Ω → ProperClause n) (hlaw : IsUniformClauseProcess μ Cseq)
    (i : ℕ) (hi : DelayIndex i (capL n)) (c0 : ProperClause n) :
    (∫ ω, (incidenceParam c0 Cseq i ω : ℝ) ^ 3
      ∂fixedClauseMeasure μ Cseq i c0) ≤
        6 * Real.exp 1 * Real.exp ((Real.exp 1 - 1) * 720) ∧
    (∫ ω, (incidenceParam c0 Cseq i ω : ℝ) ^ beta *
      (if 1 ≤ collisionCount c0 Cseq i ω then 1 else 0)
      ∂fixedClauseMeasure μ Cseq i c0) ≤
        (6 * Real.exp 1 * Real.exp 1 * Real.exp ((Real.exp 1 - 1) * 720) * 900) /
          (n : ℝ) := by
  classical
  let J := (Finset.Icc 1 (capL n)).erase i
  let ν := fixedClauseMeasure μ Cseq i c0
  let P := fun c : ProperClause n => 1 ≤ (rootLiterals c0 c).card
  let Q := fun c : ProperClause n => 2 ≤ (rootLiterals c0 c).card
  let p := (uniformClauseMeasure n 3).real {c | P c}
  let q := (uniformClauseMeasure n 3).real {c | Q c}
  let B := Real.exp ((Real.exp 1 - 1) * 720)
  let M := 6 * Real.exp 1
  have hp0 : 0 ≤ p := measureReal_nonneg
  have hq0 : 0 ≤ q := measureReal_nonneg
  have hB0 : 0 ≤ B := (Real.exp_pos _).le
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by unfold OmissionN at hn; omega : n ≠ 0)
  have hJ : ∀ j ∈ J, 1 ≤ j ∧ j ≠ i := by
    intro j hj
    obtain ⟨hji, hj⟩ := Finset.mem_erase.mp hj
    exact ⟨(Finset.mem_Icc.mp hj).1, hji⟩
  have hN : (J.card : ℝ) ≤ 10 * (n : ℝ) := by
    exact_mod_cast ((Finset.card_erase_le).trans (by simp [capL] :
      (Finset.Icc 1 (capL n)).card ≤ 10 * n))
  have hNE : J.Nonempty := by
    have hc : J.card = capL n - 1 := by
      dsimp [J]
      rw [Finset.card_erase_of_mem (Finset.mem_Icc.mpr hi)]
      simp
    apply Finset.card_pos.mp
    rw [hc]
    unfold capL OmissionN at *
    omega
  obtain ⟨a0, ha0⟩ := hNE
  let a : J := ⟨a0, ha0⟩
  have hp : p ≤ 72 / (n : ℝ) := root_hit_probability_le hn c0
  have hq : q ≤ 90 / (n : ℝ) ^ 2 := root_collision_probability_le hn c0
  have hmean : (J.card : ℝ) * p ≤ 720 := by
    calc
      _ ≤ (10 * (n : ℝ)) * (72 / (n : ℝ)) := mul_le_mul hN hp hp0 (by positivity)
      _ = _ := by field_simp; ring
  have hmean' : ((J.card - 1 : ℕ) : ℝ) * p ≤ 720 :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le J.card 1) hp0).trans hmean
  have hint : Integrable (fun ω => Real.exp (incidenceCount c0 Cseq i ω : ℝ)) ν := by
    simpa only [ν, incidenceCount, J, P] using fixedClauseMeasure_integrable_count_mark μ Cseq hlaw i hi.1 c0 J hJ P a
      (fun z _ => Real.exp (z : ℝ))
  have hexp : (∫ ω, Real.exp (incidenceCount c0 Cseq i ω : ℝ) ∂ν) ≤ B := by
    have heq := fixedClauseMeasure_exp_count μ Cseq hlaw i hi.1 c0 J hJ P 1
    simp only [one_mul] at heq
    have heq' : (∫ ω, Real.exp (incidenceCount c0 Cseq i ω : ℝ) ∂ν) =
        (1 + (Real.exp 1 - 1) * p) ^ J.card := by
      simpa only [ν, incidenceCount, J, P, p] using heq
    rw [heq']
    exact binomial_exp_moment_le J.card p 720 hp0 hmean
  have hintmark (a : J) : Integrable (fun ω =>
      Real.exp (incidenceCount c0 Cseq i ω : ℝ) * (if Q (Cseq a ω) then 1 else 0)) ν := by
    simpa only [ν, incidenceCount, J, P] using fixedClauseMeasure_integrable_count_mark μ Cseq hlaw i hi.1 c0 J hJ P a
      (fun z c => Real.exp (z : ℝ) * (if Q c then 1 else 0))
  have hmark (a : J) : (∫ ω,
      Real.exp (incidenceCount c0 Cseq i ω : ℝ) * (if Q (Cseq a ω) then 1 else 0) ∂ν) ≤
      Real.exp 1 * q * B := by
    have heq := fixedClauseMeasure_exp_count_marked μ Cseq hlaw i hi.1 c0 J hJ P Q
      (fun c hc => by dsimp [Q, P] at *; omega) a 1
    simp only [one_mul] at heq
    have heq' : (∫ ω, Real.exp (incidenceCount c0 Cseq i ω : ℝ) *
        (if Q (Cseq a ω) then 1 else 0) ∂ν) =
        (Real.exp 1 * q) * (1 + (Real.exp 1 - 1) * p) ^ (J.card - 1) := by
      convert heq using 1
      apply integral_congr_ae
      filter_upwards [] with ω
      by_cases hQ : Q (Cseq a ω) <;> simp only [hQ, if_true, if_false, mul_one,
        mul_zero, incidenceCount, J, P]
    rw [heq']
    exact mul_le_mul_of_nonneg_left (binomial_exp_moment_le _ p 720 hp0 hmean')
      (mul_nonneg (Real.exp_pos _).le hq0)
  have hNq : (J.card : ℝ) * q ≤ 900 / (n : ℝ) := by
    calc
      _ ≤ (10 * (n : ℝ)) * (90 / (n : ℝ) ^ 2) := mul_le_mul hN hq hq0 (by positivity)
      _ = _ := by field_simp; ring
  constructor
  · calc
      _ ≤ ∫ ω, M * Real.exp (incidenceCount c0 Cseq i ω : ℝ) ∂ν := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun ω => by positivity))
          (hint.const_mul M)
        exact Filter.Eventually.of_forall fun ω => max_one_cube_le_exp _
      _ = M * ∫ ω, Real.exp (incidenceCount c0 Cseq i ω : ℝ) ∂ν := integral_const_mul _ _
      _ ≤ M * B := mul_le_mul_of_nonneg_left hexp hM0
  · have hpoint (ω : Ω) :
        (incidenceParam c0 Cseq i ω : ℝ) ^ beta *
          (if 1 ≤ collisionCount c0 Cseq i ω then 1 else 0) ≤
        M * ∑ a : J, Real.exp (incidenceCount c0 Cseq i ω : ℝ) *
          (if Q (Cseq a ω) then 1 else 0) := by
      have hsum0 : 0 ≤ ∑ a : J, Real.exp (incidenceCount c0 Cseq i ω : ℝ) *
          (if Q (Cseq a ω) then 1 else 0) := by
        apply Finset.sum_nonneg
        intro a ha
        positivity
      by_cases hV : 1 ≤ collisionCount c0 Cseq i ω
      · obtain ⟨j, hj⟩ := Finset.card_pos.mp
          (show 0 < (J.filter (fun j => Q (Cseq j ω))).card from hV)
        let a : J := ⟨j, (Finset.mem_filter.mp hj).1⟩
        have hQa : Q (Cseq a ω) := (Finset.mem_filter.mp hj).2
        have hsum := Finset.single_le_sum
          (s := (Finset.univ : Finset J))
          (f := fun a : J => Real.exp (incidenceCount c0 Cseq i ω : ℝ) *
            (if Q (Cseq a ω) then 1 else 0))
          (fun b _ => by positivity) (Finset.mem_univ a)
        simp only [hQa, if_true, mul_one] at hsum
        rw [if_pos hV, mul_one]
        have hd : 1 ≤ (incidenceParam c0 Cseq i ω : ℝ) := by
          exact_mod_cast (le_max_left 1 (incidenceCount c0 Cseq i ω))
        calc
          _ ≤ (incidenceParam c0 Cseq i ω : ℝ) ^ 3 := by
            have h := Real.rpow_le_rpow_of_exponent_le hd
              (show beta ≤ (3 : ℝ) by norm_num [beta])
            simpa only [Real.rpow_ofNat] using h
          _ ≤ M * Real.exp (incidenceCount c0 Cseq i ω : ℝ) := max_one_cube_le_exp _
          _ ≤ _ := mul_le_mul_of_nonneg_left hsum hM0
      · rw [if_neg hV, mul_zero]
        exact mul_nonneg hM0 hsum0
    calc
      _ ≤ ∫ ω, M * ∑ a : J, Real.exp (incidenceCount c0 Cseq i ω : ℝ) *
          (if Q (Cseq a ω) then 1 else 0) ∂ν := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun ω => by positivity))
          ((integrable_finset_sum _ (fun a _ => hintmark a)).const_mul M)
        exact Filter.Eventually.of_forall hpoint
      _ = M * ∑ a : J, ∫ ω, Real.exp (incidenceCount c0 Cseq i ω : ℝ) *
          (if Q (Cseq a ω) then 1 else 0) ∂ν := by
        rw [integral_const_mul, integral_finset_sum _ (fun a _ => hintmark a)]
      _ ≤ M * ∑ a : J, Real.exp 1 * q * B :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => hmark a)) hM0
      _ = (M * Real.exp 1 * B) * ((J.card : ℝ) * q) := by simp; ring
      _ ≤ (M * Real.exp 1 * B) * (900 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hNq (by positivity)
      _ = _ := by dsimp [M, B]; ring

open Classical in
-- @node: lem:moments
/-- [There is a positive universal constant such that, for every dimension
with at least six variables, every positive index up to the cap, every
probability space carrying measurable independent uniform proper
three-clauses, and every fixed root clause, conditioning on that indexed
clause gives a third incidence-parameter moment bounded by the constant,
a three-halves incidence-parameter moment restricted to collisions bounded
by the constant divided by the dimension, and a probability of two or more
collisions bounded by the constant divided by the dimension squared](goal). -/
lemma incidence_moments_bound :
    ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, OmissionN n →
      ∀ i : ℕ, MomentsRange n i →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (Cseq : ℕ → Ω → ProperClause n), IsUniformClauseProcess μ Cseq →
        ∀ c0 : ProperClause n,
        (∫ ω, (incidenceParam c0 Cseq i ω : ℝ) ^ 3
          ∂(fixedClauseMeasure μ Cseq i c0)) ≤ A ∧
        (∫ ω, (incidenceParam c0 Cseq i ω : ℝ) ^ beta *
          (if 1 ≤ collisionCount c0 Cseq i ω then 1 else 0)
          ∂(fixedClauseMeasure μ Cseq i c0)) ≤ A / n ∧
        (fixedClauseMeasure μ Cseq i c0).real {ω | 2 ≤ collisionCount c0 Cseq i ω} ≤
          A / (n : ℝ) ^ 2 := by
  let B := Real.exp ((Real.exp 1 - 1) * 720)
  let A₁ := 6 * Real.exp 1 * B
  let A₂ := 6 * Real.exp 1 * Real.exp 1 * B * 900
  have hA₁ : 0 ≤ A₁ := by dsimp [A₁, B]; positivity
  have hA₂ : 0 ≤ A₂ := by dsimp [A₂, B]; positivity
  refine ⟨A₁ + A₂ + 810001, by positivity, ?_⟩
  intro n hn i hi Ω _ μ _ Cseq hlaw c0
  have hbounds := incidence_integral_bounds hn μ Cseq hlaw i ⟨hi.2.1, hi.2.2⟩ c0
  refine ⟨hbounds.1.trans ?_, hbounds.2.trans ?_,
    (collisionCount_ge_two_le hn μ Cseq hlaw i hi.2.1 c0).trans ?_⟩
  · change A₁ ≤ A₁ + A₂ + 810001
    linarith
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    change A₂ ≤ A₁ + A₂ + 810001
    linarith
  · apply div_le_div_of_nonneg_right _ (sq_nonneg (n : ℝ))
    linarith

end Papers.OaiLinearVarianceRandom
