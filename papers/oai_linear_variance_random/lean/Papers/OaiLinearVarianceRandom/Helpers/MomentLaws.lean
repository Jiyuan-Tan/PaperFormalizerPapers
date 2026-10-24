module

public import Papers.OaiLinearVarianceRandom.Helpers.HiddenClauses
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Finite product laws used by the incidence moment estimates -/

public section

noncomputable section
namespace Papers.OaiLinearVarianceRandom
open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {n : ℕ} {Ω : Type} [MeasurableSpace Ω]

open Classical in
/-- For [an independent uniform clause process](hyp:hlaw) and [a positive
omitted index](hyp:hi), [conditioning the clause at that index to equal any
fixed reference clause defines a probability measure](goal). -/
-- @node: fixedClauseMeasure_isProbabilityMeasure
lemma fixedClauseMeasure_isProbabilityMeasure
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Cseq : ℕ → Ω → ProperClause n)
    (hlaw : IsUniformClauseProcess μ Cseq) (i : ℕ) (hi : 1 ≤ i)
    (c0 : ProperClause n) : IsProbabilityMeasure (fixedClauseMeasure μ Cseq i c0) := by
  apply cond_isProbabilityMeasure
  change μ (Cseq i ⁻¹' {c0}) ≠ 0
  rw [← Measure.map_apply (hlaw.1 i hi) (measurableSet_singleton c0), hlaw.2.2 i hi]
  haveI : Nonempty (ProperClause n) := ⟨c0⟩
  simp [uniformClauseMeasure, uniformOn_univ, Measure.count_singleton,
    ENNReal.div_ne_zero]

open Classical in
/-- For [an independent uniform clause process](hyp:hlaw), [a positive omitted
index](hyp:hi), and [a finite set of positive indices different from the omitted
index](hyp:hJ), [the joint distribution of the selected clauses under the law
fixing the omitted clause is the product of their uniform clause laws](goal). -/
-- @node: fixedClauseMeasure_joint_map
lemma fixedClauseMeasure_joint_map
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Cseq : ℕ → Ω → ProperClause n)
    (hlaw : IsUniformClauseProcess μ Cseq) (i : ℕ) (hi : 1 ≤ i)
    (c0 : ProperClause n) (J : Finset ℕ)
    (hJ : ∀ j ∈ J, 1 ≤ j ∧ j ≠ i) :
    (fixedClauseMeasure μ Cseq i c0).map (fun ω (j : J) => Cseq j ω) =
      Measure.pi (fun _ : J => uniformClauseMeasure n 3) := by
  haveI : Nonempty (ProperClause n) := ⟨c0⟩
  haveI : IsProbabilityMeasure (uniformClauseMeasure n 3) := by
    unfold uniformClauseMeasure
    infer_instance
  have hm : Measurable (fun ω (j : J) => Cseq j ω) := by
    apply measurable_pi_lambda
    intro j
    exact hlaw.1 _ (hJ _ j.property).1
  apply Measure.ext_of_singleton
  intro cs
  rw [Measure.map_apply hm (measurableSet_singleton cs), Measure.pi_singleton]
  convert fixedClauseMeasure_joint_mass μ Cseq hlaw i hi c0 J hJ
    (fun j => {cs j}) using 1
  congr 1
  ext ω
  simp [funext_iff]

open Classical in
/-- For [an independent uniform clause process](hyp:hlaw), [a positive omitted
index](hyp:hi), and [a finite set of positive indices different from the omitted
index](hyp:hJ), [every real function of the selected clause vector is integrable
under the law fixing the omitted clause](goal). -/
-- @node: fixedClauseMeasure_integrable_vector
lemma fixedClauseMeasure_integrable_vector
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Cseq : ℕ → Ω → ProperClause n)
    (hlaw : IsUniformClauseProcess μ Cseq) (i : ℕ) (hi : 1 ≤ i)
    (c0 : ProperClause n) (J : Finset ℕ)
    (hJ : ∀ j ∈ J, 1 ≤ j ∧ j ≠ i) (f : (J → ProperClause n) → ℝ) :
    Integrable (fun ω => f (fun j : J => Cseq j ω))
      (fixedClauseMeasure μ Cseq i c0) := by
  haveI : Nonempty (ProperClause n) := ⟨c0⟩
  haveI : IsProbabilityMeasure (uniformClauseMeasure n 3) := by
    unfold uniformClauseMeasure
    infer_instance
  have hm : Measurable (fun ω (j : J) => Cseq j ω) := by
    apply measurable_pi_lambda
    intro j
    exact hlaw.1 _ (hJ _ j.property).1
  apply (integrable_map_measure (measurable_of_finite f).aestronglyMeasurable
    hm.aemeasurable).mp
  rw [fixedClauseMeasure_joint_map μ Cseq hlaw i hi c0 J hJ]
  exact Integrable.of_finite

open Classical in
/-- For [an independent uniform clause process](hyp:hlaw), [a positive omitted
index](hyp:hi), and [a finite set of positive indices different from the omitted
index](hyp:hJ), [the expectation under the law fixing the omitted clause of a
product of real functions, one per selected clause, equals the product of their
expectations under the uniform clause law](goal). -/
-- @node: fixedClauseMeasure_integral_prod
lemma fixedClauseMeasure_integral_prod
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Cseq : ℕ → Ω → ProperClause n)
    (hlaw : IsUniformClauseProcess μ Cseq) (i : ℕ) (hi : 1 ≤ i)
    (c0 : ProperClause n) (J : Finset ℕ)
    (hJ : ∀ j ∈ J, 1 ≤ j ∧ j ≠ i) (f : J → ProperClause n → ℝ) :
    (∫ ω, ∏ j : J, f j (Cseq j ω) ∂fixedClauseMeasure μ Cseq i c0) =
      ∏ j : J, ∫ c, f j c ∂uniformClauseMeasure n 3 := by
  haveI : Nonempty (ProperClause n) := ⟨c0⟩
  haveI : IsProbabilityMeasure (uniformClauseMeasure n 3) := by
    unfold uniformClauseMeasure
    infer_instance
  have hm : Measurable (fun ω (j : J) => Cseq j ω) := by
    apply measurable_pi_lambda
    intro j
    exact hlaw.1 _ (hJ _ j.property).1
  rw [← integral_map hm.aemeasurable
    (measurable_of_finite (fun cs : J → ProperClause n => ∏ j, f j (cs j))).aestronglyMeasurable,
    fixedClauseMeasure_joint_map μ Cseq hlaw i hi c0 J hJ,
    integral_fintype_prod_eq_prod]

open Classical in
/-- [The number of elements satisfying a predicate among all members of a
finite set, regarded as a separate type, equals the number obtained by filtering
the original finite set by that predicate](goal). -/
-- @node: filter_card_subtype_univ
lemma filter_card_subtype_univ {A : Type*} (J : Finset A) (P : A → Prop) :
    ((Finset.univ : Finset J).filter (fun j => P j.val)).card = (J.filter P).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_coe_sort J (fun j => if P j then 1 else 0)

open Classical in
/-- For [an independent uniform clause process](hyp:hlaw), [a positive omitted
index](hyp:hi), and [a finite set of positive indices different from the omitted
index](hyp:hJ), [every real function of the number of selected clauses satisfying
a predicate and of the clause at one distinguished selected index is integrable
under the law fixing the omitted clause](goal). -/
-- @node: fixedClauseMeasure_integrable_count_mark
lemma fixedClauseMeasure_integrable_count_mark
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Cseq : ℕ → Ω → ProperClause n)
    (hlaw : IsUniformClauseProcess μ Cseq) (i : ℕ) (hi : 1 ≤ i)
    (c0 : ProperClause n) (J : Finset ℕ)
    (hJ : ∀ j ∈ J, 1 ≤ j ∧ j ≠ i) (P : ProperClause n → Prop)
    (a : J) (f : ℕ → ProperClause n → ℝ) :
    Integrable (fun ω => f ((J.filter (fun j => P (Cseq j ω))).card) (Cseq a ω))
      (fixedClauseMeasure μ Cseq i c0) := by
  convert fixedClauseMeasure_integrable_vector μ Cseq hlaw i hi c0 J hJ
      (fun cs => f ((Finset.univ.filter (fun j : J => P (cs j))).card) (cs a)) using 1
  funext ω
  rw [filter_card_subtype_univ J (fun j => P (Cseq j ω))]

/-- If [p is nonnegative](hyp:hp) and [N times p is at most B](hyp:hmean), then
[the N-th power of one plus p times the difference between e and one is at most
the exponential of B times the difference between e and one](goal). -/
-- @node: binomial_exp_moment_le
lemma binomial_exp_moment_le (N : ℕ) (p B : ℝ) (hp : 0 ≤ p)
    (hmean : (N : ℝ) * p ≤ B) :
    (1 + (Real.exp 1 - 1) * p) ^ N ≤ Real.exp ((Real.exp 1 - 1) * B) := by
  have he : 0 ≤ Real.exp 1 - 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  calc
    _ ≤ Real.exp ((Real.exp 1 - 1) * p) ^ N :=
      pow_le_pow_left₀ (by positivity) (by simpa [add_comm] using
        (Real.add_one_le_exp ((Real.exp 1 - 1) * p))) N
    _ = Real.exp ((Real.exp 1 - 1) * ((N : ℝ) * p)) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hmean he)

open Classical in
/-- For [a measurable event defined by a predicate](hyp:hP), [the expectation
of the exponential of t times its indicator equals one plus the event's
probability times the difference between the exponential of t and one](goal). -/
-- @node: integral_exp_indicator
lemma integral_exp_indicator {A : Type*} [MeasurableSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν] (P : A → Prop)
    (hP : MeasurableSet {a | P a}) (t : ℝ) :
    (∫ a, Real.exp (if P a then t else 0) ∂ν) =
      1 + (Real.exp t - 1) * ν.real {a | P a} := by
  have heq : (fun a => Real.exp (if P a then t else 0)) =
      (fun a => 1 + (Real.exp t - 1) *
        ({a | P a}.indicator (fun _ => (1 : ℝ))) a) := by
    funext a
    by_cases h : P a <;> simp [h]
  rw [heq, integral_add (integrable_const 1)
    (((integrable_const 1).indicator hP).const_mul _), integral_const,
    integral_const_mul, integral_indicator hP, setIntegral_const]
  simp

open Classical in
/-- For [an independent uniform clause process](hyp:hlaw), [a positive omitted
index](hyp:hi), and [a finite set of positive indices different from the omitted
index](hyp:hJ), [the expectation under the law fixing the omitted clause of the
exponential of t times the number of selected clauses satisfying a predicate
equals one plus the uniform probability of that predicate times the difference
between the exponential of t and one, all raised to the number of selected
indices](goal). -/
-- @node: fixedClauseMeasure_exp_count
lemma fixedClauseMeasure_exp_count
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Cseq : ℕ → Ω → ProperClause n)
    (hlaw : IsUniformClauseProcess μ Cseq) (i : ℕ) (hi : 1 ≤ i)
    (c0 : ProperClause n) (J : Finset ℕ)
    (hJ : ∀ j ∈ J, 1 ≤ j ∧ j ≠ i) (P : ProperClause n → Prop) (t : ℝ) :
    (∫ ω, Real.exp (t * ((J.filter (fun j => P (Cseq j ω))).card : ℝ))
      ∂fixedClauseMeasure μ Cseq i c0) =
      (1 + (Real.exp t - 1) * (uniformClauseMeasure n 3).real {c | P c}) ^
        J.card := by
  haveI : Nonempty (ProperClause n) := ⟨c0⟩
  haveI : IsProbabilityMeasure (uniformClauseMeasure n 3) := by
    unfold uniformClauseMeasure
    infer_instance
  have heq (ω : Ω) :
      Real.exp (t * ((J.filter (fun j => P (Cseq j ω))).card : ℝ)) =
        ∏ j : J, Real.exp (if P (Cseq j ω) then t else 0) := by
    rw [← Real.exp_sum]
    congr 1
    rw [show (∑ j : J, if P (Cseq j ω) then t else 0) =
      ∑ j ∈ J, if P (Cseq j ω) then t else 0 from
        Finset.sum_coe_sort J (fun j => if P (Cseq j ω) then t else 0)]
    simp [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  simp_rw [heq]
  rw [fixedClauseMeasure_integral_prod μ Cseq hlaw i hi c0 J hJ
    (fun _ c => Real.exp (if P c then t else 0))]
  simp_rw [integral_exp_indicator _ P (by trivial) t]
  simp

open Classical in
/-- For [an independent uniform clause process](hyp:hlaw), [a positive omitted
index](hyp:hi), and [a finite set of positive indices different from the omitted
index](hyp:hJ), suppose [every clause satisfying Q also satisfies P](hyp:hQP).
Then [the expectation under the law fixing the omitted clause of the exponential
of t times the count of P, multiplied by the indicator of Q at a distinguished
selected index, equals the exponential of t times the uniform probability of Q,
times the power with exponent one less than the number of selected indices of
one plus the uniform probability of P times the difference between the
exponential of t and one](goal). -/
-- @node: fixedClauseMeasure_exp_count_marked
lemma fixedClauseMeasure_exp_count_marked
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Cseq : ℕ → Ω → ProperClause n)
    (hlaw : IsUniformClauseProcess μ Cseq) (i : ℕ) (hi : 1 ≤ i)
    (c0 : ProperClause n) (J : Finset ℕ)
    (hJ : ∀ j ∈ J, 1 ≤ j ∧ j ≠ i) (P Q : ProperClause n → Prop)
    (hQP : ∀ c, Q c → P c) (a : J) (t : ℝ) :
    (∫ ω, Real.exp (t * ((J.filter (fun j => P (Cseq j ω))).card : ℝ)) *
      (if Q (Cseq a ω) then 1 else 0) ∂fixedClauseMeasure μ Cseq i c0) =
      (Real.exp t * (uniformClauseMeasure n 3).real {c | Q c}) *
      (1 + (Real.exp t - 1) * (uniformClauseMeasure n 3).real {c | P c}) ^
        (J.card - 1) := by
  haveI : Nonempty (ProperClause n) := ⟨c0⟩
  haveI : IsProbabilityMeasure (uniformClauseMeasure n 3) := by
    unfold uniformClauseMeasure
    infer_instance
  let f : J → ProperClause n → ℝ := fun j c =>
    Real.exp (if P c then t else 0) * (if j = a then (if Q c then 1 else 0) else 1)
  have heq (ω : Ω) :
      Real.exp (t * ((J.filter (fun j => P (Cseq j ω))).card : ℝ)) *
        (if Q (Cseq a ω) then 1 else 0) = ∏ j : J, f j (Cseq j ω) := by
    simp only [f, Finset.prod_mul_distrib, Finset.prod_ite_eq,
      Finset.prod_ite_eq', Finset.mem_univ, if_true]
    congr 1
    rw [← Real.exp_sum]
    congr 1
    rw [show (∑ j : J, if P (Cseq j ω) then t else 0) =
      ∑ j ∈ J, if P (Cseq j ω) then t else 0 from
        Finset.sum_coe_sort J (fun j => if P (Cseq j ω) then t else 0)]
    simp [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  simp_rw [heq]
  rw [fixedClauseMeasure_integral_prod μ Cseq hlaw i hi c0 J hJ f]
  have hfa : (∫ c, f a c ∂uniformClauseMeasure n 3) =
      Real.exp t * (uniformClauseMeasure n 3).real {c | Q c} := by
    have hf : f a = fun c => Real.exp t *
        ({c | Q c}.indicator (fun _ => (1 : ℝ))) c := by
      funext c
      by_cases h : Q c
      · simp [f, h, hQP c h]
      · simp [f, h]
    rw [hf, integral_const_mul, integral_indicator (by trivial), setIntegral_const]
    simp [mul_comm]
  rw [← Finset.mul_prod_erase Finset.univ (fun j => ∫ c, f j c
    ∂uniformClauseMeasure n 3) (Finset.mem_univ a), hfa]
  congr 1
  have hfother : ∀ j ∈ (Finset.univ : Finset J).erase a,
      (∫ c, f j c ∂uniformClauseMeasure n 3) =
      1 + (Real.exp t - 1) * (uniformClauseMeasure n 3).real {c | P c} := by
    intro j hj
    simp only [f, (Finset.mem_erase.mp hj).1, if_false, mul_one]
    exact integral_exp_indicator _ P (by trivial) t
  rw [Finset.prod_congr rfl hfother]
  simp

open Classical in
/-- For [an independent uniform clause process](hyp:hlaw) and [a positive
omitted index](hyp:hi), if [the first selected index is positive and differs from
the omitted index](hyp:ha), [the second selected index is positive and differs
from the omitted index](hyp:hb), and [the two selected indices are
distinct](hyp:hab), then [the probability under the law fixing the omitted
clause that both selected clauses satisfy Q is the square of the uniform
clause probability of Q](goal). -/
-- @node: fixedClauseMeasure_pair_event
lemma fixedClauseMeasure_pair_event
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Cseq : ℕ → Ω → ProperClause n)
    (hlaw : IsUniformClauseProcess μ Cseq) (i : ℕ) (hi : 1 ≤ i)
    (c0 : ProperClause n) (a b : ℕ) (ha : 1 ≤ a ∧ a ≠ i)
    (hb : 1 ≤ b ∧ b ≠ i) (hab : a ≠ b) (Q : ProperClause n → Prop) :
    (fixedClauseMeasure μ Cseq i c0).real {ω | Q (Cseq a ω) ∧ Q (Cseq b ω)} =
      ((uniformClauseMeasure n 3).real {c | Q c}) ^ 2 := by
  have hJ : ∀ j ∈ ({a, b} : Finset ℕ), 1 ≤ j ∧ j ≠ i := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl <;> assumption
  have h := fixedClauseMeasure_joint_mass μ Cseq hlaw i hi c0 {a, b} hJ
    (fun _ => {c | Q c})
  have hevent : {ω | ∀ j : ({a, b} : Finset ℕ), Cseq j ω ∈ {c | Q c}} =
      {ω | Q (Cseq a ω) ∧ Q (Cseq b ω)} := by
    ext ω
    simp [Subtype.forall, or_imp, forall_and]
  rw [hevent] at h
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_coe] at h
  simp [hab] at h
  simp only [measureReal_def, h, ENNReal.toReal_pow]

end Papers.OaiLinearVarianceRandom
