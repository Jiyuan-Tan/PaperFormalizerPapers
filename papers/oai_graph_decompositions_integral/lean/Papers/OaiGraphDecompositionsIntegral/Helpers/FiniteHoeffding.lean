module
public import Causalean.Stat.FiniteDesign.FiniteDesignMeasure
public import Mathlib.Probability.Moments.SubGaussian

/-! # One-sided Hoeffding bounds for finite-design averages -/

public section

open Causalean.Experimentation.DesignBased MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Papers.OaiGraphDecompositionsIntegral

attribute [local instance] Classical.propDecidable

/-- Under a finite sampling design, suppose [the random variables are
independent](hyp:hind), [each takes values between zero and one](hyp:hb),
[each has expectation m](hyp:hm), and [a is nonnegative](hyp:ha). Then
[the probability that their sum exceeds the number of variables times m
by at least a is at most the exponential of −2a² divided by the number
of variables](goal). -/
-- @node: finiteDesign_hoeffding_upper
lemma finiteDesign_hoeffding_upper {Ω I : Type} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] [Fintype I] (D : FiniteDesign Ω)
    (X : I → Ω → ℝ) (hind : iIndepFun X D.toMeasure) (m a : ℝ)
    (hb : ∀ i z, X i z ∈ Set.Icc 0 1) (hm : ∀ i, D.E (X i) = m) (ha : 0 ≤ a) :
    D.Pr (fun z => (Fintype.card I : ℝ) * m + a ≤ ∑ i, X i z) ≤
      Real.exp (-2 * a ^ 2 / (Fintype.card I : ℝ)) := by
  have hcenter : iIndepFun (fun i z => X i z - m) D.toMeasure :=
    hind.comp (fun _ x => x - m) (fun _ => by fun_prop)
  have hsg (i : I) : HasSubgaussianMGF (fun z => X i z - m) (1 / 4) D.toMeasure := by
    have h := hasSubgaussianMGF_of_mem_Icc (μ := D.toMeasure) (a := 0) (b := 1)
      (measurable_of_finite (X i)).aemeasurable (Filter.Eventually.of_forall (hb i))
    norm_num [FiniteDesign.integral_toMeasure, hm i] at h ⊢
    exact h
  have htail := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    hcenter (c := fun _ => (1 / 4 : NNReal)) (s := Finset.univ) (fun i _ => hsg i) ha
  rw [FiniteDesign.toMeasure_real_setOf] at htail
  have hev : D.Pr (fun z => (Fintype.card I : ℝ) * m + a ≤ ∑ i, X i z) =
      D.Pr (fun z => a ≤ ∑ i, (X i z - m)) := by
    apply D.Pr_congr
    intro z
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    constructor <;> intro h <;> linarith
  rw [hev]
  convert htail using 1
  simp
  ring

/-- Under a finite sampling design, suppose [the random variables are
independent](hyp:hind), [each takes values between zero and one](hyp:hb),
[each has expectation m](hyp:hm), and [a is nonnegative](hyp:ha). Then
[the probability that their sum falls below the number of variables times m
by at least a is at most the exponential of −2a² divided by the number
of variables](goal). -/
-- @node: finiteDesign_hoeffding_lower
lemma finiteDesign_hoeffding_lower {Ω I : Type} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] [Fintype I] (D : FiniteDesign Ω)
    (X : I → Ω → ℝ) (hind : iIndepFun X D.toMeasure) (m a : ℝ)
    (hb : ∀ i z, X i z ∈ Set.Icc 0 1) (hm : ∀ i, D.E (X i) = m) (ha : 0 ≤ a) :
    D.Pr (fun z => (∑ i, X i z) ≤ (Fintype.card I : ℝ) * m - a) ≤
      Real.exp (-2 * a ^ 2 / (Fintype.card I : ℝ)) := by
  have hind' : iIndepFun (fun i z => 1 - X i z) D.toMeasure :=
    hind.comp (fun _ x => 1 - x) (fun _ => by fun_prop)
  have hb' (i : I) (z : Ω) : 1 - X i z ∈ Set.Icc (0 : ℝ) 1 := by
    have := hb i z
    constructor <;> linarith [this.1, this.2]
  have hm' (i : I) : D.E (fun z => 1 - X i z) = 1 - m := by
    rw [FiniteDesign.E_sub, FiniteDesign.E_const, hm i]
  have htail := finiteDesign_hoeffding_upper D (fun i z => 1 - X i z)
    hind' (1 - m) a hb' hm' ha
  refine le_trans (le_of_eq ?_) htail
  apply D.Pr_congr
  intro z
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  constructor <;> intro h <;> linarith

end Papers.OaiGraphDecompositionsIntegral
