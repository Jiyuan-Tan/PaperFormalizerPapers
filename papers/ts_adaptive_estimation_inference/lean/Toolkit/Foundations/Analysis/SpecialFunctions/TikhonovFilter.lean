module

public import Causalean.Estimation.NPIV.Operator.Complexification
public import Causalean.Stat.Concentration.Covering.EmpiricalPseudoMetric
public import Causalean.Stat.Sample
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
public import Mathlib.MeasureTheory.Function.FactorsThrough
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Toolkit.Foundations.Analysis.SpecialFunctions.TikhonovFilter

Scalar bounds for Tikhonov and iterated Tikhonov spectral filters
-/

public section

namespace Toolkit.Foundations.Analysis.SpecialFunctions

section

open MeasureTheory
open scoped InnerProductSpace

-- @node: iteratedResidual_qualification
/-- If [the spectral argument lies between zero and one, inclusive](hyp:hu),
[the penalty is positive](hyp:hlam), and [the source exponent is positive](hyp:hγ),
then [for every nonnegative integer iteration count, the spectral argument to the
source exponent times the residual filter to twice that count is at most the
penalty to the smaller of the source exponent and twice the count](goal). -/
lemma rpow_mul_div_add_pow_le_rpow_min {u lam γ : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (hlam : 0 < lam) (hγ : 0 < γ) (j : ℕ) :
    u ^ γ * (lam / (u + lam)) ^ (2 * j) ≤
      lam ^ min γ (2 * (j : ℝ)) := by
  have hd : 0 < u + lam := by linarith [hu.1]
  have hr0 : 0 ≤ lam / (u + lam) := div_nonneg hlam.le hd.le
  have hr1 : lam / (u + lam) ≤ 1 := (div_le_one hd).mpr (by linarith [hu.1])
  have hur : u * (lam / (u + lam)) ≤ lam := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hd).mpr
    nlinarith
  have hm : (0 : ℝ) ≤ 2 * (j : ℝ) := by positivity
  have hcast : (lam / (u + lam)) ^ (2 * j) =
      (lam / (u + lam)) ^ (2 * (j : ℝ)) := by norm_cast
  rw [hcast]
  by_cases hsmall : γ ≤ 2 * (j : ℝ)
  · rw [min_eq_left hsmall]
    calc
      u ^ γ * (lam / (u + lam)) ^ (2 * (j : ℝ)) ≤
          u ^ γ * (lam / (u + lam)) ^ γ := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge' hr0 hr1 hγ.le hsmall)
          (Real.rpow_nonneg hu.1 _)
      _ = (u * (lam / (u + lam))) ^ γ := (Real.mul_rpow hu.1 hr0).symm
      _ ≤ lam ^ γ := Real.rpow_le_rpow (mul_nonneg hu.1 hr0) hur hγ.le
  · have hlarge : 2 * (j : ℝ) ≤ γ := le_of_not_ge hsmall
    rw [min_eq_right hlarge]
    calc
      u ^ γ * (lam / (u + lam)) ^ (2 * (j : ℝ)) ≤
          u ^ (2 * (j : ℝ)) * (lam / (u + lam)) ^ (2 * (j : ℝ)) := by
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_ge' hu.1 hu.2 hm hlarge)
          (Real.rpow_nonneg hr0 _)
      _ = (u * (lam / (u + lam))) ^ (2 * (j : ℝ)) :=
        (Real.mul_rpow hu.1 hr0).symm
      _ ≤ lam ^ (2 * (j : ℝ)) := Real.rpow_le_rpow (mul_nonneg hu.1 hr0) hur hm

end

end Toolkit.Foundations.Analysis.SpecialFunctions
