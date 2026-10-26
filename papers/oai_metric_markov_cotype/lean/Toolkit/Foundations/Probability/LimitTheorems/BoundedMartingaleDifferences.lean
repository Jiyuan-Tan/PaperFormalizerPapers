module

public import Causalean.Stat.Limit.Modes
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Data.ENNReal.Holder
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.NNReal.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.SetLike.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.AtTopBot.Field
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Max
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Martingale.Convergence
public import Mathlib.Probability.Process.Filtration
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.Separation.GDelta
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real
public import StatLean.TimeSeries.ForMathlib.Probability.MartingaleCLT.BrownCLT

/-!
# Bounded martingale differences: second moments and a central limit theorem

Two facts about a sequence of real martingale differences on a discrete
filtration, with no further structure on the process:

* `integral_sq_sum_martingaleDifferences`: square-integrable martingale
  differences are orthogonal, so the second moment of a finite sum is the sum of
  the second moments.
* `tendstoInDistribution_sum_div_sqrt_of_bounded_martingaleDifferences`: uniformly
  bounded martingale differences whose averaged conditional second moments
  converge in probability to a nonnegative number satisfy the central limit
  theorem with that variance; variance zero gives the point mass at zero.

StatLean's `mds_clt_sequence` already proves characteristic-function convergence
with arbitrary nonnegative variance, including zero. The second result supplies
its Lindeberg condition from the common bound and converts
characteristic-function convergence to Mathlib convergence in distribution.

Reference: Hall and Heyde, Martingale Limit Theory and Its Application,
Corollary 3.1 (Brown's martingale central limit theorem).

The module also proves almost-sure convergence of the partial sums:

* `ae_exists_tendsto_sum_of_martingaleDifferences_of_summable_integral_sq`:
  square-integrable martingale differences with summable second moments have
  almost-surely convergent partial sums. The second-moment identity above bounds
  the partial-sum martingale in L², hence in L¹, and Mathlib's submartingale
  convergence theorem gives the limit.
* `ae_exists_tendsto_sum_of_martingaleDifferences_of_summable_bounds`: the same
  conclusion when the second moments are dominated by a summable deterministic
  sequence.

Reference: Williams, Probability with Martingales (1991), Section 12.1 and
Theorem 12.3; Hall and Heyde, Martingale Limit Theory and Its Application,
Theorem 2.15.

-/

public section

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

namespace Toolkit.Foundations.Probability.LimitTheorems

/-- For [square-integrable real increments](hyp:hD) that [are measurable at the next
filtration time](hyp:hadapted) and [have conditional mean zero at the current time](hyp:hmean),
[the second moment of their finite sum equals the sum of their second moments](goal). -/
theorem integral_sq_sum_martingaleDifferences
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ)
    (hD : ∀ k, MemLp (D k) 2 μ)
    (hadapted : ∀ k, StronglyMeasurable[F (k + 1)] (D k))
    (hmean : ∀ k, μ[D k | F k] =ᵐ[μ] 0) (n : ℕ) :
    (∫ ω, (∑ k ∈ Finset.range n, D k ω) ^ 2 ∂μ) =
      ∑ k ∈ Finset.range n, ∫ ω, (D k ω) ^ 2 ∂μ := by
  classical
  -- L² is closed under finite sums, and products of L² functions are integrable.
  have hsum (m : ℕ) : MemLp (fun ω => ∑ k ∈ Finset.range m, D k ω) 2 μ :=
    memLp_finsetSum _ (fun k _ => hD k)
  have horth (m : ℕ) : ∫ ω, (∑ k ∈ Finset.range m, D k ω) * D m ω ∂μ = 0 := by
    have hsm : StronglyMeasurable[F m] (fun ω => ∑ k ∈ Finset.range m, D k ω) :=
      Finset.stronglyMeasurable_fun_sum _ (fun k hk =>
        (hadapted k).mono (F.mono (Nat.add_one_le_iff.mpr (Finset.mem_range.mp hk))))
    have hprod := (hsum m).integrable_mul (hD m)
    have hc := condExp_mul_of_stronglyMeasurable_left hsm hprod
      ((hD m).integrable (by norm_num))
    have hz : μ[(fun ω => ∑ k ∈ Finset.range m, D k ω) * D m | F m] =ᵐ[μ] 0 := by
      filter_upwards [hc, hmean m] with ω h₁ h₂
      simp [h₁, h₂]
    change (∫ ω, ((fun ω => ∑ k ∈ Finset.range m, D k ω) * D m) ω ∂μ) = 0
    rw [← integral_condExp (F.le m), integral_congr_ae hz]
    simp
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ]
    have hexp : (fun ω => ((∑ k ∈ Finset.range n, D k ω) + D n ω) ^ 2) =
        (fun ω => (∑ k ∈ Finset.range n, D k ω) ^ 2 + (D n ω) ^ 2 +
          2 * ((∑ k ∈ Finset.range n, D k ω) * D n ω)) := by
      funext ω
      ring
    rw [hexp]
    rw [integral_add (f := fun ω => (∑ k ∈ Finset.range n, D k ω) ^ 2 + (D n ω) ^ 2)
      (g := fun ω => 2 * ((∑ k ∈ Finset.range n, D k ω) * D n ω))
      ((hsum n).integrable_sq.add (hD n).integrable_sq)
      (((hsum n).integrable_mul (hD n)).const_mul 2),
      integral_add (hsum n).integrable_sq (hD n).integrable_sq,
      integral_const_mul, horth, ih]
    ring

/-- For [real increments measurable at the next filtration time](hyp:hadapted),
[with conditional mean zero](hyp:hmean), and [a common finite absolute bound](hyp:hbound),
if [their averaged conditional second moments converge in probability](hyp:hvariance)
to [a nonnegative variance](hyp:hv), then [their square-root-normalized sums converge
in distribution to the centred Gaussian law with that variance, including its
point-mass case](goal). -/
theorem tendstoInDistribution_sum_div_sqrt_of_bounded_martingaleDifferences
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) (B v : ℝ)
    (hadapted : ∀ k, StronglyMeasurable[F (k + 1)] (D k))
    (hmean : ∀ k, μ[D k | F k] =ᵐ[μ] 0)
    (hbound : ∀ k ω, |D k ω| ≤ B) (hv : 0 ≤ v)
    (hvariance : TendstoInMeasure μ
      (fun n ω => (∑ k ∈ Finset.range n, μ[fun z => (D k z) ^ 2 | F k] ω) / n)
      atTop (fun _ => v)) :
    TendstoInDistribution (fun n ω => (∑ k ∈ Finset.range n, D k ω) / Real.sqrt n)
      atTop (id : ℝ → ℝ) (fun _ => μ) (gaussianReal 0 v.toNNReal) := by
  classical
  have hsm (k : ℕ) : StronglyMeasurable (D k) :=
    (hadapted k).mono (F.le _)
  have hL2 (k : ℕ) : MemLp (D k) 2 μ :=
    MemLp.of_bound (hsm k).aestronglyMeasurable B
      (ae_of_all μ (fun ω => by simpa only [Real.norm_eq_abs] using hbound k ω))
  have hvar : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n : ℕ => (μ {ω | δ ≤ |(n : ℝ)⁻¹ *
          (∑ k ∈ Finset.range n, μ[fun z => (D k z) ^ 2 | F k] ω) - v|}).toReal)
        atTop (𝓝 0) := by
    have h := (Causalean.Stat.Modes.tendstoInProbability_iff_measureReal_norm
      (fun _ : ℕ => μ) _ atTop (fun _ _ => v)).mp hvariance
    intro δ hδ
    simpa only [Measure.real, Real.norm_eq_abs, div_eq_inv_mul] using h δ hδ
  -- The common bound makes every Lindeberg tail empty for all sufficiently large n.
  have hlind : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
          ∫ ω in {ω | ε * Real.sqrt n ≤ |D k ω|}, (D k ω) ^ 2 ∂μ)
        atTop (𝓝 0) := by
    intro ε hε
    have ht : Tendsto (fun n : ℕ => ε * Real.sqrt n) atTop atTop :=
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hε
    apply tendsto_const_nhds.congr'
    filter_upwards [ht.eventually (eventually_gt_atTop B)] with n hn
    have hset (k : ℕ) : {ω | ε * Real.sqrt n ≤ |D k ω|} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hω
      exact (not_le_of_gt hn) (hω.trans (hbound k ω))
    simp only [hset, setIntegral_empty, Finset.sum_const_zero, mul_zero]
  refine ⟨fun n => (Finset.aemeasurable_fun_sum _ (fun k _ =>
    (hsm k).measurable.aemeasurable)).div_const _, measurable_id.aemeasurable, ?_⟩
  apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr
  intro u
  simpa only [ProbabilityMeasure.coe_mk, Measure.map_id, div_eq_inv_mul] using
    (StatLean.TimeSeries.mds_clt_sequence (fun k => F.le k) (fun _ _ h => F.mono h)
      (fun k => (hadapted k).measurable) hL2 hmean hv hvar hlind u)

/-- For real increments [measurable at the next filtration time](hyp:hadapted),
[square integrable](hyp:hξ), and [having conditional mean zero given current
information](hyp:hmean), if [their second moments are summable](hyp:hsum), then
[their partial sums converge almost surely to a finite real limit](goal).

The partial sums form a martingale; by `integral_sq_sum_martingaleDifferences`
each partial sum has second moment at most the full series, so the martingale is
bounded in L¹ (via |x| ≤ 1 + x²), and Doob's convergence theorem
`MeasureTheory.Submartingale.exists_ae_tendsto_of_bdd` applies. Reference:
Williams, Probability with Martingales (1991), Section 12.1. -/
theorem ae_exists_tendsto_sum_of_martingaleDifferences_of_summable_integral_sq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ mΩ) (ξ : ℕ → Ω → ℝ)
    (hadapted : ∀ n, StronglyMeasurable[ℱ (n + 1)] (ξ n))
    (hξ : ∀ n, MemLp (ξ n) 2 P)
    (hmean : ∀ n, P[ξ n | ℱ n] =ᵐ[P] 0)
    (hsum : Summable (fun n => ∫ ω, (ξ n ω) ^ 2 ∂P)) :
    ∀ᵐ ω ∂P, ∃ l : ℝ,
      Tendsto (fun n => ∑ i ∈ Finset.range n, ξ i ω) atTop (𝓝 l) := by
  classical
  let S : ℕ → Ω → ℝ := fun n ω => ∑ i ∈ Finset.range n, ξ i ω
  have hS (n : ℕ) : MemLp (S n) 2 P :=
    memLp_finsetSum _ (fun i _ => hξ i)
  have hSint (n : ℕ) : Integrable (S n) P :=
    (hS n).integrable (by norm_num)
  have hSadapted : StronglyAdapted ℱ S := by
    intro n
    exact Finset.stronglyMeasurable_fun_sum _ (fun i hi =>
      (hadapted i).mono (ℱ.mono (Nat.add_one_le_iff.mpr (Finset.mem_range.mp hi))))
  have hmart : Martingale S ℱ P := by
    apply martingale_of_condExp_sub_eq_zero_nat hSadapted hSint
    intro n
    have hdiff : S (n + 1) - S n = ξ n := by
      funext ω
      simp [S, Finset.sum_range_succ]
    rw [hdiff]
    exact hmean n
  have hsq (n : ℕ) : (∫ ω, (S n ω) ^ 2 ∂P) ≤
      ∑' i, ∫ ω, (ξ i ω) ^ 2 ∂P := by
    rw [integral_sq_sum_martingaleDifferences P ℱ ξ hξ hadapted hmean n]
    exact hsum.sum_le_tsum (Finset.range n) (fun i _ =>
      integral_nonneg (fun ω => sq_nonneg _))
  have hL1 (n : ℕ) : (∫ ω, ‖S n ω‖ ∂P) ≤
      1 + ∑' i, ∫ ω, (ξ i ω) ^ 2 ∂P := by
    calc
      (∫ ω, ‖S n ω‖ ∂P) ≤ ∫ ω, (1 + (S n ω) ^ 2) ∂P := by
        apply integral_mono (hSint n).norm ((integrable_const 1).add (hS n).integrable_sq)
        intro ω
        change ‖S n ω‖ ≤ 1 + (S n ω) ^ 2
        rw [Real.norm_eq_abs]
        have := sq_nonneg (|S n ω| - 1)
        have := sq_abs (S n ω)
        nlinarith
      _ = 1 + ∫ ω, (S n ω) ^ 2 ∂P := by
        rw [integral_add (integrable_const 1) (hS n).integrable_sq]
        simp
      _ ≤ 1 + ∑' i, ∫ ω, (ξ i ω) ^ 2 ∂P := add_le_add le_rfl (hsq n)
  apply hmart.submartingale.exists_ae_tendsto_of_bdd
    (R := (1 + ∑' i, ∫ ω, (ξ i ω) ^ 2 ∂P).toNNReal)
  intro n
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm (hSint n)]
  exact ENNReal.ofReal_le_coe.mpr ((hL1 n).trans (Real.le_coe_toNNReal _))

/-- For real increments [measurable at the next filtration time](hyp:hadapted),
[square integrable](hyp:hξ), and [having conditional mean zero given current
information](hyp:hmean), if [each second moment is at most the corresponding term of
a deterministic sequence](hyp:hbound) [whose series is summable](hyp:hc), then
[their partial sums converge almost surely to a finite real limit](goal). -/
theorem ae_exists_tendsto_sum_of_martingaleDifferences_of_summable_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ mΩ) (ξ : ℕ → Ω → ℝ) (c : ℕ → ℝ)
    (hadapted : ∀ n, StronglyMeasurable[ℱ (n + 1)] (ξ n))
    (hξ : ∀ n, MemLp (ξ n) 2 P)
    (hmean : ∀ n, P[ξ n | ℱ n] =ᵐ[P] 0)
    (hbound : ∀ n, (∫ ω, (ξ n ω) ^ 2 ∂P) ≤ c n)
    (hc : Summable c) :
    ∀ᵐ ω ∂P, ∃ l : ℝ,
      Tendsto (fun n => ∑ i ∈ Finset.range n, ξ i ω) atTop (𝓝 l) := by
  apply ae_exists_tendsto_sum_of_martingaleDifferences_of_summable_integral_sq
    P ℱ ξ hadapted hξ hmean
  exact Summable.of_nonneg_of_le (fun n => integral_nonneg (fun ω => sq_nonneg _))
    hbound hc


end Toolkit.Foundations.Probability.LimitTheorems
