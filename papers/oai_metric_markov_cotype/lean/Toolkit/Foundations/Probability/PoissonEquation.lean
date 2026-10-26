module

public import Batteries.Logic
public import Causalean.Mathlib.Probability.Certified.FiniteKernel
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.SetLike.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Stochastic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Lattice
public import Mathlib.Order.Max
public import Mathlib.Order.Nat
public import Mathlib.Order.Notation
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.UniformSpace.Defs

/-!
# Poisson equations for finite irreducible transition matrices

The finite-dimensional algebra behind limit theorems for additive functionals of
a finite-state Markov chain. Irreducibility is stated by positive entries of
matrix powers; no aperiodicity or contraction assumption is imposed. The
stochasticity, probability-vector and stationarity predicates are reused from
Causalean.

* `eq_const_of_mulVec_eq`: a function fixed by an irreducible row-stochastic matrix
  is constant (maximum principle).
* `exists_potential_of_stationary_mean_zero`: a function with stationary mean zero
  has a Poisson potential, a solution `g` of `g - R g = f`.
* `tendsto_average_mulVec_pow`: the averages of the first `n` matrix powers applied
  to a function converge to its stationary mean, also for periodic matrices.
* `innovationVariance`: the one-step conditional variance of a state function,
  with the supporting facts `mulVec_pow_eq_of_fixed`, `sum_stationary_mulVec` and
  `abs_mulVec_pow_le`.

Proof route: a maximum principle identifies the kernel of I minus R with the
constants. Stationarity identifies its range with the stationary-mean-zero
hyperplane by a stationary-mean correction and finite-dimensional injectivity.
Bounded matrix powers then give Cesàro convergence by telescoping the Poisson
equation.

Reference: Meyn and Tweedie, Markov Chains and Stochastic Stability, Chapter 17
(the Poisson equation), specialized to a finite state space.
-/

@[expose] public section

open scoped BigOperators Topology
open Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation

namespace Toolkit.Foundations.Probability

/-- For [a finite real transition matrix](hyp:R), [a real function on its states](hyp:g),
and [a current state](hyp:x), [the innovation variance](goal) is [the transition-weighted
mean square of the next function value minus its one-step conditional mean](step:1). -/
noncomputable def innovationVariance {T : Type*} [Fintype T]
    (R : Matrix T T ℝ) (g : T → ℝ) (x : T) : ℝ :=
  ∑ y, R x y * (g y - R.mulVec g x) ^ 2

/-- If [a real state function is fixed by one application of a finite matrix](hyp:hfixed),
then [it is fixed by every nonnegative power of that matrix](goal). -/
theorem mulVec_pow_eq_of_fixed {T : Type*} [Fintype T] [DecidableEq T]
    {R : Matrix T T ℝ} {g : T → ℝ} (hfixed : R.mulVec g = g) (n : ℕ) :
    (R ^ n).mulVec g = g := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, hfixed, ih]

/-- If [a finite transition matrix is row-stochastic](hyp:hR),
[every state can reach every other state with positive probability in some number
of steps](hyp:hreach), and [a state function is unchanged by one transition](hyp:hfixed),
then [the function is constant across all states](goal). -/
theorem eq_const_of_mulVec_eq {T : Type*} [Fintype T] [DecidableEq T] [Nonempty T]
    {R : Matrix T T ℝ} {g : T → ℝ}
    (hR : IsStochasticMatrix R)
    (hreach : ∀ x y, ∃ n : ℕ, 0 < (R ^ n) x y)
    (hfixed : R.mulVec g = g) : ∃ c : ℝ, g = fun _ => c := by
  -- At a state maximizing g, apply mulVec_pow_eq_of_fixed to a power reaching y.
  -- A convex average attaining its upper bound forces g y to equal that bound.
  classical
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image Finset.univ g Finset.univ_nonempty
  have hmax : ∀ y, g y ≤ g a := fun y => ha y (Finset.mem_univ y)
  refine ⟨g a, funext fun y => ?_⟩
  obtain ⟨n, hn⟩ := hreach a y
  have hp : R ^ n ∈ Matrix.rowStochastic ℝ T :=
    (Matrix.rowStochastic ℝ T).pow_mem (Matrix.mem_rowStochastic_iff_sum.mpr hR) n
  have hnon : ∀ z, 0 ≤ (R ^ n) a z * (g a - g z) :=
    fun z => mul_nonneg (Matrix.nonneg_of_mem_rowStochastic hp) (sub_nonneg.mpr (hmax z))
  have hsum : ∑ z, (R ^ n) a z * (g a - g z) = 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul,
      Matrix.sum_row_of_mem_rowStochastic hp, one_mul]
    have hf := congrFun (mulVec_pow_eq_of_fixed hfixed n) a
    change (∑ z, (R ^ n) a z * g z) = g a at hf
    rw [hf, sub_self]
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => hnon z)).mp hsum y
    (Finset.mem_univ y)
  have := (mul_eq_zero.mp hz).resolve_left (ne_of_gt hn)
  linarith

/-- If [a probability vector is stationary for a finite matrix](hyp:hphi), then
[the stationary mean of any state function](hyp:g) [is unchanged by applying that
matrix to the function](goal). -/
theorem sum_stationary_mulVec {T : Type*} [Fintype T]
    {R : Matrix T T ℝ} {phi : T → ℝ} (hphi : IsStationary R phi) (g : T → ℝ) :
    ∑ x, phi x * R.mulVec g x = ∑ x, phi x * g x := by
  -- Exchange finite sums and use the coordinate version of phi R = phi.
  classical
  change ∑ x, phi x * (∑ y, R x y * g y) = _
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  have hs : ∀ y, (∑ x, phi x * R x y) = phi y :=
    fun y => congrFun hphi.2 y
  simp_rw [hs]

/-- For [a row-stochastic finite matrix](hyp:hR), if [a state function is uniformly
bounded in absolute value by a real constant](hyp:hbound), then [every matrix power
applied to that function obeys the same uniform bound](goal). -/
theorem abs_mulVec_pow_le {T : Type*} [Fintype T] [DecidableEq T]
    {R : Matrix T T ℝ} {g : T → ℝ} {B : ℝ}
    (hR : IsStochasticMatrix R) (hbound : ∀ x, |g x| ≤ B) (n : ℕ) (x : T) :
    |(R ^ n).mulVec g x| ≤ B := by
  -- Use powers in Matrix.rowStochastic and the triangle inequality for finite sums.
  have hp : R ^ n ∈ Matrix.rowStochastic ℝ T :=
    (Matrix.rowStochastic ℝ T).pow_mem (Matrix.mem_rowStochastic_iff_sum.mpr hR) n
  change |∑ y, (R ^ n) x y * g y| ≤ B
  calc
    _ ≤ ∑ y, |(R ^ n) x y * g y| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ y, (R ^ n) x y * |g y| := by
      simp_rw [abs_mul, abs_of_nonneg (Matrix.nonneg_of_mem_rowStochastic hp)]
    _ ≤ ∑ y, (R ^ n) x y * B := Finset.sum_le_sum fun y _ =>
      mul_le_mul_of_nonneg_left (hbound y) (Matrix.nonneg_of_mem_rowStochastic hp)
    _ = B := by rw [← Finset.sum_mul, Matrix.sum_row_of_mem_rowStochastic hp, one_mul]

/-- For [a row-stochastic finite matrix](hyp:hR) with [positive-power reachability
between every pair of states](hyp:hreach) and [a stationary probability vector](hyp:hphi),
every [function with stationary mean zero](hyp:hcenter) [has a Poisson potential:
the function equals that potential minus its one-step transition average](goal). -/
theorem exists_potential_of_stationary_mean_zero
    {T : Type*} [Fintype T] [DecidableEq T] [Nonempty T]
    {R : Matrix T T ℝ} {phi f : T → ℝ}
    (hR : IsStochasticMatrix R)
    (hreach : ∀ x y, ∃ n : ℕ, 0 < (R ^ n) x y)
    (hphi : IsStationary R phi) (hcenter : ∑ x, phi x * f x = 0) :
    ∃ g : T → ℝ, ∀ x, g x - R.mulVec g x = f x := by
  -- I - R has the constant kernel and preserves the mean-zero hyperplane.
  -- Adding the stationary mean as a constant function gives an injective
  -- endomorphism, hence a surjective one by finite dimensionality.
  -- For a centered right-hand side the correction vanishes.
  classical
  -- The stationary-mean correction removes precisely the constant kernel.
  let L : (T → ℝ) →ₗ[ℝ] (T → ℝ) :=
    { toFun := fun u x => u x - R.mulVec u x + ∑ y, phi y * u y
      map_add' := by
        intro u v
        ext x
        simp [Matrix.mulVec_add, mul_add, Finset.sum_add_distrib]
        ring
      map_smul' := by
        intro c u
        ext x
        simp [Matrix.mulVec_smul, mul_left_comm, ← Finset.mul_sum]
        ring }
  have hmean (u : T → ℝ) : ∑ x, phi x * L u x = ∑ x, phi x * u x := by
    change (∑ x, phi x * (u x - R.mulVec u x + ∑ y, phi y * u y)) = _
    simp_rw [mul_add, mul_sub]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      sum_stationary_mulVec hphi, sub_self, zero_add, ← Finset.sum_mul,
      hphi.1.2, one_mul]
  have hinj : Function.Injective L := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro u hu
    have hm : ∑ x, phi x * u x = 0 := by
      rw [← hmean u, hu]
      simp
    have hf : R.mulVec u = u := by
      ext x
      have hx := congrFun hu x
      change u x - R.mulVec u x + ∑ y, phi y * u y = 0 at hx
      rw [hm] at hx
      linarith
    obtain ⟨c, hc⟩ := eq_const_of_mulVec_eq hR hreach hf
    have hc0 : c = 0 := by
      rw [hc] at hm
      simp only [← Finset.sum_mul, hphi.1.2, one_mul] at hm
      exact hm
    rw [hc, hc0]
    rfl
  obtain ⟨u, hu⟩ := LinearMap.surjective_of_injective hinj f
  have hm : ∑ x, phi x * u x = 0 := by
    rw [← hmean u, hu, hcenter]
  refine ⟨u, fun x => ?_⟩
  have hx := congrFun hu x
  change u x - R.mulVec u x + ∑ y, phi y * u y = f x at hx
  simpa [hm] using hx

/-- For [a row-stochastic finite matrix](hyp:hR) with [positive-power reachability](hyp:hreach)
and [a stationary probability vector](hyp:hphi), [the average of the first n matrix powers
applied to any real state function](hyp:g) [converges at each state to its stationary
mean](goal). -/
theorem tendsto_average_mulVec_pow
    {T : Type*} [Fintype T] [DecidableEq T] [Nonempty T]
    {R : Matrix T T ℝ} {phi : T → ℝ}
    (hR : IsStochasticMatrix R)
    (hreach : ∀ x y, ∃ n : ℕ, 0 < (R ^ n) x y)
    (hphi : IsStationary R phi) (g : T → ℝ) (x : T) :
    Filter.Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, (R ^ k).mulVec g x) / n)
      Filter.atTop (nhds (∑ y, phi y * g y)) := by
  -- Center g, obtain a potential, telescope powers, and bound the endpoints.
  -- Ordinary convergence of R^n is false for periodic chains and is unnecessary.
  classical
  let m : ℝ := ∑ y, phi y * g y
  have hc : ∑ y, phi y * (g y - m) = 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hphi.1.2, one_mul]
    exact sub_self m
  obtain ⟨u, hu⟩ := exists_potential_of_stationary_mean_zero hR hreach hphi hc
  have hg : g = (fun _ => m) + u - R.mulVec u := by
    ext y
    have := hu y
    change g y = m + u y - R.mulVec u y
    linarith
  have hstep (k : ℕ) :
      (R ^ k).mulVec g x = m + (R ^ k).mulVec u x - (R ^ (k + 1)).mulVec u x := by
    have hp : R ^ k ∈ Matrix.rowStochastic ℝ T :=
      (Matrix.rowStochastic ℝ T).pow_mem (Matrix.mem_rowStochastic_iff_sum.mpr hR) k
    have hconst : (R ^ k).mulVec (fun _ => m) x = m := by
      change (∑ y, (R ^ k) x y * m) = m
      rw [← Finset.sum_mul, Matrix.sum_row_of_mem_rowStochastic hp, one_mul]
    rw [hg, Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_mulVec, ← pow_succ]
    exact congrArg (fun a => a + (R ^ k).mulVec u x - (R ^ (k + 1)).mulVec u x) hconst
  have htel (n : ℕ) :
      (∑ k ∈ Finset.range n, (R ^ k).mulVec g x) =
        (n : ℝ) * m + u x - (R ^ n).mulVec u x := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, hstep]
      push_cast
      ring
  let B : ℝ := ∑ y, |u y|
  have hb (y : T) : |u y| ≤ B :=
    Finset.single_le_sum (fun z _ => abs_nonneg (u z)) (Finset.mem_univ y)
  have hp (n : ℕ) : |(R ^ n).mulVec u x| ≤ B := abs_mulVec_pow_le hR hb n x
  have hlim : Filter.Tendsto (fun n : ℕ => (u x - (R ^ n).mulVec u x) / n)
      Filter.atTop (nhds 0) := by
    apply tendsto_bdd_div_atTop_nhds_zero
      (b := u x - B) (B := u x + B)
    · exact Filter.Eventually.of_forall fun n => by linarith [(abs_le.mp (hp n)).2]
    · exact Filter.Eventually.of_forall fun n => by linarith [(abs_le.mp (hp n)).1]
    · exact tendsto_natCast_atTop_atTop
  have hlim' := hlim.const_add m
  apply Filter.Tendsto.congr' _ (by simpa using hlim')
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  rw [htel]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  field_simp
  ring

end Toolkit.Foundations.Probability
