module
public import Papers.TbsNeuralCausalPi.Setup.Assumptions.Model
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
/-! # Regularity of normalized categorical weights

The denominator need only be positive on the structural input domain.
The one-norm estimate gives the local Lipschitz conclusion without imposing
positive individual coordinates or a global lower bound on the denominator.
-/
public section
namespace Papers.TbsNeuralCausalPi
open scoped NNReal

/-- If [all weights are nonnegative](hyp:hp) and [their sum is positive](hyp:hs), then [dividing each weight by their sum gives a vector in the probability simplex](goal). -/
-- @node: canonical_normalized_mem_simplex
lemma canonical_normalized_mem_simplex {k : ℕ} (p : Fin k → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hs : 0 < ∑ j, p j) :
    (fun j => p j / ∑ l, p l) ∈ probabilitySimplex k := by
  exact ⟨fun j => div_nonneg (hp j) hs.le, by rw [← Finset.sum_div, div_self hs.ne']⟩

/-- If [the first vector has nonnegative coordinates](hyp:_hp), [the second vector has nonnegative coordinates](hyp:hq), [the first vector's coordinate sum is positive](hyp:hs), and [the second vector's coordinate sum is positive](hyp:ht), then [the one-norm distance between their normalized vectors is at most twice their original distance divided by the first vector's coordinate sum](goal). -/
-- @node: canonical_normalized_dist_le
lemma canonical_normalized_dist_le {k : ℕ} (p q : L1Vec k)
    (_hp : ∀ j, 0 ≤ p.ofLp j) (hq : ∀ j, 0 ≤ q.ofLp j)
    (hs : 0 < ∑ j, p.ofLp j) (ht : 0 < ∑ j, q.ofLp j) :
    dist (WithLp.toLp 1 (fun j => p.ofLp j / ∑ l, p.ofLp l))
      (WithLp.toLp 1 (fun j => q.ofLp j / ∑ l, q.ofLp l)) ≤
        2 / (∑ j, p.ofLp j) * dist p q := by
  let s := ∑ j, p.ofLp j
  let t := ∑ j, q.ofLp j
  have hmass : |s-t| ≤ dist p q := by
    rw [PiLp.dist_eq_of_L1]
    simpa only [s, t, ← Finset.sum_sub_distrib, Real.dist_eq] using
      (Finset.abs_sum_le_sum_abs (fun j : Fin k => p.ofLp j-q.ofLp j) Finset.univ)
  have hcoord (j : Fin k) :
      |p.ofLp j / s - q.ofLp j / t| ≤
        |p.ofLp j-q.ofLp j| / s + (q.ofLp j / t) * (|s-t| / s) := by
    have heq : p.ofLp j / s - q.ofLp j / t =
        (p.ofLp j-q.ofLp j) / s + (q.ofLp j / t) * ((t-s) / s) := by
      field_simp [show s ≠ 0 from hs.ne', show t ≠ 0 from ht.ne']
      ring
    rw [heq]
    calc
      _ ≤ |(p.ofLp j-q.ofLp j) / s| + |(q.ofLp j / t) * ((t-s) / s)| := abs_add_le _ _
      _ = _ := by
        rw [abs_div, abs_of_pos hs, abs_mul,
          abs_of_nonneg (div_nonneg (hq j) ht.le), abs_div, abs_of_pos hs, abs_sub_comm t s]
  rw [PiLp.dist_eq_of_L1]
  simp only [Real.dist_eq]
  calc
    _ ≤ ∑ j, (|p.ofLp j-q.ofLp j| / s + (q.ofLp j / t) * (|s-t| / s)) :=
      Finset.sum_le_sum (fun j _ => hcoord j)
    _ = dist p q / s + |s-t| / s := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul,
        ← Finset.sum_div, show (∑ j, q.ofLp j) = t from rfl, div_self ht.ne', one_mul]
      rw [PiLp.dist_eq_of_L1]
      rfl
    _ ≤ dist p q / s + dist p q / s := by gcongr
    _ = _ := by dsimp only [s]; ring

/-- If [a vector-valued function is continuously differentiable to order r on a set](hyp:hp) and [its coordinate sum is positive throughout that set](hyp:hs), then [dividing its coordinates by their sum preserves continuous differentiability to order r on the set](goal). -/
-- @node: canonical_normalized_contDiffOn
@[fun_prop] lemma canonical_normalized_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} {S : Set E} {p : E → L1Vec k} {r : WithTop ℕ∞}
    (hp : ContDiffOn ℝ r p S) (hs : ∀ x ∈ S, 0 < ∑ j, (p x).ofLp j) :
    ContDiffOn ℝ r (fun x => WithLp.toLp 1
      (fun j => (p x).ofLp j / ∑ l, (p x).ofLp l)) S := by
  have hc : ∀ j, ContDiffOn ℝ r (fun x => (p x).ofLp j) S :=
    (contDiffOn_piLp 1).mp hp
  have hsum : ContDiffOn ℝ r (fun x => ∑ j, (p x).ofLp j) S := by
    fun_prop
  apply (contDiffOn_piLp 1).mpr
  intro j
  exact (hc j).div hsum (fun x hx => (hs x hx).ne')

/-- If [a vector-valued function is Lipschitz with constant L on a set](hyp:hLip), [its coordinates are nonnegative there](hyp:hp), and [a nonnegative mass threshold a](hyp:a) [is strictly positive](hyp:ha) and [bounds the coordinate sum from below throughout the set](hyp:hs), then [normalizing by the coordinate sum gives a Lipschitz function on that set with constant twice L divided by a](goal). -/
-- @node: canonical_normalized_lipschitzOn
lemma canonical_normalized_lipschitzOn
    {E : Type*} [PseudoMetricSpace E] {k : ℕ} {S : Set E} {p : E → L1Vec k}
    {L : ℝ≥0} (hLip : LipschitzOnWith L p S)
    (hp : ∀ x ∈ S, ∀ j, 0 ≤ (p x).ofLp j)
    (a : ℝ≥0) (ha : 0 < a) (hs : ∀ x ∈ S, (a : ℝ) ≤ ∑ j, (p x).ofLp j) :
    LipschitzOnWith (2 * L / a) (fun x => WithLp.toLp 1
      (fun j => (p x).ofLp j / ∑ l, (p x).ofLp l)) S := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have ha' : (0 : ℝ) < a := ha
  have hsx := ha'.trans_le (hs x hx)
  have hsy := ha'.trans_le (hs y hy)
  calc
    _ ≤ 2 / (∑ j, (p x).ofLp j) * dist (p x) (p y) :=
      canonical_normalized_dist_le (p x) (p y) (hp x hx) (hp y hy) hsx hsy
    _ ≤ (2 / (a : ℝ)) * ((L : ℝ) * dist x y) := by
      gcongr
      · exact hs x hx
      · exact hLip.dist_le_mul x hx y hy
    _ = _ := by simp only [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_ofNat]; ring

/-- If [a vector-valued function has nonnegative coordinates on a set](hyp:hp), [has a positive coordinate sum at every point of the set](hyp:hs), and [is Lipschitz on some ball intersected with the set around each of its points](hyp:hlocal), then [its normalization by the coordinate sum is also Lipschitz on some ball intersected with the set around each point](goal). -/
-- @node: canonical_normalized_locally_lipschitz
lemma canonical_normalized_locally_lipschitz
    {E : Type*} [PseudoMetricSpace E] {k : ℕ} {S : Set E} {p : E → L1Vec k}
    (hp : ∀ x ∈ S, ∀ j, 0 ≤ (p x).ofLp j)
    (hs : ∀ x ∈ S, 0 < ∑ j, (p x).ofLp j)
    (hlocal : ∀ x ∈ S, ∃ L : ℝ≥0, ∃ r : ℝ, 0 < r ∧
      LipschitzOnWith L p (Metric.ball x r ∩ S)) :
    ∀ x ∈ S, ∃ A : ℝ≥0, ∃ r : ℝ, 0 < r ∧
      LipschitzOnWith A (fun x => WithLp.toLp 1
        (fun j => (p x).ofLp j / ∑ l, (p x).ofLp l)) (Metric.ball x r ∩ S) := by
  intro x hx
  obtain ⟨L, r, hr, hL⟩ := hlocal x hx
  let U := Metric.ball x r ∩ S
  let s : E → ℝ := fun y => ∑ j, (p y).ofLp j
  let a : ℝ≥0 := ⟨s x / 2, (half_pos (hs x hx)).le⟩
  have ha : 0 < a := by change (0 : ℝ) < s x / 2; exact half_pos (hs x hx)
  have hcoord (j : Fin k) : ContinuousOn (fun y => (p y).ofLp j) U := by
    first | fun_prop
          | exact ((continuous_apply j).comp (PiLp.continuous_ofLp 1 _)).comp_continuousOn
              hL.continuousOn
  have hsum : ContinuousOn s U := by
    dsimp only [s]
    fun_prop
  have hxu : x ∈ U := ⟨Metric.mem_ball_self hr, hx⟩
  have hnhds : s ⁻¹' Set.Ioi (a : ℝ) ∈ nhdsWithin x U :=
    (hsum x hxu).preimage_mem_nhdsWithin (Ioi_mem_nhds (by
      change s x / 2 < s x
      linarith [hs x hx]))
  obtain ⟨e, he, heU⟩ := Metric.mem_nhdsWithin_iff.mp hnhds
  let V := Metric.ball x (min r e) ∩ S
  have hVU : V ⊆ U := by
    intro y hy
    exact ⟨Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hy.1) (min_le_left _ _)), hy.2⟩
  refine ⟨2 * L / a, min r e, lt_min hr he, ?_⟩
  apply canonical_normalized_lipschitzOn (hL.mono hVU)
    (fun y hy => hp y hy.2) a ha
  intro y hy
  exact (heU ⟨Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hy.1)
    (min_le_right _ _)), hVU hy⟩).le

/-- If [a map does not increase distances](hyp:hpi), [sends a source set into a target set](hyp:hmaps), and [a function is Lipschitz on some ball intersected with the target set around each target point](hyp:hlocal), then [composing the function with the map is Lipschitz on some ball intersected with the source set around each source point](goal). -/
-- @node: canonical_locally_lipschitz_comp
lemma canonical_locally_lipschitz_comp
    {E F H : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F] [PseudoMetricSpace H]
    {S : Set E} {T : Set F} {p : F → H} (pi : E → F)
    (hpi : LipschitzWith 1 pi) (hmaps : Set.MapsTo pi S T)
    (hlocal : ∀ x ∈ T, ∃ A : ℝ≥0, ∃ r : ℝ, 0 < r ∧
      LipschitzOnWith A p (Metric.ball x r ∩ T)) :
    ∀ x ∈ S, ∃ A : ℝ≥0, ∃ r : ℝ, 0 < r ∧
      LipschitzOnWith A (p ∘ pi) (Metric.ball x r ∩ S) := by
  intro x hx
  obtain ⟨A, r, hr, hA⟩ := hlocal (pi x) (hmaps hx)
  refine ⟨A, r, hr, ?_⟩
  have hm : Set.MapsTo pi (Metric.ball x r ∩ S) (Metric.ball (pi x) r ∩ T) := by
    intro y hy
    refine ⟨Metric.mem_ball.mpr ?_, hmaps hy.2⟩
    have hd := hpi.dist_le_mul y x
    simp only [NNReal.coe_one, one_mul] at hd
    exact hd.trans_lt (Metric.mem_ball.mp hy.1)
  simpa only [mul_one] using hA.comp hpi.lipschitzOnWith hm

end Papers.TbsNeuralCausalPi
