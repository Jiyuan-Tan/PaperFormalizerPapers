module
public import Papers.OaiMetricMarkovCotype.Helpers.Comparison
public import Papers.OaiMetricMarkovCotype.Helpers.HilbertMarkov
public import Papers.OaiMetricMarkovCotype.Helpers.Resolvent

/-! # Endpoint comparison in matrix form

Finite three-time distributions realize the stationary-walk L₂ triangle argument
without requiring an auxiliary infinite path space.
-/

public section

open MeasureTheory
open scoped BigOperators
namespace Papers.OaiMetricMarkovCotype

/-- For [nonnegative weights on a finite set](hyp:hw), [integrating a real function against
the sum of point masses with those weights equals the weighted sum of its values](goal). -/
-- @node: integral_finite_weighted_law
lemma integral_finite_weighted_law {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (f : α → ℝ) :
    (∫ a, f a ∂(∑ b, ENNReal.ofReal (w b) • Measure.dirac b)) = ∑ a, w a * f a := by
  rw [integral_finsetSum_measure (fun a _ =>
    (Integrable.of_finite (μ := Measure.dirac a)).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw _),
    smul_eq_mul]

/-- If [the state weights form a probability vector](hyp:hπ), [the transition matrix is
stochastic](hyp:hA), and [detailed balance holds](hyp:hrev), then [the square root of the
expected squared distance between embedded states is subadditive in elapsed time](goal). -/
-- @node: matrixEndpoint_sqrt_subadditive
lemma matrixEndpoint_sqrt_subadditive {n : ℕ} {X : Type*} [MetricSpace X]
    (π : Fin n → ℝ) (hπ : IsProbabilityVector π)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A)
    (hrev : IsReversible A π) (x : Fin n → X) :
    Subadditive (fun s => Real.sqrt
      (∑ i, ∑ j, π i * (A ^ s) i j * dist (x i) (x j) ^ 2)) := by
  classical
  intro r s
  let w : Fin n × Fin n × Fin n → ℝ :=
    fun a => π a.1 * (A ^ r) a.1 a.2.1 * (A ^ s) a.2.1 a.2.2
  have hw (a) : 0 ≤ w a := mul_nonneg
    (mul_nonneg (hπ.1 _) ((isStochastic_pow A hA r).nonneg _ _))
    ((isStochastic_pow A hA s).nonneg _ _)
  let μ : Measure (Fin n × Fin n × Fin n) :=
    ∑ a, ENNReal.ofReal (w a) • Measure.dirac a
  let : IsFiniteMeasure μ := by
    constructor
    dsimp [μ]
    simp only [Measure.finsetSum_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
    exact ENNReal.sum_lt_top.mpr (fun _ _ => ENNReal.ofReal_lt_top)
  have hint (f : Fin n × Fin n × Fin n → ℝ) :
      (∫ a, f a ∂μ) = ∑ i, ∑ j, ∑ k, π i * (A ^ r) i j * (A ^ s) j k * f (i, j, k) := by
    rw [integral_finite_weighted_law w hw]
    simp only [Fintype.sum_prod_type, w]
  have hmem (f : Fin n × Fin n × Fin n → ℝ) : MemLp f 2 μ := by
    apply MemLp.of_bound (by fun_prop) (∑ a, ‖f a‖)
    exact ae_of_all _ fun a => Finset.single_le_sum (fun b _ => norm_nonneg (f b))
      (Finset.mem_univ a)
  let f : Fin n × Fin n × Fin n → ℝ := fun a => dist (x a.1) (x a.2.1)
  let g : Fin n × Fin n × Fin n → ℝ := fun a => dist (x a.2.1) (x a.2.2)
  let h : Fin n × Fin n × Fin n → ℝ := fun a => dist (x a.1) (x a.2.2)
  have hf : (∫ a, f a ^ 2 ∂μ) = ∑ i, ∑ j, π i * (A ^ r) i j * dist (x i) (x j) ^ 2 := by
    rw [hint]
    simp only [f, ← Finset.sum_mul, ← Finset.mul_sum, stochastic_power_rows A hA s, mul_one]
  have hg : (∫ a, g a ^ 2 ∂μ) = ∑ j, ∑ k, π j * (A ^ s) j k * dist (x j) (x k) ^ 2 := by
    rw [hint, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    simp only [g, mul_assoc]
    rw [show (∑ i, π i * ((A ^ r) i j * ((A ^ s) j k * dist (x j) (x k) ^ 2))) =
      (∑ i, π i * (A ^ r) i j) * ((A ^ s) j k * dist (x j) (x k) ^ 2) by
        simp only [Finset.sum_mul]; congr 1; ext i; ring]
    rw [stationary_power_columns π A (reversible_weighted_columns π A hA hrev) r j]
  have hh : (∫ a, h a ^ 2 ∂μ) =
      ∑ i, ∑ k, π i * (A ^ (r + s)) i k * dist (x i) (x k) ^ 2 := by
    rw [hint]
    simp only [h, pow_add, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    ring
  dsimp only
  rw [← hh, ← hf, ← hg]
  apply (Real.sqrt_le_sqrt (integral_mono (hmem h).integrable_sq
    ((hmem f).add (hmem g)).integrable_sq (fun a =>
      pow_le_pow_left₀ dist_nonneg (dist_triangle _ _ _) 2))).trans
  exact sqrt_integral_sq_add_le μ f g (hmem f) (hmem g)
    (fun _ => dist_nonneg) (fun _ => dist_nonneg)

/-- For [a strictly positive integer time horizon](hyp:ht), [probability weights on the
states](hyp:hπ), and [a stochastic matrix](hyp:hA) [satisfying detailed balance](hyp:hrev),
[the geometrically averaged expected squared distance is at most 28 times its average
over times one through the horizon](goal). -/
-- @node: matrixEndpoint_geometric_comparison
lemma matrixEndpoint_geometric_comparison {n : ℕ} {X : Type*} [MetricSpace X]
    (t : ℕ) (ht : GeometricParameterDomain t)
    (π : Fin n → ℝ) (hπ : IsProbabilityVector π)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsStochastic A)
    (hrev : IsReversible A π) (x : Fin n → X) :
    (∑' s : ℕ, geomKillProb t ht * geomSurvProb t ht ^ s *
      ∑ i, ∑ j, π i * (A ^ s) i j * dist (x i) (x j) ^ 2) ≤
      28 * ∑ i, ∑ j, π i *
        (((1 / (t : ℝ)) • ∑ s ∈ Finset.Icc 1 t, A ^ s) i j) *
          dist (x i) (x j) ^ 2 := by
  have hzero : (∑ i, ∑ j, π i * (A ^ 0) i j * dist (x i) (x j) ^ 2) = 0 := by
    simp [Matrix.one_apply]
  have hn (s : ℕ) : 0 ≤ ∑ i, ∑ j, π i * (A ^ s) i j * dist (x i) (x j) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (hπ.1 i) ((isStochastic_pow A hA s).nonneg i j))
        (sq_nonneg _)
  calc
    _ ≤ (28 / (t : ℝ)) * ∑ s ∈ Finset.Icc 1 t,
        ∑ i, ∑ j, π i * (A ^ s) i j * dist (x i) (x j) ^ 2 :=
      geometric_sqrtSubadditive_comparison _ hzero hn
        (matrixEndpoint_sqrt_subadditive π hπ A hA hrev x) t ht
    _ = _ := by
      simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
        Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro s _
      ring

end Papers.OaiMetricMarkovCotype
