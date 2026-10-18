module
public import Papers.TbsNeuralCausalPi.Setup.CitedResults
public import Mathlib.Topology.MetricSpace.Holder
/-! # Conversion of the cited Euclidean modulus to the paper one-norm -/
public section
namespace Papers.TbsNeuralCausalPi
open scoped NNReal ENNReal

/-- [The one-norm distance between two vectors is at most their dimension times
their Euclidean distance](goal). -/
-- @node: l1_dist_le_dim_mul_euclidean_dist
lemma l1_dist_le_dim_mul_euclidean_dist {d : ℕ} (x y : L1Vec d) :
    dist x y ≤ d * dist (toEuclidean x) (toEuclidean y) := by
  rw [PiLp.dist_eq_of_L1]
  calc
    _ ≤ ∑ _j : Fin d, dist (toEuclidean x) (toEuclidean y) := by
      apply Finset.sum_le_sum
      intro j _
      exact PiLp.dist_apply_le (toEuclidean x) (toEuclidean y) j
    _ = _ := by simp

/-- If [a scalar function is Lipschitz with constant L on the unit cube in the one-norm metric](hyp:hf)
and [the radius is nonnegative](hyp:hr), then [its Euclidean modulus at that radius is at most
L times the dimension times the radius](goal). -/
-- @node: euclidModulus_le_of_lipschitzOn
lemma euclidModulus_le_of_lipschitzOn {d : ℕ} {f : L1Vec d → ℝ}
    {L : ℝ≥0} (hf : LipschitzOnWith L f (unitCube d))
    {r : ℝ} (hr : 0 ≤ r) :
    euclidModulus f r ≤ L * d * r := by
  apply csSup_le
  · refine ⟨0, 0, ?_, 0, ?_, ?_, ?_⟩
    · intro j; simp
    · intro j; simp
    · simpa using hr
    · simp
  · rintro a ⟨x, hx, y, hy, hdist, rfl⟩
    have hLip := hf.dist_le_mul x hx y hy
    rw [Real.dist_eq] at hLip
    calc
      |f x - f y| ≤ L * dist x y := hLip
      _ ≤ L * (d * dist (toEuclidean x) (toEuclidean y)) :=
        mul_le_mul_of_nonneg_left (l1_dist_le_dim_mul_euclidean_dist x y) L.coe_nonneg
      _ ≤ L * (d * r) := by gcongr
      _ = _ := by ring

/-- If [a scalar function is Lipschitz with constant L on the unit cube in the one-norm metric](hyp:hf)
and [the radius is nonnegative](hyp:hr), then [its Euclidean modulus at that radius is at most
L times the square root of the dimension times the radius](goal). -/
-- @node: euclidModulus_le_sqrt_of_lipschitzOn
lemma euclidModulus_le_sqrt_of_lipschitzOn {d : ℕ} {f : L1Vec d → ℝ}
    {L : ℝ≥0} (hf : LipschitzOnWith L f (unitCube d))
    {r : ℝ} (hr : 0 ≤ r) :
    euclidModulus f r ≤ L * Real.sqrt d * r := by
  apply csSup_le
  · refine ⟨0, 0, ?_, 0, ?_, ?_, ?_⟩
    · intro j; simp
    · intro j; simp
    · simpa using hr
    · simp
  · rintro a ⟨x, hx, y, hy, hdist, rfl⟩
    have hmetric : dist x y ≤ Real.sqrt d * dist (toEuclidean x) (toEuclidean y) := by
      rw [PiLp.dist_eq_of_L1, PiLp.dist_eq_of_L2]
      simpa [toEuclidean] using
        (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ : Fin d => (1 : ℝ))
          (fun j => dist (x.ofLp j) (y.ofLp j)))
    have hLip := hf.dist_le_mul x hx y hy
    rw [Real.dist_eq] at hLip
    calc
      |f x - f y| ≤ L * dist x y := hLip
      _ ≤ L * (Real.sqrt d * dist (toEuclidean x) (toEuclidean y)) :=
        mul_le_mul_of_nonneg_left hmetric L.coe_nonneg
      _ ≤ L * (Real.sqrt d * r) := by gcongr
      _ = _ := by ring

/-- If [the exponent is nonnegative](hyp:halpha), [the Hölder constant is nonnegative](hyp:hA),
[absolute function differences on the unit cube are bounded by that constant times the
one-norm distance raised to that exponent](hyp:hf), and [the radius is nonnegative](hyp:hr),
then [the Euclidean modulus is at most the Hölder constant times the product of dimension
and radius raised to that exponent](goal). -/
-- @node: euclidModulus_le_of_holder
lemma euclidModulus_le_of_holder {d : ℕ} {f : L1Vec d → ℝ}
    {alpha A : ℝ} (halpha : 0 ≤ alpha) (hA : 0 ≤ A)
    (hf : ∀ x ∈ unitCube d, ∀ y ∈ unitCube d,
      |f x - f y| ≤ A * ‖x - y‖ ^ alpha)
    {r : ℝ} (hr : 0 ≤ r) :
    euclidModulus f r ≤ A * ((d : ℝ) * r) ^ alpha := by
  apply csSup_le
  · refine ⟨0, 0, ?_, 0, ?_, ?_, ?_⟩
    · intro j; simp
    · intro j; simp
    · simpa using hr
    · simp
  · rintro a ⟨x, hx, y, hy, hdist, rfl⟩
    refine (hf x hx y hy).trans ?_
    apply mul_le_mul_of_nonneg_left _ hA
    apply Real.rpow_le_rpow (norm_nonneg _) _ halpha
    calc
      ‖x - y‖ = dist x y := (dist_eq_norm x y).symm
      _ ≤ d * dist (toEuclidean x) (toEuclidean y) :=
        l1_dist_le_dim_mul_euclidean_dist x y
      _ ≤ d * r := by gcongr

/-- If [the Hölder exponent is positive](hyp:halpha), [the Hölder constant is nonnegative](hyp:hA),
and [absolute function differences on the unit cube are bounded by that constant times
the one-norm distance raised to that exponent](hyp:hf), then [the function is continuous
on the unit cube](goal). -/
-- @node: continuousOn_of_cube_holder
@[fun_prop]
lemma continuousOn_of_cube_holder {d : ℕ} {f : L1Vec d → ℝ}
    {alpha A : ℝ} (halpha : 0 < alpha) (hA : 0 ≤ A)
    (hf : ∀ x ∈ unitCube d, ∀ y ∈ unitCube d,
      |f x - f y| ≤ A * ‖x - y‖ ^ alpha) : ContinuousOn f (unitCube d) := by
  have hh : HolderOnWith A.toNNReal alpha.toNNReal f (unitCube d) := by
    intro x hx y hy
    simp only [edist_dist, Real.coe_toNNReal _ halpha.le, ENNReal.ofNNReal_toNNReal]
    rw [ENNReal.ofReal_rpow_of_nonneg dist_nonneg halpha.le, ← ENNReal.ofReal_mul hA]
    apply ENNReal.ofReal_le_ofReal
    simpa only [dist_eq_norm, Real.norm_eq_abs] using hf x hx y hy
  exact hh.continuousOn (by simpa using halpha)

/-- If [a vector-valued function is Lipschitz with constant L on a set in the one-norm metrics](hyp:hf),
then [each chosen output coordinate is Lipschitz with the same constant on that set](goal). -/
-- @node: lipschitzOnWith_output_coordinate
lemma lipschitzOnWith_output_coordinate {d k : ℕ} {S : Set (L1Vec d)}
    {f : L1Vec d → L1Vec k} {L : ℝ≥0} (hf : LipschitzOnWith L f S)
    (j : Fin k) : LipschitzOnWith L (fun x => (f x).ofLp j) S := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  exact (PiLp.dist_apply_le (f x) (f y) j).trans (hf.dist_le_mul x hx y hy)

end Papers.TbsNeuralCausalPi
