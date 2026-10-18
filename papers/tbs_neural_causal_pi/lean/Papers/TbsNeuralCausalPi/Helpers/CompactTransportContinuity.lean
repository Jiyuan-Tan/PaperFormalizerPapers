module
public import Papers.TbsNeuralCausalPi.Helpers.KantorovichCube
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.Order.Compact
/-! # Continuity of compact-space transport via normalized Lipschitz tests

Subtracting the value at one base point makes the dual test family compact.
Joint continuity of integration and the compact maximum theorem then give
continuity of transport in the weak topology.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory Filter
open BoundedContinuousFunction
open scoped ENNReal NNReal Topology

-- @node: compact_probability_integral_joint_continuous
/-- [The integral of a bounded continuous real function is jointly continuous
in the function under uniform convergence and in the probability law under weak
convergence](goal). -/
@[fun_prop] lemma compact_probability_integral_joint_continuous
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] :
    Continuous (fun z : (X →ᵇ ℝ) × ProbabilityMeasure X => ∫ x, z.1 x ∂(z.2 : Measure X)) := by
  apply continuous_prod_of_continuous_lipschitzWith _ 1
  · intro f
    exact ProbabilityMeasure.continuous_integral_boundedContinuousFunction f
  · intro mu
    apply LipschitzWith.of_dist_le_mul
    intro f g
    simp only [NNReal.coe_one, one_mul, dist_eq_norm]
    rw [← integral_sub (f.integrable _) (g.integrable _)]
    have h := norm_integral_le_of_norm_le_const (μ := (mu : Measure X))
      (Eventually.of_forall (fun x => show ‖f x - g x‖ ≤ ‖f - g‖ from by
        simpa only [dist_eq_norm] using
          (BoundedContinuousFunction.dist_coe_le_dist (f := f) (g := g) x)))
    simpa using h

-- @node: normalized_lipschitz_tests_isCompact
/-- On a compact metric space, [the bounded continuous real functions with
Lipschitz constant at most one that vanish at a fixed base point form a compact
set in the uniform norm](goal). -/
lemma normalized_lipschitz_tests_isCompact
    {X : Type*} [MetricSpace X] [CompactSpace X] (x0 : X) :
    IsCompact {f : X →ᵇ ℝ | LipschitzWith 1 f ∧ f x0 = 0} := by
  let S := {f : X →ᵇ ℝ | LipschitzWith 1 f ∧ f x0 = 0}
  have hclosed : IsClosed S := by
    have heq : S = (⋂ x, ⋂ y, {f : X →ᵇ ℝ | dist (f x) (f y) ≤ dist x y}) ∩
        {f : X →ᵇ ℝ | f x0 = 0} := by
      ext f
      simp [S, lipschitzWith_iff_dist_le_mul]
    rw [heq]
    apply IsClosed.inter
    · apply isClosed_iInter
      intro x
      apply isClosed_iInter
      intro y
      exact isClosed_le
        (((BoundedContinuousFunction.lipschitz_eval_const x).continuous).dist
          (BoundedContinuousFunction.lipschitz_eval_const y).continuous) continuous_const
    · exact isClosed_eq (BoundedContinuousFunction.lipschitz_eval_const x0).continuous
        continuous_const
  apply BoundedContinuousFunction.arzela_ascoli₂
    (Set.Icc (-Metric.diam (Set.univ : Set X)) (Metric.diam (Set.univ : Set X)))
    isCompact_Icc S hclosed
  · intro f x hf
    apply abs_le.mp
    calc
      |f x| = dist (f x) (f x0) := by rw [hf.2, Real.dist_eq, sub_zero]
      _ ≤ dist x x0 := by simpa using hf.1.dist_le_mul x x0
      _ ≤ Metric.diam (Set.univ : Set X) :=
        Metric.dist_le_diam_of_mem isCompact_univ.isBounded (Set.mem_univ _) (Set.mem_univ _)
  · apply Metric.equicontinuous_of_continuity_modulus (fun t => t) tendsto_id
    intro x y f
    simpa using f.property.1.dist_le_mul x y

-- @node: wasserstein1_eq_normalized_lipschitz_sSup
/-- On a compact metric space, [the Wasserstein distance of order one between
two probability laws equals the supremum of the nonnegative parts of their
expectation differences over real functions with Lipschitz constant at most one
that vanish at a fixed base point](goal). -/
lemma wasserstein1_eq_normalized_lipschitz_sSup
    {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (x0 : X) (mu nu : ProbabilityMeasure X) :
    wasserstein1 (mu : Measure X) (nu : Measure X) =
      sSup ((fun f : X →ᵇ ℝ => ENNReal.ofReal
        ((∫ x, f x ∂(mu : Measure X)) - ∫ x, f x ∂(nu : Measure X))) ''
          {f : X →ᵇ ℝ | LipschitzWith 1 f ∧ f x0 = 0}) := by
  rw [wasserstein1_eq_toolkit,
    Toolkit.Foundations.MeasureTheory.wasserstein1_eq_iSup_lipschitz]
  apply le_antisymm
  · apply iSup_le
    intro f
    let g : X →ᵇ ℝ := mkOfCompact
      ⟨fun x => f.val x - f.val x0, f.property.continuous.sub continuous_const⟩
    have hg : LipschitzWith 1 g ∧ g x0 = 0 := by
      refine ⟨?_, sub_self _⟩
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [g, mkOfCompact_apply, ContinuousMap.coe_mk, dist_sub_right] using
        f.property.dist_le_mul x y
    have hi (rho : ProbabilityMeasure X) : Integrable f.val (rho : Measure X) :=
      f.property.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have he (rho : ProbabilityMeasure X) :
        (∫ x, g x ∂(rho : Measure X)) = (∫ x, f.val x ∂(rho : Measure X)) - f.val x0 := by
      change (∫ x, f.val x - f.val x0 ∂(rho : Measure X)) = _
      rw [integral_sub (hi rho) (integrable_const _)]
      simp
    apply le_sSup
    refine ⟨g, hg, ?_⟩
    dsimp only
    rw [he mu, he nu]
    congr 1
    unfold Toolkit.Foundations.MeasureTheory.lipschitzContrast
    ring
  · apply sSup_le
    rintro _ ⟨f, hf, rfl⟩
    exact le_iSup_of_le ⟨f, hf.1⟩ le_rfl

-- @node: continuous_wasserstein1_right_compact
/-- On a compact metric space, [the Wasserstein distance of order one to a
fixed probability law is continuous as the other law varies weakly](goal). -/
@[fun_prop] lemma continuous_wasserstein1_right_compact
    {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (nu : ProbabilityMeasure X) :
    Continuous (fun mu : ProbabilityMeasure X =>
      wasserstein1 (mu : Measure X) (nu : Measure X)) := by
  have : Nonempty X := nonempty_of_isProbabilityMeasure (μ := (nu : Measure X))
  let x0 : X := Classical.choice inferInstance
  have hi : Continuous (fun z : ProbabilityMeasure X × (X →ᵇ ℝ) =>
      ∫ x, z.2 x ∂(z.1 : Measure X)) :=
    compact_probability_integral_joint_continuous.comp (continuous_snd.prodMk continuous_fst)
  have hj : Continuous (fun z : ProbabilityMeasure X × (X →ᵇ ℝ) =>
      ∫ x, z.2 x ∂(nu : Measure X)) :=
    compact_probability_integral_joint_continuous.comp (continuous_snd.prodMk continuous_const)
  have h := (normalized_lipschitz_tests_isCompact x0).continuous_sSup
    (f := fun (mu : ProbabilityMeasure X) (f : X →ᵇ ℝ) => ENNReal.ofReal
      ((∫ x, f x ∂(mu : Measure X)) - ∫ x, f x ∂(nu : Measure X)))
    (ENNReal.continuous_ofReal.comp (hi.sub hj))
  simpa only [← wasserstein1_eq_normalized_lipschitz_sSup x0] using h

end Papers.TbsNeuralCausalPi
