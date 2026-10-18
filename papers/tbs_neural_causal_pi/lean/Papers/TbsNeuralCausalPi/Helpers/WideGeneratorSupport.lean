module
public import Papers.TbsNeuralCausalPi.Helpers.NetworkMeasurability
public import Papers.TbsNeuralCausalPi.Helpers.NetworkClipping
public import Papers.TbsNeuralCausalPi.Helpers.OneDimensionalCurve
public import Papers.TbsNeuralCausalPi.Helpers.WassersteinBounds
/-! # Depth padding and clipping transport for component generators -/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped ENNReal NNReal

-- @node: uniformCubeLaw_probability
/-- In any finite dimension, [the uniform law on the unit cube is a probability law](goal). -/
lemma uniformCubeLaw_probability (d : ℕ) : IsProbabilityMeasure (uniformCubeLaw d) := by
  letI : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    ⟨by simp⟩
  unfold uniformCubeLaw
  apply Measure.isProbabilityMeasure_map
  fun_prop

-- @node: wasserstein_coordinateClamp_le
/-- For two probability laws on a finite-dimensional space with one-norm
distance, [clipping every coordinate to the unit interval cannot increase their
Wasserstein distance](goal). -/
lemma wasserstein_coordinateClamp_le {d : ℕ} (mu nu : Measure (L1Vec d))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    wasserstein1 (mu.map (coordinateClamp 0 1)) (nu.map (coordinateClamp 0 1)) ≤
      wasserstein1 mu nu := by
  have hm : Measurable (coordinateClamp (d := d) 0 1) := by
    exact (coordinateClamp_lipschitz 0 1).continuous.measurable
  simpa using PushForward.map_le_of_compact_range mu nu
    (coordinateClamp 0 1) (coordinateClamp 0 1) hm hm 1
    (coordinateClamp_lipschitz 0 1) 0 (by simp)
    (unitCube d) (unitCube_isCompact d)
    (fun x => coordinateClamp_mapsTo 0 1 zero_le_one x)
    (fun x => coordinateClamp_mapsTo 0 1 zero_le_one x)

-- @node: coordinateClamp_chartInverse
/-- For a homeomorphism from a unit cube onto a chart image, [clipping the
extended inverse chart coordinatewise to the unit interval leaves that inverse
unchanged](goal). -/
lemma coordinateClamp_chartInverse {D d : ℕ} {K : Set (L1Vec D)}
    (f : homeoClass (unitCube d) K) :
    coordinateClamp 0 1 ∘ chartInverse f = chartInverse f := by
  funext x
  apply coordinateClamp_fixes
  by_cases hx : x ∈ K
  · exact chartInverse_mapsTo f hx
  · simp [chartInverse, hx]

end Papers.TbsNeuralCausalPi
