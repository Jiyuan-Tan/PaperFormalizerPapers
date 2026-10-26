module
public import Papers.OaiMetricMarkovCotype.Helpers.CutAssembly
public import Papers.OaiMetricMarkovCotype.Helpers.Comparison
public import Papers.OaiMetricMarkovCotype.Helpers.EndpointLaw
public import Papers.OaiMetricMarkovCotype.Helpers.MatrixComparison
public import Papers.OaiMetricMarkovCotype.TMartingale

/-! # Metric Markov cotype two of real ℓ₁ -/

public section

open MeasureTheory
open scoped BigOperators

namespace Papers.OaiMetricMarkovCotype

/-- [Real ℓ₁ has metric Markov cotype two with constant twelve times the square
root of twenty-one](goal). -/
theorem hasMetricMarkovCotypeTwo_realEllOne :
  HasMetricMarkovCotypeTwo RealEllOne (12 * Real.sqrt 21) := by
  constructor
  intro n t _hn ht π A hπ hA hrev x
  refine ⟨modifiedPoints t ht π A x,
    (modifiedPoints_cotype_cost_le_endpoint t ht π hπ A hA hrev x).trans ?_⟩
  have hterminal :
      (∫ ω, dist (Sum.elim x x (ω 0))
        (cutReconstruction x
          (stoppedWalkTerminal (resolvent t ht A (cutEncoding x)) (cutEncoding x) ω)) ^ 2
            ∂stoppedWalkMeasure t ht π A hA) ≤
      28 * ∑ i, ∑ j, π i *
        (((1 / (t : ℝ)) • ∑ s ∈ Finset.Icc 1 t, A ^ s) i j) *
          dist (x i) (x j) ^ 2 := by
    rw [stoppedWalk_cut_endpoint_geometric_mixture t ht π hπ A hA x]
    exact matrixEndpoint_geometric_comparison t ht π hπ A hA hrev x
  calc
    _ ≤ 108 * (28 * ∑ i, ∑ j, π i *
        (((1 / (t : ℝ)) • ∑ s ∈ Finset.Icc 1 t, A ^ s) i j) *
          dist (x i) (x j) ^ 2) :=
      mul_le_mul_of_nonneg_left hterminal (by norm_num)
    _ = _ := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)]
      ring

-- @node: thm:main
/-- [The metric Markov cotype two constant of real ℓ₁ is at most twelve times
the square root of twenty-one](goal). -/
theorem metricMarkovCotypeConstant_realEllOne_le :
    metricMarkovCotypeConstant RealEllOne ≤ ENNReal.ofReal (12 * Real.sqrt 21) := by
  unfold metricMarkovCotypeConstant
  exact iInf_le_of_le (12 * Real.sqrt 21)
    (iInf_le_of_le (by positivity : 0 < 12 * Real.sqrt 21)
      (iInf_le_of_le hasMetricMarkovCotypeTwo_realEllOne le_rfl))

end Papers.OaiMetricMarkovCotype
