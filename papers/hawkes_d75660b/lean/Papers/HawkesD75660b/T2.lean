module

public import Papers.HawkesD75660b.Helpers.Series

/-! The mean duration identity for the observed Markovian Hawkes cluster. -/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

namespace Papers.HawkesD75660b

-- @env: S1
variable {Ω ΩB : Type*} [MeasurableSpace Ω] [MeasurableSpace ΩB]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure ΩB) [IsProbabilityMeasure Q]
    (C : Ω → EpochConfiguration) (ρ : ℝ≥0)
    (hworld : hawkesClusterWorld P C ρ) (B : ΩB → ℕ)

include hworld

-- @node: thm:meanidthm1
/-- Suppose C is a measurable cluster configuration with Borel-distributed size under P, [the branching parameter ρ is less than one](hyp:hsubcritical), [B has the Borel distribution with parameter ρ under Q](hyp:hB), [cluster counts include events at the observation time, the Markovian intensity has the prescribed right-continuous and left-limit versions, and the compensated count is an integrable martingale with predictable left intensity](hyp:hcounting), and [the observed duration has the combinatorial duration distribution](hyp:hrepresentation). Then [the mean observed cluster duration under P equals (1 − ρ) times the expectation under Q of B times its harmonic number, less one](goal). -/
theorem meanDurationIdentity
    (hsubcritical : subcritical ρ) (hB : auxiliaryBorelLaw ρ Q B)
    (hcounting : clusterCountingConvention P C ρ)
    (hrepresentation : durationRepresentation P C ρ) :
    (∫ ω, (clusterDuration C ω : ℝ) ∂P) =
      (1 - (ρ : ℝ)) * (∫ ω, (B ω : ℝ) * harmonicNumber (B ω) ∂Q) - 1 := by
  have hduration :
      (∫ ω, (clusterDuration C ω : ℝ) ∂P) =
        ∫ q, (combinatorialDuration q : ℝ) ∂combinatorialMeasure ρ := by
    exact (hrepresentation.comp (by fun_prop : Measurable (fun x : ℝ≥0 => (x : ℝ)))).integral_eq
  have hmoment :
      (∫ ω, (B ω : ℝ) * harmonicNumber (B ω) ∂Q) =
        ∫ j : ℕ, (j : ℝ) * harmonicNumber j ∂borelMeasure ρ := by
    exact hB.integral_comp (f := fun j : ℕ => (j : ℝ) * harmonicNumber j) (by fun_prop)
  rw [hduration, duration_series_identity ρ hsubcritical, hmoment]

end Papers.HawkesD75660b
