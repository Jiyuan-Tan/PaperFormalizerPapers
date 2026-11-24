module

public import Papers.HawkesD75660b.Helpers.Integral
public import Papers.HawkesD75660b.T2

/-! The continuously extended integral formula for the observed mean duration. -/

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

-- @node: thm:coridthm1
/-- Suppose C is a measurable cluster configuration with Borel-distributed size under P, [the branching parameter ρ is less than one](hyp:hsubcritical), [B has the Borel distribution with parameter ρ under Q](hyp:hB), [the duration integrand equals its exponential quotient below ρ, is continuous from zero through ρ, and equals 1/(1 − ρ) at ρ](hyp:hendpoint), [cluster counts include events at the observation time, the Markovian intensity has the prescribed right-continuous and left-limit versions, and the compensated count is an integrable martingale with predictable left intensity](hyp:hcounting), and [the observed duration has the combinatorial duration distribution](hyp:hrepresentation). Then [the mean observed cluster duration under P equals the integral from zero to ρ of (exp(−u) − exp(−ρ))/(ρ exp(−ρ) − u exp(−u)), continuously extended at the upper endpoint](goal). -/
theorem meanDurationIntegral
    (hsubcritical : subcritical ρ) (hB : auxiliaryBorelLaw ρ Q B)
    (hendpoint : continuousEndpointConvention ρ)
    (hcounting : clusterCountingConvention P C ρ)
    (hrepresentation : durationRepresentation P C ρ) :
    (∫ ω, (clusterDuration C ω : ℝ) ∂P) =
      ∫ u in (0 : ℝ)..(ρ : ℝ), durationIntegrand ρ u := by
  have hmoment :
      (∫ ω, (B ω : ℝ) * harmonicNumber (B ω) ∂Q) =
        ∫ j : ℕ, (j : ℝ) * harmonicNumber j ∂borelMeasure ρ := by
    exact hB.integral_comp (f := fun j : ℕ => (j : ℝ) * harmonicNumber j) (by fun_prop)
  calc
    (∫ ω, (clusterDuration C ω : ℝ) ∂P) =
        (1 - (ρ : ℝ)) * (∫ ω, (B ω : ℝ) * harmonicNumber (B ω) ∂Q) - 1 :=
      meanDurationIdentity P Q C ρ hworld B hsubcritical hB hcounting hrepresentation
    _ = (1 - (ρ : ℝ)) *
        (∫ j : ℕ, (j : ℝ) * harmonicNumber j ∂borelMeasure ρ) - 1 := by rw [hmoment]
    _ = ∫ u in (0 : ℝ)..(ρ : ℝ), durationIntegrand ρ u :=
      harmonic_borel_integral ρ hsubcritical hendpoint

end Papers.HawkesD75660b
