module

public import Papers.HawkesD75660b.Helpers.BorelMoments

/-! Real-parameter masses for the independent rooted-tree normalization proof. -/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Papers.HawkesD75660b.AnalyticBorel

-- @node: Papers.HawkesD75660b.AnalyticBorel.borelMass
/-- For [a real parameter](hyp:ρ) and [a nonnegative integer size](hyp:j), [the analytic Borel mass](goal) is [zero at size zero](step:1) and [otherwise the exponential of minus parameter times size, multiplied by parameter times size raised to size minus one, divided by the factorial of size](step:2). -/
def borelMass (ρ : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 0 else Real.exp (-ρ * j) * (ρ * j) ^ (j - 1) / (j.factorial : ℝ)

-- @node: Papers.HawkesD75660b.AnalyticBorel.borelMeasure
/-- For [a real parameter](hyp:ρ), [the analytic Borel measure is the countable sum of point masses at nonnegative integers, weighted by their analytic Borel masses converted to nonnegative weights](goal). -/
def borelMeasure (ρ : ℝ) : Measure ℕ :=
  Measure.sum (fun j => ENNReal.ofReal (borelMass ρ j) • Measure.dirac j)

end Papers.HawkesD75660b.AnalyticBorel
