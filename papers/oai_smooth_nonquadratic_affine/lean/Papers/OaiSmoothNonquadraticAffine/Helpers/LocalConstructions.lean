module

public import Papers.OaiSmoothNonquadraticAffine.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Order.Interval.Set.ProjIcc
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The local integral construction

These definitions record the paper's auxiliary continuous trial pairs, integral
averages and transform values. Continuity of the output and contraction bounds
are proof obligations of local existence, rather than fields of the input.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory

namespace OaiSmoothNonquadraticAffine

/-- For [an interval half-width δ](hyp:δ), [the space of local trial pairs](goal)
consists of two continuous real-valued functions on the closed interval from
−δ to δ, equipped with the product supremum norm. -/
abbrev LocalTrialPair (δ : ℝ) :=
  C(Icc (-δ) δ, ℝ) × C(Icc (-δ) δ, ℝ)

/-- For [an interval half-width δ](hyp:δ), [the local trial set](goal) consists
of continuous trial pairs on the closed interval from −δ to δ for which [the
first component stays within one half of one](step:1) and [the second component
stays within one half of one](step:2). -/
def localTrialSet (δ : ℝ) : Set (LocalTrialPair δ) :=
  {fp | (∀ s, |fp.1 s - 1| ≤ 1 / 2) ∧ -- @realizes f(continuous first trial component)
    (∀ s, |fp.2 s - 1| ≤ 1 / 2)} -- @realizes p(second component) @realizes \mathcal K(trial set)

/-- For [an interval half-width δ](hyp:δ) [that is positive](hyp:hδ), [a continuous
real-valued function on the closed interval from −δ to δ](hyp:f), and [a real
evaluation point s](hyp:s), [the local trial extension at s](goal) evaluates
the function at s clamped to the interval, keeping the endpoint values constant
outside it. -/
def localTrialExtension (δ : ℝ) (hδ : 0 < δ) (f : C(Icc (-δ) δ, ℝ))
    (s : ℝ) : ℝ :=
  f (projIcc (-δ) δ (neg_le_self (le_of_lt hδ)) s)

/-- For [an interval half-width δ](hyp:δ) [that is positive](hyp:hδ), [a pair of
continuous trial functions on the closed interval from −δ to δ](hyp:fp)
[whose components stay within one half of one](hyp:_hfp), and [a real auxiliary
coordinate s](hyp:s), [the local slope average](goal) is the ninth root of nine
times the integral from zero to one of the eighth power of the integration
variable times the first trial function times the second to the power
−12/11, with both functions extended by constant endpoint values and evaluated
at the square of the integration variable times s. -/
def localQ (δ : ℝ) (hδ : 0 < δ) (fp : LocalTrialPair δ)
    (_hfp : fp ∈ localTrialSet δ) (s : ℝ) : ℝ :=
  (9 * ∫ v : ℝ in 0..1, v ^ 8 * localTrialExtension δ hδ fp.1 (v ^ 2 * s) *
    localTrialExtension δ hδ fp.2 (v ^ 2 * s) ^ (-radialGamma)) ^ (1 / 9 : ℝ)
    -- @realizes q(positive root average associated with a trial pair)

/-- For [an interval half-width δ](hyp:δ) [that is positive](hyp:hδ), [a pair of
continuous trial functions on the closed interval from −δ to δ](hyp:fp)
[whose components stay within one half of one](hyp:_hfp), and [a real auxiliary
coordinate s](hyp:s), [the local flux average](goal) is the integral from zero
to one of the eighth power of the integration variable times the second trial
function to the power −1/11, extended by constant endpoint values and evaluated
at the square of the integration variable times s. -/
def localJ (δ : ℝ) (hδ : 0 < δ) (fp : LocalTrialPair δ)
    (_hfp : fp ∈ localTrialSet δ) (s : ℝ) : ℝ :=
  ∫ v : ℝ in 0..1, v ^ 8 *
    localTrialExtension δ hδ fp.2 (v ^ 2 * s) ^ (1 - radialGamma)
    -- @realizes j(normalized continuous flux average in the local construction)

/-- For [an interval half-width δ](hyp:δ) [that is positive](hyp:hδ), [a pair of
continuous trial functions on the closed interval from −δ to δ](hyp:fp)
[whose components stay within one half of one](hyp:hfp), and [an auxiliary
coordinate s in that interval](hyp:s), [the local integral transform value](goal)
is the pair consisting of one plus the integral of the local slope average
from zero to s, and one minus the paper's flux constant times the integral from
zero to s of the local flux average times the local slope average to the power
one minus the radial dimension. -/
def localTransformValues (δ : ℝ) (hδ : 0 < δ) (fp : LocalTrialPair δ)
    (hfp : fp ∈ localTrialSet δ) (s : Icc (-δ) δ) : ℝ × ℝ :=
  (1 + ∫ a : ℝ in 0..(s : ℝ), localQ δ hδ fp hfp a,
    1 - radialK * ∫ a : ℝ in 0..(s : ℝ),
      localJ δ hδ fp hfp a * localQ δ hδ fp hfp a ^ (1 - (radialDim : ℝ)))
    -- @realizes \mathcal T(integral transform evaluated at s in the auxiliary interval)

/-- For [a displacement coefficient M](hyp:M) and [a Lipschitz coefficient
L](hyp:L), [the local contraction bounds](goal) require, for every positive
interval half-width δ and every admissible trial pair, that [both transformed
components differ from one by at most M times δ at every point](step:1) and
that [the maximum difference between transformed components for any two
admissible trial pairs is at most L times δ times the distance between those
pairs at every point](step:2). -/
def LocalContractionBounds (M L : ℝ) : Prop :=
  ∀ (δ : ℝ) (hδ : 0 < δ) (fp : LocalTrialPair δ) (hfp : fp ∈ localTrialSet δ),
    (∀ s, max |(localTransformValues δ hδ fp hfp s).1 - 1|
      |(localTransformValues δ hδ fp hfp s).2 - 1| ≤ M * δ) ∧ -- @realizes M(uniform displacement)
    ∀ (gp : LocalTrialPair δ) (hgp : gp ∈ localTrialSet δ) s,
      max |(localTransformValues δ hδ fp hfp s).1 - (localTransformValues δ hδ gp hgp s).1|
        |(localTransformValues δ hδ fp hfp s).2 - (localTransformValues δ hδ gp hgp s).2| ≤
          L * δ * dist fp gp -- @realizes L(uniform Lipschitz bound independent of delta)

/-- For [a displacement coefficient M](hyp:M), [a Lipschitz coefficient
L](hyp:L), and [an auxiliary interval half-width δ](hyp:δ), [the small local
radius condition](goal) requires that [δ be positive](step:1), [M times δ be
at most one half](step:2), and [L times δ be strictly less than one](step:3). -/
def SmallLocalRadius (M L δ : ℝ) : Prop :=
  0 < δ ∧ -- @realizes \delta(positive half-length of the auxiliary interval)
  M * δ ≤ 1 / 2 ∧ -- @realizes \delta(displacement smallness constraint)
  L * δ < 1 -- @realizes \delta(contraction smallness constraint)

/-- For [a physical radius r](hyp:r) [that is nonnegative](hyp:_hr), [the radial
auxiliary coordinate](goal) is one half of the square of r. -/
def radialAuxiliaryCoordinate (r : ℝ) (_hr : 0 ≤ r) : ℝ :=
  r ^ 2 / 2 -- @realizes s(physical auxiliary coordinate r^2/2)

end OaiSmoothNonquadraticAffine
