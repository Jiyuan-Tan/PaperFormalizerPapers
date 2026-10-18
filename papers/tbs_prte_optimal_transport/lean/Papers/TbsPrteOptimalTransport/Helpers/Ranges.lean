module
public import Mathlib.MeasureTheory.Measure.Sub
public import Papers.TbsPrteOptimalTransport.Basic
public import Papers.TbsPrteOptimalTransport.Helpers.Transport
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.List.GetD
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Toolkit.Foundations.Analysis.Calculus.AbsolutelyContinuous
/-! Ordered propensity ranges, identified gap laws, and attaining kernels. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set
open scoped Classical ENNReal
universe u v
-- @env: S3
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)
-- @node: ass:continuity-p-components
/-- The [finite-component condition](goal) says that the [instrument space](hyp:Z)
has finitely many connected components. -/
def FiniteInstrumentComponents (Z : Type v) [TopologicalSpace Z] : Prop := Finite (ConnectedComponents Z)
-- @node: ass:continuity-p-on-components
/-- For the [latent instrumental-variable model](hyp:M), [componentwise propensity
continuity](goal) means that, for almost every covariate value under its marginal law,
the propensity is continuous on every connected component of the instrument space. -/
def PropensityContinuousOnComponents : Prop :=
  ∀ᵐ x ∂xLaw M, ∀ z0, ContinuousOn (fun z => M.prop z x) (connectedComponent z0)
-- @node: ass:pin-16
/-- For the [latent instrumental-variable model](hyp:M), the [almost-everywhere
continuity requirement](goal) is continuity of the propensity on each instrument
component for almost every covariate value. -/
def PropensityContinuityAEReading : Prop := PropensityContinuousOnComponents M
-- @node: ass:discrete-lower-bound-finite
/-- The [finite discrete instrument condition](goal) requires the [instrument
space](hyp:Z) to [have finitely many elements](step:1) and [carry the discrete topology](step:2). -/
def InstrumentFinite (Z : Type v) [TopologicalSpace Z] : Prop :=
  Finite Z ∧ DiscreteTopology Z -- @realizes \mathcal{Z}(finite instrument domain with its discrete topology)
-- @node: ass:discrete-lower-bound-constant-x
/-- For the [latent instrumental-variable model](hyp:M), the [constant-covariate
condition](goal) says that some covariate value occurs almost surely under the model's law. -/
def CovariateConstant : Prop := ∃ x0, ∀ᵐ s ∂M.law.toMeasure, M.Xv s = x0
-- @node: ass:continuous-lower-bound-constant-x
/-- For the [latent instrumental-variable model](hyp:M), this [constant-covariate
condition](goal) requires the covariate to equal a single value almost surely. -/
def CovariateConstant' : Prop := CovariateConstant M

-- Finite lists implement both orderings without a recursive kernel certificate.
-- @node: def:finite-propensity-levels
/-- For a [propensity function on the instrument space](hyp:p), the [ordered list
of positive propensity levels](goal) contains its distinct positive values in ascending
order if there are finitely many, and is empty otherwise. -/
noncomputable def finiteLevels (p : Z → ℝ) : List ℝ :=
  if h : (Set.range p ∩ Ioi 0).Finite then h.toFinset.sort (· ≤ ·) else []
  -- @realizes K(number of positive levels, finiteLevels.length)
/-- Given a [list of propensity levels](hyp:levels) and a [level index](hyp:i), the
[level with structural endpoints](goal) is zero at index zero, the corresponding
list entry at indices one through the list's length, and one at larger indices. -/
def pLevel (levels : List ℝ) (i : ℕ) : ℝ := -- @realizes p_i(ordered positive levels with structural endpoints)
  if i = 0 then 0 else if i ≤ levels.length then levels.getD (i - 1) 0 else 1

/-- Given a [list of propensity levels](hyp:levels) and an [interval index](hyp:i),
the [latent interval](goal) runs from that indexed level, excluded, to the next
level, included, using the structural endpoints zero and one. -/
def finiteInterval (levels : List ℝ) (i : ℕ) : Set ℝ := Ioc (pLevel levels i) (pLevel levels (i+1)) -- @realizes I_i(latent interval between consecutive baseline levels)

/-- For a [propensity function](hyp:p), the [initial latent interval](goal) runs
from zero, excluded, to its first ordered positive level, included; when the ordered
list is empty, the upper endpoint is one. -/
noncomputable def latentInterval0 (p : Z → ℝ) : Set ℝ :=
  Ioc 0 (pLevel (finiteLevels p) 1) -- @realizes I_0(latent interval (0,p₁] from the ordered population levels)
/-- For a [propensity function](hyp:p), the [latent interval at index one](goal)
runs from its first ordered positive level, excluded, to its second, included,
with missing levels replaced by the structural endpoint one. -/
noncomputable def latentInterval1 (p : Z → ℝ) : Set ℝ :=
  finiteInterval (finiteLevels p) 1 -- @realizes I_1(latent interval (p₁,p₂] from the ordered population levels)
/-- For a [propensity function](hyp:p), the [latent interval at index two](goal)
runs from its second ordered positive level, excluded, to its third, included,
with missing levels replaced by the structural endpoint one. -/
noncomputable def latentInterval2 (p : Z → ℝ) : Set ℝ :=
  finiteInterval (finiteLevels p) 2 -- @realizes I_2(latent interval (p₂,p₃] from the ordered population levels)


/-- A [finite interval representation](goal) consists of a natural-number count
and two equally sized indexed families of real numbers for the interval endpoints. -/
abbrev RangeData := Σ K : ℕ, (Fin K → ℝ) × (Fin K → ℝ)
/-- A [finite interval representation](hyp:a) is a [valid decomposition](goal) of
a [real set](hyp:R) when [each left endpoint lies between zero and its right
endpoint, which is at most one](step:1), [every earlier interval ends strictly
before every later interval begins](step:2), and [the set equals the union of
these closed intervals](step:3). -/
def RangeData.Valid (R : Set ℝ) (a : RangeData) : Prop :=
  (∀ k, 0 ≤ a.2.1 k ∧ a.2.1 k ≤ a.2.2 k ∧ a.2.2 k ≤ 1) ∧ -- @realizes \underline{p}_k(left endpoints in [0,1]) @realizes \overline{p}_k(right endpoints in [0,1])
  (∀ k l, k < l → a.2.2 k < a.2.1 l) ∧ R = ⋃ k, Icc (a.2.1 k) (a.2.2 k)
-- @node: def:range-decomposition
/-- For a [real set](hyp:R), the [chosen range decomposition](goal) is any valid
finite representation by ordered, strictly separated closed intervals in the unit
interval, if one exists, and the representation with no intervals otherwise. -/
noncomputable def RangeDecomposition (R : Set ℝ) : RangeData :=
  if h : ∃ a : RangeData, a.Valid R then Classical.choose h else ⟨0, (Fin.elim0, Fin.elim0)⟩
namespace RangeData
/-- The [component count](goal) of a [finite interval representation](hyp:D) is
the number of endpoint pairs it stores. -/
def count (D : RangeData) := D.1 -- @realizes K_x(conditional component count)
/-- For a [finite interval representation](hyp:D) and a [component index](hyp:k),
the [left endpoint](goal) is the stored left endpoint when the index is below the
component count, and one otherwise. -/
def low (D : RangeData) (k : ℕ) : ℝ := if h : k < D.1 then D.2.1 ⟨k,h⟩ else 1
  -- @realizes \underline{p}_k(left maximal-interval endpoints)
/-- For a [finite interval representation](hyp:D) and a [component index](hyp:k),
the [right endpoint](goal) is the stored right endpoint when the index is below
the component count, and zero otherwise. -/
def high (D : RangeData) (k : ℕ) : ℝ := if h : k < D.1 then D.2.2 ⟨k,h⟩ else 0
  -- @realizes \overline{p}_k(right maximal-interval endpoints)
/-- For a [finite interval representation](hyp:D) and a [gap index](hyp:k), the
[lower gap endpoint](goal) is zero for the initial gap and the preceding
component's right endpoint for every positive index. -/
def gapLo (D : RangeData) (k : ℕ) : ℝ := if k = 0 then 0 else D.high (k-1)
/-- For a [finite interval representation](hyp:D) and a [gap index](hyp:k), the
[upper gap endpoint](goal) is the left endpoint of the component at that index,
using one when the index is outside the stored components. -/
def gapHi (D : RangeData) (k : ℕ) : ℝ := D.low k
/-- For a [finite interval representation](hyp:D) and a [component index](hyp:k),
the [local instrumental-variable region](goal) is the closed interval between
that component's left and right endpoints. -/
def liv (D : RangeData) (k : ℕ) : Set ℝ := Icc (D.low k) (D.high k)
  -- @realizes L_k(closed LIV interval)
/-- The [lower tail endpoint](goal) of a [finite interval representation](hyp:D)
is zero if there are no components and the last component's right endpoint otherwise. -/
def tailLo (D : RangeData) : ℝ := if D.count = 0 then 0 else D.high (D.count-1)
/-- The [tail region](goal) of a [finite interval representation](hyp:D) runs
from its lower tail endpoint, excluded, to one, included. -/
def tail (D : RangeData) : Set ℝ := Ioc D.tailLo 1
end RangeData
-- @node: def:range-regions
/-- For a [finite interval representation](hyp:D) and a [gap index](hyp:k), the
[gap region](goal) is the open interval between the corresponding gap endpoints,
intersected with the closed unit interval. -/
def RangeDecomposition.gap (D : RangeData) (k : ℕ) : Set ℝ :=
  Ioo (D.gapLo k) (D.gapHi k) ∩ Icc 0 1 -- @realizes G_k(Borel gap in [0,1] for k < D.count; tail excluded)
/-- If [the interval representation validly decomposes the given set](hyp:hD)
and [the gap index is below its component count](hyp:hk), then [its gap region
equals the full open interval between its gap endpoints](goal). -/
lemma range_gap_eq_Ioo_of_valid (D : RangeData) (R : Set ℝ) (hD : D.Valid R)
    (k : ℕ) (hk : k < D.count) :
    RangeDecomposition.gap D k = Ioo (D.gapLo k) (D.gapHi k) := by
  have hi : D.gapHi k ≤ 1 := by
    have hk' : k < D.1 := hk
    have hb := hD.1 ⟨k, hk'⟩
    simpa only [RangeData.gapHi, RangeData.low, dif_pos hk'] using hb.2.1.trans hb.2.2
  have lo : 0 ≤ D.gapLo k := by
    by_cases hz : k = 0
    · simp [RangeData.gapLo, hz]
    · have hp : k - 1 < D.count := by omega
      have hp' : k - 1 < D.1 := hp
      have hb := hD.1 ⟨k - 1, hp'⟩
      simpa only [RangeData.gapLo, if_neg hz, RangeData.high, dif_pos hp'] using hb.1.trans hb.2.1
  ext u
  exact ⟨fun hu => hu.1, fun hu => ⟨hu, lo.trans hu.1.le, hu.2.le.trans hi⟩⟩

/-- If [the gap index is below the component count of the chosen decomposition
of a real set](hyp:hk), then [that gap region equals the full open interval
between its gap endpoints](goal). -/
lemma rangeDecomposition_gap_eq_Ioo (R : Set ℝ) (k : ℕ)
    (hk : k < (RangeDecomposition R).count) :
    RangeDecomposition.gap (RangeDecomposition R) k =
      Ioo ((RangeDecomposition R).gapLo k) ((RangeDecomposition R).gapHi k) := by
  unfold RangeDecomposition at hk ⊢
  split_ifs with h
  · rw [dif_pos h] at hk
    exact range_gap_eq_Ioo_of_valid _ R (Classical.choose_spec h) k hk
  · rw [dif_neg h] at hk
    have : k < 0 := hk
    omega

-- @node: def:range-decomposition-cov
/-- For a [latent instrumental-variable model](hyp:M) and a [covariate value](hyp:x),
the [conditional range decomposition](goal) is the chosen finite interval
decomposition of all propensity values obtained by varying the instrument at that covariate value. -/
noncomputable def CondRangeDecomposition (x : X) : RangeData := RangeDecomposition (range (fun z => M.prop z x))
/-- If [the gap index is below the component count of the conditional propensity
range decomposition](hyp:hk), then [the conditional gap region equals the full
open interval between its gap endpoints](goal). -/
lemma conditional_gap_eq_Ioo (x : X) (k : ℕ)
    (hk : k < (CondRangeDecomposition M x).count) :
    RangeDecomposition.gap (CondRangeDecomposition M x) k =
      Ioo ((CondRangeDecomposition M x).gapLo k) ((CondRangeDecomposition M x).gapHi k) :=
  rangeDecomposition_gap_eq_Ioo _ k hk

-- @node: ass:pin-31
/-- For a [finite interval representation](hyp:D), the [coverage condition up to
a null set](goal) says that the part of the closed unit interval outside its
component intervals, gaps indexed below the component count, and tail has zero Lebesgue measure. -/
def RegionsPartitionNullReading (D : RangeData) : Prop :=
  volume (Icc (0 : ℝ) 1 \ ((⋃ k ∈ Iio D.count, D.liv k) ∪
    (⋃ k ∈ Iio D.count, RangeDecomposition.gap D k) ∪ D.tail)) = 0
-- @node: ass:pin-32
/-- For the [latent instrumental-variable model](hyp:M), the [conditional
coverage condition](goal) requires that, for almost every covariate value, the
conditional component intervals, gaps, and tail cover the unit interval up to a Lebesgue null set. -/
def CondRegionsPartitionNullReading : Prop :=
  ∀ᵐ x ∂xLaw M, RegionsPartitionNullReading (CondRangeDecomposition M x)

/-- Given a [lower endpoint](hyp:a) and an [upper endpoint](hyp:b), the
[normalized interval measure](goal) is Lebesgue measure restricted to the open
interval between them, scaled by the reciprocal of its nonnegative length. -/
noncomputable def uniformInterval (a b : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (b-a))⁻¹ • volume.restrict (Ioo a b)
-- @node: def:gap-identified-measure-cov
/-- For a [latent instrumental-variable model](hyp:M), a [covariate value](hyp:x),
and a [gap index](hyp:k), the [identified gap outcome measure](goal) first
[uses the conditional propensity range decomposition](step:1), then [divides
the difference of the canonical treated outcome submeasures at the two gap
endpoints by the gap length when that length is positive, and otherwise places
unit mass at the model's lower outcome bound](step:2). -/
noncomputable def gapLaw (x : X) (k : ℕ) : Measure ℝ :=
  let D := CondRangeDecomposition M x
  if D.gapLo k < D.gapHi k then
    (ENNReal.ofReal (D.gapHi k - D.gapLo k))⁻¹ •
      (canonSubmeasure M true x (D.gapHi k) - canonSubmeasure M true x (D.gapLo k))
  else Measure.dirac M.yMin
  -- @realizes \mu_{1,k\mid x}(normalized outcome law on nonempty conditional gaps)
/-- For a [latent instrumental-variable model](hyp:M), a [covariate value](hyp:x0),
and an [interval index](hyp:i), the [conditional interval outcome measure](goal)
first [orders the distinct positive propensity levels at that covariate value](step:1),
then [scales the difference of the canonical treated outcome submeasures at
consecutive levels by the reciprocal of their nonnegative separation](step:2). -/
noncomputable def conditionalIntervalLaw (x0 : X) (i : ℕ) : Measure ℝ :=
  let levels := finiteLevels (fun z => M.prop z x0)
  (ENNReal.ofReal (pLevel levels (i+1) - pLevel levels i))⁻¹ •
    (canonSubmeasure M true x0 (pLevel levels (i+1)) -
      canonSubmeasure M true x0 (pLevel levels i))
-- @node: def:g1-canonical
/-- For a [latent instrumental-variable model](hyp:M), a [propensity threshold](hyp:p),
and a [covariate value](hyp:x), the [canonical treated first moment](goal) is
the integral of the outcome against the canonical treated outcome submeasure at that threshold. -/
noncomputable def g1Canon (p : ℝ) (x : X) := ∫ y, y ∂canonSubmeasure M true x p
  -- @realizes g_1^{\mathrm c}(canonical treated first moment)

/-- For a [latent instrumental-variable model](hyp:M), a [covariate value](hyp:x),
and a [gap index](hyp:k), the [uniform gap measure](goal) first [uses the
conditional propensity range decomposition](step:1), then [normalizes Lebesgue
measure on the open interval between the corresponding gap endpoints](step:2). -/
noncomputable def gapUnif (x : X) (k : ℕ) : Measure ℝ :=
  let D := CondRangeDecomposition M x
  uniformInterval (D.gapLo k) (D.gapHi k) -- @realizes \nu_{k\mid x}(normalized Lebesgue restriction on the nonempty k < D.count gap)
/-- For a [latent instrumental-variable model](hyp:M), a [weight function of
covariates and latent rank](hyp:om), a [covariate value](hyp:x), and a [gap
index](hyp:k), the [gap weight distribution](goal) is the image of the uniform
gap measure under the weight function at that covariate value. -/
noncomputable def weightLaw (om : X → ℝ → ℝ) (x : X) (k : ℕ) := (gapUnif M x k).map (om x)
  -- @realizes \rho_{k\mid x}(pushforward gap weight law)
/-- For a [latent instrumental-variable model](hyp:M), a [weight function of
covariates and latent rank](hyp:om), a [covariate value](hyp:x0), and an [interval
index](hyp:i), the [interval weight distribution](goal) first [orders the positive
propensity levels at that covariate value](step:1), then [maps normalized Lebesgue
measure between consecutive levels through the weight function](step:2). -/
noncomputable def weightLawInt (om : X → ℝ → ℝ) (x0 : X) (i : ℕ) :=
  let levels := finiteLevels (fun z => M.prop z x0)
  (uniformInterval (pLevel levels i) (pLevel levels (i+1))).map (om x0)
/-- For a [latent instrumental-variable model](hyp:M), a [weight function of
covariates and latent rank](hyp:om), a [covariate value](hyp:x0), and an [interval
index](hyp:i), the [conditional interval quantile pair](goal) consists of the
quantile functions of the interval outcome measure and the interval weight distribution, in that order. -/
noncomputable def conditionalIntervalQuantiles (om : X → ℝ → ℝ) (x0 : X) (i : ℕ) : (ℝ → ℝ) × (ℝ → ℝ) :=
  (Causalean.Stat.quantile (conditionalIntervalLaw M x0 i), Causalean.Stat.quantile (weightLawInt M om x0 i))
/-- For a [latent instrumental-variable model](hyp:M), a [covariate value](hyp:x),
a [gap index](hyp:k), and a [quantile argument](hyp:t), the [extended gap outcome
quantile](goal) equals the lower outcome bound at zero, the upper outcome bound
at one, and the identified gap outcome measure's quantile at every other argument. -/
noncomputable def endpointGapQuantile (x : X) (k : ℕ) (t : ℝ) :=
  if t = 0 then M.yMin else if t = 1 then M.yMax else Causalean.Stat.quantile (gapLaw M x k) t
-- @node: def:covariate-continuous-lower-bound-quantiles
/-- For a [latent instrumental-variable model](hyp:M), a [weight function of
covariates and latent rank](hyp:om), a [covariate value](hyp:x), and a [gap
index](hyp:k), the [gap quantile pair](goal) consists of the gap outcome quantile
extended to the outcome bounds at zero and one, followed by the gap weight distribution's quantile function. -/
noncomputable def gapQuantiles (om : X → ℝ → ℝ) (x : X) (k : ℕ) : (ℝ → ℝ) × (ℝ → ℝ) := -- @realizes Q_{Y,k\mid x}(lower gap outcome quantile)
  (endpointGapQuantile M x k,
    Causalean.Stat.quantile (weightLaw M om x k)) -- @realizes Q_{\omega,k\mid x}(second component on 0 < t < 1 and nonempty k < K_x gaps)
-- @node: ass:pin-46
/-- For a [latent instrumental-variable model](hyp:M) and a [weight function of
covariates and latent rank](hyp:om), the [conditional lower-inverse requirement](goal)
says that, for almost every covariate value, every positive-length gap indexed below
the component count, and every probability strictly between zero and one, [the outcome
quantile is the infimum of outcome thresholds whose cumulative gap mass within the
outcome domain reaches that probability](step:1), and [the weight quantile is the
infimum of thresholds whose cumulative gap weight mass reaches that probability](step:2). -/
def CondGapQuantilesLowerInverse (om : X → ℝ → ℝ) : Prop :=
  ∀ᵐ x ∂xLaw M, ∀ k, k < (CondRangeDecomposition M x).count →
    (CondRangeDecomposition M x).gapLo k < (CondRangeDecomposition M x).gapHi k →
    ∀ t ∈ Ioo (0 : ℝ) 1,
      (gapQuantiles M om x k).1 t =
        sInf {y : ℝ | t ≤ (gapLaw M x k (M.Yset ∩ Iic y)).toReal} ∧
      (gapQuantiles M om x k).2 t =
        sInf {v : ℝ | t ≤ (weightLaw M om x k (Iic v)).toReal}
-- @node: ass:pin-59
/-- For a [latent instrumental-variable model](hyp:M) and a [weight function of
covariates and latent rank](hyp:om), the [conditional lower-quantile interpretation](goal)
requires, for almost every covariate value, every positive-length gap indexed below
the component count, and every probability strictly between zero and one, [the outcome
quantile to equal the infimum of thresholds at which cumulative gap mass within the
outcome domain reaches that probability](step:1), and [the weight quantile to equal
the infimum of thresholds at which cumulative gap weight mass reaches it](step:2). -/
def CondGapQuantilesLowerInverseReading (om : X → ℝ → ℝ) : Prop :=
  ∀ᵐ x ∂xLaw M, ∀ k, k < (CondRangeDecomposition M x).count →
    (CondRangeDecomposition M x).gapLo k < (CondRangeDecomposition M x).gapHi k →
    ∀ t ∈ Ioo (0 : ℝ) 1,
      (gapQuantiles M om x k).1 t =
        sInf {y : ℝ | t ≤ (gapLaw M x k (M.Yset ∩ Iic y)).toReal} ∧
      (gapQuantiles M om x k).2 t =
        sInf {v : ℝ | t ≤ (weightLaw M om x k (Iic v)).toReal}
-- @node: ass:bk-3
/-- For a [latent instrumental-variable model](hyp:M) and a [candidate family of
gap outcome quantiles](hyp:Q), the [endpoint extension requirement](goal) says that
on every positive-length gap indexed below the conditional component count, [the
quantile at zero equals the lower outcome bound](step:1) and [the quantile at one
equals the upper outcome bound](step:2). -/
def GapQuantileEndpointExtension (Q : X → ℕ → ℝ → ℝ) : Prop :=
  ∀ x k, k < (CondRangeDecomposition M x).count →
    (CondRangeDecomposition M x).gapLo k < (CondRangeDecomposition M x).gapHi k →
    Q x k 0 = M.yMin ∧ Q x k 1 = M.yMax
-- @node: ass:pin-48
/-- For a [latent instrumental-variable model](hyp:M) and a [candidate family of
gap outcome quantiles](hyp:Q), the [rank-kernel extension requirement](goal) requires
[joint measurability in covariates, gap index, and quantile argument](step:1) and,
[for almost every covariate value and every positive-length gap indexed below the
component count, values in the outcome domain throughout the closed unit interval
and agreement with the gap outcome quantile throughout its interior](step:2). -/
def RankKernelExtensionReading (Q : X → ℕ → ℝ → ℝ) : Prop :=
  Measurable (fun a : X × ℕ × ℝ => Q a.1 a.2.1 a.2.2) ∧
  ∀ᵐ x ∂xLaw M, ∀ k, k < (CondRangeDecomposition M x).count →
    (CondRangeDecomposition M x).gapLo k < (CondRangeDecomposition M x).gapHi k →
    (∀ t ∈ Icc (0 : ℝ) 1, Q x k t ∈ M.Yset) ∧
    (∀ t ∈ Ioo (0 : ℝ) 1, Q x k t = Causalean.Stat.quantile (gapLaw M x k) t)

/-- For a [latent instrumental-variable model](hyp:M), a [weight function](hyp:om),
a [covariate value](hyp:x), a [gap index](hyp:k), and a [weight threshold](hyp:v),
the [weight cumulative distribution value](goal) is the real-valued gap weight
mass at or below that threshold. -/
noncomputable def weightCDF (om : X → ℝ → ℝ) (x : X) (k : ℕ) (v : ℝ) := -- @realizes F_{\omega,k\mid x}(weight distribution function)
  (weightLaw M om x k (Iic v)).toReal
/-- For a [latent instrumental-variable model](hyp:M), a [weight function](hyp:om),
a [covariate value](hyp:x), a [gap index](hyp:k), and a [weight threshold](hyp:v),
the [left cumulative distribution value](goal) is the real-valued gap weight mass
strictly below that threshold. -/
noncomputable def weightCDFLeft (om : X → ℝ → ℝ) (x : X) (k : ℕ) (v : ℝ) :=
  (weightLaw M om x k (Iio v)).toReal
/-- For a [latent instrumental-variable model](hyp:M), a [weight function](hyp:om),
a [covariate value](hyp:x), a [gap index](hyp:k), a [latent rank](hyp:u), and a
[tie-breaking coordinate](hyp:s), the [randomized weight rank](goal) is the gap
weight mass strictly below the weight at that rank plus the tie-breaking coordinate
times the mass equal to that weight. -/
noncomputable def randomizedRank (om : X → ℝ → ℝ) (x : X) (k : ℕ) (u s : ℝ) :=
  weightCDFLeft M om x k (om x u) + s *
    (weightCDF M om x k (om x u) - weightCDFLeft M om x k (om x u))
  -- @realizes R_{k,x}(randomized rank formula)
/-- For a [latent instrumental-variable model](hyp:M), a [weight function](hyp:om),
a [family of gap outcome quantiles](hyp:Q), a [covariate value](hyp:x), a [gap
index](hyp:k), and a [latent rank](hyp:u), the [attaining gap outcome measure](goal)
is the distribution of the outcome quantile evaluated at one minus the randomized
weight rank, with a uniform tie-breaking coordinate. -/
noncomputable def gapAttainingLaw (om : X → ℝ → ℝ) (Q : X → ℕ → ℝ → ℝ)
    (x : X) (k : ℕ) (u : ℝ) :=
  Causalean.Stat.unifOI.map (fun s => Q x k (1 - randomizedRank M om x k u s))
  -- @realizes S(auxiliary uniform coordinate integrated out)
/-- For a [latent instrumental-variable model](hyp:M), a [weight function](hyp:om),
a [family of gap outcome quantiles](hyp:Q), a [covariate value](hyp:x), and a
[latent rank](hyp:u), the [pasted attaining outcome measure](goal) first [uses the
conditional propensity range decomposition](step:1), then [uses the attaining gap
measure on a gap indexed below the component count; otherwise, on the tail, places
unit mass at the lower outcome bound for a nonnegative weight and the upper bound
for a negative weight; and elsewhere uses the treated latent outcome kernel](step:2). -/
noncomputable def pastedAttainingLaw (om : X → ℝ → ℝ) (Q : X → ℕ → ℝ → ℝ)
    (x : X) (u : ℝ) : Measure ℝ :=
  let D := CondRangeDecomposition M x
  if h : ∃ k, k < D.count ∧ u ∈ RangeDecomposition.gap D k then
    gapAttainingLaw M om Q x (Classical.choose h) u
  else if u ∈ D.tail then Measure.dirac (if 0 ≤ om x u then M.yMin else M.yMax)
  else outcomeKernel (latentMarginal M true) (u,x)


/-- For a [latent instrumental-variable model](hyp:M), a [weight function](hyp:om),
a [family of gap outcome quantiles](hyp:Q), and a [candidate outcome kernel](hyp:K),
the [attaining-kernel version condition](goal) requires [a probability kernel](step:1),
[zero mass outside the outcome domain at every rank and covariate pair](step:2),
[agreement with the pasted attaining measure almost everywhere under the product of
the uniform rank law and the covariate law](step:3), and [for almost every covariate
value, agreement with the attaining gap measure at every rank in each gap indexed
below the component count](step:4). -/
def IsAttainingKernelVersion (om : X → ℝ → ℝ) (Q : X → ℕ → ℝ → ℝ)
    (K : Kernel (ℝ × X) ℝ) : Prop :=
  IsMarkovKernel K ∧ -- @realizes \pi_{1,x}^\star(one jointly measurable probability kernel)
  (∀ ux, K ux M.Ysetᶜ = 0) ∧ -- @realizes \pi_{1,x}^\star(outcome support in every branch, including boundaries)
  (K =ᵐ[Causalean.Stat.unifOI.prod (xLaw M)]
    fun ux => pastedAttainingLaw M om Q ux.2 ux.1) ∧
  (∀ᵐ x ∂xLaw M, ∀ k < (CondRangeDecomposition M x).count,
    ∀ u ∈ RangeDecomposition.gap (CondRangeDecomposition M x) k,
      K (u,x) = gapAttainingLaw M om Q x k u)


/-- For a [latent instrumental-variable model](hyp:M), a [choice of upper rather
than lower bound](hyp:upper), a [weight function](hyp:om), and a [covariate
value](hyp:x), the [conditional bound integrand](goal) first [uses the conditional
propensity range decomposition](step:1), then [adds gap quantile products weighted
by nonnegative gap lengths, integrals of the canonical treated first-moment derivative
times the weight over component intervals, and the tail contribution](step:2).
Gap quantiles are paired at equal ranks for the upper bound and opposite ranks for
the lower bound; tail contributions pair positive weights with the upper outcome
bound and negative weights with the lower outcome bound for the upper bound, and
reverse these choices for the lower bound. -/
noncomputable def conditionalBoundIntegrand (upper : Bool) (om : X → ℝ → ℝ) (x : X) : ℝ :=
  let D := CondRangeDecomposition M x
  (∑ k ∈ Finset.range D.count, max 0 (D.gapHi k - D.gapLo k) *
    ∫ t in Ioo (0 : ℝ) 1, (gapQuantiles M om x k).1 t *
      (gapQuantiles M om x k).2 (if upper then t else 1-t)) +
  (∑ k ∈ Finset.range D.count, ∫ u in D.liv k, deriv (fun p => g1Canon M p x) u * om x u) +
  ∫ u in D.tail, (if upper then M.yMax else M.yMin) * max 0 (om x u) +
    (if upper then M.yMin else M.yMax) * min 0 (om x u)
/-- For a [latent instrumental-variable model](hyp:M) and a [weight function](hyp:om),
the [covariate-averaged lower value](goal) is the integral of the conditional lower
bound integrand under the covariate law. -/
noncomputable def covariateLowerValue (om : X → ℝ → ℝ) := ∫ x, conditionalBoundIntegrand M false om x ∂xLaw M
/-- For a [latent instrumental-variable model](hyp:M) and a [weight function](hyp:om),
the [covariate-averaged upper value](goal) is the integral of the conditional upper
bound integrand under the covariate law. -/
noncomputable def covariateUpperValue (om : X → ℝ → ℝ) := ∫ x, conditionalBoundIntegrand M true om x ∂xLaw M
/-- For a [latent instrumental-variable model](hyp:M), the [outcome magnitude](goal)
is the larger of the absolute values of its lower and upper outcome bounds. -/
noncomputable def outcomeMagnitude := max |M.yMin| |M.yMax|
  -- @realizes B_Y(maximum absolute outcome endpoint)

-- No-covariate objects use the almost-sure covariate value, without restricting its carrier type.
-- @node: def:y-identified-measure
/-- For a [latent instrumental-variable model](hyp:M), a [covariate value](hyp:x0)
[equal to the covariate almost surely](hyp:hX), and an [interval index below the
number of positive propensity levels](hyp:i), the [identified interval outcome
measure without covariate variation](goal) is the conditional interval outcome
measure at that covariate value and index. -/
noncomputable def intervalLaw (x0 : X) (hX : ∀ᵐ s ∂M.law.toMeasure, M.Xv s = x0)
    (i : Fin (finiteLevels (fun z => M.prop z x0)).length) : Measure ℝ :=
  conditionalIntervalLaw M x0 i
  -- @realizes \mu_{1,i}(no-covariate identified law, i < K)
-- @node: def:gap-identified-measure
/-- For a [latent instrumental-variable model](hyp:M), a [covariate value](hyp:x0)
[equal to the covariate almost surely](hyp:hX), and a [gap index below the conditional
component count](hyp:k) [whose lower endpoint is strictly below its upper
endpoint](hyp:_hk), the [identified gap outcome measure without covariate
variation](goal) first [uses the conditional propensity range decomposition](step:1),
then [divides the difference of the canonical treated outcome submeasures at the
upper and lower gap endpoints by the gap length](step:2). -/
noncomputable def gapLaw0 (x0 : X) (hX : ∀ᵐ s ∂M.law.toMeasure, M.Xv s = x0)
    (k : Fin (CondRangeDecomposition M x0).count)
    (_hk : (CondRangeDecomposition M x0).gapLo k <
      (CondRangeDecomposition M x0).gapHi k) : Measure ℝ :=
  let D := CondRangeDecomposition M x0
  (ENNReal.ofReal (D.gapHi k - D.gapLo k))⁻¹ •
    (canonSubmeasure0 M x0 hX true (D.gapHi k) - canonSubmeasure0 M x0 hX true (D.gapLo k))
  -- @realizes \mu_{1,k}(no-covariate law on a nonempty gap, k < K)
-- @node: def:g1-canonical-no-covariates
/-- For a [latent instrumental-variable model](hyp:M), a [covariate value](hyp:x0)
[equal to the covariate almost surely](hyp:hX), and a [propensity threshold](hyp:p),
the [canonical treated first moment without covariate variation](goal) is the
integral of the outcome over the outcome domain against the canonical treated
outcome submeasure at that threshold. -/
noncomputable def g1Canon0 (x0 : X) (hX : ∀ᵐ s ∂M.law.toMeasure, M.Xv s = x0) (p : ℝ) := ∫ y in M.Yset, y ∂canonSubmeasure0 M x0 hX true p
  -- @realizes g_1^{\mathrm c}(canonical no-covariate treated mean)
-- @node: def:discrete-lower-bound-quantiles
/-- For a [latent instrumental-variable model](hyp:M), a [covariate value](hyp:x0)
[equal to the covariate almost surely](hyp:hX), a [weight function of latent
rank](hyp:om), and an [interval index below the number of positive propensity
levels](hyp:i), the [interval quantile pair without covariate variation](goal)
consists of the identified interval outcome measure's quantile function followed
by the quantile function of the interval weight distribution. -/
noncomputable def intervalQuantiles (x0 : X) (hX : ∀ᵐ s ∂M.law.toMeasure, M.Xv s = x0) (om : ℝ → ℝ) -- @realizes Q_{Y,i}(one lower outcome quantile in the no-covariate world)
    (i : Fin (finiteLevels (fun z => M.prop z x0)).length) :=
  (Causalean.Stat.quantile (intervalLaw M x0 hX i),
    Causalean.Stat.quantile (weightLawInt M (fun _ => om) x0 i))
  -- @realizes Q_{\omega,i}(one lower weight quantile in the no-covariate world)
-- @node: def:continuous-lower-bound-quantiles
/-- For a [latent instrumental-variable model](hyp:M), a [covariate value](hyp:x0)
[equal to the covariate almost surely](hyp:hX), a [weight function of latent
rank](hyp:om), and a [gap index below the conditional component count](hyp:k)
[whose lower endpoint is strictly below its upper endpoint](hyp:hk), the [gap
quantile pair without covariate variation](goal) consists of the identified gap
outcome measure's quantile function followed by the gap weight distribution's
quantile function. -/
noncomputable def gapQuantiles0 (x0 : X) (hX : ∀ᵐ s ∂M.law.toMeasure, M.Xv s = x0) (om : ℝ → ℝ) -- @realizes Q_{Y,k}(one lower outcome quantile on a nonempty no-covariate gap)
    (k : Fin (CondRangeDecomposition M x0).count)
    (hk : (CondRangeDecomposition M x0).gapLo k <
      (CondRangeDecomposition M x0).gapHi k) :=
  (Causalean.Stat.quantile (gapLaw0 M x0 hX k hk),
    Causalean.Stat.quantile (weightLaw M (fun _ => om) x0 k)) -- @realizes Q_{\omega,k}(second component on 0 < t < 1; nonempty Fin K gap)
/-- For a [weight function of covariates and latent rank](hyp:om), a [covariate
value](hyp:x), and a [rank in the closed unit interval](hyp:u), the [weight at
fixed covariates](goal) is the weight function evaluated at that covariate value
and rank. -/
def fixedWeight (om : X → ℝ → ℝ) (x : X) (u : Icc (0 : ℝ) 1) := om x u.val -- @realizes T_x(weight map at a fixed covariate)

-- @node: finiteLevels_mem
/-- If [the instrument space is finite](hyp:hfinite) and [a real number belongs
to the ordered list of positive propensity levels](hyp:hr), then [it is a value
of the propensity function and is strictly positive](goal). -/
lemma finiteLevels_mem (p : Z → ℝ) (hfinite : Finite Z) {r : ℝ}
    (hr : r ∈ finiteLevels p) : r ∈ range p ∩ Ioi 0 := by
  letI : Finite Z := hfinite
  have hf : (range p ∩ Ioi 0).Finite := (finite_range p).inter_of_left _
  simpa only [finiteLevels, dif_pos hf, Finset.mem_sort, hf.mem_toFinset] using hr

-- @node: finiteLevels_sorted
/-- If [the instrument space is finite](hyp:hfinite), then [the ordered list of
positive propensity levels is strictly increasing](goal). -/
lemma finiteLevels_sorted (p : Z → ℝ) (hfinite : Finite Z) :
    (finiteLevels p).SortedLT := by
  letI : Finite Z := hfinite
  have hf : (range p ∩ Ioi 0).Finite := (finite_range p).inter_of_left _
  simpa only [finiteLevels, dif_pos hf] using hf.toFinset.sortedLT_sort

-- @node: finite_levels_ranges
/-- If [every propensity value lies in the closed unit interval](hyp:hp) and
[the instrument space is finite](hyp:hfinite), then [the ordered levels, including
the structural endpoints through one index beyond the list, lie in the closed
unit interval; consecutive levels strictly increase up to the last listed level;
and all intervals indexed from zero through the list's length lie in the closed
unit interval](goal). -/
lemma finite_levels_ranges (p : Z → ℝ) (hp : ∀ z, p z ∈ Icc (0 : ℝ) 1) -- @realizes p_i(ordered propensity levels in [0,1]) @realizes I_i(identified and tail intervals inside [0,1])
    (hfinite : Finite Z) :
    (∀ i ≤ (finiteLevels p).length + 1, pLevel (finiteLevels p) i ∈ Icc (0 : ℝ) 1) ∧
    (∀ i < (finiteLevels p).length, pLevel (finiteLevels p) i < pLevel (finiteLevels p) (i+1)) ∧
    (∀ i ≤ (finiteLevels p).length, finiteInterval (finiteLevels p) i ⊆ Icc (0 : ℝ) 1) := by
  have hmem : ∀ r ∈ finiteLevels p, 0 < r ∧ r ≤ 1 := by
    intro r hr
    obtain ⟨⟨z, rfl⟩, hpos⟩ := finiteLevels_mem p hfinite hr
    exact ⟨hpos, (hp z).2⟩
  have hlevel : ∀ i, pLevel (finiteLevels p) i ∈ Icc (0 : ℝ) 1 := by
    intro i
    by_cases hi : i = 0
    · simp [pLevel, hi]
    by_cases hil : i ≤ (finiteLevels p).length
    · have hidx : i - 1 < (finiteLevels p).length := by omega
      have hm := hmem _ (List.get_mem (finiteLevels p) ⟨i-1, hidx⟩)
      simpa only [pLevel, if_neg hi, if_pos hil,
        List.getD_eq_getElem _ _ hidx, List.get_eq_getElem] using
        (show (finiteLevels p).get ⟨i-1, hidx⟩ ∈ Icc (0 : ℝ) 1 from
          ⟨hm.1.le, hm.2⟩)
    · simp [pLevel, hi, hil]
  refine ⟨fun i _ => hlevel i, ?_, ?_⟩
  · intro i hi
    have hnext : i + 1 ≤ (finiteLevels p).length := by omega
    have hn : i + 1 ≠ 0 := by omega
    by_cases hz : i = 0
    · have hm := hmem _ (List.get_mem (finiteLevels p) ⟨i, hi⟩)
      simpa only [pLevel, if_pos hz, if_neg hn, if_pos hnext,
        Nat.add_sub_cancel, List.getD_eq_getElem _ _ hi, List.get_eq_getElem] using hm.1
    · have hil : i ≤ (finiteLevels p).length := hi.le
      have hprev : i - 1 < (finiteLevels p).length := by omega
      have hs := (finiteLevels_sorted p hfinite).strictMono_get
        (show (⟨i-1, hprev⟩ : Fin (finiteLevels p).length) < ⟨i, hi⟩ by
          simp only [Fin.mk_lt_mk]; omega)
      simpa only [pLevel, if_neg hz, if_pos hil, if_neg hn, if_pos hnext,
        Nat.add_sub_cancel, List.getD_eq_getElem _ _ hprev,
        List.getD_eq_getElem _ _ hi, List.get_eq_getElem] using hs
  · intro i hi u hu
    exact ⟨(hlevel i).1.trans hu.1.le, hu.2.trans (hlevel (i+1)).2⟩

-- @node: latent_initial_intervals_ranges
/-- If [every propensity value lies in the closed unit interval](hyp:hp) and
[the instrument space is finite](hyp:hfinite), then [the initial latent interval
lies in the closed unit interval, as do the intervals at indices one and two
whenever there are at least one and two positive propensity levels, respectively](goal). -/
lemma latent_initial_intervals_ranges (p : Z → ℝ) (hp : ∀ z, p z ∈ Icc (0 : ℝ) 1)
    (hfinite : Finite Z) :
    (latentInterval0 p ⊆ Icc (0 : ℝ) 1) ∧ -- @realizes I_0(latent interval contained in [0,1])
    (1 ≤ (finiteLevels p).length → latentInterval1 p ⊆ Icc (0 : ℝ) 1) ∧ -- @realizes I_1(latent interval contained in [0,1] when index 1 is present)
    (2 ≤ (finiteLevels p).length → latentInterval2 p ⊆ Icc (0 : ℝ) 1) := by -- @realizes I_2(latent interval contained in [0,1] when index 2 is present)
  have hr := (finite_levels_ranges p hp hfinite).2.2
  refine ⟨?_, fun hi => hr 1 hi, fun hi => hr 2 hi⟩
  simpa [latentInterval0, finiteInterval, pLevel] using hr 0 (Nat.zero_le _)

-- @node: uniformInterval_isProbability
/-- If [the lower interval endpoint is strictly below the upper endpoint](hyp:hab),
then [normalized Lebesgue measure on the open interval between them is a probability
measure](goal). -/
lemma uniformInterval_isProbability (a b : ℝ) (hab : a < b) :
    IsProbabilityMeasure (uniformInterval a b) := by
  constructor
  rw [uniformInterval, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ]
  simp only [univ_inter, Real.volume_Ioo, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hab))
    ENNReal.ofReal_ne_top

-- @node: gap_uniform_probability
/-- Under [the model's structural assumptions](hyp:h), [finitely many connected
components of the instrument space](hyp:hc), and [continuity of the propensity on
each component for almost every covariate value](hyp:hp), [for almost every
covariate value, the uniform gap measure is a probability measure on every
positive-length gap indexed below the conditional component count](goal). -/
lemma gap_uniform_probability (h : StructuralAssumptions M)
    (hc : FiniteInstrumentComponents Z) (hp : PropensityContinuousOnComponents M) :
    ∀ᵐ x ∂xLaw M, ∀ k < (CondRangeDecomposition M x).count,
      (CondRangeDecomposition M x).gapLo k < (CondRangeDecomposition M x).gapHi k →
      IsProbabilityMeasure (gapUnif M x k) := by -- @realizes \nu_{k\mid x}(probability law for nonempty conditional gaps with k < K_x)
  filter_upwards [] with x
  intro k hk hab
  exact uniformInterval_isProbability _ _ hab

-- @node: liv_interval_range
/-- If [a finite interval representation validly decomposes a real set](hyp:hD),
then [its component interval at any index below the component count is contained
in the closed unit interval](goal). -/
lemma liv_interval_range (D : RangeData) (R : Set ℝ) (hD : D.Valid R) (k : Fin D.count) :
    D.liv k ⊆ Icc (0 : ℝ) 1 := by
  have hk : (k : ℕ) < D.1 := k.isLt
  have he := hD.1 ⟨k, hk⟩
  intro u hu
  simp only [RangeData.liv, RangeData.low, RangeData.high, dif_pos hk, mem_Icc] at hu
  exact ⟨he.1.trans hu.1, hu.2.trans he.2.2⟩
  -- @realizes L_k(closed LIV intervals lie in [0,1])

-- @node: ass:pin-44
/-- For a [latent instrumental-variable model](hyp:M), a [covariate value](hyp:x0)
[equal to the covariate almost surely](hyp:hX), and a [weight function of latent
rank](hyp:om), the [interval lower-quantile requirement](goal) says that, for every
interval indexed below the number of positive propensity levels and every probability
strictly between zero and one, [the outcome quantile is the infimum of thresholds
whose cumulative interval outcome mass within the outcome domain reaches that
probability](step:1), and [the weight quantile is the infimum of thresholds whose
cumulative interval weight mass reaches that probability](step:2). -/
def IntervalLowerQuantileReading (x0 : X) (hX : ∀ᵐ s ∂M.law.toMeasure, M.Xv s = x0) (om : ℝ → ℝ) : Prop :=
  ∀ i : Fin (finiteLevels (fun z => M.prop z x0)).length,
    ∀ t ∈ Ioo (0 : ℝ) 1,
      (intervalQuantiles M x0 hX om i).1 t =
        sInf {y : ℝ | t ≤ (intervalLaw M x0 hX i (M.Yset ∩ Iic y)).toReal} ∧
      (intervalQuantiles M x0 hX om i).2 t =
        sInf {v : ℝ | t ≤ (weightLawInt M (fun _ => om) x0 i (Iic v)).toReal}
-- @node: ass:pin-45
/-- For a [latent instrumental-variable model](hyp:M), a [covariate value](hyp:x0)
[equal to the covariate almost surely](hyp:hX), and a [weight function of latent
rank](hyp:om), the [gap lower-quantile requirement](goal) says that, on every
positive-length gap indexed below the conditional component count and at every
probability strictly between zero and one, [the outcome member of the gap quantile
pair equals the identified gap outcome measure's quantile](step:1) and [the weight
member equals the gap weight distribution's quantile](step:2). -/
def GapLowerQuantileReading (x0 : X) (hX : ∀ᵐ s ∂M.law.toMeasure, M.Xv s = x0) (om : ℝ → ℝ) : Prop :=
  ∀ k : Fin (CondRangeDecomposition M x0).count,
    ∀ hk : (CondRangeDecomposition M x0).gapLo k <
      (CondRangeDecomposition M x0).gapHi k,
      ∀ t ∈ Ioo (0 : ℝ) 1,
        (gapQuantiles0 M x0 hX om k hk).1 t = Causalean.Stat.quantile (gapLaw0 M x0 hX k hk) t ∧
        (gapQuantiles0 M x0 hX om k hk).2 t = Causalean.Stat.quantile
          (weightLaw M (fun _ => om) x0 k) t

end Papers.TbsPrteOptimalTransport
