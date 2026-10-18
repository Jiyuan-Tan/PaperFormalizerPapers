module
public import Papers.TbsPrteOptimalTransport.Helpers.Ranges
public import Toolkit.Foundations.Probability.Conditioning.FiniteValuedConditionalExpectation
public import Toolkit.Tricks.Probability.Moments.QuantileVersions
/-! Finite instrument levels and the population components of the bounds. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set
open scoped Classical ENNReal
universe u v
-- @env: S4
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

/-- For [instrument values](hyp:Z) and [covariate values](hyp:X), [level data](goal)
record the number of baseline levels, policy-level counts within each baseline bin,
the corresponding instrument classes, and their covariate-dependent propensity levels. -/
structure LevelData (Z X : Type v) where
  K : ℕ -- @realizes K(positive baseline level count)
  l : ℕ → ℕ -- @realizes l_k(policy level counts)
  S : ℕ → Finset Z -- @realizes S_k(baseline equality classes)
  T : ℕ → ℕ → Finset Z -- @realizes T_{j,k}(policy equality classes)
  pLev : ℕ → X → ℝ -- @realizes p_k(baseline level functions)
  qLev : ℕ → ℕ → X → ℝ -- @realizes q_{j,k}(policy level functions)

/-- Given [baseline propensities](hyp:prop), [policy propensities](hyp:q),
[covariates](hyp:x), and [a baseline-bin index](hyp:k), [the ordered policy levels in
that bin](goal) are obtained by [listing the distinct positive baseline levels](step:1),
[taking the bin's lower endpoint](step:2), [taking its upper endpoint](step:3), and
[sorting the distinct policy values between those endpoints, excluding the upper
endpoint except in the final bin](step:4). -/
noncomputable def policyLevelsAt (prop q : Z → X → ℝ) (x : X) (k : ℕ) : List ℝ :=
  let ps := finiteLevels (fun z => prop z x)
  let a := pLevel ps k
  let b := pLevel ps (k+1)
  ((Finset.univ.image (fun z => q z x)).filter
    (fun v => a ≤ v ∧ if k < ps.length then v < b else v ≤ b)).sort (· ≤ ·)
-- @node: def:policy-level-sets
/-- Given [baseline propensities](hyp:prop), [policy propensities](hyp:q), and
[reference covariates](hyp:x0), [the canonical level structure](goal) is constructed by
[listing the reference baseline levels](step:1), [defining baseline levels at every
covariate value](step:2), [listing policy levels in each bin](step:3), [extending those
policy lists by baseline endpoints](step:4), and [collecting the reference level
counts and equality classes together with the level functions](step:5). -/
noncomputable def LevelStructure (prop q : Z → X → ℝ) (x0 : X) : LevelData Z X :=
  let ps := finiteLevels (fun z => prop z x0)
  let p := fun k x => pLevel (finiteLevels (fun z => prop z x)) k
  let qs := policyLevelsAt prop q
  let ql := fun k j x => if j = 0 then p k x else
    if j ≤ (qs x k).length then (qs x k).getD (j-1) 0 else p (k+1) x
  ⟨ps.length, fun k => (qs x0 k).length,
    fun k => Finset.univ.filter (fun z => prop z x0 = p k x0),
    fun k j => if j = 0 ∨ (qs x0 k).length < j then ∅ else
      Finset.univ.filter (fun z => q z x0 = ql k j x0), p, ql⟩
/-- For [baseline propensities](hyp:prop), [policy propensities](hyp:q), and
[fixed covariates](hyp:x), [the combined propensity range](goal) contains all values
attained by either propensity across instrument values. -/
def combinedPropensityRange (prop q : Z → X → ℝ) (x : X) : Set ℝ := -- @realizes R_x(combined population propensity-value set)
  range (fun z => prop z x) ∪ range (fun z => q z x)

/-- For [baseline propensities](hyp:prop), [policy propensities](hyp:q), and
[a proposed separation constant](hyp:cgap), [uniform gap separation](goal) requires
[the constant to be positive](step:1) and [any two combined propensity values at the
same covariates to be equal or more than that constant apart](step:2). -/
def PropensityGapSeparationWitness (prop q : Z → X → ℝ) (cgap : ℝ) : Prop :=
  0 < cgap ∧ ∀ x, ∀ v ∈ combinedPropensityRange prop q x, -- @realizes c_{\text{gap}}(one positive separation constant)
    ∀ v' ∈ combinedPropensityRange prop q x, v' = v ∨ cgap < |v-v'|

-- @node: ass:prop-gap-invariant-order
/-- For [baseline propensities](hyp:prop), [policy propensities](hyp:q), and
[level data](hyp:L), [invariance of the level structure across covariates](goal)
requires [baseline levels to match the ordered baseline values](step:1),
[policy levels to match their bin lists with baseline endpoints](step:2),
[endpoint policy classes to be empty](step:3), [the baseline count to be constant](step:4),
[each bin's policy count to be constant](step:5), [baseline classes to equal the
corresponding propensity equality classes](step:6), [interior policy classes to equal
their propensity equality classes](step:7), [baseline levels to be strictly ordered](step:8),
[interior policy levels to be strictly ordered](step:9), [both input propensities to
lie in the unit interval](step:10), [baseline levels on their index domain to lie in
the unit interval](step:11), and [policy levels on their index domain to lie in the
unit interval](step:12). -/
def LevelOrderInvariant (prop q : Z → X → ℝ) (L : LevelData Z X) : Prop :=
  (∀ x k, k ≤ L.K + 1 → L.pLev k x = pLevel (finiteLevels (fun z => prop z x)) k) ∧
  (∀ x k j, k ≤ L.K → j ≤ L.l k + 1 →
    L.qLev k j x = if j = 0 then L.pLev k x else
      if j ≤ L.l k then (policyLevelsAt prop q x k).getD (j-1) 0 else L.pLev (k+1) x) ∧
  (∀ k, k ≤ L.K → L.T k 0 = ∅ ∧ L.T k (L.l k + 1) = ∅) ∧
  (∀ x, (finiteLevels (fun z => prop z x)).length = L.K) ∧
  (∀ x k, k ≤ L.K → (policyLevelsAt prop q x k).length = L.l k) ∧
  (∀ x k z, k ≤ L.K → (z ∈ L.S k ↔ prop z x = L.pLev k x)) ∧
  (∀ x k j z, k ≤ L.K → 1 ≤ j → j ≤ L.l k → (z ∈ L.T k j ↔ q z x = L.qLev k j x)) ∧
  (∀ x i j, i < j → j ≤ L.K → L.pLev i x < L.pLev j x) ∧
  (∀ x k i j, k ≤ L.K → 1 ≤ i → i < j → j ≤ L.l k → L.qLev k i x < L.qLev k j x) ∧
  (∀ z x, prop z x ∈ Icc (0 : ℝ) 1 ∧ q z x ∈ Icc (0 : ℝ) 1) ∧ -- @realizes R_x(both input propensities in [0,1])
  (∀ x k, k ≤ L.K + 1 → L.pLev k x ∈ Icc (0 : ℝ) 1) ∧ -- @realizes p_k(population baseline levels on their paper index domain) @realizes p_i(covariate-indexed baseline levels in [0,1])
  (∀ x k j, k ≤ L.K → j ≤ L.l k + 1 → L.qLev k j x ∈ Icc (0 : ℝ) 1) -- @realizes q_{j,k}(population policy levels on their paper index domain)
-- @node: ass:prop-gap-boundary-distinct
/-- For [level data](hyp:L), [policy levels being off the lower boundary](goal)
means that every nonempty interior policy class in a bin before the final bin has
a level different from that bin's lower baseline level at every covariate value. -/
def PolicyLevelOffBoundary (L : LevelData Z X) : Prop :=
  ∀ k < L.K, ∀ j, 1 ≤ j → j ≤ L.l k →
    (L.T k j).Nonempty → ∀ x, L.qLev k j x ≠ L.pLev k x
-- @node: ass:discrete-reduction-finite
/-- For [an instrument domain with a topology](hyp:Z), [finite discrete
reduction](goal) requires [finitely many instrument values](step:1) and [the discrete
topology on those values](step:2). -/
def InstrumentFiniteReduction (Z : Type v) [TopologicalSpace Z] : Prop :=
  Finite Z ∧ DiscreteTopology Z -- @realizes \mathcal{Z}(finite instrument domain with its discrete topology)
/-- Under [the latent instrumental-variable model](hyp:M), [the conditional
instrument probability](goal) is the real-valued probability of [instrument value](hyp:z)
given [covariates](hyp:x). -/
noncomputable def instProb (z : Z) (x : X) := (M.instKernel x {z}).toReal
  -- @realizes \pi(conditional instrument point probability)
-- @node: instrument_singleton_pos
/-- If [the conditional instrument distribution has common full support](hyp:hSupport)
and [the instrument domain is finite and discrete](hyp:hFinite), then [every
instrument value has positive conditional probability for almost every covariate
value](goal). -/
lemma instrument_singleton_pos [DiscreteTopology Z] (hSupport : CommonInstrumentSupport M)
    (hFinite : InstrumentFiniteReduction Z) :
    ∀ᵐ x ∂xLaw M, ∀ z : Z, 0 < M.instKernel x {z} := by
  obtain ⟨κ, hκ, hversion, hfull⟩ := hSupport
  filter_upwards [M.instKernel_version, hversion] with x hx hκx
  intro z
  rw [hx, ← hκx]
  exact hfull x {z} (isOpen_discrete _) (singleton_nonempty z)

-- @node: def:level-set-probabilities
/-- Under [the latent instrumental-variable model](hyp:M) and [level data](hyp:L),
[the level-set probabilities](goal) are the conditional instrument probabilities
summed separately over each baseline class and each policy class. -/
noncomputable def levelSetProb (L : LevelData Z X) :
    (ℕ → X → ℝ) × (ℕ → ℕ → X → ℝ) :=
  (fun k x => ∑ z ∈ L.S k, instProb M z x,
   fun k j x => ∑ z ∈ L.T k j, instProb M z x)
  -- @realizes \pi_k(baseline set probabilities) @realizes \tau_{j,k}(policy set probabilities)
/-- For [level data](hyp:L) and [a baseline-bin index](hyp:k), [the higher-policy
instrument set](goal) is the union of policy classes in all strictly higher bins,
including policy indices from zero through each bin's policy count. -/
noncomputable def higherPolicy (L : LevelData Z X) (k : ℕ) : Finset Z :=
  (Finset.range (L.K+1)).biUnion (fun i => if k < i then
    (Finset.range (L.l i+1)).biUnion (L.T i) else ∅)
/-- For [level data](hyp:L) and [a baseline-bin index](hyp:k), [the higher-baseline
instrument set](goal) is the union of baseline classes with strictly larger indices
through the final baseline index. -/
noncomputable def higherBaseline (L : LevelData Z X) (k : ℕ) : Finset Z :=
  (Finset.range (L.K+1)).biUnion (fun i => if k < i then L.S i else ∅)
/-- For [level data](hyp:L), [a baseline bin](hyp:k), and [a starting policy
index](hyp:j), [the policy upper union](goal) contains the instrument values in
policy classes from that index through the bin's policy count. -/
noncomputable def policyUnion (L : LevelData Z X) (k j : ℕ) : Finset Z :=
  (Finset.range (L.l k+1)).biUnion (fun i => if j ≤ i then L.T k i else ∅)
/-- Under [the model](hyp:M), for [level data](hyp:L), [a baseline bin](hyp:k), and
[covariates](hyp:x), [the full-bin probability contrast](goal) is the conditional
probability of the higher-policy instrument set minus that of the higher-baseline set. -/
noncomputable def gammaFull (L : LevelData Z X) (k : ℕ) (x : X) :=
  (∑ z ∈ higherPolicy L k, instProb M z x) - ∑ z ∈ higherBaseline L k, instProb M z x
  -- @realizes \gamma_{\text{full},k}(difference of higher-bin probabilities)
/-- Under [the model](hyp:M), for [level data](hyp:L), [a baseline bin](hyp:k),
[a starting policy index](hyp:j), and [covariates](hyp:x), [the policy union
probability](goal) sums conditional instrument probabilities over policy classes at
or above that index within the bin. -/
noncomputable def gamma (L : LevelData Z X) (k j : ℕ) (x : X) :=
  ∑ z ∈ policyUnion L k j, instProb M z x
  -- @realizes \gamma_{j,k}(conditional union probability)
/-- For [level data](hyp:L), [a baseline bin](hyp:k), [a policy index](hyp:j), and
[covariates](hyp:x), [the relative policy threshold](goal) is the policy level's
distance above the lower baseline endpoint divided by the baseline-bin width. -/
noncomputable def kappa (L : LevelData Z X) (k j : ℕ) (x : X) :=
  (L.qLev k j x - L.pLev k x) / (L.pLev (k+1) x - L.pLev k x)
  -- @realizes \kappa_{j,k}(relative policy threshold)
/-- Under [the model](hyp:M), for [level data](hyp:L), [a baseline bin](hyp:k), and
[covariates](hyp:x), [the outcome gap measure](goal) is the difference between the
canonical treated-outcome submeasures at the upper and lower baseline endpoints,
scaled by the reciprocal of the bin width interpreted as a nonnegative extended real. -/
noncomputable def discreteGapLaw (L : LevelData Z X) (k : ℕ) (x : X) : Measure ℝ :=
  (ENNReal.ofReal (L.pLev (k+1) x - L.pLev k x))⁻¹ •
    (canonSubmeasure M true x (L.pLev (k+1) x) - canonSubmeasure M true x (L.pLev k x))
/-- Under [the model](hyp:M), for [level data](hyp:L), [a baseline bin](hyp:k), and
[covariates](hyp:x), [the full-interval outcome contribution](goal) is the bin width
times the integral of the outcome under its gap measure. -/
noncomputable def Jfull (L : LevelData Z X) (k : ℕ) (x : X) :=
  (L.pLev (k+1) x - L.pLev k x) * ∫ y, y ∂discreteGapLaw M L k x
  -- @realizes J_{\text{full},k}(full-interval contribution, k < K)
/-- Under [the model](hyp:M), for [level data](hyp:L), [a baseline bin](hyp:k),
[covariates](hyp:x), and [a rank](hyp:t), [the extended lower outcome quantile](goal)
equals the known outcome minimum at rank zero, the known maximum at rank one, and
the gap measure's lower quantile at every other rank. -/
noncomputable def levelGapQuantile (L : LevelData Z X) (k : ℕ) (x : X) (t : ℝ) :=
  if t = 0 then M.yMin else if t = 1 then M.yMax else
    Causalean.Stat.quantile (discreteGapLaw M L k x) t
  -- @realizes Q_{Y,k\mid x}(lower inverse on (0,1), with the prescribed endpoint extension)

/-- Under [the model](hyp:M), with [the upper-bound choice](hyp:upper), [level
data](hyp:L), [a baseline bin](hyp:k), [a policy-band index](hyp:j), and
[covariates](hyp:x), [the band contribution](goal) is the baseline-bin width times
the integral of the extended gap quantile between consecutive relative policy
thresholds, using reflected ranks for the upper bound and direct ranks otherwise. -/
noncomputable def Jband (upper : Bool) (L : LevelData Z X) (k j : ℕ) (x : X) :=
  (L.pLev (k+1) x - L.pLev k x) * ∫ t in Ioc (kappa L k j x) (kappa L k (j+1) x),
    levelGapQuantile M L k x (if upper then 1-t else t)
  -- @realizes J_{j,k}(partial quantile integral, k < K)
/-- Under [the model](hyp:M), with [the upper-bound choice](hyp:upper), [level
data](hyp:L), [policy propensities](hyp:q), and [covariates](hyp:x), [the final-bin
tail contribution](goal) is the known outcome maximum for the upper bound, or
minimum otherwise, times the probability-weighted policy increase above the final
baseline level over the final bin's policy classes starting at index one. -/
noncomputable def tailContribution (upper : Bool) (L : LevelData Z X) (q : Z → X → ℝ) (x : X) :=
  (if upper then M.yMax else M.yMin) *
    ∑ z ∈ policyUnion L L.K 1, instProb M z x * (q z x - L.pLev L.K x)
  -- @realizes \Delta_K(final-bin tail contribution)
-- @node: def:discrete-nuisance-components
/-- Under [the model](hyp:M), for [level data](hyp:L), [policy propensities](hyp:q),
and [covariates](hyp:x), [the discrete nuisance-component collection](goal) consists
of the full-bin probability contrasts, policy union probabilities, relative policy
thresholds, full-interval contributions, lower-bound band contributions, and the
lower-bound tail contribution evaluated at these covariates. -/
noncomputable def discreteComponents (L : LevelData Z X) (q : Z → X → ℝ) (x : X) :=
  (gammaFull M L, gamma M L, kappa L, Jfull M L, Jband M false L, tailContribution M false L q x)
/-- Under [the model](hyp:M), for [level data](hyp:L), [a baseline bin](hyp:k),
[a policy class index](hyp:j), [an instrument value](hyp:z), and [covariates](hyp:x),
[the within-class assignment share](goal) is the instrument's conditional probability
divided by the policy class's conditional probability when the instrument belongs
to that class, and zero otherwise. -/
noncomputable def levelShares (L : LevelData Z X) (k j : ℕ) (z : Z) (x : X) :=
  if z ∈ L.T k j then instProb M z x / (levelSetProb M L).2 k j x else 0
  -- @realizes a_{j,k}(normalized within-set assignment shares)
/-- Under [the model](hyp:M), for [level data](hyp:L) and [covariates](hyp:x),
[the tail policy probability](goal) is the conditional probability of the union of
policy classes starting at index one in the final baseline bin. -/
noncomputable def gammaTail (L : LevelData Z X) (x : X) := gamma M L L.K 1 x
  -- @realizes \gamma_K(final-bin policy probability)
/-- Under [the model](hyp:M), for [level data](hyp:L) and [a proposed overlap
constant](hyp:cpi), [baseline overlap with this constant](goal) requires [the
constant to be positive](step:1) and [every baseline class indexed from one through
the baseline count to have conditional probability at least that constant at every
covariate value](step:2). -/
def BaselineOverlapWitness (L : LevelData Z X) (cpi : ℝ) : Prop :=
  0 < cpi ∧ ∀ x k, 1 ≤ k → k ≤ L.K → cpi ≤ (levelSetProb M L).1 k x -- @realizes c_\pi(common positive overlap constant)

-- @node: ass:overlap-policy
/-- Under [the model](hyp:M), for [level data](hyp:L) and [an overlap constant](hyp:cpi),
[policy overlap](goal) requires [the constant to be positive](step:1) and [every
nonempty interior policy class, in every bin through the final bin, to have
conditional probability at least that constant at every covariate value](step:2). -/
def PolicyOverlap (L : LevelData Z X) (cpi : ℝ) : Prop :=
  0 < cpi ∧ -- @realizes c_\pi(same positive overlap witness as BaselineOverlapWitness)
  ∀ x k j, k ≤ L.K → 1 ≤ j → j ≤ L.l k →
    (L.T k j).Nonempty → cpi ≤ (levelSetProb M L).2 k j x
-- @node: ass:pin-19
/-- Under [the model](hyp:M), for [level data](hyp:L) and [a shared overlap
constant](hyp:cpi), [the same-constant policy-overlap requirement](goal) asserts
that this constant is positive and bounds below the conditional probability of
every nonempty interior policy class at every covariate value. -/
def PolicyOverlapSameConstantReading (L : LevelData Z X) (cpi : ℝ) : Prop := PolicyOverlap M L cpi
/-- Under [the model](hyp:M), for [level data](hyp:L) and [a proposed outcome
margin](hyp:ch), [the discrete outcome-gap requirement](goal) asserts [positivity
of the margin](step:1) and [that, in every bin before the final bin containing at
least one policy level, the absolute difference between the upper baseline level
minus the full-interval contribution and each policy level indexed from zero through
the bin's policy count is at least that margin almost surely in covariates](step:2). -/
def DiscreteOutcomeGapWitness (L : LevelData Z X) (ch : ℝ) : Prop :=
  0 < ch ∧ ∀ k < L.K, 1 ≤ L.l k → ∀ j ≤ L.l k,
    ∀ᵐ x ∂xLaw M, ch ≤ |L.pLev (k+1) x - Jfull M L k x - L.qLev k j x|
  -- @realizes c_h(uniform positive outcome margin)
-- @node: def:j-specialization-boundaries
/-- Under [the model](hyp:M), for [level data](hyp:L), [a baseline bin](hyp:k),
[a policy index](hyp:j), and [covariates](hyp:x), [the band boundary](goal) is the
known outcome minimum when the index or relative policy threshold is zero, and
otherwise the gap measure's lower quantile at that threshold. -/
noncomputable def bandBoundary (L : LevelData Z X) (k j : ℕ) (x : X) :=
  if j = 0 ∨ kappa L k j x = 0 then M.yMin else Causalean.Stat.quantile (discreteGapLaw M L k x) (kappa L k j x)
  -- @realizes \nu_{j,k}(lower quantile at kappa; fixed yMin at j=0)
-- @node: ass:j-specialization-continuity
/-- Under [the model](hyp:M), for [level data](hyp:L), [a baseline bin](hyp:k), and
[a policy-band index](hyp:j), [continuity at the band boundaries](goal) means that
for almost every covariate value the gap measure assigns zero mass both to the
boundary at this index and to the boundary at the next index. -/
def GapLawContinuousAtBoundaries (L : LevelData Z X) (k j : ℕ) : Prop :=
  ∀ᵐ x ∂xLaw M, discreteGapLaw M L k x {bandBoundary M L k j x} = 0 ∧
    discreteGapLaw M L k x {bandBoundary M L k (j+1) x} = 0
-- @node: ass:j-specialization-binary
/-- Under [the model](hyp:M), [binary outcomes](goal) means that the observed
outcome equals either zero or one almost surely under the population law. -/
def OutcomeBinary : Prop := ∀ᵐ a ∂M.law.toMeasure, M.Y a = 0 ∨ M.Y a = 1
-- @node: ass:pin-21
/-- Under [the model](hyp:M), for [level data](hyp:L), [a baseline bin](hyp:k), and
[a policy-band index](hyp:j), [the no-atom boundary-continuity requirement](goal)
asserts that the gap measure has no atom at either consecutive band boundary for
almost every covariate value. -/
def BoundaryContinuityNoAtomReading (L : LevelData Z X) (k j : ℕ) : Prop := GapLawContinuousAtBoundaries M L k j
-- @node: ass:pin-33
/-- Under [the model](hyp:M), given [level data](hyp:L), [candidate full-interval
contributions indexed by bins before the final bin](hyp:full), and [candidate band
contributions indexed within those bins from zero through the policy count](hyp:band),
[the component-index requirement](goal) asserts [almost-sure agreement of each
full-interval candidate with its full-bin contribution](step:1) and [almost-sure
agreement of each band candidate with its lower-bound band contribution](step:2). -/
def ComponentIndexRangeReading (L : LevelData Z X)
    (full : Fin L.K → X → ℝ) (band : (k : Fin L.K) → Fin (L.l k+1) → X → ℝ) : Prop :=
  (∀ k, ∀ᵐ x ∂xLaw M, full k x = Jfull M L k x) ∧
  (∀ k j, ∀ᵐ x ∂xLaw M, band k j x = Jband M false L k j x)
-- @node: ass:pin-64
/-- Under [the model](hyp:M), for [level data](hyp:L) and [a candidate family of
outcome quantiles](hyp:Q), [the bounded-domain lower-inverse requirement](goal)
asserts that in every bin before the final bin, almost surely in covariates, the
candidate at each rank in $[0,1)$ equals the infimum of outcomes in the known
outcome domain whose cumulative gap mass within that domain is at least the rank.

This convention includes rank zero in the known compact outcome domain. -/
def BandBoundaryBoundedLowerInverse (L : LevelData Z X)
    (Q : ℕ → X → ℝ → ℝ) : Prop :=
  ∀ k < L.K, ∀ᵐ x ∂xLaw M, ∀ t ∈ Ico (0 : ℝ) 1,
    Q k x t = sInf {y : ℝ | y ∈ M.Yset ∧
      t ≤ (discreteGapLaw M L k x (M.Yset ∩ Iic y)).toReal} -- @realizes Q_{Y,k\mid x}(bounded-domain lower inverse on [0,1))
-- @node: ass:pin-34
/-- Under [the model](hyp:M), for [level data](hyp:L) and [a candidate quantile
family](hyp:Q), [the interior lower-quantile requirement](goal) asserts that in
every bin before the final bin, almost surely in covariates, the candidate equals
the gap measure's lower quantile at every rank strictly between zero and one. -/
def LevelGapQuantileLowerInverse (L : LevelData Z X) (Q : ℕ → X → ℝ → ℝ) : Prop :=
  ∀ k < L.K, ∀ᵐ x ∂xLaw M, ∀ t ∈ Ioo (0 : ℝ) 1, Q k x t = Causalean.Stat.quantile (discreteGapLaw M L k x) t
-- @node: ass:pin-35
/-- Under [the model](hyp:M), for [level data](hyp:L) and [a candidate boundary
family](hyp:nu), [the band-boundary convention](goal) requires, in every bin before
the final bin and almost surely in covariates, the index-zero boundary to equal
the known outcome minimum and every interior policy boundary to equal that minimum
at a zero relative threshold or the gap measure's lower quantile at its threshold
otherwise. -/
def BandBoundaryReading (L : LevelData Z X) (nu : ℕ → ℕ → X → ℝ) : Prop :=
  ∀ k < L.K, ∀ᵐ x ∂xLaw M, nu k 0 x = M.yMin ∧ ∀ j, 1 ≤ j → j ≤ L.l k →
    nu k j x = if kappa L k j x = 0 then M.yMin else
      Causalean.Stat.quantile (discreteGapLaw M L k x) (kappa L k j x)
/-- Under [the model](hyp:M), with [the upper-bound choice](hyp:upper), [level
data](hyp:L), and [policy propensities](hyp:q), [the discrete population target](goal)
averages over covariates the sum of full-bin contrasts times full-interval
contributions, policy union probabilities times the preceding band contributions,
and the final-bin tail contribution, using the chosen bound for bands and the tail. -/
noncomputable def discreteTarget (upper : Bool) (L : LevelData Z X) (q : Z → X → ℝ) :=
  ∫ x, ((∑ k ∈ Finset.range L.K, (gammaFull M L k x * Jfull M L k x +
    ∑ j ∈ Finset.Icc 1 (L.l k), gamma M L k j x * Jband M upper L k (j-1) x)) +
    tailContribution M upper L q x) ∂xLaw M
/-- Under [the model](hyp:M), for [level data](hyp:L), [policy propensities](hyp:q),
[a baseline bin](hyp:k), [a policy class index](hyp:j), and [covariates](hyp:x),
[the pooled policy level](goal) is the sum of instrument-specific policy
propensities in that class weighted by their within-class assignment shares. -/
noncomputable def pooledPolicyLevel (L : LevelData Z X) (q : Z → X → ℝ) -- @realizes q_{j,k}(pooled policy-level construction from within-set shares)
    (k j : ℕ) (x : X) := ∑ z ∈ L.T k j, levelShares M L k j z x * q z x

-- @node: def:score-level-shares
/-- Under [the model](hyp:M), for [level data](hyp:L) and [policy propensities](hyp:q),
[the level-share family](goal) collects the final-bin policy probability, the
within-policy-class assignment shares, and the policy levels pooled using those shares. -/
noncomputable def levelShareFamily (L : LevelData Z X) (q : Z → X → ℝ) :=
  (gammaTail M L, levelShares M L, pooledPolicyLevel M L q)
-- @node: policyLevelsAt_mem_bounds
/-- If [a value belongs to the ordered list of policy levels in a baseline bin at
given covariates](hyp:hr), then [it lies between that bin's lower and upper baseline
endpoints, including both endpoints](goal). -/
lemma policyLevelsAt_mem_bounds (prop q : Z → X → ℝ) (x : X) (k : ℕ)
    {r : ℝ} (hr : r ∈ policyLevelsAt prop q x k) :
    pLevel (finiteLevels (fun z => prop z x)) k ≤ r ∧
      r ≤ pLevel (finiteLevels (fun z => prop z x)) (k+1) := by
  simp only [policyLevelsAt, Finset.mem_sort, Finset.mem_filter] at hr
  refine ⟨hr.2.1, ?_⟩
  split_ifs at hr with hk
  · exact hr.2.2.le
  · exact hr.2.2

-- @node: canonical_level_ranges
/-- If [all baseline propensities lie between zero and one](hyp:hp), [all policy
propensities lie between zero and one](hyp:hq), and [the level data match the
canonical propensity levels and classes with covariate-invariant counts and strict
ordering](hyp:hL), then [at every covariate value, baseline levels through one index
beyond the baseline count and policy levels through each bin's upper endpoint lie
between zero and one, as do the relative policy thresholds in every bin before the
final bin](goal). -/
lemma canonical_level_ranges (prop q : Z → X → ℝ) (L : LevelData Z X) -- @realizes p_k(canonical baseline levels in [0,1]) @realizes q_{j,k}(policy-bin levels in [0,1])
    (hp : ∀ z x, prop z x ∈ Icc (0 : ℝ) 1)
    (hq : ∀ z x, q z x ∈ Icc (0 : ℝ) 1)
    (hL : LevelOrderInvariant prop q L) :
    (∀ x k, k ≤ L.K + 1 → L.pLev k x ∈ Icc (0 : ℝ) 1) ∧
    (∀ x k j, k ≤ L.K → j ≤ L.l k + 1 → L.qLev k j x ∈ Icc (0 : ℝ) 1) ∧
    (∀ x k j, k < L.K → j ≤ L.l k + 1 → kappa L k j x ∈ Icc (0 : ℝ) 1) := by
  rcases hL with ⟨hbase, hpolicy, hboundary, hcount, hlength, hS, hT,
    hstrict, hqstrict, hinputs, hpRange, hqRange⟩
  refine ⟨hpRange, hqRange, ?_⟩
  intro x k j hk hj
  have hk1 : k + 1 ≤ L.K := by omega
  have hwidth : 0 < L.pLev (k+1) x - L.pLev k x :=
    sub_pos.mpr (hstrict x k (k+1) (Nat.lt_succ_self k) hk1)
  have hbin : L.pLev k x ≤ L.qLev k j x ∧ L.qLev k j x ≤ L.pLev (k+1) x := by
    rw [hpolicy x k j hk.le hj]
    by_cases hz : j = 0
    · simp only [if_pos hz]
      exact ⟨le_rfl, (hstrict x k (k+1) (Nat.lt_succ_self k) hk1).le⟩
    simp only [if_neg hz]
    by_cases hji : j ≤ L.l k
    · rw [if_pos hji]
      have hidx : j - 1 < (policyLevelsAt prop q x k).length := by
        rw [hlength x k hk.le]
        omega
      have hm : (policyLevelsAt prop q x k).getD (j-1) 0 ∈
          policyLevelsAt prop q x k := by
        rw [List.getD_eq_getElem _ _ hidx]
        exact List.getElem_mem hidx
      have hb := policyLevelsAt_mem_bounds prop q x k hm
      rw [← hbase x k (by omega), ← hbase x (k+1) (by omega)] at hb
      exact hb
    · rw [if_neg hji]
      exact ⟨(hstrict x k (k+1) (Nat.lt_succ_self k) hk1).le, le_rfl⟩
  change 0 ≤ (L.qLev k j x - L.pLev k x) / (L.pLev (k+1) x - L.pLev k x) ∧
    (L.qLev k j x - L.pLev k x) / (L.pLev (k+1) x - L.pLev k x) ≤ 1
  constructor
  · exact div_nonneg (sub_nonneg.mpr hbin.1) hwidth.le
  · apply (div_le_one hwidth).mpr
    exact sub_le_sub_right hbin.2 _
  -- @realizes \kappa_{j,k}(relative thresholds in [0,1])

-- @node: ass:prop-gap-separation
/-- For [baseline propensities](hyp:prop) and [policy propensities](hyp:q),
[uniform propensity-gap separation](goal) means that there exists a common constant
such that [the constant is positive](step:1) and [any two values attained by either
propensity at the same covariates are equal or differ in absolute value by more
than that constant](step:2). -/
def PropensityGapSeparation (prop q : Z → X → ℝ) : Prop :=
  ∃ cgap : ℝ, 0 < cgap ∧ ∀ x, -- @realizes c_{\text{gap}}(one existential positive constant outside all covariates and levels)
    ∀ v ∈ combinedPropensityRange prop q x,
    ∀ v' ∈ combinedPropensityRange prop q x,
      v' = v ∨ cgap < |v-v'|

-- @node: ass:overlap-baseline
/-- Under [the latent instrumental-variable model](hyp:M), for [level data](hyp:L),
[baseline overlap](goal) means that there exists a common constant such that [the
constant is positive](step:1) and [every baseline class indexed from one through
the baseline count has conditional instrument probability at least that constant
at every covariate value](step:2). -/
def BaselineOverlap (L : LevelData Z X) : Prop :=
  ∃ cpi : ℝ, 0 < cpi ∧ ∀ x k, 1 ≤ k → k ≤ L.K → cpi ≤ (levelSetProb M L).1 k x -- @realizes c_\pi(one existential positive uniform baseline-overlap constant)

-- @node: ass:discrete-outcome-gap
/-- Under [the latent instrumental-variable model](hyp:M), for [level data](hyp:L),
[the discrete outcome-gap requirement](goal) means that there exists a common
margin such that [the margin is positive](step:1) and [in every bin before the
final bin with at least one policy level, the absolute difference between the
upper baseline level minus the full-interval outcome contribution and each policy
level indexed from zero through the bin's policy count is at least that margin
almost surely in covariates](step:2). -/
def DiscreteOutcomeGap (L : LevelData Z X) : Prop :=
  ∃ ch : ℝ, 0 < ch ∧ ∀ k < L.K, 1 ≤ L.l k → ∀ j ≤ L.l k,
    ∀ᵐ x ∂xLaw M, ch ≤ |L.pLev (k+1) x - Jfull M L k x - L.qLev k j x|
  -- @realizes c_h(one existential positive outcome margin outside all indices and covariates)

end Papers.TbsPrteOptimalTransport
