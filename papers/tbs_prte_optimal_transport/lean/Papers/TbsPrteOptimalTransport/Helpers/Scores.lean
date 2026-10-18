module
public import Papers.TbsPrteOptimalTransport.Helpers.DiscreteIV
/-! Continuous-outcome score components with structural boundary conventions. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set
open scoped Classical
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)
/-- For [a covariate space](hyp:X) and [an instrument space](hyp:Z), an
[observation](goal) records covariates, the instrument, a real-valued treatment,
and a real-valued outcome, in that order. -/
abbrev Obs (X Z : Type v) := X × Z × ℝ × ℝ
  -- @realizes O(observation in order X,Z,W,Y)
/-- The [indicator](goal) of [an event](hyp:P) is one when the event holds and zero otherwise. -/
noncomputable def indicator (P : Prop) : ℝ := if P then 1 else 0
  -- @realizes \indicator(event indicator)
/-- For [a maximum level](hyp:K), the [positive level indices](goal) are the integers from one through that maximum. -/
abbrev PositiveIndex (K : ℕ) := {k : ℕ // 1 ≤ k ∧ k ≤ K}
/-- Given [a level specification](hyp:L), the [regular indices](goal) pair a level from zero through the maximum with a band number from one through that level's band count. -/
abbrev RegularIndex (L : LevelData Z X) := {a : ℕ × ℕ // a.1 ≤ L.K ∧ 1 ≤ a.2 ∧ a.2 ≤ L.l a.1}
/-- Given [a level specification](hyp:L), the [interior boundary indices](goal) pair a level strictly below the maximum with a boundary number from one through that level's band count. -/
abbrev BoundaryIndex (L : LevelData Z X) := {a : ℕ × ℕ // a.1 < L.K ∧ 1 ≤ a.2 ∧ a.2 ≤ L.l a.1}
/-- Given [a level specification](hyp:L), the [band-mean indices](goal) pair a level strictly below the maximum with a band number from zero through that level's band count. -/
abbrev MeanIndex (L : LevelData Z X) := {a : ℕ × ℕ // a.1 < L.K ∧ a.2 ≤ L.l a.1}
/-- Given [a level specification](hyp:L), the [minus-side interior boundary indices](goal) pair a positive level strictly below the maximum with a boundary number from one through that level's band count. -/
abbrev MinusBoundaryIndex (L : LevelData Z X) := {a : ℕ × ℕ // 1 ≤ a.1 ∧ a.1 < L.K ∧ 1 ≤ a.2 ∧ a.2 ≤ L.l a.1}
/-- Given [a level specification](hyp:L), the [minus-side band-mean indices](goal) pair a positive level strictly below the maximum with a band number from zero through that level's band count. -/
abbrev MinusMeanIndex (L : LevelData Z X) := {a : ℕ × ℕ // 1 ≤ a.1 ∧ a.1 < L.K ∧ a.2 ≤ L.l a.1}
/-- Given [a level specification](hyp:L), the [cumulative-indicator indices](goal) pair a level strictly below the maximum with a boundary number from zero through that level's band count. -/
abbrev IndicatorIndex (L : LevelData Z X) := {a : ℕ × ℕ // a.1 < L.K ∧ a.2 ≤ L.l a.1}
/-- Given [a level specification](hyp:L), the [minus-side cumulative-indicator indices](goal) pair a positive level strictly below the maximum with a boundary number from zero through that level's band count. -/
abbrev MinusIndicatorIndex (L : LevelData Z X) := {a : ℕ × ℕ // 1 ≤ a.1 ∧ a.1 < L.K ∧ a.2 ≤ L.l a.1}
/-- For [a level specification](hyp:L), the [continuous-outcome nuisance vector](goal)
collects propensity functions, level and regular-set probabilities, instrument shares,
higher-set probability fits, policy weights, outcome boundaries, cumulative-indicator
means, and band and full-interval outcome means for both sides of each level. -/
structure NuisanceCont (L : LevelData Z X) where
  prop : Z → X → ℝ -- @realizes p(nuisance function carrier; range via admissibility)
  pLev : PositiveIndex L.K → X → ℝ -- @realizes p_k(nuisance function carrier; range via admissibility)
  piLev : PositiveIndex L.K → X → ℝ -- @realizes \pi_k(nuisance function carrier; range via admissibility)
  tauLev : RegularIndex L → X → ℝ -- @realizes \tau_{j,k}(nuisance function carrier; range via admissibility)
  share : RegularIndex L → Z → X → ℝ -- @realizes a_{j,k}(nuisance function carrier; range via admissibility)
  higherPolicyFit : Fin L.K → X → ℝ
  higherBaselineFit : Fin L.K → X → ℝ
  gammaFull : Fin L.K → X → ℝ -- @realizes \gamma_{\text{full},k}(nuisance function carrier; range via admissibility)
  gamma : RegularIndex L → X → ℝ -- @realizes \gamma_{j,k}(nuisance function carrier; range via admissibility)
  gammaTail : X → ℝ -- @realizes \gamma_K(nuisance function carrier; range via admissibility)
  nu : BoundaryIndex L → X → ℝ -- @realizes \nu_{j,k}(nuisance function carrier; range via admissibility)
  Mplus : IndicatorIndex L → X → ℝ -- @realizes M_{j,k}^{+}(nuisance function carrier; range via admissibility)
  Mminus : MinusIndicatorIndex L → X → ℝ -- @realizes M_{j,k}^{-}(nuisance function carrier; range via admissibility)
  Jplus : MeanIndex L → X → ℝ -- @realizes J_{j,k}^{+}(nuisance function carrier; range via admissibility)
  Jminus : MinusMeanIndex L → X → ℝ -- @realizes J_{j,k}^{-}(nuisance function carrier; range via admissibility)
  JfullPlus : Fin L.K → X → ℝ -- @realizes J_{\text{full},k}^{+}(nuisance function carrier; range via admissibility)
  JfullMinus : {k : ℕ // 1 ≤ k ∧ k < L.K} → X → ℝ -- @realizes J_{\text{full},k}^{-}(nuisance function carrier; range via admissibility)

/-- For [a level specification](hyp:L), [addition of continuous-outcome nuisance vectors](goal)
adds every component function pointwise. -/
instance (L : LevelData Z X) : Add (NuisanceCont L) := ⟨fun a b => {
  prop := a.prop + b.prop
  pLev := a.pLev + b.pLev
  piLev := a.piLev + b.piLev
  tauLev := a.tauLev + b.tauLev
  share := a.share + b.share
  higherPolicyFit := a.higherPolicyFit + b.higherPolicyFit
  higherBaselineFit := a.higherBaselineFit + b.higherBaselineFit
  gammaFull := a.gammaFull + b.gammaFull
  gamma := a.gamma + b.gamma
  gammaTail := a.gammaTail + b.gammaTail
  nu := a.nu + b.nu
  Mplus := a.Mplus + b.Mplus
  Mminus := a.Mminus + b.Mminus
  Jplus := a.Jplus + b.Jplus
  Jminus := a.Jminus + b.Jminus
  JfullPlus := a.JfullPlus + b.JfullPlus
  JfullMinus := a.JfullMinus + b.JfullMinus }⟩
/-- For [a level specification](hyp:L), [real scalar multiplication of continuous-outcome nuisance vectors](goal)
multiplies every component function pointwise by the scalar. -/
instance (L : LevelData Z X) : SMul ℝ (NuisanceCont L) := ⟨fun t a => {
  prop := t • a.prop
  pLev := t • a.pLev
  piLev := t • a.piLev
  tauLev := t • a.tauLev
  share := t • a.share
  higherPolicyFit := t • a.higherPolicyFit
  higherBaselineFit := t • a.higherBaselineFit
  gammaFull := t • a.gammaFull
  gamma := t • a.gamma
  gammaTail := t • a.gammaTail
  nu := t • a.nu
  Mplus := t • a.Mplus
  Mminus := t • a.Mminus
  Jplus := t • a.Jplus
  Jminus := t • a.Jminus
  JfullPlus := t • a.JfullPlus
  JfullMinus := t • a.JfullMinus }⟩

/-- The [extended positive-level value](goal) evaluates [a function on positive levels](hyp:f)
at [a level index](hyp:k) and [covariates](hyp:x) when the index lies between one and
the maximum, and returns zero otherwise. -/
noncomputable def positiveValue {K : ℕ} (f : PositiveIndex K → X → ℝ) (k : ℕ) (x : X) : ℝ :=
  if h : 1 ≤ k ∧ k ≤ K then f ⟨k,h⟩ x else 0
/-- The [extended regular value](goal) evaluates [a function on regular indices](hyp:f)
at [a level](hyp:k), [a band number](hyp:j), and [covariates](hyp:x) when the level
does not exceed the maximum and the band number is between one and its count;
it returns zero otherwise. -/
noncomputable def regularValue {L : LevelData Z X} (f : RegularIndex L → X → ℝ)
    (k j : ℕ) (x : X) : ℝ :=
  if h : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k then f ⟨(k,j),h⟩ x else 0
/-- Using [a nuisance vector](hyp:e), the [extended instrument share](goal) at
[a level](hyp:k), [a band number](hyp:j), [an instrument value](hyp:z), and
[covariates](hyp:x) is the stored share when the level does not exceed the maximum
and the band number is between one and its count, and zero otherwise. -/
noncomputable def shareValue {L : LevelData Z X} (e : NuisanceCont L) (k j : ℕ) (z : Z) (x : X) :=
  if h : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k then e.share ⟨(k,j),h⟩ z x else 0
/-- Under [a model with outcome bounds](hyp:M), the [extended outcome boundary](goal)
from [a nuisance vector](hyp:e) at [a level](hyp:k), [a boundary number](hyp:j), and
[covariates](hyp:x) equals the lower outcome bound at boundary zero, the stored
boundary at a valid positive interior boundary, and the upper outcome bound otherwise. -/
noncomputable def nuValue {L : LevelData Z X} (e : NuisanceCont L) (k j : ℕ) (x : X) :=
  if j = 0 then M.yMin else if h : k < L.K ∧ 1 ≤ j ∧ j ≤ L.l k then e.nu ⟨(k,j),h⟩ x else M.yMax
/-- The [extended band mean](goal) evaluates [a band-mean function](hyp:f) at
[a level](hyp:k), [a band number](hyp:j), and [covariates](hyp:x) when the level is
below the maximum and the band number is from zero through its count, and is zero otherwise. -/
noncomputable def meanValue {L : LevelData Z X} (f : MeanIndex L → X → ℝ) (k j : ℕ) (x : X) :=
  if h : k < L.K ∧ j ≤ L.l k then f ⟨(k,j),h⟩ x else 0
/-- The [extended minus-side band mean](goal) evaluates [a minus-side mean function](hyp:f)
at [a level](hyp:k), [a band number](hyp:j), and [covariates](hyp:x) when the level
is positive and below the maximum and the band number is from zero through its
count, and is zero otherwise. -/
noncomputable def minusMeanValue {L : LevelData Z X} (f : MinusMeanIndex L → X → ℝ) (k j : ℕ) (x : X) :=
  if h : 1 ≤ k ∧ k < L.K ∧ j ≤ L.l k then f ⟨(k,j),h⟩ x else 0
/-- The [extended cumulative-indicator mean](goal) evaluates [a boundary-indicator mean function](hyp:f)
at [a level](hyp:k), [a boundary number](hyp:j), and [covariates](hyp:x) for a level
below the maximum and a boundary from zero through its count; it equals one at
the next boundary of such a level and zero otherwise. -/
noncomputable def boundaryValue {L : LevelData Z X} (f : IndicatorIndex L → X → ℝ) (k j : ℕ) (x : X) :=
  if h : k < L.K ∧ j ≤ L.l k then f ⟨(k,j),h⟩ x
  else if k < L.K ∧ j = L.l k + 1 then 1 else 0
/-- The [extended minus-side cumulative-indicator mean](goal) evaluates
[a minus-side boundary-indicator mean function](hyp:f) at [a level](hyp:k),
[a boundary number](hyp:j), and [covariates](hyp:x) for a positive level below the
maximum and a boundary from zero through its count; it equals one at the next
boundary of such a level and zero otherwise. -/
noncomputable def minusBoundaryValue {L : LevelData Z X} (f : MinusIndicatorIndex L → X → ℝ) (k j : ℕ) (x : X) :=
  if h : 1 ≤ k ∧ k < L.K ∧ j ≤ L.l k then f ⟨(k,j),h⟩ x
  else if 1 ≤ k ∧ k < L.K ∧ j = L.l k + 1 then 1 else 0
/-- The [extended full-interval value](goal) evaluates [a function on levels below the maximum](hyp:f)
at [a level](hyp:k) and [covariates](hyp:x) when the level is below the maximum,
and returns zero otherwise. -/
noncomputable def fullValue {L : LevelData Z X} (f : Fin L.K → X → ℝ) (k : ℕ) (x : X) :=
  if h : k < L.K then f ⟨k,h⟩ x else 0
/-- From [a nuisance vector](hyp:e), the [extended minus-side full-interval mean](goal)
at [a level](hyp:k) and [covariates](hyp:x) is the stored full-interval mean for a
positive level below the maximum, and zero otherwise. -/
noncomputable def minusFullValue {L : LevelData Z X} (e : NuisanceCont L) (k : ℕ) (x : X) :=
  if h : 1 ≤ k ∧ k < L.K then e.JfullMinus ⟨k,h⟩ x else 0
/-- Given [a policy propensity transformation](hyp:phi), [level data](hyp:L), and
[a nuisance vector](hyp:e), the [pooled policy propensity](goal) at [a baseline bin](hyp:k),
[a policy index](hyp:j), and [covariates](hyp:x) equals the lower baseline propensity
at index zero, the upper baseline propensity beyond the policy count, and otherwise
the share-weighted sum of transformed instrument-specific propensities in the policy class. -/
noncomputable def pooledQ (phi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e : NuisanceCont L)
    (k j : ℕ) (x : X) :=
  if j = 0 then positiveValue e.pLev k x else if L.l k < j then positiveValue e.pLev (k+1) x else
    ∑ z ∈ L.T k j, shareValue e k j z x * phi z x (e.prop z x)

/-- Under [the model](hyp:M), for [level data](hyp:L), [a baseline level](hyp:k), and
[covariates](hyp:x), the [treated outcome law in the baseline class](goal) is formed
by [conditioning the joint outcome, treatment, and instrument distribution on the covariates](step:1),
[restricting it to treatment equal to one and instruments in that baseline class](step:2),
and [normalizing the restricted measure and retaining only the outcome](step:3). -/
noncomputable def treatedLaw (L : LevelData Z X) (k : ℕ) (x : X) : Measure ℝ :=
  let joint := condDistrib (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure x
  let selected := joint.restrict {a | a.2.1 = 1 ∧ a.2.2 ∈ (L.S k : Set Z)}
  (selected univ)⁻¹ • selected.map Prod.fst
-- @node: def:boundary-indicator-means
/-- Under [the model](hyp:M), given [level data](hyp:L), [a choice of the plus or minus side](hyp:plus),
[a baseline bin](hyp:k), [a boundary index](hyp:j), and [covariates](hyp:x), the
[boundary-indicator mean](goal) is the treated probability of an outcome at or below
the bin's outcome boundary, using the next baseline class on the plus side and the
current class on the minus side; the minus-side value at bin zero is zero. -/
noncomputable def boundaryIndicatorMean (L : LevelData Z X) (plus : Bool) (k j : ℕ) (x : X) :=
  if !plus && k == 0 then 0 else
    (treatedLaw M L (if plus then k+1 else k) x (Iic (bandBoundary M L k j x))).toReal
/-- Under [the model](hyp:M), for [level data](hyp:L), [a choice of the plus or minus side](hyp:plus),
[a choice between the full outcome range and a single band](hyp:full), [a baseline bin](hyp:k),
[a band index](hyp:j), and [covariates](hyp:x), the [treated outcome moment](goal)
integrates the outcome over the chosen range under the treated law in the next
baseline class on the plus side or the current class on the minus side. The band
excludes its lower boundary and includes its upper boundary, and the minus-side
value at bin zero is zero. -/
noncomputable def treatedBandMean (L : LevelData Z X) (plus full : Bool) (k j : ℕ) (x : X) :=
  if !plus && k == 0 then 0 else
    if full then ∫ y, y ∂treatedLaw M L (if plus then k+1 else k) x else
      ∫ y in Ioc (bandBoundary M L k j x) (bandBoundary M L k (j+1) x),
        y ∂treatedLaw M L (if plus then k+1 else k) x
-- @node: def:orthogonality-discrete-parameters
/-- Under [the model](hyp:M) and [level data](hyp:L), the [population nuisance vector](goal)
uses the model propensity, baseline propensity levels, conditional baseline and
policy class probabilities, within-class instrument shares, higher-policy and
higher-baseline probabilities, their full-bin contrasts, policy-union and tail
probabilities, quantile band boundaries, and the plus- and minus-side treated
cumulative probabilities and band and full-range outcome moments. -/
noncomputable def trueNuisance (L : LevelData Z X) : NuisanceCont L := {
  prop := M.prop
  pLev := fun k => L.pLev k
  piLev := fun k => (levelSetProb M L).1 k
  tauLev := fun a => (levelSetProb M L).2 a.val.1 a.val.2
  share := fun a => levelShares M L a.val.1 a.val.2
  higherPolicyFit := fun k x => ∑ z ∈ higherPolicy L k, instProb M z x
  higherBaselineFit := fun k x => ∑ z ∈ higherBaseline L k, instProb M z x
  gammaFull := fun k => gammaFull M L k
  gamma := fun a => gamma M L a.val.1 a.val.2
  gammaTail := gammaTail M L
  nu := fun a => bandBoundary M L a.val.1 a.val.2
  Mplus := fun a => boundaryIndicatorMean M L true a.val.1 a.val.2
  Mminus := fun a => boundaryIndicatorMean M L false a.val.1 a.val.2
  Jplus := fun a => treatedBandMean M L true false a.val.1 a.val.2
  Jminus := fun a => treatedBandMean M L false false a.val.1 a.val.2
  JfullPlus := fun k => treatedBandMean M L true true k 0
  JfullMinus := fun k => treatedBandMean M L false true k 0 }
  -- @realizes \eta_0(population nuisance vector)
/-- Under [the model](hyp:M), for [a policy propensity transformation](hyp:phi) and
[level data](hyp:L), the [population score target](goal) is the lower discrete
sharp-bound target evaluated at policy propensities obtained by transforming the
model's instrument-specific propensities. -/
noncomputable def trueScoreTarget (phi : Z → X → ℝ → ℝ) (L : LevelData Z X) :=
  discreteTarget M false L (policyProp phi M.prop)
  -- @realizes \theta_0(true sharp-bound target)

/-- Given [level data](hyp:L), [a nuisance vector](hyp:e), [a baseline level](hyp:k),
and [an observation](hyp:o), the [baseline propensity residual](goal) is zero at
level zero and otherwise is treatment minus the fitted baseline propensity,
multiplied by the indicator of the baseline instrument class and divided by its
fitted conditional probability. -/
noncomputable def RpCont (L : LevelData Z X) (e : NuisanceCont L) (k : ℕ) (o : Obs X Z) :=
  if k = 0 then 0 else indicator (o.2.1 ∈ L.S k) / positiveValue e.piLev k o.1 *
    (o.2.2.1 - positiveValue e.pLev k o.1)
/-- Given [the derivative of the policy propensity transformation](hyp:dphi),
[level data](hyp:L), [a nuisance vector](hyp:e), [a baseline bin](hyp:k),
[a policy index](hyp:j), and [an observation](hyp:o), the [pooled policy propensity residual](goal)
is zero at index zero or beyond the policy count; otherwise it sums the
instrument-specific treatment residuals weighted by the policy derivative and
instrument indicators over the policy class, and divides by that class's fitted probability. -/
noncomputable def RqCont (dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e : NuisanceCont L)
    (k j : ℕ) (o : Obs X Z) :=
  if j = 0 ∨ L.l k < j then 0 else
    (regularValue e.tauLev k j o.1)⁻¹ * ∑ z ∈ L.T k j,
      dphi z o.1 (e.prop z o.1) * indicator (o.2.1 = z) * (o.2.2.1 - e.prop z o.1)
  -- @realizes R_{q,j,k}(pooled regular policy-level residual)
/-- Under [the model](hyp:M), given [level data](hyp:L), [a nuisance vector](hyp:e),
[a choice of the plus or minus side](hyp:plus), [a baseline bin](hyp:k),
[a band index](hyp:j), and [an observation](hyp:o), the [treated-band outcome residual](goal)
is zero on the minus side at bin zero; otherwise it [selects the next baseline level
on the plus side or the current level on the minus side](step:1) and [weights the
outcome times its band indicator minus the fitted band moment by treatment and
membership in the selected baseline class, divided by that class's fitted probability](step:2). -/
noncomputable def IFJ (L : LevelData Z X) (e : NuisanceCont L) (plus : Bool)
    (k j : ℕ) (o : Obs X Z) :=
  if !plus && k == 0 then 0 else
    let lev := if plus then k+1 else k
    indicator (o.2.1 ∈ L.S lev) * o.2.2.1 / positiveValue e.piLev lev o.1 *
      (o.2.2.2 * indicator (nuValue M e k j o.1 < o.2.2.2 ∧ o.2.2.2 ≤ nuValue M e k (j+1) o.1) -
        if plus then meanValue e.Jplus k j o.1 else minusMeanValue e.Jminus k j o.1)
  -- @realizes IF_{J^+}(plus treated-band residual) @realizes IF_{J^-}(minus residual omitted at k=0)
/-- Under [the model](hyp:M), given [level data](hyp:L), [a nuisance vector](hyp:e),
[a choice of the plus or minus side](hyp:plus), [a baseline bin](hyp:k),
[a boundary index](hyp:j), and [an observation](hyp:o), the [boundary-indicator residual](goal)
is zero on the minus side at bin zero; otherwise it [selects the next baseline level
on the plus side or the current level on the minus side](step:1) and [weights the
indicator of an outcome at or below the boundary minus its fitted cumulative mean
by treatment and membership in the selected baseline class, divided by that class's
fitted probability](step:2). -/
noncomputable def IFM (L : LevelData Z X) (e : NuisanceCont L) (plus : Bool)
    (k j : ℕ) (o : Obs X Z) :=
  if !plus ∧ k = 0 then 0 else
    let lev := if plus then k+1 else k
    indicator (o.2.1 ∈ L.S lev) * o.2.2.1 / positiveValue e.piLev lev o.1 *
      (indicator (o.2.2.2 ≤ nuValue M e k j o.1) -
        if plus then boundaryValue e.Mplus k j o.1 else minusBoundaryValue e.Mminus k j o.1)
  -- @realizes IF_{M_{j,k}^+}(plus indicator residual) @realizes IF_{M_{j,k}^-}(minus indicator residual)
/-- Given [level data](hyp:L), [a nuisance vector](hyp:e), [a baseline bin](hyp:k),
[a band index](hyp:j), and [covariates](hyp:x), the [continuous band moment contrast](goal)
is the next-level propensity times the plus-side band moment minus the current-level
propensity times the minus-side band moment, using the extended nuisance values. -/
noncomputable def contJ (L : LevelData Z X) (e : NuisanceCont L) (k j : ℕ) (x : X) :=
  positiveValue e.pLev (k+1) x * meanValue e.Jplus k j x -
    positiveValue e.pLev k x * minusMeanValue e.Jminus k j x
/-- Given [level data](hyp:L), [a nuisance vector](hyp:e), [a baseline bin](hyp:k),
and [covariates](hyp:x), the [full-interval moment contrast](goal) is the next-level
propensity times the plus-side full-interval mean minus the current-level propensity
times the minus-side full-interval mean, using the extended nuisance values. -/
noncomputable def contFullJ (L : LevelData Z X) (e : NuisanceCont L) (k : ℕ) (x : X) :=
  positiveValue e.pLev (k+1) x * fullValue e.JfullPlus k x - positiveValue e.pLev k x * minusFullValue e k x
/-- Under [the model](hyp:M), for [level data](hyp:L), [a nuisance vector](hyp:e),
[a baseline bin](hyp:k), [a band index](hyp:j), and [covariates](hyp:x), the
[lower propensity representer](goal) is minus the minus-side band moment, minus
the lower outcome boundary times its minus-side cumulative mean, plus the upper
boundary times its minus-side cumulative mean, plus the lower boundary when the
band index is positive, and minus the upper boundary. -/
noncomputable def alphaLow (L : LevelData Z X) (e : NuisanceCont L) (k j : ℕ) (x : X) :=
  -minusMeanValue e.Jminus k j x - nuValue M e k j x * minusBoundaryValue e.Mminus k j x +
    nuValue M e k (j+1) x * minusBoundaryValue e.Mminus k (j+1) x +
    indicator (1 ≤ j) * nuValue M e k j x - nuValue M e k (j+1) x
  -- @realizes \alpha_{p_k}(lower propensity representer)
/-- Under [the model](hyp:M), for [level data](hyp:L), [a nuisance vector](hyp:e),
[a baseline bin](hyp:k), [a band index](hyp:j), and [covariates](hyp:x), the
[upper propensity representer](goal) is the plus-side band moment plus the lower
outcome boundary times its plus-side cumulative mean, minus the upper boundary
times its plus-side cumulative mean. -/
noncomputable def alphaHigh (L : LevelData Z X) (e : NuisanceCont L) (k j : ℕ) (x : X) :=
  meanValue e.Jplus k j x + nuValue M e k j x * boundaryValue e.Mplus k j x -
    nuValue M e k (j+1) x * boundaryValue e.Mplus k (j+1) x
  -- @realizes \alpha_{p_{k+1}}(upper propensity representer)
/-- Under [the model](hyp:M), given [a policy propensity transformation](hyp:phi),
[its derivative](hyp:dphi), [level data](hyp:L), [a nuisance vector](hyp:e),
[a baseline bin](hyp:k), [a band index](hyp:j), and [an observation](hyp:o), the
[continuous band score](goal) first [extracts the observed covariates](step:1)
and [forms a boundary correction as the propensity-weighted cumulative-mean
contrast minus the pooled policy propensity's excess over the lower baseline
propensity, plus the difference of boundary-indicator residuals](step:2).
It then [adds to the band moment contrast the difference of treated-band residuals,
the lower-boundary correction minus the upper-boundary correction, and the
lower and upper propensity representers times their baseline propensity residuals,
then subtracts the lower-boundary-weighted policy residual and adds the upper-boundary-weighted
policy residual, omitting the lower propensity term at bin zero](step:3). -/
noncomputable def contScoreComponents (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e : NuisanceCont L) (k j : ℕ) (o : Obs X Z) : ℝ :=
  let x := o.1
  let correction := fun b => positiveValue e.pLev (k+1) x * boundaryValue e.Mplus k b x -
    positiveValue e.pLev k x * minusBoundaryValue e.Mminus k b x -
    (pooledQ phi L e k b x - positiveValue e.pLev k x) + IFM M L e true k b o - IFM M L e false k b o
  contJ L e k j x + IFJ M L e true k j o - IFJ M L e false k j o +
    nuValue M e k j x * correction j - nuValue M e k (j+1) x * correction (j+1) +
    (if k = 0 then 0 else alphaLow M L e k j x * RpCont L e k o) +
    alphaHigh M L e k j x * RpCont L e (k+1) o -
    nuValue M e k j x * RqCont dphi L e k j o + nuValue M e k (j+1) x * RqCont dphi L e k (j+1) o
  -- @realizes \psi_{j,k}^J(continuous band score)
/-- Given [level data](hyp:L), [a nuisance vector](hyp:e), [a baseline bin](hyp:k),
and [an observation](hyp:o), the [full-interval outcome score](goal) first
[extracts the observed covariates](step:1), then [adds to the full-interval moment
contrast the plus-side treatment-weighted outcome residual divided by the next
baseline class probability and the plus-side mean times the next-level propensity
residual, subtracting the analogous minus-side terms for the current level when
the bin is positive](step:2). -/
noncomputable def psiFullJ (L : LevelData Z X) (e : NuisanceCont L) (k : ℕ) (o : Obs X Z) :=
  let x := o.1
  contFullJ L e k x + indicator (o.2.1 ∈ L.S (k+1)) * o.2.2.1 / positiveValue e.piLev (k+1) x *
    (o.2.2.2 - fullValue e.JfullPlus k x) + fullValue e.JfullPlus k x * RpCont L e (k+1) o -
    (if k = 0 then 0 else indicator (o.2.1 ∈ L.S k) * o.2.2.1 / positiveValue e.piLev k x *
      (o.2.2.2 - minusFullValue e k x) + minusFullValue e k x * RpCont L e k o)
  -- @realizes \psi_{\text{full},k}^J(full interval score)
/-- Under [the model](hyp:M), given [a policy propensity transformation](hyp:phi),
[its derivative](hyp:dphi), [level data](hyp:L), [a nuisance vector](hyp:e),
[a baseline bin](hyp:k), [a policy index](hyp:j), and [an observation](hyp:o), the
[fractional-interval product score](goal) is the fitted policy-union probability
times the continuous score for the preceding band, plus that band's moment
contrast times the difference between the observed policy-union membership
indicator and its fitted probability. -/
noncomputable def psiProd (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e : NuisanceCont L) (k j : ℕ) (o : Obs X Z) :=
  regularValue e.gamma k j o.1 * contScoreComponents M phi dphi L e k (j-1) o +
    contJ L e k (j-1) o.1 * (indicator (o.2.1 ∈ policyUnion L k j) - regularValue e.gamma k j o.1)
  -- @realizes \psi_{j,k}^{\text{prod}}(fractional interval product score with j-1 shift)
/-- Given [level data](hyp:L), [a nuisance vector](hyp:e), [a baseline bin](hyp:k),
and [an observation](hyp:o), the [full-interval product score](goal) is the fitted
higher-policy minus higher-baseline probability contrast times the full-interval
outcome score, plus the full-interval moment contrast times the difference between
the observed higher-policy and higher-baseline membership indicators minus their
fitted probability contrast. -/
noncomputable def psiFullProd (L : LevelData Z X) (e : NuisanceCont L) (k : ℕ) (o : Obs X Z) :=
  fullValue e.gammaFull k o.1 * psiFullJ L e k o + contFullJ L e k o.1 *
    (indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k) - fullValue e.gammaFull k o.1)
  -- @realizes \psi_{\text{full},k}^{\text{prod}}(full interval product score)
/-- Under [the model](hyp:M), given [a policy propensity transformation](hyp:phi),
[its derivative](hyp:dphi), [level data](hyp:L), [instrument-specific propensity fits](hyp:prop),
[baseline propensity fits](hyp:pk), [baseline class probability fits](hyp:pi),
[a tail policy-union probability fit](hyp:gt), and [an observation](hyp:o), the
[common final-bin score](goal) multiplies the lower outcome bound by the final
policy-union membership indicator and the sum of the transformed propensity's
excess over the highest baseline propensity and the derivative-weighted treatment
residual. It subtracts the lower outcome bound times the fitted tail probability
and the highest baseline class's probability-normalized treatment residual,
with this subtraction set to zero when the maximum level is zero. -/
noncomputable def commonTailScore (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (prop : Z → X → ℝ) (pk pi : PositiveIndex L.K → X → ℝ) (gt : X → ℝ) (o : Obs X Z) :=
  M.yMin * indicator (o.2.1 ∈ policyUnion L L.K 1) * (phi o.2.1 o.1 (prop o.2.1 o.1) - positiveValue pk L.K o.1) +
  M.yMin * indicator (o.2.1 ∈ policyUnion L L.K 1) * dphi o.2.1 o.1 (prop o.2.1 o.1) * (o.2.2.1 - prop o.2.1 o.1) -
  (if L.K = 0 then 0 else M.yMin * gt o.1 * indicator (o.2.1 ∈ L.S L.K) /
    positiveValue pi L.K o.1 * (o.2.2.1 - positiveValue pk L.K o.1))
  -- @realizes \psi_{\Delta_K}(common final-bin score)
-- @node: ass:bk-1
/-- For [a maximum level](hyp:K), [positivity of the level count](goal) means that
the maximum level is at least one. -/
def LevelCountPos (K : ℕ) : Prop := 1 ≤ K
-- @node: def:continuous-outcome-score
/-- Under [the model](hyp:M), given [a policy propensity transformation](hyp:phi),
[its derivative](hyp:dphi), [level data](hyp:L), [a positive maximum level](hyp:_hK),
[an observation](hyp:o), and [a nuisance vector](hyp:e), the
[total continuous-outcome score](goal) sums the full-interval product score and
all fractional-interval product scores in each bin below the maximum level,
then adds the common final-bin score. -/
noncomputable def psiCont (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (_hK : LevelCountPos L.K) (o : Obs X Z) (e : NuisanceCont L) :=
  (∑ k ∈ Finset.range L.K, (psiFullProd L e k o + ∑ j ∈ Finset.Icc 1 (L.l k), psiProd M phi dphi L e k j o)) +
    commonTailScore M phi dphi L e.prop e.pLev e.piLev e.gammaTail o
  -- @realizes \psi(assembled continuous total score)
-- @node: ass:pin-49
/-- Under [the model](hyp:M), for [a policy propensity transformation](hyp:phi),
[its derivative](hyp:dphi), [level data](hyp:L), and [a positive maximum level](hyp:hK),
the [score-component interpretation](goal) requires that, for every observation
and nuisance vector, the total continuous-outcome score equal the sum, over bins
below the maximum, of the full-interval product score and all fractional-interval
product scores, plus the common final-bin score. -/
def ContinuousScoreComponentsReading (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (hK : LevelCountPos L.K) : Prop :=
  ∀ o e, psiCont M phi dphi L hK o e =
    (∑ k ∈ Finset.range L.K, (psiFullProd L e k o + ∑ j ∈ Finset.Icc 1 (L.l k), psiProd M phi dphi L e k j o)) +
    commonTailScore M phi dphi L e.prop e.pLev e.piLev e.gammaTail o

/- Population nuisance ranges use the covariate law, on one measurable representative. -/
/-- Under [the model](hyp:M), for [level data](hyp:L), [admissibility](goal) of
[a continuous-outcome nuisance vector](hyp:e) requires, at every applicable index,
[instrument-specific propensity fits between zero and one almost surely under the covariate law](step:1),
[measurability of those propensity fits](step:2),
[baseline propensity fits between zero and one almost surely](step:3),
[measurability of those baseline propensity fits](step:4),
[baseline class probability fits between zero and one almost surely](step:5),
[measurability of those baseline class probability fits](step:6),
[regular policy class probability fits between zero and one almost surely](step:7),
[measurability of those regular policy class probability fits](step:8),
[within-class instrument share fits between zero and one almost surely](step:9),
[measurability of those instrument share fits](step:10),
[full-interval probability contrast fits between minus one and one almost surely](step:11),
[measurability of those full-interval probability contrast fits](step:12),
[policy-union probability fits between zero and one almost surely](step:13),
[measurability of those policy-union probability fits](step:14),
[the tail probability fit between zero and one almost surely](step:15),
[measurability of the tail probability fit](step:16),
[outcome boundary fits between the model's outcome bounds almost surely](step:17),
[measurability of those outcome boundary fits](step:18),
[plus-side cumulative-indicator mean fits between zero and one almost surely](step:19),
[measurability of those plus-side cumulative-indicator mean fits](step:20),
[minus-side cumulative-indicator mean fits between zero and one almost surely](step:21),
[measurability of those minus-side cumulative-indicator mean fits](step:22),
[plus-side band moment fits between the smaller of zero and the lower outcome bound and the larger of zero and the upper outcome bound almost surely](step:23),
[measurability of those plus-side band moment fits](step:24),
[minus-side band moment fits between the smaller of zero and the lower outcome bound and the larger of zero and the upper outcome bound almost surely](step:25),
[measurability of those minus-side band moment fits](step:26),
[plus-side full-interval mean fits between the outcome bounds almost surely](step:27),
[measurability of those plus-side full-interval mean fits](step:28),
[minus-side full-interval mean fits between the outcome bounds almost surely](step:29),
[measurability of those minus-side full-interval mean fits](step:30), and
[instrument shares that almost surely sum to one over each regular policy class
and vanish outside that class](step:31). -/
def ContAdmissible (L : LevelData Z X) (e : NuisanceCont L) : Prop :=
  (∀ z, ∀ᵐ x ∂xLaw M, e.prop z x ∈ Icc 0 1) ∧ -- @realizes p(admissible range of this nuisance component)
  (∀ z, Measurable (fun x => e.prop z x)) ∧
  (∀ k, ∀ᵐ x ∂xLaw M, e.pLev k x ∈ Icc 0 1) ∧ -- @realizes p_k(admissible range of this nuisance component)
  (∀ k, Measurable (fun x => e.pLev k x)) ∧
  (∀ k, ∀ᵐ x ∂xLaw M, e.piLev k x ∈ Icc 0 1) ∧ -- @realizes \pi_k(admissible range of this nuisance component)
  (∀ k, Measurable (fun x => e.piLev k x)) ∧
  (∀ a, ∀ᵐ x ∂xLaw M, e.tauLev a x ∈ Icc 0 1) ∧ -- @realizes \tau_{j,k}(admissible range of this nuisance component)
  (∀ a, Measurable (fun x => e.tauLev a x)) ∧
  (∀ a z, ∀ᵐ x ∂xLaw M, e.share a z x ∈ Icc 0 1) ∧ -- @realizes a_{j,k}(admissible range of this nuisance component)
  (∀ a z, Measurable (fun x => e.share a z x)) ∧
  (∀ k, ∀ᵐ x ∂xLaw M, e.gammaFull k x ∈ Icc (-1) 1) ∧ -- @realizes \gamma_{\text{full},k}(admissible range of this nuisance component)
  (∀ k, Measurable (fun x => e.gammaFull k x)) ∧
  (∀ a, ∀ᵐ x ∂xLaw M, e.gamma a x ∈ Icc 0 1) ∧ -- @realizes \gamma_{j,k}(admissible range of this nuisance component)
  (∀ a, Measurable (fun x => e.gamma a x)) ∧
  (∀ᵐ x ∂xLaw M, e.gammaTail x ∈ Icc 0 1) ∧ -- @realizes \gamma_K(admissible range of this nuisance component)
  Measurable e.gammaTail ∧
  (∀ a, ∀ᵐ x ∂xLaw M, e.nu a x ∈ Icc M.yMin M.yMax) ∧ -- @realizes \nu_{j,k}(admissible range of this nuisance component)
  (∀ a, Measurable (fun x => e.nu a x)) ∧
  (∀ a, ∀ᵐ x ∂xLaw M, e.Mplus a x ∈ Icc 0 1) ∧ -- @realizes M_{j,k}^{+}(admissible range of this nuisance component)
  (∀ a, Measurable (fun x => e.Mplus a x)) ∧
  (∀ a, ∀ᵐ x ∂xLaw M, e.Mminus a x ∈ Icc 0 1) ∧ -- @realizes M_{j,k}^{-}(admissible range of this nuisance component)
  (∀ a, Measurable (fun x => e.Mminus a x)) ∧
  (∀ a, ∀ᵐ x ∂xLaw M, e.Jplus a x ∈ Icc (min 0 M.yMin) (max 0 M.yMax)) ∧ -- @realizes J_{j,k}^{+}(admissible range of this nuisance component)
  (∀ a, Measurable (fun x => e.Jplus a x)) ∧
  (∀ a, ∀ᵐ x ∂xLaw M, e.Jminus a x ∈ Icc (min 0 M.yMin) (max 0 M.yMax)) ∧ -- @realizes J_{j,k}^{-}(admissible range of this nuisance component)
  (∀ a, Measurable (fun x => e.Jminus a x)) ∧
  (∀ k, ∀ᵐ x ∂xLaw M, e.JfullPlus k x ∈ Icc M.yMin M.yMax) ∧ -- @realizes J_{\text{full},k}^{+}(admissible range of this nuisance component)
  (∀ k, Measurable (fun x => e.JfullPlus k x)) ∧
  (∀ k, ∀ᵐ x ∂xLaw M, e.JfullMinus k x ∈ Icc M.yMin M.yMax) ∧ -- @realizes J_{\text{full},k}^{-}(admissible range of this nuisance component)
  (∀ k, Measurable (fun x => e.JfullMinus k x)) ∧
  (∀ a, ∀ᵐ x ∂xLaw M, (∑ z ∈ L.T a.val.1 a.val.2, e.share a z x) = 1 ∧ ∀ z, z ∉ L.T a.val.1 a.val.2 → e.share a z x = 0)
/-- Under [the model](hyp:M), given [level data](hyp:L),
[a choice between the full outcome range and a single band](hyp:full),
[a baseline bin](hyp:k), [a band index](hyp:j), and [covariates](hyp:x), the
[treated outcome moment contrast](goal) is the next baseline propensity times
the plus-side treated outcome moment minus the current baseline propensity times
the minus-side treated outcome moment over the chosen range. -/
noncomputable def treatedMeanContrast (L : LevelData Z X) (full : Bool) (k j : ℕ) (x : X) :=
  L.pLev (k+1) x * treatedBandMean M L true full k j x -
    L.pLev k x * treatedBandMean M L false full k j x
-- @node: def:treated-band-means
/-- Under [the model](hyp:M) and [level data](hyp:L), the
[treated outcome moment family](goal) pairs the treated outcome moments for
either side and either the full range or a band with their baseline-propensity-weighted
plus-minus contrasts, retaining their bin, band, and covariate arguments. -/
noncomputable def treatedMeanFamily (L : LevelData Z X) :=
  (treatedBandMean M L, treatedMeanContrast M L)
-- @node: def:continuous-outcome-scores
/-- Under [the model](hyp:M), given [a policy propensity transformation](hyp:phi),
[its derivative](hyp:dphi), [level data](hyp:L), and [a nuisance vector](hyp:e),
the [continuous-outcome score family](goal) collects, in order, the continuous
band score, full-interval outcome score, full-interval product score,
fractional-interval product score, and common final-bin score, retaining each
score's remaining bin, band, and observation arguments as applicable. -/
noncomputable def contScoreFamily (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e : NuisanceCont L) :=
  (contScoreComponents M phi dphi L e, psiFullJ L e, psiFullProd L e,
    psiProd M phi dphi L e, commonTailScore M phi dphi L e.prop e.pLev e.piLev e.gammaTail)

end Papers.TbsPrteOptimalTransport
