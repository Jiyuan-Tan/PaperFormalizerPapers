module
public import Papers.TbsPrteOptimalTransport.Helpers.Scores
/-! Binary-outcome score, admissibility, and population nuisances. -/
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
open scoped Classical
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)
/-- For [a baseline and policy level system](hyp:L), the [binary nuisance data](goal)
collect [instrument propensities](step:1), [positive baseline propensities](step:2),
[positive-level treated-success regressions](step:3), [positive baseline-set
probabilities](step:4), [policy-set probabilities](step:5), [within-policy-set
instrument shares](step:6), [full-interval weights](step:7), [policy subinterval
weights](step:8), and [a final-bin weight](step:9). -/
structure NuisanceBinData (L : LevelData Z X) where
  prop : Z → X → ℝ -- @realizes p(binary propensity component)
  pLev : PositiveIndex L.K → X → ℝ -- @realizes p_k(positive baseline nuisance levels; structural p0 fixed)
  P1 : PositiveIndex L.K → X → ℝ -- @realizes P_{1,k}(positive-level success regressions; no free P1_0)
  piLev : PositiveIndex L.K → X → ℝ -- @realizes \pi_k(positive baseline probability nuisances; no pi0)
  tauLev : RegularIndex L → X → ℝ -- @realizes \tau_{j,k}(policy probability nuisance carrier)
  share : RegularIndex L → Z → X → ℝ -- @realizes a_{j,k}(within-policy-set share carrier)
  gammaFull : Fin L.K → X → ℝ -- @realizes \gamma_{\text{full},k}(full-interval weight nuisance carrier)
  gamma : RegularIndex L → X → ℝ -- @realizes \gamma_{j,k}(policy weight nuisance carrier)
  gammaTail : X → ℝ -- @realizes \gamma_K(final-bin weight nuisance carrier)


-- @node: def:dml-normality-binary-nuisances
/-- For [a baseline and policy level system](hyp:L), the [binary nuisance vector](goal)
is the record of binary nuisance data, with no free structural-zero coordinates. -/
def NuisanceBin (L : LevelData Z X) := NuisanceBinData L
  -- @realizes \eta(binary nuisance vector; structural-zero components omitted)
/-- For [a baseline and policy level system](hyp:L), [addition of binary nuisance
vectors](goal) adds each of their nine coordinates pointwise. -/
instance (L : LevelData Z X) : Add (NuisanceBin L) := ⟨fun a b =>
  ⟨a.prop+b.prop, a.pLev+b.pLev, a.P1+b.P1, a.piLev+b.piLev, a.tauLev+b.tauLev,
   a.share+b.share, a.gammaFull+b.gammaFull, a.gamma+b.gamma, a.gammaTail+b.gammaTail⟩⟩
/-- For [a baseline and policy level system](hyp:L), [real scalar multiplication
of binary nuisance vectors](goal) multiplies each coordinate pointwise. -/
instance (L : LevelData Z X) : SMul ℝ (NuisanceBin L) := ⟨fun t a =>
  ⟨t • a.prop, t • a.pLev, t • a.P1, t • a.piLev, t • a.tauLev,
   t • a.share, t • a.gammaFull, t • a.gamma, t • a.gammaTail⟩⟩
/-- In [the latent instrument model](hyp:M), for [a baseline level system](hyp:L),
[a level index](hyp:k), and [covariates](hyp:x), the [treated-success regression](goal)
is zero at level zero; otherwise it uses [the conditional joint law of outcome,
treatment, and instrument](step:1), [restricts that law to the baseline instrument
set](step:2), and [divides the integral of outcome times treatment by the selected
mass](step:3). -/
noncomputable def treatedSuccess (L : LevelData Z X) (k : ℕ) (x : X) :=
  if k = 0 then 0 else
  let joint := condDistrib (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure x
  let sel := joint.restrict {a | a.2.2 ∈ (L.S k : Set Z)}
  (sel univ).toReal⁻¹ * ∫ a, a.1 * a.2.1 ∂sel
/-- For [the latent instrument model](hyp:M) and [a baseline and policy level
system](hyp:L), the [population binary nuisance vector](goal) collects the true
propensities, baseline propensities, treated-success regressions, baseline and
policy-set probabilities, instrument shares, and full, subinterval, and tail weights. -/
noncomputable def eta0Bin (L : LevelData Z X) : NuisanceBin L :=
  ⟨M.prop, fun k => L.pLev k, fun k => treatedSuccess M L k,
   fun k => (levelSetProb M L).1 k, fun a => (levelSetProb M L).2 a.val.1 a.val.2,
   fun a => levelShares M L a.val.1 a.val.2,
   fun k => gammaFull M L k,
   fun a => gamma M L a.val.1 a.val.2, gammaTail M L⟩
/-- Given [a policy propensity transformation](hyp:phi), [a level system](hyp:L),
[binary nuisance values](hyp:e), [a baseline interval](hyp:k), [a boundary index](hyp:j),
and [covariates](hyp:x), the [pooled binary boundary](goal) equals the lower baseline
propensity at index zero, the upper baseline propensity above the last policy
boundary, and otherwise the share-weighted sum of transformed instrument propensities
over the policy set, with zero shares for invalid indices. -/
noncomputable def pooledQBin (phi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e : NuisanceBin L) (k j : ℕ) (x : X) :=
  if j = 0 then positiveValue e.pLev k x else if L.l k < j then positiveValue e.pLev (k+1) x else
    ∑ z ∈ L.T k j, (if h : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k then e.share ⟨(k,j),h⟩ z x else 0) *
      phi z x (e.prop z x)
/-- For [a level system](hyp:L), [binary nuisance values](hyp:e), [a baseline
level](hyp:k), and [an observation](hyp:o), the [treated-success residual](goal)
is zero at level zero and otherwise multiplies outcome times treatment minus its
baseline regression by baseline-set membership divided by the baseline-set probability. -/
noncomputable def RP (L : LevelData Z X) (e : NuisanceBin L) (k : ℕ) (o : Obs X Z) :=
  if k = 0 then 0 else indicator (o.2.1 ∈ L.S k) / positiveValue e.piLev k o.1 *
    (o.2.2.2 * o.2.2.1 - positiveValue e.P1 k o.1)
  -- @realizes R_{P,k}(treated-success IPW residual)
/-- For [a level system](hyp:L), [binary nuisance values](hyp:e), [a baseline
level](hyp:k), and [an observation](hyp:o), the [baseline propensity residual](goal)
is zero at level zero and otherwise multiplies treatment minus its baseline
propensity by baseline-set membership divided by the baseline-set probability. -/
noncomputable def Rp (L : LevelData Z X) (e : NuisanceBin L) (k : ℕ) (o : Obs X Z) :=
  if k = 0 then 0 else indicator (o.2.1 ∈ L.S k) / positiveValue e.piLev k o.1 *
    (o.2.2.1 - positiveValue e.pLev k o.1)
  -- @realizes R_{p,k}(positive baseline propensity residual)
/-- For [a policy derivative function](hyp:dphi), [a level system](hyp:L),
[binary nuisance values](hyp:e), [a baseline interval](hyp:k), [a policy boundary](hyp:j),
and [an observation](hyp:o), the [pooled policy residual](goal) is zero at boundary
zero or beyond the last boundary; otherwise it sums instrument-specific treatment
residuals weighted by the policy derivative and instrument membership, divided by
the policy-set probability. -/
noncomputable def RqBin (dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e : NuisanceBin L) (k j : ℕ) (o : Obs X Z) :=
  if j = 0 ∨ L.l k < j then 0 else (regularValue e.tauLev k j o.1)⁻¹ *
    ∑ z ∈ L.T k j, dphi z o.1 (e.prop z o.1) * indicator (o.2.1 = z) * (o.2.2.1 - e.prop z o.1)
/-- For [a level system](hyp:L), [binary nuisance values](hyp:e), [a baseline
interval](hyp:k), and [covariates](hyp:x), the [full-interval treated-success
increment](goal) is the upper baseline treated-success regression minus the lower one. -/
noncomputable def binFullJ (L : LevelData Z X) (e : NuisanceBin L) (k : ℕ) (x : X) :=
  positiveValue e.P1 (k+1) x - positiveValue e.P1 k x
/-- For [a policy transformation](hyp:phi), [a level system](hyp:L), [binary
nuisance values](hyp:e), [a baseline interval](hyp:k), [a policy subinterval](hyp:j),
and [covariates](hyp:x), the [binary lower subinterval contribution](goal) is the
positive part of the current pooled boundary minus the larger of the previous
pooled boundary and the upper baseline propensity less the full treated-success increment. -/
noncomputable def hMinus (phi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e : NuisanceBin L) (k j : ℕ) (x : X) :=
  max 0 (pooledQBin phi L e k j x -
    max (pooledQBin phi L e k (j-1) x) (positiveValue e.pLev (k+1) x - binFullJ L e k x))
  -- @realizes h_{j,k}^{-}(binary subinterval positive-part formula)
/-- For [a policy transformation](hyp:phi), [a level system](hyp:L), [binary
nuisance values](hyp:e), [a baseline interval](hyp:k), [a policy subinterval](hyp:j),
and [covariates](hyp:x), the [active-set indicator](goal) is one precisely when
the current pooled boundary strictly exceeds both the previous boundary and the
upper baseline propensity less the full treated-success increment, and zero otherwise. -/
noncomputable def Iact (phi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e : NuisanceBin L) (k j : ℕ) (x : X) :=
  indicator (pooledQBin phi L e k j x >
    max (pooledQBin phi L e k (j-1) x) (positiveValue e.pLev (k+1) x - binFullJ L e k x))
  -- @realizes I_{j,k}^{-}(strict active-set indicator)
/-- For [a policy transformation](hyp:phi), [a level system](hyp:L), [binary
nuisance values](hyp:e), [a baseline interval](hyp:k), [a policy subinterval](hyp:j),
and [covariates](hyp:x), the [interior-boundary indicator](goal) is one precisely
when the upper baseline propensity less the full treated-success increment lies
strictly between the previous and current pooled boundaries, and zero otherwise. -/
noncomputable def Dbd (phi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e : NuisanceBin L) (k j : ℕ) (x : X) :=
  indicator (pooledQBin phi L e k (j-1) x < positiveValue e.pLev (k+1) x - binFullJ L e k x ∧
    positiveValue e.pLev (k+1) x - binFullJ L e k x < pooledQBin phi L e k j x)
  -- @realizes D_{j,k}^{-}(strict interior-boundary indicator)
/-- For [a policy transformation](hyp:phi), [a level system](hyp:L), [binary
nuisance values](hyp:e), [a baseline interval](hyp:k), [a policy subinterval](hyp:j),
and [covariates](hyp:x), the [dominance indicator](goal) is one precisely when
the previous pooled boundary strictly exceeds the upper baseline propensity less
the full treated-success increment, and zero otherwise. -/
noncomputable def Edom (phi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e : NuisanceBin L) (k j : ℕ) (x : X) :=
  indicator (pooledQBin phi L e k (j-1) x > positiveValue e.pLev (k+1) x - binFullJ L e k x)
  -- @realizes E_{j,k}^{-}(strict dominance indicator)
/-- For [a policy transformation](hyp:phi), [its derivative function](hyp:dphi),
[a level system](hyp:L), [binary nuisance values](hyp:e), [a baseline interval](hyp:k),
[a policy subinterval](hyp:j), and [an observation](hyp:o), the [binary subinterval
score](goal) adds the lower subinterval contribution, the interior-boundary-weighted
difference of adjacent treated-success residuals, and the active current policy
residual; it subtracts the interior-boundary-weighted upper propensity residual,
the dominance-and-activity-weighted lower propensity residual at the first
subinterval, and the dominance-and-activity-weighted previous policy residual. -/
noncomputable def binScoreComponents (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e : NuisanceBin L) (k j : ℕ) (o : Obs X Z) :=
  hMinus phi L e k j o.1 + Dbd phi L e k j o.1 * (RP L e (k+1) o - RP L e k o) -
    Dbd phi L e k j o.1 * Rp L e (k+1) o -
    (if j = 1 then Edom phi L e k j o.1 * Iact phi L e k j o.1 * Rp L e k o else 0) +
    Iact phi L e k j o.1 * RqBin dphi L e k j o -
    Edom phi L e k j o.1 * Iact phi L e k j o.1 * RqBin dphi L e k (j-1) o
  -- @realizes \psi_{j,k}^{h}(binary h score)
  -- @realizes \alpha_{P,k+1}^{(j,k)}(coefficient Dbd)
  -- @realizes \alpha_{P,k}^{(j,k)}(coefficient -Dbd)
  -- @realizes \alpha_{p,k+1}^{(j,k)}(coefficient -Dbd)
  -- @realizes \alpha_{p,k}^{(j,k)}(coefficient -Edom*Iact at j=1)
/-- For [a policy transformation](hyp:phi), [its derivative function](hyp:dphi),
[a level system](hyp:L), [binary nuisance values](hyp:e), [a baseline interval](hyp:k),
[a policy subinterval](hyp:j), and [an observation](hyp:o), the [weighted binary
subinterval score](goal) is the policy weight times the subinterval score plus
the lower subinterval contribution times the difference between policy-union
membership and that weight. -/
noncomputable def psiProdBin (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e : NuisanceBin L) (k j : ℕ) (o : Obs X Z) :=
  regularValue e.gamma k j o.1 * binScoreComponents phi dphi L e k j o +
    hMinus phi L e k j o.1 * (indicator (o.2.1 ∈ policyUnion L k j) - regularValue e.gamma k j o.1)
/-- For [a level system](hyp:L), [binary nuisance values](hyp:e), [a baseline
interval](hyp:k), and [an observation](hyp:o), the [weighted full-interval binary
score](goal) is the full-interval weight times the sum of the treated-success
increment and its adjacent residual difference, plus the increment times the
difference between higher-policy and higher-baseline membership less the
full-interval weight. -/
noncomputable def psiFullProdBin (L : LevelData Z X) (e : NuisanceBin L) (k : ℕ) (o : Obs X Z) :=
  fullValue e.gammaFull k o.1 * (binFullJ L e k o.1 + RP L e (k+1) o - RP L e k o) +
    binFullJ L e k o.1 * (indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k) -
      fullValue e.gammaFull k o.1)
-- @node: def:binary-score
/-- For [the latent instrument model](hyp:M), [a policy transformation](hyp:phi),
[its derivative function](hyp:dphi), [a level system](hyp:L) with [a positive
number of levels](hyp:_hK), [an observation](hyp:o), and [binary nuisance values](hyp:e),
the [binary outcome score](goal) sums weighted full-interval and policy-subinterval
scores over all baseline intervals and adds the common tail score. -/
noncomputable def psiBin (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (_hK : LevelCountPos L.K) (o : Obs X Z) (e : NuisanceBin L) :=
  (∑ k ∈ Finset.range L.K, (psiFullProdBin L e k o +
    ∑ j ∈ Finset.Icc 1 (L.l k), psiProdBin phi dphi L e k j o)) +
    commonTailScore M phi dphi L e.prop e.pLev e.piLev e.gammaTail o
/-- For [the latent instrument model](hyp:M), [a policy transformation](hyp:phi),
[a level system](hyp:L), [binary nuisance values](hyp:e), and [covariates](hyp:x),
the [binary target integrand](goal) sums full-interval weights times treated-success
increments and subinterval weights times lower subinterval contributions, then
adds the lower outcome endpoint times the instrument-probability-weighted excess
of transformed propensities over the final baseline propensity in the tail policy union. -/
noncomputable def mBin (phi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e : NuisanceBin L) (x : X) :=
  (∑ k ∈ Finset.range L.K, (fullValue e.gammaFull k x * binFullJ L e k x +
    ∑ j ∈ Finset.Icc 1 (L.l k), regularValue e.gamma k j x * hMinus phi L e k j x)) + -- @realizes \gamma_{j,k}(component range on this conjunct)
  M.yMin * ∑ z ∈ policyUnion L L.K 1, instProb M z x * (phi z x (e.prop z x) - positiveValue e.pLev L.K x)
  -- @realizes m(binary target integrand)
-- @node: ass:pin-36
/-- For [the latent instrument model](hyp:M), [a policy transformation](hyp:phi),
[its derivative function](hyp:dphi), and [a level system](hyp:L) with [a positive
number of levels](hyp:hK), the [binary score decomposition property](goal) says
that, at every observation and nuisance vector, the score equals the sum of all
weighted full-interval and policy-subinterval scores plus the common tail score. -/
def BinaryScoreComponentsReading (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (hK : LevelCountPos L.K) : Prop := ∀ o e, psiBin M phi dphi L hK o e =
  (∑ k ∈ Finset.range L.K, (psiFullProdBin L e k o +
    ∑ j ∈ Finset.Icc 1 (L.l k), psiProdBin phi dphi L e k j o)) +
    commonTailScore M phi dphi L e.prop e.pLev e.piLev e.gammaTail o
/-- For [a level system](hyp:L) and [a binary nuisance vector](hyp:e), the
[structural-zero nuisance property](goal) requires [the baseline propensity at
level zero to be identically zero](step:1) and [the treated-success regression at
level zero to be identically zero](step:2). -/
-- @node: ass:pin-37
def BinaryNuisanceListReading (L : LevelData Z X) (e : NuisanceBin L) : Prop :=
  positiveValue e.pLev 0 = (fun _ => 0) ∧ positiveValue e.P1 0 = (fun _ => 0)

/- Population nuisance ranges use the covariate law, on one measurable representative. -/
/-- Under [the model's covariate law](hyp:M), for [a level system](hyp:L) and
[binary nuisance values](hyp:e), [binary admissibility](goal) requires [instrument
propensities in the unit interval almost everywhere](step:1), [measurable instrument
propensities](step:2), [positive baseline propensities, treated-success regressions,
and baseline-set probabilities in the unit interval almost everywhere](step:3),
[measurability of those three baseline coordinates](step:4), [policy-set probabilities
and subinterval weights in the unit interval almost everywhere](step:5),
[measurability of those policy coordinates](step:6), [instrument shares in the
unit interval almost everywhere](step:7), [measurable instrument shares](step:8),
[shares summing to one on each policy set and vanishing off it almost everywhere](step:9),
[full-interval weights between minus one and one almost everywhere](step:10),
[measurable full-interval weights](step:11), [a tail weight in the unit interval
almost everywhere](step:12), and [a measurable tail weight](step:13). -/
def BinAdmissible (L : LevelData Z X) (e : NuisanceBin L) : Prop :=
  (∀ z, ∀ᵐ x ∂xLaw M, e.prop z x ∈ Icc (0:ℝ) 1) ∧ (∀ z, Measurable (e.prop z)) ∧ -- @realizes p(component range on this conjunct)
  (∀ k, ∀ᵐ x ∂xLaw M, e.pLev k x ∈ Icc (0:ℝ) 1 ∧ e.P1 k x ∈ Icc (0:ℝ) 1 ∧ e.piLev k x ∈ Icc (0:ℝ) 1) ∧ -- @realizes p_k(component range on this conjunct) @realizes P_{1,k}(component range on this conjunct) @realizes \pi_k(component range on this conjunct)
  (∀ k, Measurable (e.pLev k) ∧ Measurable (e.P1 k) ∧ Measurable (e.piLev k)) ∧
  (∀ a, ∀ᵐ x ∂xLaw M, e.tauLev a x ∈ Icc (0:ℝ) 1 ∧ e.gamma a x ∈ Icc (0:ℝ) 1) ∧ -- @realizes \tau_{j,k}(component range on this conjunct) @realizes \gamma_{j,k}(component range on this conjunct)
  (∀ a, Measurable (e.tauLev a) ∧ Measurable (e.gamma a)) ∧
  (∀ a z, ∀ᵐ x ∂xLaw M, e.share a z x ∈ Icc (0:ℝ) 1) ∧ (∀ a z, Measurable (e.share a z)) ∧ -- @realizes a_{j,k}(component range on this conjunct)
  (∀ a, ∀ᵐ x ∂xLaw M, (∑ z ∈ L.T a.val.1 a.val.2, e.share a z x) = 1 ∧
    ∀ z, z ∉ L.T a.val.1 a.val.2 → e.share a z x = 0) ∧
  (∀ k, ∀ᵐ x ∂xLaw M, e.gammaFull k x ∈ Icc (-1:ℝ) 1) ∧ (∀ k, Measurable (e.gammaFull k)) ∧ -- @realizes \gamma_{\text{full},k}(component range on this conjunct)
  (∀ᵐ x ∂xLaw M, e.gammaTail x ∈ Icc (0:ℝ) 1) ∧ Measurable e.gammaTail -- @realizes \gamma_K(component range on this conjunct)
-- @node: ass:orthogonality-discrete-admissibility
/-- For [the latent instrument model](hyp:M), [a level system](hyp:L), [a base
nuisance vector](hyp:eta0), and [a perturbation vector](hyp:del), [direction
admissibility](goal) means [continuous base and perturbation vectors remain
continuously admissible for every sufficiently small absolute step](step:1),
[binary base and perturbation vectors remain binary admissible for every
sufficiently small absolute step](step:2), and [vectors of different outcome
types are inadmissible](step:3). -/
def DirectionAdmissible (L : LevelData Z X)
    (eta0 del : NuisanceCont L ⊕ NuisanceBin L) : Prop := -- @realizes \delta(nuisance perturbation carrier)
  match eta0, del with
  | .inl eta0, .inl del => ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, |t| < r → ContAdmissible M L (eta0 + t • del)
  | .inr eta0, .inr del => ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, |t| < r → BinAdmissible M L (eta0 + t • del)
  | _, _ => False
-- @node: def:orthogonality-discrete-directions
/-- For [the latent instrument model](hyp:M), [a level system](hyp:L), [a base
nuisance vector](hyp:eta0), and [a perturbation vector](hyp:del), the [admissible
direction certificate](goal) records [admissibility of every sufficiently small
perturbation of the base vector in that direction](step:1). -/
structure IsAdmissibleDirection (L : LevelData Z X)
    (eta0 del : NuisanceCont L ⊕ NuisanceBin L) : Prop where
  admissible : DirectionAdmissible M L eta0 del -- @realizes \mathcal T(neighborhood-admissible nuisance directions)
-- @node: def:binary-outcome-scores
/-- For [the latent instrument model](hyp:M), [a policy transformation](hyp:phi),
[its derivative function](hyp:dphi), [a level system](hyp:L), and [binary nuisance
values](hyp:e), the [binary score family](goal) consists of the subinterval score,
the weighted full-interval score, the weighted subinterval score, and the common
tail score, each retaining its observation and interval arguments as applicable. -/
noncomputable def binScoreFamily (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e : NuisanceBin L) :=
  (binScoreComponents phi dphi L e, psiFullProdBin L e,
    psiProdBin phi dphi L e, commonTailScore M phi dphi L e.prop e.pLev e.piLev e.gammaTail)

-- @node: pooledQBin_range
/-- If [the policy transformation is measurable and maps the unit interval into
itself](hyp:hphi), [the binary nuisance vector is admissible](hyp:he), [the baseline
interval index is below the number of levels](hyp:hk), and [the boundary index
does not exceed the number of policy boundaries](hyp:hj), then [the pooled binary
boundary lies in the unit interval for almost every covariate value](goal). -/
lemma pooledQBin_range (phi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e : NuisanceBin L) (hphi : IsPolicyMap phi) (he : BinAdmissible M L e)
    (k : ℕ) (hk : k < L.K) (j : ℕ) (hj : j ≤ L.l k) :
    ∀ᵐ x ∂xLaw M, pooledQBin phi L e k j x ∈ Icc (0 : ℝ) 1 := by
  rcases he with ⟨hprop, hmp, hlev, hmlev, htau, hmtau, hshare, hmshare,
    hsum, hgamma, hmgamma, htail, hmtail⟩
  have hlevels := ae_all_iff.mpr hlev
  have hprops := ae_all_iff.mpr hprop
  have hshares := ae_all_iff.mpr (fun a => ae_all_iff.mpr (hshare a))
  have hsums := ae_all_iff.mpr hsum
  filter_upwards [hlevels, hprops, hshares, hsums] with x hx hp hs hsumx
  unfold pooledQBin
  by_cases hj0 : j = 0
  · rw [if_pos hj0]
    unfold positiveValue
    split
    · exact (hx _).1
    · exact ⟨le_rfl, zero_le_one⟩
  · have ha : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k := ⟨hk.le, by omega, hj⟩
    rw [if_neg hj0, if_neg (not_lt.mpr hj)]
    simp only [dif_pos ha]
    let a : RegularIndex L := ⟨(k,j), ha⟩
    have hsum1 : ∑ z ∈ L.T k j, e.share a z x = 1 := (hsumx a).1
    constructor
    · exact Finset.sum_nonneg fun z hz => mul_nonneg (hs a z).1 (hphi.2 z x _ (hp z)).1
    · calc
        ∑ z ∈ L.T k j, e.share a z x * phi z x (e.prop z x) ≤
            ∑ z ∈ L.T k j, e.share a z x := by
          apply Finset.sum_le_sum
          intro z hz
          exact mul_le_of_le_one_right (hs a z).1 (hphi.2 z x _ (hp z)).2
        _ = 1 := hsum1

-- @node: binary_auxiliary_ranges
/-- If [the policy transformation is measurable and maps the unit interval into
itself](hyp:hphi) and [the binary nuisance vector is admissible](hyp:he), then
[for every baseline interval below the number of levels and every policy
subinterval indexed from one through its last boundary, the lower subinterval
contribution lies in the unit interval and the dominance indicator is zero or
one for almost every covariate value](goal). -/
lemma binary_auxiliary_ranges (phi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e : NuisanceBin L) (hphi : IsPolicyMap phi) (he : BinAdmissible M L e) :
    ∀ k < L.K, ∀ j, 1 ≤ j → j ≤ L.l k → ∀ᵐ x ∂xLaw M,
      hMinus phi L e k j x ∈ Icc (0 : ℝ) 1 ∧ Edom phi L e k j x ∈ ({0,1} : Set ℝ) := by
  intro k hk j hj1 hj
  have hjprev : j - 1 ≤ L.l k := (Nat.sub_le j 1).trans hj
  filter_upwards [pooledQBin_range M phi L e hphi he k hk j hj,
    pooledQBin_range M phi L e hphi he k hk (j-1) hjprev] with x hq hqprev
  constructor
  · unfold hMinus
    constructor
    · exact le_max_left _ _
    · apply max_le zero_le_one
      have hbase : 0 ≤ max (pooledQBin phi L e k (j-1) x)
          (positiveValue e.pLev (k+1) x - binFullJ L e k x) :=
        hqprev.1.trans (le_max_left _ _)
      exact (sub_le_self _ hbase).trans hq.2
  · unfold Edom indicator
    split <;> simp
  -- @realizes h_{j,k}^{-}(binary nonnegative subinterval length at most one)
  -- @realizes E_{j,k}^{-}(binary dominance indicator)

end Papers.TbsPrteOptimalTransport
