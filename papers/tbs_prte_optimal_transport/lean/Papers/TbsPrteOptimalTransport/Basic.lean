module
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Causalean.Stat.Coupling.Monotone.ProductLoss.PIT
/-! Structural latent-resistance model, observed laws, and constrained transport. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical
universe u v
-- @env: S1
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]

/-- A [latent instrumental-variable model](goal) on a [population sample space](hyp:Ω),
[covariate space](hyp:X), and [instrument space](hyp:Z) records a probability law,
potential and observed outcomes, unit-interval resistance, binary treatment, a unit-interval
propensity function, and a conditional instrument distribution, together with measurability
and a Euclidean embedding of the covariates. -/
structure LatentIVModel (Ω : Type u) (X Z : Type v)
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z]
    [TopologicalSpace X] [StandardBorelSpace Z] [Nonempty Z] where
  law : ProbabilityMeasure Ω
  Yset : Set ℝ -- @realizes \mathcal{Y}(carrier Set ℝ; compactness via DomainsCompactBorel)
  yMin : ℝ -- @realizes y_{\min}(known endpoint; range via OutcomeEndpointsKnown)
  yMax : ℝ -- @realizes y_{\max}(known endpoint; range via OutcomeEndpointsKnown)
  dX : ℕ -- @realizes d_X(covariate dimension)
  covariateCoordinates : X → (Fin dX → ℝ) -- @realizes \mathcal{X}(Euclidean covariate carrier)
  coordinates_isEmbedding : Topology.IsEmbedding covariateCoordinates -- @realizes \mathcal{X}(given Euclidean subspace topology)
  Y0 : Ω → ℝ -- @realizes Y(0)(range via PotentialSupport)
  Y1 : Ω → ℝ -- @realizes Y(1)(range via PotentialSupport)
  U : Ω → ℝ -- @realizes U(resistance carrier; intrinsic range in rangeU)
  W : Ω → ℝ -- @realizes W(treatment carrier; intrinsic range in rangeW)
  rangeU : ∀ s, U s ∈ Icc (0 : ℝ) 1 -- @realizes U(resistance values in [0,1])
  rangeW : ∀ s, W s = 0 ∨ W s = 1 -- @realizes W(binary treatment values) @realizes \mathcal{W}(W takes values in the binary domain)
  Y : Ω → ℝ -- @realizes Y(range via Consistency and PotentialSupport)
  Xv : Ω → X -- @realizes X(covariate random variable)
  Zv : Ω → Z -- @realizes Z(instrument random variable) @realizes \mathcal{Z}(carrier Z)
  prop : Z → X → ℝ -- @realizes p(carrier; intrinsic range via rangeProp)
  rangeProp : ∀ z x, prop z x ∈ Icc (0 : ℝ) 1 -- @realizes p(intrinsic propensity range) @realizes P(evaluated propensity lies in [0,1])
  measY0 : Measurable Y0
  measY1 : Measurable Y1
  measU : Measurable U
  measW : Measurable W
  measY : Measurable Y
  measX : Measurable Xv
  measZ : Measurable Zv
  instKernel : Kernel X Z
  instKernel_markov : IsMarkovKernel instKernel
  instKernel_version : instKernel =ᵐ[law.toMeasure.map Xv] condDistrib Zv Xv law.toMeasure

variable (M : LatentIVModel Ω X Z)
/-- For the [latent instrumental-variable model](hyp:M), the
[underlying population measure has total mass one](goal). -/
instance : IsProbabilityMeasure M.law.toMeasure := M.law.property
/-- For the [latent instrumental-variable model](hyp:M), the [covariate law](goal)
is the distribution of its covariate random variable under the population law. -/
noncomputable def xLaw := M.law.toMeasure.map M.Xv
/-- For the [latent instrumental-variable model](hyp:M), the [joint instrument and covariate law](goal)
is the distribution of the instrument–covariate pair under the population law. -/
noncomputable def zxLaw := M.law.toMeasure.map (fun s => (M.Zv s, M.Xv s))
/-- For the [latent instrumental-variable model](hyp:M), the [observed-data law](goal)
is the joint distribution of the observed outcome, treatment, instrument, and covariates. -/
noncomputable def observedLaw := M.law.toMeasure.map (fun s => (M.Y s, M.W s, M.Zv s, M.Xv s))
  -- @realizes \mathbb{P}_{obs}(joint law of Y,W,Z,X)
/-- For the [latent instrumental-variable model](hyp:M) and [choice of treatment status](hyp:w),
the [potential outcome](goal) is the treated potential outcome when treatment is selected
and the untreated potential outcome otherwise. -/
def potential (w : Bool) := if w then M.Y1 else M.Y0
  -- @realizes Y(w)(binary potential-outcome family)
/-- The [treatment domain](goal) consists of the two real values zero and one. -/
noncomputable def treatmentDomain : Set ℝ := {0, 1}
  -- @realizes \mathcal{W}(binary treatment domain)
/-- For the [latent instrumental-variable model](hyp:M), the [observed propensity random variable](goal)
evaluates the propensity function at each individual's instrument and covariates. -/
noncomputable def observedPropensity := fun a => M.prop (M.Zv a) (M.Xv a) -- @realizes P(propensity random variable; intrinsic range via rangeProp)

/-- Given a [covariate space](hyp:X), a [candidate joint measure of resistance, covariates,
and both potential outcomes](hyp:piT), and a [choice of treatment status](hyp:w), the
[corresponding marginal measure](goal) retains resistance, covariates, and the potential
outcome for that status. -/
noncomputable def latentJointMarginal (piT : Measure ((ℝ × X) × (ℝ × ℝ))) (w : Bool) :=
  piT.map (fun a => (a.1, if w then a.2.2 else a.2.1))
  -- @realizes \tilde{\pi}_w(marginal of a joint candidate potential-outcome law)
-- @node: ass:domains-compact-borel
/-- For the [latent instrumental-variable model](hyp:M), the [domain regularity condition](goal)
requires that [the outcome domain is compact](step:1) and [nonempty](step:2),
[the covariate space is compact](step:3), [the instrument space is compact](step:4),
and [both the covariate space](step:5) and [the instrument space](step:6) are standard Borel spaces. -/
def DomainsCompactBorel : Prop :=
  IsCompact M.Yset ∧ M.Yset.Nonempty ∧ -- @realizes \mathcal{Y}(nonempty compact outcome domain)
  CompactSpace X ∧ -- @realizes \mathcal{X}(compact Euclidean subspace with dimension d_X)
  CompactSpace Z ∧ -- @realizes \mathcal{Z}(compact instrument domain)
  StandardBorelSpace X ∧ StandardBorelSpace Z -- @realizes \mathcal{X}(standard Borel) @realizes \mathcal{Z}(standard Borel)
-- @node: ass:outcome-endpoints-known
/-- For the [latent instrumental-variable model](hyp:M), the [known-endpoints condition](goal)
requires that [the designated lower endpoint is the least outcome in the domain](step:1)
and [the designated upper endpoint is the greatest outcome in the domain](step:2). -/
def OutcomeEndpointsKnown : Prop :=
  IsLeast M.Yset M.yMin ∧ IsGreatest M.Yset M.yMax
-- @node: ass:structure-potential-support
/-- For the [latent instrumental-variable model](hyp:M), the [potential-outcome support condition](goal)
requires that [the untreated potential outcome lies in the outcome domain almost surely](step:1)
and [the treated potential outcome lies in that domain almost surely](step:2). -/
def PotentialSupport : Prop :=
  (∀ᵐ s ∂M.law.toMeasure, M.Y0 s ∈ M.Yset) ∧
  (∀ᵐ s ∂M.law.toMeasure, M.Y1 s ∈ M.Yset)
-- @node: ass:structure-consistency
/-- For the [latent instrumental-variable model](hyp:M), [consistency](goal) means that,
almost surely, the observed outcome equals treatment times the treated potential outcome
plus one minus treatment times the untreated potential outcome. -/
def Consistency : Prop :=
  ∀ᵐ s ∂M.law.toMeasure, M.Y s = M.W s * M.Y1 s + (1 - M.W s) * M.Y0 s
-- @node: ass:structure-instrument-exogeneity
/-- For the [latent instrumental-variable model](hyp:M), [instrument exogeneity](goal)
means that, for almost every covariate value, the conditional joint law of the instrument,
resistance, and both potential outcomes factors into the model's conditional instrument law
and the conditional joint law of resistance and both potential outcomes. -/
def InstrumentExogeneity : Prop :=
  condDistrib (fun s => (M.Zv s, (M.U s, M.Y0 s, M.Y1 s))) M.Xv M.law.toMeasure
    =ᵐ[xLaw M] fun x => (M.instKernel x).prod
      (condDistrib (fun s => (M.U s, M.Y0 s, M.Y1 s)) M.Xv M.law.toMeasure x)
  -- @realizes \indep(conditional joint-law factorization)
-- @node: ass:structure-threshold-crossing
/-- For the [latent instrumental-variable model](hyp:M), the [threshold-crossing condition](goal)
requires that [treatment equals one exactly when resistance does not exceed propensity,
almost surely](step:1), [propensity is jointly measurable](step:2),
[propensity lies between zero and one at every instrument–covariate pair](step:3), and
[conditional mean treatment equals propensity for almost every instrument–covariate pair](step:4). -/
def ThresholdCrossing : Prop :=
  (∀ᵐ s ∂M.law.toMeasure,
    M.W s = if M.U s ≤ M.prop (M.Zv s) (M.Xv s) then 1 else 0) ∧
  Measurable (Function.uncurry M.prop) ∧
  (∀ z x, M.prop z x ∈ Icc (0 : ℝ) 1) ∧ -- @realizes p(propensity range [0,1])
  (∀ᵐ zx ∂zxLaw M,
    ∫ w, w ∂condDistrib M.W (fun s => (M.Zv s, M.Xv s)) M.law.toMeasure zx
      = M.prop zx.1 zx.2)
-- @node: ass:structure-uniform-resistance
/-- For the [latent instrumental-variable model](hyp:M), [uniform resistance](goal)
means that, for almost every covariate value, the conditional resistance distribution
is uniform on the unit interval. -/
def UniformResistance : Prop :=
  ∀ᵐ x ∂xLaw M, condDistrib M.U M.Xv M.law.toMeasure x = Causalean.Stat.unifOI
-- @node: ass:structure-common-support
/-- For the [latent instrumental-variable model](hyp:M), [common instrument support](goal)
means that there exists a conditional instrument kernel that [is a probability kernel](step:1),
[agrees with the conditional instrument distribution for almost every covariate value](step:2),
and [assigns positive probability to every nonempty open instrument set at every covariate value](step:3). -/
def CommonInstrumentSupport : Prop :=
  ∃ κ : Kernel X Z, IsMarkovKernel κ ∧
    κ =ᵐ[xLaw M] condDistrib M.Zv M.Xv M.law.toMeasure ∧
    ∀ x (A : Set Z), IsOpen A → A.Nonempty → 0 < κ x A

/-- For the [latent instrumental-variable model](hyp:M), the [structural assumptions](goal)
combine [potential-outcome support](step:1), [consistency](step:2),
[conditional instrument exogeneity](step:3), [threshold crossing with a measurable propensity
equal to conditional mean treatment](step:4), [conditionally uniform resistance](step:5),
[common instrument support](step:6), and [compact, nonempty outcome and compact standard Borel covariate and instrument domains](step:7). -/
def StructuralAssumptions : Prop := PotentialSupport M ∧ Consistency M ∧
  InstrumentExogeneity M ∧ ThresholdCrossing M ∧ UniformResistance M ∧
  CommonInstrumentSupport M ∧ DomainsCompactBorel M
-- @node: ass:pin-12
/-- For the [latent instrumental-variable model](hyp:M), the [almost-sure reading of consistency](goal)
requires that the observed outcome almost surely equals the potential outcome for the realized treatment. -/
def ConsistencyAEReading : Prop := Consistency M
-- @node: ass:pin-13
/-- For the [latent instrumental-variable model](hyp:M), the [almost-sure threshold-crossing reading](goal)
requires that treatment is one when resistance does not exceed the instrument- and covariate-specific
propensity and zero otherwise, almost surely. -/
def ThresholdCrossingAEReading : Prop :=
  ∀ᵐ s ∂M.law.toMeasure, M.W s = if M.U s ≤ M.prop (M.Zv s) (M.Xv s) then 1 else 0
-- @node: ass:pin-14
/-- For the [latent instrumental-variable model](hyp:M), the [almost-sure uniform-resistance reading](goal)
requires that resistance is conditionally uniform on the unit interval for almost every covariate value. -/
def UniformResistanceAEReading : Prop := UniformResistance M
-- @node: ass:target-weight-measurable
/-- On the [covariate space](hyp:X), a [weight function of covariates and resistance](hyp:om)
satisfies [target-weight measurability](goal) when it is jointly measurable with resistance
restricted to the closed unit interval. -/
def TargetWeightMeasurable (om : X → ℝ → ℝ) : Prop :=
  Measurable (fun xu : X × Icc (0 : ℝ) 1 => om xu.1 xu.2.val)
  -- @realizes \omega(joint measurability)
-- @node: ass:target-weight-integrable
/-- For the [latent instrumental-variable model](hyp:M), a [weight function of covariates
and resistance](hyp:om) satisfies [target-weight integrability](goal) when it is integrable
under the product of the covariate law and Lebesgue measure on the closed unit interval. -/
def TargetWeightIntegrable (om : X → ℝ → ℝ) : Prop :=
  Integrable (Function.uncurry om) ((xLaw M).prod (volume.restrict (Icc (0 : ℝ) 1)))

-- A weight rule ranges over arbitrary structural sample spaces in one fixed universe.
/-- A [reference model](hyp:M) and a [comparison model](hyp:N) describe the [same known world](goal)
when they have [the same outcome domain](step:1), [the same lower endpoint](step:2),
[the same upper endpoint](step:3), [the same covariate dimension](step:4), and
[the same covariate coordinate map, after accounting for equality of dimensions](step:5). -/
def SameKnownWorld {A : Type u} [MeasurableSpace A] (N : LatentIVModel A X Z) : Prop :=
  N.Yset = M.Yset ∧ N.yMin = M.yMin ∧ N.yMax = M.yMax ∧
    N.dX = M.dX ∧ HEq N.covariateCoordinates M.covariateCoordinates
-- @node: ass:target-weight-identifiable
/-- On the [covariate space](hyp:X) and [instrument space](hyp:Z), a [rule assigning a weight
function to each latent model](hyp:omOf) satisfies [target-weight identifiability](goal)
when any two models with the same known world, the structural assumptions, correct known
endpoints, and the same observed-data law yield weights equal almost everywhere under the
product of the first model's covariate law and Lebesgue measure on the unit interval. -/
def TargetWeightIdentifiable
    (omOf : ∀ (A : Type u) [MeasurableSpace A], LatentIVModel A X Z → X → ℝ → ℝ) : Prop :=
  ∀ (A B : Type u) (mA : MeasurableSpace A) (mB : MeasurableSpace B)
    (N : @LatentIVModel A X Z mA _ _ _ _ _) (N' : @LatentIVModel B X Z mB _ _ _ _ _),
    SameKnownWorld N N' → StructuralAssumptions N → OutcomeEndpointsKnown N →
    StructuralAssumptions N' → OutcomeEndpointsKnown N' → observedLaw N = observedLaw N' →
    Function.uncurry (omOf A N) =ᵐ[(xLaw N).prod (volume.restrict (Icc (0 : ℝ) 1))]
      Function.uncurry (omOf B N')
-- @node: ass:pin-15
/-- On the [covariate space](hyp:X) and [instrument space](hyp:Z), the [almost-everywhere
identifiability reading](goal) for a [model-dependent weight rule](hyp:omOf) requires equal
weights almost everywhere whenever two models share the known world and observed-data law
and both satisfy the structural assumptions and known-endpoint condition. -/
def WeightIdentifiableAEReading
    (omOf : ∀ (A : Type u) [MeasurableSpace A], LatentIVModel A X Z → X → ℝ → ℝ) : Prop :=
  TargetWeightIdentifiable omOf
-- @node: ass:sharpness-observed-model
/-- Relative to a [reference latent model](hyp:M), a [proposed joint law of outcome,
treatment, instrument, and covariates](hyp:obs) is [generated by an admissible model](goal)
if some latent model [shares the reference model's known world](step:1),
[satisfies the structural assumptions](step:2), [has the designated outcome endpoints](step:3),
and [generates exactly the proposed observed-data law](step:4). -/
def ObservedLawGenerated (obs : Measure (ℝ × ℝ × Z × X)) : Prop :=
  ∃ (A : Type u) (mA : MeasurableSpace A) (N : @LatentIVModel A X Z mA _ _ _ _ _),
    SameKnownWorld M N ∧ StructuralAssumptions N ∧ OutcomeEndpointsKnown N ∧ observedLaw N = obs
-- @node: def:outcome-endpoints
/-- For an [outcome domain](hyp:Yset), the [outcome endpoint pair](goal) consists of its
infimum followed by its supremum. -/
noncomputable def outcomeEndpoints (Yset : Set ℝ) : ℝ × ℝ := (sInf Yset, sSup Yset)
-- @node: def:mte
/-- For the [latent instrumental-variable model](hyp:M), a [covariate value](hyp:x), and
a [resistance value](hyp:u), the [marginal treatment effect](goal) is the mean treated-minus-untreated
potential outcome under the conditional distribution given those resistance and covariate values. -/
noncomputable def mte (x : X) (u : ℝ) : ℝ :=
  ∫ d, d ∂condDistrib (fun s => M.Y1 s - M.Y0 s)
    (fun s => (M.U s, M.Xv s)) M.law.toMeasure (u, x)
  -- @realizes \text{MTE}(conditional mean of potential-outcome difference)
-- @node: def:target-mte
/-- For the [latent instrumental-variable model](hyp:M) and a [weight function of covariates
and resistance](hyp:om), the [target treatment-effect parameter](goal) integrates the weighted
marginal treatment effect over unit-interval resistance and then over the covariate law. -/
noncomputable def thetaTarget (om : X → ℝ → ℝ) : ℝ :=
  ∫ x, (∫ u in Icc (0 : ℝ) 1, mte M x u * om x u) ∂xLaw M
  -- @realizes \theta_\omega(weighted MTE integral)
/-- On the [covariate space](hyp:X), given a [weight function of covariates and resistance](hyp:om)
and a [candidate measure of resistance, covariates, and an outcome](hyp:pi), the
[weighted outcome component](goal) is the integral of outcome times its covariate- and
resistance-specific weight under that measure. -/
noncomputable def thetaComp (om : X → ℝ → ℝ) (pi : Measure ((ℝ × X) × ℝ)) : ℝ :=
  ∫ a, a.2 * om a.1.2 a.1.1 ∂pi
  -- @realizes \theta_{\omega,w}(candidate-law outcome-weight integral)
-- @node: def:latent-marginals
/-- For the [latent instrumental-variable model](hyp:M) and a [choice of treatment status](hyp:w),
the [latent marginal law](goal) is the joint population distribution of resistance, covariates,
and the potential outcome for that treatment status. -/
noncomputable def latentMarginal (w : Bool) : Measure ((ℝ × X) × ℝ) :=
  M.law.toMeasure.map (fun s => ((M.U s, M.Xv s), potential M w s))
  -- @realizes \pi_w(joint law of U,X,Y(w))
-- @node: def:selection-regions
/-- For a [choice of treatment status](hyp:w) and a [propensity threshold](hyp:p), the
[selection region](goal) is the resistance interval $(0,p]$ for treatment and $(p,1]$
for no treatment. -/
def selRegion (w : Bool) (p : ℝ) : Set ℝ := if w then Ioc 0 p else Ioc p 1
  -- @realizes \mathcal{R}_w(selected resistance intervals)
-- @node: def:canonical-submeasures
/-- For the [latent instrumental-variable model](hyp:M), a [choice of treatment status](hyp:w),
a [covariate value](hyp:x), and a [propensity value](hyp:p), the [observed outcome submeasure](goal)
is obtained by conditioning the outcome–treatment pair on those propensity and covariate values,
restricting to the chosen treatment status, and retaining only the outcome. -/
noncomputable def obsSubmeasure (w : Bool) (x : X) (p : ℝ) : Measure ℝ :=
  ((condDistrib (fun s => (M.Y s, M.W s))
    (fun s => (M.prop (M.Zv s) (M.Xv s), M.Xv s)) M.law.toMeasure (p, x)).restrict
    {a | a.2 = if w then 1 else 0}).map Prod.fst
/-- On the [covariate space](hyp:X), for a [candidate measure of resistance, covariates,
and an outcome](hyp:pi), the [outcome kernel](goal) is a conditional outcome distribution
given resistance and covariates when the measure is finite, and the constant point mass at zero otherwise. -/
noncomputable def outcomeKernel (pi : Measure ((ℝ × X) × ℝ)) : Kernel (ℝ × X) ℝ :=
  if h : IsFiniteMeasure pi then @Measure.condKernel _ _ _ _ _ _ pi h
  else Kernel.const _ (Measure.dirac 0)

-- @node: outcomeKernel_isMarkov
/-- For any candidate measure of resistance, covariates, and an outcome,
[the associated outcome kernel assigns a probability distribution to every resistance–covariate pair](goal). -/
lemma outcomeKernel_isMarkov (pi : Measure ((ℝ × X) × ℝ)) :
    IsMarkovKernel (outcomeKernel pi) := by
  unfold outcomeKernel
  split <;> infer_instance

-- @node: def:canonical-versions
/-- For the [latent instrumental-variable model](hyp:M), a [choice of treatment status](hyp:w),
a [covariate value](hyp:x), and a [propensity threshold](hyp:p), the [canonical outcome submeasure](goal)
integrates the conditional potential-outcome kernel over the resistance selection region
for that status and threshold using Lebesgue measure. -/
noncomputable def canonSubmeasure (w : Bool) (x : X) (p : ℝ) : Measure ℝ :=
  (volume.restrict (selRegion w p)).bind (fun u => outcomeKernel (latentMarginal M w) (u, x))
  -- @realizes H_{w,x}(integrated latent kernel on selected region)
/-- For the [latent instrumental-variable model](hyp:M), a [fixed covariate value](hyp:x0)
such that [covariates equal that value almost surely](hyp:_hX), a [choice of treatment status](hyp:w),
and a [propensity threshold](hyp:p), the [constant-covariate canonical submeasure](goal)
is the canonical outcome submeasure evaluated at that fixed covariate value. -/
noncomputable def canonSubmeasure0 (x0 : X) -- @realizes H_w(no-covariate submeasure at the almost-sure covariate value)
    (_hX : ∀ᵐ s ∂M.law.toMeasure, M.Xv s = x0) (w : Bool) (p : ℝ) :=
  canonSubmeasure M w x0 p


/-- For a [covariate space](hyp:X) and an [instrument space](hyp:Z), the
[observed transport data](goal) collect an outcome domain, a propensity function,
instrument–covariate and covariate measures, and outcome submeasures indexed by treatment
status, covariates, and propensity. -/
structure ObservedTransportData (X Z : Type v) [MeasurableSpace X] [MeasurableSpace Z] where
  Yset : Set ℝ
  prop : Z → X → ℝ
  zx : Measure (Z × X)
  x : Measure X
  H : Bool → X → ℝ → Measure ℝ
/-- For the [latent instrumental-variable model](hyp:M), its [transport data](goal)
consist of its outcome domain, propensity function, joint instrument–covariate law,
covariate law, and canonical outcome submeasures. -/
noncomputable def transportData : ObservedTransportData X Z :=
  ⟨M.Yset, M.prop, zxLaw M, xLaw M, canonSubmeasure M⟩
-- @node: ass:ot-formulation-support
/-- On the [covariate space](hyp:X), an [outcome domain](hyp:Yset) and candidate
[untreated](hyp:pi0) and [treated](hyp:pi1) joint measures satisfy [feasible support](goal)
when each [is a probability measure](step:1) and [assigns zero mass outside unit-interval
resistance and the outcome domain](step:2). -/
def FeasibleSupport (Yset : Set ℝ) (pi0 pi1 : Measure ((ℝ × X) × ℝ)) : Prop :=
  ∀ pi ∈ ({pi0, pi1} : Set (Measure ((ℝ × X) × ℝ))),
    IsProbabilityMeasure pi ∧ pi {a | a.1.1 ∈ Icc (0 : ℝ) 1 ∧ a.2 ∈ Yset}ᶜ = 0
-- @node: ass:ot-formulation-treated-compatibility
/-- Given [observed transport data](hyp:obs), a [candidate treated joint measure](hyp:pi1)
satisfies [treated compatibility](goal) when, for almost every instrument–covariate pair
and every measurable outcome set, integrating its conditional outcome probability over
resistance in $(0,p]$ equals the observed treated submeasure at that pair's propensity. -/
def TreatedCompatible (obs : ObservedTransportData X Z) (pi1 : Measure ((ℝ × X) × ℝ)) : Prop :=
  ∀ᵐ zx ∂obs.zx, ∀ A : Set ℝ, MeasurableSet A →
    ∫⁻ u in Ioc 0 (obs.prop zx.1 zx.2), outcomeKernel pi1 (u, zx.2) A
      = obs.H true zx.2 (obs.prop zx.1 zx.2) A
-- @node: ass:ot-formulation-untreated-compatibility
/-- Given [observed transport data](hyp:obs), a [candidate untreated joint measure](hyp:pi0)
satisfies [untreated compatibility](goal) when, for almost every instrument–covariate pair
and every measurable outcome set, integrating its conditional outcome probability over
resistance in $(p,1]$ equals the observed untreated submeasure at that pair's propensity. -/
def UntreatedCompatible (obs : ObservedTransportData X Z) (pi0 : Measure ((ℝ × X) × ℝ)) : Prop :=
  ∀ᵐ zx ∂obs.zx, ∀ A : Set ℝ, MeasurableSet A →
    ∫⁻ u in Ioc (obs.prop zx.1 zx.2) 1, outcomeKernel pi0 (u, zx.2) A
      = obs.H false zx.2 (obs.prop zx.1 zx.2) A
/-- If [a candidate joint measure satisfies treated compatibility with the observed transport
data](hyp:h), then [for almost every instrument–covariate pair and every measurable outcome
set, the integral of its real-valued conditional outcome probabilities over resistance in
$(0,p]$ equals the real-valued observed treated submeasure at that pair's propensity](goal). -/
-- @node: treated_compatible_toReal
lemma treated_compatible_toReal (obs : ObservedTransportData X Z)
    (pi : Measure ((ℝ × X) × ℝ)) (h : TreatedCompatible obs pi) :
    ∀ᵐ zx ∂obs.zx, ∀ B : Set ℝ, MeasurableSet B →
      (∫ u in Ioc 0 (obs.prop zx.1 zx.2), (outcomeKernel pi (u, zx.2) B).toReal) =
        (obs.H true zx.2 (obs.prop zx.1 zx.2) B).toReal := by
  letI := outcomeKernel_isMarkov pi
  filter_upwards [h] with zx hz
  intro B hB
  have hm : Measurable (fun u => outcomeKernel pi (u, zx.2) B) := by
    exact ((outcomeKernel pi).measurable_coe hB).comp
      (measurable_id.prodMk measurable_const)
  rw [integral_toReal hm.aemeasurable
    (Filter.Eventually.of_forall fun u => measure_lt_top _ B), hz B hB]

/-- If [for almost every instrument–covariate pair and every measurable outcome set, the
integral of a candidate measure's real-valued conditional outcome probabilities over
resistance in $(0,p]$ equals the real-valued canonical treated submeasure](hyp:h), then
[the candidate measure satisfies treated compatibility with the model's transport data](goal). -/
-- @node: treated_compatible_of_toReal
lemma treated_compatible_of_toReal (pi : Measure ((ℝ × X) × ℝ))
    (h : ∀ᵐ zx ∂zxLaw M, ∀ B : Set ℝ, MeasurableSet B →
      (∫ u in Ioc 0 (M.prop zx.1 zx.2), (outcomeKernel pi (u, zx.2) B).toReal) =
        (canonSubmeasure M true zx.2 (M.prop zx.1 zx.2) B).toReal) :
    TreatedCompatible (transportData M) pi := by
  letI := outcomeKernel_isMarkov pi
  letI := outcomeKernel_isMarkov (latentMarginal M true)
  filter_upwards [h] with zx hz
  intro B hB
  have hm : Measurable (fun u => outcomeKernel pi (u, zx.2) B) := by
    exact ((outcomeKernel pi).measurable_coe hB).comp
      (measurable_id.prodMk measurable_const)
  have hfin : (∫⁻ u in Ioc 0 (M.prop zx.1 zx.2),
      outcomeKernel pi (u, zx.2) B) ≠ ⊤ := by
    apply ne_of_lt
    calc
      _ ≤ ∫⁻ u in Ioc 0 (M.prop zx.1 zx.2), (1 : ℝ≥0∞) :=
        lintegral_mono fun u => prob_le_one
      _ < ⊤ := by simp
  have hcanon : canonSubmeasure M true zx.2 (M.prop zx.1 zx.2) B ≠ ⊤ := by
    unfold canonSubmeasure
    rw [Measure.bind_apply hB (by fun_prop)]
    apply ne_of_lt
    calc
      _ ≤ ∫⁻ u in selRegion true (M.prop zx.1 zx.2), (1 : ℝ≥0∞) :=
        lintegral_mono fun u => prob_le_one
      _ < ⊤ := by simp [selRegion]
  apply (ENNReal.toReal_eq_toReal_iff' hfin hcanon).mp
  rw [← integral_toReal hm.aemeasurable
    (Filter.Eventually.of_forall fun u => measure_lt_top _ B)]
  exact hz B hB

-- @node: ass:ot-formulation-uniform-covariate-marginal
/-- Given [observed transport data](hyp:obs) and candidate [untreated](hyp:pi0) and
[treated](hyp:pi1) joint measures, the [uniform-resistance covariate-marginal condition](goal)
requires that [the untreated resistance–covariate marginal](step:1) and [the treated
resistance–covariate marginal](step:2) both equal the product of the uniform unit-interval
law and the observed covariate law. -/
def UniformCovariateMarginal (obs : ObservedTransportData X Z)
    (pi0 pi1 : Measure ((ℝ × X) × ℝ)) : Prop :=
  pi0.fst = Causalean.Stat.unifOI.prod obs.x ∧ pi1.fst = Causalean.Stat.unifOI.prod obs.x
-- @node: def:gamma
/-- Given [observed transport data](hyp:obs), candidate [untreated](hyp:pi0) and
[treated](hyp:pi1) joint measures form a [feasible pair](goal) when they satisfy
[probability and support restrictions](step:1), [treated compatibility](step:2),
[untreated compatibility](step:3), and [the common product marginal of uniform resistance
and observed covariates](step:4). -/
structure IsFeasiblePair (obs : ObservedTransportData X Z)
    (pi0 pi1 : Measure ((ℝ × X) × ℝ)) : Prop where
  support : FeasibleSupport obs.Yset pi0 pi1
  treated : TreatedCompatible obs pi1
  untreated : UntreatedCompatible obs pi0
  marginal : UniformCovariateMarginal obs pi0 pi1
  -- @realizes \Gamma(feasible pair class)
/-- Given [observed transport data](hyp:obs), a [candidate treated joint measure](hyp:pi)
is [feasible for the treated state](goal) if it [is a probability measure](step:1),
[assigns zero mass outside unit-interval resistance and the observed outcome domain](step:2),
[has resistance–covariate marginal equal to uniform resistance times the observed covariate
law](step:3), and [satisfies treated compatibility](step:4). -/
def IsFeasibleTreated (obs : ObservedTransportData X Z) (pi : Measure ((ℝ × X) × ℝ)) : Prop :=
  IsProbabilityMeasure pi ∧ pi {a | a.1.1 ∈ Icc (0 : ℝ) 1 ∧ a.2 ∈ obs.Yset}ᶜ = 0 ∧
  pi.fst = Causalean.Stat.unifOI.prod obs.x ∧ TreatedCompatible obs pi
  -- @realizes \Gamma_1(treated feasible class)
-- @node: ass:pin-29
/-- Given [observed transport data](hyp:obs) and candidate [untreated](hyp:pi0) and
[treated](hyp:pi1) joint measures, the [both-states reading of the constraints](goal)
requires that these measures form a feasible pair. -/
def ConstraintsBothStatesReading (obs : ObservedTransportData X Z)
    (pi0 pi1 : Measure ((ℝ × X) × ℝ)) : Prop := IsFeasiblePair obs pi0 pi1
-- @node: def:ot-formulation
/-- For [observed transport data](hyp:obs) and a [weight function of covariates and
resistance](hyp:om), the [constrained transport value set](goal) consists of values
obtained from two joint measures that [form a feasible pair](step:1), with each value
[equal to their weighted treated outcome component minus their weighted untreated outcome
component](step:2). -/
noncomputable def ccotValueSet (obs : ObservedTransportData X Z) (om : X → ℝ → ℝ) : Set ℝ :=
  {v | ∃ pi0 pi1, IsFeasiblePair obs pi0 pi1 ∧ v = thetaComp om pi1 - thetaComp om pi0}
/-- For [observed transport data](hyp:obs) and a [weight function of covariates and
resistance](hyp:om), the [treated value set](goal) consists of values for which a joint
measure [is feasible for the treated state](step:1) and [has weighted outcome component
equal to the value](step:2). -/
noncomputable def treatedValueSet (obs : ObservedTransportData X Z) (om : X → ℝ → ℝ) : Set ℝ :=
  {v | ∃ pi, IsFeasibleTreated obs pi ∧ v = thetaComp om pi}
/-- For [observed transport data](hyp:obs) and a [weight function of covariates and
resistance](hyp:om), the [lower treated component bound](goal) is the infimum of the
attainable treated weighted outcome values. -/
noncomputable def thetaLower1 (obs : ObservedTransportData X Z) (om : X → ℝ → ℝ) : ℝ :=
  sInf (treatedValueSet obs om)
  -- @realizes \underline{\theta}_{\omega,1}(infimum of treated attainable values)
/-- For [observed transport data](hyp:obs) and a [weight function of covariates and
resistance](hyp:om), the [upper treated component bound](goal) is the supremum of the
attainable treated weighted outcome values. -/
noncomputable def thetaUpper1 (obs : ObservedTransportData X Z) (om : X → ℝ → ℝ) : ℝ :=
  sSup (treatedValueSet obs om)
  -- @realizes \overline{\theta}_{\omega,1}(supremum of treated attainable values)
/-- For [observed transport data](hyp:obs) and a [weight function of covariates and
resistance](hyp:om), the [untreated value set](goal) consists of values represented by a
joint measure that [is a probability measure](step:1), [assigns zero mass outside
unit-interval resistance and the observed outcome domain](step:2), [has marginal equal to
uniform resistance times the observed covariate law](step:3), [satisfies untreated
compatibility](step:4), and [has weighted outcome component equal to the value](step:5). -/
noncomputable def untreatedValueSet (obs : ObservedTransportData X Z) (om : X → ℝ → ℝ) : Set ℝ :=
  {v | ∃ pi : Measure ((ℝ × X) × ℝ),
    IsProbabilityMeasure pi ∧ pi {a | a.1.1 ∈ Icc (0:ℝ) 1 ∧ a.2 ∈ obs.Yset}ᶜ = 0 ∧
    pi.fst = Causalean.Stat.unifOI.prod obs.x ∧ UntreatedCompatible obs pi ∧ v = thetaComp om pi}
/-- For [observed transport data](hyp:obs) and a [weight function of covariates and
resistance](hyp:om), the [lower untreated component bound](goal) is the infimum of the
attainable untreated weighted outcome values. -/
noncomputable def thetaLower0 (obs : ObservedTransportData X Z) (om : X → ℝ → ℝ) := sInf (untreatedValueSet obs om)
/-- For [observed transport data](hyp:obs) and a [weight function of covariates and
resistance](hyp:om), the [upper untreated component bound](goal) is the supremum of the
attainable untreated weighted outcome values. -/
noncomputable def thetaUpper0 (obs : ObservedTransportData X Z) (om : X → ℝ → ℝ) := sSup (untreatedValueSet obs om)
/-- For [observed transport data](hyp:obs) and a [weight function of covariates and
resistance](hyp:om), the [sharp target interval](goal) is the closed interval from the lower
treated bound minus the upper untreated bound to the upper treated bound minus the lower
untreated bound. -/
noncomputable def sharpTargetInterval (obs : ObservedTransportData X Z) (om : X → ℝ → ℝ) :=
  Icc (thetaLower1 obs om - thetaUpper0 obs om) (thetaUpper1 obs om - thetaLower0 obs om)
-- @node: def:ot-formulation-1
/-- For [observed transport data](hyp:obs) and a [weight function of covariates and
resistance](hyp:om), the [treated optimization result](goal) pairs the infimum of attainable
treated weighted outcome values with the set of joint measures that are feasible for the
treated state and minimize the weighted outcome component among all such measures. -/
noncomputable def treatedOptimization (obs : ObservedTransportData X Z) (om : X → ℝ → ℝ) :=
  (sInf (treatedValueSet obs om),
    {pi : Measure ((ℝ × X) × ℝ) | IsFeasibleTreated obs pi ∧
      ∀ pi', IsFeasibleTreated obs pi' → thetaComp om pi ≤ thetaComp om pi'})
-- @node: def:component-bounds
/-- For [observed transport data](hyp:obs) and a [weight function of covariates and
resistance](hyp:om), the [collection of component bounds](goal) records the lower and upper
untreated bounds, the lower and upper treated bounds, the treated-minus-untreated endpoint
bounds, and the resulting closed target interval. -/
noncomputable def componentBounds (obs : ObservedTransportData X Z) (om : X → ℝ → ℝ) :=
  ((thetaLower0 obs om, thetaUpper0 obs om), (thetaLower1 obs om, thetaUpper1 obs om),
    (thetaLower1 obs om - thetaUpper0 obs om, thetaUpper1 obs om - thetaLower0 obs om),
    sharpTargetInterval obs om)
/-- For the [latent instrumental-variable model](hyp:M) and a [choice of treatment
status](hyp:w), the [latent outcome kernel](goal) is the conditional outcome kernel given
resistance and covariates obtained from the latent marginal law for that status. -/
noncomputable def latentOutcomeKernel (w : Bool) := outcomeKernel (latentMarginal M w) -- @realizes K_{w,x}(one regular conditional outcome kernel of the latent law)
-- @node: uniform_resistance_joint_law
/-- If [resistance is conditionally uniform on the unit interval given covariates](hyp:h),
then [the joint resistance–covariate law equals the product of the uniform unit-interval
law and the covariate law](goal). -/
lemma uniform_resistance_joint_law (h : UniformResistance M) :
    M.law.toMeasure.map (fun s => (M.U s, M.Xv s)) =
      Causalean.Stat.unifOI.prod (xLaw M) := by
  haveI : IsProbabilityMeasure (xLaw M) :=
    Measure.isProbabilityMeasure_map M.measX.aemeasurable
  have hk : condDistrib M.U M.Xv M.law.toMeasure =ᵐ[xLaw M]
      Kernel.const X Causalean.Stat.unifOI := h
  have hj : M.law.toMeasure.map (fun s => (M.Xv s, M.U s)) =
      (xLaw M).prod Causalean.Stat.unifOI := by
    rw [← compProd_map_condDistrib M.measU.aemeasurable]
    change (xLaw M) ⊗ₘ condDistrib M.U M.Xv M.law.toMeasure = _
    rw [Measure.compProd_congr hk, Measure.compProd_const]
  have hm := congrArg (fun μ : Measure (X × ℝ) => μ.map Prod.swap) hj
  simpa only [Measure.map_map measurable_swap (M.measX.prodMk M.measU),
    Function.comp_def, Prod.swap_prod_mk, Measure.prod_swap] using hm

-- @node: latentMarginal_uniform_fst
/-- If [resistance is conditionally uniform on the unit interval given covariates](hyp:h),
then [for either treatment status, the resistance–covariate marginal of the latent outcome
law equals the product of the uniform unit-interval law and the covariate law](goal). -/
lemma latentMarginal_uniform_fst (h : UniformResistance M) (w : Bool) :
    (latentMarginal M w).fst = Causalean.Stat.unifOI.prod (xLaw M) := by
  have hp : Measurable (potential M w) := by
    cases w
    · exact M.measY0
    · exact M.measY1
  rw [latentMarginal, Measure.fst_map_prodMk hp]
  exact uniform_resistance_joint_law M h

-- @node: latentOutcomeKernel_supported
/-- Under [the structural assumptions](hyp:h), [for either treatment status and almost
every resistance–covariate pair under the product of uniform resistance and the covariate
law, the latent outcome kernel is a probability measure assigning zero mass outside the
outcome domain](goal). -/
lemma latentOutcomeKernel_supported (h : StructuralAssumptions M) (w : Bool) :
    ∀ᵐ ux ∂Causalean.Stat.unifOI.prod (xLaw M),
      IsProbabilityMeasure (latentOutcomeKernel M w ux) ∧ -- @realizes K_{w,x}(probability measures for almost every (u,x))
      latentOutcomeKernel M w ux M.Ysetᶜ = 0 := by -- @realizes K_{w,x}(supported on the outcome domain for almost every (u,x))
  have hp : Measurable (potential M w) := by
    cases w <;> simp only [potential, Bool.false_eq_true, ↓reduceIte]
    · exact M.measY0
    · exact M.measY1
  let pi := latentMarginal M w
  have hm : Measurable (fun s => ((M.U s, M.Xv s), potential M w s)) := by
    exact (M.measU.prodMk M.measX).prodMk hp
  haveI : IsProbabilityMeasure pi := by
    dsimp [pi, latentMarginal]
    exact Measure.isProbabilityMeasure_map hm.aemeasurable
  have hs : ∀ᵐ s ∂M.law.toMeasure, potential M w s ∈ M.Yset := by
    cases w
    · exact h.1.1
    · exact h.1.2
  have hy : MeasurableSet M.Yset := h.2.2.2.2.2.2.1.isClosed.measurableSet
  have hsPi : ∀ᵐ a ∂pi, a.2 ∈ M.Yset :=
    (ae_map_iff hm.aemeasurable (measurable_snd hy)).mpr hs
  rw [← Measure.disintegrate pi pi.condKernel] at hsPi
  have hsK := Measure.ae_ae_of_ae_compProd hsPi
  rw [latentMarginal_uniform_fst M h.2.2.2.2.1 w] at hsK
  filter_upwards [hsK] with ux hux
  have heq : latentOutcomeKernel M w ux = pi.condKernel ux := by
    have hf : IsFiniteMeasure (latentMarginal M w) := inferInstanceAs (IsFiniteMeasure pi)
    simp [latentOutcomeKernel, outcomeKernel, hf, pi]
  rw [heq]
  exact ⟨inferInstance, ae_iff.mp hux⟩
-- @node: canonical_submeasure_supported
/-- Under [the structural assumptions](hyp:h), [for either treatment status and almost
every covariate value, every propensity threshold in the closed unit interval gives a
canonical outcome submeasure assigning zero mass outside the outcome domain](goal). -/
lemma canonical_submeasure_supported (h : StructuralAssumptions M) (w : Bool) :
    ∀ᵐ x ∂xLaw M, ∀ p ∈ Icc (0 : ℝ) 1, canonSubmeasure M w x p M.Ysetᶜ = 0 := by
  haveI : IsProbabilityMeasure (xLaw M) :=
    Measure.isProbabilityMeasure_map M.measX.aemeasurable
  have hs := latentOutcomeKernel_supported M h w
  have hswap : ∀ᵐ xu ∂(xLaw M).prod Causalean.Stat.unifOI,
      latentOutcomeKernel M w (xu.2, xu.1) M.Ysetᶜ = 0 := by
    have hm : ∀ᵐ ux ∂((xLaw M).prod Causalean.Stat.unifOI).map Prod.swap,
        latentOutcomeKernel M w ux M.Ysetᶜ = 0 := by
      rw [Measure.prod_swap]
      exact hs.mono fun _ ha => ha.2
    exact ae_of_ae_map measurable_swap.aemeasurable hm
  have hx := Measure.ae_ae_of_ae_prod hswap
  have hy : MeasurableSet M.Ysetᶜ := h.2.2.2.2.2.2.1.isClosed.measurableSet.compl
  filter_upwards [hx] with x hx
  intro p hp
  have hu : ∀ᵐ u ∂volume.restrict (Icc (0 : ℝ) 1),
      latentOutcomeKernel M w (u, x) M.Ysetᶜ = 0 := by
    simpa only [Causalean.Stat.unifOI, restrict_Ioo_eq_restrict_Icc] using hx
  have hsub : selRegion w p ⊆ Icc (0 : ℝ) 1 := by
    cases w
    · exact fun u hu => ⟨hp.1.trans hu.1.le, hu.2⟩
    · exact fun u hu => ⟨hu.1.le, hu.2.trans hp.2⟩
  have hK : Measurable (fun u : ℝ => latentOutcomeKernel M w (u, x)) := by
    fun_prop
  change ((volume.restrict (selRegion w p)).bind
    (fun u => latentOutcomeKernel M w (u, x))) M.Ysetᶜ = 0
  rw [Measure.bind_apply hy hK.aemeasurable]
  have hEval : Measurable (fun u => latentOutcomeKernel M w (u, x) M.Ysetᶜ) := by
    exact (Measure.measurable_coe hy).comp hK
  exact (lintegral_eq_zero_iff hEval).mpr (hu.filter_mono
    (ae_mono (Measure.restrict_mono_set volume hsub)))
-- @node: canonSubmeasure0_supported
/-- Under [the structural assumptions](hyp:h), if [covariates almost surely equal a fixed
value](hyp:hX), then [for either treatment status and every propensity threshold in the
closed unit interval, the constant-covariate canonical submeasure assigns zero mass
outside the outcome domain](goal). -/
lemma canonSubmeasure0_supported (h : StructuralAssumptions M) (x0 : X) -- @realizes H_w(canonical no-covariate submeasures are supported on the outcome domain)
    (hX : ∀ᵐ s ∂M.law.toMeasure, M.Xv s = x0) (w : Bool) :
    ∀ p ∈ Icc (0 : ℝ) 1, canonSubmeasure0 M x0 hX w p M.Ysetᶜ = 0 := by
  have hxLaw : xLaw M = Measure.dirac x0 := by
    rw [xLaw, Measure.map_congr hX, Measure.map_const]
    simp
  have hs := canonical_submeasure_supported M h w
  rw [hxLaw, ae_dirac_eq] at hs
  exact hs

-- @node: observedPropensity_range
/-- [The observed propensity lies in the closed unit interval for every individual](goal). -/
lemma observedPropensity_range : -- @realizes P(propensity random variable takes values in [0,1])
    ∀ s, observedPropensity M s ∈ Icc (0 : ℝ) 1 := by
  intro s
  exact M.rangeProp (M.Zv s) (M.Xv s)

-- @node: selRegion_subset
/-- If [the propensity threshold lies in the closed unit interval](hyp:hp), then [the
resistance selection region for either treatment status is contained in the closed unit
interval](goal). -/
lemma selRegion_subset (w : Bool) (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) : selRegion w p ⊆ Icc (0 : ℝ) 1 := by
  cases w with
  | false =>
    intro u hu
    exact ⟨hp.1.trans hu.1.le, hu.2⟩
  | true =>
    intro u hu
    exact ⟨hu.1.le, hu.2.trans hp.2⟩
  -- @realizes \mathcal{R}_w(selected resistance region lies in [0,1])

-- @node: def:policy-map
/-- Given a [policy transformation of propensity](hyp:phi), a [baseline propensity
function](hyp:prop), an [instrument value](hyp:z), and a [covariate value](hyp:x), the
[policy propensity](goal) applies that transformation to the baseline propensity at those
instrument and covariate values. -/
def policyProp (phi : Z → X → ℝ → ℝ) (prop : Z → X → ℝ) (z : Z) (x : X) := phi z x (prop z x)
  -- @realizes q(policy propensity formula)
/-- On the [instrument space](hyp:Z) and [covariate space](hyp:X), a [transformation of
propensity](hyp:phi) is an [admissible policy map](goal) if it [is jointly measurable when
the input propensity is restricted to the closed unit interval](step:1) and [maps every
unit-interval propensity into the closed unit interval at every instrument–covariate
pair](step:2). -/
def IsPolicyMap (phi : Z → X → ℝ → ℝ) : Prop :=
  Measurable (fun a : Z × X × Icc (0 : ℝ) 1 => phi a.1 a.2.1 a.2.2) ∧ -- @realizes \phi(joint measurability on the stated [0,1] propensity domain)
  ∀ z x p, p ∈ Icc (0 : ℝ) 1 → phi z x p ∈ Icc (0 : ℝ) 1 -- @realizes \phi(policy values in [0,1] on the stated domain)
/-- For the [latent instrumental-variable model](hyp:M), a [policy propensity
function](hyp:q), and an [individual](hyp:s), the [policy treatment](goal) equals one when
the individual's resistance does not exceed the policy propensity at their instrument
and covariates, and zero otherwise. -/
noncomputable def policyTreatment (q : Z → X → ℝ) (s : Ω) : ℝ :=
  if M.U s ≤ q (M.Zv s) (M.Xv s) then 1 else 0
  -- @realizes W^q(policy threshold treatment)
/-- For the [latent instrumental-variable model](hyp:M), a [policy propensity
function](hyp:q), and an [individual](hyp:s), the [policy outcome](goal) equals policy
treatment times the treated potential outcome plus one minus policy treatment times the
untreated potential outcome. -/
noncomputable def policyOutcome (q : Z → X → ℝ) (s : Ω) : ℝ :=
  policyTreatment M q s * M.Y1 s + (1 - policyTreatment M q s) * M.Y0 s
  -- @realizes Y^q(policy outcome)
-- @node: def:estimation-weight
/-- For the [latent instrumental-variable model](hyp:M), a [policy propensity
function](hyp:q), a [covariate value](hyp:x), and a [resistance value](hyp:u), the
[policy weight](goal) averages the difference between policy and baseline threshold
treatment indicators over the conditional instrument distribution at those covariates. -/
noncomputable def policyWeight (q : Z → X → ℝ) (x : X) (u : ℝ) : ℝ :=
  ∫ z, ((if u ≤ q z x then 1 else 0) - (if u ≤ M.prop z x then 1 else 0) : ℝ) ∂M.instKernel x
-- @node: ass:phi-smooth-differentiable
/-- On the [instrument space](hyp:Z) and [covariate space](hyp:X), a [policy
transformation](hyp:phi) and a [proposed propensity derivative](hyp:dphi) satisfy
[policy differentiability](goal) if, at every instrument–covariate pair and every
unit-interval propensity, the transformation has the proposed derivative with respect to
propensity within the closed unit interval, including its endpoints. -/
def PolicyDifferentiable (phi dphi : Z → X → ℝ → ℝ) : Prop :=
  ∀ z x p, p ∈ Icc (0 : ℝ) 1 → HasDerivWithinAt (phi z x) (dphi z x p) (Icc 0 1) p
-- @node: ass:phi-smooth-derivative
/-- On the [instrument space](hyp:Z) and [covariate space](hyp:X), a [policy derivative
function](hyp:dphi) satisfies [uniform boundedness and Lipschitz continuity](goal) if
there exist constants C and L such that [C is nonnegative](step:1), [L is
nonnegative](step:2), and [at every instrument–covariate pair and any two unit-interval
propensities, the derivative's absolute value is at most C and its change is at most L
times the distance between the propensities](step:3). -/
def PolicyDerivativeBoundedLipschitz (dphi : Z → X → ℝ → ℝ) : Prop :=
  ∃ C L : ℝ, 0 ≤ C ∧ 0 ≤ L ∧ ∀ z x p p', p ∈ Icc (0 : ℝ) 1 → p' ∈ Icc (0 : ℝ) 1 →
    |dphi z x p| ≤ C ∧ |dphi z x p - dphi z x p'| ≤ L * |p - p'|
-- @node: ass:pin-17
/-- On the [instrument space](hyp:Z) and [covariate space](hyp:X), the [endpoint-inclusive
differentiability reading](goal) for a [policy transformation](hyp:phi) and a [proposed
propensity derivative](hyp:dphi) requires that the transformation have that derivative
within the closed unit interval at every propensity, including the endpoints. -/
def PolicyDifferentiableEndpointReading (phi dphi : Z → X → ℝ → ℝ) : Prop := PolicyDifferentiable phi dphi
-- @node: ass:pin-18
/-- On the [instrument space](hyp:Z) and [covariate space](hyp:X), the [common-constants
reading](goal) for a [policy derivative function](hyp:dphi) requires uniform absolute
boundedness and Lipschitz continuity in unit-interval propensity, with nonnegative
constants shared by all instrument–covariate pairs. -/
def PolicyDerivativeConstantsReading (dphi : Z → X → ℝ → ℝ) : Prop := PolicyDerivativeBoundedLipschitz dphi
-- @node: policyTreatment_range
/-- [For any policy propensity function and every individual, policy treatment takes
one of the two values zero and one](goal). -/
lemma policyTreatment_range (q : Z → X → ℝ) (s : Ω) :
    policyTreatment M q s ∈ treatmentDomain := by
  unfold policyTreatment
  split <;> simp [treatmentDomain]
  -- @realizes W^q(binary policy-treatment range)

end Papers.TbsPrteOptimalTransport
