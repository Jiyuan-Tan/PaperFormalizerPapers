module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousTreatmentResidual
public import Papers.TbsPrteOptimalTransport.Helpers.DMLTailScoreConvergence
/-! Continuous terminal-score moments and convergence.
The terminal score uses only propensity, level probabilities and the terminal
weight. A coordinate projection reuses the terminal-score argument independently
of the outcome law; its unused success regression is fixed at zero. -/
@[expose] public section
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]

-- This is a carrier for shared terminal coordinates, not a binary-outcome model.
-- @node: continuousTailCoordinates
/-- For [a level structure](hyp:L) and [continuous-outcome nuisance functions on that structure](hyp:e),
[the terminal-coordinate embedding into the binary nuisance carrier](goal) retains propensity,
level probabilities, assignment probabilities, band probabilities, shares and weights, and sets the unused success regression to zero. -/
def continuousTailCoordinates (L : LevelData Z X) (e : NuisanceCont L) :
    NuisanceBin L :=
  ⟨e.prop, e.pLev, fun _ _ => 0, e.piLev, e.tauLev, e.share,
    e.gammaFull, e.gamma, e.gammaTail⟩

variable (M : LatentIVModel Ω X Z)

-- @node: continuousTailCoordinates_admissible
/-- If [the continuous-outcome nuisance functions are admissible](hyp:he), then
[their terminal-coordinate embedding is admissible in the binary nuisance carrier](goal). -/
lemma continuousTailCoordinates_admissible (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e) :
    BinAdmissible M L (continuousTailCoordinates L e) := by
  rcases he with ⟨hp, hpm, hl, hlm, hpi, hpim, ht, htm, hs, hsm,
    hf, hfm, hg, hgm, htail, htailm, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsum⟩
  refine ⟨hp, hpm, ?_, ?_, ?_, ?_, hs, hsm, hsum, hf, hfm, htail, htailm⟩
  · intro i
    filter_upwards [hl i, hpi i] with x hx hy
    exact ⟨hx, ⟨le_rfl, zero_le_one⟩, hy⟩
  · intro i
    exact ⟨hlm i, by fun_prop, hpim i⟩
  · intro a
    filter_upwards [ht a, hg a] with x hx hy
    exact ⟨hx, hy⟩
  · intro a
    exact ⟨htm a, hgm a⟩

-- The actual score is unchanged by the projection, pointwise.
-- @node: commonTailScore_continuousTailCoordinates
/-- [Embedding continuous-outcome nuisance functions in the binary carrier leaves the terminal score unchanged at every observation](goal). -/
lemma commonTailScore_continuousTailCoordinates (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e : NuisanceCont L) (o : Obs X Z) :
    commonTailScore M phi dphi L (continuousTailCoordinates L e).prop
      (continuousTailCoordinates L e).pLev (continuousTailCoordinates L e).piLev
      (continuousTailCoordinates L e).gammaTail o =
    commonTailScore M phi dphi L e.prop e.pLev e.piLev e.gammaTail o := rfl

-- @node: fitted_continuous_commonTailScore_memLp
/-- For [a valid policy](hyp:hphi) [with the specified derivative](hyp:hd) and
[a bounded, Lipschitz derivative](hyp:hDerivative), if [the continuous nuisance functions are admissible](hyp:he),
[the clipping threshold is positive](hyp:hc), and [all positive-level assignment probabilities exceed that threshold almost everywhere](hyp:hclip), then
[the fitted terminal score has a finite second moment under the observation law](goal). -/
lemma fitted_continuous_commonTailScore_memLp (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) :
    MemLp (commonTailScore M phi dphi L e.prop e.pLev e.piLev e.gammaTail)
      2 (observationLaw M) := by
  exact fitted_commonTailScore_memLp M phi dphi hphi hd hDerivative L
    (continuousTailCoordinates L e) (continuousTailCoordinates_admissible M L e he)
    c hc hclip

-- @node: nuisanceRates_continuous_commonTailScore_sq_tendsto_probability_zero
/-- For [a valid policy](hyp:hphi) [with the specified derivative](hyp:hd) and
[a bounded, Lipschitz derivative](hyp:hDerivative), suppose [the reference nuisances are admissible](hyp:he0),
[every fitted nuisance vector is admissible](hyp:heh), [the clipping threshold is positive](hyp:hc),
and [reference and fitted positive-level assignment probabilities exceed it almost everywhere](hyp:hclip).
If [propensities](hyp:hrp), [level probabilities](hyp:hrlev), [level assignment probabilities](hyp:hrpi),
and [terminal weights](hyp:hrg) satisfy the finite-coordinate nuisance rate conditions, then
[the population mean squared difference between fitted and reference terminal scores converges in probability to zero along even sample sizes](goal). -/
lemma nuisanceRates_continuous_commonTailScore_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrg : FiniteNuisanceRates M μ (fun n a (_ : Unit) => (eh n a).gammaTail)
      (fun _ => e0.gammaTail)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o,
        (commonTailScore M phi dphi L (eh (2*(n+1)) a).prop
            (eh (2*(n+1)) a).pLev (eh (2*(n+1)) a).piLev
            (eh (2*(n+1)) a).gammaTail o -
          commonTailScore M phi dphi L e0.prop e0.pLev e0.piLev e0.gammaTail o)^2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  exact nuisanceRates_commonTailScore_sq_tendsto_probability_zero M μ phi dphi hphi hd hDerivative L
    (continuousTailCoordinates L e0) (fun n a => continuousTailCoordinates L (eh n a))
    (continuousTailCoordinates_admissible M L e0 he0)
    (fun n a => continuousTailCoordinates_admissible M L (eh n a) (heh n a))
    c hc hclip hrp hrlev hrpi hrg

-- @node: nuisanceRates_continuous_commonTailScore_l2_tendsto_probability_zero
/-- For [a valid policy](hyp:hphi) [with the specified derivative](hyp:hd) and
[a bounded, Lipschitz derivative](hyp:hDerivative), assume [admissible reference nuisances](hyp:he0),
[admissible fitted nuisances at every sample size](hyp:heh), [a positive clipping threshold](hyp:hc),
and [reference and fitted positive-level assignment probabilities bounded below by that threshold almost everywhere](hyp:hclip).
If [propensities](hyp:hrp), [level probabilities](hyp:hrlev), [level assignment probabilities](hyp:hrpi),
and [terminal weights](hyp:hrg) satisfy the finite-coordinate nuisance rate conditions, then
[the population L2 distance between fitted and reference terminal scores converges in probability to zero along even sample sizes](goal). -/
lemma nuisanceRates_continuous_commonTailScore_l2_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrg : FiniteNuisanceRates M μ (fun n a (_ : Unit) => (eh n a).gammaTail)
      (fun _ => e0.gammaTail)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt (∫ o,
        (commonTailScore M phi dphi L (eh (2*(n+1)) a).prop
            (eh (2*(n+1)) a).pLev (eh (2*(n+1)) a).piLev
            (eh (2*(n+1)) a).gammaTail o -
          commonTailScore M phi dphi L e0.prop e0.pLev e0.piLev e0.gammaTail o)^2
        ∂observationLaw M)) atTop (fun _ _ => 0) := by
  exact nuisanceRates_commonTailScore_l2_tendsto_probability_zero M μ phi dphi hphi hd hDerivative L
    (continuousTailCoordinates L e0) (fun n a => continuousTailCoordinates L (eh n a))
    (continuousTailCoordinates_admissible M L e0 he0)
    (fun n a => continuousTailCoordinates_admissible M L (eh n a) (heh n a))
    c hc hclip hrp hrlev hrpi hrg

end Papers.TbsPrteOptimalTransport
