module
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVSetup
public import Papers.TsAdaptiveEstimationInference.Helpers.IterBias
/-! Fixed-population-center iterative RDIV processes and the two disclosed
Foster–Syrgkanis concentration inputs. The version convention contains no bound.
The cited inputs contain only conditional fitting concentration; radius inflation,
confidence conversion, sample transport, finite unions and recursion remain local. -/
@[expose] public section
set_option linter.unusedVariables false
set_option linter.style.longLine false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory
open scoped ENNReal
variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]
  (V : IVWorld 𝒲 𝒳 𝒵)

/-- In [the instrumental-variable model](hyp:V), [the fixed-center loss](goal)
for [reference measure](hyp:mu), [conditional density](hyp:g), [penalty](hyp:lam),
[iteration index](hyp:j), [candidate structural function](hyp:h), and
[observation](hyp:w) is the squared outcome residual under the density-induced
operator plus the penalty times the squared distance from the previous
population iterate, evaluated at the observation's covariate. -/
noncomputable def iterRdivFixedCenterLoss (mu : Measure 𝒳)
    (g : 𝒳 → 𝒵 → ℝ) (lam : ℝ) (j : ℕ) (h : V.Hbar.toSubmodule)
    (w : 𝒲) : ℝ :=
  (V.Y w - densityOperator mu g (primalVersion V h) (V.zOf w)) ^ 2 +
    lam * (primalVersion V h (V.xOf w) -
      primalVersion V (populationIterate V lam (j - 1)) (V.xOf w)) ^ 2

/-- For [the instrumental-variable model](hyp:V), [reference measure](hyp:mu),
[conditional density](hyp:g), [penalty](hyp:lam), [localization radius](hyp:r),
and [iteration index](hyp:j), [the localized fixed-center loss class](goal)
consists of loss differences between class members within that radius of the
population iterate and the population iterate itself. -/
noncomputable def iterRdivFixedCenterLossClass (mu : Measure 𝒳)
    (g : 𝒳 → 𝒵 → ℝ) (lam r : ℝ) (j : ℕ) : Set (𝒲 → ℝ) :=
  {f | ∃ h ∈ V.H, ‖h - populationIterate V lam j‖ ≤ r ∧
    f = iterRdivFixedCenterLoss V mu g lam j h -
      iterRdivFixedCenterLoss V mu g lam j (populationIterate V lam j)}

/-- For [the instrumental-variable model](hyp:V), [penalty](hyp:lam),
[localization radius](hyp:r), and [iteration index](hyp:k), [the localized
squared-loss class](goal) consists of squared pointwise differences from the
population iterate, for hypothesis-class members within the given population
norm radius. -/
noncomputable def iterRdivSquaredLossClass (lam r : ℝ) (k : ℕ) : Set (𝒲 → ℝ) :=
  {f | ∃ h ∈ V.H, ‖h - populationIterate V lam k‖ ≤ r ∧ f = fun w =>
    (primalVersion V h (V.xOf w) -
      primalVersion V (populationIterate V lam k) (V.xOf w)) ^ 2}

/-- For [the instrumental-variable model](hyp:V), [sampling law](hyp:P),
[analysis sample](hyp:sample), [sample split](hyp:split), [fitting sample
size](hyp:n), and [preliminary-data-dependent loss class](hyp:lossClass),
[coherence of the empirical supremum](goal) means there exists a version that
[is jointly measurable in preliminary data and fresh observations](step:1),
[agrees almost surely with the empirical supremum on almost every fresh-sample
section](step:2), and [also agrees almost surely on the actual fitting block](step:3). -/
noncomputable def iterRdivCoherentSupremum (P : Measure Ω)
    (sample : AnalysisSample V P) (split : SampleSplit) (n : ℕ)
    (lossClass : Ω → Set (𝒲 → ℝ)) : Prop :=
  ∃ version : Ω × (Fin n → 𝒲) → ℝ≥0∞,
    @Measurable (Ω × (Fin n → 𝒲)) ℝ≥0∞
      ((preliminarySigma V P sample split n).prod inferInstance) inferInstance version ∧
    (∀ᵐ a ∂P, (fun ws => version (a, ws)) =ᵐ[Measure.pi (fun _ => V.law)]
      empiricalSupremum V.law (lossClass a) n) ∧
    (fun ω => version (ω, fun i =>
      sample.Z ((Finset.equivFinOfCardEq (split.card_fit n)).symm i) ω)) =ᵐ[P]
      (fun ω => empiricalSupremum V.law (lossClass ω) n
        (fun i => sample.Z ((Finset.equivFinOfCardEq (split.card_fit n)).symm i) ω))

/-- For [the instrumental-variable model](hyp:V), [sampling law](hyp:P),
[analysis sample](hyp:sample), [sample split](hyp:split), [reference
measure](hyp:mu), [selected density sequence](hyp:gHat), and [grid ratio](hyp:ρ),
[the fixed-center supremum version condition](goal) requires, at every positive
sample size, positive horizon, grid penalty, and positive rational radius,
[coherent suprema for all fixed-center loss classes through the horizon](step:1)
and [coherent suprema for all squared-distance classes through the horizon](step:2). -/
-- @node: ass:bk-owner-4
noncomputable def IterRDIVFixedCenterSupremumVersion (P : Measure Ω)
    (sample : AnalysisSample V P) (split : SampleSplit) (mu : Measure 𝒳)
    (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (ρ : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ t : ℕ, 1 ≤ t → ∀ lam ∈ regGrid ρ n,
    ∀ q : ℚ, 0 < q →
    (∀ j : ℕ, 1 ≤ j → j ≤ t →
      iterRdivCoherentSupremum V P sample split n
        (fun a => iterRdivFixedCenterLossClass V mu (gHat n a) lam (q : ℝ) j)) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ t →
      iterRdivCoherentSupremum V P sample split n
        (fun _ => iterRdivSquaredLossClass V lam (q : ℝ) k))

/-- For [an observation law](hyp:law), [function class](hyp:F), [fixed comparator
function](hyp:fstar), [sample size](hyp:n), and [radius](hyp:r), [the anchored
critical-radius condition](goal) requires that the expected Rademacher complexity
of the star-shaped comparator differences with L² norm at most the radius does
not exceed the squared radius. -/
noncomputable def iterRdivAnchoredRadius {A : Type*} [MeasurableSpace A]
    (law : Measure A) (F : Set (A → ℝ)) (fstar : A → ℝ) (n : ℕ) (r : ℝ) : Prop :=
  expectedRademacher law
    {f ∈ starClass ((fun g => g - fstar) '' F) |
      eLpNorm f 2 law ≤ ENNReal.ofReal r} n ≤ ENNReal.ofReal (r ^ 2)

/-- For [the instrumental-variable model](hyp:V), [the fixed-center localized
concentration assumption](goal) asserts that every realizable, bounded density
model with bounded outcomes and hypotheses admits positive universal constants
giving a localized fixed-center loss-deviation bound on fresh samples, conditional
on almost every preliminary sample, whenever selection, measurability, coherent
versions, grid scope, population-center membership, critical radii, and the
logarithmic radius floor hold. The event has probability at least one minus
twice the tail constant times the exponential of minus the tail rate times
sample size times squared radius divided by eight; the deviation is at most
the leading constant times radius times the sum of operator error, structural
error, and radius.

Foster and Syrgkanis (2023), Orthogonal statistical learning,
DOI 10.1214/23-AOS2258, arXiv:1901.09036v4, Lemma 14
(lem:lipschitz_wainwright), fixed-population-comparator two-coordinate use.
The positive signed-tail constants come from lem:prob_localized and the retained
full lem:peeling proof; the unsigned printed c6 is not assigned a sign.
Constants precede P, sample, split, horizon, penalty, comparator index and radius.
Only the source increment is supplied. Comparator membership, clipping and
normalization, translated-radius verification, confidence conversion, measurable
version transport and iteration-grid allocation are local obligations. The
explicit sourceRadius is the actual oracle radius threaded unchanged by the
public constructors, even when the internal accuracy is rescaled. The separate
zero-source initial-acceptance application uses the deterministic singleton {2}. -/
-- @node: lem:iter-rdiv-fixed-center-concentration-lemma-14
noncomputable def IterRDIVFixedCenterLocalizedConcentration : Sort 0 :=
  ∀ (mu : Measure 𝒳) (G : Set (𝒳 → 𝒵 → ℝ)) (g₀ : 𝒳 → 𝒵 → ℝ)
    (support : Set (𝒳 × 𝒵)) (B c₀ CG : ℝ),
    RDIVSetting V mu g₀ → DensityRealizable V mu G g₀ →
    DensityBounds G g₀ support c₀ CG → OutcomeBounded V B →
    HypothesisClassBounded V support B →
    ∃ C > 0, ∃ c₁ > 0, ∃ c₂ > 0,
    ∀ (P : Measure Ω) (_hProbability : IsProbabilityMeasure P)
      (sample : AnalysisSample V P) (split : SampleSplit)
      (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (ρ : ℝ),
    MLEMaximizerSelected V P sample split G gHat →
    RDIVClassesMeasurable V P sample split mu G g₀ gHat →
    IterRDIVFixedCenterSupremumVersion V P sample split mu gHat ρ →
    ∀ (n t j : ℕ) (lam r : ℝ) (sourceRadius : ℝ)
      (_hSourceScope : gridValue ρ (terminalIndex ρ n) ≤ sourceRadius ∧
        oraclePoint ρ n sourceRadius ≤ lam), 0 < n → 1 ≤ j → j ≤ t →
    lam ∈ regGrid ρ n → lam ∈ Set.Ioc (0 : ℝ) 2 →
    populationIterate V lam j ∈ V.H →
    (populationIterate V lam (j - 1) ∈ V.H ∨ j = 1) →
    0 < r → 1 < 2 * c₂ * n →
    8 * Real.log (41 * Real.log (2 * c₂ * n)) / (c₂ * n) ≤ r ^ 2 →
    iterRdivAnchoredRadius (V.law.map V.xOf) (primalVersion V '' V.H)
      (primalVersion V (populationIterate V lam j)) n r →
    (∀ g ∈ G, iterRdivAnchoredRadius (V.law.map V.zOf)
      (densityOperator mu g '' (primalVersion V '' V.H))
      (densityOperator mu g (primalVersion V (populationIterate V lam j))) n r) →
    ∀ᵐ a ∂P, ∃ E : Set (Fin n → 𝒲), MeasurableSet E ∧
      1 - 2 * c₁ * Real.exp (-c₂ * n * r ^ 2 / 8) ≤
        (Measure.pi (fun _ : Fin n => V.law)).real E ∧
      ∀ ws ∈ E, ∀ h ∈ V.H,
        let increment := iterRdivFixedCenterLoss V mu (gHat n a) lam j h -
          iterRdivFixedCenterLoss V mu (gHat n a) lam j (populationIterate V lam j)
        |(n : ℝ)⁻¹ * (∑ i, increment (ws i)) - ∫ w, increment w ∂V.law| ≤
          C * r * (inputL2Norm (V.law.map V.zOf)
            (densityOperator mu (gHat n a) (primalVersion V h -
              primalVersion V (populationIterate V lam j))) +
            ‖h - populationIterate V lam j‖ + r)

/-- For [the instrumental-variable model](hyp:V), [the squared-loss localized
concentration assumption](goal) asserts that every realizable, bounded density
model with bounded hypotheses admits positive universal constants controlling
empirical squared distances from each admissible population iterate, conditional
on almost every preliminary sample, under measurability, coherent versions, grid
scope, class membership, the anchored critical radius, and the logarithmic radius
floor. The event has probability at least one minus twice the tail constant
times the exponential of minus the tail rate times sample size times squared
radius divided by four; uniformly over hypotheses, the squared-distance deviation
is at most the leading constant times radius times population distance plus
the leading constant times squared radius.

Foster and Syrgkanis (2023), Orthogonal statistical learning,
DOI 10.1214/23-AOS2258, arXiv:1901.09036v4, Lemma 14
(lem:lipschitz_wainwright), scalar fixed-population-comparator squared-loss use.
The signed-tail evidence is lem:prob_localized and the full lem:peeling proof,
not a correction of the unsigned c6 display. Constants are chosen before the
sampling experiment and every particular population center. No curvature,
empirical optimality, recursion, stability or calibration conclusion is assumed.
The zero-iterate identity and small-sample bounded envelope are local. -/
-- @node: lem:iter-rdiv-squared-loss-concentration-lemma-14
noncomputable def IterRDIVSquaredLossLocalizedConcentration : Sort 0 :=
  ∀ (mu : Measure 𝒳) (G : Set (𝒳 → 𝒵 → ℝ)) (g₀ : 𝒳 → 𝒵 → ℝ)
    (support : Set (𝒳 × 𝒵)) (B c₀ CG : ℝ),
    RDIVSetting V mu g₀ → DensityRealizable V mu G g₀ →
    DensityBounds G g₀ support c₀ CG → HypothesisClassBounded V support B →
    ∃ C > 0, ∃ c₁ > 0, ∃ c₂ > 0,
    ∀ (P : Measure Ω) (_hProbability : IsProbabilityMeasure P)
      (sample : AnalysisSample V P) (split : SampleSplit)
      (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (ρ : ℝ),
    RDIVClassesMeasurable V P sample split mu G g₀ gHat →
    IterRDIVFixedCenterSupremumVersion V P sample split mu gHat ρ →
    ∀ (n t k : ℕ) (lam r : ℝ) (sourceRadius : ℝ)
      (_hSourceScope : gridValue ρ (terminalIndex ρ n) ≤ sourceRadius ∧
        oraclePoint ρ n sourceRadius ≤ lam), 0 < n → 1 ≤ k → k ≤ t →
    lam ∈ regGrid ρ n → lam ∈ Set.Ioc (0 : ℝ) 2 →
    populationIterate V lam k ∈ V.H →
    0 < r → 1 < 2 * c₂ * n →
    4 * Real.log (41 * Real.log (2 * c₂ * n)) / (c₂ * n) ≤ r ^ 2 →
    iterRdivAnchoredRadius (V.law.map V.xOf) (primalVersion V '' V.H)
      (primalVersion V (populationIterate V lam k)) n r →
    ∀ᵐ a ∂P, ∃ E : Set (Fin n → 𝒲), MeasurableSet E ∧
      1 - 2 * c₁ * Real.exp (-c₂ * n * r ^ 2 / 4) ≤
        (Measure.pi (fun _ : Fin n => V.law)).real E ∧
      ∀ ws ∈ E, ∀ h ∈ V.H,
        |(n : ℝ)⁻¹ * (∑ i, (primalVersion V h (V.xOf (ws i)) -
          primalVersion V (populationIterate V lam k) (V.xOf (ws i))) ^ 2) -
          ‖h - populationIterate V lam k‖ ^ 2| ≤
          C * r * (‖h - populationIterate V lam k‖ + r)

end Papers.TsAdaptiveEstimationInference
