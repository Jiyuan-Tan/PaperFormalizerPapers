module
public import Papers.TsAdaptiveEstimationInference.Helpers.TRAE
public import Papers.TsAdaptiveEstimationInference.Helpers.TRAEIncrementNorms
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAEClipping
/-! Fixed-anchor and fixed-center Bennett Lemma 9 interfaces for iterative TRAE.
Only raw clipped deviations under the canonical iid law are cited here.
Calibration, norm conversion, fitting-block transport and finite unions are local.
-/
@[expose] public section
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory
open scoped ENNReal
variable {𝒲 𝒳 𝒵 : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] (V : IVWorld 𝒲 𝒳 𝒵)

/-- For [an observation law](hyp:law), [a class of vector-valued functions](hyp:F),
[a reference function](hyp:v0), [a loss function](hyp:loss), and [a sample size](hyp:n),
the [localized measurability condition](goal) requires, at every positive population
L2 radius around the reference, both [almost-everywhere measurability of the supremum
of absolute centered empirical loss differences](step:1) and [almost-everywhere
measurability of the corresponding supremum with independent uniform random signs](step:2).
The sample observations are independent with the given law. -/
noncomputable def AELocalizedSupremaMeasurableAt {A : Type*} [MeasurableSpace A]
    {d : ℕ} (law : Measure A) (F : Set (A → Fin d → ℝ))
    (v0 : A → Fin d → ℝ) (loss : A → (Fin d → ℝ) → ℝ) (n : ℕ) : Prop :=
  ∀ r : ℝ, 0 < r →
    let localized := {v : F //
      eLpNorm (fun w => Real.sqrt (∑ i, (v.1 w i - v0 w i) ^ 2)) 2 law ≤
        ENNReal.ofReal r}
    AEMeasurable (fun x : Fin n → A => ⨆ v : localized,
      ENNReal.ofReal |(n : ℝ)⁻¹ * (∑ i,
        (loss (x i) (v.1.1 (x i)) - loss (x i) (v0 (x i)))) -
          ∫ w, (loss w (v.1.1 w) - loss w (v0 w)) ∂law|) (Measure.pi (fun _ => law)) ∧
    AEMeasurable (fun p : (Fin n → A) × (Fin n → Bool) => ⨆ v : localized,
      ENNReal.ofReal |(n : ℝ)⁻¹ * ∑ i, (if p.2 i then (1 : ℝ) else -1) *
        (loss (p.1 i) (v.1.1 (p.1 i)) - loss (p.1 i) (v0 (p.1 i)))|)
      ((Measure.pi (fun _ => law)).prod
        ((2 ^ n : ℝ≥0∞)⁻¹ • (Measure.count : Measure (Fin n → Bool))))

/-- For [a class of scalar observation functions](hyp:F), the [scalar observation
class viewed as one-coordinate vectors](goal) consists exactly of those same
functions placed in the sole coordinate. -/
noncomputable def iterTraeScalarClass (F : Set (𝒲 → ℝ)) : Set (𝒲 → Fin 1 → ℝ) :=
  {u | ∃ f ∈ F, u = fun w => fun _ : Fin 1 => f w}

/-- Given [an envelope level](hyp:B), [a deterministic center function](hyp:center),
[an observation](hyp:w), and [a one-coordinate input](hyp:u), the [normalized clipped
squared loss](goal) is the square of the absolute difference between the input and
the center at that observation, divided by twice the larger of one and the envelope
level, and clipped at one before squaring. -/
noncomputable def iterTraeSourceSquare (B : ℝ) (center : 𝒲 → ℝ)
    (w : 𝒲) (u : Fin 1 → ℝ) : ℝ :=
  (min |(u 0 - center w) / (2 * max 1 B)| 1) ^ 2

/-- In [the instrumental-variable model](hyp:V), at [an iteration index](hyp:j)
and [a regularization penalty](hyp:lam), the [population anchor](goal) is formed by
[taking the population iterate](step:1), [applying the projected conditional
expectation operator to the difference between the minimum-norm solution and that
iterate](step:2), and [returning the three observation functions: the moment of this
critic, the product of the iterate and critic, and the critic itself](step:3). -/
noncomputable def iterTraePopulationAnchor (j : ℕ) (lam : ℝ) : 𝒲 → Fin 3 → ℝ :=
  let h := populationIterate V lam j
  let f := projCondExpOp V (minNormSolution V - h)
  fun w => ![V.m f w, primalVersion V h (V.xOf w) * dualVersion V f (V.zOf w),
    dualVersion V f (V.zOf w)]

/-- For [the instrumental-variable model](hyp:V), the [anchored localized
concentration property](goal) asserts that boundedness, a common almost-sure
envelope, and a positive confidence-floor multiplier yield a positive constant
uniform over sample sizes of at least three, failure probabilities between zero
and one, and positive radii above the confidence floor that bound the critical
radii of all three coordinate star classes. For every valid grid configuration
and horizon, and every loss-class anchor that is either zero or an admissible
population iteration on the defined oracle segment, measurability of the localized
suprema yields a measurable event of probability at least one minus the failure
probability on which all absolute centered empirical clipped-loss differences are
bounded by that constant times the sum of the squared radius and the radius
multiplied by the sum of the three coordinate L2 distances from the anchor.

Bennett, Kallus, Mao, Newey, Syrgkanis and Uehara (2023),
Source condition double robust inference on functionals of inverse problems,
arXiv:2307.13793, Lemma 9 (`lem:concentration`). The source's h_*/h_0
notation denotes one fixed deterministic anchor. Only zero and the designated
population iteration--grid anchors are included, on the actual least-index
oracle segment and its defined domain. The event follows its
anchor; the constant precedes n, confidence, radius, horizon and anchor. Dimension
three is absorbed into C. The conclusion retains the sum of coordinate L2
DIFFERENCES, without a local conversion or any variational conclusion. -/
-- @node: lem:iter-trae-anchored-concentration-lemma-9
noncomputable def IterTRAEAnchoredLocalizedConcentration : Sort 0 :=
  ∀ B cfloor : ℝ, TRAEBoundedness V B → TRAECommonNullSetBoundedness V B → 0 < cfloor →
  ∃ C > 0, ∀ n : ℕ, 3 ≤ n → ∀ ζ ∈ Set.Ioo (0 : ℝ) 1,
  ∀ r : ℝ, cfloor * Real.sqrt
    ((3 * Real.log (Real.log n) + Real.log (1 / ζ)) / n) ≤ r →
  0 < r →
  (∀ F ∈ ({starClass (momentImageClass V),
      starClass (productObservationClass V), starClass (criticObservationClass V)} :
        Set (Set (𝒲 → ℝ))),
    IsCriticalRadiusBound V.law F n r) →
  ∀ (ρ c b β : ℝ) (δ : ℕ → ℝ) (t : ℕ),
  GridDomain ρ → 0 < c → 2 ≤ b → 0 < β → 1 ≤ t →
  let radius := c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))
  ∀ anchor : 𝒲 → Fin 3 → ℝ,
  (anchor = 0 ∨ ∃ j : ℕ, 1 ≤ j ∧ j ≤ t ∧
    ∃ lam ∈ regGrid ρ n,
      (∃ k ≤ terminalIndex ρ n, gridValue ρ k ≤ radius) ∧
      oraclePoint ρ n radius ≤ lam ∧ lam ≤ 2 ∧ 0 < lam ∧
      populationIterate V lam j ∈ V.H ∧
      projCondExpOp V (minNormSolution V - populationIterate V lam j) ∈ V.F ∧
      anchor = iterTraePopulationAnchor V j lam) →
  anchor ∈ traeLossClass V →
  AELocalizedSupremaMeasurableAt V.law (traeLossClass V) anchor (traeClippedLoss B) n →
  ∃ E : Set (Fin n → 𝒲), MeasurableSet E ∧
    1 - ζ ≤ (Measure.pi (fun _ : Fin n => V.law)).real E ∧
    ∀ x ∈ E, ∀ u ∈ traeLossClass V,
      |(n : ℝ)⁻¹ * (∑ i, (traeClippedLoss B (x i) (u (x i)) -
          traeClippedLoss B (x i) (anchor (x i)))) -
        ∫ w, (traeClippedLoss B w (u w) - traeClippedLoss B w (anchor w)) ∂V.law| ≤
      C * (r * (∑ i : Fin 3, inputL2Norm V.law (fun w => u w i - anchor w i)) + r ^ 2)

/-- In [the instrumental-variable model](hyp:V), for [an envelope level](hyp:B),
[a confidence-floor multiplier](hyp:cfloor), and [a deviation constant](hyp:C), the
[fixed-center raw concentration property](goal) requires a measurable event of
probability at least one minus the failure probability on which every primal
function's absolute centered empirical clipped-square difference from the designated
population iterate is bounded by the deviation constant times the sum of the
squared radius and the radius multiplied by their population L2 distance. This holds for sample sizes
of at least three, failure probabilities between zero and one, positive radii above
the confidence floor satisfying the primal star-class critical-radius bound, valid
grid and iteration configurations on the defined oracle segment, a population
iterate in the primal class, a center equal to that iterate or its predecessor and
bounded almost surely by the envelope level, and measurable localized suprema. -/
noncomputable def IterTRAEFixedCenterRaw (B cfloor C : ℝ) : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ ζ ∈ Set.Ioo (0 : ℝ) 1,
  ∀ r : ℝ, cfloor * Real.sqrt
    ((Real.log (Real.log n) + Real.log (1 / ζ)) / n) ≤ r →
  0 < r →
  IsCriticalRadiusBound V.law (starClass (primalObservationClass V)) n r →
  ∀ (ρ c b β : ℝ) (δ : ℕ → ℝ) (t j : ℕ),
  GridDomain ρ → 0 < c → 2 ≤ b → 0 < β → 1 ≤ j → j ≤ t →
  let radius := c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))
  (∃ k ≤ terminalIndex ρ n, gridValue ρ k ≤ radius) →
  ∀ lam ∈ regGrid ρ n, oraclePoint ρ n radius ≤ lam → lam ≤ 2 → 0 < lam →
  populationIterate V lam j ∈ V.H →
  ∀ center : V.Hbar.toSubmodule,
  (center = populationIterate V lam (j - 1) ∨ center = populationIterate V lam j) →
  (∀ᵐ w ∂V.law, |primalVersion V center (V.xOf w)| ≤ B) →
  AELocalizedSupremaMeasurableAt V.law
    (iterTraeScalarClass (primalObservationClass V))
    (fun w => fun _ : Fin 1 => primalVersion V (populationIterate V lam j) (V.xOf w))
    (iterTraeSourceSquare B (fun w => primalVersion V center (V.xOf w))) n →
  ∃ E : Set (Fin n → 𝒲), MeasurableSet E ∧
    1 - ζ ≤ (Measure.pi (fun _ : Fin n => V.law)).real E ∧
    ∀ x ∈ E, ∀ h ∈ V.H,
      |(n : ℝ)⁻¹ * (∑ i,
          (iterTraeSourceSquare B (fun w => primalVersion V center (V.xOf w))
            (x i) (fun _ => primalVersion V h (V.xOf (x i))) -
          iterTraeSourceSquare B (fun w => primalVersion V center (V.xOf w))
            (x i) (fun _ => primalVersion V (populationIterate V lam j) (V.xOf (x i))))) -
        ∫ w, (iterTraeSourceSquare B (fun w => primalVersion V center (V.xOf w))
          w (fun _ => primalVersion V h (V.xOf w)) -
          iterTraeSourceSquare B (fun w => primalVersion V center (V.xOf w))
            w (fun _ => primalVersion V (populationIterate V lam j) (V.xOf w))) ∂V.law| ≤
      C * (r * inputL2Norm V.law (fun w =>
        primalVersion V h (V.xOf w) -
          primalVersion V (populationIterate V lam j) (V.xOf w)) + r ^ 2)

/-- In [the instrumental-variable model](hyp:V), for [a sample size](hyp:n),
[a scalar function class](hyp:F), [a comparator function](hyp:anchor), and [a penalty
center function](hyp:center), an [admissible scalar source application](goal)
requires [the scalar class to be exactly the primal observation class](step:1)
and [the existence of a valid grid configuration and iteration between one and the
horizon, with a defined oracle segment and a positive grid penalty between the
oracle penalty and two, whose population iterate belongs to the primal class,
whose observation function is the comparator, and whose current or preceding
population observation function is the center](step:2). -/
-- @node: IterTRAEScalarSourceApplication
noncomputable def IterTRAEScalarSourceApplication (n : ℕ)
    (F : Set (𝒲 → ℝ)) (anchor center : 𝒲 → ℝ) : Prop :=
  F = primalObservationClass V ∧
    ∃ (ρ c b β : ℝ) (δ : ℕ → ℝ) (t j : ℕ),
      GridDomain ρ ∧ 0 < c ∧ 2 ≤ b ∧ 0 < β ∧ 1 ≤ j ∧ j ≤ t ∧
      let radius := c * (b * δ n ^ 2) ^ (1 / (qualificationExponent β t + 1))
      (∃ k ≤ terminalIndex ρ n, gridValue ρ k ≤ radius) ∧
      ∃ lam ∈ regGrid ρ n, oraclePoint ρ n radius ≤ lam ∧ lam ≤ 2 ∧ 0 < lam ∧
      populationIterate V lam j ∈ V.H ∧
      anchor = (fun w => primalVersion V (populationIterate V lam j) (V.xOf w)) ∧
      (center = (fun w => primalVersion V (populationIterate V lam (j - 1)) (V.xOf w)) ∨
       center = (fun w => primalVersion V (populationIterate V lam j) (V.xOf w)))

/-- For [the instrumental-variable model](hyp:V), the [fixed-center squared-loss
concentration property](goal) asserts that boundedness, a common almost-sure envelope,
and a positive confidence-floor multiplier yield a positive deviation constant.
For sample sizes of at least three, failure probabilities between zero and one,
and positive radii above the confidence floor, every admissible scalar source
application whose anchor belongs to its class, whose class has common almost-sure
envelope twice the larger of one and the boundedness level, whose clipped-square
loss is globally one-Lipschitz, whose localized star-class expected Rademacher
complexity is at most the squared radius, and whose localized suprema are measurable
admits a measurable event of probability at least one minus the failure probability;
on this event every absolute centered empirical loss difference is bounded by the
constant times the sum of the squared radius and the radius multiplied by the
population L2 distance from the anchor.

Bennett et al. (2023), arXiv:2307.13793, Lemma 9 (`lem:concentration`),
dimension one, restricted to the two population-center applications above. Only
the raw source inequality is cited. Anchor membership, common boundedness,
global Lipschitzness and the source star-class radius are explicit premises,
discharged by the local specialization proofs below. No empirical norm,
calibrated comparison, random-center or recursive conclusion is supplied. -/
-- @node: lem:iter-trae-fixed-center-squared-loss-lemma-9
noncomputable def IterTRAEFixedCenterSquaredLossConcentration : Sort 0 :=
  ∀ B cfloor : ℝ, TRAEBoundedness V B → TRAECommonNullSetBoundedness V B → 0 < cfloor →
  ∃ C > 0, ∀ n : ℕ, 3 ≤ n → ∀ ζ ∈ Set.Ioo (0 : ℝ) 1,
  ∀ r : ℝ, cfloor * Real.sqrt
    ((Real.log (Real.log n) + Real.log (1 / ζ)) / n) ≤ r → 0 < r →
  ∀ (F : Set (𝒲 → ℝ)) (anchor center : 𝒲 → ℝ),
  IterTRAEScalarSourceApplication V n F anchor center →
  anchor ∈ F →
  (∀ᵐ w ∂V.law, ∀ f ∈ F, |f w| ≤ 2 * max 1 B) →
  (∀ w (u v : Fin 1 → ℝ),
    |iterTraeSourceSquare B center w u - iterTraeSourceSquare B center w v| ≤
      |u 0 - v 0|) →
  expectedRademacher V.law {f ∈ starClass F | eLpNorm f 2 V.law ≤ ENNReal.ofReal r} n ≤
    ENNReal.ofReal (r ^ 2) →
  AELocalizedSupremaMeasurableAt V.law (iterTraeScalarClass F)
    (fun w => fun _ : Fin 1 => anchor w) (iterTraeSourceSquare B center) n →
  ∃ E : Set (Fin n → 𝒲), MeasurableSet E ∧
    1 - ζ ≤ (Measure.pi (fun _ : Fin n => V.law)).real E ∧
    ∀ x ∈ E, ∀ f ∈ F,
      |(n : ℝ)⁻¹ * (∑ i,
          (iterTraeSourceSquare B center (x i) (fun _ => f (x i)) -
           iterTraeSourceSquare B center (x i) (fun _ => anchor (x i)))) -
        ∫ w, (iterTraeSourceSquare B center w (fun _ => f w) -
          iterTraeSourceSquare B center w (fun _ => anchor w)) ∂V.law| ≤
      C * (r * inputL2Norm V.law (fun w => f w - anchor w) + r ^ 2)

/-- [The absolute difference between the normalized clipped squared losses of
any two one-coordinate inputs, at any observation and deterministic center and
for any envelope level, is at most the absolute difference between those inputs](goal). -/
-- @node: iterTraeSourceSquare_lipschitz
lemma iterTraeSourceSquare_lipschitz (B : ℝ) (center : 𝒲 → ℝ)
    (w : 𝒲) (u v : Fin 1 → ℝ) :
    |iterTraeSourceSquare B center w u - iterTraeSourceSquare B center w v| ≤
      |u 0 - v 0| := by
  have hs : 0 < 2 * max 1 B := by positivity
  have h := iter_trae_clipped_center_lipschitz (2 * max 1 B) (center w) (u 0) (v 0) hs
  apply h.trans
  apply mul_le_of_le_one_left (abs_nonneg _)
  exact (div_le_one hs).2 (by nlinarith only [le_max_left (1 : ℝ) B])

/-- If [the scalar function class is nonempty](hyp:hF) and [the radius satisfies
the critical-radius bound for its star class at the given sample size](hyp:hcrit),
then [the expected Rademacher complexity of star-class functions with population
L2 norm at most that radius is at most the squared radius](goal).

The zero member of the star class embeds every member as a difference from zero. -/
-- @node: iterTrae_scalar_source_radius
lemma iterTrae_scalar_source_radius (F : Set (𝒲 → ℝ)) (hF : F.Nonempty)
    (n : ℕ) (r : ℝ) (hcrit : IsCriticalRadiusBound V.law (starClass F) n r) :
    expectedRademacher V.law {f ∈ starClass F | eLpNorm f 2 V.law ≤ ENNReal.ofReal r} n ≤
      ENNReal.ofReal (r ^ 2) := by
  obtain ⟨g, hg⟩ := hF
  have hz : (0 : 𝒲 → ℝ) ∈ starClass F :=
    ⟨0, ⟨le_rfl, zero_le_one⟩, g, hg, by simp⟩
  apply le_trans (trae_expectedRademacher_mono V.law ?_ n) hcrit.2
  intro f hf
  refine ⟨⟨1, ⟨zero_le_one, le_rfl⟩, f, ?_, by simp⟩, hf.2⟩
  exact ⟨f, hf.1, 0, hz, by simp⟩

/-- If [fixed-center squared-loss concentration holds](hyp:hSource), [the model
satisfies the boundedness and process conditions at the chosen envelope level](hyp:hBound),
[the primal, dual, and moment functions share an almost-sure bound at that level](hyp:hCommon),
and [the confidence-floor multiplier is positive](hyp:hfloor), then [there is a
positive deviation constant for which raw fixed-center concentration holds for
the designated population comparators and their current or preceding population
centers](goal). -/
-- @node: iterTraeFixedCenterSource_local
lemma iterTraeFixedCenterSource_local
    (hSource : IterTRAEFixedCenterSquaredLossConcentration V)
    (B cfloor : ℝ) (hBound : TRAEBoundedness V B)
    (hCommon : TRAECommonNullSetBoundedness V B) (hfloor : 0 < cfloor) :
    ∃ C > 0, IterTRAEFixedCenterRaw V B cfloor C := by
  obtain ⟨C, hC, hsource⟩ := hSource B cfloor hBound hCommon hfloor
  refine ⟨C, hC, ?_⟩
  intro n hn ζ hζ r hfloor hr hcrit ρ c b β δ t j hρ hc hb hβ hj hjt
  dsimp only
  intro hdefined lam hlam hlo hu hp hmem center hcenter henv hmeas
  have happ : IterTRAEScalarSourceApplication V n (primalObservationClass V)
      (fun w => primalVersion V (populationIterate V lam j) (V.xOf w))
      (fun w => primalVersion V center (V.xOf w)) := by
    refine ⟨rfl, ρ, c, b, β, δ, t, j, hρ, hc, hb, hβ, hj, hjt, hdefined,
      lam, hlam, hlo, hu, hp, hmem, rfl, ?_⟩
    rcases hcenter with hcenter | hcenter
    · exact Or.inl (congrArg (fun h => fun w => primalVersion V h (V.xOf w)) hcenter)
    · exact Or.inr (congrArg (fun h => fun w => primalVersion V h (V.xOf w)) hcenter)
  have ha : (fun w => primalVersion V (populationIterate V lam j) (V.xOf w)) ∈
      primalObservationClass V := ⟨_, hmem, rfl⟩
  have henvF : ∀ᵐ w ∂V.law, ∀ f ∈ primalObservationClass V, |f w| ≤ 2 * max 1 B := by
    filter_upwards [hCommon] with w hw
    rintro f ⟨h, hh, rfl⟩
    exact (hw.1 h hh).trans (by linarith [le_max_right (1 : ℝ) B, le_max_left (1 : ℝ) B])
  obtain ⟨E, hE, hpE, hgood⟩ := hsource n hn ζ hζ r hfloor hr (primalObservationClass V)
    (fun w => primalVersion V (populationIterate V lam j) (V.xOf w))
    (fun w => primalVersion V center (V.xOf w)) happ ha henvF
    (iterTraeSourceSquare_lipschitz B _) (iterTrae_scalar_source_radius V _ ⟨_, ha⟩ n r hcrit)
    hmeas
  refine ⟨E, hE, hpE, ?_⟩
  intro x hx h hh
  exact hgood x hx (fun w => primalVersion V h (V.xOf w)) ⟨h, hh, rfl⟩

end Papers.TsAdaptiveEstimationInference
