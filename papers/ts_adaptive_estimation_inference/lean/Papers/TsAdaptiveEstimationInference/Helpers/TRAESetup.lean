module
public import Papers.TsAdaptiveEstimationInference.Helpers.Discrepancy
public import Papers.TsAdaptiveEstimationInference.Helpers.Spectral
/-! Adversarial objectives, recorded assumptions, and disclosed concentration inputs. -/
@[expose] public section
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.style.longLine false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter
open scoped Topology ENNReal
variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]
  (V : IVWorld 𝒲 𝒳 𝒵) (P : Measure Ω)
  (sample : AnalysisSample V P) (split : SampleSplit)

/-- For [an instrumental-variable model](hyp:V), [a primal function h](hyp:h),
[a critic f](hyp:f), and [an observation w](hyp:w), the [adversarial loss contribution](goal)
is twice the moment contribution minus twice the product of the primal and critic
values minus the squared critic value. -/
noncomputable def traeIntegrand (h : V.Hbar.toSubmodule) (f : V.Qbar.toSubmodule)
    (w : 𝒲) : ℝ :=
  2 * V.m f w - 2 * primalVersion V h (V.xOf w) * dualVersion V f (V.zOf w) -
    dualVersion V f (V.zOf w) ^ 2

-- @node: def:trae-estimator
/-- For [a model](hyp:V), [a sampling law](hyp:P), [an analysis sample](hyp:sample),
[a sample split](hyp:split), [sample size n](hyp:n), [sample outcome ω](hyp:ω), and
[primal function h](hyp:h), the [empirical adversarial loss](goal) is the supremum
over admissible critics of the average adversarial contribution on the fitting block. -/
noncomputable def traeEmpiricalLoss (n : ℕ) (ω : Ω) (h : V.Hbar.toSubmodule) : ℝ :=
  ⨆ f : V.F, blockAverage V P sample (split.fit n) (traeIntegrand V h f) ω
  -- @realizes L_n(empirical adversarial loss)

/-- For [a model](hyp:V) and [primal function h](hyp:h), the [population adversarial
loss](goal) is the supremum over admissible critics of the expected adversarial contribution. -/
noncomputable def traePopulationLoss (h : V.Hbar.toSubmodule) : ℝ :=
  ⨆ f : V.F, ∫ w, traeIntegrand V h f w ∂V.law
  -- @realizes L(population adversarial loss)

/-- For [a model](hyp:V), [sampling law](hyp:P), [analysis sample](hyp:sample),
[sample split](hyp:split), [sample size n](hyp:n), [sample outcome ω](hyp:ω), and
[primal function h](hyp:h), the [empirical squared norm](goal) is the fitting-block
average of the squared primal values. -/
noncomputable def primalEmpSq (n : ℕ) (ω : Ω) (h : V.Hbar.toSubmodule) : ℝ :=
  blockAverage V P sample (split.fit n) (fun w => primalVersion V h (V.xOf w) ^ 2) ω

/-- For [a model](hyp:V), [sampling law](hyp:P), [analysis sample](hyp:sample),
[sample split](hyp:split), [sample size n](hyp:n), [penalty weight λ](hyp:lam), and
[candidate estimator](hyp:candidate), the [TRAE minimization requirement](goal)
is that, at every sample outcome, the candidate [belongs to the hypothesis class](step:1)
and [minimizes empirical adversarial loss plus λ times the empirical squared norm
over that class](step:2). -/
noncomputable def IsTRAEEstimator (n : ℕ) (lam : ℝ)
    (candidate : Ω → V.Hbar.toSubmodule) : Prop :=
  ∀ ω, candidate ω ∈ V.H ∧ ∀ h ∈ V.H,
    traeEmpiricalLoss V P sample split n ω (candidate ω) +
      lam * primalEmpSq V P sample split n ω (candidate ω) ≤
    traeEmpiricalLoss V P sample split n ω h + lam * primalEmpSq V P sample split n ω h

/-- For [a model](hyp:V), [sampling law](hyp:P), [analysis sample](hyp:sample),
[sample split](hyp:split), [sample size n](hyp:n), [sample outcome ω](hyp:ω),
and [two primal functions](hyp:h,h'), their [empirical squared distance](goal)
is the fitting-block average of their squared pointwise difference. -/
noncomputable def primalEmpDistanceSq (n : ℕ) (ω : Ω)
    (h h' : V.Hbar.toSubmodule) : ℝ :=
  blockAverage V P sample (split.fit n)
    (fun w => (primalVersion V h (V.xOf w) - primalVersion V h' (V.xOf w)) ^ 2) ω

-- @node: ass:closeness
/-- For [a model](hyp:V), the [closeness condition](goal) requires that the projected
conditional expectation of the difference between the minimum-norm solution and
each admissible primal function belongs to the critic class. -/
def ClosenessCondition : Prop := ∀ h ∈ V.H, projCondExpOp V (minNormSolution V - h) ∈ V.F

-- @node: ass:mean-sq-continuity
/-- For [a model](hyp:V), [mean-square continuity](goal) means that there is a real
constant C such that every admissible critic has [an integrable squared moment
contribution](step:1) and [an expected squared moment contribution bounded by C
times its squared norm](step:2). -/
def MeanSquareContinuity : Prop :=
  ∃ C : ℝ, ∀ f ∈ V.F, Integrable (fun w => V.m f w ^ 2) V.law ∧ (∫ w, V.m f w ^ 2 ∂V.law) ≤ C * ‖f‖ ^ 2

/-- For [a model](hyp:V), the [primal observation class](goal) consists of the
functions of an observation obtained by evaluating an admissible primal function
at its covariates. -/
noncomputable def primalObservationClass : Set (𝒲 → ℝ) :=
  {g | ∃ h ∈ V.H, g = fun w => primalVersion V h (V.xOf w)}
/-- For [a model](hyp:V), the [critic observation class](goal) consists of the
functions of an observation obtained by evaluating an admissible critic at its instruments. -/
noncomputable def criticObservationClass : Set (𝒲 → ℝ) :=
  {g | ∃ f ∈ V.F, g = fun w => dualVersion V f (V.zOf w)}
/-- For [a model](hyp:V), the [product observation class](goal) consists of
pointwise products of admissible primal values at the covariates and admissible
critic values at the instruments. -/
noncomputable def productObservationClass : Set (𝒲 → ℝ) :=
  {g | ∃ h ∈ V.H, ∃ f ∈ V.F,
    g = fun w => primalVersion V h (V.xOf w) * dualVersion V f (V.zOf w)}

/-- For [an observation law](hyp:law), [a class of vector-valued inputs](hyp:F),
[a reference input](hyp:v0), and [an observation-dependent loss](hyp:loss), the
[localized loss measurability requirement](goal) asks for [measurable reference
coordinates](step:1), [measurable class coordinates and loss increments](step:2),
and [measurable centered and randomly signed suprema at every positive sample
size and positive population L2 localization radius](step:3). -/
noncomputable def MeasurableLocalizedLoss {A : Type*} [MeasurableSpace A]
    {d : ℕ} (law : Measure A) (F : Set (A → Fin d → ℝ))
    (v0 : A → Fin d → ℝ) (loss : A → (Fin d → ℝ) → ℝ) : Prop :=
  (∀ i, Measurable (fun w => v0 w i)) ∧
  (∀ v ∈ F, (∀ i, Measurable (fun w => v w i)) ∧
    Measurable (fun w => loss w (v w) - loss w (v0 w))) ∧
  ∀ (n : ℕ), 0 < n → ∀ r : ℝ, 0 < r →
    let localized := {v : F //
      eLpNorm (fun w => Real.sqrt (∑ i, (v.1 w i - v0 w i) ^ 2)) 2 law ≤
        ENNReal.ofReal r}
    Measurable (fun x : Fin n → A => ⨆ v : localized,
      ENNReal.ofReal |(n : ℝ)⁻¹ * (∑ i,
        (loss (x i) (v.1.1 (x i)) - loss (x i) (v0 (x i)))) -
          ∫ w, (loss w (v.1.1 w) - loss w (v0 w)) ∂law|) ∧
    Measurable (fun p : (Fin n → A) × (Fin n → Bool) => ⨆ v : localized,
      ENNReal.ofReal |(n : ℝ)⁻¹ * ∑ i, (if p.2 i then (1 : ℝ) else -1) *
        (loss (p.1 i) (v.1.1 (p.1 i)) - loss (p.1 i) (v0 (p.1 i)))|)

/-- For [a model](hyp:V), the [three-coordinate TRAE loss class](goal) consists of
vectors whose coordinates are independently drawn from the star hulls of the
moment, primal–critic product, and critic observation classes, respectively. -/
noncomputable def traeLossClass : Set (𝒲 → Fin 3 → ℝ) :=
  {v | ∃ g1 ∈ starClass (momentImageClass V),
    ∃ g2 ∈ starClass (productObservationClass V),
    ∃ g3 ∈ starClass (criticObservationClass V),
      v = fun w => ![g1 w, g2 w, g3 w]}

/-- With [clipping threshold B](hyp:B), [an observation that does not affect the
value](hyp:_w), and [a three-coordinate input u](hyp:u), the [clipped TRAE loss](goal)
is twice the first coordinate minus twice the second coordinate minus the square
of the third coordinate clipped between −B and B. -/
def traeClippedLoss (B : ℝ) (_w : 𝒲) (u : Fin 3 → ℝ) : ℝ :=
  2 * u 0 - 2 * u 1 - (max (-B) (min (u 2) B)) ^ 2

/-- For [an observation law](hyp:law), [a vector-valued input class](hyp:F),
[a reference input](hyp:v0), [an observation-dependent loss](hyp:loss), and
[sample size n](hyp:n), the [fixed-sample localized measurability requirement](goal)
asks, at every positive population L2 radius around the reference, for
[measurability of the supremum of absolute centered loss increments](step:1)
and [measurability of the corresponding randomly signed supremum](step:2). -/
noncomputable def LocalizedSupremaMeasurableAt {A : Type*} [MeasurableSpace A]
    {d : ℕ} (law : Measure A) (F : Set (A → Fin d → ℝ))
    (v0 : A → Fin d → ℝ) (loss : A → (Fin d → ℝ) → ℝ) (n : ℕ) : Prop :=
  ∀ r : ℝ, 0 < r →
    let localized := {v : F //
      eLpNorm (fun w => Real.sqrt (∑ i, (v.1 w i - v0 w i) ^ 2)) 2 law ≤
        ENNReal.ofReal r}
    Measurable (fun x : Fin n → A => ⨆ v : localized,
      ENNReal.ofReal |(n : ℝ)⁻¹ * (∑ i,
        (loss (x i) (v.1.1 (x i)) - loss (x i) (v0 (x i)))) -
          ∫ w, (loss w (v.1.1 w) - loss w (v0 w)) ∂law|) ∧
    Measurable (fun p : (Fin n → A) × (Fin n → Bool) => ⨆ v : localized,
      ENNReal.ofReal |(n : ℝ)⁻¹ * ∑ i, (if p.2 i then (1 : ℝ) else -1) *
        (loss (p.1 i) (v.1.1 (p.1 i)) - loss (p.1 i) (v0 (p.1 i)))|)

/-- For [a model](hyp:V), [grid ratio ρ](hyp:ρ), [iteration limit t](hyp:t), and
[oracle radius sequence](hyp:oracleRadius), the [iterative fixed-center process
requirement](goal) asks for localized supremum measurability at every positive
sample size whose terminal grid value is below the oracle radius, every iteration
from one through t, and every grid penalty between the oracle point and two.
It uses [the current population iterate](step:1), [the preceding population
iterate](step:2), [the class of one-coordinate admissible primal observations](step:3),
and [the current iterate's observation function as localization anchor](step:4);
it requires measurability for squared losses centered at both iterates. -/
noncomputable def IterTRAEFixedCenterProcessesMeasurable (ρ : ℝ) (t : ℕ)
    (oracleRadius : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → gridValue ρ (terminalIndex ρ n) ≤ oracleRadius n →
    ∀ j : ℕ, 1 ≤ j → j ≤ t → ∀ lam ∈ regGrid ρ n,
    lam ∈ Set.Icc (oraclePoint ρ n (oracleRadius n)) 2 →
    let hj := populationIterate V lam j
    let center := populationIterate V lam (j - 1)
    let F := {u | ∃ h ∈ V.H,
      u = fun w => fun _ : Fin 1 => primalVersion V h (V.xOf w)}
    let anchor := fun w => fun _ : Fin 1 => primalVersion V hj (V.xOf w)
    LocalizedSupremaMeasurableAt V.law F anchor
      (fun w v => (v 0 - primalVersion V center (V.xOf w)) ^ 2) n ∧
    LocalizedSupremaMeasurableAt V.law F anchor
      (fun w v => (v 0 - primalVersion V hj (V.xOf w)) ^ 2) n

/-- For [a model](hyp:V) and [envelope B](hyp:B), the [base boundedness and
measurability requirement](goal) asserts [nonnegativity of B](step:1),
[a common almost-sure bound B for moment contributions](step:2),
[a common almost-sure bound B for primal values](step:3),
[a common almost-sure bound B for critic values](step:4),
[measurability of centered and signed squared-norm increment suprema localized
around the minimum-norm solution](step:5), and [localized measurability of the
three-coordinate clipped loss around zero](step:6). -/
noncomputable def traeBoundednessBase (B : ℝ) : Prop :=
  0 ≤ B ∧
  (∀ᵐ w ∂V.law, ∀ f ∈ V.F, |V.m f w| ≤ B) ∧
  (∀ᵐ w ∂V.law, ∀ h ∈ V.H, |primalVersion V h (V.xOf w)| ≤ B) ∧
  (∀ᵐ w ∂V.law, ∀ f ∈ V.F, |dualVersion V f (V.zOf w)| ≤ B) ∧
  (∀ n : ℕ, 0 < n → ∀ r : ℝ, 0 < r →
    Measurable (fun x : Fin n → 𝒲 =>
      ⨆ h : {h ∈ V.H | ‖h - minNormSolution V‖ ≤ r},
        ENNReal.ofReal |(n : ℝ)⁻¹ * (∑ i,
          (primalVersion V h.1 (V.xOf (x i)) ^ 2 -
            primalVersion V (minNormSolution V) (V.xOf (x i)) ^ 2)) -
          (∫ w, primalVersion V h.1 (V.xOf w) ^ 2 -
            primalVersion V (minNormSolution V) (V.xOf w) ^ 2 ∂V.law)|) ∧
    Measurable (fun p : (Fin n → 𝒲) × (Fin n → Bool) =>
      ⨆ h : {h ∈ V.H | ‖h - minNormSolution V‖ ≤ r},
        ENNReal.ofReal |(n : ℝ)⁻¹ * ∑ i,
          (if p.2 i then (1 : ℝ) else -1) *
            (primalVersion V h.1 (V.xOf (p.1 i)) ^ 2 -
              primalVersion V (minNormSolution V) (V.xOf (p.1 i)) ^ 2)|)) ∧
  MeasurableLocalizedLoss V.law (traeLossClass V) (fun _ => 0) (traeClippedLoss B)

/-- For [a model](hyp:V), [envelope B](hyp:B), and [an optional grid ratio,
iteration limit, and oracle radius sequence](hyp:iter), the [TRAE boundedness
requirement](goal) is [the base envelope and measurability requirement when no
iterative configuration is given](step:1), and [that base requirement together
with fixed-center iterative process measurability when a configuration is given](step:2). -/
-- @node: ass:critical-radius-boundedness
noncomputable def TRAEBoundedness (B : ℝ)
    (iter : Option (ℝ × ℕ × (ℕ → ℝ)) := none) : Prop :=
  match iter with
  | none => traeBoundednessBase V B
  | some (ρ, t, oracleRadius) =>
      traeBoundednessBase V B ∧ IterTRAEFixedCenterProcessesMeasurable V ρ t oracleRadius

/-- For [a model](hyp:V) and [envelope B](hyp:B), the [common-null-set boundedness
requirement](goal) asserts, outside one population null set, [the bound B on every
admissible primal value](step:1), [the bound B on every admissible critic value](step:2),
and [the bound B on every admissible moment contribution](step:3). -/
-- @node: ass:bk-owner-6
noncomputable def TRAECommonNullSetBoundedness (B : ℝ) : Prop :=
  ∀ᵐ w ∂V.law,
    (∀ h ∈ V.H, |primalVersion V h (V.xOf w)| ≤ B) ∧
    (∀ f ∈ V.F, |dualVersion V f (V.zOf w)| ≤ B) ∧
    (∀ f ∈ V.F, |V.m f w| ≤ B)

/-- For [sample size n](hyp:n) and [failure level ξ](hyp:ξ), the [confidence floor](goal)
is the square root of the quotient of log log(e n) + log(1/ξ) by n. -/
noncomputable def confidenceFloor (n : ℕ) (ξ : ℝ) : ℝ :=
  Real.sqrt ((Real.log (Real.log (Real.exp 1 * n)) + Real.log (1 / ξ)) / n)

/-- If [the sample size is positive](hyp:hn) and [the failure level lies strictly
between zero and one](hyp:hξ), then [log(1/ξ) is at most n times the squared
confidence floor](goal). -/
-- @node: confidenceFloor_log_le
lemma confidenceFloor_log_le (n : ℕ) (ξ : ℝ) (hn : 0 < n)
    (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1) :
    Real.log (1 / ξ) ≤ (n : ℝ) * confidenceFloor n ξ ^ 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnone : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnone
  have hinner : Real.log (Real.exp 1 * n) = 1 + Real.log (n : ℝ) := by
    rw [Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt hnpos), Real.log_exp]
  have hloglog : 0 ≤ Real.log (Real.log (Real.exp 1 * n)) := by
    apply Real.log_nonneg
    rw [hinner]
    linarith
  have hlogξ : 0 ≤ Real.log (1 / ξ) := by
    apply Real.log_nonneg
    exact (le_div_iff₀ hξ.1).2 (by linarith [hξ.2])
  unfold confidenceFloor
  rw [Real.sq_sqrt (div_nonneg (add_nonneg hloglog hlogξ) hnpos.le),
    mul_div_cancel₀ _ (ne_of_gt hnpos)]
  linarith

/-- If [the tail prefactor is positive](hyp:hc₁), [the exponential decay constant
is positive](hyp:hc₂), and [the confidence-floor multiplier is positive](hyp:hc),
then [there is a positive inflation constant K, uniform over positive sample
sizes and failure levels strictly between zero and one, such that whenever δ
dominates both c times the confidence floor and the inverse square root of n,
the tail c₁ exp(−c₂ n (K δ)²) is at most the failure level](goal). -/
-- @node: decayingTailConfidence
lemma decayingTailConfidence (c₁ c₂ c : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc : 0 < c) :
    ∃ K > 0, ∀ (n : ℕ) (ξ δ : ℝ), 0 < n → ξ ∈ Set.Ioo (0 : ℝ) 1 →
      c * confidenceFloor n ξ ≤ δ → (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ δ →
      c₁ * Real.exp (-c₂ * n * (K * δ) ^ 2) ≤ ξ := by
  let A := max (Real.log c₁) 0
  let D := A + (c ^ 2)⁻¹ + 1
  let K := Real.sqrt (D / c₂)
  have hA : 0 ≤ A := le_max_right _ _
  have hD : 0 < D := by dsimp [D]; positivity
  have hK : 0 < K := Real.sqrt_pos.2 (div_pos hD hc₂)
  have hKsq : c₂ * K ^ 2 = D := by
    dsimp [K]
    rw [Real.sq_sqrt (div_pos hD hc₂).le, mul_div_cancel₀ _ (ne_of_gt hc₂)]
  refine ⟨K, hK, ?_⟩
  intro n ξ δ hn hξ hfloor hsmall
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hδ : 0 ≤ δ := (Real.rpow_nonneg hnpos.le _).trans hsmall
  have hsmallSq : (n : ℝ)⁻¹ ≤ δ ^ 2 := by
    have heq : ((n : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = (n : ℝ)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
      norm_num [Real.rpow_neg_one]
    rw [← heq]
    nlinarith [Real.rpow_nonneg hnpos.le (-(1 / 2 : ℝ))]
  have hunit : 1 ≤ (n : ℝ) * δ ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hsmallSq hnpos.le
    simpa [ne_of_gt hnpos] using h
  have hfloorSq : c ^ 2 * confidenceFloor n ξ ^ 2 ≤ δ ^ 2 := by
    have hf : 0 ≤ confidenceFloor n ξ := Real.sqrt_nonneg _
    simpa only [mul_pow] using
      pow_le_pow_left₀ (mul_nonneg hc.le hf) hfloor 2
  have hlog := confidenceFloor_log_le n ξ hn hξ
  have hlogBound : Real.log (1 / ξ) ≤ (c ^ 2)⁻¹ * ((n : ℝ) * δ ^ 2) := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hc)).mp
    have hm := mul_le_mul_of_nonneg_left hfloorSq hnpos.le
    have hl := mul_le_mul_of_nonneg_right hlog (sq_nonneg c)
    field_simp
    nlinarith only [hm, hl]
  have hAunit := mul_le_mul_of_nonneg_left hunit hA
  have hbudget : Real.log c₁ + Real.log (1 / ξ) ≤ D * ((n : ℝ) * δ ^ 2) := by
    have hlogA : Real.log c₁ ≤ A := le_max_left _ _
    nlinarith only [hAunit, hlogBound, hlogA, hunit]
  have hexponent : Real.log c₁ + (-c₂ * n * (K * δ) ^ 2) ≤ Real.log ξ := by
    rw [Real.log_div one_ne_zero (ne_of_gt hξ.1), Real.log_one] at hbudget
    have heq : c₂ * n * (K * δ) ^ 2 = D * ((n : ℝ) * δ ^ 2) := by
      calc
        _ = (c₂ * K ^ 2) * ((n : ℝ) * δ ^ 2) := by ring
        _ = _ := by rw [hKsq]
    linarith
  calc
    c₁ * Real.exp (-c₂ * n * (K * δ) ^ 2) =
        Real.exp (Real.log c₁ + (-c₂ * n * (K * δ) ^ 2)) := by
      rw [Real.exp_add, Real.exp_log hc₁]
    _ ≤ Real.exp (Real.log ξ) := Real.exp_le_exp.mpr hexponent
    _ = ξ := Real.exp_log hξ.1

/-- If [the tail prefactor is positive](hyp:hc₁), [the exponential decay constant
is positive](hyp:hc₂), and [the confidence-floor multiplier is positive](hyp:hc),
then [there is an inflation constant K at least one such that, for every sample
size at least two and failure level strictly between zero and one, any radius r
above c times the confidence floor satisfies
2 c₁ exp(−c₂ n (K r)²) ≤ ξ](goal). -/
-- @node: localizedTailConfidence
lemma localizedTailConfidence (c₁ c₂ c : ℝ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc : 0 < c) :
    ∃ K ≥ (1 : ℝ), ∀ (n : ℕ) (ξ r : ℝ), 2 ≤ n →
      ξ ∈ Set.Ioo (0 : ℝ) 1 → c * confidenceFloor n ξ ≤ r →
      2 * c₁ * Real.exp (-c₂ * n * (K * r) ^ 2) ≤ ξ := by
  let m := Real.log (Real.log (Real.exp 1 * 2))
  have hinner : 1 < Real.log (Real.exp 1 * 2) := by
    have h := Real.log_lt_log (Real.exp_pos 1)
      (show Real.exp 1 < Real.exp 1 * 2 by linarith [Real.exp_pos 1])
    simpa only [Real.log_exp] using h
  have hm : 0 < m := Real.log_pos hinner
  let A := max (Real.log (2 * c₁)) 0
  let D := A / (c ^ 2 * m) + (c ^ 2)⁻¹ + 1
  let K := max 1 (Real.sqrt (D / c₂))
  have hA : 0 ≤ A := le_max_right _ _
  have hcSq : 0 < c ^ 2 := sq_pos_of_pos hc
  have hD : 0 < D := by dsimp [D]; positivity
  have hK : 1 ≤ K := le_max_left _ _
  have hKsq : D ≤ c₂ * K ^ 2 := by
    have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg (D / c₂))
      (le_max_right 1 (Real.sqrt (D / c₂))) 2
    rw [Real.sq_sqrt (div_pos hD hc₂).le] at hsq
    simpa only [K, mul_comm] using (div_le_iff₀ hc₂).mp hsq
  refine ⟨K, hK, ?_⟩
  intro n ξ r hn hξ hfloor
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hntwo : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hloglog : m ≤ Real.log (Real.log (Real.exp 1 * n)) := by
    apply Real.log_le_log (by linarith : 0 < Real.log (Real.exp 1 * 2))
    apply Real.log_le_log (by positivity)
    exact mul_le_mul_of_nonneg_left hntwo (Real.exp_pos 1).le
  have hlogξ : 0 ≤ Real.log (1 / ξ) := by
    apply Real.log_nonneg
    exact (le_div_iff₀ hξ.1).2 (by linarith [hξ.2])
  have henergy : m + Real.log (1 / ξ) ≤ (n : ℝ) * confidenceFloor n ξ ^ 2 := by
    unfold confidenceFloor
    rw [Real.sq_sqrt (div_nonneg (by linarith) hnpos.le),
      mul_div_cancel₀ _ (ne_of_gt hnpos)]
    linarith
  have hrSq : c ^ 2 * confidenceFloor n ξ ^ 2 ≤ r ^ 2 := by
    have hf : 0 ≤ confidenceFloor n ξ := Real.sqrt_nonneg _
    simpa only [mul_pow] using pow_le_pow_left₀
      (mul_nonneg hc.le hf) hfloor 2
  have hcombined : c ^ 2 * (m + Real.log (1 / ξ)) ≤ (n : ℝ) * r ^ 2 := by
    have h₁ := mul_le_mul_of_nonneg_left henergy hcSq.le
    have h₂ := mul_le_mul_of_nonneg_left hrSq hnpos.le
    nlinarith only [h₁, h₂]
  have hmEnergy : c ^ 2 * m ≤ (n : ℝ) * r ^ 2 := by
    nlinarith only [hcombined, mul_nonneg hcSq.le hlogξ]
  have hlogEnergy : Real.log (1 / ξ) ≤ (c ^ 2)⁻¹ * ((n : ℝ) * r ^ 2) := by
    apply (mul_le_mul_iff_right₀ hcSq).mp
    field_simp
    nlinarith only [hcombined, mul_pos hcSq hm]
  have hAEnergy : A ≤ A / (c ^ 2 * m) * ((n : ℝ) * r ^ 2) := by
    calc
      A = A / (c ^ 2 * m) * (c ^ 2 * m) := by
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hmEnergy (by positivity)
  have hbudget : Real.log (2 * c₁) + Real.log (1 / ξ) ≤ D * ((n : ℝ) * r ^ 2) := by
    have hlogA : Real.log (2 * c₁) ≤ A := le_max_left _ _
    nlinarith only [hAEnergy, hlogEnergy, hlogA, mul_nonneg hnpos.le (sq_nonneg r)]
  have hdecay : D * ((n : ℝ) * r ^ 2) ≤ c₂ * n * (K * r) ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hKsq
      (mul_nonneg hnpos.le (sq_nonneg r))
    nlinarith only [h]
  have hexponent : Real.log (2 * c₁) + (-c₂ * n * (K * r) ^ 2) ≤ Real.log ξ := by
    rw [Real.log_div one_ne_zero (ne_of_gt hξ.1), Real.log_one] at hbudget
    linarith only [hbudget, hdecay]
  calc
    2 * c₁ * Real.exp (-c₂ * n * (K * r) ^ 2) =
        Real.exp (Real.log (2 * c₁) + (-c₂ * n * (K * r) ^ 2)) := by
      rw [Real.exp_add, Real.exp_log (by positivity : 0 < 2 * c₁)]
    _ ≤ Real.exp (Real.log ξ) := Real.exp_le_exp.mpr hexponent
    _ = ξ := Real.exp_log hξ.1

/-- If [the tail prefactor is positive](hyp:hc₁), [the decay constant is
positive](hyp:hc₂), and [the dimension is at least one](hyp:hd), then [the minimum
of c₂ d²/(1 + 2d) and c₂/(4d) is positive, and the sum of the two exponential
tails with these decay rates is at most twice the tail with their minimum rate,
for every sample size and radius](goal). -/
-- @node: localizedSignedTailUnion
lemma localizedSignedTailUnion (c₁ c₂ : ℝ) (d n : ℕ) (r : ℝ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hd : 1 ≤ d) :
    let cstar := min (c₂ * (d : ℝ) ^ 2 / (1 + 2 * d)) (c₂ / (4 * d))
    0 < cstar ∧
      c₁ * Real.exp (-(c₂ * (d : ℝ) ^ 2 / (1 + 2 * d)) * n * r ^ 2) +
        c₁ * Real.exp (-(c₂ / (4 * d)) * n * r ^ 2) ≤
          2 * c₁ * Real.exp (-cstar * n * r ^ 2) := by
  dsimp only
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  constructor
  · apply lt_min <;> positivity
  · have hleft :
        c₁ * Real.exp (-(c₂ * (d : ℝ) ^ 2 / (1 + 2 * d)) * n * r ^ 2) ≤
        c₁ * Real.exp (-min (c₂ * (d : ℝ) ^ 2 / (1 + 2 * d))
          (c₂ / (4 * d)) * n * r ^ 2) := by
      gcongr
      exact min_le_left _ _
    have hright :
        c₁ * Real.exp (-(c₂ / (4 * d)) * n * r ^ 2) ≤
        c₁ * Real.exp (-min (c₂ * (d : ℝ) ^ 2 / (1 + 2 * d))
          (c₂ / (4 * d)) * n * r ^ 2) := by
      gcongr
      exact min_le_right _ _
    linarith

/-- If [the decay constant c₂ is positive](hyp:hc₂) and [the sample size n is
positive](hyp:hn), then [log(41 log(2 c₂ n)) is at most
log(41 (|log(2 c₂)| + 1)) plus log log(e n)](goal). -/
-- @node: peelingLog_le
lemma peelingLog_le (c₂ : ℝ) (hc₂ : 0 < c₂) (n : ℕ) (hn : 0 < n) :
    Real.log (41 * Real.log (2 * c₂ * n)) ≤
      Real.log (41 * (|Real.log (2 * c₂)| + 1)) +
        Real.log (Real.log (Real.exp 1 * n)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hlogn : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hinner : Real.log (Real.exp 1 * n) = 1 + Real.log (n : ℝ) := by
    rw [Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt hnpos), Real.log_exp]
  have hA : 0 < |Real.log (2 * c₂)| + 1 := by positivity
  have hL : 0 < Real.log (Real.exp 1 * n) := by rw [hinner]; positivity
  have hb : |Real.log (2 * c₂ * n)| ≤
      (|Real.log (2 * c₂)| + 1) * Real.log (Real.exp 1 * n) := by
    rw [Real.log_mul (by positivity) (ne_of_gt hnpos), hinner]
    calc
      |Real.log (2 * c₂) + Real.log (n : ℝ)| ≤
          |Real.log (2 * c₂)| + |Real.log (n : ℝ)| := abs_add_le _ _
      _ ≤ _ := by rw [abs_of_nonneg hlogn]; nlinarith [abs_nonneg (Real.log (2 * c₂))]
  by_cases hz : Real.log (2 * c₂ * n) = 0
  · rw [hz, mul_zero, Real.log_zero]
    exact add_nonneg (Real.log_nonneg (by nlinarith [abs_nonneg (Real.log (2 * c₂))]))
      (Real.log_nonneg (by rw [hinner]; linarith))
  · calc
      Real.log (41 * Real.log (2 * c₂ * n)) =
          Real.log |41 * Real.log (2 * c₂ * n)| := (Real.log_abs _).symm
      _ ≤ Real.log ((41 * (|Real.log (2 * c₂)| + 1)) *
          Real.log (Real.exp 1 * n)) := by
        apply Real.log_le_log (abs_pos.mpr (mul_ne_zero (by norm_num) hz))
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 41)]
        nlinarith only [hb]
      _ = _ := Real.log_mul (by positivity) (ne_of_gt hL)

/-- If [the decay constant is positive](hyp:hc₂), [the confidence-floor multiplier
is positive](hyp:hc), and [the dimension is at least one](hyp:hd), then [there
is a constant K at least one such that, for every positive sample size and
failure level strictly between zero and one, a radius r dominating both c times
the confidence floor and the inverse square root of n satisfies
4d log(41 log(2 c₂ n))/(c₂ n) ≤ (K r)²](goal). -/
-- @node: localizedPeelingRadiusWithFloor
lemma localizedPeelingRadiusWithFloor (c₂ c : ℝ) (d : ℕ)
    (hc₂ : 0 < c₂) (hc : 0 < c) (hd : 1 ≤ d) :
    ∃ K ≥ (1 : ℝ), ∀ (n : ℕ) (ξ r : ℝ), 0 < n →
      ξ ∈ Set.Ioo (0 : ℝ) 1 → c * confidenceFloor n ξ ≤ r →
      (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ r →
      4 * d * Real.log (41 * Real.log (2 * c₂ * n)) / (c₂ * n) ≤
        (K * r) ^ 2 := by
  let D := Real.log (41 * (|Real.log (2 * c₂)| + 1))
  let Q := 4 * d / c₂ * (D + (c ^ 2)⁻¹)
  let K := Real.sqrt (Q + 1)
  have hD : 0 ≤ D := Real.log_nonneg (by
    nlinarith [abs_nonneg (Real.log (2 * c₂))])
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hK : 1 ≤ K := by
    dsimp [K]
    exact (Real.le_sqrt (by norm_num) (by positivity)).2 (by nlinarith)
  have hKsq : K ^ 2 = Q + 1 := Real.sq_sqrt (by positivity)
  refine ⟨K, hK, ?_⟩
  intro n ξ r hn hξ hfloor hsmall
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnone : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : 0 ≤ r := (Real.rpow_nonneg hnpos.le _).trans hsmall
  have hsmallSq : (n : ℝ)⁻¹ ≤ r ^ 2 := by
    have heq : ((n : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = (n : ℝ)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
      norm_num [Real.rpow_neg_one]
    rw [← heq]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hnpos.le _) hsmall 2
  have hunit : 1 ≤ (n : ℝ) * r ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hsmallSq hnpos.le
    simpa [ne_of_gt hnpos] using hm
  have hlogξ : 0 ≤ Real.log (1 / ξ) :=
    Real.log_nonneg ((le_div_iff₀ hξ.1).2 (by linarith [hξ.2]))
  have hL : 0 ≤ Real.log (Real.log (Real.exp 1 * n)) := by
    apply Real.log_nonneg
    rw [Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt hnpos), Real.log_exp]
    linarith [Real.log_nonneg hnone]
  have hfloorEq : (n : ℝ) * confidenceFloor n ξ ^ 2 =
      Real.log (Real.log (Real.exp 1 * n)) + Real.log (1 / ξ) := by
    unfold confidenceFloor
    rw [Real.sq_sqrt (div_nonneg (add_nonneg hL hlogξ) hnpos.le),
      mul_div_cancel₀ _ (ne_of_gt hnpos)]
  have hfloorSq : c ^ 2 * confidenceFloor n ξ ^ 2 ≤ r ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀
      (mul_nonneg hc.le (show 0 ≤ confidenceFloor n ξ from Real.sqrt_nonneg _)) hfloor 2
  have hlogBound : Real.log (Real.log (Real.exp 1 * n)) ≤
      (c ^ 2)⁻¹ * ((n : ℝ) * r ^ 2) := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hc)).mp
    have hm := mul_le_mul_of_nonneg_left hfloorSq hnpos.le
    have he : c ^ 2 * ((c ^ 2)⁻¹ * ((n : ℝ) * r ^ 2)) = (n : ℝ) * r ^ 2 := by
      field_simp
    rw [he]
    nlinarith only [hm, hfloorEq, mul_nonneg (sq_nonneg c) hlogξ]
  have hlog := peelingLog_le c₂ hc₂ n hn
  have hbudget : Real.log (41 * Real.log (2 * c₂ * n)) ≤
      (D + (c ^ 2)⁻¹) * ((n : ℝ) * r ^ 2) := by
    have hDu := mul_le_mul_of_nonneg_left hunit hD
    change Real.log (41 * Real.log (2 * c₂ * n)) ≤ D + _ at hlog
    nlinarith only [hlog, hlogBound, hDu]
  apply (div_le_iff₀ (mul_pos hc₂ hnpos)).2
  rw [mul_pow, hKsq]
  have hm := mul_le_mul_of_nonneg_left hbudget (by positivity : (0 : ℝ) ≤ 4 * d)
  have he : Q * r ^ 2 * (c₂ * n) =
      4 * d * ((D + (c ^ 2)⁻¹) * ((n : ℝ) * r ^ 2)) := by
    dsimp [Q]
    field_simp
    <;> ring
  nlinarith only [hm, he, mul_nonneg (sq_nonneg r) (mul_pos hc₂ hnpos).le]

/-- If [the decay constant is positive](hyp:hc₂), [the confidence-floor multiplier
is positive](hyp:hc), and [the dimension is at least one](hyp:hd), then [there
is a constant K at least one such that, for every sample size at least two and
failure level strictly between zero and one, every radius r above c times the
confidence floor satisfies 4d log(41 log(2 c₂ n))/(c₂ n) ≤ (K r)²](goal). -/
-- @node: localizedPeelingRadius
lemma localizedPeelingRadius (c₂ c : ℝ) (d : ℕ)
    (hc₂ : 0 < c₂) (hc : 0 < c) (hd : 1 ≤ d) :
    ∃ K ≥ (1 : ℝ), ∀ (n : ℕ) (ξ r : ℝ), 2 ≤ n →
      ξ ∈ Set.Ioo (0 : ℝ) 1 → c * confidenceFloor n ξ ≤ r →
      4 * d * Real.log (41 * Real.log (2 * c₂ * n)) / (c₂ * n) ≤
        (K * r) ^ 2 := by
  let L := Real.log (Real.log (Real.exp 1 * 2))
  have hL : 0 < L := by
    apply Real.log_pos
    rw [Real.log_mul (ne_of_gt (Real.exp_pos _)) (by norm_num), Real.log_exp]
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  let H := max 1 (c * Real.sqrt L)⁻¹
  have hH : 1 ≤ H := le_max_left _ _
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hscale : 1 ≤ H * (c * Real.sqrt L) := by
    have hp : 0 < c * Real.sqrt L := mul_pos hc (Real.sqrt_pos.2 hL)
    have hm := mul_le_mul_of_nonneg_right (le_max_right 1 (c * Real.sqrt L)⁻¹) hp.le
    simpa only [inv_mul_cancel₀ (ne_of_gt hp)] using hm
  obtain ⟨K, hK, hbound⟩ := localizedPeelingRadiusWithFloor c₂ c d hc₂ hc hd
  refine ⟨K * H, one_le_mul_of_one_le_of_one_le hK hH, ?_⟩
  intro n ξ r hn hξ hfloor
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hr : 0 ≤ r := (mul_nonneg hc.le (Real.sqrt_nonneg _)).trans hfloor
  have hlogξ : 0 ≤ Real.log (1 / ξ) :=
    Real.log_nonneg ((le_div_iff₀ hξ.1).2 (by linarith [hξ.2]))
  have hlog : L ≤ Real.log (Real.log (Real.exp 1 * n)) := by
    apply Real.log_le_log
    · rw [Real.log_mul (ne_of_gt (Real.exp_pos _)) (by norm_num), Real.log_exp]
      linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    · apply Real.log_le_log (by positivity)
      gcongr
      exact_mod_cast hn
  have hroot : Real.sqrt L * (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ confidenceFloor n ξ := by
    calc
      _ = Real.sqrt (L / n) := by
        rw [Real.sqrt_div hL.le, Real.rpow_neg hnpos.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]
      _ ≤ _ := Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (by linarith) hnpos.le)
  have hsmall : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ H * r := by
    have hm := mul_le_mul_of_nonneg_left hroot hc.le
    have hh := mul_le_mul_of_nonneg_left (hm.trans hfloor) hHpos.le
    have hu := mul_le_mul_of_nonneg_right hscale
      (Real.rpow_nonneg hnpos.le (-(1 / 2 : ℝ)))
    nlinarith only [hh, hu]
  have hrH : r ≤ H * r := by nlinarith only [hH, hr]
  simpa only [mul_assoc] using hbound n ξ (H * r) (by omega) hξ
    (hfloor.trans hrH) hsmall

/-- If [B is nonnegative](hyp:hB), [the absolute value of u is at most B](hyp:hu),
and [the absolute value of v is at most B](hyp:hv), then [the absolute difference
of their squares is at most 2B times their absolute difference](goal). -/
-- @node: localizedSquaredLossLipschitz
lemma localizedSquaredLossLipschitz (B u v : ℝ) (hB : 0 ≤ B)
    (hu : |u| ≤ B) (hv : |v| ≤ B) :
    |u ^ 2 - v ^ 2| ≤ 2 * B * |u - v| := by
  calc
    |u ^ 2 - v ^ 2| = |u - v| * |u + v| := by
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ |u - v| * (|u| + |v|) :=
      mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using norm_add_le u v)
        (abs_nonneg _)
    _ ≤ |u - v| * (B + B) := by gcongr
    _ = 2 * B * |u - v| := by ring

/-- If [r is a valid critical-radius bound for the function class under the
observation law at sample size n](hyp:hr) and [R is at least r](hyp:hR), then
[R is also a valid critical-radius bound for that class, law, and sample size](goal). -/
-- @node: criticalRadiusBound_mono
lemma criticalRadiusBound_mono {A : Type*} [MeasurableSpace A]
    (law : Measure A) (F : Set (A → ℝ)) (n : ℕ) (r R : ℝ)
    (hr : IsCriticalRadiusBound law F n r) (hR : r ≤ R) :
    IsCriticalRadiusBound law F n R := by
  have hrpos := hr.1
  have hRpos := hrpos.trans_le hR
  let a := r / R
  let c := R / r
  have ha : 0 < a := div_pos hrpos hRpos
  have ha1 : a ≤ 1 := (div_le_one hRpos).2 hR
  have hc : 0 ≤ c := (div_pos hRpos hrpos).le
  have hca : c * a = 1 := by dsimp [c, a]; field_simp
  let Fr := {f ∈ starClass (differenceClass F) | eLpNorm f 2 law ≤ ENNReal.ofReal r}
  let FR := {f ∈ starClass (differenceClass F) | eLpNorm f 2 law ≤ ENNReal.ofReal R}
  have hscaled (f : FR) : a • f.1 ∈ Fr := by
    obtain ⟨⟨b, hb, g, hg, heq⟩, hnorm⟩ := f.2
    constructor
    · refine ⟨a * b, ⟨mul_nonneg ha.le hb.1, ?_⟩, g, hg, ?_⟩
      · exact (mul_le_mul_of_nonneg_right ha1 hb.1).trans (by simpa using hb.2)
      · rw [heq, smul_smul]
    · rw [eLpNorm_const_smul, Real.enorm_eq_ofReal ha.le]
      calc
        _ ≤ ENNReal.ofReal a * ENNReal.ofReal R := mul_le_mul_of_nonneg_left hnorm zero_le
        _ = ENNReal.ofReal r := by
          rw [← ENNReal.ofReal_mul ha.le]
          congr 1
          dsimp [a]
          field_simp
  have hsup (x : Fin n → A) (ε : Fin n → Bool) :
      signedSupremum FR n x ε ≤ ENNReal.ofReal c * signedSupremum Fr n x ε := by
    apply iSup_le
    intro f
    let g : Fr := ⟨a • f.1, hscaled f⟩
    have hid : |(n : ℝ)⁻¹ * ∑ i, (if ε i then (1 : ℝ) else -1) * f.1 (x i)| =
        c * |(n : ℝ)⁻¹ * ∑ i, (if ε i then (1 : ℝ) else -1) * g.1 (x i)| := by
      have hg : (n : ℝ)⁻¹ * ∑ i, (if ε i then (1 : ℝ) else -1) * g.1 (x i) =
          a * ((n : ℝ)⁻¹ * ∑ i, (if ε i then (1 : ℝ) else -1) * f.1 (x i)) := by
        dsimp [g]
        simp_rw [mul_left_comm (if ε _ then (1 : ℝ) else -1) a]
        rw [← Finset.mul_sum]
        ring
      rw [hg, abs_mul a, abs_of_pos ha, ← mul_assoc, hca, one_mul]
    rw [hid, ENNReal.ofReal_mul hc]
    exact mul_le_mul_of_nonneg_left (le_iSup (fun g : Fr => ENNReal.ofReal
      |(n : ℝ)⁻¹ * ∑ i, (if ε i then (1 : ℝ) else -1) * g.1 (x i)|) g) zero_le
  have hexpect : expectedRademacher law FR n ≤ ENNReal.ofReal c * expectedRademacher law Fr n := by
    unfold expectedRademacher
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro x
    calc
      _ ≤ (2 ^ n : ℝ≥0∞)⁻¹ * ∑ ε : Fin n → Bool,
          ENNReal.ofReal c * signedSupremum Fr n x ε := by
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ε _ => hsup x ε) zero_le
      _ = _ := by rw [← Finset.mul_sum]; ac_rfl
  refine ⟨hRpos, hexpect.trans ?_⟩
  calc
    ENNReal.ofReal c * expectedRademacher law Fr n ≤
        ENNReal.ofReal c * ENNReal.ofReal (r ^ 2) := mul_le_mul_of_nonneg_left hr.2 zero_le
    _ = ENNReal.ofReal (R * r) := by
      rw [← ENNReal.ofReal_mul hc]
      congr 1
      dsimp [c]
      field_simp
    _ ≤ ENNReal.ofReal (R ^ 2) := ENNReal.ofReal_le_ofReal (by nlinarith)


-- @node: ass:critical-radius-complexity
/-- For [a model](hyp:V) and [a sample-size and confidence dependent radius
bound](hyp:tildeδ), the [TRAE critical-radius requirement](goal) asserts that a
single positive constant works at every positive sample size and failure level
strictly between zero and one: the radius [dominates that constant times the
confidence floor](step:1) and bounds the critical radii of [the star hull of
primal–critic products](step:2), [the star hull of moment contributions](step:3),
[the star hull of critic observations](step:4), [the star hull of primal
observations](step:5), and [the star hull of differences of primal observations](step:6). -/
noncomputable def TRAECriticalRadiusBound (tildeδ : ℕ → ℝ → ℝ) : Prop :=
  ∃ c > 0, ∀ n : ℕ, 0 < n → ∀ ξ ∈ Set.Ioo (0 : ℝ) 1,
    c * confidenceFloor n ξ ≤ tildeδ n ξ ∧
    IsCriticalRadiusBound V.law (starClass (productObservationClass V)) n (tildeδ n ξ) ∧
    IsCriticalRadiusBound V.law (starClass (momentImageClass V)) n (tildeδ n ξ) ∧
    IsCriticalRadiusBound V.law (starClass (criticObservationClass V)) n (tildeδ n ξ) ∧
    IsCriticalRadiusBound V.law (starClass (primalObservationClass V)) n (tildeδ n ξ) ∧
    IsCriticalRadiusBound V.law (starClass (differenceClass (primalObservationClass V))) n (tildeδ n ξ)
    -- @realizes \tilde\delta_n(confidence-indexed upper bounds for all five star classes)

-- @node: ass:delta-trae
/-- For [an accuracy sequence δ](hyp:δ), [a confidence-indexed critical-radius
bound](hyp:tildeδ), and [a failure-allocation sequence](hyp:allocation), the
[TRAE scale calibration](goal) requires that [at every positive sample size δ
dominates both the allocated critical-radius bound and the inverse square root
of the sample size](step:1), and [δ tends to zero](step:2). -/
noncomputable def TRAEScaleCalibration (δ : ℕ → ℝ) (tildeδ : ℕ → ℝ → ℝ)
    (allocation : ℕ → ℝ) : Prop :=
  (∀ n : ℕ, 0 < n → max (tildeδ n (allocation n)) ((n : ℝ) ^ (-(1 / 2 : ℝ))) ≤ δ n) ∧
  Tendsto δ atTop (𝓝 0)

-- @node: ass:trae-minima
/-- For [a model](hyp:V), [sampling law](hyp:P), [analysis sample](hyp:sample),
[sample split](hyp:split), [grid ratio ρ](hyp:ρ), and [a family of candidate
estimators indexed by sample size and penalty](hyp:candidate), the [attained-minima
requirement](goal) says that at every positive sample size and grid penalty,
[the candidate minimizes the penalized empirical TRAE objective](step:1),
[the candidate is measurable](step:2), and [the empirical loss of every fixed
admissible primal function is measurable](step:3). -/
noncomputable def TRAEMinimaAttained (ρ : ℝ)
    (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ lam ∈ regGrid ρ n,
    IsTRAEEstimator V P sample split n lam (candidate n lam) ∧
    (@Measurable Ω V.Hbar.toSubmodule inferInstance (borel _) (candidate n lam)) ∧
    (∀ h ∈ V.H, Measurable
      (fun ω => traeEmpiricalLoss V P sample split n ω h))

-- @node: def:trae-common-scales
/-- For [an accuracy scale δ](hyp:δ) and [a penalty argument that does not affect
the value](hyp:_lam), the [TRAE noise level](goal) is δ squared. -/
def traeNoiseLevel (δ _lam : ℝ) : ℝ := δ ^ 2 -- @realizes A_n^{\mathrm T}(nonnegative constant delta squared, independent of lambda)
/-- For [an accuracy scale δ](hyp:δ) and [penalty λ](hyp:lam), the [TRAE stability
scale](goal) is δ squared divided by λ. -/
noncomputable def traeStability (δ lam : ℝ) : ℝ := δ ^ 2 / lam
  -- @realizes V_n^{\mathrm T}(adversarial stability scale)

-- @node: def:trae-oracle-point
/-- For [grid ratio ρ](hyp:ρ), [balancing constant c](hyp:c), [source exponent β](hyp:β),
[accuracy sequence δ](hyp:δ), and [sample size n](hyp:n), the [TRAE oracle penalty](goal)
is the oracle grid point for radius c times δ at n raised to two divided by the
bias exponent associated with β. -/
noncomputable def traeOraclePoint (ρ c β : ℝ) (δ : ℕ → ℝ) (n : ℕ) : ℝ :=
  oraclePoint ρ n (c * δ n ^ (2 / biasExponent β))
  -- @realizes \lambda_{\mathrm T}^\circ(first grid point below the balancing radius)

-- @node: def:trae-minimum-size
/-- For [envelope B](hyp:B), the [minimum TRAE sample size](goal) is the larger
of two and the natural-number ceiling of twice B squared. -/
noncomputable def traeMinSampleSize (B : ℝ) : ℕ := max 2 ⌈2 * B ^ 2⌉₊
  -- @realizes N_{\mathrm T}(B)(TRAE sample-size threshold)

/-- For [a model](hyp:V), [sampling law](hyp:P), [analysis sample](hyp:sample),
[sample split](hyp:split), [accuracy sequence δ](hyp:δ), [sample size n](hyp:n),
[an event E](hyp:E), and [comparison constant C](hyp:C), the [common TRAE
comparison requirement on E](goal) asserts at every outcome in E that
[empirical adversarial loss lies between one half of population loss minus Cδ²
and five quarters of population loss plus Cδ² for all admissible functions](step:1),
[squared-norm increments relative to the minimum-norm solution differ from
their population counterparts by at most C times the sum of δ times the distance
to that solution and δ²](step:2), [the empirical loss at the minimum-norm solution is
at most Cδ²](step:3), and [the outcome belongs to the sample zero event](step:4). -/
noncomputable def TRAEComparisonsOn (δ : ℕ → ℝ) (n : ℕ) (E : Set Ω) (C : ℝ) : Prop :=
  ∀ ω ∈ E, -- @realizes \mathcal E_n(common loss, squared-norm, and h₀-loss comparison event)
    (∀ h ∈ V.H,
      (1 / 2 : ℝ) * traePopulationLoss V h - C * δ n ^ 2 ≤
        traeEmpiricalLoss V P sample split n ω h ∧
      traeEmpiricalLoss V P sample split n ω h ≤
        (5 / 4 : ℝ) * traePopulationLoss V h + C * δ n ^ 2) ∧
    (∀ h ∈ V.H,
      |(primalEmpSq V P sample split n ω h - primalEmpSq V P sample split n ω (minNormSolution V)) -
        (‖h‖ ^ 2 - ‖minNormSolution V‖ ^ 2)| ≤
      C * (δ n * ‖h - minNormSolution V‖ + δ n ^ 2)) ∧
    traeEmpiricalLoss V P sample split n ω (minNormSolution V) ≤ C * δ n ^ 2 ∧
    ω ∈ sampleZeroEvent V P sample

-- @node: def:trae-discrepancy-bound
/-- For [a model](hyp:V), [sampling law](hyp:P), [analysis sample](hyp:sample),
[sample split](hyp:split), [grid ratio ρ](hyp:ρ), [source exponent β](hyp:β),
[accuracy sequence δ](hyp:δ), [source element w₀](hyp:w₀), [candidate estimator
family](hyp:candidate), [sample size n](hyp:n), [event E](hyp:E), and [constant C](hyp:C),
the [TRAE discrepancy envelope](goal) requires [C to be positive](step:1) and,
at every outcome in E, [the empirical loss of the minimum-norm solution to be
at most δ² and each grid candidate's empirical loss to be at most δ² plus
C times the squared norm of w₀ times the penalty raised to the bias exponent](step:2). -/
noncomputable def TRAEDiscrepancyEnvelope (ρ β : ℝ) (δ : ℕ → ℝ)
    (w₀ : V.Hbar.toSubmodule) (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (n : ℕ) (E : Set Ω) (C : ℝ) : Prop :=
  0 < C ∧ ∀ ω ∈ E, traeEmpiricalLoss V P sample split n ω (minNormSolution V) ≤ δ n ^ 2 ∧
    ∀ lam ∈ regGrid ρ n, traeEmpiricalLoss V P sample split n ω (candidate n lam ω) ≤
      δ n ^ 2 + C * ‖w₀‖ ^ 2 * lam ^ biasExponent β

-- @node: def:trae-oracle-scales
/-- For [grid ratio ρ](hyp:ρ), [balancing constant c](hyp:c), [source exponent β](hyp:β),
and [accuracy sequence δ](hyp:δ), the [TRAE oracle scale requirement](goal) asserts
[that the noise level at the oracle penalty equals δ² at every sample size](step:1)
and [that some positive constant eventually bounds oracle stability by δ raised
to the power (2b − 2)/b, where b is the bias exponent associated with β](step:2). -/
noncomputable def TRAEOracleScales (ρ c β : ℝ) (δ : ℕ → ℝ) : Prop :=
  (∀ n, traeNoiseLevel (δ n) (traeOraclePoint ρ c β δ n) = δ n ^ 2) ∧
  ∃ C > 0, ∀ᶠ n in atTop,
    traeStability (δ n) (traeOraclePoint ρ c β δ n) ≤
      C * δ n ^ (2 * (biasExponent β - 1) / biasExponent β)

/-- For [a model](hyp:V), the [localized TRAE concentration assertion](goal) says
that any envelope and confidence-indexed radius bound satisfying the range,
closeness, mean-square continuity, boundedness, common-null-set, and critical-radius
conditions admit a positive constant C uniform over calibrated accuracy and
failure-allocation sequences. At every positive sample size with allocation
strictly between zero and one, there is an event under the independent product
population law that [is measurable](step:1), [has probability at least one minus
the allocation](step:2), and [bounds every admissible primal–critic pair's absolute
clipped-loss deviation by C times the sum of the accuracy multiplied by its
three population L2 coordinate norms and the squared accuracy](step:3).

Bennett, Kallus, Mao, Newey, Syrgkanis and Uehara (2023),
`bennett2023source`, arXiv:2307.13793, Lemma 9 (`lem:concentration`),
as used in both directions in appendices.tex:630–654. This carrier records
simultaneous absolute concentration for the bounded three-coordinate clipped
loss, anchored at zero. Its remainder retains the sum of the population L2
coordinate norms. Clipping, coordinate-norm conversion, residual feasibility,
population identities and empirical supremum comparisons are local obligations.
The standing inverse-problem, closeness, continuity, boundedness, complexity and
calibration hypotheses are explicit. Its constant precedes the requested
accuracy and confidence allocations. The empirical average uses the canonical
n-tuple of iid observations under the product population law. No feasibility,
population-loss identity, empirical-supremum domination or final loss bound is
assumed by this carrier. It quantifies the paper-calibrated vanishing scales,
including their inverse-square-root floor, rather than arbitrary radii. -/
-- @node: lem:trae-localized-concentration-lemma-9
noncomputable def TRAELocalizedConcentration : Sort 0 :=
  ∀ (B : ℝ) (tildeδ : ℕ → ℝ → ℝ),
    RangeCondition V → ClosenessCondition V → MeanSquareContinuity V →
    TRAEBoundedness V B → TRAECommonNullSetBoundedness V B → TRAECriticalRadiusBound V tildeδ →
    ∃ C > 0, ∀ (δ : ℕ → ℝ) (allocation : ℕ → ℝ),
    TRAEScaleCalibration δ tildeδ allocation →
    ∀ (n : ℕ), 0 < n → allocation n ∈ Set.Ioo (0 : ℝ) 1 →
    ∃ E : Set (Fin n → 𝒲), MeasurableSet E ∧
      1 - allocation n ≤ (Measure.pi (fun _ : Fin n => V.law)).real E ∧
      ∀ x ∈ E, ∀ h ∈ V.H, ∀ f ∈ V.F,
        let u := fun w => ![V.m f w,
          primalVersion V h (V.xOf w) * dualVersion V f (V.zOf w),
          dualVersion V f (V.zOf w)]
        |(n : ℝ)⁻¹ * (∑ i, traeClippedLoss B (x i) (u (x i))) -
          (∫ w, traeClippedLoss B w (u w) ∂V.law)| ≤
          C * (δ n * (∑ i : Fin 3, inputL2Norm V.law (fun w => u w i)) + δ n ^ 2)

/-- For [an envelope bound B](hyp:B), the [normalized squared-norm scalar
loss](goal) clips its argument to the interval $[-1,1]$, squares it, and
multiplies by the square of the larger of one and B. -/
-- keep: Named realization of the paper's locally bound scalar loss ℓ; the cited squared-norm carrier records its resulting comparison.
def traeSquaredNormLoss (B : ℝ) : ℝ → ℝ := -- @realizes \ell(real scalar loss M² times the square of clipping to [-1,1], M=max(1,B))
  fun u => (max 1 B) ^ 2 * (max (-1) (min u 1)) ^ 2

/-- For [a model](hyp:V), [a normalization scale s](hyp:s), and [a scalar loss
function](hyp:loss), the [localized scalar-loss measurability requirement](goal)
uses, at every positive sample size and radius, [the admissible primal functions
whose normalized observations are within that radius of the minimum-norm
solution in population L2 distance](step:1) and [their loss increments relative
to that solution](step:2). It requires [the supremum of absolute centered
empirical increments to be almost everywhere measurable under independent
population sampling](step:3) and [the supremum of absolute randomly signed
empirical increments to be almost everywhere measurable under that sampling
law with independent uniform signs](step:4). -/
noncomputable def MeasurableLocalizedScalarLoss (s : ℝ) (loss : ℝ → ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ r : ℝ, 0 < r →
    let localized := {h ∈ V.H |
      inputL2Norm V.law (fun w => primalVersion V h (V.xOf w) / s -
        primalVersion V (minNormSolution V) (V.xOf w) / s) ≤ r}
    let increment := fun (h : V.Hbar.toSubmodule) w =>
      loss (primalVersion V h (V.xOf w) / s) -
        loss (primalVersion V (minNormSolution V) (V.xOf w) / s)
    AEMeasurable (fun x : Fin n → 𝒲 => ⨆ h : localized,
      ENNReal.ofReal |(n : ℝ)⁻¹ * (∑ i, increment h.1 (x i)) -
        ∫ w, increment h.1 w ∂V.law|) (Measure.pi (fun _ => V.law)) ∧
    AEMeasurable (fun p : (Fin n → 𝒲) × (Fin n → Bool) => ⨆ h : localized,
      ENNReal.ofReal |(n : ℝ)⁻¹ * ∑ i,
        (if p.2 i then (1 : ℝ) else -1) * increment h.1 (p.1 i)|)
      ((Measure.pi (fun _ => V.law)).prod
        ((2 ^ n : ℝ≥0∞)⁻¹ • (Measure.count : Measure (Fin n → Bool))))

/-- For [a model](hyp:V), [a sampling law](hyp:P), [an analysis sample](hyp:sample),
and [a sample split](hyp:split), the [localized squared-norm concentration
requirement](goal) says that, when the sampling law is a probability measure,
every envelope and confidence-indexed radius bound satisfying boundedness,
common-null-set boundedness, and the critical-radius requirement admit a
positive comparison constant uniform over accuracy and failure-allocation
sequences. If the minimum-norm solution is admissible and these sequences
satisfy scale calibration, every positive sample size with allocation strictly
between zero and one admits an event that [is measurable](step:1), [has
probability at least one minus the allocation](step:2), and [bounds every
admissible primal function's squared-norm increment error relative to the
minimum-norm solution by the comparison constant times the sum of accuracy
times its distance to that solution and squared accuracy](step:3).

Foster and Syrgkanis (2023), Orthogonal statistical learning,
DOI:10.1214/23-AOS2258, Lemma 14, `foster2023orthogonal`, as applied in
appendices.tex:674–720. This cited input is exactly the squared-norm increment
comparison for the paper's H, comparator h0, deterministic TRAE scale delta_n,
and supplied iid fitting sample. The allocation is the confidence at which the
recorded critical-radius and calibration assumptions are evaluated. The constant
is chosen from the fixed envelope and critical-radius floor before the accuracy
and allocation sequences; source constants are universal, not sequence-dependent.
The source application normalizes by M=max(1,B), uses the clipped squared loss
with Lipschitz constant 2M^2, and star(H-H) for the anchored radius.
The lower-floor witness is taken from tildeδ once. Fixed radius inflation
therefore depends only on that witness and the source constants, not on δ or
allocation. The n^(-1/2) calibration floor controls the finite small-n segment;
the coefficient 18 L d and the normalization then give one comparison constant
for every admissible pair of sequences, including every confidence level.
The retained lem:prob_localized and full lem:peeling proof have strictly decaying
tails; no sign is assigned to the unsigned Lemma-14 display's c6.
For d=1, r=R and u=L*R^2, the former's second bound is
c1*exp(-c2*n*R^2/3); the latter's proof gives c1*exp(-c2*n*R^2/4).
Their sum is at most 2*c1*exp(-c2*n*R^2/4), so both floor and tail
inflations can be fixed using the same positive floor witness of tildeδ.
For the finite segment 2*c2*n <= 1, the squared-norm increment deviation
is at most 2*M^2 on the common bounded event, while delta_n^2 >= 1/n.
Thus one fixed enlargement of C covers this segment, including n=1,
without a restriction on the allocation or dependence on its sequence.
This carrier supplies no theorem for arbitrary scalar classes or losses. -/
-- @node: lem:trae-squared-norm-lemma-14
noncomputable def ScalarLipschitzLocalizedConcentration
    (V : IVWorld 𝒲 𝒳 𝒵) (P : Measure Ω)
    (sample : AnalysisSample V P) (split : SampleSplit) : Sort 0 :=
  IsProbabilityMeasure P →
  ∀ (B : ℝ) (tildeδ : ℕ → ℝ → ℝ),
  TRAEBoundedness V B → TRAECommonNullSetBoundedness V B → TRAECriticalRadiusBound V tildeδ →
  ∃ C > 0, ∀ (δ allocation : ℕ → ℝ),
  H0MemHypothesisClass V → TRAEScaleCalibration δ tildeδ allocation →
  ∀ n : ℕ, 0 < n → allocation n ∈ Set.Ioo (0 : ℝ) 1 →
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - allocation n ≤ P.real E ∧
      ∀ ω ∈ E, ∀ h ∈ V.H,
        |(primalEmpSq V P sample split n ω h -
            primalEmpSq V P sample split n ω (minNormSolution V)) -
          (‖h‖ ^ 2 - ‖minNormSolution V‖ ^ 2)| ≤
            C * (δ n * ‖h - minNormSolution V‖ + δ n ^ 2)

/-- The [squared-norm localized comparison](goal) is the requirement that every
bounded model with a suitable critical-radius bound admit a positive constant
uniform over calibrated accuracy and failure-allocation sequences: whenever
the sampling law is a probability measure and the minimum-norm solution is
admissible, each positive sample size with allocation strictly between zero and
one has a measurable event of probability at least one minus the allocation on
which every admissible primal function's squared-norm increment error is at
most that constant times accuracy times distance to the minimum-norm solution
plus squared accuracy.

This is a compatibility name for the localized squared-norm concentration
requirement. -/
noncomputable abbrev SquaredNormLocalizedComparison :=
  @ScalarLipschitzLocalizedConcentration

-- @node: ass:pin-206
/-- The [pinned mean-square continuity requirement](goal) assigns to each model
the condition that some real constant bounds the expected squared moment
contribution of every admissible critic by that constant times its squared
norm, with each squared moment contribution integrable. -/
noncomputable def PinMeanSquareReading := @MeanSquareContinuity

-- @node: ass:pin-fix-958aeb7a
/-- For [a confidence-indexed radius bound](hyp:tildeδ), the [pinned
critical-radius lower-bound requirement](goal) says that a single positive
constant times the confidence floor is at most that radius bound at every
positive sample size and every failure level strictly between zero and one. -/
noncomputable def PinCriticalRadiusOmegaReading (tildeδ : ℕ → ℝ → ℝ) : Prop :=
  ∃ c > 0, ∀ n : ℕ, 0 < n → ∀ ξ ∈ Set.Ioo (0 : ℝ) 1,
    c * confidenceFloor n ξ ≤ tildeδ n ξ
    -- @realizes \tilde\delta_n(uniform positive lower-bound constant independent of n and confidence)

-- @node: ass:pin-156
/-- The [pinned TRAE minima requirement](goal) assigns to each model, sampling
law, analysis sample, sample split, grid ratio, and candidate estimator family
the condition that, at every positive sample size and grid penalty, the
candidate minimizes the penalized empirical TRAE objective and is measurable,
and the empirical loss of each fixed admissible primal function is measurable. -/
noncomputable def PinTRAEMinimaReading := @TRAEMinimaAttained

-- @node: ass:pin-160
/-- For [a model](hyp:V), [a sampling law](hyp:P), [an analysis sample](hyp:sample),
[a sample split](hyp:split), [a grid ratio ρ](hyp:ρ), [a failure level ξ](hyp:ξ),
[a source exponent β](hyp:β), [an accuracy sequence δ](hyp:δ), [a source element
w₀](hyp:w₀), [a candidate estimator family](hyp:candidate), [a sample size n](hyp:n),
[an event E](hyp:E), and [a comparison constant C](hyp:C), the [pinned TRAE
envelope requirement](goal) says that [E is measurable](step:1), [E has
probability at least one minus ξ](step:2), and [C is positive and, on E, the
minimum-norm solution's empirical loss is at most squared accuracy while each
grid candidate's empirical loss is at most squared accuracy plus C times the
squared norm of w₀ times its penalty raised to the bias exponent associated
with β](step:3). -/
noncomputable def PinTRAEEnvelopeReading (ρ ξ β : ℝ) (δ : ℕ → ℝ)
    (w₀ : V.Hbar.toSubmodule) (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (n : ℕ) (E : Set Ω) (C : ℝ) : Prop :=
  MeasurableSet E ∧ 1 - ξ ≤ P.real E ∧
    TRAEDiscrepancyEnvelope V P sample split ρ β δ w₀ candidate n E C



variable (ρ ξ B β c₀ CG Cm c a b κδ κν required : ℝ) (w₀ : V.Hbar.toSubmodule)
  (δ ν baseδ baseν : ℕ → ℝ) (δG δH δr rawG rawH rawR tildeδ : ℕ → ℝ → ℝ)
  (κ₀ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ) (mu : Measure 𝒳)
  (G : Set (𝒳 → 𝒵 → ℝ)) (g₀ : 𝒳 → 𝒵 → ℝ) (support : Set (𝒳 × 𝒵))
  (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (rHat : ℕ → Ω → 𝒵 → ℝ)
  (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
  (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule) (t : ℕ)

end Papers.TsAdaptiveEstimationInference
