module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterTRAEConcentration
/-! Transfer of recorded iterative squared-loss processes to the clipped source loss. -/
public section
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory
open scoped ENNReal

/-- If [the scaling factor is positive](hyp:hq), [outside one null set every
candidate's clipped loss increment equals its original loss increment divided
by that factor](hyp:hEq), and [the original localized suprema are
measurable](hyp:hMeas), then [the clipped localized suprema are almost-everywhere
measurable for the same class, anchor, and sample size](goal). -/
-- @node: localizedSupremaMeasurableAt_ae_scaled_loss
lemma localizedSupremaMeasurableAt_ae_scaled_loss
    {A : Type*} [MeasurableSpace A] (law : Measure A) [IsProbabilityMeasure law]
    {d : ℕ} (F : Set (A → Fin d → ℝ)) (v0 : A → Fin d → ℝ)
    (loss clipped : A → (Fin d → ℝ) → ℝ) (n : ℕ)
    (q : ℝ) (hq : 0 < q)
    (hEq : ∀ᵐ w ∂law, ∀ v ∈ F,
      clipped w (v w) - clipped w (v0 w) =
        (loss w (v w) - loss w (v0 w)) / q)
    (hMeas : LocalizedSupremaMeasurableAt law F v0 loss n) :
    AELocalizedSupremaMeasurableAt law F v0 clipped n := by
  classical
  intro r hr
  obtain ⟨hm, hs⟩ := hMeas r hr
  have hi (v : F) :
      (∫ w, clipped w (v.1 w) - clipped w (v0 w) ∂law) =
        (∫ w, loss w (v.1 w) - loss w (v0 w) ∂law) / q := by
    rw [← integral_div]
    apply integral_congr_ae
    filter_upwards [hEq] with w hw
    exact hw v.1 v.2
  have ht : ∀ᵐ x : Fin n → A ∂Measure.pi (fun _ => law),
      ∀ i, ∀ v ∈ F, clipped (x i) (v (x i)) - clipped (x i) (v0 (x i)) =
        (loss (x i) (v (x i)) - loss (x i) (v0 (x i))) / q := by
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval (fun _ : Fin n => law) i).quasiMeasurePreserving.ae hEq
  constructor
  · apply (hm.aemeasurable.div_const (ENNReal.ofReal q)).congr
    filter_upwards [ht] with x hx
    rw [ENNReal.iSup_div]
    apply iSup_congr
    intro v
    have havg : (n : ℝ)⁻¹ * ∑ i,
        (clipped (x i) (v.1.1 (x i)) - clipped (x i) (v0 (x i))) =
        ((n : ℝ)⁻¹ * ∑ i,
          (loss (x i) (v.1.1 (x i)) - loss (x i) (v0 (x i)))) / q := by
      simp_rw [hx _ _ v.1.2]
      rw [← Finset.sum_div, mul_div_assoc]
    change ENNReal.ofReal _ / ENNReal.ofReal q = ENNReal.ofReal _
    rw [havg, hi v.1, ← sub_div, abs_div, abs_of_pos hq,
      ENNReal.ofReal_div_of_pos hq]
  · apply (hs.aemeasurable.div_const (ENNReal.ofReal q)).congr
    have hp : ∀ᵐ p : (Fin n → A) × (Fin n → Bool)
        ∂(Measure.pi (fun _ => law)).prod
          ((2 ^ n : ℝ≥0∞)⁻¹ • (Measure.count : Measure (Fin n → Bool))),
        ∀ i, ∀ v ∈ F, clipped (p.1 i) (v (p.1 i)) - clipped (p.1 i) (v0 (p.1 i)) =
          (loss (p.1 i) (v (p.1 i)) - loss (p.1 i) (v0 (p.1 i))) / q :=
      Measure.quasiMeasurePreserving_fst.ae ht
    filter_upwards [hp] with p hp
    rw [ENNReal.iSup_div]
    apply iSup_congr
    intro v
    have havg : (n : ℝ)⁻¹ * ∑ i, (if p.2 i then (1 : ℝ) else -1) *
        (clipped (p.1 i) (v.1.1 (p.1 i)) - clipped (p.1 i) (v0 (p.1 i))) =
        ((n : ℝ)⁻¹ * ∑ i, (if p.2 i then (1 : ℝ) else -1) *
          (loss (p.1 i) (v.1.1 (p.1 i)) - loss (p.1 i) (v0 (p.1 i)))) / q := by
      simp_rw [hp _ _ v.1.2, ← mul_div_assoc]
      rw [← Finset.sum_div, mul_div_assoc]
    change ENNReal.ofReal _ / ENNReal.ofReal q = ENNReal.ofReal _
    rw [havg, abs_div, abs_of_pos hq, ENNReal.ofReal_div_of_pos hq]

variable {W X Z : Type*} [MeasurableSpace W] [MeasurableSpace X]
  [MeasurableSpace Z] (V : IVWorld W X Z)

/-- If [the model is bounded](hyp:hBound), [a common null-set envelope
holds](hyp:hCommon), [the anchor belongs to the hypothesis class](hyp:ha), [the
center's primal observations are almost surely bounded by the envelope](hyp:hcenter),
and [the localized raw squared-distance suprema are measurable](hyp:hMeas), then
[the localized clipped squared-distance suprema are almost-everywhere measurable
at the same anchor and sample size](goal). -/
-- @node: iter_trae_source_square_processes
lemma iter_trae_source_square_processes (B : ℝ) (hBound : TRAEBoundedness V B) (hCommon : TRAECommonNullSetBoundedness V B)
    (a center : V.Hbar.toSubmodule) (ha : a ∈ V.H)
    (hcenter : ∀ᵐ w ∂V.law, |primalVersion V center (V.xOf w)| ≤ B) (n : ℕ)
    (hMeas : LocalizedSupremaMeasurableAt V.law
      (iterTraeScalarClass (primalObservationClass V))
      (fun w => fun _ : Fin 1 => primalVersion V a (V.xOf w))
      (fun w v => (v 0 - primalVersion V center (V.xOf w)) ^ 2) n) :
    AELocalizedSupremaMeasurableAt V.law
      (iterTraeScalarClass (primalObservationClass V))
      (fun w => fun _ : Fin 1 => primalVersion V a (V.xOf w))
      (iterTraeSourceSquare B (fun w => primalVersion V center (V.xOf w))) n := by
  apply localizedSupremaMeasurableAt_ae_scaled_loss V.law _ _ _ _ n
    ((2 * max 1 B) ^ 2) (by positivity) _ hMeas
  filter_upwards [hBound.2.2.1, hcenter] with w hw hwcenter
  intro v hv
  obtain ⟨f, hf, rfl⟩ := hv
  obtain ⟨h, hh, rfl⟩ := hf
  have hs : 0 < 2 * max 1 B := by positivity
  have hBs : 2 * B ≤ 2 * max 1 B := by gcongr; exact le_max_right _ _
  have he (h : V.Hbar.toSubmodule) (hh : h ∈ V.H) :
      iterTraeSourceSquare B (fun w => primalVersion V center (V.xOf w)) w
        (fun _ => primalVersion V h (V.xOf w)) =
        (primalVersion V h (V.xOf w) - primalVersion V center (V.xOf w)) ^ 2 /
          (2 * max 1 B) ^ 2 :=
    iter_trae_clipped_distance_eq V (2 * max 1 B) B hs hBs h center w
      (hw h hh) hwcenter
  rw [he h hh, he a ha, sub_div]

/-- Assuming [fixed-center squared-loss concentration](hyp:hSource), [each
bounded model with a common null-set envelope and positive floor coefficient
admits a positive constant such that, at sample sizes at least three, a positive
radius dominating the scalar confidence floor and bounding the primal critical
radius yields, for every admissible grid iterate and adjacent bounded center
with measurable raw squared-distance processes, a measurable event of probability
at least one minus the confidence allocation uniformly bounding clipped
squared-loss increment deviations by the constant times radius times population
L2 distance from the iterate plus squared radius](goal). -/
-- @node: iter_trae_fixed_center_concentration_of_raw_processes
lemma iter_trae_fixed_center_concentration_of_raw_processes
    (hSource : IterTRAEFixedCenterSquaredLossConcentration V) :
  ∀ B cfloor : ℝ, TRAEBoundedness V B → TRAECommonNullSetBoundedness V B → 0 < cfloor →
  ∃ C > 0, ∀ n : ℕ, 3 ≤ n → ∀ ζ ∈ Set.Ioo (0 : ℝ) 1,
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
  LocalizedSupremaMeasurableAt V.law
    (iterTraeScalarClass (primalObservationClass V))
    (fun w => fun _ : Fin 1 => primalVersion V (populationIterate V lam j) (V.xOf w))
    (fun w v => (v 0 - primalVersion V center (V.xOf w)) ^ 2) n →
  ∃ E : Set (Fin n → W), MeasurableSet E ∧
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
          primalVersion V (populationIterate V lam j) (V.xOf w)) + r ^ 2) := by
  intro B cfloor hBound hCommon hcfloor
  obtain ⟨C, hC, hSource⟩ := iterTraeFixedCenterSource_local V hSource B cfloor hBound hCommon hcfloor
  refine ⟨C, hC, ?_⟩
  intro n hn ζ hζ r hfloor hr hcritical ρ c b β δ t j hρ hc hb hβ hj hjt
  dsimp only
  intro hDefined lam hlam hlow hu hp hmem center hcenter hEnvelope hMeas
  exact hSource n hn ζ hζ r hfloor hr hcritical ρ c b β δ t j
    hρ hc hb hβ hj hjt hDefined lam hlam hlow hu hp hmem center hcenter hEnvelope
    (iter_trae_source_square_processes V B hBound hCommon _ center hmem hEnvelope n hMeas)


end Papers.TsAdaptiveEstimationInference
