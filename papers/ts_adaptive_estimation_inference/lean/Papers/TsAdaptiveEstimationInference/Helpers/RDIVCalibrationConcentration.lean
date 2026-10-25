module
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVCalibrationBounds
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVFittingEvent
public import Causalean.Stat.Concentration.TailBounds.ConfidenceInterval
/-! Frozen calibration concentration with the residual-dependent Bernstein scale.

The variance proxy is proportional to the squared residual norm, including
zero residuals. Thawing the training data and taking the grid union remain
separate from this fixed-residual probability bound.
-/
public section

namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory ProbabilityTheory

variable {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]

/-- If [q is measurable](hyp:hq), [B is nonnegative](hyp:_hB), and [the absolute
value of q is at most 2B almost everywhere](hyp:hbound), [q squared is integrable,
its centered value has absolute value at most 4B² almost everywhere, and its
variance is at most the square of the product of 2B and the input L2 norm of q](goal). -/
-- @node: rdiv_calibration_squared_residual_moments
lemma rdiv_calibration_squared_residual_moments
    (μ : Measure Z) [IsProbabilityMeasure μ] (q : Z → ℝ) (B : ℝ)
    (hq : Measurable q) (_hB : 0 ≤ B) (hbound : ∀ᵐ z ∂μ, |q z| ≤ 2 * B) :
    Integrable (fun z => q z ^ 2) μ ∧
      (∀ᵐ z ∂μ, |q z ^ 2 - ∫ y, q y ^ 2 ∂μ| ≤ 4 * B ^ 2) ∧
      (∫ z, (q z ^ 2 - ∫ y, q y ^ 2 ∂μ) ^ 2 ∂μ) ≤
        (2 * B * inputL2Norm μ q) ^ 2 := by
  have hsq : ∀ᵐ z ∂μ, q z ^ 2 ≤ 4 * B ^ 2 := by
    filter_upwards [hbound] with z hz
    nlinarith only [sq_abs (q z), mul_self_le_mul_self (abs_nonneg _) hz]
  have hi : Integrable (fun z => q z ^ 2) μ := by
    apply (integrable_const (4 * B ^ 2)).mono' (by fun_prop)
    filter_upwards [hsq] with z hz
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (q z))] using hz
  have hmean0 : 0 ≤ ∫ y, q y ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hmean : (∫ y, q y ^ 2 ∂μ) ≤ 4 * B ^ 2 := by
    simpa using integral_mono_ae hi (integrable_const (4 * B ^ 2)) hsq
  refine ⟨hi, ?_, ?_⟩
  · filter_upwards [hsq] with z hz
    exact abs_le.mpr ⟨by linarith [sq_nonneg (q z)], by linarith⟩
  have hfour : Integrable (fun z => (q z ^ 2) ^ 2) μ := by
    apply (hi.const_mul (4 * B ^ 2)).mono' (by fun_prop)
    filter_upwards [hsq] with z hz
    change |(q z ^ 2) ^ 2| ≤ 4 * B ^ 2 * q z ^ 2
    rw [abs_of_nonneg (sq_nonneg (q z ^ 2))]
    nlinarith only [mul_le_mul_of_nonneg_right hz (sq_nonneg (q z))]
  have hv := variance_le_expectation_sq (μ := μ) (X := fun z => q z ^ 2)
    (by fun_prop)
  rw [variance_eq_integral (by fun_prop)] at hv
  have hmoment : (∫ z, (q z ^ 2) ^ 2 ∂μ) ≤
      4 * B ^ 2 * ∫ z, q z ^ 2 ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono_ae hfour (hi.const_mul _)
    filter_upwards [hsq] with z hz
    nlinarith only [mul_le_mul_of_nonneg_right hz (sq_nonneg (q z))]
  apply hv.trans
  change (∫ z, (q z ^ 2) ^ 2 ∂μ) ≤ _
  calc
    _ ≤ 4 * B ^ 2 * ∫ z, q z ^ 2 ∂μ := hmoment
    _ = _ := by
      unfold inputL2Norm
      rw [mul_pow, Real.sq_sqrt hmean0]
      ring

/-- If [q is measurable](hyp:hq), [B is nonnegative](hyp:hB), [q is bounded in
absolute value by 2B almost everywhere](hyp:hbound), [the sample size n is
positive](hyp:hn), and [the failure probability ζ lies strictly between zero
and one](hyp:hζ), [there is a measurable event of probability at least 1 − ζ
on which the empirical mean of q squared differs from its population mean by
at most (4B + 8B² + 3) times the sum of the input L2 norm of q times
√(log(2/ζ)/n) and log(2/ζ)/n](goal). -/
-- @node: rdiv_frozen_calibration_bernstein
lemma rdiv_frozen_calibration_bernstein
    {P : Measure Ω} {μ : Measure Z} [IsProbabilityMeasure μ]
    (S : Causalean.Stat.IIDSample Ω Z P μ) (q : Z → ℝ) (B : ℝ)
    (hq : Measurable q) (hB : 0 ≤ B) (hbound : ∀ᵐ z ∂μ, |q z| ≤ 2 * B)
    (n : ℕ) (hn : 0 < n) (ζ : ℝ) (hζ : ζ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - ζ ≤ P.real E ∧ ∀ ω ∈ E,
      |S.sampleMean (fun z => q z ^ 2) n ω - inputL2Norm μ q ^ 2| ≤
        (4 * B + 8 * B ^ 2 + 3) *
          (Real.sqrt (Real.log (2 / ζ) / n) * inputL2Norm μ q +
            Real.sqrt (Real.log (2 / ζ) / n) ^ 2) := by
  obtain ⟨hi, hc, hv⟩ := rdiv_calibration_squared_residual_moments μ q B hq hB hbound
  let a := Real.sqrt (Real.log (2 / ζ) / n)
  have ha : 0 < a := by
    apply Real.sqrt_pos.2
    apply div_pos _ (by exact_mod_cast hn)
    apply Real.log_pos
    exact (lt_div_iff₀ hζ.1).2 (by linarith [hζ.2])
  have hQ : 0 ≤ inputL2Norm μ q := Real.sqrt_nonneg _
  have hs : 0 < 2 * B * inputL2Norm μ q + a := by positivity
  have hv' : (∫ z, (q z ^ 2 - ∫ y, q y ^ 2 ∂μ) ^ 2 ∂μ) ≤
      (2 * B * inputL2Norm μ q + a) ^ 2 := by
    apply hv.trans
    nlinarith only [mul_nonneg hB hQ, ha]
  have hp := Causalean.Stat.Concentration.bernstein_ci_cover S (by fun_prop) hi
    (by positivity : 0 ≤ 4 * B ^ 2) hs hc hv' n hn hζ.1 hζ.2.le
  let E := {ω | |S.sampleMean (fun z => q z ^ 2) n ω - ∫ z, q z ^ 2 ∂μ| <
    Causalean.Stat.Concentration.bernsteinCIHalfWidth (4 * B ^ 2)
      (2 * B * inputL2Norm μ q + a) n ζ}
  refine ⟨E, ?_, hp, ?_⟩
  · apply measurableSet_lt _ measurable_const
    fun_prop
  intro ω hω
  have hnorm : inputL2Norm μ q ^ 2 = ∫ z, q z ^ 2 ∂μ :=
    Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)
  rw [hnorm]
  apply (le_of_lt hω).trans
  have ha2 : a ^ 2 = Real.log (2 / ζ) / n := Real.sq_sqrt (div_nonneg
    (Causalean.Stat.Concentration.log_two_div_nonneg hζ.1 hζ.2.le) (Nat.cast_nonneg n))
  change 2 * (2 * B * inputL2Norm μ q + a) * a +
    2 * (4 * B ^ 2) * (Real.log (2 / ζ) / n) ≤ _
  rw [← ha2, Real.sqrt_sq ha.le]
  have h₁ : 0 ≤ (8 * B ^ 2 + 3) * (a * inputL2Norm μ q) := by positivity
  have h₂ : 0 ≤ (4 * B + 1) * a ^ 2 := by positivity
  nlinarith only [h₁, h₂]

/-- If [q is strongly measurable up to a null set](hyp:hq), [B is nonnegative](hyp:hB),
[q is bounded in absolute value by 2B almost everywhere](hyp:hbound), [the sample
size n is positive](hyp:hn), and [the failure probability ζ lies strictly
between zero and one](hyp:hζ), [there is a measurable event of probability at
least 1 − ζ on which the empirical mean of q squared differs from its population
mean by at most (4B + 8B² + 3) times the sum of the input L2 norm of q times
√(log(2/ζ)/n) and log(2/ζ)/n](goal). -/
-- @node: rdiv_frozen_calibration_bernstein_ae
lemma rdiv_frozen_calibration_bernstein_ae
    {P : Measure Ω} {μ : Measure Z} [IsProbabilityMeasure μ]
    (S : Causalean.Stat.IIDSample Ω Z P μ) (q : Z → ℝ) (B : ℝ)
    (hq : AEStronglyMeasurable q μ) (hB : 0 ≤ B)
    (hbound : ∀ᵐ z ∂μ, |q z| ≤ 2 * B)
    (n : ℕ) (hn : 0 < n) (ζ : ℝ) (hζ : ζ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - ζ ≤ P.real E ∧ ∀ ω ∈ E,
      |S.sampleMean (fun z => q z ^ 2) n ω - inputL2Norm μ q ^ 2| ≤
        (4 * B + 8 * B ^ 2 + 3) *
          (Real.sqrt (Real.log (2 / ζ) / n) * inputL2Norm μ q +
            Real.sqrt (Real.log (2 / ζ) / n) ^ 2) := by
  let q' := hq.mk q
  have heq : q =ᵐ[μ] q' := hq.ae_eq_mk
  have hbound' : ∀ᵐ z ∂μ, |q' z| ≤ 2 * B := by
    filter_upwards [heq, hbound] with z hz hb
    rwa [← hz]
  obtain ⟨E, hE, hpE, hgood⟩ := rdiv_frozen_calibration_bernstein S q' B
    hq.stronglyMeasurable_mk.measurable hB hbound' n hn ζ hζ
  have hpoints : ∀ᵐ ω ∂P, ∀ i : ℕ, q (S.Z i ω) = q' (S.Z i ω) := by
    apply ae_all_iff.2
    intro i
    have heq' : q =ᵐ[P.map (S.Z i)] q' := by rwa [S.map_eq i]
    exact ae_eq_comp (S.meas i).aemeasurable heq'
  obtain ⟨N, hNsub, hN, hpN⟩ := exists_measurable_superset_of_null
    (ae_iff.1 hpoints)
  have hNae : ∀ᵐ ω ∂P, ω ∉ N := by
    rw [ae_iff]
    simpa using hpN
  have hnorm : inputL2Norm μ q = inputL2Norm μ q' := by
    unfold inputL2Norm
    congr 1
    apply integral_congr_ae
    filter_upwards [heq] with z hz
    rw [hz]
  refine ⟨E \ N, hE.diff hN, ?_, ?_⟩
  · have hevent : (E \ N : Set Ω) =ᵐ[P] E := by
      filter_upwards [hNae] with ω hω
      exact propext ⟨fun h => h.1, fun h => ⟨h, hω⟩⟩
    rwa [measureReal_congr hevent]
  intro ω hω
  have hp : ∀ i, q (S.Z i ω) = q' (S.Z i ω) := by
    by_contra hnot
    exact hω.2 (hNsub hnot)
  have hmean : S.sampleMean (fun z => q z ^ 2) n ω =
      S.sampleMean (fun z => q' z ^ 2) n ω := by
    unfold Causalean.Stat.IIDSample.sampleMean
    simp only [hp]
  rw [hmean, hnorm]
  exact hgood ω hω.1


/-- If [B is nonnegative](hyp:hB), [the failure probability ξ lies strictly
between zero and one](hyp:hξ), [the sample size n is positive](hyp:hn), [each
grid residual is strongly measurable up to a null set](hyp:hq), and [each is
bounded in absolute value by 2B almost everywhere](hyp:hbound), [there is a
measurable event of probability at least 1 − ξ/4 on which, simultaneously over
the grid, the empirical residual energy differs from its population value by
at most (4B + 8B² + 3) times the sum of the residual norm times the quarter-grid
logarithmic radius and that radius squared](goal). -/
-- @node: rdiv_frozen_calibration_grid_bernstein
lemma rdiv_frozen_calibration_grid_bernstein
    {P : Measure Ω} {μ : Measure Z} [IsProbabilityMeasure μ]
    (S : Causalean.Stat.IIDSample Ω Z P μ) (q : ℝ → Z → ℝ) (B ρ ξ : ℝ)
    (hB : 0 ≤ B) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (n : ℕ) (hn : 0 < n)
    (hq : ∀ lam ∈ regGrid ρ n, AEStronglyMeasurable (q lam) μ)
    (hbound : ∀ lam ∈ regGrid ρ n, ∀ᵐ z ∂μ, |q lam z| ≤ 2 * B) :
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - ξ / 4 ≤ P.real E ∧
      ∀ ω ∈ E, ∀ lam ∈ regGrid ρ n,
        |S.sampleMean (fun z => q lam z ^ 2) n ω - inputL2Norm μ (q lam) ^ 2| ≤
          (4 * B + 8 * B ^ 2 + 3) *
            (Real.sqrt (Real.log (2 / (gridConfidence ρ ξ n / 4)) / n) *
                inputL2Norm μ (q lam) +
              Real.sqrt (Real.log (2 / (gridConfidence ρ ξ n / 4)) / n) ^ 2) := by
  classical
  have : IsProbabilityMeasure P := S.indep.isProbabilityMeasure
  have hη : gridConfidence ρ ξ n / 4 ∈ Set.Ioo (0 : ℝ) 1 := by
    have hk : (1 : ℝ) ≤ (terminalIndex ρ n + 1 : ℕ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    have hηle : gridConfidence ρ ξ n ≤ ξ := by
      unfold gridConfidence
      exact (div_le_iff₀ (by positivity)).2 (by nlinarith only [hk, hξ.1])
    constructor
    · have hx := hξ.1
      unfold gridConfidence
      positivity
    · linarith only [hηle, hξ.2]
  have hlocal := fun lam hlam => rdiv_frozen_calibration_bernstein_ae S (q lam) B
    (hq lam hlam) hB (hbound lam hlam) n hn _ hη
  choose E hE hpE hgood using hlocal
  let F : ℝ → Set Ω := fun lam => if h : lam ∈ regGrid ρ n then E lam h else Set.univ
  have hF (lam : ℝ) (hlam : lam ∈ regGrid ρ n) : F lam = E lam hlam := by
    simp only [F, dif_pos hlam]
  obtain ⟨hm, hp⟩ := rdiv_fitting_grid_event_budget P ρ ξ hξ.1.le n F
    (fun lam hlam => by rw [hF lam hlam]; exact hE lam hlam)
    (fun lam hlam => by rw [hF lam hlam]; exact hpE lam hlam)
  refine ⟨⋂ lam ∈ regGrid ρ n, F lam, hm, hp, ?_⟩
  intro ω hω lam hlam
  have hmem := Set.mem_iInter₂.mp hω lam hlam
  rw [hF lam hlam] at hmem
  exact hgood lam hlam ω hmem

variable {𝒲 X : Type*} [MeasurableSpace 𝒲] [MeasurableSpace X]

/-- Assume [the RDIV model conditions hold](hyp:hIV), [the density class is
realizable](hyp:hDensity), [the common support and density bounds hold](hyp:hBounds),
[the hypothesis class is bounded by B on the support](hyp:hHyp), [B is
nonnegative](hyp:hB), [g belongs to the density class](hyp:hg), [the pilot r is
strongly measurable up to a null set under the input law](hyp:hr), [r is bounded
in absolute value by B almost everywhere](hyp:hrB), and [h belongs to the
hypothesis class](hyp:hh). If [the sample size n is positive](hyp:hn) and
[ζ lies strictly between zero and one](hyp:hζ), [there is a measurable event
of probability at least 1 − ζ on which the empirical energy of the residual
r minus the density operator applied to h differs from its population energy
by at most (4B + 8B² + 3) times the sum of its input L2 norm times
√(log(2/ζ)/n) and log(2/ζ)/n](goal). -/
-- @node: rdiv_density_residual_frozen_calibration
lemma rdiv_density_residual_frozen_calibration
    (V : IVWorld 𝒲 X Z) {P : Measure Ω}
    (S : Causalean.Stat.IIDSample Ω Z P (V.law.map V.zOf))
    (μ : Measure X) (G : Set (X → Z → ℝ)) (g₀ g : X → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG : ℝ) (r : Z → ℝ)
    (hIV : RDIVSetting V μ g₀) (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hHyp : HypothesisClassBounded V support B) (hB : 0 ≤ B) (hg : g ∈ G)
    (hr : AEStronglyMeasurable r (V.law.map V.zOf))
    (hrB : ∀ᵐ z ∂V.law.map V.zOf, |r z| ≤ B)
    (h : V.Hbar.toSubmodule) (hh : h ∈ V.H)
    (n : ℕ) (hn : 0 < n) (ζ : ℝ) (hζ : ζ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - ζ ≤ P.real E ∧ ∀ ω ∈ E,
      |S.sampleMean (fun z => (r z - densityOperator μ g (primalVersion V h) z) ^ 2)
          n ω - inputL2Norm (V.law.map V.zOf)
            (r - densityOperator μ g (primalVersion V h)) ^ 2| ≤
        (4 * B + 8 * B ^ 2 + 3) *
          (Real.sqrt (Real.log (2 / ζ) / n) * inputL2Norm (V.law.map V.zOf)
            (r - densityOperator μ g (primalVersion V h)) +
              Real.sqrt (Real.log (2 / ζ) / n) ^ 2) := by
  have : IsProbabilityMeasure (V.law.map V.zOf) :=
    Measure.isProbabilityMeasure_map V.measurable_z.aemeasurable
  have hT := rdiv_density_operator_memLp V μ G g₀ g support B c₀ CG
    hIV hDensity hBounds hHyp hB hg h hh
  apply rdiv_frozen_calibration_bernstein_ae S
    (r - densityOperator μ g (primalVersion V h)) B (hr.sub hT.1) hB _ n hn ζ hζ
  filter_upwards [hrB, rdiv_hypothesis_density_operator_bounded V μ G g₀ g
    support B c₀ CG hDensity hBounds hHyp hB hg] with z hrz hTz
  exact (abs_sub _ _).trans (by linarith only [hrz, hTz h hh])

end Papers.TsAdaptiveEstimationInference
