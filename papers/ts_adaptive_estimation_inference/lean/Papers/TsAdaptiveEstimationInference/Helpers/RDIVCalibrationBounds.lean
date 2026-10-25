module
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVLossBridge
/-! Residual perturbation and deterministic calibration comparisons for RDIV.

These are the norm comparisons in the calibration part of `err_l_dp`.
The probabilistic Bernstein bound is an input to the deterministic transfer,
not an additional premise of any paper theorem.
-/
public section

namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter

variable {Z : Type*} [MeasurableSpace Z]

/-- If [f is square integrable under μ](hyp:hf), [its input L2 norm equals
the norm of its equivalence class in L2](goal). -/
-- @node: rdiv_inputL2Norm_eq_toLp_norm
lemma rdiv_inputL2Norm_eq_toLp_norm (μ : Measure Z) (f : Z → ℝ)
    (hf : MemLp f 2 μ) : inputL2Norm μ f = ‖hf.toLp f‖ := by
  have he : (∫ z, f z ^ 2 ∂μ) = ‖hf.toLp f‖ ^ 2 := by
    calc
      _ = ∫ z, (hf.toLp f z) ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [hf.coeFn_toLp] with z hz
        rw [hz]
      _ = _ := by
        simpa only [L2.inner_def, RCLike.inner_apply, conj_trivial, ← pow_two] using
          real_inner_self_eq_norm_sq (hf.toLp f)
  unfold inputL2Norm
  rw [he, Real.sqrt_sq (norm_nonneg _)]

/-- If [f is square integrable under μ](hyp:hf) and [g is square integrable
under μ](hyp:hg), [the input L2 norm of their sum is at most the sum of their
input L2 norms](goal). -/
-- @node: rdiv_inputL2Norm_add_le
lemma rdiv_inputL2Norm_add_le (μ : Measure Z) (f g : Z → ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inputL2Norm μ (f + g) ≤ inputL2Norm μ f + inputL2Norm μ g := by
  rw [rdiv_inputL2Norm_eq_toLp_norm μ _ (hf.add hg), hf.toLp_add hg,
    rdiv_inputL2Norm_eq_toLp_norm μ f hf, rdiv_inputL2Norm_eq_toLp_norm μ g hg]
  exact norm_add_le _ _

/-- If [f is square integrable under μ](hyp:hf) and [g is square integrable
under μ](hyp:hg), [the input L2 norm of their difference is at most the sum
of their input L2 norms](goal). -/
-- @node: rdiv_inputL2Norm_sub_le
lemma rdiv_inputL2Norm_sub_le (μ : Measure Z) (f g : Z → ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inputL2Norm μ (f - g) ≤ inputL2Norm μ f + inputL2Norm μ g := by
  rw [rdiv_inputL2Norm_eq_toLp_norm μ _ (hf.sub hg), hf.toLp_sub hg,
    rdiv_inputL2Norm_eq_toLp_norm μ f hf, rdiv_inputL2Norm_eq_toLp_norm μ g hg]
  exact norm_sub_le _ _

/-- If [f is square integrable under μ](hyp:hf) and [g is square integrable
under μ](hyp:hg), [the absolute difference of their input L2 norms is at most
the input L2 norm of their difference](goal). -/
-- @node: rdiv_inputL2Norm_abs_sub_le
lemma rdiv_inputL2Norm_abs_sub_le (μ : Measure Z) (f g : Z → ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |inputL2Norm μ f - inputL2Norm μ g| ≤ inputL2Norm μ (f - g) := by
  rw [rdiv_inputL2Norm_eq_toLp_norm μ _ (hf.sub hg), hf.toLp_sub hg,
    rdiv_inputL2Norm_eq_toLp_norm μ f hf, rdiv_inputL2Norm_eq_toLp_norm μ g hg]
  exact abs_norm_sub_norm_le _ _

/-- If [q is square integrable under μ](hyp:hq), [u is square integrable under
μ](hyp:hu), and [their input L2 distance is at most e](hyp:he), [the absolute
difference of their squared input L2 norms is at most twice the norm of u
times e plus e squared](goal). -/
-- @node: rdiv_residual_energy_perturbation
lemma rdiv_residual_energy_perturbation (μ : Measure Z) (q u : Z → ℝ)
    (hq : MemLp q 2 μ) (hu : MemLp u 2 μ) (e : ℝ)
    (he : inputL2Norm μ (q - u) ≤ e) :
    |inputL2Norm μ q ^ 2 - inputL2Norm μ u ^ 2| ≤
      2 * inputL2Norm μ u * e + e ^ 2 := by
  have hrev := (rdiv_inputL2Norm_abs_sub_le μ q u hq hu).trans he
  have he0 : 0 ≤ e := (Real.sqrt_nonneg _).trans he
  have hq0 : 0 ≤ inputL2Norm μ q := Real.sqrt_nonneg _
  have hu0 : 0 ≤ inputL2Norm μ u := Real.sqrt_nonneg _
  have hupper : inputL2Norm μ q ≤ inputL2Norm μ u + e := by
    linarith only [(abs_le.mp hrev).2]
  calc
    _ = |inputL2Norm μ q - inputL2Norm μ u| *
        (inputL2Norm μ q + inputL2Norm μ u) := by
      rw [← abs_of_nonneg (add_nonneg hq0 hu0), ← abs_mul]
      congr 1
      ring
    _ ≤ e * (inputL2Norm μ u + e + inputL2Norm μ u) :=
      mul_le_mul hrev (by linarith only [hupper]) (add_nonneg hq0 hu0) he0
    _ = _ := by ring

/-- Assume [q and u are square integrable under μ](hyp:hq,hu), [a, ν, K, and L
are nonnegative](hyp:ha,hν,hK,hL), [a is at most ν](hyp:haν), [the input L2
distance between q and u is at most Lν](hyp:he), and [D differs from the squared
norm of q by at most K times the sum of a times that norm and a squared](hyp:hBernstein).
Then [D differs from the squared norm of u by at most (K + 2L)ν times the norm
of u plus (KL + K + L²)ν²](goal). -/
-- @node: rdiv_calibration_residual_transfer
lemma rdiv_calibration_residual_transfer (μ : Measure Z) (q u : Z → ℝ)
    (hq : MemLp q 2 μ) (hu : MemLp u 2 μ) (D a ν K L : ℝ)
    (ha : 0 ≤ a) (hν : 0 ≤ ν) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (haν : a ≤ ν) (he : inputL2Norm μ (q - u) ≤ L * ν)
    (hBernstein : |D - inputL2Norm μ q ^ 2| ≤
      K * (a * inputL2Norm μ q + a ^ 2)) :
    |D - inputL2Norm μ u ^ 2| ≤
      (K + 2 * L) * ν * inputL2Norm μ u +
        (K * L + K + L ^ 2) * ν ^ 2 := by
  have hpert := rdiv_residual_energy_perturbation μ q u hq hu (L * ν) he
  have hrev := (rdiv_inputL2Norm_abs_sub_le μ q u hq hu).trans he
  have hnorm : inputL2Norm μ q ≤ inputL2Norm μ u + L * ν := by
    linarith only [(abs_le.mp hrev).2]
  have hq0 : 0 ≤ inputL2Norm μ q := Real.sqrt_nonneg _
  have hscale : a * inputL2Norm μ q + a ^ 2 ≤
      ν * (inputL2Norm μ u + L * ν) + ν ^ 2 := by
    have h₁ := mul_le_mul_of_nonneg_right haν hq0
    have h₂ := mul_le_mul_of_nonneg_left hnorm hν
    have h₃ : a ^ 2 ≤ ν ^ 2 := by nlinarith only [ha, hν, haν]
    linarith only [h₁, h₂, h₃]
  calc
    _ ≤ |D - inputL2Norm μ q ^ 2| +
        |inputL2Norm μ q ^ 2 - inputL2Norm μ u ^ 2| := abs_sub_le _ _ _
    _ ≤ K * (ν * (inputL2Norm μ u + L * ν) + ν ^ 2) +
        (2 * inputL2Norm μ u * (L * ν) + (L * ν) ^ 2) :=
      add_le_add (hBernstein.trans (mul_le_mul_of_nonneg_left hscale hK)) hpert
    _ = _ := by ring

variable {𝒲 X : Type*} [MeasurableSpace 𝒲] [MeasurableSpace X]
  (V : IVWorld 𝒲 X Z)

/-- If [the moment representer lies in the operator range](hyp:hRange),
[the input L2 norm of the true residual for h equals the projected norm of
the error of h relative to the minimum-norm solution](goal). -/
-- @node: rdiv_true_residual_input_norm
lemma rdiv_true_residual_input_norm (hRange : RangeCondition V)
    (h : V.Hbar.toSubmodule) :
    inputL2Norm (V.law.map V.zOf)
      (dualVersion V (momentRepresenter V) - dualVersion V (projCondExpOp V h)) =
      ‖projCondExpOp V (h - minNormSolution V)‖ := by
  have he : (fun w => dualVersion V (momentRepresenter V) (V.zOf w) -
      dualVersion V (projCondExpOp V h) (V.zOf w)) =ᵐ[V.law]
      (fun w => ((momentRepresenter V - projCondExpOp V h : V.Qbar.toSubmodule) :
        Lp ℝ 2 V.law) w) :=
    ((V.dual_coherent _).sub (V.dual_coherent _)).trans (Lp.coeFn_sub _ _).symm
  have hi : (∫ z, (dualVersion V (momentRepresenter V) z -
      dualVersion V (projCondExpOp V h) z) ^ 2 ∂V.law.map V.zOf) =
      ‖momentRepresenter V - projCondExpOp V h‖ ^ 2 := by
    have hmap := integral_map (μ := V.law) V.measurable_z.aemeasurable
      (((V.dual_measurable (momentRepresenter V)).sub
        (V.dual_measurable (projCondExpOp V h))).pow_const 2).aestronglyMeasurable
    simp only [Pi.sub_apply] at hmap
    change (∫ z, (dualVersion V (momentRepresenter V) z -
      dualVersion V (projCondExpOp V h) z) ^ 2 ∂V.law.map V.zOf) =
      ∫ w, (dualVersion V (momentRepresenter V) (V.zOf w) -
        dualVersion V (projCondExpOp V h) (V.zOf w)) ^ 2 ∂V.law at hmap
    rw [hmap]
    calc
      _ = ∫ w, (((momentRepresenter V - projCondExpOp V h : V.Qbar.toSubmodule) :
          Lp ℝ 2 V.law) w) ^ 2 ∂V.law := by
        apply integral_congr_ae
        filter_upwards [he] with w hw
        rw [hw]
      _ = _ := by
        simpa only [L2.inner_def, RCLike.inner_apply, conj_trivial, ← pow_two,
          Submodule.norm_coe] using real_inner_self_eq_norm_sq
          ((momentRepresenter V - projCondExpOp V h : V.Qbar.toSubmodule) : Lp ℝ 2 V.law)
  have hn : ‖momentRepresenter V - projCondExpOp V h‖ =
      ‖projCondExpOp V (h - minNormSolution V)‖ := by
    rw [map_sub, (minNormSolution_spec V hRange).1, norm_sub_rev]
  unfold inputL2Norm
  simpa only [Pi.sub_apply, hi, Real.sqrt_sq (norm_nonneg _)] using hn

/-- Assume [the RDIV model conditions hold](hyp:hIV), [the density class is
realizable](hyp:hDensity), [the common support and density bounds hold](hyp:hBounds),
[the hypothesis class is bounded by B on the support](hyp:hHyp), [B is
nonnegative](hyp:hB), [the fitted density belongs to its class](hyp:hg),
[the preliminary comparisons hold with constant C](hyp:hpre), and [h belongs
to the hypothesis class](hyp:hh). Then [the fitted pilot-minus-operator residual
is square integrable, and its input L2 distance from the true residual is at
most the pilot radius plus C times the density radius, both evaluated at
quarter confidence](goal). -/
-- @node: rdiv_calibration_residual_perturbation
lemma rdiv_calibration_residual_perturbation {Ω : Type*}
    (μ : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (gHat : ℕ → Ω → X → Z → ℝ) (rHat : ℕ → Ω → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG ξ C : ℝ)
    (δG δr : ℕ → ℝ → ℝ) (n : ℕ) (ω : Ω)
    (hIV : RDIVSetting V μ g₀) (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hHyp : HypothesisClassBounded V support B) (hB : 0 ≤ B)
    (hg : gHat n ω ∈ G)
    (hpre : RDIVPreliminaryOn V μ g₀ gHat rHat ξ δG δr n ω C)
    (h : V.Hbar.toSubmodule) (hh : h ∈ V.H) :
    MemLp (rHat n ω - estimatedOperator V μ gHat n ω h) 2 (V.law.map V.zOf) ∧
      inputL2Norm (V.law.map V.zOf)
        ((rHat n ω - estimatedOperator V μ gHat n ω h) -
          (dualVersion V (momentRepresenter V) - dualVersion V (projCondExpOp V h))) ≤
        δr n (ξ / 4) + C * δG n (ξ / 4) := by
  have hT : MemLp (estimatedOperator V μ gHat n ω h) 2 (V.law.map V.zOf) :=
    rdiv_density_operator_memLp V μ G g₀ (gHat n ω) support B c₀ CG
      hIV hDensity hBounds hHyp hB hg h hh
  have hr₀ := (rdiv_dual_input_memLp_norm V (momentRepresenter V)).1
  have hTh := (rdiv_dual_input_memLp_norm V (projCondExpOp V h)).1
  refine ⟨hpre.2.1.sub hT, ?_⟩
  have hid : (rHat n ω - estimatedOperator V μ gHat n ω h) -
      (dualVersion V (momentRepresenter V) - dualVersion V (projCondExpOp V h)) =
      (rHat n ω - dualVersion V (momentRepresenter V)) -
        (estimatedOperator V μ gHat n ω h - dualVersion V (projCondExpOp V h)) := by
    ext z
    simp only [Pi.sub_apply]
    ring
  rw [hid]
  exact (rdiv_inputL2Norm_sub_le _ _ _ (hpre.2.1.sub hr₀) (hT.sub hTh)).trans
    (add_le_add hpre.2.2.1 (hpre.2.2.2.1 h hh))

/-- Assume [the RDIV model conditions hold](hyp:hIV), [the range condition
holds](hyp:hRange), [the density class is realizable](hyp:hDensity), [the common
support and density bounds hold](hyp:hBounds), [the hypothesis class is bounded
by B on the support](hyp:hHyp), [B is nonnegative](hyp:hB), [the fitted density
belongs to its class](hyp:hg), [the preliminary comparisons hold with constant
C](hyp:hpre), and [h belongs to the hypothesis class](hyp:hh). If [a, ν, K,
and L are nonnegative](hyp:ha,hν,hK,hL), [a is at most ν](hyp:haν), [the pilot
radius plus C times the density radius at quarter confidence is at most
Lν](hyp:hscale), and [D differs from the fitted residual's squared input L2
norm by at most K times a times that norm plus K times a squared](hyp:hBernstein),
[D differs from the squared projected error by at most (K + 2L)ν times the
projected error norm plus (KL + K + L²)ν²](goal). -/
-- @node: rdiv_calibration_projected_comparison
lemma rdiv_calibration_projected_comparison {Ω : Type*}
    (μ : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (gHat : ℕ → Ω → X → Z → ℝ) (rHat : ℕ → Ω → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG ξ C D a ν K L : ℝ)
    (δG δr : ℕ → ℝ → ℝ) (n : ℕ) (ω : Ω)
    (hIV : RDIVSetting V μ g₀) (hRange : RangeCondition V)
    (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hHyp : HypothesisClassBounded V support B) (hB : 0 ≤ B)
    (hg : gHat n ω ∈ G)
    (hpre : RDIVPreliminaryOn V μ g₀ gHat rHat ξ δG δr n ω C)
    (h : V.Hbar.toSubmodule) (hh : h ∈ V.H)
    (ha : 0 ≤ a) (hν : 0 ≤ ν) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (haν : a ≤ ν) (hscale : δr n (ξ / 4) + C * δG n (ξ / 4) ≤ L * ν)
    (hBernstein : |D - inputL2Norm (V.law.map V.zOf)
      (rHat n ω - estimatedOperator V μ gHat n ω h) ^ 2| ≤
      K * (a * inputL2Norm (V.law.map V.zOf)
        (rHat n ω - estimatedOperator V μ gHat n ω h) + a ^ 2)) :
    |D - ‖projCondExpOp V (h - minNormSolution V)‖ ^ 2| ≤
      (K + 2 * L) * ν * ‖projCondExpOp V (h - minNormSolution V)‖ +
        (K * L + K + L ^ 2) * ν ^ 2 := by
  obtain ⟨hq, he⟩ := rdiv_calibration_residual_perturbation V μ G g₀ gHat rHat
    support B c₀ CG ξ C δG δr n ω hIV hDensity hBounds hHyp hB hg hpre h hh
  have hu := (rdiv_dual_input_memLp_norm V (momentRepresenter V)).1.sub
    (rdiv_dual_input_memLp_norm V (projCondExpOp V h)).1
  have hb := rdiv_calibration_residual_transfer (V.law.map V.zOf) _ _ hq hu
    D a ν K L ha hν hK hL haν (he.trans hscale) hBernstein
  rwa [rdiv_true_residual_input_norm V hRange h] at hb

/-- If [the scales satisfy RDIV calibration with multiplier one](hyp:hScale),
[C is nonnegative](hyp:hC), [the sample size is positive](hyp:hn), [the density
radius is nonnegative at quarter confidence](hyp:hG), and [the pilot radius
is nonnegative there](hyp:hr), [ν is nonnegative at that sample size and the
pilot radius plus C times the density radius is at most (C + 1)ν](goal). -/
-- @node: rdiv_calibration_scale_domination
lemma rdiv_calibration_scale_domination
    (ρ ξ C : ℝ) (δ ν : ℕ → ℝ) (δG δH δr : ℕ → ℝ → ℝ)
    (hScale : RDIVScaleCalibration ρ ξ δ ν δG δH δr 1)
    (hC : 0 ≤ C) (n : ℕ) (hn : 0 < n)
    (hG : 0 ≤ δG n (ξ / 4)) (hr : 0 ≤ δr n (ξ / 4)) :
    0 ≤ ν n ∧ δr n (ξ / 4) + C * δG n (ξ / 4) ≤ (C + 1) * ν n := by
  have hs := ((rdivScaleCalibration_one_iff_public ρ ξ δ ν δG δH δr).mp hScale).1 n hn |>.2
  change δG n (ξ / 4) + δr n (ξ / 4) + rdivPublicLogScale ρ ξ n ≤ ν n at hs
  have hl : 0 ≤ rdivPublicLogScale ρ ξ n := Real.sqrt_nonneg _
  have hν : 0 ≤ ν n := by linarith only [hs, hG, hr, hl]
  refine ⟨hν, ?_⟩
  have hGν : δG n (ξ / 4) ≤ ν n := by linarith only [hs, hr, hl]
  have hrν : δr n (ξ / 4) ≤ ν n := by linarith only [hs, hG, hl]
  nlinarith only [mul_le_mul_of_nonneg_left hGν hC, hrν]

/-- Assume [the RDIV model conditions hold](hyp:hIV), [the range condition
holds](hyp:hRange), [the density class is realizable](hyp:hDensity), [the common
support and density bounds hold](hyp:hBounds), [the hypothesis class is bounded
by B on the support](hyp:hHyp), [B is nonnegative](hyp:hB), [C is nonnegative](hyp:hC),
[K is nonnegative](hyp:hK), and [the scales satisfy RDIV calibration with
multiplier one](hyp:hScale). Then [there is a positive constant A such that,
for every positive sample size, fitted density in the class, outcome satisfying
the preliminary comparisons, nonnegative quarter-confidence density radius,
and hypothesis in the class, any Bernstein bound for D around the fitted
residual energy with constant K and scale ν implies an error bound around
the squared projected error of Aν times the projected error norm plus Aν²](goal). -/
-- @node: rdiv_calibration_projected_comparison_calibrated
lemma rdiv_calibration_projected_comparison_calibrated {Ω : Type*}
    (μ : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (gHat : ℕ → Ω → X → Z → ℝ) (rHat : ℕ → Ω → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG ρ ξ C K : ℝ)
    (δ ν : ℕ → ℝ) (δG δH δr : ℕ → ℝ → ℝ)
    (hIV : RDIVSetting V μ g₀) (hRange : RangeCondition V)
    (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hHyp : HypothesisClassBounded V support B) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hScale : RDIVScaleCalibration ρ ξ δ ν δG δH δr 1) :
    ∃ A > 0, ∀ n, 0 < n → ∀ ω,
      gHat n ω ∈ G → RDIVPreliminaryOn V μ g₀ gHat rHat ξ δG δr n ω C →
      0 ≤ δG n (ξ / 4) → ∀ h ∈ V.H, ∀ D : ℝ,
      |D - inputL2Norm (V.law.map V.zOf)
        (rHat n ω - estimatedOperator V μ gHat n ω h) ^ 2| ≤
        K * (ν n * inputL2Norm (V.law.map V.zOf)
          (rHat n ω - estimatedOperator V μ gHat n ω h) + ν n ^ 2) →
      |D - ‖projCondExpOp V (h - minNormSolution V)‖ ^ 2| ≤
        A * ν n * ‖projCondExpOp V (h - minNormSolution V)‖ + A * ν n ^ 2 := by
  let L := C + 1
  let A := (K + 2 * L) + (K * L + K + L ^ 2) + 1
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have h₁ : 0 ≤ K + 2 * L := by positivity
  have h₂ : 0 ≤ K * L + K + L ^ 2 := by positivity
  refine ⟨A, by dsimp [A]; positivity, ?_⟩
  intro n hn ω hg hpre hG h hh D hBernstein
  have hr : 0 ≤ δr n (ξ / 4) := (Real.sqrt_nonneg _).trans hpre.2.2.1
  obtain ⟨hν, hs⟩ := rdiv_calibration_scale_domination ρ ξ C δ ν δG δH δr
    hScale hC n hn hG hr
  have hb := rdiv_calibration_projected_comparison V μ G g₀ gHat rHat support
    B c₀ CG ξ C D (ν n) (ν n) K L δG δr n ω hIV hRange hDensity hBounds
    hHyp hB hg hpre h hh hν hν hK hL le_rfl hs hBernstein
  have hcoef₁ : K + 2 * L ≤ A := by dsimp [A]; linarith only [h₂]
  have hcoef₂ : K * L + K + L ^ 2 ≤ A := by dsimp [A]; linarith only [h₁]
  exact hb.trans (add_le_add
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef₁ hν) (norm_nonneg _))
    (mul_le_mul_of_nonneg_right hcoef₂ (sq_nonneg _)))

end Papers.TsAdaptiveEstimationInference
