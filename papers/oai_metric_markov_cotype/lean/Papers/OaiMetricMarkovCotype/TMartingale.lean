module
public import Papers.OaiMetricMarkovCotype.Helpers.Flat
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Martingale energy estimate for cubic smoothing

The nonnegative energy is a lower integral of the sum of its nonnegative jumps;
its bound is the real difference of the two quartic expectations.
-/

public section

open MeasureTheory
open scoped BigOperators ENNReal Topology
open Filter
namespace Papers.OaiMetricMarkovCotype

-- @node: cube_sub_binary_abs_le_one
/-- If [u has every coordinate between zero and one](hyp:hu) and
[e has every coordinate equal to zero or one](hyp:he), then
[their absolute difference at any coordinate B is at most one](goal). -/
lemma cube_sub_binary_abs_le_one {𝓑 : Type*}
    {u e : 𝓑 → ℝ} (hu : u ∈ unitCube 𝓑) (he : BinaryVector e) (B : 𝓑) :
    |u B - e B| ≤ 1 := by
  have h := hu B (Set.mem_univ B)
  rcases he B with hB | hB <;> rw [hB] <;> apply abs_le.mpr <;> constructor <;> linarith [h.1, h.2]

-- @node: weightedHNormSq_cube_le
/-- If [the coordinate weights are strictly positive](hyp:hw),
[u lies in the unit cube](hyp:hu), and [e is a binary vector](hyp:he), then
[the weighted sum of squared coordinate differences between u and e is at most
the sum of the weights](goal). -/
lemma weightedHNormSq_cube_le {𝓑 : Type*} [Fintype 𝓑]
    (w u e : 𝓑 → ℝ) (hw : PositiveWeights w)
    (hu : u ∈ unitCube 𝓑) (he : BinaryVector e) :
    weightedHNormSq w (u - e) ≤ ∑ B, w B := by
  apply Finset.sum_le_sum
  intro B _
  have h := cube_sub_binary_abs_le_one hu he B
  have hs : (u B - e B) ^ 2 ≤ 1 := by
    nlinarith [sq_abs (u B - e B), abs_nonneg (u B - e B)]
  simpa using mul_le_mul_of_nonneg_left hs (hw B).le

-- @node: quarticPotential_cube_bound
/-- If [the coordinate weights are strictly positive](hyp:hw),
[u lies in the unit cube](hyp:hu), and [e is a binary vector](hyp:he), then
[the absolute value of the quartic potential of u about e is at most the square
of the sum of the weights](goal). -/
lemma quarticPotential_cube_bound {𝓑 : Type*} [Fintype 𝓑]
    (w u e : 𝓑 → ℝ) (hw : PositiveWeights w)
    (hu : u ∈ unitCube 𝓑) (he : BinaryVector e) :
    ‖quarticPotential w e u‖ ≤ (∑ B, w B) ^ 2 := by
  have h := weightedHNormSq_cube_le w u e hw hu he
  have hn := weightedHNormSq_nonneg w (u - e) hw
  rw [Real.norm_eq_abs, quarticPotential, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ hn h 2

/-- If [the random vector u is strongly measurable](hyp:hu), then
[the weighted sum of its squared coordinates is strongly measurable for any
fixed coordinate weights](goal). -/
@[fun_prop]
-- @node: stronglyMeasurable_weightedHNormSq
lemma stronglyMeasurable_weightedHNormSq {Ω 𝓑 : Type*} [MeasurableSpace Ω] [Fintype 𝓑]
    {u : Ω → 𝓑 → ℝ} (hu : StronglyMeasurable u) (w : 𝓑 → ℝ) :
    StronglyMeasurable (fun ω => weightedHNormSq w (u ω)) := by
  unfold weightedHNormSq
  exact Finset.stronglyMeasurable_fun_sum _ fun B _ =>
    (((continuous_apply B).comp_stronglyMeasurable hu).pow 2).const_mul (w B)

/-- If [the random vector u is strongly measurable](hyp:hu) and
[the random center e is strongly measurable](hyp:he), then
[the quartic potential of u about e is strongly measurable for any fixed
coordinate weights](goal). -/
@[fun_prop]
-- @node: stronglyMeasurable_quarticPotential
lemma stronglyMeasurable_quarticPotential {Ω 𝓑 : Type*} [MeasurableSpace Ω] [Fintype 𝓑]
    {u e : Ω → 𝓑 → ℝ} (hu : StronglyMeasurable u) (he : StronglyMeasurable e)
    (w : 𝓑 → ℝ) : StronglyMeasurable (fun ω => quarticPotential w (e ω) (u ω)) := by
  unfold quarticPotential
  fun_prop

-- @node: integrable_quarticPotential_cube
/-- Under a finite measure, if [the coordinate weights are strictly positive](hyp:hw),
[u is strongly measurable](hyp:hu), [e is strongly measurable](hyp:he),
[u lies in the unit cube at every outcome](hyp:huc), and
[e is binary at every outcome](hyp:heb), then
[the quartic potential of u about e is integrable](goal). -/
lemma integrable_quarticPotential_cube {Ω 𝓑 : Type*} [MeasurableSpace Ω] [Fintype 𝓑]
    (μ : Measure Ω) [IsFiniteMeasure μ] (w : 𝓑 → ℝ) (hw : PositiveWeights w)
    {u e : Ω → 𝓑 → ℝ} (hu : StronglyMeasurable u) (he : StronglyMeasurable e)
    (huc : ∀ ω, u ω ∈ unitCube 𝓑) (heb : ∀ ω, BinaryVector (e ω)) :
    Integrable (fun ω => quarticPotential w (e ω) (u ω)) μ := by
  refine (integrable_const ((∑ B, w B) ^ 2)).mono'
    (stronglyMeasurable_quarticPotential hu he w).aestronglyMeasurable ?_
  exact ae_of_all μ fun ω => quarticPotential_cube_bound w _ _ hw (huc ω) (heb ω)

/-- Under a finite measure, suppose [the conditioning information is contained in
the ambient measurable information](hyp:hm), [a is strongly measurable with
respect to that conditioning information](hyp:ha), [g is integrable](hyp:hg),
[a is uniformly bounded in absolute value](hyp:hb), and [the conditional
expectation of g given that information is zero almost surely](hyp:hz).
Then [the product of a and g is integrable and has integral zero](goal). -/
-- @node: integral_predictable_mul_zero
lemma integral_predictable_mul_zero {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {a g : Ω → ℝ} (ha : StronglyMeasurable[m] a) (hg : Integrable g μ)
    (hb : ∃ C : ℝ, ∀ ω, ‖a ω‖ ≤ C) (hz : μ[g | m] =ᵐ[μ] 0) :
    Integrable (fun ω => a ω * g ω) μ ∧ (∫ ω, a ω * g ω ∂μ) = 0 := by
  obtain ⟨C, hC⟩ := hb
  have hi := hg.bdd_mul (ha.mono hm).aestronglyMeasurable (ae_of_all μ hC)
  refine ⟨hi, ?_⟩
  change (∫ ω, (a * g) ω ∂μ) = 0
  rw [← integral_condExp hm]
  apply integral_eq_zero_of_ae
  filter_upwards [condExp_mul_of_stronglyMeasurable_left ha hi hg, hz] with ω hω hzω
  simpa [hzω] using hω

/-- If [the coordinate weights are strictly positive](hyp:hw),
[M is a martingale taking values in the unit cube at every time and outcome,
converging almost surely to a terminal vector that lies in the cube almost
surely](hyp:hM), and [e is a binary random vector strongly measurable with
respect to the initial information](hyp:he), then [at any time m, four times
the weighted squared distance from M to e times the weighted inner product
of that displacement with the next martingale increment is integrable and
has expectation zero](goal). -/
-- @node: integral_quartic_martingale_derivative_zero
lemma integral_quartic_martingale_derivative_zero
    {Ω 𝓑 : Type*} [mΩ : MeasurableSpace Ω] [Fintype 𝓑]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (𝓕 : Filtration ℕ mΩ)
    (w : 𝓑 → ℝ) (M : ℕ → Ω → 𝓑 → ℝ) (Minf e : Ω → 𝓑 → ℝ)
    (hw : PositiveWeights w) (hM : CubeMartingale μ 𝓕 M Minf)
    (he : InitialBinaryCenter 𝓕 e) (m : ℕ) :
    Integrable (fun ω => 4 * weightedHNormSq w (M m ω - e ω) *
      weightedInner w (M m ω - e ω) (M (m + 1) ω - M m ω)) μ ∧
    (∫ ω, 4 * weightedHNormSq w (M m ω - e ω) *
      weightedInner w (M m ω - e ω) (M (m + 1) ω - M m ω) ∂μ) = 0 := by
  have he_m := he.1.mono (𝓕.mono (Nat.zero_le m))
  have hM_m := hM.1.stronglyMeasurable m
  have hN : StronglyMeasurable[𝓕 m] (fun ω => weightedHNormSq w (M m ω - e ω)) :=
    @stronglyMeasurable_weightedHNormSq Ω 𝓑 (𝓕 m) _ _ (hM_m.sub he_m) w
  have hdint := (hM.1.integrable (m + 1)).sub (hM.1.integrable m)
  have hdz : μ[M (m + 1) - M m | 𝓕 m] =ᵐ[μ] 0 := by
    filter_upwards [condExp_sub (hM.1.integrable (m + 1)) (hM.1.integrable m) (𝓕 m),
      hM.1.condExp_ae_eq (Nat.le_succ m), hM.1.condExp_ae_eq (le_refl m)] with ω hsub hs ht
    simp only [Pi.sub_apply, hs, ht, sub_self] at hsub
    exact hsub
  have hcoord (B : 𝓑) :
      Integrable (fun ω => (weightedHNormSq w (M m ω - e ω) *
        (w B * (M m ω B - e ω B))) * (M (m + 1) ω B - M m ω B)) μ ∧
      (∫ ω, (weightedHNormSq w (M m ω - e ω) *
        (w B * (M m ω B - e ω B))) * (M (m + 1) ω B - M m ω B) ∂μ) = 0 := by
    let T : (𝓑 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj B
    have hgi : Integrable (fun ω => M (m + 1) ω B - M m ω B) μ :=
      T.integrable_comp hdint
    have hgz : μ[fun ω => M (m + 1) ω B - M m ω B | 𝓕 m] =ᵐ[μ] 0 := by
      have hzT : μ[T ∘ (M (m + 1) - M m) | 𝓕 m] =ᵐ[μ] 0 := by
        filter_upwards [T.comp_condExp_comm (m := 𝓕 m) hdint, hdz] with ω hT hz
        simpa only [Function.comp_apply, hz, map_zero, Pi.zero_apply] using hT.symm
      convert hzT using 1
      congr 1
    apply integral_predictable_mul_zero μ (𝓕 m) (𝓕.le m) _ hgi _ hgz
    · have hB := (continuous_apply B).comp_stronglyMeasurable (hM_m.sub he_m)
      exact hN.mul (hB.const_mul (w B))
    · refine ⟨(∑ C, w C) * w B, fun ω => ?_⟩
      rw [norm_mul, norm_mul, Real.norm_eq_abs (M m ω B - e ω B),
        Real.norm_of_nonneg (hw B).le,
        Real.norm_of_nonneg (weightedHNormSq_nonneg w _ hw)]
      exact mul_le_mul (weightedHNormSq_cube_le w _ _ hw (hM.2.1 m ω) (he.2 ω))
        (by simpa using (mul_le_mul_of_nonneg_left
          (cube_sub_binary_abs_le_one (hM.2.1 m ω) (he.2 ω) B) (hw B).le))
        (mul_nonneg (hw B).le (abs_nonneg _)) (Finset.sum_nonneg fun C _ => (hw C).le)
  have hid (ω : Ω) : 4 * weightedHNormSq w (M m ω - e ω) *
      weightedInner w (M m ω - e ω) (M (m + 1) ω - M m ω) =
      4 * ∑ B, (weightedHNormSq w (M m ω - e ω) *
        (w B * (M m ω B - e ω B))) * (M (m + 1) ω B - M m ω B) := by
    simp only [weightedInner, Pi.sub_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro B _
    ring
  simp_rw [hid]
  have hi := integrable_finsetSum Finset.univ (fun B _ => (hcoord B).1)
  refine ⟨hi.const_mul 4, ?_⟩
  rw [integral_const_mul, integral_finsetSum _ (fun B _ => (hcoord B).1)]
  simp only [(hcoord _).2, Finset.sum_const_zero, mul_zero]

-- @node: thm:martingale
/-- Suppose [the finite coordinate set is nonempty](hyp:h_finite),
[the coordinate weights are strictly positive](hyp:h_weights),
[M is a martingale taking values in the unit cube at every time and outcome,
converging almost surely to a terminal vector that lies in the cube almost
surely](hyp:h_process), and [e is a binary random vector strongly measurable
with respect to the initial information](hyp:h_center). Then [the nonnegative
expectation of the sum over all times of the squared weighted ℓ₁ sizes of the
increments of the coordinatewise cubic smoothing of M is at most 108 times
the difference between the terminal and initial expected quartic potentials
about e; this latter bound is itself at most 108 times the
terminal expected quartic potential](goal). -/
theorem martingale_cubic_energy_bound
    {Ω 𝓑 : Type*} [mΩ : MeasurableSpace Ω] [Fintype 𝓑]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (𝓕 : Filtration ℕ mΩ)
    (w : 𝓑 → ℝ) (M : ℕ → Ω → 𝓑 → ℝ) (Minf e : Ω → 𝓑 → ℝ)
    (h_finite : FiniteCutIndex 𝓑) (h_weights : PositiveWeights w)
    (h_process : CubeMartingale μ 𝓕 M Minf) (h_center : InitialBinaryCenter 𝓕 e) :
    ((∫⁻ ω, ∑' m : ℕ,
        ENNReal.ofReal (weightedL1Norm w (cubicMap (M (m + 1) ω) - cubicMap (M m ω)) ^ 2) ∂μ) ≤
      ENNReal.ofReal (108 * ((∫ ω, quarticPotential w (e ω) (Minf ω) ∂μ) -
        ∫ ω, quarticPotential w (e ω) (M 0 ω) ∂μ))) ∧
    (108 * ((∫ ω, quarticPotential w (e ω) (Minf ω) ∂μ) -
        ∫ ω, quarticPotential w (e ω) (M 0 ω) ∂μ) ≤
      108 * ∫ ω, quarticPotential w (e ω) (Minf ω) ∂μ) := by
  have he : StronglyMeasurable e := h_center.1.mono (𝓕.le 0)
  have hM (m : ℕ) : StronglyMeasurable (M m) :=
    (h_process.1.stronglyMeasurable m).mono (𝓕.le m)
  let P (m : ℕ) := ∫ ω, quarticPotential w (e ω) (M m ω) ∂μ
  let E (m : ℕ) (ω : Ω) :=
    weightedL1Norm w (cubicMap (M (m + 1) ω) - cubicMap (M m ω)) ^ 2
  have hPi (m : ℕ) : Integrable (fun ω => quarticPotential w (e ω) (M m ω)) μ :=
    integrable_quarticPotential_cube μ w h_weights (hM m) he
      (h_process.2.1 m) h_center.2
  have hEn (m : ℕ) (ω : Ω) : 0 ≤ E m ω := sq_nonneg _
  have hEs (m : ℕ) : StronglyMeasurable (E m) := by
    have hc : Continuous cubicSmooth := by
      unfold cubicSmooth
      fun_prop
    apply StronglyMeasurable.pow
    unfold weightedL1Norm
    apply Finset.stronglyMeasurable_fun_sum
    intro B _
    have hu := hc.comp_stronglyMeasurable
      ((continuous_apply B).comp_stronglyMeasurable (hM (m + 1)))
    have hv := hc.comp_stronglyMeasurable
      ((continuous_apply B).comp_stronglyMeasurable (hM m))
    simpa only [Real.norm_eq_abs, Pi.sub_apply, cubicMap] using
      ((hu.sub hv).norm.const_mul (w B))
  have hstep (m : ℕ) : Integrable (E m) μ ∧
      (∫ ω, E m ω ∂μ) ≤ 108 * (P (m + 1) - P m) := by
    obtain ⟨hdi, hdz⟩ := integral_quartic_martingale_derivative_zero
      μ 𝓕 w M Minf e h_weights h_process h_center m
    have hri := (((hPi (m + 1)).sub (hPi m)).sub hdi).const_mul 108
    have hb (ω : Ω) := flat_cubic_bound w (M m ω) (M (m + 1) ω) (e ω)
      h_finite h_weights ⟨h_process.2.1 m ω, h_process.2.1 (m + 1) ω⟩ (h_center.2 ω)
    have hEi : Integrable (E m) μ := hri.mono' (hEs m).aestronglyMeasurable
      (ae_of_all μ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hEn m ω)]; exact hb ω)
    refine ⟨hEi, ?_⟩
    have hint := integral_mono hEi hri hb
    simp only [Pi.sub_apply] at hri
    simp only [Pi.sub_apply] at hint
    have hsub := integral_sub ((hPi (m + 1)).sub (hPi m)) hdi
    simp only [Pi.sub_apply] at hsub
    rw [integral_const_mul, hsub,
      integral_sub (hPi (m + 1)) (hPi m), hdz, sub_zero] at hint
    exact hint
  have hfinite (L : ℕ) :
      (∑ m ∈ Finset.range L, ∫ ω, E m ω ∂μ) ≤ 108 * (P L - P 0) := by
    induction L with
    | zero => simp
    | succ L ih =>
      rw [Finset.sum_range_succ]
      have h := (hstep L).2
      linarith
  have hPlim : Tendsto P atTop
      (𝓝 (∫ ω, quarticPotential w (e ω) (Minf ω) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (∑ B, w B) ^ 2)
    · intro m
      exact (stronglyMeasurable_quarticPotential (hM m) he w).aestronglyMeasurable
    · exact integrable_const _
    · intro m
      exact ae_of_all μ fun ω => quarticPotential_cube_bound w _ _ h_weights
        (h_process.2.1 m ω) (h_center.2 ω)
    · filter_upwards [h_process.2.2.1] with ω hω
      have hc : Continuous (fun u : 𝓑 → ℝ => quarticPotential w (e ω) u) := by
        unfold quarticPotential weightedHNormSq
        fun_prop
      exact (hc.tendsto (Minf ω)).comp hω
  constructor
  · rw [lintegral_tsum (fun m => (hEs m).measurable.ennreal_ofReal.aemeasurable)]
    have hEq (m : ℕ) : (∫⁻ ω, ENNReal.ofReal (E m ω) ∂μ) =
        ENNReal.ofReal (∫ ω, E m ω ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal (hstep m).1 (ae_of_all μ (hEn m))).symm
    simp_rw [hEq]
    apply le_of_tendsto_of_tendsto (ENNReal.tendsto_nat_tsum _)
      (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_const_nhds.mul (hPlim.sub_const (P 0))))
    exact Eventually.of_forall fun L => by
      change (∑ m ∈ Finset.range L, ENNReal.ofReal (∫ ω, E m ω ∂μ)) ≤
        ENNReal.ofReal (108 * (P L - P 0))
      rw [← ENNReal.ofReal_sum_of_nonneg
        (fun m _ => integral_nonneg (μ := μ) (hEn m))]
      exact ENNReal.ofReal_le_ofReal (hfinite L)
  · have hP0 : 0 ≤ P 0 := integral_nonneg fun ω => sq_nonneg _
    dsimp [P] at hP0
    linarith


end Papers.OaiMetricMarkovCotype
