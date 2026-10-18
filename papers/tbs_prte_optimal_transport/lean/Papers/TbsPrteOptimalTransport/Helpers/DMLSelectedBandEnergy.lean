module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLChangingOutcomeBands
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationContinuousResidual
public import Papers.TbsPrteOptimalTransport.Helpers.DMLTailBaselineConvergence
/-! Selected observed-score energy is controlled by treated conditional energy.
Binary treatment selects the treated cell; normalization contributes its mass,
which is at most one, and clipped denominators give a uniform square bound. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
set_option linter.style.openClassical false
open scoped Classical Topology

-- @node: selected_treatment_sq_integral
/-- If [the instrument selection set is measurable](hyp:hD), [the outcome function is
measurable](hyp:hf), and [treatment is binary almost surely](hyp:hW), then [the integrated
squared selected treated score equals the inverse squared denominator times the mass of
the selected treated cell times the second moment of the outcome function under that
cell's normalized outcome distribution](goal). -/
lemma selected_treatment_sq_integral {Z : Type*} [MeasurableSpace Z]
    (ν : Measure (ℝ × ℝ × Z)) [IsFiniteMeasure ν]
    (D : Set Z) (hD : MeasurableSet D) (f : ℝ → ℝ) (hf : Measurable f)
    (hW : ∀ᵐ a ∂ν, a.2.1 = 0 ∨ a.2.1 = 1) (c : ℝ) :
    (∫ a, (indicator (a.2.2 ∈ D) * a.2.1 / c * f a.1) ^ 2 ∂ν) =
      c⁻¹ ^ 2 * (ν.restrict {a | a.2.1 = 1 ∧ a.2.2 ∈ D}).real univ *
        ∫ y, f y ^ 2 ∂((ν.restrict {a | a.2.1 = 1 ∧ a.2.2 ∈ D}) univ)⁻¹ •
          (ν.restrict {a | a.2.1 = 1 ∧ a.2.2 ∈ D}).map Prod.fst := by
  let E : Set (ℝ × ℝ × Z) := {a | a.2.1 = 1 ∧ a.2.2 ∈ D}
  have hE : MeasurableSet E :=
    (measurableSet_eq_fun measurable_snd.fst measurable_const).inter
      (hD.preimage measurable_snd.snd)
  have hid : (fun a : ℝ × ℝ × Z =>
      (indicator (a.2.2 ∈ D) * a.2.1 / c * f a.1) ^ 2) =ᵐ[ν]
      (fun a => c⁻¹ ^ 2 * E.indicator (fun a => f a.1 ^ 2) a) := by
    filter_upwards [hW] with a ha
    rcases ha with ha | ha <;> by_cases hz : a.2.2 ∈ D <;>
      simp [ha, hz, E, indicator, Set.indicator, div_eq_mul_inv, mul_pow]
  rw [integral_congr_ae hid, integral_const_mul, integral_indicator hE,
    normalized_selected_mean_eq_average ν D (fun y => f y ^ 2) (hf.pow_const 2)]
  rw [mul_assoc]
  congr 1
  exact (measure_smul_average (μ := ν.restrict E) (fun a => f a.1 ^ 2)).symm

-- @node: selected_treatment_sq_integral_le
/-- If [the instrument selection set is measurable](hyp:hD), [the outcome function is
measurable](hyp:hf), [treatment is binary almost surely](hyp:hW), [the denominator floor
is positive](hyp:hδ), and [the denominator is at least that floor](hyp:hc), then [the
integrated squared selected treated score is bounded by the selected treated outcome
second moment divided by the squared floor](goal). -/
lemma selected_treatment_sq_integral_le {Z : Type*} [MeasurableSpace Z]
    (ν : Measure (ℝ × ℝ × Z)) [IsProbabilityMeasure ν]
    (D : Set Z) (hD : MeasurableSet D) (f : ℝ → ℝ) (hf : Measurable f)
    (hW : ∀ᵐ a ∂ν, a.2.1 = 0 ∨ a.2.1 = 1)
    (c δ : ℝ) (hδ : 0 < δ) (hc : δ ≤ c) :
    (∫ a, (indicator (a.2.2 ∈ D) * a.2.1 / c * f a.1) ^ 2 ∂ν) ≤
      δ⁻¹ ^ 2 * ∫ y, f y ^ 2
        ∂((ν.restrict {a | a.2.1 = 1 ∧ a.2.2 ∈ D}) univ)⁻¹ •
          (ν.restrict {a | a.2.1 = 1 ∧ a.2.2 ∈ D}).map Prod.fst := by
  rw [selected_treatment_sq_integral ν D hD f hf hW c]
  have hm : (ν.restrict {a | a.2.1 = 1 ∧ a.2.2 ∈ D}).real univ ≤ 1 := by
    rw [measureReal_def, Measure.restrict_apply MeasurableSet.univ, univ_inter]
    have h : ν {a | a.2.1 = 1 ∧ a.2.2 ∈ D} ≤ ν univ := measure_mono (subset_univ _)
    simpa only [measure_univ, ENNReal.toReal_one] using
      ENNReal.toReal_mono (measure_ne_top ν univ) h
  have hc0 : 0 < c := hδ.trans_le hc
  have hinv : c⁻¹ ^ 2 ≤ δ⁻¹ ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr hc0.le) (inv_le_inv₀ hc0 hδ |>.mpr hc) 2
  have hi : 0 ≤ ∫ y, f y ^ 2
      ∂((ν.restrict {a | a.2.1 = 1 ∧ a.2.2 ∈ D}) univ)⁻¹ •
        (ν.restrict {a | a.2.1 = 1 ∧ a.2.2 ∈ D}).map Prod.fst :=
    integral_nonneg (fun y => sq_nonneg (f y))
  calc
    _ ≤ c⁻¹ ^ 2 * 1 * _ := by gcongr
    _ ≤ δ⁻¹ ^ 2 * _ := by rw [mul_one]; exact mul_le_mul_of_nonneg_right hinv hi

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
  [Fintype Z] [DecidableEq Z]

-- @node: observationLaw_integral_selected_kernel
/-- For [a measurable function of the observed data](hyp:hf) that is [integrable under
the observation distribution](hyp:hi), [its conditional mean given covariates is
integrable, and its population mean equals the covariate average of its mean under the
conditional distribution of outcome, treatment, and instrument](goal). -/
lemma observationLaw_integral_selected_kernel (M : LatentIVModel Ω X Z)
    (f : Obs X Z → ℝ) (hf : Measurable f) (hi : Integrable f (observationLaw M)) :
    Integrable (fun x => ∫ a : ℝ × ℝ × Z, f (x, a.2.2, a.2.1, a.1)
      ∂condDistrib (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure x)
      (xLaw M) ∧
    (∫ o, f o ∂observationLaw M) =
      ∫ x, ∫ a : ℝ × ℝ × Z, f (x, a.2.2, a.2.1, a.1)
        ∂condDistrib (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure x
        ∂xLaw M := by
  haveI : IsProbabilityMeasure (xLaw M) := by
    unfold xLaw
    exact Measure.isProbabilityMeasure_map M.measX.aemeasurable
  let F : X × (ℝ × ℝ × Z) → ℝ := fun p => f (p.1, p.2.2.2, p.2.2.1, p.2.1)
  have hF : Measurable F := by fun_prop
  have hobs : Measurable (fun s => (M.Xv s, M.Zv s, M.W s, M.Y s)) := by
    first | fun_prop | exact M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
  have hjoint : Measurable (fun s => (M.Y s, M.W s, M.Zv s)) := by
    first | fun_prop | exact M.measY.prodMk (M.measW.prodMk M.measZ)
  have hpair := M.measX.prodMk hjoint
  have hi' := (integrable_map_measure hf.aestronglyMeasurable hobs.aemeasurable).mp hi
  have hFi : Integrable F (M.law.toMeasure.map
      (fun s => (M.Xv s, M.Y s, M.W s, M.Zv s))) :=
    (integrable_map_measure hF.aestronglyMeasurable hpair.aemeasurable).mpr hi'
  refine ⟨hFi.integral_condDistrib_map hjoint.aemeasurable, ?_⟩
  have hmap : (xLaw M) ⊗ₘ
      condDistrib (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure =
      M.law.toMeasure.map (fun s => (M.Xv s, M.Y s, M.W s, M.Zv s)) :=
    compProd_map_condDistrib hjoint.aemeasurable
  have hprod : Integrable F ((xLaw M) ⊗ₘ
      condDistrib (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure) := by
    rw [hmap]
    exact hFi
  calc
    _ = ∫ s, f (M.Xv s, M.Zv s, M.W s, M.Y s) ∂M.law.toMeasure :=
      integral_map hobs.aemeasurable hf.aestronglyMeasurable
    _ = ∫ p, F p ∂((xLaw M) ⊗ₘ
        condDistrib (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure) := by
      rw [hmap, integral_map hpair.aemeasurable hF.aestronglyMeasurable]
    _ = _ := Measure.integral_compProd hprod

-- @node: observationLaw_selected_sq_integral_le
/-- Suppose [the covariate–outcome function is measurable](hyp:hf), [the denominator is
measurable](hyp:hc), [its floor is positive](hyp:hδ), and [it is at least that floor almost
everywhere](hyp:hclip). If [the squared selected treated score is integrable](hyp:hi)
and [the conditional treated second moment is integrable over covariates](hyp:hfi),
then [the observed score's second moment is at most the integrated conditional treated
second moment divided by the squared denominator floor](goal). -/
lemma observationLaw_selected_sq_integral_le (M : LatentIVModel Ω X Z)
    (L : LevelData Z X) (k : ℕ) (f : X × ℝ → ℝ) (hf : Measurable f)
    (c : X → ℝ) (hc : Measurable c) (δ : ℝ) (hδ : 0 < δ)
    (hclip : ∀ᵐ x ∂xLaw M, δ ≤ c x)
    (hi : Integrable (fun o : Obs X Z =>
      (indicator (o.2.1 ∈ L.S k) * o.2.2.1 / c o.1 * f (o.1, o.2.2.2)) ^ 2)
      (observationLaw M))
    (hfi : Integrable (fun x => ∫ y, f (x, y) ^ 2 ∂treatedLaw M L k x) (xLaw M)) :
    (∫ o : Obs X Z,
      (indicator (o.2.1 ∈ L.S k) * o.2.2.1 / c o.1 * f (o.1, o.2.2.2)) ^ 2
      ∂observationLaw M) ≤
      δ⁻¹ ^ 2 * ∫ x, ∫ y, f (x, y) ^ 2 ∂treatedLaw M L k x ∂xLaw M := by
  have hm : Measurable (fun o : Obs X Z =>
      (indicator (o.2.1 ∈ L.S k) * o.2.2.1 / c o.1 * f (o.1, o.2.2.2)) ^ 2) := by
    fun_prop
  obtain ⟨hi', heq⟩ := observationLaw_integral_selected_kernel M _ hm hi
  rw [heq, ← integral_const_mul]
  apply integral_mono_ae hi' (hfi.const_mul _)
  filter_upwards [hclip, population_joint_treatment_binary M] with x hx hW
  exact selected_treatment_sq_integral_le _ (L.S k : Set Z)
    (L.S k).finite_toSet.measurableSet (fun y => f (x, y))
    (hf.comp (measurable_const.prodMk measurable_id)) hW (c x) δ hδ hx

-- @node: observationLaw_selected_sq_tendsto_probability_zero
/-- Suppose [every fitted covariate–outcome function is measurable](hyp:hf), [every
fitted denominator is measurable](hyp:hc), [the common floor is positive](hyp:hδ),
and [all denominators are at least that floor almost everywhere](hyp:hclip). If [all squared selected
treated scores are integrable](hyp:hi), [their conditional treated second moments are
integrable over covariates](hyp:hfi), and [these integrated conditional second moments
converge to zero in probability](hyp:hr), then [the observed selected treated score
second moments also converge to zero in probability](goal). -/
lemma observationLaw_selected_sq_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X) (k : ℕ)
    (f : ℕ → A → X × ℝ → ℝ) (c : ℕ → A → X → ℝ)
    (hf : ∀ n a, Measurable (f n a)) (hc : ∀ n a, Measurable (c n a))
    (δ : ℝ) (hδ : 0 < δ) (hclip : ∀ n a, ∀ᵐ x ∂xLaw M, δ ≤ c n a x)
    (hi : ∀ n a, Integrable (fun o : Obs X Z =>
      (indicator (o.2.1 ∈ L.S k) * o.2.2.1 / c n a o.1 * f n a (o.1, o.2.2.2)) ^ 2)
      (observationLaw M))
    (hfi : ∀ n a, Integrable
      (fun x => ∫ y, f n a (x, y) ^ 2 ∂treatedLaw M L k x) (xLaw M))
    (hr : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, ∫ y, f n a (x, y) ^ 2
        ∂treatedLaw M L k x ∂xLaw M) atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        (indicator (o.2.1 ∈ L.S k) * o.2.2.1 / c n a o.1 * f n a (o.1, o.2.2.2)) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  have ht := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    (show Continuous (fun t : ℝ => δ⁻¹ ^ 2 * t) by fun_prop).continuousAt hr
  simp only [mul_zero] at ht
  apply probability_zero_of_nonneg_le μ _ _ ht
  intro n
  apply Eventually.of_forall
  intro a
  exact ⟨integral_nonneg (fun o => sq_nonneg _),
    observationLaw_selected_sq_integral_le M L k (f n a) (hf n a) (c n a)
      (hc n a) δ hδ (hclip n a) (hi n a) (hfi n a)⟩

-- @node: observationLaw_selected_memLp
/-- If [the covariate–outcome function is measurable](hyp:hf), [the denominator is
measurable](hyp:hc), [the denominator floor is positive](hyp:hδ), [the denominator
is at least that floor almost everywhere](hyp:hclip), and [the outcome function is uniformly
bounded in absolute value for almost every covariate](hyp:hbound), then [the selected
treated score divided by this denominator has a finite second moment under the
observation distribution](goal). -/
lemma observationLaw_selected_memLp (M : LatentIVModel Ω X Z)
    (L : LevelData Z X) (k : ℕ) (f : X × ℝ → ℝ) (hf : Measurable f)
    (c : X → ℝ) (hc : Measurable c) (δ B : ℝ) (hδ : 0 < δ)
    (hclip : ∀ᵐ x ∂xLaw M, δ ≤ c x)
    (hbound : ∀ᵐ x ∂xLaw M, ∀ y, |f (x, y)| ≤ B) :
    MemLp (fun o : Obs X Z =>
      indicator (o.2.1 ∈ L.S k) * o.2.2.1 / c o.1 * f (o.1, o.2.2.2))
      2 (observationLaw M) := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  have hm : Measurable (fun o : Obs X Z =>
      indicator (o.2.1 ∈ L.S k) * o.2.2.1 / c o.1 * f (o.1, o.2.2.2)) := by fun_prop
  apply MemLp.of_bound hm.aestronglyMeasurable (B / δ)
  filter_upwards [observationLaw_covariate_ae M _ hclip,
    observationLaw_covariate_ae M _ hbound,
    observationLaw_treatment_range M] with o hc' hf' hW
  have hs : |indicator (o.2.1 ∈ L.S k)| ≤ 1 := by
    unfold indicator
    split_ifs <;> norm_num
  have hw : |o.2.2.1| ≤ 1 := by rw [abs_of_nonneg hW.1]; exact hW.2
  have hB : 0 ≤ B := (abs_nonneg _).trans (hf' o.2.2.2)
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_mul,
    abs_of_pos (hδ.trans_le hc')]
  calc
    _ ≤ (1 * 1) / c o.1 * B := by
      gcongr
      · exact div_nonneg (by norm_num) (hδ.trans_le hc').le
      · exact (hδ.trans_le hc').le
      · exact hf' _
    _ = B / c o.1 := by ring
    _ ≤ B / δ := div_le_div_of_nonneg_left hB hδ hc'

-- @node: observationLaw_selected_centered_sq_tendsto_probability_zero
/-- Suppose [all fitted outcome functions are measurable](hyp:hf), [all fitted
denominators are measurable](hyp:hc), [the denominator floor is positive](hyp:hδ),
[the outcome bound is nonnegative](hyp:hB), [denominators are at least the common floor
almost everywhere](hyp:hclip), and [the outcome functions obey the common absolute
bound](hyp:hbound). If [each conditional treated outcome function has a finite second
moment](hyp:hmem), [its conditional second moment is integrable over covariates](hyp:hfi),
and [the integrated uncentered second moments converge to zero in probability](hyp:hr),
then [the observed second moments of the selected treated scores, centered by their
conditional treated means and divided by the fitted denominators, converge to zero
in probability](goal). -/
lemma observationLaw_selected_centered_sq_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X) (k : ℕ)
    (f : ℕ → A → X × ℝ → ℝ) (c : ℕ → A → X → ℝ)
    (hf : ∀ n a, Measurable (f n a)) (hc : ∀ n a, Measurable (c n a))
    (δ B : ℝ) (hδ : 0 < δ) (hB : 0 ≤ B)
    (hclip : ∀ n a, ∀ᵐ x ∂xLaw M, δ ≤ c n a x)
    (hbound : ∀ n a, ∀ᵐ x ∂xLaw M, ∀ y, |f n a (x, y)| ≤ B)
    (hmem : ∀ n a x, MemLp (fun y => f n a (x, y)) 2 (treatedLaw M L k x))
    (hfi : ∀ n a, Integrable
      (fun x => ∫ y, f n a (x, y) ^ 2 ∂treatedLaw M L k x) (xLaw M))
    (hr : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, ∫ y, f n a (x, y) ^ 2
        ∂treatedLaw M L k x ∂xLaw M) atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        (indicator (o.2.1 ∈ L.S k) * o.2.2.1 / c n a o.1 *
          (f n a (o.1, o.2.2.2) - ∫ y, f n a (o.1, y) ∂treatedLaw M L k o.1)) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  let d : ℕ → A → X × ℝ → ℝ := fun n a p =>
    f n a p - ∫ y, f n a (p.1, y) ∂treatedLaw M L k p.1
  have hd n a : Measurable (d n a) := by
    dsimp only [d]
    exact (hf n a).sub
      ((measurable_treatedLaw_integral_prod M L k (f n a) (hf n a)).comp measurable_fst)
  have hb n a : ∀ᵐ x ∂xLaw M, ∀ y, |d n a (x, y)| ≤ 2 * B := by
    filter_upwards [hbound n a] with x hx
    haveI := treatedLaw_isFiniteMeasure M L k x
    have hi : |∫ y, f n a (x, y) ∂treatedLaw M L k x| ≤ B := by
      calc
        _ ≤ B * (treatedLaw M L k x).real univ := by
          simpa only [Real.norm_eq_abs] using norm_integral_le_of_norm_le_const
            (μ := treatedLaw M L k x) (f := fun y => f n a (x, y)) (C := B)
            (Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hx y)
        _ ≤ B * 1 := mul_le_mul_of_nonneg_left (treatedLaw_mass_le_one M L k x) hB
        _ = B := mul_one B
    intro y
    exact (abs_sub _ _).trans (by dsimp only [d]; linarith [hx y])
  apply observationLaw_selected_sq_tendsto_probability_zero M μ L k d c hd hc δ hδ hclip
  · intro n a
    exact (observationLaw_selected_memLp M L k (d n a) (hd n a) (c n a) (hc n a)
      δ (2 * B) hδ (hclip n a) (hb n a)).integrable_sq
  · intro n a
    exact (treatedLaw_integrated_centered_sq_le M L k (f n a) (hf n a)
      (hmem n a) (hfi n a)).1
  · exact treatedLaw_centered_sq_tendsto_probability_zero M μ L k f hf hmem hfi hr

end Papers.TbsPrteOptimalTransport
