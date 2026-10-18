module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLSelectedBandEnergy
public import Papers.TbsPrteOptimalTransport.Helpers.DMLIPWConvergence
/-! Changing clipped denominators in selected continuous score terms.
Treated conditional numerator energy and covariate denominator energy jointly
control the observed score discrepancy. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

-- @node: dml_clipped_ipw_residual_energy_tendsto_probability_zero
/-- Assume [a positive denominator floor](hyp:hc), measurability of [the true
denominator](hyp:hp), [true regression](hyp:hj), [outcome](hyp:hy), and [assignment
weight](hyp:ha), and measurability of [every fitted denominator](hyp:hph) and [fitted
regression](hyp:hjh). If [regression errors](hyp:heJ) and [denominator errors](hyp:heP)
are square integrable, [true and fitted denominators exceed the floor almost everywhere](hyp:hclip),
[the assignment weight has absolute value at most one almost everywhere](hyp:hassign),
[the true residual has a common absolute bound almost everywhere](hyp:hres),
[regression mean-square errors vanish in probability](hyp:hrJ), and [denominator
mean-square errors vanish in probability](hyp:hrP), then [the difference between fitted
and true assignment-weighted inverse-probability residuals has integrated square
converging to zero in probability](goal). -/
lemma dml_clipped_ipw_residual_energy_tendsto_probability_zero {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) (p j y a : B → ℝ)
    (ph jh : ℕ → A → B → ℝ) (c R : ℝ)
    (hc : 0 < c) (hp : Measurable p) (hj : Measurable j)
    (hy : Measurable y) (ha : Measurable a)
    (hph : ∀ n t, Measurable (ph n t)) (hjh : ∀ n t, Measurable (jh n t))
    (heJ : ∀ n t, MemLp (fun x => jh n t x - j x) 2 ν)
    (heP : ∀ n t, MemLp (fun x => ph n t x - p x) 2 ν)
    (hclip : ∀ n t, ∀ᵐ x ∂ν, c ≤ p x ∧ c ≤ ph n t x)
    (hassign : ∀ᵐ x ∂ν, |a x| ≤ 1)
    (hres : ∀ᵐ x ∂ν, |y x - j x| ≤ R)
    (hrJ : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (jh n t x - j x) ^ 2 ∂ν) atTop (fun _ _ => 0))
    (hrP : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (ph n t x - p x) ^ 2 ∂ν) atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x,
        (a x / ph n t x * (y x - jh n t x) - a x / p x * (y x - j x)) ^ 2 ∂ν)
      atTop (fun _ _ => 0) := by
  have hJ := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    (show Continuous (fun z : ℝ => (2 / c ^ 2) * z) by fun_prop).continuousAt hrJ
  have hP := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    (show Continuous (fun z : ℝ => -(2 * R ^ 2 / (c ^ 2) ^ 2 * z)) by fun_prop).continuousAt hrP
  simp only [mul_zero, neg_zero] at hJ hP
  have hs := hJ.sub hP
  simp only [sub_zero, sub_neg_eq_add] at hs
  apply probability_zero_of_nonneg_le μ _ _ hs
  intro n
  apply Eventually.of_forall
  intro t
  exact ⟨integral_nonneg (fun x => sq_nonneg _),
    (clipped_ipw_residual_integrated_sq_bound ν p (ph n t) j (jh n t) y a c R
      hc hp (hph n t) hj (hjh n t) hy ha (heJ n t) (heP n t)
      (hclip n t) hassign hres).2⟩

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
  [Fintype Z] [DecidableEq Z]

-- @node: observationLaw_changing_selected_denominator_sq_tendsto_probability_zero
/-- Assume [a positive denominator floor](hyp:hc), [a measurable true covariate-outcome
function](hyp:hf0), [measurable fitted functions](hyp:hfh), [a measurable true
denominator](hyp:hp), and [measurable fitted denominators](hyp:hph). Suppose [true
and fitted denominators exceed the floor almost everywhere over covariates](hyp:hclip),
[the true function is uniformly bounded over outcomes for almost every covariate](hyp:hb0),
[the function errors have a common uniform bound over outcomes for almost every
covariate](hyp:hbd), [denominator errors are square integrable](hyp:heP), and
[the conditional squared function errors are integrable over covariates](hyp:hfi).
If [the treated integrated squared function errors vanish in probability](hyp:hrf)
and [denominator errors vanish in covariate mean square in probability](hyp:hrp), then
[the selected, inverse-probability-weighted fitted function converges to its true
counterpart in observation-law mean square in probability](goal). -/
lemma observationLaw_changing_selected_denominator_sq_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X) (k : ℕ)
    (f0 : X × ℝ → ℝ) (fh : ℕ → A → X × ℝ → ℝ)
    (p : X → ℝ) (ph : ℕ → A → X → ℝ) (c B D : ℝ)
    (hc : 0 < c) (hf0 : Measurable f0) (hfh : ∀ n a, Measurable (fh n a))
    (hp : Measurable p) (hph : ∀ n a, Measurable (ph n a))
    (hclip : ∀ n a, ∀ᵐ x ∂xLaw M, c ≤ p x ∧ c ≤ ph n a x)
    (hb0 : ∀ᵐ x ∂xLaw M, ∀ y, |f0 (x, y)| ≤ B)
    (hbd : ∀ n a, ∀ᵐ x ∂xLaw M, ∀ y, |fh n a (x, y) - f0 (x, y)| ≤ D)
    (heP : ∀ n a, MemLp (fun x => ph n a x - p x) 2 (xLaw M))
    (hfi : ∀ n a, Integrable (fun x => ∫ y,
      (fh n a (x, y) - f0 (x, y)) ^ 2 ∂treatedLaw M L k x) (xLaw M))
    (hrf : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, ∫ y, (fh n a (x, y) - f0 (x, y)) ^ 2
        ∂treatedLaw M L k x ∂xLaw M) atTop (fun _ _ => 0))
    (hrp : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, (ph n a x - p x) ^ 2 ∂xLaw M) atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        (indicator (o.2.1 ∈ L.S k) * o.2.2.1 / ph n a o.1 * fh n a (o.1, o.2.2.2) -
          indicator (o.2.1 ∈ L.S k) * o.2.2.1 / p o.1 * f0 (o.1, o.2.2.2)) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  let G0 : Obs X Z → ℝ := fun o => indicator (o.2.1 ∈ L.S k) * o.2.2.1 * f0 (o.1, o.2.2.2)
  let Gh : ℕ → A → Obs X Z → ℝ := fun n a o =>
    indicator (o.2.1 ∈ L.S k) * o.2.2.1 * fh n a (o.1, o.2.2.2)
  have hG0 : Measurable G0 := by fun_prop
  have hGh n a : Measurable (Gh n a) := by fun_prop
  have hid n a o : Gh n a o - G0 o =
      indicator (o.2.1 ∈ L.S k) * o.2.2.1 / 1 *
        (fh n a (o.1, o.2.2.2) - f0 (o.1, o.2.2.2)) := by
    dsimp only [Gh, G0]
    ring
  have hmem n a : MemLp (fun o => Gh n a o - G0 o) 2 (observationLaw M) := by
    simpa only [hid] using observationLaw_selected_memLp M L k
      (fun z => fh n a z - f0 z) (by fun_prop) (fun _ => 1) measurable_const
      1 D (by norm_num) (Eventually.of_forall fun _ => le_rfl) (hbd n a)
  have hrf' := observationLaw_selected_sq_tendsto_probability_zero M μ L k
    (fun n a z => fh n a z - f0 z) (fun _ _ _ => 1)
    (by intro n a; fun_prop) (fun _ _ => measurable_const) 1 (by norm_num)
    (fun _ _ => Eventually.of_forall fun _ => le_rfl)
    (fun n a => by simpa only [← hid] using (hmem n a).integrable_sq) hfi hrf
  have hrp' : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z, (ph n a o.1 - p o.1) ^ 2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
    have hidp n a := observationLaw_covariate_integral M
      (fun x => (ph n a x - p x) ^ 2) (by fun_prop)
    simpa only [hidp] using hrp
  have hbG : ∀ᵐ o ∂observationLaw M, |G0 o| ≤ B := by
    filter_upwards [observationLaw_covariate_ae M _ hb0,
      observationLaw_treatment_range M] with o ho hw
    have hs : |indicator (o.2.1 ∈ L.S k)| ≤ 1 := by
      unfold indicator
      split_ifs <;> norm_num
    have hB : 0 ≤ B := (abs_nonneg _).trans (ho o.2.2.2)
    dsimp only [G0]
    rw [abs_mul, abs_mul, abs_of_nonneg hw.1]
    calc
      _ ≤ 1 * 1 * B := by
        gcongr
        · exact hw.1
        · exact hw.2
        · exact ho o.2.2.2
      _ = B := by ring
  have ht := dml_clipped_ipw_residual_energy_tendsto_probability_zero μ (observationLaw M)
    (fun o => p o.1) (fun o => -G0 o) (fun _ => 0) (fun _ => 1)
    (fun n a o => ph n a o.1) (fun n a o => -Gh n a o) c B hc
    (by fun_prop) (by fun_prop) measurable_const measurable_const
    (by intro n a; fun_prop) (by intro n a; fun_prop)
    (fun n a => by
      convert (hmem n a).neg using 1
      ext o
      simp only [Pi.neg_apply]
      ring)
    (fun n a => (heP n a).comp_measurePreserving (observationLaw_fst_measurePreserving M))
    (fun n a => observationLaw_covariate_ae M _ (hclip n a))
    (Eventually.of_forall fun _ => by norm_num)
    (by simpa only [zero_sub, neg_neg] using hbG)
    (by
      have hs n a o : (-Gh n a o - -G0 o) ^ 2 =
          (indicator (o.2.1 ∈ L.S k) * o.2.2.1 / 1 *
            (fh n a (o.1, o.2.2.2) - f0 (o.1, o.2.2.2))) ^ 2 := by
        rw [← hid]
        ring
      simpa only [hs] using hrf') hrp'
  have heq n a o :
      1 / ph n a o.1 * (0 - -Gh n a o) - 1 / p o.1 * (0 - -G0 o) =
        indicator (o.2.1 ∈ L.S k) * o.2.2.1 / ph n a o.1 * fh n a (o.1, o.2.2.2) -
          indicator (o.2.1 ∈ L.S k) * o.2.2.1 / p o.1 * f0 (o.1, o.2.2.2) := by
    dsimp only [Gh, G0]
    simp only [div_eq_mul_inv]
    ring
  simpa only [heq] using ht

-- @node: treatedLaw_centered_abs_bound
/-- If [a bound is nonnegative](hyp:hB) and [a covariate-outcome function is bounded
in absolute value by it for every outcome and almost every covariate](hyp:hb), then
[subtracting the treated-law integral leaves an absolute value at most twice that
bound for every outcome and almost every covariate](goal). -/
lemma treatedLaw_centered_abs_bound
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (k : ℕ)
    (f : X × ℝ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ᵐ x ∂xLaw M, ∀ y, |f (x, y)| ≤ B) :
    ∀ᵐ x ∂xLaw M, ∀ y,
      |f (x, y) - ∫ z, f (x, z) ∂treatedLaw M L k x| ≤ 2 * B := by
  filter_upwards [hb] with x hx
  haveI := treatedLaw_isFiniteMeasure M L k x
  have hi : |∫ z, f (x, z) ∂treatedLaw M L k x| ≤ B := by
    calc
      _ ≤ B * (treatedLaw M L k x).real univ := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_of_norm_le_const
          (μ := treatedLaw M L k x) (f := fun z => f (x, z)) (C := B)
          (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hx z)
      _ ≤ B * 1 := mul_le_mul_of_nonneg_left (treatedLaw_mass_le_one M L k x) hB
      _ = B := mul_one B
  intro y
  exact (abs_sub _ _).trans (by linarith [hx y])

-- @node: observationLaw_changing_selected_centered_denominator_sq_tendsto_probability_zero
/-- Assume [a positive denominator floor](hyp:hc), [a nonnegative true-function bound](hyp:hB),
and [a nonnegative function-error bound](hyp:hD). Suppose [the true function](hyp:hf0),
[all fitted functions](hyp:hfh), [the true denominator](hyp:hp), and [all fitted
denominators](hyp:hph) are measurable, [true and fitted denominators exceed the floor
almost everywhere over covariates](hyp:hclip), [the true function obeys its uniform
absolute bound over outcomes almost everywhere](hyp:hb0), and [function errors obey
their uniform absolute bound over outcomes almost everywhere](hyp:hbd). If [the true
function has square-integrable treated-law sections](hyp:hm0), [all fitted functions
have square-integrable treated-law sections](hyp:hmh), [denominator errors are square
integrable over covariates](hyp:heP), [conditional squared function errors are integrable
over covariates](hyp:hfi), [treated integrated squared function errors vanish in
probability](hyp:hrf), and [denominator errors vanish in covariate mean square in
probability](hyp:hrp), then [the selected, inverse-probability-weighted fitted function,
centered by its own treated-law integral, converges to the corresponding centered true
function in observation-law mean square in probability](goal). -/
lemma observationLaw_changing_selected_centered_denominator_sq_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X) (k : ℕ)
    (f0 : X × ℝ → ℝ) (fh : ℕ → A → X × ℝ → ℝ)
    (p : X → ℝ) (ph : ℕ → A → X → ℝ) (c B D : ℝ)
    (hc : 0 < c) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hf0 : Measurable f0) (hfh : ∀ n a, Measurable (fh n a))
    (hp : Measurable p) (hph : ∀ n a, Measurable (ph n a))
    (hclip : ∀ n a, ∀ᵐ x ∂xLaw M, c ≤ p x ∧ c ≤ ph n a x)
    (hb0 : ∀ᵐ x ∂xLaw M, ∀ y, |f0 (x, y)| ≤ B)
    (hbd : ∀ n a, ∀ᵐ x ∂xLaw M, ∀ y, |fh n a (x, y) - f0 (x, y)| ≤ D)
    (hm0 : ∀ x, MemLp (fun y => f0 (x, y)) 2 (treatedLaw M L k x))
    (hmh : ∀ n a x, MemLp (fun y => fh n a (x, y)) 2 (treatedLaw M L k x))
    (heP : ∀ n a, MemLp (fun x => ph n a x - p x) 2 (xLaw M))
    (hfi : ∀ n a, Integrable (fun x => ∫ y,
      (fh n a (x, y) - f0 (x, y)) ^ 2 ∂treatedLaw M L k x) (xLaw M))
    (hrf : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, ∫ y, (fh n a (x, y) - f0 (x, y)) ^ 2
        ∂treatedLaw M L k x ∂xLaw M) atTop (fun _ _ => 0))
    (hrp : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, (ph n a x - p x) ^ 2 ∂xLaw M) atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        (indicator (o.2.1 ∈ L.S k) * o.2.2.1 / ph n a o.1 *
            (fh n a (o.1, o.2.2.2) - ∫ y, fh n a (o.1, y) ∂treatedLaw M L k o.1) -
          indicator (o.2.1 ∈ L.S k) * o.2.2.1 / p o.1 *
            (f0 (o.1, o.2.2.2) - ∫ y, f0 (o.1, y) ∂treatedLaw M L k o.1)) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  let center := fun (f : X × ℝ → ℝ) (z : X × ℝ) =>
    f z - ∫ y, f (z.1, y) ∂treatedLaw M L k z.1
  let d := fun n a z => fh n a z - f0 z
  have hcm (f : X × ℝ → ℝ) (hf : Measurable f) : Measurable (center f) := by
    exact hf.sub
      ((measurable_treatedLaw_integral_prod M L k f hf).comp measurable_fst)
  have hd n a : Measurable (d n a) := (hfh n a).sub hf0
  have hid n a z : center (fh n a) z - center f0 z = center (d n a) z := by
    haveI := treatedLaw_isFiniteMeasure M L k z.1
    dsimp only [center, d]
    rw [integral_sub ((hmh n a z.1).integrable (by norm_num))
      ((hm0 z.1).integrable (by norm_num))]
    ring
  have hdm n a x := (hmh n a x).sub (hm0 x)
  have hi n a := (treatedLaw_integrated_centered_sq_le M L k (d n a)
    (hd n a) (hdm n a) (hfi n a)).1
  have hr := treatedLaw_centered_sq_tendsto_probability_zero M μ L k d hd hdm hfi hrf
  apply observationLaw_changing_selected_denominator_sq_tendsto_probability_zero
    M μ L k (center f0) (fun n a => center (fh n a)) p ph c (2 * B) (2 * D)
    hc (hcm f0 hf0) (fun n a => hcm _ (hfh n a)) hp hph hclip
    (treatedLaw_centered_abs_bound M L k f0 B hB hb0)
  · intro n a
    simpa only [hid] using treatedLaw_centered_abs_bound M L k (d n a) D hD (hbd n a)
  · exact heP
  · intro n a
    simpa only [hid] using hi n a
  · simpa only [hid] using hr
  · exact hrp

end Papers.TbsPrteOptimalTransport
