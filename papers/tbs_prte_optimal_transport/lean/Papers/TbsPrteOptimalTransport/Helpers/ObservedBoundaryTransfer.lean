module
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousBandBoundaryMean
/-! Transfer of selected outcome boundary remainders to observation-level scores. -/
@[expose] public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

-- The normalization identity includes cells of zero mass.
-- @node: selected_treatment_integral_eq_mass_mul_mean
/-- If [the selected instrument set is measurable](hyp:hD), [the outcome function is
measurable](hyp:hg), and [treatment is binary almost everywhere](hyp:hW), [the integral of
the selected treated outcome function divided by a constant equals the selected treated
mass divided by that constant times the outcome mean under the normalized selected law](goal).

The identity also includes cells with zero mass. -/
lemma selected_treatment_integral_eq_mass_mul_mean {Z : Type*} [MeasurableSpace Z]
    (ν : Measure (ℝ × ℝ × Z)) [IsFiniteMeasure ν]
    (D : Set Z) (hD : MeasurableSet D) (g : ℝ → ℝ) (hg : Measurable g)
    (hW : ∀ᵐ a ∂ν, a.2.1 = 0 ∨ a.2.1 = 1) (c : ℝ) :
    (∫ a : ℝ × ℝ × Z, indicator (a.2.2 ∈ D) * a.2.1 / c * g a.1 ∂ν) =
      ((ν {a : ℝ × ℝ × Z | a.2.1 = 1 ∧ a.2.2 ∈ D}).toReal / c) *
        (∫ y, g y ∂((ν.restrict {a | a.2.1 = 1 ∧ a.2.2 ∈ D}) univ)⁻¹ •
          (ν.restrict {a | a.2.1 = 1 ∧ a.2.2 ∈ D}).map Prod.fst) := by
  let E : Set (ℝ × ℝ × Z) := {a | a.2.1 = 1 ∧ a.2.2 ∈ D}
  have hE : MeasurableSet E :=
    (measurableSet_eq_fun measurable_snd.fst measurable_const).inter
      (hD.preimage measurable_snd.snd)
  have hid : (fun a : ℝ × ℝ × Z => indicator (a.2.2 ∈ D) * a.2.1 / c * g a.1) =ᵐ[ν]
      (fun a => c⁻¹ * E.indicator (fun a => g a.1) a) := by
    filter_upwards [hW] with a ha
    rcases ha with ha | ha <;> by_cases hz : a.2.2 ∈ D <;>
      simp [ha, hz, E, indicator, Set.indicator, div_eq_mul_inv]
  rw [integral_congr_ae hid, integral_const_mul, integral_indicator hE,
    normalized_selected_mean_eq_average ν D g hg]
  have hm := measure_smul_average (μ := ν.restrict E) (fun a => g a.1)
  simp only [smul_eq_mul, Measure.real, Measure.restrict_apply_univ] at hm
  change c⁻¹ * (∫ a in E, g a.1 ∂ν) = (ν E).toReal / c * ⨍ a in E, g a.1 ∂ν
  rw [← hm]
  ring

-- @node: debiased_quantile_boundary_norm_le
/-- [The absolute size of the quantile hinge remainder after subtracting its linear
correction at the original threshold is bounded by the absolute threshold displacement](goal). -/
lemma debiased_quantile_boundary_norm_le (a b y : ℝ) :
    ‖(b - y) * indicator (y ≤ b) - (a - y) * indicator (y ≤ a) -
      (b - a) * indicator (y ≤ a)‖ ≤ |b - a| := by
  rw [debiased_quantile_boundary_pointwise, norm_mul, Real.norm_eq_abs]
  have hs : |(if a ≤ b then 1 else -1 : ℝ)| = 1 := by
    split_ifs <;> norm_num
  rw [hs, one_mul]
  by_cases hy : y ∈ Ioc (min a b) (max a b)
  · rw [Set.indicator_of_mem hy, Real.norm_eq_abs]
    by_cases hab : a ≤ b
    · simp only [min_eq_left hab, max_eq_right hab, mem_Ioc] at hy
      rw [abs_of_nonneg (by linarith : 0 ≤ b - y),
        abs_of_nonneg (sub_nonneg.mpr hab)]
      linarith [hy.1, hy.2]
    · have hba : b ≤ a := le_of_not_ge hab
      simp only [min_eq_right hba, max_eq_left hba, mem_Ioc] at hy
      rw [abs_of_nonpos (by linarith : b - y ≤ 0),
        abs_of_nonpos (sub_nonpos.mpr hba)]
      linarith [hy.1, hy.2]
  · rw [Set.indicator_of_notMem hy, norm_zero]
    exact abs_nonneg _

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: selectedTreatmentMass
/-- For [a latent instrumental-variable model](hyp:M), [a level structure](hyp:L),
[a baseline level index](hyp:i), and [a covariate value](hyp:x), [the selected treatment
mass](goal) is the conditional probability of being treated and having an instrument in
that baseline level, given those covariates. -/
noncomputable def selectedTreatmentMass (L : LevelData Z X) (i : ℕ) (x : X) : ℝ :=
  (condDistrib (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure x
    {a : ℝ × ℝ × Z | a.2.1 = 1 ∧ a.2.2 ∈ (L.S i : Set Z)}).toReal

-- @node: selectedTreatmentMass_measurable
/-- [The conditional probability of treatment and instrument membership in a given baseline
level is measurable as a function of covariates](goal). -/
@[fun_prop] lemma selectedTreatmentMass_measurable (L : LevelData Z X) (i : ℕ) :
    Measurable (selectedTreatmentMass M L i) := by
  first | fun_prop | skip
  unfold selectedTreatmentMass
  exact (Kernel.measurable_coe _
    ((measurableSet_eq_fun measurable_snd.fst measurable_const).inter
      ((L.S i).finite_toSet.measurableSet.preimage measurable_snd.snd))).ennreal_toReal

-- @node: selectedTreatmentMass_range
/-- [At every covariate value, the selected treatment mass for any baseline level lies
between zero and one, inclusive](goal). -/
lemma selectedTreatmentMass_range (L : LevelData Z X) (i : ℕ) (x : X) :
    selectedTreatmentMass M L i x ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact ENNReal.toReal_nonneg
  · exact (measureReal_mono (subset_univ _)).trans_eq (by simp)

-- Conditioning on X leaves the actual selected mass, rather than an
-- unweighted assignment probability. This is the coefficient of the
-- nonlinear outcome boundary remainder in the paper's score expansion.
-- @node: population_selected_treatment_integral_transfer
/-- If [the covariate-dependent outcome function is jointly measurable](hyp:hg),
[the weight](hyp:hw) and [the denominator](hyp:hc) are measurable, and [the weighted selected
treatment term is integrable under the observation law](hyp:hi), [its population integral
equals the covariate integral of the weight times the selected treatment mass divided by
the denominator times the conditional selected treated outcome mean](goal). -/
lemma population_selected_treatment_integral_transfer
    (L : LevelData Z X) (i : ℕ) (g : X → ℝ → ℝ)
    (hg : Measurable (Function.uncurry g)) (w c : X → ℝ)
    (hw : Measurable w) (hc : Measurable c)
    (hi : Integrable (fun o : Obs X Z => w o.1 *
      (indicator (o.2.1 ∈ L.S i) * o.2.2.1 / c o.1 * g o.1 o.2.2.2))
      (observationLaw M)) :
    (∫ o : Obs X Z, w o.1 *
      (indicator (o.2.1 ∈ L.S i) * o.2.2.1 / c o.1 * g o.1 o.2.2.2)
      ∂observationLaw M) =
    ∫ x, (w x * (selectedTreatmentMass M L i x / c x)) *
      (∫ y, g x y ∂treatedLaw M L i x) ∂xLaw M := by
  let f : Obs X Z → ℝ := fun o => w o.1 *
    (indicator (o.2.1 ∈ L.S i) * o.2.2.1 / c o.1 * g o.1 o.2.2.2)
  have hf : Measurable f := by
    dsimp only [f]
    fun_prop
  have hobs := M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
  have hi' : Integrable (fun s => f (M.Xv s, M.Zv s, M.W s, M.Y s)) M.law.toMeasure :=
    (integrable_map_measure hf.aestronglyMeasurable hobs.aemeasurable).mp hi
  have hjoint := M.measY.prodMk (M.measW.prodMk M.measZ)
  have hpair : StronglyMeasurable (fun p : X × (ℝ × ℝ × Z) =>
      f (p.1, p.2.2.2, p.2.2.1, p.2.1)) := by
    fun_prop
  have ht := condExp_prod_ae_eq_integral_condDistrib M.measX hjoint.aemeasurable hpair hi'
  have hW := ae_of_ae_map M.measX.aemeasurable (population_joint_treatment_binary M)
  have heq : M.law.toMeasure[(fun s => f (M.Xv s, M.Zv s, M.W s, M.Y s)) |
      MeasurableSpace.comap M.Xv inferInstance] =ᵐ[M.law.toMeasure]
      (fun s => (w (M.Xv s) * (selectedTreatmentMass M L i (M.Xv s) / c (M.Xv s))) *
        (∫ y, g (M.Xv s) y ∂treatedLaw M L i (M.Xv s))) := by
    filter_upwards [ht, hW] with s hs hsW
    rw [hs]
    dsimp only [f]
    rw [integral_const_mul]
    have hsel := selected_treatment_integral_eq_mass_mul_mean _
      (L.S i : Set Z) (L.S i).finite_toSet.measurableSet (g (M.Xv s))
      hg.of_uncurry_left hsW (c (M.Xv s))
    simp only [Finset.mem_coe] at hsel
    rw [hsel]
    change w _ * (selectedTreatmentMass M L i _ / c _ *
      (∫ y, g (M.Xv s) y ∂treatedLaw M L i (M.Xv s))) = _
    ring
  have hm : Measurable (fun x => (w x * (selectedTreatmentMass M L i x / c x)) *
      (∫ y, g x y ∂treatedLaw M L i x)) := by
    fun_prop
  change (∫ o, f o ∂observationLaw M) = _
  rw [observationLaw, integral_map hobs.aemeasurable hf.aestronglyMeasurable,
    ← integral_condExp M.measX.comap_le, integral_congr_ae heq,
    xLaw, integral_map M.measX.aemeasurable hm.aestronglyMeasurable]

-- An integrable covariate envelope suffices for the raw selected term.
-- In particular, an L2 quantile direction supplies this envelope for every t.
-- @node: population_selected_integrand_integrable_of_envelope
/-- Suppose [the outcome function is jointly measurable](hyp:hg), [its envelope is
measurable](hyp:hH) and [integrable under the covariate law](hyp:hHi), and [the envelope
bounds its absolute value uniformly over outcomes for almost every covariate](hyp:hb).
If [the weight](hyp:hw) and [denominator](hyp:hc) are measurable, [the weight bound is
nonnegative](hyp:hB), [the denominator bound is positive](hyp:hc0), [the weight is almost
everywhere bounded in absolute value by the former](hyp:hwb), and [the denominator is
almost everywhere at least the latter](hyp:hcl), [the weighted selected treatment outcome
term is integrable under the observation law](goal). -/
lemma population_selected_integrand_integrable_of_envelope
    (L : LevelData Z X) (i : ℕ) (g : X → ℝ → ℝ)
    (hg : Measurable (Function.uncurry g)) (H : X → ℝ)
    (hH : Measurable H) (hHi : Integrable H (xLaw M))
    (hb : ∀ᵐ x ∂xLaw M, ∀ y, ‖g x y‖ ≤ H x)
    (w c : X → ℝ) (hw : Measurable w) (hc : Measurable c)
    (B c0 : ℝ) (hB : 0 ≤ B) (hc0 : 0 < c0)
    (hwb : ∀ᵐ x ∂xLaw M, |w x| ≤ B)
    (hcl : ∀ᵐ x ∂xLaw M, c0 ≤ c x) :
    Integrable (fun o : Obs X Z => w o.1 *
      (indicator (o.2.1 ∈ L.S i) * o.2.2.1 / c o.1 * g o.1 o.2.2.2))
      (observationLaw M) := by
  have hobs := M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
  have hmap : (observationLaw M).map Prod.fst = xLaw M := by
    simpa only [observationLaw, xLaw, Function.comp_def] using Measure.map_map measurable_fst hobs
  have hHi' : Integrable (fun o : Obs X Z => H o.1) (observationLaw M) := by
    apply (integrable_map_measure hH.aestronglyMeasurable measurable_fst.aemeasurable).mp
    rwa [hmap]
  have ht : ∀ᵐ o : Obs X Z ∂observationLaw M, ‖o.2.2.1‖ ≤ 1 := by
    apply (ae_map_iff hobs.aemeasurable
      (measurableSet_le (by fun_prop) measurable_const)).mpr
    exact Eventually.of_forall (fun s => by rcases M.rangeW s with hs | hs <;> simp [hs])
  have hm : Measurable (fun o : Obs X Z => w o.1 *
      (indicator (o.2.1 ∈ L.S i) * o.2.2.1 / c o.1 * g o.1 o.2.2.2)) := by
    fun_prop
  apply (hHi'.norm.const_mul (B / c0)).mono' hm.aestronglyMeasurable
  filter_upwards [ht, observationLaw_covariate_ae M _ hb,
    observationLaw_covariate_ae M _ hwb, observationLaw_covariate_ae M _ hcl]
    with o hto hgo hwo hco
  have hi : ‖indicator (o.2.1 ∈ L.S i)‖ ≤ 1 := by
    unfold indicator
    split_ifs <;> norm_num
  have hcpos : 0 < c o.1 := hc0.trans_le hco
  have hgH : ‖g o.1 o.2.2.2‖ ≤ ‖H o.1‖ :=
    (hgo _).trans (by simpa only [Real.norm_eq_abs] using le_abs_self (H o.1))
  rw [norm_mul, norm_mul, norm_div, norm_mul, Real.norm_eq_abs (c o.1), abs_of_pos hcpos]
  calc
    _ ≤ B * ((1 * 1) / c0 * ‖H o.1‖) := by
      rw [Real.norm_eq_abs (w o.1)]
      gcongr
    _ = (B / c0) * ‖H o.1‖ := by ring

-- The tower identity and the density-based quadratic estimate now act on
-- the same observation-level remainder used by IFJ/IFM, with gamma and pi
-- allowed to move jointly. Integrability is derived from the L2 direction.
-- @node: population_observed_quantile_boundary_local_path_orthogonality
/-- Suppose [the baseline threshold](hyp:ha) and [its perturbation direction](hyp:hd) are
measurable, [the direction is square-integrable](hyp:hd2), [the weight bound is nonnegative](hyp:hB),
[the denominator bound is positive](hyp:hc0), [the neighborhood radius is positive](hyp:hr),
and [the density bound is nonnegative](hyp:hC). If [locally along the path the weight and
denominator are measurable, the weight is bounded in absolute value, and the denominator
has that positive lower bound](hyp:hlocal), and [the selected treated outcome law assigns
each interval near the threshold at most the density bound times its length](hyp:hden),
[the population weighted selected treatment quantile remainder along the linear threshold
path has derivative zero at zero](goal). -/
lemma population_observed_quantile_boundary_local_path_orthogonality
    (L : LevelData Z X) (i : ℕ) (a d : X → ℝ)
    (ha : Measurable a) (hd : Measurable d) (hd2 : MemLp d 2 (xLaw M))
    (w c : ℝ → X → ℝ) (B c0 r C : ℝ)
    (hB : 0 ≤ B) (hc0 : 0 < c0) (hr : 0 < r) (hC : 0 ≤ C)
    (hlocal : ∀ᶠ t : ℝ in 𝓝 0, Measurable (w t) ∧ Measurable (c t) ∧
      (∀ᵐ x ∂xLaw M, |w t x| ≤ B) ∧ (∀ᵐ x ∂xLaw M, c0 ≤ c t x))
    (hden : ∀ᵐ x ∂xLaw M, ∀ u v, a x - r ≤ u → u ≤ v → v ≤ a x + r →
      (treatedLaw M L i x (Ioc u v)).toReal ≤ C * (v - u)) :
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z, w t o.1 *
      (indicator (o.2.1 ∈ L.S i) * o.2.2.1 / c t o.1 *
        ((a o.1 + t * d o.1 - o.2.2.2) * indicator (o.2.2.2 ≤ a o.1 + t * d o.1) -
          (a o.1 - o.2.2.2) * indicator (o.2.2.2 ≤ a o.1) -
          (t * d o.1) * indicator (o.2.2.2 ≤ a o.1))) ∂observationLaw M) 0 0 := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  have hdi : Integrable d (xLaw M) := hd2.integrable (by norm_num)
  let v : ℝ → X → ℝ := fun t x => w t x * (selectedTreatmentMass M L i x / c t x)
  have hv : ∀ᶠ t : ℝ in 𝓝 0, Measurable (v t) ∧
      ∀ᵐ x ∂xLaw M, |v t x| ≤ B / c0 := by
    filter_upwards [hlocal] with t ht
    have hwm := ht.1
    have hcm := ht.2.1
    refine ⟨by dsimp only [v]; fun_prop, ?_⟩
    filter_upwards [ht.2.2.1, ht.2.2.2] with x hwx hcx
    have hmass := selectedTreatmentMass_range M L i x
    have hcp : 0 < c t x := hc0.trans_le hcx
    simp only [v, abs_mul, abs_div, abs_of_nonneg hmass.1, abs_of_pos hcp]
    calc
      _ ≤ B * (1 / c0) := mul_le_mul hwx
        (div_le_div₀ zero_le_one hmass.2 hc0 hcx) (div_nonneg hmass.1 hcp.le) hB
      _ = B / c0 := by ring
  have hz := population_weighted_quantile_boundary_local_path_orthogonality M L i a d v
    ha hd hd2 (B / c0) (by positivity) hv r C hr hC hden
  apply hz.congr_of_eventuallyEq
  filter_upwards [hlocal] with t ht
  let g : X → ℝ → ℝ := fun x y =>
    (a x + t * d x - y) * indicator (y ≤ a x + t * d x) -
      (a x - y) * indicator (y ≤ a x) - (t * d x) * indicator (y ≤ a x)
  have hg : Measurable (Function.uncurry g) := by dsimp only [g]; fun_prop
  have hgb : ∀ᵐ x ∂xLaw M, ∀ y, ‖g x y‖ ≤ |t| * |d x| := by
    exact Eventually.of_forall fun x y => by
      simpa only [g, add_sub_cancel_left, abs_mul] using
        debiased_quantile_boundary_norm_le (a x) (a x + t * d x) y
  have hi := population_selected_integrand_integrable_of_envelope M L i g hg
    (fun x => |t| * |d x|) (by fun_prop) (hdi.abs.const_mul |t|) hgb
    (w t) (c t) ht.1 ht.2.1 B c0 hB hc0 ht.2.2.1 ht.2.2.2
  exact (population_selected_treatment_integral_transfer M L i g hg
    (w t) (c t) ht.1 ht.2.1 hi)

-- Every hypothesis on the varying weight and denominator is now supplied
-- by the original admissible direction and population overlap. The density
-- assumption is used only at an estimated interior threshold.
-- @node: population_continuous_observed_boundary_orthogonality
/-- Suppose [outcome densities near band boundaries are bounded](hyp:h), [baseline
assignment probabilities satisfy the overlap bound](hyp:hov), and [the continuous nuisance
direction is admissible at the truth](hyp:hd). If [the selected positive baseline level is
adjacent to the boundary's level](hyp:hi) and [the baseline band boundary is measurable](hyp:ha),
[the population selected treatment quantile remainder, weighted by the moving score weight
and divided by the moving assignment probability along that direction, has derivative zero
at zero](goal). -/
lemma population_continuous_observed_boundary_orthogonality
    (L : LevelData Z X) (h : BoundaryDensitiesBounded M L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (a : BoundaryIndex L) (g : RegularIndex L) (b : PositiveIndex L.K)
    (hi : b.val = a.val.1 + 1 ∨ (1 ≤ a.val.1 ∧ b.val = a.val.1))
    (ha : Measurable (bandBoundary M L a.val.1 a.val.2)) :
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
      (trueNuisance M L + t • del).gamma g o.1 *
      (indicator (o.2.1 ∈ L.S b.val) * o.2.2.1 /
        (trueNuisance M L + t • del).piLev b o.1 *
        ((bandBoundary M L a.val.1 a.val.2 o.1 + t * del.nu a o.1 - o.2.2.2) *
            indicator (o.2.2.2 ≤ bandBoundary M L a.val.1 a.val.2 o.1 + t * del.nu a o.1) -
          (bandBoundary M L a.val.1 a.val.2 o.1 - o.2.2.2) *
            indicator (o.2.2.2 ≤ bandBoundary M L a.val.1 a.val.2 o.1) -
          (t * del.nu a o.1) * indicator (o.2.2.2 ≤ bandBoundary M L a.val.1 a.val.2 o.1)))
      ∂observationLaw M) 0 0 := by
  have hcpi : 0 < cpi := hov.1
  obtain ⟨r, C, hr, hden⟩ := h
  obtain ⟨_, _, hdir⟩ := continuous_quantile_direction_regular M L _ del hd
  apply population_observed_quantile_boundary_local_path_orthogonality M L b.val
    (bandBoundary M L a.val.1 a.val.2) (del.nu a) ha (hdir a).1
    (continuous_quantile_direction_memLp M L _ del hd a) _ _
    1 (cpi / 2) r |C| zero_le_one (by positivity) hr (abs_nonneg C)
  · obtain ⟨s, hs, hpath⟩ := hd.admissible
    filter_upwards [continuous_assignment_path_uniform_lower_bound M L cpi hov del hd,
      continuousAt_id.abs.eventually_lt_const (by simpa using hs)] with t ht hst
    have had := hpath t hst
    rcases had with ⟨_, _, _, _, _, hpim, _, _, _, _, _, _, hgb, hgm, _⟩
    refine ⟨hgm g, hpim b, ?_, ht b⟩
    filter_upwards [hgb g] with x hx
    simpa only [abs_of_nonneg hx.1] using hx.2
  · filter_upwards [hden a.val.1 a.property.1 a.val.2 a.property.2.1 a.property.2.2 b.val hi]
      with x hx
    intro u v hu huv hv
    exact (hx u v hu huv hv).trans
      (mul_le_mul_of_nonneg_right (le_abs_self C) (sub_nonneg.mpr huv))

end Papers.TbsPrteOptimalTransport
