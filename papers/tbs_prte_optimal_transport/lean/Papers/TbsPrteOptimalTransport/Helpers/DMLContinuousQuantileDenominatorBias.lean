module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousRestoredBandBias
public import Papers.TbsPrteOptimalTransport.Helpers.WeightedQuantileBoundary
/-! Quadratic boundary bias with fitted assignment denominators.
The tower calculation produces the fitted gamma/pi ratio times the true
treatment and assignment probabilities. Clipping bounds this coefficient;
the boundary quarter rate then makes its debiased ramp remainder negligible. -/
public section
set_option linter.style.haveILetI false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: nuisanceRates_weighted_debiased_quantile_bias_root_n_negligible
/-- Suppose [the reference quantile is measurable](hyp:ht), [all fitted quantiles are
measurable](hyp:hf), [all weights are measurable](hyp:hw), [the weight bound is
nonnegative](hyp:hD), [weights are uniformly bounded in absolute value by it almost
surely](hyp:hwb), and [quantile errors are square integrable](hyp:he). If [the
neighborhood radius is positive](hyp:hr), [the density bound is nonnegative](hyp:hC),
[treated-outcome probabilities of intervals within that radius of the reference
quantile are at most the density bound times interval length almost surely](hyp:hdensity),
and [each fitted quantile has an L² error toward its reference value smaller in probability
than the inverse fourth root of sample size](hyp:hrates),
[the covariate mean of the weighted integrated lower-ramp error after subtracting its
linear term, multiplied by the square root of one plus the index, converges in
probability to zero along sample sizes twice one plus the index](goal). -/
lemma nuisanceRates_weighted_debiased_quantile_bias_root_n_negligible
    {A B : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (i : ℕ)
    (truth : B → X → ℝ) (fit : ℕ → A → B → X → ℝ)
    (w : ℕ → A → X → ℝ) (b : B) (D r C : ℝ)
    (ht : Measurable (truth b)) (hf : ∀ n a, Measurable (fit n a b))
    (hw : ∀ n a, Measurable (w n a)) (hD : 0 ≤ D)
    (hwb : ∀ n a, ∀ᵐ x ∂xLaw M, |w n a x| ≤ D)
    (he : ∀ n a, MemLp (fun x => fit n a b x - truth b x) 2 (xLaw M))
    (hr : 0 < r) (hC : 0 ≤ C)
    (hdensity : ∀ᵐ x ∂xLaw M, ∀ u v, truth b x - r ≤ u → u ≤ v →
      v ≤ truth b x + r → (treatedLaw M L i x (Ioc u v)).toReal ≤ C * (v-u))
    (hrates : FiniteNuisanceRates M μ fit truth) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        ∫ x, w (2*(n+1)) a x * (∫ y,
          (fit (2*(n+1)) a b x - y) * indicator (y ≤ fit (2*(n+1)) a b x) -
          (truth b x - y) * indicator (y ≤ truth b x) -
          (fit (2*(n+1)) a b x - truth b x) * indicator (y ≤ truth b x)
          ∂treatedLaw M L i x) ∂xLaw M) atTop (fun _ _ => 0) := by
  apply dml_root_n_bias_tendsto_probability
  let E := max 1 (D * (C + 1/r))
  have hE : 0 < E := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hs := dml_quarter_rate_product μ
    (fun n a => finiteL2Error M (fit (2*(n+1)) a b) (truth b))
    (fun n a => finiteL2Error M (fit (2*(n+1)) a b) (truth b))
    (hrates b) (hrates b)
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul hE hs
  intro n a
  have hb := (population_weighted_quantile_boundary_integrated_quadratic M L i
    (truth b) (fit (2*(n+1)) a b) (w (2*(n+1)) a)
    ht (hf _ a) (hw _ a) D hD (hwb _ a) (he _ a) r C hr hC hdensity).2
  have hsq : (∫ x, (fit (2*(n+1)) a b x - truth b x)^2 ∂xLaw M) =
      finiteL2Error M (fit (2*(n+1)) a b) (truth b)^2 := by
    simp only [finiteL2Error, Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)]
  rw [hsq] at hb
  calc
    _ ≤ D * (C + 1/r) * finiteL2Error M (fit (2*(n+1)) a b) (truth b)^2 := hb
    _ ≤ E * finiteL2Error M (fit (2*(n+1)) a b) (truth b)^2 :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
    _ = _ := by rw [← sq, abs_of_nonneg (sq_nonneg _)]

-- @node: continuous_fitted_boundary_assignment_weight_bound
/-- If [both nuisance records are admissible](hyp:he,hb), [the assignment denominator
floor is positive](hyp:hc), and [the first record's assignment probability exceeds
that floor almost surely](hyp:hclip), [the first record's regular effect coefficient
divided by its assignment probability, multiplied by the second record's level
probability and assignment probability, is measurable and has absolute value at most
the reciprocal floor almost surely](goal). -/
lemma continuous_fitted_boundary_assignment_weight_bound
    (L : LevelData Z X) (e b : NuisanceCont L)
    (he : ContAdmissible M L e) (hb : ContAdmissible M L b)
    (g : RegularIndex L) (i : PositiveIndex L.K) (c : ℝ) (hc : 0 < c)
    (hclip : ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) :
    Measurable (fun x => (e.gamma g x / e.piLev i x) *
      (b.pLev i x * b.piLev i x)) ∧
    (∀ᵐ x ∂xLaw M, |(e.gamma g x / e.piLev i x) *
      (b.pLev i x * b.piLev i x)| ≤ 1/c) := by
  rcases he with ⟨_, _, _, _, _, hpim, _, _, _, _, _, _, hgb, hgm, _⟩
  rcases hb with ⟨_, _, hpb, hpm, hpib, hpim0, _⟩
  refine ⟨by fun_prop, ?_⟩
  filter_upwards [hgb g, hpb i, hpib i, hclip] with x hg hp hpi hden
  have hpos : 0 < e.piLev i x := hc.trans_le hden
  have hprod : |b.pLev i x * b.piLev i x| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hp.1, abs_of_nonneg hpi.1]
    exact (mul_le_mul hp.2 hpi.2 hpi.1 zero_le_one).trans_eq (by norm_num)
  have hratio : |e.gamma g x / e.piLev i x| ≤ 1/c := by
    rw [abs_div, abs_of_nonneg hg.1, abs_of_pos hpos]
    exact div_le_div₀ zero_le_one hg.2 hc hden
  rw [abs_mul]
  exact (mul_le_mul hratio hprod (abs_nonneg _) (by positivity)).trans_eq (mul_one _)

-- @node: encoded_continuous_assignment_quantile_bias_root_n_negligible
/-- Assume [true nuisances are admissible](hyp:he0), [all fitted nuisances are
admissible](hyp:heh), [boundary densities are bounded](hyp:hd), and [encoded nuisance
L² errors are smaller in probability than the inverse fourth root of sample size](hyp:hrates).
If [the selected treatment level
is immediately above the boundary or equals its positive lower level](hyp:hi),
[the assignment denominator floor is positive](hyp:hc), and [all fitted assignment
probabilities at that level exceed the floor almost surely](hyp:hclip), [the mean
debiased quantile lower-ramp remainder, weighted by the fitted effect coefficient
divided by the fitted assignment probability and multiplied by the true level and
assignment probabilities, becomes negligible in probability after multiplication by
the square root of one plus the index, along sample sizes twice one plus the index](goal). -/
lemma encoded_continuous_assignment_quantile_bias_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A) (L : LevelData Z X)
    (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hd : BoundaryDensitiesBounded M L)
    (hrates : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (b : BoundaryIndex L) (g : RegularIndex L) (i : PositiveIndex L.K)
    (hi : i.val = b.val.1 + 1 ∨ (1 ≤ b.val.1 ∧ i.val = b.val.1))
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        ∫ x, ((eh (2*(n+1)) a).gamma g x / (eh (2*(n+1)) a).piLev i x) *
          ((trueNuisance M L).pLev i x * (trueNuisance M L).piLev i x) * (∫ y,
          ((eh (2*(n+1)) a).nu b x - y) * indicator (y ≤ (eh (2*(n+1)) a).nu b x) -
          ((trueNuisance M L).nu b x - y) * indicator (y ≤ (trueNuisance M L).nu b x) -
          ((eh (2*(n+1)) a).nu b x - (trueNuisance M L).nu b x) *
            indicator (y ≤ (trueNuisance M L).nu b x)
          ∂treatedLaw M L i.val x) ∂xLaw M) atTop (fun _ _ => 0) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  obtain ⟨r, C, hr, hC, hdensity⟩ := dml_quantile_boundary_density_constants M L hd
  obtain ⟨_, _, _, _, _, _, _, _, hrnu, _⟩ :=
    continuous_component_rates_to_oracle_rates M μ L eh (trueNuisance M L) hrates
  have hw n a := continuous_fitted_boundary_assignment_weight_bound
    M L (eh n a) (trueNuisance M L) (heh n a) he0 g i c hc (hclip n a)
  have ht : Measurable ((trueNuisance M L).nu b) := by
    first | fun_prop | skip
    rcases he0 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _⟩
    exact hm b
  have ht2 : MemLp ((trueNuisance M L).nu b) 2 (xLaw M) := by
    rcases he0 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hn, _⟩
    apply memLp_of_bounded (hn b)
    fun_prop
  have hf n a : Measurable ((eh n a).nu b) := by
    first | fun_prop | skip
    rcases heh n a with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _⟩
    exact hm b
  have hf2 n a : MemLp ((eh n a).nu b) 2 (xLaw M) := by
    rcases heh n a with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hn, _⟩
    apply memLp_of_bounded (hn b)
    fun_prop
  exact nuisanceRates_weighted_debiased_quantile_bias_root_n_negligible M μ L i.val
    (trueNuisance M L).nu (fun n a => (eh n a).nu)
    (fun n a x => ((eh n a).gamma g x / (eh n a).piLev i x) *
      ((trueNuisance M L).pLev i x * (trueNuisance M L).piLev i x))
    b (1/c) r C ht hf (fun n a => (hw n a).1) (by positivity)
    (fun n a => (hw n a).2) (fun n a => (hf2 n a).sub ht2)
    hr hC (hdensity b i.val hi) hrnu

-- @node: encoded_continuous_assignment_quantile_bias_block_root_n_negligible
/-- Assume [true nuisances are admissible](hyp:he0), [all fitted nuisances are
admissible](hyp:heh), [boundary densities are bounded](hyp:hd), and [encoded nuisance
L² errors are smaller in probability than the inverse fourth root of sample size](hyp:hrates).
If [every boundary, regular-index,
and treatment-level triple in the finite block uses the level immediately above its
boundary or its positive lower level](hyp:hi), [the assignment denominator floor is
positive](hyp:hc), and [all fitted assignment probabilities exceed that floor almost
surely](hyp:hclip), [the finite sum of mean debiased quantile lower-ramp remainders,
each weighted by its fitted effect-to-assignment ratio and true level and assignment
probabilities, multiplied by the square root of one plus the index, converges in
probability to zero along sample sizes twice one plus the index](goal). -/
lemma encoded_continuous_assignment_quantile_bias_block_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A) (L : LevelData Z X)
    (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hd : BoundaryDensitiesBounded M L)
    (hrates : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (t : Finset (BoundaryIndex L × RegularIndex L × PositiveIndex L.K))
    (hi : ∀ b ∈ t, b.2.2.val = b.1.val.1 + 1 ∨
      (1 ≤ b.1.val.1 ∧ b.2.2.val = b.1.val.1))
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) * ∑ b ∈ t,
        ∫ x, ((eh (2*(n+1)) a).gamma b.2.1 x / (eh (2*(n+1)) a).piLev b.2.2 x) *
          ((trueNuisance M L).pLev b.2.2 x * (trueNuisance M L).piLev b.2.2 x) * (∫ y,
          ((eh (2*(n+1)) a).nu b.1 x - y) * indicator (y ≤ (eh (2*(n+1)) a).nu b.1 x) -
          ((trueNuisance M L).nu b.1 x - y) * indicator (y ≤ (trueNuisance M L).nu b.1 x) -
          ((eh (2*(n+1)) a).nu b.1 x - (trueNuisance M L).nu b.1 x) *
            indicator (y ≤ (trueNuisance M L).nu b.1 x)
          ∂treatedLaw M L b.2.2.val x) ∂xLaw M) atTop (fun _ _ => 0) := by
  let F := fun (b : BoundaryIndex L × RegularIndex L × PositiveIndex L.K) n a =>
    Real.sqrt ((n+1 : ℕ) : ℝ) *
      ∫ x, ((eh (2*(n+1)) a).gamma b.2.1 x / (eh (2*(n+1)) a).piLev b.2.2 x) *
        ((trueNuisance M L).pLev b.2.2 x * (trueNuisance M L).piLev b.2.2 x) * (∫ y,
        ((eh (2*(n+1)) a).nu b.1 x - y) * indicator (y ≤ (eh (2*(n+1)) a).nu b.1 x) -
        ((trueNuisance M L).nu b.1 x - y) * indicator (y ≤ (trueNuisance M L).nu b.1 x) -
        ((eh (2*(n+1)) a).nu b.1 x - (trueNuisance M L).nu b.1 x) *
          indicator (y ≤ (trueNuisance M L).nu b.1 x)
        ∂treatedLaw M L b.2.2.val x) ∂xLaw M
  have hF b (hb : b ∈ t) : TendstoInMeasure μ (F b) atTop (fun _ => (0 : ℝ)) :=
    encoded_continuous_assignment_quantile_bias_root_n_negligible M μ L eh he0 heh hd
      hrates b.1 b.2.1 b.2.2 (hi b hb) c hc (fun n a => hclip n a b.2.2)
  have hs : TendstoInMeasure μ (fun n a => ∑ b ∈ t, F b n a)
      atTop (fun _ => (0 : ℝ)) := by
    induction t using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      intro eps heps
      simpa only [edist_self, not_le.mpr heps, Set.ofPred_false, measure_empty]
        using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
    | @insert b t hb ih =>
      have hsingle := hF b (Finset.mem_insert_self b t)
      have hrest := ih (fun d hd => hi d (Finset.mem_insert_of_mem hd))
        (fun d hd => hF d (Finset.mem_insert_of_mem hd))
      simpa only [Finset.sum_insert hb] using hsingle.add_zero hrest
  change TendstoInMeasure μ _ atTop (fun _ => (0 : ℝ))
  simpa only [F, Finset.mul_sum] using hs

end Papers.TbsPrteOptimalTransport
