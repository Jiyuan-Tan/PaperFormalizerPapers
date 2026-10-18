module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousEncodedBand
/-! Outcome-weighted moving bands inherit indicator energy convergence.
Clipped endpoints bound the outcome wherever either band is nonzero, so the
argument also applies to off-support fibers of the treated conditional law. -/
public section
set_option linter.unusedFintypeInType false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

-- @node: outcome_weighted_band_sq_bound
/-- If [the original lower endpoint](hyp:ha), [the original upper endpoint](hyp:hb), [the alternative lower endpoint](hyp:ha'), and [the alternative upper endpoint](hyp:hb') all have absolute value at most a common bound, then [the squared difference of the two weighted interval indicators after multiplication by the outcome is at most the bound squared times the squared indicator difference](goal). -/
lemma outcome_weighted_band_sq_bound (a b a' b' w w' y B : ℝ)
    (ha : |a| ≤ B) (hb : |b| ≤ B) (ha' : |a'| ≤ B) (hb' : |b'| ≤ B) :
    (y * (w' * indicator (a' < y ∧ y ≤ b') - w * indicator (a < y ∧ y ≤ b))) ^ 2 ≤
      B ^ 2 * (w' * indicator (a' < y ∧ y ≤ b') - w * indicator (a < y ∧ y ≤ b)) ^ 2 := by
  by_cases h : (a' < y ∧ y ≤ b') ∨ (a < y ∧ y ≤ b)
  · have hy : |y| ≤ B := by
      apply abs_le.mpr
      rcases h with h | h
      · exact ⟨(abs_le.mp ha').1.trans h.1.le, h.2.trans (abs_le.mp hb').2⟩
      · exact ⟨(abs_le.mp ha).1.trans h.1.le, h.2.trans (abs_le.mp hb).2⟩
    have hs : y ^ 2 ≤ B ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg y) hy 2
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hs (sq_nonneg _)
  · have h' := not_or.mp h
    simp only [indicator, if_neg h'.1, if_neg h'.2, mul_zero, sub_self,
      zero_pow (by norm_num : 2 ≠ 0), le_refl]

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: treatedLaw_outcome_band_energy_bound
/-- Suppose [the original endpoints are measurable](hyp:ha,hb), [the alternative endpoints are measurable](hyp:ha',hb'), [both weights are measurable](hyp:hw,hw'), and [all four endpoints are almost everywhere bounded in absolute value by a common constant](hyp:hbound). If [the conditional squared difference of the weighted interval indicators is integrable over covariates](hyp:hi), then [the conditional squared difference after outcome multiplication is also integrable over covariates, and its overall integral is at most the common bound squared times the original overall squared-difference integral](goal). -/
lemma treatedLaw_outcome_band_energy_bound
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (k : ℕ)
    (a b a' b' w w' : X → ℝ) (B : ℝ)
    (ha : Measurable a) (hb : Measurable b)
    (ha' : Measurable a') (hb' : Measurable b')
    (hw : Measurable w) (hw' : Measurable w')
    (hbound : ∀ᵐ x ∂xLaw M,
      |a x| ≤ B ∧ |b x| ≤ B ∧ |a' x| ≤ B ∧ |b' x| ≤ B)
    (hi : Integrable (fun x => ∫ y,
      (w' x * indicator (a' x < y ∧ y ≤ b' x) -
        w x * indicator (a x < y ∧ y ≤ b x)) ^ 2 ∂treatedLaw M L k x) (xLaw M)) :
    Integrable (fun x => ∫ y,
      (y * (w' x * indicator (a' x < y ∧ y ≤ b' x) -
        w x * indicator (a x < y ∧ y ≤ b x))) ^ 2 ∂treatedLaw M L k x) (xLaw M) ∧
    (∫ x, ∫ y, (y * (w' x * indicator (a' x < y ∧ y ≤ b' x) -
      w x * indicator (a x < y ∧ y ≤ b x))) ^ 2 ∂treatedLaw M L k x ∂xLaw M) ≤
      B ^ 2 * (∫ x, ∫ y, (w' x * indicator (a' x < y ∧ y ≤ b' x) -
        w x * indicator (a x < y ∧ y ≤ b x)) ^ 2 ∂treatedLaw M L k x ∂xLaw M) := by
  let d : X × ℝ → ℝ := fun p => w' p.1 * indicator (a' p.1 < p.2 ∧ p.2 ≤ b' p.1) -
    w p.1 * indicator (a p.1 < p.2 ∧ p.2 ≤ b p.1)
  have hd : Measurable d := by fun_prop
  have hmem x : MemLp (fun y => d (x, y)) 2 (treatedLaw M L k x) := by
    let := treatedLaw_isFiniteMeasure M L k x
    apply MemLp.of_bound (by
      first
      | fun_prop
      | exact (hd.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      (|w' x| + |w x|)
    apply Eventually.of_forall
    intro y
    dsimp only [d]
    unfold indicator
    split_ifs <;> simp only [mul_one, mul_zero, sub_zero, zero_sub, Real.norm_eq_abs,
      abs_neg, abs_zero] <;> first
      | exact abs_sub _ _
      | linarith [abs_nonneg (w x), abs_nonneg (w' x)]
  have hbnd : ∀ᵐ x ∂xLaw M,
      (∫ y, (y * d (x, y)) ^ 2 ∂treatedLaw M L k x) ≤
        B ^ 2 * ∫ y, d (x, y) ^ 2 ∂treatedLaw M L k x := by
    filter_upwards [hbound] with x hx
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg (Eventually.of_forall fun y => sq_nonneg _)
      ((hmem x).integrable_sq.const_mul (B ^ 2))
    exact Eventually.of_forall fun y =>
      outcome_weighted_band_sq_bound _ _ _ _ _ _ _ _ hx.1 hx.2.1 hx.2.2.1 hx.2.2.2
  have hm : Measurable (fun x => ∫ y, (y * d (x, y)) ^ 2 ∂treatedLaw M L k x) := by
    apply measurable_treatedLaw_integral_prod M L k (fun p => (p.2 * d p) ^ 2)
    fun_prop
  have hi' := (hi.const_mul (B ^ 2)).mono' hm.aestronglyMeasurable (by
    filter_upwards [hbnd] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg
      (integral_nonneg fun y => sq_nonneg (y * d (x, y)))]
    exact hx)
  refine ⟨hi', ?_⟩
  calc
    _ ≤ ∫ x, B ^ 2 * ∫ y, d (x, y) ^ 2 ∂treatedLaw M L k x ∂xLaw M :=
      integral_mono_ae hi' (hi.const_mul _) hbnd
    _ = _ := integral_const_mul _ _

-- @node: treatedLaw_outcome_band_sq_tendsto_probability_zero
/-- Suppose [the fixed interval endpoints are measurable](hyp:ha,hb), [the original weights are measurable](hyp:hw), [all fitted lower endpoints are measurable](hyp:hah), [all fitted upper endpoints are measurable](hyp:hbh), [all fitted weights are measurable](hyp:hwh), and [all fixed and fitted endpoints share an almost everywhere absolute bound](hyp:hbound). If [each conditional squared weighted-indicator difference is integrable over covariates](hyp:hi) and [its overall integral converges in probability to zero](hyp:hr), then [the overall squared difference after multiplying by the outcome also converges in probability to zero](goal). -/
lemma treatedLaw_outcome_band_sq_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X) (k : ℕ)
    (a b : X → ℝ) (ah bh w wh : ℕ → A → X → ℝ) (B : ℝ)
    (ha : Measurable a) (hb : Measurable b) (hw : ∀ n s, Measurable (w n s))
    (hah : ∀ n s, Measurable (ah n s)) (hbh : ∀ n s, Measurable (bh n s))
    (hwh : ∀ n s, Measurable (wh n s))
    (hbound : ∀ n s, ∀ᵐ x ∂xLaw M,
      |a x| ≤ B ∧ |b x| ≤ B ∧ |ah n s x| ≤ B ∧ |bh n s x| ≤ B)
    (hi : ∀ n s, Integrable (fun x => ∫ y,
      (wh n s x * indicator (ah n s x < y ∧ y ≤ bh n s x) -
        w n s x * indicator (a x < y ∧ y ≤ b x)) ^ 2 ∂treatedLaw M L k x) (xLaw M))
    (hr : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n s => ∫ x, ∫ y,
        (wh n s x * indicator (ah n s x < y ∧ y ≤ bh n s x) -
          w n s x * indicator (a x < y ∧ y ≤ b x)) ^ 2 ∂treatedLaw M L k x ∂xLaw M)
      atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n s => ∫ x, ∫ y,
        (y * (wh n s x * indicator (ah n s x < y ∧ y ≤ bh n s x) -
          w n s x * indicator (a x < y ∧ y ≤ b x))) ^ 2 ∂treatedLaw M L k x ∂xLaw M)
      atTop (fun _ _ => 0) := by
  have ht := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    (show Continuous (fun t : ℝ => B ^ 2 * t) by fun_prop).continuousAt hr
  simp only [mul_zero] at ht
  apply probability_zero_of_nonneg_le μ _ _ ht
  intro n
  apply Eventually.of_forall
  intro s
  exact ⟨integral_nonneg fun x => integral_nonneg fun y => sq_nonneg _,
    (treatedLaw_outcome_band_energy_bound M L k a b (ah n s) (bh n s) (w n s) (wh n s) B
      ha hb (hah n s) (hbh n s) (hw n s) (hwh n s) (hbound n s) (hi n s)).2⟩

-- @node: outcome_band_memLp
/-- [An outcome multiplied by a constant weight and the indicator of a finite interval is square-integrable under any finite measure on the real line](goal). -/
lemma outcome_band_memLp (ν : Measure ℝ) [IsFiniteMeasure ν] (a b w : ℝ) :
    MemLp (fun y => y * (w * indicator (a < y ∧ y ≤ b))) 2 ν := by
  have hm : Measurable (fun y => y * (w * indicator (a < y ∧ y ≤ b))) := by
    fun_prop
  apply MemLp.of_bound hm.aestronglyMeasurable ((|a| + |b|) * |w|)
  apply Eventually.of_forall
  intro y
  by_cases h : a < y ∧ y ≤ b
  · have hy : |y| ≤ |a| + |b| := by
      apply abs_le.mpr
      constructor
      · linarith [neg_abs_le a, abs_nonneg b]
      · linarith [le_abs_self b, abs_nonneg a]
    simp only [indicator, if_pos h, mul_one, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hy (abs_nonneg w)
  · simp only [indicator, if_neg h, mul_zero, norm_zero]
    positivity

-- @node: treatedLaw_centered_outcome_band_sq_tendsto_probability_zero
/-- Suppose [the fixed interval endpoints are measurable](hyp:ha,hb), [the original weights are measurable](hyp:hw), [the fitted lower endpoints are measurable](hyp:hah), [the fitted upper endpoints are measurable](hyp:hbh), [the fitted weights are measurable](hyp:hwh), and [all fixed and fitted endpoints have a common almost everywhere absolute bound](hyp:hbound). If [the conditional squared weighted-indicator differences are integrable over covariates](hyp:hi) and [their overall integrals converge in probability to zero](hyp:hr), then [the integrated square of the outcome-weighted difference, centered by its conditional treated-law integral at each covariate value, converges in probability to zero](goal). -/
lemma treatedLaw_centered_outcome_band_sq_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X) (k : ℕ)
    (a b : X → ℝ) (ah bh w wh : ℕ → A → X → ℝ) (B : ℝ)
    (ha : Measurable a) (hb : Measurable b) (hw : ∀ n s, Measurable (w n s))
    (hah : ∀ n s, Measurable (ah n s)) (hbh : ∀ n s, Measurable (bh n s))
    (hwh : ∀ n s, Measurable (wh n s))
    (hbound : ∀ n s, ∀ᵐ x ∂xLaw M,
      |a x| ≤ B ∧ |b x| ≤ B ∧ |ah n s x| ≤ B ∧ |bh n s x| ≤ B)
    (hi : ∀ n s, Integrable (fun x => ∫ y,
      (wh n s x * indicator (ah n s x < y ∧ y ≤ bh n s x) -
        w n s x * indicator (a x < y ∧ y ≤ b x)) ^ 2 ∂treatedLaw M L k x) (xLaw M))
    (hr : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n s => ∫ x, ∫ y,
        (wh n s x * indicator (ah n s x < y ∧ y ≤ bh n s x) -
          w n s x * indicator (a x < y ∧ y ≤ b x)) ^ 2 ∂treatedLaw M L k x ∂xLaw M)
      atTop (fun _ _ => 0)) :
    let d : ℕ → A → X × ℝ → ℝ := fun n s p => p.2 *
      (wh n s p.1 * indicator (ah n s p.1 < p.2 ∧ p.2 ≤ bh n s p.1) -
        w n s p.1 * indicator (a p.1 < p.2 ∧ p.2 ≤ b p.1))
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n s => ∫ x, ∫ y, (d n s (x, y) -
        ∫ z, d n s (x, z) ∂treatedLaw M L k x) ^ 2
        ∂treatedLaw M L k x ∂xLaw M) atTop (fun _ _ => 0) := by
  dsimp only
  apply treatedLaw_centered_sq_tendsto_probability_zero M μ L k
    (fun n s p => p.2 *
      (wh n s p.1 * indicator (ah n s p.1 < p.2 ∧ p.2 ≤ bh n s p.1) -
        w n s p.1 * indicator (a p.1 < p.2 ∧ p.2 ≤ b p.1)))
  · intro n s
    fun_prop
  · intro n s x
    let := treatedLaw_isFiniteMeasure M L k x
    have hs :=
      (outcome_band_memLp (treatedLaw M L k x) (ah n s x) (bh n s x) (wh n s x)).sub
        (outcome_band_memLp (treatedLaw M L k x) (a x) (b x) (w n s x))
    convert hs using 1
    ext y
    exact mul_sub _ _ _
  · intro n s
    exact (treatedLaw_outcome_band_energy_bound M L k a b (ah n s) (bh n s)
      (w n s) (wh n s) B ha hb (hah n s) (hbh n s) (hw n s) (hwh n s)
      (hbound n s) (hi n s)).1
  · exact treatedLaw_outcome_band_sq_tendsto_probability_zero M μ L k a b ah bh w wh B
      ha hb hw hah hbh hwh hbound hi hr

-- @node: encoded_continuous_outcome_band_sq_tendsto_probability_zero
/-- Suppose [the true continuous nuisance is admissible](hyp:he0), [every fitted nuisance satisfies continuous clipping](hyp:hclip), [the fitted shares lie in their simplices](hyp:hshares), [all encoded fitted components are measurable](hyp:hm), [boundary densities are bounded](hyp:hd), and [the encoded components satisfy the finite nuisance rates](hyp:hr). For [a treated level immediately above the band level, or equal to a positive band level](hyp:hk'), [the integrated square of the outcome times the fitted regular coefficient times the difference between fitted and true quantile-band indicators, at even sample sizes, converges in probability to zero](goal). -/
lemma encoded_continuous_outcome_band_sq_tendsto_probability_zero
    [Fintype Z] (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n s, ContClipping M L (eh n s))
    (hshares : ∀ n s, ContFittedSharesSimplex L (eh n s))
    (hm : ∀ n s c, Measurable (contComponent M L (eh n s) c))
    (hd : BoundaryDensitiesBounded M L)
    (hr : FiniteNuisanceRates M μ (fun n s => contComponent M L (eh n s))
      (contComponent M L (trueNuisance M L)))
    (g : RegularIndex L) (k j₀ j₁ k' : ℕ)
    (hk' : k' = k + 1 ∨ (1 ≤ k ∧ k' = k)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n s => ∫ x, ∫ y,
        (y * ((eh (2*(n+1)) s).gamma g x *
          (indicator (nuValue M (eh (2*(n+1)) s) k j₀ x < y ∧
              y ≤ nuValue M (eh (2*(n+1)) s) k j₁ x) -
            indicator (nuValue M (trueNuisance M L) k j₀ x < y ∧
              y ≤ nuValue M (trueNuisance M L) k j₁ x)))) ^ 2
          ∂treatedLaw M L k' x ∂xLaw M) atTop (fun _ _ => 0) := by
  classical
  let er := fun n s => restrictContShares L (eh n s)
  have her n s : ContAdmissible M L (er n s) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n s)
      (hclip n s) (hshares n s) (hm n s)
  have hg n s : Measurable ((er n s).gamma g) ∧
      (∀ᵐ x ∂xLaw M, |(er n s).gamma g x| ≤ 1) := by
    rcases her n s with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hg, hgm, _⟩
    refine ⟨?_, ?_⟩
    · fun_prop
    · filter_upwards [hg g] with x hx
      simpa only [abs_of_nonneg hx.1] using hx.2
  have ht j : Measurable (nuValue M (trueNuisance M L) k j) := by
    fun_prop
  have hh n s j : Measurable (nuValue M (er n s) k j) := by
    first | fun_prop | exact continuous_admissible_nuValue_measurable M L _ (her n s) k j
  have hbounds n s : ∀ᵐ x ∂xLaw M,
      |nuValue M (trueNuisance M L) k j₀ x| ≤ |M.yMin| + |M.yMax| ∧
      |nuValue M (trueNuisance M L) k j₁ x| ≤ |M.yMin| + |M.yMax| ∧
      |nuValue M (er n s) k j₀ x| ≤ |M.yMin| + |M.yMax| ∧
      |nuValue M (er n s) k j₁ x| ≤ |M.yMin| + |M.yMax| := by
    filter_upwards [continuous_admissible_nuValue_abs_bound M L _ he0 k j₀,
      continuous_admissible_nuValue_abs_bound M L _ he0 k j₁,
      continuous_admissible_nuValue_abs_bound M L _ (her n s) k j₀,
      continuous_admissible_nuValue_abs_bound M L _ (her n s) k j₁] with x h0 h1 h2 h3
    exact ⟨h0, h1, h2, h3⟩
  have hi n s := (treatedLaw_weighted_quantile_band_integrated_sq_bound M L k'
    (nuValue M (trueNuisance M L) k j₀) (nuValue M (trueNuisance M L) k j₁)
    (nuValue M (er (2*(n+1)) s) k j₀) (nuValue M (er (2*(n+1)) s) k j₁)
    ((er (2*(n+1)) s).gamma g) 1 (ht _) (ht _) (hh _ s _) (hh _ s _)
    (hg _ s).1 (hg _ s).2).1
  have hband := treatedLaw_weighted_quantile_band_sq_tendsto_probability_zero M μ L k'
    (nuValue M (trueNuisance M L) k j₀) (nuValue M (trueNuisance M L) k j₁)
    (fun n s => nuValue M (er n s) k j₀) (fun n s => nuValue M (er n s) k j₁)
    (fun n s => (er n s).gamma g) 1 (ht _) (ht _)
    (fun n s => hh n s _) (fun n s => hh n s _)
    (fun n s => (hg n s).1) (fun n s => (hg n s).2)
    (encoded_continuous_nuValue_indicator_sq_tendsto_probability_zero
      M μ L he0 eh hclip hshares hm hd hr k j₀ k' hk')
    (encoded_continuous_nuValue_indicator_sq_tendsto_probability_zero
      M μ L he0 eh hclip hshares hm hd hr k j₁ k' hk')
  simpa only [← mul_sub, er, restrictContShares, nuValue] using
    (treatedLaw_outcome_band_sq_tendsto_probability_zero M μ L k'
      (nuValue M (trueNuisance M L) k j₀) (nuValue M (trueNuisance M L) k j₁)
      (fun n s => nuValue M (er (2*(n+1)) s) k j₀)
      (fun n s => nuValue M (er (2*(n+1)) s) k j₁)
      (fun n s => (er (2*(n+1)) s).gamma g)
      (fun n s => (er (2*(n+1)) s).gamma g) (|M.yMin| + |M.yMax|)
      (ht _) (ht _) (fun n s => (hg _ s).1)
      (fun n s => hh _ s _) (fun n s => hh _ s _) (fun n s => (hg _ s).1)
      (fun n s => hbounds _ s)
      (fun n s => by simpa only [mul_sub] using hi n s)
      (by simpa only [mul_sub] using hband))

-- @node: encoded_continuous_centered_outcome_band_sq_tendsto_probability_zero
/-- Suppose [the true continuous nuisance is admissible](hyp:he0), [every fitted nuisance satisfies continuous clipping](hyp:hclip), [the fitted shares lie in their simplices](hyp:hshares), [all encoded fitted components are measurable](hyp:hm), [boundary densities are bounded](hyp:hd), and [the encoded components satisfy the finite nuisance rates](hyp:hr). For [a treated level immediately above the band level, or equal to a positive band level](hyp:hk'), [the integrated square of the outcome-weighted, fitted-coefficient-weighted difference between fitted and true quantile-band indicators, centered by its conditional treated-law integral, converges in probability to zero along even sample sizes](goal). -/
lemma encoded_continuous_centered_outcome_band_sq_tendsto_probability_zero
    [Fintype Z] (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n s, ContClipping M L (eh n s))
    (hshares : ∀ n s, ContFittedSharesSimplex L (eh n s))
    (hm : ∀ n s c, Measurable (contComponent M L (eh n s) c))
    (hd : BoundaryDensitiesBounded M L)
    (hr : FiniteNuisanceRates M μ (fun n s => contComponent M L (eh n s))
      (contComponent M L (trueNuisance M L)))
    (g : RegularIndex L) (k j₀ j₁ k' : ℕ)
    (hk' : k' = k + 1 ∨ (1 ≤ k ∧ k' = k)) :
    let d : ℕ → A → X × ℝ → ℝ := fun n s p =>
      p.2 * ((eh (2*(n+1)) s).gamma g p.1 *
        (indicator (nuValue M (eh (2*(n+1)) s) k j₀ p.1 < p.2 ∧
            p.2 ≤ nuValue M (eh (2*(n+1)) s) k j₁ p.1) -
          indicator (nuValue M (trueNuisance M L) k j₀ p.1 < p.2 ∧
            p.2 ≤ nuValue M (trueNuisance M L) k j₁ p.1)))
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n s => ∫ x, ∫ y, (d n s (x, y) -
        ∫ z, d n s (x, z) ∂treatedLaw M L k' x) ^ 2
        ∂treatedLaw M L k' x ∂xLaw M) atTop (fun _ _ => 0) := by
  classical
  let er := fun n s => restrictContShares L (eh n s)
  have her n s : ContAdmissible M L (er n s) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n s)
      (hclip n s) (hshares n s) (hm n s)
  have hg n s : Measurable ((er n s).gamma g) ∧
      (∀ᵐ x ∂xLaw M, |(er n s).gamma g x| ≤ 1) := by
    rcases her n s with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hg, hgm, _⟩
    refine ⟨?_, ?_⟩
    · fun_prop
    · filter_upwards [hg g] with x hx
      simpa only [abs_of_nonneg hx.1] using hx.2
  have ht j : Measurable (nuValue M (trueNuisance M L) k j) := by
    fun_prop
  have hh n s j : Measurable (nuValue M (er n s) k j) := by
    first | fun_prop | exact continuous_admissible_nuValue_measurable M L _ (her n s) k j
  have hbounds n s : ∀ᵐ x ∂xLaw M,
      |nuValue M (trueNuisance M L) k j₀ x| ≤ |M.yMin| + |M.yMax| ∧
      |nuValue M (trueNuisance M L) k j₁ x| ≤ |M.yMin| + |M.yMax| ∧
      |nuValue M (er n s) k j₀ x| ≤ |M.yMin| + |M.yMax| ∧
      |nuValue M (er n s) k j₁ x| ≤ |M.yMin| + |M.yMax| := by
    filter_upwards [continuous_admissible_nuValue_abs_bound M L _ he0 k j₀,
      continuous_admissible_nuValue_abs_bound M L _ he0 k j₁,
      continuous_admissible_nuValue_abs_bound M L _ (her n s) k j₀,
      continuous_admissible_nuValue_abs_bound M L _ (her n s) k j₁] with x h0 h1 h2 h3
    exact ⟨h0, h1, h2, h3⟩
  have hi n s := (treatedLaw_weighted_quantile_band_integrated_sq_bound M L k'
    (nuValue M (trueNuisance M L) k j₀) (nuValue M (trueNuisance M L) k j₁)
    (nuValue M (er (2*(n+1)) s) k j₀) (nuValue M (er (2*(n+1)) s) k j₁)
    ((er (2*(n+1)) s).gamma g) 1 (ht _) (ht _) (hh _ s _) (hh _ s _)
    (hg _ s).1 (hg _ s).2).1
  have hband := treatedLaw_weighted_quantile_band_sq_tendsto_probability_zero M μ L k'
    (nuValue M (trueNuisance M L) k j₀) (nuValue M (trueNuisance M L) k j₁)
    (fun n s => nuValue M (er n s) k j₀) (fun n s => nuValue M (er n s) k j₁)
    (fun n s => (er n s).gamma g) 1 (ht _) (ht _)
    (fun n s => hh n s _) (fun n s => hh n s _)
    (fun n s => (hg n s).1) (fun n s => (hg n s).2)
    (encoded_continuous_nuValue_indicator_sq_tendsto_probability_zero
      M μ L he0 eh hclip hshares hm hd hr k j₀ k' hk')
    (encoded_continuous_nuValue_indicator_sq_tendsto_probability_zero
      M μ L he0 eh hclip hshares hm hd hr k j₁ k' hk')
  simpa only [← mul_sub, er, restrictContShares, nuValue] using
    (treatedLaw_centered_outcome_band_sq_tendsto_probability_zero M μ L k'
      (nuValue M (trueNuisance M L) k j₀) (nuValue M (trueNuisance M L) k j₁)
      (fun n s => nuValue M (er (2*(n+1)) s) k j₀)
      (fun n s => nuValue M (er (2*(n+1)) s) k j₁)
      (fun n s => (er (2*(n+1)) s).gamma g)
      (fun n s => (er (2*(n+1)) s).gamma g) (|M.yMin| + |M.yMax|)
      (ht _) (ht _) (fun n s => (hg _ s).1)
      (fun n s => hh _ s _) (fun n s => hh _ s _) (fun n s => (hg _ s).1)
      (fun n s => hbounds _ s)
      (fun n s => by simpa only [mul_sub] using hi n s)
      (by simpa only [mul_sub] using hband))

end Papers.TbsPrteOptimalTransport
