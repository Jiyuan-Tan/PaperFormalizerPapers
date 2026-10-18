module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLOutcomeBandConvergence
/-! Changing weights and quantile boundaries in outcome bands.
The band discrepancy splits into a moving-boundary term and a coefficient
error. Square-energy bounds control their sum, multiplication by the bounded
outcome on the bands, and conditional centering. -/
public section
set_option linter.style.openClassical false
set_option linter.unreachableTactic false
set_option linter.unusedFintypeInType false
set_option linter.unusedTactic false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open Classical

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: treatedLaw_sum_sq_tendsto_probability_zero
/-- Suppose [the first function sequence is measurable](hyp:hf) and [the second is
measurable](hyp:hg), [the first has square-integrable treated-law sections](hyp:hfm)
and [so does the second](hyp:hgm), and [the first conditional squared energies are
integrable over covariates](hyp:hfi), [as are the second](hyp:hgi). If [the first
integrated squared energies vanish in probability](hyp:hrf) and [the second integrated
squared energies vanish in probability](hyp:hrg), then [the integrated squared energy
of their sum converges to zero in probability](goal). -/
lemma treatedLaw_sum_sq_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X) (k : ℕ)
    (f g : ℕ → A → X × ℝ → ℝ)
    (hf : ∀ n a, Measurable (f n a)) (hg : ∀ n a, Measurable (g n a))
    (hfm : ∀ n a x, MemLp (fun y => f n a (x, y)) 2 (treatedLaw M L k x))
    (hgm : ∀ n a x, MemLp (fun y => g n a (x, y)) 2 (treatedLaw M L k x))
    (hfi : ∀ n a, Integrable (fun x => ∫ y, f n a (x, y) ^ 2
      ∂treatedLaw M L k x) (xLaw M))
    (hgi : ∀ n a, Integrable (fun x => ∫ y, g n a (x, y) ^ 2
      ∂treatedLaw M L k x) (xLaw M))
    (hrf : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, ∫ y, f n a (x, y) ^ 2 ∂treatedLaw M L k x ∂xLaw M)
      atTop (fun _ _ => 0))
    (hrg : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, ∫ y, g n a (x, y) ^ 2 ∂treatedLaw M L k x ∂xLaw M)
      atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, ∫ y,
        (f n a (x, y) + g n a (x, y)) ^ 2
        ∂treatedLaw M L k x ∂xLaw M) atTop (fun _ _ => 0) := by
  have hn := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    (show Continuous (fun t : ℝ => -t) by fun_prop).continuousAt hrg
  simp only [neg_zero] at hn
  have hs := hrf.sub hn
  simp only [sub_zero, sub_neg_eq_add] at hs
  have ht := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    (show Continuous (fun t : ℝ => 2 * t) by fun_prop).continuousAt hs
  simp only [mul_zero] at ht
  apply probability_zero_of_nonneg_le μ _ _ ht
  intro n
  apply Eventually.of_forall
  intro a
  exact ⟨integral_nonneg fun x => integral_nonneg fun y => sq_nonneg _,
    (treatedLaw_sum_integrated_sq_le M L k _ _ (hf n a) (hg n a)
      (hfm n a) (hgm n a) (hfi n a) (hgi n a)).2⟩

-- @node: treatedLaw_changing_weight_band_energy_and_convergence
/-- Suppose [the true lower endpoint is measurable](hyp:ha), [the true upper endpoint
is measurable](hyp:hb), [the true weight is measurable](hyp:hw0), [all fitted lower
endpoints are measurable](hyp:hah), [all fitted upper endpoints are measurable](hyp:hbh),
and [all fitted weights are measurable](hyp:hw). If [fitted weights have a common
absolute bound almost everywhere over covariates](hyp:hwb), [weight errors are square
integrable](hyp:hwm), [lower-threshold indicator errors vanish in treated integrated
square in probability](hyp:hA), [upper-threshold indicator errors do likewise](hyp:hB),
and [weight errors vanish in covariate mean square in probability](hyp:hW), then
[the difference between fitted and true weighted band indicators has integrable
conditional squared energy whose covariate average converges to zero in probability
along even sample sizes](goal). -/
lemma treatedLaw_changing_weight_band_energy_and_convergence
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X) (k : ℕ)
    (a b w0 : X → ℝ) (ah bh w : ℕ → A → X → ℝ) (D : ℝ)
    (ha : Measurable a) (hb : Measurable b) (hw0 : Measurable w0)
    (hah : ∀ n s, Measurable (ah n s)) (hbh : ∀ n s, Measurable (bh n s))
    (hw : ∀ n s, Measurable (w n s))
    (hwb : ∀ n s, ∀ᵐ x ∂xLaw M, |w n s x| ≤ D)
    (hwm : ∀ n s, MemLp (fun x => w n s x - w0 x) 2 (xLaw M))
    (hA : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n s => ∫ x, ∫ y, (indicator (y ≤ ah (2 * (n + 1)) s x) -
        indicator (y ≤ a x)) ^ 2 ∂treatedLaw M L k x ∂xLaw M)
      atTop (fun _ _ => 0))
    (hB : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n s => ∫ x, ∫ y, (indicator (y ≤ bh (2 * (n + 1)) s x) -
        indicator (y ≤ b x)) ^ 2 ∂treatedLaw M L k x ∂xLaw M)
      atTop (fun _ _ => 0))
    (hW : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n s => ∫ x, (w (2 * (n + 1)) s x - w0 x) ^ 2 ∂xLaw M)
      atTop (fun _ _ => 0)) :
    let d : ℕ → A → X × ℝ → ℝ := fun n s p =>
      w (2 * (n + 1)) s p.1 * indicator (ah (2 * (n + 1)) s p.1 < p.2 ∧
        p.2 ≤ bh (2 * (n + 1)) s p.1) -
      w0 p.1 * indicator (a p.1 < p.2 ∧ p.2 ≤ b p.1)
    (∀ n s, Integrable (fun x => ∫ y, d n s (x, y) ^ 2
      ∂treatedLaw M L k x) (xLaw M)) ∧
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n s => ∫ x, ∫ y, d n s (x, y) ^ 2
        ∂treatedLaw M L k x ∂xLaw M) atTop (fun _ _ => 0) := by
  dsimp only
  let f : ℕ → A → X × ℝ → ℝ := fun n s p =>
    w (2 * (n + 1)) s p.1 * (indicator (ah (2 * (n + 1)) s p.1 < p.2 ∧
      p.2 ≤ bh (2 * (n + 1)) s p.1) - indicator (a p.1 < p.2 ∧ p.2 ≤ b p.1))
  let g : ℕ → A → X × ℝ → ℝ := fun n s p =>
    (w (2 * (n + 1)) s p.1 - w0 p.1) * indicator (a p.1 < p.2 ∧ p.2 ≤ b p.1)
  have hBand (c d : X → ℝ) (hc : Measurable c) (hd : Measurable d) :
      Measurable (fun p : X × ℝ => indicator (c p.1 < p.2 ∧ p.2 ≤ d p.1)) := by
    fun_prop
  have hf n s : Measurable (f n s) :=
    ((hw _ s).comp measurable_fst).mul
      ((hBand _ _ (hah _ s) (hbh _ s)).sub (hBand _ _ ha hb))
  have hg n s : Measurable (g n s) :=
    (((hw _ s).sub hw0).comp measurable_fst).mul (hBand _ _ ha hb)
  have hfm n s x : MemLp (fun y => f n s (x, y)) 2 (treatedLaw M L k x) := by
    let := treatedLaw_isFiniteMeasure M L k x
    apply MemLp.of_bound (by
      first | fun_prop | exact ((hf n s).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      |w (2 * (n + 1)) s x|
    apply Eventually.of_forall
    intro y
    dsimp only [f]
    unfold indicator
    split_ifs <;> simp [Real.norm_eq_abs]
  have hgm n s x : MemLp (fun y => g n s (x, y)) 2 (treatedLaw M L k x) := by
    let := treatedLaw_isFiniteMeasure M L k x
    apply MemLp.of_bound (by
      first | fun_prop | exact ((hg n s).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      |w (2 * (n + 1)) s x - w0 x|
    apply Eventually.of_forall
    intro y
    dsimp only [g]
    unfold indicator
    split_ifs <;> simp [Real.norm_eq_abs]
  have hgi n s := treatedLaw_bounded_multiplier_integrated_sq_le M L k
    (fun x => w (2 * (n + 1)) s x - w0 x)
    (fun p => indicator (a p.1 < p.2 ∧ p.2 ≤ b p.1))
    ((hw _ s).sub hw0) (hBand _ _ ha hb)
    (fun x y => by unfold indicator; split_ifs <;> norm_num)
    (hwm _ s).integrable_sq
  have hgr : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n s => ∫ x, ∫ y, g n s (x, y) ^ 2 ∂treatedLaw M L k x ∂xLaw M)
      atTop (fun _ _ => 0) := by
    apply probability_zero_of_nonneg_le μ _ _ hW
    intro n
    apply Eventually.of_forall
    intro s
    exact ⟨integral_nonneg fun x => integral_nonneg fun y => sq_nonneg _, (hgi n s).2⟩
  have hfr := treatedLaw_weighted_quantile_band_sq_tendsto_probability_zero M μ L k
    a b ah bh w D ha hb hah hbh hw hwb hA hB
  have hfi n s := (treatedLaw_weighted_quantile_band_integrated_sq_bound M L k
    a b (ah (2 * (n + 1)) s) (bh (2 * (n + 1)) s) (w (2 * (n + 1)) s) D
    ha hb (hah _ s) (hbh _ s) (hw _ s) (hwb _ s)).1
  have hsum n s := treatedLaw_sum_integrated_sq_le M L k (f n s) (g n s)
    (hf n s) (hg n s) (hfm n s) (hgm n s) (hfi n s) (hgi n s).1
  have hs := treatedLaw_sum_sq_tendsto_probability_zero M μ L k f g hf hg hfm hgm
    hfi (fun n s => (hgi n s).1) hfr hgr
  have hid n s p : f n s p + g n s p =
      w (2 * (n + 1)) s p.1 * indicator (ah (2 * (n + 1)) s p.1 < p.2 ∧
        p.2 ≤ bh (2 * (n + 1)) s p.1) -
      w0 p.1 * indicator (a p.1 < p.2 ∧ p.2 ≤ b p.1) := by
    dsimp only [f, g]
    ring
  refine ⟨?_, ?_⟩
  · intro n s
    simpa only [hid] using (hsum n s).1
  · simpa only [hid] using hs

-- @node: treatedLaw_changing_weight_centered_outcome_band_sq_tendsto_probability_zero
/-- Suppose [the true lower endpoint is measurable](hyp:ha), [the true upper endpoint
is measurable](hyp:hb), [the true weight is measurable](hyp:hw0), [all fitted lower
endpoints are measurable](hyp:hah), [all fitted upper endpoints are measurable](hyp:hbh),
and [all fitted weights are measurable](hyp:hw). If [fitted weights have a common
absolute bound almost everywhere](hyp:hwb), [all true and fitted endpoints have a
common absolute bound almost everywhere](hyp:hbound), [weight errors are square
integrable](hyp:hwm), [lower-threshold indicator errors](hyp:hA) and [upper-threshold
indicator errors](hyp:hB) vanish in treated integrated square in probability, and
[weight errors vanish in covariate mean square in probability](hyp:hW), then
[the outcome times the difference of fitted and true weighted band indicators,
centered by its treated-law integral, has integrated squared energy converging to
zero in probability along even sample sizes](goal). -/
lemma treatedLaw_changing_weight_centered_outcome_band_sq_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X) (k : ℕ)
    (a b w0 : X → ℝ) (ah bh w : ℕ → A → X → ℝ) (D B : ℝ)
    (ha : Measurable a) (hb : Measurable b) (hw0 : Measurable w0)
    (hah : ∀ n s, Measurable (ah n s)) (hbh : ∀ n s, Measurable (bh n s))
    (hw : ∀ n s, Measurable (w n s))
    (hwb : ∀ n s, ∀ᵐ x ∂xLaw M, |w n s x| ≤ D)
    (hbound : ∀ n s, ∀ᵐ x ∂xLaw M,
      |a x| ≤ B ∧ |b x| ≤ B ∧ |ah n s x| ≤ B ∧ |bh n s x| ≤ B)
    (hwm : ∀ n s, MemLp (fun x => w n s x - w0 x) 2 (xLaw M))
    (hA : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n s => ∫ x, ∫ y, (indicator (y ≤ ah (2 * (n + 1)) s x) -
        indicator (y ≤ a x)) ^ 2 ∂treatedLaw M L k x ∂xLaw M)
      atTop (fun _ _ => 0))
    (hB : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n s => ∫ x, ∫ y, (indicator (y ≤ bh (2 * (n + 1)) s x) -
        indicator (y ≤ b x)) ^ 2 ∂treatedLaw M L k x ∂xLaw M)
      atTop (fun _ _ => 0))
    (hW : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n s => ∫ x, (w (2 * (n + 1)) s x - w0 x) ^ 2 ∂xLaw M)
      atTop (fun _ _ => 0)) :
    let d : ℕ → A → X × ℝ → ℝ := fun n s p => p.2 *
      (w (2 * (n + 1)) s p.1 * indicator (ah (2 * (n + 1)) s p.1 < p.2 ∧
        p.2 ≤ bh (2 * (n + 1)) s p.1) -
      w0 p.1 * indicator (a p.1 < p.2 ∧ p.2 ≤ b p.1))
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n s => ∫ x, ∫ y, (d n s (x, y) -
        ∫ z, d n s (x, z) ∂treatedLaw M L k x) ^ 2
        ∂treatedLaw M L k x ∂xLaw M) atTop (fun _ _ => 0) := by
  dsimp only
  obtain ⟨hi, hr⟩ := treatedLaw_changing_weight_band_energy_and_convergence
    M μ L k a b w0 ah bh w D ha hb hw0 hah hbh hw hwb hwm hA hB hW
  exact treatedLaw_centered_outcome_band_sq_tendsto_probability_zero
    M μ L k a b (fun n s => ah (2 * (n + 1)) s) (fun n s => bh (2 * (n + 1)) s)
    (fun _ _ => w0) (fun n s => w (2 * (n + 1)) s) B ha hb (fun _ _ => hw0)
    (fun n s => hah _ s) (fun n s => hbh _ s) (fun n s => hw _ s)
    (fun n s => hbound _ s) hi hr

-- @node: encoded_continuous_changing_weight_centered_outcome_band_sq_tendsto_probability_zero
/-- Suppose [the true continuous nuisance is admissible](hyp:he0), [fitted nuisances
are clipped](hyp:hclip), [fitted shares lie in the simplex](hyp:hshares), [all encoded
fitted components are measurable](hyp:hm), [boundary densities are bounded](hyp:hd),
and [the encoded estimates satisfy the finite nuisance rates](hyp:hr). If [the treated
level is the upper adjacent level, or the lower adjacent level at a positive boundary](hyp:hk'),
then [the outcome times the difference between fitted and true product-score-weighted
quantile-band indicators, centered by its treated-law integral, has integrated squared
energy converging to zero in probability along even sample sizes](goal). -/
lemma encoded_continuous_changing_weight_centered_outcome_band_sq_tendsto_probability_zero
    [Fintype Z] (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n a, ContClipping M L (eh n a))
    (hshares : ∀ n a, ContFittedSharesSimplex L (eh n a))
    (hm : ∀ n a c, Measurable (contComponent M L (eh n a) c))
    (hd : BoundaryDensitiesBounded M L)
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (g : RegularIndex L) (k j₀ j₁ k' : ℕ)
    (hk' : k' = k + 1 ∨ (1 ≤ k ∧ k' = k)) :
    let d : ℕ → A → X × ℝ → ℝ := fun n a p => p.2 *
      ((eh (2 * (n + 1)) a).gamma g p.1 *
        indicator (nuValue M (eh (2 * (n + 1)) a) k j₀ p.1 < p.2 ∧
          p.2 ≤ nuValue M (eh (2 * (n + 1)) a) k j₁ p.1) -
      (trueNuisance M L).gamma g p.1 *
        indicator (nuValue M (trueNuisance M L) k j₀ p.1 < p.2 ∧
          p.2 ≤ nuValue M (trueNuisance M L) k j₁ p.1))
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, ∫ y, (d n a (x, y) -
        ∫ z, d n a (x, z) ∂treatedLaw M L k' x) ^ 2
        ∂treatedLaw M L k' x ∂xLaw M) atTop (fun _ _ => 0) := by
  classical
  let er := fun n a => restrictContShares L (eh n a)
  have her n a : ContAdmissible M L (er n a) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n a)
      (hclip n a) (hshares n a) (hm n a)
  have hgamma (e : NuisanceCont L) (he : ContAdmissible M L e) :
      Measurable (e.gamma g) ∧ (∀ᵐ x ∂xLaw M, |e.gamma g x| ≤ 1) := by
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hg, hgm, _⟩
    refine ⟨?_, ?_⟩
    · first | fun_prop | exact hgm g
    · filter_upwards [hg g] with x hx
      simpa only [abs_of_nonneg hx.1] using hx.2
  have hmem (e : NuisanceCont L) (he : ContAdmissible M L e) :
      MemLp (e.gamma g) 2 (xLaw M) := by
    have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
    apply MemLp.of_bound (by first | fun_prop | exact (hgamma e he).1.aestronglyMeasurable) 1
    simpa only [Real.norm_eq_abs] using (hgamma e he).2
  obtain ⟨_, _, _, _, _, _, hrg, _⟩ :=
    continuous_component_rates_to_oracle_rates M μ L eh (trueNuisance M L) hr
  have hbounds n a : ∀ᵐ x ∂xLaw M,
      |nuValue M (trueNuisance M L) k j₀ x| ≤ |M.yMin| + |M.yMax| ∧
      |nuValue M (trueNuisance M L) k j₁ x| ≤ |M.yMin| + |M.yMax| ∧
      |nuValue M (er n a) k j₀ x| ≤ |M.yMin| + |M.yMax| ∧
      |nuValue M (er n a) k j₁ x| ≤ |M.yMin| + |M.yMax| := by
    filter_upwards [continuous_admissible_nuValue_abs_bound M L _ he0 k j₀,
      continuous_admissible_nuValue_abs_bound M L _ he0 k j₁,
      continuous_admissible_nuValue_abs_bound M L _ (her n a) k j₀,
      continuous_admissible_nuValue_abs_bound M L _ (her n a) k j₁] with x h0 h1 h2 h3
    exact ⟨h0, h1, h2, h3⟩
  exact treatedLaw_changing_weight_centered_outcome_band_sq_tendsto_probability_zero
    M μ L k' (nuValue M (trueNuisance M L) k j₀)
    (nuValue M (trueNuisance M L) k j₁) ((trueNuisance M L).gamma g)
    (fun n a => nuValue M (er n a) k j₀)
    (fun n a => nuValue M (er n a) k j₁) (fun n a => (er n a).gamma g) 1 (|M.yMin| + |M.yMax|)
    (by fun_prop) (by fun_prop) (hgamma _ he0).1
    (fun n a => continuous_admissible_nuValue_measurable M L _ (her n a) k j₀)
    (fun n a => continuous_admissible_nuValue_measurable M L _ (her n a) k j₁)
    (fun n a => (hgamma _ (her n a)).1)
    (fun n a => (hgamma _ (her n a)).2)
    hbounds
    (fun n a => (hmem _ (her n a)).sub (hmem _ he0))
    (encoded_continuous_nuValue_indicator_sq_tendsto_probability_zero
      M μ L he0 eh hclip hshares hm hd hr k j₀ k' hk')
    (encoded_continuous_nuValue_indicator_sq_tendsto_probability_zero
      M μ L he0 eh hclip hshares hm hd hr k j₁ k' hk')
    (nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hrg g)


end Papers.TbsPrteOptimalTransport
