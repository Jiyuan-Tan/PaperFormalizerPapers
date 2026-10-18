module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLGammaOutcomeContrast
/-! Convergence of gamma-weighted plug-in outcome bands in continuous DML.
The propensity and product-weight rates control the coefficient, and the encoded
outcome-mean rates control each band. The minus baseline remains structural zero. -/
public section
set_option linter.style.openClassical false
set_option linter.unnecessarySimpa false
set_option linter.unusedFintypeInType false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: fitted_continuous_gamma_band_coordinates
/-- If [the continuous-outcome nuisance vector is admissible](hyp:he), then
[for either the upper or lower band, the product of a regular gamma weight and the corresponding treatment-level probability is measurable and bounded in absolute value by one almost everywhere, while the selected band mean is measurable and bounded in absolute value by the sum of the absolute outcome endpoints almost everywhere](goal). -/
lemma fitted_continuous_gamma_band_coordinates [Fintype Z]
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (g : RegularIndex L) (plus : Bool) (k j : ℕ) :
    (Measurable (fun x => e.gamma g x *
      positiveValue e.pLev (if plus then k+1 else k) x) ∧
      ∀ᵐ x ∂xLaw M, |e.gamma g x *
        positiveValue e.pLev (if plus then k+1 else k) x| ≤ 1) ∧
    (Measurable (fun x => if plus then meanValue e.Jplus k j x
      else minusMeanValue e.Jminus k j x) ∧
      ∀ᵐ x ∂xLaw M, |if plus then meanValue e.Jplus k j x
        else minusMeanValue e.Jminus k j x| ≤ |M.yMin| + |M.yMax|) := by
  have hp := (fitted_continuous_full_coordinates M L e he
    (if plus then k+1 else k)).1
  have hj := continuous_admissible_band_means_abs_bound M L e he k j
  have hgb : ∀ᵐ x ∂xLaw M, |e.gamma g x| ≤ 1 := by
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hb, _⟩
    filter_upwards [hb g] with x hx
    simpa only [abs_of_nonneg hx.1] using hx.2
  have hgm : Measurable (e.gamma g) := by
    first | fun_prop | skip
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hm, _⟩
    exact hm g
  have hJm : Measurable (fun x => if plus then meanValue e.Jplus k j x
      else minusMeanValue e.Jminus k j x) := by
    first | fun_prop | skip
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, hplus, _, hminus, _⟩
    cases plus <;> simp only [Bool.false_eq_true, Bool.true_eq, if_true, if_false]
    · unfold minusMeanValue
      split_ifs <;> fun_prop
    · unfold meanValue
      split_ifs <;> fun_prop
  refine ⟨⟨hgm.mul hp.1, ?_⟩, ⟨hJm, ?_⟩⟩
  · filter_upwards [hgb, hp.2] with x hx hy
    rw [abs_mul]
    exact (mul_le_mul hx hy (abs_nonneg _) zero_le_one).trans (by norm_num)
  · cases plus
    · simpa using hj.2
    · simpa using hj.1

-- @node: fitted_continuous_gamma_band_product_memLp
/-- If [the continuous-outcome nuisance vector is admissible](hyp:he), then
[the product of a regular gamma weight, the selected upper or lower treatment-level probability, and the corresponding outcome-band mean is square-integrable under the covariate law](goal). -/
lemma fitted_continuous_gamma_band_product_memLp [Fintype Z]
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (g : RegularIndex L) (plus : Bool) (k j : ℕ) :
    MemLp (fun x => (e.gamma g x * positiveValue e.pLev
      (if plus then k+1 else k) x) *
      (if plus then meanValue e.Jplus k j x else minusMeanValue e.Jminus k j x))
      2 (xLaw M) := by
  have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  obtain ⟨hw, hJ⟩ := fitted_continuous_gamma_band_coordinates M L e he g plus k j
  apply MemLp.of_bound (by first | fun_prop | exact (hw.1.mul hJ.1).aestronglyMeasurable)
    (|M.yMin| + |M.yMax|)
  filter_upwards [hw.2, hJ.2] with x hx hy
  rw [Real.norm_eq_abs, abs_mul]
  exact (mul_le_mul hx hy (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

-- @node: encoded_continuous_gamma_band_product_sq_tendsto_probability_zero
/-- Suppose [the true continuous-outcome nuisance vector is admissible](hyp:he0),
[all fitted nuisance vectors satisfy the clipping restrictions](hyp:hclip),
[all fitted share vectors lie in the simplex](hyp:hshares), and
[all encoded fitted components are measurable](hyp:hm).
If [the encoded components satisfy the finite nuisance rates relative to truth](hyp:hr), then
[for either the upper or lower band, the covariate-law integrated squared error of gamma times the corresponding treatment-level probability times the band mean converges in probability to zero along sample sizes twice n plus two](goal). -/
lemma encoded_continuous_gamma_band_product_sq_tendsto_probability_zero [Fintype Z]
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L)))
    (g : RegularIndex L) (plus : Bool) (k j : ℕ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x,
        (((eh (2*(n+1)) t).gamma g x * positiveValue (eh (2*(n+1)) t).pLev
          (if plus then k+1 else k) x) *
          (if plus then meanValue (eh (2*(n+1)) t).Jplus k j x
            else minusMeanValue (eh (2*(n+1)) t).Jminus k j x) -
        ((trueNuisance M L).gamma g x * positiveValue (trueNuisance M L).pLev
          (if plus then k+1 else k) x) *
          (if plus then meanValue (trueNuisance M L).Jplus k j x
            else minusMeanValue (trueNuisance M L).Jminus k j x))^2 ∂xLaw M)
      atTop (fun _ _ => 0) := by
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  let w := fun (e : NuisanceCont L) x => e.gamma g x *
    positiveValue e.pLev (if plus then k+1 else k) x
  let J := fun (e : NuisanceCont L) x =>
    if plus then meanValue e.Jplus k j x else minusMeanValue e.Jminus k j x
  have hc (e : NuisanceCont L) (he : ContAdmissible M L e) :=
    fitted_continuous_gamma_band_coordinates M L e he g plus k j
  have hmem (f : X → ℝ) (hf : Measurable f) (R : ℝ)
      (hb : ∀ᵐ x ∂xLaw M, |f x| ≤ R) : MemLp f 2 (xLaw M) :=
    MemLp.of_bound hf.aestronglyMeasurable R (by simpa only [Real.norm_eq_abs] using hb)
  obtain ⟨_, hrp, _, _, _, _, hrg, _⟩ :=
    continuous_component_rates_to_oracle_rates M μ L eh (trueNuisance M L) hr
  have hrw := nuisanceRates_continuous_band_coefficient_sq_tendsto_probability_zero
    M μ L (trueNuisance M L) er he0 her hrp hrg g (if plus then k+1 else k)
  have hrJ : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (J (er (2*(n+1)) t) x - J (trueNuisance M L) x)^2
        ∂xLaw M) atTop (fun _ _ => 0) := by
    let z0 : Z := Classical.choice inferInstance
    cases plus
    · simpa only [J, Bool.false_eq_true, if_false, er, restrictContShares, contComponent] using
        nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hr (12, k, j, z0)
    · simpa only [J, Bool.true_eq, if_true, er, restrictContShares, contComponent] using
        nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hr (11, k, j, z0)
  have hs := dml_weighted_residual_sq_tendsto_probability_zero μ (xLaw M)
    (w (trueNuisance M L)) (J (trueNuisance M L))
    (fun n t => w (er (2*(n+1)) t)) (fun n t => J (er (2*(n+1)) t))
    1 (|M.yMin| + |M.yMax|) (hc _ he0).1.1 (hc _ he0).2.1
    (fun n t => (hc _ (her _ t)).1.1) (fun n t => (hc _ (her _ t)).2.1)
    (fun n t => (hmem _ (hc _ (her _ t)).1.1 _ (hc _ (her _ t)).1.2).sub
      (hmem _ (hc _ he0).1.1 _ (hc _ he0).1.2))
    (fun n t => (hmem _ (hc _ (her _ t)).2.1 _ (hc _ (her _ t)).2.2).sub
      (hmem _ (hc _ he0).2.1 _ (hc _ he0).2.2))
    (fun n t => (hc _ (her _ t)).1.2) (fun _ _ => (hc _ he0).2.2) hrw hrJ
  simpa only [w, J, er, restrictContShares] using hs

-- @node: fitted_continuous_gamma_contJ_memLp
/-- If [the continuous-outcome nuisance vector is admissible](hyp:he), then
[a regular gamma weight multiplied by any chosen outcome-band contrast is square-integrable under the observation law](goal). -/
lemma fitted_continuous_gamma_contJ_memLp [Fintype Z]
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (g : RegularIndex L) (k j : ℕ) :
    MemLp (fun o : Obs X Z => e.gamma g o.1 * contJ L e k j o.1)
      2 (observationLaw M) := by
  have hs := (fitted_continuous_gamma_band_product_memLp M L e he g true k j).sub
    (fitted_continuous_gamma_band_product_memLp M L e he g false k j)
  have hx : MemLp (fun x => e.gamma g x * contJ L e k j x) 2 (xLaw M) := by
    convert hs using 1
    funext x
    simp only [contJ, Pi.sub_apply, Bool.true_eq, Bool.false_eq_true, if_true, if_false]
    ring
  exact hx.comp_measurePreserving (observationLaw_fst_measurePreserving M)

-- @node: encoded_continuous_gamma_contJ_sq_tendsto_probability_zero
/-- Suppose [the true continuous-outcome nuisance vector is admissible](hyp:he0),
[all fitted nuisance vectors satisfy the clipping restrictions](hyp:hclip),
[all fitted share vectors lie in the simplex](hyp:hshares), and
[all encoded fitted components are measurable](hyp:hm).
If [the encoded components satisfy the finite nuisance rates relative to truth](hyp:hr), then
[the observation-law integrated squared error of a regular gamma weight times any chosen outcome-band contrast converges in probability to zero along sample sizes twice n plus two](goal). -/
lemma encoded_continuous_gamma_contJ_sq_tendsto_probability_zero [Fintype Z]
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L)))
    (g : RegularIndex L) (k j : ℕ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o : Obs X Z,
        ((eh (2*(n+1)) t).gamma g o.1 * contJ L (eh (2*(n+1)) t) k j o.1 -
          (trueNuisance M L).gamma g o.1 * contJ L (trueNuisance M L) k j o.1)^2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  let F := fun (plus : Bool) (e : NuisanceCont L) x =>
    (e.gamma g x * positiveValue e.pLev (if plus then k+1 else k) x) *
      (if plus then meanValue e.Jplus k j x else minusMeanValue e.Jminus k j x)
  let r := fun plus n t x => F plus (er (2*(n+1)) t) x - F plus (trueNuisance M L) x
  have hmem plus n t : MemLp (r plus n t) 2 (xLaw M) :=
    (fitted_continuous_gamma_band_product_memLp M L _ (her _ t) g plus k j).sub
      (fitted_continuous_gamma_band_product_memLp M L _ he0 g plus k j)
  have hrate plus : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (r plus n t x)^2 ∂xLaw M) atTop (fun _ _ => 0) := by
    simpa only [r, F, er, restrictContShares] using
      encoded_continuous_gamma_band_product_sq_tendsto_probability_zero
        M μ L he0 eh hclip hshares hm hr g plus k j
  have hz : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun _ : ℕ => fun _ : A => (0 : ℝ)) atTop (fun _ _ => 0) := by
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
    intro eps heps
    simpa [not_le_of_gt heps] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
  have hs := dml_three_term_sq_tendsto_probability_zero μ (xLaw M)
    (r true) (fun _ _ _ => 0) (r false) (hmem true)
    (fun _ _ => MemLp.zero) (hmem false) (hrate true) (by simpa using hz) (hrate false)
  have hi n t : (∫ o : Obs X Z, (r true n t o.1 + 0 - r false n t o.1)^2
      ∂observationLaw M) = ∫ x, (r true n t x + 0 - r false n t x)^2 ∂xLaw M := by
    classical
    apply observationLaw_covariate_integral M (fun x => (r true n t x + 0 - r false n t x)^2)
    have hme plus (e : NuisanceCont L) (he : ContAdmissible M L e) :
        Measurable (F plus e) := by
      obtain ⟨hw, hJ⟩ := fitted_continuous_gamma_band_coordinates M L e he g plus k j
      first | fun_prop | exact hw.1.mul hJ.1
    have hp := (hme true _ (her (2*(n+1)) t)).sub (hme true _ he0)
    have hn := (hme false _ (her (2*(n+1)) t)).sub (hme false _ he0)
    first | fun_prop | exact ((hp.add measurable_const).sub hn).pow_const 2
  have hs' : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o : Obs X Z, (r true n t o.1 + 0 - r false n t o.1)^2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
    simpa only [hi] using hs
  convert hs' using 1
  funext n t
  congr 1
  funext o
  simp only [r, F, er, restrictContShares, contJ,
    Bool.true_eq, Bool.false_eq_true, if_true, if_false]
  ring

end Papers.TbsPrteOptimalTransport
