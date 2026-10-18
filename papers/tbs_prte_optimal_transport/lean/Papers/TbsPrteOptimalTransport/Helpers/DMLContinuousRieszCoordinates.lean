module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLQuantileBoundaryBlock
/-! Smooth continuous propensity representers from encoded nuisance rates.
Clipping bounds boundary means and quantiles. Their products converge in L2,
and both propensity coefficients are assembled from their smooth coordinates. -/
public section
set_option linter.unnecessarySimpa false
set_option linter.unreachableTactic false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: continuous_admissible_boundaryValue_coordinates
/-- If [the continuous nuisance record is admissible](hyp:he), then [its upper boundary-mean coordinate is measurable and has absolute value at most one almost everywhere under the covariate law](goal). -/
lemma continuous_admissible_boundaryValue_coordinates [Fintype Z]
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (k j : ℕ) :
    Measurable (boundaryValue e.Mplus k j) ∧
      (∀ᵐ x ∂xLaw M, |boundaryValue e.Mplus k j x| ≤ 1) := by
  rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hb, hm, _⟩
  unfold boundaryValue
  split_ifs with hj hlast
  · refine ⟨by first | fun_prop | exact hm _, ?_⟩
    filter_upwards [hb ⟨(k,j), hj⟩] with x hx
    simpa only [abs_of_nonneg hx.1] using hx.2
  · exact ⟨measurable_const, Eventually.of_forall (by simp)⟩
  · exact ⟨measurable_const, Eventually.of_forall (by simp)⟩

-- @node: fitted_continuous_quantile_boundary_product_memLp
/-- If [the continuous nuisance record is admissible](hyp:he), then [the product of its quantile and upper boundary-mean coordinates is square integrable under the covariate law](goal). -/
lemma fitted_continuous_quantile_boundary_product_memLp [Fintype Z]
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (k j : ℕ) :
    MemLp (fun x => nuValue M e k j x * boundaryValue e.Mplus k j x)
      2 (xLaw M) := by
  have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  obtain ⟨hm, hb⟩ := continuous_admissible_boundaryValue_coordinates M L e he k j
  have hn := continuous_admissible_nuValue_measurable M L e he k j
  apply MemLp.of_bound (by fun_prop) (|M.yMin| + |M.yMax|)
  filter_upwards [hb, continuous_admissible_nuValue_abs_bound M L e he k j] with x hx hy
  rw [Real.norm_eq_abs, abs_mul]
  exact (mul_le_mul hy hx (abs_nonneg _) (by positivity)).trans_eq (mul_one _)

-- No density assumption is required for these smooth boundary-mean products.
-- @node: encoded_continuous_quantile_boundary_product_sq_tendsto_probability_zero
/-- If [the true nuisance record is admissible](hyp:he0), [all fitted records satisfy continuous clipping](hyp:hclip), [their fitted shares lie in the simplex](hyp:hshares), [all encoded fitted coordinates are measurable](hyp:hm), and [the encoded coordinates satisfy the finite nuisance rates toward truth](hyp:hr), then [the population integrated squared error of the quantile times upper boundary-mean product, evaluated at even sample sizes, converges in probability to zero](goal). -/
lemma encoded_continuous_quantile_boundary_product_sq_tendsto_probability_zero [Fintype Z]
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L))) (k j : ℕ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x,
        (nuValue M (eh (2*(n+1)) t) k j x * boundaryValue (eh (2*(n+1)) t).Mplus k j x -
          nuValue M (trueNuisance M L) k j x * boundaryValue (trueNuisance M L).Mplus k j x)^2
        ∂xLaw M) atTop (fun _ _ => 0) := by
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  let N := fun (e : NuisanceCont L) => nuValue M e k j
  let B := fun (e : NuisanceCont L) => boundaryValue e.Mplus k j
  have hN (e : NuisanceCont L) (he : ContAdmissible M L e) :
      Measurable (N e) ∧ (∀ᵐ x ∂xLaw M, |N e x| ≤ |M.yMin| + |M.yMax|) :=
    ⟨continuous_admissible_nuValue_measurable M L e he k j,
      continuous_admissible_nuValue_abs_bound M L e he k j⟩
  have hB (e : NuisanceCont L) (he : ContAdmissible M L e) :=
    continuous_admissible_boundaryValue_coordinates M L e he k j
  have hmem (f : X → ℝ) (hf : Measurable f) (R : ℝ)
      (hb : ∀ᵐ x ∂xLaw M, |f x| ≤ R) : MemLp f 2 (xLaw M) :=
    MemLp.of_bound hf.aestronglyMeasurable R (by simpa only [Real.norm_eq_abs] using hb)
  let z0 : Z := Classical.choice inferInstance
  have hrN : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (N (er (2*(n+1)) t) x - N (trueNuisance M L) x)^2
        ∂xLaw M) atTop (fun _ _ => 0) := by
    simpa only [N, er, restrictContShares, contComponent, nuValue] using
      nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hr (8,k,j,z0)
  have hrB : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (B (er (2*(n+1)) t) x - B (trueNuisance M L) x)^2
        ∂xLaw M) atTop (fun _ _ => 0) := by
    simpa only [B, er, restrictContShares, contComponent, nuValue] using
      nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hr (9,k,j,z0)
  have hs := dml_weighted_residual_sq_tendsto_probability_zero μ (xLaw M)
    (N (trueNuisance M L)) (B (trueNuisance M L))
    (fun n t => N (er (2*(n+1)) t)) (fun n t => B (er (2*(n+1)) t))
    (|M.yMin| + |M.yMax|) 1 (hN _ he0).1 (hB _ he0).1
    (fun n t => (hN _ (her _ t)).1) (fun n t => (hB _ (her _ t)).1)
    (fun n t => (hmem _ (hN _ (her _ t)).1 _ (hN _ (her _ t)).2).sub
      (hmem _ (hN _ he0).1 _ (hN _ he0).2))
    (fun n t => (hmem _ (hB _ (her _ t)).1 _ (hB _ (her _ t)).2).sub
      (hmem _ (hB _ he0).1 _ (hB _ he0).2))
    (fun n t => (hN _ (her _ t)).2) (fun _ _ => (hB _ he0).2) hrN hrB
  simpa only [N, B, er, restrictContShares, nuValue] using hs

-- @node: fitted_continuous_meanValue_memLp
/-- If [the continuous nuisance record is admissible](hyp:he), then [its upper band-mean coordinate is square integrable under the covariate law](goal). -/
lemma fitted_continuous_meanValue_memLp [Fintype Z]
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (k j : ℕ) :
    MemLp (meanValue e.Jplus k j) 2 (xLaw M) := by
  have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  have hJ : Measurable (meanValue e.Jplus k j) := by fun_prop
  apply MemLp.of_bound hJ.aestronglyMeasurable (|M.yMin| + |M.yMax|)
  simpa only [Real.norm_eq_abs] using
    (continuous_admissible_band_means_abs_bound M L e he k j).1

-- @node: fitted_continuous_alphaHigh_memLp
/-- If [the continuous nuisance record is admissible](hyp:he), then [its upper propensity representer is square integrable under the covariate law](goal). -/
lemma fitted_continuous_alphaHigh_memLp [Fintype Z]
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (k j : ℕ) :
    MemLp (alphaHigh M L e k j) 2 (xLaw M) := by
  exact ((fitted_continuous_meanValue_memLp M L e he k j).add
    (fitted_continuous_quantile_boundary_product_memLp M L e he k j)).sub
    (fitted_continuous_quantile_boundary_product_memLp M L e he k (j+1))

-- @node: encoded_continuous_alphaHigh_sq_tendsto_probability_zero
/-- If [the true nuisance record is admissible](hyp:he0), [the fitted records satisfy continuous clipping](hyp:hclip), [their shares lie in the simplex](hyp:hshares), [their encoded coordinates are measurable](hyp:hm), and [those coordinates satisfy the finite nuisance rates toward truth](hyp:hr), then [the population integrated squared error of the upper propensity representer at even sample sizes converges in probability to zero](goal). -/
lemma encoded_continuous_alphaHigh_sq_tendsto_probability_zero [Fintype Z]
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L))) (k j : ℕ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (alphaHigh M L (eh (2*(n+1)) t) k j x -
        alphaHigh M L (trueNuisance M L) k j x)^2 ∂xLaw M)
      atTop (fun _ _ => 0) := by
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  let J := fun (e : NuisanceCont L) => meanValue e.Jplus k j
  let P := fun (b : ℕ) (e : NuisanceCont L) x =>
    nuValue M e k b x * boundaryValue e.Mplus k b x
  let F := fun n t x => J (er (2*(n+1)) t) x - J (trueNuisance M L) x
  let G := fun b n t x => P b (er (2*(n+1)) t) x - P b (trueNuisance M L) x
  have hJ (e : NuisanceCont L) (he : ContAdmissible M L e) : MemLp (J e) 2 (xLaw M) :=
    fitted_continuous_meanValue_memLp M L e he k j
  have hF n t := (hJ _ (her (2*(n+1)) t)).sub (hJ _ he0)
  have hG b n t := (fitted_continuous_quantile_boundary_product_memLp M L _
    (her (2*(n+1)) t) k b).sub
    (fitted_continuous_quantile_boundary_product_memLp M L _ he0 k b)
  let z0 : Z := Classical.choice inferInstance
  have hrF : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (F n t x)^2 ∂xLaw M) atTop (fun _ _ => 0) := by
    simpa only [F, J, er, restrictContShares, contComponent, nuValue] using
      nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hr (11,k,j,z0)
  have hrG b : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (G b n t x)^2 ∂xLaw M) atTop (fun _ _ => 0) := by
    simpa only [G, P, er, restrictContShares, nuValue] using
      encoded_continuous_quantile_boundary_product_sq_tendsto_probability_zero
        M μ L he0 eh hclip hshares hm hr k b
  have hs := dml_three_term_sq_tendsto_probability_zero μ (xLaw M)
    F (G j) (G (j+1)) hF (hG j) (hG (j+1)) hrF (hrG j) (hrG (j+1))
  convert hs using 1
  funext n t
  congr 1
  funext x
  simp only [F, G, J, P, er, restrictContShares, alphaHigh, nuValue]
  ring

-- @node: continuous_admissible_minusBoundaryValue_coordinates
/-- If [the continuous nuisance record is admissible](hyp:he), then [its lower boundary-mean coordinate is measurable and has absolute value at most one almost everywhere under the covariate law](goal). -/
lemma continuous_admissible_minusBoundaryValue_coordinates [Fintype Z]
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (k j : ℕ) :
    Measurable (minusBoundaryValue e.Mminus k j) ∧
      (∀ᵐ x ∂xLaw M, |minusBoundaryValue e.Mminus k j x| ≤ 1) := by
  rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hb, hm, _⟩
  unfold minusBoundaryValue
  split_ifs with hj hlast
  · refine ⟨by first | fun_prop | exact hm _, ?_⟩
    filter_upwards [hb ⟨(k,j), hj⟩] with x hx
    simpa only [abs_of_nonneg hx.1] using hx.2
  · exact ⟨measurable_const, Eventually.of_forall (by simp)⟩
  · exact ⟨measurable_const, Eventually.of_forall (by simp)⟩

-- @node: fitted_continuous_quantile_minus_boundary_product_memLp
/-- If [the continuous nuisance record is admissible](hyp:he), then [the product of its quantile and lower boundary-mean coordinates is square integrable under the covariate law](goal). -/
lemma fitted_continuous_quantile_minus_boundary_product_memLp [Fintype Z]
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (k j : ℕ) :
    MemLp (fun x => nuValue M e k j x * minusBoundaryValue e.Mminus k j x)
      2 (xLaw M) := by
  have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  obtain ⟨hm, hb⟩ := continuous_admissible_minusBoundaryValue_coordinates M L e he k j
  have hn := continuous_admissible_nuValue_measurable M L e he k j
  apply MemLp.of_bound (by fun_prop) (|M.yMin| + |M.yMax|)
  filter_upwards [hb, continuous_admissible_nuValue_abs_bound M L e he k j] with x hx hy
  rw [Real.norm_eq_abs, abs_mul]
  exact (mul_le_mul hy hx (abs_nonneg _) (by positivity)).trans_eq (mul_one _)

-- No density assumption is required for these smooth boundary-mean products.
-- @node: encoded_continuous_quantile_minus_boundary_product_sq_tendsto_probability_zero
/-- If [the true nuisance record is admissible](hyp:he0), [all fitted records satisfy continuous clipping](hyp:hclip), [their shares lie in the simplex](hyp:hshares), [their encoded coordinates are measurable](hyp:hm), and [those coordinates satisfy the finite nuisance rates toward truth](hyp:hr), then [the population integrated squared error of the quantile times lower boundary-mean product, evaluated at even sample sizes, converges in probability to zero](goal). -/
lemma encoded_continuous_quantile_minus_boundary_product_sq_tendsto_probability_zero [Fintype Z]
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L))) (k j : ℕ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x,
        (nuValue M (eh (2*(n+1)) t) k j x * minusBoundaryValue (eh (2*(n+1)) t).Mminus k j x -
          nuValue M (trueNuisance M L) k j x * minusBoundaryValue (trueNuisance M L).Mminus k j x)^2
        ∂xLaw M) atTop (fun _ _ => 0) := by
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  let N := fun (e : NuisanceCont L) => nuValue M e k j
  let B := fun (e : NuisanceCont L) => minusBoundaryValue e.Mminus k j
  have hN (e : NuisanceCont L) (he : ContAdmissible M L e) :
      Measurable (N e) ∧ (∀ᵐ x ∂xLaw M, |N e x| ≤ |M.yMin| + |M.yMax|) :=
    ⟨continuous_admissible_nuValue_measurable M L e he k j,
      continuous_admissible_nuValue_abs_bound M L e he k j⟩
  have hB (e : NuisanceCont L) (he : ContAdmissible M L e) :=
    continuous_admissible_minusBoundaryValue_coordinates M L e he k j
  have hmem (f : X → ℝ) (hf : Measurable f) (R : ℝ)
      (hb : ∀ᵐ x ∂xLaw M, |f x| ≤ R) : MemLp f 2 (xLaw M) :=
    MemLp.of_bound hf.aestronglyMeasurable R (by simpa only [Real.norm_eq_abs] using hb)
  let z0 : Z := Classical.choice inferInstance
  have hrN : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (N (er (2*(n+1)) t) x - N (trueNuisance M L) x)^2
        ∂xLaw M) atTop (fun _ _ => 0) := by
    simpa only [N, er, restrictContShares, contComponent, nuValue] using
      nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hr (8,k,j,z0)
  have hrB : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (B (er (2*(n+1)) t) x - B (trueNuisance M L) x)^2
        ∂xLaw M) atTop (fun _ _ => 0) := by
    simpa only [B, er, restrictContShares, contComponent, nuValue] using
      nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hr (10,k,j,z0)
  have hs := dml_weighted_residual_sq_tendsto_probability_zero μ (xLaw M)
    (N (trueNuisance M L)) (B (trueNuisance M L))
    (fun n t => N (er (2*(n+1)) t)) (fun n t => B (er (2*(n+1)) t))
    (|M.yMin| + |M.yMax|) 1 (hN _ he0).1 (hB _ he0).1
    (fun n t => (hN _ (her _ t)).1) (fun n t => (hB _ (her _ t)).1)
    (fun n t => (hmem _ (hN _ (her _ t)).1 _ (hN _ (her _ t)).2).sub
      (hmem _ (hN _ he0).1 _ (hN _ he0).2))
    (fun n t => (hmem _ (hB _ (her _ t)).1 _ (hB _ (her _ t)).2).sub
      (hmem _ (hB _ he0).1 _ (hB _ he0).2))
    (fun n t => (hN _ (her _ t)).2) (fun _ _ => (hB _ he0).2) hrN hrB
  simpa only [N, B, er, restrictContShares, nuValue] using hs

-- @node: fitted_continuous_minusMeanValue_memLp
/-- If [the continuous nuisance record is admissible](hyp:he), then [its lower band-mean coordinate is square integrable under the covariate law](goal). -/
lemma fitted_continuous_minusMeanValue_memLp [Fintype Z]
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (k j : ℕ) :
    MemLp (minusMeanValue e.Jminus k j) 2 (xLaw M) := by
  have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  have hJ : Measurable (minusMeanValue e.Jminus k j) := by
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, hm, _⟩
    unfold minusMeanValue
    split_ifs <;> fun_prop
  apply MemLp.of_bound hJ.aestronglyMeasurable (|M.yMin| + |M.yMax|)
  simpa only [Real.norm_eq_abs] using
    (continuous_admissible_band_means_abs_bound M L e he k j).2


-- @node: fitted_continuous_alphaLow_memLp
/-- If [the continuous nuisance record is admissible](hyp:he), then [its lower propensity representer is square integrable under the covariate law](goal). -/
lemma fitted_continuous_alphaLow_memLp [Fintype Z]
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (k j : ℕ) :
    MemLp (alphaLow M L e k j) 2 (xLaw M) := by
  have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  have hn b : MemLp (nuValue M e k b) 2 (xLaw M) := by
    apply MemLp.of_bound (by fun_prop) (|M.yMin| + |M.yMax|)
    simpa only [Real.norm_eq_abs] using
      continuous_admissible_nuValue_abs_bound M L e he k b
  exact (((((fitted_continuous_minusMeanValue_memLp M L e he k j).neg).sub
    (fitted_continuous_quantile_minus_boundary_product_memLp M L e he k j)).add
    (fitted_continuous_quantile_minus_boundary_product_memLp M L e he k (j+1))).add
    ((hn j).const_mul (indicator (1 ≤ j)))).sub (hn (j+1))

-- @node: encoded_continuous_alphaLow_sq_tendsto_probability_zero
/-- If [the true nuisance record is admissible](hyp:he0), [the fitted records satisfy continuous clipping](hyp:hclip), [their shares lie in the simplex](hyp:hshares), [their encoded coordinates are measurable](hyp:hm), and [those coordinates satisfy the finite nuisance rates toward truth](hyp:hr), then [the population integrated squared error of the lower propensity representer at even sample sizes converges in probability to zero](goal). -/
lemma encoded_continuous_alphaLow_sq_tendsto_probability_zero [Fintype Z]
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L))) (k j : ℕ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (alphaLow M L (eh (2*(n+1)) t) k j x -
        alphaLow M L (trueNuisance M L) k j x)^2 ∂xLaw M)
      atTop (fun _ _ => 0) := by
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  let P := fun (b : ℕ) (e : NuisanceCont L) x =>
    nuValue M e k b x * minusBoundaryValue e.Mminus k b x
  let piece := fun (e : NuisanceCont L) (i : Fin 5) (x : X) =>
    match i.val with
    | 0 => -minusMeanValue e.Jminus k j x
    | 1 => -P j e x
    | 2 => P (j+1) e x
    | 3 => indicator (1 ≤ j) * nuValue M e k j x
    | _ => -nuValue M e k (j+1) x
  have hn (e : NuisanceCont L) (he : ContAdmissible M L e) b :
      MemLp (nuValue M e k b) 2 (xLaw M) := by
    apply MemLp.of_bound (by fun_prop) (|M.yMin| + |M.yMax|)
    simpa only [Real.norm_eq_abs] using
      continuous_admissible_nuValue_abs_bound M L e he k b
  have hp (e : NuisanceCont L) (he : ContAdmissible M L e) (i : Fin 5) :
      MemLp (piece e i) 2 (xLaw M) := by
    fin_cases i
    · exact (fitted_continuous_minusMeanValue_memLp M L e he k j).neg
    · exact (fitted_continuous_quantile_minus_boundary_product_memLp M L e he k j).neg
    · exact fitted_continuous_quantile_minus_boundary_product_memLp M L e he k (j+1)
    · exact (hn e he j).const_mul (indicator (1 ≤ j))
    · exact (hn e he (j+1)).neg
  let z0 : Z := Classical.choice inferInstance
  have hrnu b : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (nuValue M (er (2*(n+1)) t) k b x -
        nuValue M (trueNuisance M L) k b x)^2 ∂xLaw M) atTop (fun _ _ => 0) := by
    simpa only [er, restrictContShares, contComponent, nuValue] using
      nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hr (8,k,b,z0)
  have hrP b : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (P b (er (2*(n+1)) t) x - P b (trueNuisance M L) x)^2
        ∂xLaw M) atTop (fun _ _ => 0) := by
    simpa only [P, er, restrictContShares, nuValue] using
      encoded_continuous_quantile_minus_boundary_product_sq_tendsto_probability_zero
        M μ L he0 eh hclip hshares hm hr k b
  have hrpiece (i : Fin 5) : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (piece (er (2*(n+1)) t) i x -
        piece (trueNuisance M L) i x)^2 ∂xLaw M) atTop (fun _ _ => 0) := by
    fin_cases i
    · simpa only [piece, neg_sub_neg, sub_sq_comm, er, restrictContShares, contComponent] using
        nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hr (12,k,j,z0)
    · simpa only [piece, neg_sub_neg, sub_sq_comm] using hrP j
    · exact hrP (j+1)
    · by_cases hj : 1 ≤ j
      · simpa only [piece, indicator, if_pos hj, one_mul] using hrnu j
      · simp only [piece, indicator, if_neg hj, zero_mul, sub_self,
          zero_pow (by norm_num : 2 ≠ 0), integral_zero]
        rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
        intro eps heps
        simpa [not_le_of_gt heps] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
    · simpa only [piece, neg_sub_neg, sub_sq_comm] using hrnu (j+1)
  have hs := dml_finset_sum_sq_tendsto_probability_zero μ (xLaw M) Finset.univ
    (fun i n t x => piece (er (2*(n+1)) t) i x - piece (trueNuisance M L) i x)
    (fun i _ n t => (hp _ (her _ t) i).sub (hp _ he0 i)) (fun i _ => hrpiece i)
  have hsum (e : NuisanceCont L) x : (∑ i : Fin 5, piece e i x) = alphaLow M L e k j x := by
    simp [Fin.sum_univ_succ, piece, P, alphaLow]
    ring
  simpa only [Finset.sum_sub_distrib, hsum, er, restrictContShares, alphaLow, nuValue] using hs

end Papers.TbsPrteOptimalTransport
