module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousBoundaryProducts
/-! Quantile-weighted boundary contrasts in the continuous fractional score.
The clipped quantile and boundary probabilities have bounded second moments;
their product converges using the encoded rates and boundary-product convergence. -/
@[expose] public section
set_option linter.style.haveILetI false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
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
  [Fintype Z]

-- @node: continuousQuantileBoundaryContrast
/-- For [a latent instrumental-variable model](hyp:M), [a level and band
specification](hyp:L), [continuous nuisance functions](hyp:e), [a level index](hyp:k),
[a boundary index](hyp:j), and [covariates](hyp:x), the [quantile-weighted boundary
contrast](goal) is the boundary quantile times the difference between the next-level
probability weighted by the upper boundary probability and the current-level
probability weighted by the lower boundary probability. -/
noncomputable def continuousQuantileBoundaryContrast (M : LatentIVModel Ω X Z)
    (L : LevelData Z X) (e : NuisanceCont L) (k j : ℕ) (x : X) : ℝ :=
  nuValue M e k j x * (positiveValue e.pLev (k+1) x * boundaryValue e.Mplus k j x -
    positiveValue e.pLev k x * minusBoundaryValue e.Mminus k j x)

-- @node: fitted_continuous_boundary_contrast_measurable
/-- If [the continuous nuisances are admissible](hyp:he), then [the difference between
the next-level probability times the upper boundary probability and the current-level
probability times the lower boundary probability is measurable in covariates, for
every level and boundary index](goal). -/
@[fun_prop] lemma fitted_continuous_boundary_contrast_measurable
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (k j : ℕ) :
    Measurable (fun x => positiveValue e.pLev (k+1) x * boundaryValue e.Mplus k j x -
      positiveValue e.pLev k x * minusBoundaryValue e.Mminus k j x) := by
  first | fun_prop | skip
  have hp := (fitted_continuous_full_coordinates M L e he (k+1)).1.1
  have hp' := (fitted_continuous_full_coordinates M L e he k).1.1
  have hb := continuous_admissible_boundary_values_regular M L e he k j
  exact (hp.mul hb.1.1).sub (hp'.mul hb.2.1)

-- @node: fitted_continuous_boundary_contrast_abs_bound
/-- If [the continuous nuisances are admissible](hyp:he), then [the absolute difference
between the next-level probability times the upper boundary probability and the
current-level probability times the lower boundary probability is at most two almost
everywhere under the covariate law, for every level and boundary index](goal). -/
lemma fitted_continuous_boundary_contrast_abs_bound
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (k j : ℕ) :
    ∀ᵐ x ∂xLaw M, |positiveValue e.pLev (k+1) x * boundaryValue e.Mplus k j x -
      positiveValue e.pLev k x * minusBoundaryValue e.Mminus k j x| ≤ 2 := by
  have hp := (fitted_continuous_full_coordinates M L e he (k+1)).1.2
  have hp' := (fitted_continuous_full_coordinates M L e he k).1.2
  have hb := continuous_admissible_boundary_values_regular M L e he k j
  filter_upwards [hp, hp', hb.1.2, hb.2.2] with x hx hx' hy hy'
  apply (abs_sub _ _).trans
  rw [abs_mul, abs_mul]
  have hplus := mul_le_mul hx hy (abs_nonneg _) zero_le_one
  have hminus := mul_le_mul hx' hy' (abs_nonneg _) zero_le_one
  norm_num at hplus hminus
  linarith

-- @node: fitted_continuous_quantile_boundary_contrast_memLp
/-- If [the continuous nuisances are admissible](hyp:he), then [the quantile-weighted
boundary contrast at any level and boundary index has a finite second moment under
the covariate law](goal). -/
lemma fitted_continuous_quantile_boundary_contrast_memLp
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (k j : ℕ) :
    MemLp (continuousQuantileBoundaryContrast M L e k j) 2 (xLaw M) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  have hn := continuous_admissible_nuValue_measurable M L e he k j
  have hb := fitted_continuous_boundary_contrast_measurable M L e he k j
  unfold continuousQuantileBoundaryContrast
  apply MemLp.of_bound (by fun_prop) ((|M.yMin| + |M.yMax|) * 2)
  filter_upwards [continuous_admissible_nuValue_abs_bound M L e he k j,
    fitted_continuous_boundary_contrast_abs_bound M L e he k j] with x hx hy
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) (by positivity)

-- @node: encoded_continuous_quantile_boundary_contrast_sq_tendsto_probability_zero
/-- Suppose [the true continuous nuisances are admissible](hyp:he0), and [a sequence
of fitted continuous nuisances](hyp:eh) obeys [clipping at every sample index and
realization](hyp:hclip), [the fitted-share simplex restrictions](hyp:hshares),
[measurability of every encoded coordinate](hyp:hm), and [the finite nuisance rate
conditions relative to truth](hyp:hr). Then [the covariate-law integrated squared
error of the quantile-weighted boundary contrast at any fixed level and boundary,
evaluated at sample indices twice one plus the sequence index, converges to zero in
probability under the fitting measure](goal). -/
lemma encoded_continuous_quantile_boundary_contrast_sq_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L))) (k j : ℕ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (continuousQuantileBoundaryContrast M L (eh (2*(n+1)) t) k j x -
        continuousQuantileBoundaryContrast M L (trueNuisance M L) k j x)^2 ∂xLaw M)
      atTop (fun _ _ => 0) := by
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  let N := fun (e : NuisanceCont L) => nuValue M e k j
  let B := fun (e : NuisanceCont L) x =>
    positiveValue e.pLev (k+1) x * boundaryValue e.Mplus k j x -
      positiveValue e.pLev k x * minusBoundaryValue e.Mminus k j x
  have hN (e : NuisanceCont L) (he : ContAdmissible M L e) :
      Measurable (N e) ∧ ∀ᵐ x ∂xLaw M, |N e x| ≤ |M.yMin| + |M.yMax| :=
    ⟨continuous_admissible_nuValue_measurable M L e he k j,
      continuous_admissible_nuValue_abs_bound M L e he k j⟩
  have hB (e : NuisanceCont L) (he : ContAdmissible M L e) :
      Measurable (B e) ∧ ∀ᵐ x ∂xLaw M, |B e x| ≤ 2 :=
    ⟨fitted_continuous_boundary_contrast_measurable M L e he k j,
      fitted_continuous_boundary_contrast_abs_bound M L e he k j⟩
  have hmem (f : X → ℝ) (hf : Measurable f) (R : ℝ)
      (hb : ∀ᵐ x ∂xLaw M, |f x| ≤ R) : MemLp f 2 (xLaw M) :=
    MemLp.of_bound hf.aestronglyMeasurable R (by simpa only [Real.norm_eq_abs] using hb)
  let z0 : Z := Classical.choice inferInstance
  have hrN : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (N (er (2*(n+1)) t) x - N (trueNuisance M L) x)^2 ∂xLaw M)
      atTop (fun _ _ => 0) := by
    simpa only [N, er, restrictContShares, contComponent, nuValue] using
      nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hr (8,k,j,z0)
  have hrB : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (B (er (2*(n+1)) t) x - B (trueNuisance M L) x)^2 ∂xLaw M)
      atTop (fun _ _ => 0) := by
    simpa only [B, er, restrictContShares] using
      encoded_continuous_boundary_contrast_sq_tendsto_probability_zero
        M μ L he0 eh hclip hshares hm hr k j
  have hs := dml_weighted_residual_sq_tendsto_probability_zero μ (xLaw M)
    (N (trueNuisance M L)) (B (trueNuisance M L))
    (fun n t => N (er (2*(n+1)) t)) (fun n t => B (er (2*(n+1)) t))
    (|M.yMin| + |M.yMax|) 2 (hN _ he0).1 (hB _ he0).1
    (fun n t => (hN _ (her _ t)).1) (fun n t => (hB _ (her _ t)).1)
    (fun n t => (hmem _ (hN _ (her _ t)).1 _ (hN _ (her _ t)).2).sub
      (hmem _ (hN _ he0).1 _ (hN _ he0).2))
    (fun n t => (fitted_continuous_boundary_contrast_memLp M L _ (her _ t) k j).sub
      (fitted_continuous_boundary_contrast_memLp M L _ he0 k j))
    (fun n t => (hN _ (her _ t)).2) (fun _ _ => (hB _ he0).2) hrN hrB
  simpa only [N, B, er, restrictContShares, continuousQuantileBoundaryContrast, nuValue] using hs

-- @node: encoded_continuous_quantile_boundary_contrast_l2_tendsto_probability_zero
/-- Given [admissible true continuous nuisances](hyp:he0), suppose [the fitted nuisance
sequence](hyp:eh) satisfies [clipping](hyp:hclip), [the fitted-share simplex
restrictions](hyp:hshares), [measurability of all encoded coordinates](hyp:hm), and
[the finite nuisance rate conditions relative to truth](hyp:hr). Then [the square
root of the covariate-law integrated squared error of the quantile-weighted boundary
contrast, for any fixed level and boundary at sample indices twice one plus the
sequence index, converges to zero in probability under the fitting measure](goal). -/
lemma encoded_continuous_quantile_boundary_contrast_l2_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L))) (k j : ℕ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => Real.sqrt (∫ x,
        (continuousQuantileBoundaryContrast M L (eh (2*(n+1)) t) k j x -
          continuousQuantileBoundaryContrast M L (trueNuisance M L) k j x)^2 ∂xLaw M))
      atTop (fun _ _ => 0) := by
  have hs := encoded_continuous_quantile_boundary_contrast_sq_tendsto_probability_zero
    M μ L he0 eh hclip hshares hm hr k j
  have hc : Continuous (fun t : ℝ => Real.sqrt t) := by fun_prop
  simpa only [Real.sqrt_zero] using
    Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt hc.continuousAt hs

-- @node: continuousQuantileBoundaryContrast_measurable
/-- If [the continuous nuisances are admissible](hyp:he), then [the quantile-weighted
boundary contrast at every level and boundary index is measurable in covariates](goal). -/
@[fun_prop] lemma continuousQuantileBoundaryContrast_measurable
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (k j : ℕ) :
    Measurable (continuousQuantileBoundaryContrast M L e k j) := by
  first | fun_prop | skip
  unfold continuousQuantileBoundaryContrast
  exact (continuous_admissible_nuValue_measurable M L e he k j).mul
    (fitted_continuous_boundary_contrast_measurable M L e he k j)

-- @node: continuousQuantileBoundaryContrast_abs_bound
/-- If [the continuous nuisances are admissible](hyp:he), then [the absolute
quantile-weighted boundary contrast is at most twice the sum of the absolute lower
and upper outcome bounds, almost everywhere under the covariate law, for every
level and boundary index](goal). -/
lemma continuousQuantileBoundaryContrast_abs_bound
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (k j : ℕ) :
    ∀ᵐ x ∂xLaw M, |continuousQuantileBoundaryContrast M L e k j x| ≤
      (|M.yMin| + |M.yMax|) * 2 := by
  filter_upwards [continuous_admissible_nuValue_abs_bound M L e he k j,
    fitted_continuous_boundary_contrast_abs_bound M L e he k j] with x hx hy
  simp only [continuousQuantileBoundaryContrast, abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) (by positivity)

-- @node: fitted_continuous_gamma_quantile_boundary_contrast_memLp
/-- If [the continuous nuisances are admissible](hyp:he), then [the product of any
regular band's gamma weight and any quantile-weighted boundary contrast has a finite
second moment under the covariate law](goal). -/
lemma fitted_continuous_gamma_quantile_boundary_contrast_memLp
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) (g : RegularIndex L) (k j : ℕ) :
    MemLp (fun x => e.gamma g x * continuousQuantileBoundaryContrast M L e k j x)
      2 (xLaw M) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  have hgm : Measurable (e.gamma g) := by
    first | fun_prop | skip
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hm, _⟩
    exact hm g
  have hgb : ∀ᵐ x ∂xLaw M, |e.gamma g x| ≤ 1 := by
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hb, _⟩
    filter_upwards [hb g] with x hx
    simpa only [abs_of_nonneg hx.1] using hx.2
  have hq := continuousQuantileBoundaryContrast_measurable M L e he k j
  apply MemLp.of_bound (by fun_prop) ((|M.yMin| + |M.yMax|) * 2)
  filter_upwards [hgb, continuousQuantileBoundaryContrast_abs_bound M L e he k j] with x hx hy
  rw [Real.norm_eq_abs, abs_mul]
  exact (mul_le_mul hx hy (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

-- @node: encoded_continuous_gamma_quantile_boundary_contrast_sq_tendsto_probability_zero
/-- Suppose [the true continuous nuisances are admissible](hyp:he0), and [the fitted
nuisance sequence](hyp:eh) satisfies [clipping](hyp:hclip), [the fitted-share simplex
restrictions](hyp:hshares), [measurability of all encoded coordinates](hyp:hm), and
[the finite nuisance rate conditions relative to truth](hyp:hr). Then [the covariate-law
integrated squared error of any fixed regular band's gamma weight times any fixed
quantile-weighted boundary contrast, at sample indices twice one plus the sequence
index, converges to zero in probability under the fitting measure](goal). -/
lemma encoded_continuous_gamma_quantile_boundary_contrast_sq_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L))) (g : RegularIndex L) (k j : ℕ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x,
        ((eh (2*(n+1)) t).gamma g x *
            continuousQuantileBoundaryContrast M L (eh (2*(n+1)) t) k j x -
          (trueNuisance M L).gamma g x *
            continuousQuantileBoundaryContrast M L (trueNuisance M L) k j x)^2 ∂xLaw M)
      atTop (fun _ _ => 0) := by
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  have hG (e : NuisanceCont L) (he : ContAdmissible M L e) :
      Measurable (e.gamma g) ∧ ∀ᵐ x ∂xLaw M, |e.gamma g x| ≤ 1 := by
    have hgm : Measurable (e.gamma g) := by
      first | fun_prop | skip
      rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hm, _⟩
      exact hm g
    refine ⟨hgm, ?_⟩
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hb, _⟩
    filter_upwards [hb g] with x hx
    simpa only [abs_of_nonneg hx.1] using hx.2
  have hmem (e : NuisanceCont L) (he : ContAdmissible M L e) :
      MemLp (e.gamma g) 2 (xLaw M) :=
    MemLp.of_bound (hG e he).1.aestronglyMeasurable 1
      (by simpa only [Real.norm_eq_abs] using (hG e he).2)
  let z0 : Z := Classical.choice inferInstance
  have hrG : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, ((er (2*(n+1)) t).gamma g x -
        (trueNuisance M L).gamma g x)^2 ∂xLaw M) atTop (fun _ _ => 0) := by
    have hg := g.property
    simpa only [contComponent, regularValue, dif_pos hg, er, restrictContShares] using
      nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hr (6,g.val.1,g.val.2,z0)
  have hrQ : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x,
        (continuousQuantileBoundaryContrast M L (er (2*(n+1)) t) k j x -
          continuousQuantileBoundaryContrast M L (trueNuisance M L) k j x)^2 ∂xLaw M)
      atTop (fun _ _ => 0) := by
    simpa only [er, continuousQuantileBoundaryContrast, restrictContShares, nuValue] using
      encoded_continuous_quantile_boundary_contrast_sq_tendsto_probability_zero
        M μ L he0 eh hclip hshares hm hr k j
  have hs := dml_weighted_residual_sq_tendsto_probability_zero μ (xLaw M)
    ((trueNuisance M L).gamma g) (continuousQuantileBoundaryContrast M L (trueNuisance M L) k j)
    (fun n t => (er (2*(n+1)) t).gamma g)
    (fun n t => continuousQuantileBoundaryContrast M L (er (2*(n+1)) t) k j)
    1 ((|M.yMin| + |M.yMax|) * 2) (hG _ he0).1
    (continuousQuantileBoundaryContrast_measurable M L _ he0 k j)
    (fun n t => (hG _ (her _ t)).1)
    (fun n t => continuousQuantileBoundaryContrast_measurable M L _ (her _ t) k j)
    (fun n t => (hmem _ (her _ t)).sub (hmem _ he0))
    (fun n t => (fitted_continuous_quantile_boundary_contrast_memLp M L _ (her _ t) k j).sub
      (fitted_continuous_quantile_boundary_contrast_memLp M L _ he0 k j))
    (fun n t => (hG _ (her _ t)).2)
    (fun _ _ => continuousQuantileBoundaryContrast_abs_bound M L _ he0 k j) hrG hrQ
  simpa only [er, continuousQuantileBoundaryContrast, restrictContShares, nuValue] using hs

-- @node: continuousQuantileBoundaryBlock
/-- For [a latent instrumental-variable model](hyp:M), [a level and band
specification](hyp:L), [continuous nuisance functions](hyp:e), and [an observation](hyp:o),
the [quantile boundary block](goal) sums over nonterminal levels and their bands the
band's gamma weight times its lower-endpoint quantile-weighted boundary contrast
minus its upper-endpoint contrast, evaluated at the observation's covariates. -/
noncomputable def continuousQuantileBoundaryBlock (M : LatentIVModel Ω X Z)
    (L : LevelData Z X) (e : NuisanceCont L) (o : Obs X Z) : ℝ :=
  ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
    regularValue e.gamma k j o.1 *
      (continuousQuantileBoundaryContrast M L e k (j-1) o.1 -
        continuousQuantileBoundaryContrast M L e k j o.1)

-- @node: fitted_continuous_quantile_boundary_block_memLp
/-- If [the continuous nuisances are admissible](hyp:he), then [the quantile boundary
block has a finite second moment under the observation law](goal). -/
lemma fitted_continuous_quantile_boundary_block_memLp
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) :
    MemLp (continuousQuantileBoundaryBlock M L e) 2 (observationLaw M) := by
  unfold continuousQuantileBoundaryBlock
  apply memLp_finsetSum
  intro k hk
  apply memLp_finsetSum
  intro j hj
  have hg : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k :=
    ⟨(Finset.mem_range.mp hk).le, Finset.mem_Icc.mp hj⟩
  have h := ((fitted_continuous_gamma_quantile_boundary_contrast_memLp M L e he
    ⟨(k,j),hg⟩ k (j-1)).sub
    (fitted_continuous_gamma_quantile_boundary_contrast_memLp M L e he
      ⟨(k,j),hg⟩ k j)).comp_measurePreserving (observationLaw_fst_measurePreserving M)
  convert h using 1
  funext o
  simp only [Function.comp_apply, Pi.sub_apply, regularValue, dif_pos hg]
  ring

-- @node: encoded_continuous_quantile_boundary_block_sq_tendsto_probability_zero
/-- Suppose [the true continuous nuisances are admissible](hyp:he0), and [a fitted
nuisance sequence](hyp:eh) satisfies [clipping](hyp:hclip), [the fitted-share simplex
restrictions](hyp:hshares), [measurability of every encoded coordinate](hyp:hm), and
[the finite nuisance rate conditions relative to truth](hyp:hr). Then [the observation-law
integrated squared error of the quantile boundary block at sample indices twice one
plus the sequence index converges to zero in probability under the fitting measure](goal). -/
lemma encoded_continuous_quantile_boundary_block_sq_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L))) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o : Obs X Z,
        (continuousQuantileBoundaryBlock M L (eh (2*(n+1)) t) o -
          continuousQuantileBoundaryBlock M L (trueNuisance M L) o)^2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  let F := fun k j b n t x => regularValue (er (2*(n+1)) t).gamma k j x *
    continuousQuantileBoundaryContrast M L (er (2*(n+1)) t) k b x -
    regularValue (trueNuisance M L).gamma k j x *
      continuousQuantileBoundaryContrast M L (trueNuisance M L) k b x
  have hF k j b n t (hg : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k) :
      MemLp (F k j b n t) 2 (xLaw M) := by
    simpa only [F, regularValue, dif_pos hg, Pi.sub_def] using
      (fitted_continuous_gamma_quantile_boundary_contrast_memLp M L _ (her _ t)
        ⟨(k,j),hg⟩ k b).sub
      (fitted_continuous_gamma_quantile_boundary_contrast_memLp M L _ he0 ⟨(k,j),hg⟩ k b)
  have hFm k j b n t (hg : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k) :
      Measurable (F k j b n t) := by
    have hgm (e : NuisanceCont L) (he : ContAdmissible M L e) :
        Measurable (regularValue e.gamma k j) := by
      first | fun_prop | skip
      rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hm, _⟩
      change Measurable (fun x => regularValue e.gamma k j x)
      simpa only [regularValue, dif_pos hg] using hm ⟨(k,j),hg⟩
    have hgh := hgm _ (her (2*(n+1)) t)
    have hg0 := hgm _ he0
    have hqh := continuousQuantileBoundaryContrast_measurable M L _ (her (2*(n+1)) t) k b
    have hq0 := continuousQuantileBoundaryContrast_measurable M L _ he0 k b
    dsimp only [F]
    fun_prop
  have hrF k j b (hg : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k) :
      Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
        (fun n t => ∫ x, (F k j b n t x)^2 ∂xLaw M) atTop (fun _ _ => 0) := by
    simpa only [F, er, regularValue, dif_pos hg, continuousQuantileBoundaryContrast,
      restrictContShares, nuValue] using
      encoded_continuous_gamma_quantile_boundary_contrast_sq_tendsto_probability_zero
        M μ L he0 eh hclip hshares hm hr ⟨(k,j),hg⟩ k b
  have hz : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun (_ : ℕ) (_ : A) => (0 : ℝ)) atTop (fun _ _ => 0) := by
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
    intro eps heps
    simpa [not_le_of_gt heps] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
  let D := fun k j n t x => F k j (j-1) n t x + 0 - F k j j n t x
  have hD k j n t (hg : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k) :
      MemLp (D k j n t) 2 (xLaw M) := by
    simpa only [D, add_zero, Pi.sub_def] using (hF k j (j-1) n t hg).sub (hF k j j n t hg)
  have hrD k j (hg : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k) :=
    dml_three_term_sq_tendsto_probability_zero μ (xLaw M)
      (F k j (j-1)) (fun _ _ _ => 0) (F k j j) (fun n t => hF k j (j-1) n t hg)
      (fun _ _ => MemLp.zero') (fun n t => hF k j j n t hg)
      (hrF k j (j-1) hg) (by simpa using hz) (hrF k j j hg)
  have hs := dml_finset_sum_sq_tendsto_probability_zero μ (xLaw M)
    (Finset.range L.K) (fun k n t x => ∑ j ∈ Finset.Icc 1 (L.l k), D k j n t x)
    (fun k hk n t => memLp_finsetSum _ (fun j hj =>
      hD k j n t ⟨(Finset.mem_range.mp hk).le, Finset.mem_Icc.mp hj⟩)) (by
      intro k hk
      apply dml_finset_sum_sq_tendsto_probability_zero μ (xLaw M)
        (Finset.Icc 1 (L.l k)) (D k)
        (fun j hj n t => hD k j n t ⟨(Finset.mem_range.mp hk).le, Finset.mem_Icc.mp hj⟩)
      intro j hj
      exact hrD k j ⟨(Finset.mem_range.mp hk).le, Finset.mem_Icc.mp hj⟩)
  have hid n t (o : Obs X Z) :
      (∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k), D k j n t o.1) =
      continuousQuantileBoundaryBlock M L (eh (2*(n+1)) t) o -
        continuousQuantileBoundaryBlock M L (trueNuisance M L) o := by
    simp only [D, F, continuousQuantileBoundaryBlock, er, restrictContShares,
      continuousQuantileBoundaryContrast, nuValue, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro j hj
    ring
  -- Covariate-only block: push its squared error through the observation law.
  have hi n t := observationLaw_covariate_integral M
    (fun x => (∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k), D k j n t x)^2)
    (by
      first | fun_prop | skip
      apply Measurable.pow_const
      apply Finset.measurable_sum
      intro k hk
      apply Finset.measurable_sum
      intro j hj
      have hg : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k :=
        ⟨(Finset.mem_range.mp hk).le, Finset.mem_Icc.mp hj⟩
      dsimp only [D]
      exact ((hFm k j (j-1) n t hg).add measurable_const).sub (hFm k j j n t hg))
  convert hs using 1
  funext n t
  rw [← hi n t]
  congr 1
  funext o
  rw [hid]

-- @node: continuous_fractional_quantile_moment_boundary_decomposition
/-- [The continuous fractional quantile moment equals the quantile boundary block
minus the sum over nonterminal levels and bands of the gamma-weighted difference
between lower- and upper-endpoint quantiles times their respective pooled-quantile
residuals relative to the current-level probability](goal). -/
lemma continuous_fractional_quantile_moment_boundary_decomposition
    (M : LatentIVModel Ω X Z) (phi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e : NuisanceCont L) (o : Obs X Z) :
    continuousFractionalQuantileMoment M phi L e o = continuousQuantileBoundaryBlock M L e o -
      ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k), regularValue e.gamma k j o.1 *
        (nuValue M e k (j-1) o.1 * (pooledQ phi L e k (j-1) o.1 - positiveValue e.pLev k o.1) -
          nuValue M e k j o.1 * (pooledQ phi L e k j o.1 - positiveValue e.pLev k o.1)) := by
  unfold continuousFractionalQuantileMoment continuousQuantileBoundaryBlock
  simp only [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro j hj
  unfold continuousQuantileBoundaryContrast
  ring

-- @node: encoded_continuous_quantile_boundary_block_l2_tendsto_probability_zero
/-- Under [admissibility of the true continuous nuisances](hyp:he0), suppose [the
fitted nuisance sequence](hyp:eh) obeys [clipping](hyp:hclip), [the fitted-share
simplex restrictions](hyp:hshares), [measurability of every encoded coordinate](hyp:hm),
and [the finite nuisance rate conditions relative to truth](hyp:hr). Then [the square
root of the observation-law integrated squared error of the quantile boundary block
at sample indices twice one plus the sequence index converges to zero in probability
under the fitting measure](goal). -/
lemma encoded_continuous_quantile_boundary_block_l2_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L))) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => Real.sqrt (∫ o : Obs X Z,
        (continuousQuantileBoundaryBlock M L (eh (2*(n+1)) t) o -
          continuousQuantileBoundaryBlock M L (trueNuisance M L) o)^2 ∂observationLaw M))
      atTop (fun _ _ => 0) := by
  have hs := encoded_continuous_quantile_boundary_block_sq_tendsto_probability_zero
    M μ L he0 eh hclip hshares hm hr
  have hc : Continuous (fun t : ℝ => Real.sqrt t) := by fun_prop
  simpa only [Real.sqrt_zero] using
    Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt hc.continuousAt hs

-- @node: continuous_fractional_product_score_boundary_block_decomposition
/-- [The sum of continuous fractional product scores over nonterminal levels and
bands equals the gamma-weighted band core plus the band-share correction and the
quantile boundary block, minus the sum of gamma-weighted differences between
lower- and upper-endpoint quantiles times their respective pooled-quantile residuals
relative to the current-level probability](goal). -/
lemma continuous_fractional_product_score_boundary_block_decomposition
    (M : LatentIVModel Ω X Z) (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e : NuisanceCont L) (o : Obs X Z) :
    (∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k), psiProd M phi dphi L e k j o) =
      continuousGammaBandCore M dphi L e o + continuousBandShareCorrection L e o +
        continuousQuantileBoundaryBlock M L e o -
      ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k), regularValue e.gamma k j o.1 *
        (nuValue M e k (j-1) o.1 * (pooledQ phi L e k (j-1) o.1 - positiveValue e.pLev k o.1) -
          nuValue M e k j o.1 * (pooledQ phi L e k j o.1 - positiveValue e.pLev k o.1)) := by
  have h := continuous_fractional_score_sub_quantile_moment M phi dphi L e o
  rw [continuous_fractional_quantile_moment_boundary_decomposition M phi L e o] at h
  convert (sub_eq_iff_eq_add.mp h) using 1 <;> ring


end Papers.TbsPrteOptimalTransport
