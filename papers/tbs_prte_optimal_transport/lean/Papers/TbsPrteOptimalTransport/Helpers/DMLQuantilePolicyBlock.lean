module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousPoolingRates
/-! Gamma-weighted quantile policy widths and their finite score block.
Bounded products and finite-sum convergence close the policy part of the
continuous fractional quantile moment. -/
@[expose] public section
set_option linter.style.openClassical false

set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
  [Fintype Z]

-- @node: continuousQuantilePolicyWidth
/-- For [a latent instrumental-variable model](hyp:M) on [a latent population](hyp:Ω), [a covariate space](hyp:X), and [an instrument space](hyp:Z), with [a policy map](hyp:phi), [a level structure](hyp:L), [continuous nuisance functions](hyp:e), [a level index](hyp:k), [a boundary index](hyp:j), and [a covariate value](hyp:x), [the quantile policy width](goal) is the boundary quantile multiplied by the difference between the pooled policy probability and the baseline probability at that level. -/
noncomputable def continuousQuantilePolicyWidth (M : LatentIVModel Ω X Z)
    (phi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e : NuisanceCont L)
    (k j : ℕ) (x : X) : ℝ :=
  nuValue M e k j x * (pooledQ phi L e k j x - positiveValue e.pLev k x)

-- @node: continuousQuantilePolicyWidth_restrictContShares
/-- [Restricting the continuous nuisance shares leaves the quantile policy width unchanged at every covariate value](goal). -/
lemma continuousQuantilePolicyWidth_restrictContShares (M : LatentIVModel Ω X Z)
    (phi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e : NuisanceCont L) (k j : ℕ) :
    continuousQuantilePolicyWidth M phi L (restrictContShares L e) k j =
      continuousQuantilePolicyWidth M phi L e k j := by
  funext x
  unfold continuousQuantilePolicyWidth
  rw [pooledQ_restrictContShares]
  rfl

-- @node: fitted_continuous_quantile_policy_width_abs_bound
/-- If [the policy map is valid](hyp:hphi) and [the continuous nuisance functions are admissible](hyp:he), then, for [a level below the number of levels](hyp:hk) and [a boundary index no greater than that level's boundary count](hyp:hj), [the absolute quantile policy width is almost surely bounded by twice the sum of the absolute lower and upper outcome bounds](goal). -/
lemma fitted_continuous_quantile_policy_width_abs_bound (M : LatentIVModel Ω X Z)
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e)
    (k j : ℕ) (hk : k < L.K) (hj : j ≤ L.l k) :
    ∀ᵐ x ∂xLaw M, |continuousQuantilePolicyWidth M phi L e k j x| ≤
      (|M.yMin| + |M.yMax|) * 2 := by
  filter_upwards [continuous_admissible_nuValue_abs_bound M L e he k j,
    fitted_continuous_policy_width_abs_bound M phi hphi L e he k j hk hj] with x hx hy
  simp only [continuousQuantilePolicyWidth, abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) (by positivity)

-- @node: fitted_continuous_gamma_quantile_policy_width_memLp
/-- If [the policy map is valid](hyp:hphi) and [the continuous nuisance functions are admissible](hyp:he), then [the gamma-weighted quantile policy width at any regular gamma index and any level and boundary indices is square integrable under the covariate law](goal). -/
lemma fitted_continuous_gamma_quantile_policy_width_memLp
    (M : LatentIVModel Ω X Z) (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e)
    (g : RegularIndex L) (k j : ℕ) :
    MemLp (fun x => e.gamma g x * continuousQuantilePolicyWidth M phi L e k j x)
      2 (xLaw M) := by
  have hgm : Measurable (e.gamma g) := by
    first | fun_prop | skip
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hm, _⟩
    exact hm g
  have hgb : ∀ᵐ x ∂xLaw M, |e.gamma g x| ≤ 1 := by
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hb, _⟩
    filter_upwards [hb g] with x hx
    simpa only [abs_of_nonneg hx.1] using hx.2
  have hw := fitted_continuous_quantile_policy_width_memLp M phi hphi L e he k j
  apply hw.of_le_mul (c := 1) (hgm.aestronglyMeasurable.mul hw.1)
  filter_upwards [hgb] with x hx
  simp only [Pi.mul_apply]
  rw [norm_mul, Real.norm_eq_abs (e.gamma g x)]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

-- @node: encoded_continuous_gamma_quantile_policy_width_sq_tendsto_probability_zero
/-- Suppose [the policy map is valid](hyp:hphi), [its derivative is the specified derivative map](hyp:hd), [that derivative is bounded and Lipschitz](hyp:hDerivative), and [the true continuous nuisances are admissible](hyp:he0). If [the fitted nuisances are clipped](hyp:hclip), [their shares satisfy the simplex constraints](hyp:hshares), [their encoded components are measurable](hyp:hm), and [their finite-component estimation errors satisfy the nuisance convergence rates](hyp:hr), then, for [a level below the number of levels](hyp:hk) and [a boundary index within that level's boundary count](hyp:hj), [the population mean squared error of the gamma-weighted quantile policy width at even sample sizes converges in probability to zero](goal). -/
lemma encoded_continuous_gamma_quantile_policy_width_sq_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L))) (g : RegularIndex L) (k j : ℕ)
    (hk : k < L.K) (hj : j ≤ L.l k) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x,
        ((eh (2*(n+1)) t).gamma g x *
            continuousQuantilePolicyWidth M phi L (eh (2*(n+1)) t) k j x -
          (trueNuisance M L).gamma g x *
            continuousQuantilePolicyWidth M phi L (trueNuisance M L) k j x)^2 ∂xLaw M)
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
  have hQ (e : NuisanceCont L) (he : ContAdmissible M L e) :
      MemLp (continuousQuantilePolicyWidth M phi L e k j) 2 (xLaw M) :=
    fitted_continuous_quantile_policy_width_memLp M phi hphi L e he k j
  have hrQ : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x,
        (continuousQuantilePolicyWidth M phi L (er (2*(n+1)) t) k j x -
          continuousQuantilePolicyWidth M phi L (trueNuisance M L) k j x)^2 ∂xLaw M)
      atTop (fun _ _ => 0) := by
    simp only [er, continuousQuantilePolicyWidth_restrictContShares]
    exact encoded_continuous_quantile_policy_width_sq_tendsto_probability_zero
      M μ phi dphi hphi hd hDerivative L he0 eh hclip hshares hm hr k j hk hj
  have hs := dml_ae_weighted_residual_sq_tendsto_probability_zero μ (xLaw M)
    ((trueNuisance M L).gamma g) (continuousQuantilePolicyWidth M phi L (trueNuisance M L) k j)
    (fun n t => (er (2*(n+1)) t).gamma g)
    (fun n t => continuousQuantilePolicyWidth M phi L (er (2*(n+1)) t) k j)
    1 ((|M.yMin| + |M.yMax|) * 2) (hG _ he0).1.aestronglyMeasurable (hQ _ he0).1
    (fun n t => (hG _ (her _ t)).1.aestronglyMeasurable)
    (fun n t => (hQ _ (her _ t)).1)
    (fun n t => (hmem _ (her _ t)).sub (hmem _ he0))
    (fun n t => (hQ _ (her _ t)).sub (hQ _ he0))
    (fun n t => (hG _ (her _ t)).2)
    (fun _ _ => fitted_continuous_quantile_policy_width_abs_bound
      M phi hphi L _ he0 k j hk hj) hrG hrQ
  simp only [er] at hs
  simp only [continuousQuantilePolicyWidth_restrictContShares] at hs
  simp only [restrictContShares] at hs
  exact hs

-- @node: continuousQuantilePolicyBlock
/-- For [a latent instrumental-variable model](hyp:M) on [a latent population](hyp:Ω), [a covariate space](hyp:X), and [an instrument space](hyp:Z), with [a policy map](hyp:phi), [a level structure](hyp:L), [continuous nuisance functions](hyp:e), and [an observation](hyp:o), [the quantile policy block](goal) sums, over all levels and their regular bands, the gamma weight times the difference between the quantile policy widths at the preceding and current boundaries, evaluated at the observation's covariates. -/
noncomputable def continuousQuantilePolicyBlock (M : LatentIVModel Ω X Z)
    (phi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e : NuisanceCont L) (o : Obs X Z) : ℝ :=
  ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
    regularValue e.gamma k j o.1 *
      (continuousQuantilePolicyWidth M phi L e k (j-1) o.1 -
        continuousQuantilePolicyWidth M phi L e k j o.1)

-- @node: continuousQuantilePolicyBlock_restrictContShares
/-- [Restricting the continuous nuisance shares leaves the entire quantile policy block unchanged as a function of the observation](goal). -/
lemma continuousQuantilePolicyBlock_restrictContShares
    (M : LatentIVModel Ω X Z) (phi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e : NuisanceCont L) :
    continuousQuantilePolicyBlock M phi L (restrictContShares L e) =
      continuousQuantilePolicyBlock M phi L e := by
  funext o
  unfold continuousQuantilePolicyBlock
  simp only [continuousQuantilePolicyWidth_restrictContShares]
  rfl

-- @node: continuousQuantileBoundaryBlock_restrictContShares
/-- [Restricting the continuous nuisance shares leaves the quantile boundary block unchanged as a function of the observation](goal). -/
lemma continuousQuantileBoundaryBlock_restrictContShares
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (e : NuisanceCont L) :
    continuousQuantileBoundaryBlock M L (restrictContShares L e) =
      continuousQuantileBoundaryBlock M L e := by
  funext o
  simp only [continuousQuantileBoundaryBlock, continuousQuantileBoundaryContrast,
    restrictContShares, nuValue, regularValue]

-- @node: fitted_continuous_quantile_policy_block_memLp
/-- If [the policy map is valid](hyp:hphi) and [the continuous nuisance functions are admissible](hyp:he), then [the quantile policy block is square integrable under the population observation law](goal). -/
lemma fitted_continuous_quantile_policy_block_memLp
    (M : LatentIVModel Ω X Z) (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) :
    MemLp (continuousQuantilePolicyBlock M phi L e) 2 (observationLaw M) := by
  unfold continuousQuantilePolicyBlock
  apply memLp_finsetSum
  intro k hk
  apply memLp_finsetSum
  intro j hj
  have hg : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k :=
    ⟨(Finset.mem_range.mp hk).le, Finset.mem_Icc.mp hj⟩
  have h := ((fitted_continuous_gamma_quantile_policy_width_memLp M phi hphi L e he
    ⟨(k,j),hg⟩ k (j-1)).sub
    (fitted_continuous_gamma_quantile_policy_width_memLp M phi hphi L e he
      ⟨(k,j),hg⟩ k j)).comp_measurePreserving (observationLaw_fst_measurePreserving M)
  convert h using 1
  funext o
  simp only [Function.comp_apply, Pi.sub_apply, regularValue, dif_pos hg]
  ring

-- @node: encoded_continuous_quantile_policy_block_sq_tendsto_probability_zero
/-- Suppose [the policy map is valid](hyp:hphi), [the specified map is its derivative](hyp:hd), [that derivative is bounded and Lipschitz](hyp:hDerivative), and [the true continuous nuisances are admissible](hyp:he0). If [the fitted nuisances are clipped](hyp:hclip), [their shares satisfy the simplex constraints](hyp:hshares), [their encoded components are measurable](hyp:hm), and [their finite-component errors satisfy the nuisance convergence rates](hyp:hr), then [the population mean squared difference between the fitted and true quantile policy blocks at even sample sizes converges in probability to zero](goal). -/
lemma encoded_continuous_quantile_policy_block_sq_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L))) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o : Obs X Z,
        (continuousQuantilePolicyBlock M phi L (eh (2*(n+1)) t) o -
          continuousQuantilePolicyBlock M phi L (trueNuisance M L) o)^2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  let F := fun k j b n t x => regularValue (er (2*(n+1)) t).gamma k j x *
    continuousQuantilePolicyWidth M phi L (er (2*(n+1)) t) k b x -
    regularValue (trueNuisance M L).gamma k j x *
      continuousQuantilePolicyWidth M phi L (trueNuisance M L) k b x
  have hF k j b n t (hg : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k) :
      MemLp (F k j b n t) 2 (xLaw M) := by
    simpa only [F, regularValue, dif_pos hg, Pi.sub_def] using
      (fitted_continuous_gamma_quantile_policy_width_memLp M phi hphi L _ (her _ t)
        ⟨(k,j),hg⟩ k b).sub
      (fitted_continuous_gamma_quantile_policy_width_memLp M phi hphi L _ he0 ⟨(k,j),hg⟩ k b)
  have hrF k j b (hk : k < L.K) (hb : b ≤ L.l k)
      (hg : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k) :
      Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
        (fun n t => ∫ x, (F k j b n t x)^2 ∂xLaw M) atTop (fun _ _ => 0) := by
    dsimp only [F, er]
    simp only [continuousQuantilePolicyWidth_restrictContShares]
    simpa only [regularValue, dif_pos hg, restrictContShares] using
      encoded_continuous_gamma_quantile_policy_width_sq_tendsto_probability_zero
        M μ phi dphi hphi hd hDerivative L he0 eh hclip hshares hm hr ⟨(k,j),hg⟩ k b hk hb
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
  have hrD k j (hk : k < L.K) (hg : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k) :=
    dml_three_term_sq_tendsto_probability_zero μ (xLaw M)
      (F k j (j-1)) (fun _ _ _ => 0) (F k j j) (fun n t => hF k j (j-1) n t hg)
      (fun _ _ => MemLp.zero') (fun n t => hF k j j n t hg)
      (hrF k j (j-1) hk (by omega) hg) (by simpa using hz) (hrF k j j hk hg.2.2 hg)
  have hs := dml_finset_sum_sq_tendsto_probability_zero μ (xLaw M)
    (Finset.range L.K) (fun k n t x => ∑ j ∈ Finset.Icc 1 (L.l k), D k j n t x)
    (fun k hk n t => memLp_finsetSum _ (fun j hj =>
      hD k j n t ⟨(Finset.mem_range.mp hk).le, Finset.mem_Icc.mp hj⟩)) (by
      intro k hk
      apply dml_finset_sum_sq_tendsto_probability_zero μ (xLaw M)
        (Finset.Icc 1 (L.l k)) (D k)
        (fun j hj n t => hD k j n t ⟨(Finset.mem_range.mp hk).le, Finset.mem_Icc.mp hj⟩)
      intro j hj
      exact hrD k j (Finset.mem_range.mp hk) ⟨(Finset.mem_range.mp hk).le, Finset.mem_Icc.mp hj⟩)
  have hid n t (o : Obs X Z) :
      (∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k), D k j n t o.1) =
      continuousQuantilePolicyBlock M phi L (eh (2*(n+1)) t) o -
        continuousQuantilePolicyBlock M phi L (trueNuisance M L) o := by
    dsimp only [D, F, er]
    simp only [continuousQuantilePolicyWidth_restrictContShares]
    simp only [continuousQuantilePolicyBlock, restrictContShares, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hi n t :
      (∫ o : Obs X Z, (∑ k ∈ Finset.range L.K,
        ∑ j ∈ Finset.Icc 1 (L.l k), D k j n t o.1)^2 ∂observationLaw M) =
      ∫ x, (∑ k ∈ Finset.range L.K,
        ∑ j ∈ Finset.Icc 1 (L.l k), D k j n t x)^2 ∂xLaw M := by
    have hsum : MemLp (fun x => ∑ k ∈ Finset.range L.K,
        ∑ j ∈ Finset.Icc 1 (L.l k), D k j n t x) 2 (xLaw M) :=
      memLp_finsetSum _ (fun k hk => memLp_finsetSum _ (fun j hj =>
        hD k j n t ⟨(Finset.mem_range.mp hk).le, Finset.mem_Icc.mp hj⟩))
    have hmp := observationLaw_fst_measurePreserving M
    rw [← hmp.map_eq]
    exact (integral_map hmp.aemeasurable (by
      simpa only [hmp.map_eq] using hsum.1.pow 2)).symm
  convert hs using 1
  funext n t
  rw [← hi n t]
  congr 1
  funext o
  rw [hid]

-- @node: continuous_fractional_quantile_moment_policy_block_decomposition
/-- [The continuous fractional quantile moment equals the quantile boundary block minus the quantile policy block at each observation](goal). -/
lemma continuous_fractional_quantile_moment_policy_block_decomposition
    (M : LatentIVModel Ω X Z) (phi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e : NuisanceCont L) (o : Obs X Z) :
    continuousFractionalQuantileMoment M phi L e o =
      continuousQuantileBoundaryBlock M L e o - continuousQuantilePolicyBlock M phi L e o := by
  rw [continuous_fractional_quantile_moment_boundary_decomposition]
  rfl

-- @node: fitted_continuous_fractional_quantile_moment_memLp
/-- If [the policy map is valid](hyp:hphi) and [the continuous nuisance functions are admissible](hyp:he), then [the continuous fractional quantile moment is square integrable under the population observation law](goal). -/
lemma fitted_continuous_fractional_quantile_moment_memLp
    (M : LatentIVModel Ω X Z) (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e) :
    MemLp (continuousFractionalQuantileMoment M phi L e) 2 (observationLaw M) := by
  change MemLp (fun o => continuousFractionalQuantileMoment M phi L e o) 2 (observationLaw M)
  simp_rw [continuous_fractional_quantile_moment_policy_block_decomposition]
  exact (fitted_continuous_quantile_boundary_block_memLp M L e he).sub
    (fitted_continuous_quantile_policy_block_memLp M phi hphi L e he)

-- @node: continuousFractionalQuantileMoment_restrictContShares
/-- [Restricting the continuous nuisance shares leaves the continuous fractional quantile moment unchanged as a function of the observation](goal). -/
lemma continuousFractionalQuantileMoment_restrictContShares
    (M : LatentIVModel Ω X Z) (phi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e : NuisanceCont L) :
    continuousFractionalQuantileMoment M phi L (restrictContShares L e) =
      continuousFractionalQuantileMoment M phi L e := by
  funext o
  unfold continuousFractionalQuantileMoment
  simp only [pooledQ_restrictContShares]
  rfl

-- @node: encoded_continuous_fractional_quantile_moment_sq_tendsto_probability_zero
/-- Assume [the policy map is valid](hyp:hphi), [the specified derivative differentiates it](hyp:hd), [the derivative is bounded and Lipschitz](hyp:hDerivative), and [the true continuous nuisances are admissible](hyp:he0). If [the fitted nuisances are clipped](hyp:hclip), [their shares obey the simplex constraints](hyp:hshares), [their encoded components are measurable](hyp:hm), and [their finite-component errors satisfy the nuisance convergence rates](hyp:hr), then [the population mean squared error of the fitted continuous fractional quantile moment at even sample sizes converges in probability to zero](goal). -/
lemma encoded_continuous_fractional_quantile_moment_sq_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L))) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o : Obs X Z,
        (continuousFractionalQuantileMoment M phi L (eh (2*(n+1)) t) o -
          continuousFractionalQuantileMoment M phi L (trueNuisance M L) o)^2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  let F := fun n t o => continuousQuantileBoundaryBlock M L (eh (2*(n+1)) t) o -
    continuousQuantileBoundaryBlock M L (trueNuisance M L) o
  let G := fun n t o => continuousQuantilePolicyBlock M phi L (eh (2*(n+1)) t) o -
    continuousQuantilePolicyBlock M phi L (trueNuisance M L) o
  have hF n t : MemLp (F n t) 2 (observationLaw M) := by
    have h := (fitted_continuous_quantile_boundary_block_memLp M L _ (her (2*(n+1)) t)).sub
      (fitted_continuous_quantile_boundary_block_memLp M L _ he0)
    dsimp only [er] at h
    rw [continuousQuantileBoundaryBlock_restrictContShares] at h
    exact h
  have hG n t : MemLp (G n t) 2 (observationLaw M) := by
    have h := (fitted_continuous_quantile_policy_block_memLp M phi hphi L _ (her (2*(n+1)) t)).sub
      (fitted_continuous_quantile_policy_block_memLp M phi hphi L _ he0)
    dsimp only [er] at h
    rw [continuousQuantilePolicyBlock_restrictContShares] at h
    exact h
  have hz : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun (_ : ℕ) (_ : A) => (0 : ℝ)) atTop (fun _ _ => 0) := by
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
    intro eps heps
    simpa [not_le_of_gt heps] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
  have hs := dml_three_term_sq_tendsto_probability_zero μ (observationLaw M)
    F (fun _ _ _ => 0) G hF (fun _ _ => MemLp.zero') hG
    (encoded_continuous_quantile_boundary_block_sq_tendsto_probability_zero
      M μ L he0 eh hclip hshares hm hr) (by simpa using hz)
    (encoded_continuous_quantile_policy_block_sq_tendsto_probability_zero
      M μ phi dphi hphi hd hDerivative L he0 eh hclip hshares hm hr)
  convert hs using 1
  funext n t
  congr 1
  funext o
  simp only [continuous_fractional_quantile_moment_policy_block_decomposition, F, G]
  ring

-- @node: encoded_continuous_fractional_quantile_moment_l2_tendsto_probability_zero
/-- If [the policy map is valid](hyp:hphi), [the specified map is its derivative](hyp:hd), [the derivative is bounded and Lipschitz](hyp:hDerivative), and [the true continuous nuisances are admissible](hyp:he0), while [the fitted nuisances are clipped](hyp:hclip), [their shares obey the simplex constraints](hyp:hshares), [their encoded components are measurable](hyp:hm), and [their finite-component errors satisfy the nuisance convergence rates](hyp:hr), then [the square root of the population mean squared error of the fitted continuous fractional quantile moment at even sample sizes converges in probability to zero](goal). -/
lemma encoded_continuous_fractional_quantile_moment_l2_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L))) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => Real.sqrt (∫ o : Obs X Z,
        (continuousFractionalQuantileMoment M phi L (eh (2*(n+1)) t) o -
          continuousFractionalQuantileMoment M phi L (trueNuisance M L) o)^2 ∂observationLaw M))
      atTop (fun _ _ => 0) := by
  have hs := encoded_continuous_fractional_quantile_moment_sq_tendsto_probability_zero
    M μ phi dphi hphi hd hDerivative L he0 eh hclip hshares hm hr
  have hc : Continuous (fun t : ℝ => Real.sqrt t) := by fun_prop
  simpa only [Real.sqrt_zero] using
    Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt hc.continuousAt hs

-- @node: fitted_continuous_fractional_product_score_memLp
/-- Suppose [the policy map is valid](hyp:hphi), [the specified map is its derivative](hyp:hd), [the derivative is bounded and Lipschitz](hyp:hDerivative), and [the continuous nuisance functions are admissible](hyp:he). If [the common denominator bound is positive](hyp:hc), [every positive-level baseline probability is almost surely at least that bound](hyp:hpi), and [every regular-band policy probability is almost surely at least that bound](hyp:htau), then [the sum of the continuous fractional product scores over all levels and regular bands is square integrable under the population observation law](goal). -/
lemma fitted_continuous_fractional_product_score_memLp
    (M : LatentIVModel Ω X Z) (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e)
    (c : ℝ) (hc : 0 < c)
    (hpi : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (htau : ∀ r : RegularIndex L, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x) :
    MemLp (fun o : Obs X Z => ∑ k ∈ Finset.range L.K,
      ∑ j ∈ Finset.Icc 1 (L.l k), psiProd M phi dphi L e k j o) 2 (observationLaw M) := by
  have h := (fitted_continuous_fractional_score_sub_quantile_moment_memLp
    M phi dphi hphi hd hDerivative L e he c hc hpi htau).add
    (fitted_continuous_fractional_quantile_moment_memLp M phi hphi L e he)
  convert h using 1
  funext o
  simp only [Pi.add_apply, sub_add_cancel]

-- @node: encoded_continuous_fractional_product_score_sq_tendsto_probability_zero
/-- Suppose [the policy map is valid](hyp:hphi), [the specified map is its derivative](hyp:hd), [the derivative is bounded and Lipschitz](hyp:hDerivative), and [the true continuous nuisances are admissible](hyp:he0). If [the fitted nuisances are clipped](hyp:hclip), [their shares obey the simplex constraints](hyp:hshares), [their encoded components are measurable](hyp:hm), [their finite-component errors satisfy the nuisance convergence rates](hyp:hr), [boundary densities are bounded](hyp:hDensity), [baseline overlap holds at the chosen bound](hyp:hov), [policy overlap holds at that bound](hyp:hpol), and [the fitted denominators are clipped at that bound](hyp:hden), then [the population mean squared error of the sum of continuous fractional product scores over all levels and regular bands, evaluated at even sample sizes, converges in probability to zero](goal). -/
lemma encoded_continuous_fractional_product_score_sq_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L)))
    (hDensity : BoundaryDensitiesBounded M L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hpol : PolicyOverlap M L cpi)
    (hden : ∀ n t, ContDenominatorsClipped L (eh n t) cpi) :
    let score := fun (e : NuisanceCont L) (o : Obs X Z) =>
      ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k), psiProd M phi dphi L e k j o
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o : Obs X Z, (score (eh (2*(n+1)) t) o -
        score (trueNuisance M L) o)^2 ∂observationLaw M) atTop (fun _ _ => 0) := by
  dsimp only
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  let C := fun (e : NuisanceCont L) (o : Obs X Z) =>
    continuousGammaBandCore M dphi L e o + continuousBandShareCorrection L e o
  let Q := continuousFractionalQuantileMoment M phi L
  let F := fun n t o => C (eh (2*(n+1)) t) o - C (trueNuisance M L) o
  let G := fun n t o => Q (eh (2*(n+1)) t) o - Q (trueNuisance M L) o
  have hc : 0 < cpi/2 := by linarith [hov.1]
  have hp0 (i : PositiveIndex L.K) :
      ∀ᵐ x ∂xLaw M, cpi/2 ≤ (trueNuisance M L).piLev i x := by
    apply Eventually.of_forall
    intro x
    have hx := hov.2 x i.val i.property.1 i.property.2
    change cpi/2 ≤ (levelSetProb M L).1 i.val x
    linarith [hov.1]
  have ht0 (r : RegularIndex L) :
      ∀ᵐ x ∂xLaw M, cpi/2 ≤ (trueNuisance M L).tauLev r x := by
    have hne := continuous_admissible_policy_nonempty M L _ he0 r
    apply Eventually.of_forall
    intro x
    have hx : cpi ≤ (trueNuisance M L).tauLev r x :=
      hpol.2 x r.val.1 r.val.2 r.property.1 r.property.2.1 r.property.2.2 hne
    linarith [hpol.1]
  have hF n t : MemLp (F n t) 2 (observationLaw M) := by
    have hfit := fitted_continuous_fractional_score_sub_quantile_moment_memLp
      M phi dphi hphi hd hDerivative L _ (her (2*(n+1)) t) (cpi/2) hc
      (fun i => Eventually.of_forall (fun x => (hden (2*(n+1)) t).1 i x |>.1))
      (fun r => Eventually.of_forall (fun x => ((hden (2*(n+1)) t).2 r x
        (contFittedSharesSimplex_policy_nonempty L (eh (2*(n+1)) t)
          (hshares (2*(n+1)) t) r)).1))
    have htrue := fitted_continuous_fractional_score_sub_quantile_moment_memLp
      M phi dphi hphi hd hDerivative L _ he0 (cpi/2) hc hp0 ht0
    simp_rw [continuous_fractional_score_sub_quantile_moment] at hfit htrue
    dsimp only [er] at hfit
    rw [continuousGammaBandCore_restrictContShares] at hfit
    simpa only [F, C, er, continuousBandShareCorrection, restrictContShares,
      contJ, regularValue, Pi.sub_def] using hfit.sub htrue
  have hG n t : MemLp (G n t) 2 (observationLaw M) := by
    have hfit := fitted_continuous_fractional_quantile_moment_memLp
      M phi hphi L _ (her (2*(n+1)) t)
    dsimp only [er] at hfit
    rw [continuousFractionalQuantileMoment_restrictContShares] at hfit
    exact hfit.sub (fitted_continuous_fractional_quantile_moment_memLp M phi hphi L _ he0)
  have hrF : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o, (F n t o)^2 ∂observationLaw M) atTop (fun _ _ => 0) := by
    have h := encoded_continuous_fractional_score_sub_quantile_moment_sq_tendsto_probability_zero
      M μ phi dphi hphi hd hDerivative L he0 eh hclip hshares hm hDensity hr cpi hov hpol hden
    dsimp only at h
    simp_rw [continuous_fractional_score_sub_quantile_moment] at h
    simpa only [F, C] using h
  have hrG := encoded_continuous_fractional_quantile_moment_sq_tendsto_probability_zero
    M μ phi dphi hphi hd hDerivative L he0 eh hclip hshares hm hr
  have hz : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun (_ : ℕ) (_ : A) => (0 : ℝ)) atTop (fun _ _ => 0) := by
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
    intro eps heps
    simpa [not_le_of_gt heps] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
  have hs := dml_three_term_sq_tendsto_probability_zero μ (observationLaw M)
    F G (fun _ _ _ => 0) hF hG (fun _ _ => MemLp.zero') hrF hrG (by simpa using hz)
  have hid (e : NuisanceCont L) o :
      (∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k), psiProd M phi dphi L e k j o) =
      C e o + Q e o := by
    have h := continuous_fractional_score_sub_quantile_moment M phi dphi L e o
    exact sub_eq_iff_eq_add.mp h
  convert hs using 1
  funext n t
  congr 1
  funext o
  rw [hid, hid]
  dsimp only [F, G]
  ring

-- @node: encoded_continuous_fractional_product_score_l2_tendsto_probability_zero
/-- Assume [a valid policy map](hyp:hphi) with [the specified derivative](hyp:hd) that [is bounded and Lipschitz](hyp:hDerivative), and [admissible true continuous nuisances](hyp:he0). If [the fitted nuisances are clipped](hyp:hclip), [their shares satisfy the simplex constraints](hyp:hshares), [their encoded components are measurable](hyp:hm), [their finite-component errors satisfy the nuisance convergence rates](hyp:hr), [boundary densities are bounded](hyp:hDensity), [baseline overlap holds at the chosen bound](hyp:hov), [policy overlap holds at that bound](hyp:hpol), and [the fitted denominators are clipped at that bound](hyp:hden), then [the square root of the population mean squared error of the sum of continuous fractional product scores over all levels and regular bands at even sample sizes converges in probability to zero](goal). -/
lemma encoded_continuous_fractional_product_score_l2_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L)))
    (hDensity : BoundaryDensitiesBounded M L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hpol : PolicyOverlap M L cpi)
    (hden : ∀ n t, ContDenominatorsClipped L (eh n t) cpi) :
    let score := fun (e : NuisanceCont L) (o : Obs X Z) =>
      ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k), psiProd M phi dphi L e k j o
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => Real.sqrt (∫ o : Obs X Z, (score (eh (2*(n+1)) t) o -
        score (trueNuisance M L) o)^2 ∂observationLaw M)) atTop (fun _ _ => 0) := by
  have hs := encoded_continuous_fractional_product_score_sq_tendsto_probability_zero
    M μ phi dphi hphi hd hDerivative L he0 eh hclip hshares hm hr hDensity cpi hov hpol hden
  have hc : Continuous (fun t : ℝ => Real.sqrt t) := by fun_prop
  simpa only [Real.sqrt_zero] using
    Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt hc.continuousAt hs

end Papers.TbsPrteOptimalTransport
