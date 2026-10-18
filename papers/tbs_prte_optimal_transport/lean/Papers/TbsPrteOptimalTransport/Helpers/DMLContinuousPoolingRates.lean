module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLQuantileBoundaryProducts
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousTailConvergence
public import Papers.TbsPrteOptimalTransport.Helpers.DMLPooledPolicyConvergence
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousFullRates
/-! Continuous pooled-policy endpoint rates and quantile-weighted widths.
The binary coordinate carrier is used only for shared policy coordinates;
no binary-outcome assumption is needed. -/
public section
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
  [Fintype Z] [DecidableEq Z]

-- @node: fitted_continuous_pooledQ_memLp
/-- If [the policy map is valid](hyp:hphi) and [the continuous nuisances are admissible](hyp:he),
[the fitted pooled policy endpoint is square integrable under the covariate law](goal). -/
lemma fitted_continuous_pooledQ_memLp (M : LatentIVModel Ω X Z)
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e)
    (k j : ℕ) : MemLp (pooledQ phi L e k j) 2 (xLaw M) := by
  exact fitted_pooledQBin_memLp M phi hphi L (continuousTailCoordinates L e)
    (continuousTailCoordinates_admissible M L e he) k j

-- @node: nuisanceRates_continuous_pooledQ_quarter_rate
/-- If [the policy map is valid](hyp:hphi), [it has the specified derivative](hyp:hd),
[the derivative is bounded and Lipschitz](hyp:hDerivative), [the reference and all fitted
nuisances are admissible](hyp:he0,heh), [propensity L² errors toward their reference
values are smaller in probability than the inverse fourth root of sample size](hyp:hrp),
[level-probability L² errors have that same rate](hyp:hrlev), and [share L² errors at
each regular index have that same rate](hyp:hrs),
[the fitted pooled policy endpoints also have L² errors of that order toward their
reference endpoints](goal). -/
lemma nuisanceRates_continuous_pooledQ_quarter_rate (M : LatentIVModel Ω X Z)
    (μ : Measure A) (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n t, ContAdmissible M L (eh n t))
    (hrp : FiniteNuisanceRates M μ (fun n t => (eh n t).prop) e0.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n t => (eh n t).pLev) e0.pLev)
    (hrs : ∀ r : RegularIndex L,
      FiniteNuisanceRates M μ (fun n t => (eh n t).share r) (e0.share r)) :
    FiniteNuisanceRates M μ (fun n t (b : ℕ × ℕ) => pooledQ phi L (eh n t) b.1 b.2)
      (fun b => pooledQ phi L e0 b.1 b.2) := by
  obtain ⟨B, Lip, hB, hLip, hder⟩ := hDerivative
  have hlip := policy_lipschitz_of_derivative_bound phi dphi hd B
    (fun z x p hp => (hder z x p p hp hp).1)
  exact nuisanceRates_pooledQBin_quarter_rate M μ phi hphi B hB hlip L
    (continuousTailCoordinates L e0) (fun n t => continuousTailCoordinates L (eh n t))
    (continuousTailCoordinates_admissible M L e0 he0)
    (fun n t => continuousTailCoordinates_admissible M L (eh n t) (heh n t))
    hrp hrlev hrs

-- @node: encoded_continuous_pooledQ_quarter_rate
/-- If [the policy map is valid](hyp:hphi), [it has the specified derivative](hyp:hd),
[the derivative is bounded and Lipschitz](hyp:hDerivative), [true nuisances are admissible](hyp:he0),
[fitted nuisances satisfy clipping](hyp:hclip), [fitted shares form simplexes](hyp:hshares),
[encoded fitted components are measurable](hyp:hm), and [their componentwise L² errors
toward truth are smaller in probability than the inverse fourth root of sample size](hyp:hr),
[each fitted pooled policy endpoint has an L² error toward its true endpoint smaller
in probability than the inverse fourth root of sample size](goal). -/
lemma encoded_continuous_pooledQ_quarter_rate (M : LatentIVModel Ω X Z)
    (μ : Measure A) (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L))) :
    FiniteNuisanceRates M μ (fun n t (b : ℕ × ℕ) => pooledQ phi L (eh n t) b.1 b.2)
      (fun b => pooledQ phi L (trueNuisance M L) b.1 b.2) := by
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  obtain ⟨hrp, hrlev, _, _, hrs, _⟩ :=
    continuous_component_rates_to_oracle_rates M μ L eh (trueNuisance M L) hr
  have hrs' (r : RegularIndex L) :
      FiniteNuisanceRates M μ (fun n t => (er n t).share r) ((trueNuisance M L).share r) := by
    intro z
    have heq n t : finiteL2Error M ((er n t).share r z)
        ((restrictContShares L (trueNuisance M L)).share r z) =
        finiteL2Error M ((er n t).share r z) ((trueNuisance M L).share r z) := by
      unfold finiteL2Error
      congr 1
      apply integral_congr_ae
      filter_upwards [restrictContShares_eq_of_admissible M L _ he0] with x hx
      rw [hx r z]
    simpa only [er, heq] using hrs r z
  have hs := nuisanceRates_continuous_pooledQ_quarter_rate M μ phi dphi hphi hd
    hDerivative L (trueNuisance M L) er he0 her hrp hrlev hrs'
  have heq : (fun n t (b : ℕ × ℕ) => pooledQ phi L (er n t) b.1 b.2) =
      (fun n t (b : ℕ × ℕ) => pooledQ phi L (eh n t) b.1 b.2) := by
    funext n t b x
    exact pooledQ_restrictContShares phi L (eh n t) b.1 b.2 x
  rw [heq] at hs
  exact hs

-- @node: encoded_continuous_pooledQ_sq_tendsto_probability_zero
/-- Under [a valid policy map](hyp:hphi) [with the specified derivative](hyp:hd),
[a bounded Lipschitz derivative](hyp:hDerivative), [admissible true nuisances](hyp:he0),
[clipped fitted nuisances](hyp:hclip), [fitted share simplexes](hyp:hshares),
[measurable fitted components](hyp:hm), and [encoded componentwise L² errors toward truth
smaller in probability than the inverse fourth root of sample size](hyp:hr),
[the integrated squared error of each fitted pooled policy endpoint converges in
probability to zero along sample sizes twice one plus the index](goal). -/
lemma encoded_continuous_pooledQ_sq_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L))) (k j : ℕ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (pooledQ phi L (eh (2*(n+1)) t) k j x -
        pooledQ phi L (trueNuisance M L) k j x)^2 ∂xLaw M)
      atTop (fun _ _ => 0) := by
  exact nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _
    (encoded_continuous_pooledQ_quarter_rate M μ phi dphi hphi hd hDerivative
      L he0 eh hclip hshares hm hr) (k,j)

-- @node: fitted_continuous_policy_width_memLp
/-- If [the policy map is valid](hyp:hphi) and [the continuous nuisances are admissible](hyp:he),
[the fitted policy width, the pooled endpoint minus the baseline level probability,
is square integrable under the covariate law](goal). -/
lemma fitted_continuous_policy_width_memLp (M : LatentIVModel Ω X Z)
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e)
    (k j : ℕ) :
    MemLp (fun x => pooledQ phi L e k j x - positiveValue e.pLev k x)
      2 (xLaw M) := by
  exact (fitted_continuous_pooledQ_memLp M phi hphi L e he k j).sub
    (fitted_continuous_full_coordinate_memLp M L e he k).1

-- @node: fitted_continuous_policy_width_abs_bound
/-- If [the policy map is valid](hyp:hphi), [the continuous nuisances are admissible](hyp:he),
[the level index is strictly below the number of levels](hyp:hk), and [the boundary
index does not exceed the number of boundaries at that level](hyp:hj), [the absolute
fitted policy width is at most two almost surely under the covariate law](goal). -/
lemma fitted_continuous_policy_width_abs_bound (M : LatentIVModel Ω X Z)
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e)
    (k j : ℕ) (hk : k < L.K) (hj : j ≤ L.l k) :
    ∀ᵐ x ∂xLaw M, |pooledQ phi L e k j x - positiveValue e.pLev k x| ≤ 2 := by
  have hq := pooledQBin_range M phi L (continuousTailCoordinates L e) hphi
    (continuousTailCoordinates_admissible M L e he) k hk j hj
  filter_upwards [hq, (fitted_continuous_full_coordinates M L e he k).1.2] with x hx hp
  change pooledQ phi L e k j x ∈ Icc (0 : ℝ) 1 at hx
  exact (abs_sub _ _).trans (by rw [abs_of_nonneg hx.1]; linarith [hx.2])

-- @node: encoded_continuous_policy_width_sq_tendsto_probability_zero
/-- If [the policy map is valid](hyp:hphi), [it has the specified derivative](hyp:hd),
[the derivative is bounded and Lipschitz](hyp:hDerivative), [true nuisances are admissible](hyp:he0),
[fitted nuisances satisfy clipping](hyp:hclip), [fitted shares form simplexes](hyp:hshares),
[fitted components are measurable](hyp:hm), and [encoded componentwise L² errors toward
truth are smaller in probability than the inverse fourth root of sample size](hyp:hr),
[the integrated squared error of the fitted policy width
converges in probability to zero along sample sizes twice one plus the index](goal). -/
lemma encoded_continuous_policy_width_sq_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L))) (k j : ℕ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x,
        ((pooledQ phi L (eh (2*(n+1)) t) k j x -
            positiveValue (eh (2*(n+1)) t).pLev k x) -
          (pooledQ phi L (trueNuisance M L) k j x -
            positiveValue (trueNuisance M L).pLev k x))^2 ∂xLaw M)
      atTop (fun _ _ => 0) := by
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  let Q := fun n t x => pooledQ phi L (er (2*(n+1)) t) k j x -
    pooledQ phi L (trueNuisance M L) k j x
  let P := fun n t x => positiveValue (er (2*(n+1)) t).pLev k x -
    positiveValue (trueNuisance M L).pLev k x
  have hQ n t : MemLp (Q n t) 2 (xLaw M) :=
    (fitted_continuous_pooledQ_memLp M phi hphi L _ (her _ t) k j).sub
      (fitted_continuous_pooledQ_memLp M phi hphi L _ he0 k j)
  have hP n t : MemLp (P n t) 2 (xLaw M) :=
    (fitted_continuous_full_coordinate_memLp M L _ (her _ t) k).1.sub
      (fitted_continuous_full_coordinate_memLp M L _ he0 k).1
  have hrQ : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (Q n t x)^2 ∂xLaw M) atTop (fun _ _ => 0) := by
    have hq := encoded_continuous_pooledQ_sq_tendsto_probability_zero
      M μ phi dphi hphi hd hDerivative L he0 eh hclip hshares hm hr k j
    simpa only [Q, er, pooledQ_restrictContShares] using hq
  let z0 : Z := Classical.choice inferInstance
  have hrP : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (P n t x)^2 ∂xLaw M) atTop (fun _ _ => 0) := by
    simpa only [P, er, restrictContShares, contComponent] using
      nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hr (1,k,0,z0)
  have hz : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun (_ : ℕ) (_ : A) => (0 : ℝ)) atTop (fun _ _ => 0) := by
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
    intro eps heps
    simpa [not_le_of_gt heps] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
  have hs := dml_three_term_sq_tendsto_probability_zero μ (xLaw M) Q
    (fun _ _ _ => 0) P hQ (fun _ _ => MemLp.zero') hP hrQ (by simpa using hz) hrP
  convert hs using 1
  funext n t
  congr 1
  funext x
  simp only [Q, P, er, pooledQ_restrictContShares]
  simp only [restrictContShares]
  ring

-- @node: fitted_continuous_quantile_policy_width_memLp
/-- If [the policy map is valid](hyp:hphi) and [the continuous nuisances are admissible](hyp:he),
[the fitted quantile times the policy width is square integrable under the covariate law](goal). -/
lemma fitted_continuous_quantile_policy_width_memLp (M : LatentIVModel Ω X Z)
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e)
    (k j : ℕ) :
    MemLp (fun x => nuValue M e k j x *
      (pooledQ phi L e k j x - positiveValue e.pLev k x)) 2 (xLaw M) := by
  have hw := fitted_continuous_policy_width_memLp M phi hphi L e he k j
  have hnu : Measurable (nuValue M e k j) := by fun_prop
  apply hw.of_le_mul (c := |M.yMin| + |M.yMax|)
    (hnu.aestronglyMeasurable.mul hw.1)
  filter_upwards [continuous_admissible_nuValue_abs_bound M L e he k j] with x hx
  simp only [Pi.mul_apply]
  rw [norm_mul, Real.norm_eq_abs (nuValue M e k j x)]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

-- @node: encoded_continuous_quantile_policy_width_sq_tendsto_probability_zero
/-- Assume [a valid policy map](hyp:hphi) [with the specified derivative](hyp:hd),
[a bounded Lipschitz derivative](hyp:hDerivative), [admissible true nuisances](hyp:he0),
[clipped fitted nuisances](hyp:hclip), [fitted share simplexes](hyp:hshares),
[measurable fitted components](hyp:hm), and [encoded componentwise L² errors toward truth
smaller in probability than the inverse fourth root of sample size](hyp:hr).
If [the level index is below the number of levels](hyp:hk) and [the boundary index does
not exceed the number of boundaries at that level](hyp:hj), [the integrated squared
error of the fitted quantile-weighted policy width converges in probability to zero
along sample sizes twice one plus the index](goal). -/
lemma encoded_continuous_quantile_policy_width_sq_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L))) (k j : ℕ)
    (hk : k < L.K) (hj : j ≤ L.l k) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x,
        (nuValue M (eh (2*(n+1)) t) k j x *
            (pooledQ phi L (eh (2*(n+1)) t) k j x -
              positiveValue (eh (2*(n+1)) t).pLev k x) -
          nuValue M (trueNuisance M L) k j x *
            (pooledQ phi L (trueNuisance M L) k j x -
              positiveValue (trueNuisance M L).pLev k x))^2 ∂xLaw M)
      atTop (fun _ _ => 0) := by
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  let N := fun (e : NuisanceCont L) => nuValue M e k j
  let W := fun (e : NuisanceCont L) x => pooledQ phi L e k j x - positiveValue e.pLev k x
  have hN (e : NuisanceCont L) : N (restrictContShares L e) = N e := by
    funext x
    simp only [N, nuValue, restrictContShares]
  have hW (e : NuisanceCont L) : W (restrictContShares L e) = W e := by
    funext x
    dsimp only [W]
    rw [pooledQ_restrictContShares]
    rfl
  have hn (e : NuisanceCont L) (he : ContAdmissible M L e) :
      MemLp (N e) 2 (xLaw M) :=
    MemLp.of_bound (by fun_prop) (|M.yMin| + |M.yMax|)
      (by simpa only [N, Real.norm_eq_abs] using
        continuous_admissible_nuValue_abs_bound M L e he k j)
  have hw (e : NuisanceCont L) (he : ContAdmissible M L e) :
      MemLp (W e) 2 (xLaw M) :=
    fitted_continuous_policy_width_memLp M phi hphi L e he k j
  let z0 : Z := Classical.choice inferInstance
  have hrN : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (N (er (2*(n+1)) t) x - N (trueNuisance M L) x)^2 ∂xLaw M)
      atTop (fun _ _ => 0) := by
    simp only [er, hN]
    simpa only [N, contComponent] using
      nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hr (8,k,j,z0)
  have hrW : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (W (er (2*(n+1)) t) x - W (trueNuisance M L) x)^2 ∂xLaw M)
      atTop (fun _ _ => 0) := by
    simp only [er, hW]
    simpa only [W] using
      encoded_continuous_policy_width_sq_tendsto_probability_zero
        M μ phi dphi hphi hd hDerivative L he0 eh hclip hshares hm hr k j
  have hs := dml_ae_weighted_residual_sq_tendsto_probability_zero μ (xLaw M)
    (N (trueNuisance M L)) (W (trueNuisance M L))
    (fun n t => N (er (2*(n+1)) t)) (fun n t => W (er (2*(n+1)) t))
    (|M.yMin| + |M.yMax|) 2 (hn _ he0).1 (hw _ he0).1
    (fun n t => (hn _ (her _ t)).1) (fun n t => (hw _ (her _ t)).1)
    (fun n t => (hn _ (her _ t)).sub (hn _ he0))
    (fun n t => (hw _ (her _ t)).sub (hw _ he0))
    (fun n t => continuous_admissible_nuValue_abs_bound M L _ (her _ t) k j)
    (fun _ _ => fitted_continuous_policy_width_abs_bound M phi hphi L _ he0 k j hk hj)
    hrN hrW
  simp only [er, hN, hW] at hs
  exact hs

-- @node: encoded_continuous_quantile_policy_width_l2_tendsto_probability_zero
/-- Assume [a valid policy map](hyp:hphi) [with the specified derivative](hyp:hd),
[a bounded Lipschitz derivative](hyp:hDerivative), [admissible true nuisances](hyp:he0),
[clipped fitted nuisances](hyp:hclip), [fitted share simplexes](hyp:hshares),
[measurable fitted components](hyp:hm), and [encoded componentwise L² errors toward truth
smaller in probability than the inverse fourth root of sample size](hyp:hr).
If [the level index is below the number of levels](hyp:hk) and [the boundary index does
not exceed the number of boundaries at that level](hyp:hj), [the covariate L² error of
the fitted quantile-weighted policy width converges in probability to zero along sample
sizes twice one plus the index](goal). -/
lemma encoded_continuous_quantile_policy_width_l2_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L))) (k j : ℕ)
    (hk : k < L.K) (hj : j ≤ L.l k) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => Real.sqrt (∫ x,
        (nuValue M (eh (2*(n+1)) t) k j x *
            (pooledQ phi L (eh (2*(n+1)) t) k j x -
              positiveValue (eh (2*(n+1)) t).pLev k x) -
          nuValue M (trueNuisance M L) k j x *
            (pooledQ phi L (trueNuisance M L) k j x -
              positiveValue (trueNuisance M L).pLev k x))^2 ∂xLaw M))
      atTop (fun _ _ => 0) := by
  have hs := encoded_continuous_quantile_policy_width_sq_tendsto_probability_zero
    M μ phi dphi hphi hd hDerivative L he0 eh hclip hshares hm hr k j hk hj
  have hc : Continuous (fun t : ℝ => Real.sqrt t) := by fun_prop
  simpa only [Real.sqrt_zero] using
    Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt hc.continuousAt hs

end Papers.TbsPrteOptimalTransport
