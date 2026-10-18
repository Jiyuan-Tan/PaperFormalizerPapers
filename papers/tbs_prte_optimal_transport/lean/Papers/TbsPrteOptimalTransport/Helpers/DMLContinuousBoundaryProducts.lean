module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousBandCoreConvergence
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousMovingPropensity
/-! Boundary probability products in the continuous fractional quantile moment.
Clipping bounds both factors, and the encoded component rates control their
product without a density assumption or a score-convergence premise. -/
public section
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSimpArgs false
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

-- @node: fitted_continuous_boundary_product_memLp
/-- For [an admissible continuous nuisance fit](hyp:he), [the product of the
fitted treatment probability and the matching upper or lower boundary probability
is square-integrable under the covariate distribution](goal). -/
lemma fitted_continuous_boundary_product_memLp (M : LatentIVModel Ω X Z)
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e)
    (plus : Bool) (k j : ℕ) :
    MemLp (fun x => positiveValue e.pLev (if plus then k+1 else k) x *
      (if plus then boundaryValue e.Mplus k j x else minusBoundaryValue e.Mminus k j x))
      2 (xLaw M) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  have hp := (fitted_continuous_full_coordinates M L e he (if plus then k+1 else k)).1
  have hb := continuous_admissible_boundary_values_regular M L e he k j
  have hm : Measurable (fun x => if plus then boundaryValue e.Mplus k j x
      else minusBoundaryValue e.Mminus k j x) := by
    cases plus <;> simp only [Bool.false_eq_true, Bool.true_eq, if_false, if_true] <;>
      first | fun_prop | exact hb.1.1 | exact hb.2.1
  have hbound : ∀ᵐ x ∂xLaw M, |if plus then boundaryValue e.Mplus k j x
      else minusBoundaryValue e.Mminus k j x| ≤ 1 := by
    cases plus
    · simpa using hb.2.2
    · simpa using hb.1.2
  apply MemLp.of_bound (by first | fun_prop | exact (hp.1.mul hm).aestronglyMeasurable) 1
  filter_upwards [hp.2, hbound] with x hx hy
  rw [Real.norm_eq_abs, abs_mul]
  exact (mul_le_mul hx hy (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

-- @node: encoded_continuous_boundary_product_sq_tendsto_probability_zero
/-- If [the population nuisance is admissible](hyp:he0) and fitted nuisances
[are clipped](hyp:hclip), [have simplex-valued shares](hyp:hshares), [have measurable
encoded components](hyp:hm), and [have componentwise L² errors that vanish faster
in probability than the inverse fourth root of sample size](hyp:hr),
[the covariate-integrated squared error of the selected treatment-probability
times boundary-probability product converges to zero in probability, along
sample sizes twice one plus the index](goal). -/
lemma encoded_continuous_boundary_product_sq_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L))) (plus : Bool) (k j : ℕ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x,
        (positiveValue (eh (2*(n+1)) t).pLev (if plus then k+1 else k) x *
            (if plus then boundaryValue (eh (2*(n+1)) t).Mplus k j x
              else minusBoundaryValue (eh (2*(n+1)) t).Mminus k j x) -
          positiveValue (trueNuisance M L).pLev (if plus then k+1 else k) x *
            (if plus then boundaryValue (trueNuisance M L).Mplus k j x
              else minusBoundaryValue (trueNuisance M L).Mminus k j x))^2 ∂xLaw M)
      atTop (fun _ _ => 0) := by
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  let P := fun (e : NuisanceCont L) => positiveValue e.pLev (if plus then k+1 else k)
  let B := fun (e : NuisanceCont L) x =>
    if plus then boundaryValue e.Mplus k j x else minusBoundaryValue e.Mminus k j x
  have hP (e : NuisanceCont L) (he : ContAdmissible M L e) :
      Measurable (P e) ∧ ∀ᵐ x ∂xLaw M, |P e x| ≤ 1 :=
    (fitted_continuous_full_coordinates M L e he _).1
  have hB (e : NuisanceCont L) (he : ContAdmissible M L e) :
      Measurable (B e) ∧ ∀ᵐ x ∂xLaw M, |B e x| ≤ 1 := by
    have hb := continuous_admissible_boundary_values_regular M L e he k j
    cases plus
    · simpa only [B, Bool.false_eq_true, if_false] using hb.2
    · simpa only [B, Bool.true_eq, if_true] using hb.1
  have hmem (f : X → ℝ) (hf : Measurable f)
      (hb : ∀ᵐ x ∂xLaw M, |f x| ≤ 1) : MemLp f 2 (xLaw M) :=
    MemLp.of_bound hf.aestronglyMeasurable 1 (by simpa only [Real.norm_eq_abs] using hb)
  let z0 : Z := Classical.choice inferInstance
  have hrP : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (P (er (2*(n+1)) t) x - P (trueNuisance M L) x)^2 ∂xLaw M)
      atTop (fun _ _ => 0) := by
    simpa only [P, er, restrictContShares, contComponent] using
      nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hr
        (1, (if plus then k+1 else k), 0, z0)
  have hrB : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (B (er (2*(n+1)) t) x - B (trueNuisance M L) x)^2 ∂xLaw M)
      atTop (fun _ _ => 0) := by
    cases plus
    · simpa only [B, Bool.false_eq_true, if_false, er, restrictContShares, contComponent] using
        nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hr (10, k, j, z0)
    · simpa only [B, Bool.true_eq, if_true, er, restrictContShares, contComponent] using
        nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hr (9, k, j, z0)
  have hs := dml_weighted_residual_sq_tendsto_probability_zero μ (xLaw M)
    (P (trueNuisance M L)) (B (trueNuisance M L))
    (fun n t => P (er (2*(n+1)) t)) (fun n t => B (er (2*(n+1)) t)) 1 1
    (hP _ he0).1 (hB _ he0).1 (fun n t => (hP _ (her _ t)).1)
    (fun n t => (hB _ (her _ t)).1)
    (fun n t => (hmem _ (hP _ (her _ t)).1 (hP _ (her _ t)).2).sub
      (hmem _ (hP _ he0).1 (hP _ he0).2))
    (fun n t => (hmem _ (hB _ (her _ t)).1 (hB _ (her _ t)).2).sub
      (hmem _ (hB _ he0).1 (hB _ he0).2))
    (fun n t => (hP _ (her _ t)).2) (fun _ _ => (hB _ he0).2) hrP hrB
  simpa only [P, B, er, restrictContShares] using hs

-- @node: fitted_continuous_boundary_contrast_memLp
/-- If [the continuous nuisance fit is admissible](hyp:he), [the upper
treatment-probability-weighted boundary probability minus its lower counterpart
is square-integrable under the covariate distribution](goal). -/
lemma fitted_continuous_boundary_contrast_memLp (M : LatentIVModel Ω X Z)
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e) (k j : ℕ) :
    MemLp (fun x => positiveValue e.pLev (k+1) x * boundaryValue e.Mplus k j x -
      positiveValue e.pLev k x * minusBoundaryValue e.Mminus k j x) 2 (xLaw M) := by
  simpa only [Bool.true_eq, Bool.false_eq_true, if_true, if_false, Pi.sub_def] using
    (fitted_continuous_boundary_product_memLp M L e he true k j).sub
      (fitted_continuous_boundary_product_memLp M L e he false k j)

-- @node: encoded_continuous_boundary_contrast_sq_tendsto_probability_zero
/-- Assume [population nuisance admissibility](hyp:he0), [clipped fitted
nuisances](hyp:hclip), [simplex-valued fitted shares](hyp:hshares), [measurable
encoded components](hyp:hm), and [componentwise L² errors that vanish faster in
probability than the inverse fourth root of sample size](hyp:hr). Then [the
covariate integral of the squared error in the upper-minus-lower
treatment-probability-weighted boundary contrast converges to zero in probability,
along sample sizes twice one plus the index](goal). -/
lemma encoded_continuous_boundary_contrast_sq_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L))) (k j : ℕ) :
    let contrast := fun (e : NuisanceCont L) x =>
      positiveValue e.pLev (k+1) x * boundaryValue e.Mplus k j x -
        positiveValue e.pLev k x * minusBoundaryValue e.Mminus k j x
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (contrast (eh (2*(n+1)) t) x -
        contrast (trueNuisance M L) x)^2 ∂xLaw M) atTop (fun _ _ => 0) := by
  dsimp only
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  let P := fun (e : NuisanceCont L) (b : Bool) x =>
    positiveValue e.pLev (if b then k+1 else k) x *
      (if b then boundaryValue e.Mplus k j x else minusBoundaryValue e.Mminus k j x)
  let F := fun (b : Bool) n t x => P (er (2*(n+1)) t) b x - P (trueNuisance M L) b x
  have hF b n t : MemLp (F b n t) 2 (xLaw M) :=
    (fitted_continuous_boundary_product_memLp M L _ (her _ t) b k j).sub
      (fitted_continuous_boundary_product_memLp M L _ he0 b k j)
  have hrF b : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (F b n t x)^2 ∂xLaw M) atTop (fun _ _ => 0) := by
    simpa only [F, P, er, restrictContShares] using
      encoded_continuous_boundary_product_sq_tendsto_probability_zero
        M μ L he0 eh hclip hshares hm hr b k j
  have hz : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun (_ : ℕ) (_ : A) => (0 : ℝ)) atTop (fun _ _ => 0) := by
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
    intro eps heps
    simpa [not_le_of_gt heps] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
  have hs := dml_three_term_sq_tendsto_probability_zero μ (xLaw M)
    (F true) (fun _ _ _ => 0) (F false) (hF true) (fun _ _ => MemLp.zero')
    (hF false) (hrF true) (by simpa using hz) (hrF false)
  convert hs using 1
  funext n t
  congr 1
  funext x
  simp only [F, P, er, restrictContShares, Bool.true_eq, Bool.false_eq_true, if_true, if_false]
  ring

-- @node: encoded_continuous_boundary_contrast_l2_tendsto_probability_zero
/-- Under [admissibility of the population nuisance](hyp:he0), [clipping of the
fits](hyp:hclip), [simplex-valued fitted shares](hyp:hshares), [measurability of
encoded components](hyp:hm), and [componentwise L² errors that vanish faster in
probability than the inverse fourth root of sample size](hyp:hr),
[the square root of the covariate-integrated squared error in the
upper-minus-lower treatment-probability-weighted boundary contrast converges to
zero in probability, along sample sizes twice one plus the index](goal). -/
lemma encoded_continuous_boundary_contrast_l2_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L))) (k j : ℕ) :
    let contrast := fun (e : NuisanceCont L) x =>
      positiveValue e.pLev (k+1) x * boundaryValue e.Mplus k j x -
        positiveValue e.pLev k x * minusBoundaryValue e.Mminus k j x
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => Real.sqrt (∫ x, (contrast (eh (2*(n+1)) t) x -
        contrast (trueNuisance M L) x)^2 ∂xLaw M)) atTop (fun _ _ => 0) := by
  have hs := encoded_continuous_boundary_contrast_sq_tendsto_probability_zero
    M μ L he0 eh hclip hshares hm hr k j
  have hc : Continuous (fun t : ℝ => Real.sqrt t) := by fun_prop
  simpa only [Real.sqrt_zero] using
    Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt hc.continuousAt hs

end Papers.TbsPrteOptimalTransport
