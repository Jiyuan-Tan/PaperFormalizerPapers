module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLGammaBandBlock
/-! L2 convergence of continuous outcome bands and their product-share correction.
The event multiplier is fixed by the oracle level sets. Its energy is controlled
by the original propensity and band-mean rates, while the fitted gamma term uses
its own component rate. -/
@[expose] public section
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option linter.unusedFintypeInType false
set_option linter.unusedSimpArgs false
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

-- @node: fitted_continuous_band_product_memLp
/-- For [an admissible continuous nuisance fit](hyp:he), [the product of the fitted
treatment probability and band mean, on either the upper or lower side of a band,
is square-integrable under the covariate distribution](goal). -/
lemma fitted_continuous_band_product_memLp (M : LatentIVModel Ω X Z)
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e)
    (plus : Bool) (k j : ℕ) :
    MemLp (fun x => positiveValue e.pLev (if plus then k+1 else k) x *
      (if plus then meanValue e.Jplus k j x else minusMeanValue e.Jminus k j x))
      2 (xLaw M) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  have hp := (fitted_continuous_full_coordinates M L e he (if plus then k+1 else k)).1
  have hm : Measurable (fun x => if plus then meanValue e.Jplus k j x
      else minusMeanValue e.Jminus k j x) := by
    cases plus <;> simp only [Bool.false_eq_true, Bool.true_eq, if_false, if_true] <;> fun_prop
  have hb : ∀ᵐ x ∂xLaw M, |if plus then meanValue e.Jplus k j x
      else minusMeanValue e.Jminus k j x| ≤ |M.yMin| + |M.yMax| := by
    have hh := continuous_admissible_band_means_abs_bound M L e he k j
    cases plus
    · simpa using hh.2
    · simpa using hh.1
  apply MemLp.of_bound (by first | fun_prop | exact (hp.1.mul hm).aestronglyMeasurable)
    (|M.yMin| + |M.yMax|)
  filter_upwards [hp.2, hb] with x hx hy
  rw [Real.norm_eq_abs, abs_mul]
  exact (mul_le_mul hx hy (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

-- @node: fitted_contJ_memLp
/-- If [the continuous nuisance fit is admissible](hyp:he), [the fitted band moment,
the upper probability-weighted mean minus the lower one, is square-integrable under
the covariate distribution](goal). -/
lemma fitted_contJ_memLp (M : LatentIVModel Ω X Z)
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e) (k j : ℕ) :
    MemLp (fun x => contJ L e k j x) 2 (xLaw M) := by
  convert (fitted_continuous_band_product_memLp M L e he true k j).sub
    (fitted_continuous_band_product_memLp M L e he false k j) using 1
  funext x
  simp only [contJ, Pi.sub_apply, Bool.true_eq, Bool.false_eq_true, if_true, if_false]

-- @node: encoded_contJ_sq_tendsto_probability_zero
/-- Suppose [the population nuisance is admissible](hyp:he0), the fitted nuisances
[satisfy clipping restrictions](hyp:hclip), [have shares in the simplex](hyp:hshares),
[have measurable encoded components](hyp:hm), and [each encoded component's L²
error relative to its population counterpart vanishes faster in probability than
the inverse fourth root of sample size](hyp:hr). Then [the covariate
integral of the squared fitted band-moment error, at sample sizes twice one plus
the index, converges to zero in probability under the training-data measure](goal). -/
lemma encoded_contJ_sq_tendsto_probability_zero (M : LatentIVModel Ω X Z)
    (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L))) (k j : ℕ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (contJ L (eh (2*(n+1)) t) k j x -
        contJ L (trueNuisance M L) k j x)^2 ∂xLaw M) atTop (fun _ _ => 0) := by
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  let P := fun (e : NuisanceCont L) (b : Bool) x =>
    positiveValue e.pLev (if b then k+1 else k) x
  let J := fun (e : NuisanceCont L) (b : Bool) x =>
    if b then meanValue e.Jplus k j x else minusMeanValue e.Jminus k j x
  have hP (e : NuisanceCont L) (he : ContAdmissible M L e) (b : Bool) :
      Measurable (P e b) ∧ ∀ᵐ x ∂xLaw M, |P e b x| ≤ 1 :=
    (fitted_continuous_full_coordinates M L e he (if b then k+1 else k)).1
  have hJ (e : NuisanceCont L) (he : ContAdmissible M L e) (b : Bool) :
      Measurable (J e b) ∧ ∀ᵐ x ∂xLaw M, |J e b x| ≤ |M.yMin| + |M.yMax| := by
    refine ⟨?_, ?_⟩
    · cases b <;> simp only [J, Bool.false_eq_true, Bool.true_eq, if_false, if_true] <;> fun_prop
    · have hh := continuous_admissible_band_means_abs_bound M L e he k j
      cases b
      · simpa only [J, Bool.false_eq_true, if_false] using hh.2
      · simpa only [J, Bool.true_eq, if_true] using hh.1
  have hmem (f : X → ℝ) (hf : Measurable f) (R : ℝ)
      (hb : ∀ᵐ x ∂xLaw M, |f x| ≤ R) : MemLp f 2 (xLaw M) :=
    MemLp.of_bound hf.aestronglyMeasurable R (by simpa only [Real.norm_eq_abs] using hb)
  let z0 : Z := Classical.choice inferInstance
  have hprod (b : Bool) : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (P (er (2*(n+1)) t) b x * J (er (2*(n+1)) t) b x -
        P (trueNuisance M L) b x * J (trueNuisance M L) b x)^2 ∂xLaw M)
      atTop (fun _ _ => 0) := by
    apply dml_weighted_residual_sq_tendsto_probability_zero μ (xLaw M)
      (P (trueNuisance M L) b) (J (trueNuisance M L) b)
      (fun n t => P (er (2*(n+1)) t) b) (fun n t => J (er (2*(n+1)) t) b)
      1 (|M.yMin| + |M.yMax|) (hP _ he0 b).1 (hJ _ he0 b).1
      (fun n t => (hP _ (her _ t) b).1) (fun n t => (hJ _ (her _ t) b).1)
      (fun n t => (hmem _ (hP _ (her _ t) b).1 _ (hP _ (her _ t) b).2).sub
        (hmem _ (hP _ he0 b).1 _ (hP _ he0 b).2))
      (fun n t => (hmem _ (hJ _ (her _ t) b).1 _ (hJ _ (her _ t) b).2).sub
        (hmem _ (hJ _ he0 b).1 _ (hJ _ he0 b).2))
      (fun n t => (hP _ (her _ t) b).2) (fun _ _ => (hJ _ he0 b).2)
    · simpa only [P, er, restrictContShares, contComponent] using
        nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hr
          (1, (if b then k+1 else k), 0, z0)
    · cases b
      · simpa only [J, er, restrictContShares, contComponent, Bool.false_eq_true, if_false] using
          nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hr (12, k, j, z0)
      · simpa only [J, er, restrictContShares, contComponent, Bool.true_eq, if_true] using
          nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hr (11, k, j, z0)
  let F := fun b n t x => P (er (2*(n+1)) t) b x * J (er (2*(n+1)) t) b x -
    P (trueNuisance M L) b x * J (trueNuisance M L) b x
  have hF b n t : MemLp (F b n t) 2 (xLaw M) :=
    (fitted_continuous_band_product_memLp M L _ (her _ t) b k j).sub
      (fitted_continuous_band_product_memLp M L _ he0 b k j)
  have hz : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun (_ : ℕ) (_ : A) => (0 : ℝ)) atTop (fun _ _ => 0) := by
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
    intro eps heps
    simpa [not_le_of_gt heps] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
  have hs := dml_three_term_sq_tendsto_probability_zero μ (xLaw M)
    (F true) (fun _ _ _ => 0) (F false) (hF true) (fun _ _ => MemLp.zero')
    (hF false) (hprod true) (by simpa using hz) (hprod false)
  have hid n t x : contJ L (eh (2*(n+1)) t) k j x -
      contJ L (trueNuisance M L) k j x = F true n t x + 0 - F false n t x := by
    simp only [F, P, J, er, restrictContShares, contJ,
      Bool.true_eq, Bool.false_eq_true, if_true, if_false]
    ring
  simpa only [← hid] using hs

-- @node: fitted_contJ_measurable
/-- For [an admissible continuous nuisance fit](hyp:he), [the fitted band moment is
a measurable function of covariates](goal). -/
@[fun_prop] lemma fitted_contJ_measurable (M : LatentIVModel Ω X Z)
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e) (k j : ℕ) :
    Measurable (fun x => contJ L e k j x) := by
  first | fun_prop | skip
  have hp := (fitted_continuous_full_coordinates M L e he k).1.1
  have hp' := (fitted_continuous_full_coordinates M L e he (k+1)).1.1
  unfold contJ
  fun_prop

-- @node: fitted_continuous_band_event_memLp
/-- If [the continuous nuisance fit is admissible](hyp:he), [its band moment
multiplied by the indicator that the instrument belongs to the specified policy
union is square-integrable under the observation distribution](goal). -/
lemma fitted_continuous_band_event_memLp (M : LatentIVModel Ω X Z)
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e) (k j b : ℕ) :
    MemLp (fun o : Obs X Z => indicator (o.2.1 ∈ policyUnion L k j) *
      contJ L e k b o.1) 2 (observationLaw M) := by
  have hd := (fitted_contJ_memLp M L e he k b).comp_measurePreserving
    (observationLaw_fst_measurePreserving M)
  have hj := fitted_contJ_measurable M L e he k b
  have hev : Measurable (fun o : Obs X Z => indicator (o.2.1 ∈ policyUnion L k j)) := by
    fun_prop
  apply hd.norm.mono' (by fun_prop)
  apply Eventually.of_forall
  intro o
  rw [norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  simp only [Real.norm_eq_abs, indicator]
  split_ifs <;> norm_num

-- @node: encoded_continuous_band_event_sq_tendsto_probability_zero
/-- Assume [the population nuisance is admissible](hyp:he0), and the fitted nuisances
[are clipped](hyp:hclip), [have simplex-valued shares](hyp:hshares), [have measurable
encoded components](hyp:hm), and [have componentwise L² errors that vanish faster
in probability than the inverse fourth root of sample size](hyp:hr).
Then [the observation integral of the squared band-moment error multiplied by the
policy-union indicator converges to zero in probability, along sample sizes twice
one plus the index](goal). -/
lemma encoded_continuous_band_event_sq_tendsto_probability_zero (M : LatentIVModel Ω X Z)
    (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L))) (k j b : ℕ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o : Obs X Z,
        (indicator (o.2.1 ∈ policyUnion L k j) *
          (contJ L (eh (2*(n+1)) t) k b o.1 -
            contJ L (trueNuisance M L) k b o.1))^2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  have hs := encoded_contJ_sq_tendsto_probability_zero M μ L he0 eh hclip hshares hm hr k b
  have hi n t := observationLaw_covariate_integral M
    (fun x => (contJ L (er (2*(n+1)) t) k b x - contJ L (trueNuisance M L) k b x)^2)
    (by
      first | fun_prop | exact
        ((fitted_contJ_measurable M L _ (her (2*(n+1)) t) k b).sub
          (fitted_contJ_measurable M L _ he0 k b)).pow_const 2)
  have hs' : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o : Obs X Z,
        (contJ L (er (2*(n+1)) t) k b o.1 -
          contJ L (trueNuisance M L) k b o.1)^2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
    convert hs using 1
    funext n t
    exact hi n t
  have hs'' : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o : Obs X Z,
        (indicator (o.2.1 ∈ policyUnion L k j) *
          (contJ L (er (2*(n+1)) t) k b o.1 -
            contJ L (trueNuisance M L) k b o.1))^2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
    apply probability_zero_of_nonneg_le μ _ _ hs'
    intro n
    apply Eventually.of_forall
    intro t
    have hd := ((fitted_contJ_memLp M L _ (her (2*(n+1)) t) k b).sub
      (fitted_contJ_memLp M L _ he0 k b)).comp_measurePreserving
        (observationLaw_fst_measurePreserving M)
    have hw := (fitted_continuous_band_event_memLp M L _ (her (2*(n+1)) t) k j b).sub
      (fitted_continuous_band_event_memLp M L _ he0 k j b)
    have hw' : MemLp (fun o : Obs X Z => indicator (o.2.1 ∈ policyUnion L k j) *
        (contJ L (er (2*(n+1)) t) k b o.1 - contJ L (trueNuisance M L) k b o.1))
        2 (observationLaw M) := by
      convert hw using 1
      funext o
      simp only [Pi.sub_apply]
      ring
    refine ⟨integral_nonneg (fun o => sq_nonneg _), ?_⟩
    apply integral_mono hw'.integrable_sq hd.integrable_sq
    intro o
    dsimp only [Function.comp_apply, Pi.sub_apply]
    rw [mul_pow]
    have hb : indicator (o.2.1 ∈ policyUnion L k j)^2 ≤ 1 := by
      unfold indicator
      split_ifs <;> norm_num
    exact mul_le_of_le_one_left (sq_nonneg _) hb
  simpa only [er, restrictContShares, contJ] using hs''

-- @node: continuousBandShareCorrection
/-- For [a system of treatment levels and policy bands](hyp:L), [a continuous
nuisance fit](hyp:e), and [an observed covariate, instrument, treatment, and
outcome record](hyp:o), [the continuous band share correction](goal) is the sum
over all nonterminal levels and their policy bands of the fitted band moment
times the difference between policy-union membership and its fitted share. -/
noncomputable def continuousBandShareCorrection (L : LevelData Z X)
    (e : NuisanceCont L) (o : Obs X Z) : ℝ :=
  ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
    contJ L e k (j-1) o.1 *
      (indicator (o.2.1 ∈ policyUnion L k j) - regularValue e.gamma k j o.1)

-- @node: fitted_continuous_band_share_correction_memLp
/-- For [an admissible continuous nuisance fit](hyp:he), [the complete continuous
band share correction is square-integrable under the observation distribution](goal). -/
lemma fitted_continuous_band_share_correction_memLp (M : LatentIVModel Ω X Z)
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e) :
    MemLp (continuousBandShareCorrection L e) 2 (observationLaw M) := by
  unfold continuousBandShareCorrection
  apply memLp_finsetSum
  intro k hk
  apply memLp_finsetSum
  intro j hj
  have hg : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k :=
    ⟨(Finset.mem_range.mp hk).le, Finset.mem_Icc.mp hj⟩
  convert (fitted_continuous_band_event_memLp M L e he k j (j-1)).sub
    (fitted_continuous_gamma_contJ_memLp M L e he ⟨(k,j), hg⟩ k (j-1)) using 1
  funext o
  simp only [regularValue, dif_pos hg, Pi.sub_apply]
  ring

-- @node: encoded_continuous_band_share_correction_sq_tendsto_probability_zero
/-- Suppose [the population nuisance is admissible](hyp:he0), and fitted nuisances
[satisfy clipping](hyp:hclip), [have simplex-valued shares](hyp:hshares), [have
measurable encoded components](hyp:hm), and [have componentwise L² errors that
vanish faster in probability than the inverse fourth root of sample size](hyp:hr).
Then [the observation integral of the squared difference
between fitted and population band share corrections converges to zero in
probability, along sample sizes twice one plus the index](goal). -/
lemma encoded_continuous_band_share_correction_sq_tendsto_probability_zero
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
        (continuousBandShareCorrection L (eh (2*(n+1)) t) o -
          continuousBandShareCorrection L (trueNuisance M L) o)^2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  let F := fun k j n t (o : Obs X Z) =>
    contJ L (er (2*(n+1)) t) k (j-1) o.1 *
      (indicator (o.2.1 ∈ policyUnion L k j) - regularValue (er (2*(n+1)) t).gamma k j o.1) -
    contJ L (trueNuisance M L) k (j-1) o.1 *
      (indicator (o.2.1 ∈ policyUnion L k j) - regularValue (trueNuisance M L).gamma k j o.1)
  have hF k j n t (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
      MemLp (F k j n t) 2 (observationLaw M) := by
    have hg : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k := ⟨hk.le, hj⟩
    have hb (e : NuisanceCont L) (he : ContAdmissible M L e) :
        MemLp (fun o : Obs X Z => contJ L e k (j-1) o.1 *
          (indicator (o.2.1 ∈ policyUnion L k j) - regularValue e.gamma k j o.1))
          2 (observationLaw M) := by
      convert (fitted_continuous_band_event_memLp M L e he k j (j-1)).sub
        (fitted_continuous_gamma_contJ_memLp M L e he ⟨(k,j), hg⟩ k (j-1)) using 1
      funext o
      simp only [regularValue, dif_pos hg, Pi.sub_apply]
      ring
    exact (hb _ (her _ t)).sub (hb _ he0)
  have hrF k j (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
      Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
        (fun n t => ∫ o, (F k j n t o)^2 ∂observationLaw M)
        atTop (fun _ _ => 0) := by
    have hg : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k := ⟨hk.le, hj⟩
    let E := fun n t (o : Obs X Z) => indicator (o.2.1 ∈ policyUnion L k j) *
      (contJ L (er (2*(n+1)) t) k (j-1) o.1 - contJ L (trueNuisance M L) k (j-1) o.1)
    let G := fun n t (o : Obs X Z) => (er (2*(n+1)) t).gamma ⟨(k,j), hg⟩ o.1 *
      contJ L (er (2*(n+1)) t) k (j-1) o.1 -
      (trueNuisance M L).gamma ⟨(k,j), hg⟩ o.1 * contJ L (trueNuisance M L) k (j-1) o.1
    have hE n t : MemLp (E n t) 2 (observationLaw M) := by
      convert (fitted_continuous_band_event_memLp M L _ (her (2*(n+1)) t) k j (j-1)).sub
        (fitted_continuous_band_event_memLp M L _ he0 k j (j-1)) using 1
      funext o
      simp only [E, Pi.sub_apply]
      ring
    have hG n t : MemLp (G n t) 2 (observationLaw M) :=
      (fitted_continuous_gamma_contJ_memLp M L _ (her _ t) ⟨(k,j), hg⟩ k (j-1)).sub
        (fitted_continuous_gamma_contJ_memLp M L _ he0 ⟨(k,j), hg⟩ k (j-1))
    have hrE : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
        (fun n t => ∫ o, (E n t o)^2 ∂observationLaw M) atTop (fun _ _ => 0) := by
      simpa only [E, er, restrictContShares, contJ] using
        encoded_continuous_band_event_sq_tendsto_probability_zero
          M μ L he0 eh hclip hshares hm hr k j (j-1)
    have hrG : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
        (fun n t => ∫ o, (G n t o)^2 ∂observationLaw M) atTop (fun _ _ => 0) := by
      simpa only [G, er, restrictContShares, contJ] using
        encoded_continuous_gamma_contJ_sq_tendsto_probability_zero
          M μ L he0 eh hclip hshares hm hr ⟨(k,j), hg⟩ k (j-1)
    have hz : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
        (fun (_ : ℕ) (_ : A) => (0 : ℝ)) atTop (fun _ _ => 0) := by
      rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
      intro eps heps
      simpa [not_le_of_gt heps] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
    have hs := dml_three_term_sq_tendsto_probability_zero μ (observationLaw M)
      E (fun _ _ _ => 0) G hE (fun _ _ => MemLp.zero') hG hrE (by simpa using hz) hrG
    have hid n t o : F k j n t o = E n t o + 0 - G n t o := by
      simp only [F, E, G, regularValue, dif_pos hg]
      ring
    simpa only [← hid] using hs
  have hs := dml_finset_sum_sq_tendsto_probability_zero μ (observationLaw M)
    (Finset.range L.K) (fun k n t o => ∑ j ∈ Finset.Icc 1 (L.l k), F k j n t o)
    (fun k hk n t => memLp_finsetSum _ (fun j hj =>
      hF k j n t (Finset.mem_range.mp hk) (Finset.mem_Icc.mp hj))) (by
      intro k hk
      apply dml_finset_sum_sq_tendsto_probability_zero μ (observationLaw M)
        (Finset.Icc 1 (L.l k)) (F k)
        (fun j hj n t => hF k j n t (Finset.mem_range.mp hk) (Finset.mem_Icc.mp hj))
      intro j hj
      exact hrF k j (Finset.mem_range.mp hk) (Finset.mem_Icc.mp hj))
  simpa only [continuousBandShareCorrection, F, er, restrictContShares, contJ,
    regularValue, Finset.sum_sub_distrib] using hs

-- @node: encoded_continuous_band_share_correction_l2_tendsto_probability_zero
/-- With [an admissible population nuisance](hyp:he0) and fitted nuisances that
[are clipped](hyp:hclip), [have shares in the simplex](hyp:hshares), [have measurable
encoded components](hyp:hm), and [have componentwise L² errors that vanish faster
in probability than the inverse fourth root of sample size](hyp:hr),
[the square root of the observation-integrated squared error of the band share
correction converges to zero in probability, along sample sizes twice one plus
the index](goal). -/
lemma encoded_continuous_band_share_correction_l2_tendsto_probability_zero
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
        (continuousBandShareCorrection L (eh (2*(n+1)) t) o -
          continuousBandShareCorrection L (trueNuisance M L) o)^2 ∂observationLaw M))
      atTop (fun _ _ => 0) := by
  have hs := encoded_continuous_band_share_correction_sq_tendsto_probability_zero
    M μ L he0 eh hclip hshares hm hr
  have hcont : Continuous (fun t : ℝ => Real.sqrt t) := by fun_prop
  simpa only [Real.sqrt_zero] using
    Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt hcont.continuousAt hs

end Papers.TbsPrteOptimalTransport
