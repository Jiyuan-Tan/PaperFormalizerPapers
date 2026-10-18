module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousBandRegressionRates
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousBandShares
/-! Second-order product remainders for continuous outcome bands.
The propensity and band-mean rates give quarter-power rates for the plug-in
band target. Cauchy--Schwarz then controls its product with a gamma error. -/
public section
set_option linter.style.haveILetI false
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false
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
  [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z) (μ : Measure A)

-- @node: encoded_continuous_band_target_product_quarter_rate
/-- If [the reference nuisance is admissible](hyp:he0), [every fitted nuisance is
admissible](hyp:heh), and [the encoded nuisance errors vanish faster than the
inverse fourth root of sample size in probability](hyp:hr), then [the products
of treatment propensities and upper or lower band means satisfy the same
coordinatewise L² rate relative to the reference products](goal). -/
lemma encoded_continuous_band_target_product_quarter_rate
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L e0)) :
    FiniteNuisanceRates M μ
      (fun n a (i : Bool × (ℕ × ℕ)) x =>
        positiveValue (eh n a).pLev (if i.1 then i.2.1+1 else i.2.1) x *
          (if i.1 then meanValue (eh n a).Jplus i.2.1 i.2.2 x
            else minusMeanValue (eh n a).Jminus i.2.1 i.2.2 x))
      (fun i x => positiveValue e0.pLev (if i.1 then i.2.1+1 else i.2.1) x *
        (if i.1 then meanValue e0.Jplus i.2.1 i.2.2 x
          else minusMeanValue e0.Jminus i.2.1 i.2.2 x)) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  let P := fun (e : NuisanceCont L) (i : Bool × (ℕ × ℕ)) =>
    positiveValue e.pLev (if i.1 then i.2.1+1 else i.2.1)
  let J := fun (e : NuisanceCont L) (i : Bool × (ℕ × ℕ)) x =>
    if i.1 then meanValue e.Jplus i.2.1 i.2.2 x
      else minusMeanValue e.Jminus i.2.1 i.2.2 x
  have hp (e : NuisanceCont L) (he : ContAdmissible M L e) i :
      MemLp (P e i) 2 (xLaw M) := by
    obtain ⟨hm, hb⟩ := (fitted_continuous_full_coordinates M L e he
      (if i.1 then i.2.1+1 else i.2.1)).1
    apply MemLp.of_bound hm.aestronglyMeasurable 1
    simpa only [Real.norm_eq_abs] using hb
  have hj (e : NuisanceCont L) (he : ContAdmissible M L e) i :
      MemLp (J e i) 2 (xLaw M) := by
    dsimp only [J]
    split_ifs
    · exact fitted_continuous_meanValue_memLp M L e he i.2.1 i.2.2
    · exact fitted_continuous_minusMeanValue_memLp M L e he i.2.1 i.2.2
  let z0 : Z := Classical.choice inferInstance
  have hrp : FiniteNuisanceRates M μ (fun n a => P (eh n a)) (P e0) := by
    intro i
    simpa only [P, finiteL2Error, contComponent] using
      hr (1, (if i.1 then i.2.1+1 else i.2.1), 0, z0)
  have hrj : FiniteNuisanceRates M μ (fun n a => J (eh n a)) (J e0) := by
    intro i
    dsimp only [J]
    split_ifs
    · simpa only [finiteL2Error, contComponent] using hr (11, i.2.1, i.2.2, z0)
    · simpa only [finiteL2Error, contComponent] using hr (12, i.2.1, i.2.2, z0)
  apply nuisanceRates_bounded_product M μ _ _ _ _
    (fun n a => hp _ (heh n a)) (fun n a => hj _ (heh n a))
    (hp _ he0) (hj _ he0) (|M.yMin| + |M.yMax|) (by positivity) _ _ hrp hrj
  · intro n a i
    exact (fitted_continuous_full_coordinates M L _ (heh n a)
      (if i.1 then i.2.1+1 else i.2.1)).1.2
  · intro i
    have hb := continuous_admissible_band_means_abs_bound M L e0 he0 i.2.1 i.2.2
    dsimp only [J]
    split_ifs
    · exact hb.1
    · exact hb.2

-- @node: encoded_continuous_contJ_quarter_rate
/-- If [the reference nuisance is admissible](hyp:he0), [all fitted nuisances are
admissible](hyp:heh), and [their encoded errors have little-o fourth-root
rates](hyp:hr), then [each fitted continuous band target has an L² error that
vanishes faster than the inverse fourth root of sample size in probability](goal). -/
lemma encoded_continuous_contJ_quarter_rate
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L e0)) :
    FiniteNuisanceRates M μ (fun n a (i : ℕ × ℕ) => contJ L (eh n a) i.1 i.2)
      (fun i => contJ L e0 i.1 i.2) := by
  let F := fun (e : NuisanceCont L) (plus : Bool) (i : ℕ × ℕ) x =>
    positiveValue e.pLev (if plus then i.1+1 else i.1) x *
      (if plus then meanValue e.Jplus i.1 i.2 x else minusMeanValue e.Jminus i.1 i.2 x)
  have hf (e : NuisanceCont L) (he : ContAdmissible M L e) plus i :
      MemLp (F e plus i) 2 (xLaw M) :=
    fitted_continuous_band_product_memLp M L e he plus i.1 i.2
  have hrf plus : FiniteNuisanceRates M μ (fun n a => F (eh n a) plus) (F e0 plus) := by
    intro i
    simpa only [F, finiteL2Error] using
      encoded_continuous_band_target_product_quarter_rate M μ L e0 eh
        he0 heh hr (plus, i)
  have hs := nuisanceRates_sub M μ
      (fun n a => F (eh n a) true) (fun n a => F (eh n a) false)
      (F e0 true) (F e0 false) (fun n a => hf _ (heh n a) true)
      (fun n a => hf _ (heh n a) false) (hf _ he0 true) (hf _ he0 false)
      (hrf true) (hrf false)
  intro i
  simpa only [finiteL2Error, F, Bool.true_eq, Bool.false_eq_true, if_true, if_false, contJ]
    using hs i

-- @node: fitted_continuous_band_product_absolute_cross_error_bound
/-- For [an admissible reference nuisance](hyp:he0) and [an admissible fitted
nuisance](hyp:he), [the absolute product of the assignment-share error and the
preceding band-target error is integrable, and its covariate mean is bounded by
the product of their L² errors](goal). -/
lemma fitted_continuous_band_product_absolute_cross_error_bound
    (L : LevelData Z X) (e0 e : NuisanceCont L)
    (he0 : ContAdmissible M L e0) (he : ContAdmissible M L e) (k j : ℕ) :
    Integrable (fun x => |(regularValue e.gamma k j x - regularValue e0.gamma k j x) *
      (contJ L e k (j-1) x - contJ L e0 k (j-1) x)|) (xLaw M) ∧
    (∫ x, |(regularValue e.gamma k j x - regularValue e0.gamma k j x) *
      (contJ L e k (j-1) x - contJ L e0 k (j-1) x)| ∂xLaw M) ≤
      finiteL2Error M (regularValue e.gamma k j) (regularValue e0.gamma k j) *
        finiteL2Error M (contJ L e k (j-1)) (contJ L e0 k (j-1)) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  have hg (b : NuisanceCont L) (hb : ContAdmissible M L b) :
      MemLp (regularValue b.gamma k j) 2 (xLaw M) := by
    have hm : Measurable (regularValue b.gamma k j) := by
      first | fun_prop | skip
      rcases hb with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hm, _⟩
      unfold regularValue
      split_ifs
      · exact hm _
      · fun_prop
    apply MemLp.of_bound hm.aestronglyMeasurable 1
    rcases hb with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hb, _⟩
    unfold regularValue
    split_ifs with h
    · filter_upwards [hb ⟨(k,j),h⟩] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
      exact hx.2
    · exact Eventually.of_forall (fun _ => by norm_num)
  have hgd := (hg e he).sub (hg e0 he0)
  have hjd := (fitted_contJ_memLp M L e he k (j-1)).sub
    (fitted_contJ_memLp M L e0 he0 k (j-1))
  refine ⟨(hgd.integrable_mul hjd).abs, ?_⟩
  rw [l2Error_eq_eLpNorm M _ _ hgd, l2Error_eq_eLpNorm M _ _ hjd]
  exact Causalean.Stat.integral_abs_mul_le_eLpNorm_mul_eLpNorm hgd hjd

-- @node: encoded_continuous_band_product_cross_root_n_negligible
/-- If [the reference nuisance is admissible](hyp:he0), [all fitted nuisances are
admissible](hyp:heh), and [their encoded errors have little-o fourth-root
rates](hyp:hr), then [the covariate mean of the absolute assignment-share error
times the preceding band-target error, evaluated at sample size twice n plus
two and multiplied by the square root of n plus one, converges to zero in
probability](goal). -/
lemma encoded_continuous_band_product_cross_root_n_negligible
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L e0)) (k j : ℕ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        ∫ x, |(regularValue (eh (2*(n+1)) a).gamma k j x - regularValue e0.gamma k j x) *
          (contJ L (eh (2*(n+1)) a) k (j-1) x - contJ L e0 k (j-1) x)| ∂xLaw M)
      atTop (fun _ _ => 0) := by
  let z0 : Z := Classical.choice inferInstance
  have hg : Causalean.Stat.IsLittleOp
      (fun n a => finiteL2Error M (regularValue (eh (2*(n+1)) a).gamma k j)
        (regularValue e0.gamma k j))
      (fun n => ((2*(n+1) : ℕ) : ℝ)^(-1/4 : ℝ)) μ := by
    simpa only [finiteL2Error, contComponent] using hr (6,k,j,z0)
  have hj := encoded_continuous_contJ_quarter_rate M μ L e0 eh he0 heh hr (k,j-1)
  apply dml_root_n_bias_tendsto_probability μ
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul one_pos
    (dml_quarter_rate_product μ _ _ hg hj)
  intro n a
  rw [one_mul, abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))]
  exact (fitted_continuous_band_product_absolute_cross_error_bound M L e0
    (eh (2*(n+1)) a) he0 (heh _ a) k j).2.trans (le_abs_self _)

-- Absolute values make this finite assembly usable before any cancellation
-- in the population score mean. The index set can contain all regular bands.
-- @node: encoded_continuous_band_product_block_cross_root_n_negligible
/-- Under [reference admissibility](hyp:he0), [admissibility of every fitted
nuisance](hyp:heh), and [little-o fourth-root rates for the encoded nuisance
errors](hyp:hr), [the covariate mean of the finite sum of absolute products of
assignment-share and preceding band-target errors, using fits at size twice n
plus two and scaled by the square root of n plus one, converges to zero in
probability](goal). -/
lemma encoded_continuous_band_product_block_cross_root_n_negligible
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L e0)) (t : Finset (ℕ × ℕ)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        ∫ x, ∑ i ∈ t,
          |(regularValue (eh (2*(n+1)) a).gamma i.1 i.2 x -
              regularValue e0.gamma i.1 i.2 x) *
            (contJ L (eh (2*(n+1)) a) i.1 (i.2-1) x -
              contJ L e0 i.1 (i.2-1) x)| ∂xLaw M)
      atTop (fun _ _ => 0) := by
  let G := fun (e : NuisanceCont L) (i : ℕ × ℕ) => regularValue e.gamma i.1 i.2
  let J := fun (e : NuisanceCont L) (i : ℕ × ℕ) => contJ L e i.1 (i.2-1)
  let reg := fun n a => maxErrors (t.toList.map (fun i =>
    finiteL2Error M (J (eh (2*(n+1)) a) i) (J e0 i)))
  let wt := fun n a => maxErrors (t.toList.map (fun i =>
    finiteL2Error M (G (eh (2*(n+1)) a) i) (G e0 i)))
  have hrJ : FiniteNuisanceRates M μ (fun n a => J (eh n a)) (J e0) := by
    intro i
    simpa only [J, finiteL2Error] using
      encoded_continuous_contJ_quarter_rate M μ L e0 eh he0 heh hr (i.1,i.2-1)
  have hrG : FiniteNuisanceRates M μ (fun n a => G (eh n a)) (G e0) := by
    intro i
    let z0 : Z := Classical.choice inferInstance
    simpa only [G, finiteL2Error, contComponent] using hr (6,i.1,i.2,z0)
  have hreg := nuisanceRates_finite_maxErrors M μ
    (fun n a => J (eh n a)) (J e0) t.toList hrJ
  have hwt := nuisanceRates_finite_maxErrors M μ
    (fun n a => G (eh n a)) (G e0) t.toList hrG
  apply dml_root_n_bias_tendsto_probability μ
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul
    (by positivity : 0 < (t.card : ℝ) + 1)
    (dml_quarter_rate_product μ reg wt hreg hwt)
  intro n a
  rw [abs_of_nonneg (integral_nonneg (fun _ =>
    Finset.sum_nonneg (fun _ _ => abs_nonneg _))),
    abs_of_nonneg (mul_nonneg (maxErrors_nonneg _) (maxErrors_nonneg _))]
  have hi (i : ℕ × ℕ) := (fitted_continuous_band_product_absolute_cross_error_bound M L e0
    (eh (2*(n+1)) a) he0 (heh _ a) i.1 i.2).1
  rw [integral_finsetSum t (fun i _ => hi i)]
  calc
    _ ≤ ∑ i ∈ t, finiteL2Error M (G (eh (2*(n+1)) a) i) (G e0 i) *
        finiteL2Error M (J (eh (2*(n+1)) a) i) (J e0 i) := by
      apply Finset.sum_le_sum
      intro i _
      exact (fitted_continuous_band_product_absolute_cross_error_bound M L e0
        (eh (2*(n+1)) a) he0 (heh _ a) i.1 i.2).2
    _ ≤ ∑ _i ∈ t, wt n a * reg n a := by
      apply Finset.sum_le_sum
      intro i hit
      have hw : finiteL2Error M (G (eh (2*(n+1)) a) i) (G e0 i) ≤ wt n a :=
        le_maxErrors_of_mem (List.mem_map.mpr ⟨i, by simpa using hit, rfl⟩)
      have hj : finiteL2Error M (J (eh (2*(n+1)) a) i) (J e0 i) ≤ reg n a :=
        le_maxErrors_of_mem (List.mem_map.mpr ⟨i, by simpa using hit, rfl⟩)
      exact mul_le_mul hw hj (Real.sqrt_nonneg _) (maxErrors_nonneg _)
    _ = (t.card : ℝ) * (reg n a * wt n a) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith)
      (mul_nonneg (maxErrors_nonneg _) (maxErrors_nonneg _))

-- @node: continuous_band_product_fixed_gamma_difference
/-- If [two nuisances have identical assignment shares](hyp:hg), then [their
product-score difference at any observation equals the common fitted share
times the component-score difference, plus the band-target difference times
the policy-event indicator minus that fitted share](goal). -/
lemma continuous_band_product_fixed_gamma_difference
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e b : NuisanceCont L)
    (hg : e.gamma = b.gamma) (k j : ℕ) (o : Obs X Z) :
    psiProd M phi dphi L e k j o - psiProd M phi dphi L b k j o =
      regularValue e.gamma k j o.1 *
        (contScoreComponents M phi dphi L e k (j-1) o -
          contScoreComponents M phi dphi L b k (j-1) o) +
      (contJ L e k (j-1) o.1 - contJ L b k (j-1) o.1) *
        (indicator (o.2.1 ∈ policyUnion L k j) - regularValue e.gamma k j o.1) := by
  simp only [psiProd, hg]
  ring

end Papers.TbsPrteOptimalTransport
