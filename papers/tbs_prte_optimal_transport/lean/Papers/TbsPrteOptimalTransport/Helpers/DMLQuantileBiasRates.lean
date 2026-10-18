module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLIndicatorRates
/-! Quantile-boundary bias under local densities and clipped boundary estimates.
The remote-error bound comes from the outcome interval, and the integrated
quadratic bound converts the componentwise quarter rate into negligible bias. -/
public section
set_option linter.style.haveILetI false
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open scoped Classical Topology

-- @node: quantile_boundary_integral_clipped_bound
/-- For a finite outcome measure, if [the first endpoint lies in a fixed closed outcome interval](hyp:ha), [the second endpoint lies in that interval](hyp:hb), and [the measure has total mass at most one](hyp:hmass), [the absolute integral of the second endpoint minus the outcome over the interval between the endpoints, excluding the smaller endpoint and including the larger, is at most the width of the fixed outcome interval](goal). -/
lemma quantile_boundary_integral_clipped_bound (ν : Measure ℝ) [IsFiniteMeasure ν]
    (a b lo hi : ℝ) (ha : a ∈ Icc lo hi) (hb : b ∈ Icc lo hi)
    (hmass : ν.real univ ≤ 1) :
    |∫ y in Ioc (min a b) (max a b), b - y ∂ν| ≤ hi - lo := by
  have hwidth : 0 ≤ hi - lo := sub_nonneg.mpr (ha.1.trans ha.2)
  have hbound : ∀ᵐ y ∂ν.restrict (Ioc (min a b) (max a b)),
      ‖b - y‖ ≤ hi - lo := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    have hylo : lo ≤ y := (le_min ha.1 hb.1).trans hy.1.le
    have hyhi : y ≤ hi := hy.2.trans (max_le ha.2 hb.2)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hb.1, hb.2]
  have hmass' : (ν (Ioc (min a b) (max a b))).toReal ≤ 1 :=
    (measureReal_mono (subset_univ _)).trans hmass
  have h := norm_integral_le_of_norm_le_const hbound
  simp only [Real.norm_eq_abs, Measure.real, Measure.restrict_apply_univ] at h
  exact h.trans (by simpa using mul_le_mul_of_nonneg_left hmass' hwidth)

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: measurable_treatedLaw_quantile_boundary_remainder
/-- If [the first boundary is measurable in covariates](hyp:ha) and [the second boundary is measurable in covariates](hyp:hb), [the conditional treated-law integral of the second boundary minus the outcome over the interval between them, excluding the smaller boundary and including the larger, is measurable in covariates](goal). -/
@[fun_prop] lemma measurable_treatedLaw_quantile_boundary_remainder
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (k : ℕ)
    (a b : X → ℝ) (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun x => ∫ y in Ioc (min (a x) (b x)) (max (a x) (b x)),
      b x - y ∂treatedLaw M L k x) := by
  let κ := ProbabilityTheory.condDistrib
    (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure
  let t : Set (ℝ × ℝ × Z) := {z | z.2.1 = 1 ∧ z.2.2 ∈ (L.S k : Set Z)}
  have ht : MeasurableSet t :=
    (measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const).inter
      ((L.S k).measurableSet.preimage (measurable_snd.comp measurable_snd))
  let F : X × (ℝ × ℝ × Z) → ℝ := fun z =>
    if min (a z.1) (b z.1) < z.2.1 ∧ z.2.1 ≤ max (a z.1) (b z.1)
    then b z.1 - z.2.1 else 0
  have hF : StronglyMeasurable F := by
    apply Measurable.stronglyMeasurable
    dsimp only [F]
    apply Measurable.ite
      ((measurableSet_lt ((ha.comp measurable_fst).min (hb.comp measurable_fst))
        (measurable_fst.comp measurable_snd)).inter
        (measurableSet_le (measurable_fst.comp measurable_snd)
          ((ha.comp measurable_fst).max (hb.comp measurable_fst))))
    · fun_prop
    · fun_prop
  let G := (Prod.snd ⁻¹' t).indicator F
  have hG : StronglyMeasurable G := hF.indicator (ht.preimage measurable_snd)
  have hi : Measurable (fun x => ∫ z, G (x, z) ∂κ x) :=
    (hG.integral_kernel_prod_right').measurable
  have hm : Measurable (fun x => (κ x).restrict t univ) := by
    simpa only [Measure.restrict_apply_univ] using κ.measurable_coe ht
  have hid : (fun x => ∫ y in Ioc (min (a x) (b x)) (max (a x) (b x)),
      b x - y ∂treatedLaw M L k x) =
      (fun x => ((κ x).restrict t univ)⁻¹.toReal * ∫ z, G (x, z) ∂κ x) := by
    funext x
    rw [← integral_indicator measurableSet_Ioc]
    have hfx : StronglyMeasurable
        ((Ioc (min (a x) (b x)) (max (a x) (b x))).indicator (fun y => b x - y)) := by
      apply StronglyMeasurable.indicator _ measurableSet_Ioc
      fun_prop
    rw [treatedLaw, integral_smul_measure, smul_eq_mul,
      integral_map_of_stronglyMeasurable measurable_fst hfx]
    congr 1
    rw [← integral_indicator ht]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro z
    simp [G, F, Set.indicator, Set.mem_Ioc]
  rw [hid]
  fun_prop

-- @node: treatedLaw_quantile_boundary_integrated_quadratic
/-- Suppose [the reference boundary](hyp:ha) and [replacement boundary](hyp:hb) are measurable, [the reference boundary lies almost surely in the model's outcome interval](hyp:haRange), [the replacement boundary lies there almost surely](hyp:hbRange), [the neighborhood radius is positive](hyp:hr), [the density-bound constant is nonnegative](hyp:hC), and [almost surely every interval within that radius of the reference boundary has treated-law mass at most the constant times its length](hyp:hdensity). Then [the conditional boundary remainder is integrable over covariates, and the absolute value of its covariate integral is bounded by the squared covariate L2 distance between the boundaries multiplied by the sum of the density-bound constant and the outcome width divided by the squared radius](goal). -/
lemma treatedLaw_quantile_boundary_integrated_quadratic
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (k : ℕ)
    (a b : X → ℝ) (r C : ℝ) (ha : Measurable a) (hb : Measurable b)
    (haRange : ∀ᵐ x ∂xLaw M, a x ∈ Icc M.yMin M.yMax)
    (hbRange : ∀ᵐ x ∂xLaw M, b x ∈ Icc M.yMin M.yMax)
    (hr : 0 < r) (hC : 0 ≤ C)
    (hdensity : ∀ᵐ x ∂xLaw M, ∀ u v, a x - r ≤ u → u ≤ v → v ≤ a x + r →
      (treatedLaw M L k x (Ioc u v)).toReal ≤ C * (v - u)) :
    Integrable (fun x => ∫ y in Ioc (min (a x) (b x)) (max (a x) (b x)),
      b x - y ∂treatedLaw M L k x) (xLaw M) ∧
    |∫ x, ∫ y in Ioc (min (a x) (b x)) (max (a x) (b x)),
      b x - y ∂treatedLaw M L k x ∂xLaw M| ≤
      (C + (M.yMax - M.yMin) / r ^ 2) * finiteL2Error M b a ^ 2 := by
  haveI : IsProbabilityMeasure (xLaw M) :=
    Measure.isProbabilityMeasure_map M.measX.aemeasurable
  have hwidth : 0 ≤ M.yMax - M.yMin := by
    obtain ⟨x, hx⟩ := haRange.exists
    exact sub_nonneg.mpr (hx.1.trans hx.2)
  have hea : MemLp a 2 (xLaw M) := by
    apply memLp_of_bounded haRange
    fun_prop
  have heb : MemLp b 2 (xLaw M) := by
    apply memLp_of_bounded hbRange
    fun_prop
  have hR : Measurable (fun x => ∫ y in Ioc (min (a x) (b x)) (max (a x) (b x)),
      b x - y ∂treatedLaw M L k x) := by fun_prop
  have h := quantile_remainder_integrated_quadratic (xLaw M) _ (fun x => b x - a x)
    r C (M.yMax - M.yMin) hr hC hwidth hR.aestronglyMeasurable (heb.sub hea) ?_ ?_
  · refine ⟨h.1, ?_⟩
    simpa only [finiteL2Error, Real.sq_sqrt (integral_nonneg fun x => sq_nonneg (b x - a x))]
      using h.2
  · filter_upwards [hdensity] with x hx
    intro he
    let := treatedLaw_isFiniteMeasure M L k x
    simpa only [sq_abs] using quantile_boundary_integral_local
      (treatedLaw M L k x) (a x) (b x) r C he hx
  · filter_upwards [haRange, hbRange] with x hx hy
    let := treatedLaw_isFiniteMeasure M L k x
    exact quantile_boundary_integral_clipped_bound (treatedLaw M L k x)
      (a x) (b x) M.yMin M.yMax hx hy (treatedLaw_mass_le_one M L k x)

-- @node: treatedLaw_quantile_boundary_bias_isLittleOp
/-- Suppose [the true boundary is measurable](hyp:htruth), [every fitted boundary is measurable](hyp:hfit), [the true boundary lies almost surely in the outcome interval](hyp:htruthRange), [every fitted boundary lies there almost surely](hyp:hfitRange), [the local radius is positive](hyp:hr), [the density-bound constant is nonnegative](hyp:hC), and [treated-law masses of intervals within that radius of the true boundary are almost surely bounded by the constant times interval length](hyp:hdensity). If [the boundary's covariate L2 error is smaller in probability than the inverse fourth root of the even sample size](hyp:hrate), [the boundary remainder integrated over treated outcomes and covariates is smaller in probability than the inverse square root of that sample size](goal). -/
lemma treatedLaw_quantile_boundary_bias_isLittleOp
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X) (k : ℕ)
    (truth : X → ℝ) (fit : ℕ → A → X → ℝ) (r C : ℝ)
    (htruth : Measurable truth) (hfit : ∀ n a, Measurable (fit n a))
    (htruthRange : ∀ᵐ x ∂xLaw M, truth x ∈ Icc M.yMin M.yMax)
    (hfitRange : ∀ n a, ∀ᵐ x ∂xLaw M, fit n a x ∈ Icc M.yMin M.yMax)
    (hr : 0 < r) (hC : 0 ≤ C)
    (hdensity : ∀ᵐ x ∂xLaw M, ∀ u v, truth x - r ≤ u → u ≤ v → v ≤ truth x + r →
      (treatedLaw M L k x (Ioc u v)).toReal ≤ C * (v - u))
    (hrate : Causalean.Stat.IsLittleOp
      (fun n a => finiteL2Error M (fit (2 * (n + 1)) a) truth)
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ) :
    Causalean.Stat.IsLittleOp
      (fun n a => ∫ x, ∫ y in
        Ioc (min (truth x) (fit (2 * (n + 1)) a x))
          (max (truth x) (fit (2 * (n + 1)) a x)),
        fit (2 * (n + 1)) a x - y ∂treatedLaw M L k x ∂xLaw M)
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 2 : ℝ)) μ := by
  let D := max 1 (C + (M.yMax - M.yMin) / r ^ 2)
  have hD : 0 < D := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hs := dml_quarter_rate_product μ
    (fun n a => finiteL2Error M (fit (2 * (n + 1)) a) truth)
    (fun n a => finiteL2Error M (fit (2 * (n + 1)) a) truth) hrate hrate
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul hD hs
  intro n a
  have h := (treatedLaw_quantile_boundary_integrated_quadratic M L k truth
    (fit (2 * (n + 1)) a) r C htruth (hfit _ a) htruthRange
    (hfitRange _ a) hr hC hdensity).2
  calc
    _ ≤ (C + (M.yMax - M.yMin) / r ^ 2) *
        finiteL2Error M (fit (2 * (n + 1)) a) truth ^ 2 := h
    _ ≤ D * finiteL2Error M (fit (2 * (n + 1)) a) truth ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
    _ = _ := by rw [← sq, abs_of_nonneg (sq_nonneg _)]

-- @node: nuisanceRates_quantile_boundary_bias_root_n_negligible
/-- For a chosen nuisance coordinate, suppose [the true boundary is measurable](hyp:htruth), [every fitted boundary is measurable](hyp:hfit), [the true boundary lies almost surely in the outcome interval](hyp:htruthRange), [all fitted boundaries lie there almost surely](hyp:hfitRange), [the neighborhood radius is positive](hyp:hr), [the density-bound constant is nonnegative](hyp:hC), and [conditional treated-law interval masses near the true boundary are almost surely bounded by that constant times interval length](hyp:hdensity). Under [the finite nuisance rate conditions](hyp:hrates), [the boundary remainder integrated over treated outcomes and covariates, using fits from sample size twice the positive index and multiplied by the square root of that index, converges to zero in probability](goal). -/
lemma nuisanceRates_quantile_boundary_bias_root_n_negligible {B : Type*}
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X) (k : ℕ)
    (truth : B → X → ℝ) (fit : ℕ → A → B → X → ℝ) (c : B) (r C : ℝ)
    (htruth : Measurable (truth c)) (hfit : ∀ n a, Measurable (fit n a c))
    (htruthRange : ∀ᵐ x ∂xLaw M, truth c x ∈ Icc M.yMin M.yMax)
    (hfitRange : ∀ n a, ∀ᵐ x ∂xLaw M, fit n a c x ∈ Icc M.yMin M.yMax)
    (hr : 0 < r) (hC : 0 ≤ C)
    (hdensity : ∀ᵐ x ∂xLaw M, ∀ u v, truth c x - r ≤ u → u ≤ v →
      v ≤ truth c x + r → (treatedLaw M L k x (Ioc u v)).toReal ≤ C * (v - u))
    (hrates : FiniteNuisanceRates M μ fit truth) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (∫ x, ∫ y in Ioc (min (truth c x) (fit (2 * (n + 1)) a c x))
          (max (truth c x) (fit (2 * (n + 1)) a c x)),
          fit (2 * (n + 1)) a c x - y ∂treatedLaw M L k x ∂xLaw M))
      atTop (fun _ _ => 0) := by
  apply dml_root_n_bias_tendsto_probability
  exact treatedLaw_quantile_boundary_bias_isLittleOp M μ L k (truth c)
    (fun n a => fit n a c) r C htruth hfit htruthRange hfitRange hr hC hdensity (hrates c)

-- Use the regime's density condition at the true nuisance coordinate;
-- equality with bandBoundary is definitional for trueNuisance.
-- @node: dml_quantile_boundary_density_constants
/-- If [boundary densities satisfy the model's boundedness condition](hyp:hd), [there exist a common positive radius and nonnegative constant such that, at every true nuisance boundary and each adjacent treated level, almost surely every interval inside that radius has treated-law mass at most the constant times its length](goal). -/
lemma dml_quantile_boundary_density_constants (M : LatentIVModel Ω X Z)
    (L : LevelData Z X) (hd : BoundaryDensitiesBounded M L) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ a : BoundaryIndex L,
      ∀ k', k' = a.val.1 + 1 ∨ (1 ≤ a.val.1 ∧ k' = a.val.1) →
      ∀ᵐ x ∂xLaw M, ∀ u v, (trueNuisance M L).nu a x - r ≤ u → u ≤ v →
        v ≤ (trueNuisance M L).nu a x + r →
        (treatedLaw M L k' x (Ioc u v)).toReal ≤ C * (v - u) := by
  obtain ⟨r, C, hr, hd⟩ := hd
  refine ⟨r, max C 0, hr, le_max_right _ _, ?_⟩
  intro a k' hk'
  have ha := a.property
  filter_upwards [hd a.val.1 ha.1 a.val.2 ha.2.1 ha.2.2 k' hk'] with x hx
  intro u v hu huv hv
  exact (hx u v hu huv hv).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (sub_nonneg.mpr huv))

-- @node: nuisanceRates_continuous_quantile_boundary_bias_root_n_negligible
/-- Suppose [the true continuous nuisance is admissible](hyp:he0), [every fitted continuous nuisance is admissible](hyp:heh), [boundary densities are bounded](hyp:hd), and [the quantile boundary coordinates satisfy the finite nuisance rate conditions](hyp:hrates). If [the treated level is the level just above the selected boundary or its positive current level](hyp:hk'), [the boundary remainder integrated over treated outcomes and covariates, formed from fits at twice the positive sample index and multiplied by the square root of that index, converges to zero in probability](goal). -/
lemma nuisanceRates_continuous_quantile_boundary_bias_root_n_negligible
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hd : BoundaryDensitiesBounded M L)
    (hrates : FiniteNuisanceRates M μ (fun n a => (eh n a).nu) (trueNuisance M L).nu)
    (c : BoundaryIndex L) (k' : ℕ)
    (hk' : k' = c.val.1 + 1 ∨ (1 ≤ c.val.1 ∧ k' = c.val.1)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (∫ x, ∫ y in
          Ioc (min ((trueNuisance M L).nu c x) ((eh (2 * (n + 1)) a).nu c x))
            (max ((trueNuisance M L).nu c x) ((eh (2 * (n + 1)) a).nu c x)),
          (eh (2 * (n + 1)) a).nu c x - y ∂treatedLaw M L k' x ∂xLaw M))
      atTop (fun _ _ => 0) := by
  obtain ⟨r, C, hr, hC, hdensity⟩ := dml_quantile_boundary_density_constants M L hd
  rcases he0 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hn0, hm0, _⟩
  have hnh (n : ℕ) (a : A) :
      ∀ c, ∀ᵐ x ∂xLaw M, (eh n a).nu c x ∈ Icc M.yMin M.yMax := by
    rcases heh n a with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hn, _⟩
    exact hn
  have hmh (n : ℕ) (a : A) (c : BoundaryIndex L) : Measurable ((eh n a).nu c) := by
    first | fun_prop | skip
    rcases heh n a with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _⟩
    exact hm c
  exact nuisanceRates_quantile_boundary_bias_root_n_negligible M μ L k'
    (trueNuisance M L).nu (fun n a => (eh n a).nu) c r C (hm0 c)
    (fun n a => hmh n a c) (hn0 c) (fun n a => hnh n a c)
    hr hC (hdensity c k' hk') hrates

end Papers.TbsPrteOptimalTransport
