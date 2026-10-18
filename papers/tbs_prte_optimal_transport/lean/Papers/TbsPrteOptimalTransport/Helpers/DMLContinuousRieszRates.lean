module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousFullRates
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousRieszCoordinates
/-! Quarter-power rates for the smooth continuous propensity representers.
Bounded boundary probabilities preserve the quantile product rates; affine
assembly then preserves the rates of both propensity representers. -/
public section
set_option linter.style.haveILetI false
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

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

-- @node: nuisanceRates_neg
/-- If [the fitted coordinates converge to their reference coordinates at the finite nuisance rates](hyp:hr), then [negating both fitted and reference coordinates preserves those rates](goal). -/
lemma nuisanceRates_neg {C : Type*} (f : ℕ → A → C → X → ℝ) (f0 : C → X → ℝ)
    (hr : FiniteNuisanceRates M μ f f0) :
    FiniteNuisanceRates M μ (fun n a c x => -f n a c x) (fun c x => -f0 c x) := by
  intro c
  simpa only [finiteL2Error, neg_sub_neg, sub_sq_comm] using hr c

-- @node: nuisanceRates_sub
/-- Suppose [the first fitted family is square integrable coordinate by coordinate](hyp:hf), [the second fitted family is square integrable](hyp:hg), [the first reference family is square integrable](hyp:hf0), and [the second reference family is square integrable](hyp:hg0). If [the first family satisfies the finite nuisance rates toward its reference](hyp:hrf) and [the second family does too](hyp:hrg), then [their difference satisfies the same rates toward the difference of their references](goal). -/
lemma nuisanceRates_sub {C : Type*} (f g : ℕ → A → C → X → ℝ)
    (f0 g0 : C → X → ℝ)
    (hf : ∀ n a c, MemLp (f n a c) 2 (xLaw M))
    (hg : ∀ n a c, MemLp (g n a c) 2 (xLaw M))
    (hf0 : ∀ c, MemLp (f0 c) 2 (xLaw M))
    (hg0 : ∀ c, MemLp (g0 c) 2 (xLaw M))
    (hrf : FiniteNuisanceRates M μ f f0) (hrg : FiniteNuisanceRates M μ g g0) :
    FiniteNuisanceRates M μ (fun n a c x => f n a c x - g n a c x)
      (fun c x => f0 c x - g0 c x) := by
  intro c
  have hs := (hrf c).add_eventually_nonneg_rate
    (Eventually.of_forall (fun _ => Real.rpow_nonneg (by positivity) _)) (hrg c)
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul one_pos hs
  intro n a
  rw [one_mul, abs_of_nonneg (show 0 ≤ finiteL2Error M _ _ from Real.sqrt_nonneg _),
    abs_of_nonneg (show 0 ≤ finiteL2Error M _ _ + finiteL2Error M _ _ from
      add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  exact dml_l2Error_sub_le M _ _ _ _ (hf0 c) (hf _ a c) (hg0 c) (hg _ a c)

-- @node: nuisanceRates_add
/-- Suppose [the first fitted family is square integrable coordinate by coordinate](hyp:hf), [the second fitted family is square integrable](hyp:hg), [the first reference family is square integrable](hyp:hf0), and [the second reference family is square integrable](hyp:hg0). If [the first family satisfies the finite nuisance rates toward its reference](hyp:hrf) and [the second family satisfies those rates toward its reference](hyp:hrg), then [their sum satisfies the same rates toward the sum of their references](goal). -/
lemma nuisanceRates_add {C : Type*} (f g : ℕ → A → C → X → ℝ)
    (f0 g0 : C → X → ℝ)
    (hf : ∀ n a c, MemLp (f n a c) 2 (xLaw M))
    (hg : ∀ n a c, MemLp (g n a c) 2 (xLaw M))
    (hf0 : ∀ c, MemLp (f0 c) 2 (xLaw M))
    (hg0 : ∀ c, MemLp (g0 c) 2 (xLaw M))
    (hrf : FiniteNuisanceRates M μ f f0) (hrg : FiniteNuisanceRates M μ g g0) :
    FiniteNuisanceRates M μ (fun n a c x => f n a c x + g n a c x)
      (fun c x => f0 c x + g0 c x) := by
  simpa only [sub_neg_eq_add] using nuisanceRates_sub M μ f
    (fun n a c x => -g n a c x) f0 (fun c x => -g0 c x) hf
    (fun n a c => (hg n a c).neg) hf0 (fun c => (hg0 c).neg) hrf
    (nuisanceRates_neg M μ g g0 hrg)

-- @node: nuisanceRates_bounded_product
/-- Suppose [the fitted probability family is square integrable](hyp:hp), [the fitted outcome family is square integrable](hyp:hj), [the reference probability family is square integrable](hyp:hp0), and [the reference outcome family is square integrable](hyp:hj0). If [the outcome bound is nonnegative](hyp:hB), [fitted probabilities have absolute value at most one almost everywhere](hyp:hpb), [reference outcomes have absolute value at most that bound almost everywhere](hyp:hjb), [the probability family satisfies the finite nuisance rates](hyp:hrp), and [the outcome family satisfies those rates](hyp:hrj), then [their product satisfies the same rates toward the product of the references](goal). -/
lemma nuisanceRates_bounded_product {C : Type*} (p j : ℕ → A → C → X → ℝ)
    (p0 j0 : C → X → ℝ)
    (hp : ∀ n a c, MemLp (p n a c) 2 (xLaw M))
    (hj : ∀ n a c, MemLp (j n a c) 2 (xLaw M))
    (hp0 : ∀ c, MemLp (p0 c) 2 (xLaw M))
    (hj0 : ∀ c, MemLp (j0 c) 2 (xLaw M))
    (B : ℝ) (hB : 0 ≤ B)
    (hpb : ∀ n a c, ∀ᵐ x ∂xLaw M, |p n a c x| ≤ 1)
    (hjb : ∀ c, ∀ᵐ x ∂xLaw M, |j0 c x| ≤ B)
    (hrp : FiniteNuisanceRates M μ p p0) (hrj : FiniteNuisanceRates M μ j j0) :
    FiniteNuisanceRates M μ (fun n a c x => p n a c x * j n a c x)
      (fun c x => p0 c x * j0 c x) := by
  intro c
  have hs := (hrp c).add_eventually_nonneg_rate
    (Eventually.of_forall (fun _ => Real.rpow_nonneg (by positivity) _)) (hrj c)
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul (by positivity : 0 < B + 1) hs
  intro n a
  rw [abs_of_nonneg (show 0 ≤ finiteL2Error M _ _ from Real.sqrt_nonneg _),
    abs_of_nonneg (show 0 ≤ finiteL2Error M _ _ + finiteL2Error M _ _ from
      add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  apply (dml_l2Error_bounded_product_le M _ _ _ _ (hp0 c) (hp _ a c)
    (hj0 c) (hj _ a c) B hB (hpb _ a c) (hjb c)).trans
  nlinarith [show 0 ≤ finiteL2Error M (p (2*(n+1)) a c) (p0 c) from Real.sqrt_nonneg _,
    show 0 ≤ finiteL2Error M (j (2*(n+1)) a c) (j0 c) from Real.sqrt_nonneg _]

-- @node: encoded_continuous_quantile_boundary_product_quarter_rate
/-- If [the reference nuisance record is admissible](hyp:he0), [every fitted nuisance record is admissible](hyp:heh), and [the encoded coordinates converge to the reference at the finite nuisance rates](hyp:hr), then [the products of quantiles and upper boundary means converge to their reference products in covariate L₂ at a rate smaller in probability than the inverse fourth root of the half-sample size](goal). -/
lemma encoded_continuous_quantile_boundary_product_quarter_rate
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L e0)) :
    FiniteNuisanceRates M μ
      (fun n a (i : ℕ × ℕ) x => nuValue M (eh n a) i.1 i.2 x *
        boundaryValue (eh n a).Mplus i.1 i.2 x)
      (fun i x => nuValue M e0 i.1 i.2 x * boundaryValue e0.Mplus i.1 i.2 x) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  let N := fun (e : NuisanceCont L) (i : ℕ × ℕ) => nuValue M e i.1 i.2
  let P := fun (e : NuisanceCont L) (i : ℕ × ℕ) => boundaryValue e.Mplus i.1 i.2
  have hn (e : NuisanceCont L) (he : ContAdmissible M L e) i :
      MemLp (N e i) 2 (xLaw M) := by
    apply MemLp.of_bound (by fun_prop) (|M.yMin| + |M.yMax|)
    simpa only [Real.norm_eq_abs] using
      continuous_admissible_nuValue_abs_bound M L e he i.1 i.2
  have hp (e : NuisanceCont L) (he : ContAdmissible M L e) i :
      MemLp (P e i) 2 (xLaw M) := by
    obtain ⟨hm, hb⟩ := continuous_admissible_boundaryValue_coordinates M L e he i.1 i.2
    apply MemLp.of_bound hm.aestronglyMeasurable 1
    simpa only [Real.norm_eq_abs] using hb
  let z0 : Z := Classical.choice inferInstance
  have hrn : FiniteNuisanceRates M μ (fun n a => N (eh n a)) (N e0) := by
    intro i
    exact hr (8,i.1,i.2,z0)
  have hrp : FiniteNuisanceRates M μ (fun n a => P (eh n a)) (P e0) := by
    intro i
    exact hr (9,i.1,i.2,z0)
  simpa only [P, N, mul_comm] using nuisanceRates_bounded_product M μ
    (fun n a => P (eh n a)) (fun n a => N (eh n a)) (P e0) (N e0)
    (fun n a => hp _ (heh n a)) (fun n a => hn _ (heh n a)) (hp _ he0) (hn _ he0)
    (|M.yMin| + |M.yMax|) (by positivity)
    (fun n a i => (continuous_admissible_boundaryValue_coordinates M L _ (heh n a) i.1 i.2).2)
    (fun i => continuous_admissible_nuValue_abs_bound M L e0 he0 i.1 i.2) hrp hrn

-- @node: encoded_continuous_alphaHigh_quarter_rate
/-- If [the reference nuisance record is admissible](hyp:he0), [all fitted records are admissible](hyp:heh), and [their encoded coordinates satisfy the finite nuisance rates toward the reference](hyp:hr), then [the upper propensity representers converge to their reference values in covariate L₂ at a rate smaller in probability than the inverse fourth root of the half-sample size](goal). -/
lemma encoded_continuous_alphaHigh_quarter_rate
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L e0)) :
    FiniteNuisanceRates M μ (fun n a (i : ℕ × ℕ) => alphaHigh M L (eh n a) i.1 i.2)
      (fun i => alphaHigh M L e0 i.1 i.2) := by
  let J := fun (e : NuisanceCont L) (i : ℕ × ℕ) => meanValue e.Jplus i.1 i.2
  let P := fun (e : NuisanceCont L) (i : ℕ × ℕ) x =>
    nuValue M e i.1 i.2 x * boundaryValue e.Mplus i.1 i.2 x
  have hj (e : NuisanceCont L) (he : ContAdmissible M L e) i :
      MemLp (J e i) 2 (xLaw M) := fitted_continuous_meanValue_memLp M L e he i.1 i.2
  have hp (e : NuisanceCont L) (he : ContAdmissible M L e) i :
      MemLp (P e i) 2 (xLaw M) :=
    fitted_continuous_quantile_boundary_product_memLp M L e he i.1 i.2
  let z0 : Z := Classical.choice inferInstance
  have hrj : FiniteNuisanceRates M μ (fun n a => J (eh n a)) (J e0) := by
    intro i
    exact hr (11,i.1,i.2,z0)
  have hrp := encoded_continuous_quantile_boundary_product_quarter_rate M μ L e0 eh he0 heh hr
  have hs := nuisanceRates_add M μ (fun n a => J (eh n a)) (fun n a => P (eh n a))
    (J e0) (P e0) (fun n a => hj _ (heh n a)) (fun n a => hp _ (heh n a))
    (hj _ he0) (hp _ he0) hrj hrp
  have hrp' : FiniteNuisanceRates M μ
      (fun n a (i : ℕ × ℕ) => P (eh n a) (i.1,i.2+1))
      (fun i => P e0 (i.1,i.2+1)) := fun i => hrp (i.1,i.2+1)
  exact nuisanceRates_sub M μ _ _ _ _
    (fun n a i => (hj _ (heh n a) i).add (hp _ (heh n a) i))
    (fun n a i => hp _ (heh n a) (i.1,i.2+1))
    (fun i => (hj _ he0 i).add (hp _ he0 i))
    (fun i => hp _ he0 (i.1,i.2+1)) hs hrp'

-- @node: encoded_continuous_quantile_minus_boundary_product_quarter_rate
/-- If [the reference nuisance record is admissible](hyp:he0), [the fitted nuisance records are admissible](hyp:heh), and [their encoded coordinates satisfy the finite nuisance rates toward the reference](hyp:hr), then [the products of quantiles and lower boundary means converge to their reference products in covariate L₂ at a rate smaller in probability than the inverse fourth root of the half-sample size](goal). -/
lemma encoded_continuous_quantile_minus_boundary_product_quarter_rate
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L e0)) :
    FiniteNuisanceRates M μ
      (fun n a (i : ℕ × ℕ) x => nuValue M (eh n a) i.1 i.2 x *
        minusBoundaryValue (eh n a).Mminus i.1 i.2 x)
      (fun i x => nuValue M e0 i.1 i.2 x * minusBoundaryValue e0.Mminus i.1 i.2 x) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  let N := fun (e : NuisanceCont L) (i : ℕ × ℕ) => nuValue M e i.1 i.2
  let P := fun (e : NuisanceCont L) (i : ℕ × ℕ) => minusBoundaryValue e.Mminus i.1 i.2
  have hn (e : NuisanceCont L) (he : ContAdmissible M L e) i :
      MemLp (N e i) 2 (xLaw M) := by
    apply MemLp.of_bound (by fun_prop) (|M.yMin| + |M.yMax|)
    simpa only [Real.norm_eq_abs] using
      continuous_admissible_nuValue_abs_bound M L e he i.1 i.2
  have hp (e : NuisanceCont L) (he : ContAdmissible M L e) i :
      MemLp (P e i) 2 (xLaw M) := by
    obtain ⟨hm, hb⟩ := continuous_admissible_minusBoundaryValue_coordinates M L e he i.1 i.2
    apply MemLp.of_bound hm.aestronglyMeasurable 1
    simpa only [Real.norm_eq_abs] using hb
  let z0 : Z := Classical.choice inferInstance
  have hrn : FiniteNuisanceRates M μ (fun n a => N (eh n a)) (N e0) := by
    intro i
    exact hr (8,i.1,i.2,z0)
  have hrp : FiniteNuisanceRates M μ (fun n a => P (eh n a)) (P e0) := by
    intro i
    exact hr (10,i.1,i.2,z0)
  simpa only [P, N, mul_comm] using nuisanceRates_bounded_product M μ
    (fun n a => P (eh n a)) (fun n a => N (eh n a)) (P e0) (N e0)
    (fun n a => hp _ (heh n a)) (fun n a => hn _ (heh n a)) (hp _ he0) (hn _ he0)
    (|M.yMin| + |M.yMax|) (by positivity)
    (fun n a i => (continuous_admissible_minusBoundaryValue_coordinates M L _ (heh n a) i.1 i.2).2)
    (fun i => continuous_admissible_nuValue_abs_bound M L e0 he0 i.1 i.2) hrp hrn


-- The fixed lower-boundary indicator contributes either a quantile coordinate
-- or zero; its rate does not require any moving-indicator density argument.
-- @node: encoded_continuous_alphaLow_quarter_rate
/-- If [the reference nuisance record is admissible](hyp:he0), [the fitted records are admissible](hyp:heh), and [their encoded coordinates satisfy the finite nuisance rates toward the reference](hyp:hr), then [the lower propensity representers converge to their reference values in covariate L₂ at a rate smaller in probability than the inverse fourth root of the half-sample size](goal). -/
lemma encoded_continuous_alphaLow_quarter_rate
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0) (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L e0)) :
    FiniteNuisanceRates M μ (fun n a (i : ℕ × ℕ) => alphaLow M L (eh n a) i.1 i.2)
      (fun i => alphaLow M L e0 i.1 i.2) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  let J := fun (e : NuisanceCont L) (i : ℕ × ℕ) => minusMeanValue e.Jminus i.1 i.2
  let P := fun (e : NuisanceCont L) (i : ℕ × ℕ) x =>
    nuValue M e i.1 i.2 x * minusBoundaryValue e.Mminus i.1 i.2 x
  let N := fun (e : NuisanceCont L) (i : ℕ × ℕ) => nuValue M e i.1 i.2
  let Q := fun (e : NuisanceCont L) (i : ℕ × ℕ) x => indicator (1 ≤ i.2) * N e i x
  have hj (e : NuisanceCont L) (he : ContAdmissible M L e) i :
      MemLp (J e i) 2 (xLaw M) := fitted_continuous_minusMeanValue_memLp M L e he i.1 i.2
  have hp (e : NuisanceCont L) (he : ContAdmissible M L e) i :
      MemLp (P e i) 2 (xLaw M) :=
    fitted_continuous_quantile_minus_boundary_product_memLp M L e he i.1 i.2
  have hn (e : NuisanceCont L) (he : ContAdmissible M L e) i :
      MemLp (N e i) 2 (xLaw M) := by
    apply MemLp.of_bound (by fun_prop) (|M.yMin| + |M.yMax|)
    simpa only [Real.norm_eq_abs] using
      continuous_admissible_nuValue_abs_bound M L e he i.1 i.2
  have hq (e : NuisanceCont L) (he : ContAdmissible M L e) i :
      MemLp (Q e i) 2 (xLaw M) := (hn e he i).const_mul _
  let z0 : Z := Classical.choice inferInstance
  have hrj : FiniteNuisanceRates M μ (fun n a => J (eh n a)) (J e0) :=
    fun i => hr (12,i.1,i.2,z0)
  have hrn : FiniteNuisanceRates M μ (fun n a => N (eh n a)) (N e0) :=
    fun i => hr (8,i.1,i.2,z0)
  have hrq : FiniteNuisanceRates M μ (fun n a => Q (eh n a)) (Q e0) := by
    intro i
    by_cases hi : 1 ≤ i.2
    · simpa only [Q, indicator, if_pos hi, one_mul] using hrn i
    · simp only [Q, indicator, if_neg hi, zero_mul, finiteL2Error, sub_self,
        zero_pow (by norm_num : 2 ≠ 0), integral_zero, Real.sqrt_zero]
      apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul one_pos (hrn i)
      intro n a
      simp only [abs_zero, one_mul]
      exact abs_nonneg _
  have hrp := encoded_continuous_quantile_minus_boundary_product_quarter_rate
    M μ L e0 eh he0 heh hr
  have hrp' : FiniteNuisanceRates M μ
      (fun n a (i : ℕ × ℕ) => P (eh n a) (i.1,i.2+1))
      (fun i => P e0 (i.1,i.2+1)) := fun i => hrp (i.1,i.2+1)
  have hrn' : FiniteNuisanceRates M μ
      (fun n a (i : ℕ × ℕ) => N (eh n a) (i.1,i.2+1))
      (fun i => N e0 (i.1,i.2+1)) := fun i => hrn (i.1,i.2+1)
  have h1 := nuisanceRates_sub M μ (fun n a i x => -J (eh n a) i x)
    (fun n a => P (eh n a)) (fun i x => -J e0 i x) (P e0)
    (fun n a i => (hj _ (heh n a) i).neg) (fun n a => hp _ (heh n a))
    (fun i => (hj _ he0 i).neg) (hp _ he0)
    (nuisanceRates_neg M μ _ _ hrj) hrp
  have h2 := nuisanceRates_add M μ _ _ _ _
    (fun n a i => ((hj _ (heh n a) i).neg).sub (hp _ (heh n a) i))
    (fun n a i => hp _ (heh n a) (i.1,i.2+1))
    (fun i => ((hj _ he0 i).neg).sub (hp _ he0 i))
    (fun i => hp _ he0 (i.1,i.2+1)) h1 hrp'
  have h3 := nuisanceRates_add M μ _ _ _ _
    (fun n a i => (((hj _ (heh n a) i).neg).sub (hp _ (heh n a) i)).add
      (hp _ (heh n a) (i.1,i.2+1))) (fun n a => hq _ (heh n a))
    (fun i => (((hj _ he0 i).neg).sub (hp _ he0 i)).add (hp _ he0 (i.1,i.2+1)))
    (hq _ he0) h2 hrq
  exact nuisanceRates_sub M μ _ _ _ _
    (fun n a i => ((((hj _ (heh n a) i).neg).sub (hp _ (heh n a) i)).add
      (hp _ (heh n a) (i.1,i.2+1))).add (hq _ (heh n a) i))
    (fun n a i => hn _ (heh n a) (i.1,i.2+1))
    (fun i => ((((hj _ he0 i).neg).sub (hp _ he0 i)).add
      (hp _ he0 (i.1,i.2+1))).add (hq _ he0 i))
    (fun i => hn _ he0 (i.1,i.2+1)) h3 hrn'

-- No rate is required of the multiplier: it multiplies a regression error,
-- and its clipped absolute bound alone preserves that error's quarter rate.
-- @node: nuisanceRates_bounded_error_multiplier
/-- Suppose [the fitted coordinates are square integrable](hyp:hf), [their reference coordinates are square integrable](hyp:hf0), [the multipliers are measurable](hyp:hw), and [the multipliers have absolute value at most one almost everywhere](hyp:hb). If [the fitted coordinates satisfy the finite nuisance rates toward their references](hyp:hr), then [multiplying their estimation errors by these multipliers preserves the finite nuisance rates toward zero](goal). -/
lemma nuisanceRates_bounded_error_multiplier {C : Type*}
    (f : ℕ → A → C → X → ℝ) (f0 : C → X → ℝ)
    (w : ℕ → A → C → X → ℝ)
    (hf : ∀ n a c, MemLp (f n a c) 2 (xLaw M))
    (hf0 : ∀ c, MemLp (f0 c) 2 (xLaw M))
    (hw : ∀ n a c, Measurable (w n a c))
    (hb : ∀ n a c, ∀ᵐ x ∂xLaw M, |w n a c x| ≤ 1)
    (hr : FiniteNuisanceRates M μ f f0) :
    FiniteNuisanceRates M μ (fun n a c x => w n a c x * (f n a c x - f0 c x))
      (fun _ _ => 0) := by
  intro c
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul one_pos (hr c)
  intro n a
  let d := fun x => f (2*(n+1)) a c x - f0 c x
  have hd : MemLp d 2 (xLaw M) := (hf _ a c).sub (hf0 c)
  have hbound : ∀ᵐ x ∂xLaw M, ‖w (2*(n+1)) a c x * d x‖ ≤ ‖d x‖ := by
    filter_upwards [hb (2*(n+1)) a c] with x hx
    rw [norm_mul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hx (norm_nonneg _)).trans_eq (one_mul _)
  have hmem : MemLp (fun x => w (2*(n+1)) a c x * d x) 2 (xLaw M) :=
    hd.norm.mono' (by first | fun_prop | exact (hw _ a c).aestronglyMeasurable.mul hd.1) hbound
  have hn := eLpNorm_mono_ae (p := (2 : ENNReal)) hbound
  rw [one_mul, abs_of_nonneg (show 0 ≤ finiteL2Error M _ _ from Real.sqrt_nonneg _),
    abs_of_nonneg (show 0 ≤ finiteL2Error M _ _ from Real.sqrt_nonneg _)]
  rw [l2Error_eq_eLpNorm M _ _ (by simpa only [sub_zero] using hmem),
    l2Error_eq_eLpNorm M _ _ hd]
  simpa only [sub_zero] using ENNReal.toReal_mono hd.eLpNorm_ne_top hn

-- Jointly changing fitted regressions can be compared through their common
-- population coordinates, then multiplied by any clipped propensity weight.
-- @node: encoded_continuous_weighted_alpha_difference_quarter_rate
/-- Suppose [the common reference record is admissible](hyp:he0), [the first fitted nuisance sequence is admissible](hyp:heh), [the second fitted sequence is admissible](hyp:hbh), [the first sequence satisfies the finite encoded nuisance rates toward that reference](hyp:hre), and [the second sequence satisfies those rates toward the same reference](hyp:hrb). For [measurable weights](hyp:hw) [bounded in absolute value by one almost everywhere](hyp:hb), [the weighted difference of the two upper or lower propensity representers satisfies the finite nuisance rates toward zero](goal). -/
lemma encoded_continuous_weighted_alpha_difference_quarter_rate
    (L : LevelData Z X) (e0 : NuisanceCont L)
    (eh bh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L e0)
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hbh : ∀ n a, ContAdmissible M L (bh n a))
    (hre : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L e0))
    (hrb : FiniteNuisanceRates M μ (fun n a => contComponent M L (bh n a))
      (contComponent M L e0))
    (w : ℕ → A → Bool × (ℕ × ℕ) → X → ℝ)
    (hw : ∀ n a i, Measurable (w n a i))
    (hb : ∀ n a i, ∀ᵐ x ∂xLaw M, |w n a i x| ≤ 1) :
    FiniteNuisanceRates M μ
      (fun n a i x => w n a i x *
        ((if i.1 then alphaHigh M L (eh n a) i.2.1 i.2.2 x
          else alphaLow M L (eh n a) i.2.1 i.2.2 x) -
         (if i.1 then alphaHigh M L (bh n a) i.2.1 i.2.2 x
          else alphaLow M L (bh n a) i.2.1 i.2.2 x))) (fun _ _ => 0) := by
  let F := fun (e : NuisanceCont L) (i : Bool × (ℕ × ℕ)) x =>
    if i.1 then alphaHigh M L e i.2.1 i.2.2 x else alphaLow M L e i.2.1 i.2.2 x
  have hm (e : NuisanceCont L) (he : ContAdmissible M L e) i :
      MemLp (F e i) 2 (xLaw M) := by
    cases hi : i.1
    · simpa only [F, hi, Bool.false_eq_true, if_false] using
        fitted_continuous_alphaLow_memLp M L e he i.2.1 i.2.2
    · simpa only [F, hi, if_true] using
        fitted_continuous_alphaHigh_memLp M L e he i.2.1 i.2.2
  have rates (e : ℕ → A → NuisanceCont L)
      (he : ∀ n a, ContAdmissible M L (e n a))
      (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (e n a))
        (contComponent M L e0)) : FiniteNuisanceRates M μ (fun n a => F (e n a)) (F e0) := by
    intro i
    cases hi : i.1
    · simpa only [F, hi, Bool.false_eq_true, if_false] using
        encoded_continuous_alphaLow_quarter_rate M μ L e0 e he0 he hr i.2
    · simpa only [F, hi, if_true] using
        encoded_continuous_alphaHigh_quarter_rate M μ L e0 e he0 he hr i.2
  have hd := nuisanceRates_sub M μ (fun n a => F (eh n a)) (fun n a => F (bh n a))
    (F e0) (F e0) (fun n a => hm _ (heh n a)) (fun n a => hm _ (hbh n a))
    (hm _ he0) (hm _ he0) (rates eh heh hre) (rates bh hbh hrb)
  simpa only [F, sub_self, sub_zero] using nuisanceRates_bounded_error_multiplier M μ
    (fun n a i x => F (eh n a) i x - F (bh n a) i x)
    (fun _ _ => 0) w (fun n a i => (hm _ (heh n a) i).sub (hm _ (hbh n a) i))
    (fun _ => MemLp.zero') hw hb (by simpa only [sub_self] using hd)

end Papers.TbsPrteOptimalTransport
