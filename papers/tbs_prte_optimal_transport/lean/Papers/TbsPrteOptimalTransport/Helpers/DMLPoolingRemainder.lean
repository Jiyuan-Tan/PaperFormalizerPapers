module
public import Papers.TbsPrteOptimalTransport.Helpers.PooledPolicyDirections
public import Papers.TbsPrteOptimalTransport.Helpers.ProductScoreMoments
public import Papers.TbsPrteOptimalTransport.Helpers.DMLIndicatorRates
/-! Simplex cancellation and quantitative share-policy pooling remainders for DML. -/
public section
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Filter
open scoped Topology ENNReal

-- At a population policy level the values all equal q. The simplex constraint
-- removes the standalone share error, leaving the product in the roadmap.
-- @node: simplex_pooling_error_identity
/-- If [the reference shares sum to one over a finite set](hyp:ha) and
[the fitted shares also sum to one](hyp:hah), then [the fitted pooled value
minus the common reference policy value and the reference-share-weighted policy
change equals the sum of share changes times policy changes](goal). -/
lemma simplex_pooling_error_identity {ι : Type*} (s : Finset ι)
    (a ah qh : ι → ℝ) (q : ℝ)
    (ha : ∑ z ∈ s, a z = 1) (hah : ∑ z ∈ s, ah z = 1) :
    (∑ z ∈ s, ah z * qh z) - q - (∑ z ∈ s, a z * (qh z - q)) =
      ∑ z ∈ s, (ah z - a z) * (qh z - q) := by
  have hzero : ∑ z ∈ s, (ah z - a z) * q = 0 := by
    rw [← Finset.sum_mul, Finset.sum_sub_distrib, hah, ha]
    ring
  calc
    _ = (∑ z ∈ s, (ah z - a z) * qh z) := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ha, one_mul]
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib]
      ring
    _ = _ := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, hzero, sub_zero]

-- L2 membership gives integrability of every cross product for free.
-- @node: finite_pooling_product_L2_bound
/-- If [every first-factor function in a finite set has a finite second
moment](hyp:hf) and [every corresponding second-factor function does too](hyp:hg),
then [their summed products are integrable, and the absolute integral is at
most the sum of the products of the corresponding L2 norms](goal). -/
lemma finite_pooling_product_L2_bound {ι X : Type*} [MeasurableSpace X]
    (ν : Measure X) (s : Finset ι) (f g : ι → X → ℝ)
    (hf : ∀ z ∈ s, MemLp (f z) 2 ν) (hg : ∀ z ∈ s, MemLp (g z) 2 ν) :
    Integrable (fun x => ∑ z ∈ s, f z x * g z x) ν ∧
      |∫ x, ∑ z ∈ s, f z x * g z x ∂ν| ≤
        ∑ z ∈ s, (eLpNorm (f z) 2 ν).toReal * (eLpNorm (g z) 2 ν).toReal := by
  have hi : ∀ z ∈ s, Integrable (fun x => f z x * g z x) ν :=
    fun z hz => (hf z hz).integrable_mul (hg z hz)
  refine ⟨integrable_finsetSum s hi, ?_⟩
  rw [integral_finsetSum s hi]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro z hz
  calc
    _ ≤ ∫ x, |f z x * g z x| ∂ν := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun x => f z x * g z x)
    _ ≤ _ := Causalean.Stat.integral_abs_mul_le_eLpNorm_mul_eLpNorm (hf z hz) (hg z hz)

-- @node: dml_finite_quarter_rate_product_sum
/-- If [each first-factor sequence in a finite set is negligible relative to
the inverse fourth root of twice n plus two](hyp:hf) and [each second-factor
sequence has the same rate](hyp:hg), then [the sum of their pairwise products
is negligible in probability relative to the inverse square root of twice
n plus two](goal). -/
lemma dml_finite_quarter_rate_product_sum {A ι : Type*} [MeasurableSpace A]
    (μ : Measure A) (s : Finset ι) (f g : ι → ℕ → A → ℝ)
    (hf : ∀ z ∈ s, Causalean.Stat.IsLittleOp (f z)
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ)
    (hg : ∀ z ∈ s, Causalean.Stat.IsLittleOp (g z)
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ) :
    Causalean.Stat.IsLittleOp (fun n a => ∑ z ∈ s, f z n a * g z n a)
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 2 : ℝ)) μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro eps heps
    have hempty (n : ℕ) : {a : A | eps *
        ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 2 : ℝ) ≤ ‖∑ z ∈ (∅ : Finset ι), f z n a * g z n a‖} = ∅ := by
      ext a
      simp only [Finset.sum_empty, norm_zero, Set.mem_ofPred_eq,
        Set.mem_empty_iff_false, iff_false]
      exact not_le_of_gt (mul_pos heps (Real.rpow_pos_of_pos (by positivity) _))
    simpa only [hempty, measure_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
  | @insert z s hz ih =>
    have htail := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi => hg i (Finset.mem_insert_of_mem hi))
    have hhead := dml_quarter_rate_product μ (f z) (g z)
      (hf z (Finset.mem_insert_self _ _)) (hg z (Finset.mem_insert_self _ _))
    simpa only [Finset.sum_insert hz] using hhead.add_eventually_nonneg_rate
      (Eventually.of_forall (fun n => Real.rpow_nonneg (by positivity) _)) htail

-- This is a derived stochastic rate for the pooling term, not an assumed
-- score-bias bound. The full-score expansion must still identify this term.
-- @node: dml_pooling_product_isLittleOp
/-- Suppose [all first-factor functions](hyp:hf) and [all second-factor
functions](hyp:hg) in a finite collection have finite second moments for every
sample size and realization, while [their first-factor L2 norms](hyp:hrf) and
[their second-factor L2 norms](hyp:hrg) are negligible relative to the inverse
fourth root of twice n plus two. Then [the integral of the sum of pairwise
products is negligible in probability relative to the inverse square root
of twice n plus two](goal). -/
lemma dml_pooling_product_isLittleOp {A X ι : Type*}
    [MeasurableSpace A] [MeasurableSpace X] (μ : Measure A) (ν : Measure X)
    (s : Finset ι) (f g : ι → ℕ → A → X → ℝ)
    (hf : ∀ z ∈ s, ∀ n a, MemLp (f z n a) 2 ν)
    (hg : ∀ z ∈ s, ∀ n a, MemLp (g z n a) 2 ν)
    (hrf : ∀ z ∈ s, Causalean.Stat.IsLittleOp
      (fun n a => (eLpNorm (f z n a) 2 ν).toReal)
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ)
    (hrg : ∀ z ∈ s, Causalean.Stat.IsLittleOp
      (fun n a => (eLpNorm (g z n a) 2 ν).toReal)
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ) :
    Causalean.Stat.IsLittleOp
      (fun n a => ∫ x, ∑ z ∈ s, f z n a x * g z n a x ∂ν)
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 2 : ℝ)) μ := by
  have hr := dml_finite_quarter_rate_product_sum μ s
    (fun z n a => (eLpNorm (f z n a) 2 ν).toReal)
    (fun z n a => (eLpNorm (g z n a) 2 ν).toReal) hrf hrg
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul one_pos hr
  intro n a
  simpa only [one_mul, abs_of_nonneg (Finset.sum_nonneg fun z hz =>
    mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)] using
    (finite_pooling_product_L2_bound ν s (fun z => f z n a) (fun z => g z n a)
      (fun z hz => hf z hz n a) (fun z hz => hg z hz n a)).2

-- This bound applies to the actual pooling residual after the population
-- first-order policy term has been subtracted.
-- @node: simplex_pooling_residual_L2_bound
/-- If [reference shares sum to one almost everywhere](hyp:ha), [fitted shares
sum to one almost everywhere](hyp:hah), and [share errors](hyp:heA) and
[deviations of fitted policy values from a common reference value](hyp:heQ)
have finite second moments for each member of a finite set, then [the pooled
value minus the common reference value and the reference-share-weighted policy
change is integrable, with absolute integral bounded by the sum of the products
of the corresponding share-error and policy-error L2 norms](goal). -/
lemma simplex_pooling_residual_L2_bound {ι X : Type*} [MeasurableSpace X]
    (ν : Measure X) (s : Finset ι) (a ah qh : ι → X → ℝ) (q : X → ℝ)
    (ha : ∀ᵐ x ∂ν, ∑ z ∈ s, a z x = 1)
    (hah : ∀ᵐ x ∂ν, ∑ z ∈ s, ah z x = 1)
    (heA : ∀ z ∈ s, MemLp (fun x => ah z x - a z x) 2 ν)
    (heQ : ∀ z ∈ s, MemLp (fun x => qh z x - q x) 2 ν) :
    Integrable (fun x => (∑ z ∈ s, ah z x * qh z x) - q x -
      ∑ z ∈ s, a z x * (qh z x - q x)) ν ∧
    |∫ x, (∑ z ∈ s, ah z x * qh z x) - q x -
      ∑ z ∈ s, a z x * (qh z x - q x) ∂ν| ≤
        ∑ z ∈ s, (eLpNorm (fun x => ah z x - a z x) 2 ν).toReal *
          (eLpNorm (fun x => qh z x - q x) 2 ν).toReal := by
  have hid : (fun x => (∑ z ∈ s, ah z x * qh z x) - q x -
      ∑ z ∈ s, a z x * (qh z x - q x)) =ᵐ[ν]
      (fun x => ∑ z ∈ s, (ah z x - a z x) * (qh z x - q x)) := by
    filter_upwards [ha, hah] with x hx hxh
    exact simplex_pooling_error_identity s _ _ _ _ hx hxh
  obtain ⟨hi, hb⟩ := finite_pooling_product_L2_bound ν s
    (fun z x => ah z x - a z x) (fun z x => qh z x - q x) heA heQ
  exact ⟨hi.congr hid.symm, (integral_congr_ae hid).symm ▸ hb⟩

universe u v w
variable {Ω : Type u} {X Z : Type v} {A : Type w} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- The L2 errors are exactly those in the paper's nuisance-rate predicate.
-- @node: nuisanceRates_pooling_root_n_negligible
/-- If [every fitted share error](hyp:ha) and [every fitted policy error](hyp:hq)
in a finite pooling set has a finite second moment, and [shares](hyp:hra) and
[policy values](hyp:hrq) satisfy the componentwise nuisance quarter-rate
conditions, then [the integral of the sum of share errors times policy errors,
evaluated at sample sizes twice n plus two and multiplied by the square root
of n plus one, converges to zero in probability](goal). -/
lemma nuisanceRates_pooling_root_n_negligible {ι : Type*}
    (M : LatentIVModel Ω X Z) (μ : Measure A) (s : Finset ι)
    (aHat qHat : ℕ → A → ι → X → ℝ) (a0 q0 : ι → X → ℝ)
    (ha : ∀ z ∈ s, ∀ n a,
      MemLp (fun x => aHat n a z x - a0 z x) 2 (xLaw M))
    (hq : ∀ z ∈ s, ∀ n a,
      MemLp (fun x => qHat n a z x - q0 z x) 2 (xLaw M))
    (hra : FiniteNuisanceRates M μ aHat a0) (hrq : FiniteNuisanceRates M μ qHat q0) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        ∫ x, ∑ z ∈ s, (aHat (2 * (n + 1)) a z x - a0 z x) *
          (qHat (2 * (n + 1)) a z x - q0 z x) ∂xLaw M)
      atTop (fun _ _ => 0) := by
  apply dml_root_n_bias_tendsto_probability
  apply dml_pooling_product_isLittleOp μ (xLaw M) s
    (fun z n a x => aHat (2 * (n + 1)) a z x - a0 z x)
    (fun z n a x => qHat (2 * (n + 1)) a z x - q0 z x)
    (fun z hz n a => ha z hz _ a) (fun z hz n a => hq z hz _ a)
  · intro z hz
    simpa only [l2Error_eq_eLpNorm M _ _ (ha z hz _ _)] using hra z
  · intro z hz
    simpa only [l2Error_eq_eLpNorm M _ _ (hq z hz _ _)] using hrq z

variable [Fintype Z] [DecidableEq Z]

-- Connect the cancellation to the continuous-outcome nuisance construction.
-- @node: pooledQ_simplex_error_identity
/-- If [reference continuous-outcome pooling shares lie in the simplex](hyp:hs)
and [fitted shares do too](hyp:hsh), then [at any regular level and covariate
value, the fitted pooled policy minus the level's policy value and the
reference-share-weighted policy deviation equals the sum of share errors
times deviations of fitted instrument policies from that level's policy value](goal). -/
lemma pooledQ_simplex_error_identity (phi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e eh : NuisanceCont L) (r : RegularIndex L) (x : X)
    (hs : ContFittedSharesSimplex L e) (hsh : ContFittedSharesSimplex L eh) :
    pooledQ phi L eh r.val.1 r.val.2 x - L.qLev r.val.1 r.val.2 x -
      (∑ z ∈ L.T r.val.1 r.val.2, e.share r z x *
        (phi z x (eh.prop z x) - L.qLev r.val.1 r.val.2 x)) =
      ∑ z ∈ L.T r.val.1 r.val.2, (eh.share r z x - e.share r z x) *
        (phi z x (eh.prop z x) - L.qLev r.val.1 r.val.2 x) := by
  have hj0 : r.val.2 ≠ 0 := by have := r.property.2.1; omega
  have hj : ¬ L.l r.val.1 < r.val.2 := not_lt.mpr r.property.2.2
  simp only [pooledQ, if_neg hj0, if_neg hj, shareValue, dif_pos r.property]
  exact simplex_pooling_error_identity _ _ _ _ _ (hs r x).2 (hsh r x).2

-- The binary algorithm uses the same simplex shares and pooled policy map.
-- @node: pooledQBin_simplex_error_identity
/-- If [reference binary-outcome pooling shares lie in the simplex](hyp:hs)
and [fitted shares do too](hyp:hsh), then [at any regular level and covariate
value, the fitted pooled binary policy minus the level's policy value and
the reference-share-weighted policy deviation equals the sum of share errors
times deviations of fitted instrument policies from that level's policy value](goal). -/
lemma pooledQBin_simplex_error_identity (phi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e eh : NuisanceBin L) (r : RegularIndex L) (x : X)
    (hs : BinFittedSharesSimplex L e) (hsh : BinFittedSharesSimplex L eh) :
    pooledQBin phi L eh r.val.1 r.val.2 x - L.qLev r.val.1 r.val.2 x -
      (∑ z ∈ L.T r.val.1 r.val.2, e.share r z x *
        (phi z x (eh.prop z x) - L.qLev r.val.1 r.val.2 x)) =
      ∑ z ∈ L.T r.val.1 r.val.2, (eh.share r z x - e.share r z x) *
        (phi z x (eh.prop z x) - L.qLev r.val.1 r.val.2 x) := by
  have hj0 : r.val.2 ≠ 0 := by have := r.property.2.1; omega
  have hj : ¬ L.l r.val.1 < r.val.2 := not_lt.mpr r.property.2.2
  simp only [pooledQBin, if_neg hj0, if_neg hj, dif_pos r.property]
  exact simplex_pooling_error_identity _ _ _ _ _ (hs r x).2 (hsh r x).2

end Papers.TbsPrteOptimalTransport
