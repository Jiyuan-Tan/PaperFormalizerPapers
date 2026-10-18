module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLQuantileBandConvergence
/-! Conditional treated-band means inherit the moving-band energy bound.
The treated law may have mass zero off support; its mass bound suffices for
the squared-mean contraction, without a probability-measure instance. -/
public section
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedFintypeInType false
set_option linter.unusedTactic false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

-- @node: integral_sq_mean_le_of_mass_le_one
/-- For a finite measure, if [a real function is square-integrable](hyp:hf) and [the measure has total mass at most one](hyp:hmass), [the square of its integral is at most the integral of its square](goal). -/
lemma integral_sq_mean_le_of_mass_le_one {B : Type*} [MeasurableSpace B]
    (ν : Measure B) [IsFiniteMeasure ν] (f : B → ℝ)
    (hf : MemLp f 2 ν) (hmass : ν.real univ ≤ 1) :
    (∫ y, f y ∂ν) ^ 2 ≤ ∫ y, f y ^ 2 ∂ν := by
  let m := ∫ y, f y ∂ν
  have hfi : Integrable f ν := hf.integrable (by norm_num)
  have heq : (∫ y, (f y - m) ^ 2 ∂ν) =
      (∫ y, f y ^ 2 ∂ν) - 2 * m ^ 2 + ν.real univ * m ^ 2 := by
    simp_rw [show ∀ y, (f y - m) ^ 2 = f y ^ 2 - (2 * m) * f y + m ^ 2
      from fun y => by ring]
    have hs : Integrable (fun y => f y ^ 2 - (2 * m) * f y) ν :=
      hf.integrable_sq.sub (hfi.const_mul (2 * m))
    rw [integral_add hs (integrable_const (m ^ 2)),
      integral_sub hf.integrable_sq (hfi.const_mul (2 * m)),
      integral_const_mul, integral_const]
    dsimp only [m]
    simp only [smul_eq_mul]
    ring
  have hnonneg : 0 ≤ ∫ y, (f y - m) ^ 2 ∂ν :=
    integral_nonneg (fun y => sq_nonneg (f y - m))
  rw [heq] at hnonneg
  have hmass' := mul_le_mul_of_nonneg_right hmass (sq_nonneg m)
  dsimp only [m] at *
  nlinarith

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: treatedLaw_integrated_sq_mean_le
/-- If [a function of covariates and outcomes is measurable](hyp:hf), [its outcome section is square-integrable under each conditional treated law](hyp:hmem), and [its conditional second moment is integrable over covariates](hyp:hi), [its squared conditional treated-law mean is integrable over covariates and its integral is bounded by the integrated conditional second moment](goal). -/
lemma treatedLaw_integrated_sq_mean_le
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (k : ℕ)
    (f : X × ℝ → ℝ) (hf : Measurable f)
    (hmem : ∀ x, MemLp (fun y => f (x, y)) 2 (treatedLaw M L k x))
    (hi : Integrable (fun x => ∫ y, f (x, y) ^ 2 ∂treatedLaw M L k x) (xLaw M)) :
    Integrable (fun x => (∫ y, f (x, y) ∂treatedLaw M L k x) ^ 2) (xLaw M) ∧
    (∫ x, (∫ y, f (x, y) ∂treatedLaw M L k x) ^ 2 ∂xLaw M) ≤
      ∫ x, ∫ y, f (x, y) ^ 2 ∂treatedLaw M L k x ∂xLaw M := by
  have hb (x : X) : (∫ y, f (x, y) ∂treatedLaw M L k x) ^ 2 ≤
      ∫ y, f (x, y) ^ 2 ∂treatedLaw M L k x := by
    let := treatedLaw_isFiniteMeasure M L k x
    exact integral_sq_mean_le_of_mass_le_one _ _ (hmem x)
      (treatedLaw_mass_le_one M L k x)
  have hm : Measurable (fun x => (∫ y, f (x, y) ∂treatedLaw M L k x) ^ 2) := by
    fun_prop
  have hi' : Integrable (fun x => (∫ y, f (x, y) ∂treatedLaw M L k x) ^ 2)
      (xLaw M) := hi.mono' hm.aestronglyMeasurable (Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs, abs_sq] using hb x)
  exact ⟨hi', integral_mono hi' hi hb⟩

-- @node: treatedLaw_weighted_quantile_band_mean_sq_bound
/-- If [the original lower endpoint](hyp:ha), [original upper endpoint](hyp:hb), [replacement lower endpoint](hyp:ha'), [replacement upper endpoint](hyp:hb'), and [weight](hyp:hw) are measurable, and [the weight is almost surely bounded in absolute value by a fixed constant under the covariate law](hyp:hwb), [the squared conditional treated-law mean of the weighted band-indicator change is integrable over covariates, and its integral is at most the integrated conditional second moment of that change](goal). -/
lemma treatedLaw_weighted_quantile_band_mean_sq_bound
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (k : ℕ)
    (a b a' b' w : X → ℝ) (D : ℝ)
    (ha : Measurable a) (hb : Measurable b)
    (ha' : Measurable a') (hb' : Measurable b') (hw : Measurable w)
    (hwb : ∀ᵐ x ∂xLaw M, |w x| ≤ D) :
    Integrable (fun x => (∫ y,
      w x * (indicator (a' x < y ∧ y ≤ b' x) -
        indicator (a x < y ∧ y ≤ b x)) ∂treatedLaw M L k x) ^ 2) (xLaw M) ∧
    (∫ x, (∫ y, w x * (indicator (a' x < y ∧ y ≤ b' x) -
        indicator (a x < y ∧ y ≤ b x)) ∂treatedLaw M L k x) ^ 2 ∂xLaw M) ≤
      ∫ x, ∫ y, (w x * (indicator (a' x < y ∧ y ≤ b' x) -
        indicator (a x < y ∧ y ≤ b x))) ^ 2 ∂treatedLaw M L k x ∂xLaw M := by
  let f : X × ℝ → ℝ := fun z => w z.1 *
    (indicator (a' z.1 < z.2 ∧ z.2 ≤ b' z.1) -
      indicator (a z.1 < z.2 ∧ z.2 ≤ b z.1))
  have hB (c d : X → ℝ) (hc : Measurable c) (hd : Measurable d) :
      Measurable (fun z : X × ℝ => indicator (c z.1 < z.2 ∧ z.2 ≤ d z.1)) := by
    unfold indicator
    apply Measurable.ite
    · exact (measurableSet_lt (hc.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (hd.comp measurable_fst))
    · fun_prop
    · fun_prop
  have hf : Measurable f := (hw.comp measurable_fst).mul
    ((hB a' b' ha' hb').sub (hB a b ha hb))
  have hmem (x : X) : MemLp (fun y => f (x, y)) 2 (treatedLaw M L k x) := by
    let := treatedLaw_isFiniteMeasure M L k x
    apply MemLp.of_bound (by
      first | fun_prop | exact (hf.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      |w x|
    apply Eventually.of_forall
    intro y
    dsimp only [f]
    unfold indicator
    split_ifs <;> simp [Real.norm_eq_abs]
  exact treatedLaw_integrated_sq_mean_le M L k f hf hmem
    (treatedLaw_weighted_quantile_band_integrated_sq_bound M L k a b a' b' w D
      ha hb ha' hb' hw hwb).1

-- Both conditional means and conditional second moments are controlled by
-- the same two moving endpoint indicators in the roadmap.
-- @node: treatedLaw_weighted_quantile_band_mean_sq_tendsto_probability_zero
/-- Suppose [the true lower endpoint](hyp:ha) and [true upper endpoint](hyp:hb) are measurable, [all fitted lower endpoints](hyp:hah), [all fitted upper endpoints](hyp:hbh), and [all fitted weights](hyp:hw) are measurable, and [the weights share an almost-sure absolute bound under the covariate law](hyp:hwb). If [the integrated squared lower-threshold indicator error converges to zero in probability at even sample sizes](hyp:hA) and [the corresponding upper-threshold error converges to zero as well](hyp:hB), [the covariate integral of the squared conditional treated-law mean of the weighted band change converges to zero in probability at those sample sizes](goal). -/
lemma treatedLaw_weighted_quantile_band_mean_sq_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X) (k : ℕ)
    (a b : X → ℝ) (ah bh w : ℕ → A → X → ℝ) (D : ℝ)
    (ha : Measurable a) (hb : Measurable b)
    (hah : ∀ n s, Measurable (ah n s)) (hbh : ∀ n s, Measurable (bh n s))
    (hw : ∀ n s, Measurable (w n s))
    (hwb : ∀ n s, ∀ᵐ x ∂xLaw M, |w n s x| ≤ D)
    (hA : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n s => ∫ x, ∫ y, (indicator (y ≤ ah (2*(n+1)) s x) -
        indicator (y ≤ a x)) ^ 2 ∂treatedLaw M L k x ∂xLaw M)
      atTop (fun _ _ => 0))
    (hB : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n s => ∫ x, ∫ y, (indicator (y ≤ bh (2*(n+1)) s x) -
        indicator (y ≤ b x)) ^ 2 ∂treatedLaw M L k x ∂xLaw M)
      atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n s => ∫ x, (∫ y,
        w (2*(n+1)) s x * (indicator (ah (2*(n+1)) s x < y ∧
            y ≤ bh (2*(n+1)) s x) - indicator (a x < y ∧ y ≤ b x))
          ∂treatedLaw M L k x) ^ 2 ∂xLaw M) atTop (fun _ _ => 0) := by
  have hs := treatedLaw_weighted_quantile_band_sq_tendsto_probability_zero
    M μ L k a b ah bh w D ha hb hah hbh hw hwb hA hB
  apply probability_zero_of_nonneg_le μ _ _ hs
  intro n
  apply Eventually.of_forall
  intro s
  exact ⟨integral_nonneg fun x => sq_nonneg _,
    (treatedLaw_weighted_quantile_band_mean_sq_bound M L k a b
      (ah (2*(n+1)) s) (bh (2*(n+1)) s) (w (2*(n+1)) s) D
      ha hb (hah _ s) (hbh _ s) (hw _ s) (hwb _ s)).2⟩

-- @node: encoded_continuous_weighted_quantile_band_mean_sq_tendsto_probability_zero
/-- Suppose [the true continuous nuisance is admissible](hyp:he0), [all fitted nuisances satisfy continuous clipping](hyp:hclip), [their fitted shares lie in the simplex](hyp:hshares), [every encoded fitted component is measurable](hyp:hm), [boundary densities are bounded](hyp:hd), and [the encoded nuisance components satisfy the finite nuisance rate conditions](hyp:hrates). If [the treated level is the level just above the first boundary or its positive current level](hyp:hkc) and [it also satisfies this adjacency condition for the second boundary](hyp:hkd), [the covariate integral of the squared conditional treated-law mean of the band change between the two fitted boundaries, weighted by a fitted regular policy-union probability, converges to zero in probability along even sample sizes](goal). -/
lemma encoded_continuous_weighted_quantile_band_mean_sq_tendsto_probability_zero
    [Fintype Z] (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n s, ContClipping M L (eh n s))
    (hshares : ∀ n s, ContFittedSharesSimplex L (eh n s))
    (hm : ∀ n s c, Measurable (contComponent M L (eh n s) c))
    (hd : BoundaryDensitiesBounded M L)
    (hrates : FiniteNuisanceRates M μ (fun n s => contComponent M L (eh n s))
      (contComponent M L (trueNuisance M L)))
    (c d : BoundaryIndex L) (g : RegularIndex L) (k' : ℕ)
    (hkc : k' = c.val.1 + 1 ∨ (1 ≤ c.val.1 ∧ k' = c.val.1))
    (hkd : k' = d.val.1 + 1 ∨ (1 ≤ d.val.1 ∧ k' = d.val.1)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n s => ∫ x, (∫ y,
        (eh (2*(n+1)) s).gamma g x *
          (indicator ((eh (2*(n+1)) s).nu c x < y ∧
              y ≤ (eh (2*(n+1)) s).nu d x) -
            indicator ((trueNuisance M L).nu c x < y ∧
              y ≤ (trueNuisance M L).nu d x))
          ∂treatedLaw M L k' x) ^ 2 ∂xLaw M) atTop (fun _ _ => 0) := by
  let er := fun n s => restrictContShares L (eh n s)
  have her n s : ContAdmissible M L (er n s) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n s)
      (hclip n s) (hshares n s) (hm n s)
  have hcoords n s : Measurable ((er n s).nu c) ∧ Measurable ((er n s).nu d) ∧
      Measurable ((er n s).gamma g) ∧
      (∀ᵐ x ∂xLaw M, |(er n s).gamma g x| ≤ 1) := by
    rcases her n s with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hg, hgm,
      _, _, _, hnm, _⟩
    refine ⟨hnm c, hnm d, hgm g, ?_⟩
    filter_upwards [hg g] with x hx
    simpa only [abs_of_nonneg hx.1] using hx.2
  have ht (b : BoundaryIndex L) : Measurable ((trueNuisance M L).nu b) := by
    first | fun_prop | skip
    rcases he0 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hnu, _⟩
    exact hnu b
  exact treatedLaw_weighted_quantile_band_mean_sq_tendsto_probability_zero M μ L k'
    ((trueNuisance M L).nu c) ((trueNuisance M L).nu d)
    (fun n s => (er n s).nu c) (fun n s => (er n s).nu d)
    (fun n s => (er n s).gamma g) 1 (ht c) (ht d)
    (fun n s => (hcoords n s).1) (fun n s => (hcoords n s).2.1)
    (fun n s => (hcoords n s).2.2.1) (fun n s => (hcoords n s).2.2.2)
    (encoded_continuous_quantile_oracle_remainders M μ L he0 eh hclip hshares hm
      hd hrates c k' hkc).2
    (encoded_continuous_quantile_oracle_remainders M μ L he0 eh hclip hshares hm
      hd hrates d k' hkd).2


end Papers.TbsPrteOptimalTransport
