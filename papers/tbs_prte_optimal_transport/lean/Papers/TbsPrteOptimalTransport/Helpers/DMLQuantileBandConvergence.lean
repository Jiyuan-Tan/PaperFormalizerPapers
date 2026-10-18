module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLWeightedQuantileIndicator
/-! Moving treated bands in the continuous DML score.
A band can change only if one of its endpoint indicators changes. This remains
true for crossed fitted endpoints, so no ordering condition is imposed on fits.
Bounded fitted weights preserve the resulting squared-error convergence. -/
public section
set_option linter.style.openClassical false
set_option linter.style.whitespace false
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

-- @node: measurable_treatedLaw_integral_prod
/-- If [a function of covariates and outcomes is measurable](hyp:hf), [its integral against the conditional treated-outcome law at any level is measurable as a function of covariates](goal). -/
@[fun_prop] lemma measurable_treatedLaw_integral_prod
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (k : ℕ)
    (f : X × ℝ → ℝ) (hf : Measurable f) :
    Measurable (fun x => ∫ y, f (x, y) ∂treatedLaw M L k x) := by
  first | fun_prop | skip
  let κ := condDistrib (fun s => (M.Y s, M.W s, M.Zv s)) M.Xv M.law.toMeasure
  let t : Set (ℝ × ℝ × Z) := {z | z.2.1 = 1 ∧ z.2.2 ∈ (L.S k : Set Z)}
  have ht : MeasurableSet t :=
    (measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const).inter
      ((L.S k).measurableSet.preimage (measurable_snd.comp measurable_snd))
  let F : X × (ℝ × ℝ × Z) → ℝ := fun z => f (z.1, z.2.1)
  have hF : StronglyMeasurable F := by
    apply Measurable.stronglyMeasurable
    exact hf.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  let G := (Prod.snd ⁻¹' t).indicator F
  have hG : StronglyMeasurable G := hF.indicator (ht.preimage measurable_snd)
  have hi : Measurable (fun x => ∫ z, G (x, z) ∂κ x) :=
    (hG.integral_kernel_prod_right').measurable
  have hm : Measurable (fun x => (κ x).restrict t univ) := by
    simpa only [Measure.restrict_apply_univ] using κ.measurable_coe ht
  have hid (x : X) : (∫ y, f (x, y) ∂treatedLaw M L k x) =
      ((κ x).restrict t univ)⁻¹.toReal * ∫ z, G (x, z) ∂κ x := by
    have hfx : StronglyMeasurable (fun y : ℝ => f (x, y)) :=
      (hf.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable
    rw [treatedLaw, integral_smul_measure, smul_eq_mul,
      integral_map_of_stronglyMeasurable measurable_fst hfx]
    congr 1
    rw [← integral_indicator ht]
    rfl
  simp_rw [hid]
  fun_prop

-- The two Boolean endpoint tests determine the band, even when endpoints cross.
-- @node: quantile_band_indicator_sq_bound
/-- [The squared weighted change in membership of a band that excludes its lower endpoint and includes its upper endpoint is bounded by the sum of the squared weighted changes in the two endpoint threshold indicators, even when endpoints cross](goal). -/
lemma quantile_band_indicator_sq_bound (a b a' b' y w : ℝ) :
    (w * (indicator (a' < y ∧ y ≤ b') - indicator (a < y ∧ y ≤ b))) ^ 2 ≤
      (w * (indicator (y ≤ a') - indicator (y ≤ a))) ^ 2 +
        (w * (indicator (y ≤ b') - indicator (y ≤ b))) ^ 2 := by
  have h : (indicator (a' < y ∧ y ≤ b') - indicator (a < y ∧ y ≤ b)) ^ 2 ≤
      (indicator (y ≤ a') - indicator (y ≤ a)) ^ 2 +
        (indicator (y ≤ b') - indicator (y ≤ b)) ^ 2 := by
    simp only [← not_le, indicator]
    split_ifs <;> norm_num <;> tauto
  simp only [mul_pow]
  nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg w)]

-- @node: treatedLaw_weighted_quantile_band_integrated_sq_bound
/-- If [the original lower endpoint](hyp:ha), [original upper endpoint](hyp:hb), [replacement lower endpoint](hyp:ha'), [replacement upper endpoint](hyp:hb'), and [weight](hyp:hw) are measurable, and [the absolute weight is almost surely bounded by a fixed constant under the covariate law](hyp:hwb), [the conditional treated-law squared weighted band change is integrable over covariates, and its integral is at most the sum of the corresponding integrated squared changes in the two endpoint threshold indicators](goal). -/
lemma treatedLaw_weighted_quantile_band_integrated_sq_bound
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (k : ℕ)
    (a b a' b' w : X → ℝ) (D : ℝ)
    (ha : Measurable a) (hb : Measurable b)
    (ha' : Measurable a') (hb' : Measurable b') (hw : Measurable w)
    (hwb : ∀ᵐ x ∂xLaw M, |w x| ≤ D) :
    Integrable (fun x => ∫ y,
      (w x * (indicator (a' x < y ∧ y ≤ b' x) -
        indicator (a x < y ∧ y ≤ b x))) ^ 2 ∂treatedLaw M L k x) (xLaw M) ∧
    (∫ x, ∫ y, (w x * (indicator (a' x < y ∧ y ≤ b' x) -
        indicator (a x < y ∧ y ≤ b x))) ^ 2 ∂treatedLaw M L k x ∂xLaw M) ≤
      (∫ x, ∫ y, (w x * (indicator (y ≤ a' x) - indicator (y ≤ a x))) ^ 2
        ∂treatedLaw M L k x ∂xLaw M) +
      (∫ x, ∫ y, (w x * (indicator (y ≤ b' x) - indicator (y ≤ b x))) ^ 2
        ∂treatedLaw M L k x ∂xLaw M) := by
  have hI (x : X) (t : ℝ) : MemLp (fun y : ℝ => indicator (y ≤ t)) 2
      (treatedLaw M L k x) := by
    let := treatedLaw_isFiniteMeasure M L k x
    apply MemLp.of_bound (by
      unfold indicator
      exact (Measurable.ite measurableSet_Iic measurable_const
        measurable_const).aestronglyMeasurable) 1
    exact Eventually.of_forall (fun y => by unfold indicator; split_ifs <;> norm_num)
  let R := fun x => ∫ y, (w x * (indicator (a' x < y ∧ y ≤ b' x) -
    indicator (a x < y ∧ y ≤ b x))) ^ 2 ∂treatedLaw M L k x
  let U := fun x => ∫ y, (w x * (indicator (y ≤ a' x) - indicator (y ≤ a x))) ^ 2
    ∂treatedLaw M L k x
  let V := fun x => ∫ y, (w x * (indicator (y ≤ b' x) - indicator (y ≤ b x))) ^ 2
    ∂treatedLaw M L k x
  have hUi : Integrable U (xLaw M) :=
    (treatedLaw_weighted_quantile_indicator_integrated_sq_bound M L k a a' w D
      ha ha' hw hwb).1
  have hVi : Integrable V (xLaw M) :=
    (treatedLaw_weighted_quantile_indicator_integrated_sq_bound M L k b b' w D
      hb hb' hw hwb).1
  have hbound (x : X) : R x ≤ U x + V x := by
    have hiA := (((hI x (a' x)).sub (hI x (a x))).const_mul (w x)).integrable_sq
    have hiB := (((hI x (b' x)).sub (hI x (b x))).const_mul (w x)).integrable_sq
    simp only [Pi.sub_apply] at hiA hiB
    dsimp only [R, U, V]
    rw [← integral_add hiA hiB]
    apply integral_mono_of_nonneg
      (Eventually.of_forall (fun y => sq_nonneg _)) (hiA.add hiB)
    exact Eventually.of_forall (fun y => quantile_band_indicator_sq_bound
      (a x) (b x) (a' x) (b' x) y (w x))
  have hRm : Measurable R := by
    apply measurable_treatedLaw_integral_prod M L k (fun z : X × ℝ =>
      (w z.1 * (indicator (a' z.1 < z.2 ∧ z.2 ≤ b' z.1) -
        indicator (a z.1 < z.2 ∧ z.2 ≤ b z.1))) ^ 2)
    have hB (c d : X → ℝ) (hc : Measurable c) (hd : Measurable d) :
        Measurable (fun z : X × ℝ => indicator (c z.1 < z.2 ∧ z.2 ≤ d z.1)) := by
      unfold indicator
      apply Measurable.ite
      · exact (measurableSet_lt (hc.comp measurable_fst) measurable_snd).inter
          (measurableSet_le measurable_snd (hd.comp measurable_fst))
      · fun_prop
      · fun_prop
    exact ((hw.comp measurable_fst).mul ((hB a' b' ha' hb').sub
      (hB a b ha hb))).pow_const 2
  have hR0 (x : X) : 0 ≤ R x := integral_nonneg fun y => sq_nonneg _
  have hRi : Integrable R (xLaw M) := (hUi.add hVi).mono' hRm.aestronglyMeasurable
    (Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hR0 x), Pi.add_apply]
        using hbound x))
  refine ⟨hRi, ?_⟩
  calc
    _ ≤ ∫ x, U x + V x ∂xLaw M :=
      integral_mono_ae hRi (hUi.add hVi) (Eventually.of_forall hbound)
    _ = _ := integral_add hUi hVi

-- @node: treatedLaw_weighted_quantile_band_sq_tendsto_probability_zero
/-- Suppose [the true lower endpoint](hyp:ha) and [true upper endpoint](hyp:hb) are measurable, [every fitted lower endpoint](hyp:hah), [every fitted upper endpoint](hyp:hbh), and [every fitted weight](hyp:hw) are measurable, and [the weights have a common almost-sure absolute bound under the covariate law](hyp:hwb). If [the integrated squared lower-threshold indicator error vanishes in probability along even sample sizes](hyp:hA) and [the upper-threshold error does likewise](hyp:hB), [the squared weighted band-indicator error, integrated over the conditional treated-outcome and covariate laws, converges to zero in probability along the same sample sizes](goal). -/
lemma treatedLaw_weighted_quantile_band_sq_tendsto_probability_zero
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
      (fun n s => ∫ x, ∫ y,
        (w (2*(n+1)) s x * (indicator (ah (2*(n+1)) s x < y ∧
            y ≤ bh (2*(n+1)) s x) - indicator (a x < y ∧ y ≤ b x))) ^ 2
          ∂treatedLaw M L k x ∂xLaw M) atTop (fun _ _ => 0) := by
  have hAw := treatedLaw_weighted_quantile_indicator_sq_tendsto_probability_zero
    M μ L k a ah w D ha hah hw hwb hA
  have hBw := treatedLaw_weighted_quantile_indicator_sq_tendsto_probability_zero
    M μ L k b bh w D hb hbh hw hwb hB
  have hneg : Continuous (fun t : ℝ => -t) := by fun_prop
  have hBn := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    hneg.continuousAt hBw
  simp only [neg_zero] at hBn
  have hsum := hAw.sub hBn
  simp only [sub_zero, sub_neg_eq_add] at hsum
  apply probability_zero_of_nonneg_le μ _ _ hsum
  intro n
  apply Eventually.of_forall
  intro s
  exact ⟨integral_nonneg fun x => integral_nonneg fun y => sq_nonneg _,
    (treatedLaw_weighted_quantile_band_integrated_sq_bound M L k a b
      (ah (2*(n+1)) s) (bh (2*(n+1)) s) (w (2*(n+1)) s) D
      ha hb (hah _ s) (hbh _ s) (hw _ s) (hwb _ s)).2⟩

-- The actual product-score weight is clipped; its convergence is unnecessary
-- for the part of the score discrepancy caused solely by moving boundaries.
-- @node: encoded_continuous_weighted_quantile_band_sq_tendsto_probability_zero
/-- Suppose [the true continuous nuisance is admissible](hyp:he0), [all fitted nuisances satisfy continuous clipping](hyp:hclip), [their fitted shares lie in the simplex](hyp:hshares), [every encoded fitted component is measurable](hyp:hm), [boundary densities are bounded](hyp:hd), and [the encoded nuisance components satisfy the finite nuisance rate conditions](hyp:hrates). If [the treated level is the level just above the first boundary or its positive current level](hyp:hkc) and [the same adjacency condition holds for the second boundary](hyp:hkd), [the integrated squared change in the band between these fitted boundaries, weighted by any fitted regular policy-union probability, converges to zero in probability along even sample sizes](goal). -/
lemma encoded_continuous_weighted_quantile_band_sq_tendsto_probability_zero
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
      (fun n s => ∫ x, ∫ y,
        ((eh (2*(n+1)) s).gamma g x *
          (indicator ((eh (2*(n+1)) s).nu c x < y ∧
              y ≤ (eh (2*(n+1)) s).nu d x) -
            indicator ((trueNuisance M L).nu c x < y ∧
              y ≤ (trueNuisance M L).nu d x))) ^ 2
          ∂treatedLaw M L k' x ∂xLaw M) atTop (fun _ _ => 0) := by
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
  exact treatedLaw_weighted_quantile_band_sq_tendsto_probability_zero M μ L k'
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
