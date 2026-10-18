module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLMinusOutcomeConvergence
/-! Gamma-weighted outcome-band residual convergence for continuous DML.
These are the IFJ terms appearing directly in the fractional product score.
Moving boundaries, fitted regressions, and clipped denominators are controlled
by the encoded nuisance rates. -/
public section
set_option linter.unnecessarySimpa false
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

-- @node: encoded_continuous_gamma_plus_IFJ_sq_tendsto_probability_zero
/-- Assume [admissibility of the true nuisances](hyp:he0), [clipping of fitted nuisances](hyp:hclip), [nonnegative fitted shares summing to one](hyp:hshares), [measurability of encoded fitted components](hyp:hm), [bounded treated-outcome densities near band boundaries](hyp:hd), and [componentwise L2 errors of smaller order in probability than the inverse fourth root of sample size](hyp:hr). With [baseline overlap](hyp:hov), [overlap-based fitted denominator clipping](hyp:hden), and [a nonterminal population level](hyp:hk), [the observation-integrated squared error of the gamma-weighted upper treated outcome-band residual converges in probability to zero along sample sizes twice one plus the index](goal). -/
lemma encoded_continuous_gamma_plus_IFJ_sq_tendsto_probability_zero
    [Fintype Z]
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hd : BoundaryDensitiesBounded M L)
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L)))
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hden : ∀ n t, ContDenominatorsClipped L (eh n t) cpi)
    (g : RegularIndex L) (k j : ℕ) (hk : k < L.K) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o : Obs X Z,
        ((eh (2 * (n + 1)) t).gamma g o.1 *
            IFJ M L (eh (2 * (n + 1)) t) true k j o -
          (trueNuisance M L).gamma g o.1 *
            IFJ M L (trueNuisance M L) true k j o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  classical
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  let i : PositiveIndex L.K := ⟨k + 1, by omega⟩
  let B := |M.yMin| + |M.yMax|
  let w := fun (e : NuisanceCont L) x => e.gamma g x
  let J := fun (e : NuisanceCont L) => meanValue e.Jplus k j
  have hw (e : NuisanceCont L) (he : ContAdmissible M L e) :
      Measurable (w e) ∧ (∀ᵐ x ∂xLaw M, |w e x| ≤ 1) := by
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hg, hgm, _⟩
    refine ⟨by fun_prop, ?_⟩
    filter_upwards [hg g] with x hx
    simpa only [w, abs_of_nonneg hx.1] using hx.2
  have hJ (e : NuisanceCont L) (he : ContAdmissible M L e) :
      Measurable (J e) ∧ (∀ᵐ x ∂xLaw M, |J e x| ≤ B) :=
    ⟨by fun_prop,
      (continuous_admissible_band_means_abs_bound M L e he k j).1⟩
  have hpi (e : NuisanceCont L) (he : ContAdmissible M L e) :
      Measurable (e.piLev i) ∧ (∀ᵐ x ∂xLaw M, |e.piLev i x| ≤ 1) := by
    rcases he with ⟨_, _, _, _, hb, hm, _⟩
    refine ⟨by fun_prop, ?_⟩
    filter_upwards [hb i] with x hx
    simpa only [abs_of_nonneg hx.1] using hx.2
  have hmem (f : X → ℝ) (hf : Measurable f) (R : ℝ)
      (hb : ∀ᵐ x ∂xLaw M, |f x| ≤ R) : MemLp f 2 (xLaw M) :=
    MemLp.of_bound hf.aestronglyMeasurable R (by simpa only [Real.norm_eq_abs] using hb)
  have hmprod (e : NuisanceCont L) (he : ContAdmissible M L e) :
      Measurable (fun x => w e x * J e x) ∧
        (∀ᵐ x ∂xLaw M, |w e x * J e x| ≤ B) := by
    refine ⟨by first | fun_prop | exact (hw e he).1.mul (hJ e he).1, ?_⟩
    filter_upwards [(hw e he).2, (hJ e he).2] with x hx hy
    rw [abs_mul]
    exact (mul_le_mul hx hy (abs_nonneg _) zero_le_one).trans (by simp)
  obtain ⟨_, _, hrpi, _, _, _, hrg, _⟩ :=
    continuous_component_rates_to_oracle_rates M μ L eh (trueNuisance M L) hr
  have hrw := nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hrg g
  have hrJ : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (J (er (2 * (n + 1)) t) x - J (trueNuisance M L) x) ^ 2
        ∂xLaw M) atTop (fun _ _ => 0) := by
    let z0 : Z := Classical.choice inferInstance
    simpa only [contComponent, J, er, restrictContShares] using
      nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hr (11, k, j, z0)
  have hrm := dml_weighted_residual_sq_tendsto_probability_zero μ (xLaw M)
    (w (trueNuisance M L)) (J (trueNuisance M L))
    (fun n t => w (er (2 * (n + 1)) t)) (fun n t => J (er (2 * (n + 1)) t)) 1 B
    (hw _ he0).1 (hJ _ he0).1 (fun n t => (hw _ (her _ t)).1)
    (fun n t => (hJ _ (her _ t)).1)
    (fun n t => (hmem _ (hw _ (her _ t)).1 _ (hw _ (her _ t)).2).sub
      (hmem _ (hw _ he0).1 _ (hw _ he0).2))
    (fun n t => (hmem _ (hJ _ (her _ t)).1 _ (hJ _ (her _ t)).2).sub
      (hmem _ (hJ _ he0).1 _ (hJ _ he0).2))
    (fun n t => (hw _ (her _ t)).2) (fun _ _ => (hJ _ he0).2) hrw hrJ
  have hcl n t : ∀ᵐ x ∂xLaw M,
      cpi / 2 ≤ (trueNuisance M L).piLev i x ∧ cpi / 2 ≤ (er n t).piLev i x := by
    apply Eventually.of_forall
    intro x
    refine ⟨?_, (hden n t).1 i x |>.1⟩
    have hx := hov.2 x i.val i.property.1 i.property.2
    change cpi / 2 ≤ (levelSetProb M L).1 i.val x
    linarith [hov.1]
  have hs := observationLaw_changing_outcome_band_regression_sq_tendsto_probability_zero
    M μ L (k + 1) (nuValue M (trueNuisance M L) k j)
    (nuValue M (trueNuisance M L) k (j + 1)) (w (trueNuisance M L))
    (fun x => w (trueNuisance M L) x * J (trueNuisance M L) x)
    ((trueNuisance M L).piLev i)
    (fun n t => nuValue M (er n t) k j) (fun n t => nuValue M (er n t) k (j + 1))
    (fun n t => w (er n t)) (fun n t x => w (er n t) x * J (er n t) x)
    (fun n t => (er n t).piLev i) (cpi / 2) 1 B B
    (by linarith [hov.1]) zero_le_one (by dsimp only [B]; positivity)
    (by fun_prop) (by fun_prop) (hw _ he0).1 (hmprod _ he0).1 (hpi _ he0).1
    (fun n t => continuous_admissible_nuValue_measurable M L _ (her n t) k j)
    (fun n t => continuous_admissible_nuValue_measurable M L _ (her n t) k (j + 1))
    (fun n t => (hw _ (her n t)).1) (fun n t => (hmprod _ (her n t)).1)
    (fun n t => (hpi _ (her n t)).1) (hw _ he0).2 (fun n t => (hw _ (her n t)).2)
    (by filter_upwards [continuous_admissible_nuValue_abs_bound M L _ he0 k j,
          continuous_admissible_nuValue_abs_bound M L _ he0 k (j + 1)] with x ha hb
        exact ⟨ha, hb⟩)
    (fun n t => by
      filter_upwards [continuous_admissible_nuValue_abs_bound M L _ (her n t) k j,
        continuous_admissible_nuValue_abs_bound M L _ (her n t) k (j + 1)] with x ha hb
      exact ⟨ha, hb⟩)
    (hmprod _ he0).2 (fun n t => (hmprod _ (her n t)).2) hcl
    (fun n t => (hmem _ (hw _ (her n t)).1 _ (hw _ (her n t)).2).sub
      (hmem _ (hw _ he0).1 _ (hw _ he0).2))
    (fun n t => (hmem _ (hmprod _ (her n t)).1 _ (hmprod _ (her n t)).2).sub
      (hmem _ (hmprod _ he0).1 _ (hmprod _ he0).2))
    (fun n t => (hmem _ (hpi _ (her n t)).1 _ (hpi _ (her n t)).2).sub
      (hmem _ (hpi _ he0).1 _ (hpi _ he0).2))
    (encoded_continuous_nuValue_indicator_sq_tendsto_probability_zero
      M μ L he0 eh hclip hshares hm hd hr k j (k + 1) (Or.inl rfl))
    (encoded_continuous_nuValue_indicator_sq_tendsto_probability_zero
      M μ L he0 eh hclip hshares hm hd hr k (j + 1) (k + 1) (Or.inl rfl))
    hrw hrm (nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hrpi i)
  convert hs using 1
  funext n t
  congr 1
  funext o
  have hlev : 1 ≤ k + 1 ∧ k + 1 ≤ L.K := by omega
  simp only [IFJ, Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false, if_true,
    w, J, er, restrictContShares, nuValue, positiveValue, dif_pos hlev, i]
  ring

-- @node: encoded_continuous_gamma_minus_IFJ_sq_tendsto_probability_zero
/-- Suppose [the true nuisances are admissible](hyp:he0), [fitted nuisances are clipped](hyp:hclip), [their shares are nonnegative and sum to one](hyp:hshares), [encoded fitted components are measurable](hyp:hm), [treated-outcome densities are bounded near band boundaries](hyp:hd), and [componentwise L2 errors are of smaller order in probability than the inverse fourth root of sample size](hyp:hr). Under [baseline overlap](hyp:hov) and [overlap-based fitted denominator clipping](hyp:hden), for [a population level at least one](hyp:hk0) that [is nonterminal](hyp:hk), [the observation-integrated squared error of the gamma-weighted lower treated outcome-band residual converges in probability to zero along sample sizes twice one plus the index](goal). -/
lemma encoded_continuous_gamma_minus_IFJ_sq_tendsto_probability_zero
    [Fintype Z]
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hd : BoundaryDensitiesBounded M L)
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L)))
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hden : ∀ n t, ContDenominatorsClipped L (eh n t) cpi)
    (g : RegularIndex L) (k j : ℕ) (hk0 : 1 ≤ k) (hk : k < L.K) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o : Obs X Z,
        ((eh (2 * (n + 1)) t).gamma g o.1 *
            IFJ M L (eh (2 * (n + 1)) t) false k j o -
          (trueNuisance M L).gamma g o.1 *
            IFJ M L (trueNuisance M L) false k j o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  classical
  let er := fun n t => restrictContShares L (eh n t)
  have her n t : ContAdmissible M L (er n t) :=
    restrictContShares_admissible_of_encoded_clipping M L (eh n t)
      (hclip n t) (hshares n t) (hm n t)
  have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  let i : PositiveIndex L.K := ⟨k, by omega⟩
  let B := |M.yMin| + |M.yMax|
  let w := fun (e : NuisanceCont L) x => e.gamma g x
  let J := fun (e : NuisanceCont L) => minusMeanValue e.Jminus k j
  have hw (e : NuisanceCont L) (he : ContAdmissible M L e) :
      Measurable (w e) ∧ (∀ᵐ x ∂xLaw M, |w e x| ≤ 1) := by
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hg, hgm, _⟩
    refine ⟨by fun_prop, ?_⟩
    filter_upwards [hg g] with x hx
    simpa only [w, abs_of_nonneg hx.1] using hx.2
  have hJ (e : NuisanceCont L) (he : ContAdmissible M L e) :
      Measurable (J e) ∧ (∀ᵐ x ∂xLaw M, |J e x| ≤ B) :=
    ⟨by fun_prop,
      (continuous_admissible_band_means_abs_bound M L e he k j).2⟩
  have hpi (e : NuisanceCont L) (he : ContAdmissible M L e) :
      Measurable (e.piLev i) ∧ (∀ᵐ x ∂xLaw M, |e.piLev i x| ≤ 1) := by
    rcases he with ⟨_, _, _, _, hb, hm, _⟩
    refine ⟨by fun_prop, ?_⟩
    filter_upwards [hb i] with x hx
    simpa only [abs_of_nonneg hx.1] using hx.2
  have hmem (f : X → ℝ) (hf : Measurable f) (R : ℝ)
      (hb : ∀ᵐ x ∂xLaw M, |f x| ≤ R) : MemLp f 2 (xLaw M) :=
    MemLp.of_bound hf.aestronglyMeasurable R (by simpa only [Real.norm_eq_abs] using hb)
  have hmprod (e : NuisanceCont L) (he : ContAdmissible M L e) :
      Measurable (fun x => w e x * J e x) ∧
        (∀ᵐ x ∂xLaw M, |w e x * J e x| ≤ B) := by
    refine ⟨by first | fun_prop | exact (hw e he).1.mul (hJ e he).1, ?_⟩
    filter_upwards [(hw e he).2, (hJ e he).2] with x hx hy
    rw [abs_mul]
    exact (mul_le_mul hx hy (abs_nonneg _) zero_le_one).trans (by simp)
  obtain ⟨_, _, hrpi, _, _, _, hrg, _⟩ :=
    continuous_component_rates_to_oracle_rates M μ L eh (trueNuisance M L) hr
  have hrw := nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hrg g
  have hrJ : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ x, (J (er (2 * (n + 1)) t) x - J (trueNuisance M L) x) ^ 2
        ∂xLaw M) atTop (fun _ _ => 0) := by
    let z0 : Z := Classical.choice inferInstance
    simpa only [contComponent, J, er, restrictContShares] using
      nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hr (12, k, j, z0)
  have hrm := dml_weighted_residual_sq_tendsto_probability_zero μ (xLaw M)
    (w (trueNuisance M L)) (J (trueNuisance M L))
    (fun n t => w (er (2 * (n + 1)) t)) (fun n t => J (er (2 * (n + 1)) t)) 1 B
    (hw _ he0).1 (hJ _ he0).1 (fun n t => (hw _ (her _ t)).1)
    (fun n t => (hJ _ (her _ t)).1)
    (fun n t => (hmem _ (hw _ (her _ t)).1 _ (hw _ (her _ t)).2).sub
      (hmem _ (hw _ he0).1 _ (hw _ he0).2))
    (fun n t => (hmem _ (hJ _ (her _ t)).1 _ (hJ _ (her _ t)).2).sub
      (hmem _ (hJ _ he0).1 _ (hJ _ he0).2))
    (fun n t => (hw _ (her _ t)).2) (fun _ _ => (hJ _ he0).2) hrw hrJ
  have hcl n t : ∀ᵐ x ∂xLaw M,
      cpi / 2 ≤ (trueNuisance M L).piLev i x ∧ cpi / 2 ≤ (er n t).piLev i x := by
    apply Eventually.of_forall
    intro x
    refine ⟨?_, (hden n t).1 i x |>.1⟩
    have hx := hov.2 x i.val i.property.1 i.property.2
    change cpi / 2 ≤ (levelSetProb M L).1 i.val x
    linarith [hov.1]
  have hs := observationLaw_changing_outcome_band_regression_sq_tendsto_probability_zero
    M μ L k (nuValue M (trueNuisance M L) k j)
    (nuValue M (trueNuisance M L) k (j + 1)) (w (trueNuisance M L))
    (fun x => w (trueNuisance M L) x * J (trueNuisance M L) x)
    ((trueNuisance M L).piLev i)
    (fun n t => nuValue M (er n t) k j) (fun n t => nuValue M (er n t) k (j + 1))
    (fun n t => w (er n t)) (fun n t x => w (er n t) x * J (er n t) x)
    (fun n t => (er n t).piLev i) (cpi / 2) 1 B B
    (by linarith [hov.1]) zero_le_one (by dsimp only [B]; positivity)
    (by fun_prop) (by fun_prop) (hw _ he0).1 (hmprod _ he0).1 (hpi _ he0).1
    (fun n t => continuous_admissible_nuValue_measurable M L _ (her n t) k j)
    (fun n t => continuous_admissible_nuValue_measurable M L _ (her n t) k (j + 1))
    (fun n t => (hw _ (her n t)).1) (fun n t => (hmprod _ (her n t)).1)
    (fun n t => (hpi _ (her n t)).1) (hw _ he0).2 (fun n t => (hw _ (her n t)).2)
    (by filter_upwards [continuous_admissible_nuValue_abs_bound M L _ he0 k j,
          continuous_admissible_nuValue_abs_bound M L _ he0 k (j + 1)] with x ha hb
        exact ⟨ha, hb⟩)
    (fun n t => by
      filter_upwards [continuous_admissible_nuValue_abs_bound M L _ (her n t) k j,
        continuous_admissible_nuValue_abs_bound M L _ (her n t) k (j + 1)] with x ha hb
      exact ⟨ha, hb⟩)
    (hmprod _ he0).2 (fun n t => (hmprod _ (her n t)).2) hcl
    (fun n t => (hmem _ (hw _ (her n t)).1 _ (hw _ (her n t)).2).sub
      (hmem _ (hw _ he0).1 _ (hw _ he0).2))
    (fun n t => (hmem _ (hmprod _ (her n t)).1 _ (hmprod _ (her n t)).2).sub
      (hmem _ (hmprod _ he0).1 _ (hmprod _ he0).2))
    (fun n t => (hmem _ (hpi _ (her n t)).1 _ (hpi _ (her n t)).2).sub
      (hmem _ (hpi _ he0).1 _ (hpi _ he0).2))
    (encoded_continuous_nuValue_indicator_sq_tendsto_probability_zero
      M μ L he0 eh hclip hshares hm hd hr k j k (Or.inr ⟨hk0, rfl⟩))
    (encoded_continuous_nuValue_indicator_sq_tendsto_probability_zero
      M μ L he0 eh hclip hshares hm hd hr k (j + 1) k (Or.inr ⟨hk0, rfl⟩))
    hrw hrm (nuisanceRates_xLaw_sq_tendsto_probability_zero M μ _ _ hrpi i)
  convert hs using 1
  funext n t
  congr 1
  funext o
  have hlev : 1 ≤ k ∧ k ≤ L.K := by omega
  have hkne : k ≠ 0 := by omega
  simp only [IFJ, Bool.not_false, Bool.true_and, Bool.false_eq_true, beq_iff_eq, hkne, if_false,
    w, J, er, restrictContShares, nuValue, positiveValue, dif_pos hlev, i]
  ring


-- @node: encoded_continuous_gamma_minus_IFJ_all_levels_sq_tendsto_probability_zero
/-- Given [admissible true nuisances](hyp:he0), [clipped fitted nuisances](hyp:hclip), [nonnegative fitted shares summing to one](hyp:hshares), [measurable encoded fitted components](hyp:hm), [bounded treated-outcome densities near band boundaries](hyp:hd), and [componentwise L2 errors of smaller order in probability than the inverse fourth root of sample size](hyp:hr), assume [baseline overlap](hyp:hov) and [overlap-based fitted denominator clipping](hyp:hden). At [any nonterminal population level, including zero](hyp:hk), [the observation-integrated squared error of the gamma-weighted lower treated outcome-band residual converges in probability to zero along sample sizes twice one plus the index](goal). -/
lemma encoded_continuous_gamma_minus_IFJ_all_levels_sq_tendsto_probability_zero
    [Fintype Z]
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n t, ContClipping M L (eh n t))
    (hshares : ∀ n t, ContFittedSharesSimplex L (eh n t))
    (hm : ∀ n t d, Measurable (contComponent M L (eh n t) d))
    (hd : BoundaryDensitiesBounded M L)
    (hr : FiniteNuisanceRates M μ (fun n t => contComponent M L (eh n t))
      (contComponent M L (trueNuisance M L)))
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (hden : ∀ n t, ContDenominatorsClipped L (eh n t) cpi)
    (g : RegularIndex L) (k j : ℕ) (hk : k < L.K) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n t => ∫ o : Obs X Z,
        ((eh (2 * (n + 1)) t).gamma g o.1 *
            IFJ M L (eh (2 * (n + 1)) t) false k j o -
          (trueNuisance M L).gamma g o.1 *
            IFJ M L (trueNuisance M L) false k j o) ^ 2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  by_cases hk0 : k = 0
  · subst k
    -- The baseline minus residual is structurally absent from the score.
    simp only [IFJ, Bool.not_false, beq_self_eq_true, Bool.and_self,
      if_true, mul_zero, sub_self, zero_pow (by norm_num : 2 ≠ 0), integral_zero]
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
    intro eps heps
    simpa [not_le_of_gt heps] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
  · exact encoded_continuous_gamma_minus_IFJ_sq_tendsto_probability_zero
      M μ L he0 eh hclip hshares hm hd hr cpi hov hden g k j (by omega) hk

end Papers.TbsPrteOptimalTransport
