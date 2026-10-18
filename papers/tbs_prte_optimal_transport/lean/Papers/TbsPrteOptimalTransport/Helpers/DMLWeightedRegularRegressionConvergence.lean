module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLFractionalTreatmentConvergence
/-! Convergence of the fitted product weight times the fractional regression correction.
Clipping bounds all four residual terms; component rates control the weight and
the unweighted correction separately before their product is assembled. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: fitted_regular_gamma_abs_bound
/-- If [the fitted binary nuisance specification is admissible](hyp:he), then
[its regular gamma weight at any level and boundary has absolute value at most
one almost everywhere under the covariate law](goal). -/
lemma fitted_regular_gamma_abs_bound (L : LevelData Z X) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (k j : ℕ) :
    ∀ᵐ x ∂xLaw M, |regularValue e.gamma k j x| ≤ 1 := by
  unfold regularValue
  split_ifs with hi
  · filter_upwards [he.2.2.2.2.1 ⟨(k,j), hi⟩] with x hx
    rw [abs_of_nonneg hx.2.1]
    exact hx.2.2
  · simp

-- Every residual, including the fixed zero boundary, has the same overlap bound.
-- @node: fitted_regular_regression_correction_abs_bound
/-- If [the fitted binary nuisance specification is admissible](hyp:he), [the
outcome is binary almost surely](hyp:hy), [c is positive](hyp:hc), [all fitted
positive-level instrument probabilities are at least c almost
everywhere](hyp:hclip), and [k is below the highest level](hyp:hk), then [the
fitted regular regression correction has absolute value at most 4/c almost surely
under the observation law](goal). -/
lemma fitted_regular_regression_correction_abs_bound
    (phi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (hy : OutcomeBinaryAE M) (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (k j : ℕ) (hk : k < L.K) :
    ∀ᵐ o ∂observationLaw M,
      |binaryRegularRegressionCorrection phi L e k j o| ≤ 4 / c := by
  filter_upwards [fitted_RP_abs_bound M L e he hy c hc hclip (k+1) (by omega),
    fitted_RP_abs_bound M L e he hy c hc hclip k hk.le,
    fitted_Rp_abs_bound M L e he c hc hclip (k+1) (by omega),
    fitted_Rp_abs_bound M L e he c hc hclip k hk.le] with o hp hm ht hb
  have hD : |Dbd phi L e k j o.1| ≤ 1 := by
    unfold Dbd indicator
    split_ifs <;> norm_num
  have hE : |Edom phi L e k j o.1 * Iact phi L e k j o.1| ≤ 1 := by
    unfold Edom Iact indicator
    split_ifs <;> norm_num
  have hpair : |Dbd phi L e k j o.1 * (RP L e (k+1) o - RP L e k o)| ≤ 2 / c := by
    rw [abs_mul]
    calc
      _ ≤ 1 * (|RP L e (k+1) o| + |RP L e k o|) :=
        mul_le_mul hD (abs_sub _ _) (abs_nonneg _) zero_le_one
      _ ≤ 2 / c := by simp only [div_eq_mul_inv] at *; linarith
  have htop : |Dbd phi L e k j o.1 * Rp L e (k+1) o| ≤ 1 / c := by
    rw [abs_mul]
    exact (mul_le_mul hD ht (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hbase : |(if j = 1 then Edom phi L e k j o.1 * Iact phi L e k j o.1 *
      Rp L e k o else 0)| ≤ 1 / c := by
    split_ifs
    · rw [abs_mul]
      exact (mul_le_mul hE hb (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    · simp only [abs_zero]; positivity
  unfold binaryRegularRegressionCorrection
  exact (abs_sub _ _).trans (by
    have hh := abs_sub (Dbd phi L e k j o.1 * (RP L e (k+1) o - RP L e k o))
      (Dbd phi L e k j o.1 * Rp L e (k+1) o)
    simp only [div_eq_mul_inv] at *
    linarith)

-- @node: fitted_weighted_regular_regression_correction_memLp
/-- If [the policy is a policy map](hyp:hphi), [the fitted binary nuisance
specification is admissible](hyp:he), [the outcome is binary almost
surely](hyp:hy), [c is positive](hyp:hc), [every fitted positive-level instrument
probability is at least c almost everywhere](hyp:hclip), and [k is below the
highest level](hyp:hk), then [the fitted regular regression correction multiplied
by its fitted gamma weight is square integrable under the observation law](goal). -/
lemma fitted_weighted_regular_regression_correction_memLp
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e)
    (hy : OutcomeBinaryAE M) (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (k j : ℕ) (hk : k < L.K) :
    MemLp (fun o : Obs X Z => regularValue e.gamma k j o.1 *
      binaryRegularRegressionCorrection phi L e k j o) 2 (observationLaw M) := by
  have hg := (fitted_regular_gamma_memLp M L e he k j).comp_measurePreserving
    (observationLaw_fst_measurePreserving M)
  have hr := fitted_regular_regression_correction_memLp M phi hphi L e he hy c hc hclip k j hk
  apply hr.norm.mono' (by first | fun_prop | exact hg.1.mul hr.1)
  filter_upwards [observationLaw_covariate_ae M _
    (fitted_regular_gamma_abs_bound M L e he k j)] with o ho
  rw [norm_mul, Real.norm_eq_abs (regularValue e.gamma k j o.1)]
  exact mul_le_of_le_one_left (norm_nonneg _) ho

-- The weight's energy comes from its original nuisance rate, and the correction's
-- energy from the proved branch and IPW residual convergence.
-- @node: nuisanceRates_weighted_regular_regression_correction_sq_tendsto_probability_zero
/-- Suppose [the policy is a policy map](hyp:hphi), [dphi is its
derivative](hyp:hd), [the derivative is bounded and Lipschitz on the unit
interval](hyp:hDerivative), [the reference nuisance specification is
admissible](hyp:he0), [every fitted specification is admissible](hyp:heh), and
[the outcome is binary almost surely](hyp:hy). If [c is positive](hyp:hc),
[reference and fitted positive-level instrument probabilities are at least c
almost everywhere](hyp:hclip), the fitted [propensities](hyp:hrp), [level
treatment probabilities](hyp:hrlev), [binary outcome regressions](hyp:hrP),
[level instrument probabilities](hyp:hrpi), [shares at every regular
index](hyp:hrs), and [gamma weights](hyp:hrg) satisfy the finite nuisance rate
conditions, [k is below the highest level](hyp:hk), [j is a valid positive
boundary at k](hyp:hj), [sep is positive](hyp:hsep), and [the reference adjacent
pooled policy values and the distances of the residual treatment mass from both
values are at least sep almost everywhere](hyp:hgap), then [the observation-law
integrated squared difference between fitted and reference gamma-weighted regular
regression corrections, using fits at sample size twice n plus two, converges to
zero in probability](goal). -/
lemma nuisanceRates_weighted_regular_regression_correction_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hy : OutcomeBinaryAE M) (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrs : ∀ a : RegularIndex L,
      FiniteNuisanceRates M μ (fun n t => (eh n t).share a) (e0.share a))
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gamma) e0.gamma)
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (sep : ℝ) (hsep : 0 < sep)
    (hgap : ∀ᵐ x ∂xLaw M,
      sep ≤ pooledQBin phi L e0 k j x - pooledQBin phi L e0 k (j-1) x ∧
      sep ≤ |positiveValue e0.pLev (k+1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k (j-1) x| ∧
      sep ≤ |positiveValue e0.pLev (k+1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k j x|) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        (regularValue (eh (2*(n+1)) a).gamma k j o.1 *
            binaryRegularRegressionCorrection phi L (eh (2*(n+1)) a) k j o -
          regularValue e0.gamma k j o.1 *
            binaryRegularRegressionCorrection phi L e0 k j o)^2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  let r : RegularIndex L := ⟨(k,j), hk.le, hj⟩
  have hg (e : NuisanceBin L) : regularValue e.gamma k j = e.gamma r := by
    funext x
    simp only [regularValue, dif_pos r.property, r]
  have hmp := observationLaw_fst_measurePreserving M
  have hw (e : NuisanceBin L) (he : BinAdmissible M L e) :=
    (fitted_regular_gamma_memLp M L e he k j).comp_measurePreserving hmp
  have hR (e : NuisanceBin L) (he : BinAdmissible M L e)
      (hpi : ∀ i, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) :=
    fitted_regular_regression_correction_memLp M phi hphi L e he hy c hc hpi k j hk
  have hRm : AEStronglyMeasurable (binaryRegularRegressionCorrection phi L e0 k j)
      (observationLaw M) := by
    first | fun_prop | skip
    obtain ⟨hI, hD, hE⟩ := fitted_fractional_branches_memLp M phi hphi L e0 he0 k j
    have hi := (hI.comp_measurePreserving hmp).1
    have hd := (hD.comp_measurePreserving hmp).1
    have he := (hE.comp_measurePreserving hmp).1
    have hp := (fitted_RP_measurable M L e0 he0 (k+1)).aestronglyMeasurable (μ := observationLaw M)
    have hm := (fitted_RP_measurable M L e0 he0 k).aestronglyMeasurable (μ := observationLaw M)
    have ht := (fitted_Rp_measurable M L e0 he0 (k+1)).aestronglyMeasurable (μ := observationLaw M)
    have hb := (fitted_Rp_measurable M L e0 he0 k).aestronglyMeasurable (μ := observationLaw M)
    unfold binaryRegularRegressionCorrection
    by_cases hj : j = 1
    · simp only [if_pos hj]
      exact ((hd.mul (hp.sub hm)).sub (hd.mul ht)).sub ((he.mul hi).mul hb)
    · simp only [if_neg hj, sub_zero]
      exact (hd.mul (hp.sub hm)).sub (hd.mul ht)
  apply dml_ae_weighted_residual_sq_tendsto_probability_zero μ (observationLaw M)
    (fun o => regularValue e0.gamma k j o.1) (binaryRegularRegressionCorrection phi L e0 k j)
    (fun n a o => regularValue (eh (2*(n+1)) a).gamma k j o.1)
    (fun n a => binaryRegularRegressionCorrection phi L (eh (2*(n+1)) a) k j) 1 (4/c)
    (hw e0 he0).1
    hRm
    (fun n a => (hw _ (heh _ a)).1)
    (fun n a => (hR _ (heh _ a) (fun i => (hclip _ a i).mono (fun _ hx => hx.2))).1)
  · exact fun n a => (hw _ (heh _ a)).sub (hw e0 he0)
  · intro n a
    exact (hR _ (heh _ a) (fun i => (hclip _ a i).mono (fun _ hx => hx.2))).sub
      (hR e0 he0 (fun i => (hclip (2*(n+1)) a i).mono (fun _ hx => hx.1)))
  · exact fun n a => observationLaw_covariate_ae M _
      (fitted_regular_gamma_abs_bound M L _ (heh _ a) k j)
  · exact fun n a => fitted_regular_regression_correction_abs_bound M phi L e0 he0 hy c hc
      (fun i => (hclip n a i).mono (fun _ hx => hx.1)) k j hk
  · simpa only [hg] using nuisanceRates_covariate_sq_tendsto_probability_zero M μ e0.gamma
      (fun n a => (eh n a).gamma) (fun i => (he0.2.2.2.2.2.1 i).2)
      (fun n a i => ((heh n a).2.2.2.2.2.1 i).2) hrg r
  · exact nuisanceRates_regular_regression_correction_sq_tendsto_probability_zero M μ
      phi dphi hphi hd hDerivative L e0 eh he0 heh hy c hc hclip
      hrp hrlev hrP hrpi hrs k j hk sep hsep hgap

-- Assemble the actual weighted regression block over its finitely many levels
-- and boundaries, using only the component-rate result above.
-- @node: nuisanceRates_weighted_regular_regression_block_sq_tendsto_probability_zero
/-- Suppose [the policy is a policy map](hyp:hphi), [dphi is its
derivative](hyp:hd), [the derivative is bounded and Lipschitz on the unit
interval](hyp:hDerivative), [the reference nuisance specification is
admissible](hyp:he0), [every fitted specification is admissible](hyp:heh), and
[the outcome is binary almost surely](hyp:hy). If [c is positive](hyp:hc),
[reference and fitted positive-level instrument probabilities are at least c
almost everywhere](hyp:hclip), the fitted [propensities](hyp:hrp), [level
treatment probabilities](hyp:hrlev), [binary outcome regressions](hyp:hrP),
[level instrument probabilities](hyp:hrpi), [shares at every regular
index](hyp:hrs), and [gamma weights](hyp:hrg) satisfy the finite nuisance rate
conditions, [sep is positive](hyp:hsep), and [at every regular boundary below the
highest level the reference adjacent pooled values and the distances of the
residual treatment mass from both values are at least sep almost
everywhere](hyp:hgap), then [the integrated squared difference between the fitted
and reference sums of gamma-weighted regular regression corrections over all
these levels and boundaries, using fits at sample size twice n plus two,
converges to zero in probability](goal). -/
lemma nuisanceRates_weighted_regular_regression_block_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hy : OutcomeBinaryAE M) (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M,
      c ≤ e0.piLev i x ∧ c ≤ (eh n a).piLev i x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) e0.piLev)
    (hrs : ∀ a : RegularIndex L,
      FiniteNuisanceRates M μ (fun n t => (eh n t).share a) (e0.share a))
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gamma) e0.gamma)
    (sep : ℝ) (hsep : 0 < sep)
    (hgap : ∀ k, k < L.K → ∀ j, 1 ≤ j ∧ j ≤ L.l k → ∀ᵐ x ∂xLaw M,
      sep ≤ pooledQBin phi L e0 k j x - pooledQBin phi L e0 k (j-1) x ∧
      sep ≤ |positiveValue e0.pLev (k+1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k (j-1) x| ∧
      sep ≤ |positiveValue e0.pLev (k+1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k j x|) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        ((∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.range (L.l k),
            regularValue (eh (2*(n+1)) a).gamma k (j+1) o.1 *
              binaryRegularRegressionCorrection phi L (eh (2*(n+1)) a) k (j+1) o) -
          ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.range (L.l k),
            regularValue e0.gamma k (j+1) o.1 *
              binaryRegularRegressionCorrection phi L e0 k (j+1) o)^2 ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  let F := fun (k j n : ℕ) (a : A) (o : Obs X Z) =>
    regularValue (eh (2*(n+1)) a).gamma k (j+1) o.1 *
        binaryRegularRegressionCorrection phi L (eh (2*(n+1)) a) k (j+1) o -
      regularValue e0.gamma k (j+1) o.1 *
        binaryRegularRegressionCorrection phi L e0 k (j+1) o
  have hF (k j n : ℕ) (a : A) (hk : k < L.K) :
      MemLp (F k j n a) 2 (observationLaw M) :=
    (fitted_weighted_regular_regression_correction_memLp M phi hphi L _ (heh _ a) hy c hc
      (fun i => (hclip _ a i).mono (fun _ hx => hx.2)) k (j+1) hk).sub
      (fitted_weighted_regular_regression_correction_memLp M phi hphi L e0 he0 hy c hc
        (fun i => (hclip (2*(n+1)) a i).mono (fun _ hx => hx.1)) k (j+1) hk)
  have hsum := dml_finset_sum_sq_tendsto_probability_zero μ (observationLaw M)
    (Finset.range L.K) (fun k n a o => ∑ j ∈ Finset.range (L.l k), F k j n a o)
    (fun k hk n a => memLp_finsetSum _
      (fun j _ => hF k j n a (Finset.mem_range.mp hk))) (by
      intro k hk
      apply dml_finset_sum_sq_tendsto_probability_zero μ (observationLaw M)
        (Finset.range (L.l k)) (F k)
        (fun j _ n a => hF k j n a (Finset.mem_range.mp hk))
      intro j hj
      have hj' : 1 ≤ j+1 ∧ j+1 ≤ L.l k := by
        have := Finset.mem_range.mp hj
        omega
      exact nuisanceRates_weighted_regular_regression_correction_sq_tendsto_probability_zero
        M μ phi dphi hphi hd hDerivative L e0 eh he0 heh hy c hc hclip
        hrp hrlev hrP hrpi hrs hrg k (j+1) (Finset.mem_range.mp hk) hj' sep hsep
        (hgap k (Finset.mem_range.mp hk) (j+1) hj'))
  simpa only [F, Finset.sum_sub_distrib] using hsum

end Papers.TbsPrteOptimalTransport
