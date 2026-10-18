module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLCountableScoreLabels
public import Papers.TbsPrteOptimalTransport.Helpers.DMLFiniteLabelVariance
/-! Measurability of the feasible continuous score selected by recovered finite labels.
This supplies the evaluation-row measurability needed for oracle CLT transfer. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open scoped Classical Topology
universe u v w
variable {Ω : Type u} {X Z : Type v} {B : Type w}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace B]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
  [Fintype Z] [DecidableEq Z]

-- @node: measurable_zero_level_continuous_tail
/-- If [the policy is a valid policy map](hyp:hphi), [its derivative is the specified derivative](hyp:hd),
[there are no positive levels](hyp:hK), [every fitted nuisance coordinate is jointly measurable in the fit and covariates](hyp:hm),
and [fitted propensities lie between zero and one](hyp:hr), then
[the terminal score is jointly measurable in the fit and observation](goal). -/
@[fun_prop] lemma measurable_zero_level_continuous_tail
    (M : LatentIVModel Ω X Z) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hd : PolicyDifferentiable phi dphi)
    (L : LevelData Z X) (hK : L.K = 0) (e : B → NuisanceCont L)
    (hm : ∀ c, Measurable (fun bx : B × X => contComponent M L (e bx.1) c bx.2))
    (hr : ∀ b z x, (e b).prop z x ∈ Icc (0 : ℝ) 1) :
    Measurable (fun bo : B × Obs X Z => commonTailScore M phi dphi L
      (e bo.1).prop (e bo.1).pLev (e bo.1).piLev (e bo.1).gammaTail bo.2) := by
  have hp : Measurable (fun bzx : B × Z × X => (e bzx.1).prop bzx.2.1 bzx.2.2) := by
    have hh : Measurable (fun zbx : Z × B × X => (e zbx.2.1).prop zbx.1 zbx.2.2) :=
      measurable_from_prod_countable_right (fun z => hm (0, 0, 0, z))
    exact hh.comp (measurable_snd.fst.prodMk (measurable_fst.prodMk measurable_snd.snd))
  have hq := measurable_fitted_policy_graph phi hphi (fun b => (e b).prop) hp hr
  have hdq := measurable_fitted_policy_derivative_graph phi dphi hphi hd
    (fun b => (e b).prop) hp hr
  have hpo : Measurable (fun bo : B × Obs X Z => (e bo.1).prop bo.2.2.1 bo.2.1) :=
    hp.comp (measurable_fst.prodMk (measurable_snd.snd.fst.prodMk measurable_snd.fst))
  have hqo : Measurable (fun bo : B × Obs X Z =>
      phi bo.2.2.1 bo.2.1 ((e bo.1).prop bo.2.2.1 bo.2.1)) :=
    hq.comp (measurable_fst.prodMk (measurable_snd.snd.fst.prodMk measurable_snd.fst))
  have hdqo : Measurable (fun bo : B × Obs X Z =>
      dphi bo.2.2.1 bo.2.1 ((e bo.1).prop bo.2.2.1 bo.2.1)) :=
    hdq.comp (measurable_fst.prodMk (measurable_snd.snd.fst.prodMk measurable_snd.fst))
  have hind : Measurable (fun bo : B × Obs X Z => indicator (bo.2.2.1 ∈ policyUnion L 0 1)) := by
    unfold indicator
    apply Measurable.ite _ measurable_const measurable_const
    exact (Finset.measurableSet _).preimage measurable_snd.snd.fst
  simp only [commonTailScore, hK, positiveValue, show ¬ (1 ≤ (0 : ℕ) ∧ 0 ≤ 0) by omega,
    ↓reduceDIte, ↓reduceIte, sub_zero]
  exact (((measurable_const.mul hind).mul hqo).add
    (((measurable_const.mul hind).mul hdqo).mul
      (measurable_snd.snd.snd.fst.sub hpo)))

-- @node: measurable_continuous_score_random_labels
/-- For [continuous-outcome nuisance records on the random level structures](hyp:e), if [the policy is valid](hyp:hphi) and [has the specified derivative](hyp:hd),
[the recovered score labels are measurable](hyp:hlabels), [all fitted nuisance coordinates are jointly measurable](hyp:hm),
and [fitted propensities lie between zero and one](hyp:hr), then
[the score selected by the random level structure is jointly measurable in the fit and observation, using the terminal score when there are no positive levels](goal). -/
@[fun_prop] lemma measurable_continuous_score_random_labels
    (M : LatentIVModel Ω X Z) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hd : PolicyDifferentiable phi dphi)
    (L : B → LevelData Z X) (e : ∀ b, NuisanceCont (L b))
    (hlabels : Measurable (fun b => scoreRecoveryLabels (L b)))
    (hm : ∀ c, Measurable (fun bx : B × X => contComponent M (L bx.1) (e bx.1) c bx.2))
    (hr : ∀ b z x, (e b).prop z x ∈ Icc (0 : ℝ) 1) :
    Measurable (fun bo : B × Obs X Z =>
      if h : LevelCountPos (L bo.1).K then
        psiCont M phi dphi (L bo.1) h bo.2 (e bo.1)
      else commonTailScore M phi dphi (L bo.1)
        (e bo.1).prop (e bo.1).pLev (e bo.1).piLev (e bo.1).gammaTail bo.2) := by
  let F := fun b => contComponent M (L b) (e b)
  let g := fun H : LevelData Z X => fun bo : B × Obs X Z =>
    if h : LevelCountPos H.K then
      psiCont M phi dphi H h bo.2 (decodeContComponents H (F bo.1))
    else commonTailScore M phi dphi H
      (decodeContComponents H (F bo.1)).prop (decodeContComponents H (F bo.1)).pLev
      (decodeContComponents H (F bo.1)).piLev (decodeContComponents H (F bo.1)).gammaTail bo.2
  apply measurable_scoreLabel_selection (fun bo : B × Obs X Z => L bo.1) _
    (fun H => ((hlabels.comp measurable_fst).eq_const _).setOf) g
  · intro H
    by_cases hk : LevelCountPos H.K
    · simp only [g, dif_pos hk]
      exact measurable_decoded_continuous_score M phi dphi hphi hd H hk F hm hr
    · simp only [g, dif_neg hk]
      exact measurable_zero_level_continuous_tail M phi dphi hphi hd H
        (by unfold LevelCountPos at hk; omega)
        (fun b => decodeContComponents H (F b))
        (decodeContComponents_measurable M H F hm) hr
  · intro bo H heq
    have hK := (scoreRecoveryLabels_eq_iff _ _).mp heq |>.1
    by_cases hk : LevelCountPos H.K
    · have hk' : LevelCountPos (L bo.1).K := hK.symm ▸ hk
      simp only [dif_pos hk', g, dif_pos hk]
      rw [← psiCont_decodeContComponents_contComponent M phi dphi (L bo.1)
        hk' bo.2 (e bo.1)]
      exact psiCont_decode_eq_of_scoreLabels_eq M phi dphi (L bo.1) H
        heq hk' hk (F bo.1) bo.2
    · have hk' : ¬ LevelCountPos (L bo.1).K := by simpa only [hK] using hk
      have hzero : H.K = 0 := by unfold LevelCountPos at hk; omega
      have hzero' : (L bo.1).K = 0 := hK.trans hzero
      have hu := policyUnion_eq_of_scoreLabels_eq (L bo.1) H heq 0 1 (by omega)
      simp only [dif_neg hk', g, dif_neg hk, commonTailScore, hzero, hzero',
        positiveValue, show ¬ (1 ≤ (0 : ℕ) ∧ 0 ≤ 0) by omega, ↓reduceDIte,
        ↓reduceIte, sub_zero, hu]
      rfl

-- @node: dynamicContFit_measurable_fittedContScore
/-- For [a valid policy](hyp:hphi) [with the specified derivative](hyp:hd),
if [the continuous-outcome nuisance estimates on recovered levels](hyp:eHat)
[satisfy the dynamic fitting conditions](hyp:hfit)
and [the sample size is at least two](hyp:hn) and [even](hyp:heven), then
[the fitted continuous score is jointly measurable in the sample realization and observation](goal). -/
@[fun_prop] lemma dynamicContFit_measurable_fittedContScore
    (M : LatentIVModel Ω X Z) {μ : Measure B} [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit B)
    (pHat : ℕ → B → Z → X → ℝ) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hd : PolicyDifferentiable phi dphi)
    (rho : ℕ → ℝ) (gap cpi : ℝ)
    (eHat : ∀ n b, NuisanceCont (recoveredData M S I₁ I₂ pHat phi rho gap n b))
    (hfit : DynamicContFit M S I₁ I₂ pHat phi rho gap eHat cpi)
    (n : ℕ) (hn : 2 ≤ n) (heven : Even n) :
    Measurable (fun bo : B × Obs X Z =>
      fittedContScore M S I₁ I₂ pHat phi dphi rho gap eHat n bo.1 bo.2) := by
  rcases hfit with ⟨hSplit, hthreshold, hscope, hcoord, haux, hjoint⟩
  obtain ⟨htrain, hrange, hprop, hclip, hnu⟩ := hscope
  have hlabels := equalHalfSplit_measurable_recoveredData_labels M S I₁ I₂ hSplit
    pHat htrain hrange phi hphi rho gap n hn heven
  have hs := measurable_scoreRecoveryLabels_of_measurable_recoveryLabels _ hlabels
  have hc (c) := (measurable_pi_apply c).comp (hjoint n)
  apply measurable_continuous_score_random_labels M phi dphi hphi hd _ _ hs hc
  intro b z x
  rw [hprop n b]
  exact hrange n b z x

-- @node: dynamicContFit_aemeasurable_fittedContScore_evaluation
/-- If [the policy is valid](hyp:hphi), [its derivative is the specified derivative](hyp:hd),
and [the continuous-outcome nuisance estimates on recovered levels](hyp:eHat)
[satisfy the dynamic fitting conditions](hyp:hfit), then
[the fitted score at any indexed observation in the evaluation half is almost everywhere measurable under the sampling law](goal). -/
@[fun_prop] lemma dynamicContFit_aemeasurable_fittedContScore_evaluation
    (M : LatentIVModel Ω X Z) {μ : Measure B} [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit B)
    (pHat : ℕ → B → Z → X → ℝ) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hd : PolicyDifferentiable phi dphi)
    (rho : ℕ → ℝ) (gap cpi : ℝ)
    (eHat : ∀ n b, NuisanceCont (recoveredData M S I₁ I₂ pHat phi rho gap n b))
    (hfit : DynamicContFit M S I₁ I₂ pHat phi rho gap eHat cpi)
    (n : ℕ) (i : Fin (n + 1)) :
    AEMeasurable (fun b => fittedContScore M S I₁ I₂ pHat phi dphi rho gap eHat
      (2 * (n + 1)) b (S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) b) i) b)) μ := by
  have hm := dynamicContFit_measurable_fittedContScore M S I₁ I₂ pHat phi dphi hphi hd
    rho gap cpi eHat hfit (2 * (n + 1)) (by omega) (even_two_mul _)
  have hl := equalHalfSplit_evaluationIndex_laws M μ S I₁ I₂ hfit.1 n
  exact (hm.comp (measurable_id.prodMk (hl.2.2.1 i))).aemeasurable

-- @node: equalHalfSplit_varianceRV_aemeasurable_of_evaluation_rows
/-- Under [an equal split into training and evaluation halves](hyp:hSplit), if
[each indexed evaluation score is almost everywhere measurable](hyp:hrow), then
[the empirical score variance is almost everywhere measurable at every even sample size of at least two](goal). -/
@[fun_prop] lemma equalHalfSplit_varianceRV_aemeasurable_of_evaluation_rows
    (M : LatentIVModel Ω X Z) (μ : Measure B) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit B)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (score : ℕ → B → Obs X Z → ℝ)
    (hrow : ∀ n i, AEMeasurable (fun b => score (2 * (n + 1)) b
      (S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) b) i) b)) μ) :
    ∀ n, AEMeasurable (fun b => varianceRV M S I₂ score (2 * (n + 1)) b) μ := by
  intro n
  have hmean := equalHalfSplit_dmlRV_aemeasurable_of_evaluation_rows M μ S I₁ I₂
    hSplit score hrow n
  have hsq : AEMeasurable (fun b => ((n + 1 : ℕ) : ℝ)⁻¹ *
      ∑ i : Fin (n + 1), (score (2 * (n + 1)) b
        (S.Z (dmlEvaluationIndex n (I₂ (2 * (n + 1)) b) i) b)) ^ 2) μ := by
    simpa only [Finset.sum_apply] using
      (Finset.aemeasurable_sum Finset.univ (fun i _ => (hrow n i).pow_const 2)).const_mul
        (((n + 1 : ℕ) : ℝ)⁻¹)
  apply (hsq.sub (hmean.pow_const 2)).congr
  filter_upwards [(equalHalfSplit_evaluationIndex_laws M μ S I₁ I₂ hSplit n).1,
    (hSplit (2 * (n + 1)) (by omega) ⟨n + 1, by omega⟩).1] with b he hb
  have hc : (I₂ (2 * (n + 1)) b).card = n + 1 := by simpa using hb.2.2.2
  have hne : (I₂ (2 * (n + 1)) b).Nonempty := by
    apply Finset.card_pos.mp
    rw [hc]
    omega
  rw [varianceRV_oracle_second_moment_identity M S I₂ score _ b hne 0]
  simp only [hc, sub_zero, Pi.sub_apply]
  congr 1
  congr 1
  calc
    _ = ∑ i ∈ Finset.univ.image (dmlEvaluationIndex n (I₂ (2 * (n + 1)) b)),
        (score (2 * (n + 1)) b (S.Z i b)) ^ 2 :=
      (Finset.sum_image (fun i hi j hj hij => he.1 hij)).symm
    _ = _ := by rw [he.2]

-- @node: dynamicContFit_aemeasurable_dmlRV
/-- If [the policy is valid](hyp:hphi), [its derivative is the specified derivative](hyp:hd),
and [the continuous-outcome nuisance estimates on recovered levels](hyp:eHat)
[satisfy the dynamic fitting conditions](hyp:hfit), then
[the evaluation-half average of the fitted continuous score is almost everywhere measurable at sample size twice the evaluation-half size](goal). -/
@[fun_prop] lemma dynamicContFit_aemeasurable_dmlRV
    (M : LatentIVModel Ω X Z) {μ : Measure B} [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit B)
    (pHat : ℕ → B → Z → X → ℝ) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hd : PolicyDifferentiable phi dphi)
    (rho : ℕ → ℝ) (gap cpi : ℝ)
    (eHat : ∀ n b, NuisanceCont (recoveredData M S I₁ I₂ pHat phi rho gap n b))
    (hfit : DynamicContFit M S I₁ I₂ pHat phi rho gap eHat cpi) (n : ℕ) :
    AEMeasurable (fun b => dmlRV M S I₂
      (fittedContScore M S I₁ I₂ pHat phi dphi rho gap eHat) (2 * (n + 1)) b) μ := by
  exact equalHalfSplit_dmlRV_aemeasurable_of_evaluation_rows M μ S I₁ I₂ hfit.1 _
    (dynamicContFit_aemeasurable_fittedContScore_evaluation M S I₁ I₂ pHat phi dphi
      hphi hd rho gap cpi eHat hfit) n

-- @node: dynamicContFit_aemeasurable_varianceRV
/-- If [the policy is valid](hyp:hphi), [its derivative is the specified derivative](hyp:hd),
and [the continuous-outcome nuisance estimates on recovered levels](hyp:eHat)
[satisfy the dynamic fitting conditions](hyp:hfit), then
[the evaluation-half empirical variance of the fitted continuous score is almost everywhere measurable at sample size twice the evaluation-half size](goal). -/
@[fun_prop] lemma dynamicContFit_aemeasurable_varianceRV
    (M : LatentIVModel Ω X Z) {μ : Measure B} [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit B)
    (pHat : ℕ → B → Z → X → ℝ) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hd : PolicyDifferentiable phi dphi)
    (rho : ℕ → ℝ) (gap cpi : ℝ)
    (eHat : ∀ n b, NuisanceCont (recoveredData M S I₁ I₂ pHat phi rho gap n b))
    (hfit : DynamicContFit M S I₁ I₂ pHat phi rho gap eHat cpi) (n : ℕ) :
    AEMeasurable (fun b => varianceRV M S I₂
      (fittedContScore M S I₁ I₂ pHat phi dphi rho gap eHat) (2 * (n + 1)) b) μ := by
  exact equalHalfSplit_varianceRV_aemeasurable_of_evaluation_rows M μ S I₁ I₂ hfit.1 _
    (dynamicContFit_aemeasurable_fittedContScore_evaluation M S I₁ I₂ pHat phi dphi
      hphi hd rho gap cpi eHat hfit) n

end Papers.TbsPrteOptimalTransport
