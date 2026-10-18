module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLFittedTail
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRemainderRates
public import Papers.TbsPrteOptimalTransport.Helpers.DMLFullBlockRates
/-! Quadratic bias and root-n negligibility of the fitted terminal score. -/
public section
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- Uniform component errors assemble the Taylor and denominator cross-errors
-- of the actual score, retaining its fitted residual correction.
-- @node: fitted_tail_quadratic_bias_bound
/-- Under [a threshold-crossing representation](hyp:h), suppose [the policy map is
valid](hyp:hphi), [its specified derivative is correct](hyp:hd), [the derivative is
bounded and Lipschitz](hyp:hDerivative), [the chosen Lipschitz constant is nonnegative](hyp:hLip),
and [it bounds derivative differences on the unit interval](hyp:hlip). Assume [there
is at least one positive level](hyp:hK), [baseline and policy level orders agree](hyp:hOrder),
[the fitted nuisances are admissible](hyp:he), [the population nuisances are admissible](hyp:he0),
[baseline overlap holds](hyp:hov), [the clipping floor is positive](hyp:hc), [the
regression-error envelope is nonnegative](hyp:hreg), [the weight-error envelope is
nonnegative](hyp:_hwt), and [the fitted terminal selection probability is at least
the floor almost everywhere](hyp:hclip). If [propensity errors on the terminal policy
union have second-moment norms bounded by the regression envelope](hyp:hp), [the
terminal level error has the same bound](hyp:hlev), [the terminal selection-probability
error norm is bounded by the weight envelope](hyp:hpi), and [the terminal coefficient
error norm has the same weight bound](hyp:hg), then [the absolute difference between
fitted and population terminal score means is at most the absolute lower outcome
endpoint times the sum of the Lipschitz constant times the terminal union's cardinality
times the squared regression envelope and twice the product of the two envelopes
divided by the clipping floor](goal). -/
lemma fitted_tail_quadratic_bias_bound (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (Lip : ℝ) (hLip : 0 ≤ Lip)
    (hlip : ∀ z x a b, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 →
      |dphi z x a - dphi z x b| ≤ Lip * |a - b|)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (e : NuisanceBin L) (he : BinAdmissible M L e)
    (he0 : BinAdmissible M L (eta0Bin M L))
    (cpi c reg wt : ℝ) (hov : BaselineOverlapWitness M L cpi) (hc : 0 < c)
    (hreg : 0 ≤ reg) (_hwt : 0 ≤ wt)
    (hclip : ∀ᵐ x ∂xLaw M, c ≤ positiveValue e.piLev L.K x)
    (hp : ∀ z ∈ policyUnion L L.K 1,
      (eLpNorm (fun x => e.prop z x - M.prop z x) 2 (xLaw M)).toReal ≤ reg)
    (hlev : (eLpNorm (fun x => positiveValue e.pLev L.K x - L.pLev L.K x)
      2 (xLaw M)).toReal ≤ reg)
    (hpi : (eLpNorm (fun x => positiveValue e.piLev L.K x -
      (levelSetProb M L).1 L.K x) 2 (xLaw M)).toReal ≤ wt)
    (hg : (eLpNorm (fun x => e.gammaTail x - gammaTail M L x)
      2 (xLaw M)).toReal ≤ wt) :
    |(∫ o, commonTailScore M phi dphi L e.prop e.pLev e.piLev e.gammaTail o
        ∂observationLaw M) -
      (∫ o, commonTailScore M phi dphi L (eta0Bin M L).prop (eta0Bin M L).pLev
        (eta0Bin M L).piLev (eta0Bin M L).gammaTail o ∂observationLaw M)| ≤
      |M.yMin| * (Lip * ((policyUnion L L.K 1).card : ℝ) * reg ^ 2 +
        (2 / c) * (reg * wt)) := by
  have hb := fitted_tail_bias_L2_bound M h phi dphi hphi hd hDerivative Lip hLip hlip
    L hK hOrder e he he0 cpi c hov hc hclip
  dsimp only at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply add_le_add
  · calc
      _ ≤ Lip * (∑ _z ∈ policyUnion L L.K 1, reg ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hLip
        apply Finset.sum_le_sum
        intro z hz
        exact pow_le_pow_left₀ ENNReal.toReal_nonneg (hp z hz) 2
      _ = _ := by simp; ring
  · calc
      _ ≤ reg * (wt + wt) / c := by
        gcongr
      _ = _ := by ring

-- Both regression and weight errors have the paper's quarter-power rate.
-- The score-mean rate is derived from the expansion above.
-- @node: fitted_tail_root_n_bias_negligible
/-- Under [a threshold-crossing representation](hyp:h), suppose [the policy map is
valid](hyp:hphi), [its specified derivative is correct](hyp:hd), [the derivative is
bounded and Lipschitz](hyp:hDerivative), [the chosen Lipschitz constant is nonnegative](hyp:hLip),
[it bounds derivative differences on the unit interval](hyp:hlip), [there is at least
one positive level](hyp:hK), and [baseline and policy level orders agree](hyp:hOrder).
Assume [all fitted nuisances are admissible](hyp:he), [the population nuisances are
admissible](hyp:he0), [baseline overlap holds](hyp:hov), [the clipping floor is positive](hyp:hc),
[regression envelopes are nonnegative](hyp:hreg), [weight envelopes are nonnegative](hyp:hwt),
and [fitted terminal selection probabilities are at least the floor almost everywhere](hyp:hclip).
If [the propensity error norms on the terminal policy union are bounded by the
regression envelopes](hyp:hp), [terminal level error norms obey the same bounds](hyp:hlev),
[terminal selection-probability error norms are bounded by the weight envelopes](hyp:hpi),
[terminal coefficient error norms obey the same weight bounds](hyp:hg), and [both
envelopes are of smaller order in probability than the inverse fourth root of twice
the evaluation size](hyp:hr,hw), then [the difference between fitted and population
terminal score means, multiplied by the square root of the evaluation size, converges
to zero in probability](goal). -/
lemma fitted_tail_root_n_bias_negligible {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (Lip : ℝ) (hLip : 0 ≤ Lip)
    (hlip : ∀ z x a b, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 →
      |dphi z x a - dphi z x b| ≤ Lip * |a - b|)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (eh : ℕ → A → NuisanceBin L) (he : ∀ n a, BinAdmissible M L (eh n a))
    (he0 : BinAdmissible M L (eta0Bin M L))
    (cpi c : ℝ) (reg wt : ℕ → A → ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hc : 0 < c)
    (hreg : ∀ n a, 0 ≤ reg n a) (hwt : ∀ n a, 0 ≤ wt n a)
    (hclip : ∀ n a, ∀ᵐ x ∂xLaw M, c ≤ positiveValue (eh n a).piLev L.K x)
    (hp : ∀ n a z, z ∈ policyUnion L L.K 1 →
      (eLpNorm (fun x => (eh n a).prop z x - M.prop z x) 2 (xLaw M)).toReal ≤ reg n a)
    (hlev : ∀ n a, (eLpNorm (fun x => positiveValue (eh n a).pLev L.K x - L.pLev L.K x)
      2 (xLaw M)).toReal ≤ reg n a)
    (hpi : ∀ n a, (eLpNorm (fun x => positiveValue (eh n a).piLev L.K x -
      (levelSetProb M L).1 L.K x) 2 (xLaw M)).toReal ≤ wt n a)
    (hg : ∀ n a, (eLpNorm (fun x => (eh n a).gammaTail x - gammaTail M L x)
      2 (xLaw M)).toReal ≤ wt n a)
    (hr : Causalean.Stat.IsLittleOp reg
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ)
    (hw : Causalean.Stat.IsLittleOp wt
      (fun n => ((2 * (n + 1) : ℕ) : ℝ) ^ (-1 / 4 : ℝ)) μ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        ((∫ o, commonTailScore M phi dphi L (eh n a).prop (eh n a).pLev
            (eh n a).piLev (eh n a).gammaTail o ∂observationLaw M) -
          (∫ o, commonTailScore M phi dphi L (eta0Bin M L).prop (eta0Bin M L).pLev
            (eta0Bin M L).piLev (eta0Bin M L).gammaTail o ∂observationLaw M)))
      atTop (fun _ _ => 0) := by
  let C := |M.yMin| * (Lip * ((policyUnion L L.K 1).card : ℝ) + 2 / c) + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  apply dml_quadratic_bias_root_n_negligible μ _ reg wt C hC hr hw
  intro n a
  have hb := fitted_tail_quadratic_bias_bound M h phi dphi hphi hd hDerivative Lip hLip hlip
    L hK hOrder (eh n a) (he n a) he0 cpi c (reg n a) (wt n a) hov hc
    (hreg n a) (hwt n a) (hclip n a) (hp n a) (hlev n a) (hpi n a) (hg n a)
  apply hb.trans
  have hn : 0 ≤ reg n a * wt n a := mul_nonneg (hreg n a) (hwt n a)
  calc
    _ ≤ |M.yMin| * ((Lip * ((policyUnion L L.K 1).card : ℝ) + 2 / c) *
        (reg n a ^ 2 + reg n a * wt n a)) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      nlinarith [mul_nonneg (by positivity : 0 ≤ 2 / c) (sq_nonneg (reg n a)),
        mul_nonneg (by positivity : 0 ≤ Lip * ((policyUnion L L.K 1).card : ℝ)) hn]
    _ = (C - 1) * (reg n a ^ 2 + reg n a * wt n a) := by dsimp only [C]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (add_nonneg (sq_nonneg _) hn)

-- Clipped propensity and terminal-weight coordinates have finite second moments.
-- @node: fitted_prop_gammaTail_memLp
/-- If [the fitted binary nuisances are admissible](hyp:he), then [every fitted
instrument-specific propensity and the fitted terminal coefficient have finite second
moments under the covariate distribution](goal). -/
lemma fitted_prop_gammaTail_memLp (L : LevelData Z X) (e : NuisanceBin L)
    (he : BinAdmissible M L e) :
    (∀ z, MemLp (e.prop z) 2 (xLaw M)) ∧ MemLp e.gammaTail 2 (xLaw M) := by
  have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  rcases he with ⟨hp, hmp, _, _, _, _, _, _, _, _, _, hg, hmg⟩
  constructor
  · intro z
    apply MemLp.of_bound (by fun_prop) 1
    filter_upwards [hp z] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
    exact hx.2
  · apply MemLp.of_bound (by fun_prop) 1
    filter_upwards [hg] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
    exact hx.2

-- Construct the finite envelopes directly from the componentwise rates.
-- No rate for the score bias is supplied as an assumption.
-- @node: nuisanceRates_tail_root_n_bias_negligible
/-- Under [a threshold-crossing representation](hyp:h), suppose [the policy map is
valid](hyp:hphi), [its specified derivative is correct](hyp:hd), [the derivative is
bounded and Lipschitz](hyp:hDerivative), [the chosen Lipschitz constant is nonnegative](hyp:hLip),
[it bounds derivative differences on the unit interval](hyp:hlip), [there is at least
one positive level](hyp:hK), and [baseline and policy level orders agree](hyp:hOrder).
If [all fitted binary nuisances are admissible](hyp:he), [the population nuisances
are admissible](hyp:he0), [baseline overlap holds](hyp:hov), [the clipping floor is
positive](hyp:hc), [all fitted terminal selection probabilities are at least that
floor almost everywhere](hyp:hclip), and [propensity, positive-level, level-selection
probability, and terminal coefficient errors satisfy the finite nuisance rate
conditions](hyp:hrp,hrlev,hrpi,hrg), then [the difference between fitted and population
terminal score means, multiplied by the square root of the evaluation size, converges
to zero in probability along training sizes twice the evaluation size](goal). -/
lemma nuisanceRates_tail_root_n_bias_negligible {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (Lip : ℝ) (hLip : 0 ≤ Lip)
    (hlip : ∀ z x a b, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 →
      |dphi z x a - dphi z x b| ≤ Lip * |a - b|)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (eh : ℕ → A → NuisanceBin L) (he : ∀ n a, BinAdmissible M L (eh n a))
    (he0 : BinAdmissible M L (eta0Bin M L))
    (cpi c : ℝ) (hov : BaselineOverlapWitness M L cpi) (hc : 0 < c)
    (hclip : ∀ n a, ∀ᵐ x ∂xLaw M, c ≤ positiveValue (eh n a).piLev L.K x)
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) (eta0Bin M L).prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) (eta0Bin M L).pLev)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) (eta0Bin M L).piLev)
    (hrg : FiniteNuisanceRates M μ (fun n a (_ : Unit) => (eh n a).gammaTail)
      (fun _ => (eta0Bin M L).gammaTail)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n + 1 : ℕ) : ℝ) *
        ((∫ o, commonTailScore M phi dphi L (eh (2*(n+1)) a).prop
            (eh (2*(n+1)) a).pLev (eh (2*(n+1)) a).piLev
            (eh (2*(n+1)) a).gammaTail o ∂observationLaw M) -
          (∫ o, commonTailScore M phi dphi L (eta0Bin M L).prop (eta0Bin M L).pLev
            (eta0Bin M L).piLev (eta0Bin M L).gammaTail o ∂observationLaw M)))
      atTop (fun _ _ => 0) := by
  let zs := (Finset.univ : Finset Z).toList
  let dp := fun n a z => finiteL2Error M ((eh (2*(n+1)) a).prop z) ((eta0Bin M L).prop z)
  let dl := fun n a => finiteL2Error M (positiveValue (eh (2*(n+1)) a).pLev L.K)
    (positiveValue (eta0Bin M L).pLev L.K)
  let dt := fun n a => finiteL2Error M (positiveValue (eh (2*(n+1)) a).piLev L.K)
    (positiveValue (eta0Bin M L).piLev L.K)
  let dg := fun n a => finiteL2Error M (eh (2*(n+1)) a).gammaTail (eta0Bin M L).gammaTail
  let reg := fun n a => maxErrors (zs.map (dp n a)) + dl n a
  let wt := fun n a => dt n a + dg n a
  have hl := nuisanceRates_positiveValue M μ L.K _ _ hrlev L.K
  have ht := nuisanceRates_positiveValue M μ L.K _ _ hrpi L.K
  have hp := nuisanceRates_finite_maxErrors M μ _ _ zs hrp
  have hr := hp.add_eventually_nonneg_rate
    (Eventually.of_forall (fun _ => Real.rpow_nonneg (by positivity) _)) hl
  have hw := ht.add_eventually_nonneg_rate
    (Eventually.of_forall (fun _ => Real.rpow_nonneg (by positivity) _)) (hrg ())
  have hi : 1 ≤ L.K ∧ L.K ≤ L.K := ⟨hK, le_rfl⟩
  have hreg : ∀ n a, 0 ≤ reg n a := fun _ _ =>
    add_nonneg (maxErrors_nonneg _) (Real.sqrt_nonneg _)
  have hwt : ∀ n a, 0 ≤ wt n a := fun _ _ =>
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  apply fitted_tail_root_n_bias_negligible M μ h phi dphi hphi hd hDerivative
    Lip hLip hlip L hK hOrder (fun n a => eh (2*(n+1)) a)
    (fun n a => he _ a) he0 cpi c reg wt hov hc hreg hwt (fun n a => hclip _ a)
  · intro n a z _hz
    change (eLpNorm (fun x => (eh (2*(n+1)) a).prop z x -
      (eta0Bin M L).prop z x) 2 (xLaw M)).toReal ≤ reg n a
    rw [← l2Error_eq_eLpNorm M _ _
      (((fitted_prop_gammaTail_memLp M L (eh (2*(n+1)) a) (he _ a)).1 z).sub
        ((fitted_prop_gammaTail_memLp M L (eta0Bin M L) he0).1 z))]
    have hb : dp n a z ≤ maxErrors (zs.map (dp n a)) := by
      apply le_maxErrors_of_mem
      exact List.mem_map.mpr ⟨z, by simp [zs], rfl⟩
    exact hb.trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  · intro n a
    have hm := ((fitted_positive_treatment_assignment_memLp M L
      (eh (2*(n+1)) a) (he _ a) L.K).1).sub
        (fitted_positive_treatment_assignment_memLp M L (eta0Bin M L) he0 L.K).1
    have hb : dl n a ≤ reg n a := le_add_of_nonneg_left (maxErrors_nonneg _)
    dsimp only [dl] at hb
    rw [l2Error_eq_eLpNorm M _ _ hm] at hb
    simpa only [eta0Bin, positiveValue, dif_pos hi] using hb
  · intro n a
    have hm := ((fitted_positive_treatment_assignment_memLp M L
      (eh (2*(n+1)) a) (he _ a) L.K).2).sub
        (fitted_positive_treatment_assignment_memLp M L (eta0Bin M L) he0 L.K).2
    have hb : dt n a ≤ wt n a := le_add_of_nonneg_right (Real.sqrt_nonneg _)
    dsimp only [dt] at hb
    rw [l2Error_eq_eLpNorm M _ _ hm] at hb
    simpa only [eta0Bin, positiveValue, dif_pos hi] using hb
  · intro n a
    have hm := (fitted_prop_gammaTail_memLp M L (eh (2*(n+1)) a) (he _ a)).2.sub
      (fitted_prop_gammaTail_memLp M L (eta0Bin M L) he0).2
    have hb : dg n a ≤ wt n a := le_add_of_nonneg_left (Real.sqrt_nonneg _)
    dsimp only [dg] at hb
    rw [l2Error_eq_eLpNorm M _ _ hm] at hb
    exact hb
  · exact hr
  · exact hw

-- At the true nuisances the fitted residual corrections vanish, leaving
-- precisely the terminal contribution to the lower-bound target.
-- @node: true_binary_tail_score_mean
/-- Under [a threshold-crossing representation](hyp:h), if [the policy map is valid](hyp:hphi),
[its specified derivative is correct](hyp:hd), [the derivative is bounded and Lipschitz](hyp:hDerivative),
[there is at least one positive level](hyp:hK), [baseline and policy level orders
agree](hyp:hOrder), [the population binary nuisances are admissible](hyp:he0), and
[baseline overlap holds](hyp:hov), then [the terminal score at the population nuisances
is integrable, and its mean equals the covariate average of the lower outcome endpoint
times the difference between the instrument-probability-weighted policy propensity
sum over the terminal policy union and the terminal level times its terminal
coefficient](goal). -/
lemma true_binary_tail_score_mean (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (he0 : BinAdmissible M L (eta0Bin M L))
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) :
    Integrable (commonTailScore M phi dphi L (eta0Bin M L).prop
      (eta0Bin M L).pLev (eta0Bin M L).piLev (eta0Bin M L).gammaTail)
      (observationLaw M) ∧
    (∫ o, commonTailScore M phi dphi L (eta0Bin M L).prop (eta0Bin M L).pLev
        (eta0Bin M L).piLev (eta0Bin M L).gammaTail o ∂observationLaw M) =
      ∫ x, M.yMin * ((∑ z ∈ policyUnion L L.K 1,
        instProb M z x * phi z x (M.prop z x)) -
        L.pLev L.K x * gammaTail M L x) ∂xLaw M := by
  have hi : 1 ≤ L.K ∧ L.K ≤ L.K := ⟨hK, le_rfl⟩
  have hclip : ∀ᵐ x ∂xLaw M, cpi ≤ positiveValue (eta0Bin M L).piLev L.K x :=
    Eventually.of_forall (fun x => by
      simpa only [positiveValue, dif_pos hi, eta0Bin] using hov.2 x L.K hK le_rfl)
  have hm := fitted_tail_population_mean M h phi dphi hphi hd hDerivative
    L hK hOrder (eta0Bin M L) he0 cpi hov.1 hclip
  refine ⟨hm.1, ?_⟩
  simpa only [eta0Bin, positiveValue, dif_pos hi, sub_self, mul_zero,
    zero_mul, add_zero] using hm.2

end Papers.TbsPrteOptimalTransport
