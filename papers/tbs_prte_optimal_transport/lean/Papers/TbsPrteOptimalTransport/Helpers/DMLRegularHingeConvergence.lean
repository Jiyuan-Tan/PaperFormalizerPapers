module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLWeightedRegularRegressionConvergence
/-! L2 convergence of the instrument-event hinge contribution to the fractional
binary product score. The product correction cancels its fitted gamma weight;
the remaining event-weighted hinge is controlled by the original nuisance rates. -/
public section
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- The fitted product's plug-in gamma cancels against the event correction.
-- @node: psiProdBin_event_hinge_split
/-- [The binary regular product score equals the hinge multiplied by the indicator
that the observed instrument belongs to the policy group union, plus fitted gamma
times the regular score component's deviation from that hinge](goal). -/
lemma psiProdBin_event_hinge_split (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e : NuisanceBin L) (k j : ℕ) (o : Obs X Z) :
    psiProdBin phi dphi L e k j o =
      indicator (o.2.1 ∈ policyUnion L k j) * hMinus phi L e k j o.1 +
        regularValue e.gamma k j o.1 *
          (binScoreComponents phi dphi L e k j o - hMinus phi L e k j o.1) := by
  unfold psiProdBin
  ring

-- @node: fitted_event_hinge_memLp
/-- For [a valid policy map](hyp:hphi) and [admissible binary nuisances](hyp:he), if
[the baseline index is below the last level](hyp:hk) and [the policy index lies
between one and its level count](hyp:hj), then [the hinge multiplied by the indicator
that the observed instrument belongs to the policy group union is square integrable
under the observation law](goal). -/
lemma fitted_event_hinge_memLp (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e)
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    MemLp (fun o : Obs X Z => indicator (o.2.1 ∈ policyUnion L k j) *
      hMinus phi L e k j o.1) 2 (observationLaw M) := by
  have hh := (binary_hMinus_memLp_of_admissible M phi hphi L e he k j hk hj).comp_measurePreserving (observationLaw_fst_measurePreserving M)
  have hi : Measurable (fun o : Obs X Z => indicator (o.2.1 ∈ policyUnion L k j)) := by
    fun_prop
  apply hh.norm.mono' (hi.aestronglyMeasurable.mul hh.1)
  apply Eventually.of_forall
  intro o
  dsimp only [Pi.mul_apply, Function.comp_apply]
  rw [norm_mul]
  have hb : ‖indicator (o.2.1 ∈ policyUnion L k j)‖ ≤ 1 := by
    unfold indicator
    split_ifs <;> norm_num
  exact mul_le_of_le_one_left (norm_nonneg _) hb

-- Measurable versions enter only the change of measure. No branch gap is
-- needed for the value of the hinge itself.
-- @node: nuisanceRates_hMinus_observation_sq_tendsto_probability_zero
/-- Suppose [the policy map is valid](hyp:hphi), [has the specified derivative](hyp:hd),
and [that derivative is bounded and Lipschitz](hyp:hDerivative), with [admissible
reference binary nuisances](hyp:he0) and [admissible fitted binary nuisances at every
sample size and realization](hyp:heh). If the finite nuisance rate conditions hold
for [the propensity](hyp:hrp), [the baseline levels](hyp:hrlev), [the treated success
probabilities](hyp:hrP), and [every regular-index share](hyp:hrs), and [the baseline
index is below the last level](hyp:hk) while [the policy index lies between one and
its level count](hyp:hj), then [the observation-law integral of the squared fitted-minus-reference
hinge difference converges in probability to zero along even sample sizes starting
at two](goal). -/
lemma nuisanceRates_hMinus_observation_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1)
    (hrs : ∀ a : RegularIndex L,
      FiniteNuisanceRates M μ (fun n t => (eh n t).share a) (e0.share a))
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        (hMinus phi L (eh (2*(n+1)) a) k j o.1 - hMinus phi L e0 k j o.1)^2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  have hr := nuisanceRates_hMinus_quarter_rate M μ phi dphi hphi hd hDerivative
    L e0 eh he0 heh hrp hrlev hrP hrs k j hk hj
  have hc : Continuous (fun t : ℝ => t^2) := by fun_prop
  have hs := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    hc.continuousAt (dml_quarter_rate_tendsto_probability_zero μ _ hr)
  simp only [finiteL2Error, Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _),
    zero_pow (by norm_num : 2 ≠ 0)] at hs
  have heq (n : ℕ) (a : A) :
      (∫ o : Obs X Z,
        (hMinus phi L (eh (2*(n+1)) a) k j o.1 - hMinus phi L e0 k j o.1)^2
        ∂observationLaw M) =
      ∫ x, (hMinus phi L (eh (2*(n+1)) a) k j x - hMinus phi L e0 k j x)^2
        ∂xLaw M := by
    have hm := ((binary_hMinus_memLp_of_admissible M phi hphi L (eh (2*(n+1)) a) (heh (2*(n+1)) a) k j hk hj).sub (binary_hMinus_memLp_of_admissible M phi hphi L e0 he0 k j hk hj)).1.pow 2
    have hmp := observationLaw_fst_measurePreserving M
    rw [← hmp.map_eq]
    exact (integral_map hmp.aemeasurable (by rw [hmp.map_eq]; exact hm)).symm
  simpa only [heq] using hs

-- The event is fixed after oracle recovery. Its indicator decreases energy.
-- @node: nuisanceRates_event_hinge_sq_tendsto_probability_zero
/-- Suppose [the policy map is valid](hyp:hphi), [has the specified derivative](hyp:hd),
and [that derivative is bounded and Lipschitz](hyp:hDerivative), with [admissible
reference binary nuisances](hyp:he0) and [admissible fitted binary nuisances at every
sample size and realization](hyp:heh). If the finite nuisance rate conditions hold
for [the propensity](hyp:hrp), [the baseline levels](hyp:hrlev), [the treated success
probabilities](hyp:hrP), and [every regular-index share](hyp:hrs), and [the baseline
index is below the last level](hyp:hk) while [the policy index lies between one and
its level count](hyp:hj), then [the observation-law integral of the squared difference
between fitted and reference hinges, each multiplied by the same policy group
union indicator, converges in probability to zero along even sample sizes starting
at two](goal). -/
lemma nuisanceRates_event_hinge_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1)
    (hrs : ∀ a : RegularIndex L,
      FiniteNuisanceRates M μ (fun n t => (eh n t).share a) (e0.share a))
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        (indicator (o.2.1 ∈ policyUnion L k j) * hMinus phi L (eh (2*(n+1)) a) k j o.1 -
          indicator (o.2.1 ∈ policyUnion L k j) * hMinus phi L e0 k j o.1)^2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  apply probability_zero_of_nonneg_le μ _ _
    (nuisanceRates_hMinus_observation_sq_tendsto_probability_zero M μ phi dphi hphi hd
      hDerivative L e0 eh he0 heh hrp hrlev hrP hrs k j hk hj)
  intro n
  apply Eventually.of_forall
  intro a
  refine ⟨integral_nonneg (fun o => sq_nonneg _), ?_⟩
  have hi := ((fitted_event_hinge_memLp M phi hphi L (eh (2*(n+1)) a) (heh (2*(n+1)) a) k j hk hj).sub
    (fitted_event_hinge_memLp M phi hphi L e0 he0 k j hk hj)).integrable_sq
  have hh := (((binary_hMinus_memLp_of_admissible M phi hphi L (eh (2*(n+1)) a) (heh (2*(n+1)) a) k j hk hj).sub
    (binary_hMinus_memLp_of_admissible M phi hphi L e0 he0 k j hk hj)).comp_measurePreserving (observationLaw_fst_measurePreserving M)).integrable_sq
  apply integral_mono hi hh
  intro o
  dsimp only [Pi.sub_apply, Function.comp_apply]
  unfold indicator
  split_ifs
  · simp only [one_mul, le_refl]
  · simp only [zero_mul, sub_self, zero_pow (by norm_num : 2 ≠ 0)]
    exact sq_nonneg _

-- The index sets are exactly the range/Icc sets in the total binary score.
-- @node: fitted_event_hinge_block_memLp
/-- For [a valid policy map](hyp:hphi) and [admissible binary nuisances](hyp:he),
[the sum of policy group union indicator-weighted hinges over all baseline indices
below the last level and all policy indices from one through their level counts
is square integrable under the observation law](goal). -/
lemma fitted_event_hinge_block_memLp
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e) :
    MemLp (fun o : Obs X Z => ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
      indicator (o.2.1 ∈ policyUnion L k j) * hMinus phi L e k j o.1)
      2 (observationLaw M) := by
  apply memLp_finsetSum
  intro k hk
  apply memLp_finsetSum
  intro j hj
  exact fitted_event_hinge_memLp M phi hphi L e he k j
    (Finset.mem_range.mp hk) (Finset.mem_Icc.mp hj)

-- Every summand's energy is obtained from component rates, then assembled
-- using the proved finite-sum energy bound.
-- @node: nuisanceRates_event_hinge_block_sq_tendsto_probability_zero
/-- Suppose [the policy map is valid](hyp:hphi), [has the specified derivative](hyp:hd),
and [that derivative is bounded and Lipschitz](hyp:hDerivative), with [admissible
reference binary nuisances](hyp:he0) and [admissible fitted binary nuisances at every
sample size and realization](hyp:heh). If the finite nuisance rate conditions hold
for [the propensity](hyp:hrp), [the baseline levels](hyp:hrlev), [the treated success
probabilities](hyp:hrP), and [every regular-index share](hyp:hrs), then [the observation-law
integral of the squared difference between the fitted and reference sums of policy
group union indicator-weighted hinges over all valid regular indices converges in
probability to zero along even sample sizes starting at two](goal). -/
lemma nuisanceRates_event_hinge_block_sq_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1)
    (hrs : ∀ a : RegularIndex L,
      FiniteNuisanceRates M μ (fun n t => (eh n t).share a) (e0.share a))
    :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o : Obs X Z,
        ((∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
          indicator (o.2.1 ∈ policyUnion L k j) * hMinus phi L (eh (2*(n+1)) a) k j o.1) -
          ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
          indicator (o.2.1 ∈ policyUnion L k j) * hMinus phi L e0 k j o.1)^2
        ∂observationLaw M) atTop (fun _ _ => 0) := by
  let F := fun (k j n : ℕ) (a : A) (o : Obs X Z) =>
    indicator (o.2.1 ∈ policyUnion L k j) * hMinus phi L (eh (2*(n+1)) a) k j o.1 -
      indicator (o.2.1 ∈ policyUnion L k j) * hMinus phi L e0 k j o.1
  have hF (k j n : ℕ) (a : A) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
      MemLp (F k j n a) 2 (observationLaw M) :=
    (fitted_event_hinge_memLp M phi hphi L _ (heh (2*(n+1)) a) k j hk hj).sub
      (fitted_event_hinge_memLp M phi hphi L e0 he0 k j hk hj)
  have hs := dml_finset_sum_sq_tendsto_probability_zero μ (observationLaw M)
    (Finset.range L.K) (fun k n a o => ∑ j ∈ Finset.Icc 1 (L.l k), F k j n a o)
    (fun k hk n a => memLp_finsetSum _
      (fun j hj => hF k j n a (Finset.mem_range.mp hk) (Finset.mem_Icc.mp hj))) (by
      intro k hk
      apply dml_finset_sum_sq_tendsto_probability_zero μ (observationLaw M)
        (Finset.Icc 1 (L.l k)) (F k)
        (fun j hj n a => hF k j n a (Finset.mem_range.mp hk) (Finset.mem_Icc.mp hj))
      intro j hj
      exact nuisanceRates_event_hinge_sq_tendsto_probability_zero M μ phi dphi hphi hd
        hDerivative L e0 eh he0 heh hrp hrlev hrP hrs k j
        (Finset.mem_range.mp hk) (Finset.mem_Icc.mp hj))
  simpa only [F, Finset.sum_sub_distrib] using hs

-- @node: nuisanceRates_event_hinge_block_l2_tendsto_probability_zero
/-- Suppose [the policy map is valid](hyp:hphi), [has the specified derivative](hyp:hd),
and [that derivative is bounded and Lipschitz](hyp:hDerivative), with [admissible
reference binary nuisances](hyp:he0) and [admissible fitted binary nuisances at every
sample size and realization](hyp:heh). If the finite nuisance rate conditions hold
for [the propensity](hyp:hrp), [the baseline levels](hyp:hrlev), [the treated success
probabilities](hyp:hrP), and [every regular-index share](hyp:hrs), then [the L2 distance
under the observation law between the fitted and reference sums of policy group
union indicator-weighted hinges over all valid regular indices converges in
probability to zero along even sample sizes starting at two](goal). -/
lemma nuisanceRates_event_hinge_block_l2_tendsto_probability_zero
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1)
    (hrs : ∀ a : RegularIndex L,
      FiniteNuisanceRates M μ (fun n t => (eh n t).share a) (e0.share a))
    :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt (∫ o : Obs X Z,
        ((∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
          indicator (o.2.1 ∈ policyUnion L k j) * hMinus phi L (eh (2*(n+1)) a) k j o.1) -
          ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
          indicator (o.2.1 ∈ policyUnion L k j) * hMinus phi L e0 k j o.1)^2
        ∂observationLaw M)) atTop (fun _ _ => 0) := by
  have hs := nuisanceRates_event_hinge_block_sq_tendsto_probability_zero M μ phi dphi
    hphi hd hDerivative L e0 eh he0 heh hrp hrlev hrP hrs
  have hc : Continuous (fun t : ℝ => Real.sqrt t) := by fun_prop
  simpa only [Real.sqrt_zero] using
    Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt hc.continuousAt hs

end Papers.TbsPrteOptimalTransport
