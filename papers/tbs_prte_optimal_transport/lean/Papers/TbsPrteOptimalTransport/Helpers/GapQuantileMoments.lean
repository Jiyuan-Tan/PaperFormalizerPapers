module
public import Papers.TbsPrteOptimalTransport.Helpers.JQuantileBands
public import Papers.TbsPrteOptimalTransport.Helpers.SelectedConditionalLaw
public import Papers.TbsPrteOptimalTransport.Helpers.Scores
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationBinaryTarget
/-! Unnormalized conditional quantile moments for the finite-instrument gaps. -/
public section
set_option linter.unusedSectionVars false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- Finite nonnegative interval increments permit subtraction after toReal.
-- @node: canonical_treated_increment_real
/-- If [the lower treatment threshold is nonnegative](hyp:ha) and [does not exceed
the upper threshold](hyp:hab), then [the real-valued mass of the treated submeasure
increment on any outcome set equals the upper-threshold mass minus the
lower-threshold mass](goal). -/
lemma canonical_treated_increment_real (x : X) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (B : Set ℝ) :
    ((canonSubmeasure M true x b - canonSubmeasure M true x a) B).toReal =
      (canonSubmeasure M true x b B).toReal - (canonSubmeasure M true x a B).toReal := by
  let K := (outcomeKernel (latentMarginal M true)).comap
    (fun u : ℝ => (u, x)) (by fun_prop)
  letI := outcomeKernel_isMarkov (latentMarginal M true)
  have hlow := interval_kernel_finite K 0 a
  have hinc := interval_kernel_finite K a b
  letI : IsFiniteMeasure ((volume.restrict (Ioc 0 a)).bind K) := ⟨hlow.lt_top⟩
  change (((volume.restrict (Ioc 0 b)).bind K -
      (volume.restrict (Ioc 0 a)).bind K) B).toReal =
    (((volume.restrict (Ioc 0 b)).bind K) B).toReal -
      (((volume.restrict (Ioc 0 a)).bind K) B).toReal
  rw [interval_kernel_add K 0 a b ha hab, add_comm,
    Measure.add_sub_cancel, Measure.add_apply,
    ENNReal.toReal_add
      (ne_top_of_le_ne_top hinc (measure_mono (subset_univ B)))
      (ne_top_of_le_ne_top hlow (measure_mono (subset_univ B)))]
  ring

-- Undo normalization before translating the quantile rank into the score moment.
-- @node: discrete_gap_cdf_unnormalized
/-- Under [invariant ordering of the baseline and policy levels](hyp:hL), for
[a gap index below the number of baseline gaps](hyp:hk), [the gap width times
the gap distribution's cumulative probability at any outcome threshold equals
the unnormalized treated submeasure increment below that threshold](goal). -/
lemma discrete_gap_cdf_unnormalized (prop q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant prop q L) (k : ℕ) (hk : k < L.K) (x : X) (y : ℝ) :
    (L.pLev (k+1) x - L.pLev k x) * cdf (discreteGapLaw M L k x) y =
      ((canonSubmeasure M true x (L.pLev (k+1) x) -
        canonSubmeasure M true x (L.pLev k x)) (Iic y)).toReal := by
  letI := discrete_gap_law_probability M prop q L hL k hk x
  have hwidth := hL.2.2.2.2.2.2.2.1 x k (k+1) (by omega) (by omega)
  have hp : 0 < L.pLev (k+1) x - L.pLev k x := sub_pos.mpr hwidth
  rw [cdf_eq_real, measureReal_def, discreteGapLaw, Measure.smul_apply,
    smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hp.le]
  rw [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]

-- The atom-free quantile has exactly its prescribed rank; multiplying by
-- the gap width gives the conditional moment used in the paper's score.
-- @node: discrete_gap_boundary_unnormalized_moment
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
and [invariant ordering of the baseline and policy levels](hyp:hL), [for almost
every covariate value, every valid gap and boundary with no atom at that boundary
has unnormalized cumulative gap mass equal to the policy level minus the lower
baseline propensity](goal). -/
lemma discrete_gap_boundary_unnormalized_moment (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (prop q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant prop q L) :
    ∀ᵐ x ∂xLaw M, ∀ k < L.K, ∀ j ≤ L.l k,
      discreteGapLaw M L k x {bandBoundary M L k j x} = 0 →
      ((canonSubmeasure M true x (L.pLev (k+1) x) -
        canonSubmeasure M true x (L.pLev k x))
          (Iic (bandBoundary M L k j x))).toReal = L.qLev k j x - L.pLev k x := by
  filter_upwards [discrete_band_boundary_cdf M h he prop q L hL] with x hx
  intro k hk j hj hn
  rw [← discrete_gap_cdf_unnormalized M prop q L hL k hk x, hx k hk j hj hn]
  have hwidth := hL.2.2.2.2.2.2.2.1 x k (k+1) (by omega) (by omega)
  unfold kappa
  exact mul_div_cancel₀ _ (sub_pos.mpr hwidth).ne'

-- This is the quantile equation expressed as the difference of the two
-- cumulative treated submeasures, before converting to selected-cell means.
-- @node: discrete_gap_boundary_submeasure_moment
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
and [invariant ordering of the baseline and policy levels](hyp:hL), [for almost
every covariate value and every valid gap boundary carrying no atom, the upper
treated cumulative mass minus the lower treated cumulative mass minus the policy
level's distance from the lower baseline propensity is zero](goal). -/
lemma discrete_gap_boundary_submeasure_moment (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (prop q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant prop q L) :
    ∀ᵐ x ∂xLaw M, ∀ k < L.K, ∀ j ≤ L.l k,
      discreteGapLaw M L k x {bandBoundary M L k j x} = 0 →
      (canonSubmeasure M true x (L.pLev (k+1) x)
        (Iic (bandBoundary M L k j x))).toReal -
      (canonSubmeasure M true x (L.pLev k x)
        (Iic (bandBoundary M L k j x))).toReal -
      (L.qLev k j x - L.pLev k x) = 0 := by
  filter_upwards [discrete_gap_boundary_unnormalized_moment M h he prop q L hL] with x hx
  intro k hk j hj hn
  have ha := hL.2.2.2.2.2.2.2.2.2.2.1 x k (by omega)
  have hab := hL.2.2.2.2.2.2.2.1 x k (k+1) (by omega) (by omega)
  have hm := hx k hk j hj hn
  rw [canonical_treated_increment_real M x _ _ ha.1 hab.le] at hm
  exact sub_eq_zero.mpr hm


-- A selected baseline cell has a constant propensity. Its assignment mass
-- cancels from the normalized law, leaving the latent treated submeasure.
-- @node: population_treated_cdf_unnormalized
/-- Under [the structural assumptions](hyp:h) and [invariant ordering of the
baseline and policy levels](hyp:hL), [for almost every covariate value, each valid
baseline instrument cell with nonzero assignment mass satisfies this identity:
its propensity times its normalized treated probability of any measurable outcome
set equals the canonical treated submeasure's mass on that set](goal). -/
lemma population_treated_cdf_unnormalized (h : StructuralAssumptions M)
    (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) :
    ∀ᵐ x ∂xLaw M, ∀ i ≤ L.K,
      M.instKernel x (L.S i : Set Z) ≠ 0 → ∀ B : Set ℝ, MeasurableSet B →
      L.pLev i x * (treatedLaw M L i x B).toReal =
        (canonSubmeasure M true x (L.pLev i x) B).toReal := by
  haveI := M.instKernel_markov
  filter_upwards [conditional_selected_submeasure_evaluation M h,
    conditional_selected_submeasure_mass M h, canonical_submeasure_mass M h true]
    with x he hm hc
  intro i hi hmass B hB
  have hS : MeasurableSet (L.S i : Set Z) := (L.S i).finite_toSet.measurableSet
  have hp := hL.2.2.2.2.2.2.2.2.2.2.1 x i (by omega)
  have hprop : ∀ᵐ z ∂(M.instKernel x).restrict (L.S i : Set Z),
      M.prop z x = L.pLev i x := by
    filter_upwards [ae_restrict_mem hS] with z hz
    exact (hL.2.2.2.2.2.1 x i z hi).mp hz
  have hev := he (L.S i : Set Z) hS B hB
  have hmv := hm (L.S i : Set Z) hS
  rw [lintegral_congr_ae (hprop.mono fun z hz => by rw [hz]),
    lintegral_const, Measure.restrict_apply_univ] at hev hmv
  simp only [Measure.restrict_apply_univ] at hmv
  rw [treatedLaw, Measure.smul_apply, hev, Measure.restrict_apply_univ, hmv, smul_eq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hp.1]
  have hmassR : (M.instKernel x (L.S i : Set Z)).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hmass, measure_ne_top _ _⟩
  by_cases hp0 : L.pLev i x = 0
  · have hz : canonSubmeasure M true x (L.pLev i x) B = 0 := by
      have hu : canonSubmeasure M true x (L.pLev i x) univ = 0 := by
        simpa only [Bool.true_eq, if_true, hp0, ENNReal.ofReal_zero] using hc _ hp
      exact le_antisymm ((measure_mono (subset_univ B)).trans_eq hu) (zero_le)
    rw [hz]
    simp [hp0]
  · field_simp


-- The structural-zero minus cell is omitted; every positive cell is supplied
-- by baseline overlap. No positivity of the zero cell is needed.
-- @node: population_boundary_indicator_unnormalized_moment
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[invariant ordering of baseline and policy levels](hyp:hL), and [baseline overlap
with a positive uniform lower bound on positive-level cell assignment masses](hyp:hov),
[almost everywhere in covariates, at every valid gap boundary without an atom,
the upper propensity times its boundary indicator mean minus the lower propensity
times its boundary indicator mean equals the policy level minus the lower
propensity](goal). -/
lemma population_boundary_indicator_unnormalized_moment (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (q : Z → X → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop q L) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) :
    ∀ᵐ x ∂xLaw M, ∀ k < L.K, ∀ j ≤ L.l k,
      discreteGapLaw M L k x {bandBoundary M L k j x} = 0 →
      L.pLev (k+1) x * boundaryIndicatorMean M L true k j x -
        L.pLev k x * boundaryIndicatorMean M L false k j x -
        (L.qLev k j x - L.pLev k x) = 0 := by
  haveI := M.instKernel_markov
  filter_upwards [population_treated_cdf_unnormalized M h q L hL,
    discrete_gap_boundary_submeasure_moment M h he M.prop q L hL,
    canonical_submeasure_mass M h true] with x ht hm hc
  intro k hk j hj hn
  have hmass (i : ℕ) (hi : 1 ≤ i) (hiK : i ≤ L.K) :
      M.instKernel x (L.S i : Set Z) ≠ 0 := by
    have hpos : 0 < (M.instKernel x (L.S i : Set Z)).toReal := by
      have hp := hov.2 x i hi hiK
      have hs := sum_measureReal_singleton (μ := M.instKernel x) (L.S i)
      change (∑ z ∈ L.S i, (M.instKernel x {z}).toReal) =
        (M.instKernel x (L.S i : Set Z)).toReal at hs
      change cpi ≤ ∑ z ∈ L.S i, (M.instKernel x {z}).toReal at hp
      rw [hs] at hp
      exact hov.1.trans_le hp
    exact fun hz => by simpa [hz] using hpos
  have hp := ht (k+1) (by omega) (hmass (k+1) (by omega) (by omega))
    (Iic (bandBoundary M L k j x)) measurableSet_Iic
  have hmoment := hm k hk j hj hn
  simp only [boundaryIndicatorMean, Bool.not_true, Bool.false_and,
    Bool.false_eq_true, if_false, if_true] at hp ⊢
  rw [hp]
  by_cases hk0 : k = 0
  · subst k
    have hp0 : L.pLev 0 x = 0 := by
      rw [hL.1 x 0 (by omega)]
      simp [pLevel]
    have hz : canonSubmeasure M true x (L.pLev 0 x)
        (Iic (bandBoundary M L 0 j x)) = 0 := by
      have hu : canonSubmeasure M true x (L.pLev 0 x) univ = 0 := by
        simpa only [Bool.true_eq, if_true, hp0, ENNReal.ofReal_zero] using hc (L.pLev 0 x) (by
          rw [hp0]; exact ⟨le_rfl, zero_le_one⟩)
      exact le_antisymm ((measure_mono (subset_univ _)).trans_eq hu) zero_le
    rw [hz] at hmoment
    simpa [hp0] using hmoment
  · have hm' := ht k hk.le (hmass k (by omega) hk.le)
      (Iic (bandBoundary M L k j x)) measurableSet_Iic
    simpa only [Bool.not_false, Bool.true_and, beq_iff_eq, hk0, if_false,
      Bool.false_eq_true, hm'] using hmoment


-- Both outcome scores use the same simplex-normalized policy pooling.
-- @node: population_pooledQ_eq_ordered_level
/-- Under [invariant ordering of baseline and induced policy levels](hyp:hL) and
[policy overlap](hyp:hov), for [a baseline level index no greater than the number
of gaps](hyp:hk) and [a boundary index within its policy subdivision](hyp:hj),
[the policy-pooled level evaluated at the true nuisance functions equals the
corresponding ordered policy level at every covariate value](goal). -/
lemma population_pooledQ_eq_ordered_level (phi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi) (k j : ℕ)
    (hk : k ≤ L.K) (hj : j ≤ L.l k) (x : X) :
    pooledQ phi L (trueNuisance M L) k j x = L.qLev k j x := by
  have heq : pooledQ phi L (trueNuisance M L) k j x =
      pooledQBin phi L (eta0Bin M L) k j x := by
    rfl
  rw [heq]
  exact population_pooledQBin_eq_ordered_level M phi L hL cpi hov k j hk hj x

-- This is the exact quantile moment in the continuous score, with its
-- structural-zero and simplex-pooling conventions unfolded faithfully.
-- @node: population_continuous_score_quantile_moment
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[invariant ordering of baseline and induced policy levels](hyp:hL),
[baseline overlap](hyp:hov), and [policy overlap](hyp:hpol), [the continuous
score's quantile moment at the true nuisance functions is zero almost everywhere
in covariates, for every valid gap boundary without an atom: the propensity-weighted
difference of boundary means equals the pooled policy level minus the lower
propensity, with the structural-zero conventions included](goal). -/
lemma population_continuous_score_quantile_moment (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (phi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi) :
    ∀ᵐ x ∂xLaw M, ∀ k < L.K, ∀ j ≤ L.l k,
      discreteGapLaw M L k x {bandBoundary M L k j x} = 0 →
      positiveValue (trueNuisance M L).pLev (k+1) x *
          boundaryValue (trueNuisance M L).Mplus k j x -
        positiveValue (trueNuisance M L).pLev k x *
          minusBoundaryValue (trueNuisance M L).Mminus k j x -
        (pooledQ phi L (trueNuisance M L) k j x -
          positiveValue (trueNuisance M L).pLev k x) = 0 := by
  filter_upwards [population_boundary_indicator_unnormalized_moment M h he
    (policyProp phi M.prop) L hL cpi hov] with x hx
  intro k hk j hj hn
  have hm := hx k hk j hj hn
  rw [population_pooledQ_eq_ordered_level M phi L hL cpi hpol k j hk.le hj]
  have hp : positiveValue (trueNuisance M L).pLev (k+1) x = L.pLev (k+1) x := by
    simp [positiveValue, trueNuisance, show 1 ≤ k+1 ∧ k+1 ≤ L.K by omega]
  rw [hp]
  simp only [boundaryValue, show k < L.K ∧ j ≤ L.l k from ⟨hk, hj⟩,
    dif_pos, trueNuisance]
  by_cases hk0 : k = 0
  · subst k
    have hp0 : L.pLev 0 x = 0 := by
      rw [hL.1 x 0 (by omega)]
      simp [pLevel]
    simpa [positiveValue, minusBoundaryValue, hp0] using hm
  · have hk1 : 1 ≤ k := by omega
    simpa [positiveValue, minusBoundaryValue, hk1, hk.le, hk, hj,
      trueNuisance] using hm

end Papers.TbsPrteOptimalTransport
