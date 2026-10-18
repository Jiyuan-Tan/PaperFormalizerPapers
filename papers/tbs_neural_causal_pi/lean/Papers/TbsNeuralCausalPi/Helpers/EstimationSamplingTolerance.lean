module
public import Papers.TbsNeuralCausalPi.Helpers.EstimationSamplingSupport
public import Papers.TbsNeuralCausalPi.Helpers.SimulationSamplingMesh
public import Papers.TbsNeuralCausalPi.Helpers.ObservationalRateExponents
/-! # Absorption of the complete sampling error into the prescribed tolerance

The simulation mesh retains the constant term in its depth budget. It is
absorbed into the latent mesh without changing the dimension or the rate.
The empirical entropy bias is then included in the same fixed multiplier.
-/
public section
namespace Papers.TbsNeuralCausalPi
open Filter MeasureTheory
open scoped NNReal ENNReal Topology

-- @node: simulation_constant_depth_le_latent_mesh
/-- If [simulation size is at least one](hyp:hm), then [its logarithm divided
by its square root is at most its logarithm times the negative power with
exponent one divided by two plus the larger of one and the latent dimension](goal). -/
lemma simulation_constant_depth_le_latent_mesh (DU : ℕ) {m : ℝ} (hm : 1 ≤ m) :
    Real.log m / Real.sqrt m ≤
      m ^ (-(1 : ℝ) / (max 1 DU + 2 : ℕ)) * Real.log m := by
  have hm0 : 0 < m := by linarith
  have he : -(1 : ℝ) / 2 ≤ -(1 : ℝ) / (max 1 DU + 2 : ℕ) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (max 1 DU + 2 : ℕ))).mpr
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
    nlinarith [Nat.cast_nonneg (max 1 DU) (α := ℝ)]
  have hp := Real.monotone_rpow_of_base_ge_one hm he
  calc
    _ = m ^ (-(1 : ℝ) / 2) * Real.log m := by
      rw [Real.sqrt_eq_rpow, neg_div, Real.rpow_neg hm0.le, div_eq_mul_inv, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_right hp (Real.log_nonneg hm)

-- @node: simulation_full_mesh_le_twice_unpadded
/-- If [simulation size is at least one](hyp:hm) and [total depth is nonnegative](hyp:hh),
then [the latent simulation mesh plus the log-size over square-root-size term
weighted by one plus depth is at most twice the same sum weighted by depth
without the added one](goal). -/
lemma simulation_full_mesh_le_twice_unpadded (DU : ℕ) {m h : ℝ}
    (hm : 1 ≤ m) (hh : 0 ≤ h) :
    m ^ (-(1 : ℝ) / (max 1 DU + 2 : ℕ)) * Real.log m +
        (1 + h) * Real.log m / Real.sqrt m ≤
      2 * (m ^ (-(1 : ℝ) / (max 1 DU + 2 : ℕ)) * Real.log m +
        h * Real.log m / Real.sqrt m) := by
  have hc := simulation_constant_depth_le_latent_mesh DU hm
  have hd : 0 ≤ h * Real.log m / Real.sqrt m :=
    div_nonneg (mul_nonneg hh (Real.log_nonneg hm)) (Real.sqrt_nonneg _)
  rw [add_mul, add_div, one_mul]
  linarith

-- @node: consistencyGrowth_sampling_slack_le_sN
/-- Under [the consistency growth schedule](hyp:h), with [positive regularization
parameters](hyp:hlam), [a nonnegative simulation multiplier](hyp:hA), and [a
nonnegative observational multiplier](hyp:hT), [there exists a positive sampling
tolerance multiplier such that eventually the weighted full simulation mesh,
the weighted observational rate, and twice regularization times one plus the
log of the product of sample sizes sum to at most the prescribed sampling
tolerance](goal). -/
lemma consistencyGrowth_sampling_slack_le_sN {dU DU : ℕ}
    {m W0 L1 L2 : ℕ → ℕ} {tau lam : ℕ → ℝ}
    (h : ConsistencyGrowthSchedule dU m W0 L1 L2 tau lam)
    (hlam : ∀ r, 0 < lam r) {A T : ℝ} (hA : 0 ≤ A) (hT : 0 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ r in atTop,
      A * ((m r : ℝ) ^ (-(1 : ℝ) / (max 1 DU + 2 : ℕ)) * Real.log (m r) +
        (1 + (L1 r : ℝ) + L2 r) * Real.log (m r) / Real.sqrt (m r)) +
        T * observationalRateScale DU r +
        2 * (Real.log (r * m r : ℕ) + 1) * lam r ≤ sN c DU m L1 L2 lam r := by
  let c := 2 * A + T + 5
  have hc : 0 < c := by dsimp [c]; linarith
  refine ⟨c, hc, ?_⟩
  have hm := consistencyGrowth_simulation_tendsto h
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [consistencyGrowth_sN_eventually_eq (DU := DU) hc hlam h,
    hm.eventually (eventually_ge_atTop (1 : ℝ)),
    hlog.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (1 : ℕ)] with r heq hm1 hrlog hr1
  rw [heq]
  have hprod : (r : ℝ) ≤ (r : ℝ) * (m r : ℝ) :=
    le_mul_of_one_le_right (Nat.cast_nonneg _) hm1
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
  have hb : 1 ≤ Real.log (r * m r : ℕ) := by
    exact hrlog.trans (Real.log_le_log hr0 (by simpa only [Nat.cast_mul] using hprod))
  have hbias : 2 * (Real.log (r * m r : ℕ) + 1) * lam r ≤
      4 * (Real.log (r * m r : ℕ) * lam r) := by nlinarith [hlam r]
  have hmesh := simulation_full_mesh_le_twice_unpadded DU hm1
    (add_nonneg (Nat.cast_nonneg (L1 r)) (Nat.cast_nonneg (L2 r)))
  have hmeshA := mul_le_mul_of_nonneg_left hmesh hA
  have hu : 0 ≤ (m r : ℝ) ^ (-(1 : ℝ) / (max 1 DU + 2 : ℕ)) * Real.log (m r) :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.log_nonneg hm1)
  have hv : 0 ≤ (L1 r + L2 r : ℕ) * Real.log (m r) / Real.sqrt (m r) :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hm1)) (Real.sqrt_nonneg _)
  have ht : 0 ≤ observationalRateScale DU r := by unfold observationalRateScale; positivity
  have hz : 0 ≤ Real.log (r * m r : ℕ) * lam r := mul_nonneg (by linarith) (hlam r).le
  have hcu : 0 ≤ c - 2 * A := by dsimp [c]; linarith
  have hct : 0 ≤ c - T := by dsimp [c]; linarith
  have hcz : 0 ≤ c - 4 := by dsimp [c]; linarith
  have h1 := mul_nonneg hcu hu
  have h2 := mul_nonneg hcu hv
  have h3 := mul_nonneg hct ht
  have h4 := mul_nonneg hcz hz
  simp only [Nat.cast_add] at hv h2 ⊢
  simp only [observationalRateScale] at ht h3 ⊢
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_max] at h1 h2 h3 h4 hmeshA hbias ⊢
  simp only [add_assoc] at hmeshA ⊢
  simp only [div_eq_mul_inv] at hmeshA h1 h2 h3 h4 hbias ⊢
  nlinarith only [hmeshA, hbias, h1, h2, h3, h4]

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

-- @node: consistencyGrowth_constraint_threshold_of_sampling_tails
/-- For [output and Lipschitz bounds](hyp:K,L), assume [the reference model's
variables satisfy the output bound](hyp:hK), [all simulation sizes](hyp:hm) and
[regularization parameters](hyp:hlam) are positive, and [the consistency growth
schedule holds](hyp:hgrowth). For [observed samples](hyp:sample) and [simulation
inputs](hyp:draws), suppose [the observations are complete independent draws from
the reference law](hyp:hsample), [the simulation multiplier](hyp:hA), [observational
multiplier](hyp:hT), and [observational failure constant](hyp:hBobs) are nonnegative,
[the uniform simulation mesh error has an eventual inverse-cubic simulation-size
failure bound](hyp:hsim), and [the observational rate error has an eventual
inverse-fourth-power sample-size failure bound](hyp:hobs). Then [there exist
positive tolerance and failure constants such that eventually the probability
that any restricted candidate violates either population Wasserstein versus
empirical Sinkhorn comparison, with the prescribed sampling tolerance as slack,
is at most the failure constant times inverse sample size squared](goal). -/
lemma consistencyGrowth_constraint_threshold_of_sampling_tails
    {Omega : Type*} [MeasurableSpace Omega] (Q : Measure Omega)
    (M : EuclideanSCM kind dims) (K L : ℝ≥0) (hK : VariablesBoundedAt M K)
    {counts : Fin b → ℕ}
    (F0 : ℕ → StructuralClass kind dims dag C) (F1 : ℕ → GeneratorClass dims counts)
    {dU : ℕ} (m W0 L1 L2 : ℕ → ℕ) (tau lam : ℕ → ℝ)
    (hm : ∀ r, 0 < m r) (hlam : ∀ r, 0 < lam r)
    (hgrowth : ConsistencyGrowthSchedule dU m W0 L1 L2 tau lam)
    (sample : ∀ r, Fin r → Omega → Joint kind)
    (draws : ∀ r, Fin (m r) → Omega → SimulationInput kind counts)
    (hsample : ObservationalSampleCompleteIID Q M sample)
    (A T Bobs : ℝ) (hA : 0 ≤ A) (hT : 0 ≤ T) (hBobs : 0 ≤ Bobs)
    (hsim : ∀ᶠ r in atTop,
      Q {w | ∃ R : NCMIn kind dims dag G C counts (F0 r) (F1 r),
        restrictedCandidate K L R ∧
        ¬ wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
          (empiricalMeasure (fun i => ncmEval R (draws r i w))) ≤
            ENNReal.ofReal (A * ((m r : ℝ) ^ (-(1 : ℝ) / (max 1 (∑ j, dims j) + 2 : ℕ)) *
              Real.log (m r) + (1 + (L1 r : ℝ) + L2 r) * Real.log (m r) / Real.sqrt (m r)))} ≤
        ENNReal.ofReal ((m r : ℝ) ^ (-(3 : ℝ))))
    (hobs : ∀ᶠ r in atTop,
      Q {w | ¬ wasserstein1 (observationalLaw M)
        (empiricalMeasure (fun i => sample r i w)) ≤
          ENNReal.ofReal (T * observationalRateScale (∑ j, dims j) r)} ≤
        ENNReal.ofReal (Bobs * (r : ℝ) ^ (-(4 : ℤ)))) :
    ∃ cs B : ℝ, 0 < cs ∧ 0 < B ∧ ∀ᶠ r in atTop,
      Q {w | ∃ R : NCMIn kind dims dag G C counts (F0 r) (F1 r),
        restrictedCandidate K L R ∧
        let e := sinkhornDivergence (lam r)
          (fun i => jointVector (ncmEval R (draws r i w)))
          (fun i => jointVector (sample r i w)) (uniformWeights (m r)) (uniformWeights r)
        let slack := sN cs (∑ j, dims j) m L1 L2 lam r
        ¬ (wasserstein1 (observationalLaw R.canonical.toEuclideanSCM) (observationalLaw M) ≤
          ENNReal.ofReal (e + slack) ∧ ENNReal.ofReal (e - slack) ≤
            wasserstein1 (observationalLaw R.canonical.toEuclideanSCM) (observationalLaw M))} ≤
        ENNReal.ofReal (B * (r : ℝ) ^ (-(2 : ℤ))) := by
  obtain ⟨cs, hcs, hslack⟩ := consistencyGrowth_sampling_slack_le_sN
    (DU := ∑ j, dims j) hgrowth hlam hA hT
  obtain ⟨Bs, hBs, hscale⟩ := consistencyGrowth_simulation_cubic_tail_le hgrowth
  refine ⟨cs, Bs + Bobs, hcs, by linarith, ?_⟩
  filter_upwards [hsim, hobs, hslack, hscale, eventually_ge_atTop (2 : ℕ)]
    with r hs ho hsl hsc hr
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
  have hmR : (1 : ℝ) ≤ m r := by exact_mod_cast hm r
  have hlog : 0 ≤ Real.log (m r) := Real.log_nonneg hmR
  have hraw := restricted_ncm_sinkhorn_constraint_failure_le Q (by omega) (hm r)
    M K L hK (F0 r) (F1 r) (sample r) (fun i => (hsample r).2 i |>.1)
    (fun i => (hsample r).2 i |>.2) (draws r) _ _ (lam r)
    (mul_nonneg hA (add_nonneg
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hlog)
      (div_nonneg (mul_nonneg (by positivity) hlog) (Real.sqrt_nonneg _))))
    (mul_nonneg hT (observationalRateScale_pos _ (by exact_mod_cast hr)).le)
    (hlam r) _ _ hs ho
  apply le_trans (measure_mono ?_) (hraw.trans ?_)
  · intro w hw
    obtain ⟨R, hR, hbad⟩ := hw
    refine ⟨R, hR, ?_⟩
    dsimp only at hbad ⊢
    intro hgood
    apply hbad
    constructor
    · exact hgood.1.trans (ENNReal.ofReal_le_ofReal (by linarith only [hsl]))
    · exact (ENNReal.ofReal_le_ofReal (sub_le_sub_left hsl _)).trans hgood.2
  · have hp : (r : ℝ) ^ (-(4 : ℤ)) ≤ (r : ℝ) ^ (-(2 : ℤ)) := by
      simp only [zpow_neg, zpow_ofNat]
      exact inv_anti₀ (by positivity : (0 : ℝ) < (r : ℝ)^2)
        (pow_le_pow_right₀ hrR (by norm_num : 2 ≤ 4))
    calc
      _ ≤ ENNReal.ofReal (Bs * (r : ℝ) ^ (-(2 : ℤ))) +
          ENNReal.ofReal (Bobs * (r : ℝ) ^ (-(2 : ℤ))) :=
        add_le_add (ENNReal.ofReal_le_ofReal hsc)
          (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hp hBobs))
      _ = _ := by
        rw [← ENNReal.ofReal_add (mul_nonneg hBs.le (by positivity))
          (mul_nonneg hBobs (by positivity)), ← add_mul]

end Papers.TbsNeuralCausalPi
