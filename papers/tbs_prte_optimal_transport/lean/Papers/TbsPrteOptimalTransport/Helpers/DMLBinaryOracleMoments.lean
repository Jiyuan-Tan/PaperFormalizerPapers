module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLOracleSecondMoment
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBinaryScoreBounds
/-! The binary oracle second-moment LLN from clipping and overlap. The complete
score bound supplies square integrability of centered squares without imposing
an additional fourth-moment assumption on the paper. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: fitted_binary_centered_square_memLp
/-- For [a valid policy map](hyp:hphi) with [the specified derivative](hyp:hd) and
[a bounded Lipschitz derivative](hyp:hDerivative), suppose [the level count is positive](hyp:hK),
[the nuisance record is admissible](hyp:he), and [outcomes are almost surely binary](hyp:hy).
If [the common denominator lower bound is positive](hyp:hc) and
[baseline level masses](hyp:hpi) and [regular group masses](hyp:htau) exceed it almost surely,
then [the squared binary score centered at any real constant is square integrable
under the observation distribution](goal). -/
lemma fitted_binary_centered_square_memLp
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (e : NuisanceBin L) (he : BinAdmissible M L e) (hy : OutcomeBinaryAE M)
    (c : ℝ) (hc : 0 < c)
    (hpi : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (htau : ∀ r : RegularIndex L, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x) (theta : ℝ) :
    MemLp (fun o => (psiBin M phi dphi L hK o e - theta)^2) 2 (observationLaw M) := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  have hm := (fitted_binary_score_memLp M phi dphi hphi hd hDerivative L hK e he
    hy c hc hpi htau).aestronglyMeasurable
  obtain ⟨B, D, hB, hD, hb⟩ := hDerivative
  let C : ℝ := (∑ k ∈ Finset.range L.K, (1 + 2/c + ∑ j ∈ Finset.Icc 1 (L.l k),
      (1 + 4/c + ((L.T k j).card + (L.T k (j-1)).card) * B / c))) +
      |M.yMin| * (2 + B + 1/c)
  have hbound := fitted_binary_score_abs_bound M phi dphi hphi B hB
    (fun z x p hp => (hb z x p p hp hp).1) L hK e he hy c hc hpi htau
  apply MemLp.of_bound (hm.sub aestronglyMeasurable_const |>.pow 2)
    ((max C 0 + |theta|)^2)
  filter_upwards [hbound] with o ho
  change ‖(psiBin M phi dphi L hK o e - theta)^2‖ ≤ (max C 0 + |theta|)^2
  have hh : |psiBin M phi dphi L hK o e - theta| ≤ max C 0 + |theta| :=
    (abs_sub _ _).trans (add_le_add (ho.trans (le_max_left C 0)) le_rfl)
  have hn : 0 ≤ max C 0 + |theta| := add_nonneg (le_max_right C 0) (abs_nonneg theta)
  simpa only [Real.norm_eq_abs, abs_pow] using
    (sq_le_sq₀ (abs_nonneg _) hn).2 hh

-- @node: equalHalfSplit_binary_oracle_second_moment_consistent
/-- Under [an equal half-split sampling scheme](hyp:hSplit),
[a valid policy map](hyp:hphi), [its specified derivative](hyp:hd), and
[a bounded Lipschitz derivative](hyp:hDerivative), assume [a positive level count](hyp:hK),
[an admissible fixed nuisance record](hyp:he), [almost surely binary outcomes](hyp:hy),
[a positive denominator lower bound](hyp:hc), and almost sure lower bounds on
[baseline level masses](hyp:hpi) and [regular group masses](hyp:htau).
Then [the evaluation-sample average of squared binary scores centered at the chosen constant
converges in probability to its population counterpart](goal). -/
lemma equalHalfSplit_binary_oracle_second_moment_consistent
    {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (e : NuisanceBin L) (he : BinAdmissible M L e) (hy : OutcomeBinaryAE M)
    (c : ℝ) (hc : 0 < c)
    (hpi : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (htau : ∀ r : RegularIndex L, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x) (theta : ℝ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ((I₂ (2 * (n + 1)) a).card : ℝ)⁻¹ *
        ∑ i ∈ I₂ (2 * (n + 1)) a, (psiBin M phi dphi L hK (S.Z i a) e - theta)^2)
      atTop (fun _ _ => populationVariance M (fun o => psiBin M phi dphi L hK o e) theta) := by
  exact equalHalfSplit_oracle_mean_consistent_of_memLp M μ S I₁ I₂ hSplit
    (fun o => (psiBin M phi dphi L hK o e - theta)^2)
    (fitted_binary_centered_square_memLp M phi dphi hphi hd hDerivative L hK e he
      hy c hc hpi htau theta)

-- The oracle LLN is discharged here; only the fitted empirical error and
-- point-estimator consistency remain for the nuisance-rate argument to supply.
-- @node: equalHalfSplit_binary_varianceRV_consistent_of_empirical_score_error
/-- Suppose [sampling uses equal halves](hyp:hSplit), [the policy map is valid](hyp:hphi),
[its derivative is correctly specified](hyp:hd) and [bounded and Lipschitz](hyp:hDerivative),
[the level count is positive](hyp:hK), [the fixed nuisance record is admissible](hyp:he),
and [outcomes are almost surely binary](hyp:hy). With [a positive common lower bound](hyp:hc)
on [baseline level masses](hyp:hpi) and [regular group masses](hyp:htau), if
[the evaluation-sample mean squared difference between fitted and fixed binary scores vanishes in probability](hyp:hE)
and [the fitted score average converges in probability to the chosen center](hyp:hb), then
[the fitted empirical variance converges in probability to the fixed score's population squared deviation from that center](goal). -/
lemma equalHalfSplit_binary_varianceRV_consistent_of_empirical_score_error
    {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₁ I₂ : SampleSplit A)
    (hSplit : EqualHalfSplit M μ S I₁ I₂)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (e : NuisanceBin L) (he : BinAdmissible M L e) (hy : OutcomeBinaryAE M)
    (c : ℝ) (hc : 0 < c)
    (hpi : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (htau : ∀ r : RegularIndex L, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x) (theta : ℝ)
    (score : ℕ → A → Obs X Z → ℝ)
    (hE : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ((I₂ (2 * (n + 1)) a).card : ℝ)⁻¹ *
        ∑ i ∈ I₂ (2 * (n + 1)) a,
          (score (2 * (n + 1)) a (S.Z i a) - psiBin M phi dphi L hK (S.Z i a) e)^2)
      atTop (fun _ _ => 0))
    (hb : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => dmlRV M S I₂ score (2 * (n + 1)) a - theta)
      atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ score (2 * (n + 1)) a) atTop
      (fun _ _ => populationVariance M (fun o => psiBin M phi dphi L hK o e) theta) := by
  have hI : ∀ n, ∀ᵐ a ∂μ, (I₂ (2 * (n + 1)) a).Nonempty := by
    intro n
    filter_upwards [(equalHalfSplit_evaluationIndex_laws M μ S I₁ I₂ hSplit n).1] with a ha
    rw [← ha.2]
    exact Finset.image_nonempty.mpr Finset.univ_nonempty
  exact varianceRV_consistent_of_empirical_score_error M S I₂ score
    (fun o => psiBin M phi dphi L hK o e) (fun n => 2 * (n + 1)) theta
    (populationVariance M (fun o => psiBin M phi dphi L hK o e) theta) hI hE
    (equalHalfSplit_binary_oracle_second_moment_consistent M μ S I₁ I₂ hSplit
      phi dphi hphi hd hDerivative L hK e he hy c hc hpi htau theta) hb

end Papers.TbsPrteOptimalTransport
