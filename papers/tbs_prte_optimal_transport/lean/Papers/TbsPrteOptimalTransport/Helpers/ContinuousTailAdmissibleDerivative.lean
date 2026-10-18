module
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousFullAdmissibleDerivative
/-! Simultaneous continuous tail-policy and baseline cancellations from admissibility. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: continuous_admissible_direction_origin
/-- If [a direction gives an admissible continuous-nuisance path in a
neighborhood of a baseline](hyp:hd), [the baseline nuisance functions themselves
are admissible](goal). -/
lemma continuous_admissible_direction_origin (L : LevelData Z X)
    (eta del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl eta) (.inl del)) :
    ContAdmissible M L eta := by
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  have h0 := hpath 0 (by simpa using hr)
  rwa [continuous_nuisance_path_zero] at h0

-- @node: continuous_propensity_direction_regular
/-- If [a direction gives an admissible continuous-nuisance path around a
baseline](hyp:hd), [its propensity direction is measurable for every instrument
value and is almost surely bounded in absolute value by one common nonnegative
constant](goal). -/
lemma continuous_propensity_direction_regular (L : LevelData Z X)
    (eta del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl eta) (.inl del)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, Measurable (del.prop z) ∧
      ∀ᵐ x ∂xLaw M, ‖del.prop z x‖ ≤ C := by
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  have h0 := continuous_admissible_direction_origin M L eta del hd
  have ht := hpath (r/2) (by rw [abs_of_pos (by positivity)]; linarith)
  refine ⟨2/r, by positivity, ?_⟩
  intro z
  exact affine_unit_direction_regular (xLaw M) (eta.prop z) (del.prop z) r hr
    (h0.2.1 z) (ht.2.1 z) (h0.1 z) (ht.1 z)

-- @node: continuous_tail_weight_direction_regular
/-- If [a direction gives an admissible continuous-nuisance path around a
baseline](hyp:hd), [its common-tail weight direction is measurable and almost
surely bounded in absolute value by a nonnegative constant](goal). -/
lemma continuous_tail_weight_direction_regular (L : LevelData Z X)
    (eta del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl eta) (.inl del)) :
    Measurable del.gammaTail ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ x ∂xLaw M, ‖del.gammaTail x‖ ≤ C := by
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  have h0 := continuous_admissible_direction_origin M L eta del hd
  have ht := hpath (r/2) (by rw [abs_of_pos (by positivity)]; linarith)
  have hg := affine_unit_direction_regular (xLaw M) eta.gammaTail del.gammaTail r hr
    h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    ht.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    ht.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact ⟨hg.1, 2/r, by positivity, hg.2⟩

-- @node: continuous_propensity_path_uniform_neighborhood
/-- If [a direction gives an admissible continuous-nuisance path around a
baseline](hyp:hd), [for every sufficiently small step and every instrument value,
the baseline propensity plus the step times its direction lies almost surely
in the unit interval](goal). -/
lemma continuous_propensity_path_uniform_neighborhood (L : LevelData Z X)
    (eta del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl eta) (.inl del)) :
    ∀ᶠ t : ℝ in 𝓝 0, ∀ z, ∀ᵐ x ∂xLaw M,
      eta.prop z x + t * del.prop z x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  filter_upwards [continuousAt_id.abs.eventually_lt_const (by simpa using hr)] with t ht
  exact (hpath t ht).1

-- @node: continuous_propensity_direction_memLp
/-- If [a direction gives an admissible continuous-nuisance path around a
baseline](hyp:hd), [its propensity direction for any chosen instrument value
is measurable up to null sets and square-integrable under the covariate
distribution](goal). -/
lemma continuous_propensity_direction_memLp (L : LevelData Z X)
    (eta del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl eta) (.inl del)) (z : Z) :
    MemLp (del.prop z) 2 (xLaw M) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  obtain ⟨C, _, hb⟩ := continuous_propensity_direction_regular M L eta del hd
  exact MemLp.of_bound (hb z).1.aestronglyMeasurable C (hb z).2

-- Assemble the actual baseline part of the simultaneous tail mean. All three
-- directions move together; their interaction is quadratic, not discarded.
-- @node: population_continuous_tail_baseline_joint_orthogonality_of_admissible
/-- If [there is at least one positive baseline level](hyp:hK), [baseline
assignment probabilities satisfy overlap with the given bound](hyp:hov), and
[the continuous nuisance direction is admissible at the truth](hyp:hd), then
[the covariate mean of the negative perturbed highest baseline propensity times
the true tail weight, plus the step times the ratio of the perturbed tail weight
to the perturbed highest-level assignment probability times the baseline
propensity direction and true highest-level assignment probability, has
derivative zero at step zero](goal). -/
lemma population_continuous_tail_baseline_joint_orthogonality_of_admissible
    (L : LevelData Z X) (hK : LevelCountPos L.K) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del)) :
    HasDerivAt (fun t : ℝ => ∫ x,
      -(positiveValue (trueNuisance M L).pLev L.K x + t * positiveValue del.pLev L.K x) *
        (trueNuisance M L).gammaTail x +
      t * (((trueNuisance M L).gammaTail x + t * del.gammaTail x) /
        (positiveValue (trueNuisance M L).piLev L.K x + t * positiveValue del.piLev L.K x) *
          (positiveValue del.pLev L.K x * positiveValue (trueNuisance M L).piLev L.K x))
      ∂xLaw M) 0 0 := by
  haveI : IsProbabilityMeasure (xLaw M) := Measure.isProbabilityMeasure_map M.measX.aemeasurable
  have he := continuous_admissible_direction_origin M L (trueNuisance M L) del hd
  obtain ⟨R, hR, hp⟩ := continuous_baseline_direction_regular M L (trueNuisance M L) del hd
  obtain ⟨C, hC, hpi⟩ := continuous_assignment_direction_regular M L (trueNuisance M L) del hd
  obtain ⟨hg, G, hG, hb⟩ := continuous_tail_weight_direction_regular M L (trueNuisance M L) del hd
  let a : PositiveIndex L.K := ⟨L.K, hK, le_rfl⟩
  have hidx : 1 ≤ L.K ∧ L.K ≤ L.K := ⟨hK, le_rfl⟩
  simp only [positiveValue, dif_pos hidx]
  have hp0 : Measurable ((trueNuisance M L).pLev a) := he.2.2.2.1 a
  have hpi0 : Measurable ((trueNuisance M L).piLev a) := he.2.2.2.2.2.1 a
  have hg0 : Measurable ((trueNuisance M L).gammaTail) := he.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  apply tail_baseline_joint_integral_orthogonality (xLaw M)
    ((trueNuisance M L).pLev a) (del.pLev a) ((trueNuisance M L).piLev a) (del.piLev a)
    (trueNuisance M L).gammaTail del.gammaTail cpi R C G hov.1 hR hC hG
  · intro t
    have hdp := (hp a).1
    have hdpi := (hpi a).1
    fun_prop
  · apply Integrable.of_bound (hp0.neg.mul hg0).aestronglyMeasurable 1
    filter_upwards [he.2.2.1 a, he.2.2.2.2.1 a, he.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1] with x hx hix hgx
    change ‖-((trueNuisance M L).pLev a x) * (trueNuisance M L).gammaTail x‖ ≤ 1
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hx.1,
      abs_of_nonneg hgx.1]
    exact mul_le_one₀ hx.2 hgx.1 hgx.2
  · filter_upwards [(hp a).2, (hpi a).2, hb, he.2.2.1 a, he.2.2.2.2.1 a,
      he.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1] with x hx hix hgx heX hpiX hgX
    refine ⟨?_, ?_, ?_, ⟨hov.2 x L.K hK le_rfl, hpiX.2⟩, ?_⟩
    · simpa only [Real.norm_eq_abs] using hx
    · simpa only [Real.norm_eq_abs] using hix
    · simpa only [Real.norm_eq_abs] using hgx
    · rw [abs_of_nonneg hgX.1]
      exact hgX.2

-- Only values on [0,1] enter the policy. A clipped representative supplies
-- measurability without imposing any condition on its off-domain extension.
-- @node: population_continuous_tail_policy_path_integrable_of_admissible
/-- Suppose [treatment follows a threshold-crossing model](hyp:h), [the policy
map is measurable and preserves the unit interval](hyp:hphi), [it has the
specified derivative](hyp:hDiff), [that derivative is uniformly bounded and
Lipschitz](hyp:hDerivative), and [the continuous nuisance direction is admissible
at the truth](hyp:hd). Then [for every sufficiently small step and every
instrument value, the policy evaluated at the perturbed propensity minus the
step times its derivative there times the propensity direction, weighted by
the true instrument probability, is integrable under the covariate
distribution](goal). -/
lemma population_continuous_tail_policy_path_integrable_of_admissible
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del)) :
    ∀ᶠ t : ℝ in nhds 0, ∀ z, Integrable (fun x => instProb M z x *
      (phi z x (M.prop z x + t * del.prop z x) -
        t * (dphi z x (M.prop z x + t * del.prop z x) * del.prop z x))) (xLaw M) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  obtain ⟨B, D, hB, hD, hbound⟩ := hDerivative
  obtain ⟨C, hC, hdir⟩ := continuous_propensity_direction_regular M L (trueNuisance M L) del hd
  filter_upwards [continuous_propensity_path_uniform_neighborhood M L (trueNuisance M L) del hd]
    with t ht
  intro z
  let p : X → ℝ := fun x => M.prop z x + t * del.prop z x
  let pc : X → ℝ := fun x => max 0 (min 1 (p x))
  have hp : Measurable p :=
    (h.2.1.comp (measurable_const.prodMk measurable_id)).add ((hdir z).1.const_mul t)
  have hpc : Measurable pc := by fun_prop
  have hpcRange : ∀ x, pc x ∈ Icc (0 : ℝ) 1 := by
    intro x
    exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have heq : ∀ᵐ x ∂xLaw M, pc x = p x := by
    filter_upwards [ht z] with x hx
    change p x ∈ Icc (0 : ℝ) 1 at hx
    simp only [pc, min_eq_right hx.2, max_eq_right hx.1]
  have hPhi : Measurable (fun x => phi z x (pc x)) :=
    hphi.1.comp (measurable_const.prodMk
      (measurable_id.prodMk (hpc.subtype_mk (h := hpcRange))))
  have hDPhi : Measurable (fun x => dphi z x (pc x)) :=
    (policy_derivative_graph_measurable phi dphi hphi hDiff (fun _ x => pc x)
      (hpc.comp measurable_snd) (fun _ x => hpcRange x)).comp
        (measurable_const.prodMk measurable_id)
  have hm : Measurable (instProb M z) :=
    (Kernel.measurable_coe _ (measurableSet_singleton z)).ennreal_toReal
  have hmeas : AEStronglyMeasurable (fun x => instProb M z x *
      (phi z x (p x) - t * (dphi z x (p x) * del.prop z x))) (xLaw M) := by
    have hc : Measurable (fun x => instProb M z x *
        (phi z x (pc x) - t * (dphi z x (pc x) * del.prop z x))) := by
      have hdel := (hdir z).1
      first | fun_prop | exact hm.mul (hPhi.sub ((hDPhi.mul hdel).const_mul t))
    apply hc.aestronglyMeasurable.congr
    filter_upwards [heq] with x hx
    rw [hx]
  apply Integrable.of_bound hmeas (1 + |t| * (B*C))
  filter_upwards [ht z, (hdir z).2] with x hx hdX
  change p x ∈ Icc (0 : ℝ) 1 at hx
  haveI := M.instKernel_markov
  have hmB : |instProb M z x| ≤ 1 := by
    rw [instProb, abs_of_nonneg ENNReal.toReal_nonneg]
    exact measureReal_le_one
  have hqB : |phi z x (p x)| ≤ 1 := by
    have hq := hphi.2 z x (p x) hx
    rw [abs_of_nonneg hq.1]
    exact hq.2
  have hdB : |dphi z x (p x)| ≤ B := (hbound z x (p x) (p x) hx hx).1
  have heB : |del.prop z x| ≤ C := by simpa only [Real.norm_eq_abs] using hdX
  change ‖instProb M z x * (phi z x (p x) -
    t * (dphi z x (p x) * del.prop z x))‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul]
  calc
    _ ≤ 1 * (|phi z x (p x)| + |t * (dphi z x (p x) * del.prop z x)|) := by
      apply mul_le_mul hmB _ (abs_nonneg _) zero_le_one
      simpa only [sub_zero, zero_sub, abs_neg] using
        abs_sub_le (phi z x (p x)) 0 (t * (dphi z x (p x) * del.prop z x))
    _ ≤ 1 * (1 + |t| * (B*C)) := by
      simp only [abs_mul]
      gcongr
    _ = _ := one_mul _

-- @node: population_continuous_tail_policy_joint_orthogonality_of_admissible
/-- Suppose [treatment follows a threshold-crossing model](hyp:h), [the policy
map is measurable and preserves the unit interval](hyp:hphi), [it has the
specified derivative](hyp:hDiff), [that derivative is uniformly bounded and
Lipschitz](hyp:hDerivative), and [the continuous nuisance direction is admissible
at the truth](hyp:hd). Then [for any instrument value, the covariate mean of the
policy evaluated at the perturbed propensity minus the step times its
derivative there times the propensity direction, weighted by the true
instrument probability, has derivative zero at step zero](goal). -/
lemma population_continuous_tail_policy_joint_orthogonality_of_admissible
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del)) (z : Z) :
    HasDerivAt (fun t : ℝ => ∫ x, instProb M z x *
      (phi z x (M.prop z x + t * del.prop z x) -
        t * (dphi z x (M.prop z x + t * del.prop z x) * del.prop z x)) ∂xLaw M) 0 0 := by
  have hi := population_continuous_tail_policy_path_integrable_of_admissible M h
    phi dphi hphi hDiff hDerivative L del hd
  obtain ⟨B, D, hB, hD, hbound⟩ := hDerivative
  apply policy_debiased_weighted_integral_orthogonality (xLaw M) phi dphi hDiff
    D hD (fun z x a b ha hb => (hbound z x a b ha hb).2)
    z (M.prop z) (del.prop z) (instProb M z)
    (continuous_propensity_direction_memLp M L (trueNuisance M L) del hd z)
  · haveI := M.instKernel_markov
    apply Eventually.of_forall
    intro x
    exact ⟨ENNReal.toReal_nonneg, measureReal_le_one⟩
  · exact Eventually.of_forall (fun x => M.rangeProp z x)
  · exact (continuous_propensity_path_uniform_neighborhood M L (trueNuisance M L) del hd).mono
      (fun _ ht => ht z)
  · exact hi.mono (fun _ ht => (ht z).aestronglyMeasurable)
  · simpa only [zero_mul, add_zero, sub_zero] using hi.self_of_nhds z

-- @node: population_continuous_tail_baseline_path_integrable_of_admissible
/-- If [there is at least one positive baseline level](hyp:hK), [baseline
assignment probabilities satisfy overlap with the given bound](hyp:hov), and
[the continuous nuisance direction is admissible at the truth](hyp:hd), then
[for every sufficiently small step, the negative perturbed highest baseline
propensity times the true tail weight, plus the step times the ratio of the
perturbed tail weight to the perturbed highest-level assignment probability
times the baseline propensity direction and true highest-level assignment
probability, is integrable under the covariate distribution](goal). -/
lemma population_continuous_tail_baseline_path_integrable_of_admissible
    (L : LevelData Z X) (hK : LevelCountPos L.K) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del)) :
    ∀ᶠ t : ℝ in nhds 0, Integrable (fun x =>
      -(positiveValue (trueNuisance M L).pLev L.K x + t * positiveValue del.pLev L.K x) *
        (trueNuisance M L).gammaTail x +
      t * (((trueNuisance M L).gammaTail x + t * del.gammaTail x) /
        (positiveValue (trueNuisance M L).piLev L.K x + t * positiveValue del.piLev L.K x) *
          (positiveValue del.pLev L.K x * positiveValue (trueNuisance M L).piLev L.K x)))
      (xLaw M) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  have he := continuous_admissible_direction_origin M L (trueNuisance M L) del hd
  obtain ⟨R, hR, hp⟩ := continuous_baseline_direction_regular M L (trueNuisance M L) del hd
  obtain ⟨C, hC, hpi⟩ := continuous_assignment_direction_regular M L (trueNuisance M L) del hd
  obtain ⟨hg, G, hG, hb⟩ := continuous_tail_weight_direction_regular M L (trueNuisance M L) del hd
  let a : PositiveIndex L.K := ⟨L.K, hK, le_rfl⟩
  have hidx : 1 ≤ L.K ∧ L.K ≤ L.K := ⟨hK, le_rfl⟩
  simp only [positiveValue, dif_pos hidx]
  have hp0 : Measurable ((trueNuisance M L).pLev a) := he.2.2.2.1 a
  have hpi0 : Measurable ((trueNuisance M L).piLev a) := he.2.2.2.2.2.1 a
  have hg0 : Measurable ((trueNuisance M L).gammaTail) := he.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hdp := (hp a).1
  have hdpi := (hpi a).1
  have hcpi := hov.1
  have radius : 0 < cpi / (2*(C+1)) := by positivity
  filter_upwards [continuousAt_id.abs.eventually_lt_const (by simpa using radius)] with t ht
  change |t| < cpi / (2*(C+1)) at ht
  have hm : Measurable (fun x =>
      -((trueNuisance M L).pLev a x + t * del.pLev a x) * (trueNuisance M L).gammaTail x +
      t * (((trueNuisance M L).gammaTail x + t * del.gammaTail x) /
        ((trueNuisance M L).piLev a x + t * del.piLev a x) *
          (del.pLev a x * (trueNuisance M L).piLev a x))) := by fun_prop
  apply Integrable.of_bound hm.aestronglyMeasurable
    (1 + (R * (C+G) / (cpi/2)) * t^2)
  filter_upwards [(hp a).2, (hpi a).2, hb, he.2.2.1 a, he.2.2.2.2.1 a,
    he.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1] with x hx hix hgx heX hpiX hgX
  have hpB : |(trueNuisance M L).pLev a x| ≤ 1 := by
    rw [abs_of_nonneg heX.1]; exact heX.2
  have hpiB : |(trueNuisance M L).piLev a x| ≤ 1 := by
    rw [abs_of_nonneg hpiX.1]; exact hpiX.2
  have hgB : |(trueNuisance M L).gammaTail x| ≤ 1 := by
    rw [abs_of_nonneg hgX.1]; exact hgX.2
  simp only [Real.norm_eq_abs] at hx hix hgx
  have hden : cpi/2 ≤ (trueNuisance M L).piLev a x + t * del.piLev a x := by
    have hmul : |t * del.piLev a x| ≤ |t| * C := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hix (abs_nonneg t)
    have hsmall := (lt_div_iff₀ (by positivity : 0 < 2*(C+1))).mp ht
    have htrue := hov.2 x L.K hK le_rfl
    change cpi ≤ (trueNuisance M L).piLev a x at htrue
    nlinarith [neg_abs_le (t * del.piLev a x), abs_nonneg t]
  have hcoef : |del.pLev a x| * (|(trueNuisance M L).gammaTail x| * |del.piLev a x| +
      |del.gammaTail x| * |(trueNuisance M L).piLev a x|) / (cpi/2) ≤ R * (C+G) / (cpi/2) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc
      _ ≤ R * (1*C + G*1) := by gcongr
      _ = _ := by ring
  have hr := tail_baseline_joint_remainder_bound ((trueNuisance M L).pLev a x)
    (del.pLev a x) ((trueNuisance M L).piLev a x) (del.piLev a x)
    ((trueNuisance M L).gammaTail x) (del.gammaTail x) t (cpi/2) (by positivity) hden
  have hbase : |-(trueNuisance M L).pLev a x * (trueNuisance M L).gammaTail x| ≤ 1 := by
    rw [abs_mul, abs_neg]
    exact mul_le_one₀ hpB (abs_nonneg _) hgB
  rw [Real.norm_eq_abs]
  calc
    _ ≤ |-(trueNuisance M L).pLev a x * (trueNuisance M L).gammaTail x| +
        |(-((trueNuisance M L).pLev a x + t * del.pLev a x) * (trueNuisance M L).gammaTail x +
          t * (((trueNuisance M L).gammaTail x + t * del.gammaTail x) /
            ((trueNuisance M L).piLev a x + t * del.piLev a x) *
            (del.pLev a x * (trueNuisance M L).piLev a x))) -
          (-(trueNuisance M L).pLev a x * (trueNuisance M L).gammaTail x)| := by
      simpa only [sub_zero, add_comm] using abs_sub_le
        (-((trueNuisance M L).pLev a x + t * del.pLev a x) * (trueNuisance M L).gammaTail x +
          t * (((trueNuisance M L).gammaTail x + t * del.gammaTail x) /
            ((trueNuisance M L).piLev a x + t * del.piLev a x) *
              (del.pLev a x * (trueNuisance M L).piLev a x)))
        (-(trueNuisance M L).pLev a x * (trueNuisance M L).gammaTail x) 0
    _ ≤ 1 + (R * (C+G) / (cpi/2)) * t^2 := by
      apply add_le_add hbase
      convert! hr.trans (mul_le_mul_of_nonneg_left hcoef (sq_nonneg t)) using 1 <;> ring

-- The complete finite conditional tail expression now needs no extra analytic
-- hypotheses. This is the expression identified by the population tower lemma.
-- @node: population_continuous_tail_finite_mean_joint_orthogonality_of_admissible
/-- Suppose [treatment follows a threshold-crossing model](hyp:h), [the policy
map is measurable and preserves the unit interval](hyp:hphi), [it has the
specified derivative](hyp:hDiff), [that derivative is uniformly bounded and
Lipschitz](hyp:hDerivative), [there is at least one positive baseline
level](hyp:hK), [baseline assignment probabilities satisfy overlap](hyp:hov), and
[the continuous nuisance direction is admissible at the truth](hyp:hd). Then
[the covariate mean of the lower outcome endpoint times the sum of the
instrument-probability-weighted, derivative-corrected policy values over the
tail policy group and the corrected negative highest baseline propensity
contribution has derivative zero at step zero when the nuisance functions
move jointly](goal).

The baseline contribution uses the perturbed highest baseline propensity times
the negative true tail weight, with a step correction equal to the perturbed
tail weight divided by the perturbed highest-level assignment probability,
times the baseline propensity direction and true highest-level assignment
probability. -/
lemma population_continuous_tail_finite_mean_joint_orthogonality_of_admissible
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del)) :
    HasDerivAt (fun t : ℝ => ∫ x, M.yMin *
      ((∑ z ∈ policyUnion L L.K 1, instProb M z x *
        (phi z x (M.prop z x + t * del.prop z x) -
          t * (dphi z x (M.prop z x + t * del.prop z x) * del.prop z x))) -
        (positiveValue (trueNuisance M L).pLev L.K x + t * positiveValue del.pLev L.K x) *
          (trueNuisance M L).gammaTail x +
        t * (((trueNuisance M L).gammaTail x + t * del.gammaTail x) /
          (positiveValue (trueNuisance M L).piLev L.K x + t * positiveValue del.piLev L.K x) *
            (positiveValue del.pLev L.K x * positiveValue (trueNuisance M L).piLev L.K x)))
      ∂xLaw M) 0 0 := by
  let P : ℝ → Z → X → ℝ := fun t z x => instProb M z x *
    (phi z x (M.prop z x + t * del.prop z x) -
      t * (dphi z x (M.prop z x + t * del.prop z x) * del.prop z x))
  let B : ℝ → X → ℝ := fun t x =>
    -(positiveValue (trueNuisance M L).pLev L.K x + t * positiveValue del.pLev L.K x) *
      (trueNuisance M L).gammaTail x +
    t * (((trueNuisance M L).gammaTail x + t * del.gammaTail x) /
      (positiveValue (trueNuisance M L).piLev L.K x + t * positiveValue del.piLev L.K x) *
        (positiveValue del.pLev L.K x * positiveValue (trueNuisance M L).piLev L.K x))
  have hp : ∀ z ∈ policyUnion L L.K 1,
      HasDerivAt (fun t : ℝ => ∫ x, P t z x ∂xLaw M) 0 0 := by
    intro z _
    exact population_continuous_tail_policy_joint_orthogonality_of_admissible M h
      phi dphi hphi hDiff hDerivative L del hd z
  have hs : HasDerivAt (fun t : ℝ => ∑ z ∈ policyUnion L L.K 1,
      ∫ x, P t z x ∂xLaw M) 0 0 := by
    simpa only [Finset.sum_const_zero] using HasDerivAt.fun_sum hp
  have hb : HasDerivAt (fun t : ℝ => ∫ x, B t x ∂xLaw M) 0 0 :=
    population_continuous_tail_baseline_joint_orthogonality_of_admissible M L hK cpi hov del hd
  have hd' := (hs.add hb).const_mul M.yMin
  simp only [add_zero, mul_zero] at hd'
  apply hd'.congr_of_eventuallyEq
  filter_upwards [population_continuous_tail_policy_path_integrable_of_admissible M h
    phi dphi hphi hDiff hDerivative L del hd,
    population_continuous_tail_baseline_path_integrable_of_admissible M L hK cpi hov del hd]
      with t ht hbt
  have hi : ∀ z ∈ policyUnion L L.K 1, Integrable (P t z) (xLaw M) := fun z _ => ht z
  have heq : (fun x => (∑ z ∈ policyUnion L L.K 1, P t z x) -
      (positiveValue (trueNuisance M L).pLev L.K x + t * positiveValue del.pLev L.K x) *
        (trueNuisance M L).gammaTail x +
      t * (((trueNuisance M L).gammaTail x + t * del.gammaTail x) /
        (positiveValue (trueNuisance M L).piLev L.K x + t * positiveValue del.piLev L.K x) *
          (positiveValue del.pLev L.K x * positiveValue (trueNuisance M L).piLev L.K x))) =
      (fun x => (∑ z ∈ policyUnion L L.K 1, P t z x) + B t x) := by
    funext x
    dsimp only [B]
    ring
  symm
  change M.yMin * ((∑ z ∈ policyUnion L L.K 1, ∫ x, P t z x ∂xLaw M) +
    ∫ x, B t x ∂xLaw M) = _
  rw [integral_const_mul]
  change M.yMin * _ = M.yMin * ∫ x, _ ∂xLaw M
  rw [heq, integral_add (integrable_finsetSum _ hi) hbt, integral_finsetSum _ hi]

end Papers.TbsPrteOptimalTransport
