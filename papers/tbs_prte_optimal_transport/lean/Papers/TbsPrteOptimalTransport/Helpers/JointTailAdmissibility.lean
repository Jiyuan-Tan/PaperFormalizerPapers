module
public import Papers.TbsPrteOptimalTransport.Helpers.JointTailIntegration
public import Papers.TbsPrteOptimalTransport.Helpers.PolicyDerivativeMeasurability
/-! Tail-direction regularity and integrated baseline cancellation from admissibility. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

-- Two points of a bounded affine path recover a measurable bounded direction.
-- @node: affine_unit_direction_regular
/-- If [the path radius is positive](hyp:hr), [the initial function is measurable](hyp:hm0),
[its affine perturbation at half the radius is measurable](hyp:hmt), and [both the
initial function](hyp:hb0) and [that perturbation](hyp:hbt) lie between zero and one
almost everywhere, then [the direction is measurable and its absolute value is at
most two divided by the radius almost everywhere](goal). -/
lemma affine_unit_direction_regular {B : Type*} [MeasurableSpace B]
    (ν : Measure B) (p d : B → ℝ) (r : ℝ) (hr : 0 < r)
    (hm0 : Measurable p) (hmt : Measurable (fun b => p b + (r/2) * d b))
    (hb0 : ∀ᵐ b ∂ν, p b ∈ Icc (0 : ℝ) 1)
    (hbt : ∀ᵐ b ∂ν, p b + (r/2) * d b ∈ Icc (0 : ℝ) 1) :
    Measurable d ∧ ∀ᵐ b ∂ν, ‖d b‖ ≤ 2/r := by
  constructor
  · have hid : d = fun b => ((p b + (r/2) * d b) - p b) / (r/2) := by
      funext b
      field_simp
      <;> ring
    rw [hid]
    exact (hmt.sub hm0).div_const _
  · filter_upwards [hb0, hbt] with b hb ht
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · rw [← neg_div, div_le_iff₀ hr]
      nlinarith [hb.1, hb.2, ht.1, ht.2]
    · apply (le_div_iff₀ hr).2
      nlinarith [hb.1, hb.2, ht.1, ht.2]

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- The bound is common to every instrument; it does not assume a bounded direction.
-- @node: binary_propensity_direction_regular
/-- If [a binary nuisance direction is admissible at the given nuisance values](hyp:hd),
then [there is a common nonnegative bound such that every instrument-specific
propensity direction is measurable and bounded in absolute value by that constant
for almost every covariate value](goal). -/
lemma binary_propensity_direction_regular (L : LevelData Z X) (eta del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr eta) (.inr del)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, Measurable (del.prop z) ∧
      ∀ᵐ x ∂xLaw M, ‖del.prop z x‖ ≤ C := by
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  have h0 := hpath 0 (by simpa using hr)
  have ht := hpath (r/2) (by rw [abs_of_pos (by positivity)]; linarith)
  refine ⟨2/r, by positivity, ?_⟩
  intro z
  apply affine_unit_direction_regular (xLaw M) (eta.prop z) (del.prop z) r hr
  · have hm : Measurable (fun x => eta.prop z x + 0 * del.prop z x) := h0.2.1 z
    simpa only [zero_mul, add_zero] using hm
  · exact ht.2.1 z
  · have hb : ∀ᵐ x ∂xLaw M, eta.prop z x + 0 * del.prop z x ∈ Icc (0 : ℝ) 1 := h0.1 z
    simpa only [zero_mul, add_zero] using hb
  · exact ht.1 z

-- The same admissible neighborhood controls the positive baseline levels.
-- @node: binary_baseline_propensity_direction_regular
/-- If [a binary nuisance direction is admissible at the given nuisance values](hyp:hd),
then [there is a common nonnegative bound such that each positive-level baseline
propensity direction is measurable and bounded in absolute value by that constant
for almost every covariate value](goal). -/
lemma binary_baseline_propensity_direction_regular (L : LevelData Z X)
    (eta del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr eta) (.inr del)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : PositiveIndex L.K,
      Measurable (del.pLev a) ∧ ∀ᵐ x ∂xLaw M, ‖del.pLev a x‖ ≤ C := by
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  have h0 := hpath 0 (by simpa using hr)
  have ht := hpath (r/2) (by rw [abs_of_pos (by positivity)]; linarith)
  refine ⟨2/r, by positivity, ?_⟩
  intro a
  apply affine_unit_direction_regular (xLaw M) (eta.pLev a) (del.pLev a) r hr
  · have hm : Measurable (fun x => eta.pLev a x + 0 * del.pLev a x) := (h0.2.2.2.1 a).1
    simpa only [zero_mul, add_zero] using hm
  · exact (ht.2.2.2.1 a).1
  · have hb : ∀ᵐ x ∂xLaw M, eta.pLev a x + 0 * del.pLev a x ∈ Icc (0 : ℝ) 1 :=
      (h0.2.2.1 a).mono (fun _ hx => hx.1)
    simpa only [zero_mul, add_zero] using hb
  · exact (ht.2.2.1 a).mono (fun _ hx => hx.1)

-- Unlike a pointwise eventual statement, this neighborhood is uniform in x and z.
-- @node: binary_propensity_path_uniform_neighborhood
/-- If [a binary nuisance direction is admissible at the given nuisance values](hyp:hd),
then [throughout some common neighborhood of zero, every instrument-specific affine
propensity path lies between zero and one for almost every covariate value](goal). -/
lemma binary_propensity_path_uniform_neighborhood (L : LevelData Z X)
    (eta del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr eta) (.inr del)) :
    ∀ᶠ t : ℝ in nhds 0, ∀ z, ∀ᵐ x ∂xLaw M,
      eta.prop z x + t * del.prop z x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  filter_upwards [continuousAt_id.abs.eventually_lt_const (by simpa using hr)] with t ht
  exact (hpath t ht).1

-- Square integrability needed by the policy Taylor remainder is derived here.
-- @node: binary_propensity_direction_memLp
/-- If [a binary nuisance direction is admissible at the given nuisance values](hyp:hd),
then [its propensity direction for any fixed instrument is square integrable under
the covariate distribution](goal). -/
lemma binary_propensity_direction_memLp (L : LevelData Z X) (eta del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr eta) (.inr del)) (z : Z) :
    MemLp (del.prop z) 2 (xLaw M) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  obtain ⟨C, _, hb⟩ := binary_propensity_direction_regular M L eta del hd
  exact MemLp.of_bound (hb z).1.aestronglyMeasurable C (hb z).2

-- Assemble the actual baseline part of the simultaneous tail mean. All three
-- directions move together; their interaction is quadratic, not discarded.
-- @node: population_binary_tail_baseline_joint_orthogonality_of_admissible
/-- If [there is at least one level](hyp:hK), [baseline assignment probabilities have
the specified positive overlap bound](hyp:hov), and [the binary nuisance direction is
admissible at the truth](hyp:hd), then [the covariate integral of the negative perturbed
final-level propensity times the true tail weight, plus the path parameter times the
perturbed tail-weight-to-denominator ratio times the final-level propensity direction
and true denominator, has derivative zero at zero](goal). -/
lemma population_binary_tail_baseline_joint_orthogonality_of_admissible
    (L : LevelData Z X) (hK : LevelCountPos L.K) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del)) :
    HasDerivAt (fun t : ℝ => ∫ x,
      -(positiveValue (eta0Bin M L).pLev L.K x + t * positiveValue del.pLev L.K x) *
        (eta0Bin M L).gammaTail x +
      t * (((eta0Bin M L).gammaTail x + t * del.gammaTail x) /
        (positiveValue (eta0Bin M L).piLev L.K x + t * positiveValue del.piLev L.K x) *
          (positiveValue del.pLev L.K x * positiveValue (eta0Bin M L).piLev L.K x))
      ∂xLaw M) 0 0 := by
  haveI : IsProbabilityMeasure (xLaw M) := Measure.isProbabilityMeasure_map M.measX.aemeasurable
  have he := binary_admissible_direction_origin M L (eta0Bin M L) del hd
  obtain ⟨R, hR, hp⟩ := binary_baseline_propensity_direction_regular M L (eta0Bin M L) del hd
  obtain ⟨C, hC, hpi⟩ := binary_assignment_denominator_direction_regular M L (eta0Bin M L) del hd
  obtain ⟨hg, G, hG, hb⟩ := binary_tail_weight_direction_regular M L (eta0Bin M L) del hd
  let a : PositiveIndex L.K := ⟨L.K, hK, le_rfl⟩
  have hidx : 1 ≤ L.K ∧ L.K ≤ L.K := ⟨hK, le_rfl⟩
  simp only [positiveValue, dif_pos hidx]
  have hp0 : Measurable ((eta0Bin M L).pLev a) := (he.2.2.2.1 a).1
  have hpi0 : Measurable ((eta0Bin M L).piLev a) := (he.2.2.2.1 a).2.2
  have hg0 : Measurable ((eta0Bin M L).gammaTail) := he.2.2.2.2.2.2.2.2.2.2.2.2
  apply tail_baseline_joint_integral_orthogonality (xLaw M)
    ((eta0Bin M L).pLev a) (del.pLev a) ((eta0Bin M L).piLev a) (del.piLev a)
    (eta0Bin M L).gammaTail del.gammaTail cpi R C G hov.1 hR hC hG
  · intro t
    have hdp := (hp a).1
    have hdpi := (hpi a).1
    fun_prop
  · apply Integrable.of_bound (hp0.neg.mul hg0).aestronglyMeasurable 1
    filter_upwards [he.2.2.1 a, he.2.2.2.2.2.2.2.2.2.2.2.1] with x hx hgx
    change ‖-((eta0Bin M L).pLev a x) * (eta0Bin M L).gammaTail x‖ ≤ 1
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hx.1.1,
      abs_of_nonneg hgx.1]
    exact mul_le_one₀ hx.1.2 hgx.1 hgx.2
  · filter_upwards [(hp a).2, (hpi a).2, hb, he.2.2.1 a,
      he.2.2.2.2.2.2.2.2.2.2.2.1] with x hx hix hgx heX hgX
    refine ⟨?_, ?_, ?_, ⟨hov.2 x L.K hK le_rfl, heX.2.2.2⟩, ?_⟩
    · simpa only [Real.norm_eq_abs] using hx
    · simpa only [Real.norm_eq_abs] using hix
    · simpa only [Real.norm_eq_abs] using hgx
    · rw [abs_of_nonneg hgX.1]
      exact hgX.2

-- Only values on [0,1] enter the policy. A clipped representative supplies
-- measurability without imposing any condition on its off-domain extension.
-- @node: population_binary_tail_policy_path_integrable_of_admissible
/-- If [the model satisfies threshold crossing](hyp:h), [the policy is measurable and
maps propensities into the unit interval](hyp:hphi), [it has the specified propensity
derivative](hyp:hDiff), [that derivative is uniformly bounded and Lipschitz](hyp:hDerivative),
and [the binary nuisance direction is admissible at the truth](hyp:hd), then [for every
instrument and all path parameters sufficiently near zero, the true assignment
probability times the perturbed policy minus its derivative-based path correction
is integrable under the covariate distribution](goal). -/
lemma population_binary_tail_policy_path_integrable_of_admissible
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del)) :
    ∀ᶠ t : ℝ in nhds 0, ∀ z, Integrable (fun x => instProb M z x *
      (phi z x (M.prop z x + t * del.prop z x) -
        t * (dphi z x (M.prop z x + t * del.prop z x) * del.prop z x))) (xLaw M) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  obtain ⟨B, D, hB, hD, hbound⟩ := hDerivative
  obtain ⟨C, hC, hdir⟩ := binary_propensity_direction_regular M L (eta0Bin M L) del hd
  filter_upwards [binary_propensity_path_uniform_neighborhood M L (eta0Bin M L) del hd]
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

-- @node: population_binary_tail_policy_joint_orthogonality_of_admissible
/-- If [the model satisfies threshold crossing](hyp:h), [the policy is measurable and
maps propensities into the unit interval](hyp:hphi), [it has the specified propensity
derivative](hyp:hDiff), [that derivative is uniformly bounded and Lipschitz](hyp:hDerivative),
and [the binary nuisance direction is admissible at the truth](hyp:hd), then [for the
chosen instrument, the covariate integral of the true assignment probability times
the perturbed policy minus its derivative-based path correction has derivative zero
at zero](goal). -/
lemma population_binary_tail_policy_joint_orthogonality_of_admissible
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del)) (z : Z) :
    HasDerivAt (fun t : ℝ => ∫ x, instProb M z x *
      (phi z x (M.prop z x + t * del.prop z x) -
        t * (dphi z x (M.prop z x + t * del.prop z x) * del.prop z x)) ∂xLaw M) 0 0 := by
  have hi := population_binary_tail_policy_path_integrable_of_admissible M h
    phi dphi hphi hDiff hDerivative L del hd
  obtain ⟨B, D, hB, hD, hbound⟩ := hDerivative
  apply policy_debiased_weighted_integral_orthogonality (xLaw M) phi dphi hDiff
    D hD (fun z x a b ha hb => (hbound z x a b ha hb).2)
    z (M.prop z) (del.prop z) (instProb M z)
    (binary_propensity_direction_memLp M L (eta0Bin M L) del hd z)
  · haveI := M.instKernel_markov
    apply Eventually.of_forall
    intro x
    exact ⟨ENNReal.toReal_nonneg, measureReal_le_one⟩
  · exact Eventually.of_forall (fun x => M.rangeProp z x)
  · exact (binary_propensity_path_uniform_neighborhood M L (eta0Bin M L) del hd).mono
      (fun _ ht => ht z)
  · exact hi.mono (fun _ ht => (ht z).aestronglyMeasurable)
  · simpa only [zero_mul, add_zero, sub_zero] using hi.self_of_nhds z

-- @node: population_binary_tail_baseline_path_integrable_of_admissible
/-- If [there is at least one level](hyp:hK), [baseline assignment probabilities have
the specified positive overlap bound](hyp:hov), and [the binary nuisance direction is
admissible at the truth](hyp:hd), then [for all path parameters sufficiently near zero,
the negative perturbed final-level propensity times the true tail weight, plus the
path parameter times the perturbed tail-weight-to-denominator ratio times the
final-level propensity direction and true denominator, is covariate-integrable](goal). -/
lemma population_binary_tail_baseline_path_integrable_of_admissible
    (L : LevelData Z X) (hK : LevelCountPos L.K) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del)) :
    ∀ᶠ t : ℝ in nhds 0, Integrable (fun x =>
      -(positiveValue (eta0Bin M L).pLev L.K x + t * positiveValue del.pLev L.K x) *
        (eta0Bin M L).gammaTail x +
      t * (((eta0Bin M L).gammaTail x + t * del.gammaTail x) /
        (positiveValue (eta0Bin M L).piLev L.K x + t * positiveValue del.piLev L.K x) *
          (positiveValue del.pLev L.K x * positiveValue (eta0Bin M L).piLev L.K x)))
      (xLaw M) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  have he := binary_admissible_direction_origin M L (eta0Bin M L) del hd
  obtain ⟨R, hR, hp⟩ := binary_baseline_propensity_direction_regular M L (eta0Bin M L) del hd
  obtain ⟨C, hC, hpi⟩ := binary_assignment_denominator_direction_regular M L (eta0Bin M L) del hd
  obtain ⟨hg, G, hG, hb⟩ := binary_tail_weight_direction_regular M L (eta0Bin M L) del hd
  let a : PositiveIndex L.K := ⟨L.K, hK, le_rfl⟩
  have hidx : 1 ≤ L.K ∧ L.K ≤ L.K := ⟨hK, le_rfl⟩
  simp only [positiveValue, dif_pos hidx]
  have hp0 : Measurable ((eta0Bin M L).pLev a) := (he.2.2.2.1 a).1
  have hpi0 : Measurable ((eta0Bin M L).piLev a) := (he.2.2.2.1 a).2.2
  have hg0 : Measurable ((eta0Bin M L).gammaTail) := he.2.2.2.2.2.2.2.2.2.2.2.2
  have hdp := (hp a).1
  have hdpi := (hpi a).1
  have hcpi := hov.1
  have radius : 0 < cpi / (2*(C+1)) := by positivity
  filter_upwards [continuousAt_id.abs.eventually_lt_const (by simpa using radius)] with t ht
  change |t| < cpi / (2*(C+1)) at ht
  have hm : Measurable (fun x =>
      -((eta0Bin M L).pLev a x + t * del.pLev a x) * (eta0Bin M L).gammaTail x +
      t * (((eta0Bin M L).gammaTail x + t * del.gammaTail x) /
        ((eta0Bin M L).piLev a x + t * del.piLev a x) *
          (del.pLev a x * (eta0Bin M L).piLev a x))) := by fun_prop
  apply Integrable.of_bound hm.aestronglyMeasurable
    (1 + (R * (C+G) / (cpi/2)) * t^2)
  filter_upwards [(hp a).2, (hpi a).2, hb, he.2.2.1 a,
    he.2.2.2.2.2.2.2.2.2.2.2.1] with x hx hix hgx heX hgX
  have hpB : |(eta0Bin M L).pLev a x| ≤ 1 := by
    rw [abs_of_nonneg heX.1.1]; exact heX.1.2
  have hpiB : |(eta0Bin M L).piLev a x| ≤ 1 := by
    rw [abs_of_nonneg heX.2.2.1]; exact heX.2.2.2
  have hgB : |(eta0Bin M L).gammaTail x| ≤ 1 := by
    rw [abs_of_nonneg hgX.1]; exact hgX.2
  simp only [Real.norm_eq_abs] at hx hix hgx
  have hden : cpi/2 ≤ (eta0Bin M L).piLev a x + t * del.piLev a x := by
    have hmul : |t * del.piLev a x| ≤ |t| * C := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hix (abs_nonneg t)
    have hsmall := (lt_div_iff₀ (by positivity : 0 < 2*(C+1))).mp ht
    have htrue := hov.2 x L.K hK le_rfl
    change cpi ≤ (eta0Bin M L).piLev a x at htrue
    nlinarith [neg_abs_le (t * del.piLev a x), abs_nonneg t]
  have hcoef : |del.pLev a x| * (|(eta0Bin M L).gammaTail x| * |del.piLev a x| +
      |del.gammaTail x| * |(eta0Bin M L).piLev a x|) / (cpi/2) ≤ R * (C+G) / (cpi/2) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc
      _ ≤ R * (1*C + G*1) := by gcongr
      _ = _ := by ring
  have hr := tail_baseline_joint_remainder_bound ((eta0Bin M L).pLev a x)
    (del.pLev a x) ((eta0Bin M L).piLev a x) (del.piLev a x)
    ((eta0Bin M L).gammaTail x) (del.gammaTail x) t (cpi/2) (by positivity) hden
  have hbase : |-(eta0Bin M L).pLev a x * (eta0Bin M L).gammaTail x| ≤ 1 := by
    rw [abs_mul, abs_neg]
    exact mul_le_one₀ hpB (abs_nonneg _) hgB
  rw [Real.norm_eq_abs]
  calc
    _ ≤ |-(eta0Bin M L).pLev a x * (eta0Bin M L).gammaTail x| +
        |(-((eta0Bin M L).pLev a x + t * del.pLev a x) * (eta0Bin M L).gammaTail x +
          t * (((eta0Bin M L).gammaTail x + t * del.gammaTail x) /
            ((eta0Bin M L).piLev a x + t * del.piLev a x) *
            (del.pLev a x * (eta0Bin M L).piLev a x))) -
          (-(eta0Bin M L).pLev a x * (eta0Bin M L).gammaTail x)| := by
      simpa only [sub_zero, add_comm] using abs_sub_le
        (-((eta0Bin M L).pLev a x + t * del.pLev a x) * (eta0Bin M L).gammaTail x +
          t * (((eta0Bin M L).gammaTail x + t * del.gammaTail x) /
            ((eta0Bin M L).piLev a x + t * del.piLev a x) *
              (del.pLev a x * (eta0Bin M L).piLev a x)))
        (-(eta0Bin M L).pLev a x * (eta0Bin M L).gammaTail x) 0
    _ ≤ 1 + (R * (C+G) / (cpi/2)) * t^2 := by
      apply add_le_add hbase
      convert! hr.trans (mul_le_mul_of_nonneg_left hcoef (sq_nonneg t)) using 1 <;> ring

-- The complete finite conditional tail expression now needs no extra analytic
-- hypotheses. This is the expression identified by the population tower lemma.
-- @node: population_binary_tail_finite_mean_joint_orthogonality_of_admissible
/-- If [the model satisfies threshold crossing](hyp:h), [the policy is measurable and
maps propensities into the unit interval](hyp:hphi), [it has the specified propensity
derivative](hyp:hDiff), [that derivative is uniformly bounded and Lipschitz](hyp:hDerivative),
[there is at least one level](hyp:hK), [baseline assignment probabilities have the
specified positive overlap bound](hyp:hov), and [the binary nuisance direction is
admissible at the truth](hyp:hd), then [the covariate integral of the outcome-floor-scaled
finite tail expression, combining true-probability-weighted debiased policies with
the jointly perturbed baseline correction, has derivative zero at zero](goal). -/
lemma population_binary_tail_finite_mean_joint_orthogonality_of_admissible
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del)) :
    HasDerivAt (fun t : ℝ => ∫ x, M.yMin *
      ((∑ z ∈ policyUnion L L.K 1, instProb M z x *
        (phi z x (M.prop z x + t * del.prop z x) -
          t * (dphi z x (M.prop z x + t * del.prop z x) * del.prop z x))) -
        (positiveValue (eta0Bin M L).pLev L.K x + t * positiveValue del.pLev L.K x) *
          (eta0Bin M L).gammaTail x +
        t * (((eta0Bin M L).gammaTail x + t * del.gammaTail x) /
          (positiveValue (eta0Bin M L).piLev L.K x + t * positiveValue del.piLev L.K x) *
            (positiveValue del.pLev L.K x * positiveValue (eta0Bin M L).piLev L.K x)))
      ∂xLaw M) 0 0 := by
  let P : ℝ → Z → X → ℝ := fun t z x => instProb M z x *
    (phi z x (M.prop z x + t * del.prop z x) -
      t * (dphi z x (M.prop z x + t * del.prop z x) * del.prop z x))
  let B : ℝ → X → ℝ := fun t x =>
    -(positiveValue (eta0Bin M L).pLev L.K x + t * positiveValue del.pLev L.K x) *
      (eta0Bin M L).gammaTail x +
    t * (((eta0Bin M L).gammaTail x + t * del.gammaTail x) /
      (positiveValue (eta0Bin M L).piLev L.K x + t * positiveValue del.piLev L.K x) *
        (positiveValue del.pLev L.K x * positiveValue (eta0Bin M L).piLev L.K x))
  have hp : ∀ z ∈ policyUnion L L.K 1,
      HasDerivAt (fun t : ℝ => ∫ x, P t z x ∂xLaw M) 0 0 := by
    intro z _
    exact population_binary_tail_policy_joint_orthogonality_of_admissible M h
      phi dphi hphi hDiff hDerivative L del hd z
  have hs : HasDerivAt (fun t : ℝ => ∑ z ∈ policyUnion L L.K 1,
      ∫ x, P t z x ∂xLaw M) 0 0 := by
    simpa only [Finset.sum_const_zero] using HasDerivAt.fun_sum hp
  have hb : HasDerivAt (fun t : ℝ => ∫ x, B t x ∂xLaw M) 0 0 :=
    population_binary_tail_baseline_joint_orthogonality_of_admissible M L hK cpi hov del hd
  have hd' := (hs.add hb).const_mul M.yMin
  simp only [add_zero, mul_zero] at hd'
  apply hd'.congr_of_eventuallyEq
  filter_upwards [population_binary_tail_policy_path_integrable_of_admissible M h
    phi dphi hphi hDiff hDerivative L del hd,
    population_binary_tail_baseline_path_integrable_of_admissible M L hK cpi hov del hd]
      with t ht hbt
  have hi : ∀ z ∈ policyUnion L L.K 1, Integrable (P t z) (xLaw M) := fun z _ => ht z
  have heq : (fun x => (∑ z ∈ policyUnion L L.K 1, P t z x) -
      (positiveValue (eta0Bin M L).pLev L.K x + t * positiveValue del.pLev L.K x) *
        (eta0Bin M L).gammaTail x +
      t * (((eta0Bin M L).gammaTail x + t * del.gammaTail x) /
        (positiveValue (eta0Bin M L).piLev L.K x + t * positiveValue del.piLev L.K x) *
          (positiveValue del.pLev L.K x * positiveValue (eta0Bin M L).piLev L.K x))) =
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
