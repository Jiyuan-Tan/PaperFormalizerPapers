module
public import Papers.TbsPrteOptimalTransport.Helpers.JointPooledRemainder
public import Papers.TbsPrteOptimalTransport.Helpers.JointTailAdmissibility
public import Papers.TbsPrteOptimalTransport.Helpers.JointRegularConditional
/-! Admissible pooled directions and population cancellation of their joint remainder. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

set_option linter.style.haveILetI false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- Both regularity and the uniform bound follow from two points of the path.
-- @node: binary_pooled_denominator_direction_regular
/-- If [a binary nuisance direction is admissible at the baseline nuisance](hyp:hd),
[all its regular pooled-denominator directions are measurable and share a finite
nonnegative almost-everywhere bound under the covariate law](goal). -/
lemma binary_pooled_denominator_direction_regular (L : LevelData Z X)
    (eta del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr eta) (.inr del)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : RegularIndex L,
      Measurable (del.tauLev a) ∧ ∀ᵐ x ∂xLaw M, ‖del.tauLev a x‖ ≤ C := by
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  have h0 := hpath 0 (by simpa using hr)
  have ht := hpath (r/2) (by rw [abs_of_pos (by positivity)]; linarith)
  refine ⟨2/r, by positivity, ?_⟩
  intro a
  apply affine_unit_direction_regular (xLaw M) (eta.tauLev a) (del.tauLev a) r hr
  · have hm : Measurable (fun x => eta.tauLev a x + 0 * del.tauLev a x) :=
      (h0.2.2.2.2.2.1 a).1
    simpa only [zero_mul, add_zero] using hm
  · exact (ht.2.2.2.2.2.1 a).1
  · have hb : ∀ᵐ x ∂xLaw M, eta.tauLev a x + 0 * del.tauLev a x ∈ Icc (0 : ℝ) 1 :=
      (h0.2.2.2.2.1 a).mono (fun _ hx => hx.1)
    simpa only [zero_mul, add_zero] using hb
  · exact (ht.2.2.2.2.1 a).mono (fun _ hx => hx.1)

-- @node: binary_simplex_share_direction_regular
/-- If [a binary nuisance direction is admissible at the baseline nuisance](hyp:hd),
[its share directions are measurable and uniformly bounded almost everywhere by
one finite nonnegative constant, across regular levels and instruments](goal). -/
lemma binary_simplex_share_direction_regular (L : LevelData Z X)
    (eta del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr eta) (.inr del)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : RegularIndex L) z,
      Measurable (del.share a z) ∧ ∀ᵐ x ∂xLaw M, ‖del.share a z x‖ ≤ C := by
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  have h0 := hpath 0 (by simpa using hr)
  have ht := hpath (r/2) (by rw [abs_of_pos (by positivity)]; linarith)
  refine ⟨2/r, by positivity, ?_⟩
  intro a z
  apply affine_unit_direction_regular (xLaw M) (eta.share a z) (del.share a z) r hr
  · have hm : Measurable (fun x => eta.share a z x + 0 * del.share a z x) :=
      h0.2.2.2.2.2.2.2.1 a z
    simpa only [zero_mul, add_zero] using hm
  · exact ht.2.2.2.2.2.2.2.1 a z
  · have hb : ∀ᵐ x ∂xLaw M, eta.share a z x + 0 * del.share a z x ∈ Icc (0 : ℝ) 1 :=
      h0.2.2.2.2.2.2.1 a z
    simpa only [zero_mul, add_zero] using hb
  · exact ht.2.2.2.2.2.2.1 a z

-- The overlap neighborhood is uniform in x, rather than pointwise eventual.
-- @node: binary_pooled_denominator_uniform_neighborhood
/-- If [the nuisance direction is admissible](hyp:hd), [the lower bound is
positive](hyp:hc), and [the baseline pooled denominator at the chosen regular
level is at least that bound almost everywhere](hyp:hbase), then [throughout a
neighborhood of zero the perturbed denominator is at least half that bound
almost everywhere](goal). -/
lemma binary_pooled_denominator_uniform_neighborhood (L : LevelData Z X)
    (eta del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr eta) (.inr del))
    (a : RegularIndex L) (c : ℝ) (hc : 0 < c)
    (hbase : ∀ᵐ x ∂xLaw M, c ≤ eta.tauLev a x) :
    ∀ᶠ t : ℝ in nhds 0, ∀ᵐ x ∂xLaw M,
      c/2 ≤ (eta + t • del).tauLev a x := by
  obtain ⟨C, hC, hb⟩ := binary_pooled_denominator_direction_regular M L eta del hd
  have radius : 0 < c / (2*(C+1)) := by positivity
  filter_upwards [continuousAt_id.abs.eventually_lt_const (by simpa using radius)] with t ht
  change |t| < c / (2*(C+1)) at ht
  filter_upwards [hbase, (hb a).2] with x hx hdx
  simp only [Real.norm_eq_abs] at hdx
  have hmul : |t * del.tauLev a x| ≤ |t| * C := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hdx (abs_nonneg t)
  have hsmall := (lt_div_iff₀ (by positivity : 0 < 2*(C+1))).mp ht
  change c/2 ≤ eta.tauLev a x + t * del.tauLev a x
  nlinarith [neg_abs_le (t * del.tauLev a x), abs_nonneg t]

-- This is the actual pooled level and finite conditional residual. All analytic
-- conditions, including the L2 envelope, are derived from admissibility.
-- @node: binary_pooled_joint_integral_orthogonality_of_admissible
/-- Suppose [the policy is measurable and takes probabilities to probabilities](hyp:hphi),
[its derivative is the specified function](hyp:hDiff), and [that derivative is
uniformly bounded and Lipschitz](hyp:hDerivative). If [the joint nuisance direction
is admissible](hyp:hd), [the denominator lower bound is positive](hyp:hc),
[the baseline denominator exceeds it almost everywhere](hyp:hden), [baseline
shares equal instrument probabilities divided by that denominator](hyp:hshare),
and [all instruments in the level have the common baseline policy value](hyp:hcommon),
then [the covariate expectation of the perturbed pooled level plus its finite
conditional policy residual has derivative zero at zero](goal). -/
lemma binary_pooled_joint_integral_orthogonality_of_admissible
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (eta del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr eta) (.inr del))
    (a : RegularIndex L) (c : ℝ) (hc : 0 < c)
    (hden : ∀ᵐ x ∂xLaw M, c ≤ eta.tauLev a x)
    (hshare : ∀ᵐ x ∂xLaw M, ∀ z ∈ L.T a.val.1 a.val.2,
      eta.share a z x = instProb M z x / eta.tauLev a x)
    (hcommon : ∀ᵐ x ∂xLaw M, ∀ z ∈ L.T a.val.1 a.val.2,
      phi z x (eta.prop z x) = L.qLev a.val.1 a.val.2 x) :
    HasDerivAt (fun t : ℝ => ∫ x,
      pooledQBin phi L (eta + t • del) a.val.1 a.val.2 x +
        ∑ z, instProb M z x * RqBin dphi L (eta + t • del) a.val.1 a.val.2
          (x, z, eta.prop z x, 0) ∂xLaw M) 0 0 := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  obtain ⟨r, hr, hadm⟩ := hd.admissible
  have he : BinAdmissible M L eta := by
    simpa only [binary_nuisance_affine_zero] using hadm 0 (by simpa using hr)
  obtain ⟨B, Lip, hB, hLip, hb⟩ := hDerivative
  have hbound : ∀ z x p, p ∈ Icc (0 : ℝ) 1 → |dphi z x p| ≤ B :=
    fun z x p hp => (hb z x p p hp hp).1
  have hlip : ∀ z x p q, p ∈ Icc (0 : ℝ) 1 → q ∈ Icc (0 : ℝ) 1 →
      |dphi z x p - dphi z x q| ≤ Lip * |p-q| :=
    fun z x p q hp hq => (hb z x p q hp hq).2
  obtain ⟨Ca, _, ha⟩ := binary_simplex_share_direction_regular M L eta del hd
  obtain ⟨Ct, _, ht⟩ := binary_pooled_denominator_direction_regular M L eta del hd
  have hp : ∀ z ∈ L.T a.val.1 a.val.2, MemLp (del.prop z) 2 (xLaw M) :=
    fun z _ => binary_propensity_direction_memLp M L eta del hd z
  have hda : ∀ z ∈ L.T a.val.1 a.val.2, MemLp (del.share a z) 2 (xLaw M) :=
    fun z _ => MemLp.of_bound (ha a z).1.aestronglyMeasurable Ca (ha a z).2
  have hdt : MemLp (del.tauLev a) 2 (xLaw M) :=
    MemLp.of_bound (ht a).1.aestronglyMeasurable Ct (ht a).2
  let F : ℝ → X → ℝ := fun t x =>
    (∑ z ∈ L.T a.val.1 a.val.2,
      (eta.share a z x + t * del.share a z x) * phi z x (eta.prop z x + t * del.prop z x)) -
    t * ((eta.tauLev a x + t * del.tauLev a x)⁻¹ *
      ∑ z ∈ L.T a.val.1 a.val.2, instProb M z x *
        dphi z x (eta.prop z x + t * del.prop z x) * del.prop z x)
  have hlocal : ∀ᶠ t : ℝ in nhds 0, BinAdmissible M L (eta + t • del) := by
    filter_upwards [continuousAt_id.abs.eventually_lt_const (by simpa using hr)] with t ht
    exact hadm t ht
  have hmeas : ∀ᶠ t : ℝ in nhds 0, AEStronglyMeasurable (F t) (xLaw M) := by
    filter_upwards [hlocal] with t het
    let pc : Z → X → ℝ := fun z x => max 0 (min 1 ((eta + t • del).prop z x))
    have hpc : Measurable (fun zx : Z × X => pc zx.1 zx.2) := by
      apply measurable_from_prod_countable_right
      intro z
      have hm := het.2.1 z
      dsimp only [pc]
      fun_prop
    have hpcR : ∀ z x, pc z x ∈ Icc (0 : ℝ) 1 := fun z x =>
      ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
    have hq : Measurable (fun zx : Z × X => phi zx.1 zx.2 (pc zx.1 zx.2)) :=
      hphi.1.comp (measurable_fst.prodMk
        (measurable_snd.prodMk (hpc.subtype_mk (h := fun zx => hpcR zx.1 zx.2))))
    have hdq := policy_derivative_graph_measurable phi dphi hphi hDiff pc hpc hpcR
    have hmshare := het.2.2.2.2.2.2.2.1 a
    have hmtau := (het.2.2.2.2.2.1 a).1
    have hmass (z : Z) : Measurable (instProb M z) :=
      (Kernel.measurable_coe _ (measurableSet_singleton z)).ennreal_toReal
    have hfm : Measurable (fun x =>
        (∑ z ∈ L.T a.val.1 a.val.2, (eta + t • del).share a z x * phi z x (pc z x)) -
        t * (((eta + t • del).tauLev a x)⁻¹ *
          ∑ z ∈ L.T a.val.1 a.val.2, instProb M z x * dphi z x (pc z x) * del.prop z x)) := by
      first
      | fun_prop
      | apply Measurable.sub
        · apply Finset.measurable_sum
          intro z hz
          exact (hmshare z).mul (hq.comp (measurable_const.prodMk measurable_id))
        · apply Measurable.const_mul
          apply hmtau.inv.mul
          apply Finset.measurable_sum
          intro z hz
          exact ((hmass z).mul (hdq.comp (measurable_const.prodMk measurable_id))).mul
            (((binary_propensity_direction_regular M L eta del hd).choose_spec.2 z).1)
    apply hfm.aestronglyMeasurable.congr
    filter_upwards [ae_all_iff.mpr het.1] with x hx
    have hcx (z : Z) : pc z x = eta.prop z x + t * del.prop z x := by
      simp only [pc, min_eq_right (hx z).2, max_eq_right (hx z).1]
      rfl
    simp only [F, hcx]
    rfl
  have hbase : Integrable (fun x => ∑ z ∈ L.T a.val.1 a.val.2,
      eta.share a z x * phi z x (eta.prop z x)) (xLaw M) := by
    have hm := hmeas.self_of_nhds
    have h0 : F 0 = fun x => ∑ z ∈ L.T a.val.1 a.val.2,
        eta.share a z x * phi z x (eta.prop z x) := by
      funext x
      simp only [F, zero_mul, add_zero, sub_zero]
    rw [h0] at hm
    apply Integrable.of_bound hm (L.T a.val.1 a.val.2).card
    filter_upwards [ae_all_iff.mpr he.1,
      ae_all_iff.mpr (he.2.2.2.2.2.2.1 a)] with x hx hs
    rw [Real.norm_eq_abs]
    calc
      _ ≤ ∑ z ∈ L.T a.val.1 a.val.2, |eta.share a z x * phi z x (eta.prop z x)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ z ∈ L.T a.val.1 a.val.2, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro z hz
        have hq := hphi.2 z x (eta.prop z x) (hx z)
        rw [abs_mul, abs_of_nonneg (hs z).1, abs_of_nonneg hq.1]
        exact mul_le_one₀ (hs z).2 hq.1 hq.2
      _ = _ := by simp
  have horigin : ∀ᵐ x ∂xLaw M,
      (∀ z ∈ L.T a.val.1 a.val.2, instProb M z x = eta.share a z x * eta.tauLev a x ∧
        |eta.share a z x| ≤ 1 ∧ eta.prop z x ∈ Icc (0 : ℝ) 1 ∧
        phi z x (eta.prop z x) = L.qLev a.val.1 a.val.2 x) ∧
      ∑ z ∈ L.T a.val.1 a.val.2, del.share a z x = 0 := by
    filter_upwards [hshare, hcommon, hden, ae_all_iff.mpr he.1,
      ae_all_iff.mpr (he.2.2.2.2.2.2.1 a),
      bin_admissible_share_direction M L eta del hd a] with x hs hq ht hp ha hd
    refine ⟨?_, hd⟩
    intro z hz
    refine ⟨?_, ?_, hp z, hq z hz⟩
    · rw [hs z hz, div_mul_cancel₀ _ (ne_of_gt (hc.trans_le ht))]
    · rw [abs_of_nonneg (ha z).1]
      exact (ha z).2
  have hpath : ∀ᶠ t : ℝ in nhds 0, ∀ᵐ x ∂xLaw M,
      c/2 ≤ eta.tauLev a x + t * del.tauLev a x ∧
        ∀ z ∈ L.T a.val.1 a.val.2, eta.prop z x + t * del.prop z x ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [binary_pooled_denominator_uniform_neighborhood M L eta del hd a c hc hden,
      binary_propensity_path_uniform_neighborhood M L eta del hd] with t ht hp
    filter_upwards [ht, ae_all_iff.mpr hp] with x hx hp
    exact ⟨hx, fun z _ => hp z⟩
  have hf := pooled_policy_debiased_joint_integral_orthogonality (xLaw M)
    phi dphi hDiff B Lip hB hLip hbound hlip (L.T a.val.1 a.val.2)
    eta.prop del.prop (eta.share a) (del.share a) (instProb M)
    (L.qLev a.val.1 a.val.2) (eta.tauLev a) (del.tauLev a) (c/2)
    (by positivity) hp hda hdt hbase horigin hpath hmeas
  apply hf.congr_of_eventuallyEq
  apply Eventually.of_forall
  intro t
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  change pooledQBin phi L (eta + t • del) a.val.1 a.val.2 x +
    (∑ z, instProb M z x * RqBin dphi L (eta + t • del) a.val.1 a.val.2
      (x, z, eta.prop z x, 0)) = F t x
  have hj0 : a.val.2 ≠ 0 := by have := a.property; omega
  have hj : ¬ L.l a.val.1 < a.val.2 := not_lt.mpr a.property.2.2
  have hbad : ¬ (a.val.2 = 0 ∨ L.l a.val.1 < a.val.2) := by omega
  rw [RqBin_finite_conditional_mean]
  simp only [pooledQBin, if_neg hj0, if_neg hj, if_neg hbad,
    regularValue, dif_pos a.property]
  change (∑ z ∈ L.T a.val.1 a.val.2,
    (eta.share a z x + t * del.share a z x) * phi z x (eta.prop z x + t * del.prop z x)) +
    (eta.tauLev a x + t * del.tauLev a x)⁻¹ *
      (∑ z ∈ L.T a.val.1 a.val.2, instProb M z x *
        dphi z x (eta.prop z x + t * del.prop z x) *
          (eta.prop z x - (eta.prop z x + t * del.prop z x))) = F t x
  dsimp only [F]
  have hsum : (∑ z ∈ L.T a.val.1 a.val.2, instProb M z x *
      dphi z x (eta.prop z x + t * del.prop z x) *
        (eta.prop z x - (eta.prop z x + t * del.prop z x))) =
      -t * ∑ z ∈ L.T a.val.1 a.val.2, instProb M z x *
        dphi z x (eta.prop z x + t * del.prop z x) * del.prop z x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    ring
  rw [hsum]
  ring

-- At the population nuisance, the normalized-share and common-level premises
-- above are exactly the level construction and invariant-order identities.
-- @node: population_binary_pooled_joint_integral_orthogonality
/-- Suppose [the policy is measurable and probability valued](hyp:hphi),
[has the specified derivative](hyp:hDiff), and [has a uniformly bounded Lipschitz
derivative](hyp:hDerivative). Under [invariant ordering of baseline and policy
levels](hyp:hOrder), [policy overlap with the given constant](hyp:hov), and
[an admissible joint direction at the population nuisance](hyp:hd), [the covariate
expectation of the perturbed pooled level plus its policy residual averaged over
the true instrument distribution and evaluated at true treatment propensities
has derivative zero at zero](goal). -/
lemma population_binary_pooled_joint_integral_orthogonality
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del))
    (a : RegularIndex L) :
    HasDerivAt (fun t : ℝ => ∫ x,
      pooledQBin phi L (eta0Bin M L + t • del) a.val.1 a.val.2 x +
        ∑ z, instProb M z x * RqBin dphi L (eta0Bin M L + t • del) a.val.1 a.val.2
          (x, z, M.prop z x, 0) ∂xLaw M) 0 0 := by
  apply binary_pooled_joint_integral_orthogonality_of_admissible M phi dphi
    hphi hDiff hDerivative L (eta0Bin M L) del hd a cpi hov.1
  · apply Eventually.of_forall
    intro x
    exact hov.2 x a.val.1 a.val.2 a.property.1 a.property.2.1 a.property.2.2
      (ordered_policy_level_nonempty M (policyProp phi M.prop) L hOrder
        a.val.1 a.val.2 a.property.1 a.property.2.1 a.property.2.2)
  · apply Eventually.of_forall
    intro x z hz
    simp only [eta0Bin, levelShares, if_pos hz]
  · apply Eventually.of_forall
    intro x z hz
    exact (hOrder.2.2.2.2.2.2.1 x a.val.1 a.val.2 z a.property.1
      a.property.2.1 a.property.2.2).mp hz

end Papers.TbsPrteOptimalTransport
