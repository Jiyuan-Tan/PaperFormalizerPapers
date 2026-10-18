module
public import Papers.TbsPrteOptimalTransport.Helpers.JointPooledIntegration
public import Papers.TbsPrteOptimalTransport.Helpers.RegularComponentRemainder
/-! Quantitative pooled-policy errors along the entire admissible binary nuisance path. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSimpArgs false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v

-- Split the fitted pooling error into a policy increment and a share increment.
-- This estimate does not require the fitted shares to equal normalized masses.
-- @node: pooled_policy_affine_increment_bound
/-- Suppose [the policy transformations have the proposed derivatives on the unit
interval](hyp:hd), [the derivative bound is nonnegative](hyp:_hB), and [all those
derivatives are bounded in absolute value by that bound](hyp:hbound). If, for the
selected instruments, [the initial propensities lie in the unit interval](hyp:hp),
[the perturbed propensities also lie there](hyp:ht), [the initial pooling weights
have absolute value at most one](hyp:ha), and [the policy values at the perturbed
propensities have absolute value at most one](hyp:hq), then [the absolute change
in the pooled policy sum along the affine propensity and weight paths is at most
the absolute path parameter times the sum of the derivative bound times each
absolute propensity direction plus each absolute weight direction](goal). -/
lemma pooled_policy_affine_increment_bound {X Z : Type v}
    (phi dphi : Z → X → ℝ → ℝ) (hd : PolicyDifferentiable phi dphi)
    (B : ℝ) (_hB : 0 ≤ B)
    (hbound : ∀ z x p, p ∈ Icc (0 : ℝ) 1 → |dphi z x p| ≤ B)
    (s : Finset Z) (x : X) (p dp a da : Z → ℝ) (t : ℝ)
    (hp : ∀ z ∈ s, p z ∈ Icc (0 : ℝ) 1)
    (ht : ∀ z ∈ s, p z + t * dp z ∈ Icc (0 : ℝ) 1)
    (ha : ∀ z ∈ s, |a z| ≤ 1)
    (hq : ∀ z ∈ s, |phi z x (p z + t * dp z)| ≤ 1) :
    |(∑ z ∈ s, (a z + t * da z) * phi z x (p z + t * dp z)) -
      (∑ z ∈ s, a z * phi z x (p z))| ≤
      |t| * ∑ z ∈ s, (B * |dp z| + |da z|) := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro z hz
  have hi : |phi z x (p z + t * dp z) - phi z x (p z)| ≤
      B * (|t| * |dp z|) := by
    simpa only [add_sub_cancel_left, abs_mul] using
      policy_bounded_derivative_increment (phi z x) (dphi z x) B (p z)
        (p z + t * dp z) (hp z hz) (ht z hz) (hd z x) (hbound z x)
  have heq : (a z + t * da z) * phi z x (p z + t * dp z) -
      a z * phi z x (p z) =
      a z * (phi z x (p z + t * dp z) - phi z x (p z)) +
        t * da z * phi z x (p z + t * dp z) := by ring
  rw [heq]
  calc
    _ ≤ |a z| * |phi z x (p z + t * dp z) - phi z x (p z)| +
        |t| * |da z| * |phi z x (p z + t * dp z)| := by
      simpa only [abs_mul] using abs_add_le
        (a z * (phi z x (p z + t * dp z) - phi z x (p z)))
        (t * da z * phi z x (p z + t * dp z))
    _ ≤ 1 * (B * (|t| * |dp z|)) + |t| * |da z| * 1 := by
      gcongr
      · exact ha z hz
      · exact hq z hz
    _ = _ := by ring

variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- This supplies the upper/lower policy residual envelopes needed by the
-- regular-component bias bound. Its coefficients depend only on L2 directions.
-- @node: population_binary_pooled_path_quadratic_envelope
/-- Suppose [the policy transformations have the proposed derivatives on the unit
interval](hyp:hDiff), [the derivative bound is nonnegative](hyp:hB), [the Lipschitz
constant is nonnegative](hyp:hLip), [the derivatives are uniformly bounded by the
derivative bound](hyp:hbound), and [their changes are bounded by the Lipschitz
constant times the propensity change](hyp:hlip). Under [the invariant ordering of
baseline and transformed policy levels](hyp:hOrder), [positive uniform policy-class
overlap](hyp:hov), and [an admissible direction at the true binary nuisance
functions](hyp:hd), [the sum over the selected regular policy class of the Lipschitz
constant times squared propensity directions, the derivative bound times absolute
share–propensity direction products, and twice the derivative bound divided by
the overlap constant times absolute denominator–propensity direction products is
integrable; for all sufficiently small path parameters, this sum times the squared
parameter almost surely bounds the absolute change in the pooled policy value
plus its instrument-averaged propensity residual correction](goal). -/
lemma population_binary_pooled_path_quadratic_envelope
    (phi dphi : Z → X → ℝ → ℝ) (hDiff : PolicyDifferentiable phi dphi)
    (B Lip : ℝ) (hB : 0 ≤ B) (hLip : 0 ≤ Lip)
    (hbound : ∀ z x p, p ∈ Icc (0 : ℝ) 1 → |dphi z x p| ≤ B)
    (hlip : ∀ z x p q, p ∈ Icc (0 : ℝ) 1 → q ∈ Icc (0 : ℝ) 1 →
      |dphi z x p - dphi z x q| ≤ Lip * |p - q|)
    (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del))
    (a : RegularIndex L) :
    let E := fun x => ∑ z ∈ L.T a.val.1 a.val.2,
      (Lip * (del.prop z x)^2 + B * |del.share a z x * del.prop z x| +
        (B/(cpi/2)) * |del.tauLev a x * del.prop z x|)
    Integrable E (xLaw M) ∧
    ∀ᶠ t : ℝ in nhds 0, ∀ᵐ x ∂xLaw M,
      |pooledQBin phi L (eta0Bin M L + t • del) a.val.1 a.val.2 x +
        (∑ z, instProb M z x * RqBin dphi L (eta0Bin M L + t • del)
          a.val.1 a.val.2 (x,z,M.prop z x,0)) -
        pooledQBin phi L (eta0Bin M L) a.val.1 a.val.2 x| ≤ E x * t^2 := by
  dsimp only
  have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  have he := binary_admissible_direction_origin M L (eta0Bin M L) del hd
  obtain ⟨Ca, _, ha⟩ := binary_simplex_share_direction_regular M L (eta0Bin M L) del hd
  obtain ⟨Ct, _, ht⟩ := binary_pooled_denominator_direction_regular M L (eta0Bin M L) del hd
  have hden : ∀ᵐ x ∂xLaw M, cpi ≤ (eta0Bin M L).tauLev a x := by
    apply Eventually.of_forall
    intro x
    exact hov.2 x a.val.1 a.val.2 a.property.1 a.property.2.1 a.property.2.2
      (ordered_policy_level_nonempty M (policyProp phi M.prop) L hOrder
        a.val.1 a.val.2 a.property.1 a.property.2.1 a.property.2.2)
  refine ⟨?_, ?_⟩
  · apply pooled_policy_joint_L2_envelope_integrable
    · intro z _
      exact binary_propensity_direction_memLp M L (eta0Bin M L) del hd z
    · intro z _
      exact MemLp.of_bound (ha a z).1.aestronglyMeasurable Ca (ha a z).2
    · exact MemLp.of_bound (ht a).1.aestronglyMeasurable Ct (ht a).2
  · filter_upwards [binary_pooled_denominator_uniform_neighborhood M L
      (eta0Bin M L) del hd a cpi hov.1 hden,
      binary_propensity_path_uniform_neighborhood M L (eta0Bin M L) del hd]
        with t hdt hp
    filter_upwards [hden, hdt, ae_all_iff.mpr hp,
      ae_all_iff.mpr (he.2.2.2.2.2.2.1 a),
      bin_admissible_share_direction M L (eta0Bin M L) del hd a]
        with x hx htx hpx hax hsimplex
    have hshare : ∀ z ∈ L.T a.val.1 a.val.2,
        (eta0Bin M L).share a z x = instProb M z x / (eta0Bin M L).tauLev a x := by
      intro z hz
      simp only [eta0Bin, levelShares, if_pos hz]
    have hcommon : ∀ z ∈ L.T a.val.1 a.val.2,
        phi z x ((eta0Bin M L).prop z x) = L.qLev a.val.1 a.val.2 x := by
      intro z hz
      exact (hOrder.2.2.2.2.2.2.1 x a.val.1 a.val.2 z a.property.1
        a.property.2.1 a.property.2.2).mp hz
    have hb := pooledQBin_joint_conditional_remainder_bound phi dphi hDiff B Lip hB hLip
      hbound hlip L (eta0Bin M L) del a x (fun z => instProb M z x) t (cpi/2)
      (by have := hov.1; positivity) (ne_of_gt (hov.1.trans_le hx)) htx hshare
      (fun z _ => M.rangeProp z x) (fun z _ => hpx z) hcommon hsimplex
    have hE := pooled_policy_joint_remainder_envelope_le (L.T a.val.1 a.val.2)
      (fun z => (eta0Bin M L).share a z x) (fun z => del.share a z x)
      (fun z => del.prop z x) (del.tauLev a x) B Lip (cpi/2) hB hLip
      (by have := hov.1; positivity) (fun z _ => by
        rw [abs_of_nonneg (hax z).1]; exact (hax z).2)
    exact hb.trans (mul_le_mul_of_nonneg_right hE (sq_nonneg t))

-- Uniform control is available because admissibility bounds the whole affine
-- direction. It supplies the branch-error envelope without a new assumption.
-- @node: population_binary_pooled_path_increment_bound
/-- If [the policy transformations are measurable and map unit-interval
propensities into the unit interval](hyp:hphi), [they have the proposed derivatives
there](hyp:hDiff), [those derivatives are uniformly bounded and Lipschitz](hyp:hDerivative),
and [the nuisance direction is admissible at the true binary nuisance functions](hyp:hd),
then [there exists a nonnegative constant such that, for every sufficiently small
path parameter and almost every covariate value, the absolute change in the
selected regular pooled policy value along the full affine nuisance path is at
most that constant times the absolute parameter](goal). -/
lemma population_binary_pooled_path_increment_bound
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del))
    (a : RegularIndex L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t : ℝ in nhds 0, ∀ᵐ x ∂xLaw M,
      |pooledQBin phi L (eta0Bin M L + t • del) a.val.1 a.val.2 x -
        pooledQBin phi L (eta0Bin M L) a.val.1 a.val.2 x| ≤ C * |t| := by
  obtain ⟨B, Lip, hB, hLip, hb⟩ := hDerivative
  obtain ⟨Cp, hCp, hp⟩ := binary_propensity_direction_regular M L (eta0Bin M L) del hd
  obtain ⟨Cs, hCs, hs⟩ := binary_simplex_share_direction_regular M L (eta0Bin M L) del hd
  have he := binary_admissible_direction_origin M L (eta0Bin M L) del hd
  refine ⟨(L.T a.val.1 a.val.2).card * (B*Cp + Cs), by positivity, ?_⟩
  filter_upwards [binary_propensity_path_uniform_neighborhood M L (eta0Bin M L) del hd]
    with t ht
  filter_upwards [ae_all_iff.mpr ht, ae_all_iff.mpr (fun z => (hp z).2),
    ae_all_iff.mpr (fun z => (hs a z).2), ae_all_iff.mpr (he.2.2.2.2.2.2.1 a)]
      with x htx hpx hsx hax
  have hbq := pooled_policy_affine_increment_bound phi dphi hDiff B hB
    (fun z x p hp => (hb z x p p hp hp).1) (L.T a.val.1 a.val.2) x
    (fun z => M.prop z x) (fun z => del.prop z x)
    (fun z => (eta0Bin M L).share a z x) (fun z => del.share a z x) t
    (fun z _ => M.rangeProp z x) (fun z _ => htx z)
    (fun z _ => by rw [abs_of_nonneg (hax z).1]; exact (hax z).2)
    (fun z _ => by
      have hr := hphi.2 z x (M.prop z x + t * del.prop z x) (htx z)
      rw [abs_of_nonneg hr.1]; exact hr.2)
  have hsum : (∑ z ∈ L.T a.val.1 a.val.2,
      (B * |del.prop z x| + |del.share a z x|)) ≤
      (L.T a.val.1 a.val.2).card * (B*Cp + Cs) := by
    calc
      _ ≤ ∑ z ∈ L.T a.val.1 a.val.2, (B*Cp + Cs) := by
        apply Finset.sum_le_sum
        intro z _
        have hpz : |del.prop z x| ≤ Cp := by simpa only [Real.norm_eq_abs] using hpx z
        have hsz : |del.share a z x| ≤ Cs := by simpa only [Real.norm_eq_abs] using hsx z
        exact add_le_add (mul_le_mul_of_nonneg_left hpz hB) hsz
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hj0 : a.val.2 ≠ 0 := by have := a.property; omega
  have hj : ¬ L.l a.val.1 < a.val.2 := not_lt.mpr a.property.2.2
  simp only [pooledQBin, if_neg hj0, if_neg hj, regularValue, dif_pos a.property]
  exact hbq.trans (by simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left hsum (abs_nonneg t))

-- The fixed lower policy boundary is q_0 = p_k; there is no pooled residual
-- at index zero. The remaining centering error is a denominator-error product.
-- @node: binary_lower_boundary_centering_error
/-- If [the overlap bound is positive](hyp:hc) and [the fitted baseline-class
probability is at least that bound whenever the boundary level is a valid positive
level](hyp:hpi), then [the absolute sum of the reference-probability-weighted
reference-minus-fitted baseline propensity difference divided by the fitted class
probability, the instrument-averaged lower-boundary policy residual, and the
fitted-minus-reference pooled lower boundary is at most the product of the absolute
class-probability error and absolute baseline propensity error divided by the
overlap bound](goal). -/
lemma binary_lower_boundary_centering_error
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e0 e : NuisanceBin L) (k : ℕ) (x : X) (c : ℝ) (hc : 0 < c)
    (hpi : 1 ≤ k ∧ k ≤ L.K → c ≤ positiveValue e.piLev k x) :
    |positiveValue e0.piLev k x *
        (positiveValue e0.pLev k x - positiveValue e.pLev k x) / positiveValue e.piLev k x +
      (∑ z, instProb M z x * RqBin dphi L e k 0 (x,z,M.prop z x,0)) +
      (pooledQBin phi L e k 0 x - pooledQBin phi L e0 k 0 x)| ≤
      |positiveValue e.piLev k x - positiveValue e0.piLev k x| *
        |positiveValue e.pLev k x - positiveValue e0.pLev k x| / c := by
  simp only [RqBin, true_or, if_true, mul_zero, Finset.sum_const_zero,
    pooledQBin, add_zero]
  by_cases hk : 1 ≤ k ∧ k ≤ L.K
  · exact fitted_ipw_residual_centering_error hc (hpi hk)
  · simp only [positiveValue, dif_neg hk, sub_self, mul_zero, zero_div,
      add_zero, abs_zero, zero_mul]
    exact le_rfl

-- Specialize the error product to the simultaneous affine path, keeping the
-- structural zero convention. This is the EL envelope when j = 1.
-- @node: binary_lower_boundary_affine_centering_error
/-- If [the overlap bound is positive](hyp:hc) and [the baseline-class probability
along the affine nuisance path is at least that bound whenever the boundary level
is a valid positive level](hyp:hpi), then [the absolute sum of the reference class
probability times the reference-minus-path baseline propensity difference divided
by the path's class probability, the instrument-averaged lower-boundary policy
residual, and the path-minus-reference pooled lower boundary is at most the absolute
product of the class-probability and baseline propensity directions divided by the
overlap bound, times the squared path parameter](goal). -/
lemma binary_lower_boundary_affine_centering_error
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e0 del : NuisanceBin L) (k : ℕ) (x : X) (c t : ℝ) (hc : 0 < c)
    (hpi : 1 ≤ k ∧ k ≤ L.K → c ≤ positiveValue (e0 + t • del).piLev k x) :
    |positiveValue e0.piLev k x *
        (positiveValue e0.pLev k x - positiveValue (e0 + t • del).pLev k x) /
          positiveValue (e0 + t • del).piLev k x +
      (∑ z, instProb M z x * RqBin dphi L (e0 + t • del) k 0 (x,z,M.prop z x,0)) +
      (pooledQBin phi L (e0 + t • del) k 0 x - pooledQBin phi L e0 k 0 x)| ≤
      (|positiveValue del.piLev k x * positiveValue del.pLev k x| / c) * t^2 := by
  have hb := binary_lower_boundary_centering_error M phi dphi L e0 (e0 + t • del)
    k x c hc hpi
  apply hb.trans
  by_cases hk : 1 ≤ k ∧ k ≤ L.K
  · simp only [positiveValue, dif_pos hk]
    change |(e0.piLev ⟨k,hk⟩ x + t * del.piLev ⟨k,hk⟩ x) - e0.piLev ⟨k,hk⟩ x| *
      |(e0.pLev ⟨k,hk⟩ x + t * del.pLev ⟨k,hk⟩ x) - e0.pLev ⟨k,hk⟩ x| / c ≤ _
    simp only [add_sub_cancel_left, abs_mul]
    rw [← sq_abs t]
    exact le_of_eq (by ring)
  · simp only [positiveValue, dif_neg hk, sub_self, abs_zero, zero_mul,
      zero_div, mul_zero]
    exact le_rfl

end Papers.TbsPrteOptimalTransport
