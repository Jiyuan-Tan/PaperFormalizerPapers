module
public import Papers.TbsPrteOptimalTransport.Helpers.RegressionPathEnvelopes
/-! Joint regression and policy residual envelopes, including the fixed lower boundary. -/
public section
set_option maxHeartbeats 800000
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

-- The denominator and propensity directions are bounded by admissibility.
-- Thus the structural lower boundary needs no extra integrability premise.
-- @node: population_binary_lower_boundary_path_quadratic_envelope
/-- Under [baseline overlap with constant cpi](hyp:hov) and [an admissible joint
direction at the population nuisance](hyp:hd), [the absolute product of the
assignment-probability and level-propensity directions, divided by half cpi, is
an integrable envelope whose product with the squared path parameter bounds the
absolute sum of the lower-boundary treatment residual, finite conditional policy
residual, and pooled-boundary increment, almost everywhere throughout a
neighborhood of zero](goal). -/
lemma population_binary_lower_boundary_path_quadratic_envelope
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del)) (k : ℕ) :
    let E := fun x => |positiveValue del.piLev k x * positiveValue del.pLev k x| / (cpi/2)
    Integrable E (xLaw M) ∧
    ∀ᶠ t : ℝ in nhds 0, ∀ᵐ x ∂xLaw M,
      let e := eta0Bin M L + t • del
      |positiveValue (eta0Bin M L).piLev k x *
          (positiveValue (eta0Bin M L).pLev k x - positiveValue e.pLev k x) /
            positiveValue e.piLev k x +
        (∑ z, instProb M z x * RqBin dphi L e k 0 (x,z,M.prop z x,0)) +
        (pooledQBin phi L e k 0 x - pooledQBin phi L (eta0Bin M L) k 0 x)| ≤ E x * t^2 := by
  dsimp only
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  obtain ⟨C, hC, hden⟩ := binary_assignment_denominator_direction_regular M L
    (eta0Bin M L) del hd
  obtain ⟨P, hP, hprop⟩ := binary_baseline_propensity_direction_regular M L
    (eta0Bin M L) del hd
  have hD := binary_positive_regression_direction_regular (M := M) L del.piLev C hC hden k
  have hV := binary_positive_regression_direction_regular (M := M) L del.pLev P hP hprop k
  have hc : 0 < cpi/2 := by have := hov.1; positivity
  constructor
  · have hm : Measurable (fun x =>
        |positiveValue del.piLev k x * positiveValue del.pLev k x| / (cpi/2)) := by
      first | fun_prop | exact (hD.1.mul hV.1).abs.div_const _
    apply Integrable.of_bound hm.aestronglyMeasurable (C*P/(cpi/2))
    filter_upwards [hD.2, hV.2] with x hx hy
    simp only [Real.norm_eq_abs] at hx hy ⊢
    rw [abs_of_nonneg (by positivity), abs_mul]
    exact div_le_div_of_nonneg_right (mul_le_mul hx hy (abs_nonneg _) hC) hc.le
  · filter_upwards [binary_assignment_denominators_uniform_neighborhood M L cpi hov del hd]
      with t ht
    filter_upwards [ae_all_iff.mpr ht] with x hx
    exact binary_lower_boundary_affine_centering_error M phi dphi L (eta0Bin M L) del
      k x (cpi/2) t hc (fun hi => by
        simpa only [positiveValue, dif_pos hi] using hx ⟨k,hi⟩)

-- The same statement covers a pooled lower boundary and q_0 = p_k.
-- @node: population_binary_regular_lower_residual_path_envelope
/-- Suppose [the policy has the specified derivative](hyp:hDiff) and [a uniformly
bounded Lipschitz derivative](hyp:hDerivative), [baseline and policy levels have
invariant ordering](hyp:hOrder), [baseline overlap](hyp:hov) and [policy overlap](hyp:hpol)
hold with the given constant, and [the joint direction at the population
nuisance is admissible](hyp:hd). For [a baseline level index at most the number
of levels](hyp:hk) and [a regular interval](hyp:hj), [there is an integrable
envelope bounding, almost everywhere near zero, the absolute sum of the
lower-boundary propensity residual when the interval is first, the finite
conditional lower policy residual, and the lower pooled-boundary increment by
the envelope times the squared path parameter](goal). -/
lemma population_binary_regular_lower_residual_path_envelope
    (phi dphi : Z → X → ℝ → ℝ) (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi) (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del))
    (k j : ℕ) (hk : k ≤ L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    ∃ E : X → ℝ, Integrable E (xLaw M) ∧
      ∀ᶠ t : ℝ in nhds 0, ∀ᵐ x ∂xLaw M,
        let e := eta0Bin M L + t • del
        let rp := positiveValue (eta0Bin M L).piLev k x *
          (positiveValue (eta0Bin M L).pLev k x - positiveValue e.pLev k x) /
            positiveValue e.piLev k x
        |(if j = 1 then rp else 0) +
          (∑ z, instProb M z x * RqBin dphi L e k (j-1) (x,z,M.prop z x,0)) +
          (pooledQBin phi L e k (j-1) x - pooledQBin phi L (eta0Bin M L) k (j-1) x)| ≤
          E x * t^2 := by
  by_cases hj1 : j = 1
  · subst j
    obtain ⟨hi, hb⟩ := population_binary_lower_boundary_path_quadratic_envelope M
      phi dphi L cpi hov del hd k
    refine ⟨_, hi, ?_⟩
    simpa only [Nat.sub_self, if_true] using hb
  · obtain ⟨B, Lip, hB, hLip, hb⟩ := hDerivative
    let a : RegularIndex L := ⟨(k,j-1), hk, by omega, by change j-1 ≤ L.l k; omega⟩
    obtain ⟨hi, hq⟩ := population_binary_pooled_path_quadratic_envelope M phi dphi hDiff
      B Lip hB hLip (fun z x p hp => (hb z x p p hp hp).1)
      (fun z x p q hp hq => (hb z x p q hp hq).2) L hOrder cpi hpol del hd a
    refine ⟨_, hi, ?_⟩
    filter_upwards [hq] with t ht
    filter_upwards [ht] with x hx
    dsimp only [a] at hx
    dsimp only
    rw [if_neg hj1, zero_add]
    convert hx using 1
    congr 1
    ring

-- Assemble the three errors used in the six-correction branch expansion.
-- All envelopes are derived, and their shared neighborhood permits simultaneous
-- regression, propensity, assignment, pooled-denominator, and share directions.
-- @node: population_binary_regular_residual_path_envelopes
/-- Suppose [the policy has the specified derivative](hyp:hDiff) with [a uniformly
bounded Lipschitz derivative](hyp:hDerivative), [baseline and policy levels have
invariant ordering](hyp:hOrder), [baseline overlap](hyp:hov) and [policy overlap](hyp:hpol)
hold, and [the population nuisance direction is admissible](hyp:hd). For [a
baseline level index at most the number of levels](hyp:hk) and [a regular
interval](hyp:hj), [three integrable envelopes simultaneously bound, almost
everywhere near zero and after multiplication by the squared path parameter,
the absolute regression residual combination minus its corresponding argument
increment, the upper conditional policy residual plus its boundary increment,
and the lower conditional policy residual plus its boundary increment and the
lower propensity residual when the interval is first](goal). -/
lemma population_binary_regular_residual_path_envelopes
    (phi dphi : Z → X → ℝ → ℝ) (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi) (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del))
    (k j : ℕ) (hk : k ≤ L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    ∃ EB EQ EL : X → ℝ,
      Integrable EB (xLaw M) ∧ Integrable EQ (xLaw M) ∧ Integrable EL (xLaw M) ∧
      ∀ᶠ t : ℝ in nhds 0, ∀ᵐ x ∂xLaw M,
        let e := eta0Bin M L + t • del
        let rP := fun i => positiveValue (eta0Bin M L).piLev i x *
          (positiveValue (eta0Bin M L).P1 i x - positiveValue e.P1 i x) /
            positiveValue e.piLev i x
        let rp := fun i => positiveValue (eta0Bin M L).piLev i x *
          (positiveValue (eta0Bin M L).pLev i x - positiveValue e.pLev i x) /
            positiveValue e.piLev i x
        let Q := fun i => ∑ z, instProb M z x * RqBin dphi L e k i (x,z,M.prop z x,0)
        |(rP (k+1) - rP k - rp (k+1)) -
          ((positiveValue e.pLev (k+1) x - binFullJ L e k x) -
            (positiveValue (eta0Bin M L).pLev (k+1) x -
              binFullJ L (eta0Bin M L) k x))| ≤ EB x * t^2 ∧
        |Q j + (pooledQBin phi L e k j x - pooledQBin phi L (eta0Bin M L) k j x)| ≤ EQ x * t^2 ∧
        |(if j = 1 then rp k else 0) + Q (j-1) +
          (pooledQBin phi L e k (j-1) x - pooledQBin phi L (eta0Bin M L) k (j-1) x)| ≤
          EL x * t^2 := by
  obtain ⟨iB, hB⟩ := population_binary_regression_path_quadratic_envelope M L cpi hov del hd k
  have hder := hDerivative
  obtain ⟨B, Lip, hBp, hLip, hb⟩ := hder
  let a : RegularIndex L := ⟨(k,j), hk, hj⟩
  obtain ⟨iQ, hQ⟩ := population_binary_pooled_path_quadratic_envelope M phi dphi hDiff
    B Lip hBp hLip (fun z x p hp => (hb z x p p hp hp).1)
    (fun z x p q hp hq => (hb z x p q hp hq).2) L hOrder cpi hpol del hd a
  obtain ⟨EL, iL, hL⟩ := population_binary_regular_lower_residual_path_envelope M
    phi dphi hDiff hDerivative L hOrder cpi hov hpol del hd k j hk hj
  refine ⟨_, _, EL, iB, iQ, iL, ?_⟩
  filter_upwards [hB, hQ, hL] with t htB htQ htL
  filter_upwards [htB, htQ, htL] with x hxB hxQ hxL
  refine ⟨hxB, ?_, hxL⟩
  dsimp only [a] at hxQ
  convert hxQ using 1
  congr 1
  ring


-- One common linear envelope controls every affine argument of the two maxima.
-- @node: population_binary_regular_arguments_path_increment_bound
/-- Suppose [the policy is measurable and probability valued](hyp:hphi), [has
the specified derivative](hyp:hDiff), and [has a uniformly bounded Lipschitz
derivative](hyp:hDerivative), and [the joint direction at the population nuisance
is admissible](hyp:hd). For [a baseline level index strictly below the number
of levels](hyp:hk) and [a regular interval](hyp:hj), [one finite nonnegative
constant bounds the absolute increments of both pooled boundaries and of the
upper level propensity minus the adjacent treated-outcome contrast by that
constant times the absolute path parameter, almost everywhere near zero](goal). -/
lemma population_binary_regular_arguments_path_increment_bound
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del))
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t : ℝ in nhds 0, ∀ᵐ x ∂xLaw M,
      let e := eta0Bin M L + t • del
      |pooledQBin phi L e k j x - pooledQBin phi L (eta0Bin M L) k j x| ≤ C * |t| ∧
      |pooledQBin phi L e k (j-1) x - pooledQBin phi L (eta0Bin M L) k (j-1) x| ≤ C * |t| ∧
      |(positiveValue e.pLev (k+1) x - binFullJ L e k x) -
        (positiveValue (eta0Bin M L).pLev (k+1) x - binFullJ L (eta0Bin M L) k x)| ≤
        C * |t| := by
  obtain ⟨Cq, hCq, hq⟩ := population_binary_pooled_boundary_path_increment_bound M
    phi dphi hphi hDiff hDerivative L del hd k j hk.le hj.2
  obtain ⟨Cl, hCl, hl⟩ := population_binary_pooled_boundary_path_increment_bound M
    phi dphi hphi hDiff hDerivative L del hd k (j-1) hk.le (by omega)
  obtain ⟨Cp, hCp, hp⟩ := binary_baseline_propensity_direction_regular M L
    (eta0Bin M L) del hd
  obtain ⟨CR, hCR, hR⟩ := binary_regression_direction_regular M L (eta0Bin M L) del hd
  have hp' := binary_positive_regression_direction_regular (M := M) L del.pLev Cp hCp hp (k+1)
  have hRplus := binary_positive_regression_direction_regular (M := M) L del.P1 CR hCR hR (k+1)
  have hRminus := binary_positive_regression_direction_regular (M := M) L del.P1 CR hCR hR k
  refine ⟨Cq + Cl + (Cp + CR + CR), by positivity, ?_⟩
  filter_upwards [hq, hl] with t hqt hlt
  filter_upwards [hqt, hlt, hp'.2, hRplus.2, hRminus.2] with x hqx hlx hpx hRx hRm
  have hv (d e : PositiveIndex L.K → X → ℝ) (i : ℕ) :
      positiveValue (fun a x => e a x + t * d a x) i x - positiveValue e i x =
        t * positiveValue d i x := by
    unfold positiveValue
    split_ifs <;> ring
  have hbid : (positiveValue (eta0Bin M L + t • del).pLev (k+1) x -
      binFullJ L (eta0Bin M L + t • del) k x) -
      (positiveValue (eta0Bin M L).pLev (k+1) x - binFullJ L (eta0Bin M L) k x) =
      t * (positiveValue del.pLev (k+1) x - positiveValue del.P1 (k+1) x +
        positiveValue del.P1 k x) := by
    unfold binFullJ
    have hpv := hv del.pLev (eta0Bin M L).pLev (k+1)
    have hrv := hv del.P1 (eta0Bin M L).P1 (k+1)
    have hrm := hv del.P1 (eta0Bin M L).P1 k
    change positiveValue (fun a x => (eta0Bin M L).pLev a x + t * del.pLev a x) (k+1) x -
      (positiveValue (fun a x => (eta0Bin M L).P1 a x + t * del.P1 a x) (k+1) x -
        positiveValue (fun a x => (eta0Bin M L).P1 a x + t * del.P1 a x) k x) - _ = _
    linarith
  have hb : |(positiveValue (eta0Bin M L + t • del).pLev (k+1) x -
      binFullJ L (eta0Bin M L + t • del) k x) -
      (positiveValue (eta0Bin M L).pLev (k+1) x - binFullJ L (eta0Bin M L) k x)| ≤
      (Cp + CR + CR) * |t| := by
    rw [hbid, abs_mul]
    have hb' := (abs_add_le (positiveValue del.pLev (k+1) x -
      positiveValue del.P1 (k+1) x) (positiveValue del.P1 k x)).trans
      (add_le_add (abs_sub _ _) le_rfl)
    have hb'' : |positiveValue del.pLev (k+1) x - positiveValue del.P1 (k+1) x +
        positiveValue del.P1 k x| ≤ Cp + CR + CR := by
      simp only [Real.norm_eq_abs] at hpx hRx hRm
      linarith
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb'' (abs_nonneg t)
  refine ⟨?_, ?_, ?_⟩
  · exact hqx.trans (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg t))
  · exact hlx.trans (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg t))
  · exact hb.trans (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg t))

-- Apply the paper's separated-branch bound only after debiasing all six terms.
-- The resulting envelope is integrable and independent of the path parameter.
-- @node: population_binary_regular_mean_path_quadratic_envelope
/-- Suppose [the policy is measurable and probability valued](hyp:hphi), [has
the specified derivative](hyp:hDiff), and [has a uniformly bounded Lipschitz
derivative](hyp:hDerivative), with [invariant ordering of baseline and policy
levels](hyp:hOrder), [baseline overlap](hyp:hov), [policy overlap](hyp:hpol), and
[an admissible joint population nuisance direction](hyp:hd). For [a baseline
level index strictly below the number of levels](hyp:hk) and [a regular
interval](hyp:hj), assume [the separation constant is positive](hyp:hsep) and
[almost everywhere the upper-minus-lower pooled boundary and the distances of
the upper propensity minus the treated-outcome contrast from both boundaries
are at least that constant](hyp:hgap). Then [an integrable envelope times the
squared path parameter bounds the absolute fitted hinge plus regression and
policy mean corrections minus the population hinge, almost everywhere near
zero](goal). -/
lemma population_binary_regular_mean_path_quadratic_envelope
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi) (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del))
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (sep : ℝ) (hsep : 0 < sep)
    (hgap : ∀ᵐ x ∂xLaw M,
      sep ≤ pooledQBin phi L (eta0Bin M L) k j x -
        pooledQBin phi L (eta0Bin M L) k (j-1) x ∧
      sep ≤ |positiveValue (eta0Bin M L).pLev (k+1) x - binFullJ L (eta0Bin M L) k x -
        pooledQBin phi L (eta0Bin M L) k (j-1) x| ∧
      sep ≤ |positiveValue (eta0Bin M L).pLev (k+1) x - binFullJ L (eta0Bin M L) k x -
        pooledQBin phi L (eta0Bin M L) k j x|) :
    ∃ E : X → ℝ, Integrable E (xLaw M) ∧
      ∀ᶠ t : ℝ in nhds 0, ∀ᵐ x ∂xLaw M,
        let e := eta0Bin M L + t • del
        |hMinus phi L e k j x + binaryRegularRegressionMean phi L (eta0Bin M L) e k j x +
          binaryRegularPolicyMean M phi dphi L e k j x - hMinus phi L (eta0Bin M L) k j x| ≤
          E x * t^2 := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  obtain ⟨EB, EQ, EL, iB, iQ, iL, hres⟩ := population_binary_regular_residual_path_envelopes M
    phi dphi hDiff hDerivative L hOrder cpi hov hpol del hd k j hk.le hj
  obtain ⟨C, hC, herr⟩ := population_binary_regular_arguments_path_increment_bound M
    phi dphi hphi hDiff hDerivative L del hd k j hk hj
  refine ⟨fun x => (26 / sep) * C^2 + EB x + EQ x + EL x,
    (((integrable_const _).fun_add iB).fun_add iQ).fun_add iL, ?_⟩
  filter_upwards [hres, herr] with t htR htE
  filter_upwards [hgap, htR, htE] with x hxG hxR hxE
  have hb := binary_regular_component_mean_remainder_bound M phi dphi L (eta0Bin M L)
    (eta0Bin M L + t • del) k j x (C * |t|) sep (EB x * t^2) (EQ x * t^2)
    (EL x * t^2) hsep hxG.1 hxG.2.1 hxG.2.2 hxE.1 hxE.2.1 hxE.2.2
    hxR.1 hxR.2.1 hxR.2.2
  refine hb.trans (le_of_eq ?_)
  rw [mul_pow, sq_abs]
  ring

-- The tower identity is applied to the fitted score before the quadratic bound.
-- This leaves only the product-weight/hinge interaction for product assembly.
-- @node: population_binary_regular_component_joint_bias_orthogonality
/-- Under [the threshold-crossing model](hyp:h) with [almost surely binary
outcomes](hyp:hy), suppose [the policy is measurable and probability valued](hyp:hphi),
[has the specified derivative](hyp:hDiff), and [has a uniformly bounded Lipschitz
derivative](hyp:hDerivative). Assume [invariant baseline and policy level
ordering](hyp:hOrder), [baseline overlap](hyp:hov), [policy overlap](hyp:hpol),
and [an admissible joint direction at the population nuisance](hyp:hd). For [a
baseline level index strictly below the number of levels](hyp:hk) and [a regular
interval](hyp:hj), if [the separation constant is positive](hyp:hsep) and [almost
everywhere the pooled boundary gap and the distances of the upper propensity
minus the treated-outcome contrast from both boundaries exceed or equal that
constant](hyp:hgap), then [the fitted product weight times the difference between
the component score and the population hinge is integrable near zero, and its observation
expectation has derivative zero at zero](goal). -/
lemma population_binary_regular_component_joint_bias_orthogonality
    (h : ThresholdCrossing M) (hy : OutcomeBinaryAE M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi) (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del))
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (sep : ℝ) (hsep : 0 < sep)
    (hgap : ∀ᵐ x ∂xLaw M,
      sep ≤ pooledQBin phi L (eta0Bin M L) k j x -
        pooledQBin phi L (eta0Bin M L) k (j-1) x ∧
      sep ≤ |positiveValue (eta0Bin M L).pLev (k+1) x - binFullJ L (eta0Bin M L) k x -
        pooledQBin phi L (eta0Bin M L) k (j-1) x| ∧
      sep ≤ |positiveValue (eta0Bin M L).pLev (k+1) x - binFullJ L (eta0Bin M L) k x -
        pooledQBin phi L (eta0Bin M L) k j x|) :
    let F := fun (t : ℝ) (o : Obs X Z) =>
      regularValue (eta0Bin M L + t • del).gamma k j o.1 *
        (binScoreComponents phi dphi L (eta0Bin M L + t • del) k j o -
          hMinus phi L (eta0Bin M L) k j o.1)
    (∀ᶠ t : ℝ in nhds 0, Integrable (F t) (observationLaw M)) ∧
      HasDerivAt (fun t : ℝ => ∫ o, F t o ∂observationLaw M) 0 0 := by
  dsimp only
  let F := fun (t : ℝ) (o : Obs X Z) =>
    regularValue (eta0Bin M L + t • del).gamma k j o.1 *
      (binScoreComponents phi dphi L (eta0Bin M L + t • del) k j o -
        hMinus phi L (eta0Bin M L) k j o.1)
  obtain ⟨E, iE, hE⟩ := population_binary_regular_mean_path_quadratic_envelope M
    phi dphi hphi hDiff hDerivative L hOrder cpi hov hpol del hd k j hk hj sep hsep hgap
  have hobs := M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
  have hmap : (observationLaw M).map Prod.fst = xLaw M := by
    simpa only [observationLaw, xLaw, Function.comp_def] using
      Measure.map_map measurable_fst hobs
  have iEO : Integrable (fun o : Obs X Z => |E o.1|) (observationLaw M) := by
    have ie : Integrable (fun x => |E x|) ((observationLaw M).map Prod.fst) := by
      rw [hmap]
      exact iE.abs
    exact (integrable_map_measure ie.aestronglyMeasurable measurable_fst.aemeasurable).mp ie
  have he0 := binary_admissible_direction_origin M L (eta0Bin M L) del hd
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  have hlocal : ∀ᶠ t : ℝ in nhds 0, Integrable (F t) (observationLaw M) ∧
      |∫ o, F t o ∂observationLaw M| ≤
        (∫ o : Obs X Z, |E o.1| ∂observationLaw M) * t^2 := by
    filter_upwards [hE, population_binary_regular_component_path_local_mean M h
      phi dphi hphi hDiff hDerivative L hOrder cpi hov hpol hy del hd,
      continuousAt_id.abs.eventually_lt_const (by simpa using hr)] with t ht hm htr
    let e := eta0Bin M L + t • del
    let w := regularValue e.gamma k j
    have he := hpath t htr
    let a : RegularIndex L := ⟨(k,j), hk.le, hj⟩
    have hw : Measurable w := by
      change Measurable (regularValue e.gamma k j)
      unfold regularValue
      split_ifs
      · exact (he.2.2.2.2.2.1 _).2
      · fun_prop
    have hwb : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ 1 := by
      filter_upwards [he.2.2.2.2.1 a] with x hx
      change ‖regularValue e.gamma k j x‖ ≤ 1
      simp only [regularValue, dif_pos (show k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from ⟨hk.le,hj⟩)]
      rw [Real.norm_eq_abs, abs_of_nonneg hx.2.1]
      exact hx.2.2
    have ip := binary_weighted_hMinus_integrable_of_admissible M phi hphi L e he
      k j hk hj w hw 1 hwb
    have i0 := binary_weighted_hMinus_integrable_of_admissible M phi hphi L (eta0Bin M L)
      he0 k j hk hj w hw 1 hwb
    have hc := hm k j hk.le
    let R := fun o : Obs X Z => w o.1 *
      (hMinus phi L e k j o.1 + binaryRegularRegressionMean phi L (eta0Bin M L) e k j o.1 +
        binaryRegularPolicyMean M phi dphi L e k j o.1 -
          hMinus phi L (eta0Bin M L) k j o.1)
    have iF : Integrable (F t) (observationLaw M) := by
      convert! (ip.fun_add hc.1).sub' i0 using 1
      funext o
      dsimp only [F, w, e]
      ring
    have iR : Integrable R (observationLaw M) := by
      convert! (ip.fun_add hc.2.1).sub' i0 using 1
      funext o
      dsimp only [R]
      ring
    have heq : (∫ o, F t o ∂observationLaw M) = ∫ o, R o ∂observationLaw M := by
      have hf : F t = fun o : Obs X Z =>
          w o.1 * hMinus phi L e k j o.1 +
            w o.1 * (binScoreComponents phi dphi L e k j o - hMinus phi L e k j o.1) -
              w o.1 * hMinus phi L (eta0Bin M L) k j o.1 := by
        funext o
        dsimp only [F, w, e]
        ring
      rw [hf, integral_sub (ip.fun_add hc.1) i0, integral_add ip hc.1, hc.2.2,
        ← integral_add ip hc.2.1, ← integral_sub (ip.fun_add hc.2.1) i0]
      apply integral_congr_ae
      exact Eventually.of_forall (fun o => by dsimp only [R]; ring)
    have hb : ∀ᵐ o ∂observationLaw M, |R o| ≤ |E o.1| * t^2 := by
      filter_upwards [observationLaw_covariate_ae M _ ht,
        observationLaw_covariate_ae M _ hwb] with o ho hw'
      dsimp only [R]
      rw [abs_mul]
      have hwa : |w o.1| ≤ 1 := by simpa only [Real.norm_eq_abs] using hw'
      calc
        _ ≤ 1 * |hMinus phi L e k j o.1 +
            binaryRegularRegressionMean phi L (eta0Bin M L) e k j o.1 +
            binaryRegularPolicyMean M phi dphi L e k j o.1 -
            hMinus phi L (eta0Bin M L) k j o.1| :=
          mul_le_mul_of_nonneg_right hwa (abs_nonneg _)
        _ ≤ E o.1 * t^2 := by simpa only [one_mul] using ho
        _ ≤ |E o.1| * t^2 := mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg t)
    refine ⟨iF, ?_⟩
    rw [heq]
    calc
      _ ≤ ∫ o, |R o| ∂observationLaw M := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm R
      _ ≤ ∫ o : Obs X Z, |E o.1| * t^2 ∂observationLaw M :=
        integral_mono_ae iR.abs (iEO.mul_const _) hb
      _ = _ := integral_mul_const _ _
  refine ⟨hlocal.mono (fun _ ht => ht.1), ?_⟩
  have hzero : (∫ o, F 0 o ∂observationLaw M) = 0 := by
    apply abs_eq_zero.mp
    have hz := hlocal.self_of_nhds.2
    simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero] at hz
    exact le_antisymm hz (abs_nonneg _)
  have ho : (fun t : ℝ => ∫ o, F t o ∂observationLaw M) =O[nhds 0]
      (fun t : ℝ => t^2) := by
    apply Asymptotics.IsBigO.of_bound (∫ o : Obs X Z, |E o.1| ∂observationLaw M)
    filter_upwards [hlocal] with t ht
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)] using ht.2
  change HasDerivAt (fun t : ℝ => ∫ o, F t o ∂observationLaw M) 0 0
  apply HasDerivAt.of_isLittleO
  simpa only [hzero, smul_zero, sub_zero] using
    ho.trans_isLittleO (Asymptotics.isLittleO_pow_id (𝕜 := ℝ) (by norm_num : 1 < 2))


-- Product inheritance keeps the fitted weight, centers the fitted hinge event,
-- and subtracts the already-controlled weight/hinge error product.
-- @node: population_binary_regular_product_joint_orthogonality_of_margins
/-- Under [the threshold-crossing model](hyp:h) with [almost surely binary
outcomes](hyp:hy), suppose [the policy is measurable and probability valued](hyp:hphi),
[has the specified derivative](hyp:hDiff), and [has a uniformly bounded Lipschitz
derivative](hyp:hDerivative). Assume [invariant baseline and policy level
ordering](hyp:hOrder), [baseline overlap](hyp:hov), [policy overlap](hyp:hpol),
and [an admissible joint direction at the population nuisance](hyp:hd). For [a
baseline level index strictly below the number of levels](hyp:hk) and [a regular
interval](hyp:hj), if [the separation constant is positive](hyp:hsep) and [almost
everywhere the pooled boundary gap and the distances of the upper propensity
minus the treated-outcome contrast from both boundaries are at least that
constant](hyp:hgap), then [the fitted product score is integrable throughout a
neighborhood of zero and its observation expectation has derivative zero at
zero along the full joint nuisance path](goal). -/
lemma population_binary_regular_product_joint_orthogonality_of_margins
    (h : ThresholdCrossing M) (hy : OutcomeBinaryAE M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi) (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del))
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (sep : ℝ) (hsep : 0 < sep)
    (hgap : ∀ᵐ x ∂xLaw M,
      sep ≤ pooledQBin phi L (eta0Bin M L) k j x -
        pooledQBin phi L (eta0Bin M L) k (j-1) x ∧
      sep ≤ |positiveValue (eta0Bin M L).pLev (k+1) x - binFullJ L (eta0Bin M L) k x -
        pooledQBin phi L (eta0Bin M L) k (j-1) x| ∧
      sep ≤ |positiveValue (eta0Bin M L).pLev (k+1) x - binFullJ L (eta0Bin M L) k x -
        pooledQBin phi L (eta0Bin M L) k j x|) :
    (∀ᶠ t : ℝ in nhds 0, Integrable
      (psiProdBin phi dphi L (eta0Bin M L + t • del) k j) (observationLaw M)) ∧
    HasDerivAt (fun t : ℝ => ∫ o, psiProdBin phi dphi L
      (eta0Bin M L + t • del) k j o ∂observationLaw M) 0 0 := by
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  let F := fun (t : ℝ) (o : Obs X Z) =>
    regularValue (eta0Bin M L + t • del).gamma k j o.1 *
      (binScoreComponents phi dphi L (eta0Bin M L + t • del) k j o -
        hMinus phi L (eta0Bin M L) k j o.1)
  let C := fun (t : ℝ) (x : X) =>
    (regularValue (eta0Bin M L + t • del).gamma k j x -
      regularValue (eta0Bin M L).gamma k j x) *
    (hMinus phi L (eta0Bin M L + t • del) k j x - hMinus phi L (eta0Bin M L) k j x)
  have hF := population_binary_regular_component_joint_bias_orthogonality M h hy phi dphi
    hphi hDiff hDerivative L hOrder cpi hov hpol del hd k j hk hj sep hsep hgap
  have hC := population_binary_hinge_weight_interaction_orthogonality M phi dphi hphi
    hDiff hDerivative L del hd k j hk hj
  have he0 := binary_admissible_direction_origin M L (eta0Bin M L) del hd
  let a : RegularIndex L := ⟨(k,j), hk.le, hj⟩
  have hv (e : NuisanceBin L) : regularValue e.gamma k j = e.gamma a := by
    funext x
    simp only [regularValue, dif_pos (show k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from ⟨hk.le,hj⟩)]
    rfl
  have hg0 : regularValue (eta0Bin M L).gamma k j = gamma M L k j := by
    rw [hv]
    rfl
  have hm (e : NuisanceBin L) (he : BinAdmissible M L e) :
      Measurable (regularValue e.gamma k j) ∧
      ∀ᵐ x ∂xLaw M, ‖regularValue e.gamma k j x‖ ≤ 1 := by
    rw [hv]
    refine ⟨(he.2.2.2.2.2.1 a).2, ?_⟩
    filter_upwards [he.2.2.2.2.1 a] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx.2.1]
    exact hx.2.2
  have h0 := hm (eta0Bin M L) he0
  have iT := binary_weighted_hMinus_integrable_of_admissible M phi hphi L (eta0Bin M L)
    he0 k j hk hj _ h0.1 1 h0.2
  let target := ∫ o : Obs X Z, regularValue (eta0Bin M L).gamma k j o.1 *
    hMinus phi L (eta0Bin M L) k j o.1 ∂observationLaw M
  have hmap : (observationLaw M).map Prod.fst = xLaw M := by
    simpa only [observationLaw, xLaw, Function.comp_def] using Measure.map_map measurable_fst
      (M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY)))
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  have hlocal : ∀ᶠ t : ℝ in nhds 0,
      Integrable (psiProdBin phi dphi L (eta0Bin M L + t • del) k j) (observationLaw M) ∧
      (∫ o, psiProdBin phi dphi L (eta0Bin M L + t • del) k j o ∂observationLaw M) =
        (∫ o, F t o ∂observationLaw M) - (∫ x, C t x ∂xLaw M) + target := by
    filter_upwards [hF.1, continuousAt_id.abs.eventually_lt_const (by simpa using hr)]
      with t iF htr
    let e := eta0Bin M L + t • del
    have he := hpath t htr
    have ht := hm e he
    let w := fun x => regularValue e.gamma k j x - regularValue (eta0Bin M L).gamma k j x
    have hw : Measurable w := by first | fun_prop | exact ht.1.sub h0.1
    have hwb : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ 2 := by
      filter_upwards [ht.2, h0.2] with x hx hy
      exact (norm_sub_le _ _).trans (by linarith)
    have i1 := binary_weighted_hMinus_integrable_of_admissible M phi hphi L e he
      k j hk hj w hw 2 hwb
    have i0 := binary_weighted_hMinus_integrable_of_admissible M phi hphi L (eta0Bin M L)
      he0 k j hk hj w hw 2 hwb
    have iCo : Integrable (fun o : Obs X Z => C t o.1) (observationLaw M) := by
      simpa only [C, w, e, mul_sub] using i1.sub' i0
    obtain ⟨H0, hm0, heq0⟩ := binary_hMinus_measurable_version M phi hphi L (eta0Bin M L) he0 k j
    obtain ⟨Ht, hmt, heqt⟩ := binary_hMinus_measurable_version M phi hphi L e he k j
    have hcm : AEStronglyMeasurable (C t) (xLaw M) := by
      have hv : Measurable (fun x => w x * (Ht x - H0 x)) := by fun_prop
      apply hv.aestronglyMeasurable.congr
      filter_upwards [heqt, heq0] with x hxt hx0
      simp only [C, w, e, hxt, hx0]
    have hci : (∫ o : Obs X Z, C t o.1 ∂observationLaw M) = ∫ x, C t x ∂xLaw M := by
      rw [← hmap]
      exact (integral_map measurable_fst.aemeasurable (by rwa [hmap])).symm
    obtain ⟨iCenter, hCenter⟩ := population_binary_fitted_hinge_event_centering M
      phi hphi L e he he0 k j hk hj
    have hid : (fun o => psiProdBin phi dphi L e k j o -
        regularValue (eta0Bin M L).gamma k j o.1 * hMinus phi L (eta0Bin M L) k j o.1) =
        (fun o => F t o + hMinus phi L e k j o.1 *
          (indicator (o.2.1 ∈ policyUnion L k j) - gamma M L k j o.1) - C t o.1) := by
      funext o
      dsimp only [F, C]
      rw [hg0]
      exact binary_regular_product_bias_decomposition M phi dphi L e k j o
    have iBias := (iF.fun_add iCenter).sub' iCo
    rw [← hid] at iBias
    have iScore : Integrable (psiProdBin phi dphi L e k j) (observationLaw M) := by
      convert! iBias.fun_add iT using 1
      funext o
      ring
    refine ⟨iScore, ?_⟩
    have heq := integral_congr_ae (μ := observationLaw M) (Eventually.of_forall (congrFun hid))
    rw [integral_sub iScore iT, integral_sub (iF.fun_add iCenter) iCo,
      integral_add iF iCenter, hCenter, add_zero, hci] at heq
    change (∫ o, psiProdBin phi dphi L e k j o ∂observationLaw M) = _
    dsimp only [target]
    linarith
  refine ⟨hlocal.mono (fun _ ht => ht.1), ?_⟩
  have hder : HasDerivAt (fun t : ℝ =>
      (∫ o, F t o ∂observationLaw M) - (∫ x, C t x ∂xLaw M) + target) 0 0 := by
    simpa only [Pi.sub_apply, sub_self] using (hF.2.sub hC).add_const target
  apply hder.congr_of_eventuallyEq
  exact hlocal.mono (fun _ ht => ht.2)

end Papers.TbsPrteOptimalTransport
