module
public import Papers.TbsPrteOptimalTransport.Helpers.JointPooledEnvelopes
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationFullJointDerivative
public import Papers.TbsPrteOptimalTransport.Helpers.RegularProductBias
/-! Hinge increments and quadratic product-weight interactions on admissible paths. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

-- The two maxima are Lipschitz even when a fitted branch changes.
-- @node: binary_hinge_increment_bound
/-- [The change in the positive part of an upper level minus the larger of two
lower thresholds is bounded by the sum of the absolute changes in those three
inputs](goal). -/
lemma binary_hinge_increment_bound (q l b q0 l0 b0 : ℝ) :
    |max 0 (q - max l b) - max 0 (q0 - max l0 b0)| ≤
      |q - q0| + |l - l0| + |b - b0| := by
  have hm := abs_max_sub_max_le_max l b l0 b0
  have hm' : |max l b - max l0 b0| ≤ |l - l0| + |b - b0| :=
    hm.trans (max_le (le_add_of_nonneg_right (abs_nonneg _))
      (le_add_of_nonneg_left (abs_nonneg _)))
  have ha : |(q - max l b) - (q0 - max l0 b0)| ≤
      |q - q0| + |l - l0| + |b - b0| := by
    rw [show (q - max l b) - (q0 - max l0 b0) =
      (q - q0) - (max l b - max l0 b0) by ring]
    exact (abs_sub _ _).trans (by linarith)
  exact (abs_max_sub_max_le_max 0 _ 0 _).trans
    (max_le (by simp only [sub_self, abs_zero]; positivity) ha)

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- Extend the pooled increment to the fixed q_0 = p_k boundary.
-- @node: population_binary_pooled_boundary_path_increment_bound
/-- If [the policy is a valid policy map](hyp:hphi), [its derivative is the
specified derivative function](hyp:hDiff), [that derivative is bounded and
Lipschitz](hyp:hDerivative), and [the binary nuisance direction is admissible
at the truth](hyp:hd), then, for [a baseline index no greater than the number
of gaps](hyp:hk) and [a boundary index within its policy subdivision](hyp:hj),
[there is a nonnegative constant bounding the absolute pooled boundary change
by that constant times the absolute path displacement, for all sufficiently
small displacements and almost every covariate value](goal). -/
lemma population_binary_pooled_boundary_path_increment_bound
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del))
    (k j : ℕ) (hk : k ≤ L.K) (hj : j ≤ L.l k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t : ℝ in nhds 0, ∀ᵐ x ∂xLaw M,
      |pooledQBin phi L (eta0Bin M L + t • del) k j x -
        pooledQBin phi L (eta0Bin M L) k j x| ≤ C * |t| := by
  by_cases hj0 : j = 0
  · subst j
    obtain ⟨C, hC, hb⟩ := binary_baseline_propensity_direction_regular M L
      (eta0Bin M L) del hd
    have hp := binary_positive_regression_direction_regular (M := M) L del.pLev C hC hb k
    refine ⟨C, hC, Eventually.of_forall (fun t => ?_)⟩
    filter_upwards [hp.2] with x hx
    simp only [pooledQBin, if_true]
    by_cases hi : 1 ≤ k ∧ k ≤ L.K
    · simp only [positiveValue, dif_pos hi]
      change |((eta0Bin M L).pLev ⟨k,hi⟩ x + t * del.pLev ⟨k,hi⟩ x) -
        (eta0Bin M L).pLev ⟨k,hi⟩ x| ≤ _
      simp only [add_sub_cancel_left, abs_mul]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        (show |del.pLev ⟨k,hi⟩ x| ≤ C from by
          simpa only [positiveValue, dif_pos hi, Real.norm_eq_abs] using hx) (abs_nonneg t)
    · simp only [positiveValue, dif_neg hi, sub_self, abs_zero]
      positivity
  · exact population_binary_pooled_path_increment_bound M phi dphi hphi hDiff
      hDerivative L del hd ⟨(k,j), hk, by omega, hj⟩

-- Every affine argument of the hinge has a uniform linear increment.
-- @node: population_binary_hinge_path_increment_bound
/-- If [the policy is a valid policy map](hyp:hphi), [it has the specified
derivative](hyp:hDiff), [the derivative is bounded and Lipschitz](hyp:hDerivative),
and [the binary nuisance direction is admissible at the truth](hyp:hd), then,
for [a gap index below the number of baseline gaps](hyp:hk) and [a positive
boundary index within that gap's policy subdivision](hyp:hj), [the absolute
change in the binary lower hinge is bounded by a nonnegative constant times
the absolute path displacement, for all sufficiently small displacements and
almost every covariate value](goal). -/
lemma population_binary_hinge_path_increment_bound
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del))
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t : ℝ in nhds 0, ∀ᵐ x ∂xLaw M,
      |hMinus phi L (eta0Bin M L + t • del) k j x -
        hMinus phi L (eta0Bin M L) k j x| ≤ C * |t| := by
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
  unfold hMinus
  exact (binary_hinge_increment_bound _ _ _ _ _ _).trans (by linarith)

-- This is precisely the weight-times-hinge error left by the product score.
-- @node: population_binary_hinge_weight_path_quadratic_bound
/-- If [the policy is a valid policy map](hyp:hphi), [it has the specified
derivative](hyp:hDiff), [the derivative is bounded and Lipschitz](hyp:hDerivative),
and [the binary nuisance direction is admissible at the truth](hyp:hd), then,
for [a valid baseline gap](hyp:hk) and [a positive boundary index within its
policy subdivision](hyp:hj), [the absolute product of the regular weight change
and the lower hinge change is bounded by a nonnegative constant times the squared
path displacement, for all sufficiently small displacements and almost every
covariate value](goal). -/
lemma population_binary_hinge_weight_path_quadratic_bound
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del))
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t : ℝ in nhds 0, ∀ᵐ x ∂xLaw M,
      |(regularValue (eta0Bin M L + t • del).gamma k j x -
          regularValue (eta0Bin M L).gamma k j x) *
        (hMinus phi L (eta0Bin M L + t • del) k j x -
          hMinus phi L (eta0Bin M L) k j x)| ≤ C * t^2 := by
  obtain ⟨H, hH, hh⟩ := population_binary_hinge_path_increment_bound M
    phi dphi hphi hDiff hDerivative L del hd k j hk hj
  obtain ⟨G, hG, hg⟩ := binary_regular_weight_direction_regular M L (eta0Bin M L) del hd
  let a : RegularIndex L := ⟨(k,j), hk.le, hj⟩
  refine ⟨G * H, mul_nonneg hG hH, ?_⟩
  filter_upwards [hh] with t ht
  filter_upwards [ht, (hg a).2] with x hx hgx
  have hw : |regularValue (eta0Bin M L + t • del).gamma k j x -
      regularValue (eta0Bin M L).gamma k j x| ≤ G * |t| := by
    simp only [regularValue, dif_pos (show k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from ⟨hk.le,hj⟩)]
    change |((eta0Bin M L).gamma a x + t * del.gamma a x) -
      (eta0Bin M L).gamma a x| ≤ _
    simp only [add_sub_cancel_left, abs_mul]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (show |del.gamma a x| ≤ G from by simpa only [Real.norm_eq_abs] using hgx)
      (abs_nonneg t)
  rw [abs_mul]
  calc
    _ ≤ (G * |t|) * (H * |t|) :=
      mul_le_mul hw hx (abs_nonneg _) (mul_nonneg hG (abs_nonneg t))
    _ = G * H * t^2 := by rw [← sq_abs t]; ring

-- Measurable hinge versions are derived from admissibility, so this population
-- derivative needs no analytic premises beyond those of the paper.
-- @node: population_binary_hinge_weight_interaction_orthogonality
/-- If [the policy is a valid policy map](hyp:hphi), [it has the specified
derivative](hyp:hDiff), [the derivative is bounded and Lipschitz](hyp:hDerivative),
and [the binary nuisance direction is admissible at the truth](hyp:hd), then,
for [a valid baseline gap](hyp:hk) and [a positive boundary index within its
policy subdivision](hyp:hj), [the covariate-integrated product of the regular
weight change and the lower hinge change has derivative zero at zero path
displacement](goal). -/
lemma population_binary_hinge_weight_interaction_orthogonality
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del))
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    HasDerivAt (fun t : ℝ => ∫ x,
      (regularValue (eta0Bin M L + t • del).gamma k j x -
        regularValue (eta0Bin M L).gamma k j x) *
      (hMinus phi L (eta0Bin M L + t • del) k j x -
        hMinus phi L (eta0Bin M L) k j x) ∂xLaw M) 0 0 := by
  haveI : IsProbabilityMeasure (xLaw M) :=
    Measure.isProbabilityMeasure_map M.measX.aemeasurable
  let F := fun (t : ℝ) (x : X) =>
    (regularValue (eta0Bin M L + t • del).gamma k j x -
      regularValue (eta0Bin M L).gamma k j x) *
    (hMinus phi L (eta0Bin M L + t • del) k j x -
      hMinus phi L (eta0Bin M L) k j x)
  have hzero : F 0 = fun _ => 0 := by
    funext x
    have hw : regularValue (eta0Bin M L + (0 : ℝ) • del).gamma k j x -
        regularValue (eta0Bin M L).gamma k j x = 0 := by
      simp only [regularValue, dif_pos (show k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from ⟨hk.le,hj⟩)]
      change ((eta0Bin M L).gamma _ x + 0 * del.gamma _ x) -
        (eta0Bin M L).gamma _ x = 0
      ring
    exact show F 0 x = 0 from by dsimp only [F]; rw [hw, zero_mul]
  obtain ⟨C, hC, hb⟩ := population_binary_hinge_weight_path_quadratic_bound M
    phi dphi hphi hDiff hDerivative L del hd k j hk hj
  have he0 := binary_admissible_direction_origin M L (eta0Bin M L) del hd
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  let a : RegularIndex L := ⟨(k,j), hk.le, hj⟩
  apply integral_local_quadratic_orthogonality (xLaw M) F C
  · rw [hzero]
    exact integrable_zero X ℝ _
  · filter_upwards [hb, continuousAt_id.abs.eventually_lt_const (by simpa using hr)]
      with t ht htr
    have het := hpath t htr
    obtain ⟨H0, hm0, heq0⟩ := binary_hMinus_measurable_version M phi hphi L
      (eta0Bin M L) he0 k j
    obtain ⟨Ht, hmt, heqt⟩ := binary_hMinus_measurable_version M phi hphi L
      (eta0Bin M L + t • del) het k j
    have hval (e : NuisanceBin L) : regularValue e.gamma k j = e.gamma a := by
      funext x
      simp only [regularValue, dif_pos (show k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from ⟨hk.le,hj⟩)]
      rfl
    have hg0 : Measurable (regularValue (eta0Bin M L).gamma k j) := by
      rw [hval]
      exact (he0.2.2.2.2.2.1 a).2
    have hgt : Measurable (regularValue (eta0Bin M L + t • del).gamma k j) := by
      rw [hval]
      exact (het.2.2.2.2.2.1 a).2
    refine ⟨?_, ?_⟩
    · have hm : Measurable (fun x =>
          (regularValue (eta0Bin M L + t • del).gamma k j x -
            regularValue (eta0Bin M L).gamma k j x) * (Ht x - H0 x)) := by
        first | fun_prop | exact (hgt.sub hg0).mul (hmt.sub hm0)
      apply hm.aestronglyMeasurable.congr
      filter_upwards [heq0, heqt] with x hx0 hxt
      simp only [F, hx0, hxt]
    · simpa only [hzero, sub_zero] using ht

end Papers.TbsPrteOptimalTransport
