module
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousLearners
/-! Uniform first-stage perturbation bounds for the continuous primitive learner rate. -/
public section
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: propensity_support_uniform_perturbation
/-- If [the original propensity lies between zero and one everywhere](hyp:hp),
[the perturbed propensity does too](hyp:hp'), and [their absolute difference is
uniformly bounded by an error tolerance](hyp:he), then [at any covariate value both
the lower and upper propensity support endpoints change by at most that tolerance](goal). -/
lemma propensity_support_uniform_perturbation (p p' : Z → X → ℝ)
    (hp : ∀ z x, p z x ∈ Icc (0 : ℝ) 1)
    (hp' : ∀ z x, p' z x ∈ Icc (0 : ℝ) 1)
    (e : ℝ) (he : ∀ z x, |p' z x - p z x| ≤ e) (x : X) :
    |pLow p' x - pLow p x| ≤ e ∧ |pHigh p' x - pHigh p x| ≤ e := by
  have hbl : BddBelow (range (fun z => p z x)) :=
    ⟨0, by rintro _ ⟨z, rfl⟩; exact (hp z x).1⟩
  have hbl' : BddBelow (range (fun z => p' z x)) :=
    ⟨0, by rintro _ ⟨z, rfl⟩; exact (hp' z x).1⟩
  have hbu : BddAbove (range (fun z => p z x)) :=
    ⟨1, by rintro _ ⟨z, rfl⟩; exact (hp z x).2⟩
  have hbu' : BddAbove (range (fun z => p' z x)) :=
    ⟨1, by rintro _ ⟨z, rfl⟩; exact (hp' z x).2⟩
  have hlo : pLow p x - e ≤ pLow p' x := by
    apply le_csInf (range_nonempty _)
    rintro _ ⟨z, rfl⟩
    have hz := csInf_le hbl (mem_range_self z)
    have hd := (abs_le.mp (he z x)).1
    change pLow p x ≤ p z x at hz
    linarith
  have hlo' : pLow p' x - e ≤ pLow p x := by
    apply le_csInf (range_nonempty _)
    rintro _ ⟨z, rfl⟩
    have hz := csInf_le hbl' (mem_range_self z)
    have hd := (abs_le.mp (he z x)).2
    change pLow p' x ≤ p' z x at hz
    linarith
  have hhi : pHigh p' x ≤ pHigh p x + e := by
    apply csSup_le (range_nonempty _)
    rintro _ ⟨z, rfl⟩
    have hz := le_csSup hbu (mem_range_self z)
    have hd := (abs_le.mp (he z x)).2
    change p z x ≤ pHigh p x at hz
    linarith
  have hhi' : pHigh p x ≤ pHigh p' x + e := by
    apply csSup_le (range_nonempty _)
    rintro _ ⟨z, rfl⟩
    have hz := le_csSup hbu' (mem_range_self z)
    have hd := (abs_le.mp (he z x)).1
    change p' z x ≤ pHigh p' x at hz
    linarith
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith

-- @node: uniform_first_stage_error_bounds
/-- If [every fitted propensity lies between zero and one](hyp:hp), then [at each
sample size and sample realization the supremum first-stage error is nonnegative
and bounds every instrument-covariate pair's absolute propensity error](goal). -/
lemma uniform_first_stage_error_bounds (M : LatentIVModel Ω X Z)
    (pHat : ℕ → A → Z → X → ℝ)
    (hp : ∀ n a z x, pHat n a z x ∈ Icc (0 : ℝ) 1) (n : ℕ) (a : A) :
    0 ≤ uniformFirstStageError M pHat n a ∧
      ∀ z x, |pHat n a z x - M.prop z x| ≤ uniformFirstStageError M pHat n a := by
  have hb : BddAbove (range (fun zx : Z × X =>
      |pHat n a zx.1 zx.2 - M.prop zx.1 zx.2|)) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨⟨z, x⟩, rfl⟩
    apply abs_le.mpr
    constructor <;> linarith [(hp n a z x).1, (hp n a z x).2,
      (M.rangeProp z x).1, (M.rangeProp z x).2]
  have he (z : Z) (x : X) :
      |pHat n a z x - M.prop z x| ≤ uniformFirstStageError M pHat n a :=
    le_csSup hb (mem_range_self (z, x))
  exact ⟨(abs_nonneg _).trans (he (Classical.ofNonempty) (Classical.ofNonempty)), he⟩

-- @node: policy_propensity_uniform_perturbation
/-- If [the policy is uniformly Lipschitz in propensity with a nonnegative
constant](hyp:hL), [the original propensity lies between zero and one](hyp:hp),
[the perturbed propensity does too](hyp:hp'), and [their difference is uniformly
bounded by an error tolerance](hyp:he), then [the policy-transformed propensities
differ at any instrument-covariate pair by at most the Lipschitz constant times
that tolerance](goal). -/
lemma policy_propensity_uniform_perturbation (phi : Z → X → ℝ → ℝ)
    (L : ℝ) (hL : PolicyLipschitz phi L) (p p' : Z → X → ℝ)
    (hp : ∀ z x, p z x ∈ Icc (0 : ℝ) 1)
    (hp' : ∀ z x, p' z x ∈ Icc (0 : ℝ) 1)
    (e : ℝ) (he : ∀ z x, |p' z x - p z x| ≤ e) (z : Z) (x : X) :
    |policyProp phi p' z x - policyProp phi p z x| ≤ L * e := by
  exact (hL.2 z x _ _ (hp z x) (hp' z x)).trans
    (mul_le_mul_of_nonneg_left (he z x) hL.1)

-- @node: endpoint_map_uniform_perturbation
/-- If [the policy is uniformly Lipschitz in propensity with a nonnegative
constant](hyp:hL), [the original propensity lies between zero and one](hyp:hp),
[the perturbed propensity does too](hyp:hp'), [the error tolerance is nonnegative](hyp:he0),
and [the propensity difference is uniformly bounded by that tolerance](hyp:he),
then [each of the three endpoint maps changes at any instrument-covariate pair
by at most the tolerance times the sum of one and the Lipschitz constant](goal). -/
lemma endpoint_map_uniform_perturbation (phi : Z → X → ℝ → ℝ)
    (L : ℝ) (hL : PolicyLipschitz phi L) (p p' : Z → X → ℝ)
    (hp : ∀ z x, p z x ∈ Icc (0 : ℝ) 1)
    (hp' : ∀ z x, p' z x ∈ Icc (0 : ℝ) 1)
    (e : ℝ) (he0 : 0 ≤ e) (he : ∀ z x, |p' z x - p z x| ≤ e)
    (j : Fin 3) (zx : Z × X) :
    |endpointMap p' (policyProp phi p') j zx -
      endpointMap p (policyProp phi p) j zx| ≤ (1 + L) * e := by
  have hs := propensity_support_uniform_perturbation p p' hp hp' e he zx.2
  have hq := policy_propensity_uniform_perturbation phi L hL p p' hp hp' e he zx.1 zx.2
  have heD : e ≤ (1 + L) * e := by nlinarith [mul_nonneg hL.1 he0]
  have hqD : L * e ≤ (1 + L) * e := by nlinarith
  unfold endpointMap
  split_ifs
  · exact hs.1.trans heD
  · exact (abs_min_sub_min_le_max _ _ _ _).trans
      (max_le (hs.1.trans heD) (hq.trans hqD))
  · have hd : |(policyProp phi p' zx.1 zx.2 - pHigh p' zx.2) -
        (policyProp phi p zx.1 zx.2 - pHigh p zx.2)| ≤ (1 + L) * e := by
      calc
        _ = |(policyProp phi p' zx.1 zx.2 - policyProp phi p zx.1 zx.2) -
            (pHigh p' zx.2 - pHigh p zx.2)| := by congr 1; ring
        _ ≤ |policyProp phi p' zx.1 zx.2 - policyProp phi p zx.1 zx.2| +
            |pHigh p' zx.2 - pHigh p zx.2| := abs_sub _ _
        _ ≤ L * e + e := add_le_add hq hs.2
        _ = (1 + L) * e := by ring
    exact (abs_max_sub_max_le_max _ _ _ _).trans
      (max_le (by simpa using mul_nonneg (by linarith [hL.1]) he0) hd)

-- @node: support_projection_nonexpansive_at_support
/-- If [a comparison index lies in the conditional propensity support interval](hyp:hu),
then [projecting any real index onto that interval cannot increase its distance
from the comparison index](goal). -/
lemma support_projection_nonexpansive_at_support (M : LatentIVModel Ω X Z)
    (x : X) (t u : ℝ) (hu : u ∈ supportInterval M x) :
    |supportProjection M x t - u| ≤ |t - u| := by
  have hfix : supportProjection M x u = u := by
    simp only [supportProjection, max_eq_right hu.1, min_eq_right hu.2]
  calc
    |supportProjection M x t - u| =
        |supportProjection M x t - supportProjection M x u| := by rw [hfix]
    _ ≤ |t - u| := Causalean.Mathlib.Analysis.abs_min_max_sub_min_max_le _ _ _ _

-- @node: boundedAtRate_of_uniform_domination
/-- If [a scaling constant is strictly positive](hyp:hK), [one random sequence is
bounded in probability at a given rate under the sampling measure](hyp:hf), and
[the absolute value of a second sequence is everywhere bounded by that constant
times the first sequence's absolute value](hyp:hgf), then [the second sequence is
bounded in probability at the same rate under that measure](goal). -/
lemma boundedAtRate_of_uniform_domination (μ : Measure A)
    (f g : ℕ → A → ℝ) (r : ℕ → ℝ) (K : ℝ) (hK : 0 < K)
    (hf : BoundedAtRate μ f r) (hgf : ∀ n a, |g n a| ≤ K * |f n a|) :
    BoundedAtRate μ g r := by
  refine ⟨hf.1, ?_⟩
  intro ε hε
  obtain ⟨C, hC, hn⟩ := hf.2 ε hε
  refine ⟨K * C, mul_pos hK hC, ?_⟩
  filter_upwards [hn] with n hn
  apply (measure_mono _).trans hn
  intro a ha
  have hd := hgf n a
  change K * C * r n < |g n a| at ha
  change C * r n < |f n a|
  nlinarith

-- @node: first_stage_endpoint_map_rates
/-- If [the policy is uniformly Lipschitz in propensity with a nonnegative
constant](hyp:hL), [all fitted propensities lie between zero and one](hyp:hp),
[the uniform first-stage error is bounded in probability at a nonnegative rate](hyp:hrp),
and [that rate converges to zero](hyp:hv), then [each of the three endpoint maps'
absolute errors, integrated over the population instrument-covariate law, is bounded
in probability under the sampling measure at that same nonnegative, vanishing rate](goal). -/
lemma first_stage_endpoint_map_rates (M : LatentIVModel Ω X Z) (μ : Measure A)
    (phi : Z → X → ℝ → ℝ) (L : ℝ) (hL : PolicyLipschitz phi L)
    (pHat : ℕ → A → Z → X → ℝ)
    (hp : ∀ n a z x, pHat n a z x ∈ Icc (0 : ℝ) 1)
    (rp : ℕ → ℝ) (hrp : FirstStageUniformRate M μ pHat rp)
    (hv : Tendsto rp atTop (𝓝 0)) : EndpointMapRates M μ phi pHat rp := by
  haveI : IsProbabilityMeasure (zxLaw M) := Measure.isProbabilityMeasure_map
    (M.measZ.prodMk M.measX).aemeasurable
  refine ⟨hrp.1, hv, ?_⟩
  intro j
  apply boundedAtRate_of_uniform_domination μ (uniformFirstStageError M pHat)
    _ rp (1 + L) (by linarith [hL.1]) hrp
  intro n a
  have he := uniform_first_stage_error_bounds M pHat hp n a
  have hb : ∀ zx : Z × X,
      |endpointMap (pHat n a) (policyProp phi (pHat n a)) j zx -
        endpointMap M.prop (policyProp phi M.prop) j zx| ≤
        (1 + L) * uniformFirstStageError M pHat n a :=
    endpoint_map_uniform_perturbation phi L hL M.prop (pHat n a)
      M.rangeProp (hp n a) _ he.1 he.2 j
  have hi := norm_integral_le_of_norm_le_const (μ := zxLaw M)
    (f := fun zx => |endpointMap (pHat n a) (policyProp phi (pHat n a)) j zx -
      endpointMap M.prop (policyProp phi M.prop) j zx|)
    (Filter.Eventually.of_forall fun zx => by
      simpa only [Real.norm_eq_abs, abs_abs] using hb zx)
  simpa only [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one, mul_one,
    abs_of_nonneg he.1] using hi

-- @node: clamp_policy_uniform_perturbation
/-- If [the policy is uniformly Lipschitz in propensity with a nonnegative
constant](hyp:hL), [the original propensity lies between zero and one](hyp:hp),
[the perturbed propensity does too](hyp:hp'), [the error tolerance is nonnegative](hyp:he0),
and [the propensity difference is uniformly bounded by that tolerance](hyp:he),
then [the policy propensities clamped to their respective support intervals differ
by at most the tolerance times the sum of one and the Lipschitz constant](goal). -/
lemma clamp_policy_uniform_perturbation (phi : Z → X → ℝ → ℝ)
    (L : ℝ) (hL : PolicyLipschitz phi L) (p p' : Z → X → ℝ)
    (hp : ∀ z x, p z x ∈ Icc (0 : ℝ) 1)
    (hp' : ∀ z x, p' z x ∈ Icc (0 : ℝ) 1)
    (e : ℝ) (he0 : 0 ≤ e) (he : ∀ z x, |p' z x - p z x| ≤ e)
    (z : Z) (x : X) :
    |clampPolicy p' (policyProp phi p') z x -
      clampPolicy p (policyProp phi p) z x| ≤ (1 + L) * e := by
  have hs := propensity_support_uniform_perturbation p p' hp hp' e he x
  have hq := policy_propensity_uniform_perturbation phi L hL p p' hp hp' e he z x
  have heD : e ≤ (1 + L) * e := by nlinarith [mul_nonneg hL.1 he0]
  have hqD : L * e ≤ (1 + L) * e := by nlinarith
  exact (abs_min_sub_min_le_max _ _ _ _).trans
    (max_le (hs.2.trans heD) ((abs_max_sub_max_le_max _ _ _ _).trans
      (max_le (hs.1.trans heD) (hq.trans hqD))))

-- @node: evaluation_indices_uniform_perturbation
/-- If [the policy is uniformly Lipschitz in propensity with a nonnegative
constant](hyp:hL), [the original propensity lies between zero and one](hyp:hp),
[the perturbed propensity does too](hyp:hp'), [the error tolerance is nonnegative](hyp:he0),
and [the propensity difference is uniformly bounded by that tolerance](hyp:he),
then [either evaluation index, the clamped policy propensity or the baseline
propensity, changes by at most the tolerance times the sum of one and the Lipschitz constant
at every instrument-covariate pair](goal). -/
lemma evaluation_indices_uniform_perturbation (phi : Z → X → ℝ → ℝ)
    (L : ℝ) (hL : PolicyLipschitz phi L) (p p' : Z → X → ℝ)
    (hp : ∀ z x, p z x ∈ Icc (0 : ℝ) 1)
    (hp' : ∀ z x, p' z x ∈ Icc (0 : ℝ) 1)
    (e : ℝ) (he0 : 0 ≤ e) (he : ∀ z x, |p' z x - p z x| ≤ e)
    (ell : Fin 2) (z : Z) (x : X) :
    |evalIndex phi p' ell z x - evalIndex phi p ell z x| ≤ (1 + L) * e := by
  unfold evalIndex
  split_ifs
  · exact clamp_policy_uniform_perturbation phi L hL p p' hp hp' e he0 he z x
  · exact (he z x).trans (by nlinarith [mul_nonneg hL.1 he0])

-- @node: population_evaluation_indices_in_support
/-- [Both population evaluation indices, the clamped policy propensity and the
baseline propensity, lie in the conditional propensity support interval at every
instrument-covariate pair](goal). -/
lemma population_evaluation_indices_in_support (M : LatentIVModel Ω X Z)
    (phi : Z → X → ℝ → ℝ) (ell : Fin 2) (z : Z) (x : X) :
    evalIndex phi M.prop ell z x ∈ supportInterval M x := by
  have hs := propensity_support_endpoints M.prop M.rangeProp x
  unfold evalIndex
  split_ifs
  · exact ⟨le_min hs.2.2 (le_max_left _ _), min_le_left _ _⟩
  · exact ⟨csInf_le ⟨0, by rintro _ ⟨z, rfl⟩; exact (M.rangeProp z x).1⟩
      (mem_range_self z),
      le_csSup ⟨1, by rintro _ ⟨z, rfl⟩; exact (M.rangeProp z x).2⟩
        (mem_range_self z)⟩

-- @node: selected_propensity_localization
/-- If [the original propensity lies between zero and one](hyp:hp), [the perturbed
propensity does too](hyp:hp'), [their difference is uniformly bounded by an error
tolerance](hyp:he), and [the selected perturbed propensity is at most a given margin
above its lower support endpoint](hyp:hsel), then [the original propensity lies
between its own lower support endpoint and that endpoint plus the margin and twice
the error tolerance](goal). -/
lemma selected_propensity_localization (p p' : Z → X → ℝ)
    (hp : ∀ z x, p z x ∈ Icc (0 : ℝ) 1)
    (hp' : ∀ z x, p' z x ∈ Icc (0 : ℝ) 1)
    (e : ℝ) (he : ∀ z x, |p' z x - p z x| ≤ e)
    (delta : ℝ) (z : Z) (x : X) (hsel : p' z x ≤ pLow p' x + delta) :
    pLow p x ≤ p z x ∧ p z x ≤ pLow p x + delta + 2 * e := by
  have hs := (abs_le.mp
    (propensity_support_uniform_perturbation p p' hp hp' e he x).1).2
  have hd := (abs_le.mp (he z x)).1
  refine ⟨csInf_le ⟨0, ?_⟩ (mem_range_self z), ?_⟩
  · rintro _ ⟨z, rfl⟩
    exact (hp z x).1
  · linarith

-- @node: projected_regression_error_bound
/-- Under [the model's structural assumptions](hyp:h), [known outcome support
endpoints](hyp:hend), [a policy uniformly Lipschitz in propensity with a nonnegative
constant](hyp:hL), [a fitted propensity taking values between zero and one](hyp:hp),
[a nonnegative error tolerance](hyp:he0), and [a uniform bound by that tolerance on
the fitted propensity's deviation from the true propensity](hyp:he), [for almost
every covariate value and every evaluation-index choice and instrument value, the
regression error relative to the canonical regression at the population index is
at most its error relative to the canonical regression at the projected fitted
index, plus the product of the maximum absolute outcome endpoint, the tolerance,
and the sum of one and the policy Lipschitz constant](goal). -/
lemma projected_regression_error_bound (M : LatentIVModel Ω X Z)
    (h : StructuralAssumptions M) (hend : OutcomeEndpointsKnown M)
    (phi : Z → X → ℝ → ℝ) (L : ℝ) (hL : PolicyLipschitz phi L)
    (p : Z → X → ℝ) (hp : ∀ z x, p z x ∈ Icc (0 : ℝ) 1)
    (g : ℝ → X → ℝ) (e : ℝ) (he0 : 0 ≤ e)
    (he : ∀ z x, |p z x - M.prop z x| ≤ e) :
    ∀ᵐ x ∂xLaw M, ∀ ell z,
      |g (evalIndex phi p ell z x) x - g1 M (evalIndex phi M.prop ell z x) x| ≤
        |g (evalIndex phi p ell z x) x -
          g1 M (supportProjection M x (evalIndex phi p ell z x)) x| +
        outcomeMagnitude M * ((1 + L) * e) := by
  filter_upwards [canonical_regression_lipschitz M h hend] with x hx
  intro ell z
  have hu := population_evaluation_indices_in_support M phi ell z x
  have hproj := (support_projection_range M x (evalIndex phi p ell z x)).2
  have hsub := (support_projection_range M x 0).1
  have hlip := hx _ (hsub hproj) _ (hsub hu)
  have hdist := (support_projection_nonexpansive_at_support M x
    (evalIndex phi p ell z x) (evalIndex phi M.prop ell z x) hu).trans
      (evaluation_indices_uniform_perturbation phi L hL M.prop p M.rangeProp hp e he0 he ell z x)
  have hC : 0 ≤ outcomeMagnitude M := (abs_nonneg M.yMin).trans (le_max_left _ _)
  calc
    _ ≤ |g (evalIndex phi p ell z x) x -
          g1 M (supportProjection M x (evalIndex phi p ell z x)) x| +
        |g1 M (supportProjection M x (evalIndex phi p ell z x)) x -
          g1 M (evalIndex phi M.prop ell z x) x| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add le_rfl (hlip.trans (mul_le_mul_of_nonneg_left hdist hC))

end Papers.TbsPrteOptimalTransport
