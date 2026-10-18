module
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousBandPropensityBias
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousBandQuantileRegressionAssembly
/-! Admissible-path envelopes and continuous band propensity cancellation. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false
set_option linter.style.longLine false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- The same bound includes the structural zero and out-of-family coordinates.
-- @node: continuous_baseline_path_increment_regular
/-- Along [an admissible continuous nuisance direction from the truth](hyp:hd),
[there is a nonnegative constant uniformly bounding every baseline propensity
level increment in absolute value by that constant times the absolute path
parameter, almost everywhere in covariates; each increment is measurable for
every parameter and level index, including indices outside the level family](goal). -/
lemma continuous_baseline_path_increment_regular (L : LevelData Z X)
    (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del)) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ t : ℝ, ∀ i : ℕ,
      Measurable (fun x => positiveValue (trueNuisance M L + t • del).pLev i x -
        positiveValue (trueNuisance M L).pLev i x) ∧
      ∀ᵐ x ∂xLaw M, |positiveValue (trueNuisance M L + t • del).pLev i x -
        positiveValue (trueNuisance M L).pLev i x| ≤ R * |t| := by
  obtain ⟨R, hR, hp⟩ := continuous_baseline_direction_regular M L (trueNuisance M L) del hd
  refine ⟨R, hR, ?_⟩
  intro t i
  by_cases hi : 1 ≤ i ∧ i ≤ L.K
  · have heq : (fun x => positiveValue (trueNuisance M L + t • del).pLev i x -
        positiveValue (trueNuisance M L).pLev i x) = fun x => t * del.pLev ⟨i, hi⟩ x := by
      funext x
      simp only [positiveValue, dif_pos hi]
      change _ + t * _ - _ = _
      ring
    rw [heq]
    refine ⟨(hp ⟨i,hi⟩).1.const_mul t, ?_⟩
    filter_upwards [(hp ⟨i,hi⟩).2] with x hx
    rw [congrFun heq x, abs_mul, mul_comm R]
    exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hx) (abs_nonneg t)
  · simp only [positiveValue, dif_neg hi, sub_self, abs_zero]
    exact ⟨measurable_const, Eventually.of_forall (fun _ => by positivity)⟩

-- The fitted assignment probability differs from its population mass by t*dpi.
-- @node: continuous_assignment_path_defect_regular
/-- Along [an admissible continuous nuisance direction from the truth](hyp:hd),
[there is a nonnegative constant such that, for every path parameter and positive
level index, the absolute difference between the fitted assignment probability
and the true conditional mass of that level's instrument set is almost everywhere
bounded by the constant times the absolute path parameter](goal). -/
lemma continuous_assignment_path_defect_regular (L : LevelData Z X)
    (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ∀ i, 1 ≤ i → i ≤ L.K →
      ∀ᵐ x ∂xLaw M,
        |positiveValue (trueNuisance M L + t • del).piLev i x -
          ∑ z ∈ L.S i, instProb M z x| ≤ C * |t| := by
  obtain ⟨C, hC, hp⟩ := continuous_assignment_direction_regular M L (trueNuisance M L) del hd
  refine ⟨C, hC, ?_⟩
  intro t i hi hK
  filter_upwards [(hp ⟨i,hi,hK⟩).2] with x hx
  have heq : positiveValue (trueNuisance M L + t • del).piLev i x -
      ∑ z ∈ L.S i, instProb M z x = t * del.piLev ⟨i,hi,hK⟩ x := by
    simp only [positiveValue, dif_pos (show 1 ≤ i ∧ i ≤ L.K from ⟨hi,hK⟩)]
    change (levelSetProb M L).1 i x + t * _ - _ = _
    simp only [levelSetProb]
    ring
  rw [heq, abs_mul, mul_comm C]
  exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hx) (abs_nonneg t)

-- @node: continuous_admissible_meanValue_measurable
/-- For [an admissible continuous nuisance specification](hyp:he), [the plus-side
band outcome mean is measurable in covariates at every level and band index](goal). -/
@[fun_prop] lemma continuous_admissible_meanValue_measurable (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e) (k j : ℕ) :
    Measurable (meanValue e.Jplus k j) := by
  first | fun_prop | skip
  rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _⟩
  unfold meanValue
  split_ifs
  · exact hm _
  · fun_prop

-- @node: continuous_admissible_minusMeanValue_measurable
/-- For [an admissible continuous nuisance specification](hyp:he), [the minus-side
band outcome mean is measurable in covariates at every level and band index](goal). -/
@[fun_prop] lemma continuous_admissible_minusMeanValue_measurable (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e) (k j : ℕ) :
    Measurable (minusMeanValue e.Jminus k j) := by
  first | fun_prop | skip
  rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _⟩
  unfold minusMeanValue
  split_ifs
  · exact hm _
  · fun_prop

-- The clipped signed regression ranges also cover the zero minus-side boundary.
-- @node: continuous_admissible_band_means_abs_bound
/-- For [an admissible continuous nuisance specification](hyp:he), [both the
plus-side and minus-side band outcome means are almost everywhere bounded in
absolute value by the sum of the absolute outcome endpoints, at every level
and band index](goal). -/
lemma continuous_admissible_band_means_abs_bound (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e) (k j : ℕ) :
    (∀ᵐ x ∂xLaw M, |meanValue e.Jplus k j x| ≤ |M.yMin| + |M.yMax|) ∧
    (∀ᵐ x ∂xLaw M, |minusMeanValue e.Jminus k j x| ≤ |M.yMin| + |M.yMax|) := by
  rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hp, _, hm, _⟩
  have bound (a : ℝ) (ha : a ∈ Icc (min 0 M.yMin) (max 0 M.yMax)) :
      |a| ≤ |M.yMin| + |M.yMax| := by
    apply abs_le.mpr
    constructor
    · have hmin : -(|M.yMin| + |M.yMax|) ≤ min 0 M.yMin := by
        apply le_min <;> nlinarith [neg_abs_le M.yMin, abs_nonneg M.yMin, abs_nonneg M.yMax]
      exact hmin.trans ha.1
    · have hmax : max 0 M.yMax ≤ |M.yMin| + |M.yMax| := by
        apply max_le <;> nlinarith [le_abs_self M.yMax, abs_nonneg M.yMin, abs_nonneg M.yMax]
      exact ha.2.trans hmax
  constructor
  · unfold meanValue
    split_ifs with hi
    · exact (hp ⟨(k,j),hi⟩).mono (fun _ hx => bound _ hx)
    · exact Eventually.of_forall (fun _ => by simp only [abs_zero]; positivity)
  · unfold minusMeanValue
    split_ifs with hi
    · exact (hm ⟨(k,j),hi⟩).mono (fun _ hx => bound _ hx)
    · exact Eventually.of_forall (fun _ => by simp only [abs_zero]; positivity)

-- Freeze the quantiles and J/M fields after their separately proved cancellation.
-- Every remaining field, including policy shares and denominators, still moves.
-- @node: population_continuous_band_admissible_propensity_derivative
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[a level partition preserving baseline and policy propensity order](hyp:hL), and
[baseline overlap at the specified positive bound](hyp:hov), consider [an admissible
continuous direction from the true nuisance](hyp:hd) and [a band within its
level](hyp:hj) with [measurable lower](hyp:ha) and [upper boundaries](hyp:hb).
For [a nonnegative weight bound](hyp:hW) and [weights that are measurable and
almost everywhere uniformly bounded by it near zero](hyp:hw), [the population
weighted band score difference has derivative zero at zero when comparing the
path with quantiles and band regressions fixed at truth to the same path with
baseline propensity levels also fixed at truth](goal). -/
lemma population_continuous_band_admissible_propensity_derivative
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (k : Fin L.K) (j : ℕ) (hj : j < L.l k)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j+1)))
    (w : ℝ → X → ℝ) (W : ℝ) (hW : 0 ≤ W)
    (hw : ∀ᶠ t : ℝ in 𝓝 0, Measurable (w t) ∧ ∀ᵐ x ∂xLaw M, |w t x| ≤ W) :
    let e := fun t : ℝ => {trueNuisance M L + t • del with
      nu := (trueNuisance M L).nu,
      Jplus := (trueNuisance M L).Jplus, Jminus := (trueNuisance M L).Jminus,
      Mplus := (trueNuisance M L).Mplus, Mminus := (trueNuisance M L).Mminus}
    let b := fun t => {e t with pLev := (trueNuisance M L).pLev}
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z, w t o.1 *
      (contScoreComponents M phi dphi L (e t) k j o -
        contScoreComponents M phi dphi L (b t) k j o) ∂observationLaw M) 0 0 := by
  dsimp only
  let e := fun t : ℝ => {trueNuisance M L + t • del with
    nu := (trueNuisance M L).nu,
    Jplus := (trueNuisance M L).Jplus, Jminus := (trueNuisance M L).Jminus,
    Mplus := (trueNuisance M L).Mplus, Mminus := (trueNuisance M L).Mminus}
  let b := fun t => {e t with pLev := (trueNuisance M L).pLev}
  let vp := fun t x => w t x * (alphaHigh M L (trueNuisance M L) k j x *
    (positiveValue (trueNuisance M L + t • del).pLev (k+1) x -
      positiveValue (trueNuisance M L).pLev (k+1) x))
  let vm := fun t x => w t x * (if k.val = 0 then 0 else
    -alphaLow M L (trueNuisance M L) k j x *
      (positiveValue (trueNuisance M L + t • del).pLev k x -
        positiveValue (trueNuisance M L).pLev k x))
  obtain ⟨R, hR, hp⟩ := continuous_baseline_path_increment_regular M L del hd
  obtain ⟨C, hC, hpi⟩ := continuous_assignment_path_defect_regular M L del hd
  have hmag : 0 ≤ outcomeMagnitude M := (abs_nonneg M.yMin).trans (le_max_left _ _)
  have hhi := population_continuous_alphaHigh_norm_bound M h he _ L hL k j k.isLt hj
  have hlo := population_continuous_alphaLow_norm_bound M h he _ L hL k j k.isLt hj
  have hmhi := population_continuous_band_alphaHigh_measurable M L k j k.isLt hj ha hb
  have hmlo := population_continuous_band_alphaLow_measurable M L k j k.isLt hj ha hb
  have he0 : e 0 = b 0 := by
    dsimp only [e, b]
    simp only [continuous_nuisance_path_zero]
  apply population_continuous_band_joint_propensity_derivative M phi dphi L e b he0
    k j hj w vp vm (cpi/2) (W * (5 * outcomeMagnitude M * R)) C
    (div_pos hov.1 (by norm_num)) (by positivity) hC
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  filter_upwards [hw, continuous_assignment_path_uniform_lower_bound M L cpi hov del hd,
    continuousAt_id.abs.eventually_lt_const (by simpa using hr)] with t ht hclip hnear
  have hmw := ht.1
  have hmPi : ∀ a, Measurable ((b t).piLev a) := (hpath t hnear).2.2.2.2.2.1
  have hmp : Measurable (vp t) := by
    have hmInc := (hp t (k+1)).1
    dsimp only [vp]
    fun_prop
  have hmm : Measurable (vm t) := by
    have hmInc := (hp t k).1
    dsimp only [vm]
    split_ifs <;> fun_prop
  have hBp : ∀ᵐ x ∂xLaw M, |vp t x| ≤ (W * (5 * outcomeMagnitude M * R)) * |t| := by
    filter_upwards [ht.2, hhi, (hp t (k+1)).2] with x hx haX hpX
    simp only [Real.norm_eq_abs] at haX
    dsimp only [vp]
    rw [abs_mul, abs_mul]
    calc
      _ ≤ W * ((5 * outcomeMagnitude M) * (R * |t|)) := by
        gcongr
        exact haX.trans (by nlinarith)
      _ = _ := by ring
  have hBm : ∀ᵐ x ∂xLaw M, |vm t x| ≤ (W * (5 * outcomeMagnitude M * R)) * |t| := by
    filter_upwards [ht.2, hlo, (hp t k).2] with x hx haX hpX
    simp only [Real.norm_eq_abs] at haX
    dsimp only [vm]
    split_ifs
    · simp only [mul_zero, abs_zero]
      positivity
    · rw [abs_mul, abs_mul, abs_neg]
      calc
        _ ≤ W * ((5 * outcomeMagnitude M) * (R * |t|)) := by gcongr
        _ = _ := by ring
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_,
    hmPi, hmp, hmm, hclip, hBp, hBm, hpi t⟩
  · intro x
    rfl
  · intro x
    rfl

-- The product-score residual contributes only a weight-error times propensity-error.
-- @node: population_continuous_band_admissible_propensity_product_derivative
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[a level partition preserving baseline and policy propensity order](hyp:hL), and
[baseline overlap at the specified positive bound](hyp:hov), take [an admissible
continuous direction from truth](hyp:hd) and [a band within its level](hyp:hj)
with [measurable lower](hyp:ha) and [upper boundaries](hyp:hb). [The population
product-score difference between the path with quantiles and band regressions
fixed at truth and the same path with baseline propensity levels additionally
fixed has derivative zero at zero, and this score difference is integrable for
all sufficiently small path parameters](goal). -/
lemma population_continuous_band_admissible_propensity_product_derivative
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (k : Fin L.K) (j : ℕ) (hj : j < L.l k)
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j+1))) :
    let e := fun t : ℝ => {trueNuisance M L + t • del with
      nu := (trueNuisance M L).nu,
      Jplus := (trueNuisance M L).Jplus, Jminus := (trueNuisance M L).Jminus,
      Mplus := (trueNuisance M L).Mplus, Mminus := (trueNuisance M L).Mminus}
    let b := fun t => {e t with pLev := (trueNuisance M L).pLev}
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
      psiProd M phi dphi L (e t) k (j+1) o -
        psiProd M phi dphi L (b t) k (j+1) o ∂observationLaw M) 0 0 ∧
    (∀ᶠ t : ℝ in 𝓝 0, Integrable (fun o =>
      psiProd M phi dphi L (e t) k (j+1) o -
        psiProd M phi dphi L (b t) k (j+1) o) (observationLaw M)) := by
  dsimp only
  let e := fun t : ℝ => {trueNuisance M L + t • del with
    nu := (trueNuisance M L).nu,
    Jplus := (trueNuisance M L).Jplus, Jminus := (trueNuisance M L).Jminus,
    Mplus := (trueNuisance M L).Mplus, Mminus := (trueNuisance M L).Mminus}
  let b := fun t => {e t with pLev := (trueNuisance M L).pLev}
  let w := fun t => regularValue (e t).gamma k (j+1)
  let W : ℝ := 1
  let vp := fun t x => w t x * (alphaHigh M L (trueNuisance M L) k j x *
    (positiveValue (trueNuisance M L + t • del).pLev (k+1) x -
      positiveValue (trueNuisance M L).pLev (k+1) x))
  let vm := fun t x => w t x * (if k.val = 0 then 0 else
    -alphaLow M L (trueNuisance M L) k j x *
      (positiveValue (trueNuisance M L + t • del).pLev k x -
        positiveValue (trueNuisance M L).pLev k x))
  obtain ⟨R, hR, hp⟩ := continuous_baseline_path_increment_regular M L del hd
  obtain ⟨C, hC, hpi⟩ := continuous_assignment_path_defect_regular M L del hd
  have hmag : 0 ≤ outcomeMagnitude M := (abs_nonneg M.yMin).trans (le_max_left _ _)
  have hhi := population_continuous_alphaHigh_norm_bound M h he _ L hL k j k.isLt hj
  have hlo := population_continuous_alphaLow_norm_bound M h he _ L hL k j k.isLt hj
  have hmhi := population_continuous_band_alphaHigh_measurable M L k j k.isLt hj ha hb
  have hmlo := population_continuous_band_alphaLow_measurable M L k j k.isLt hj ha hb
  have he0 : e 0 = b 0 := by
    dsimp only [e, b]
    simp only [continuous_nuisance_path_zero]
  obtain ⟨G, hG, hgamma⟩ := continuous_regular_weight_direction_regular M L (trueNuisance M L) del hd
  have horigin : ContAdmissible M L (trueNuisance M L) := by
    obtain ⟨r, hr, hp⟩ := hd.admissible
    have hzero := hp 0 (by simpa using hr)
    rwa [continuous_nuisance_path_zero] at hzero
  have hmJp := continuous_admissible_meanValue_measurable M L _ horigin k j
  have hmJm := continuous_admissible_minusMeanValue_measurable M L _ horigin k j
  have hJ := continuous_admissible_band_means_abs_bound M L _ horigin k j
  let B : ℝ := |M.yMin| + |M.yMax|
  let v := fun t x => contJ L (e t) k j x - contJ L (b t) k j x
  have hvId (t : ℝ) : v t = fun x =>
      (positiveValue (trueNuisance M L + t • del).pLev (k+1) x -
        positiveValue (trueNuisance M L).pLev (k+1) x) * meanValue (trueNuisance M L).Jplus k j x -
      (positiveValue (trueNuisance M L + t • del).pLev k x -
        positiveValue (trueNuisance M L).pLev k x) * minusMeanValue (trueNuisance M L).Jminus k j x := by
    funext x
    dsimp only [v, e, b, contJ]
    ring
  have hi : k.val ≤ L.K ∧ 1 ≤ j+1 ∧ j+1 ≤ L.l k := by omega
  have hge (t : ℝ) : ∀ᵐ x ∂xLaw M,
      |(∑ z ∈ policyUnion L k (j+1), instProb M z x) - w t x| ≤ G * |t| := by
    filter_upwards [(hgamma ⟨(k,j+1),hi⟩).2] with x hx
    have hid : (∑ z ∈ policyUnion L k (j+1), instProb M z x) - w t x =
        -(t * del.gamma ⟨(k,j+1),hi⟩ x) := by
      simp only [w, e, regularValue, dif_pos hi]
      change _ - ((trueNuisance M L).gamma ⟨(k,j+1),hi⟩ x + t * _) = _
      simp only [trueNuisance, gamma]
      ring
    rw [hid, abs_neg, abs_mul, mul_comm G]
    exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hx) (abs_nonneg t)
  have hlocal : ∀ᶠ t : ℝ in 𝓝 0,
      (e t).piLev = (b t).piLev ∧ (e t).nu = (b t).nu ∧
      (e t).Jplus = (b t).Jplus ∧ (e t).Jminus = (b t).Jminus ∧
      (e t).Mplus = (b t).Mplus ∧ (e t).Mminus = (b t).Mminus ∧ (e t).prop = (b t).prop ∧
      (e t).share = (b t).share ∧ (e t).tauLev = (b t).tauLev ∧
      (e t).gamma = (b t).gamma ∧
      (∀ x, vp t x = regularValue (e t).gamma k (j+1) x *
        (alphaHigh M L (b t) k j x *
          (positiveValue (e t).pLev (k+1) x - positiveValue (b t).pLev (k+1) x))) ∧
      (∀ x, vm t x = regularValue (e t).gamma k (j+1) x *
        (if k.val = 0 then 0 else -alphaLow M L (b t) k j x *
          (positiveValue (e t).pLev k x - positiveValue (b t).pLev k x))) ∧
      (∀ a, Measurable ((b t).piLev a)) ∧ Measurable (vp t) ∧ Measurable (vm t) ∧
      (∀ a, ∀ᵐ x ∂xLaw M, cpi/2 ≤ (b t).piLev a x) ∧
      (∀ᵐ x ∂xLaw M, |vp t x| ≤ (W * (5 * outcomeMagnitude M * R)) * |t|) ∧
      (∀ᵐ x ∂xLaw M, |vm t x| ≤ (W * (5 * outcomeMagnitude M * R)) * |t|) ∧
      (∀ i, 1 ≤ i → i ≤ L.K → ∀ᵐ x ∂xLaw M,
        |positiveValue (b t).piLev i x - ∑ z ∈ L.S i, instProb M z x| ≤ C * |t|) ∧
      (∀ x, v t x = contJ L (e t) k j x - contJ L (b t) k j x) ∧
      Measurable (v t) ∧ Measurable (regularValue (e t).gamma k (j+1)) ∧
      (∀ᵐ x ∂xLaw M, |v t x| ≤ (2 * R * B) * |t|) ∧
      (∀ᵐ x ∂xLaw M,
        |(∑ z ∈ policyUnion L k (j+1), instProb M z x) -
          regularValue (e t).gamma k (j+1) x| ≤ G * |t|) := by
    obtain ⟨r, hr, hpath⟩ := hd.admissible
    have hw : ∀ᶠ t : ℝ in 𝓝 0, Measurable (w t) ∧ ∀ᵐ x ∂xLaw M, |w t x| ≤ W := by
      filter_upwards [continuousAt_id.abs.eventually_lt_const (by simpa using hr)] with t ht
      have had := hpath t ht
      change (Measurable (fun x => regularValue (trueNuisance M L + t • del).gamma k (j+1) x)) ∧ _
      simp only [regularValue, dif_pos hi]
      refine ⟨had.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _, ?_⟩
      filter_upwards [had.2.2.2.2.2.2.2.2.2.2.2.2.1 ⟨(k,j+1),hi⟩] with x hx
      simpa only [w, e, regularValue, dif_pos hi, W, abs_of_nonneg hx.1] using hx.2
    filter_upwards [hw, continuous_assignment_path_uniform_lower_bound M L cpi hov del hd,
      continuousAt_id.abs.eventually_lt_const (by simpa using hr)] with t ht hclip hnear
    have hmw := ht.1
    have hmPi : ∀ a, Measurable ((b t).piLev a) := (hpath t hnear).2.2.2.2.2.1
    have hmp : Measurable (vp t) := by
      have hmInc := (hp t (k+1)).1
      dsimp only [vp]
      fun_prop
    have hmm : Measurable (vm t) := by
      have hmInc := (hp t k).1
      dsimp only [vm]
      split_ifs <;> fun_prop
    have hBp : ∀ᵐ x ∂xLaw M, |vp t x| ≤ (W * (5 * outcomeMagnitude M * R)) * |t| := by
      filter_upwards [ht.2, hhi, (hp t (k+1)).2] with x hx haX hpX
      simp only [Real.norm_eq_abs] at haX
      dsimp only [vp]
      rw [abs_mul, abs_mul]
      calc
        _ ≤ W * ((5 * outcomeMagnitude M) * (R * |t|)) := by
          gcongr
          exact haX.trans (by nlinarith)
        _ = _ := by ring
    have hBm : ∀ᵐ x ∂xLaw M, |vm t x| ≤ (W * (5 * outcomeMagnitude M * R)) * |t| := by
      filter_upwards [ht.2, hlo, (hp t k).2] with x hx haX hpX
      simp only [Real.norm_eq_abs] at haX
      dsimp only [vm]
      split_ifs
      · simp only [mul_zero, abs_zero]
        dsimp only [W]
        positivity
      · rw [abs_mul, abs_mul, abs_neg]
        calc
          _ ≤ W * ((5 * outcomeMagnitude M) * (R * |t|)) := by gcongr
          _ = _ := by ring
    have hvm : Measurable (v t) := by
      rw [hvId]
      have hp1 := (hp t (k+1)).1
      have hp0 := (hp t k).1
      fun_prop
    have hve : ∀ᵐ x ∂xLaw M, |v t x| ≤ (2 * R * B) * |t| := by
      filter_upwards [(hp t (k+1)).2, (hp t k).2, hJ.1, hJ.2] with x hp1 hp0 hjp hjm
      rw [congrFun (hvId t) x]
      calc
        _ ≤ |(positiveValue (trueNuisance M L + t • del).pLev (k+1) x -
            positiveValue (trueNuisance M L).pLev (k+1) x) * meanValue (trueNuisance M L).Jplus k j x| +
          |(positiveValue (trueNuisance M L + t • del).pLev k x -
            positiveValue (trueNuisance M L).pLev k x) * minusMeanValue (trueNuisance M L).Jminus k j x| := abs_sub _ _
        _ ≤ (R * |t|) * B + (R * |t|) * B := by
          simp only [abs_mul]
          gcongr
        _ = _ := by ring
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_,
      hmPi, hmp, hmm, hclip, hBp, hBm, hpi t, (fun _ => rfl), hvm, ht.1, hve, hge t⟩
    · intro x
      rfl
    · intro x
      rfl

  refine ⟨population_continuous_band_joint_propensity_product_derivative M phi dphi L e b he0
    k j hj vp vm v (cpi/2) (W * (5 * outcomeMagnitude M * R)) C (2 * R * B) G
    (div_pos hov.1 (by norm_num)) (by dsimp only [W]; positivity) hC
    (by dsimp only [B]; positivity) hG hlocal, ?_⟩
  filter_upwards [hlocal] with t ht
  rcases ht with ⟨hpiEq, hn, hJp, hJm, hMp, hMm, hprop, hshare, htau, hg, hvp, hvm,
    hpm, hvpm, hvmm, hclip, hBp, hBm, hden, hv, hvm', hgm, hve, hge⟩
  exact (population_continuous_band_joint_propensity_product_difference_bound M phi dphi L
    (e t) (b t) hpiEq hn hJp hJm hMp hMm hprop hshare htau k j hj (vp t) (vm t) hvp hvm
    hpm hvpm hvmm (cpi/2) (W * (5 * outcomeMagnitude M * R)) C t
    (div_pos hov.1 (by norm_num)) (by dsimp only [W]; positivity) hC hclip hBp hBm hden hg (v t)
    hv hvm' hgm (2 * R * B) G (by dsimp only [B]; positivity) hG hve hge).1

-- The finite sum retains both the derivative and the integrability needed by
-- the next telescope in the total continuous score.
-- @node: population_continuous_regular_sum_admissible_propensity_derivative
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[a level partition preserving baseline and policy propensity order](hyp:hL),
[baseline overlap at the specified positive bound](hyp:hov), [an admissible
continuous direction from truth](hyp:hd), and [measurability of every band
boundary](hyp:hb), [the population sum of regular-band product-score differences
has derivative zero at zero and is integrable for all sufficiently small path
parameters, when comparing the path with quantiles and band regressions fixed
at truth to that path with baseline propensity levels additionally fixed](goal). -/
lemma population_continuous_regular_sum_admissible_propensity_derivative
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (hb : ∀ k j, k < L.K → j ≤ L.l k → Measurable (bandBoundary M L k j)) :
    let e := fun t : ℝ => {trueNuisance M L + t • del with
      nu := (trueNuisance M L).nu,
      Jplus := (trueNuisance M L).Jplus, Jminus := (trueNuisance M L).Jminus,
      Mplus := (trueNuisance M L).Mplus, Mminus := (trueNuisance M L).Mminus}
    let b := fun t => {e t with pLev := (trueNuisance M L).pLev}
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
      ∑ k : Fin L.K, ∑ j ∈ Finset.range (L.l k),
        (psiProd M phi dphi L (e t) k (j+1) o -
          psiProd M phi dphi L (b t) k (j+1) o) ∂observationLaw M) 0 0 ∧
    (∀ᶠ t : ℝ in 𝓝 0, Integrable (fun o : Obs X Z =>
      ∑ k : Fin L.K, ∑ j ∈ Finset.range (L.l k),
        (psiProd M phi dphi L (e t) k (j+1) o -
          psiProd M phi dphi L (b t) k (j+1) o)) (observationLaw M)) := by
  dsimp only
  let e := fun t : ℝ => {trueNuisance M L + t • del with
    nu := (trueNuisance M L).nu,
    Jplus := (trueNuisance M L).Jplus, Jminus := (trueNuisance M L).Jminus,
    Mplus := (trueNuisance M L).Mplus, Mminus := (trueNuisance M L).Mminus}
  let b := fun t => {e t with pLev := (trueNuisance M L).pLev}
  let f := fun (t : ℝ) (k : Fin L.K) (j : ℕ) (o : Obs X Z) =>
    psiProd M phi dphi L (e t) k (j+1) o - psiProd M phi dphi L (b t) k (j+1) o
  have hcomp (k : Fin L.K) (j : ℕ) (hj : j ∈ Finset.range (L.l k)) :
      HasDerivAt (fun t : ℝ => ∫ o, f t k j o ∂observationLaw M) 0 0 ∧
      ∀ᶠ t : ℝ in 𝓝 0, Integrable (f t k j) (observationLaw M) := by
    have hj' := Finset.mem_range.mp hj
    exact population_continuous_band_admissible_propensity_product_derivative M h he
      phi dphi L hL cpi hov del hd k j hj' (hb k j k.isLt hj'.le)
      (hb k (j+1) k.isLt (by omega))
  have hi : ∀ᶠ t : ℝ in 𝓝 0, ∀ k : Fin L.K, ∀ j ∈ Finset.range (L.l k),
      Integrable (f t k j) (observationLaw M) := by
    apply (Filter.eventually_all).mpr
    intro k
    exact (Finset.eventually_all _).mpr (fun j hj => (hcomp k j hj).2)
  have hdSum : HasDerivAt (fun t : ℝ => ∑ k : Fin L.K,
      ∑ j ∈ Finset.range (L.l k), ∫ o, f t k j o ∂observationLaw M) 0 0 := by
    have hdk (k : Fin L.K) : HasDerivAt (fun t : ℝ =>
        ∑ j ∈ Finset.range (L.l k), ∫ o, f t k j o ∂observationLaw M) 0 0 := by
      simpa only [Finset.sum_const_zero] using
        HasDerivAt.fun_sum (fun j hj => (hcomp k j hj).1)
    simpa only [Finset.sum_const_zero] using
      HasDerivAt.fun_sum (fun k (_ : k ∈ Finset.univ) => hdk k)
  refine ⟨hdSum.congr_of_eventuallyEq ?_, ?_⟩
  · filter_upwards [hi] with t ht
    symm
    rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (ht k))]
    apply Finset.sum_congr rfl
    intro k _
    exact (integral_finsetSum _ (ht k)).symm
  · filter_upwards [hi] with t ht
    exact integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (ht k))

end Papers.TbsPrteOptimalTransport
