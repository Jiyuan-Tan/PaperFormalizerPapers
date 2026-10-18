module
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousBandAdmissiblePropensity
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousBandIndicatorJoint
/-! Propensity cancellation retaining jointly moving continuous quantile thresholds. -/
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

-- @node: continuous_admissible_boundary_values_regular
/-- For [an admissible continuous nuisance specification](hyp:he), [the upper
and lower boundary probability functions at every pair of indices are measurable
and bounded in absolute value by one almost surely](goal). -/
lemma continuous_admissible_boundary_values_regular (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e) (k j : ℕ) :
    (Measurable (boundaryValue e.Mplus k j) ∧
      ∀ᵐ x ∂xLaw M, |boundaryValue e.Mplus k j x| ≤ 1) ∧
    (Measurable (minusBoundaryValue e.Mminus k j) ∧
      ∀ᵐ x ∂xLaw M, |minusBoundaryValue e.Mminus k j x| ≤ 1) := by
  rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hp, hpm, hn, hnm, _⟩
  constructor
  · unfold boundaryValue
    split_ifs with h
    · refine ⟨hpm ⟨(k,j),h⟩, ?_⟩
      filter_upwards [hp ⟨(k,j),h⟩] with x hx
      simpa only [abs_of_nonneg hx.1] using hx.2
    · exact ⟨measurable_const, Eventually.of_forall fun _ => by norm_num⟩
    · exact ⟨measurable_const, Eventually.of_forall fun _ => by norm_num⟩
  · unfold minusBoundaryValue
    split_ifs with h
    · refine ⟨hnm ⟨(k,j),h⟩, ?_⟩
      filter_upwards [hn ⟨(k,j),h⟩] with x hx
      simpa only [abs_of_nonneg hx.1] using hx.2
    · exact ⟨measurable_const, Eventually.of_forall fun _ => by norm_num⟩
    · exact ⟨measurable_const, Eventually.of_forall fun _ => by norm_num⟩

-- @node: continuous_admissible_alphaHigh_measurable
/-- For [an admissible continuous nuisance specification](hyp:he), [the upper
propensity representer at every pair of indices is measurable in covariates](goal). -/
@[fun_prop] lemma continuous_admissible_alphaHigh_measurable (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e) (k j : ℕ) :
    Measurable (alphaHigh M L e k j) := by
  have hmJ := continuous_admissible_meanValue_measurable M L e he k j
  have hma := continuous_admissible_nuValue_measurable M L e he k j
  have hmb := continuous_admissible_nuValue_measurable M L e he k (j+1)
  have hmA := (continuous_admissible_boundary_values_regular M L e he k j).1.1
  have hmB := (continuous_admissible_boundary_values_regular M L e he k (j+1)).1.1
  unfold alphaHigh
  fun_prop

-- @node: continuous_admissible_alphaLow_measurable
/-- For [an admissible continuous nuisance specification](hyp:he), [the lower
propensity representer at every pair of indices is measurable in covariates](goal). -/
@[fun_prop] lemma continuous_admissible_alphaLow_measurable (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e) (k j : ℕ) :
    Measurable (alphaLow M L e k j) := by
  have hmJ := continuous_admissible_minusMeanValue_measurable M L e he k j
  have hma := continuous_admissible_nuValue_measurable M L e he k j
  have hmb := continuous_admissible_nuValue_measurable M L e he k (j+1)
  have hmA := (continuous_admissible_boundary_values_regular M L e he k j).2.1
  have hmB := (continuous_admissible_boundary_values_regular M L e he k (j+1)).2.1
  unfold alphaLow
  fun_prop

-- The clipped ranges bound representers even when both quantile endpoints move.
-- @node: continuous_admissible_alpha_abs_bounds
/-- For [an admissible continuous nuisance specification](hyp:he), [both the
upper and lower propensity representers are bounded in absolute value almost
surely by five times the sum of the absolute outcome endpoints](goal). -/
lemma continuous_admissible_alpha_abs_bounds (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e) (k j : ℕ) :
    (∀ᵐ x ∂xLaw M, |alphaHigh M L e k j x| ≤ 5 * (|M.yMin| + |M.yMax|)) ∧
    (∀ᵐ x ∂xLaw M, |alphaLow M L e k j x| ≤ 5 * (|M.yMin| + |M.yMax|)) := by
  have hJ := continuous_admissible_band_means_abs_bound M L e he k j
  have ha := continuous_admissible_nuValue_abs_bound M L e he k j
  have hb := continuous_admissible_nuValue_abs_bound M L e he k (j+1)
  have hA := continuous_admissible_boundary_values_regular M L e he k j
  have hB := continuous_admissible_boundary_values_regular M L e he k (j+1)
  have hC : 0 ≤ |M.yMin| + |M.yMax| := by positivity
  have hi : |indicator (1 ≤ j)| ≤ 1 := by unfold indicator; split_ifs <;> norm_num
  constructor
  · filter_upwards [hJ.1, ha, hb, hA.1.2, hB.1.2] with x hJx hax hbx hAx hBx
    have hpa := mul_le_mul hax hAx (abs_nonneg _) hC
    have hpb := mul_le_mul hbx hBx (abs_nonneg _) hC
    have h1 := abs_add_le (meanValue e.Jplus k j x)
      (nuValue M e k j x * boundaryValue e.Mplus k j x)
    have h2 := abs_sub (meanValue e.Jplus k j x + nuValue M e k j x * boundaryValue e.Mplus k j x)
      (nuValue M e k (j+1) x * boundaryValue e.Mplus k (j+1) x)
    simp only [abs_mul, mul_one] at h1 h2 hpa hpb
    unfold alphaHigh
    linarith
  · filter_upwards [hJ.2, ha, hb, hA.2.2, hB.2.2] with x hJx hax hbx hAx hBx
    have hpa := mul_le_mul hax hAx (abs_nonneg _) hC
    have hpb := mul_le_mul hbx hBx (abs_nonneg _) hC
    have hpi := mul_le_mul hi hax (abs_nonneg _) zero_le_one
    simp only [mul_one, one_mul] at hpa hpb hpi
    unfold alphaLow
    calc
      _ ≤ |minusMeanValue e.Jminus k j x| +
          |nuValue M e k j x| * |minusBoundaryValue e.Mminus k j x| +
          |nuValue M e k (j+1) x| * |minusBoundaryValue e.Mminus k (j+1) x| +
          |indicator (1 ≤ j)| * |nuValue M e k j x| + |nuValue M e k (j+1) x| := by
        have h1 := abs_sub (-minusMeanValue e.Jminus k j x)
          (nuValue M e k j x * minusBoundaryValue e.Mminus k j x)
        have h2 := abs_add_le
          (-minusMeanValue e.Jminus k j x - nuValue M e k j x * minusBoundaryValue e.Mminus k j x)
          (nuValue M e k (j+1) x * minusBoundaryValue e.Mminus k (j+1) x)
        have h3 := abs_add_le
          (-minusMeanValue e.Jminus k j x - nuValue M e k j x * minusBoundaryValue e.Mminus k j x +
            nuValue M e k (j+1) x * minusBoundaryValue e.Mminus k (j+1) x)
          (indicator (1 ≤ j) * nuValue M e k j x)
        have h4 := abs_sub
          (-minusMeanValue e.Jminus k j x - nuValue M e k j x * minusBoundaryValue e.Mminus k j x +
            nuValue M e k (j+1) x * minusBoundaryValue e.Mminus k (j+1) x +
            indicator (1 ≤ j) * nuValue M e k j x)
          (nuValue M e k (j+1) x)
        simp only [abs_neg, abs_mul] at h1 h2 h3 h4
        linarith
      _ ≤ _ := by linarith

-- @node: continuous_admissible_replace_propensity_regressions
/-- If [the original continuous nuisance specification is admissible](hyp:he)
and [a second specification is admissible](hyp:hb), then [replacing the original
level treatment propensities, upper and lower band means, and upper and lower
boundary probabilities by those of the second specification preserves
admissibility](goal). -/
lemma continuous_admissible_replace_propensity_regressions (L : LevelData Z X)
    (e b : NuisanceCont L) (he : ContAdmissible M L e) (hb : ContAdmissible M L b) :
    ContAdmissible M L {e with pLev := b.pLev, Jplus := b.Jplus, Jminus := b.Jminus, Mplus := b.Mplus, Mminus := b.Mminus} := by
  rcases he with ⟨e1, e2, _, _, e5, e6, e7, e8, e9, e10, e11, e12,
    e13, e14, e15, e16, e17, e18, _, _, _, _, _, _, _, _, e27, e28, e29, e30, e31⟩
  rcases hb with ⟨_, _, b3, b4, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    b19, b20, b21, b22, b23, b24, b25, b26, _, _, _, _, _⟩
  exact ⟨e1, e2, b3, b4, e5, e6, e7, e8, e9, e10, e11, e12,
    e13, e14, e15, e16, e17, e18, b19, b20, b21, b22, b23, b24, b25, b26,
    e27, e28, e29, e30, e31⟩

-- @node: population_continuous_band_moving_quantile_propensity_product_derivative
/-- With [baseline overlap at floor cpi](hyp:hov), consider [an admissible
direction from the true continuous nuisance specification](hyp:hd) and [a band
index below the number of bands at the chosen level](hyp:hj). Holding band means
and boundary probabilities at their true values along the affine path while
allowing quantile thresholds to move, [the difference between the band product
score and its version with true level treatment propensities has population
mean derivative zero at zero and is integrable for all sufficiently small
displacements](goal). -/
lemma population_continuous_band_moving_quantile_propensity_product_derivative
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (k : Fin L.K) (j : ℕ) (hj : j < L.l k) :
    let e := fun t : ℝ => {trueNuisance M L + t • del with
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
    Jplus := (trueNuisance M L).Jplus, Jminus := (trueNuisance M L).Jminus,
    Mplus := (trueNuisance M L).Mplus, Mminus := (trueNuisance M L).Mminus}
  let b := fun t => {e t with pLev := (trueNuisance M L).pLev}
  let w := fun t => regularValue (e t).gamma k (j+1)
  let W : ℝ := 1
  let vp := fun t x => w t x * (alphaHigh M L (b t) k j x *
    (positiveValue (trueNuisance M L + t • del).pLev (k+1) x -
      positiveValue (trueNuisance M L).pLev (k+1) x))
  let vm := fun t x => w t x * (if k.val = 0 then 0 else
    -alphaLow M L (b t) k j x *
      (positiveValue (trueNuisance M L + t • del).pLev k x -
        positiveValue (trueNuisance M L).pLev k x))
  obtain ⟨R, hR, hp⟩ := continuous_baseline_path_increment_regular M L del hd
  obtain ⟨C, hC, hpi⟩ := continuous_assignment_path_defect_regular M L del hd
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
      (∀ᵐ x ∂xLaw M, |vp t x| ≤ (W * (5 * (|M.yMin| + |M.yMax|) * R)) * |t|) ∧
      (∀ᵐ x ∂xLaw M, |vm t x| ≤ (W * (5 * (|M.yMin| + |M.yMax|) * R)) * |t|) ∧
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
    have hadb : ContAdmissible M L (b t) :=
      continuous_admissible_replace_propensity_regressions M L
        (trueNuisance M L + t • del) (trueNuisance M L) (hpath t hnear) horigin
    have hhi := (continuous_admissible_alpha_abs_bounds M L (b t) hadb k j).1
    have hlo := (continuous_admissible_alpha_abs_bounds M L (b t) hadb k j).2
    have hmhi := continuous_admissible_alphaHigh_measurable M L (b t) hadb k j
    have hmlo := continuous_admissible_alphaLow_measurable M L (b t) hadb k j
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
    have hBp : ∀ᵐ x ∂xLaw M, |vp t x| ≤ (W * (5 * (|M.yMin| + |M.yMax|) * R)) * |t| := by
      filter_upwards [ht.2, hhi, (hp t (k+1)).2] with x hx haX hpX
      dsimp only [vp]
      rw [abs_mul, abs_mul]
      calc
        _ ≤ W * ((5 * (|M.yMin| + |M.yMax|)) * (R * |t|)) := by
          gcongr
        _ = _ := by ring
    have hBm : ∀ᵐ x ∂xLaw M, |vm t x| ≤ (W * (5 * (|M.yMin| + |M.yMax|) * R)) * |t| := by
      filter_upwards [ht.2, hlo, (hp t k).2] with x hx haX hpX
      dsimp only [vm]
      split_ifs
      · simp only [mul_zero, abs_zero]
        dsimp only [W]
        positivity
      · rw [abs_mul, abs_mul, abs_neg]
        calc
          _ ≤ W * ((5 * (|M.yMin| + |M.yMax|)) * (R * |t|)) := by gcongr
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
    k j hj vp vm v (cpi/2) (W * (5 * (|M.yMin| + |M.yMax|) * R)) C (2 * R * B) G
    (div_pos hov.1 (by norm_num)) (by dsimp only [W]; positivity) hC
    (by dsimp only [B]; positivity) hG hlocal, ?_⟩
  filter_upwards [hlocal] with t ht
  rcases ht with ⟨hpiEq, hn, hJp, hJm, hMp, hMm, hprop, hshare, htau, hg, hvp, hvm,
    hpm, hvpm, hvmm, hclip, hBp, hBm, hden, hv, hvm', hgm, hve, hge⟩
  exact (population_continuous_band_joint_propensity_product_difference_bound M phi dphi L
    (e t) (b t) hpiEq hn hJp hJm hMp hMm hprop hshare htau k j hj (vp t) (vm t) hvp hvm
    hpm hvpm hvmm (cpi/2) (W * (5 * (|M.yMin| + |M.yMax|) * R)) C t
    (div_pos hov.1 (by norm_num)) (by dsimp only [W]; positivity) hC hclip hBp hBm hden hg (v t)
    hv hvm' hgm (2 * R * B) G (by dsimp only [B]; positivity) hG hve hge).1


-- The finite sum retains both the derivative and the integrability needed by
-- the next telescope in the total continuous score.
-- @node: population_continuous_regular_sum_moving_quantile_propensity_derivative
/-- With [baseline overlap at floor cpi](hyp:hov), consider [an admissible
direction from the true continuous nuisance specification](hyp:hd). Holding band
means and boundary probabilities at the truth along the affine path while
allowing quantile thresholds to move, [the sum over all regular bands of the
product score differences obtained by restoring true level treatment
propensities has population mean derivative zero at zero and is integrable
for all sufficiently small displacements](goal). -/
lemma population_continuous_regular_sum_moving_quantile_propensity_derivative
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del)) :
    let e := fun t : ℝ => {trueNuisance M L + t • del with
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
    Jplus := (trueNuisance M L).Jplus, Jminus := (trueNuisance M L).Jminus,
    Mplus := (trueNuisance M L).Mplus, Mminus := (trueNuisance M L).Mminus}
  let b := fun t => {e t with pLev := (trueNuisance M L).pLev}
  let f := fun (t : ℝ) (k : Fin L.K) (j : ℕ) (o : Obs X Z) =>
    psiProd M phi dphi L (e t) k (j+1) o - psiProd M phi dphi L (b t) k (j+1) o
  have hcomp (k : Fin L.K) (j : ℕ) (hj : j ∈ Finset.range (L.l k)) :
      HasDerivAt (fun t : ℝ => ∫ o, f t k j o ∂observationLaw M) 0 0 ∧
      ∀ᶠ t : ℝ in 𝓝 0, Integrable (f t k j) (observationLaw M) := by
    have hj' := Finset.mem_range.mp hj
    exact population_continuous_band_moving_quantile_propensity_product_derivative M
      phi dphi L cpi hov del hd k j hj'
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
