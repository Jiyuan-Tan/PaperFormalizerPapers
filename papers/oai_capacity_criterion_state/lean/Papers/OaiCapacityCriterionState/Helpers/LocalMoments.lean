module

public import Papers.OaiCapacityCriterionState.Helpers.ThirdSymmetry

/-! # Local moment bounds for symmetric posterior experiments

Only the second law needs channel smoothing. The common constant depends on the
channel parameter alone; the lower bound for quadratic information also holds with seven.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace OaiCapacityCriterionState

-- @node: channel_coordinate_bounds
/-- If [the channel parameter is strictly between zero and one](hyp:hlam) and
[the posterior law is obtained by applying that channel to another posterior law](hyp:hchannel),
then [almost every posterior assigns each of the four states probability at least
one quarter of one minus the channel parameter](goal). -/
lemma channel_coordinate_bounds (lam : ℝ) (hlam : LocalMomentsLambda lam)
    (nu : PosteriorLaw) (hchannel : LocalMomentsChannel lam nu) :
    ∀ᵐ q ∂(nu : Measure (Fin 4 → ℝ)), ∀ i : Fin 4, (1 - lam) / 4 ≤ q i := by
  obtain ⟨nu0, hnu⟩ := hchannel
  rw [hnu, channelStep]
  have hmap : Measurable (channelPosterior lam) := by
    unfold channelPosterior
    fun_prop
  rw [ae_map_iff hmap.aemeasurable (by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i =>
      measurableSet_le measurable_const (measurable_pi_apply i))]
  have hs : ∀ᵐ p ∂(nu0 : Measure (Fin 4 → ℝ)), p ∈ stdSimplex ℝ (Fin 4) :=
    ae_iff.mpr nu0.property.2.1
  filter_upwards [hs] with p hp
  intro i
  have hpi := hp.1 i
  change (1 - lam) / 4 ≤ 1 / 4 + lam * (p i - 1 / 4)
  nlinarith [mul_nonneg hlam.1.le hpi]

-- @node: productZ_eq_one_add_coordinateDot
/-- For [a four-state probability vector p](hyp:hp) and
[a four-state probability vector q](hyp:hq), [the product normalizer equals one
plus the inner product of their posterior coordinate vectors](goal). -/
lemma productZ_eq_one_add_coordinateDot (p q : Fin 4 → ℝ)
    (hp : p ∈ stdSimplex ℝ (Fin 4)) (hq : q ∈ stdSimplex ℝ (Fin 4)) :
    productZ (p, q) = 1 + coordinateDot p q := by
  have hid : productZ (p, q) =
      (∑ i : Fin 4, p i) * (∑ i : Fin 4, q i) + coordinateDot p q := by
    simp [productZ, coordinateDot, postCoords, coordMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]
    ring
  simpa [hp.2, hq.2] using hid

-- @node: smoothed_product_bounds
/-- If [the channel parameter is strictly between zero and one](hyp:hlam) and
[the second posterior law is the channel image of another posterior law](hyp:hchannel),
then [for almost every independent pair of posteriors, their coordinate inner product
lies between minus the channel parameter and three, their product normalizer equals
one plus that inner product, and this normalizer is at least one minus the channel
parameter and is strictly positive](goal). -/
lemma smoothed_product_bounds (lam : ℝ) (hlam : LocalMomentsLambda lam)
    (mu nu : PosteriorLaw) (hchannel : LocalMomentsChannel lam nu) :
    ∀ᵐ pq ∂((mu : Measure (Fin 4 → ℝ)).prod (nu : Measure (Fin 4 → ℝ))),
      coordinateDot pq.1 pq.2 ∈ Set.Icc (-lam) 3 ∧ -- @realizes s(range [-lambda,3])
      productZ pq = 1 + coordinateDot pq.1 pq.2 ∧ -- @realizes Z(identity Z = 1 + s)
      1 - lam ≤ productZ pq ∧ -- @realizes Z(lower bound 1-lambda)
      0 < productZ pq := by -- @realizes Z(strictly positive denominator)
  have : IsProbabilityMeasure (mu : Measure (Fin 4 → ℝ)) := mu.property.1
  have : IsProbabilityMeasure (nu : Measure (Fin 4 → ℝ)) := nu.property.1
  have hmu : ∀ᵐ p ∂(mu : Measure (Fin 4 → ℝ)), p ∈ stdSimplex ℝ (Fin 4) :=
    ae_iff.mpr mu.property.2.1
  have hnu : ∀ᵐ q ∂(nu : Measure (Fin 4 → ℝ)), q ∈ stdSimplex ℝ (Fin 4) :=
    ae_iff.mpr nu.property.2.1
  have hp := (Measure.quasiMeasurePreserving_fst (ν := (nu : Measure (Fin 4 → ℝ)))).ae hmu
  have hq := (Measure.quasiMeasurePreserving_snd (μ := (mu : Measure (Fin 4 → ℝ)))).ae hnu
  have hc := (Measure.quasiMeasurePreserving_snd (μ := (mu : Measure (Fin 4 → ℝ)))).ae
    (channel_coordinate_bounds lam hlam nu hchannel)
  filter_upwards [hp, hq, hc] with pq hp hq hc
  have hid := productZ_eq_one_add_coordinateDot pq.1 pq.2 hp hq
  have hlo : 1 - lam ≤ productZ pq := by
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      mul_le_mul_of_nonneg_left (hc i) (hp.1 i))
    rw [← Finset.sum_mul, hp.2] at hsum
    dsimp [productZ]
    linarith
  have hhi : productZ pq ≤ 4 := by
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      mul_le_mul_of_nonneg_left (mem_Icc_of_mem_stdSimplex hq i).2 (hp.1 i))
    simp only [mul_one, hp.2] at hsum
    dsimp [productZ]
    linarith
  exact ⟨⟨by linarith, by linarith⟩, hid, hlo, by linarith [hlam.2]⟩

-- @node: thirdStat_abs_le_quadStat
/-- For [a probability vector on four states](hyp:hp), [the absolute product of its
three posterior coordinates is at most the sum of their squares](goal). -/
lemma thirdStat_abs_le_quadStat (p : Fin 4 → ℝ)
    (hp : p ∈ stdSimplex ℝ (Fin 4)) :
    |postCoords p 0 * postCoords p 1 * postCoords p 2| ≤ quadStat p := by
  have hz : |postCoords p 2| ≤ 1 := abs_le.mpr (postCoords_mem_Icc p hp 2)
  calc
    _ = |postCoords p 0| * |postCoords p 1| * |postCoords p 2| := by
      rw [abs_mul, abs_mul]
    _ ≤ |postCoords p 0| * |postCoords p 1| :=
      mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hz
    _ ≤ quadStat p := by
      have hs := sq_nonneg (|postCoords p 0| - |postCoords p 1|)
      simp only [quadStat, Fin.sum_univ_succ, Fin.isValue, Fin.succ_zero_eq_one,
        Fin.succ_one_eq_two, Finset.univ_unique, Fin.default_eq_zero,
        Finset.sum_singleton] at *
      nlinarith [sq_abs (postCoords p 0), sq_abs (postCoords p 1),
        sq_nonneg (postCoords p 2)]

-- @node: quadStat_integrable
/-- Under any posterior law, [the sum of squared posterior coordinates is integrable](goal). -/
lemma quadStat_integrable (mu : PosteriorLaw) :
    Integrable quadStat (mu : Measure (Fin 4 → ℝ)) := by
  let : IsProbabilityMeasure (mu : Measure (Fin 4 → ℝ)) := mu.property.1
  have hm : AEStronglyMeasurable quadStat (mu : Measure (Fin 4 → ℝ)) := by
    apply Continuous.aestronglyMeasurable
    unfold quadStat postCoords Matrix.mulVec dotProduct
    fun_prop
  apply (integrable_const (3 : ℝ)).mono' hm
  filter_upwards [ae_iff.mpr mu.property.2.1] with p hp
  simpa [Real.norm_eq_abs, abs_of_nonneg (quadStat_mem_Icc p hp).1] using
    (quadStat_mem_Icc p hp).2

-- @node: absThird_le_quadInfo
/-- For any posterior law, [the absolute value of the expected product of its three
posterior coordinates is at most its quadratic information](goal). -/
lemma absThird_le_quadInfo (mu : PosteriorLaw) : absThird mu ≤ quadInfo mu := by
  unfold absThird thirdMoment quadInfo
  rw [← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le (quadStat_integrable mu)
  filter_upwards [ae_iff.mpr mu.property.2.1] with p hp
  simpa only [Real.norm_eq_abs] using thirdStat_abs_le_quadStat p hp

-- @node: thirdMoment_product_abs_le
/-- For two posterior laws, [the absolute product of their signed third moments is
at most half the sum of each law's absolute third moment times the other law's
quadratic information](goal). -/
lemma thirdMoment_product_abs_le (mu nu : PosteriorLaw) :
    |thirdMoment mu * thirdMoment nu| ≤
      (absThird mu * quadInfo nu + quadInfo mu * absThird nu) / 2 := by
  rw [abs_mul]
  have hmu := absThird_le_quadInfo mu
  have hnu := absThird_le_quadInfo nu
  have h1 := mul_le_mul_of_nonneg_left hnu (abs_nonneg (thirdMoment mu))
  have h2 := mul_le_mul_of_nonneg_right hmu (abs_nonneg (thirdMoment nu))
  change |thirdMoment mu| ≤ quadInfo mu at hmu
  change |thirdMoment nu| ≤ quadInfo nu at hnu
  unfold absThird at *
  linarith

-- @node: quadratic_cancellation
/-- If [both posterior laws are symmetric](hyp:hsym), [the expectation under their
independent product of the squared length of the product coordinate numerator times
one minus the coordinate inner product equals a + b − 4(αb + aβ) − 6αβ, where
a and b are their quadratic informations and α and β are their signed third moments](goal). -/
lemma quadratic_cancellation (mu nu : PosteriorLaw)
    (hsym : LocalMomentsSymmetry mu nu) :
    let a := quadInfo mu -- @realizes a(the abbreviation m(mu), in [0,3])
    let b := quadInfo nu -- @realizes b(the abbreviation m(nu), in [0,3])
    let alpha := thirdMoment mu -- @realizes \alpha(the signed moment tau(mu))
    let beta := thirdMoment nu -- @realizes \beta(the signed moment tau(nu))
    (∫ pq, (∑ i : Fin 3, productNumerator pq.1 pq.2 i ^ 2) *
      (1 - coordinateDot pq.1 pq.2)
      ∂((mu : Measure (Fin 4 → ℝ)).prod (nu : Measure (Fin 4 → ℝ)))) =
    a + b - 4 * (alpha * b + a * beta) - 6 * alpha * beta := by
  let : IsProbabilityMeasure (mu : Measure (Fin 4 → ℝ)) := mu.property.1
  let : IsProbabilityMeasure (nu : Measure (Fin 4 → ℝ)) := nu.property.1
  change (∫ pq, quadraticIntegrand (postCoords pq.1) (postCoords pq.2)
      ∂((mu : Measure (Fin 4 → ℝ)).prod (nu : Measure (Fin 4 → ℝ)))) = _
  have hi : Integrable (fun pq => quadraticIntegrand (postCoords pq.1) (postCoords pq.2))
      ((mu : Measure (Fin 4 → ℝ)).prod (nu : Measure (Fin 4 → ℝ))) := by
    apply posterior_prod_continuous_integrable
    unfold quadraticIntegrand mixedCoords postCoords Matrix.mulVec dotProduct
    fun_prop
  rw [integral_prod _ hi]
  simp_rw [quadratic_integral_average nu hsym.2]
  calc
    _ = ∫ p, quadInfo nu + (1 - 4 * thirdMoment nu) * quadStat p +
        (-4 * quadInfo nu - 6 * thirdMoment nu) *
          (postCoords p 0 * postCoords p 1 * postCoords p 2)
        ∂(mu : Measure (Fin 4 → ℝ)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun p => by ring
    _ = _ := by
      rw [posterior_integral_affine_moments]
      ring

-- @node: quadratic_cancellation_lower_bound
/-- If [both posterior laws are symmetric](hyp:hsym), [the expected squared length
of the product coordinate numerator times one minus the coordinate inner product
is at least the sum of their quadratic informations minus seven times the sum of
each law's absolute third moment times the other law's quadratic information](goal). -/
lemma quadratic_cancellation_lower_bound (mu nu : PosteriorLaw)
    (hsym : LocalMomentsSymmetry mu nu) :
    quadInfo mu + quadInfo nu -
        7 * (absThird mu * quadInfo nu + quadInfo mu * absThird nu) ≤
      ∫ pq, (∑ i : Fin 3, productNumerator pq.1 pq.2 i ^ 2) *
        (1 - coordinateDot pq.1 pq.2)
        ∂((mu : Measure (Fin 4 → ℝ)).prod (nu : Measure (Fin 4 → ℝ))) := by
  rw [quadratic_cancellation mu nu hsym]
  have hcross := thirdMoment_product_abs_le mu nu
  have hmu := le_abs_self (thirdMoment mu)
  have hnu := le_abs_self (thirdMoment nu)
  have h1 := mul_le_mul_of_nonneg_right hmu (quadInfo_mem_Icc nu).1
  have h2 := mul_le_mul_of_nonneg_left hnu (quadInfo_mem_Icc mu).1
  have h3 := le_abs_self (thirdMoment mu * thirdMoment nu)
  change thirdMoment mu * quadInfo nu ≤ absThird mu * quadInfo nu at h1
  change quadInfo mu * thirdMoment nu ≤ quadInfo mu * absThird nu at h2
  nlinarith

-- @node: quadInfo_starLaw_integral
/-- If [the channel parameter is strictly between zero and one](hyp:hlam) and
[the second posterior law is obtained by applying that channel](hyp:hchannel),
[the quadratic information of the combined law equals the independent-product
expectation of the squared length of the product coordinate numerator divided by
one plus the coordinate inner product](goal). -/
lemma quadInfo_starLaw_integral (lam : ℝ) (hlam : LocalMomentsLambda lam)
    (mu nu : PosteriorLaw) (hchannel : LocalMomentsChannel lam nu) :
    quadInfo (starLaw mu nu) =
      ∫ pq, (∑ i : Fin 3, productNumerator pq.1 pq.2 i ^ 2) /
        (1 + coordinateDot pq.1 pq.2)
        ∂((mu : Measure (Fin 4 → ℝ)).prod (nu : Measure (Fin 4 → ℝ))) := by
  have hzmeas : Measurable productZ := by unfold productZ; fun_prop
  have hpmeas : Measurable productP := by
    unfold productP
    refine Measurable.ite (measurableSet_lt measurable_const hzmeas) ?_ measurable_const
    apply measurable_pi_lambda
    intro i
    fun_prop
  have hqmeas : Measurable quadStat := by
    unfold quadStat postCoords Matrix.mulVec dotProduct
    fun_prop
  unfold quadInfo starLaw
  rw [integral_map hpmeas.aemeasurable hqmeas.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hzmeas.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hp := (Measure.quasiMeasurePreserving_fst
    (ν := (nu : Measure (Fin 4 → ℝ)))).ae (ae_iff.mpr mu.property.2.1)
  have hq := (Measure.quasiMeasurePreserving_snd
    (μ := (mu : Measure (Fin 4 → ℝ)))).ae (ae_iff.mpr nu.property.2.1)
  apply integral_congr_ae
  filter_upwards [hp, hq, smoothed_product_bounds lam hlam mu nu hchannel]
    with pq hp hq hb
  rw [ENNReal.toReal_ofReal hb.2.2.2.le]
  simp only [smul_eq_mul, quadStat]
  simp_rw [productP_coordinates pq.1 pq.2 hp hq hb.2.2.2]
  rw [← hb.2.1]
  simp_rw [div_pow]
  rw [← Finset.sum_div]
  field_simp

-- @node: quadratic_product_integrable
/-- If [the channel parameter is strictly between zero and one](hyp:hlam) and
[the second posterior law is obtained by applying that channel](hyp:hchannel),
[both the squared length of the product coordinate numerator times one minus the
coordinate inner product and that squared length divided by one plus the coordinate
inner product are integrable under the independent product of the laws](goal). -/
lemma quadratic_product_integrable (lam : ℝ) (hlam : LocalMomentsLambda lam)
    (mu nu : PosteriorLaw) (hchannel : LocalMomentsChannel lam nu) :
    Integrable (fun pq => (∑ i : Fin 3, productNumerator pq.1 pq.2 i ^ 2) *
        (1 - coordinateDot pq.1 pq.2))
      ((mu : Measure (Fin 4 → ℝ)).prod (nu : Measure (Fin 4 → ℝ))) ∧
    Integrable (fun pq => (∑ i : Fin 3, productNumerator pq.1 pq.2 i ^ 2) /
        (1 + coordinateDot pq.1 pq.2))
      ((mu : Measure (Fin 4 → ℝ)).prod (nu : Measure (Fin 4 → ℝ))) := by
  let : IsProbabilityMeasure (mu : Measure (Fin 4 → ℝ)) := mu.property.1
  let : IsProbabilityMeasure (nu : Measure (Fin 4 → ℝ)) := nu.property.1
  have hp := (Measure.quasiMeasurePreserving_fst
    (ν := (nu : Measure (Fin 4 → ℝ)))).ae (ae_iff.mpr mu.property.2.1)
  have hq := (Measure.quasiMeasurePreserving_snd
    (μ := (mu : Measure (Fin 4 → ℝ)))).ae (ae_iff.mpr nu.property.2.1)
  have hsum : ∀ᵐ pq ∂((mu : Measure (Fin 4 → ℝ)).prod (nu : Measure (Fin 4 → ℝ))),
      (∑ i : Fin 3, productNumerator pq.1 pq.2 i ^ 2) ∈ Set.Icc 0 48 := by
    filter_upwards [hp, hq] with pq hp hq
    refine ⟨Finset.sum_nonneg fun i _ => sq_nonneg _, ?_⟩
    calc
      _ ≤ ∑ _i : Fin 3, (16 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have hi := productNumerator_abs_le_four pq.1 pq.2 hp hq i
        have hi' := abs_le.mp hi
        nlinarith [mul_nonneg (sub_nonneg.mpr hi'.2) (sub_nonneg.mpr hi'.1)]
      _ = 48 := by norm_num
  constructor
  · have hm : AEStronglyMeasurable (fun pq =>
        (∑ i : Fin 3, productNumerator pq.1 pq.2 i ^ 2) *
          (1 - coordinateDot pq.1 pq.2))
        ((mu : Measure (Fin 4 → ℝ)).prod (nu : Measure (Fin 4 → ℝ))) := by
      apply Continuous.aestronglyMeasurable
      unfold productNumerator mixedCoords coordinateDot postCoords Matrix.mulVec dotProduct
      fun_prop
    apply (integrable_const (96 : ℝ)).mono' hm
    filter_upwards [hsum, smoothed_product_bounds lam hlam mu nu hchannel] with pq ha hb
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ha.1]
    have hs : |1 - coordinateDot pq.1 pq.2| ≤ 2 := by
      apply abs_le.mpr
      constructor <;> linarith [hb.1.1, hb.1.2, hlam.2]
    calc
      _ ≤ (48 : ℝ) * 2 := mul_le_mul ha.2 hs (abs_nonneg _) (by norm_num)
      _ = 96 := by norm_num
  · have hm : AEStronglyMeasurable (fun pq =>
        (∑ i : Fin 3, productNumerator pq.1 pq.2 i ^ 2) /
          (1 + coordinateDot pq.1 pq.2))
        ((mu : Measure (Fin 4 → ℝ)).prod (nu : Measure (Fin 4 → ℝ))) := by
      apply Measurable.aestronglyMeasurable
      unfold productNumerator mixedCoords coordinateDot postCoords Matrix.mulVec dotProduct
      fun_prop
    apply (integrable_const (48 / (1 - lam) : ℝ)).mono' hm
    filter_upwards [hsum, smoothed_product_bounds lam hlam mu nu hchannel] with pq ha hb
    have hz : 0 < 1 + coordinateDot pq.1 pq.2 := by linarith [hb.2.2.2, hb.2.1]
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg ha.1 hz.le)]
    exact div_le_div₀ (by positivity : (0 : ℝ) ≤ 48) ha.2
      (sub_pos.mpr hlam.2) (by linarith [hb.1.1])

-- @node: local_quadInfo_lower_seven
/-- If [the channel parameter is strictly between zero and one](hyp:hlam),
[both posterior laws are symmetric](hyp:hsym), and
[the second is obtained by applying that channel](hyp:hchannel),
[their combined quadratic information is at least the sum of their quadratic
informations minus seven times the sum of each law's absolute third moment times
the other law's quadratic information](goal). -/
lemma local_quadInfo_lower_seven (lam : ℝ) (hlam : LocalMomentsLambda lam)
    (mu nu : PosteriorLaw) (hsym : LocalMomentsSymmetry mu nu)
    (hchannel : LocalMomentsChannel lam nu) :
    quadInfo mu + quadInfo nu -
        7 * (absThird mu * quadInfo nu + quadInfo mu * absThird nu) ≤
      quadInfo (starLaw mu nu) := by
  rw [quadInfo_starLaw_integral lam hlam mu nu hchannel]
  refine (quadratic_cancellation_lower_bound mu nu hsym).trans ?_
  obtain ⟨hpoly, hquot⟩ := quadratic_product_integrable lam hlam mu nu hchannel
  apply integral_mono_ae hpoly hquot
  filter_upwards [smoothed_product_bounds lam hlam mu nu hchannel] with pq hb
  have hz : 0 < 1 + coordinateDot pq.1 pq.2 := by linarith [hb.2.2.2, hb.2.1]
  have hs : 1 - coordinateDot pq.1 pq.2 ≤ 1 / (1 + coordinateDot pq.1 pq.2) := by
    apply (le_div_iff₀ hz).mpr
    nlinarith [sq_nonneg (coordinateDot pq.1 pq.2)]
  simpa only [div_eq_mul_inv, one_mul] using
    mul_le_mul_of_nonneg_left hs (Finset.sum_nonneg fun i _ =>
      sq_nonneg (productNumerator pq.1 pq.2 i))

-- @node: inverse_square_remainder_bound
/-- If [the channel parameter is strictly between zero and one](hyp:hlam) and
[s lies between minus that parameter and three](hyp:hs), [the absolute error from
approximating the reciprocal square of one plus s by one minus twice s is at most
nine times s squared divided by the square of one minus the channel parameter](goal). -/
lemma inverse_square_remainder_bound (lam s : ℝ) (hlam : LocalMomentsLambda lam)
    (hs : s ∈ Set.Icc (-lam) 3) :
    |(1 + s) ^ (-2 : ℤ) - (1 - 2 * s)| ≤ (9 / (1 - lam) ^ 2) * s ^ 2 := by
  have hd : 0 < 1 - lam := sub_pos.mpr hlam.2
  have hz : 0 < 1 + s := by linarith [hs.1]
  have hn : 0 ≤ 3 + 2 * s := by linarith
  have heq : (1 + s) ^ (-2 : ℤ) - (1 - 2 * s) =
      s ^ 2 * (3 + 2 * s) / (1 + s) ^ 2 := by
    rw [zpow_neg, zpow_ofNat]
    field_simp
    ring
  rw [heq, abs_of_nonneg (by positivity : 0 ≤ s ^ 2 * (3 + 2 * s) / (1 + s) ^ 2)]
  calc
    _ ≤ s ^ 2 * 9 / (1 + s) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_left (by linarith [hs.2]) (sq_nonneg _)
    _ ≤ s ^ 2 * 9 / (1 - lam) ^ 2 := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith [hs.1]
    _ = (9 / (1 - lam) ^ 2) * s ^ 2 := by ring

-- @node: denominator_replacement_error
/-- If [the channel parameter is strictly between zero and one](hyp:hlam),
[there is a nonnegative constant depending only on that parameter such that, for
any two symmetric posterior laws with the second obtained by applying the channel,
the absolute independent-product expectation of the product of the three coordinate
numerators times the error in replacing the reciprocal square of one plus their
coordinate inner product by one minus twice that inner product is bounded by the
constant times their two quadratic informations](goal). -/
lemma denominator_replacement_error (lam : ℝ) (hlam : LocalMomentsLambda lam) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ -- @realizes C_0(nonnegative error constant depending only on lambda)
      ∀ mu nu : PosteriorLaw, LocalMomentsSymmetry mu nu → LocalMomentsChannel lam nu →
        |∫ pq, (productNumerator pq.1 pq.2 0 * productNumerator pq.1 pq.2 1 *
            productNumerator pq.1 pq.2 2) *
            ((1 + coordinateDot pq.1 pq.2) ^ (-2 : ℤ) -
              (1 - 2 * coordinateDot pq.1 pq.2))
          ∂((mu : Measure (Fin 4 → ℝ)).prod (nu : Measure (Fin 4 → ℝ)))| ≤
        C0 * quadInfo mu * quadInfo nu := by
  let K : ℝ := 9 / (1 - lam) ^ 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨64 * K, by positivity, ?_⟩
  intro mu nu _hsym hchannel
  let : IsProbabilityMeasure (mu : Measure (Fin 4 → ℝ)) := mu.property.1
  let : IsProbabilityMeasure (nu : Measure (Fin 4 → ℝ)) := nu.property.1
  have hint (rho : PosteriorLaw) : Integrable quadStat (rho : Measure (Fin 4 → ℝ)) := by
    let : IsProbabilityMeasure (rho : Measure (Fin 4 → ℝ)) := rho.property.1
    have hm : AEStronglyMeasurable quadStat (rho : Measure (Fin 4 → ℝ)) := by
      apply Continuous.aestronglyMeasurable
      unfold quadStat postCoords Matrix.mulVec dotProduct
      fun_prop
    apply (integrable_const (3 : ℝ)).mono' hm
    have hs : ∀ᵐ p ∂(rho : Measure (Fin 4 → ℝ)), p ∈ stdSimplex ℝ (Fin 4) :=
      ae_iff.mpr rho.property.2.1
    filter_upwards [hs] with p hp
    simpa [Real.norm_eq_abs, abs_of_nonneg (quadStat_mem_Icc p hp).1] using
      (quadStat_mem_Icc p hp).2
  have hi := ((hint mu).mul_prod (hint nu)).const_mul (64 * K)
  have hp := (Measure.quasiMeasurePreserving_fst
    (ν := (nu : Measure (Fin 4 → ℝ)))).ae (ae_iff.mpr mu.property.2.1)
  have hq := (Measure.quasiMeasurePreserving_snd
    (μ := (mu : Measure (Fin 4 → ℝ)))).ae (ae_iff.mpr nu.property.2.1)
  have hbounds := smoothed_product_bounds lam hlam mu nu hchannel
  have hpoint : ∀ᵐ pq ∂((mu : Measure (Fin 4 → ℝ)).prod (nu : Measure (Fin 4 → ℝ))),
      ‖(productNumerator pq.1 pq.2 0 * productNumerator pq.1 pq.2 1 *
          productNumerator pq.1 pq.2 2) *
          ((1 + coordinateDot pq.1 pq.2) ^ (-2 : ℤ) -
            (1 - 2 * coordinateDot pq.1 pq.2))‖ ≤
        (64 * K) * (quadStat pq.1 * quadStat pq.2) := by
    filter_upwards [hp, hq, hbounds] with pq hp hq hb
    have hn (i : Fin 3) := productNumerator_abs_le_four pq.1 pq.2 hp hq i
    have hnum : |productNumerator pq.1 pq.2 0 * productNumerator pq.1 pq.2 1 *
        productNumerator pq.1 pq.2 2| ≤ 64 := by
      rw [abs_mul, abs_mul]
      calc
        _ ≤ (4 * 4) * 4 := mul_le_mul
          (mul_le_mul (hn 0) (hn 1) (abs_nonneg _) (by norm_num))
          (hn 2) (abs_nonneg _) (by norm_num)
        _ = 64 := by norm_num
    have hr := inverse_square_remainder_bound lam (coordinateDot pq.1 pq.2) hlam hb.1
    have hcs : coordinateDot pq.1 pq.2 ^ 2 ≤ quadStat pq.1 * quadStat pq.2 :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (postCoords pq.1) (postCoords pq.2)
    rw [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ 64 * (K * coordinateDot pq.1 pq.2 ^ 2) :=
        mul_le_mul hnum hr (abs_nonneg _) (by norm_num)
      _ ≤ 64 * (K * (quadStat pq.1 * quadStat pq.2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcs hK) (by norm_num)
      _ = (64 * K) * (quadStat pq.1 * quadStat pq.2) := by ring
  calc
    _ ≤ ∫ pq, (64 * K) * (quadStat pq.1 * quadStat pq.2)
        ∂((mu : Measure (Fin 4 → ℝ)).prod (nu : Measure (Fin 4 → ℝ))) := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_of_norm_le hi hpoint
    _ = (64 * K) * quadInfo mu * quadInfo nu := by
      rw [integral_const_mul, integral_prod_mul]
      simp only [quadInfo]
      ring

-- @node: productNumerator_triple_abs_le
/-- For [a four-state probability vector p](hyp:hp) and
[a four-state probability vector q](hyp:hq), [the absolute product of the three
product coordinate numerators is at most sixty-four](goal). -/
lemma productNumerator_triple_abs_le (p q : Fin 4 → ℝ)
    (hp : p ∈ stdSimplex ℝ (Fin 4)) (hq : q ∈ stdSimplex ℝ (Fin 4)) :
    |productNumerator p q 0 * productNumerator p q 1 * productNumerator p q 2| ≤ 64 := by
  have hn (i : Fin 3) := productNumerator_abs_le_four p q hp hq i
  rw [abs_mul, abs_mul]
  calc
    _ ≤ (4 * 4) * 4 := mul_le_mul
      (mul_le_mul (hn 0) (hn 1) (abs_nonneg _) (by norm_num))
      (hn 2) (abs_nonneg _) (by norm_num)
    _ = 64 := by norm_num

-- @node: thirdMoment_starLaw_integral
/-- If [the channel parameter is strictly between zero and one](hyp:hlam) and
[the second posterior law is obtained by applying that channel](hyp:hchannel),
[the signed third moment of the combined law equals the independent-product
expectation of the product of the three coordinate numerators divided by the
square of one plus the coordinate inner product](goal). -/
lemma thirdMoment_starLaw_integral (lam : ℝ) (hlam : LocalMomentsLambda lam)
    (mu nu : PosteriorLaw) (hchannel : LocalMomentsChannel lam nu) :
    thirdMoment (starLaw mu nu) =
      ∫ pq, (productNumerator pq.1 pq.2 0 * productNumerator pq.1 pq.2 1 *
        productNumerator pq.1 pq.2 2) * (1 + coordinateDot pq.1 pq.2) ^ (-2 : ℤ)
        ∂((mu : Measure (Fin 4 → ℝ)).prod (nu : Measure (Fin 4 → ℝ))) := by
  have hzmeas : Measurable productZ := by unfold productZ; fun_prop
  have hpmeas : Measurable productP := by
    unfold productP
    refine Measurable.ite (measurableSet_lt measurable_const hzmeas) ?_ measurable_const
    apply measurable_pi_lambda
    intro i
    fun_prop
  have htmeas : Measurable (fun p => postCoords p 0 * postCoords p 1 * postCoords p 2) := by
    unfold postCoords Matrix.mulVec dotProduct
    fun_prop
  unfold thirdMoment starLaw
  rw [integral_map hpmeas.aemeasurable htmeas.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hzmeas.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hp := (Measure.quasiMeasurePreserving_fst
    (ν := (nu : Measure (Fin 4 → ℝ)))).ae (ae_iff.mpr mu.property.2.1)
  have hq := (Measure.quasiMeasurePreserving_snd
    (μ := (mu : Measure (Fin 4 → ℝ)))).ae (ae_iff.mpr nu.property.2.1)
  apply integral_congr_ae
  filter_upwards [hp, hq, smoothed_product_bounds lam hlam mu nu hchannel]
    with pq hp hq hb
  rw [ENNReal.toReal_ofReal hb.2.2.2.le]
  simp only [smul_eq_mul]
  simp_rw [productP_coordinates pq.1 pq.2 hp hq hb.2.2.2]
  rw [← hb.2.1, zpow_neg, zpow_ofNat]
  field_simp

-- @node: third_product_integrable
/-- If [the channel parameter is strictly between zero and one](hyp:hlam) and
[the second posterior law is obtained by applying that channel](hyp:hchannel),
[the product of the three coordinate numerators divided by the square of one plus
the coordinate inner product is integrable under the independent product of the laws](goal). -/
lemma third_product_integrable (lam : ℝ) (hlam : LocalMomentsLambda lam)
    (mu nu : PosteriorLaw) (hchannel : LocalMomentsChannel lam nu) :
    Integrable (fun pq => (productNumerator pq.1 pq.2 0 * productNumerator pq.1 pq.2 1 *
        productNumerator pq.1 pq.2 2) * (1 + coordinateDot pq.1 pq.2) ^ (-2 : ℤ))
      ((mu : Measure (Fin 4 → ℝ)).prod (nu : Measure (Fin 4 → ℝ))) := by
  let : IsProbabilityMeasure (mu : Measure (Fin 4 → ℝ)) := mu.property.1
  let : IsProbabilityMeasure (nu : Measure (Fin 4 → ℝ)) := nu.property.1
  have hm : AEStronglyMeasurable (fun pq =>
      (productNumerator pq.1 pq.2 0 * productNumerator pq.1 pq.2 1 *
        productNumerator pq.1 pq.2 2) * (1 + coordinateDot pq.1 pq.2) ^ (-2 : ℤ))
      ((mu : Measure (Fin 4 → ℝ)).prod (nu : Measure (Fin 4 → ℝ))) := by
    apply Measurable.aestronglyMeasurable
    unfold productNumerator mixedCoords coordinateDot postCoords Matrix.mulVec dotProduct
    fun_prop
  apply (integrable_const (64 / (1 - lam) ^ 2 : ℝ)).mono' hm
  have hp := (Measure.quasiMeasurePreserving_fst
    (ν := (nu : Measure (Fin 4 → ℝ)))).ae (ae_iff.mpr mu.property.2.1)
  have hq := (Measure.quasiMeasurePreserving_snd
    (μ := (mu : Measure (Fin 4 → ℝ)))).ae (ae_iff.mpr nu.property.2.1)
  filter_upwards [hp, hq, smoothed_product_bounds lam hlam mu nu hchannel]
    with pq hp hq hb
  have hd : 0 < 1 - lam := sub_pos.mpr hlam.2
  have hz : 0 < 1 + coordinateDot pq.1 pq.2 := by linarith [hb.1.1]
  simp only [Real.norm_eq_abs, abs_mul, zpow_neg, zpow_ofNat, abs_inv, abs_pow,
    abs_of_pos hz]
  simpa only [div_eq_mul_inv, abs_mul] using
    div_le_div₀ (by norm_num : (0 : ℝ) ≤ 64)
      (productNumerator_triple_abs_le pq.1 pq.2 hp hq)
      (sq_pos_of_pos hd) (by nlinarith [hb.1.1] : (1 - lam) ^ 2 ≤
        (1 + coordinateDot pq.1 pq.2) ^ 2)

-- @node: local_absThird_upper
/-- If [the channel parameter is strictly between zero and one](hyp:hlam),
[there is a nonnegative constant depending only on that parameter such that the
absolute third moment of the combination of any two symmetric posterior laws,
with the second obtained by applying the channel, is at most the sum of their
absolute third moments plus the constant times their two quadratic informations](goal). -/
lemma local_absThird_upper (lam : ℝ) (hlam : LocalMomentsLambda lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ mu nu : PosteriorLaw,
      LocalMomentsSymmetry mu nu → LocalMomentsChannel lam nu →
      absThird (starLaw mu nu) ≤ absThird mu + absThird nu + C * quadInfo mu * quadInfo nu := by
  obtain ⟨C0, hC0, herr⟩ := denominator_replacement_error lam hlam
  refine ⟨C0 + 30, by linarith, ?_⟩
  intro mu nu hsym hchannel
  have hi := third_product_integrable lam hlam mu nu hchannel
  have hg : Integrable (fun pq => thirdIntegrand (postCoords pq.1) (postCoords pq.2))
      ((mu : Measure (Fin 4 → ℝ)).prod (nu : Measure (Fin 4 → ℝ))) := by
    apply posterior_prod_continuous_integrable
    unfold thirdIntegrand mixedCoords postCoords Matrix.mulVec dotProduct
    fun_prop
  have hid : thirdMoment (starLaw mu nu) -
      (∫ pq, thirdIntegrand (postCoords pq.1) (postCoords pq.2)
        ∂((mu : Measure (Fin 4 → ℝ)).prod (nu : Measure (Fin 4 → ℝ)))) =
      ∫ pq, (productNumerator pq.1 pq.2 0 * productNumerator pq.1 pq.2 1 *
        productNumerator pq.1 pq.2 2) *
        ((1 + coordinateDot pq.1 pq.2) ^ (-2 : ℤ) - (1 - 2 * coordinateDot pq.1 pq.2))
        ∂((mu : Measure (Fin 4 → ℝ)).prod (nu : Measure (Fin 4 → ℝ))) := by
    rw [thirdMoment_starLaw_integral lam hlam mu nu hchannel, ← integral_sub hi hg]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun pq => by
      change _ - _ * _ * _ * _ = _
      dsimp [thirdIntegrand, productNumerator, coordinateDot]
      ring
  have hp := third_polynomial_integral_bound mu nu hsym
  have he := herr mu nu hsym hchannel
  rw [← hid] at he
  have ht : |thirdMoment (starLaw mu nu) - thirdMoment mu - thirdMoment nu| ≤
      (C0 + 30) * quadInfo mu * quadInfo nu := by
    calc
      _ = |(thirdMoment (starLaw mu nu) -
          ∫ pq, thirdIntegrand (postCoords pq.1) (postCoords pq.2)
            ∂((mu : Measure (Fin 4 → ℝ)).prod (nu : Measure (Fin 4 → ℝ)))) +
          ((∫ pq, thirdIntegrand (postCoords pq.1) (postCoords pq.2)
            ∂((mu : Measure (Fin 4 → ℝ)).prod (nu : Measure (Fin 4 → ℝ)))) -
          thirdMoment mu - thirdMoment nu)| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans ((add_le_add he hp).trans (by ring_nf; rfl))
  have ht' := abs_add_le (thirdMoment mu + thirdMoment nu)
    (thirdMoment (starLaw mu nu) - thirdMoment mu - thirdMoment nu)
  have hs := abs_add_le (thirdMoment mu) (thirdMoment nu)
  have heq : thirdMoment mu + thirdMoment nu +
      (thirdMoment (starLaw mu nu) - thirdMoment mu - thirdMoment nu) =
      thirdMoment (starLaw mu nu) := by ring
  rw [heq] at ht'
  unfold absThird
  linarith

-- @node: lem:local-moments
/-- Assuming [the squared Euclidean norm equals the sum of squared coordinates](hyp:hpin1),
[the combined posterior law obeys the density-weighted product rule for every valid
measurable extension of the normalized product](hyp:hpin2), and
[the channel parameter is strictly between zero and one](hyp:hlam),
[there is a positive constant depending only on that parameter such that, for two
symmetric posterior laws with the second obtained by applying the channel, their
combined quadratic information is at least their total quadratic information minus
the constant times the sum of each absolute third moment times the other quadratic
information, their combined absolute third moment is at most their total absolute
third moment plus the constant times their two quadratic informations, and the
quadratic lower bound also holds with constant seven](goal). -/
lemma local_moment_bounds (hpin1 : EuclideanNormPin) (hpin2 : ProductRulePin)
    (lam : ℝ) (hlam : LocalMomentsLambda lam) :
    ∃ C : ℝ, 0 < C ∧ -- @realizes C(finite positive common constant depending only on lambda)
      ∀ mu nu : PosteriorLaw,
        LocalMomentsSymmetry mu nu → LocalMomentsChannel lam nu →
        quadInfo (starLaw mu nu) ≥ quadInfo mu + quadInfo nu -
          C * (absThird mu * quadInfo nu + quadInfo mu * absThird nu) ∧
        absThird (starLaw mu nu) ≤ absThird mu + absThird nu + C * quadInfo mu * quadInfo nu ∧
        quadInfo (starLaw mu nu) ≥ quadInfo mu + quadInfo nu -
          7 * (absThird mu * quadInfo nu + quadInfo mu * absThird nu) := by
  obtain ⟨C3, hC3, hthird⟩ := local_absThird_upper lam hlam
  refine ⟨C3 + 7, by linarith, ?_⟩
  intro mu nu hsym hchannel
  have hseven := local_quadInfo_lower_seven lam hlam mu nu hsym hchannel
  have hcross : 0 ≤ absThird mu * quadInfo nu + quadInfo mu * absThird nu :=
    add_nonneg (mul_nonneg (abs_nonneg _) (quadInfo_mem_Icc nu).1)
      (mul_nonneg (quadInfo_mem_Icc mu).1 (abs_nonneg _))
  refine ⟨?_, ?_, hseven⟩
  · exact (sub_le_sub_left (mul_le_mul_of_nonneg_right (by linarith : 7 ≤ C3 + 7)
      hcross) _).trans hseven
  · have hmono := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : C3 ≤ C3 + 7)
        (quadInfo_mem_Icc mu).1) (quadInfo_mem_Icc nu).1
    linarith [hthird mu nu hsym hchannel]

end OaiCapacityCriterionState
