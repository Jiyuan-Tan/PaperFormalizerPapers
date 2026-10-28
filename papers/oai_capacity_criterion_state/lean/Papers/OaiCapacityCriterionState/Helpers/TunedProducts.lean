module

public import Papers.OaiCapacityCriterionState.Helpers.ProductMoments

/-! # Tuning small finite products with controlled third moments

The finite-product estimates give both an information lower bound and a bound
on the third moment relative to that information. Attenuation preserves the
latter bound while tuning the information to any smaller nonnegative target.
All smallness conditions are explicit inequalities on the sum of the moments.
-/

public section

open MeasureTheory

namespace OaiCapacityCriterionState

-- @node: FiniteSpinExperiment.tune_absThird_ratio_le
/-- If [the tolerance is nonnegative](hyp:heps), [a finite spin experiment's
absolute third moment is at most the tolerance times its quadratic information](hyp:hthird),
and the target information is [nonnegative](hyp:ha) and [no larger than the
experiment's quadratic information](hyp:ham), then [tuning the experiment to
that target gives an absolute third moment at most the tolerance times the target](goal). -/
lemma FiniteSpinExperiment.tune_absThird_ratio_le (E : FiniteSpinExperiment)
    (eps : ℝ) (heps : 0 ≤ eps) (hthird : absThird E.law ≤ eps * quadInfo E.law)
    (a : ℝ) (ha : 0 ≤ a) (ham : a ≤ quadInfo E.law) :
    absThird (E.tune a ha ham).law ≤ eps * a := by
  have ht := (attenuationParameter_spec a (quadInfo E.law) ha ham).1
  have hscaled := mul_le_mul_of_nonneg_left hthird (pow_nonneg ht.1 3)
  rw [(E.tune_moments a ha ham).2.2]
  calc
    _ ≤ attenuationParameter a (quadInfo E.law) ^ 3 *
        (eps * quadInfo E.law) := hscaled
    _ = eps * attenuationParameter a (quadInfo E.law) *
        (attenuationParameter a (quadInfo E.law) ^ 2 * quadInfo E.law) := by ring
    _ = eps * attenuationParameter a (quadInfo E.law) * a := by
      rw [(attenuationParameter_spec a (quadInfo E.law) ha ham).2]
    _ ≤ eps * a := by
      nlinarith [mul_le_mul_of_nonneg_left ht.2 (mul_nonneg heps ha)]

-- @node: product_moment_bounds_of_smallness
/-- Suppose [the total information S is nonnegative](hyp:hS) and [the tolerance
ε is nonnegative](hyp:heps). If [the information m is at least
S − 7SD − (7K/2)S³](hyp:hlower), [the third moment d is at most
D + (K/2)S²](hyp:hupper), [D is at most ηS](hyp:hD),
[7ηS + (7K/2)S² is at most 1 − q](hyp:hsmall), and
[η + (K/2)S is at most εq](hyp:hthird), then [m is at least qS and d is
at most εm](goal). -/
lemma product_moment_bounds_of_smallness {m d S D K eta eps q : ℝ}
    (hS : 0 ≤ S) (heps : 0 ≤ eps)
    (hlower : S - 7 * S * D - (7 * K / 2) * S ^ 3 ≤ m)
    (hupper : d ≤ D + K / 2 * S ^ 2)
    (hD : D ≤ eta * S)
    (hsmall : 7 * eta * S + (7 * K / 2) * S ^ 2 ≤ 1 - q)
    (hthird : eta + K / 2 * S ≤ eps * q) :
    q * S ≤ m ∧ d ≤ eps * m := by
  have herror := mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ 7 * S)
  have hsmall' := mul_le_mul_of_nonneg_right hsmall hS
  have hthird' := mul_le_mul_of_nonneg_right hthird hS
  have hm : q * S ≤ m := by nlinarith [hlower, herror, hsmall']
  refine ⟨hm, ?_⟩
  exact (show d ≤ eps * (q * S) by nlinarith [hupper, hD, hthird']).trans
    (mul_le_mul_of_nonneg_left hm heps)

-- @node: channel_list_third_ratio_bound
/-- If [the channel parameter λ is strictly between zero and one](hyp:hlam),
[every measure in a finite list is a posterior law](hyp:hpost), and
[each law's absolute third moment is at most ε times its quadratic information](hyp:hthird),
then [after applying the channel to every law, the sum of absolute third moments
is at most λε times the sum of quadratic informations](goal). -/
lemma channel_list_third_ratio_bound (lam : ℝ) (hlam : MainLambda lam)
    (eps : ℝ) (mus : List (Measure (Fin 4 → ℝ)))
    (hpost : ∀ mu ∈ mus, IsPosteriorLaw mu)
    (hthird : ∀ mu ∈ mus, absThird mu ≤ eps * quadInfo mu) :
    ((mus.map (channelStep lam)).map absThird).sum ≤
      (lam * eps) * ((mus.map (channelStep lam)).map quadInfo).sum := by
  rw [← List.sum_map_mul_left]
  apply List.sum_le_sum
  intro mu hmu
  obtain ⟨nu, hnu, rfl⟩ := List.mem_map.mp hmu
  have hm := moments_channelStep lam ⟨hlam.1.le, hlam.2.le⟩ nu (hpost nu hnu)
  have hquad := congrArg Prod.fst hm
  have hthird' := congrArg (fun x => x.2.2) hm
  change quadInfo (channelStep lam nu) = sqParam lam * quadInfo nu at hquad
  change absThird (channelStep lam nu) = lam ^ 3 * absThird nu at hthird'
  rw [hquad, hthird']
  calc
    _ ≤ lam ^ 3 * (eps * quadInfo nu) :=
      mul_le_mul_of_nonneg_left (hthird nu hnu) (pow_nonneg hlam.1.le 3)
    _ = _ := by unfold sqParam; ring

-- @node: companion_class_tunable_products
/-- Assuming [the companion proposition giving a symmetric posterior class
closed under channels and conditional products with a quantitative moment saving](hyp:hCompanion)
and [a channel parameter λ strictly between zero and one](hyp:hlam),
[there exist a nonnegative constant K and a class of symmetric posterior laws
containing the revealing and uninformative laws and closed under channels with
parameters in the unit interval and conditional products, with the following
tuning property: for any finite list of class members realized by finite spin
experiments and each expressible as a λ-channel output of a posterior law,
write S and D for their total quadratic information and absolute third moment;
for any real η, nonnegative tolerance ε, real q, and nonnegative target a,
if D ≤ ηS, 7ηS + (7K/2)S² ≤ 1 − q, η + (K/2)S ≤ εq, and a ≤ qS,
there is a finite spin experiment in the class that is a degradation of the
conditional product, has quadratic information exactly a, and has absolute
third moment at most εa](goal). -/
lemma companion_class_tunable_products (hCompanion : CompanionMomentSaving)
    (lam : ℝ) (hlam : LocalMomentsLambda lam) :
    ∃ (C : Set (Measure (Fin 4 → ℝ))) (K : ℝ),
      0 ≤ K ∧
      (∀ mu ∈ C, IsPosteriorLaw mu ∧ IsSymmetricLaw mu) ∧
      revealingLaw ∈ C ∧ uninformativeLaw ∈ C ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ mu ∈ C, channelStep t mu ∈ C) ∧
      (∀ mu ∈ C, ∀ nu ∈ C, starLaw mu nu ∈ C) ∧
      ∀ (mus : List (Measure (Fin 4 → ℝ)))
        (_hmus : ∀ mu ∈ mus, mu ∈ C),
        (∀ mu ∈ mus, ∃ E : FiniteSpinExperiment, E.law = mu) →
        (∀ mu ∈ mus, ∃ nu : PosteriorLaw, mu = channelStep lam nu) →
        ∀ (eta eps q a : ℝ), 0 ≤ eps → 0 ≤ a →
        let S := (mus.map quadInfo).sum
        let D := (mus.map absThird).sum
        D ≤ eta * S →
        7 * eta * S + (7 * K / 2) * S ^ 2 ≤ 1 - q →
        eta + K / 2 * S ≤ eps * q →
        a ≤ q * S →
        ∃ F : FiniteSpinExperiment,
          F.law ∈ C ∧
          FiniteLawDegrades (mus.foldr starLaw uninformativeLaw) F.law ∧
          quadInfo F.law = a ∧ absThird F.law ≤ eps * a := by
  obtain ⟨C, K, hK, hC, hr, hz, hchannel, hstar, hbounds⟩ :=
    companion_class_finite_product_moments hCompanion lam hlam
  refine ⟨C, K, hK, hC, hr, hz, hchannel, hstar, ?_⟩
  intro mus hmus hfinite hsmooth eta eps q a heps ha S D hD hsmall hthird hatarget
  obtain ⟨E, hE⟩ := rightProductLaw_finite mus hfinite
  obtain ⟨_, hd, hm⟩ := hbounds mus hmus hsmooth
  have hS : 0 ≤ S := List.sum_nonneg (fun x hx => by
    obtain ⟨mu, hmu, rfl⟩ := List.mem_map.mp hx
    exact (quadInfo_mem_Icc ⟨mu, (hC mu (hmus mu hmu)).1⟩).1)
  have hcontrol := product_moment_bounds_of_smallness hS heps hm hd hD hsmall hthird
  have ham : a ≤ quadInfo E.law := by
    rw [hE]
    exact hatarget.trans hcontrol.1
  have hratio : absThird E.law ≤ eps * quadInfo E.law := by
    rw [hE]
    exact hcontrol.2
  refine ⟨E.tune a ha ham, ?_, ?_, (E.tune_moments a ha ham).1,
    E.tune_absThird_ratio_le eps heps hratio a ha ham⟩
  · exact E.tune_mem C hchannel (hE ▸ rightProductLaw_mem C hz hstar mus hmus) a ha ham
  · have hdegrades := E.tune_degrades a ha ham
    rw [hE, rightProductLaw_eq_foldr mus hfinite] at hdegrades
    exact hdegrades

-- @node: exists_product_tuning_window
/-- If [λ is nonnegative](hyp:hlam), [ε is strictly positive](hyp:heps),
[q exceeds λ](hyp:hql), [q is less than one](hyp:hq), and [K is nonnegative](hyp:hK),
then [there is a positive δ such that every S between zero and δ, inclusive,
satisfies both 7λεS + (7K/2)S² ≤ 1 − q and λε + (K/2)S ≤ εq](goal). -/
lemma exists_product_tuning_window {lam eps q K : ℝ}
    (hlam : 0 ≤ lam) (heps : 0 < eps) (hql : lam < q) (hq : q < 1)
    (hK : 0 ≤ K) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ S ∈ Set.Icc 0 delta,
      7 * (lam * eps) * S + (7 * K / 2) * S ^ 2 ≤ 1 - q ∧
      lam * eps + K / 2 * S ≤ eps * q := by
  let A := 7 * (lam * eps) + 7 * K / 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hA1 : 0 < A + 1 := by positivity
  have hK1 : 0 < K / 2 + 1 := by positivity
  let delta := min 1 (min ((1 - q) / (A + 1)) (eps * (q - lam) / (K / 2 + 1)))
  have hd : 0 < delta := by
    dsimp [delta]
    exact lt_min zero_lt_one (lt_min (div_pos (sub_pos.mpr hq) hA1)
      (div_pos (mul_pos heps (sub_pos.mpr hql)) hK1))
  refine ⟨delta, hd, ?_⟩
  intro S hS
  have hS1 : S ≤ 1 := hS.2.trans (min_le_left _ _)
  have hSa : S ≤ (1 - q) / (A + 1) :=
    hS.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSk : S ≤ eps * (q - lam) / (K / 2 + 1) :=
    hS.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hSa' := (le_div_iff₀ hA1).mp hSa
  have hSk' := (le_div_iff₀ hK1).mp hSk
  have hsq : S ^ 2 ≤ S := by nlinarith [mul_nonneg hS.1 (sub_nonneg.mpr hS1)]
  constructor
  · have hquad := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 7 * K / 2)
    dsimp [A] at hSa'
    nlinarith
  · nlinarith

-- @node: companion_class_channel_tunable_products
/-- Assuming [the companion proposition giving a symmetric posterior class
closed under channels and conditional products with a quantitative moment saving](hyp:hCompanion)
and [a channel parameter λ strictly between zero and one](hyp:hlam),
[there exist a nonnegative constant K and a class of symmetric posterior laws
containing the revealing and uninformative laws and closed under channels with
parameters in the unit interval and conditional products, with the following
property: for any finite list of class members realized by finite spin experiments,
any nonnegative ε and target a, and any real q, if each input's absolute third
moment is at most ε times its quadratic information, then, writing S for the
total quadratic information after applying the λ-channel, the inequalities
7λεS + (7K/2)S² ≤ 1 − q, λε + (K/2)S ≤ εq, and a ≤ qS guarantee a finite
spin experiment in the class that is a degradation of the conditional product
of the channel outputs, has quadratic information exactly a, and has absolute
third moment at most εa](goal). -/
lemma companion_class_channel_tunable_products (hCompanion : CompanionMomentSaving)
    (lam : ℝ) (hlam : MainLambda lam) :
    ∃ (C : Set (Measure (Fin 4 → ℝ))) (K : ℝ),
      0 ≤ K ∧
      (∀ mu ∈ C, IsPosteriorLaw mu ∧ IsSymmetricLaw mu) ∧
      revealingLaw ∈ C ∧ uninformativeLaw ∈ C ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ mu ∈ C, channelStep t mu ∈ C) ∧
      (∀ mu ∈ C, ∀ nu ∈ C, starLaw mu nu ∈ C) ∧
      ∀ (mus : List (Measure (Fin 4 → ℝ)))
        (_hmus : ∀ mu ∈ mus, mu ∈ C),
        (∀ mu ∈ mus, ∃ E : FiniteSpinExperiment, E.law = mu) →
        ∀ (eps q a : ℝ), 0 ≤ eps → 0 ≤ a →
        (∀ mu ∈ mus, absThird mu ≤ eps * quadInfo mu) →
        let S := ((mus.map (channelStep lam)).map quadInfo).sum
        7 * (lam * eps) * S + (7 * K / 2) * S ^ 2 ≤ 1 - q →
        lam * eps + K / 2 * S ≤ eps * q →
        a ≤ q * S →
        ∃ F : FiniteSpinExperiment,
          F.law ∈ C ∧
          FiniteLawDegrades
            ((mus.map (channelStep lam)).foldr starLaw uninformativeLaw) F.law ∧
          quadInfo F.law = a ∧ absThird F.law ≤ eps * a := by
  obtain ⟨C, K, hK, hC, hr, hz, hchannel, hstar, htune⟩ :=
    companion_class_tunable_products hCompanion lam hlam
  refine ⟨C, K, hK, hC, hr, hz, hchannel, hstar, ?_⟩
  intro mus hmus hfinite eps q a heps ha hthird S hsmall hratio hatarget
  have ht : IsChannelParameter lam := ⟨hlam.1.le, hlam.2.le⟩
  have hmem : ∀ mu ∈ mus.map (channelStep lam), mu ∈ C := by
    intro mu hmu
    obtain ⟨nu, hnu, rfl⟩ := List.mem_map.mp hmu
    exact hchannel lam ht nu (hmus nu hnu)
  have hfin : ∀ mu ∈ mus.map (channelStep lam),
      ∃ E : FiniteSpinExperiment, E.law = mu := by
    intro mu hmu
    obtain ⟨nu, hnu, rfl⟩ := List.mem_map.mp hmu
    obtain ⟨E, rfl⟩ := hfinite nu hnu
    exact ⟨E.channel lam ht, E.law_channel lam ht⟩
  have hsmooth : ∀ mu ∈ mus.map (channelStep lam),
      ∃ nu : PosteriorLaw, mu = channelStep lam nu := by
    intro mu hmu
    obtain ⟨nu, hnu, rfl⟩ := List.mem_map.mp hmu
    exact ⟨⟨nu, (hC nu (hmus nu hnu)).1⟩, rfl⟩
  exact htune _ hmem hfin hsmooth (lam * eps) eps q a heps ha
    (channel_list_third_ratio_bound lam hlam eps mus
      (fun mu hmu => (hC mu (hmus mu hmu)).1) hthird) hsmall hratio hatarget

end OaiCapacityCriterionState
