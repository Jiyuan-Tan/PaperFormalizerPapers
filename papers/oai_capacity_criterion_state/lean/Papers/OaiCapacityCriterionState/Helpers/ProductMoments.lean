module

public import Papers.OaiCapacityCriterionState.Helpers.Attenuation

/-! # Finite products with controlled third moments

Combine each smoothed factor on the right, so the binary local estimates apply
at every stage. The total quadratic and third moments bound the accumulated
error without a dependence on the number of factors.
-/

@[expose] public section

open MeasureTheory

namespace OaiCapacityCriterionState

-- @node: rightProductLaw
/-- The [right-combined posterior law](goal) of a list of four-state posterior
measures is [the uninformative law for an empty list](step:1); for a nonempty list,
it is [the combination of the recursively combined tail with the first measure
as the right factor](step:2). -/
noncomputable def rightProductLaw : List (Measure (Fin 4 → ℝ)) → Measure (Fin 4 → ℝ)
  | [] => uninformativeLaw
  | mu :: mus => starLaw (rightProductLaw mus) mu

-- @node: rightProductLaw_mem
/-- If [a class contains the uninformative law](hyp:hzero),
[is closed under combining two member laws](hyp:hstar), and
[contains every measure in a given list](hyp:hmus), [it contains the list's
right-combined posterior law](goal). -/
lemma rightProductLaw_mem (C : Set (Measure (Fin 4 → ℝ)))
    (hzero : uninformativeLaw ∈ C)
    (hstar : ∀ mu ∈ C, ∀ nu ∈ C, starLaw mu nu ∈ C)
    (mus : List (Measure (Fin 4 → ℝ))) (hmus : ∀ mu ∈ mus, mu ∈ C) :
    rightProductLaw mus ∈ C := by
  induction mus with
  | nil => exact hzero
  | cons mu mus ih =>
      exact hstar _ (ih (fun nu hnu => hmus nu (by simp [hnu]))) _ (hmus mu (by simp))

-- @node: FiniteSpinExperiment.starLaw_comm
/-- For any two finite spin experiments, [combining their posterior laws gives
the same law in either order](goal). -/
lemma FiniteSpinExperiment.starLaw_comm (E F : FiniteSpinExperiment) :
    starLaw E.law F.law = starLaw F.law E.law := by
  rw [← E.law_product F, ← F.law_product E]
  change experimentLaw (productLikelihood E.likelihood F.likelihood) =
    experimentLaw (productLikelihood F.likelihood E.likelihood)
  have heq : productLikelihood E.likelihood F.likelihood =
      (fun i o => productLikelihood F.likelihood E.likelihood i
        ((Equiv.prodComm E.Obs F.Obs) o)) := by
    funext i o
    exact mul_comm _ _
  rw [heq]
  exact experimentLaw_reindex (Equiv.prodComm E.Obs F.Obs) _

-- @node: rightProductLaw_finite
/-- If [every measure in a list is the posterior law of a finite spin experiment](hyp:hmus),
[the right-combined law of that list is also the posterior law of a finite spin
experiment](goal). -/
lemma rightProductLaw_finite (mus : List (Measure (Fin 4 → ℝ)))
    (hmus : ∀ mu ∈ mus, ∃ E : FiniteSpinExperiment, E.law = mu) :
    ∃ E : FiniteSpinExperiment, E.law = rightProductLaw mus := by
  induction mus with
  | nil => exact ⟨uninformativeExperiment, uninformativeExperiment_law⟩
  | cons mu mus ih =>
      obtain ⟨E, hE⟩ := hmus mu (by simp)
      obtain ⟨F, hF⟩ := ih (fun nu hnu => hmus nu (by simp [hnu]))
      exact ⟨F.product E, (F.law_product E).trans (by rw [hF, hE]; rfl)⟩

-- @node: rightProductLaw_eq_foldr
/-- If [every measure in a list is the posterior law of a finite spin experiment](hyp:hmus),
[its right-combined law equals the law obtained by combining the first measure
with the recursively combined remainder, starting from the uninformative law](goal). -/
lemma rightProductLaw_eq_foldr (mus : List (Measure (Fin 4 → ℝ)))
    (hmus : ∀ mu ∈ mus, ∃ E : FiniteSpinExperiment, E.law = mu) :
    rightProductLaw mus = mus.foldr starLaw uninformativeLaw := by
  induction mus with
  | nil => rfl
  | cons mu mus ih =>
      have ht : ∀ nu ∈ mus, ∃ E : FiniteSpinExperiment, E.law = nu :=
        fun nu hnu => hmus nu (by simp [hnu])
      obtain ⟨E, rfl⟩ := hmus mu (by simp)
      obtain ⟨F, hF⟩ := rightProductLaw_finite mus ht
      change starLaw (rightProductLaw mus) E.law =
        starLaw E.law (mus.foldr starLaw uninformativeLaw)
      rw [← ih ht, ← hF, F.starLaw_comm E]

-- @node: rightProductLaw_moment_bounds
/-- Suppose [every member of a class is a symmetric posterior law](hyp:hC),
[the class contains the uninformative law](hyp:hzero), [is closed under combining
laws](hyp:hstar), and [combination is subadditive for quadratic information within
the class](hyp:hupper). If [the channel parameter is strictly between zero and one](hyp:hlam),
[K is nonnegative](hyp:hK), [combining symmetric posterior laws with a channel-smoothed
second factor increases their total absolute third moment by at most K times their
two quadratic informations](hyp:hthird), [all laws in a list belong to the class](hyp:hmus),
and [each is obtained by applying that channel to a posterior law](hyp:hsmooth),
then [writing S for their total quadratic information and D for their total absolute
third moment, the right-combined law has quadratic information at most S, absolute
third moment at most D + KS²/2, and quadratic information at least
S − 7SD − 7KS³/2](goal). -/
lemma rightProductLaw_moment_bounds
    (C : Set (Measure (Fin 4 → ℝ)))
    (hC : ∀ mu ∈ C, IsPosteriorLaw mu ∧ IsSymmetricLaw mu)
    (hzero : uninformativeLaw ∈ C)
    (hstar : ∀ mu ∈ C, ∀ nu ∈ C, starLaw mu nu ∈ C)
    (hupper : ∀ mu ∈ C, ∀ nu ∈ C,
      quadInfo (starLaw mu nu) ≤ quadInfo mu + quadInfo nu)
    (lam : ℝ) (hlam : LocalMomentsLambda lam)
    (K : ℝ) (hK : 0 ≤ K)
    (hthird : ∀ mu nu : PosteriorLaw,
      LocalMomentsSymmetry mu nu → LocalMomentsChannel lam nu →
      absThird (starLaw mu nu) ≤ absThird mu + absThird nu +
        K * quadInfo mu * quadInfo nu)
    (mus : List (Measure (Fin 4 → ℝ)))
    (hmus : ∀ mu ∈ mus, mu ∈ C)
    (hsmooth : ∀ mu (hmu : mu ∈ mus),
      LocalMomentsChannel lam ⟨mu, (hC mu (hmus mu hmu)).1⟩) :
    let S := (mus.map quadInfo).sum
    let D := (mus.map absThird).sum
    quadInfo (rightProductLaw mus) ≤ S ∧
      absThird (rightProductLaw mus) ≤ D + K / 2 * S ^ 2 ∧
      S - 7 * S * D - (7 * K / 2) * S ^ 3 ≤ quadInfo (rightProductLaw mus) := by
  induction mus with
  | nil =>
      simp only [rightProductLaw, List.map_nil, List.sum_nil]
      rw [extreme_moments.2.1, extreme_moments.2.2]
      norm_num
  | cons mu mus ih =>
      have hm := hmus mu (by simp)
      have ht : ∀ nu ∈ mus, nu ∈ C := fun nu hnu => hmus nu (by simp [hnu])
      have hc := rightProductLaw_mem C hzero hstar mus ht
      obtain ⟨ihm, iht, ihl⟩ := ih ht (fun nu hnu => hsmooth nu (by simp [hnu]))
      let S := (mus.map quadInfo).sum
      let D := (mus.map absThird).sum
      let a := quadInfo mu
      let d := absThird mu
      have ha : 0 ≤ a := (quadInfo_mem_Icc ⟨mu, (hC mu hm).1⟩).1
      have hd : 0 ≤ d := abs_nonneg _
      have hS : 0 ≤ S := List.sum_nonneg (fun x hx => by
        obtain ⟨nu, hnu, rfl⟩ := List.mem_map.mp hx
        exact (quadInfo_mem_Icc ⟨nu, (hC nu (ht nu hnu)).1⟩).1)
      have hD : 0 ≤ D := List.sum_nonneg (fun x hx => by
        obtain ⟨nu, _, rfl⟩ := List.mem_map.mp hx
        exact abs_nonneg _)
      have hsym : LocalMomentsSymmetry
          ⟨rightProductLaw mus, (hC _ hc).1⟩ ⟨mu, (hC mu hm).1⟩ :=
        ⟨(hC _ hc).2, (hC mu hm).2⟩
      have hsm := hsmooth mu (by simp)
      have hu := hupper _ hc mu hm
      have ht' := hthird _ _ hsym hsm
      have hl := local_quadInfo_lower_seven lam hlam _ _ hsym hsm
      have hmul := mul_le_mul_of_nonneg_right ihm ha
      have hcross := add_le_add
        (mul_le_mul_of_nonneg_right iht ha)
        (mul_le_mul_of_nonneg_right ihm hd)
      change quadInfo (starLaw (rightProductLaw mus) mu) ≤ a + S ∧
        absThird (starLaw (rightProductLaw mus) mu) ≤
          d + D + K / 2 * (a + S) ^ 2 ∧
        a + S - 7 * (a + S) * (d + D) - (7 * K / 2) * (a + S) ^ 3 ≤
          quadInfo (starLaw (rightProductLaw mus) mu)
      refine ⟨by linarith, ?_, ?_⟩
      · have hk := mul_le_mul_of_nonneg_left hmul hK
        dsimp only [S, D, a, d] at *
        nlinarith [mul_nonneg hK (sq_nonneg (quadInfo mu))]
      · change absThird (rightProductLaw mus) * a +
          quadInfo (rightProductLaw mus) * d ≤ (D + K / 2 * S ^ 2) * a + S * d at hcross
        change S - 7 * S * D - (7 * K / 2) * S ^ 3 ≤
          quadInfo (rightProductLaw mus) at ihl
        have hextra : 0 ≤ 7 * a * d + (7 * K / 2) *
            (2 * S ^ 2 * a + 3 * S * a ^ 2 + a ^ 3) := by positivity
        nlinarith

-- @node: companion_class_finite_product_moments
/-- Assuming [there exists a class of symmetric posterior laws containing the
revealing and uninformative laws, closed under channels and combination, with the
companion fourth-moment saving in quadratic information](hyp:hCompanion), and
[the channel parameter is strictly between zero and one](hyp:hlam),
[there exist such a class closed under channels and combination and a nonnegative
constant K so that any list of its channel-smoothed members, with total quadratic
information S and total absolute third moment D, has right-combined quadratic
information at most S and at least S − 7SD − 7KS³/2, and right-combined absolute
third moment at most D + KS²/2](goal). -/
lemma companion_class_finite_product_moments (hCompanion : CompanionMomentSaving)
    (lam : ℝ) (hlam : LocalMomentsLambda lam) :
    ∃ (C : Set (Measure (Fin 4 → ℝ))) (K : ℝ),
      0 ≤ K ∧
      (∀ mu ∈ C, IsPosteriorLaw mu ∧ IsSymmetricLaw mu) ∧
      revealingLaw ∈ C ∧ uninformativeLaw ∈ C ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ mu ∈ C, channelStep t mu ∈ C) ∧
      (∀ mu ∈ C, ∀ nu ∈ C, starLaw mu nu ∈ C) ∧
      ∀ (mus : List (Measure (Fin 4 → ℝ)))
        (_hmus : ∀ mu ∈ mus, mu ∈ C),
        (∀ mu ∈ mus, ∃ nu : PosteriorLaw, mu = channelStep lam nu) →
        let S := (mus.map quadInfo).sum
        let D := (mus.map absThird).sum
        quadInfo (rightProductLaw mus) ≤ S ∧
          absThird (rightProductLaw mus) ≤ D + K / 2 * S ^ 2 ∧
          S - 7 * S * D - (7 * K / 2) * S ^ 3 ≤ quadInfo (rightProductLaw mus) := by
  obtain ⟨C, hC, hr, hz, hchannel, hstar, hsave⟩ :=
    companion_class_cubic_saving hCompanion
  obtain ⟨K, hK, hthird⟩ := local_absThird_upper lam hlam
  refine ⟨C, K, hK, hC, hr, hz, hchannel, hstar, ?_⟩
  intro mus hmus hsmooth
  apply rightProductLaw_moment_bounds C hC hz hstar ?_ lam hlam K hK hthird mus hmus hsmooth
  intro mu hmu nu hnu
  have hmu0 := (quadInfo_mem_Icc ⟨mu, (hC mu hmu).1⟩).1
  have hnu0 := (quadInfo_mem_Icc ⟨nu, (hC nu hnu).1⟩).1
  exact (hsave mu hmu nu hnu).1.trans (sub_le_self _ (by positivity))

-- @node: FiniteSpinExperiment.tune_absThird_le
/-- If [the target quadratic information a is nonnegative](hyp:ha) and
[does not exceed the finite experiment's quadratic information](hyp:ham),
[the absolute third moment of the experiment tuned to a is at most a times the
attenuation parameter used for that tuning](goal). -/
lemma FiniteSpinExperiment.tune_absThird_le (E : FiniteSpinExperiment)
    (a : ℝ) (ha : 0 ≤ a) (ham : a ≤ quadInfo E.law) :
    absThird (E.tune a ha ham).law ≤
      attenuationParameter a (quadInfo E.law) * a := by
  have ht := (attenuationParameter_spec a (quadInfo E.law) ha ham).1.1
  have hbound := mul_le_mul_of_nonneg_left
    (absThird_le_quadInfo ⟨E.law, E.law_isPosteriorLaw⟩)
    (pow_nonneg ht 3)
  rw [(E.tune_moments a ha ham).2.2]
  calc
    _ ≤ attenuationParameter a (quadInfo E.law) ^ 3 * quadInfo E.law := hbound
    _ = attenuationParameter a (quadInfo E.law) *
        (attenuationParameter a (quadInfo E.law) ^ 2 * quadInfo E.law) := by ring
    _ = _ := by rw [(attenuationParameter_spec a (quadInfo E.law) ha ham).2]

-- @node: FiniteSpinExperiment.tune_absThird_le_of_budget
/-- If [the target quadratic information a is nonnegative](hyp:ha) and
[does not exceed the finite experiment's quadratic information](hyp:ham),
[ε is nonnegative](hyp:heps), and [a is at most ε² times the experiment's quadratic
information](hyp:hbudget), [the experiment tuned to a has absolute third moment
at most εa](goal). -/
lemma FiniteSpinExperiment.tune_absThird_le_of_budget (E : FiniteSpinExperiment)
    (a : ℝ) (ha : 0 ≤ a) (ham : a ≤ quadInfo E.law)
    (eps : ℝ) (heps : 0 ≤ eps) (hbudget : a ≤ eps ^ 2 * quadInfo E.law) :
    absThird (E.tune a ha ham).law ≤ eps * a := by
  have hm := (quadInfo_mem_Icc ⟨E.law, E.law_isPosteriorLaw⟩).1
  by_cases hm0 : quadInfo E.law = 0
  · have ha0 : a = 0 := le_antisymm (ham.trans_eq hm0) ha
    simpa only [ha0, mul_zero] using E.tune_absThird_le a ha ham
  · have hmpos : 0 < quadInfo E.law := lt_of_le_of_ne hm (Ne.symm hm0)
    have hspec := attenuationParameter_spec a (quadInfo E.law) ha ham
    have hsquare : attenuationParameter a (quadInfo E.law) ^ 2 ≤ eps ^ 2 := by
      apply (mul_le_mul_iff_left₀ hmpos).mp
      nlinarith [hspec.2]
    have hparam : attenuationParameter a (quadInfo E.law) ≤ eps := by
      nlinarith [hspec.1.1]
    exact (E.tune_absThird_le a ha ham).trans
      (mul_le_mul_of_nonneg_right hparam ha)

end OaiCapacityCriterionState
