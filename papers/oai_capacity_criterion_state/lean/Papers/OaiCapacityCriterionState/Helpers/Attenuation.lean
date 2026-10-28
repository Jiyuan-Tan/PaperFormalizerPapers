module

public import Papers.OaiCapacityCriterionState.Helpers.GarblingClosure

/-! # Attenuating finite posterior experiments by observation garbling

Replacing an observation with an independent sample from its marginal realizes
channel smoothing of its posterior. This permits exact tuning of quadratic
information, while retaining an explicit garbling certificate and third moments.
Observation kernels compose, so attenuation can be interleaved with further
postprocessing on the same finite experiment presentation.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace OaiCapacityCriterionState

-- @node: garbledLikelihood_comp
/-- For a state-dependent likelihood and two successive observation kernels,
[garbling first by the first kernel and then by the second equals garbling once
by their composition, whose entries sum products over intermediate observations](goal). -/
lemma garbledLikelihood_comp {O P Q : Type} [Fintype O] [Fintype P]
    (lik : Fin 4 → O → ℝ) (K : O → P → ℝ) (L : P → Q → ℝ) :
    garbledLikelihood (garbledLikelihood lik K) L =
      garbledLikelihood lik (fun o q => ∑ p, K o p * L p q) := by
  funext i q
  simp only [garbledLikelihood, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o _
  apply Finset.sum_congr rfl
  intro p _
  ring

-- @node: marginalResamplingKernel
/-- For [a finite experiment](hyp:E), [a real retention weight](hyp:t),
[an original observation](hyp:o), and [a replacement observation](hyp:o'), the
[marginal resampling kernel entry](goal) is the retention weight times the
indicator that the observations coincide, plus one minus that weight times the
replacement observation's marginal probability. -/
noncomputable def marginalResamplingKernel (E : FiniteSpinExperiment) (t : ℝ)
    (o o' : E.Obs) : ℝ := by
  classical
  exact t * (if o = o' then 1 else 0) + (1 - t) * experimentMarginal E.likelihood o'

-- @node: marginalResamplingKernel_nonneg
/-- If [the retention weight lies between zero and one](hyp:ht), then
[every entry of the finite experiment's marginal resampling kernel is nonnegative](goal). -/
lemma marginalResamplingKernel_nonneg (E : FiniteSpinExperiment)
    (t : ℝ) (ht : IsChannelParameter t) (o o' : E.Obs) :
    0 ≤ marginalResamplingKernel E t o o' := by
  have hm : 0 ≤ experimentMarginal E.likelihood o' :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => E.nonneg i o')
  unfold marginalResamplingKernel
  exact add_nonneg (mul_nonneg ht.1 (by split_ifs <;> norm_num))
    (mul_nonneg (sub_nonneg.mpr ht.2) hm)

-- @node: marginalResamplingKernel_sum
/-- For any finite experiment and real retention weight, [the marginal resampling
kernel entries sum to one over replacement observations for each original observation](goal). -/
lemma marginalResamplingKernel_sum (E : FiniteSpinExperiment) (t : ℝ)
    (o : E.Obs) : ∑ o', marginalResamplingKernel E t o o' = 1 := by
  classical
  have hm : ∑ o', experimentMarginal E.likelihood o' = 1 := by
    simp only [experimentMarginal, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp [← Finset.mul_sum, E.normalized]
  simp [marginalResamplingKernel, Finset.sum_add_distrib,
    ← Finset.mul_sum, hm]

-- @node: garbledLikelihood_marginalResampling
/-- For any finite experiment and real weight, [garbling observations by marginal
resampling gives the same likelihood as applying the symmetric channel with that
weight to the state](goal). -/
lemma garbledLikelihood_marginalResampling (E : FiniteSpinExperiment) (t : ℝ) :
    garbledLikelihood E.likelihood (marginalResamplingKernel E t) =
      channelLikelihood t E.likelihood := by
  classical
  funext i o'
  have hleft : garbledLikelihood E.likelihood (marginalResamplingKernel E t) i o' =
      t * E.likelihood i o' + (1 - t) * experimentMarginal E.likelihood o' := by
    simp only [garbledLikelihood, marginalResamplingKernel, mul_add,
      Finset.sum_add_distrib]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, ← Finset.sum_mul, E.normalized, one_mul]
    ring
  rw [hleft]
  simp only [channelLikelihood, channel, add_mul, Finset.sum_add_distrib]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    ← Finset.mul_sum, experimentMarginal]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

-- @node: FiniteLawDegrades.attenuate
/-- If [the channel weight lies between zero and one](hyp:ht), then
[the finite experiment's posterior law can be degraded by observation garbling
to its channel-smoothed law](goal). -/
lemma FiniteLawDegrades.attenuate (E : FiniteSpinExperiment)
    (t : ℝ) (ht : IsChannelParameter t) :
    FiniteLawDegrades E.law (channelStep t E.law) := by
  refine ⟨E, E.channel t ht, rfl, E.law_channel t ht,
    marginalResamplingKernel E t, marginalResamplingKernel_nonneg E t ht,
    marginalResamplingKernel_sum E t, ?_⟩
  exact (garbledLikelihood_marginalResampling E t).symm

-- @node: FiniteLawDegrades.attenuate_right
/-- If [one posterior law can be degraded to another by finite observation
garbling](hyp:h) and [the channel weight lies between zero and one](hyp:ht), then
[the first law can also be degraded to the channel-smoothed second law](goal). -/
lemma FiniteLawDegrades.attenuate_right {mu nu : Measure (Fin 4 → ℝ)}
    (h : FiniteLawDegrades mu nu) (t : ℝ) (ht : IsChannelParameter t) :
    FiniteLawDegrades mu (channelStep t nu) := by
  obtain ⟨E, F, rfl, rfl, K, hK, hsum, heq⟩ := h
  let L := marginalResamplingKernel F t
  refine ⟨E, F.channel t ht, rfl, F.law_channel t ht,
    (fun o q => ∑ p, K o p * L p q), ?_, ?_, ?_⟩
  · intro o q
    exact Finset.sum_nonneg fun p _ =>
      mul_nonneg (hK o p) (marginalResamplingKernel_nonneg F t ht p q)
  · intro o
    change (∑ q : F.Obs, ∑ p : F.Obs, K o p * L p q) = 1
    dsimp only [L]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, marginalResamplingKernel_sum, mul_one, hsum]
  · change channelLikelihood t F.likelihood = _
    rw [← garbledLikelihood_marginalResampling, heq, garbledLikelihood_comp]
    rfl

-- @node: attenuationParameter
/-- For [a target quadratic information level](hyp:a) and [an initial quadratic
information level](hyp:m), the [attenuation weight](goal) is the square root of
the target divided by the initial level. -/
noncomputable def attenuationParameter (a m : ℝ) : ℝ := Real.sqrt (a / m)

-- @node: attenuationParameter_spec
/-- If [the target information is nonnegative](hyp:ha) and [does not exceed the
initial information](hyp:ham), then [the attenuation weight lies between zero
and one, and its square times the initial information equals the target](goal). -/
lemma attenuationParameter_spec (a m : ℝ) (ha : 0 ≤ a) (ham : a ≤ m) :
    IsChannelParameter (attenuationParameter a m) ∧
      attenuationParameter a m ^ 2 * m = a := by
  have hm : 0 ≤ m := ha.trans ham
  have hratio : a / m ≤ 1 := by
    by_cases hz : m = 0
    · simp [hz]
    · exact (div_le_one (lt_of_le_of_ne hm (Ne.symm hz))).mpr ham
  constructor
  · exact ⟨Real.sqrt_nonneg _, (Real.sqrt_le_sqrt hratio).trans_eq (by simp)⟩
  · unfold attenuationParameter
    rw [Real.sq_sqrt (div_nonneg ha hm)]
    by_cases hz : m = 0
    · have ha0 : a = 0 := le_antisymm (ham.trans_eq hz) ha
      simp [hz, ha0]
    · exact div_mul_cancel₀ a hz

-- @node: FiniteSpinExperiment.tune
/-- For [a finite experiment](hyp:E) and [a target quadratic information level](hyp:a)
that [is nonnegative](hyp:ha) and [does not exceed the experiment's quadratic
information](hyp:ham), the [tuned experiment](goal) applies a symmetric channel
whose weight is the square root of the target divided by the original information. -/
noncomputable def FiniteSpinExperiment.tune (E : FiniteSpinExperiment)
    (a : ℝ) (ha : 0 ≤ a) (ham : a ≤ quadInfo E.law) : FiniteSpinExperiment :=
  E.channel (attenuationParameter a (quadInfo E.law))
    (attenuationParameter_spec a (quadInfo E.law) ha ham).1

-- @node: FiniteSpinExperiment.tune_degrades
/-- If [the target information is nonnegative](hyp:ha) and [does not exceed the
finite experiment's quadratic information](hyp:ham), then [the original posterior
law can be degraded by finite observation garbling to the tuned experiment's law](goal). -/
lemma FiniteSpinExperiment.tune_degrades (E : FiniteSpinExperiment)
    (a : ℝ) (ha : 0 ≤ a) (ham : a ≤ quadInfo E.law) :
    FiniteLawDegrades E.law (E.tune a ha ham).law := by
  unfold FiniteSpinExperiment.tune
  rw [FiniteSpinExperiment.law_channel]
  exact FiniteLawDegrades.attenuate E _
    (attenuationParameter_spec a (quadInfo E.law) ha ham).1

-- @node: FiniteSpinExperiment.tune_moments
/-- If [the target information is nonnegative](hyp:ha) and [does not exceed the
finite experiment's quadratic information](hyp:ham), then [the tuned experiment
has quadratic information equal to the target, and both its signed third moment
and the absolute value of that moment equal their original values multiplied by
the cube of the attenuation weight](goal). -/
lemma FiniteSpinExperiment.tune_moments (E : FiniteSpinExperiment)
    (a : ℝ) (ha : 0 ≤ a) (ham : a ≤ quadInfo E.law) :
    quadInfo (E.tune a ha ham).law = a ∧
      thirdMoment (E.tune a ha ham).law =
        attenuationParameter a (quadInfo E.law) ^ 3 * thirdMoment E.law ∧
      absThird (E.tune a ha ham).law =
        attenuationParameter a (quadInfo E.law) ^ 3 * absThird E.law := by
  have ht := (attenuationParameter_spec a (quadInfo E.law) ha ham).1
  have h := moments_channelStep _ ht E.law E.law_isPosteriorLaw
  unfold FiniteSpinExperiment.tune
  rw [FiniteSpinExperiment.law_channel]
  refine ⟨?_, (congrArg (fun x => x.2.1) h), (congrArg (fun x => x.2.2) h)⟩
  exact (congrArg Prod.fst h).trans
    (attenuationParameter_spec a (quadInfo E.law) ha ham).2

-- @node: channelStep_mul
/-- For any two real channel weights and any measure on posterior vectors,
[successive channel smoothing equals a single smoothing with the product of
the weights](goal). -/
lemma channelStep_mul (s t : ℝ) (mu : Measure (Fin 4 → ℝ)) :
    channelStep s (channelStep t mu) = channelStep (s * t) mu := by
  have hs : Measurable (channelPosterior s) := by unfold channelPosterior; fun_prop
  have ht : Measurable (channelPosterior t) := by unfold channelPosterior; fun_prop
  unfold channelStep
  rw [Measure.map_map hs ht]
  congr 1
  funext p i
  simp [channelPosterior, unifVec]
  ring

-- @node: channelStep_comm
/-- For any two real channel weights and any measure on posterior vectors,
[applying the two channel smoothings in either order gives the same measure](goal). -/
lemma channelStep_comm (s t : ℝ) (mu : Measure (Fin 4 → ℝ)) :
    channelStep s (channelStep t mu) = channelStep t (channelStep s mu) := by
  rw [channelStep_mul, channelStep_mul, mul_comm s t]

-- @node: channelStep_isSymmetricLaw
/-- If [a measure on posterior vectors is invariant under permutations of the
four states](hyp:hmu), then [channel smoothing with any real weight preserves
that invariance](goal). -/
lemma channelStep_isSymmetricLaw (t : ℝ) (mu : Measure (Fin 4 → ℝ))
    (hmu : IsSymmetricLaw mu) : IsSymmetricLaw (channelStep t mu) := by
  intro perm
  have hc : Measurable (channelPosterior t) := by unfold channelPosterior; fun_prop
  have hp : Measurable (fun p : Fin 4 → ℝ => p ∘ perm) := by fun_prop
  unfold channelStep
  rw [Measure.map_map hp hc]
  have hcomm : (fun p : Fin 4 → ℝ => p ∘ perm) ∘ channelPosterior t =
      channelPosterior t ∘ (fun p : Fin 4 → ℝ => p ∘ perm) := by
    funext p i
    rfl
  rw [hcomm, ← Measure.map_map hc hp, hmu perm]

-- @node: channelStep_preserves_local_channel
/-- If [the additional smoothing weight lies between zero and one](hyp:ht) and
[a posterior law is obtainable by channel smoothing at the original weight](hyp:hnu),
then [the additionally smoothed law is still obtainable by channel smoothing at
the original weight](goal). -/
lemma channelStep_preserves_local_channel (s t : ℝ)
    (ht : IsChannelParameter t) (nu : PosteriorLaw)
    (hnu : LocalMomentsChannel s nu) :
    LocalMomentsChannel s
      ⟨channelStep t nu, channelStep_isPosteriorLaw t ht nu nu.property⟩ := by
  obtain ⟨nu0, hnu0⟩ := hnu
  refine ⟨⟨channelStep t nu0, channelStep_isPosteriorLaw t ht nu0 nu0.property⟩, ?_⟩
  change channelStep t nu = channelStep s (channelStep t nu0)
  rw [hnu0, channelStep_comm]

-- @node: FiniteSpinExperiment.tune_mem
/-- If [a class of measures is closed under every channel smoothing with weight
between zero and one](hyp:hC), [the finite experiment's law belongs to that
class](hyp:hE), and [the target information is nonnegative](hyp:ha) and
[does not exceed the experiment's quadratic information](hyp:ham), then
[the tuned experiment's law also belongs to the class](goal). -/
lemma FiniteSpinExperiment.tune_mem (E : FiniteSpinExperiment)
    (C : Set (Measure (Fin 4 → ℝ)))
    (hC : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ mu ∈ C, channelStep t mu ∈ C)
    (hE : E.law ∈ C) (a : ℝ) (ha : 0 ≤ a) (ham : a ≤ quadInfo E.law) :
    (E.tune a ha ham).law ∈ C := by
  unfold FiniteSpinExperiment.tune
  rw [FiniteSpinExperiment.law_channel]
  exact hC _ (attenuationParameter_spec a (quadInfo E.law) ha ham).1 _ hE

-- @node: FiniteSpinExperiment.tune_symmetric
/-- If [a finite experiment's posterior law is invariant under permutations of
the four states](hyp:hE), [the target information is nonnegative](hyp:ha), and
[the target does not exceed the experiment's quadratic information](hyp:ham),
then [the tuned experiment's law is also invariant under state permutations](goal). -/
lemma FiniteSpinExperiment.tune_symmetric (E : FiniteSpinExperiment)
    (hE : IsSymmetricLaw E.law) (a : ℝ) (ha : 0 ≤ a) (ham : a ≤ quadInfo E.law) :
    IsSymmetricLaw (E.tune a ha ham).law := by
  unfold FiniteSpinExperiment.tune
  rw [FiniteSpinExperiment.law_channel]
  exact channelStep_isSymmetricLaw _ _ hE

-- @node: FiniteSpinExperiment.tune_local_channel
/-- If [a finite experiment's law is obtainable by channel smoothing at a given
weight](hyp:hE), [the target information is nonnegative](hyp:ha), and
[the target does not exceed the experiment's quadratic information](hyp:ham),
then [the tuned experiment's law is also obtainable by channel smoothing at
that same weight](goal). -/
lemma FiniteSpinExperiment.tune_local_channel (E : FiniteSpinExperiment)
    (s : ℝ) (hE : LocalMomentsChannel s ⟨E.law, E.law_isPosteriorLaw⟩)
    (a : ℝ) (ha : 0 ≤ a) (ham : a ≤ quadInfo E.law) :
    LocalMomentsChannel s
      ⟨(E.tune a ha ham).law, (E.tune a ha ham).law_isPosteriorLaw⟩ := by
  obtain ⟨nu0, hnu0⟩ := hE
  have ht := (attenuationParameter_spec a (quadInfo E.law) ha ham).1
  refine ⟨⟨channelStep (attenuationParameter a (quadInfo E.law)) nu0,
    channelStep_isPosteriorLaw _ ht nu0 nu0.property⟩, ?_⟩
  change (E.tune a ha ham).law = channelStep s
    (channelStep (attenuationParameter a (quadInfo E.law)) nu0)
  unfold FiniteSpinExperiment.tune
  rw [FiniteSpinExperiment.law_channel]
  exact (congrArg (channelStep (attenuationParameter a (quadInfo E.law)))
    (show E.law = channelStep s nu0 from hnu0)).trans (channelStep_comm _ _ _)

-- @node: FiniteLawDegrades.tune_right
/-- If [a law can be degraded by finite observation garbling to a finite
experiment's law](hyp:h), [the target information is nonnegative](hyp:ha), and
[the target does not exceed the experiment's quadratic information](hyp:ham),
then [the original law can also be degraded to the tuned experiment's law](goal). -/
lemma FiniteLawDegrades.tune_right {mu : Measure (Fin 4 → ℝ)}
    (E : FiniteSpinExperiment) (h : FiniteLawDegrades mu E.law)
    (a : ℝ) (ha : 0 ≤ a) (ham : a ≤ quadInfo E.law) :
    FiniteLawDegrades mu (E.tune a ha ham).law := by
  unfold FiniteSpinExperiment.tune
  rw [FiniteSpinExperiment.law_channel]
  exact h.attenuate_right _ (attenuationParameter_spec a (quadInfo E.law) ha ham).1

-- @node: FiniteSpinExperiment.tune_absThird_mul
/-- If [the target information is nonnegative](hyp:ha) and [does not exceed the
finite experiment's quadratic information](hyp:ham), then [the absolute value
of the tuned signed third moment times the original quadratic information equals
the attenuation weight times the target information times the absolute value of
the original signed third moment](goal). -/
lemma FiniteSpinExperiment.tune_absThird_mul (E : FiniteSpinExperiment)
    (a : ℝ) (ha : 0 ≤ a) (ham : a ≤ quadInfo E.law) :
    absThird (E.tune a ha ham).law * quadInfo E.law =
      attenuationParameter a (quadInfo E.law) * a * absThird E.law := by
  rw [(E.tune_moments a ha ham).2.2]
  calc
    _ = attenuationParameter a (quadInfo E.law) *
        (attenuationParameter a (quadInfo E.law) ^ 2 * quadInfo E.law) *
          absThird E.law := by ring
    _ = _ := by rw [(attenuationParameter_spec a (quadInfo E.law) ha ham).2]

-- @node: FiniteSpinExperiment.tune_absThird_sq_mul
/-- If [the target information is nonnegative](hyp:ha) and [does not exceed the
finite experiment's quadratic information](hyp:ham), then [the squared absolute
value of the tuned signed third moment times the cube of the original quadratic
information equals the cube of the target times the squared absolute value of
the original signed third moment](goal). -/
lemma FiniteSpinExperiment.tune_absThird_sq_mul (E : FiniteSpinExperiment)
    (a : ℝ) (ha : 0 ≤ a) (ham : a ≤ quadInfo E.law) :
    absThird (E.tune a ha ham).law ^ 2 * quadInfo E.law ^ 3 =
      a ^ 3 * absThird E.law ^ 2 := by
  rw [(E.tune_moments a ha ham).2.2]
  calc
    _ = (attenuationParameter a (quadInfo E.law) ^ 2 * quadInfo E.law) ^ 3 *
        absThird E.law ^ 2 := by ring
    _ = _ := by rw [(attenuationParameter_spec a (quadInfo E.law) ha ham).2]

-- @node: FiniteSpinExperiment.tune_absThird_le_of_cubic_budget
/-- If [the target information is nonnegative](hyp:ha), [does not exceed the
finite experiment's quadratic information](hyp:ham), [the desired bound is
nonnegative](hyp:hb), and [the target cubed times the squared absolute value of
the original signed third moment is at most the bound squared times the original
quadratic information cubed](hyp:hbudget), then [the absolute value of the tuned
signed third moment is at most the desired bound](goal). -/
lemma FiniteSpinExperiment.tune_absThird_le_of_cubic_budget (E : FiniteSpinExperiment)
    (a : ℝ) (ha : 0 ≤ a) (ham : a ≤ quadInfo E.law)
    (b : ℝ) (hb : 0 ≤ b)
    (hbudget : a ^ 3 * absThird E.law ^ 2 ≤ b ^ 2 * quadInfo E.law ^ 3) :
    absThird (E.tune a ha ham).law ≤ b := by
  have hm : 0 ≤ quadInfo E.law := ha.trans ham
  by_cases hm0 : quadInfo E.law = 0
  · have ha0 : a = 0 := le_antisymm (ham.trans_eq hm0) ha
    rw [(E.tune_moments a ha ham).2.2]
    simpa only [attenuationParameter, ha0, hm0, div_zero, Real.sqrt_zero,
      zero_pow (by decide : 3 ≠ 0), zero_mul] using hb
  · have hmpos : 0 < quadInfo E.law := lt_of_le_of_ne hm (Ne.symm hm0)
    rw [← E.tune_absThird_sq_mul a ha ham] at hbudget
    have hs := le_of_mul_le_mul_right hbudget (pow_pos hmpos 3)
    exact (sq_le_sq₀ (abs_nonneg _) hb).mp hs

-- @node: FiniteSpinExperiment.tune_absThird_le_of_bounds
/-- Suppose [the target information is nonnegative](hyp:ha), [is at most an
intermediate information level](hyp:haL), and [that level is at most the finite
experiment's quadratic information](hyp:hL). If [the absolute value of the
original signed third moment is at most a given moment bound](hyp:hD),
[the desired final bound is nonnegative](hyp:hb), and [the target cubed times
the moment bound squared is at most the final bound squared times the intermediate
information level cubed](hyp:hbudget), then [the absolute value of the tuned
signed third moment is at most the desired final bound](goal). -/
lemma FiniteSpinExperiment.tune_absThird_le_of_bounds (E : FiniteSpinExperiment)
    (a : ℝ) (ha : 0 ≤ a) (L D b : ℝ) (haL : a ≤ L)
    (hL : L ≤ quadInfo E.law) (hD : absThird E.law ≤ D) (hb : 0 ≤ b)
    (hbudget : a ^ 3 * D ^ 2 ≤ b ^ 2 * L ^ 3) :
    absThird (E.tune a ha (haL.trans hL)).law ≤ b := by
  apply E.tune_absThird_le_of_cubic_budget a ha (haL.trans hL) b hb
  calc
    a ^ 3 * absThird E.law ^ 2 ≤ a ^ 3 * D ^ 2 :=
      mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hD)).mpr hD)
        (pow_nonneg ha 3)
    _ ≤ b ^ 2 * L ^ 3 := hbudget
    _ ≤ b ^ 2 * quadInfo E.law ^ 3 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (ha.trans haL) hL 3) (sq_nonneg b)

end OaiCapacityCriterionState
