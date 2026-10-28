module

public import Papers.OaiCapacityCriterionState.Helpers.PosteriorLaws
public import Papers.OaiCapacityCriterionState.Helpers.Broadcast

/-! # Composition of finite experiments

Finite products of normalized likelihoods realize iterated posterior products.
Relabeling the finite observation space leaves the posterior law unchanged.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace OaiCapacityCriterionState

variable {O O' : Type} [Fintype O] [Fintype O']

omit [Fintype O] in
-- @node: channelLikelihood_nonneg
/-- If [the channel parameter lies between zero and one](hyp:ht) and [the original
likelihoods are nonnegative](hyp:h), then [all likelihoods after passing the state
through the channel are nonnegative](goal). -/
lemma channelLikelihood_nonneg (t : ℝ) (ht : IsChannelParameter t)
    (lik : Fin 4 → O → ℝ) (h : ∀ i o, 0 ≤ lik i o) :
    ∀ i o, 0 ≤ channelLikelihood t lik i o := by
  intro i o
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg _ (h j o)
  unfold channel
  exact add_nonneg (mul_nonneg ht.1 (by split_ifs <;> norm_num))
    (div_nonneg (sub_nonneg.mpr ht.2) (by norm_num))

-- @node: channelLikelihood_sum
/-- If [the original likelihoods sum to one for each state](hyp:h), then [the
channel-transformed likelihoods also sum to one for each state](goal), for any real
channel parameter. -/
lemma channelLikelihood_sum (t : ℝ) (lik : Fin 4 → O → ℝ)
    (h : ∀ i, ∑ o, lik i o = 1) :
    ∀ i, ∑ o, channelLikelihood t lik i o = 1 := by
  intro i
  simp only [channelLikelihood]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, h, mul_one]
  exact channel_row_sum t i

omit [Fintype O] [Fintype O'] in
-- @node: productLikelihood_nonneg
/-- If [the first experiment has nonnegative likelihoods](hyp:h) and [the second
experiment has nonnegative likelihoods](hyp:h'), then [their product likelihood is
nonnegative for every state and observation pair](goal). -/
lemma productLikelihood_nonneg (lik : Fin 4 → O → ℝ) (lik' : Fin 4 → O' → ℝ)
    (h : ∀ i o, 0 ≤ lik i o) (h' : ∀ i o, 0 ≤ lik' i o) :
    ∀ i obs, 0 ≤ productLikelihood lik lik' i obs := by
  intro i obs
  exact mul_nonneg (h i obs.1) (h' i obs.2)

-- @node: productLikelihood_sum
/-- If [the first experiment's likelihoods sum to one for each state](hyp:h) and
[the second experiment's likelihoods do likewise](hyp:h'), then [their product
likelihoods sum to one over observation pairs for each state](goal). -/
lemma productLikelihood_sum (lik : Fin 4 → O → ℝ) (lik' : Fin 4 → O' → ℝ)
    (h : ∀ i, ∑ o, lik i o = 1) (h' : ∀ i, ∑ o, lik' i o = 1) :
    ∀ i, ∑ obs, productLikelihood lik lik' i obs = 1 := by
  intro i
  simp only [productLikelihood, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, h', mul_one]
  exact h i

-- @node: experimentLaw_reindex
/-- [Relabeling observations by a bijection leaves the law of the posterior vector
unchanged](goal). -/
lemma experimentLaw_reindex (e : O ≃ O') (lik : Fin 4 → O' → ℝ) :
    experimentLaw (fun i o => lik i (e o)) = experimentLaw lik := by
  classical
  exact e.sum_comp (fun o => ENNReal.ofReal (experimentMarginal lik o) •
    Measure.dirac (experimentPosterior lik o))

-- @node: productObservation
/-- For [an observation space](hyp:O), the [space of observation tuples of a given
length](goal) has [one empty tuple at length zero](step:1) and [a first observation
paired with a tuple of the remaining length at each positive length](step:2). -/
def productObservation (O : Type) : ℕ → Type
  | 0 => Unit
  | n + 1 => O × productObservation O n

-- @node: productObservationFintype
/-- For [a finite observation space](hyp:O) and [a tuple length](hyp:n),
[a finite enumeration of observation tuples of that length](goal) uses
[the singleton enumeration for the empty
tuple](step:1) and [the product of the observation enumeration and the recursively
enumerated remaining tuple for each positive length](step:2). -/
instance productObservationFintype (O : Type) [Fintype O] :
    (n : ℕ) → Fintype (productObservation O n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => by
      change Fintype (O × productObservation O n)
      letI := productObservationFintype O n
      infer_instance

-- @node: listLikelihood
/-- For [a list of experiment likelihoods](hyp:liks) on [a common observation
space](hyp:O), the [joint likelihood conditional on a state](goal) is [one for an
empty list](step:1) and [the first experiment's likelihood at the first observation
times the remaining list's likelihood at the remaining observations](step:2). -/
def listLikelihood : (liks : List (Fin 4 → O → ℝ)) →
    Fin 4 → productObservation O liks.length → ℝ
  | [], _, _ => 1
  | lik :: liks, i, obs => lik i obs.1 * listLikelihood liks i obs.2

omit [Fintype O] in
-- @node: listLikelihood_nonneg
/-- If [every likelihood in a list of experiments is nonnegative](hyp:h), then
[the list's joint likelihood is nonnegative for every state and observation
tuple](goal). -/
lemma listLikelihood_nonneg (liks : List (Fin 4 → O → ℝ))
    (h : ∀ lik ∈ liks, ∀ i o, 0 ≤ lik i o) :
    ∀ i obs, 0 ≤ listLikelihood liks i obs := by
  induction liks with
  | nil => intro i obs; exact zero_le_one
  | cons lik liks ih =>
      intro i obs
      exact mul_nonneg (h lik (by simp) i obs.1)
        (ih (fun l hl => h l (by simp [hl])) i obs.2)

-- @node: listLikelihood_sum
/-- If [each experiment in a list has likelihoods summing to one for every
state](hyp:h), then [the joint likelihood sums to one over observation tuples for
every state](goal). -/
lemma listLikelihood_sum (liks : List (Fin 4 → O → ℝ))
    (h : ∀ lik ∈ liks, ∀ i, ∑ o, lik i o = 1) :
    ∀ i, ∑ obs, listLikelihood liks i obs = 1 := by
  induction liks with
  | nil =>
      intro i
      change (∑ _ : Unit, (1 : ℝ)) = 1
      simp
  | cons lik liks ih =>
      exact productLikelihood_sum lik (listLikelihood liks)
        (h lik (by simp)) (ih (fun l hl => h l (by simp [hl])))

-- @node: experimentLaw_unit
/-- [An experiment with a single observation of likelihood one in every state has
the uninformative posterior law, concentrated at the uniform prior](goal). -/
lemma experimentLaw_unit : experimentLaw (fun (_ : Fin 4) (_ : Unit) => (1 : ℝ)) =
    uninformativeLaw := by
  suffices (Measure.dirac (fun _ : Fin 4 => (4 : ℝ)⁻¹)) = Measure.dirac unifVec by
    simpa [experimentLaw, experimentMarginal, experimentPosterior, uninformativeLaw] using this
  congr 1
  funext i
  norm_num [unifVec]

-- @node: experimentLaw_list
/-- If [every likelihood in a list of experiments is nonnegative](hyp:hnonneg) and
[each experiment's likelihoods sum to one for every state](hyp:hnorm), then [the
joint experiment's posterior law equals the iterated posterior product of the
individual laws, combined from right to left starting with the uninformative
law](goal). -/
lemma experimentLaw_list (liks : List (Fin 4 → O → ℝ))
    (hnonneg : ∀ lik ∈ liks, ∀ i o, 0 ≤ lik i o)
    (hnorm : ∀ lik ∈ liks, ∀ i, ∑ o, lik i o = 1) :
    experimentLaw (listLikelihood liks) =
      (liks.map experimentLaw).foldr starLaw uninformativeLaw := by
  induction liks with
  | nil => exact experimentLaw_unit
  | cons lik liks ih =>
      change experimentLaw (productLikelihood lik (listLikelihood liks)) = _
      rw [experimentLaw_prod lik (listLikelihood liks)
        (hnonneg lik (by simp))
        (listLikelihood_nonneg liks (fun l hl => hnonneg l (by simp [hl])))
        (hnorm lik (by simp))
        (listLikelihood_sum liks (fun l hl => hnorm l (by simp [hl])))]
      rw [ih (fun l hl => hnonneg l (by simp [hl]))
        (fun l hl => hnorm l (by simp [hl]))]
      rfl

-- @node: experimentLaw_list_isPosteriorLaw
/-- If [every likelihood in a list of experiments is nonnegative](hyp:hnonneg) and
[each experiment's likelihoods sum to one for every state](hyp:hnorm), then [the
joint experiment's posterior law is a probability law supported on probability
vectors over four states with mean one quarter in every coordinate](goal). -/
lemma experimentLaw_list_isPosteriorLaw (liks : List (Fin 4 → O → ℝ))
    (hnonneg : ∀ lik ∈ liks, ∀ i o, 0 ≤ lik i o)
    (hnorm : ∀ lik ∈ liks, ∀ i, ∑ o, lik i o = 1) :
    IsPosteriorLaw (experimentLaw (listLikelihood liks)) :=
  experimentLaw_isPosteriorLaw _ (listLikelihood_nonneg liks hnonneg)
    (listLikelihood_sum liks hnorm)

-- @node: experimentLaw_list_channel
/-- If [the channel parameter lies between zero and one](hyp:ht), [all likelihoods
in a list of experiments are nonnegative](hyp:hnonneg), and [each experiment's
likelihoods sum to one for every state](hyp:hnorm), then [the joint posterior law
after applying the channel to each experiment equals the posterior product of the
individually channel-transformed posterior laws, combined from right to left
starting with the uninformative law](goal). -/
lemma experimentLaw_list_channel (t : ℝ) (ht : IsChannelParameter t)
    (liks : List (Fin 4 → O → ℝ))
    (hnonneg : ∀ lik ∈ liks, ∀ i o, 0 ≤ lik i o)
    (hnorm : ∀ lik ∈ liks, ∀ i, ∑ o, lik i o = 1) :
    experimentLaw (listLikelihood (liks.map (channelLikelihood t))) =
      ((liks.map experimentLaw).map (channelStep t)).foldr starLaw uninformativeLaw := by
  rw [experimentLaw_list]
  · congr 1
    simp only [List.map_map]
    apply List.map_congr_left
    intro lik hlik
    exact experimentLaw_channel t ht lik (hnonneg lik hlik) (hnorm lik hlik)
  · intro lik hlik
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hlik
    exact channelLikelihood_nonneg t ht l (hnonneg l hl)
  · intro lik hlik
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hlik
    exact channelLikelihood_sum t l (hnorm l hl)

-- @node: integral_experimentLaw
/-- For [nonnegative experiment likelihoods](hyp:hnonneg), [the integral of any
real-valued function of the posterior vector equals the sum of its values at each
observation's posterior, weighted by that observation's marginal mass](goal). -/
lemma integral_experimentLaw (lik : Fin 4 → O → ℝ)
    (hnonneg : ∀ i o, 0 ≤ lik i o) (f : (Fin 4 → ℝ) → ℝ) :
    ∫ p, f p ∂(experimentLaw lik) =
      ∑ o, experimentMarginal lik o * f (experimentPosterior lik o) := by
  unfold experimentLaw
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro o _
    have hm : 0 ≤ experimentMarginal lik o :=
      mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => hnonneg i o))
    rw [ENNReal.toReal_ofReal hm]
  · intro o _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

end OaiCapacityCriterionState
