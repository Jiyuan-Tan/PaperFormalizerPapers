module

public import Papers.OaiCapacityCriterionState.Helpers.ExperimentGarbling
public import Papers.OaiCapacityCriterionState.Helpers.InformationFlow

/-! # Finite garblings commute with channels and independent products

Finite experiments retain explicit normalized likelihoods. A garbling of their
observations decreases quadratic information, and is preserved by both operations
used in the tree recursion. Consequently the recursive tree experiments have
monotone, convergent quadratic information at every vertex; their limits
supply the labels in the companion-to-capacity argument.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace OaiCapacityCriterionState

-- @node: garbledLikelihood_channel
/-- For [a channel parameter](hyp:t), [four-state observation likelihoods](hyp:lik),
and [an observation garbling kernel](hyp:K), [applying the channel and then garbling
gives the same likelihoods as garbling and then applying the channel](goal). -/
lemma garbledLikelihood_channel {O O' : Type} [Fintype O]
    (t : ℝ) (lik : Fin 4 → O → ℝ) (K : O → O' → ℝ) :
    garbledLikelihood (channelLikelihood t lik) K =
      channelLikelihood t (garbledLikelihood lik K) := by
  funext i o'
  simp only [garbledLikelihood, channelLikelihood, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro o _
  ring

-- @node: garbledLikelihood_product
/-- For [a first set of four-state observation likelihoods](hyp:lik),
[a second set](hyp:lik'), and [respective observation garbling kernels](hyp:K,K'),
[garbling the conditionally independent product with the product kernel gives
the product of the separately garbled likelihoods](goal). -/
lemma garbledLikelihood_product {O O' P P' : Type} [Fintype O] [Fintype P]
    (lik : Fin 4 → O → ℝ) (lik' : Fin 4 → P → ℝ)
    (K : O → O' → ℝ) (K' : P → P' → ℝ) :
    garbledLikelihood (productLikelihood lik lik')
      (fun x y => K x.1 y.1 * K' x.2 y.2) =
      productLikelihood (garbledLikelihood lik K) (garbledLikelihood lik' K') := by
  funext i obs
  simp only [garbledLikelihood, productLikelihood, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o _
  apply Finset.sum_congr rfl
  intro p _
  ring

-- @node: FiniteSpinExperiment
/-- A [finite experiment about a four-state hidden variable](goal) consists of
a finite observation space and nonnegative conditional observation probabilities
that sum to one for each hidden state. -/
structure FiniteSpinExperiment where
  Obs : Type
  [finite : Fintype Obs]
  likelihood : Fin 4 → Obs → ℝ
  nonneg : ∀ i o, 0 ≤ likelihood i o
  normalized : ∀ i, ∑ o, likelihood i o = 1

attribute [instance] FiniteSpinExperiment.finite


-- @node: FiniteSpinExperiment.law
/-- For [a finite four-state experiment](hyp:E), its [posterior law](goal) is
the distribution of the posterior probability vector under a uniform prior. -/
noncomputable def FiniteSpinExperiment.law (E : FiniteSpinExperiment) :
    Measure (Fin 4 → ℝ) := experimentLaw E.likelihood

-- @node: FiniteSpinExperiment.law_isPosteriorLaw
/-- For [a finite four-state experiment](hyp:E), [its posterior law is a probability
measure supported on the probability simplex with mean equal to the uniform
prior](goal). -/
lemma FiniteSpinExperiment.law_isPosteriorLaw (E : FiniteSpinExperiment) :
    IsPosteriorLaw E.law :=
  experimentLaw_isPosteriorLaw E.likelihood E.nonneg E.normalized

-- @node: FiniteSpinExperiment.channel
/-- For [a finite experiment](hyp:E) and [a channel parameter](hyp:t)
[between zero and one, inclusive](hyp:ht), the [experiment obtained by applying
the channel](goal) uses [the original observation space](step:1),
[its finite enumeration](step:2), and [the channel-transformed likelihoods](step:3),
which are [nonnegative](step:4) and [sum to one for each hidden state](step:5). -/
noncomputable def FiniteSpinExperiment.channel (E : FiniteSpinExperiment)
    (t : ℝ) (ht : IsChannelParameter t) : FiniteSpinExperiment where
  Obs := E.Obs
  finite := E.finite
  likelihood := channelLikelihood t E.likelihood
  nonneg := channelLikelihood_nonneg t ht E.likelihood E.nonneg
  normalized := channelLikelihood_sum t E.likelihood E.normalized

-- @node: FiniteSpinExperiment.law_channel
/-- For [a finite experiment](hyp:E) and [a channel parameter](hyp:t)
[between zero and one, inclusive](hyp:ht), [the posterior law after applying
the channel to the experiment equals the channel transformation of its posterior
law](goal). -/
lemma FiniteSpinExperiment.law_channel (E : FiniteSpinExperiment)
    (t : ℝ) (ht : IsChannelParameter t) :
    (E.channel t ht).law = channelStep t E.law :=
  experimentLaw_channel t ht E.likelihood E.nonneg E.normalized

-- @node: FiniteSpinExperiment.product
/-- For [two finite experiments](hyp:E,F), their [conditionally independent
product experiment](goal) has [pairs of observations](step:1), [the corresponding
finite enumeration](step:2), and [likelihoods equal to the products of the two
likelihoods](step:3), which are [nonnegative](step:4) and [sum to one for each
hidden state](step:5). -/
noncomputable def FiniteSpinExperiment.product (E F : FiniteSpinExperiment) :
    FiniteSpinExperiment where
  Obs := E.Obs × F.Obs
  finite := inferInstance
  likelihood := productLikelihood E.likelihood F.likelihood
  nonneg := productLikelihood_nonneg _ _ E.nonneg F.nonneg
  normalized := productLikelihood_sum _ _ E.normalized F.normalized

-- @node: FiniteSpinExperiment.law_product
/-- For [two finite experiments](hyp:E,F), [the posterior law of their conditionally
independent product equals the Bayesian combination of their posterior laws](goal). -/
lemma FiniteSpinExperiment.law_product (E F : FiniteSpinExperiment) :
    (E.product F).law = starLaw E.law F.law :=
  experimentLaw_prod _ _ E.nonneg F.nonneg E.normalized F.normalized

-- @node: revealingExperiment
/-- The [fully revealing four-state experiment](goal) uses [the four hidden states
as observations](step:1), [their finite enumeration](step:2), and [probability one
for observing the true state and zero for every other observation](step:3);
these probabilities are [nonnegative](step:4) and [sum to one](step:5). -/
noncomputable def revealingExperiment : FiniteSpinExperiment where
  Obs := Fin 4
  finite := inferInstance
  likelihood := fun i j => if i = j then 1 else 0
  nonneg := by intros; split_ifs <;> norm_num
  normalized := by intro i; simp

-- @node: revealingExperiment_law
/-- [The posterior law of the fully revealing experiment is the uniform mixture
of the four point masses at certainty about each hidden state](goal). -/
lemma revealingExperiment_law : revealingExperiment.law = revealingLaw := by
  classical
  simp [FiniteSpinExperiment.law, revealingExperiment, experimentLaw,
    experimentMarginal, experimentPosterior, revealingLaw, eq_comm]
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  funext j
  simp [Pi.single_apply, eq_comm]

-- @node: uninformativeExperiment
/-- The [uninformative four-state experiment](goal) has [a single possible
observation](step:1), [its finite enumeration](step:2), and [likelihood one for
that observation in every hidden state](step:3); these likelihoods are
[nonnegative](step:4) and [sum to one](step:5). -/
noncomputable def uninformativeExperiment : FiniteSpinExperiment where
  Obs := Unit
  finite := inferInstance
  likelihood := fun _ _ => 1
  nonneg := by intros; exact zero_le_one
  normalized := by intro i; simp

-- @node: uninformativeExperiment_law
/-- [The posterior law of the uninformative experiment is concentrated at the
uniform prior](goal). -/
lemma uninformativeExperiment_law :
    uninformativeExperiment.law = uninformativeLaw := experimentLaw_unit

-- @node: FiniteLawDegrades
/-- For [an initial posterior-vector measure](hyp:mu) and [a target
posterior-vector measure](hyp:nu), [finite degradation](goal) means there exist
two finite experiments and an observation kernel such that [the first experiment
has the initial law](step:1), [the second has the target law](step:2),
[the kernel is nonnegative](step:3), [each kernel row sums to one](step:4),
and [the second experiment's likelihoods result from garbling the first
experiment's likelihoods with this kernel](step:5). -/
def FiniteLawDegrades (mu nu : Measure (Fin 4 → ℝ)) : Prop :=
  ∃ E F : FiniteSpinExperiment, E.law = mu ∧ F.law = nu ∧
    ∃ K : E.Obs → F.Obs → ℝ,
      (∀ o o', 0 ≤ K o o') ∧ (∀ o, ∑ o', K o o' = 1) ∧
      F.likelihood = garbledLikelihood E.likelihood K

-- @node: FiniteLawDegrades.quadInfo_le
/-- If [one posterior law is a finite garbling of another](hyp:h), [the garbled
law has no greater quadratic information than the original law](goal). -/
lemma FiniteLawDegrades.quadInfo_le {mu nu : Measure (Fin 4 → ℝ)}
    (h : FiniteLawDegrades mu nu) : quadInfo nu ≤ quadInfo mu := by
  obtain ⟨E, F, rfl, rfl, K, hK, hsum, heq⟩ := h
  change quadInfo (experimentLaw F.likelihood) ≤ _
  rw [heq]
  exact quadInfo_garbledLikelihood_le E.likelihood K E.nonneg hK hsum

-- @node: FiniteLawDegrades.channel
/-- If [a target law is a finite garbling of an initial law](hyp:h), then for
[a channel parameter](hyp:t) [between zero and one, inclusive](hyp:ht),
[the channel-transformed target law is a finite garbling of the
channel-transformed initial law](goal). -/
lemma FiniteLawDegrades.channel {mu nu : Measure (Fin 4 → ℝ)}
    (h : FiniteLawDegrades mu nu) (t : ℝ) (ht : IsChannelParameter t) :
    FiniteLawDegrades (channelStep t mu) (channelStep t nu) := by
  obtain ⟨E, F, rfl, rfl, K, hK, hsum, heq⟩ := h
  refine ⟨E.channel t ht, F.channel t ht, E.law_channel t ht,
    F.law_channel t ht, K, hK, hsum, ?_⟩
  change channelLikelihood t F.likelihood =
    garbledLikelihood (channelLikelihood t E.likelihood) K
  rw [heq, garbledLikelihood_channel]

-- @node: FiniteLawDegrades.product
/-- If [a first target law is a finite garbling of a first initial law](hyp:h)
and [a second target law is a finite garbling of a second initial law](hyp:h'),
[the Bayesian combination of the target laws is a finite garbling of the
Bayesian combination of the initial laws](goal). -/
lemma FiniteLawDegrades.product {mu nu mu' nu' : Measure (Fin 4 → ℝ)}
    (h : FiniteLawDegrades mu nu) (h' : FiniteLawDegrades mu' nu') :
    FiniteLawDegrades (starLaw mu mu') (starLaw nu nu') := by
  obtain ⟨E, F, rfl, rfl, K, hK, hsum, heq⟩ := h
  obtain ⟨E', F', rfl, rfl, K', hK', hsum', heq'⟩ := h'
  refine ⟨E.product E', F.product F', E.law_product E', F.law_product F',
    (fun x y => K x.1 y.1 * K' x.2 y.2),
    (fun x y => mul_nonneg (hK _ _) (hK' _ _)), ?_, ?_⟩
  · intro x
    change (∑ y : F.Obs × F'.Obs, K x.1 y.1 * K' x.2 y.2) = 1
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, hsum', mul_one, hsum]
  · change productLikelihood F.likelihood F'.likelihood =
      garbledLikelihood (productLikelihood E.likelihood E'.likelihood)
        (fun x y => K x.1 y.1 * K' x.2 y.2)
    rw [heq, heq', garbledLikelihood_product]

-- @node: FiniteLawDegrades.refl
/-- For [a finite experiment](hyp:E), [its posterior law is a finite garbling
of itself](goal). -/
lemma FiniteLawDegrades.refl (E : FiniteSpinExperiment) :
    FiniteLawDegrades E.law E.law := by
  classical
  refine ⟨E, E, rfl, rfl, (fun o o' => if o = o' then 1 else 0), ?_, ?_, ?_⟩
  · intro o o'; dsimp only; split_ifs <;> norm_num
  · intro o; simp
  · funext i o
    simp [garbledLikelihood]

-- @node: FiniteLawDegrades.from_revealing
/-- For [any finite four-state experiment](hyp:E), [its posterior law is a finite
garbling of the fully revealing posterior law](goal). -/
lemma FiniteLawDegrades.from_revealing (E : FiniteSpinExperiment) :
    FiniteLawDegrades revealingLaw E.law := by
  refine ⟨revealingExperiment, E, revealingExperiment_law, rfl,
    E.likelihood, E.nonneg, E.normalized, ?_⟩
  funext i o
  change E.likelihood i o = ∑ j : Fin 4, (if i = j then 1 else 0) * E.likelihood j o
  simp

-- @node: treeExperimentLaw_finite
/-- For [a tree with bounded branching](hyp:T), [a channel parameter](hyp:lam)
[strictly between zero and one](hyp:hlam), [an observation depth](hyp:n), and
[a vertex address](hyp:v), [the recursive tree posterior law is the posterior
law of some finite experiment](goal). -/
lemma treeExperimentLaw_finite {B : ℕ} (T : BoundedTree B) (lam : ℝ)
    (hlam : MainLambda lam) (n : ℕ) (v : List (Fin B)) :
    ∃ E : FiniteSpinExperiment, E.law = treeExperimentLaw T lam n v := by
  apply treeExperimentLaw_mem {mu | ∃ E : FiniteSpinExperiment, E.law = mu}
    ⟨revealingExperiment, revealingExperiment_law⟩
    ⟨uninformativeExperiment, uninformativeExperiment_law⟩
    (fun t ht mu hmu => ?_) (fun mu hmu nu hnu => ?_) T lam hlam n v
  · obtain ⟨E, rfl⟩ := hmu
    exact ⟨E.channel t ht, E.law_channel t ht⟩
  · obtain ⟨E, rfl⟩ := hmu
    obtain ⟨F, rfl⟩ := hnu
    exact ⟨E.product F, E.law_product F⟩

-- @node: FiniteLawDegrades.foldr
/-- For [a finite list of indices](hyp:l) and [two indexed families of posterior
laws](hyp:f,g), if [each target law at an index in the list is a finite garbling
of its corresponding initial law](hyp:h), [combining the target laws successively,
starting from the uninformative law, gives a finite garbling of the corresponding
combination of initial laws](goal). -/
lemma FiniteLawDegrades.foldr {α : Type} (l : List α)
    (f g : α → Measure (Fin 4 → ℝ))
    (h : ∀ x ∈ l, FiniteLawDegrades (f x) (g x)) :
    FiniteLawDegrades ((l.map f).foldr starLaw uninformativeLaw)
      ((l.map g).foldr starLaw uninformativeLaw) := by
  induction l with
  | nil =>
      simpa only [List.map_nil, List.foldr_nil, uninformativeExperiment_law]
        using FiniteLawDegrades.refl uninformativeExperiment
  | cons x l ih =>
      exact (h x (by simp)).product (ih (fun y hy => h y (by simp [hy])))

-- @node: treeExperimentLaw_degrades_succ
/-- For [a tree with bounded branching](hyp:T), [a channel parameter](hyp:lam)
[strictly between zero and one](hyp:hlam), [a depth](hyp:n), and [a vertex
address](hyp:v), [the tree posterior law at the next depth is a finite garbling
of the law at the current depth](goal). -/
lemma treeExperimentLaw_degrades_succ {B : ℕ} (T : BoundedTree B) (lam : ℝ)
    (hlam : MainLambda lam) (n : ℕ) (v : List (Fin B)) :
    FiniteLawDegrades (treeExperimentLaw T lam n v)
      (treeExperimentLaw T lam (n + 1) v) := by
  induction n generalizing v with
  | zero =>
      obtain ⟨E, hE⟩ := treeExperimentLaw_finite T lam hlam 1 v
      rw [← hE]
      exact FiniteLawDegrades.from_revealing E
  | succ n ih =>
      simp only [treeExperimentLaw, List.map_map, Function.comp_def]
      apply FiniteLawDegrades.foldr
      intro w _
      simpa only [treeExperimentLaw, List.map_map, Function.comp_def] using
        (ih w).channel lam ⟨hlam.1.le, hlam.2.le⟩

-- @node: treeExperimentLaw_isPosteriorLaw
/-- For [a tree with bounded branching](hyp:T), [a channel parameter](hyp:lam)
[strictly between zero and one](hyp:hlam), [a depth](hyp:n), and [a vertex
address](hyp:v), [the tree posterior law is a probability measure supported
on the probability simplex with uniform mean](goal). -/
lemma treeExperimentLaw_isPosteriorLaw {B : ℕ} (T : BoundedTree B) (lam : ℝ)
    (hlam : MainLambda lam) (n : ℕ) (v : List (Fin B)) :
    IsPosteriorLaw (treeExperimentLaw T lam n v) := by
  obtain ⟨E, hE⟩ := treeExperimentLaw_finite T lam hlam n v
  rw [← hE]
  exact E.law_isPosteriorLaw

-- @node: treeExperimentLaw_quadInfo_mem_Icc
/-- For [a tree with bounded branching](hyp:T), [a channel parameter](hyp:lam)
[strictly between zero and one](hyp:hlam), [a depth](hyp:n), and [a vertex
address](hyp:v), [the quadratic information of the tree posterior law lies
between zero and three, inclusive](goal). -/
lemma treeExperimentLaw_quadInfo_mem_Icc {B : ℕ} (T : BoundedTree B) (lam : ℝ)
    (hlam : MainLambda lam) (n : ℕ) (v : List (Fin B)) :
    quadInfo (treeExperimentLaw T lam n v) ∈ Set.Icc 0 3 :=
  quadInfo_mem_Icc ⟨_, treeExperimentLaw_isPosteriorLaw T lam hlam n v⟩

-- @node: treeExperimentLaw_quadInfo_antitone
/-- For [a tree with bounded branching](hyp:T), [a channel parameter](hyp:lam)
[strictly between zero and one](hyp:hlam), and [a vertex address](hyp:v),
[the quadratic information of the tree posterior law is nonincreasing as
observation depth increases](goal). -/
lemma treeExperimentLaw_quadInfo_antitone {B : ℕ} (T : BoundedTree B) (lam : ℝ)
    (hlam : MainLambda lam) (v : List (Fin B)) :
    Antitone (fun n => quadInfo (treeExperimentLaw T lam n v)) := by
  apply antitone_nat_of_succ_le
  intro n
  exact (treeExperimentLaw_degrades_succ T lam hlam n v).quadInfo_le

-- @node: treeExperimentLimit
/-- For [a tree with bounded branching](hyp:T), [a channel parameter](hyp:lam),
and [a vertex address](hyp:v), the [limiting tree information](goal) is the
limit of the quadratic information of the recursive tree posterior laws as
observation depth tends to infinity, using the general limit operator. -/
noncomputable def treeExperimentLimit {B : ℕ} (T : BoundedTree B) (lam : ℝ)
    (v : List (Fin B)) : ℝ :=
  Filter.limUnder Filter.atTop (fun n => quadInfo (treeExperimentLaw T lam n v))

-- @node: treeExperimentLaw_quadInfo_tendsto
/-- For [a tree with bounded branching](hyp:T), [a channel parameter](hyp:lam)
[strictly between zero and one](hyp:hlam), and [a vertex address](hyp:v),
[the quadratic information of the tree posterior laws converges to the limiting
tree information as observation depth tends to infinity](goal). -/
lemma treeExperimentLaw_quadInfo_tendsto {B : ℕ} (T : BoundedTree B) (lam : ℝ)
    (hlam : MainLambda lam) (v : List (Fin B)) :
    Filter.Tendsto (fun n => quadInfo (treeExperimentLaw T lam n v))
      Filter.atTop (nhds (treeExperimentLimit T lam v)) := by
  have hb : BddBelow (Set.range (fun n => quadInfo (treeExperimentLaw T lam n v))) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (treeExperimentLaw_quadInfo_mem_Icc T lam hlam n v).1
  have hc := tendsto_atTop_ciInf (treeExperimentLaw_quadInfo_antitone T lam hlam v) hb
  unfold treeExperimentLimit
  rw [hc.limUnder_eq]
  exact hc

-- @node: treeExperimentLimit_mem_Icc
/-- For [a tree with bounded branching](hyp:T), [a channel parameter](hyp:lam)
[strictly between zero and one](hyp:hlam), and [a vertex address](hyp:v),
[the limiting tree information lies between zero and three, inclusive](goal). -/
lemma treeExperimentLimit_mem_Icc {B : ℕ} (T : BoundedTree B) (lam : ℝ)
    (hlam : MainLambda lam) (v : List (Fin B)) :
    treeExperimentLimit T lam v ∈ Set.Icc 0 3 :=
  isClosed_Icc.mem_of_tendsto (treeExperimentLaw_quadInfo_tendsto T lam hlam v)
    (Filter.Eventually.of_forall (fun n => treeExperimentLaw_quadInfo_mem_Icc T lam hlam n v))

-- @node: treeExperimentLimit_le_quadInfo
/-- For [a tree with bounded branching](hyp:T), [a channel parameter](hyp:lam)
[strictly between zero and one](hyp:hlam), [a vertex address](hyp:v), and
[any finite observation depth](hyp:n), [the limiting tree information is no
greater than the quadratic information at that depth](goal). -/
lemma treeExperimentLimit_le_quadInfo {B : ℕ} (T : BoundedTree B) (lam : ℝ)
    (hlam : MainLambda lam) (v : List (Fin B)) (n : ℕ) :
    treeExperimentLimit T lam v ≤ quadInfo (treeExperimentLaw T lam n v) :=
  le_of_tendsto (treeExperimentLaw_quadInfo_tendsto T lam hlam v)
    (Filter.eventually_atTop.2 ⟨n, fun _ hm => treeExperimentLaw_quadInfo_antitone T lam hlam v hm⟩)

-- @node: treeExperimentLimit_pos_iff_uniform_pos
/-- For [a tree with bounded branching](hyp:T), [a channel parameter](hyp:lam)
[strictly between zero and one](hyp:hlam), and [a vertex address](hyp:v),
[the limiting tree information is positive if and only if a single positive
constant bounds the quadratic information from below at every observation
depth](goal). -/
lemma treeExperimentLimit_pos_iff_uniform_pos {B : ℕ} (T : BoundedTree B) (lam : ℝ)
    (hlam : MainLambda lam) (v : List (Fin B)) :
    0 < treeExperimentLimit T lam v ↔
      ∃ c : ℝ, 0 < c ∧ ∀ n, c ≤ quadInfo (treeExperimentLaw T lam n v) := by
  constructor
  · intro hpos
    exact ⟨_, hpos, treeExperimentLimit_le_quadInfo T lam hlam v⟩
  · rintro ⟨c, hc, hbound⟩
    exact hc.trans_le (ge_of_tendsto (treeExperimentLaw_quadInfo_tendsto T lam hlam v)
      (Filter.Eventually.of_forall hbound))

-- @node: treeExperimentLimit_flow_labels
/-- Assuming [the companion class of symmetric posterior laws with the prescribed
moment-saving bound exists](hyp:hCompanion), for [a tree with bounded
branching](hyp:T) and [a channel parameter](hyp:lam) [strictly between zero and
one](hyp:hlam), [transforming each limiting information value x into
(1 − λ⁴)(x + x³/3000)/1000 gives nonnegative vertex labels, each bounded above
by the sum over its children of λ² times the child's label divided by the square
root of one plus that label squared](goal). -/
lemma treeExperimentLimit_flow_labels (hCompanion : CompanionMomentSaving)
    {B : ℕ} (T : BoundedTree B) (lam : ℝ) (hlam : MainLambda lam) :
    FlowLabelRecursion T lam (fun v => cubicInfoScale (sqParam lam) *
      cubicInfoTransform (treeExperimentLimit T lam v)) := by
  obtain ⟨C, hC, hrevealing, hzero, hchannel, hstar, hsave⟩ :=
    companion_class_cubic_saving hCompanion
  exact flow_labels_of_companion_experiment_limits C (fun mu hmu => (hC mu hmu).1)
    hzero hchannel hstar (fun mu hmu nu hnu => (hsave mu hmu nu hnu).2)
    T lam hlam (treeExperimentLaw T lam)
    (fun n v _ => treeExperimentLaw_mem C hrevealing hzero hchannel hstar T lam hlam n v)
    (fun _ _ _ => rfl) (treeExperimentLimit T lam)
    (fun v _ => treeExperimentLaw_quadInfo_tendsto T lam hlam v)

-- @node: capacity_pos_of_treeExperimentLimit_pos
/-- Assuming [the companion class of symmetric posterior laws with the prescribed
moment-saving bound exists](hyp:hCompanion), for [a tree with bounded
branching](hyp:T) and [a channel parameter](hyp:lam), if [the branching bound is
positive and the tree is infinite](hyp:hT), [the channel parameter is strictly
between zero and one](hyp:hlam), and [the limiting tree information at the root
is positive](hyp:hroot), then [the tree's order-three capacity is positive](goal). -/
theorem capacity_pos_of_treeExperimentLimit_pos (hCompanion : CompanionMomentSaving)
    {B : ℕ} (T : BoundedTree B) (lam : ℝ) (hT : MainTree T) (hlam : MainLambda lam)
    (hroot : 0 < treeExperimentLimit T lam []) : 0 < capacity3 T lam :=
  capacity_pos_of_treeExperimentLaw_limits hCompanion T lam hT hlam
    (treeExperimentLimit T lam)
    (fun v _ => treeExperimentLaw_quadInfo_tendsto T lam hlam v) hroot

-- @node: capacity_pos_of_treeExperimentLaw_uniform_pos
/-- Assuming [the companion class of symmetric posterior laws with the prescribed
moment-saving bound exists](hyp:hCompanion), for [a tree with bounded
branching](hyp:T) and [a channel parameter](hyp:lam), if [the branching bound is
positive and the tree is infinite](hyp:hT), [the channel parameter is strictly
between zero and one](hyp:hlam), and [a single positive constant bounds the root's
quadratic information from below at every observation depth](hyp:hroot), then
[the tree's order-three capacity is positive](goal). -/
theorem capacity_pos_of_treeExperimentLaw_uniform_pos (hCompanion : CompanionMomentSaving)
    {B : ℕ} (T : BoundedTree B) (lam : ℝ) (hT : MainTree T) (hlam : MainLambda lam)
    (hroot : ∃ c : ℝ, 0 < c ∧ ∀ n, c ≤ quadInfo (treeExperimentLaw T lam n [])) :
    0 < capacity3 T lam :=
  capacity_pos_of_treeExperimentLimit_pos hCompanion T lam hT hlam
    ((treeExperimentLimit_pos_iff_uniform_pos T lam hlam []).mpr hroot)

end OaiCapacityCriterionState
