module
public import Papers.TbsNeuralCausalPi.Helpers.GumbelMaxClosedSimplex
/-! # Robust categorical choices for the current-representation sampling bound

Lower the proposed winner's weight and raise every competitor's weight by the
rounding tolerance. Strict victory in this modified race certifies the same
label for every coordinatewise perturbation in the closed simplex.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
open scoped ENNReal

-- @node: robustRaceWeights
/-- Given [category weights q](hyp:q), [a perturbation tolerance a](hyp:a),
[a proposed winning label i](hyp:i), and [a label j whose weight is evaluated](hyp:j),
the [modified race weight](goal) is [the winner's weight minus a when j is
i](step:1), and [the competitor's weight plus a otherwise](step:2). -/
def robustRaceWeights {n : ℕ} (q : Fin n → ℝ) (a : ℝ) (i j : Fin n) : ℝ :=
  if j = i then q i - a else q j + a

-- @node: RobustCategoricalWinner
/-- For [category weights q](hyp:q), [tolerance a](hyp:a), [noise scores G](hyp:G),
and [a proposed winning label i](hyp:i), [robust categorical victory](goal)
means [i's weight exceeds a](step:1) and [every other label whose weight plus
a is positive has a strictly smaller log-weight-plus-noise score after its
weight is raised by a and i's weight is lowered by a](step:2). -/
def RobustCategoricalWinner {n : ℕ} (q : Fin n → ℝ) (a : ℝ)
    (G : Fin n → ℝ) (i : Fin n) : Prop :=
  a < q i ∧ ∀ j, j ≠ i → 0 < q j + a →
    Real.log (q j + a) + G j < Real.log (q i - a) + G i

/-- If [the tolerance is nonnegative](hyp:_ha), [the perturbed weights are
nonnegative](hyp:hp), [they sum to one](hyp:hsum), [each differs from its
reference weight by at most the tolerance](hyp:hnear), and [i is a robust
winner for the reference weights and the given noise](hyp:hi), then [the
smallest-maximizer rule applied to perturbed log weights plus noise selects i,
treating a zero weight as a score of minus infinity](goal). -/
-- @node: robustCategoricalWinner_selects
lemma robustCategoricalWinner_selects {n : ℕ} (q p : Fin n → ℝ) (a : ℝ)
    (_ha : 0 ≤ a) (hp : ∀ j, 0 ≤ p j) (hsum : ∑ j, p j = 1)
    (hnear : ∀ j, |p j - q j| ≤ a) (G : Fin n → ℝ) (i : Fin n)
    (hi : RobustCategoricalWinner q a G i) :
    firstArgmax (fun j => extendedLog (p j) + (G j : EReal)) = some i := by
  have hpi : 0 < p i := by
    have := (abs_le.mp (hnear i)).1
    linarith [hi.1]
  obtain ⟨j, hj⟩ := firstArgmax_exists (Nat.zero_lt_of_lt i.isLt)
    (fun j => extendedLog (p j) + (G j : EReal))
  obtain ⟨hpj, hmax⟩ := firstArgmax_positive_and_maximizes p hp
    (by rw [hsum]; norm_num) G j hj
  have hji : j = i := by
    by_contra hne
    have hqj : p j ≤ q j + a := by linarith [(abs_le.mp (hnear j)).2]
    have hqi : q i - a ≤ p i := by linarith [(abs_le.mp (hnear i)).1]
    have hlogj := Real.log_le_log hpj hqj
    have hlogi := Real.log_le_log (by linarith [hi.1] : 0 < q i - a) hqi
    have hstrict := hi.2 j hne (lt_of_lt_of_le hpj hqj)
    have := hmax i hpi
    linarith
  simpa only [hji] using hj

-- @node: robustCategoricalWinner_disjoint
/-- If [the reference weights are nonnegative](hyp:hq), [sum to one](hyp:hsum),
and [the tolerance is nonnegative](hyp:ha), then [two distinct labels](hyp:hij)
have [disjoint events of robust victory](goal). -/
lemma robustCategoricalWinner_disjoint {n : ℕ} (q : Fin n → ℝ) (a : ℝ)
    (hq : ∀ j, 0 ≤ q j) (hsum : ∑ j, q j = 1) (ha : 0 ≤ a)
    {i j : Fin n} (hij : i ≠ j) :
    Disjoint {G | RobustCategoricalWinner q a G i}
      {G | RobustCategoricalWinner q a G j} := by
  apply Set.disjoint_left.mpr
  intro G hi hj
  have hnear (k : Fin n) : |q k - q k| ≤ a := by simpa using ha
  have h1 := robustCategoricalWinner_selects q q a ha hq hsum hnear G i hi
  have h2 := robustCategoricalWinner_selects q q a ha hq hsum hnear G j hj
  exact hij (Option.some.inj (h1.symm.trans h2))

/-- If [the reference weights are nonnegative](hyp:hq), [sum to one](hyp:hsum),
[the tolerance a is nonnegative](hyp:ha), and [the proposed winner's weight
exceeds a](hyp:hi), then [all modified race weights are nonnegative, their
sum is positive, and their sum is at most one plus the number of labels times a](goal). -/
-- @node: robustRaceWeights_sum_bounds
lemma robustRaceWeights_sum_bounds {n : ℕ} (q : Fin n → ℝ) (a : ℝ)
    (hq : ∀ j, 0 ≤ q j) (hsum : ∑ j, q j = 1) (ha : 0 ≤ a)
    (i : Fin n) (hi : a < q i) :
    (∀ j, 0 ≤ robustRaceWeights q a i j) ∧
      0 < ∑ j, robustRaceWeights q a i j ∧
      (∑ j, robustRaceWeights q a i j) ≤ 1 + n * a := by
  have hnonneg (j) : 0 ≤ robustRaceWeights q a i j := by
    unfold robustRaceWeights
    split_ifs <;> linarith [hq j]
  refine ⟨hnonneg, ?_, ?_⟩
  · exact Finset.sum_pos' (fun j _ => hnonneg j)
      ⟨i, Finset.mem_univ _, by simpa [robustRaceWeights] using sub_pos.mpr hi⟩
  · calc
      (∑ j, robustRaceWeights q a i j) ≤ ∑ j, (q j + a) := by
        apply Finset.sum_le_sum
        intro j _
        unfold robustRaceWeights
        split_ifs with hji
        · subst j; linarith
        · exact le_rfl
      _ = 1 + n * a := by simp [Finset.sum_add_distrib, hsum]

/-- If [the reference weights sum to one](hyp:hsum), then [the sum of their
positive parts after subtracting a from each is at least one minus the number
of labels times a](goal). -/
-- @node: sum_positive_lower_weights
lemma sum_positive_lower_weights {n : ℕ} (q : Fin n → ℝ) (a : ℝ)
    (hsum : ∑ j, q j = 1) :
    1 - n * a ≤ ∑ j, max (q j - a) 0 := by
  calc
    1 - n * a = ∑ j, (q j - a) := by simp [Finset.sum_sub_distrib, hsum]
    _ ≤ _ := Finset.sum_le_sum (fun j _ => le_max_left _ _)

/-- If [all race weights are nonnegative](hyp:hw) and [label i has positive
weight](hyp:hi), then [under independent standard Gumbel noise the probability
that i's log-weight-plus-noise score strictly exceeds every other positive-weight
label's score equals i's weight divided by the total weight](goal). -/
-- @node: gumbel_strict_maximum_probability
lemma gumbel_strict_maximum_probability {n : ℕ} (w : Fin n → ℝ)
    (hw : ∀ j, 0 ≤ w j) (i : Fin n) (hi : 0 < w i) :
    gumbelInputs n {G | ∀ j, j ≠ i → 0 < w j →
      Real.log (w j) + G j < Real.log (w i) + G i} =
      ENNReal.ofReal (w i / ∑ j, w j) := by
  have hS : 0 < ∑ j, w j :=
    Finset.sum_pos' (fun j _ => hw j) ⟨i, Finset.mem_univ _, hi⟩
  let p : Fin n → ℝ := fun j => w j / ∑ k, w k
  have hp : ∀ j, 0 ≤ p j := fun j => div_nonneg (hw j) hS.le
  have hsum : ∑ j, p j = 1 := by
    dsimp [p]
    rw [← Finset.sum_div, div_self hS.ne']
  have hpi : 0 < p i := div_pos hi hS
  have heq : {G : Fin n → ℝ | ∀ j, j ≠ i → 0 < w j →
      Real.log (w j) + G j < Real.log (w i) + G i} =ᵐ[gumbelInputs n]
      {G | ∀ j, 0 < p j → Real.log (p j) + G j ≤ Real.log (p i) + G i} := by
    filter_upwards [gumbel_scores_ne_ae w] with G hG
    apply propext
    change (∀ j, j ≠ i → 0 < w j → _) ↔ (∀ j, 0 < p j → _)
    constructor
    · intro h j hj
      have hwj : 0 < w j := (div_pos_iff_of_pos_right hS).mp hj
      rw [show Real.log (p j) = Real.log (w j) - Real.log (∑ k, w k) from
        Real.log_div hwj.ne' hS.ne', show Real.log (p i) = _ from Real.log_div hi.ne' hS.ne']
      by_cases hji : j = i
      · subst j; exact le_rfl
      · linarith [h j hji hwj]
    · intro h j hji hwj
      have hj := h j (div_pos hwj hS)
      change Real.log (w j / ∑ k, w k) + G j ≤ Real.log (w i / ∑ k, w k) + G i at hj
      rw [Real.log_div hwj.ne' hS.ne', Real.log_div hi.ne' hS.ne'] at hj
      exact lt_of_le_of_ne (by linarith) (hG j i hji)
  rw [measure_congr heq]
  cases n with
  | zero => exact Fin.elim0 i
  | succ n => exact gumbel_maximum_probability_nonneg p hp hsum i hpi

/-- If [the reference weights are nonnegative](hyp:hq), [sum to one](hyp:hsum),
[the tolerance a is nonnegative](hyp:ha), and [i's weight exceeds a](hyp:hi),
then [under independent standard Gumbel noise the probability that i is a robust
winner equals its weight minus a divided by the total modified race weight](goal). -/
-- @node: robustCategoricalWinner_probability
lemma robustCategoricalWinner_probability {n : ℕ} (q : Fin n → ℝ) (a : ℝ)
    (hq : ∀ j, 0 ≤ q j) (hsum : ∑ j, q j = 1) (ha : 0 ≤ a)
    (i : Fin n) (hi : a < q i) :
    gumbelInputs n {G | RobustCategoricalWinner q a G i} =
      ENNReal.ofReal ((q i - a) / ∑ j, robustRaceWeights q a i j) := by
  obtain ⟨hw, hS, _⟩ := robustRaceWeights_sum_bounds q a hq hsum ha i hi
  have heq : {G | RobustCategoricalWinner q a G i} =
      {G | ∀ j, j ≠ i → 0 < robustRaceWeights q a i j →
        Real.log (robustRaceWeights q a i j) + G j <
          Real.log (robustRaceWeights q a i i) + G i} := by
    ext G
    simp only [RobustCategoricalWinner, hi, true_and]
    apply forall_congr'
    intro j
    by_cases hji : j = i <;> simp [robustRaceWeights, hji]
  rw [heq, gumbel_strict_maximum_probability _ hw i
    (by simpa [robustRaceWeights] using sub_pos.mpr hi)]
  simp only [robustRaceWeights, ite_true]

-- @node: measurableSet_robustCategoricalWinner
/-- [The set of noise vectors for which label i is a robust winner at the
given weights and tolerance is measurable](goal). -/
lemma measurableSet_robustCategoricalWinner {n : ℕ}
    (q : Fin n → ℝ) (a : ℝ) (i : Fin n) :
    MeasurableSet {G | RobustCategoricalWinner q a G i} := by
  classical
  by_cases hi : a < q i
  · simp only [RobustCategoricalWinner, hi, true_and, Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun _ => measurableSet_lt (by fun_prop) (by fun_prop)
  · simp [RobustCategoricalWinner, hi]

/-- If [the reference weights are nonnegative](hyp:hq), [sum to one](hyp:hsum),
and [the tolerance a is nonnegative](hyp:ha), then [the probability of robust
victory for i under independent standard Gumbel noise is at least the positive
part of its weight minus a, divided by one plus the number of labels times a](goal). -/
-- @node: robustCategoricalWinner_probability_lower
lemma robustCategoricalWinner_probability_lower {n : ℕ} (q : Fin n → ℝ) (a : ℝ)
    (hq : ∀ j, 0 ≤ q j) (hsum : ∑ j, q j = 1) (ha : 0 ≤ a) (i : Fin n) :
    ENNReal.ofReal (max (q i - a) 0 / (1 + n * a)) ≤
      gumbelInputs n {G | RobustCategoricalWinner q a G i} := by
  by_cases hi : a < q i
  · rw [robustCategoricalWinner_probability q a hq hsum ha i hi,
      max_eq_left (sub_pos.mpr hi).le]
    apply ENNReal.ofReal_le_ofReal
    obtain ⟨_, hS, hbound⟩ := robustRaceWeights_sum_bounds q a hq hsum ha i hi
    exact div_le_div_of_nonneg_left (sub_pos.mpr hi).le hS hbound
  · rw [max_eq_right (by linarith : q i - a ≤ 0), zero_div, ENNReal.ofReal_zero]
    exact bot_le

/-- If [the reference weights are nonnegative](hyp:hq), [sum to one](hyp:hsum),
and [the tolerance a is nonnegative](hyp:ha), then [under independent standard
Gumbel noise the probability that no label is a robust winner is at most
twice the number of labels times a](goal). -/
-- @node: gumbel_no_robust_label_probability_le
lemma gumbel_no_robust_label_probability_le {n : ℕ} (q : Fin n → ℝ) (a : ℝ)
    (hq : ∀ j, 0 ≤ q j) (hsum : ∑ j, q j = 1) (ha : 0 ≤ a) :
    gumbelInputs n {G | ¬ ∃ i, RobustCategoricalWinner q a G i} ≤
      ENNReal.ofReal (2 * n * a) := by
  let := gumbelInputs_probability n
  let S : Fin n → Set (Fin n → ℝ) := fun i => {G | RobustCategoricalWinner q a G i}
  have hmeas (i) : MeasurableSet (S i) := measurableSet_robustCategoricalWinner q a i
  have hdis : Pairwise (fun i j => Disjoint (S i) (S j)) := fun i j hij =>
    robustCategoricalWinner_disjoint q a hq hsum ha hij
  have hden : 0 < 1 + (n : ℝ) * a := by positivity
  have hcoord (i : Fin n) : max (q i - a) 0 / (1 + n * a) ≤
      (gumbelInputs n).real (S i) := by
    have h := ENNReal.toReal_mono (measure_ne_top _ _)
      (robustCategoricalWinner_probability_lower q a hq hsum ha i)
    simpa only [measureReal_def, S,
      ENNReal.toReal_ofReal (div_nonneg (le_max_right _ _) hden.le)] using h
  have hunion : (1 - (n : ℝ) * a) / (1 + n * a) ≤
      (gumbelInputs n).real (⋃ i, S i) := by
    calc
      _ ≤ (∑ i, max (q i - a) 0) / (1 + n * a) :=
        div_le_div_of_nonneg_right (sum_positive_lower_weights q a hsum) hden.le
      _ = ∑ i, max (q i - a) 0 / (1 + n * a) := Finset.sum_div _ _ _
      _ ≤ ∑ i, (gumbelInputs n).real (S i) := Finset.sum_le_sum (fun i _ => hcoord i)
      _ = _ := (measureReal_iUnion_fintype hdis hmeas).symm
  have hcompl : (gumbelInputs n).real (⋃ i, S i)ᶜ ≤ 2 * n * a := by
    rw [measureReal_compl (MeasurableSet.iUnion hmeas)]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one]
    have halg : 1 - (1 - (n : ℝ) * a) / (1 + n * a) =
        2 * n * a / (1 + n * a) := by field_simp; ring
    calc
      _ ≤ 1 - (1 - (n : ℝ) * a) / (1 + n * a) := sub_le_sub_left hunion 1
      _ = _ := halg
      _ ≤ 2 * n * a := div_le_self (by positivity) (by nlinarith)
  have heq : {G | ¬ ∃ i, RobustCategoricalWinner q a G i} = (⋃ i, S i)ᶜ := by
    ext G
    simp [S]
  rw [heq, ← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hcompl

/-- If [the tolerance is nonnegative](hyp:ha), [the perturbed weights are
nonnegative](hyp:hp), [sum to one](hyp:hsum), and [differ coordinatewise from
the reference weights by at most the tolerance](hyp:hnear), and [i is a robust
winner for the reference weights and noise](hyp:hi), then, using [the guarantee
that this categorical node has at least one label](hyp:hk), [the canonical
categorical selector for the perturbed weights and the same noise returns i](goal). -/
-- @node: robustCategoricalWinner_canonicalSelector
lemma robustCategoricalWinner_canonicalSelector {n : ℕ} (q p : Fin n → ℝ) (a : ℝ)
    (ha : 0 ≤ a) (hp : ∀ j, 0 ≤ p j) (hsum : ∑ j, p j = 1)
    (hnear : ∀ j, |p j - q j| ≤ a) (G : Fin n → ℝ) (i : Fin n)
    (hi : RobustCategoricalWinner q a G i)
    (hk : ∀ m, Sum.inr n = (Sum.inr m : NodeKind) → 0 < m) :
    canonicalSelector (.inr n) hk (WithLp.toLp 1 p) (WithLp.toLp 1 G) = i := by
  change (firstArgmax (fun j => extendedLog (p j) + (G j : EReal))).getD _ = i
  rw [robustCategoricalWinner_selects q p a ha hp hsum hnear G i hi]
  rfl

/-- If [the reference weights are nonnegative](hyp:hq), [sum to one](hyp:hsum),
[the tolerance a is nonnegative](hyp:ha), and [the categorical node has at least
one label](hyp:hk), then [the outer probability under independent standard
Gumbel noise that some probability vector within a in every coordinate changes
the canonical selection is at most twice the number of labels times a](goal). -/
-- @node: gumbel_uniform_categorical_perturbation_probability_le
lemma gumbel_uniform_categorical_perturbation_probability_le {n : ℕ}
    (q : Fin n → ℝ) (a : ℝ) (hq : ∀ j, 0 ≤ q j) (hsum : ∑ j, q j = 1)
    (ha : 0 ≤ a) (hk : ∀ m, Sum.inr n = (Sum.inr m : NodeKind) → 0 < m) :
    gumbelInputs n {G | ∃ p : Fin n → ℝ,
      (∀ j, 0 ≤ p j) ∧ (∑ j, p j = 1) ∧ (∀ j, |p j - q j| ≤ a) ∧
      canonicalSelector (.inr n) hk (WithLp.toLp 1 p) (WithLp.toLp 1 G) ≠
        canonicalSelector (.inr n) hk (WithLp.toLp 1 q) (WithLp.toLp 1 G)} ≤
      ENNReal.ofReal (2 * n * a) := by
  apply le_trans (measure_mono ?_) (gumbel_no_robust_label_probability_le q a hq hsum ha)
  rintro G ⟨p, hp, hpSum, hnear, hdiff⟩ ⟨i, hi⟩
  exact hdiff ((robustCategoricalWinner_canonicalSelector q p a ha hp hpSum hnear G i hi hk).trans
    (robustCategoricalWinner_canonicalSelector q q a ha hq hsum
      (fun j => by simpa using ha) G i hi hk).symm)

end Papers.TbsNeuralCausalPi
