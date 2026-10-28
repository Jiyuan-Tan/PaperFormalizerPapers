module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.StarsTrialBudget
public import Papers.OaiGraphDecompositionsIntegral.Helpers.BernoulliTests

/-! # Finite fresh-row star trials

The greedy update records the remaining star sizes and unused leaves. A
reciprocal-success potential controls a finite number of trials directly;
no infinite auxiliary host or almost-sure stopping-time argument is needed.
-/

@[expose] public section

open Causalean.Experimentation.DesignBased
open scoped BigOperators

namespace Papers.OaiGraphDecompositionsIntegral

attribute [local instance] Classical.propDecidable

-- @node: StarRowState
/-- For [a type of possible leaves](hyp:X), a [star-trial state](goal) records
the list of remaining leaf demands and the finite set of unused leaves. -/
structure StarRowState (X : Type) where
  todo : List ℕ
  unused : Finset X

-- @node: starRowNeighbors
/-- Given [a star-trial state](hyp:s) and [a row of Boolean edge indicators](hyp:z),
the [row's available neighbors](goal) are the unused leaves whose edge indicator is true. -/
def starRowNeighbors {X : Type} (s : StarRowState X) (z : X → Bool) : Finset X :=
  s.unused.filter (fun x => z x = true)

-- @node: starChooseLeaves
/-- From [a finite candidate set](hyp:S) and [a requested number of leaves](hyp:ell),
the [chosen leaves](goal) are an arbitrary subset of that size if enough candidates
exist, and the empty set otherwise. -/
noncomputable def starChooseLeaves {X : Type} (S : Finset X) (ell : ℕ) : Finset X :=
  if h : ell ≤ S.card then Classical.choose (Finset.exists_subset_card_eq h) else ∅

-- @node: star_choose_leaves_spec
/-- If [the candidate set contains at least the requested number of leaves](hyp:h),
then [the chosen leaves form a subset of the candidates and have exactly the requested size](goal). -/
lemma star_choose_leaves_spec {X : Type} (S : Finset X) (ell : ℕ)
    (h : ell ≤ S.card) :
    starChooseLeaves S ell ⊆ S ∧ (starChooseLeaves S ell).card = ell := by
  simpa only [starChooseLeaves, dif_pos h] using
    Classical.choose_spec (Finset.exists_subset_card_eq h)

-- @node: starRowUpdate
/-- Given [a star-trial state](hyp:s) and [a row of edge indicators](hyp:z),
the [updated state](goal) [stays unchanged when there are no remaining demands](step:1);
[otherwise it removes the first demand and its chosen neighboring leaves if enough
neighbors are available, and stays unchanged if they are not](step:2). -/
noncomputable def starRowUpdate {X : Type} [DecidableEq X]
    (s : StarRowState X) (z : X → Bool) : StarRowState X :=
  match s.todo with
  | [] => s
  | ell :: rest =>
      if ell ≤ (starRowNeighbors s z).card then
        ⟨rest, s.unused \ starChooseLeaves (starRowNeighbors s z) ell⟩
      else s

-- @node: star_row_update_unused_subset
/-- [Every leaf unused after a row update was also unused before that update](goal). -/
lemma star_row_update_unused_subset {X : Type} [DecidableEq X]
    (s : StarRowState X) (z : X → Bool) :
    (starRowUpdate s z).unused ⊆ s.unused := by
  cases h : s.todo with
  | nil => simp [starRowUpdate, h]
  | cons ell rest =>
      by_cases hs : ell ≤ (starRowNeighbors s z).card
      · simpa only [starRowUpdate, h, if_pos hs] using
          (Finset.sdiff_subset : s.unused \ starChooseLeaves (starRowNeighbors s z) ell ⊆ _)
      · simp [starRowUpdate, h, hs]

-- @node: star_row_update_finished
/-- If [no leaf demands remain](hyp:h), then [a row update leaves the state unchanged](goal). -/
lemma star_row_update_finished {X : Type} [DecidableEq X]
    (s : StarRowState X) (z : X → Bool) (h : s.todo = []) :
    starRowUpdate s z = s := by simp [starRowUpdate, h]

-- @node: star_row_leaf_conservation
/-- [The number of unused leaves after an update plus the previous total demand
equals the previous number of unused leaves plus the remaining total demand](goal). -/
lemma star_row_leaf_conservation {X : Type} [DecidableEq X]
    (s : StarRowState X) (z : X → Bool) :
    (starRowUpdate s z).unused.card + s.todo.sum =
      s.unused.card + (starRowUpdate s z).todo.sum := by
  cases h : s.todo with
  | nil => simp [starRowUpdate, h]
  | cons ell rest =>
      by_cases hs : ell ≤ (starRowNeighbors s z).card
      · have hc := star_choose_leaves_spec (starRowNeighbors s z) ell hs
        have hsub : starChooseLeaves (starRowNeighbors s z) ell ⊆ s.unused :=
          hc.1.trans (Finset.filter_subset _ _)
        have hle := Finset.card_le_card hsub
        rw [hc.2] at hle
        simp only [starRowUpdate, h, if_pos hs, List.sum_cons,
          Finset.card_sdiff_of_subset hsub, hc.2]
        omega
      · simp [starRowUpdate, h, hs]

-- @node: starTodoBudget
/-- Given [a real-valued success function on leaf counts](hyp:u) and
[a list of remaining leaf demands](hyp:L), the [remaining budget](goal) is the sum
of the reciprocals of their success values. -/
noncomputable def starTodoBudget (u : ℕ → ℝ) (L : List ℕ) : ℝ :=
  (L.map (fun ell => (u ell)⁻¹)).sum

-- @node: star_todo_budget_nonneg
/-- If [every success value is nonnegative](hyp:hu), then
[the reciprocal-success budget of any list of demands is nonnegative](goal). -/
lemma star_todo_budget_nonneg (u : ℕ → ℝ) (L : List ℕ)
    (hu : ∀ ell, 0 ≤ u ell) : 0 ≤ starTodoBudget u L := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨ell, _, rfl⟩ := List.mem_map.mp hx
  exact inv_nonneg.mpr (hu ell)

-- @node: star_row_budget_gain
/-- If [the remaining demands start with the specified leaf count followed by the
specified remainder](hyp:h), then [the budget decrease from a row update equals
the reciprocal success value of that first demand times the indicator that the
row has enough available neighbors](goal). -/
lemma star_row_budget_gain {X : Type} [DecidableEq X]
    (u : ℕ → ℝ) (s : StarRowState X) (ell : ℕ) (rest : List ℕ)
    (h : s.todo = ell :: rest) (z : X → Bool) :
    starTodoBudget u s.todo - starTodoBudget u (starRowUpdate s z).todo =
      (u ell)⁻¹ * FiniteDesign.ind (fun z => ell ≤ (starRowNeighbors s z).card) z := by
  by_cases hs : ell ≤ (starRowNeighbors s z).card <;>
    simp [starRowUpdate, h, hs, starTodoBudget, FiniteDesign.ind]

-- @node: star_row_expected_budget_drop
/-- If [the demand list begins with the specified leaf count and remainder](hyp:h),
[that leaf count has a positive success value](hyp:hu), and [this value is at most
the probability that the row has enough available neighbors](hyp:hsuccess), then
[the expected budget after the update plus one is at most the current budget](goal). -/
lemma star_row_expected_budget_drop {X : Type} [Fintype X] [DecidableEq X]
    (D : FiniteDesign (X → Bool)) (u : ℕ → ℝ)
    (s : StarRowState X) (ell : ℕ) (rest : List ℕ)
    (h : s.todo = ell :: rest) (hu : 0 < u ell)
    (hsuccess : u ell ≤ D.Pr (fun z => ell ≤ (starRowNeighbors s z).card)) :
    D.E (fun z => starTodoBudget u (starRowUpdate s z).todo) + 1 ≤
      starTodoBudget u s.todo := by
  have heq := D.E_congr (star_row_budget_gain u s ell rest h)
  rw [D.E_sub, D.E_const, D.E_const_mul] at heq
  have hg : (1 : ℝ) ≤ (u ell)⁻¹ *
      D.Pr (fun z => ell ≤ (starRowNeighbors s z).card) := by
    calc
      1 = (u ell)⁻¹ * u ell := (inv_mul_cancel₀ hu.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hsuccess (inv_nonneg.mpr hu.le)
  change starTodoBudget u s.todo -
    D.E (fun z => starTodoBudget u (starRowUpdate s z).todo) =
      (u ell)⁻¹ * D.Pr (fun z => ell ≤ (starRowNeighbors s z).card) at heq
  linarith

-- @node: star_row_success_ge_binomial
/-- If [the unused set contains at least the designated number of available leaves](hyp:hleaves),
then [the binomial trial success probability is at most the probability that an
independent Bernoulli row has enough unused neighbors for the requested star](goal). -/
lemma star_row_success_ge_binomial {X : Type} [Fintype X] [DecidableEq X]
    (n ell : ℕ) (p : ℝ) (s : StarRowState X)
    (hleaves : availableLeaves n ≤ s.unused.card) :
    starTrialSuccess n p ell ≤
      (productMeasure X p).Pr (fun z => ell ≤ (starRowNeighbors s z).card) := by
  classical
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin (availableLeaves n)) ≤ Fintype.card ↥s.unused by
      simpa using hleaves)
  let f : Fin (availableLeaves n) → X := fun i => (e i).val
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hmarg := productMeasure_E_comp_injective p f hf
    (FiniteDesign.ind (fun z => ell ≤ (toFinset' z).card))
  calc
    starTrialSuccess n p ell = (productMeasure X p).Pr
        (fun z => ell ≤ (toFinset' (fun i => z (f i))).card) := hmarg.symm
    _ ≤ _ := by
      apply FiniteDesign.Pr_mono
      intro z hz
      let T := toFinset' (fun i => z (f i))
      have hsub : T.image f ⊆ starRowNeighbors s z := by
        intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_filter.mpr ⟨(e i).property,
          (Finset.mem_filter.mp hi).2⟩
      have hc := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ hf] at hc
      exact hz.trans hc

-- @node: star_row_binomial_budget_drop
/-- If [the demand list begins with the specified leaf count and remainder](hyp:h),
[enough unused leaves remain to cover the designated available-leaf count](hyp:hleaves),
and [the binomial success probability for the first demand is positive](hyp:hu),
then [the expected reciprocal-binomial-success budget after one Bernoulli row
plus one is at most the current budget](goal). -/
lemma star_row_binomial_budget_drop {X : Type} [Fintype X] [DecidableEq X]
    (n : ℕ) (p : ℝ) (s : StarRowState X) (ell : ℕ) (rest : List ℕ)
    (h : s.todo = ell :: rest) (hleaves : availableLeaves n ≤ s.unused.card)
    (hu : 0 < starTrialSuccess n p ell) :
    (productMeasure X p).E (fun z =>
      starTodoBudget (starTrialSuccess n p) (starRowUpdate s z).todo) + 1 ≤
      starTodoBudget (starTrialSuccess n p) s.todo :=
  star_row_expected_budget_drop _ _ s ell rest h hu
    (star_row_success_ge_binomial n ell p s hleaves)

-- @node: starRowStateAfter
/-- From [an initial star-trial state](hyp:s) and [a sequence of edge-indicator rows](hyp:rows),
the [state after a given number of trials](goal) [is the initial state at zero trials](step:1)
and [is obtained at each subsequent trial by updating the preceding state with the next row](step:2). -/
noncomputable def starRowStateAfter {X : Type} [DecidableEq X]
    (s : StarRowState X) (rows : ℕ → X → Bool) : ℕ → StarRowState X
  | 0 => s
  | t + 1 => starRowUpdate (starRowStateAfter s rows t) (rows t)

-- @node: star_row_state_depends_on_past
/-- If [two row sequences agree at every trial before the specified time](hyp:h),
then [they produce the same state at that time from the same initial state](goal). -/
lemma star_row_state_depends_on_past {X : Type} [DecidableEq X]
    (s : StarRowState X) (rows rows' : ℕ → X → Bool) (t : ℕ)
    (h : ∀ j < t, rows j = rows' j) :
    starRowStateAfter s rows t = starRowStateAfter s rows' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [starRowStateAfter, ih (fun j hj => h j (by omega)), h t (by omega)]

-- @node: star_row_state_leaf_conservation
/-- [After any number of trials, the unused-leaf count plus the initial total
demand equals the initial unused-leaf count plus the remaining total demand](goal). -/
lemma star_row_state_leaf_conservation {X : Type} [DecidableEq X]
    (s : StarRowState X) (rows : ℕ → X → Bool) (t : ℕ) :
    (starRowStateAfter s rows t).unused.card + s.todo.sum =
      s.unused.card + (starRowStateAfter s rows t).todo.sum := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have hs := star_row_leaf_conservation (starRowStateAfter s rows t) (rows t)
      simp only [starRowStateAfter]
      omega

-- @node: star_row_state_leaf_reserve
/-- If [the initial unused-leaf count covers the total initial demand plus a
reserve of the specified size](hyp:h), then [at least that many leaves remain
unused after any number of trials](goal). -/
lemma star_row_state_leaf_reserve {X : Type} [DecidableEq X]
    (s : StarRowState X) (rows : ℕ → X → Bool) (t b : ℕ)
    (h : b + s.todo.sum ≤ s.unused.card) :
    b ≤ (starRowStateAfter s rows t).unused.card := by
  have hs := star_row_state_leaf_conservation s rows t
  omega

-- @node: star_row_state_finished_stays_finished
/-- If [all demands are completed at the specified trial](hyp:h), then
[all demands remain completed after any additional number of trials](goal). -/
lemma star_row_state_finished_stays_finished {X : Type} [DecidableEq X]
    (s : StarRowState X) (rows : ℕ → X → Bool) (t k : ℕ)
    (h : (starRowStateAfter s rows t).todo = []) :
    (starRowStateAfter s rows (t + k)).todo = [] := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
      rw [Nat.add_succ, starRowStateAfter,
        star_row_update_finished _ _ ih]
      exact ih

-- @node: star_expectation_by_choice
/-- [The expected value of a statistic selected by a finite-valued choice equals
the sum, over all choices, of the expectation of that statistic restricted to
the event that it is chosen](goal). -/
lemma star_expectation_by_choice {Ω I : Type} [Fintype Ω] [Fintype I]
    (D : FiniteDesign Ω) (choose : Ω → I) (F : I → Ω → ℝ) :
    D.E (fun z => F (choose z) z) =
      ∑ i, D.E (fun z => if choose z = i then F i z else 0) := by
  rw [← D.E_sum]
  apply D.E_congr
  intro z
  simp

-- @node: star_adaptive_row_budget_drop
/-- Suppose [each fixed state has expected budget decrease at least one when
unfinished and at least zero when finished under the reference row distribution](hyp:hfixed),
and [for each choice of state, its probability times its reference expected decrease
equals the actual expected decrease restricted to that choice](hyp:hfresh).
Then [the expected updated budget plus the probability of an unfinished chosen
state is at most the expected budget before the update](goal). -/
lemma star_adaptive_row_budget_drop {Ω I X : Type}
    [Fintype Ω] [Fintype I] [Fintype X] [DecidableEq X]
    (D : FiniteDesign Ω) (R : FiniteDesign (X → Bool))
    (choose : Ω → I) (state : I → StarRowState X) (row : Ω → X → Bool)
    (u : ℕ → ℝ)
    (hfixed : ∀ i, R.E (fun z => starTodoBudget u (state i).todo -
      starTodoBudget u (starRowUpdate (state i) z).todo) ≥
        if (state i).todo = [] then 0 else 1)
    (hfresh : ∀ i,
      D.E (fun z => if choose z = i then
        starTodoBudget u (state i).todo -
          starTodoBudget u (starRowUpdate (state i) (row z)).todo else 0) =
      D.Pr (fun z => choose z = i) * R.E (fun z =>
        starTodoBudget u (state i).todo -
          starTodoBudget u (starRowUpdate (state i) z).todo)) :
    D.E (fun z => starTodoBudget u (starRowUpdate (state (choose z)) (row z)).todo) +
      D.Pr (fun z => (state (choose z)).todo ≠ []) ≤
        D.E (fun z => starTodoBudget u (state (choose z)).todo) := by
  have hsplit := star_expectation_by_choice D choose
    (fun i z => starTodoBudget u (state i).todo -
      starTodoBudget u (starRowUpdate (state i) (row z)).todo)
  rw [D.E_sub] at hsplit
  simp_rw [hfresh] at hsplit
  have hactive : D.Pr (fun z => (state (choose z)).todo ≠ []) =
      ∑ i, D.Pr (fun z => choose z = i) *
        (if (state i).todo = [] then (0 : ℝ) else 1) := by
    have heq := star_expectation_by_choice D choose
      (fun i _ => if (state i).todo = [] then (0 : ℝ) else 1)
    have hleft : D.E (fun z => if (state (choose z)).todo = [] then (0 : ℝ) else 1) =
        D.Pr (fun z => (state (choose z)).todo ≠ []) := by
      apply D.E_congr
      intro z
      by_cases h : (state (choose z)).todo = [] <;> simp [FiniteDesign.ind, h]
    rw [hleft] at heq
    rw [heq]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : (state i).todo = []
    · simp [h, D.E_const]
    · simp only [h, if_false, mul_one]
      rfl
  have hle : (∑ i, D.Pr (fun z => choose z = i) *
      (if (state i).todo = [] then (0 : ℝ) else 1)) ≤
      ∑ i, D.Pr (fun z => choose z = i) * R.E (fun z =>
        starTodoBudget u (state i).todo -
          starTodoBudget u (starRowUpdate (state i) z).todo) := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hfixed i) (D.Pr_nonneg _)
  rw [← hactive] at hle
  linarith

-- @node: star_finite_trial_drift
/-- If [the initial potential equals the budget for every outcome](hyp:hzero)
and [at each trial before the horizon, the next expected potential plus the
probability of activity is at most the current expected potential](hyp:hstep),
then [the expected terminal potential plus the sum of the activity probabilities
before the horizon is at most the initial budget](goal). -/
lemma star_finite_trial_drift {Ω : Type} [Fintype Ω]
    (D : FiniteDesign Ω) (P : ℕ → Ω → ℝ) (A : ℕ → Ω → Prop)
    (K : ℕ) (budget : ℝ) (hzero : ∀ z, P 0 z = budget)
    (hstep : ∀ t < K, D.E (P (t + 1)) + D.Pr (A t) ≤ D.E (P t)) :
    D.E (P K) + (∑ t ∈ Finset.range K, D.Pr (A t)) ≤ budget := by
  have hz : D.E (P 0) = budget := by
    rw [D.E_congr hzero, D.E_const]
  have hind : ∀ k ≤ K,
      D.E (P k) + (∑ t ∈ Finset.range k, D.Pr (A t)) ≤ budget := by
    intro k
    induction k with
    | zero => intro _; simp [hz]
    | succ k ih =>
        intro hk
        have hp := ih (by omega)
        have hs := hstep k (by omega)
        rw [Finset.sum_range_succ]
        linarith
  exact hind K le_rfl

-- @node: star_finite_trial_failure_bound
/-- If [the initial potential always equals the budget](hyp:hzero),
[each step's expected potential decrease covers its activity probability](hyp:hstep),
[the terminal potential is nonnegative for every outcome](hyp:hP), and
[activity at the horizon implies activity at every earlier trial](hyp:hactive),
then [the horizon times the probability of terminal activity is at most the budget](goal). -/
lemma star_finite_trial_failure_bound {Ω : Type} [Fintype Ω]
    (D : FiniteDesign Ω) (P : ℕ → Ω → ℝ) (A : ℕ → Ω → Prop)
    (K : ℕ) (budget : ℝ) (hzero : ∀ z, P 0 z = budget)
    (hstep : ∀ t < K, D.E (P (t + 1)) + D.Pr (A t) ≤ D.E (P t))
    (hP : ∀ z, 0 ≤ P K z)
    (hactive : ∀ t < K, ∀ z, A K z → A t z) :
    (K : ℝ) * D.Pr (A K) ≤ budget := by
  have ht := star_finite_trial_drift D P A K budget hzero hstep
  have hnonneg := D.E_nonneg hP
  have hsum : (K : ℝ) * D.Pr (A K) ≤ ∑ t ∈ Finset.range K, D.Pr (A t) := by
    calc
      _ = ∑ _t ∈ Finset.range K, D.Pr (A K) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun t ht =>
        D.Pr_mono _ _ (hactive t (Finset.mem_range.mp ht)))
  linarith

-- @node: star_finite_trial_finish_probability
/-- Suppose [the trial horizon is positive](hyp:hK), [the initial potential always
equals the budget](hyp:hzero), [each step's expected potential decrease covers its
activity probability](hyp:hstep), [the terminal potential is nonnegative](hyp:hP),
[terminal activity implies activity at every earlier trial](hyp:hactive), and
[the budget is at most half the horizon](hyp:hbudget). Then [the probability of
being inactive at the horizon is at least one half](goal). -/
lemma star_finite_trial_finish_probability {Ω : Type} [Fintype Ω]
    (D : FiniteDesign Ω) (P : ℕ → Ω → ℝ) (A : ℕ → Ω → Prop)
    (K : ℕ) (hK : 0 < K) (budget : ℝ)
    (hzero : ∀ z, P 0 z = budget)
    (hstep : ∀ t < K, D.E (P (t + 1)) + D.Pr (A t) ≤ D.E (P t))
    (hP : ∀ z, 0 ≤ P K z)
    (hactive : ∀ t < K, ∀ z, A K z → A t z)
    (hbudget : budget ≤ (K : ℝ) / 2) :
    (1 / 2 : ℝ) ≤ D.Pr (fun z => ¬ A K z) := by
  have hb := star_finite_trial_failure_bound D P A K budget hzero hstep hP hactive
  have hsplit : D.Pr (A K) + D.Pr (fun z => ¬ A K z) = 1 := by
    unfold FiniteDesign.Pr
    rw [← D.E_add]
    calc
      _ = D.E (fun _ => (1 : ℝ)) := D.E_congr (fun z => by
        by_cases hz : A K z <;> simp [FiniteDesign.ind, hz])
      _ = 1 := D.E_const 1
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  have hf : D.Pr (A K) ≤ 1 / 2 := by nlinarith
  linarith

end Papers.OaiGraphDecompositionsIntegral
