module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.StarsFreshRows
public import Causalean.Experimentation.DesignBased.ProductBlock

/-! # Fresh center rows in the actual finite random host

Past-state fibers and a fresh center row use disjoint unordered edge
coordinates. Their expectations factor without conditioning on a positive
probability history or paying for the number of histories.
-/

@[expose] public section

open Causalean.Experimentation.DesignBased
open scoped BigOperators

namespace Papers.OaiGraphDecompositionsIntegral

attribute [local instance] Classical.propDecidable

-- @node: starHostRows
/-- Given [a finite leaf bin](hyp:Y), [a sequence of centers](hyp:c),
[all of whose centers lie outside that bin](hyp:hc), and [Boolean indicators for
the host edges](hyp:z), the [host row entry](goal) at [a trial index](hyp:j) and
[a leaf in the bin](hyp:y) is the indicator of the edge joining that trial's center to that leaf. -/
def starHostRows {n : ℕ} (Y : Finset (Fin n)) (c : ℕ → Fin n)
    (hc : ∀ j, c j ∉ Y) (z : KEdge n → Bool) (j : ℕ) (y : ↥Y) : Bool :=
  z (neighborhoodEdge Y (c j) (hc j) y)

-- @node: star_host_row_edges_ne
/-- If [the first center lies outside the leaf bin](hyp:ha), [the second center
also lies outside it](hyp:hb), and [the centers are distinct](hyp:hab), then
[an edge from the first center to any leaf in the bin differs from an edge from
the second center to any leaf in the bin](goal). -/
lemma star_host_row_edges_ne {n : ℕ} (Y : Finset (Fin n))
    (a b : Fin n) (ha : a ∉ Y) (hb : b ∉ Y) (hab : a ≠ b)
    (y y' : ↥Y) : neighborhoodEdge Y a ha y ≠ neighborhoodEdge Y b hb y' := by
  intro h
  have he := congrArg Subtype.val h
  simp only [neighborhoodEdge, Sym2.eq_iff] at he
  rcases he with he | he
  · exact hab he.1
  · exact ha (he.1 ▸ y'.property)

-- @node: star_host_fresh_row_factor
/-- If [the edge probability lies between zero and one](hyp:hp),
[all centers lie outside the leaf bin](hyp:hc), [the current center differs from
every earlier center](hyp:hct), and [the event is determined by the earlier rows](hyp:hA),
then [the expected current-row statistic restricted to that event equals the
event's probability times the statistic's expectation under independent Bernoulli
indicators on the leaf bin](goal). -/
lemma star_host_fresh_row_factor {n : ℕ} (p : ℝ) (hp : p ∈ Set.Icc 0 1)
    (Y : Finset (Fin n)) (c : ℕ → Fin n) (hc : ∀ j, c j ∉ Y) (t : ℕ)
    (hct : ∀ j < t, c j ≠ c t)
    (A : (KEdge n → Bool) → Prop)
    (hA : ∀ z z', (∀ j < t, starHostRows Y c hc z j =
      starHostRows Y c hc z' j) → (A z ↔ A z'))
    (F : (↥Y → Bool) → ℝ) :
    (randomHost n p hp).E (fun z => if A z then F (starHostRows Y c hc z t) else 0) =
      (randomHost n p hp).Pr A * (productMeasure ↥Y p).E F := by
  classical
  let e := neighborhoodEdge Y (c t) (hc t)
  let block : Finset (KEdge n) := Finset.univ.image e
  have hrow : ∀ z z', (∀ d ∈ block, z d = z' d) →
      F (starHostRows Y c hc z t) = F (starHostRows Y c hc z' t) := by
    intro z z' hz
    apply congrArg F
    funext y
    exact hz (e y) (Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩)
  have hpast : ∀ z z', (∀ d ∉ block, z d = z' d) → (A z ↔ A z') := by
    intro z z' hz
    apply hA z z'
    intro j hj
    funext y
    apply hz (neighborhoodEdge Y (c j) (hc j) y)
    intro hd
    obtain ⟨y', _, he⟩ := Finset.mem_image.mp hd
    exact star_host_row_edges_ne Y (c j) (c t) (hc j) (hc t) (hct j hj) y y' he.symm
  have hfactor : (randomHost n p hp).E (fun z =>
      F (starHostRows Y c hc z t) * FiniteDesign.ind A z) =
      (randomHost n p hp).E (fun z => F (starHostRows Y c hc z t)) *
        (randomHost n p hp).Pr A := by
    dsimp [randomHost]
    rw [Toolkit.Foundations.Probability.bernoulliCube_eq p hp.1 hp.2]
    apply FiniteDesign.E_prod_block_mul _ block
    · exact hrow
    · intro z z' hz
      simp only [FiniteDesign.ind, hpast z z' hz]
  have hpoint : (fun z => if A z then F (starHostRows Y c hc z t) else 0) =
      (fun z => F (starHostRows Y c hc z t) * FiniteDesign.ind A z) := by
    funext z
    by_cases h : A z <;> simp [FiniteDesign.ind, h]
  rw [hpoint, hfactor]
  have hmarg : (randomHost n p hp).E (fun z => F (starHostRows Y c hc z t)) =
      (productMeasure ↥Y p).E F :=
    productMeasure_E_comp_injective p e (neighborhoodEdge_injective Y (c t) (hc t)) F
  rw [hmarg, mul_comm]

-- @node: star_row_update_todo_mem
/-- If [a leaf count occurs in the demand list after a row update](hyp:h),
then [it occurred in the demand list before the update](goal). -/
lemma star_row_update_todo_mem {X : Type} [DecidableEq X]
    (s : StarRowState X) (z : X → Bool) (ell : ℕ)
    (h : ell ∈ (starRowUpdate s z).todo) : ell ∈ s.todo := by
  cases hs : s.todo with
  | nil => simp [starRowUpdate, hs] at h
  | cons a rest =>
      by_cases ha : a ≤ (starRowNeighbors s z).card
      · simp only [starRowUpdate, hs, if_pos ha] at h
        simp [h]
      · simpa [starRowUpdate, hs, ha] using h

-- @node: star_row_state_todo_mem
/-- If [a leaf count occurs among the remaining demands after the specified
number of trials](hyp:h), then [it occurs in the initial demand list](goal). -/
lemma star_row_state_todo_mem {X : Type} [DecidableEq X]
    (s : StarRowState X) (rows : ℕ → X → Bool) (t ell : ℕ)
    (h : ell ∈ (starRowStateAfter s rows t).todo) : ell ∈ s.todo := by
  induction t with
  | zero => exact h
  | succ t ih => exact ih (star_row_update_todo_mem _ _ ell h)

-- @node: star_row_expected_gain_ge_active
/-- If [the unused leaves cover the designated available-leaf count](hyp:hleaves)
and [every remaining demand has positive binomial trial success probability](hyp:hu),
then [the expected decrease in reciprocal-success budget under an independent
Bernoulli row is at least zero for a finished state and at least one otherwise](goal). -/
lemma star_row_expected_gain_ge_active {X : Type} [Fintype X] [DecidableEq X]
    (n : ℕ) (p : ℝ) (s : StarRowState X)
    (hleaves : availableLeaves n ≤ s.unused.card)
    (hu : ∀ ell ∈ s.todo, 0 < starTrialSuccess n p ell) :
    (productMeasure X p).E (fun z => starTodoBudget (starTrialSuccess n p) s.todo -
      starTodoBudget (starTrialSuccess n p) (starRowUpdate s z).todo) ≥
        if s.todo = [] then 0 else 1 := by
  cases h : s.todo with
  | nil => simp [starRowUpdate, h, FiniteDesign.E_const]
  | cons ell rest =>
      have hpos := hu ell (by simp [h])
      have hd := star_row_binomial_budget_drop n p s ell rest h hleaves hpos
      rw [FiniteDesign.E_sub, FiniteDesign.E_const]
      simp only [List.cons_ne_nil, if_false]
      rw [h] at hd
      linarith

-- @node: star_host_adaptive_budget_drop
/-- Suppose [the edge probability lies between zero and one](hyp:hp),
[all centers lie outside the leaf bin](hyp:hc), [the current center differs from
every earlier center](hyp:hct), [the initial unused leaves cover the total demand
plus the designated available-leaf reserve](hyp:hreserve), and [every initial
demand has positive binomial success probability](hyp:hu). Then [the expected
budget after the next host row plus the probability that demands remain before
that row is at most the expected budget before the row](goal). -/
lemma star_host_adaptive_budget_drop {n : ℕ} (p : ℝ) (hp : p ∈ Set.Icc 0 1)
    (Y : Finset (Fin n)) (c : ℕ → Fin n) (hc : ∀ j, c j ∉ Y)
    (s : StarRowState ↥Y) (t : ℕ) (hct : ∀ j < t, c j ≠ c t)
    (hreserve : availableLeaves n + s.todo.sum ≤ s.unused.card)
    (hu : ∀ ell ∈ s.todo, 0 < starTrialSuccess n p ell) :
    (randomHost n p hp).E (fun z => starTodoBudget (starTrialSuccess n p)
      (starRowStateAfter s (starHostRows Y c hc z) (t + 1)).todo) +
      (randomHost n p hp).Pr (fun z =>
        (starRowStateAfter s (starHostRows Y c hc z) t).todo ≠ []) ≤
    (randomHost n p hp).E (fun z => starTodoBudget (starTrialSuccess n p)
      (starRowStateAfter s (starHostRows Y c hc z) t).todo) := by
  classical
  let I := Fin t → ↥Y → Bool
  let choose : (KEdge n → Bool) → I := fun z j => starHostRows Y c hc z j
  let rows : I → ℕ → ↥Y → Bool := fun i j y =>
    if hj : j < t then i ⟨j, hj⟩ y else false
  let state : I → StarRowState ↥Y := fun i => starRowStateAfter s (rows i) t
  have hstate (z : KEdge n → Bool) :
      state (choose z) = starRowStateAfter s (starHostRows Y c hc z) t := by
    apply star_row_state_depends_on_past
    intro j hj
    funext y
    simp [rows, choose, hj]
  have hfixed (i : I) : (productMeasure ↥Y p).E (fun z =>
      starTodoBudget (starTrialSuccess n p) (state i).todo -
        starTodoBudget (starTrialSuccess n p) (starRowUpdate (state i) z).todo) ≥
      if (state i).todo = [] then 0 else 1 := by
    apply star_row_expected_gain_ge_active
    · exact star_row_state_leaf_reserve s (rows i) t _ hreserve
    · intro ell hell
      exact hu ell (star_row_state_todo_mem s (rows i) t ell hell)
  have hfresh (i : I) : (randomHost n p hp).E (fun z => if choose z = i then
      starTodoBudget (starTrialSuccess n p) (state i).todo -
        starTodoBudget (starTrialSuccess n p)
          (starRowUpdate (state i) (starHostRows Y c hc z t)).todo else 0) =
      (randomHost n p hp).Pr (fun z => choose z = i) *
        (productMeasure ↥Y p).E (fun z =>
          starTodoBudget (starTrialSuccess n p) (state i).todo -
            starTodoBudget (starTrialSuccess n p) (starRowUpdate (state i) z).todo) := by
    have hA : ∀ z z', (∀ j < t, starHostRows Y c hc z j =
        starHostRows Y c hc z' j) → (choose z = i ↔ choose z' = i) := by
      intro z z' hz
      have he : choose z = choose z' := by
        funext j
        exact hz j j.isLt
      rw [he]
    convert star_host_fresh_row_factor p hp Y c hc t hct
      (fun z => choose z = i) hA (fun z =>
        starTodoBudget (starTrialSuccess n p) (state i).todo -
          starTodoBudget (starTrialSuccess n p) (starRowUpdate (state i) z).todo)
      using 1 <;> congr!
  have hd := star_adaptive_row_budget_drop (randomHost n p hp) (productMeasure ↥Y p)
    choose state (fun z => starHostRows Y c hc z t) (starTrialSuccess n p) hfixed
    (by intro i; convert hfresh i using 1 <;> congr!)
  simpa only [hstate, starRowStateAfter] using hd

-- @node: star_host_finish_probability
/-- Suppose [the edge probability lies between zero and one](hyp:hp),
[all centers lie outside the leaf bin](hyp:hc), [the trial horizon is positive](hyp:hK),
[the centers used before that horizon are pairwise distinct](hyp:hdistinct),
[the initial unused leaves cover total demand plus the designated reserve](hyp:hreserve),
[every initial demand has positive binomial success probability](hyp:hu), and
[the initial reciprocal-success budget is at most half the horizon](hyp:hbudget).
Then [all demands are completed by the horizon with probability at least one half
in the finite random host](goal). -/
lemma star_host_finish_probability {n : ℕ} (p : ℝ) (hp : p ∈ Set.Icc 0 1)
    (Y : Finset (Fin n)) (c : ℕ → Fin n) (hc : ∀ j, c j ∉ Y)
    (s : StarRowState ↥Y) (K : ℕ) (hK : 0 < K)
    (hdistinct : ∀ t < K, ∀ j < t, c j ≠ c t)
    (hreserve : availableLeaves n + s.todo.sum ≤ s.unused.card)
    (hu : ∀ ell ∈ s.todo, 0 < starTrialSuccess n p ell)
    (hbudget : starTodoBudget (starTrialSuccess n p) s.todo ≤ (K : ℝ) / 2) :
    (1 / 2 : ℝ) ≤ (randomHost n p hp).Pr (fun z =>
      (starRowStateAfter s (starHostRows Y c hc z) K).todo = []) := by
  have hf := star_finite_trial_finish_probability (randomHost n p hp)
    (fun t z => starTodoBudget (starTrialSuccess n p)
      (starRowStateAfter s (starHostRows Y c hc z) t).todo)
    (fun t z => (starRowStateAfter s (starHostRows Y c hc z) t).todo ≠ [])
    K hK (starTodoBudget (starTrialSuccess n p) s.todo) (fun _ => rfl)
    (by
      intro t ht
      convert star_host_adaptive_budget_drop p hp Y c hc s t
        (hdistinct t ht) hreserve hu using 1; congr!)
    (fun z => star_todo_budget_nonneg _ _ (fun ell =>
      (binomialDesign (availableLeaves n) p).Pr_nonneg _))
    (by
      intro t ht z hactive hfinished
      have hstay := star_row_state_finished_stays_finished s (starHostRows Y c hc z)
        t (K - t) hfinished
      rw [Nat.add_sub_of_le ht.le] at hstay
      exact hactive hstay)
    hbudget
  simpa only [not_not] using hf

-- @node: star_todo_budget_eq_grouped
/-- [The reciprocal-success budget equals the sum over distinct leaf counts of
their multiplicity in the demand list divided by their success value](goal). -/
lemma star_todo_budget_eq_grouped (u : ℕ → ℝ) (L : List ℕ) :
    starTodoBudget u L = ∑ ell ∈ L.toFinset, (L.count ell : ℝ) / u ell := by
  rw [starTodoBudget, Finset.sum_list_map_count]
  simp only [nsmul_eq_mul, div_eq_mul_inv]

-- @node: star_todo_budget_lt
/-- Suppose [the host size is positive](hyp:hn), [the density parameter is
nonnegative](hyp:hq), [the star constant times that parameter is less than one half](hyp:hp),
[every demand is at least one](hyp:hell), [each demand is at most one hundredth
of the host size](hyp:hsize), [for each demand, its factorial divided by the host
size raised to one more than that demand, times its multiplicity divided by twice
the exponential of one, is at most the density parameter raised to that demand](hyp:hcount),
and [the number of demands is at most one two-hundredth of the host size](hyp:hcomponents).
Then [the reciprocal-binomial-success budget at edge probability equal to the
star constant times the density parameter is less than one eighth of the host size](goal). -/
lemma star_todo_budget_lt (n : ℕ) (q : ℝ) (L : List ℕ)
    (hn : 0 < n) (hq : 0 ≤ q) (hp : starConstA * q < 1 / 2)
    (hell : ∀ ell ∈ L, 1 ≤ ell)
    (hsize : ∀ ell ∈ L, (ell : ℝ) ≤ (n : ℝ) / 100)
    (hcount : ∀ ell ∈ L, (ell.factorial : ℝ) / (n : ℝ) ^ (ell + 1) *
      ((L.count ell : ℝ) / (2 * Real.exp 1)) ≤ q ^ ell)
    (hcomponents : (L.length : ℝ) ≤ (n : ℝ) / 200) :
    starTodoBudget (starTrialSuccess n (starConstA * q)) L < (n : ℝ) / 8 := by
  have hsum : (∑ ell ∈ L.toFinset, (L.count ell : ℝ)) = (L.length : ℝ) := by
    exact_mod_cast List.sum_toFinset_count_eq_length L
  rw [star_todo_budget_eq_grouped]
  have hb := star_total_trial_budget_le n L.toFinset (fun ell => L.count ell) q
    hn hq hp (fun ell h => hell ell (List.mem_toFinset.mp h))
    (fun ell h => hsize ell (List.mem_toFinset.mp h))
    (fun ell h => hcount ell (List.mem_toFinset.mp h)) (by simpa [hsum] using hcomponents)
  calc
    _ ≤ (3 / 100 + 2 * Real.exp 1 / 99) * n := hb
    _ < (1 / 8 : ℝ) * n := mul_lt_mul_of_pos_right star_trial_budget_coefficient_lt
      (by exact_mod_cast hn)
    _ = _ := by ring

-- @node: star_trial_success_pos_of_count
/-- Suppose [the host size is positive](hyp:hn), [the leaf demand is at least one](hyp:hell),
[its multiplicity is positive](hyp:hm), [the density parameter is nonnegative](hyp:hq),
[the star constant times that parameter is less than one half](hyp:hp),
[the demand is at most one hundredth of the host size](hyp:hsize), and
[the demand's factorial divided by the host size raised to one more than the
demand, times its multiplicity divided by twice the exponential of one, is at most
the density parameter raised to the demand](hyp:hcount). Then [the binomial trial
success probability at edge probability equal to the star constant times the
density parameter is positive](goal). -/
lemma star_trial_success_pos_of_count (n ell m : ℕ) (q : ℝ)
    (hn : 0 < n) (hell : 1 ≤ ell) (hm : 0 < m) (hq : 0 ≤ q)
    (hp : starConstA * q < 1 / 2) (hsize : (ell : ℝ) ≤ (n : ℝ) / 100)
    (hcount : (ell.factorial : ℝ) / (n : ℝ) ^ (ell + 1) *
      ((m : ℝ) / (2 * Real.exp 1)) ≤ q ^ ell) :
    0 < starTrialSuccess n (starConstA * q) ell := by
  have hA : 0 < starConstA := by unfold starConstA; positivity
  by_cases hmean : 2 * (ell : ℝ) ≤ starBinomialMean n (starConstA * q)
  · have h := star_trial_success_large_mean n ell (starConstA * q)
      (mul_nonneg hA.le hq) (by linarith) hell hmean
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 6) h
  · have h := star_trial_success_small_mean_of_count n ell m q hn hq hp hsize
      (lt_of_not_ge hmean) hcount
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    exact lt_of_lt_of_le (by positivity) h

-- @node: star_host_finish_probability_of_count
/-- Suppose [the host has at least two vertices](hyp:hn), [the density parameter
is nonnegative](hyp:hq), [the star constant times that parameter is less than one half](hyp:hp),
[all centers lie outside the leaf bin](hyp:hc), [the centers used in the first
half of the host size, rounded down, are pairwise distinct](hyp:hdistinct),
[the initial unused leaves cover total demand plus the designated reserve](hyp:hreserve),
[each demand is at least one](hyp:hell), [each demand is at most one hundredth
of the host size](hyp:hsize), [for each demand, its factorial divided by the host
size raised to one more than that demand, times its multiplicity divided by twice
the exponential of one, is at most the density parameter raised to that demand](hyp:hcount),
and [the number of demands is at most one two-hundredth of the host size](hyp:hcomponents).
Then [all demands are completed within half the host size, rounded down, with
probability at least one half in the random host whose edge probability is the
star constant times the density parameter](goal). -/
lemma star_host_finish_probability_of_count {n : ℕ} (q : ℝ) (hn : 2 ≤ n)
    (hq : 0 ≤ q) (hp : starConstA * q < 1 / 2)
    (Y : Finset (Fin n)) (c : ℕ → Fin n) (hc : ∀ j, c j ∉ Y)
    (s : StarRowState ↥Y)
    (hdistinct : ∀ t < n / 2, ∀ j < t, c j ≠ c t)
    (hreserve : availableLeaves n + s.todo.sum ≤ s.unused.card)
    (hell : ∀ ell ∈ s.todo, 1 ≤ ell)
    (hsize : ∀ ell ∈ s.todo, (ell : ℝ) ≤ (n : ℝ) / 100)
    (hcount : ∀ ell ∈ s.todo, (ell.factorial : ℝ) / (n : ℝ) ^ (ell + 1) *
      ((s.todo.count ell : ℝ) / (2 * Real.exp 1)) ≤ q ^ ell)
    (hcomponents : (s.todo.length : ℝ) ≤ (n : ℝ) / 200) :
    (1 / 2 : ℝ) ≤ (randomHost n (starConstA * q)
      (by exact ⟨mul_nonneg (by unfold starConstA; positivity) hq, by linarith⟩)).Pr (fun z =>
      (starRowStateAfter s (starHostRows Y c hc z) (n / 2)).todo = []) := by
  have hA : 0 < starConstA := by unfold starConstA; positivity
  apply star_host_finish_probability (starConstA * q)
    ⟨mul_nonneg hA.le hq, by linarith⟩ Y c hc s (n / 2) (by omega)
    hdistinct hreserve
  · intro ell hmem
    exact star_trial_success_pos_of_count n ell (s.todo.count ell) q (by omega)
      (hell ell hmem) (List.count_pos_iff.mpr hmem) hq hp
      (hsize ell hmem) (hcount ell hmem)
  · have hb := star_todo_budget_lt n q s.todo (by omega) hq hp hell hsize hcount hcomponents
    have hnK : n ≤ 4 * (n / 2) := by omega
    have hr : (n : ℝ) ≤ 4 * (n / 2 : ℕ) := by exact_mod_cast hnK
    linarith

end Papers.OaiGraphDecompositionsIntegral
