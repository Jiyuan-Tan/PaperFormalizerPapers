module
public import Papers.OaiGraphDecompositionsIntegral.Helpers.StarsHostRows
public import Papers.OaiGraphDecompositionsIntegral.Helpers.StarsCopyCover

/-! # Deterministic witnesses extracted from completed star trials

Successful rows provide exactly the demanded leaf counts, in order, with
pairwise disjoint chosen leaves. Every chosen edge belongs to its tested row.
-/

public section

namespace Papers.OaiGraphDecompositionsIntegral

attribute [local instance] Classical.propDecidable

-- @node: star_row_state_after_shift
/-- [Processing k plus one rows from an initial state gives the same state
as processing the first row and then processing k rows of the shifted
sequence](goal). -/
lemma star_row_state_after_shift {X : Type} [DecidableEq X]
    (s : StarRowState X) (rows : ℕ → X → Bool) (k : ℕ) :
    starRowStateAfter s rows (k + 1) =
      starRowStateAfter (starRowUpdate s (rows 0)) (fun j => rows (j + 1)) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      exact congrArg (fun a => starRowUpdate a (rows (k + 1))) ih

/-- If [no demands remain after K rows have been processed](hyp:hfinish),
then [there is a list of row indices and leaf sets whose leaf counts equal
the initial demands in order, with strictly increasing row indices and
pairwise disjoint leaf sets, each index below K and each leaf set contained
in the initial reserve and successful in its row](goal). -/
-- @node: star_finished_row_witnesses
lemma star_finished_row_witnesses {X : Type} [DecidableEq X]
    (s : StarRowState X) (rows : ℕ → X → Bool) (K : ℕ)
    (hfinish : (starRowStateAfter s rows K).todo = []) :
    ∃ W : List (ℕ × Finset X),
      W.map (fun a => a.2.card) = s.todo ∧
      W.Pairwise (fun a b => a.1 < b.1 ∧ Disjoint a.2 b.2) ∧
      ∀ a ∈ W, a.1 < K ∧ a.2 ⊆ s.unused ∧ ∀ x ∈ a.2, rows a.1 x = true := by
  classical
  induction K generalizing s rows with
  | zero =>
      refine ⟨[], ?_, List.Pairwise.nil, ?_⟩
      · exact hfinish.symm
      · simp
  | succ K ih =>
      rw [star_row_state_after_shift] at hfinish
      obtain ⟨W, hcards, hpair, hrows⟩ := ih (starRowUpdate s (rows 0))
        (fun j => rows (j + 1)) hfinish
      let shift : ℕ × Finset X → ℕ × Finset X := fun a => (a.1 + 1, a.2)
      have hpair' : (W.map shift).Pairwise
          (fun a b => a.1 < b.1 ∧ Disjoint a.2 b.2) := by
        apply List.pairwise_map.mpr
        exact hpair.imp (by intro a b h; exact ⟨Nat.add_lt_add_right h.1 1, h.2⟩)
      have hrows' : ∀ a ∈ W.map shift,
          a.1 < K + 1 ∧ a.2 ⊆ (starRowUpdate s (rows 0)).unused ∧
            ∀ x ∈ a.2, rows a.1 x = true := by
        intro a ha
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
        obtain ⟨ht, hsub, htrue⟩ := hrows b hb
        exact ⟨Nat.add_lt_add_right ht 1, hsub, htrue⟩
      have hcards' : (W.map shift).map (fun a => a.2.card) =
          (starRowUpdate s (rows 0)).todo := by
        simpa [List.map_map, shift, Function.comp_def] using hcards
      cases hs : s.todo with
      | nil => exact ⟨[], by simp, List.Pairwise.nil, by simp⟩
      | cons ell rest =>
          by_cases hok : ell ≤ (starRowNeighbors s (rows 0)).card
          · let S := starChooseLeaves (starRowNeighbors s (rows 0)) ell
            have hS := star_choose_leaves_spec (starRowNeighbors s (rows 0)) ell hok
            have hup : starRowUpdate s (rows 0) = ⟨rest, s.unused \ S⟩ := by
              simp [starRowUpdate, hs, hok, S]
            refine ⟨(0, S) :: W.map shift, ?_, ?_, ?_⟩
            · simpa only [List.map_cons, hcards', hup] using
                congrArg (fun k => k :: rest) hS.2
            · apply List.Pairwise.cons
              · intro a ha
                obtain ⟨ht, hsub, htrue⟩ := hrows' a ha
                refine ⟨?_, Finset.disjoint_left.mpr ?_⟩
                · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
                  simp [shift]
                · intro x hxS hxa
                  have hx := hsub hxa
                  rw [hup] at hx
                  exact (Finset.mem_sdiff.mp hx).2 hxS
              · exact hpair'
            · intro a ha
              rcases List.mem_cons.mp ha with rfl | ha
              · refine ⟨by omega, hS.1.trans (Finset.filter_subset _ _), ?_⟩
                intro x hx
                exact (Finset.mem_filter.mp (hS.1 hx)).2
              · obtain ⟨ht, hsub, htrue⟩ := hrows' a ha
                exact ⟨ht, hsub.trans (star_row_update_unused_subset s (rows 0)), htrue⟩
          · have hup : starRowUpdate s (rows 0) = s := by
              simp [starRowUpdate, hs, hok]
            refine ⟨W.map shift,
              hcards'.trans ((congrArg StarRowState.todo hup).trans hs), hpair', ?_⟩
            intro a ha
            simpa only [hup] using hrows' a ha

/-- If [the first center lies outside the common leaf bin](hyp:ha), [the
second center also lies outside that bin](hyp:hb), [the centers are
distinct](hyp:hab), and [the two chosen subsets of the bin are disjoint](hyp:hST),
then [the centered stars obtained from those choices have disjoint vertex
supports](goal). -/
-- @node: star_host_chosen_supports_disjoint
lemma star_host_chosen_supports_disjoint {n : ℕ} (Y : Finset (Fin n))
    (a b : Fin n) (ha : a ∉ Y) (hb : b ∉ Y) (hab : a ≠ b)
    (S T : Finset ↥Y) (hST : Disjoint S T) :
    Disjoint (centeredStarSupport (a, S.image Subtype.val))
      (centeredStarSupport (b, T.image Subtype.val)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hx hx'
  simp only [centeredStarSupport, Finset.mem_insert] at hx hx'
  rcases hx with rfl | hx
  · rcases hx' with he | hx'
    · exact hab he
    · obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx'
      exact ha (he ▸ y.property)
  · rcases hx' with rfl | hx'
    · obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
      exact hb (he ▸ y.property)
    · obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
      obtain ⟨y', hy', he'⟩ := Finset.mem_image.mp hx'
      have heq : y = y' := Subtype.ext (he.trans he'.symm)
      exact Finset.disjoint_left.mp hST hy (heq ▸ hy')

/-- Suppose [every trial center lies outside the leaf bin](hyp:hc) and
[the first K trial centers are distinct](hyp:hdistinct). If [the host-row
process has no remaining demands after K trials](hyp:hfinish), then [there
is a list of vertex-disjoint centered stars in the host whose leaf counts
equal the initial demands in order, with every center outside its leaves
and adjacent to each of them](goal). -/
-- @node: star_host_finished_witnesses
lemma star_host_finished_witnesses {n : ℕ}
    (Y : Finset (Fin n)) (c : ℕ → Fin n) (hc : ∀ j, c j ∉ Y)
    (s : StarRowState ↥Y) (z : KEdge n → Bool) (K : ℕ)
    (hdistinct : ∀ t < K, ∀ j < t, c j ≠ c t)
    (hfinish : (starRowStateAfter s (starHostRows Y c hc z) K).todo = []) :
    ∃ W : List (Fin n × Finset (Fin n)),
      W.map (fun a => a.2.card) = s.todo ∧
      W.Pairwise (fun a b => Disjoint (centeredStarSupport a) (centeredStarSupport b)) ∧
      ∀ a ∈ W, a.1 ∉ a.2 ∧ ∀ x ∈ a.2, (hostGraph z).Adj a.1 x := by
  classical
  obtain ⟨W, hcards, hpair, hrows⟩ := star_finished_row_witnesses s
    (starHostRows Y c hc z) K hfinish
  let place : ℕ × Finset ↥Y → Fin n × Finset (Fin n) :=
    fun a => (c a.1, a.2.image Subtype.val)
  refine ⟨W.map place, ?_, ?_, ?_⟩
  · simpa [List.map_map, place, Function.comp_def,
      Finset.card_image_of_injective _ Subtype.val_injective] using hcards
  · apply List.pairwise_map.mpr
    apply hpair.imp_of_mem
    intro a b ha hb hab
    exact star_host_chosen_supports_disjoint Y (c a.1) (c b.1)
      (hc a.1) (hc b.1) (hdistinct b.1 (hrows b hb).1 a.1 hab.1)
      a.2 b.2 hab.2
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    refine ⟨?_, ?_⟩
    · intro h
      obtain ⟨y, hy, he⟩ := Finset.mem_image.mp h
      change y.val = c b.1 at he
      exact hc b.1 (he ▸ y.property)
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      have htrue := (hrows b hb).2.2 y hy
      have hne : c b.1 ≠ y.val := fun he => hc b.1 (he ▸ y.property)
      simpa [place, starHostRows, hostGraph, SimpleGraph.fromEdgeSet_adj,
        neighborhoodEdge, hne] using htrue

/-- Suppose [n is at least two](hyp:hn), [q is nonnegative](hyp:hq), and
[the sampling density A times q is below one half](hyp:hp), where A is the
fixed star constant. Assume [every trial center lies outside the leaf
bin](hyp:hc), [the centers in the first half of the trials are distinct](hyp:hdistinct),
[the unused reserve contains at least the designated available-leaf count
plus the sum of the demands](hyp:hreserve), [each demand is positive](hyp:hell),
[each demand is at most n divided by 100](hyp:hsize), [for every demanded
size ell, ell factorial divided by n to the power ell plus one, times its
multiplicity divided by twice Euler's number, is at most q to the power
ell](hyp:hcount), and [there are at most n divided by 200 demands](hyp:hcomponents).
Then [with probability at least one half, the random host at density A
times q contains a list of vertex-disjoint centered stars whose leaf counts
equal the initial demands in order, each center outside its leaves and
adjacent to all of them](goal). -/
-- @node: star_host_packing_probability_of_count
lemma star_host_packing_probability_of_count {n : ℕ} (q : ℝ) (hn : 2 ≤ n)
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
      ∃ W : List (Fin n × Finset (Fin n)),
        W.map (fun a => a.2.card) = s.todo ∧
        W.Pairwise (fun a b => Disjoint (centeredStarSupport a) (centeredStarSupport b)) ∧
        ∀ a ∈ W, a.1 ∉ a.2 ∧ ∀ x ∈ a.2, (hostGraph z).Adj a.1 x) := by
  classical
  apply (star_host_finish_probability_of_count q hn hq hp Y c hc s
    hdistinct hreserve hell hsize hcount hcomponents).trans
  apply Causalean.Experimentation.DesignBased.FiniteDesign.Pr_mono
  intro z hz
  exact star_host_finished_witnesses Y c hc s z (n / 2) hdistinct hz

end Papers.OaiGraphDecompositionsIntegral
