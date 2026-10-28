module

public import Papers.OaiNearInclusionsVon.Helpers.MainSequence

/-! Extracting small implementing unitaries when eventual uniform separation fails. -/

public section

namespace Papers.OaiNearInclusionsVon

set_option maxHeartbeats 800000

open Filter
open scoped Topology

/-- [Square-summable families in a separable complex normed space, indexed by
a countable set, form a separable space](goal). -/
-- @node: lp_separableSpace_of_countable
lemma lp_separableSpace_of_countable {I E : Type*} [Countable I]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace.SeparableSpace E] :
    TopologicalSpace.SeparableSpace (lp (fun _ : I => E) 2) := by
  classical
  let s : Set (lp (fun _ : I => E) 2) := ⋃ i : I, Set.range (lp.single 2 i)
  have hs : TopologicalSpace.IsSeparable s := by
    apply TopologicalSpace.IsSeparable.iUnion
    intro i
    exact TopologicalSpace.isSeparable_range
      (lp.singleContinuousLinearMap ℂ (fun _ : I => E) 2 i).continuous
  have hd : Dense (Submodule.span ℂ s : Set (lp (fun _ : I => E) 2)) := by
    intro x
    apply isClosed_closure.mem_of_tendsto (lp.hasSum_single (by norm_num) x)
    apply Eventually.of_forall
    intro t
    apply subset_closure
    exact (Submodule.span ℂ s).sum_mem fun i _ =>
      Submodule.subset_span (Set.mem_iUnion.mpr ⟨i, ⟨x i, rfl⟩⟩)
  exact hd.isSeparable_iff.mp hs.span

-- @node: mainH_separableSpace
/-- [The main Hilbert space at every clock index has a countable dense subset](goal). -/
lemma mainH_separableSpace (n : ClockNat) : TopologicalSpace.SeparableSpace (mainH n) := by
  let : Countable FreeGrp := FreeGroup.toWord_injective.countable
  let : TopologicalSpace.SeparableSpace (lp (fun _ : FreeGrp => ClockSpace n) 2) :=
    lp_separableSpace_of_countable
  let : TopologicalSpace.SeparableSpace (Lsp (ClockSpace n)) :=
    lp_separableSpace_of_countable
  exact lp_separableSpace_of_countable

/-- Given [an admissibility criterion for objects at each clock index](hyp:P)
and [a real-valued size for each such object](hyp:d), suppose [all sizes are
nonnegative](hyp:hd) and [no positive constant eventually bounds the sizes of
all admissible objects from below](hyp:hsmall). Then [there are strictly
increasing clock indices and an admissible object at each selected index whose
sizes tend to zero](goal). -/
-- @node: clock_index_small_values_subsequence
lemma clock_index_small_values_subsequence
    (E : ClockNat → Type*) (P : ∀ n, E n → Prop) (d : ∀ n, E n → ℝ)
    (hd : ∀ n x, 0 ≤ d n x)
    (hsmall : ¬ ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n in atTop, ∀ x, P n x → ε ≤ d n x) :
    ∃ (φ : ℕ → ClockNat) (x : ∀ k, E (φ k)),
      StrictMono φ ∧ (∀ k, P (φ k) (x k)) ∧
      Tendsto (fun k => d (φ k) (x k)) atTop (𝓝 0) := by
  classical
  let : Nonempty ClockNat := ⟨⟨3, le_rfl⟩⟩
  have hex (ε : ℝ) (hε : 0 < ε) (b : ClockNat) :
      ∃ n : ClockNat, b < n ∧ ∃ x : E n, P n x ∧ d n x < ε := by
    by_contra! h
    apply hsmall
    refine ⟨ε, hε, eventually_atTop.2 ⟨⟨b.val + 1, by
      have hb := b.property; unfold ClockIndex at *; omega⟩, ?_⟩⟩
    intro n hn x hx
    exact h n (by change b.val < n.val; change b.val + 1 ≤ n.val at hn; omega) x hx
  let X := Σ n : ClockNat, {x : E n // P n x}
  have hnext (k : ℕ) (b : ClockNat) :
      ∃ x : X, b < x.1 ∧ d x.1 x.2.val < ((k : ℝ) + 1)⁻¹ := by
    obtain ⟨n, hn, x, hx, he⟩ := hex (((k : ℝ) + 1)⁻¹) (by positivity) b
    exact ⟨⟨n, ⟨x, hx⟩⟩, hn, he⟩
  let next (k : ℕ) (b : ClockNat) : X := Classical.choose (hnext k b)
  have hnext_spec (k : ℕ) (b : ClockNat) :
      b < (next k b).1 ∧ d (next k b).1 (next k b).2.val < ((k : ℝ) + 1)⁻¹ :=
    Classical.choose_spec (hnext k b)
  let xs : ℕ → X := fun k => Nat.rec (next 0 ⟨3, le_rfl⟩)
    (fun j x => next (j + 1) x.1) k
  have hxs (k : ℕ) : d (xs k).1 (xs k).2.val < ((k : ℝ) + 1)⁻¹ := by
    cases k with
    | zero => exact (hnext_spec 0 ⟨3, le_rfl⟩).2
    | succ k => exact (hnext_spec (k + 1) (xs k).1).2
  refine ⟨fun k => (xs k).1, fun k => (xs k).2.val,
    strictMono_nat_of_lt_succ (fun k => (hnext_spec (k + 1) (xs k).1).1),
    fun k => (xs k).2.property, ?_⟩
  apply squeeze_zero (fun k => hd _ _) (fun k => (hxs k).le)
  simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- Suppose [the representations and coefficients satisfy the circle-family
conditions](hyp:hπ) and [no positive constant eventually bounds from below the
distance from the identity of every unitary conjugating the source algebra into
the target algebra](hyp:hsmall). Then [there are strictly increasing clock
indices and such implementing unitaries at those indices whose distances from
the identity tend to zero](goal). -/
-- @node: main_small_implementations_subsequence
lemma main_small_implementations_subsequence
    (π : CircleRep) (A : LaurentData) (hπ : IsCircleFamily π A)
    (hsmall : ¬ ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n in atTop,
      ∀ u ∈ unitary (mainH n →L[ℂ] mainH n),
        (∀ x ∈ mainSource π A hπ n, u * x * star u ∈ mainTarget n) → ε ≤ ‖u - 1‖) :
    ∃ (φ : ℕ → ClockNat) (u : ∀ k, mainH (φ k) →L[ℂ] mainH (φ k)),
      StrictMono φ ∧ (∀ k, u k ∈ unitary _) ∧
      (∀ k, ∀ x ∈ mainSource π A hπ (φ k), u k * x * star (u k) ∈ mainTarget (φ k)) ∧
      Tendsto (fun k => ‖u k - 1‖) atTop (𝓝 0) := by
  have hs : ¬ ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n in atTop,
      ∀ u : mainH n →L[ℂ] mainH n,
        (u ∈ unitary _ ∧ ∀ x ∈ mainSource π A hπ n,
          u * x * star u ∈ mainTarget n) → ε ≤ ‖u - 1‖ := by
    intro h
    apply hsmall
    obtain ⟨ε, hε, h⟩ := h
    refine ⟨ε, hε, ?_⟩
    exact h.mono fun n hn u hu hi => hn u ⟨hu, hi⟩
  obtain ⟨φ, u, hφ, hu, ht⟩ := clock_index_small_values_subsequence
    (fun n => mainH n →L[ℂ] mainH n)
    (fun n u => u ∈ unitary _ ∧ ∀ x ∈ mainSource π A hπ n,
      u * x * star u ∈ mainTarget n)
    (fun _ u => ‖u - 1‖) (fun _ _ => norm_nonneg _) hs
  exact ⟨φ, u, hφ, fun k => (hu k).1, fun k => (hu k).2, ht⟩

/-- If [the representations and coefficients satisfy the circle-family
conditions](hyp:hπ) and [no sequence of unitaries along strictly increasing
clock indices can both conjugate the source algebras into the target algebras
and have distances from the identity tending to zero](hyp:hno), [there is a
positive constant that eventually bounds from below the distance from the
identity of every unitary implementing these inclusions](goal). -/
-- @node: main_eventual_separation_of_no_subsequence
lemma main_eventual_separation_of_no_subsequence
    (π : CircleRep) (A : LaurentData) (hπ : IsCircleFamily π A)
    (hno : ∀ (φ : ℕ → ClockNat) (u : ∀ k, mainH (φ k) →L[ℂ] mainH (φ k)),
      StrictMono φ → (∀ k, u k ∈ unitary _) →
      (∀ k, ∀ x ∈ mainSource π A hπ (φ k), u k * x * star (u k) ∈ mainTarget (φ k)) →
      ¬ Tendsto (fun k => ‖u k - 1‖) atTop (𝓝 0)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n in atTop,
      ∀ u ∈ unitary (mainH n →L[ℂ] mainH n),
        (∀ x ∈ mainSource π A hπ n, u * x * star u ∈ mainTarget n) → ε ≤ ‖u - 1‖ := by
  by_contra h
  obtain ⟨φ, u, hφ, hu, hi, hd⟩ := main_small_implementations_subsequence π A hπ h
  exact hno φ u hφ hu hi hd

end Papers.OaiNearInclusionsVon
