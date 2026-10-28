module

public import Papers.OaiBoundDyadicTriangular.Basic

/-! # Unique parents of XOR-admissible dyadic children -/

@[expose] public section

open scoped BigOperators

namespace Papers.OaiBoundDyadicTriangular

-- @node: xor3_mod_two
/-- [The remainder modulo two of the bitwise exclusive-or of three
nonnegative integers equals the bitwise exclusive-or of their individual
remainders modulo two](goal). -/
lemma xor3_mod_two (a b c : ℕ) :
    xor3 a b c % 2 = xor3 (a % 2) (b % 2) (c % 2) := by
  have hm (a b : ℕ) : (a ^^^ b) % 2 = a % 2 ^^^ b % 2 :=
    Nat.xor_mod_two_pow (n := 1)
  simp only [xor3, hm]

-- @node: admissible_parent
/-- If [a triple of nonnegative indices has bitwise exclusive-or zero](hyp:hn),
then [the parent triple obtained by dividing each index by two and rounding
down also has bitwise exclusive-or zero](goal). -/
lemma admissible_parent {n : Fin 3 → ℕ} (hn : IsAdmissible n) :
    IsAdmissible (fun v => n v / 2) := by
  have h := congrArg (fun a : ℕ => a / 2) hn
  simpa only [IsAdmissible, xor3, Nat.xor_div_two, Nat.zero_div] using h

-- @node: admissible_lowBits
/-- If [a triple of nonnegative indices has bitwise exclusive-or zero](hyp:hn),
then [its three remainders modulo two form an allowed child-bit triple,
whose bitwise exclusive-or is zero](goal). -/
lemma admissible_lowBits {n : Fin 3 → ℕ} (hn : IsAdmissible n) :
    (fun v => (⟨n v % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2)) ∈ childBits := by
  have h := congrArg (fun a : ℕ => a % 2 ^ 1) hn
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  change xor3 (n 0 % 2) (n 1 % 2) (n 2 % 2) = 0
  change xor3 (n 0) (n 1) (n 2) % 2 = 0 at h
  rwa [xor3_mod_two] at h

-- @node: mem_children_iff
/-- If [the parent triple n has bitwise exclusive-or zero](hyp:hn), then
[a triple c is one of its dyadic children exactly when c has bitwise
exclusive-or zero and dividing each index of c by two and rounding down
recovers n](goal). -/
lemma mem_children_iff (n c : Fin 3 → ℕ) (hn : IsAdmissible n) :
    c ∈ children n ↔ IsAdmissible c ∧ (fun v => c v / 2) = n := by
  constructor
  · intro hc
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hc
    have hp : (fun v => (2 * n v + (b v).val) / 2) = n := by
      funext v
      have := (b v).isLt
      omega
    refine ⟨?_, hp⟩
    have hb' : xor3 (b 0).val (b 1).val (b 2).val = 0 :=
      (Finset.mem_filter.mp hb).2
    -- The high bits are the parent and the low bits are b.
    change xor3 (2 * n 0 + (b 0).val) (2 * n 1 + (b 1).val)
      (2 * n 2 + (b 2).val) = 0
    have hq : xor3 (2 * n 0 + (b 0).val) (2 * n 1 + (b 1).val)
        (2 * n 2 + (b 2).val) / 2 = 0 := by
      simpa only [IsAdmissible, xor3, Nat.xor_div_two, congrFun hp] using hn
    have hr : xor3 (2 * n 0 + (b 0).val) (2 * n 1 + (b 1).val)
        (2 * n 2 + (b 2).val) % 2 = 0 := by
      have hm (v : Fin 3) : (2 * n v + (b v).val) % 2 = (b v).val := by
        have := (b v).isLt
        omega
      simpa only [xor3_mod_two, hm] using hb'
    omega
  · rintro ⟨hc, hp⟩
    apply Finset.mem_image.mpr
    refine ⟨fun v => ⟨c v % 2, Nat.mod_lt _ (by decide)⟩,
      admissible_lowBits hc, ?_⟩
    funext v
    have hv := congrFun hp v
    dsimp at hv ⊢
    omega

-- @node: admissible_edge_pair_injective
/-- [For any cyclic position v among three indices, the indices at v and
the next position uniquely determine a triple whose bitwise exclusive-or
is zero](goal). -/
lemma admissible_edge_pair_injective (v : Fin 3) :
    Function.Injective (fun n : admissibleSet => (n.val v, n.val (v + 1))) := by
  intro n q h
  have hn : n.val 0 ^^^ n.val 1 = n.val 2 := Nat.xor_eq_zero_iff.mp n.property
  have hq : q.val 0 ^^^ q.val 1 = q.val 2 := Nat.xor_eq_zero_iff.mp q.property
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  apply Subtype.ext
  fin_cases v
  · change n.val 0 = q.val 0 at h₁
    change n.val 1 = q.val 1 at h₂
    have he : n.val 2 = q.val 2 := by rw [← hn, ← hq, h₁, h₂]
    funext w
    fin_cases w <;> assumption
  · change n.val 1 = q.val 1 at h₁
    change n.val 2 = q.val 2 at h₂
    have he : n.val 0 = q.val 0 := (Nat.xor_left_inj (z := n.val 1)).mp (by rw [hn, h₁, hq, h₂])
    funext w
    fin_cases w <;> assumption
  · change n.val 2 = q.val 2 at h₁
    change n.val 0 = q.val 0 at h₂
    have he : n.val 1 = q.val 1 := (Nat.xor_right_inj (x := n.val 0)).mp (by rw [hn, h₂, hq, h₁])
    funext w
    fin_cases w <;> assumption

-- @node: admissibleChildEquiv
/-- [The parent-child correspondence is a bijection from pairs consisting
of a triple with bitwise exclusive-or zero and one of its dyadic children
to all triples with bitwise exclusive-or zero, sending each pair to its
child](goal). -/
noncomputable def admissibleChildEquiv :
    (Σ n : admissibleSet, {c // c ∈ children n.val}) ≃ admissibleSet :=
  Equiv.ofBijective
    (fun p => ⟨p.2.val, ((mem_children_iff p.1.val p.2.val p.1.property).mp
      p.2.property).1⟩) (by
    constructor
    · intro a b h
      have hc : a.2.val = b.2.val := congrArg Subtype.val h
      have hn : a.1 = b.1 := Subtype.ext (by
        rw [← ((mem_children_iff a.1.val a.2.val a.1.property).mp a.2.property).2,
          ← ((mem_children_iff b.1.val b.2.val b.1.property).mp b.2.property).2, hc])
      apply Sigma.ext hn
      cases a with | mk na ca =>
        cases b with | mk nb cb =>
          dsimp at hn hc ⊢
          subst nb
          exact heq_of_eq (Subtype.ext hc)
    · intro c
      let n : admissibleSet := ⟨fun v => c.val v / 2, admissible_parent c.property⟩
      refine ⟨⟨n, ⟨c.val, ?_⟩⟩, rfl⟩
      exact (mem_children_iff n.val c.val n.property).mpr ⟨c.property, rfl⟩)

-- @node: summable_children_and_tsum
/-- If [the real-valued function g is summable over triples of nonnegative
indices with bitwise exclusive-or zero](hyp:hg), then [the sums of g over
each such parent's dyadic children are summable over parents, and summing
these child sums equals the original sum of g over all such triples](goal). -/
lemma summable_children_and_tsum (g : (Fin 3 → ℕ) → ℝ)
    (hg : Summable (fun n : admissibleSet => g n.val)) :
    Summable (fun n : admissibleSet => ∑ c ∈ children n.val, g c) ∧
    (∑' n : admissibleSet, ∑ c ∈ children n.val, g c) =
      ∑' c : admissibleSet, g c.val := by
  classical
  have hs : Summable (fun p : Σ n : admissibleSet, {c // c ∈ children n.val} =>
      g p.2.val) := admissibleChildEquiv.summable_iff.mpr hg
  have hi (n : admissibleSet) :
      (∑' c : {c // c ∈ children n.val}, g c.val) = ∑ c ∈ children n.val, g c := by
    rw [tsum_fintype]
    exact (Finset.sum_subtype (children n.val) (fun _ => Iff.rfl) g).symm
  refine ⟨?_, ?_⟩
  · simpa only [hi] using hs.sigma
  · calc
      _ = ∑' p : Σ n : admissibleSet, {c // c ∈ children n.val}, g p.2.val := by
        rw [hs.tsum_sigma]
        simp only [hi]
      _ = _ := admissibleChildEquiv.tsum_eq (fun n : admissibleSet => g n.val)

end Papers.OaiBoundDyadicTriangular
