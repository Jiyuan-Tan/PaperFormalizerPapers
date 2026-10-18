module
public import Causalean.Stat.Concentration.VC.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic
/-! # Solving the simulation-table shattering inequality

The pattern count for the current generator class leads to a logarithmic
inequality in the number of shattered inputs. A tangent bound for the logarithm
solves that inequality without an implicit occurrence of that number on the
right. The generator pattern count itself remains a separate obligation.
-/
public section
namespace Papers.TbsNeuralCausalPi

/-- If [x is positive](hyp:hx) and [the scale t is positive](hyp:ht), then
[log x is at most x/t + log t − 1](goal). -/
-- @node: simulation_log_le_scaled
lemma simulation_log_le_scaled {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    Real.log x ≤ x / t + Real.log t - 1 := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx ht)
  rw [Real.log_div hx.ne' ht.ne'] at h
  linarith

/-- If [b is positive](hyp:hb), [c is positive](hyp:hc), [ℓ is positive](hyp:hl),
[x + h is positive](hyp:hxh), and [ℓx is at most a + b log(c(x + h))](hyp:hgrowth),
then [x is at most 2a/ℓ + (2b/ℓ) log(2bc/ℓ) + h](goal). -/
-- @node: simulation_logarithmic_inequality_bound
lemma simulation_logarithmic_inequality_bound {x a b c h l : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hl : 0 < l) (hxh : 0 < x + h)
    (hgrowth : l * x ≤ a + b * Real.log (c * (x + h))) :
    x ≤ 2 * a / l + 2 * b / l * Real.log (2 * b * c / l) + h := by
  have ht : 0 < 2 * b / l := by positivity
  have htangent := simulation_log_le_scaled hxh ht
  have hlog : Real.log (c * (x + h)) ≤
      (x + h) / (2 * b / l) + Real.log (2 * b * c / l) - 1 := by
    rw [Real.log_mul hc.ne' hxh.ne']
    have he : Real.log (2 * b * c / l) = Real.log c + Real.log (2 * b / l) := by
      rw [show 2 * b * c / l = c * (2 * b / l) by ring, Real.log_mul hc.ne' ht.ne']
    rw [he]
    linarith
  have hhalf : b * ((x + h) / (2 * b / l)) = l * (x + h) / 2 := by
    field_simp
  have hmul := mul_le_mul_of_nonneg_left hlog hb.le
  have hfinal : l * x ≤ 2 * a + 2 * b * Real.log (2 * b * c / l) + l * h := by
    nlinarith
  calc
    x ≤ (2 * a + 2 * b * Real.log (2 * b * c / l) + l * h) / l :=
      (le_div_iff₀ hl).mpr (by nlinarith)
    _ = _ := by field_simp

/-- If [the table-count bound is positive](hyp:htables), [the pattern-count
base is positive](hyp:hbase), and [2ᵐ is at most the table-count bound times
2ʲ times the b-th power of that base](hyp:hcount), then [m log 2 is at most
the log of the table-count bound plus j log 2 plus b times the log of the
base](goal). -/
-- @node: simulation_pattern_count_log_bound
lemma simulation_pattern_count_log_bound (m j b : ℕ) {tables base : ℝ}
    (htables : 0 < tables) (hbase : 0 < base)
    (hcount : (2 : ℝ) ^ m ≤ tables * 2 ^ j * base ^ b) :
    (m : ℝ) * Real.log 2 ≤
      Real.log tables + (j : ℝ) * Real.log 2 + (b : ℝ) * Real.log base := by
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ m) hcount
  rw [Real.log_mul (by positivity : tables * 2 ^ j ≠ 0) (pow_ne_zero _ hbase.ne'),
    Real.log_mul htables.ne' (by positivity : (2 : ℝ) ^ j ≠ 0)] at hlog
  simpa only [Real.log_pow] using hlog

/-- If [the exponent b is positive](hyp:hb), [the table-count bound is
positive](hyp:htables), [C is positive](hyp:hC), [H is positive](hyp:hH),
[ρ is positive](hyp:hrho), and [2ᵐ is at most the table-count bound times
2ʲ times (C(m + H)H/ρ) raised to b](hyp:hcount), then [m is at most
2(log tables + j log 2)/log 2 + (2b/log 2) log(2bCH/(ρ log 2)) + H](goal). -/
-- @node: simulation_shattered_card_bound
lemma simulation_shattered_card_bound (m j b : ℕ) {tables C H rho : ℝ}
    (hb : 0 < b) (htables : 0 < tables) (hC : 0 < C) (hH : 0 < H)
    (hrho : 0 < rho)
    (hcount : (2 : ℝ) ^ m ≤ tables * 2 ^ j * (C * ((m : ℝ) + H) * H / rho) ^ b) :
    (m : ℝ) ≤
      2 * (Real.log tables + (j : ℝ) * Real.log 2) / Real.log 2 +
      2 * b / Real.log 2 * Real.log (2 * b * (C * H / rho) / Real.log 2) + H := by
  have hbase : 0 < C * ((m : ℝ) + H) * H / rho := by positivity
  have hlog := simulation_pattern_count_log_bound m j b htables hbase hcount
  have he : C * ((m : ℝ) + H) * H / rho = (C * H / rho) * ((m : ℝ) + H) := by ring
  rw [he] at hlog
  exact simulation_logarithmic_inequality_bound (by exact_mod_cast hb)
    (by positivity) (Real.log_pos (by norm_num)) (by positivity)
    (by simpa only [mul_comm (Real.log 2)] using hlog)

/-- If [the Boolean function class shatters a set of coordinates of the
sample](hyp:hs), then [on the smaller sample obtained by enumerating those
coordinates, the class realizes every Boolean pattern](goal). -/
-- @node: simulation_growthFamily_eq_univ_of_shatters
lemma simulation_growthFamily_eq_univ_of_shatters
    {X I : Type*} (pi : I → X → Bool) {n : ℕ} (sample : Fin n → X)
    (s : Finset (Fin n))
    (hs : (Causalean.Stat.Concentration.growthFamily pi sample).Shatters s) :
    Causalean.Stat.Concentration.growthFamily pi
      (fun k : Fin s.card => sample ((s.equivFin.symm k).val)) = Finset.univ := by
  classical
  let e : Fin s.card ↪ Fin n :=
    ⟨fun k => (s.equivFin.symm k).val, Subtype.val_injective.comp s.equivFin.symm.injective⟩
  apply Finset.eq_univ_of_forall
  intro A
  have hsub : A.map e ⊆ s := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hk
    exact (s.equivFin.symm i).property
  obtain ⟨u, hu, heq⟩ := hs hsub
  obtain ⟨i, hi⟩ := Causalean.Stat.Concentration.mem_growthFamily_iff.mp hu
  apply Causalean.Stat.Concentration.mem_growthFamily_iff.mpr
  refine ⟨i, ?_⟩
  ext k
  rw [Causalean.Stat.Concentration.restrictionPattern_mem_iff]
  have hmem : e k ∈ u ↔ k ∈ A := by
    calc
      e k ∈ u ↔ e k ∈ s ∩ u := by simp [e, (s.equivFin.symm k).property]
      _ ↔ e k ∈ A.map e := by rw [heq]
      _ ↔ k ∈ A := Finset.mem_map' e
  rw [← hmem, ← hi, Causalean.Stat.Concentration.restrictionPattern_mem_iff]
  rfl

/-- Suppose [b is positive](hyp:hb), [the table-count bound is positive](hyp:htables),
[C is positive](hyp:hC), [H is positive](hyp:hH), and [ρ is positive](hyp:hrho).
If [on every m-point sample of inputs paired with real thresholds the
subgraphs of the real-valued function class realize at most
tables · 2ʲ · (C(m + H)H/ρ)ᵇ patterns](hyp:hpatterns), and
[2(log tables + j log 2)/log 2 + (2b/log 2) log(2bCH/(ρ log 2)) + H
is at most v](hyp:hbudget), then [the class has pseudo-dimension at most v](goal). -/
-- @node: simulation_hasPseudoDimAtMost_of_pattern_count
lemma simulation_hasPseudoDimAtMost_of_pattern_count
    {X I : Type*} (F : I → X → ℝ) (j b v : ℕ) {tables C H rho : ℝ}
    (hb : 0 < b) (htables : 0 < tables) (hC : 0 < C) (hH : 0 < H)
    (hrho : 0 < rho)
    (hpatterns : ∀ (m : ℕ) (sample : Fin m → X × ℝ),
      ((Causalean.Stat.Concentration.growthFamily
        (Causalean.Stat.Concentration.subgraphClassifier F) sample).card : ℝ) ≤
        tables * 2 ^ j * (C * ((m : ℝ) + H) * H / rho) ^ b)
    (hbudget : 2 * (Real.log tables + (j : ℝ) * Real.log 2) / Real.log 2 +
      2 * b / Real.log 2 * Real.log (2 * b * (C * H / rho) / Real.log 2) + H ≤ v) :
    Causalean.Stat.Concentration.HasPseudoDimAtMost F v := by
  classical
  intro n sample
  unfold Finset.vcDim
  apply Finset.sup_le
  intro s hs
  have hshatter := Finset.mem_shatterer.mp hs
  have hp := hpatterns s.card
    (fun k : Fin s.card => sample ((s.equivFin.symm k).val))
  rw [simulation_growthFamily_eq_univ_of_shatters _ sample s hshatter] at hp
  simp only [Finset.card_univ, Fintype.card_finset, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat] at hp
  have hcard := simulation_shattered_card_bound s.card j b hb htables hC hH hrho hp
  exact_mod_cast hcard.trans hbudget

/-- [On any finite sample of inputs paired with real thresholds, the number
of subgraph patterns of the zero-one indicators of a Boolean class is at
most the number of Boolean output patterns that the class realizes on the
same inputs](goal). -/
-- @node: simulation_indicator_subgraph_card_le
lemma simulation_indicator_subgraph_card_le
    {X I : Type*} (B : I → X → Bool) (m : ℕ) (sample : Fin m → X × ℝ) :
    (Causalean.Stat.Concentration.growthFamily
      (Causalean.Stat.Concentration.subgraphClassifier
        (fun i x => if B i x then (1 : ℝ) else 0)) sample).card ≤
      (Causalean.Stat.Concentration.growthFamily B (fun k => (sample k).1)).card := by
  classical
  let transform : Finset (Fin m) → Finset (Fin m) := fun p =>
    Finset.univ.filter fun k => if k ∈ p then (sample k).2 < 1 else (sample k).2 < 0
  apply le_trans (Finset.card_le_card (t :=
    (Causalean.Stat.Concentration.growthFamily B (fun k => (sample k).1)).image
      transform) ?_) (Finset.card_image_le)
  intro p hp
  obtain ⟨i, rfl⟩ := Causalean.Stat.Concentration.mem_growthFamily_iff.mp hp
  apply Finset.mem_image.mpr
  refine ⟨Causalean.Stat.Concentration.restrictionPattern (B i)
    (fun k => (sample k).1), ?_, ?_⟩
  · exact Causalean.Stat.Concentration.mem_growthFamily_iff.mpr ⟨i, rfl⟩
  · ext k
    cases h : B i (sample k).1 <;>
      simp [transform, Causalean.Stat.Concentration.restrictionPattern,
        Causalean.Stat.Concentration.subgraphClassifier, h]

/-- If [every pattern in the family can be encoded by a table from the finite
table collection and a pattern from the finite latent-pattern collection,
together with either a subset of the finite type set for the indicator or
the ambiguity output](hyp:hencode), then [the family's cardinality is at
most the number of tables times the number of latent patterns times the
sum of one and two raised to the number of types](goal). -/
-- @node: simulation_table_patterns_card_le
lemma simulation_table_patterns_card_le
    {T P J : Type*} [Fintype J]
    {m : ℕ} (tables : Finset T) (patterns : Finset P)
    (family : Finset (Finset (Fin m)))
    (indicator : T → P → Finset J → Finset (Fin m))
    (ambiguity : T → P → Finset (Fin m))
    (hencode : ∀ a ∈ family, ∃ t ∈ tables, ∃ p ∈ patterns,
      (∃ s, indicator t p s = a) ∨ ambiguity t p = a) :
    family.card ≤ tables.card * patterns.card * (2 ^ Fintype.card J + 1) := by
  classical
  let choices := fun t p => (Finset.univ.image (indicator t p)) ∪ {ambiguity t p}
  have hlocal : ∀ t p, (choices t p).card ≤ 2 ^ Fintype.card J + 1 := by
    intro t p
    exact (Finset.card_union_le _ _).trans (by
      simpa using Nat.add_le_add_right
        (Finset.card_image_le (s := (Finset.univ : Finset (Finset J)))
          (f := indicator t p)) 1)
  have hsub : family ⊆ tables.biUnion (fun t => patterns.biUnion (choices t)) := by
    intro a ha
    obtain ⟨t, ht, p, hp, h⟩ := hencode a ha
    apply Finset.mem_biUnion.mpr
    refine ⟨t, ht, Finset.mem_biUnion.mpr ⟨p, hp, ?_⟩⟩
    rcases h with ⟨s, rfl⟩ | rfl
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  calc
    family.card ≤ (tables.biUnion fun t => patterns.biUnion (choices t)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ t ∈ tables, ∑ p ∈ patterns, (2 ^ Fintype.card J + 1) :=
      Finset.card_biUnion_le.trans (Finset.sum_le_sum fun t ht =>
        Finset.card_biUnion_le.trans (Finset.sum_le_sum fun p hp => hlocal t p))
    _ = _ := by simp [Nat.mul_assoc]

/-- Suppose [b is positive](hyp:hb), [the table-count bound is positive](hyp:htables),
[C is positive](hyp:hC), [H is positive](hyp:hH), and [ρ is positive](hyp:hrho).
If [on every m-point input sample the Boolean class realizes at most
tables · 2ʲ · (C(m + H)H/ρ)ᵇ patterns](hyp:hpatterns), and
[2(log tables + j log 2)/log 2 + (2b/log 2) log(2bCH/(ρ log 2)) + H
is at most v](hyp:hbudget), then [the corresponding zero-one indicator
class has pseudo-dimension at most v](goal). -/
-- @node: simulation_indicator_hasPseudoDimAtMost_of_pattern_count
lemma simulation_indicator_hasPseudoDimAtMost_of_pattern_count
    {X I : Type*} (B : I → X → Bool) (j b v : ℕ) {tables C H rho : ℝ}
    (hb : 0 < b) (htables : 0 < tables) (hC : 0 < C) (hH : 0 < H)
    (hrho : 0 < rho)
    (hpatterns : ∀ (m : ℕ) (sample : Fin m → X),
      ((Causalean.Stat.Concentration.growthFamily B sample).card : ℝ) ≤
        tables * 2 ^ j * (C * ((m : ℝ) + H) * H / rho) ^ b)
    (hbudget : 2 * (Real.log tables + (j : ℝ) * Real.log 2) / Real.log 2 +
      2 * b / Real.log 2 * Real.log (2 * b * (C * H / rho) / Real.log 2) + H ≤ v) :
    Causalean.Stat.Concentration.HasPseudoDimAtMost
      (fun i x => if B i x then (1 : ℝ) else 0) v := by
  apply simulation_hasPseudoDimAtMost_of_pattern_count _ j b v
    hb htables hC hH hrho _ hbudget
  intro m sample
  exact (Nat.cast_le.mpr (simulation_indicator_subgraph_card_le B m sample)).trans
    (hpatterns m (fun k => (sample k).1))

end Papers.TbsNeuralCausalPi
