module
public import Papers.TbsNeuralCausalPi.Helpers.SimulationNetworkComparisons
public import Mathlib.Data.Set.Card.Arithmetic
/-! # Counting all stored network shapes

Layer dimensions have a finite code independent of their numerical weights.
Summing the activation-history comparison bound over these codes removes the
fixed-shape restriction, including zero-width and zero-depth architectures.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
noncomputable section

-- @node: simulationNetworkShapeSpace
/-- The [space of network shape codes](goal) for [hidden depth L](hyp:L) and
[dimension bound w](hyp:w) records a final hidden width and an input-output
dimension pair for each hidden layer, with every dimension between zero and w. -/
abbrev simulationNetworkShapeSpace (L w : ℕ) :=
  Fin (w + 1) × (Fin L → Fin (w + 1) × Fin (w + 1))

-- @node: simulationNetworkShapeCode
/-- The [shape code](goal) of [a ReLU network](hyp:q), using [dimension bound w](hyp:w)
with [input dimension at most w](hyp:hdin) and [hidden-width bound at most w](hyp:hW),
records its final hidden width and the input and output dimensions of each hidden layer. -/
def simulationNetworkShapeCode {din dout W L : ℕ} (q : ReLUNet din dout W L)
    (w : ℕ) (hdin : din ≤ w) (hW : W ≤ w) : simulationNetworkShapeSpace L w :=
  (⟨finalWidth din q.hidden, Nat.lt_succ_of_le
    (simulation_finalWidth_le q.hidden din w hdin
      (fun l hl => (q.widths l hl).trans hW))⟩,
    fun k =>
      (⟨(simulationStoredLayers q k).input, Nat.lt_succ_of_le
        (simulationStoredLayers_dimensions q w hdin hW k k.isLt).1⟩,
       ⟨(simulationStoredLayers q k).output, Nat.lt_succ_of_le
        (simulationStoredLayers_dimensions q w hdin hW k k.isLt).2⟩))

/-- If [the input dimension is at most w](hyp:hdin) and [the hidden-width bound
is at most w](hyp:hW), then [two networks have equal shape codes exactly when
their final hidden widths and all hidden-layer input and output dimensions agree](goal). -/
-- @node: simulationNetworkShapeCode_eq_iff
lemma simulationNetworkShapeCode_eq_iff {din dout W L : ℕ}
    (q r : ReLUNet din dout W L) (w : ℕ) (hdin : din ≤ w) (hW : W ≤ w) :
    simulationNetworkShapeCode q w hdin hW = simulationNetworkShapeCode r w hdin hW ↔
      simulationSameNetworkShape q r := by
  constructor
  · intro h
    refine ⟨congrArg (fun c => c.1.val) h, ?_⟩
    intro k hk
    exact ⟨congrArg (fun c => (c.2 ⟨k, hk⟩).1.val) h,
      congrArg (fun c => (c.2 ⟨k, hk⟩).2.val) h⟩
  · rintro ⟨hf, hl⟩
    apply Prod.ext
    · exact Fin.ext hf
    · funext k
      exact Prod.ext (Fin.ext (hl k k.isLt).1) (Fin.ext (hl k k.isLt).2)

-- @node: simulationNetworkShapeSpace_card
/-- [The number of shape codes at hidden depth L and dimension bound w is
$(w+1)^{2L+1}$](goal). -/
lemma simulationNetworkShapeSpace_card (L w : ℕ) :
    Fintype.card (simulationNetworkShapeSpace L w) = (w + 1) ^ (2 * L + 1) := by
  simp only [simulationNetworkShapeSpace, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin]
  rw [← pow_two, ← pow_mul, pow_succ, Nat.mul_comm]

/-- If [the input dimension is at most w](hyp:hdin), [the hidden-width bound is
at most w](hyp:hW), and [each fixed network shape yields at most N distinct
values of f](hyp:hf), then [over all network shapes, f takes at most
$(w+1)^{2L+1}N$ distinct values](goal). -/
-- @node: simulationNetwork_shape_union_encard_le
lemma simulationNetwork_shape_union_encard_le {din dout W L : ℕ} {A : Type*}
    (f : ReLUNet din dout W L → A) (w : ℕ) (hdin : din ≤ w) (hW : W ≤ w)
    (N : ℕ)
    (hf : ∀ q : ReLUNet din dout W L,
      {s | ∃ r : ReLUNet din dout W L, simulationSameNetworkShape q r ∧ f r = s}.encard ≤ N) :
    (Set.range f).encard ≤ ((w + 1) ^ (2 * L + 1) * N : ℕ) := by
  classical
  let S : simulationNetworkShapeSpace L w → Set A := fun c =>
    {s | ∃ r : ReLUNet din dout W L,
      simulationNetworkShapeCode r w hdin hW = c ∧ f r = s}
  have hS (c) : (S c).encard ≤ N := by
    by_cases hc : ∃ q : ReLUNet din dout W L, simulationNetworkShapeCode q w hdin hW = c
    · obtain ⟨q, hq⟩ := hc
      apply (Set.encard_mono (b := {s | ∃ r : ReLUNet din dout W L,
        simulationSameNetworkShape q r ∧ f r = s}) ?_).trans (hf q)
      rintro s ⟨r, hr, hs⟩
      exact ⟨r, (simulationNetworkShapeCode_eq_iff q r w hdin hW).mp
        (hq.trans hr.symm), hs⟩
    · have he : S c = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro s ⟨r, hr, _⟩
        exact hc ⟨r, hr⟩
      simp [he]
  calc
    (Set.range f).encard ≤ (⋃ c, S c).encard := by
      apply Set.encard_mono
      rintro s ⟨r, rfl⟩
      exact Set.mem_iUnion.mpr ⟨simulationNetworkShapeCode r w hdin hW, r, rfl, rfl⟩
    _ ≤ ∑ c, (S c).encard := Set.encard_iUnion_le_of_fintype S
    _ ≤ ∑ _c : simulationNetworkShapeSpace L w, (N : ℕ∞) :=
      Finset.sum_le_sum (fun c _ => hS c)
    _ = ((w + 1) ^ (2 * L + 1) * N : ℕ) := by
      rw [Finset.sum_const, Finset.card_univ, simulationNetworkShapeSpace_card,
        nsmul_eq_mul]
      simp only [Nat.cast_mul]

/-- If [the input dimension is at most w](hyp:hdin), [the output dimension is at
most w](hyp:hdout), and [the hidden-width bound is at most w](hyp:hW), then
[the number of joint weak
and strict threshold-comparison patterns of network outputs, over all weights
and shapes, is at most
$(w+1)^{2L+1}(8mW\max(L,1)+5)^{((L+1)w(w+1)+2)L}
(8|J|(L+1)+5)^{(L+1)w(w+1)+2}$](goal). -/
-- @node: simulationNetwork_all_shapes_grid_patterns_encard_le
lemma simulationNetwork_all_shapes_grid_patterns_encard_le {din dout W L m : ℕ}
    {J : Type*} [Fintype J]
    (sample : Fin m → L1Vec din) (coord : J → Fin m × Fin dout) (threshold : J → ℝ)
    (w : ℕ) (hdin : din ≤ w) (hdout : dout ≤ w) (hW : W ≤ w) :
    (Set.range (fun r : ReLUNet din dout W L => fun j =>
      (decide ((r.eval (sample (coord j).1)).ofLp (coord j).2 ≤ threshold j),
        decide ((r.eval (sample (coord j).1)).ofLp (coord j).2 < threshold j)))).encard ≤
      ((w + 1) ^ (2 * L + 1) *
        ((8 * (m * W) * max L 1 + 5) ^ (((L + 1) * (w * (w + 1)) + 2) * L) *
          (8 * Fintype.card J * (L + 1) + 5) ^ ((L + 1) * (w * (w + 1)) + 2)) : ℕ) := by
  apply simulationNetwork_shape_union_encard_le _ w hdin hW
  intro q
  exact simulationNetwork_same_shape_grid_patterns_encard_le q sample coord threshold w hdin hdout hW

/-- If [the input dimension is at most w](hyp:hdin), [the output dimension is at
most w](hyp:hdout), and [the hidden-width bound is at most w](hyp:hW), then
[the number of joint weak
and strict threshold-comparison patterns after clipping outputs to the K-cube,
over all weights and shapes, is at most
$(w+1)^{2L+1}(8mW\max(L,1)+5)^{((L+1)w(w+1)+2)L}
(8|J|(L+1)+5)^{(L+1)w(w+1)+2}$](goal). -/
-- @node: simulationNetwork_all_shapes_clipped_patterns_encard_le
lemma simulationNetwork_all_shapes_clipped_patterns_encard_le {din dout W L m : ℕ}
    {J : Type*} [Fintype J]
    (sample : Fin m → L1Vec din) (coord : J → Fin m × Fin dout) (threshold : J → ℝ) (K : ℝ)
    (w : ℕ) (hdin : din ≤ w) (hdout : dout ≤ w) (hW : W ≤ w) :
    (Set.range (fun r : ReLUNet din dout W L => fun j =>
      (decide ((truncK K (r.eval (sample (coord j).1))).ofLp (coord j).2 ≤ threshold j),
        decide ((truncK K (r.eval (sample (coord j).1))).ofLp (coord j).2 < threshold j)))).encard ≤
      ((w + 1) ^ (2 * L + 1) *
        ((8 * (m * W) * max L 1 + 5) ^ (((L + 1) * (w * (w + 1)) + 2) * L) *
          (8 * Fintype.card J * (L + 1) + 5) ^ ((L + 1) * (w * (w + 1)) + 2)) : ℕ) := by
  apply simulationNetwork_shape_union_encard_le _ w hdin hW
  intro q
  exact simulationNetwork_same_shape_clipped_patterns_encard_le q sample coord threshold K w hdin hdout hW

/-- If [the input dimension is at most w](hyp:hdin), [the output dimension is at
most w](hyp:hdout), and [the hidden-width bound is at most w](hyp:hW), then
[decoding the clipped-output
threshold comparisons of any allowed subset of networks produces at most
$(w+1)^{2L+1}(8mW\max(L,1)+5)^{((L+1)w(w+1)+2)L}
(8|J|(L+1)+5)^{(L+1)w(w+1)+2}$ distinct readouts](goal). -/
-- @node: simulationNetwork_all_shapes_clipped_readout_encard_le
lemma simulationNetwork_all_shapes_clipped_readout_encard_le {din dout W L m : ℕ}
    {J A : Type*} [Fintype J]
    (sample : Fin m → L1Vec din) (coord : J → Fin m × Fin dout) (threshold : J → ℝ) (K : ℝ)
    (decode : (J → Bool × Bool) → A) (allowed : Set (ReLUNet din dout W L))
    (w : ℕ) (hdin : din ≤ w) (hdout : dout ≤ w) (hW : W ≤ w) :
    {s | ∃ r ∈ allowed, decode (fun j =>
      (decide ((truncK K (r.eval (sample (coord j).1))).ofLp (coord j).2 ≤ threshold j),
        decide ((truncK K (r.eval (sample (coord j).1))).ofLp (coord j).2 < threshold j))) = s}.encard ≤
      ((w + 1) ^ (2 * L + 1) *
        ((8 * (m * W) * max L 1 + 5) ^ (((L + 1) * (w * (w + 1)) + 2) * L) *
          (8 * Fintype.card J * (L + 1) + 5) ^ ((L + 1) * (w * (w + 1)) + 2)) : ℕ) := by
  let f := fun r : ReLUNet din dout W L => fun j =>
    (decide ((truncK K (r.eval (sample (coord j).1))).ofLp (coord j).2 ≤ threshold j),
      decide ((truncK K (r.eval (sample (coord j).1))).ofLp (coord j).2 < threshold j))
  apply (Set.encard_mono (b := decode '' Set.range f) ?_).trans
    ((Set.encard_image_le _ _).trans
      (simulationNetwork_all_shapes_clipped_patterns_encard_le sample coord threshold K w hdin hdout hW))
  rintro s ⟨r, _, rfl⟩
  exact ⟨f r, ⟨r, rfl⟩, rfl⟩

/-- [The product of the shape count $(w+1)^{2L+1}$, the hidden-history bound
$(8mW\max(L,1)+5)^{((L+1)w(w+1)+2)L}$, and the terminal comparison bound
$(8J(L+1)+5)^{(L+1)w(w+1)+2}$ is at most
$(8(mW+J)(L+1)+w+6)^{(w(w+1)+5)(L+1)^2}$](goal). -/
-- @node: simulationNetwork_shape_bound_le_depth_square
lemma simulationNetwork_shape_bound_le_depth_square (m W L J w : ℕ) :
    (w + 1) ^ (2 * L + 1) *
      ((8 * (m * W) * max L 1 + 5) ^ (((L + 1) * (w * (w + 1)) + 2) * L) *
        (8 * J * (L + 1) + 5) ^ ((L + 1) * (w * (w + 1)) + 2)) ≤
      (8 * (m * W + J) * (L + 1) + w + 6) ^
        ((w * (w + 1) + 5) * (L + 1) ^ 2) := by
  let B := 8 * (m * W + J) * (L + 1) + w + 6
  let P := (L + 1) * (w * (w + 1)) + 2
  have hshape : w + 1 ≤ B := by dsimp [B]; omega
  have hhidden : 8 * (m * W) * max L 1 + 5 ≤ B := by
    have hmax : max L 1 ≤ L + 1 := by omega
    have h := Nat.mul_le_mul_left (8 * (m * W)) hmax
    dsimp [B]
    nlinarith
  have hterminal : 8 * J * (L + 1) + 5 ≤ B := by
    dsimp [B]
    rw [Nat.mul_add 8 (m * W) J, Nat.add_mul]
    omega
  have he : (2 * L + 1) + (P * L + P) ≤
      (w * (w + 1) + 5) * (L + 1) ^ 2 := by
    dsimp [P]
    nlinarith [Nat.zero_le (w * (w + 1) * L * (L + 1))]
  calc
    _ ≤ B ^ (2 * L + 1) * (B ^ (P * L) * B ^ P) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hshape _)
        (Nat.mul_le_mul (Nat.pow_le_pow_left hhidden _) (Nat.pow_le_pow_left hterminal _))
    _ = B ^ ((2 * L + 1) + (P * L + P)) := by rw [← pow_add, ← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by dsimp [B]; omega) he

/-- If [the input dimension is at most w](hyp:hdin), [the output dimension is at
most w](hyp:hdout), and [the hidden-width bound is at most w](hyp:hW), then
[the number of joint weak
and strict threshold-comparison patterns of clipped network outputs, over all
weights and shapes, is at most
$(8(mW+|J|)(L+1)+w+6)^{(w(w+1)+5)(L+1)^2}$](goal). -/
-- @node: simulationNetwork_all_shapes_clipped_depth_square
lemma simulationNetwork_all_shapes_clipped_depth_square {din dout W L m : ℕ}
    {J : Type*} [Fintype J]
    (sample : Fin m → L1Vec din) (coord : J → Fin m × Fin dout) (threshold : J → ℝ) (K : ℝ)
    (w : ℕ) (hdin : din ≤ w) (hdout : dout ≤ w) (hW : W ≤ w) :
    (Set.range (fun r : ReLUNet din dout W L => fun j =>
      (decide ((truncK K (r.eval (sample (coord j).1))).ofLp (coord j).2 ≤ threshold j),
        decide ((truncK K (r.eval (sample (coord j).1))).ofLp (coord j).2 < threshold j)))).encard ≤
      ((8 * (m * W + Fintype.card J) * (L + 1) + w + 6) ^
        ((w * (w + 1) + 5) * (L + 1) ^ 2) : ℕ) := by
  exact (simulationNetwork_all_shapes_clipped_patterns_encard_le
    sample coord threshold K w hdin hdout hW).trans
      (by exact_mod_cast simulationNetwork_shape_bound_le_depth_square m W L (Fintype.card J) w)

end
end Papers.TbsNeuralCausalPi
