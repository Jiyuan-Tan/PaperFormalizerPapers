module
public import Papers.TbsNeuralCausalPi.Helpers.SimulationGeneratorHistories
public import Papers.TbsNeuralCausalPi.Helpers.SimulationNetworkShapes
/-! # Uniform generator comparison counts over all stored shapes

Shape transport preserves the signed bridge between the generator blocks.
Finite codes for both blocks of every component remove the prototype restriction
without changing the quadratic dependence of the exponent on total depth.
The joint latent-block product keeps sample indices paired and pays table and
type-subset choices once after all generator comparisons.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
noncomputable section

-- @node: simulationStoredLayers_shape_congr_le
/-- For [two networks](hyp:q,r) with [the same stored layer shapes](hyp:h),
at [layer index k](hyp:k) [no greater than their depth](hyp:hk),
[the stored layers have equal input and output dimensions](goal). -/
lemma simulationStoredLayers_shape_congr_le {din dout W L : ℕ}
    (q r : ReLUNet din dout W L) (h : simulationSameNetworkShape q r)
    (k : ℕ) (hk : k ≤ L) :
    (simulationStoredLayers q k).input = (simulationStoredLayers r k).input ∧
      (simulationStoredLayers q k).output = (simulationStoredLayers r k).output := by
  by_cases hlt : k < L
  · exact h.2 k hlt
  · have he : k = L := by omega
    subst k
    rw [simulationStoredLayers, simulationStoredLayers,
      dif_neg (by rw [q.depth]; omega : ¬ L < q.hidden.length),
      dif_neg (by rw [r.depth]; omega : ¬ L < r.hidden.length)]
    exact ⟨h.1, rfl⟩

-- @node: simulationTwoBlockLayers_shape_congr
/-- For [a pair of first blocks](hyp:q1,r1) and [a pair of second blocks](hyp:q2,r2),
if [the first blocks have the same shapes](hyp:h1) and [the second blocks have
the same shapes](hyp:h2), then at [index k](hyp:k) [within the combined layer
sequence](hyp:hk), [the two combined layers have equal input and output dimensions](goal). -/
lemma simulationTwoBlockLayers_shape_congr {din dmid dout W1 W2 L1 L2 : ℕ}
    (q1 r1 : ReLUNet din dmid W1 L1) (q2 r2 : ReLUNet dmid dout W2 L2)
    (h1 : simulationSameNetworkShape q1 r1) (h2 : simulationSameNetworkShape q2 r2)
    (k : ℕ) (hk : k < L1 + L2 + 2) :
    (simulationTwoBlockLayers q1 q2 k).input = (simulationTwoBlockLayers r1 r2 k).input ∧
      (simulationTwoBlockLayers q1 q2 k).output = (simulationTwoBlockLayers r1 r2 k).output := by
  unfold simulationTwoBlockLayers
  split_ifs with h
  · exact simulationStoredLayers_shape_congr_le q1 r1 h1 k h
  · exact simulationStoredLayers_shape_congr_le q2 r2 h2 _ (by omega)

-- @node: simulationBridgeState_shape_congr
/-- For [two layer sequences](hyp:layers,other), [an activation schedule](hyp:activate),
[polynomial inputs for each sample](hyp:z), and [a propagation depth t](hyp:t),
if [the layer dimensions agree before t](hyp:hshape), then for [a sign history](hyp:s),
[sample a](hyp:a), and [coordinate j](hyp:j), [the propagated bridge polynomials
are identical](goal). -/
lemma simulationBridgeState_shape_congr {m w : ℕ} (layers other : ℕ → AffineLayer)
    (activate : ℕ → Bool) (z : Fin m → ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ)
    (t : ℕ) (hshape : ∀ k < t, (layers k).input = (other k).input ∧
      (layers k).output = (other k).output)
    (s : List (Fin m × Fin w → Bool × Bool)) (a : Fin m) (j : ℕ) :
    simulationBridgeState layers activate z t s a j =
      simulationBridgeState other activate z t s a j := by
  induction t generalizing s j with
  | zero => rfl
  | succ t ih =>
    have hz : simulationBridgeState layers activate z t s.tail a =
        simulationBridgeState other activate z t s.tail a :=
      funext (fun j => ih (fun k hk => hshape k (by omega)) s.tail j)
    simp only [simulationBridgeState, hz, simulationReluPolynomial,
      simulationAffinePolynomial_shape_congr _ _ (hshape t (by omega)).1
        (hshape t (by omega)).2]

-- @node: simulationBridgeTests_shape_congr
/-- For [two layer sequences](hyp:layers,other), [an activation schedule](hyp:activate),
[polynomial sample inputs](hyp:z), and [a depth t](hyp:t), suppose [the layer
dimensions agree before t](hyp:hshape). At [layer k](hyp:k) [before t](hyp:hk),
for [a sign history](hyp:s), [the two bridge comparison tests are identical](goal). -/
lemma simulationBridgeTests_shape_congr {m w : ℕ} (layers other : ℕ → AffineLayer)
    (activate : ℕ → Bool) (z : Fin m → ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ)
    (t : ℕ) (hshape : ∀ k < t, (layers k).input = (other k).input ∧
      (layers k).output = (other k).output) (k : ℕ) (hk : k < t)
    (s : List (Fin m × Fin w → Bool × Bool)) :
    simulationBridgeTests layers activate z k s = simulationBridgeTests other activate z k s := by
  funext aj
  have hz : simulationBridgeState layers activate z k s aj.1 =
      simulationBridgeState other activate z k s aj.1 :=
    funext (simulationBridgeState_shape_congr layers other activate z k
      (fun r hr => hshape r (hr.trans hk)) s aj.1)
  simp only [simulationBridgeTests, hz,
    simulationAffinePolynomial_shape_congr _ _ (hshape k hk).1 (hshape k hk).2]

-- @node: simulationSameGeneratorShape
/-- [Shape agreement](goal) of [two three-part generators](hyp:q,r) means that,
for every component, [their first network blocks have the same stored shapes](step:1)
and [their second network blocks have the same stored shapes](step:2). -/
def simulationSameGeneratorShape {n d : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q r : ThreePartGenerator n d dC W1 L1 W2 L2 tau) : Prop :=
  ∀ i, simulationSameNetworkShape (q.g1 i) (r.g1 i) ∧
    simulationSameNetworkShape (q.g2 i) (r.g2 i)

-- @node: simulationGeneratorHistoryTests_shape_congr
/-- For [two generators](hyp:q,r) with [the same stored shapes](hyp:h) and
[a common latent sample](hyp:sample), [all polynomial history tests coincide](goal). -/
lemma simulationGeneratorHistoryTests_shape_congr {n d m w : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q r : ThreePartGenerator n d dC W1 L1 W2 L2 tau)
    (h : simulationSameGeneratorShape q r)
    (sample : Fin m → (Fin n → ℝ) × (Fin n → ℝ)) :
    simulationGeneratorHistoryTests q sample w = simulationGeneratorHistoryTests r sample w := by
  funext k s iaj
  unfold simulationGeneratorHistoryTests
  split_ifs with hk
  · rw [simulationBridgeTests_shape_congr _ _ _ _ (L1 + L2 + 2)
      (simulationTwoBlockLayers_shape_congr _ _ _ _ (h iaj.1).1 (h iaj.1).2) k hk]
  · rfl

-- @node: simulationGeneratorHistoryComponentPolynomial_shape_congr
/-- For [two generators](hyp:q,r) with [the same stored shapes](hyp:h),
[a latent sample](hyp:sample), and [a sign history](hyp:s), the polynomial for
[component i](hyp:i), [sample a](hyp:a), and [output coordinate j](hyp:j)
[is the same for both generators](goal). -/
lemma simulationGeneratorHistoryComponentPolynomial_shape_congr
    {n d m w : ℕ} {dC : Fin n → ℕ} {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q r : ThreePartGenerator n d dC W1 L1 W2 L2 tau)
    (h : simulationSameGeneratorShape q r)
    (sample : Fin m → (Fin n → ℝ) × (Fin n → ℝ))
    (s : List (Fin n × (Fin m × Fin w) → Bool × Bool)) (i : Fin n) (a : Fin m) (j : Fin d) :
    simulationGeneratorHistoryComponentPolynomial q sample s i a j =
      simulationGeneratorHistoryComponentPolynomial r sample s i a j := by
  unfold simulationGeneratorHistoryComponentPolynomial
  rw [simulationBridgeState_shape_congr _ _ _ _ (L1 + L2 + 2)
    (simulationTwoBlockLayers_shape_congr _ _ _ _ (h i).1 (h i).2)]

-- @node: simulationGeneratorHistoryGridPolynomial_shape_congr
/-- For [two generators](hyp:q,r) with [the same stored shapes](hyp:h),
[a latent sample](hyp:sample), [selected sample and output coordinates](hyp:coord),
[comparison thresholds](hyp:threshold), and [a sign history](hyp:s),
[the grid comparison polynomials coincide](goal). -/
lemma simulationGeneratorHistoryGridPolynomial_shape_congr
    {n d m w : ℕ} {J : Type*} {dC : Fin n → ℕ} {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q r : ThreePartGenerator n d dC W1 L1 W2 L2 tau)
    (h : simulationSameGeneratorShape q r)
    (sample : Fin m → (Fin n → ℝ) × (Fin n → ℝ))
    (coord : J → Fin m × Fin d) (threshold : J → ℝ)
    (s : List (Fin n × (Fin m × Fin w) → Bool × Bool)) :
    simulationGeneratorHistoryGridPolynomial q sample coord threshold s =
      simulationGeneratorHistoryGridPolynomial r sample coord threshold s := by
  funext j
  simp only [simulationGeneratorHistoryGridPolynomial,
    simulationGeneratorHistoryComponentPolynomial_shape_congr q r h]

/-- For [a prototype and a target generator](hyp:q,r) with [the same stored
shapes](hyp:h), [a latent sample](hyp:sample), [selected sample and output
coordinates](hyp:coord), [thresholds](hyp:threshold), and [a width cap w](hyp:w),
assume [w is at least one](hyp:hw), [the output dimension is at most w](hyp:hd),
[all component input dimensions are at most w](hyp:hC), [the first block width
is at most w](hyp:hW1), and [the second block width is at most w](hyp:hW2).
Then [replaying the prototype's history polynomials at the target's parameters
gives exactly the target's weak and strict threshold comparison bits](goal). -/
-- @node: simulationGenerator_grid_pattern_same_shape
lemma simulationGenerator_grid_pattern_same_shape {n d m : ℕ} {J : Type*}
    {dC : Fin n → ℕ} {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q r : ThreePartGenerator n d dC W1 L1 W2 L2 tau)
    (h : simulationSameGeneratorShape q r)
    (sample : Fin m → (Fin n → ℝ) × (Fin n → ℝ))
    (coord : J → Fin m × Fin d) (threshold : J → ℝ) (w : ℕ)
    (hw : 1 ≤ w) (hd : d ≤ w) (hC : ∀ i, dC i ≤ w) (hW1 : W1 ≤ w) (hW2 : W2 ≤ w) :
    polynomialComparisonPattern
      (simulationGeneratorHistoryGridPolynomial q sample coord threshold
        (simulationLayerPatternHistory (simulationGeneratorHistoryTests q sample w)
          (simulationGeneratorParameters r) (L1 + L2 + 2))) (simulationGeneratorParameters r) =
      fun j => (decide ((r.eval (sample (coord j).1)).ofLp (coord j).2 ≤ threshold j),
        decide ((r.eval (sample (coord j).1)).ofLp (coord j).2 < threshold j)) := by
  rw [simulationGeneratorHistoryTests_shape_congr q r h sample,
    simulationGeneratorHistoryGridPolynomial_shape_congr q r h]
  funext j
  obtain ⟨hle, hlt⟩ := simulationGeneratorHistoryGridPolynomial_actual
    r sample coord threshold w hw hd hC hW1 hW2 j
  simp only [polynomialComparisonPattern, ← hle, ← hlt]

-- @node: simulationGenerator_same_shape_grid_patterns_encard_le
/-- For [a prototype generator](hyp:q), [a latent sample](hyp:sample),
[selected sample and output coordinates](hyp:coord), [thresholds](hyp:threshold),
and [a width cap w](hyp:w), assume [w is at least one](hyp:hw), [the output
dimension is at most w](hyp:hd), [all component input dimensions are at most
w](hyp:hC), [the first block width is at most w](hyp:hW1), and [the second
block width is at most w](hyp:hW2). Then [the number of weak and strict
comparison patterns among generators sharing the prototype's shapes is at most
$(8(nmw+|J|)(L_1+L_2+3)+5)^{(n+nw(w+1)+2)(L_1+L_2+3)^2}$](goal). -/
lemma simulationGenerator_same_shape_grid_patterns_encard_le
    {n d m : ℕ} {J : Type*} [Fintype J] {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau)
    (sample : Fin m → (Fin n → ℝ) × (Fin n → ℝ))
    (coord : J → Fin m × Fin d) (threshold : J → ℝ) (w : ℕ)
    (hw : 1 ≤ w) (hd : d ≤ w) (hC : ∀ i, dC i ≤ w) (hW1 : W1 ≤ w) (hW2 : W2 ≤ w) :
    {s | ∃ r : ThreePartGenerator n d dC W1 L1 W2 L2 tau,
      simulationSameGeneratorShape q r ∧ (fun j =>
        (decide ((r.eval (sample (coord j).1)).ofLp (coord j).2 ≤ threshold j),
          decide ((r.eval (sample (coord j).1)).ofLp (coord j).2 < threshold j))) = s}.encard ≤
      ((8 * (n * (m * w) + Fintype.card J) * (L1 + L2 + 3) + 5) ^
        ((n + n * (w * (w + 1)) + 2) * (L1 + L2 + 3) ^ 2) : ℕ) := by
  apply (Set.encard_mono (b := Set.range (fun theta => polynomialComparisonPattern
      (simulationGeneratorHistoryGridPolynomial q sample coord threshold
        (simulationLayerPatternHistory (simulationGeneratorHistoryTests q sample w)
          theta (L1 + L2 + 2))) theta)) ?_).trans
    ((simulationGeneratorHistory_grid_patterns_encard_le
      q sample coord threshold w hw hd hC hW1 hW2).trans
        (by exact_mod_cast (simulationGenerator_history_bound_le_depth_square
          n m w (Fintype.card J) (L1 + L2 + 2))))
  rintro s ⟨r, hr, rfl⟩
  exact ⟨simulationGeneratorParameters r,
    simulationGenerator_grid_pattern_same_shape q r hr sample coord threshold w hw hd hC hW1 hW2⟩

-- @node: simulationGeneratorShapeSpace
/-- For [n generator components](hyp:n), [first block depth L₁](hyp:L1),
[second block depth L₂](hyp:L2), and [width cap w](hyp:w), [the generator shape
space](goal) assigns each component a pair of network shape codes, one for each block. -/
abbrev simulationGeneratorShapeSpace (n L1 L2 w : ℕ) :=
  Fin n → simulationNetworkShapeSpace L1 w × simulationNetworkShapeSpace L2 w

-- @node: simulationGeneratorShapeCode
/-- For [a generator](hyp:q) and [a width cap w](hyp:w), with [w at least
one](hyp:hw), [all component input dimensions at most w](hyp:hC), [the first
block width at most w](hyp:hW1), and [the second block width at most w](hyp:hW2),
[its shape code](goal) records the pair of stored network shape codes at every component. -/
def simulationGeneratorShapeCode {n d : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau) (w : ℕ)
    (hw : 1 ≤ w) (hC : ∀ i, dC i ≤ w) (hW1 : W1 ≤ w) (hW2 : W2 ≤ w) :
    simulationGeneratorShapeSpace n L1 L2 w :=
  fun i => (simulationNetworkShapeCode (q.g1 i) w hw hW1,
    simulationNetworkShapeCode (q.g2 i) w (hC i) hW2)

-- @node: simulationGeneratorShapeCode_eq_iff
/-- For [two generators](hyp:q,r) and [a width cap w](hyp:w), assume [w is at
least one](hyp:hw), [all component input dimensions are at most w](hyp:hC),
[the first block width is at most w](hyp:hW1), and [the second block width is
at most w](hyp:hW2). Then [their shape codes agree if and only if both network
blocks have the same stored shapes in every component](goal). -/
lemma simulationGeneratorShapeCode_eq_iff {n d : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q r : ThreePartGenerator n d dC W1 L1 W2 L2 tau) (w : ℕ)
    (hw : 1 ≤ w) (hC : ∀ i, dC i ≤ w) (hW1 : W1 ≤ w) (hW2 : W2 ≤ w) :
    simulationGeneratorShapeCode q w hw hC hW1 hW2 =
      simulationGeneratorShapeCode r w hw hC hW1 hW2 ↔ simulationSameGeneratorShape q r := by
  constructor
  · intro h i
    have hi := congrFun h i
    exact ⟨(simulationNetworkShapeCode_eq_iff _ _ w hw hW1).mp (congrArg Prod.fst hi),
      (simulationNetworkShapeCode_eq_iff _ _ w (hC i) hW2).mp (congrArg Prod.snd hi)⟩
  · intro h
    funext i
    exact Prod.ext ((simulationNetworkShapeCode_eq_iff _ _ w hw hW1).mpr (h i).1)
      ((simulationNetworkShapeCode_eq_iff _ _ w (hC i) hW2).mpr (h i).2)

-- @node: simulationGeneratorShapeSpace_card
/-- For [n components](hyp:n), [first block depth L₁](hyp:L1), [second block
depth L₂](hyp:L2), and [width cap w](hyp:w), [the shape space contains exactly
$(w+1)^{n(2(L_1+L_2)+2)}$ codes](goal). -/
lemma simulationGeneratorShapeSpace_card (n L1 L2 w : ℕ) :
    Fintype.card (simulationGeneratorShapeSpace n L1 L2 w) =
      (w + 1) ^ (n * (2 * (L1 + L2) + 2)) := by
  rw [Fintype.card_fun, Fintype.card_prod, simulationNetworkShapeSpace_card,
    simulationNetworkShapeSpace_card, Fintype.card_fin, ← pow_add, ← pow_mul]
  congr 1
  ring

/-- For [a generator readout](hyp:f) and [a width cap w](hyp:w), assume [w is
at least one](hyp:hw), [all component input dimensions are at most w](hyp:hC),
[the first block width is at most w](hyp:hW1), and [the second block width is
at most w](hyp:hW2). If [N is a bound per shape](hyp:N) and [every fixed-shape
class produces at most N readout values](hyp:hf), then [the full readout range
has at most $(w+1)^{n(2(L_1+L_2)+2)}N$ values](goal). -/
-- @node: simulationGenerator_shape_union_encard_le
lemma simulationGenerator_shape_union_encard_le {n d : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ} {A : Type*}
    (f : ThreePartGenerator n d dC W1 L1 W2 L2 tau → A) (w : ℕ)
    (hw : 1 ≤ w) (hC : ∀ i, dC i ≤ w) (hW1 : W1 ≤ w) (hW2 : W2 ≤ w)
    (N : ℕ)
    (hf : ∀ q : ThreePartGenerator n d dC W1 L1 W2 L2 tau,
      {s | ∃ r : ThreePartGenerator n d dC W1 L1 W2 L2 tau,
        simulationSameGeneratorShape q r ∧ f r = s}.encard ≤ N) :
    (Set.range f).encard ≤ ((w + 1) ^ (n * (2 * (L1 + L2) + 2)) * N : ℕ) := by
  classical
  let S : simulationGeneratorShapeSpace n L1 L2 w → Set A := fun c =>
    {s | ∃ r : ThreePartGenerator n d dC W1 L1 W2 L2 tau,
      simulationGeneratorShapeCode r w hw hC hW1 hW2 = c ∧ f r = s}
  have hS (c) : (S c).encard ≤ N := by
    by_cases hc : ∃ q : ThreePartGenerator n d dC W1 L1 W2 L2 tau,
        simulationGeneratorShapeCode q w hw hC hW1 hW2 = c
    · obtain ⟨q, hq⟩ := hc
      apply (Set.encard_mono (b := {s | ∃ r : ThreePartGenerator n d dC W1 L1 W2 L2 tau,
        simulationSameGeneratorShape q r ∧ f r = s}) ?_).trans (hf q)
      rintro s ⟨r, hr, hs⟩
      exact ⟨r, (simulationGeneratorShapeCode_eq_iff q r w hw hC hW1 hW2).mp
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
      exact Set.mem_iUnion.mpr ⟨simulationGeneratorShapeCode r w hw hC hW1 hW2, r, rfl, rfl⟩
    _ ≤ ∑ c, (S c).encard := Set.encard_iUnion_le_of_fintype S
    _ ≤ ∑ _c : simulationGeneratorShapeSpace n L1 L2 w, (N : ℕ∞) :=
      Finset.sum_le_sum (fun c _ => hS c)
    _ = ((w + 1) ^ (n * (2 * (L1 + L2) + 2)) * N : ℕ) := by
      rw [Finset.sum_const, Finset.card_univ, simulationGeneratorShapeSpace_card, nsmul_eq_mul]
      simp only [Nat.cast_mul]

-- @node: simulationGenerator_all_shapes_grid_patterns_encard_le
/-- For [a latent sample](hyp:sample), [selected sample and output
coordinates](hyp:coord), [thresholds](hyp:threshold), and [a width cap w](hyp:w),
assume [w is at least one](hyp:hw), [the output dimension is at most w](hyp:hd),
[all component input dimensions are at most w](hyp:hC), [the first block width
is at most w](hyp:hW1), and [the second block width is at most w](hyp:hW2).
Then [the number of weak and strict comparison patterns over all generator
shapes is at most $(w+1)^{n(2(L_1+L_2)+2)}$ times
$(8(nmw+|J|)(L_1+L_2+3)+5)^{(n+nw(w+1)+2)(L_1+L_2+3)^2}$](goal). -/
lemma simulationGenerator_all_shapes_grid_patterns_encard_le
    {n d m : ℕ} {J : Type*} [Fintype J] {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (sample : Fin m → (Fin n → ℝ) × (Fin n → ℝ))
    (coord : J → Fin m × Fin d) (threshold : J → ℝ) (w : ℕ)
    (hw : 1 ≤ w) (hd : d ≤ w) (hC : ∀ i, dC i ≤ w) (hW1 : W1 ≤ w) (hW2 : W2 ≤ w) :
    (Set.range (fun r : ThreePartGenerator n d dC W1 L1 W2 L2 tau => fun j =>
      (decide ((r.eval (sample (coord j).1)).ofLp (coord j).2 ≤ threshold j),
        decide ((r.eval (sample (coord j).1)).ofLp (coord j).2 < threshold j)))).encard ≤
      ((w + 1) ^ (n * (2 * (L1 + L2) + 2)) *
        (8 * (n * (m * w) + Fintype.card J) * (L1 + L2 + 3) + 5) ^
          ((n + n * (w * (w + 1)) + 2) * (L1 + L2 + 3) ^ 2) : ℕ) := by
  apply simulationGenerator_shape_union_encard_le _ w hw hC hW1 hW2
  intro q
  exact simulationGenerator_same_shape_grid_patterns_encard_le
    q sample coord threshold w hw hd hC hW1 hW2

/-- For [a latent sample](hyp:sample), [selected sample and output
coordinates](hyp:coord), [thresholds](hyp:threshold), [clipping level K](hyp:K),
[a fixed decoder of comparison bits](hyp:decode), [an allowed generator
class](hyp:allowed), and [a width cap w](hyp:w), assume [w is at least
one](hyp:hw), [the output dimension is at most w](hyp:hd), [all component input
dimensions are at most w](hyp:hC), [the first block width is at most w](hyp:hW1),
and [the second block width is at most w](hyp:hW2). Then [the number of decoded
clipped comparison patterns is at most $(w+1)^{n(2(L_1+L_2)+2)}$ times
$(8(nmw+|J|)(L_1+L_2+3)+5)^{(n+nw(w+1)+2)(L_1+L_2+3)^2}$](goal). -/
-- @node: simulationGenerator_all_shapes_clipped_readout_encard_le
lemma simulationGenerator_all_shapes_clipped_readout_encard_le
    {n d m : ℕ} {J A : Type*} [Fintype J] {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (sample : Fin m → (Fin n → ℝ) × (Fin n → ℝ))
    (coord : J → Fin m × Fin d) (threshold : J → ℝ) (K : ℝ)
    (decode : (J → Bool × Bool) → A)
    (allowed : Set (ThreePartGenerator n d dC W1 L1 W2 L2 tau)) (w : ℕ)
    (hw : 1 ≤ w) (hd : d ≤ w) (hC : ∀ i, dC i ≤ w) (hW1 : W1 ≤ w) (hW2 : W2 ≤ w) :
    {s | ∃ r ∈ allowed, decode (fun j =>
      (decide ((truncK K (r.eval (sample (coord j).1))).ofLp (coord j).2 ≤ threshold j),
        decide ((truncK K (r.eval (sample (coord j).1))).ofLp (coord j).2 < threshold j))) =
          s}.encard ≤
      ((w + 1) ^ (n * (2 * (L1 + L2) + 2)) *
        (8 * (n * (m * w) + Fintype.card J) * (L1 + L2 + 3) + 5) ^
          ((n + n * (w * (w + 1)) + 2) * (L1 + L2 + 3) ^ 2) : ℕ) := by
  let f := fun r : ThreePartGenerator n d dC W1 L1 W2 L2 tau => fun j =>
    (decide ((r.eval (sample (coord j).1)).ofLp (coord j).2 ≤ threshold j),
      decide ((r.eval (sample (coord j).1)).ofLp (coord j).2 < threshold j))
  let clip : (J → Bool × Bool) → (J → Bool × Bool) := fun bits j =>
    (decide (-K ≤ threshold j) && (decide (K ≤ threshold j) || (bits j).1),
      decide (-K < threshold j) && (decide (K < threshold j) || (bits j).2))
  have hclip (r) : clip (f r) = fun j =>
      (decide ((truncK K (r.eval (sample (coord j).1))).ofLp (coord j).2 ≤ threshold j),
        decide ((truncK K (r.eval (sample (coord j).1))).ofLp (coord j).2 < threshold j)) := by
    funext j
    simp only [clip, f, truncK, WithLp.ofLp_toLp, max_le_iff, min_le_iff,
      max_lt_iff, min_lt_iff, Bool.decide_and, Bool.decide_or, Bool.or_comm]
  apply (Set.encard_mono (b := (decode ∘ clip) '' Set.range f) ?_).trans
    ((Set.encard_image_le _ _).trans
      (simulationGenerator_all_shapes_grid_patterns_encard_le
        sample coord threshold w hw hd hC hW1 hW2))
  rintro s ⟨r, _, rfl⟩
  exact ⟨f r, ⟨r, rfl⟩, congrArg decode (hclip r)⟩

-- @node: simulationGenerator_shape_bound_le_depth_square
/-- For [component count n](hyp:n), [sample size m](hyp:m), [width cap w](hyp:w),
[comparison count J](hyp:J), and [block depths L₁ and L₂](hyp:L1,L2),
[the product of the shape count $(w+1)^{n(2(L_1+L_2)+2)}$ and the history bound
$(8(nmw+J)(L_1+L_2+3)+5)^{(n+nw(w+1)+2)(L_1+L_2+3)^2}$ is at most
$(8(nmw+J)(L_1+L_2+3)+w+6)^{(3n+nw(w+1)+2)(L_1+L_2+3)^2}$](goal). -/
lemma simulationGenerator_shape_bound_le_depth_square (n m w J L1 L2 : ℕ) :
    (w + 1) ^ (n * (2 * (L1 + L2) + 2)) *
      (8 * (n * (m * w) + J) * (L1 + L2 + 3) + 5) ^
        ((n + n * (w * (w + 1)) + 2) * (L1 + L2 + 3) ^ 2) ≤
    (8 * (n * (m * w) + J) * (L1 + L2 + 3) + w + 6) ^
      ((3 * n + n * (w * (w + 1)) + 2) * (L1 + L2 + 3) ^ 2) := by
  let B := 8 * (n * (m * w) + J) * (L1 + L2 + 3) + w + 6
  have hshape : w + 1 ≤ B := by dsimp [B]; omega
  have hbase : 8 * (n * (m * w) + J) * (L1 + L2 + 3) + 5 ≤ B := by dsimp [B]; omega
  have he : n * (2 * (L1 + L2) + 2) +
      (n + n * (w * (w + 1)) + 2) * (L1 + L2 + 3) ^ 2 ≤
      (3 * n + n * (w * (w + 1)) + 2) * (L1 + L2 + 3) ^ 2 := by
    have h : 2 * (L1 + L2) + 2 ≤ 2 * (L1 + L2 + 3) ^ 2 := by nlinarith
    nlinarith [Nat.mul_le_mul_left n h]
  calc
    _ ≤ B ^ (n * (2 * (L1 + L2) + 2)) *
        B ^ ((n + n * (w * (w + 1)) + 2) * (L1 + L2 + 3) ^ 2) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hshape _) (Nat.pow_le_pow_left hbase _)
    _ = B ^ (n * (2 * (L1 + L2) + 2) +
        (n + n * (w * (w + 1)) + 2) * (L1 + L2 + 3) ^ 2) := (pow_add ..).symm
    _ ≤ _ := Nat.pow_le_pow_right (by dsimp [B]; omega) he

-- @node: simulationGenerator_all_shapes_clipped_readout_depth_square
/-- For [a latent sample](hyp:sample), [selected sample and output
coordinates](hyp:coord), [thresholds](hyp:threshold), [clipping level K](hyp:K),
[a decoder](hyp:decode), [an allowed generator class](hyp:allowed), and [a width
cap w](hyp:w), assume [w is at least one](hyp:hw), [the output dimension is at
most w](hyp:hd), [all component input dimensions are at most w](hyp:hC),
[the first block width is at most w](hyp:hW1), and [the second block width is
at most w](hyp:hW2). Then [the number of decoded clipped comparison patterns
is at most $(8(nmw+|J|)(L_1+L_2+3)+w+6)^{(3n+nw(w+1)+2)(L_1+L_2+3)^2}$](goal). -/
lemma simulationGenerator_all_shapes_clipped_readout_depth_square
    {n d m : ℕ} {J A : Type*} [Fintype J] {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (sample : Fin m → (Fin n → ℝ) × (Fin n → ℝ))
    (coord : J → Fin m × Fin d) (threshold : J → ℝ) (K : ℝ)
    (decode : (J → Bool × Bool) → A)
    (allowed : Set (ThreePartGenerator n d dC W1 L1 W2 L2 tau)) (w : ℕ)
    (hw : 1 ≤ w) (hd : d ≤ w) (hC : ∀ i, dC i ≤ w) (hW1 : W1 ≤ w) (hW2 : W2 ≤ w) :
    {s | ∃ r ∈ allowed, decode (fun j =>
      (decide ((truncK K (r.eval (sample (coord j).1))).ofLp (coord j).2 ≤ threshold j),
        decide ((truncK K (r.eval (sample (coord j).1))).ofLp (coord j).2 < threshold j))) =
          s}.encard ≤
      ((8 * (n * (m * w) + Fintype.card J) * (L1 + L2 + 3) + w + 6) ^
        ((3 * n + n * (w * (w + 1)) + 2) * (L1 + L2 + 3) ^ 2) : ℕ) := by
  exact (simulationGenerator_all_shapes_clipped_readout_encard_le
    sample coord threshold K decode allowed w hw hd hC hW1 hW2).trans
      (by exact_mod_cast (simulationGenerator_shape_bound_le_depth_square
        n m w (Fintype.card J) L1 L2))

-- @node: simulationJointGeneratorBits
/-- Given [a sample of paired latent inputs across blocks](hyp:sample),
[the sample and output coordinate selected for each comparison](hyp:coord),
[block-specific thresholds](hyp:threshold), [clipping level K](hyp:K), and
[one generator per block](hyp:q), [the joint generator bits](goal) record
[whether each clipped output is at most its threshold](step:1) and
[whether it is strictly below its threshold](step:2). -/
def simulationJointGeneratorBits {b m : ℕ} {counts dims : Fin b → ℕ}
    {dC : ∀ j, Fin (counts j) → ℕ} {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    {J : Fin b → Type*}
    (sample : Fin m → ∀ j, (Fin (counts j) → ℝ) × (Fin (counts j) → ℝ))
    (coord : ∀ j, J j → Fin m × Fin (dims j)) (threshold : ∀ j, J j → ℝ) (K : ℝ)
    (q : ∀ j, ThreePartGenerator (counts j) (dims j) (dC j) W1 L1 W2 L2 tau) :
    ∀ j, J j → Bool × Bool := fun j k =>
  (decide ((truncK K ((q j).eval (sample (coord j k).1 j))).ofLp (coord j k).2 ≤ threshold j k),
    decide ((truncK K ((q j).eval (sample (coord j k).1 j))).ofLp (coord j k).2 < threshold j k))

/-- For [paired latent samples across blocks](hyp:sample), [selected sample
and output coordinates](hyp:coord), [block-specific thresholds](hyp:threshold),
[clipping level K](hyp:K), and [a width cap w](hyp:w), assume [w is at least
one](hyp:hw), [all output dimensions are at most w](hyp:hd), [all component
input dimensions are at most w](hyp:hC), [the first block width is at most
w](hyp:hW1), and [the second block width is at most w](hyp:hW2). Then [the
number of joint clipped comparison patterns is at most the product over blocks j
of $(8(n_jmw+|J_j|)(L_1+L_2+3)+w+6)^{(3n_j+n_jw(w+1)+2)(L_1+L_2+3)^2}$,
where nⱼ is the component count of block j](goal). -/
-- @node: simulationJointGeneratorBits_encard_le
lemma simulationJointGeneratorBits_encard_le
    {b m : ℕ} {counts dims : Fin b → ℕ} {dC : ∀ j, Fin (counts j) → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ} {J : Fin b → Type*} [∀ j, Fintype (J j)]
    (sample : Fin m → ∀ j, (Fin (counts j) → ℝ) × (Fin (counts j) → ℝ))
    (coord : ∀ j, J j → Fin m × Fin (dims j)) (threshold : ∀ j, J j → ℝ) (K : ℝ)
    (w : ℕ) (hw : 1 ≤ w) (hd : ∀ j, dims j ≤ w)
    (hC : ∀ j i, dC j i ≤ w) (hW1 : W1 ≤ w) (hW2 : W2 ≤ w) :
    (Set.range (simulationJointGeneratorBits (L1 := L1) (L2 := L2) (tau := tau)
      (W1 := W1) (W2 := W2) (dC := dC) sample coord threshold K)).encard ≤
      (∏ j, (8 * (counts j * (m * w) + Fintype.card (J j)) * (L1 + L2 + 3) + w + 6) ^
        ((3 * counts j + counts j * (w * (w + 1)) + 2) * (L1 + L2 + 3) ^ 2) : ℕ) := by
  let f := fun j (q : ThreePartGenerator (counts j) (dims j) (dC j) W1 L1 W2 L2 tau) =>
    fun k : J j =>
      (decide ((truncK K (q.eval (sample (coord j k).1 j))).ofLp (coord j k).2 ≤ threshold j k),
        decide ((truncK K (q.eval (sample (coord j k).1 j))).ofLp (coord j k).2 < threshold j k))
  have hj (j : Fin b) : (Set.range (f j)).encard ≤
      ((8 * (counts j * (m * w) + Fintype.card (J j)) * (L1 + L2 + 3) + w + 6) ^
        ((3 * counts j + counts j * (w * (w + 1)) + 2) * (L1 + L2 + 3) ^ 2) : ℕ) := by
    have h := simulationGenerator_all_shapes_clipped_readout_depth_square
      (L1 := L1) (L2 := L2) (tau := tau) (W1 := W1) (W2 := W2) (dC := dC j)
      (fun a => sample a j) (coord j) (threshold j) K id Set.univ
      w hw (hd j) (hC j) hW1 hW2
    convert h using 1
    congr 1
    ext s
    simp [f]
  have hsub : Set.range (simulationJointGeneratorBits (L1 := L1) (L2 := L2) (tau := tau)
      (W1 := W1) (W2 := W2) (dC := dC) sample coord threshold K) ⊆
      Set.pi Set.univ (fun j => Set.range (f j)) := by
    rintro _ ⟨q, rfl⟩ j _
    exact ⟨q j, rfl⟩
  apply (Set.encard_mono hsub).trans
  rw [Set.encard_pi_eq_prod_encard, Nat.cast_prod]
  exact Finset.prod_le_prod' (fun j _ => hj j)

/-- For [paired latent samples](hyp:sample), [selected sample and output
coordinates](hyp:coord), [thresholds](hyp:threshold), [clipping level K](hyp:K),
[width cap w](hyp:w), [component cap N](hyp:N), and [comparison cap Q](hyp:Q),
assume [w is at least one](hyp:hw), [all output dimensions are at most w](hyp:hd),
[all component input dimensions are at most w](hyp:hC), [the first block width
is at most w](hyp:hW1), [the second block width is at most w](hyp:hW2),
[each block has at most N components](hyp:hN), and [each block has at most Q
comparisons](hyp:hQ). Then [the number of joint clipped comparison patterns
across b blocks is at most
$(8(Nmw+Q)(L_1+L_2+3)+w+6)^{b(3N+Nw(w+1)+2)(L_1+L_2+3)^2}$](goal). -/
-- @node: simulationJointGeneratorBits_uniform_encard_le
lemma simulationJointGeneratorBits_uniform_encard_le
    {b m : ℕ} {counts dims : Fin b → ℕ} {dC : ∀ j, Fin (counts j) → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ} {J : Fin b → Type*} [∀ j, Fintype (J j)]
    (sample : Fin m → ∀ j, (Fin (counts j) → ℝ) × (Fin (counts j) → ℝ))
    (coord : ∀ j, J j → Fin m × Fin (dims j)) (threshold : ∀ j, J j → ℝ) (K : ℝ)
    (w N Q : ℕ) (hw : 1 ≤ w) (hd : ∀ j, dims j ≤ w)
    (hC : ∀ j i, dC j i ≤ w) (hW1 : W1 ≤ w) (hW2 : W2 ≤ w)
    (hN : ∀ j, counts j ≤ N) (hQ : ∀ j, Fintype.card (J j) ≤ Q) :
    (Set.range (simulationJointGeneratorBits (L1 := L1) (L2 := L2) (tau := tau)
      (W1 := W1) (W2 := W2) (dC := dC) sample coord threshold K)).encard ≤
      ((8 * (N * (m * w) + Q) * (L1 + L2 + 3) + w + 6) ^
        (b * (3 * N + N * (w * (w + 1)) + 2) * (L1 + L2 + 3) ^ 2) : ℕ) := by
  apply (simulationJointGeneratorBits_encard_le sample coord threshold K w hw hd hC hW1 hW2).trans
  apply Nat.cast_le.mpr
  calc
    _ ≤ ∏ _j : Fin b, (8 * (N * (m * w) + Q) * (L1 + L2 + 3) + w + 6) ^
        ((3 * N + N * (w * (w + 1)) + 2) * (L1 + L2 + 3) ^ 2) := by
      apply Finset.prod_le_prod'
      intro j _
      calc
        _ ≤ (8 * (N * (m * w) + Q) * (L1 + L2 + 3) + w + 6) ^
            ((3 * counts j + counts j * (w * (w + 1)) + 2) * (L1 + L2 + 3) ^ 2) :=
          Nat.pow_le_pow_left (by gcongr <;> first | exact hN j | exact hQ j) _
        _ ≤ _ := Nat.pow_le_pow_right (by omega) (by gcongr <;> exact hN j)
    _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]; congr 1; ring

/-- For [paired latent samples](hyp:sample), [selected sample and output
coordinates](hyp:coord), [thresholds](hyp:threshold), [clipping level K](hyp:K),
[width cap w](hyp:w), [component cap N](hyp:N), and [comparison cap Q](hyp:Q),
assume [w is at least one](hyp:hw), [all output dimensions are at most w](hyp:hd),
[all component input dimensions are at most w](hyp:hC), [the first block width
is at most w](hyp:hW1), [the second block width is at most w](hyp:hW2),
[each block has at most N components](hyp:hN), and [each block has at most Q
comparisons](hyp:hQ). Given [a finite table collection](hyp:tables), [a family
of sample subsets](hyp:family), [a rule selecting sample indices from a table,
joint comparison bits, and a type subset](hyp:indicator), and [a rule selecting
ambiguous sample indices from a table and joint bits](hyp:ambiguity), if [every
family member is encoded by one of these two rules using an available table
and some generators](hyp:hencode), then [the family size is at most the number
of tables times $(8(Nmw+Q)(L_1+L_2+3)+w+6)^{b(3N+Nw(w+1)+2)(L_1+L_2+3)^2}$
times one plus the number of type subsets](goal). -/
-- @node: simulation_joint_generator_table_patterns_card_le
lemma simulation_joint_generator_table_patterns_card_le
    {b m : ℕ} {counts dims : Fin b → ℕ} {dC : ∀ j, Fin (counts j) → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ} {J : Fin b → Type*} [∀ j, Fintype (J j)]
    {T Types : Type*} [Fintype Types]
    (sample : Fin m → ∀ j, (Fin (counts j) → ℝ) × (Fin (counts j) → ℝ))
    (coord : ∀ j, J j → Fin m × Fin (dims j)) (threshold : ∀ j, J j → ℝ) (K : ℝ)
    (w N Q : ℕ) (hw : 1 ≤ w) (hd : ∀ j, dims j ≤ w)
    (hC : ∀ j i, dC j i ≤ w) (hW1 : W1 ≤ w) (hW2 : W2 ≤ w)
    (hN : ∀ j, counts j ≤ N) (hQ : ∀ j, Fintype.card (J j) ≤ Q)
    (tables : Finset T) (family : Finset (Finset (Fin m)))
    (indicator : T → (∀ j, J j → Bool × Bool) → Finset Types → Finset (Fin m))
    (ambiguity : T → (∀ j, J j → Bool × Bool) → Finset (Fin m))
    (hencode : ∀ a ∈ family, ∃ t ∈ tables,
      ∃ q : ∀ j, ThreePartGenerator (counts j) (dims j) (dC j) W1 L1 W2 L2 tau,
        (∃ s, indicator t (simulationJointGeneratorBits sample coord threshold K q) s = a) ∨
          ambiguity t (simulationJointGeneratorBits sample coord threshold K q) = a) :
    family.card ≤ tables.card *
      (8 * (N * (m * w) + Q) * (L1 + L2 + 3) + w + 6) ^
        (b * (3 * N + N * (w * (w + 1)) + 2) * (L1 + L2 + 3) ^ 2) *
          (2 ^ Fintype.card Types + 1) := by
  classical
  let S := Set.range (simulationJointGeneratorBits (L1 := L1) (L2 := L2) (tau := tau)
    (W1 := W1) (W2 := W2) (dC := dC) sample coord threshold K)
  have hbound := simulationJointGeneratorBits_uniform_encard_le
    (L1 := L1) (L2 := L2) (tau := tau) sample coord threshold K w N Q hw hd hC hW1 hW2 hN hQ
  have hfinite : S.Finite := Set.finite_of_encard_le_coe hbound
  have hcard : hfinite.toFinset.card ≤
      (8 * (N * (m * w) + Q) * (L1 + L2 + 3) + w + 6) ^
        (b * (3 * N + N * (w * (w + 1)) + 2) * (L1 + L2 + 3) ^ 2) := by
    have h : S.encard ≤ _ := hbound
    rw [hfinite.encard_eq_coe_toFinset_card] at h
    exact_mod_cast h
  have h := simulation_table_patterns_card_le tables hfinite.toFinset family indicator ambiguity (by
    intro a ha
    obtain ⟨t, ht, q, hq⟩ := hencode a ha
    exact ⟨t, ht, _, hfinite.mem_toFinset.mpr ⟨q, rfl⟩, hq⟩)
  exact h.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hcard))

end
end Papers.TbsNeuralCausalPi
