module
public import Papers.TbsNeuralCausalPi.Helpers.SimulationGeneratorShapes
public import Papers.TbsNeuralCausalPi.Helpers.SimulationCubeGrid
public import Papers.TbsNeuralCausalPi.Helpers.SimulationTableAmbiguity
public import Papers.TbsNeuralCausalPi.Helpers.FixedLabelStrata
public import Papers.TbsNeuralCausalPi.Setup.Optimization
/-! # Actual latent grid patterns from generator comparisons

Finite scalar thresholds recover the occupied floor cell exactly, including
its boundaries. The established polynomial comparison count therefore bounds
joint latent grid patterns over all generator weights and stored shapes.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open scoped NNReal
noncomputable section

-- @node: simulation_floor_eq_of_thresholds
/-- If [x is nonnegative](hyp:hx), [y is nonnegative](hyp:hy), [the floor of x
is less than N](hyp:hxN), [the floor of y is less than N](hyp:hyN), and [x and y
give the same strict comparisons with every integer from zero through N minus
one](hyp:h), then [their floors are equal](goal). -/
lemma simulation_floor_eq_of_thresholds {x y : ℝ} {N : ℕ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxN : ⌊x⌋₊ < N) (hyN : ⌊y⌋₊ < N)
    (h : ∀ k : Fin N, x < (k : ℕ) ↔ y < (k : ℕ)) : ⌊x⌋₊ = ⌊y⌋₊ := by
  apply le_antisymm
  · by_contra hle
    have hlt : ⌊y⌋₊ < ⌊x⌋₊ := Nat.lt_of_not_ge hle
    have hxlt := (h ⟨⌊x⌋₊, hxN⟩).mpr ((Nat.floor_lt hy).mp hlt)
    exact (lt_irrefl ⌊x⌋₊) ((Nat.floor_lt hx).mpr hxlt)
  · by_contra hle
    have hlt : ⌊x⌋₊ < ⌊y⌋₊ := Nat.lt_of_not_ge hle
    have hylt := (h ⟨⌊y⌋₊, hyN⟩).mp ((Nat.floor_lt hx).mp hlt)
    exact (lt_irrefl ⌊y⌋₊) ((Nat.floor_lt hy).mpr hylt)

-- @node: simulationLatentGridIndex
/-- For [a grid offset K](hyp:K), [a grid spacing](hyp:step) and [a vector of
latent blocks](hyp:x), [the latent grid index](goal) assigns each coordinate the
nonnegative integer floor of its value plus K divided by the spacing. -/
def simulationLatentGridIndex {b : ℕ} {dims : Fin b → ℕ}
    (K step : ℝ) (x : Latent dims) : ∀ j, Fin (dims j) → ℕ :=
  fun j i => ⌊(x.ofLp ⟨j, i⟩ + K) / step⌋₊

-- @node: simulationGeneratorGridBits
/-- Given [a sample of paired noise vectors for each block](hyp:sample), [a
clipping level K](hyp:K), [a grid spacing](hyp:step) and [one three-part generator
for each block](hyp:q), [the grid comparison bits](goal) record both weak and
strict comparisons of every clipped output coordinate on every draw against
thresholds k times the spacing minus K, for integers k from zero through the
nonnegative integer floor of twice K divided by the spacing. -/
def simulationGeneratorGridBits {b m : ℕ} {counts dims : Fin b → ℕ}
    {dC : ∀ j, Fin (counts j) → ℕ} {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (sample : Fin m → ∀ j, (Fin (counts j) → ℝ) × (Fin (counts j) → ℝ)) (K step : ℝ)
    (q : ∀ j, ThreePartGenerator (counts j) (dims j) (dC j) W1 L1 W2 L2 tau) :
    ∀ j, (Fin m × Fin (dims j) × Fin (⌊2 * K / step⌋₊ + 1)) → Bool × Bool :=
  simulationJointGeneratorBits sample (fun _ u => (u.1, u.2.1))
    (fun _ u => (u.2.2 : ℕ) * step - K) K q

-- @node: simulationGeneratorGridBits_determine_index
/-- On [a sample of paired noise vectors for each block](hyp:sample), with [a
nonnegative clipping level](hyp:hK) and [positive grid spacing](hyp:hstep), consider
[one family of block generators](hyp:q) and [a second family of the same
architecture](hyp:r). If [the two families give identical grid comparison
bits](hyp:hbits), then [their clipped latent outputs have identical grid indices
at every sample position](goal). -/
lemma simulationGeneratorGridBits_determine_index {b m : ℕ} {counts dims : Fin b → ℕ}
    {dC : ∀ j, Fin (counts j) → ℕ} {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (sample : Fin m → ∀ j, (Fin (counts j) → ℝ) × (Fin (counts j) → ℝ))
    {K step : ℝ} (hK : 0 ≤ K) (hstep : 0 < step)
    (q r : ∀ j, ThreePartGenerator (counts j) (dims j) (dC j) W1 L1 W2 L2 tau)
    (hbits : simulationGeneratorGridBits sample K step q = simulationGeneratorGridBits sample K step r) :
    (fun a => simulationLatentGridIndex K step (WithLp.toLp 1 (fun ji => (truncK K ((q ji.1).eval (sample a ji.1))).ofLp ji.2))) =
      (fun a => simulationLatentGridIndex K step (WithLp.toLp 1 (fun ji => (truncK K ((r ji.1).eval (sample a ji.1))).ofLp ji.2))) := by
  funext a j i
  have hbound (v : L1Vec (dims j)) :
      -(K : ℝ) ≤ (truncK K v).ofLp i ∧ (truncK K v).ofLp i ≤ K := by
    exact coordinateClamp_mapsTo (-K) K (by linarith) v i
  have hfloor (v : L1Vec (dims j)) :
      ⌊((truncK K v).ofLp i + K) / step⌋₊ < ⌊2 * K / step⌋₊ + 1 := by
    apply Nat.lt_succ_of_le
    apply Nat.floor_mono
    exact div_le_div_of_nonneg_right (by linarith [(hbound v).2]) hstep.le
  apply simulation_floor_eq_of_thresholds
    (div_nonneg (by linarith [(hbound ((q j).eval (sample a j))).1]) hstep.le)
    (div_nonneg (by linarith [(hbound ((r j).eval (sample a j))).1]) hstep.le)
    (hfloor _) (hfloor _)
  intro k
  have hb := congrArg (fun f => (f j (a, i, k)).2) hbits
  simp only [simulationGeneratorGridBits, simulationJointGeneratorBits] at hb
  have hh : ((truncK K ((q j).eval (sample a j))).ofLp i < (k : ℕ) * step - K) ↔
      ((truncK K ((r j).eval (sample a j))).ofLp i < (k : ℕ) * step - K) := by
    exact decide_eq_decide.mp hb
  rw [div_lt_iff₀ hstep, div_lt_iff₀ hstep]
  constructor <;> intro h
  · have := hh.mp (by linarith)
    linarith
  · have := hh.mpr (by linarith)
    linarith

-- @node: simulationGeneratorGridIndex_encard_le
/-- On [a sample of m paired noise draws for each block](hyp:sample), suppose
[the clipping level K is nonnegative](hyp:hK), [the grid spacing is positive](hyp:hstep),
[the common width bound w is at least one](hyp:hw), [every output dimension is at
most w](hyp:hd), [every categorical dimension is at most w](hyp:hC), [the first
network width is at most w](hyp:hW1), [the second network width is at most w](hyp:hW2)
and [each block has at most N noise coordinates](hyp:hN). Then [the number of
joint grid-index patterns attainable by the block generators is at most
$(8(Nmw+mwH)D+w+6)^{b(3N+Nw(w+1)+2)D^2}$, where b is the number of blocks,
D is the sum of the two network depths plus three, and H is one plus the
nonnegative integer floor of twice K divided by the grid spacing](goal). -/
lemma simulationGeneratorGridIndex_encard_le {b m : ℕ} {counts dims : Fin b → ℕ}
    {dC : ∀ j, Fin (counts j) → ℕ} {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (sample : Fin m → ∀ j, (Fin (counts j) → ℝ) × (Fin (counts j) → ℝ))
    {K step : ℝ} (hK : 0 ≤ K) (hstep : 0 < step)
    (w N : ℕ) (hw : 1 ≤ w) (hd : ∀ j, dims j ≤ w)
    (hC : ∀ j i, dC j i ≤ w) (hW1 : W1 ≤ w) (hW2 : W2 ≤ w)
    (hN : ∀ j, counts j ≤ N) :
    (Set.range (fun (q : ∀ j, ThreePartGenerator (counts j) (dims j) (dC j) W1 L1 W2 L2 tau)
        a => simulationLatentGridIndex K step (WithLp.toLp 1 (fun ji => (truncK K ((q ji.1).eval (sample a ji.1))).ofLp ji.2)))).encard ≤
      ((8 * (N * (m * w) + m * (w * (⌊2 * K / step⌋₊ + 1))) * (L1 + L2 + 3) + w + 6) ^
        (b * (3 * N + N * (w * (w + 1)) + 2) * (L1 + L2 + 3) ^ 2) : ℕ) := by
  have hcount := simulationJointGeneratorBits_uniform_encard_le
    (L1 := L1) (L2 := L2) (tau := tau) (W1 := W1) (W2 := W2) (dC := dC)
    sample (fun j (u : Fin m × Fin (dims j) × Fin (⌊2 * K / step⌋₊ + 1)) => (u.1, u.2.1))
    (fun _ u => (u.2.2 : ℕ) * step - K) K w N (m * (w * (⌊2 * K / step⌋₊ + 1)))
    hw hd hC hW1 hW2 hN (by intro j; simp only [Fintype.card_prod, Fintype.card_fin]; gcongr; exact hd j)
  apply le_trans _ hcount
  classical
  let grid := fun (q : ∀ j, ThreePartGenerator (counts j) (dims j) (dC j) W1 L1 W2 L2 tau) a =>
    simulationLatentGridIndex K step
      (WithLp.toLp 1 (fun ji => (truncK K ((q ji.1).eval (sample a ji.1))).ofLp ji.2))
  let read := fun p : Set.range (simulationGeneratorGridBits sample K step) =>
    grid (Classical.choose p.property)
  have hsub : Set.range grid ⊆ Set.range read := by
    rintro _ ⟨q, rfl⟩
    refine ⟨⟨simulationGeneratorGridBits sample K step q, ⟨q, rfl⟩⟩, ?_⟩
    exact simulationGeneratorGridBits_determine_index sample hK hstep _ _
      (Classical.choose_spec (show ∃ r, simulationGeneratorGridBits sample K step r =
        simulationGeneratorGridBits sample K step q from ⟨q, rfl⟩))
  apply (Set.encard_mono hsub).trans
  change (Set.range read).encard ≤ (Set.range (simulationGeneratorGridBits
    (W1 := W1) (L1 := L1) (W2 := W2) (L2 := L2) (tau := tau) (dC := dC) sample K step)).encard
  simpa only [Set.image_univ, Set.encard_univ, ENat.card_coe_set_eq] using
    Set.encard_image_le read Set.univ

-- @node: ncm_simulationLatentGridIndex_encard_le
/-- For [a structural equation class](hyp:F0), [categorical dimensions for each
block's noise coordinates](hyp:dC), [a nonnegative clipping level K](hyp:K), [a
generator size dU](hyp:dU), [a first-stage width multiplier c1](hyp:c1), [a
second-stage width multiplier c2](hyp:c2), [a resolution r0](hyp:r0), [a first-stage
depth schedule](hyp:L1), [a second-stage depth schedule](hyp:L2), [a temperature
schedule](hyp:tau) and [m simulation input draws](hyp:draws), assume [positive
grid spacing](hyp:hstep), [a common width bound w of at least one](hyp:hw),
[output dimensions at most w](hyp:hd), [categorical dimensions at most w](hyp:hC),
[first-stage width c1 times dU at most w](hyp:hW1), [second-stage width c2 times
dU squared at most w](hyp:hW2) and [at most N noise coordinates per block](hyp:hN).
Then [the number of joint grid-index patterns of generated non-Gumbel latent
blocks, as neural causal representations in this class vary, is at most
$(8(Nmw+mwH)D+w+6)^{b(3N+Nw(w+1)+2)D^2}$, where b is the number of blocks,
D is the sum of the two depths at resolution r0 plus three, and H is one plus
the nonnegative integer floor of twice K divided by the grid spacing](goal). -/
lemma ncm_simulationLatentGridIndex_encard_le
    {n b m : ℕ} {kind : Fin n → NodeKind} {dims counts : Fin b → ℕ}
    {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
    {C : Fin b → Set (Fin n)} (F0 : StructuralClass kind dims dag C)
    (dC : ∀ j, Fin (counts j) → ℕ) (K : ℝ≥0) (dU c1 c2 r0 : ℕ)
    (L1 L2 : ℕ → ℕ) (tau : ℕ → ℝ)
    (draws : Fin m → SimulationInput kind counts) {step : ℝ} (hstep : 0 < step)
    (w N : ℕ) (hw : 1 ≤ w) (hd : ∀ j, dims j ≤ w)
    (hC : ∀ j i, dC j i ≤ w) (hW1 : c1 * dU ≤ w) (hW2 : c2 * dU^2 ≤ w)
    (hN : ∀ j, counts j ≤ N) :
    (Set.range (fun (R : NCMIn kind dims dag G C counts F0
        (generatorClassN counts dC K dU c1 c2 L1 L2 tau r0)) a =>
      simulationLatentGridIndex K step (jointNonGumbel (ncmSimulationExogenous R (draws a))))).encard ≤
      ((8 * (N * (m * w) + m * (w * (⌊2 * (K : ℝ) / step⌋₊ + 1))) *
        (L1 r0 + L2 r0 + 3) + w + 6) ^
        (b * (3 * N + N * (w * (w + 1)) + 2) * (L1 r0 + L2 r0 + 3) ^ 2) : ℕ) := by
  apply (Set.encard_mono ?_).trans
    (simulationGeneratorGridIndex_encard_le
      (dC := dC) (W1 := c1 * dU) (W2 := c2 * dU^2)
      (L1 := L1 r0) (L2 := L2 r0) (tau := tau r0)
      (fun a => (draws a).1) K.coe_nonneg hstep w N hw hd hC hW1 hW2 hN)
  rintro _ ⟨R, rfl⟩
  have hgen (j : Fin b) : ∃ q : ThreePartGenerator (counts j) (dims j) (dC j)
      (c1 * dU) (L1 r0) (c2 * dU^2) (L2 r0) (tau r0),
      R.generator j = truncK K ∘ q.eval := R.generatorMem j
  choose q hq using hgen
  refine ⟨q, ?_⟩
  funext a j i
  change ⌊((truncK K ((q j).eval ((draws a).1 j))).ofLp i + K) / step⌋₊ =
    ⌊((R.generator j ((draws a).1 j)).ofLp i + K) / step⌋₊
  rw [hq j]
  rfl

end
end Papers.TbsNeuralCausalPi
