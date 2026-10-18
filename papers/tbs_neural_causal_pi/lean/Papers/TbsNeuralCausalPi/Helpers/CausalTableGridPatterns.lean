module
public import Papers.TbsNeuralCausalPi.Helpers.CausalTableReadouts
public import Papers.TbsNeuralCausalPi.Helpers.CausalTableConcentration
public import Papers.TbsNeuralCausalPi.Helpers.SimulationGeneratorGridPatterns
public import Papers.TbsNeuralCausalPi.Helpers.CausalTableBorelParameters
/-! # The actual finite causal-table code inherits the generator pattern count

The cube code is a finite reindexing of the occupied floor cells. Its grid
representatives retain the deterministic approximation bound. On generated
latent vectors, clipping is the identity and this code is a fixed readout of
the raw indices already counted by the polynomial generator argument.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section

-- @node: causalTableCellEquiv
/-- For [dimension d](hyp:d), [cube radius K and mesh spacing step](hyp:K,step),
the [cell enumeration](goal) is a bijection between coordinatewise cell indices
and a single index among (floor(2K/step) + 1) raised to the power d cells. -/
def causalTableCellEquiv (d : ℕ) (K step : ℝ) :
    (Fin d → Fin (⌊2 * K / step⌋₊ + 1)) ≃ Fin ((⌊2 * K / step⌋₊ + 1) ^ d) :=
  (Fintype.equivFin _).trans (finCongr (by simp))

-- @node: causalTableCubeCode
/-- Given [cube radius K and mesh spacing step](hyp:K,step), with
[strictly positive spacing](hyp:hs), the [finite cube code](goal) assigns
[a point in the bounded cube](hyp:x) the enumerated index of its floor cell. -/
def causalTableCubeCode {d : ℕ} (K step : ℝ) (hs : 0 < step)
    (x : boundedCube d K) : Fin ((⌊2 * K / step⌋₊ + 1) ^ d) :=
  causalTableCellEquiv d K step (simulationCubeCellIndex K step hs x)

-- @node: causalTableCubeCode_measurable
/-- If [the mesh spacing is positive](hyp:hs), then
[the finite floor-cell code on the bounded cube is measurable](goal). -/
@[fun_prop] lemma causalTableCubeCode_measurable {d : ℕ}
    (K step : ℝ) (hs : 0 < step) : Measurable (causalTableCubeCode (d := d) K step hs) := by
  exact (measurable_of_finite (causalTableCellEquiv d K step)).comp
    (simulationCubeCellIndex_measurable K step hs)

-- @node: causalTableCubeGrid
/-- For [cube radius K and mesh spacing step](hyp:K,step) with
[positive spacing](hyp:hs), the [cube grid representative](goal) decodes
[a finite cell index](hyp:j) and returns its cell representative, using
[a fixed cube point as the fallback for empty cells](hyp:x0). -/
def causalTableCubeGrid {d : ℕ} (K step : ℝ) (hs : 0 < step)
    (x0 : boundedCube d K) (j : Fin ((⌊2 * K / step⌋₊ + 1) ^ d)) : boundedCube d K :=
  simulationCubeCellRepresentative K step hs x0 ((causalTableCellEquiv d K step).symm j)

-- @node: causalTableCubeGrid_error
/-- For [positive mesh spacing](hyp:hs), [the distance from any cube point to
the grid representative selected by its code is at most the dimension times
the spacing](goal), for any choice of fallback cube point. -/
lemma causalTableCubeGrid_error {d : ℕ} (K step : ℝ) (hs : 0 < step)
    (x0 x : boundedCube d K) :
    dist x.val (causalTableCubeGrid K step hs x0 (causalTableCubeCode K step hs x)).val ≤
      d * step := by
  simp only [causalTableCubeGrid, causalTableCubeCode, Equiv.symm_apply_apply]
  exact (dist_comm _ _).trans_le (simulationCubeRound_dist_le K step hs x0 x)

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

/-- For [latent block dimensions](hyp:dims), [cube radius and mesh spacing](hyp:K,step),
and [a natural cell index for each coordinate of each block](hyp:p), the
[finite index readout](goal) reduces each coordinate index modulo the number
of cells per axis and enumerates the resulting joint cell. -/
-- @node: causalTableIndexReadout
def causalTableIndexReadout (dims : Fin b → ℕ) (K step : ℝ)
    (p : ∀ j, Fin (dims j) → ℕ) : Fin ((⌊2 * K / step⌋₊ + 1) ^ (∑ j, dims j)) :=
  causalTableCellEquiv (∑ j, dims j) K step (fun i =>
    ⟨p ((jointLatentCoordinateEquiv dims).symm i).1
      ((jointLatentCoordinateEquiv dims).symm i).2 % (⌊2 * K / step⌋₊ + 1),
      Nat.mod_lt _ (Nat.succ_pos _)⟩)

/-- For [a nonnegative cube radius](hyp:K), [positive mesh spacing](hyp:hs),
and [a latent vector lying in the joint cube](hyp:hz), [coding the vector's
cube point equals applying the finite index readout to its raw floor
indices](goal), including cell boundaries and zero dimension. -/
-- @node: causalTableCubeCode_eq_indexReadout
lemma causalTableCubeCode_eq_indexReadout (K : ℝ≥0) {step : ℝ} (hs : 0 < step)
    (z : Latent dims) (hz : z ∈ jointLatentCube dims K) :
    causalTableCubeCode K step hs (simulationLatentCubePoint K z) =
      causalTableIndexReadout dims K step (simulationLatentGridIndex K step z) := by
  unfold causalTableCubeCode causalTableIndexReadout
  congr 1
  funext i
  apply Fin.ext
  change ⌊(((simulationLatentCubePoint K z).val).ofLp i + K) / step⌋₊ = _
  rw [simulationLatentCubePoint_eq_of_mem K z hz]
  change ⌊(z.ofLp ((jointLatentCoordinateEquiv dims).symm i) + K) / step⌋₊ =
    ⌊(z.ofLp ((jointLatentCoordinateEquiv dims).symm i) + K) / step⌋₊ % _
  symm
  apply Nat.mod_eq_of_lt
  apply Nat.lt_succ_of_le
  apply Nat.floor_mono
  apply div_le_div_of_nonneg_right _ hs.le
  have h := (abs_le.mp (hz ((jointLatentCoordinateEquiv dims).symm i))).2
  linarith

/-- For [component input dimensions](hyp:dC), [a nonnegative truncation radius](hyp:K),
and [positive mesh spacing](hyp:hs), suppose [the width bound is at least one](hyp:hw),
[latent block dimensions](hyp:hd), [component dimensions](hyp:hC),
[first network widths](hyp:hW1), and [second network widths](hyp:hW2) are at most w,
and [each block has at most N components](hyp:hN). Then [the number of distinct
cube-code vectors produced on the fixed draws by all generator representations
is at most the displayed comparison polynomial raised to the architecture
exponent](goal). -/
-- @node: ncm_causalTableCubeCode_patterns_encard_le
lemma ncm_causalTableCubeCode_patterns_encard_le
    {counts : Fin b → ℕ} {m : ℕ} (F0 : StructuralClass kind dims dag C)
    (dC : ∀ j, Fin (counts j) → ℕ) (K : ℝ≥0) (dU c1 c2 r0 : ℕ)
    (L1 L2 : ℕ → ℕ) (tau : ℕ → ℝ)
    (draws : Fin m → SimulationInput kind counts) {step : ℝ} (hs : 0 < step)
    (w N : ℕ) (hw : 1 ≤ w) (hd : ∀ j, dims j ≤ w)
    (hC : ∀ j i, dC j i ≤ w) (hW1 : c1 * dU ≤ w) (hW2 : c2 * dU ^ 2 ≤ w)
    (hN : ∀ j, counts j ≤ N) :
    (Set.range (fun (R : NCMIn kind dims dag G C counts F0
        (generatorClassN counts dC K dU c1 c2 L1 L2 tau r0)) a =>
      causalTableCubeCode K step hs (simulationLatentCubePoint K
        (jointNonGumbel (ncmSimulationExogenous R (draws a)))))).encard ≤
      ((8 * (N * (m * w) + m * (w * (⌊2 * (K : ℝ) / step⌋₊ + 1))) *
        (L1 r0 + L2 r0 + 3) + w + 6) ^
        (b * (3 * N + N * (w * (w + 1)) + 2) * (L1 r0 + L2 r0 + 3) ^ 2) : ℕ) := by
  let read := fun p : Fin m → (∀ j, Fin (dims j) → ℕ) =>
    fun a => causalTableIndexReadout dims K step (p a)
  have hsub : Set.range (fun (R : NCMIn kind dims dag G C counts F0
        (generatorClassN counts dC K dU c1 c2 L1 L2 tau r0)) a =>
      causalTableCubeCode K step hs (simulationLatentCubePoint K
        (jointNonGumbel (ncmSimulationExogenous R (draws a))))) ⊆
      read '' Set.range (fun (R : NCMIn kind dims dag G C counts F0
        (generatorClassN counts dC K dU c1 c2 L1 L2 tau r0)) a =>
          simulationLatentGridIndex K step
            (jointNonGumbel (ncmSimulationExogenous R (draws a)))) := by
    rintro _ ⟨R, rfl⟩
    refine ⟨_, ⟨R, rfl⟩, ?_⟩
    funext a
    exact (causalTableCubeCode_eq_indexReadout K hs _
      (generatorClassN_jointNonGumbel_mem_cube dC K dU c1 c2 L1 L2 tau r0 R _)).symm
  exact (Set.encard_mono hsub).trans ((Set.encard_image_le _ _).trans
    (ncm_simulationLatentGridIndex_encard_le F0 dC K dU c1 c2 r0 L1 L2 tau
      draws hs w N hw hd hC hW1 hW2 hN))

/-- For [component input dimensions](hyp:dC), [nonnegative truncation radius](hyp:K),
[positive mesh spacing](hyp:hs), and [a finite alphabet of categorical probability
tables](hyp:tables), assume [w is at least one](hyp:hw), [latent dimensions](hyp:hd),
[component dimensions](hyp:hC), [first network widths](hyp:hW1), and
[second network widths](hyp:hW2) are bounded by w, and [component counts are
bounded by N](hyp:hN). Then [the indicator patterns on the fixed draws number
at most the table count times the generator comparison bound times one plus
the number of subsets of cell-and-label types](goal). -/
-- @node: ncm_causalTableCubeCode_indicator_growth_card_le
lemma ncm_causalTableCubeCode_indicator_growth_card_le
    {counts : Fin b → ℕ} {m : ℕ} (F0 : StructuralClass kind dims dag C)
    (dC : ∀ j, Fin (counts j) → ℕ) (K : ℝ≥0) (dU c1 c2 r0 : ℕ)
    (L1 L2 : ℕ → ℕ) (tau : ℕ → ℝ)
    {A : Type*} (repr : A → NCMIn kind dims dag G C counts F0
      (generatorClassN counts dC K dU c1 c2 L1 L2 tau r0))
    (R0 : NCMIn kind dims dag G C counts F0
      (generatorClassN counts dC K dU c1 c2 L1 L2 tau r0))
    (draws : Fin m → SimulationInput kind counts) {step : ℝ} (hs : 0 < step)
    (tables : Finset (∀ i k, kind i = Sum.inr k → CategoricalStratum kind →
      Fin ((⌊2 * (K : ℝ) / step⌋₊ + 1) ^ (∑ j, dims j)) → probabilitySimplex k))
    (a : ℝ) (w N : ℕ) (hw : 1 ≤ w) (hd : ∀ j, dims j ≤ w)
    (hC : ∀ j i, dC j i ≤ w) (hW1 : c1 * dU ≤ w) (hW2 : c2 * dU ^ 2 ≤ w)
    (hN : ∀ j, counts j ≤ N) :
    (Causalean.Stat.Concentration.growthFamily
      (fun idx : A × tables × Option (Finset
        (Fin ((⌊2 * (K : ℝ) / step⌋₊ + 1) ^ (∑ j, dims j)) × CategoricalStratum kind)) =>
        ncmCausalTableIndicator (repr idx.1)
          (causalTableCubeCode K step hs ∘ simulationLatentCubePoint K)
          idx.2.1.val a idx.2.2) draws).card ≤
      tables.card *
        (8 * (N * (m * w) + m * (w * (⌊2 * (K : ℝ) / step⌋₊ + 1))) *
          (L1 r0 + L2 r0 + 3) + w + 6) ^
          (b * (3 * N + N * (w * (w + 1)) + 2) * (L1 r0 + L2 r0 + 3) ^ 2) *
        (2 ^ Fintype.card
          (Fin ((⌊2 * (K : ℝ) / step⌋₊ + 1) ^ (∑ j, dims j)) × CategoricalStratum kind) + 1) := by
  apply ncmCausalTableIndicator_growth_card_le_of_grid_encard repr R0
    (causalTableCubeCode K step hs ∘ simulationLatentCubePoint K) tables a draws
  apply (Set.encard_mono ?_).trans
    (ncm_causalTableCubeCode_patterns_encard_le (G := G) F0 dC K dU c1 c2 r0 L1 L2 tau
      draws hs w N hw hd hC hW1 hW2 hN)
  rintro _ ⟨r, rfl⟩
  exact ⟨repr r, rfl⟩

/-- If [the cube radius is nonnegative](hyp:hK), [the mesh radius is positive](hyp:hrho)
and [at most one](hyp:hrho1), and [the padded depth T is at least one](hyp:hT),
then [the generator comparison base for spacing rho divided by d + 1 is at
most (8w(N + 2K(d + 1) + 1) + w + 6)(m + T)T divided by rho](goal). -/
-- @node: causalTable_generator_comparison_base_le
lemma causalTable_generator_comparison_base_le (d N m w T : ℕ)
    {K rho : ℝ} (hK : 0 ≤ K) (hrho : 0 < rho) (hrho1 : rho ≤ 1) (hT : 1 ≤ T) :
    ((8 * (N * (m * w) + m * (w * (⌊2 * K / (rho / (d + 1))⌋₊ + 1))) * T + w + 6 : ℕ) : ℝ) ≤
      (8 * w * (N + 2 * K * (d + 1) + 1) + w + 6) *
        ((m : ℝ) + T) * T / rho := by
  have hd : (0 : ℝ) < d + 1 := by positivity
  have hs : 0 < rho / (d + 1) := div_pos hrho hd
  have hfloor := Nat.floor_le (show 0 ≤ 2 * K / (rho / (d + 1)) by positivity)
  have heq : 2 * K / (rho / (d + 1)) = 2 * K * (d + 1) / rho := by field_simp
  rw [heq] at hfloor
  have hf := (le_div_iff₀ hrho).mp hfloor
  have hcells : ((⌊2 * K / (rho / (d + 1))⌋₊ + 1 : ℕ) : ℝ) * rho ≤
      2 * K * (d + 1) + 1 := by push_cast; linarith
  have hN : (N : ℝ) * rho ≤ N := mul_le_of_le_one_right (Nat.cast_nonneg _) hrho1
  have hleft := mul_le_mul_of_nonneg_left hN (show 0 ≤ (m : ℝ) * w by positivity)
  have hright := mul_le_mul_of_nonneg_left hcells (show 0 ≤ (m : ℝ) * w by positivity)
  have hcount := mul_le_mul_of_nonneg_left (add_le_add hleft hright)
    (show 0 ≤ 8 * (T : ℝ) by positivity)
  have hpad := mul_le_mul_of_nonneg_left hrho1 (show 0 ≤ (w : ℝ) + 6 by positivity)
  let X : ℝ := 8 * w * (N + 2 * K * (d + 1) + 1)
  let Y : ℝ := w + 6
  have hbase :
      ((8 * (N * (m * w) + m * (w * (⌊2 * K / (rho / (d + 1))⌋₊ + 1))) * T + w + 6 : ℕ) : ℝ) ≤
        (X * m * T + Y) / rho := by
    apply (le_div_iff₀ hrho).mpr
    dsimp [X, Y]
    push_cast at hcount ⊢
    nlinarith only [hcount, hpad]
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hmT : (1 : ℝ) ≤ ((m : ℝ) + T) * T := by
    nlinarith [Nat.cast_nonneg m (α := ℝ),
      mul_nonneg (Nat.cast_nonneg m (α := ℝ)) (Nat.cast_nonneg T)]
  apply hbase.trans
  apply div_le_div_of_nonneg_right _ hrho.le
  calc
    X * m * T + Y ≤ X * ((m : ℝ) + T) * T + Y * (((m : ℝ) + T) * T) :=
      add_le_add (by gcongr; exact le_add_of_nonneg_right (Nat.cast_nonneg T))
        (le_mul_of_one_le_right hY hmT)
    _ = _ := by dsimp [X, Y]; ring

/-- For [component input dimensions](hyp:dC), [nonnegative truncation radius](hyp:K),
[positive mesh spacing](hyp:hs), and [a finite table alphabet](hyp:tables), assume
[w is at least one](hyp:hw), [latent dimensions](hyp:hd), [component dimensions](hyp:hC),
[first network widths](hyp:hW1), and [second network widths](hyp:hW2) are at most w,
and [component counts are at most N](hyp:hN). If [the alphabet is nonempty](hyp:htables),
[the comparison exponent](hyp:hexponent), [comparison constant](hyp:hCbase),
[depth scale](hyp:hH), and [mesh scale](hyp:hrho) are positive,
[the architecture exponent is bounded by the chosen exponent](hyp:hexp),
[every sample-size comparison base is bounded by Cbase times (m + H)H/rho](hyp:hbase),
and [the displayed logarithmic shattering budget is at most v](hyp:hbudget),
then [the real-valued cube-table indicators have pseudo-dimension at most v](goal). -/
-- @node: ncm_causalTableCubeCode_indicator_pseudodim
lemma ncm_causalTableCubeCode_indicator_pseudodim
    {counts : Fin b → ℕ} (F0 : StructuralClass kind dims dag C)
    (dC : ∀ j, Fin (counts j) → ℕ) (K : ℝ≥0) (dU c1 c2 r0 : ℕ)
    (L1 L2 : ℕ → ℕ) (tau : ℕ → ℝ)
    {A : Type*} (repr : A → NCMIn kind dims dag G C counts F0
      (generatorClassN counts dC K dU c1 c2 L1 L2 tau r0))
    (R0 : NCMIn kind dims dag G C counts F0
      (generatorClassN counts dC K dU c1 c2 L1 L2 tau r0))
    {step : ℝ} (hs : 0 < step)
    (tables : Finset (∀ i k, kind i = Sum.inr k → CategoricalStratum kind →
      Fin ((⌊2 * (K : ℝ) / step⌋₊ + 1) ^ (∑ j, dims j)) → probabilitySimplex k))
    (a : ℝ) (w N : ℕ) (hw : 1 ≤ w) (hd : ∀ j, dims j ≤ w)
    (hC : ∀ j i, dC j i ≤ w) (hW1 : c1 * dU ≤ w) (hW2 : c2 * dU ^ 2 ≤ w)
    (hN : ∀ j, counts j ≤ N)
    (exponent v : ℕ) (Cbase H rho : ℝ)
    (htables : 0 < tables.card) (hexponent : 0 < exponent)
    (hCbase : 0 < Cbase) (hH : 0 < H) (hrho : 0 < rho)
    (hexp : b * (3 * N + N * (w * (w + 1)) + 2) *
      (L1 r0 + L2 r0 + 3) ^ 2 ≤ exponent)
    (hbase : ∀ m : ℕ,
      ((8 * (N * (m * w) + m * (w * (⌊2 * (K : ℝ) / step⌋₊ + 1))) *
        (L1 r0 + L2 r0 + 3) + w + 6 : ℕ) : ℝ) ≤
          Cbase * ((m : ℝ) + H) * H / rho)
    (hbudget : 2 * (Real.log (tables.card : ℝ) +
        (Fintype.card (Fin ((⌊2 * (K : ℝ) / step⌋₊ + 1) ^ (∑ j, dims j)) ×
          CategoricalStratum kind) + 1 : ℕ) * Real.log 2) / Real.log 2 +
      2 * exponent / Real.log 2 *
        Real.log (2 * exponent * (Cbase * H / rho) / Real.log 2) + H ≤ v) :
    Causalean.Stat.Concentration.HasPseudoDimAtMost
      (fun (idx : A × tables × Option (Finset
          (Fin ((⌊2 * (K : ℝ) / step⌋₊ + 1) ^ (∑ j, dims j)) × CategoricalStratum kind))) z =>
        if ncmCausalTableIndicator (repr idx.1)
          (causalTableCubeCode K step hs ∘ simulationLatentCubePoint K)
          idx.2.1.val a idx.2.2 z then (1 : ℝ) else 0) v := by
  let P := fun m =>
    (8 * (N * (m * w) + m * (w * (⌊2 * (K : ℝ) / step⌋₊ + 1))) *
      (L1 r0 + L2 r0 + 3) + w + 6) ^
      (b * (3 * N + N * (w * (w + 1)) + 2) * (L1 r0 + L2 r0 + 3) ^ 2)
  apply ncmCausalTableIndicator_pseudodim_of_grid_patterns repr R0
    (causalTableCubeCode K step hs ∘ simulationLatentCubePoint K)
    tables a P exponent v Cbase H rho htables hexponent hCbase hH hrho ?_ ?_ hbudget
  · intro m draws
    apply (Set.encard_mono ?_).trans
      (ncm_causalTableCubeCode_patterns_encard_le (G := G) F0 dC K dU c1 c2 r0 L1 L2 tau
        draws hs w N hw hd hC hW1 hW2 hN)
    rintro _ ⟨r, rfl⟩
    exact ⟨repr r, rfl⟩
  · intro m
    dsimp only [P]
    rw [Nat.cast_pow]
    apply (pow_le_pow_left₀ (Nat.cast_nonneg _) (hbase m) _).trans
    apply pow_le_pow_right₀ _ hexp
    exact (by
      exact_mod_cast (show 1 ≤ 8 * (N * (m * w) +
        m * (w * (⌊2 * (K : ℝ) / step⌋₊ + 1))) * (L1 r0 + L2 r0 + 3) + w + 6 by omega)
      : (1 : ℝ) ≤ ((8 * (N * (m * w) + m * (w * (⌊2 * (K : ℝ) / step⌋₊ + 1))) *
        (L1 r0 + L2 r0 + 3) + w + 6 : ℕ) : ℝ)).trans (hbase m)

/-- For [component input dimensions](hyp:dC), [a nonnegative truncation radius](hyp:K),
[a positive mesh radius](hyp:hrho) [at most one](hyp:hrho1), and
[positive spacing](hyp:hs) [equal to the mesh radius divided by total latent
dimension plus one](hyp:hstep), take [a finite table alphabet](hyp:tables)
that [is nonempty](hyp:htables). If [w is at least one](hyp:hw),
[latent dimensions](hyp:hd), [component dimensions](hyp:hC),
[first network widths](hyp:hW1), and [second network widths](hyp:hW2) are at most w,
and [component counts are at most N](hyp:hN), then [the cube-table indicator
class has pseudo-dimension at most the ceiling of the nonnegative part of
the explicit logarithmic budget, using padded depth, architecture exponent,
and comparison constant defined in the statement](goal). -/
-- @node: ncm_causalTableCubeCode_mesh_pseudodim
lemma ncm_causalTableCubeCode_mesh_pseudodim
    {counts : Fin b → ℕ} (F0 : StructuralClass kind dims dag C)
    (dC : ∀ j, Fin (counts j) → ℕ) (K : ℝ≥0) (dU c1 c2 r0 : ℕ)
    (L1 L2 : ℕ → ℕ) (tau : ℕ → ℝ)
    {A : Type*} (repr : A → NCMIn kind dims dag G C counts F0
      (generatorClassN counts dC K dU c1 c2 L1 L2 tau r0))
    (R0 : NCMIn kind dims dag G C counts F0
      (generatorClassN counts dC K dU c1 c2 L1 L2 tau r0))
    {rho step : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1) (hs : 0 < step)
    (hstep : step = rho / ((∑ j, dims j) + 1))
    (tables : Finset (∀ i k, kind i = Sum.inr k → CategoricalStratum kind →
      Fin ((⌊2 * (K : ℝ) / step⌋₊ + 1) ^ (∑ j, dims j)) → probabilitySimplex k))
    (htables : tables.Nonempty) (a : ℝ) (w N : ℕ) (hw : 1 ≤ w)
    (hd : ∀ j, dims j ≤ w) (hC : ∀ j i, dC j i ≤ w)
    (hW1 : c1 * dU ≤ w) (hW2 : c2 * dU ^ 2 ≤ w) (hN : ∀ j, counts j ≤ N) :
    let H : ℕ := L1 r0 + L2 r0 + 3
    let exponent : ℕ := b * (3 * N + N * (w * (w + 1)) + 2) * H ^ 2 + 1
    let Cbase : ℝ := 8 * w * (N + 2 * K * ((∑ j, dims j) + 1) + 1) + w + 6
    let budget := 2 * (Real.log (tables.card : ℝ) +
        (Fintype.card (Fin ((⌊2 * (K : ℝ) / step⌋₊ + 1) ^ (∑ j, dims j)) ×
          CategoricalStratum kind) + 1 : ℕ) * Real.log 2) / Real.log 2 +
      2 * exponent / Real.log 2 *
        Real.log (2 * exponent * (Cbase * H / rho) / Real.log 2) + H
    Causalean.Stat.Concentration.HasPseudoDimAtMost
      (fun (idx : A × tables × Option (Finset
          (Fin ((⌊2 * (K : ℝ) / step⌋₊ + 1) ^ (∑ j, dims j)) × CategoricalStratum kind))) z =>
        if ncmCausalTableIndicator (repr idx.1)
          (causalTableCubeCode K step hs ∘ simulationLatentCubePoint K)
          idx.2.1.val a idx.2.2 z then (1 : ℝ) else 0) ⌈max budget 0⌉₊ := by
  intro H exponent Cbase budget
  apply ncm_causalTableCubeCode_indicator_pseudodim F0 dC K dU c1 c2 r0 L1 L2 tau
    repr R0 hs tables a w N hw hd hC hW1 hW2 hN exponent ⌈max budget 0⌉₊
    Cbase H rho htables.card_pos (by dsimp [exponent]; omega)
    (by dsimp [Cbase]; positivity) (by dsimp [H]; positivity) hrho
    (by dsimp [exponent, H]; omega) ?_ ?_
  · intro m
    dsimp [H, Cbase]
    rw [hstep]
    exact causalTable_generator_comparison_base_le (∑ j, dims j) N m w _ K.coe_nonneg
      hrho hrho1 (by omega)
  · exact (le_max_left budget 0).trans (Nat.le_ceil (max budget 0))

/-- For [component input dimensions](hyp:dC), [a nonnegative truncation radius](hyp:K),
[a positive mesh radius](hyp:hrho) [at most one](hyp:hrho1), and
[positive spacing](hyp:hs) [equal to the radius divided by total latent dimension
plus one](hyp:hstep), choose [a finite table alphabet](hyp:tables) that
[is nonempty](hyp:htables). If [w is at least one](hyp:hw),
[latent dimensions](hyp:hd), [component dimensions](hyp:hC),
[first network widths](hyp:hW1), and [second network widths](hyp:hW2) are at most w,
and [component counts are at most N](hyp:hN), then [the cube-table indicators
are contained in a measurably parametrized Boolean class with pseudo-dimension
bounded by the ceiling of the nonnegative explicit logarithmic budget](goal). -/
-- @node: ncm_causalTableCubeCode_mesh_envelope
lemma ncm_causalTableCubeCode_mesh_envelope
    {counts : Fin b → ℕ} (F0 : StructuralClass kind dims dag C)
    (dC : ∀ j, Fin (counts j) → ℕ) (K : ℝ≥0) (dU c1 c2 r0 : ℕ)
    (L1 L2 : ℕ → ℕ) (tau : ℕ → ℝ)
    {A : Type*} (repr : A → NCMIn kind dims dag G C counts F0
      (generatorClassN counts dC K dU c1 c2 L1 L2 tau r0))
    (R0 : NCMIn kind dims dag G C counts F0
      (generatorClassN counts dC K dU c1 c2 L1 L2 tau r0))
    {rho step : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1) (hs : 0 < step)
    (hstep : step = rho / ((∑ j, dims j) + 1))
    (tables : Finset (∀ i k, kind i = Sum.inr k → CategoricalStratum kind →
      Fin ((⌊2 * (K : ℝ) / step⌋₊ + 1) ^ (∑ j, dims j)) → probabilitySimplex k))
    (htables : tables.Nonempty) (a : ℝ) (w N : ℕ) (hw : 1 ≤ w)
    (hd : ∀ j, dims j ≤ w) (hC : ∀ j i, dC j i ≤ w)
    (hW1 : c1 * dU ≤ w) (hW2 : c2 * dU ^ 2 ≤ w) (hN : ∀ j, counts j ≤ N) :
    let H : ℕ := L1 r0 + L2 r0 + 3
    let exponent : ℕ := b * (3 * N + N * (w * (w + 1)) + 2) * H ^ 2 + 1
    let Cbase : ℝ := 8 * w * (N + 2 * K * ((∑ j, dims j) + 1) + 1) + w + 6
    let budget := 2 * (Real.log (tables.card : ℝ) +
        (Fintype.card (Fin ((⌊2 * (K : ℝ) / step⌋₊ + 1) ^ (∑ j, dims j)) ×
          CategoricalStratum kind) + 1 : ℕ) * Real.log 2) / Real.log 2 +
      2 * exponent / Real.log 2 *
        Real.log (2 * exponent * (Cbase * H / rho) / Real.log 2) + H
    BooleanClassEnvelope
      (fun (idx : A × tables × Option (Finset
          (Fin ((⌊2 * (K : ℝ) / step⌋₊ + 1) ^ (∑ j, dims j)) × CategoricalStratum kind))) =>
        ncmCausalTableIndicator (repr idx.1)
          (causalTableCubeCode K step hs ∘ simulationLatentCubePoint K)
          idx.2.1.val a idx.2.2) ⌈max budget 0⌉₊ := by
  classical
  intro H exponent Cbase budget
  have hprototype (j : Fin b) : ∃ q : ThreePartGenerator (counts j) (dims j) (dC j)
      (c1 * dU) (L1 r0) (c2 * dU ^ 2) (L2 r0) (tau r0),
      R0.generator j = truncK K ∘ q.eval := R0.generatorMem j
  choose prototype hprototype using hprototype
  let T := ∀ j, generatorBorelParameters (counts j) (dims j) (dC j)
    (c1 * dU) (L1 r0) (c2 * dU ^ 2) (L2 r0)
  let Q := fun (p : T) j => generatorBorelDecode (prototype j).temperature (p j)
  let family := fun p : T =>
    ncmWithThreePartGenerators dC K dU c1 c2 r0 L1 L2 tau R0 (Q p)
  let code := causalTableCubeCode K step hs ∘ simulationLatentCubePoint (dims := dims) K
  letI : MeasurableSpace tables := ⊤
  letI : MeasurableSpace (Option (Finset
      (Fin ((⌊2 * (K : ℝ) / step⌋₊ + 1) ^ (∑ j, dims j)) × CategoricalStratum kind))) := ⊤
  let B := fun idx : T × tables × Option (Finset
      (Fin ((⌊2 * (K : ℝ) / step⌋₊ + 1) ^ (∑ j, dims j)) × CategoricalStratum kind)) =>
    ncmCausalTableIndicator (family idx.1) code idx.2.1.val a idx.2.2
  have hlatent : Measurable (fun p : T × SimulationInput kind counts =>
      jointNonGumbel (ncmSimulationExogenous (family p.1) p.2)) := by
    have hgen (j : Fin b) : Measurable (fun p : T × SimulationInput kind counts =>
        (Q p.1 j).eval (p.2.1 j)) := by
      have hm : Measurable (fun p : T × SimulationInput kind counts =>
          (p.1 j, p.2.1 j)) := by
        dsimp [T]
        fun_prop
      have hg := generatorBorelDecode_eval_measurable
        (n := counts j) (d := dims j) (dC := dC j)
        (W1 := c1 * dU) (L1 := L1 r0) (W2 := c2 * dU ^ 2) (L2 := L2 r0)
        (prototype j).temperature
      intro s hs
      exact hm (hg hs)
    change Measurable (fun p : T × SimulationInput kind counts =>
      WithLp.toLp 1 (fun ji : Σ j : Fin b, Fin (dims j) =>
        (truncK K ((Q p.1 ji.1).eval (p.2.1 ji.1))).ofLp ji.2))
    apply scm_toLp_measurable.comp
    apply measurable_pi_lambda
    rintro ⟨j, i⟩
    exact ((measurable_pi_apply i).comp scm_ofLp_measurable).comp
      ((coordinateClamp_measurable (-(K : ℝ)) K).comp (hgen j))
  refine ⟨Set.range B, ?_, ?_, ?_⟩
  · apply borelParametrizedClass_range B
    exact ncmCausalTableIndicator_joint_measurable family R0 code
      ((causalTableCubeCode_measurable K step hs).comp
        ((simulationLatentCubePoint_measurable K).comp hlatent)) tables a
  · rintro _ ⟨idx, rfl⟩
    have hq (j : Fin b) : ∃ q : ThreePartGenerator (counts j) (dims j) (dC j)
        (c1 * dU) (L1 r0) (c2 * dU ^ 2) (L2 r0) (tau r0),
        (repr idx.1).generator j = truncK K ∘ q.eval := (repr idx.1).generatorMem j
    choose q hq using hq
    choose p hp using fun j =>
      generatorBorelDecode_eval_surjective (prototype j).temperature (q j)
    have hgeq (j : Fin b) : (family p).generator j = (repr idx.1).generator j := by
      change truncK K ∘ (generatorBorelDecode (prototype j).temperature (p j)).eval = _
      rw [hp j]
      exact (hq j).symm
    refine ⟨(p, idx.2), ?_⟩
    funext z
    have hz : jointNonGumbel (ncmSimulationExogenous (family p) z) =
        jointNonGumbel (ncmSimulationExogenous (repr idx.1) z) := by
      apply PiLp.ext
      rintro ⟨j, i⟩
      change ((family p).generator j (z.1 j)).ofLp i =
        ((repr idx.1).generator j (z.1 j)).ofLp i
      rw [hgeq j]
    change ncmCausalTableIndicator (family p) code idx.2.1.val a idx.2.2 z =
      ncmCausalTableIndicator (repr idx.1) code idx.2.1.val a idx.2.2 z
    rw [ncmCausalTableIndicator_eq_reference_readout (family p) R0,
      ncmCausalTableIndicator_eq_reference_readout (repr idx.1) R0, hz]
  · apply hasPseudoDimAtMost_range B
    exact ncm_causalTableCubeCode_mesh_pseudodim F0 dC K dU c1 c2 r0 L1 L2 tau
      family R0 hrho hrho1 hs hstep tables htables a w N hw hd hC hW1 hW2 hN

/-- Assuming [the Anthony–Bartlett packing bound](hyp:hpacking) and
[squared-loss bound](hyp:hsquared), [there are positive universal tail constants
such that, for restricted candidate networks, a measurable grid approximation,
independent measurable simulation draws with the prescribed law, and the
indicated ambiguity, pseudo-dimension, and measurable-envelope bounds, the
probability that any candidate's empirical observational law exceeds the
stated Wasserstein error is at most the displayed exponential bound](goal).
The error combines grid approximation with the ambiguity tolerance, while the
exponent combines covering complexity with a negative sample-size term. -/
-- @node: restrictedCandidate_causalTable_grid_concentration
lemma restrictedCandidate_causalTable_grid_concentration
    (hpacking : AnthonyBartlettPacking) (hsquared : AnthonyBartlettSquaredLoss) :
    ∃ Ctail ctail : ℝ, 0 < Ctail ∧ 0 < ctail ∧
    ∀ {counts : Fin b → ℕ} {F0 : StructuralClass kind dims dag C}
    (M : CanonicalSCM kind dims dag G C)
    (p0 : ∀ i k, kind i = Sum.inr k → probabilitySimplex k)
    (dC : ∀ j, Fin (counts j) → ℕ) (K L : ℝ≥0) (D c1 c2 : ℕ)
    (L1 L2 : ℕ → ℕ) (tau : ℕ → ℝ) (r0 : ℕ)
    {A : Type*} (repr : A → NCMIn kind dims dag G C counts F0
      (generatorClassN counts dC K D c1 c2 L1 L2 tau r0))
    (hR : ∀ r, restrictedCandidate K L (repr r))
    {s N : ℕ} (hN : 0 < N) {rho : ℝ} (hrho : 0 ≤ rho)
    (grid : Fin s → boundedCube (∑ j, dims j) K)
    (code : boundedCube (∑ j, dims j) K → Fin s) (hcode : Measurable code)
    (hgrid : ∀ x, dist x.val (grid (code x)).val ≤ rho)
    {Omega : Type*} [MeasurableSpace Omega]
    (Q : Measure Omega) [IsProbabilityMeasure Q]
    {m : ℕ} (hm : 0 < m) (draws : Fin m → Omega → SimulationInput kind counts)
    (hind : ProbabilityTheory.iIndepFun draws Q) (hdraws : ∀ j, Measurable (draws j))
    (hlaw : ∀ j, Q.map (draws j) = simulationInputLaw kind counts)
    (delta eps : ℝ) (hdelta : 0 < delta) (heps : 0 < eps)
    (hevent : 2 * (∑ i, ∑ _c : CategoricalStratum kind, (noiseDim (kind i) : ℝ)) *
      ((causalTablePropensityBudget M L : ℝ) * rho + (N : ℝ)⁻¹) ≤ delta + eps)
    (vDim : ℕ)
    (hdim : Causalean.Stat.Concentration.HasPseudoDimAtMost
      (fun (idx : A × (causalPropensityTableGrid p0 N s) ×
          Option (Finset (Fin s × CategoricalStratum kind))) z =>
        if ncmCausalTableIndicator (repr idx.1)
          (code ∘ simulationLatentCubePoint K) idx.2.1.val
          ((causalTablePropensityBudget M L : ℝ) * rho + (N : ℝ)⁻¹) idx.2.2 z
          then (1 : ℝ) else 0) vDim)
    (henvelope : BooleanClassEnvelope
      (fun (idx : A × (causalPropensityTableGrid p0 N s) ×
          Option (Finset (Fin s × CategoricalStratum kind))) =>
        ncmCausalTableIndicator (repr idx.1)
          (code ∘ simulationLatentCubePoint K) idx.2.1.val
          ((causalTablePropensityBudget M L : ℝ) * rho + (N : ℝ)⁻¹) idx.2.2) vDim),
    Q {w | ∃ r, ¬ wasserstein1 (observationalLaw (repr r).canonical.toEuclideanSCM)
        (empiricalMeasure (fun j => ncmEval (repr r) (draws j w))) ≤
      ENNReal.ofReal (2 * (fixedLabelLipschitzBudget M.toEuclideanSCM L (n * n + n) : ℝ) * rho +
        8 * ((∑ i, valueDim (kind i)) * (estimationObservationRadius kind K : ℝ)) *
          (delta + eps))} ≤
      ENNReal.ofReal (Real.exp (Ctail * ((1 + delta⁻¹) * Real.log (2 + delta⁻¹) +
        (vDim + 1 : ℝ) * Real.log (2 + eps⁻¹)) - ctail * m * eps ^ 2)) := by
  obtain ⟨Ctail, ctail, hCtail, hctail, htail⟩ :=
    ncmCausalTable_sampling_concentration (kind := kind) (dims := dims)
      (dag := dag) (G := G) (C := C) hpacking hsquared
  refine ⟨Ctail, ctail, hCtail, hctail, ?_⟩
  intro counts F0 M p0 dC K L D c1 c2 L1 L2 tau r0 A repr hR s N hN rho hrho
    grid code hcode hgrid Omega _ Q _ m hm draws hind hdraws hlaw delta eps hdelta heps
    hevent vDim hdim henvelope
  have htables (r : A) := restrictedCandidate_exists_causalTable_grid
    p0 dC K L D c1 c2 L1 L2 tau r0 (repr r) (hR r) hN hrho grid code hgrid
  choose table hmem hcausal herr using htables
  let selected (r : A) : causalPropensityTableGrid p0 N s := ⟨table r, hmem r⟩
  have hreadouts (r : A) := restrictedCandidate_causalTable_grid_readout
    dC K L D c1 c2 L1 L2 tau r0 (repr r) (hR r) grid code hgrid
  let a := (causalTablePropensityBudget M L : ℝ) * rho + (N : ℝ)⁻¹
  let c := (fixedLabelLipschitzBudget M.toEuclideanSCM L (n * n + n) : ℝ) * rho
  let B := (∑ i, valueDim (kind i)) * (estimationObservationRadius kind K : ℝ)
  have hprop (r i k hi z l j) :
      |(fixedLabelCategoricalPropensity (repr r).canonical l i k hi
          (jointNonGumbel (ncmSimulationExogenous (repr r) z))).val j -
        ((selected r).val i k hi l
          ((code ∘ simulationLatentCubePoint K)
            (jointNonGumbel (ncmSimulationExogenous (repr r) z)))).val j| ≤ a := by
    simpa only [a, selected, Function.comp_apply,
      causalTablePropensityBudget_eq (repr r).canonical M] using herr r i k hi z l j
  have hread (r z l) :
      dist (fixedLabelObservation (repr r).canonical.toEuclideanSCM
        (categoricalStratumAssignment l) (jointNonGumbel (ncmSimulationExogenous (repr r) z)))
        (categoricalStratumVectorObservation (repr r).canonical.toEuclideanSCM l
          (grid ((code ∘ simulationLatentCubePoint K)
            (jointNonGumbel (ncmSimulationExogenous (repr r) z)))).val) ≤ c := by
    simpa only [c, Function.comp_apply,
      canonical_fixedLabelLipschitzBudget_eq (repr r).canonical M] using (hreadouts r).2.2 z l
  have ht := htail repr hm (code ∘ simulationLatentCubePoint K) (by fun_prop)
    (causalPropensityTableGrid p0 N s) selected a (by dsimp [a]; positivity)
    (fun r => hcausal r) hprop
    (fun r l j => categoricalStratumVectorObservation (repr r).canonical.toEuclideanSCM l
      (grid j).val) c B delta eps (by dsimp [c]; positivity) (by dsimp [B]; positivity)
    hdelta heps (fun r => (hreadouts r).1) (fun r => (hreadouts r).2.1) hread hevent
    Q draws hind hdraws hlaw vDim hdim henvelope
  simpa only [c, B, mul_assoc] using ht

end
end Papers.TbsNeuralCausalPi
