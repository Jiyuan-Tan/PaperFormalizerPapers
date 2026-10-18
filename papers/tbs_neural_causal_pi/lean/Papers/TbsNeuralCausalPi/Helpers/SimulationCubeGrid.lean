module
public import Papers.TbsNeuralCausalPi.Helpers.EmpiricalTestNets
public import Papers.TbsNeuralCausalPi.Helpers.SimplexTableGrid
public import Papers.TbsNeuralCausalPi.Helpers.RobustCategoricalTables
public import Mathlib.MeasureTheory.Function.Floor
/-! # Measurable cube quantization for complete simulation tables

Occupied coordinate floor cells are represented by points of the original
cube. The resulting finite code is measurable, preserves the cube, and has
one-norm error at most dimension times the coordinate mesh. This also covers
singleton, zero-dimensional cubes. Tables of continuous outputs use the same
finite alphabet, independently of the network representation.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

-- @node: simulationCubeCellIndex
/-- For [a cube of radius K](hyp:K), [a coordinate mesh](hyp:step) that is
[strictly positive](hyp:hstep), and [a point in the cube](hyp:x), the
[cell index](goal) records the integer part of each coordinate shifted by K
and divided by the mesh. -/
def simulationCubeCellIndex {d : ℕ} (K step : ℝ) (hstep : 0 < step)
    (x : boundedCube d K) : Fin d → Fin (⌊2 * K / step⌋₊ + 1) := fun i =>
  ⟨⌊(x.val.ofLp i + K) / step⌋₊, by
    apply Nat.lt_succ_of_le
    apply Nat.floor_mono
    apply div_le_div_of_nonneg_right _ hstep.le
    have hi := (abs_le.mp (x.property i)).2
    linarith⟩

-- @node: simulationCubeCellIndex_measurable
/-- If [the coordinate mesh is positive](hyp:hstep), then
[the map assigning each cube point its cell index is measurable](goal). -/
@[fun_prop] lemma simulationCubeCellIndex_measurable {d : ℕ} (K step : ℝ)
    (hstep : 0 < step) : Measurable (simulationCubeCellIndex (d := d) K step hstep) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_to_countable'
  intro c
  have hm : Measurable (fun x : boundedCube d K => ⌊(x.val.ofLp i + K) / step⌋₊) := by
    fun_prop
  convert hm (measurableSet_singleton c.val) using 1
  ext x
  simp [simulationCubeCellIndex, Fin.ext_iff]

-- @node: simulationCubeCellIndex_dist_le
/-- If [the mesh is positive](hyp:hstep) and [two cube points have the same
cell index](hyp:h), then [their one-norm distance is at most the dimension
times the mesh](goal). -/
lemma simulationCubeCellIndex_dist_le {d : ℕ} {K step : ℝ} (hstep : 0 < step)
    (x y : boundedCube d K)
    (h : simulationCubeCellIndex K step hstep x = simulationCubeCellIndex K step hstep y) :
    dist x.val y.val ≤ d * step := by
  rw [PiLp.dist_eq_of_L1]
  calc
    _ ≤ ∑ _i : Fin d, step := by
      apply Finset.sum_le_sum
      intro i _
      rw [Real.dist_eq]
      exact empirical_same_floor_bin_le hstep
        (abs_le.mp (x.property i)).1 (abs_le.mp (y.property i)).1
        (congrArg Fin.val (congrFun h i))
    _ = _ := by simp

-- @node: simulationCubeCellRepresentative
/-- Given [a cube radius](hyp:K), [a mesh](hyp:step) that is
[positive](hyp:hstep), [a fallback point in the cube](hyp:x0), and
[a cell index](hyp:c), the [cell representative](goal) is [a chosen cube
point with that index when the cell is occupied](step:1), and [the fallback
point otherwise](step:2). -/
def simulationCubeCellRepresentative {d : ℕ} (K step : ℝ) (hstep : 0 < step)
    (x0 : boundedCube d K) (c : Fin d → Fin (⌊2 * K / step⌋₊ + 1)) : boundedCube d K :=
  if h : ∃ x : boundedCube d K, simulationCubeCellIndex K step hstep x = c then
    Classical.choose h else x0

-- @node: simulationCubeCellRepresentative_index
/-- If [the mesh is positive](hyp:hstep), then [the representative of the
cell containing a cube point has the same cell index as that point](goal),
for any fallback point in the cube. -/
lemma simulationCubeCellRepresentative_index {d : ℕ} (K step : ℝ) (hstep : 0 < step)
    (x0 x : boundedCube d K) :
    simulationCubeCellIndex K step hstep
      (simulationCubeCellRepresentative K step hstep x0 (simulationCubeCellIndex K step hstep x)) =
        simulationCubeCellIndex K step hstep x := by
  unfold simulationCubeCellRepresentative
  rw [dif_pos ⟨x, rfl⟩]
  exact Classical.choose_spec (show ∃ y : boundedCube d K,
    simulationCubeCellIndex K step hstep y = simulationCubeCellIndex K step hstep x from ⟨x, rfl⟩)

-- @node: simulationCubeRound
/-- Given [a cube radius](hyp:K), [a coordinate mesh](hyp:step) that is
[positive](hyp:hstep), [a fallback cube point](hyp:x0), and [a cube point
to approximate](hyp:x), the [rounded point](goal) is the representative of
the cell containing that point. -/
def simulationCubeRound {d : ℕ} (K step : ℝ) (hstep : 0 < step)
    (x0 : boundedCube d K) (x : boundedCube d K) : boundedCube d K :=
  simulationCubeCellRepresentative K step hstep x0 (simulationCubeCellIndex K step hstep x)

-- @node: simulationCubeRound_measurable
/-- If [the mesh is positive](hyp:hstep), then [rounding cube points to their
cell representatives is measurable](goal), for any fallback cube point. -/
@[fun_prop] lemma simulationCubeRound_measurable {d : ℕ} (K step : ℝ) (hstep : 0 < step)
    (x0 : boundedCube d K) : Measurable (simulationCubeRound K step hstep x0) := by
  exact (measurable_of_finite (simulationCubeCellRepresentative K step hstep x0)).comp
    (simulationCubeCellIndex_measurable K step hstep)

-- @node: simulationCubeRound_dist_le
/-- If [the mesh is positive](hyp:hstep), then [the one-norm distance between
a cube point and its rounded representative is at most the dimension times
the mesh](goal). -/
lemma simulationCubeRound_dist_le {d : ℕ} (K step : ℝ) (hstep : 0 < step)
    (x0 x : boundedCube d K) :
    dist (simulationCubeRound K step hstep x0 x).val x.val ≤ d * step :=
  simulationCubeCellIndex_dist_le hstep _ _
    (simulationCubeCellRepresentative_index K step hstep x0 x)

-- @node: simulationCubeTableGrid
/-- Given [a cube radius](hyp:K), [a mesh](hyp:step) that is
[positive](hyp:hstep), [a fallback cube point](hyp:x0), and [a number of table
entries](hyp:J), the [finite table grid](goal) consists of all tables obtained
by choosing a cell representative independently at each entry. -/
def simulationCubeTableGrid {d : ℕ} (K step : ℝ) (hstep : 0 < step)
    (x0 : boundedCube d K) (J : ℕ) : Finset (Fin J → boundedCube d K) :=
  Finset.univ.image (fun c : Fin J → (Fin d → Fin (⌊2 * K / step⌋₊ + 1)) =>
    fun j => simulationCubeCellRepresentative K step hstep x0 (c j))

-- @node: simulationCubeTableGrid_card_le
/-- If [the mesh is positive](hyp:hstep), then [the number of cube tables is
at most the number of scalar cell indices raised to the dimension times the
number of entries](goal), where the number of scalar indices is one plus the
integer part of twice the cube radius divided by the mesh. -/
lemma simulationCubeTableGrid_card_le {d : ℕ} (K step : ℝ) (hstep : 0 < step)
    (x0 : boundedCube d K) (J : ℕ) :
    (simulationCubeTableGrid K step hstep x0 J).card ≤
      (⌊2 * K / step⌋₊ + 1) ^ (d * J) := by
  unfold simulationCubeTableGrid
  simpa [Fintype.card_fun, pow_mul] using
    (Finset.card_image_le (s := Finset.univ)
      (f := fun c : Fin J → (Fin d → Fin (⌊2 * K / step⌋₊ + 1)) =>
        fun j => simulationCubeCellRepresentative K step hstep x0 (c j)))

-- @node: simulationCubeTableGrid_round_mem
/-- If [the mesh is positive](hyp:hstep), then [rounding every entry of any
cube-valued table produces a table in the finite table grid](goal). -/
lemma simulationCubeTableGrid_round_mem {d : ℕ} (K step : ℝ) (hstep : 0 < step)
    (x0 : boundedCube d K) (J : ℕ) (f : Fin J → boundedCube d K) :
    (fun j => simulationCubeRound K step hstep x0 (f j)) ∈
      simulationCubeTableGrid K step hstep x0 J := by
  exact Finset.mem_image.mpr
    ⟨fun j => simulationCubeCellIndex K step hstep (f j), Finset.mem_univ _, rfl⟩

-- @node: simulationCubeTableGrid_log_card_le
/-- If [the cube radius is nonnegative](hyp:hK) and [the mesh is
positive](hyp:hstep), then [the logarithm of the table grid's cardinality is
at most the dimension times the number of entries times the logarithm of
one plus twice the radius divided by the mesh](goal). -/
lemma simulationCubeTableGrid_log_card_le {d : ℕ} {K step : ℝ}
    (hK : 0 ≤ K) (hstep : 0 < step) (x0 : boundedCube d K) (J : ℕ) :
    Real.log ((simulationCubeTableGrid K step hstep x0 J).card : ℝ) ≤
      (d * J : ℕ) * Real.log (1 + 2 * K / step) := by
  have hne : (simulationCubeTableGrid K step hstep x0 J).Nonempty :=
    ⟨_, simulationCubeTableGrid_round_mem K step hstep x0 J (fun _ => x0)⟩
  have hp : (0 : ℝ) < (simulationCubeTableGrid K step hstep x0 J).card := by
    exact_mod_cast hne.card_pos
  have hc : ((simulationCubeTableGrid K step hstep x0 J).card : ℝ) ≤
      ((⌊2 * K / step⌋₊ + 1 : ℕ) : ℝ) ^ (d * J) := by
    exact_mod_cast simulationCubeTableGrid_card_le K step hstep x0 J
  apply ((Real.log_le_log hp hc).trans_eq (Real.log_pow _ _)).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Real.log_le_log (by positivity : (0 : ℝ) < (⌊2 * K / step⌋₊ + 1 : ℕ))
  have hf := Nat.floor_le (show 0 ≤ 2 * K / step by positivity)
  push_cast
  linarith

-- @node: exists_simulation_cube_table_net
/-- If [the cube radius is nonnegative](hyp:hK) and [the error tolerance is
positive](hyp:hrho), then [there is a finite family of cube-valued tables
approximating every table within that tolerance in one-norm at every entry,
whose logarithmic cardinality is at most the dimension times the number of
entries times the logarithm of one plus twice the radius times one plus the
dimension divided by the tolerance](goal). -/
lemma exists_simulation_cube_table_net (d J : ℕ) {K rho : ℝ}
    (hK : 0 ≤ K) (hrho : 0 < rho) :
    ∃ T : Finset (Fin J → boundedCube d K),
      (∀ f : Fin J → boundedCube d K, ∃ g ∈ T,
        ∀ j, dist (f j).val (g j).val ≤ rho) ∧
      Real.log (T.card : ℝ) ≤
        (d * J : ℕ) * Real.log (1 + 2 * K * (d + 1) / rho) := by
  let step := rho / (d + 1)
  have hs : 0 < step := by dsimp [step]; positivity
  let x0 : boundedCube d K := ⟨0, by intro i; simpa using hK⟩
  refine ⟨simulationCubeTableGrid K step hs x0 J, ?_, ?_⟩
  · intro f
    refine ⟨fun j => simulationCubeRound K step hs x0 (f j),
      simulationCubeTableGrid_round_mem K step hs x0 J f, ?_⟩
    intro j
    rw [dist_comm]
    apply (simulationCubeRound_dist_le K step hs x0 (f j)).trans
    dsimp [step]
    have hd : (0 : ℝ) < d + 1 := by positivity
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hd).mpr
    nlinarith
  · convert simulationCubeTableGrid_log_card_le hK hs x0 J using 1
    dsimp [step]
    congr 2
    field_simp


-- @node: exists_simulation_cube_quantizer
/-- If [the cube radius is nonnegative](hyp:hK) and [the approximation
tolerance is positive](hyp:hrho), then [there are a positive finite alphabet,
cube representatives, and a measurable code that approximates every cube
point within the tolerance in one-norm; the alphabet size is one plus the
integer part of twice the radius times one plus the dimension divided by
the tolerance, raised to the dimension](goal). -/
lemma exists_simulation_cube_quantizer (d : ℕ) {K rho : ℝ}
    (hK : 0 ≤ K) (hrho : 0 < rho) :
    ∃ k : ℕ, 0 < k ∧ k = (⌊2 * K * (d + 1) / rho⌋₊ + 1) ^ d ∧
      ∃ grid : Fin k → boundedCube d K,
      ∃ code : boundedCube d K → Fin k, Measurable code ∧
        ∀ x, dist x.val (grid (code x)).val ≤ rho := by
  let step := rho / (d + 1)
  have hs : 0 < step := by dsimp [step]; positivity
  let x0 : boundedCube d K := ⟨0, by intro i; simpa using hK⟩
  let I := Fin d → Fin (⌊2 * K / step⌋₊ + 1)
  let e := Fintype.equivFin I
  have heq : 2 * K / step = 2 * K * (d + 1) / rho := by
    dsimp [step]
    field_simp
  refine ⟨Fintype.card I, by simp [I], ?_,
    fun i => simulationCubeCellRepresentative K step hs x0 (e.symm i),
    fun x => e (simulationCubeCellIndex K step hs x), ?_, ?_⟩
  · simp [I, heq]
  · exact (measurable_of_finite e).comp (simulationCubeCellIndex_measurable K step hs)
  · intro x
    simp only [Equiv.symm_apply_apply]
    rw [dist_comm]
    apply (simulationCubeRound_dist_le K step hs x0 x).trans
    dsimp [step]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < d + 1)).mpr
    nlinarith

-- @node: simulation_cube_quantizer_card_le
/-- If [the cube radius is nonnegative](hyp:hK) and [the tolerance is
positive](hyp:hrho) and [at most one](hyp:hrho1), then [the quantizer alphabet
size is at most one plus twice the radius times one plus the dimension,
raised to the dimension, times the inverse tolerance raised to the
dimension](goal). -/
lemma simulation_cube_quantizer_card_le (d : ℕ) {K rho : ℝ}
    (hK : 0 ≤ K) (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    ((⌊2 * K * (d + 1) / rho⌋₊ + 1 : ℕ) : ℝ) ^ d ≤
      (1 + 2 * K * (d + 1)) ^ d * (rho⁻¹) ^ d := by
  rw [← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  have hf := Nat.floor_le
    (show 0 ≤ 2 * K * (d + 1) / rho by positivity)
  push_cast
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ hrho).mpr
  have hm := (le_div_iff₀ hrho).mp hf
  nlinarith

-- @node: exists_simulation_lipschitz_tables
/-- If [the input cube radius is nonnegative](hyp:hK), [the output cube radius
is nonnegative](hyp:hB), [the input approximation tolerance is positive](hyp:hrho),
and [the output approximation tolerance is positive](hyp:heta), then for [a nonnegative Lipschitz
bound L](hyp:L), [there are a common measurable input code and a finite
family of output tables approximating every L-Lipschitz map with error at
most L times the input tolerance plus the output tolerance; the code has
positive size equal to one plus the integer part of twice the input radius
times one plus the input dimension divided by the input tolerance, raised
to the input dimension, and the table family's logarithmic cardinality is
at most the output dimension times the code size times the logarithm of
one plus twice the output radius times one plus the output dimension
divided by the output tolerance](goal). -/
lemma exists_simulation_lipschitz_tables (d e : ℕ) {K B rho eta : ℝ}
    (hK : 0 ≤ K) (hB : 0 ≤ B) (hrho : 0 < rho) (heta : 0 < eta)
    (L : ℝ≥0) :
    ∃ k : ℕ, 0 < k ∧ k = (⌊2 * K * (d + 1) / rho⌋₊ + 1) ^ d ∧
      ∃ code : boundedCube d K → Fin k, Measurable code ∧
      ∃ T : Finset (Fin k → boundedCube e B),
        Real.log (T.card : ℝ) ≤
          (e * k : ℕ) * Real.log (1 + 2 * B * (e + 1) / eta) ∧
        ∀ f : boundedCube d K → boundedCube e B, LipschitzWith L f →
          ∃ table ∈ T, ∀ x,
            dist (f x).val (table (code x)).val ≤ (L : ℝ) * rho + eta := by
  obtain ⟨k, hk, hcard, grid, code, hcode, hgrid⟩ :=
    exists_simulation_cube_quantizer d hK hrho
  obtain ⟨T, hT, hentropy⟩ := exists_simulation_cube_table_net e k hB heta
  refine ⟨k, hk, hcard, code, hcode, T, hentropy, ?_⟩
  intro f hf
  obtain ⟨table, htable, herr⟩ := hT (fun j => f (grid j))
  refine ⟨table, htable, ?_⟩
  intro x
  have hLip : dist (f x).val (f (grid (code x))).val ≤ (L : ℝ) * rho :=
    (hf.dist_le_mul x (grid (code x))).trans
      (mul_le_mul_of_nonneg_left (hgrid x) L.coe_nonneg)
  exact (dist_triangle _ (f (grid (code x))).val _).trans
    (add_le_add hLip (herr (code x)))


-- @node: exists_simulation_simplex_tables_on_grid
/-- Given [a positive output tolerance](hyp:heta), [a nonnegative coordinate
Lipschitz bound L](hyp:L), and [a grid and code approximating every cube point
within the input tolerance in one-norm](hyp:hgrid), [there is a finite family
of probability-vector tables that approximates every map with coordinate
Lipschitz bound L, with coordinate error at most L times the input tolerance
plus the output tolerance; its logarithmic cardinality is at most the number
of categories times the code size times the logarithm of two plus the inverse
output tolerance](goal). -/
lemma exists_simulation_simplex_tables_on_grid {d n k : ℕ} {K rho eta : ℝ}
    (heta : 0 < eta) (L : ℝ≥0) (p0 : probabilitySimplex n)
    (grid : Fin k → boundedCube d K) (code : boundedCube d K → Fin k)
    (hgrid : ∀ x, dist x.val (grid (code x)).val ≤ rho) :
    ∃ T : Finset (Fin k → probabilitySimplex n),
      Real.log (T.card : ℝ) ≤ (n * k : ℕ) * Real.log (2 + eta⁻¹) ∧
      ∀ f : boundedCube d K → probabilitySimplex n,
        (∀ i, LipschitzWith L (fun x => (f x).val i)) →
        ∃ table ∈ T, ∀ x i,
          |(f x).val i - (table (code x)).val i| ≤ (L : ℝ) * rho + eta := by
  obtain ⟨T, hT, hentropy⟩ := exists_simplex_table_net p0 k heta
  refine ⟨T, hentropy, ?_⟩
  intro f hf
  obtain ⟨table, htable, herr⟩ := hT (fun j => f (grid j))
  refine ⟨table, htable, ?_⟩
  intro x i
  have hLip : |(f x).val i - (f (grid (code x))).val i| ≤ (L : ℝ) * rho :=
    ((hf i).dist_le_mul x (grid (code x))).trans
      (mul_le_mul_of_nonneg_left (hgrid x) L.coe_nonneg)
  calc
    _ ≤ |(f x).val i - (f (grid (code x))).val i| +
        |(f (grid (code x))).val i - (table (code x)).val i| := abs_sub_le _ _ _
    _ ≤ (L : ℝ) * rho + eta := add_le_add hLip
      (by simpa only [abs_sub_comm] using (herr (code x) i).le)

-- @node: simulation_simplex_table_selector_agreement
/-- Suppose [the cube-valued latent variable is measurable](hyp:hU), [the
Gumbel vector is measurable](hyp:hG), [these variables are independent](hyp:hind),
[the vector has the standard independent Gumbel law](hyp:hlaw), and [the
finite code is measurable](hyp:hcode). If [the error bound is
nonnegative](hyp:ha), [the probability map and its coded table differ by at
most this bound in every coordinate](hyp:herr), and [the categorical node
has a positive number of categories](hyp:hk), then [there is a measurable
exceptional event of probability at most twice the number of categories
times the error bound, outside which their canonical selectors agree when
using the same Gumbel draw](goal). -/
lemma simulation_simplex_table_selector_agreement
    {Omega : Type*} [MeasurableSpace Omega] {d n k : ℕ} {K a : ℝ}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (U : Omega → boundedCube d K) (G : Omega → Fin n → ℝ)
    (hU : Measurable U) (hG : Measurable G)
    (hind : ProbabilityTheory.IndepFun U G mu) (hlaw : mu.map G = gumbelInputs n)
    (code : boundedCube d K → Fin k) (hcode : Measurable code)
    (table : Fin k → probabilitySimplex n) (f : boundedCube d K → probabilitySimplex n)
    (ha : 0 ≤ a) (herr : ∀ x i, |(f x).val i - (table (code x)).val i| ≤ a)
    (hk : ∀ m, Sum.inr n = (Sum.inr m : NodeKind) → 0 < m) :
    ∃ bad : Set Omega, MeasurableSet bad ∧ mu bad ≤ ENNReal.ofReal (2 * n * a) ∧
      ∀ w ∉ bad,
        canonicalSelector (.inr n) hk (WithLp.toLp 1 (f (U w)).val)
          (WithLp.toLp 1 (G w)) =
        canonicalSelector (.inr n) hk (WithLp.toLp 1 (table (code (U w))).val)
          (WithLp.toLp 1 (G w)) := by
  let q : boundedCube d K → Fin n → ℝ := fun x => (table (code x)).val
  have hq : Measurable q := by
    fun_prop
  let bad := {w | ¬ ∃ i, RobustCategoricalWinner (q (U w)) a (G w) i}
  have hbad : MeasurableSet bad := by
    simpa only [bad, Set.compl_iUnion, Set.compl_ofPred, Set.iInter_ofPred,
      not_exists, Function.comp_apply] using
      (MeasurableSet.iUnion fun i => measurableSet_robustCategoricalWinner_random
        (q ∘ U) G (by fun_prop) hG a i).compl
  refine ⟨bad, hbad,
    gumbel_no_robust_label_independent_probability_le mu U G hU hG hind hlaw q hq
      (fun x => (table (code x)).property.1) (fun x => (table (code x)).property.2) a ha, ?_⟩
  intro w hw
  have hex : ∃ i, RobustCategoricalWinner (q (U w)) a (G w) i := by
    by_contra h
    exact hw h
  obtain ⟨i, hi⟩ := hex
  exact (robustCategoricalWinner_canonicalSelector _ _ a ha (f (U w)).property.1
    (f (U w)).property.2 (herr (U w)) _ i hi hk).trans
    (robustCategoricalWinner_canonicalSelector _ _ a ha (table (code (U w))).property.1
      (table (code (U w))).property.2 (fun j => by simpa [q] using ha) _ i hi hk).symm

end
end Papers.TbsNeuralCausalPi
