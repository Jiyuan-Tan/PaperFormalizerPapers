module
public import Papers.TbsNeuralCausalPi.Helpers.CausalTableGridPatterns
/-! # Explicit concentration for the actual floor-mesh simulations

The floor grid, finite simplex alphabet, polynomial comparison count and
pseudo-dimension bound are assembled for the same complete-observation map.
The tolerance multiplier also pays for ambiguity at zero simplex weights.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
set_option linter.unusedVariables false

/-- For [a positive mesh radius](hyp:hrho), [one plus the ceiling of its
reciprocal is a positive integer whose reciprocal is at most the radius](goal). -/
-- @node: causalTable_mesh_resolution
lemma causalTable_mesh_resolution {rho : ℝ} (hrho : 0 < rho) :
    0 < ⌈rho⁻¹⌉₊ + 1 ∧ (((⌈rho⁻¹⌉₊ + 1 : ℕ) : ℝ))⁻¹ ≤ rho := by
  refine ⟨by omega, ?_⟩
  have hN : (0 : ℝ) < (⌈rho⁻¹⌉₊ + 1 : ℕ) := by positivity
  have hle : rho⁻¹ ≤ ((⌈rho⁻¹⌉₊ + 1 : ℕ) : ℝ) :=
    (Nat.le_ceil _).trans (by push_cast; linarith)
  have hinv := inv_anti₀ (inv_pos.mpr hrho) hle
  simpa only [inv_inv] using hinv

/-- Given [the number of probability tables](hyp:tables), [the number of
cell-and-label types](hyp:types), [the generator comparison exponent](hyp:exponent),
[the padded network depth](hyp:depth), [the comparison constant](hyp:base),
and [the mesh radius](hyp:rho), the [mesh pseudo-dimension budget](goal) is
the ceiling of the nonnegative part of the sum of twice the table-and-type
logarithmic count divided by log 2, twice the exponent times the logarithm
of 2 times exponent times base times depth divided by radius and log 2,
divided by log 2, and the depth. -/
-- @node: causalTableMeshPseudoDim
def causalTableMeshPseudoDim (tables types exponent depth : ℕ) (base rho : ℝ) : ℕ :=
  ⌈max (2 * (Real.log (tables : ℝ) + (types + 1 : ℕ) * Real.log 2) / Real.log 2 +
    2 * exponent / Real.log 2 * Real.log (2 * exponent * (base * depth / rho) / Real.log 2) +
    depth) 0⌉₊

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

/-- Under [the Anthony–Bartlett packing bound](hyp:hpacking) and
[squared-loss bound](hyp:hsquared), [positive universal tail constants bound
the probability that any restricted candidate's empirical observational law
has Wasserstein error above the displayed constant times the mesh radius by
the displayed exponential expression involving the explicit mesh
pseudo-dimension](goal). This holds for mesh radii in `(0, 1]`, bounded
generator dimensions, widths and component counts, independent measurable
draws with the simulation law, and a positive multiplier large enough to
cover the categorical ambiguity budget. -/
-- @node: restrictedCandidate_causalTable_mesh_concentration
lemma restrictedCandidate_causalTable_mesh_concentration
    (hpacking : AnthonyBartlettPacking) (hsquared : AnthonyBartlettSquaredLoss) :
    ∃ Ctail ctail : ℝ, 0 < Ctail ∧ 0 < ctail ∧
    ∀ {counts : Fin b → ℕ} {F0 : StructuralClass kind dims dag C}
    (M : CanonicalSCM kind dims dag G C)
    (p0 : ∀ i k, kind i = Sum.inr k → probabilitySimplex k)
    (dC : ∀ j, Fin (counts j) → ℕ) (K L : ℝ≥0) (D c1 c2 : ℕ)
    (L1 L2 : ℕ → ℕ) (tau : ℕ → ℝ) (r0 : ℕ)
    {A : Type*}
    (repr : A → NCMIn kind dims dag G C counts F0
      (generatorClassN counts dC K D c1 c2 L1 L2 tau r0))
    (hR : ∀ r, restrictedCandidate K L (repr r))
    {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (w N : ℕ) (hw : 1 ≤ w) (hd : ∀ j, dims j ≤ w)
    (hC : ∀ j i, dC j i ≤ w) (hW1 : c1 * D ≤ w) (hW2 : c2 * D ^ 2 ≤ w)
    (hN : ∀ j, counts j ≤ N)
    {Omega : Type*} [MeasurableSpace Omega]
    (Q : Measure Omega) [IsProbabilityMeasure Q]
    {m : ℕ} (hm : 0 < m) (draws : Fin m → Omega → SimulationInput kind counts)
    (hind : ProbabilityTheory.iIndepFun draws Q) (hdraws : ∀ j, Measurable (draws j))
    (hlaw : ∀ j, Q.map (draws j) = simulationInputLaw kind counts)
    (mult : ℝ) (hmult : 0 < mult)
    (hamb : 2 * (∑ i, ∑ _c : CategoricalStratum kind, (noiseDim (kind i) : ℝ)) *
      ((causalTablePropensityBudget M L : ℝ) + 1) ≤ 1 + mult),
    let step := rho / ((∑ j, dims j) + 1)
    let cells := (⌊2 * (K : ℝ) / step⌋₊ + 1) ^ (∑ j, dims j)
    let H := L1 r0 + L2 r0 + 3
    let exponent := b * (3 * N + N * (w * (w + 1)) + 2) * H ^ 2 + 1
    let base : ℝ := 8 * w * (N + 2 * K * ((∑ j, dims j) + 1) + 1) + w + 6
    let v := causalTableMeshPseudoDim
      (causalPropensityTableGrid p0 (⌈rho⁻¹⌉₊ + 1) cells).card
      (Fintype.card (Fin cells × CategoricalStratum kind)) exponent H base rho
    Q {z | ∃ r, ¬ wasserstein1 (observationalLaw (repr r).canonical.toEuclideanSCM)
        (empiricalMeasure (fun j => ncmEval (repr r) (draws j z))) ≤
      ENNReal.ofReal ((2 * (fixedLabelLipschitzBudget M.toEuclideanSCM L (n * n + n) : ℝ) +
        8 * ((∑ i, valueDim (kind i)) * (estimationObservationRadius kind K : ℝ)) *
          (1 + mult)) * rho)} ≤
      ENNReal.ofReal (Real.exp (Ctail * ((1 + rho⁻¹) * Real.log (2 + rho⁻¹) +
        (v + 1 : ℝ) * Real.log (2 + (mult * rho)⁻¹)) - ctail * m * (mult * rho) ^ 2)) := by
  obtain ⟨Ct, ct, hCt, hct, htail⟩ :=
    restrictedCandidate_causalTable_grid_concentration (kind := kind) (dims := dims)
      (dag := dag) (G := G) (C := C) hpacking hsquared
  refine ⟨Ct, ct, hCt, hct, ?_⟩
  intro counts F0 M p0 dC K L D c1 c2 L1 L2 tau r0 A repr hR
    rho hrho hrho1 w N hw hd hC hW1 hW2 hN Omega _ Q _ m hm draws hind hdraws hlaw
    mult hmult hamb step cells H exponent base v
  by_cases hA : Nonempty A
  · let := hA
    have hs : 0 < step := by dsimp [step]; positivity
    let x0 : boundedCube (∑ j, dims j) K := ⟨0, by intro j; simp [K.coe_nonneg]⟩
    have hgrid (x : boundedCube (∑ j, dims j) K) :
        dist x.val
        (causalTableCubeGrid K step hs x0 (causalTableCubeCode K step hs x)).val ≤ rho := by
      apply (causalTableCubeGrid_error K step hs x0 x).trans
      dsimp [step]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (∑ j, dims j) + 1)).mpr
      nlinarith
    have hdim := ncm_causalTableCubeCode_mesh_pseudodim F0 dC K D c1 c2 r0 L1 L2 tau
      repr (repr (Classical.choice ‹Nonempty A›)) hrho hrho1 hs rfl
      (causalPropensityTableGrid p0 (⌈rho⁻¹⌉₊ + 1) cells)
      (causalPropensityTableGrid_nonempty p0 _ _)
      ((causalTablePropensityBudget M L : ℝ) * rho + ((⌈rho⁻¹⌉₊ + 1 : ℕ) : ℝ)⁻¹)
      w N hw hd hC hW1 hW2 hN
    have henvelope := ncm_causalTableCubeCode_mesh_envelope F0 dC K D c1 c2 r0 L1 L2 tau
      repr (repr (Classical.choice ‹Nonempty A›)) hrho hrho1 hs rfl
      (causalPropensityTableGrid p0 (⌈rho⁻¹⌉₊ + 1) cells)
      (causalPropensityTableGrid_nonempty p0 _ _)
      ((causalTablePropensityBudget M L : ℝ) * rho + ((⌈rho⁻¹⌉₊ + 1 : ℕ) : ℝ)⁻¹)
      w N hw hd hC hW1 hW2 hN
    have hevent : 2 * (∑ i, ∑ _c : CategoricalStratum kind, (noiseDim (kind i) : ℝ)) *
        ((causalTablePropensityBudget M L : ℝ) * rho + ((⌈rho⁻¹⌉₊ + 1 : ℕ) : ℝ)⁻¹) ≤
        rho + mult * rho := by
      have hsum : 0 ≤ 2 * (∑ i, ∑ _c : CategoricalStratum kind,
          (noiseDim (kind i) : ℝ)) := by positivity
      calc
        _ ≤ 2 * (∑ i, ∑ _c : CategoricalStratum kind, (noiseDim (kind i) : ℝ)) *
            (((causalTablePropensityBudget M L : ℝ) + 1) * rho) :=
          mul_le_mul_of_nonneg_left (by linarith [(causalTable_mesh_resolution hrho).2]) hsum
        _ ≤ (1 + mult) * rho := by nlinarith only [mul_le_mul_of_nonneg_right hamb hrho.le]
        _ = _ := by ring
    have ht := htail M p0 dC K L D c1 c2 L1 L2 tau r0 repr hR
      (causalTable_mesh_resolution hrho).1 hrho.le
      (causalTableCubeGrid K step hs x0) (causalTableCubeCode K step hs)
      (by fun_prop) hgrid Q hm draws hind hdraws hlaw rho (mult * rho) hrho
      (mul_pos hmult hrho) hevent v (by simpa only [v, causalTableMeshPseudoDim] using hdim)
      (by simpa only [v, causalTableMeshPseudoDim] using henvelope)
    have heq : (2 * (fixedLabelLipschitzBudget M.toEuclideanSCM L (n * n + n) : ℝ) +
        8 * ((∑ i, valueDim (kind i)) * (estimationObservationRadius kind K : ℝ)) *
          (1 + mult)) * rho =
        2 * (fixedLabelLipschitzBudget M.toEuclideanSCM L (n * n + n) : ℝ) * rho +
          8 * ((∑ i, valueDim (kind i)) * (estimationObservationRadius kind K : ℝ)) *
            (rho + mult * rho) := by ring
    rw [heq]
    exact ht
  · have hempty : {z | ∃ r, ¬ wasserstein1
        (observationalLaw (repr r).canonical.toEuclideanSCM)
        (empiricalMeasure (fun j => ncmEval (repr r) (draws j z))) ≤
          ENNReal.ofReal ((2 *
            (fixedLabelLipschitzBudget M.toEuclideanSCM L (n * n + n) : ℝ) +
              8 * ((∑ i, valueDim (kind i)) * (estimationObservationRadius kind K : ℝ)) *
                (1 + mult)) * rho)} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
      intro r _
      exact hA ⟨r⟩
    rw [hempty, measure_empty]
    exact bot_le

/-- Assuming [the Anthony–Bartlett packing bound](hyp:hpacking) and
[squared-loss bound](hyp:hsquared), for [reference categorical probability
vectors](hyp:p0) and [nonnegative truncation and regularity bounds](hyp:K,L),
[there are positive tail constants and an ambiguity multiplier at least one
such that the displayed exponential bound controls the probability of a
Wasserstein error above the stated multiple of the mesh radius for any
restricted generator model](goal). The constants work for every admissible
mesh, bounded architecture, and independent measurable sample with the
simulation law, including empty candidate classes. -/
-- @node: uniform_restrictedCandidate_causalTable_mesh_concentration
lemma uniform_restrictedCandidate_causalTable_mesh_concentration
    (hpacking : AnthonyBartlettPacking) (hsquared : AnthonyBartlettSquaredLoss)
    (M : CanonicalSCM kind dims dag G C)
    (p0 : ∀ i k, kind i = Sum.inr k → probabilitySimplex k) (K L : ℝ≥0) :
    ∃ Ctail ctail mult : ℝ, 0 < Ctail ∧ 0 < ctail ∧ 1 ≤ mult ∧
    ∀ {counts : Fin b → ℕ} {F0 : StructuralClass kind dims dag C}
    (dC : ∀ j, Fin (counts j) → ℕ) (D c1 c2 : ℕ)
    (L1 L2 : ℕ → ℕ) (tau : ℕ → ℝ) (r0 : ℕ)
    {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (w N : ℕ) (hw : 1 ≤ w) (hd : ∀ j, dims j ≤ w)
    (hC : ∀ j i, dC j i ≤ w) (hW1 : c1 * D ≤ w) (hW2 : c2 * D ^ 2 ≤ w)
    (hN : ∀ j, counts j ≤ N)
    {Omega : Type*} [MeasurableSpace Omega]
    (Q : Measure Omega) [IsProbabilityMeasure Q]
    {m : ℕ} (hm : 0 < m) (draws : Fin m → Omega → SimulationInput kind counts)
    (hind : ProbabilityTheory.iIndepFun draws Q) (hdraws : ∀ j, Measurable (draws j))
    (hlaw : ∀ j, Q.map (draws j) = simulationInputLaw kind counts),
    let step := rho / ((∑ j, dims j) + 1)
    let cells := (⌊2 * (K : ℝ) / step⌋₊ + 1) ^ (∑ j, dims j)
    let H := L1 r0 + L2 r0 + 3
    let exponent := b * (3 * N + N * (w * (w + 1)) + 2) * H ^ 2 + 1
    let base : ℝ := 8 * w * (N + 2 * K * ((∑ j, dims j) + 1) + 1) + w + 6
    let v := causalTableMeshPseudoDim
      (causalPropensityTableGrid p0 (⌈rho⁻¹⌉₊ + 1) cells).card
      (Fintype.card (Fin cells × CategoricalStratum kind)) exponent H base rho
    Q {z | ∃ R : NCMIn kind dims dag G C counts F0
        (generatorClassN counts dC K D c1 c2 L1 L2 tau r0),
      restrictedCandidate K L R ∧ ¬ wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
        (empiricalMeasure (fun j => ncmEval R (draws j z))) ≤
      ENNReal.ofReal ((2 * (fixedLabelLipschitzBudget M.toEuclideanSCM L (n * n + n) : ℝ) +
        8 * ((∑ i, valueDim (kind i)) * (estimationObservationRadius kind K : ℝ)) *
          (1 + mult)) * rho)} ≤
      ENNReal.ofReal (Real.exp (Ctail * ((1 + rho⁻¹) * Real.log (2 + rho⁻¹) +
        (v + 1 : ℝ) * Real.log (2 + (mult * rho)⁻¹)) - ctail * m * (mult * rho) ^ 2)) := by
  obtain ⟨Ct, ct, hCt, hct, htail⟩ :=
    restrictedCandidate_causalTable_mesh_concentration (kind := kind) (dims := dims)
      (dag := dag) (G := G) (C := C) hpacking hsquared
  let mult : ℝ := 2 * (∑ i, ∑ _c : CategoricalStratum kind,
    (noiseDim (kind i) : ℝ)) * ((causalTablePropensityBudget M L : ℝ) + 1) + 1
  have hmult : 1 ≤ mult := by
    have hp : 0 ≤ 2 * (∑ i, ∑ _c : CategoricalStratum kind,
      (noiseDim (kind i) : ℝ)) * ((causalTablePropensityBudget M L : ℝ) + 1) := by positivity
    dsimp [mult]
    linarith
  have hamb : 2 * (∑ i, ∑ _c : CategoricalStratum kind, (noiseDim (kind i) : ℝ)) *
      ((causalTablePropensityBudget M L : ℝ) + 1) ≤ 1 + mult := by dsimp [mult]; linarith
  refine ⟨Ct, ct, mult, hCt, hct, hmult, ?_⟩
  intro counts F0 dC D c1 c2 L1 L2 tau r0 rho hrho hrho1 w N hw hd hC hW1 hW2 hN
    Omega _ Q _ m hm draws hind hdraws hlaw step cells H exponent base v
  let A := {R : NCMIn kind dims dag G C counts F0
    (generatorClassN counts dC K D c1 c2 L1 L2 tau r0) // restrictedCandidate K L R}
  have ht := htail M p0 dC K L D c1 c2 L1 L2 tau r0 (Subtype.val : A → _)
    (fun r => r.property) hrho hrho1 w N hw hd hC hW1 hW2 hN
    Q hm draws hind hdraws hlaw mult (by linarith) hamb
  simpa only [Subtype.exists, exists_prop] using ht

end
end Papers.TbsNeuralCausalPi
