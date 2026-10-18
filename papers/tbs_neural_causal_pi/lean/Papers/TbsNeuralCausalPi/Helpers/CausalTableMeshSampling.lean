module
public import Papers.TbsNeuralCausalPi.Helpers.CausalTableMeshEntropy
/-! # Inverse-cubic sampling for the concrete causal-table simulation

The actual table concentration and its explicit entropy are combined with
one fixed tolerance multiplier for the given graph and architecture widths.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
noncomputable section

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

/-- Under [the Anthony–Bartlett packing bound](hyp:hpacking) and
[squared-loss bound](hyp:hsquared), for [reference categorical probability
vectors](hyp:p0), [nonnegative truncation and regularity bounds](hyp:K,L),
and [a width bound at least one](hyp:hw), [there is a positive error constant
such that the probability that any restricted candidate exceeds that constant
times the prescribed mesh in empirical Wasserstein error is at most the
inverse cube of sample size](goal). This holds uniformly over architectures
within the width and component bounds and independent measurable simulation
samples, whenever padded depth is at most sample size, the sample logarithm
is at least one, and the mesh is at most one. -/
-- @node: uniform_restrictedCandidate_causalTable_mesh_cubic_bound
lemma uniform_restrictedCandidate_causalTable_mesh_cubic_bound
    (hpacking : AnthonyBartlettPacking) (hsquared : AnthonyBartlettSquaredLoss)
    (M : CanonicalSCM kind dims dag G C)
    (p0 : ∀ i k, kind i = Sum.inr k → probabilitySimplex k)
    (K L : ℝ≥0) (w N : ℕ) (hw : 1 ≤ w) :
    ∃ A : ℝ, 0 < A ∧
    ∀ {counts : Fin b → ℕ} {F0 : StructuralClass kind dims dag C}
      (dC : ∀ j, Fin (counts j) → ℕ) (D c1 c2 : ℕ)
      (L1 L2 : ℕ → ℕ) (tau : ℕ → ℝ) (r0 : ℕ)
      (hd : ∀ j, dims j ≤ w) (hC : ∀ j i, dC j i ≤ w)
      (hW1 : c1 * D ≤ w) (hW2 : c2 * D ^ 2 ≤ w) (hN : ∀ j, counts j ≤ N)
      {Omega : Type*} [MeasurableSpace Omega]
      (Q : Measure Omega) [IsProbabilityMeasure Q]
      {m : ℕ} (hm : 2 ≤ m) (draws : Fin m → Omega → SimulationInput kind counts)
      (hind : ProbabilityTheory.iIndepFun draws Q) (hdraws : ∀ j, Measurable (draws j))
      (hlaw : ∀ j, Q.map (draws j) = simulationInputLaw kind counts)
      (hHm : (L1 r0 + L2 r0 + 3 : ℕ) ≤ m) (hl : 1 ≤ Real.log m),
      let rho := (m : ℝ) ^ (-(1 : ℝ) / (max 1 (∑ j, dims j) + 2 : ℕ)) * Real.log m +
        (L1 r0 + L2 r0 + 3 : ℕ) * Real.log m / Real.sqrt m
      rho ≤ 1 →
      Q {z | ∃ R : NCMIn kind dims dag G C counts F0
          (generatorClassN counts dC K D c1 c2 L1 L2 tau r0),
        restrictedCandidate K L R ∧ ¬ wasserstein1
          (observationalLaw R.canonical.toEuclideanSCM)
          (empiricalMeasure (fun j => ncmEval R (draws j z))) ≤
            ENNReal.ofReal (A * rho)} ≤
        ENNReal.ofReal ((m : ℝ) ^ (-(3 : ℝ))) := by
  obtain ⟨Ct, ct, hCt, hct, hconcentration⟩ :=
    restrictedCandidate_causalTable_mesh_concentration (kind := kind) (dims := dims)
      (dag := dag) (G := G) (C := C) hpacking hsquared
  let a := b * (3 * N + N * (w * (w + 1)) + 2)
  let base : ℝ := 8 * w * (N + 2 * K * ((∑ j, dims j) + 1) + 1) + w + 6
  let minimum : ℝ := 2 * (∑ i, ∑ _c : CategoricalStratum kind,
    (noiseDim (kind i) : ℝ)) * ((causalTablePropensityBudget M L : ℝ) + 1)
  obtain ⟨mult, hmult, hminimum, htail⟩ := causalTableMeshPseudoDim_mesh_cubic_tail
    (kind := kind) (∑ j, dims j) a K.coe_nonneg
    (show 0 < base by dsimp [base]; positivity) hCt.le hct minimum
  let A : ℝ := 2 * (fixedLabelLipschitzBudget M.toEuclideanSCM L (n * n + n) : ℝ) +
    8 * ((∑ i, valueDim (kind i)) * (estimationObservationRadius kind K : ℝ)) *
      (1 + mult) + 1
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro counts F0 dC D c1 c2 L1 L2 tau r0 hd hC hW1 hW2 hN
    Omega _ Q _ m hm draws hind hdraws hlaw hHm hl rho hrho1
  have hlatent : (m : ℝ) ^ (-(1 : ℝ) / (max 1 (∑ j, dims j) + 2 : ℕ)) *
      Real.log m ≤ rho := by
    dsimp [rho]
    have hp : 0 ≤ (L1 r0 + L2 r0 + 3 : ℕ) * Real.log m / Real.sqrt m := by positivity
    linarith
  have hrho : 0 < rho := (mul_pos
    (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < m by omega)) _)
      (by linarith : 0 < Real.log m)).trans_le hlatent
  let Rtype := {R : NCMIn kind dims dag G C counts F0
    (generatorClassN counts dC K D c1 c2 L1 L2 tau r0) // restrictedCandidate K L R}
  have hc := hconcentration M p0 dC K L D c1 c2 L1 L2 tau r0
    (Subtype.val : Rtype → _) (fun R => R.property) hrho hrho1 w N hw hd hC hW1 hW2 hN
    Q (by omega) draws hind hdraws hlaw mult (by linarith)
    (show minimum ≤ 1 + mult by linarith)
  have ht := htail p0 (L1 r0 + L2 r0 + 3) m (by omega)
    (by exact_mod_cast hm) (by exact_mod_cast hHm) hl hrho1
  have hb := hc.trans (ENNReal.ofReal_le_ofReal (show _ ≤ (m : ℝ) ^ (-(3 : ℝ)) from by
    simpa only [rho, a, base, Nat.cast_add, Nat.cast_one] using ht))
  apply le_trans (measure_mono ?_) hb
  intro z hz
  obtain ⟨R, hR, hbad⟩ := hz
  refine ⟨⟨R, hR⟩, ?_⟩
  intro hgood
  apply hbad
  apply hgood.trans
  apply ENNReal.ofReal_le_ofReal
  dsimp [A]
  nlinarith only [hrho]

/-- Under [the consistency growth schedule for sample size, widths, depths,
temperature and penalty](hyp:h), [the sum of the inverse-power sample-size
mesh term times the sample logarithm and the padded depth times the sample
logarithm divided by the square root of sample size converges to zero](goal). -/
-- @node: consistencyGrowth_padded_simulation_mesh_tendsto_zero
lemma consistencyGrowth_padded_simulation_mesh_tendsto_zero {dU DU : ℕ}
    {m W0 L1 L2 : ℕ → ℕ} {tau lam : ℕ → ℝ}
    (h : ConsistencyGrowthSchedule dU m W0 L1 L2 tau lam) :
    Tendsto (fun r => (m r : ℝ) ^ (-(1 : ℝ) / (max 1 DU + 2 : ℕ)) * Real.log (m r) +
      (L1 r + L2 r + 3 : ℕ) * Real.log (m r) / Real.sqrt (m r)) atTop (𝓝 0) := by
  have hm := consistencyGrowth_simulation_tendsto h
  have hc := estimation_depth_sampling_tendsto (depth := fun _ => (3 : ℝ))
    (p := 0) hm (by norm_num) (by
      simpa only [Real.rpow_zero] using
        (Asymptotics.isBigO_const_const (c := (3 : ℝ)) (c' := (1 : ℝ)) (l := atTop) (by norm_num)))
  have hbase := consistencyGrowth_simulation_mesh_tendsto_zero (DU := DU) h
  have hconstant := estimation_depth_sampling_tendsto (depth := fun _ => (1 : ℝ))
    (p := 0) hm (by norm_num) (by
      simpa only [Real.rpow_zero] using
        (Asymptotics.isBigO_refl (fun _ : ℕ => (1 : ℝ)) atTop))
  have hs := (hbase.sub hconstant).add hc
  simp only [sub_zero, zero_add] at hs
  convert hs using 1
  ext r
  simp only [Nat.cast_add, Nat.cast_ofNat, add_mul, add_div, one_mul]
  ring

/-- Under [the consistency growth schedule](hyp:h), [eventually the sample
size is at least two, the sum of the two depths plus three is at most the
sample size, the sample logarithm is at least one, and the sum of the
inverse-power and padded-depth mesh terms is at most one](goal). -/
-- @node: consistencyGrowth_eventually_causalTable_mesh_conditions
lemma consistencyGrowth_eventually_causalTable_mesh_conditions {dU DU : ℕ}
    {m W0 L1 L2 : ℕ → ℕ} {tau lam : ℕ → ℝ}
    (h : ConsistencyGrowthSchedule dU m W0 L1 L2 tau lam) :
    ∀ᶠ r in atTop, 2 ≤ m r ∧ L1 r + L2 r + 3 ≤ m r ∧ 1 ≤ Real.log (m r) ∧
      (m r : ℝ) ^ (-(1 : ℝ) / (max 1 DU + 2 : ℕ)) * Real.log (m r) +
        (L1 r + L2 r + 3 : ℕ) * Real.log (m r) / Real.sqrt (m r) ≤ 1 := by
  have hm := consistencyGrowth_simulation_tendsto h
  have hl := Real.tendsto_log_atTop.comp hm
  filter_upwards [hm.eventually (eventually_ge_atTop (2 : ℝ)),
    hl.eventually (eventually_ge_atTop (1 : ℝ)),
    (consistencyGrowth_padded_simulation_mesh_tendsto_zero (DU := DU) h).eventually
      (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))] with r hm2 hl1 hrho
  refine ⟨by exact_mod_cast hm2, ?_, hl1, hrho⟩
  have hmr : (1 : ℝ) ≤ m r := by linarith
  have hs : 0 < Real.sqrt (m r) := Real.sqrt_pos.mpr (by linarith)
  have hdepth : (L1 r + L2 r + 3 : ℕ) * Real.log (m r) / Real.sqrt (m r) ≤ 1 := by
    have hp : 0 ≤ (m r : ℝ) ^ (-(1 : ℝ) / (max 1 DU + 2 : ℕ)) * Real.log (m r) := by positivity
    linarith
  have hmul := (div_le_iff₀ hs).mp hdepth
  have hlog := le_mul_of_one_le_right (Nat.cast_nonneg (L1 r + L2 r + 3) (α := ℝ)) hl1
  have hsqrt : Real.sqrt (m r) ≤ (m r : ℝ) := by
    have hsq := Real.sq_sqrt (Nat.cast_nonneg (m r) (α := ℝ))
    nlinarith [Real.sqrt_nonneg (m r)]
  have hh : ((L1 r + L2 r + 3 : ℕ) : ℝ) ≤ (m r : ℝ) := by
    simp only [Function.comp_apply] at hlog
    nlinarith only [hlog, hmul, hsqrt]
  exact_mod_cast hh

/-- Assuming [the Anthony–Bartlett packing bound](hyp:hpacking) and
[squared-loss bound](hyp:hsquared), fix [reference categorical probability
vectors](hyp:p0), [nonnegative truncation and regularity bounds](hyp:K,L),
[component input dimensions](hyp:dC), [a consistency growth schedule](hyp:hgrowth),
and [simulation draws at every schedule index](hyp:draws) that [are independent
with the prescribed simulation law](hyp:hsim). Then [there is a positive
constant A such that eventually the probability that any restricted candidate
has empirical Wasserstein error above A times the sum of the latent
inverse-power mesh term and the depth mesh term is at most the inverse cube
of sample size](goal), where the depth term uses one plus the two depths. -/
-- @node: consistencyGrowth_uniform_simulation_cubic_tail
lemma consistencyGrowth_uniform_simulation_cubic_tail
    (hpacking : AnthonyBartlettPacking) (hsquared : AnthonyBartlettSquaredLoss)
    (M : CanonicalSCM kind dims dag G C)
    (p0 : ∀ i k, kind i = Sum.inr k → probabilitySimplex k)
    (K L : ℝ≥0) {counts : Fin b → ℕ}
    (F0 : ℕ → StructuralClass kind dims dag C)
    (dC : ∀ j, Fin (counts j) → ℕ) (D c1 c2 : ℕ)
    {dU : ℕ} (m W0 L1 L2 : ℕ → ℕ) (tau lam : ℕ → ℝ)
    (hgrowth : ConsistencyGrowthSchedule dU m W0 L1 L2 tau lam)
    {Omega : Type*} [MeasurableSpace Omega]
    (Q : Measure Omega) [IsProbabilityMeasure Q]
    (draws : ∀ r, Fin (m r) → Omega → SimulationInput kind counts)
    (hsim : SimulationDrawsIID Q m draws) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ r in atTop,
      Q {z | ∃ R : NCMIn kind dims dag G C counts (F0 r)
          (generatorClassN counts dC K D c1 c2 L1 L2 tau r),
        restrictedCandidate K L R ∧ ¬ wasserstein1
          (observationalLaw R.canonical.toEuclideanSCM)
          (empiricalMeasure (fun j => ncmEval R (draws r j z))) ≤
            ENNReal.ofReal (A *
              ((m r : ℝ) ^ (-(1 : ℝ) / (max 1 (∑ j, dims j) + 2 : ℕ)) * Real.log (m r) +
                (1 + (L1 r : ℝ) + L2 r) * Real.log (m r) / Real.sqrt (m r)))} ≤
        ENNReal.ofReal ((m r : ℝ) ^ (-(3 : ℝ))) := by
  let w := max 1 (max (Finset.univ.sup dims)
    (max (Finset.univ.sup (fun j => Finset.univ.sup (dC j))) (max (c1 * D) (c2 * D ^ 2))))
  let N := Finset.univ.sup counts
  have hw : 1 ≤ w := le_max_left _ _
  have hd (j) : dims j ≤ w := by
    have h := Finset.le_sup (f := dims) (Finset.mem_univ j)
    dsimp [w]
    omega
  have hC (j i) : dC j i ≤ w := by
    have h1 := Finset.le_sup (f := dC j) (Finset.mem_univ i)
    have h2 := Finset.le_sup (f := fun j => Finset.univ.sup (dC j)) (Finset.mem_univ j)
    dsimp [w]
    omega
  have hW1 : c1 * D ≤ w := by dsimp [w]; omega
  have hW2 : c2 * D ^ 2 ≤ w := by dsimp [w]; omega
  have hN (j) : counts j ≤ N := Finset.le_sup (Finset.mem_univ j)
  obtain ⟨A, hA, htail⟩ := uniform_restrictedCandidate_causalTable_mesh_cubic_bound
    hpacking hsquared M p0 K L w N hw
  refine ⟨3 * A, by positivity, ?_⟩
  filter_upwards [consistencyGrowth_eventually_causalTable_mesh_conditions
    (DU := ∑ j, dims j) hgrowth] with r hr
  have ht := htail (F0 := F0 r) dC D c1 c2 L1 L2 tau r hd hC hW1 hW2 hN Q hr.1 (draws r)
    (hsim r).1 (fun j => ((hsim r).2 j).1) (fun j => ((hsim r).2 j).2)
    hr.2.1 hr.2.2.1 hr.2.2.2
  apply le_trans (measure_mono ?_) ht
  intro z hz
  obtain ⟨R, hR, hbad⟩ := hz
  refine ⟨R, hR, ?_⟩
  intro hgood
  apply hbad
  apply hgood.trans
  apply ENNReal.ofReal_le_ofReal
  have hu : 0 ≤ (m r : ℝ) ^ (-(1 : ℝ) / (max 1 (∑ j, dims j) + 2 : ℕ)) *
      Real.log (m r) := by positivity
  have hv : 0 ≤ Real.log (m r) / Real.sqrt (m r) := by positivity
  have hdv := mul_nonneg
    (show 0 ≤ (L1 r : ℝ) + L2 r by positivity) hv
  have hb : (m r : ℝ) ^ (-(1 : ℝ) / (max 1 (∑ j, dims j) + 2 : ℕ)) * Real.log (m r) +
      (L1 r + L2 r + 3 : ℕ) * Real.log (m r) / Real.sqrt (m r) ≤
    3 * ((m r : ℝ) ^ (-(1 : ℝ) / (max 1 (∑ j, dims j) + 2 : ℕ)) * Real.log (m r) +
      (1 + (L1 r : ℝ) + L2 r) * Real.log (m r) / Real.sqrt (m r)) := by
    simp only [Nat.cast_add, Nat.cast_ofNat, mul_div_assoc] at hu ⊢
    nlinarith only [hu, hdv]
  nlinarith only [mul_le_mul_of_nonneg_left hb hA.le]

end
end Papers.TbsNeuralCausalPi
