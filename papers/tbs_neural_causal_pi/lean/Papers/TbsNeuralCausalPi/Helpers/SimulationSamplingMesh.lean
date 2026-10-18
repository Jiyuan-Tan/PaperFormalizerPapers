module
public import Papers.TbsNeuralCausalPi.Helpers.SimulationSamplingConcentration
public import Papers.TbsNeuralCausalPi.Helpers.EstimationFeasibility
public import Papers.TbsNeuralCausalPi.Helpers.SimulationMeshEntropy
public import Papers.TbsNeuralCausalPi.Helpers.SimulationCubeGrid
/-! # Inverse-cubic concentration for the actual neural simulation laws

This assembles finite-table transport with entropy absorption at the prescribed
mesh. The table approximation and representation complexity remain explicit
local obligations; no sampling bound is assumed on a paper theorem.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
noncomputable section
set_option linter.unusedVariables false
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)} {C : Fin b → Set (Fin n)}

/-- Assuming [the Anthony–Bartlett packing bound](hyp:hpacking), [the
Anthony–Bartlett squared-loss bound](hyp:hsquared), and [a nonnegative
complexity coefficient V](hyp:hV), [there is a multiplier A at least one
such that the probability of any admissible model's empirical observational
law having Wasserstein error greater than 2a + 4B(δ + ε) is at most m⁻³,
provided the draws are independent, measurable and have the simulation input
law, the outputs and table values lie in a common compact set, the table
diameter is at most B, approximation error is at most a outside measurable
ambiguity events of probability at most δ + ε and at most a + B inside,
and the table indicators are Borel-parametrized with pseudo-dimension at most
vDim. Here a and B are nonnegative, δ and ε are positive, m is at least two
with log m at least one, D is at least one and at least the nonnegative
integer d, H lies between zero and m, δ equals
m raised to −1/(D + 2) times log m plus H log m divided by √m, ε equals Aδ,
and vDim + 1 is at most V times the sum of δ⁻ᵈ log(2 + 1/δ) and
H² log(2 + H/δ)](goal). -/
-- @node: ncmEval_sampling_mesh_cubic_concentration
lemma ncmEval_sampling_mesh_cubic_concentration
    (hpacking : AnthonyBartlettPacking) (hsquared : AnthonyBartlettSquaredLoss)
    {V : ℝ} (hV : 0 ≤ V) :
    ∃ A : ℝ, 1 ≤ A ∧
    ∀ {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {Omega : Type*} [MeasurableSpace Omega] (Q : Measure Omega) [IsProbabilityMeasure Q]
    {k m : ℕ} (hm : 0 < m)
    (admissible : NCMIn kind dims dag G C counts F0 F1 → Prop)
    (typeOf : NCMIn kind dims dag G C counts F0 F1 → SimulationInput kind counts → Fin k)
    (v : NCMIn kind dims dag G C counts F0 F1 → Fin k → Joint kind)
    (E : NCMIn kind dims dag G C counts F0 F1 → Set (SimulationInput kind counts))
    (draws : Fin m → Omega → SimulationInput kind counts)
    (hind : iIndepFun draws Q) (hdraws : ∀ j, Measurable (draws j))
    (hlaw : ∀ j, Q.map (draws j) = simulationInputLaw kind counts)
    (S : Set (Joint kind)) (hS : IsCompact S) (a B delta eps : ℝ)
    (ha : 0 ≤ a) (hB : 0 ≤ B) (hdelta : 0 < delta) (heps : 0 < eps)
    (htype : ∀ R, admissible R → Measurable (typeOf R))
    (hE : ∀ R, admissible R → MeasurableSet (E R))
    (hparam : BorelParametrizedClass (Set.range
      (tableSamplingIndicator (fun R : {R // admissible R} => typeOf R.val)
        (fun R => E R.val))))
    (hfrange : ∀ R, admissible R → ∀ z, ncmEval R z ∈ S)
    (hvrange : ∀ R, admissible R → ∀ i, v R i ∈ S)
    (hdiam : ∀ R, admissible R → ∀ i j, dist (v R i) (v R j) ≤ B)
    (herr : ∀ R, admissible R → ∀ z, edist (ncmEval R z) (v R (typeOf R z)) ≤
      ENNReal.ofReal a + (E R).indicator (fun _ => ENNReal.ofReal B) z)
    (hprob : ∀ R, admissible R → (simulationInputLaw kind counts).real (E R) ≤ delta + eps)
    (d vDim : ℕ) (D H : ℝ)
    (hm2 : 2 ≤ m) (hD : 1 ≤ D) (hd : (d : ℝ) ≤ D)
    (hH : 0 ≤ H) (hHm : H ≤ m) (hl : 1 ≤ Real.log m)
    (hmesh : delta = (m : ℝ) ^ (-(1 : ℝ) / (D + 2)) * Real.log m +
      H * Real.log m / Real.sqrt m)
    (hepsMesh : eps = A * delta)
    (hbudget : (vDim : ℝ) + 1 ≤ V *
      ((delta⁻¹) ^ d * Real.log (2 + delta⁻¹) + H ^ 2 * Real.log (2 + H / delta)))
    (hdim : Causalean.Stat.Concentration.HasPseudoDimAtMost
      (fun i : {R // admissible R} × Option (Finset (Fin k)) => fun z =>
        if tableSamplingIndicator (fun R : {R // admissible R} => typeOf R.val)
          (fun R => E R.val) i z then (1 : ℝ) else 0) vDim),
      Q {w | ∃ R, admissible R ∧
        ¬ wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
          (empiricalMeasure (fun i => ncmEval R (draws i w))) ≤
            ENNReal.ofReal (2 * a + 4 * B * (delta + eps))} ≤
        ENNReal.ofReal ((m : ℝ) ^ (-(3 : ℝ))) := by
  obtain ⟨Ctail, c, hC, hc, htail⟩ :=
    ncmEval_sampling_concentration_of_table_pseudodim
      (kind := kind) (dims := dims) (dag := dag) (G := G) (C := C) hpacking hsquared
  obtain ⟨A, hA, hmeshTail⟩ := simulation_mesh_pseudodim_cubic_tail hC.le hc hV
  refine ⟨A, hA, ?_⟩
  intro counts F0 F1 Omega _ Q _ k m hm admissible typeOf v E draws hind hdraws hlaw
    S hS a B delta eps ha hB hdelta heps htype hE hparam hfrange hvrange hdiam herr hprob
    d vDim D H hm2 hD hd hH hHm hl hmesh hepsMesh hbudget hdim
  apply (htail Q hm admissible typeOf v E draws hind hdraws hlaw S hS a B delta eps
    ha hB hdelta heps htype hE hparam hfrange hvrange hdiam herr hprob vDim hdim).trans
  apply ENNReal.ofReal_le_ofReal
  subst eps
  subst delta
  exact hmeshTail m D H d vDim (by exact_mod_cast hm2) hD hd hH hHm hl hbudget

/-- If [the simulation size m is at least one](hyp:hm), [the observation
index r is positive](hyp:hr), [c is positive](hyp:hc), and [r is at most
c times m](hyp:hlinear), then [m⁻³ is at most c²r⁻²](goal). -/
-- @node: simulation_inverse_cubic_le_observation_square
lemma simulation_inverse_cubic_le_observation_square {m r c : ℝ}
    (hm : 1 ≤ m) (hr : 0 < r) (hc : 0 < c) (hlinear : r ≤ c * m) :
    m ^ (-(3 : ℝ)) ≤ c ^ 2 * r ^ (-(2 : ℤ)) := by
  have hm0 : 0 < m := by linarith
  rw [Real.rpow_neg hm0.le, show (3 : ℝ) = (3 : ℕ) from rfl,
    Real.rpow_natCast, zpow_neg, zpow_ofNat]
  have hs : r ^ 2 ≤ (c * m) ^ 2 := by nlinarith
  have hm23 : m ^ 2 ≤ m ^ 3 := by nlinarith [sq_nonneg (m - 1)]
  rw [← one_div, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ (by positivity : 0 < m ^ 3) (by positivity : 0 < r ^ 2)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hm23 (sq_nonneg c)]

/-- For [a consistency growth schedule for the simulation sizes, network
sizes, and tuning sequences](hyp:h), [there is a positive constant B such
that, for all sufficiently large observation indices r, the inverse cube of
the simulation size is at most B times r⁻²](goal). -/
-- @node: consistencyGrowth_simulation_cubic_tail_le
lemma consistencyGrowth_simulation_cubic_tail_le {dU : ℕ}
    {m W0 L1 L2 : ℕ → ℕ} {tau lam : ℕ → ℝ}
    (h : ConsistencyGrowthSchedule dU m W0 L1 L2 tau lam) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ r in atTop,
      (m r : ℝ) ^ (-(3 : ℝ)) ≤ B * (r : ℝ) ^ (-(2 : ℤ)) := by
  obtain ⟨c, hc, hbound⟩ := h.1.exists_pos
  refine ⟨c ^ 2, by positivity, ?_⟩
  filter_upwards [hbound.bound, eventually_ge_atTop (1 : ℕ),
    (consistencyGrowth_simulation_tendsto h).eventually (eventually_ge_atTop (1 : ℝ))]
    with r hr hindex hm
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (Nat.cast_nonneg _)] at hr
  exact simulation_inverse_cubic_le_observation_square hm
    (by exact_mod_cast hindex) hc hr

/-- For [a consistency growth schedule](hyp:h), if [the measure of the failure
event at index r is eventually bounded by the inverse cube of the simulation
size at r](hyp:hbad), then [almost every outcome belongs to none of the
failure events after some finite index](goal). -/
-- @node: consistencyGrowth_ae_eventually_of_simulation_cubic_bound
lemma consistencyGrowth_ae_eventually_of_simulation_cubic_bound
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {dU : ℕ} {m W0 L1 L2 : ℕ → ℕ} {tau lam : ℕ → ℝ}
    (h : ConsistencyGrowthSchedule dU m W0 L1 L2 tau lam)
    (bad : ℕ → Set Omega)
    (hbad : ∀ᶠ r in atTop, mu (bad r) ≤
      ENNReal.ofReal ((m r : ℝ) ^ (-(3 : ℝ)))) :
    ∀ᵐ w ∂mu, ∀ᶠ r in atTop, w ∉ bad r := by
  obtain ⟨B, _, hB⟩ := consistencyGrowth_simulation_cubic_tail_le h
  apply estimation_ae_eventually_of_inverse_square_bound mu bad B
  filter_upwards [hbad, hB] with r hr hBr
  exact hr.trans (ENNReal.ofReal_le_ofReal hBr)

end
end Papers.TbsNeuralCausalPi
