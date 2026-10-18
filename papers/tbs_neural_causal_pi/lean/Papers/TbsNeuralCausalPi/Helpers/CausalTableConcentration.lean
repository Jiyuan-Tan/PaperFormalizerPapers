module
public import Papers.TbsNeuralCausalPi.Helpers.SimulationIndicatorConcentration
public import Papers.TbsNeuralCausalPi.Helpers.CausalTablePatterns
public import Papers.TbsNeuralCausalPi.Setup.EmpiricalAdmissibility
/-! # Uniform concentration for the actual causal tables

The joint indicator class counts both type subsets and ambiguity events.
Its grid-pattern bound gives pseudo-dimension, and the two separate cited
empirical-process results control the complete observed simulation error.
All deterministic table approximation obligations remain explicit here.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

-- @node: ncmCausalTableIndicator_pseudodim_of_grid_patterns
/-- For [a finite collection of categorical probability tables](hyp:tables) that [is nonempty](hyp:htables),
assume [a positive growth exponent](hyp:hexponent), [a positive base constant](hyp:hC),
[a positive offset](hyp:hH), and [a positive scale](hyp:hrho).
If [the number of generated grid patterns on every sample is bounded by the specified counting function](hyp:hpatterns),
[that counting function is at most the base constant times sample size plus offset, times offset divided by scale, all raised to the growth exponent](hyp:hP),
and [the prescribed logarithmic budget, including the table count and one extra bit beyond the finite type count, does not exceed the dimension bound](hyp:hbudget),
[the joint class of ambiguity and type-subset indicators has pseudo-dimension at most that bound](goal). -/
lemma ncmCausalTableIndicator_pseudodim_of_grid_patterns {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} {A : Type*}
    (repr : A → NCMIn kind dims dag G C counts F0 F1 bound)
    (R0 : NCMIn kind dims dag G C counts F0 F1 bound)
    {s : ℕ} (code : Latent dims → Fin s)
    (tables : Finset (∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k))
    (a : ℝ) (P : ℕ → ℕ) (exponent v : ℕ) (Cbase H rho : ℝ)
    (htables : 0 < tables.card) (hexponent : 0 < exponent)
    (hC : 0 < Cbase) (hH : 0 < H) (hrho : 0 < rho)
    (hpatterns : ∀ m (draws : Fin m → SimulationInput kind counts),
      (Set.range (fun r j =>
        code (jointNonGumbel (ncmSimulationExogenous (repr r) (draws j))))).encard ≤ P m)
    (hP : ∀ m, (P m : ℝ) ≤ (Cbase * ((m : ℝ) + H) * H / rho) ^ exponent)
    (hbudget : 2 * (Real.log (tables.card : ℝ) +
        (Fintype.card (Fin s × CategoricalStratum kind) + 1 : ℕ) * Real.log 2) / Real.log 2 +
      2 * exponent / Real.log 2 *
        Real.log (2 * exponent * (Cbase * H / rho) / Real.log 2) + H ≤ v) :
    Causalean.Stat.Concentration.HasPseudoDimAtMost
      (fun (idx : A × tables × Option (Finset (Fin s × CategoricalStratum kind))) z =>
        if ncmCausalTableIndicator (repr idx.1) code idx.2.1.val a idx.2.2 z
          then (1 : ℝ) else 0) v := by
  apply simulation_indicator_hasPseudoDimAtMost_of_pattern_count _
    (Fintype.card (Fin s × CategoricalStratum kind) + 1) exponent v
    hexponent (by exact_mod_cast htables) hC hH hrho _ hbudget
  intro m draws
  have hg := ncmCausalTableIndicator_growth_card_le_of_grid_encard
    repr R0 code tables a draws (P m) (hpatterns m draws)
  have hbits : 2 ^ Fintype.card (Fin s × CategoricalStratum kind) + 1 ≤
      2 ^ (Fintype.card (Fin s × CategoricalStratum kind) + 1) := by
    rw [pow_succ]
    have : 1 ≤ 2 ^ Fintype.card (Fin s × CategoricalStratum kind) :=
      Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
    omega
  have hg' := hg.trans (Nat.mul_le_mul_left (tables.card * P m) hbits)
  have hgR := (Nat.cast_le (α := ℝ)).mpr hg'
  push_cast at hgR
  apply hgR.trans
  calc
    (tables.card : ℝ) * P m * 2 ^ (Fintype.card (Fin s × CategoricalStratum kind) + 1) ≤
        tables.card * (Cbase * ((m : ℝ) + H) * H / rho) ^ exponent *
          2 ^ (Fintype.card (Fin s × CategoricalStratum kind) + 1) := by
      gcongr
      exact hP m
    _ = _ := by ring

-- @node: ncmCausalTableIndicator_integral
/-- Given [a measurable latent grid code](hyp:hcode) and [a categorical probability table](hyp:table),
[the mean of a causal-table indicator equals the ambiguity probability when no type subset is selected, and equals the probability that the generated cell and evaluated labels belong to the selected subset otherwise](goal). -/
lemma ncmCausalTableIndicator_integral {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} (R : NCMIn kind dims dag G C counts F0 F1 bound)
    {s : ℕ} (code : Latent dims → Fin s) (hcode : Measurable code)
    (table : ∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k) (a : ℝ)
    (t : Option (Finset (Fin s × CategoricalStratum kind))) :
    (∫ z, (if ncmCausalTableIndicator R code table a t z then (1 : ℝ) else 0)
      ∂simulationInputLaw kind counts) =
      match t with
      | none => (simulationInputLaw kind counts).real (ncmCausalTableAmbiguity R code table a)
      | some u => (simulationInputLaw kind counts).real
          (ncmCausalTableType R code table ⁻¹' (u : Set (Fin s × CategoricalStratum kind))) := by
  letI := simulationInputLaw_probability kind counts
  rw [simulation_indicator_integral_eq_probability
    (simulationInputLaw kind counts) (ncmCausalTableIndicator_measurable R code hcode table a t)]
  cases t <;> simp [ncmCausalTableIndicator] <;> rfl

-- @node: ncmCausalTable_sampling_failure_subset
/-- For [a positive sample size](hyp:hm), [a measurable grid code](hyp:hcode),
and [a finite collection of categorical probability tables](hyp:tables), suppose
[the propensity tolerance is nonnegative](hyp:ha), [each selected table depends only on earlier labels](hyp:hcausal),
and [each selected table approximates all fixed-label propensities within that tolerance](hyp:herr).
Assume [a nonnegative readout error](hyp:hc), [a nonnegative norm bound](hyp:hB),
[a nonnegative sampling tolerance](hyp:he), [model outputs bounded in norm by that bound](hyp:hbound),
[readout values bounded in norm by that bound](hyp:hvbound),
[fixed-label observations approximated by the readouts within the readout error](hyp:hread),
and [twice the propensity tolerance times the total categorical noise dimension over nodes and labels at most the sampling tolerance](hyp:hevent).
Then [whenever some model's empirical observational law has Wasserstein distance exceeding twice the readout error plus eight times the norm bound times the sampling tolerance, some ambiguity or type-subset indicator has absolute empirical mean error exceeding the sampling tolerance](goal). -/
lemma ncmCausalTable_sampling_failure_subset {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} {A Omega : Type*}
    (repr : A → NCMIn kind dims dag G C counts F0 F1 bound)
    {s m : ℕ} (hm : 0 < m) (code : Latent dims → Fin s) (hcode : Measurable code)
    (tables : Finset (∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k))
    (selected : A → tables)
    (a : ℝ) (ha : 0 ≤ a)
    (hcausal : ∀ r i k hi l l',
      (∀ j, dag.topoOrder j < dag.topoOrder i → l j = l' j) →
        (selected r).val i k hi l = (selected r).val i k hi l')
    (herr : ∀ r i k hi z l j,
      |(fixedLabelCategoricalPropensity (repr r).canonical l i k hi
          (jointNonGumbel (ncmSimulationExogenous (repr r) z))).val j -
        ((selected r).val i k hi l
          (code (jointNonGumbel (ncmSimulationExogenous (repr r) z)))).val j| ≤ a)
    (v : A → CategoricalStratum kind → Fin s → Joint kind) (c B e : ℝ)
    (hc : 0 ≤ c) (hB : 0 ≤ B) (he : 0 ≤ e)
    (hbound : ∀ r z, ‖ncmEval (repr r) z‖ ≤ B)
    (hvbound : ∀ r l j, ‖v r l j‖ ≤ B)
    (hread : ∀ r z l,
      dist (fixedLabelObservation (repr r).canonical.toEuclideanSCM (categoricalStratumAssignment l)
        (jointNonGumbel (ncmSimulationExogenous (repr r) z)))
        (v r l (code (jointNonGumbel (ncmSimulationExogenous (repr r) z)))) ≤ c)
    (hevent : 2 * (∑ i, ∑ _l : CategoricalStratum kind, (noiseDim (kind i) : ℝ)) * a ≤ e)
    (draws : Fin m → Omega → SimulationInput kind counts) :
    {w | ∃ r, ¬ wasserstein1 (observationalLaw (repr r).canonical.toEuclideanSCM)
        (empiricalMeasure (fun i => ncmEval (repr r) (draws i w))) ≤
          ENNReal.ofReal (2 * c + 8 * B * e)} ⊆
      {w | ∃ idx : A × tables × Option (Finset (Fin s × CategoricalStratum kind)), e <
        |(∫ z, (if ncmCausalTableIndicator (repr idx.1) code idx.2.1.val a idx.2.2 z
            then (1 : ℝ) else 0) ∂simulationInputLaw kind counts) -
          (m : ℝ)⁻¹ * ∑ j, if ncmCausalTableIndicator (repr idx.1) code idx.2.1.val a
            idx.2.2 (draws j w) then (1 : ℝ) else 0|} := by
  classical
  rintro w ⟨r, hbad⟩
  change ∃ idx : A × tables × Option (Finset (Fin s × CategoricalStratum kind)), _
  by_contra hgood
  push Not at hgood
  have hamb := hgood (r, selected r, none)
  rw [ncmCausalTableIndicator_integral _ code hcode] at hamb
  have hamb' : |(simulationInputLaw kind counts).real
      (ncmCausalTableAmbiguity (repr r) code (selected r).val a) - (m : ℝ)⁻¹ *
        ∑ i, (ncmCausalTableAmbiguity (repr r) code (selected r).val a).indicator
          (fun _ => (1 : ℝ)) (draws i w)| ≤ e := by
    simpa [ncmCausalTableIndicator, Set.indicator] using hamb
  have hsub (t : Set (Fin s × CategoricalStratum kind)) :
      |(simulationInputLaw kind counts).real
          (ncmCausalTableType (repr r) code (selected r).val ⁻¹' t) -
        (m : ℝ)⁻¹ * ∑ i, if ncmCausalTableType (repr r) code (selected r).val (draws i w) ∈ t
          then (1 : ℝ) else 0| ≤ e := by
    have ht := hgood (r, selected r, some t.toFinite.toFinset)
    rw [ncmCausalTableIndicator_integral _ code hcode] at ht
    simpa [ncmCausalTableIndicator] using ht
  exact hbad ((ncmCausalTable_sampling_transport (repr r) code hcode (selected r).val
    (hcausal r) a ha (herr r) (v r) c B e hc hB he (hbound r) (hvbound r) (hread r)
    hevent).2.2 m hm (fun i => draws i w) hamb' hsub)

-- @node: ncmCausalTable_sampling_concentration
/-- Assume [the Anthony–Bartlett packing bound](hyp:hpacking) and [the Anthony–Bartlett squared-loss bound](hyp:hsquared).
[There are universal positive tail constants giving the following bound for every family of neural causal models,
positive sample size, measurable grid code, and finite alphabet of categorical probability tables.
Suppose each model selects a table whose weights depend only on earlier labels in topological order,
whose fixed-label propensity error is at most a nonnegative tolerance, and whose grid readouts approximate
fixed-label observations within a nonnegative readout error; suppose also that all outputs and readouts
have norm at most a common nonnegative bound. For any positive slack and deviation whose sum is at least
twice the propensity tolerance times the total categorical noise dimension over nodes and label strata,
and independent measurable draws with the simulation input law, if the joint indicator class has a
pseudo-dimension bound and a Boolean class envelope at that dimension, then the probability that any
empirical observational law has Wasserstein error exceeding twice the readout error plus eight times
the norm bound times the sum of slack and deviation is at most an exponential bound. Its exponent is
the first tail constant times the sum of the slack complexity and the product of one plus the dimension
bound with the deviation complexity, minus the second tail constant times sample size times squared deviation](goal).

Here the slack complexity is the product of one plus inverse slack and the logarithm of two plus inverse slack, and the deviation complexity is the logarithm of two plus inverse deviation. -/
lemma ncmCausalTable_sampling_concentration
    (hpacking : AnthonyBartlettPacking) (hsquared : AnthonyBartlettSquaredLoss) :
    ∃ Ctail ctail : ℝ, 0 < Ctail ∧ 0 < ctail ∧ ∀ {counts : Fin b → ℕ}
    {F0 : StructuralClass kind dims dag C} {F1 : GeneratorClass dims counts}
    {bound : Option (ℝ × ℝ)} {A Omega : Type*} [MeasurableSpace Omega]
    (repr : A → NCMIn kind dims dag G C counts F0 F1 bound)
    {s m : ℕ} (hm : 0 < m) (code : Latent dims → Fin s) (hcode : Measurable code)
    (tables : Finset (∀ i k, kind i = Sum.inr k →
      CategoricalStratum kind → Fin s → probabilitySimplex k))
    (selected : A → tables)
    (a : ℝ) (ha : 0 ≤ a)
    (hcausal : ∀ r i k hi l l',
      (∀ j, dag.topoOrder j < dag.topoOrder i → l j = l' j) →
        (selected r).val i k hi l = (selected r).val i k hi l')
    (herr : ∀ r i k hi z l j,
      |(fixedLabelCategoricalPropensity (repr r).canonical l i k hi
          (jointNonGumbel (ncmSimulationExogenous (repr r) z))).val j -
        ((selected r).val i k hi l
          (code (jointNonGumbel (ncmSimulationExogenous (repr r) z)))).val j| ≤ a)
    (v : A → CategoricalStratum kind → Fin s → Joint kind) (c B delta eps : ℝ)
    (hc : 0 ≤ c) (hB : 0 ≤ B) (hdelta : 0 < delta) (heps : 0 < eps)
    (hbound : ∀ r z, ‖ncmEval (repr r) z‖ ≤ B)
    (hvbound : ∀ r l j, ‖v r l j‖ ≤ B)
    (hread : ∀ r z l,
      dist (fixedLabelObservation (repr r).canonical.toEuclideanSCM (categoricalStratumAssignment l)
        (jointNonGumbel (ncmSimulationExogenous (repr r) z)))
        (v r l (code (jointNonGumbel (ncmSimulationExogenous (repr r) z)))) ≤ c)
    (hevent : 2 * (∑ i, ∑ _l : CategoricalStratum kind, (noiseDim (kind i) : ℝ)) * a ≤ delta + eps)
    (Q : Measure Omega) [IsProbabilityMeasure Q]
    (draws : Fin m → Omega → SimulationInput kind counts)
    (hind : iIndepFun draws Q) (hdraws : ∀ j, Measurable (draws j))
    (hlaw : ∀ j, Q.map (draws j) = simulationInputLaw kind counts)
    (vDim : ℕ)
    (hdim : Causalean.Stat.Concentration.HasPseudoDimAtMost
      (fun (idx : A × tables × Option (Finset (Fin s × CategoricalStratum kind))) z =>
        if ncmCausalTableIndicator (repr idx.1) code idx.2.1.val a idx.2.2 z
          then (1 : ℝ) else 0) vDim)
    (henvelope : BooleanClassEnvelope
      (fun (idx : A × tables × Option (Finset (Fin s × CategoricalStratum kind))) =>
        ncmCausalTableIndicator (repr idx.1) code idx.2.1.val a idx.2.2) vDim),
    Q {w | ∃ r, ¬ wasserstein1 (observationalLaw (repr r).canonical.toEuclideanSCM)
        (empiricalMeasure (fun i => ncmEval (repr r) (draws i w))) ≤
          ENNReal.ofReal (2 * c + 8 * B * (delta + eps))} ≤
      ENNReal.ofReal (Real.exp
        (Ctail * ((1 + delta⁻¹) * Real.log (2 + delta⁻¹) +
          (vDim + 1 : ℝ) * Real.log (2 + eps⁻¹)) - ctail * m * eps^2)) := by
  obtain ⟨Ctail, ctail, hCtail, hctail, htail⟩ :=
    uniform_simulation_indicator_concentration_of_envelope hpacking hsquared
  refine ⟨Ctail, ctail, hCtail, hctail, ?_⟩
  intro counts F0 F1 bound A Omega _ repr s m hm code hcode tables selected a ha
    hcausal herr v c B delta eps hc hB hdelta heps hbound hvbound hread hevent
    Q _ draws hind hdraws hlaw vDim hdim henvelope
  letI := simulationInputLaw_probability kind counts
  let mu : ProbabilityMeasure (SimulationInput kind counts) :=
    ⟨simulationInputLaw kind counts, inferInstance⟩
  let indicator := fun (idx : A × tables × Option (Finset (Fin s × CategoricalStratum kind))) =>
    ncmCausalTableIndicator (repr idx.1) code idx.2.1.val a idx.2.2
  have hjoint : Q.map (fun w j => draws j w) =
      Measure.pi (fun _ : Fin m => (mu : Measure _)) := by
    rw [hind.map_fun_eq_pi_map (fun j => (hdraws j).aemeasurable)]
    congr 1
    funext j
    exact hlaw j
  apply le_trans (measure_mono (ncmCausalTable_sampling_failure_subset repr hm code hcode
    tables selected a ha hcausal herr v c B (delta + eps) hc hB (add_pos hdelta heps).le
    hbound hvbound hread hevent draws))
  apply le_trans (simulation_indicator_failure_measure_le_iid Q mu draws (by fun_prop)
    hjoint indicator (delta + eps))
  exact htail _ mu _ indicator vDim henvelope m hm
    delta eps hdelta heps

end
end Papers.TbsNeuralCausalPi
