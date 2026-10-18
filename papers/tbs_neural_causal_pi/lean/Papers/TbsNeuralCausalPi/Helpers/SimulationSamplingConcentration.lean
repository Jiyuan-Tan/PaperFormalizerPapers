module
public import Papers.TbsNeuralCausalPi.Helpers.SimulationTableAmbiguity
public import Papers.TbsNeuralCausalPi.Helpers.SimulationIndicatorConcentration
public import Papers.TbsNeuralCausalPi.Setup.EmpiricalAdmissibility
/-! # Concentration of complete observed simulations

One scalar class contains every ambiguity indicator and every subset of the
finite table types. Its pseudo-dimension remains a separate complexity
obligation. Given that bound, the established finite-table transport argument
and the uniform Wasserstein theorem yield an exponential sampling bound for
the actual canonical observational laws on the common IID exogenous draws.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

/-- Given [a representation-dependent finite type assignment](hyp:typeOf),
[a representation-dependent ambiguity event](hyp:E), [a representation paired
with either no subset or a subset of types](hyp:a), and [an input point](hyp:x),
[the table sampling indicator](goal) reports [membership in the ambiguity
event when no subset is selected](step:1), or [membership of the input's type
in the selected subset otherwise](step:2). -/
-- @node: tableSamplingIndicator
def tableSamplingIndicator {X R : Type*} {k : ℕ}
    (typeOf : R → X → Fin k) (E : R → Set X)
    (a : R × Option (Finset (Fin k))) (x : X) : Bool := by
  classical
  exact match a.2 with
    | none => if x ∈ E a.1 then true else false
    | some s => if typeOf a.1 x ∈ s then true else false

-- @node: tableSamplingIndicator_measurable
/-- If [each representation's type assignment is measurable](hyp:htype) and
[each representation's ambiguity event is measurable](hyp:hE), then [the
table sampling indicator for any fixed representation and subset choice
is a measurable function of the input](goal). -/
@[fun_prop] lemma tableSamplingIndicator_measurable
    {X R : Type*} [MeasurableSpace X] {k : ℕ}
    (typeOf : R → X → Fin k) (E : R → Set X)
    (htype : ∀ r, Measurable (typeOf r)) (hE : ∀ r, MeasurableSet (E r))
    (a : R × Option (Finset (Fin k))) : Measurable (tableSamplingIndicator typeOf E a) := by
  first | fun_prop | skip
  rcases a with ⟨r, _ | s⟩
  · exact Measurable.ite (hE r) measurable_const measurable_const
  · exact Measurable.ite ((htype r) (Set.toFinite _).measurableSet)
      measurable_const measurable_const

/-- If [each representation's type assignment is measurable](hyp:htype) and
[each representation's ambiguity event is measurable](hyp:hE), then [every
sample outcome for which some ambiguity-event frequency or some subset-of-types
frequency differs from its population measure by more than e also has a table
sampling indicator whose empirical mean differs from its population integral
by more than e](goal). -/
-- @node: table_indicator_failure_subset_mean_failure
lemma table_indicator_failure_subset_mean_failure
    {X R Omega : Type*} [MeasurableSpace X] {k m : ℕ}
    (mu : Measure X) [IsFiniteMeasure mu]
    (typeOf : R → X → Fin k) (E : R → Set X)
    (htype : ∀ r, Measurable (typeOf r)) (hE : ∀ r, MeasurableSet (E r))
    (draws : Fin m → Omega → X) (e : ℝ) :
    {w | ∃ r,
      (¬ |mu.real (E r) - (m : ℝ)⁻¹ *
          ∑ j, (E r).indicator (fun _ => (1 : ℝ)) (draws j w)| ≤ e ∨
        ∃ s : Finset (Fin k), ¬ |mu.real (typeOf r ⁻¹' (s : Set (Fin k))) -
          (m : ℝ)⁻¹ * ∑ j, if typeOf r (draws j w) ∈ s then (1 : ℝ) else 0| ≤ e)} ⊆
      {w | ∃ a : R × Option (Finset (Fin k)), e <
        |(∫ y, (if tableSamplingIndicator typeOf E a y then (1 : ℝ) else 0) ∂mu) -
          (m : ℝ)⁻¹ * ∑ j,
            if tableSamplingIndicator typeOf E a (draws j w) then (1 : ℝ) else 0|} := by
  classical
  rintro w ⟨r, h | ⟨s, h⟩⟩
  · refine ⟨(r, none), ?_⟩
    have heq : (fun y => if tableSamplingIndicator typeOf E (r, none) y then (1 : ℝ) else 0) =
        (E r).indicator (fun _ => (1 : ℝ)) := by
      funext y
      simp [tableSamplingIndicator, Set.indicator]
    have hint : (∫ y, (if tableSamplingIndicator typeOf E (r, none) y then (1 : ℝ) else 0) ∂mu) =
        mu.real (E r) := by
      rw [heq]
      exact integral_indicator_one (hE r)
    rw [hint]
    simpa [tableSamplingIndicator, Set.indicator] using lt_of_not_ge h
  · refine ⟨(r, some s), ?_⟩
    have heq : (fun y => if tableSamplingIndicator typeOf E (r, some s) y then (1 : ℝ) else 0) =
        (typeOf r ⁻¹' (s : Set (Fin k))).indicator (fun _ => (1 : ℝ)) := by
      funext y
      simp [tableSamplingIndicator, Set.indicator]
    have hs : MeasurableSet (typeOf r ⁻¹' (s : Set (Fin k))) :=
      (htype r) (Set.toFinite _).measurableSet
    have hint : (∫ y, (if tableSamplingIndicator typeOf E (r, some s) y then (1 : ℝ) else 0) ∂mu) =
        mu.real (typeOf r ⁻¹' (s : Set (Fin k))) := by
      rw [heq]
      exact integral_indicator_one hs
    rw [hint]
    simpa [tableSamplingIndicator] using lt_of_not_ge h

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)} {C : Fin b → Set (Fin n)}

/-- Assuming [the Anthony–Bartlett packing bound](hyp:hpacking) and [the
Anthony–Bartlett squared-loss bound](hyp:hsquared), [there are positive
constants Ctail and c giving the following uniform simulation bound: for
independent measurable draws with the simulation input law, compactly
supported model outputs and table values, nonnegative approximation error a
and table diameter B, positive δ and ε, measurable Borel-parametrized table
indicators of pseudo-dimension at most vDim, and a table approximation with
error at most a outside an ambiguity event of probability at most δ + ε and
error at most a + B inside it, the probability that any admissible model's
empirical observational law has Wasserstein distance greater than
2a + 4B(δ + ε) from its population law is at most
exp(Ctail((1 + 1/δ) log(2 + 1/δ) + (vDim + 1) log(2 + 1/ε)) − c m ε²),
where m is the positive number of draws](goal). -/
-- @node: ncmEval_sampling_concentration_of_table_pseudodim
lemma ncmEval_sampling_concentration_of_table_pseudodim
    (hpacking : AnthonyBartlettPacking) (hsquared : AnthonyBartlettSquaredLoss) :
    ∃ Ctail c : ℝ, 0 < Ctail ∧ 0 < c ∧
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
    (vDim : ℕ)
    (hdim : Causalean.Stat.Concentration.HasPseudoDimAtMost
      (fun i : {R // admissible R} × Option (Finset (Fin k)) => fun z =>
        if tableSamplingIndicator (fun R : {R // admissible R} => typeOf R.val)
          (fun R => E R.val) i z then (1 : ℝ) else 0) vDim),
      Q {w | ∃ R, admissible R ∧
        ¬ wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
          (empiricalMeasure (fun i => ncmEval R (draws i w))) ≤
            ENNReal.ofReal (2 * a + 4 * B * (delta + eps))} ≤
        ENNReal.ofReal (Real.exp
          (Ctail * ((1 + delta⁻¹) * Real.log (2 + delta⁻¹) +
            (vDim + 1 : ℝ) * Real.log (2 + eps⁻¹)) - c * m * eps^2)) := by
  classical
  obtain ⟨Ctail, c, hC, hc, htail⟩ := uniform_simulation_indicator_concentration hpacking hsquared
  refine ⟨Ctail, c, hC, hc, ?_⟩
  intro counts F0 F1 Omega _ Q _ k m hm admissible typeOf v E draws hind hdraws hlaw
    S hS a B delta eps ha hB hdelta heps htype hE hparam hfrange hvrange hdiam herr hprob vDim hdim
  letI := simulationInputLaw_probability kind counts
  let mu : ProbabilityMeasure (SimulationInput kind counts) :=
    ⟨simulationInputLaw kind counts, inferInstance⟩
  let T := fun R : {R // admissible R} => typeOf R.val
  let A := fun R : {R // admissible R} => E R.val
  have hT : ∀ R, Measurable (T R) := fun R => htype R.val R.property
  have hA : ∀ R, MeasurableSet (A R) := fun R => hE R.val R.property
  apply le_trans (ncmEval_sampling_failure_le_indicator_failure Q hm admissible typeOf v E
    draws S hS a B (delta + eps) ha hB (add_pos hdelta heps).le
    htype hE hfrange hvrange hdiam herr hprob)
  have hjoint : Q.map (fun w j => draws j w) =
      Measure.pi (fun _ : Fin m => (mu : Measure _)) := by
    rw [hind.map_fun_eq_pi_map (fun j => (hdraws j).aemeasurable)]
    congr 1
    funext j
    exact hlaw j
  apply le_trans (measure_mono ?_)
    ((simulation_indicator_failure_measure_le_iid Q mu draws (by fun_prop) hjoint
      (tableSamplingIndicator T A) (delta + eps)).trans
        (htail _ mu _ (tableSamplingIndicator T A) vDim hdim
          (tableSamplingIndicator_measurable T A hT hA) hparam m hm delta eps hdelta heps))
  rintro w ⟨R, hR, hbad⟩
  apply table_indicator_failure_subset_mean_failure (simulationInputLaw kind counts)
    T A hT hA draws (delta + eps)
  exact ⟨⟨R, hR⟩, hbad⟩

end
end Papers.TbsNeuralCausalPi
