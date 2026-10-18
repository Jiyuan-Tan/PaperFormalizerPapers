module
public import Papers.TbsNeuralCausalPi.Helpers.ComponentLaws
public import Mathlib.Topology.Separation.Connected
/-! # Normalized singleton components of finite latent laws

Finite latent laws use zero-dimensional cube charts. Domination is proved for
the normalized restriction to each atom, rather than for the whole latent law.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped ENNReal NNReal
noncomputable section

-- @node: singletonCubeChart
/-- For [a point in the latent vector space](hyp:a), the [singleton cube chart](goal)
is the homeomorphism sending the unique point of the zero-dimensional unit cube to that point. -/
def singletonCubeChart {d : ℕ} (a : L1Vec d) :
    homeoClass (unitCube 0) ({a} : Set (L1Vec d)) where
  toFun := fun _ => ⟨a, Set.mem_singleton a⟩
  invFun := fun _ => ⟨0, by intro j; exact Fin.elim0 j⟩
  left_inv := fun _ => Subsingleton.elim _ _
  right_inv := fun _ => Subsingleton.elim _ _
  continuous_toFun := continuous_const
  continuous_invFun := continuous_const

-- @node: singletonCubeChart_lipschitz
/-- [The singleton cube chart has Lipschitz constant zero](goal). -/
lemma singletonCubeChart_lipschitz {d : ℕ} (a : L1Vec d) :
    LipschitzWith 0 (singletonCubeChart a) := by
  exact LipschitzWith.const _

-- @node: zeroDimensionalLebesgue_eq_dirac
/-- [The product of zero copies of Lebesgue measure, expressed in the
zero-dimensional latent vector space, is the point mass at zero](goal). -/
lemma zeroDimensionalLebesgue_eq_dirac :
    (Measure.pi (fun _ : Fin 0 => (volume : Measure ℝ))).map (WithLp.toLp 1) =
      Measure.dirac (0 : L1Vec 0) := by
  rw [Measure.pi_of_empty (x := (0 : Fin 0 → ℝ)), Measure.map_dirac]
  rfl

-- @node: cond_singleton_eq_dirac
/-- If [a singleton has nonzero mass under a finite measure](hyp:ha),
[normalizing the restriction to that singleton gives the point mass at its element](goal). -/
lemma cond_singleton_eq_dirac {d : ℕ} (P : Measure (L1Vec d))
    [IsFiniteMeasure P] (a : L1Vec d) (ha : P {a} ≠ 0) :
    ProbabilityTheory.cond P {a} = Measure.dirac a := by
  rw [ProbabilityTheory.cond, Measure.restrict_singleton, smul_smul,
    ENNReal.inv_mul_cancel ha (measure_ne_top P _), one_smul]

-- @node: singleton_lowerBoundDominationAt
/-- [The point mass at any latent vector satisfies lower-bound domination on
its singleton through the zero-dimensional cube chart, with Lipschitz constant
zero and domination constant one](goal). -/
lemma singleton_lowerBoundDominationAt {d : ℕ} (a : L1Vec d) :
    lowerBoundDominationAt (Measure.dirac a) {a} (singletonCubeChart a) 0 1 := by
  refine ⟨isCompact_singleton, by simp, zero_lt_one,
    singletonCubeChart_lipschitz a, ?_⟩
  intro B hB hcube
  rw [zeroDimensionalLebesgue_eq_dirac]
  by_cases hzero : (0 : L1Vec 0) ∈ B
  · have ha : a ∈ Subtype.val ''
        (singletonCubeChart a '' (Subtype.val ⁻¹' B)) := by
      refine ⟨⟨a, Set.mem_singleton a⟩, ?_, rfl⟩
      exact ⟨⟨0, by intro j; exact Fin.elim0 j⟩, hzero, rfl⟩
    simp [Measure.dirac_apply_of_mem ha, Measure.dirac_apply_of_mem hzero]
  · simp [Measure.dirac_apply' _ hB, hzero]

-- @node: normalized_singleton_generator_conditions
/-- If [an atom has nonzero mass under a finite measure](hyp:ha),
[its normalized conditional law satisfies both lower-bound domination and
vanishing pullback mass on the boundary in dimension zero, with Lipschitz constant zero](goal). -/
lemma normalized_singleton_generator_conditions {d : ℕ}
    (P : Measure (L1Vec d)) [IsFiniteMeasure P]
    (a : L1Vec d) (ha : P {a} ≠ 0) :
    LowerBoundDomination (d := 0) (ProbabilityTheory.cond P {a}) {a} 0 ∧
      PullbackVanishesOnBoundary (d := 0) (ProbabilityTheory.cond P {a}) {a} 0 := by
  rw [cond_singleton_eq_dirac P a ha]
  have hdom := singleton_lowerBoundDominationAt a
  exact ⟨⟨singletonCubeChart a, 1, hdom⟩,
    ⟨singletonCubeChart a, 1, hdom, by omega⟩⟩

-- @node: connectedComponentIn_finite_eq_singleton
/-- If [a set of latent vectors is finite](hyp:hS) and [a point belongs to it](hyp:ha),
[the connected component of that point within the set is its singleton](goal). -/
lemma connectedComponentIn_finite_eq_singleton {d : ℕ}
    {S : Set (L1Vec d)} (hS : S.Finite) {a : L1Vec d} (ha : a ∈ S) :
    connectedComponentIn S a = {a} := by
  have hfin := hS.subset (connectedComponentIn_subset S a)
  have hsub : (connectedComponentIn S a).Subsingleton := by
    intro x hx y hy
    by_contra hxy
    exact hfin.not_infinite
      ((isPreconnected_connectedComponentIn).infinite_of_nontrivial
        ⟨x, hx, y, hy, hxy⟩)
  apply Set.Subset.antisymm
  · intro x hx
    exact hsub hx (mem_connectedComponentIn ha)
  · exact Set.singleton_subset_iff.mpr (mem_connectedComponentIn ha)

-- @node: generatorRegular_of_finite_support
/-- If [a latent probability law has finite support](hyp:hfinite),
[it satisfies generator regularity](goal).

Its components are singletons, with zero-dimensional cube charts and lower
bounds for their normalized conditional laws. -/
lemma generatorRegular_of_finite_support {d : ℕ}
    (P : ProbabilityMeasure (L1Vec d))
    (hfinite : (measureSupport (P : Measure (L1Vec d))).Finite) :
    GeneratorRegular (P : Measure (L1Vec d)) := by
  classical
  let S := measureSupport (P : Measure (L1Vec d))
  let : Fintype S := hfinite.fintype
  let e := (Fintype.equivFin S).symm
  let a : Fin (Fintype.card S) → L1Vec d := fun i => (e i).val
  have ha (i) : a i ∈ S := (e i).property
  have hcharts : ComponentsLipschitzHomeomorphic (fun i => {a i}) (fun _ => 0) 0 :=
    fun i => ⟨singletonCubeChart (a i), singletonCubeChart_lipschitz (a i)⟩
  have hsupp : SupportFiniteComponents (P : Measure (L1Vec d)) (fun i => {a i}) := by
    refine ⟨?_, ?_, ?_⟩
    · apply Set.Subset.antisymm
      · intro x hx
        refine Set.mem_iUnion.mpr ⟨e.symm ⟨x, hx⟩, ?_⟩
        simp [a]
      · intro x hx
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        exact (Set.mem_singleton_iff.mp hi) ▸ ha i
    · intro i j hij
      apply e.injective
      apply Subtype.ext
      exact Set.singleton_injective hij
    · intro i
      exact ⟨a i, ha i, (connectedComponentIn_finite_eq_singleton hfinite (ha i)).symm⟩
  refine ⟨Fintype.card S, (fun i => {a i}), (fun _ => 0), 0, hsupp, hcharts, ?_⟩
  intro i
  exact normalized_singleton_generator_conditions (P : Measure (L1Vec d)) (a i)
    (ne_of_gt (support_component_mass_pos P hsupp hcharts i))

-- @node: generatorRegular_of_finite_carrier
/-- If [a carrying set is finite](hyp:hS) and [a latent probability law assigns
almost every vector to that set](hyp:hP), [the law satisfies generator regularity](goal). -/
lemma generatorRegular_of_finite_carrier {d : ℕ}
    (P : Measure (L1Vec d)) [IsProbabilityMeasure P]
    {S : Set (L1Vec d)} (hS : S.Finite) (hP : ∀ᵐ x ∂P, x ∈ S) :
    GeneratorRegular P := by
  apply generatorRegular_of_finite_support (⟨P, inferInstance⟩ : ProbabilityMeasure _)
  rw [measureSupport_eq_support]
  exact hS.subset (Measure.support_subset_of_isClosed hS.isClosed hP)

-- @node: generatorRegular_of_finite_coordinate_carriers
/-- If [each coordinate's allowed set of real values is finite](hyp:hS) and
[a latent probability law almost surely places every coordinate in its allowed set](hyp:hP),
[the law satisfies generator regularity](goal).

No independence between coordinates is required. -/
lemma generatorRegular_of_finite_coordinate_carriers {d : ℕ}
    (P : Measure (L1Vec d)) [IsProbabilityMeasure P]
    (S : Fin d → Set ℝ) (hS : ∀ j, (S j).Finite)
    (hP : ∀ᵐ x ∂P, ∀ j, x.ofLp j ∈ S j) :
    GeneratorRegular P := by
  have hfinite := (Set.Finite.pi' hS).image (WithLp.toLp 1)
  apply generatorRegular_of_finite_carrier P hfinite
  filter_upwards [hP] with x hx
  exact ⟨x.ofLp, hx, WithLp.toLp_ofLp 1 x⟩

-- @node: generatorRegular_of_binary_coordinates
/-- If [every coordinate of a latent probability vector is almost surely zero or one](hyp:hP),
[its law satisfies generator regularity](goal). -/
lemma generatorRegular_of_binary_coordinates {d : ℕ}
    (P : Measure (L1Vec d)) [IsProbabilityMeasure P]
    (hP : ∀ᵐ x ∂P, ∀ j, x.ofLp j = 0 ∨ x.ofLp j = 1) :
    GeneratorRegular P := by
  apply generatorRegular_of_finite_coordinate_carriers P (fun _ => {0, 1})
    (fun _ => Set.toFinite _)
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hP

-- @node: generatorRegular_map_of_finite_range
/-- If [a latent-vector-valued transformation is measurable](hyp:hf) and
[has finite range](hyp:hfinite), [pushing a probability law through it gives
a law satisfying generator regularity](goal). -/
lemma generatorRegular_map_of_finite_range {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (f : Ω → L1Vec d) (hf : Measurable f) (hfinite : (Set.range f).Finite) :
    GeneratorRegular (P.map f) := by
  let : IsProbabilityMeasure (P.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  apply generatorRegular_of_finite_carrier (P.map f) hfinite
  exact ae_map_mem_range f hfinite.measurableSet P

-- @node: latentLawsGeneratorRegular_of_finite_coordinate_carriers
/-- Given [allowed real-value sets for every coordinate of every private latent block](hyp:S),
if [all these sets are finite](hyp:hS) and [each block law almost surely places
its coordinates in their allowed sets](hyp:hM), [all latent block laws of the
canonical structural causal model satisfy generator regularity](goal). -/
lemma latentLawsGeneratorRegular_of_finite_coordinate_carriers
    {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
    {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
    {C : Fin b → Set (Fin n)} (M : CanonicalSCM kind dims dag G C)
    (S : ∀ j, Fin (dims j) → Set ℝ) (hS : ∀ j k, (S j k).Finite)
    (hM : ∀ j, ∀ᵐ x ∂(M.blockLaw j : Measure (L1Vec (dims j))), ∀ k, x.ofLp k ∈ S j k) :
    LatentLawsGeneratorRegular M := by
  intro j
  exact generatorRegular_of_finite_coordinate_carriers
    (M.blockLaw j : Measure (L1Vec (dims j))) (S j) (hS j) (hM j)

end
end Papers.TbsNeuralCausalPi
