module
public import Papers.TbsNeuralCausalPi.Setup.Assumptions.Generators
public import Mathlib.MeasureTheory.Measure.Support
/-! # Positive component laws and the finite support mixture

The compact charts separate the finitely many connected components. Every
component therefore has positive mass, and normalized restrictions recover
the original probability law exactly.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped ENNReal NNReal

-- @node: measureSupport_eq_support
/-- [The support defined by positive mass in every open neighborhood equals the usual
topological support](goal) of a measure on a finite-dimensional space. -/
lemma measureSupport_eq_support {d : ℕ} (P : Measure (L1Vec d)) :
    measureSupport P = P.support := by
  rw [Measure.support_eq_forall_isOpen]
  ext x
  exact ⟨fun h U hx hU => pos_iff_ne_zero.mpr (h U hU hx),
    fun h U hU hx => ne_of_gt (h U hx hU)⟩

-- @node: measureSupport_compl_null
/-- [The complement of the support has measure zero](goal) for any measure on a
finite-dimensional space. -/
lemma measureSupport_compl_null {d : ℕ} (P : Measure (L1Vec d)) :
    P (measureSupport P)ᶜ = 0 := by
  rw [measureSupport_eq_support]
  exact Measure.measure_compl_support

-- @node: unitCube_isCompact
/-- [The unit cube in any finite dimension is compact](goal). -/
lemma unitCube_isCompact (d : ℕ) : IsCompact (unitCube d) := by
  have hc := (isCompact_univ_pi (fun _ : Fin d =>
    isCompact_Icc (a := (0 : ℝ)) (b := 1))).image
    (PiLp.continuous_toLp (p := (1 : ENNReal)) (β := fun _ : Fin d => ℝ))
  convert hc using 1
  ext x
  constructor
  · intro hx
    exact ⟨x.ofLp, fun j _ => hx j, WithLp.toLp_ofLp 1 x⟩
  · rintro ⟨y, hy, rfl⟩
    exact fun j => hy j (Set.mem_univ j)

-- @node: component_isCompact
/-- If [each member of a finite family of sets has a Lipschitz homeomorphism
with a unit cube](hyp:hcharts), then [each such set is compact](goal). -/
lemma component_isCompact {d N : ℕ} {S : Fin N → Set (L1Vec d)}
    {dC : Fin N → ℕ} {L : ℝ≥0}
    (hcharts : ComponentsLipschitzHomeomorphic S dC L) (i : Fin N) :
    IsCompact (S i) := by
  obtain ⟨f, hf⟩ := hcharts i
  let : CompactSpace (unitCube (dC i)) :=
    isCompact_iff_compactSpace.mp (unitCube_isCompact (dC i))
  have hc := isCompact_range (continuous_subtype_val.comp f.continuous)
  have hr : Set.range (fun x => (f x).val) = S i := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (f x).property
    · intro hy
      exact ⟨f.symm ⟨y, hy⟩, congrArg Subtype.val (f.apply_symm_apply _)⟩
  exact hr ▸ hc

-- @node: support_components_pairwise_disjoint
/-- If [a finite family lists the distinct connected components of a measure's
support](hyp:hsupp), then [any two differently indexed components are disjoint](goal). -/
lemma support_components_pairwise_disjoint {d N : ℕ}
    {P : Measure (L1Vec d)} {S : Fin N → Set (L1Vec d)}
    (hsupp : SupportFiniteComponents P S) :
    Pairwise (fun i j => Disjoint (S i) (S j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro z hzi hzj
  obtain ⟨x, hx, hix⟩ := hsupp.2.2 i
  obtain ⟨y, hy, hjy⟩ := hsupp.2.2 j
  have heq : S i = S j := by
    rw [hix, hjy]
    exact (connectedComponentIn_eq (hix ▸ hzi)).trans
      (connectedComponentIn_eq (hjy ▸ hzj)).symm
  exact hij (hsupp.2.1 heq)

-- @node: support_component_mass_pos
/-- If [a finite family lists the distinct connected components of a probability
law's support](hyp:hsupp) and [each component is Lipschitz homeomorphic to a unit
cube](hyp:hcharts), then [every component has strictly positive probability](goal). -/
lemma support_component_mass_pos {d N : ℕ}
    (P : ProbabilityMeasure (L1Vec d)) {S : Fin N → Set (L1Vec d)}
    {dC : Fin N → ℕ} {L : ℝ≥0}
    (hsupp : SupportFiniteComponents (P : Measure _) S)
    (hcharts : ComponentsLipschitzHomeomorphic S dC L) (i : Fin N) :
    0 < (P : Measure _) (S i) := by
  classical
  obtain ⟨x, hx, hix⟩ := hsupp.2.2 i
  have hxi : x ∈ S i := hix.symm ▸ mem_connectedComponentIn hx
  have hdis := support_components_pairwise_disjoint hsupp
  let O : Set (L1Vec d) := ⋃ j : {j : Fin N // j ≠ i}, S j.val
  have hO : IsClosed O := isClosed_iUnion_of_finite fun j =>
    (component_isCompact hcharts j.val).isClosed
  have hxO : x ∈ Oᶜ := by
    intro h
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h
    exact Set.disjoint_left.mp (hdis j.property) hj hxi
  apply pos_iff_ne_zero.mpr
  intro hzero
  have hsub : Oᶜ ⊆ S i ∪ (measureSupport (P : Measure _))ᶜ := by
    intro y hy
    by_cases hys : y ∈ measureSupport (P : Measure _)
    · rw [hsupp.1] at hys
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hys
      by_cases hji : j = i
      · exact Or.inl (hji ▸ hj)
      · exact (hy (Set.mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)).elim
    · exact Or.inr hys
  have hnull : (P : Measure _) Oᶜ = 0 := measure_mono_null hsub
    (measure_union_null hzero (measureSupport_compl_null _))
  exact hx Oᶜ hO.isOpen_compl hxO hnull

-- @node: support_components_restrict_sum
/-- If [a finite family lists the distinct connected components of a probability
law's support](hyp:hsupp) and [each component is Lipschitz homeomorphic to a unit
cube](hyp:hcharts), then [the law equals the sum of its restrictions to those
components](goal). -/
lemma support_components_restrict_sum {d N : ℕ}
    (P : ProbabilityMeasure (L1Vec d)) {S : Fin N → Set (L1Vec d)}
    {dC : Fin N → ℕ} {L : ℝ≥0}
    (hsupp : SupportFiniteComponents (P : Measure _) S)
    (hcharts : ComponentsLipschitzHomeomorphic S dC L) :
    (P : Measure _) = ∑ i, (P : Measure _).restrict (S i) := by
  let : BorelSpace (L1Vec d) := ⟨rfl⟩
  have ha : ∀ᵐ x ∂(P : Measure _), x ∈ ⋃ i, S i := by
    rw [← hsupp.1, measureSupport_eq_support]
    exact Measure.support_mem_ae
  calc
    (P : Measure _) = (P : Measure _).restrict (⋃ i, S i) :=
      (Measure.restrict_eq_self_of_ae_mem ha).symm
    _ = ∑ i, (P : Measure _).restrict (S i) := by
      rw [Measure.restrict_iUnion (support_components_pairwise_disjoint hsupp)
        (fun i => (component_isCompact hcharts i).measurableSet), Measure.sum_fintype]

-- @node: support_component_masses_sum
/-- If [a finite family lists the distinct connected components of a probability
law's support](hyp:hsupp) and [each component is Lipschitz homeomorphic to a unit
cube](hyp:hcharts), then [the component probabilities sum to one](goal). -/
lemma support_component_masses_sum {d N : ℕ}
    (P : ProbabilityMeasure (L1Vec d)) {S : Fin N → Set (L1Vec d)}
    {dC : Fin N → ℕ} {L : ℝ≥0}
    (hsupp : SupportFiniteComponents (P : Measure _) S)
    (hcharts : ComponentsLipschitzHomeomorphic S dC L) :
    ∑ i, (P : Measure _) (S i) = 1 := by
  have h := congrArg (fun mu : Measure (L1Vec d) => mu Set.univ)
    (support_components_restrict_sum P hsupp hcharts)
  simpa only [measure_univ, Measure.finsetSum_apply,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] using h.symm

-- @node: support_component_real_masses
/-- If [a finite family lists the distinct connected components of a probability
law's support](hyp:hsupp) and [each component is Lipschitz homeomorphic to a unit
cube](hyp:hcharts), then [their probabilities, viewed as real numbers, are all
strictly positive and sum to one](goal). -/
lemma support_component_real_masses {d N : ℕ}
    (P : ProbabilityMeasure (L1Vec d)) {S : Fin N → Set (L1Vec d)}
    {dC : Fin N → ℕ} {L : ℝ≥0}
    (hsupp : SupportFiniteComponents (P : Measure _) S)
    (hcharts : ComponentsLipschitzHomeomorphic S dC L) :
    (∀ i, 0 < ((P : Measure _) (S i)).toReal) ∧
      (∑ i, ((P : Measure _) (S i)).toReal) = 1 := by
  constructor
  · intro i
    exact ENNReal.toReal_pos (ne_of_gt (support_component_mass_pos P hsupp hcharts i))
      (measure_ne_top _ _)
  · rw [← ENNReal.toReal_sum (fun i _ => measure_ne_top (P : Measure _) (S i)),
      support_component_masses_sum P hsupp hcharts, ENNReal.toReal_one]

-- @node: support_component_cond_probability
/-- If [a finite family lists the distinct connected components of a probability
law's support](hyp:hsupp) and [each component is Lipschitz homeomorphic to a unit
cube](hyp:hcharts), then [conditioning the law on any component yields a
probability measure](goal). -/
lemma support_component_cond_probability {d N : ℕ}
    (P : ProbabilityMeasure (L1Vec d)) {S : Fin N → Set (L1Vec d)}
    {dC : Fin N → ℕ} {L : ℝ≥0}
    (hsupp : SupportFiniteComponents (P : Measure _) S)
    (hcharts : ComponentsLipschitzHomeomorphic S dC L) (i : Fin N) :
    IsProbabilityMeasure (ProbabilityTheory.cond (P : Measure _) (S i)) := by
  exact ProbabilityTheory.cond_isProbabilityMeasure
    (ne_of_gt (support_component_mass_pos P hsupp hcharts i))

-- @node: support_components_cond_mixture
/-- If [a finite family lists the distinct connected components of a probability
law's support](hyp:hsupp) and [each component is Lipschitz homeomorphic to a unit
cube](hyp:hcharts), then [the original law is the mixture of its conditional
component laws, weighted by the component probabilities](goal). -/
lemma support_components_cond_mixture {d N : ℕ}
    (P : ProbabilityMeasure (L1Vec d)) {S : Fin N → Set (L1Vec d)}
    {dC : Fin N → ℕ} {L : ℝ≥0}
    (hsupp : SupportFiniteComponents (P : Measure _) S)
    (hcharts : ComponentsLipschitzHomeomorphic S dC L) :
    (P : Measure _) = ∑ i, ENNReal.ofReal (((P : Measure _) (S i)).toReal) •
      ProbabilityTheory.cond (P : Measure _) (S i) := by
  conv_lhs => rw [support_components_restrict_sum P hsupp hcharts]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _), ProbabilityTheory.cond,
    smul_smul, ENNReal.mul_inv_cancel
      (ne_of_gt (support_component_mass_pos P hsupp hcharts i)) (measure_ne_top _ _),
    one_smul]

-- @node: exists_normalized_component_laws
/-- If [a finite family lists the distinct connected components of a probability
law's support](hyp:hsupp) and [each component is Lipschitz homeomorphic to a unit
cube](hyp:hcharts), then [there exist probability laws equal to the conditional
laws on those components, with strictly positive component weights forming a
probability vector, each assigning probability one to its component, whose
weighted mixture is the original law](goal). -/
lemma exists_normalized_component_laws {d N : ℕ}
    (P : ProbabilityMeasure (L1Vec d)) {S : Fin N → Set (L1Vec d)}
    {dC : Fin N → ℕ} {L : ℝ≥0}
    (hsupp : SupportFiniteComponents (P : Measure _) S)
    (hcharts : ComponentsLipschitzHomeomorphic S dC L) :
    ∃ mu : Fin N → ProbabilityMeasure (L1Vec d),
      (∀ i, (mu i : Measure (L1Vec d)) = ProbabilityTheory.cond (P : Measure _) (S i)) ∧
      (∀ i, 0 < ((P : Measure _) (S i)).toReal) ∧
      (fun i => ((P : Measure _) (S i)).toReal) ∈ stdSimplex ℝ (Fin N) ∧
      (∀ i, (mu i : Measure (L1Vec d)) (S i) = 1) ∧
      (P : Measure _) = ∑ i, ENNReal.ofReal (((P : Measure _) (S i)).toReal) •
        (mu i : Measure (L1Vec d)) := by
  let mu : Fin N → ProbabilityMeasure (L1Vec d) := fun i =>
    ⟨ProbabilityTheory.cond (P : Measure _) (S i),
      support_component_cond_probability P hsupp hcharts i⟩
  have hp := support_component_real_masses P hsupp hcharts
  refine ⟨mu, fun i => rfl, hp.1, ⟨fun i => (hp.1 i).le, hp.2⟩, ?_, ?_⟩
  · intro i
    exact ProbabilityTheory.cond_apply_self
      (ne_of_gt (support_component_mass_pos P hsupp hcharts i)) (measure_ne_top _ _)
  · exact support_components_cond_mixture P hsupp hcharts

end Papers.TbsNeuralCausalPi
