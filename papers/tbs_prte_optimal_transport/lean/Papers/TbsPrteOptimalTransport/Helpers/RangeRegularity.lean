module
public import Papers.TbsPrteOptimalTransport.Helpers.Canonical
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.LocallyFinite
/-! Shared RangeRegularity proof obligations. -/
public section
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set
open scoped Classical ENNReal
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)
-- @node: continuous_of_finite_components
/-- On a topological space with finitely many connected components, if [a real-valued function is continuous on each connected component](hyp:hf), then [it is continuous on the whole space](goal). -/
lemma continuous_of_finite_components {A : Type*} [TopologicalSpace A]
    [Finite (ConnectedComponents A)] (f : A → ℝ)
    (hf : ∀ a, ContinuousOn f (connectedComponent a)) : Continuous f := by
  let C : ConnectedComponents A → Set A := fun q => ConnectedComponents.mk ⁻¹' {q}
  have hC (q : ConnectedComponents A) : ∃ a, C q = connectedComponent a := by
    obtain ⟨a, rfl⟩ := ConnectedComponents.surjective_coe q
    exact ⟨a, connectedComponents_preimage_singleton⟩
  apply (locallyFinite_of_finite C).continuous
  · ext a
    simp [C]
  · intro q
    obtain ⟨a, ha⟩ := hC q
    rw [ha]
    exact isClosed_connectedComponent
  · intro q
    obtain ⟨a, ha⟩ := hC q
    rw [ha]
    exact hf a

-- @node: compact_finite_components_rangeData
/-- If [a real set is compact](hyp:hR), [lies between zero and one inclusive](hyp:hunit), and has finitely many connected components, then [it admits a valid finite decomposition into ordered, strictly separated closed intervals within the unit interval](goal). -/
lemma compact_finite_components_rangeData (R : Set ℝ) (hR : IsCompact R)
    (hunit : R ⊆ Icc (0 : ℝ) 1) [Finite (ConnectedComponents R)] :
    ∃ D : RangeData, D.Valid R := by
  letI : CompactSpace R := isCompact_iff_compactSpace.mp hR
  let C : ConnectedComponents R → Set ℝ := fun q =>
    Subtype.val '' (ConnectedComponents.mk ⁻¹' {q})
  have hC (q : ConnectedComponents R) : IsConnected (C q) ∧ IsCompact (C q) := by
    obtain ⟨r, rfl⟩ := ConnectedComponents.surjective_coe q
    dsimp [C]
    rw [connectedComponents_preimage_singleton]
    exact ⟨isConnected_connectedComponent.image _ continuous_subtype_val.continuousOn,
      isClosed_connectedComponent.isCompact.image continuous_subtype_val⟩
  have hsub (q : ConnectedComponents R) : C q ⊆ R := by
    rintro y ⟨r, _, rfl⟩
    exact r.property
  have hinterval (q : ConnectedComponents R) :
      C q = Icc (sInf (C q)) (sSup (C q)) :=
    eq_Icc_of_connected_compact (hC q).1 (hC q).2
  have hlo (q : ConnectedComponents R) : sInf (C q) ∈ C q :=
    (hC q).2.sInf_mem (hC q).1.nonempty
  have hhi (q : ConnectedComponents R) : sSup (C q) ∈ C q :=
    (hC q).2.sSup_mem (hC q).1.nonempty
  have hunique {q q' : ConnectedComponents R} {y : ℝ}
      (hy : y ∈ C q) (hy' : y ∈ C q') : q = q' := by
    obtain ⟨r, hr, hry⟩ := hy
    obtain ⟨r', hr', hr'y⟩ := hy'
    have he : r = r' := Subtype.ext (hry.trans hr'y.symm)
    exact hr.symm.trans (he ▸ hr')
  let lows := (Set.finite_range (fun q : ConnectedComponents R => sInf (C q))).toFinset
  let e := lows.orderIsoOfFin rfl
  have hrep (a : lows) : ∃ q, sInf (C q) = a.val := by
    have ha : a.val ∈ range (fun q : ConnectedComponents R => sInf (C q)) := by
      exact (Set.Finite.mem_toFinset _).mp a.property
    exact ha
  let rep : lows → ConnectedComponents R := fun a => Classical.choose (hrep a)
  have hrep_eq (a : lows) : sInf (C (rep a)) = a.val := Classical.choose_spec (hrep a)
  let D : RangeData := ⟨lows.card, (fun i => (e i).val), (fun i => sSup (C (rep (e i))))⟩
  refine ⟨D, ?_, ?_, ?_⟩
  · intro i
    have hl := hunit (hsub _ (hlo (rep (e i))))
    have hh := hunit (hsub _ (hhi (rep (e i))))
    have hlh := (hinterval (rep (e i))).subset (hlo (rep (e i)))
    change 0 ≤ (e i).val ∧ (e i).val ≤ sSup (C (rep (e i))) ∧ _
    rw [← hrep_eq]
    exact ⟨hl.1, hlh.2, hh.2⟩
  · intro i j hij
    have hlow : (e i).val < (e j).val := e.strictMono hij
    change sSup (C (rep (e i))) < (e j).val
    by_contra hn
    have hy : (e j).val ∈ C (rep (e i)) := by
      rw [hinterval, mem_Icc, hrep_eq]
      exact ⟨hlow.le, le_of_not_gt hn⟩
    have hy' : (e j).val ∈ C (rep (e j)) := by
      rw [← hrep_eq]
      exact hlo _
    have he := hunique hy hy'
    have : (e i).val = (e j).val := by
      rw [← hrep_eq (e i), ← hrep_eq (e j), he]
    exact hlow.ne this
  · ext y
    constructor
    · intro hy
      let q := ConnectedComponents.mk (⟨y, hy⟩ : R)
      have hyl : y ∈ C q := ⟨⟨y, hy⟩, rfl, rfl⟩
      have hm : sInf (C q) ∈ lows := by simp [lows]
      let a : lows := ⟨sInf (C q), hm⟩
      have heq : rep a = q := by
        apply hunique (hlo (rep a))
        rw [hrep_eq]
        exact hlo q
      refine mem_iUnion.mpr ⟨e.symm a, ?_⟩
      change y ∈ Icc (e (e.symm a)).val (sSup (C (rep (e (e.symm a)))))
      simp only [e.apply_symm_apply]
      rw [← hrep_eq a, ← hinterval, heq]
      exact hyl
    · intro hy
      obtain ⟨i, hi⟩ := mem_iUnion.mp hy
      change y ∈ Icc (e i).val (sSup (C (rep (e i)))) at hi
      rw [← hrep_eq, ← hinterval] at hi
      exact hsub _ hi

-- @node: range_decomposition_valid
/-- If [the model satisfies the structural assumptions](hyp:h), [the instrument space has finitely many connected components](hyp:hfin), and [the propensity is continuous on each instrument component for almost every covariate value](hyp:hc), then [the canonical conditional range decomposition is valid for the instrument propensity range at almost every covariate value](goal). -/
lemma range_decomposition_valid (h : StructuralAssumptions M)
    (hfin : FiniteInstrumentComponents Z) (hc : PropensityContinuousOnComponents M) :
    ∀ᵐ x ∂xLaw M, (CondRangeDecomposition M x).Valid (range (fun z => M.prop z x)) := by
  letI : CompactSpace Z := h.2.2.2.2.2.2.2.2.2.1
  letI : Finite (ConnectedComponents Z) := hfin
  filter_upwards [hc] with x hx
  have hcont := continuous_of_finite_components (fun z => M.prop z x) hx
  let f : Z → range (fun z => M.prop z x) := fun z => ⟨M.prop z x, mem_range_self z⟩
  have hf : Continuous f := hcont.subtype_mk _
  have hsurj : Function.Surjective f := by
    rintro ⟨y, z, rfl⟩
    exact ⟨z, rfl⟩
  letI : Finite (ConnectedComponents (range (fun z => M.prop z x))) :=
    Finite.of_surjective hf.connectedComponentsMap (hf.connectedComponentsMap_surjective hsurj)
  have hcompact : IsCompact (range (fun z => M.prop z x)) := isCompact_range hcont
  have hunit : range (fun z => M.prop z x) ⊆ Icc (0 : ℝ) 1 := by
    rintro y ⟨z, rfl⟩
    exact M.rangeProp z x
  have hex := compact_finite_components_rangeData _ hcompact hunit
  change (RangeDecomposition (range (fun z => M.prop z x))).Valid _
  rw [RangeDecomposition, dif_pos hex]
  exact Classical.choose_spec hex
end Papers.TbsPrteOptimalTransport
