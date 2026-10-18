module
public import Papers.TbsPrteOptimalTransport.Helpers.RangeRegularity
public import Papers.TbsPrteOptimalTransport.Helpers.EssentialRanges
public import Mathlib.Order.Preorder.Finite
/-! Measurable versions of finite ordered propensity ranges. -/
public section
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)

-- @node: measurable_component_extrema_versions
/-- Under [the model's structural assumptions](hyp:h), if [the propensity is continuous on each
instrument component for almost every covariate value](hyp:hc) and [the instrument space has finitely
many connected components](hyp:hfin), [there are measurable lower and upper endpoint functions
equal, almost surely under the covariate law, to the infimum and supremum of the propensity on the
connected component containing the chosen instrument value](goal).

Full support and continuity identify essential extrema with pointwise extrema; finite components
make each component both open and closed. No countable dense subset is required. -/
lemma measurable_component_extrema_versions
    (h : StructuralAssumptions M) (hc : PropensityContinuousOnComponents M)
    (hfin : FiniteInstrumentComponents Z) (z0 : Z) :
    ∃ a b : X → ℝ, Measurable a ∧ Measurable b ∧
      ∀ᵐ x ∂xLaw M,
        a x = sInf ((fun z => M.prop z x) '' connectedComponent z0) ∧
        b x = sSup ((fun z => M.prop z x) '' connectedComponent z0) := by
  letI : Finite (ConnectedComponents Z) := hfin
  obtain ⟨κ, hκ, hversion, hfull⟩ := h.2.2.2.2.2.1
  letI : IsMarkovKernel κ := hκ
  have hC := finite_components_isOpen z0
  have hne : (connectedComponent z0).Nonempty := ⟨z0, mem_connectedComponent⟩
  have hm : Measurable (Function.uncurry M.prop) := h.2.2.2.1.2.1
  obtain ⟨b, hb, hbeq⟩ := measurable_full_support_supremum (xLaw M) κ hfull
    (connectedComponent z0) hC hne M.prop hm M.rangeProp
    (hc.mono fun x hx => hx z0)
  have hm' : Measurable (Function.uncurry (fun z x => 1 - M.prop z x)) := by
    fun_prop
  have hr' (z : Z) (x : X) : 1 - M.prop z x ∈ Icc (0 : ℝ) 1 := by
    have hr := M.rangeProp z x
    constructor <;> linarith [hr.1, hr.2]
  obtain ⟨c, hcmeas, hceq⟩ := measurable_full_support_supremum (xLaw M) κ hfull
    (connectedComponent z0) hC hne (fun z x => 1 - M.prop z x) hm' hr' (by
      filter_upwards [hc] with x hx
      exact continuousOn_const.sub (hx z0))
  refine ⟨fun x => 1 - c x, b, by fun_prop, hb, ?_⟩
  filter_upwards [hbeq, hceq] with x hbx hcx
  refine ⟨?_, hbx⟩
  rw [hcx]
  let R := (fun z => M.prop z x) '' connectedComponent z0
  let S := (fun z => 1 - M.prop z x) '' connectedComponent z0
  have hR : R.Nonempty := hne.image _
  have hS : S.Nonempty := hne.image _
  have hRb : BddBelow R := by
    refine ⟨0, ?_⟩
    rintro y ⟨z, hz, rfl⟩
    exact (M.rangeProp z x).1
  have hSb : BddAbove S := by
    refine ⟨1, ?_⟩
    rintro y ⟨z, hz, rfl⟩
    exact (hr' z x).2
  change 1 - sSup S = sInf R
  apply le_antisymm
  · apply le_csInf hR
    rintro y ⟨z, hz, rfl⟩
    have hs := le_csSup hSb (show 1 - M.prop z x ∈ S from ⟨z, hz, rfl⟩)
    linarith
  · have hs : sSup S ≤ 1 - sInf R := by
      apply csSup_le hS
      rintro y ⟨z, hz, rfl⟩
      have hi := csInf_le hRb (show M.prop z x ∈ R from ⟨z, hz, rfl⟩)
      linarith
    linarith

/-- Under [the model's structural assumptions](hyp:h), if [the propensity is continuous on each
instrument component for almost every covariate value](hyp:hc) and [there are finitely many
instrument components](hyp:hfin), [the propensity range on the component containing the chosen
instrument value is almost surely a closed interval with measurable endpoints, ordered between
zero and one](goal). -/
lemma measurable_component_interval_versions
    (h : StructuralAssumptions M) (hc : PropensityContinuousOnComponents M)
    (hfin : FiniteInstrumentComponents Z) (z0 : Z) :
    ∃ a b : X → ℝ, Measurable a ∧ Measurable b ∧
      ∀ᵐ x ∂xLaw M,
        (fun z => M.prop z x) '' connectedComponent z0 = Icc (a x) (b x) ∧
        0 ≤ a x ∧ a x ≤ b x ∧ b x ≤ 1 := by
  let C := connectedComponent z0
  letI : Nonempty C := ⟨⟨z0, mem_connectedComponent⟩⟩
  letI : CompactSpace Z := h.2.2.2.2.2.2.2.2.2.1
  let F : C → X → ℝ := fun z x => M.prop z.val x
  have hm (z : C) : Measurable (F z) := by
    first | fun_prop | exact h.2.2.2.1.2.1.comp (measurable_const.prodMk measurable_id)
  have hcont : ∀ᵐ x ∂xLaw M, Continuous (fun z : C => F z x) := by
    filter_upwards [hc] with x hx
    exact (hx z0).domRestrict
  obtain ⟨a, b, ha, hb, hab⟩ := measurable_component_extrema_versions M h hc hfin z0
  refine ⟨a, b, ha, hb, ?_⟩
  filter_upwards [hc, hab] with x hx heq
  have hcompact := isClosed_connectedComponent.isCompact.image_of_continuousOn (hx z0)
  have hconnected := isConnected_connectedComponent.image _ (hx z0)
  have hrange : range (fun z : C => F z x) = (fun z => M.prop z x) '' C := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z.val, z.property, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
  have hinterval := eq_Icc_of_connected_compact hconnected hcompact
  have ha_mem := hcompact.sInf_mem hconnected.nonempty
  have hb_mem := hcompact.sSup_mem hconnected.nonempty
  have hunit : (fun z => M.prop z x) '' C ⊆ Icc (0 : ℝ) 1 := by
    rintro y ⟨z, hz, rfl⟩
    exact M.rangeProp z x
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [heq.1, heq.2] using hinterval
  · simpa only [heq.1] using (hunit ha_mem).1
  · rw [heq.1, heq.2]
    exact (hinterval.subset ha_mem).2
  · simpa only [heq.2] using (hunit hb_mem).2

/-- Under [the model's structural assumptions](hyp:h), if [the propensity is continuous on each
instrument component for almost every covariate value](hyp:hc) and [the instrument space has finitely
many connected components](hyp:hfin), [there are measurable endpoint functions for every component
whose closed intervals almost surely cover exactly the full propensity range, with every lower
endpoint between zero and its upper endpoint and every upper endpoint at most one](goal). -/
lemma measurable_finite_component_range_versions
    (h : StructuralAssumptions M) (hc : PropensityContinuousOnComponents M)
    (hfin : FiniteInstrumentComponents Z) :
    ∃ a b : ConnectedComponents Z → X → ℝ,
      (∀ q, Measurable (a q) ∧ Measurable (b q)) ∧
      ∀ᵐ x ∂xLaw M,
        range (fun z => M.prop z x) = ⋃ q, Icc (a q x) (b q x) ∧
        ∀ q, 0 ≤ a q x ∧ a q x ≤ b q x ∧ b q x ≤ 1 := by
  letI : Finite (ConnectedComponents Z) := hfin
  choose rep hrep using (ConnectedComponents.surjective_coe :
    ∀ q : ConnectedComponents Z, ∃ z : Z, ConnectedComponents.mk z = q)
  choose a b ha hb hab using
    (fun q => measurable_component_interval_versions M h hc hfin (rep q))
  refine ⟨a, b, fun q => ⟨ha q, hb q⟩, ?_⟩
  filter_upwards [ae_all_iff.mpr hab] with x hx
  refine ⟨?_, fun q => (hx q).2⟩
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    refine mem_iUnion.mpr ⟨ConnectedComponents.mk z, ?_⟩
    rw [← (hx (ConnectedComponents.mk z)).1]
    refine ⟨z, ?_, rfl⟩
    exact ConnectedComponents.coe_eq_coe'.mp (hrep (ConnectedComponents.mk z)).symm
  · intro hy
    obtain ⟨q, hq⟩ := mem_iUnion.mp hy
    rw [← (hx q).1] at hq
    obtain ⟨z, hz, rfl⟩ := hq
    exact mem_range_self z

/-- If [an interval list represents a set as an ordered union of nonempty closed intervals in the
unit interval separated by strict gaps](hyp:hD), and [a real number belongs to one listed
interval](hyp:hi) and [also belongs to another listed interval](hyp:hj), [the two interval indices
are equal](goal). -/
lemma rangeData_index_eq_of_mem (D : RangeData) {R : Set ℝ} (hD : D.Valid R)
    {i j : Fin D.count} {y : ℝ}
    (hi : y ∈ Icc (D.2.1 i) (D.2.2 i))
    (hj : y ∈ Icc (D.2.1 j) (D.2.2 j)) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · have hs := hD.2.1 i j hij
    exact False.elim (not_lt_of_ge (hj.1.trans hi.2) hs)
  · exact hij
  · have hs := hD.2.1 j i hij
    exact False.elim (not_lt_of_ge (hi.1.trans hj.2) hs)

/-- Suppose [an interval list represents a set as an ordered union of nonempty closed intervals in
the unit interval separated by strict gaps](hyp:hD). If [a second set is connected, allowing the
empty set](hyp:hS), [is contained in the represented set](hyp:hsub), and [contains a point](hyp:hy)
that [lies in a chosen listed interval](hyp:hyi), [the entire second set is contained in that
interval](goal). -/
lemma rangeData_preconnected_subset (D : RangeData) {R S : Set ℝ}
    (hD : D.Valid R) (hS : IsPreconnected S) (hsub : S ⊆ R)
    (i : Fin D.count) {y : ℝ} (hy : y ∈ S)
    (hyi : y ∈ Icc (D.2.1 i) (D.2.2 i)) :
    S ⊆ Icc (D.2.1 i) (D.2.2 i) := by
  let T := ⋃ j : {j : Fin D.count // j ≠ i}, Icc (D.2.1 j.val) (D.2.2 j.val)
  have hT : IsClosed T := isClosed_iUnion_of_finite (fun _ => isClosed_Icc)
  have hdis : Disjoint (Icc (D.2.1 i) (D.2.2 i)) T := by
    apply disjoint_left.mpr
    intro z hz hzT
    obtain ⟨j, hj⟩ := mem_iUnion.mp hzT
    exact j.property (rangeData_index_eq_of_mem D hD hj hz)
  have hcover : S ⊆ Icc (D.2.1 i) (D.2.2 i) ∪ T := by
    intro z hz
    have hr := hsub hz
    rw [hD.2.2] at hr
    obtain ⟨j, hj⟩ := mem_iUnion.mp hr
    by_cases he : j = i
    · exact Or.inl (he ▸ hj)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨j, he⟩, hj⟩)
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hS _ _ isClosed_Icc hT
      hcover (by rw [hdis.inter_eq, inter_empty]) with hs | hs
  · exact hs
  · exact False.elim (disjoint_left.mp hdis hyi (hs hy))

/-- If [one list represents a set as an ordered union of nonempty closed intervals in the unit
interval separated by strict gaps](hyp:hD) and [a second list does so for the same set](hyp:hE),
[every interval in the first list has an interval in the second list with exactly the same lower
and upper endpoints](goal). -/
lemma rangeData_interval_match (D E : RangeData) {R : Set ℝ}
    (hD : D.Valid R) (hE : E.Valid R) (i : Fin D.count) :
    ∃ j : Fin E.count, D.2.1 i = E.2.1 j ∧ D.2.2 i = E.2.2 j := by
  have hi : D.2.1 i ≤ D.2.2 i := (hD.1 i).2.1
  have hlowR : D.2.1 i ∈ R := by
    rw [hD.2.2]
    exact mem_iUnion.mpr ⟨i, ⟨le_rfl, hi⟩⟩
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hE.2.2 ▸ hlowR)
  have hDE : Icc (D.2.1 i) (D.2.2 i) ⊆ Icc (E.2.1 j) (E.2.2 j) :=
    rangeData_preconnected_subset E hE isPreconnected_Icc
      (by rw [hD.2.2]; exact subset_iUnion (fun k : Fin D.1 => Icc (D.2.1 k) (D.2.2 k)) i)
      j ⟨le_rfl, hi⟩ hj
  have hjle : E.2.1 j ≤ E.2.2 j := (hE.1 j).2.1
  have hElowR : E.2.1 j ∈ R := by
    rw [hE.2.2]
    exact mem_iUnion.mpr ⟨j, ⟨le_rfl, hjle⟩⟩
  obtain ⟨l, hl⟩ := mem_iUnion.mp (hD.2.2 ▸ hElowR)
  have hED : Icc (E.2.1 j) (E.2.2 j) ⊆ Icc (D.2.1 l) (D.2.2 l) :=
    rangeData_preconnected_subset D hD isPreconnected_Icc
      (by rw [hE.2.2]; exact subset_iUnion (fun k : Fin E.1 => Icc (E.2.1 k) (E.2.2 k)) j)
      l ⟨le_rfl, hjle⟩ hl
  have hli : l = i := rangeData_index_eq_of_mem D hD (hED hj) ⟨le_rfl, hi⟩
  subst l
  exact ⟨j, le_antisymm (hED ⟨le_rfl, hjle⟩).1 (hDE ⟨le_rfl, hi⟩).1,
    le_antisymm (hDE ⟨hi, le_rfl⟩).2 (hED ⟨hjle, le_rfl⟩).2⟩

/-- If [an interval list represents a set as an ordered union of nonempty closed intervals in the
unit interval separated by strict gaps](hyp:hD), [its lower endpoints strictly increase with the
interval index](goal). -/
lemma rangeData_low_strictMono (D : RangeData) {R : Set ℝ} (hD : D.Valid R) :
    StrictMono D.2.1 := by
  intro i j hij
  exact lt_of_le_of_lt (hD.1 i).2.1 (hD.2.1 i j hij)

/-- If [one list represents a set as an ordered union of nonempty closed intervals in the unit
interval separated by strict gaps](hyp:hD) and [a second list gives such a representation of the
same set](hyp:hE), [the lists are identical, including their lengths and all endpoints](goal). -/
lemma rangeData_valid_unique (D E : RangeData) {R : Set ℝ}
    (hD : D.Valid R) (hE : E.Valid R) : D = E := by
  have hdl := rangeData_low_strictMono D hD
  have hel := rangeData_low_strictMono E hE
  choose f hf using rangeData_interval_match D E hD hE
  choose g hg using rangeData_interval_match E D hE hD
  have hfmono : StrictMono f := by
    intro i j hij
    apply hel.lt_iff_lt.mp
    rw [← (hf i).1, ← (hf j).1]
    exact hdl hij
  have hgmono : StrictMono g := by
    intro i j hij
    apply hdl.lt_iff_lt.mp
    rw [← (hg i).1, ← (hg j).1]
    exact hel hij
  have hcount : D.count = E.count := by
    apply Nat.le_antisymm
    · simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hfmono.injective
    · simpa only [Fintype.card_fin] using Fintype.card_le_of_injective g hgmono.injective
  rcases D with ⟨n, dl, dh⟩
  rcases E with ⟨m, el, eh⟩
  change n = m at hcount
  subst m
  have hfid : f = id := hfmono.eq_id
  have hlo : dl = el := by
    funext i
    have hi := (hf i).1
    change dl i = el (f i) at hi
    rw [hfid] at hi
    exact hi
  have hhi : dh = eh := by
    funext i
    have hi := (hf i).2
    change dh i = eh (f i) at hi
    rw [hfid] at hi
    exact hi
  cases hlo
  cases hhi
  rfl

/-- Given a finite family of closed intervals with [each lower endpoint at most its upper
endpoint](hyp:hab), suppose [an ordered list of nonempty closed intervals in the unit interval,
separated by strict gaps, represents their union](hyp:hD). Then [each listed lower endpoint can
be chosen from a distinct original interval's lower endpoint, each listed upper endpoint can be
chosen from an original upper endpoint, and the list has at most as many intervals as the original
family](goal). -/
lemma rangeData_endpoints_from_finite_union {J : Type*} [Fintype J]
    (a b : J → ℝ) (hab : ∀ j, a j ≤ b j) (D : RangeData)
    (hD : D.Valid (⋃ j, Icc (a j) (b j))) :
    ∃ l r : Fin D.count → J, Function.Injective l ∧
      (∀ k, D.2.1 k = a (l k) ∧ D.2.2 k = b (r k)) ∧
      D.count ≤ Fintype.card J := by
  have hleft (k : Fin D.count) : ∃ j, D.2.1 k = a j := by
    have hlow : D.2.1 k ∈ ⋃ j, Icc (a j) (b j) := by
      rw [hD.2.2]
      exact mem_iUnion.mpr ⟨k, ⟨le_rfl, (hD.1 k).2.1⟩⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp hlow
    have hs : Icc (a j) (b j) ⊆ Icc (D.2.1 k) (D.2.2 k) :=
      rangeData_preconnected_subset D hD isPreconnected_Icc
        (subset_iUnion (fun j => Icc (a j) (b j)) j)
        k hj ⟨le_rfl, (hD.1 k).2.1⟩
    exact ⟨j, le_antisymm (hs ⟨le_rfl, hab j⟩).1 hj.1⟩
  have hright (k : Fin D.count) : ∃ j, D.2.2 k = b j := by
    have hhigh : D.2.2 k ∈ ⋃ j, Icc (a j) (b j) := by
      rw [hD.2.2]
      exact mem_iUnion.mpr ⟨k, ⟨(hD.1 k).2.1, le_rfl⟩⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp hhigh
    have hs : Icc (a j) (b j) ⊆ Icc (D.2.1 k) (D.2.2 k) :=
      rangeData_preconnected_subset D hD isPreconnected_Icc
        (subset_iUnion (fun j => Icc (a j) (b j)) j)
        k hj ⟨(hD.1 k).2.1, le_rfl⟩
    exact ⟨j, le_antisymm hj.2 (hs ⟨hab j, le_rfl⟩).2⟩
  choose l hl using hleft
  choose r hr using hright
  have hinj : Function.Injective l := by
    intro i j hij
    apply (rangeData_low_strictMono D hD).injective
    rw [hl i, hl j, hij]
  exact ⟨l, r, hinj, fun k => ⟨hl k, hr k⟩,
    by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective l hinj⟩

/- Rational tests determine the nondegenerate intervals; endpoint tests retain
   singleton components, which rational tests alone would miss. -/
/-- If [a set of real numbers is closed](hyp:hS), [contains the proposed interval's lower
endpoint](hyp:ha), and [contains every rational number in the closed interval between the two
endpoints](hyp:hq), [it contains that entire closed interval](goal). -/
lemma interval_subset_closed_of_rational_tests {S : Set ℝ} (hS : IsClosed S)
    (a b : ℝ) (ha : a ∈ S)
    (hq : ∀ q : ℚ, (q : ℝ) ∈ Icc a b → (q : ℝ) ∈ S) : Icc a b ⊆ S := by
  by_cases hab : a = b
  · subst b
    simpa only [Icc_self, singleton_subset_iff] using ha
  · have hrat : range (fun q : ℚ => (q : ℝ)) ∩ Ioo a b ⊆ S := by
      rintro y ⟨⟨q, rfl⟩, hq'⟩
      exact hq q ⟨hq'.1.le, hq'.2.le⟩
    have hd := (Rat.denseRange_cast : Dense (range (fun q : ℚ => (q : ℝ)))).open_subset_closure_inter
      (isOpen_Ioo : IsOpen (Ioo a b))
    have hi : Ioo a b ⊆ S := hd.trans (closure_minimal (by simpa [inter_comm] using hrat) hS)
    rw [← closure_Ioo hab]
    exact closure_minimal hi hS

/-- For a family of closed intervals with [each lower endpoint at most its upper endpoint](hyp:hab)
and a finite target family of closed intervals, [the first union is contained in the target union
if and only if every lower endpoint of the first family and every rational number in its union
belong to the target union](goal). -/
lemma finite_interval_union_subset_iff {J K : Type*} [Finite K]
    (a b : J → ℝ) (c d : K → ℝ) (hab : ∀ j, a j ≤ b j) :
    (⋃ j, Icc (a j) (b j)) ⊆ (⋃ k, Icc (c k) (d k)) ↔
      (∀ j, a j ∈ ⋃ k, Icc (c k) (d k)) ∧
      (∀ q : ℚ, (q : ℝ) ∈ (⋃ j, Icc (a j) (b j)) →
        (q : ℝ) ∈ ⋃ k, Icc (c k) (d k)) := by
  constructor
  · intro hs
    exact ⟨fun j => hs (mem_iUnion.mpr ⟨j, ⟨le_rfl, hab j⟩⟩),
      fun q hq => hs hq⟩
  · rintro ⟨ha, hq⟩ y hy
    obtain ⟨j, hj⟩ := mem_iUnion.mp hy
    exact interval_subset_closed_of_rational_tests
      (isClosed_iUnion_of_finite (fun _ => isClosed_Icc)) (a j) (b j) (ha j)
      (fun q hq' => hq q (mem_iUnion.mpr ⟨j, hq'⟩)) hj

/-- For a countable family of closed intervals depending on an underlying observation, if
[each lower endpoint is measurable](hyp:ha), [each upper endpoint is measurable](hyp:hb), and
[the real-valued quantity being tested is measurable](hyp:hy), [the observations where that
quantity belongs to the interval union form a measurable set](goal). -/
lemma measurableSet_mem_finite_interval_union {B J : Type*}
    [MeasurableSpace B] [Countable J] (a b : J → B → ℝ) (y : B → ℝ)
    (ha : ∀ j, Measurable (a j)) (hb : ∀ j, Measurable (b j)) (hy : Measurable y) :
    MeasurableSet {x | y x ∈ ⋃ j, Icc (a j x) (b j x)} := by
  simp only [mem_iUnion, mem_Icc]
  simpa only [setOf_exists, setOf_and] using
    MeasurableSet.iUnion (fun j => (measurableSet_le (ha j) hy).inter
      (measurableSet_le hy (hb j)))

/-- Consider a countable source family and a finite target family of closed intervals depending
on an observation. If [the source lower endpoints are measurable](hyp:ha), [the source upper
endpoints are measurable](hyp:hb), [the target lower endpoints are measurable](hyp:hc), [the target
upper endpoints are measurable](hyp:hd), and [every source lower endpoint is at most its upper
endpoint at every observation](hyp:hab), [the observations where the source union is contained in
the target union form a measurable set](goal). -/
lemma measurableSet_finite_interval_union_subset {B J K : Type*}
    [MeasurableSpace B] [Countable J] [Finite K]
    (a b : J → B → ℝ) (c d : K → B → ℝ)
    (ha : ∀ j, Measurable (a j)) (hb : ∀ j, Measurable (b j))
    (hc : ∀ k, Measurable (c k)) (hd : ∀ k, Measurable (d k))
    (hab : ∀ x j, a j x ≤ b j x) :
    MeasurableSet {x | (⋃ j, Icc (a j x) (b j x)) ⊆ ⋃ k, Icc (c k x) (d k x)} := by
  simp_rw [finite_interval_union_subset_iff _ _ _ _ (hab _)]
  apply MeasurableSet.inter
  · change MeasurableSet {x | ∀ j, a j x ∈ ⋃ k, Icc (c k x) (d k x)}
    rw [ofPred_forall]
    exact MeasurableSet.iInter (fun j =>
      measurableSet_mem_finite_interval_union c d (a j) hc hd (ha j))
  · change MeasurableSet {x | ∀ q : ℚ,
      (q : ℝ) ∈ (⋃ j, Icc (a j x) (b j x)) →
        (q : ℝ) ∈ ⋃ k, Icc (c k x) (d k x)}
    rw [ofPred_forall]
    apply MeasurableSet.iInter
    intro q
    have he : {x | (q : ℝ) ∈ (⋃ j, Icc (a j x) (b j x)) →
          (q : ℝ) ∈ ⋃ k, Icc (c k x) (d k x)} =
        {x | (q : ℝ) ∈ ⋃ j, Icc (a j x) (b j x)}ᶜ ∪
          {x | (q : ℝ) ∈ ⋃ k, Icc (c k x) (d k x)} := by
      ext x
      simp only [mem_setOf_eq, mem_union, mem_compl_iff, imp_iff_not_or]
    rw [he]
    exact
      (measurableSet_mem_finite_interval_union a b (fun _ => (q : ℝ))
        ha hb measurable_const).compl.union
      (measurableSet_mem_finite_interval_union c d (fun _ => (q : ℝ))
        hc hd measurable_const)

/-- Consider a finite family of closed intervals and a candidate ordered list of fixed length,
all depending on an observation. If [the original lower endpoints are measurable](hyp:ha),
[the original upper endpoints are measurable](hyp:hb), [the original intervals have ordered
endpoints everywhere](hyp:hab), [the candidate lower endpoints are measurable](hyp:hc),
[the candidate upper endpoints are measurable](hyp:hd), and [the candidate intervals have ordered
endpoints everywhere](hyp:hcd), [the observations where the candidate list represents the original
union with nonempty intervals in the unit interval separated by strict gaps form a measurable
set](goal). -/
lemma measurableSet_rangeData_valid_finite_union {B J : Type*}
    [MeasurableSpace B] [Finite J] (a b : J → B → ℝ)
    (ha : ∀ j, Measurable (a j)) (hb : ∀ j, Measurable (b j))
    (hab : ∀ x j, a j x ≤ b j x) (n : ℕ) (c d : Fin n → B → ℝ)
    (hc : ∀ k, Measurable (c k)) (hd : ∀ k, Measurable (d k))
    (hcd : ∀ x k, c k x ≤ d k x) :
    MeasurableSet {x | RangeData.Valid (⋃ j, Icc (a j x) (b j x))
      ⟨n, (fun k => c k x), (fun k => d k x)⟩} := by
  have hbounds : MeasurableSet {x | ∀ k, 0 ≤ c k x ∧ c k x ≤ d k x ∧ d k x ≤ 1} := by
    rw [ofPred_forall]
    apply MeasurableSet.iInter
    intro k
    rw [ofPred_and, ofPred_and]
    exact (measurableSet_le measurable_const (hc k)).inter
      ((measurableSet_le (hc k) (hd k)).inter (measurableSet_le (hd k) measurable_const))
  have horder : MeasurableSet {x | ∀ k l : Fin n, k < l → d k x < c l x} := by
    rw [ofPred_forall]
    apply MeasurableSet.iInter
    intro k
    rw [ofPred_forall]
    apply MeasurableSet.iInter
    intro l
    by_cases hkl : k < l
    · simpa only [hkl, true_implies] using measurableSet_lt (hd k) (hc l)
    · simp only [hkl, false_implies, ofPred_true]
      exact MeasurableSet.univ
  have hsub := measurableSet_finite_interval_union_subset a b c d ha hb hc hd hab
  have hsup := measurableSet_finite_interval_union_subset c d a b hc hd ha hb hcd
  have heq : MeasurableSet {x | (⋃ j, Icc (a j x) (b j x)) =
      ⋃ k, Icc (c k x) (d k x)} := by
    simp_rw [Set.Subset.antisymm_iff]
    rw [ofPred_and]
    exact hsub.inter hsup
  change MeasurableSet {x | (∀ k, 0 ≤ c k x ∧ c k x ≤ d k x ∧ d k x ≤ 1) ∧
    (∀ k l : Fin n, k < l → d k x < c l x) ∧
      (⋃ j, Icc (a j x) (b j x)) = ⋃ k, Icc (c k x) (d k x)}
  rw [ofPred_and, ofPred_and]
  exact hbounds.inter (horder.inter heq)

/-- For a finite family of closed intervals depending on an observation, assume [the lower
endpoints are measurable](hyp:ha), [the upper endpoints are measurable](hyp:hb), and [each lower
endpoint is at most its upper endpoint everywhere](hyp:hab). If [a given list almost surely
represents their union as ordered nonempty closed intervals in the unit interval separated by
strict gaps](hyp:hE), [there is a list equal to it almost surely under the given measure whose
length and every lower and upper endpoint coordinate are measurable](goal). -/
lemma measurable_ordered_finite_union_version {B J : Type*}
    [MeasurableSpace B] [Fintype J] (mu : Measure B)
    (a b : J → B → ℝ) (ha : ∀ j, Measurable (a j)) (hb : ∀ j, Measurable (b j))
    (hab : ∀ x j, a j x ≤ b j x) (E : B → RangeData)
    (hE : ∀ᵐ x ∂mu, (E x).Valid (⋃ j, Icc (a j x) (b j x))) :
    ∃ D : B → RangeData, Measurable (fun x => (D x).count) ∧
      (∀ k, Measurable (fun x => (D x).low k) ∧ Measurable (fun x => (D x).high k)) ∧
      D =ᵐ[mu] E := by
  classical
  let C := Σ n : ℕ, (Fin n → J) × (Fin n → J)
  letI : Encodable C := Encodable.ofCountable C
  let emptyC : C := ⟨0, Fin.elim0, Fin.elim0⟩
  let idx : ℕ → C := fun n => (Encodable.decode (α := C) n).getD emptyC
  have hidx : Function.Surjective idx := by
    intro c
    exact ⟨Encodable.encode c, by simp [idx]⟩
  let candidate : ℕ → B → RangeData := fun n x =>
    ⟨(idx n).1, (fun k => min (a ((idx n).2.1 k) x) (b ((idx n).2.2 k) x)),
      (fun k => max (a ((idx n).2.1 k) x) (b ((idx n).2.2 k) x))⟩
  let valid : ℕ → B → Prop := fun n x => (candidate n x).Valid (⋃ j, Icc (a j x) (b j x))
  have hm (n : ℕ) : MeasurableSet {x | valid n x} :=
    measurableSet_rangeData_valid_finite_union a b ha hb hab (idx n).1 _ _
      (fun k => (ha _).min (hb _)) (fun k => (ha _).max (hb _))
      (fun x k => min_le_max)
  let p : ℕ → B → Prop := fun n x => valid n x ∨ (n = 0 ∧ ¬ ∃ m, valid m x)
  have hp (n : ℕ) : MeasurableSet {x | p n x} := by
    have hex : MeasurableSet {x | ∃ m, valid m x} := by
      rw [ofPred_exists]
      exact MeasurableSet.iUnion hm
    change MeasurableSet {x | valid n x ∨ (n = 0 ∧ ¬ ∃ m, valid m x)}
    rw [ofPred_or, ofPred_and]
    apply (hm n).union
    apply MeasurableSet.inter _ hex.compl
    by_cases hn : n = 0 <;> simp [hn]
  have hpExists (x : B) : ∃ n, p n x := by
    by_cases hv : ∃ n, valid n x
    · obtain ⟨n, hn⟩ := hv
      exact ⟨n, Or.inl hn⟩
    · exact ⟨0, Or.inr ⟨rfl, hv⟩⟩
  let D : B → RangeData := fun x => candidate (Nat.find (hpExists x)) x
  refine ⟨D, ?_, ?_, ?_⟩
  · exact Measurable.find (f := fun n (_ : B) => (idx n).1)
      (fun n => measurable_const) hp hpExists
  · intro k
    have hlo (n : ℕ) : Measurable (fun x => (candidate n x).low k) := by
      by_cases hk : k < (idx n).1
      · simpa only [candidate, RangeData.low, dif_pos hk] using
          (ha ((idx n).2.1 ⟨k, hk⟩)).min (hb ((idx n).2.2 ⟨k, hk⟩))
      · simpa only [candidate, RangeData.low, dif_neg hk] using
          (measurable_const : Measurable (fun _ : B => (1 : ℝ)))
    have hhi (n : ℕ) : Measurable (fun x => (candidate n x).high k) := by
      by_cases hk : k < (idx n).1
      · simpa only [candidate, RangeData.high, dif_pos hk] using
          (ha ((idx n).2.1 ⟨k, hk⟩)).max (hb ((idx n).2.2 ⟨k, hk⟩))
      · simpa only [candidate, RangeData.high, dif_neg hk] using
          (measurable_const : Measurable (fun _ : B => (0 : ℝ)))
    exact ⟨Measurable.find (f := fun n x => (candidate n x).low k) hlo hp hpExists,
      Measurable.find (f := fun n x => (candidate n x).high k) hhi hp hpExists⟩
  · filter_upwards [hE] with x hx
    obtain ⟨l, r, hl, hends, hcount⟩ := rangeData_endpoints_from_finite_union
      (fun j => a j x) (fun j => b j x) (hab x) (E x) hx
    dsimp only [RangeData.count] at l r hcount
    obtain ⟨n, hn⟩ := hidx ⟨(E x).1, l, r⟩
    have hcand : candidate n x = E x := by
      dsimp only [candidate]
      rw [hn]
      have hlo : (fun k => min (a (l k) x) (b (r k) x)) = (E x).2.1 := by
        funext k
        rw [← (hends k).1, ← (hends k).2]
        exact min_eq_left (hx.1 k).2.1
      have hhi : (fun k => max (a (l k) x) (b (r k) x)) = (E x).2.2 := by
        funext k
        rw [← (hends k).1, ← (hends k).2]
        exact max_eq_right (hx.1 k).2.1
      change ⟨(E x).1, (fun k => min (a (l k) x) (b (r k) x)),
        (fun k => max (a (l k) x) (b (r k) x))⟩ = E x
      rw [hlo, hhi]
    have hv : ∃ m, valid m x := ⟨n, by change (candidate n x).Valid _; rwa [hcand]⟩
    have hchosen : valid (Nat.find (hpExists x)) x := by
      rcases Nat.find_spec (hpExists x) with hv' | hv'
      · exact hv'
      · exact False.elim (hv'.2 hv)
    exact rangeData_valid_unique (D x) (E x) hchosen hx

/-- Under [the model's structural assumptions](hyp:h), if [the propensity is continuous on each
instrument component for almost every covariate value](hyp:hc) and [the instrument space has
finitely many connected components](hyp:hfin), [the canonical ordered decomposition of the
conditional propensity range has an almost surely equal version under the covariate law with
measurable interval count and measurable lower and upper gap endpoints at every index](goal). -/
lemma measurable_ordered_gap_law_version
    (h : StructuralAssumptions M) (hc : PropensityContinuousOnComponents M)
    (hfin : FiniteInstrumentComponents Z) :
    ∃ D : X → RangeData, Measurable (fun x => (D x).count) ∧
      (∀ k, Measurable (fun x => (D x).gapLo k) ∧
        Measurable (fun x => (D x).gapHi k)) ∧
      D =ᵐ[xLaw M] CondRangeDecomposition M := by
  classical
  letI : Finite (ConnectedComponents Z) := hfin
  letI : Fintype (ConnectedComponents Z) := Fintype.ofFinite _
  obtain ⟨a, b, hm, hr⟩ := measurable_finite_component_range_versions M h hc hfin
  let lo : ConnectedComponents Z → X → ℝ := fun j x => min (a j x) (b j x)
  let hi : ConnectedComponents Z → X → ℝ := fun j x => max (a j x) (b j x)
  have hlo (j) : Measurable (lo j) := (hm j).1.min (hm j).2
  have hhi (j) : Measurable (hi j) := (hm j).1.max (hm j).2
  have hvalid : ∀ᵐ x ∂xLaw M,
      (CondRangeDecomposition M x).Valid (⋃ j, Icc (lo j x) (hi j x)) := by
    filter_upwards [hr, range_decomposition_valid M h hfin hc] with x hx hv
    have heq : (⋃ j, Icc (lo j x) (hi j x)) = range (fun z => M.prop z x) := by
      rw [hx.1]
      congr 1
      funext j
      dsimp only [lo, hi]
      rw [min_eq_left (hx.2 j).2.1, max_eq_right (hx.2 j).2.1]
    rwa [heq]
  obtain ⟨D, hcount, hend, heq⟩ := measurable_ordered_finite_union_version
    (xLaw M) lo hi hlo hhi (fun _ _ => min_le_max) (CondRangeDecomposition M) hvalid
  refine ⟨D, hcount, ?_, heq⟩
  intro k
  constructor
  · by_cases hk : k = 0
    · simpa only [RangeData.gapLo, hk, if_true] using
        (measurable_const : Measurable (fun _ : X => (0 : ℝ)))
    · simpa only [RangeData.gapLo, if_neg hk] using (hend (k - 1)).2
  · exact (hend k).1

end Papers.TbsPrteOptimalTransport
