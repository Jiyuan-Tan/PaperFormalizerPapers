module

public import Papers.OaiPairedStatesHamiltonian.Helpers.CancelDelta
public import Papers.OaiPairedStatesHamiltonian.Helpers.CancelCycleLift

/-! Cancellation for a fixed state with a cyclic opposite-edge graph. -/

public section

namespace OaiPairedStatesHamiltonian

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
open Classical
attribute [local instance] propDecidable



-- @node: exists_cancellation_partner
/-- If [the map is a sphere triangulation](hyp:hT), [the face coloring gives opposite colors across every edge](hyp:hcol), [the opposite-edge graph of the fixed state contains a cycle](hyp:hcyclic), and [it has a simple cycle](hyp:hpin), then [one can choose a simple cycle independently of the partner state so that every partner has another partner obtained by swapping its chosen vertex with the third vertex exactly on that cycle, with phase index changing by two modulo four](goal). -/
lemma exists_cancellation_partner (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (t0 : T.Face)
    (s : State T col t0) (hcyclic : QsCyclic T col t0 s)
    (hpin : QsHasSimpleCycle T col t0 s) :
    ∃ v, ∃ C : (Qs T col t0 s).Walk v v, C.IsCycle ∧
      ∀ (r : State T col t0) (hpair : IsPair T col t0 r s),
        ∃ tildeR : State T col t0, ∃ hnew : IsPair T col t0 tildeR s,
          -- @realizes \widetilde r(partner obtained by swapping the other two vertices on the fixed cycle)
          (∀ t : blackNonOuter T col t0,
            let u := thirdVertex T hT t.val (r.val t).val (s.val t).val
              (r.property.incident t) (s.property.incident t) (pair_vertex_ne T col t0 r s hpair t)
            (tildeR.val t).val = if s((r.val t).val, u.val) ∈ C.edges then u.val else (r.val t).val) ∧
          (J T col t0 hT tildeR s hnew - J T col t0 hT r s hpair) % 4 = 2 := by
  obtain ⟨v, C, hC⟩ := hpin
  refine ⟨v, C, hC, ?_⟩
  intro r hpair
  obtain ⟨D, hD, hedges⟩ :=
    exists_directed_opposite_cycle_lift T col t0 hT hcol r s hpair v C hC
  obtain ⟨q, hq, hswitch⟩ := exists_opposite_cycle_switch T col t0 hT r s hpair D hD
  refine ⟨q, hq, ?_, opposite_cycle_switch_phase T col t0 hT hcol r s q hpair hq D hD hswitch⟩
  intro t
  simpa only [← hedges t, oppositeEdge, oppositeVertex, oppositeThirdVertex] using hswitch t


-- @node: triangle_remaining_vertex_unique
/-- In [a sphere triangulation](hyp:hT), suppose [v belongs to face f](hyp:hv), [w belongs to f](hyp:hw), [u belongs to f](hyp:hu), and [x belongs to f](hyp:hx), with [v and w distinct](hyp:hvw), [u different from v](hyp:huv) and [u different from w](hyp:huw), and [x different from v](hyp:hxv) and [x different from w](hyp:hxw). Then [x equals u](goal). -/
lemma triangle_remaining_vertex_unique (T : SphereMap) (hT : IsSphereTriangulation T)
    (f : T.Face) (v w u x : T.Vertex)
    (hv : v ∈ T.faceVertices f) (hw : w ∈ T.faceVertices f)
    (hu : u ∈ T.faceVertices f) (hx : x ∈ T.faceVertices f)
    (hvw : v ≠ w) (huv : u ≠ v) (huw : u ≠ w)
    (hxv : x ≠ v) (hxw : x ≠ w) : x = u := by
  have hsub : ({v, w, u} : Finset T.Vertex) ⊆ T.faceVertices f := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hv, hw, hu⟩
  have heq : ({v, w, u} : Finset T.Vertex) = T.faceVertices f :=
    Finset.eq_of_subset_of_card_le hsub (by
      rw [(hT.props.2.2.2 f).2]
      simp [hvw, Ne.symm huv, Ne.symm huw])
  rw [← heq] at hx
  simpa [hxv, hxw] using hx

-- @node: I_zpow_neg_of_sub_mod_four
/-- If [the difference of two integer exponents is two modulo four](hyp:h), then [the corresponding powers of the imaginary unit are negatives of one another](goal). -/
lemma I_zpow_neg_of_sub_mod_four (m n : ℤ) (h : (m - n) % 4 = 2) :
    Complex.I ^ m = -(Complex.I ^ n) := by
  have hd : Complex.I ^ (m - n) = -1 := by
    rw [Complex.I_zpow_eq_zpow_mod, h]
    norm_num
  calc
    Complex.I ^ m = Complex.I ^ (m - n) * Complex.I ^ n := by
      rw [← zpow_add₀ Complex.I_ne_zero, sub_add_cancel]
    _ = -(Complex.I ^ n) := by rw [hd, neg_one_mul]

-- @node: lem:cancel
/-- For [a sphere triangulation](hyp:hT) with [oppositely colored faces across every edge](hyp:hcol), suppose [the fixed state's opposite-edge graph contains a cycle](hyp:hcyclic) and [has a simple cycle](hyp:hpin). Then [the sum over all partner states of the imaginary unit raised to the pair's phase index, multiplied by the exponential of x times the fixed state's weighted energy, is zero](goal). -/
lemma sum_Z_terms_eq_zero_of_cyclic (T : SphereMap) (hT : IsSphereTriangulation T)
    (col : T.Face → Bool) (hcol : PartitionColoring T col) (t0 : T.Face)
    (s : State T col t0) (hcyclic : QsCyclic T col t0 s)
    (hpin : QsHasSimpleCycle T col t0 s) (a : IncidenceWeights T col t0) (x : ℝ) :
    (∑ r : {r : State T col t0 // IsPair T col t0 r s},
      Complex.I ^ J T col t0 hT r.val s r.property *
        Complex.exp ((x * omega T col t0 a s : ℝ) : ℂ)) = 0 := by
  obtain ⟨v, C, hcycle, hswitch⟩ :=
    exists_cancellation_partner T hT col hcol t0 s hcyclic hpin
  let P := {r : State T col t0 // IsPair T col t0 r s}
  have hex (r : P) : ∃ q : P,
      (∀ t : blackNonOuter T col t0,
        let u := thirdVertex T hT t.val (r.val.val t).val (s.val t).val
          (r.val.property.incident t) (s.property.incident t)
          (pair_vertex_ne T col t0 r.val s r.property t)
        (q.val.val t).val = if s((r.val.val t).val, u.val) ∈ C.edges then u.val
          else (r.val.val t).val) ∧
      (J T col t0 hT q.val s q.property - J T col t0 hT r.val s r.property) % 4 = 2 := by
    obtain ⟨q, hq, hs, hj⟩ := hswitch r.val r.property
    exact ⟨⟨q, hq⟩, hs, hj⟩
  let g : P → P := fun r => Classical.choose (hex r)
  have hg (r : P) := Classical.choose_spec (hex r)
  have hinv (r : P) : g (g r) = r := by
    apply Subtype.ext
    apply Subtype.ext
    funext t
    apply Subtype.ext
    let u := thirdVertex T hT t.val (r.val.val t).val (s.val t).val
      (r.val.property.incident t) (s.property.incident t)
      (pair_vertex_ne T col t0 r.val s r.property t)
    let u' := thirdVertex T hT t.val ((g r).val.val t).val (s.val t).val
      ((g r).val.property.incident t) (s.property.incident t)
      (pair_vertex_ne T col t0 (g r).val s (g r).property t)
    have hr := (hg r).1 t
    have hgr := (hg (g r)).1 t
    change ((g r).val.val t).val =
      if s((r.val.val t).val, u.val) ∈ C.edges then u.val else (r.val.val t).val at hr
    change ((g (g r)).val.val t).val =
      if s(((g r).val.val t).val, u'.val) ∈ C.edges then u'.val
        else ((g r).val.val t).val at hgr
    by_cases he : s((r.val.val t).val, u.val) ∈ C.edges
    · have hru : ((g r).val.val t).val = u.val := by simpa [he] using hr
      have hu' : u'.val = (r.val.val t).val := by
        apply triangle_remaining_vertex_unique T hT t.val u.val (s.val t).val
          (r.val.val t).val u'.val u.property.1 (s.property.incident t)
          (r.val.property.incident t) u'.property.1 u.property.2.2
          (Ne.symm u.property.2.1) (pair_vertex_ne T col t0 r.val s r.property t)
        · simpa [hru] using u'.property.2.1
        · exact u'.property.2.2
      have he' : s(((g r).val.val t).val, u'.val) ∈ C.edges := by
        simpa only [hru, hu', Sym2.eq_swap] using he
      rw [if_pos he'] at hgr
      exact hgr.trans hu'
    · have hrr : ((g r).val.val t).val = (r.val.val t).val := by simpa [he] using hr
      have hu' : u'.val = u.val := by
        apply triangle_remaining_vertex_unique T hT t.val (r.val.val t).val (s.val t).val
          u.val u'.val (r.val.property.incident t) (s.property.incident t)
          u.property.1 u'.property.1 (pair_vertex_ne T col t0 r.val s r.property t)
          u.property.2.1 u.property.2.2
        · simpa [hrr] using u'.property.2.1
        · exact u'.property.2.2
      have he' : s(((g r).val.val t).val, u'.val) ∉ C.edges := by
        simpa only [hrr, hu'] using he
      rw [if_neg he'] at hgr
      exact hgr.trans hrr
  apply Finset.sum_involution (fun r _ => g r)
  · intro r hr
    have hphase := I_zpow_neg_of_sub_mod_four _ _ (hg r).2
    change Complex.I ^ J T col t0 hT r.val s r.property * _ +
      Complex.I ^ J T col t0 hT (g r).val s (g r).property * _ = 0
    rw [hphase, neg_mul, add_neg_cancel]
  · intro r hr hn heq
    have hj := (hg r).2
    change (J T col t0 hT (g r).val s (g r).property -
      J T col t0 hT r.val s r.property) % 4 = 2 at hj
    rw [heq] at hj
    norm_num at hj
  · intro r hr
    exact Finset.mem_univ _
  · intro r hr
    exact hinv r


end OaiPairedStatesHamiltonian
