module
public import Papers.OaiGeometricErdosSimilarity.Helpers.TreeRouting
public import Papers.OaiGeometricErdosSimilarity.Helpers.BoundaryDensity

/-! # Stability of centers and grid keys -/

public section

namespace Papers.OaiGeometricErdosSimilarity

open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {M d : ℕ} (q : ℝ) (g r0 : ℕ) {n0 : ℕ}

-- @node: isStableCenter_iff_avoids_boundary_intervals
/-- If [the base length is positive](hyp:hr) and [the starting index is at
least one](hyp:hn0), then [x is a stable center exactly when, for every edge
and its immediate predecessor, x avoids every interval extending left from
a predecessor grid boundary by twice q to the current window's starting
index, including the left endpoint and excluding the boundary itself](goal). -/
lemma isStableCenter_iff_avoids_boundary_intervals
    (hr : BaseLengthDomain r0) (hn0 : 1 ≤ n0) (x : ℝ) :
    IsStableCenter q M d g r0 n0 x ↔
      ∀ e f : TreeEdge M d, IsPredecessor f e → ∀ k : ℤ,
        x ∉ Set.Ico ((k : ℝ) / gridResolution q (windowEnd q M d g r0 n0 f) -
          2 * q ^ windowStart q M d g r0 n0 e)
          ((k : ℝ) / gridResolution q (windowEnd q M d g r0 n0 f)) := by
  constructor
  · intro hx e f hef k hk
    have hempty := hx.stable.2.2 e f hef
    have hmem : (k : ℝ) / gridResolution q (windowEnd q M d g r0 n0 f) ∈
        Set.Ioc x (x + 2 * q ^ windowStart q M d g r0 n0 e) ∩
          gridLattice q (windowEnd q M d g r0 n0 f) := by
      exact ⟨⟨hk.2, by linarith [hk.1]⟩, ⟨k, rfl⟩⟩
    rw [hempty] at hmem
    exact hmem
  · intro hx
    refine ⟨hr, hn0, ?_⟩
    intro e f hef
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    obtain ⟨k, rfl⟩ := hy.2
    exact hx e f hef k ⟨by linarith [hy.1.2], hy.1.1⟩

-- @node: stableSet_measurable
/-- If [the base length is positive](hyp:hr) and [the starting index is at
least one](hyp:hn0), then [the set of stable centers is measurable](goal). -/
lemma stableSet_measurable (hr : BaseLengthDomain r0) (hn0 : 1 ≤ n0) :
    MeasurableSet (stableSet q M d g r0 n0) := by
  first | fun_prop | skip
  have hset : stableSet q M d g r0 n0 =
      ⋂ e : TreeEdge M d, ⋂ f : TreeEdge M d, ⋂ (_ : IsPredecessor f e), ⋂ k : ℤ,
        (Set.Ico ((k : ℝ) / gridResolution q (windowEnd q M d g r0 n0 f) -
          2 * q ^ windowStart q M d g r0 n0 e)
          ((k : ℝ) / gridResolution q (windowEnd q M d g r0 n0 f)))ᶜ := by
    ext x
    simp only [stableSet, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_compl_iff]
    exact isStableCenter_iff_avoids_boundary_intervals q g r0 hr hn0 x
  rw [hset]
  exact MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => measurableSet_Ico.compl

-- @node: stableSet_onePeriodic
/-- If [the base length is positive](hyp:hr) and [the starting index is at
least one](hyp:hn0), then [a real number is a stable center exactly when that
number plus one is a stable center](goal). -/
lemma stableSet_onePeriodic (hr : BaseLengthDomain r0) (hn0 : 1 ≤ n0) :
    IsOnePeriodic (stableSet q M d g r0 n0) := by
  have hshift (x : ℝ) (z : ℤ) (hx : IsStableCenter q M d g r0 n0 x) :
      IsStableCenter q M d g r0 n0 (x + (z : ℝ)) := by
    apply (isStableCenter_iff_avoids_boundary_intervals q g r0 hr hn0 _).mpr
    intro e f hef k hk
    let N := gridResolution q (windowEnd q M d g r0 n0 f)
    have hN : (N : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (gridResolution_pos q _))
    have hboundary : (((k - z * (N : ℤ) : ℤ) : ℝ) / N) = (k : ℝ) / N - z := by
      push_cast
      field_simp
    have hxk := (isStableCenter_iff_avoids_boundary_intervals q g r0 hr hn0 x).mp hx
      e f hef (k - z * (N : ℤ))
    change x ∉ Set.Ico ((((k - z * (N : ℤ) : ℤ) : ℝ) / N) -
      2 * q ^ windowStart q M d g r0 n0 e) _ at hxk
    rw [hboundary] at hxk
    exact hxk ⟨by linarith [hk.1], by linarith [hk.2]⟩
  intro x
  change IsStableCenter q M d g r0 n0 x ↔ IsStableCenter q M d g r0 n0 (x + 1)
  constructor
  · intro hx
    simpa only [Int.cast_one] using hshift x 1 hx
  · intro hx
    have hback := hshift (x + 1) (-1) hx
    simpa using hback

-- @node: gridKey_eq_of_no_boundary
/-- If [x is at most y](hyp:hxy) and [there is no grid boundary at resolution
index b strictly above x and at or below y](hyp:havoid), then [y and x have
the same grid key at index b](goal). -/
lemma gridKey_eq_of_no_boundary (b : ℕ) {x y : ℝ} (hxy : x ≤ y)
    (havoid : Set.Ioc x y ∩ gridLattice q b = ∅) : gridKey q b y = gridKey q b x := by
  let N := gridResolution q b
  have hN : (0 : ℝ) < N := by exact_mod_cast gridResolution_pos q b
  have hupper : (N : ℝ) * y < (⌊(N : ℝ) * x⌋ : ℤ) + 1 := by
    by_contra h
    have hmem : (((⌊(N : ℝ) * x⌋ + 1 : ℤ) : ℝ) / N) ∈
        Set.Ioc x y ∩ gridLattice q b := by
      refine ⟨⟨?_, ?_⟩, ⟨⌊(N : ℝ) * x⌋ + 1, rfl⟩⟩
      · apply (lt_div_iff₀ hN).mpr
        push_cast
        simpa [mul_comm] using Int.lt_floor_add_one ((N : ℝ) * x)
      · apply (div_le_iff₀ hN).mpr
        push_cast
        linarith
    rw [havoid] at hmem
    exact hmem
  have hscaled : ⌊(N : ℝ) * y⌋ = ⌊(N : ℝ) * x⌋ := by
    apply Int.floor_eq_iff.mpr
    exact ⟨(Int.floor_le _).trans (mul_le_mul_of_nonneg_left hxy hN.le), hupper⟩
  have hbase : ⌊y⌋ = ⌊x⌋ := by
    have hdiv := congrArg (fun k : ℤ => k / (N : ℤ)) hscaled
    simpa only [← Int.floor_div_natCast, mul_div_cancel_left₀ _ hN.ne'] using hdiv
  have hnorm : ⌊(N : ℝ) * Int.fract y⌋ = ⌊(N : ℝ) * Int.fract x⌋ := by
    simp only [Int.fract, mul_sub]
    have hcast (z : ℝ) : (N : ℝ) * (⌊z⌋ : ℤ) = ((N : ℤ) * ⌊z⌋ : ℤ) := by
      push_cast
      rfl
    rw [hcast, hcast, Int.floor_sub_intCast, Int.floor_sub_intCast, hscaled, hbase]
  simpa only [Int.floor_toNat, gridKey] using congrArg Int.toNat hnorm

-- @node: exists_predecessor_of_preorderLt
/-- If [edge f occurs before edge e in the tree's preorder](hyp:hfe), then
[e has an immediate predecessor that either equals f or occurs after f in
that preorder](goal). -/
lemma exists_predecessor_of_preorderLt (f e : TreeEdge M d) (hfe : preorderLt f e) :
    ∃ p : TreeEdge M d, IsPredecessor p e ∧ (preorderLt f p ∨ f = p) := by
  let S := Finset.univ.filter (fun a : TreeEdge M d => preorderLt a e)
  have hfS : f ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfe⟩
  obtain ⟨p, hp, hmax⟩ := S.exists_max_image (fun a => vertexPath a.val) ⟨f, hfS⟩
  refine ⟨p, ⟨(Finset.mem_filter.mp hp).2, ?_⟩, ?_⟩
  · rintro ⟨a, hpa, hae⟩
    have haS : a ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hae⟩
    exact not_lt_of_ge (hmax a haS) hpa
  · rcases lt_or_eq_of_le (hmax f hfS) with h | h
    · exact Or.inl h
    · exact Or.inr (Subtype.ext (vertexPath_injective h))

-- @node: stableCenter_preceding_keys
/-- Suppose [q lies strictly between zero and one](hyp:hq), [the base length
is positive](hyp:hr), [the starting index is at least one](hyp:hn0), and
[x is a stable center](hyp:hx). If [n belongs to edge e's window](hyp:hn),
[t lies between one and two, inclusive](hyp:ht), and [edge f precedes e in
the tree's preorder](hyp:hfe), then [moving from x to x plus t times q to
the power n leaves the grid key at f's window endpoint unchanged](goal). -/
lemma stableCenter_preceding_keys (hq : QDomain q) (hr : BaseLengthDomain r0)
    (hn0 : 1 ≤ n0) (x : ℝ) (hx : IsStableCenter q M d g r0 n0 x)
    (e : TreeEdge M d) (n : ℕ) (hn : n ∈ windowSet q M d g r0 n0 e)
    (t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) 2) (f : TreeEdge M d)
    (hfe : preorderLt f e) :
    gridKey q (windowEnd q M d g r0 n0 f) (x + t * q ^ n) =
      gridKey q (windowEnd q M d g r0 n0 f) x := by
  obtain ⟨p, hpe, hfp⟩ := exists_predecessor_of_preorderLt f e hfe
  have hnpow : q ^ n ≤ q ^ windowStart q M d g r0 n0 e :=
    pow_le_pow_of_le_one hq.1.le hq.2.le (Finset.mem_Icc.mp hn).1
  have hstep : 0 ≤ t * q ^ n := mul_nonneg (by linarith [ht.1]) (pow_pos hq.1 n).le
  have hstepupper : t * q ^ n ≤ 2 * q ^ windowStart q M d g r0 n0 e := by
    calc
      t * q ^ n ≤ 2 * q ^ n := mul_le_mul_of_nonneg_right ht.2 (pow_pos hq.1 n).le
      _ ≤ 2 * q ^ windowStart q M d g r0 n0 e := by linarith
  have havoid : Set.Ioc x (x + t * q ^ n) ∩
      gridLattice q (windowEnd q M d g r0 n0 p) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hz' : z ∈ Set.Ioc x (x + 2 * q ^ windowStart q M d g r0 n0 e) ∩
        gridLattice q (windowEnd q M d g r0 n0 p) :=
      ⟨⟨hz.1.1, by linarith [hz.1.2]⟩, hz.2⟩
    rw [hx.stable.2.2 e p hpe] at hz'
    exact hz'
  have hkey := gridKey_eq_of_no_boundary q (windowEnd q M d g r0 n0 p)
    (by linarith : x ≤ x + t * q ^ n) havoid
  have hbp : windowEnd q M d g r0 n0 f ≤ windowEnd q M d g r0 n0 p := by
    rcases hfp with hfp | rfl
    · exact windowEnd_le_of_preorderLt hr f p hfp
    · rfl
  have hnest := ((gridNesting_of_qDomain q hq).2.2
    (windowEnd q M d g r0 n0 f) (windowEnd q M d g r0 n0 p)
    (windowEnd_positive q g r0 hr hn0 f) hbp).2
  rw [hnest (x + t * q ^ n), hnest x, hkey]

-- @node: predecessor_unique
/-- If [f is an immediate predecessor of e](hyp:hf) and [p is also an
immediate predecessor of e](hyp:hp), then [f and p are the same edge](goal). -/
lemma predecessor_unique {f p e : TreeEdge M d}
    (hf : IsPredecessor f e) (hp : IsPredecessor p e) : f = p := by
  rcases lt_trichotomy (vertexPath f.val) (vertexPath p.val) with h | h | h
  · exact False.elim (hf.2 ⟨p, h, hp.1⟩)
  · exact Subtype.ext (vertexPath_injective h)
  · exact False.elim (hp.2 ⟨f, h, hf.1⟩)

-- @node: windowStart_eq_predecessor_end
/-- If [the base length is positive](hyp:hr) and [f is the immediate
predecessor of e](hyp:hfe), then [e's window starts at f's window endpoint
plus g plus one, leaving exactly g unused indices between the windows](goal). -/
lemma windowStart_eq_predecessor_end (hr : BaseLengthDomain r0)
    {f e : TreeEdge M d} (hfe : IsPredecessor f e) :
    windowStart q M d g r0 n0 e = windowEnd q M d g r0 n0 f + g + 1 := by
  let A := Finset.univ.filter (fun a : TreeEdge M d => preorderLt a f)
  have hfA : f ∉ A := by
    intro hf
    exact (lt_irrefl (vertexPath f.val)) (Finset.mem_filter.mp hf).2
  have hfilter : Finset.univ.filter (fun a : TreeEdge M d => preorderLt a e) =
      insert f A := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hae
      rcases lt_trichotomy (vertexPath a.val) (vertexPath f.val) with h | h | h
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      · exact Or.inl (Subtype.ext (vertexPath_injective h))
      · exact False.elim (hfe.2 ⟨a, h, hae⟩)
    · rintro (rfl | ha)
      · exact hfe.1
      · exact List.lex_trans (fun hab hbc => lt_trans hab hbc)
          (Finset.mem_filter.mp ha).2 hfe.1
  have hlen := windowLength_pos M g r0 (sourceHeight f) hr
  unfold windowStart windowEnd
  rw [hfilter, Finset.sum_insert hfA]
  change n0 + (windowLength M g r0 (sourceHeight f) + g +
      ∑ a ∈ A, (windowLength M g r0 (sourceHeight a) + g)) =
    n0 + ∑ a ∈ A, (windowLength M g r0 (sourceHeight a) + g) +
      windowLength M g r0 (sourceHeight f) - 1 + g + 1
  omega

-- @node: predecessor_boundary_density_le
/-- If [q lies strictly between zero and one](hyp:hq), [the base length is
positive](hyp:hr), and [f is the immediate predecessor of e](hyp:hfe), then
[the periodic density of the union of intervals extending left from every
grid boundary at f's window endpoint by twice q to e's window starting
index, including the left endpoint and excluding the boundary, is at most
four times the grid constant times q to the power (g plus one)](goal). -/
lemma predecessor_boundary_density_le (hq : QDomain q) (hr : BaseLengthDomain r0)
    {f e : TreeEdge M d} (hfe : IsPredecessor f e) :
    periodicDensity {x : ℝ | ∃ k : ℤ,
      x ∈ Set.Ico ((k : ℝ) / gridResolution q (windowEnd q M d g r0 n0 f) -
        2 * q ^ windowStart q M d g r0 n0 e)
        ((k : ℝ) / gridResolution q (windowEnd q M d g r0 n0 f))} ≤
      4 * gridConst q * q ^ (g + 1) := by
  have hq0 : 0 < q := hq.1
  have hbound := boundary_intervals_density_le
    (gridResolution q (windowEnd q M d g r0 n0 f)) (gridResolution_pos q _)
    (2 * q ^ windowStart q M d g r0 n0 e) (by positivity)
  apply hbound.trans
  have hsize := (gridSizeComparison_of_qDomain q hq (windowEnd q M d g r0 n0 f)).2.le
  have hmul := mul_le_mul_of_nonneg_right hsize
    (show 0 ≤ 2 * q ^ windowStart q M d g r0 n0 e by positivity)
  rw [windowStart_eq_predecessor_end q g r0 hr hfe,
    show windowEnd q M d g r0 n0 f + g + 1 =
      windowEnd q M d g r0 n0 f + (g + 1) by omega,
    pow_add, zpow_neg, zpow_natCast] at hmul
  have hp : q ^ windowEnd q M d g r0 n0 f ≠ 0 := (pow_pos hq.1 _).ne'
  rw [windowStart_eq_predecessor_end q g r0 hr hfe,
    show windowEnd q M d g r0 n0 f + g + 1 =
      windowEnd q M d g r0 n0 f + (g + 1) by omega, pow_add]
  convert hmul using 1 <;> field_simp <;> ring

-- @node: stableSet_compl_density_le
/-- If [q lies strictly between zero and one](hyp:hq), [the base length is
positive](hyp:hr), and [the starting index is at least one](hyp:hn0), then
[the periodic density of centers that are not stable is at most four times
the number of tree edges times the grid constant times q to the power
(g plus one)](goal). -/
lemma stableSet_compl_density_le (hq : QDomain q) (hr : BaseLengthDomain r0)
    (hn0 : 1 ≤ n0) :
    periodicDensity (stableSet q M d g r0 n0)ᶜ ≤
      4 * edgeCount M d * gridConst q * q ^ (g + 1) := by
  classical
  let A : TreeEdge M d → Set ℝ := fun e => {x | ∃ f : TreeEdge M d,
    IsPredecessor f e ∧ ∃ k : ℤ,
      x ∈ Set.Ico ((k : ℝ) / gridResolution q (windowEnd q M d g r0 n0 f) -
        2 * q ^ windowStart q M d g r0 n0 e)
        ((k : ℝ) / gridResolution q (windowEnd q M d g r0 n0 f))}
  have hcover : (stableSet q M d g r0 n0)ᶜ ⊆ ⋃ e, A e := by
    intro x hx
    have hx' : ¬ IsStableCenter q M d g r0 n0 x := hx
    rw [isStableCenter_iff_avoids_boundary_intervals q g r0 hr hn0 x] at hx'
    push Not at hx'
    obtain ⟨e, f, hfe, k, hk⟩ := hx'
    exact Set.mem_iUnion.mpr ⟨e, f, hfe, k, hk⟩
  have hA (e : TreeEdge M d) : periodicDensity (A e) ≤
      4 * gridConst q * q ^ (g + 1) := by
    by_cases hex : ∃ f : TreeEdge M d, IsPredecessor f e
    · obtain ⟨f, hf⟩ := hex
      have hsub : A e ⊆ {x : ℝ | ∃ k : ℤ,
          x ∈ Set.Ico ((k : ℝ) / gridResolution q (windowEnd q M d g r0 n0 f) -
            2 * q ^ windowStart q M d g r0 n0 e)
            ((k : ℝ) / gridResolution q (windowEnd q M d g r0 n0 f))} := by
        rintro x ⟨p, hp, hk⟩
        have hpf := predecessor_unique hp hf
        subst p
        exact hk
      exact (periodicDensity_mono hsub).trans (predecessor_boundary_density_le q g r0 hq hr hf)
    · have hzero : A e = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro x ⟨f, hf, hk⟩
        exact hex ⟨f, hf⟩
      rw [hzero]
      simp only [periodicDensity, Set.empty_inter, measure_empty, ENNReal.toReal_zero]
      have hc : 0 ≤ gridConst q := by
        exact div_nonneg (by norm_num) (by linarith [hq.2])
      have hq0 : 0 < q := hq.1
      positivity
  calc
    periodicDensity (stableSet q M d g r0 n0)ᶜ ≤ periodicDensity (⋃ e, A e) :=
      periodicDensity_mono hcover
    _ ≤ ∑ e, periodicDensity (A e) := periodicDensity_iUnion_le A
    _ ≤ ∑ _e : TreeEdge M d, 4 * gridConst q * q ^ (g + 1) :=
      Finset.sum_le_sum fun e _ => hA e
    _ = 4 * edgeCount M d * gridConst q * q ^ (g + 1) := by
      simp [edgeCount]
      <;> ring

-- @node: lem:stability
/-- Assume [q lies strictly between zero and one](hyp:hq), [M is at least
two](hyp:hM), [the depth is positive](hyp:hd), [the gap is positive](hyp:hg),
[the base length is positive](hyp:hr), and [the starting index is at least
one](hyp:hn0). Then [the stable centers form a measurable set invariant
under translation by one, their complement has periodic density at most
four times the number of tree edges times the grid constant times q to the
power (g plus one), and for every stable center x, index n in an edge's window,
and scale t between one and two, the point x plus t times q to the power n
has the same grid key as x at every earlier edge's window endpoint](goal). -/
lemma stableSet_measurable_density_and_keys (hq : QDomain q) (hM : BranchingDomain M)
    (hd : DepthDomain d) (hg : GapDomain g) (hr : BaseLengthDomain r0)
    (hn0 : 1 ≤ n0) :
    MeasurableSet (stableSet q M d g r0 n0) ∧ IsOnePeriodic (stableSet q M d g r0 n0) ∧
    periodicDensity (stableSet q M d g r0 n0)ᶜ ≤ 4 * edgeCount M d * gridConst q * q ^ (g + 1) ∧
    ∀ x, IsStableCenter q M d g r0 n0 x → ∀ (e : TreeEdge M d) (n : ℕ),
      n ∈ windowSet q M d g r0 n0 e → ∀ t ∈ Set.Icc (1 : ℝ) 2, ∀ f : TreeEdge M d,
      preorderLt f e → gridKey q (windowEnd q M d g r0 n0 f) (x + t * q ^ n) =
        gridKey q (windowEnd q M d g r0 n0 f) x := by
  refine ⟨stableSet_measurable q g r0 hr hn0, stableSet_onePeriodic q g r0 hr hn0, ?_⟩
  refine ⟨?_, ?_⟩
  · exact stableSet_compl_density_le q g r0 hq hr hn0
  · intro x hx e n hn t ht f hfe
    exact stableCenter_preceding_keys q g r0 hq hr hn0 x hx e n hn t ht f hfe

end Papers.OaiGeometricErdosSimilarity
