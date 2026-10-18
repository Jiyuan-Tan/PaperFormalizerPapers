module
public import Papers.TbsPrteOptimalTransport.Helpers.TailAttainment
/-! Coverage and separation of the conditional gap, LIV, and tail regions. -/
public section
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v

-- @node: range_prefix_covered
/-- If [n indexes an available range component](hyp:hn), [the rank u is positive](hyp:hu),
[is at most one](hyp:hu1), and [does not exceed component n's upper endpoint](hyp:hhigh),
then [u belongs to an LIV interval or gap with index at most n](goal). -/
lemma range_prefix_covered (D : RangeData) (n : ℕ) (hn : n < D.count)
    {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (hhigh : u ≤ D.high n) :
    ∃ k, k ≤ n ∧ (u ∈ D.liv k ∨ u ∈ RangeDecomposition.gap D k) := by
  induction n with
  | zero =>
    refine ⟨0, le_rfl, ?_⟩
    by_cases hl : u < D.low 0
    · exact Or.inr ⟨⟨by simpa [RangeData.gapLo] using hu, hl⟩, hu.le, hu1⟩
    · exact Or.inl ⟨le_of_not_gt hl, hhigh⟩
  | succ n ih =>
    by_cases hp : u ≤ D.high n
    · obtain ⟨k, hk, hmem⟩ := ih (by omega) hp
      exact ⟨k, hk.trans (Nat.le_succ n), hmem⟩
    · refine ⟨n + 1, le_rfl, ?_⟩
      by_cases hl : u < D.low (n + 1)
      · apply Or.inr
        exact ⟨⟨by simpa [RangeData.gapLo] using lt_of_not_ge hp, hl⟩, hu.le, hu1⟩
      · exact Or.inl ⟨le_of_not_gt hl, hhigh⟩

-- @node: range_regions_cover_positive
/-- If [u lies in the unit interval with zero excluded](hyp:hu), then
[u belongs to an indexed LIV interval, an indexed gap, or the tail](goal). -/
lemma range_regions_cover_positive (D : RangeData) {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1) :
    u ∈ (⋃ k ∈ Iio D.count, D.liv k) ∪
      (⋃ k ∈ Iio D.count, RangeDecomposition.gap D k) ∪ D.tail := by
  by_cases ht : D.tailLo < u
  · exact Or.inr ⟨ht, hu.2⟩
  · have hn : D.count ≠ 0 := by
      intro hz
      have hzero : D.tailLo = 0 := by simp [RangeData.tailLo, hz]
      exact ht (hzero ▸ hu.1)
    have hh : u ≤ D.high (D.count - 1) := by
      simpa [RangeData.tailLo, hn] using le_of_not_gt ht
    obtain ⟨k, hk, hm⟩ := range_prefix_covered D (D.count - 1) (by omega) hu.1 hu.2 hh
    have hk' : k ∈ Iio D.count := by change k < D.count; omega
    rcases hm with hl | hg
    · exact Or.inl (Or.inl (mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hk', hl⟩⟩))
    · exact Or.inl (Or.inr (mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hk', hg⟩⟩))

-- @node: range_regions_partition_null
/-- [The part of the unit interval outside all indexed LIV intervals, gaps, and the tail
has Lebesgue measure zero](goal). -/
lemma range_regions_partition_null (D : RangeData) : RegionsPartitionNullReading D := by
  apply measure_mono_null (t := ({0} : Set ℝ)) _ (measure_singleton 0)
  intro u hu
  have hz : u = 0 := by
    by_contra hn
    have hp : 0 < u := lt_of_le_of_ne hu.1.1 (Ne.symm hn)
    exact hu.2 (range_regions_cover_positive D ⟨hp, hu.1.2⟩)
  exact hz

-- @node: conditional_regions_partition_null
/-- [For almost every covariate value, the conditional LIV intervals, gaps, and tail
cover the unit interval up to a Lebesgue null set](goal). -/
lemma conditional_regions_partition_null
    {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z]
    [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
    [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
    (M : LatentIVModel Ω X Z) : CondRegionsPartitionNullReading M := by
  exact Filter.Eventually.of_forall fun x => range_regions_partition_null _

-- @node: range_low_le_high
/-- If [the range decomposition is valid for R](hyp:hD) and
[k indexes an available component](hyp:hk), then
[its lower endpoint does not exceed its upper endpoint](goal). -/
lemma range_low_le_high (D : RangeData) (R : Set ℝ) (hD : D.Valid R)
    {k : ℕ} (hk : k < D.count) : D.low k ≤ D.high k := by
  have hk' : k < D.1 := hk
  simpa only [RangeData.low, RangeData.high, dif_pos hk'] using (hD.1 ⟨k, hk'⟩).2.1

-- @node: range_high_lt_low
/-- If [the range decomposition is valid for R](hyp:hD), [k precedes l](hyp:hkl),
and [l indexes an available component](hyp:hl), then
[component k's upper endpoint is strictly below component l's lower endpoint](goal). -/
lemma range_high_lt_low (D : RangeData) (R : Set ℝ) (hD : D.Valid R)
    {k l : ℕ} (hkl : k < l) (hl : l < D.count) : D.high k < D.low l := by
  have hk' : k < D.1 := hkl.trans hl
  have hl' : l < D.1 := hl
  simpa only [RangeData.low, RangeData.high, dif_pos hk', dif_pos hl'] using
    hD.2.1 ⟨k, hk'⟩ ⟨l, hl'⟩ hkl

-- @node: range_liv_pairwise_disjoint
/-- If [the range decomposition is valid for R](hyp:hD), then
[its indexed LIV intervals are pairwise disjoint](goal). -/
lemma range_liv_pairwise_disjoint (D : RangeData) (R : Set ℝ) (hD : D.Valid R) :
    (Iio D.count).Pairwise (fun k l => Disjoint (D.liv k) (D.liv l)) := by
  intro k hk l hl hne
  apply disjoint_left.mpr
  intro u huk hul
  rcases lt_or_gt_of_ne hne with hkl | hlk
  · exact (not_le_of_gt (range_high_lt_low D R hD hkl hl)) (hul.1.trans huk.2)
  · exact (not_le_of_gt (range_high_lt_low D R hD hlk hk)) (huk.1.trans hul.2)

-- @node: range_high_mono
/-- If [the range decomposition is valid for R](hyp:hD), [k is at most l](hyp:hkl),
and [l indexes an available component](hyp:hl), then
[component k's upper endpoint does not exceed component l's upper endpoint](goal). -/
lemma range_high_mono (D : RangeData) (R : Set ℝ) (hD : D.Valid R)
    {k l : ℕ} (hkl : k ≤ l) (hl : l < D.count) : D.high k ≤ D.high l := by
  rcases eq_or_lt_of_le hkl with rfl | hlt
  · exact le_rfl
  · exact (range_high_lt_low D R hD hlt hl).le.trans (range_low_le_high D R hD hl)

-- @node: range_liv_gap_disjoint
/-- If [the range decomposition is valid for R](hyp:hD) and
[k and l index available components](hyp:hk,hl), then
[the LIV interval at k is disjoint from the gap at l](goal). -/
lemma range_liv_gap_disjoint (D : RangeData) (R : Set ℝ) (hD : D.Valid R)
    {k l : ℕ} (hk : k < D.count) (hl : l < D.count) :
    Disjoint (D.liv k) (RangeDecomposition.gap D l) := by
  apply disjoint_left.mpr
  intro u huk hul
  have hul := hul.1
  rcases le_or_gt l k with hlk | hkl
  · have hlow : D.low l ≤ D.low k := by
      rcases eq_or_lt_of_le hlk with rfl | hlt
      · exact le_rfl
      · exact (range_low_le_high D R hD hl).trans (range_high_lt_low D R hD hlt hk).le
    exact (not_lt_of_ge (hlow.trans huk.1)) hul.2
  · have hl0 : l ≠ 0 := by omega
    have hp : l - 1 < D.count := by omega
    have hh := range_high_mono D R hD (show k ≤ l - 1 by omega) hp
    have hgap : D.high (l - 1) < u := by simpa [RangeData.gapLo, hl0] using hul.1
    exact (not_lt_of_ge (huk.2.trans hh)) hgap

-- @node: range_gap_pairwise_disjoint
/-- If [the range decomposition is valid for R](hyp:hD), then
[its indexed gaps are pairwise disjoint](goal). -/
lemma range_gap_pairwise_disjoint (D : RangeData) (R : Set ℝ) (hD : D.Valid R) :
    (Iio D.count).Pairwise (fun k l =>
      Disjoint (RangeDecomposition.gap D k) (RangeDecomposition.gap D l)) := by
  have ordered {k l : ℕ} (hkl : k < l) (hl : l < D.count) :
      Disjoint (RangeDecomposition.gap D k) (RangeDecomposition.gap D l) := by
    apply disjoint_left.mpr
    intro u huk hul
    have huk := huk.1
    have hul := hul.1
    have hl0 : l ≠ 0 := by omega
    have hh := range_high_mono D R hD (show k ≤ l - 1 by omega)
      (show l - 1 < D.count by omega)
    have hlh := range_low_le_high D R hD (hkl.trans hl)
    have hgap : D.high (l - 1) < u := by simpa [RangeData.gapLo, hl0] using hul.1
    exact (not_lt_of_ge (hlh.trans hh)) (hgap.trans huk.2)
  intro k hk l hl hne
  rcases lt_or_gt_of_ne hne with hkl | hlk
  · exact ordered hkl hl
  · exact (ordered hlk hk).symm

-- @node: range_liv_tail_disjoint
/-- If [the range decomposition is valid for R](hyp:hD) and
[k indexes an available component](hyp:hk), then
[the LIV interval at k is disjoint from the tail](goal). -/
lemma range_liv_tail_disjoint (D : RangeData) (R : Set ℝ) (hD : D.Valid R)
    {k : ℕ} (hk : k < D.count) : Disjoint (D.liv k) D.tail := by
  have hn : D.count ≠ 0 := by omega
  have hh := range_high_mono D R hD (show k ≤ D.count - 1 by omega)
    (show D.count - 1 < D.count by omega)
  apply disjoint_left.mpr
  intro u huk hut
  have ht : D.high (D.count - 1) < u := by simpa [RangeData.tailLo, hn] using hut.1
  exact (not_lt_of_ge (huk.2.trans hh)) ht

-- @node: range_gap_tail_disjoint
/-- If [the range decomposition is valid for R](hyp:hD) and
[k indexes an available component](hyp:hk), then
[the gap at k is disjoint from the tail](goal). -/
lemma range_gap_tail_disjoint (D : RangeData) (R : Set ℝ) (hD : D.Valid R)
    {k : ℕ} (hk : k < D.count) : Disjoint (RangeDecomposition.gap D k) D.tail := by
  have hn : D.count ≠ 0 := by omega
  have hh := (range_low_le_high D R hD hk).trans
    (range_high_mono D R hD (show k ≤ D.count - 1 by omega)
      (show D.count - 1 < D.count by omega))
  apply disjoint_left.mpr
  intro u huk hut
  have huk := huk.1
  have ht : D.high (D.count - 1) < u := by simpa [RangeData.tailLo, hn] using hut.1
  exact (not_lt_of_ge hh) (ht.trans huk.2)

variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)

-- @node: pasted_attaining_law_on_gap
/-- If [the conditional decomposition at x is valid for the propensity range](hyp:hv),
[k indexes one of its components](hyp:hk), and [u belongs to its k-th gap](hyp:hu), then
[the pasted attaining outcome law at x and u equals the gap attaining law for k](goal). -/
lemma pasted_attaining_law_on_gap (om : X → ℝ → ℝ) (Q : X → ℕ → ℝ → ℝ)
    (x : X) (hv : (CondRangeDecomposition M x).Valid (range (fun z => M.prop z x)))
    (k : ℕ) (hk : k < (CondRangeDecomposition M x).count)
    (u : ℝ) (hu : u ∈ RangeDecomposition.gap (CondRangeDecomposition M x) k) :
    pastedAttainingLaw M om Q x u = gapAttainingLaw M om Q x k u := by
  let D := CondRangeDecomposition M x
  have hex : ∃ j, j < D.count ∧ u ∈ RangeDecomposition.gap D j := ⟨k, hk, hu⟩
  have he : Classical.choose hex = k := by
    obtain ⟨hj, hmem⟩ := Classical.choose_spec hex
    by_contra hne
    exact (disjoint_left.mp (range_gap_pairwise_disjoint D _ hv hj hk hne)) hmem hu
  change (if h : ∃ j, j < D.count ∧ u ∈ RangeDecomposition.gap D j then
    gapAttainingLaw M om Q x (Classical.choose h) u else _) = _
  rw [dif_pos hex, he]

-- @node: pasted_attaining_law_on_liv
/-- If [the conditional decomposition at x is valid for the propensity range](hyp:hv),
[k indexes one of its components](hyp:hk), and [u belongs to its k-th LIV interval](hyp:hu),
then [the pasted attaining law at x and u equals the treated latent outcome law](goal). -/
lemma pasted_attaining_law_on_liv (om : X → ℝ → ℝ) (Q : X → ℕ → ℝ → ℝ)
    (x : X) (hv : (CondRangeDecomposition M x).Valid (range (fun z => M.prop z x)))
    (k : ℕ) (hk : k < (CondRangeDecomposition M x).count)
    (u : ℝ) (hu : u ∈ (CondRangeDecomposition M x).liv k) :
    pastedAttainingLaw M om Q x u = outcomeKernel (latentMarginal M true) (u, x) := by
  let D := CondRangeDecomposition M x
  have hn : ¬ ∃ j, j < D.count ∧ u ∈ RangeDecomposition.gap D j := by
    rintro ⟨j, hj, hmem⟩
    exact disjoint_left.mp (range_liv_gap_disjoint D _ hv hk hj) hu hmem
  have ht : u ∉ D.tail := fun hut =>
    disjoint_left.mp (range_liv_tail_disjoint D _ hv hk) hu hut
  change (if h : ∃ j, j < D.count ∧ u ∈ RangeDecomposition.gap D j then _
    else if u ∈ D.tail then _ else _) = _
  rw [dif_neg hn, if_neg ht]

-- @node: pasted_attaining_law_on_tail
/-- If [the conditional decomposition at x is valid for the propensity range](hyp:hv)
and [u belongs to its tail](hyp:hu), then [the pasted attaining law puts all mass at
the lower outcome endpoint when the target weight is nonnegative, and at the upper
endpoint otherwise](goal). -/
lemma pasted_attaining_law_on_tail (om : X → ℝ → ℝ) (Q : X → ℕ → ℝ → ℝ)
    (x : X) (hv : (CondRangeDecomposition M x).Valid (range (fun z => M.prop z x)))
    (u : ℝ) (hu : u ∈ (CondRangeDecomposition M x).tail) :
    pastedAttainingLaw M om Q x u =
      Measure.dirac (if 0 ≤ om x u then M.yMin else M.yMax) := by
  let D := CondRangeDecomposition M x
  have hn : ¬ ∃ j, j < D.count ∧ u ∈ RangeDecomposition.gap D j := by
    rintro ⟨j, hj, hmem⟩
    exact disjoint_left.mp (range_gap_tail_disjoint D _ hv hj) hmem hu
  change (if h : ∃ j, j < D.count ∧ u ∈ RangeDecomposition.gap D j then _
    else if u ∈ D.tail then _ else _) = _
  rw [dif_neg hn, if_pos hu]

-- @node: pasted_attaining_law_isProbability
/-- If [Q supplies the rank kernel extension](hyp:hQ), then
[the pasted attaining outcome law is a probability measure at every covariate value
and rank](goal). -/
lemma pasted_attaining_law_isProbability (om : X → ℝ → ℝ) (Q : X → ℕ → ℝ → ℝ)
    (hQ : RankKernelExtensionReading M Q) (x : X) (u : ℝ) :
    IsProbabilityMeasure (pastedAttainingLaw M om Q x u) := by
  by_cases hg : ∃ k, k < (CondRangeDecomposition M x).count ∧
      u ∈ RangeDecomposition.gap (CondRangeDecomposition M x) k
  · rw [pastedAttainingLaw, dif_pos hg]
    exact gap_attaining_law_isProbability M om Q hQ x _ u
  · rw [pastedAttainingLaw, dif_neg hg]
    split
    · infer_instance
    · letI := outcomeKernel_isMarkov (latentMarginal M true)
      infer_instance

-- @node: pasted_attaining_gap_cost
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[continuity of propensity on instrument components](hyp:hc), and
[finitely many instrument components](hyp:hfin), with [a measurable target weight](hyp:hm)
that [is integrable](hyp:hi) and [Q supplying the rank kernel extension](hyp:hQ),
[for almost every covariate value, the pasted law's weighted outcome integral on each
gap equals the nonnegative gap length times the integral of the outcome and weight
quantiles paired at opposite ranks](goal). -/
lemma pasted_attaining_gap_cost (h : StructuralAssumptions M)
    (he : OutcomeEndpointsKnown M) (hc : PropensityContinuousOnComponents M)
    (hfin : FiniteInstrumentComponents Z) (om : X → ℝ → ℝ)
    (hm : TargetWeightMeasurable om) (hi : TargetWeightIntegrable M om)
    (Q : X → ℕ → ℝ → ℝ) (hQ : RankKernelExtensionReading M Q) :
    ∀ᵐ x ∂xLaw M, ∀ k < (CondRangeDecomposition M x).count,
      (∫ u in RangeDecomposition.gap (CondRangeDecomposition M x) k,
        (∫ y, y ∂pastedAttainingLaw M om Q x u) * om x u) =
      max 0 ((CondRangeDecomposition M x).gapHi k - (CondRangeDecomposition M x).gapLo k) *
        ∫ t in Ioo (0 : ℝ) 1, (gapQuantiles M om x k).1 t *
          (gapQuantiles M om x k).2 (1 - t) := by
  filter_upwards [range_decomposition_valid M h hfin hc,
    gap_attaining_region_cost M h he om hm hi Q hQ] with x hv hcost
  intro k hk
  by_cases hab : (CondRangeDecomposition M x).gapLo k < (CondRangeDecomposition M x).gapHi k
  · calc
      _ = ∫ u in RangeDecomposition.gap (CondRangeDecomposition M x) k,
          (∫ y, y ∂gapAttainingLaw M om Q x k u) * om x u := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem (measurableSet_Ioo.inter measurableSet_Icc)] with u hu
        rw [pasted_attaining_law_on_gap M om Q x hv k hk u hu]
      _ = _ := hcost k hk hab
  · have hempty : RangeDecomposition.gap (CondRangeDecomposition M x) k = ∅ :=
      by
        rw [conditional_gap_eq_Ioo M x k hk]
        exact Ioo_eq_empty_of_le (le_of_not_gt hab)
    rw [hempty, Measure.restrict_empty, integral_zero_measure,
      max_eq_left (sub_nonpos.mpr (le_of_not_gt hab)), zero_mul]

-- @node: pasted_attaining_liv_cost
/-- If [the conditional decomposition at x is valid for the propensity range](hyp:hv)
and [k indexes one of its components](hyp:hk), then [the target-weighted mean outcome
integrated over its k-th LIV interval is the same for the pasted attaining law and
the treated latent outcome law](goal). -/
lemma pasted_attaining_liv_cost (om : X → ℝ → ℝ) (Q : X → ℕ → ℝ → ℝ)
    (x : X) (hv : (CondRangeDecomposition M x).Valid (range (fun z => M.prop z x)))
    (k : ℕ) (hk : k < (CondRangeDecomposition M x).count) :
    (∫ u in (CondRangeDecomposition M x).liv k,
      (∫ y, y ∂pastedAttainingLaw M om Q x u) * om x u) =
    ∫ u in (CondRangeDecomposition M x).liv k,
      (∫ y, y ∂outcomeKernel (latentMarginal M true) (u, x)) * om x u := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  rw [pasted_attaining_law_on_liv M om Q x hv k hk u hu]

-- @node: pasted_attaining_tail_cost
/-- If [the conditional decomposition at x is valid for the propensity range](hyp:hv),
then [the pasted law's target-weighted outcome integral over the tail equals the
integral of the lower outcome endpoint times the positive part of the weight plus
the upper endpoint times the negative part of the weight](goal). -/
lemma pasted_attaining_tail_cost (om : X → ℝ → ℝ) (Q : X → ℕ → ℝ → ℝ)
    (x : X) (hv : (CondRangeDecomposition M x).Valid (range (fun z => M.prop z x))) :
    (∫ u in (CondRangeDecomposition M x).tail,
      (∫ y, y ∂pastedAttainingLaw M om Q x u) * om x u) =
    ∫ u in (CondRangeDecomposition M x).tail,
      M.yMin * max 0 (om x u) + M.yMax * min 0 (om x u) := by
  calc
    _ = ∫ u in (CondRangeDecomposition M x).tail,
        (∫ y : ℝ, y ∂Measure.dirac (if 0 ≤ om x u then M.yMin else M.yMax)) * om x u := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      rw [pasted_attaining_law_on_tail M om Q x hv u hu]
    _ = _ := tail_region_cost M false om x

end Papers.TbsPrteOptimalTransport
