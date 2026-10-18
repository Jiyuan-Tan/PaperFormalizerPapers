module
public import Papers.TbsPrteOptimalTransport.TCovariateLowerBound
public import Mathlib.Order.Interval.Set.Infinite
/-! Finite instrument ranges have singleton LIV regions. -/
@[expose] public section
set_option linter.style.openClassical false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

-- @node: singletonRangeData
/-- For [a list of real levels](hyp:levels), the [singleton range data](goal) have
one component per list entry, with both endpoints equal to that entry. -/
def singletonRangeData (levels : List ℝ) : RangeData :=
  ⟨levels.length, (fun i => levels.get i), (fun i => levels.get i)⟩

-- @node: singletonRangeData_valid
/-- If [the levels are strictly increasing](hyp:hs) and [every level lies between
zero and one](hyp:hu), then [their singleton components form a valid ordered
decomposition of the set of listed levels](goal). -/
lemma singletonRangeData_valid (levels : List ℝ) (hs : levels.SortedLT)
    (hu : ∀ y ∈ levels, y ∈ Icc (0 : ℝ) 1) :
    (singletonRangeData levels).Valid {y | y ∈ levels} := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hi := hu _ (List.get_mem levels i)
    exact ⟨hi.1, le_rfl, hi.2⟩
  · intro i j hij
    exact hs.strictMono_get hij
  · ext y
    simp only [mem_ofPred_eq, mem_iUnion, mem_Icc]
    constructor
    · intro hy
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hy
      exact ⟨i, hi ▸ ⟨le_rfl, le_rfl⟩⟩
    · rintro ⟨i, hi⟩
      have he : y = levels.get i := le_antisymm hi.2 hi.1
      exact he ▸ List.get_mem levels i

-- @node: finite_rangeData_endpoints_eq
/-- If [the interval data validly decompose a set](hyp:hD) and [that set is
finite](hyp:hR), then [the lower and upper endpoints of every component coincide](goal). -/
lemma finite_rangeData_endpoints_eq (D : RangeData) {R : Set ℝ}
    (hD : D.Valid R) (hR : R.Finite) (i : Fin D.count) :
    D.2.1 i = D.2.2 i := by
  have hsub : Icc (D.2.1 i) (D.2.2 i) ⊆ R := by
    rw [hD.2.2]
    exact subset_iUnion_of_subset i (Subset.refl _)
  have hfinite := hR.subset hsub
  apply le_antisymm (hD.1 i).2.1
  by_contra hn
  exact (Icc_infinite (lt_of_not_ge hn)).not_finite hfinite

-- @node: finite_rangeData_liv_eq_singleton
/-- If [the interval data validly decompose a set](hyp:hD), [the set is finite](hyp:hR),
and [the component index is below the component count](hyp:hk), then [its local
instrumental-variable region consists only of its lower endpoint](goal). -/
lemma finite_rangeData_liv_eq_singleton (D : RangeData) {R : Set ℝ}
    (hD : D.Valid R) (hR : R.Finite) {k : ℕ} (hk : k < D.count) :
    D.liv k = {D.low k} := by
  change k < D.1 at hk
  have he := finite_rangeData_endpoints_eq D hD hR ⟨k, hk⟩
  have he' : D.low k = D.high k := by
    simpa only [RangeData.low, RangeData.high, RangeData.count, dif_pos hk] using he
  rw [RangeData.liv, ← he', Icc_self]

-- @node: finite_rangeData_liv_integral_zero
/-- If [the interval data validly decompose a set](hyp:hD) and [the set is finite](hyp:hR),
then [the sum of the Lebesgue integrals of any component-specific function over
the local instrumental-variable regions is zero](goal). -/
lemma finite_rangeData_liv_integral_zero (D : RangeData) {R : Set ℝ}
    (hD : D.Valid R) (hR : R.Finite) (f : ℕ → ℝ → ℝ) :
    (∑ k ∈ Finset.range D.count, ∫ u in D.liv k, f k u) = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  rw [finite_rangeData_liv_eq_singleton D hD hR (Finset.mem_range.mp hk)]
  simp

-- @node: finiteRangeLevels
/-- For [a real-valued propensity function on the instrument domain](hyp:p), the
[range-level list](goal) prepends zero to the ordered positive-level list if zero
is attained, and otherwise uses the positive-level list alone. -/
noncomputable def finiteRangeLevels {Z : Type*} (p : Z → ℝ) : List ℝ :=
  if 0 ∈ range p then 0 :: finiteLevels p else finiteLevels p

section Levels
variable {Z : Type*} [MeasurableSpace Z] [TopologicalSpace Z]
  [BorelSpace Z] [StandardBorelSpace Z] [Nonempty Z]

-- @node: finiteLevels_mem_iff
/-- If [the instrument domain is finite](hyp:hf), then [a real number belongs to
the ordered positive-level list exactly when it is an attained, strictly positive
propensity value](goal). -/
lemma finiteLevels_mem_iff (p : Z → ℝ) (hf : Finite Z) (y : ℝ) :
    y ∈ finiteLevels p ↔ y ∈ range p ∧ 0 < y := by
  letI : Finite Z := hf
  have hset : (range p ∩ Ioi 0).Finite := (finite_range p).inter_of_left _
  simp only [finiteLevels, dif_pos hset, Finset.mem_sort, hset.mem_toFinset,
    mem_inter_iff, mem_Ioi]

-- @node: finiteRangeLevels_mem
/-- If [the instrument domain is finite](hyp:hf) and [all propensity values lie
between zero and one](hyp:hp), then [membership in the range-level list is
equivalent to being an attained propensity value](goal). -/
lemma finiteRangeLevels_mem (p : Z → ℝ)
    (hf : Finite Z) (hp : ∀ z, p z ∈ Icc (0 : ℝ) 1) (y : ℝ) :
    y ∈ finiteRangeLevels p ↔ y ∈ range p := by
  unfold finiteRangeLevels
  split_ifs with hz
  · rw [List.mem_cons, finiteLevels_mem_iff p hf]
    constructor
    · rintro (rfl | ⟨hy, _⟩)
      · exact hz
      · exact hy
    · intro hy
      by_cases hy0 : y = 0
      · exact Or.inl hy0
      · obtain ⟨z, rfl⟩ := hy
        exact Or.inr ⟨mem_range_self _, lt_of_le_of_ne (hp z).1 (Ne.symm hy0)⟩
  · rw [finiteLevels_mem_iff p hf]
    constructor
    · exact And.left
    · intro hy
      have hy0 : y ≠ 0 := fun he => hz (he ▸ hy)
      obtain ⟨z, rfl⟩ := hy
      exact ⟨mem_range_self _, lt_of_le_of_ne (hp z).1 (Ne.symm hy0)⟩

-- @node: finiteRangeLevels_sorted
/-- If [the instrument domain is finite](hyp:hf), then [the range-level list is
strictly increasing](goal). -/
lemma finiteRangeLevels_sorted (p : Z → ℝ) (hf : Finite Z) :
    (finiteRangeLevels p).SortedLT := by
  unfold finiteRangeLevels
  split_ifs
  · apply List.Pairwise.sortedLT
    exact List.pairwise_cons.mpr ⟨fun y hy => (finiteLevels_mem p hf hy).2,
      (finiteLevels_sorted p hf).pairwise⟩
  · exact finiteLevels_sorted p hf

-- @node: finiteRangeLevels_valid
/-- If [the instrument domain is finite](hyp:hf) and [all propensity values lie
between zero and one](hyp:hp), then [the singleton components of the range-level
list form a valid decomposition of the propensity range](goal). -/
lemma finiteRangeLevels_valid (p : Z → ℝ)
    (hf : Finite Z) (hp : ∀ z, p z ∈ Icc (0 : ℝ) 1) :
    (singletonRangeData (finiteRangeLevels p)).Valid (range p) := by
  have hm : {y | y ∈ finiteRangeLevels p} = range p := by
    ext y
    exact finiteRangeLevels_mem p hf hp y
  rw [← hm]
  apply singletonRangeData_valid _ (finiteRangeLevels_sorted p hf)
  intro y hy
  obtain ⟨z, rfl⟩ := (finiteRangeLevels_mem p hf hp y).mp hy
  exact hp z

-- @node: finite_range_decomposition_eq
/-- If [the instrument domain is finite](hyp:hf) and [all propensity values lie
between zero and one](hyp:hp), then [the canonical decomposition of the propensity
range equals the singleton data built from its range-level list](goal). -/
lemma finite_range_decomposition_eq (p : Z → ℝ)
    (hf : Finite Z) (hp : ∀ z, p z ∈ Icc (0 : ℝ) 1) :
    RangeDecomposition (range p) = singletonRangeData (finiteRangeLevels p) := by
  have hv := finiteRangeLevels_valid p hf hp
  have he : ∃ D : RangeData, D.Valid (range p) := ⟨_, hv⟩
  apply rangeData_valid_unique _ _ _ hv
  simpa only [RangeDecomposition, dif_pos he] using Classical.choose_spec he

end Levels

-- @node: singletonRangeData_low
/-- If [the index is below the number of listed levels](hyp:hk), then [the lower
endpoint of that singleton component equals the list entry at that index](goal). -/
lemma singletonRangeData_low (levels : List ℝ) {k : ℕ} (hk : k < levels.length) :
    (singletonRangeData levels).low k = levels.getD k 0 := by
  rw [RangeData.low, dif_pos (show k < (singletonRangeData levels).1 from hk)]
  change levels.get ⟨k, hk⟩ = _
  rw [List.getD_eq_getElem _ _ hk]
  rfl

-- @node: singletonRangeData_high
/-- If [the index is below the number of listed levels](hyp:hk), then [the upper
endpoint of that singleton component equals the list entry at that index](goal). -/
lemma singletonRangeData_high (levels : List ℝ) {k : ℕ} (hk : k < levels.length) :
    (singletonRangeData levels).high k = levels.getD k 0 := by
  rw [RangeData.high, dif_pos (show k < (singletonRangeData levels).1 from hk)]
  change levels.get ⟨k, hk⟩ = _
  rw [List.getD_eq_getElem _ _ hk]
  rfl

-- @node: positive_singleton_gap_endpoints
/-- If [the gap index is below the number of listed levels](hyp:hk), then [the
gap's lower and upper endpoints in the singleton decomposition are the indexed
level and its successor, with level zero defined as zero](goal). -/
lemma positive_singleton_gap_endpoints (levels : List ℝ) {k : ℕ}
    (hk : k < levels.length) :
    (singletonRangeData levels).gapLo k = pLevel levels k ∧
      (singletonRangeData levels).gapHi k = pLevel levels (k+1) := by
  constructor
  · by_cases hz : k = 0
    · subst k
      simp [RangeData.gapLo, pLevel]
    · rw [RangeData.gapLo, if_neg hz, singletonRangeData_high levels (by omega)]
      simp only [pLevel, if_neg hz, if_pos hk.le]
  · rw [RangeData.gapHi, singletonRangeData_low levels hk]
    simp only [pLevel, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
      ↓reduceIte, show k + 1 ≤ levels.length from hk, Nat.add_sub_cancel]

-- @node: zero_cons_singleton_gap_endpoints
/-- If [the index is below the number of listed levels](hyp:hk), then [after
prepending zero, the gap at the successor index has endpoints given by the original
indexed level and its successor, with level zero defined as zero](goal). -/
lemma zero_cons_singleton_gap_endpoints (levels : List ℝ) {k : ℕ}
    (hk : k < levels.length) :
    (singletonRangeData (0 :: levels)).gapLo (k+1) = pLevel levels k ∧
      (singletonRangeData (0 :: levels)).gapHi (k+1) = pLevel levels (k+1) := by
  constructor
  · rw [RangeData.gapLo, if_neg (by omega), Nat.add_sub_cancel,
      singletonRangeData_high (0 :: levels) (by simpa using hk.le)]
    cases k with
    | zero => simp [pLevel]
    | succ k => simp [pLevel, hk.le, List.getD,
        List.getElem?_eq_getElem (show k < levels.length by omega)]
  · rw [RangeData.gapHi, singletonRangeData_low (0 :: levels) (by simpa using hk)]
    simp [pLevel, show k + 1 ≤ levels.length from hk, List.getD,
      List.getElem?_eq_getElem hk]

-- @node: finite_singleton_tailLo
/-- [The lower endpoint of the tail in the singleton decomposition is the last
listed level, or zero when the list is empty](goal). -/
lemma finite_singleton_tailLo (levels : List ℝ) :
    (singletonRangeData levels).tailLo = pLevel levels levels.length := by
  change (if levels.length = 0 then 0 else
    (singletonRangeData levels).high (levels.length - 1)) = _
  by_cases hz : levels.length = 0
  · simp [hz, pLevel]
  · rw [if_neg hz, singletonRangeData_high levels (by omega)]
    simp [pLevel, hz]

-- @node: zero_cons_singleton_tailLo
/-- [Prepending zero to the level list gives a singleton decomposition whose tail
starts at the last original level, or at zero if the original list is empty](goal). -/
lemma zero_cons_singleton_tailLo (levels : List ℝ) :
    (singletonRangeData (0 :: levels)).tailLo = pLevel levels levels.length := by
  change (if (0 :: levels).length = 0 then 0 else
    (singletonRangeData (0 :: levels)).high ((0 :: levels).length - 1)) = _
  simp only [List.length_cons, Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
  rw [singletonRangeData_high (0 :: levels) (by simp)]
  cases levels with
  | nil => simp [pLevel]
  | cons y ys => simp [pLevel]

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)

-- @node: conditionalGapTerm
/-- For [a latent instrumental-variable model](hyp:M), [an upper-versus-lower bound
selector](hyp:upper), [a covariate-dependent resistance weight](hyp:om), [a covariate
value](hyp:x), and [a gap index](hyp:k), the [conditional gap contribution](goal)
[uses the conditional propensity-range decomposition](step:1), then [multiplies
the nonnegative gap width by the integral over unit ranks of the outcome quantile
times the weight quantile, pairing equal ranks for the upper bound and opposite
ranks for the lower bound](step:2). -/
noncomputable def conditionalGapTerm (upper : Bool) (om : X → ℝ → ℝ)
    (x : X) (k : ℕ) : ℝ :=
  let D := CondRangeDecomposition M x
  max 0 (D.gapHi k - D.gapLo k) *
    ∫ t in Ioo (0 : ℝ) 1, (gapQuantiles M om x k).1 t *
      (gapQuantiles M om x k).2 (if upper then t else 1-t)

-- @node: conditional_gap_term_eq_interval
/-- If [the conditional gap endpoints equal two consecutive finite propensity
levels](hyp:he) and [these levels are strictly ordered](hyp:hw), then [the conditional
gap contribution equals their difference times the unit-rank integral of the
corresponding interval outcome and weight quantiles, paired at equal ranks for the
upper bound and opposite ranks for the lower bound](goal). -/
lemma conditional_gap_term_eq_interval (upper : Bool) (om : X → ℝ → ℝ)
    (x : X) (k i : ℕ)
    (he : (CondRangeDecomposition M x).gapLo k =
        pLevel (finiteLevels (fun z => M.prop z x)) i ∧
      (CondRangeDecomposition M x).gapHi k =
        pLevel (finiteLevels (fun z => M.prop z x)) (i+1))
    (hw : pLevel (finiteLevels (fun z => M.prop z x)) i <
      pLevel (finiteLevels (fun z => M.prop z x)) (i+1)) :
    conditionalGapTerm M upper om x k =
      (pLevel (finiteLevels (fun z => M.prop z x)) (i+1) -
        pLevel (finiteLevels (fun z => M.prop z x)) i) *
      ∫ t in Ioo (0 : ℝ) 1, (conditionalIntervalQuantiles M om x i).1 t *
        (conditionalIntervalQuantiles M om x i).2 (if upper then t else 1-t) := by
  have hg : (CondRangeDecomposition M x).gapLo k <
      (CondRangeDecomposition M x).gapHi k := by rw [he.1, he.2]; exact hw
  unfold conditionalGapTerm
  dsimp only
  rw [he.1, he.2, max_eq_right (sub_pos.mpr hw).le]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have ht0 : t ≠ 0 := ne_of_gt ht.1
  have ht1 : t ≠ 1 := ne_of_lt ht.2
  simp only [gapQuantiles, endpointGapQuantile, if_neg ht0, if_neg ht1,
    gapLaw, if_pos hg, conditionalIntervalQuantiles, conditionalIntervalLaw,
    weightLaw, weightLawInt, gapUnif, he.1, he.2, if_pos hw]

-- @node: conditional_gap_term_zero
/-- If [the conditional gap's upper and lower endpoints coincide](hyp:he), then
[its conditional bound contribution is zero](goal). -/
lemma conditional_gap_term_zero (upper : Bool) (om : X → ℝ → ℝ)
    (x : X) (k : ℕ)
    (he : (CondRangeDecomposition M x).gapHi k =
      (CondRangeDecomposition M x).gapLo k) :
    conditionalGapTerm M upper om x k = 0 := by
  simp only [conditionalGapTerm, he, sub_self, max_self, zero_mul]

-- @node: finite_instrument_components
/-- If [the instrument domain is finite](hyp:hf), then [it has finitely many
connected components](goal). -/
lemma finite_instrument_components (hf : Finite Z) : FiniteInstrumentComponents Z := by
  letI : Finite Z := hf
  exact Finite.of_surjective ConnectedComponents.mk ConnectedComponents.surjective_coe

-- @node: finite_instrument_propensity_continuous
/-- If [the instrument domain is finite and has the discrete topology](hyp:hf),
then [the propensity is continuous on each connected component for almost every
covariate value](goal). -/
lemma finite_instrument_propensity_continuous (hf : InstrumentFinite Z) :
    PropensityContinuousOnComponents M := by
  letI : DiscreteTopology Z := hf.2
  exact Eventually.of_forall fun _ _ => (continuous_of_discreteTopology).continuousOn

-- @node: finite_conditional_bound_without_liv
/-- Under [the model's structural assumptions](hyp:h) and [a finite instrument
domain with the discrete topology](hyp:hf), [for almost every covariate value the
conditional bound integrand equals the sum of the nonnegative gap widths times
their outcome-weight quantile integrals, plus the tail integral assigning outcome
endpoints according to the weight's sign and the chosen bound direction](goal). -/
lemma finite_conditional_bound_without_liv (h : StructuralAssumptions M)
    (hf : InstrumentFinite Z) (upper : Bool) (om : X → ℝ → ℝ) :
    ∀ᵐ x ∂xLaw M,
      conditionalBoundIntegrand M upper om x =
        (∑ k ∈ Finset.range (CondRangeDecomposition M x).count,
          max 0 ((CondRangeDecomposition M x).gapHi k -
            (CondRangeDecomposition M x).gapLo k) *
          ∫ t in Ioo (0 : ℝ) 1, (gapQuantiles M om x k).1 t *
            (gapQuantiles M om x k).2 (if upper then t else 1-t)) +
        ∫ u in (CondRangeDecomposition M x).tail,
          (if upper then M.yMax else M.yMin) * max 0 (om x u) +
            (if upper then M.yMin else M.yMax) * min 0 (om x u) := by
  letI : Finite Z := hf.1
  filter_upwards [range_decomposition_valid M h (finite_instrument_components hf.1)
    (finite_instrument_propensity_continuous M hf)] with x hx
  dsimp only [conditionalBoundIntegrand]
  rw [finite_rangeData_liv_integral_zero _ hx (finite_range _) _, add_zero]

-- @node: finite_conditional_bound_eq_interval_sum
/-- If [the instrument domain is finite and has the discrete topology](hyp:hf),
then [at every covariate value the conditional bound integrand equals the sum over
consecutive positive propensity levels, starting from zero, of interval width times
the outcome-weight quantile integral, plus the tail integral above the largest
level assigning outcome endpoints according to the weight's sign and bound
direction](goal). Equal ranks are paired for the upper bound and opposite ranks
for the lower bound. -/
lemma finite_conditional_bound_eq_interval_sum (hf : InstrumentFinite Z)
    (upper : Bool) (om : X → ℝ → ℝ) (x : X) :
    conditionalBoundIntegrand M upper om x =
      (∑ i ∈ Finset.range (finiteLevels (fun z => M.prop z x)).length,
        (pLevel (finiteLevels (fun z => M.prop z x)) (i+1) -
          pLevel (finiteLevels (fun z => M.prop z x)) i) *
        ∫ t in Ioo (0 : ℝ) 1, (conditionalIntervalQuantiles M om x i).1 t *
          (conditionalIntervalQuantiles M om x i).2 (if upper then t else 1-t)) +
      ∫ u in Ioc (pLevel (finiteLevels (fun z => M.prop z x))
        (finiteLevels (fun z => M.prop z x)).length) 1,
        (if upper then M.yMax else M.yMin) * max 0 (om x u) +
          (if upper then M.yMin else M.yMax) * min 0 (om x u) := by
  letI : Finite Z := hf.1
  let ps := finiteLevels (fun z => M.prop z x)
  let D := CondRangeDecomposition M x
  have hD : D = singletonRangeData (finiteRangeLevels (fun z => M.prop z x)) :=
    finite_range_decomposition_eq _ hf.1 (fun z => M.rangeProp z x)
  have hv : D.Valid (range (fun z => M.prop z x)) := by
    rw [hD]
    exact finiteRangeLevels_valid _ hf.1 (fun z => M.rangeProp z x)
  have hw := (finite_levels_ranges (fun z => M.prop z x)
    (fun z => M.rangeProp z x) hf.1).2.1
  dsimp only [conditionalBoundIntegrand]
  rw [finite_rangeData_liv_integral_zero _ hv (finite_range _) _, add_zero]
  change (∑ k ∈ Finset.range D.count, conditionalGapTerm M upper om x k) + _ = _
  have htail : D.tailLo = pLevel ps ps.length := by
    rw [hD]
    unfold finiteRangeLevels
    split_ifs
    · exact zero_cons_singleton_tailLo ps
    · exact finite_singleton_tailLo ps
  rw [show (CondRangeDecomposition M x).tail = Ioc (pLevel ps ps.length) 1 from
    congrArg (fun t => Ioc t 1) htail]
  congr 1
  by_cases hz : 0 ∈ range (fun z => M.prop z x)
  · have hD' : D = singletonRangeData (0 :: ps) := by
      simpa only [finiteRangeLevels, if_pos hz] using hD
    have hcount : D.count = ps.length + 1 := by rw [hD']; rfl
    rw [hcount, Finset.sum_range_succ']
    have hzterm : conditionalGapTerm M upper om x 0 = 0 := by
      apply conditional_gap_term_zero M upper om x 0
      change D.gapHi 0 = D.gapLo 0
      rw [hD', RangeData.gapHi, singletonRangeData_low (0 :: ps) (by simp)]
      simp [RangeData.gapLo]
    rw [hzterm, add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    apply conditional_gap_term_eq_interval M upper om x (i+1) i
    · change D.gapLo (i+1) = _ ∧ D.gapHi (i+1) = _
      rw [hD']
      exact zero_cons_singleton_gap_endpoints ps (Finset.mem_range.mp hi)
    · exact hw i (Finset.mem_range.mp hi)
  · have hD' : D = singletonRangeData ps := by
      simpa only [finiteRangeLevels, if_neg hz] using hD
    have hcount : D.count = ps.length := by rw [hD']; rfl
    rw [hcount]
    apply Finset.sum_congr rfl
    intro i hi
    apply conditional_gap_term_eq_interval M upper om x i i
    · change D.gapLo i = _ ∧ D.gapHi i = _
      rw [hD']
      exact positive_singleton_gap_endpoints ps (Finset.mem_range.mp hi)
    · exact hw i (Finset.mem_range.mp hi)

end Papers.TbsPrteOptimalTransport
