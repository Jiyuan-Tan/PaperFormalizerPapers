module

public import Mathlib.Probability.UniformOn
public import Papers.HawkesD75660b.Helpers.ParkingPrefixes
public import Papers.HawkesD75660b.Helpers.CountFibers
public import Papers.HawkesD75660b.Helpers.ParkingCriterion
public import Papers.HawkesD75660b.Helpers.CircularParking

/-! Parking enumeration, multinomial fibers, and normalization. -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Papers.HawkesD75660b

/-- For [a vector of labels ranging from zero to one less than the alphabet size](hyp:π),
[the bounded preference vector adds one to each label to obtain positive preferences](goal). -/
def boundedParkingVector {m n : ℕ} (π : Fin m → Fin n) : PreferenceVector m :=
  fun a => ⟨(π a).val + 1, Nat.succ_pos _⟩

/-- [The number of positive preferences at most one plus a given label, added to the
number of labels strictly greater than that label, equals the total number of cars](goal). -/
lemma boundedParking_prefix_complement {r q : ℕ} (w : Fin r → Fin q) (t : Fin q) :
    parkingPrefix (boundedParkingVector w) (t.val + 1) +
      (List.ofFn (fun i => (w i).castSucc)).countP
        (fun p => decide (t.castSucc < p)) = r := by
  classical
  rw [parkingPrefix_eq_sum, parking_countP_ofFn, ← Finset.sum_add_distrib]
  calc
    _ = ∑ _i : Fin r, 1 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [boundedParkingVector, Fin.lt_def, Fin.val_castSucc, decide_eq_true_eq]
      change (if (w i).val + 1 ≤ t.val + 1 then 1 else 0) +
        (if t.val < (w i).val then 1 else 0) = (1 : ℕ)
      split_ifs <;> omega
    _ = r := by simp

/-- If [the number of cars is at most the number of linear spots](hyp:hrq),
[the last spot in the circle with one additional spot remains empty exactly when the
corresponding positive preferences satisfy the generalized sorted parking criterion](goal). -/
lemma circularEmpty_last_iff_order {r q : ℕ} (hrq : r ≤ q) (w : Fin r → Fin q) :
    Fin.last q ∈ circularEmpty (fun i => (w i).castSucc) ↔
      generalizedParkingOrder q (boundedParkingVector w) := by
  rw [circularEmpty_last_iff_suffix hrq, generalizedParkingOrder_iff_prefix hrq]
  constructor
  · intro h u hu
    by_cases hz : u = 0
    · omega
    let t : Fin q := ⟨u - 1, by omega⟩
    have hc := boundedParking_prefix_complement w t
    have hb := h t
    have ht : t.val + 1 = u := by dsimp [t]; omega
    rw [ht] at hc
    have htval : t.val = u - 1 := rfl
    omega
  · intro h t
    have hc := boundedParking_prefix_complement w t
    have hb := h (t.val + 1) (by have := t.isLt; omega)
    have ht := t.isLt
    omega

open Classical in
/-- For [a number of cars](hyp:m) and [an alphabet size](hyp:n), [the generalized parking
set consists of all vectors of labels from zero to one less than the alphabet size
whose corresponding positive preferences are generalized parking functions](goal). -/
def generalizedParkingSet (m n : ℕ) : Finset (Fin m → Fin n) :=
  Finset.univ.filter (fun π => GeneralizedParkingFunction n (boundedParkingVector π))

-- @node: generalizedParking_enumeration
/-- If [the car count and alphabet size are positive and the car count does not exceed
the alphabet size](hyp:h), [the number of generalized parking vectors is the alphabet size
minus the car count plus one, multiplied by the alphabet size plus one raised to the car count minus one](goal). -/
lemma generalizedParking_enumeration {m n : ℕ} (h : generalizedParkingParameters m n) :
    (generalizedParkingSet m n).card = (n - m + 1) * (n + 1) ^ (m - 1) := by
  classical
  have hcard : (generalizedParkingSet m n).card = Fintype.card (LastAvoidingWords m n) := by
    rw [Fintype.card_subtype]
    congr 1
    ext w
    simp only [generalizedParkingSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hw => (circularEmpty_last_iff_order h.2.2 w).mpr hw.order,
      fun hw => ⟨h, (circularEmpty_last_iff_order h.2.2 w).mp hw⟩⟩
  rw [hcard, lastAvoidingWords_card h.1]
  congr 1
  have := h.2.2
  omega

open Classical in
/-- If [the car count is at most the alphabet size](hyp:hrq), [the number of bounded
preference vectors satisfying the generalized sorted criterion is one for zero cars;
otherwise it is the alphabet size minus the car count plus one times the alphabet size
plus one raised to the car count minus one](goal). -/
lemma parkingOrderWords_card {r q : ℕ} (hrq : r ≤ q) :
    Fintype.card {w : Fin r → Fin q // generalizedParkingOrder q (boundedParkingVector w)} =
      if r = 0 then 1 else (q - r + 1) * (q + 1) ^ (r - 1) := by
  classical
  by_cases hr : r = 0
  · subst r
    simp [Fintype.card_subtype, generalizedParkingOrder]
  · rw [if_neg hr]
    have hp : generalizedParkingParameters r q := ⟨by omega, by omega, hrq⟩
    have he : Fintype.card {w : Fin r → Fin q //
        generalizedParkingOrder q (boundedParkingVector w)} = (generalizedParkingSet r q).card := by
      rw [Fintype.card_subtype]
      congr 1
      ext w
      simp only [generalizedParkingSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => ⟨hp, h⟩, fun h => h.order⟩
    rw [he, generalizedParking_enumeration hp]

/-- [Appending a fixed initial preference block to a bounded remaining block, after
adding a fixed shift to its positive preferences, is injective in the remaining block](goal). -/
lemma parkingAppend_bounded_injective {s r q : ℕ} (m : ℕ) (low : PreferenceVector s) :
    Function.Injective (fun tail : Fin r → Fin q =>
      parkingAppend m low (boundedParkingVector tail)) := by
  intro a b h
  funext i
  have he := congrArg (fun w : PreferenceVector (s + r) => (w (Fin.natAdd s i) : ℕ)) h
  have ha : (parkingAppend m low (boundedParkingVector a) (Fin.natAdd s i) : ℕ) =
      m + ((a i).val + 1) := congrArg (fun x : ℕ+ => (x : ℕ)) (Fin.append_right _ _ i)
  have hb : (parkingAppend m low (boundedParkingVector b) (Fin.natAdd s i) : ℕ) =
      m + ((b i).val + 1) := congrArg (fun x : ℕ+ => (x : ℕ)) (Fin.append_right _ _ i)
  rw [ha, hb] at he
  apply Fin.ext
  omega

open Classical in
/-- For [a lower threshold for the remaining preferences](hyp:m) and [a fixed initial
preference block](hyp:low), [the completion set consists of vectors satisfying the sorted
parking criterion with as many spots as total cars, with the initial block fixed and
each remaining preference strictly above the threshold and at most the total car count](goal). -/
def parkingCompletionSet {s r : ℕ} (m : ℕ) (low : PreferenceVector s) :
    Finset (PreferenceVector (s + r)) :=
  (Finset.univ.filter (fun tail : Fin r → Fin (s + r - m) =>
    generalizedParkingOrder (s + r) (parkingAppend m low (boundedParkingVector tail)))).image
      (fun tail => parkingAppend m low (boundedParkingVector tail))

/-- [A preference vector belongs to the completion set exactly when it satisfies the
sorted parking criterion with as many spots as cars, agrees with the fixed initial
block, and has every remaining preference strictly above the shift and at most the total car count](goal). -/
lemma mem_parkingCompletionSet {s r m : ℕ} (low : PreferenceVector s)
    (π : PreferenceVector (s + r)) :
    π ∈ parkingCompletionSet (r := r) m low ↔
      generalizedParkingOrder (s + r) π ∧
        (∀ i, π (Fin.castAdd r i) = low i) ∧
        (∀ j, m < (π (Fin.natAdd s j) : ℕ) ∧ (π (Fin.natAdd s j) : ℕ) ≤ s + r) := by
  classical
  constructor
  · intro h
    obtain ⟨tail, ht, rfl⟩ := Finset.mem_image.mp h
    refine ⟨(Finset.mem_filter.mp ht).2, ?_, ?_⟩
    · intro i
      exact Fin.append_left _ _ i
    · intro j
      have he : (parkingAppend m low (boundedParkingVector tail) (Fin.natAdd s j) : ℕ) =
          m + ((tail j).val + 1) :=
        congrArg (fun x : ℕ+ => (x : ℕ)) (Fin.append_right _ _ j)
      rw [he]
      have := (tail j).isLt
      omega
  · rintro ⟨ho, hl, hr⟩
    let tail : Fin r → Fin (s + r - m) := fun j =>
      ⟨(π (Fin.natAdd s j) : ℕ) - m - 1, by have := hr j; omega⟩
    have he : parkingAppend m low (boundedParkingVector tail) = π := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · exact (Fin.append_left _ _ j).trans (hl j).symm
      · apply Subtype.ext
        have hv : (parkingAppend m low (boundedParkingVector tail) (Fin.natAdd s j) : ℕ) =
            m + ((tail j).val + 1) :=
          congrArg (fun x : ℕ+ => (x : ℕ)) (Fin.append_right _ _ j)
        change (parkingAppend m low (boundedParkingVector tail) (Fin.natAdd s j) : ℕ) = _
        rw [hv]
        change m + ((π (Fin.natAdd s j) : ℕ) - m - 1 + 1) =
          (π (Fin.natAdd s j) : ℕ)
        have := hr j
        omega
    apply Finset.mem_image.mpr
    refine ⟨tail, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, he⟩
    rw [he]
    exact ho

/-- Suppose [the shift is at most the initial block's size](hyp:hms), [every initial
preference is at most the shift](hyp:hlow), and [each threshold up to the shift has at
least that many initial preferences at most it](hyp:hprefix). Then [the completion count
is one when no cars remain; otherwise it is the initial block's size minus the shift
plus one times the total car count minus the shift plus one raised to the remaining car count minus one](goal). -/
lemma parkingCompletionSet_card {s r m : ℕ} (hms : m ≤ s)
    (low : PreferenceVector s) (hlow : ∀ i, (low i : ℕ) ≤ m)
    (hprefix : ∀ t, t ≤ m → t ≤ parkingPrefix low t) :
    (parkingCompletionSet (r := r) m low).card =
      if r = 0 then 1 else (s - m + 1) * (s + r - m + 1) ^ (r - 1) := by
  classical
  rw [parkingCompletionSet, Finset.card_image_of_injective _ (parkingAppend_bounded_injective m low)]
  have he : (Finset.univ.filter (fun tail : Fin r → Fin (s + r - m) =>
      generalizedParkingOrder (s + r) (parkingAppend m low (boundedParkingVector tail)))).card =
      Fintype.card {tail : Fin r → Fin (s + r - m) //
        generalizedParkingOrder (s + r - m) (boundedParkingVector tail)} := by
    rw [Fintype.card_subtype]
    congr 1
    ext tail
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact parkingAppend_order_iff hms low _ hlow hprefix
  rw [he, parkingOrderWords_card (by omega : r ≤ s + r - m)]
  have hh : s + r - m - r = s - m := by omega
  rw [hh]

open Classical in
/-- For [a car count](hyp:n), [the classic parking set consists of all vectors of labels
from zero to one less than that count whose positive preferences satisfy the classic
sorted parking criterion, including the unique empty vector at count zero](goal). -/
def classicParkingSet (n : ℕ) : Finset (Fin n → Fin n) :=
  Finset.univ.filter (fun π => CombinatorialParkingFunction n (boundedParkingVector π))

open Classical in
/-- If [the car count is positive](hyp:hn), [the classic parking set equals the set of
bounded label vectors whose positive preferences are classic parking functions in the manuscript's sense](goal). -/
lemma classicParkingSet_eq_paper {n : ℕ} (hn : 0 < n) :
    classicParkingSet n = Finset.univ.filter (fun π : Fin n → Fin n =>
      ClassicParkingFunction n (boundedParkingVector π)) := by
  classical
  ext π
  simp only [classicParkingSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact combinatorialParkingFunction_iff_classic _ ⟨hn, hn, le_rfl⟩

-- @node: classicParking_enumeration
/-- [The number of classic parking vectors for a given car count is that count plus
one raised to the count minus one, with one empty vector when the count is zero](goal). -/
lemma classicParking_enumeration (n : ℕ) :
    (classicParkingSet n).card = (n + 1) ^ (n - 1) := by
  classical
  by_cases hn : n = 0
  · subst n
    have hempty : ∀ π : Fin 0 → Fin 0, CombinatorialParkingFunction 0 (boundedParkingVector π) :=
      fun π => ⟨fun a => Fin.elim0 a, rfl⟩
    simp [classicParkingSet, hempty]
  · have hparams : generalizedParkingParameters n n := ⟨by omega, by omega, le_rfl⟩
    have hsets : classicParkingSet n = generalizedParkingSet n n := by
      rw [classicParkingSet_eq_paper hparams.1]
      ext π
      simp only [generalizedParkingSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => ⟨h.parameters, h.order⟩, fun h => ⟨hparams, h.order, rfl⟩⟩
    rw [hsets, generalizedParking_enumeration hparams]
    simp

open Classical in
-- @node: parking_count_fiber
/-- If [the preference counts sum to the car count and every initial cumulative count
is at least the number of preference values included](hyp:hk), [the number of classic
parking vectors with those counts, multiplied by the product of the factorials of the
counts, equals the factorial of the car count](goal). -/
lemma parking_count_fiber {n : ℕ} {k : CountVector n} (hk : PreferenceCounts k) :
    ((classicParkingSet n).filter
      (fun π => preferenceCountsOfParking n (boundedParkingVector π) = k)).card *
      (∏ a, Nat.factorial (k a)) = Nat.factorial n := by
  classical
  have hcounts (π : Fin n → Fin n) (a : Fin n) :
      preferenceCountsOfParking n (boundedParkingVector π) a =
        Fintype.card {i // π i = a} := by
    simp only [preferenceCountsOfParking, boundedParkingVector, Fintype.card_subtype]
    congr 1
    ext i
    simp [Fin.ext_iff]
  have heq (π : Fin n → Fin n) :
      preferenceCountsOfParking n (boundedParkingVector π) = k ↔
        ∀ a, Fintype.card {i // π i = a} = k a := by
    rw [funext_iff]
    simp only [hcounts]
  have hcard :
      ((classicParkingSet n).filter
        (fun π => preferenceCountsOfParking n (boundedParkingVector π) = k)).card =
      Fintype.card {π : Fin n → Fin n // ∀ a, Fintype.card {i // π i = a} = k a} := by
    rw [Fintype.card_subtype]
    congr 1
    ext π
    simp only [classicParkingSet, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => (heq π).mp h.2
    · intro h
      have hc := (heq π).mpr h
      exact ⟨classicParking_of_counts_supported (hc.symm ▸ hk), hc⟩
  rw [hcard]
  have h := countFibers_prescribed_card (α := Fin n) k
    (by simpa only [Fintype.card_fin, preferenceTotal] using hk.total)
  simp only [Fintype.card_fin] at h
  convert h using 1
  congr 1
  congr!

-- @node: preferenceCountMass_multinomial
/-- If [the counts sum to the car count and every initial cumulative count is at least
the number of preference values included](hyp:hk), [their preference count mass equals
their multinomial coefficient divided by the car count plus one raised to the car count minus one](goal). -/
lemma preferenceCountMass_multinomial {n : ℕ} {k : CountVector n}
    (hk : PreferenceCounts k) :
    preferenceCountMass n k =
      (Nat.multinomial Finset.univ k : ℝ) / (n + 1 : ℝ) ^ (n - 1) := by
  classical
  have hprod : (∏ a, (Nat.factorial (k a) : ℝ)) ≠ 0 := by positivity
  have hpow : (n + 1 : ℝ) ^ (n - 1) ≠ 0 := by positivity
  have hmulti : (Nat.multinomial Finset.univ k : ℝ) *
      (∏ a, (Nat.factorial (k a) : ℝ)) = Nat.factorial n := by
    have htotal : ∑ a, k a = n := hk.total
    exact_mod_cast (by simpa [htotal, mul_comm] using Nat.multinomial_spec Finset.univ k)
  rw [preferenceCountMass, if_pos hk]
  field_simp
  nlinarith [hmulti]

-- @node: preferenceCountMeasure_singleton
/-- [The real-valued measure of a singleton count vector under the preference count
measure equals the preference count mass assigned to that vector](goal). -/
lemma preferenceCountMeasure_singleton (n : ℕ) (k : CountVector n) :
    (preferenceCountMeasure n).real {k} = preferenceCountMass n k := by
  classical
  have hnonneg : 0 ≤ preferenceCountMass n k := by
    unfold preferenceCountMass
    split_ifs <;> positivity
  by_cases hk : PreferenceCounts k
  · let b : Fin n → Fin (n + 1) := fun a => ⟨k a, Nat.lt_succ_of_le
        (preferenceCounts_coordinate_bound hk a)⟩
    have heq : ∀ c : Fin n → Fin (n + 1), (fun a => (c a).val) = k ↔ c = b := by
      intro c
      constructor
      · intro h
        funext a
        exact Fin.ext (congrFun h a)
      · intro h
        subst c
        rfl
    simp only [Measure.real, preferenceCountMeasure, Measure.finsetSum_apply,
      Measure.smul_apply, smul_eq_mul]
    simp_rw [Measure.dirac_apply, Set.indicator_apply, Set.mem_singleton_iff, heq]
    simp [b, ENNReal.toReal_ofReal hnonneg]
  · have heq : ∀ c : Fin n → Fin (n + 1),
        ENNReal.ofReal (preferenceCountMass n (fun a => (c a).val)) *
          (Measure.dirac (fun a => (c a).val) : Measure (CountVector n)) {k} = 0 := by
      intro c
      by_cases hc : (fun a => (c a).val) = k
      · simp [hc, preferenceCountMass, hk]
      · simp [hc]
    simp only [Measure.real, preferenceCountMeasure, Measure.finsetSum_apply,
      Measure.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_zero (fun c _ => heq c)]
    simp [preferenceCountMass, hk]

-- @node: preferenceCountMeasure_supported
/-- [Almost every vector under the preference count measure has counts summing to the
car count and initial cumulative counts at least as large as the number of preference values included](goal). -/
lemma preferenceCountMeasure_supported (n : ℕ) :
    ∀ᵐ k ∂preferenceCountMeasure n, PreferenceCounts k := by
  classical
  unfold preferenceCountMeasure
  apply ae_finsetSum_measure_iff.mpr
  intro k hk
  by_cases h : PreferenceCounts (fun a => (k a).val)
  · apply Measure.ae_smul_measure
    simpa only [ae_dirac_eq, Filter.eventually_pure] using h
  · simp [preferenceCountMass, h]

-- @node: uniformParking_counts_law
/-- [The preference counts of a uniformly chosen classic parking vector have the
preference count measure as their probability law](goal). -/
lemma uniformParking_counts_law (n : ℕ) :
    HasLaw (fun π : Fin n → Fin n => preferenceCountsOfParking n (boundedParkingVector π))
      (preferenceCountMeasure n) (uniformOn (classicParkingSet n : Set (Fin n → Fin n))) := by
  classical
  constructor
  · exact (measurable_of_countable _).aemeasurable
  · apply Measure.ext_of_singleton
    intro k
    rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton k)]
    have hfinite : (preferenceCountMeasure n) {k} ≠ ∞ := by
      simp only [preferenceCountMeasure, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
      apply ENNReal.sum_ne_top.mpr
      intro c hc
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
    rw [← ofReal_measureReal hfinite,
      preferenceCountMeasure_singleton]
    let f := fun π : Fin n → Fin n => preferenceCountsOfParking n (boundedParkingVector π)
    have hset : f ⁻¹' {k} = (Finset.univ.filter (fun π => f π = k) : Set (Fin n → Fin n)) := by
      ext π
      simp
    change uniformOn (classicParkingSet n : Set (Fin n → Fin n)) (f ⁻¹' {k}) = _
    rw [hset, uniformOn_apply_finset]
    have hinter : classicParkingSet n ∩ Finset.univ.filter (fun π => f π = k) =
        (classicParkingSet n).filter (fun π => f π = k) := by
      ext π
      simp
    rw [hinter, classicParking_enumeration]
    by_cases hk : PreferenceCounts k
    · have hf := parking_count_fiber hk
      have hprod : (∏ a, (Nat.factorial (k a) : ℝ)) ≠ 0 := by positivity
      have hpow : (n + 1 : ℝ) ^ (n - 1) ≠ 0 := by positivity
      have hreal : (((classicParkingSet n).filter (fun π => f π = k)).card : ℝ) /
          (n + 1 : ℝ) ^ (n - 1) = preferenceCountMass n k := by
        rw [preferenceCountMass, if_pos hk]
        have hf' : (((classicParkingSet n).filter (fun π => f π = k)).card : ℝ) *
            (∏ a, (Nat.factorial (k a) : ℝ)) = Nat.factorial n := by
          exact_mod_cast hf
        field_simp
        nlinarith [hf']
      rw [← hreal, ENNReal.ofReal_div_of_pos (by positivity)]
      rw [ENNReal.ofReal_pow (by positivity)]
      simp [ENNReal.ofReal_add (Nat.cast_nonneg n) zero_le_one]
    · have hempty : (classicParkingSet n).filter (fun π => f π = k) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro π hπ
        obtain ⟨hπ, heq⟩ := Finset.mem_filter.mp hπ
        have hs := countsOfClassicParking_supported (Finset.mem_filter.mp hπ).2
        exact hk (heq ▸ hs)
      simp [hempty, preferenceCountMass, hk]

-- @node: preferenceCountMeasure_probability
/-- [The preference count measure has total mass one and is therefore a probability measure](goal). -/
lemma preferenceCountMeasure_probability (n : ℕ) :
    IsProbabilityMeasure (preferenceCountMeasure n) := by
  have hpos : 0 < (classicParkingSet n).card := by
    rw [classicParking_enumeration]
    positivity
  haveI := isProbabilityMeasure_uniformOn (classicParkingSet n).finite_toSet
    (Finset.coe_nonempty.mpr (Finset.card_pos.mp hpos))
  exact (uniformParking_counts_law n).isProbabilityMeasure_iff.mp inferInstance

end Papers.HawkesD75660b
