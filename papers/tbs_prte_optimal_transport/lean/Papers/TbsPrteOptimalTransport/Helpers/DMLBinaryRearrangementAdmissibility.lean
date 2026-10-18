module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLProcedureCore
/-! Measurability and admissibility of the finite binary rearrangement. -/
public section
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedTactic false
set_option linter.style.openClassical false
set_option linter.flexible false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open scoped Classical Topology

-- @node: measurable_orderedInsert_getD
/-- If [a covariate-dependent list has a fixed length](hyp:hlen), [each of its
coordinates is measurable when missing entries are assigned zero](hyp:hg), and
[the value to insert is measurable](hyp:hf), [every coordinate after ordered
insertion is measurable with the same zero fallback](goal). -/
@[fun_prop] lemma measurable_orderedInsert_getD {B : Type*} [MeasurableSpace B]
    (N : ℕ) (g : B → List ℝ) (f : B → ℝ)
    (hlen : ∀ x, (g x).length = N)
    (hg : ∀ i, Measurable (fun x => (g x).getD i 0)) (hf : Measurable f)
    (i : ℕ) : Measurable (fun x => ((g x).orderedInsert (· ≤ ·) (f x)).getD i 0) := by
  induction N generalizing g i with
  | zero =>
    have he : ∀ x, g x = [] := by
      intro x
      cases h : g x with
      | nil => rfl
      | cons a l => have hh := hlen x; simp [h] at hh
    simp only [he, List.orderedInsert_nil]
    cases i <;> simp <;> fun_prop
  | succ N ih =>
    let b : B → ℝ := fun x => (g x).getD 0 0
    let t : B → List ℝ := fun x => (g x).tail
    have he (x : B) : g x = b x :: t x := by
      cases h : g x with
      | nil => have hh := hlen x; simp [h] at hh
      | cons a l => simp [b, t, h]
    have htlen (x : B) : (t x).length = N := by
      have hh := hlen x
      rw [he x] at hh
      simpa using hh
    have ht (j : ℕ) : Measurable (fun x => (t x).getD j 0) := by
      convert hg (j + 1) using 1
      funext x
      rw [he x]
      simp
    have hb : Measurable b := hg 0
    have hs : MeasurableSet {x | f x ≤ b x} := measurableSet_le hf hb
    cases i with
    | zero =>
      have hid : (fun x => ((g x).orderedInsert (· ≤ ·) (f x)).getD 0 0) =
          (fun x => if f x ≤ b x then f x else b x) := by
        funext x
        rw [he x, List.orderedInsert_cons]
        split <;> simp
      rw [hid]
      exact Measurable.ite hs hf hb
    | succ i =>
      have hid : (fun x => ((g x).orderedInsert (· ≤ ·) (f x)).getD (i + 1) 0) =
          (fun x => if f x ≤ b x then (g x).getD i 0 else
            ((t x).orderedInsert (· ≤ ·) (f x)).getD i 0) := by
        funext x
        rw [he x, List.orderedInsert_cons]
        split <;> simp
      rw [hid]
      exact Measurable.ite hs (hg i) (ih t htlen ht i)

-- @node: measurable_mergeSort_getD
/-- If [every function in a finite list is measurable](hyp:hl), [evaluating
the functions, sorting their values in increasing order, and selecting any
coordinate with a zero fallback gives a measurable function](goal). -/
@[fun_prop] lemma measurable_mergeSort_getD {B : Type*} [MeasurableSpace B]
    (l : List (B → ℝ)) (hl : ∀ f ∈ l, Measurable f) (i : ℕ) :
    Measurable (fun x => ((l.map (fun f => f x)).mergeSort (· ≤ ·)).getD i 0) := by
  simp only [List.mergeSort_eq_insertionSort]
  induction l generalizing i with
  | nil => simp
  | cons f l ih =>
    simp only [List.map_cons, List.insertionSort_cons]
    apply measurable_orderedInsert_getD l.length
    · intro x
      simp
    · intro j
      exact ih (fun h hh => hl h (by simp [hh])) j
    · exact hl f (by simp)

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: rearrangeP1_measurable
/-- If [the binary nuisance collection is admissible](hyp:he), [each
positive-level success regression obtained by clipping and sorting is a
measurable function of covariates](goal). -/
@[fun_prop] lemma rearrangeP1_measurable (L : LevelData Z X) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (k : PositiveIndex L.K) :
    Measurable ((rearrangeP1 L e).P1 k) := by
  first | fun_prop | skip
  have hm (i : ℕ) : Measurable (fun x => min 1 (max 0 (positiveValue e.P1 (i + 1) x))) := by
    first | fun_prop | skip
    unfold positiveValue
    split_ifs <;> first | fun_prop | exact measurable_const.min (measurable_const.max ((he.2.2.2.1 _).2.1))
  have hh := measurable_mergeSort_getD
    ((List.range L.K).map (fun i x => min 1 (max 0 (positiveValue e.P1 (i + 1) x))))
    (by
      intro f hf
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hf
      exact hm i) (k.val - 1)
  simpa only [List.map_map, Function.comp_def, rearrangeP1] using hh

-- @node: rearrangeP1_range
/-- [Every positive-level success probability obtained by clipping and sorting
lies between zero and one at every covariate value](goal). -/
lemma rearrangeP1_range (L : LevelData Z X) (e : NuisanceBin L)
    (k : PositiveIndex L.K) (x : X) : (rearrangeP1 L e).P1 k x ∈ Icc (0 : ℝ) 1 := by
  let l := (List.range L.K).map (fun i => min 1 (max 0 (positiveValue e.P1 (i + 1) x)))
  have hlen : k.val - 1 < (l.mergeSort (· ≤ ·)).length := by
    simp only [List.length_mergeSort, List.length_map, List.length_range, l]
    omega
  have hmem : (l.mergeSort (· ≤ ·)).getD (k.val - 1) 0 ∈ l := by
    apply (List.mergeSort_perm l (· ≤ ·)).mem_iff.mp
    simpa only [List.getD_eq_getElem _ _ hlen] using
      List.getElem_mem hlen
  obtain ⟨i, hi, hv⟩ := List.mem_map.mp hmem
  change (l.mergeSort (· ≤ ·)).getD (k.val - 1) 0 ∈ Icc (0 : ℝ) 1
  rw [← hv]
  exact ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

-- @node: rearrangeP1_admissible
/-- If [a binary nuisance collection is admissible](hyp:he), [the collection
obtained by clipping and sorting its positive-level success regressions is
also admissible](goal). -/
lemma rearrangeP1_admissible (L : LevelData Z X) (e : NuisanceBin L)
    (he : BinAdmissible M L e) : BinAdmissible M L (rearrangeP1 L e) := by
  rcases he with ⟨hp, hmp, hl, hml, hr, hmr, hs, hms, hsimplex, hf, hmf, ht, hmt⟩
  refine ⟨hp, hmp, ?_, ?_, hr, hmr, hs, hms, hsimplex, hf, hmf, ht, hmt⟩
  · intro k
    filter_upwards [hl k] with x hx
    exact ⟨hx.1, rearrangeP1_range L e k x, hx.2.2⟩
  · intro k
    exact ⟨(hml k).1, rearrangeP1_measurable M L e
      ⟨hp, hmp, hl, hml, hr, hmr, hs, hms, hsimplex, hf, hmf, ht, hmt⟩ k,
      (hml k).2.2⟩

end Papers.TbsPrteOptimalTransport
