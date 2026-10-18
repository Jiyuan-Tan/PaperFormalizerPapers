module
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Topology.Order.Compact
public import Mathlib.MeasureTheory.Measure.Sub
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
/-! # The first-hit measurable section of a continuous interval surjection

This is the section used to lift a cube measure to the Hilbert parameter interval.
-/
@[expose] public section

namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped NNReal

-- @node: hilbertFirstHit
/-- For [a curve from the unit interval](hyp:H) and [a target point](hyp:x), the
[first-hit parameter](goal) is the infimum of the parameters mapped to that point. -/
noncomputable def hilbertFirstHit {Y : Type*}
    (H : Set.Icc (0 : ℝ) 1 → Y) (x : Y) : ℝ :=
  sInf (Subtype.val '' (H ⁻¹' {x}))

-- @node: hilbertFirstHit_isLeast
/-- If [the curve is continuous](hyp:hH) and [reaches every target point](hyp:hsurj),
[the first-hit parameter is the least parameter mapped to the given point](goal). -/
lemma hilbertFirstHit_isLeast {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (H : Set.Icc (0 : ℝ) 1 → Y) (hH : Continuous H)
    (hsurj : Function.Surjective H) (x : Y) :
    IsLeast (Subtype.val '' (H ⁻¹' {x})) (hilbertFirstHit H x) := by
  have hc : IsCompact (H ⁻¹' {x}) :=
    (isClosed_singleton.preimage hH).isCompact
  have hn : (H ⁻¹' {x}).Nonempty := by
    obtain ⟨t, ht⟩ := hsurj x
    exact ⟨t, ht⟩
  exact (hc.image continuous_subtype_val).isLeast_sInf (hn.image Subtype.val)

-- @node: hilbertFirstHit_mem
/-- If [the curve is continuous](hyp:hH) and [reaches every target point](hyp:hsurj),
[the first-hit parameter for any target point lies in the unit interval](goal). -/
lemma hilbertFirstHit_mem {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (H : Set.Icc (0 : ℝ) 1 → Y) (hH : Continuous H)
    (hsurj : Function.Surjective H) (x : Y) :
    hilbertFirstHit H x ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨t, ht, heq⟩ := (hilbertFirstHit_isLeast H hH hsurj x).1
  exact heq ▸ t.property

-- @node: hilbertFirstHit_sublevel
/-- If [the curve is continuous](hyp:hH) and [reaches every target point](hyp:hsurj),
[the points first reached by a given threshold are exactly the image of the
unit-interval parameters at or below that threshold](goal). -/
lemma hilbertFirstHit_sublevel {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (H : Set.Icc (0 : ℝ) 1 → Y) (hH : Continuous H)
    (hsurj : Function.Surjective H) (a : ℝ) :
    {x | hilbertFirstHit H x ≤ a} =
      H '' {t : Set.Icc (0 : ℝ) 1 | (t : ℝ) ≤ a} := by
  ext x
  constructor
  · intro hx
    change hilbertFirstHit H x ≤ a at hx
    obtain ⟨t, ht, heq⟩ := (hilbertFirstHit_isLeast H hH hsurj x).1
    refine ⟨t, ?_, ht⟩
    change (t : ℝ) ≤ a
    simpa only [heq] using hx
  · rintro ⟨t, ht, rfl⟩
    exact ((hilbertFirstHit_isLeast H hH hsurj (H t)).2
      ⟨t, rfl, rfl⟩).trans ht

-- @node: hilbertFirstHit_measurable
/-- If [the curve is continuous](hyp:hH) and [reaches every target point](hyp:hsurj),
[the function assigning each point its first-hit parameter is measurable](goal). -/
@[fun_prop]
lemma hilbertFirstHit_measurable {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (H : Set.Icc (0 : ℝ) 1 → Y) (hH : Continuous H)
    (hsurj : Function.Surjective H) : Measurable (hilbertFirstHit H) := by
  apply measurable_of_Iic
  intro a
  change MeasurableSet {x | hilbertFirstHit H x ≤ a}
  rw [hilbertFirstHit_sublevel H hH hsurj a]
  have hc : IsCompact (H '' {t : Set.Icc (0 : ℝ) 1 | (t : ℝ) ≤ a}) :=
    ((isClosed_le continuous_subtype_val continuous_const).isCompact).image hH
  exact hc.isClosed.measurableSet

-- @node: exists_hilbert_firstHit_section
/-- If [the curve is continuous](hyp:hH) and [reaches every target point](hyp:hsurj),
[there is a measurable choice of a parameter for each point that maps back to
that point and is no larger than any other parameter mapping to it](goal). -/
lemma exists_hilbert_firstHit_section {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (H : Set.Icc (0 : ℝ) 1 → Y) (hH : Continuous H)
    (hsurj : Function.Surjective H) :
    ∃ s : Y → Set.Icc (0 : ℝ) 1, Measurable s ∧
      Function.RightInverse s H ∧
      ∀ x t, H t = x → (s x : ℝ) ≤ (t : ℝ) := by
  let s : Y → Set.Icc (0 : ℝ) 1 := fun x =>
    ⟨hilbertFirstHit H x, hilbertFirstHit_mem H hH hsurj x⟩
  refine ⟨s, ?_, ?_, ?_⟩
  · fun_prop
  · intro x
    obtain ⟨t, ht, heq⟩ := (hilbertFirstHit_isLeast H hH hsurj x).1
    have hs : s x = t := Subtype.ext heq.symm
    exact hs ▸ ht
  · intro x t ht
    exact (hilbertFirstHit_isLeast H hH hsurj x).2 ⟨t, ht, rfl⟩

-- @node: exists_dominating_probability_lift
/-- Suppose [the forward map is measurable](hyp:hH), [the parameter selection is
measurable](hyp:hs), and [mapping each selected parameter forward returns its
original point](hyp:hright). For [a nonnegative scale factor](hyp:c), if [the target
probability law dominates the scaled image of the finite parameter measure](hyp:hdom),
[there is a probability law on parameters that dominates the scaled parameter
measure and maps forward to exactly the target law](goal). -/
lemma exists_dominating_probability_lift {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (H : X → Y) (s : Y → X) (hH : Measurable H) (hs : Measurable s)
    (hright : Function.RightInverse s H)
    (lam : Measure X) [IsFiniteMeasure lam]
    (P : Measure Y) [IsProbabilityMeasure P] (c : ℝ≥0)
    (hdom : c • lam.map H ≤ P) :
    ∃ rho : Measure X, IsProbabilityMeasure rho ∧ c • lam ≤ rho ∧ rho.map H = P := by
  let residual := P - c • lam.map H
  let rho := c • lam + residual.map s
  have hmap : rho.map H = P := by
    have hcomp : H ∘ s = id := funext hright
    calc
      rho.map H = (c • lam).map H + (residual.map s).map H :=
        Measure.map_add _ _ hH
      _ = c • lam.map H + residual := by
        rw [Measure.map_smul, Measure.map_map hH hs, hcomp, Measure.map_id]
      _ = P := by
        rw [add_comm]
        exact Measure.sub_add_cancel_of_le hdom
  refine ⟨rho, ?_, ?_, hmap⟩
  · constructor
    have hm := congrArg (fun m : Measure Y => m Set.univ) hmap
    simpa only [Measure.map_apply hH MeasurableSet.univ,
      Set.preimage_univ, measure_univ] using hm
  · exact Measure.le_add_right le_rfl

-- @node: exists_hilbert_parameter_lift
/-- Suppose [the curve on the unit interval is continuous](hyp:hH) and [reaches
every target point](hyp:hsurj). For [a nonnegative scale factor](hyp:c), if [the
target probability law dominates the scaled image of the finite interval
measure](hyp:hdom), [there is a probability law on the unit interval that dominates
the scaled interval measure and maps along the curve to the target law](goal). -/
lemma exists_hilbert_parameter_lift {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (H : Set.Icc (0 : ℝ) 1 → Y) (hH : Continuous H)
    (hsurj : Function.Surjective H)
    (lam : Measure (Set.Icc (0 : ℝ) 1)) [IsFiniteMeasure lam]
    (P : Measure Y) [IsProbabilityMeasure P] (c : ℝ≥0)
    (hdom : c • lam.map H ≤ P) :
    ∃ rho : Measure (Set.Icc (0 : ℝ) 1),
      IsProbabilityMeasure rho ∧ c • lam ≤ rho ∧ rho.map H = P := by
  obtain ⟨s, hs, hright, hleast⟩ := exists_hilbert_firstHit_section H hH hsurj
  have hmeas : Measurable H := by fun_prop
  exact exists_dominating_probability_lift H s hmeas hs hright lam P c hdom

end Papers.TbsNeuralCausalPi
