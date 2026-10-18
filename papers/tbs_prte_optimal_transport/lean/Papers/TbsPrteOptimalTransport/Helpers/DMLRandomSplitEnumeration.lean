module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLProcedure
public import Mathlib.Data.Fintype.EquivFin
/-! Measurable enumeration of the random evaluation half.
The enumeration depends only on the split and lists every held-out index
exactly once, giving fixed-size rows for conditional moment arguments. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: equalHalfSplit_measurable_evaluation_enumeration
/-- Under [an equal half split independent of the sample](hyp:hSplit), [there is a coordinatewise measurable enumeration of each evaluation half that almost surely lists each held-out index exactly once and keeps every index below the total sample size, twice the evaluation size](goal). -/
lemma equalHalfSplit_measurable_evaluation_enumeration
    (M : LatentIVModel Ω X Z) (μ : Measure A) (S : ObservedSample M μ)
    (I₁ I₂ : SampleSplit A) (hSplit : EqualHalfSplit M μ S I₁ I₂) :
    ∃ J : ∀ n, A → Fin (n + 1) → ℕ,
      (∀ n i, Measurable (fun a => J n a i)) ∧
      ∀ n, ∀ᵐ a ∂μ, Function.Injective (J n a) ∧
        Finset.univ.image (J n a) = I₂ (2 * (n + 1)) a ∧
        ∀ i, J n a i < 2 * (n + 1) := by
  classical
  let enum (n : ℕ) (s : Finset ℕ) : Fin (n + 1) → ℕ :=
    if hs : s.card = n + 1 then
      fun i => ((s.equivFinOfCardEq hs).symm i).val
    else fun _ => 0
  have hsplit (n : ℕ) := hSplit (2 * (n + 1)) (by omega)
    (show Even (2 * (n + 1)) from ⟨n + 1, by omega⟩)
  refine ⟨fun n a => enum n (I₂ (2 * (n + 1)) a), ?_, ?_⟩
  · intro n i
    have he : Measurable (fun s : Finset ℕ => enum n s i) := by
      first | fun_prop | exact measurable_of_countable _
    exact he.comp (hsplit n).2.2.1
  · intro n
    filter_upwards [(hsplit n).1] with a ha
    have hcard : (I₂ (2 * (n + 1)) a).card = n + 1 := by
      simpa using ha.2.2.2
    simp only [enum, dif_pos hcard]
    let e := (I₂ (2 * (n + 1)) a).equivFinOfCardEq hcard
    refine ⟨Subtype.val_injective.comp e.symm.injective, ?_, ?_⟩
    · ext j
      constructor
      · intro hj
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
        exact (e.symm i).property
      · intro hj
        apply Finset.mem_image.mpr
        exact ⟨e ⟨j, hj⟩, Finset.mem_univ _, by simp [e]⟩
    · intro i
      have hmem : (e.symm i).val ∈ Finset.range (2 * (n + 1)) := by
        rw [← ha.2.1]
        exact Finset.mem_union_right _ (e.symm i).property
      exact Finset.mem_range.mp hmem

end Papers.TbsPrteOptimalTransport
