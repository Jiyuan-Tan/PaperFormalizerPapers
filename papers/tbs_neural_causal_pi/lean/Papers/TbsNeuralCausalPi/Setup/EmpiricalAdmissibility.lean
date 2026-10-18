module
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Causalean.Stat.Concentration.VC.Basic
/-! # Structural measurability of empirical-process classes

The standing measurability caveat in Anthony--Bartlett (1999), printed p. 15,
is implemented by a standard Borel parameter space and a jointly measurable
evaluation map. This condition concerns the class, independently of any
probability law, sample size, tolerance, or concentration estimate.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory

/-- A [function class](hyp:F) has a [Borel parameterization](goal) if there exist a parameter space and a family of functions such that [the parameter space is standard Borel, and may be empty](step:1), [evaluation is jointly measurable in parameter and input](step:2), and [the class is exactly the family’s range](step:3). -/
def BorelParametrizedClass {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (F : Set (X → Y)) : Prop :=
  ∃ (T : Type) (mT : MeasurableSpace T), letI := mT
    StandardBorelSpace T ∧ ∃ g : T → X → Y,
      Measurable (fun p : T × X => g p.1 p.2) ∧ F = Set.range g

/-- If [evaluation of a family indexed by a standard Borel parameter space is jointly measurable in parameter and input](hyp:hg), then [the family’s range has a Borel parameterization](goal). -/
lemma borelParametrizedClass_range {X Y T : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace T] [StandardBorelSpace T]
    (g : T → X → Y) (hg : Measurable (fun p : T × X => g p.1 p.2)) :
    BorelParametrizedClass (Set.range g) :=
  ⟨T, inferInstance, inferInstance, g, hg, rfl⟩

/-- If [a function class has a Borel parameterization](hyp:hF), then [every function in the class is measurable](goal). -/
lemma BorelParametrizedClass.measurable {X Y : Type}
    [MeasurableSpace X] [MeasurableSpace Y] {F : Set (X → Y)}
    (hF : BorelParametrizedClass F) : ∀ f ∈ F, Measurable f := by
  obtain ⟨T, mT, hT, g, hg, rfl⟩ := hF
  letI := mT
  rintro f ⟨t, rfl⟩
  exact hg.comp (measurable_const.prodMk measurable_id)

/-- If [a function class has a Borel parameterization](hyp:hF) and [a transformation of its outputs](hyp:h) [is measurable](hyp:hh), then [the class obtained by applying that transformation to every function also has a Borel parameterization](goal). -/
lemma BorelParametrizedClass.postcomp {X Y Z : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    {F : Set (X → Y)} (hF : BorelParametrizedClass F)
    (h : Y → Z) (hh : Measurable h) :
    BorelParametrizedClass ((fun f => h ∘ f) '' F) := by
  obtain ⟨T, mT, hT, g, hg, rfl⟩ := hF
  letI := mT
  letI := hT
  refine ⟨T, mT, hT, (fun t => h ∘ g t), hh.comp hg, ?_⟩
  ext f
  simp

/-- For [an indexed family of Boolean-valued functions](hyp:B) and [a complexity bound](hyp:v), a [Boolean class envelope](goal) exists when there is a class of Boolean-valued functions that [has a Borel parameterization](step:1), [contains every member of the indexed family](step:2), and [has pseudo-dimension at most the complexity bound when true and false are represented by one and zero](step:3).

The envelope supplies measurability and complexity control even for restrictions indexed by non-Borel sets. -/
def BooleanClassEnvelope {X : Type} [MeasurableSpace X] {I : Type*}
    (B : I → X → Bool) (v : ℕ) : Prop :=
  ∃ H : Set (X → Bool), BorelParametrizedClass H ∧ Set.range B ⊆ H ∧
    Causalean.Stat.Concentration.HasPseudoDimAtMost
      (fun b : H => fun x => if b.val x then (1 : ℝ) else 0) v

end Papers.TbsNeuralCausalPi
