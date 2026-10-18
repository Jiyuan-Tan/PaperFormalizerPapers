module
public import Papers.TbsPrteOptimalTransport.Helpers.RangeRegularity
public import Mathlib.Probability.Kernel.MeasurableLIntegral
/-! Component extrema obtained from positive kernel mass of rational superlevel sets. -/
public section
set_option linter.style.openClassical false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set
open scoped Classical Topology

-- @node: finite_components_isOpen
/-- [In a topological space with finitely many connected components, the connected
component containing any given point is open](goal). -/
lemma finite_components_isOpen {Z : Type*} [TopologicalSpace Z]
    [Finite (ConnectedComponents Z)] (z0 : Z) : IsOpen (connectedComponent z0) := by
  have hclosed (q : ConnectedComponents Z) :
      IsClosed (ConnectedComponents.mk ⁻¹' {q}) := by
    obtain ⟨z, rfl⟩ := ConnectedComponents.surjective_coe q
    rw [connectedComponents_preimage_singleton]
    exact isClosed_connectedComponent
  have he : (connectedComponent z0)ᶜ =
      ⋃ q : {q : ConnectedComponents Z // q ≠ ConnectedComponents.mk z0},
        ConnectedComponents.mk ⁻¹' {q.val} := by
    ext z
    simp only [mem_compl_iff, mem_iUnion, mem_preimage, mem_singleton_iff]
    constructor
    · intro hz
      exact ⟨⟨ConnectedComponents.mk z,
        fun he => hz (ConnectedComponents.coe_eq_coe'.mp he)⟩, rfl⟩
    · rintro ⟨q, hq⟩ hz
      exact q.property (hq.symm.trans (ConnectedComponents.coe_eq_coe'.mpr hz))
  exact isClosed_compl_iff.mp (he ▸ isClosed_iUnion_of_finite (fun q => hclosed q.val))

-- @node: measurable_full_support_supremum
/-- If [the conditional instrument kernel assigns positive mass to every nonempty open
set at every covariate value](hyp:hκ), [the instrument set is open](hyp:hC) and
[nonempty](hyp:hne), [the function of instrument and covariates is jointly measurable](hyp:hm),
[its values lie between zero and one](hyp:hr), and [its instrument sections are continuous
on that set for almost every covariate value](hyp:hc), then [there exists a measurable
function of covariates equal almost everywhere to the pointwise supremum over that
instrument set](goal). -/
lemma measurable_full_support_supremum
    {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace Z]
    [BorelSpace Z] (μ : Measure X) (κ : Kernel X Z) [IsMarkovKernel κ]
    (hκ : ∀ x (A : Set Z), IsOpen A → A.Nonempty → 0 < κ x A)
    (C : Set Z) (hC : IsOpen C) (hne : C.Nonempty)
    (F : Z → X → ℝ) (hm : Measurable (Function.uncurry F))
    (hr : ∀ z x, F z x ∈ Icc (0 : ℝ) 1)
    (hc : ∀ᵐ x ∂μ, ContinuousOn (fun z => F z x) C) :
    ∃ b : X → ℝ, Measurable b ∧
      ∀ᵐ x ∂μ, b x = sSup ((fun z => F z x) '' C) := by
  let T (q : ℚ) (x : X) := {z | z ∈ C ∧ (q : ℝ) < F z x}
  have hmass (q : ℚ) : Measurable (fun x => κ x (T q x)) := by
    apply Kernel.measurable_kernel_prodMk_left
      (t := {xz : X × Z | xz.2 ∈ C ∧ (q : ℝ) < F xz.2 xz.1})
    exact (measurable_snd hC.measurableSet).inter
      (measurableSet_lt measurable_const (hm.comp measurable_swap))
  let f (q : ℚ) (x : X) : ℝ := if 0 < κ x (T q x) then max 0 (q : ℝ) else 0
  have hf (q : ℚ) : Measurable (f q) := by
    exact Measurable.ite (measurableSet_lt measurable_const (hmass q))
      measurable_const measurable_const
  have hpos {q : ℚ} {x : X} (hq : 0 < κ x (T q x)) :
      ∃ z ∈ C, (q : ℝ) < F z x := by
    have hn : (T q x).Nonempty := by
      by_contra hn
      rw [not_nonempty_iff_eq_empty.mp hn, measure_empty] at hq
      exact lt_irrefl _ hq
    exact hn
  have hbound (x : X) : BddAbove (range (fun q => f q x)) := by
    refine ⟨1, ?_⟩
    rintro y ⟨q, rfl⟩
    dsimp only [f]
    split_ifs with hq
    · obtain ⟨z, hz, hqz⟩ := hpos hq
      exact max_le (by norm_num) (hqz.le.trans (hr z x).2)
    · norm_num
  refine ⟨fun x => ⨆ q, f q x, ?_, ?_⟩
  · fun_prop
  · filter_upwards [hc] with x hx
    have hRne : ((fun z => F z x) '' C).Nonempty := hne.image _
    have hRbdd : BddAbove ((fun z => F z x) '' C) := by
      refine ⟨1, ?_⟩
      rintro y ⟨z, hz, rfl⟩
      exact (hr z x).2
    have hs0 : 0 ≤ sSup ((fun z => F z x) '' C) := by
      obtain ⟨z, hz⟩ := hne
      exact (hr z x).1.trans (le_csSup hRbdd ⟨z, hz, rfl⟩)
    apply le_antisymm
    · apply ciSup_le
      intro q
      dsimp only [f]
      split_ifs with hq
      · obtain ⟨z, hz, hqz⟩ := hpos hq
        exact max_le hs0 (hqz.le.trans (le_csSup hRbdd ⟨z, hz, rfl⟩))
      · exact hs0
    · apply csSup_le hRne
      rintro y ⟨z, hz, rfl⟩
      by_contra hn
      obtain ⟨q, hq, hqz⟩ := exists_rat_btwn (lt_of_not_ge hn)
      have ht : IsOpen (T q x) := hx.isOpen_inter_preimage hC isOpen_Ioi
      have hp : 0 < κ x (T q x) := hκ x _ ht ⟨z, hz, hqz⟩
      have hle := le_ciSup (hbound x) q
      dsimp only [f] at hle
      rw [if_pos hp] at hle
      exact (not_lt_of_ge ((le_max_right _ _).trans hle)) hq

end Papers.TbsPrteOptimalTransport
