module
public import Papers.OaiMetricMarkovCotype.Basic
public import Toolkit.Foundations.Probability.Processes.ConditionalExpectation
public import Toolkit.Foundations.Probability.Processes.DeterministicIteration

/-! # Harmonic finite-state observables on the canonical path space -/

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Papers.OaiMetricMarkovCotype

-- @node: finite_kernel_harmonic_martingale
/-- If [the expected next value of a finite-dimensional observable equals its current value at
every state](hyp:hg), then [the observable along the finite-state Markov chain is a martingale
with respect to the history of the chain](goal). -/
lemma finite_kernel_harmonic_martingale
    {α 𝓑 : Type*} [Fintype α] [MeasurableSpace α] [DiscreteMeasurableSpace α]
    [Fintype 𝓑] (μ₀ : Measure α) [IsProbabilityMeasure μ₀]
    (K : Kernel α α) [IsMarkovKernel K] (g : α → 𝓑 → ℝ)
    (hg : ∀ a, ∫ b, g b ∂K a = g a) :
    Martingale (fun m ω => g (ω m))
      (Toolkit.Foundations.Probability.Processes.naturalFiltration (fun _ => α))
      (Toolkit.Foundations.Probability.Processes.pathLaw μ₀
        (Toolkit.Foundations.Probability.Processes.homogeneousTransition K)) := by
  classical
  let κ := Toolkit.Foundations.Probability.Processes.homogeneousTransition K
  let μ := Toolkit.Foundations.Probability.Processes.pathLaw μ₀ κ
  let 𝓕 := Toolkit.Foundations.Probability.Processes.naturalFiltration (fun _ => α)
  have hgm : Measurable g := by fun_prop
  have hbound (a : α) : ‖g a‖ ≤ ∑ b, ‖g b‖ :=
    Finset.single_le_sum (fun b _ => norm_nonneg (g b)) (Finset.mem_univ a)
  have hadp : StronglyAdapted 𝓕 (fun m ω => g (ω m)) := by
    intro m
    exact (hgm.comp
      (Toolkit.Foundations.Probability.Processes.adapted_coordinate (fun _ => α) m)).stronglyMeasurable
  have hint (m : ℕ) : Integrable (fun ω => g (ω m)) μ := by
    apply Integrable.of_bound ((hadp m).mono (𝓕.le m)).aestronglyMeasurable (∑ b, ‖g b‖)
    exact ae_of_all μ fun ω => hbound (ω m)
  apply martingale_nat hadp hint
  intro m
  have hF : Integrable (fun p :
      Toolkit.Foundations.Probability.Processes.History (fun _ => α) m × α => g p.2)
      ((μ.map (Toolkit.Foundations.Probability.Processes.history (fun _ => α) m)).compProd (κ m)) := by
    apply Integrable.of_bound (by fun_prop) (∑ b, ‖g b‖)
    exact ae_of_all _ fun p => hbound p.2
  have hc := Toolkit.Foundations.Probability.Processes.condExp_history_next
    (X := fun _ => α) (E := 𝓑 → ℝ) μ₀ κ m
    (fun p : Toolkit.Foundations.Probability.Processes.History (fun _ => α) m × α => g p.2) hF
  filter_upwards [hc] with ω hω
  exact (hω.trans (hg (ω m))).symm

/-- For a finite-state Markov chain, [the expected score of two consecutive states equals
the expectation of the score averaged over the transition law from the current state](goal). -/
-- @node: finite_kernel_integral_transition
lemma finite_kernel_integral_transition
    {α : Type*} [Fintype α] [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀]
    (K : Kernel α α) [IsMarkovKernel K] (F : α → α → ℝ) (m : ℕ) :
    (∫ ω, F (ω m) (ω (m + 1))
      ∂Toolkit.Foundations.Probability.Processes.pathLaw μ₀
        (Toolkit.Foundations.Probability.Processes.homogeneousTransition K)) =
    ∫ ω, (∫ s, F (ω m) s ∂K (ω m))
      ∂Toolkit.Foundations.Probability.Processes.pathLaw μ₀
        (Toolkit.Foundations.Probability.Processes.homogeneousTransition K) := by
  classical
  let κ := Toolkit.Foundations.Probability.Processes.homogeneousTransition K
  let μ := Toolkit.Foundations.Probability.Processes.pathLaw μ₀ κ
  let 𝓕 := Toolkit.Foundations.Probability.Processes.naturalFiltration (fun _ => α)
  let G : Toolkit.Foundations.Probability.Processes.History (fun _ => α) m × α → ℝ :=
    fun p => F (p.1 ⟨m, Finset.mem_Iic.mpr le_rfl⟩) p.2
  have hF : Measurable (Function.uncurry F) := by fun_prop
  have hG : Measurable G := by
    have hprev : Measurable (fun p :
        Toolkit.Foundations.Probability.Processes.History (fun _ => α) m × α =>
          p.1 ⟨m, Finset.mem_Iic.mpr le_rfl⟩) :=
      (measurable_pi_apply _).comp measurable_fst
    exact hF.comp (hprev.prodMk measurable_snd)
  have hb (a b : α) : ‖F a b‖ ≤ ∑ i : α, ∑ j : α, ‖F i j‖ := by
    exact (Finset.single_le_sum (fun j _ => norm_nonneg (F a j))
      (Finset.mem_univ b)).trans (Finset.single_le_sum
        (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg (F i j)) (Finset.mem_univ a))
  have hi : Integrable G ((μ.map
      (Toolkit.Foundations.Probability.Processes.history (fun _ => α) m)).compProd (κ m)) := by
    apply Integrable.of_bound hG.aestronglyMeasurable (∑ i : α, ∑ j : α, ‖F i j‖)
    exact ae_of_all _ fun p => hb _ _
  have hc := Toolkit.Foundations.Probability.Processes.condExp_history_next
    (X := fun _ => α) (E := ℝ) μ₀ κ m G hi
  change (∫ ω, F (ω m) (ω (m + 1)) ∂μ) = _
  rw [← integral_condExp (𝓕.le m)]
  exact integral_congr_ae hc

end Papers.OaiMetricMarkovCotype
