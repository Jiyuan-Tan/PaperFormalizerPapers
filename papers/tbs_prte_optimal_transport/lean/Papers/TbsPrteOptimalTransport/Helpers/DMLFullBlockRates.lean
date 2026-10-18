module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBoundaryResidualRates
/-! Full-interval binary score bias from the componentwise nuisance rates.
Finite error envelopes are constructed here, including the fixed zero boundary. -/
public section
set_option linter.style.haveILetI false
set_option linter.style.openClassical false
set_option linter.unreachableTactic false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

-- @node: le_maxErrors_of_mem
/-- If [a real number belongs to a finite list of errors](hyp:h), then
[it is at most the maximum of zero and the errors in that list](goal). -/
lemma le_maxErrors_of_mem {r : ℝ} {s : List ℝ} (h : r ∈ s) :
    r ≤ maxErrors s := by
  induction s with
  | nil => simp at h
  | cons a s ih =>
    rcases List.mem_cons.mp h with h | h
    · subst r
      exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: fitted_gammaFull_memLp
/-- If [the binary nuisance vector is admissible](hyp:he), then
[its full-interval weight at any interval index is square-integrable under the covariate law](goal). -/
lemma fitted_gammaFull_memLp (L : LevelData Z X) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (k : Fin L.K) :
    MemLp (e.gammaFull k) 2 (xLaw M) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  rcases he with ⟨_, _, _, _, _, _, _, _, _, hgb, hgm, _, _⟩
  apply MemLp.of_bound (by first | fun_prop | exact (hgm k).aestronglyMeasurable) 1
  filter_upwards [hgb k] with x hx
  rw [Real.norm_eq_abs]
  exact abs_le.mpr hx

-- A single coherent P1 vector supplies both neighbors, with no independent
-- estimate or rate assumption for the interval gap.
-- @node: nuisanceRates_binFullJ_quarter_rate
/-- If [the reference binary nuisance vector is admissible](hyp:he0),
[all fitted nuisance vectors are admissible](hyp:heh), and
[the success-probability components satisfy the finite nuisance rates relative to the reference](hyp:hrP), then
[the adjacent success-probability contrasts also satisfy the finite nuisance rates](goal). -/
lemma nuisanceRates_binFullJ_quarter_rate {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (L : LevelData Z X) (e0 : NuisanceBin L)
    (eh : ℕ → A → NuisanceBin L) (he0 : BinAdmissible M L e0)
    (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1) :
    FiniteNuisanceRates M μ (fun n a k => binFullJ L (eh n a) k)
      (fun k => binFullJ L e0 k) := by
  have hr := nuisanceRates_positiveValue M μ L.K _ _ hrP
  intro k
  exact fitted_binFullJ_quarter_rate M μ L e0
    (fun n a => eh (2*(n+1)) a) he0 (fun n a => heh _ a) k hr

-- The only rates supplied are those of P1, pi, and gammaFull. The score
-- remainder itself is obtained from its proved residual-correction expansion.
-- @node: nuisanceRates_full_block_root_n_bias_negligible
/-- Suppose [baseline overlap holds with the specified overlap constant](hyp:hov),
[the clipping constant is positive](hyp:hc), [the outcome is binary almost surely](hyp:hy),
[the true binary nuisance vector is admissible](hyp:he0), [all fitted nuisance vectors are admissible](hyp:heh), and
[all fitted positive-level assignment probabilities are bounded below by the clipping constant almost everywhere](hyp:hclip).
If [the success-probability, assignment-probability, and full-interval weight components satisfy the finite nuisance rates relative to truth](hyp:hrP,hrpi,hrg), then
[the integrated fitted full-interval score block minus the true full-interval target, multiplied by the square root of n plus one and evaluated using fits at sample sizes twice n plus two, converges in probability to zero](goal). -/
lemma nuisanceRates_full_block_root_n_bias_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (eh : ℕ → A → NuisanceBin L)
    (cpi c : ℝ) (hov : BaselineOverlapWitness M L cpi) (hc : 0 < c)
    (hy : OutcomeBinaryAE M) (he0 : BinAdmissible M L (eta0Bin M L))
    (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) (eta0Bin M L).P1)
    (hrpi : FiniteNuisanceRates M μ (fun n a => (eh n a).piLev) (eta0Bin M L).piLev)
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gammaFull) (eta0Bin M L).gammaFull) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        ((∫ o, ∑ k : Fin L.K, psiFullProdBin L (eh (2*(n+1)) a) k o
            ∂observationLaw M) -
          (∑ k : Fin L.K, ∫ x, gammaFull M L k x * binFullJ L (eta0Bin M L) k x
            ∂xLaw M))) atTop (fun _ _ => 0) := by
  let ids := List.range (L.K + 1)
  let ks := (Finset.univ : Finset (Fin L.K)).toList
  let dP := fun n a i => finiteL2Error M (positiveValue (eh (2*(n+1)) a).P1 i)
    (positiveValue (eta0Bin M L).P1 i)
  let dpi := fun n a i => finiteL2Error M (positiveValue (eh (2*(n+1)) a).piLev i)
    (positiveValue (eta0Bin M L).piLev i)
  let dg := fun n a k => finiteL2Error M ((eh (2*(n+1)) a).gammaFull k)
    ((eta0Bin M L).gammaFull k)
  let reg := fun n a => maxErrors (ids.map (dP n a))
  let wt := fun n a => maxErrors (ids.map (dpi n a)) + maxErrors (ks.map (dg n a))
  have hP := nuisanceRates_positiveValue M μ L.K _ _ hrP
  have hpi := nuisanceRates_positiveValue M μ L.K _ _ hrpi
  have hr := nuisanceRates_finite_maxErrors M μ _ _ ids hP
  have hwpi := nuisanceRates_finite_maxErrors M μ _ _ ids hpi
  have hwg := nuisanceRates_finite_maxErrors M μ _ _ ks hrg
  have hw := hwpi.add_eventually_nonneg_rate
    (Eventually.of_forall (fun _ => Real.rpow_nonneg (by positivity) _)) hwg
  have hreg : ∀ n a, 0 ≤ reg n a := fun _ _ => maxErrors_nonneg _
  have hwt : ∀ n a, 0 ≤ wt n a := fun _ _ =>
    add_nonneg (maxErrors_nonneg _) (maxErrors_nonneg _)
  have bound (f : ℕ → ℝ) (i : ℕ) (hi : i ≤ L.K) :
      f i ≤ maxErrors (ids.map f) := by
    apply le_maxErrors_of_mem
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩
  have hPb (n : ℕ) (a : A) (i : ℕ) : dP n a i ≤ reg n a := by
    by_cases hi : i ≤ L.K
    · exact bound _ i hi
    · have hbad : ¬ (1 ≤ i ∧ i ≤ L.K) := by omega
      simpa only [dP, positiveValue, dif_neg hbad, finiteL2Error, sub_self,
        zero_pow (by norm_num : 2 ≠ 0), integral_zero, Real.sqrt_zero] using hreg n a
  have hpib (n : ℕ) (a : A) (i : ℕ) : dpi n a i ≤ wt n a := by
    have hb : dpi n a i ≤ maxErrors (ids.map (dpi n a)) := by
      by_cases hi : i ≤ L.K
      · exact bound _ i hi
      · have hbad : ¬ (1 ≤ i ∧ i ≤ L.K) := by omega
        simpa only [dpi, positiveValue, dif_neg hbad, finiteL2Error, sub_self,
          zero_pow (by norm_num : 2 ≠ 0), integral_zero, Real.sqrt_zero] using
          maxErrors_nonneg (ids.map (dpi n a))
    exact hb.trans (le_add_of_nonneg_right (maxErrors_nonneg _))
  have hgb (n : ℕ) (a : A) (k : Fin L.K) : dg n a k ≤ wt n a := by
    have hb : dg n a k ≤ maxErrors (ks.map (dg n a)) := by
      apply le_maxErrors_of_mem
      exact List.mem_map.mpr ⟨k, by simp [ks], rfl⟩
    exact hb.trans (le_add_of_nonneg_left (maxErrors_nonneg _))
  apply fitted_full_block_root_n_bias_negligible M μ L
    (fun n a => eh (2*(n+1)) a) cpi c reg wt hov hc hreg hwt hy he0
    (fun n a => heh _ a) (fun n a => hclip _ a) hPb
  · intro n a i
    rw [← l2Error_eq_eLpNorm M _ _
      (((fitted_positive_treatment_assignment_memLp M L (eh (2*(n+1)) a)
        (heh _ a) i).2).sub
          (fitted_positive_treatment_assignment_memLp M L (eta0Bin M L) he0 i).2)]
    exact hpib n a i
  · intro n a k
    change (eLpNorm (fun x => (eh (2*(n+1)) a).gammaFull k x -
      (eta0Bin M L).gammaFull k x) 2 (xLaw M)).toReal ≤ wt n a
    rw [← l2Error_eq_eLpNorm M _ _
      ((fitted_gammaFull_memLp M L (eh (2*(n+1)) a) (heh _ a) k).sub
        (fitted_gammaFull_memLp M L (eta0Bin M L) he0 k))]
    exact hgb n a k
  · exact hr
  · exact hw

end Papers.TbsPrteOptimalTransport
