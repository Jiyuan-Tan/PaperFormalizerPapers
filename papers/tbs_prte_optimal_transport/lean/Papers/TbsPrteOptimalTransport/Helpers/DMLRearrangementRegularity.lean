module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBinaryRearrangement
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBinaryRearrangementAdmissibility
public import Papers.TbsPrteOptimalTransport.Helpers.DMLFullProductAssembly
/-! Measurability and moment conditions for the clipped binary rearrangement.
The finite sorting construction supplies these conditions before aggregate
contraction is used to preserve the componentwise nuisance rates. -/
public section
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.openClassical false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: rearrangeP1_component_l2Error_le_sum_ae
/-- If [the fitted binary nuisance record is admissible](hyp:he),
[the target record is admissible](hyp:ht), and [the target success probabilities
are nondecreasing across positive levels for almost every covariate value](hyp:hmono),
then [the covariate-distribution L² error of any one rearranged success
probability is bounded by the sum of the original positive-level L² errors](goal). -/
lemma rearrangeP1_component_l2Error_le_sum_ae (L : LevelData Z X)
    (e truth : NuisanceBin L) (he : BinAdmissible M L e)
    (ht : BinAdmissible M L truth)
    (hmono : ∀ᵐ x ∂xLaw M, ∀ i j : PositiveIndex L.K,
      i.val ≤ j.val → truth.P1 i x ≤ truth.P1 j x) (i : Fin L.K) :
    finiteL2Error M (positiveValue (rearrangeP1 L e).P1 (i + 1))
      (positiveValue truth.P1 (i + 1)) ≤
    ∑ j : Fin L.K, finiteL2Error M (positiveValue e.P1 (j + 1))
      (positiveValue truth.P1 (j + 1)) := by
  have hs (j : Fin L.K) := ((fitted_positive_success_memLp M L
    (rearrangeP1 L e) (rearrangeP1_admissible M L e he) (j + 1)).sub
    (fitted_positive_success_memLp M L truth ht (j + 1))).integrable_sq
  have hu (j : Fin L.K) := ((fitted_positive_success_memLp M L e he (j + 1)).sub
    (fitted_positive_success_memLp M L truth ht (j + 1))).integrable_sq
  simp only [Pi.sub_apply] at hs hu
  have hrange : ∀ᵐ x ∂xLaw M, ∀ k, truth.P1 k x ∈ Icc (0 : ℝ) 1 :=
    ae_all_iff.mpr (fun k => (ht.2.2.1 k).mono (fun _ hx => hx.2.1))
  have htotal : (∑ j : Fin L.K, ∫ x,
      (positiveValue (rearrangeP1 L e).P1 (j + 1) x -
        positiveValue truth.P1 (j + 1) x)^2 ∂xLaw M) ≤
      ∑ j : Fin L.K, ∫ x,
        (positiveValue e.P1 (j + 1) x - positiveValue truth.P1 (j + 1) x)^2 ∂xLaw M := by
    rw [← integral_finsetSum _ (fun j _ => hs j),
      ← integral_finsetSum _ (fun j _ => hu j)]
    apply integral_mono_ae (integrable_finsetSum _ (fun j _ => hs j))
      (integrable_finsetSum _ (fun j _ => hu j))
    filter_upwards [hmono, hrange] with x hm hx
    exact rearrangeP1_aggregate_squared_error_le L e truth x hm hx
  have hsingle : (∫ x,
      (positiveValue (rearrangeP1 L e).P1 (i + 1) x -
        positiveValue truth.P1 (i + 1) x)^2 ∂xLaw M) ≤
      ∑ j : Fin L.K, ∫ x,
        (positiveValue (rearrangeP1 L e).P1 (j + 1) x -
          positiveValue truth.P1 (j + 1) x)^2 ∂xLaw M := by
    apply Finset.single_le_sum _ (Finset.mem_univ i)
    intro j _
    exact integral_nonneg (fun x => sq_nonneg _)
  have hsq := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
    (f := fun j : Fin L.K => finiteL2Error M (positiveValue e.P1 (j + 1))
      (positiveValue truth.P1 (j + 1))) (fun _ _ => Real.sqrt_nonneg _)
  simp only [finiteL2Error, Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg _))] at hsq
  have hb := Real.sqrt_le_sqrt (hsingle.trans (htotal.trans hsq))
  simpa only [finiteL2Error, Real.sqrt_sq (Finset.sum_nonneg
    (fun j _ => Real.sqrt_nonneg _))] using hb

-- @node: dml_fin_sum_isLittleOp
/-- For [a rate that is positive at every sample size](hyp:hr), if
[each member of a fixed finite collection is negligible in probability
relative to that rate](hyp:hf), then [their sum is negligible in probability
relative to the same rate](goal). -/
lemma dml_fin_sum_isLittleOp {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (N : ℕ) (f : ℕ → A → Fin N → ℝ)
    (hf : ∀ j, Causalean.Stat.IsLittleOp (fun n a => f n a j) r μ) :
    Causalean.Stat.IsLittleOp (fun n a => ∑ j, f n a j) r μ := by
  induction N with
  | zero =>
    have hz := maxErrors_isLittleOp μ ([] : List Unit) (fun _ _ _ => (0 : ℝ))
      r hr (by simp)
    simpa only [List.map_nil, maxErrors, List.foldr_nil, Fin.sum_univ_zero] using hz
  | succ N ih =>
    have ht := ih (fun n a j => f n a j.succ) (fun j => hf j.succ)
    simpa only [Fin.sum_univ_succ] using
      (hf 0).add_eventually_nonneg_rate (Eventually.of_forall (fun n => (hr n).le)) ht

-- @node: nuisanceRates_rearrangeP1
/-- If [all fitted binary nuisance records are admissible](hyp:hf),
[the target record is admissible](hyp:ht), [its success probabilities are
nondecreasing across positive levels almost everywhere](hyp:hmono), and
[the fitted positive-level success probabilities satisfy the required
componentwise nuisance rates](hyp:hr), then [clipping and sorting those
probabilities preserves the same rates toward the target probabilities](goal). -/
lemma nuisanceRates_rearrangeP1 {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (L : LevelData Z X) (fit : ℕ → A → NuisanceBin L)
    (truth : NuisanceBin L) (hf : ∀ n a, BinAdmissible M L (fit n a))
    (ht : BinAdmissible M L truth)
    (hmono : ∀ᵐ x ∂xLaw M, ∀ i j : PositiveIndex L.K,
      i.val ≤ j.val → truth.P1 i x ≤ truth.P1 j x)
    (hr : FiniteNuisanceRates M μ (fun n a => (fit n a).P1) truth.P1) :
    FiniteNuisanceRates M μ (fun n a => (rearrangeP1 L (fit n a)).P1) truth.P1 := by
  have hrate (j : Fin L.K) : Causalean.Stat.IsLittleOp
      (fun n a => finiteL2Error M (positiveValue (fit (2 * (n + 1)) a).P1 (j + 1))
        (positiveValue truth.P1 (j + 1)))
      (fun n => ((2 * (n + 1) : ℕ) : ℝ)^(-1 / 4 : ℝ)) μ := by
    let k : PositiveIndex L.K := ⟨j.val + 1, by omega⟩
    have hp (e : NuisanceBin L) : positiveValue e.P1 (j.val + 1) = e.P1 k := by
      funext x
      exact dif_pos k.property
    simpa only [hp] using hr k
  have hsum := dml_fin_sum_isLittleOp μ _ (fun n => Real.rpow_pos_of_pos (by positivity) _)
    L.K _ hrate
  intro k
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul one_pos hsum
  intro n a
  rw [one_mul]
  rw [abs_of_nonneg (show 0 ≤ finiteL2Error M
    ((rearrangeP1 L (fit (2 * (n + 1)) a)).P1 k) (truth.P1 k) from Real.sqrt_nonneg _)]
  apply le_trans _ (le_abs_self _)
  have hh := rearrangeP1_component_l2Error_le_sum_ae M L (fit (2 * (n + 1)) a)
    truth (hf _ _) ht hmono ⟨k.val - 1, by omega⟩
  have hp (e : NuisanceBin L) : positiveValue e.P1 k.val = e.P1 k := by
    funext x
    exact dif_pos k.property
  simpa only [show k.val - 1 + 1 = k.val by omega, hp] using hh

end Papers.TbsPrteOptimalTransport
