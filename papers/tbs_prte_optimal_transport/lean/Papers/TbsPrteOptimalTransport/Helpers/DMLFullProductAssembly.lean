module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLFittedFullProduct
public import Papers.TbsPrteOptimalTransport.Helpers.DMLPoolingRemainder
/-! Assembly of the fitted binary full-interval score block and its quadratic bias rate. -/
public section
set_option linter.style.haveILetI false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- Clipping supplies the moment condition, including the fixed zero boundary.
-- @node: fitted_positive_success_memLp
/-- If [the binary nuisance vector is admissible](hyp:he), then
[each success-probability coordinate, extended by zero outside the positive levels, is square-integrable under the covariate law](goal). -/
lemma fitted_positive_success_memLp (L : LevelData Z X) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (i : ℕ) :
    MemLp (positiveValue e.P1 i) 2 (xLaw M) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  apply MemLp.of_bound (by fun_prop) 1
  filter_upwards [fitted_positive_success_range M L e he i] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
  exact hx.2

-- The coherent adjacent contrast inherits the two component errors. This
-- applies to the single rearranged P1 vector used throughout the score.
-- @node: fitted_binFullJ_l2Error_bound
/-- If [the reference binary nuisance vector is admissible](hyp:he) and [the fitted binary nuisance vector is admissible](hyp:heh), then
[the covariate L2 error of their adjacent success-probability contrast is at most the sum of the success-probability L2 errors at the upper and lower neighboring levels](goal). -/
lemma fitted_binFullJ_l2Error_bound (L : LevelData Z X) (e eh : NuisanceBin L)
    (he : BinAdmissible M L e) (heh : BinAdmissible M L eh) (k : ℕ) :
    finiteL2Error M (binFullJ L eh k) (binFullJ L e k) ≤
      finiteL2Error M (positiveValue eh.P1 (k+1)) (positiveValue e.P1 (k+1)) +
      finiteL2Error M (positiveValue eh.P1 k) (positiveValue e.P1 k) := by
  have hp := (fitted_positive_success_memLp M L eh heh (k+1)).sub
    (fitted_positive_success_memLp M L e he (k+1))
  have hm := (fitted_positive_success_memLp M L eh heh k).sub
    (fitted_positive_success_memLp M L e he k)
  have hid : (fun x => binFullJ L eh k x - binFullJ L e k x) =
      (fun x => positiveValue eh.P1 (k+1) x - positiveValue e.P1 (k+1) x) -
      (fun x => positiveValue eh.P1 k x - positiveValue e.P1 k x) := by
    funext x
    simp only [binFullJ, Pi.sub_apply]
    ring
  have hj : MemLp (fun x => binFullJ L eh k x - binFullJ L e k x) 2 (xLaw M) := by
    rw [hid]
    exact hp.sub hm
  rw [l2Error_eq_eLpNorm M _ _ hj, l2Error_eq_eLpNorm M _ _ hp,
    l2Error_eq_eLpNorm M _ _ hm, hid]
  calc
    _ ≤ (eLpNorm (fun x => positiveValue eh.P1 (k+1) x -
        positiveValue e.P1 (k+1) x) 2 (xLaw M) +
        eLpNorm (fun x => positiveValue eh.P1 k x - positiveValue e.P1 k x)
          2 (xLaw M)).toReal :=
      ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hp.eLpNorm_ne_top, hm.eLpNorm_ne_top⟩)
        (eLpNorm_sub_le hp.aestronglyMeasurable hm.aestronglyMeasurable (by norm_num))
    _ = _ := ENNReal.toReal_add hp.eLpNorm_ne_top hm.eLpNorm_ne_top

-- @node: fitted_binFullJ_quarter_rate
/-- If [the reference binary nuisance vector is admissible](hyp:he),
[all fitted nuisance vectors are admissible](hyp:heh), and
[the L2 error of each zero-extended success-probability coordinate is little-o in probability of the inverse fourth root of twice n plus two](hyp:hr), then
[the L2 error of any adjacent success-probability contrast is little-o in probability at the same rate](goal). -/
lemma fitted_binFullJ_quarter_rate {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (L : LevelData Z X) (e : NuisanceBin L)
    (eh : ℕ → A → NuisanceBin L) (he : BinAdmissible M L e)
    (heh : ∀ n a, BinAdmissible M L (eh n a)) (k : ℕ)
    (hr : ∀ i, Causalean.Stat.IsLittleOp
      (fun n a => finiteL2Error M (positiveValue (eh n a).P1 i) (positiveValue e.P1 i))
      (fun n => ((2 * (n+1) : ℕ) : ℝ) ^ (-1/4 : ℝ)) μ) :
    Causalean.Stat.IsLittleOp
      (fun n a => finiteL2Error M (binFullJ L (eh n a) k) (binFullJ L e k))
      (fun n => ((2 * (n+1) : ℕ) : ℝ) ^ (-1/4 : ℝ)) μ := by
  have hs := (hr (k+1)).add_eventually_nonneg_rate
    (Eventually.of_forall (fun _ => Real.rpow_nonneg (by positivity) _)) (hr k)
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul one_pos hs
  intro n a
  have hn : 0 ≤ finiteL2Error M (binFullJ L (eh n a) k) (binFullJ L e k) :=
    Real.sqrt_nonneg _
  rw [one_mul, abs_of_nonneg hn]
  exact (fitted_binFullJ_l2Error_bound M L e (eh n a) he (heh n a) k).trans
    (le_abs_self _)

-- The component bounds are summed for the actual score block. All three
-- errors below concern nuisance components, not the score bias itself.
-- @node: fitted_full_block_bias_bound
/-- Suppose [baseline overlap holds](hyp:hov), [the clipping constant c is positive](hyp:hc),
[the regression error envelope is nonnegative](hyp:hreg), [the weight error envelope is nonnegative](hyp:hwt),
[the outcome is binary almost surely](hyp:hy), [the true nuisance vector is admissible](hyp:he0),
[the fitted nuisance vector is admissible](hyp:he), and
[fitted positive-level assignment probabilities are bounded below by c almost everywhere](hyp:hclip).
If [every success-probability L2 error is bounded by the regression envelope](hyp:hP),
[every assignment-probability L2 error is bounded by the weight envelope](hyp:hPi), and
[every full-interval weight L2 error is bounded by the weight envelope](hyp:hG), then
[the full fitted score block is integrable and its absolute bias relative to the true full-interval target is at most the number of intervals times (2/c + 2) times the product of the two error envelopes](goal). -/
lemma fitted_full_block_bias_bound (L : LevelData Z X) (e : NuisanceBin L)
    (cpi c reg wt : ℝ) (hov : BaselineOverlapWitness M L cpi) (hc : 0 < c)
    (hreg : 0 ≤ reg) (hwt : 0 ≤ wt)
    (hy : OutcomeBinaryAE M) (he0 : BinAdmissible M L (eta0Bin M L))
    (he : BinAdmissible M L e)
    (hclip : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (hP : ∀ i, finiteL2Error M (positiveValue e.P1 i)
      (positiveValue (eta0Bin M L).P1 i) ≤ reg)
    (hPi : ∀ i, (eLpNorm (fun x => positiveValue e.piLev i x -
      positiveValue (eta0Bin M L).piLev i x) 2 (xLaw M)).toReal ≤ wt)
    (hG : ∀ k : Fin L.K, (eLpNorm (fun x => e.gammaFull k x -
      gammaFull M L k x) 2 (xLaw M)).toReal ≤ wt) :
    Integrable (fun o => ∑ k : Fin L.K, psiFullProdBin L e k o) (observationLaw M) ∧
    |(∫ o, ∑ k : Fin L.K, psiFullProdBin L e k o ∂observationLaw M) -
      (∑ k : Fin L.K, ∫ x, gammaFull M L k x * binFullJ L (eta0Bin M L) k x
        ∂xLaw M)| ≤ (L.K : ℝ) * (2 / c + 2) * (reg * wt) := by
  have hi (k : Fin L.K) : Integrable (psiFullProdBin L e k) (observationLaw M) :=
    (fitted_full_product_exact_bias M L e k cpi c hov hc hy he0 he hclip).1
  have hPn (i : ℕ) : (eLpNorm (fun x => positiveValue e.P1 i x -
      positiveValue (eta0Bin M L).P1 i x) 2 (xLaw M)).toReal ≤ reg := by
    rw [← l2Error_eq_eLpNorm M _ _ ((fitted_positive_success_memLp M L e he i).sub
      (fitted_positive_success_memLp M L (eta0Bin M L) he0 i))]
    exact hP i
  have hJ (k : Fin L.K) : (eLpNorm (fun x => binFullJ L e k x -
      binFullJ L (eta0Bin M L) k x) 2 (xLaw M)).toReal ≤ 2 * reg := by
    have hj := (fitted_positive_success_memLp M L e he (k+1)).sub
      (fitted_positive_success_memLp M L e he k)
    have hj0 := (fitted_positive_success_memLp M L (eta0Bin M L) he0 (k+1)).sub
      (fitted_positive_success_memLp M L (eta0Bin M L) he0 k)
    have hjdiff : MemLp (fun x => binFullJ L e k x - binFullJ L (eta0Bin M L) k x)
        2 (xLaw M) := hj.sub hj0
    rw [← l2Error_eq_eLpNorm M _ _ hjdiff]
    exact (fitted_binFullJ_l2Error_bound M L (eta0Bin M L) e he0 he k).trans
      (by linarith [hP (k+1), hP k])
  refine ⟨integrable_finsetSum Finset.univ (fun k _ => hi k), ?_⟩
  rw [integral_finsetSum Finset.univ (fun k _ => hi k), ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k : Fin L.K, |(∫ o, psiFullProdBin L e k o ∂observationLaw M) -
        (∫ x, gammaFull M L k x * binFullJ L (eta0Bin M L) k x ∂xLaw M)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin L.K, (2 / c + 2) * (reg * wt) := by
      apply Finset.sum_le_sum
      intro k _
      apply (fitted_full_product_bias_L2_bound M L e k cpi c hov hc hy he0 he hclip).trans
      calc
        _ ≤ wt * reg / c + wt * reg / c + wt * (2 * reg) := by
          gcongr
          · exact hPi (k+1)
          · exact hPn (k+1)
          · exact hPi k
          · exact hPn k
          · exact hG k
          · exact hJ k
        _ = _ := by ring
    _ = _ := by simp; ring

-- This is the full-interval contribution to the conditional DML bias.
-- Its rate follows from the fitted score expansion, including all residual
-- corrections, and not from a plug-in target expansion.
-- @node: fitted_full_block_root_n_bias_negligible
/-- Suppose [baseline overlap holds](hyp:hov), [the clipping constant is positive](hyp:hc),
[the regression and weight error envelopes are nonnegative for every fit](hyp:hreg,hwt),
[the outcome is binary almost surely](hyp:hy), [the true nuisance vector is admissible](hyp:he0),
[all fitted nuisance vectors are admissible](hyp:heh), and
[fitted positive-level assignment probabilities are bounded below by the clipping constant almost everywhere](hyp:hclip).
If [the regression envelope bounds every success-probability L2 error](hyp:hP),
[the weight envelope bounds every assignment-probability L2 error](hyp:hPi),
[the weight envelope also bounds every full-interval weight L2 error](hyp:hG), and
[both envelopes are little-o in probability of the inverse fourth root of twice n plus two](hyp:hr,hw), then
[the integrated fitted full-interval score block minus its true target, multiplied by the square root of n plus one, converges in probability to zero](goal). -/
lemma fitted_full_block_root_n_bias_negligible {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (L : LevelData Z X) (eh : ℕ → A → NuisanceBin L)
    (cpi c : ℝ) (reg wt : ℕ → A → ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hc : 0 < c)
    (hreg : ∀ n a, 0 ≤ reg n a) (hwt : ∀ n a, 0 ≤ wt n a)
    (hy : OutcomeBinaryAE M) (he0 : BinAdmissible M L (eta0Bin M L))
    (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hclip : ∀ n a (i : PositiveIndex L.K), ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x)
    (hP : ∀ n a i, finiteL2Error M (positiveValue (eh n a).P1 i)
      (positiveValue (eta0Bin M L).P1 i) ≤ reg n a)
    (hPi : ∀ n a i, (eLpNorm (fun x => positiveValue (eh n a).piLev i x -
      positiveValue (eta0Bin M L).piLev i x) 2 (xLaw M)).toReal ≤ wt n a)
    (hG : ∀ n a (k : Fin L.K), (eLpNorm (fun x => (eh n a).gammaFull k x -
      gammaFull M L k x) 2 (xLaw M)).toReal ≤ wt n a)
    (hr : Causalean.Stat.IsLittleOp reg
      (fun n => ((2 * (n+1) : ℕ) : ℝ) ^ (-1/4 : ℝ)) μ)
    (hw : Causalean.Stat.IsLittleOp wt
      (fun n => ((2 * (n+1) : ℕ) : ℝ) ^ (-1/4 : ℝ)) μ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        ((∫ o, ∑ k : Fin L.K, psiFullProdBin L (eh n a) k o ∂observationLaw M) -
          (∑ k : Fin L.K, ∫ x, gammaFull M L k x * binFullJ L (eta0Bin M L) k x
            ∂xLaw M))) atTop (fun _ _ => 0) := by
  have hC : 0 ≤ (L.K : ℝ) * (2 / c + 2) := by positivity
  apply dml_quadratic_bias_root_n_negligible μ _ reg wt
    ((L.K : ℝ) * (2 / c + 2) + 1) (by positivity) hr hw
  intro n a
  have hb := (fitted_full_block_bias_bound M L (eh n a) cpi c (reg n a) (wt n a)
    hov hc (hreg n a) (hwt n a) hy he0 (heh n a) (hclip n a)
    (hP n a) (hPi n a) (hG n a)).2
  apply hb.trans
  calc
    _ ≤ ((L.K : ℝ) * (2 / c + 2) + 1) * (reg n a * wt n a) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (hreg n a) (hwt n a))
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (sq_nonneg _))
      (by positivity)

end Papers.TbsPrteOptimalTransport
