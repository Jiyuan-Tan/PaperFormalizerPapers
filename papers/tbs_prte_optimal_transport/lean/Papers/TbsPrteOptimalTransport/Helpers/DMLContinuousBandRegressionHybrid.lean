module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLContinuousBandProductRegression
/-! Restoring band regressions in the continuous fitted score.
The hybrid retains the fitted quantiles, propensities and weights. Its band
regressions are restored to the reference values, so admissibility and all
component rates persist. The fitted-to-hybrid product block is negligible. -/
@[expose] public section
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: continuousBandRegressionHybrid
/-- The [band regression hybrid](goal) takes [a base nuisance](hyp:e) and
[a reference nuisance](hyp:b), retaining the base coordinates except that the
upper and lower band probability and outcome regressions come from the reference. -/
def continuousBandRegressionHybrid {L : LevelData Z X} (e b : NuisanceCont L) :
    NuisanceCont L :=
  {e with Mplus := b.Mplus, Mminus := b.Mminus, Jplus := b.Jplus, Jminus := b.Jminus}

-- @node: continuous_band_regression_hybrid_admissible
/-- If [the base nuisance is admissible](hyp:he) and [the reference nuisance is
admissible](hyp:hb), then [replacing the base's band probability and outcome
regressions with the reference regressions yields an admissible nuisance](goal). -/
lemma continuous_band_regression_hybrid_admissible
    (L : LevelData Z X) (e b : NuisanceCont L)
    (he : ContAdmissible M L e) (hb : ContAdmissible M L b) :
    ContAdmissible M L (continuousBandRegressionHybrid e b) := by
  rcases he with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    h13, h14, h15, h16, h17, h18, _, _, _, _, _, _, _, _, h27, h28, h29, h30, h31⟩
  rcases hb with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    h19, h20, h21, h22, h23, h24, h25, h26, _⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26,
    h27, h28, h29, h30, h31⟩

-- @node: continuous_band_regression_hybrid_component
/-- [An encoded coordinate of the band regression hybrid equals the reference
coordinate for coordinate types 9, 10, 11, and 12, and equals the base
coordinate for every other type](goal). -/
lemma continuous_band_regression_hybrid_component
    (L : LevelData Z X) (e b : NuisanceCont L) (i : ℕ × ℕ × ℕ × Z) :
    contComponent M L (continuousBandRegressionHybrid e b) i =
      if i.1 ∈ ({9, 10, 11, 12} : Finset ℕ) then contComponent M L b i
        else contComponent M L e i := by
  rcases i with ⟨r, k, j, z⟩
  rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | r <;>
    simp only [Finset.mem_insert, Finset.mem_singleton, false_or,
      true_or, if_true, if_false, Nat.succ_ne_zero, Nat.succ.injEq]
  all_goals
    funext x
    simp [contComponent, continuousBandRegressionHybrid, minusFullValue,
      shareValue, nuValue]
  split <;> first | omega | rfl

-- @node: encoded_continuous_band_regression_hybrid_rates
/-- If [the fitted encoded nuisance errors have little-o fourth-root rates
relative to a reference nuisance](hyp:hr), then [replacing their band
regressions with the reference regressions preserves those coordinatewise
L² rates](goal). -/
lemma encoded_continuous_band_regression_hybrid_rates
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (L : LevelData Z X) (e0 : NuisanceCont L) (eh : ℕ → A → NuisanceCont L)
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L e0)) :
    FiniteNuisanceRates M μ
      (fun n a => contComponent M L (continuousBandRegressionHybrid (eh n a) e0))
      (contComponent M L e0) := by
  intro i
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul one_pos (hr i)
  intro n a
  dsimp only
  rw [continuous_band_regression_hybrid_component M, one_mul]
  split_ifs
  · simp only [finiteL2Error, sub_self, abs_zero, zero_pow (by norm_num : 2 ≠ 0),
      integral_zero, Real.sqrt_zero]
    exact abs_nonneg _
  · exact le_rfl

-- @node: continuous_restored_band_regression_block_integrable
/-- For [an admissible base nuisance](hyp:he) and [an admissible reference
nuisance](hyp:hb), suppose [each band number in the finite block is between one
and its level's band count](hyp:hj), [the clipping constant is positive](hyp:hc),
and [all base assignment denominators are at least that constant almost
everywhere](hyp:hclip). Then [the sum over the block of product-score changes
from restoring the reference band regressions is integrable](goal). -/
lemma continuous_restored_band_regression_block_integrable
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e b : NuisanceCont L)
    (he : ContAdmissible M L e) (hb : ContAdmissible M L b)
    (t : Finset (Fin L.K × ℕ))
    (hj : ∀ i ∈ t, 1 ≤ i.2 ∧ i.2 ≤ L.l i.1)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ i, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) :
    Integrable (fun o : Obs X Z => ∑ i ∈ t,
      (psiProd M phi dphi L e i.1 i.2 o -
        psiProd M phi dphi L (continuousBandRegressionHybrid e b) i.1 i.2 o))
      (observationLaw M) := by
  apply integrable_finsetSum
  intro i hit
  exact continuous_band_product_joint_regression_integrable M phi dphi L
    e (continuousBandRegressionHybrid e b) he
    (continuous_band_regression_hybrid_admissible M L e b he hb)
    rfl rfl rfl rfl rfl rfl rfl i.1 i.2 (hj i hit) c hc hclip

-- @node: encoded_continuous_restored_band_regression_block_root_n_negligible
/-- Suppose [truth is admissible](hyp:he0), [every fitted nuisance is
admissible](hyp:heh), and [the encoded fitted errors have little-o fourth-root
rates relative to truth](hyp:hr). If [all band numbers in the finite block lie
between one and their level's band count](hyp:hj), [the clipping constant is
positive](hyp:hc), and [the fitted assignment denominators are uniformly at
least that constant almost everywhere](hyp:hclip), then [the mean sum of
product-score changes from restoring the true band regressions, using fits at
size twice n plus two and scaled by the square root of n plus one, converges
to zero in probability](goal). -/
lemma encoded_continuous_restored_band_regression_block_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (eh : ℕ → A → NuisanceCont L)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (heh : ∀ n a, ContAdmissible M L (eh n a))
    (hr : FiniteNuisanceRates M μ (fun n a => contComponent M L (eh n a))
      (contComponent M L (trueNuisance M L)))
    (t : Finset (Fin L.K × ℕ))
    (hj : ∀ i ∈ t, 1 ≤ i.2 ∧ i.2 ≤ L.l i.1)
    (c : ℝ) (hc : 0 < c)
    (hclip : ∀ n a i, ∀ᵐ x ∂xLaw M, c ≤ (eh n a).piLev i x) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        ∫ o : Obs X Z, ∑ i ∈ t,
          (psiProd M phi dphi L (eh (2*(n+1)) a) i.1 i.2 o -
            psiProd M phi dphi L
              (continuousBandRegressionHybrid (eh (2*(n+1)) a) (trueNuisance M L))
              i.1 i.2 o) ∂observationLaw M)
      atTop (fun _ _ => 0) := by
  exact encoded_continuous_band_product_joint_regression_block_root_n_negligible
    M μ phi dphi L eh
    (fun n a => continuousBandRegressionHybrid (eh n a) (trueNuisance M L))
    he0 heh (fun n a => continuous_band_regression_hybrid_admissible
      M L (eh n a) (trueNuisance M L) (heh n a) he0)
    hr (encoded_continuous_band_regression_hybrid_rates M μ L _ eh hr)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    t hj c hc hclip

end Papers.TbsPrteOptimalTransport
