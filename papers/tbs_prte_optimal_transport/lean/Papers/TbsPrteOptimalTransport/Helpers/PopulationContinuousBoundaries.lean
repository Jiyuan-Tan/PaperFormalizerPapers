module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationBinaryTarget
public import Papers.TbsPrteOptimalTransport.Helpers.GapKernelQuantile
/-! Measurability of the constructed finite-instrument quantile boundaries. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set
open scoped Classical
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: ordered_policy_level_measurable
/-- With [jointly measurable policy propensities](hyp:hq),
[covariate-invariant level ordering](hyp:hL), and [measurable baseline levels](hyp:hlev),
[each ordered policy level is measurable](goal) whenever
[the bin is at or before the final bin](hyp:hk) and
[the policy index is at most the bin's policy-level count](hyp:hj). -/
@[fun_prop] lemma ordered_policy_level_measurable
    (q : Z → X → ℝ) (hq : Measurable (Function.uncurry q))
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (hlev : ∀ k, Measurable (L.pLev k))
    (k j : ℕ) (hk : k ≤ L.K) (hj : j ≤ L.l k) : Measurable (L.qLev k j) := by
  first | fun_prop | skip
  by_cases hj0 : j = 0
  · subst j
    have heq : L.qLev k 0 = L.pLev k := by
      funext x
      rw [hL.2.1 x k 0 hk (by omega), if_pos rfl]
    rw [heq]
    exact hlev k
  · obtain ⟨z, hz⟩ := ordered_policy_level_nonempty M q L hL k j hk (by omega) hj
    have heq : L.qLev k j = q z := by
      funext x
      exact ((hL.2.2.2.2.2.2.1 x k j z hk (by omega) hj).mp hz).symm
    rw [heq]
    exact hq.comp (measurable_const.prodMk measurable_id)

-- @node: population_bandBoundary_measurable
/-- If [policy propensities are jointly measurable](hyp:hq),
[level ordering is invariant across covariates](hyp:hL), and
[baseline levels are measurable](hyp:hlev), then [the population band boundary is measurable](goal)
for [a nonfinal bin](hyp:hk) and [an index no larger than its policy-level count](hyp:hj). -/
@[fun_prop] lemma population_bandBoundary_measurable
    (q : Z → X → ℝ) (hq : Measurable (Function.uncurry q))
    (L : LevelData Z X) (hL : LevelOrderInvariant M.prop q L)
    (hlev : ∀ k, Measurable (L.pLev k))
    (k j : ℕ) (hk : k < L.K) (hj : j ≤ L.l k) :
    Measurable (bandBoundary M L k j) := by
  first | fun_prop | skip
  by_cases hj0 : j = 0
  · subst j
    change Measurable (fun x => bandBoundary M L k 0 x)
    simpa only [bandBoundary, true_or, if_true] using
      (measurable_const : Measurable (fun _ : X => M.yMin))
  have hqj := ordered_policy_level_measurable M q hq L hL hlev k j hk.le hj
  have hr : Measurable (kappa L k j) := by
    change Measurable (fun x => (L.qLev k j x - L.pLev k x) /
      (L.pLev (k+1) x - L.pLev k x))
    fun_prop
  let K := outcomeKernel (latentMarginal M true)
  letI := outcomeKernel_isMarkov (latentMarginal M true)
  obtain ⟨D, hD, hDeq⟩ := exists_normalized_interval_kernel K (L.pLev k)
    (L.pLev (k+1)) (hlev k) (hlev (k+1)) M.yMin
  letI := hD
  have heq (x : X) : D x = discreteGapLaw M L k x := by
    have ha := hL.2.2.2.2.2.2.2.2.2.2.1 x k (by omega)
    have hab := hL.2.2.2.2.2.2.2.1 x k (k+1) (by omega) (by omega)
    rw [hDeq, if_pos hab, discreteGapLaw,
      canonical_treated_increment M x _ _ ha.1 hab.le]
  have hm := (measurable_kernel_endpoint_quantile D M.yMin M.yMax).comp
    (measurable_id.prodMk hr)
  convert hm using 1
  funext x
  dsimp only [Function.comp_def, id_eq]
  have hinputs := hL.2.2.2.2.2.2.2.2.2.1
  have hkr := (canonical_level_ranges M.prop q L
    (fun z x => (hinputs z x).1) (fun z x => (hinputs z x).2) hL).2.2
      x k j hk (by omega)
  have hlt := kappa_lt_one_of_policy_level M.prop q L hL x k j hk (by omega) hj
  by_cases hz : kappa L k j x = 0
  · simp [bandBoundary, hj0, hz]
  · have ht : kappa L k j x ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne hkr.1 (Ne.symm hz), hlt⟩
    simp only [bandBoundary, hj0, false_or, if_neg hz, if_neg (ne_of_lt hlt),
      if_pos ht, heq]

end Papers.TbsPrteOptimalTransport
