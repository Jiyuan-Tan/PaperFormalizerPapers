module
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationContinuousBandWeights
/-! Simultaneous regular-product weight directions of the continuous total score. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: continuous_band_product_weight_path
/-- If [the level index is at most the number of levels](hyp:hk) and [the band index lies between one and the number of bands at that level](hyp:hj,hjl), [adding a scalar multiple of a direction to the regular weights changes the band product score by that scalar times the direction times the difference between the debiased band score and its plug-in value](goal). -/
lemma continuous_band_product_weight_path (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (eta : NuisanceCont L) (d : RegularIndex L → X → ℝ)
    (k j : ℕ) (hk : k ≤ L.K) (hj : 1 ≤ j) (hjl : j ≤ L.l k)
    (o : Obs X Z) (t : ℝ) :
    psiProd M phi dphi L {eta with gamma := fun a x => eta.gamma a x + t * d a x} k j o =
      psiProd M phi dphi L eta k j o + t * (regularValue d k j o.1 *
        (contScoreComponents M phi dphi L eta k (j - 1) o - contJ L eta k (j - 1) o.1)) := by
  have hs : contScoreComponents M phi dphi L
      {eta with gamma := fun a x => eta.gamma a x + t * d a x} k (j - 1) o =
      contScoreComponents M phi dphi L eta k (j - 1) o := rfl
  have hJ : contJ L {eta with gamma := fun a x => eta.gamma a x + t * d a x}
      k (j - 1) o.1 = contJ L eta k (j - 1) o.1 := rfl
  simp only [psiProd, hs, hJ, regularValue, dif_pos (And.intro hk (And.intro hj hjl))]
  ring

-- @node: continuous_total_band_weight_path
/-- With [a positive number of levels](hyp:hK), [perturbing all regular weights by a common scalar times a direction changes the total continuous score by that scalar times the sum of direction-weighted differences between debiased band scores and their plug-in values over all regular bands](goal). -/
lemma continuous_total_band_weight_path (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (hK : LevelCountPos L.K) (eta : NuisanceCont L)
    (d : RegularIndex L → X → ℝ) (o : Obs X Z) (t : ℝ) :
    psiCont M phi dphi L hK o {eta with gamma := fun a x => eta.gamma a x + t * d a x} =
      psiCont M phi dphi L hK o eta + t *
        ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k), regularValue d k j o.1 *
          (contScoreComponents M phi dphi L eta k (j - 1) o - contJ L eta k (j - 1) o.1) := by
  have hf : ∀ k, psiFullProd L
      {eta with gamma := fun a x => eta.gamma a x + t * d a x} k o =
      psiFullProd L eta k o := fun _ => rfl
  simp only [psiCont, hf]
  rw [Finset.mul_sum]
  have hs : ∀ k ∈ Finset.range L.K,
      psiFullProd L eta k o + ∑ j ∈ Finset.Icc 1 (L.l k),
        psiProd M phi dphi L {eta with gamma := fun a x => eta.gamma a x + t * d a x} k j o =
      (psiFullProd L eta k o + ∑ j ∈ Finset.Icc 1 (L.l k), psiProd M phi dphi L eta k j o) +
        t * ∑ j ∈ Finset.Icc 1 (L.l k), regularValue d k j o.1 *
          (contScoreComponents M phi dphi L eta k (j - 1) o - contJ L eta k (j - 1) o.1) := by
    intro k hk
    have hj : ∀ j ∈ Finset.Icc 1 (L.l k),
        psiProd M phi dphi L {eta with gamma := fun a x => eta.gamma a x + t * d a x} k j o =
        psiProd M phi dphi L eta k j o + t * (regularValue d k j o.1 *
          (contScoreComponents M phi dphi L eta k (j - 1) o - contJ L eta k (j - 1) o.1)) := by
      intro j hj
      exact continuous_band_product_weight_path M phi dphi L eta d k j
        (Finset.mem_range.mp hk).le (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 o t
    rw [Finset.sum_congr rfl hj, Finset.sum_add_distrib, Finset.mul_sum]
    ring
  rw [Finset.sum_congr rfl hs, Finset.sum_add_distrib]
  ring

-- @node: population_continuous_total_band_weight_integral_path
/-- Assume [the structural model conditions](hyp:h), [known outcome endpoints](hyp:he), [a measurable policy derivative evaluated at the baseline propensity](hyp:hdphi), [a positive number of levels](hyp:hK), [level ordering preserved by the policy](hyp:hL), [baseline overlap](hyp:hov), [policy overlap](hyp:hpol), [measurable band boundaries](hyp:hb), [bounded boundary densities](hyp:hd), and [no atom at the lower endpoint](hyp:h0). For [measurable regular-weight directions](hyp:hw), if the direction-weighted [plug-in band values](hyp:hplugin), [outcome influence corrections](hyp:hJ), [lower-boundary mass corrections](hyp:hMa), [upper-boundary mass corrections](hyp:hMb), [lower propensity corrections](hyp:hl), [upper propensity corrections](hyp:hh), [lower policy corrections](hyp:hql), and [upper policy corrections](hyp:hqh) are integrable, and [the true total score is integrable](hyp:hbase), then [every scalar perturbation of the true regular weights leaves the population mean of the total continuous score unchanged](goal). -/
lemma population_continuous_total_band_weight_integral_path
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hb : ∀ k j, Measurable (bandBoundary M L k j))
    (hd : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L)
    (d : RegularIndex L → X → ℝ) (hw : ∀ a, Measurable (d a))
    (hplugin : ∀ k, k < L.K → ∀ j, j < L.l k → Integrable (fun o : Obs X Z => regularValue d k (j + 1) o.1 *
      contJ L (trueNuisance M L) k j o.1) (observationLaw M))
    (hJ : ∀ k, k < L.K → ∀ j, j < L.l k → ∀ plus, Integrable (fun o : Obs X Z => regularValue d k (j + 1) o.1 *
      IFJ M L (trueNuisance M L) plus k j o) (observationLaw M))
    (hMa : ∀ k, k < L.K → ∀ j, j < L.l k → ∀ plus, Integrable (fun o : Obs X Z =>
      (regularValue d k (j + 1) o.1 * bandBoundary M L k j o.1) *
      IFM M L (trueNuisance M L) plus k j o) (observationLaw M))
    (hMb : ∀ k, k < L.K → ∀ j, j < L.l k → ∀ plus, Integrable (fun o : Obs X Z =>
      (regularValue d k (j + 1) o.1 * bandBoundary M L k (j + 1) o.1) *
      IFM M L (trueNuisance M L) plus k (j + 1) o) (observationLaw M))
    (hl : ∀ k, k < L.K → ∀ j, j < L.l k → Integrable (fun o : Obs X Z => (regularValue d k (j + 1) o.1 *
      alphaLow M L (trueNuisance M L) k j o.1) *
      RpCont L (trueNuisance M L) k o) (observationLaw M))
    (hh : ∀ k, k < L.K → ∀ j, j < L.l k → Integrable (fun o : Obs X Z => (regularValue d k (j + 1) o.1 *
      alphaHigh M L (trueNuisance M L) k j o.1) *
      RpCont L (trueNuisance M L) (k + 1) o) (observationLaw M))
    (hql : ∀ k, k < L.K → ∀ j, j < L.l k → Integrable (fun o : Obs X Z => (regularValue d k (j + 1) o.1 * bandBoundary M L k j o.1) *
      RqCont dphi L (trueNuisance M L) k j o) (observationLaw M))
    (hqh : ∀ k, k < L.K → ∀ j, j < L.l k → Integrable (fun o : Obs X Z => (regularValue d k (j + 1) o.1 * bandBoundary M L k (j + 1) o.1) *
      RqCont dphi L (trueNuisance M L) k (j + 1) o) (observationLaw M))
    (hbase : Integrable (fun o => psiCont M phi dphi L hK o (trueNuisance M L))
      (observationLaw M)) (t : ℝ) :
    (∫ o, psiCont M phi dphi L hK o
      {trueNuisance M L with gamma := fun a x => (trueNuisance M L).gamma a x + t * d a x}
      ∂observationLaw M) =
    ∫ o, psiCont M phi dphi L hK o (trueNuisance M L) ∂observationLaw M := by
  have hc k (hk : k < L.K) j (hj : j < L.l k) :=
    population_continuous_band_correction_weighted_zero M h he phi dphi hdphi L hL cpi
      hov hpol k j hk hj (hb k j) (hb k (j + 1)) hd h0
      (regularValue d k (j + 1)) (by
        unfold regularValue
        split_ifs
        · exact hw _
        · fun_prop)
      (hplugin k hk j hj) (hJ k hk j hj) (hMa k hk j hj) (hMb k hk j hj)
      (hl k hk j hj) (hh k hk j hj) (hql k hk j hj) (hqh k hk j hj)
  have hi : ∀ k ∈ Finset.range L.K, ∀ j ∈ Finset.Icc 1 (L.l k),
      Integrable (fun o : Obs X Z => regularValue d k j o.1 *
        (contScoreComponents M phi dphi L (trueNuisance M L) k (j - 1) o -
          contJ L (trueNuisance M L) k (j - 1) o.1)) (observationLaw M) := by
    intro k hk j hj
    have hj1 := (Finset.mem_Icc.mp hj).1
    have hjl := (Finset.mem_Icc.mp hj).2
    simpa only [Nat.sub_add_cancel hj1] using
      (hc k (Finset.mem_range.mp hk) (j - 1) (by omega)).1
  have hz : (∫ o : Obs X Z, ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
      regularValue d k j o.1 *
        (contScoreComponents M phi dphi L (trueNuisance M L) k (j - 1) o -
          contJ L (trueNuisance M L) k (j - 1) o.1) ∂observationLaw M) = 0 := by
    rw [integral_finsetSum _ (fun k hk => integrable_finsetSum _ (hi k hk))]
    apply Finset.sum_eq_zero
    intro k hk
    rw [integral_finsetSum _ (hi k hk)]
    apply Finset.sum_eq_zero
    intro j hj
    have hj1 := (Finset.mem_Icc.mp hj).1
    have hjl := (Finset.mem_Icc.mp hj).2
    simpa only [Nat.sub_add_cancel hj1] using
      (hc k (Finset.mem_range.mp hk) (j - 1) (by omega)).2
  simp_rw [continuous_total_band_weight_path]
  rw [integral_add hbase
    ((integrable_finsetSum _ (fun k hk => integrable_finsetSum _ (hi k hk))).const_mul t),
    integral_const_mul, hz, mul_zero, add_zero]

-- @node: population_continuous_total_band_weight_orthogonality
/-- Assume [the structural model conditions](hyp:h), [known outcome endpoints](hyp:he), [a measurable policy derivative at the baseline propensity](hyp:hdphi), [a positive number of levels](hyp:hK), [policy-invariant level ordering](hyp:hL), [baseline overlap](hyp:hov), [policy overlap](hyp:hpol), [measurable band boundaries](hyp:hb), [bounded boundary densities](hyp:hd), and [no lower-endpoint atom](hyp:h0). For [measurable regular-weight directions](hyp:hw), suppose the direction-weighted [plug-in band values](hyp:hplugin), [outcome influence corrections](hyp:hJ), [lower mass corrections](hyp:hMa), [upper mass corrections](hyp:hMb), [lower propensity corrections](hyp:hl), [upper propensity corrections](hyp:hh), [lower policy corrections](hyp:hql), and [upper policy corrections](hyp:hqh) are integrable and [the true total score is integrable](hyp:hbase); then [the population mean of the continuous score has derivative zero at the true regular weights along this direction](goal). -/
lemma population_continuous_total_band_weight_orthogonality
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (phi dphi : Z → X → ℝ → ℝ)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hL : LevelOrderInvariant M.prop (policyProp phi M.prop) L) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hb : ∀ k j, Measurable (bandBoundary M L k j))
    (hd : BoundaryDensitiesBounded M L) (h0 : NoAtomAtLowerEndpoint M L)
    (d : RegularIndex L → X → ℝ) (hw : ∀ a, Measurable (d a))
    (hplugin : ∀ k, k < L.K → ∀ j, j < L.l k → Integrable (fun o : Obs X Z => regularValue d k (j + 1) o.1 *
      contJ L (trueNuisance M L) k j o.1) (observationLaw M))
    (hJ : ∀ k, k < L.K → ∀ j, j < L.l k → ∀ plus, Integrable (fun o : Obs X Z => regularValue d k (j + 1) o.1 *
      IFJ M L (trueNuisance M L) plus k j o) (observationLaw M))
    (hMa : ∀ k, k < L.K → ∀ j, j < L.l k → ∀ plus, Integrable (fun o : Obs X Z =>
      (regularValue d k (j + 1) o.1 * bandBoundary M L k j o.1) *
      IFM M L (trueNuisance M L) plus k j o) (observationLaw M))
    (hMb : ∀ k, k < L.K → ∀ j, j < L.l k → ∀ plus, Integrable (fun o : Obs X Z =>
      (regularValue d k (j + 1) o.1 * bandBoundary M L k (j + 1) o.1) *
      IFM M L (trueNuisance M L) plus k (j + 1) o) (observationLaw M))
    (hl : ∀ k, k < L.K → ∀ j, j < L.l k → Integrable (fun o : Obs X Z => (regularValue d k (j + 1) o.1 *
      alphaLow M L (trueNuisance M L) k j o.1) *
      RpCont L (trueNuisance M L) k o) (observationLaw M))
    (hh : ∀ k, k < L.K → ∀ j, j < L.l k → Integrable (fun o : Obs X Z => (regularValue d k (j + 1) o.1 *
      alphaHigh M L (trueNuisance M L) k j o.1) *
      RpCont L (trueNuisance M L) (k + 1) o) (observationLaw M))
    (hql : ∀ k, k < L.K → ∀ j, j < L.l k → Integrable (fun o : Obs X Z => (regularValue d k (j + 1) o.1 * bandBoundary M L k j o.1) *
      RqCont dphi L (trueNuisance M L) k j o) (observationLaw M))
    (hqh : ∀ k, k < L.K → ∀ j, j < L.l k → Integrable (fun o : Obs X Z => (regularValue d k (j + 1) o.1 * bandBoundary M L k (j + 1) o.1) *
      RqCont dphi L (trueNuisance M L) k (j + 1) o) (observationLaw M))
    (hbase : Integrable (fun o => psiCont M phi dphi L hK o (trueNuisance M L))
      (observationLaw M)) :
    HasDerivAt (fun t : ℝ => ∫ o, psiCont M phi dphi L hK o
      {trueNuisance M L with gamma := fun a x => (trueNuisance M L).gamma a x + t * d a x}
      ∂observationLaw M) 0 0 := by
  have heq : (fun t : ℝ => ∫ o, psiCont M phi dphi L hK o
      {trueNuisance M L with gamma := fun a x => (trueNuisance M L).gamma a x + t * d a x}
      ∂observationLaw M) =
      (fun _ : ℝ => ∫ o, psiCont M phi dphi L hK o (trueNuisance M L)
        ∂observationLaw M) := by
    funext t
    exact population_continuous_total_band_weight_integral_path M h he phi dphi hdphi
      L hK hL cpi hov hpol hb hd h0 d hw hplugin hJ hMa hMb hl hh hql hqh hbase t
  rw [heq]
  exact hasDerivAt_const 0 _

end Papers.TbsPrteOptimalTransport
