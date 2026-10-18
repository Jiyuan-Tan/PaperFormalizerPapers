module
public import Papers.TbsPrteOptimalTransport.Helpers.FittedBranchRegression
public import Papers.TbsPrteOptimalTransport.Helpers.JointFullRegressionWeights
/-! Finite-sum assembly of binary outcome-regression orthogonality. -/
public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set
open scoped Classical

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)

variable [Fintype Z] [DecidableEq Z]

-- @node: population_binary_regular_product_regression_path_integrable
/-- Assume [threshold crossing](hyp:h), [a valid policy map](hyp:hphi),
[measurability of the policy derivative evaluated at the propensity](hyp:hdphi),
[a nonnegative derivative bound](hyp:hB), and [that bound on the absolute
policy derivative at every instrument and covariate value](hyp:hbphi).
Under [invariant ordering of baseline and policy levels](hyp:hOrder),
[measurable propensity levels](hyp:hlev), [baseline](hyp:hov) and [policy
overlap](hyp:hpol), [binary outcomes almost surely](hyp:hy), [an admissible
nuisance direction at the truth](hyp:had), [a level index below the level
count](hyp:hk), and [a band index between one and the level's band count](hyp:hj),
[the regular binary product score is integrable under the observation law
at every point of the affine path that perturbs only the treated regressions
in that direction](goal). -/
lemma population_binary_regular_product_regression_path_integrable
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (B : ℝ) (hB : 0 ≤ B) (hbphi : ∀ z x, |dphi z x (M.prop z x)| ≤ B)
    (L : LevelData Z X) (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hlev : ∀ i, Measurable (L.pLev i)) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hy : OutcomeBinaryAE M) (del : NuisanceBin L)
    (had : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del))
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (t : ℝ) :
    Integrable (psiProdBin phi dphi L
      {eta0Bin M L with P1 := fun a x => (eta0Bin M L).P1 a x + t * del.P1 a x}
      k j) (observationLaw M) := by
  have : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  have : IsProbabilityMeasure (xLaw M) := Measure.isProbabilityMeasure_map M.measX.aemeasurable
  have he := binary_admissible_direction_origin M L (eta0Bin M L) del had
  obtain ⟨C, hC, hd⟩ := binary_regression_direction_regular M L (eta0Bin M L) del had
  have hpos i := binary_positive_regression_direction_regular M L del.P1 C hC hd i
  let d := fun x => positiveValue del.P1 (k+1) x - positiveValue del.P1 k x
  have hdm : Measurable d := (hpos (k+1)).1.sub (hpos k).1
  have hdb : ∀ᵐ x ∂xLaw M, ‖d x‖ ≤ 2*C := by
    filter_upwards [(hpos (k+1)).2, (hpos k).2] with x hp hm
    exact (norm_sub_le _ _).trans (by linarith)
  let et : ℝ → NuisanceBin L := fun t : ℝ => {eta0Bin M L with P1 := fun a x => (eta0Bin M L).P1 a x + t * del.P1 a x}
  let w := gamma M L k j
  have hw : Measurable w := population_instrument_set_probability_measurable M (policyUnion L k j)
  have hwb : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ 1 := by
    apply Filter.Eventually.of_forall
    intro x
    have hx := population_instrument_set_probability_range M (policyUnion L k j) x
    simpa only [w, gamma, Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2
  have hq := population_pooledQBin_measurable M h phi hphi L hlev k j
  have hl := population_pooledQBin_measurable M h phi hphi L hlev k (j-1)
  have hp : Measurable (positiveValue (eta0Bin M L).pLev (k+1)) := by
    unfold positiveValue
    split_ifs
    · exact hlev (k+1)
    · fun_prop
  have hb0 : Measurable (fun x => positiveValue (eta0Bin M L).pLev (k+1) x -
      binFullJ L (eta0Bin M L) k x) := by fun_prop
  have hbt (t : ℝ) : Measurable (fun x => positiveValue (et t).pLev (k+1) x -
      binFullJ L (et t) k x) := by
    have hid : (fun x => positiveValue (et t).pLev (k+1) x - binFullJ L (et t) k x) =
        (fun x => (positiveValue (eta0Bin M L).pLev (k+1) x -
          binFullJ L (eta0Bin M L) k x) + t * (-d x)) := by
      funext x
      exact binary_regression_boundary_path L (eta0Bin M L) del.P1 k x t
    rw [hid]
    fun_prop
  have hD t : Measurable (Dbd phi L (et t) k j) :=
    binary_Dbd_measurable phi L (et t) k j hq hl (hbt t)
  have hE t : Measurable (Edom phi L (et t) k j) :=
    binary_Edom_measurable phi L (et t) k j hl (hbt t)
  have hI t : Measurable (Iact phi L (et t) k j) :=
    binary_Iact_measurable phi L (et t) k j hq hl (hbt t)
  have hH t : Measurable (hMinus phi L (et t) k j) := by
    unfold hMinus
    exact measurable_const.max (hq.sub (hl.max (hbt t)))
  have hHb t : ∀ᵐ x ∂xLaw M, ‖hMinus phi L (et t) k j x‖ ≤ 1 := by
    filter_upwards [pooledQBin_range M phi L (eta0Bin M L) hphi he k hk j hj.2,
      pooledQBin_range M phi L (eta0Bin M L) hphi he k hk (j-1)
        ((Nat.sub_le j 1).trans hj.2)] with x hqx hlx
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
    apply max_le zero_le_one
    exact (sub_le_self _ (hlx.1.trans (le_max_left _ _))).trans hqx.2
  have hDb t : ∀ x, ‖Dbd phi L (et t) k j x‖ ≤ 1 := by
    intro x
    unfold Dbd indicator
    split_ifs <;> norm_num
  have iP i := population_binary_weighted_RP_integrable M L cpi hov hy he i w hw 1 hwb
  have ip i := population_binary_weighted_Rp_integrable M L cpi hov he i w hw 1 hwb
  have iq a := population_binary_weighted_RqBin_integrable M h dphi hdphi B hB hbphi
    phi L hOrder cpi hpol he k a w hw 1 hwb
  let f := fun t x => w x * (hMinus phi L (et t) k j x - Dbd phi L (et t) k j x * (t*d x))
  have hfm t : Measurable (f t) := by dsimp only [f]; fun_prop
  have hfint t : Integrable (fun o : Obs X Z => f t o.1) (observationLaw M) := by
    have ih : Integrable (fun o : Obs X Z => hMinus phi L (et t) k j o.1)
        (observationLaw M) := Integrable.of_bound ((hH t).comp measurable_fst).aestronglyMeasurable
          1 (observationLaw_covariate_ae M _ (hHb t))
    have id : Integrable (fun o : Obs X Z => t*d o.1) (observationLaw M) := by
      apply Integrable.of_bound ((hdm.comp measurable_fst).const_mul t).aestronglyMeasurable (|t| * (2*C))
      filter_upwards [observationLaw_covariate_ae M _ hdb] with o ho
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left ho (abs_nonneg t)
    have iDd := id.bdd_mul ((hD t).comp measurable_fst).aestronglyMeasurable
      (Filter.Eventually.of_forall fun o : Obs X Z => hDb t o.1)
    exact (ih.sub' iDd).bdd_mul (hw.comp measurable_fst).aestronglyMeasurable
      (observationLaw_covariate_ae M _ hwb)
  have hcomp := population_binary_regression_component_integral_path M h phi dphi hdphi
    L hOrder cpi hov del.P1 C hC hd w hw 1 zero_le_one hwb k j t
    (hD t) (hE t) (hI t) (iP (k+1)) (iP k) (ip (k+1)) (ip k) (iq j) (iq (j-1)) (hfint t)
  have hres := population_assignment_residual_integrable M (policyUnion L k j)
    (hMinus phi L (et t) k j) (hH t) 1 (hHb t)
  have hid : (fun o => psiProdBin phi dphi L (et t) k j o) =
      (fun o => w o.1 * binScoreComponents phi dphi L (et t) k j o +
        hMinus phi L (et t) k j o.1 * (indicator (o.2.1 ∈ policyUnion L k j) - w o.1)) := by
    funext o
    simp only [psiProdBin, regularValue, dif_pos (show k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from ⟨hk.le, hj⟩), et, eta0Bin]
    rfl
  change Integrable (fun o => psiProdBin phi dphi L (et t) k j o) _
  rw [hid]
  exact hcomp.1.fun_add hres

-- @node: population_binary_total_regression_orthogonality_of_gap
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[a finite instrument reduction](hyp:hf), [a valid policy map](hyp:hphi),
[measurability of the policy derivative at the propensity](hyp:hdphi),
[a nonnegative derivative bound](hyp:hB), and [that bound on its absolute
value everywhere](hyp:hbphi), suppose [the level count is positive](hyp:hK),
[baseline and policy level ordering is invariant](hyp:hOrder), [the propensity
levels are measurable](hyp:hlev), [baseline](hyp:hov) and [policy overlap
hold](hyp:hpol), [outcomes are binary almost surely](hyp:hy), [the nuisance
direction is admissible at the truth](hyp:had), and [the discrete outcome
gap condition holds](hyp:hgap). Then [the expected total binary score has
derivative zero at zero along the affine path perturbing only the treated
regressions in that direction](goal). -/
lemma population_binary_total_regression_orthogonality_of_gap
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (hf : InstrumentFiniteReduction Z) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi)
    (hdphi : Measurable (fun zx : Z × X => dphi zx.1 zx.2 (M.prop zx.1 zx.2)))
    (B : ℝ) (hB : 0 ≤ B) (hbphi : ∀ z x, |dphi z x (M.prop z x)| ≤ B)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hlev : ∀ i, Measurable (L.pLev i)) (cpi : ℝ)
    (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hy : OutcomeBinaryAE M) (del : NuisanceBin L)
    (had : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del))
    (hgap : DiscreteOutcomeGap M L) :
    HasDerivAt (fun t : ℝ => ∫ o, psiBin M phi dphi L hK o
      {eta0Bin M L with P1 := fun a x => (eta0Bin M L).P1 a x + t * del.P1 a x}
      ∂observationLaw M) 0 0 := by
  let et : ℝ → NuisanceBin L := fun t => {eta0Bin M L with
    P1 := fun a x => (eta0Bin M L).P1 a x + t * del.P1 a x}
  have ifull t : ∀ k ∈ Finset.range L.K,
      Integrable (psiFullProdBin L (et t) k) (observationLaw M) := by
    intro k hk
    exact population_binary_full_regression_path_integrable_of_admissible M L cpi hov
      hy del had ⟨k, Finset.mem_range.mp hk⟩ t
  have ireg t : ∀ k ∈ Finset.range L.K, ∀ j ∈ Finset.Icc 1 (L.l k),
      Integrable (psiProdBin phi dphi L (et t) k j) (observationLaw M) := by
    intro k hk j hj
    exact population_binary_regular_product_regression_path_integrable M h.2.2.2.1
      phi dphi hphi hdphi B hB hbphi L hOrder hlev cpi hov hpol hy del had
      k j (Finset.mem_range.mp hk) (Finset.mem_Icc.mp hj) t
  have isum t : Integrable (fun o => ∑ k ∈ Finset.range L.K,
      (psiFullProdBin L (et t) k o +
        ∑ j ∈ Finset.Icc 1 (L.l k), psiProdBin phi dphi L (et t) k j o))
      (observationLaw M) :=
    integrable_finsetSum _ (fun k hk => (ifull t k hk).fun_add
      (integrable_finsetSum _ (ireg t k hk)))
  have het0 : et 0 = eta0Bin M L := by
    simp only [et, zero_mul, add_zero]
    rfl
  have ibase := (population_binary_score_mean_of_overlap M h.2.2.2.1 phi dphi hphi
    hdphi B hB hbphi L hK hOrder hlev cpi hov hpol hy
    (binary_admissible_direction_origin M L (eta0Bin M L) del had)).1
  have itail : Integrable (fun o => commonTailScore M phi dphi L
      (eta0Bin M L).prop (eta0Bin M L).pLev (eta0Bin M L).piLev
      (eta0Bin M L).gammaTail o) (observationLaw M) := by
    have hi := ibase.sub' (isum 0)
    rw [het0] at hi
    convert hi using 1
    funext o
    simp only [psiBin]
    ring
  have hdf : ∀ k ∈ Finset.range L.K,
      HasDerivAt (fun t : ℝ => ∫ o, psiFullProdBin L (et t) k o
        ∂observationLaw M) 0 0 := by
    intro k hk
    exact population_binary_full_product_regression_orthogonality_of_admissible M
      L cpi hov hy del had ⟨k, Finset.mem_range.mp hk⟩
  have hdr : ∀ k ∈ Finset.range L.K, ∀ j ∈ Finset.Icc 1 (L.l k),
      HasDerivAt (fun t : ℝ => ∫ o, psiProdBin phi dphi L (et t) k j o
        ∂observationLaw M) 0 0 := by
    intro k hk j hj
    exact population_binary_regular_product_regression_orthogonality_of_gap M h he hf
      phi dphi hphi hdphi B hB hbphi L hOrder hlev cpi hov hpol hy del had hgap
      k j (Finset.mem_range.mp hk) (Finset.mem_Icc.mp hj)
  have hs := HasDerivAt.fun_sum (fun k hk => (hdf k hk).add
    (HasDerivAt.fun_sum (hdr k hk)))
  have heq : (fun t : ℝ => ∫ o, psiBin M phi dphi L hK o (et t)
      ∂observationLaw M) =
      (fun t : ℝ => (∑ k ∈ Finset.range L.K,
        ((∫ o, psiFullProdBin L (et t) k o ∂observationLaw M) +
          ∑ j ∈ Finset.Icc 1 (L.l k),
            ∫ o, psiProdBin phi dphi L (et t) k j o ∂observationLaw M)) +
        ∫ o, commonTailScore M phi dphi L (eta0Bin M L).prop
          (eta0Bin M L).pLev (eta0Bin M L).piLev (eta0Bin M L).gammaTail o
          ∂observationLaw M) := by
    funext t
    simp only [psiBin]
    change (∫ o, (∑ k ∈ Finset.range L.K, _) +
      commonTailScore M phi dphi L (eta0Bin M L).prop
        (eta0Bin M L).pLev (eta0Bin M L).piLev (eta0Bin M L).gammaTail o
      ∂observationLaw M) = _
    rw [integral_add (isum t) itail,
      integral_finsetSum _ (fun k hk => (ifull t k hk).fun_add
        (integrable_finsetSum _ (ireg t k hk)))]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [integral_add (ifull t k hk) (integrable_finsetSum _ (ireg t k hk)),
      integral_finsetSum _ (ireg t k hk)]
  change HasDerivAt (fun t : ℝ => ∫ o, psiBin M phi dphi L hK o (et t)
    ∂observationLaw M) 0 0
  rw [heq]
  simpa only [Finset.sum_const_zero, add_zero, Pi.add_apply] using hs.add_const
    (∫ o, commonTailScore M phi dphi L (eta0Bin M L).prop
      (eta0Bin M L).pLev (eta0Bin M L).piLev (eta0Bin M L).gammaTail o
      ∂observationLaw M)

end Papers.TbsPrteOptimalTransport
