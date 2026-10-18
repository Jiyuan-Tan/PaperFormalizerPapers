module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLFittedRegularProduct
public import Papers.TbsPrteOptimalTransport.Helpers.DMLIndicatorRates
/-! L2 control of the product-weight contribution to the fitted fractional binary score bias. -/
public section
set_option linter.style.haveILetI false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- Clipping supplies the moment condition even at unused indices.
-- @node: fitted_regular_gamma_memLp
/-- If [the binary nuisance collection is admissible](hyp:he), then [its regular product weight is square integrable under the covariate distribution at every pair of indices](goal). -/
lemma fitted_regular_gamma_memLp (L : LevelData Z X) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (k j : ℕ) :
    MemLp (regularValue e.gamma k j) 2 (xLaw M) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  have hm : Measurable (regularValue e.gamma k j) := by
    first | fun_prop | skip
    unfold regularValue
    split_ifs
    · exact (he.2.2.2.2.2.1 _).2
    · fun_prop
  apply MemLp.of_bound hm.aestronglyMeasurable 1
  unfold regularValue
  split_ifs with hi
  · filter_upwards [he.2.2.2.2.1 ⟨(k,j), hi⟩] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx.2.1]
    exact hx.2.2
  · simp

-- The policy is only measurable on its documented domain. Its clipped
-- representative supplies the L2 moment without pointwise clipping premises.
-- @node: binary_hMinus_memLp_of_admissible
/-- For [a valid policy map](hyp:hphi) and [an admissible binary nuisance collection](hyp:he), at [a level below the level count](hyp:hk) and [a boundary between one and that level's boundary count](hyp:hj), [the lower binary hinge is square integrable under the covariate distribution](goal). -/
lemma binary_hMinus_memLp_of_admissible
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e)
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    MemLp (hMinus phi L e k j) 2 (xLaw M) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  obtain ⟨H, hH, hHe⟩ := binary_hMinus_measurable_version M phi hphi L e he k j
  have hHp : MemLp H 2 (xLaw M) := by
    apply MemLp.of_bound hH.aestronglyMeasurable 1
    filter_upwards [hHe,
      binary_auxiliary_ranges M phi L e hphi he k hk j hj.1 hj.2] with x hx hr
    rw [hx, Real.norm_eq_abs, abs_of_nonneg hr.1.1]
    exact hr.1.2
  exact hHp.ae_eq hHe

-- This is exactly the product of errors left by the fitted event correction.
-- No moment assumptions are added: both errors are differences of clipped
-- admissible nuisances.
-- @node: fitted_regular_product_cross_L2_bound
/-- For [a valid policy map](hyp:hphi), [an admissible reference nuisance collection](hyp:he0), and [an admissible fitted collection](hyp:he), at [a level below the level count](hyp:hk) and [a valid positive boundary index](hyp:hj), [the product of the regular-weight error and lower-hinge error is integrable, and its absolute expectation is at most the product of their population L² errors](goal). -/
lemma fitted_regular_product_cross_L2_bound
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e0 e : NuisanceBin L)
    (he0 : BinAdmissible M L e0) (he : BinAdmissible M L e)
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    Integrable (fun x => (regularValue e.gamma k j x - regularValue e0.gamma k j x) *
      (hMinus phi L e k j x - hMinus phi L e0 k j x)) (xLaw M) ∧
    |∫ x, (regularValue e.gamma k j x - regularValue e0.gamma k j x) *
      (hMinus phi L e k j x - hMinus phi L e0 k j x) ∂xLaw M| ≤
      finiteL2Error M (regularValue e.gamma k j) (regularValue e0.gamma k j) *
        finiteL2Error M (hMinus phi L e k j) (hMinus phi L e0 k j) := by
  have hg := (fitted_regular_gamma_memLp M L e he k j).sub
    (fitted_regular_gamma_memLp M L e0 he0 k j)
  have hh := (binary_hMinus_memLp_of_admissible M phi hphi L e he k j hk hj).sub
    (binary_hMinus_memLp_of_admissible M phi hphi L e0 he0 k j hk hj)
  refine ⟨hg.integrable_mul hh, ?_⟩
  rw [l2Error_eq_eLpNorm M _ _ hg, l2Error_eq_eLpNorm M _ _ hh]
  calc
    _ ≤ ∫ x, |(regularValue e.gamma k j x - regularValue e0.gamma k j x) *
        (hMinus phi L e k j x - hMinus phi L e0 k j x)| ∂xLaw M := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x => (regularValue e.gamma k j x - regularValue e0.gamma k j x) *
          (hMinus phi L e k j x - hMinus phi L e0 k j x))
    _ ≤ _ := Causalean.Stat.integral_abs_mul_le_eLpNorm_mul_eLpNorm hg hh

-- Assemble the actual fitted-score identity with the cross-product bound.
-- The remaining component bias still includes both regression and policy
-- residual corrections; it is not replaced by the plug-in target error.
-- @node: fitted_regular_product_bias_L2_decomposition
/-- Assume [threshold crossing](hyp:h), [a valid policy map](hyp:hphi) with [the specified derivative](hyp:hDiff) whose [values are bounded and Lipschitz](hyp:hDerivative), [level ordering invariant under the policy](hyp:hOrder), [baseline overlap at the given overlap constant](hyp:hov), and [an almost surely binary outcome](hyp:hy). For [admissible true nuisances](hyp:he0) and [admissible fitted nuisances](hyp:he), with [a positive lower bound](hyp:hc) on [all fitted level probabilities](hyp:hpi) and [all fitted regular-cell probabilities](hyp:htau), at [a level below the level count](hyp:hk) and [a valid positive boundary](hyp:hj), [the absolute product-score bias is bounded by the absolute expectation of the fitted-weighted hinge discrepancy including regression and policy mean corrections, plus the product of the weight and hinge L² errors](goal). -/
lemma fitted_regular_product_bias_L2_decomposition
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hy : OutcomeBinaryAE M)
    (he0 : BinAdmissible M L (eta0Bin M L)) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (c : ℝ) (hc : 0 < c)
    (hpi : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ e.piLev a x)
    (htau : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev a x)
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    |(∫ o, psiProdBin phi dphi L e k j o ∂observationLaw M) -
      (∫ o : Obs X Z, gamma M L k j o.1 *
        hMinus phi L (eta0Bin M L) k j o.1 ∂observationLaw M)| ≤
      |∫ o : Obs X Z, regularValue e.gamma k j o.1 *
        (hMinus phi L e k j o.1 +
          binaryRegularRegressionMean phi L (eta0Bin M L) e k j o.1 +
          binaryRegularPolicyMean M phi dphi L e k j o.1 -
          hMinus phi L (eta0Bin M L) k j o.1) ∂observationLaw M| +
      finiteL2Error M (regularValue e.gamma k j) (regularValue (eta0Bin M L).gamma k j) *
        finiteL2Error M (hMinus phi L e k j) (hMinus phi L (eta0Bin M L) k j) := by
  let a : RegularIndex L := ⟨(k,j), hk.le, hj⟩
  have hw : Measurable (regularValue e.gamma k j) := by
    first | fun_prop | skip
    change Measurable (fun x => regularValue e.gamma k j x)
    simpa only [regularValue, dif_pos (show k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from
      ⟨hk.le, hj⟩)] using (he.2.2.2.2.2.1 a).2
  have hb : ∀ᵐ x ∂xLaw M, ‖regularValue e.gamma k j x‖ ≤ 1 := by
    filter_upwards [he.2.2.2.2.1 a] with x hx
    simp only [regularValue, dif_pos (show k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from
      ⟨hk.le, hj⟩)]
    rw [Real.norm_eq_abs, abs_of_nonneg hx.2.1]
    exact hx.2.2
  have ht := population_binary_regular_component_correction_fitted_mean M h phi dphi
    hphi hDiff hDerivative L hOrder cpi hov hy he0 e he c hc hpi htau k j hk.le
    (regularValue e.gamma k j) hw 1 hb
  have iPlug := binary_weighted_hMinus_integrable_of_admissible M phi hphi L e he
    k j hk hj (regularValue e.gamma k j) hw 1 hb
  have iTrue := binary_weighted_hMinus_integrable_of_admissible M phi hphi L
    (eta0Bin M L) he0 k j hk hj (regularValue e.gamma k j) hw 1 hb
  have iComp : Integrable (fun o : Obs X Z => regularValue e.gamma k j o.1 *
      (hMinus phi L e k j o.1 +
        binaryRegularRegressionMean phi L (eta0Bin M L) e k j o.1 +
        binaryRegularPolicyMean M phi dphi L e k j o.1 -
        hMinus phi L (eta0Bin M L) k j o.1)) (observationLaw M) := by
    convert (iPlug.fun_add ht.2.1).sub' iTrue using 1
    funext o
    ring
  let cross := fun x => (regularValue e.gamma k j x -
    regularValue (eta0Bin M L).gamma k j x) *
    (hMinus phi L e k j x - hMinus phi L (eta0Bin M L) k j x)
  obtain ⟨iCross, hCross⟩ := fitted_regular_product_cross_L2_bound M phi hphi L
    (eta0Bin M L) e he0 he k j hk hj
  have hobs := M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
  have hmap : (observationLaw M).map Prod.fst = xLaw M := by
    simpa only [observationLaw, xLaw, Function.comp_def] using
      Measure.map_map measurable_fst hobs
  have iMap : Integrable cross ((observationLaw M).map Prod.fst) := by
    simpa only [hmap] using iCross
  have iCo : Integrable (fun o : Obs X Z => cross o.1) (observationLaw M) :=
    (integrable_map_measure iMap.aestronglyMeasurable measurable_fst.aemeasurable).mp iMap
  have hCo : (∫ o : Obs X Z, cross o.1 ∂observationLaw M) =
      ∫ x, cross x ∂xLaw M := by
    rw [← hmap]
    exact (integral_map measurable_fst.aemeasurable iMap.aestronglyMeasurable).symm
  have hg0 (x : X) : regularValue (eta0Bin M L).gamma k j x = gamma M L k j x := by
    simp only [regularValue, eta0Bin, dif_pos (show k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from
      ⟨hk.le, hj⟩)]
  rw [(fitted_regular_product_exact_bias M h phi dphi hphi hDiff hDerivative L hOrder
    cpi hov hy he0 e he c hc hpi htau k j hk hj).2]
  simp_rw [← hg0]
  rw [integral_sub iComp iCo]
  apply (abs_sub _ _).trans
  apply add_le_add le_rfl
  rw [hCo]
  exact hCross

-- Nested maxima are Lipschitz also at fitted ties and off the population
-- branch. Thus the product-error term needs no branch-stability event.
-- @node: binary_hinge_difference_abs_le
/-- [The absolute change in the positive part of an upper argument minus the maximum of two lower arguments is at most the sum of the absolute changes in all three arguments](goal). -/
lemma binary_hinge_difference_abs_le (q l b qh lh bh : ℝ) :
    |max 0 (qh - max lh bh) - max 0 (q - max l b)| ≤
      |qh - q| + |lh - l| + |bh - b| := by
  have hm : |max lh bh - max l b| ≤ |lh - l| + |bh - b| :=
    (abs_max_sub_max_le_max lh bh l b).trans
      (max_le (le_add_of_nonneg_right (abs_nonneg _))
        (le_add_of_nonneg_left (abs_nonneg _)))
  have ho : |max 0 (qh - max lh bh) - max 0 (q - max l b)| ≤
      |(qh - max lh bh) - (q - max l b)| := by
    simpa only [sub_self, abs_zero,
      max_eq_right (abs_nonneg ((qh - max lh bh) - (q - max l b)))] using
      abs_max_sub_max_le_max (0 : ℝ) (qh - max lh bh) 0 (q - max l b)
  have hid : (qh - max lh bh) - (q - max l b) =
      (qh - q) - (max lh bh - max l b) := by ring
  rw [hid] at ho
  exact (ho.trans (abs_sub _ _)).trans (by linarith)

-- The raw affine arguments, rather than a rate for the hinge itself, control
-- its L2 error. The hinge moment is supplied by admissibility above.
-- @node: fitted_hMinus_l2Error_bound
/-- For [a valid policy map](hyp:hphi), [admissible reference nuisances](hyp:he0), and [admissible fitted nuisances](hyp:he), at [a level below the level count](hyp:hk) and [a valid positive boundary](hyp:hj), suppose the differences in [the current pooled policy argument](hyp:hq), [the preceding pooled policy argument](hyp:hl), and [the next-level probability minus the full-level term](hyp:hb) are square integrable. Then [the lower-hinge L² error is at most the sum of the L² errors in these three arguments](goal). -/
lemma fitted_hMinus_l2Error_bound
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e0 e : NuisanceBin L)
    (he0 : BinAdmissible M L e0) (he : BinAdmissible M L e)
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (hq : MemLp (fun x => pooledQBin phi L e k j x - pooledQBin phi L e0 k j x)
      2 (xLaw M))
    (hl : MemLp (fun x => pooledQBin phi L e k (j-1) x -
      pooledQBin phi L e0 k (j-1) x) 2 (xLaw M))
    (hb : MemLp (fun x => (positiveValue e.pLev (k+1) x - binFullJ L e k x) -
      (positiveValue e0.pLev (k+1) x - binFullJ L e0 k x)) 2 (xLaw M)) :
    finiteL2Error M (hMinus phi L e k j) (hMinus phi L e0 k j) ≤
      finiteL2Error M (pooledQBin phi L e k j) (pooledQBin phi L e0 k j) +
      finiteL2Error M (pooledQBin phi L e k (j-1)) (pooledQBin phi L e0 k (j-1)) +
      finiteL2Error M (fun x => positiveValue e.pLev (k+1) x - binFullJ L e k x)
        (fun x => positiveValue e0.pLev (k+1) x - binFullJ L e0 k x) := by
  let eq := fun x => pooledQBin phi L e k j x - pooledQBin phi L e0 k j x
  let el := fun x => pooledQBin phi L e k (j-1) x - pooledQBin phi L e0 k (j-1) x
  let eb := fun x => (positiveValue e.pLev (k+1) x - binFullJ L e k x) -
    (positiveValue e0.pLev (k+1) x - binFullJ L e0 k x)
  have hh := (binary_hMinus_memLp_of_admissible M phi hphi L e he k j hk hj).sub
    (binary_hMinus_memLp_of_admissible M phi hphi L e0 he0 k j hk hj)
  have hmono : eLpNorm (fun x => hMinus phi L e k j x - hMinus phi L e0 k j x)
      2 (xLaw M) ≤ eLpNorm (fun x => ‖eq x‖ + ‖el x‖ + ‖eb x‖) 2 (xLaw M) := by
    apply eLpNorm_mono_ae_real
    apply Eventually.of_forall
    intro x
    simpa only [hMinus, Real.norm_eq_abs, eq, el, eb] using
      binary_hinge_difference_abs_le
        (pooledQBin phi L e0 k j x) (pooledQBin phi L e0 k (j-1) x)
        (positiveValue e0.pLev (k+1) x - binFullJ L e0 k x)
        (pooledQBin phi L e k j x) (pooledQBin phi L e k (j-1) x)
        (positiveValue e.pLev (k+1) x - binFullJ L e k x)
  have hsum : eLpNorm (fun x => ‖eq x‖ + ‖el x‖ + ‖eb x‖) 2 (xLaw M) ≤
      eLpNorm eq 2 (xLaw M) + eLpNorm el 2 (xLaw M) + eLpNorm eb 2 (xLaw M) := by
    calc
      _ ≤ eLpNorm (fun x => ‖eq x‖ + ‖el x‖) 2 (xLaw M) +
          eLpNorm (fun x => ‖eb x‖) 2 (xLaw M) :=
        eLpNorm_add_le (hq.norm.add hl.norm).aestronglyMeasurable
          hb.norm.aestronglyMeasurable (by norm_num : (1 : ENNReal) ≤ 2)
      _ ≤ (eLpNorm (fun x => ‖eq x‖) 2 (xLaw M) +
          eLpNorm (fun x => ‖el x‖) 2 (xLaw M)) +
          eLpNorm (fun x => ‖eb x‖) 2 (xLaw M) :=
        add_le_add (eLpNorm_add_le hq.norm.aestronglyMeasurable
          hl.norm.aestronglyMeasurable (by norm_num : (1 : ENNReal) ≤ 2)) le_rfl
      _ = _ := by simp only [eLpNorm_norm]
  rw [l2Error_eq_eLpNorm M _ _ hh, l2Error_eq_eLpNorm M _ _ hq,
    l2Error_eq_eLpNorm M _ _ hl, l2Error_eq_eLpNorm M _ _ hb]
  have hfin : eLpNorm eq 2 (xLaw M) + eLpNorm el 2 (xLaw M) +
      eLpNorm eb 2 (xLaw M) ≠ ⊤ := by
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr ⟨hq.eLpNorm_ne_top, hl.eLpNorm_ne_top⟩, hb.eLpNorm_ne_top⟩
  calc
    _ ≤ (eLpNorm eq 2 (xLaw M) + eLpNorm el 2 (xLaw M) +
        eLpNorm eb 2 (xLaw M)).toReal := ENNReal.toReal_mono hfin (hmono.trans hsum)
    _ = _ := by
      rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr
        ⟨hq.eLpNorm_ne_top, hl.eLpNorm_ne_top⟩) hb.eLpNorm_ne_top,
        ENNReal.toReal_add hq.eLpNorm_ne_top hl.eLpNorm_ne_top]

-- Componentwise rates of the three affine hinge arguments preserve their
-- quarter rate through the nested maxima, including estimated ties.
-- @node: fitted_hMinus_quarter_rate
/-- For [a valid policy map](hyp:hphi), [admissible reference nuisances](hyp:he0), and [fitted nuisances admissible for every sample and sample size](hyp:heh), at [a level below the level count](hyp:hk) and [a valid positive boundary](hyp:hj), assume square integrability of the errors in [the current pooled argument](hyp:hq), [the preceding pooled argument](hyp:hl), and [the next-level probability minus the full-level term](hyp:hb). If their respective L² errors [for the current argument](hyp:hrq), [for the preceding argument](hyp:hrl), and [for the probability-minus-full-level argument](hyp:hrb) are negligible relative to the full sample size to the power minus one quarter, then [the lower-hinge L² error has that same rate](goal). -/
lemma fitted_hMinus_quarter_rate {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (hq : ∀ n a, MemLp (fun x => pooledQBin phi L (eh n a) k j x -
      pooledQBin phi L e0 k j x) 2 (xLaw M))
    (hl : ∀ n a, MemLp (fun x => pooledQBin phi L (eh n a) k (j-1) x -
      pooledQBin phi L e0 k (j-1) x) 2 (xLaw M))
    (hb : ∀ n a, MemLp (fun x =>
      (positiveValue (eh n a).pLev (k+1) x - binFullJ L (eh n a) k x) -
      (positiveValue e0.pLev (k+1) x - binFullJ L e0 k x)) 2 (xLaw M))
    (hrq : Causalean.Stat.IsLittleOp
      (fun n a => finiteL2Error M (pooledQBin phi L (eh n a) k j) (pooledQBin phi L e0 k j))
      (fun n => ((2 * (n+1) : ℕ) : ℝ) ^ (-1/4 : ℝ)) μ)
    (hrl : Causalean.Stat.IsLittleOp
      (fun n a => finiteL2Error M (pooledQBin phi L (eh n a) k (j-1))
        (pooledQBin phi L e0 k (j-1)))
      (fun n => ((2 * (n+1) : ℕ) : ℝ) ^ (-1/4 : ℝ)) μ)
    (hrb : Causalean.Stat.IsLittleOp
      (fun n a => finiteL2Error M
        (fun x => positiveValue (eh n a).pLev (k+1) x - binFullJ L (eh n a) k x)
        (fun x => positiveValue e0.pLev (k+1) x - binFullJ L e0 k x))
      (fun n => ((2 * (n+1) : ℕ) : ℝ) ^ (-1/4 : ℝ)) μ) :
    Causalean.Stat.IsLittleOp
      (fun n a => finiteL2Error M (hMinus phi L (eh n a) k j) (hMinus phi L e0 k j))
      (fun n => ((2 * (n+1) : ℕ) : ℝ) ^ (-1/4 : ℝ)) μ := by
  have hrpos : ∀ᶠ n : ℕ in atTop, 0 ≤ ((2 * (n+1) : ℕ) : ℝ) ^ (-1/4 : ℝ) :=
    Eventually.of_forall (fun _ => Real.rpow_nonneg (by positivity) _)
  have hs := (hrq.add_eventually_nonneg_rate hrpos hrl).add_eventually_nonneg_rate hrpos hrb
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul one_pos hs
  intro n a
  have hn : 0 ≤ finiteL2Error M (hMinus phi L (eh n a) k j) (hMinus phi L e0 k j) :=
    Real.sqrt_nonneg _
  rw [one_mul, abs_of_nonneg hn]
  exact (fitted_hMinus_l2Error_bound M phi hphi L e0 (eh n a) he0 (heh n a)
    k j hk hj (hq n a) (hl n a) (hb n a)).trans (le_abs_self _)

-- @node: fitted_regular_product_cross_root_n_negligible
/-- For [a valid policy map](hyp:hphi), [admissible reference nuisances](hyp:he0), and [fitted nuisances admissible for every sample and sample size](hyp:heh), at [a level below the level count](hyp:hk) and [a valid positive boundary](hyp:hj), suppose [the lower-hinge L² error](hyp:hr) and [the regular-weight L² error](hyp:hw) are negligible relative to the full sample size to the power minus one quarter. Then [the expected product of these two errors, multiplied by the square root of the evaluation sample size, converges to zero in probability](goal), when the full sample size is twice the evaluation sample size. -/
lemma fitted_regular_product_cross_root_n_negligible {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (hr : Causalean.Stat.IsLittleOp
      (fun n a => finiteL2Error M (hMinus phi L (eh n a) k j) (hMinus phi L e0 k j))
      (fun n => ((2 * (n+1) : ℕ) : ℝ) ^ (-1/4 : ℝ)) μ)
    (hw : Causalean.Stat.IsLittleOp
      (fun n a => finiteL2Error M (regularValue (eh n a).gamma k j) (regularValue e0.gamma k j))
      (fun n => ((2 * (n+1) : ℕ) : ℝ) ^ (-1/4 : ℝ)) μ) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        ∫ x, (regularValue (eh n a).gamma k j x - regularValue e0.gamma k j x) *
          (hMinus phi L (eh n a) k j x - hMinus phi L e0 k j x) ∂xLaw M)
      atTop (fun _ _ => 0) := by
  apply dml_root_n_bias_tendsto_probability
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul one_pos
    (dml_quarter_rate_product μ _ _ hw hr)
  intro n a
  rw [one_mul]
  exact (fitted_regular_product_cross_L2_bound M phi hphi L e0 (eh n a)
    he0 (heh n a) k j hk hj).2.trans (le_abs_self _)

end Papers.TbsPrteOptimalTransport
