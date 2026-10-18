module
public import Papers.TbsPrteOptimalTransport.Helpers.StructuralZeroBranches
public import Papers.TbsPrteOptimalTransport.Helpers.JointResidualEnvelopes
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationBinaryMargins
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationFullJointDerivative
public import Papers.TbsPrteOptimalTransport.Helpers.JointTailPopulation
/-! Simultaneous debiasing at the fixed zero baseline boundary. -/
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

-- Only the upper policy residual survives at the fixed zero boundary.
-- @node: binary_structural_zero_component_mean_remainder_bound
/-- Suppose [the separation constant is positive](hyp:hc), [the reference boundary
is at least that constant](hyp:hbc), and [its distance from the first pooled policy
quantity is at least that constant](hyp:hbq). If [the pooled policy quantity changes
by at most the error allowance](hyp:hq) and [the boundary changes by at most the
same allowance](hyp:hb), [regression and policy residual remainders bounded by their
respective allowances imply that the absolute debiased structural-zero component
error is at most sixteen times the squared error allowance divided by the
separation constant, plus the two residual allowances](goal). -/
lemma binary_structural_zero_component_mean_remainder_bound
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e0 e : NuisanceBin L) (x : X) (err c EB EQ : ℝ)
    (hc : 0 < c)
    (hbc : c ≤ positiveValue e0.pLev 1 x - binFullJ L e0 0 x)
    (hbq : c ≤ |positiveValue e0.pLev 1 x - binFullJ L e0 0 x -
      pooledQBin phi L e0 0 1 x|)
    (hq : |pooledQBin phi L e 0 1 x - pooledQBin phi L e0 0 1 x| ≤ err)
    (hb : |(positiveValue e.pLev 1 x - binFullJ L e 0 x) -
      (positiveValue e0.pLev 1 x - binFullJ L e0 0 x)| ≤ err) :
    let rP := fun i => positiveValue e0.piLev i x *
      (positiveValue e0.P1 i x - positiveValue e.P1 i x) / positiveValue e.piLev i x
    let rp := fun i => positiveValue e0.piLev i x *
      (positiveValue e0.pLev i x - positiveValue e.pLev i x) / positiveValue e.piLev i x
    let Q := ∑ z, instProb M z x * RqBin dphi L e 0 1 (x,z,M.prop z x,0)
    |(rP 1 - rP 0 - rp 1) -
      ((positiveValue e.pLev 1 x - binFullJ L e 0 x) -
        (positiveValue e0.pLev 1 x - binFullJ L e0 0 x))| ≤ EB →
    |Q + (pooledQBin phi L e 0 1 x - pooledQBin phi L e0 0 1 x)| ≤ EQ →
    |hMinus phi L e 0 1 x + binaryRegularRegressionMean phi L e0 e 0 1 x +
      binaryRegularPolicyMean M phi dphi L e 0 1 x - hMinus phi L e0 0 1 x| ≤
      (16 / c) * err ^ 2 + EB + EQ := by
  dsimp only
  intro hrB hrQ
  have hh := binary_structural_zero_debiased_remainder hc hbc hbq hq hb hrB hrQ
  simp only [add_sub_cancel] at hh
  have hzero (e' : NuisanceBin L) : pooledQBin phi L e' 0 0 x = 0 := by
    simp [pooledQBin, positiveValue]
  have hQzero : ∑ z, instProb M z x * RqBin dphi L e 0 0 (x,z,M.prop z x,0) = 0 := by
    simp [RqBin]
  have hvzero (v : PositiveIndex L.K → X → ℝ) : positiveValue v 0 x = 0 := by
    simp [positiveValue]
  convert hh using 1
  congr 1
  simp only [hMinus, binaryRegularRegressionMean, binaryRegularPolicyMean,
    Dbd, Iact, Nat.reduceAdd, Nat.reduceSub, hzero, if_true, hQzero,
    hvzero, zero_mul, zero_div, sub_self, mul_zero, sub_zero]
  ring

-- Admissibility and overlap supply every residual envelope; no analytic
-- hypothesis is added to the population path.
-- @node: population_binary_structural_zero_mean_path_quadratic_envelope
/-- Assume [the policy map is valid](hyp:hphi), [its given derivative is
correct](hyp:hDiff) and [bounded and Lipschitz](hyp:hDerivative), and [the level
ordering is invariant between baseline and policy propensities](hyp:hOrder).
With [baseline overlap](hyp:hov), [policy overlap](hyp:hpol), [an admissible joint
nuisance direction from the truth](hyp:hd), [at least one positive baseline
level](hyp:hk), and [a first policy sublevel at the zero baseline](hyp:hj), if
[the separation constant is positive](hyp:hsep) and [both the structural-zero
boundary and its distance from the first pooled policy quantity are almost surely
at least that constant](hyp:hgap), [there is an integrable covariate envelope
bounding the absolute debiased structural-zero component mean error by the envelope
times the squared path parameter, almost surely for all sufficiently small path
parameters](goal). -/
lemma population_binary_structural_zero_mean_path_quadratic_envelope
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi) (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del))
    (hk : 0 < L.K) (hj : 1 ≤ L.l 0) (sep : ℝ) (hsep : 0 < sep)
    (hgap : ∀ᵐ x ∂xLaw M,
      sep ≤ positiveValue (eta0Bin M L).pLev 1 x - binFullJ L (eta0Bin M L) 0 x ∧
      sep ≤ |positiveValue (eta0Bin M L).pLev 1 x - binFullJ L (eta0Bin M L) 0 x -
        pooledQBin phi L (eta0Bin M L) 0 1 x|) :
    ∃ E : X → ℝ, Integrable E (xLaw M) ∧
      ∀ᶠ t : ℝ in nhds 0, ∀ᵐ x ∂xLaw M,
        let e := eta0Bin M L + t • del
        |hMinus phi L e 0 1 x + binaryRegularRegressionMean phi L (eta0Bin M L) e 0 1 x +
          binaryRegularPolicyMean M phi dphi L e 0 1 x - hMinus phi L (eta0Bin M L) 0 1 x| ≤
          E x * t^2 := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  obtain ⟨EB, EQ, EL, iB, iQ, iL, hres⟩ := population_binary_regular_residual_path_envelopes M
    phi dphi hDiff hDerivative L hOrder cpi hov hpol del hd 0 1 hk.le ⟨le_rfl, hj⟩
  obtain ⟨C, hC, herr⟩ := population_binary_regular_arguments_path_increment_bound M
    phi dphi hphi hDiff hDerivative L del hd 0 1 hk ⟨le_rfl, hj⟩
  refine ⟨fun x => (16 / sep) * C^2 + EB x + EQ x,
    ((integrable_const _).fun_add iB).fun_add iQ, ?_⟩
  filter_upwards [hres, herr] with t htR htE
  filter_upwards [hgap, htR, htE] with x hxG hxR hxE
  have hb := binary_structural_zero_component_mean_remainder_bound M phi dphi L (eta0Bin M L)
    (eta0Bin M L + t • del) x (C * |t|) sep (EB x * t^2) (EQ x * t^2)
    hsep hxG.1 hxG.2 hxE.1 hxE.2.2 hxR.1 hxR.2.1
  refine hb.trans (le_of_eq ?_)
  rw [mul_pow, sq_abs]
  ring

-- The tower identity is applied to the fitted score before the quadratic bound.
-- This leaves only the product-weight/hinge interaction for product assembly.
-- @node: population_binary_structural_zero_component_joint_bias_orthogonality
/-- Under [threshold crossing](hyp:h) and [almost surely binary outcomes](hyp:hy),
assume [a valid policy map](hyp:hphi) with [the given derivative](hyp:hDiff) that is
[bounded and Lipschitz](hyp:hDerivative), [invariant baseline and policy level
ordering](hyp:hOrder), [baseline overlap](hyp:hov), and [policy overlap](hyp:hpol).
For [an admissible joint nuisance direction from the truth](hyp:hd), with [a
positive baseline level](hyp:hk0), [a first policy sublevel at the zero
baseline](hyp:hj0), [a positive separation constant](hyp:hsep), and [almost sure
separation of both the structural-zero boundary and its distance from the first
pooled policy quantity by that constant](hyp:hgap), [the fitted-weighted difference
between the structural-zero component score and its true hinge is integrable
locally along the path, and its population mean has zero derivative at zero](goal). -/
lemma population_binary_structural_zero_component_joint_bias_orthogonality
    (h : ThresholdCrossing M) (hy : OutcomeBinaryAE M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi) (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del))
    (hk0 : 0 < L.K) (hj0 : 1 ≤ L.l 0)
    (sep : ℝ) (hsep : 0 < sep)
    (hgap : ∀ᵐ x ∂xLaw M,
      sep ≤ positiveValue (eta0Bin M L).pLev 1 x - binFullJ L (eta0Bin M L) 0 x ∧
      sep ≤ |positiveValue (eta0Bin M L).pLev 1 x - binFullJ L (eta0Bin M L) 0 x -
        pooledQBin phi L (eta0Bin M L) 0 1 x|) :
    let F := fun (t : ℝ) (o : Obs X Z) =>
      regularValue (eta0Bin M L + t • del).gamma 0 1 o.1 *
        (binScoreComponents phi dphi L (eta0Bin M L + t • del) 0 1 o -
          hMinus phi L (eta0Bin M L) 0 1 o.1)
    (∀ᶠ t : ℝ in nhds 0, Integrable (F t) (observationLaw M)) ∧
      HasDerivAt (fun t : ℝ => ∫ o, F t o ∂observationLaw M) 0 0 := by
  let k : ℕ := 0
  let j : ℕ := 1
  have hk : k < L.K := hk0
  have hj : 1 ≤ j ∧ j ≤ L.l k := ⟨le_rfl, hj0⟩
  dsimp only
  let F := fun (t : ℝ) (o : Obs X Z) =>
    regularValue (eta0Bin M L + t • del).gamma k j o.1 *
      (binScoreComponents phi dphi L (eta0Bin M L + t • del) k j o -
        hMinus phi L (eta0Bin M L) k j o.1)
  obtain ⟨E, iE, hE⟩ := population_binary_structural_zero_mean_path_quadratic_envelope M
    phi dphi hphi hDiff hDerivative L hOrder cpi hov hpol del hd hk0 hj0 sep hsep hgap
  have hobs := M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
  have hmap : (observationLaw M).map Prod.fst = xLaw M := by
    simpa only [observationLaw, xLaw, Function.comp_def] using
      Measure.map_map measurable_fst hobs
  have iEO : Integrable (fun o : Obs X Z => |E o.1|) (observationLaw M) := by
    have ie : Integrable (fun x => |E x|) ((observationLaw M).map Prod.fst) := by
      rw [hmap]
      exact iE.abs
    exact (integrable_map_measure ie.aestronglyMeasurable measurable_fst.aemeasurable).mp ie
  have he0 := binary_admissible_direction_origin M L (eta0Bin M L) del hd
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  have hlocal : ∀ᶠ t : ℝ in nhds 0, Integrable (F t) (observationLaw M) ∧
      |∫ o, F t o ∂observationLaw M| ≤
        (∫ o : Obs X Z, |E o.1| ∂observationLaw M) * t^2 := by
    filter_upwards [hE, population_binary_regular_component_path_local_mean M h
      phi dphi hphi hDiff hDerivative L hOrder cpi hov hpol hy del hd,
      continuousAt_id.abs.eventually_lt_const (by simpa using hr)] with t ht hm htr
    let e := eta0Bin M L + t • del
    let w := regularValue e.gamma k j
    have he := hpath t htr
    let a : RegularIndex L := ⟨(k,j), hk.le, hj⟩
    have hw : Measurable w := by
      change Measurable (regularValue e.gamma k j)
      unfold regularValue
      split_ifs
      · exact (he.2.2.2.2.2.1 _).2
      · fun_prop
    have hwb : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ 1 := by
      filter_upwards [he.2.2.2.2.1 a] with x hx
      change ‖regularValue e.gamma k j x‖ ≤ 1
      simp only [regularValue, dif_pos (show k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from ⟨hk.le,hj⟩)]
      rw [Real.norm_eq_abs, abs_of_nonneg hx.2.1]
      exact hx.2.2
    have ip := binary_weighted_hMinus_integrable_of_admissible M phi hphi L e he
      k j hk hj w hw 1 hwb
    have i0 := binary_weighted_hMinus_integrable_of_admissible M phi hphi L (eta0Bin M L)
      he0 k j hk hj w hw 1 hwb
    have hc := hm k j hk.le
    let R := fun o : Obs X Z => w o.1 *
      (hMinus phi L e k j o.1 + binaryRegularRegressionMean phi L (eta0Bin M L) e k j o.1 +
        binaryRegularPolicyMean M phi dphi L e k j o.1 -
          hMinus phi L (eta0Bin M L) k j o.1)
    have iF : Integrable (F t) (observationLaw M) := by
      convert! (ip.fun_add hc.1).sub' i0 using 1
      funext o
      dsimp only [F, w, e]
      ring
    have iR : Integrable R (observationLaw M) := by
      convert! (ip.fun_add hc.2.1).sub' i0 using 1
      funext o
      dsimp only [R]
      ring
    have heq : (∫ o, F t o ∂observationLaw M) = ∫ o, R o ∂observationLaw M := by
      have hf : F t = fun o : Obs X Z =>
          w o.1 * hMinus phi L e k j o.1 +
            w o.1 * (binScoreComponents phi dphi L e k j o - hMinus phi L e k j o.1) -
              w o.1 * hMinus phi L (eta0Bin M L) k j o.1 := by
        funext o
        dsimp only [F, w, e]
        ring
      rw [hf, integral_sub (ip.fun_add hc.1) i0, integral_add ip hc.1, hc.2.2,
        ← integral_add ip hc.2.1, ← integral_sub (ip.fun_add hc.2.1) i0]
      apply integral_congr_ae
      exact Eventually.of_forall (fun o => by dsimp only [R]; ring)
    have hb : ∀ᵐ o ∂observationLaw M, |R o| ≤ |E o.1| * t^2 := by
      filter_upwards [observationLaw_covariate_ae M _ ht,
        observationLaw_covariate_ae M _ hwb] with o ho hw'
      dsimp only [R]
      rw [abs_mul]
      have hwa : |w o.1| ≤ 1 := by simpa only [Real.norm_eq_abs] using hw'
      calc
        _ ≤ 1 * |hMinus phi L e k j o.1 +
            binaryRegularRegressionMean phi L (eta0Bin M L) e k j o.1 +
            binaryRegularPolicyMean M phi dphi L e k j o.1 -
            hMinus phi L (eta0Bin M L) k j o.1| :=
          mul_le_mul_of_nonneg_right hwa (abs_nonneg _)
        _ ≤ E o.1 * t^2 := by simpa only [one_mul] using ho
        _ ≤ |E o.1| * t^2 := mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg t)
    refine ⟨iF, ?_⟩
    rw [heq]
    calc
      _ ≤ ∫ o, |R o| ∂observationLaw M := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm R
      _ ≤ ∫ o : Obs X Z, |E o.1| * t^2 ∂observationLaw M :=
        integral_mono_ae iR.abs (iEO.mul_const _) hb
      _ = _ := integral_mul_const _ _
  refine ⟨hlocal.mono (fun _ ht => ht.1), ?_⟩
  have hzero : (∫ o, F 0 o ∂observationLaw M) = 0 := by
    apply abs_eq_zero.mp
    have hz := hlocal.self_of_nhds.2
    simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero] at hz
    exact le_antisymm hz (abs_nonneg _)
  have ho : (fun t : ℝ => ∫ o, F t o ∂observationLaw M) =O[nhds 0]
      (fun t : ℝ => t^2) := by
    apply Asymptotics.IsBigO.of_bound (∫ o : Obs X Z, |E o.1| ∂observationLaw M)
    filter_upwards [hlocal] with t ht
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)] using ht.2
  change HasDerivAt (fun t : ℝ => ∫ o, F t o ∂observationLaw M) 0 0
  apply HasDerivAt.of_isLittleO
  simpa only [hzero, smul_zero, sub_zero] using
    ho.trans_isLittleO (Asymptotics.isLittleO_pow_id (𝕜 := ℝ) (by norm_num : 1 < 2))


-- Product inheritance keeps the fitted weight, centers the fitted hinge event,
-- and subtracts the already-controlled weight/hinge error product.
-- @node: population_binary_structural_zero_product_joint_orthogonality_of_margins
/-- Under [threshold crossing](hyp:h) and [almost surely binary outcomes](hyp:hy),
assume [a valid policy map](hyp:hphi) with [the given derivative](hyp:hDiff) that is
[bounded and Lipschitz](hyp:hDerivative), [invariant baseline and policy level
ordering](hyp:hOrder), [baseline overlap](hyp:hov), and [policy overlap](hyp:hpol).
For [an admissible joint nuisance direction from the truth](hyp:hd), with [a
positive baseline level](hyp:hk0), [a first policy sublevel at the zero
baseline](hyp:hj0), [a positive separation constant](hyp:hsep), and [almost sure
separation of both the structural-zero boundary and its distance from the first
pooled policy quantity by that constant](hyp:hgap), [the structural-zero product
score is integrable locally along the joint path and its population mean has zero
derivative at zero](goal). -/
lemma population_binary_structural_zero_product_joint_orthogonality_of_margins
    (h : ThresholdCrossing M) (hy : OutcomeBinaryAE M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi) (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del))
    (hk0 : 0 < L.K) (hj0 : 1 ≤ L.l 0)
    (sep : ℝ) (hsep : 0 < sep)
    (hgap : ∀ᵐ x ∂xLaw M,
      sep ≤ positiveValue (eta0Bin M L).pLev 1 x - binFullJ L (eta0Bin M L) 0 x ∧
      sep ≤ |positiveValue (eta0Bin M L).pLev 1 x - binFullJ L (eta0Bin M L) 0 x -
        pooledQBin phi L (eta0Bin M L) 0 1 x|) :
    (∀ᶠ t : ℝ in nhds 0, Integrable
      (psiProdBin phi dphi L (eta0Bin M L + t • del) 0 1) (observationLaw M)) ∧
    HasDerivAt (fun t : ℝ => ∫ o, psiProdBin phi dphi L
      (eta0Bin M L + t • del) 0 1 o ∂observationLaw M) 0 0 := by
  let k : ℕ := 0
  let j : ℕ := 1
  have hk : k < L.K := hk0
  have hj : 1 ≤ j ∧ j ≤ L.l k := ⟨le_rfl, hj0⟩
  haveI : IsFiniteMeasure (observationLaw M) := by unfold observationLaw; infer_instance
  let F := fun (t : ℝ) (o : Obs X Z) =>
    regularValue (eta0Bin M L + t • del).gamma k j o.1 *
      (binScoreComponents phi dphi L (eta0Bin M L + t • del) k j o -
        hMinus phi L (eta0Bin M L) k j o.1)
  let C := fun (t : ℝ) (x : X) =>
    (regularValue (eta0Bin M L + t • del).gamma k j x -
      regularValue (eta0Bin M L).gamma k j x) *
    (hMinus phi L (eta0Bin M L + t • del) k j x - hMinus phi L (eta0Bin M L) k j x)
  have hF := population_binary_structural_zero_component_joint_bias_orthogonality M h hy phi dphi
    hphi hDiff hDerivative L hOrder cpi hov hpol del hd hk0 hj0 sep hsep hgap
  have hC := population_binary_hinge_weight_interaction_orthogonality M phi dphi hphi
    hDiff hDerivative L del hd k j hk hj
  have he0 := binary_admissible_direction_origin M L (eta0Bin M L) del hd
  let a : RegularIndex L := ⟨(k,j), hk.le, hj⟩
  have hv (e : NuisanceBin L) : regularValue e.gamma k j = e.gamma a := by
    funext x
    simp only [regularValue, dif_pos (show k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from ⟨hk.le,hj⟩)]
    rfl
  have hg0 : regularValue (eta0Bin M L).gamma k j = gamma M L k j := by
    rw [hv]
    rfl
  have hm (e : NuisanceBin L) (he : BinAdmissible M L e) :
      Measurable (regularValue e.gamma k j) ∧
      ∀ᵐ x ∂xLaw M, ‖regularValue e.gamma k j x‖ ≤ 1 := by
    rw [hv]
    refine ⟨(he.2.2.2.2.2.1 a).2, ?_⟩
    filter_upwards [he.2.2.2.2.1 a] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx.2.1]
    exact hx.2.2
  have h0 := hm (eta0Bin M L) he0
  have iT := binary_weighted_hMinus_integrable_of_admissible M phi hphi L (eta0Bin M L)
    he0 k j hk hj _ h0.1 1 h0.2
  let target := ∫ o : Obs X Z, regularValue (eta0Bin M L).gamma k j o.1 *
    hMinus phi L (eta0Bin M L) k j o.1 ∂observationLaw M
  have hmap : (observationLaw M).map Prod.fst = xLaw M := by
    simpa only [observationLaw, xLaw, Function.comp_def] using Measure.map_map measurable_fst
      (M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY)))
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  have hlocal : ∀ᶠ t : ℝ in nhds 0,
      Integrable (psiProdBin phi dphi L (eta0Bin M L + t • del) k j) (observationLaw M) ∧
      (∫ o, psiProdBin phi dphi L (eta0Bin M L + t • del) k j o ∂observationLaw M) =
        (∫ o, F t o ∂observationLaw M) - (∫ x, C t x ∂xLaw M) + target := by
    filter_upwards [hF.1, continuousAt_id.abs.eventually_lt_const (by simpa using hr)]
      with t iF htr
    let e := eta0Bin M L + t • del
    have he := hpath t htr
    have ht := hm e he
    let w := fun x => regularValue e.gamma k j x - regularValue (eta0Bin M L).gamma k j x
    have hw : Measurable w := by first | fun_prop | exact ht.1.sub h0.1
    have hwb : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ 2 := by
      filter_upwards [ht.2, h0.2] with x hx hy
      exact (norm_sub_le _ _).trans (by linarith)
    have i1 := binary_weighted_hMinus_integrable_of_admissible M phi hphi L e he
      k j hk hj w hw 2 hwb
    have i0 := binary_weighted_hMinus_integrable_of_admissible M phi hphi L (eta0Bin M L)
      he0 k j hk hj w hw 2 hwb
    have iCo : Integrable (fun o : Obs X Z => C t o.1) (observationLaw M) := by
      simpa only [C, w, e, mul_sub] using i1.sub' i0
    obtain ⟨H0, hm0, heq0⟩ := binary_hMinus_measurable_version M phi hphi L (eta0Bin M L) he0 k j
    obtain ⟨Ht, hmt, heqt⟩ := binary_hMinus_measurable_version M phi hphi L e he k j
    have hcm : AEStronglyMeasurable (C t) (xLaw M) := by
      have hv : Measurable (fun x => w x * (Ht x - H0 x)) := by fun_prop
      apply hv.aestronglyMeasurable.congr
      filter_upwards [heqt, heq0] with x hxt hx0
      simp only [C, w, e, hxt, hx0]
    have hci : (∫ o : Obs X Z, C t o.1 ∂observationLaw M) = ∫ x, C t x ∂xLaw M := by
      rw [← hmap]
      exact (integral_map measurable_fst.aemeasurable (by rwa [hmap])).symm
    obtain ⟨iCenter, hCenter⟩ := population_binary_fitted_hinge_event_centering M
      phi hphi L e he he0 k j hk hj
    have hid : (fun o => psiProdBin phi dphi L e k j o -
        regularValue (eta0Bin M L).gamma k j o.1 * hMinus phi L (eta0Bin M L) k j o.1) =
        (fun o => F t o + hMinus phi L e k j o.1 *
          (indicator (o.2.1 ∈ policyUnion L k j) - gamma M L k j o.1) - C t o.1) := by
      funext o
      dsimp only [F, C]
      rw [hg0]
      exact binary_regular_product_bias_decomposition M phi dphi L e k j o
    have iBias := (iF.fun_add iCenter).sub' iCo
    rw [← hid] at iBias
    have iScore : Integrable (psiProdBin phi dphi L e k j) (observationLaw M) := by
      convert! iBias.fun_add iT using 1
      funext o
      ring
    refine ⟨iScore, ?_⟩
    have heq := integral_congr_ae (μ := observationLaw M) (Eventually.of_forall (congrFun hid))
    rw [integral_sub iScore iT, integral_sub (iF.fun_add iCenter) iCo,
      integral_add iF iCenter, hCenter, add_zero, hci] at heq
    change (∫ o, psiProdBin phi dphi L e k j o ∂observationLaw M) = _
    dsimp only [target]
    linarith
  refine ⟨hlocal.mono (fun _ ht => ht.1), ?_⟩
  have hder : HasDerivAt (fun t : ℝ =>
      (∫ o, F t o ∂observationLaw M) - (∫ x, C t x ∂xLaw M) + target) 0 0 := by
    simpa only [Pi.sub_apply, sub_self] using (hF.2.sub hC).add_const target
  apply hder.congr_of_eventuallyEq
  exact hlocal.mono (fun _ ht => ht.2)

-- The normalized binary gap has mean at most one. At k = 0 its
-- propensity width is p_1, giving a nonnegative outcome boundary.
-- @node: population_binary_structural_zero_boundary_nonneg
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[a finite reduction of the instrument](hyp:hf), and [almost surely binary
outcomes](hyp:hy), if [the baseline and comparison propensities have invariant level
ordering](hyp:hOrder) and [there is a positive baseline level](hyp:hk), [the first
true baseline propensity minus the full binary outcome contrast at the zero
baseline is nonnegative for almost every covariate value](goal). -/
lemma population_binary_structural_zero_boundary_nonneg
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (hf : InstrumentFiniteReduction Z) (hy : OutcomeBinaryAE M)
    (q : Z → X → ℝ) (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop q L) (hk : 0 < L.K) :
    ∀ᵐ x ∂xLaw M,
      0 ≤ positiveValue (eta0Bin M L).pLev 1 x - binFullJ L (eta0Bin M L) 0 x := by
  filter_upwards [discrete_gap_law_binary_supported M h hf hy q L hOrder,
    population_binary_full_contrast_eq_Jfull M h he hf q L hOrder 0 hk] with x hs hfull
  let ν := discreteGapLaw M L 0 x
  haveI : IsProbabilityMeasure ν := discrete_gap_law_probability M M.prop q L hOrder 0 hk x
  have hae : ∀ᵐ y ∂ν, y = 0 ∨ y = 1 := by
    have hm : MeasurableSet ({0, 1} : Set ℝ) := by measurability
    have hh := (ae_iff.mpr (hs 0 hk))
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hh
  have hi : Integrable (fun y : ℝ => y) ν := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [hae] with y hy
    rcases hy with rfl | rfl <;> norm_num
  have hm : (∫ y : ℝ, y ∂ν) ≤ 1 := by
    calc
      _ ≤ ∫ _ : ℝ, (1 : ℝ) ∂ν := integral_mono_ae hi (integrable_const _) (by
        filter_upwards [hae] with y hy
        rcases hy with rfl | rfl <;> norm_num)
      _ = 1 := by simp
  rw [population_binary_baseline_value M q L hOrder 1 (by omega), hfull, Jfull,
    hOrder.1 x 0 (by omega)]
  have hp0 : pLevel (finiteLevels (fun z => M.prop z x)) 0 = 0 := by simp [pLevel]
  rw [hp0, sub_zero]
  have hp : 0 ≤ L.pLev 1 x :=
    (hOrder.2.2.2.2.2.2.2.2.2.2.1 x 1 (by omega)).1
  exact sub_nonneg.mpr (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hm hp)

-- @node: population_binary_structural_zero_joint_margins
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[a finite reduction of the instrument](hyp:hf), and [almost surely binary
outcomes](hyp:hy), assume [invariant baseline and policy level ordering](hyp:hOrder),
[policy overlap](hyp:hpol), and [a discrete outcome gap witnessed by the specified
margin](hyp:hOutcome). If [there is a positive baseline level](hyp:hk) and [a first
policy sublevel at the zero baseline](hyp:hj), [both the structural-zero boundary
and its absolute distance from the first pooled policy quantity are at least the
outcome-gap margin for almost every covariate value](goal). -/
lemma population_binary_structural_zero_joint_margins
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (hf : InstrumentFiniteReduction Z) (hy : OutcomeBinaryAE M)
    (phi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hpol : PolicyOverlap M L cpi) (ch : ℝ)
    (hOutcome : DiscreteOutcomeGapWitness M L ch) (hk : 0 < L.K) (hj : 1 ≤ L.l 0) :
    ∀ᵐ x ∂xLaw M,
      ch ≤ positiveValue (eta0Bin M L).pLev 1 x - binFullJ L (eta0Bin M L) 0 x ∧
      ch ≤ |positiveValue (eta0Bin M L).pLev 1 x - binFullJ L (eta0Bin M L) 0 x -
        pooledQBin phi L (eta0Bin M L) 0 1 x| := by
  filter_upwards [population_binary_regression_endpoint_margins M h he hf phi L hOrder
    cpi hpol ch hOutcome 0 1 hk ⟨le_rfl, hj⟩,
    population_binary_structural_zero_boundary_nonneg M h he hf hy _ L hOrder hk]
    with x hm hn
  have hz : pooledQBin phi L (eta0Bin M L) 0 0 x = 0 := by simp [pooledQBin, positiveValue]
  simpa only [Nat.reduceAdd, Nat.reduceSub, hz, sub_zero, abs_of_nonneg hn] using hm

-- @node: population_binary_structural_zero_product_joint_orthogonality_of_gap
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[a finite reduction of the instrument](hyp:hf), and [almost surely binary
outcomes](hyp:hy), assume [a valid policy map](hyp:hphi) with [the given
derivative](hyp:hDiff) that is [bounded and Lipschitz](hyp:hDerivative), [invariant
baseline and policy level ordering](hyp:hOrder), [baseline overlap](hyp:hov),
[policy overlap](hyp:hpol), and [a discrete outcome gap](hyp:hOutcome). For [an
admissible joint nuisance direction from the truth](hyp:hd), if [there is a positive
baseline level](hyp:hk) and [a first policy sublevel at the zero baseline](hyp:hj),
[the structural-zero product score is integrable locally along the joint path and
its population mean has zero derivative at zero](goal). -/
lemma population_binary_structural_zero_product_joint_orthogonality_of_gap
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (hf : InstrumentFiniteReduction Z) (hy : OutcomeBinaryAE M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi) (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hOutcome : DiscreteOutcomeGap M L) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del))
    (hk : 0 < L.K) (hj : 1 ≤ L.l 0) :
    (∀ᶠ t : ℝ in nhds 0, Integrable
      (psiProdBin phi dphi L (eta0Bin M L + t • del) 0 1) (observationLaw M)) ∧
    HasDerivAt (fun t : ℝ => ∫ o, psiProdBin phi dphi L
      (eta0Bin M L + t • del) 0 1 o ∂observationLaw M) 0 0 := by
  obtain ⟨ch, hch, hmargin⟩ := hOutcome
  exact population_binary_structural_zero_product_joint_orthogonality_of_margins M
    h.2.2.2.1 hy phi dphi hphi hDiff hDerivative L hOrder cpi hov hpol del hd hk hj ch hch
    (population_binary_structural_zero_joint_margins M h he hf hy phi L hOrder cpi hpol
      ch ⟨hch, hmargin⟩ hk hj)
-- Finite summation combines the regular, fixed-zero, full, and tail paths.
-- @node: population_binary_total_joint_orthogonality_of_gap
/-- Under [the structural assumptions](hyp:h), [known outcome endpoints](hyp:he),
[a finite reduction of the instrument](hyp:hf), and [almost surely binary
outcomes](hyp:hy), assume [a valid policy map](hyp:hphi) with [the given
derivative](hyp:hDiff) that is [bounded and Lipschitz](hyp:hDerivative), [at least
one positive baseline level](hyp:hK), [invariant baseline and policy level
ordering](hyp:hOrder), [policy levels off the boundaries](hyp:hOff), [a witnessed
separation of propensity gaps](hyp:hGap), [baseline overlap](hyp:hov), [policy
overlap](hyp:hpol), and [a discrete outcome gap](hyp:hOutcome). For [an admissible
joint nuisance direction from the truth](hyp:hd), [the population mean of the total
binary score has zero derivative at zero along the joint nuisance path](goal). -/
lemma population_binary_total_joint_orthogonality_of_gap
    (h : StructuralAssumptions M) (he : OutcomeEndpointsKnown M)
    (hf : InstrumentFiniteReduction Z) (hy : OutcomeBinaryAE M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi) (L : LevelData Z X)
    (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (hOff : PolicyLevelOffBoundary L) (gap : ℝ)
    (hGap : PropensityGapSeparationWitness M.prop (policyProp phi M.prop) gap)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hpol : PolicyOverlap M L cpi)
    (hOutcome : DiscreteOutcomeGap M L) (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del)) :
    HasDerivAt (fun t : ℝ => ∫ o, psiBin M phi dphi L hK o
      (eta0Bin M L + t • del) ∂observationLaw M) 0 0 := by
  have hr : ∀ k ∈ Finset.range L.K, ∀ j ∈ Finset.Icc 1 (L.l k),
      (∀ᶠ t : ℝ in nhds 0, Integrable
        (psiProdBin phi dphi L (eta0Bin M L + t • del) k j) (observationLaw M)) ∧
      HasDerivAt (fun t : ℝ => ∫ o, psiProdBin phi dphi L
        (eta0Bin M L + t • del) k j o ∂observationLaw M) 0 0 := by
    intro k hk j hj
    have hk' := Finset.mem_range.mp hk
    have hj' := Finset.mem_Icc.mp hj
    by_cases hz : k = 0 ∧ j = 1
    · rcases hz with ⟨rfl, rfl⟩
      exact population_binary_structural_zero_product_joint_orthogonality_of_gap M h he hf hy
        phi dphi hphi hDiff hDerivative L hOrder cpi hov hpol hOutcome del hd hk' hj'.2
    · exact population_binary_regular_product_joint_orthogonality_of_gap M h he hf hy
        phi dphi hphi hDiff hDerivative L hOrder hOff gap hGap cpi hov hpol hOutcome del hd
        k j hk' hj' (by tauto)
  have ireg : ∀ᶠ t : ℝ in nhds 0, ∀ k ∈ Finset.range L.K,
      ∀ j ∈ Finset.Icc 1 (L.l k), Integrable
        (psiProdBin phi dphi L (eta0Bin M L + t • del) k j) (observationLaw M) := by
    apply (eventually_all_finset _).2
    intro k hk
    apply (eventually_all_finset _).2
    intro j hj
    exact (hr k hk j hj).1
  have ifull : ∀ᶠ t : ℝ in nhds 0, ∀ k ∈ Finset.range L.K,
      Integrable (psiFullProdBin L (eta0Bin M L + t • del) k) (observationLaw M) := by
    apply (eventually_all_finset _).2
    intro k hk
    exact (population_binary_full_joint_path_local_mean_of_admissible M L cpi hov hy del hd
      ⟨k, Finset.mem_range.mp hk⟩).mono (fun _ ht => ht.1)
  have hfder := population_binary_full_sum_joint_orthogonality_of_admissible M L cpi hov hy del hd
  have hrder := HasDerivAt.fun_sum (fun k hk => HasDerivAt.fun_sum
    (fun j hj => (hr k hk j hj).2))
  have htder := population_binary_tail_joint_orthogonality_of_admissible M h.2.2.2.1
    phi dphi hphi hDiff hDerivative L hK hOrder cpi hov del hd
  have hder : HasDerivAt (fun t : ℝ =>
      (∫ o, ∑ k ∈ Finset.range L.K, psiFullProdBin L (eta0Bin M L + t • del) k o
        ∂observationLaw M) +
      (∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
        ∫ o, psiProdBin phi dphi L (eta0Bin M L + t • del) k j o ∂observationLaw M) +
      (∫ o, commonTailScore M phi dphi L (eta0Bin M L + t • del).prop
        (eta0Bin M L + t • del).pLev (eta0Bin M L + t • del).piLev
        (eta0Bin M L + t • del).gammaTail o ∂observationLaw M)) 0 0 := by
    convert! (hfder.add hrder).add htder using 1 <;>
      simp only [Finset.sum_const_zero, add_zero, Pi.add_apply]
  apply hder.congr_of_eventuallyEq
  filter_upwards [ireg, ifull, population_binary_tail_joint_path_integrable_of_admissible M
    phi dphi hphi hDiff hDerivative L hK cpi hov del hd] with t ir iff it
  have ifs := integrable_finsetSum _ iff
  have irs := integrable_finsetSum _ (fun k hk => integrable_finsetSum _ (ir k hk))
  have hid : (fun o => psiBin M phi dphi L hK o (eta0Bin M L + t • del)) =
      (fun o => (∑ k ∈ Finset.range L.K, psiFullProdBin L (eta0Bin M L + t • del) k o) +
        (∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
          psiProdBin phi dphi L (eta0Bin M L + t • del) k j o) +
        commonTailScore M phi dphi L (eta0Bin M L + t • del).prop
          (eta0Bin M L + t • del).pLev (eta0Bin M L + t • del).piLev
          (eta0Bin M L + t • del).gammaTail o) := by
    funext o
    simp only [psiBin, Finset.sum_add_distrib]
  rw [hid, integral_add (ifs.fun_add irs) it, integral_add ifs irs,
    integral_finsetSum _ (fun k hk => integrable_finsetSum _ (ir k hk))]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  exact integral_finsetSum _ (ir k hk)

end Papers.TbsPrteOptimalTransport
