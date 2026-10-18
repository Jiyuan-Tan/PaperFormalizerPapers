module
public import Papers.TbsPrteOptimalTransport.Helpers.WeightedFittedTreatment
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationBinaryComponents
/-! Joint fitted regression and assignment means for the binary regular-interval corrections. -/
@[expose] public section
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

-- The four regression corrections in the actual regular component score.
-- @node: binaryRegularRegressionCorrection
/-- For [a policy map](hyp:phi), [treatment and policy level data](hyp:L), [a fitted
binary nuisance](hyp:e), [a treatment interval k](hyp:k), [a policy index j](hyp:j), and
[an observation](hyp:o), [the regular binary regression correction](goal) is the
boundary-branch-weighted difference of adjacent outcome residuals minus the corresponding
upper propensity residual and, when j is one, the active lower-branch propensity residual. -/
noncomputable def binaryRegularRegressionCorrection
    (phi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e : NuisanceBin L)
    (k j : ℕ) (o : Obs X Z) : ℝ :=
  Dbd phi L e k j o.1 * (RP L e (k+1) o - RP L e k o) -
    Dbd phi L e k j o.1 * Rp L e (k+1) o -
    (if j = 1 then Edom phi L e k j o.1 * Iact phi L e k j o.1 * Rp L e k o else 0)

-- Conditional residual means retain the true assignment mass and fitted denominator.
-- @node: binaryRegularRegressionMean
/-- For [a policy](hyp:phi), [level data](hyp:L), [a reference binary nuisance](hyp:e0),
[a fitted binary nuisance](hyp:e), [a treatment interval k](hyp:k), [a policy index j](hyp:j),
and [covariates x](hyp:x), [the regular regression correction mean](goal) is obtained by
[forming outcome regression differences weighted by reference assignment masses and
divided by fitted assignment masses](step:1), [forming the analogous propensity regression
differences](step:2), and [combining their adjacent-level differences with the fitted
boundary and active lower-branch indicators, including the lower propensity term only when j is one](step:3). -/
noncomputable def binaryRegularRegressionMean
    (phi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e0 e : NuisanceBin L)
    (k j : ℕ) (x : X) : ℝ :=
  let rP := fun i => positiveValue e0.piLev i x *
    (positiveValue e0.P1 i x - positiveValue e.P1 i x) / positiveValue e.piLev i x
  let rp := fun i => positiveValue e0.piLev i x *
    (positiveValue e0.pLev i x - positiveValue e.pLev i x) / positiveValue e.piLev i x
  Dbd phi L e k j x * (rP (k+1) - rP k) - Dbd phi L e k j x * rp (k+1) -
    (if j = 1 then Edom phi L e k j x * Iact phi L e k j x * rp k else 0)

-- @node: binScoreComponents_regression_correction_decomposition
/-- [The binary regular component score equals the fitted negative hinge plus the
regression correction and the active upper policy correction, minus the active
lower-branch policy correction](goal). -/
lemma binScoreComponents_regression_correction_decomposition
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e : NuisanceBin L)
    (k j : ℕ) (o : Obs X Z) :
    binScoreComponents phi dphi L e k j o =
      hMinus phi L e k j o.1 + binaryRegularRegressionCorrection phi L e k j o +
      Iact phi L e k j o.1 * RqBin dphi L e k j o -
      Edom phi L e k j o.1 * Iact phi L e k j o.1 * RqBin dphi L e k (j-1) o := by
  unfold binScoreComponents binaryRegularRegressionCorrection
  ring

-- @node: binary_pooledQBin_measurable_of_pointwise_range
/-- If [the policy map is admissible](hyp:hphi), [each fitted propensity is measurable](hyp:hp)
and [takes values in the unit interval everywhere](hyp:hr), and [the treatment-level
propensities](hyp:hl) and [instrument pooling shares](hyp:hs) are measurable, [every
pooled binary policy endpoint is measurable](goal). -/
@[fun_prop] lemma binary_pooledQBin_measurable_of_pointwise_range
    (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e : NuisanceBin L)
    (hp : ∀ z, Measurable (e.prop z)) (hr : ∀ z x, e.prop z x ∈ Icc (0 : ℝ) 1)
    (hl : ∀ a, Measurable (e.pLev a)) (hs : ∀ a z, Measurable (e.share a z))
    (k j : ℕ) : Measurable (pooledQBin phi L e k j) := by
  first
  | fun_prop
  | have hpos i : Measurable (positiveValue e.pLev i) := by
      unfold positiveValue
      split_ifs
      · exact hl _
      · fun_prop
    unfold pooledQBin
    split_ifs
    · exact hpos k
    · exact hpos (k+1)
    · apply Finset.measurable_sum
      intro z hz
      have hpol : Measurable (fun x => phi z x (e.prop z x)) :=
        hphi.1.comp (measurable_const.prodMk
          (measurable_id.prodMk ((hp z).subtype_mk (h := hr z))))
      exact (hs _ z).mul hpol
    · simp only [zero_mul, Finset.sum_const_zero]
      fun_prop

variable (M : LatentIVModel Ω X Z)

-- Every fitted branch coefficient is bounded by one, including at ties.
-- The tower identities therefore apply with moving branches and product weights.
-- @node: population_binary_regular_regression_correction_fitted_mean
/-- Under [threshold crossing](hyp:h), [invariant level ordering](hyp:hOrder),
[baseline overlap with constant cpi](hyp:hov), [binary outcomes almost surely](hyp:hy),
and [admissible true](hyp:he0) and [fitted binary nuisances](hyp:he), suppose [c is positive](hyp:hc)
and [all fitted assignment masses are at least c almost everywhere](hyp:hden).
If [the covariate weight is measurable](hyp:hw) and [bounded in norm by B almost everywhere](hyp:hwB),
and [the fitted boundary indicator](hyp:hD), [lower-dominance indicator](hyp:hE), and
[active indicator](hyp:hI) are measurable, [the weighted regression correction and its
reference-assignment-weighted regression mean are integrable under the observation law
and have equal integrals](goal). -/
lemma population_binary_regular_regression_correction_fitted_mean
    (h : ThresholdCrossing M) (phi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hy : OutcomeBinaryAE M)
    (he0 : BinAdmissible M L (eta0Bin M L)) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (c : ℝ) (hc : 0 < c)
    (hden : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ e.piLev a x)
    (k j : ℕ) (w : X → ℝ) (hw : Measurable w) (B : ℝ)
    (hwB : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ B)
    (hD : Measurable (Dbd phi L e k j))
    (hE : Measurable (Edom phi L e k j))
    (hI : Measurable (Iact phi L e k j)) :
    Integrable (fun o : Obs X Z => w o.1 * binaryRegularRegressionCorrection phi L e k j o)
      (observationLaw M) ∧
    Integrable (fun o : Obs X Z => w o.1 *
      binaryRegularRegressionMean phi L (eta0Bin M L) e k j o.1) (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 * binaryRegularRegressionCorrection phi L e k j o
      ∂observationLaw M) =
      ∫ o : Obs X Z, w o.1 * binaryRegularRegressionMean phi L (eta0Bin M L) e k j o.1
        ∂observationLaw M := by
  let D := Dbd phi L e k j
  let E := Edom phi L e k j
  let I := Iact phi L e k j
  have hDb : ∀ x, ‖D x‖ ≤ 1 := by
    intro x
    unfold D Dbd indicator
    split_ifs <;> norm_num
  have hEIb : ∀ x, ‖E x * I x‖ ≤ 1 := by
    intro x
    unfold E I Edom Iact indicator
    split_ifs <;> norm_num
  have hwd : Measurable (fun x => w x * D x) := hw.mul hD
  have hwei : Measurable (fun x => w x * (E x * I x)) := hw.mul (hE.mul hI)
  have hwdb : ∀ᵐ x ∂xLaw M, ‖w x * D x‖ ≤ B := by
    filter_upwards [hwB] with x hx
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hDb x) (norm_nonneg _)).trans (by simpa using hx)
  have hweib : ∀ᵐ x ∂xLaw M, ‖w x * (E x * I x)‖ ≤ B := by
    filter_upwards [hwB] with x hx
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hEIb x) (norm_nonneg _)).trans (by simpa using hx)
  have hP i := population_RP_weighted_mean_of_binary_admissible M L cpi hov hy he0
    e he c hc hden (fun x => w x * D x) hwd B hwdb i
  have hp := population_Rp_weighted_mean_of_binary_admissible M L cpi hov h
    (policyProp phi M.prop) hOrder he0 e he c hc hden
      (fun x => w x * D x) hwd B hwdb (k+1)
  have hl := population_Rp_weighted_mean_of_binary_admissible M L cpi hov h
    (policyProp phi M.prop) hOrder he0 e he c hc hden
      (fun x => w x * (E x * I x)) hwei B hweib k
  let f := fun o : Obs X Z => if j = 1 then (w o.1 * (E o.1 * I o.1)) * Rp L e k o else 0
  let g := fun o : Obs X Z => if j = 1 then
    w o.1 * (E o.1 * I o.1) * positiveValue (eta0Bin M L).piLev k o.1 *
      (positiveValue (eta0Bin M L).pLev k o.1 - positiveValue e.pLev k o.1) /
        positiveValue e.piLev k o.1 else 0
  have fi : Integrable f (observationLaw M) := by
    dsimp only [f]
    split_ifs
    · exact hl.1
    · exact integrable_zero _ _ _
  have gi : Integrable g (observationLaw M) := by
    dsimp only [g]
    split_ifs
    · exact hl.2.1
    · exact integrable_zero _ _ _
  have fg : (∫ o, f o ∂observationLaw M) = ∫ o, g o ∂observationLaw M := by
    dsimp only [f, g]
    split_ifs
    · exact hl.2.2
    · rfl
  have feq : (fun o : Obs X Z => w o.1 * binaryRegularRegressionCorrection phi L e k j o) =
      (fun o => (w o.1 * D o.1) * RP L e (k+1) o -
        (w o.1 * D o.1) * RP L e k o - (w o.1 * D o.1) * Rp L e (k+1) o - f o) := by
    funext o
    dsimp only [binaryRegularRegressionCorrection, D, E, I, f]
    split_ifs <;> ring
  have geq : (fun o : Obs X Z => w o.1 *
      binaryRegularRegressionMean phi L (eta0Bin M L) e k j o.1) =
      (fun o => w o.1 * D o.1 * positiveValue (eta0Bin M L).piLev (k+1) o.1 *
          (positiveValue (eta0Bin M L).P1 (k+1) o.1 - positiveValue e.P1 (k+1) o.1) /
            positiveValue e.piLev (k+1) o.1 -
        w o.1 * D o.1 * positiveValue (eta0Bin M L).piLev k o.1 *
          (positiveValue (eta0Bin M L).P1 k o.1 - positiveValue e.P1 k o.1) /
            positiveValue e.piLev k o.1 -
        w o.1 * D o.1 * positiveValue (eta0Bin M L).piLev (k+1) o.1 *
          (positiveValue (eta0Bin M L).pLev (k+1) o.1 - positiveValue e.pLev (k+1) o.1) /
            positiveValue e.piLev (k+1) o.1 - g o) := by
    funext o
    dsimp only [binaryRegularRegressionMean, D, E, I, g]
    split_ifs <;> ring
  rw [feq, geq]
  refine ⟨(((hP (k+1)).1.sub' (hP k).1).sub' hp.1).sub' fi,
    (((hP (k+1)).2.1.sub' (hP k).2.1).sub' hp.2.1).sub' gi, ?_⟩
  rw [integral_sub (((hP (k+1)).1.sub' (hP k).1).sub' hp.1) fi,
    integral_sub ((hP (k+1)).1.sub' (hP k).1) hp.1,
    integral_sub (hP (k+1)).1 (hP k).1,
    integral_sub (((hP (k+1)).2.1.sub' (hP k).2.1).sub' hp.2.1) gi,
    integral_sub ((hP (k+1)).2.1.sub' (hP k).2.1) hp.2.1,
    integral_sub (hP (k+1)).2.1 (hP k).2.1,
    (hP (k+1)).2.2, (hP k).2.2, hp.2.2, fg]

-- Clipping changes only null-set values. It supplies pointwise range for the
-- policy map, so branch measurability is derived rather than postulated.
-- @node: population_binary_regular_regression_correction_mean_of_admissible
/-- Under [threshold crossing](hyp:h), [an admissible policy](hyp:hphi), [invariant
level ordering](hyp:hOrder), [baseline overlap with constant cpi](hyp:hov), [binary
outcomes almost surely](hyp:hy), and [admissible true](hyp:he0) and [fitted binary nuisances](hyp:he),
suppose [c is positive](hyp:hc) and [all fitted assignment masses are at least c almost
everywhere](hyp:hden). For [a measurable weight](hyp:hw) whose [norm is bounded by B
almost everywhere](hyp:hwB), [the weighted regression correction and the corresponding
regression mean are integrable under the observation law and have equal integrals](goal). -/
lemma population_binary_regular_regression_correction_mean_of_admissible
    (h : ThresholdCrossing M) (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hy : OutcomeBinaryAE M)
    (he0 : BinAdmissible M L (eta0Bin M L)) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (c : ℝ) (hc : 0 < c)
    (hden : ∀ a, ∀ᵐ x ∂xLaw M, c ≤ e.piLev a x)
    (k j : ℕ) (w : X → ℝ) (hw : Measurable w) (B : ℝ)
    (hwB : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ B) :
    Integrable (fun o : Obs X Z => w o.1 * binaryRegularRegressionCorrection phi L e k j o)
      (observationLaw M) ∧
    Integrable (fun o : Obs X Z => w o.1 *
      binaryRegularRegressionMean phi L (eta0Bin M L) e k j o.1) (observationLaw M) ∧
    (∫ o : Obs X Z, w o.1 * binaryRegularRegressionCorrection phi L e k j o
      ∂observationLaw M) =
      ∫ o : Obs X Z, w o.1 * binaryRegularRegressionMean phi L (eta0Bin M L) e k j o.1
        ∂observationLaw M := by
  let pc := fun z x => max 0 (min 1 (e.prop z x))
  let ep : NuisanceBin L := {e with prop := pc}
  have hpc z : Measurable (pc z) := by
    have hm := he.2.1 z
    dsimp only [pc]
    fun_prop
  have hpcR : ∀ z x, pc z x ∈ Icc (0 : ℝ) 1 := fun z x =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hep : BinAdmissible M L ep :=
    ⟨fun z => Eventually.of_forall (hpcR z), hpc, he.2.2⟩
  have hq i := binary_pooledQBin_measurable_of_pointwise_range phi hphi L ep
    hpc hpcR (fun a => (he.2.2.2.1 a).1) (he.2.2.2.2.2.2.2.1) k i
  have hpos i : Measurable (positiveValue ep.pLev i) := by
    unfold positiveValue
    split_ifs
    · exact (he.2.2.2.1 _).1
    · fun_prop
  have hP i : Measurable (positiveValue ep.P1 i) := by
    unfold positiveValue
    split_ifs
    · exact (he.2.2.2.1 _).2.1
    · fun_prop
  have hb : Measurable (fun x => positiveValue ep.pLev (k+1) x - binFullJ L ep k x) := by
    first
    | fun_prop
    | exact (hpos (k+1)).sub ((hP (k+1)).sub (hP k))
  have hD := binary_Dbd_measurable phi L ep k j (hq j) (hq (j-1)) hb
  have hE := binary_Edom_measurable phi L ep k j (hq (j-1)) hb
  have hI := binary_Iact_measurable phi L ep k j (hq j) (hq (j-1)) hb
  have hm := population_binary_regular_regression_correction_fitted_mean M h phi L hOrder
    cpi hov hy he0 ep hep c hc hden k j w hw B hwB hD hE hI
  have heq : ∀ᵐ x ∂xLaw M, ∀ i,
      pooledQBin phi L ep k i x = pooledQBin phi L e k i x := by
    filter_upwards [ae_all_iff.mpr he.1] with x hx
    intro i
    simp only [pooledQBin, ep]
    split_ifs
    · rfl
    · rfl
    · apply Finset.sum_congr rfl
      intro z hz
      simp only [pc, min_eq_right (hx z).2, max_eq_right (hx z).1]
    · simp only [zero_mul, Finset.sum_const_zero]
  have hcoeff : ∀ᵐ x ∂xLaw M,
      Dbd phi L ep k j x = Dbd phi L e k j x ∧
      Edom phi L ep k j x = Edom phi L e k j x ∧
      Iact phi L ep k j x = Iact phi L e k j x := by
    filter_upwards [heq] with x hx
    simp only [Dbd, Edom, Iact, hx j, hx (j-1)]
    exact ⟨rfl, rfl, rfl⟩
  have hcor : (fun o : Obs X Z => w o.1 * binaryRegularRegressionCorrection phi L ep k j o)
      =ᵐ[observationLaw M]
      (fun o => w o.1 * binaryRegularRegressionCorrection phi L e k j o) := by
    filter_upwards [observationLaw_covariate_ae M _ hcoeff] with o ho
    simp only [binaryRegularRegressionCorrection, ho.1, ho.2.1, ho.2.2]
    rfl
  have hmean : (fun o : Obs X Z => w o.1 *
      binaryRegularRegressionMean phi L (eta0Bin M L) ep k j o.1)
      =ᵐ[observationLaw M]
      (fun o => w o.1 * binaryRegularRegressionMean phi L (eta0Bin M L) e k j o.1) := by
    filter_upwards [observationLaw_covariate_ae M _ hcoeff] with o ho
    simp only [binaryRegularRegressionMean, ho.1, ho.2.1, ho.2.2]
    rfl
  refine ⟨hm.1.congr hcor, hm.2.1.congr hmean, ?_⟩
  rw [← integral_congr_ae hcor, hm.2.2, integral_congr_ae hmean]

-- The actual fitted product weight is measurable and in [0,1] by admissibility.
-- One assignment-overlap neighborhood works for every interval simultaneously.
-- @node: population_binary_regular_regression_path_local_mean
/-- Under [threshold crossing](hyp:h), [an admissible policy](hyp:hphi), [invariant
level ordering](hyp:hOrder), [baseline overlap with constant cpi](hyp:hov), and [binary
outcomes almost surely](hyp:hy), for [an admissible binary nuisance direction from the
truth](hyp:hd), [all sufficiently small path parameters simultaneously give, at every
pair of indices, integrability and equality of the regression correction mean and its
covariate regression representation, both weighted by the fitted regular product weight](goal). -/
lemma population_binary_regular_regression_path_local_mean
    (h : ThresholdCrossing M) (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi) (hy : OutcomeBinaryAE M)
    (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del)) :
    ∀ᶠ t : ℝ in nhds 0, ∀ k j,
      let e := eta0Bin M L + t • del
      let w := regularValue e.gamma k j
      Integrable (fun o : Obs X Z => w o.1 * binaryRegularRegressionCorrection phi L e k j o)
        (observationLaw M) ∧
      Integrable (fun o : Obs X Z => w o.1 *
        binaryRegularRegressionMean phi L (eta0Bin M L) e k j o.1) (observationLaw M) ∧
      (∫ o : Obs X Z, w o.1 * binaryRegularRegressionCorrection phi L e k j o
        ∂observationLaw M) =
        ∫ o : Obs X Z, w o.1 * binaryRegularRegressionMean phi L (eta0Bin M L) e k j o.1
          ∂observationLaw M := by
  have he0 := binary_admissible_direction_origin M L (eta0Bin M L) del hd
  obtain ⟨r, hr, hadm⟩ := hd.admissible
  filter_upwards [continuousAt_id.abs.eventually_lt_const (by simpa using hr),
    binary_assignment_denominators_uniform_neighborhood M L cpi hov del hd] with t ht hden
  intro k j
  dsimp only
  let e := eta0Bin M L + t • del
  have he : BinAdmissible M L e := hadm t ht
  have hw : Measurable (regularValue e.gamma k j) := by
    first
    | fun_prop
    | unfold regularValue
      split_ifs
      · exact (he.2.2.2.2.2.1 _).2
      · fun_prop
  have hwB : ∀ᵐ x ∂xLaw M, ‖regularValue e.gamma k j x‖ ≤ 1 := by
    unfold regularValue
    split_ifs
    · filter_upwards [he.2.2.2.2.1 _] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg hx.2.1]
      exact hx.2.2
    · exact Eventually.of_forall (fun _ => by norm_num)
  exact population_binary_regular_regression_correction_mean_of_admissible M h phi hphi
    L hOrder cpi hov hy he0 e he (cpi/2) (by have := hov.1; positivity) hden
    k j (regularValue e.gamma k j) hw 1 hwB

end Papers.TbsPrteOptimalTransport
