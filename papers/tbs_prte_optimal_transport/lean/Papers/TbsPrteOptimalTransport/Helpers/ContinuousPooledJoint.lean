module
public import Papers.TbsPrteOptimalTransport.Helpers.WeightedPooledPopulation
public import Papers.TbsPrteOptimalTransport.Helpers.QuantilePolicyCancellation
public import Papers.TbsPrteOptimalTransport.Helpers.JointPooledEnvelopes
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousTailAdmissibleDerivative
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousBandIndicatorJoint
/-! Joint continuous pooled-policy cancellation with moving simplex shares and weights. -/
@[expose] public section
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false
set_option linter.style.longLine false

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]

-- The success coordinate is unused by pooling. Zero makes its range constraint
-- automatic without requiring any binary-outcome assumption.
-- @node: continuousPooledCarrier
/-- For [an instrument space](hyp:Z), [a covariate space](hyp:X), [a system of
propensity and policy levels](hyp:L), and [continuous-outcome nuisance functions
for those levels](hyp:e), the [pooled binary carrier](goal)
retains the propensity, level, assignment, pooling-share, and weight functions,
and sets the auxiliary success regression to zero. -/
def continuousPooledCarrier (L : LevelData Z X) (e : NuisanceCont L) : NuisanceBin L :=
  ⟨e.prop, e.pLev, 0, e.piLev, e.tauLev, e.share, e.gammaFull, e.gamma, e.gammaTail⟩

-- @node: continuous_pooled_carrier_affine
/-- [Converting an affine perturbation of continuous nuisance functions to the
pooled binary carrier gives the same result as perturbing their carriers](goal),
for any level system, baseline nuisance functions, direction, and real step size. -/
lemma continuous_pooled_carrier_affine (L : LevelData Z X) (e d : NuisanceCont L) (t : ℝ) :
    continuousPooledCarrier L (e + t • d) =
      continuousPooledCarrier L e + t • continuousPooledCarrier L d := by
  change NuisanceBinData.mk _ _ _ _ _ _ _ _ _ = _
  congr 1
  ext x
  change (0 : ℝ) = 0 + t * 0
  ring

variable (M : LatentIVModel Ω X Z)

-- @node: continuous_pooled_carrier_admissible
/-- If [continuous-outcome nuisance functions are admissible for the model and
level system](hyp:he), [their pooled binary carrier is also admissible](goal). -/
lemma continuous_pooled_carrier_admissible (L : LevelData Z X) (e : NuisanceCont L)
    (he : ContAdmissible M L e) : BinAdmissible M L (continuousPooledCarrier L e) := by
  rcases he with ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12,
    e13, e14, e15, e16, e17, e18, e19, e20, e21, e22,
    e23, e24, e25, e26, e27, e28, e29, e30, e31⟩
  refine ⟨e1, e2, ?_, ?_, ?_, ?_, e9, e10, e31, e11, e12, e15, e16⟩
  · intro a
    filter_upwards [e3 a, e5 a] with x hp hi
    exact ⟨hp, by change (0 : ℝ) ∈ Icc 0 1; norm_num, hi⟩
  · intro a
    exact ⟨e4 a, measurable_const, e6 a⟩
  · intro a
    filter_upwards [e7 a, e13 a] with x ht hg
    exact ⟨ht, hg⟩
  · intro a
    exact ⟨e8 a, e14 a⟩

-- @node: continuous_pooled_carrier_direction
/-- If [a direction generates an admissible continuous-nuisance path around a
baseline](hyp:hd), [the corresponding pooled carriers generate an admissible
binary-nuisance path](goal). -/
lemma continuous_pooled_carrier_direction (L : LevelData Z X) (e d : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl e) (.inl d)) :
    IsAdmissibleDirection M L (.inr (continuousPooledCarrier L e))
      (.inr (continuousPooledCarrier L d)) := by
  obtain ⟨r, hr, hp⟩ := hd.admissible
  refine ⟨r, hr, ?_⟩
  intro t ht
  rw [← continuous_pooled_carrier_affine]
  exact continuous_pooled_carrier_admissible M L _ (hp t ht)

-- @node: continuous_pooled_carrier_level
/-- [The pooled policy level computed from the binary carrier equals the pooled
policy level computed from the original continuous nuisance functions](goal),
at every pair of level indices and every covariate value. -/
lemma continuous_pooled_carrier_level (phi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e : NuisanceCont L) (k j : ℕ) (x : X) :
    pooledQBin phi L (continuousPooledCarrier L e) k j x = pooledQ phi L e k j x := by
  rfl

-- @node: continuous_pooled_carrier_residual
/-- [The pooled policy residual computed from the binary carrier equals the
continuous-outcome pooled policy residual](goal), for every pair of level indices
and every observation. -/
lemma continuous_pooled_carrier_residual (dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e : NuisanceCont L) (k j : ℕ) (o : Obs X Z) :
    RqBin dphi L (continuousPooledCarrier L e) k j o = RqCont dphi L e k j o := by
  rfl

-- The finite-instrument tower identity applies to the continuous policy block
-- because neither its pooled level nor its residual uses an outcome coordinate.
-- @node: population_continuous_weighted_pooled_fitted_mean
/-- Suppose [treatment follows a threshold-crossing model](hyp:h), [the policy
map is measurable and maps probabilities to probabilities](hyp:hphi), [its
derivative is the specified derivative map](hyp:hDiff), and [that derivative is
uniformly bounded and Lipschitz](hyp:hDerivative). If [the continuous nuisance
functions are admissible](hyp:he), [the denominator bound is positive](hyp:hc),
[the pooling denominator at the chosen regular level is almost surely at least
that bound](hyp:hden), and the covariate weight is [measurable](hyp:hw) and
[almost surely bounded in absolute value by a common constant](hyp:hwB), then
[the weighted pooled level plus residual is integrable both over observations
and after averaging over instruments at their true treatment propensities, and
these two population means agree](goal). -/
lemma population_continuous_weighted_pooled_fitted_mean (h : ThresholdCrossing M)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e)
    (a : RegularIndex L) (c : ℝ) (hc : 0 < c)
    (hden : ∀ᵐ x ∂xLaw M, c ≤ e.tauLev a x)
    (w : X → ℝ) (hw : Measurable w) (W : ℝ)
    (hwB : ∀ᵐ x ∂xLaw M, ‖w x‖ ≤ W) :
    Integrable (fun o : Obs X Z => w o.1 *
      (pooledQ phi L e a.val.1 a.val.2 o.1 + RqCont dphi L e a.val.1 a.val.2 o))
      (observationLaw M) ∧
    Integrable (fun x => w x * (pooledQ phi L e a.val.1 a.val.2 x +
      ∑ z, instProb M z x * RqCont dphi L e a.val.1 a.val.2
        (x,z,M.prop z x,0))) (xLaw M) ∧
    (∫ o : Obs X Z, w o.1 * (pooledQ phi L e a.val.1 a.val.2 o.1 +
      RqCont dphi L e a.val.1 a.val.2 o) ∂observationLaw M) =
      ∫ x, w x * (pooledQ phi L e a.val.1 a.val.2 x +
        ∑ z, instProb M z x * RqCont dphi L e a.val.1 a.val.2
          (x,z,M.prop z x,0)) ∂xLaw M := by
  exact population_binary_weighted_pooled_fitted_mean M h phi dphi hphi hDiff
    hDerivative L (continuousPooledCarrier L e)
    (continuous_pooled_carrier_admissible M L e he) a c hc hden w hw W hwB

-- This supplies the upper/lower policy residual envelopes needed by the
-- regular-component bias bound. Its coefficients depend only on L2 directions.
-- @node: population_continuous_pooled_path_quadratic_envelope
/-- Suppose [the policy has the specified derivative](hyp:hDiff), [the derivative
bound is nonnegative](hyp:hB), [the Lipschitz constant is nonnegative](hyp:hLip),
[the derivative is bounded by the former on the unit interval](hyp:hbound), and
[its changes are bounded by the latter times changes in propensity](hyp:hlip).
If [baseline and policy propensities respect the level ordering](hyp:hOrder),
[policy pooling satisfies overlap with the given lower bound](hyp:hov), and
[the nuisance direction is admissible at the truth](hyp:hd), then [the sum over
the chosen pooling group of the Lipschitz constant times squared propensity
directions, the derivative bound times absolute share–propensity products, and
the derivative bound divided by half the overlap bound times absolute
denominator–propensity products is integrable and bounds the absolute
conditional debiased pooled-level error times the squared step size, almost
surely for all sufficiently small steps](goal). -/
lemma population_continuous_pooled_path_quadratic_envelope
    (phi dphi : Z → X → ℝ → ℝ) (hDiff : PolicyDifferentiable phi dphi)
    (B Lip : ℝ) (hB : 0 ≤ B) (hLip : 0 ≤ Lip)
    (hbound : ∀ z x p, p ∈ Icc (0 : ℝ) 1 → |dphi z x p| ≤ B)
    (hlip : ∀ z x p q, p ∈ Icc (0 : ℝ) 1 → q ∈ Icc (0 : ℝ) 1 →
      |dphi z x p - dphi z x q| ≤ Lip * |p - q|)
    (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi) (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (a : RegularIndex L) :
    let E := fun x => ∑ z ∈ L.T a.val.1 a.val.2,
      (Lip * (del.prop z x)^2 + B * |del.share a z x * del.prop z x| +
        (B/(cpi/2)) * |del.tauLev a x * del.prop z x|)
    Integrable E (xLaw M) ∧
    ∀ᶠ t : ℝ in nhds 0, ∀ᵐ x ∂xLaw M,
      |pooledQ phi L (trueNuisance M L + t • del) a.val.1 a.val.2 x +
        (∑ z, instProb M z x * RqCont dphi L (trueNuisance M L + t • del)
          a.val.1 a.val.2 (x,z,M.prop z x,0)) -
        pooledQ phi L (trueNuisance M L) a.val.1 a.val.2 x| ≤ E x * t^2 := by
  dsimp only
  have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  let eta := continuousPooledCarrier L (trueNuisance M L)
  let d := continuousPooledCarrier L del
  have hbd := continuous_pooled_carrier_direction M L (trueNuisance M L) del hd
  have he := continuous_admissible_direction_origin M L (trueNuisance M L) del hd
  obtain ⟨Ca, _, ha⟩ := binary_simplex_share_direction_regular M L eta d hbd
  obtain ⟨Ct, _, ht⟩ := binary_pooled_denominator_direction_regular M L eta d hbd
  have hden : ∀ᵐ x ∂xLaw M, cpi ≤ (trueNuisance M L).tauLev a x := by
    apply Eventually.of_forall
    intro x
    exact hov.2 x a.val.1 a.val.2 a.property.1 a.property.2.1 a.property.2.2
      (ordered_policy_level_nonempty M (policyProp phi M.prop) L hOrder
        a.val.1 a.val.2 a.property.1 a.property.2.1 a.property.2.2)
  refine ⟨?_, ?_⟩
  · apply pooled_policy_joint_L2_envelope_integrable
    · intro z _
      exact continuous_propensity_direction_memLp M L (trueNuisance M L) del hd z
    · intro z _
      exact MemLp.of_bound (ha a z).1.aestronglyMeasurable Ca (ha a z).2
    · exact MemLp.of_bound (ht a).1.aestronglyMeasurable Ct (ht a).2
  · filter_upwards [(continuous_pooled_path_uniform_lower_bound M (policyProp phi M.prop) L hOrder
      cpi hov del hd).mono (fun _ ht => ht a),
      continuous_propensity_path_uniform_neighborhood M L (trueNuisance M L) del hd]
        with t hdt hp
    filter_upwards [hden, hdt, ae_all_iff.mpr hp,
      ae_all_iff.mpr (he.2.2.2.2.2.2.2.2.1 a),
      bin_admissible_share_direction M L eta d hbd a]
        with x hx htx hpx hax hsimplex
    have hshare : ∀ z ∈ L.T a.val.1 a.val.2,
        (trueNuisance M L).share a z x = instProb M z x / (trueNuisance M L).tauLev a x := by
      intro z hz
      simp only [trueNuisance, levelShares, if_pos hz]
    have hcommon : ∀ z ∈ L.T a.val.1 a.val.2,
        phi z x ((trueNuisance M L).prop z x) = L.qLev a.val.1 a.val.2 x := by
      intro z hz
      exact (hOrder.2.2.2.2.2.2.1 x a.val.1 a.val.2 z a.property.1
        a.property.2.1 a.property.2.2).mp hz
    have hb := pooledQBin_joint_conditional_remainder_bound phi dphi hDiff B Lip hB hLip
      hbound hlip L eta d a x (fun z => instProb M z x) t (cpi/2)
      (by have := hov.1; positivity) (ne_of_gt (hov.1.trans_le hx)) htx hshare
      (fun z _ => M.rangeProp z x) (fun z _ => hpx z) hcommon hsimplex
    have hE := pooled_policy_joint_remainder_envelope_le (L.T a.val.1 a.val.2)
      (fun z => (trueNuisance M L).share a z x) (fun z => del.share a z x)
      (fun z => del.prop z x) (del.tauLev a x) B Lip (cpi/2) hB hLip
      (by have := hov.1; positivity) (fun z _ => by
        rw [abs_of_nonneg (hax z).1]; exact (hax z).2)
    have hprop : eta.prop = M.prop := rfl
    rw [hprop] at hb
    have hres := hb.trans (mul_le_mul_of_nonneg_right hE (sq_nonneg t))
    simpa only [eta, d, ← continuous_pooled_carrier_affine,
      continuous_pooled_carrier_level, continuous_pooled_carrier_residual] using hres


-- The pooled Taylor remainder, share/propensity product, and denominator/propensity
-- product survive jointly. A bounded moving weight preserves their quadratic order.
-- @node: population_continuous_weighted_pooled_joint_orthogonality
/-- Suppose [treatment follows a threshold-crossing model](hyp:h), [the policy
map is measurable and preserves the unit interval](hyp:hphi), [it has the
specified derivative](hyp:hDiff), [that derivative is uniformly bounded and
Lipschitz](hyp:hDerivative), [baseline and policy propensities respect the level
ordering](hyp:hOrder), [policy pooling satisfies overlap](hyp:hov), and [the
nuisance direction is admissible at the truth](hyp:hd). For [a nonnegative
weight bound](hyp:hW), if [the moving covariate weights are measurable and
almost surely bounded in absolute value by that bound for all sufficiently
small steps](hyp:hw), then [the population mean of the weighted change in the
pooled policy level plus its residual has derivative zero at step zero, and its
integrand is integrable for all sufficiently small steps](goal). -/
lemma population_continuous_weighted_pooled_joint_orthogonality
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi) (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (a : RegularIndex L) (w : ℝ → X → ℝ) (W : ℝ) (hW : 0 ≤ W)
    (hw : ∀ᶠ t : ℝ in 𝓝 0, Measurable (w t) ∧ ∀ᵐ x ∂xLaw M, ‖w t x‖ ≤ W) :
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z, w t o.1 *
      (pooledQ phi L (trueNuisance M L + t • del) a.val.1 a.val.2 o.1 +
        RqCont dphi L (trueNuisance M L + t • del) a.val.1 a.val.2 o -
        pooledQ phi L (trueNuisance M L) a.val.1 a.val.2 o.1)
        ∂observationLaw M) 0 0 ∧
    (∀ᶠ t : ℝ in 𝓝 0, Integrable (fun o : Obs X Z => w t o.1 *
      (pooledQ phi L (trueNuisance M L + t • del) a.val.1 a.val.2 o.1 +
        RqCont dphi L (trueNuisance M L + t • del) a.val.1 a.val.2 o -
        pooledQ phi L (trueNuisance M L) a.val.1 a.val.2 o.1))
      (observationLaw M)) := by
  obtain ⟨B, Lip, hB, hLip, hb⟩ := hDerivative
  let E : X → ℝ := fun x => ∑ z ∈ L.T a.val.1 a.val.2,
    (Lip * (del.prop z x)^2 + B * |del.share a z x * del.prop z x| +
      (B/(cpi/2)) * |del.tauLev a x * del.prop z x|)
  have hE := population_continuous_pooled_path_quadratic_envelope M phi dphi hDiff
    B Lip hB hLip (fun z x p hp => (hb z x p p hp hp).1)
    (fun z x p q hp hq => (hb z x p q hp hq).2) L hOrder cpi hov del hd a
  dsimp only at hE
  have he0 := continuous_admissible_direction_origin M L (trueNuisance M L) del hd
  obtain ⟨r, hr, hadm⟩ := hd.admissible
  let f : ℝ → ℝ := fun t => ∫ o : Obs X Z, w t o.1 *
    (pooledQ phi L (trueNuisance M L + t • del) a.val.1 a.val.2 o.1 +
      RqCont dphi L (trueNuisance M L + t • del) a.val.1 a.val.2 o -
      pooledQ phi L (trueNuisance M L) a.val.1 a.val.2 o.1) ∂observationLaw M
  have hlocal : ∀ᶠ t : ℝ in 𝓝 0,
      Integrable (fun o : Obs X Z => w t o.1 *
        (pooledQ phi L (trueNuisance M L + t • del) a.val.1 a.val.2 o.1 +
          RqCont dphi L (trueNuisance M L + t • del) a.val.1 a.val.2 o -
          pooledQ phi L (trueNuisance M L) a.val.1 a.val.2 o.1))
        (observationLaw M) ∧ |f t| ≤ (W * ∫ x, E x ∂xLaw M) * t^2 := by
    filter_upwards [hw, hE.2,
      continuous_pooled_path_uniform_lower_bound M (policyProp phi M.prop) L hOrder
        cpi hov del hd,
      continuousAt_id.abs.eventually_lt_const (by simpa using hr)] with t hwt hEt hdt ht
    let e := trueNuisance M L + t • del
    have he : ContAdmissible M L e := hadm t ht
    have hm := population_continuous_weighted_pooled_fitted_mean M h phi dphi hphi
      hDiff ⟨B, Lip, hB, hLip, hb⟩ L e he a (cpi/2)
      (div_pos hov.1 (by norm_num)) (hdt a) (w t) hwt.1 W hwt.2
    have hbase := pooledQBin_weighted_integrable_of_binary_admissible M phi hphi L
      (continuousPooledCarrier L (trueNuisance M L))
      (continuous_pooled_carrier_admissible M L _ he0) a (w t) hwt.1 W hwt.2
    simp only [continuous_pooled_carrier_level] at hbase
    have hobs : Integrable (fun o : Obs X Z => w t o.1 *
        (pooledQ phi L e a.val.1 a.val.2 o.1 + RqCont dphi L e a.val.1 a.val.2 o -
          pooledQ phi L (trueNuisance M L) a.val.1 a.val.2 o.1)) (observationLaw M) := by
      simpa only [mul_sub] using hm.1.sub' hbase.2.1
    let R : X → ℝ := fun x => pooledQ phi L e a.val.1 a.val.2 x +
      (∑ z, instProb M z x * RqCont dphi L e a.val.1 a.val.2 (x,z,M.prop z x,0)) -
      pooledQ phi L (trueNuisance M L) a.val.1 a.val.2 x
    have hiR : Integrable (fun x => w t x * R x) (xLaw M) := by
      simpa only [R, mul_sub] using hm.2.1.sub' hbase.1
    have hid : f t = ∫ x, w t x * R x ∂xLaw M := by
      dsimp only [f, R]
      simp_rw [mul_sub]
      rw [integral_sub hm.1 hbase.2.1, integral_sub hm.2.1 hbase.1,
        hm.2.2, hbase.2.2]
    have hbound : ∀ᵐ x ∂xLaw M, |w t x * R x| ≤ W * E x * t^2 := by
      filter_upwards [hwt.2, hEt] with x hx hRx
      rw [abs_mul]
      have hx' : |w t x| ≤ W := by simpa only [Real.norm_eq_abs] using hx
      calc
        _ ≤ W * |R x| := mul_le_mul_of_nonneg_right hx' (abs_nonneg _)
        _ ≤ W * (E x * t^2) := mul_le_mul_of_nonneg_left hRx hW
        _ = _ := by ring
    refine ⟨hobs, ?_⟩
    rw [hid]
    calc
      _ ≤ ∫ x, |w t x * R x| ∂xLaw M := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => w t x * R x)
      _ ≤ ∫ x, W * E x * t^2 ∂xLaw M :=
        integral_mono_ae hiR.abs ((hE.1.const_mul W).mul_const (t^2)) hbound
      _ = _ := by rw [integral_mul_const, integral_const_mul]
  have hf0 : f 0 = 0 := by
    have hz := hlocal.self_of_nhds.2
    simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero] at hz
    exact abs_eq_zero.mp (le_antisymm hz (abs_nonneg _))
  have ho : (fun t => f t - f 0) =O[𝓝 0] (fun t : ℝ => t^2) := by
    apply Asymptotics.IsBigO.of_bound (W * ∫ x, E x ∂xLaw M)
    filter_upwards [hlocal] with t ht
    simpa only [hf0, sub_zero, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)] using ht.2
  refine ⟨?_, hlocal.mono (fun _ ht => ht.1)⟩
  apply HasDerivAt.of_isLittleO
  simpa only [f, smul_zero, sub_zero] using
    ho.trans_isLittleO (Asymptotics.isLittleO_pow_id (𝕜 := ℝ) (by norm_num : 1 < 2))

-- This is the coefficient appearing in either signed policy channel of a band
-- product. Its measurability and bound are consequences of the admissible path.
-- @node: population_continuous_band_weighted_pooled_joint_orthogonality
/-- Suppose [treatment follows a threshold-crossing model](hyp:h), [the policy
map is measurable and preserves the unit interval](hyp:hphi), [it has the
specified derivative](hyp:hDiff), [that derivative is uniformly bounded and
Lipschitz](hyp:hDerivative), [baseline and policy propensities respect the level
ordering](hyp:hOrder), [policy pooling satisfies overlap](hyp:hov), and [the
nuisance direction is admissible at the truth](hyp:hd). Then [the population
mean of the debiased change in a regular pooled policy level, weighted by the
moving regular-component weight times the moving band boundary, has derivative
zero at step zero, and the weighted integrand is integrable for all sufficiently
small steps](goal). -/
lemma population_continuous_band_weighted_pooled_joint_orthogonality
    (h : ThresholdCrossing M) (phi dphi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (hDiff : PolicyDifferentiable phi dphi)
    (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi) (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (a g : RegularIndex L) (k i : ℕ) :
    let e := fun t : ℝ => trueNuisance M L + t • del
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z,
      ((e t).gamma g o.1 * nuValue M (e t) k i o.1) *
      (pooledQ phi L (e t) a.val.1 a.val.2 o.1 +
        RqCont dphi L (e t) a.val.1 a.val.2 o -
        pooledQ phi L (trueNuisance M L) a.val.1 a.val.2 o.1)
        ∂observationLaw M) 0 0 ∧
    (∀ᶠ t : ℝ in 𝓝 0, Integrable (fun o : Obs X Z =>
      ((e t).gamma g o.1 * nuValue M (e t) k i o.1) *
      (pooledQ phi L (e t) a.val.1 a.val.2 o.1 +
        RqCont dphi L (e t) a.val.1 a.val.2 o -
        pooledQ phi L (trueNuisance M L) a.val.1 a.val.2 o.1))
      (observationLaw M)) := by
  dsimp only
  apply population_continuous_weighted_pooled_joint_orthogonality M h phi dphi hphi
    hDiff hDerivative L hOrder cpi hov del hd a
    (fun t x => (trueNuisance M L + t • del).gamma g x *
      nuValue M (trueNuisance M L + t • del) k i x)
    (|M.yMin| + |M.yMax|) (by positivity)
  obtain ⟨r, hr, hp⟩ := hd.admissible
  filter_upwards [continuousAt_id.abs.eventually_lt_const (by simpa using hr)] with t ht
  have he := hp t ht
  have hgm := he.2.2.2.2.2.2.2.2.2.2.2.2.2.1 g
  have hnm := continuous_admissible_nuValue_measurable M L _ he k i
  refine ⟨by fun_prop, ?_⟩
  filter_upwards [he.2.2.2.2.2.2.2.2.2.2.2.2.1 g,
    continuous_admissible_nuValue_abs_bound M L _ he k i] with x hg hn
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hg.1]
  calc
    _ ≤ 1 * (|M.yMin| + |M.yMax|) :=
      mul_le_mul hg.2 hn (abs_nonneg _) (by norm_num)
    _ = _ := one_mul _

end Papers.TbsPrteOptimalTransport
