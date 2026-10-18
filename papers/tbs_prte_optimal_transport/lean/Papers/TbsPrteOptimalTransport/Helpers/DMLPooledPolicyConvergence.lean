module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRegularProductAssembly
public import Papers.TbsPrteOptimalTransport.Helpers.DMLTailAssembly
/-! Policy composition and pooled policy rates for the fractional binary score.
Measurable clipped versions handle nuisance ranges that hold only almost everywhere. -/
public section
set_option linter.style.haveILetI false
set_option linter.style.longLine false
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

-- @node: fitted_policy_measurable_version
/-- If [the policy map is valid](hyp:hphi) and [the binary nuisance fit is
admissible](hyp:he), then [for each instrument the fitted policy admits a
measurable version taking values between zero and one everywhere and agreeing
with the original policy almost surely under the covariate law](goal). -/
lemma fitted_policy_measurable_version (phi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (L : LevelData Z X) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (z : Z) :
    ∃ q : X → ℝ, Measurable q ∧ (∀ x, q x ∈ Icc (0 : ℝ) 1) ∧
      q =ᵐ[xLaw M] (fun x => phi z x (e.prop z x)) := by
  let pc := fun x => max 0 (min 1 (e.prop z x))
  have hm : Measurable pc := by
    dsimp only [pc]
    first | fun_prop | have hp := he.2.1 z; fun_prop
  have hr : ∀ x, pc x ∈ Icc (0 : ℝ) 1 := fun x =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  refine ⟨fun x => phi z x (pc x), ?_, fun x => hphi.2 z x _ (hr x), ?_⟩
  · first | fun_prop | exact hphi.1.comp (measurable_const.prodMk
      (measurable_id.prodMk (hm.subtype_mk (h := hr))))
  · filter_upwards [he.1 z] with x hx
    simp only [pc, min_eq_right hx.2, max_eq_right hx.1]

-- @node: fitted_policy_memLp
/-- For [a valid policy map](hyp:hphi) and [admissible binary nuisances](hyp:he),
[the policy evaluated at the fitted propensity for any instrument has a finite
second moment under the covariate law](goal). -/
lemma fitted_policy_memLp (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e) (z : Z) :
    MemLp (fun x => phi z x (e.prop z x)) 2 (xLaw M) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  obtain ⟨q, hm, hr, heq⟩ := fitted_policy_measurable_version M phi hphi L e he z
  have hq : MemLp q 2 (xLaw M) := by
    apply MemLp.of_bound hm.aestronglyMeasurable 1
    exact Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hr x).1]; exact (hr x).2)
  exact hq.ae_eq heq

-- A uniform derivative bound supplies the documented Lipschitz constant.
-- This lemma takes that analytic bound, never a rate for the policy itself.
-- @node: fitted_policy_l2Error_bound
/-- Suppose [the policy map is valid](hyp:hphi), [B is nonnegative](hyp:hB),
and [changing propensity within the unit interval changes policy by at most
B times the propensity change](hyp:hlip). For [admissible reference](hyp:he0)
and [fitted](hyp:he) nuisances, [the instrument-specific policy L2 error is
at most B times the propensity L2 error](goal). -/
lemma fitted_policy_l2Error_bound (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (B : ℝ) (hB : 0 ≤ B)
    (hlip : ∀ z x p r, p ∈ Icc (0 : ℝ) 1 → r ∈ Icc (0 : ℝ) 1 →
      |phi z x p - phi z x r| ≤ B * |p - r|)
    (L : LevelData Z X) (e0 e : NuisanceBin L)
    (he0 : BinAdmissible M L e0) (he : BinAdmissible M L e) (z : Z) :
    finiteL2Error M (fun x => phi z x (e.prop z x)) (fun x => phi z x (e0.prop z x)) ≤
      B * finiteL2Error M (e.prop z) (e0.prop z) := by
  have hp := ((fitted_prop_gammaTail_memLp M L e he).1 z).sub
    ((fitted_prop_gammaTail_memLp M L e0 he0).1 z)
  have hq := (fitted_policy_memLp M phi hphi L e he z).sub
    (fitted_policy_memLp M phi hphi L e0 he0 z)
  rw [l2Error_eq_eLpNorm M _ _ hp, l2Error_eq_eLpNorm M _ _ hq]
  have hb := eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (f := fun x => phi z x (e.prop z x) - phi z x (e0.prop z x))
    (g := fun x => e.prop z x - e0.prop z x) (c := B) (p := (2 : ENNReal)) (by
    filter_upwards [he.1 z, he0.1 z] with x hx hx0
    simpa only [Real.norm_eq_abs] using hlip z x _ _ hx hx0)
  calc
    _ ≤ (ENNReal.ofReal B * eLpNorm (fun x => e.prop z x - e0.prop z x)
        2 (xLaw M)).toReal := ENNReal.toReal_mono
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hp.eLpNorm_ne_top) hb
    _ = _ := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB]

-- @node: nuisanceRates_policy_quarter_rate
/-- If [the policy is valid](hyp:hphi), [B is nonnegative](hyp:hB), and
[the policy is uniformly B-Lipschitz in propensity on the unit interval](hyp:hlip),
then [admissibility of the reference](hyp:he0) and [all fitted nuisances](hyp:heh),
together with [the finite propensity quarter-rate condition](hyp:hrp), imply
[the same componentwise quarter-rate condition for fitted policy values](goal). -/
lemma nuisanceRates_policy_quarter_rate {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (B : ℝ) (hB : 0 ≤ B)
    (hlip : ∀ z x p r, p ∈ Icc (0 : ℝ) 1 → r ∈ Icc (0 : ℝ) 1 →
      |phi z x p - phi z x r| ≤ B * |p - r|)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop) :
    FiniteNuisanceRates M μ (fun n a z x => phi z x ((eh n a).prop z x))
      (fun z x => phi z x (e0.prop z x)) := by
  intro z
  apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul (by positivity : 0 < B + 1) (hrp z)
  intro n a
  simp only [finiteL2Error, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (fitted_policy_l2Error_bound M phi hphi B hB hlip L e0 _ he0 (heh _ a) z).trans
    (mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _))

-- The policy's Lipschitz bound is a consequence of the paper's derivative
-- assumption, including the endpoints through within-derivatives.
-- @node: policy_lipschitz_of_derivative_bound
/-- If [the policy has the specified derivative on the unit interval](hyp:hd)
and [that derivative has absolute value at most B everywhere on the interval](hyp:hb),
then [for every instrument and covariate value the policy change between any
two propensities in the unit interval is at most B times their distance](goal). -/
lemma policy_lipschitz_of_derivative_bound (phi dphi : Z → X → ℝ → ℝ)
    (hd : PolicyDifferentiable phi dphi) (B : ℝ)
    (hb : ∀ z x p, p ∈ Icc (0 : ℝ) 1 → |dphi z x p| ≤ B) :
    ∀ z x p r, p ∈ Icc (0 : ℝ) 1 → r ∈ Icc (0 : ℝ) 1 →
      |phi z x p - phi z x r| ≤ B * |p - r| := by
  intro z x p r hp hr
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (hd z x)
      (fun t ht => by simpa only [Real.norm_eq_abs] using hb z x t ht)
      (convex_Icc (0 : ℝ) 1) hr hp

-- @node: fitted_policy_share_memLp
/-- For [a valid policy](hyp:hphi) and [an admissible binary nuisance fit](hyp:he),
[the product of an instrument's fitted pooling share and its fitted policy
value has a finite second moment under the covariate law at every regular
level](goal). -/
lemma fitted_policy_share_memLp (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e)
    (a : RegularIndex L) (z : Z) :
    MemLp (fun x => e.share a z x * phi z x (e.prop z x)) 2 (xLaw M) := by
  haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  have hs := he.2.2.2.2.2.2.2.1 a z
  have hq := fitted_policy_memLp M phi hphi L e he z
  apply MemLp.of_bound (by first | fun_prop | exact hs.aestronglyMeasurable.mul hq.1) 1
  filter_upwards [he.2.2.2.2.2.2.1 a z, he.1 z] with x hx hp
  have hr := hphi.2 z x _ hp
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hx.1, abs_of_nonneg hr.1]
  exact (mul_le_mul hx.2 hr.2 hr.1 zero_le_one).trans_eq (one_mul _)

-- Clipping supplies second moments of every pooled endpoint, including the
-- fixed zero and upper endpoints. No global measurability of phi is required.
-- @node: fitted_pooledQBin_memLp
/-- If [the policy map is valid](hyp:hphi) and [the binary nuisance fit is
admissible](hyp:he), then [every fitted pooled policy value, including endpoint
values, has a finite second moment under the covariate law](goal). -/
lemma fitted_pooledQBin_memLp (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e) (k j : ℕ) :
    MemLp (pooledQBin phi L e k j) 2 (xLaw M) := by
  unfold pooledQBin
  split_ifs with hj0 hj hi
  · exact (fitted_positive_treatment_assignment_memLp M L e he k).1
  · exact (fitted_positive_treatment_assignment_memLp M L e he (k+1)).1
  · exact memLp_finsetSum _ (fun z _ => fitted_policy_share_memLp M phi hphi L e he
      ⟨(k,j), hi⟩ z)
  · simpa only [zero_mul, Finset.sum_const_zero] using
      (MemLp.zero' : MemLp (fun _ : X => (0 : ℝ)) 2 (xLaw M))

-- @node: fitted_pooledQBin_l2Error_bound
/-- For [a valid policy](hyp:hphi), [a nonnegative constant B](hyp:hB), and
[a uniform B-Lipschitz bound in propensity on the unit interval](hyp:hlip),
suppose [the reference](hyp:he0) and [fitted](hyp:he) nuisances are admissible
and [the treatment and policy indices form a regular level](hyp:hi). Then
[the pooled policy L2 error is bounded by the sum over that level's instruments
of B times each propensity L2 error plus each pooling-share L2 error](goal). -/
lemma fitted_pooledQBin_l2Error_bound (phi : Z → X → ℝ → ℝ)
    (hphi : IsPolicyMap phi) (B : ℝ) (hB : 0 ≤ B)
    (hlip : ∀ z x p r, p ∈ Icc (0 : ℝ) 1 → r ∈ Icc (0 : ℝ) 1 →
      |phi z x p - phi z x r| ≤ B * |p - r|)
    (L : LevelData Z X) (e0 e : NuisanceBin L)
    (he0 : BinAdmissible M L e0) (he : BinAdmissible M L e)
    (k j : ℕ) (hi : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k) :
    finiteL2Error M (pooledQBin phi L e k j) (pooledQBin phi L e0 k j) ≤
      ∑ z ∈ L.T k j, (B * finiteL2Error M (e.prop z) (e0.prop z) +
        finiteL2Error M (e.share ⟨(k,j), hi⟩ z) (e0.share ⟨(k,j), hi⟩ z)) := by
  let a : RegularIndex L := ⟨(k,j), hi⟩
  let dp := fun z x => e.prop z x - e0.prop z x
  let ds := fun z x => e.share a z x - e0.share a z x
  let E := fun z x => B * ‖dp z x‖ + ‖ds z x‖
  have hp z : MemLp (dp z) 2 (xLaw M) :=
    ((fitted_prop_gammaTail_memLp M L e he).1 z).sub
      ((fitted_prop_gammaTail_memLp M L e0 he0).1 z)
  have hs z : MemLp (ds z) 2 (xLaw M) := by
    haveI : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
    have sh (e' : NuisanceBin L) (he' : BinAdmissible M L e') :
        MemLp (e'.share a z) 2 (xLaw M) := by
      apply MemLp.of_bound (he'.2.2.2.2.2.2.2.1 a z).aestronglyMeasurable 1
      filter_upwards [he'.2.2.2.2.2.2.1 a z] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg hx.1]; exact hx.2
    exact (sh e he).sub (sh e0 he0)
  have hE z : MemLp (E z) 2 (xLaw M) := ((hp z).norm.const_mul B).add (hs z).norm
  have hq := (fitted_pooledQBin_memLp M phi hphi L e he k j).sub
    (fitted_pooledQBin_memLp M phi hphi L e0 he0 k j)
  have hmono : eLpNorm (fun x => pooledQBin phi L e k j x - pooledQBin phi L e0 k j x)
      2 (xLaw M) ≤ eLpNorm (fun x => ∑ z ∈ L.T k j, E z x) 2 (xLaw M) := by
    apply eLpNorm_mono_ae_real
    filter_upwards [ae_all_iff.mpr he.1, ae_all_iff.mpr he0.1,
      ae_all_iff.mpr (he.2.2.2.2.2.2.1 a),
      ae_all_iff.mpr (he0.2.2.2.2.2.2.1 a)] with x hp1 hp0 hs1 hs0
    have hj0 : j ≠ 0 := by omega
    have hjl : ¬ L.l k < j := by omega
    simp only [pooledQBin, if_neg hj0, if_neg hjl, dif_pos hi, ← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro z hz
    have hq0 := hphi.2 z x _ (hp0 z)
    have hpol := hlip z x _ _ (hp1 z) (hp0 z)
    have hid : e.share a z x * phi z x (e.prop z x) -
        e0.share a z x * phi z x (e0.prop z x) =
        e.share a z x * (phi z x (e.prop z x) - phi z x (e0.prop z x)) +
          (e.share a z x - e0.share a z x) * phi z x (e0.prop z x) := by ring
    rw [hid]
    apply (abs_add_le _ _).trans
    dsimp only [E, dp, ds]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (hs1 z).1, abs_of_nonneg hq0.1]
    exact add_le_add
      ((mul_le_mul_of_nonneg_left hpol (hs1 z).1).trans
        (mul_le_of_le_one_left (mul_nonneg hB (abs_nonneg _)) (hs1 z).2))
      (mul_le_of_le_one_right (abs_nonneg _) hq0.2)
  have hsum := eLpNorm_sum_le (fun z (_ : z ∈ L.T k j) => (hE z).1)
    (by norm_num : (1 : ENNReal) ≤ 2)
  have heq : (∑ z ∈ L.T k j, E z) = (fun x => ∑ z ∈ L.T k j, E z x) := by
    funext x
    simp only [Finset.sum_apply]
  rw [heq] at hsum
  have hfin : (∑ z ∈ L.T k j, eLpNorm (E z) 2 (xLaw M)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun z _ => (hE z).eLpNorm_ne_top)
  rw [l2Error_eq_eLpNorm M _ _ hq]
  apply (ENNReal.toReal_mono hfin (hmono.trans hsum)).trans
  rw [ENNReal.toReal_sum (fun z _ => (hE z).eLpNorm_ne_top)]
  apply Finset.sum_le_sum
  intro z hz
  have hb := eLpNorm_add_le ((hp z).norm.const_mul B).1 (hs z).norm.1
    (by norm_num : (1 : ENNReal) ≤ 2)
  have hf : eLpNorm (fun x => B * ‖dp z x‖) 2 (xLaw M) +
      eLpNorm (fun x => ‖ds z x‖) 2 (xLaw M) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨((hp z).norm.const_mul B).eLpNorm_ne_top,
      (hs z).norm.eLpNorm_ne_top⟩
  rw [l2Error_eq_eLpNorm M _ _ (hp z), l2Error_eq_eLpNorm M _ _ (hs z)]
  have hsmul : eLpNorm (fun x => B * ‖dp z x‖) 2 (xLaw M) =
      ‖B‖ₑ * eLpNorm (fun x => ‖dp z x‖) 2 (xLaw M) :=
    eLpNorm_const_smul B (fun x => ‖dp z x‖) 2 (xLaw M)
  apply (ENNReal.toReal_mono hf hb).trans_eq
  rw [ENNReal.toReal_add ((hp z).norm.const_mul B).eLpNorm_ne_top
    (hs z).norm.eLpNorm_ne_top, hsmul, eLpNorm_norm, eLpNorm_norm,
    ENNReal.toReal_mul, toReal_enorm,
    Real.norm_of_nonneg hB]

-- The finite envelope is constructed from instrument and share errors.
-- Endpoint branches use the baseline rates, including the structural zero.
-- @node: nuisanceRates_pooledQBin_quarter_rate
/-- Suppose [the policy is valid](hyp:hphi), [B is nonnegative](hyp:hB),
[the policy is uniformly B-Lipschitz in propensity on the unit interval](hyp:hlip),
and [the reference](hyp:he0) and [all fitted nuisances](hyp:heh) are admissible.
If [propensities](hyp:hrp), [treatment-level propensities](hyp:hrlev), and
[pooling shares at every regular level](hyp:hrs) satisfy the finite componentwise
quarter-rate conditions, then [all pooled binary policy values satisfy those
quarter-rate conditions, including endpoints](goal). -/
lemma nuisanceRates_pooledQBin_quarter_rate {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (B : ℝ) (hB : 0 ≤ B)
    (hlip : ∀ z x p r, p ∈ Icc (0 : ℝ) 1 → r ∈ Icc (0 : ℝ) 1 →
      |phi z x p - phi z x r| ≤ B * |p - r|)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrs : ∀ a : RegularIndex L,
      FiniteNuisanceRates M μ (fun n t => (eh n t).share a) (e0.share a)) :
    FiniteNuisanceRates M μ (fun n t (kj : ℕ × ℕ) => pooledQBin phi L (eh n t) kj.1 kj.2)
      (fun kj => pooledQBin phi L e0 kj.1 kj.2) := by
  intro ⟨k,j⟩
  have hl := nuisanceRates_positiveValue M μ L.K _ _ hrlev
  by_cases hj0 : j = 0
  · have hq (e : NuisanceBin L) : pooledQBin phi L e k j = positiveValue e.pLev k := by
      funext x
      simp only [pooledQBin, if_pos hj0]
    simpa only [hq] using hl k
  by_cases hjl : L.l k < j
  · have hq (e : NuisanceBin L) : pooledQBin phi L e k j = positiveValue e.pLev (k+1) := by
      funext x
      simp only [pooledQBin, if_neg hj0, if_pos hjl]
    simpa only [hq] using hl (k+1)
  by_cases hi : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k
  · let a : RegularIndex L := ⟨(k,j), hi⟩
    let zs := (L.T k j).toList
    let dp := fun n t z => finiteL2Error M ((eh (2*(n+1)) t).prop z) (e0.prop z)
    let ds := fun n t z => finiteL2Error M ((eh (2*(n+1)) t).share a z) (e0.share a z)
    let E := fun n t => maxErrors (zs.map (dp n t)) + maxErrors (zs.map (ds n t))
    have hr := (nuisanceRates_finite_maxErrors M μ _ _ zs hrp).add_eventually_nonneg_rate
      (Eventually.of_forall (fun _ => Real.rpow_nonneg (by positivity) _))
      (nuisanceRates_finite_maxErrors M μ _ _ zs (hrs a))
    let C := ((L.T k j).card : ℝ) * (B+1) + 1
    apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul (by dsimp only [C]; positivity : 0 < C) hr
    intro n t
    have hn : 0 ≤ E n t := add_nonneg (maxErrors_nonneg _) (maxErrors_nonneg _)
    change |finiteL2Error M (pooledQBin phi L (eh (2*(n+1)) t) k j)
      (pooledQBin phi L e0 k j)| ≤ C * |E n t|
    rw [abs_of_nonneg (show 0 ≤ finiteL2Error M _ _ from Real.sqrt_nonneg _), abs_of_nonneg hn]
    apply (fitted_pooledQBin_l2Error_bound M phi hphi B hB hlip L e0 _ he0
      (heh _ t) k j hi).trans
    calc
      _ ≤ ∑ _z ∈ L.T k j, (B+1) * E n t := by
        apply Finset.sum_le_sum
        intro z hz
        have hp : dp n t z ≤ maxErrors (zs.map (dp n t)) :=
          le_maxErrors_of_mem (List.mem_map.mpr ⟨z, by simpa only [zs, Finset.mem_toList] using hz, rfl⟩)
        have hs : ds n t z ≤ maxErrors (zs.map (ds n t)) :=
          le_maxErrors_of_mem (List.mem_map.mpr ⟨z, by simpa only [zs, Finset.mem_toList] using hz, rfl⟩)
        change B * dp n t z + ds n t z ≤ (B+1) * E n t
        dsimp only [E]
        nlinarith [mul_le_mul_of_nonneg_left hp hB,
          mul_nonneg hB (maxErrors_nonneg (zs.map (ds n t))),
          maxErrors_nonneg (zs.map (dp n t))]
      _ = (((L.T k j).card : ℝ) * (B+1)) * E n t := by simp; ring
      _ ≤ C * E n t := mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) hn
  · have hzero : ¬ (1 ≤ 0 ∧ 0 ≤ L.K) := by omega
    have hq (e : NuisanceBin L) : pooledQBin phi L e k j = positiveValue e.pLev 0 := by
      funext x
      simp only [pooledQBin, if_neg hj0, if_neg hjl, dif_neg hi, zero_mul,
        Finset.sum_const_zero, positiveValue, dif_neg hzero]
    simpa only [hq] using hl 0

-- @node: dml_l2Error_sub_le
/-- If [the first reference function](hyp:hf), [its fit](hyp:hfh),
[the second reference function](hyp:hg), and [its fit](hyp:hgh) have finite
second moments under the covariate law, then [the L2 error in their fitted
difference is at most the sum of their individual L2 errors](goal). -/
lemma dml_l2Error_sub_le (f fh g gh : X → ℝ)
    (hf : MemLp f 2 (xLaw M)) (hfh : MemLp fh 2 (xLaw M))
    (hg : MemLp g 2 (xLaw M)) (hgh : MemLp gh 2 (xLaw M)) :
    finiteL2Error M (fun x => fh x - gh x) (fun x => f x - g x) ≤
      finiteL2Error M fh f + finiteL2Error M gh g := by
  have hp := hfh.sub hf
  have hq := hgh.sub hg
  have hid : (fun x => (fh x - gh x) - (f x - g x)) =
      (fun x => fh x - f x) - (fun x => gh x - g x) := by
    funext x
    simp only [Pi.sub_apply]
    ring
  have hd : MemLp (fun x => (fh x - gh x) - (f x - g x)) 2 (xLaw M) := by
    rw [hid]
    exact hp.sub hq
  rw [l2Error_eq_eLpNorm M _ _ hd, l2Error_eq_eLpNorm M _ _ hp,
    l2Error_eq_eLpNorm M _ _ hq, hid]
  exact (ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hp.eLpNorm_ne_top, hq.eLpNorm_ne_top⟩)
    (eLpNorm_sub_le hp.1 hq.1 (by norm_num))).trans_eq
      (ENNReal.toReal_add hp.eLpNorm_ne_top hq.eLpNorm_ne_top)

-- This closes the smooth affine-argument part of the binary branch proof.
-- All three hinge-argument rates come from the original nuisance rates;
-- the Lipschitz constant is extracted from the policy-smoothness assumption.
-- @node: nuisanceRates_hMinus_quarter_rate
/-- For [a valid policy](hyp:hphi) with [the specified derivative](hyp:hd)
that is [uniformly bounded and Lipschitz](hyp:hDerivative), suppose [reference](hyp:he0)
and [all fitted nuisances](hyp:heh) are admissible and [propensities](hyp:hrp),
[treatment-level propensities](hyp:hrlev), [treated-success probabilities](hyp:hrP),
and [all regular-level pooling shares](hyp:hrs) satisfy the componentwise
quarter-rate conditions. At [a treatment level below the maximum](hyp:hk)
and [an interior policy index](hyp:hj), [the L2 error of the negative hinge
component is negligible relative to the inverse fourth root of sample size,
along sample sizes twice n plus two](goal). -/
lemma nuisanceRates_hMinus_quarter_rate {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1)
    (hrs : ∀ a : RegularIndex L,
      FiniteNuisanceRates M μ (fun n t => (eh n t).share a) (e0.share a))
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    Causalean.Stat.IsLittleOp
      (fun n a => finiteL2Error M (hMinus phi L (eh (2*(n+1)) a) k j) (hMinus phi L e0 k j))
      (fun n => ((2*(n+1) : ℕ) : ℝ) ^ (-1/4 : ℝ)) μ := by
  obtain ⟨B, Lip, hB, hLip, hder⟩ := hDerivative
  have hlip := policy_lipschitz_of_derivative_bound phi dphi hd B
    (fun z x p hp => (hder z x p p hp hp).1)
  have hpool := nuisanceRates_pooledQBin_quarter_rate M μ phi hphi B hB hlip
    L e0 eh he0 heh hrp hrlev hrs
  have hlev := nuisanceRates_positiveValue M μ L.K _ _ hrlev
  have hJ := nuisanceRates_binFullJ_quarter_rate M μ L e0 eh he0 heh hrP
  have pos (e : NuisanceBin L) (he : BinAdmissible M L e) :
      MemLp (positiveValue e.pLev (k+1)) 2 (xLaw M) :=
    (fitted_positive_treatment_assignment_memLp M L e he (k+1)).1
  have gap (e : NuisanceBin L) (he : BinAdmissible M L e) :
      MemLp (binFullJ L e k) 2 (xLaw M) :=
    (fitted_positive_success_memLp M L e he (k+1)).sub
      (fitted_positive_success_memLp M L e he k)
  have hbr : Causalean.Stat.IsLittleOp
      (fun n a => finiteL2Error M
        (fun x => positiveValue (eh (2*(n+1)) a).pLev (k+1) x - binFullJ L (eh (2*(n+1)) a) k x)
        (fun x => positiveValue e0.pLev (k+1) x - binFullJ L e0 k x))
      (fun n => ((2*(n+1) : ℕ) : ℝ) ^ (-1/4 : ℝ)) μ := by
    have hs := (hlev (k+1)).add_eventually_nonneg_rate
      (Eventually.of_forall (fun _ => Real.rpow_nonneg (by positivity) _)) (hJ k)
    apply Causalean.Stat.IsLittleOp.of_abs_le_const_mul one_pos hs
    intro n a
    rw [one_mul, abs_of_nonneg (show 0 ≤ finiteL2Error M _ _ from Real.sqrt_nonneg _)]
    exact (dml_l2Error_sub_le M _ _ _ _ (pos e0 he0) (pos _ (heh _ a))
      (gap e0 he0) (gap _ (heh _ a))).trans (le_abs_self _)
  apply fitted_hMinus_quarter_rate M μ phi hphi L e0
    (fun n a => eh (2*(n+1)) a) he0 (fun n a => heh _ a) k j hk hj
  · intro n a
    exact (fitted_pooledQBin_memLp M phi hphi L _ (heh _ a) k j).sub
      (fitted_pooledQBin_memLp M phi hphi L e0 he0 k j)
  · intro n a
    exact (fitted_pooledQBin_memLp M phi hphi L _ (heh _ a) k (j-1)).sub
      (fitted_pooledQBin_memLp M phi hphi L e0 he0 k (j-1))
  · intro n a
    exact ((pos _ (heh _ a)).sub (gap _ (heh _ a))).sub ((pos e0 he0).sub (gap e0 he0))
  · exact hpool (k,j)
  · exact hpool (k,j-1)
  · exact hbr

-- The product remainder is now controlled directly by the original
-- nuisance rates, rather than a separate convergence premise for hMinus.
-- @node: nuisanceRates_regular_product_cross_root_n_negligible
/-- Assume [a valid policy](hyp:hphi) with [the specified derivative](hyp:hd)
that is [uniformly bounded and Lipschitz](hyp:hDerivative), [admissible reference](hyp:he0)
and [fitted nuisances](hyp:heh), and componentwise quarter-rate conditions for
[propensities](hyp:hrp), [treatment-level propensities](hyp:hrlev),
[treated-success probabilities](hyp:hrP), [pooling shares](hyp:hrs), and
[regular-level regression weights](hyp:hrg). At [a treatment level below the
maximum](hyp:hk) and [an interior policy index](hyp:hj), [the integral of the
regression-weight error times the negative-hinge error, evaluated at sample
sizes twice n plus two and multiplied by the square root of n plus one,
converges to zero in probability](goal). -/
lemma nuisanceRates_regular_product_cross_root_n_negligible
    {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (hd : PolicyDifferentiable phi dphi) (hDerivative : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e0 : NuisanceBin L) (eh : ℕ → A → NuisanceBin L)
    (he0 : BinAdmissible M L e0) (heh : ∀ n a, BinAdmissible M L (eh n a))
    (hrp : FiniteNuisanceRates M μ (fun n a => (eh n a).prop) e0.prop)
    (hrlev : FiniteNuisanceRates M μ (fun n a => (eh n a).pLev) e0.pLev)
    (hrP : FiniteNuisanceRates M μ (fun n a => (eh n a).P1) e0.P1)
    (hrs : ∀ a : RegularIndex L,
      FiniteNuisanceRates M μ (fun n t => (eh n t).share a) (e0.share a))
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gamma) e0.gamma)
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) *
        ∫ x, (regularValue (eh (2*(n+1)) a).gamma k j x - regularValue e0.gamma k j x) *
          (hMinus phi L (eh (2*(n+1)) a) k j x - hMinus phi L e0 k j x) ∂xLaw M)
      atTop (fun _ _ => 0) := by
  have hh := nuisanceRates_hMinus_quarter_rate M μ phi dphi hphi hd hDerivative
    L e0 eh he0 heh hrp hrlev hrP hrs k j hk hj
  have hi : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k := ⟨hk.le, hj⟩
  have hg (e : NuisanceBin L) : regularValue e.gamma k j = e.gamma ⟨(k,j), hi⟩ := by
    funext x
    simp only [regularValue, dif_pos hi]
  apply fitted_regular_product_cross_root_n_negligible M μ phi hphi L e0
    (fun n a => eh (2*(n+1)) a) he0 (fun n a => heh _ a) k j hk hj hh
  simpa only [hg] using hrg ⟨(k,j), hi⟩

end Papers.TbsPrteOptimalTransport
