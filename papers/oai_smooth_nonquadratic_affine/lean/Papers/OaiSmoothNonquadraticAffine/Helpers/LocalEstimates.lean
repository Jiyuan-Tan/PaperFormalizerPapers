module

public import Papers.OaiSmoothNonquadraticAffine.Helpers.LocalFixedPoint
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Uniform estimates for the local integral operator -/

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped NNReal ContDiff

namespace OaiSmoothNonquadraticAffine

-- @node: localScalarBox
/-- The [local scalar box](goal) consists of pairs whose two coordinates both lie
between one half and three halves, including the endpoints. -/
def localScalarBox : Set (ℝ × ℝ) :=
  Icc (1 / 2 : ℝ) (3 / 2) ×ˢ Icc (1 / 2 : ℝ) (3 / 2)

-- @node: localScalarAverages
/-- For [a pair of scalar values](hyp:z), the [scalar averaging map](goal) returns
the first value times the second to the power −12/11, and the second to the power −1/11. -/
def localScalarAverages (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1 * z.2 ^ (-radialGamma), z.2 ^ (1 - radialGamma))

-- @node: localScalarAverages_smooth
/-- The [scalar averaging map is infinitely differentiable on the box where both
coordinates lie between one half and three halves](goal). -/
lemma localScalarAverages_smooth : ContDiffOn ℝ ∞ localScalarAverages localScalarBox := by
  have hne : ∀ z ∈ localScalarBox, z.2 ≠ 0 := by
    intro z hz
    exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hz.2.1)
  exact (contDiff_fst.contDiffOn.mul
    (contDiff_snd.contDiffOn.rpow_const_of_ne hne)).prodMk
      (contDiff_snd.contDiffOn.rpow_const_of_ne hne)

-- @node: localWeightedMean_mono
/-- If [the first function is continuous](hyp:hf), [the second function is
continuous](hyp:hg), and [the first is no larger than the second throughout the
unit interval](hyp:hfg), then [their averages with density nine times the eighth
power of the argument have the same ordering](goal). -/
lemma localWeightedMean_mono {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ v ∈ Icc (0 : ℝ) 1, f v ≤ g v) :
    9 * (∫ v : ℝ in 0..1, v ^ 8 * f v) ≤
      9 * (∫ v : ℝ in 0..1, v ^ 8 * g v) := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((by fun_prop : Continuous (fun v => v ^ 8 * f v)).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun v => v ^ 8 * g v)).intervalIntegrable _ _)
  intro v hv
  exact mul_le_mul_of_nonneg_left (hfg v hv) (pow_nonneg hv.1 _)

-- @node: localWeightedMean_const
/-- For [a constant value](hyp:c), [averaging it over the unit interval with density
nine times the eighth power of the argument returns that same value](goal). -/
lemma localWeightedMean_const (c : ℝ) :
    9 * (∫ v : ℝ in 0..1, v ^ 8 * c) = c := by
  rw [intervalIntegral.integral_mul_const, integral_pow]
  ring_nf

-- @node: localWeightedMean_mem
/-- If [a function is continuous](hyp:hf) and [takes values between two bounds on
the unit interval](hyp:h), then [its average with density nine times the eighth
power of the argument lies between those same bounds](goal). -/
lemma localWeightedMean_mem {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ}
    (h : ∀ v ∈ Icc (0 : ℝ) 1, f v ∈ Icc a b) :
    9 * (∫ v : ℝ in 0..1, v ^ 8 * f v) ∈ Icc a b := by
  constructor
  · simpa only [localWeightedMean_const] using
      localWeightedMean_mono continuous_const hf (fun v hv => (h v hv).1)
  · simpa only [localWeightedMean_const] using
      localWeightedMean_mono hf continuous_const (fun v hv => (h v hv).2)

-- @node: localWeightedMean_sub_le
/-- If [the first function is continuous](hyp:hf), [the second is continuous](hyp:hg),
and [their absolute difference is at most C throughout the unit interval](hyp:h),
then [their averages with density nine times the eighth power of the argument
differ in absolute value by at most C](goal). -/
lemma localWeightedMean_sub_le {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {C : ℝ} (h : ∀ v ∈ Icc (0 : ℝ) 1, |f v - g v| ≤ C) :
    |9 * (∫ v : ℝ in 0..1, v ^ 8 * f v) -
      9 * (∫ v : ℝ in 0..1, v ^ 8 * g v)| ≤ C := by
  have hb := localWeightedMean_mem (hf.sub hg)
    (a := -C) (b := C) (fun v hv => abs_le.mp (h v hv))
  simp_rw [Pi.sub_apply, mul_sub] at hb
  rw [intervalIntegral.integral_sub
    ((by fun_prop : Continuous (fun v => v ^ 8 * f v)).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun v => v ^ 8 * g v)).intervalIntegrable _ _)] at hb
  simpa only [mul_sub, abs_le, mem_Icc] using hb

-- @node: localScalarAverages_bounds
/-- There [exist bounds a and b with a positive and no larger than b, such that
throughout the local scalar box the first scalar average lies between a and b
and the second lies between −b and b](goal). -/
lemma localScalarAverages_bounds : ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧
    ∀ z ∈ localScalarBox,
      (localScalarAverages z).1 ∈ Icc a b ∧ (localScalarAverages z).2 ∈ Icc (-b) b := by
  have hc : IsCompact localScalarBox := isCompact_Icc.prod isCompact_Icc
  have hne : localScalarBox.Nonempty := ⟨(1, 1), by norm_num [localScalarBox]⟩
  obtain ⟨z₀, hz₀, hmin⟩ := hc.exists_isMinOn hne localScalarAverages_smooth.continuousOn.fst
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuousOn localScalarAverages_smooth.continuousOn
  have hpos : 0 < (localScalarAverages z₀).1 := by
    exact mul_pos (by have := hz₀.1.1; linarith)
      (Real.rpow_pos_of_pos (by have := hz₀.2.1; linarith) _)
  have hfst (z : ℝ × ℝ) (hz : z ∈ localScalarBox) : |(localScalarAverages z).1| ≤ B :=
    (le_max_left _ _).trans (hB z hz)
  have hsnd (z : ℝ × ℝ) (hz : z ∈ localScalarBox) : |(localScalarAverages z).2| ≤ B :=
    (le_max_right _ _).trans (hB z hz)
  refine ⟨(localScalarAverages z₀).1, B, hpos,
    (le_abs_self _).trans (hfst z₀ hz₀), ?_⟩
  intro z hz
  exact ⟨⟨hmin hz, (le_abs_self _).trans (hfst z hz)⟩, abs_le.mp (hsnd z hz)⟩

-- @node: localScalarAverages_lipschitz
/-- The [scalar averaging map has a finite nonnegative Lipschitz constant on the
local scalar box](goal): distances between outputs are bounded by that constant
times the corresponding input distances. -/
lemma localScalarAverages_lipschitz :
    ∃ K : ℝ≥0, LipschitzOnWith K localScalarAverages localScalarBox :=
  localScalarAverages_smooth.exists_lipschitzOnWith (by simp)
    ((convex_Icc _ _).prod (convex_Icc _ _)) (isCompact_Icc.prod isCompact_Icc)

-- @node: localTrialVector
/-- Given [a positive interval radius](hyp:hδ), [a pair of continuous trial
functions on that interval](hyp:fp), and [a real auxiliary argument](hyp:s), the
[trial vector](goal) consists of their values at that argument, extending each
function constantly beyond the interval endpoints. -/
def localTrialVector {δ : ℝ} (hδ : 0 < δ) (fp : LocalTrialPair δ) (s : ℝ) : ℝ × ℝ :=
  (localTrialExtension δ hδ fp.1 s, localTrialExtension δ hδ fp.2 s)

-- @node: localTrialVector_mem
/-- For [a positive interval radius](hyp:hδ) and [a trial pair whose components
stay within one half of one](hyp:hfp), [the extended trial vector at any real
auxiliary argument](hyp:s) [belongs to the local scalar box](goal). -/
lemma localTrialVector_mem {δ : ℝ} (hδ : 0 < δ) {fp : LocalTrialPair δ}
    (hfp : fp ∈ localTrialSet δ) (s : ℝ) : localTrialVector hδ fp s ∈ localScalarBox :=
  localTrialExtension_mem hδ hfp s

-- @node: localTrialVector_dist_le
/-- For [a positive interval radius](hyp:hδ), [two continuous trial pairs](hyp:fp,gp),
and [any real auxiliary argument](hyp:s), [the distance between their extended
trial vectors is at most the supremum distance between the trial pairs](goal). -/
lemma localTrialVector_dist_le {δ : ℝ} (hδ : 0 < δ) (fp gp : LocalTrialPair δ) (s : ℝ) :
    dist (localTrialVector hδ fp s) (localTrialVector hδ gp s) ≤ dist fp gp := by
  apply max_le
  · exact (ContinuousMap.dist_apply_le_dist _).trans (le_max_left _ _)
  · exact (ContinuousMap.dist_apply_le_dist _).trans (le_max_right _ _)

-- @node: localNormalizedAverages
/-- Given [a positive interval radius](hyp:hδ), [a continuous trial pair](hyp:fp),
and [a real auxiliary argument s](hyp:s), the [normalized averages](goal) are the
averages of both scalar-map outputs evaluated on the extended trial vector at
v²s, integrating v from zero to one with density 9v⁸. -/
def localNormalizedAverages {δ : ℝ} (hδ : 0 < δ) (fp : LocalTrialPair δ) (s : ℝ) : ℝ × ℝ :=
  (9 * ∫ v : ℝ in 0..1, v ^ 8 * (localScalarAverages (localTrialVector hδ fp (v ^ 2 * s))).1,
   9 * ∫ v : ℝ in 0..1, v ^ 8 * (localScalarAverages (localTrialVector hδ fp (v ^ 2 * s))).2)

-- @node: localScalarTrial_continuous
/-- For [a positive interval radius](hyp:hδ), [a trial pair whose components stay
within one half of one](hyp:hfp), and [a fixed real auxiliary argument s](hyp:s),
[applying the scalar averaging map to the extended trial vector at v²s gives a
continuous function of v on the real line](goal). -/
@[fun_prop] lemma localScalarTrial_continuous {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ) (s : ℝ) :
    Continuous (fun v => localScalarAverages (localTrialVector hδ fp (v ^ 2 * s))) := by
  apply localScalarAverages_smooth.continuousOn.comp_continuous
  · unfold localTrialVector
    fun_prop
  · intro v
    exact localTrialVector_mem hδ hfp _

-- @node: localNormalizedAverages_mem
/-- Suppose [the scalar averaging map sends the local box into the rectangle
with coordinate bounds a to b and −b to b](hyp:hb). For [a positive interval
radius](hyp:hδ), [a trial pair whose components stay within one half of one](hyp:hfp),
and [any real auxiliary argument](hyp:s), [the normalized averages belong to
that same rectangle](goal). -/
lemma localNormalizedAverages_mem {a b δ : ℝ}
    (hb : ∀ z ∈ localScalarBox,
      (localScalarAverages z).1 ∈ Icc a b ∧ (localScalarAverages z).2 ∈ Icc (-b) b)
    (hδ : 0 < δ) {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ) (s : ℝ) :
    localNormalizedAverages hδ fp s ∈ Icc a b ×ˢ Icc (-b) b := by
  constructor
  · apply localWeightedMean_mem (localScalarTrial_continuous hδ hfp s).fst
    intro v hv
    exact (hb _ (localTrialVector_mem hδ hfp _)).1
  · apply localWeightedMean_mem (localScalarTrial_continuous hδ hfp s).snd
    intro v hv
    exact (hb _ (localTrialVector_mem hδ hfp _)).2

-- @node: localNormalizedAverages_dist_le
/-- If [the scalar averaging map is Lipschitz with constant K on the local
box](hyp:hK), then for [a positive interval radius](hyp:hδ), [a first trial pair
whose components stay within one half of one](hyp:hfp), [a second such trial
pair](hyp:hgp), and [any real auxiliary argument](hyp:s), [the distance between
their normalized averages is at most K times the supremum distance between the
trial pairs](goal). -/
lemma localNormalizedAverages_dist_le {K : ℝ≥0}
    (hK : LipschitzOnWith K localScalarAverages localScalarBox)
    {δ : ℝ} (hδ : 0 < δ) {fp gp : LocalTrialPair δ}
    (hfp : fp ∈ localTrialSet δ) (hgp : gp ∈ localTrialSet δ) (s : ℝ) :
    dist (localNormalizedAverages hδ fp s) (localNormalizedAverages hδ gp s) ≤ K * dist fp gp := by
  have hb (v : ℝ) :
      dist (localScalarAverages (localTrialVector hδ fp (v ^ 2 * s)))
        (localScalarAverages (localTrialVector hδ gp (v ^ 2 * s))) ≤ K * dist fp gp :=
    (hK.dist_le_mul _ (localTrialVector_mem hδ hfp _) _ (localTrialVector_mem hδ hgp _)).trans
      (mul_le_mul_of_nonneg_left (localTrialVector_dist_le hδ fp gp _) K.coe_nonneg)
  apply max_le
  · apply localWeightedMean_sub_le (localScalarTrial_continuous hδ hfp s).fst
      (localScalarTrial_continuous hδ hgp s).fst
    intro v hv
    exact (le_max_left _ _).trans (hb v)
  · apply localWeightedMean_sub_le (localScalarTrial_continuous hδ hfp s).snd
      (localScalarTrial_continuous hδ hgp s).snd
    intro v hv
    exact (le_max_right _ _).trans (hb v)

-- @node: localAuxiliaryField
/-- For [a pair of normalized averages](hyp:z), the [auxiliary derivative
field](goal) returns the ninth root of the first average and minus eleven ninths
times the second average times that root raised to one minus the radial dimension. -/
def localAuxiliaryField (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1 ^ (1 / 9 : ℝ),
    -radialK * (z.2 / 9) * (z.1 ^ (1 / 9 : ℝ)) ^ (1 - (radialDim : ℝ)))

-- @node: localAuxiliaryField_smooth
/-- If [the lower bound a is positive](hyp:ha), then [the auxiliary derivative
field is infinitely differentiable on the rectangle with coordinate bounds a
to b and −b to b](goal). -/
lemma localAuxiliaryField_smooth {a b : ℝ} (ha : 0 < a) :
    ContDiffOn ℝ ∞ localAuxiliaryField (Icc a b ×ˢ Icc (-b) b) := by
  have hroot : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => z.1 ^ (1 / 9 : ℝ))
      (Icc a b ×ˢ Icc (-b) b) :=
    contDiff_fst.contDiffOn.rpow_const_of_ne (fun z hz => (ha.trans_le hz.1.1).ne')
  have hpow := hroot.rpow_const_of_ne (p := 1 - (radialDim : ℝ))
    (fun z hz => (Real.rpow_pos_of_pos (ha.trans_le hz.1.1) _).ne')
  exact hroot.prodMk (((contDiffOn_const.mul (contDiff_snd.contDiffOn.div_const 9))).mul hpow)

-- @node: localDifferentialValues
/-- Given [a positive interval radius](hyp:hδ), [a continuous trial pair](hyp:fp)
[whose components stay within one half of one](hyp:hfp), and [a real auxiliary
argument](hyp:s), the [prescribed derivative pair](goal) consists of the positive
ninth-root average q and minus eleven times the flux average j times q raised
to one minus the radial dimension, all evaluated at that argument. -/
def localDifferentialValues {δ : ℝ} (hδ : 0 < δ) (fp : LocalTrialPair δ)
    (hfp : fp ∈ localTrialSet δ) (s : ℝ) : ℝ × ℝ :=
  (localQ δ hδ fp hfp s,
    -radialK * localJ δ hδ fp hfp s * localQ δ hδ fp hfp s ^ (1 - (radialDim : ℝ)))

-- @node: localDifferentialValues_eq
/-- For [a positive interval radius](hyp:hδ), [a trial pair whose components
stay within one half of one](hyp:hfp), and [any real auxiliary argument](hyp:s),
[the prescribed derivative pair equals the auxiliary derivative field evaluated
at the normalized averages](goal). -/
lemma localDifferentialValues_eq {δ : ℝ} (hδ : 0 < δ) {fp : LocalTrialPair δ}
    (hfp : fp ∈ localTrialSet δ) (s : ℝ) :
    localDifferentialValues hδ fp hfp s =
      localAuxiliaryField (localNormalizedAverages hδ fp s) := by
  simp [localDifferentialValues, localAuxiliaryField, localNormalizedAverages,
    localScalarAverages, localTrialVector, localQ, localJ, mul_assoc]

-- @node: localDifferentialValues_continuous
/-- For [a positive interval radius](hyp:hδ) and [a trial pair whose components
stay within one half of one](hyp:hfp), [the prescribed derivative pair is a
continuous function of the real auxiliary argument](goal). -/
@[fun_prop] lemma localDifferentialValues_continuous {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ) :
    Continuous (localDifferentialValues hδ fp hfp) := by
  have hq := localQ_continuous hδ hfp
  have hj := localJ_continuous hδ hfp
  exact hq.prodMk ((continuous_const.mul hj).mul
    (hq.rpow_const (fun s => Or.inl (localQ_pos hδ hfp s).ne')))

-- @node: localDifferentialValues_uniform_bounds
/-- There [exist nonnegative constants M and L, independent of the positive
interval radius, such that every trial pair whose components stay within one
half of one has prescribed derivative norm at most M at every real argument,
and the derivative pairs of any two such trials are at distance at most L times
their supremum distance](goal). -/
lemma localDifferentialValues_uniform_bounds :
    ∃ M L : ℝ, 0 ≤ M ∧ 0 ≤ L ∧
      ∀ (δ : ℝ) (hδ : 0 < δ) (fp : LocalTrialPair δ) (hfp : fp ∈ localTrialSet δ),
        (∀ s, ‖localDifferentialValues hδ fp hfp s‖ ≤ M) ∧
        ∀ (gp : LocalTrialPair δ) (hgp : gp ∈ localTrialSet δ) s,
          dist (localDifferentialValues hδ fp hfp s) (localDifferentialValues hδ gp hgp s) ≤
            L * dist fp gp := by
  obtain ⟨a, b, ha, hab, hb⟩ := localScalarAverages_bounds
  obtain ⟨K₀, hK₀⟩ := localScalarAverages_lipschitz
  have hc : IsCompact (Icc a b ×ˢ Icc (-b) b) := isCompact_Icc.prod isCompact_Icc
  have hs := localAuxiliaryField_smooth (b := b) ha
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuousOn hs.continuousOn
  obtain ⟨K₁, hK₁⟩ := hs.exists_lipschitzOnWith (by simp)
    ((convex_Icc _ _).prod (convex_Icc _ _)) hc
  refine ⟨max 0 M, K₁ * K₀, le_max_left _ _, mul_nonneg K₁.coe_nonneg K₀.coe_nonneg, ?_⟩
  intro δ hδ fp hfp
  constructor
  · intro s
    rw [localDifferentialValues_eq]
    exact (hM _ (localNormalizedAverages_mem hb hδ hfp s)).trans (le_max_right _ _)
  · intro gp hgp s
    rw [localDifferentialValues_eq hδ hfp, localDifferentialValues_eq hδ hgp]
    calc
      _ ≤ K₁ * dist (localNormalizedAverages hδ fp s) (localNormalizedAverages hδ gp s) :=
        hK₁.dist_le_mul _ (localNormalizedAverages_mem hb hδ hfp s)
          _ (localNormalizedAverages_mem hb hδ hgp s)
      _ ≤ K₁ * (K₀ * dist fp gp) := mul_le_mul_of_nonneg_left
        (localNormalizedAverages_dist_le hK₀ hδ hfp hgp s) K₁.coe_nonneg
      _ = (K₁ : ℝ) * K₀ * dist fp gp := (mul_assoc _ _ _).symm

-- @node: localTransformValues_integrals
/-- For [a positive interval radius](hyp:hδ), [a trial pair whose components
stay within one half of one](hyp:hfp), and [an auxiliary argument in the closed
interval from minus the radius to the radius](hyp:s), [each component of the
integral transform equals one plus the integral from zero to that argument of
the corresponding prescribed derivative](goal). -/
lemma localTransformValues_integrals {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ) (s : Icc (-δ) δ) :
    localTransformValues δ hδ fp hfp s =
      (1 + ∫ a : ℝ in 0..(s : ℝ), (localDifferentialValues hδ fp hfp a).1,
       1 + ∫ a : ℝ in 0..(s : ℝ), (localDifferentialValues hδ fp hfp a).2) := by
  simp only [localTransformValues, localDifferentialValues, mul_assoc,
    intervalIntegral.integral_const_mul]
  congr 1
  ring

-- @node: localIntegral_bound
/-- If [C is nonnegative](hyp:hC) and [a real function has absolute value at
most C everywhere](hyp:hf), then for [an endpoint in the closed interval from
−δ to δ](hyp:s), [the absolute value of its integral from zero to that endpoint
is at most Cδ](goal). -/
lemma localIntegral_bound {δ C : ℝ} (hC : 0 ≤ C) {f : ℝ → ℝ}
    (hf : ∀ a, ‖f a‖ ≤ C) (s : Icc (-δ) δ) :
    ‖∫ a : ℝ in 0..(s : ℝ), f a‖ ≤ C * δ := by
  have hs : |(s : ℝ)| ≤ δ := abs_le.mpr s.property
  calc
    _ ≤ C * |(s : ℝ) - 0| := intervalIntegral.norm_integral_le_of_norm_le_const (fun a _ => hf a)
    _ ≤ C * δ := by simpa only [sub_zero] using mul_le_mul_of_nonneg_left hs hC

-- @node: localIntegral_sub_bound
/-- If [C is nonnegative](hyp:hC), [the first function is continuous](hyp:hf),
[the second is continuous](hyp:hg), and [their absolute difference is at most C
everywhere](hyp:hfg), then for [an endpoint in the closed interval from −δ to
δ](hyp:s), [the quantities obtained by adding one to their integrals from zero
to that endpoint differ in absolute value by at most Cδ](goal). -/
lemma localIntegral_sub_bound {δ C : ℝ} (hC : 0 ≤ C) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hfg : ∀ a, |f a - g a| ≤ C)
    (s : Icc (-δ) δ) :
    |(1 + ∫ a : ℝ in 0..(s : ℝ), f a) -
      (1 + ∫ a : ℝ in 0..(s : ℝ), g a)| ≤ C * δ := by
  have hb := localIntegral_bound hC
    (f := fun a => f a - g a) (fun a => by simpa only [Real.norm_eq_abs] using hfg a) s
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)] at hb
  simpa only [add_sub_add_left_eq_sub, Real.norm_eq_abs] using hb

-- @node: exists_localContractionBounds
/-- There [exist constants M and L, independent of the positive interval radius
δ, such that the integral transform of any trial pair within one half of one
deviates from the constant pair one by at most Mδ, and transforms of any two
such trial pairs differ by at most Lδ times their supremum distance, uniformly
on the auxiliary interval](goal). -/
lemma exists_localContractionBounds : ∃ M L : ℝ, LocalContractionBounds M L := by
  obtain ⟨M, L, hM, hL, hb⟩ := localDifferentialValues_uniform_bounds
  refine ⟨M, L, ?_⟩
  intro δ hδ fp hfp
  have hfpcont := localDifferentialValues_continuous hδ hfp
  constructor
  · intro s
    rw [localTransformValues_integrals hδ hfp s]
    simp only [add_sub_cancel_left]
    apply max_le
    · exact localIntegral_bound hM (fun a => (le_max_left _ _).trans ((hb δ hδ fp hfp).1 a)) s
    · exact localIntegral_bound hM (fun a => (le_max_right _ _).trans ((hb δ hδ fp hfp).1 a)) s
  · intro gp hgp s
    have hgpcont := localDifferentialValues_continuous hδ hgp
    have hnonneg : 0 ≤ L * dist fp gp := mul_nonneg hL dist_nonneg
    have hdist := (hb δ hδ fp hfp).2 gp hgp
    rw [localTransformValues_integrals hδ hfp s, localTransformValues_integrals hδ hgp s]
    apply max_le
    · exact (localIntegral_sub_bound hnonneg hfpcont.fst hgpcont.fst
        (fun a => (le_max_left _ _).trans (hdist a)) s).trans_eq (by ring)
    · exact (localIntegral_sub_bound hnonneg hfpcont.snd hgpcont.snd
        (fun a => (le_max_right _ _).trans (hdist a)) s).trans_eq (by ring)

-- @node: exists_local_integral_solution
/-- There [exist a positive interval radius and a continuous trial pair whose
components stay within one half of one, such that the pair equals its integral
transform at every point of the auxiliary interval](goal). -/
lemma exists_local_integral_solution :
    ∃ (δ : ℝ) (hδ : 0 < δ) (fp : LocalTrialPair δ) (hfp : fp ∈ localTrialSet δ),
      ∀ s, (fp.1 s, fp.2 s) = localTransformValues δ hδ fp hfp s := by
  obtain ⟨M, L, hb⟩ := exists_localContractionBounds
  obtain ⟨δ, hδ, fp, hfp, _, hfix⟩ := exists_local_integral_fixedPoint hb
  exact ⟨δ, hδ, fp, hfp, hfix⟩

-- @node: localIntegralPrimitives
/-- Given [a positive interval radius](hyp:hδ), [a continuous trial pair](hyp:fp)
[whose components stay within one half of one](hyp:hfp), and [a real auxiliary
argument](hyp:s), the [integral primitive pair](goal) consists of one plus the
integral from zero to that argument of each prescribed derivative component. -/
def localIntegralPrimitives {δ : ℝ} (hδ : 0 < δ) (fp : LocalTrialPair δ)
    (hfp : fp ∈ localTrialSet δ) (s : ℝ) : ℝ × ℝ :=
  (1 + ∫ a : ℝ in 0..s, (localDifferentialValues hδ fp hfp a).1,
   1 + ∫ a : ℝ in 0..s, (localDifferentialValues hδ fp hfp a).2)

-- @node: localIntegralPrimitives_hasDerivAt
/-- For [a positive interval radius](hyp:hδ), [a trial pair whose components
stay within one half of one](hyp:hfp), and [any real auxiliary argument](hyp:s),
[each integral primitive has derivative equal to the corresponding prescribed
derivative component at that argument](goal). -/
lemma localIntegralPrimitives_hasDerivAt {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ) (s : ℝ) :
    HasDerivAt (fun a => (localIntegralPrimitives hδ fp hfp a).1)
      (localDifferentialValues hδ fp hfp s).1 s ∧
    HasDerivAt (fun a => (localIntegralPrimitives hδ fp hfp a).2)
      (localDifferentialValues hδ fp hfp s).2 s := by
  have hc := localDifferentialValues_continuous hδ hfp
  exact ⟨(hc.fst.integral_hasStrictDerivAt 0 s).hasDerivAt.const_add 1,
    (hc.snd.integral_hasStrictDerivAt 0 s).hasDerivAt.const_add 1⟩

-- @node: localFixedPoint_extension_eq
/-- For [a positive interval radius](hyp:hδ) and [a trial pair whose components
stay within one half of one](hyp:hfp), if [the pair equals its integral transform
throughout the auxiliary interval](hyp:hfix), then at [any point of the closed
interval from minus the radius to the radius](hyp:s), [the extended trial pair
equals the integral primitive pair](goal). -/
lemma localFixedPoint_extension_eq {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ)
    (hfix : ∀ s, (fp.1 s, fp.2 s) = localTransformValues δ hδ fp hfp s)
    (s : Icc (-δ) δ) :
    (localTrialExtension δ hδ fp.1 s, localTrialExtension δ hδ fp.2 s) =
      localIntegralPrimitives hδ fp hfp s := by
  rw [localTrialExtension_eq, localTrialExtension_eq, hfix s,
    localTransformValues_integrals]
  rfl

-- @node: localFixedPoint_averages_zero
/-- For [a positive interval radius](hyp:hδ) and [a trial pair whose components
stay within one half of one](hyp:hfp), if [the pair equals its integral transform
throughout the auxiliary interval](hyp:hfix), then [at zero the positive
ninth-root average q equals one and the flux average j equals one ninth](goal). -/
lemma localFixedPoint_averages_zero {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ)
    (hfix : ∀ s, (fp.1 s, fp.2 s) = localTransformValues δ hδ fp hfp s) :
    localQ δ hδ fp hfp 0 = 1 ∧ localJ δ hδ fp hfp 0 = 1 / 9 := by
  let s₀ : Icc (-δ) δ := ⟨0, by constructor <;> linarith⟩
  have hzero := localFixedPoint_extension_eq hδ hfp hfix s₀
  have hF : localTrialExtension δ hδ fp.1 0 = 1 := by
    simpa only [s₀, localIntegralPrimitives, intervalIntegral.integral_same, add_zero]
      using congrArg Prod.fst hzero
  have hP : localTrialExtension δ hδ fp.2 0 = 1 := by
    simpa only [s₀, localIntegralPrimitives, intervalIntegral.integral_same, add_zero]
      using congrArg Prod.snd hzero
  constructor <;> norm_num [localQ, localJ, hF, hP, integral_pow]

-- @node: localFixedPoint_initial_derivatives
/-- For [a positive interval radius](hyp:hδ) and [a trial pair whose components
stay within one half of one](hyp:hfp), if [the pair equals its integral transform
throughout the auxiliary interval](hyp:hfix), then [the first and second integral
primitives have derivatives one and minus eleven ninths, respectively, at
zero](goal). -/
lemma localFixedPoint_initial_derivatives {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ)
    (hfix : ∀ s, (fp.1 s, fp.2 s) = localTransformValues δ hδ fp hfp s) :
    HasDerivAt (fun s => (localIntegralPrimitives hδ fp hfp s).1) 1 0 ∧
    HasDerivAt (fun s => (localIntegralPrimitives hδ fp hfp s).2) (-(11 / 9 : ℝ)) 0 := by
  obtain ⟨hq, hj⟩ := localFixedPoint_averages_zero hδ hfp hfix
  have hd := localIntegralPrimitives_hasDerivAt hδ hfp 0
  norm_num [localDifferentialValues, hq, hj, radialK] at hd ⊢
  exact hd

end OaiSmoothNonquadraticAffine
