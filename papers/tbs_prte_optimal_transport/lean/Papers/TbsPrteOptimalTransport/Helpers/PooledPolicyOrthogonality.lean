module
public import Papers.TbsPrteOptimalTransport.Helpers.PooledPolicyDirections
public import Papers.TbsPrteOptimalTransport.Helpers.PopulationBinaryAdmissibility
public import Mathlib.Analysis.Calculus.Deriv.Slope
/-! Simultaneous propensity, simplex-share, and denominator paths for pooled policy levels.
The policy derivative need only be Lipschitz; no second derivative is used. -/
public section

set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open scoped Topology Classical
universe v

-- The coefficient can be merely continuous: its changes multiply the zero
-- residual mean at t=0. This avoids assuming differentiability of dphi.
-- @node: continuous_coefficient_times_path_deriv
/-- If [a coefficient function is continuous at zero](hyp:hf), then [path time
times that coefficient has derivative equal to the coefficient's value at zero](goal). -/
lemma continuous_coefficient_times_path_deriv (f : ℝ → ℝ)
    (hf : ContinuousAt f 0) : HasDerivAt (fun t => t * f t) (f 0) 0 := by
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  have ht : Tendsto f (𝓝[≠] 0) (𝓝 (f 0)) := hf.tendsto.mono_left nhdsWithin_le_nhds
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hn : t ≠ 0 := by simpa using ht
  simp [smul_eq_mul, hn]

-- This is the conditional policy cancellation with all three groups varying
-- together. The conditional law is held fixed, so pi is the true atom mass.
-- @node: pooled_policy_debiased_joint_path_orthogonality
/-- Suppose [the policy transformations have the specified derivatives](hyp:hd),
[those derivatives are uniformly bounded and Lipschitz on the unit interval](hyp:hL),
[the pooling denominator is nonzero](hyp:htau), [baseline shares are instrument masses
divided by that denominator](hyp:ha), [baseline propensities lie in the unit interval](hyp:hp),
[their affine paths remain there near zero](hyp:hpath), [all transformed baseline
propensities equal q](hyp:hq), and [share directions sum to zero](hyp:hda). Then
[the pooled policy minus path time times the propensity correction has derivative
zero at zero, even when propensities, shares, and the denominator vary together](goal). -/
lemma pooled_policy_debiased_joint_path_orthogonality {X Z : Type v}
    (phi dphi : Z → X → ℝ → ℝ) (hd : PolicyDifferentiable phi dphi)
    (hL : PolicyDerivativeBoundedLipschitz dphi)
    (s : Finset Z) (x : X) (p dp a da pi : Z → ℝ) (q tau dtau : ℝ)
    (htau : tau ≠ 0) (ha : ∀ z ∈ s, a z = pi z / tau)
    (hp : ∀ z ∈ s, p z ∈ Icc (0 : ℝ) 1)
    (hpath : ∀ z ∈ s, ∀ᶠ t : ℝ in 𝓝 0, p z + t * dp z ∈ Icc (0 : ℝ) 1)
    (hq : ∀ z ∈ s, phi z x (p z) = q) (hda : ∑ z ∈ s, da z = 0) :
    HasDerivAt (fun t : ℝ =>
      (∑ z ∈ s, (a z + t * da z) * phi z x (p z + t * dp z)) -
      t * ((tau + t * dtau)⁻¹ *
        ∑ z ∈ s, pi z * dphi z x (p z + t * dp z) * dp z)) 0 0 := by
  have hc : ContinuousAt (fun t : ℝ => (tau + t * dtau)⁻¹ *
      ∑ z ∈ s, pi z * dphi z x (p z + t * dp z) * dp z) 0 := by
    apply ContinuousAt.mul
    · apply ContinuousAt.inv₀
      · fun_prop
      · simpa using htau
    · have hc : ∀ z ∈ s, ContinuousAt (fun t : ℝ =>
          pi z * dphi z x (p z + t * dp z) * dp z) 0 := by
        intro z hz
        have hdc : ContinuousAt (fun t : ℝ => dphi z x (p z + t * dp z)) 0 := by
          obtain ⟨C, L, hC, hL0, hb⟩ := hL
          have hlip : LipschitzOnWith ⟨L, hL0⟩ (dphi z x) (Icc 0 1) := by
            apply LipschitzOnWith.of_dist_le_mul
            intro a ha b hb'
            change dist (dphi z x a) (dphi z x b) ≤ L * dist a b
            simpa only [Real.dist_eq] using (hb z x a b ha hb').2
          have ha : Tendsto (fun t : ℝ => p z + t * dp z) (𝓝 0) (𝓝 (p z)) := by
            simpa using ((continuousAt_id (x := (0 : ℝ))).mul_const (dp z)).const_add (p z)
              |>.tendsto
          have ht : Tendsto (fun t : ℝ => p z + t * dp z) (𝓝 0) (𝓝[Icc 0 1] (p z)) :=
            tendsto_nhdsWithin_iff.mpr ⟨ha, hpath z hz⟩
          change Tendsto (fun t : ℝ => dphi z x (p z + t * dp z)) (𝓝 0)
            (𝓝 (dphi z x (p z + 0 * dp z)))
          simpa only [Function.comp_def, zero_mul, add_zero] using
            (hlip.continuousOn (p z) (hp z hz)).tendsto.comp ht
        exact (hdc.const_mul (pi z)).mul_const (dp z)
      exact tendsto_finsetSum s (fun z hz => (hc z hz).tendsto)
  have hplugin := pooled_policy_simplex_derivative s a da p dp
    (fun z => phi z x) (fun z => dphi z x) q
    (fun z hz => policy_admissible_affine_derivative (phi z x) (p z) (dp z)
      (dphi z x (p z)) (hd z x (p z) (hp z hz)) (hpath z hz)) hda hq
  have h := hplugin.sub (continuous_coefficient_times_path_deriv _ hc)
  have heq : (∑ z ∈ s, a z * dphi z x (p z) * dp z) -
      ((tau + 0 * dtau)⁻¹ * ∑ z ∈ s, pi z * dphi z x (p z + 0 * dp z) * dp z) = 0 := by
    simp only [zero_mul, add_zero]
    rw [Finset.mul_sum]
    have hh : (∑ z ∈ s, a z * dphi z x (p z) * dp z) =
        ∑ z ∈ s, tau⁻¹ * (pi z * dphi z x (p z) * dp z) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [ha z hz, div_eq_mul_inv]
      ring
    rw [hh, sub_self]
  rw [heq] at h
  exact h

-- Rq is affine in W. Thus replacing W by its conditional mean and averaging
-- over the true instrument masses computes its conditional mean exactly.
-- @node: RqBin_finite_conditional_mean
/-- [Averaging the binary policy correction over instrument masses, with treatment
replaced by its instrument-specific mean p, gives zero at boundary or out-of-range
policy indices and otherwise gives the inverse pooling denominator times the sum
over the policy pool of instrument mass times policy derivative times the difference
between p and the nuisance propensity](goal). -/
lemma RqBin_finite_conditional_mean {X Z : Type v} [Fintype Z] [DecidableEq Z]
    (dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e : NuisanceBin L)
    (k j : ℕ) (x : X) (pi p : Z → ℝ) :
    (∑ z, pi z * RqBin dphi L e k j (x, z, p z, 0)) =
      if j = 0 ∨ L.l k < j then 0 else
        (regularValue e.tauLev k j x)⁻¹ *
          ∑ z ∈ L.T k j, pi z * dphi z x (e.prop z x) * (p z - e.prop z x) := by
  by_cases hbad : j = 0 ∨ L.l k < j
  · simp only [RqBin, if_pos hbad, mul_zero, Finset.sum_const_zero]
  · simp only [RqBin, if_neg hbad]
    simp_rw [mul_assoc (pi _) _ _, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z hz
    simp only [indicator, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ z]
    simp only [Finset.mem_univ, if_true]
    ring

-- This connects the joint-path cancellation to the actual pooled level and
-- policy correction used by the binary score. Other nuisance fields are fixed.
-- @node: pooledQBin_policy_correction_joint_orthogonality
/-- Suppose [the policy transformations have the specified derivatives](hyp:hd),
[the derivatives are uniformly bounded and Lipschitz on the unit interval](hyp:hL),
[the baseline pooling denominator is nonzero](hyp:htau), [shares equal instrument
masses divided by that denominator](hyp:hshare), [baseline propensities lie in the
unit interval](hyp:hp), [their affine paths stay there near zero](hyp:hpath),
[transformed propensities share the value q in the pool](hyp:hq), and [share
directions sum to zero](hyp:hda). Then [the binary pooled policy plus its correction
averaged over the fixed instrument masses and baseline treatment means has derivative
zero along the joint propensity, share, and denominator path](goal). -/
lemma pooledQBin_policy_correction_joint_orthogonality {X Z : Type v}
    [Fintype Z] [DecidableEq Z]
    (phi dphi : Z → X → ℝ → ℝ) (hd : PolicyDifferentiable phi dphi)
    (hL : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (e : NuisanceBin L)
    (dp : Z → X → ℝ) (da : RegularIndex L → Z → X → ℝ)
    (dtau : RegularIndex L → X → ℝ)
    (a : RegularIndex L) (x : X) (pi : Z → ℝ) (q : ℝ)
    (htau : e.tauLev a x ≠ 0)
    (hshare : ∀ z ∈ L.T a.val.1 a.val.2, e.share a z x = pi z / e.tauLev a x)
    (hp : ∀ z ∈ L.T a.val.1 a.val.2, e.prop z x ∈ Icc (0 : ℝ) 1)
    (hpath : ∀ z ∈ L.T a.val.1 a.val.2,
      ∀ᶠ t : ℝ in 𝓝 0, e.prop z x + t * dp z x ∈ Icc (0 : ℝ) 1)
    (hq : ∀ z ∈ L.T a.val.1 a.val.2, phi z x (e.prop z x) = q)
    (hda : ∑ z ∈ L.T a.val.1 a.val.2, da a z x = 0) :
    HasDerivAt (fun t : ℝ =>
      let et := {e with
        prop := fun z x => e.prop z x + t * dp z x
        share := fun a z x => e.share a z x + t * da a z x
        tauLev := fun a x => e.tauLev a x + t * dtau a x}
      pooledQBin phi L et a.val.1 a.val.2 x +
        ∑ z, pi z * RqBin dphi L et a.val.1 a.val.2 (x, z, e.prop z x, 0)) 0 0 := by
  have hj0 : a.val.2 ≠ 0 := by have := a.property; omega
  have hj : ¬L.l a.val.1 < a.val.2 := by have := a.property; omega
  have hbad : ¬(a.val.2 = 0 ∨ L.l a.val.1 < a.val.2) := by tauto
  have h := pooled_policy_debiased_joint_path_orthogonality phi dphi hd hL
    (L.T a.val.1 a.val.2) x (fun z => e.prop z x) (fun z => dp z x)
    (fun z => e.share a z x) (fun z => da a z x) pi q (e.tauLev a x) (dtau a x)
    htau hshare hp hpath hq hda
  convert h using 1
  funext t
  dsimp only
  erw [RqBin_finite_conditional_mean]
  simp only [pooledQBin, if_neg hj0, if_neg hj, if_neg hbad,
    dif_pos a.property, regularValue]
  have hs : (∑ z ∈ L.T a.val.1 a.val.2,
      pi z * dphi z x (e.prop z x + t * dp z x) *
        (e.prop z x - (e.prop z x + t * dp z x))) =
      -t * ∑ z ∈ L.T a.val.1 a.val.2,
        pi z * dphi z x (e.prop z x + t * dp z x) * dp z x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    ring
  rw [hs]
  ring

universe u
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- No added regularity or simplex premises: the actual admissible direction
-- supplies them. Overlap gives the nonzero population pooling denominator.
-- @node: population_binary_pooled_policy_correction_orthogonality
/-- If [the policy transformations have the specified derivatives](hyp:hdphi),
[the derivatives are uniformly bounded and Lipschitz on the unit interval](hyp:hL),
[baseline and policy levels have the specified invariant ordering](hyp:hOrder),
[policy-pool probabilities satisfy overlap with bound cpi](hyp:hov), and [the binary
nuisance direction is admissible at the truth](hyp:hd), then [almost everywhere in
covariates the pooled policy plus its policy correction, averaged over true instrument
probabilities and true treatment means, has derivative zero along that direction](goal). -/
lemma population_binary_pooled_policy_correction_orthogonality
    (phi dphi : Z → X → ℝ → ℝ) (hdphi : PolicyDifferentiable phi dphi)
    (hL : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : PolicyOverlap M L cpi)
    (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del))
    (a : RegularIndex L) :
    ∀ᵐ x ∂xLaw M, HasDerivAt (fun t : ℝ =>
      pooledQBin phi L (eta0Bin M L + t • del) a.val.1 a.val.2 x +
        ∑ z, instProb M z x * RqBin dphi L (eta0Bin M L + t • del)
          a.val.1 a.val.2 (x, z, M.prop z x, 0)) 0 0 := by
  have hs := bin_admissible_share_direction M L (eta0Bin M L) del hd a
  have hp := bin_admissible_propensity_path M L (eta0Bin M L) del hd
  filter_upwards [hs, hp] with x hx hp
  have htau : 0 < (levelSetProb M L).2 a.val.1 a.val.2 x :=
    hov.1.trans_le (hov.2 x a.val.1 a.val.2 a.property.1 a.property.2.1 a.property.2.2
      (ordered_policy_level_nonempty M _ L hOrder a.val.1 a.val.2
        a.property.1 a.property.2.1 a.property.2.2))
  have hshare : ∀ z ∈ L.T a.val.1 a.val.2,
      (eta0Bin M L).share a z x = instProb M z x / (eta0Bin M L).tauLev a x := by
    intro z hz
    simp only [eta0Bin, levelShares, if_pos hz]
  have hq : ∀ z ∈ L.T a.val.1 a.val.2,
      phi z x ((eta0Bin M L).prop z x) = L.qLev a.val.1 a.val.2 x := by
    intro z hz
    exact (hOrder.2.2.2.2.2.2.1 x a.val.1 a.val.2 z
      a.property.1 a.property.2.1 a.property.2.2).mp hz
  have h := pooledQBin_policy_correction_joint_orthogonality phi dphi hdphi hL L
    (eta0Bin M L) del.prop del.share del.tauLev a x (fun z => instProb M z x)
    (L.qLev a.val.1 a.val.2 x) htau.ne' hshare
    (fun z _ => M.rangeProp z x) (fun z _ => hp z) hq hx
  have hj0 : a.val.2 ≠ 0 := by have := a.property; omega
  have hj : ¬L.l a.val.1 < a.val.2 := by have := a.property; omega
  have hbad : ¬(a.val.2 = 0 ∨ L.l a.val.1 < a.val.2) := by tauto
  convert h using 1
  funext t
  simp only [pooledQBin, RqBin, if_neg hj0, if_neg hj, if_neg hbad,
    dif_pos a.property, regularValue]
  rfl

end Papers.TbsPrteOptimalTransport
