module
public import Papers.TbsPrteOptimalTransport.Helpers.Orthogonality
/-! Simultaneous share and propensity directions in pooled policy levels. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Filter Set
open scoped Classical
open scoped Topology

-- The paper assumes one-sided derivatives at propensity endpoints. An
-- admissible two-sided nuisance path stays in the interval, so the within
-- derivative composes to an ordinary derivative of that path.
-- @node: policy_admissible_affine_derivative
/-- If [a policy transformation has derivative dphi within the unit interval at p](hyp:hphi)
and [the affine propensity path stays in that interval near zero](hyp:hpath), then
[the transformed path has derivative dphi times the propensity direction at zero](goal). -/
lemma policy_admissible_affine_derivative (phi : ℝ → ℝ) (p dp dphi : ℝ)
    (hphi : HasDerivWithinAt phi dphi (Icc 0 1) p)
    (hpath : ∀ᶠ t : ℝ in 𝓝 0, p + t * dp ∈ Icc 0 1) :
    HasDerivAt (fun t : ℝ => phi (p + t * dp)) (dphi * dp) 0 := by
  have hp := ((hasDerivAt_id (0 : ℝ)).mul_const dp).const_add p
  simpa [Function.comp_def] using
    hphi.comp_hasDerivAt_of_eq 0 hp hpath (by simp)

-- @node: pooled_policy_affine_derivative
/-- If [each transformed propensity path has derivative equal to its policy derivative
times its propensity direction](hyp:hphi), then [the derivative of the pooled policy
along simultaneous affine share and propensity changes is the sum of the share-direction
times policy-value terms and the baseline-share times policy-derivative times
propensity-direction terms](goal). -/
lemma pooled_policy_affine_derivative {ι : Type*} (s : Finset ι)
    (a da p dp : ι → ℝ) (phi dphi : ι → ℝ → ℝ)
    (hphi : ∀ z ∈ s, HasDerivAt (fun t : ℝ => phi z (p z + t * dp z))
      (dphi z (p z) * dp z) 0) :
    HasDerivAt (fun t : ℝ =>
      ∑ z ∈ s, (a z + t * da z) * phi z (p z + t * dp z))
      (∑ z ∈ s, (da z * phi z (p z) + a z * dphi z (p z) * dp z)) 0 := by
  have hz : ∀ z ∈ s, HasDerivAt
      (fun t : ℝ => (a z + t * da z) * phi z (p z + t * dp z))
      (da z * phi z (p z) + a z * dphi z (p z) * dp z) 0 := by
    intro z hzs
    have ha := ((hasDerivAt_id (0 : ℝ)).mul_const (da z)).const_add (a z)
    have hq := hphi z hzs
    have hprod := @HasDerivAt.mul ℝ _ 0 ℝ
      (inferInstance : NormedField ℝ).toNormedDivisionRing.toNormedRing
      (NormedAlgebra.id ℝ) _ _ _ _ ha hq
    simpa [Function.comp_def, Pi.mul_def, mul_assoc] using hprod
  exact HasDerivAt.fun_sum hz

-- At the population law all policy values in the set agree. The simplex
-- tangent removes the share derivative even when propensities vary too.
-- @node: pooled_policy_simplex_derivative
/-- If [each transformed propensity path has the policy chain-rule derivative](hyp:hphi),
[share directions sum to zero in the pool](hyp:hshare), and [all baseline transformed
propensities equal the common level q](hyp:hcommon), then [the pooled policy derivative
is the sum of baseline shares times policy derivatives times propensity directions](goal). -/
lemma pooled_policy_simplex_derivative {ι : Type*} (s : Finset ι)
    (a da p dp : ι → ℝ) (phi dphi : ι → ℝ → ℝ) (q : ℝ)
    (hphi : ∀ z ∈ s, HasDerivAt (fun t : ℝ => phi z (p z + t * dp z))
      (dphi z (p z) * dp z) 0)
    (hshare : ∑ z ∈ s, da z = 0) (hcommon : ∀ z ∈ s, phi z (p z) = q) :
    HasDerivAt (fun t : ℝ =>
      ∑ z ∈ s, (a z + t * da z) * phi z (p z + t * dp z))
      (∑ z ∈ s, a z * dphi z (p z) * dp z) 0 := by
  have hzero : ∑ z ∈ s, da z * phi z (p z) = 0 := by
    calc
      _ = ∑ z ∈ s, da z * q := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [hcommon z hz]
      _ = (∑ z ∈ s, da z) * q := (Finset.sum_mul s da q).symm
      _ = 0 := by rw [hshare, zero_mul]
  simpa only [Finset.sum_add_distrib, hzero, zero_add] using
    pooled_policy_affine_derivative s a da p dp phi dphi hphi

-- @node: affine_propensity_path_from_two_bounds
/-- If [the radius r is positive](hyp:hr) and the affine propensity lies in the unit
interval [at r](hyp:hp) and [at minus r](hyp:hn), then [it stays in the unit interval
for all sufficiently small positive and negative path times](goal). -/
lemma affine_propensity_path_from_two_bounds (p dp r : ℝ) (hr : 0 < r)
    (hp : p + r * dp ∈ Icc 0 1) (hn : p + (-r) * dp ∈ Icc 0 1) :
    ∀ᶠ t : ℝ in 𝓝 0, p + t * dp ∈ Icc 0 1 := by
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, |t| < r :=
    continuousAt_id.abs.eventually_lt_const (by simpa using hr)
  filter_upwards [hnear] with t ht
  obtain ⟨htl, htu⟩ := abs_lt.mp ht
  rcases hp with ⟨hpl, hpu⟩
  rcases hn with ⟨hnl, hnu⟩
  by_cases hd : 0 ≤ dp
  · constructor <;> nlinarith [mul_nonneg (by linarith : 0 ≤ t + r) hd,
      mul_nonneg (by linarith : 0 ≤ r - t) hd]
  · have hd' : 0 ≤ -dp := by linarith
    constructor <;> nlinarith [mul_nonneg (by linarith : 0 ≤ t + r) hd',
      mul_nonneg (by linarith : 0 ≤ r - t) hd']

universe u v
variable {X Z : Type v} [Fintype Z] [DecidableEq Z]

-- @node: pooledQ_joint_direction_derivative
/-- Suppose [the policy transformations have the specified derivatives on the unit
interval](hyp:hphi), [share directions sum to zero in the selected regular pool](hyp:hshare),
[baseline transformed propensities equal that pool's policy level](hyp:hcommon), and
[each propensity path stays in the unit interval near zero](hyp:hpath). Then [the
continuous-outcome pooled policy derivative along the joint affine path equals the
sum of baseline shares times policy derivatives times propensity directions](goal). -/
lemma pooledQ_joint_direction_derivative (phi dphi : Z → X → ℝ → ℝ)
    (hphi : PolicyDifferentiable phi dphi) (L : LevelData Z X)
    (e del : NuisanceCont L) (a : RegularIndex L) (x : X)
    (hshare : ∑ z ∈ L.T a.val.1 a.val.2, del.share a z x = 0)
    (hcommon : ∀ z ∈ L.T a.val.1 a.val.2, phi z x (e.prop z x) = L.qLev a.val.1 a.val.2 x)
    (hpath : ∀ z ∈ L.T a.val.1 a.val.2,
      ∀ᶠ t : ℝ in 𝓝 0, e.prop z x + t * del.prop z x ∈ Icc 0 1) :
    HasDerivAt (fun t : ℝ => pooledQ phi L
      {e with prop := fun z x => e.prop z x + t * del.prop z x
              share := fun a z x => e.share a z x + t * del.share a z x}
      a.val.1 a.val.2 x)
      (∑ z ∈ L.T a.val.1 a.val.2, e.share a z x * dphi z x (e.prop z x) * del.prop z x) 0 := by
  have hj0 : a.val.2 ≠ 0 := by have := a.property.2.1; omega
  have hj : ¬ L.l a.val.1 < a.val.2 := not_lt.mpr a.property.2.2
  simp only [pooledQ, if_neg hj0, if_neg hj, shareValue, dif_pos a.property]
  apply pooled_policy_simplex_derivative (L.T a.val.1 a.val.2)
    (fun z => e.share a z x) (fun z => del.share a z x)
    (fun z => e.prop z x) (fun z => del.prop z x)
    (fun z => phi z x) (fun z => dphi z x) (L.qLev a.val.1 a.val.2 x)
    _ hshare hcommon
  intro z hz
  have hp : e.prop z x ∈ Icc 0 1 := by
    simpa using (hpath z hz).self_of_nhds
  exact policy_admissible_affine_derivative (phi z x) (e.prop z x) (del.prop z x)
    (dphi z x (e.prop z x)) (hphi z x (e.prop z x) hp) (hpath z hz)

-- @node: pooledQBin_joint_direction_derivative
/-- Suppose [the policy transformations have the specified derivatives on the unit
interval](hyp:hphi), [share directions sum to zero in the selected regular pool](hyp:hshare),
[baseline transformed propensities equal that pool's policy level](hyp:hcommon), and
[each propensity path stays in the unit interval near zero](hyp:hpath). Then [the
binary-outcome pooled policy derivative along the joint affine path equals the sum
of baseline shares times policy derivatives times propensity directions](goal). -/
lemma pooledQBin_joint_direction_derivative (phi dphi : Z → X → ℝ → ℝ)
    (hphi : PolicyDifferentiable phi dphi) (L : LevelData Z X)
    (e del : NuisanceBin L) (a : RegularIndex L) (x : X)
    (hshare : ∑ z ∈ L.T a.val.1 a.val.2, del.share a z x = 0)
    (hcommon : ∀ z ∈ L.T a.val.1 a.val.2, phi z x (e.prop z x) = L.qLev a.val.1 a.val.2 x)
    (hpath : ∀ z ∈ L.T a.val.1 a.val.2,
      ∀ᶠ t : ℝ in 𝓝 0, e.prop z x + t * del.prop z x ∈ Icc 0 1) :
    HasDerivAt (fun t : ℝ => pooledQBin phi L
      {e with prop := fun z x => e.prop z x + t * del.prop z x
              share := fun a z x => e.share a z x + t * del.share a z x}
      a.val.1 a.val.2 x)
      (∑ z ∈ L.T a.val.1 a.val.2, e.share a z x * dphi z x (e.prop z x) * del.prop z x) 0 := by
  have hj0 : a.val.2 ≠ 0 := by have := a.property.2.1; omega
  have hj : ¬ L.l a.val.1 < a.val.2 := not_lt.mpr a.property.2.2
  simp only [pooledQBin, if_neg hj0, if_neg hj, dif_pos a.property]
  apply pooled_policy_simplex_derivative (L.T a.val.1 a.val.2)
    (fun z => e.share a z x) (fun z => del.share a z x)
    (fun z => e.prop z x) (fun z => del.prop z x)
    (fun z => phi z x) (fun z => dphi z x) (L.qLev a.val.1 a.val.2 x)
    _ hshare hcommon
  intro z hz
  have hp : e.prop z x ∈ Icc 0 1 := by
    simpa using (hpath z hz).self_of_nhds
  exact policy_admissible_affine_derivative (phi z x) (e.prop z x) (del.prop z x)
    (dphi z x (e.prop z x)) (hphi z x (e.prop z x) hp) (hpath z hz)

variable {Ω : Type u} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)

-- Only two nuisance values are needed to obtain a common a.e. neighborhood
-- in x; no uncountable intersection of the pathwise a.e. conditions is taken.
-- @node: cont_admissible_propensity_path
/-- If [a continuous-outcome nuisance direction is admissible at the given nuisance
value](hyp:hd), then [for almost every covariate value, every instrument's affine
propensity path stays in the unit interval near zero](goal). -/
lemma cont_admissible_propensity_path (L : LevelData Z X) (e del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl e) (.inl del)) :
    ∀ᵐ x ∂xLaw M, ∀ z, ∀ᶠ t : ℝ in 𝓝 0,
      e.prop z x + t * del.prop z x ∈ Icc 0 1 := by
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  have hpos := (hpath (r / 2) (by rw [abs_of_pos (by positivity)]; linarith)).1
  have hneg := (hpath (-(r / 2)) (by rw [abs_neg, abs_of_pos (by positivity)]; linarith)).1
  filter_upwards [ae_all_iff.mpr hpos, ae_all_iff.mpr hneg] with x hp hn
  intro z
  apply affine_propensity_path_from_two_bounds (e.prop z x) (del.prop z x) (r / 2)
    (by positivity)
  · exact hp z
  · exact hn z

-- @node: bin_admissible_propensity_path
/-- If [a binary-outcome nuisance direction is admissible at the given nuisance
value](hyp:hd), then [for almost every covariate value, every instrument's affine
propensity path stays in the unit interval near zero](goal). -/
lemma bin_admissible_propensity_path (L : LevelData Z X) (e del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr e) (.inr del)) :
    ∀ᵐ x ∂xLaw M, ∀ z, ∀ᶠ t : ℝ in 𝓝 0,
      e.prop z x + t * del.prop z x ∈ Icc 0 1 := by
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  have hpos := (hpath (r / 2) (by rw [abs_of_pos (by positivity)]; linarith)).1
  have hneg := (hpath (-(r / 2)) (by rw [abs_neg, abs_of_pos (by positivity)]; linarith)).1
  filter_upwards [ae_all_iff.mpr hpos, ae_all_iff.mpr hneg] with x hp hn
  intro z
  apply affine_propensity_path_from_two_bounds (e.prop z x) (del.prop z x) (r / 2)
    (by positivity)
  · exact hp z
  · exact hn z

-- @node: continuous_true_pooled_policy_derivative
/-- If [the policy transformations have the specified derivatives](hyp:hphi),
[baseline and policy propensity levels obey the given invariant ordering](hyp:hOrder),
and [the continuous-outcome nuisance direction is admissible at the truth](hyp:hd),
then [almost everywhere in covariates, the regular pooled policy derivative at the
truth is the sum of true shares times policy derivatives at true propensities times
propensity directions](goal). -/
lemma continuous_true_pooled_policy_derivative (phi dphi : Z → X → ℝ → ℝ)
    (hphi : PolicyDifferentiable phi dphi) (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (a : RegularIndex L) :
    ∀ᵐ x ∂xLaw M, HasDerivAt
      (fun t : ℝ => pooledQ phi L (trueNuisance M L + t • del) a.val.1 a.val.2 x)
      (∑ z ∈ L.T a.val.1 a.val.2,
        (trueNuisance M L).share a z x * dphi z x (M.prop z x) * del.prop z x) 0 := by
  have hs := cont_admissible_share_direction M L (trueNuisance M L) del hd a
  have hp := cont_admissible_propensity_path M L (trueNuisance M L) del hd
  rcases hOrder with ⟨_, _, _, _, _, _, hT, _⟩
  filter_upwards [hs, hp] with x hx hp
  have hc : ∀ z ∈ L.T a.val.1 a.val.2,
      phi z x ((trueNuisance M L).prop z x) = L.qLev a.val.1 a.val.2 x := by
    intro z hz
    exact (hT x a.val.1 a.val.2 z a.property.1 a.property.2.1 a.property.2.2).mp hz
  have hder := pooledQ_joint_direction_derivative phi dphi hphi L
    (trueNuisance M L) del a x hx hc (fun z _ => hp z)
  have hj0 : a.val.2 ≠ 0 := by have := a.property.2.1; omega
  have hj : ¬ L.l a.val.1 < a.val.2 := not_lt.mpr a.property.2.2
  convert hder using 1
  · funext t
    simp only [pooledQ, if_neg hj0, if_neg hj, shareValue, dif_pos a.property]
    rfl
  · rfl

-- @node: binary_true_pooled_policy_derivative
/-- If [the policy transformations have the specified derivatives](hyp:hphi),
[baseline and policy propensity levels obey the given invariant ordering](hyp:hOrder),
and [the binary-outcome nuisance direction is admissible at the truth](hyp:hd), then
[almost everywhere in covariates, the regular pooled policy derivative at the truth
is the sum of true shares times policy derivatives at true propensities times
propensity directions](goal). -/
lemma binary_true_pooled_policy_derivative (phi dphi : Z → X → ℝ → ℝ)
    (hphi : PolicyDifferentiable phi dphi) (L : LevelData Z X)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del))
    (a : RegularIndex L) :
    ∀ᵐ x ∂xLaw M, HasDerivAt
      (fun t : ℝ => pooledQBin phi L (eta0Bin M L + t • del) a.val.1 a.val.2 x)
      (∑ z ∈ L.T a.val.1 a.val.2,
        (eta0Bin M L).share a z x * dphi z x (M.prop z x) * del.prop z x) 0 := by
  have hs := bin_admissible_share_direction M L (eta0Bin M L) del hd a
  have hp := bin_admissible_propensity_path M L (eta0Bin M L) del hd
  rcases hOrder with ⟨_, _, _, _, _, _, hT, _⟩
  filter_upwards [hs, hp] with x hx hp
  have hc : ∀ z ∈ L.T a.val.1 a.val.2,
      phi z x ((eta0Bin M L).prop z x) = L.qLev a.val.1 a.val.2 x := by
    intro z hz
    exact (hT x a.val.1 a.val.2 z a.property.1 a.property.2.1 a.property.2.2).mp hz
  have hder := pooledQBin_joint_direction_derivative phi dphi hphi L
    (eta0Bin M L) del a x hx hc (fun z _ => hp z)
  have hj0 : a.val.2 ≠ 0 := by have := a.property.2.1; omega
  have hj : ¬ L.l a.val.1 < a.val.2 := not_lt.mpr a.property.2.2
  convert hder using 1
  · funext t
    simp only [pooledQBin, if_neg hj0, if_neg hj, dif_pos a.property]
    rfl
  · rfl

end Papers.TbsPrteOptimalTransport
