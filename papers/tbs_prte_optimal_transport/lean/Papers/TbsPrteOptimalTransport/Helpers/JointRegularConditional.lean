module
public import Papers.TbsPrteOptimalTransport.Helpers.JointFullRegressionWeights
public import Papers.TbsPrteOptimalTransport.Helpers.PooledPolicyOrthogonality
/-! Finite conditional means for simultaneous binary regular-interval nuisance paths.
The outcome and treatment moments are kept separate, since the score uses both. -/
public section
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

namespace Papers.TbsPrteOptimalTransport
open Filter
open Set
open scoped Classical Topology
universe v
variable {X Z : Type v}
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]

-- @node: binary_RP_finite_conditional_mean_with_treatment
/-- If [the instrument masses in a baseline level sum to its reference assignment
probability](hyp:hmass) and [their outcome-times-treatment moment equals that
probability times the reference treated-outcome mean](hyp:hmoment), then [the
mass-weighted outcome residual equals the reference assignment probability times
the reference-minus-fitted treated-outcome mean, divided by the fitted assignment
probability](goal). -/
lemma binary_RP_finite_conditional_mean_with_treatment (L : LevelData Z X)
    (e e0 : NuisanceBin L) (i : ℕ) (x : X) (mass w y : Z → ℝ)
    (hmass : ∑ z ∈ L.S i, mass z = positiveValue e0.piLev i x)
    (hmoment : ∑ z ∈ L.S i, mass z * (y z * w z) =
      positiveValue e0.piLev i x * positiveValue e0.P1 i x) :
    (∑ z, mass z * RP L e i (x, z, w z, y z)) =
      positiveValue e0.piLev i x *
        (positiveValue e0.P1 i x - positiveValue e.P1 i x) /
          positiveValue e.piLev i x := by
  have heq : ∀ z, RP L e i (x, z, w z, y z) =
      RP L e i (x, z, 1, y z * w z) := by
    intro z
    simp only [RP, mul_one]
  simp_rw [heq]
  exact binary_RP_finite_conditional_mean L e e0 i x mass
    (fun z => y z * w z) hmass hmoment

-- @node: binary_Rp_finite_conditional_mean
/-- If [the instrument masses in a baseline level sum to its reference assignment
probability](hyp:hmass) and [their treatment moment equals that probability times
the reference treatment propensity](hyp:hmoment), then [the mass-weighted
treatment residual equals the reference assignment probability times the
reference-minus-fitted level propensity, divided by the fitted assignment
probability](goal). -/
lemma binary_Rp_finite_conditional_mean (L : LevelData Z X)
    (e e0 : NuisanceBin L) (i : ℕ) (x : X) (mass w y : Z → ℝ)
    (hmass : ∑ z ∈ L.S i, mass z = positiveValue e0.piLev i x)
    (hmoment : ∑ z ∈ L.S i, mass z * w z =
      positiveValue e0.piLev i x * positiveValue e0.pLev i x) :
    (∑ z, mass z * Rp L e i (x, z, w z, y z)) =
      positiveValue e0.piLev i x *
        (positiveValue e0.pLev i x - positiveValue e.pLev i x) /
          positiveValue e.piLev i x := by
  have heq : ∀ z, Rp L e i (x, z, w z, y z) =
      RP L {e with P1 := e.pLev} i (x, z, 1, w z) := by
    intro z
    simp only [Rp, RP, mul_one]
  simp_rw [heq]
  exact binary_RP_finite_conditional_mean L {e with P1 := e.pLev}
    {e0 with P1 := e0.pLev} i x mass w hmass hmoment

-- Every fitted coefficient factors out of the finite conditional sum. This
-- identity holds away from the truth as well as at fitted branch ties.
-- @node: binary_regular_component_finite_conditional_mean
/-- If [instrument masses sum to one](hyp:hmass), then [the mass-weighted regular
component score equals its fitted hinge plus the fitted boundary derivative
times the difference of adjacent outcome-residual means, minus that derivative
times the upper treatment-residual mean, minus the lower treatment-residual mean
weighted by dominance and activity when the interval is first, plus the active
upper policy-residual mean, minus the lower policy-residual mean weighted by
dominance and activity](goal). -/
lemma binary_regular_component_finite_conditional_mean
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e : NuisanceBin L)
    (k j : ℕ) (x : X) (mass w y : Z → ℝ) (hmass : ∑ z, mass z = 1) :
    (∑ z, mass z * binScoreComponents phi dphi L e k j (x, z, w z, y z)) =
      hMinus phi L e k j x +
      Dbd phi L e k j x * ((∑ z, mass z * RP L e (k+1) (x, z, w z, y z)) -
        ∑ z, mass z * RP L e k (x, z, w z, y z)) -
      Dbd phi L e k j x * (∑ z, mass z * Rp L e (k+1) (x, z, w z, y z)) -
      (if j = 1 then Edom phi L e k j x * Iact phi L e k j x *
        (∑ z, mass z * Rp L e k (x, z, w z, y z)) else 0) +
      Iact phi L e k j x * (∑ z, mass z * RqBin dphi L e k j (x, z, w z, y z)) -
      Edom phi L e k j x * Iact phi L e k j x *
        (∑ z, mass z * RqBin dphi L e k (j-1) (x, z, w z, y z)) := by
  simp only [binScoreComponents, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  by_cases hj : j = 1
  all_goals simp only [hj, if_true, if_false, mul_zero, Finset.sum_const_zero,
    sub_zero, mul_left_comm (mass _), ← Finset.mul_sum, ← Finset.sum_mul, hmass,
    one_mul]

-- The explicit product prefactor and assignment residual combine exactly.
-- Consequently its moving weight multiplies only the component correction.
-- @node: binary_regular_product_finite_conditional_mean
/-- If [instrument masses sum to one](hyp:hmass) and [the mass of the policy
union equals g](hyp:hgamma), then [the mass-weighted product score equals g times
the fitted hinge plus the fitted product weight times the difference between
the mass-weighted component score and the fitted hinge](goal). -/
lemma binary_regular_product_finite_conditional_mean
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e : NuisanceBin L)
    (k j : ℕ) (x : X) (mass w y : Z → ℝ) (g : ℝ)
    (hmass : ∑ z, mass z = 1)
    (hgamma : ∑ z, mass z * indicator (z ∈ policyUnion L k j) = g) :
    (∑ z, mass z * psiProdBin phi dphi L e k j (x, z, w z, y z)) =
      g * hMinus phi L e k j x + regularValue e.gamma k j x *
        ((∑ z, mass z * binScoreComponents phi dphi L e k j (x, z, w z, y z)) -
          hMinus phi L e k j x) := by
  have hid : ∀ z, mass z * psiProdBin phi dphi L e k j (x, z, w z, y z) =
      regularValue e.gamma k j x *
        (mass z * binScoreComponents phi dphi L e k j (x, z, w z, y z)) +
      hMinus phi L e k j x * (mass z * indicator (z ∈ policyUnion L k j)) -
      mass z * (hMinus phi L e k j x * regularValue e.gamma k j x) := by
    intro z
    simp only [psiProdBin]
    ring
  simp_rw [hid]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.sum_mul, hmass, hgamma]
  ring

-- Propensity and denominator directions cancel jointly, including structural p0.
-- @node: binary_propensity_residual_joint_path_derivative
/-- If [the baseline assignment probability is nonzero whenever the level index
is valid](hyp:hpi), then [the baseline assignment probability times the
baseline-minus-perturbed level propensity, divided by the perturbed assignment
probability, has derivative equal to the negative level-propensity direction at
zero](goal). -/
lemma binary_propensity_residual_joint_path_derivative (L : LevelData Z X)
    (e del : NuisanceBin L) (i : ℕ) (x : X)
    (hpi : 1 ≤ i ∧ i ≤ L.K → positiveValue e.piLev i x ≠ 0) :
    HasDerivAt (fun t : ℝ => positiveValue e.piLev i x *
      (positiveValue e.pLev i x - positiveValue (e + t • del).pLev i x) /
        positiveValue (e + t • del).piLev i x)
      (-positiveValue del.pLev i x) 0 := by
  exact binary_full_residual_joint_path_derivative L {e with P1 := e.pLev}
    {del with P1 := del.pLev} i x hpi

-- The pooled-level derivative and its actual finite policy residual cancel
-- along the full affine vector, without differentiating the policy derivative.
-- @node: binary_pooled_policy_joint_path_derivatives
/-- Suppose [the policy has the specified derivative](hyp:hd), [that derivative
is uniformly bounded and Lipschitz](hyp:hL), [the baseline pooled denominator is
nonzero](hyp:htau), [shares equal instrument masses divided by that denominator](hyp:hshare),
[baseline policy values equal the common level](hyp:hcommon), [share directions
sum to zero](hyp:hsimplex), and [every propensity in the pool remains in the unit
interval near zero](hyp:hpath). Then [the pooled level has derivative equal to
the sum of baseline shares times policy derivatives times propensity directions,
while its mass-weighted policy residual evaluated at baseline propensities has
the opposite derivative, both at zero](goal). -/
lemma binary_pooled_policy_joint_path_derivatives
    (phi dphi : Z → X → ℝ → ℝ) (hd : PolicyDifferentiable phi dphi)
    (hL : PolicyDerivativeBoundedLipschitz dphi) (L : LevelData Z X)
    (e del : NuisanceBin L) (a : RegularIndex L) (x : X) (mass y : Z → ℝ)
    (htau : e.tauLev a x ≠ 0)
    (hshare : ∀ z ∈ L.T a.val.1 a.val.2, e.share a z x = mass z / e.tauLev a x)
    (hcommon : ∀ z ∈ L.T a.val.1 a.val.2,
      phi z x (e.prop z x) = L.qLev a.val.1 a.val.2 x)
    (hsimplex : ∑ z ∈ L.T a.val.1 a.val.2, del.share a z x = 0)
    (hpath : ∀ z ∈ L.T a.val.1 a.val.2,
      ∀ᶠ t : ℝ in 𝓝 0, e.prop z x + t * del.prop z x ∈ Icc 0 1) :
    let dq := ∑ z ∈ L.T a.val.1 a.val.2,
      e.share a z x * dphi z x (e.prop z x) * del.prop z x
    HasDerivAt (fun t : ℝ => pooledQBin phi L (e + t • del) a.val.1 a.val.2 x) dq 0 ∧
    HasDerivAt (fun t : ℝ => ∑ z, mass z * RqBin dphi L (e + t • del)
      a.val.1 a.val.2 (x, z, e.prop z x, y z)) (-dq) 0 := by
  dsimp only
  have hq : HasDerivAt (fun t : ℝ => pooledQBin phi L (e + t • del) a.val.1 a.val.2 x)
      (∑ z ∈ L.T a.val.1 a.val.2, e.share a z x * dphi z x (e.prop z x) * del.prop z x) 0 := by
    convert pooledQBin_joint_direction_derivative phi dphi hd L e del a x
      hsimplex hcommon hpath using 1
    funext t
    have hj0 : a.val.2 ≠ 0 := by have := a.property; omega
    have hj : ¬ L.l a.val.1 < a.val.2 := not_lt.mpr a.property.2.2
    simp only [pooledQBin, if_neg hj0, if_neg hj, dif_pos a.property]
    rfl
  have hc : HasDerivAt (fun t : ℝ =>
      pooledQBin phi L (e + t • del) a.val.1 a.val.2 x +
        ∑ z, mass z * RqBin dphi L (e + t • del)
          a.val.1 a.val.2 (x, z, e.prop z x, y z)) 0 0 := by
    convert pooledQBin_policy_correction_joint_orthogonality phi dphi hd hL L e
      del.prop del.share del.tauLev a x mass (L.qLev a.val.1 a.val.2 x)
      htau hshare (fun z hz => by simpa using (hpath z hz).self_of_nhds) hpath hcommon hsimplex using 1
    funext t
    have hj0 : a.val.2 ≠ 0 := by have := a.property; omega
    have hj : ¬ L.l a.val.1 < a.val.2 := not_lt.mpr a.property.2.2
    have hbad : ¬(a.val.2 = 0 ∨ L.l a.val.1 < a.val.2) := by omega
    simp only [pooledQBin, RqBin, if_neg hj0, if_neg hj, if_neg hbad,
      regularValue, dif_pos a.property]
    rfl
  refine ⟨hq, ?_⟩
  convert! hc.sub hq using 1
  · funext t
    dsimp only [Pi.sub_apply]
    ring
  · ring

-- @node: positiveValue_affine_path_hasDerivAt
/-- [A level value extended by zero outside the positive level indices, and
perturbed affinely on those indices, has derivative at zero equal to the
correspondingly extended direction value](goal). -/
lemma positiveValue_affine_path_hasDerivAt (K : ℕ)
    (p dp : PositiveIndex K → X → ℝ) (i : ℕ) (x : X) :
    HasDerivAt (fun t : ℝ => positiveValue (fun a x => p a x + t * dp a x) i x)
      (positiveValue dp i x) 0 := by
  unfold positiveValue
  split_ifs
  · convert! ((hasDerivAt_id (0 : ℝ)).mul_const (dp _ x)).const_add (p _ x)
      using 1 <;> first | rfl | ring
  · exact hasDerivAt_const 0 0

-- @node: binary_nuisance_affine_zero
/-- [Perturbing a binary nuisance vector by zero times any direction returns the
original nuisance vector](goal). -/
lemma binary_nuisance_affine_zero (L : LevelData Z X) (e del : NuisanceBin L) :
    e + (0 : ℝ) • del = e := by
  change (⟨e.prop + 0 • del.prop, e.pLev + 0 • del.pLev,
    e.P1 + 0 • del.P1, e.piLev + 0 • del.piLev, e.tauLev + 0 • del.tauLev,
    e.share + 0 • del.share, e.gammaFull + 0 • del.gammaFull,
    e.gamma + 0 • del.gamma, e.gammaTail + 0 • del.gammaTail⟩ : NuisanceBin L) = e
  simp only [zero_smul, add_zero]
  cases e
  rfl

-- This uses the actual finite conditional score, with its outcome and treatment
-- moments, and permits all nuisance fields to move simultaneously.
-- @node: binary_regular_component_joint_finite_conditional_orthogonality
/-- Suppose [the policy has the specified derivative](hyp:hd) with [a uniformly
bounded Lipschitz derivative](hyp:hL), [the baseline level index is at most the
number of levels](hyp:hk), and [the interval index is regular](hyp:hj). Assume
[instrument masses sum to one](hyp:hmass), [masses in each adjacent baseline
level match its assignment probability](hyp:hlevelmass), [outcome-times-propensity
moments match the corresponding treated-outcome means](hyp:hPmoment), and
[propensity moments match the level treatment means](hyp:hpmoment). If [valid
adjacent assignment probabilities are nonzero](hyp:hpi), [all regular pooled
denominators are nonzero](hyp:htau), [shares are normalized instrument masses](hyp:hshare),
[policy values agree within every regular pool](hyp:hcommon), [each pool's share
directions sum to zero](hyp:hsimplex), [propensity paths stay in the unit interval
near zero](hyp:hpath), [the upper pooled boundary strictly exceeds the lower](hyp:horder),
and [the upper level propensity minus the adjacent treated-outcome contrast
differs from the lower boundary](hyp:hbl) and [from the upper boundary](hyp:hbq),
then [the mass-weighted component score evaluated at baseline propensities has
derivative zero at zero along the joint nuisance path](goal). -/
lemma binary_regular_component_joint_finite_conditional_orthogonality
    (phi dphi : Z → X → ℝ → ℝ) (hd : PolicyDifferentiable phi dphi)
    (hL : PolicyDerivativeBoundedLipschitz dphi) (L : LevelData Z X)
    (e del : NuisanceBin L) (k j : ℕ) (hk : k ≤ L.K)
    (hj : 1 ≤ j ∧ j ≤ L.l k) (x : X) (mass y : Z → ℝ)
    (hmass : ∑ z, mass z = 1)
    (hlevelmass : ∀ i ∈ ({k, k+1} : Finset ℕ),
      ∑ z ∈ L.S i, mass z = positiveValue e.piLev i x)
    (hPmoment : ∀ i ∈ ({k, k+1} : Finset ℕ),
      ∑ z ∈ L.S i, mass z * (y z * e.prop z x) =
        positiveValue e.piLev i x * positiveValue e.P1 i x)
    (hpmoment : ∀ i ∈ ({k, k+1} : Finset ℕ),
      ∑ z ∈ L.S i, mass z * e.prop z x =
        positiveValue e.piLev i x * positiveValue e.pLev i x)
    (hpi : ∀ i ∈ ({k, k+1} : Finset ℕ),
      1 ≤ i ∧ i ≤ L.K → positiveValue e.piLev i x ≠ 0)
    (htau : ∀ a : RegularIndex L, e.tauLev a x ≠ 0)
    (hshare : ∀ (a : RegularIndex L) z, z ∈ L.T a.val.1 a.val.2 →
      e.share a z x = mass z / e.tauLev a x)
    (hcommon : ∀ (a : RegularIndex L) z, z ∈ L.T a.val.1 a.val.2 →
      phi z x (e.prop z x) = L.qLev a.val.1 a.val.2 x)
    (hsimplex : ∀ a : RegularIndex L, ∑ z ∈ L.T a.val.1 a.val.2, del.share a z x = 0)
    (hpath : ∀ z, ∀ᶠ t : ℝ in 𝓝 0, e.prop z x + t * del.prop z x ∈ Icc 0 1)
    (horder : pooledQBin phi L e k (j-1) x < pooledQBin phi L e k j x)
    (hbl : positiveValue e.pLev (k+1) x - binFullJ L e k x ≠
      pooledQBin phi L e k (j-1) x)
    (hbq : positiveValue e.pLev (k+1) x - binFullJ L e k x ≠
      pooledQBin phi L e k j x) :
    HasDerivAt (fun t : ℝ => ∑ z, mass z * binScoreComponents phi dphi L
      (e + t • del) k j (x, z, e.prop z x, y z)) 0 0 := by
  let dq := fun a : RegularIndex L => ∑ z ∈ L.T a.val.1 a.val.2,
    e.share a z x * dphi z x (e.prop z x) * del.prop z x
  have hpol (a : RegularIndex L) := binary_pooled_policy_joint_path_derivatives
    phi dphi hd hL L e del a x mass y (htau a) (hshare a) (hcommon a)
      (hsimplex a) (fun z _ => hpath z)
  let ap : RegularIndex L := ⟨(k,j), hk, hj⟩
  have hq := (hpol ap).1
  have hrq := (hpol ap).2
  have hp (i : ℕ) : HasDerivAt (fun t : ℝ => positiveValue (e + t • del).pLev i x)
      (positiveValue del.pLev i x) 0 :=
    positiveValue_affine_path_hasDerivAt L.K e.pLev del.pLev i x
  have hP (i : ℕ) : HasDerivAt (fun t : ℝ => positiveValue (e + t • del).P1 i x)
      (positiveValue del.P1 i x) 0 :=
    positiveValue_affine_path_hasDerivAt L.K e.P1 del.P1 i x
  have hrP (i : ℕ) (hi : i ∈ ({k,k+1} : Finset ℕ)) :
      HasDerivAt (fun t : ℝ => ∑ z, mass z * RP L (e + t • del) i
        (x, z, e.prop z x, y z)) (-positiveValue del.P1 i x) 0 := by
    have heq (t : ℝ) := binary_RP_finite_conditional_mean_with_treatment L (e + t • del) e i
      x mass (fun z => e.prop z x) y (hlevelmass i hi) (hPmoment i hi)
    simp_rw [heq]
    exact binary_full_residual_joint_path_derivative L e del i x (hpi i hi)
  have hrp (i : ℕ) (hi : i ∈ ({k,k+1} : Finset ℕ)) :
      HasDerivAt (fun t : ℝ => ∑ z, mass z * Rp L (e + t • del) i
        (x, z, e.prop z x, y z)) (-positiveValue del.pLev i x) 0 := by
    have heq (t : ℝ) := binary_Rp_finite_conditional_mean L (e + t • del) e i
      x mass (fun z => e.prop z x) y (hlevelmass i hi) (hpmoment i hi)
    simp_rw [heq]
    exact binary_propensity_residual_joint_path_derivative L e del i x (hpi i hi)
  have hlower : ∃ dl,
      HasDerivAt (fun t : ℝ => pooledQBin phi L (e + t • del) k (j-1) x) dl 0 ∧
      HasDerivAt (fun t : ℝ => if j = 1 then
        ∑ z, mass z * Rp L (e + t • del) k (x, z, e.prop z x, y z) else
        ∑ z, mass z * RqBin dphi L (e + t • del) k (j-1)
          (x, z, e.prop z x, y z)) (-dl) 0 := by
    by_cases hj1 : j = 1
    · refine ⟨positiveValue del.pLev k x, ?_, ?_⟩
      · simpa only [hj1, Nat.sub_self, pooledQBin, if_true] using hp k
      · simpa only [hj1, if_true] using hrp k (by simp)
    · have hm : 1 ≤ j-1 ∧ j-1 ≤ L.l k := by omega
      let am : RegularIndex L := ⟨(k,j-1), hk, hm⟩
      exact ⟨dq am, (hpol am).1, by simpa only [hj1, if_false] using (hpol am).2⟩
  obtain ⟨dl, hl, hrl⟩ := hlower
  have hzero : j = 1 → ∀ t : ℝ, (∑ z, mass z * RqBin dphi L (e + t • del)
      k (j-1) (x, z, e.prop z x, y z)) = 0 := by
    intro hj1 t
    simp only [hj1, Nat.sub_self, RqBin, true_or, if_true, mul_zero, Finset.sum_const_zero]
  have hc := binary_component_conditional_path_orthogonality phi L
    (fun t => e + t • del) k j x _ _ _ _ _ _ (dq ap) dl
    (positiveValue del.pLev (k+1) x) (positiveValue del.P1 (k+1) x)
    (positiveValue del.P1 k x) hq hl (hp (k+1)) (hP (k+1)) (hP k)
    (hrP (k+1) (by simp)) (hrP k (by simp)) (hrp (k+1) (by simp)) hrq hrl hzero
    (by simpa only [binary_nuisance_affine_zero] using horder)
    (by simpa only [binary_nuisance_affine_zero] using hbl)
    (by simpa only [binary_nuisance_affine_zero] using hbq)
  convert! hc using 1
  funext t
  exact binary_regular_component_finite_conditional_mean phi dphi L (e + t • del)
    k j x mass (fun z => e.prop z x) y hmass

-- Product inheritance needs only continuity of the plug-in: the moving weight
-- multiplies a component residual which is zero at the population origin.
-- @node: binary_regular_product_joint_finite_orthogonality_of_component
/-- For [a baseline level index at most the number of levels](hyp:hk) and [a
regular interval index](hyp:hj), assume [instrument masses sum to one](hyp:hmass),
[the policy-union mass equals the baseline product weight](hyp:hgamma), [the
baseline mass-weighted component score equals its hinge](hyp:hmean), [the
mass-weighted component score has derivative zero at zero along the joint
path](hyp:hcomp), and [the fitted hinge is continuous there](hyp:hcont). Then
[the mass-weighted product score also has derivative zero at zero along that
path](goal). -/
lemma binary_regular_product_joint_finite_orthogonality_of_component
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (e del : NuisanceBin L)
    (k j : ℕ) (hk : k ≤ L.K) (hj : 1 ≤ j ∧ j ≤ L.l k)
    (x : X) (mass w y : Z → ℝ) (hmass : ∑ z, mass z = 1)
    (hgamma : ∑ z, mass z * indicator (z ∈ policyUnion L k j) = regularValue e.gamma k j x)
    (hmean : (∑ z, mass z * binScoreComponents phi dphi L e k j (x, z, w z, y z)) =
      hMinus phi L e k j x)
    (hcomp : HasDerivAt (fun t : ℝ => ∑ z, mass z * binScoreComponents phi dphi L
      (e + t • del) k j (x, z, w z, y z)) 0 0)
    (hcont : ContinuousAt (fun t : ℝ => hMinus phi L (e + t • del) k j x) 0) :
    HasDerivAt (fun t : ℝ => ∑ z, mass z * psiProdBin phi dphi L
      (e + t • del) k j (x, z, w z, y z)) 0 0 := by
  let C := fun t : ℝ => ∑ z, mass z * binScoreComponents phi dphi L
    (e + t • del) k j (x, z, w z, y z)
  let H := fun t : ℝ => hMinus phi L (e + t • del) k j x
  have hz : C 0 - H 0 = 0 := by
    simp only [C, H, binary_nuisance_affine_zero, hmean, sub_self]
  have hc : ContinuousAt (fun t : ℝ => regularValue del.gamma k j x * (C t - H t)) 0 :=
    (hcomp.continuousAt.sub hcont).const_mul _
  have hd := continuous_coefficient_times_path_deriv _ hc
  have hd0 : HasDerivAt (fun t : ℝ => t *
      (regularValue del.gamma k j x * (C t - H t))) 0 0 := by
    simpa only [hz, mul_zero] using hd
  have hs := (hcomp.const_mul (regularValue e.gamma k j x)).add hd0
  convert! hs using 1
  · funext t
    rw [binary_regular_product_finite_conditional_mean phi dphi L (e + t • del)
      k j x mass w y (regularValue e.gamma k j x) hmass hgamma]
    dsimp only [C, H, Pi.add_apply]
    simp only [regularValue, dif_pos (show k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k from ⟨hk,hj⟩)]
    have hgt : (e + t • del).gamma ⟨(k,j),hk,hj⟩ x =
        e.gamma ⟨(k,j),hk,hj⟩ x + t * del.gamma ⟨(k,j),hk,hj⟩ x := rfl
    rw [hgt]
    ring
  · ring

-- The full vector, including its product weight, is now handled by the actual
-- regular-interval finite conditional calculation.
-- @node: binary_regular_product_joint_finite_conditional_orthogonality
/-- Suppose [the policy has the specified derivative](hyp:hd) with [a uniformly
bounded Lipschitz derivative](hyp:hL), [the baseline level index is at most the
number of levels](hyp:hk), and [the interval is regular](hyp:hj). Assume
[instrument masses sum to one](hyp:hmass), [policy-union mass equals the baseline
product weight](hyp:hgamma), [adjacent level masses match their assignment
probabilities](hyp:hlevelmass), [outcome-times-propensity moments match the
treated-outcome means](hyp:hPmoment), and [propensity moments match the level
treatment means](hyp:hpmoment). If [valid adjacent assignment probabilities are
nonzero](hyp:hpi), [regular pooled denominators are nonzero](hyp:htau), [shares
are normalized instrument masses](hyp:hshare), [policy values agree within each
regular pool](hyp:hcommon), [share directions sum to zero in every pool](hyp:hsimplex),
[propensity paths stay in the unit interval near zero](hyp:hpath), [the pooled
boundaries are strictly ordered](hyp:horder), and [the upper level propensity
minus the adjacent treated-outcome contrast differs from the lower boundary](hyp:hbl)
and [from the upper boundary](hyp:hbq), then [the mass-weighted product score
evaluated at baseline propensities has derivative zero at zero along the full
joint nuisance path](goal). -/
lemma binary_regular_product_joint_finite_conditional_orthogonality
    (phi dphi : Z → X → ℝ → ℝ) (hd : PolicyDifferentiable phi dphi)
    (hL : PolicyDerivativeBoundedLipschitz dphi) (L : LevelData Z X)
    (e del : NuisanceBin L) (k j : ℕ) (hk : k ≤ L.K)
    (hj : 1 ≤ j ∧ j ≤ L.l k) (x : X) (mass y : Z → ℝ)
    (hmass : ∑ z, mass z = 1)
    (hgamma : ∑ z, mass z * indicator (z ∈ policyUnion L k j) = regularValue e.gamma k j x)
    (hlevelmass : ∀ i ∈ ({k, k+1} : Finset ℕ),
      ∑ z ∈ L.S i, mass z = positiveValue e.piLev i x)
    (hPmoment : ∀ i ∈ ({k, k+1} : Finset ℕ),
      ∑ z ∈ L.S i, mass z * (y z * e.prop z x) =
        positiveValue e.piLev i x * positiveValue e.P1 i x)
    (hpmoment : ∀ i ∈ ({k, k+1} : Finset ℕ),
      ∑ z ∈ L.S i, mass z * e.prop z x =
        positiveValue e.piLev i x * positiveValue e.pLev i x)
    (hpi : ∀ i ∈ ({k, k+1} : Finset ℕ),
      1 ≤ i ∧ i ≤ L.K → positiveValue e.piLev i x ≠ 0)
    (htau : ∀ a : RegularIndex L, e.tauLev a x ≠ 0)
    (hshare : ∀ (a : RegularIndex L) z, z ∈ L.T a.val.1 a.val.2 →
      e.share a z x = mass z / e.tauLev a x)
    (hcommon : ∀ (a : RegularIndex L) z, z ∈ L.T a.val.1 a.val.2 →
      phi z x (e.prop z x) = L.qLev a.val.1 a.val.2 x)
    (hsimplex : ∀ a : RegularIndex L, ∑ z ∈ L.T a.val.1 a.val.2, del.share a z x = 0)
    (hpath : ∀ z, ∀ᶠ t : ℝ in 𝓝 0, e.prop z x + t * del.prop z x ∈ Icc 0 1)
    (horder : pooledQBin phi L e k (j-1) x < pooledQBin phi L e k j x)
    (hbl : positiveValue e.pLev (k+1) x - binFullJ L e k x ≠
      pooledQBin phi L e k (j-1) x)
    (hbq : positiveValue e.pLev (k+1) x - binFullJ L e k x ≠
      pooledQBin phi L e k j x) :
    HasDerivAt (fun t : ℝ => ∑ z, mass z * psiProdBin phi dphi L
      (e + t • del) k j (x, z, e.prop z x, y z)) 0 0 := by
  have hc := binary_regular_component_joint_finite_conditional_orthogonality
    phi dphi hd hL L e del k j hk hj x mass y hmass hlevelmass hPmoment hpmoment
    hpi htau hshare hcommon hsimplex hpath horder hbl hbq
  have hp (i : ℕ) : ContinuousAt (fun t : ℝ => positiveValue (e + t • del).pLev i x) 0 :=
    (positiveValue_affine_path_hasDerivAt L.K e.pLev del.pLev i x).continuousAt
  have hP (i : ℕ) : ContinuousAt (fun t : ℝ => positiveValue (e + t • del).P1 i x) 0 :=
    (positiveValue_affine_path_hasDerivAt L.K e.P1 del.P1 i x).continuousAt
  have hq (a : RegularIndex L) : ContinuousAt
      (fun t : ℝ => pooledQBin phi L (e + t • del) a.val.1 a.val.2 x) 0 :=
    (binary_pooled_policy_joint_path_derivatives phi dphi hd hL L e del a x mass y
      (htau a) (hshare a) (hcommon a) (hsimplex a) (fun z _ => hpath z)).1.continuousAt
  have hl : ContinuousAt (fun t : ℝ => pooledQBin phi L (e + t • del) k (j-1) x) 0 := by
    by_cases hj1 : j = 1
    · simpa only [hj1, Nat.sub_self, pooledQBin, if_true] using hp k
    · have hm : 1 ≤ j-1 ∧ j-1 ≤ L.l k := by omega
      exact hq ⟨(k,j-1), hk, hm⟩
  have hcont : ContinuousAt (fun t : ℝ => hMinus phi L (e + t • del) k j x) 0 :=
    continuousAt_const.max ((hq ⟨(k,j),hk,hj⟩).sub (hl.max ((hp (k+1)).sub
      ((hP (k+1)).sub (hP k)))))
  have hrP (i : ℕ) (hi : i ∈ ({k,k+1} : Finset ℕ)) :
      (∑ z, mass z * RP L e i (x, z, e.prop z x, y z)) = 0 := by
    rw [binary_RP_finite_conditional_mean_with_treatment L e e i x mass
      (fun z => e.prop z x) y (hlevelmass i hi) (hPmoment i hi)]
    simp only [sub_self, mul_zero, zero_div]
  have hrp (i : ℕ) (hi : i ∈ ({k,k+1} : Finset ℕ)) :
      (∑ z, mass z * Rp L e i (x, z, e.prop z x, y z)) = 0 := by
    rw [binary_Rp_finite_conditional_mean L e e i x mass
      (fun z => e.prop z x) y (hlevelmass i hi) (hpmoment i hi)]
    simp only [sub_self, mul_zero, zero_div]
  have hrq (a : ℕ) : (∑ z, mass z * RqBin dphi L e k a
      (x, z, e.prop z x, y z)) = 0 := by
    have heq : ∀ z, RqBin dphi L e k a (x, z, e.prop z x, y z) =
        RqBin dphi L e k a (x, z, e.prop z x, 0) := fun _ => rfl
    simp_rw [heq, RqBin_finite_conditional_mean]
    simp only [sub_self, mul_zero, Finset.sum_const_zero, ite_self]
  have hmean : (∑ z, mass z * binScoreComponents phi dphi L e k j
      (x, z, e.prop z x, y z)) = hMinus phi L e k j x := by
    rw [binary_regular_component_finite_conditional_mean phi dphi L e k j x mass
      (fun z => e.prop z x) y hmass, hrP (k+1) (by simp), hrP k (by simp),
      hrp (k+1) (by simp), hrp k (by simp), hrq j, hrq (j-1)]
    simp only [sub_self, mul_zero, sub_zero, add_zero, ite_self]
  exact binary_regular_product_joint_finite_orthogonality_of_component phi dphi L e del
    k j hk hj x mass (fun z => e.prop z x) y hmass hgamma hmean hc hcont

end Papers.TbsPrteOptimalTransport
