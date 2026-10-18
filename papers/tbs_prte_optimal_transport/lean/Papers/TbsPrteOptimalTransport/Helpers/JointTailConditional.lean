module
public import Papers.TbsPrteOptimalTransport.Helpers.PooledPolicyOrthogonality
public import Papers.TbsPrteOptimalTransport.Helpers.TailScoreOrthogonality
/-! Simultaneous conditional tail-score cancellations, without a second policy derivative. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Set Filter
open scoped Classical Topology
universe v

-- @node: policy_debiased_affine_orthogonality
/-- If [the policy has the specified propensity derivative](hyp:hd), [that derivative is
uniformly bounded and Lipschitz](hyp:hL), [the initial propensity is between zero and
one](hyp:hp), and [its affine perturbation stays between zero and one near zero](hyp:hpath),
then [the perturbed policy minus the path displacement times its derivative evaluated
at the perturbed propensity has derivative zero at zero](goal). -/
lemma policy_debiased_affine_orthogonality {X Z : Type v}
    (phi dphi : Z → X → ℝ → ℝ) (hd : PolicyDifferentiable phi dphi)
    (hL : PolicyDerivativeBoundedLipschitz dphi) (z : Z) (x : X) (p dp : ℝ)
    (hp : p ∈ Icc (0 : ℝ) 1)
    (hpath : ∀ᶠ t : ℝ in 𝓝 0, p + t * dp ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun t : ℝ => phi z x (p + t * dp) -
      t * (dphi z x (p + t * dp) * dp)) 0 0 := by
  have h := pooled_policy_debiased_joint_path_orthogonality phi dphi hd hL
    {z} x (fun _ => p) (fun _ => dp) (fun _ => 1) (fun _ => 0)
    (fun _ => 1) (phi z x p) 1 0 (by norm_num)
    (by simp) (by simpa using hp) (by simpa using hpath) (by simp) (by simp)
  simpa using h

-- The two baseline terms cancel even when the denominator and signed
-- coefficient move simultaneously. Their changes multiply a zero residual.
-- @node: tail_baseline_joint_scalar_orthogonality
/-- If [the initial assignment denominator is nonzero](hyp:hpi), then [the negative
perturbed baseline propensity times the initial tail weight, plus the path parameter
times the perturbed tail-weight-to-denominator ratio times the baseline propensity
direction and initial denominator, has derivative zero at zero](goal). -/
lemma tail_baseline_joint_scalar_orthogonality (p dp pi dpi g dg : ℝ)
    (hpi : pi ≠ 0) :
    HasDerivAt (fun t : ℝ => -(p + t * dp) * g +
      t * ((g + t * dg) / (pi + t * dpi) * (dp * pi))) 0 0 := by
  have hc : ContinuousAt (fun t : ℝ =>
      (g + t * dg) / (pi + t * dpi) * (dp * pi)) 0 := by
    apply ContinuousAt.mul
    · apply ContinuousAt.div
      · fun_prop
      · fun_prop
      · simpa using hpi
    · fun_prop
  have hb := (((hasDerivAt_id (0 : ℝ)).mul_const dp).const_add p).neg.mul_const g
  have h := hb.add (continuous_coefficient_times_path_deriv _ hc)
  convert! h using 1
  simp only [zero_mul, add_zero, one_mul]
  field_simp [hpi]
  <;> ring

-- @node: tail_joint_finite_mean_orthogonality
/-- If [the policy has the specified propensity derivative](hyp:hd), [its derivative is
uniformly bounded and Lipschitz](hyp:hL), [the initial denominator is nonzero](hyp:hpi),
[each propensity in the finite instrument set lies between zero and one](hyp:hp), and
[each affine propensity path stays in that interval near zero](hyp:hpath), then
[the outcome-floor-scaled finite weighted sum of debiased policies, together with the
jointly perturbed baseline correction, has derivative zero at zero](goal). -/
lemma tail_joint_finite_mean_orthogonality {X Z : Type v}
    (phi dphi : Z → X → ℝ → ℝ) (hd : PolicyDifferentiable phi dphi)
    (hL : PolicyDerivativeBoundedLipschitz dphi) (s : Finset Z) (x : X)
    (p dp mass : Z → ℝ) (pk dpk pi dpi g dg ymin : ℝ)
    (hpi : pi ≠ 0) (hp : ∀ z ∈ s, p z ∈ Icc (0 : ℝ) 1)
    (hpath : ∀ z ∈ s, ∀ᶠ t : ℝ in 𝓝 0, p z + t * dp z ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun t : ℝ => ymin *
      ((∑ z ∈ s, mass z * (phi z x (p z + t * dp z) -
          t * (dphi z x (p z + t * dp z) * dp z))) -
        (pk + t * dpk) * g +
        t * ((g + t * dg) / (pi + t * dpi) * (dpk * pi)))) 0 0 := by
  have hs := HasDerivAt.fun_sum (u := s) (fun z hz =>
    (policy_debiased_affine_orthogonality phi dphi hd hL z x (p z) (dp z)
      (hp z hz) (hpath z hz)).const_mul (mass z))
  simp only [mul_zero, Finset.sum_const_zero] at hs
  have hb := tail_baseline_joint_scalar_orthogonality pk dpk pi dpi g dg hpi
  have h := (hs.add hb).const_mul ymin
  convert! h using 1
  · funext t
    dsimp only [Pi.add_apply]
    ring
  · ring

universe u
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- This is the actual common tail score averaged under the fixed conditional
-- law. Only its first treatment moment is needed, since the score is affine in W.
-- @node: commonTailScore_joint_finite_conditional_mean
/-- If [there is at least one propensity level](hyp:hK), [propensities in the final
level equal its baseline propensity](hyp:hlevel), [the masses in that level sum to its
assignment denominator](hyp:hpi), and [the masses in the tail policy region sum to the
tail weight](hyp:hg), then [the finite weighted average of the common tail score along
the simultaneous affine nuisance path equals the outcome floor times the sum of
the weighted debiased policies, minus the perturbed final-level propensity times the
initial tail weight, plus the path parameter times the perturbed tail-weight-to-denominator
ratio times the final-level propensity direction and initial denominator](goal). -/
lemma commonTailScore_joint_finite_conditional_mean
    (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X) (hK : LevelCountPos L.K)
    (prop dp : Z → X → ℝ) (pk dpk pi dpi : PositiveIndex L.K → X → ℝ)
    (g dg : X → ℝ) (x : X) (mass : Z → ℝ) (t : ℝ)
    (hlevel : ∀ z ∈ L.S L.K, prop z x = positiveValue pk L.K x)
    (hpi : ∑ z ∈ L.S L.K, mass z = positiveValue pi L.K x)
    (hg : ∑ z ∈ policyUnion L L.K 1, mass z = g x) :
    (∑ z, mass z * commonTailScore M phi dphi L
      (fun z x => prop z x + t * dp z x)
      (fun k x => pk k x + t * dpk k x)
      (fun k x => pi k x + t * dpi k x)
      (fun x => g x + t * dg x) (x, z, prop z x, 0)) =
    M.yMin * ((∑ z ∈ policyUnion L L.K 1, mass z *
      (phi z x (prop z x + t * dp z x) - t * (dphi z x (prop z x + t * dp z x) * dp z x))) -
      (positiveValue pk L.K x + t * positiveValue dpk L.K x) * g x +
      t * ((g x + t * dg x) /
        (positiveValue pi L.K x + t * positiveValue dpi L.K x) *
          (positiveValue dpk L.K x * positiveValue pi L.K x))) := by
  have hk : L.K ≠ 0 := by unfold LevelCountPos at hK; omega
  have hi : 1 ≤ L.K ∧ L.K ≤ L.K := ⟨hK, le_rfl⟩
  have hid : ∀ z, mass z * commonTailScore M phi dphi L
      (fun z x => prop z x + t * dp z x)
      (fun k x => pk k x + t * dpk k x)
      (fun k x => pi k x + t * dpi k x)
      (fun x => g x + t * dg x) (x, z, prop z x, 0) =
      M.yMin * (if z ∈ policyUnion L L.K 1 then mass z *
        (phi z x (prop z x + t * dp z x) - t * (dphi z x (prop z x + t * dp z x) * dp z x) -
          (positiveValue pk L.K x + t * positiveValue dpk L.K x)) else 0) +
      M.yMin * (t * ((g x + t * dg x) /
        (positiveValue pi L.K x + t * positiveValue dpi L.K x) * positiveValue dpk L.K x)) *
          (if z ∈ L.S L.K then mass z else 0) := by
    intro z
    by_cases hs : z ∈ L.S L.K <;> by_cases ha : z ∈ policyUnion L L.K 1
    all_goals simp only [commonTailScore, if_neg hk, indicator, hs, ha, if_true, if_false,
      positiveValue, dif_pos hi]
    all_goals try rw [hlevel z hs]
    all_goals try simp only [positiveValue, dif_pos hi]
    all_goals ring
  simp_rw [hid]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [Finset.sum_ite_mem, Finset.univ_inter]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hpi, hg]
  ring

-- @node: commonTailScore_joint_finite_conditional_orthogonality
/-- Suppose [the policy has the specified propensity derivative](hyp:hd), [the derivative
is uniformly bounded and Lipschitz](hyp:hL), [there is at least one level](hyp:hK),
[final-level propensities equal the final baseline propensity](hyp:hlevel), [final-level
masses sum to the assignment denominator](hyp:hpi), and [tail-region masses sum to the
tail weight](hyp:hg). If [the final denominator is nonzero](hyp:hne), [tail-region
propensities lie between zero and one](hyp:hp), and [their affine paths stay in this
interval near zero](hyp:hpath), then [the finite weighted average of the common tail
score has derivative zero at zero under simultaneous affine perturbations of all
four nuisance components](goal). -/
lemma commonTailScore_joint_finite_conditional_orthogonality
    (phi dphi : Z → X → ℝ → ℝ) (hd : PolicyDifferentiable phi dphi)
    (hL : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (prop dp : Z → X → ℝ) (pk dpk pi dpi : PositiveIndex L.K → X → ℝ)
    (g dg : X → ℝ) (x : X) (mass : Z → ℝ)
    (hlevel : ∀ z ∈ L.S L.K, prop z x = positiveValue pk L.K x)
    (hpi : ∑ z ∈ L.S L.K, mass z = positiveValue pi L.K x)
    (hg : ∑ z ∈ policyUnion L L.K 1, mass z = g x)
    (hne : positiveValue pi L.K x ≠ 0)
    (hp : ∀ z ∈ policyUnion L L.K 1, prop z x ∈ Icc (0 : ℝ) 1)
    (hpath : ∀ z ∈ policyUnion L L.K 1,
      ∀ᶠ t : ℝ in 𝓝 0, prop z x + t * dp z x ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun t : ℝ => ∑ z, mass z * commonTailScore M phi dphi L
      (fun z x => prop z x + t * dp z x)
      (fun k x => pk k x + t * dpk k x)
      (fun k x => pi k x + t * dpi k x)
      (fun x => g x + t * dg x) (x, z, prop z x, 0)) 0 0 := by
  have heq := fun t => commonTailScore_joint_finite_conditional_mean M phi dphi L hK
    prop dp pk dpk pi dpi g dg x mass t hlevel hpi hg
  simp_rw [heq]
  exact tail_joint_finite_mean_orthogonality phi dphi hd hL (policyUnion L L.K 1)
    x (fun z => prop z x) (fun z => dp z x) mass
    (positiveValue pk L.K x) (positiveValue dpk L.K x)
    (positiveValue pi L.K x) (positiveValue dpi L.K x) (g x) (dg x) M.yMin hne hp hpath

-- @node: population_binary_tail_joint_conditional_orthogonality_of_admissible
/-- If [the policy has the specified propensity derivative](hyp:hdphi), [that derivative
is uniformly bounded and Lipschitz](hyp:hL), [there is at least one level](hyp:hK),
[the levels preserve the ordering of the true and policy propensities](hyp:hOrder),
[baseline assignment probabilities satisfy the specified positive overlap bound](hyp:hov),
and [the binary nuisance direction is admissible at the truth](hyp:hd), then
[for almost every covariate value, the true-instrument-probability-weighted common tail
score, with treatment fixed at its true conditional mean, has derivative zero at zero
along the simultaneous nuisance path](goal). -/
lemma population_binary_tail_joint_conditional_orthogonality_of_admissible
    (phi dphi : Z → X → ℝ → ℝ) (hdphi : PolicyDifferentiable phi dphi)
    (hL : PolicyDerivativeBoundedLipschitz dphi)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (cpi : ℝ) (hov : BaselineOverlapWitness M L cpi)
    (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del)) :
    ∀ᵐ x ∂xLaw M, HasDerivAt (fun t : ℝ => ∑ z, instProb M z x *
      commonTailScore M phi dphi L (eta0Bin M L + t • del).prop
        (eta0Bin M L + t • del).pLev (eta0Bin M L + t • del).piLev
        (eta0Bin M L + t • del).gammaTail (x, z, M.prop z x, 0)) 0 0 := by
  have hp := bin_admissible_propensity_path M L (eta0Bin M L) del hd
  filter_upwards [hp] with x hx
  have hi : 1 ≤ L.K ∧ L.K ≤ L.K := ⟨hK, le_rfl⟩
  have hlevel : ∀ z ∈ L.S L.K, M.prop z x = positiveValue (eta0Bin M L).pLev L.K x := by
    intro z hz
    simp only [positiveValue, dif_pos hi, eta0Bin]
    exact (hOrder.2.2.2.2.2.1 x L.K z le_rfl).mp hz
  have hpi : ∑ z ∈ L.S L.K, instProb M z x =
      positiveValue (eta0Bin M L).piLev L.K x := by
    simp only [positiveValue, dif_pos hi, eta0Bin, levelSetProb]
  have hg : ∑ z ∈ policyUnion L L.K 1, instProb M z x = (eta0Bin M L).gammaTail x := by
    rfl
  have hne : positiveValue (eta0Bin M L).piLev L.K x ≠ 0 := by
    have hb := hov.1.trans_le (hov.2 x L.K hK le_rfl)
    simpa only [positiveValue, dif_pos hi, eta0Bin] using hb.ne'
  exact commonTailScore_joint_finite_conditional_orthogonality M phi dphi hdphi hL L hK
    M.prop del.prop (eta0Bin M L).pLev del.pLev (eta0Bin M L).piLev del.piLev
    (eta0Bin M L).gammaTail del.gammaTail x (fun z => instProb M z x)
    hlevel hpi hg hne (fun z _ => M.rangeProp z x) (fun z _ => hx z)

end Papers.TbsPrteOptimalTransport
