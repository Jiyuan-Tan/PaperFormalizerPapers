module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLWeightedBaselineCancellation
/-! Finite assembly of fractional binary bias contributions. The fitted hinge
and product-weight errors are controlled by the original nuisance rates. -/
public section
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

-- @node: dml_finite_integral_root_n_negligible
/-- If [each member of a finite family is integrable for every sample size and
sample realization](hyp:hi) and [each integral multiplied by the square root of
one more than the sample index converges in probability to zero](hyp:hr), then
[the integral of their finite sum, with the same scaling, also converges in
probability to zero](goal). -/
lemma dml_finite_integral_root_n_negligible {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B] (μ : Measure A) (ν : Measure B)
    (s : Finset ι) (f : ι → ℕ → A → B → ℝ)
    (hi : ∀ i ∈ s, ∀ n a, Integrable (f i n a) ν)
    (hr : ∀ i ∈ s, Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) * ∫ x, f i n a x ∂ν)
      atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) * ∫ x, ∑ i ∈ s, f i n a x ∂ν)
      atTop (fun _ _ => 0) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, integral_zero, mul_zero]
    rw [Causalean.Stat.Modes.tendstoInProbability_iff_norm]
    intro eps heps
    simpa only [sub_self, norm_zero, not_le.mpr heps, Set.ofPred_false,
      measure_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
  | @insert i s his ih =>
    have hit : ∀ j ∈ s, ∀ n a, Integrable (f j n a) ν :=
      fun j hj => hi j (Finset.mem_insert_of_mem hj)
    have ht := ih hit (fun j hj => hr j (Finset.mem_insert_of_mem hj))
    have hh := hr i (Finset.mem_insert_self i s)
    have hn := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
      (show Continuous (fun t : ℝ => -t) by fun_prop).continuousAt ht
    simp only [neg_zero] at hn
    have hs := hh.sub hn
    simp only [sub_zero, sub_neg_eq_add] at hs
    simpa only [Finset.sum_insert his,
      integral_add (hi i (Finset.mem_insert_self i s) _ _)
        (integrable_finsetSum s (fun j hj => hit j hj _ _)), mul_add] using hs

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: nuisanceRates_fractional_product_cross_block_root_n_negligible
/-- For [a valid policy map](hyp:hphi) with [the specified derivative](hyp:hd)
and [a bounded Lipschitz derivative](hyp:hDerivative), suppose [the reference
nuisances are admissible](hyp:he0) and [all fitted nuisances are admissible](hyp:heh).
If componentwise L2 errors are of smaller order in probability than the inverse
fourth root of sample size for [propensities](hyp:hrp),
[level propensities](hyp:hrlev), [treated-outcome masses](hyp:hrP), [every regular
component's instrument shares](hyp:hrs), and [component weights](hyp:hrg), then
[the integrated sum over all regular components of weight errors times fractional
hinge errors, evaluated at sample sizes twice one more than the index and scaled
by the square root of one more than the index, converges in probability to zero](goal). -/
lemma nuisanceRates_fractional_product_cross_block_root_n_negligible
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
    (hrg : FiniteNuisanceRates M μ (fun n a => (eh n a).gamma) e0.gamma) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) * ∫ x,
        ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
          (regularValue (eh (2*(n+1)) a).gamma k j x - regularValue e0.gamma k j x) *
            (hMinus phi L (eh (2*(n+1)) a) k j x - hMinus phi L e0 k j x)
        ∂xLaw M) atTop (fun _ _ => 0) := by
  let F := fun k j n a x =>
    (regularValue (eh (2*(n+1)) a).gamma k j x - regularValue e0.gamma k j x) *
      (hMinus phi L (eh (2*(n+1)) a) k j x - hMinus phi L e0 k j x)
  have hi (k j n : ℕ) (a : A) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
      Integrable (F k j n a) (xLaw M) :=
    (fitted_regular_product_cross_L2_bound M phi hphi L e0 (eh (2*(n+1)) a)
      he0 (heh _ a) k j hk hj).1
  apply dml_finite_integral_root_n_negligible μ (xLaw M) (Finset.range L.K)
    (fun k n a x => ∑ j ∈ Finset.Icc 1 (L.l k), F k j n a x)
  · intro k hk n a
    exact integrable_finsetSum _ (fun j hj => hi k j n a
      (Finset.mem_range.mp hk) (Finset.mem_Icc.mp hj))
  · intro k hk
    apply dml_finite_integral_root_n_negligible μ (xLaw M) (Finset.Icc 1 (L.l k)) (F k)
    · intro j hj n a
      exact hi k j n a (Finset.mem_range.mp hk) (Finset.mem_Icc.mp hj)
    · intro j hj
      exact nuisanceRates_regular_product_cross_root_n_negligible M μ phi dphi hphi hd
        hDerivative L e0 eh he0 heh hrp hrlev hrP hrs hrg k j
        (Finset.mem_range.mp hk) (Finset.mem_Icc.mp hj)

-- @node: nuisanceRates_fractional_hinge_bias_block_root_n_negligible
/-- For [a valid policy map](hyp:hphi) with [the specified derivative](hyp:hd)
and [a bounded Lipschitz derivative](hyp:hDerivative), suppose [the reference
nuisances](hyp:he0) and [all fitted nuisances](hyp:heh) are admissible and componentwise
L2 errors are of smaller order in probability than the inverse fourth
root of sample size for [propensities](hyp:hrp), [level propensities](hyp:hrlev),
[treated-outcome masses](hyp:hrP), and [each regular component's instrument shares](hyp:hrs).
If [the separation constant is positive](hyp:hc) and [every regular component's
reference pooled-policy interval has width at least that constant and its boundary
is at least that far from both endpoints almost surely](hyp:hgap), then [the
integrated sum of fitted-weighted hinge remainders at sample sizes twice one more
than the index, scaled by the square root of one more than the index, converges
in probability to zero](goal). -/
lemma nuisanceRates_fractional_hinge_bias_block_root_n_negligible
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
    (c : ℝ) (hc : 0 < c)
    (hgap : ∀ k ∈ Finset.range L.K, ∀ j ∈ Finset.Icc 1 (L.l k),
      ∀ᵐ x ∂xLaw M,
      c ≤ pooledQBin phi L e0 k j x - pooledQBin phi L e0 k (j-1) x ∧
      c ≤ |positiveValue e0.pLev (k+1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k (j-1) x| ∧
      c ≤ |positiveValue e0.pLev (k+1) x - binFullJ L e0 k x -
        pooledQBin phi L e0 k j x|) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => Real.sqrt ((n+1 : ℕ) : ℝ) * ∫ x,
        ∑ k ∈ Finset.range L.K, ∑ j ∈ Finset.Icc 1 (L.l k),
        regularValue (eh (2*(n+1)) a).gamma k j x * binaryFittedHingeRemainder
          (pooledQBin phi L e0 k j x) (pooledQBin phi L e0 k (j-1) x)
          (positiveValue e0.pLev (k+1) x - binFullJ L e0 k x)
          (pooledQBin phi L (eh (2*(n+1)) a) k j x)
          (pooledQBin phi L (eh (2*(n+1)) a) k (j-1) x)
          (positiveValue (eh (2*(n+1)) a).pLev (k+1) x -
            binFullJ L (eh (2*(n+1)) a) k x) ∂xLaw M) atTop (fun _ _ => 0) := by
  let F := fun k j n a x => regularValue (eh (2*(n+1)) a).gamma k j x *
    binaryFittedHingeRemainder
      (pooledQBin phi L e0 k j x) (pooledQBin phi L e0 k (j-1) x)
      (positiveValue e0.pLev (k+1) x - binFullJ L e0 k x)
      (pooledQBin phi L (eh (2*(n+1)) a) k j x)
      (pooledQBin phi L (eh (2*(n+1)) a) k (j-1) x)
      (positiveValue (eh (2*(n+1)) a).pLev (k+1) x -
        binFullJ L (eh (2*(n+1)) a) k x)
  have hi (k j n : ℕ) (a : A) (hk : k ∈ Finset.range L.K)
      (hj : j ∈ Finset.Icc 1 (L.l k)) : Integrable (F k j n a) (xLaw M) :=
    (fitted_fractional_hinge_bias_energy_bound M phi hphi L e0 (eh (2*(n+1)) a)
      he0 (heh _ a) k j c hc (hgap k hk j hj)).1
  apply dml_finite_integral_root_n_negligible μ (xLaw M) (Finset.range L.K)
    (fun k n a x => ∑ j ∈ Finset.Icc 1 (L.l k), F k j n a x)
  · intro k hk n a
    exact integrable_finsetSum _ (fun j hj => hi k j n a hk hj)
  · intro k hk
    apply dml_finite_integral_root_n_negligible μ (xLaw M) (Finset.Icc 1 (L.l k)) (F k)
    · intro j hj n a
      exact hi k j n a hk hj
    · intro j hj
      exact nuisanceRates_fractional_hinge_bias_root_n_negligible M μ phi dphi hphi hd
        hDerivative L e0 eh he0 heh hrp hrlev hrP hrs k j c hc (hgap k hk j hj)

end Papers.TbsPrteOptimalTransport
