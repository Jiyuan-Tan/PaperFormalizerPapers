module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLQuantileBandMeans
/-! Centering moving-band discrepancies preserves their vanishing second moments.
The treated conditional law has mass at most one, including off-support fibers,
so subtracting its integral contracts the squared energy without normalization. -/
public section
set_option linter.unusedFintypeInType false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

-- @node: integral_centered_sq_le_of_mass_le_one
/-- If [a function is square integrable under a finite measure](hyp:hf) and
[that measure has total mass at most one](hyp:hmass), then [subtracting its integral
does not increase its integrated square](goal). -/
lemma integral_centered_sq_le_of_mass_le_one {B : Type*} [MeasurableSpace B]
    (ν : Measure B) [IsFiniteMeasure ν] (f : B → ℝ)
    (hf : MemLp f 2 ν) (hmass : ν.real univ ≤ 1) :
    (∫ y, (f y - ∫ z, f z ∂ν) ^ 2 ∂ν) ≤ ∫ y, f y ^ 2 ∂ν := by
  let m := ∫ y, f y ∂ν
  have hfi : Integrable f ν := hf.integrable (by norm_num)
  have heq : (∫ y, (f y - m) ^ 2 ∂ν) =
      (∫ y, f y ^ 2 ∂ν) - 2 * m ^ 2 + ν.real univ * m ^ 2 := by
    simp_rw [show ∀ y, (f y - m) ^ 2 = f y ^ 2 - (2 * m) * f y + m ^ 2
      from fun y => by ring]
    have hs : Integrable (fun y => f y ^ 2 - (2 * m) * f y) ν :=
      hf.integrable_sq.sub (hfi.const_mul (2 * m))
    rw [integral_add hs (integrable_const (m ^ 2)),
      integral_sub hf.integrable_sq (hfi.const_mul (2 * m)),
      integral_const_mul, integral_const]
    dsimp only [m]
    simp only [smul_eq_mul]
    ring
  change (∫ y, (f y - m) ^ 2 ∂ν) ≤ _
  rw [heq]
  have hmass' := mul_le_mul_of_nonneg_right hmass (sq_nonneg m)
  nlinarith [sq_nonneg m]

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: treatedLaw_integrated_centered_sq_le
/-- If [a covariate-outcome function is measurable](hyp:hf), [each outcome section is
square integrable under the treated law](hyp:hmem), and [its conditional squared
energy is integrable over covariates](hyp:hi), then [centering by its treated-law
integral gives an integrable conditional squared energy whose covariate average is
no larger than the uncentered energy](goal). -/
lemma treatedLaw_integrated_centered_sq_le
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (k : ℕ)
    (f : X × ℝ → ℝ) (hf : Measurable f)
    (hmem : ∀ x, MemLp (fun y => f (x, y)) 2 (treatedLaw M L k x))
    (hi : Integrable (fun x => ∫ y, f (x, y) ^ 2 ∂treatedLaw M L k x) (xLaw M)) :
    Integrable (fun x => ∫ y,
      (f (x, y) - ∫ z, f (x, z) ∂treatedLaw M L k x) ^ 2
        ∂treatedLaw M L k x) (xLaw M) ∧
    (∫ x, ∫ y, (f (x, y) - ∫ z, f (x, z) ∂treatedLaw M L k x) ^ 2
      ∂treatedLaw M L k x ∂xLaw M) ≤
      ∫ x, ∫ y, f (x, y) ^ 2 ∂treatedLaw M L k x ∂xLaw M := by
  have hb (x : X) :
      (∫ y, (f (x, y) - ∫ z, f (x, z) ∂treatedLaw M L k x) ^ 2
        ∂treatedLaw M L k x) ≤ ∫ y, f (x, y) ^ 2 ∂treatedLaw M L k x := by
    let := treatedLaw_isFiniteMeasure M L k x
    exact integral_centered_sq_le_of_mass_le_one _ _ (hmem x)
      (treatedLaw_mass_le_one M L k x)
  have hm : Measurable (fun x => ∫ y,
      (f (x, y) - ∫ z, f (x, z) ∂treatedLaw M L k x) ^ 2
        ∂treatedLaw M L k x) := by
    apply measurable_treatedLaw_integral_prod M L k
      (fun p : X × ℝ =>
        (f p - ∫ z, f (p.1, z) ∂treatedLaw M L k p.1) ^ 2)
    exact (hf.sub ((measurable_treatedLaw_integral_prod M L k f hf).comp
      measurable_fst)).pow_const 2
  have hi' : Integrable (fun x => ∫ y,
      (f (x, y) - ∫ z, f (x, z) ∂treatedLaw M L k x) ^ 2
        ∂treatedLaw M L k x) (xLaw M) :=
    hi.mono' hm.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (integral_nonneg (fun y => sq_nonneg
          (f (x, y) - ∫ z, f (x, z) ∂treatedLaw M L k x)))]
      exact hb x)
  exact ⟨hi', integral_mono hi' hi hb⟩

-- @node: treatedLaw_centered_sq_tendsto_probability_zero
/-- For [measurable random functions](hyp:hf) with [square-integrable treated-law
sections](hyp:hmem) and [conditional squared energies integrable over covariates](hyp:hi),
if [their integrated squared energies converge to zero in probability](hyp:hr),
then [their integrated squared energies after subtracting the treated-law integrals
also converge to zero in probability](goal). -/
lemma treatedLaw_centered_sq_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X) (k : ℕ)
    (f : ℕ → A → X × ℝ → ℝ)
    (hf : ∀ n a, Measurable (f n a))
    (hmem : ∀ n a x, MemLp (fun y => f n a (x, y)) 2 (treatedLaw M L k x))
    (hi : ∀ n a, Integrable
      (fun x => ∫ y, f n a (x, y) ^ 2 ∂treatedLaw M L k x) (xLaw M))
    (hr : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, ∫ y, f n a (x, y) ^ 2
        ∂treatedLaw M L k x ∂xLaw M) atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, ∫ y,
        (f n a (x, y) - ∫ z, f n a (x, z) ∂treatedLaw M L k x) ^ 2
          ∂treatedLaw M L k x ∂xLaw M) atTop (fun _ _ => 0) := by
  apply probability_zero_of_nonneg_le μ _ _ hr
  intro n
  apply Eventually.of_forall
  intro a
  exact ⟨integral_nonneg fun x => integral_nonneg fun y => sq_nonneg _,
    (treatedLaw_integrated_centered_sq_le M L k (f n a) (hf n a)
      (hmem n a) (hi n a)).2⟩

-- The coefficient is the fitted product-score weight. Its bound follows from
-- clipping; the two endpoint energies follow from the encoded nuisance rates.
open Classical in
-- @node: encoded_continuous_centered_quantile_band_sq_tendsto_probability_zero
/-- Suppose [the true continuous nuisance is admissible](hyp:he0), [the fitted
nuisances are clipped](hyp:hclip), [their shares lie in the simplex](hyp:hshares),
[their encoded components are measurable](hyp:hm), [boundary densities are bounded](hyp:hd),
and [the encoded nuisance estimates satisfy the finite nuisance rates](hyp:hrates).
If [the treated level is adjacent to the lower boundary](hyp:hkc) and [also adjacent
to the upper boundary](hyp:hkd), then [the fitted product-score-weighted difference
between fitted and true quantile-band indicators, centered by its treated-law
integral, has integrated squared energy converging to zero in probability along even
sample sizes](goal). -/
lemma encoded_continuous_centered_quantile_band_sq_tendsto_probability_zero
    [Fintype Z] (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X)
    (he0 : ContAdmissible M L (trueNuisance M L))
    (eh : ℕ → A → NuisanceCont L)
    (hclip : ∀ n s, ContClipping M L (eh n s))
    (hshares : ∀ n s, ContFittedSharesSimplex L (eh n s))
    (hm : ∀ n s c, Measurable (contComponent M L (eh n s) c))
    (hd : BoundaryDensitiesBounded M L)
    (hrates : FiniteNuisanceRates M μ (fun n s => contComponent M L (eh n s))
      (contComponent M L (trueNuisance M L)))
    (c d : BoundaryIndex L) (g : RegularIndex L) (k' : ℕ)
    (hkc : k' = c.val.1 + 1 ∨ (1 ≤ c.val.1 ∧ k' = c.val.1))
    (hkd : k' = d.val.1 + 1 ∨ (1 ≤ d.val.1 ∧ k' = d.val.1)) :
    let f : ℕ → A → X × ℝ → ℝ := fun n s p =>
      (eh (2*(n+1)) s).gamma g p.1 *
        (indicator ((eh (2*(n+1)) s).nu c p.1 < p.2 ∧
            p.2 ≤ (eh (2*(n+1)) s).nu d p.1) -
          indicator ((trueNuisance M L).nu c p.1 < p.2 ∧
            p.2 ≤ (trueNuisance M L).nu d p.1))
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n s => ∫ x, ∫ y,
        (f n s (x, y) - ∫ z, f n s (x, z) ∂treatedLaw M L k' x) ^ 2
          ∂treatedLaw M L k' x ∂xLaw M) atTop (fun _ _ => 0) := by
  classical
  dsimp only
  let f : ℕ → A → X × ℝ → ℝ := fun n s p =>
    (eh (2*(n+1)) s).gamma g p.1 *
      (indicator ((eh (2*(n+1)) s).nu c p.1 < p.2 ∧
          p.2 ≤ (eh (2*(n+1)) s).nu d p.1) -
        indicator ((trueNuisance M L).nu c p.1 < p.2 ∧
          p.2 ≤ (trueNuisance M L).nu d p.1))
  have her n s := restrictContShares_admissible_of_encoded_clipping
    M L (eh n s) (hclip n s) (hshares n s) (hm n s)
  have hcoords n s : Measurable ((eh n s).nu c) ∧ Measurable ((eh n s).nu d) ∧
      Measurable ((eh n s).gamma g) ∧
      (∀ᵐ x ∂xLaw M, |(eh n s).gamma g x| ≤ 1) := by
    rcases her n s with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hg, hgm,
      _, _, _, hnm, _⟩
    refine ⟨hnm c, hnm d, hgm g, ?_⟩
    filter_upwards [hg g] with x hx
    change 0 ≤ (eh n s).gamma g x ∧ (eh n s).gamma g x ≤ 1 at hx
    simpa only [abs_of_nonneg hx.1] using hx.2
  have ht (b : BoundaryIndex L) : Measurable ((trueNuisance M L).nu b) := by
    rcases he0 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hnu, _⟩
    exact hnu b
  have hB (a b : X → ℝ) (ha : Measurable a) (hb : Measurable b) :
      Measurable (fun p : X × ℝ => indicator (a p.1 < p.2 ∧ p.2 ≤ b p.1)) := by
    fun_prop
  have hf n s : Measurable (f n s) := by
    exact ((hcoords _ s).2.2.1.comp measurable_fst).mul
      ((hB _ _ (hcoords _ s).1 (hcoords _ s).2.1).sub (hB _ _ (ht c) (ht d)))
  have hmem n s x : MemLp (fun y => f n s (x, y)) 2 (treatedLaw M L k' x) := by
    let := treatedLaw_isFiniteMeasure M L k' x
    apply MemLp.of_bound (by
      first | fun_prop | exact ((hf n s).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      |(eh (2*(n+1)) s).gamma g x|
    apply Eventually.of_forall
    intro y
    dsimp only [f]
    unfold indicator
    split_ifs <;> simp [Real.norm_eq_abs]
  apply treatedLaw_centered_sq_tendsto_probability_zero M μ L k' f hf hmem
  · intro n s
    exact (treatedLaw_weighted_quantile_band_integrated_sq_bound M L k'
      ((trueNuisance M L).nu c) ((trueNuisance M L).nu d)
      ((eh (2*(n+1)) s).nu c) ((eh (2*(n+1)) s).nu d)
      ((eh (2*(n+1)) s).gamma g) 1 (ht c) (ht d)
      (hcoords _ s).1 (hcoords _ s).2.1 (hcoords _ s).2.2.1
      (hcoords _ s).2.2.2).1
  · exact encoded_continuous_weighted_quantile_band_sq_tendsto_probability_zero
      M μ L he0 eh hclip hshares hm hd hrates c d g k' hkc hkd

end Papers.TbsPrteOptimalTransport
