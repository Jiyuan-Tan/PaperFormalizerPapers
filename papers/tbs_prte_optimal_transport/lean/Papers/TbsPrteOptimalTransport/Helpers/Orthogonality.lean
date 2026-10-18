module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLProcedure
public import Papers.TbsPrteOptimalTransport.Helpers.BinaryBranches
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
/-! Regime hypotheses and the population score moment equations. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
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
  [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)
variable {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
variable (S : ObservedSample M μ) [Fintype Z] [DecidableEq Z]
/-- For [the latent instrumental-variable model](hyp:M), [sampling law](hyp:μ),
[observed sample](hyp:S), [training split](hyp:I₁), [evaluation split](hyp:I₂),
[estimated propensities](hyp:pHat), [policy transformation](hyp:phi),
[recovery thresholds](hyp:rho), [level separation gap](hyp:gap),
[denominator clipping constant](hyp:cpi), [population level structure](hyp:L),
[auxiliary margin constant, unused in this condition](hyp:ch), and
[continuous nuisance estimates on recovered levels](hyp:eHat), the
[finite-error continuous DML regime](goal) requires [dynamic continuous fitting](step:1),
[componentwise finite integral L2 errors of order smaller in probability than sample size
to the negative one-quarter power along even sample sizes](step:2),
[bounded treated-outcome densities near band boundaries](step:3), and
[no treated-outcome atom at the lower outcome endpoint](step:4). -/
def FiniteContDMLRegime (I₁ I₂ : SampleSplit A) (pHat : ℕ → A → Z → X → ℝ)
    (phi : Z → X → ℝ → ℝ) (rho : ℕ → ℝ) (gap cpi : ℝ)
    (L : LevelData Z X) (ch : ℝ)
    (eHat : ∀ n a, NuisanceCont (recoveredData M S I₁ I₂ pHat phi rho gap n a)) : Prop :=
  DynamicContFit M S I₁ I₂ pHat phi rho gap eHat cpi ∧
  FiniteNuisanceRates M μ (fun n a c => contComponent M _ (eHat n a) c)
    (fun c => contComponent M L (trueNuisance M L) c) ∧
  BoundaryDensitiesBounded M L ∧ NoAtomAtLowerEndpoint M L
/-- For [the latent instrumental-variable model](hyp:M), [sampling law](hyp:μ),
[observed sample](hyp:S), [training split](hyp:I₁), [evaluation split](hyp:I₂),
[estimated propensities](hyp:pHat), [policy transformation](hyp:phi),
[recovery thresholds](hyp:rho), [level separation gap](hyp:gap),
[denominator clipping constant](hyp:cpi), [population level structure](hyp:L),
[auxiliary margin constant, unused in this condition](hyp:ch), and
[binary nuisance estimates on recovered levels](hyp:eHat), the
[finite-error binary DML regime](goal) requires [dynamic binary fitting](step:1),
[componentwise finite integral L2 errors of order smaller in probability than sample size
to the negative one-quarter power along even sample sizes](step:2),
[outcomes equal to zero or one almost surely](step:3), and
[a uniform positive separation of the binary outcome thresholds](step:4). -/
def FiniteBinDMLRegime (I₁ I₂ : SampleSplit A) (pHat : ℕ → A → Z → X → ℝ)
    (phi : Z → X → ℝ → ℝ) (rho : ℕ → ℝ) (gap cpi : ℝ)
    (L : LevelData Z X) (ch : ℝ)
    (eHat : ∀ n a, NuisanceBin (recoveredData M S I₁ I₂ pHat phi rho gap n a)) : Prop :=
  DynamicBinFit M S I₁ I₂ pHat phi rho gap eHat cpi ∧
  FiniteNuisanceRates M μ (fun n a c => binComponent _ (eHat n a) c)
    (fun c => binComponent L (eta0Bin M L) c) ∧
  OutcomeBinaryAE M ∧ DiscreteOutcomeGap M L

/-- For [the latent instrumental-variable model](hyp:M), [sampling law](hyp:μ),
[observed sample](hyp:S), [training split](hyp:I₁), [evaluation split](hyp:I₂),
[estimated propensities](hyp:pHat), [policy transformation](hyp:phi),
[recovery thresholds](hyp:rho), [level separation gap](hyp:gap),
[denominator clipping constant](hyp:cpi), [population level structure](hyp:L),
[auxiliary margin constant, unused in this condition](hyp:ch), and
[continuous nuisance estimates on recovered levels](hyp:eHat), the
[continuous DML regime](goal) requires [dynamic continuous fitting](step:1),
[componentwise extended population L2 errors of order smaller in probability than sample
size to the negative one-quarter power along even sample sizes](step:2),
[bounded treated-outcome densities near band boundaries](step:3), and
[no treated-outcome atom at the lower outcome endpoint](step:4). -/
def ContDMLRegime (I₁ I₂ : SampleSplit A) (pHat : ℕ → A → Z → X → ℝ)
    (phi : Z → X → ℝ → ℝ) (rho : ℕ → ℝ) (gap cpi : ℝ)
    (L : LevelData Z X) (ch : ℝ)
    (eHat : ∀ n a, NuisanceCont (recoveredData M S I₁ I₂ pHat phi rho gap n a)) : Prop :=
  DynamicContFit M S I₁ I₂ pHat phi rho gap eHat cpi ∧
  NuisanceRates M μ (fun n a c => contComponent M _ (eHat n a) c)
    (fun c => contComponent M L (trueNuisance M L) c) ∧
  BoundaryDensitiesBounded M L ∧ NoAtomAtLowerEndpoint M L
/-- For [the latent instrumental-variable model](hyp:M), [sampling law](hyp:μ),
[observed sample](hyp:S), [training split](hyp:I₁), [evaluation split](hyp:I₂),
[estimated propensities](hyp:pHat), [policy transformation](hyp:phi),
[recovery thresholds](hyp:rho), [level separation gap](hyp:gap),
[denominator clipping constant](hyp:cpi), [population level structure](hyp:L),
[auxiliary margin constant, unused in this condition](hyp:ch), and
[binary nuisance estimates on recovered levels](hyp:eHat), the
[binary DML regime](goal) requires [dynamic binary fitting](step:1),
[componentwise extended population L2 errors of order smaller in probability than sample
size to the negative one-quarter power along even sample sizes](step:2),
[outcomes equal to zero or one almost surely](step:3), and
[a uniform positive separation of the binary outcome thresholds](step:4). -/
def BinDMLRegime (I₁ I₂ : SampleSplit A) (pHat : ℕ → A → Z → X → ℝ)
    (phi : Z → X → ℝ → ℝ) (rho : ℕ → ℝ) (gap cpi : ℝ)
    (L : LevelData Z X) (ch : ℝ)
    (eHat : ∀ n a, NuisanceBin (recoveredData M S I₁ I₂ pHat phi rho gap n a)) : Prop :=
  DynamicBinFit M S I₁ I₂ pHat phi rho gap eHat cpi ∧
  NuisanceRates M μ (fun n a c => binComponent _ (eHat n a) c)
    (fun c => binComponent L (eta0Bin M L) c) ∧
  OutcomeBinaryAE M ∧ DiscreteOutcomeGap M L

/-- For [continuous nuisance records fitted on the recovered levels](hyp:eHat), if [the continuous DML regime holds with extended population L2 nuisance rates](hyp:h),
then [the continuous DML regime with finite integral nuisance rates also holds for the
same sample, fits, and level structure](goal). -/
lemma ContDMLRegime.finite (I₁ I₂ : SampleSplit A) (pHat : ℕ → A → Z → X → ℝ)
    (phi : Z → X → ℝ → ℝ) (rho : ℕ → ℝ) (gap cpi : ℝ) (L : LevelData Z X) (ch : ℝ)
    (eHat : ∀ n a, NuisanceCont (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (h : ContDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat) :
    FiniteContDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat := by
  exact ⟨h.1, NuisanceRates.finite M μ _ _ h.2.1, h.2.2⟩
/-- For [binary nuisance records fitted on the recovered levels](hyp:eHat), if [the binary DML regime holds with extended population L2 nuisance rates](hyp:h),
then [the binary DML regime with finite integral nuisance rates also holds for the
same sample, fits, and level structure](goal). -/
lemma BinDMLRegime.finite (I₁ I₂ : SampleSplit A) (pHat : ℕ → A → Z → X → ℝ)
    (phi : Z → X → ℝ → ℝ) (rho : ℕ → ℝ) (gap cpi : ℝ) (L : LevelData Z X) (ch : ℝ)
    (eHat : ∀ n a, NuisanceBin (recoveredData M S I₁ I₂ pHat phi rho gap n a))
    (h : BinDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat) :
    FiniteBinDMLRegime M μ S I₁ I₂ pHat phi rho gap cpi L ch eHat := by
  exact ⟨h.1, NuisanceRates.finite M μ _ _ h.2.1, h.2.2⟩

/-- For [the population model](hyp:M), [an uncentered observation score](hyp:score), and
[a centering value](hyp:theta), the [population score variance](goal) is the population
integral of the squared difference between the score and that value. -/
noncomputable def populationVariance (score : Obs X Z → ℝ) (theta : ℝ) :=
  ∫ o, (score o - theta)^2 ∂observationLaw M
  -- @realizes \sigma^2(population variance of the true uncentered score)
-- @node: simplex_affine_direction_sum_zero
/-- If [the perturbation size is nonzero](hyp:ht), [the original weights sum to one over
the finite index set](hyp:h0), and [the weights after the affine perturbation also sum
to one](hyp:htotal), then [the perturbation directions sum to zero over that set](goal). -/
lemma simplex_affine_direction_sum_zero {ι : Type*} (s : Finset ι)
    (a d : ι → ℝ) (t : ℝ) (ht : t ≠ 0)
    (h0 : ∑ z ∈ s, a z = 1) (htotal : ∑ z ∈ s, (a z + t * d z) = 1) :
    ∑ z ∈ s, d z = 0 := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, h0] at htotal
  have hmul : t * ∑ z ∈ s, d z = 0 := by linarith
  exact (mul_eq_zero.mp hmul).resolve_left ht

-- @node: cont_admissible_share_direction
/-- If [a continuous nuisance direction is admissible at the given nuisance vector](hyp:hd),
then [its share components sum to zero within the chosen regular policy group for almost
every population covariate value](goal). -/
lemma cont_admissible_share_direction (L : LevelData Z X) (eta del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl eta) (.inl del)) (a : RegularIndex L) :
    ∀ᵐ x ∂xLaw M, ∑ z ∈ L.T a.val.1 a.val.2, del.share a z x = 0 := by
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  have h0 := hpath 0 (by simpa using hr)
  have ht := hpath (r / 2) (by rw [abs_of_pos (by positivity)]; linarith)
  rcases h0 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, hs0⟩
  rcases ht with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, hst⟩
  filter_upwards [hs0 a, hst a] with x hx0 hxt
  apply simplex_affine_direction_sum_zero (L.T a.val.1 a.val.2)
    (fun z => eta.share a z x) (fun z => del.share a z x) (r / 2) (by positivity)
  · have hx : (∑ z ∈ L.T a.val.1 a.val.2,
        (eta.share a z x + 0 * del.share a z x)) = 1 := hx0.1
    simpa using hx
  · exact hxt.1

-- @node: bin_admissible_share_direction
/-- If [a binary nuisance direction is admissible at the given nuisance vector](hyp:hd),
then [its share components sum to zero within the chosen regular policy group for almost
every population covariate value](goal). -/
lemma bin_admissible_share_direction (L : LevelData Z X) (eta del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr eta) (.inr del)) (a : RegularIndex L) :
    ∀ᵐ x ∂xLaw M, ∑ z ∈ L.T a.val.1 a.val.2, del.share a z x = 0 := by
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  have h0 := hpath 0 (by simpa using hr)
  have ht := hpath (r / 2) (by rw [abs_of_pos (by positivity)]; linarith)
  rcases h0 with ⟨_, _, _, _, _, _, _, _, hs0, _⟩
  rcases ht with ⟨_, _, _, _, _, _, _, _, hst, _⟩
  filter_upwards [hs0 a, hst a] with x hx0 hxt
  apply simplex_affine_direction_sum_zero (L.T a.val.1 a.val.2)
    (fun z => eta.share a z x) (fun z => del.share a z x) (r / 2) (by positivity)
  · have hx : (∑ z ∈ L.T a.val.1 a.val.2,
        (eta.share a z x + 0 * del.share a z x)) = 1 := hx0.1
    simpa using hx
  · exact hxt.1

-- @node: simplex_common_policy_share_path
/-- If [the share directions sum to zero over a finite group](hyp:hd) and
[all policy values in that group equal a common value](hyp:hq), then
[an affine change in the shares leaves the share-weighted policy sum unchanged at every
perturbation size](goal). -/
lemma simplex_common_policy_share_path {ι : Type*} (s : Finset ι)
    (a d q : ι → ℝ) (q0 : ℝ) (hd : ∑ z ∈ s, d z = 0)
    (hq : ∀ z ∈ s, q z = q0) (t : ℝ) :
    (∑ z ∈ s, (a z + t * d z) * q z) = ∑ z ∈ s, a z * q z := by
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  have hz : ∑ z ∈ s, t * d z * q z = 0 := by
    calc
      _ = ∑ z ∈ s, t * (d z * q0) := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [hq z hz, mul_assoc]
      _ = t * ((∑ z ∈ s, d z) * q0) := by
        rw [← Finset.mul_sum, ← Finset.sum_mul]
      _ = 0 := by rw [hd]; ring
  rw [hz, add_zero]

-- @node: simplex_common_policy_share_deriv
/-- If [the share directions sum to zero over a finite group](hyp:hd) and
[all policy values in that group equal a common value](hyp:hq), then
[the share-weighted policy sum has derivative zero at zero along the affine share path](goal). -/
lemma simplex_common_policy_share_deriv {ι : Type*} (s : Finset ι)
    (a d q : ι → ℝ) (q0 : ℝ) (hd : ∑ z ∈ s, d z = 0)
    (hq : ∀ z ∈ s, q z = q0) :
    HasDerivAt (fun t : ℝ => ∑ z ∈ s, (a z + t * d z) * q z) 0 0 := by
  have hfun : (fun t : ℝ => ∑ z ∈ s, (a z + t * d z) * q z) =
      (fun _ : ℝ => ∑ z ∈ s, a z * q z) := by
    funext t
    exact simplex_common_policy_share_path s a d q q0 hd hq t
  rw [hfun]
  exact hasDerivAt_const 0 _

-- @node: simplex_pooling_error_product
/-- If [the population shares sum to one](hyp:ha) and [the fitted shares also sum to
one](hyp:hahat) over a finite group, then [the sum of share errors times fitted policy
values equals the sum of share errors times deviations of those values from any common
reference value](goal). -/
lemma simplex_pooling_error_product {ι : Type*} (s : Finset ι)
    (a ahat qhat : ι → ℝ) (q0 : ℝ)
    (ha : ∑ z ∈ s, a z = 1) (hahat : ∑ z ∈ s, ahat z = 1) :
    (∑ z ∈ s, (ahat z - a z) * qhat z) =
      ∑ z ∈ s, (ahat z - a z) * (qhat z - q0) := by
  have hzero : ∑ z ∈ s, (ahat z - a z) * q0 = 0 := by
    rw [← Finset.sum_mul, Finset.sum_sub_distrib, hahat, ha]
    ring
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, hzero, sub_zero]

-- @node: pooledQ_share_update
/-- If [share directions sum to zero in every regular group at the chosen covariate
value](hyp:hs) and [policy-transformed nuisance propensities equal each group's policy
level on its instrument set](hyp:hq), then [an affine update of the continuous nuisance
shares leaves the pooled policy value unchanged at the chosen indices](goal). -/
lemma pooledQ_share_update (phi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (eta del : NuisanceCont L) (x : X) (t : ℝ)
    (hs : ∀ a : RegularIndex L, ∑ z ∈ L.T a.val.1 a.val.2, del.share a z x = 0)
    (hq : ∀ k j z, k ≤ L.K → 1 ≤ j → j ≤ L.l k →
      z ∈ L.T k j → phi z x (eta.prop z x) = L.qLev k j x) (k j : ℕ) :
    pooledQ phi L {eta with share := fun a z x => eta.share a z x + t * del.share a z x} k j x =
      pooledQ phi L eta k j x := by
  unfold pooledQ
  split
  · rfl
  · split
    · rfl
    · unfold shareValue
      by_cases ha : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k
      · simp only [dif_pos ha]
        exact simplex_common_policy_share_path (L.T k j)
          (fun z => eta.share ⟨(k,j),ha⟩ z x) (fun z => del.share ⟨(k,j),ha⟩ z x)
          (fun z => phi z x (eta.prop z x)) (L.qLev k j x)
          (hs ⟨(k,j),ha⟩) (fun z hz => hq k j z ha.1 ha.2.1 ha.2.2 hz) t
      · simp only [dif_neg ha]

-- @node: pooledQBin_share_update
/-- If [share directions sum to zero in every regular group at the chosen covariate
value](hyp:hs) and [policy-transformed nuisance propensities equal each group's policy
level on its instrument set](hyp:hq), then [an affine update of the binary nuisance
shares leaves the pooled policy value unchanged at the chosen indices](goal). -/
lemma pooledQBin_share_update (phi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (eta del : NuisanceBin L) (x : X) (t : ℝ)
    (hs : ∀ a : RegularIndex L, ∑ z ∈ L.T a.val.1 a.val.2, del.share a z x = 0)
    (hq : ∀ k j z, k ≤ L.K → 1 ≤ j → j ≤ L.l k →
      z ∈ L.T k j → phi z x (eta.prop z x) = L.qLev k j x) (k j : ℕ) :
    pooledQBin phi L {eta with share := fun a z x => eta.share a z x + t * del.share a z x} k j x =
      pooledQBin phi L eta k j x := by
  unfold pooledQBin
  split
  · rfl
  · split
    · rfl
    · by_cases ha : k ≤ L.K ∧ 1 ≤ j ∧ j ≤ L.l k
      · simp only [dif_pos ha]
        exact simplex_common_policy_share_path (L.T k j)
          (fun z => eta.share ⟨(k,j),ha⟩ z x) (fun z => del.share ⟨(k,j),ha⟩ z x)
          (fun z => phi z x (eta.prop z x)) (L.qLev k j x)
          (hs ⟨(k,j),ha⟩) (fun z hz => hq k j z ha.1 ha.2.1 ha.2.2 hz) t
      · simp only [dif_neg ha]

-- @node: psiCont_share_update
/-- If [the number of levels is positive](hyp:hK), [share directions sum to zero in
every regular group at the observation's covariates](hyp:hs), and
[policy-transformed nuisance propensities equal their group policy levels](hyp:hq), then
[an affine update of the shares leaves the continuous observation score unchanged](goal). -/
lemma psiCont_share_update (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (hK : LevelCountPos L.K) (eta del : NuisanceCont L) (o : Obs X Z) (t : ℝ)
    (hs : ∀ a : RegularIndex L, ∑ z ∈ L.T a.val.1 a.val.2, del.share a z o.1 = 0)
    (hq : ∀ k j z, k ≤ L.K → 1 ≤ j → j ≤ L.l k →
      z ∈ L.T k j → phi z o.1 (eta.prop z o.1) = L.qLev k j o.1) :
    psiCont M phi dphi L hK o
      {eta with share := fun a z x => eta.share a z x + t * del.share a z x} =
      psiCont M phi dphi L hK o eta := by
  have hp := pooledQ_share_update phi L eta del o.1 t hs hq
  simp only [psiCont, psiProd, contScoreComponents]
  simp only [hp]
  rfl

-- @node: psiBin_share_update
/-- If [the number of levels is positive](hyp:hK), [share directions sum to zero in
every regular group at the observation's covariates](hyp:hs), and
[policy-transformed nuisance propensities equal their group policy levels](hyp:hq), then
[an affine update of the shares leaves the binary observation score unchanged](goal). -/
lemma psiBin_share_update (phi dphi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (hK : LevelCountPos L.K) (eta del : NuisanceBin L) (o : Obs X Z) (t : ℝ)
    (hs : ∀ a : RegularIndex L, ∑ z ∈ L.T a.val.1 a.val.2, del.share a z o.1 = 0)
    (hq : ∀ k j z, k ≤ L.K → 1 ≤ j → j ≤ L.l k →
      z ∈ L.T k j → phi z o.1 (eta.prop z o.1) = L.qLev k j o.1) :
    psiBin M phi dphi L hK o
      {eta with share := fun a z x => eta.share a z x + t * del.share a z x} =
      psiBin M phi dphi L hK o eta := by
  have hp := pooledQBin_share_update phi L eta del o.1 t hs hq
  simp only [psiBin, psiProdBin, binScoreComponents, hMinus, Dbd, Iact, Edom]
  simp only [hp]
  rfl

-- @node: observationLaw_covariate_ae
/-- If [a covariate property holds almost everywhere under the population covariate
law](hyp:hp), then [it holds for the covariates of almost every observation under the
population observation law](goal). -/
lemma observationLaw_covariate_ae (p : X → Prop) (hp : ∀ᵐ x ∂xLaw M, p x) :
    ∀ᵐ o ∂observationLaw M, p o.1 := by
  have hm : Measurable (fun a => (M.Xv a, M.Zv a, M.W a, M.Y a)) := by
    first | fun_prop | exact M.measX.prodMk (M.measZ.prodMk (M.measW.prodMk M.measY))
  have hmap : (observationLaw M).map Prod.fst = xLaw M := by
    simpa only [observationLaw, xLaw, Function.comp_def] using
      Measure.map_map measurable_fst hm
  apply ae_of_ae_map measurable_fst.aemeasurable
  rwa [hmap]

-- @node: continuous_share_score_orthogonality
/-- If [the number of levels is positive](hyp:hK), [the policy preserves the level
ordering and group structure of the true propensities](hyp:hOrder), and
[the continuous nuisance direction is admissible at the truth](hyp:hd), then
[the population continuous score moment has derivative zero at zero when only the true
shares are perturbed affinely in that direction](goal). -/
lemma continuous_share_score_orthogonality (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del)) :
    HasDerivAt (fun t : ℝ => ∫ o, psiCont M phi dphi L hK o
      {trueNuisance M L with share := fun a z x =>
        (trueNuisance M L).share a z x + t * del.share a z x} ∂observationLaw M) 0 0 := by
  have hs := ae_all_iff.mpr (cont_admissible_share_direction M L (trueNuisance M L) del hd)
  have hobs := observationLaw_covariate_ae M _ hs
  rcases hOrder with ⟨_, _, _, _, _, _, hT, _⟩
  have hfun : (fun t : ℝ => ∫ o, psiCont M phi dphi L hK o
      {trueNuisance M L with share := fun a z x =>
        (trueNuisance M L).share a z x + t * del.share a z x} ∂observationLaw M) =
      (fun _ : ℝ => ∫ o, psiCont M phi dphi L hK o (trueNuisance M L) ∂observationLaw M) := by
    funext t
    apply integral_congr_ae
    filter_upwards [hobs] with o ho
    apply psiCont_share_update M phi dphi L hK (trueNuisance M L) del o t ho
    intro k j z hk hj hjl hz
    exact (hT o.1 k j z hk hj hjl).mp hz
  rw [hfun]
  exact hasDerivAt_const 0 _

-- @node: binary_share_score_orthogonality
/-- If [the number of levels is positive](hyp:hK), [the policy preserves the level
ordering and group structure of the true propensities](hyp:hOrder), and
[the binary nuisance direction is admissible at the truth](hyp:hd), then
[the population binary score moment has derivative zero at zero when only the true
shares are perturbed affinely in that direction](goal). -/
lemma binary_share_score_orthogonality (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (hOrder : LevelOrderInvariant M.prop (policyProp phi M.prop) L)
    (del : NuisanceBin L)
    (hd : IsAdmissibleDirection M L (.inr (eta0Bin M L)) (.inr del)) :
    HasDerivAt (fun t : ℝ => ∫ o, psiBin M phi dphi L hK o
      {eta0Bin M L with share := fun a z x =>
        (eta0Bin M L).share a z x + t * del.share a z x} ∂observationLaw M) 0 0 := by
  have hs := ae_all_iff.mpr (bin_admissible_share_direction M L (eta0Bin M L) del hd)
  have hobs := observationLaw_covariate_ae M _ hs
  rcases hOrder with ⟨_, _, _, _, _, _, hT, _⟩
  have hfun : (fun t : ℝ => ∫ o, psiBin M phi dphi L hK o
      {eta0Bin M L with share := fun a z x =>
        (eta0Bin M L).share a z x + t * del.share a z x} ∂observationLaw M) =
      (fun _ : ℝ => ∫ o, psiBin M phi dphi L hK o (eta0Bin M L) ∂observationLaw M) := by
    funext t
    apply integral_congr_ae
    filter_upwards [hobs] with o ho
    apply psiBin_share_update M phi dphi L hK (eta0Bin M L) del o t ho
    intro k j z hk hj hjl hz
    exact (hT o.1 k j z hk hj hjl).mp hz
  rw [hfun]
  exact hasDerivAt_const 0 _

-- The tower and pull-out step used by the product-score cancellations below.
-- @node: score_weighted_conditional_residual_zero
/-- Suppose [the conditioning information is contained in the ambient information](hyp:hm),
[the weight is measurable with respect to the conditioning information](hyp:hw),
[the score is integrable](hyp:hs), [the regression is integrable](hyp:hj),
[the weighted score-minus-regression residual is integrable](hyp:hwr),
[the conditional expectation of the score equals the regression almost everywhere](hyp:hcond),
and [the regression is measurable with respect to the conditioning information](hyp:hjm).
Then [the integral of the weighted residual is zero](goal). -/
lemma score_weighted_conditional_residual_zero {B : Type*} [mB : MeasurableSpace B]
    (ν : Measure B) (m : MeasurableSpace B) (hm : m ≤ mB)
    [SigmaFinite (ν.trim hm)] (w s j : B → ℝ)
    (hw : StronglyMeasurable[m] w) (hs : Integrable s ν) (hj : Integrable j ν)
    (hwr : Integrable (fun b => w b * (s b - j b)) ν)
    (hcond : ν[s | m] =ᵐ[ν] j) (hjm : StronglyMeasurable[m] j) :
    (∫ b, w b * (s b - j b) ∂ν) = 0 := by
  let : MeasurableSpace B := mB
  have hr : ν[s - j | m] =ᵐ[ν] 0 := by
    have hjfix := condExp_of_stronglyMeasurable hm hjm hj
    filter_upwards [condExp_sub hs hj m, hcond] with b hb hc
    simpa only [Pi.sub_apply, hc, hjfix, sub_self, Pi.zero_apply] using hb
  have hid : (fun b => w b * (s b - j b)) = w * (s - j) := by
    funext b
    simp only [Pi.mul_apply, Pi.sub_apply]
  rw [hid] at hwr ⊢
  have hp := condExp_mul_of_stronglyMeasurable_left hw hwr (hs.sub hj)
  calc
    (∫ b, (w * (s - j)) b ∂ν) =
        ∫ b, ν[w * (s - j) | m] b ∂ν := (integral_condExp hm).symm
    _ = ∫ b, (0 : ℝ) ∂ν := by
      apply integral_congr_ae
      filter_upwards [hp, hr] with b hb hz
      simpa only [Pi.mul_apply, hz, Pi.zero_apply, mul_zero] using hb
    _ = 0 := by simp

-- No positivity restriction on g: this also covers the signed full-interval weight.
-- @node: product_score_weight_path
/-- Suppose [the product score, consisting of a weight times a score plus a regression
times the target-minus-weight difference, is integrable](hyp:hbase),
[the weight direction times the score-minus-regression residual is integrable](hyp:hres),
and [that directional residual has integral zero](hyp:hzero). Then
[replacing the weight by itself plus any scalar multiple of the direction leaves the
integral of the product score unchanged](goal). -/
lemma product_score_weight_path {B : Type*} [MeasurableSpace B]
    (ν : Measure B) (g d s j a : B → ℝ)
    (hbase : Integrable (fun b => g b * s b + j b * (a b - g b)) ν)
    (hres : Integrable (fun b => d b * (s b - j b)) ν)
    (hzero : (∫ b, d b * (s b - j b) ∂ν) = 0) (t : ℝ) :
    (∫ b, (g b + t * d b) * s b + j b * (a b - (g b + t * d b)) ∂ν) =
      ∫ b, g b * s b + j b * (a b - g b) ∂ν := by
  have hid : (fun b => (g b + t * d b) * s b + j b * (a b - (g b + t * d b))) =
      (fun b => (g b * s b + j b * (a b - g b)) + t * (d b * (s b - j b))) := by
    funext b
    ring
  rw [hid, integral_add hbase (hres.const_mul t), integral_const_mul, hzero,
    mul_zero, add_zero]

-- @node: product_score_weight_orthogonality
/-- Suppose [the conditioning information is contained in the ambient information](hyp:hm),
[the weight direction is measurable with respect to that conditioning information](hyp:hd),
[the score is integrable](hyp:hs), [the regression is integrable](hyp:hj),
[the regression is measurable with respect to the conditioning information](hyp:hjm),
[it equals the conditional expectation of the score almost everywhere](hyp:hcond),
[the product score formed as weight times score plus regression times target-minus-weight
is integrable](hyp:hbase), and [the direction times the score-minus-regression residual
is integrable](hyp:hres). Then [the population product-score moment has derivative zero
at zero along the affine weight path](goal). -/
lemma product_score_weight_orthogonality {B : Type*} [mB : MeasurableSpace B]
    (ν : Measure B) (m : MeasurableSpace B) (hm : m ≤ mB)
    [SigmaFinite (ν.trim hm)] (g d s j a : B → ℝ)
    (hd : StronglyMeasurable[m] d) (hs : Integrable s ν) (hj : Integrable j ν)
    (hjm : StronglyMeasurable[m] j) (hcond : ν[s | m] =ᵐ[ν] j)
    (hbase : Integrable (fun b => g b * s b + j b * (a b - g b)) ν)
    (hres : Integrable (fun b => d b * (s b - j b)) ν) :
    HasDerivAt (fun t : ℝ => ∫ b, (g b + t * d b) * s b +
      j b * (a b - (g b + t * d b)) ∂ν) 0 0 := by
  let : MeasurableSpace B := mB
  have hz := score_weighted_conditional_residual_zero ν m hm d s j hd hs hj hres hcond hjm
  have heq : (fun t : ℝ => ∫ b, (g b + t * d b) * s b +
      j b * (a b - (g b + t * d b)) ∂ν) =
      (fun _ : ℝ => ∫ b, g b * s b + j b * (a b - g b) ∂ν) := by
    funext t
    exact product_score_weight_path ν g d s j a hbase hres hz t
  rw [heq]
  exact hasDerivAt_const 0 _

-- @node: psiFullJ_regression_decomposition
/-- [The continuous full-interval score for a baseline bin equals the next level's
inverse instrument-group probability weighted treated outcome plus its propensity times
its upper full-interval regression times one minus that inverse probability weight,
less the analogous current-level expression using the lower full-interval regression;
the current-level expression is zero in bin zero](goal). -/
lemma psiFullJ_regression_decomposition (L : LevelData Z X) (e : NuisanceCont L)
    (k : ℕ) (o : Obs X Z) :
    psiFullJ L e k o =
      indicator (o.2.1 ∈ L.S (k+1)) / positiveValue e.piLev (k+1) o.1 * o.2.2.1 * o.2.2.2 +
      positiveValue e.pLev (k+1) o.1 * fullValue e.JfullPlus k o.1 *
        (1 - indicator (o.2.1 ∈ L.S (k+1)) / positiveValue e.piLev (k+1) o.1) -
      (if k = 0 then 0 else
        indicator (o.2.1 ∈ L.S k) / positiveValue e.piLev k o.1 * o.2.2.1 * o.2.2.2 +
        positiveValue e.pLev k o.1 * minusFullValue e k o.1 *
          (1 - indicator (o.2.1 ∈ L.S k) / positiveValue e.piLev k o.1)) := by
  have hk1 : k + 1 ≠ 0 := by omega
  by_cases hk : k = 0
  · have hz : positiveValue e.pLev k o.1 = 0 := by simp [hk, positiveValue]
    simp only [psiFullJ, contFullJ, RpCont, if_pos hk, if_neg hk1, hz,
      zero_mul, sub_zero, div_eq_mul_inv]
    ring
  · simp only [psiFullJ, contFullJ, RpCont, if_neg hk, if_neg hk1, div_eq_mul_inv]
    ring

-- @node: psiFullJ_regression_path
/-- For [a lower full-interval regression direction indexed by positive levels below the last baseline level](hyp:dm), [affinely perturbing the upper and lower full-interval outcome regressions changes
the continuous full-interval score by the perturbation size times the difference between
the next-level propensity times the upper regression direction times one minus the
inverse instrument-group probability weight and the corresponding current-level term
with the lower regression direction; the current-level term is zero in bin zero and
directions outside their index ranges contribute zero](goal). -/
lemma psiFullJ_regression_path (L : LevelData Z X) (e : NuisanceCont L)
    (dp : Fin L.K → X → ℝ) (dm : {k : ℕ // 1 ≤ k ∧ k < L.K} → X → ℝ)
    (k : ℕ) (o : Obs X Z) (t : ℝ) :
    psiFullJ L {e with
      JfullPlus := fun k x => e.JfullPlus k x + t * dp k x
      JfullMinus := fun k x => e.JfullMinus k x + t * dm k x} k o =
    psiFullJ L e k o + t *
      (positiveValue e.pLev (k+1) o.1 * fullValue dp k o.1 *
        (1 - indicator (o.2.1 ∈ L.S (k+1)) / positiveValue e.piLev (k+1) o.1) -
      (if k = 0 then 0 else positiveValue e.pLev k o.1 *
        (if h : 1 ≤ k ∧ k < L.K then dm ⟨k,h⟩ o.1 else 0) *
        (1 - indicator (o.2.1 ∈ L.S k) / positiveValue e.piLev k o.1))) := by
  rw [psiFullJ_regression_decomposition, psiFullJ_regression_decomposition]
  simp only [fullValue, minusFullValue]
  split_ifs <;> ring

-- @node: continuous_full_product_weight_orthogonality
/-- Suppose [the conditioning information is contained in the observation information](hyp:hm),
[the chosen bin's full-interval weight direction is measurable with respect to that
information](hyp:hd), [the continuous full-interval score is integrable](hyp:hs),
[its nuisance regression is integrable](hyp:hj), [that regression is measurable with
respect to the conditioning information](hyp:hjm), [the conditional expectation of the
score equals that regression almost surely](hyp:hcond), [the full-interval product score
is integrable](hyp:hbase), and [the weight direction times the score-minus-regression
residual is integrable](hyp:hres). Then [the population continuous full-interval
product-score moment has derivative zero at zero when its weight alone is perturbed
affinely in that direction](goal). -/
lemma continuous_full_product_weight_orthogonality (L : LevelData Z X)
    (e : NuisanceCont L) (d : Fin L.K → X → ℝ) (k : Fin L.K)
    (m : MeasurableSpace (Obs X Z)) (hm : m ≤ Prod.instMeasurableSpace)
    [SigmaFinite ((observationLaw M).trim hm)]
    (hd : StronglyMeasurable[m] (fun o : Obs X Z => d k o.1))
    (hs : Integrable (fun o => psiFullJ L e k o) (observationLaw M))
    (hj : Integrable (fun o : Obs X Z => contFullJ L e k o.1) (observationLaw M))
    (hjm : StronglyMeasurable[m] (fun o : Obs X Z => contFullJ L e k o.1))
    (hcond : (observationLaw M)[(fun o => psiFullJ L e k o) | m] =ᵐ[observationLaw M]
      (fun o => contFullJ L e k o.1))
    (hbase : Integrable (fun o => psiFullProd L e k o) (observationLaw M))
    (hres : Integrable (fun o => d k o.1 *
      (psiFullJ L e k o - contFullJ L e k o.1)) (observationLaw M)) :
    HasDerivAt (fun t : ℝ => ∫ o, psiFullProd L
      {e with gammaFull := fun k x => e.gammaFull k x + t * d k x} k o
      ∂observationLaw M) 0 0 := by
  let : MeasurableSpace (Obs X Z) := Prod.instMeasurableSpace
  have hz := score_weighted_conditional_residual_zero (observationLaw M) m hm
    (fun o => d k o.1) (fun o => psiFullJ L e k o)
    (fun o => contFullJ L e k o.1) hd hs hj hres hcond hjm
  have hp := product_score_weight_path (observationLaw M)
    (fun o => e.gammaFull k o.1) (fun o => d k o.1)
    (fun o => psiFullJ L e k o) (fun o => contFullJ L e k o.1)
    (fun o => indicator (o.2.1 ∈ higherPolicy L k) -
      indicator (o.2.1 ∈ higherBaseline L k))
    (by simpa only [psiFullProd, fullValue, dif_pos k.isLt] using hbase) hres hz
  have heq : (fun t : ℝ => ∫ o, psiFullProd L
      {e with gammaFull := fun k x => e.gammaFull k x + t * d k x} k o
      ∂observationLaw M) =
      (fun _ : ℝ => ∫ o, psiFullProd L e k o ∂observationLaw M) := by
    funext t
    have hscore : ∀ o, psiFullJ L
        {e with gammaFull := fun k x => e.gammaFull k x + t * d k x} k o =
        psiFullJ L e k o := fun _ => rfl
    have hplug : ∀ x, contFullJ L
        {e with gammaFull := fun k x => e.gammaFull k x + t * d k x} k x =
        contFullJ L e k x := fun _ => rfl
    simpa only [psiFullProd, hscore, hplug, fullValue, dif_pos k.isLt] using hp t
  rw [heq]
  exact hasDerivAt_const 0 _

-- @node: binary_full_product_weight_orthogonality
/-- Suppose [the conditioning information is contained in the observation information](hyp:hm),
[the chosen bin's full-interval weight direction is measurable with respect to that
information](hyp:hd), [the binary full-interval regression plus the next-level treatment
correction minus the current-level correction is integrable](hyp:hs),
[the regression itself is integrable](hyp:hj), [it is measurable with respect to the
conditioning information](hyp:hjm), [the conditional expectation of that corrected score
equals the regression almost surely](hyp:hcond), [the binary full-interval product score
is integrable](hyp:hbase), and [the weight direction times the difference of the two
treatment corrections is integrable](hyp:hres). Then [the population binary full-interval
product-score moment has derivative zero at zero when its weight alone is perturbed
affinely in that direction](goal). -/
lemma binary_full_product_weight_orthogonality (L : LevelData Z X)
    (e : NuisanceBin L) (d : Fin L.K → X → ℝ) (k : Fin L.K)
    (m : MeasurableSpace (Obs X Z)) (hm : m ≤ Prod.instMeasurableSpace)
    [SigmaFinite ((observationLaw M).trim hm)]
    (hd : StronglyMeasurable[m] (fun o : Obs X Z => d k o.1))
    (hs : Integrable (fun o => binFullJ L e k o.1 + RP L e (k+1) o - RP L e k o)
      (observationLaw M))
    (hj : Integrable (fun o : Obs X Z => binFullJ L e k o.1) (observationLaw M))
    (hjm : StronglyMeasurable[m] (fun o : Obs X Z => binFullJ L e k o.1))
    (hcond : (observationLaw M)[(fun o => binFullJ L e k o.1 + RP L e (k+1) o -
      RP L e k o) | m] =ᵐ[observationLaw M] (fun o => binFullJ L e k o.1))
    (hbase : Integrable (fun o => psiFullProdBin L e k o) (observationLaw M))
    (hres : Integrable (fun o => d k o.1 *
      (RP L e (k+1) o - RP L e k o)) (observationLaw M)) :
    HasDerivAt (fun t : ℝ => ∫ o, psiFullProdBin L
      {e with gammaFull := fun k x => e.gammaFull k x + t * d k x} k o
      ∂observationLaw M) 0 0 := by
  let : MeasurableSpace (Obs X Z) := Prod.instMeasurableSpace
  have hid : ∀ o, (binFullJ L e k o.1 + RP L e (k+1) o - RP L e k o) -
      binFullJ L e k o.1 = RP L e (k+1) o - RP L e k o := by
    intro o
    ring
  have hz := score_weighted_conditional_residual_zero (observationLaw M) m hm
    (fun o => d k o.1)
    (fun o => binFullJ L e k o.1 + RP L e (k+1) o - RP L e k o)
    (fun o => binFullJ L e k o.1) hd hs hj
    (by simpa only [hid] using hres) hcond hjm
  have hp := product_score_weight_path (observationLaw M)
    (fun o => e.gammaFull k o.1) (fun o => d k o.1)
    (fun o => binFullJ L e k o.1 + RP L e (k+1) o - RP L e k o)
    (fun o => binFullJ L e k o.1)
    (fun o => indicator (o.2.1 ∈ higherPolicy L k) -
      indicator (o.2.1 ∈ higherBaseline L k))
    (by simpa only [psiFullProdBin, fullValue, dif_pos k.isLt] using hbase)
    (by simpa only [hid] using hres) hz
  have heq : (fun t : ℝ => ∫ o, psiFullProdBin L
      {e with gammaFull := fun k x => e.gammaFull k x + t * d k x} k o
      ∂observationLaw M) =
      (fun _ : ℝ => ∫ o, psiFullProdBin L e k o ∂observationLaw M) := by
    funext t
    have hP : ∀ i o, RP L
        {e with gammaFull := fun k x => e.gammaFull k x + t * d k x} i o =
        RP L e i o := fun _ _ => rfl
    have hJ : ∀ x, binFullJ L
        {e with gammaFull := fun k x => e.gammaFull k x + t * d k x} k x =
        binFullJ L e k x := fun _ => rfl
    simpa only [psiFullProdBin, hP, hJ, fullValue, dif_pos k.isLt] using hp t
  rw [heq]
  exact hasDerivAt_const 0 _

-- @node: populationVariance_nonneg
/-- [The population integral of a score's squared deviation from any centering value
is nonnegative](goal). -/
lemma populationVariance_nonneg (score : Obs X Z → ℝ) (theta : ℝ) :
    0 ≤ populationVariance M score theta := by
  exact integral_nonneg fun o => sq_nonneg (score o - theta)
  -- @realizes \sigma^2(nonnegative population score variance)

end Papers.TbsPrteOptimalTransport
