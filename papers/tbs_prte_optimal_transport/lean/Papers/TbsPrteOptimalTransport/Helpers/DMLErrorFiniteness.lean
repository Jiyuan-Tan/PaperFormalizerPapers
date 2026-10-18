module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLBinaryRearrangementAdmissibility
/-! Population error magnitudes and their finiteness on admissible nuisances. -/
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
open scoped Classical Topology ENNReal
universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
variable {μ : Measure A} {B : Type*}
variable (M : LatentIVModel Ω X Z)
variable [Fintype Z] [DecidableEq Z]
/-- For [a finite list of nonnegative, possibly infinite errors](hyp:errors), the [maximum error](goal) is their maximum, with zero for an empty list. -/
def maxExtendedErrors (errors : List ℝ≥0∞) : ℝ≥0∞ := errors.foldr max 0

/-- For [the latent instrument model](hyp:M), [a policy transformation](hyp:phi), [a level structure](hyp:L), [fitted continuous-outcome nuisances](hyp:e), and [reference nuisances](hyp:truth), the [regression comparison list](goal) first [chooses an arbitrary instrument value for coordinates that do not depend on it](step:1), then [pairs the fitted and reference propensities, positive-level probabilities, pooled policy probabilities, and included regression components](step:2). -/
noncomputable def regressionErrorPairs (phi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e truth : NuisanceCont L) : List ((X → ℝ) × (X → ℝ)) :=
  let z0 : Z := Classical.choice inferInstance
  (
    (Finset.univ.toList.map fun z => (e.prop z, truth.prop z)) ++
    ((List.range L.K).map fun k =>
      (positiveValue e.pLev (k+1), positiveValue truth.pLev (k+1))) ++
    ((policyErrorIndices L).map fun kj =>
      (pooledQ phi L e kj.1 kj.2, pooledQ phi L truth kj.1 kj.2)) ++
    ((List.range L.K).flatMap fun k =>
      ((List.range (L.l k)).map fun j =>
        (nuValue M e k (j+1), nuValue M truth k (j+1))) ++
      ((List.range (L.l k+1)).flatMap fun j =>
        [9,10,11,12].map fun c =>
          (contComponent M L e (c,k,j,z0), contComponent M L truth (c,k,j,z0))) ++
      ([13,14].map fun c =>
        (contComponent M L e (c,k,0,z0), contComponent M L truth (c,k,0,z0)))))

/-- For [the latent instrument model](hyp:M), [a level structure](hyp:L), [fitted continuous- or binary-outcome nuisances](hyp:e), and [reference nuisances of the same kind](hyp:truth), the [weight comparison list](goal) pairs their weight components at every included weight coordinate. -/
noncomputable def weightErrorPairs (L : LevelData Z X)
    (e truth : NuisanceCont L ⊕ NuisanceBin L) : List ((X → ℝ) × (X → ℝ)) :=
  ((weightErrorIndices L).map fun c =>
    (weightComponent M L e c, weightComponent M L truth c))

/-- For [a policy transformation](hyp:phi), [a level structure](hyp:L), [fitted binary-outcome nuisances](hyp:fit), and [reference binary nuisances](hyp:truth), the [binary core comparison list](goal) first [clips and rearranges the fitted success probabilities](step:1), then [pairs the resulting and reference propensities, level and success probabilities, and pooled policy probabilities](step:2). -/
noncomputable def binaryCoreErrorPairs (phi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (fit truth : NuisanceBin L) : List ((X → ℝ) × (X → ℝ)) :=
  let e := rearrangeP1 L fit
  (
    (Finset.univ.toList.map fun z => (e.prop z, truth.prop z)) ++
    ((List.range (L.K+1)).flatMap fun k =>
      [(positiveValue e.pLev k, positiveValue truth.pLev k),
       (positiveValue e.P1 k, positiveValue truth.P1 k)]) ++
    ((policyErrorIndices L).map fun kj =>
      (pooledQBin phi L e kj.1 kj.2, pooledQBin phi L truth kj.1 kj.2)))

/-- For [the latent instrument model](hyp:M), [a policy transformation](hyp:phi), [a level structure](hyp:L), and [continuous-outcome nuisance estimates](hyp:e), [finite regression errors](goal) means that every included fitted-minus-population regression coordinate is square integrable under the covariate distribution. -/
def RegressionErrorsFinite (phi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e : NuisanceCont L) : Prop :=
  ∀ fg ∈ regressionErrorPairs M phi L e (trueNuisance M L),
    MemLp (fun x => fg.1 x - fg.2 x) 2 (xLaw M)
  -- @realizes r_{\mathrm{reg},n}(admissible domain: every included error is square integrable)

/-- For [the latent instrument model](hyp:M), [a level structure](hyp:L), and [continuous- or binary-outcome nuisance estimates](hyp:e), [finite weight errors](goal) means [selecting the corresponding continuous or binary population nuisances](step:1) and [requiring every included fitted-minus-population weight coordinate to be square integrable under the covariate distribution](step:2). -/
def WeightErrorsFinite (L : LevelData Z X) (e : NuisanceCont L ⊕ NuisanceBin L) : Prop :=
  let truth := match e with
    | .inl _ => Sum.inl (trueNuisance M L)
    | .inr _ => Sum.inr (eta0Bin M L)
  ∀ fg ∈ weightErrorPairs M L e truth, MemLp (fun x => fg.1 x - fg.2 x) 2 (xLaw M)
  -- @realizes r_{\mathrm{wt},n}(admissible domain: every included error is square integrable)

/-- For [the latent instrument model](hyp:M), [a policy transformation](hyp:phi), [a level structure](hyp:L), and [binary-outcome nuisance estimates](hyp:e), [finite binary core errors](goal) means that every included core coordinate, after clipping and rearranging the fitted success probabilities, has a square-integrable error relative to the population nuisances. -/
def BinaryCoreErrorsFinite (phi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (e : NuisanceBin L) : Prop :=
  ∀ fg ∈ binaryCoreErrorPairs phi L e (eta0Bin M L),
    MemLp (fun x => fg.1 x - fg.2 x) 2 (xLaw M)
  -- @realizes r_{\mathrm{core},n}(admissible domain: every included error is square integrable)

/-- For [the latent instrument model](hyp:M), [a policy transformation](hyp:phi), [a level structure](hyp:L), [a sequence of continuous-outcome nuisance estimators](hyp:fit), [a sample-size index](hyp:n), and [a sample realization](hyp:a), the [extended regression error magnitude](goal) is the maximum population root mean squared error over the included regression coordinates, allowing infinity. -/
noncomputable def extendedRegressionErrorMagnitude (phi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (fit : ℕ → A → NuisanceCont L) (n : ℕ) (a : A) : ℝ≥0∞ :=
  maxExtendedErrors ((regressionErrorPairs M phi L (fit n a) (trueNuisance M L)).map
    fun fg => l2Error M fg.1 fg.2)

/-- For [the latent instrument model](hyp:M), [a level structure](hyp:L), [a sequence of continuous- or binary-outcome nuisance estimators](hyp:fit), [a sample-size index](hyp:n), and [a sample realization](hyp:a), the [extended weight error magnitude](goal) is obtained by [evaluating the fitted nuisances](step:1), [selecting the population nuisances of the same outcome type](step:2), and [taking the maximum population root mean squared error over the included weight coordinates, allowing infinity](step:3). -/
noncomputable def extendedWeightErrorMagnitude (L : LevelData Z X)
    (fit : ℕ → A → NuisanceCont L ⊕ NuisanceBin L) (n : ℕ) (a : A) : ℝ≥0∞ :=
  let e := fit n a
  let truth := match e with
    | .inl _ => Sum.inl (trueNuisance M L)
    | .inr _ => Sum.inr (eta0Bin M L)
  maxExtendedErrors ((weightErrorPairs M L e truth).map fun fg => l2Error M fg.1 fg.2)

/-- For [the latent instrument model](hyp:M), [a policy transformation](hyp:phi), [a level structure](hyp:L), [a sequence of binary-outcome nuisance estimators](hyp:fit), [a sample-size index](hyp:n), and [a sample realization](hyp:a), the [extended binary core error magnitude](goal) is the maximum population root mean squared error over the included core coordinates after clipping and rearranging fitted success probabilities, allowing infinity. -/
noncomputable def extendedBinaryCoreErrorMagnitude (phi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (fit : ℕ → A → NuisanceBin L) (n : ℕ) (a : A) : ℝ≥0∞ :=
  maxExtendedErrors ((binaryCoreErrorPairs phi L (fit n a) (eta0Bin M L)).map
    fun fg => l2Error M fg.1 fg.2)

-- @node: maxExtendedErrors_lt_top
/-- For [a finite list of nonnegative, possibly infinite errors](hyp:errors), if [every error in the list is finite](hyp:h), then [their maximum, with zero for an empty list, is finite](goal). -/
lemma maxExtendedErrors_lt_top (errors : List ℝ≥0∞)
    (h : ∀ r ∈ errors, r < ⊤) : maxExtendedErrors errors < ⊤ := by
  induction errors with
  | nil => exact ENNReal.zero_lt_top
  | cons r errors ih =>
    change max r (maxExtendedErrors errors) < ⊤
    exact max_lt_iff.mpr ⟨h r (List.mem_cons_self ..),
      ih (fun t ht => h t (List.mem_cons_of_mem r ht))⟩

-- @node: maxExtendedL2Errors_lt_top
/-- If [the difference in every listed pair of covariate functions is square integrable under the population covariate distribution](hyp:h), then [the maximum of their population root mean squared errors is finite](goal). -/
lemma maxExtendedL2Errors_lt_top (pairs : List ((X → ℝ) × (X → ℝ)))
    (h : ∀ fg ∈ pairs, MemLp (fun x => fg.1 x - fg.2 x) 2 (xLaw M)) :
    maxExtendedErrors (pairs.map fun fg => l2Error M fg.1 fg.2) < ⊤ := by
  apply maxExtendedErrors_lt_top
  intro r hr
  obtain ⟨fg, hfg, rfl⟩ := List.mem_map.mp hr
  exact (h fg hfg).eLpNorm_lt_top

-- @node: regressionErrorMagnitude_lt_top
/-- If [all included regression errors of the fitted continuous-outcome nuisances are square integrable](hyp:h), then [their extended maximum root mean squared error is finite](goal). -/
lemma regressionErrorMagnitude_lt_top (phi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (fit : ℕ → A → NuisanceCont L) (n : ℕ) (a : A)
    (h : RegressionErrorsFinite M phi L (fit n a)) :
    extendedRegressionErrorMagnitude M phi L fit n a < ⊤ := by
  exact maxExtendedL2Errors_lt_top M _ h

-- @node: weightErrorMagnitude_lt_top
/-- If [all included weight errors of the fitted nuisances are square integrable](hyp:h), then [their extended maximum root mean squared error is finite](goal). -/
lemma weightErrorMagnitude_lt_top (L : LevelData Z X)
    (fit : ℕ → A → NuisanceCont L ⊕ NuisanceBin L) (n : ℕ) (a : A)
    (h : WeightErrorsFinite M L (fit n a)) :
    extendedWeightErrorMagnitude M L fit n a < ⊤ := by
  exact maxExtendedL2Errors_lt_top M _ h

-- @node: binaryCoreErrorMagnitude_lt_top
/-- If [all included binary core errors after clipping and rearrangement are square integrable](hyp:h), then [their extended maximum root mean squared error is finite](goal). -/
lemma binaryCoreErrorMagnitude_lt_top (phi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (fit : ℕ → A → NuisanceBin L) (n : ℕ) (a : A)
    (h : BinaryCoreErrorsFinite M phi L (fit n a)) :
    extendedBinaryCoreErrorMagnitude M phi L fit n a < ⊤ := by
  exact maxExtendedL2Errors_lt_top M _ h

/-- For [the latent instrument model](hyp:M), [a policy transformation](hyp:phi), [a level structure](hyp:L), [a sequence of continuous-outcome nuisance estimators](hyp:fit), [a sample-size index](hyp:n), and [a sample realization](hyp:a), under [square integrability of all included regression errors](hyp:h), the [finite regression error magnitude](goal) is their maximum population root mean squared error together with its guarantee of finiteness. -/
noncomputable def regressionErrorMagnitude (phi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (fit : ℕ → A → NuisanceCont L) (n : ℕ) (a : A)
    (h : RegressionErrorsFinite M phi L (fit n a)) : {r : ℝ≥0∞ // r < ⊤} :=
  ⟨extendedRegressionErrorMagnitude M phi L fit n a,
    regressionErrorMagnitude_lt_top M phi L fit n a h⟩
  -- @realizes r_{\mathrm{reg},n}(finite maximum of all specified population regression L2 errors)

/-- For [the latent instrument model](hyp:M), [a level structure](hyp:L), [a sequence of continuous- or binary-outcome nuisance estimators](hyp:fit), [a sample-size index](hyp:n), and [a sample realization](hyp:a), under [square integrability of all included weight errors](hyp:h), the [finite weight error magnitude](goal) is their maximum population root mean squared error together with its guarantee of finiteness. -/
noncomputable def weightErrorMagnitude (L : LevelData Z X)
    (fit : ℕ → A → NuisanceCont L ⊕ NuisanceBin L) (n : ℕ) (a : A)
    (h : WeightErrorsFinite M L (fit n a)) : {r : ℝ≥0∞ // r < ⊤} :=
  ⟨extendedWeightErrorMagnitude M L fit n a, weightErrorMagnitude_lt_top M L fit n a h⟩
  -- @realizes r_{\mathrm{wt},n}(finite maximum of all specified population weight L2 errors)

/-- For [the latent instrument model](hyp:M), [a policy transformation](hyp:phi), [a level structure](hyp:L), [a sequence of binary-outcome nuisance estimators](hyp:fit), [a sample-size index](hyp:n), and [a sample realization](hyp:a), under [square integrability of all included binary core errors](hyp:h), the [finite binary core error magnitude](goal) is their maximum population root mean squared error after clipping and rearrangement, together with its guarantee of finiteness. -/
noncomputable def binaryCoreErrorMagnitude (phi : Z → X → ℝ → ℝ) (L : LevelData Z X)
    (fit : ℕ → A → NuisanceBin L) (n : ℕ) (a : A)
    (h : BinaryCoreErrorsFinite M phi L (fit n a)) : {r : ℝ≥0∞ // r < ⊤} :=
  ⟨extendedBinaryCoreErrorMagnitude M phi L fit n a,
    binaryCoreErrorMagnitude_lt_top M phi L fit n a h⟩
  -- @realizes r_{\mathrm{core},n}(finite maximum including clipped and rearranged P1 errors)

-- @node: admissible_interval_memLp
/-- If [a covariate function is measurable](hyp:hf) and [lies almost surely between two fixed finite real bounds](hyp:hr), then [it is square integrable under the population covariate distribution](goal). -/
lemma admissible_interval_memLp (f : X → ℝ) (a b : ℝ) (hf : Measurable f)
    (hr : ∀ᵐ x ∂xLaw M, f x ∈ Icc a b) : MemLp f 2 (xLaw M) := by
  have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  apply MemLp.of_bound hf.aestronglyMeasurable (max |a| |b|)
  filter_upwards [hr] with x hx
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · exact (neg_le_neg (le_max_left |a| |b|)).trans ((neg_abs_le a).trans hx.1)
  · exact hx.2.trans ((le_abs_self b).trans (le_max_right _ _))

-- @node: admissible_weightComponent_memLp
/-- If [the continuous- or binary-outcome nuisance record is admissible](hyp:he) and [the selected coordinate has weight code 2, 3, 4, 5, 6, or 7](hyp:hc), then [its weight component is square integrable under the population covariate distribution](goal). -/
lemma admissible_weightComponent_memLp (L : LevelData Z X)
    (e : NuisanceCont L ⊕ NuisanceBin L)
    (he : match e with | .inl e => ContAdmissible M L e | .inr e => BinAdmissible M L e)
    (c : ℕ × ℕ × ℕ × Z) (hc : c.1 ∈ [2,3,4,5,6,7]) :
    MemLp (weightComponent M L e c) 2 (xLaw M) := by
  have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  change MemLp (fun x => weightComponent M L e c x) 2 (xLaw M)
  rcases c with ⟨code,k,j,z⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  cases e with
  | inl e =>
    rcases he with ⟨hp, hmp, hpl, hmpl, hpi, hmpi, ht, hmt, hs, hms,
      hgf, hmgf, hg, hmg, htail, hmtail, hrest⟩
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [weightComponent, contComponent, positiveValue, regularValue, shareValue, fullValue]
      (try split_ifs) <;> first
        | exact memLp_const _
        | exact admissible_interval_memLp M _ _ _ (hmpi _) (hpi _)
        | exact admissible_interval_memLp M _ _ _ (hmt _) (ht _)
        | exact admissible_interval_memLp M _ _ _ (hms _ _) (hs _ _)
        | exact admissible_interval_memLp M _ _ _ (hmgf _) (hgf _)
        | exact admissible_interval_memLp M _ _ _ (hmg _) (hg _)
        | exact admissible_interval_memLp M _ _ _ hmtail htail
  | inr e =>
    rcases he with ⟨hp, hmp, hlev, hmlev, ht, hmt, hs, hms,
      hsum, hgf, hmgf, htail, hmtail⟩
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [weightComponent, binComponent, positiveValue, regularValue, fullValue]
      (try split_ifs) <;> first
        | exact memLp_const _
        | exact admissible_interval_memLp M _ _ _ (hmlev _).2.2
            ((hlev _).mono (fun _ h => h.2.2))
        | exact admissible_interval_memLp M _ _ _ (hmt _).1
            ((ht _).mono (fun _ h => h.1))
        | exact admissible_interval_memLp M _ _ _ (hmt _).2
            ((ht _).mono (fun _ h => h.2))
        | exact admissible_interval_memLp M _ _ _ (hms _ _) (hs _ _)
        | exact admissible_interval_memLp M _ _ _ (hmgf _) (hgf _)
        | exact admissible_interval_memLp M _ _ _ hmtail htail

-- @node: admissible_policy_share_memLp
/-- If [the policy transformation is measurable and preserves the unit interval](hyp:hphi), [the propensity function is measurable](hyp:hp), [the share function is measurable](hyp:ha), [the propensity lies in the unit interval almost surely](hyp:hrp), and [the share lies in the unit interval almost surely](hyp:hra), then [the share times the policy-transformed propensity at the chosen instrument value is square integrable under the covariate distribution](goal). -/
lemma admissible_policy_share_memLp (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (z : Z) (p a : X → ℝ) (hp : Measurable p) (ha : Measurable a)
    (hrp : ∀ᵐ x ∂xLaw M, p x ∈ Icc (0 : ℝ) 1)
    (hra : ∀ᵐ x ∂xLaw M, a x ∈ Icc (0 : ℝ) 1) :
    MemLp (fun x => a x * phi z x (p x)) 2 (xLaw M) := by
  let pc := fun x => max 0 (min 1 (p x))
  have hm : Measurable pc := by fun_prop
  have hr : ∀ x, pc x ∈ Icc (0 : ℝ) 1 := fun x =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hq : Measurable (fun x => phi z x (pc x)) := by
    first | fun_prop | exact hphi.1.comp (measurable_const.prodMk
      (measurable_id.prodMk (hm.subtype_mk (h := hr))))
  have hv : MemLp (fun x => a x * phi z x (pc x)) 2 (xLaw M) := by
    apply admissible_interval_memLp M _ 0 1 (by first | fun_prop | exact ha.mul hq)
    filter_upwards [hra] with x hx
    exact ⟨mul_nonneg hx.1 (hphi.2 z x _ (hr x)).1,
      mul_le_one₀ hx.2 (hphi.2 z x _ (hr x)).1 (hphi.2 z x _ (hr x)).2⟩
  apply hv.ae_eq
  filter_upwards [hrp] with x hx
  simp only [pc, min_eq_right hx.2, max_eq_right hx.1]

-- @node: admissible_cont_pooledQ_memLp
/-- If [the policy transformation is measurable and preserves the unit interval](hyp:hphi) and [the continuous-outcome nuisance record is admissible](hyp:he), then [its pooled policy probability at any level and component index is square integrable under the covariate distribution](goal). -/
lemma admissible_cont_pooledQ_memLp (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e)
    (k j : ℕ) : MemLp (pooledQ phi L e k j) 2 (xLaw M) := by
  have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  rcases he with ⟨hp, hmp, hl, hml, hpi, hmpi, ht, hmt, hs, hms, hrest⟩
  unfold pooledQ
  split_ifs with hj0 hj
  · unfold positiveValue
    split_ifs <;> first | exact memLp_const _ |
      exact admissible_interval_memLp M _ _ _ (hml _) (hl _)
  · unfold positiveValue
    split_ifs <;> first | exact memLp_const _ |
      exact admissible_interval_memLp M _ _ _ (hml _) (hl _)
  · apply memLp_finsetSum
    intro z hz
    unfold shareValue
    split_ifs
    · exact admissible_policy_share_memLp M phi hphi z _ _ (hmp z) (hms _ z) (hp z) (hs _ z)
    · simpa using (memLp_const (0 : ℝ) : MemLp (fun _ : X => (0 : ℝ)) 2 (xLaw M))

-- @node: admissible_cont_regressionComponent_memLp
/-- If [the continuous-outcome nuisance record is admissible](hyp:he) and [the selected coordinate has regression code 0, 1, 8, 9, 10, 11, 12, 13, or 14](hyp:hc), then [its regression component is square integrable under the covariate distribution](goal). -/
lemma admissible_cont_regressionComponent_memLp (L : LevelData Z X)
    (e : NuisanceCont L) (he : ContAdmissible M L e)
    (c : ℕ × ℕ × ℕ × Z) (hc : c.1 ∈ [0,1,8,9,10,11,12,13,14]) :
    MemLp (contComponent M L e c) 2 (xLaw M) := by
  have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  rcases he with ⟨hp, hmp, hl, hml, hpi, hmpi, ht, hmt, hs, hms,
    hgf, hmgf, hg, hmg, htail, hmtail, hn, hmn, hmpR, hmmp, hmmR, hmmm,
    hjp, hmjp, hjm, hmjm, hjfp, hmjfp, hjfm, hmjfm, hrest⟩
  change MemLp (fun x => contComponent M L e c x) 2 (xLaw M)
  rcases c with ⟨code,k,j,z⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [contComponent, positiveValue, nuValue, boundaryValue, minusBoundaryValue,
      meanValue, minusMeanValue, fullValue, minusFullValue]
    (try split_ifs) <;> first
      | exact memLp_const _
      | exact admissible_interval_memLp M _ _ _ (hmp _) (hp _)
      | exact admissible_interval_memLp M _ _ _ (hml _) (hl _)
      | exact admissible_interval_memLp M _ _ _ (hmn _) (hn _)
      | exact admissible_interval_memLp M _ _ _ (hmmp _) (hmpR _)
      | exact admissible_interval_memLp M _ _ _ (hmmm _) (hmmR _)
      | exact admissible_interval_memLp M _ _ _ (hmjp _) (hjp _)
      | exact admissible_interval_memLp M _ _ _ (hmjm _) (hjm _)
      | exact admissible_interval_memLp M _ _ _ (hmjfp _) (hjfp _)
      | exact admissible_interval_memLp M _ _ _ (hmjfm _) (hjfm _)

/-- If [the policy transformation is measurable and preserves the unit interval](hyp:hphi), [the fitted continuous-outcome nuisances are admissible](hyp:he), and [the population continuous-outcome nuisances are admissible](hyp:ht), then [all included regression errors are square integrable under the population covariate distribution](goal). -/
-- @node: regressionErrorsFinite_of_admissible
lemma regressionErrorsFinite_of_admissible (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e : NuisanceCont L) (he : ContAdmissible M L e)
    (ht : ContAdmissible M L (trueNuisance M L)) : RegressionErrorsFinite M phi L e := by
  intro fg hfg
  simp only [regressionErrorPairs, List.mem_append, List.mem_map, List.mem_flatMap] at hfg
  rcases hfg with ((h | h) | h) | h
  · obtain ⟨z, hz, rfl⟩ := h
    exact (admissible_cont_regressionComponent_memLp M L e he (0,0,0,z) (by simp)).sub
      (admissible_cont_regressionComponent_memLp M L _ ht (0,0,0,z) (by simp))
  · obtain ⟨k, hk, rfl⟩ := h
    exact (admissible_cont_regressionComponent_memLp M L e he (1,k+1,0,Classical.choice inferInstance)
      (by simp)).sub (admissible_cont_regressionComponent_memLp M L _ ht
        (1,k+1,0,Classical.choice inferInstance) (by simp))
  · obtain ⟨kj, hkj, rfl⟩ := h
    exact (admissible_cont_pooledQ_memLp M phi hphi L e he _ _).sub
      (admissible_cont_pooledQ_memLp M phi hphi L _ ht _ _)
  · obtain ⟨k, hk, h⟩ := h
    rcases h with (h | h) | h
    · obtain ⟨j, hj, rfl⟩ := h
      exact (admissible_cont_regressionComponent_memLp M L e he
        (8,k,j+1,Classical.choice inferInstance) (by simp)).sub
        (admissible_cont_regressionComponent_memLp M L _ ht
          (8,k,j+1,Classical.choice inferInstance) (by simp))
    · obtain ⟨j, hj, c, hc, rfl⟩ := h
      have hc' : c ∈ [0,1,8,9,10,11,12,13,14] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
        rcases hc with rfl | rfl | rfl | rfl <;> simp
      exact (admissible_cont_regressionComponent_memLp M L e he _ hc').sub
        (admissible_cont_regressionComponent_memLp M L _ ht _ hc')
    · obtain ⟨c, hc, rfl⟩ := h
      have hc' : c ∈ [0,1,8,9,10,11,12,13,14] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
        rcases hc with rfl | rfl <;> simp
      exact (admissible_cont_regressionComponent_memLp M L e he _ hc').sub
        (admissible_cont_regressionComponent_memLp M L _ ht _ hc')

-- @node: weightErrorsFinite_of_admissible
/-- If [the fitted nuisances are admissible for their continuous or binary outcome type](hyp:he) and [the corresponding population nuisances are admissible](hyp:ht), then [all included weight errors are square integrable under the population covariate distribution](goal). -/
lemma weightErrorsFinite_of_admissible (L : LevelData Z X)
    (e : NuisanceCont L ⊕ NuisanceBin L)
    (he : match e with | .inl e => ContAdmissible M L e | .inr e => BinAdmissible M L e)
    (ht : match e with
      | .inl _ => ContAdmissible M L (trueNuisance M L)
      | .inr _ => BinAdmissible M L (eta0Bin M L)) : WeightErrorsFinite M L e := by
  intro fg hfg
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hfg
  have hcode : c.1 ∈ [2,3,4,5,6,7] := by
    simp only [weightErrorIndices, List.mem_append, List.mem_map, List.mem_flatMap,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with ((h | h) | h) | h
    · obtain ⟨k, hk, rfl⟩ := h
      simp
    · obtain ⟨kj, hkj, hc⟩ := h
      rcases hc with h | h
      · rcases h with rfl | rfl <;> simp
      · obtain ⟨z, hz, rfl⟩ := h
        simp
    · obtain ⟨k, hk, rfl⟩ := h
      simp
    · subst c
      simp
  have hf := admissible_weightComponent_memLp M L e he c hcode
  cases e with
  | inl e => exact hf.sub (admissible_weightComponent_memLp M L
      (.inl (trueNuisance M L)) ht c hcode)
  | inr e => exact hf.sub (admissible_weightComponent_memLp M L
      (.inr (eta0Bin M L)) ht c hcode)

-- @node: admissible_bin_coreComponent_memLp
/-- If [the binary-outcome nuisance record is admissible](hyp:he) and [the selected coordinate has core code 0, 1, or 2](hyp:hc), then [its binary core component is square integrable under the covariate distribution](goal). -/
lemma admissible_bin_coreComponent_memLp (L : LevelData Z X)
    (e : NuisanceBin L) (he : BinAdmissible M L e)
    (c : ℕ × ℕ × ℕ × Z) (hc : c.1 ∈ [0,1,2]) :
    MemLp (binComponent L e c) 2 (xLaw M) := by
  have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  rcases he with ⟨hp, hmp, hl, hml, hrest⟩
  change MemLp (fun x => binComponent L e c x) 2 (xLaw M)
  rcases c with ⟨code,k,j,z⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  all_goals
    simp only [binComponent, positiveValue]
    (try split_ifs) <;> first
      | exact memLp_const _
      | exact admissible_interval_memLp M _ _ _ (hmp _) (hp _)
      | exact admissible_interval_memLp M _ _ _ (hml _).1
          ((hl _).mono (fun _ h => h.1))
      | exact admissible_interval_memLp M _ _ _ (hml _).2.1
          ((hl _).mono (fun _ h => h.2.1))

-- @node: admissible_bin_pooledQ_memLp
/-- If [the policy transformation is measurable and preserves the unit interval](hyp:hphi) and [the binary-outcome nuisance record is admissible](hyp:he), then [its pooled policy probability at any level and component index is square integrable under the covariate distribution](goal). -/
lemma admissible_bin_pooledQ_memLp (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e)
    (k j : ℕ) : MemLp (pooledQBin phi L e k j) 2 (xLaw M) := by
  have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  rcases he with ⟨hp, hmp, hl, hml, ht, hmt, hs, hms, hrest⟩
  unfold pooledQBin
  split_ifs with hj0 hj hi
  · unfold positiveValue
    split_ifs <;> first | exact memLp_const _ |
      exact admissible_interval_memLp M _ _ _ (hml _).1 ((hl _).mono (fun _ h => h.1))
  · unfold positiveValue
    split_ifs <;> first | exact memLp_const _ |
      exact admissible_interval_memLp M _ _ _ (hml _).1 ((hl _).mono (fun _ h => h.1))
  · apply memLp_finsetSum
    intro z hz
    exact admissible_policy_share_memLp M phi hphi z _ _ (hmp z) (hms _ z) (hp z) (hs _ z)
  · simpa only [zero_mul, Finset.sum_const_zero] using
      (MemLp.zero' : MemLp (fun _ : X => (0 : ℝ)) 2 (xLaw M))

-- @node: binaryCoreErrorsFinite_of_admissible
/-- If [the policy transformation is measurable and preserves the unit interval](hyp:hphi), [the fitted binary nuisances are admissible](hyp:he), and [the population binary nuisances are admissible](hyp:ht), then [all included binary core errors after clipping and rearranging fitted success probabilities are square integrable under the population covariate distribution](goal). -/
lemma binaryCoreErrorsFinite_of_admissible (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e)
    (ht : BinAdmissible M L (eta0Bin M L)) : BinaryCoreErrorsFinite M phi L e := by
  have hr := rearrangeP1_admissible M L e he
  intro fg hfg
  simp only [binaryCoreErrorPairs, List.mem_append, List.mem_map, List.mem_flatMap] at hfg
  rcases hfg with (h | h) | h
  · obtain ⟨z, hz, rfl⟩ := h
    exact (admissible_bin_coreComponent_memLp M L _ hr (0,0,0,z) (by simp)).sub
      (admissible_bin_coreComponent_memLp M L _ ht (0,0,0,z) (by simp))
  · obtain ⟨k, hk, h⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact (admissible_bin_coreComponent_memLp M L _ hr
        (1,k,0,Classical.choice inferInstance) (by simp)).sub
        (admissible_bin_coreComponent_memLp M L _ ht
          (1,k,0,Classical.choice inferInstance) (by simp))
    · exact (admissible_bin_coreComponent_memLp M L _ hr
        (2,k,0,Classical.choice inferInstance) (by simp)).sub
        (admissible_bin_coreComponent_memLp M L _ ht
          (2,k,0,Classical.choice inferInstance) (by simp))
  · obtain ⟨kj, hkj, rfl⟩ := h
    exact (admissible_bin_pooledQ_memLp M phi hphi L _ hr _ _).sub
      (admissible_bin_pooledQ_memLp M phi hphi L _ ht _ _)



end Papers.TbsPrteOptimalTransport
