module
public import Papers.TbsNeuralCausalPi.Setup.CitedResults
public import Papers.TbsNeuralCausalPi.Helpers.EmpiricalCovers
public import Papers.TbsNeuralCausalPi.Helpers.EmpiricalProducts
public import Papers.TbsNeuralCausalPi.Helpers.EmpiricalEntropy
public import Papers.TbsNeuralCausalPi.Setup.Assumptions.Auxiliary
public import Papers.TbsNeuralCausalPi.Helpers.KantorovichCube
public import Papers.TbsNeuralCausalPi.Helpers.EmpiricalSqrt
public import Papers.TbsNeuralCausalPi.Helpers.EmpiricalContrasts
public import Papers.TbsNeuralCausalPi.Helpers.EmpiricalTestNets
public import Papers.TbsNeuralCausalPi.Helpers.EmpiricalNetEntropy
public import Papers.TbsNeuralCausalPi.Setup.Optimization
/-! # Deterministic reduction and entropy for empirical Wasserstein deviation -/
public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
open MeasureTheory
open scoped ENNReal NNReal
noncomputable section

/-- If [K is nonnegative](hyp:hK), [the first probability law assigns full mass
to the cube of coordinate radius K](hyp:hmu), and [the second law does
too](hyp:hnu), then [their Wasserstein distance is at most 2 d K](goal). -/
-- @node: wasserstein1_le_cube_diameter
lemma wasserstein1_le_cube_diameter {d : ℕ} (K : ℝ) (hK : 0 ≤ K)
    (mu nu : ProbabilityMeasure (L1Vec d))
    (hmu : (mu : Measure (L1Vec d)) (boundedCube d K) = 1)
    (hnu : (nu : Measure (L1Vec d)) (boundedCube d K) = 1) :
    wasserstein1 (mu : Measure (L1Vec d)) (nu : Measure (L1Vec d)) ≤ ENNReal.ofReal (2 * d * K) := by
  refine (wasserstein1_le_sup_lipschitz_cube K hK mu nu hmu hnu).trans ?_
  apply iSup_le
  intro h
  have hbound (rho : ProbabilityMeasure (L1Vec d))
      (hrho : (rho : Measure (L1Vec d)) (boundedCube d K) = 1) :
      |∫ x, h.val x ∂(rho : Measure (L1Vec d))| ≤ (d : ℝ) * K := by
    have hae : ∀ᵐ x ∂(rho : Measure (L1Vec d)), x ∈ boundedCube d K :=
      (ae_mem_iff_measure_eq (boundedCube_isCompact d K).measurableSet.nullMeasurableSet).mpr
        (by simpa using hrho)
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := (rho : Measure (L1Vec d)))
        (f := h.val) (C := (d : ℝ) * K) (hae.mono fun x hx =>
        by simpa only [Real.norm_eq_abs] using
          anchored_cube_test_abs_le hK h.property.1 h.property.2 hx))
  apply ENNReal.ofReal_le_ofReal
  have hm := hbound mu hmu
  have hn := hbound nu hnu
  have hm' := (abs_le.mp hm).2
  have hn' := (abs_le.mp hn).1
  linarith

/-- If [the first law assigns full mass to the cube](hyp:hmu), [the second law
assigns full mass to the cube](hyp:hnu), [h is continuous on the cube](hyp:hh), [g is continuous on the
cube](hyp:hg), and [their pointwise absolute difference there is at most
r](hyp:hclose), then [the first-minus-second expectation contrast of h is at
most that of g plus 2 r](goal). -/
-- @node: cube_contrast_le_of_uniform_dist
lemma cube_contrast_le_of_uniform_dist {d : ℕ} {K r : ℝ}
    (mu nu : ProbabilityMeasure (L1Vec d))
    (hmu : (mu : Measure (L1Vec d)) (boundedCube d K) = 1)
    (hnu : (nu : Measure (L1Vec d)) (boundedCube d K) = 1)
    {h g : L1Vec d → ℝ}
    (hh : ContinuousOn h (boundedCube d K))
    (hg : ContinuousOn g (boundedCube d K))
    (hclose : ∀ x ∈ boundedCube d K, |h x - g x| ≤ r) :
    (∫ x, h x ∂(mu : Measure (L1Vec d))) - (∫ x, h x ∂(nu : Measure (L1Vec d))) ≤
      2 * r + ((∫ x, g x ∂(mu : Measure (L1Vec d))) - (∫ x, g x ∂(nu : Measure (L1Vec d)))) := by
  let C := boundedCube d K
  have hC : IsCompact C := boundedCube_isCompact d K
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let m := (mu : Measure (L1Vec d)).comap ((↑) : C → L1Vec d)
  let n := (nu : Measure (L1Vec d)).comap ((↑) : C → L1Vec d)
  let : IsProbabilityMeasure m :=
    (Toolkit.Foundations.MeasureTheory.probability_comap_subtype _ C hC.measurableSet hmu).1
  let : IsProbabilityMeasure n :=
    (Toolkit.Foundations.MeasureTheory.probability_comap_subtype _ C hC.measurableSet hnu).1
  change Toolkit.Foundations.MeasureTheory.lipschitzContrast _ _ h ≤
    2 * r + Toolkit.Foundations.MeasureTheory.lipschitzContrast _ _ g
  rw [Toolkit.Foundations.MeasureTheory.lipschitzContrast_eq_subtype_comap
    _ _ C hC.measurableSet hmu hnu h,
    Toolkit.Foundations.MeasureTheory.lipschitzContrast_eq_subtype_comap
    _ _ C hC.measurableSet hmu hnu g]
  have hhi (rho : Measure C) [IsProbabilityMeasure rho] :
      Integrable (fun x : C => h x.val) rho :=
    hh.domRestrict.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hgi (rho : Measure C) [IsProbabilityMeasure rho] :
      Integrable (fun x : C => g x.val) rho :=
    hg.domRestrict.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hbound (rho : Measure C) [IsProbabilityMeasure rho] :
      |(∫ x : C, h x.val ∂rho) - ∫ x : C, g x.val ∂rho| ≤ r := by
    rw [← integral_sub (hhi rho) (hgi rho)]
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := rho) (f := fun x : C => h x.val - g x.val)
        (Filter.Eventually.of_forall fun x : C => by
          simpa only [Real.norm_eq_abs] using hclose x.val x.property))
  have hm := abs_le.mp (hbound m)
  have hn := abs_le.mp (hbound n)
  change (∫ x : C, h x.val ∂m) - (∫ x : C, h x.val ∂n) ≤
    2 * r + ((∫ x : C, g x.val ∂m) - (∫ x : C, g x.val ∂n))
  linarith [hm.2, hn.1]

/-- Suppose [K is nonnegative](hyp:hK), [the first law assigns full mass to
the cube](hyp:hmu), [the second law does too](hyp:hnu), [all tests in H are
continuous on the cube](hyp:hH), and [delta is nonnegative](hyp:hdelta).
If [H approximates every one-Lipschitz test vanishing at zero uniformly on the
cube within delta/2](hyp:hnet), then [the Wasserstein distance is at most delta
plus the supremum over H of the nonnegative first-minus-second expectation
contrasts](goal). -/
-- @node: wasserstein1_le_cube_test_net
lemma wasserstein1_le_cube_test_net {d : ℕ} (K : ℝ) (hK : 0 ≤ K)
    (mu nu : ProbabilityMeasure (L1Vec d))
    (hmu : (mu : Measure (L1Vec d)) (boundedCube d K) = 1)
    (hnu : (nu : Measure (L1Vec d)) (boundedCube d K) = 1)
    (H : Set (L1Vec d → ℝ))
    (hH : ∀ g ∈ H, ContinuousOn g (boundedCube d K))
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hnet : ∀ h : L1Vec d → ℝ, LipschitzOnWith 1 h (boundedCube d K) → h 0 = 0 →
      ∃ g ∈ H, ∀ x ∈ boundedCube d K, |h x - g x| ≤ delta / 2) :
    wasserstein1 (mu : Measure (L1Vec d)) (nu : Measure (L1Vec d)) ≤
      ENNReal.ofReal delta + ⨆ g : H,
        ENNReal.ofReal ((∫ x, g.val x ∂(mu : Measure (L1Vec d))) - ∫ x, g.val x ∂(nu : Measure (L1Vec d))) := by
  refine (wasserstein1_le_sup_lipschitz_cube K hK mu nu hmu hnu).trans ?_
  apply iSup_le
  intro h
  obtain ⟨g, hg, hclose⟩ := hnet h.val h.property.1 h.property.2
  have hcontrast := cube_contrast_le_of_uniform_dist mu nu hmu hnu
    h.property.1.continuousOn (hH g hg) hclose
  have hle := ENNReal.ofReal_le_ofReal hcontrast
  have hscale : 2 * (delta / 2) = delta := by ring
  rw [hscale] at hle
  refine hle.trans ?_
  calc
    _ ≤ ENNReal.ofReal delta + ENNReal.ofReal
        ((∫ x, g x ∂(mu : Measure (L1Vec d))) - ∫ x, g x ∂(nu : Measure (L1Vec d))) :=
      ENNReal.ofReal_add_le
    _ ≤ _ := add_le_add le_rfl (le_iSup
      (fun g : H => ENNReal.ofReal ((∫ x, g.val x ∂(mu : Measure (L1Vec d))) -
        ∫ x, g.val x ∂(nu : Measure (L1Vec d)))) ⟨g, hg⟩)

/-- If [the sample size is positive](hyp:hn), then [its empirical measure is
a probability measure](goal). -/
-- @node: empiricalMeasure_probability
lemma empiricalMeasure_probability {X : Type*} [MeasurableSpace X]
    {n : ℕ} (hn : 0 < n) (x : Fin n → X) :
    IsProbabilityMeasure (empiricalMeasure x) := by
  constructor
  simp only [empiricalMeasure, Measure.smul_apply, Measure.coe_finsetSum,
    Finset.sum_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (by simp)

/-- If [f is measurable](hyp:hf) and [all its values lie in the cube](hyp:hbound),
then [pushing a probability law through f gives the cube mass one](goal). -/
-- @node: map_cube_mass_one
lemma map_cube_mass_one {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu] {d : ℕ} {K : ℝ}
    {f : X → L1Vec d} (hf : Measurable f)
    (hbound : ∀ x, f x ∈ boundedCube d K) :
    (mu.map f) (boundedCube d K) = 1 := by
  rw [Measure.map_apply hf (boundedCube_isCompact d K).measurableSet]
  have hpre : f ⁻¹' boundedCube d K = Set.univ := Set.eq_univ_of_forall hbound
  rw [hpre, measure_univ]

/-- If [F is uniformly bounded by the positive constant K](hyp:hbound),
[every map in F is measurable](hyp:hF), and [the sample size is
positive](hyp:hn), then [the supremum over F of the Wasserstein distances
between population and empirical pushforwards is at most 2 d K](goal). -/
-- @node: uniform_empirical_wasserstein_diameter
lemma uniform_empirical_wasserstein_diameter {X : Type*} [MeasurableSpace X]
    (mu : ProbabilityMeasure X) {d : ℕ} {K : ℝ}
    {F : Set (X → L1Vec d)} (hbound : ClassUniformlyBounded F K)
    (hF : ∀ f ∈ F, Measurable f) {n : ℕ} (hn : 0 < n) (x : Fin n → X) :
    (⨆ f : F, wasserstein1 ((mu : Measure X).map f.val)
      ((empiricalMeasure x).map f.val)) ≤ ENNReal.ofReal (2 * d * K) := by
  let := empiricalMeasure_probability hn x
  apply iSup_le
  intro f
  have hf := hF f.val f.property
  have hcube : ∀ x, f.val x ∈ boundedCube d K := by
    intro x j
    exact (norm_le_pi_norm (f.val x).ofLp j).trans (hbound.2 f.val f.property x)
  let m : ProbabilityMeasure (L1Vec d) :=
    ⟨(mu : Measure X).map f.val, Measure.isProbabilityMeasure_map hf.aemeasurable⟩
  let m' : ProbabilityMeasure (L1Vec d) :=
    ⟨(empiricalMeasure x).map f.val, Measure.isProbabilityMeasure_map hf.aemeasurable⟩
  exact wasserstein1_le_cube_diameter K hbound.1.le m m'
    (map_cube_mass_one (mu : Measure X) hf hcube)
    (map_cube_mass_one (empiricalMeasure x) hf hcube)

/-- If [F is uniformly bounded by the positive constant K](hyp:hbound),
[every map in F is measurable](hyp:hF), [the sample size is positive](hyp:hn),
[delta is nonnegative](hyp:hdelta), and [eps is at least 2 d K](hyp:heps), then
[the event that the supremum of the population-to-empirical pushforward
Wasserstein distances exceeds delta plus eps is empty](goal). -/
-- @node: uniform_empirical_wasserstein_large_eps_event_empty
lemma uniform_empirical_wasserstein_large_eps_event_empty
    {X : Type*} [MeasurableSpace X] (mu : ProbabilityMeasure X)
    {d : ℕ} {K : ℝ} {F : Set (X → L1Vec d)}
    (hbound : ClassUniformlyBounded F K) (hF : ∀ f ∈ F, Measurable f)
    {n : ℕ} (hn : 0 < n) {delta eps : ℝ} (hdelta : 0 ≤ delta)
    (heps : 2 * d * K ≤ eps) :
    {x : Fin n → X | ENNReal.ofReal (delta + eps) <
      ⨆ f : F, wasserstein1 ((mu : Measure X).map f.val)
        ((empiricalMeasure x).map f.val)} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hdiam := uniform_empirical_wasserstein_diameter mu hbound hF hn x
  have hthreshold : ENNReal.ofReal (2 * d * K) ≤ ENNReal.ofReal (delta + eps) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  exact (not_lt_of_ge (hdiam.trans hthreshold)) hx

/-- Suppose [F is uniformly bounded by the positive constant K](hyp:hbound),
[its maps are measurable](hyp:hF), [the sample size is positive](hyp:hn),
[all tests in H are continuous on the cube](hyp:hH), [delta is
nonnegative](hyp:hdelta), and [eps is nonnegative](hyp:heps). If [H approximates
every one-Lipschitz cube test vanishing at zero within delta/2 uniformly](hyp:hnet)
and [the nonnegative part of every population-minus-empirical contrast for a
test in H and a map in F is at most eps](hyp:hgood), then [the supremum of the pushforward
Wasserstein errors for this sample is at most delta plus eps](goal). -/
-- @node: uniform_empirical_wasserstein_le_of_test_net
lemma uniform_empirical_wasserstein_le_of_test_net
    {X : Type*} [MeasurableSpace X] (mu : ProbabilityMeasure X)
    {d : ℕ} {K : ℝ} {F : Set (X → L1Vec d)}
    (hbound : ClassUniformlyBounded F K) (hF : ∀ f ∈ F, Measurable f)
    {n : ℕ} (hn : 0 < n) (x : Fin n → X)
    (H : Set (L1Vec d → ℝ))
    (hH : ∀ g ∈ H, ContinuousOn g (boundedCube d K))
    {delta eps : ℝ} (hdelta : 0 ≤ delta) (heps : 0 ≤ eps)
    (hnet : ∀ h : L1Vec d → ℝ, LipschitzOnWith 1 h (boundedCube d K) → h 0 = 0 →
      ∃ g ∈ H, ∀ y ∈ boundedCube d K, |h y - g y| ≤ delta / 2)
    (hgood : ∀ g ∈ H, ∀ f ∈ F,
      ENNReal.ofReal ((∫ y, g y ∂((mu : Measure X).map f)) -
        ∫ y, g y ∂((empiricalMeasure x).map f)) ≤ ENNReal.ofReal eps) :
    (⨆ f : F, wasserstein1 ((mu : Measure X).map f.val)
      ((empiricalMeasure x).map f.val)) ≤ ENNReal.ofReal (delta + eps) := by
  let := empiricalMeasure_probability hn x
  apply iSup_le
  intro f
  have hf := hF f.val f.property
  have hcube : ∀ y, f.val y ∈ boundedCube d K := by
    intro y j
    exact (norm_le_pi_norm (f.val y).ofLp j).trans (hbound.2 f.val f.property y)
  let m : ProbabilityMeasure (L1Vec d) :=
    ⟨(mu : Measure X).map f.val, Measure.isProbabilityMeasure_map hf.aemeasurable⟩
  let m' : ProbabilityMeasure (L1Vec d) :=
    ⟨(empiricalMeasure x).map f.val, Measure.isProbabilityMeasure_map hf.aemeasurable⟩
  have hdual := wasserstein1_le_cube_test_net K hbound.1.le m m'
    (map_cube_mass_one (mu : Measure X) hf hcube)
    (map_cube_mass_one (empiricalMeasure x) hf hcube) H hH hdelta hnet
  refine hdual.trans ?_
  calc
    _ ≤ ENNReal.ofReal delta + ENNReal.ofReal eps := by
      apply add_le_add le_rfl
      exact iSup_le fun g => hgood g.val g.property f.val f.property
    _ = _ := (ENNReal.ofReal_add hdelta heps).symm

/-- Suppose [F is uniformly bounded by the positive constant K](hyp:hbound),
[its maps are measurable](hyp:hF), [the sample size is positive](hyp:hn),
[the finite test family H consists of functions continuous on the cube](hyp:hH),
[delta is nonnegative](hyp:hdelta), and [eps is nonnegative](hyp:heps).
If [H uniformly approximates every one-Lipschitz cube test vanishing at zero
within delta/2](hyp:hnet), then [under any sample measure Q, the outer measure
of the event that the supremum pushforward Wasserstein error exceeds delta
plus eps is at most the sum over H of the outer measures of the events that
some map in F has nonnegative test contrast exceeding eps](goal). -/
-- @node: uniform_empirical_wasserstein_test_net_union_bound
lemma uniform_empirical_wasserstein_test_net_union_bound
    {X : Type*} [MeasurableSpace X] (mu : ProbabilityMeasure X)
    {d : ℕ} {K : ℝ} {F : Set (X → L1Vec d)}
    (hbound : ClassUniformlyBounded F K) (hF : ∀ f ∈ F, Measurable f)
    {n : ℕ} (hn : 0 < n) (Q : Measure (Fin n → X))
    (H : Finset (L1Vec d → ℝ))
    (hH : ∀ g ∈ H, ContinuousOn g (boundedCube d K))
    {delta eps : ℝ} (hdelta : 0 ≤ delta) (heps : 0 ≤ eps)
    (hnet : ∀ h : L1Vec d → ℝ, LipschitzOnWith 1 h (boundedCube d K) → h 0 = 0 →
      ∃ g ∈ H, ∀ y ∈ boundedCube d K, |h y - g y| ≤ delta / 2) :
    Q {x : Fin n → X | ENNReal.ofReal (delta + eps) <
      ⨆ f : F, wasserstein1 ((mu : Measure X).map f.val)
        ((empiricalMeasure x).map f.val)} ≤
      ∑ g ∈ H, Q {x : Fin n → X | ∃ f ∈ F,
        ENNReal.ofReal eps < ENNReal.ofReal
          ((∫ y, g y ∂((mu : Measure X).map f)) -
            ∫ y, g y ∂((empiricalMeasure x).map f))} := by
  classical
  let B : (L1Vec d → ℝ) → Set (Fin n → X) := fun g =>
    {x | ∃ f ∈ F, ENNReal.ofReal eps < ENNReal.ofReal
      ((∫ y, g y ∂((mu : Measure X).map f)) -
        ∫ y, g y ∂((empiricalMeasure x).map f))}
  refine (measure_mono (t := ⋃ g ∈ H, B g) ?_).trans
    (measure_biUnion_finset_le H B)
  intro x hx
  by_contra hnot
  have hgood : ∀ g ∈ H, ∀ f ∈ F,
      ENNReal.ofReal ((∫ y, g y ∂((mu : Measure X).map f)) -
        ∫ y, g y ∂((empiricalMeasure x).map f)) ≤ ENNReal.ofReal eps := by
    intro g hg f hf
    apply le_of_not_gt
    intro hbad
    exact hnot (Set.mem_iUnion.mpr ⟨g, Set.mem_iUnion.mpr ⟨hg, f, hf, hbad⟩⟩)
  exact (not_lt_of_ge (uniform_empirical_wasserstein_le_of_test_net mu hbound hF hn x
    (H : Set (L1Vec d → ℝ)) hH hdelta heps hnet hgood)) hx

/-- If [the dimension is positive](hyp:hd), [K is positive](hyp:hK), [the sample
size is positive](hyp:hm), [r is positive](hyp:hr), [h is one-Lipschitz on the
cube](hyp:hh), [h vanishes at zero](hyp:hzero), and [every map in F takes its
values in the cube](hyp:hF), then [the empirical average-L1 covering number at
radius r of the class obtained by composing F with the normalized square-root
test of h at scale d K is at most the empirical L1 covering number of F at
radius 2 d K m r²](goal). -/
-- @node: anchored_cube_sqrt_cover_le
lemma anchored_cube_sqrt_cover_le {X : Type*} {d m : ℕ} {K r : ℝ}
    {F : Set (X → L1Vec d)} (hd : 0 < d) (hK : 0 < K)
    (hm : 0 < m) (hr : 0 < r) {h : L1Vec d → ℝ}
    (hh : LipschitzOnWith 1 h (boundedCube d K)) (hzero : h 0 = 0)
    (hF : ∀ f ∈ F, ∀ x, f x ∈ boundedCube d K) :
    N1avg r ((fun f : X → L1Vec d => normalizedSqrtTest h (d * K) ∘ f) '' F) m
      (normalizedSqrtTest_class_range (mul_pos (Nat.cast_pos.mpr hd) hK)
        (fun y hy => anchored_cube_test_abs_le hK.le hh hzero hy) hF) ≤
      empiricalL1CoveringNumber (ENNReal.ofReal (2 * d * K * m * r^2)) F m := by
  have hcover := normalizedSqrtTest_cover_le (mul_pos (Nat.cast_pos.mpr hd) hK)
    hr hm hh (fun y hy => anchored_cube_test_abs_le hK.le hh hzero hy) hF
  convert hcover using 1
  congr 2
  ring

/-- If [the coordinate pseudo-dimensions of F are bounded by dF](hyp:hF), then
[the class of scalar functions obtained from any coordinate j has
pseudo-dimension at most the nonnegative integer floor of dF](goal). -/
-- @node: coordinate_pseudodim_floor
lemma coordinate_pseudodim_floor {X : Type*} {d : ℕ}
    {F : Set (X → L1Vec d)} {dF : ℝ} (hF : CoordinatePseudoDimBound F dF)
    (j : Fin d) :
    Causalean.Stat.Concentration.HasPseudoDimAtMost
      (fun g : ((fun f : X → L1Vec d => fun x => (f x).ofLp j) '' F) => g.val) ⌊dF⌋₊ := by
  classical
  obtain ⟨k, hk, hv⟩ := hF.2 j
  have hkle : k ≤ ⌊dF⌋₊ := Nat.le_floor hk.le
  intro m T
  have heq : Causalean.Stat.Concentration.growthFamily
      (Causalean.Stat.Concentration.subgraphClassifier
        (fun g : ((fun f : X → L1Vec d => fun x => (f x).ofLp j) '' F) => g.val)) T =
      Causalean.Stat.Concentration.growthFamily
        (Causalean.Stat.Concentration.subgraphClassifier
          (fun f : F => fun x => (f.val x).ofLp j)) T := by
    ext A
    simp only [Causalean.Stat.Concentration.mem_growthFamily_iff]
    constructor
    · rintro ⟨⟨_, f, hf, rfl⟩, hpat⟩
      exact ⟨⟨f, hf⟩, hpat⟩
    · rintro ⟨⟨f, hf⟩, hpat⟩
      exact ⟨⟨_, Set.mem_image_of_mem _ hf⟩, hpat⟩
  rw [heq]
  exact (hv m T).trans hkle

/-- Assuming [the Anthony–Bartlett covering and concentration results](hyp:hAnthony),
if [F is nonempty](hyp:hne), [its coordinate pseudo-dimensions are bounded by
dF](hyp:hdim), [F is uniformly bounded by the positive constant K](hyp:hbound),
[m is positive](hyp:hm), and [r is positive](hyp:hr), then [the empirical L1
covering number of coordinate j, viewed as a one-dimensional vector, at radius
r/(2 d) is at most e (floor(dF) + 1) (2 + 8 e K d m/r) raised to floor(dF),
where the floor is truncated below at zero](goal). -/
-- @node: coordinate_empirical_cover_le
lemma coordinate_empirical_cover_le (hAnthony : AnthonyBartlettCoveringConcentration)
    {X : Type} {d : ℕ} {F : Set (X → L1Vec d)} (hne : F.Nonempty)
    {dF K : ℝ} (hdim : CoordinatePseudoDimBound F dF)
    (hbound : ClassUniformlyBounded F K) (j : Fin d)
    {m : ℕ} (hm : 0 < m) {r : ℝ} (hr : 0 < r) :
    (empiricalL1CoveringNumber (ENNReal.ofReal (r/(2*d)))
      ((fun g : X → ℝ => fun x => WithLp.toLp 1 (fun _ : Fin 1 => g x)) ''
        ((fun f : X → L1Vec d => fun x => (f x).ofLp j) '' F)) m).toENNReal ≤
      ENNReal.ofReal (Real.exp 1 * (⌊dF⌋₊+1) *
        (2 + 8 * Real.exp 1 * K * d * m / r)^⌊dF⌋₊) := by
  have hd : 0 < d := Nat.zero_lt_of_lt j.isLt
  have hscalar : ∀ g ∈ ((fun f : X → L1Vec d => fun x => (f x).ofLp j) '' F),
      ∀ x, |g x| ≤ K := by
    rintro _ ⟨f, hf, rfl⟩ x
    exact (norm_le_pi_norm (f x).ofLp j).trans (hbound.2 f hf x)
  have hb := empirical_scalar_cover_le hAnthony (hne.image _) hbound.1 hscalar
    (coordinate_pseudodim_floor hdim j) hm
    (div_pos hr (by positivity : (0 : ℝ) < 2*d))
  have hratio : 4 * Real.exp 1 * K * m / (r/(2*d)) =
      8 * Real.exp 1 * K * d * m / r := by
    field_simp
    <;> ring
  simpa only [hratio] using hb

/-- Assuming [the Anthony–Bartlett covering and concentration results](hyp:hAnthony),
if [the dimension is positive](hyp:hd), [F is nonempty](hyp:hne), [its coordinate
pseudo-dimensions are bounded by dF](hyp:hdim), [F is uniformly bounded by the
positive constant K](hyp:hbound), [m is positive](hyp:hm), and [r is
positive](hyp:hr), then [the empirical L1 covering number of F at radius r is
at most the d-th power of e (floor(dF) + 1) (2 + 8 e K d m/r) raised to
floor(dF), with the floor truncated below at zero](goal). -/
-- @node: vector_empirical_cover_le
lemma vector_empirical_cover_le (hAnthony : AnthonyBartlettCoveringConcentration)
    {X : Type} {d : ℕ} (hd : 0 < d) {F : Set (X → L1Vec d)} (hne : F.Nonempty)
    {dF K : ℝ} (hdim : CoordinatePseudoDimBound F dF)
    (hbound : ClassUniformlyBounded F K)
    {m : ℕ} (hm : 0 < m) {r : ℝ} (hr : 0 < r) :
    (empiricalL1CoveringNumber (ENNReal.ofReal r) F m).toENNReal ≤
      ENNReal.ofReal ((Real.exp 1 * (⌊dF⌋₊+1) *
        (2 + 8 * Real.exp 1 * K * d * m / r)^⌊dF⌋₊)^d) := by
  have hprod := ENat.toENNReal_mono
    (empiricalL1CoveringNumber_le_coordinate_product hd hr F m)
  refine hprod.trans ?_
  change ENat.toENNRealRingHom (∏ j : Fin d, _) ≤ _
  rw [map_prod]
  calc
    _ ≤ ∏ _j : Fin d, ENNReal.ofReal (Real.exp 1 * (⌊dF⌋₊+1) *
        (2 + 8 * Real.exp 1 * K * d * m / r)^⌊dF⌋₊) := by
      apply Finset.prod_le_prod'
      intro j _
      exact coordinate_empirical_cover_le hAnthony hne hdim hbound j hm hr
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      symm
      apply ENNReal.ofReal_pow
      have hK := hbound.1
      positivity

/-- Assuming [the Anthony–Bartlett covering and concentration results](hyp:hAnthony),
suppose [the dimension is positive](hyp:hd), [F is nonempty](hyp:hne), [its
coordinate pseudo-dimensions are bounded by dF](hyp:hdim), [F is uniformly
bounded by the positive constant K](hyp:hbound), [m is positive](hyp:hm), and
[r is positive](hyp:hr). If [h is one-Lipschitz on the cube](hyp:hh) and [vanishes
at zero](hyp:hzero), then [the empirical average-L1 covering number at radius r
of its normalized square-root compositions with F, at scale d K, is at most
the d-th power of e (floor(dF) + 1) (2 + 4 e/r²) raised to floor(dF), with the
floor truncated below at zero](goal). -/
-- @node: anchored_cube_sqrt_entropy_le
lemma anchored_cube_sqrt_entropy_le (hAnthony : AnthonyBartlettCoveringConcentration)
    {X : Type} {d m : ℕ} {K r dF : ℝ}
    {F : Set (X → L1Vec d)} (hd : 0 < d) (hne : F.Nonempty)
    (hdim : CoordinatePseudoDimBound F dF) (hbound : ClassUniformlyBounded F K)
    (hm : 0 < m) (hr : 0 < r) {h : L1Vec d → ℝ}
    (hh : LipschitzOnWith 1 h (boundedCube d K)) (hzero : h 0 = 0) :
    (N1avg r ((fun f : X → L1Vec d => normalizedSqrtTest h (d*K) ∘ f) '' F) m
      (normalizedSqrtTest_class_range (mul_pos (Nat.cast_pos.mpr hd) hbound.1)
        (fun y hy => anchored_cube_test_abs_le hbound.1.le hh hzero hy)
        (fun f hf x j => (norm_le_pi_norm (f x).ofLp j).trans (hbound.2 f hf x)))).toENNReal ≤
      ENNReal.ofReal ((Real.exp 1 * (⌊dF⌋₊+1) *
        (2 + 4 * Real.exp 1 / r^2)^⌊dF⌋₊)^d) := by
  have hc := anchored_cube_sqrt_cover_le hd hbound.1 hm hr hh hzero
    (fun f hf x j => (norm_le_pi_norm (f x).ofLp j).trans (hbound.2 f hf x))
  have hK := hbound.1
  have hv := vector_empirical_cover_le hAnthony hd hne hdim hbound hm
    (by positivity : 0 < 2 * (d : ℝ) * K * m * r^2)
  have hratio : 8 * Real.exp 1 * K * d * m / (2 * d * K * m * r^2) =
      4 * Real.exp 1 / r^2 := by
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    have hK0 := hbound.1.ne'
    field_simp
    <;> ring
  rw [hratio] at hv
  exact (ENat.toENNReal_mono hc).trans hv

/-- Suppose [F is uniformly bounded by the positive constant K](hyp:hbound),
[its maps are measurable](hyp:hF), [the sample size is positive](hyp:hn),
[the finite family H consists of tests continuous on the cube](hyp:hH),
[delta is nonnegative](hyp:hdelta), and [eps is nonnegative](hyp:heps).
If [H approximates every one-Lipschitz cube test vanishing at zero uniformly
within delta/2](hyp:hnet), [the logarithm of its cardinality is at most
entropy](hyp:hcard), and [each test's event that some map in F has nonnegative
population-minus-empirical contrast exceeding eps has Q-outer measure at most
exp(rate)](hyp:htail), then [the event that the supremum pushforward Wasserstein
error exceeds delta plus eps has Q-outer measure at most exp(entropy + rate)](goal). -/
-- @node: uniform_empirical_wasserstein_net_exp_bound
lemma uniform_empirical_wasserstein_net_exp_bound
    {X : Type*} [MeasurableSpace X] (mu : ProbabilityMeasure X)
    {d : ℕ} {K : ℝ} {F : Set (X → L1Vec d)}
    (hbound : ClassUniformlyBounded F K) (hF : ∀ f ∈ F, Measurable f)
    {n : ℕ} (hn : 0 < n) (Q : Measure (Fin n → X))
    (H : Finset (L1Vec d → ℝ))
    (hH : ∀ g ∈ H, ContinuousOn g (boundedCube d K))
    {delta eps entropy rate : ℝ} (hdelta : 0 ≤ delta) (heps : 0 ≤ eps)
    (hnet : ∀ h : L1Vec d → ℝ, LipschitzOnWith 1 h (boundedCube d K) → h 0 = 0 →
      ∃ g ∈ H, ∀ y ∈ boundedCube d K, |h y - g y| ≤ delta / 2)
    (hcard : Real.log (H.card : ℝ) ≤ entropy)
    (htail : ∀ g ∈ H, Q {x : Fin n → X | ∃ f ∈ F,
        ENNReal.ofReal eps < ENNReal.ofReal
          ((∫ y, g y ∂((mu : Measure X).map f)) -
            ∫ y, g y ∂((empiricalMeasure x).map f))} ≤
      ENNReal.ofReal (Real.exp rate)) :
    Q {x : Fin n → X | ENNReal.ofReal (delta+eps) <
      ⨆ f : F, wasserstein1 ((mu : Measure X).map f.val)
        ((empiricalMeasure x).map f.val)} ≤
      ENNReal.ofReal (Real.exp (entropy+rate)) := by
  exact (uniform_empirical_wasserstein_test_net_union_bound mu hbound hF hn Q H hH
    hdelta heps hnet).trans (empirical_finite_sum_exp_le H _ hcard htail)

/-- Suppose [F is uniformly bounded by the positive constant K](hyp:hbound),
[its maps are measurable](hyp:hF), [the sample size is positive](hyp:hn),
[the finite test family H is continuous on the cube](hyp:hH), [delta is
positive](hyp:hdelta), [eps is positive](hyp:heps), [dF is nonnegative](hyp:hdF),
[C₀ is nonnegative](hyp:hC₀), and [C₂ is nonnegative](hyp:hC₂). If [H uniformly
approximates every one-Lipschitz cube test vanishing at zero within
delta/2](hyp:hnet), [its log cardinality is at most C₂ (1 + delta⁻ᵈ)
log(2 + delta⁻¹)](hyp:hcard), and [each fixed-test failure event at tolerance eps
has Q-outer measure at most exp(C₀ (1 + dF log(2 + eps⁻¹)) − c n eps²)](hyp:htail),
then [the event that the supremum pushforward Wasserstein error exceeds delta
plus eps has Q-outer measure at most exp((C₀ + C₂ + C₀/log 2)
((1 + delta⁻ᵈ) log(2 + delta⁻¹) + dF log(2 + eps⁻¹)) − c n eps²)](goal). -/
-- @node: uniform_empirical_wasserstein_net_rate_bound
lemma uniform_empirical_wasserstein_net_rate_bound
    {X : Type*} [MeasurableSpace X] (mu : ProbabilityMeasure X)
    {d : ℕ} {K : ℝ} {F : Set (X → L1Vec d)}
    (hbound : ClassUniformlyBounded F K) (hF : ∀ f ∈ F, Measurable f)
    {n : ℕ} (hn : 0 < n) (Q : Measure (Fin n → X))
    (H : Finset (L1Vec d → ℝ))
    (hH : ∀ g ∈ H, ContinuousOn g (boundedCube d K))
    {delta eps dF C₀ C₂ c : ℝ} (hdelta : 0 < delta) (heps : 0 < eps)
    (hdF : 0 ≤ dF) (hC₀ : 0 ≤ C₀) (hC₂ : 0 ≤ C₂)
    (hnet : ∀ h : L1Vec d → ℝ, LipschitzOnWith 1 h (boundedCube d K) → h 0 = 0 →
      ∃ g ∈ H, ∀ y ∈ boundedCube d K, |h y - g y| ≤ delta / 2)
    (hcard : Real.log (H.card : ℝ) ≤
      C₂ * ((1 + delta ^ (-(d : ℤ))) * Real.log (2+delta⁻¹)))
    (htail : ∀ g ∈ H, Q {x : Fin n → X | ∃ f ∈ F,
        ENNReal.ofReal eps < ENNReal.ofReal
          ((∫ y, g y ∂((mu : Measure X).map f)) -
            ∫ y, g y ∂((empiricalMeasure x).map f))} ≤
      ENNReal.ofReal (Real.exp
        (C₀ * (1+dF * Real.log (2+eps⁻¹)) - c * n * eps^2))) :
    Q {x : Fin n → X | ENNReal.ofReal (delta+eps) <
      ⨆ f : F, wasserstein1 ((mu : Measure X).map f.val)
        ((empiricalMeasure x).map f.val)} ≤
      ENNReal.ofReal (Real.exp
        ((C₀ + C₂ + C₀ / Real.log 2) *
          ((1 + delta ^ (-(d : ℤ))) * Real.log (2+delta⁻¹) +
            dF * Real.log (2+eps⁻¹)) - c * n * eps^2)) := by
  have hdeltaInv : 0 ≤ delta⁻¹ := inv_nonneg.mpr hdelta.le
  have hepsInv : 0 ≤ eps⁻¹ := inv_nonneg.mpr heps.le
  have hlog : Real.log 2 ≤ Real.log (2+delta⁻¹) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlog0 : 0 ≤ Real.log (2+delta⁻¹) :=
    Real.log_nonneg (by linarith)
  have hD : Real.log 2 ≤
      (1 + delta ^ (-(d : ℤ))) * Real.log (2+delta⁻¹) := by
    calc
      _ ≤ Real.log (2+delta⁻¹) := hlog
      _ ≤ _ := by nlinarith [mul_nonneg (zpow_nonneg hdelta.le (-(d : ℤ))) hlog0]
  have hE : 0 ≤ dF * Real.log (2+eps⁻¹) :=
    mul_nonneg hdF (Real.log_nonneg (by linarith))
  have h := uniform_empirical_wasserstein_net_exp_bound mu hbound hF hn Q H hH
    hdelta.le heps.le hnet hcard htail
  refine h.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
  simpa only [add_sub_assoc] using
    sub_le_sub_right (empirical_entropy_constants_absorb hC₀ hC₂ hD hE) (c * n * eps^2)

/-- If [K is nonnegative](hyp:hK) and [C₀ is nonnegative](hyp:hC₀), then [there
is a positive constant C depending only on d, K, and C₀ such that, for any
uniformly K-bounded class of measurable maps, positive sample size, sample
measure Q, positive delta and eps, and nonnegative dF, fixed-test failure bounds
exp(C₀ (1 + dF log(2 + eps⁻¹)) − c n eps²) for all one-Lipschitz cube tests
vanishing at zero imply a Q-outer measure bound of
exp(C ((1 + delta⁻ᵈ) log(2 + delta⁻¹) + dF log(2 + eps⁻¹)) − c n eps²)
for the event that the supremum pushforward Wasserstein error exceeds delta
plus eps](goal). -/
-- @node: uniform_empirical_wasserstein_rate_of_fixed_test_tail
lemma uniform_empirical_wasserstein_rate_of_fixed_test_tail
    (d : ℕ) {K C₀ : ℝ} (hK : 0 ≤ K) (hC₀ : 0 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X : Type) [MeasurableSpace X] (mu : ProbabilityMeasure X)
        (F : Set (X → L1Vec d)),
        ClassUniformlyBounded F K → (∀ f ∈ F, Measurable f) →
        ∀ (n : ℕ), 0 < n → ∀ (Q : Measure (Fin n → X))
          (delta eps dF c : ℝ), 0 < delta → 0 < eps → 0 ≤ dF →
          (∀ g : L1Vec d → ℝ, LipschitzOnWith 1 g (boundedCube d K) → g 0 = 0 →
            Q {x : Fin n → X | ∃ f ∈ F,
              ENNReal.ofReal eps < ENNReal.ofReal
                ((∫ y, g y ∂((mu : Measure X).map f)) -
                  ∫ y, g y ∂((empiricalMeasure x).map f))} ≤
              ENNReal.ofReal (Real.exp
                (C₀ * (1+dF * Real.log (2+eps⁻¹)) - c * n * eps^2))) →
          Q {x : Fin n → X | ENNReal.ofReal (delta+eps) <
            ⨆ f : F, wasserstein1 ((mu : Measure X).map f.val)
              ((empiricalMeasure x).map f.val)} ≤
            ENNReal.ofReal (Real.exp
              (C * ((1+delta^(-(d : ℤ))) * Real.log (2+delta⁻¹) +
                dF * Real.log (2+eps⁻¹)) - c * n * eps^2)) := by
  obtain ⟨C₂, hC₂, hnet⟩ := exists_anchored_cube_test_net_entropy d hK
  refine ⟨C₀ + C₂ + C₀ / Real.log 2, ?_, ?_⟩
  · have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  · intro X _ mu F hbound hF n hn Q delta eps dF c hdelta heps hdF htail
    obtain ⟨T, hT, hcard, hcover⟩ := hnet delta hdelta
    exact uniform_empirical_wasserstein_net_rate_bound mu hbound hF hn Q T
      (fun g hg => (hT g hg).1.continuousOn) hdelta heps hdF hC₀ hC₂.le
      hcover hcard (fun g hg => htail g (hT g hg).1 (hT g hg).2)

/-- If [every map in F takes values in S](hyp:himage) and [h and g agree on
S](hyp:heq), then [their normalized square-root compositions with F give
identical function classes at every common scale R](goal). -/
-- @node: normalizedSqrtTest_class_congr_on
lemma normalizedSqrtTest_class_congr_on
    {X E : Type*} {F : Set (X → E)} {S : Set E}
    (himage : ∀ f ∈ F, ∀ x, f x ∈ S)
    {h g : E → ℝ} (heq : ∀ y ∈ S, h y = g y) (R : ℝ) :
    ((fun f : X → E => normalizedSqrtTest h R ∘ f) '' F) =
      ((fun f : X → E => normalizedSqrtTest g R ∘ f) '' F) := by
  have hcomp (f : X → E) (hf : f ∈ F) :
      normalizedSqrtTest h R ∘ f = normalizedSqrtTest g R ∘ f := by
    funext x
    simp only [Function.comp_apply, normalizedSqrtTest, heq _ (himage f hf x)]
  ext z
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, hf, (hcomp f hf).symm⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, hf, hcomp f hf⟩


/-- If [F is uniformly bounded by the positive constant K](hyp:hbound),
[h is one-Lipschitz on the cube](hyp:hh), and [h vanishes at zero](hyp:hzero),
then [there is a measurable test g that is one-Lipschitz on the cube, vanishes
at zero, is bounded in absolute value by d K everywhere, agrees with h on the
cube, and gives the same class of normalized square-root compositions with F
at scale d K](goal). -/
-- @node: exists_measurable_anchored_cube_test_representative
lemma exists_measurable_anchored_cube_test_representative
    {X : Type*} {d : ℕ} {K : ℝ} {F : Set (X → L1Vec d)}
    (hbound : ClassUniformlyBounded F K) {h : L1Vec d → ℝ}
    (hh : LipschitzOnWith 1 h (boundedCube d K)) (hzero : h 0 = 0) :
    ∃ g : L1Vec d → ℝ, Measurable g ∧
      LipschitzOnWith 1 g (boundedCube d K) ∧ g 0 = 0 ∧
      (∀ y, |g y| ≤ d*K) ∧
      (∀ y ∈ boundedCube d K, g y = h y) ∧
      ((fun f : X → L1Vec d => normalizedSqrtTest g (d*K) ∘ f) '' F) =
        ((fun f : X → L1Vec d => normalizedSqrtTest h (d*K) ∘ f) '' F) := by
  obtain ⟨g, hg, heq, hgbound⟩ := exists_measurable_bounded_test_representative
    (boundedCube_isCompact d K).measurableSet hh.continuousOn
    (mul_nonneg (Nat.cast_nonneg d) hbound.1.le)
    (fun y hy => anchored_cube_test_abs_le hbound.1.le hh hzero hy)
  have hLip : LipschitzOnWith 1 g (boundedCube d K) := by
    intro x hx y hy
    rw [heq x hx, heq y hy]
    exact hh hx hy
  have h0 : (0 : L1Vec d) ∈ boundedCube d K := by
    intro j
    simpa using hbound.1.le
  refine ⟨g, hg, hLip, (heq 0 h0).trans hzero, hgbound, heq, ?_⟩
  exact normalizedSqrtTest_class_congr_on (S := boundedCube d K)
    (fun f hf x j => (norm_le_pi_norm (f x).ofLp j).trans (hbound.2 f hf x)) heq _

end
end Papers.TbsNeuralCausalPi
