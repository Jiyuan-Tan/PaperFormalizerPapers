module
public import Papers.TbsNeuralCausalPi.Helpers.FiniteTableTransport
/-! # Transport across observed categorical strata

The observational sampling argument couples common categorical masses within
strata and residual masses across strata. The bounds below retain zero weights
and require neither independence of conditional latent coordinates nor attainment
of an optimal transport coupling.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

-- @node: finite_mixture_coupling
/-- Given [nonnegative extended-real source weights a](hyp:a), [target weights
b](hyp:b), and [transport matrix r](hyp:r), suppose [the source weights sum
to one](hyp:ha), [the matrix row sums equal a](hyp:hrow), and [its column sums
equal b](hyp:hcol). For [a coupling of every source and target component
pair](hyp:pi), [the matrix-weighted sum of these couplings is a coupling of
the corresponding weighted mixture laws](goal). -/
lemma finite_mixture_coupling
    {X I J : Type*} [MeasurableSpace X] [Fintype I] [Fintype J]
    (mu : I → Measure X) (nu : J → Measure X)
    (a : I → ℝ≥0∞) (b : J → ℝ≥0∞) (r : I → J → ℝ≥0∞)
    (ha : ∑ i, a i = 1) (hrow : ∀ i, ∑ j, r i j = a i)
    (hcol : ∀ j, ∑ i, r i j = b j)
    (pi : ∀ i j, couplings (mu i) (nu j)) :
    (∑ i, ∑ j, r i j • (pi i j).val) ∈
      couplings (∑ i, a i • mu i) (∑ j, b j • nu j) := by
  classical
  let (i : I) (j : J) : IsProbabilityMeasure (pi i j).val := (pi i j).property.1
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · simpa only [Measure.finsetSum_apply, Measure.smul_apply, measure_univ,
      smul_eq_mul, mul_one, hrow] using ha
  · simp_rw [Measure.map_finset_sum measurable_fst.aemeasurable,
      Measure.map_smul, (pi _ _).property.2.1]
    simp_rw [← Finset.sum_smul, hrow]
  · simp_rw [Measure.map_finset_sum measurable_snd.aemeasurable,
      Measure.map_smul, (pi _ _).property.2.2]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, hcol]

-- @node: finite_mixture_wasserstein_le_coupling_cost
/-- Given [nonnegative extended-real source weights a](hyp:a), [target weights
b](hyp:b), and [transport matrix r](hyp:r), suppose [a sums to one](hyp:ha),
[the row sums of r equal a](hyp:hrow), and [the column sums equal b](hyp:hcol).
For [couplings of every source and target component pair](hyp:pi), [the
Wasserstein-1 distance between the weighted mixture laws is at most the sum
of the component coupling costs weighted by r](goal). -/
lemma finite_mixture_wasserstein_le_coupling_cost
    {X I J : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [Fintype I] [Fintype J]
    (mu : I → Measure X) (nu : J → Measure X)
    (a : I → ℝ≥0∞) (b : J → ℝ≥0∞) (r : I → J → ℝ≥0∞)
    (ha : ∑ i, a i = 1) (hrow : ∀ i, ∑ j, r i j = a i)
    (hcol : ∀ j, ∑ i, r i j = b j)
    (pi : ∀ i j, couplings (mu i) (nu j)) :
    wasserstein1 (∑ i, a i • mu i) (∑ j, b j • nu j) ≤
      ∑ i, ∑ j, r i j * ∫⁻ z, edist z.1 z.2 ∂(pi i j).val := by
  have hc := finite_mixture_coupling mu nu a b r ha hrow hcol pi
  calc
    _ ≤ ∫⁻ z, edist z.1 z.2 ∂(∑ i, ∑ j, r i j • (pi i j).val) :=
      (wasserstein1_eq_couplings _ _).trans_le (iInf_le_of_le ⟨_, hc⟩ le_rfl)
    _ = _ := by simp only [lintegral_finsetSum_measure, lintegral_smul_measure, smul_eq_mul]

-- @node: coupling_cost_le_diameter
/-- If [S is measurable](hyp:hS), [the first marginal assigns S mass
one](hyp:hm), [the second marginal assigns S mass one](hyp:hn), and [all
pairwise distances in S are at most D](hyp:hdiam), [the expected transport
distance under any coupling of these marginals is at most D](goal). -/
lemma coupling_cost_le_diameter
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {mu nu : Measure X} (pi : couplings mu nu)
    (S : Set X) (hS : MeasurableSet S) (hm : mu S = 1) (hn : nu S = 1)
    (D : ℝ) (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ D) :
    (∫⁻ z, edist z.1 z.2 ∂pi.val) ≤ ENNReal.ofReal D := by
  let : IsProbabilityMeasure pi.val := pi.property.1
  let : IsProbabilityMeasure mu := pi.property.2.1 ▸
    Measure.isProbabilityMeasure_map (μ := pi.val) measurable_fst.aemeasurable
  let : IsProbabilityMeasure nu := pi.property.2.2 ▸
    Measure.isProbabilityMeasure_map (μ := pi.val) measurable_snd.aemeasurable
  have hm' : ∀ᵐ z ∂pi.val, z.1 ∈ S := by
    apply (ae_map_iff measurable_fst.aemeasurable hS).mp
    rw [pi.property.2.1]
    apply (ae_iff_measure_eq hS.nullMeasurableSet).mpr
    rw [show {a | S a} = S by ext a; rfl, measure_univ]
    exact hm
  have hn' : ∀ᵐ z ∂pi.val, z.2 ∈ S := by
    apply (ae_map_iff measurable_snd.aemeasurable hS).mp
    rw [pi.property.2.2]
    apply (ae_iff_measure_eq hS.nullMeasurableSet).mpr
    rw [show {a | S a} = S by ext a; rfl, measure_univ]
    exact hn
  calc
    _ ≤ ∫⁻ _z, ENNReal.ofReal D ∂pi.val := by
      apply lintegral_mono_ae
      filter_upwards [hm', hn'] with z hz hz'
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (hdiam _ hz _ hz')
    _ = _ := by simp

-- @node: categoricalCouplingWeights_diagonal
/-- [Each diagonal entry of the categorical coupling matrix equals the
minimum of the corresponding two category weights](goal). -/
lemma categoricalCouplingWeights_diagonal {k : ℕ} (p q : Fin k → ℝ) (i : Fin k) :
    categoricalCouplingWeights p q i i = min (p i) (q i) := by
  have hzero : (p i - min (p i) (q i)) * (q i - min (p i) (q i)) = 0 := by
    rcases le_total (p i) (q i) with h | h
    · simp [min_eq_left h]
    · simp [min_eq_right h]
  simp [categoricalCouplingWeights, hzero]

-- @node: stratified_mixture_wasserstein_le_coupling_cost
/-- Suppose [p is a probability vector](hyp:hp), [q is a probability
vector](hyp:hq), [S is measurable](hyp:hS), [all source component laws give S
mass one](hyp:hm), [all target component laws give S mass one](hyp:hn), and
[pairwise distances in S are at most D](hyp:hdiam). Given [a coupling between
the source and target law in each stratum](hyp:pi), [the mixture
Wasserstein-1 distance is at most the sum of these coupling costs weighted by
the minimum stratum masses, plus D divided by two times the sum of absolute
differences between p and q](goal). -/
lemma stratified_mixture_wasserstein_le_coupling_cost
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {k : ℕ} (mu nu : Fin k → Measure X)
    [∀ i, IsProbabilityMeasure (mu i)] [∀ i, IsProbabilityMeasure (nu i)]
    (p q : Fin k → ℝ) (hp : p ∈ probabilitySimplex k) (hq : q ∈ probabilitySimplex k)
    (S : Set X) (hS : MeasurableSet S)
    (hm : ∀ i, mu i S = 1) (hn : ∀ i, nu i S = 1)
    (D : ℝ) (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ D)
    (pi : ∀ i, couplings (mu i) (nu i)) :
    wasserstein1 (∑ i, ENNReal.ofReal (p i) • mu i)
      (∑ i, ENNReal.ofReal (q i) • nu i) ≤
        (∑ i, ENNReal.ofReal (min (p i) (q i)) *
          ∫⁻ z, edist z.1 z.2 ∂(pi i).val) +
        ENNReal.ofReal (D / 2 * ∑ i, |p i - q i|) := by
  classical
  let joint (i j : Fin k) : couplings (mu i) (nu j) :=
    if h : i = j then h ▸ pi i else
      ⟨(mu i).prod (nu j), inferInstance, by simp, by simp⟩
  obtain ⟨hr, hrow, hcol, hoff⟩ := categoricalCouplingWeights_properties hp hq
  have hbound (i j : Fin k) :
      ENNReal.ofReal (categoricalCouplingWeights p q i j) *
        (∫⁻ z, edist z.1 z.2 ∂(joint i j).val) ≤
      (if i = j then ENNReal.ofReal (min (p i) (q i)) *
        (∫⁻ z, edist z.1 z.2 ∂(pi i).val) else 0) +
      ENNReal.ofReal (if i = j then 0 else categoricalCouplingWeights p q i j) *
        ENNReal.ofReal D := by
    by_cases hij : i = j
    · subst j
      simp [joint, categoricalCouplingWeights_diagonal]
    · simp only [hij, ↓reduceIte, zero_add]
      gcongr
      exact coupling_cost_le_diameter (joint i j) S hS (hm i) (hn j) D hdiam
  calc
    _ ≤ ∑ i, ∑ j, ENNReal.ofReal (categoricalCouplingWeights p q i j) *
        ∫⁻ z, edist z.1 z.2 ∂(joint i j).val :=
      finite_mixture_wasserstein_le_coupling_cost mu nu _ _ _
        (by rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hp.1 i), hp.2]; simp)
        (fun i => by rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hr i j), hrow])
        (fun j => by rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hr i j), hcol]) joint
    _ ≤ ∑ i, ∑ j, ((if i = j then ENNReal.ofReal (min (p i) (q i)) *
          (∫⁻ z, edist z.1 z.2 ∂(pi i).val) else 0) +
        ENNReal.ofReal (if i = j then 0 else categoricalCouplingWeights p q i j) *
          ENNReal.ofReal D) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hbound i j
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hji
          simp [Ne.symm hji]
        · simp
      · have hnonneg (i j : Fin k) :
            0 ≤ (if i = j then 0 else categoricalCouplingWeights p q i j) := by
          split_ifs <;> first | exact le_rfl | exact hr i j
        simp_rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hnonneg _ j)]
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ =>
          Finset.sum_nonneg (fun j _ => hnonneg i j)), hoff,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

-- @node: stratified_mixture_wasserstein_le
/-- Suppose [p is a probability vector](hyp:hp), [q is a probability
vector](hyp:hq), [S is measurable](hyp:hS), [all source component laws give S
mass one](hyp:hm), [all target component laws give S mass one](hyp:hn), and
[pairwise distances in S are at most D](hyp:hdiam). [The mixture
Wasserstein-1 distance is at most the sum of the within-stratum Wasserstein-1
distances weighted by the minimum stratum masses, plus D divided by two
times the sum of absolute differences between p and q](goal). -/
lemma stratified_mixture_wasserstein_le
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {k : ℕ} (mu nu : Fin k → Measure X)
    [∀ i, IsProbabilityMeasure (mu i)] [∀ i, IsProbabilityMeasure (nu i)]
    (p q : Fin k → ℝ) (hp : p ∈ probabilitySimplex k) (hq : q ∈ probabilitySimplex k)
    (S : Set X) (hS : MeasurableSet S)
    (hm : ∀ i, mu i S = 1) (hn : ∀ i, nu i S = 1)
    (D : ℝ) (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ D) :
    wasserstein1 (∑ i, ENNReal.ofReal (p i) • mu i)
      (∑ i, ENNReal.ofReal (q i) • nu i) ≤
        (∑ i, ENNReal.ofReal (min (p i) (q i)) * wasserstein1 (mu i) (nu i)) +
        ENNReal.ofReal (D / 2 * ∑ i, |p i - q i|) := by
  classical
  let C (i : Fin k) := couplings (mu i) (nu i)
  have hne (i : Fin k) : Nonempty (C i) :=
    ⟨⟨(mu i).prod (nu i), inferInstance, by simp, by simp⟩⟩
  let (i : Fin k) : Nonempty (C i) := hne i
  let cost (i : Fin k) (pi : C i) :=
    ENNReal.ofReal (min (p i) (q i)) * ∫⁻ z, edist z.1 z.2 ∂pi.val
  have hdir (t : Finset (Fin k)) (a b : ∀ i, C i) :
      ∃ c : ∀ i, C i, ∀ i ∈ t,
        cost i (c i) ≤ cost i (a i) ∧ cost i (c i) ≤ cost i (b i) := by
    refine ⟨fun i => if cost i (a i) ≤ cost i (b i) then a i else b i, ?_⟩
    intro i hi
    dsimp only
    split_ifs with h
    · exact ⟨le_rfl, h⟩
    · exact ⟨le_of_not_ge h, le_rfl⟩
  have heval (i : Fin k) :
      (⨅ pi : ∀ j, C j, cost i (pi i)) = ⨅ q : C i, cost i q := by
    apply le_antisymm
    · refine le_iInf fun q => ?_
      let pi : ∀ j, C j := Function.update (fun j => Classical.choice (hne j)) i q
      exact iInf_le_of_le pi (by simp [pi])
    · exact le_iInf fun pi => iInf_le (fun q => cost i q) (pi i)
  calc
    _ ≤ ⨅ pi : ∀ i, C i, (∑ i, cost i (pi i)) +
        ENNReal.ofReal (D / 2 * ∑ i, |p i - q i|) :=
      le_iInf fun pi => stratified_mixture_wasserstein_le_coupling_cost
        mu nu p q hp hq S hS hm hn D hdiam pi
    _ = (∑ i, ⨅ pi : ∀ j, C j, cost i (pi i)) +
        ENNReal.ofReal (D / 2 * ∑ i, |p i - q i|) := by
      rw [← ENNReal.iInf_add, ENNReal.iInf_sum hdir]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [heval, wasserstein1_eq_couplings]
      exact (ENNReal.mul_iInf (by simp)).symm

-- @node: finite_stratum_probability_decomposition
/-- For [a measurable finite-valued label](hyp:hlabel) and [a measurable
set S](hyp:hS) with [population mass one](hyp:hm), [there exist stratum
probability laws that all give S mass one, agree with the population law
conditioned on the label whenever that label has nonzero mass, and reconstruct
the population law as their mixture weighted by label probabilities](goal). -/
lemma finite_stratum_probability_decomposition
    {X : Type*} [MeasurableSpace X] {k : ℕ}
    (mu : Measure X) [IsProbabilityMeasure mu]
    (label : X → Fin k) (hlabel : Measurable label)
    (S : Set X) (hS : MeasurableSet S) (hm : mu S = 1) :
    ∃ rho : Fin k → ProbabilityMeasure X,
      (∀ i, (rho i : Measure X) S = 1 ∧
        (mu (label ⁻¹' {i}) ≠ 0 →
          (rho i : Measure X) = ProbabilityTheory.cond mu (label ⁻¹' {i}))) ∧
      mu = ∑ i, mu (label ⁻¹' {i}) • (rho i : Measure X) := by
  classical
  let rho (i : Fin k) : ProbabilityMeasure X :=
    if h : mu (label ⁻¹' {i}) = 0 then ⟨mu, inferInstance⟩ else
      ⟨ProbabilityTheory.cond mu (label ⁻¹' {i}),
        ProbabilityTheory.cond_isProbabilityMeasure h⟩
  refine ⟨rho, ?_, ?_⟩
  · intro i
    by_cases hi : mu (label ⁻¹' {i}) = 0
    · simp [rho, hi, hm]
    · dsimp only [rho]
      rw [dif_neg hi]
      simp only [ProbabilityMeasure.coe_mk]
      refine ⟨?_, fun _ => True.intro⟩
      let : IsProbabilityMeasure (ProbabilityTheory.cond mu (label ⁻¹' {i})) :=
        ProbabilityTheory.cond_isProbabilityMeasure hi
      have hset : {a | S a} = S := by ext a; rfl
      have hmem : ∀ᵐ x ∂mu, x ∈ S :=
        (ae_iff_measure_eq hS.nullMeasurableSet).mpr
          (by simpa only [hset, measure_univ] using hm)
      have hcond := (ProbabilityTheory.cond_absolutelyContinuous
        (μ := mu) (s := label ⁻¹' {i})).ae_le hmem
      simpa only [hset, measure_univ] using
        (ae_iff_measure_eq hS.nullMeasurableSet).mp hcond
  · conv_lhs => rw [← ProbabilityTheory.sum_meas_smul_cond_fiber hlabel mu]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hz : mu (label ⁻¹' {i}) = 0
    · simp [hz]
    · simp [rho, hz]

-- @node: finite_stratum_weights_simplex
/-- For [a measurable finite-valued label](hyp:hlabel), [the vector of
population label probabilities belongs to the probability simplex: all its
entries are nonnegative and their sum is one](goal). -/
lemma finite_stratum_weights_simplex
    {X : Type*} [MeasurableSpace X] {k : ℕ}
    (mu : Measure X) [IsProbabilityMeasure mu]
    (label : X → Fin k) (hlabel : Measurable label) :
    (fun i => mu.real (label ⁻¹' {i})) ∈ probabilitySimplex k := by
  let : IsProbabilityMeasure (mu.map label) :=
    Measure.isProbabilityMeasure_map hlabel.aemeasurable
  have heq : (fun i => mu.real (label ⁻¹' {i})) =
      (fun i => (mu.map label).real {i}) := by
    funext i
    simp only [Measure.real, Measure.map_apply hlabel (measurableSet_singleton i)]
  rw [heq]
  exact finite_type_masses_simplex (mu.map label)

-- @node: observational_stratified_wasserstein_le
/-- Given [a measurable categorical label](hyp:hlabel) and [a measurable
carrier S](hyp:hS) with [mass one under the first law](hyp:hm) and [mass one
under the second law](hyp:hn), assume [pairwise distances in S are at most
D](hyp:hdiam). [There exist stratum probability laws agreeing with each
law's conditional distributions on every nonzero-mass stratum, such that the
Wasserstein-1 distance between the full laws is at most the sum of their
stratum Wasserstein-1 distances weighted by the minimum stratum probabilities,
plus D divided by two times the sum of absolute differences in stratum
probabilities](goal). -/
lemma observational_stratified_wasserstein_le
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {k : ℕ}
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (label : X → Fin k) (hlabel : Measurable label)
    (S : Set X) (hS : MeasurableSet S) (hm : mu S = 1) (hn : nu S = 1)
    (D : ℝ) (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ D) :
    ∃ rho sigma : Fin k → ProbabilityMeasure X,
      (∀ i, (mu (label ⁻¹' {i}) ≠ 0 →
          (rho i : Measure X) = ProbabilityTheory.cond mu (label ⁻¹' {i})) ∧
        (nu (label ⁻¹' {i}) ≠ 0 →
          (sigma i : Measure X) = ProbabilityTheory.cond nu (label ⁻¹' {i}))) ∧
      wasserstein1 mu nu ≤
        (∑ i, ENNReal.ofReal (min (mu.real (label ⁻¹' {i})) (nu.real (label ⁻¹' {i}))) *
          wasserstein1 (rho i : Measure X) (sigma i : Measure X)) +
        ENNReal.ofReal (D / 2 * ∑ i,
          |mu.real (label ⁻¹' {i}) - nu.real (label ⁻¹' {i})|) := by
  obtain ⟨rho, hrho, hmu⟩ := finite_stratum_probability_decomposition mu label hlabel S hS hm
  obtain ⟨sigma, hsigma, hnu⟩ := finite_stratum_probability_decomposition nu label hlabel S hS hn
  refine ⟨rho, sigma, fun i => ⟨(hrho i).2, (hsigma i).2⟩, ?_⟩
  have h := stratified_mixture_wasserstein_le
    (fun i => (rho i : Measure X)) (fun i => (sigma i : Measure X))
    (fun i => mu.real (label ⁻¹' {i})) (fun i => nu.real (label ⁻¹' {i}))
    (finite_stratum_weights_simplex mu label hlabel)
    (finite_stratum_weights_simplex nu label hlabel) S hS
    (fun i => (hrho i).1) (fun i => (hsigma i).1) D hdiam
  simp only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top mu _),
    ENNReal.ofReal_toReal (measure_ne_top nu _)] at h
  rwa [← hmu, ← hnu] at h

end Papers.TbsNeuralCausalPi
