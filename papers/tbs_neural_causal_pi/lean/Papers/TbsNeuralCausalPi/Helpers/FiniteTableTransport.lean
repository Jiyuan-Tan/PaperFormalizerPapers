module
public import Papers.TbsNeuralCausalPi.Helpers.CategoricalCoupling
public import Papers.TbsNeuralCausalPi.Helpers.EmpiricalWassersteinSteps
public import Papers.TbsNeuralCausalPi.Helpers.EmpiricalContrasts
public import Papers.TbsNeuralCausalPi.Helpers.WassersteinSpace
/-! # Transport of finite simulation tables

Uniform control of all subsets of a finite type space controls its half-L1
mass discrepancy. The existing maximal coupling then transports any bounded
table encoding, retaining the paired complete observed vector.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped ENNReal

-- @node: finite_type_positive_residual
/-- If [p is a probability vector](hyp:hp) and [q is a probability vector on
the same finite type space](hyp:hq), [summing p minus q over the types where p is at least q gives
half the sum of their absolute coordinate differences](goal). -/
lemma finite_type_positive_residual {k : ℕ} {p q : Fin k → ℝ}
    (hp : p ∈ probabilitySimplex k) (hq : q ∈ probabilitySimplex k) :
    (∑ i ∈ Finset.univ.filter (fun i => q i ≤ p i), (p i - q i)) =
      (∑ i, |p i - q i|) / 2 := by
  classical
  rw [← (categorical_residual_mass hp hq).2]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : q i ≤ p i
  · simp [hi]
  · simp [hi, min_eq_left (le_of_not_ge hi)]

-- @node: finite_type_half_l1_le_of_subsets
/-- If [p is a finite probability vector](hyp:hp), [q is a probability vector
on the same types](hyp:hq), and [their
total masses differ by at most e on every subset of types](hyp:hsub),
[half the sum of their absolute coordinate differences is at most e](goal). -/
lemma finite_type_half_l1_le_of_subsets {k : ℕ} {p q : Fin k → ℝ}
    (hp : p ∈ probabilitySimplex k) (hq : q ∈ probabilitySimplex k)
    (e : ℝ) (hsub : ∀ s : Finset (Fin k), |∑ i ∈ s, (p i - q i)| ≤ e) :
    (∑ i, |p i - q i|) / 2 ≤ e := by
  classical
  have h := hsub (Finset.univ.filter (fun i => q i ≤ p i))
  rw [finite_type_positive_residual hp hq, abs_of_nonneg
    (div_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by norm_num))] at h
  exact h

-- @node: finite_table_wasserstein_le_of_subsets
/-- Suppose [p is a finite probability vector](hyp:hp), [q is a probability
vector on the same types](hyp:hq),
[D is nonnegative](hyp:hD), [the encoded outputs have pairwise distance at
most D](hyp:hdiam), and [the two probability vectors differ in total mass by
at most e on every subset of types](hyp:hsub). Then [the Wasserstein distance
between their encoded atomic laws is at most D times e](goal). -/
lemma finite_table_wasserstein_le_of_subsets
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {k : ℕ} {p q : Fin k → ℝ}
    (hp : p ∈ probabilitySimplex k) (hq : q ∈ probabilitySimplex k)
    (v : Fin k → X) (D e : ℝ) (hD : 0 ≤ D)
    (hdiam : ∀ i j, dist (v i) (v j) ≤ D)
    (hsub : ∀ s : Finset (Fin k), |∑ i ∈ s, (p i - q i)| ≤ e) :
    wasserstein1 (∑ i, ENNReal.ofReal (p i) • Measure.dirac (v i))
      (∑ i, ENNReal.ofReal (q i) • Measure.dirac (v i)) ≤ ENNReal.ofReal (D * e) := by
  apply (categorical_wasserstein_half_l1_le hp hq v D hdiam).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    D / 2 * ∑ i, |p i - q i| = D * ((∑ i, |p i - q i|) / 2) := by ring
    _ ≤ D * e := mul_le_mul_of_nonneg_left
      (finite_type_half_l1_le_of_subsets hp hq e hsub) hD

-- @node: finite_type_masses_simplex
/-- [The singleton masses of a probability law on a finite type space are
nonnegative and sum to one](goal). -/
lemma finite_type_masses_simplex {k : ℕ} (mu : Measure (Fin k))
    [IsProbabilityMeasure mu] : (fun i => mu.real {i}) ∈ probabilitySimplex k := by
  classical
  refine ⟨fun i => ENNReal.toReal_nonneg, ?_⟩
  have h : (∑ i : Fin k, mu {i}) = 1 := by
    simp
  rw [← ENNReal.toReal_one, ← h, ENNReal.toReal_sum (fun i _ => measure_ne_top mu {i})]
  rfl

-- @node: finite_table_map_eq
/-- [Pushing a probability law on a finite type space through an encoding gives
the sum of point masses at the encoded values, weighted by the original type
probabilities](goal).

Zero-mass types and coincident encoded outputs are allowed. -/
lemma finite_table_map_eq {k : ℕ} {X : Type*} [MeasurableSpace X]
    (mu : Measure (Fin k)) [IsProbabilityMeasure mu] (v : Fin k → X) :
    mu.map v = ∑ i, ENNReal.ofReal (mu.real {i}) • Measure.dirac (v i) := by
  classical
  have hv : Measurable v := measurable_of_countable v
  conv_lhs => rw [← Measure.sum_smul_dirac mu]
  rw [Measure.sum_fintype, ← Measure.sum_fintype,
    Measure.map_sum hv.aemeasurable, Measure.sum_fintype]
  simp only [Measure.map_smul, Measure.map_dirac' hv, Measure.real,
    ENNReal.ofReal_toReal (measure_ne_top mu _)]

-- @node: finite_table_law_wasserstein_le
/-- If [D is nonnegative](hyp:hD), [a finite encoding has pairwise output
distances at most D](hyp:hdiam), and [two type probability laws differ in mass
by at most e on every subset](hyp:hsub), [the Wasserstein distance between their
encoded laws is at most D times e](goal). -/
lemma finite_table_law_wasserstein_le
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {k : ℕ} (mu nu : Measure (Fin k)) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (v : Fin k → X) (D e : ℝ) (hD : 0 ≤ D)
    (hdiam : ∀ i j, dist (v i) (v j) ≤ D)
    (hsub : ∀ s : Finset (Fin k), |mu.real (s : Set (Fin k)) - nu.real s| ≤ e) :
    wasserstein1 (mu.map v) (nu.map v) ≤ ENNReal.ofReal (D * e) := by
  rw [finite_table_map_eq mu v, finite_table_map_eq nu v]
  apply finite_table_wasserstein_le_of_subsets (finite_type_masses_simplex mu)
    (finite_type_masses_simplex nu) v D e hD hdiam
  intro s
  have hm := sum_measure_singleton (μ := mu) (s := s)
  have hn := sum_measure_singleton (μ := nu) (s := s)
  have hm' := congrArg ENNReal.toReal hm
  have hn' := congrArg ENNReal.toReal hn
  rw [ENNReal.toReal_sum (fun i _ => measure_ne_top mu {i})] at hm'
  rw [ENNReal.toReal_sum (fun i _ => measure_ne_top nu {i})] at hn'
  simpa only [Finset.sum_sub_distrib, Measure.real, hm', hn'] using hsub s

-- @node: empiricalMeasure_map_eq
/-- If [a transformation is measurable](hyp:hf), [pushing the empirical measure
of a sample through it gives the empirical measure of the transformed sample](goal). -/
lemma empiricalMeasure_map_eq {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]
    {m : ℕ} (x : Fin m → A) (f : A → X) (hf : Measurable f) :
    (empiricalMeasure x).map f = empiricalMeasure (fun i => f (x i)) := by
  simp only [empiricalMeasure, Measure.map_smul,
    Measure.map_finset_sum hf.aemeasurable, Measure.map_dirac' hf]

-- @node: empiricalMeasure_real_eq_indicator_average
/-- For [a measurable set](hyp:hs), [its mass under an empirical measure is the
sample average of its membership indicator](goal). -/
lemma empiricalMeasure_real_eq_indicator_average {X : Type*} [MeasurableSpace X]
    {m : ℕ} (x : Fin m → X) (s : Set X) (hs : MeasurableSet s) :
    (empiricalMeasure x).real s =
      (m : ℝ)⁻¹ * ∑ i, s.indicator (fun _ => (1 : ℝ)) (x i) := by
  calc
    _ = ∫ y, s.indicator (fun _ => (1 : ℝ)) y ∂empiricalMeasure x := by
      simpa only [Pi.one_def] using (integral_indicator_one (μ := empiricalMeasure x) hs).symm
    _ = _ := empiricalMeasure_integral_eq_average x (measurable_const.indicator hs)

-- @node: finite_table_empirical_wasserstein_le
/-- Suppose [the sample size is positive](hyp:hm), [the finite type assignment
is measurable](hyp:htype), [D is nonnegative](hyp:hD), [encoded type values have
pairwise distance at most D](hyp:hdiam), and [every type subset's population
probability differs from its sample frequency by at most e](hyp:hsub). Then
[the Wasserstein distance between the population law of the encoded types and
their empirical law on these draws is at most D times e](goal). -/
lemma finite_table_empirical_wasserstein_le
    {A X : Type*} [MeasurableSpace A]
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (mu : Measure A) [IsProbabilityMeasure mu] {k m : ℕ} (hm : 0 < m)
    (typeOf : A → Fin k) (htype : Measurable typeOf) (draws : Fin m → A)
    (v : Fin k → X) (D e : ℝ) (hD : 0 ≤ D)
    (hdiam : ∀ i j, dist (v i) (v j) ≤ D)
    (hsub : ∀ s : Finset (Fin k),
      |mu.real (typeOf ⁻¹' (s : Set (Fin k))) -
        (m : ℝ)⁻¹ * ∑ i, if typeOf (draws i) ∈ s then (1 : ℝ) else 0| ≤ e) :
    wasserstein1 (mu.map (v ∘ typeOf))
      (empiricalMeasure (fun i => v (typeOf (draws i)))) ≤ ENNReal.ofReal (D * e) := by
  classical
  let := Measure.isProbabilityMeasure_map (μ := mu) htype.aemeasurable
  let := empiricalMeasure_probability hm (fun i => typeOf (draws i))
  have hv : Measurable v := measurable_of_countable v
  rw [← Measure.map_map hv htype,
    ← empiricalMeasure_map_eq (fun i => typeOf (draws i)) v hv]
  apply finite_table_law_wasserstein_le _ _ v D e hD hdiam
  intro s
  rw [Measure.real, Measure.map_apply htype (s.measurableSet),
    ← Measure.real, empiricalMeasure_real_eq_indicator_average _ _ s.measurableSet]
  simpa [Set.indicator] using hsub s

-- @node: table_synchronous_wasserstein_le
/-- If [one simulation map is measurable](hyp:hf) and [a second simulation map
is measurable](hyp:hg), [the Wasserstein distance between their laws under the
same input probability measure is at most the expected distance between their
outputs evaluated on the same input](goal). -/
lemma table_synchronous_wasserstein_le
    {A X : Type*} [MeasurableSpace A]
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (mu : Measure A) [IsProbabilityMeasure mu]
    (f g : A → X) (hf : Measurable f) (hg : Measurable g) :
    wasserstein1 (mu.map f) (mu.map g) ≤ ∫⁻ z, edist (f z) (g z) ∂mu := by
  have hp : Measurable (fun z => (f z, g z)) := by fun_prop
  have hc : Causalean.Stat.IsCoupling (mu.map (fun z => (f z, g z)))
      (mu.map f) (mu.map g) := by
    refine ⟨Measure.isProbabilityMeasure_map hp.aemeasurable, ?_, ?_⟩
    · rw [Measure.map_map measurable_fst hp]
      rfl
    · rw [Measure.map_map measurable_snd hp]
      rfl
  apply (Toolkit.Foundations.MeasureTheory.wasserstein1_le_cost hc).trans_eq
  rw [lintegral_map (by fun_prop) hp]

-- @node: table_ambiguity_wasserstein_le
/-- Suppose [the first simulation map is measurable](hyp:hf), [the second is
measurable](hyp:hg), and [the ambiguity set is measurable](hyp:hE). Given
[a nonnegative, possibly infinite baseline cost c](hyp:c) and [a nonnegative,
possibly infinite ambiguity penalty B](hyp:B), if [the pointwise output
distance is at most c plus B on the ambiguity set, and at most c elsewhere](hyp:herr),
[the Wasserstein distance between the two output laws is at most c plus B
times the probability of ambiguity](goal). -/
lemma table_ambiguity_wasserstein_le
    {A X : Type*} [MeasurableSpace A]
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (mu : Measure A) [IsProbabilityMeasure mu]
    (f g : A → X) (hf : Measurable f) (hg : Measurable g)
    (E : Set A) (hE : MeasurableSet E) (c B : ℝ≥0∞)
    (herr : ∀ z, edist (f z) (g z) ≤ c + E.indicator (fun _ => B) z) :
    wasserstein1 (mu.map f) (mu.map g) ≤ c + B * mu E := by
  apply (table_synchronous_wasserstein_le mu f g hf hg).trans
  calc
    (∫⁻ z, edist (f z) (g z) ∂mu) ≤
        ∫⁻ z, c + E.indicator (fun _ => B) z ∂mu := lintegral_mono herr
    _ = _ := by
      rw [lintegral_add_left measurable_const, lintegral_indicator hE]
      simp

-- @node: empirical_table_ambiguity_wasserstein_le
/-- Suppose [the sample size is positive](hyp:hm), [the first simulation map
is measurable](hyp:hf), [the second is measurable](hyp:hg), and [the ambiguity
set is measurable](hyp:hE). Given [a nonnegative, possibly infinite baseline
cost c](hyp:c) and [a nonnegative, possibly infinite ambiguity penalty B](hyp:B),
if [the pointwise output distance is at most c plus B on the ambiguity set,
and at most c elsewhere](hyp:herr), [the Wasserstein distance between the two
empirical output laws on the same draws is at most c plus B times the sample
frequency of ambiguity](goal). -/
lemma empirical_table_ambiguity_wasserstein_le
    {A X : Type*} [MeasurableSpace A]
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    {m : ℕ} (hm : 0 < m) (draws : Fin m → A)
    (f g : A → X) (hf : Measurable f) (hg : Measurable g)
    (E : Set A) (hE : MeasurableSet E) (c B : ℝ≥0∞)
    (herr : ∀ z, edist (f z) (g z) ≤ c + E.indicator (fun _ => B) z) :
    wasserstein1 (empiricalMeasure (fun i => f (draws i)))
      (empiricalMeasure (fun i => g (draws i))) ≤
      c + B * ENNReal.ofReal ((m : ℝ)⁻¹ *
        ∑ i, E.indicator (fun _ => (1 : ℝ)) (draws i)) := by
  let := empiricalMeasure_probability hm draws
  have h := table_ambiguity_wasserstein_le (empiricalMeasure draws) f g hf hg E hE c B herr
  rw [empiricalMeasure_map_eq draws f hf, empiricalMeasure_map_eq draws g hg] at h
  rw [← ENNReal.ofReal_toReal (measure_ne_top (empiricalMeasure draws) E),
    ← Measure.real, empiricalMeasure_real_eq_indicator_average draws E hE] at h
  exact h

-- @node: simulation_table_transport_assembly
/-- Suppose [the sample size is positive](hyp:hm), [the simulation map is
measurable](hyp:hf), [the finite type assignment is measurable](hyp:htype),
[the output carrier is compact](hyp:hS), [every simulated output belongs to
that carrier](hyp:hfrange), [every table output belongs to it](hyp:hvrange),
and [the ambiguity set is measurable](hyp:hE). Given [a nonnegative, possibly
infinite baseline cost c](hyp:c) and [a nonnegative, possibly infinite ambiguity
penalty B](hyp:B), assume [D is nonnegative](hyp:hD), [table outputs have pairwise
distance at most D](hyp:hdiam), [simulation and table outputs differ by at most
c plus B on the ambiguity set and by at most c elsewhere](hyp:herr), and
[every type subset's population probability differs from its sample frequency
by at most e](hyp:hsub). Then [the Wasserstein error of the empirical simulation
law is at most the sum of c plus B times the population ambiguity probability,
D times e, and c plus B times the empirical ambiguity frequency](goal). -/
lemma simulation_table_transport_assembly
    {A X : Type*} [MeasurableSpace A]
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (mu : Measure A) [IsProbabilityMeasure mu] {k m : ℕ} (hm : 0 < m)
    (f : A → X) (hf : Measurable f)
    (typeOf : A → Fin k) (htype : Measurable typeOf) (draws : Fin m → A)
    (v : Fin k → X) (S : Set X) (hS : IsCompact S)
    (hfrange : ∀ z, f z ∈ S) (hvrange : ∀ i, v i ∈ S)
    (E : Set A) (hE : MeasurableSet E) (c B : ℝ≥0∞) (D e : ℝ)
    (hD : 0 ≤ D) (hdiam : ∀ i j, dist (v i) (v j) ≤ D)
    (herr : ∀ z, edist (f z) (v (typeOf z)) ≤ c + E.indicator (fun _ => B) z)
    (hsub : ∀ s : Finset (Fin k),
      |mu.real (typeOf ⁻¹' (s : Set (Fin k))) -
        (m : ℝ)⁻¹ * ∑ i, if typeOf (draws i) ∈ s then (1 : ℝ) else 0| ≤ e) :
    wasserstein1 (mu.map f) (empiricalMeasure (fun i => f (draws i))) ≤
      (c + B * mu E) + ENNReal.ofReal (D * e) +
        (c + B * ENNReal.ofReal ((m : ℝ)⁻¹ *
          ∑ i, E.indicator (fun _ => (1 : ℝ)) (draws i))) := by
  have hv : Measurable v := measurable_of_countable v
  have hg : Measurable (v ∘ typeOf) := by fun_prop
  letI := Measure.isProbabilityMeasure_map (μ := mu) hf.aemeasurable
  letI := Measure.isProbabilityMeasure_map (μ := mu) hg.aemeasurable
  letI := empiricalMeasure_probability hm (fun i => f (draws i))
  letI := empiricalMeasure_probability hm (fun i => v (typeOf (draws i)))
  have hfm : (mu.map f) S = 1 := by
    rw [Measure.map_apply hf hS.measurableSet]
    rw [show f ⁻¹' S = Set.univ by ext z; simp [hfrange z], measure_univ]
  have hgm : (mu.map (v ∘ typeOf)) S = 1 := by
    rw [Measure.map_apply hg hS.measurableSet]
    rw [show (v ∘ typeOf) ⁻¹' S = Set.univ by
      ext z; simp [Function.comp_def, hvrange], measure_univ]
  have hfe : (empiricalMeasure (fun i => f (draws i))) S = 1 := by
    simp only [empiricalMeasure, Measure.smul_apply, Measure.finsetSum_apply,
      Measure.dirac_apply' _ hS.measurableSet]
    simp [hfrange, ENNReal.inv_mul_cancel (a := (m : ℝ≥0∞)) (by exact_mod_cast hm.ne') (by simp)]
  have hge : (empiricalMeasure (fun i => v (typeOf (draws i)))) S = 1 := by
    simp only [empiricalMeasure, Measure.smul_apply, Measure.finsetSum_apply,
      Measure.dirac_apply' _ hS.measurableSet]
    simp [hvrange, ENNReal.inv_mul_cancel (a := (m : ℝ≥0∞)) (by exact_mod_cast hm.ne') (by simp)]
  have hpop := table_ambiguity_wasserstein_le mu f (v ∘ typeOf) hf hg E hE c B herr
  have htable := finite_table_empirical_wasserstein_le mu hm typeOf htype draws
    v D e hD hdiam hsub
  have hemp := empirical_table_ambiguity_wasserstein_le hm draws f (v ∘ typeOf)
    hf hg E hE c B herr
  have hsym := wasserstein1_symm
    (⟨empiricalMeasure (fun i => v (typeOf (draws i))), inferInstance⟩ : ProbabilityMeasure X)
    (⟨empiricalMeasure (fun i => f (draws i)), inferInstance⟩ : ProbabilityMeasure X)
  change wasserstein1 (empiricalMeasure (fun i => v (typeOf (draws i))))
    (empiricalMeasure (fun i => f (draws i))) =
    wasserstein1 (empiricalMeasure (fun i => f (draws i)))
      (empiricalMeasure (fun i => v (typeOf (draws i)))) at hsym
  calc
    _ ≤ wasserstein1 (mu.map f) (mu.map (v ∘ typeOf)) +
        wasserstein1 (mu.map (v ∘ typeOf)) (empiricalMeasure (fun i => f (draws i))) :=
      wasserstein1_triangle_compact_mass _ _ _ S hS hfm hgm hfe
    _ ≤ (c + B * mu E) +
        (wasserstein1 (mu.map (v ∘ typeOf))
          (empiricalMeasure (fun i => v (typeOf (draws i)))) +
        wasserstein1 (empiricalMeasure (fun i => v (typeOf (draws i))))
          (empiricalMeasure (fun i => f (draws i)))) :=
      add_le_add hpop (wasserstein1_triangle_compact_mass _ _ _ S hS hgm hge hfe)
    _ ≤ _ := by
      rw [hsym]
      exact (add_le_add (le_refl (c + B * mu E)) (add_le_add htable hemp)).trans_eq
        (add_assoc _ _ _).symm

-- @node: simulation_table_empirical_wasserstein_le
/-- Suppose [the sample size is positive](hyp:hm), [the simulation map is
measurable](hyp:hf), [the finite type assignment is measurable](hyp:htype),
[the output carrier is compact](hyp:hS), [all simulated outputs lie in the
carrier](hyp:hfrange), [all table outputs lie in it](hyp:hvrange), and [the
ambiguity set is measurable](hyp:hE). Assume [the baseline error c is nonnegative](hyp:hc),
[the ambiguity penalty B is nonnegative](hyp:hB), [the tolerance e is nonnegative](hyp:he),
[table outputs have pairwise distance at most B](hyp:hdiam), [the simulation
differs from its table by at most c plus B on the ambiguity set and by at most
c elsewhere](hyp:herr), [the population ambiguity probability is at most e](hyp:hprob),
[its empirical frequency differs from that probability by at most e](hyp:hamb),
and [every type subset's empirical frequency differs from its population
probability by at most e](hyp:hsub). Then [the Wasserstein distance between the
population simulation law and its empirical law is at most 2c + 4B e](goal). -/
lemma simulation_table_empirical_wasserstein_le
    {A X : Type*} [MeasurableSpace A]
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (mu : Measure A) [IsProbabilityMeasure mu] {k m : ℕ} (hm : 0 < m)
    (f : A → X) (hf : Measurable f)
    (typeOf : A → Fin k) (htype : Measurable typeOf) (draws : Fin m → A)
    (v : Fin k → X) (S : Set X) (hS : IsCompact S)
    (hfrange : ∀ z, f z ∈ S) (hvrange : ∀ i, v i ∈ S)
    (E : Set A) (hE : MeasurableSet E) (c B e : ℝ)
    (hc : 0 ≤ c) (hB : 0 ≤ B) (he : 0 ≤ e)
    (hdiam : ∀ i j, dist (v i) (v j) ≤ B)
    (herr : ∀ z, edist (f z) (v (typeOf z)) ≤
      ENNReal.ofReal c + E.indicator (fun _ => ENNReal.ofReal B) z)
    (hprob : mu.real E ≤ e)
    (hamb : |mu.real E - (m : ℝ)⁻¹ *
      ∑ i, E.indicator (fun _ => (1 : ℝ)) (draws i)| ≤ e)
    (hsub : ∀ s : Finset (Fin k),
      |mu.real (typeOf ⁻¹' (s : Set (Fin k))) -
        (m : ℝ)⁻¹ * ∑ i, if typeOf (draws i) ∈ s then (1 : ℝ) else 0| ≤ e) :
    wasserstein1 (mu.map f) (empiricalMeasure (fun i => f (draws i))) ≤
      ENNReal.ofReal (2 * c + 4 * B * e) := by
  have hfreq : (m : ℝ)⁻¹ *
      ∑ i, E.indicator (fun _ => (1 : ℝ)) (draws i) ≤ 2 * e := by
    have hlo := (abs_le.mp hamb).1
    linarith
  have hp : mu E ≤ ENNReal.ofReal e := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top mu E)]
    exact ENNReal.ofReal_le_ofReal hprob
  apply (simulation_table_transport_assembly mu hm f hf typeOf htype draws v S hS
    hfrange hvrange E hE (ENNReal.ofReal c) (ENNReal.ofReal B) B e hB hdiam
    herr hsub).trans
  calc
    _ ≤ (ENNReal.ofReal c + ENNReal.ofReal B * ENNReal.ofReal e) +
        ENNReal.ofReal (B * e) +
        (ENNReal.ofReal c + ENNReal.ofReal B * ENNReal.ofReal (2 * e)) :=
      add_le_add (add_le_add (add_le_add le_rfl (mul_le_mul le_rfl hp bot_le bot_le)) le_rfl)
        (add_le_add le_rfl (mul_le_mul le_rfl (ENNReal.ofReal_le_ofReal hfreq) bot_le bot_le))
    _ = _ := by
      rw [← ENNReal.ofReal_mul hB, ← ENNReal.ofReal_mul hB,
        ← ENNReal.ofReal_add hc (mul_nonneg hB he),
        ← ENNReal.ofReal_add (add_nonneg hc (mul_nonneg hB he)) (mul_nonneg hB he),
        ← ENNReal.ofReal_add hc (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

end Papers.TbsNeuralCausalPi
