module
public import Papers.TbsNeuralCausalPi.Helpers.Sinkhorn
public import Papers.TbsNeuralCausalPi.Helpers.FiniteTableTransport
public import Papers.TbsNeuralCausalPi.Helpers.EstimationFeasibility
/-! # The finite transport matrix and empirical-measure Wasserstein cost

The matrix infimum used in the Sinkhorn constraint agrees with the coupling
infimum, including repeated atoms and zero weights. Finite transport duality
supplies the reverse inequality; a minimizing matrix supplies a coupling.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section

/-- If [the target atom list is nonempty](hyp:hm), [the source weights are
nonnegative and sum to one](hyp:hmu), and [the target weights are nonnegative
and sum to one](hyp:hnu), then [the finite matrix transport cost equals the
Wasserstein distance between the corresponding weighted atomic measures](goal). -/
-- @node: discreteW1_eq_atomic_wasserstein1
lemma discreteW1_eq_atomic_wasserstein1 {n m d : ℕ} (hm : 0 < m)
    (x : Fin n → L1Vec d) (y : Fin m → L1Vec d)
    (mu : Fin n → ℝ) (nu : Fin m → ℝ)
    (hmu : mu ∈ probabilitySimplex n) (hnu : nu ∈ probabilitySimplex m) :
    ENNReal.ofReal (discreteW1 x y mu nu) =
      wasserstein1 (∑ i, ENNReal.ofReal (mu i) • Measure.dirac (x i))
        (∑ j, ENNReal.ofReal (nu j) • Measure.dirac (y j)) := by
  classical
  let a : Fin n → ℝ≥0 := fun i => ⟨mu i, hmu.1 i⟩
  let b : Fin m → ℝ≥0 := fun j => ⟨nu j, hnu.1 j⟩
  have ha : ∑ i, (a i : ℝ) = 1 := hmu.2
  have hb : ∑ j, (b j : ℝ) = 1 := hnu.2
  have hplan (p : Fin n → Fin m → ℝ) :
      p ∈ transportPlans mu nu ↔
        Toolkit.Foundations.Optimization.Convex.IsFiniteTransportPlan a b p := by
    constructor
    · exact fun hp => ⟨hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2⟩
    · exact fun hp => ⟨hmu, hnu, hp.1, hp.2.1, hp.2.2⟩
  obtain ⟨p, hp, hmin⟩ :=
    Toolkit.Foundations.Optimization.Convex.exists_minimal_finiteTransportPlan
      a b ha hb (fun i j => dist (x i) (y j))
  have hp' := (hplan p).mpr hp
  have hvalue : discreteW1 x y mu nu = transportCost x y p := by
    unfold discreteW1
    apply le_antisymm
    · exact csInf_le ⟨0, by
        rintro _ ⟨q, hq, rfl⟩
        exact transportCost_nonneg x y hq⟩ ⟨p, hp', rfl⟩
    · have hne : (transportCost x y '' transportPlans mu nu).Nonempty :=
        ⟨transportCost x y p, p, hp', rfl⟩
      apply le_csInf hne
      rintro _ ⟨q, hq, rfl⟩
      exact hmin q ((hplan q).mp hq)
  let muA : Measure (L1Vec d) := ∑ i, (a i : ℝ≥0∞) • Measure.dirac (x i)
  let nuA : Measure (L1Vec d) := ∑ j, (b j : ℝ≥0∞) • Measure.dirac (y j)
  have hmuA : muA = ∑ i, ENNReal.ofReal (mu i) • Measure.dirac (x i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [show (a i : ℝ≥0∞) = ENNReal.ofReal (mu i) from
      (ENNReal.ofReal_eq_coe_nnreal (hmu.1 i)).symm]
  have hnuA : nuA = ∑ j, ENNReal.ofReal (nu j) • Measure.dirac (y j) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [show (b j : ℝ≥0∞) = ENNReal.ofReal (nu j) from
      (ENNReal.ofReal_eq_coe_nnreal (hnu.1 j)).symm]
  rw [← hmuA, ← hnuA, hvalue]
  obtain ⟨pi, hpi, hcost⟩ :=
    Toolkit.Foundations.MeasureTheory.finiteTransportPlan_coupling a b ha x y p hp
  have hupper : wasserstein1 muA nuA ≤ ENNReal.ofReal (transportCost x y p) :=
    hcost ▸ Toolkit.Foundations.MeasureTheory.wasserstein1_le_cost hpi
  have hfinite : wasserstein1 muA nuA ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hupper
  apply le_antisymm ?_ hupper
  apply (ENNReal.ofReal_le_iff_le_toReal hfinite).mpr
  apply le_of_forall_pos_le_add
  intro eps heps
  obtain ⟨u, v, huv, hnear⟩ :=
    Toolkit.Foundations.Optimization.Convex.finiteTransport_dual_certificate
      a b (fun i j => dist (x i) (y j)) p hp hmin heps
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨f, hf, hsource, htarget⟩ :=
    Toolkit.Foundations.MeasureTheory.exists_lipschitz_potential x y u v huv
  have hint (z : Fin n → L1Vec d) (w : Fin n → ℝ≥0) :
      Integrable f (∑ i, (w i : ℝ≥0∞) • Measure.dirac (z i)) := by
    apply integrable_finsetSum_measure.mpr
    intro i _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.coe_ne_top
  have hintNu : Integrable f nuA := by
    apply integrable_finsetSum_measure.mpr
    intro j _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.coe_ne_top
  have htest : (∫ z, f z ∂muA) - (∫ z, f z ∂nuA) ≤
      (wasserstein1 muA nuA).toReal := by
    apply (ENNReal.ofReal_le_iff_le_toReal hfinite).mp
    exact Toolkit.Foundations.MeasureTheory.lipschitzContrast_le_wasserstein1
      hf (hint x a) hintNu
  have hleft := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hsource i) (a i).coe_nonneg)
  have hright := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (htarget j) (b j).coe_nonneg)
  have hIm : (∫ z, f z ∂muA) = ∑ i, (a i : ℝ) * f (x i) := by
    rw [integral_finsetSum_measure (fun i _ =>
      (integrable_dirac (by simp)).smul_measure ENNReal.coe_ne_top)]
    simp [NNReal.smul_def, smul_eq_mul]
  have hIn : (∫ z, f z ∂nuA) = ∑ j, (b j : ℝ) * f (y j) := by
    rw [integral_finsetSum_measure (fun j _ =>
      (integrable_dirac (by simp)).smul_measure ENNReal.coe_ne_top)]
    simp [NNReal.smul_def, smul_eq_mul]
  rw [hIm, hIn] at htest
  simp only [mul_neg, Finset.sum_neg_distrib] at hright
  change transportCost x y p < _ at hnear
  linarith

/-- If [the sample size is positive](hyp:hm), then [its uniform weights are
nonnegative and sum to one](goal). -/
-- @node: uniformWeights_mem_probabilitySimplex
lemma uniformWeights_mem_probabilitySimplex {m : ℕ} (hm : 0 < m) :
    uniformWeights m ∈ probabilitySimplex m := by
  refine ⟨fun _ => inv_nonneg.mpr (Nat.cast_nonneg m), ?_⟩
  simp [uniformWeights, ne_of_gt hm]

/-- [The empirical measure of a finite sample equals the sum of point masses
at its observations weighted by the uniform sample weights](goal). -/
-- @node: empiricalMeasure_eq_uniform_atomic
lemma empiricalMeasure_eq_uniform_atomic {X : Type*} [MeasurableSpace X]
    {m : ℕ} (x : Fin m → X) :
    empiricalMeasure x = ∑ i, ENNReal.ofReal (uniformWeights m i) • Measure.dirac (x i) := by
  by_cases hm : m = 0
  · subst m
    simp [empiricalMeasure]
  · simp only [empiricalMeasure, uniformWeights, ENNReal.ofReal_inv_of_pos
      (by exact_mod_cast Nat.pos_of_ne_zero hm : (0 : ℝ) < m),
      ENNReal.ofReal_natCast, Finset.smul_sum]

/-- If [the source sample size is positive](hyp:hn) and [the target sample size
is positive](hyp:hm), then [the finite matrix transport cost with uniform weights
equals the Wasserstein distance between the two empirical measures](goal). -/
-- @node: discreteW1_eq_empirical_wasserstein1
lemma discreteW1_eq_empirical_wasserstein1 {n m d : ℕ} (hn : 0 < n) (hm : 0 < m)
    (x : Fin n → L1Vec d) (y : Fin m → L1Vec d) :
    ENNReal.ofReal (discreteW1 x y (uniformWeights n) (uniformWeights m)) =
      wasserstein1 (empiricalMeasure x) (empiricalMeasure y) := by
  rw [empiricalMeasure_eq_uniform_atomic x, empiricalMeasure_eq_uniform_atomic y]
  exact discreteW1_eq_atomic_wasserstein1 hm x y _ _
    (uniformWeights_mem_probabilitySimplex hn) (uniformWeights_mem_probabilitySimplex hm)

/-- If [the source sample size is positive](hyp:hn), [the target sample size
is positive](hyp:hm), and [the regularization parameter is positive](hyp:hlam), then
[the empirical Wasserstein distance lies between the nonnegative parts of
the Sinkhorn divergence minus and plus the bias, where the bias is twice
the regularization parameter times one plus the logarithm of the product
of sample sizes](goal). -/
-- @node: sinkhorn_empirical_wasserstein1_control
lemma sinkhorn_empirical_wasserstein1_control {n m d : ℕ} (hn : 0 < n) (hm : 0 < m)
    (x : Fin n → L1Vec d) (y : Fin m → L1Vec d) (lam : ℝ) (hlam : 0 < lam) :
    let e := sinkhornDivergence lam x y (uniformWeights n) (uniformWeights m)
    let bias := 2 * (Real.log (m * n : ℕ) + 1) * lam
    wasserstein1 (empiricalMeasure x) (empiricalMeasure y) ≤ ENNReal.ofReal (e + bias) ∧
      ENNReal.ofReal (e - bias) ≤ wasserstein1 (empiricalMeasure x) (empiricalMeasure y) := by
  dsimp only
  have h := (sinkhorn_approx hn hm x y _ _
    (uniformWeights_mem_probabilitySimplex hn)
    (uniformWeights_mem_probabilitySimplex hm) lam hlam).2.2
  rw [← discreteW1_eq_empirical_wasserstein1 hn hm x y]
  obtain ⟨hl, hu⟩ := abs_le.mp h
  constructor <;> apply ENNReal.ofReal_le_ofReal <;> linarith

/-- [Mapping both measures through a distance-preserving bijection cannot
increase their Wasserstein distance](goal). -/
-- @node: wasserstein1_map_isometry_le
lemma wasserstein1_map_isometry_le {A B : Type*}
    [MetricSpace A] [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
    [MetricSpace B] [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
    (f : A ≃ᵢ B) (a b : Measure A) :
    wasserstein1 (a.map f) (b.map f) ≤ wasserstein1 a b := by
  have hfm : Measurable f := by fun_prop
  rw [wasserstein1_eq_couplings a b]
  refine le_iInf fun pi => ?_
  let := pi.property.1
  let F : A × A → B × B := fun z => (f z.1, f z.2)
  have hF : Measurable F := by fun_prop
  have hc : pi.val.map F ∈ couplings (a.map f) (b.map f) := by
    refine ⟨Measure.isProbabilityMeasure_map hF.aemeasurable, ?_, ?_⟩
    · rw [Measure.map_map measurable_fst hF,
        show Prod.fst ∘ F = f ∘ Prod.fst from rfl,
        ← Measure.map_map hfm measurable_fst, pi.property.2.1]
    · rw [Measure.map_map measurable_snd hF,
        show Prod.snd ∘ F = f ∘ Prod.snd from rfl,
        ← Measure.map_map hfm measurable_snd, pi.property.2.2]
  calc
    wasserstein1 (a.map f) (b.map f) ≤ ∫⁻ z, edist z.1 z.2 ∂pi.val.map F :=
      (wasserstein1_eq_couplings _ _).trans_le (iInf_le_of_le ⟨_, hc⟩ le_rfl)
    _ = ∫⁻ z, edist z.1 z.2 ∂pi.val := by
      rw [lintegral_map (by fun_prop) hF]
      simp only [F, f.isometry.edist_eq]

/-- [Mapping both measures through a distance-preserving bijection preserves
their Wasserstein distance](goal). -/
-- @node: wasserstein1_map_isometryEquiv
lemma wasserstein1_map_isometryEquiv {X Y : Type*}
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (e : X ≃ᵢ Y) (mu nu : Measure X) :
    wasserstein1 (mu.map e) (nu.map e) = wasserstein1 mu nu := by
  apply le_antisymm (wasserstein1_map_isometry_le e mu nu)
  have h := wasserstein1_map_isometry_le e.symm (mu.map e) (nu.map e)
  simpa only [Measure.map_map e.symm.continuous.measurable e.continuous.measurable,
    e.symm_comp_self, Measure.map_id] using h

/-- [Flattening joint observations into coordinate vectors preserves their
one-norm distances](goal). -/
-- @node: jointVector_isometry
lemma jointVector_isometry {n : ℕ} (kind : Fin n → NodeKind) :
    Isometry (jointVector (kind := kind)) := by
  exact (LinearIsometryEquiv.piLpCongrLeft 1 ℝ ℝ
    (Fintype.equivFin (JointCoordinates kind))).isometry

/-- If [the first sample size is positive](hyp:hn) and [the second sample size
is positive](hyp:hm), then [the uniformly weighted matrix transport cost of the
flattened joint observations equals the Wasserstein distance between their
joint empirical measures](goal). -/
-- @node: joint_discreteW1_eq_empirical_wasserstein1
lemma joint_discreteW1_eq_empirical_wasserstein1 {v n m : ℕ}
    {kind : Fin v → NodeKind} (hn : 0 < n) (hm : 0 < m)
    (x : Fin n → Joint kind) (y : Fin m → Joint kind) :
    ENNReal.ofReal (discreteW1 (fun i => jointVector (x i)) (fun j => jointVector (y j))
      (uniformWeights n) (uniformWeights m)) =
      wasserstein1 (empiricalMeasure x) (empiricalMeasure y) := by
  rw [discreteW1_eq_empirical_wasserstein1 hn hm]
  let e := (LinearIsometryEquiv.piLpCongrLeft 1 ℝ ℝ
    (Fintype.equivFin (JointCoordinates kind))).toIsometryEquiv
  have he : (e : Joint kind → L1Vec (Fintype.card (JointCoordinates kind))) = jointVector := rfl
  have hm : Measurable (jointVector (kind := kind)) := by
    exact (jointVector_isometry kind).continuous.measurable
  rw [← empiricalMeasure_map_eq x jointVector hm, ← empiricalMeasure_map_eq y jointVector hm,
    ← he]
  exact wasserstein1_map_isometryEquiv e _ _

/-- Suppose [S is compact](hyp:hS), [the first population law gives S full
mass](hyp:hmu), [the second population law gives S full mass](hyp:hnu),
[the first empirical law gives S full mass](hyp:hmuE), and [the second
empirical law gives S full mass](hyp:hnuE). If [a is nonnegative](hyp:ha),
[b is nonnegative](hyp:hb), [q is nonnegative](hyp:hq), [the first
population-to-empirical Wasserstein error is at most a](hyp:hsim), [the second
is at most b](hyp:hobs), [the empirical Wasserstein distance equals q](hyp:hemp),
and [e differs from q by at most bias](hyp:hreg), then [the population
Wasserstein distance lies between the nonnegative parts of e minus and plus
the combined error a + b + bias](goal). -/
-- @node: wasserstein1_two_sample_constraint_control
lemma wasserstein1_two_sample_constraint_control {X : Type*}
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (mu nu muE nuE : Measure X)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    [IsProbabilityMeasure muE] [IsProbabilityMeasure nuE]
    (S : Set X) (hS : IsCompact S)
    (hmu : mu S = 1) (hnu : nu S = 1) (hmuE : muE S = 1) (hnuE : nuE S = 1)
    (a b q e bias : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hq : 0 ≤ q)
    (hsim : wasserstein1 mu muE ≤ ENNReal.ofReal a)
    (hobs : wasserstein1 nu nuE ≤ ENNReal.ofReal b)
    (hemp : wasserstein1 muE nuE = ENNReal.ofReal q)
    (hreg : |e - q| ≤ bias) :
    wasserstein1 mu nu ≤ ENNReal.ofReal (e + (a + b + bias)) ∧
      ENNReal.ofReal (e - (a + b + bias)) ≤ wasserstein1 mu nu := by
  have hsim' : wasserstein1 muE mu ≤ ENNReal.ofReal a := by
    exact (wasserstein1_symm ⟨muE, inferInstance⟩ ⟨mu, inferInstance⟩).trans_le hsim
  have hobs' : wasserstein1 nuE nu ≤ ENNReal.ofReal b := by
    exact (wasserstein1_symm ⟨nuE, inferInstance⟩ ⟨nu, inferInstance⟩).trans_le hobs
  have hupper : wasserstein1 mu nu ≤ ENNReal.ofReal (a + q + b) := by
    calc
      wasserstein1 mu nu ≤ wasserstein1 mu muE + wasserstein1 muE nu :=
        wasserstein1_triangle_compact_mass _ _ _ S hS hmu hmuE hnu
      _ ≤ ENNReal.ofReal a + (wasserstein1 muE nuE + ENNReal.ofReal b) :=
        add_le_add hsim ((wasserstein1_triangle_compact_mass _ _ _ S hS
          hmuE hnuE hnu).trans (add_le_add le_rfl hobs'))
      _ = ENNReal.ofReal (a + q + b) := by
        rw [hemp, ← ENNReal.ofReal_add hq hb,
          ← ENNReal.ofReal_add ha (add_nonneg hq hb)]
        congr 1
        ring
  have hp : wasserstein1 mu nu ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hupper
  have hlower : ENNReal.ofReal q ≤
      ENNReal.ofReal a + (wasserstein1 mu nu + ENNReal.ofReal b) := by
    rw [← hemp]
    exact (wasserstein1_triangle_compact_mass _ _ _ S hS hmuE hmu hnuE).trans
      (add_le_add hsim' ((wasserstein1_triangle_compact_mass _ _ _ S hS
        hmu hnu hnuE).trans (add_le_add le_rfl hobs)))
  have hlowerReal : q ≤ a + (wasserstein1 mu nu).toReal + b := by
    rw [← add_assoc] at hlower
    have h := ENNReal.toReal_mono (by finiteness) hlower
    simpa only [ENNReal.toReal_add (by finiteness :
      ENNReal.ofReal a + wasserstein1 mu nu ≠ ⊤) ENNReal.ofReal_ne_top,
      ENNReal.toReal_add ENNReal.ofReal_ne_top hp,
      ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb,
      ENNReal.toReal_ofReal hq, ← add_assoc] using h
  obtain ⟨hrlo, hrhi⟩ := abs_le.mp hreg
  constructor
  · exact hupper.trans (ENNReal.ofReal_le_ofReal (by linarith))
  · apply (ENNReal.ofReal_le_iff_le_toReal hp).mpr
    linarith

/-- If [the source weights are nonnegative and sum to one](hyp:hmu) and
[the target weights are nonnegative and sum to one](hyp:hnu), then [the
finite matrix transport cost is nonnegative](goal). -/
-- @node: discreteW1_nonneg
lemma discreteW1_nonneg {n m d : ℕ}
    (x : Fin n → L1Vec d) (y : Fin m → L1Vec d)
    {mu : Fin n → ℝ} {nu : Fin m → ℝ}
    (hmu : mu ∈ probabilitySimplex n) (hnu : nu ∈ probabilitySimplex m) :
    0 ≤ discreteW1 x y mu nu := by
  unfold discreteW1
  have hne : (transportCost x y '' transportPlans mu nu).Nonempty :=
    ⟨_, _, product_mem_transportPlans hmu hnu, rfl⟩
  apply le_csInf hne
  rintro _ ⟨p, hp, rfl⟩
  exact transportCost_nonneg x y hp

/-- If [the sample size is positive](hyp:hm), [S is measurable](hyp:hS), and
[every sample observation belongs to S](hyp:hx), then [the empirical measure
assigns mass one to S](goal). -/
-- @node: empiricalMeasure_mass_one_of_mem
lemma empiricalMeasure_mass_one_of_mem {X : Type*} [MeasurableSpace X]
    {m : ℕ} (hm : 0 < m) (x : Fin m → X)
    (S : Set X) (hS : MeasurableSet S) (hx : ∀ i, x i ∈ S) :
    empiricalMeasure x S = 1 := by
  simp only [empiricalMeasure, Measure.smul_apply, Measure.coe_finsetSum,
    Finset.sum_apply, Measure.dirac_apply' _ hS, Set.indicator_of_mem (hx _),
    Pi.one_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hm.ne') (by simp)

/-- Suppose [the simulation sample size is positive](hyp:hn), [the observation
sample size is positive](hyp:hm), [S is compact](hyp:hS), [the simulation
population gives S full mass](hyp:hmu), [the observational population gives
S full mass](hyp:hnu), [all simulated observations lie in S](hyp:hx), and
[all observed observations lie in S](hyp:hy). If [the simulation tolerance a
is nonnegative](hyp:ha), [the observation tolerance b is nonnegative](hyp:hb),
[regularization is positive](hyp:hlam), [the simulation
Wasserstein sampling error is at most a](hyp:hsim), and [the observation
Wasserstein sampling error is at most b](hyp:hobs), then [the population
Wasserstein distance lies between the nonnegative parts of the joint
Sinkhorn divergence minus and plus a slack equal to a + b plus twice
regularization times one plus the logarithm of the product of sample sizes](goal). -/
-- @node: joint_sinkhorn_population_constraint_control
lemma joint_sinkhorn_population_constraint_control {v n m : ℕ}
    {kind : Fin v → NodeKind} (hn : 0 < n) (hm : 0 < m)
    (mu nu : Measure (Joint kind)) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (x : Fin n → Joint kind) (y : Fin m → Joint kind)
    (S : Set (Joint kind)) (hS : IsCompact S) (hmu : mu S = 1) (hnu : nu S = 1)
    (hx : ∀ i, x i ∈ S) (hy : ∀ j, y j ∈ S)
    (a b lam : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hlam : 0 < lam)
    (hsim : wasserstein1 mu (empiricalMeasure x) ≤ ENNReal.ofReal a)
    (hobs : wasserstein1 nu (empiricalMeasure y) ≤ ENNReal.ofReal b) :
    let e := sinkhornDivergence lam (fun i => jointVector (x i))
      (fun j => jointVector (y j)) (uniformWeights n) (uniformWeights m)
    let slack := a + b + 2 * (Real.log (m * n : ℕ) + 1) * lam
    wasserstein1 mu nu ≤ ENNReal.ofReal (e + slack) ∧
      ENNReal.ofReal (e - slack) ≤ wasserstein1 mu nu := by
  let := empiricalMeasure_probability hn x
  let := empiricalMeasure_probability hm y
  exact wasserstein1_two_sample_constraint_control mu nu (empiricalMeasure x)
    (empiricalMeasure y) S hS hmu hnu
    (empiricalMeasure_mass_one_of_mem hn x S hS.measurableSet hx)
    (empiricalMeasure_mass_one_of_mem hm y S hS.measurableSet hy)
    a b _ _ _ ha hb (discreteW1_nonneg _ _
      (uniformWeights_mem_probabilitySimplex hn) (uniformWeights_mem_probabilitySimplex hm))
    hsim hobs (joint_discreteW1_eq_empirical_wasserstein1 hn hm x y).symm
    (sinkhorn_approx hn hm _ _ _ _ (uniformWeights_mem_probabilitySimplex hn)
      (uniformWeights_mem_probabilitySimplex hm) lam hlam).2.2

/-- Suppose [the simulation sample size is positive](hyp:hn), [the observation
sample size is positive](hyp:hm), [S is compact](hyp:hS), [every admissible population law gives
S full mass](hyp:hpop), [the reference law gives S full mass](hyp:href), and
[almost surely all admissible simulated samples and the observed sample
lie in S](hyp:hsupport). For [nonnegative simulation tolerance a](hyp:ha),
[nonnegative observation tolerance b](hyp:hb), [positive regularization](hyp:hlam),
[a simulation failure allowance](hyp:failureSim), and [an observation failure
allowance](hyp:failureObs), assume [the measure of any admissible simulation
sampling error exceeding a is bounded by its allowance](hyp:hsim) and
[the measure of the reference sampling error exceeding b is bounded by its
allowance](hyp:hobs). Then [the measure of any admissible population
Wasserstein distance falling outside its joint Sinkhorn bounds is at most
the sum of the two failure allowances, using slack a + b plus twice
regularization times one plus the logarithm of the product of sample sizes](goal). -/
-- @node: joint_sinkhorn_constraint_failure_le
lemma joint_sinkhorn_constraint_failure_le {Omega A : Type*} [MeasurableSpace Omega]
    {v n m : ℕ} {kind : Fin v → NodeKind}
    (Q : Measure Omega) (hn : 0 < n) (hm : 0 < m)
    (admissible : A → Prop) (population : A → ProbabilityMeasure (Joint kind))
    (reference : ProbabilityMeasure (Joint kind))
    (x : A → Fin n → Omega → Joint kind) (y : Fin m → Omega → Joint kind)
    (S : Set (Joint kind)) (hS : IsCompact S)
    (hpop : ∀ r, admissible r → (population r : Measure (Joint kind)) S = 1)
    (href : (reference : Measure (Joint kind)) S = 1)
    (hsupport : ∀ᵐ w ∂Q, (∀ r, admissible r → ∀ i, x r i w ∈ S) ∧
      (∀ j, y j w ∈ S))
    (a b lam : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hlam : 0 < lam)
    (failureSim failureObs : ℝ≥0∞)
    (hsim : Q {w | ∃ r, admissible r ∧
      ¬ wasserstein1 (population r : Measure (Joint kind)) (empiricalMeasure (fun i => x r i w)) ≤
        ENNReal.ofReal a} ≤ failureSim)
    (hobs : Q {w | ¬ wasserstein1 (reference : Measure (Joint kind))
      (empiricalMeasure (fun j => y j w)) ≤
      ENNReal.ofReal b} ≤ failureObs) :
    Q {w | ∃ r, admissible r ∧
      let e := sinkhornDivergence lam (fun i => jointVector (x r i w))
        (fun j => jointVector (y j w)) (uniformWeights n) (uniformWeights m)
      let slack := a + b + 2 * (Real.log (m * n : ℕ) + 1) * lam
      ¬ (wasserstein1 (population r : Measure (Joint kind)) (reference : Measure (Joint kind)) ≤
        ENNReal.ofReal (e + slack) ∧ ENNReal.ofReal (e - slack) ≤
          wasserstein1 (population r : Measure (Joint kind)) (reference : Measure (Joint kind)))} ≤
      failureSim + failureObs := by
  classical
  apply le_trans (measure_mono_ae (t :=
    {w | ∃ r, admissible r ∧
      ¬ wasserstein1 (population r : Measure (Joint kind)) (empiricalMeasure (fun i => x r i w)) ≤
        ENNReal.ofReal a} ∪
    {w | ¬ wasserstein1 (reference : Measure (Joint kind)) (empiricalMeasure (fun j => y j w)) ≤
      ENNReal.ofReal b}) ?_)
    ((measure_union_le _ _).trans (add_le_add hsim hobs))
  filter_upwards [hsupport] with w hw
  intro hbad
  by_contra hgood
  have hsimGood : ∀ r, admissible r →
      wasserstein1 (population r : Measure (Joint kind)) (empiricalMeasure (fun i => x r i w)) ≤
        ENNReal.ofReal a := by
    intro r hr
    by_contra h
    exact hgood (Or.inl ⟨r, hr, h⟩)
  have hobsGood : wasserstein1 (reference : Measure (Joint kind))
      (empiricalMeasure (fun j => y j w)) ≤
      ENNReal.ofReal b := by
    by_contra h
    exact hgood (Or.inr h)
  obtain ⟨r, hr, hfail⟩ := hbad
  exact hfail (joint_sinkhorn_population_constraint_control hn hm
    (population r : Measure (Joint kind)) (reference : Measure (Joint kind))
    (fun i => x r i w) (fun j => y j w)
    S hS (hpop r hr) href (hw.1 r hr) hw.2 a b lam ha hb hlam
    (hsimGood r hr) hobsGood)

/-- [The observational law of a Euclidean structural causal model is a
probability measure](goal). -/
-- @node: observationalLaw_probability
lemma observationalLaw_probability {v b : ℕ} {kind : Fin v → NodeKind}
    {dims : Fin b → ℕ} (M : EuclideanSCM kind dims) :
    IsProbabilityMeasure (observationalLaw M) := by
  let := M.probability
  change IsProbabilityMeasure (M.latentLaw.map (intervenedEval M (noIntervention kind).val))
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- Suppose [the observed sample size is positive](hyp:hn) and [the simulation
sample size is positive](hyp:hm), with [variable bound K](hyp:K) and [regularity bound L](hyp:L).
Assume [S is compact](hyp:hS), [every candidate satisfying these bounds has
observational mass one on S](hyp:hpop), [the reference model has observational
mass one on S](hyp:href), and [almost surely every such candidate's simulated
observations and all reference observations lie in S](hyp:hsupport). For
[nonnegative simulation tolerance a](hyp:ha), [nonnegative observation
tolerance bObs](hyp:hb), [positive regularization](hyp:hlam), [a simulation
failure allowance](hyp:failureSim), and [an observation failure allowance](hyp:failureObs),
assume [the measure of any restricted candidate's simulation Wasserstein
error exceeding a is bounded by its allowance](hyp:hsim) and [the measure
of the reference Wasserstein sampling error exceeding bObs is bounded by
its allowance](hyp:hobs). Then [the measure of any restricted candidate's
population Wasserstein distance falling outside the empirical Sinkhorn
bounds is at most the sum of the allowances, using slack a + bObs plus
twice regularization times one plus the logarithm of the product of sample
sizes](goal). -/
-- @node: ncm_sinkhorn_constraint_failure_le
lemma ncm_sinkhorn_constraint_failure_le
    {Omega : Type*} [MeasurableSpace Omega]
    {v b n m : ℕ} {kind : Fin v → NodeKind} {dims : Fin b → ℕ}
    {dag : Causalean.Graph.DAG (Fin v)} {G : SimpleGraph (Fin v)}
    {C : Fin b → Set (Fin v)} {counts : Fin b → ℕ}
    (Q : Measure Omega) (hn : 0 < n) (hm : 0 < m)
    (M : EuclideanSCM kind dims)
    (F0 : StructuralClass kind dims dag C) (F1 : GeneratorClass dims counts)
    (K L : ℝ≥0) (sample : Fin n → Omega → Joint kind)
    (draws : Fin m → Omega → SimulationInput kind counts)
    (S : Set (Joint kind)) (hS : IsCompact S)
    (hpop : ∀ R : NCMIn kind dims dag G C counts F0 F1,
      restrictedCandidate K L R → (observationalLaw R.canonical.toEuclideanSCM) S = 1)
    (href : observationalLaw M S = 1)
    (hsupport : ∀ᵐ w ∂Q,
      (∀ R : NCMIn kind dims dag G C counts F0 F1,
        restrictedCandidate K L R → ∀ i, ncmEval R (draws i w) ∈ S) ∧
      (∀ j, sample j w ∈ S))
    (a bObs lam : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ bObs) (hlam : 0 < lam)
    (failureSim failureObs : ℝ≥0∞)
    (hsim : Q {w | ∃ R : NCMIn kind dims dag G C counts F0 F1,
      restrictedCandidate K L R ∧
      ¬ wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
        (empiricalMeasure (fun i => ncmEval R (draws i w))) ≤ ENNReal.ofReal a} ≤ failureSim)
    (hobs : Q {w | ¬ wasserstein1 (observationalLaw M)
      (empiricalMeasure (fun j => sample j w)) ≤ ENNReal.ofReal bObs} ≤ failureObs) :
    Q {w | ∃ R : NCMIn kind dims dag G C counts F0 F1,
      restrictedCandidate K L R ∧
      let e := sinkhornDivergence lam (fun i => jointVector (ncmEval R (draws i w)))
        (fun j => jointVector (sample j w)) (uniformWeights m) (uniformWeights n)
      let slack := a + bObs + 2 * (Real.log (n * m : ℕ) + 1) * lam
      ¬ (wasserstein1 (observationalLaw R.canonical.toEuclideanSCM) (observationalLaw M) ≤
        ENNReal.ofReal (e + slack) ∧ ENNReal.ofReal (e - slack) ≤
          wasserstein1 (observationalLaw R.canonical.toEuclideanSCM) (observationalLaw M))} ≤
      failureSim + failureObs := by
  exact joint_sinkhorn_constraint_failure_le Q hm hn (restrictedCandidate K L)
    (fun R => ⟨observationalLaw R.canonical.toEuclideanSCM,
      observationalLaw_probability R.canonical.toEuclideanSCM⟩)
    ⟨observationalLaw M, observationalLaw_probability M⟩
    (fun R i w => ncmEval R (draws i w)) sample S hS hpop href hsupport
    a bObs lam ha hb hlam failureSim failureObs hsim hobs

/-- Fix [a variable bound K](hyp:K), [a regularity bound L](hyp:L),
[positive simulation sample sizes at every stage](hyp:hm), [observed samples
of size equal to the stage](hyp:sample), and [simulation inputs of the
stage-specific sizes](hyp:draws). Suppose [S is compact](hyp:hS), [all
restricted candidate laws give S full mass at every stage](hyp:hpop),
[the reference law gives S full mass](hyp:href), and [at each stage all
restricted simulations and observations lie in S almost surely](hyp:hsupport).
Assume [nonnegative simulation tolerances](hyp:ha), [nonnegative observation
tolerances](hyp:hb), [positive regularization parameters](hyp:hlam),
[a nonnegative simulation tail constant](hyp:hBs), [a nonnegative observation
tail constant](hyp:hBo), [eventual uniform simulation-error failure bounds
given by the simulation constant divided by the squared stage](hyp:hsim),
and [eventual observation-error failure bounds given by the observation
constant divided by the squared stage](hyp:hobs). Then [almost surely,
at all sufficiently large stages, every restricted candidate's population
Wasserstein distance lies within its empirical Sinkhorn bounds, with slack
equal to the two tolerances plus twice regularization times one plus the
logarithm of the product of sample sizes](goal). -/
-- @node: ncm_sinkhorn_constraint_ae_eventually
lemma ncm_sinkhorn_constraint_ae_eventually
    {Omega : Type*} [MeasurableSpace Omega]
    {v b : ℕ} {kind : Fin v → NodeKind} {dims : Fin b → ℕ}
    {dag : Causalean.Graph.DAG (Fin v)} {G : SimpleGraph (Fin v)}
    {C : Fin b → Set (Fin v)} {counts : Fin b → ℕ}
    (Q : Measure Omega) (M : EuclideanSCM kind dims)
    (F0 : ℕ → StructuralClass kind dims dag C) (F1 : ℕ → GeneratorClass dims counts)
    (K L : ℝ≥0) (m : ℕ → ℕ) (hm : ∀ r, 0 < m r)
    (sample : ∀ r, Fin r → Omega → Joint kind)
    (draws : ∀ r, Fin (m r) → Omega → SimulationInput kind counts)
    (S : Set (Joint kind)) (hS : IsCompact S)
    (hpop : ∀ r (R : NCMIn kind dims dag G C counts (F0 r) (F1 r)),
      restrictedCandidate K L R → (observationalLaw R.canonical.toEuclideanSCM) S = 1)
    (href : observationalLaw M S = 1)
    (hsupport : ∀ r, ∀ᵐ w ∂Q,
      (∀ R : NCMIn kind dims dag G C counts (F0 r) (F1 r),
        restrictedCandidate K L R → ∀ i, ncmEval R (draws r i w) ∈ S) ∧
      (∀ j, sample r j w ∈ S))
    (a bObs lam : ℕ → ℝ) (ha : ∀ r, 0 ≤ a r) (hb : ∀ r, 0 ≤ bObs r)
    (hlam : ∀ r, 0 < lam r) (Bsim Bobs : ℝ) (hBs : 0 ≤ Bsim) (hBo : 0 ≤ Bobs)
    (hsim : ∀ᶠ r in atTop,
      Q {w | ∃ R : NCMIn kind dims dag G C counts (F0 r) (F1 r),
        restrictedCandidate K L R ∧
        ¬ wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
          (empiricalMeasure (fun i => ncmEval R (draws r i w))) ≤ ENNReal.ofReal (a r)} ≤
        ENNReal.ofReal (Bsim * (r : ℝ)^(-(2 : ℤ))))
    (hobs : ∀ᶠ r in atTop,
      Q {w | ¬ wasserstein1 (observationalLaw M)
        (empiricalMeasure (fun j => sample r j w)) ≤ ENNReal.ofReal (bObs r)} ≤
        ENNReal.ofReal (Bobs * (r : ℝ)^(-(2 : ℤ)))) :
    ∀ᵐ w ∂Q, ∀ᶠ r in atTop,
      ∀ R : NCMIn kind dims dag G C counts (F0 r) (F1 r), restrictedCandidate K L R →
        let e := sinkhornDivergence (lam r) (fun i => jointVector (ncmEval R (draws r i w)))
          (fun j => jointVector (sample r j w)) (uniformWeights (m r)) (uniformWeights r)
        let slack := a r + bObs r + 2 * (Real.log (r * m r : ℕ) + 1) * lam r
        wasserstein1 (observationalLaw R.canonical.toEuclideanSCM) (observationalLaw M) ≤
          ENNReal.ofReal (e + slack) ∧ ENNReal.ofReal (e - slack) ≤
            wasserstein1 (observationalLaw R.canonical.toEuclideanSCM) (observationalLaw M) := by
  apply estimation_ae_eventually_uniform_constraint_control Q
    (fun _ => restrictedCandidate K L)
    (fun _ R => wasserstein1 (observationalLaw R.canonical.toEuclideanSCM) (observationalLaw M))
    (fun r R w => sinkhornDivergence (lam r)
      (fun i => jointVector (ncmEval R (draws r i w))) (fun j => jointVector (sample r j w))
      (uniformWeights (m r)) (uniformWeights r))
    (fun r => a r + bObs r + 2 * (Real.log (r * m r : ℕ) + 1) * lam r) (Bsim + Bobs)
  filter_upwards [hsim, hobs, eventually_gt_atTop (0 : ℕ)] with r hs ho hr
  have h := ncm_sinkhorn_constraint_failure_le Q hr (hm r) M (F0 r) (F1 r) K L
    (sample r) (draws r) S hS (hpop r) href (hsupport r) (a r) (bObs r) (lam r)
    (ha r) (hb r) (hlam r) _ _ hs ho
  apply h.trans
  rw [← ENNReal.ofReal_add (mul_nonneg hBs (by positivity)) (mul_nonneg hBo (by positivity)),
    ← add_mul]

end
end Papers.TbsNeuralCausalPi
