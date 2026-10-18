module
public import Papers.TbsNeuralCausalPi.Helpers.DeepFirstBlocks
public import Papers.TbsNeuralCausalPi.TWideNn
/-! # Component transport and mixture assembly for deep generators -/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped ENNReal NNReal

/-- For [a probability law](hyp:P), [component sets](hyp:S), and [a Lipschitz bound](hyp:L),
suppose [the sets are its finite support components](hyp:hsupp) and
[admit Lipschitz cube charts](hyp:hcharts). Given [chosen charts](hyp:f) that
[satisfy that Lipschitz bound](hyp:hf), [a three-part generator](hyp:Q) whose
[first blocks map the unit interval into the chart cubes](hyp:hcube), and
[a box radius](hyp:K) such that [all components lie in that box](hyp:hbox) and
[all second-block outputs lie there](hyp:hbounded), take [two error constants](hyp:A1,A2)
that [are nonnegative](hyp:hA1,hA2). If [positive-dimensional first-block pullback errors
are bounded by the first constant times the first depth rate](hyp:hfirst) and
[second-block uniform chart errors are bounded by the second constant times the second
depth rate, or zero when all charts have dimension zero](hyp:hsecond),
[each conditional component law is within Wasserstein distance of its composed
generator law at most the Lipschitz bound times the first constant plus the second
constant, multiplied by the sum of the depth powers with exponent minus two over
the maximum of one and the largest chart dimension; the bound is zero when all
charts have dimension zero](goal). -/
-- @node: deep_generator_component_errors_le
lemma deep_generator_component_errors_le {d N W1 L1 W2 L2 : ℕ}
    {dC : Fin N → ℕ} {tau : ℝ}
    (P : ProbabilityMeasure (L1Vec d)) (S : Fin N → Set (L1Vec d))
    (L : ℝ≥0) (hsupp : SupportFiniteComponents (P : Measure _) S)
    (hcharts : ComponentsLipschitzHomeomorphic S dC L)
    (f : ∀ i, homeoClass (unitCube (dC i)) (S i))
    (hf : ∀ i, LipschitzWith L (f i))
    (Q : ThreePartGenerator N d dC W1 L1 W2 L2 tau)
    (hcube : ∀ i, Set.MapsTo (Q.g1 i).eval (unitCube 1) (unitCube (dC i)))
    (K : ℝ) (hbox : ∀ i, S i ⊆ boundedCube d K)
    (hbounded : ∀ i x, (Q.g2 i).eval x ∈ boundedCube d K)
    (A1 A2 : ℝ) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2)
    (hfirst : ∀ i, 0 < dC i → wasserstein1
      ((ProbabilityTheory.cond (P : Measure _) (S i)).map (chartInverse (f i)))
      ((uniformCubeLaw 1).map (Q.g1 i).eval) ≤
        ENNReal.ofReal (A1 * (L1 : ℝ) ^ (-(2 : ℝ) / max 1 (Finset.univ.sup dC))))
    (hsecond : ∀ i, ∀ x : unitCube (dC i), ‖((f i) x).val-(Q.g2 i).eval x.val‖ ≤
      if 0 < Finset.univ.sup dC then
        A2 * (L2 : ℝ) ^ (-(2 : ℝ) / max 1 (Finset.univ.sup dC)) else 0) :
    ∀ i, wasserstein1 (ProbabilityTheory.cond (P : Measure _) (S i))
      ((uniformCubeLaw 1).map ((Q.g2 i).eval ∘ (Q.g1 i).eval)) ≤
      ENNReal.ofReal (((L : ℝ) * A1 + A2) *
        (if 0 < Finset.univ.sup dC then
          (L1 : ℝ) ^ (-(2 : ℝ) / max 1 (Finset.univ.sup dC)) +
          (L2 : ℝ) ^ (-(2 : ℝ) / max 1 (Finset.univ.sup dC)) else 0)) := by
  intro i
  let mu : ProbabilityMeasure (L1Vec d) :=
    ⟨ProbabilityTheory.cond (P : Measure _) (S i),
      support_component_cond_probability P hsupp hcharts i⟩
  have hm : (mu : Measure _) (S i) = 1 :=
    ProbabilityTheory.cond_apply_self
      (ne_of_gt (support_component_mass_pos P hsupp hcharts i)) (measure_ne_top _ _)
  have ht := wide_component_transport_le mu (f i) (component_isCompact hcharts i)
    hm L (hf i) (Q.g1 i) (Q.g2 i) (hcube i) K (hbox i) (hbounded i)
    _ (hsecond i)
  have hinput : wasserstein1 ((mu : Measure _).map (chartInverse (f i)))
      ((uniformCubeLaw 1).map (Q.g1 i).eval) ≤
      ENNReal.ofReal (if 0 < Finset.univ.sup dC then
        A1 * (L1 : ℝ) ^ (-(2 : ℝ) / max 1 (Finset.univ.sup dC)) else 0) := by
    by_cases hi : 0 < dC i
    · have hsup : 0 < Finset.univ.sup dC :=
        hi.trans_le (Finset.le_sup (Finset.mem_univ i))
      rw [if_pos hsup]
      exact hfirst i hi
    · have hzero : dC i = 0 := by omega
      let : Subsingleton (L1Vec (dC i)) := hzero ▸ inferInstanceAs (Subsingleton (L1Vec 0))
      let : IsProbabilityMeasure (uniformCubeLaw 1) := uniformCubeLaw_probability 1
      let : IsProbabilityMeasure ((mu : Measure _).map (chartInverse (f i))) :=
        Measure.isProbabilityMeasure_map (by fun_prop)
      let : IsProbabilityMeasure ((uniformCubeLaw 1).map (Q.g1 i).eval) :=
        Measure.isProbabilityMeasure_map (by fun_prop)
      rw [wasserstein_subsingleton_eq_zero]
      exact bot_le
  have hmul := mul_le_mul_right hinput (L : ℝ≥0∞)
  refine ht.trans ((add_le_add hmul le_rfl).trans ?_)
  by_cases hsup : 0 < Finset.univ.sup dC
  · simp only [if_pos hsup]
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul L.coe_nonneg,
      ← ENNReal.ofReal_add (mul_nonneg L.coe_nonneg
        (mul_nonneg hA1 (Real.rpow_nonneg (Nat.cast_nonneg L1) _)))
        (mul_nonneg hA2 (Real.rpow_nonneg (Nat.cast_nonneg L2) _))]
    apply ENNReal.ofReal_le_ofReal
    have hcross1 := mul_nonneg (mul_nonneg L.coe_nonneg hA1)
      (Real.rpow_nonneg (Nat.cast_nonneg L2) (-(2 : ℝ) / max 1 (Finset.univ.sup dC)))
    have hcross2 := mul_nonneg hA2
      (Real.rpow_nonneg (Nat.cast_nonneg L1) (-(2 : ℝ) / max 1 (Finset.univ.sup dC)))
    nlinarith only [hcross1, hcross2]
  · simp [hsup]

/-- For [a probability law](hyp:P), [component sets](hyp:S), [chart dimensions](hyp:dC),
and [a Lipschitz bound](hyp:L), assume [the sets are its finite support components](hyp:hsupp),
[they admit Lipschitz cube charts](hyp:hcharts), [their conditional laws dominate cube
volume through such charts](hyp:hdom), and [coordinate approximation is available](hyp:hgate).
[There exist a positive second width factor, error constant, and box radius such that
any two depths at least four and any positive temperature admit a three-part generator
with first width twelve times the maximum of one and the largest chart dimension and
second width the chosen factor times the ambient dimension times that maximum, exact
component masses, cube-valued first blocks, bounded second blocks, and exact component
membership for zero-dimensional charts; its component mixture approximates the target
law with Wasserstein error at most the constant times the sum of the two depth powers
with exponent minus two over that maximum, or zero if every chart dimension is zero](goal). -/
-- @node: exists_deep_relu_generator_mixture_bound
lemma exists_deep_relu_generator_mixture_bound {d N : ℕ}
    (P : ProbabilityMeasure (L1Vec d)) (S : Fin N → Set (L1Vec d))
    (dC : Fin N → ℕ) (L : ℝ≥0)
    (hsupp : SupportFiniteComponents (P : Measure _) S)
    (hcharts : ComponentsLipschitzHomeomorphic S dC L)
    (hdom : ∀ i, LowerBoundDomination (d := dC i)
      (ProbabilityTheory.cond (P : Measure _) (S i)) (S i) L)
    (hgate : YarotskyCoordinateApprox) :
    ∃ c2 : ℕ, 0 < c2 ∧ ∃ A K : ℝ, 0 < A ∧ 0 < K ∧
      ∀ L1 L2 : ℕ, 4 ≤ L1 → 4 ≤ L2 → ∀ tau : ℝ, 0 < tau →
        ∃ Q : ThreePartGenerator N d dC (12 * max 1 (Finset.univ.sup dC)) L1
            (c2 * d * max 1 (Finset.univ.sup dC)) L2 tau,
          (∀ i, Q.p i = ((P : Measure _) (S i)).toReal) ∧
          (∀ i, Set.MapsTo (Q.g1 i).eval (unitCube 1) (unitCube (dC i))) ∧
          (∀ i x, (Q.g2 i).eval x ∈ boundedCube d K) ∧
          (∀ i, dC i = 0 → Set.MapsTo (Q.g2 i).eval (unitCube (dC i)) (S i)) ∧
          wasserstein1 (P : Measure _) (∑ i, ENNReal.ofReal (Q.p i) •
            (uniformCubeLaw 1).map ((Q.g2 i).eval ∘ (Q.g1 i).eval)) ≤
            ENNReal.ofReal (A * (if 0 < Finset.univ.sup dC then
              (L1 : ℝ) ^ (-(2 : ℝ) / max 1 (Finset.univ.sup dC)) +
              (L2 : ℝ) ^ (-(2 : ℝ) / max 1 (Finset.univ.sup dC)) else 0)) := by
  classical
  choose f Cf hdomAt using hdom
  have hf (i : Fin N) : LipschitzWith L (f i) := (hdomAt i).2.2.2.1
  obtain ⟨K, hK, hbox⟩ := exists_component_bounding_box hcharts
  obtain ⟨A1, hA1, hfirst⟩ :=
    exists_deep_relu_first_blocks P S dC L hsupp hcharts f Cf hdomAt hgate
  obtain ⟨c2, hc2, A2, hA2, hsecond⟩ :=
    exists_wide_relu_second_blocks f L hf K hK.le hbox hgate
  have hp := support_component_real_masses P hsupp hcharts
  refine ⟨c2, hc2, (L : ℝ) * A1 + A2, K, by positivity, hK, ?_⟩
  intro L1 L2 hL1 hL2 tau htau
  obtain ⟨g1, hcube, hgen⟩ := hfirst L1 hL1
  obtain ⟨g2, hbounded, hzero, herr⟩ := hsecond L2 hL2
  let Q : ThreePartGenerator N d dC (12 * max 1 (Finset.univ.sup dC)) L1
      (c2 * d * max 1 (Finset.univ.sup dC)) L2 tau :=
    { g1 := g1, g2 := g2, p := fun i => ((P : Measure _) (S i)).toReal,
      weights := ⟨fun i => (hp.1 i).le, hp.2⟩,
      positiveWeights := hp.1, temperature := htau }
  refine ⟨Q, fun i => rfl, hcube, hbounded, hzero, ?_⟩
  exact wide_generator_mixture_error_le P S hsupp hcharts Q (fun i => rfl) K hbounded _
    (deep_generator_component_errors_le P S L hsupp hcharts f hf Q hcube K hbox hbounded
      A1 A2 hA1.le hA2.le hgen herr)


/-- Given [a probability law](hyp:P), [component sets](hyp:S), [chart dimensions](hyp:dC),
and [a Lipschitz bound](hyp:L), assume [the sets form its finite support components](hyp:hsupp),
[Lipschitz cube charts exist](hyp:hcharts), [each conditional law dominates cube volume
through such a chart](hyp:hdom), and [coordinate approximation is available](hyp:hgate).
[There are positive error and box constants such that every two depths at least four
and positive temperature admit a generator with the universal first width factor times
the maximum of one and the largest chart dimension, and the universal second width
factor times the ambient dimension times that maximum, exact component masses,
cube-valued first blocks, bounded second blocks, and component-valued zero-dimensional
second blocks; its component mixture has Wasserstein error bounded by the error constant
times the two depth powers with exponent minus two over that maximum, or zero when
all charts have dimension zero](goal). -/
lemma exists_deep_relu_generator_mixture_bound_explicit {d N : ℕ}
    (P : ProbabilityMeasure (L1Vec d)) (S : Fin N → Set (L1Vec d))
    (dC : Fin N → ℕ) (L : ℝ≥0)
    (hsupp : SupportFiniteComponents (P : Measure _) S)
    (hcharts : ComponentsLipschitzHomeomorphic S dC L)
    (hdom : ∀ i, LowerBoundDomination (d := dC i)
      (ProbabilityTheory.cond (P : Measure _) (S i)) (S i) L)
    (hgate : YarotskyCoordinateApprox) :
    ∃ A K : ℝ, 0 < A ∧ 0 < K ∧
      ∀ L1 L2 : ℕ, 4 ≤ L1 → 4 ≤ L2 → ∀ tau : ℝ, 0 < tau →
        ∃ Q : ThreePartGenerator N d dC (deepFirstWidthFactor * max 1 (Finset.univ.sup dC)) L1
            (deepSecondWidthFactor * d * max 1 (Finset.univ.sup dC)) L2 tau,
          (∀ i, Q.p i = ((P : Measure _) (S i)).toReal) ∧
          (∀ i, Set.MapsTo (Q.g1 i).eval (unitCube 1) (unitCube (dC i))) ∧
          (∀ i x, (Q.g2 i).eval x ∈ boundedCube d K) ∧
          (∀ i, dC i = 0 → Set.MapsTo (Q.g2 i).eval (unitCube (dC i)) (S i)) ∧
          wasserstein1 (P : Measure _) (∑ i, ENNReal.ofReal (Q.p i) •
            (uniformCubeLaw 1).map ((Q.g2 i).eval ∘ (Q.g1 i).eval)) ≤
            ENNReal.ofReal (A * (if 0 < Finset.univ.sup dC then
              (L1 : ℝ) ^ (-(2 : ℝ) / max 1 (Finset.univ.sup dC)) +
              (L2 : ℝ) ^ (-(2 : ℝ) / max 1 (Finset.univ.sup dC)) else 0)) := by
  classical
  choose f Cf hdomAt using hdom
  have hf (i : Fin N) : LipschitzWith L (f i) := (hdomAt i).2.2.2.1
  obtain ⟨K, hK, hbox⟩ := exists_component_bounding_box hcharts
  obtain ⟨A1, hA1, hfirst⟩ :=
    exists_deep_relu_first_blocks P S dC L hsupp hcharts f Cf hdomAt hgate
  obtain ⟨A2, hA2, hsecond⟩ :=
    exists_wide_relu_second_blocks_explicit f L hf K hK.le hbox hgate
  have hp := support_component_real_masses P hsupp hcharts
  refine ⟨(L : ℝ) * A1 + A2, K, by positivity, hK, ?_⟩
  intro L1 L2 hL1 hL2 tau htau
  obtain ⟨g1, hcube, hgen⟩ := hfirst L1 hL1
  obtain ⟨g2, hbounded, hzero, herr⟩ := hsecond L2 hL2
  let Q : ThreePartGenerator N d dC (deepFirstWidthFactor * max 1 (Finset.univ.sup dC)) L1
      (deepSecondWidthFactor * d * max 1 (Finset.univ.sup dC)) L2 tau :=
    { g1 := g1, g2 := g2, p := fun i => ((P : Measure _) (S i)).toReal,
      weights := ⟨fun i => (hp.1 i).le, hp.2⟩,
      positiveWeights := hp.1, temperature := htau }
  refine ⟨Q, fun i => rfl, hcube, hbounded, hzero, ?_⟩
  exact wide_generator_mixture_error_le P S hsupp hcharts Q (fun i => rfl) K hbounded _
    (deep_generator_component_errors_le P S L hsupp hcharts f hf Q hcube K hbox hbounded
      A1 A2 hA1.le hA2.le hgen herr)

end Papers.TbsNeuralCausalPi
