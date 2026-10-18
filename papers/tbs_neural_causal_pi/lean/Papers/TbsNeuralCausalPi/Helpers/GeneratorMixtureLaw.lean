module
public import Papers.TbsNeuralCausalPi.Helpers.GeneratorMixing
public import Papers.TbsNeuralCausalPi.Helpers.GumbelMax
public import Papers.TbsNeuralCausalPi.Helpers.WassersteinSpace
/-! # The law of an independently selected generator block -/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped ENNReal

-- @node: independent_selector_map_eq_mixture
/-- If [each component output is measurable in its input](hyp:hV) and [the
finite-valued selector is measurable in its input](hyp:hs), [the output measure
under the product input measure is the sum of the component output measures,
each scaled by the selector-input measure of choosing that component](goal). -/
lemma independent_selector_map_eq_mixture
    {Ω Ξ X : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace X]
    {n : ℕ} (mu : Measure Ω) (nu : Measure Ξ) [SFinite mu] [SFinite nu]
    (V : Ω → Fin n → X) (hV : ∀ i, Measurable (fun x => V x i))
    (s : Ξ → Fin n) (hs : Measurable s) :
    (mu.prod nu).map (fun z => V z.1 (s z.2)) =
      ∑ i, nu (s ⁻¹' {i}) • mu.map (fun x => V x i) := by
  have hselect : Measurable (fun z : Ω × Fin n => V z.1 z.2) := by
    exact measurable_from_prod_countable_left (fun i => hV i)
  calc
    _ = (mu.prod (nu.map s)).map (fun z => V z.1 z.2) := by
      have hm := Measure.map_prod_map mu nu measurable_id hs
      rw [Measure.map_id] at hm
      rw [hm, Measure.map_map hselect (measurable_id.prodMap hs)]
      rfl
    _ = _ := by
      rw [Measure.map_eq_sum nu s hs, Measure.prod_sum_right,
        Measure.map_sum hselect.aemeasurable, Measure.sum_fintype]
      apply Finset.sum_congr rfl
      intro i _
      rw [Measure.prod_smul_right, Measure.map_smul, Measure.prod_dirac,
        Measure.map_map hselect measurable_prodMk_right]
      rfl

-- @node: gumbelSoftmaxMix_zero_eq_selected
/-- [At zero temperature, the mixture output equals the component at the first
index maximizing log weight plus Gumbel score, using the given default index
if no maximizer is returned](goal). -/
lemma gumbelSoftmaxMix_zero_eq_selected {n d : ℕ} (j0 : Fin n)
    (V : Fin n → L1Vec d) (p G : Fin n → ℝ) :
    gumbelSoftmaxMix V p 0 G =
      V ((firstArgmax (fun k => extendedLog (p k) + (G k : EReal))).getD j0) := by
  obtain ⟨j, hj⟩ := firstArgmax_exists (Nat.zero_lt_of_lt j0.isLt)
    (fun k => extendedLog (p k) + (G k : EReal))
  simp [gumbelSoftmaxMix_eq_sum, hardWeights_eq_oneHot p G j hj, hj]

-- @node: hard_selector_map_eq_mixture
/-- If [each component output is measurable in its input](hyp:hV), [the
zero-temperature mixture's output measure under independent component and
score inputs is the sum of the component output measures, each scaled by the
score-input measure that its index is the first maximizer of log weight plus
score](goal). -/
lemma hard_selector_map_eq_mixture
    {Ω : Type*} [MeasurableSpace Ω] {n d : ℕ}
    (mu : Measure Ω) (nu : Measure (Fin n → ℝ)) [SFinite mu] [SFinite nu]
    (j0 : Fin n) (V : Ω → Fin n → L1Vec d)
    (hV : ∀ i, Measurable (fun x => V x i)) (p : Fin n → ℝ) :
    (mu.prod nu).map (fun z => gumbelSoftmaxMix (V z.1) p 0 z.2) =
      ∑ i, nu {G | firstArgmax (fun k => extendedLog (p k) + (G k : EReal)) = some i} •
        mu.map (fun x => V x i) := by
  let s := fun G : Fin n → ℝ =>
    (firstArgmax (fun k => extendedLog (p k) + (G k : EReal))).getD j0
  have hs : Measurable s := by
    apply firstArgmax_getD_measurable
    intro k
    fun_prop
  have heq : (fun z : Ω × (Fin n → ℝ) => gumbelSoftmaxMix (V z.1) p 0 z.2) =
      fun z => V z.1 (s z.2) := by
    funext z
    exact gumbelSoftmaxMix_zero_eq_selected j0 (V z.1) p z.2
  rw [heq, independent_selector_map_eq_mixture mu nu V hV s hs]
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  ext G
  obtain ⟨j, hj⟩ := firstArgmax_exists (Nat.zero_lt_of_lt j0.isLt)
    (fun k => extendedLog (p k) + (G k : EReal))
  simp [s, hj]

-- @node: uniform_inputs_scalar_cube_marginal
/-- [Any coordinate of an array of independent uniform draws on the unit
interval, viewed as a one-dimensional vector, has the uniform law on the
one-dimensional unit cube](goal). -/
lemma uniform_inputs_scalar_cube_marginal {n : ℕ} (i : Fin n) :
    (Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1))).map
      (fun u => WithLp.toLp 1 (fun _ : Fin 1 => u i)) = uniformCubeLaw 1 := by
  let m := volume.restrict (Set.Icc (0 : ℝ) 1)
  let : IsProbabilityMeasure m := ⟨by simp [m]⟩
  have hleft := (measurePreserving_eval (fun _ : Fin n => m) i).map_eq
  have hright := (measurePreserving_eval (fun _ : Fin 1 => m) (0 : Fin 1)).map_eq
  have hconst : Measurable (fun x : ℝ => WithLp.toLp 1 (fun _ : Fin 1 => x)) := by
    fun_prop
  have hL := congrArg (fun μ : Measure ℝ => μ.map (fun x =>
    WithLp.toLp 1 (fun _ : Fin 1 => x))) hleft
  have hR := congrArg (fun μ : Measure ℝ => μ.map (fun x =>
    WithLp.toLp 1 (fun _ : Fin 1 => x))) hright
  rw [Measure.map_map hconst (by fun_prop)] at hL hR
  change (Measure.pi (fun _ : Fin n => m)).map
    (fun u => WithLp.toLp 1 (fun _ : Fin 1 => u i)) = _
  change (Measure.pi (fun _ : Fin n => m)).map
    (fun u => WithLp.toLp 1 (fun _ : Fin 1 => u i)) = _ at hL
  change (Measure.pi (fun _ : Fin 1 => m)).map
    (fun u => WithLp.toLp 1 (fun _ : Fin 1 => u 0)) = _ at hR
  rw [hL, ← hR]
  unfold uniformCubeLaw
  congr 1
  funext u
  congr 1
  funext j
  exact congrArg u (Subsingleton.elim _ _)

-- @node: gumbel_hard_mix_map_eq_mixture
/-- If [there is at least one component](hyp:hn), [each component output is
measurable in its input](hyp:hV), [all selector weights are strictly
positive](hyp:hp), and [the weights sum to one](hyp:hsum), [the output measure of
the hard mixture under independent component input and Gumbel noise equals the
sum of the component output measures scaled by their selector weights](goal). -/
lemma gumbel_hard_mix_map_eq_mixture
    {Ω : Type*} [MeasurableSpace Ω] {n d : ℕ}
    (mu : Measure Ω) [SFinite mu] (hn : 0 < n)
    (V : Ω → Fin n → L1Vec d) (hV : ∀ i, Measurable (fun x => V x i))
    (p : Fin n → ℝ) (hp : ∀ j, 0 < p j) (hsum : ∑ j, p j = 1) :
    (mu.prod (gumbelInputs n)).map (fun z => gumbelSoftmaxMix (V z.1) p 0 z.2) =
      ∑ i, ENNReal.ofReal (p i) • mu.map (fun x => V x i) := by
  let := gumbelInputs_probability n
  rw [hard_selector_map_eq_mixture mu (gumbelInputs n) ⟨0, hn⟩ V hV p]
  simp_rw [gumbel_firstArgmax_probability p hp hsum]

-- @node: generator_hard_law_eq_mixture
/-- If [the generator has at least one component](hyp:hn), [its hard-selector
output law under the declared independent uniform and Gumbel inputs is the
mixture, weighted by the generator's selector probabilities, of the component
laws obtained by passing a uniform scalar input through each component's two
successive networks](goal). -/
lemma generator_hard_law_eq_mixture {n d : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (Q : ThreePartGenerator n d dC W1 L1 W2 L2 tau) (hn : 0 < n) :
    (generatorInputLaw n).map (fun z => gumbelSoftmaxMix
      (fun i => (Q.g2 i).eval ((Q.g1 i).eval (WithLp.toLp 1 (fun _ => z.1 i))))
      Q.p 0 z.2) =
      ∑ i, ENNReal.ofReal (Q.p i) •
        (uniformCubeLaw 1).map ((Q.g2 i).eval ∘ (Q.g1 i).eval) := by
  let m := volume.restrict (Set.Icc (0 : ℝ) 1)
  let : IsProbabilityMeasure m := ⟨by simp [m]⟩
  rw [generatorInputLaw, gumbel_hard_mix_map_eq_mixture
    (Measure.pi (fun _ : Fin n => m)) hn
    (fun (u : Fin n → ℝ) i =>
      (Q.g2 i).eval ((Q.g1 i).eval (WithLp.toLp 1 (fun _ => u i))))
    (by intro i; fun_prop) Q.p Q.positiveWeights Q.weights.2]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [← uniform_inputs_scalar_cube_marginal i,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

-- @node: gumbelSoftmaxMix_mem_boundedCube
/-- If [there is at least one component](hyp:hn), [all weights are strictly
positive](hyp:hp), [the temperature is nonzero](hyp:htau), and [every component
vector lies in the d-dimensional coordinate cube of radius K](hyp:hV), [the soft
mixture output lies in that same cube for every score vector](goal). -/
lemma gumbelSoftmaxMix_mem_boundedCube {n d : ℕ} (hn : 0 < n)
    (V : Fin n → L1Vec d) (p : Fin n → ℝ) (hp : ∀ i, 0 < p i)
    (tau : ℝ) (htau : tau ≠ 0) (G : Fin n → ℝ) (K : ℝ)
    (hV : ∀ i, V i ∈ boundedCube d K) :
    gumbelSoftmaxMix V p tau G ∈ boundedCube d K := by
  intro j
  change |∑ i, (V i).ofLp j *
    (if tau = 0 then hardWeights p G else softmaxWeights p tau G).ofLp i| ≤ K
  rw [if_neg htau]
  calc
    _ ≤ ∑ i, |(V i).ofLp j * (softmaxWeights p tau G).ofLp i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |(V i).ofLp j| * (softmaxWeights p tau G).ofLp i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul, abs_of_nonneg (softmaxWeights_nonneg p tau G i)]
    _ ≤ ∑ i, K * (softmaxWeights p tau G).ofLp i := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (hV i j) (softmaxWeights_nonneg p tau G i)
    _ = K := by rw [← Finset.mul_sum, softmaxWeights_sum hn p hp tau G, mul_one]


end Papers.TbsNeuralCausalPi
