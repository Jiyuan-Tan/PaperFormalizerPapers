module
public import Papers.TbsNeuralCausalPi.Helpers.SimulationTwoBlockHistories
/-! # Shared histories for positive-temperature generator comparisons

All components replay their actual two-block networks. A single history on the
joint parameter assignment records their simultaneous activation comparisons;
the mixture readout clears its positive denominator using the existing formula.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
noncomputable section

-- @node: simulationComponentHistory
/-- From [a joint history of activation comparisons across components, samples, and
neurons](hyp:s), the [history for component](goal) [i](hyp:i) is obtained by
restricting every recorded comparison to that component. -/
def simulationComponentHistory {n m w : ℕ}
    (s : List (Fin n × (Fin m × Fin w) → Bool × Bool)) (i : Fin n) :
    List (Fin m × Fin w → Bool × Bool) :=
  s.map (fun f aj => f (i, aj))

-- @node: simulationGeneratorHistoryTests
/-- For [a three-part generator](hyp:q), [sample inputs and mixture covariates](hyp:sample),
[a neuron indexing width](hyp:w), [a layer index](hyp:k), [a joint activation
history](hyp:s), and [a component, sample, and neuron index](hyp:iaj), the
[activation comparison polynomial in the joint generator parameters](goal) is
[the component's two-block comparison polynomial, with its parameters embedded
in the joint parameter space, before the total layer count](step:1), and
[zero at or beyond that count](step:2). -/
def simulationGeneratorHistoryTests {n d m : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau)
    (sample : Fin m → (Fin n → ℝ) × (Fin n → ℝ)) (w : ℕ)
    (k : ℕ) (s : List (Fin n × (Fin m × Fin w) → Bool × Bool))
    (iaj : Fin n × (Fin m × Fin w)) : MvPolynomial (simulationGeneratorVariable n) ℝ :=
  if k < L1 + L2 + 2 then
    MvPolynomial.rename (fun v => Sum.inr (iaj.1, v))
      (simulationBridgeTests (simulationTwoBlockLayers (q.g1 iaj.1) (q.g2 iaj.1))
        (simulationTwoBlockActivate L1 L2)
        (fun a => simulationInputPolynomial
          (WithLp.toLp 1 (fun _ : Fin 1 => (sample a).1 iaj.1)))
        k (simulationComponentHistory s iaj.1) iaj.2)
  else 0

/-- If [the recorded layer count is at most the sum of the two block depths
plus two](hyp:ht), [restricting the joint activation history to one component
gives exactly that component's two-block activation history under the restricted
parameter assignment](goal). -/
-- @node: simulationGeneratorHistory_component
lemma simulationGeneratorHistory_component {n d m w : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau)
    (sample : Fin m → (Fin n → ℝ) × (Fin n → ℝ))
    (theta : simulationGeneratorVariable n → ℝ) (i : Fin n)
    (t : ℕ) (ht : t ≤ L1 + L2 + 2) :
    simulationComponentHistory
      (simulationLayerPatternHistory (simulationGeneratorHistoryTests q sample w) theta t) i =
      simulationLayerPatternHistory
        (simulationBridgeTests (w := w) (simulationTwoBlockLayers (q.g1 i) (q.g2 i))
          (simulationTwoBlockActivate L1 L2)
          (fun a => simulationInputPolynomial
            (WithLp.toLp 1 (fun _ : Fin 1 => (sample a).1 i))))
        (fun v => theta (Sum.inr (i, v))) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change List.map _ (_ :: _) = _ :: _
    rw [List.map_cons]
    apply congrArg₂ List.cons
    · funext aj
      simp only [polynomialComparisonPattern, simulationGeneratorHistoryTests,
        if_pos (show t < L1 + L2 + 2 by omega), MvPolynomial.eval_rename]
      rw [ih (by omega)]
      rfl
    · exact ih (by omega)

-- @node: simulationGeneratorHistoryComponentPolynomial
/-- For [a three-part generator](hyp:q), [sample inputs and mixture covariates](hyp:sample),
[a joint activation history](hyp:s), [a component index](hyp:i), [a sample
index](hyp:a), and [an output coordinate](hyp:j), the [component output
polynomial](goal) replays both network blocks with that component's restricted
history and embeds its parameters in the joint generator parameter space. -/
def simulationGeneratorHistoryComponentPolynomial {n d m w : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau)
    (sample : Fin m → (Fin n → ℝ) × (Fin n → ℝ))
    (s : List (Fin n × (Fin m × Fin w) → Bool × Bool))
    (i : Fin n) (a : Fin m) (j : Fin d) : MvPolynomial (simulationGeneratorVariable n) ℝ :=
  MvPolynomial.rename (fun v => Sum.inr (i, v))
    (simulationBridgeState (simulationTwoBlockLayers (q.g1 i) (q.g2 i))
      (simulationTwoBlockActivate L1 L2)
      (fun a => simulationInputPolynomial
        (WithLp.toLp 1 (fun _ : Fin 1 => (sample a).1 i)))
      (L1 + L2 + 2) (simulationComponentHistory s i) a j)

-- @node: simulationGeneratorHistoryComponentPolynomial_degree
/-- [For any joint activation history, every component output polynomial has
total degree at most the sum of the two block depths plus two](goal). -/
lemma simulationGeneratorHistoryComponentPolynomial_degree {n d m w : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau)
    (sample : Fin m → (Fin n → ℝ) × (Fin n → ℝ))
    (s : List (Fin n × (Fin m × Fin w) → Bool × Bool)) (i : Fin n) (a : Fin m) (j : Fin d) :
    (simulationGeneratorHistoryComponentPolynomial q sample s i a j).totalDegree ≤ L1 + L2 + 2 := by
  apply (MvPolynomial.totalDegree_rename_le _ _).trans
  simpa only [zero_add] using simulationBridgeState_degree _ _ _ 0
    (fun _ _ => by simp [simulationInputPolynomial]) _ _ a j

-- @node: simulationGeneratorHistoryComponentPolynomial_actual
/-- If [the indexing width is at least one](hyp:hw), [covers the output
dimension](hyp:hd), [covers every intermediate component dimension](hyp:hC),
and [covers the first](hyp:hW1) and [second block widths](hyp:hW2), [evaluating
the component output polynomial at the generator's parameters with its actual
joint activation history gives the selected coordinate of the actual two-block
component output on the selected sample](goal). -/
lemma simulationGeneratorHistoryComponentPolynomial_actual {n d m : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau)
    (sample : Fin m → (Fin n → ℝ) × (Fin n → ℝ)) (w : ℕ)
    (hw : 1 ≤ w) (hd : d ≤ w) (hC : ∀ i, dC i ≤ w) (hW1 : W1 ≤ w) (hW2 : W2 ≤ w)
    (i : Fin n) (a : Fin m) (j : Fin d) :
    MvPolynomial.eval (simulationGeneratorParameters q)
      (simulationGeneratorHistoryComponentPolynomial q sample
        (simulationLayerPatternHistory (simulationGeneratorHistoryTests q sample w)
          (simulationGeneratorParameters q) (L1 + L2 + 2)) i a j) =
      ((q.g2 i).eval ((q.g1 i).eval
        (WithLp.toLp 1 (fun _ : Fin 1 => (sample a).1 i)))).ofLp j := by
  rw [simulationGeneratorHistoryComponentPolynomial, MvPolynomial.eval_rename,
    simulationGeneratorHistory_component q sample _ i _ le_rfl]
  exact simulationTwoBlockHistory_actual (q.g1 i) (q.g2 i) _ w hw (hC i) hd hW1 hW2 a j

-- @node: simulationGeneratorHistoryGridPolynomial
/-- For [a three-part generator](hyp:q), [sample inputs and mixture covariates](hyp:sample),
[a map selecting a sample and output coordinate for each comparison](hyp:coord),
[comparison thresholds](hyp:threshold), [a joint activation history](hyp:s),
and [a comparison index](hyp:j), the [threshold comparison polynomial](goal)
is the sum over components of the mixture amplitude times the exponential of
the covariate-to-temperature ratio times the difference between the component
output polynomial and the selected threshold. -/
def simulationGeneratorHistoryGridPolynomial {n d m w : ℕ} {J : Type*} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau)
    (sample : Fin m → (Fin n → ℝ) × (Fin n → ℝ))
    (coord : J → Fin m × Fin d) (threshold : J → ℝ)
    (s : List (Fin n × (Fin m × Fin w) → Bool × Bool)) (j : J) :
    MvPolynomial (simulationGeneratorVariable n) ℝ :=
  simulationMixtureComparison Sum.inl
    (fun i => Real.exp ((sample (coord j).1).2 i / tau))
    (fun i => simulationGeneratorHistoryComponentPolynomial q sample s i (coord j).1 (coord j).2)
    (threshold j)

-- @node: simulationGeneratorHistoryGridPolynomial_degree
/-- [For any joint activation history, every terminal threshold comparison
polynomial has total degree at most the sum of the two block depths plus
three](goal). -/
lemma simulationGeneratorHistoryGridPolynomial_degree {n d m w : ℕ} {J : Type*}
    {dC : Fin n → ℕ} {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau)
    (sample : Fin m → (Fin n → ℝ) × (Fin n → ℝ))
    (coord : J → Fin m × Fin d) (threshold : J → ℝ)
    (s : List (Fin n × (Fin m × Fin w) → Bool × Bool)) (j : J) :
    (simulationGeneratorHistoryGridPolynomial q sample coord threshold s j).totalDegree ≤
      L1 + L2 + 3 :=
  simulationMixtureComparison_degree _ _ _ _
    (fun i => simulationGeneratorHistoryComponentPolynomial_degree q sample s i _ _)

/-- If [the indexing width is at least one](hyp:hw), [covers the output
dimension](hyp:hd), [covers every intermediate component dimension](hyp:hC),
and [covers the first](hyp:hW1) and [second block widths](hyp:hW2), [the actual
generator output is below the selected threshold, weakly or strictly, exactly
when the terminal comparison polynomial evaluated at the actual parameters and
joint activation history is below zero in the corresponding sense](goal). -/
-- @node: simulationGeneratorHistoryGridPolynomial_actual
lemma simulationGeneratorHistoryGridPolynomial_actual {n d m : ℕ} {J : Type*}
    {dC : Fin n → ℕ} {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau)
    (sample : Fin m → (Fin n → ℝ) × (Fin n → ℝ))
    (coord : J → Fin m × Fin d) (threshold : J → ℝ) (w : ℕ)
    (hw : 1 ≤ w) (hd : d ≤ w) (hC : ∀ i, dC i ≤ w) (hW1 : W1 ≤ w) (hW2 : W2 ≤ w) (j : J) :
    let p := simulationGeneratorHistoryGridPolynomial q sample coord threshold
      (simulationLayerPatternHistory (simulationGeneratorHistoryTests q sample w)
        (simulationGeneratorParameters q) (L1 + L2 + 2)) j
    (((q.eval (sample (coord j).1)).ofLp (coord j).2 ≤ threshold j ↔
      MvPolynomial.eval (simulationGeneratorParameters q) p ≤ 0) ∧
    ((q.eval (sample (coord j).1)).ofLp (coord j).2 < threshold j ↔
      MvPolynomial.eval (simulationGeneratorParameters q) p < 0)) := by
  constructor
  · exact gumbelSoftmaxMix_le_iff_polynomial Sum.inl _ (simulationGeneratorParameters q)
      _ _ q.p q.weights.2 q.temperature.ne' _ _ (fun _ => rfl)
      (fun i => simulationGeneratorHistoryComponentPolynomial_actual q sample w hw hd hC hW1 hW2 i _ _)
  · exact gumbelSoftmaxMix_lt_iff_polynomial Sum.inl _ (simulationGeneratorParameters q)
      _ _ q.p q.weights.2 q.temperature.ne' _ _ (fun _ => rfl)
      (fun i => simulationGeneratorHistoryComponentPolynomial_actual q sample w hw hd hC hW1 hW2 i _ _)

-- @node: simulationGeneratorBox_component_mem
/-- If [a network parameter index belongs to the parameter box for the given
depth and width](hyp:hv), [embedding it as a parameter of any selected component
places it in the joint generator parameter box](goal). -/
lemma simulationGeneratorBox_component_mem {n depth w : ℕ} (i : Fin n)
    {v : ℕ × ℕ × ℕ} (hv : v ∈ simulationParameterBox depth w) :
    Sum.inr (i, v) ∈ simulationGeneratorParameterBox n depth w := by
  classical
  exact Finset.mem_union_right _ (Finset.mem_image.mpr
    ⟨(i, v), Finset.mem_product.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩)

-- @node: simulationGeneratorHistoryComponentPolynomial_vars
/-- If [the indexing width is at least one](hyp:hw), [covers the output
dimension](hyp:hd), [covers every intermediate component dimension](hyp:hC),
and [covers the first](hyp:hW1) and [second block widths](hyp:hW2), [every variable
in any component output polynomial belongs to the joint generator parameter box
with that width and depth equal to the sum of the two block depths plus two](goal). -/
lemma simulationGeneratorHistoryComponentPolynomial_vars {n d m w : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau)
    (sample : Fin m → (Fin n → ℝ) × (Fin n → ℝ))
    (hw : 1 ≤ w) (hd : d ≤ w) (hC : ∀ i, dC i ≤ w) (hW1 : W1 ≤ w) (hW2 : W2 ≤ w)
    (s : List (Fin n × (Fin m × Fin w) → Bool × Bool)) (i : Fin n) (a : Fin m) (j : Fin d) :
    (simulationGeneratorHistoryComponentPolynomial q sample s i a j).vars ⊆
      simulationGeneratorParameterBox n (L1 + L2 + 2) w := by
  classical
  have hbase := simulationBridgeState_vars (simulationTwoBlockLayers (q.g1 i) (q.g2 i))
    (simulationTwoBlockActivate L1 L2)
    (fun a => simulationInputPolynomial (WithLp.toLp 1 (fun _ : Fin 1 => (sample a).1 i)))
    (simulationParameterBox (L1 + L2 + 2) w)
    (by intro a j; simp [simulationInputPolynomial]) (L1 + L2 + 2)
    (by
      intro k hk
      have h := simulationTwoBlockLayers_dimensions (q.g1 i) (q.g2 i) w
        hw (hC i) hd hW1 hW2 k hk
      exact simulationLayerVariables_subset_box hk h.1 h.2)
    (simulationComponentHistory s i) a j
  unfold simulationGeneratorHistoryComponentPolynomial
  apply (MvPolynomial.vars_rename _ _).trans
  apply (Finset.image_subset_image hbase).trans
  intro v hv
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
  exact simulationGeneratorBox_component_mem i hu

-- @node: simulationGeneratorHistoryTests_vars
/-- If [the indexing width is at least one](hyp:hw), [covers the output
dimension](hyp:hd), [covers every intermediate component dimension](hyp:hC),
and [covers the first](hyp:hW1) and [second block widths](hyp:hW2), [every variable
in any joint-history activation comparison polynomial belongs to the joint
generator parameter box with that width and depth equal to the sum of the two
block depths plus two](goal). -/
lemma simulationGeneratorHistoryTests_vars {n d m w : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau)
    (sample : Fin m → (Fin n → ℝ) × (Fin n → ℝ))
    (hw : 1 ≤ w) (hd : d ≤ w) (hC : ∀ i, dC i ≤ w) (hW1 : W1 ≤ w) (hW2 : W2 ≤ w)
    (k : ℕ) (s : List (Fin n × (Fin m × Fin w) → Bool × Bool))
    (iaj : Fin n × (Fin m × Fin w)) :
    (simulationGeneratorHistoryTests q sample w k s iaj).vars ⊆
      simulationGeneratorParameterBox n (L1 + L2 + 2) w := by
  classical
  unfold simulationGeneratorHistoryTests
  split_ifs with hk
  · have hbase := simulationBridgeTests_vars
      (simulationTwoBlockLayers (q.g1 iaj.1) (q.g2 iaj.1))
      (simulationTwoBlockActivate L1 L2)
      (fun a => simulationInputPolynomial
        (WithLp.toLp 1 (fun _ : Fin 1 => (sample a).1 iaj.1)))
      (simulationParameterBox (L1 + L2 + 2) w)
      (by intro a j; simp [simulationInputPolynomial]) (L1 + L2 + 2)
      (by
        intro r hr
        have h := simulationTwoBlockLayers_dimensions (q.g1 iaj.1) (q.g2 iaj.1) w
          hw (hC iaj.1) hd hW1 hW2 r hr
        exact simulationLayerVariables_subset_box hr h.1 h.2)
      k hk (simulationComponentHistory s iaj.1) iaj.2
    apply (MvPolynomial.vars_rename _ _).trans
    apply (Finset.image_subset_image hbase).trans
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    exact simulationGeneratorBox_component_mem iaj.1 hu
  · simp

-- @node: simulationGeneratorHistoryTests_degree
/-- If [the layer index is less than the sum of the two block depths plus
two](hyp:hk), [the corresponding joint-history activation comparison polynomial
has total degree at most that sum plus two](goal). -/
lemma simulationGeneratorHistoryTests_degree {n d m w : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau)
    (sample : Fin m → (Fin n → ℝ) × (Fin n → ℝ))
    (k : ℕ) (hk : k < L1 + L2 + 2)
    (s : List (Fin n × (Fin m × Fin w) → Bool × Bool)) (iaj : Fin n × (Fin m × Fin w)) :
    (simulationGeneratorHistoryTests q sample w k s iaj).totalDegree ≤ L1 + L2 + 2 := by
  rw [simulationGeneratorHistoryTests, if_pos hk]
  apply (MvPolynomial.totalDegree_rename_le _ _).trans
  exact (simulationBridgeTests_degree _ _ _ 0
    (fun _ _ => by simp [simulationInputPolynomial]) k _ _).trans (by omega)

-- @node: simulationGeneratorHistoryGridPolynomial_vars
/-- If [the indexing width is at least one](hyp:hw), [covers the output
dimension](hyp:hd), [covers every intermediate component dimension](hyp:hC),
and [covers the first](hyp:hW1) and [second block widths](hyp:hW2), [every variable
in any terminal threshold comparison polynomial belongs to the joint generator
parameter box with that width and depth equal to the sum of the two block
depths plus two](goal). -/
lemma simulationGeneratorHistoryGridPolynomial_vars {n d m w : ℕ} {J : Type*}
    {dC : Fin n → ℕ} {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau)
    (sample : Fin m → (Fin n → ℝ) × (Fin n → ℝ))
    (coord : J → Fin m × Fin d) (threshold : J → ℝ)
    (hw : 1 ≤ w) (hd : d ≤ w) (hC : ∀ i, dC i ≤ w) (hW1 : W1 ≤ w) (hW2 : W2 ≤ w)
    (s : List (Fin n × (Fin m × Fin w) → Bool × Bool)) (j : J) :
    (simulationGeneratorHistoryGridPolynomial q sample coord threshold s j).vars ⊆
      simulationGeneratorParameterBox n (L1 + L2 + 2) w := by
  classical
  unfold simulationGeneratorHistoryGridPolynomial simulationMixtureComparison
  apply (MvPolynomial.vars_sum_subset _ _).trans
  apply Finset.biUnion_subset.mpr
  intro i _
  apply (MvPolynomial.vars_mul _ _).trans
  apply Finset.union_subset
  · apply (MvPolynomial.vars_mul _ _).trans
    simp only [MvPolynomial.vars_C, MvPolynomial.vars_X, Finset.empty_union,
      Finset.singleton_subset_iff]
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  · apply (MvPolynomial.vars_sub_subset (p := _) (q := _)).trans
    simp only [MvPolynomial.vars_C, Finset.union_empty]
    exact simulationGeneratorHistoryComponentPolynomial_vars q sample hw hd hC hW1 hW2 s i _ _

/-- If [the indexing width is at least one](hyp:hw), [covers the output
dimension](hyp:hd), [covers every intermediate component dimension](hyp:hC),
and [covers the first](hyp:hW1) and [second block widths](hyp:hW2), [the number
of distinct terminal weak and strict comparison patterns over all joint
parameter assignments is at most $(8nmwT+5)^{(P+2)T}(8r(T+1)+5)^{P+2}$,
where $T$ is the sum of the two block depths plus two, $P$ is the size of the
joint parameter box at depth $T$ and width $w$, and $r$ is the number of terminal
comparisons](goal). -/
-- @node: simulationGeneratorHistory_grid_patterns_encard_le
lemma simulationGeneratorHistory_grid_patterns_encard_le {n d m : ℕ} {J : Type*} [Fintype J]
    {dC : Fin n → ℕ} {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau)
    (sample : Fin m → (Fin n → ℝ) × (Fin n → ℝ))
    (coord : J → Fin m × Fin d) (threshold : J → ℝ) (w : ℕ)
    (hw : 1 ≤ w) (hd : d ≤ w) (hC : ∀ i, dC i ≤ w) (hW1 : W1 ≤ w) (hW2 : W2 ≤ w) :
    (Set.range (fun theta => polynomialComparisonPattern
      (simulationGeneratorHistoryGridPolynomial q sample coord threshold
        (simulationLayerPatternHistory (simulationGeneratorHistoryTests q sample w)
          theta (L1 + L2 + 2))) theta)).encard ≤
      ((8 * (n * (m * w)) * (L1 + L2 + 2) + 5) ^
        (((simulationGeneratorParameterBox n (L1 + L2 + 2) w).card + 2) * (L1 + L2 + 2)) *
        (8 * Fintype.card J * (L1 + L2 + 3) + 5) ^
          ((simulationGeneratorParameterBox n (L1 + L2 + 2) w).card + 2) : ℕ) := by
  have h := simulationTerminalPatterns_encard_le
    (simulationGeneratorParameterBox n (L1 + L2 + 2) w)
    (simulationGeneratorHistoryTests q sample w)
    (simulationGeneratorHistoryGridPolynomial q sample coord threshold)
    (simulationGeneratorHistoryTests_vars q sample hw hd hC hW1 hW2)
    (simulationGeneratorHistoryGridPolynomial_vars q sample coord threshold hw hd hC hW1 hW2)
    (L1 + L2 + 2) (L1 + L2 + 3) (L1 + L2 + 2)
    (simulationGeneratorHistoryTests_degree q sample)
    (simulationGeneratorHistoryGridPolynomial_degree q sample coord threshold)
  simpa only [Fintype.card_prod, Fintype.card_fin,
    max_eq_left (show 1 ≤ L1 + L2 + 2 by omega),
    max_eq_left (show 1 ≤ L1 + L2 + 3 by omega)] using h

/-- [For any component count $n$, sample size $m$, width $w$, terminal comparison
count $J$, and depth $T$, the product $(8nmwT+5)^{(P+2)T}(8J(T+1)+5)^{P+2}$
is at most $(8(nmw+J)(T+1)+5)^{(n+nw(w+1)+2)(T+1)^2}$, where $P$ is the
size of the joint generator parameter box at depth $T$ and width $w$](goal). -/
-- @node: simulationGenerator_history_bound_le_depth_square
lemma simulationGenerator_history_bound_le_depth_square (n m w J T : ℕ) :
    (8 * (n * (m * w)) * T + 5) ^
        (((simulationGeneratorParameterBox n T w).card + 2) * T) *
      (8 * J * (T + 1) + 5) ^ ((simulationGeneratorParameterBox n T w).card + 2) ≤
    (8 * (n * (m * w) + J) * (T + 1) + 5) ^
      ((n + n * (w * (w + 1)) + 2) * (T + 1) ^ 2) := by
  let B := 8 * (n * (m * w) + J) * (T + 1) + 5
  let P := (simulationGeneratorParameterBox n T w).card + 2
  have hhidden : 8 * (n * (m * w)) * T + 5 ≤ B := by
    dsimp [B]
    gcongr <;> omega
  have hterminal : 8 * J * (T + 1) + 5 ≤ B := by
    dsimp [B]
    gcongr <;> omega
  have hP : P ≤ (n + n * (w * (w + 1)) + 2) * (T + 1) := by
    have hc := simulationGeneratorParameterBox_card n T w
    dsimp [P]
    calc
      _ ≤ n + n * (T * (w * (w + 1))) + 2 := Nat.add_le_add_right hc 2
      _ ≤ _ := by
        rw [show (n + n * (w * (w + 1)) + 2) * (T + 1) =
          (n + n * (T * (w * (w + 1))) + 2) +
            (n * T + n * (w * (w + 1)) + 2 * T) by ring]
        omega
  calc
    _ ≤ B ^ (P * T) * B ^ P :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hhidden _) (Nat.pow_le_pow_left hterminal _)
    _ = B ^ (P * (T + 1)) := by rw [← pow_add, Nat.mul_add, Nat.mul_one]
    _ ≤ _ := Nat.pow_le_pow_right (by dsimp [B]; omega)
      (by
        calc
          P * (T + 1) ≤ ((n + n * (w * (w + 1)) + 2) * (T + 1)) * (T + 1) :=
            Nat.mul_le_mul_right (T + 1) hP
          _ = _ := by ring)

/-- If [the indexing width is at least one](hyp:hw), [covers the output
dimension](hyp:hd), [covers every intermediate component dimension](hyp:hC),
and [covers the first](hyp:hW1) and [second block widths](hyp:hW2), [the weak
and strict threshold comparison indicators for the generator output after
taking its minimum with $K$ and then its maximum with $-K$ equal the Boolean
readout that requires the threshold to exceed $-K$ and either reach $K$ or
satisfy the corresponding terminal polynomial comparison, using weak or strict
inequalities respectively](goal). -/
-- @node: simulationGeneratorHistory_clipped_pattern
lemma simulationGeneratorHistory_clipped_pattern {n d m : ℕ} {J : Type*}
    {dC : Fin n → ℕ} {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau)
    (sample : Fin m → (Fin n → ℝ) × (Fin n → ℝ))
    (coord : J → Fin m × Fin d) (threshold : J → ℝ) (K : ℝ) (w : ℕ)
    (hw : 1 ≤ w) (hd : d ≤ w) (hC : ∀ i, dC i ≤ w) (hW1 : W1 ≤ w) (hW2 : W2 ≤ w) :
    let bits := polynomialComparisonPattern
      (simulationGeneratorHistoryGridPolynomial q sample coord threshold
        (simulationLayerPatternHistory (simulationGeneratorHistoryTests q sample w)
          (simulationGeneratorParameters q) (L1 + L2 + 2))) (simulationGeneratorParameters q)
    (fun j =>
      (decide (-K ≤ threshold j) && (decide (K ≤ threshold j) || (bits j).1),
       decide (-K < threshold j) && (decide (K < threshold j) || (bits j).2))) =
    (fun j =>
      (decide ((truncK K (q.eval (sample (coord j).1))).ofLp (coord j).2 ≤ threshold j),
       decide ((truncK K (q.eval (sample (coord j).1))).ofLp (coord j).2 < threshold j))) := by
  funext j
  obtain ⟨hle, hlt⟩ := simulationGeneratorHistoryGridPolynomial_actual
    q sample coord threshold w hw hd hC hW1 hW2 j
  simp only [polynomialComparisonPattern]
  simp only [← hle, ← hlt]
  simp only [truncK, WithLp.ofLp_toLp, max_le_iff, min_le_iff,
    max_lt_iff, min_lt_iff, Bool.decide_and, Bool.decide_or, Bool.or_comm]

end
end Papers.TbsNeuralCausalPi
