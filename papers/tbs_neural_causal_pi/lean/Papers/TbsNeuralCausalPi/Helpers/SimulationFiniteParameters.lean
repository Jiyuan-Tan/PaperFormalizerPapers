module
public import Papers.TbsNeuralCausalPi.Helpers.SimulationGeneratorPolynomials
public import Papers.TbsNeuralCausalPi.Helpers.SimulationShattering
public import Papers.TbsNeuralCausalPi.Helpers.PolynomialRootArrangement
public import Papers.TbsNeuralCausalPi.Helpers.PolynomialSignComponents
public import Papers.TbsNeuralCausalPi.Helpers.PolynomialUnivariateComponents
public import Papers.TbsNeuralCausalPi.Helpers.PolynomialCurveArrangement
public import Papers.TbsNeuralCausalPi.Helpers.PolynomialCompactHypersurface
public import Papers.TbsNeuralCausalPi.Helpers.PolynomialComponentMinima
public import Papers.TbsNeuralCausalPi.Helpers.PolynomialCriticalWitnesses
public import Papers.TbsNeuralCausalPi.Helpers.PolynomialQuotientRoots
public import Papers.TbsNeuralCausalPi.Helpers.PolynomialBarrierMaxima
/-! # Finite parameter spaces for simulation comparison polynomials

The common parameter box is independent of the stored network widths and
weights. Renaming into its finite type, with one unused default coordinate,
preserves every evaluation and does not increase degree. This supplies an
actual finite-dimensional polynomial family. The perturbed-barrier sign bound
then controls its comparison patterns with exponent linear in the parameter count.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
noncomputable section

-- @node: simulationFiniteVariable
/-- For [a finite set of parameter labels](hyp:S) and [a parameter label](hyp:v),
[the finite-coordinate encoding](goal) retains that label if it belongs to the set
and otherwise sends it to an extra default coordinate. -/
def simulationFiniteVariable {V : Type*} (S : Finset V) (v : V) : Option S := by
  classical
  exact if h : v ∈ S then some ⟨v, h⟩ else none

-- @node: simulationFinitePolynomial
/-- For [a finite set of parameter labels](hyp:S) and [a real polynomial in the
original parameters](hyp:p), [the polynomial on the finite parameter space](goal)
renames each label to its coordinate in the set, using one extra default coordinate
for labels outside the set. -/
def simulationFinitePolynomial {V : Type*} (S : Finset V)
    (p : MvPolynomial V ℝ) : MvPolynomial (Option S) ℝ :=
  MvPolynomial.rename (simulationFiniteVariable S) p

-- @node: simulationFiniteAssignment
/-- Given [a finite set of parameter labels](hyp:S) and [real values for the
original parameters](hyp:a), [the corresponding finite parameter assignment](goal)
assigns [zero to the extra default coordinate](step:1) and [the original value to
each coordinate labelled by a member of the set](step:2). -/
def simulationFiniteAssignment {V : Type*} (S : Finset V) (a : V → ℝ) : Option S → ℝ
  | none => 0
  | some v => a v.val

-- @node: simulationFinitePolynomial_eval
/-- If [every variable occurring in the polynomial belongs to the chosen finite
parameter set](hyp:hp), then [evaluating its finite-coordinate version at the
corresponding finite assignment gives the same value as evaluating the original
polynomial at the original assignment](goal). -/
lemma simulationFinitePolynomial_eval {V : Type*} (S : Finset V)
    (p : MvPolynomial V ℝ) (hp : p.vars ⊆ S) (a : V → ℝ) :
    MvPolynomial.eval (simulationFiniteAssignment S a) (simulationFinitePolynomial S p) =
      MvPolynomial.eval a p := by
  classical
  rw [simulationFinitePolynomial, MvPolynomial.eval_rename]
  apply MvPolynomial.eval₂Hom_congr' rfl _ rfl
  intro v hv _
  simp [simulationFiniteVariable, simulationFiniteAssignment, hp hv]

-- @node: simulationFinitePolynomial_degree
/-- [Renaming a polynomial into the finite parameter space does not increase
its total degree](goal). -/
lemma simulationFinitePolynomial_degree {V : Type*} (S : Finset V)
    (p : MvPolynomial V ℝ) :
    (simulationFinitePolynomial S p).totalDegree ≤ p.totalDegree :=
  MvPolynomial.totalDegree_rename_le _ _

-- @node: simulationFinitePolynomial_card
/-- [The finite parameter space has exactly one more coordinate than the number
of labels in the chosen finite set](goal). -/
lemma simulationFinitePolynomial_card {V : Type*} (S : Finset V) :
    Fintype.card (Option S) = S.card + 1 := by
  simp

-- @node: simulationFinitePolynomial_pattern_range_subset
/-- If [every polynomial in the family uses only labels in the chosen finite
parameter set](hyp:hp), then [every simultaneous Boolean test pattern attainable
with the original parameters is attainable with the finite-coordinate polynomials
when their coordinates vary freely](goal). -/
lemma simulationFinitePolynomial_pattern_range_subset {V I : Type*}
    (S : Finset V) (p : I → MvPolynomial V ℝ) (hp : ∀ i, (p i).vars ⊆ S)
    (test : ℝ → Bool) :
    Set.range (fun a : V → ℝ => fun i => test (MvPolynomial.eval a (p i))) ⊆
      Set.range (fun a : Option S → ℝ => fun i =>
        test (MvPolynomial.eval a (simulationFinitePolynomial S (p i)))) := by
  rintro _ ⟨a, rfl⟩
  refine ⟨simulationFiniteAssignment S a, ?_⟩
  funext i
  exact congrArg test (simulationFinitePolynomial_eval S (p i) (hp i) a)


-- @node: simulationFinitePolynomial_comparison_range_subset
/-- If [every polynomial in the family uses only labels in the chosen finite
parameter set](hyp:hp), then [every joint pattern of weak and strict comparisons
with zero attainable with the original parameters is also attainable with the
finite-coordinate polynomials](goal). -/
lemma simulationFinitePolynomial_comparison_range_subset {V I : Type*}
    (S : Finset V) (p : I → MvPolynomial V ℝ) (hp : ∀ i, (p i).vars ⊆ S) :
    Set.range (polynomialComparisonPattern p) ⊆
      Set.range (polynomialComparisonPattern (fun i => simulationFinitePolynomial S (p i))) := by
  rintro _ ⟨a, rfl⟩
  refine ⟨simulationFiniteAssignment S a, ?_⟩
  funext i
  simp only [polynomialComparisonPattern, simulationFinitePolynomial_eval S (p i) (hp i) a]

-- @node: simulationFinitePolynomial_comparison_encard_le
/-- If [every polynomial uses only labels in a finite parameter set](hyp:hp) and
[each has total degree at most d](hyp:hd), then [the number of attainable joint
weak and strict comparison patterns is at most
$(8 M \max(d,1)+5)^{s+2}$, where M is the number of polynomials and s is the
number of parameter labels in that set](goal). -/
lemma simulationFinitePolynomial_comparison_encard_le {V I : Type*} [Fintype I]
    (S : Finset V) (p : I → MvPolynomial V ℝ) (hp : ∀ i, (p i).vars ⊆ S)
    (d : ℕ) (hd : ∀ i, (p i).totalDegree ≤ d) :
    (Set.range (polynomialComparisonPattern p)).encard ≤
      ((8 * Fintype.card I * max d 1 + 5) ^ (S.card + 2) : ℕ) := by
  have h := (Set.encard_mono
    (simulationFinitePolynomial_comparison_range_subset S p hp)).trans
      (polynomialComparisonPattern_encard_le_degree_power
        (fun i => simulationFinitePolynomial S (p i)) d
        (fun i => (simulationFinitePolynomial_degree S (p i)).trans (hd i)))
  simpa only [simulationFinitePolynomial_card, Nat.add_assoc] using h

-- @node: simulationPolynomial_comparison_growth_card_le
/-- If [all input-indexed polynomials use only labels in a fixed finite parameter
set](hyp:hp) and [have total degree at most d](hyp:hd), then [on any sample of m
inputs, the number of subsets selected by comparisons with zero is at most
$(8 m \max(d,1)+5)^{s+2}$, where s is the number of parameter labels; the Boolean
choice selects strict comparisons when true and weak comparisons otherwise](goal). -/
lemma simulationPolynomial_comparison_growth_card_le {V X : Type*}
    (S : Finset V) (p : X → MvPolynomial V ℝ) (hp : ∀ x, (p x).vars ⊆ S)
    (d : ℕ) (hd : ∀ x, (p x).totalDegree ≤ d) (upper : Bool)
    {m : ℕ} (sample : Fin m → X) :
    (Causalean.Stat.Concentration.growthFamily
      (fun (a : V → ℝ) x => if upper then decide (MvPolynomial.eval a (p x) < 0)
        else decide (MvPolynomial.eval a (p x) ≤ 0)) sample).card ≤
      (8 * m * max d 1 + 5) ^ (S.card + 2) := by
  classical
  let encode (f : Fin m → Bool × Bool) : Finset (Fin m) :=
    Finset.univ.filter (fun i => if upper then (f i).2 else (f i).1)
  have hsub : (↑(Causalean.Stat.Concentration.growthFamily
      (fun (a : V → ℝ) x => if upper then decide (MvPolynomial.eval a (p x) < 0)
        else decide (MvPolynomial.eval a (p x) ≤ 0)) sample) : Set (Finset (Fin m))) ⊆
      encode '' Set.range (polynomialComparisonPattern (fun i => p (sample i))) := by
    intro u hu
    obtain ⟨a, rfl⟩ := Causalean.Stat.Concentration.mem_growthFamily_iff.mp hu
    refine ⟨polynomialComparisonPattern (fun i => p (sample i)) a, ⟨a, rfl⟩, ?_⟩
    ext i
    cases upper <;> simp [encode, polynomialComparisonPattern,
      Causalean.Stat.Concentration.restrictionPattern_mem_iff]
  have h := (Set.encard_mono hsub).trans ((Set.encard_image_le _ _).trans
    (simulationFinitePolynomial_comparison_encard_le S (fun i => p (sample i))
      (fun i => hp (sample i)) d (fun i => hd (sample i))))
  simpa only [Set.encard_coe_eq_coe_finsetCard, Fintype.card_fin, Nat.cast_le] using h

-- @node: simulationFinitePolynomial_growthFamily_subset
/-- If [all input-indexed polynomials use only labels in the chosen finite
parameter set](hyp:hp), then [every subset of sample positions selected by applying
the Boolean test to their original evaluations can also be selected using their
finite-coordinate versions](goal). -/
lemma simulationFinitePolynomial_growthFamily_subset {V X : Type*}
    (S : Finset V) (p : X → MvPolynomial V ℝ) (hp : ∀ x, (p x).vars ⊆ S)
    (test : ℝ → Bool) {m : ℕ} (sample : Fin m → X) :
    Causalean.Stat.Concentration.growthFamily
      (fun (a : V → ℝ) x => test (MvPolynomial.eval a (p x))) sample ⊆
    Causalean.Stat.Concentration.growthFamily
      (fun (a : Option S → ℝ) x =>
        test (MvPolynomial.eval a (simulationFinitePolynomial S (p x)))) sample := by
  classical
  intro u hu
  obtain ⟨a, rfl⟩ := Causalean.Stat.Concentration.mem_growthFamily_iff.mp hu
  apply Causalean.Stat.Concentration.mem_growthFamily_iff.mpr
  refine ⟨simulationFiniteAssignment S a, ?_⟩
  ext k
  simp only [Causalean.Stat.Concentration.restrictionPattern_mem_iff,
    simulationFinitePolynomial_eval S (p (sample k)) (hp (sample k)) a]

-- @node: simulationFinitePolynomial_growthFamily_card_le
/-- If [all input-indexed polynomials use only labels in the chosen finite
parameter set](hyp:hp), then [the number of subsets of sample positions selected
by the Boolean test under original parameter assignments is no greater than the
number selected under finite-coordinate assignments](goal). -/
lemma simulationFinitePolynomial_growthFamily_card_le {V X : Type*}
    (S : Finset V) (p : X → MvPolynomial V ℝ) (hp : ∀ x, (p x).vars ⊆ S)
    (test : ℝ → Bool) {m : ℕ} (sample : Fin m → X) :
    (Causalean.Stat.Concentration.growthFamily
      (fun (a : V → ℝ) x => test (MvPolynomial.eval a (p x))) sample).card ≤
    (Causalean.Stat.Concentration.growthFamily
      (fun (a : Option S → ℝ) x =>
        test (MvPolynomial.eval a (simulationFinitePolynomial S (p x)))) sample).card :=
  Finset.card_le_card (simulationFinitePolynomial_growthFamily_subset S p hp test sample)

-- @node: simulationFinitePolynomial_growthFamily_eq
/-- If [all input-indexed polynomials use only labels in the chosen finite
parameter set](hyp:hp), then [the subsets of sample positions selected by the
Boolean test are exactly the same for original parameter assignments and for
finite-coordinate assignments](goal). -/
lemma simulationFinitePolynomial_growthFamily_eq {V X : Type*}
    (S : Finset V) (p : X → MvPolynomial V ℝ) (hp : ∀ x, (p x).vars ⊆ S)
    (test : ℝ → Bool) {m : ℕ} (sample : Fin m → X) :
    Causalean.Stat.Concentration.growthFamily
      (fun (a : V → ℝ) x => test (MvPolynomial.eval a (p x))) sample =
    Causalean.Stat.Concentration.growthFamily
      (fun (a : Option S → ℝ) x =>
        test (MvPolynomial.eval a (simulationFinitePolynomial S (p x)))) sample := by
  classical
  apply Finset.Subset.antisymm
    (simulationFinitePolynomial_growthFamily_subset S p hp test sample)
  intro u hu
  obtain ⟨a, rfl⟩ := Causalean.Stat.Concentration.mem_growthFamily_iff.mp hu
  apply Causalean.Stat.Concentration.mem_growthFamily_iff.mpr
  refine ⟨a ∘ simulationFiniteVariable S, ?_⟩
  ext k
  simp only [Causalean.Stat.Concentration.restrictionPattern_mem_iff,
    simulationFinitePolynomial, MvPolynomial.eval_rename]

-- @node: simulationGeneratorFinitePolynomial
/-- For [a three-part generator](hyp:q), [a common width bound](hyp:w), [activation
masks for its first network stage](hyp:m1), [activation masks for its second
network stage](hyp:m2), [a pair of noise vectors](hyp:z), [an output coordinate](hyp:j)
and [a comparison threshold](hyp:threshold), [the finite generator comparison
polynomial](goal) is the weighted sum of masked component output-minus-threshold
polynomials, renamed into the common finite parameter box with one extra default
coordinate. -/
def simulationGeneratorFinitePolynomial {n d : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau) (w : ℕ)
    (m1 m2 : Fin n → List (ℕ → Bool))
    (z : (Fin n → ℝ) × (Fin n → ℝ)) (j : Fin d) (threshold : ℝ) :
    MvPolynomial (Option (simulationGeneratorParameterBox n (L1 + L2 + 2) w)) ℝ :=
  simulationFinitePolynomial (simulationGeneratorParameterBox n (L1 + L2 + 2) w)
    (simulationGeneratorGridPolynomial q m1 m2 z j threshold)

-- @node: simulationGeneratorFinitePolynomial_degree
/-- [The finite generator comparison polynomial has total degree at most the
sum of the two network depths plus three](goal). -/
lemma simulationGeneratorFinitePolynomial_degree {n d : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau) (w : ℕ)
    (m1 m2 : Fin n → List (ℕ → Bool))
    (z : (Fin n → ℝ) × (Fin n → ℝ)) (j : Fin d) (threshold : ℝ) :
    (simulationGeneratorFinitePolynomial q w m1 m2 z j threshold).totalDegree ≤
      L1 + L2 + 3 :=
  (simulationFinitePolynomial_degree _ _).trans
    (simulationGeneratorGridPolynomial_degree q m1 m2 z j threshold)

-- @node: simulationGeneratorFinitePolynomial_eval
/-- If [the common width bound is at least one](hyp:hw), [bounds the output
dimension](hyp:hd), [bounds every categorical dimension](hyp:hC), [bounds the
first network width](hyp:hW1) and [bounds the second network width](hyp:hW2), then
[evaluating the finite comparison polynomial at the generator's finite parameter
assignment equals evaluating the original comparison polynomial at its original
parameters](goal). -/
lemma simulationGeneratorFinitePolynomial_eval {n d : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau) (w : ℕ)
    (hw : 1 ≤ w) (hd : d ≤ w) (hC : ∀ i, dC i ≤ w) (hW1 : W1 ≤ w) (hW2 : W2 ≤ w)
    (m1 m2 : Fin n → List (ℕ → Bool))
    (z : (Fin n → ℝ) × (Fin n → ℝ)) (j : Fin d) (threshold : ℝ) :
    MvPolynomial.eval
      (simulationFiniteAssignment (simulationGeneratorParameterBox n (L1 + L2 + 2) w)
        (simulationGeneratorParameters q))
      (simulationGeneratorFinitePolynomial q w m1 m2 z j threshold) =
    MvPolynomial.eval (simulationGeneratorParameters q)
      (simulationGeneratorGridPolynomial q m1 m2 z j threshold) :=
  simulationFinitePolynomial_eval _ _
    (simulationGeneratorGridPolynomial_uniform_vars q w hw hd hC hW1 hW2 m1 m2 z j threshold) _

-- @node: simulationGeneratorFinitePolynomial_parameter_count
/-- [The common finite generator parameter space, including its default
coordinate, has at most $n+n(L_1+L_2+2)w(w+1)+1$ coordinates](goal). -/
lemma simulationGeneratorFinitePolynomial_parameter_count (n L1 L2 w : ℕ) :
    Fintype.card (Option (simulationGeneratorParameterBox n (L1 + L2 + 2) w)) ≤
      n + n * ((L1 + L2 + 2) * (w * (w + 1))) + 1 := by
  rw [simulationFinitePolynomial_card]
  exact Nat.add_le_add_right (simulationGeneratorParameterBox_card n (L1 + L2 + 2) w) 1

-- @node: simulationGenerator_finite_grid_comparisons
/-- If [the common width bound is at least one](hyp:hw), [bounds the output
dimension](hyp:hd), [bounds every categorical dimension](hyp:hC), [bounds the first
network width](hyp:hW1) and [bounds the second network width](hyp:hW2), then [one
finite parameter vector works for all noise draws: each draw admits activation
masks of the prescribed two depths such that every weak or strict comparison of
an output coordinate with a threshold is equivalent to the corresponding
polynomial comparison with zero](goal). -/
lemma simulationGenerator_finite_grid_comparisons {n d : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau) (w : ℕ)
    (hw : 1 ≤ w) (hd : d ≤ w) (hC : ∀ i, dC i ≤ w) (hW1 : W1 ≤ w) (hW2 : W2 ≤ w) :
    ∃ theta : Option (simulationGeneratorParameterBox n (L1 + L2 + 2) w) → ℝ,
      ∀ z : (Fin n → ℝ) × (Fin n → ℝ),
      ∃ m1 m2 : Fin n → List (ℕ → Bool),
        (∀ i, (m1 i).length = L1 ∧ (m2 i).length = L2) ∧
        ∀ (j : Fin d) (threshold : ℝ),
          ((q.eval z).ofLp j ≤ threshold ↔
            MvPolynomial.eval theta
              (simulationGeneratorFinitePolynomial q w m1 m2 z j threshold) ≤ 0) ∧
          ((q.eval z).ofLp j < threshold ↔
            MvPolynomial.eval theta
              (simulationGeneratorFinitePolynomial q w m1 m2 z j threshold) < 0) := by
  refine ⟨simulationFiniteAssignment _ (simulationGeneratorParameters q), ?_⟩
  intro z
  obtain ⟨m1, m2, hlen, h⟩ := simulationGenerator_grid_comparisons q z
  refine ⟨m1, m2, hlen, ?_⟩
  intro j threshold
  rw [simulationGeneratorFinitePolynomial_eval q w hw hd hC hW1 hW2]
  exact h j threshold

-- @node: simulationGenerator_finite_clipped_grid_comparisons
/-- If [the common width bound is at least one](hyp:hw), [bounds the output
dimension](hyp:hd), [bounds every categorical dimension](hyp:hC), [bounds the first
network width](hyp:hW1) and [bounds the second network width](hyp:hW2), then [one
finite parameter vector works for all noise draws, with activation masks of the
prescribed depths for each draw: a clipped output is at most a threshold exactly
when the threshold is at least minus K and either at least K or the comparison
polynomial is nonpositive; the strict comparison satisfies the same formula with
all inequalities strict](goal). -/
lemma simulationGenerator_finite_clipped_grid_comparisons {n d : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau) (w : ℕ)
    (hw : 1 ≤ w) (hd : d ≤ w) (hC : ∀ i, dC i ≤ w) (hW1 : W1 ≤ w) (hW2 : W2 ≤ w)
    (K : ℝ) :
    ∃ theta : Option (simulationGeneratorParameterBox n (L1 + L2 + 2) w) → ℝ,
      ∀ z : (Fin n → ℝ) × (Fin n → ℝ),
      ∃ m1 m2 : Fin n → List (ℕ → Bool),
        (∀ i, (m1 i).length = L1 ∧ (m2 i).length = L2) ∧
        ∀ (j : Fin d) (threshold : ℝ),
          ((truncK K (q.eval z)).ofLp j ≤ threshold ↔
            -K ≤ threshold ∧ (K ≤ threshold ∨
              MvPolynomial.eval theta
                (simulationGeneratorFinitePolynomial q w m1 m2 z j threshold) ≤ 0)) ∧
          ((truncK K (q.eval z)).ofLp j < threshold ↔
            -K < threshold ∧ (K < threshold ∨
              MvPolynomial.eval theta
                (simulationGeneratorFinitePolynomial q w m1 m2 z j threshold) < 0)) := by
  refine ⟨simulationFiniteAssignment _ (simulationGeneratorParameters q), ?_⟩
  intro z
  obtain ⟨m1, m2, hlen, h⟩ := simulationGenerator_clipped_grid_comparisons q z K
  refine ⟨m1, m2, hlen, ?_⟩
  intro j threshold
  rw [simulationGeneratorFinitePolynomial_eval q w hw hd hC hW1 hW2]
  exact h j threshold

end
end Papers.TbsNeuralCausalPi
