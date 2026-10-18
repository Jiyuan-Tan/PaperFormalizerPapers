module
public import Papers.TbsNeuralCausalPi.Helpers.SimulationFiniteParameters
public import Mathlib.Data.List.OfFn
/-! # Finite activation masks for the simulation polynomial construction

Only the coordinates below the fixed width can have nonzero preactivations.
Extending a finite mask by `true` preserves the non-strict sign convention at
the zero preactivations outside that width. The resulting finite alphabet
represents the actual networks without a generic-position assumption.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
noncomputable section

-- @node: simulationExtendMask
/-- For [a Boolean activation mask on a finite width](hyp:mask) and [a
nonnegative coordinate index](hyp:j), the [extended mask](goal) [uses the
original mask within the width](step:1) and [marks every coordinate beyond
the width as active](step:2). -/
def simulationExtendMask {w : ℕ} (mask : Fin w → Bool) (j : ℕ) : Bool :=
  if h : j < w then mask ⟨j, h⟩ else true

-- @node: simulationAffinePolynomial_eq_zero_of_width
/-- If [a layer's output width is at most a width bound](hyp:hw) and [a
coordinate index is at least that bound](hyp:hj), then [the layer's affine
polynomial at that coordinate is zero](goal). -/
lemma simulationAffinePolynomial_eq_zero_of_width
    (l : AffineLayer) (k : ℕ) (z : ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ)
    {j w : ℕ} (hw : l.output ≤ w) (hj : w ≤ j) :
    simulationAffinePolynomial l k z j = 0 := by
  exact if_neg (by omega)

-- @node: simulationActivationRegion_finite_exists
/-- If [every layer's output width is at most the chosen width](hyp:hw), then
[there is one finite Boolean mask per layer whose extensions satisfy the
activation-region conditions for the given input polynomials and parameter
assignment](goal). -/
lemma simulationActivationRegion_finite_exists
    (ls : List AffineLayer) (k w : ℕ)
    (hw : ∀ l ∈ ls, l.output ≤ w)
    (z : ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ) (theta : (ℕ × ℕ × ℕ) → ℝ) :
    ∃ masks : List (Fin w → Bool), masks.length = ls.length ∧
      simulationActivationRegion ls k (masks.map simulationExtendMask) z theta := by
  induction ls generalizing k z with
  | nil => exact ⟨[], rfl, trivial⟩
  | cons l ls ih =>
    let active : Fin w → Bool := fun j =>
      decide (0 ≤ MvPolynomial.eval theta (simulationAffinePolynomial l k z j.val))
    obtain ⟨masks, hlen, hregion⟩ := ih (k + 1)
      (fun a ha => hw a (by simp [ha]))
      (simulationReluPolynomial l k (simulationExtendMask active) z)
    refine ⟨active :: masks, by simp [hlen], ?_⟩
    change (∀ j, simulationExtendMask active j = _) ∧ _
    refine ⟨?_, hregion⟩
    intro j
    by_cases hj : j < w
    · simp [simulationExtendMask, hj, active]
    · rw [simulationExtendMask, dif_neg hj,
        simulationAffinePolynomial_eq_zero_of_width l k z
          (hw l (by simp)) (by omega)]
      simp

-- @node: simulationMaskList
/-- Given [a Boolean activation mask for each of finitely many layers and
coordinates](hyp:mask), the [decoded mask list](goal) lists the layer masks
in order and extends each mask by marking coordinates beyond the width as
active. -/
def simulationMaskList {L w : ℕ} (mask : Fin L → Fin w → Bool) : List (ℕ → Bool) :=
  (List.ofFn mask).map simulationExtendMask

-- @node: simulationMaskList_length
/-- [Decoding a finite array of layer masks produces a list whose length is
the number of layers](goal). -/
lemma simulationMaskList_length {L w : ℕ} (mask : Fin L → Fin w → Bool) :
    (simulationMaskList mask).length = L := by
  simp [simulationMaskList]

-- @node: simulationMaskAlphabet_card
/-- [The number of Boolean mask arrays for L layers of width w is two raised
to L times w](goal). -/
lemma simulationMaskAlphabet_card (L w : ℕ) :
    Fintype.card (Fin L → Fin w → Bool) = 2 ^ (L * w) := by
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, ← pow_mul]
  rw [Nat.mul_comm]

-- @node: simulationNetworkPolynomial_finite_represents
/-- [For every ReLU network and input, there is a finite activation-mask array
whose decoded masks satisfy the network's activation-region conditions and
whose output polynomials have degree at most the depth plus one and evaluate
at the network's stored parameters to the actual output coordinates](goal). -/
lemma simulationNetworkPolynomial_finite_represents {din dout W L : ℕ}
    (q : ReLUNet din dout W L) (x : L1Vec din) :
    ∃ mask : Fin L → Fin W → Bool,
      simulationActivationRegion q.hidden 0 (simulationMaskList mask)
        (simulationInputPolynomial x) (simulationNetworkParameters q) ∧
      ∀ j : Fin dout,
        (simulationNetworkPolynomial q (simulationMaskList mask) x j).totalDegree ≤ L + 1 ∧
        MvPolynomial.eval (simulationNetworkParameters q)
          (simulationNetworkPolynomial q (simulationMaskList mask) x j) = (q.eval x).ofLp j := by
  obtain ⟨masks, hlen, hregion⟩ := simulationActivationRegion_finite_exists
    q.hidden 0 W q.widths (simulationInputPolynomial x) (simulationNetworkParameters q)
  have hlenL : masks.length = L := hlen.trans q.depth
  let mask : Fin L → Fin W → Bool := fun i => masks.get (Fin.cast hlenL.symm i)
  have hdecode : simulationMaskList mask = masks.map simulationExtendMask := by
    subst L
    simp [simulationMaskList, mask]
  refine ⟨mask, hdecode ▸ hregion, ?_⟩
  intro j
  exact ⟨simulationNetworkPolynomial_degree q _ x j,
    simulationNetworkPolynomial_eval q _ x (hdecode ▸ hregion) j⟩

-- @node: simulationNormalizeMasks
/-- Given [a width bound](hyp:w) and [a list of activation masks on all
nonnegative coordinates](hyp:masks), the [normalized mask list](goal)
restricts each mask to coordinates below the bound and then extends it by
marking all remaining coordinates as active. -/
def simulationNormalizeMasks (w : ℕ) (masks : List (ℕ → Bool)) : List (ℕ → Bool) :=
  masks.map (fun active => simulationExtendMask (fun j : Fin w => active j.val))

-- @node: simulationReluPolynomial_normalize_mask
/-- If [a layer's output width is at most the normalization width](hyp:hw),
then [restricting its activation mask to that width and extending it as active
beyond the width leaves the layer's ReLU polynomials unchanged](goal). -/
lemma simulationReluPolynomial_normalize_mask
    (l : AffineLayer) (k w : ℕ) (hw : l.output ≤ w) (active : ℕ → Bool)
    (z : ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ) :
    simulationReluPolynomial l k
      (simulationExtendMask (fun j : Fin w => active j.val)) z =
      simulationReluPolynomial l k active z := by
  funext j
  by_cases hj : j < w
  · simp [simulationReluPolynomial, simulationExtendMask, hj]
  · have hz := simulationAffinePolynomial_eq_zero_of_width l k z hw (by omega : w ≤ j)
    simp [simulationReluPolynomial, hz]

-- @node: simulationHiddenPolynomial_normalize_masks
/-- If [every hidden layer's output width is at most the normalization
width](hyp:hw), then [normalizing the mask list leaves the hidden-layer
polynomials unchanged](goal). -/
lemma simulationHiddenPolynomial_normalize_masks
    (ls : List AffineLayer) (k w : ℕ) (hw : ∀ l ∈ ls, l.output ≤ w)
    (masks : List (ℕ → Bool)) (z : ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ) :
    simulationHiddenPolynomial ls k (simulationNormalizeMasks w masks) z =
      simulationHiddenPolynomial ls k masks z := by
  induction ls generalizing k masks z with
  | nil => rfl
  | cons l ls ih =>
    have ht := ih (k + 1) (fun a ha => hw a (by simp [ha]))
    cases masks with
    | nil =>
      exact ht [] (simulationReluPolynomial l k (fun _ => false) z)
    | cons a masks =>
      simp only [simulationNormalizeMasks, List.map_cons, simulationHiddenPolynomial,
        List.headD_cons, List.tail_cons]
      rw [simulationReluPolynomial_normalize_mask l k w (hw l (by simp)) a z]
      exact ht masks (simulationReluPolynomial l k a z)

-- @node: simulationNetworkPolynomialAt_normalize_masks
/-- If [the network's width bound is at most the normalization width](hyp:hw),
then [normalizing the activation masks leaves each network output polynomial
unchanged, for any starting layer index and input polynomials](goal). -/
lemma simulationNetworkPolynomialAt_normalize_masks {din dout W L : ℕ}
    (q : ReLUNet din dout W L) (k w : ℕ) (hw : W ≤ w)
    (masks : List (ℕ → Bool)) (z : ℕ → MvPolynomial (ℕ × ℕ × ℕ) ℝ)
    (j : Fin dout) :
    simulationNetworkPolynomialAt q k (simulationNormalizeMasks w masks) z j =
      simulationNetworkPolynomialAt q k masks z j := by
  unfold simulationNetworkPolynomialAt
  rw [simulationHiddenPolynomial_normalize_masks q.hidden k w
    (fun l hl => (q.widths l hl).trans hw) masks z]

-- @node: simulationNormalizeMasks_has_finite_code
/-- If [the mask list has length L](hyp:hlen), then [there is a finite Boolean
array with L layers and the chosen width whose decoded mask list equals the
normalized original list](goal). -/
lemma simulationNormalizeMasks_has_finite_code {L : ℕ} (w : ℕ)
    (masks : List (ℕ → Bool)) (hlen : masks.length = L) :
    ∃ code : Fin L → Fin w → Bool,
      simulationMaskList code = simulationNormalizeMasks w masks := by
  subst L
  refine ⟨fun i j => masks.get i j.val, ?_⟩
  unfold simulationMaskList simulationNormalizeMasks
  change (List.ofFn ((fun active : ℕ → Bool => fun j : Fin w => active j.val) ∘
    masks.get)).map simulationExtendMask = _
  rw [← List.map_ofFn, List.ofFn_get, List.map_map]
  rfl

-- @node: simulationGeneratorComponentPolynomial_normalize_masks
/-- [Normalizing both activation-mask lists to their respective network widths
leaves every mixture-component output polynomial unchanged at any scalar
latent input](goal). -/
lemma simulationGeneratorComponentPolynomial_normalize_masks
    {n d : ℕ} {dC : Fin n → ℕ} {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau) (i : Fin n)
    (m1 m2 : List (ℕ → Bool)) (u : ℝ) (j : Fin d) :
    simulationGeneratorComponentPolynomial q i
      (simulationNormalizeMasks W1 m1) (simulationNormalizeMasks W2 m2) u j =
      simulationGeneratorComponentPolynomial q i m1 m2 u j := by
  have hinter : simulationGeneratorIntermediate q i (simulationNormalizeMasks W1 m1) u =
      simulationGeneratorIntermediate q i m1 u := by
    funext a
    unfold simulationGeneratorIntermediate
    split_ifs
    · exact simulationNetworkPolynomialAt_normalize_masks _ _ _ le_rfl _ _ _
    · rfl
  unfold simulationGeneratorComponentPolynomial
  rw [hinter, simulationNetworkPolynomialAt_normalize_masks _ _ _ le_rfl]

-- @node: simulationGeneratorGridPolynomial_normalize_masks
/-- [Normalizing both activation-mask lists for every mixture component to
their respective network widths leaves the generator's grid-comparison
polynomial unchanged for every exogenous input, output coordinate, and
threshold](goal). -/
lemma simulationGeneratorGridPolynomial_normalize_masks
    {n d : ℕ} {dC : Fin n → ℕ} {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau)
    (m1 m2 : Fin n → List (ℕ → Bool))
    (z : (Fin n → ℝ) × (Fin n → ℝ)) (j : Fin d) (threshold : ℝ) :
    simulationGeneratorGridPolynomial q
      (fun i => simulationNormalizeMasks W1 (m1 i))
      (fun i => simulationNormalizeMasks W2 (m2 i)) z j threshold =
      simulationGeneratorGridPolynomial q m1 m2 z j threshold := by
  unfold simulationGeneratorGridPolynomial
  simp_rw [simulationGeneratorComponentPolynomial_normalize_masks]

-- @node: simulationGenerator_grid_comparisons_finite_masks
/-- [For every generator and exogenous input, there are finite activation-mask
arrays for both network blocks of every component such that, simultaneously
for all output coordinates and thresholds, the output is below the threshold
if and only if the corresponding grid-comparison polynomial evaluated at the
generator's parameters is negative; the same equivalence holds with weak
inequalities](goal). -/
lemma simulationGenerator_grid_comparisons_finite_masks
    {n d : ℕ} {dC : Fin n → ℕ} {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    ∃ m1 : Fin n → Fin L1 → Fin W1 → Bool,
    ∃ m2 : Fin n → Fin L2 → Fin W2 → Bool,
      ∀ (j : Fin d) (threshold : ℝ),
        ((q.eval z).ofLp j ≤ threshold ↔
          MvPolynomial.eval (simulationGeneratorParameters q)
            (simulationGeneratorGridPolynomial q
              (fun i => simulationMaskList (m1 i))
              (fun i => simulationMaskList (m2 i)) z j threshold) ≤ 0) ∧
        ((q.eval z).ofLp j < threshold ↔
          MvPolynomial.eval (simulationGeneratorParameters q)
            (simulationGeneratorGridPolynomial q
              (fun i => simulationMaskList (m1 i))
              (fun i => simulationMaskList (m2 i)) z j threshold) < 0) := by
  obtain ⟨a1, a2, hlen, hcompare⟩ := simulationGenerator_grid_comparisons q z
  choose m1 hm1 using fun i => simulationNormalizeMasks_has_finite_code W1 (a1 i) (hlen i).1
  choose m2 hm2 using fun i => simulationNormalizeMasks_has_finite_code W2 (a2 i) (hlen i).2
  refine ⟨m1, m2, ?_⟩
  intro j threshold
  simp_rw [hm1, hm2, simulationGeneratorGridPolynomial_normalize_masks]
  exact hcompare j threshold

-- @node: simulationGeneratorMaskAlphabet_card
/-- [The number of pairs of activation-mask arrays for n components, with
block depths L1 and L2 and widths W1 and W2, is two raised to n times the sum
of L1 times W1 and L2 times W2](goal). -/
lemma simulationGeneratorMaskAlphabet_card (n L1 W1 L2 W2 : ℕ) :
    Fintype.card ((Fin n → Fin L1 → Fin W1 → Bool) ×
      (Fin n → Fin L2 → Fin W2 → Bool)) = 2 ^ (n * (L1 * W1 + L2 * W2)) := by
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, ← pow_mul, ← pow_add]
  congr 1
  ring

-- @node: simulationGenerator_finite_parameter_mask_comparisons
/-- Suppose [the common width bound is at least one](hyp:hw), [the output
dimension is at most this bound](hyp:hd), [every component's intermediate
dimension is at most this bound](hyp:hC), [the first network width is at most
this bound](hyp:hW1), and [the second network width is at most this bound](hyp:hW2).
Then [there is a
single parameter vector indexed by a finite box with an additional default
index such that, for every exogenous input, finite activation-mask arrays
give comparison polynomials of degree at most the sum of the two block
depths plus three, and every strict or weak output-threshold comparison is
equivalent to the corresponding strict or weak comparison of the evaluated
polynomial with zero](goal). -/
lemma simulationGenerator_finite_parameter_mask_comparisons
    {n d : ℕ} {dC : Fin n → ℕ} {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (q : ThreePartGenerator n d dC W1 L1 W2 L2 tau) (w : ℕ)
    (hw : 1 ≤ w) (hd : d ≤ w) (hC : ∀ i, dC i ≤ w)
    (hW1 : W1 ≤ w) (hW2 : W2 ≤ w) :
    ∃ theta : Option (simulationGeneratorParameterBox n (L1 + L2 + 2) w) → ℝ,
      ∀ z : (Fin n → ℝ) × (Fin n → ℝ),
      ∃ m1 : Fin n → Fin L1 → Fin W1 → Bool,
      ∃ m2 : Fin n → Fin L2 → Fin W2 → Bool,
        ∀ (j : Fin d) (threshold : ℝ),
          let p := simulationGeneratorFinitePolynomial q w
            (fun i => simulationMaskList (m1 i))
            (fun i => simulationMaskList (m2 i)) z j threshold
          p.totalDegree ≤ L1 + L2 + 3 ∧
          ((q.eval z).ofLp j ≤ threshold ↔ MvPolynomial.eval theta p ≤ 0) ∧
          ((q.eval z).ofLp j < threshold ↔ MvPolynomial.eval theta p < 0) := by
  refine ⟨simulationFiniteAssignment _ (simulationGeneratorParameters q), ?_⟩
  intro z
  obtain ⟨m1, m2, hcompare⟩ := simulationGenerator_grid_comparisons_finite_masks q z
  refine ⟨m1, m2, ?_⟩
  intro j threshold
  refine ⟨simulationGeneratorFinitePolynomial_degree q w _ _ z j threshold, ?_⟩
  rw [simulationGeneratorFinitePolynomial_eval q w hw hd hC hW1 hW2]
  exact hcompare j threshold

end
end Papers.TbsNeuralCausalPi
