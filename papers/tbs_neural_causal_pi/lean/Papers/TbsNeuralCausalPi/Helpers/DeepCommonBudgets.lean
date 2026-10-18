module
public import Papers.TbsNeuralCausalPi.TCorFix3c402872
/-! # Common latent generator budgets for finitely many blocks

Widening preserves the concrete networks and their laws. Component rates are
compared only when their dimensions are bounded by the supplied ambient budget.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section

/-- For [a three-part generator](hyp:q), [an increase in its first width budget](hyp:h1),
and [an increase in its second width budget](hyp:h2), [the widened generator](goal)
retains the component functions and mixing weights with the larger width budgets. -/
-- @node: ThreePartGenerator.widen
def ThreePartGenerator.widen {N d : ℕ} {dC : Fin N → ℕ}
    {W1 L1 W2 L2 W1' W2' : ℕ} {tau : ℝ}
    (q : ThreePartGenerator N d dC W1 L1 W2 L2 tau)
    (h1 : W1 ≤ W1') (h2 : W2 ≤ W2') :
    ThreePartGenerator N d dC W1' L1 W2' L2 tau :=
  { q with g1 := fun i => (q.g1 i).widen h1
           g2 := fun i => (q.g2 i).widen h2 }

-- @node: ThreePartGenerator.widen_eval
/-- For [a three-part generator](hyp:q), when [the first width budget is increased](hyp:h1)
and [the second width budget is increased](hyp:h2), [the widened generator evaluates
to exactly the same function](goal). -/
lemma ThreePartGenerator.widen_eval {N d : ℕ} {dC : Fin N → ℕ}
    {W1 L1 W2 L2 W1' W2' : ℕ} {tau : ℝ}
    (q : ThreePartGenerator N d dC W1 L1 W2 L2 tau)
    (h1 : W1 ≤ W1') (h2 : W2 ≤ W2') :
    (q.widen h1 h2).eval = q.eval := rfl

-- @node: generatorLaw_widen
/-- For [a three-part generator](hyp:q), [increasing its first width budget](hyp:h1)
and [increasing its second width budget](hyp:h2) [leaves its generated distribution unchanged](goal). -/
lemma generatorLaw_widen {N d : ℕ} {dC : Fin N → ℕ}
    {W1 L1 W2 L2 W1' W2' : ℕ} {tau : ℝ}
    (q : ThreePartGenerator N d dC W1 L1 W2 L2 tau)
    (h1 : W1 ≤ W1') (h2 : W2 ≤ W2') :
    generatorLaw (q.widen h1 h2) = generatorLaw q := rfl

/-- If [the common dimension bound is positive](hyp:hD), [the chart dimension
does not exceed it](hyp:hqD), and [both depths are at least one](hyp:hL1,hL2),
[the sum of the two depth rates with exponent minus two divided by the chart
dimension, taken as zero for a zero-dimensional chart, is bounded by the sum
of the rates with exponent minus two divided by the common dimension bound](goal). -/
-- @node: deep_component_budget_rate_le
lemma deep_component_budget_rate_le {q D L1 L2 : ℕ}
    (hD : 0 < D) (hqD : q ≤ D) (hL1 : 1 ≤ L1) (hL2 : 1 ≤ L2) :
    (if 0 < q then
      (L1 : ℝ) ^ (-(2 : ℝ) / max 1 q) +
      (L2 : ℝ) ^ (-(2 : ℝ) / max 1 q) else 0) ≤
      (L1 : ℝ) ^ (-(2 : ℝ) / D) + (L2 : ℝ) ^ (-(2 : ℝ) / D) := by
  split_ifs with hq
  · have hmax : max 1 q ≤ D := max_le hD hqD
    exact add_le_add
      (wide_component_rate_le (by omega) hmax (by exact_mod_cast hL1) (by norm_num))
      (wide_component_rate_le (by omega) hmax (by exact_mod_cast hL2) (by norm_num))
  · positivity

/-- For [block dimensions](hyp:dims), [block probability laws](hyp:P), [component counts](hyp:counts),
[component sets](hyp:S), [chart dimensions](hyp:dC), and [a common Lipschitz bound](hyp:L),
suppose [the sets are precisely the finitely many support components](hyp:hsupp),
[they admit cube charts with that Lipschitz bound](hyp:hcharts),
[their conditional laws dominate cube volume through such charts](hyp:hdom),
[suitable chart pullbacks give zero mass to positive-dimensional cube boundaries](hyp:hboundary),
and [the coordinate approximation theorem holds](hyp:hgate).
For [an ambient dimension budget](hyp:D) that [is positive](hyp:hD) and
[bounds all block dimensions](hyp:hdims) and [all chart dimensions](hyp:hchartdims),
[there exist common positive width factors, an error constant, a depth threshold,
and a temperature cutoff below one such that all larger depths and smaller positive
temperatures admit block generators of widths proportional to the budget and its square,
with exact component masses, first blocks mapping into their cubes, exact membership
for zero-dimensional second blocks, and each block's Wasserstein error bounded by
the error constant times the sum of the two depth powers with exponent minus two
over the budget and the temperature minus temperature times its logarithm](goal). -/
-- @node: deep_generators_common_budgets
lemma deep_generators_common_budgets {b : ℕ} (dims : Fin b → ℕ)
    (P : ∀ j, ProbabilityMeasure (L1Vec (dims j)))
    (counts : Fin b → ℕ) (S : ∀ j, Fin (counts j) → Set (L1Vec (dims j)))
    (dC : ∀ j, Fin (counts j) → ℕ) (L : ℝ≥0)
    (hsupp : ∀ j, SupportFiniteComponents (P j : Measure _) (S j))
    (hcharts : ∀ j, ComponentsLipschitzHomeomorphic (S j) (dC j) L)
    (hdom : ∀ j i, LowerBoundDomination (d := dC j i)
      (ProbabilityTheory.cond (P j : Measure _) (S j i)) (S j i) L)
    (hboundary : ∀ j i, PullbackVanishesOnBoundary (d := dC j i)
      (ProbabilityTheory.cond (P j : Measure _) (S j i)) (S j i) L)
    (hgate : YarotskyCoordinateApprox)
    (D : ℕ) (hD : 0 < D) (hdims : ∀ j, dims j ≤ D)
    (hchartdims : ∀ j i, dC j i ≤ D) :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧ ∃ A : ℝ, 0 < A ∧
      ∃ B : ℕ, 1 ≤ B ∧ ∃ tb : ℝ, 0 < tb ∧ tb < 1 ∧
      ∀ L1 L2 : ℕ, B ≤ L1 → B ≤ L2 → ∀ tau : ℝ, 0 < tau → tau < tb →
        ∃ Q : ∀ j, ThreePartGenerator (counts j) (dims j) (dC j)
          (c1 * D) L1 (c2 * D ^ 2) L2 tau,
          (∀ j i, (Q j).p i = ((P j : Measure _) (S j i)).toReal) ∧
          (∀ j i, Set.MapsTo ((Q j).g1 i).eval (unitCube 1) (unitCube (dC j i))) ∧
          (∀ j i, dC j i = 0 →
            Set.MapsTo ((Q j).g2 i).eval (unitCube (dC j i)) (S j i)) ∧
          ∀ j, wasserstein1 (generatorLaw (Q j)) (P j : Measure _) ≤
            ENNReal.ofReal (A * ((L1 : ℝ) ^ (-(2 : ℝ) / D) +
              (L2 : ℝ) ^ (-(2 : ℝ) / D) + tau - tau * Real.log tau)) := by
  classical
  choose c1 c2 hc1 hc2 A hA B hB tb htb htb1 happ using
    fun j => deep_generator_approximation_exists_factors (P j) (S j) (dC j) L
      (hsupp j) (hcharts j) (hdom j) (hboundary j) hgate
  let C1 := 1 + ∑ j, c1 j
  let C2 := 1 + ∑ j, c2 j
  let E := 1 + ∑ j, A j
  let Bmax := 1 + ∑ j, B j
  have hc1le (j : Fin b) : c1 j ≤ C1 := by
    have := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => Nat.zero_le (c1 k))
      (Finset.mem_univ j)
    dsimp [C1]; omega
  have hc2le (j : Fin b) : c2 j ≤ C2 := by
    have := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => Nat.zero_le (c2 k))
      (Finset.mem_univ j)
    dsimp [C2]; omega
  have hBle (j : Fin b) : B j ≤ Bmax := by
    have := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => Nat.zero_le (B k))
      (Finset.mem_univ j)
    dsimp [Bmax]; omega
  have hAle (j : Fin b) : A j ≤ E := by
    have := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => (hA k).le)
      (Finset.mem_univ j)
    dsimp [E]; linarith
  have hE : 0 < E := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => (hA j).le)
    dsimp [E]; linarith
  have hsmall (s : Finset (Fin b)) :
      ∃ t : ℝ, 0 < t ∧ t < 1 ∧ ∀ j ∈ s, t ≤ tb j := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1/2, by norm_num, by norm_num, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨t, ht, ht1, hts⟩ := ih
      refine ⟨min t (tb a), lt_min ht (htb a), (min_le_left _ _).trans_lt ht1, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hts j hj)
  obtain ⟨t, ht, ht1, htle⟩ := hsmall Finset.univ
  refine ⟨C1, C2, by dsimp [C1]; omega, by dsimp [C2]; omega,
    E, hE, Bmax, by dsimp [Bmax]; omega, t, ht, ht1, ?_⟩
  intro L1 L2 hL1 hL2 tau htau htaut
  choose Q hp hcube hzero herr using fun j =>
    happ j L1 L2 ((hBle j).trans hL1) ((hBle j).trans hL2) tau htau
      (htaut.trans_le (htle j (Finset.mem_univ j)))
  have hqD (j : Fin b) : Finset.univ.sup (dC j) ≤ D :=
    Finset.sup_le (fun i _ => hchartdims j i)
  have hwidth1 (j : Fin b) : c1 j * max 1 (Finset.univ.sup (dC j)) ≤ C1 * D :=
    Nat.mul_le_mul (hc1le j) (max_le hD (hqD j))
  have hwidth2 (j : Fin b) :
      c2 j * dims j * max 1 (Finset.univ.sup (dC j)) ≤ C2 * D ^ 2 := by
    calc
      _ ≤ C2 * D * D := Nat.mul_le_mul
        (Nat.mul_le_mul (hc2le j) (hdims j)) (max_le hD (hqD j))
      _ = _ := by ring
  refine ⟨fun j => (Q j).widen (hwidth1 j) (hwidth2 j), hp, hcube, hzero, ?_⟩
  intro j
  rw [generatorLaw_widen]
  refine (herr j).trans (ENNReal.ofReal_le_ofReal ?_)
  have hrate := deep_component_budget_rate_le hD (hqD j)
    ((hB j).trans ((hBle j).trans hL1)) ((hB j).trans ((hBle j).trans hL2))
  have hlog : Real.log tau ≤ 0 := Real.log_nonpos htau.le
    (htaut.trans ht1).le
  have hnonneg : 0 ≤ (L1 : ℝ) ^ (-(2 : ℝ) / D) +
      (L2 : ℝ) ^ (-(2 : ℝ) / D) + tau - tau * Real.log tau := by
    have := Real.rpow_nonneg (Nat.cast_nonneg L1) (-(2 : ℝ) / D)
    have := Real.rpow_nonneg (Nat.cast_nonneg L2) (-(2 : ℝ) / D)
    have := mul_nonpos_of_nonneg_of_nonpos htau.le hlog
    linarith
  exact (mul_le_mul_of_nonneg_left (by linarith :
    ((if 0 < Finset.univ.sup (dC j) then
      (L1 : ℝ) ^ (-(2 : ℝ) / max 1 (Finset.univ.sup (dC j))) +
      (L2 : ℝ) ^ (-(2 : ℝ) / max 1 (Finset.univ.sup (dC j))) else 0) +
      tau - tau * Real.log tau) ≤
      (L1 : ℝ) ^ (-(2 : ℝ) / D) + (L2 : ℝ) ^ (-(2 : ℝ) / D) +
      tau - tau * Real.log tau) (hA j).le).trans
        (mul_le_mul_of_nonneg_right (hAle j) hnonneg)


/-- Given [block dimensions](hyp:dims), [block laws](hyp:P), [component counts](hyp:counts),
[component sets](hyp:S), [chart dimensions](hyp:dC), and [a Lipschitz bound](hyp:L),
assume [the sets form the finite support components](hyp:hsupp),
[Lipschitz cube charts exist](hyp:hcharts), [conditional laws dominate cube volume](hyp:hdom),
[suitable chart pullbacks have no positive-dimensional boundary mass](hyp:hboundary),
and [coordinate approximation is available](hyp:hgate).
For [a dimension budget](hyp:D) that [is positive](hyp:hD), [bounds the block dimensions](hyp:hdims),
and [bounds the chart dimensions](hyp:hchartdims), [there are a common positive error
constant, depth threshold, and temperature cutoff below one such that all larger depths
and smaller positive temperatures admit generators with the universal first width factor
times the budget and second width factor times its square, exact component masses,
cube-valued first blocks, component-valued zero-dimensional second blocks, and block
Wasserstein errors bounded by the constant times the two depth powers with exponent
minus two over the budget plus temperature minus temperature times its logarithm](goal). -/
lemma deep_generators_common_budgets_explicit {b : ℕ} (dims : Fin b → ℕ)
    (P : ∀ j, ProbabilityMeasure (L1Vec (dims j)))
    (counts : Fin b → ℕ) (S : ∀ j, Fin (counts j) → Set (L1Vec (dims j)))
    (dC : ∀ j, Fin (counts j) → ℕ) (L : ℝ≥0)
    (hsupp : ∀ j, SupportFiniteComponents (P j : Measure _) (S j))
    (hcharts : ∀ j, ComponentsLipschitzHomeomorphic (S j) (dC j) L)
    (hdom : ∀ j i, LowerBoundDomination (d := dC j i)
      (ProbabilityTheory.cond (P j : Measure _) (S j i)) (S j i) L)
    (hboundary : ∀ j i, PullbackVanishesOnBoundary (d := dC j i)
      (ProbabilityTheory.cond (P j : Measure _) (S j i)) (S j i) L)
    (hgate : YarotskyCoordinateApprox)
    (D : ℕ) (hD : 0 < D) (hdims : ∀ j, dims j ≤ D)
    (hchartdims : ∀ j i, dC j i ≤ D) :
    ∃ A : ℝ, 0 < A ∧
      ∃ B : ℕ, 1 ≤ B ∧ ∃ tb : ℝ, 0 < tb ∧ tb < 1 ∧
      ∀ L1 L2 : ℕ, B ≤ L1 → B ≤ L2 → ∀ tau : ℝ, 0 < tau → tau < tb →
        ∃ Q : ∀ j, ThreePartGenerator (counts j) (dims j) (dC j)
          (deepFirstWidthFactor * D) L1 (deepSecondWidthFactor * D ^ 2) L2 tau,
          (∀ j i, (Q j).p i = ((P j : Measure _) (S j i)).toReal) ∧
          (∀ j i, Set.MapsTo ((Q j).g1 i).eval (unitCube 1) (unitCube (dC j i))) ∧
          (∀ j i, dC j i = 0 →
            Set.MapsTo ((Q j).g2 i).eval (unitCube (dC j i)) (S j i)) ∧
          ∀ j, wasserstein1 (generatorLaw (Q j)) (P j : Measure _) ≤
            ENNReal.ofReal (A * ((L1 : ℝ) ^ (-(2 : ℝ) / D) +
              (L2 : ℝ) ^ (-(2 : ℝ) / D) + tau - tau * Real.log tau)) := by
  classical
  choose A hA B hB tb htb htb1 happ using
    fun j => deep_generator_approximation (P j) (S j) (dC j) L
      (hsupp j) (hcharts j) (hdom j) (hboundary j) hgate
  let E := 1 + ∑ j, A j
  let Bmax := 1 + ∑ j, B j
  have hBle (j : Fin b) : B j ≤ Bmax := by
    have := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => Nat.zero_le (B k))
      (Finset.mem_univ j)
    dsimp [Bmax]; omega
  have hAle (j : Fin b) : A j ≤ E := by
    have := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => (hA k).le)
      (Finset.mem_univ j)
    dsimp [E]; linarith
  have hE : 0 < E := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => (hA j).le)
    dsimp [E]; linarith
  have hsmall (s : Finset (Fin b)) :
      ∃ t : ℝ, 0 < t ∧ t < 1 ∧ ∀ j ∈ s, t ≤ tb j := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1/2, by norm_num, by norm_num, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨t, ht, ht1, hts⟩ := ih
      refine ⟨min t (tb a), lt_min ht (htb a), (min_le_left _ _).trans_lt ht1, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hts j hj)
  obtain ⟨t, ht, ht1, htle⟩ := hsmall Finset.univ
  refine ⟨E, hE, Bmax, by dsimp [Bmax]; omega, t, ht, ht1, ?_⟩
  intro L1 L2 hL1 hL2 tau htau htaut
  choose Q hp hcube hzero herr using fun j =>
    happ j L1 L2 ((hBle j).trans hL1) ((hBle j).trans hL2) tau htau
      (htaut.trans_le (htle j (Finset.mem_univ j)))
  have hqD (j : Fin b) : Finset.univ.sup (dC j) ≤ D :=
    Finset.sup_le (fun i _ => hchartdims j i)
  have hwidth1 (j : Fin b) :
      deepFirstWidthFactor * max 1 (Finset.univ.sup (dC j)) ≤ deepFirstWidthFactor * D :=
    Nat.mul_le_mul_left deepFirstWidthFactor (max_le hD (hqD j))
  have hwidth2 (j : Fin b) :
      deepSecondWidthFactor * dims j * max 1 (Finset.univ.sup (dC j)) ≤
        deepSecondWidthFactor * D ^ 2 := by
    calc
      _ ≤ deepSecondWidthFactor * D * D := Nat.mul_le_mul
        (Nat.mul_le_mul_left deepSecondWidthFactor (hdims j)) (max_le hD (hqD j))
      _ = _ := by ring
  refine ⟨fun j => (Q j).widen (hwidth1 j) (hwidth2 j), hp, hcube, hzero, ?_⟩
  intro j
  rw [generatorLaw_widen]
  refine (herr j).trans (ENNReal.ofReal_le_ofReal ?_)
  have hrate := deep_component_budget_rate_le hD (hqD j)
    ((hB j).trans ((hBle j).trans hL1)) ((hB j).trans ((hBle j).trans hL2))
  have hlog : Real.log tau ≤ 0 := Real.log_nonpos htau.le
    (htaut.trans ht1).le
  have hnonneg : 0 ≤ (L1 : ℝ) ^ (-(2 : ℝ) / D) +
      (L2 : ℝ) ^ (-(2 : ℝ) / D) + tau - tau * Real.log tau := by
    have := Real.rpow_nonneg (Nat.cast_nonneg L1) (-(2 : ℝ) / D)
    have := Real.rpow_nonneg (Nat.cast_nonneg L2) (-(2 : ℝ) / D)
    have := mul_nonpos_of_nonneg_of_nonpos htau.le hlog
    linarith
  exact (mul_le_mul_of_nonneg_left (by linarith :
    ((if 0 < Finset.univ.sup (dC j) then
      (L1 : ℝ) ^ (-(2 : ℝ) / max 1 (Finset.univ.sup (dC j))) +
      (L2 : ℝ) ^ (-(2 : ℝ) / max 1 (Finset.univ.sup (dC j))) else 0) +
      tau - tau * Real.log tau) ≤
      (L1 : ℝ) ^ (-(2 : ℝ) / D) + (L2 : ℝ) ^ (-(2 : ℝ) / D) +
      tau - tau * Real.log tau) (hA j).le).trans
        (mul_le_mul_of_nonneg_right (hAle j) hnonneg)

end
end Papers.TbsNeuralCausalPi
