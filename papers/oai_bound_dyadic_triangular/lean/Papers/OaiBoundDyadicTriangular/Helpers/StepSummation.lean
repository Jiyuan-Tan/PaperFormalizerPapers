module

public import Papers.OaiBoundDyadicTriangular.Helpers.AtomTrace
public import Papers.OaiBoundDyadicTriangular.TIncrease
public import Papers.OaiBoundDyadicTriangular.Helpers.Summation
public import Papers.OaiBoundDyadicTriangular.Helpers.Continuity

/-! # Summing the increment estimate for dyadic step inputs -/

public section

open MeasureTheory
open scoped BigOperators

namespace Papers.OaiBoundDyadicTriangular

-- @node: energyIncrement_summable
/-- For [three real functions of two variables](hyp:F), [a comparison scale](hyp:k),
and [an atom scale](hyp:m), if [each function vanishes outside a bounded square
in the nonnegative quadrant](hyp:hCompact), then [the energy increments form an
absolutely summable family over admissible dyadic interval triples](goal). -/
lemma energyIncrement_summable (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (hCompact : StepCompact F) :
    Summable (fun n : admissibleSet => energyIncrement F k m n.val) := by
  exact ((summable_children_and_tsum (localEnergy F (k - 1) m)
    (localEnergy_summable F (k - 1) m hCompact)).1.mul_left (1 / 4 : ℝ)).sub
      (localEnergy_summable F k m hCompact)

-- @node: step_localForm_sum_le_energy_difference
/-- For [three real functions of two variables](hyp:F), [a comparison scale](hyp:k),
[an atom scale](hyp:m), and [a finite collection of admissible interval triples](hyp:T),
assume [the functions are bounded on the nonnegative quadrant](hyp:hBounded),
[vanish there outside bounded squares](hyp:hCompact), and [are constant on dyadic
atom rectangles at the atom scale](hyp:hAtoms), [the comparison scale is at least
one greater than the atom scale](hyp:hScale), and [the Haar signs are positive on
left halves and negative on right halves](hyp:hHalves). Then [the total energy
at the preceding scale minus that at the comparison scale is nonnegative, and
the sum of the absolute local forms over the chosen triples is at most ten times
the square root of two divided by three times this energy difference](goal). -/
lemma step_localForm_sum_le_energy_difference (F : Fin 3 → ℝ × ℝ → ℝ) (k m : ℤ)
    (hBounded : StepBounded F) (hCompact : StepCompact F) (hAtoms : StepAtoms F m)
    (hScale : IncreaseScale k m) (hHalves : HaarHalvesConvention)
    (T : Finset admissibleSet) :
    0 ≤ totalEnergy F (k - 1) m - totalEnergy F k m ∧
    (∑ n ∈ T, |localForm k n.val F|) ≤
      (10 * Real.sqrt 2 / 3) * (totalEnergy F (k - 1) m - totalEnergy F k m) := by
  have hInc := fun n : admissibleSet => energyIncrement_controls_trace F k m n.val
    hBounded hCompact hAtoms n.property hScale hHalves
  have hNonneg (n : admissibleSet) :
      0 ≤ (2 : ℝ) ^ (2 * k) * energyIncrement F k m n.val :=
    mul_nonneg (by positivity) (hInc n).1
  have hSum := (energyIncrement_summable F k m hCompact).mul_left ((2 : ℝ) ^ (2 * k))
  have hTel := totalEnergy_telescope F k m hCompact
  refine ⟨?_, ?_⟩
  · rw [← hTel]
    exact tsum_nonneg hNonneg
  · calc
      _ ≤ ∑ n ∈ T, (10 * Real.sqrt 2 / 3) *
          ((2 : ℝ) ^ (2 * k) * energyIncrement F k m n.val) := by
        apply Finset.sum_le_sum
        intro n _
        rw [localForm_eq_traceNormalizedForm F k m n.val hAtoms n.property hScale hHalves,
          traceNormalizedForm, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ (2 * k))]
        calc
          _ ≤ (2 : ℝ) ^ (2 * k) *
              ((10 * Real.sqrt 2 / 3) * energyIncrement F k m n.val) :=
            mul_le_mul_of_nonneg_left (hInc n).2 (by positivity)
          _ = _ := by ring
      _ = (10 * Real.sqrt 2 / 3) *
          ∑ n ∈ T, (2 : ℝ) ^ (2 * k) * energyIncrement F k m n.val := by
        rw [Finset.mul_sum]
      _ ≤ (10 * Real.sqrt 2 / 3) *
          ∑' n : admissibleSet, (2 : ℝ) ^ (2 * k) * energyIncrement F k m n.val :=
        mul_le_mul_of_nonneg_left (hSum.sum_le_tsum T (fun n _ => hNonneg n))
          (by positivity)
      _ = _ := by rw [hTel]

-- @node: step_localForm_range_bound
/-- For [three real functions of two variables](hyp:F), [an atom scale](hyp:m),
[a nonnegative number of consecutive scales](hyp:N), and [a finite collection of
admissible interval triples at each integer scale](hyp:T), assume [the functions
are bounded on the nonnegative quadrant](hyp:hBounded), [vanish there outside
bounded squares](hyp:hCompact), [are constant on dyadic atom rectangles at the
atom scale](hyp:hAtoms), and [the Haar signs are positive on left halves and
negative on right halves](hyp:hHalves). Then [the sum of the absolute local forms
over the chosen triples at the specified number of scales starting one above
the atom scale is at most forty thirds times the sum of the cubes of the three
L³ norms on the quadrant](goal). -/
lemma step_localForm_range_bound (F : Fin 3 → ℝ × ℝ → ℝ) (m : ℤ) (N : ℕ)
    (hBounded : StepBounded F) (hCompact : StepCompact F) (hAtoms : StepAtoms F m)
    (hHalves : HaarHalvesConvention) (T : ℤ → Finset admissibleSet) :
    (∑ i ∈ Finset.range N, ∑ n ∈ T (m + 1 + i), |localForm (m + 1 + i) n.val F|) ≤
      (40 / 3 : ℝ) * ∑ v : Fin 3, (eLpNorm (F v) 3 quadrantMeasure).toReal ^ 3 := by
  have hScale (i : ℕ) : IncreaseScale (m + 1 + i) m := by
    unfold IncreaseScale
    omega
  have hStep := fun i : ℕ => (step_localForm_sum_le_energy_difference F (m + 1 + i) m
    hBounded hCompact hAtoms (hScale i) hHalves (T (m + 1 + i))).2
  have hTel : (∑ i ∈ Finset.range N,
      (totalEnergy F (m + 1 + i - 1) m - totalEnergy F (m + 1 + i) m)) =
      totalEnergy F m m - totalEnergy F (m + N) m := by
    calc
      _ = ∑ i ∈ Finset.range N,
          (totalEnergy F (m + i) m - totalEnergy F (m + (i + 1 : ℕ)) m) := by
        apply Finset.sum_congr rfl
        intro i _
        congr 2 <;> push_cast <;> ring
      _ = _ := by
        simpa only [Nat.cast_zero, add_zero] using
          Finset.sum_range_sub' (fun i : ℕ => totalEnergy F (m + i) m) N
  have hTotal := ((totalEnergy_bound_and_telescope F m m hBounded hCompact hAtoms).1
    (show TotalScale m m from le_rfl)).2
  calc
    _ ≤ ∑ i ∈ Finset.range N, (10 * Real.sqrt 2 / 3) *
        (totalEnergy F (m + 1 + i - 1) m - totalEnergy F (m + 1 + i) m) :=
      Finset.sum_le_sum fun i _ => hStep i
    _ = (10 * Real.sqrt 2 / 3) *
        (totalEnergy F m m - totalEnergy F (m + N) m) := by
      rw [← Finset.mul_sum, hTel]
    _ ≤ (10 * Real.sqrt 2 / 3) * totalEnergy F m m :=
      mul_le_mul_of_nonneg_left (sub_le_self _ (totalEnergy_nonneg F (m + N) m))
        (by positivity)
    _ ≤ (10 * Real.sqrt 2 / 3) * (2 * Real.sqrt 2 *
        ∑ v : Fin 3, (eLpNorm (F v) 3 quadrantMeasure).toReal ^ 3) :=
      mul_le_mul_of_nonneg_left hTotal (by positivity)
    _ = (20 / 3 : ℝ) * (Real.sqrt 2) ^ 2 *
        ∑ v : Fin 3, (eLpNorm (F v) 3 quadrantMeasure).toReal ^ 3 := by ring
    _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring

-- @node: step_localForm_additive_bound
/-- For [a finite set of integer scales](hyp:S), [three real functions of two variables](hyp:F),
[an atom scale](hyp:m), and [a finite collection of admissible interval triples
at each scale](hyp:T), assume [the functions are bounded on the nonnegative quadrant](hyp:hBounded),
[vanish there outside bounded squares](hyp:hCompact), [are constant on dyadic
atom rectangles at the atom scale](hyp:hAtoms), [every chosen scale is at least
one greater than the atom scale](hyp:hScale), and [the Haar signs are positive
on left halves and negative on right halves](hyp:hHalves). Then [the sum of the
absolute local forms over the chosen scales and triples is at most forty thirds
times the sum of the cubes of the three L³ norms on the quadrant](goal). -/
lemma step_localForm_additive_bound (S : Finset ℤ) (F : Fin 3 → ℝ × ℝ → ℝ) (m : ℤ)
    (hBounded : StepBounded F) (hCompact : StepCompact F) (hAtoms : StepAtoms F m)
    (hScale : ∀ k ∈ S, m + 1 ≤ k) (hHalves : HaarHalvesConvention)
    (T : ℤ → Finset admissibleSet) :
    (∑ k ∈ S, ∑ n ∈ T k, |localForm k n.val F|) ≤
      (40 / 3 : ℝ) * ∑ v : Fin 3, (eLpNorm (F v) 3 quadrantMeasure).toReal ^ 3 := by
  classical
  let N := S.sup (fun k => (k - m).toNat) + 1
  have hSubset : S ⊆ (Finset.range N).image (fun i : ℕ => m + 1 + i) := by
    intro k hk
    have hLower := hScale k hk
    have hUpper : (k - m).toNat < N :=
      Nat.lt_succ_of_le (Finset.le_sup (f := fun k => (k - m).toNat) hk)
    apply Finset.mem_image.mpr
    refine ⟨(k - m - 1).toNat, Finset.mem_range.mpr ?_, ?_⟩ <;> omega
  calc
    _ ≤ ∑ k ∈ (Finset.range N).image (fun i : ℕ => m + 1 + i),
        ∑ n ∈ T k, |localForm k n.val F| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hSubset
      intro k _ _
      exact Finset.sum_nonneg fun n _ => abs_nonneg _
    _ = ∑ i ∈ Finset.range N, ∑ n ∈ T (m + 1 + i),
        |localForm (m + 1 + i) n.val F| := by
      rw [Finset.sum_image]
      intro i _ j _ hij
      dsimp at hij
      omega
    _ ≤ _ := step_localForm_range_bound F m N hBounded hCompact hAtoms hHalves T


-- @node: stepBounded_scale_inputs
/-- For [three real functions of two variables](hyp:F) and [one real multiplier
for each function](hyp:c), if [each function is bounded on the nonnegative quadrant](hyp:hF),
then [multiplying each function by its multiplier preserves boundedness on that quadrant](goal). -/
lemma stepBounded_scale_inputs (F : Fin 3 → ℝ × ℝ → ℝ) (c : Fin 3 → ℝ)
    (hF : StepBounded F) : StepBounded (fun v x => c v * F v x) := by
  intro v
  obtain ⟨C, hC⟩ := hF v
  refine ⟨|c v| * C, fun x hx => ?_⟩
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hC x hx) (abs_nonneg _)

-- @node: stepCompact_scale_inputs
/-- For [three real functions of two variables](hyp:F) and [one real multiplier
for each function](hyp:c), if [each function vanishes outside a bounded square
in the nonnegative quadrant](hyp:hF), then [the multiplied functions also vanish
outside bounded squares in that quadrant](goal). -/
lemma stepCompact_scale_inputs (F : Fin 3 → ℝ × ℝ → ℝ) (c : Fin 3 → ℝ)
    (hF : StepCompact F) : StepCompact (fun v x => c v * F v x) := by
  intro v
  obtain ⟨R, hR⟩ := hF v
  exact ⟨R, fun x hx hy h => by dsimp only; rw [hR x hx hy h, mul_zero]⟩

-- @node: stepAtoms_scale_inputs
/-- For [three real functions of two variables](hyp:F), [one real multiplier for
each function](hyp:c), and [an integer atom scale](hyp:m), if [each function is
constant on every dyadic atom rectangle at that scale](hyp:hF), then [multiplying
each function by its multiplier preserves constancy on those rectangles](goal). -/
lemma stepAtoms_scale_inputs (F : Fin 3 → ℝ × ℝ → ℝ) (c : Fin 3 → ℝ) (m : ℤ)
    (hF : StepAtoms F m) : StepAtoms (fun v x => c v * F v x) m := by
  intro v a b x y hx hy
  dsimp only
  rw [hF v a b x y hx hy]

-- @node: localForm_scale_inputs
/-- For [an integer scale](hyp:k), [three dyadic interval indices](hyp:n),
[three real functions of two variables](hyp:F), and [one real multiplier for
each function](hyp:c), [the local form of the multiplied functions equals the
product of the three multipliers times the original local form](goal). -/
lemma localForm_scale_inputs (k : ℤ) (n : Fin 3 → ℕ)
    (F : Fin 3 → ℝ × ℝ → ℝ) (c : Fin 3 → ℝ) :
    localForm k n (fun v x => c v * F v x) = (∏ v, c v) * localForm k n F := by
  have h : (fun x : ℝ × (ℝ × ℝ) =>
      (c 0 * F 0 (x.1, x.2.1)) * (c 1 * F 1 (x.2.1, x.2.2)) *
        (c 2 * F 2 (x.2.2, x.1)) *
        haarSign k (n 0) x.1 * haarSign k (n 1) x.2.1 * haarSign k (n 2) x.2.2) =
      (fun x => (∏ v, c v) *
        (F 0 (x.1, x.2.1) * F 1 (x.2.1, x.2.2) * F 2 (x.2.2, x.1) *
          haarSign k (n 0) x.1 * haarSign k (n 1) x.2.1 * haarSign k (n 2) x.2.2)) := by
    funext x
    rw [Fin.prod_univ_three]
    ring
  unfold localForm
  rw [h, integral_const_mul]
  ring

-- @node: eLpNorm_scale_toReal
/-- For [a real function of two variables](hyp:f) and [a real multiplier](hyp:c),
[the real value of the extended L³ norm on the nonnegative quadrant of the
multiplied function equals the absolute multiplier times the real value of the
original extended L³ norm](goal).

Here the real value of an infinite extended norm is defined to be zero. -/
lemma eLpNorm_scale_toReal (f : ℝ × ℝ → ℝ) (c : ℝ) :
    (eLpNorm (fun x => c * f x) 3 quadrantMeasure).toReal =
      |c| * (eLpNorm f 3 quadrantMeasure).toReal := by
  change (eLpNorm (c • f) 3 quadrantMeasure).toReal = _
  rw [eLpNorm_const_smul, ENNReal.toReal_mul, toReal_enorm, Real.norm_eq_abs]

-- @node: step_localForm_bound_of_norm_ne_zero
/-- For [a finite set of integer scales](hyp:S), [three real functions of two variables](hyp:F),
[an atom scale](hyp:m), and [a finite collection of admissible interval triples
at each scale](hyp:T), assume [the functions are bounded on the nonnegative quadrant](hyp:hBounded),
[vanish there outside bounded squares](hyp:hCompact), [are constant on dyadic
atom rectangles at the atom scale](hyp:hAtoms), [each chosen scale is at least
one greater than the atom scale](hyp:hScale), [the Haar signs are positive on
left halves and negative on right halves](hyp:hHalves), and [the real values of
all three extended L³ norms on the quadrant are nonzero](hyp:hNorm). Then [the
sum of the absolute local forms over the chosen scales and triples is at most
forty times the product of those three norm values](goal). -/
lemma step_localForm_bound_of_norm_ne_zero (S : Finset ℤ)
    (F : Fin 3 → ℝ × ℝ → ℝ) (m : ℤ)
    (hBounded : StepBounded F) (hCompact : StepCompact F) (hAtoms : StepAtoms F m)
    (hScale : ∀ k ∈ S, m + 1 ≤ k) (hHalves : HaarHalvesConvention)
    (hNorm : ∀ v, (eLpNorm (F v) 3 quadrantMeasure).toReal ≠ 0)
    (T : ℤ → Finset admissibleSet) :
    (∑ k ∈ S, ∑ n ∈ T k, |localForm k n.val F|) ≤
      40 * ∏ v : Fin 3, (eLpNorm (F v) 3 quadrantMeasure).toReal := by
  let c : Fin 3 → ℝ := fun v => (eLpNorm (F v) 3 quadrantMeasure).toReal⁻¹
  let G : Fin 3 → ℝ × ℝ → ℝ := fun v x => c v * F v x
  have hGn (v : Fin 3) : (eLpNorm (G v) 3 quadrantMeasure).toReal = 1 := by
    rw [eLpNorm_scale_toReal]
    dsimp [c]
    rw [abs_inv, abs_of_nonneg ENNReal.toReal_nonneg, inv_mul_cancel₀ (hNorm v)]
  have hBound := step_localForm_additive_bound S G m
    (stepBounded_scale_inputs F c hBounded) (stepCompact_scale_inputs F c hCompact)
    (stepAtoms_scale_inputs F c m hAtoms) hScale hHalves T
  have hUnit : (∑ k ∈ S, ∑ n ∈ T k, |localForm k n.val G|) ≤ 40 := by
    simpa [hGn, Fin.sum_univ_three] using hBound
  have hProd : 0 < ∏ v, (eLpNorm (F v) 3 quadrantMeasure).toReal :=
    Finset.prod_pos fun v _ => lt_of_le_of_ne ENNReal.toReal_nonneg (hNorm v).symm
  have hRescale : (∑ k ∈ S, ∑ n ∈ T k, |localForm k n.val G|) =
      (∏ v, (eLpNorm (F v) 3 quadrantMeasure).toReal)⁻¹ *
        ∑ k ∈ S, ∑ n ∈ T k, |localForm k n.val F| := by
    simp only [G, localForm_scale_inputs, abs_mul]
    simp_rw [← Finset.mul_sum]
    congr 1
    rw [abs_of_pos (Finset.prod_pos fun v _ => inv_pos.mpr
      (lt_of_le_of_ne ENNReal.toReal_nonneg (hNorm v).symm))]
    simp only [Finset.prod_inv_distrib]
  rw [hRescale] at hUnit
  apply (div_le_iff₀ hProd).mp
  simpa only [div_eq_mul_inv, mul_comm] using hUnit

-- @node: step_localForm_bound
/-- For [a finite set of integer scales](hyp:S), [three real functions of two variables](hyp:F),
[an atom scale](hyp:m), and [a finite collection of admissible interval triples
at each scale](hyp:T), assume [the functions are bounded on the nonnegative quadrant](hyp:hBounded),
[vanish there outside bounded squares](hyp:hCompact), [are constant on dyadic
atom rectangles at the atom scale](hyp:hAtoms), [are measurable up to null sets
and have finite integrals of their absolute cubes on the quadrant](hyp:hInputs),
[each chosen scale is at least one greater than the atom scale](hyp:hScale), and
[the Haar signs are positive on left halves and negative on right halves](hyp:hHalves).
Then [the sum of the absolute local forms over the chosen scales and triples is
at most forty times the product of the three L³ norms on the quadrant](goal). -/
lemma step_localForm_bound (S : Finset ℤ) (F : Fin 3 → ℝ × ℝ → ℝ) (m : ℤ)
    (hBounded : StepBounded F) (hCompact : StepCompact F) (hAtoms : StepAtoms F m)
    (hInputs : ContinuityInputs F) (hScale : ∀ k ∈ S, m + 1 ≤ k)
    (hHalves : HaarHalvesConvention) (T : ℤ → Finset admissibleSet) :
    (∑ k ∈ S, ∑ n ∈ T k, |localForm k n.val F|) ≤
      40 * ∏ v : Fin 3, (eLpNorm (F v) 3 quadrantMeasure).toReal := by
  classical
  by_cases hNorm : ∀ v, (eLpNorm (F v) 3 quadrantMeasure).toReal ≠ 0
  · exact step_localForm_bound_of_norm_ne_zero S F m hBounded hCompact hAtoms
      hScale hHalves hNorm T
  · push Not at hNorm
    obtain ⟨v, hv⟩ := hNorm
    have hProd : (∏ w : Fin 3, (eLpNorm (F w) 3 quadrantMeasure).toReal) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ v) hv
    rw [hProd, mul_zero]
    calc
      _ ≤ ∑ k ∈ S, ∏ w : Fin 3, (eLpNorm (F w) 3 quadrantMeasure).toReal :=
        Finset.sum_le_sum fun k _ => localForm_one_scale_sum_bound k F hInputs (T k)
      _ = 0 := by simp only [hProd, Finset.sum_const_zero]

-- @node: localForm_tendsto_of_L3_approximation
/-- For [three real functions of two variables](hyp:F), [a sequence of triples
of approximating functions](hyp:G), [an integer scale](hyp:k), and [an admissible
triple of dyadic interval indices](hyp:n), assume [the limiting functions are
measurable up to null sets and have finite integrals of their absolute cubes
on the nonnegative quadrant](hyp:hF), [every approximating triple has these same
properties](hyp:hG), and [the Haar signs are positive on left halves and negative
on right halves](hyp:hHalves). If [each approximation error has L³ norm tending
to zero on the quadrant](hyp:hDiff) and [each approximating L³ norm converges to
the corresponding limiting norm](hyp:hNorm), then [the local forms of the
approximating triples converge to the local form of the limiting triple at
the chosen scale and interval indices](goal). -/
lemma localForm_tendsto_of_L3_approximation (F : Fin 3 → ℝ × ℝ → ℝ)
    (G : ℕ → Fin 3 → ℝ × ℝ → ℝ) (hF : ContinuityInputs F)
    (hG : ∀ j, ContinuityInputs (G j)) (hHalves : HaarHalvesConvention)
    (hDiff : ∀ v, Filter.Tendsto
      (fun j => (eLpNorm (fun x => G j v x - F v x) 3 quadrantMeasure).toReal)
      Filter.atTop (nhds 0))
    (hNorm : ∀ v, Filter.Tendsto
      (fun j => (eLpNorm (G j v) 3 quadrantMeasure).toReal)
      Filter.atTop (nhds ((eLpNorm (F v) 3 quadrantMeasure).toReal)))
    (k : ℤ) (n : admissibleSet) :
    Filter.Tendsto (fun j => localForm k n.val (G j))
      Filter.atTop (nhds (localForm k n.val F)) := by
  have hBound (j : ℕ) :=
    (localForm_one_scale_bound k (G j) (Set.mem_univ k) (hG j) hHalves).2 F hF {n}
  have hZero := (((hDiff 0).mul (hNorm 1)).mul (hNorm 2)).add
    (((hDiff 1).const_mul ((eLpNorm (F 0) 3 quadrantMeasure).toReal)).mul (hNorm 2))
  have hLimit : Filter.Tendsto (fun j =>
      (eLpNorm (fun x => G j 0 x - F 0 x) 3 quadrantMeasure).toReal *
        (eLpNorm (G j 1) 3 quadrantMeasure).toReal *
        (eLpNorm (G j 2) 3 quadrantMeasure).toReal +
      (eLpNorm (F 0) 3 quadrantMeasure).toReal *
        (eLpNorm (fun x => G j 1 x - F 1 x) 3 quadrantMeasure).toReal *
        (eLpNorm (G j 2) 3 quadrantMeasure).toReal +
      (eLpNorm (F 0) 3 quadrantMeasure).toReal *
        (eLpNorm (F 1) 3 quadrantMeasure).toReal *
        (eLpNorm (fun x => G j 2 x - F 2 x) 3 quadrantMeasure).toReal)
      Filter.atTop (nhds 0) := by
    simpa only [zero_mul, mul_zero, add_zero, zero_add] using
      hZero.add ((hDiff 2).const_mul
        ((eLpNorm (F 0) 3 quadrantMeasure).toReal * (eLpNorm (F 1) 3 quadrantMeasure).toReal))
  have hAbs : Filter.Tendsto (fun j => |localForm k n.val (G j) - localForm k n.val F|)
      Filter.atTop (nhds 0) :=
    squeeze_zero (fun _ => abs_nonneg _) (fun j => by simpa using hBound j) hLimit
  exact (tendsto_iff_dist_tendsto_zero).mpr (by simpa only [Real.dist_eq] using hAbs)

-- @node: dyadic_bound_of_step_approximation
/-- For [a finite set of integer scales](hyp:S), [three limiting real functions
of two variables](hyp:F), [a sequence of approximating triples](hyp:G),
[an integer atom scale for each approximating triple](hyp:m), and [a finite
collection of admissible interval triples at each scale](hyp:T), assume [the
limiting functions are measurable up to null sets and have finite integrals
of their absolute cubes on the nonnegative quadrant](hyp:hF), [each approximating
triple is bounded on the quadrant, vanishes there outside bounded squares, is
constant on dyadic rectangles at its atom scale, and is measurable up to null
sets with finite integrals of its absolute cubes](hyp:hG), [every chosen scale
is at least one greater than every approximating atom scale](hyp:hScale), and
[the Haar signs are positive on left halves and negative on right halves](hyp:hHalves).
If [each approximation error has L³ norm tending to zero on the quadrant](hyp:hDiff)
and [each approximating L³ norm converges to its limiting norm](hyp:hNorm), then
[the sum of the absolute local forms of the limiting triple over the chosen
scales and interval triples is at most forty times the product of the three
limiting L³ norms on the quadrant](goal). -/
lemma dyadic_bound_of_step_approximation (S : Finset ℤ) (F : Fin 3 → ℝ × ℝ → ℝ)
    (G : ℕ → Fin 3 → ℝ × ℝ → ℝ) (m : ℕ → ℤ)
    (hF : ContinuityInputs F)
    (hG : ∀ j, StepBounded (G j) ∧ StepCompact (G j) ∧
      StepAtoms (G j) (m j) ∧ ContinuityInputs (G j))
    (hScale : ∀ j k, k ∈ S → m j + 1 ≤ k) (hHalves : HaarHalvesConvention)
    (hDiff : ∀ v, Filter.Tendsto
      (fun j => (eLpNorm (fun x => G j v x - F v x) 3 quadrantMeasure).toReal)
      Filter.atTop (nhds 0))
    (hNorm : ∀ v, Filter.Tendsto
      (fun j => (eLpNorm (G j v) 3 quadrantMeasure).toReal)
      Filter.atTop (nhds ((eLpNorm (F v) 3 quadrantMeasure).toReal)))
    (T : ℤ → Finset admissibleSet) :
    (∑ k ∈ S, ∑ n ∈ T k, |localForm k n.val F|) ≤
      40 * ∏ v : Fin 3, (eLpNorm (F v) 3 quadrantMeasure).toReal := by
  have hLocal := localForm_tendsto_of_L3_approximation F G hF
    (fun j => (hG j).2.2.2) hHalves hDiff hNorm
  have hLeft : Filter.Tendsto
      (fun j => ∑ k ∈ S, ∑ n ∈ T k, |localForm k n.val (G j)|)
      Filter.atTop (nhds (∑ k ∈ S, ∑ n ∈ T k, |localForm k n.val F|)) :=
    tendsto_finsetSum S fun k _ => tendsto_finsetSum (T k) fun n _ => (hLocal k n).abs
  have hRight : Filter.Tendsto
      (fun j => 40 * ∏ v : Fin 3, (eLpNorm (G j v) 3 quadrantMeasure).toReal)
      Filter.atTop (nhds (40 * ∏ v : Fin 3, (eLpNorm (F v) 3 quadrantMeasure).toReal)) :=
    tendsto_const_nhds.mul (tendsto_finsetProd Finset.univ fun v _ => hNorm v)
  apply le_of_tendsto_of_tendsto hLeft hRight
  exact Filter.Eventually.of_forall fun j => step_localForm_bound S (G j) (m j)
    (hG j).1 (hG j).2.1 (hG j).2.2.1 (hG j).2.2.2 (hScale j) hHalves T

end Papers.OaiBoundDyadicTriangular
