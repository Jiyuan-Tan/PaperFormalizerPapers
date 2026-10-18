module
public import Papers.TbsExtremeEffects.Helpers.ThresholdPrefixes
public import Papers.TbsExtremeEffects.Helpers.ThresholdCountable
public import Causalean.Stat.EmpiricalProcess.Countable.FiniteSigns
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Tactic

/-! Conditional-on-observations square bounds for signed threshold processes.
Only finite sign averages are used here, so the fourth-moment intermediate
does not impose any fourth-moment assumption on the observation law. -/

@[expose] public section
noncomputable section
namespace Papers.TbsExtremeEffects
open MeasureTheory
open scoped BigOperators
open Causalean.Stat.EmpiricalProcess.Countable

-- @node: signAverage_square_le
/-- [The square of a finite-sign average is no larger than the finite-sign average of its square](goal). -/
lemma signAverage_square_le {n : ℕ} (H : (Fin n → Bool) → ℝ) :
    signAverage H ^ 2 ≤ signAverage (fun s => H s ^ 2) := by
  have h := sum_div_card_sq_le_sum_sq_div_card
    (s := Finset.univ) (f := H)
  simpa only [signAverage, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using h

-- @node: signedPrefixMax_second_le_energy
/-- [The sign-averaged squared maximum of signed prefix sums is at most four times their coefficient square energy](goal). -/
lemma signedPrefixMax_second_le_energy {n : ℕ} (a : Fin n → ℝ) :
    signAverage (fun s => signedPrefixMax a s ^ 2) ≤ 4 * ∑ i, a i ^ 2 := by
  have hJensen := signAverage_square_le (fun s => signedPrefixMax a s ^ 2)
  have hFourth := signedPrefixMax_fourth_le_energy a
  have hPowers : (fun s => (signedPrefixMax a s ^ 2) ^ 2) =
      (fun s => signedPrefixMax a s ^ 4) := by funext s; ring
  rw [hPowers] at hJensen
  have hEnergy : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hMean : 0 ≤ signAverage (fun s => signedPrefixMax a s ^ 2) :=
    signAverage_nonneg _ (fun _ => sq_nonneg _)
  nlinarith [sq_nonneg (signAverage (fun s => signedPrefixMax a s ^ 2) -
    4 * ∑ i, a i ^ 2)]

-- @node: signAverage_permute
/-- [Permuting the coordinates before evaluating a function leaves its finite-sign average unchanged](goal). -/
lemma signAverage_permute {n : ℕ} (H : (Fin n → Bool) → ℝ)
    (p : Equiv.Perm (Fin n)) :
    signAverage (fun s => H (s ∘ p)) = signAverage H := by
  let e : (Fin n → Bool) ≃ (Fin n → Bool) :=
    { toFun := fun s => s ∘ p
      invFun := fun s => s ∘ p.symm
      left_inv := by intro s; funext i; simp
      right_inv := by intro s; funext i; simp }
  exact congrArg (fun x : ℝ => x / (2 : ℝ) ^ n) (Equiv.sum_comp e H)

/-- [There exists a nonnegative sign-indexed envelope](goal) that dominates every squared signed threshold sum above the lower endpoint and whose sign average is at most four times the clipped square energy. -/
-- @node: threshold_signed_square_envelope
lemma threshold_signed_square_envelope {n : ℕ} (R z : Fin n → ℝ) (ell : ℝ) :
    ∃ H : (Fin n → Bool) → ℝ,
      (∀ s, 0 ≤ H s) ∧
      (∀ s, ∀ t ≥ ell,
        (∑ i : Fin n, if t < R i then
          (if s i then (1 : ℝ) else -1) * z i else 0) ^ 2 ≤ H s) ∧
      signAverage H ≤ 4 * ∑ i : Fin n, if ell < R i then z i ^ 2 else 0 := by
  classical
  obtain ⟨p, hp, _, hEnergy⟩ := threshold_band_signed_prefix_reduction R z ell
  let a : Fin n → ℝ := fun i => if ell < R (p i) then z (p i) else 0
  let H : (Fin n → Bool) → ℝ := fun s => signedPrefixMax a (s ∘ p) ^ 2
  refine ⟨H, fun s => sq_nonneg _, ?_, ?_⟩
  · intro s t ht
    have hPrefix : ∀ k ≤ n,
        |∑ i : Fin n, if i.val < k then
          (if ell < R (p i) then (if s (p i) then (1 : ℝ) else -1) * z (p i)
            else 0) else 0| ≤ signedPrefixMax a (s ∘ p) := by
      intro k hk
      have h := le_ciSup (Finite.bddAbove_range
        (fun k : Fin (n + 1) => |signedPrefix a (s ∘ p) k|))
          (⟨k, by omega⟩ : Fin (n + 1))
      simpa only [signedPrefixMax, signedPrefix, a, Function.comp_apply,
        mul_ite, mul_zero] using h
    have hBound := threshold_band_bound_of_prefix_bound R
      (fun i => (if s i then (1 : ℝ) else -1) * z i) ell
      (signedPrefixMax a (s ∘ p)) p hp hPrefix t ht
    simpa only [H, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hBound 2
  · dsimp only [H]
    rw [signAverage_permute (fun s => signedPrefixMax a s ^ 2) p]
    exact (signedPrefixMax_second_le_energy a).trans_eq (congrArg (4 * ·) hEnergy)

-- @node: thresholdSignedSquareMax
/-- For [radii](hyp:R) and [coefficients](hyp:z) [at the lower endpoint](hyp:ell) and a [sign assignment](hyp:s), [the threshold signed-square maximum](goal) is the supremum of squared signed sums over thresholds at or above that endpoint. -/
def thresholdSignedSquareMax {n : ℕ} (R z : Fin n → ℝ) (ell : ℝ)
    (s : Fin n → Bool) : ℝ :=
  ⨆ t : Set.Ici ell, (∑ i : Fin n, if t.1 < R i then
    (if s i then (1 : ℝ) else -1) * z i else 0) ^ 2

-- @node: thresholdSignedSquareMax_properties
/-- [The threshold signed-square maximum is nonnegative, dominates every eligible threshold sum, and has sign average bounded by four times clipped square energy](goal). -/
lemma thresholdSignedSquareMax_properties {n : ℕ} (R z : Fin n → ℝ) (ell : ℝ) :
    (∀ s, 0 ≤ thresholdSignedSquareMax R z ell s) ∧
    (∀ s, ∀ t ≥ ell,
      (∑ i : Fin n, if t < R i then
        (if s i then (1 : ℝ) else -1) * z i else 0) ^ 2 ≤
          thresholdSignedSquareMax R z ell s) ∧
    signAverage (thresholdSignedSquareMax R z ell) ≤
      4 * ∑ i : Fin n, if ell < R i then z i ^ 2 else 0 := by
  obtain ⟨H, hH0, hDom, hMean⟩ := threshold_signed_square_envelope R z ell
  letI : Nonempty (Set.Ici ell) := ⟨⟨ell, Set.mem_Ici.mpr le_rfl⟩⟩
  have hBdd (s : Fin n → Bool) : BddAbove (Set.range
      (fun t : Set.Ici ell => (∑ i : Fin n, if t.1 < R i then
        (if s i then (1 : ℝ) else -1) * z i else 0) ^ 2)) := by
    refine ⟨H s, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact hDom s t.1 t.2
  have hDomMax : ∀ s, ∀ t ≥ ell,
      (∑ i : Fin n, if t < R i then
        (if s i then (1 : ℝ) else -1) * z i else 0) ^ 2 ≤
          thresholdSignedSquareMax R z ell s := by
    intro s t ht
    exact le_ciSup (hBdd s) (⟨t, ht⟩ : Set.Ici ell)
  refine ⟨fun s => (sq_nonneg _).trans (hDomMax s ell le_rfl), hDomMax, ?_⟩
  apply (signAverage_mono _ H ?_).trans hMean
  intro s
  exact ciSup_le (fun t => hDom s t.1 t.2)

-- @node: measurable_thresholdSignedSquareMax
/-- If every radius coordinate is [measurable](hyp:hR) and every coefficient coordinate is [measurable](hyp:hz), then [the threshold signed-square maximum is measurable](goal). -/
@[fun_prop]
lemma measurable_thresholdSignedSquareMax {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (R z : Ω → Fin n → ℝ) (ell : ℝ) (s : Fin n → Bool)
    (hR : ∀ i, Measurable (fun w => R w i))
    (hz : ∀ i, Measurable (fun w => z w i)) :
    Measurable (fun w => thresholdSignedSquareMax (R w) (z w) ell s) := by
  classical
  obtain ⟨D, hD, hDT, _, hApprox⟩ :=
    exists_countable_oneSided_skeleton true (Set.Ici ell)
  letI : Countable D := hD.to_subtype
  let F : Ω → ℝ → ℝ := fun w t => (∑ i : Fin n, if t < R w i then
    (if s i then (1 : ℝ) else -1) * z w i else 0) ^ 2
  have hEq (w : Ω) : thresholdSignedSquareMax (R w) (z w) ell s =
      ⨆ t : D, F w t.1 := by
    obtain ⟨H, _, hDom, _⟩ := threshold_signed_square_envelope (R w) (z w) ell
    have hBdd : BddAbove (Set.range (fun t : Set.Ici ell => F w t.1)) := by
      refine ⟨H s, ?_⟩
      rintro _ ⟨t, rfl⟩
      exact hDom s t.1 t.2
    have hBddD : BddAbove (Set.range (fun t : D => F w t.1)) := by
      refine ⟨H s, ?_⟩
      rintro _ ⟨t, rfl⟩
      exact hDom s t.1 (hDT t.2)
    obtain ⟨s0, hs0, _⟩ := hApprox ell (Set.mem_Ici.mpr le_rfl)
    letI : Nonempty D := ⟨⟨s0 0, hs0 0⟩⟩
    letI : Nonempty (Set.Ici ell) := ⟨⟨ell, Set.mem_Ici.mpr le_rfl⟩⟩
    apply le_antisymm
    · apply ciSup_le
      intro t
      obtain ⟨v, hvD, hv⟩ := hApprox t.1 t.2
      have hLim : Filter.Tendsto (fun k => F w (v k)) Filter.atTop (nhds (F w t.1)) := by
        apply Filter.Tendsto.pow
        apply tendsto_finsetSum
        intro i _
        have h := thresholdFunction_tendsto true (R w)
          (fun i => (if s i then (1 : ℝ) else -1) * z w i)
          (-(fun i => (if s i then (1 : ℝ) else -1) * z w i)) v t.1 hv i
        simpa only [← strict_threshold_eq_affine_closed] using h
      exact le_of_tendsto hLim (Filter.Eventually.of_forall (fun k =>
        le_ciSup hBddD (⟨v k, hvD k⟩ : D)))
    · exact ciSup_le (fun t => le_ciSup hBdd (⟨t.1, hDT t.2⟩ : Set.Ici ell))
  simp_rw [hEq]
  apply Measurable.iSup
  intro t
  dsimp only [F]
  first | fun_prop | skip
  apply Measurable.pow_const
  apply Finset.measurable_fun_sum
  intro i _
  exact Measurable.ite (measurableSet_lt measurable_const (hR i))
    ((hz i).const_mul _) measurable_const

/-- If the sign-averaged maximum is [almost-everywhere strongly measurable](hyp:hMeas) and the clipped square energy is [integrable](hyp:hEnergy), then [the former is integrable and its integral is at most four times the latter's integral](goal). -/
-- @node: integral_thresholdSignedSquareMax_le_energy
lemma integral_thresholdSignedSquareMax_le_energy {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {n : ℕ} (R z : Ω → Fin n → ℝ) (ell : ℝ)
    (hMeas : AEStronglyMeasurable
      (fun w => signAverage (thresholdSignedSquareMax (R w) (z w) ell)) P)
    (hEnergy : Integrable
      (fun w => ∑ i : Fin n, if ell < R w i then z w i ^ 2 else 0) P) :
    Integrable (fun w => signAverage (thresholdSignedSquareMax (R w) (z w) ell)) P ∧
    (∫ w, signAverage (thresholdSignedSquareMax (R w) (z w) ell) ∂P) ≤
      4 * ∫ w, (∑ i : Fin n, if ell < R w i then z w i ^ 2 else 0) ∂P := by
  have hNonneg : ∀ w, 0 ≤ signAverage (thresholdSignedSquareMax (R w) (z w) ell) :=
    fun w => signAverage_nonneg _ (thresholdSignedSquareMax_properties (R w) (z w) ell).1
  have hBound := fun w => (thresholdSignedSquareMax_properties (R w) (z w) ell).2.2
  have hInt : Integrable
      (fun w => signAverage (thresholdSignedSquareMax (R w) (z w) ell)) P := by
    apply (hEnergy.const_mul 4).mono' hMeas
    exact Filter.Eventually.of_forall (fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hNonneg w)]
      exact hBound w)
  refine ⟨hInt, ?_⟩
  calc
    _ ≤ ∫ w, 4 * (∑ i : Fin n, if ell < R w i then z w i ^ 2 else 0) ∂P :=
      integral_mono hInt (hEnergy.const_mul 4) hBound
    _ = _ := integral_const_mul _ _

/-- If each radius coordinate is [measurable](hyp:hR), each coefficient coordinate is [measurable](hyp:hz), [the target integral is at most four times the integral of the signed clipped-square maximum](hyp:hSymm), clipped square energy is [integrable](hyp:hEnergy), and its integral is [at most the supplied constant](hyp:hMean), then [the integral of the target process is at most sixteen times that constant](goal). -/
-- @node: square_integral_of_threshold_symmetrization
lemma square_integral_of_threshold_symmetrization {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {n : ℕ} (R z : Ω → Fin n → ℝ) (ell : ℝ)
    (hR : ∀ i, Measurable (fun w => R w i))
    (hz : ∀ i, Measurable (fun w => z w i))
    (H : Ω → ℝ) {K : ℝ}
    (hSymm : (∫ w, H w ∂P) ≤
      4 * ∫ w, signAverage (thresholdSignedSquareMax (R w) (z w) ell) ∂P)
    (hEnergy : Integrable
      (fun w => ∑ i : Fin n, if ell < R w i then z w i ^ 2 else 0) P)
    (hMean : (∫ w, (∑ i : Fin n, if ell < R w i then z w i ^ 2 else 0) ∂P) ≤ K) :
    (∫ w, H w ∂P) ≤ 16 * K := by
  have hMeas : Measurable
      (fun w => signAverage (thresholdSignedSquareMax (R w) (z w) ell)) := by
    first | fun_prop | skip
    unfold signAverage
    apply Measurable.div_const
    exact Finset.measurable_fun_sum _ (fun s _ =>
      measurable_thresholdSignedSquareMax R z ell s hR hz)
  have hSigned := (integral_thresholdSignedSquareMax_le_energy P R z ell
    hMeas.aestronglyMeasurable hEnergy).2
  calc
    _ ≤ 4 * ∫ w, signAverage (thresholdSignedSquareMax (R w) (z w) ell) ∂P := hSymm
    _ ≤ 4 * (4 * ∫ w, (∑ i : Fin n, if ell < R w i then z w i ^ 2 else 0) ∂P) :=
      mul_le_mul_of_nonneg_left hSigned (by norm_num)
    _ ≤ 4 * (4 * K) := by gcongr
    _ = _ := by ring

end Papers.TbsExtremeEffects
