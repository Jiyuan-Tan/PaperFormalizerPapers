module

public import Papers.OaiLinearVarianceRandom.Helpers.HittingMoments

/-! # A uniform first-moment tail and the error from the linear cap -/

public section

namespace Papers.OaiLinearVarianceRandom
open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {n : ℕ} {Ω : Type} [MeasurableSpace Ω]

/-- With [at least three variables](hyp:hn), [for every assignment there is a
finite family of clauses, all falsified by that assignment, whose uniform
clause probability is one eighth](goal). -/
-- @node: exists_falsifying_clause_family
lemma exists_falsifying_clause_family (hn : MainN n) (z : Fin n → Bool) :
    ∃ B : Finset (ProperClause n),
      (∀ c ∈ B, ¬ ClauseSat c z) ∧ (uniformClauseMeasure n 3).real B = 1 / 8 := by
  classical
  let T := {s : Finset (Fin n) // s.card = 3}
  let bad : T → ProperClause n := fun s => properClauseOfSigns s (fun v => !(z v.val))
  have hinj : Function.Injective bad := by
    intro s t h
    have hs : (⟨s, fun v => !(z v.val)⟩ : Σ s : T, s.val → Bool) =
        ⟨t, fun v => !(z v.val)⟩ := (properClauseOfSigns_bijective n 3).1 h
    exact congrArg Sigma.fst hs
  let B := Finset.univ.image bad
  refine ⟨B, ?_, ?_⟩
  · intro c hc
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hc
    rintro ⟨l, hl, hs⟩
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hl
    have he : z v.val = !(z v.val) := hs
    cases hz : z v.val <;> simp [hz] at he
  · have hcard : B.card = n.choose 3 := by
      rw [Finset.card_image_of_injective _ hinj]
      simp [T, Fintype.card_finset_len]
    haveI : Nonempty (ProperClause n) := properClauseA_nonempty n 3 hn
    have hchoose : (n.choose 3 : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hn))
    simp only [uniformClauseMeasure, uniformOn_univ, measureReal_def,
      ENNReal.toReal_div, Measure.count_apply_finset, ENNReal.toReal_natCast,
      Measure.count_univ, Nat.card_eq_fintype_card, card_properClauseA, hcard]
    push_cast
    field_simp
    <;> ring

/-- With [at least three variables](hyp:hn) and [an independent uniform clause
process](hyp:hlaw), [the probability that the first unsatisfiable time exceeds
a given nonnegative integer is at most two to the number of variables times
seven eighths to that integer power](goal). -/
-- @node: hittingTime_uniform_tail
lemma hittingTime_uniform_tail (hn : MainN n)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Cseq : ℕ → Ω → ProperClause n) (hlaw : IsUniformClauseProcess μ Cseq) (m : ℕ) :
    μ.real {ω | m < hittingTime (fun j => Cseq j ω)} ≤
      (2 : ℝ) ^ n * (7 / 8 : ℝ) ^ m := by
  classical
  let ν := uniformClauseMeasure n 3
  haveI : Nonempty (ProperClause n) := properClauseA_nonempty n 3 hn
  haveI : IsProbabilityMeasure ν := by dsimp [ν, uniformClauseMeasure]; infer_instance
  choose B hbad hB using exists_falsifying_clause_family hn
  let E : (Fin n → Bool) → Set Ω := fun z =>
    {ω | ∀ j : Fin m, Cseq (j.val + 1) ω ∉ B z}
  have hmass (z : Fin n → Bool) : μ.real (E z) = (7 / 8 : ℝ) ^ m := by
    have h := clauseProcess_joint_mass μ Cseq hlaw
      (fun j : Fin m => j.val + 1) (by intro a b h; apply Fin.ext; exact Nat.add_right_cancel h)
      (fun _ => by omega) (fun _ => ((B z : Set (ProperClause n)))ᶜ)
    have hs : ν.real ((B z : Set (ProperClause n))ᶜ) = 7 / 8 := by
      rw [measureReal_compl (by trivial), hB z]
      norm_num
    change (μ (E z)).toReal = _
    rw [show μ (E z) = ∏ _j : Fin m, ν ((B z : Set (ProperClause n))ᶜ) by
      simpa [E, ν] using h, ENNReal.toReal_prod]
    simp only [← measureReal_def, hs, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsub : {ω | m < hittingTime (fun j => Cseq j ω)} ⊆ ⋃ z, E z := by
    intro ω hω
    obtain ⟨z, hz⟩ := prefixSat_of_lt_hittingTime _ m hω
    refine Set.mem_iUnion.mpr ⟨z, ?_⟩
    intro j hc
    exact hbad z _ hc (hz (j.val + 1) (Finset.mem_Icc.mpr ⟨by omega, j.isLt⟩))
  calc
    _ ≤ μ.real (⋃ z, E z) := measureReal_mono hsub
    _ ≤ ∑ z : Fin n → Bool, μ.real (E z) := measureReal_iUnion_fintype_le _
    _ = _ := by simp [hmass, Fintype.card_fun, Fintype.card_fin]

/-- [There is a nonnegative constant bounding the expected squared positive
excess of the first unsatisfiable time beyond ten times the number of variables,
uniformly over all variable counts of at least three and all independent
uniform clause processes on probability spaces](goal). -/
-- @node: hittingTime_cap_error_bound
lemma hittingTime_cap_error_bound :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ n : ℕ, MainN n →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (Cseq : ℕ → Ω → ProperClause n), IsUniformClauseProcess μ Cseq →
      (∫ ω, ((hittingTime (fun j => Cseq j ω) - capL n : ℕ) : ℝ) ^ 2 ∂μ) ≤ Q := by
  let r : ℝ := 7 / 8
  have hr : 0 < r := by norm_num [r]
  have hs : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ 2 * r ^ k) := by
    have hg := summable_pow_mul_geometric_of_norm_lt_one 2
      (by norm_num [r] : ‖r‖ < 1)
    have h := ((summable_nat_add_iff 1).2 hg).mul_right r⁻¹
    apply h.congr
    intro k
    rw [pow_succ]
    field_simp
    simp [pow_succ, mul_comm]
  refine ⟨∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ 2 * r ^ k,
    tsum_nonneg (fun _ => by positivity), ?_⟩
  intro n hn Ω _ μ _ Cseq hlaw
  let H := fun ω => hittingTime (fun j => Cseq j ω)
  let R := fun ω => H ω - capL n
  have hH : Measurable H := measurable_hittingTime Cseq hlaw.1
  have hR : Measurable R := hH.sub measurable_const
  have hi : Integrable (fun ω => (R ω : ℝ) ^ 2) μ := by
    apply (hittingTime_integrable_pow hn μ Cseq hlaw 2).mono'
    · fun_prop
    · filter_upwards [] with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.sub_le (H ω) (capL n)) 2
  let S : ℕ → Set Ω := fun k => {ω | R ω = k + 1}
  have hS (k : ℕ) : MeasurableSet (S k) := hR (measurableSet_singleton (k + 1))
  have hd : Pairwise (Function.onFun Disjoint S) := by
    intro j k hjk
    apply Set.disjoint_left.mpr
    intro ω hj hk
    exact hjk (by have : j + 1 = k + 1 := hj.symm.trans hk; omega)
  have hcover : (∫ ω in ⋃ k, S k, (R ω : ℝ) ^ 2 ∂μ) =
      ∫ ω, (R ω : ℝ) ^ 2 ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro ω hω
    have hz : R ω = 0 := by
      by_contra h
      exact hω (Set.mem_iUnion.mpr ⟨R ω - 1, by
        change R ω = R ω - 1 + 1
        omega⟩)
    simp [hz]
  have hfiber (k : ℕ) : (∫ ω in S k, (R ω : ℝ) ^ 2 ∂μ) =
      μ.real (S k) * ((k + 1 : ℕ) : ℝ) ^ 2 := by
    rw [show (∫ ω in S k, (R ω : ℝ) ^ 2 ∂μ) =
        ∫ _ω in S k, ((k + 1 : ℕ) : ℝ) ^ 2 ∂μ by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (hS k)] with ω hω
      rw [show R ω = k + 1 from hω], setIntegral_const, smul_eq_mul]
  have htail (k : ℕ) : μ.real (S k) ≤ r ^ k := by
    have hsub : S k ⊆ {ω | capL n + k < H ω} := by
      intro ω hω
      change H ω - capL n = k + 1 at hω
      change capL n + k < H ω
      omega
    have h := (measureReal_mono hsub).trans
      (hittingTime_uniform_tail hn μ Cseq hlaw (capL n + k))
    have hcoef : (2 : ℝ) ^ n * r ^ capL n ≤ 1 := by
      rw [capL, pow_mul, ← mul_pow]
      exact pow_le_one₀ (by positivity) (by norm_num [r])
    calc
      _ ≤ (2 : ℝ) ^ n * r ^ (capL n + k) := h
      _ = ((2 : ℝ) ^ n * r ^ capL n) * r ^ k := by rw [pow_add]; ring
      _ ≤ 1 * r ^ k := mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = r ^ k := one_mul _
  rw [← hcover, integral_iUnion hS hd hi.integrableOn]
  apply Summable.tsum_le_tsum
    (fun k => by
      rw [hfiber]
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_right (htail k) (sq_nonneg ((k + 1 : ℕ) : ℝ)))
    (hasSum_integral_iUnion hS hd hi.integrableOn).summable
  simpa only [mul_comm] using hs

/-- If [the first real random variable is square integrable](hyp:hX) and [the
comparison variable is square integrable](hyp:hY), then [the variance of the
first is at most twice the comparison variable's variance plus twice their
expected squared difference](goal). -/
-- @node: variance_le_twice_comparison_error
lemma variance_le_twice_comparison_error
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    variance X μ ≤ 2 * variance Y μ + 2 * ∫ ω, (X ω - Y ω) ^ 2 ∂μ := by
  have hcenter : variance X μ ≤ ∫ ω, (X ω - ∫ ω, Y ω ∂μ) ^ 2 ∂μ := by
    rw [← variance_sub_const hX.aestronglyMeasurable (∫ ω, Y ω ∂μ)]
    exact variance_le_expectation_sq (hX.sub (memLp_const (∫ ω, Y ω ∂μ))).aestronglyMeasurable
  have h := integral_mono_ae (hX.sub (memLp_const (∫ ω, Y ω ∂μ))).integrable_sq
    (((hY.sub (memLp_const (∫ ω, Y ω ∂μ))).integrable_sq.const_mul 2).add
      ((hX.sub hY).integrable_sq.const_mul 2))
    (Filter.Eventually.of_forall (fun ω => by
      simp only [Pi.add_apply, Pi.sub_apply]
      have hs := sq_nonneg ((Y ω - ∫ ω, Y ω ∂μ) - (X ω - Y ω))
      nlinarith))
  simp only [Pi.add_apply] at h
  rw [integral_add ((hY.sub (memLp_const (∫ ω, Y ω ∂μ))).integrable_sq.const_mul 2)
    ((hX.sub hY).integrable_sq.const_mul 2)] at h
  simp only [integral_const_mul] at h
  rw [variance_eq_integral hY.aemeasurable]
  exact hcenter.trans h

end Papers.OaiLinearVarianceRandom
