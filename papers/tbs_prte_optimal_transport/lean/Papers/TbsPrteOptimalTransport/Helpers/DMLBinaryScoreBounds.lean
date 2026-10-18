module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLRegularScoreConvergence
/-! Uniform bounds for the complete clipped binary score. These bounds supply
the moments needed by the oracle variance law of large numbers. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- @node: fitted_full_product_abs_bound
/-- If [the fitted binary nuisances are admissible](hyp:he), [outcomes are
binary almost surely](hyp:hy), [c is positive](hyp:hc), and [every fitted
positive-level instrument probability is at least c almost everywhere](hyp:hpi),
[the absolute full-product score at any level is at most 1 + 2/c almost surely](goal). -/
lemma fitted_full_product_abs_bound (L : LevelData Z X) (e : NuisanceBin L)
    (he : BinAdmissible M L e) (hy : OutcomeBinaryAE M)
    (c : ℝ) (hc : 0 < c)
    (hpi : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (k : Fin L.K) :
    ∀ᵐ o ∂observationLaw M, |psiFullProdBin L e k o| ≤ 1 + 2 / c := by
  filter_upwards [fitted_RP_abs_bound M L e he hy c hc hpi (k+1) (by omega),
    fitted_RP_abs_bound M L e he hy c hc hpi k k.isLt.le,
    observationLaw_covariate_ae M _ (fitted_binFullJ_norm_bound M L e he k),
    observationLaw_covariate_ae M _ (he.2.2.2.2.2.2.2.2.2.1 k)] with o hp hm hj hg
  have hgb : |e.gammaFull k o.1| ≤ 1 := abs_le.mpr hg
  have hev : |indicator (o.2.1 ∈ higherPolicy L k) -
      indicator (o.2.1 ∈ higherBaseline L k)| ≤ 1 := by
    unfold indicator
    split_ifs <;> norm_num
  have hid : psiFullProdBin L e k o =
      (indicator (o.2.1 ∈ higherPolicy L k) - indicator (o.2.1 ∈ higherBaseline L k)) *
        binFullJ L e k o.1 + e.gammaFull k o.1 * RP L e (k+1) o -
          e.gammaFull k o.1 * RP L e k o := by
    simp only [psiFullProdBin, fullValue, dif_pos k.isLt]
    ring
  rw [hid]
  calc
    _ ≤ |(indicator (o.2.1 ∈ higherPolicy L k) -
          indicator (o.2.1 ∈ higherBaseline L k)) * binFullJ L e k o.1| +
        |e.gammaFull k o.1 * RP L e (k+1) o| + |e.gammaFull k o.1 * RP L e k o| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 1 * 1 + 1 * (1/c) + 1 * (1/c) := by
      simp only [abs_mul, Real.norm_eq_abs] at *
      gcongr
    _ = _ := by ring

-- @node: fitted_regular_product_abs_bound
/-- Suppose [the policy map is valid](hyp:hphi), [B is nonnegative](hyp:hB),
[the proposed policy derivative has absolute value at most B on the unit
interval](hyp:hb), [the binary nuisances are admissible](hyp:he), [outcomes are
binary almost surely](hyp:hy), [c is positive](hyp:hc), [positive-level instrument
probabilities](hyp:hpi) and [regular-cell probabilities](hyp:htau) are at least c
almost everywhere, and [the level](hyp:hk) and [regular branch](hyp:hj) are in
range; then [the absolute regular-product score is almost surely at most
1 + 4/c plus B/c times the combined cardinalities of the two adjacent instrument groups](goal). -/
lemma fitted_regular_product_abs_bound
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ z x p, p ∈ Icc (0 : ℝ) 1 → |dphi z x p| ≤ B)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e)
    (hy : OutcomeBinaryAE M) (c : ℝ) (hc : 0 < c)
    (hpi : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (htau : ∀ r : RegularIndex L, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x)
    (k j : ℕ) (hk : k < L.K) (hj : 1 ≤ j ∧ j ≤ L.l k) :
    ∀ᵐ o ∂observationLaw M, |psiProdBin phi dphi L e k j o| ≤
      1 + 4 / c + ((L.T k j).card + (L.T k (j-1)).card) * B / c := by
  filter_upwards [fitted_regular_regression_correction_abs_bound M phi L e he hy c hc hpi k j hk,
    fitted_regular_policy_correction_abs_bound M phi dphi B hB hb L e he c hc htau k j hk.le,
    observationLaw_covariate_ae M _ (fitted_regular_gamma_abs_bound M L e he k j),
    observationLaw_covariate_ae M _ (binary_auxiliary_ranges M phi L e hphi he k hk j hj.1 hj.2)]
    with o hr hp hg hh
  have hhb : |hMinus phi L e k j o.1| ≤ 1 := by
    rw [abs_of_nonneg hh.1.1]
    exact hh.1.2
  have hi : |indicator (o.2.1 ∈ policyUnion L k j)| ≤ 1 := by
    unfold indicator
    split_ifs <;> norm_num
  rw [psiProdBin_correction_split]
  calc
    _ ≤ |indicator (o.2.1 ∈ policyUnion L k j) * hMinus phi L e k j o.1| +
        |regularValue e.gamma k j o.1 * binaryRegularRegressionCorrection phi L e k j o| +
        |regularValue e.gamma k j o.1 * binaryRegularPolicyCorrection phi dphi L e k j o| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 1 * 1 + 1 * (4/c) +
        1 * (((L.T k j).card + (L.T k (j-1)).card) * B / c) := by
      simp only [abs_mul]
      gcongr
    _ = _ := by ring

-- @node: fitted_binary_tail_abs_bound
/-- If [the policy map is valid](hyp:hphi), [B is nonnegative](hyp:hB),
[the proposed policy derivative is bounded in absolute value by B on the unit
interval](hyp:hb), [the fitted binary nuisances are admissible](hyp:he),
[c is positive](hyp:hc), and [all fitted positive-level instrument probabilities
are at least c almost everywhere](hyp:hpi), [the absolute common tail score is
almost surely bounded by the absolute lower outcome endpoint times 2 + B + 1/c](goal). -/
lemma fitted_binary_tail_abs_bound
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ z x p, p ∈ Icc (0 : ℝ) 1 → |dphi z x p| ≤ B)
    (L : LevelData Z X) (e : NuisanceBin L) (he : BinAdmissible M L e)
    (c : ℝ) (hc : 0 < c)
    (hpi : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x) :
    ∀ᵐ o ∂observationLaw M,
      |commonTailScore M phi dphi L e.prop e.pLev e.piLev e.gammaTail o| ≤
        |M.yMin| * (2 + B + 1/c) := by
  filter_upwards [observationLaw_treatment_range M,
    observationLaw_covariate_ae M _ (ae_all_iff.mpr he.1),
    observationLaw_covariate_ae M _ (fitted_positive_treatment_range M L e he L.K),
    observationLaw_covariate_ae M _ he.2.2.2.2.2.2.2.2.2.2.2.1,
    fitted_Rp_abs_bound M L e he c hc hpi L.K le_rfl] with o hw hp hlev hg hr
  have hq := hphi.2 o.2.1 o.1 _ (hp o.2.1)
  have hqb : |phi o.2.1 o.1 (e.prop o.2.1 o.1)| ≤ 1 := by
    rw [abs_of_nonneg hq.1]; exact hq.2
  have hwb : |o.2.2.1 - e.prop o.2.1 o.1| ≤ 1 := abs_le.mpr
    ⟨by linarith [(hp o.2.1).2, hw.1], by linarith [(hp o.2.1).1, hw.2]⟩
  have hlb : |positiveValue e.pLev L.K o.1| ≤ 1 := by
    rw [abs_of_nonneg hlev.1]; exact hlev.2
  have hgb : |e.gammaTail o.1| ≤ 1 := by
    rw [abs_of_nonneg hg.1]; exact hg.2
  have hi : |indicator (o.2.1 ∈ policyUnion L L.K 1)| ≤ 1 := by
    unfold indicator
    split_ifs <;> norm_num
  have hdb := hb o.2.1 o.1 _ (hp o.2.1)
  rw [commonTailScore_binary_residual_split, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  calc
    _ ≤ |indicator (o.2.1 ∈ policyUnion L L.K 1)| *
        (|phi o.2.1 o.1 (e.prop o.2.1 o.1)| +
          |dphi o.2.1 o.1 (e.prop o.2.1 o.1)| * |o.2.2.1 - e.prop o.2.1 o.1|) +
        (|indicator (o.2.1 ∈ policyUnion L L.K 1)| * |positiveValue e.pLev L.K o.1| +
          |e.gammaTail o.1| * |Rp L e L.K o|) := by
      exact (abs_sub _ _).trans (add_le_add
        (by rw [abs_mul]; gcongr; exact (abs_add_le _ _).trans_eq (by rw [abs_mul]))
        (by simpa only [abs_mul] using (abs_add_le
          (indicator (o.2.1 ∈ policyUnion L L.K 1) * positiveValue e.pLev L.K o.1)
          (e.gammaTail o.1 * Rp L e L.K o))))
    _ ≤ 1 * (1 + B * 1) + (1 * 1 + 1 * (1/c)) := by gcongr
    _ = _ := by ring

-- The bound depends on the finite level structure and overlap, not on the fit.
-- @node: fitted_binary_score_abs_bound
/-- Suppose [the policy map is valid](hyp:hphi), [B is nonnegative](hyp:hB),
[the proposed policy derivative is bounded in absolute value by B on the unit
interval](hyp:hb), [there is at least one positive level](hyp:hK), [the binary
nuisances are admissible](hyp:he), [outcomes are binary almost surely](hyp:hy),
[c is positive](hyp:hc), and [positive-level instrument probabilities](hyp:hpi)
and [regular-cell probabilities](hyp:htau) are at least c almost everywhere;
then [the absolute complete binary score is almost surely bounded by the sum,
over levels, of 1 + 2/c and the regular-branch bounds 1 + 4/c plus B/c times
the adjacent instrument-group cardinalities, together with the absolute lower
outcome endpoint times 2 + B + 1/c](goal). -/
lemma fitted_binary_score_abs_bound
    (phi dphi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ z x p, p ∈ Icc (0 : ℝ) 1 → |dphi z x p| ≤ B)
    (L : LevelData Z X) (hK : LevelCountPos L.K)
    (e : NuisanceBin L) (he : BinAdmissible M L e) (hy : OutcomeBinaryAE M)
    (c : ℝ) (hc : 0 < c)
    (hpi : ∀ i : PositiveIndex L.K, ∀ᵐ x ∂xLaw M, c ≤ e.piLev i x)
    (htau : ∀ r : RegularIndex L, ∀ᵐ x ∂xLaw M, c ≤ e.tauLev r x) :
    ∀ᵐ o ∂observationLaw M, |psiBin M phi dphi L hK o e| ≤
      (∑ k ∈ Finset.range L.K, (1 + 2/c + ∑ j ∈ Finset.Icc 1 (L.l k),
        (1 + 4/c + ((L.T k j).card + (L.T k (j-1)).card) * B / c))) +
        |M.yMin| * (2 + B + 1/c) := by
  have hf : ∀ᵐ o ∂observationLaw M, ∀ k : Fin L.K,
      |psiFullProdBin L e k o| ≤ 1 + 2/c :=
    ae_all_iff.mpr (fitted_full_product_abs_bound M L e he hy c hc hpi)
  have hr : ∀ᵐ o ∂observationLaw M, ∀ k j, k < L.K →
      1 ≤ j ∧ j ≤ L.l k → |psiProdBin phi dphi L e k j o| ≤
        1 + 4/c + ((L.T k j).card + (L.T k (j-1)).card) * B / c := by
    apply ae_all_iff.mpr
    intro k
    apply ae_all_iff.mpr
    intro j
    by_cases hk : k < L.K
    · by_cases hj : 1 ≤ j ∧ j ≤ L.l k
      · exact (fitted_regular_product_abs_bound M phi dphi hphi B hB hb L e he
          hy c hc hpi htau k j hk hj).mono (fun _ hx _ _ => hx)
      · exact Eventually.of_forall (fun _ _ hj' => (hj hj').elim)
    · exact Eventually.of_forall (fun _ hk' _ => (hk hk').elim)
  filter_upwards [hf, hr, fitted_binary_tail_abs_bound M phi dphi hphi B hB hb L e he c hc hpi]
    with o hf hr ht
  unfold psiBin
  apply (abs_add_le _ _).trans
  apply add_le_add _ ht
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  apply (abs_add_le _ _).trans
  apply add_le_add (hf ⟨k, Finset.mem_range.mp hk⟩)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  exact Finset.sum_le_sum (fun j hj => hr k j (Finset.mem_range.mp hk) (Finset.mem_Icc.mp hj))

end Papers.TbsPrteOptimalTransport
