module
public import Papers.TbsExtremeEffects.Helpers.AdaptiveTailCounts

/-! Two-sided polynomial radial tails and deterministic band endpoint rates. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory Filter
open scoped BigOperators Topology

/-- For [a finite measure](hyp:P), [a collection of component variables](hyp:W), and [a positive number of components](hyp:hm), [the probability that their sum exceeds a threshold is at most the sum of probabilities that a component exceeds its equal threshold share](goal). -/
-- @node: finite_sum_tail_union_bound
lemma finite_sum_tail_union_bound {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (W : Fin m → Ω → ℝ)
    (hm : 0 < m) (x : ℝ) :
    P.real {z | x < ∑ j, W j z} ≤ ∑ j, P.real {z | x / m < W j z} := by
  classical
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  apply (measureReal_mono (h₂ := measure_ne_top P _) ?_).trans
    (measureReal_biUnion_finset_le Finset.univ (fun j => {z | x / m < W j z}))
  intro z hz
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_univ]
  by_contra h
  have hsmall : ∀ j : Fin m, W j z ≤ x / m := by
    intro j
    exact le_of_not_gt (fun hj => h ⟨j, trivial, hj⟩)
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hsmall j)
  have hbound : (∑ j, W j z) ≤ x := by
    calc
      _ ≤ (m : ℝ) * (x / m) := by simpa using hsum
      _ = x := by field_simp
  exact (not_lt.mpr hbound) hz

/-- If [there is a positive number of components](hyp:hm), [the tail index is positive](hyp:hb), [the threshold is positive](hyp:hx), and [all component weights are positive](hyp:ha), then [the weighted nominal Pareto sum has the displayed polynomial tail upper bound](goal). -/
-- @node: hill_nominal_sum_tail_upper
lemma hill_nominal_sum_tail_upper {m : ℕ} {beta x : ℝ}
    (hm : 0 < m) (hb : 0 < beta) (hx : 0 < x)
    (a : Fin m → ℝ) (ha : ∀ i, 0 < a i) :
    (hillNominalComponentLaw beta m).real {z | x < ∑ j, a j * z j} ≤
      ((∑ j, (a j) ^ beta) * (m : ℝ) ^ beta) * x ^ (-beta) := by
  let P := hillNominalComponentLaw beta m
  let := hill_nominal_probability hb m
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  calc
    _ ≤ ∑ j, P.real {z | x / m < a j * z j} :=
      finite_sum_tail_union_bound P (fun j z => a j * z j) hm x
    _ ≤ ∑ j, (a j) ^ beta * (x / m) ^ (-beta) := by
      apply Finset.sum_le_sum
      intro j _
      exact hill_scaled_paretoII_polynomial_tail P (fun z => a j * z j) (ha j)
        (by fun_prop) (hill_nominal_weighted_coordinate_law hb a ha j)
        (x / m) (div_pos hx hmR)
    _ = _ := by
      rw [← Finset.sum_mul, Real.div_rpow hx.le hmR.le, Real.rpow_neg hmR.le,
        div_inv_eq_mul]
      ring

/-- If [there is a positive number of components](hyp:hm), [the tail index is positive](hyp:hb), [the threshold is positive](hyp:hx), [the loading matrix is nonnegative](hyp:hA), and [each of its columns has positive l1 norm](hyp:ha), then [the transformed nominal vector has the displayed polynomial tail upper bound](goal). -/
-- @node: hill_nominal_matrix_tail_upper
lemma hill_nominal_matrix_tail_upper {d m : ℕ} {beta x : ℝ}
    (hm : 0 < m) (hb : 0 < beta) (hx : 0 < x)
    (A : Matrix (Fin d) (Fin m) ℝ) (hA : ∀ r i, 0 ≤ A r i)
    (ha : ∀ i, 0 < l1Norm (fun r => A r i)) :
    ((hillNominalComponentLaw beta m).map (fun z => l1Norm (A.mulVec z))).real
      (Set.Ioi x) ≤
      ((∑ i, (l1Norm (fun r => A r i)) ^ beta) * (m : ℝ) ^ beta) * x ^ (-beta) := by
  let P := hillNominalComponentLaw beta m
  let := hill_nominal_probability hb m
  have hpos' : ∀ j : Fin m, ∀ᵐ z ∂P, 0 ≤ z j := by
    intro j
    simpa only [one_mul] using hill_scaled_paretoII_nonneg_ae P
      (fun z => (1 : ℝ) * z j) (by norm_num : (0 : ℝ) < 1) (by fun_prop)
      (by simpa only [one_mul, div_one] using hill_nominal_coordinate_law hb j)
  have hpos : ∀ᵐ z ∂P, z ∈ nonnegativeOrthant := ae_all_iff.mpr hpos'
  rw [map_measureReal_apply (by fun_prop) measurableSet_Ioi]
  have hEq : P.real {z | x < l1Norm (A.mulVec z)} =
      P.real {z | x < ∑ j, l1Norm (fun r => A r j) * z j} := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hpos] with z hz
    change (x < l1Norm (A.mulVec z)) = (x < ∑ j, l1Norm (fun r => A r j) * z j)
    rw [hill_radial_matrix_sum A hA hz]
  exact hEq.le.trans (hill_nominal_sum_tail_upper hm hb hx _ ha)

/-- For [an extreme-value model](hyp:M), [tail parameters](hyp:tp), [regularly varying noise](hyp:hRV), and [a Pareto tail representation](hyp:model), [there is a positive polynomial upper envelope for the radial tail beyond some threshold](goal). -/
-- @node: radial_polynomial_tail_upper
lemma radial_polynomial_tail_upper (M : ExtremeModel q d) (tp : TailParams)
    (hRV : NoiseRegularlyVarying M) (model : ParetoTailModel M m tp) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℝ, ∀ t ≥ T, tailProb M t ≤ C * t ^ (-M.beta) := by
  classical
  obtain ⟨k, hk, kappa, hkappa, hTransfer⟩ := hill_radial_survival_transfer M tp model
  have hm : 0 < m := by obtain ⟨hd, hdm⟩ := model.constants.1; omega
  let a := fun i => l1Norm (fun r => model.A r i)
  have ha : ∀ i, 0 < a i := fun i => model.constants.2.1.trans_le (model.matrix.2.1 i).1
  have hsum : 0 < ∑ i, (a i) ^ M.beta := by
    apply Finset.sum_pos
    · intro i _; exact Real.rpow_pos_of_pos (ha i) _
    · exact ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  let cutoff := tp.u * (tp.zeta * (k : ℝ) ^ ((1 - 2 * tp.s) / M.beta))
  refine ⟨kappa * ((∑ i, (a i) ^ M.beta) * (m : ℝ) ^ M.beta),
    mul_pos hkappa (mul_pos hsum (Real.rpow_pos_of_pos (by exact_mod_cast hm) _)),
    max (cutoff + 1) 1, ?_⟩
  intro t ht
  have hcut : cutoff < t := by linarith [le_max_left (cutoff + 1) 1]
  have htpos : 0 < t := zero_lt_one.trans_le ((le_max_right _ _).trans ht)
  rw [hTransfer t hcut]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (hill_nominal_matrix_tail_upper hm hRV.1 htpos model.A model.matrix.1 ha) hkappa.le

/-- If [the threshold multiplier is positive](hyp:hc), [the sample size is positive](hyp:hn), and [the exponents satisfy the displayed relation](hyp:hExponent), then [evaluating the polynomial tail envelope at that threshold gives the stated power of sample size](goal). -/
-- @node: polynomial_tail_at_threshold
lemma polynomial_tail_at_threshold {beta C c kappa r : ℝ}
    (hc : 0 < c) {n : ℕ} (hn : 0 < n)
    (hExponent : (1 - beta * kappa) / 2 = r) :
    C * (c * (n : ℝ) ^ kappa) ^ (-beta) =
      (C * c ^ (-beta)) * (n : ℝ) ^ (-1 + 2 * r) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [Real.mul_rpow hc.le (Real.rpow_nonneg hnR.le _), ← Real.rpow_mul hnR.le]
  have he : kappa * (-beta) = -1 + 2 * r := by linarith
  rw [he]
  ring

/-- For [an extreme-value model](hyp:M) with [tail parameters](hyp:tp), if [its noise is regularly varying](hyp:hRV), [it admits a Pareto tail representation](hyp:hTail), [both endpoint multipliers are positive](hyp:hcm,hcp), [the threshold exponent is positive](hyp:hk), and [the count exponent identity holds](hyp:hExponent), then [positive lower and upper endpoint tail envelopes hold eventually](goal). -/
-- @node: adaptive_band_tail_envelopes
lemma adaptive_band_tail_envelopes (M : ExtremeModel q d) (tp : TailParams)
    (hRV : NoiseRegularlyVarying M) (hTail : Nonempty (ParetoTailModel M m tp))
    {cminus cplus kappa r : ℝ} (hcm : 0 < cminus) (hcp : 0 < cplus)
    (hk : 0 < kappa) (hExponent : (1 - M.beta * kappa) / 2 = r) :
    ∃ L U : ℝ, 0 < L ∧ 0 < U ∧ ∀ᶠ n : ℕ in atTop,
      L * (n : ℝ) ^ (-1 + 2 * r) ≤
        tailProb M (2 * cplus * (n : ℝ) ^ kappa) ∧
      tailProb M ((cminus / 2) * (n : ℝ) ^ kappa) ≤
        U * (n : ℝ) ^ (-1 + 2 * r) := by
  obtain ⟨model⟩ := hTail
  obtain ⟨Cl, hCl, Tl, hl⟩ := radial_polynomial_tail_lower M tp hRV model
  obtain ⟨Cu, hCu, Tu, hu⟩ := radial_polynomial_tail_upper M tp hRV model
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hUpper : Tendsto (fun n : ℕ => 2 * cplus * (n : ℝ) ^ kappa) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by positivity)).mpr ((tendsto_rpow_atTop hk).comp hn)
  have hLower : Tendsto (fun n : ℕ => (cminus / 2) * (n : ℝ) ^ kappa) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by positivity)).mpr ((tendsto_rpow_atTop hk).comp hn)
  refine ⟨Cl * (2 * cplus) ^ (-M.beta), Cu * (cminus / 2) ^ (-M.beta),
    by positivity, by positivity, ?_⟩
  filter_upwards [hUpper.eventually (eventually_ge_atTop Tl),
    hLower.eventually (eventually_ge_atTop Tu), eventually_ge_atTop (1 : ℕ)] with n hU hL hn1
  have hnpos : 0 < n := by omega
  constructor
  · rw [← polynomial_tail_at_threshold (by positivity : 0 < 2 * cplus) hnpos hExponent]
    exact hl _ hU
  · rw [← polynomial_tail_at_threshold (by positivity : 0 < cminus / 2) hnpos hExponent]
    exact hu _ hL

/-- If [the threshold is positive](hyp:hx), [the lower envelope constant is positive](hyp:hL), [the upper envelope constant is positive](hyp:hU), [the variance proxy is nonnegative](hyp:hV), [the confidence tolerance is positive](hyp:hd), [the lower endpoint tail is bounded above as stated](hyp:hell), and [the upper endpoint tail is bounded below as stated](hyp:hu), then [the sampling-radius term is bounded by the displayed rate](goal). -/
-- @node: polynomial_band_sampling_radius_bound
lemma polynomial_band_sampling_radius_bound {x ell u L U V delta r : ℝ}
    (hx : 0 < x) (hL : 0 < L) (hU : 0 < U) (hV : 0 ≤ V) (hd : 0 < delta)
    (hell : ell ≤ U * x ^ (-1 + 2 * r))
    (hu : L * x ^ (-1 + 2 * r) ≤ u) :
    4 * Real.sqrt (192 * V * ell / (delta * x * u ^ 2)) ≤
      (4 * Real.sqrt (192 * U / L ^ 2)) * Real.sqrt (V / delta) * x ^ (-r) := by
  have hz : 0 < x ^ (-1 + 2 * r) := Real.rpow_pos_of_pos hx _
  have hu0 : 0 < u := (mul_pos hL hz).trans_le hu
  have hsq : (L * x ^ (-1 + 2 * r)) ^ 2 ≤ u ^ 2 :=
    pow_le_pow_left₀ (by positivity) hu 2
  have hNumerator : 192 * V * ell ≤ 192 * V * (U * x ^ (-1 + 2 * r)) :=
    mul_le_mul_of_nonneg_left hell (by positivity)
  have hInside : 192 * V * ell / (delta * x * u ^ 2) ≤
      (192 * U / L ^ 2) * (V / delta) * x ^ (-2 * r) := by
    calc
      _ ≤ 192 * V * (U * x ^ (-1 + 2 * r)) / (delta * x * u ^ 2) :=
        div_le_div_of_nonneg_right hNumerator (by positivity)
      _ ≤ 192 * V * (U * x ^ (-1 + 2 * r)) /
          (delta * x * (L * x ^ (-1 + 2 * r)) ^ 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_left hsq (by positivity))
      _ = _ := by
        have hden : x * (x ^ (-1 + 2 * r)) ^ 2 = x ^ (-1 + 4 * r) := by
          rw [← Real.rpow_natCast (x ^ (-1 + 2 * r)) 2,
            ← Real.rpow_mul hx.le]
          nth_rw 1 [← Real.rpow_one x]
          rw [← Real.rpow_add hx]
          congr 1
          norm_num
          ring
        rw [mul_pow]
        have hfactor : delta * x * (L ^ 2 * (x ^ (-1 + 2 * r)) ^ 2) =
            (delta * L ^ 2) * (x * (x ^ (-1 + 2 * r)) ^ 2) := by ring
        rw [hfactor, hden, div_eq_mul_inv, mul_inv_rev, mul_inv_rev,
          ← Real.rpow_neg hx.le]
        rw [show -(-1 + 4 * r) = 1 - 4 * r by ring]
        have hp : x ^ (-1 + 2 * r) * x ^ (1 - 4 * r) = x ^ (-2 * r) := by
          rw [← Real.rpow_add hx]; congr 1; ring
        calc
          _ = (192 * U / L ^ 2) * (V / delta) *
              (x ^ (-1 + 2 * r) * x ^ (1 - 4 * r)) := by ring
          _ = _ := by rw [hp]
  have hRoot : Real.sqrt (x ^ (-2 * r)) = x ^ (-r) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]
    congr 1
    ring
  calc
    _ ≤ 4 * Real.sqrt ((192 * U / L ^ 2) * (V / delta) * x ^ (-2 * r)) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hInside) (by norm_num)
    _ = _ := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ (192 * U / L ^ 2) * (V / delta)),
        Real.sqrt_mul (by positivity : 0 ≤ 192 * U / L ^ 2), hRoot]
      ring

/-- If [the threshold is positive](hyp:hx), [the lower tail probability is nonnegative](hyp:hell), [the upper tail probability is positive](hyp:hu), [the variance proxy is nonnegative](hyp:hV), and [the confidence tolerance is positive](hyp:hd), then [the two maximal-process radius terms equal the stated single radius](goal). -/
-- @node: threshold_process_radius_identity
lemma threshold_process_radius_identity {x ell u V delta : ℝ}
    (hx : 0 < x) (hell : 0 ≤ ell) (hu : 0 < u) (hV : 0 ≤ V) (hd : 0 < delta) :
    (Real.sqrt (48 * x * V * ell / delta) +
      Real.sqrt V * Real.sqrt (48 * x * ell / delta)) / (x * u / 4) =
      4 * Real.sqrt (192 * V * ell / (delta * x * u ^ 2)) := by
  have hRewrite : 48 * x * V * ell / delta = V * (48 * x * ell / delta) := by ring
  rw [hRewrite, Real.sqrt_mul hV]
  have hRootSq := Real.sq_sqrt (show 0 ≤ 48 * x * ell / delta by positivity)
  have hVSq := Real.sq_sqrt hV
  have hRightSq := Real.sq_sqrt (show 0 ≤ 192 * V * ell / (delta * x * u ^ 2) by positivity)
  have hSquare : ((Real.sqrt V * Real.sqrt (48 * x * ell / delta) +
        Real.sqrt V * Real.sqrt (48 * x * ell / delta)) / (x * u / 4)) ^ 2 =
      (4 * Real.sqrt (192 * V * ell / (delta * x * u ^ 2))) ^ 2 := by
    rw [div_pow]
    have hnum : (Real.sqrt V * Real.sqrt (48 * x * ell / delta) +
        Real.sqrt V * Real.sqrt (48 * x * ell / delta)) ^ 2 =
        4 * V * (48 * x * ell / delta) := by
      nlinarith only [hRootSq, hVSq,
        Real.mul_self_sqrt hV, Real.mul_self_sqrt (show 0 ≤ 48 * x * ell / delta by positivity)]
    rw [hnum, mul_pow, hRightSq]
    field_simp
    <;> ring
  nlinarith [Real.sqrt_nonneg V, Real.sqrt_nonneg (48 * x * ell / delta),
    Real.sqrt_nonneg (192 * V * ell / (delta * x * u ^ 2)),
    show 0 ≤ (Real.sqrt V * Real.sqrt (48 * x * ell / delta) +
      Real.sqrt V * Real.sqrt (48 * x * ell / delta)) / (x * u / 4) by positivity]

/-- If [the threshold is positive](hyp:hx), [the lower envelope constant is positive](hyp:hL), [the upper envelope constant is positive](hyp:hU), [the lower tail probability is nonnegative](hyp:hell0), [the variance proxy is nonnegative](hyp:hV), [the confidence tolerance is positive](hyp:hd), [the lower endpoint tail has its stated upper envelope](hyp:hell), and [the upper endpoint tail has its stated lower envelope](hyp:hu), then [the maximal-process radius is bounded by the displayed sampling rate](goal). -/
-- @node: threshold_process_radius_rate_bound
lemma threshold_process_radius_rate_bound {x ell u L U V delta r : ℝ}
    (hx : 0 < x) (hL : 0 < L) (hU : 0 < U) (hell0 : 0 ≤ ell)
    (hV : 0 ≤ V) (hd : 0 < delta)
    (hell : ell ≤ U * x ^ (-1 + 2 * r))
    (hu : L * x ^ (-1 + 2 * r) ≤ u) :
    (Real.sqrt (48 * x * V * ell / delta) +
      Real.sqrt V * Real.sqrt (48 * x * ell / delta)) / (x * u / 4) ≤
      (4 * Real.sqrt (192 * U / L ^ 2)) * Real.sqrt (V / delta) * x ^ (-r) := by
  have hu0 : 0 < u := (mul_pos hL (Real.rpow_pos_of_pos hx _)).trans_le hu
  rw [threshold_process_radius_identity hx hell0 hu0 hV hd]
  exact polynomial_band_sampling_radius_bound hx hL hU hV hd hell hu

end Papers.TbsExtremeEffects
