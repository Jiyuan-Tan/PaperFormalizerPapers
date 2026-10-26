module
public import Papers.OaiMetricMarkovCotype.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Logic.Equiv.Fin.Basic

/-! # Geometric moment and remainder estimates for the endpoint comparison -/

public section

noncomputable section
open scoped BigOperators
namespace Papers.OaiMetricMarkovCotype

-- @node: geomSurvProb_pos_lt_one
/-- For [a positive integer time parameter](hyp:ht), [the one-step geometric
survival probability is strictly between zero and one](goal). -/
lemma geomSurvProb_pos_lt_one (t : ℕ) (ht : GeometricParameterDomain t) :
    0 < geomSurvProb t ht ∧ geomSurvProb t ht < 1 := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  unfold geomSurvProb geomKillProb
  constructor <;> have := one_div_pos.mpr (by linarith : (0 : ℝ) < t + 1)
  · have := (div_lt_one (by linarith : (0 : ℝ) < t + 1)).mpr
      (by linarith : (1 : ℝ) < t + 1)
    linarith
  · linarith

/-- For [a positive integer time parameter t](hyp:ht), [the probability of
surviving t steps is at most one half](goal). -/
-- @node: geomSurvProb_pow_time_le_half
lemma geomSurvProb_pow_time_le_half (t : ℕ) (ht : GeometricParameterDomain t) :
    geomSurvProb t ht ^ t ≤ 1 / 2 := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hber := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 / t by linarith [one_div_pos.mpr htR]) t
  have htwo : (2 : ℝ) ≤ (1 + 1 / (t : ℝ)) ^ t := by
    have hcancel : (t : ℝ) * (1 / (t : ℝ)) = 1 := by field_simp
    rw [hcancel] at hber
    norm_num at hber ⊢
    exact hber
  have hprod : geomSurvProb t ht * (1 + 1 / (t : ℝ)) = 1 := by
    unfold geomSurvProb geomKillProb
    field_simp
    ring
  have hp := congrArg (fun a : ℝ => a ^ t) hprod
  rw [mul_pow, one_pow] at hp
  have hq := (geomSurvProb_pos_lt_one t ht).1.le
  nlinarith [pow_nonneg hq t]

/-- If [q is nonnegative](hyp:hq) and [q is less than one](hyp:hq1), then [the
sum over nonnegative integers s of s squared times q to the power s equals
q times one plus q divided by the cube of one minus q](goal). -/
-- @node: tsum_sq_mul_geometric
lemma tsum_sq_mul_geometric {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    (∑' s : ℕ, (s : ℝ) ^ 2 * q ^ s) = q * (1 + q) / (1 - q) ^ 3 := by
  have hn : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hq] using hq1
  have ha := summable_pow_mul_geometric_of_norm_lt_one 2 hn
  have hb := hasSum_coe_mul_geometric_of_norm_lt_one hn
  have hc := hasSum_geometric_of_lt_one hq hq1
  have hshift : (∑' s : ℕ, (s : ℝ) ^ 2 * q ^ s) =
      ∑' s : ℕ, ((s : ℝ) + 1) ^ 2 * q ^ (s + 1) := by
    simpa using ha.tsum_eq_zero_add
  have hexpand : (∑' s : ℕ, ((s : ℝ) + 1) ^ 2 * q ^ (s + 1)) =
      q * ((∑' s : ℕ, (s : ℝ) ^ 2 * q ^ s) +
        2 * (q / (1 - q) ^ 2) + (1 - q)⁻¹) := by
    calc
      _ = ∑' s : ℕ, q * ((s : ℝ) ^ 2 * q ^ s + 2 * ((s : ℝ) * q ^ s) + q ^ s) := by
        apply tsum_congr
        intro s
        rw [pow_succ]
        ring
      _ = _ := by
        rw [tsum_mul_left, (ha.add (hb.summable.mul_left 2)).tsum_add hc.summable,
          ha.tsum_add (hb.summable.mul_left 2), tsum_mul_left, hb.tsum_eq, hc.tsum_eq]
  have hne : 1 - q ≠ 0 := by linarith
  rw [hexpand] at hshift
  apply (eq_div_iff (pow_ne_zero 3 hne)).mpr
  field_simp at hshift
  nlinarith [hshift]

-- @node: geometric_secondMoment_sum
/-- For [a positive integer time parameter t](hyp:ht), [the second raw moment
of the number of live steps before geometric killing is twice t squared plus
t](goal). -/
lemma geometric_secondMoment_sum (t : ℕ) (ht : GeometricParameterDomain t) :
    (∑' s : ℕ, geomKillProb t ht * geomSurvProb t ht ^ s * (s : ℝ) ^ 2) =
      2 * (t : ℝ) ^ 2 + t := by
  have hq := geomSurvProb_pos_lt_one t ht
  calc
    _ = geomKillProb t ht * ∑' s : ℕ, (s : ℝ) ^ 2 * geomSurvProb t ht ^ s := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro s
      ring
    _ = _ := by
      rw [tsum_sq_mul_geometric hq.1.le hq.2]
      simp only [geomSurvProb, geomKillProb]
      have htR : (0 : ℝ) < t := by exact_mod_cast ht
      field_simp
      ring

/-- For [a positive integer time parameter t](hyp:ht), [the second raw moment
of the integer quotient of the number of live steps before geometric killing
by t is at most three](goal). -/
-- @node: geometric_block_secondMoment_bound
lemma geometric_block_secondMoment_bound (t : ℕ) (ht : GeometricParameterDomain t) :
    (∑' s : ℕ, geomKillProb t ht * geomSurvProb t ht ^ s * ((s / t : ℕ) : ℝ) ^ 2) ≤ 3 := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hq := geomSurvProb_pos_lt_one t ht
  have hn : ‖geomSurvProb t ht‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_pos hq.1] using hq.2
  have hmajor := (summable_pow_mul_geometric_of_norm_lt_one 2 hn).mul_left
    (geomKillProb t ht / (t : ℝ) ^ 2)
  have hp : 0 ≤ geomKillProb t ht := by unfold geomKillProb; positivity
  have hpoint (s : ℕ) :
      geomKillProb t ht * geomSurvProb t ht ^ s * ((s / t : ℕ) : ℝ) ^ 2 ≤
        (geomKillProb t ht / (t : ℝ) ^ 2) * ((s : ℝ) ^ 2 * geomSurvProb t ht ^ s) := by
    have hdiv : ((s / t : ℕ) : ℝ) * t ≤ s := by
      exact_mod_cast Nat.div_mul_le_self s t
    have hsq : ((s / t : ℕ) : ℝ) ^ 2 ≤ (s : ℝ) ^ 2 / (t : ℝ) ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos htR)).mpr
      have hs := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (s / t : ℕ) * t) hdiv 2
      simpa [mul_pow] using hs
    calc
      _ ≤ geomKillProb t ht * geomSurvProb t ht ^ s *
          ((s : ℝ) ^ 2 / (t : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (mul_nonneg hp (pow_nonneg hq.1.le _))
      _ = _ := by ring
  have hminor := hmajor.of_nonneg_of_le
    (fun s => mul_nonneg (mul_nonneg hp (pow_nonneg hq.1.le _)) (sq_nonneg _)) hpoint
  calc
    _ ≤ ∑' s : ℕ, (geomKillProb t ht / (t : ℝ) ^ 2) *
        ((s : ℝ) ^ 2 * geomSurvProb t ht ^ s) := hminor.tsum_le_tsum hpoint hmajor
    _ = (2 * (t : ℝ) ^ 2 + t) / (t : ℝ) ^ 2 := by
      rw [tsum_mul_left]
      have hm := geometric_secondMoment_sum t ht
      rw [show (∑' s : ℕ, geomKillProb t ht * geomSurvProb t ht ^ s * (s : ℝ) ^ 2) =
        geomKillProb t ht * ∑' s : ℕ, (s : ℝ) ^ 2 * geomSurvProb t ht ^ s by
          rw [← tsum_mul_left]; apply tsum_congr; intro s; ring] at hm
      rw [div_mul_eq_mul_div, hm]
    _ ≤ 3 := by
      apply (div_le_iff₀ (sq_pos_of_pos htR)).mpr
      have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
      nlinarith

/-- If [q is nonnegative](hyp:hq), [q is less than one](hyp:hq1), [the multiplier
p is nonnegative](hyp:hp), and [the absolute values of a real sequence D are
uniformly bounded by C](hyp:hC), then [the series with terms p times q to the
power s times D at s is summable](goal). -/
-- @node: summable_geometric_weighted_bounded
lemma summable_geometric_weighted_bounded {q p : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (hp : 0 ≤ p) (D : ℕ → ℝ) (C : ℝ) (hC : ∀ s, ‖D s‖ ≤ C) :
    Summable (fun s : ℕ => p * q ^ s * D s) := by
  apply ((hasSum_geometric_of_lt_one hq hq1).summable.mul_left (p * C)).of_norm_bounded
  intro s
  rw [norm_mul, norm_mul, Real.norm_of_nonneg hp,
    Real.norm_of_nonneg (pow_nonneg hq s)]
  nlinarith [mul_le_mul_of_nonneg_left (hC s) (mul_nonneg hp (pow_nonneg hq s))]

/-- For [a positive integer time parameter t](hyp:ht), [the geometric-weighted
sum of D evaluated at the remainder of the live time modulo t equals the sum
over remainders r from zero through t minus one of D at r times the killing
probability times the r-step survival probability, divided by one minus the
t-step survival probability](goal). -/
-- @node: geometric_remainder_sum
lemma geometric_remainder_sum (t : ℕ) (ht : GeometricParameterDomain t) (D : ℕ → ℝ) :
    (∑' s : ℕ, geomKillProb t ht * geomSurvProb t ht ^ s * D (s % t)) =
      ∑ r : Fin t, (geomKillProb t ht * geomSurvProb t ht ^ (r : ℕ) /
        (1 - geomSurvProb t ht ^ t)) * D r := by
  classical
  let : NeZero t := ⟨Nat.ne_of_gt ht⟩
  let p := geomKillProb t ht
  let q := geomSurvProb t ht
  have hq := geomSurvProb_pos_lt_one t ht
  have hp : 0 ≤ p := by dsimp [p, geomKillProb]; positivity
  have hbound (s : ℕ) : ‖D (s % t)‖ ≤ ∑ r : Fin t, ‖D r‖ :=
    Finset.single_le_sum (fun (r : Fin t) _ => norm_nonneg (D r))
      (Finset.mem_univ (⟨s % t, Nat.mod_lt s ht⟩ : Fin t))
  have hs := summable_geometric_weighted_bounded hq.1.le hq.2 hp
    (fun s => D (s % t)) _ hbound
  let e := (Nat.divModEquiv t).symm
  have he (a : ℕ × Fin t) : e a % t = a.2 := by
    simp [e, Nat.add_mod, Nat.mod_eq_of_lt a.2.is_lt]
  have hsp := hs.comp_injective e.injective
  calc
    _ = ∑' a : ℕ × Fin t, p * q ^ (a.1 * t + a.2) * D a.2 := by
      rw [← e.tsum_eq (fun s => p * q ^ s * D (s % t))]
      apply tsum_congr
      intro a
      rw [he]
      rfl
    _ = ∑ r : Fin t, ∑' j : ℕ, p * q ^ (j * t + r) * D r := by
      have hsp' : Summable (fun a : ℕ × Fin t => p * q ^ (a.1 * t + a.2) * D a.2) := by
        have hf : (fun a : ℕ × Fin t => p * q ^ (a.1 * t + a.2) * D a.2) =
            ((fun s => p * q ^ s * D (s % t)) ∘ e) := by
          funext a
          dsimp only [Function.comp_apply]
          rw [he]
          rfl
        rw [hf]
        exact hsp
      calc
        _ = ∑' a : Fin t × ℕ, p * q ^ (a.2 * t + a.1) * D a.1 :=
          ((Equiv.prodComm (Fin t) ℕ).tsum_eq _).symm
        _ = ∑' r : Fin t, ∑' j : ℕ, p * q ^ (j * t + r) * D r :=
          hsp'.prod_symm.tsum_prod
        _ = _ := tsum_fintype _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      have hqt : q ^ t < 1 := (geomSurvProb_pow_time_le_half t ht).trans_lt (by norm_num)
      calc
        _ = (p * q ^ (r : ℕ) * D r) * ∑' j : ℕ, (q ^ t) ^ j := by
          rw [← tsum_mul_left]
          apply tsum_congr
          intro j
          rw [pow_add, Nat.mul_comm j t, pow_mul]
          ring
        _ = _ := by
          rw [(hasSum_geometric_of_lt_one (pow_nonneg hq.1.le t) hqt).tsum_eq]
          dsimp [p, q]
          ring

/-- For [a positive integer time parameter t](hyp:ht), if [D is nonnegative at
every nonnegative integer](hyp:hD) and [D is zero at zero](hyp:hzero), then [the
geometric-weighted sum of D evaluated at the live time modulo t is at most
twice the average of D over the integers from one through t](goal). -/
-- @node: geometric_remainder_sum_bound
lemma geometric_remainder_sum_bound (t : ℕ) (ht : GeometricParameterDomain t)
    (D : ℕ → ℝ) (hD : ∀ s, 0 ≤ D s) (hzero : D 0 = 0) :
    (∑' s : ℕ, geomKillProb t ht * geomSurvProb t ht ^ s * D (s % t)) ≤
      (2 / (t : ℝ)) * ∑ s ∈ Finset.Icc 1 t, D s := by
  have hq := geomSurvProb_pos_lt_one t ht
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hden : (1 / 2 : ℝ) ≤ 1 - geomSurvProb t ht ^ t := by
    linarith [geomSurvProb_pow_time_le_half t ht]
  have hp : 0 ≤ geomKillProb t ht := by unfold geomKillProb; positivity
  have hw (r : Fin t) :
      geomKillProb t ht * geomSurvProb t ht ^ (r : ℕ) /
        (1 - geomSurvProb t ht ^ t) ≤ 2 / (t : ℝ) := by
    have hpow : geomSurvProb t ht ^ (r : ℕ) ≤ 1 := pow_le_one₀ hq.1.le hq.2.le
    have hple : geomKillProb t ht ≤ 1 / (t : ℝ) := by
      unfold geomKillProb
      exact one_div_le_one_div_of_le htR (by linarith)
    apply (div_le_iff₀ (by linarith : 0 < 1 - geomSurvProb t ht ^ t)).mpr
    have hm := mul_le_mul_of_nonneg_left hden (by positivity : (0 : ℝ) ≤ 2 / t)
    have hc : (2 / (t : ℝ)) * (1 / 2) = 1 / t := by ring
    rw [hc] at hm
    nlinarith [mul_le_mul_of_nonneg_left hpow hp]
  have hrange : (∑ r : Fin t, D r) ≤ ∑ s ∈ Finset.Icc 1 t, D s := by
    rw [Fin.sum_univ_eq_sum_range]
    have hz : (∑ s ∈ Finset.range (t + 1), D s) = ∑ s ∈ Finset.Icc 1 t, D s := by
      rw [Finset.sum_range_eq_add_Ico D (Nat.succ_pos t), hzero, zero_add]
      congr 1
    rw [← hz, Finset.sum_range_succ]
    exact le_add_of_nonneg_right (hD t)
  calc
    _ = _ := geometric_remainder_sum t ht D
    _ ≤ ∑ r : Fin t, (2 / (t : ℝ)) * D r :=
      Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_right (hw r) (hD r)
    _ = (2 / (t : ℝ)) * ∑ r : Fin t, D r := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hrange (by positivity)

end Papers.OaiMetricMarkovCotype
