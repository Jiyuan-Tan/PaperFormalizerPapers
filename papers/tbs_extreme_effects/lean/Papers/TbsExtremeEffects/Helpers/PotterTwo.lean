module
public import Papers.TbsExtremeEffects.Helpers.Potter

/-! A finer geometric grid makes the Potter prefactor two, for the explicit
radial-moment coefficient in the NETE rate. -/

public section
namespace Papers.TbsExtremeEffects
open Filter
open scoped Topology

/-- If [the geometric base exceeds one](hyp:hb), [the starting threshold is nonnegative](hyp:ht₀), [the one-step multiplier is nonnegative](hyp:hρ), [each multiplication by the base above the start obeys the one-step tail bound](hyp:hstep), and [the chosen threshold is above the start](hyp:ht), then [iteration gives the corresponding geometric power bound](goal).

@node: tail_geometric_iterate -/
lemma tail_geometric_iterate (F : ℝ → ℝ) {t₀ ρ b : ℝ}
    (hb : 1 < b) (ht₀ : 0 ≤ t₀) (hρ : 0 ≤ ρ)
    (hstep : ∀ t ≥ t₀, F (b * t) ≤ ρ * F t)
    {t : ℝ} (ht : t₀ ≤ t) (k : ℕ) :
    F (b ^ k * t) ≤ ρ ^ k * F t := by
  have htpos : 0 ≤ t := ht₀.trans ht
  induction k with
  | zero => simp
  | succ k ih =>
    have hscale : t₀ ≤ b ^ k * t := by
      have hp : (1 : ℝ) ≤ b ^ k := one_le_pow₀ (by linarith [hb])
      nlinarith
    calc
      F (b ^ (k + 1) * t) = F (b * (b ^ k * t)) := by
        congr 1
        rw [pow_succ]
        ring
      _ ≤ ρ * F (b ^ k * t) := hstep _ hscale
      _ ≤ ρ * (ρ ^ k * F t) := mul_le_mul_of_nonneg_left ih hρ
      _ = ρ ^ (k + 1) * F t := by rw [pow_succ]; ring

/-- If [the geometric base exceeds one](hyp:hb), [the starting threshold is nonnegative](hyp:ht₀), [the decay exponent is positive](hyp:ha), [the tail function is nonincreasing above the start](hyp:hmono), [it is nonnegative there](hyp:hnonneg), [each multiplication by the base satisfies the stated power decay](hyp:hstep), [the threshold is above the start](hyp:ht), and [the scale factor is at least one](hyp:hx), then [the tail at the scaled threshold is bounded by the stated geometric Potter envelope](goal).

@node: tail_geometric_bound -/
lemma tail_geometric_bound (F : ℝ → ℝ) {t₀ a b : ℝ}
    (hb : 1 < b) (ht₀ : 0 ≤ t₀) (ha : 0 < a)
    (hmono : AntitoneOn F (Set.Ici t₀))
    (hnonneg : ∀ t ≥ t₀, 0 ≤ F t)
    (hstep : ∀ t ≥ t₀, F (b * t) ≤ b ^ (-a) * F t)
    {t x : ℝ} (ht : t₀ ≤ t) (hx : 1 ≤ x) :
    F (t * x) ≤ b ^ a * x ^ (-a) * F t := by
  obtain ⟨k, hk, hk'⟩ := exists_nat_pow_near hx hb
  have htpos : 0 ≤ t := ht₀.trans ht
  have hscale : t₀ ≤ b ^ k * t := by
    have hp : (1 : ℝ) ≤ b ^ k := one_le_pow₀ (by linarith [hb])
    nlinarith
  have htx : t₀ ≤ t * x := by nlinarith
  have hpow : (b ^ (-a)) ^ k =
      b ^ a * (b ^ (k + 1)) ^ (-a) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : (0 : ℝ) ≤ b),
      ← Real.rpow_natCast, ← Real.rpow_mul (by linarith : (0 : ℝ) ≤ b),
      ← Real.rpow_add (by linarith : (0 : ℝ) < b)]
    congr 1
    push_cast
    ring
  calc
    F (t * x) ≤ F (b ^ k * t) :=
      hmono hscale htx (by nlinarith)
    _ ≤ (b ^ (-a)) ^ k * F t :=
      tail_geometric_iterate F hb ht₀ (Real.rpow_nonneg (by linarith [hb]) _) hstep ht k
    _ = (b ^ a * (b ^ (k + 1)) ^ (-a)) * F t := by rw [hpow]
    _ ≤ (b ^ a * x ^ (-a)) * F t := by
      apply mul_le_mul_of_nonneg_right _ (hnonneg t ht)
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith [hb]) _)
      exact Real.rpow_le_rpow_of_nonpos (by positivity) hk'.le (by linarith)

/-- If [the slack exponent is positive](hyp:hε), [it is smaller than the tail exponent](hyp:hεβ), [the tail function is nonincreasing above zero](hyp:hmono), [it is eventually positive](hyp:hpos), and [its ratio at every dilation factor greater than one converges to the Pareto ratio](hyp:hratio), then [beyond some positive threshold its scaled-to-unscaled ratio is bounded by twice the stated power envelope](goal).

@node: tail_potter_ratio_two -/
lemma tail_potter_ratio_two (F : ℝ → ℝ) {β ε : ℝ}
    (hε : 0 < ε) (hεβ : ε < β)
    (hmono : AntitoneOn F (Set.Ioi 0))
    (hpos : ∀ᶠ t in atTop, 0 < F t)
    (hratio : ∀ b > 1,
      Tendsto (fun t => F (b * t) / F t) atTop (𝓝 (b ^ (-β)))) :
    ∃ t₀ > 0, ∀ t ≥ t₀, ∀ x ≥ 1,
      F (t * x) / F t ≤ 2 * x ^ (-(β - ε)) := by
  let a := β - ε
  have ha : 0 < a := sub_pos.mpr hεβ
  let b := (2 : ℝ) ^ (1 / a)
  have hb : 1 < b := Real.one_lt_rpow (by norm_num) (by positivity)
  have hba : b ^ a = 2 := by
    dsimp [b]
    rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel ha.ne', Real.rpow_one]
  have hgap : b ^ (-β) < b ^ (-a) :=
    Real.rpow_lt_rpow_of_exponent_lt hb (by dsimp [a]; linarith)
  have hsmall : ∀ᶠ t in atTop, F (b * t) / F t < b ^ (-a) :=
    (tendsto_order.1 (hratio b hb)).2 _ hgap
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hpos.and hsmall)
  have hbase : 0 < max (1 : ℝ) T := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨max 1 T, hbase, ?_⟩
  intro t ht x hx
  have hbound := tail_geometric_bound F hb hbase.le ha
    (fun u hu v hv huv => hmono (hbase.trans_le hu) (hbase.trans_le hv) huv)
    (fun u hu => (hT u ((le_max_right _ _).trans hu)).1.le)
    (fun u hu => ((div_lt_iff₀ (hT u ((le_max_right _ _).trans hu)).1).1
      (hT u ((le_max_right _ _).trans hu)).2).le) ht hx
  rw [hba] at hbound
  exact (div_le_iff₀ (hT t ((le_max_right _ _).trans ht)).1).2 hbound

end Papers.TbsExtremeEffects
