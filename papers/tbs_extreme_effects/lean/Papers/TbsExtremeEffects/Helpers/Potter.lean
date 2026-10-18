module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Topology.Order.Basic
public import Mathlib.Tactic

/-! The one-sided dyadic tail bound used for radial moment domination.
The argument needs only monotonicity and the tail-ratio limit at dilation two. -/

public section
namespace Papers.TbsExtremeEffects
open Filter
open scoped Topology

/-- If [the starting threshold is nonnegative](hyp:ht₀), [the one-step multiplier is nonnegative](hyp:hρ), [each doubling above the starting threshold obeys the one-step tail bound](hyp:hstep), and [the chosen threshold is above the starting threshold](hyp:ht), then [iterating over any number of doublings gives the corresponding power bound](goal).

@node: tail_dyadic_iterate -/
lemma tail_dyadic_iterate (F : ℝ → ℝ) {t₀ ρ : ℝ}
    (ht₀ : 0 ≤ t₀) (hρ : 0 ≤ ρ)
    (hstep : ∀ t ≥ t₀, F (2 * t) ≤ ρ * F t)
    {t : ℝ} (ht : t₀ ≤ t) (k : ℕ) :
    F ((2 : ℝ) ^ k * t) ≤ ρ ^ k * F t := by
  have htpos : 0 ≤ t := ht₀.trans ht
  induction k with
  | zero => simp
  | succ k ih =>
    have hscale : t₀ ≤ (2 : ℝ) ^ k * t := by
      have hp : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      nlinarith
    calc
      F ((2 : ℝ) ^ (k + 1) * t) = F (2 * (2 ^ k * t)) := by
        congr 1
        rw [pow_succ]
        ring
      _ ≤ ρ * F (2 ^ k * t) := hstep _ hscale
      _ ≤ ρ * (ρ ^ k * F t) := mul_le_mul_of_nonneg_left ih hρ
      _ = ρ ^ (k + 1) * F t := by rw [pow_succ]; ring

/-- If [the starting threshold is nonnegative](hyp:ht₀), [the decay exponent is positive](hyp:ha), [the tail function is nonincreasing above the start](hyp:hmono), [it is nonnegative there](hyp:hnonneg), [each doubling satisfies the stated power decay](hyp:hstep), [the threshold is above the start](hyp:ht), and [the scale factor is at least one](hyp:hx), then [the tail at the scaled threshold is bounded by the stated dyadic Potter envelope](goal).

@node: tail_dyadic_bound -/
lemma tail_dyadic_bound (F : ℝ → ℝ) {t₀ a : ℝ}
    (ht₀ : 0 ≤ t₀) (ha : 0 < a)
    (hmono : AntitoneOn F (Set.Ici t₀))
    (hnonneg : ∀ t ≥ t₀, 0 ≤ F t)
    (hstep : ∀ t ≥ t₀, F (2 * t) ≤ (2 : ℝ) ^ (-a) * F t)
    {t x : ℝ} (ht : t₀ ≤ t) (hx : 1 ≤ x) :
    F (t * x) ≤ (2 : ℝ) ^ a * x ^ (-a) * F t := by
  obtain ⟨k, hk, hk'⟩ := exists_nat_pow_near hx (show (1 : ℝ) < 2 by norm_num)
  have htpos : 0 ≤ t := ht₀.trans ht
  have hscale : t₀ ≤ (2 : ℝ) ^ k * t := by
    have hp : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    nlinarith
  have htx : t₀ ≤ t * x := by nlinarith
  have hpow : ((2 : ℝ) ^ (-a)) ^ k =
      (2 : ℝ) ^ a * ((2 : ℝ) ^ (k + 1)) ^ (-a) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    push_cast
    ring
  calc
    F (t * x) ≤ F (2 ^ k * t) :=
      hmono hscale htx (by nlinarith)
    _ ≤ ((2 : ℝ) ^ (-a)) ^ k * F t :=
      tail_dyadic_iterate F ht₀ (Real.rpow_nonneg (by norm_num) _) hstep ht k
    _ = ((2 : ℝ) ^ a * ((2 : ℝ) ^ (k + 1)) ^ (-a)) * F t := by rw [hpow]
    _ ≤ ((2 : ℝ) ^ a * x ^ (-a)) * F t := by
      apply mul_le_mul_of_nonneg_right _ (hnonneg t ht)
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) _)
      exact Real.rpow_le_rpow_of_nonpos (by positivity) hk'.le (by linarith)

/-- If [the slack exponent is positive](hyp:hε), [it is smaller than the tail exponent](hyp:hεβ), [the tail function is nonincreasing above zero](hyp:hmono), [it is eventually positive](hyp:hpos), and [its doubling ratio converges to the stated Pareto ratio](hyp:hratio), then [beyond some positive threshold every scale factor at least one obeys the stated Potter tail bound](goal).

@node: tail_potter_bound -/
lemma tail_potter_bound (F : ℝ → ℝ) {β ε : ℝ}
    (hε : 0 < ε) (hεβ : ε < β)
    (hmono : AntitoneOn F (Set.Ioi 0))
    (hpos : ∀ᶠ t in atTop, 0 < F t)
    (hratio : Tendsto (fun t => F (2 * t) / F t) atTop (𝓝 ((2 : ℝ) ^ (-β)))) :
    ∃ t₀ > 0, ∀ t ≥ t₀, ∀ x ≥ 1,
      F (t * x) ≤ (2 : ℝ) ^ (β - ε) * x ^ (-(β - ε)) * F t := by
  have hgap : (2 : ℝ) ^ (-β) < (2 : ℝ) ^ (-(β - ε)) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have hsmall : ∀ᶠ t in atTop,
      F (2 * t) / F t < (2 : ℝ) ^ (-(β - ε)) :=
    (tendsto_order.1 hratio).2 _ hgap
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hpos.and hsmall)
  refine ⟨max 1 T, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro t ht x hx
  have hbase : 0 < max (1 : ℝ) T := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  apply tail_dyadic_bound F hbase.le (by linarith) _ _ _ ht hx
  · intro u hu v hv huv
    exact hmono (hbase.trans_le hu) (hbase.trans_le hv) huv
  · intro u hu
    exact (hT u ((le_max_right _ _).trans hu)).1.le
  · intro u hu
    have hh := hT u ((le_max_right _ _).trans hu)
    exact ((div_lt_iff₀ hh.1).1 hh.2).le

/-- If [the slack exponent is positive](hyp:hε), [it is smaller than the tail exponent](hyp:hεβ), [the tail function is nonincreasing above zero](hyp:hmono), [it is eventually positive](hyp:hpos), and [its doubling ratio converges to the stated Pareto ratio](hyp:hratio), then [beyond some positive threshold its scaled-to-unscaled ratio obeys the stated Potter bound](goal).

@node: tail_potter_ratio -/
lemma tail_potter_ratio (F : ℝ → ℝ) {β ε : ℝ}
    (hε : 0 < ε) (hεβ : ε < β)
    (hmono : AntitoneOn F (Set.Ioi 0))
    (hpos : ∀ᶠ t in atTop, 0 < F t)
    (hratio : Tendsto (fun t => F (2 * t) / F t) atTop (𝓝 ((2 : ℝ) ^ (-β)))) :
    ∃ t₀ > 0, ∀ t ≥ t₀, ∀ x ≥ 1,
      F (t * x) / F t ≤ (2 : ℝ) ^ (β - ε) * x ^ (-(β - ε)) := by
  obtain ⟨T₁, hT₁, hbound⟩ := tail_potter_bound F hε hεβ hmono hpos hratio
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.1 hpos
  refine ⟨max T₁ T₂, hT₁.trans_le (le_max_left _ _), ?_⟩
  intro t ht x hx
  exact (div_le_iff₀ (hT₂ t ((le_max_right _ _).trans ht))).2
    (hbound t ((le_max_left _ _).trans ht) x hx)

/-- If [the slack exponent is positive](hyp:hε), [it is smaller than the tail exponent](hyp:hεβ), [the tail function is nonincreasing above zero](hyp:hmono), [it is nonnegative above zero](hyp:hnonneg), [it is eventually positive](hyp:hpos), and [its doubling ratio converges to the stated Pareto ratio](hyp:hratio), then [beyond some positive threshold the absolute weighted tail-ratio integrand is bounded by the displayed power envelope](goal).

@node: tail_potter_integrand_bound -/
lemma tail_potter_integrand_bound (F : ℝ → ℝ) {β ε a : ℝ}
    (hε : 0 < ε) (hεβ : ε < β)
    (hmono : AntitoneOn F (Set.Ioi 0))
    (hnonneg : ∀ t > 0, 0 ≤ F t)
    (hpos : ∀ᶠ t in atTop, 0 < F t)
    (hratio : Tendsto (fun t => F (2 * t) / F t) atTop (𝓝 ((2 : ℝ) ^ (-β)))) :
    ∃ t₀ > 0, ∀ t ≥ t₀, ∀ r ≥ 1,
      |a * r ^ (a - 1) * (F (t * r) / F t)| ≤
        (|a| * (2 : ℝ) ^ (β - ε)) * r ^ (a - β + ε - 1) := by
  obtain ⟨T₁, hT₁, hbound⟩ := tail_potter_ratio F hε hεβ hmono hpos hratio
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.1 hpos
  refine ⟨max T₁ T₂, hT₁.trans_le (le_max_left _ _), ?_⟩
  intro t ht r hr
  have htpos : 0 < t := hT₁.trans_le ((le_max_left _ _).trans ht)
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hF : 0 ≤ F (t * r) / F t :=
    div_nonneg (hnonneg _ (mul_pos htpos hrpos))
      (hT₂ t ((le_max_right _ _).trans ht)).le
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hrpos.le _), abs_of_nonneg hF]
  calc
    |a| * r ^ (a - 1) * (F (t * r) / F t) ≤
        |a| * r ^ (a - 1) * ((2 : ℝ) ^ (β - ε) * r ^ (-(β - ε))) :=
      mul_le_mul_of_nonneg_left
        (hbound t ((le_max_left _ _).trans ht) r hr)
        (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hrpos.le _))
    _ = (|a| * (2 : ℝ) ^ (β - ε)) * r ^ (a - β + ε - 1) := by
      have he : a - β + ε - 1 = (a - 1) + (-(β - ε)) := by ring
      rw [he, Real.rpow_add hrpos]
      ring

end Papers.TbsExtremeEffects
