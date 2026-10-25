module
public import Papers.TsAdaptiveEstimationInference.Helpers.DoublyRobust
/-! Squared score differences for independent doubly robust evaluation. -/
public section

namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory

variable {𝒲 𝒳 𝒵 : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] (V : IVWorld 𝒲 𝒳 𝒵)
variable (hTarget : Continuous V.targetFunctional)

/-- [The population mean of the squared difference between the chosen primal
function versions equals their squared Hilbert-space distance](goal). -/
-- @node: dr_primal_difference_energy
lemma dr_primal_difference_energy (h h' : V.Hbar.toSubmodule) :
    (∫ w, (primalVersion V h (V.xOf w) - primalVersion V h' (V.xOf w)) ^ 2
      ∂V.law) = ‖h - h'‖ ^ 2 := by
  have he : (fun w => primalVersion V h (V.xOf w) - primalVersion V h' (V.xOf w))
      =ᵐ[V.law] (fun w => ((h - h' : V.Hbar.toSubmodule) : Lp ℝ 2 V.law) w) := by
    exact ((V.primal_coherent h).sub (V.primal_coherent h')).trans (Lp.coeFn_sub _ _).symm
  calc
    _ = ∫ w, (((h - h' : V.Hbar.toSubmodule) : Lp ℝ 2 V.law) w) ^ 2 ∂V.law := by
      apply integral_congr_ae
      filter_upwards [he] with w hw
      exact congrArg (fun x : ℝ => x ^ 2) hw
    _ = _ := by
      simpa only [L2.inner_def, RCLike.inner_apply, conj_trivial, ← pow_two,
        Submodule.norm_coe] using
        (real_inner_self_eq_norm_sq ((h - h' : V.Hbar.toSubmodule) : Lp ℝ 2 V.law))

include hTarget in
/-- [The population mean of the squared difference between the chosen dual
function versions equals their squared Hilbert-space distance](goal). -/
-- @node: dr_dual_difference_energy
lemma dr_dual_difference_energy (q q' : V.Qbar.toSubmodule) :
    (∫ w, (dualVersion V q (V.zOf w) - dualVersion V q' (V.zOf w)) ^ 2
      ∂V.law) = ‖q - q'‖ ^ 2 := by
  exact dr_primal_difference_energy (dualWorld V hTarget) q q'

/-- Under [primal TRAE boundedness with envelope B](hyp:hBound) and [dual TRAE
boundedness with envelope B](hyp:qBound), suppose [h belongs to the primal
hypothesis class](hyp:_hh), [h′ belongs to the primal hypothesis class](hyp:hh'),
[q belongs to the dual hypothesis class](hyp:hq), and [q′ belongs to the dual
hypothesis class](hyp:_hq'). Then [the difference between the products of their chosen
primal and dual versions is square integrable, and its population squared
mean is at most twice B squared times the sum of the squared primal and dual
distances](goal). -/
-- @node: dr_product_difference_energy
lemma dr_product_difference_energy (B : ℝ)
    (hBound : TRAEBoundedness V B) (qBound : TRAEBoundedness (dualWorld V hTarget) B)
    (h h' : V.Hbar.toSubmodule) (q q' : V.Qbar.toSubmodule)
    (_hh : h ∈ V.H) (hh' : h' ∈ V.H) (hq : q ∈ V.Q) (_hq' : q' ∈ V.Q) :
    Integrable (fun w => (primalVersion V h (V.xOf w) * dualVersion V q (V.zOf w) -
      primalVersion V h' (V.xOf w) * dualVersion V q' (V.zOf w)) ^ 2) V.law ∧
    (∫ w, (primalVersion V h (V.xOf w) * dualVersion V q (V.zOf w) -
      primalVersion V h' (V.xOf w) * dualVersion V q' (V.zOf w)) ^ 2 ∂V.law) ≤
      2 * B ^ 2 * (‖h - h'‖ ^ 2 + ‖q - q'‖ ^ 2) := by
  let dh := fun w => primalVersion V h (V.xOf w) - primalVersion V h' (V.xOf w)
  let dq := fun w => dualVersion V q (V.zOf w) - dualVersion V q' (V.zOf w)
  let dp := fun w => primalVersion V h (V.xOf w) * dualVersion V q (V.zOf w) -
    primalVersion V h' (V.xOf w) * dualVersion V q' (V.zOf w)
  have hdh : Integrable (fun w => dh w ^ 2) V.law :=
    ((dr_primal_memLp V h).sub (dr_primal_memLp V h')).integrable_sq
  have hdq : Integrable (fun w => dq w ^ 2) V.law :=
    ((dr_dual_memLp V q).sub (dr_dual_memLp V q')).integrable_sq
  have hmajor : Integrable (fun w => 2 * B ^ 2 * (dh w ^ 2 + dq w ^ 2)) V.law :=
    (hdh.add hdq).const_mul _
  have hpoint : ∀ᵐ w ∂V.law, dp w ^ 2 ≤ 2 * B ^ 2 * (dh w ^ 2 + dq w ^ 2) := by
    filter_upwards [hBound.2.2.1, qBound.2.2.1] with w hw qw
    have hb := hw h' hh'
    have qb := qw q hq
    change |dualVersion V q (V.zOf w)| ≤ B at qb
    have hs (x : ℝ) (hx : |x| ≤ B) : x ^ 2 ≤ B ^ 2 :=
      (sq_abs x) ▸ pow_le_pow_left₀ (abs_nonneg x) hx 2
    have h₁ := mul_le_mul_of_nonneg_right (hs _ qb) (sq_nonneg (dh w))
    have h₂ := mul_le_mul_of_nonneg_right (hs _ hb) (sq_nonneg (dq w))
    have hid : dp w = dh w * dualVersion V q (V.zOf w) +
        primalVersion V h' (V.xOf w) * dq w := by dsimp only [dp, dh, dq]; ring
    rw [hid]
    nlinarith only [h₁, h₂, sq_nonneg (dh w * dualVersion V q (V.zOf w) -
      primalVersion V h' (V.xOf w) * dq w)]
  have hdp : Integrable (fun w => dp w ^ 2) V.law := by
    apply hmajor.mono' (((dr_primal_memLp V h).aestronglyMeasurable.mul
      (dr_dual_memLp V q).aestronglyMeasurable).sub
      ((dr_primal_memLp V h').aestronglyMeasurable.mul
        (dr_dual_memLp V q').aestronglyMeasurable) |>.pow 2)
    filter_upwards [hpoint] with w hw
    change ‖dp w ^ 2‖ ≤ _
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (dp w))] using hw
  refine ⟨hdp, ?_⟩
  calc
    _ ≤ ∫ w, 2 * B ^ 2 * (dh w ^ 2 + dq w ^ 2) ∂V.law :=
      integral_mono_ae hdp hmajor hpoint
    _ = _ := by
      rw [integral_const_mul, integral_add hdh hdq,
        dr_primal_difference_energy, dr_dual_difference_energy V hTarget]

/-- Under [primal TRAE boundedness with envelope B](hyp:hBound), [dual TRAE
boundedness with envelope B](hyp:qBound), and [mean-square Hölder continuity of the two score components
with constant C and positive exponents γh and γq](hyp:hScore), suppose
[h belongs to the primal hypothesis class](hyp:hh), [h′ belongs to the primal
hypothesis class](hyp:hh'), [q belongs to the dual hypothesis class](hyp:hq),
and [q′ belongs to the dual hypothesis class](hyp:hq'). Then [the
score difference is square integrable, and its population squared mean is at
most three times C times the sum of the primal distance to power γh and the
dual distance to power γq, plus six times B squared times the sum of the two
squared distances](goal). -/
-- @node: drScore_difference_energy
lemma drScore_difference_energy (B C γh γq : ℝ)
    (hBound : TRAEBoundedness V B) (qBound : TRAEBoundedness (dualWorld V hTarget) B)
    (hScore : ScoreHolderContinuity V C γh γq)
    (h h' : V.Hbar.toSubmodule) (q q' : V.Qbar.toSubmodule)
    (hh : h ∈ V.H) (hh' : h' ∈ V.H) (hq : q ∈ V.Q) (hq' : q' ∈ V.Q) :
    Integrable (fun w => (drScore V h q w - drScore V h' q' w) ^ 2) V.law ∧
    (∫ w, (drScore V h q w - drScore V h' q' w) ^ 2 ∂V.law) ≤
      3 * C * (‖h - h'‖ ^ γh + ‖q - q'‖ ^ γq) +
        6 * B ^ 2 * (‖h - h'‖ ^ 2 + ‖q - q'‖ ^ 2) := by
  let a := fun w => V.mt h w - V.mt h' w
  let b := fun w => V.m q w - V.m q' w
  let c := fun w => primalVersion V h (V.xOf w) * dualVersion V q (V.zOf w) -
    primalVersion V h' (V.xOf w) * dualVersion V q' (V.zOf w)
  have ha := hScore.2.2.1 h hh h' hh'
  have hb := hScore.2.2.2 q hq q' hq'
  obtain ⟨hc, hcBound⟩ := dr_product_difference_energy V hTarget B hBound qBound h h' q q'
    hh hh' hq hq'
  have hmajor : Integrable (fun w => 3 * (a w ^ 2 + b w ^ 2 + c w ^ 2)) V.law :=
    ((ha.1.add hb.1).add hc).const_mul _
  have hpoint (w : 𝒲) : (drScore V h q w - drScore V h' q' w) ^ 2 ≤
      3 * (a w ^ 2 + b w ^ 2 + c w ^ 2) := by
    have hid : drScore V h q w - drScore V h' q' w = a w + b w - c w := by
      dsimp only [drScore, a, b, c]; ring
    rw [hid]
    nlinarith only [sq_nonneg (a w - b w), sq_nonneg (a w + c w),
      sq_nonneg (b w + c w)]
  have hint : Integrable (fun w => (drScore V h q w - drScore V h' q' w) ^ 2) V.law := by
    apply hmajor.mono' (((drScore_integrable V h q).aestronglyMeasurable.sub
      (drScore_integrable V h' q').aestronglyMeasurable).pow 2)
    exact Filter.Eventually.of_forall fun w => by
      change ‖(drScore V h q w - drScore V h' q' w) ^ 2‖ ≤ _
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg (drScore V h q w - drScore V h' q' w))] using hpoint w
  refine ⟨hint, ?_⟩
  calc
    _ ≤ ∫ w, 3 * (a w ^ 2 + b w ^ 2 + c w ^ 2) ∂V.law :=
      integral_mono_ae hint hmajor (Filter.Eventually.of_forall hpoint)
    _ = 3 * ((∫ w, a w ^ 2 ∂V.law) + (∫ w, b w ^ 2 ∂V.law) +
        ∫ w, c w ^ 2 ∂V.law) := by
      rw [integral_const_mul]
      congr 1
      dsimp only [a, b, c]
      have hai := ha.1
      have hbi := hb.1
      integral_linearity
    _ ≤ _ := by linarith only [ha.2, hb.2, hcBound]

end Papers.TsAdaptiveEstimationInference
