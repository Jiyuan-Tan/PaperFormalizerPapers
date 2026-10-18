module
public import Papers.TbsPrteOptimalTransport.Helpers.ConnectedIV
/-!
# Stability of the lower-boundary functional

The scaled quantile tail is Lipschitz in its two unnormalized endpoints,
including a zero lower-support endpoint. This is the deterministic boundary
step of the continuous plug-in rate proof.
-/
@[expose] public section
open MeasureTheory Set
open scoped Topology
namespace Papers.TbsPrteOptimalTransport
universe u v

-- @node: scaledTail
/-- For [a tail function B](hyp:B), [a total mass A](hyp:A), and [a cutoff mass D](hyp:D),
the [scaled tail](goal) is [A times B evaluated at D divided by A when A is positive](step:1),
and [zero otherwise](step:2). -/
noncomputable def scaledTail (B : ℝ → ℝ) (A D : ℝ) : ℝ :=
  if 0 < A then A * B (D / A) else 0

-- @node: scaledTail_bound
/-- If [C is nonnegative](hyp:hC), [A is nonnegative](hyp:hA),
[D is nonnegative](hyp:hD), [D does not exceed A](hyp:hDA), and
[B is bounded in absolute value by C on the unit interval](hyp:hB), then
[the absolute scaled tail at A and D is at most C times A](goal). -/
lemma scaledTail_bound (B : ℝ → ℝ) {C A D : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hD : 0 ≤ D) (hDA : D ≤ A)
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, |B t| ≤ C) :
    |scaledTail B A D| ≤ C * A := by
  by_cases ha : 0 < A
  · rw [scaledTail, if_pos ha, abs_mul, abs_of_nonneg hA]
    have ht : D / A ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hD hA, (div_le_one ha).mpr hDA⟩
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (hB _ ht) hA
  · rw [scaledTail, if_neg ha, abs_zero]
    exact mul_nonneg hC hA

-- @node: scaledTail_lipschitz_ordered
/-- Suppose [C is nonnegative](hyp:hC), [A is nonnegative](hyp:hA),
[A does not exceed A′](hyp:hAA), [D is nonnegative](hyp:hD),
[D does not exceed A](hyp:hDA), [D′ is nonnegative](hyp:hD'), and
[D′ does not exceed A′](hyp:hDA'). If [B is bounded in absolute value by C on the
unit interval](hyp:hB) and [B is Lipschitz there with constant C](hyp:hLip), then
[the absolute change in the scaled tail is at most C times twice the absolute
change in A plus C times the absolute change in D](goal). -/
lemma scaledTail_lipschitz_ordered (B : ℝ → ℝ) {C A A' D D' : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hAA : A ≤ A')
    (hD : 0 ≤ D) (hDA : D ≤ A) (hD' : 0 ≤ D') (hDA' : D' ≤ A')
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, |B t| ≤ C)
    (hLip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |B s - B t| ≤ C * |s - t|) :
    |scaledTail B A' D' - scaledTail B A D| ≤
      C * (2 * |A' - A| + |D' - D|) := by
  have hA' : 0 ≤ A' := hA.trans hAA
  have hdiff : 0 ≤ A' - A := sub_nonneg.mpr hAA
  rw [abs_of_nonneg hdiff]
  by_cases ha : 0 < A
  · have ha' : 0 < A' := ha.trans_le hAA
    have ht : D / A ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hD hA, (div_le_one ha).mpr hDA⟩
    have ht' : D' / A' ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hD' hA', (div_le_one ha').mpr hDA'⟩
    have he : A * (D' / A' - D / A) =
        (D' - D) - (A' - A) * (D' / A') := by
      field_simp
      ring
    have hr : A * |D' / A' - D / A| ≤ |D' - D| + (A' - A) := by
      rw [show A * |D' / A' - D / A| = |A * (D' / A' - D / A)| by
        rw [abs_mul, abs_of_nonneg hA], he]
      calc
        |(D' - D) - (A' - A) * (D' / A')| ≤
            |D' - D| + |(A' - A) * (D' / A')| := abs_sub _ _
        _ ≤ |D' - D| + (A' - A) := by
          rw [abs_mul, abs_of_nonneg hdiff, abs_of_nonneg ht'.1]
          have hh := mul_nonneg hdiff (sub_nonneg.mpr ht'.2)
          nlinarith
    rw [scaledTail, scaledTail, if_pos ha, if_pos ha']
    have heB : A' * B (D' / A') - A * B (D / A) =
        (A' - A) * B (D' / A') + A * (B (D' / A') - B (D / A)) := by ring
    rw [heB]
    calc
      _ ≤ |(A' - A) * B (D' / A')| + |A * (B (D' / A') - B (D / A))| := abs_add_le _ _
      _ ≤ (A' - A) * C + A * (C * |D' / A' - D / A|) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hdiff, abs_of_nonneg hA]
        exact add_le_add (mul_le_mul_of_nonneg_left (hB _ ht') hdiff)
          (mul_le_mul_of_nonneg_left (hLip _ ht' _ ht) hA)
      _ ≤ (A' - A) * C + C * (|D' - D| + (A' - A)) := by
        have hh := mul_le_mul_of_nonneg_left hr hC
        nlinarith
      _ = _ := by ring
  · have hz : A = 0 := le_antisymm (le_of_not_gt ha) hA
    have hzTail : scaledTail B A D = 0 := by rw [scaledTail, if_neg ha]
    rw [hzTail, sub_zero]
    have hb := scaledTail_bound B hC hA' hD' hDA' hB
    rw [hz] at *
    nlinarith [abs_nonneg (D' - D)]

-- @node: scaledTail_lipschitz
/-- Suppose [C is nonnegative](hyp:hC), [A is nonnegative](hyp:hA),
[A′ is nonnegative](hyp:hA'), [D is nonnegative](hyp:hD),
[D does not exceed A](hyp:hDA), [D′ is nonnegative](hyp:hD'), and
[D′ does not exceed A′](hyp:hDA'). If [B is bounded in absolute value by C on the
unit interval](hyp:hB) and [B is Lipschitz there with constant C](hyp:hLip), then
[the absolute change in the scaled tail is at most C times twice the absolute
change in A plus C times the absolute change in D](goal). -/
lemma scaledTail_lipschitz (B : ℝ → ℝ) {C A A' D D' : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hA' : 0 ≤ A')
    (hD : 0 ≤ D) (hDA : D ≤ A) (hD' : 0 ≤ D') (hDA' : D' ≤ A')
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, |B t| ≤ C)
    (hLip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |B s - B t| ≤ C * |s - t|) :
    |scaledTail B A' D' - scaledTail B A D| ≤
      C * (2 * |A' - A| + |D' - D|) := by
  rcases le_total A A' with hh | hh
  · exact scaledTail_lipschitz_ordered B hC hA hh hD hDA hD' hDA' hB hLip
  · simpa only [abs_sub_comm] using
      scaledTail_lipschitz_ordered B hC hA' hh hD' hDA' hD hDA hB hLip

-- @node: unit_interval_integrable
/-- If [Q is integrable on the unit interval](hyp:hQ) and
[s](hyp:hs) and [t](hyp:ht) both belong to that interval, then
[Q is integrable between s and t](goal). -/
lemma unit_interval_integrable (Q : ℝ → ℝ)
    (hQ : IntegrableOn Q (Icc (0 : ℝ) 1)) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable Q volume s t := by
  apply intervalIntegrable_iff.mpr
  apply hQ.mono_set
  intro u hu
  exact ⟨(le_min hs.1 ht.1).trans hu.1.le,
    hu.2.trans (max_le hs.2 ht.2)⟩

-- @node: unit_tail_bound
/-- If [C is nonnegative](hyp:hC), [Q is bounded in absolute value by C on the
unit interval](hyp:hb), and [s belongs to that interval](hyp:hs), then
[the absolute integral of Q from s to one is at most C](goal). -/
lemma unit_tail_bound (Q : ℝ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, |Q t| ≤ C)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    |∫ t in s..1, Q t| ≤ C := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := s) (b := 1) (f := Q) (C := C) (fun t ht => by
      rw [uIoc_of_le hs.2] at ht
      simpa only [Real.norm_eq_abs] using hb t ⟨hs.1.trans ht.1.le, ht.2⟩)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hs.2)] at hh
  nlinarith [mul_nonneg hC hs.1]

-- @node: unit_tail_lipschitz
/-- If [Q is integrable on the unit interval](hyp:hQ),
[its absolute value there is at most C](hyp:hb), and
[s](hyp:hs) and [t](hyp:ht) belong to that interval, then
[the absolute difference between the integrals from s and t to one is at most
C times the distance between s and t](goal). -/
lemma unit_tail_lipschitz (Q : ℝ → ℝ)
    (hQ : IntegrableOn Q (Icc (0 : ℝ) 1)) {C : ℝ}
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, |Q t| ≤ C)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    |(∫ u in s..1, Q u) - ∫ u in t..1, Q u| ≤ C * |s - t| := by
  have he := intervalIntegral.integral_add_adjacent_intervals
    (unit_interval_integrable Q hQ hs ht)
    (unit_interval_integrable Q hQ ht ⟨zero_le_one, le_rfl⟩)
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := s) (b := t) (f := Q) (C := C) (fun u hu => by
      simpa only [Real.norm_eq_abs] using hb u
        ⟨(le_min hs.1 ht.1).trans hu.1.le, hu.2.trans (max_le hs.2 ht.2)⟩)
  rw [← he, add_sub_cancel_right, abs_sub_comm]
  exact hh

-- @node: quantile_tail_endpoint_lipschitz
/-- Suppose [Q is integrable on the unit interval](hyp:hQ),
[C is nonnegative](hyp:hC), [Q is bounded in absolute value by C there](hyp:hb),
[A is nonnegative](hyp:hA), [A′ is nonnegative](hyp:hA'),
[D is nonnegative](hyp:hD), [D does not exceed A](hyp:hDA),
[D′ is nonnegative](hyp:hD'), and [D′ does not exceed A′](hyp:hDA'). Then
[the absolute change in the scaled integral of Q from the cutoff rank to one
is at most C times twice the absolute change in A plus C times the absolute
change in D](goal). -/
lemma quantile_tail_endpoint_lipschitz (Q : ℝ → ℝ)
    (hQ : IntegrableOn Q (Icc (0 : ℝ) 1)) {C A A' D D' : ℝ}
    (hC : 0 ≤ C) (hb : ∀ t ∈ Icc (0 : ℝ) 1, |Q t| ≤ C)
    (hA : 0 ≤ A) (hA' : 0 ≤ A')
    (hD : 0 ≤ D) (hDA : D ≤ A) (hD' : 0 ≤ D') (hDA' : D' ≤ A') :
    |scaledTail (fun s => ∫ t in s..1, Q t) A' D' -
      scaledTail (fun s => ∫ t in s..1, Q t) A D| ≤
      C * (2 * |A' - A| + |D' - D|) := by
  apply scaledTail_lipschitz _ hC hA hA' hD hDA hD' hDA'
  · exact fun s hs => unit_tail_bound Q hC hb hs
  · exact fun s hs t ht => unit_tail_lipschitz Q hQ hb hs ht

-- @node: quantile_tail_primitive
/-- If [Q is integrable on the unit interval](hyp:hQ) and
[s belongs to that interval](hyp:hs), then [the integral of Q from s to one
equals its cumulative integral at one minus its cumulative integral at s](goal). -/
lemma quantile_tail_primitive (Q : ℝ → ℝ)
    (hQ : IntegrableOn Q (Icc (0 : ℝ) 1)) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ t in s..1, Q t) = quantilePrimitive Q 1 - quantilePrimitive Q s := by
  rw [quantilePrimitive, quantilePrimitive,
    ← intervalIntegral.integral_of_le zero_le_one,
    ← intervalIntegral.integral_of_le hs.1]
  exact (intervalIntegral.integral_interval_sub_left
    (unit_interval_integrable Q hQ ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩)
    (unit_interval_integrable Q hQ ⟨le_rfl, zero_le_one⟩ hs)).symm

-- @node: quantile_tail_law_stability
/-- If [Q](hyp:hQ) and [Q′](hyp:hQ') are integrable on the unit interval,
[A is nonnegative](hyp:hA), [D is nonnegative](hyp:hD), and
[D does not exceed A](hyp:hDA), then [replacing Q by Q′ changes the scaled tail
integral by at most A times the integral of their absolute difference over the
unit interval](goal). -/
lemma quantile_tail_law_stability (Q Q' : ℝ → ℝ)
    (hQ : IntegrableOn Q (Icc (0 : ℝ) 1))
    (hQ' : IntegrableOn Q' (Icc (0 : ℝ) 1)) {A D : ℝ}
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hDA : D ≤ A) :
    |scaledTail (fun s => ∫ t in s..1, Q' t) A D -
      scaledTail (fun s => ∫ t in s..1, Q t) A D| ≤
      A * ∫ t in Icc (0 : ℝ) 1, |Q' t - Q t| := by
  have hi : IntegrableOn (fun t => |Q' t - Q t|) (Icc (0 : ℝ) 1) :=
    (hQ'.sub hQ).abs
  have hn : 0 ≤ ∫ t in Icc (0 : ℝ) 1, |Q' t - Q t| :=
    integral_nonneg fun _ => abs_nonneg _
  by_cases ha : 0 < A
  · have hs : D / A ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hD hA, (div_le_one ha).mpr hDA⟩
    simp only [scaledTail, if_pos ha]
    rw [← mul_sub, abs_mul, abs_of_nonneg hA,
      ← intervalIntegral.integral_sub
        (unit_interval_integrable Q' hQ' hs ⟨zero_le_one, le_rfl⟩)
        (unit_interval_integrable Q hQ hs ⟨zero_le_one, le_rfl⟩),
      intervalIntegral.integral_of_le hs.2]
    apply mul_le_mul_of_nonneg_left _ hA
    apply abs_integral_le_integral_abs.trans
    apply setIntegral_mono_set hi (Filter.Eventually.of_forall (fun _ => abs_nonneg _))
    apply Filter.Eventually.of_forall
    intro t ht
    exact ⟨hs.1.trans ht.1.le, ht.2⟩
  · simp only [scaledTail, if_neg ha, sub_self, abs_zero]
    exact mul_nonneg hA hn

-- @node: quantile_tail_perturbation
/-- Suppose [Q](hyp:hQ) and [Q′](hyp:hQ') are integrable on the unit interval,
[C is nonnegative](hyp:hC), [Q′ is bounded in absolute value by C there](hyp:hb),
[A is nonnegative](hyp:hA), [A′ is nonnegative](hyp:hA'),
[D is nonnegative](hyp:hD), [D does not exceed A](hyp:hDA),
[D′ is nonnegative](hyp:hD'), and [D′ does not exceed A′](hyp:hDA'). Then
[the change in the scaled tail integral is bounded by C times twice the absolute
mass change plus the absolute cutoff change, together with A times the integrated
absolute difference between Q′ and Q](goal). -/
lemma quantile_tail_perturbation (Q Q' : ℝ → ℝ)
    (hQ : IntegrableOn Q (Icc (0 : ℝ) 1))
    (hQ' : IntegrableOn Q' (Icc (0 : ℝ) 1)) {C A A' D D' : ℝ}
    (hC : 0 ≤ C) (hb : ∀ t ∈ Icc (0 : ℝ) 1, |Q' t| ≤ C)
    (hA : 0 ≤ A) (hA' : 0 ≤ A')
    (hD : 0 ≤ D) (hDA : D ≤ A) (hD' : 0 ≤ D') (hDA' : D' ≤ A') :
    |scaledTail (fun s => ∫ t in s..1, Q' t) A' D' -
      scaledTail (fun s => ∫ t in s..1, Q t) A D| ≤
      C * (2 * |A' - A| + |D' - D|) +
        A * ∫ t in Icc (0 : ℝ) 1, |Q' t - Q t| := by
  exact (abs_sub_le _ (scaledTail (fun s => ∫ t in s..1, Q' t) A D) _).trans
    (add_le_add
      (quantile_tail_endpoint_lipschitz Q' hQ' hC hb hA hA' hD hDA hD' hDA')
      (quantile_tail_law_stability Q Q' hQ hQ' hA hD hDA))

-- @node: boundary_primitive_scaledTail
/-- If [Q is integrable on the unit interval](hyp:hQ),
[A is nonnegative](hyp:hA), and [q is nonnegative](hyp:hq), then
[the negative A-weighted difference of cumulative integrals between one and the
smaller of one and q divided by A, defined as zero when A is zero, equals the
negative scaled tail integral with cutoff mass equal to the smaller of A and q](goal). -/
lemma boundary_primitive_scaledTail (Q : ℝ → ℝ)
    (hQ : IntegrableOn Q (Icc (0 : ℝ) 1)) {A q : ℝ}
    (hA : 0 ≤ A) (hq : 0 ≤ q) :
    (if 0 < A then -A * (quantilePrimitive Q 1 -
        quantilePrimitive Q (min 1 (q / A))) else 0) =
      -scaledTail (fun s => ∫ t in s..1, Q t) A (min A q) := by
  by_cases ha : 0 < A
  · have hs : min A q / A ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (le_min hA hq) hA, (div_le_one ha).mpr (min_le_left _ _)⟩
    have he : min 1 (q / A) = min A q / A := by
      rw [← min_div_div_right hA, div_self (ne_of_gt ha)]
    rw [if_pos ha, scaledTail, if_pos ha, he, quantile_tail_primitive Q hQ hs]
    ring
  · simp only [if_neg ha, scaledTail, neg_zero]

-- @node: boundary_primitive_perturbation
/-- Suppose [Q](hyp:hQ) and [Q′](hyp:hQ') are integrable on the unit interval,
[C is nonnegative](hyp:hC), [Q′ is bounded in absolute value by C there](hyp:hb),
[A](hyp:hA), [A′](hyp:hA'), [q](hyp:hq), and [q′](hyp:hq') are nonnegative.
Then [the absolute change in the negative mass-weighted tail primitive, using
cutoff rank q divided by A capped at one and value zero at zero mass, is at most
C times twice the absolute change in A plus the absolute change in the smaller
of A and q, together with A times the integrated absolute difference of Q′ and Q](goal). -/
lemma boundary_primitive_perturbation (Q Q' : ℝ → ℝ)
    (hQ : IntegrableOn Q (Icc (0 : ℝ) 1))
    (hQ' : IntegrableOn Q' (Icc (0 : ℝ) 1)) {C A A' q q' : ℝ}
    (hC : 0 ≤ C) (hb : ∀ t ∈ Icc (0 : ℝ) 1, |Q' t| ≤ C)
    (hA : 0 ≤ A) (hA' : 0 ≤ A') (hq : 0 ≤ q) (hq' : 0 ≤ q') :
    |(if 0 < A' then -A' * (quantilePrimitive Q' 1 -
        quantilePrimitive Q' (min 1 (q' / A'))) else 0) -
      (if 0 < A then -A * (quantilePrimitive Q 1 -
        quantilePrimitive Q (min 1 (q / A))) else 0)| ≤
      C * (2 * |A' - A| + |min A' q' - min A q|) +
        A * ∫ t in Icc (0 : ℝ) 1, |Q' t - Q t| := by
  rw [boundary_primitive_scaledTail Q' hQ' hA' hq',
    boundary_primitive_scaledTail Q hQ hA hq, neg_sub_neg, abs_sub_comm]
  exact quantile_tail_perturbation Q Q' hQ hQ' hC hb hA hA'
    (le_min hA hq) (min_le_left _ _) (le_min hA' hq') (min_le_left _ _)

-- @node: fittedInt_lower_error
/-- Suppose [the policy map is jointly measurable and maps unit-interval
propensities to the unit interval](hyp:hphi), [p](hyp:hp) and [p′](hyp:hp')
take values in the unit interval, [C is nonnegative](hyp:hC),
[Q](hyp:hQ) and [Q′](hyp:hQ') are integrable over unit ranks at the observation's
covariate, and [Q′ is bounded there in absolute value by C](hyp:hb). Then
[the absolute change in the fitted lower-bound integrand is bounded by the sum
of C times the sum of twice the absolute change in the lower propensity endpoint
and the absolute change in the smaller of that endpoint and policy propensity,
the integrated absolute
quantile error weighted by the original lower propensity endpoint, the absolute
regression changes at the clamped policy and observed propensity, and the change
in policy excess above the upper propensity endpoint weighted by the absolute
lower outcome bound](goal). -/
lemma fittedInt_lower_error
    {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z]
    [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
    [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
    (M : LatentIVModel Ω X Z) (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (p p' : Z → X → ℝ) (g g' : ℝ → X → ℝ) (Q Q' : X → ℝ → ℝ)
    (hp : ∀ z x, p z x ∈ Icc (0 : ℝ) 1)
    (hp' : ∀ z x, p' z x ∈ Icc (0 : ℝ) 1)
    (o : Obs X Z) {C : ℝ} (hC : 0 ≤ C)
    (hQ : IntegrableOn (Q o.1) (Icc (0 : ℝ) 1))
    (hQ' : IntegrableOn (Q' o.1) (Icc (0 : ℝ) 1))
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, |Q' o.1 t| ≤ C) :
    |fittedInt M false phi p' g' (fun x => quantilePrimitive (Q' x)) o -
      fittedInt M false phi p g (fun x => quantilePrimitive (Q x)) o| ≤
      C * (2 * |pLow p' o.1 - pLow p o.1| +
        |min (pLow p' o.1) (policyProp phi p' o.2.1 o.1) -
          min (pLow p o.1) (policyProp phi p o.2.1 o.1)|) +
      pLow p o.1 * (∫ t in Icc (0 : ℝ) 1, |Q' o.1 t - Q o.1 t|) +
      (|g' (clampPolicy p' (policyProp phi p') o.2.1 o.1) o.1 -
          g (clampPolicy p (policyProp phi p) o.2.1 o.1) o.1| +
        |g' (p' o.2.1 o.1) o.1 - g (p o.2.1 o.1) o.1|) +
      |M.yMin| * |max 0 (policyProp phi p' o.2.1 o.1 - pHigh p' o.1) -
        max 0 (policyProp phi p o.2.1 o.1 - pHigh p o.1)| := by
  have hA := (propensity_support_endpoints p hp o.1).1.1
  have hA' := (propensity_support_endpoints p' hp' o.1).1.1
  have hq := (hphi.2 o.2.1 o.1 (p o.2.1 o.1) (hp _ _)).1
  have hq' := (hphi.2 o.2.1 o.1 (p' o.2.1 o.1) (hp' _ _)).1
  have hboundary := boundary_primitive_perturbation (Q o.1) (Q' o.1)
    hQ hQ' hC hb hA hA' hq hq'
  unfold fittedInt
  simp only [Bool.false_eq_true, if_false]
  set b' : ℝ := (if 0 < pLow p' o.1 then -pLow p' o.1 *
    (quantilePrimitive (Q' o.1) 1 - quantilePrimitive (Q' o.1)
      (min 1 (phi o.2.1 o.1 (p' o.2.1 o.1) / pLow p' o.1))) else 0)
  set b : ℝ := (if 0 < pLow p o.1 then -pLow p o.1 *
    (quantilePrimitive (Q o.1) 1 - quantilePrimitive (Q o.1)
      (min 1 (phi o.2.1 o.1 (p o.2.1 o.1) / pLow p o.1))) else 0)
  calc
    _ = |(b' - b) +
        ((g' (clampPolicy p' (policyProp phi p') o.2.1 o.1) o.1 -
            g (clampPolicy p (policyProp phi p) o.2.1 o.1) o.1) -
          (g' (p' o.2.1 o.1) o.1 - g (p o.2.1 o.1) o.1)) +
        M.yMin * (max 0 (policyProp phi p' o.2.1 o.1 - pHigh p' o.1) -
          max 0 (policyProp phi p o.2.1 o.1 - pHigh p o.1))| := by
      congr 1
      dsimp only [policyProp]
      ring
    _ ≤ _ := by
      apply (abs_add_le _ _).trans
      rw [abs_mul]
      apply add_le_add _ le_rfl
      apply (abs_add_le _ _).trans
      exact add_le_add hboundary (abs_sub _ _)

-- @node: monotone_uniform_map_quantile_ae
/-- If [Q is nondecreasing on the open unit interval](hyp:hQ), then
[Q agrees almost everywhere under the uniform rank distribution with the
quantile function of the distribution obtained by applying Q to a uniform rank](goal). -/
lemma monotone_uniform_map_quantile_ae (Q : ℝ → ℝ)
    (hQ : MonotoneOn Q (Ioo (0 : ℝ) 1)) :
    Q =ᵐ[Causalean.Stat.unifOI] Causalean.Stat.quantile (Causalean.Stat.unifOI.map Q) := by
  have hmeas : AEMeasurable Q Causalean.Stat.unifOI :=
    aemeasurable_restrict_of_monotoneOn measurableSet_Ioo hQ
  letI : IsProbabilityMeasure (Causalean.Stat.unifOI.map Q) :=
    Measure.isProbabilityMeasure_map hmeas
  have hc := Toolkit.Tricks.Probability.Moments.countable_ne_quantile_of_monotoneOn_of_map_eq
    (Causalean.Stat.unifOI.map Q) Q hQ rfl
  apply (ae_restrict_iff' measurableSet_Ioo).2
  filter_upwards [hc.ae_notMem volume] with t ht hmem
  exact not_ne_iff.mp (fun hne => ht ⟨hmem, hne⟩)

-- @node: quantile_distance_uniform_map
/-- If [Q is nondecreasing on the open unit interval](hyp:hQ), then
[the integrated quantile distance between the distribution of Q at a uniform
rank and ν equals the integral over unit ranks of the absolute difference
between Q and the quantile function of ν](goal). -/
lemma quantile_distance_uniform_map (Q : ℝ → ℝ) (ν : Measure ℝ)
    (hQ : MonotoneOn Q (Ioo (0 : ℝ) 1)) :
    quantileDistanceIntegral (Causalean.Stat.unifOI.map Q) ν =
      ∫ t in Icc (0 : ℝ) 1, |Q t - Causalean.Stat.quantile ν t| := by
  unfold quantileDistanceIntegral
  rw [← restrict_Ioo_eq_restrict_Icc]
  apply integral_congr_ae
  exact (monotone_uniform_map_quantile_ae Q hQ).mono fun t ht => by
    dsimp only
    rw [ht]

-- @node: boundary_primitive_wasserstein_perturbation
/-- Suppose [the quantile function of ν](hyp:hQ) and [Q′](hyp:hQ') are integrable
on the unit interval, [Q′ is nondecreasing on its interior](hyp:hmono),
[C is nonnegative](hyp:hC), [Q′ is bounded in absolute value by C](hyp:hb), and
[A](hyp:hA), [A′](hyp:hA'), [q](hyp:hq), and [q′](hyp:hq') are nonnegative.
Then [the absolute change in the negative mass-weighted tail primitive, with
cutoff rank capped at one and value zero at zero mass, is at most C times twice
the absolute mass change plus the absolute change in the smaller of mass and
cutoff, together with A times the integrated quantile distance between the law
of Q′ at a uniform rank and ν](goal). -/
lemma boundary_primitive_wasserstein_perturbation (ν : Measure ℝ) (Q' : ℝ → ℝ)
    (hQ : IntegrableOn (Causalean.Stat.quantile ν) (Icc (0 : ℝ) 1))
    (hQ' : IntegrableOn Q' (Icc (0 : ℝ) 1))
    (hmono : MonotoneOn Q' (Ioo (0 : ℝ) 1)) {C A A' q q' : ℝ}
    (hC : 0 ≤ C) (hb : ∀ t ∈ Icc (0 : ℝ) 1, |Q' t| ≤ C)
    (hA : 0 ≤ A) (hA' : 0 ≤ A') (hq : 0 ≤ q) (hq' : 0 ≤ q') :
    |(if 0 < A' then -A' * (quantilePrimitive Q' 1 -
        quantilePrimitive Q' (min 1 (q' / A'))) else 0) -
      (if 0 < A then -A * (quantilePrimitive (Causalean.Stat.quantile ν) 1 -
        quantilePrimitive (Causalean.Stat.quantile ν) (min 1 (q / A))) else 0)| ≤
      C * (2 * |A' - A| + |min A' q' - min A q|) +
        A * quantileDistanceIntegral (Causalean.Stat.unifOI.map Q') ν := by
  rw [quantile_distance_uniform_map Q' ν hmono]
  exact boundary_primitive_perturbation (Causalean.Stat.quantile ν) Q'
    hQ hQ' hC hb hA hA' hq hq'

-- @node: bounded_monotone_rank_integrable
/-- If [Q is nondecreasing on the open unit interval](hyp:hQ) and
[bounded in absolute value by C on the closed unit interval](hyp:hb), then
[Q is integrable on the closed unit interval](goal). -/
lemma bounded_monotone_rank_integrable (Q : ℝ → ℝ)
    (hQ : MonotoneOn Q (Ioo (0 : ℝ) 1)) {C : ℝ}
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, |Q t| ≤ C) :
    IntegrableOn Q (Icc (0 : ℝ) 1) := by
  change Integrable Q (volume.restrict (Icc (0 : ℝ) 1))
  rw [← restrict_Ioo_eq_restrict_Icc]
  apply Integrable.of_bound
    (aemeasurable_restrict_of_monotoneOn measurableSet_Ioo hQ).aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  simpa only [Real.norm_eq_abs] using hb t ⟨ht.1.le, ht.2.le⟩

-- @node: fittedInt_lower_bounded
/-- Suppose [the policy map is jointly measurable and maps unit-interval
propensities to the unit interval](hyp:hphi), [propensities lie in the unit
interval](hyp:hp), [C is nonnegative](hyp:hC), [the absolute lower outcome bound
is at most C](hyp:hy), [the regression function is bounded in absolute value by C
at every covariate and unit rank](hyp:hg), [each covariate's quantile curve is
integrable over unit ranks](hyp:hQ), and [all these curves are bounded in
absolute value by C there](hyp:hb). Then [the fitted lower-bound integrand at
any observation has absolute value at most four times C](goal). -/
lemma fittedInt_lower_bounded
    {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z]
    [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
    [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]
    (M : LatentIVModel Ω X Z) (phi : Z → X → ℝ → ℝ) (hphi : IsPolicyMap phi)
    (p : Z → X → ℝ) (g : ℝ → X → ℝ) (Q : X → ℝ → ℝ)
    (hp : ∀ z x, p z x ∈ Icc (0 : ℝ) 1)
    {C : ℝ} (hC : 0 ≤ C) (hy : |M.yMin| ≤ C)
    (hg : ∀ t x, t ∈ Icc (0 : ℝ) 1 → |g t x| ≤ C)
    (hQ : ∀ x, IntegrableOn (Q x) (Icc (0 : ℝ) 1))
    (hb : ∀ x t, t ∈ Icc (0 : ℝ) 1 → |Q x t| ≤ C) (o : Obs X Z) :
    |fittedInt M false phi p g (fun x => quantilePrimitive (Q x)) o| ≤ 4 * C := by
  have he := propensity_support_endpoints p hp o.1
  have hq := hphi.2 o.2.1 o.1 (p o.2.1 o.1) (hp _ _)
  have hclamp : clampPolicy p (policyProp phi p) o.2.1 o.1 ∈ Icc (0 : ℝ) 1 := by
    exact ⟨le_min he.2.1.1 (le_max_of_le_left he.1.1),
      (min_le_left _ _).trans he.2.1.2⟩
  have hboundary :
      |if 0 < pLow p o.1 then -pLow p o.1 *
        (quantilePrimitive (Q o.1) 1 - quantilePrimitive (Q o.1)
          (min 1 (policyProp phi p o.2.1 o.1 / pLow p o.1))) else 0| ≤ C := by
    rw [boundary_primitive_scaledTail (Q o.1) (hQ o.1)
      (q := policyProp phi p o.2.1 o.1) he.1.1 hq.1, abs_neg]
    exact (scaledTail_bound _ hC he.1.1 (le_min he.1.1 hq.1)
      (min_le_left _ _) (fun t ht => unit_tail_bound (Q o.1) hC (hb o.1) ht)).trans
      (by nlinarith [he.1.2])
  have htail : |M.yMin * max 0 (policyProp phi p o.2.1 o.1 - pHigh p o.1)| ≤ C := by
    have ht0 : 0 ≤ max 0 (policyProp phi p o.2.1 o.1 - pHigh p o.1) := le_max_left _ _
    have ht1 : max 0 (policyProp phi p o.2.1 o.1 - pHigh p o.1) ≤ 1 :=
      max_le zero_le_one (by dsimp only [policyProp]; linarith [he.2.1.1, hq.2])
    rw [abs_mul, abs_of_nonneg ht0]
    exact (mul_le_mul_of_nonneg_right hy ht0).trans (by nlinarith)
  have hgq := hg _ o.1 hclamp
  have hgp := hg _ o.1 (hp o.2.1 o.1)
  change |(if 0 < pLow p o.1 then -pLow p o.1 *
      (quantilePrimitive (Q o.1) 1 - quantilePrimitive (Q o.1)
        (min 1 (policyProp phi p o.2.1 o.1 / pLow p o.1))) else 0) +
    g (clampPolicy p (policyProp phi p) o.2.1 o.1) o.1 - g (p o.2.1 o.1) o.1 +
    M.yMin * max 0 (policyProp phi p o.2.1 o.1 - pHigh p o.1)| ≤ _
  exact (abs_add_le _ _).trans ((add_le_add
    ((abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans
      (add_le_add hboundary hgq)) hgp)) htail).trans (by ring_nf; rfl))

end Papers.TbsPrteOptimalTransport
