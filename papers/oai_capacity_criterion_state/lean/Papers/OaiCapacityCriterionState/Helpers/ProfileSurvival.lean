module

public import Papers.OaiCapacityCriterionState.Helpers.FlowPathAverages

/-! # Uniform information retained by terminally degraded flow experiments

The local moment estimates and finite descendant loss bound yield a positive
root information bound with a single scale independent of the terminal depth.
-/

public section

open scoped BigOperators

namespace OaiCapacityCriterionState

-- @node: companion_profile_deficit_envelope
/-- Assuming [the companion moment-saving property](hyp:hCompanion) and [a channel
parameter strictly between zero and one](hyp:hlam), [there is a nonnegative constant
such that every profile taking values between zero and three and conserving
squared-channel-weighted mass yields degraded tree experiments, and its one-step
quadratic information deficit is at most that constant times the local profile
value times the sum of the cubic-channel-weighted terminal profile and the
accumulated cubic-channel-weighted squared profiles](goal). -/
lemma companion_profile_deficit_envelope (hCompanion : CompanionMomentSaving)
    (lam : ℝ) (hlam : MainLambda lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {B : ℕ} (T : BoundedTree B)
      (X : List (Fin B) → ℝ),
      (∀ v ∈ T.verts, X v ∈ Set.Icc 0 3) →
      (∀ v ∈ T.verts, ∑ w ∈ T.children v, sqParam lam * X w = X v) →
      (∀ n v, v ∈ T.verts →
        FiniteLawDegrades (treeExperimentLaw T lam n v) (profileExperimentLaw T lam X n v)) ∧
      ∀ n v, v ∈ T.verts →
        ((∑ w ∈ T.children v, sqParam lam * quadInfo (profileExperimentLaw T lam X n w)) -
          quadInfo (profileExperimentLaw T lam X (n + 1) v)) ≤
          C * X v * (T.weightedDescendantSum (lam ^ 3) X (n + 1) v +
            ∑ k ∈ Finset.range (n + 1),
              T.weightedDescendantSum (lam ^ 3) (fun u => X u ^ 2) k v) := by
  classical
  obtain ⟨K, hK, hbounds⟩ := companion_profile_moment_bounds hCompanion lam hlam
  let C0 := 1 + K / 2
  have hC0 : 1 ≤ C0 := by dsimp [C0]; linarith
  refine ⟨7 * C0, by positivity, ?_⟩
  intro B T X hX hconserve
  obtain ⟨hprops, hlocal⟩ := hbounds T X hX hconserve
  let H (n : ℕ) (v : List (Fin B)) := T.weightedDescendantSum (lam ^ 3) X n v +
    ∑ k ∈ Finset.range n, T.weightedDescendantSum (lam ^ 3) (fun u => X u ^ 2) k v
  have hHstep (n : ℕ) (v : List (Fin B)) :
      H (n + 1) v = lam ^ 3 * (∑ w ∈ T.children v, H n w) + X v ^ 2 :=
    T.weightedDescendantSum_envelope_step (lam ^ 3) X (fun u => X u ^ 2) n v
  have hcost (n : ℕ) (v : List (Fin B))
      (hh : ∀ w ∈ T.children v, absThird (profileExperimentLaw T lam X n w) ≤ C0 * H n w) :
      (∑ w ∈ T.children v, lam ^ 3 * absThird (profileExperimentLaw T lam X n w)) +
        K / 2 * X v ^ 2 ≤ C0 * H (n + 1) v := by
    have hb := Finset.sum_le_sum (fun w hw =>
      mul_le_mul_of_nonneg_left (hh w hw) (pow_nonneg hlam.1.le 3))
    rw [hHstep]
    have hs : (∑ w ∈ T.children v, lam ^ 3 * (C0 * H n w)) =
        C0 * (lam ^ 3 * ∑ w ∈ T.children v, H n w) := by
      simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
    rw [hs] at hb
    have he := mul_le_mul_of_nonneg_right
      (show K / 2 ≤ C0 by dsimp [C0]; linarith) (sq_nonneg (X v))
    nlinarith
  have hh : ∀ n v, v ∈ T.verts → absThird (profileExperimentLaw T lam X n v) ≤ C0 * H n v := by
    intro n
    induction n with
    | zero =>
        intro v hv
        have hb := (profileExperimentLaw_boundary_moments T lam X v (hX v hv)).2
        have hs : Real.sqrt (X v / 3) ≤ 1 := Real.sqrt_le_one.mpr (by linarith [(hX v hv).2])
        have hlin := mul_le_mul_of_nonneg_right hs (hX v hv).1
        have hscale := mul_le_mul_of_nonneg_right hC0 (hX v hv).1
        simpa only [H, BoundedTree.weightedDescendantSum, Finset.range_zero,
          Finset.sum_empty, add_zero] using hb.trans (hlin.trans (by simpa using hscale))
    | succ n ih =>
        intro v hv
        apply ((hlocal n v hv).1).trans
        apply hcost n v
        intro w hw
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
        exact ih _ (Finset.mem_filter.mp ha).2
  refine ⟨fun n v hv => (hprops n v hv).2.1, ?_⟩
  intro n v hv
  have hc := hcost n v (fun w hw => by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
    exact hh n _ (Finset.mem_filter.mp ha).2)
  have he := mul_le_mul_of_nonneg_left hc (mul_nonneg (by norm_num : (0 : ℝ) ≤ 7) (hX v hv).1)
  exact ((hlocal n v hv).2.2).trans (by dsimp only [H] at he; nlinarith [he])

-- @node: companion_scaled_profile_root_bound
/-- Assuming [the companion moment-saving property](hyp:hCompanion) and [a channel
parameter strictly between zero and one](hyp:hlam), [there is a nonnegative constant
C, uniform over trees and depths, such that a flow with ray potentials at most
one and mass m, scaled by a nonnegative ε with ε(1 + m) ≤ 3, produces a degraded
root profile experiment whose quadratic information is at least
εm − Cεm((m² + 1)ε² + (1 + m)ε)/(1 − λ)](goal). -/
lemma companion_scaled_profile_root_bound (hCompanion : CompanionMomentSaving)
    (lam : ℝ) (hlam : MainLambda lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {B : ℕ} (T : BoundedTree B)
      (theta : List (Fin B) → ℝ), IsFlow T theta →
      (∀ xi ∈ T.rays, pathPotential lam theta xi ≤ 1) →
      ∀ eps : ℝ, 0 ≤ eps → eps * (1 + flowMass T theta) ≤ 3 → ∀ N : ℕ,
        FiniteLawDegrades (treeExperimentLaw T lam N [])
          (profileExperimentLaw T lam (fun v => eps * normalizedFlow T lam theta v) N []) ∧
        eps * flowMass T theta - C * ((eps * flowMass T theta) *
          (((flowMass T theta ^ 2 + 1) * eps ^ 2) / (1 - lam) +
            ((1 + flowMass T theta) * eps) / (1 - lam))) ≤
          quadInfo (profileExperimentLaw T lam
            (fun v => eps * normalizedFlow T lam theta v) N []) := by
  classical
  obtain ⟨C, hC, henv⟩ := companion_profile_deficit_envelope hCompanion lam hlam
  refine ⟨C, hC, ?_⟩
  intro B T theta htheta hpotential eps heps hsmall N
  let X := fun v => eps * normalizedFlow T lam theta v
  obtain ⟨hX, hconserve⟩ := scaled_normalizedFlow_profile T lam hlam theta htheta
    hpotential eps heps hsmall
  obtain ⟨hdeg, hcost⟩ := henv T X hX hconserve
  refine ⟨hdeg N [] T.nil_mem, ?_⟩
  let loss := ∑ i ∈ Finset.range N, sqParam lam ^ i * ∑ v ∈ T.level i,
    ((∑ w ∈ T.children v, sqParam lam *
      quadInfo (profileExperimentLaw T lam X (N - (i + 1)) w)) -
        quadInfo (profileExperimentLaw T lam X (N - i) v))
  let L := ∑ i ∈ Finset.range N, sqParam lam ^ i * ∑ v ∈ T.level i,
    X v * (T.weightedDescendantSum (lam ^ 3) X (N - i) v +
      ∑ k ∈ Finset.range (N - i), T.weightedDescendantSum (lam ^ 3) (fun u => X u ^ 2) k v)
  have hloss : loss ≤ C * L := by
    dsimp only [loss, L]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hni : N - (i + 1) + 1 = N - i := by
      simp only [Finset.mem_range] at hi
      omega
    have hs := Finset.sum_le_sum (s := T.level i) (fun v hv => by
      have hvT := ((T.mem_level_iff v i).mp hv).1
      have hc := hcost (N - (i + 1)) v hvT
      rw [hni] at hc
      exact hc)
    calc
      _ ≤ sqParam lam ^ i * ∑ v ∈ T.level i,
          C * X v * (T.weightedDescendantSum (lam ^ 3) X (N - i) v +
            ∑ k ∈ Finset.range (N - i),
              T.weightedDescendantSum (lam ^ 3) (fun u => X u ^ 2) k v) :=
        mul_le_mul_of_nonneg_left hs (pow_nonneg (sq_nonneg lam) i)
      _ = _ := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intros
        ring
  have hb := mul_le_mul_of_nonneg_left
    (scaled_profile_descendant_loss_bound T lam hlam theta htheta hpotential eps heps N) hC
  have ht := profileExperimentLaw_deficit_telescope T lam X hX hconserve N
  have hroot : X [] = eps * flowMass T theta := by simp [X, normalizedFlow]
  change quadInfo (profileExperimentLaw T lam X N []) = X [] - loss at ht
  rw [hroot] at ht
  exact (sub_le_sub_left (hloss.trans hb) _).trans_eq ht.symm

-- @node: exists_uniform_profile_scale
/-- If [λ is less than one](hyp:hlam), [C is nonnegative](hyp:hC), and [m is
nonnegative](hyp:hm), [there is a positive scale ε at most one such that
ε(1 + m) ≤ 3 and C((m² + 1)ε² + (1 + m)ε)/(1 − λ) ≤ 1/2](goal). -/
lemma exists_uniform_profile_scale (lam C m : ℝ) (hlam : lam < 1)
    (hC : 0 ≤ C) (hm : 0 ≤ m) :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 ∧ eps * (1 + m) ≤ 3 ∧
      C * (((m ^ 2 + 1) * eps ^ 2) / (1 - lam) +
        ((1 + m) * eps) / (1 - lam)) ≤ 1 / 2 := by
  obtain ⟨a, ha, ha1, hscale⟩ := exists_uniform_path_loss_scale lam C (m ^ 2 + 1) (1 + m)
    hlam hC (by positivity) (by linarith)
  let eps := a / (1 + m)
  have hden : 0 < 1 + m := by linarith
  have heps : 0 < eps := div_pos ha hden
  have hle : eps ≤ a := (div_le_iff₀ hden).mpr (by nlinarith)
  refine ⟨eps, heps, hle.trans ha1, ?_, ?_⟩
  · dsimp only [eps]
    rw [div_mul_cancel₀ _ hden.ne']
    linarith
  · apply le_trans _ hscale
    apply mul_le_mul_of_nonneg_left _ hC
    apply add_le_add <;> apply div_le_div_of_nonneg_right _ (sub_pos.mpr hlam).le
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ heps.le hle 2) (by positivity)
    · exact mul_le_mul_of_nonneg_left hle hden.le

-- @node: companion_profile_uniform_root_lower_bound
/-- Assuming [the companion moment-saving property](hyp:hCompanion), [a channel
parameter strictly between zero and one](hyp:hlam), [a flow on the tree](hyp:htheta)
with [all ray potentials at most one](hyp:hpotential) and [positive mass](hyp:hmass),
[there is a single positive scale ε such that, at every depth, the normalized flow
profile experiment at the root is degraded from the tree experiment and has
quadratic information at least ε times the flow mass divided by two](goal). -/
lemma companion_profile_uniform_root_lower_bound (hCompanion : CompanionMomentSaving)
    {B : ℕ} (T : BoundedTree B) (lam : ℝ) (hlam : MainLambda lam)
    (theta : List (Fin B) → ℝ) (htheta : IsFlow T theta)
    (hpotential : ∀ xi ∈ T.rays, pathPotential lam theta xi ≤ 1)
    (hmass : 0 < flowMass T theta) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ N : ℕ,
      FiniteLawDegrades (treeExperimentLaw T lam N [])
        (profileExperimentLaw T lam (fun v => eps * normalizedFlow T lam theta v) N []) ∧
      eps * flowMass T theta / 2 ≤
        quadInfo (profileExperimentLaw T lam
          (fun v => eps * normalizedFlow T lam theta v) N []) := by
  obtain ⟨C, hC, hbound⟩ := companion_scaled_profile_root_bound hCompanion lam hlam
  obtain ⟨eps, heps, _, hsmall, hscale⟩ := exists_uniform_profile_scale lam C
    (flowMass T theta) hlam.2 hC hmass.le
  refine ⟨eps, heps, fun N => ?_⟩
  obtain ⟨hdeg, hinfo⟩ := hbound T theta htheta hpotential eps heps.le hsmall N
  refine ⟨hdeg, ?_⟩
  have hs := mul_le_mul_of_nonneg_left hscale (mul_nonneg heps.le hmass.le)
  nlinarith

-- @node: capacity_pos_implies_treeExperiment_uniform_pos
/-- Assuming [the companion moment-saving property](hyp:hCompanion), [a channel
parameter strictly between zero and one](hyp:hlam), and [positive cubic capacity
of the tree](hyp:hcap), [the root tree experiments have quadratic information
bounded below by a single positive constant at every depth](goal). -/
lemma capacity_pos_implies_treeExperiment_uniform_pos (hCompanion : CompanionMomentSaving)
    {B : ℕ} (T : BoundedTree B) (lam : ℝ) (hlam : MainLambda lam)
    (hcap : 0 < capacity3 T lam) :
    ∃ c : ℝ, 0 < c ∧ ∀ N, c ≤ quadInfo (treeExperimentLaw T lam N []) := by
  obtain ⟨theta, htheta, hpotential, hmass⟩ := (capacity_pos_iff_exists_flow T lam).mp hcap
  obtain ⟨eps, heps, hbound⟩ := companion_profile_uniform_root_lower_bound
    hCompanion T lam hlam theta htheta hpotential hmass
  refine ⟨eps * flowMass T theta / 2, by positivity, fun N => ?_⟩
  exact (hbound N).2.trans (hbound N).1.quadInfo_le

end OaiCapacityCriterionState
