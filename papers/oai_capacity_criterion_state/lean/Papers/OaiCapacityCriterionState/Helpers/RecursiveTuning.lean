module

public import Papers.OaiCapacityCriterionState.Helpers.TunedProducts
public import Papers.OaiCapacityCriterionState.Helpers.Attenuation

/-! # Recursive tuning of finite tree experiments

Depth-dependent information targets and third moment budgets suffice to build degraded experiments
at every finite depth. The construction keeps its garbling certificate through
each product and subsequent attenuation. Its information targets therefore give
lower bounds on the limiting tree experiment. Targets may vary with the depth
and pass to a limiting lower bound.
The revealing boundary only needs
the initial third-moment budget; interior budgets may shrink with the depth.
The cubic-budget construction retains the full third-moment attenuation gain;
the simpler ratio-budget construction follows as a corollary.
Constructing these budgets from
an admissible flow is a separate obligation in the capacity converse.
-/

public section

open MeasureTheory Filter Topology
open scoped BigOperators

namespace OaiCapacityCriterionState

-- @node: treeExperimentLimit_ge_of_tendsto_degraded_targets
/-- For [a channel parameter strictly between zero and one](hyp:hlam), if
[a sequence of information targets converges to a limit](hyp:ha) and [at every
sufficiently large depth there is a finite experiment degraded from the tree
experiment at v with quadratic information equal to that depth's target](hyp:h),
[the target limit is at most the limiting tree information at v](goal). -/
lemma treeExperimentLimit_ge_of_tendsto_degraded_targets {B : ℕ} (T : BoundedTree B)
    (lam : ℝ) (hlam : MainLambda lam) (v : List (Fin B))
    (a : ℕ → ℝ) (target : ℝ) (ha : Tendsto a atTop (𝓝 target))
    (h : ∀ᶠ n in atTop, ∃ F : FiniteSpinExperiment,
      FiniteLawDegrades (treeExperimentLaw T lam n v) F.law ∧ quadInfo F.law = a n) :
    target ≤ treeExperimentLimit T lam v := by
  apply le_of_tendsto_of_tendsto ha (treeExperimentLaw_quadInfo_tendsto T lam hlam v)
  filter_upwards [h] with n hn
  obtain ⟨F, hdeg, hF⟩ := hn
  exact hF ▸ hdeg.quadInfo_le


-- @node: treeExperimentLimit_ge_of_degraded_targets
/-- For [a channel parameter strictly between zero and one](hyp:hlam), if
[at every depth a finite experiment degraded from the tree experiment at v has
quadratic information a](hyp:h), [a is at most the limiting tree information
at v](goal). -/
lemma treeExperimentLimit_ge_of_degraded_targets {B : ℕ} (T : BoundedTree B)
    (lam : ℝ) (hlam : MainLambda lam) (v : List (Fin B)) (a : ℝ)
    (h : ∀ n, ∃ F : FiniteSpinExperiment,
      FiniteLawDegrades (treeExperimentLaw T lam n v) F.law ∧ quadInfo F.law = a) :
    a ≤ treeExperimentLimit T lam v := by
  exact treeExperimentLimit_ge_of_tendsto_degraded_targets T lam hlam v
    (fun _ => a) a tendsto_const_nhds (Eventually.of_forall h)


-- @node: companion_varying_depth_cubic_tuning
/-- Assuming [the companion moment-saving property](hyp:hCompanion) and [a channel
parameter strictly between zero and one](hyp:hlam), [there is a nonnegative
constant K with the following guarantee: nonnegative depth-dependent information
targets a and third-moment budgets b are realizable by finite experiments
degraded from the corresponding tree experiments, with information exactly a
and absolute third moment at most b, whenever initially a ≤ 3 and a³ ≤ 3b²,
and at each update, writing S for the λ²-weighted child targets and D for the
λ³-weighted child budgets, the next values satisfy
7D + 7KS²/2 ≤ 1 − q, a³(D + KS²/2)² ≤ b²(qS)³, and a ≤ qS](goal). -/
lemma companion_varying_depth_cubic_tuning (hCompanion : CompanionMomentSaving)
    (lam : ℝ) (hlam : MainLambda lam) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {B : ℕ} (T : BoundedTree B)
      (a b q : ℕ → List (Fin B) → ℝ),
      (∀ n v, v ∈ T.verts → 0 ≤ a n v) →
      (∀ v ∈ T.verts, a 0 v ≤ 3 ∧ a 0 v ^ 3 ≤ 3 * (b 0 v) ^ 2) →
      (∀ n v, v ∈ T.verts → 0 ≤ b n v) →
      (∀ n v, v ∈ T.verts →
        let S := ∑ w ∈ T.children v, sqParam lam * a n w
        let D := ∑ w ∈ T.children v, lam ^ 3 * b n w
        7 * D + (7 * K / 2) * S ^ 2 ≤ 1 - q (n + 1) v ∧
        a (n + 1) v ^ 3 * (D + K / 2 * S ^ 2) ^ 2 ≤
          (b (n + 1) v) ^ 2 * (q (n + 1) v * S) ^ 3 ∧ a (n + 1) v ≤ q (n + 1) v * S) →
      (∀ n v, v ∈ T.verts → ∃ F : FiniteSpinExperiment,
        FiniteLawDegrades (treeExperimentLaw T lam n v) F.law ∧
        quadInfo F.law = a n v ∧ absThird F.law ≤ b n v) := by
  classical
  obtain ⟨C, K, hK, hC, hr, hz, hchannel, hstar, hbounds⟩ :=
    companion_class_finite_product_moments hCompanion lam hlam
  refine ⟨K, hK, ?_⟩
  intro B T a b q ha haInit hb hbudget
  have hconstruct : ∀ n v, v ∈ T.verts → ∃ F : FiniteSpinExperiment,
      F.law ∈ C ∧ FiniteLawDegrades (treeExperimentLaw T lam n v) F.law ∧
        quadInfo F.law = a n v ∧ absThird F.law ≤ b n v := by
    intro n
    induction n with
    | zero =>
        intro v hv
        have ha0 := ha 0 v hv
        obtain ⟨ha3, hab⟩ := haInit v hv
        have ham : a 0 v ≤ quadInfo revealingExperiment.law := by
          rw [revealingExperiment_law, extreme_moments.1]
          exact ha3
        refine ⟨revealingExperiment.tune (a 0 v) ha0 ham,
          revealingExperiment.tune_mem C hchannel
            (revealingExperiment_law ▸ hr) _ ha0 ham, ?_,
          (revealingExperiment.tune_moments _ ha0 ham).1, ?_⟩
        · simpa only [treeExperimentLaw, revealingExperiment_law] using
            revealingExperiment.tune_degrades (a 0 v) ha0 ham
        · apply revealingExperiment.tune_absThird_le_of_bounds (a 0 v) ha0 3 3 (b 0 v)
            ha3 (by rw [revealingExperiment_law, extreme_moments.1])
            (by simpa only [revealingExperiment_law, extreme_moments.1] using
              absThird_le_quadInfo ⟨revealingExperiment.law,
                revealingExperiment.law_isPosteriorLaw⟩) (hb 0 v hv)
          nlinarith
    | succ n ih =>
        intro v hv
        let F (w : List (Fin B)) : FiniteSpinExperiment :=
          if hw : w ∈ T.verts then Classical.choose (ih w hw) else uninformativeExperiment
        have hF (w : List (Fin B)) (hw : w ∈ T.verts) :
            (F w).law ∈ C ∧ FiniteLawDegrades (treeExperimentLaw T lam n w) (F w).law ∧
              quadInfo (F w).law = a n w ∧ absThird (F w).law ≤ b n w := by
          simpa only [F, dif_pos hw] using Classical.choose_spec (ih w hw)
        have hchild (w : List (Fin B)) (hw : w ∈ T.children v) : w ∈ T.verts := by
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
          exact (Finset.mem_filter.mp hi).2
        let mus := (T.children v).toList.map (fun w => (F w).law)
        let smus := mus.map (channelStep lam)
        let S := ∑ w ∈ T.children v, sqParam lam * a n w
        let D := ∑ w ∈ T.children v, lam ^ 3 * b n w
        have hmem : ∀ mu ∈ mus, mu ∈ C := by
          intro mu hmu
          obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hmu
          exact (hF w (hchild w (Finset.mem_toList.mp hw))).1
        have hsmem : ∀ mu ∈ smus, mu ∈ C := by
          intro mu hmu
          obtain ⟨nu, hnu, rfl⟩ := List.mem_map.mp hmu
          exact hchannel lam ⟨hlam.1.le, hlam.2.le⟩ nu (hmem nu hnu)
        have hsmooth : ∀ mu ∈ smus, ∃ nu : PosteriorLaw, mu = channelStep lam nu := by
          intro mu hmu
          obtain ⟨nu, hnu, rfl⟩ := List.mem_map.mp hmu
          exact ⟨⟨nu, (hC nu (hmem nu hnu)).1⟩, rfl⟩
        have hfinite : ∀ mu ∈ smus, ∃ E : FiniteSpinExperiment, E.law = mu := by
          intro mu hmu
          obtain ⟨nu, hnu, rfl⟩ := List.mem_map.mp hmu
          obtain ⟨w, _, rfl⟩ := List.mem_map.mp hnu
          exact ⟨(F w).channel lam ⟨hlam.1.le, hlam.2.le⟩,
            (F w).law_channel lam ⟨hlam.1.le, hlam.2.le⟩⟩
        have hsum : (smus.map quadInfo).sum = S := by
          dsimp [smus, mus, S]
          simp only [List.map_map, Function.comp_def]
          rw [Finset.sum_map_toList]
          apply Finset.sum_congr rfl
          intro w hw
          have hm := congrArg Prod.fst (moments_channelStep lam ⟨hlam.1.le, hlam.2.le⟩
            (F w).law (F w).law_isPosteriorLaw)
          change quadInfo (channelStep lam (F w).law) = sqParam lam * quadInfo (F w).law at hm
          rw [hm, (hF w (hchild w hw)).2.2.1]
        have hthird : (smus.map absThird).sum ≤ D := by
          dsimp [smus, mus, D]
          simp only [List.map_map, Function.comp_def]
          rw [Finset.sum_map_toList]
          apply Finset.sum_le_sum
          intro w hw
          have hm := congrArg (fun x => x.2.2)
            (moments_channelStep lam ⟨hlam.1.le, hlam.2.le⟩
              (F w).law (F w).law_isPosteriorLaw)
          change absThird (channelStep lam (F w).law) = lam ^ 3 * absThird (F w).law at hm
          rw [hm]
          exact mul_le_mul_of_nonneg_left (hF w (hchild w hw)).2.2.2 (pow_nonneg hlam.1.le _)
        obtain ⟨E, hE⟩ := rightProductLaw_finite smus hfinite
        obtain ⟨_, hd, hm⟩ := hbounds smus hsmem hsmooth
        rw [hsum] at hd hm
        have hS : 0 ≤ S := Finset.sum_nonneg fun w hw => by
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
          exact mul_nonneg (sq_nonneg lam) (ha n _ (Finset.mem_filter.mp hi).2)
        obtain ⟨hsmall, hcubic, hatarget⟩ := hbudget n v hv
        have hlower : q (n + 1) v * S ≤ quadInfo E.law := by
          rw [hE]
          have herror := mul_le_mul_of_nonneg_left hthird (by positivity : 0 ≤ 7 * S)
          have hsmall' := mul_le_mul_of_nonneg_right hsmall hS
          nlinarith
        have ham : a (n + 1) v ≤ quadInfo E.law := hatarget.trans hlower
        have hdegrades : FiniteLawDegrades (treeExperimentLaw T lam (n + 1) v) E.law := by
          rw [hE, rightProductLaw_eq_foldr smus hfinite]
          have h := FiniteLawDegrades.foldr (T.children v).toList
            (fun w => channelStep lam (treeExperimentLaw T lam n w))
            (fun w => channelStep lam (F w).law)
            (fun w hw => (hF w (hchild w (Finset.mem_toList.mp hw))).2.1.channel
              lam ⟨hlam.1.le, hlam.2.le⟩)
          simpa only [treeExperimentLaw, smus, mus, List.map_map, Function.comp_def] using h
        refine ⟨E.tune (a (n + 1) v) (ha (n + 1) v hv) ham,
          E.tune_mem C hchannel (hE ▸ rightProductLaw_mem C hz hstar smus hsmem) _ _ ham,
          FiniteLawDegrades.tune_right E hdegrades _ (ha (n + 1) v hv) ham,
          (E.tune_moments _ (ha (n + 1) v hv) ham).1,
          E.tune_absThird_le_of_bounds (a (n + 1) v) (ha (n + 1) v hv)
            (q (n + 1) v * S) (D + K / 2 * S ^ 2) (b (n + 1) v)
            hatarget hlower (by rw [hE]; exact hd.trans (add_le_add hthird le_rfl))
            (hb (n + 1) v hv) hcubic⟩
  intro n v hv
  obtain ⟨F, _, hdeg, hquad, hthird⟩ := hconstruct n v hv
  exact ⟨F, hdeg, hquad, hthird⟩


-- @node: companion_depth_cubic_tuning
/-- Assuming [the companion moment-saving property](hyp:hCompanion) and [a channel
parameter strictly between zero and one](hyp:hlam), [there is a nonnegative
constant K such that nonnegative vertex targets a with a ≤ 3 and a³ ≤ 3b₀²
are realized at every depth by finite degraded experiments with absolute third
moment at most the nonnegative depth-dependent budget b, and bound the limiting
tree information from below, provided every update satisfies
7D + 7KS²/2 ≤ 1 − q, a³(D + KS²/2)² ≤ b²(qS)³, and a ≤ qS, where S is the
λ²-weighted sum of child targets, D is the λ³-weighted sum of child budgets,
and b and q on the right refer to the next depth](goal). -/
lemma companion_depth_cubic_tuning (hCompanion : CompanionMomentSaving)
    (lam : ℝ) (hlam : MainLambda lam) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {B : ℕ} (T : BoundedTree B)
      (a : List (Fin B) → ℝ) (b q : ℕ → List (Fin B) → ℝ),
      (∀ v ∈ T.verts, 0 ≤ a v ∧ a v ≤ 3 ∧ a v ^ 3 ≤ 3 * (b 0 v) ^ 2) →
      (∀ n v, v ∈ T.verts → 0 ≤ b n v) →
      (∀ n v, v ∈ T.verts →
        let S := ∑ w ∈ T.children v, sqParam lam * a w
        let D := ∑ w ∈ T.children v, lam ^ 3 * b n w
        7 * D + (7 * K / 2) * S ^ 2 ≤ 1 - q (n + 1) v ∧
        a v ^ 3 * (D + K / 2 * S ^ 2) ^ 2 ≤
          (b (n + 1) v) ^ 2 * (q (n + 1) v * S) ^ 3 ∧ a v ≤ q (n + 1) v * S) →
      (∀ n v, v ∈ T.verts → ∃ F : FiniteSpinExperiment,
        FiniteLawDegrades (treeExperimentLaw T lam n v) F.law ∧
        quadInfo F.law = a v ∧ absThird F.law ≤ b n v) ∧
      ∀ v ∈ T.verts, a v ≤ treeExperimentLimit T lam v := by
  obtain ⟨K, hK, htune⟩ := companion_varying_depth_cubic_tuning hCompanion lam hlam
  refine ⟨K, hK, ?_⟩
  intro B T a b q ha hb hbudget
  have hconstruct := htune T (fun _ => a) b q
    (fun _ v hv => (ha v hv).1)
    (fun v hv => (ha v hv).2) hb hbudget
  refine ⟨hconstruct, ?_⟩
  intro v hv
  apply treeExperimentLimit_ge_of_degraded_targets T lam hlam v (a v)
  intro n
  obtain ⟨F, hdeg, hquad, _⟩ := hconstruct n v hv
  exact ⟨F, hdeg, hquad⟩


-- @node: companion_depth_recursive_tuning
/-- Assuming [the companion moment-saving property](hyp:hCompanion) and [a channel
parameter strictly between zero and one](hyp:hlam), [there is a nonnegative
constant K such that nonnegative vertex targets a, initially satisfying a ≤ 3
and a ≤ 3ε₀², are realized at every depth by finite degraded experiments with
absolute third moment at most εa and bound the limiting tree information from
below, whenever ε is nonnegative and every update satisfies
7D + 7KS²/2 ≤ 1 − q, D + KS²/2 ≤ εqS, and a ≤ qS, where S sums λ² times child
targets, D sums λ³ times child values of εa, and ε and q on the right are the
next-depth values](goal). -/
lemma companion_depth_recursive_tuning (hCompanion : CompanionMomentSaving)
    (lam : ℝ) (hlam : MainLambda lam) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {B : ℕ} (T : BoundedTree B)
      (a : List (Fin B) → ℝ) (eps q : ℕ → List (Fin B) → ℝ),
      (∀ v ∈ T.verts, 0 ≤ eps 0 v ∧ 0 ≤ a v ∧ a v ≤ 3 ∧
        a v ≤ (eps 0 v) ^ 2 * 3) →
      (∀ n v, v ∈ T.verts → 0 ≤ eps n v) →
      (∀ n v, v ∈ T.verts →
        let S := ∑ w ∈ T.children v, sqParam lam * a w
        let D := ∑ w ∈ T.children v, lam ^ 3 * (eps n w * a w)
        7 * D + (7 * K / 2) * S ^ 2 ≤ 1 - q (n + 1) v ∧
        D + K / 2 * S ^ 2 ≤ eps (n + 1) v * (q (n + 1) v * S) ∧ a v ≤ q (n + 1) v * S) →
      (∀ n v, v ∈ T.verts → ∃ F : FiniteSpinExperiment,
        FiniteLawDegrades (treeExperimentLaw T lam n v) F.law ∧
        quadInfo F.law = a v ∧ absThird F.law ≤ eps n v * a v) ∧
      ∀ v ∈ T.verts, a v ≤ treeExperimentLimit T lam v := by
  classical
  obtain ⟨K, hK, htune⟩ := companion_depth_cubic_tuning hCompanion lam hlam
  refine ⟨K, hK, ?_⟩
  intro B T a eps q ha heps hbudget
  apply htune T a (fun n v => eps n v * a v) q
  · intro v hv
    obtain ⟨he, ha0, ha3, hab⟩ := ha v hv
    refine ⟨ha0, ha3, ?_⟩
    have h := mul_le_mul_of_nonneg_right hab (sq_nonneg (a v))
    nlinarith
  · intro n v hv
    exact mul_nonneg (heps n v hv) (ha v hv).2.1
  · intro n v hv
    obtain ⟨hsmall, hratio, hatarget⟩ := hbudget n v hv
    refine ⟨hsmall, ?_, hatarget⟩
    let S := ∑ w ∈ T.children v, sqParam lam * a w
    let D := ∑ w ∈ T.children v, lam ^ 3 * (eps n w * a w)
    have ha0 : 0 ≤ a v := (ha v hv).2.1
    have hL : 0 ≤ q (n + 1) v * S := ha0.trans hatarget
    have hD : 0 ≤ D + K / 2 * S ^ 2 := by
      apply add_nonneg
      · apply Finset.sum_nonneg
        intro w hw
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
        have hwv := (Finset.mem_filter.mp hi).2
        exact mul_nonneg (pow_nonneg hlam.1.le 3)
          (mul_nonneg (heps n _ hwv) (ha _ hwv).2.1)
      · positivity
    calc
      a v ^ 3 * (D + K / 2 * S ^ 2) ^ 2 ≤
          a v ^ 3 * (eps (n + 1) v * (q (n + 1) v * S)) ^ 2 :=
        mul_le_mul_of_nonneg_left
          ((sq_le_sq₀ hD (mul_nonneg (heps _ _ hv) hL)).mpr hratio)
          (pow_nonneg ha0 3)
      _ = (eps (n + 1) v * a v) ^ 2 *
          (q (n + 1) v * S) ^ 2 * a v := by ring
      _ ≤ (eps (n + 1) v * a v) ^ 2 * (q (n + 1) v * S) ^ 3 := by
        simpa only [pow_succ, mul_assoc] using
          mul_le_mul_of_nonneg_left hatarget
            (mul_nonneg (sq_nonneg (eps (n + 1) v * a v))
              (sq_nonneg (q (n + 1) v * S)))


-- @node: companion_recursive_tuning
/-- Assuming [the companion moment-saving property](hyp:hCompanion) and [a channel
parameter strictly between zero and one](hyp:hlam), [there is a nonnegative
constant K such that vertex targets a and ratios ε satisfying 0 ≤ a ≤ 3,
ε ≥ 0, and a ≤ 3ε² are realized at every depth by finite degraded experiments
with absolute third moment at most εa and bound the limiting tree information
from below, provided at each vertex 7D + 7KS²/2 ≤ 1 − q,
D + KS²/2 ≤ εqS, and a ≤ qS, where S sums λ² times child targets and D sums
λ³ times child values of εa](goal). -/
lemma companion_recursive_tuning (hCompanion : CompanionMomentSaving)
    (lam : ℝ) (hlam : MainLambda lam) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {B : ℕ} (T : BoundedTree B)
      (a eps q : List (Fin B) → ℝ),
      (∀ v ∈ T.verts, 0 ≤ eps v ∧ 0 ≤ a v ∧ a v ≤ 3 ∧ a v ≤ (eps v) ^ 2 * 3) →
      (∀ v ∈ T.verts,
        let S := ∑ w ∈ T.children v, sqParam lam * a w
        let D := ∑ w ∈ T.children v, lam ^ 3 * (eps w * a w)
        7 * D + (7 * K / 2) * S ^ 2 ≤ 1 - q v ∧
        D + K / 2 * S ^ 2 ≤ eps v * (q v * S) ∧ a v ≤ q v * S) →
      (∀ n v, v ∈ T.verts → ∃ F : FiniteSpinExperiment,
        FiniteLawDegrades (treeExperimentLaw T lam n v) F.law ∧
        quadInfo F.law = a v ∧ absThird F.law ≤ eps v * a v) ∧
      ∀ v ∈ T.verts, a v ≤ treeExperimentLimit T lam v := by
  obtain ⟨K, hK, htune⟩ := companion_depth_recursive_tuning hCompanion lam hlam
  refine ⟨K, hK, ?_⟩
  intro B T a eps q ha hbudget
  exact htune T a (fun _ => eps) (fun _ => q) ha
    (fun _ v hv => (ha v hv).1) (fun _ v hv => hbudget v hv)

end OaiCapacityCriterionState
