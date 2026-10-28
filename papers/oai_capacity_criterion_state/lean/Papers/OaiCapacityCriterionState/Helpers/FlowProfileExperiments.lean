module

public import Papers.OaiCapacityCriterionState.Helpers.RecursiveTuning
public import Papers.OaiCapacityCriterionState.Helpers.FlowPathLoss

/-! # Experiments with attenuation only at the terminal boundary

A conserved linear profile prescribes terminal noise sqrt(X / 3). Interior
vertices combine child observations without further tuning. The resulting
experiments are degraded finite broadcast observations; their local moment
bounds preserve the coefficient lambda cubed on inherited third moments.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace OaiCapacityCriterionState

-- @node: profileExperimentLaw
/-- The [profile experiment law](goal) on [a bounded tree](hyp:T), with
[channel parameter λ](hyp:lam) and [a vertex information profile X](hyp:X),
[at depth zero attenuates the fully revealing law by the square root of X
divided by three](step:1), and [at each subsequent depth combines the child
laws after passing each through the channel with parameter λ](step:2). -/
noncomputable def profileExperimentLaw {B : ℕ} (T : BoundedTree B) (lam : ℝ)
    (X : List (Fin B) → ℝ) : ℕ → List (Fin B) → Measure (Fin 4 → ℝ)
  | 0, v => channelStep (attenuationParameter (X v) 3) revealingLaw
  | n + 1, v => rightProductLaw ((T.children v).toList.map
      (fun w => channelStep lam (profileExperimentLaw T lam X n w)))

-- @node: profileExperimentLaw_boundary_moments
/-- If [the profile value at a vertex lies between zero and three](hyp:hX),
[the depth-zero profile experiment has quadratic information equal to that
value and absolute third moment at most that value times the square root of
one third of that value](goal). -/
lemma profileExperimentLaw_boundary_moments {B : ℕ} (T : BoundedTree B) (lam : ℝ)
    (X : List (Fin B) → ℝ) (v : List (Fin B)) (hX : X v ∈ Set.Icc 0 3) :
    quadInfo (profileExperimentLaw T lam X 0 v) = X v ∧
      absThird (profileExperimentLaw T lam X 0 v) ≤
        Real.sqrt (X v / 3) * X v := by
  have ht := (attenuationParameter_spec (X v) 3 hX.1 hX.2).1
  have hm := moments_channelStep _ ht revealingLaw (revealingExperiment_law ▸ revealingExperiment.law_isPosteriorLaw)
  have hq := congrArg Prod.fst hm
  have hd := congrArg (fun x => x.2.2) hm
  change quadInfo (channelStep _ revealingLaw) = _ at hq
  change absThird (channelStep _ revealingLaw) = _ at hd
  rw [extreme_moments.1] at hq
  have hrevealing : absThird revealingLaw ≤ 3 := by
    simpa only [extreme_moments.1] using
      absThird_le_quadInfo ⟨revealingLaw, (revealingExperiment_law ▸ revealingExperiment.law_isPosteriorLaw)⟩
  refine ⟨hq.trans (attenuationParameter_spec (X v) 3 hX.1 hX.2).2, ?_⟩
  change absThird (channelStep _ revealingLaw) ≤ _
  rw [hd]
  calc
    _ ≤ attenuationParameter (X v) 3 ^ 3 * 3 :=
      mul_le_mul_of_nonneg_left hrevealing (pow_nonneg ht.1 3)
    _ = attenuationParameter (X v) 3 * X v := by
      calc
        _ = attenuationParameter (X v) 3 * (attenuationParameter (X v) 3 ^ 2 * 3) := by ring
        _ = _ := by rw [(attenuationParameter_spec (X v) 3 hX.1 hX.2).2]
    _ = _ := rfl

-- @node: profileExperimentLaw_properties
/-- Suppose a class of laws [contains the fully revealing law](hyp:hr),
[contains the uninformative law](hyp:hz), [is closed under channels with
parameters between zero and one](hyp:hchannel), and [is closed under combining
two laws](hyp:hstar). If [λ lies strictly between zero and one](hyp:hlam) and
[the profile lies between zero and three at every tree vertex](hyp:hX), then
[at every depth and tree vertex the profile experiment belongs to the class,
is the law of a finite spin experiment, and is a degradation of the
corresponding broadcast tree experiment](goal). -/
lemma profileExperimentLaw_properties
    (C : Set (Measure (Fin 4 → ℝ)))
    (hr : revealingLaw ∈ C) (hz : uninformativeLaw ∈ C)
    (hchannel : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ mu ∈ C, channelStep t mu ∈ C)
    (hstar : ∀ mu ∈ C, ∀ nu ∈ C, starLaw mu nu ∈ C)
    {B : ℕ} (T : BoundedTree B) (lam : ℝ) (hlam : MainLambda lam)
    (X : List (Fin B) → ℝ) (hX : ∀ v ∈ T.verts, X v ∈ Set.Icc 0 3) :
    ∀ n v, v ∈ T.verts →
      profileExperimentLaw T lam X n v ∈ C ∧
      (∃ E : FiniteSpinExperiment, E.law = profileExperimentLaw T lam X n v) ∧
      FiniteLawDegrades (treeExperimentLaw T lam n v) (profileExperimentLaw T lam X n v) := by
  classical
  intro n
  induction n with
  | zero =>
      intro v hv
      have ht := (attenuationParameter_spec (X v) 3 (hX v hv).1 (hX v hv).2).1
      refine ⟨hchannel _ ht _ hr, ?_, ?_⟩
      · exact ⟨revealingExperiment.channel _ ht,
          (revealingExperiment.law_channel _ ht).trans (by rw [revealingExperiment_law]; rfl)⟩
      · simpa only [treeExperimentLaw, profileExperimentLaw, revealingExperiment_law] using
          FiniteLawDegrades.attenuate revealingExperiment _ ht
  | succ n ih =>
      intro v hv
      have hchild (w : List (Fin B)) (hw : w ∈ T.children v) : w ∈ T.verts := by
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
        exact (Finset.mem_filter.mp ha).2
      let mus := (T.children v).toList.map
        (fun w => channelStep lam (profileExperimentLaw T lam X n w))
      have hmem : ∀ mu ∈ mus, mu ∈ C := by
        intro mu hmu
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hmu
        exact hchannel lam ⟨hlam.1.le, hlam.2.le⟩ _
          (ih w (hchild w (Finset.mem_toList.mp hw))).1
      have hfinite : ∀ mu ∈ mus, ∃ E : FiniteSpinExperiment, E.law = mu := by
        intro mu hmu
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hmu
        obtain ⟨E, hE⟩ := (ih w (hchild w (Finset.mem_toList.mp hw))).2.1
        exact ⟨E.channel lam ⟨hlam.1.le, hlam.2.le⟩,
          (E.law_channel lam ⟨hlam.1.le, hlam.2.le⟩).trans (by rw [hE])⟩
      refine ⟨rightProductLaw_mem C hz hstar mus hmem, rightProductLaw_finite mus hfinite, ?_⟩
      change FiniteLawDegrades _ (rightProductLaw mus)
      rw [rightProductLaw_eq_foldr mus hfinite]
      simpa only [treeExperimentLaw, mus, List.map_map, Function.comp_def] using
        FiniteLawDegrades.foldr (T.children v).toList
          (fun w => channelStep lam (treeExperimentLaw T lam n w))
          (fun w => channelStep lam (profileExperimentLaw T lam X n w))
          (fun w hw => (ih w (hchild w (Finset.mem_toList.mp hw))).2.2.channel
            lam ⟨hlam.1.le, hlam.2.le⟩)

-- @node: companion_profile_moment_bounds
/-- Assuming [there exists a class of symmetric posterior laws containing
the revealing and uninformative laws, closed under channels and independent
combination, and satisfying the companion quadratic-information saving
inequality](hyp:hCompanion) and
[a channel parameter λ strictly between zero and one](hyp:hlam), [there is a
nonnegative constant K such that every profile between zero and three whose
λ-squared-weighted child values sum to its parent value has the following
bounds: its experiments are finite degradations of the broadcast experiments
with quadratic information at most the profile; at each next step the
absolute third moment is at most the λ-cubed-weighted child third moments
plus K times half the squared profile, and the loss from the λ-squared-weighted
child quadratic information is nonnegative and at most seven times the
profile times that same third-moment bound](goal). -/
lemma companion_profile_moment_bounds (hCompanion : CompanionMomentSaving)
    (lam : ℝ) (hlam : MainLambda lam) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {B : ℕ} (T : BoundedTree B)
      (X : List (Fin B) → ℝ),
      (∀ v ∈ T.verts, X v ∈ Set.Icc 0 3) →
      (∀ v ∈ T.verts, ∑ w ∈ T.children v, sqParam lam * X w = X v) →
      (∀ n v, v ∈ T.verts →
        (∃ E : FiniteSpinExperiment, E.law = profileExperimentLaw T lam X n v) ∧
        FiniteLawDegrades (treeExperimentLaw T lam n v) (profileExperimentLaw T lam X n v) ∧
        quadInfo (profileExperimentLaw T lam X n v) ≤ X v) ∧
      ∀ n v, v ∈ T.verts →
        let D := ∑ w ∈ T.children v, lam ^ 3 * absThird (profileExperimentLaw T lam X n w)
        let S := ∑ w ∈ T.children v, sqParam lam * quadInfo (profileExperimentLaw T lam X n w)
        absThird (profileExperimentLaw T lam X (n + 1) v) ≤ D + K / 2 * X v ^ 2 ∧
        0 ≤ S - quadInfo (profileExperimentLaw T lam X (n + 1) v) ∧
        S - quadInfo (profileExperimentLaw T lam X (n + 1) v) ≤
          7 * X v * (D + K / 2 * X v ^ 2) := by
  classical
  obtain ⟨C, K, hK, hC, hr, hz, hchannel, hstar, hbounds⟩ :=
    companion_class_finite_product_moments hCompanion lam hlam
  refine ⟨K, hK, ?_⟩
  intro B T X hX hconserve
  have hprops := profileExperimentLaw_properties C hr hz hchannel hstar T lam hlam X hX
  have hchild (v w : List (Fin B)) (hw : w ∈ T.children v) : w ∈ T.verts := by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
    exact (Finset.mem_filter.mp ha).2
  have hstep (n : ℕ) (v : List (Fin B)) :
      let D := ∑ w ∈ T.children v, lam ^ 3 * absThird (profileExperimentLaw T lam X n w)
      let S := ∑ w ∈ T.children v, sqParam lam * quadInfo (profileExperimentLaw T lam X n w)
      quadInfo (profileExperimentLaw T lam X (n + 1) v) ≤ S ∧
      absThird (profileExperimentLaw T lam X (n + 1) v) ≤ D + K / 2 * S ^ 2 ∧
      S - 7 * S * D - (7 * K / 2) * S ^ 3 ≤
        quadInfo (profileExperimentLaw T lam X (n + 1) v) := by
    let mus := (T.children v).toList.map
      (fun w => channelStep lam (profileExperimentLaw T lam X n w))
    have hmem : ∀ mu ∈ mus, mu ∈ C := by
      intro mu hmu
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hmu
      exact hchannel lam ⟨hlam.1.le, hlam.2.le⟩ _
        (hprops n w (hchild v w (Finset.mem_toList.mp hw))).1
    have hsmooth : ∀ mu ∈ mus, ∃ nu : PosteriorLaw, mu = channelStep lam nu := by
      intro mu hmu
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hmu
      exact ⟨⟨_, (hC _ (hprops n w (hchild v w (Finset.mem_toList.mp hw))).1).1⟩, rfl⟩
    have hsum : (mus.map quadInfo).sum =
        ∑ w ∈ T.children v, sqParam lam * quadInfo (profileExperimentLaw T lam X n w) := by
      dsimp only [mus]
      rw [List.map_map, Finset.sum_map_toList]
      apply Finset.sum_congr rfl
      intro w hw
      exact congrArg Prod.fst (moments_channelStep lam ⟨hlam.1.le, hlam.2.le⟩ _
        (hC _ (hprops n w (hchild v w hw)).1).1)
    have hthird : (mus.map absThird).sum =
        ∑ w ∈ T.children v, lam ^ 3 * absThird (profileExperimentLaw T lam X n w) := by
      dsimp only [mus]
      rw [List.map_map, Finset.sum_map_toList]
      apply Finset.sum_congr rfl
      intro w hw
      exact congrArg (fun x => x.2.2) (moments_channelStep lam ⟨hlam.1.le, hlam.2.le⟩ _
        (hC _ (hprops n w (hchild v w hw)).1).1)
    simpa only [hsum, hthird, profileExperimentLaw] using hbounds mus hmem hsmooth
  have hm : ∀ n v, v ∈ T.verts → quadInfo (profileExperimentLaw T lam X n v) ≤ X v := by
    intro n
    induction n with
    | zero => intro v hv; exact (profileExperimentLaw_boundary_moments T lam X v (hX v hv)).1.le
    | succ n ih =>
        intro v hv
        apply (hstep n v).1.trans
        rw [← hconserve v hv]
        exact Finset.sum_le_sum fun w hw => mul_le_mul_of_nonneg_left
          (ih w (hchild v w hw)) (sq_nonneg lam)
  refine ⟨fun n v hv => ⟨(hprops n v hv).2.1, (hprops n v hv).2.2, hm n v hv⟩, ?_⟩
  intro n v hv D S
  have hSX : S ≤ X v := by
    dsimp only [S]
    rw [← hconserve v hv]
    exact Finset.sum_le_sum fun w hw => mul_le_mul_of_nonneg_left
      (hm n w (hchild v w hw)) (sq_nonneg lam)
  have hS : 0 ≤ S := Finset.sum_nonneg fun w hw => mul_nonneg (sq_nonneg lam)
    (quadInfo_mem_Icc ⟨_, (hC _ (hprops n w (hchild v w hw)).1).1⟩).1
  have hD : 0 ≤ D := Finset.sum_nonneg fun w _ =>
    mul_nonneg (pow_nonneg hlam.1.le 3) (abs_nonneg _)
  obtain ⟨hu, hd, hl⟩ := hstep n v
  have hsq : S ^ 2 ≤ X v ^ 2 := (sq_le_sq₀ hS (hX v hv).1).mpr hSX
  have hthird : absThird (profileExperimentLaw T lam X (n + 1) v) ≤ D + K / 2 * X v ^ 2 :=
    hd.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ K / 2)))
  refine ⟨hthird, sub_nonneg.mpr hu, ?_⟩
  have herror := mul_le_mul hSX
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ K / 2)))
    (by positivity : 0 ≤ D + K / 2 * S ^ 2) (hX v hv).1
  nlinarith

-- @node: scaled_normalizedFlow_profile
/-- If [λ lies strictly between zero and one](hyp:hlam), [the edge weights
form a flow](hyp:htheta), [every tree ray has path potential at most
one](hyp:hpotential), [the scale ε is nonnegative](hyp:heps), and
[ε times the sum of one and the total flow mass is at most three](hyp:hsmall), then
[the ε-scaled normalized flow lies between zero and three at every tree
vertex, and its λ-squared-weighted child values sum to its parent value](goal). -/
lemma scaled_normalizedFlow_profile {B : ℕ} (T : BoundedTree B) (lam : ℝ)
    (hlam : MainLambda lam) (theta : List (Fin B) → ℝ) (htheta : IsFlow T theta)
    (hpotential : ∀ xi ∈ T.rays, pathPotential lam theta xi ≤ 1)
    (eps : ℝ) (heps : 0 ≤ eps) (hsmall : eps * (1 + flowMass T theta) ≤ 3) :
    (∀ v ∈ T.verts, eps * normalizedFlow T lam theta v ∈ Set.Icc 0 3) ∧
    (∀ v ∈ T.verts, ∑ w ∈ T.children v,
      sqParam lam * (eps * normalizedFlow T lam theta w) =
        eps * normalizedFlow T lam theta v) := by
  classical
  have hm := flowMass_nonneg T theta htheta
  refine ⟨?_, ?_⟩
  · intro v hv
    refine ⟨mul_nonneg heps (normalizedFlow_nonneg T lam theta htheta v), ?_⟩
    have hb : normalizedFlow T lam theta v ≤ 1 + flowMass T theta := by
      by_cases hne : v = []
      · subst v; simp only [normalizedFlow, if_true]; linarith
      · rw [normalizedFlow, if_neg hne]
        have hden : 0 < sqParam lam ^ v.length := pow_pos (sqParam_mem_Ioo lam hlam).1 _
        exact ((div_le_one hden).mpr
          (admissible_flow_edge_bound T lam hlam theta htheta hpotential v hv hne)).trans
            (by linarith)
    exact (mul_le_mul_of_nonneg_left hb heps).trans hsmall
  · intro v hv
    calc
      _ = eps * ∑ w ∈ T.children v, sqParam lam * normalizedEdgeFlow lam theta w := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w hw
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hw
        simp only [normalizedFlow, List.cons_ne_nil, if_false]
        ring
      _ = _ := by rw [normalizedFlow_children T lam hlam theta htheta v hv]

-- @node: BoundedTree.weighted_level_telescope
/-- For any depth-dependent vertex values and real weight r, [the root value
equals r to the terminal depth times the sum of terminal values, minus the
sum over earlier levels of r to the level times the total difference between
the r-weighted child values and their parent values](goal). -/
lemma BoundedTree.weighted_level_telescope {B : ℕ} (T : BoundedTree B)
    (r : ℝ) (m : ℕ → List (Fin B) → ℝ) (N : ℕ) :
    m 0 [] = r ^ N * (∑ v ∈ T.level N, m N v) -
      ∑ i ∈ Finset.range N, r ^ i * ∑ v ∈ T.level i,
        ((∑ w ∈ T.children v, r * m (i + 1) w) - m i v) := by
  classical
  let f (i : ℕ) := r ^ i * ∑ v ∈ T.level i, m i v
  have hstep (i : ℕ) : r ^ i * (∑ v ∈ T.level i,
      ((∑ w ∈ T.children v, r * m (i + 1) w) - m i v)) = f (i + 1) - f i := by
    dsimp only [f]
    rw [T.sum_level_succ, Finset.sum_sub_distrib, mul_sub, pow_succ]
    simp only [← Finset.mul_sum]
    ring
  simp_rw [hstep]
  rw [Finset.sum_range_sub]
  simp [f, BoundedTree.level]

-- @node: BoundedTree.conserved_profile_level_mass
/-- If [the r-weighted child profile values sum to the parent profile at every
tree vertex](hyp:hconserve), then [r to any depth times the sum of profile
values at that level equals the root profile value](goal). -/
lemma BoundedTree.conserved_profile_level_mass {B : ℕ} (T : BoundedTree B)
    (r : ℝ) (X : List (Fin B) → ℝ)
    (hconserve : ∀ v ∈ T.verts, ∑ w ∈ T.children v, r * X w = X v) (N : ℕ) :
    r ^ N * (∑ v ∈ T.level N, X v) = X [] := by
  classical
  induction N with
  | zero => simp [BoundedTree.level]
  | succ N ih =>
      rw [T.sum_level_succ, pow_succ, mul_assoc, Finset.mul_sum]
      have heq : (∑ v ∈ T.level N, r * ∑ w ∈ T.children v, X w) =
          ∑ v ∈ T.level N, X v := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [Finset.mul_sum]
        exact hconserve v ((T.mem_level_iff v N).mp hv).1
      rw [heq, ih]

-- @node: profileExperimentLaw_deficit_telescope
/-- If [the profile lies between zero and three at every tree vertex](hyp:hX)
and [the λ-squared-weighted child profile values sum to the parent
value](hyp:hconserve), then [the quadratic information of the root profile
experiment at any depth equals the root profile minus the sum over earlier
levels of the local information deficits, weighted by λ squared to the level;
each deficit is the λ-squared-weighted child information minus the parent
information at the corresponding remaining depths](goal). -/
lemma profileExperimentLaw_deficit_telescope {B : ℕ} (T : BoundedTree B)
    (lam : ℝ) (X : List (Fin B) → ℝ)
    (hX : ∀ v ∈ T.verts, X v ∈ Set.Icc 0 3)
    (hconserve : ∀ v ∈ T.verts, ∑ w ∈ T.children v, sqParam lam * X w = X v)
    (N : ℕ) :
    quadInfo (profileExperimentLaw T lam X N []) = X [] -
      ∑ i ∈ Finset.range N, sqParam lam ^ i * ∑ v ∈ T.level i,
        ((∑ w ∈ T.children v, sqParam lam *
          quadInfo (profileExperimentLaw T lam X (N - (i + 1)) w)) -
            quadInfo (profileExperimentLaw T lam X (N - i) v)) := by
  classical
  have ht := T.weighted_level_telescope (sqParam lam)
    (fun i v => quadInfo (profileExperimentLaw T lam X (N - i) v)) N
  have hboundary : (∑ v ∈ T.level N,
      quadInfo (profileExperimentLaw T lam X (N - N) v)) = ∑ v ∈ T.level N, X v := by
    rw [Nat.sub_self]
    apply Finset.sum_congr rfl
    intro v hv
    exact profileExperimentLaw_boundary_moments T lam X v
      (hX v ((T.mem_level_iff v N).mp hv).1) |>.1
  rw [hboundary, T.conserved_profile_level_mass (sqParam lam) X hconserve N] at ht
  simpa only [Nat.sub_zero] using ht

-- @node: BoundedTree.weightedDescendantSum
/-- On [a bounded tree](hyp:T), the [weighted descendant sum](goal) with
[per-generation multiplier c](hyp:c) and [vertex values f](hyp:f)
[returns the value at the starting vertex at depth zero](step:1) and
[at a positive depth multiplies the sum of the child descendant sums at one
less depth by c](step:2). -/
noncomputable def BoundedTree.weightedDescendantSum {B : ℕ} (T : BoundedTree B)
    (c : ℝ) (f : List (Fin B) → ℝ) : ℕ → List (Fin B) → ℝ
  | 0, v => f v
  | n + 1, v => c * ∑ w ∈ T.children v, T.weightedDescendantSum c f n w

-- @node: BoundedTree.weightedDescendantSum_unroll
/-- For [nonnegative propagation weight c](hyp:hc) and [depth-dependent vertex
values h](hyp:h), suppose [each next value is at most c times the sum of the
child values at the preceding depth plus a vertex error](hyp:hstep). Then
[at every depth and tree vertex, h is at most the weighted descendant sum of
its initial values plus the sum of weighted descendant errors over all
smaller depths](goal). -/
lemma BoundedTree.weightedDescendantSum_unroll {B : ℕ} (T : BoundedTree B)
    (c : ℝ) (hc : 0 ≤ c) (h : ℕ → List (Fin B) → ℝ)
    (e : List (Fin B) → ℝ)
    (hstep : ∀ n v, v ∈ T.verts →
      h (n + 1) v ≤ c * (∑ w ∈ T.children v, h n w) + e v) :
    ∀ n v, v ∈ T.verts → h n v ≤
      T.weightedDescendantSum c (h 0) n v +
        ∑ k ∈ Finset.range n, T.weightedDescendantSum c e k v := by
  classical
  intro n
  induction n with
  | zero => intro v hv; simp only [weightedDescendantSum, Finset.range_zero, Finset.sum_empty, add_zero, le_refl]
  | succ n ih =>
      intro v hv
      have hchild (w : List (Fin B)) (hw : w ∈ T.children v) : w ∈ T.verts := by
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
        exact (Finset.mem_filter.mp ha).2
      have hb := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun w hw => ih w (hchild w hw))) hc
      have hsum : (∑ k ∈ Finset.range (n + 1), T.weightedDescendantSum c e k v) =
          e v + c * ∑ w ∈ T.children v,
            ∑ k ∈ Finset.range n, T.weightedDescendantSum c e k w := by
        rw [Finset.sum_range_succ']
        simp only [weightedDescendantSum, ← Finset.mul_sum]
        rw [Finset.sum_comm]
        ring
      rw [hsum, weightedDescendantSum]
      rw [Finset.sum_add_distrib, mul_add] at hb
      exact (hstep n v hv).trans (by linarith)

-- @node: companion_profile_third_unroll
/-- Assuming [there exists a class of symmetric posterior laws containing
the revealing and uninformative laws, closed under channels and independent
combination, and satisfying the companion quadratic-information saving
inequality](hyp:hCompanion) and
[a channel parameter λ strictly between zero and one](hyp:hlam), [there is a
nonnegative constant K such that, for every profile between zero and three
conserved by λ-squared-weighted child summation, the absolute third moment of
each profile experiment is at most the λ-cubed-weighted descendant sum of its
depth-zero third moments plus the sum, over smaller descendant depths, of
the λ-cubed-weighted descendant sums of K times half the squared profile](goal). -/
lemma companion_profile_third_unroll (hCompanion : CompanionMomentSaving)
    (lam : ℝ) (hlam : MainLambda lam) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {B : ℕ} (T : BoundedTree B)
      (X : List (Fin B) → ℝ),
      (∀ v ∈ T.verts, X v ∈ Set.Icc 0 3) →
      (∀ v ∈ T.verts, ∑ w ∈ T.children v, sqParam lam * X w = X v) →
      ∀ n v, v ∈ T.verts →
        absThird (profileExperimentLaw T lam X n v) ≤
          T.weightedDescendantSum (lam ^ 3)
            (fun w => absThird (profileExperimentLaw T lam X 0 w)) n v +
          ∑ k ∈ Finset.range n,
            T.weightedDescendantSum (lam ^ 3) (fun w => K / 2 * X w ^ 2) k v := by
  obtain ⟨K, hK, hbounds⟩ := companion_profile_moment_bounds hCompanion lam hlam
  refine ⟨K, hK, ?_⟩
  intro B T X hX hconserve
  apply T.weightedDescendantSum_unroll (lam ^ 3) (pow_nonneg hlam.1.le 3)
  intro n v hv
  simpa only [Finset.mul_sum] using (hbounds T X hX hconserve).2 n v hv |>.1

end OaiCapacityCriterionState
