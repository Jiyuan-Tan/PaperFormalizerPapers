module

public import Papers.OaiCapacityCriterionState.Helpers.Subtrees
public import Papers.OaiCapacityCriterionState.Helpers.DependentProducts

/-! # Companion bounds for the broadcast experiment

The dependent product theorem applies to the child-subtree factorization of the
broadcast likelihood. Consequently every finite broadcast posterior stays in
the companion class, with the corresponding information bound at each branch.
-/

public section

open Filter Topology
open MeasureTheory
open scoped BigOperators

namespace OaiCapacityCriterionState

-- @node: broadcastPosteriorLaw_companion_step
/-- Suppose a class of laws [contains the uninformative law](hyp:hzero), [is closed
under channel updates with parameters between zero and one](hyp:hchannel), [is
closed under combining independent experiments](hyp:hstar), and [has cubic
transformed quadratic information subadditive under that combination](hyp:hsave).
If [λ lies strictly between zero and one](hyp:hlam) and [every child subtree's
depth-n broadcast posterior law belongs to the class](hyp:hmem), then [the
depth-(n + 1) broadcast posterior law also belongs to the class, and its cubic
transformed quadratic information is at most the sum of that quantity for the
channel-updated child laws](goal). -/
lemma broadcastPosteriorLaw_companion_step
    (C : Set (Measure (Fin 4 → ℝ)))
    (hzero : uninformativeLaw ∈ C)
    (hchannel : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ mu ∈ C, channelStep t mu ∈ C)
    (hstar : ∀ mu ∈ C, ∀ nu ∈ C, starLaw mu nu ∈ C)
    (hsave : ∀ mu ∈ C, ∀ nu ∈ C,
      cubicInfoTransform (quadInfo (starLaw mu nu)) ≤
        cubicInfoTransform (quadInfo mu) + cubicInfoTransform (quadInfo nu))
    {B : ℕ} (T : BoundedTree B) (lam : ℝ) (hlam : MainLambda lam) (n : ℕ)
    (hmem : ∀ a : T.rootChildren,
      broadcastPosteriorLaw (T.subtree [a.val] (T.rootChild_mem a)) lam n ∈ C) :
    broadcastPosteriorLaw T lam (n + 1) ∈ C ∧
      cubicInfoTransform (quadInfo (broadcastPosteriorLaw T lam (n + 1))) ≤
        ∑ a : T.rootChildren, cubicInfoTransform (quadInfo (channelStep lam
          (broadcastPosteriorLaw (T.subtree [a.val] (T.rootChild_mem a)) lam n))) := by
  classical
  have ht : IsChannelParameter lam := ⟨hlam.1.le, hlam.2.le⟩
  have hlaw (a : T.rootChildren) :
      experimentLaw (channelLikelihood lam
        (broadcastLikelihood (T.subtree [a.val] (T.rootChild_mem a)) lam n)) =
      channelStep lam
        (broadcastPosteriorLaw (T.subtree [a.val] (T.rootChild_mem a)) lam n) :=
    experimentLaw_channel lam ht _ (broadcastLikelihood_nonneg _ lam ht n)
      (broadcastLikelihood_sum _ lam n)
  have h := companion_dependent_product_bound C hzero hstar hsave
    (fun a : T.rootChildren => (T.subtree [a.val] (T.rootChild_mem a)).level n → Fin 4)
    (fun a : T.rootChildren => channelLikelihood lam
      (broadcastLikelihood (T.subtree [a.val] (T.rootChild_mem a)) lam n))
    (fun a => channelLikelihood_nonneg lam ht _ (broadcastLikelihood_nonneg _ lam ht n))
    (fun a => channelLikelihood_sum lam _ (broadcastLikelihood_sum _ lam n))
    (fun a => (hlaw a).symm ▸ hchannel lam ht _ (hmem a))
  rw [← broadcastPosteriorLaw_root_branches] at h
  simpa only [hlaw] using h

-- @node: broadcastPosteriorLaw_mem_companion
/-- Suppose a class of laws [contains the fully revealing law](hyp:hrevealing) and
[the uninformative law](hyp:hzero), [is closed under channel updates with parameters
between zero and one](hyp:hchannel), [is closed under combining independent
experiments](hyp:hstar), and [has cubic transformed quadratic information
subadditive under that combination](hyp:hsave). If [the channel parameter lies
strictly between zero and one](hyp:hlam), then [every finite-depth broadcast
posterior law on a bounded tree belongs to the class](goal). -/
lemma broadcastPosteriorLaw_mem_companion
    (C : Set (Measure (Fin 4 → ℝ)))
    (hrevealing : revealingLaw ∈ C) (hzero : uninformativeLaw ∈ C)
    (hchannel : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ mu ∈ C, channelStep t mu ∈ C)
    (hstar : ∀ mu ∈ C, ∀ nu ∈ C, starLaw mu nu ∈ C)
    (hsave : ∀ mu ∈ C, ∀ nu ∈ C,
      cubicInfoTransform (quadInfo (starLaw mu nu)) ≤
        cubicInfoTransform (quadInfo mu) + cubicInfoTransform (quadInfo nu))
    {B : ℕ} (T : BoundedTree B) (lam : ℝ) (hlam : MainLambda lam) (n : ℕ) :
    broadcastPosteriorLaw T lam n ∈ C := by
  induction n generalizing T with
  | zero => rw [broadcastPosteriorLaw_zero]; exact hrevealing
  | succ n ih =>
      exact (broadcastPosteriorLaw_companion_step C hzero hchannel hstar hsave
        T lam hlam n (fun a => ih _)).1

-- @node: broadcastPosteriorLaw_channel_label_bound
/-- Suppose a class of laws [contains the fully revealing law](hyp:hrevealing) and
[the uninformative law](hyp:hzero), [is closed under channel updates with parameters
between zero and one](hyp:hchannel), [is closed under combining independent
experiments](hyp:hstar), and [has cubic transformed quadratic information
subadditive under that combination](hyp:hsave). If [λ lies strictly between zero
and one](hyp:hlam), then [the scaled cubic information label of the depth-(n + 1)
broadcast posterior law is at most the sum over root children of λ² times each
child's depth-n label divided by the square root of one plus its squared
label](goal).

Here the label of a law with quadratic information x is
((1 − λ⁴) / 1000)(x + x³ / 3000). -/
lemma broadcastPosteriorLaw_channel_label_bound
    (C : Set (Measure (Fin 4 → ℝ)))
    (hrevealing : revealingLaw ∈ C) (hzero : uninformativeLaw ∈ C)
    (hchannel : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ mu ∈ C, channelStep t mu ∈ C)
    (hstar : ∀ mu ∈ C, ∀ nu ∈ C, starLaw mu nu ∈ C)
    (hsave : ∀ mu ∈ C, ∀ nu ∈ C,
      cubicInfoTransform (quadInfo (starLaw mu nu)) ≤
        cubicInfoTransform (quadInfo mu) + cubicInfoTransform (quadInfo nu))
    {B : ℕ} (T : BoundedTree B) (lam : ℝ) (hlam : MainLambda lam) (n : ℕ) :
    cubicInfoScale (sqParam lam) *
        cubicInfoTransform (quadInfo (broadcastPosteriorLaw T lam (n + 1))) ≤
      ∑ a : T.rootChildren,
        sqParam lam * (cubicInfoScale (sqParam lam) * cubicInfoTransform (quadInfo
          (broadcastPosteriorLaw (T.subtree [a.val] (T.rootChild_mem a)) lam n))) /
        Real.sqrt (1 + (cubicInfoScale (sqParam lam) * cubicInfoTransform (quadInfo
          (broadcastPosteriorLaw (T.subtree [a.val] (T.rootChild_mem a)) lam n))) ^ 2) := by
  classical
  have hr := sqParam_mem_Ioo lam hlam
  have hk := (cubicInfoScale_pos hr).le
  have ht : IsChannelParameter lam := ⟨hlam.1.le, hlam.2.le⟩
  have hb := (broadcastPosteriorLaw_companion_step C hzero hchannel hstar hsave
    T lam hlam n (fun a => broadcastPosteriorLaw_mem_companion C hrevealing hzero
      hchannel hstar hsave _ lam hlam n)).2
  calc
    _ ≤ cubicInfoScale (sqParam lam) *
        ∑ a : T.rootChildren, cubicInfoTransform (quadInfo (channelStep lam
          (broadcastPosteriorLaw (T.subtree [a.val] (T.rootChild_mem a)) lam n))) :=
      mul_le_mul_of_nonneg_left hb hk
    _ = ∑ a : T.rootChildren, cubicInfoScale (sqParam lam) *
        cubicInfoTransform (quadInfo (channelStep lam
          (broadcastPosteriorLaw (T.subtree [a.val] (T.rootChild_mem a)) lam n))) :=
      Finset.mul_sum _ _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro a _
      let mu := broadcastPosteriorLaw (T.subtree [a.val] (T.rootChild_mem a)) lam n
      have hmu := broadcastPosteriorLaw_isPosteriorLaw
        (T.subtree [a.val] (T.rootChild_mem a)) lam ht n
      have hscale := congrArg Prod.fst (moments_channelStep lam ht mu hmu)
      change quadInfo (channelStep lam mu) = sqParam lam * quadInfo mu at hscale
      change cubicInfoScale (sqParam lam) * cubicInfoTransform (quadInfo (channelStep lam mu)) ≤ _
      rw [hscale]
      have h := mul_le_mul_of_nonneg_left
        (cubicInfoTransform_channel_contraction hr (quadInfo_mem_Icc ⟨mu, hmu⟩)) hk
      convert h using 1 <;> first | ring | rfl

-- @node: broadcast_limit_label_bound
/-- Assuming [the companion moment-saving property](hyp:hCompanion) and [a channel
parameter λ strictly between zero and one](hyp:hlam), [the scaled cubic label of
the tree's limiting quadratic information is at most the sum over root children
of λ² times the corresponding child-subtree label divided by the square root of
one plus its squared label](goal).

The label associated with limiting quadratic information x is
((1 − λ⁴) / 1000)(x + x³ / 3000). -/
lemma broadcast_limit_label_bound (hCompanion : CompanionMomentSaving)
    {B : ℕ} (T : BoundedTree B) (lam : ℝ) (hlam : MainLambda lam) :
    cubicInfoScale (sqParam lam) * cubicInfoTransform (limitQuadInfo T lam) ≤
      ∑ a : T.rootChildren,
        sqParam lam * (cubicInfoScale (sqParam lam) * cubicInfoTransform
          (limitQuadInfo (T.subtree [a.val] (T.rootChild_mem a)) lam)) /
        Real.sqrt (1 + (cubicInfoScale (sqParam lam) * cubicInfoTransform
          (limitQuadInfo (T.subtree [a.val] (T.rootChild_mem a)) lam)) ^ 2) := by
  classical
  obtain ⟨C, _, hrevealing, hzero, hchannel, hstar, hsave⟩ :=
    companion_class_cubic_saving hCompanion
  have hsave' : ∀ mu ∈ C, ∀ nu ∈ C,
      cubicInfoTransform (quadInfo (starLaw mu nu)) ≤
        cubicInfoTransform (quadInfo mu) + cubicInfoTransform (quadInfo nu) :=
    fun mu hmu nu hnu => (hsave mu hmu nu hnu).2
  have hcont : Continuous (fun x : ℝ =>
      cubicInfoScale (sqParam lam) * cubicInfoTransform x) := by
    unfold cubicInfoTransform
    fun_prop
  have hkernel : Continuous (fun z : ℝ => sqParam lam * z / Real.sqrt (1 + z ^ 2)) := by
    fun_prop (disch := intro z; exact ne_of_gt (Real.sqrt_pos.2 (by positivity)))
  have hleft := hcont.continuousAt.tendsto.comp
    ((quadInfo_broadcastPosteriorLaw_tendsto T lam hlam).comp (tendsto_add_atTop_nat 1))
  have hright : Tendsto
      (fun n => ∑ a : T.rootChildren,
        sqParam lam * (cubicInfoScale (sqParam lam) * cubicInfoTransform (quadInfo
          (broadcastPosteriorLaw (T.subtree [a.val] (T.rootChild_mem a)) lam n))) /
        Real.sqrt (1 + (cubicInfoScale (sqParam lam) * cubicInfoTransform (quadInfo
          (broadcastPosteriorLaw (T.subtree [a.val] (T.rootChild_mem a)) lam n))) ^ 2))
      atTop (𝓝 (∑ a : T.rootChildren,
        sqParam lam * (cubicInfoScale (sqParam lam) * cubicInfoTransform
          (limitQuadInfo (T.subtree [a.val] (T.rootChild_mem a)) lam)) /
        Real.sqrt (1 + (cubicInfoScale (sqParam lam) * cubicInfoTransform
          (limitQuadInfo (T.subtree [a.val] (T.rootChild_mem a)) lam)) ^ 2))) := by
    apply tendsto_finsetSum
    intro a _
    exact hkernel.continuousAt.tendsto.comp (hcont.continuousAt.tendsto.comp
      (quadInfo_broadcastPosteriorLaw_tendsto _ lam hlam))
  exact le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall
    (broadcastPosteriorLaw_channel_label_bound C hrevealing hzero hchannel hstar hsave'
      T lam hlam))

-- @node: broadcast_limit_flow_labels
/-- Assuming [the companion moment-saving property](hyp:hCompanion) and [a channel
parameter λ strictly between zero and one](hyp:hlam), [there exist real labels on
vertex addresses that are nonnegative on the tree, with each vertex's label at
most the sum over its children of λ² times the child label divided by the square
root of one plus its square, and with root label equal to the scaled cubic
transform of the tree's limiting quadratic information](goal).

The scaled cubic transform of x is ((1 − λ⁴) / 1000)(x + x³ / 3000). -/
lemma broadcast_limit_flow_labels (hCompanion : CompanionMomentSaving)
    {B : ℕ} (T : BoundedTree B) (lam : ℝ) (hlam : MainLambda lam) :
    ∃ z : List (Fin B) → ℝ, FlowLabelRecursion T lam z ∧
      z [] = cubicInfoScale (sqParam lam) * cubicInfoTransform (limitQuadInfo T lam) := by
  classical
  let z : List (Fin B) → ℝ := fun v => if hv : v ∈ T.verts then
    cubicInfoScale (sqParam lam) * cubicInfoTransform (limitQuadInfo (T.subtree v hv) lam)
    else 0
  refine ⟨z, ?_, ?_⟩
  · intro v hv
    let S := T.subtree v hv
    have hzv : z v = cubicInfoScale (sqParam lam) *
        cubicInfoTransform (limitQuadInfo S lam) := dif_pos hv
    rw [hzv]
    refine ⟨mul_nonneg (cubicInfoScale_pos (sqParam_mem_Ioo lam hlam)).le
      (cubicInfoTransform_nonneg (limitQuadInfo_mem_Icc S lam hlam).1), ?_⟩
    have hb := broadcast_limit_label_bound hCompanion S lam hlam
    have hchild (a : S.rootChildren) :
        z (a.val :: v) = cubicInfoScale (sqParam lam) * cubicInfoTransform
          (limitQuadInfo (S.subtree [a.val] (S.rootChild_mem a)) lam) := by
      have hav : a.val :: v ∈ T.verts := S.rootChild_mem a
      dsimp [z]
      rw [dif_pos hav]
      congr 3
      exact (T.subtree_subtree v hv [a.val] (S.rootChild_mem a)).symm
    simp_rw [← hchild] at hb
    convert hb using 1
    rw [Finset.sum_coe_sort S.rootChildren
      (fun a => sqParam lam * z (a :: v) / Real.sqrt (1 + z (a :: v) ^ 2))]
    dsimp [BoundedTree.children, BoundedTree.rootChildren, S, BoundedTree.subtree]
    rw [Finset.sum_image]
    intro a _ b _ h
    exact List.cons.inj h |>.1
  · dsimp [z]
    rw [dif_pos T.nil_mem, T.subtree_root]

-- @node: capacity_pos_of_reconstructs
/-- Assuming [the companion moment-saving property](hyp:hCompanion), [an infinite
rooted tree with a strictly positive finite branching bound](hyp:hT), [a channel
parameter strictly between zero and one](hyp:hlam), and [strictly positive
limiting reconstruction information](hyp:hrec), [the tree's cubic capacity is
strictly positive](goal). -/
theorem capacity_pos_of_reconstructs (hCompanion : CompanionMomentSaving)
    {B : ℕ} (T : BoundedTree B) (lam : ℝ) (hT : MainTree T) (hlam : MainLambda lam)
    (hrec : 0 < limitInfo T lam) : 0 < capacity3 T lam := by
  obtain ⟨z, hz, hroot⟩ := broadcast_limit_flow_labels hCompanion T lam hlam
  have hpos : 0 < z [] := by
    rw [hroot]
    exact mul_pos (cubicInfoScale_pos (sqParam_mem_Ioo lam hlam))
      (cubicInfoTransform_pos ((reconstructs_iff_limitQuadInfo_pos T lam hlam).mp hrec))
  exact (ENNReal.ofReal_pos.mpr hpos).trans_le
    (exists_flow_of_labels T lam z hT hlam hz).2

end OaiCapacityCriterionState
