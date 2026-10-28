module

public import Papers.OaiCapacityCriterionState.Helpers.BroadcastCompanion
public import Mathlib.Data.List.NodupEquivFin

/-! # Identification of recursive and broadcast posterior experiments

Enumerating the children in the recursive product order identifies its factors
with the independent broadcast experiments in the rooted child subtrees.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace OaiCapacityCriterionState

-- @node: experimentLaw_fin_foldr
/-- For finitely many finite-observation experiments with [conditional likelihoods
for each experiment, root state, and observation](hyp:lik), [nonnegative conditional
likelihoods](hyp:hnonneg) that [sum to one for each root state in each
experiment](hyp:hnorm), [the posterior law of their conditionally independent
product equals the successive combination of their posterior laws, in index
order, starting from the uninformative law](goal). -/
lemma experimentLaw_fin_foldr (n : ℕ) (O : Fin n → Type)
    [∀ a, Fintype (O a)] (lik : ∀ a, Fin 4 → O a → ℝ)
    (hnonneg : ∀ a i o, 0 ≤ lik a i o)
    (hnorm : ∀ a i, ∑ o, lik a i o = 1) :
    experimentLaw (fun i (obs : ∀ a, O a) => ∏ a, lik a i (obs a)) =
      (List.ofFn (fun a => experimentLaw (lik a))).foldr starLaw uninformativeLaw := by
  induction n with
  | zero => simpa using experimentLaw_fin_zero O lik
  | succ n ih =>
      rw [experimentLaw_fin_succ O lik hnonneg hnorm, List.ofFn_succ, List.foldr_cons]
      rw [ih (fun a => O a.succ) (fun a => lik a.succ)
        (fun a => hnonneg a.succ) (fun a => hnorm a.succ)]

-- @node: BoundedTree.childSubtreeEquiv
/-- For [a bounded tree](hyp:T) and [a vertex address v](hyp:v) that [belongs to
the tree](hyp:hv), the [child-subtree correspondence is a bijection between the
root children of the subtree at v and the children of v in the original tree](goal). -/
noncomputable def BoundedTree.childSubtreeEquiv {B : ℕ} (T : BoundedTree B)
    (v : List (Fin B)) (hv : v ∈ T.verts) :
    (T.subtree v hv).rootChildren ≃ T.children v := by
  classical
  refine Equiv.ofBijective (fun a => ⟨a.val :: v, ?_⟩) ?_
  · exact Finset.mem_image.mpr ⟨a.val,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (T.subtree v hv).rootChild_mem a⟩, rfl⟩
  · constructor
    · intro a b h
      exact Subtype.ext (List.cons.inj (congrArg Subtype.val h)).1
    · intro w
      obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp w.property
      refine ⟨⟨a, ?_⟩, Subtype.ext heq⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩

-- @node: treeExperimentLaw_eq_broadcast_subtree
/-- If [the channel parameter lies strictly between zero and one](hyp:hlam) and
[v is a vertex of the tree](hyp:hv), then [the recursively constructed experiment
law at v and depth n equals the depth-n broadcast posterior law on the subtree
rooted at v](goal). -/
lemma treeExperimentLaw_eq_broadcast_subtree {B : ℕ} (T : BoundedTree B)
    (lam : ℝ) (hlam : MainLambda lam) (n : ℕ) (v : List (Fin B))
    (hv : v ∈ T.verts) :
    treeExperimentLaw T lam n v = broadcastPosteriorLaw (T.subtree v hv) lam n := by
  classical
  induction n generalizing v with
  | zero => exact (broadcastPosteriorLaw_zero _ lam).symm
  | succ n ih =>
      let S := T.subtree v hv
      let l := (T.children v).toList
      let g : Fin l.length ≃ T.children v :=
        (List.Nodup.getEquiv l (Finset.nodup_toList _)).trans
          (Equiv.subtypeEquivRight (fun w => Finset.mem_toList))
      let e : Fin l.length ≃ S.rootChildren := g.trans (T.childSubtreeEquiv v hv).symm
      have he (a : Fin l.length) : (e a).val :: v = l.get a := by
        have h := congrArg Subtype.val ((T.childSubtreeEquiv v hv).apply_symm_apply (g a))
        exact h
      have ht : IsChannelParameter lam := ⟨hlam.1.le, hlam.2.le⟩
      rw [broadcastPosteriorLaw_root_branches, experimentLaw_pi_reindex e]
      rw [experimentLaw_fin_foldr _ _ _
        (fun a => channelLikelihood_nonneg lam ht _ (broadcastLikelihood_nonneg _ lam ht n))
        (fun a => channelLikelihood_sum lam _ (broadcastLikelihood_sum _ lam n))]
      have hf (a : Fin l.length) :
          experimentLaw (channelLikelihood lam (broadcastLikelihood
            (S.subtree [(e a).val] (S.rootChild_mem (e a))) lam n)) =
          channelStep lam (treeExperimentLaw T lam n (l.get a)) := by
        rw [experimentLaw_channel lam ht _ (broadcastLikelihood_nonneg _ lam ht n)
          (broadcastLikelihood_sum _ lam n)]
        have hw : l.get a ∈ T.verts := by
          rw [← he a]
          exact S.rootChild_mem (e a)
        rw [ih _ hw]
        change channelStep lam (broadcastPosteriorLaw
          ((T.subtree v hv).subtree [(e a).val] _) lam n) = _
        rw [T.subtree_subtree]
        simp only [List.singleton_append, he a]
      dsimp only [S] at hf
      simp_rw [hf]
      change ((l.map (treeExperimentLaw T lam n)).map (channelStep lam)).foldr
        starLaw uninformativeLaw = _
      rw [List.map_map]
      congr 1
      symm
      simpa only [List.ofFn_get, Function.comp_def] using
        (List.ofFn_comp' l.get (fun w => channelStep lam (treeExperimentLaw T lam n w)))

-- @node: treeExperimentLaw_root_eq_broadcastPosteriorLaw
/-- If [the channel parameter lies strictly between zero and one](hyp:hlam), then
[the recursively constructed experiment law at the root equals the broadcast
posterior law at the same depth](goal). -/
lemma treeExperimentLaw_root_eq_broadcastPosteriorLaw {B : ℕ} (T : BoundedTree B)
    (lam : ℝ) (hlam : MainLambda lam) (n : ℕ) :
    treeExperimentLaw T lam n [] = broadcastPosteriorLaw T lam n := by
  simpa only [BoundedTree.subtree_root] using
    treeExperimentLaw_eq_broadcast_subtree T lam hlam n [] T.nil_mem

end OaiCapacityCriterionState
