module
public import Papers.OaiGraphDecompositionsIntegral.Basic
public import Mathlib.Combinatorics.Hall.Basic

/-! # The Hall matching step for transfer -/

public section

namespace Papers.OaiGraphDecompositionsIntegral

-- @node: lem:transfer-hall
/-- Suppose [D, Y, and J form a transfer configuration with parameters n
and s](hyp:hconfiguration), [U consists of positive-degree vertices of J
outside Y](hyp:hU), [each vertex in U has all its candidates outside
Y](hyp:hcand), and [every subset of U has at least as many distinct
candidates collectively as it has vertices](hyp:hHall). Then [there is
a function on the n vertices that is injective on U and assigns each
vertex in U one of its candidates](goal).

Philip Hall (1935), *On representatives of subsets*; handle `cite:hall35`. -/
lemma transfer_hall {n s : ℕ} (D : Set (Finset (KEdge n))) (Y : Finset (Fin n))
    (J : SimpleGraph (Fin n)) [DecidableRel J.Adj]
    (hconfiguration : TransferConfiguration n s D Y J)
    (U : Finset (Fin n)) -- @realizes U(finite set of outside vertices to match)
    (cand : Fin n → Finset (Fin n))
    (hU : U ⊆ (Finset.univ \ Y).filter (fun w => 0 < J.degree w))
    (hcand : ∀ w ∈ U, cand w ⊆ Finset.univ \ Y)
    (hHall : ∀ U' ⊆ U, U'.card ≤ (U'.biUnion cand).card) :
    ∃ f : Fin n → Fin n, Set.InjOn f U ∧ ∀ w ∈ U, f w ∈ cand w := by
  classical
  have hrestricted : ∀ S : Finset U,
      S.card ≤ (S.biUnion (fun w : U => cand w)).card := by
    intro S
    have hsub : S.image Subtype.val ⊆ U := by
      intro w hw
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hw
      exact v.property
    have h := hHall (S.image Subtype.val) hsub
    simpa only [Finset.card_image_of_injective S Subtype.coe_injective,
      Finset.image_biUnion] using h
  obtain ⟨g, hg, hmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective'
      (fun w : U => cand w)).mp hrestricted
  let f : Fin n → Fin n := fun w => if hw : w ∈ U then g ⟨w, hw⟩ else w
  refine ⟨f, ?_, ?_⟩
  · intro v hv w hw heq
    change v ∈ U at hv
    change w ∈ U at hw
    have heq' : g ⟨v, hv⟩ = g ⟨w, hw⟩ := by simpa [f, hv, hw] using heq
    exact congrArg Subtype.val (hg heq')
  · intro w hw
    simpa [f, hw] using hmem ⟨w, hw⟩

end Papers.OaiGraphDecompositionsIntegral
