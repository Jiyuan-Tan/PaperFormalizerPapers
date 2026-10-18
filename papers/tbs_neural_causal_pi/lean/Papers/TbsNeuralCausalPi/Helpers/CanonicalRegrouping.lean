module
public import Papers.TbsNeuralCausalPi.Setup.Assumptions.Model
public import Mathlib.Order.Preorder.Finite
/-! # Assigning original latent blocks to canonical components

The bidirected graph uses statistical dependence, so a block independent of
itself may occur at unrelated vertices. Such blocks can be copied into several
components. Every other block is assigned to a single containing maximal clique.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
noncomputable section

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}

/-- If [the model's named latent blocks are jointly independent](hyp:hind), then [two nodes are adjacent in its bidirected causal graph exactly when they are distinct and share an incident non-Gumbel block that is not independent of itself](goal). -/
-- @node: causalGraph_adj_iff_shared_dependent_block
lemma causalGraph_adj_iff_shared_dependent_block (M : EuclideanSCM kind dims)
    (hind : LatentBlocksIndependent M) (i j : Fin n) :
    (causalGraph M).2.Adj i j ↔ i ≠ j ∧ ∃ k : Fin b,
      k ∈ M.incidence i ∧ k ∈ M.incidence j ∧
      ¬ IndepFun (blockProjection k) (blockProjection k) M.latentLaw := by
  constructor
  · rintro ⟨hij, h | h⟩
    · rcases h with ⟨k, hk, l, hl, hdep⟩
      have hkl : k = l := by
        by_contra hne
        exact hdep (hind.indepFun (show Sum.inl k ≠ (Sum.inl l : Fin b ⊕ Fin n) from
          fun h => hne (Sum.inl.inj h)))
      subst l
      exact ⟨hij, k, hk, hl, hdep⟩
    · rcases h with ⟨k, hk, l, hl, hdep⟩
      have hkl : k = l := by
        by_contra hne
        exact hdep (hind.indepFun (show Sum.inl k ≠ (Sum.inl l : Fin b ⊕ Fin n) from
          fun h => hne (Sum.inl.inj h)))
      subst l
      exact ⟨hij, k, hl, hk, hdep⟩
  · rintro ⟨hij, k, hk, hk', hdep⟩
    exact ⟨hij, Or.inl ⟨k, hk, k, hk', hdep⟩⟩

/-- If [the model's named latent blocks are jointly independent](hyp:hind) and [a particular non-Gumbel block is not independent of itself](hyp:hk), then [the nodes receiving that block form a clique in the bidirected causal graph](goal). -/
-- @node: latent_incidence_isClique
lemma latent_incidence_isClique (M : EuclideanSCM kind dims)
    (hind : LatentBlocksIndependent M) (k : Fin b)
    (hk : ¬ IndepFun (blockProjection k) (blockProjection k) M.latentLaw) :
    (causalGraph M).2.IsClique {i | k ∈ M.incidence i} := by
  intro i hi j hj hij
  exact (causalGraph_adj_iff_shared_dependent_block M hind i j).2 ⟨hij, k, hi, hj, hk⟩

/-- If [a set of nodes is a clique in the given graph](hyp:hs), then [it is contained in a maximal clique, called a C²-component](goal). -/
-- @node: clique_subset_canonical_component
lemma clique_subset_canonical_component (G : SimpleGraph (Fin n))
    (s : Set (Fin n)) (hs : G.IsClique s) :
    ∃ t, s ⊆ t ∧ IsC2Component G t := by
  obtain ⟨t, hst, ht⟩ := Finite.exists_le_maximal hs
  exact ⟨t, hst, ⟨ht⟩⟩

/-- [Every finite graph admits a finite enumeration of its C²-components, each a maximal clique, that lists every component exactly once and characterizes adjacency by distinct nodes belonging to a common component](goal). -/
-- @node: exists_canonical_component_enumeration
lemma exists_canonical_component_enumeration (G : SimpleGraph (Fin n)) :
    ∃ b' : ℕ, ∃ C : Fin b' → Set (Fin n),
      (∀ c, IsC2Component G (C c)) ∧
      (∀ s, IsC2Component G s → ∃ c, C c = s) ∧
      Function.Injective C ∧
      (∀ i j, G.Adj i j ↔ i ≠ j ∧ ∃ c, i ∈ C c ∧ j ∈ C c) := by
  classical
  let K := {s : Set (Fin n) // IsC2Component G s}
  let : Fintype K := Fintype.ofFinite K
  let e := Fintype.equivFin K
  let C : Fin (Fintype.card K) → Set (Fin n) := fun c => (e.symm c).val
  refine ⟨Fintype.card K, C, (fun c => (e.symm c).property), ?_, ?_, ?_⟩
  · intro s hs
    exact ⟨e ⟨s, hs⟩, by simp [C]⟩
  · intro c d h
    apply e.symm.injective
    exact Subtype.ext h
  · intro i j
    constructor
    · intro hij
      have hclique : G.IsClique {i,j} := SimpleGraph.isClique_pair.mpr (fun _ => hij)
      obtain ⟨s, hsub, hs⟩ := clique_subset_canonical_component G {i,j} hclique
      refine ⟨hij.ne, e ⟨s, hs⟩, ?_, ?_⟩
      · simpa [C] using hsub (by simp : i ∈ ({i,j} : Set (Fin n)))
      · simpa [C] using hsub (by simp : j ∈ ({i,j} : Set (Fin n)))
    · rintro ⟨hij, c, hi, hj⟩
      exact (e.symm c).property.maximalClique.1 hi hj hij

/-- If [the model's named latent blocks are jointly independent](hyp:hind), then [there is a finite enumeration of all C²-components of its bidirected graph without repetition, with groups covering all original non-Gumbel blocks, such that each node receives every required block from a component containing that node, distinct groups share only blocks independent of themselves, and distinct nodes are adjacent exactly when they share a component](goal). -/
-- @node: exists_canonical_latent_grouping
lemma exists_canonical_latent_grouping (M : EuclideanSCM kind dims)
    (hind : LatentBlocksIndependent M) :
    ∃ b' : ℕ, ∃ C : Fin b' → Set (Fin n), ∃ groups : Fin b' → Finset (Fin b),
      (∀ c, IsC2Component (causalGraph M).2 (C c)) ∧
      (∀ s, IsC2Component (causalGraph M).2 s → ∃ c, C c = s) ∧
      Function.Injective C ∧
      (∀ k, ∃ c, k ∈ groups c) ∧
      (∀ i k, k ∈ M.incidence i → ∃ c, i ∈ C c ∧ k ∈ groups c) ∧
      (∀ c d k, k ∈ groups c → k ∈ groups d → c ≠ d →
        IndepFun (blockProjection k) (blockProjection k) M.latentLaw) ∧
      (∀ i j, (causalGraph M).2.Adj i j ↔ i ≠ j ∧ ∃ c, i ∈ C c ∧ j ∈ C c) := by
  classical
  obtain ⟨b', C, hC, hexhaustive, hinj, hgraph⟩ :=
    exists_canonical_component_enumeration (causalGraph M).2
  have hcover (s : Set (Fin n)) (hs : (causalGraph M).2.IsClique s) :
      ∃ c, s ⊆ C c := by
    obtain ⟨t, hst, ht⟩ := clique_subset_canonical_component (causalGraph M).2 s hs
    obtain ⟨c, rfl⟩ := hexhaustive t ht
    exact ⟨c, hst⟩
  obtain ⟨c₀, hc₀⟩ := hcover ∅ (by intro i hi; exact hi.elim)
  have hassign (k : Fin b) : ∃ c, ∀ i, k ∈ M.incidence i →
      ¬ IndepFun (blockProjection k) (blockProjection k) M.latentLaw → i ∈ C c := by
    by_cases hk : IndepFun (blockProjection k) (blockProjection k) M.latentLaw
    · exact ⟨c₀, fun _ _ h => (h hk).elim⟩
    · obtain ⟨c, hc⟩ := hcover {i | k ∈ M.incidence i} (latent_incidence_isClique M hind k hk)
      exact ⟨c, fun _ hi _ => hc hi⟩
  choose assign hassign using hassign
  let groups : Fin b' → Finset (Fin b) := fun c => Finset.univ.filter (fun k =>
    IndepFun (blockProjection k) (blockProjection k) M.latentLaw ∨ assign k = c)
  have hmem (c : Fin b') (k : Fin b) : k ∈ groups c ↔
      IndepFun (blockProjection k) (blockProjection k) M.latentLaw ∨ assign k = c := by
    simp [groups]
  refine ⟨b', C, groups, hC, hexhaustive, hinj, ?_, ?_, ?_, hgraph⟩
  · intro k
    exact ⟨assign k, (hmem _ _).2 (Or.inr rfl)⟩
  · intro i k hik
    by_cases hk : IndepFun (blockProjection k) (blockProjection k) M.latentLaw
    · obtain ⟨c, hc⟩ := hcover {i} ((causalGraph M).2.isClique_singleton i)
      exact ⟨c, hc (by simp), (hmem _ _).2 (Or.inl hk)⟩
    · exact ⟨assign k, hassign k i hik hk, (hmem _ _).2 (Or.inr rfl)⟩
  · intro c d k hkc hkd hcd
    rcases (hmem c k).1 hkc with hk | hk
    · exact hk
    · rcases (hmem d k).1 hkd with hk' | hk'
      · exact hk'
      · exact (hcd (hk.symm.trans hk')).elim

/-- If [every original block belongs to at least one of the given groups](hyp:hcover), then [there exist finite dimensions and coordinate bijections for the grouped blocks, a measurable regrouping map that copies the indicated block coordinates and preserves intrinsic noise coordinates, and a representative group for each original block whose measurable recovery map recovers every original exogenous vector and every original probability or measure law](goal). -/
-- @node: exists_canonical_regrouping_coordinates
lemma exists_canonical_regrouping_coordinates {b' : ℕ}
    (groups : Fin b' → Finset (Fin b)) (hcover : ∀ j, ∃ c, j ∈ groups c) :
    ∃ dims' : Fin b' → ℕ,
    ∃ coords : ∀ c, Fin (dims' c) ≃ (Σ j : {j // j ∈ groups c}, Fin (dims j)),
    ∃ merge : Exogenous kind dims → Exogenous kind dims',
      Measurable merge ∧
      (∀ u c k, (merge u).ofLp (.inl ⟨c,k⟩) =
        u.ofLp (.inl ⟨(coords c k).1.val, (coords c k).2⟩)) ∧
      (∀ u i k, (merge u).ofLp (.inr ⟨i,k⟩) = u.ofLp (.inr ⟨i,k⟩)) ∧
    ∃ representative : ∀ j, {c // j ∈ groups c},
      let recover := fun u : Exogenous kind dims' => WithLp.toLp 1 (fun q =>
        match q with
        | .inl ⟨j,k⟩ => u.ofLp (.inl ⟨(representative j).val,
            (coords (representative j).val).symm ⟨⟨j, (representative j).property⟩, k⟩⟩)
        | .inr q => u.ofLp (.inr q))
      Measurable recover ∧ (∀ u, recover (merge u) = u) ∧
      ∀ μ : Measure (Exogenous kind dims), (μ.map merge).map recover = μ := by
  classical
  let dims' : Fin b' → ℕ := fun c =>
    Fintype.card (Σ j : {j // j ∈ groups c}, Fin (dims j))
  let coords : ∀ c, Fin (dims' c) ≃ (Σ j : {j // j ∈ groups c}, Fin (dims j)) :=
    fun c => (Fintype.equivFin _).symm
  let merge : Exogenous kind dims → Exogenous kind dims' := fun u =>
    WithLp.toLp 1 (fun q => match q with
      | .inl ⟨c,k⟩ => u.ofLp (.inl ⟨(coords c k).1.val, (coords c k).2⟩)
      | .inr q => u.ofLp (.inr q))
  have hm : Measurable merge := by
    apply scm_toLp_measurable.comp
    apply measurable_pi_lambda
    rintro (⟨c,k⟩ | q) <;>
      exact (measurable_pi_apply _).comp scm_ofLp_measurable
  let representative : ∀ j, {c // j ∈ groups c} := fun j =>
    ⟨Classical.choose (hcover j), Classical.choose_spec (hcover j)⟩
  let recover : Exogenous kind dims' → Exogenous kind dims := fun u =>
    WithLp.toLp 1 (fun q => match q with
      | .inl ⟨j,k⟩ => u.ofLp (.inl ⟨(representative j).val,
          (coords (representative j).val).symm ⟨⟨j, (representative j).property⟩, k⟩⟩)
      | .inr q => u.ofLp (.inr q))
  have hr : Measurable recover := by
    apply scm_toLp_measurable.comp
    apply measurable_pi_lambda
    rintro (⟨j,k⟩ | q) <;>
      exact (measurable_pi_apply _).comp scm_ofLp_measurable
  have hre (u : Exogenous kind dims) : recover (merge u) = u := by
    apply WithLp.ofLp_injective
    funext q
    rcases q with ⟨j,k⟩ | q
    · dsimp only [recover, merge, WithLp.ofLp_toLp]
      rw [Equiv.apply_symm_apply]
    · rfl
  refine ⟨dims', coords, merge, hm, (fun _ _ _ => rfl), (fun _ _ _ => rfl),
    representative, hr, hre, ?_⟩
  intro μ
  rw [Measure.map_map hr hm]
  have he : recover ∘ merge = id := funext hre
  rw [he, Measure.map_id]

/-- If [a selection of coordinates is injective](hyp:hf), then [there exists a continuous linear map that returns exactly those coordinates and does not increase one-norm distances](goal). -/
-- @node: exists_l1_coordinate_projection
lemma exists_l1_coordinate_projection {I J : Type*} [Fintype I] [Fintype J]
    (f : I → J) (hf : Function.Injective f) :
    ∃ p : WithLp 1 (J → ℝ) →L[ℝ] WithLp 1 (I → ℝ),
      (∀ x i, (p x).ofLp i = x.ofLp (f i)) ∧ LipschitzWith 1 p := by
  classical
  let l : WithLp 1 (J → ℝ) →ₗ[ℝ] WithLp 1 (I → ℝ) :=
    { toFun := fun x => WithLp.toLp 1 (fun i => x.ofLp (f i))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hn (x : WithLp 1 (J → ℝ)) : ‖l x‖ ≤ 1 * ‖x‖ := by
    rw [one_mul, PiLp.norm_eq_of_L1, PiLp.norm_eq_of_L1]
    change (∑ i, ‖x.ofLp (f i)‖) ≤ ∑ j, ‖x.ofLp j‖
    calc
      _ = ∑ j ∈ Finset.univ.image f, ‖x.ofLp j‖ :=
        (Finset.sum_image (fun _ _ _ _ he => hf he)).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => norm_nonneg _)
  refine ⟨l.mkContinuous 1 hn, (fun _ _ => rfl), ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm, NNReal.coe_one, ← map_sub, LinearMap.mkContinuous_apply]
    using hn (x-y)

/-- Given [bijections identifying each grouped block's coordinates with its constituent original block coordinates](hyp:coords) and [a choice, for every block incident to each node, of a canonical component incident to that node whose group contains the block](hyp:locate), [there exist continuous linear projections from canonical structural inputs to original structural inputs that preserve parent coordinates, recover each original block coordinate from the chosen component using those bijections, do not increase distances, and send admissible canonical inputs into the original domains](goal). -/
-- @node: exists_canonical_structural_projection
lemma exists_canonical_structural_projection (M : EuclideanSCM kind dims)
    {b' : ℕ} (dims' : Fin b' → ℕ) (C : Fin b' → Set (Fin n))
    (groups : Fin b' → Finset (Fin b))
    (coords : ∀ c, Fin (dims' c) ≃ (Σ j : {j // j ∈ groups c}, Fin (dims j)))
    (locate : ∀ i (j : {j // j ∈ M.incidence i}),
      {c // c ∈ canonicalIncidence C i ∧ j.val ∈ groups c}) :
    ∃ pi : ∀ i, StructuralInput kind dims' M.dag (canonicalIncidence C) i →L[ℝ]
        StructuralInput kind dims M.dag M.incidence i,
      (∀ i x p k, (pi i x).ofLp (.inl ⟨p,k⟩) = x.ofLp (.inl ⟨p,k⟩)) ∧
      (∀ i x j k, (pi i x).ofLp (.inr ⟨j,k⟩) =
        x.ofLp (.inr ⟨⟨(locate i j).val, (locate i j).property.1⟩,
          (coords (locate i j).val).symm ⟨⟨j.val, (locate i j).property.2⟩, k⟩⟩)) ∧
      (∀ i, LipschitzWith 1 (pi i) ∧
        Set.MapsTo (pi i) (admissibleStructuralInputs kind dims' M.dag (canonicalIncidence C) i)
          (M.domain i)) := by
  classical
  have hp (i : Fin n) :
      ∃ p : StructuralInput kind dims' M.dag (canonicalIncidence C) i →L[ℝ]
          StructuralInput kind dims M.dag M.incidence i,
        (∀ x p' k, (p x).ofLp (.inl ⟨p',k⟩) = x.ofLp (.inl ⟨p',k⟩)) ∧
        (∀ x j k, (p x).ofLp (.inr ⟨j,k⟩) =
          x.ofLp (.inr ⟨⟨(locate i j).val, (locate i j).property.1⟩,
            (coords (locate i j).val).symm ⟨⟨j.val, (locate i j).property.2⟩, k⟩⟩)) ∧
        LipschitzWith 1 p := by
    let f : (Σ p : {p // p ∈ M.dag.parents i}, Fin (valueDim (kind p))) ⊕
        (Σ j : {j // j ∈ M.incidence i}, Fin (dims j)) →
        (Σ p : {p // p ∈ M.dag.parents i}, Fin (valueDim (kind p))) ⊕
        (Σ c : {c // c ∈ canonicalIncidence C i}, Fin (dims' c)) := fun q =>
      match q with
      | .inl q => .inl q
      | .inr ⟨j,k⟩ => .inr ⟨⟨(locate i j).val, (locate i j).property.1⟩,
          (coords (locate i j).val).symm ⟨⟨j.val, (locate i j).property.2⟩, k⟩⟩
    have hf : Function.Injective f := by
      intro a b hab
      rcases a with a | ⟨a,k⟩ <;> rcases b with b | ⟨b,l⟩
      · exact congrArg Sum.inl (Sum.inl.inj hab)
      · cases hab
      · cases hab
      · have he := congrArg (fun q : (Σ c : {c // c ∈ canonicalIncidence C i}, Fin (dims' c)) =>
            (⟨(coords q.1.val q.2).1.val, (coords q.1.val q.2).2⟩ : Σ j, Fin (dims j)))
          (Sum.inr.inj hab)
        dsimp only [f] at he
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at he
        have hab' : a = b := Subtype.ext (congrArg Sigma.fst he)
        subst b
        have hkl : k = l := eq_of_heq (Sigma.mk.inj_iff.mp he).2
        subst l
        rfl
    obtain ⟨p, hcoord, hLip⟩ := exists_l1_coordinate_projection f hf
    exact ⟨p, (fun x p' k => hcoord x (.inl ⟨p',k⟩)),
      (fun x j k => hcoord x (.inr ⟨j,k⟩)), hLip⟩
  choose pi hparents hlatents hLip using hp
  refine ⟨pi, hparents, hlatents, ?_⟩
  intro i
  refine ⟨hLip i, ?_⟩
  intro x hx
  refine ⟨?_, Set.mem_univ _⟩
  intro p k hk
  obtain ⟨label, hlabel⟩ := hx p k hk
  exact ⟨label, fun j => (hparents i x p j).trans (hlabel j)⟩

end
end Papers.TbsNeuralCausalPi
