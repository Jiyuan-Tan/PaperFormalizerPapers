module
public import Papers.TbsNeuralCausalPi.Setup.Assumptions.Estimation
public import Papers.TbsNeuralCausalPi.Setup.CitedResults
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Papers.TbsNeuralCausalPi.Helpers.CanonicalNormalization
public import Papers.TbsNeuralCausalPi.Helpers.CanonicalEvaluation
/-! # Law-preserving canonical regrouping -/
public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)} {C : Fin b → Set (Fin n)}

set_option maxHeartbeats 800000 in
-- @node: prop:equivalent-g-constrianed
/-- For [a Euclidean structural causal model](hyp:M) and [mechanism weights](hyp:p), suppose
[the latent blocks are independent](hyp:hind), [the noise has a latent Gumbel
decomposition](hyp:hdecomp), [categorical mechanisms follow Gumbel argmax with
these weights](hyp:hcat), and [categorical weights are nonnegative with positive
total mass on their domains](hyp:hpositive). Then [there exists a canonical
model with the same directed and bidirected causal graphs and every
interventional distribution unchanged, obtained by regrouping latent blocks
through coordinate bijections while retaining categorical noise, with its
latent law given by this regrouping and the original law recoverable by
coordinate selection; linear input projections retain parents, select the
corresponding latent coordinates, are nonexpansive, and map new domains into
old ones, and the new mechanisms are the old continuous mechanisms or
normalized categorical weights composed with these projections, preserving
continuous-mechanism Lipschitz constants and differentiability, normalized
categorical Lipschitz constants, and categorical differentiability and local
Lipschitz regularity](goal). -/
theorem exists_canonical_representation (M : EuclideanSCM kind dims)
    (p : MechanismWeights M)
    (hind : LatentBlocksIndependent M) (hdecomp : LatentGumbelDecomposition M)
    (hcat : CategoricalGumbelArgmax M p) (hpositive : CategoricalWeightsPositive M p) :
    ∃ b' : ℕ, ∃ dims' : Fin b' → ℕ, ∃ C' : Fin b' → Set (Fin n),
      ∃ Mhat : CanonicalSCM kind dims' M.dag (causalGraph M).2 C',
        (∀ t : LawIntervention kind, interventionalLaw M t = interventionalLaw Mhat.toEuclideanSCM t) ∧
        ∃ groups : Fin b' → Finset (Fin b),
        ∃ coords : ∀ c, Fin (dims' c) ≃ (Σ j : {j // j ∈ groups c}, Fin (dims j)),
        ∃ merge : Exogenous kind dims → Exogenous kind dims',
          (∀ u c k, (merge u).ofLp (.inl ⟨c,k⟩) =
            u.ofLp (.inl ⟨(coords c k).1.val, (coords c k).2⟩)) ∧
          (∀ u i k, (merge u).ofLp (.inr ⟨i,k⟩) = u.ofLp (.inr ⟨i,k⟩)) ∧
          Mhat.latentLaw = M.latentLaw.map merge ∧
        ∃ representative : ∀ j, {c // j ∈ groups c},
          let recover := fun u : Exogenous kind dims' => WithLp.toLp 1 (fun q =>
            match q with
            | .inl ⟨j,k⟩ => u.ofLp (.inl ⟨(representative j).val,
                (coords (representative j).val).symm ⟨⟨j, (representative j).property⟩, k⟩⟩)
            | .inr q => u.ofLp (.inr q))
          Mhat.latentLaw.map recover = M.latentLaw ∧
        ∃ locate : ∀ i (j : {j // j ∈ M.incidence i}),
          {c // c ∈ canonicalIncidence C' i ∧ j.val ∈ groups c},
        ∃ pi : ∀ i, StructuralInput kind dims' M.dag (canonicalIncidence C') i →L[ℝ]
          StructuralInput kind dims M.dag M.incidence i,
          (∀ i x p k, (pi i x).ofLp (.inl ⟨p,k⟩) = x.ofLp (.inl ⟨p,k⟩)) ∧
          (∀ i x j k, (pi i x).ofLp (.inr ⟨j,k⟩) =
            x.ofLp (.inr ⟨⟨(locate i j).val, (locate i j).property.1⟩,
              (coords (locate i j).val).symm ⟨⟨j.val, (locate i j).property.2⟩, k⟩⟩)) ∧
          (∀ i, LipschitzWith 1 (pi i) ∧
            Set.MapsTo (pi i) (Mhat.domain i) (M.domain i)) ∧
          (∀ i d, kind i = Sum.inl d → ∀ x ∈ Mhat.domain i, Mhat.f i x = M.continuousMap i (pi i x)) ∧
          (∀ i k, kind i = Sum.inr k → ∀ x ∈ Mhat.domain i,
            Mhat.f i x = WithLp.toLp 1 (fun j =>
              (p i (pi i x)).ofLp j / ∑ l, (p i (pi i x)).ofLp l)) ∧
          (∀ i d, kind i = Sum.inl d → ∀ L : ℝ≥0,
            LipschitzOnWith L (M.continuousMap i) (M.domain i) → LipschitzOnWith L (Mhat.f i) (Mhat.domain i)) ∧
          (∀ i d, kind i = Sum.inl d → ∀ r,
            ContDiffOn ℝ r (M.continuousMap i) (M.domain i) → ContDiffOn ℝ r (Mhat.f i) (Mhat.domain i)) ∧
          (∀ i k, kind i = Sum.inr k → ∀ L : ℝ≥0,
            LipschitzOnWith L (fun x => WithLp.toLp 1 (fun j =>
              (p i x).ofLp j / ∑ l, (p i x).ofLp l)) (M.domain i) →
                LipschitzOnWith L (Mhat.f i) (Mhat.domain i)) ∧
          (∀ i k, kind i = Sum.inr k → ∀ r,
            ContDiffOn ℝ r (p i) (M.domain i) → ContDiffOn ℝ r (Mhat.f i) (Mhat.domain i)) ∧
          (∀ i k, kind i = Sum.inr k →
            (∀ x ∈ M.domain i, ∃ A : ℝ≥0, ∃ r : ℝ, 0 < r ∧ LipschitzOnWith A (p i) (Metric.ball x r ∩ M.domain i)) →
            ∀ x ∈ Mhat.domain i, ∃ A : ℝ≥0, ∃ r : ℝ, 0 < r ∧ LipschitzOnWith A (Mhat.f i) (Metric.ball x r ∩ Mhat.domain i))  := by
  -- Construct the graph, coordinate projections and measurable mechanisms;
  -- transport their synchronous evaluations under each intervention.
  have hconstruction :
    ∃ b' : ℕ, ∃ dims' : Fin b' → ℕ, ∃ C' : Fin b' → Set (Fin n),
      ∃ Mhat : CanonicalSCM kind dims' M.dag (causalGraph M).2 C',
        (∀ t : LawIntervention kind, interventionalLaw M t = interventionalLaw Mhat.toEuclideanSCM t) ∧
        ∃ groups : Fin b' → Finset (Fin b),
        ∃ coords : ∀ c, Fin (dims' c) ≃ (Σ j : {j // j ∈ groups c}, Fin (dims j)),
        ∃ merge : Exogenous kind dims → Exogenous kind dims',
          (∀ u c k, (merge u).ofLp (.inl ⟨c,k⟩) =
            u.ofLp (.inl ⟨(coords c k).1.val, (coords c k).2⟩)) ∧
          (∀ u i k, (merge u).ofLp (.inr ⟨i,k⟩) = u.ofLp (.inr ⟨i,k⟩)) ∧
          Mhat.latentLaw = M.latentLaw.map merge ∧
        ∃ representative : ∀ j, {c // j ∈ groups c},
          let recover := fun u : Exogenous kind dims' => WithLp.toLp 1 (fun q =>
            match q with
            | .inl ⟨j,k⟩ => u.ofLp (.inl ⟨(representative j).val,
                (coords (representative j).val).symm ⟨⟨j, (representative j).property⟩, k⟩⟩)
            | .inr q => u.ofLp (.inr q))
          Mhat.latentLaw.map recover = M.latentLaw ∧
        ∃ locate : ∀ i (j : {j // j ∈ M.incidence i}),
          {c // c ∈ canonicalIncidence C' i ∧ j.val ∈ groups c},
        ∃ pi : ∀ i, StructuralInput kind dims' M.dag (canonicalIncidence C') i →L[ℝ]
          StructuralInput kind dims M.dag M.incidence i,
          (∀ i x p k, (pi i x).ofLp (.inl ⟨p,k⟩) = x.ofLp (.inl ⟨p,k⟩)) ∧
          (∀ i x j k, (pi i x).ofLp (.inr ⟨j,k⟩) =
            x.ofLp (.inr ⟨⟨(locate i j).val, (locate i j).property.1⟩,
              (coords (locate i j).val).symm ⟨⟨j.val, (locate i j).property.2⟩, k⟩⟩)) ∧
          (∀ i, LipschitzWith 1 (pi i) ∧
            Set.MapsTo (pi i) (Mhat.domain i) (M.domain i)) ∧
          (∀ i d, kind i = Sum.inl d → ∀ x ∈ Mhat.domain i, Mhat.f i x = M.continuousMap i (pi i x)) ∧
          (∀ i k, kind i = Sum.inr k → ∀ x ∈ Mhat.domain i,
            Mhat.f i x = WithLp.toLp 1 (fun j =>
              (p i (pi i x)).ofLp j / ∑ l, (p i (pi i x)).ofLp l)) := by
    obtain ⟨b', C', groups, hcomponents, hexhaustive, hdistinct, hcover,
      hinputs, hoverlap, hgraph⟩ := exists_canonical_latent_grouping M hind
    obtain ⟨dims', coords, merge, hmerge_measurable, hmerge, hgumbel,
      representative, hrecover_measurable, hrecover_pointwise, hrecover_law⟩ :=
      exists_canonical_regrouping_coordinates (kind := kind) (dims := dims) groups hcover
    have hlocate (i : Fin n) (j : {j // j ∈ M.incidence i}) :
        ∃ c, c ∈ canonicalIncidence C' i ∧ j.val ∈ groups c := by
      obtain ⟨c, hc, hj⟩ := hinputs i j.val j.property
      exact ⟨c, by simpa only [canonicalIncidence, Finset.mem_filter,
        Finset.mem_univ, true_and] using hc, hj⟩
    let locate : ∀ i (j : {j // j ∈ M.incidence i}),
        {c // c ∈ canonicalIncidence C' i ∧ j.val ∈ groups c} :=
      fun i j => ⟨Classical.choose (hlocate i j), Classical.choose_spec (hlocate i j)⟩
    obtain ⟨pi, hparents, hlatent, hpi⟩ :=
      exists_canonical_structural_projection M dims' C' groups coords locate
    have hmodel : ∃ Mhat : CanonicalSCM kind dims' M.dag (causalGraph M).2 C',
        (∀ t : LawIntervention kind,
          interventionalLaw M t = interventionalLaw Mhat.toEuclideanSCM t) ∧
        Mhat.latentLaw = M.latentLaw.map merge ∧
        (∀ i d, kind i = Sum.inl d → ∀ x ∈ Mhat.domain i,
          Mhat.f i x = M.continuousMap i (pi i x)) ∧
        (∀ i k, kind i = Sum.inr k → ∀ x ∈ Mhat.domain i,
          Mhat.f i x = WithLp.toLp 1 (fun j =>
            (p i (pi i x)).ofLp j / ∑ l, (p i (pi i x)).ofLp l)) := by
      obtain ⟨f, hf, hfcontinuous, hfcategorical, hfsimplex⟩ :=
        exists_canonical_regrouped_mechanisms M p hcat dims' C' pi
          (fun i => (hpi i).2)
      let := M.probability
      have hblock (c : Fin b') : Measurable (fun u => blockProjection c (merge u)) := by
        first | fun_prop | fun_prop [blockProjection]
      let blockLaw : ∀ c, ProbabilityMeasure (L1Vec (dims' c)) := fun c =>
        ⟨M.latentLaw.map (fun u => blockProjection c (merge u)),
          Measure.isProbabilityMeasure_map (hblock c).aemeasurable⟩
      let Mhat : CanonicalSCM kind dims' M.dag (causalGraph M).2 C' :=
        { categoricalPositive := M.categoricalPositive
          component := hcomponents
          exhaustive := hexhaustive
          distinct := hdistinct
          f := f
          structuralMeasurable := hf
          blockLaw := blockLaw
          simplex := hfsimplex }
      have hmergedLaw : Mhat.latentLaw = M.latentLaw.map merge :=
        canonical_regrouped_latent_law M p hind hcat groups coords merge
          hmerge_measurable hmerge hgumbel hoverlap Mhat (fun _ => rfl)
      have hlaws :
          (∀ t : LawIntervention kind,
            interventionalLaw M t = interventionalLaw Mhat.toEuclideanSCM t) ∧
          Mhat.latentLaw = M.latentLaw.map merge := by
        refine ⟨?_, hmergedLaw⟩
        have hinput (i : Fin n) (v : Joint kind) (u : Exogenous kind dims) :
            pi i (structuralInput Mhat.toEuclideanSCM i v (merge u)) =
              structuralInput M i v u :=
          canonical_regrouping_structuralInput M C' groups coords merge hmerge
            locate pi hparents hlatent Mhat i v u
        intro t
        have hdomain (i : Fin n) (u : Exogenous kind dims) :
            structuralInput Mhat.toEuclideanSCM i
              (evalSteps M t.val u (M.dag.topoOrder i)) (merge u) ∈ Mhat.domain i := by
          exact ⟨(evalSteps_structuralInput_mem_domain M t.val t.property u i _ rfl).1,
            Set.mem_univ _⟩
        apply interventionalLaw_regrouped_of_nodeValue_ae M Mhat.toEuclideanSCM
          rfl merge hmerge_measurable hmergedLaw t
        intro i
        have hkind : (∃ d, kind i = Sum.inl d) ∨ (∃ k, kind i = Sum.inr k) := by
          cases h : kind i with
          | inl d => exact Or.inl ⟨d, rfl⟩
          | inr k => exact Or.inr ⟨k, rfl⟩
        rcases hkind with ⟨d, hi⟩ | ⟨k, hi⟩
        · apply Filter.Eventually.of_forall
          intro u
          apply WithLp.ofLp_injective
          funext j
          erw [nodeValue_continuousMap_coordinate M i d hi,
            nodeValue_continuousMap_coordinate Mhat.toEuclideanSCM i d hi,
            canonical_continuousMap_eq_weights Mhat i d hi]
          change (M.continuousMap i _).ofLp _ = (f i _).ofLp _
          erw [hfcontinuous i d hi, hinput]
        · let X := fun u => structuralInput M i
            (evalSteps M t.val u (M.dag.topoOrder i)) u
          have hX : Measurable X := by fun_prop
          have hd (u) : X u ∈ M.domain i :=
            evalSteps_structuralInput_mem_domain M t.val t.property u i _ rfl
          obtain ⟨w, hw, hwn⟩ := exists_measurable_normalized_propensity M p hcat i k hi
          have he := categoricalLabel_random_input_ae_normalized M p hcat i k hi X hX hd
            (structuralInput_evalSteps_indep_current_gumbels M hind i t.val k hi) w hw hwn
          filter_upwards [he] with u hu
          apply nodeValue_eq_of_categoricalLabel_eq M Mhat.toEuclideanSCM i k hi
          have hweights : Mhat.f i (structuralInput Mhat.toEuclideanSCM i
                (evalSteps M t.val u (M.dag.topoOrder i)) (merge u)) = w (X u) := by
            change f i _ = _
            rw [hfcategorical i k hi _ (hdomain i u).1, hinput, hwn _ (hd u)]
          erw [canonical_categoricalLabel_eq_selector, hweights,
            canonical_regrouping_categoricalNoise merge hgumbel]
          exact hu

      refine ⟨Mhat, hlaws.1, hlaws.2, ?_, ?_⟩
      · intro i d hi x hx
        exact hfcontinuous i d hi x
      · intro i k hi x hx
        exact hfcategorical i k hi x hx.1
    obtain ⟨Mhat, hlaw, hmergedLaw, hcontinuous, hcategorical⟩ := hmodel
    refine ⟨b', dims', C', Mhat, hlaw, groups, coords, merge, hmerge, hgumbel,
      hmergedLaw, representative, ?_, locate, pi, hparents, hlatent, ?_,
      hcontinuous, hcategorical⟩
    · rw [hmergedLaw]
      exact hrecover_law M.latentLaw
    · intro i
      exact ⟨(hpi i).1, fun x hx => (hpi i).2 hx.1⟩
  rcases hconstruction with
    ⟨b', dims', C', Mhat, hlaw, groups, coords, merge, hmerge, hgumbel, hmergedLaw,
      representative, hrecover, locate, pi, hparents, hlatent, hpi, hcontinuous, hcategorical⟩
  refine ⟨b', dims', C', Mhat, hlaw, groups, coords, merge, hmerge, hgumbel, hmergedLaw,
    representative, hrecover, locate, pi, hparents, hlatent, hpi, hcontinuous, hcategorical,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro i d hi L hL x hx y hy
    rw [hcontinuous i d hi x hx, hcontinuous i d hi y hy]
    have h := hL.comp (hpi i).1.lipschitzOnWith (hpi i).2
    convert h hx hy using 1 <;> first | rfl | (simp only [mul_one]; rfl)
  · intro i d hi r hr
    exact (hr.comp (pi i).contDiff.contDiffOn (hpi i).2).congr (hcontinuous i d hi)
  · intro i k hi L hL x hx y hy
    rw [hcategorical i k hi x hx, hcategorical i k hi y hy]
    have h := hL.comp (hpi i).1.lipschitzOnWith (hpi i).2
    convert h hx hy using 1 <;> first | rfl | (simp only [mul_one]; rfl)
  · intro i k hi r hr
    have hs := fun x hx => (hpositive i k hi x hx).2
    exact ((canonical_normalized_contDiffOn hr hs).comp
      (pi i).contDiff.contDiffOn (hpi i).2).congr (hcategorical i k hi)
  · intro i k hi hlocal
    have hp := fun x hx => (hpositive i k hi x hx).1
    have hs := fun x hx => (hpositive i k hi x hx).2
    have hn := canonical_normalized_locally_lipschitz hp hs hlocal
    intro x hx
    obtain ⟨A, r, hr, hA⟩ := canonical_locally_lipschitz_comp (pi i)
      (hpi i).1 (hpi i).2 hn x hx
    refine ⟨A, r, hr, ?_⟩
    apply LipschitzOnWith.of_dist_le_mul
    intro y hy z hz
    rw [hcategorical i k hi y hy.2, hcategorical i k hi z hz.2]
    exact hA.dist_le_mul y hy z hz

end
end Papers.TbsNeuralCausalPi
