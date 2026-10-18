module
public import Papers.TbsNeuralCausalPi.Helpers.CanonicalTransport
public import Mathlib.Probability.Independence.ZeroOne
public import Mathlib.MeasureTheory.Measure.Typeclasses.ZeroOne
public import Mathlib.Probability.ProductMeasure
/-! # Latent laws used in canonical regrouping

Independence factors the original joint block law. Blocks independent of
themselves have Dirac marginals, so copying them preserves their joint law.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
noncomputable section

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}

-- @node: canonical_self_independent_block_dirac
/-- If [a latent block is independent of itself](hyp:hj), then [its marginal law is concentrated at a single vector](goal). -/
lemma canonical_self_independent_block_dirac (M : EuclideanSCM kind dims)
    (j : Fin b) (hj : IndepFun (blockProjection j) (blockProjection j) M.latentLaw) :
    ∃ a : L1Vec (dims j), M.latentLaw.map (blockProjection j) = Measure.dirac a := by
  let := M.probability
  have hm : Measurable (blockProjection (kind := kind) (dims := dims) j) := by
    first | fun_prop | fun_prop [blockProjection]
  let : IsProbabilityMeasure (M.latentLaw.map (blockProjection j)) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  let : IsZeroOneMeasure (M.latentLaw.map (blockProjection j)) := ⟨by
    intro s hs
    rw [Measure.map_apply hm hs]
    exact measure_eq_zero_or_one_of_indepSet_self ((indepFun_iff_indepSet_preimage hm hm).mp hj s s hs hs)⟩
  exact IsZeroOneMeasure.exists_eq_dirac

-- @node: canonical_self_independent_block_ae_const
/-- If [a latent block is independent of itself](hyp:hj), then [it equals a fixed vector almost surely under the model's latent law](goal). -/
lemma canonical_self_independent_block_ae_const (M : EuclideanSCM kind dims)
    (j : Fin b) (hj : IndepFun (blockProjection j) (blockProjection j) M.latentLaw) :
    ∃ a : L1Vec (dims j), ∀ᵐ u ∂M.latentLaw, blockProjection j u = a := by
  obtain ⟨a, ha⟩ := canonical_self_independent_block_dirac M j hj
  have hm : Measurable (blockProjection (kind := kind) (dims := dims) j) := by
    first | fun_prop | fun_prop [blockProjection]
  refine ⟨a, ?_⟩
  have h : ∀ᵐ x ∂M.latentLaw.map (blockProjection j), x = a := by
    rw [ha]
    simp
  exact (ae_map_iff hm.aemeasurable (measurableSet_singleton a)).mp h

/-- If [a family of random variables is jointly independent](hyp:hX), [each variable is measurable](hyp:hm), and [every variable whose index belongs to both of two finite index sets is almost surely constant](hyp:hc), then [the tuples indexed by those two sets are independent](goal). -/
-- @node: canonical_indepFun_overlapping_finsets
lemma canonical_indepFun_overlapping_finsets
    {Ω I : Type*} [MeasurableSpace Ω] [DecidableEq I]
    {β : I → Type*} [∀ i, MeasurableSpace (β i)] {μ : Measure Ω}
    {X : ∀ i, Ω → β i} (hX : iIndepFun X μ) (hm : ∀ i, Measurable (X i))
    (S T : Finset I)
    (hc : ∀ i ∈ S ∩ T, ∃ a, ∀ᵐ ω ∂μ, X i ω = a) :
    IndepFun (fun ω (i : S) => X i ω) (fun ω (i : T) => X i ω) μ := by
  classical
  choose a ha using fun i : (S ∩ T : Finset I) => hc i i.property
  let restore : (∀ i : (T \ S : Finset I), β i) → ∀ i : T, β i := fun z i =>
    if hi : i.val ∈ S then a ⟨i, Finset.mem_inter.mpr ⟨hi, i.property⟩⟩
    else z ⟨i, Finset.mem_sdiff.mpr ⟨i.property, hi⟩⟩
  have hr : Measurable restore := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : i.val ∈ S
    · simp only [restore, dif_pos hi]
      fun_prop
    · simp only [restore, dif_neg hi]
      fun_prop
  have hind := hX.indepFun_finset S (T \ S) Finset.disjoint_sdiff hm
  have hind' := hind.comp measurable_id hr
  apply hind'.congr (Filter.Eventually.of_forall (fun _ => rfl))
  have hall : ∀ᵐ ω ∂μ, ∀ i : (S ∩ T : Finset I), X i ω = a i :=
    (ae_all_iff).mpr ha
  filter_upwards [hall] with ω hω
  funext i
  dsimp only [Function.comp_apply, id_eq, restore]
  split_ifs with hi
  · exact (hω ⟨i, Finset.mem_inter.mpr ⟨hi, i.property⟩⟩).symm
  · rfl

/-- If [a family of random variables is jointly independent](hyp:hX), [each variable is measurable](hyp:hm), and [every variable shared by two distinct finite index groups is almost surely constant](hyp:hc), then [the entire family of grouped tuples is jointly independent](goal). -/
-- @node: canonical_iIndepFun_overlapping_groups
lemma canonical_iIndepFun_overlapping_groups
    {Ω I J : Type*} [MeasurableSpace Ω] [DecidableEq I]
    {β : I → Type*} [∀ i, MeasurableSpace (β i)] {μ : Measure Ω}
    {X : ∀ i, Ω → β i} (hX : iIndepFun X μ) (hm : ∀ i, Measurable (X i))
    (groups : J → Finset I)
    (hc : ∀ c d i, i ∈ groups c → i ∈ groups d → c ≠ d →
      ∃ a, ∀ᵐ ω ∂μ, X i ω = a) :
    iIndepFun (fun c ω (i : groups c) => X i ω) μ := by
  classical
  let := hX.isProbabilityMeasure
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro s sets hsets
  induction s using Finset.induction_on with
  | empty => simp
  | @insert c s hcs ih =>
    let U := s.biUnion groups
    let B : Set (∀ i : U, β i) := {z | ∀ d : s,
      (fun i : groups d => z ⟨i, Finset.mem_biUnion.mpr ⟨d, d.property, i.property⟩⟩) ∈ sets d}
    have hB : MeasurableSet B := by
      simp only [B, Set.ofPred_forall]
      apply MeasurableSet.iInter
      intro d
      apply (hsets d (Finset.mem_insert_of_mem d.property)).preimage
      fun_prop
    have hcU : ∀ i ∈ groups c ∩ U, ∃ a, ∀ᵐ ω ∂μ, X i ω = a := by
      intro i hi
      obtain ⟨hic, hiU⟩ := Finset.mem_inter.mp hi
      obtain ⟨d, hds, hid⟩ := Finset.mem_biUnion.mp hiU
      exact hc c d i hic hid (fun h => hcs (h ▸ hds))
    have hind := canonical_indepFun_overlapping_finsets hX hm (groups c) U hcU
    have hpre : (fun ω (i : U) => X i ω) ⁻¹' B =
        ⋂ d ∈ s, (fun ω (i : groups d) => X i ω) ⁻¹' sets d := by
      ext ω
      simp [B]
    have hstep := hind.measure_inter_preimage_eq_mul (sets c) B
      (hsets c (Finset.mem_insert_self c s)) hB
    rw [hpre] at hstep
    have hins : (⋂ i ∈ insert c s, (fun ω (j : groups i) => X j ω) ⁻¹' sets i) =
        (fun ω (j : groups c) => X j ω) ⁻¹' sets c ∩
          ⋂ i ∈ s, (fun ω (j : groups i) => X j ω) ⁻¹' sets i := by
      ext ω
      simp
    rw [hins, hstep, Finset.prod_insert hcs,
      ih (fun d hd => hsets d (Finset.mem_insert_of_mem hd))]

/-- Suppose [the model's named latent blocks are jointly independent](hyp:hind), and [each new block's coordinates are in bijection with the coordinates of the original blocks assigned to its group](hyp:coords). If [the regrouping map copies those block coordinates according to these bijections](hyp:hm), [preserves all intrinsic node-noise coordinates](hyp:hg), and [every original block shared by distinct groups is independent of itself](hyp:hoverlap), then [all regrouped named latent blocks, including the intrinsic noises, are jointly independent under the original latent law](goal). -/
-- @node: canonical_regrouped_named_latents_independent
lemma canonical_regrouped_named_latents_independent (M : EuclideanSCM kind dims)
    (hind : LatentBlocksIndependent M) {b' : ℕ} {dims' : Fin b' → ℕ}
    (groups : Fin b' → Finset (Fin b))
    (coords : ∀ c, Fin (dims' c) ≃ (Σ j : {j // j ∈ groups c}, Fin (dims j)))
    (merge : Exogenous kind dims → Exogenous kind dims')
    (hm : ∀ u c k, (merge u).ofLp (.inl ⟨c,k⟩) =
      u.ofLp (.inl ⟨(coords c k).1.val, (coords c k).2⟩))
    (hg : ∀ u i k, (merge u).ofLp (.inr ⟨i,k⟩) = u.ofLp (.inr ⟨i,k⟩))
    (hoverlap : ∀ c d j, j ∈ groups c → j ∈ groups d → c ≠ d →
      IndepFun (blockProjection j) (blockProjection j) M.latentLaw) :
    iIndepFun (fun j u => exogenousProjection kind dims' j (merge u)) M.latentLaw := by
  classical
  let H : Fin b' ⊕ Fin n → Finset (Fin b ⊕ Fin n) := fun j => match j with
    | .inl c => (groups c).image Sum.inl
    | .inr i => {Sum.inr i}
  have hmeas (j : Fin b ⊕ Fin n) : Measurable (namedLatent M j) := by
    cases j <;> first | fun_prop | fun_prop [namedLatent, blockProjection, categoricalNoise]
  have hdup : ∀ c d j, j ∈ H c → j ∈ H d → c ≠ d →
      ∃ a, ∀ᵐ u ∂M.latentLaw, namedLatent M j u = a := by
    intro c d j hjc hjd hcd
    cases c with
    | inl c =>
      cases d with
      | inl d =>
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hjc
        have hj' : j ∈ groups d := by simpa [H] using hjd
        exact canonical_self_independent_block_ae_const M j
          (hoverlap c d j hj hj' (fun h => hcd (congrArg Sum.inl h)))
      | inr d =>
        have he : j = Sum.inr d := Finset.mem_singleton.mp hjd
        subst j
        simp [H] at hjc
    | inr c =>
      have he : j = Sum.inr c := Finset.mem_singleton.mp hjc
      subst j
      cases d with
      | inl d => simp [H] at hjd
      | inr d =>
        have he : c = d := by simpa [H] using hjd
        exact (hcd (congrArg Sum.inr he)).elim
  have hgroup := canonical_iIndepFun_overlapping_groups hind hmeas H hdup
  let flatten : ∀ j : Fin b' ⊕ Fin n,
      (∀ a : H j, L1Vec (fullLatentDim kind dims a)) →
        L1Vec (latentBlockDim kind dims' j) := fun j => match j with
    | .inl c => fun z => WithLp.toLp 1 (fun k =>
        (z ⟨Sum.inl (coords c k).1.val,
          Finset.mem_image.mpr ⟨(coords c k).1.val, (coords c k).1.property, rfl⟩⟩).ofLp
            (coords c k).2)
    | .inr i => fun z => z ⟨Sum.inr i, Finset.mem_singleton_self _⟩
  have hf : ∀ j, Measurable (flatten j) := by
    intro j
    cases j with
    | inl c =>
      apply scm_toLp_measurable.comp
      apply measurable_pi_lambda
      intro k
      exact (measurable_pi_apply _).comp
        (scm_ofLp_measurable.comp (measurable_pi_apply _))
    | inr i => exact measurable_pi_apply _
  have hflat := hgroup.comp flatten hf
  convert hflat using 1
  funext j u
  cases j with
  | inl c =>
    apply WithLp.ofLp_injective
    funext k
    exact hm u c k
  | inr i =>
    apply WithLp.ofLp_injective
    funext k
    exact hg u i k

-- @node: canonical_original_noise_coordinates_law
/-- If [the model's categorical mechanisms use Gumbel argmax generation with the given weights](hyp:hcat), then [each node's intrinsic noise coordinates have the corresponding product standard Gumbel law](goal). -/
lemma canonical_original_noise_coordinates_law (M : EuclideanSCM kind dims)
    (p : MechanismWeights M) (hcat : CategoricalGumbelArgmax M p) (i : Fin n) :
    M.latentLaw.map (fun u => (categoricalNoise i u).ofLp) =
      gumbelInputs (noiseDim (kind i)) := by
  let := M.probability
  by_cases hzero : noiseDim (kind i) = 0
  · have he : (fun u : Exogenous kind dims => (categoricalNoise i u).ofLp) =
        (fun _ => (0 : Fin (noiseDim (kind i)) → ℝ)) := by
      funext u k
      exact (Nat.not_lt_zero k.val (hzero ▸ k.isLt)).elim
    rw [he, Measure.map_const, measure_univ, one_smul]
    unfold gumbelInputs
    have : IsEmpty (Fin (noiseDim (kind i))) := by rw [hzero]; infer_instance
    exact (Measure.pi_of_empty _ 0).symm
  · obtain ⟨k, hi⟩ : ∃ k, kind i = Sum.inr k := by
      cases hi : kind i with
      | inl d => exact (hzero (by simp [hi, noiseDim])).elim
      | inr k => exact ⟨k, rfl⟩
    have h := hcat.2.2.2 i k hi
    have hsize : noiseDim (kind i) = k := congrArg noiseDim hi
    subst k
    have he : (fun u : Exogenous kind dims => (categoricalNoise i u).ofLp ∘
        Fin.cast (congrArg noiseDim hi).symm) =
        (fun u => (categoricalNoise i u).ofLp) := by
      funext u j
      apply congrArg ((categoricalNoise i u).ofLp)
      exact Fin.ext rfl
    rw [he] at h
    exact h

-- @node: canonical_original_noise_law
/-- If [the model's categorical mechanisms use Gumbel argmax generation with the given weights](hyp:hcat), then [each node's intrinsic noise vector has the law obtained by packing independent standard Gumbel draws into a vector of its noise dimension](goal). -/
lemma canonical_original_noise_law (M : EuclideanSCM kind dims)
    (p : MechanismWeights M) (hcat : CategoricalGumbelArgmax M p) (i : Fin n) :
    M.latentLaw.map (categoricalNoise i) =
      (gumbelInputs (noiseDim (kind i))).map (WithLp.toLp 1) := by
  rw [← canonical_original_noise_coordinates_law M p hcat i,
    Measure.map_map scm_toLp_measurable (show Measurable
      (fun u : Exogenous kind dims => (categoricalNoise i u).ofLp) from
      scm_ofLp_measurable.comp (by fun_prop))]
  rfl

/-- [Packing independent scalar standard Gumbel draws into nodewise vectors gives exactly the product of the nodewise Gumbel-vector laws, including empty noise vectors at continuous nodes](goal). -/
-- @node: canonical_gumbel_vector_product_law
lemma canonical_gumbel_vector_product_law :
    (Measure.pi (fun _ : Σ i, Fin (noiseDim (kind i)) => gumbelLaw)).map
      (fun g i => WithLp.toLp 1 (fun k => g ⟨i,k⟩)) =
    Measure.pi (fun i => (gumbelInputs (noiseDim (kind i))).map (WithLp.toLp 1)) := by
  let := gumbelLaw_probability
  have h := Measure.infinitePi_map_piCurry (fun (i : Fin n) (_ : Fin (noiseDim (kind i))) => gumbelLaw)
  simp only [Measure.infinitePi_eq_pi] at h
  have hm : Measurable (fun z : ∀ i, Fin (noiseDim (kind i)) → ℝ =>
      fun i => WithLp.toLp 1 (z i)) := by fun_prop
  have h' := congrArg (fun μ => μ.map (fun z : ∀ i, Fin (noiseDim (kind i)) → ℝ =>
      fun i => WithLp.toLp 1 (z i))) h
  rw [Measure.map_map hm (MeasurableEquiv.piCurry _).measurable,
    Measure.pi_map_pi (fun _ => scm_toLp_measurable.aemeasurable)] at h'
  exact h'

/-- For an exogenous random vector [that is measurable](hyp:hZ) and [whose named latent blocks are jointly independent](hyp:hind), [the joint law of its non-Gumbel blocks and intrinsic node noises equals the product of the block marginal laws and the node-noise marginal laws](goal). -/
-- @node: canonical_independent_named_latents_joint_law
lemma canonical_independent_named_latents_joint_law
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → Exogenous kind dims) (hZ : Measurable Z)
    (hind : iIndepFun (fun j ω => exogenousProjection kind dims j (Z ω)) μ) :
    μ.map (fun ω => (fun j => blockProjection j (Z ω), fun i => categoricalNoise i (Z ω))) =
      (Measure.pi (fun j => μ.map (fun ω => blockProjection j (Z ω)))).prod
        (Measure.pi (fun i => μ.map (fun ω => categoricalNoise i (Z ω)))) := by
  have hm (j : Fin b ⊕ Fin n) :
      Measurable (fun ω => exogenousProjection kind dims j (Z ω)) := by
    cases j <;> first | fun_prop | fun_prop [exogenousProjection, blockProjection, categoricalNoise]
  let ν := fun j => μ.map (fun ω => exogenousProjection kind dims j (Z ω))
  let (j : Fin b ⊕ Fin n) : IsProbabilityMeasure (ν j) :=
    Measure.isProbabilityMeasure_map (hm j).aemeasurable
  have h := hind.map_fun_eq_pi_map (fun j => (hm j).aemeasurable)
  let e := MeasurableEquiv.sumPiEquivProdPi (fun j => L1Vec (latentBlockDim kind dims j))
  calc
    _ = (μ.map (fun ω j => exogenousProjection kind dims j (Z ω))).map e := by
      rw [Measure.map_map e.measurable (by fun_prop)]
      rfl
    _ = _ := by
      rw [h]
      exact (measurePreserving_sumPiEquivProdPi ν).map_eq

/-- Suppose [the original named latent blocks are jointly independent](hyp:hind) and [the original categorical mechanisms use Gumbel argmax generation with the given weights](hyp:hcat). Given [bijections from each new block's coordinates to the original coordinates in its group](hyp:coords), assume [the regrouping map is measurable](hyp:hmerge), [copies block coordinates according to these bijections](hyp:hm), [preserves intrinsic node-noise coordinates](hyp:hg), and [shares between distinct groups only blocks independent of themselves](hyp:hoverlap); if [each canonical block law is the corresponding regrouped marginal of the original latent law](hyp:hblock), then [the canonical latent law is exactly the original latent law transported by the regrouping map](goal). -/
-- @node: canonical_regrouped_latent_law
lemma canonical_regrouped_latent_law (M : EuclideanSCM kind dims)
    (p : MechanismWeights M) (hind : LatentBlocksIndependent M)
    (hcat : CategoricalGumbelArgmax M p) {b' : ℕ} {dims' : Fin b' → ℕ}
    (groups : Fin b' → Finset (Fin b))
    (coords : ∀ c, Fin (dims' c) ≃ (Σ j : {j // j ∈ groups c}, Fin (dims j)))
    (merge : Exogenous kind dims → Exogenous kind dims') (hmerge : Measurable merge)
    (hm : ∀ u c k, (merge u).ofLp (.inl ⟨c,k⟩) =
      u.ofLp (.inl ⟨(coords c k).1.val, (coords c k).2⟩))
    (hg : ∀ u i k, (merge u).ofLp (.inr ⟨i,k⟩) = u.ofLp (.inr ⟨i,k⟩))
    (hoverlap : ∀ c d j, j ∈ groups c → j ∈ groups d → c ≠ d →
      IndepFun (blockProjection j) (blockProjection j) M.latentLaw)
    {C : Fin b' → Set (Fin n)} (N : CanonicalSCM kind dims' M.dag (causalGraph M).2 C)
    (hblock : ∀ c, (N.blockLaw c : Measure (L1Vec (dims' c))) =
      M.latentLaw.map (fun u => blockProjection c (merge u))) :
    N.latentLaw = M.latentLaw.map merge := by
  let := M.probability
  let := gumbelLaw_probability
  have hi := canonical_regrouped_named_latents_independent M hind groups coords merge hm hg hoverlap
  have hsplit := canonical_independent_named_latents_joint_law M.latentLaw merge hmerge hi
  have hn (i : Fin n) : M.latentLaw.map (fun u => categoricalNoise i (merge u)) =
      (gumbelInputs (noiseDim (kind i))).map (WithLp.toLp 1) := by
    have he : (fun u => categoricalNoise i (merge u)) = categoricalNoise i :=
      funext (canonical_regrouping_categoricalNoise merge hg i)
    rw [he]
    exact canonical_original_noise_law M p hcat i
  simp_rw [← hblock, hn] at hsplit
  let B := Measure.pi (fun j => (N.blockLaw j : Measure (L1Vec (dims' j))))
  let A := Measure.pi (fun _ : Σ i, Fin (noiseDim (kind i)) => gumbelLaw)
  let pack : (∀ j, L1Vec (dims' j)) × (∀ i, L1Vec (noiseDim (kind i))) →
      Exogenous kind dims' := fun z => WithLp.toLp 1 (fun q => match q with
        | .inl ⟨j,k⟩ => (z.1 j).ofLp k
        | .inr ⟨i,k⟩ => (z.2 i).ofLp k)
  have hpack : Measurable pack := by
    apply scm_toLp_measurable.comp
    apply measurable_pi_lambda
    rintro (⟨j,k⟩ | ⟨i,k⟩) <;> dsimp [pack] <;> fun_prop
  let wrap := fun g : (Σ i, Fin (noiseDim (kind i))) → ℝ =>
    fun i => WithLp.toLp 1 (fun k => g ⟨i,k⟩)
  have hwrap : Measurable wrap := by fun_prop
  have hprod := Measure.map_prod_map B A measurable_id hwrap
  rw [Measure.map_id, canonical_gumbel_vector_product_law] at hprod
  calc
    N.latentLaw = (B.prod (Measure.pi (fun i =>
        (gumbelInputs (noiseDim (kind i))).map (WithLp.toLp 1)))).map pack := by
      rw [hprod, Measure.map_map hpack (measurable_id.prodMap hwrap)]
      unfold CanonicalSCM.latentLaw
      congr 1
      funext z
      apply WithLp.ofLp_injective
      funext q
      rcases q with ⟨j,k⟩ | ⟨i,k⟩ <;> rfl
    _ = (M.latentLaw.map (fun u =>
        (fun j => blockProjection j (merge u), fun i => categoricalNoise i (merge u)))).map pack := by
      rw [hsplit]
    _ = M.latentLaw.map merge := by
      rw [Measure.map_map hpack (by
        first | fun_prop | fun_prop [blockProjection, categoricalNoise])]
      congr 1
      funext u
      apply WithLp.ofLp_injective
      funext q
      rcases q with ⟨j,k⟩ | ⟨i,k⟩ <;> rfl

end
end Papers.TbsNeuralCausalPi
