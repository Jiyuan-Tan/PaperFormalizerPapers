module
public import Papers.TbsNeuralCausalPi.Helpers.KantorovichCube
public import Papers.TbsNeuralCausalPi.Setup.SCM
/-! # Common independent noise in the initial approximation history

Appending the same independent noise law preserves transport cost whenever
the history encoding preserves distances on each fixed-noise slice and has a
nonexpansive latent projection. This includes the paper's one-norm encoding.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped ENNReal

-- @node: approximation_wasserstein_map_nonexpansive
/-- For [two measures](hyp:mu,nu) and [a map between their metric spaces](hyp:f),
if [the map is measurable](hyp:hf) and [never increases distances](hyp:hd), then
[the Wasserstein distance between the image measures is at most the original
Wasserstein distance](goal).

No first moment or compactness assumption is needed for this extended-valued bound. -/
lemma approximation_wasserstein_map_nonexpansive
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (mu nu : Measure X) (f : X → Y) (hf : Measurable f)
    (hd : ∀ x y, edist (f x) (f y) ≤ edist x y) :
    wasserstein1 (mu.map f) (nu.map f) ≤ wasserstein1 mu nu := by
  rw [wasserstein1_eq_couplings mu nu]
  refine le_iInf fun pi => ?_
  let := pi.property.1
  let F : X × X → Y × Y := fun z => (f z.1, f z.2)
  have hF : Measurable F := by fun_prop
  have hc : pi.val.map F ∈ couplings (mu.map f) (nu.map f) := by
    refine ⟨Measure.isProbabilityMeasure_map hF.aemeasurable, ?_, ?_⟩
    · rw [Measure.map_map measurable_fst hF]
      change pi.val.map (f ∘ Prod.fst) = _
      rw [← Measure.map_map hf measurable_fst, pi.property.2.1]
    · rw [Measure.map_map measurable_snd hF]
      change pi.val.map (f ∘ Prod.snd) = _
      rw [← Measure.map_map hf measurable_snd, pi.property.2.2]
  calc
    wasserstein1 (mu.map f) (nu.map f) ≤ ∫⁻ z, edist z.1 z.2 ∂pi.val.map F :=
      (wasserstein1_eq_couplings _ _).trans_le (iInf_le_of_le ⟨_, hc⟩ le_rfl)
    _ = ∫⁻ z, edist (f z.1) (f z.2) ∂pi.val := by
      rw [lintegral_map (by fun_prop) hF]
    _ ≤ ∫⁻ z, edist z.1 z.2 ∂pi.val := lintegral_mono fun z => hd z.1 z.2

-- @node: approximation_wasserstein_append_independent_eq
/-- For [two probability laws](hyp:mu,nu), [a common independent noise law](hyp:eta),
[an encoding of a state and noise into a metric space](hyp:encode), and [a
projection back to the state space](hyp:project), assume [the encoding is
measurable](hyp:he), [the projection is measurable](hyp:hp), [projecting an encoded
pair recovers its state](hyp:hproject), [projection never increases distances](hyp:hcontract),
and [encoding preserves distances between states with the same noise](hyp:hslice).
Then [the Wasserstein distance between the encoded state-and-noise laws equals
the Wasserstein distance between the original state laws](goal).

The equality holds even when either transport cost is infinite. -/
lemma approximation_wasserstein_append_independent_eq
    {X Y Z : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    [MeasurableSpace Y] [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    [SecondCountableTopology Z]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (eta : Measure Y) [IsProbabilityMeasure eta]
    (encode : X × Y → Z) (he : Measurable encode)
    (project : Z → X) (hp : Measurable project)
    (hproject : ∀ x y, project (encode (x, y)) = x)
    (hcontract : ∀ z w, edist (project z) (project w) ≤ edist z w)
    (hslice : ∀ x x' y, edist (encode (x, y)) (encode (x', y)) = edist x x') :
    wasserstein1 ((mu.prod eta).map encode) ((nu.prod eta).map encode) =
      wasserstein1 mu nu := by
  apply le_antisymm
  · rw [wasserstein1_eq_couplings mu nu]
    refine le_iInf fun pi => ?_
    let := pi.property.1
    let rho := pi.val.prod eta
    let F : (X × X) × Y → Z × Z :=
      fun z => (encode (z.1.1, z.2), encode (z.1.2, z.2))
    have hF : Measurable F := by fun_prop
    have hleft : rho.map (fun z => (z.1.1, z.2)) = mu.prod eta := by
      have h := (Measure.map_prod_map pi.val eta measurable_fst measurable_id).symm
      simp only [Measure.map_id, pi.property.2.1] at h
      convert h using 2
      funext z
      rcases z with ⟨x, y⟩
      exact (Prod.map_apply Prod.fst id x y).symm
    have hright : rho.map (fun z => (z.1.2, z.2)) = nu.prod eta := by
      have h := (Measure.map_prod_map pi.val eta measurable_snd measurable_id).symm
      simp only [Measure.map_id, pi.property.2.2] at h
      convert h using 2
      funext z
      rcases z with ⟨x, y⟩
      exact (Prod.map_apply Prod.snd id x y).symm
    have hc : rho.map F ∈ couplings
        ((mu.prod eta).map encode) ((nu.prod eta).map encode) := by
      refine ⟨Measure.isProbabilityMeasure_map hF.aemeasurable, ?_, ?_⟩
      · rw [Measure.map_map measurable_fst hF, ← hleft,
          Measure.map_map he (by fun_prop)]
        rfl
      · rw [Measure.map_map measurable_snd hF, ← hright,
          Measure.map_map he (by fun_prop)]
        rfl
    calc
      wasserstein1 _ _ ≤ ∫⁻ z, edist z.1 z.2 ∂rho.map F :=
        (wasserstein1_eq_couplings _ _).trans_le (iInf_le_of_le ⟨_, hc⟩ le_rfl)
      _ = ∫⁻ z, edist z.1.1 z.1.2 ∂rho := by
        rw [lintegral_map (by fun_prop) hF]
        simp only [F, hslice]
      _ = ∫⁻ z, edist z.1 z.2 ∂pi.val := by
        rw [show rho = pi.val.prod eta from rfl, lintegral_prod _ (by fun_prop)]
        simp
  · have h := approximation_wasserstein_map_nonexpansive
      ((mu.prod eta).map encode) ((nu.prod eta).map encode) project hp hcontract
    have hcomp : project ∘ encode = Prod.fst := by
      funext z
      exact hproject z.1 z.2
    simpa only [Measure.map_map hp he, hcomp, Measure.map_fst_prod,
      measure_univ, one_smul] using h

-- @node: approximation_wasserstein_common_coordinates_eq
/-- For [two probability laws on a finite real coordinate vector](hyp:mu,nu) and
[a common independent probability law on another finite coordinate vector](hyp:eta),
[concatenating the independent vectors preserves exactly the Wasserstein distance
between the first two laws when distances use the sum-of-absolute-values norm](goal).

Empty coordinate sets are allowed, and the common noise needs no moment assumption. -/
lemma approximation_wasserstein_common_coordinates_eq
    {I J : Type*} [Fintype I] [Fintype J]
    (mu nu : Measure (WithLp 1 (I → ℝ)))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (eta : Measure (WithLp 1 (J → ℝ))) [IsProbabilityMeasure eta] :
    wasserstein1
      ((mu.prod eta).map (fun z => WithLp.toLp 1 (Sum.elim z.1.ofLp z.2.ofLp)))
      ((nu.prod eta).map (fun z => WithLp.toLp 1 (Sum.elim z.1.ofLp z.2.ofLp))) =
      wasserstein1 mu nu := by
  let encode : WithLp 1 (I → ℝ) × WithLp 1 (J → ℝ) → WithLp 1 ((I ⊕ J) → ℝ) :=
    fun z => WithLp.toLp 1 (Sum.elim z.1.ofLp z.2.ofLp)
  let project : WithLp 1 ((I ⊕ J) → ℝ) → WithLp 1 (I → ℝ) :=
    fun z => WithLp.toLp 1 (fun i => z.ofLp (Sum.inl i))
  have he : Measurable encode := by
    first | fun_prop | skip
    apply Continuous.measurable
    apply (PiLp.continuous_toLp 1 _).comp
    apply continuous_pi
    intro c
    cases c <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> fun_prop
  have hp : Measurable project := by fun_prop
  apply approximation_wasserstein_append_independent_eq mu nu eta encode he project hp
  · intro x y
    rfl
  · intro z w
    simp only [project, PiLp.edist_eq_of_L1, Fintype.sum_sum_type]
    exact le_add_right le_rfl
  · intro x x' y
    simp [encode, PiLp.edist_eq_of_L1, Fintype.sum_sum_type]

-- @node: approximation_wasserstein_fixed_coordinates_eq
/-- For [two probability laws on finite real coordinate vectors](hyp:mu,nu) and
[a fixed vector of additional coordinates](hyp:fixed), [appending that same vector
to both laws preserves their Wasserstein distance under the sum-of-absolute-values
norm](goal). -/
lemma approximation_wasserstein_fixed_coordinates_eq
    {I J : Type*} [Fintype I] [Fintype J]
    (mu nu : Measure (WithLp 1 (I → ℝ)))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (fixed : WithLp 1 (J → ℝ)) :
    wasserstein1
      (mu.map (fun x => WithLp.toLp 1 (Sum.elim x.ofLp fixed.ofLp)))
      (nu.map (fun x => WithLp.toLp 1 (Sum.elim x.ofLp fixed.ofLp))) =
      wasserstein1 mu nu := by
  have h := approximation_wasserstein_common_coordinates_eq mu nu (Measure.dirac fixed)
  have hm : Measurable (fun z : WithLp 1 (I → ℝ) × WithLp 1 (J → ℝ) =>
      WithLp.toLp 1 (Sum.elim z.1.ofLp z.2.ofLp)) := by
    first | fun_prop | skip
    apply Continuous.measurable
    apply (PiLp.continuous_toLp 1 _).comp
    apply continuous_pi
    intro c
    cases c <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> fun_prop
  simpa only [Measure.prod_dirac, Measure.map_map hm measurable_prodMk_right,
    Function.comp_def] using h

-- @node: canonical_latent_wasserstein_eq_nonGumbel
/-- For [two canonical causal models with the same graph and coordinate
structure](hyp:M,Mhat), [the Wasserstein distance between their full latent laws
equals the distance between their independent non-Gumbel block laws, packed into
real vectors with the sum-of-absolute-values norm](goal). -/
lemma canonical_latent_wasserstein_eq_nonGumbel
    {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
    {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
    {C : Fin b → Set (Fin n)} (M Mhat : CanonicalSCM kind dims dag G C) :
    wasserstein1 M.latentLaw Mhat.latentLaw =
      wasserstein1
        ((Measure.pi (fun j => (M.blockLaw j : Measure (L1Vec (dims j))))).map
          (fun z => WithLp.toLp 1 (fun c : Σ j, Fin (dims j) => (z c.1).ofLp c.2)))
        ((Measure.pi (fun j => (Mhat.blockLaw j : Measure (L1Vec (dims j))))).map
          (fun z => WithLp.toLp 1 (fun c : Σ j, Fin (dims j) => (z c.1).ofLp c.2))) := by
  let pack : (∀ j, L1Vec (dims j)) → WithLp 1 ((Σ j, Fin (dims j)) → ℝ) :=
    fun z => WithLp.toLp 1 (fun c => (z c.1).ofLp c.2)
  let noisePack : ((Σ i, Fin (noiseDim (kind i))) → ℝ) →
      WithLp 1 ((Σ i, Fin (noiseDim (kind i))) → ℝ) := WithLp.toLp 1
  let eta := (Measure.pi (fun _ : Σ i, Fin (noiseDim (kind i)) => gumbelLaw)).map noisePack
  have hpack : Measurable pack := by fun_prop
  have hnoise : Measurable noisePack := by fun_prop
  let encode : WithLp 1 ((Σ j, Fin (dims j)) → ℝ) ×
      WithLp 1 ((Σ i, Fin (noiseDim (kind i))) → ℝ) → Exogenous kind dims :=
    fun z => WithLp.toLp 1 (Sum.elim z.1.ofLp z.2.ofLp)
  have hencode : Measurable encode := by
    first | fun_prop | skip
    apply Continuous.measurable
    apply (PiLp.continuous_toLp 1 _).comp
    apply continuous_pi
    intro c
    cases c <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> fun_prop
  let := gumbelLaw_probability
  let : IsProbabilityMeasure eta := Measure.isProbabilityMeasure_map hnoise.aemeasurable
  have hmap (N : CanonicalSCM kind dims dag G C) :
      N.latentLaw =
        ((((Measure.pi (fun j => (N.blockLaw j : Measure (L1Vec (dims j))))).map pack).prod eta).map
          encode) := by
    rw [show eta = _ from rfl, Measure.map_prod_map _ _ hpack hnoise,
      Measure.map_map hencode (hpack.prodMap hnoise)]
    unfold CanonicalSCM.latentLaw
    congr 1
    funext z
    apply WithLp.ofLp_injective
    funext c
    cases c <;> rfl
  let (N : CanonicalSCM kind dims dag G C) :
      IsProbabilityMeasure ((Measure.pi (fun j => (N.blockLaw j : Measure (L1Vec (dims j))))).map pack) :=
    Measure.isProbabilityMeasure_map hpack.aemeasurable
  rw [hmap M, hmap Mhat]
  exact approximation_wasserstein_common_coordinates_eq
    _ _ eta

end Papers.TbsNeuralCausalPi
