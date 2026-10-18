module
public import Papers.TbsNeuralCausalPi.Helpers.ApproximationLatents
public import Papers.TbsNeuralCausalPi.Helpers.ApproximationStep
public import Papers.TbsNeuralCausalPi.Helpers.CategoricalCoupling
public import Mathlib.Probability.Kernel.Composition.MeasureComp
/-! # Transport through continuous and categorical history extensions

Push arbitrary history couplings through the two mechanisms. The source laws
need only be concentrated on the domain where the cross-history estimate holds;
no compactness or finite first moments are required.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped NNReal ENNReal

-- @node: approximation_wasserstein_bind_cross_bound_on
/-- If [the first history law is concentrated on S](hyp:hmu), [the second is
concentrated on T](hyp:hnu), and [the transition coupling has the prescribed
conditional marginals at every pair of histories](hyp:hR), then, for [a finite
nonnegative propagation coefficient A](hyp:A) and [a possibly infinite
nonnegative error E](hyp:E), [an expected transition distance bounded by A times
the history distance plus E on S and T](hyp:hcost) implies [that the Wasserstein
distance between the updated laws is at most A times their original Wasserstein
distance plus E](goal). -/
lemma approximation_wasserstein_bind_cross_bound_on
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (S T : Set X) (hmu : ∀ᵐ x ∂mu, x ∈ S) (hnu : ∀ᵐ x ∂nu, x ∈ T)
    (kappa eta : ProbabilityTheory.Kernel X Y)
    (R : ProbabilityTheory.Kernel (X × X) (Y × Y))
    (hR : ∀ z, R z ∈ couplings (kappa z.1) (eta z.2))
    (A : ℝ≥0) (E : ℝ≥0∞)
    (hcost : ∀ z, z.1 ∈ S → z.2 ∈ T → (∫⁻ w, edist w.1 w.2 ∂R z) ≤
      (A : ℝ≥0∞) * edist z.1 z.2 + E) :
    wasserstein1 (mu.bind kappa) (nu.bind eta) ≤
      (A : ℝ≥0∞) * wasserstein1 mu nu + E := by
  have hp : mu.prod nu ∈ couplings mu nu := by
    refine ⟨inferInstance, ?_, ?_⟩ <;> simp
  let : Nonempty (couplings mu nu) := ⟨⟨_, hp⟩⟩
  have : ProbabilityTheory.IsMarkovKernel R := ⟨fun z => (hR z).1⟩
  rw [wasserstein1_eq_couplings mu nu, ENNReal.mul_iInf (by simp), ENNReal.iInf_add]
  refine le_iInf fun pi => ?_
  let := pi.property.1
  have hleft : (pi.val.bind R).map Prod.fst = mu.bind kappa := by
    ext s hs
    rw [Measure.map_apply measurable_fst hs,
      Measure.bind_apply (measurable_fst hs) R.aemeasurable,
      Measure.bind_apply hs kappa.aemeasurable]
    calc
      (∫⁻ z, R z (Prod.fst ⁻¹' s) ∂pi.val) =
          ∫⁻ z, kappa z.1 s ∂pi.val := by
        apply lintegral_congr
        intro z
        rw [← Measure.map_apply measurable_fst hs, (hR z).2.1]
      _ = ∫⁻ x, kappa x s ∂mu := by
        have hm := lintegral_map (μ := pi.val) (kappa.measurable_coe hs) measurable_fst
        rw [pi.property.2.1] at hm
        exact hm.symm
  have hright : (pi.val.bind R).map Prod.snd = nu.bind eta := by
    ext s hs
    rw [Measure.map_apply measurable_snd hs,
      Measure.bind_apply (measurable_snd hs) R.aemeasurable,
      Measure.bind_apply hs eta.aemeasurable]
    calc
      (∫⁻ z, R z (Prod.snd ⁻¹' s) ∂pi.val) =
          ∫⁻ z, eta z.2 s ∂pi.val := by
        apply lintegral_congr
        intro z
        rw [← Measure.map_apply measurable_snd hs, (hR z).2.2]
      _ = ∫⁻ x, eta x s ∂nu := by
        have hm := lintegral_map (μ := pi.val) (eta.measurable_coe hs) measurable_snd
        rw [pi.property.2.2] at hm
        exact hm.symm
  have hc : pi.val.bind R ∈ couplings (mu.bind kappa) (nu.bind eta) :=
    ⟨inferInstance, hleft, hright⟩
  calc
    wasserstein1 (mu.bind kappa) (nu.bind eta) ≤
        ∫⁻ w, edist w.1 w.2 ∂pi.val.bind R :=
      (wasserstein1_eq_couplings _ _).trans_le (iInf_le_of_le ⟨_, hc⟩ le_rfl)
    _ = ∫⁻ z, ∫⁻ w, edist w.1 w.2 ∂R z ∂pi.val :=
      Measure.lintegral_bind R.aemeasurable (by fun_prop)
    _ ≤ ∫⁻ z : X × X, (A : ℝ≥0∞) * edist z.1 z.2 + E ∂pi.val := by
      have hleft : ∀ᵐ z ∂pi.val, z.1 ∈ S := by
        apply ae_of_ae_map measurable_fst.aemeasurable
        rw [pi.property.2.1]
        exact hmu
      have hright : ∀ᵐ z ∂pi.val, z.2 ∈ T := by
        apply ae_of_ae_map measurable_snd.aemeasurable
        rw [pi.property.2.2]
        exact hnu
      apply lintegral_mono_ae
      filter_upwards [hleft, hright] with z hz hz'
      exact hcost z hz hz'
    _ = (A : ℝ≥0∞) * (∫⁻ z, edist z.1 z.2 ∂pi.val) + E := by
      rw [lintegral_add_left (by fun_prop), lintegral_const_mul _ (by fun_prop)]
      simp

-- @node: approximation_wasserstein_bind_cross_bound
/-- If [the transition coupling has the prescribed conditional marginals at
every pair of histories](hyp:hR), then, for [a finite nonnegative coefficient
A](hyp:A) and [a possibly infinite nonnegative error E](hyp:E), [an expected
transition distance bounded everywhere by A times the history distance plus
E](hyp:hcost) implies [that the Wasserstein distance between the updated laws is
at most A times the original Wasserstein distance plus E](goal). -/
lemma approximation_wasserstein_bind_cross_bound
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (kappa eta : ProbabilityTheory.Kernel X Y)
    (R : ProbabilityTheory.Kernel (X × X) (Y × Y))
    (hR : ∀ z, R z ∈ couplings (kappa z.1) (eta z.2))
    (A : ℝ≥0) (E : ℝ≥0∞)
    (hcost : ∀ z, (∫⁻ w, edist w.1 w.2 ∂R z) ≤
      (A : ℝ≥0∞) * edist z.1 z.2 + E) :
    wasserstein1 (mu.bind kappa) (nu.bind eta) ≤
      (A : ℝ≥0∞) * wasserstein1 mu nu + E := by
  exact approximation_wasserstein_bind_cross_bound_on mu nu Set.univ Set.univ
    (Filter.Eventually.of_forall (fun _ => Set.mem_univ _))
    (Filter.Eventually.of_forall (fun _ => Set.mem_univ _))
    kappa eta R hR A E (fun z _ _ => hcost z)

-- @node: approximation_kernel_history_uniform_bound
/-- Suppose [the first sequence of laws evolves through its transition
kernels](hyp:hmu), [the second sequence does likewise](hyp:hnu), and [each
transition coupling has the corresponding conditional marginals](hyp:hR).
For [nonnegative propagation and error coefficients A and B](hyp:A,B) and
[a possibly infinite nonnegative error scale S](hyp:S), if [A is at least
one](hyp:hA), [each expected transition distance is at most A times the current
distance plus B times S](hyp:hcost), and [the time m does not exceed the horizon
N](hyp:hm), then [the Wasserstein distance at time m is bounded by the finite
geometric propagation constant for A, B, and N times the sum of S and the
initial Wasserstein distance](goal). -/
lemma approximation_kernel_history_uniform_bound
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    (mu nu : ℕ → Measure X)
    [∀ r, IsProbabilityMeasure (mu r)] [∀ r, IsProbabilityMeasure (nu r)]
    (kappa eta : ℕ → ProbabilityTheory.Kernel X X)
    (hmu : ∀ r, mu (r + 1) = (mu r).bind (kappa r))
    (hnu : ∀ r, nu (r + 1) = (nu r).bind (eta r))
    (R : ℕ → ProbabilityTheory.Kernel (X × X) (X × X))
    (hR : ∀ r z, R r z ∈ couplings (kappa r z.1) (eta r z.2))
    (A B : ℝ≥0) (S : ℝ≥0∞) (hA : 1 ≤ A)
    (hcost : ∀ r z, (∫⁻ w, edist w.1 w.2 ∂R r z) ≤
      (A : ℝ≥0∞) * edist z.1 z.2 + (B : ℝ≥0∞) * S)
    {m N : ℕ} (hm : m ≤ N) :
    wasserstein1 (mu m) (nu m) ≤
      (approximationPropagationConstant A B N : ℝ≥0∞) *
        (S + wasserstein1 (mu 0) (nu 0)) := by
  apply approximation_history_uniform_bound
    (fun r => wasserstein1 (mu r) (nu r)) A B S hA _ hm
  intro r
  rw [hmu r, hnu r]
  exact approximation_wasserstein_bind_cross_bound (mu r) (nu r)
    (kappa r) (eta r) (R r) (hR r) A ((B : ℝ≥0∞) * S) (hcost r)

-- @node: approximation_wasserstein_map_cross_bound
/-- Suppose [the first law is concentrated on S](hyp:hmu), [the second law is
concentrated on T](hyp:hnu), and [both maps are measurable](hyp:hf,hg).
For [a finite nonnegative coefficient A](hyp:A) and
[a possibly infinite nonnegative error E](hyp:E), if [the distance between the
two outputs at histories in S and T is at most A times the history distance
plus E](hyp:hcross), then [the Wasserstein distance between the two image laws
is at most A times the original Wasserstein distance plus E](goal). -/
lemma approximation_wasserstein_map_cross_bound
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (S T : Set X) (hmu : ∀ᵐ x ∂mu, x ∈ S) (hnu : ∀ᵐ x ∂nu, x ∈ T)
    (f g : X → Y) (hf : Measurable f) (hg : Measurable g)
    (A : ℝ≥0) (E : ℝ≥0∞)
    (hcross : ∀ x ∈ S, ∀ y ∈ T, edist (f x) (g y) ≤ (A : ℝ≥0∞) * edist x y + E) :
    wasserstein1 (mu.map f) (nu.map g) ≤ (A : ℝ≥0∞) * wasserstein1 mu nu + E := by
  have hp : mu.prod nu ∈ couplings mu nu := by
    refine ⟨inferInstance, ?_, ?_⟩ <;> simp
  let : Nonempty (couplings mu nu) := ⟨⟨_, hp⟩⟩
  rw [wasserstein1_eq_couplings mu nu, ENNReal.mul_iInf (by simp), ENNReal.iInf_add]
  refine le_iInf fun pi => ?_
  let := pi.property.1
  let F : X × X → Y × Y := fun z => (f z.1, g z.2)
  have hF : Measurable F := by fun_prop
  have hc : pi.val.map F ∈ couplings (mu.map f) (nu.map g) := by
    refine ⟨Measure.isProbabilityMeasure_map hF.aemeasurable, ?_, ?_⟩
    · rw [Measure.map_map measurable_fst hF]
      change pi.val.map (f ∘ Prod.fst) = _
      rw [← Measure.map_map hf measurable_fst, pi.property.2.1]
    · rw [Measure.map_map measurable_snd hF]
      change pi.val.map (g ∘ Prod.snd) = _
      rw [← Measure.map_map hg measurable_snd, pi.property.2.2]
  have hleft : ∀ᵐ z ∂pi.val, z.1 ∈ S := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    rw [pi.property.2.1]
    exact hmu
  have hright : ∀ᵐ z ∂pi.val, z.2 ∈ T := by
    apply ae_of_ae_map measurable_snd.aemeasurable
    rw [pi.property.2.2]
    exact hnu
  calc
    wasserstein1 (mu.map f) (nu.map g) ≤ ∫⁻ z, edist z.1 z.2 ∂pi.val.map F :=
      (wasserstein1_eq_couplings _ _).trans_le (iInf_le_of_le ⟨_, hc⟩ le_rfl)
    _ = ∫⁻ z, edist (f z.1) (g z.2) ∂pi.val := by
      rw [lintegral_map (by fun_prop) hF]
    _ ≤ ∫⁻ z : X × X, (A : ℝ≥0∞) * edist z.1 z.2 + E ∂pi.val := by
      apply lintegral_mono_ae
      filter_upwards [hleft, hright] with z hz hz'
      exact hcross z.1 hz z.2 hz'
    _ = (A : ℝ≥0∞) * (∫⁻ z, edist z.1 z.2 ∂pi.val) + E := by
      rw [lintegral_add_left (by fun_prop), lintegral_const_mul _ (by fun_prop)]
      simp

-- @node: approximation_wasserstein_map_perturbation_le
/-- Suppose [the first law is concentrated on S](hyp:hmu), [the second is also
concentrated on S](hyp:hnu), and [both the true and comparison maps are
measurable](hyp:hf,hg). For [a nonnegative coefficient A](hyp:A), if
[the true map is A-Lipschitz on S](hyp:hLip), and for [a possibly infinite
nonnegative error E](hyp:E), if [the distance between the maps is at most E
at every point of S](hyp:herror), then [the Wasserstein distance between the image
laws is at most A times the original Wasserstein distance plus E](goal). -/
lemma approximation_wasserstein_map_perturbation_le
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (S : Set X) (hmu : ∀ᵐ x ∂mu, x ∈ S) (hnu : ∀ᵐ x ∂nu, x ∈ S)
    (f g : X → Y) (hf : Measurable f) (hg : Measurable g)
    (A : ℝ≥0) (hLip : LipschitzOnWith A f S) (E : ℝ≥0∞)
    (herror : ∀ y ∈ S, edist (f y) (g y) ≤ E) :
    wasserstein1 (mu.map f) (nu.map g) ≤ (A : ℝ≥0∞) * wasserstein1 mu nu + E := by
  apply approximation_wasserstein_map_cross_bound mu nu S S hmu hnu f g hf hg A E
  intro x hx y hy
  calc
    edist (f x) (g y) ≤ edist (f x) (f y) + edist (f y) (g y) := edist_triangle _ _ _
    _ ≤ (A : ℝ≥0∞) * edist x y + E :=
      add_le_add (hLip hx hy) (herror y hy)

-- @node: approximation_edist_le_dim_supDistOn
/-- At [a point belonging to S](hyp:hx), [the one-norm distance between two
d-dimensional output vectors is at most d times the supremum coordinate error
of the two maps on S](goal), including zero dimensions and infinite suprema. -/
lemma approximation_edist_le_dim_supDistOn
    {X : Type*} {d : ℕ} (S : Set X) (f g : X → L1Vec d) {x : X} (hx : x ∈ S) :
    edist (f x) (g x) ≤ (d : ℝ≥0∞) * supDistOn S f g := by
  rw [PiLp.edist_eq_of_L1]
  calc
    ∑ j : Fin d, edist ((f x).ofLp j) ((g x).ofLp j) ≤
        ∑ _j : Fin d, supDistOn S f g := by
      apply Finset.sum_le_sum
      intro j _
      rw [edist_dist, Real.dist_eq]
      apply le_iSup_of_le (⟨x, hx⟩ : S)
      apply ENNReal.ofReal_le_ofReal
      change ‖(f x - g x).ofLp j‖ ≤ ‖(f x - g x).ofLp‖
      exact norm_le_pi_norm ((f x - g x).ofLp) j
    _ = _ := by simp

-- @node: approximation_continuous_history_step
/-- Suppose [the first history law is concentrated on S](hyp:hmu), [the second
is concentrated on S](hyp:hnu), and [both output maps are
measurable](hyp:hf,hg). For [a nonnegative
coefficient L](hyp:L), if [the true output map is L-Lipschitz on S](hyp:hLip),
then [appending the respective d-dimensional outputs gives laws whose
Wasserstein distance is at most the original distance multiplied by the sum
of one and L, plus d times the supremum coordinate error on S](goal). -/
lemma approximation_continuous_history_step
    {h d : ℕ} (mu nu : Measure (L1Vec h))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (S : Set (L1Vec h)) (hmu : ∀ᵐ x ∂mu, x ∈ S) (hnu : ∀ᵐ x ∂nu, x ∈ S)
    (f g : L1Vec h → L1Vec d) (hf : Measurable f) (hg : Measurable g)
    (L : ℝ≥0) (hLip : LipschitzOnWith L f S) :
    wasserstein1
      (mu.map (fun x => WithLp.toLp 1 (Sum.elim x.ofLp (f x).ofLp)))
      (nu.map (fun x => WithLp.toLp 1 (Sum.elim x.ofLp (g x).ofLp))) ≤
      ((1+L : ℝ≥0) : ℝ≥0∞) * wasserstein1 mu nu +
        (d : ℝ≥0∞) * supDistOn S f g := by
  let F : L1Vec h → WithLp 1 ((Fin h ⊕ Fin d) → ℝ) :=
    fun x => WithLp.toLp 1 (Sum.elim x.ofLp (f x).ofLp)
  let G : L1Vec h → WithLp 1 ((Fin h ⊕ Fin d) → ℝ) :=
    fun x => WithLp.toLp 1 (Sum.elim x.ofLp (g x).ofLp)
  have hF : Measurable F := by
    apply (PiLp.continuous_toLp 1 _).measurable.comp
    apply measurable_pi_lambda
    intro i
    cases i <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> fun_prop
  have hG : Measurable G := by
    apply (PiLp.continuous_toLp 1 _).measurable.comp
    apply measurable_pi_lambda
    intro i
    cases i <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> fun_prop
  have hFLip : LipschitzOnWith (1+L) F S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hdist : dist (F x) (F y) = dist x y + dist (f x) (f y) := by
      simp only [F, PiLp.dist_eq_of_L1, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    rw [hdist]
    calc
      dist x y + dist (f x) (f y) ≤ dist x y + (L : ℝ) * dist x y :=
        add_le_add le_rfl (hLip.dist_le_mul x hx y hy)
      _ = _ := by simp only [NNReal.coe_add, NNReal.coe_one]; ring
  apply approximation_wasserstein_map_perturbation_le mu nu S hmu hnu F G hF hG
    (1+L) hFLip ((d : ℝ≥0∞) * supDistOn S f g)
  intro x hx
  have heq : edist (F x) (G x) = edist (f x) (g x) := by
    simp [F, G, PiLp.edist_eq_of_L1, Fintype.sum_sum_type]
  rw [heq]
  exact approximation_edist_le_dim_supDistOn S f g hx

-- @node: categoricalEncodedKernel
/-- Given [history-dependent category weights p](hyp:p) with [measurable
coordinates](hyp:hp) and [a history-dependent encoding v of the categories](hyp:v)
with [measurable encoded values for each category](hyp:hv), [the encoded
categorical kernel](goal) places the nonnegative part of each category's weight
at its encoded value and sums over categories. -/
noncomputable def categoricalEncodedKernel
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {k : ℕ}
    (p : X → Fin k → ℝ) (hp : ∀ i, Measurable (fun x => p x i))
    (v : X → Fin k → Y) (hv : ∀ i, Measurable (fun x => v x i)) :
    ProbabilityTheory.Kernel X Y where
  toFun x := ∑ i, ENNReal.ofReal (p x i) • Measure.dirac (v x i)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ hs]
    fun_prop

-- @node: categoricalEncodedCouplingKernel
/-- Given [two history-dependent category weight vectors p and q](hyp:p,q)
whose coordinates are [measurable for p](hyp:hp) and [measurable for q](hyp:hq),
and [two category encodings v and w](hyp:v,w) whose values are [measurable for
v](hyp:hv) and [measurable for w](hyp:hw), [the encoded categorical coupling
kernel](goal) assigns the explicit maximal coupling weights to pairs of encoded
values at the two histories. -/
noncomputable def categoricalEncodedCouplingKernel
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {k : ℕ}
    (p q : X → Fin k → ℝ)
    (hp : ∀ i, Measurable (fun x => p x i))
    (hq : ∀ i, Measurable (fun x => q x i))
    (v w : X → Fin k → Y)
    (hv : ∀ i, Measurable (fun x => v x i))
    (hw : ∀ i, Measurable (fun x => w x i)) :
    ProbabilityTheory.Kernel (X × X) (Y × Y) where
  toFun z := ∑ i, ∑ j,
    ENNReal.ofReal (categoricalCouplingWeights (p z.1) (q z.2) i j) •
      (Measure.dirac (v z.1 i)).prod (Measure.dirac (w z.2 j))
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.prod_dirac, Measure.map_dirac' measurable_prodMk_right,
      Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ hs]
    fun_prop

-- @node: categoricalEncodedCouplingKernel_coupling
/-- If [the first category weights have measurable coordinates](hyp:hp),
[the second category weights have measurable coordinates](hyp:hq), [the first
encoding is measurable for each category](hyp:hv), [the second encoding is
measurable for each category](hyp:hw), and [both weight vectors are probability
vectors at every history](hyp:hps,hqs), then
[the encoded maximal coupling at any pair of histories couples exactly the two
encoded categorical transition laws](goal). -/
lemma categoricalEncodedCouplingKernel_coupling
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {k : ℕ}
    (p q : X → Fin k → ℝ)
    (hp : ∀ i, Measurable (fun x => p x i))
    (hq : ∀ i, Measurable (fun x => q x i))
    (v w : X → Fin k → Y)
    (hv : ∀ i, Measurable (fun x => v x i))
    (hw : ∀ i, Measurable (fun x => w x i))
    (hps : ∀ x, p x ∈ probabilitySimplex k)
    (hqs : ∀ x, q x ∈ probabilitySimplex k) (z : X × X) :
    categoricalEncodedCouplingKernel p q hp hq v w hv hw z ∈ couplings
      (categoricalEncodedKernel p hp v hv z.1) (categoricalEncodedKernel q hq w hw z.2) := by
  obtain ⟨hr, hrow, hcol, hoff⟩ := categoricalCouplingWeights_properties (hps z.1) (hqs z.2)
  have hc := Toolkit.Foundations.MeasureTheory.finite_product_mixture_coupling
    (fun i => Measure.dirac (v z.1 i)) (fun j => Measure.dirac (w z.2 j))
    (fun _ => inferInstance) (fun _ => inferInstance)
    (fun i => ENNReal.ofReal (p z.1 i)) (fun j => ENNReal.ofReal (q z.2 j))
    (fun i j => ENNReal.ofReal (categoricalCouplingWeights (p z.1) (q z.2) i j))
    (by rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (hps z.1).1 i), (hps z.1).2]; simp)
    (fun i => by rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hr i j), hrow])
    (fun j => by rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hr i j), hcol])
  exact ⟨hc.isProbabilityMeasure, hc.map_fst, hc.map_snd⟩

-- @node: categoricalEncodedCouplingKernel_cost_le
/-- Suppose [the first category weights have measurable coordinates](hyp:hp),
[the second weights have measurable coordinates](hyp:hq), and [both encodings
are measurable for each category](hyp:hv,hw). If [the weights at the respective
histories are probability vectors](hyp:hps,hqs),
and [every encoded pair is at distance at most H, with an additional D allowed
when the labels differ](hyp:hcost), then [the expected distance under the
encoded maximal coupling is at most the nonnegative part of the sum of H and
D times half the sum of absolute differences between the category weights](goal). -/
lemma categoricalEncodedCouplingKernel_cost_le
    {X Y : Type*} [MeasurableSpace X] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {k : ℕ} (p q : X → Fin k → ℝ)
    (hp : ∀ i, Measurable (fun x => p x i))
    (hq : ∀ i, Measurable (fun x => q x i))
    (v w : X → Fin k → Y)
    (hv : ∀ i, Measurable (fun x => v x i))
    (hw : ∀ i, Measurable (fun x => w x i))
    (z : X × X) (hps : p z.1 ∈ probabilitySimplex k)
    (hqs : q z.2 ∈ probabilitySimplex k) (H D : ℝ)
    (hcost : ∀ i j, dist (v z.1 i) (w z.2 j) ≤ H + if i = j then 0 else D) :
    (∫⁻ y, edist y.1 y.2 ∂categoricalEncodedCouplingKernel p q hp hq v w hv hw z) ≤
      ENNReal.ofReal (H + D / 2 * ∑ i, |p z.1 i - q z.2 i|) := by
  classical
  let r := categoricalCouplingWeights (p z.1) (q z.2)
  obtain ⟨hr, hrow, hcol, hoff⟩ := categoricalCouplingWeights_properties hps hqs
  have hmass : (∑ i, ∑ j, r i j) = 1 := by dsimp only [r]; simp_rw [hrow]; exact hps.2
  have hbound : (∑ i, ∑ j, r i j * dist (v z.1 i) (w z.2 j)) ≤
      H + D / 2 * ∑ i, |p z.1 i - q z.2 i| := by
    calc
      _ ≤ ∑ i, ∑ j, r i j * (H + if i = j then 0 else D) := by
        apply Finset.sum_le_sum
        intro i _
        exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hcost i j) (hr i j)
      _ = H * (∑ i, ∑ j, r i j) + D * (∑ i, ∑ j, if i = j then 0 else r i j) := by
        simp_rw [mul_add, Finset.sum_add_distrib]
        congr 1
        · simp_rw [← Finset.sum_mul]; ring
        · simp_rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          split_ifs <;> ring
      _ = _ := by rw [hmass, hoff]; ring
  calc
    _ = ENNReal.ofReal (∑ i, ∑ j, r i j * dist (v z.1 i) (w z.2 j)) := by
      simp only [categoricalEncodedCouplingKernel, ProbabilityTheory.Kernel.coe_mk,
        lintegral_finsetSum_measure, lintegral_smul_measure]
      simp only [Measure.prod_dirac, Measure.map_dirac, lintegral_dirac,
        smul_eq_mul, edist_dist]
      simp_rw [← ENNReal.ofReal_mul (hr _ _)]
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ =>
        Finset.sum_nonneg (fun j _ => mul_nonneg (hr i j) dist_nonneg))]
      apply Finset.sum_congr rfl
      intro i _
      exact (ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (hr i j) dist_nonneg)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hbound

-- @node: categorical_encoded_history_step
/-- Suppose [both history laws are concentrated on S](hyp:hmu,hnu), [both
propensity maps are measurable](hyp:hp,hq), [both propensity maps take values
in the probability simplex everywhere](hyp:hps,hqs), and
[each label encoding is measurable in the history](hyp:hv). For [nonnegative
constants L and D](hyp:L,D), if [the true propensity is L-Lipschitz on
S](hyp:hLip) and [encoded outputs at two histories in S are separated by at
most the history distance plus D when their labels differ](hyp:hcost), then
[the Wasserstein distance between the encoded transition laws is at most
the original Wasserstein distance multiplied by the sum of one and D times L divided by two,
plus k times D divided by two times the supremum coordinate propensity
error on S](goal). -/
lemma categorical_encoded_history_step
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    {k : ℕ} (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (S : Set X) (hmu : ∀ᵐ x ∂mu, x ∈ S) (hnu : ∀ᵐ x ∂nu, x ∈ S)
    (p q : X → L1Vec k) (hp : Measurable p) (hq : Measurable q)
    (hps : ∀ x, (p x).ofLp ∈ probabilitySimplex k)
    (hqs : ∀ x, (q x).ofLp ∈ probabilitySimplex k)
    (v : X → Fin k → Y) (hv : ∀ i, Measurable (fun x => v x i))
    (L D : ℝ≥0) (hLip : LipschitzOnWith L p S)
    (hcost : ∀ x ∈ S, ∀ y ∈ S, ∀ i j,
      dist (v x i) (v y j) ≤ dist x y + if i = j then 0 else (D : ℝ)) :
    wasserstein1
      (mu.bind (categoricalEncodedKernel (fun x => (p x).ofLp) (by fun_prop) v hv))
      (nu.bind (categoricalEncodedKernel (fun x => (q x).ofLp) (by fun_prop) v hv)) ≤
      ((1 + D * L / 2 : ℝ≥0) : ℝ≥0∞) * wasserstein1 mu nu +
        ((k * D / 2 : ℝ≥0) : ℝ≥0∞) * supDistOn S p q := by
  let pm := fun i => (show Measurable (fun x => (p x).ofLp i) by fun_prop)
  let qm := fun i => (show Measurable (fun x => (q x).ofLp i) by fun_prop)
  apply approximation_wasserstein_bind_cross_bound_on mu nu S S hmu hnu
    _ _ (categoricalEncodedCouplingKernel _ _ pm qm v v hv hv)
    (categoricalEncodedCouplingKernel_coupling _ _ pm qm v v hv hv hps hqs)
  intro z hx hy
  let e : ℝ := ‖(p z.2 - q z.2).ofLp‖
  have he : 0 ≤ e := norm_nonneg _
  have hsup : ENNReal.ofReal e ≤ supDistOn S p q :=
    le_iSup_of_le (⟨z.2, hy⟩ : S) le_rfl
  have hlocal : dist (p z.2) (q z.2) ≤ (k : ℝ) * e := by
    rw [PiLp.dist_eq_of_L1]
    calc
      _ ≤ ∑ _i : Fin k, e := by
        apply Finset.sum_le_sum
        intro i _
        exact norm_le_pi_norm ((p z.2 - q z.2).ofLp) i
      _ = _ := by simp
  have hprop : dist (p z.1) (q z.2) ≤ (L : ℝ) * dist z.1 z.2 + k * e :=
    (dist_triangle _ (p z.2) _).trans (add_le_add (hLip.dist_le_mul _ hx _ hy) hlocal)
  calc
    _ ≤ ENNReal.ofReal (dist z.1 z.2 + (D : ℝ) / 2 *
        ∑ i, |(p z.1).ofLp i - (q z.2).ofLp i|) :=
      categoricalEncodedCouplingKernel_cost_le _ _ pm qm v v hv hv z
        (hps z.1) (hqs z.2) _ _ (hcost _ hx _ hy)
    _ ≤ ENNReal.ofReal ((1 + (D : ℝ) * L / 2) * dist z.1 z.2 +
        (k : ℝ) * D / 2 * e) := by
      apply ENNReal.ofReal_le_ofReal
      have h := mul_le_mul_of_nonneg_left hprop (show 0 ≤ (D : ℝ) / 2 by positivity)
      rw [PiLp.dist_eq_of_L1] at h
      simp only [Real.dist_eq] at h
      nlinarith
    _ = ((1 + D * L / 2 : ℝ≥0) : ℝ≥0∞) * edist z.1 z.2 +
        ((k * D / 2 : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal e := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), edist_dist]
      congr 2
      · simpa only [NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul, NNReal.coe_div,
          NNReal.coe_ofNat] using (@ENNReal.ofReal_coe_nnreal (1 + D * L / 2))
      · simpa only [NNReal.coe_mul, NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_natCast]
          using (@ENNReal.ofReal_coe_nnreal (k * D / 2))
    _ ≤ _ := by gcongr

-- @node: categorical_history_encoding_measurable
/-- [Appending the fixed category's one-based numeric label to a history is
a measurable map](goal). -/
@[fun_prop] lemma categorical_history_encoding_measurable {h k : ℕ} (i : Fin k) :
    Measurable (fun x : L1Vec h =>
      WithLp.toLp 1 (Sum.elim x.ofLp (fun _ : Unit => (i.val + 1 : ℝ)))) := by
  apply (PiLp.continuous_toLp 1 _).measurable.comp
  apply measurable_pi_lambda
  intro j
  cases j <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> fun_prop

-- @node: approximation_categorical_history_step
/-- Suppose [both history laws are concentrated on S](hyp:hmu,hnu), [both
propensity maps are measurable](hyp:hp,hq), and [both propensity maps take
values in the probability simplex everywhere](hyp:hps,hqs).
For [a nonnegative constant L](hyp:L), if [the true propensity is L-Lipschitz
on S](hyp:hLip), then [appending a categorical draw encoded by its one-based
numeric label gives a Wasserstein distance at most the original distance
multiplied by the sum of one and the label range times L divided by two, plus k times the label
range divided by two times the supremum coordinate propensity error on
S, where the label range is k minus one truncated at zero](goal). -/
lemma approximation_categorical_history_step
    {h k : ℕ} (mu nu : Measure (L1Vec h))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (S : Set (L1Vec h)) (hmu : ∀ᵐ x ∂mu, x ∈ S) (hnu : ∀ᵐ x ∂nu, x ∈ S)
    (p q : L1Vec h → L1Vec k) (hp : Measurable p) (hq : Measurable q)
    (hps : ∀ x, (p x).ofLp ∈ probabilitySimplex k)
    (hqs : ∀ x, (q x).ofLp ∈ probabilitySimplex k)
    (L : ℝ≥0) (hLip : LipschitzOnWith L p S) :
    let v := fun (x : L1Vec h) (i : Fin k) =>
      WithLp.toLp 1 (Sum.elim x.ofLp (fun _ : Unit => (i.val + 1 : ℝ)))
    wasserstein1
      (mu.bind (categoricalEncodedKernel (fun x => (p x).ofLp) (by fun_prop) v (by fun_prop)))
      (nu.bind (categoricalEncodedKernel (fun x => (q x).ofLp) (by fun_prop) v (by fun_prop))) ≤
      ((1 + (k-1 : ℕ) * L / 2 : ℝ≥0) : ℝ≥0∞) * wasserstein1 mu nu +
        ((k * (k-1 : ℕ) / 2 : ℝ≥0) : ℝ≥0∞) * supDistOn S p q := by
  dsimp only
  apply categorical_encoded_history_step mu nu S hmu hnu p q hp hq hps hqs
    _ _ L (k-1 : ℕ) hLip
  intro x hx y hy i j
  simp only [PiLp.dist_eq_of_L1, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Fintype.sum_unique]
  by_cases hij : i = j
  · simp [hij]
  · simp only [hij, ↓reduceIte]
    exact add_le_add le_rfl (categorical_label_diameter_le i j)

end Papers.TbsNeuralCausalPi
