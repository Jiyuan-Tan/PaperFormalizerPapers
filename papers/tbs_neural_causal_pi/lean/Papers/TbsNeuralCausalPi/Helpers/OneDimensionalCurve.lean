module
public import Papers.TbsNeuralCausalPi.Helpers.ComponentLaws
public import Papers.TbsNeuralCausalPi.Helpers.HilbertQuantile
public import Papers.TbsNeuralCausalPi.Setup.Cubes
/-! # The one-dimensional cube branch of the representing-curve construction -/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped ENNReal NNReal

-- @node: chartInverse_measurable
/-- For [a homeomorphism from the unit cube onto a set](hyp:chart), if
[that set is compact](hyp:hK), then [the inverse chart, extended by zero outside
the set, is measurable](goal). -/
@[fun_prop] lemma chartInverse_measurable {D d : ℕ} {K : Set (L1Vec D)}
    (chart : homeoClass (unitCube d) K) (hK : IsCompact K) :
    Measurable (chartInverse chart) := by
  let : BorelSpace (L1Vec D) := ⟨rfl⟩
  let : BorelSpace (L1Vec d) := ⟨rfl⟩
  apply measurable_of_restrict_of_restrict_compl hK.measurableSet
  · have hm : Measurable (fun x : K => (chart.symm x).val) := by fun_prop
    convert hm using 1
    funext x
    exact dif_pos x.property
  · have heq : Kᶜ.domRestrict (chartInverse chart) = fun _ => (0 : L1Vec d) := by
      funext x
      exact dif_neg x.property
    rw [heq]
    fun_prop

-- @node: chartInverse_mapsTo
/-- Given [a homeomorphism from the unit cube onto a set](hyp:chart),
[its extended inverse maps every point of that set into the unit cube](goal). -/
lemma chartInverse_mapsTo {D d : ℕ} {K : Set (L1Vec D)}
    (chart : homeoClass (unitCube d) K) :
    Set.MapsTo (chartInverse chart) K (unitCube d) := by
  intro x hx
  simp only [chartInverse, dif_pos hx]
  exact (chart.symm ⟨x, hx⟩).property

-- @node: chartInverse_pullback_mass
/-- For [a probability measure](hyp:P) and [a homeomorphism from the unit cube
onto a set](hyp:chart), if [the set is compact](hyp:hK) and [has probability
one](hyp:hmass), then [transporting the measure through the extended inverse
chart assigns mass one to the unit cube](goal). -/
lemma chartInverse_pullback_mass {D d : ℕ} {K : Set (L1Vec D)}
    (P : ProbabilityMeasure (L1Vec D)) (chart : homeoClass (unitCube d) K)
    (hK : IsCompact K) (hmass : (P : Measure _) K = 1) :
    ((P : Measure _).map (chartInverse chart)) (unitCube d) = 1 := by
  let : BorelSpace (L1Vec d) := ⟨rfl⟩
  rw [Measure.map_apply (chartInverse_measurable chart hK)
    (unitCube_isCompact d).measurableSet]
  apply le_antisymm prob_le_one
  rw [← hmass]
  exact measure_mono (chartInverse_mapsTo chart)

-- @node: chartInverse_domination
/-- For [a probability measure](hyp:P), [a chart from the unit cube onto a
set](hyp:chart), [a nonnegative Lipschitz bound](hyp:L), and [a real domination
constant](hyp:Cf), suppose [the set is compact with probability one, the constant
is positive, the chart satisfies the Lipschitz bound, and probabilities of chart
images dominate the constant times cube volume](hyp:hdom). Then [the measure
transported through the inverse chart dominates that constant times Lebesgue
measure restricted to the unit cube](goal). -/
lemma chartInverse_domination {D d : ℕ} {K : Set (L1Vec D)}
    (P : ProbabilityMeasure (L1Vec D)) (chart : homeoClass (unitCube d) K)
    (L : ℝ≥0) (Cf : ℝ)
    (hdom : lowerBoundDominationAt (P : Measure _) K chart L Cf) :
    ENNReal.ofReal Cf •
      (((Measure.pi (fun _ : Fin d => volume)).map (WithLp.toLp 1)).restrict
        (unitCube d)) ≤ (P : Measure _).map (chartInverse chart) := by
  let : BorelSpace (L1Vec d) := ⟨rfl⟩
  apply Measure.le_iff.mpr
  intro B hB
  rw [Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply hB, Measure.map_apply (chartInverse_measurable chart hdom.1) hB]
  refine (hdom.2.2.2.2 (B ∩ unitCube d)
    (hB.inter (unitCube_isCompact d).measurableSet) Set.inter_subset_right).trans ?_
  apply measure_mono
  rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
  have hx : (chart z).val ∈ K := (chart z).property
  simpa [chartInverse, hx] using hz.1


-- @node: oneDimCoordinate
/-- For [a vector with one coordinate](hyp:x), [its scalar coordinate](goal)
is its unique entry. -/
def oneDimCoordinate (x : L1Vec 1) : ℝ := x.ofLp 0

-- @node: oneDimEmbedding
/-- For [a real number](hyp:t), [its one-dimensional vector embedding](goal)
is the vector whose unique entry is that number. -/
def oneDimEmbedding (t : ℝ) : L1Vec 1 := WithLp.toLp 1 (fun _ => t)

-- @node: oneDimCoordinate_measurable
/-- [Extracting the unique scalar coordinate of a one-dimensional vector is
measurable](goal). -/
@[fun_prop] lemma oneDimCoordinate_measurable : Measurable oneDimCoordinate := by
  unfold oneDimCoordinate
  fun_prop

-- @node: oneDimEmbedding_lipschitz
/-- [Embedding real numbers as one-dimensional vectors is Lipschitz with
constant one](goal). -/
lemma oneDimEmbedding_lipschitz : LipschitzWith 1 oneDimEmbedding := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp [oneDimEmbedding, PiLp.dist_eq_of_L1]

-- @node: oneDimEmbedding_coordinate
/-- For [a one-dimensional vector](hyp:x), [extracting its scalar coordinate
and embedding that coordinate again recovers the original vector](goal). -/
lemma oneDimEmbedding_coordinate (x : L1Vec 1) :
    oneDimEmbedding (oneDimCoordinate x) = x := by
  apply PiLp.ext
  intro j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  rfl

-- @node: oneDimCoordinate_cube_preimage
/-- [The vectors whose unique coordinate lies in the closed unit interval
are exactly the one-dimensional unit cube](goal). -/
lemma oneDimCoordinate_cube_preimage :
    oneDimCoordinate ⁻¹' Set.Icc (0 : ℝ) 1 = unitCube 1 := by
  ext x
  constructor
  · intro hx j
    have hj : j = 0 := Subsingleton.elim _ _
    simpa [hj, oneDimCoordinate] using hx
  · intro hx
    exact hx 0

-- @node: oneDimCoordinate_cube_volume
/-- [Transporting one-dimensional cube volume through the scalar coordinate
map gives Lebesgue measure restricted to the closed unit interval](goal). -/
lemma oneDimCoordinate_cube_volume :
    ((((Measure.pi (fun _ : Fin 1 => volume)).map (WithLp.toLp 1)).restrict
      (unitCube 1)).map oneDimCoordinate) = curveLebesgue := by
  let : BorelSpace (L1Vec 1) := ⟨rfl⟩
  have hvol : ((Measure.pi (fun _ : Fin 1 => volume)).map
      (WithLp.toLp 1)).map oneDimCoordinate = volume := by
    rw [Measure.map_map oneDimCoordinate_measurable (by fun_prop)]
    exact (measurePreserving_funUnique volume (Fin 1)).map_eq
  rw [← oneDimCoordinate_cube_preimage]
  rw [← Measure.restrict_map oneDimCoordinate_measurable measurableSet_Icc, hvol]
  rfl

-- @node: exists_oneDim_component_pullback_curve
/-- For [a probability measure](hyp:mu), [a chart from the one-dimensional unit
cube onto a set](hyp:chart), [a nonnegative Lipschitz bound](hyp:L), and [a real
domination constant](hyp:Cf), assume [the set is compact with probability one,
the constant is positive, the chart satisfies the Lipschitz bound, and chart-image
probabilities dominate that constant times cube volume](hyp:hdom). Then [there
is a curve with a finite nonnegative Lipschitz bound on the closed unit interval,
taking values in the one-dimensional unit cube, that transports uniform interval
measure to the probability measure transported through the inverse chart](goal). -/
lemma exists_oneDim_component_pullback_curve {D : ℕ}
    (mu : ProbabilityMeasure (L1Vec D)) {K : Set (L1Vec D)}
    (chart : homeoClass (unitCube 1) K) (L : ℝ≥0) (Cf : ℝ)
    (hdom : lowerBoundDominationAt (mu : Measure _) K chart L Cf) :
    ∃ gamma : ℝ → L1Vec 1, ∃ A : ℝ≥0,
      LipschitzOnWith A gamma (Set.Icc 0 1) ∧
      Set.MapsTo gamma (Set.Icc 0 1) (unitCube 1) ∧
      curveLebesgue.map gamma = (mu : Measure _).map (chartInverse chart) := by
  let rho := ((mu : Measure _).map (chartInverse chart)).map oneDimCoordinate
  let : IsProbabilityMeasure ((mu : Measure _).map (chartInverse chart)) :=
    Measure.isProbabilityMeasure_map (chartInverse_measurable chart hdom.1).aemeasurable
  let : IsProbabilityMeasure rho :=
    Measure.isProbabilityMeasure_map oneDimCoordinate_measurable.aemeasurable
  have hmass : rho (Set.Icc (0 : ℝ) 1) = 1 := by
    dsimp [rho]
    rw [Measure.map_apply oneDimCoordinate_measurable measurableSet_Icc,
      oneDimCoordinate_cube_preimage]
    exact chartInverse_pullback_mass mu chart hdom.1 hdom.2.1
  let c : ℝ≥0 := ⟨Cf, hdom.2.2.1.le⟩
  have hc : 0 < c := hdom.2.2.1
  have hdomrho : c • curveLebesgue ≤ rho := by
    have hh := Measure.map_mono (chartInverse_domination mu chart L Cf hdom)
      oneDimCoordinate_measurable
    rw [Measure.map_smul, oneDimCoordinate_cube_volume] at hh
    change (c : ℝ≥0∞) • curveLebesgue ≤ rho
    have heq : ENNReal.ofReal Cf = (c : ℝ≥0∞) :=
      ENNReal.ofReal_eq_coe_nnreal hdom.2.2.1.le
    rw [heq] at hh
    exact hh
  obtain ⟨Q, hLip, hcont, hmem, hzero, hone, hmap⟩ :=
    exists_dominated_interval_reparameterization rho hmass c hc hdomrho
  refine ⟨oneDimEmbedding ∘ Q, c⁻¹, ?_, ?_, ?_⟩
  · simpa only [one_mul] using oneDimEmbedding_lipschitz.comp_lipschitzOnWith hLip
  · intro t ht j
    exact hmem ht
  · have hQ : AEMeasurable Q curveLebesgue := by
      first | fun_prop | exact hcont.aemeasurable measurableSet_Icc
    have hemb : Measurable oneDimEmbedding := by
      let : BorelSpace (L1Vec 1) := ⟨rfl⟩
      exact oneDimEmbedding_lipschitz.continuous.measurable
    change curveLebesgue.map Q = rho at hmap
    rw [← AEMeasurable.map_map_of_aemeasurable hemb.aemeasurable hQ, hmap]
    dsimp [rho]
    rw [Measure.map_map hemb oneDimCoordinate_measurable]
    have hid : oneDimEmbedding ∘ oneDimCoordinate = id := by
      funext x
      exact oneDimEmbedding_coordinate x
    rw [hid, Measure.map_id]

-- @node: chartForward
/-- Given [a homeomorphism from the unit cube onto a set](hyp:chart) and [an
input vector in the cube's ambient space](hyp:x), [the extended forward
chart](goal) returns [the chart image when the vector belongs to the unit
cube](step:1) and [the zero vector otherwise](step:2). -/
noncomputable def chartForward {D d : ℕ} {K : Set (L1Vec D)}
    (chart : homeoClass (unitCube d) K) (x : L1Vec d) : L1Vec D := by
  classical
  exact if hx : x ∈ unitCube d then (chart ⟨x, hx⟩).val else 0

-- @node: chartForward_measurable
/-- For [a homeomorphism from the unit cube onto a set](hyp:chart), [the forward
chart extended by zero outside the cube is measurable](goal). -/
@[fun_prop] lemma chartForward_measurable {D d : ℕ} {K : Set (L1Vec D)}
    (chart : homeoClass (unitCube d) K) : Measurable (chartForward chart) := by
  let : BorelSpace (L1Vec D) := ⟨rfl⟩
  let : BorelSpace (L1Vec d) := ⟨rfl⟩
  apply measurable_of_restrict_of_restrict_compl (unitCube_isCompact d).measurableSet
  · have hm : Measurable (fun x : unitCube d => (chart x).val) := by fun_prop
    convert hm using 1
    funext x
    exact dif_pos x.property
  · have heq : (unitCube d)ᶜ.domRestrict (chartForward chart) =
        fun _ => (0 : L1Vec D) := by
      funext x
      exact dif_neg x.property
    rw [heq]
    fun_prop

-- @node: chartForward_lipschitzOn
/-- For [a homeomorphism from the unit cube onto a set](hyp:chart) and [a
nonnegative constant](hyp:L), if [the chart is Lipschitz with that
constant](hyp:hL), then [its extension by zero has the same Lipschitz bound
on the unit cube](goal). -/
lemma chartForward_lipschitzOn {D d : ℕ} {K : Set (L1Vec D)}
    (chart : homeoClass (unitCube d) K) (L : ℝ≥0) (hL : LipschitzWith L chart) :
    LipschitzOnWith L (chartForward chart) (unitCube d) := by
  intro x hx y hy
  simpa only [chartForward, dif_pos hx, dif_pos hy, Subtype.edist_eq] using
    hL ⟨x, hx⟩ ⟨y, hy⟩

-- @node: chartForward_mapsTo
/-- Given [a homeomorphism from the unit cube onto a set](hyp:chart), [the
extended forward chart maps the unit cube into that set](goal). -/
lemma chartForward_mapsTo {D d : ℕ} {K : Set (L1Vec D)}
    (chart : homeoClass (unitCube d) K) :
    Set.MapsTo (chartForward chart) (unitCube d) K := by
  intro x hx
  simpa only [chartForward, dif_pos hx] using (chart ⟨x, hx⟩).property

-- @node: chartForward_map_pullback
/-- For [a probability measure](hyp:P) and [a homeomorphism from the unit cube
onto a set](hyp:chart), if [the set is compact](hyp:hK) and [has probability
one](hyp:hmass), then [transporting the measure first through the extended
inverse chart and then through the extended forward chart recovers the original
measure](goal). -/
lemma chartForward_map_pullback {D d : ℕ} {K : Set (L1Vec D)}
    (P : ProbabilityMeasure (L1Vec D)) (chart : homeoClass (unitCube d) K)
    (hK : IsCompact K) (hmass : (P : Measure _) K = 1) :
    ((P : Measure _).map (chartInverse chart)).map (chartForward chart) =
      (P : Measure _) := by
  let : BorelSpace (L1Vec D) := ⟨rfl⟩
  rw [Measure.map_map (chartForward_measurable chart) (chartInverse_measurable chart hK)]
  have hae : chartForward chart ∘ chartInverse chart =ᵐ[(P : Measure _)] id := by
    filter_upwards [(mem_ae_iff_prob_eq_one hK.measurableSet).2 hmass] with x hx
    dsimp [Function.comp, chartInverse]
    rw [dif_pos hx]
    simp only [chartForward, dif_pos (chart.symm ⟨x, hx⟩).property,
      chart.apply_symm_apply]
  rw [Measure.map_congr hae, Measure.map_id]

-- @node: exists_oneDim_measure_representing_lipschitz_curve
/-- For [a probability measure](hyp:P), [a subset of its ambient vector
space](hyp:K), and [a nonnegative chart Lipschitz bound](hyp:L), suppose [the set
admits a chart from the one-dimensional unit cube satisfying that bound and
positive lower domination of cube volume, and is compact with probability
one](hyp:hdomination). Then [there is a curve, Lipschitz with some finite
nonnegative bound on the closed unit interval and taking values in the set,
that transports uniform interval measure to the given probability measure](goal). -/
lemma exists_oneDim_measure_representing_lipschitz_curve {D : ℕ}
    (P : ProbabilityMeasure (L1Vec D)) (K : Set (L1Vec D)) (L : ℝ≥0)
    (hdomination : LowerBoundDomination (d := 1) (P : Measure _) K L) :
    ∃ gamma : ℝ → L1Vec D, ∃ A : ℝ≥0,
      LipschitzOnWith A gamma (Set.Icc 0 1) ∧
      Set.MapsTo gamma (Set.Icc 0 1) K ∧
      curveLebesgue.map gamma = (P : Measure _) := by
  let : BorelSpace (L1Vec 1) := ⟨rfl⟩
  obtain ⟨chart, Cf, hdom⟩ := hdomination
  obtain ⟨zeta, A, hLip, hmem, hmap⟩ :=
    exists_oneDim_component_pullback_curve P chart L Cf hdom
  refine ⟨chartForward chart ∘ zeta, L * A,
    (chartForward_lipschitzOn chart L hdom.2.2.2.1).comp hLip hmem,
    (chartForward_mapsTo chart).comp hmem, ?_⟩
  have hzeta : AEMeasurable zeta curveLebesgue := by
    first | fun_prop | exact hLip.continuousOn.aemeasurable measurableSet_Icc
  rw [← AEMeasurable.map_map_of_aemeasurable
    (chartForward_measurable chart).aemeasurable hzeta, hmap]
  exact chartForward_map_pullback P chart hdom.1 hdom.2.1

end Papers.TbsNeuralCausalPi
