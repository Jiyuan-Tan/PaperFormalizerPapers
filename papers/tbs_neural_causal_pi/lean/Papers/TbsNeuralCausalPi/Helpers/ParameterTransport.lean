module
public import Papers.TbsNeuralCausalPi.Helpers.ParameterExtension
/-! # Transport costs of clipped population representatives

Embedding the compact latent cubes preserves marginal Wasserstein costs.
Together with the common structural clipping, this identifies the error
consumed by the population transport estimate with the parameter distance.
-/
public section
namespace Papers.TbsNeuralCausalPi
set_option backward.isDefEq.respectTransparency false
set_option linter.style.longLine false
open MeasureTheory Filter
open scoped NNReal ENNReal Topology

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)} {K L : ℝ≥0}

-- @node: ofParam_blockLaw_wasserstein_eq
/-- [The Wasserstein distance between the latent laws of two population
representatives in a given block equals the Wasserstein distance between
their corresponding laws on the bounded cube](goal). -/
lemma ofParam_blockLaw_wasserstein_eq
    (base : CanonicalSCM kind dims dag G C)
    (p q : PopulationParam kind dims dag C K L) (j : Fin b) :
    wasserstein1 ((ofParam base p.parameter).blockLaw j : Measure (L1Vec (dims j)))
      ((ofParam base q.parameter).blockLaw j : Measure (L1Vec (dims j))) =
      wasserstein1 (p.parameter.2 j : Measure (boundedCube (dims j) K))
        (q.parameter.2 j : Measure (boundedCube (dims j) K)) := by
  rw [wasserstein1_eq_toolkit, wasserstein1_eq_toolkit]
  rw [Toolkit.Foundations.MeasureTheory.wasserstein1_subtype_comap
    ((ofParam base p.parameter).blockLaw j : Measure (L1Vec (dims j)))
    ((ofParam base q.parameter).blockLaw j : Measure (L1Vec (dims j)))
    (boundedCube (dims j) K) (boundedCube_isCompact _ _).measurableSet
    (ofParam_blockLaw_cube base p j) (ofParam_blockLaw_cube base q j)]
  have he := MeasurableEmbedding.subtype_coe (boundedCube_isCompact (dims j) K).measurableSet
  simp only [ofParam, ProbabilityMeasure.coe_mk, he.comap_map]

-- @node: boxTruncated_ofParam_norm_sub_le_paramDist
/-- If [every categorical label count is at most the cube bound](hyp:hlabels),
[the norm of the difference between the two clipped structural outputs at
any input is at most the output dimension times the parameter distance](goal). -/
lemma boxTruncated_ofParam_norm_sub_le_paramDist
    (base : CanonicalSCM kind dims dag G C)
    (p q : PopulationParam kind dims dag C K L)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ K)
    (i : Fin n) (x : Input kind dims dag C i) :
    ‖(boxTruncatedSCM (ofParam base p.parameter) K hlabels).f i x -
      (boxTruncatedSCM (ofParam base q.parameter) K hlabels).f i x‖ ≤
      (outputDim (kind i) : ℝ) * paramDist p q := by
  rw [boxTruncated_ofParam_apply base p hlabels,
    boxTruncated_ofParam_apply base q hlabels]
  exact population_structural_norm_sub_le_paramDist p q i _

-- @node: paramDist_tendsto_boxTruncated_uniformly
/-- If [every categorical label count is at most the cube bound](hyp:hlabels)
and [the parameter distances to a fixed population parameter tend to zero](hyp:h),
[the clipped structural functions at each node converge uniformly over the
entire ambient input space to those of that parameter](goal). -/
lemma paramDist_tendsto_boxTruncated_uniformly
    (base : CanonicalSCM kind dims dag G C)
    (p : ℕ → PopulationParam kind dims dag C K L)
    (q : PopulationParam kind dims dag C K L)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ K)
    (h : Tendsto (fun r => paramDist (p r) q) atTop (𝓝 0)) (i : Fin n) :
    TendstoUniformly
      (fun r => (boxTruncatedSCM (ofParam base (p r).parameter) K hlabels).f i)
      ((boxTruncatedSCM (ofParam base q.parameter) K hlabels).f i) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro eps heps
  have ht : Tendsto (fun r => (outputDim (kind i) : ℝ) * paramDist (p r) q)
      atTop (𝓝 0) := by simpa using h.const_mul (outputDim (kind i) : ℝ)
  filter_upwards [ht.eventually (gt_mem_nhds heps)] with r hr x
  exact lt_of_le_of_lt (by
    simpa only [dist_eq_norm, norm_sub_rev] using
      boxTruncated_ofParam_norm_sub_le_paramDist base (p r) q hlabels i x) hr

-- @node: boxTruncated_ofParam_transport_error_le_paramDist
/-- Given [an input set for each node on which to compare mechanisms](hyp:S),
if [every categorical label count is at most the cube bound](hyp:hlabels),
[the sum of the structural uniform discrepancies on the chosen input sets
and the latent block Wasserstein distances between two clipped population
representatives is at most their parameter distance](goal). -/
lemma boxTruncated_ofParam_transport_error_le_paramDist
    (base : CanonicalSCM kind dims dag G C)
    (p q : PopulationParam kind dims dag C K L)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ K)
    (S : ∀ i, Set (Input kind dims dag C i)) :
    (∑ i, supDistOn (S i)
      ((boxTruncatedSCM (ofParam base p.parameter) K hlabels).f i)
      ((boxTruncatedSCM (ofParam base q.parameter) K hlabels).f i)) +
      (∑ j, wasserstein1
        ((boxTruncatedSCM (ofParam base p.parameter) K hlabels).blockLaw j : Measure (L1Vec (dims j)))
        ((boxTruncatedSCM (ofParam base q.parameter) K hlabels).blockLaw j : Measure (L1Vec (dims j)))) ≤
      ENNReal.ofReal (paramDist p q) := by
  rw [paramDist_ofReal_eq_sum]
  apply add_le_add
  · exact Finset.sum_le_sum (fun i _ =>
      boxTruncated_ofParam_supDistOn_le base p q hlabels i (S i))
  · apply le_of_eq
    apply Finset.sum_congr rfl
    intro j _
    exact ofParam_blockLaw_wasserstein_eq base p q j

-- @node: paramDist_tendsto_ofParam_blockLaw_wasserstein
/-- If [the parameter distances to a fixed population parameter tend to zero](hyp:h),
[the Wasserstein distance between each latent block law of the associated
representatives and the corresponding limiting law tends to zero](goal). -/
lemma paramDist_tendsto_ofParam_blockLaw_wasserstein
    (base : CanonicalSCM kind dims dag G C)
    (p : ℕ → PopulationParam kind dims dag C K L)
    (q : PopulationParam kind dims dag C K L)
    (h : Tendsto (fun r => paramDist (p r) q) atTop (𝓝 0)) (j : Fin b) :
    Tendsto (fun r => wasserstein1
      ((ofParam base (p r).parameter).blockLaw j : Measure (L1Vec (dims j)))
      ((ofParam base q.parameter).blockLaw j : Measure (L1Vec (dims j))))
      atTop (𝓝 0) := by
  simp_rw [ofParam_blockLaw_wasserstein_eq]
  exact paramDist_tendsto_latent_wasserstein p q h j

-- @node: paramDist_tendsto_boxTruncated_transport_error
/-- Given [an input set for each node on which to compare mechanisms](hyp:S),
if [every categorical label count is at most the cube bound](hyp:hlabels)
and [the parameter distances to a fixed population parameter tend to zero](hyp:h),
[the sum of structural uniform discrepancies on the chosen input sets and
latent block Wasserstein distances for the clipped representatives tends
to zero](goal). -/
lemma paramDist_tendsto_boxTruncated_transport_error
    (base : CanonicalSCM kind dims dag G C)
    (p : ℕ → PopulationParam kind dims dag C K L)
    (q : PopulationParam kind dims dag C K L)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ K)
    (S : ∀ i, Set (Input kind dims dag C i))
    (h : Tendsto (fun r => paramDist (p r) q) atTop (𝓝 0)) :
    Tendsto (fun r =>
      (∑ i, supDistOn (S i)
        ((boxTruncatedSCM (ofParam base (p r).parameter) K hlabels).f i)
        ((boxTruncatedSCM (ofParam base q.parameter) K hlabels).f i)) +
      (∑ j, wasserstein1
        ((boxTruncatedSCM (ofParam base (p r).parameter) K hlabels).blockLaw j : Measure (L1Vec (dims j)))
        ((boxTruncatedSCM (ofParam base q.parameter) K hlabels).blockLaw j : Measure (L1Vec (dims j)))))
      atTop (𝓝 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using ENNReal.tendsto_ofReal h) (fun _ => bot_le)
    (fun r => boxTruncated_ofParam_transport_error_le_paramDist base (p r) q hlabels S)

end Papers.TbsNeuralCausalPi
