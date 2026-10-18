module
public import Papers.TbsNeuralCausalPi.Helpers.DeepCommonBudgets
public import Papers.TbsNeuralCausalPi.Helpers.WideGeneratorSupport
public import Papers.TbsNeuralCausalPi.Setup.Optimization
public import Papers.TbsNeuralCausalPi.Helpers.CanonicalLatentIndependence
public import Papers.TbsNeuralCausalPi.Helpers.CubeDimension
/-! # Clipped latent generators at the consistency architecture budgets

The true latent law is carried by its bounded cube. Output truncation fixes
that law and contracts transport cost. Common generator widths may then be
increased to any of the selected architecture factors.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped ENNReal NNReal

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
    {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
    {C : Fin b → Set (Fin n)}

-- @node: canonical_blockProjection_law
/-- [The marginal law of any private latent block in a canonical model equals
that block's prescribed probability law](goal). -/
lemma canonical_blockProjection_law (M : CanonicalSCM kind dims dag G C) (j : Fin b) :
    M.latentLaw.map (blockProjection j) = (M.blockLaw j : Measure _) := by
  let := fun i => canonicalNamedLatentLaw_probability M i
  have hm : Measurable (blockProjection (kind := kind) (dims := dims) j) := by
    first | fun_prop | fun_prop [blockProjection]
  rw [canonical_latentLaw_eq_named_product M,
    Measure.map_map hm restoreNamedLatents_measurable]
  change (Measure.pi (canonicalNamedLatentLaw M)).map (fun z => z (.inl j)) = _
  exact (measurePreserving_eval (canonicalNamedLatentLaw M) (.inl j)).map_eq

-- @node: canonical_blockLaw_ae_boundedCube
/-- For [a nonnegative radius K](hyp:K), if [the canonical model's variables are
bounded at K](hyp:hbound), [each private block lies almost surely in its
coordinate cube of radius K under its prescribed law](goal). -/
lemma canonical_blockLaw_ae_boundedCube (M : CanonicalSCM kind dims dag G C)
    (K : ℝ≥0) (hbound : VariablesBoundedAt M.toEuclideanSCM K) (j : Fin b) :
    ∀ᵐ x ∂(M.blockLaw j : Measure _), x ∈ boundedCube (dims j) K := by
  rw [← canonical_blockProjection_law M j]
  apply (ae_map_iff (by first | fun_prop | fun_prop [blockProjection])
    (by exact (boundedCube_isCompact (dims j) K).measurableSet)).2
  exact hbound.2.mono (fun u hu => hu.2 j)

-- @node: wasserstein_truncK_le
/-- For [a nonnegative clipping radius K](hyp:K), if [the target probability law
is concentrated on the coordinate cube of radius K](hyp:hmu), [clipping a
candidate probability law to that cube cannot increase its Wasserstein-1
distance from the target](goal). -/
lemma wasserstein_truncK_le {d : ℕ} (mu nu : Measure (L1Vec d))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] (K : ℝ≥0)
    (hmu : ∀ᵐ x ∂mu, x ∈ boundedCube d K) :
    wasserstein1 mu (nu.map (truncK K)) ≤ wasserstein1 mu nu := by
  have hm : Measurable (truncK (d := d) K) := by
    change Measurable (coordinateClamp (-(K : ℝ)) K)
    fun_prop
  have hfix : mu.map (truncK K) = mu := by
    calc
      _ = mu.map id := Measure.map_congr (hmu.mono (fun x hx =>
        coordinateClamp_fixes (-(K : ℝ)) K x (fun j => abs_le.mp (hx j))))
      _ = mu := Measure.map_id
  have hrange (x : L1Vec d) : truncK K x ∈ boundedCube d K := by
    intro j
    exact abs_le.mpr (coordinateClamp_mapsTo (-(K : ℝ)) K (by linarith [K.coe_nonneg]) x j)
  have h := PushForward.map_le_of_compact_range mu nu (truncK K) (truncK K)
    hm hm 1 (coordinateClamp_lipschitz (-(K : ℝ)) K) 0 (by simp)
    (boundedCube d K) (boundedCube_isCompact d K) hrange hrange
  simpa only [hfix, ENNReal.coe_one, one_mul, add_zero] using h

-- @node: generator_truncK_wasserstein_le
/-- For [a nonnegative clipping radius K](hyp:K), if [the target law is
concentrated on the coordinate cube of radius K](hyp:hP), [clipping the generator's
output to that cube cannot increase its Wasserstein-1 error relative to the
target](goal). -/
lemma generator_truncK_wasserstein_le {N d W1 L1 W2 L2 : ℕ}
    {dC : Fin N → ℕ} {tau : ℝ}
    (P : ProbabilityMeasure (L1Vec d)) (K : ℝ≥0)
    (hP : ∀ᵐ x ∂(P : Measure _), x ∈ boundedCube d K)
    (q : ThreePartGenerator N d dC W1 L1 W2 L2 tau) :
    wasserstein1 (P : Measure _) ((generatorInputLaw N).map (truncK K ∘ q.eval)) ≤
      wasserstein1 (P : Measure _) (generatorLaw q) := by
  let := generatorInputLaw_probability N
  let : IsProbabilityMeasure ((generatorInputLaw N).map q.eval) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  rw [← Measure.map_map (by change Measurable (coordinateClamp (-(K : ℝ)) K); fun_prop)
    (by fun_prop)]
  exact wasserstein_truncK_le _ _ K hP

-- @node: clipped_generators_architecture_budgets
/-- Consider [target probability laws for the latent blocks](hyp:P), [families
of component sets](hyp:S), [their chart dimensions](hyp:dC), and [nonnegative
regularity and clipping constants L and K](hyp:L,K). Suppose [each target has
the specified finite component support](hyp:hsupp), [the components admit
Lipschitz homeomorphic cube charts with constant L](hyp:hcharts), [the conditional
component laws satisfy lower-bound domination with constant L](hyp:hdom),
[their pullbacks vanish on the boundary with constant L](hyp:hboundary),
[the targets lie almost surely in their radius-K cubes](hyp:hbox),
[Yarotsky coordinate approximation is available](hyp:hgate), [D is positive](hyp:hD),
[all block dimensions are at most D](hyp:hdims), and [all chart dimensions are at
most D](hyp:hchartdims); then [there exist positive minimum width factors, a
positive error constant A, a minimum depth of at least one, and a temperature
threshold strictly between zero and one such that every larger pair of width
factors, every larger pair of depths, and every positive temperature below the
threshold admit generators in the prescribed clipped architecture, with outputs
in the radius-K cubes and total marginal Wasserstein-1 error at most A times
the sum of the two depths to the power minus two over D and the temperature
times one minus its logarithm](goal). -/
lemma clipped_generators_architecture_budgets {b : ℕ} (dims : Fin b → ℕ)
    (P : ∀ j, ProbabilityMeasure (L1Vec (dims j)))
    (counts : Fin b → ℕ) (S : ∀ j, Fin (counts j) → Set (L1Vec (dims j)))
    (dC : ∀ j, Fin (counts j) → ℕ) (L K : ℝ≥0)
    (hsupp : ∀ j, SupportFiniteComponents (P j : Measure _) (S j))
    (hcharts : ∀ j, ComponentsLipschitzHomeomorphic (S j) (dC j) L)
    (hdom : ∀ j i, LowerBoundDomination (d := dC j i)
      (ProbabilityTheory.cond (P j : Measure _) (S j i)) (S j i) L)
    (hboundary : ∀ j i, PullbackVanishesOnBoundary (d := dC j i)
      (ProbabilityTheory.cond (P j : Measure _) (S j i)) (S j i) L)
    (hbox : ∀ j, ∀ᵐ x ∂(P j : Measure _), x ∈ boundedCube (dims j) K)
    (hgate : YarotskyCoordinateApprox)
    (D : ℕ) (hD : 0 < D) (hdims : ∀ j, dims j ≤ D)
    (hchartdims : ∀ j i, dC j i ≤ D) :
    ∃ a1 a2 : ℕ, 0 < a1 ∧ 0 < a2 ∧ ∃ A : ℝ, 0 < A ∧
      ∃ B : ℕ, 1 ≤ B ∧ ∃ tb : ℝ, 0 < tb ∧ tb < 1 ∧
      ∀ c1 c2 : ℕ, a1 ≤ c1 → a2 ≤ c2 →
      ∀ L1 L2 : ℕ, B ≤ L1 → B ≤ L2 → ∀ tau : ℝ, 0 < tau → tau < tb →
        ∃ g : ∀ j, ((Fin (counts j) → ℝ) × (Fin (counts j) → ℝ)) → L1Vec (dims j),
          (∀ j, g j ∈ generatorClassN counts dC K D c1 c2
            (fun _ => L1) (fun _ => L2) (fun _ => tau) 0 j) ∧
          (∀ j x, g j x ∈ boundedCube (dims j) K) ∧
          (∑ j, wasserstein1 (P j : Measure _)
            ((generatorInputLaw (counts j)).map (g j))) ≤
            ENNReal.ofReal (A * ((L1 : ℝ)^(-(2 : ℝ)/D) +
              (L2 : ℝ)^(-(2 : ℝ)/D) + tau * (1 - Real.log tau))) := by
  classical
  obtain ⟨a1, a2, ha1, ha2, E, hE, B, hB, tb, htb, htb1, happ⟩ :=
    deep_generators_common_budgets dims P counts S dC L hsupp hcharts hdom hboundary
      hgate D hD hdims hchartdims
  refine ⟨a1, a2, ha1, ha2, (b + 1 : ℝ) * E, by positivity,
    B, hB, tb, htb, htb1, ?_⟩
  intro c1 c2 hc1 hc2 L1 L2 hL1 hL2 tau htau htaub
  obtain ⟨Q, hp, hcube, hzero, herr⟩ := happ L1 L2 hL1 hL2 tau htau htaub
  let R := fun j => (Q j).widen (Nat.mul_le_mul_right D hc1)
    (Nat.mul_le_mul_right (D^2) hc2)
  let g := fun j => truncK K ∘ (R j).eval
  have hr : ∀ j, (R j).eval = (Q j).eval := fun _ => rfl
  have hrate : 0 ≤ (L1 : ℝ)^(-(2 : ℝ)/D) +
      (L2 : ℝ)^(-(2 : ℝ)/D) + tau * (1 - Real.log tau) := by
    have hlog : Real.log tau ≤ 0 := Real.log_nonpos htau.le (htaub.trans htb1).le
    exact add_nonneg (add_nonneg (Real.rpow_nonneg (Nat.cast_nonneg L1) _)
      (Real.rpow_nonneg (Nat.cast_nonneg L2) _))
      (mul_nonneg htau.le (by linarith))
  have herror (j : Fin b) : wasserstein1 (P j : Measure _)
      ((generatorInputLaw (counts j)).map (g j)) ≤
      ENNReal.ofReal (E * ((L1 : ℝ)^(-(2 : ℝ)/D) +
        (L2 : ℝ)^(-(2 : ℝ)/D) + tau * (1 - Real.log tau))) := by
    refine (generator_truncK_wasserstein_le (P j) K (hbox j) (R j)).trans ?_
    change wasserstein1 (P j : Measure _) (generatorLaw (Q j)) ≤ _
    let := generatorInputLaw_probability (counts j)
    let nu : ProbabilityMeasure (L1Vec (dims j)) :=
      ⟨generatorLaw (Q j), Measure.isProbabilityMeasure_map (by fun_prop)⟩
    rw [show generatorLaw (Q j) = (nu : Measure _) from rfl, wasserstein1_symm]
    convert herr j using 1 <;> congr 1 <;> ring
  refine ⟨g, fun j => ⟨R j, rfl⟩, ?_, ?_⟩
  · intro j x k
    exact abs_le.mpr (coordinateClamp_mapsTo (-(K : ℝ)) K (by linarith [K.coe_nonneg]) ((R j).eval x) k)
  · calc
      _ ≤ ∑ _j : Fin b, ENNReal.ofReal (E * ((L1 : ℝ)^(-(2 : ℝ)/D) +
          (L2 : ℝ)^(-(2 : ℝ)/D) + tau * (1 - Real.log tau))) :=
        Finset.sum_le_sum (fun j _ => herror j)
      _ = ENNReal.ofReal ((b : ℝ) * (E * ((L1 : ℝ)^(-(2 : ℝ)/D) +
          (L2 : ℝ)^(-(2 : ℝ)/D) + tau * (1 - Real.log tau)))) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => mul_nonneg hE.le hrate)]
        simp
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith [mul_nonneg hE.le hrate])

-- @node: canonical_clipped_generators_architecture_budgets
/-- For a canonical causal model, take [nonnegative bounding and chart constants
K and Lchart](hyp:K,Lchart), [component sets for each latent block](hyp:S), and
[their chart dimensions](hyp:dC). If [the model's variables are bounded at
K](hyp:hbound), [its maximum latent dimension is positive](hyp:hD), [each block
law has the specified finite component support](hyp:hsupp), [the components
admit Lipschitz homeomorphic cube charts with constant Lchart](hyp:hcharts),
[conditional component laws satisfy lower-bound domination with that
constant](hyp:hdom), [their pullbacks vanish on the boundary with that
constant](hyp:hboundary), and [Yarotsky coordinate approximation is
available](hyp:hgate), [there exist positive minimum width factors, a positive
error constant A, a minimum depth of at least one, and a temperature threshold
strictly between zero and one such that all larger width factors and depths
and all positive temperatures below the threshold admit generators in the
prescribed clipped architecture, with radius-K bounded outputs and total
Wasserstein-1 error for the block laws at most A times the sum of the two depths
to the power minus two over the maximum latent dimension and the temperature
times one minus its logarithm](goal). -/
lemma canonical_clipped_generators_architecture_budgets
    (M : CanonicalSCM kind dims dag G C) (K Lchart : ℝ≥0)
    (counts : Fin b → ℕ) (S : ∀ j, Fin (counts j) → Set (L1Vec (dims j)))
    (dC : ∀ j, Fin (counts j) → ℕ)
    (hbound : VariablesBoundedAt M.toEuclideanSCM K)
    (hD : 0 < maxLatentDim M.toEuclideanSCM)
    (hsupp : ∀ j, SupportFiniteComponents (M.blockLaw j : Measure _) (S j))
    (hcharts : ∀ j, ComponentsLipschitzHomeomorphic (S j) (dC j) Lchart)
    (hdom : ∀ j i, LowerBoundDomination (d := dC j i)
      (ProbabilityTheory.cond (M.blockLaw j : Measure _) (S j i)) (S j i) Lchart)
    (hboundary : ∀ j i, PullbackVanishesOnBoundary (d := dC j i)
      (ProbabilityTheory.cond (M.blockLaw j : Measure _) (S j i)) (S j i) Lchart)
    (hgate : YarotskyCoordinateApprox) :
    ∃ a1 a2 : ℕ, 0 < a1 ∧ 0 < a2 ∧ ∃ A : ℝ, 0 < A ∧
      ∃ B : ℕ, 1 ≤ B ∧ ∃ tb : ℝ, 0 < tb ∧ tb < 1 ∧
      ∀ c1 c2 : ℕ, a1 ≤ c1 → a2 ≤ c2 →
      ∀ L1 L2 : ℕ, B ≤ L1 → B ≤ L2 → ∀ tau : ℝ, 0 < tau → tau < tb →
        ∃ g : ∀ j, ((Fin (counts j) → ℝ) × (Fin (counts j) → ℝ)) → L1Vec (dims j),
          (∀ j, g j ∈ generatorClassN counts dC K (maxLatentDim M.toEuclideanSCM) c1 c2
            (fun _ => L1) (fun _ => L2) (fun _ => tau) 0 j) ∧
          (∀ j x, g j x ∈ boundedCube (dims j) K) ∧
          (∑ j, wasserstein1 (M.blockLaw j : Measure _)
            ((generatorInputLaw (counts j)).map (g j))) ≤
            ENNReal.ofReal (A * ((L1 : ℝ)^(-(2 : ℝ)/maxLatentDim M.toEuclideanSCM) +
              (L2 : ℝ)^(-(2 : ℝ)/maxLatentDim M.toEuclideanSCM) +
              tau * (1 - Real.log tau))) := by
  have hchartdims (j : Fin b) (i : Fin (counts j)) :
      dC j i ≤ maxLatentDim M.toEuclideanSCM := by
    obtain ⟨f, hf⟩ := hcharts j i
    exact (cube_chart_dimension_le_ambient f).trans
      (Finset.le_sup (Finset.mem_univ j))
  exact clipped_generators_architecture_budgets dims M.blockLaw counts S dC Lchart K
    hsupp hcharts hdom hboundary (canonical_blockLaw_ae_boundedCube M K hbound)
    hgate (maxLatentDim M.toEuclideanSCM) hD
    (fun j => Finset.le_sup (Finset.mem_univ j)) hchartdims

end Papers.TbsNeuralCausalPi
