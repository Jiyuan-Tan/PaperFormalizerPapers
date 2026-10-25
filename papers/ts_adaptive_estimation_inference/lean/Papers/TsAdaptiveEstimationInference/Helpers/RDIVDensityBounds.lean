module
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVPerturbation
/-! Bounded conditional operators and the global Hellinger rate for RDIV.

Bounds on hypotheses are needed only on the common density support. The
normalization event is shared by every hypothesis, so the uniform conclusions
below do not require an intersection over an uncountable hypothesis class.
-/
public section

namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory

variable {A Z : Type*} [MeasurableSpace A]

/-- If [u is strongly measurable up to a null set](hyp:hu), [the density section
at z is integrable](hyp:hg) and [nonnegative everywhere](hyp:hg0), [the absolute
value of u is bounded by B on the common support](hyp:huB), and [the density
vanishes outside that support](hyp:hgSupport), then [u times the density section
at z is integrable](goal). -/
-- @node: rdiv_density_weighted_integrable_support
lemma rdiv_density_weighted_integrable_support
    (μ : Measure A) (g : A → Z → ℝ) (u : A → ℝ) (B : ℝ)
    (support : Set (A × Z)) (z : Z)
    (hu : AEStronglyMeasurable u μ) (hg : Integrable (fun x => g x z) μ)
    (hg0 : ∀ x, 0 ≤ g x z)
    (huB : ∀ p ∈ support, |u p.1| ≤ B)
    (hgSupport : ∀ p ∉ support, g p.1 p.2 = 0) :
    Integrable (fun x => u x * g x z) μ := by
  apply (hg.const_mul B).mono' (hu.mul hg.aestronglyMeasurable)
  filter_upwards [] with x
  change |u x * g x z| ≤ B * g x z
  rw [abs_mul, abs_of_nonneg (hg0 x)]
  by_cases hs : (x, z) ∈ support
  · exact mul_le_mul_of_nonneg_right (huB (x, z) hs) (hg0 x)
  · rw [hgSupport (x, z) hs, mul_zero, mul_zero]

/-- If [u and v are strongly measurable up to null sets](hyp:hu,hv), [the density
section at z is integrable](hyp:hg) and [nonnegative everywhere](hyp:hg0),
[both functions have absolute value at most B on the common support](hyp:huB,hvB),
and [the density vanishes outside that support](hyp:hgSupport), then [the density
operator applied to u minus v at z equals the difference of its values on u and v](goal). -/
-- @node: rdiv_density_operator_sub_support
lemma rdiv_density_operator_sub_support
    (μ : Measure A) (g : A → Z → ℝ) (u v : A → ℝ) (B : ℝ)
    (support : Set (A × Z)) (z : Z)
    (hu : AEStronglyMeasurable u μ) (hv : AEStronglyMeasurable v μ)
    (hg : Integrable (fun x => g x z) μ) (hg0 : ∀ x, 0 ≤ g x z)
    (huB : ∀ p ∈ support, |u p.1| ≤ B)
    (hvB : ∀ p ∈ support, |v p.1| ≤ B)
    (hgSupport : ∀ p ∉ support, g p.1 p.2 = 0) :
    densityOperator μ g (u - v) z = densityOperator μ g u z - densityOperator μ g v z := by
  have hui := rdiv_density_weighted_integrable_support μ g u B support z
    hu hg hg0 huB hgSupport
  have hvi := rdiv_density_weighted_integrable_support μ g v B support z
    hv hg hg0 hvB hgSupport
  simp only [densityOperator, Pi.sub_apply, sub_mul]
  exact integral_sub hui hvi

variable {𝒲 : Type*} [MeasurableSpace 𝒲] [MeasurableSpace Z]
    (V : IVWorld 𝒲 A Z)

/-- If [the density class contains the true density and consists of measurable,
nonnegative conditional densities normalized almost everywhere](hyp:hDensity),
[the true density has positive lower bound c₀ on the common support and class
densities have upper bound CG there and vanish outside it](hyp:hBounds),
[every hypothesis has absolute value at most B on that support](hyp:hHyp),
[B is nonnegative](hyp:hB), and [g belongs to the density class](hyp:hg), then
[for almost every instrument value, the density operator under g has absolute
value at most B simultaneously for every hypothesis](goal). -/
-- @node: rdiv_hypothesis_density_operator_bounded
lemma rdiv_hypothesis_density_operator_bounded
    (μ : Measure A) (G : Set (A → Z → ℝ)) (g₀ g : A → Z → ℝ)
    (support : Set (A × Z)) (B c₀ CG : ℝ)
    (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hHyp : HypothesisClassBounded V support B) (hB : 0 ≤ B) (hg : g ∈ G) :
    ∀ᵐ z ∂V.law.map V.zOf, ∀ h ∈ V.H,
      |densityOperator μ g (primalVersion V h) z| ≤ B := by
  filter_upwards [rdiv_density_integrable_of_realizable V μ G g₀ g hDensity hg,
    (hDensity.2 g hg).2.2] with z hgi hgn
  intro h hh
  exact rdiv_density_operator_support_bound μ g (primalVersion V h) B support hB
    (V.primal_measurable h) (hHyp h hh) (hBounds.2.2.2.2 g hg) z hgi
    (fun x => (hDensity.2 g hg).2.1 x z) hgn

/-- If [the density class contains the true density and consists of measurable,
nonnegative conditional densities normalized almost everywhere](hyp:hDensity),
[g belongs to this class](hyp:hg), and [the squared Hellinger discrepancy between
g and the true density is strongly measurable up to an instrument-law null set](hyp:hm),
then [this discrepancy is integrable over the instrument distribution](goal). -/
-- @node: rdiv_density_hellinger_integrable
lemma rdiv_density_hellinger_integrable
    (μ : Measure A) (G : Set (A → Z → ℝ)) (g₀ g : A → Z → ℝ)
    (hDensity : DensityRealizable V μ G g₀) (hg : g ∈ G)
    (hm : AEStronglyMeasurable
      (fun z => hellingerSqDensity μ (fun x => g x z) (fun x => g₀ x z))
      (V.law.map V.zOf)) :
    Integrable (fun z => hellingerSqDensity μ (fun x => g x z) (fun x => g₀ x z))
      (V.law.map V.zOf) := by
  apply (integrable_const (2 : ℝ)).mono' hm
  filter_upwards [rdiv_density_integrable_of_realizable V μ G g₀ g hDensity hg,
    rdiv_density_integrable_of_realizable V μ G g₀ g₀ hDensity hDensity.1,
    (hDensity.2 g hg).2.2, (hDensity.2 g₀ hDensity.1).2.2] with z hgi hg₀i hgn hg₀n
  have hH := Causalean.Stat.Minimax.hellingerSqDensity_bounds μ
    (fun x => g x z) (fun x => g₀ x z) hgi hg₀i
    (fun x => (hDensity.2 g hg).2.1 x z)
    (fun x => (hDensity.2 g₀ hDensity.1).2.1 x z) hgn hg₀n
  change ‖Causalean.Stat.hellingerSqDensity μ (fun x => g x z) (fun x => g₀ x z)‖ ≤ 2
  rw [Real.norm_eq_abs, abs_of_nonneg hH.1]
  exact hH.2

/-- Suppose [the density class contains the true density and consists of measurable,
nonnegative conditional densities normalized almost everywhere](hyp:hDensity),
[the true density is bounded below by positive c₀ on the common support and class
densities are bounded above by positive CG there and vanish outside it](hyp:hBounds),
[all hypotheses are bounded in absolute value by B on that support](hyp:hHyp),
[B is nonnegative](hyp:hB), [g belongs to the density class](hyp:hg), and
[C and δ are nonnegative](hyp:hC,hδ). If [the squared Hellinger discrepancy is
strongly measurable up to a null set](hyp:hHm), [its instrument-law integral is
at most Cδ²](hyp:hRate), and [each hypothesis's operator difference between g
and the true density is strongly measurable up to a null set](hyp:hError), then
[every hypothesis has operator error in instrument-law L² norm at most
2B√C times δ](goal). -/
-- @node: rdiv_hypothesis_operator_global_rate
lemma rdiv_hypothesis_operator_global_rate
    (μ : Measure A) (G : Set (A → Z → ℝ)) (g₀ g : A → Z → ℝ)
    (support : Set (A × Z)) (B c₀ CG C δ : ℝ)
    (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hHyp : HypothesisClassBounded V support B) (hB : 0 ≤ B)
    (hg : g ∈ G) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hHm : AEStronglyMeasurable
      (fun z => hellingerSqDensity μ (fun x => g x z) (fun x => g₀ x z))
      (V.law.map V.zOf))
    (hRate : (∫ z, hellingerSqDensity μ (fun x => g x z) (fun x => g₀ x z)
      ∂V.law.map V.zOf) ≤ C * δ ^ 2)
    (hError : ∀ h ∈ V.H, AEStronglyMeasurable
      (densityOperator μ g (primalVersion V h) - densityOperator μ g₀ (primalVersion V h))
      (V.law.map V.zOf)) :
    ∀ h ∈ V.H, inputL2Norm (V.law.map V.zOf)
      (densityOperator μ g (primalVersion V h) - densityOperator μ g₀ (primalVersion V h)) ≤
      (2 * B * Real.sqrt C) * δ := by
  intro h hh
  have hb := rdiv_hypothesis_operator_global_bound V μ G g₀ g support B c₀ CG
    hDensity hBounds hHyp hB hg h hh (hError h hh)
    (rdiv_density_hellinger_integrable V μ G g₀ g hDensity hg hHm)
  have hs : Real.sqrt (∫ z, hellingerSqDensity μ (fun x => g x z) (fun x => g₀ x z)
      ∂V.law.map V.zOf) ≤ Real.sqrt C * δ := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt hC]
    exact hRate
  exact hb.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * B))

end Papers.TsAdaptiveEstimationInference
