module

public import Papers.OaiCapacityCriterionState.Helpers.LocalCoordinates
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Finite symmetry averaging for the quadratic cancellation

Averaging over the twelve even state permutations retains precisely the second
and signed third moments used in the local quadratic bound.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace OaiCapacityCriterionState

-- @node: posterior_continuous_integrable
/-- If [a real-valued function of a four-state probability vector is
continuous](hyp:hf), [it is integrable under any posterior law](goal). -/
lemma posterior_continuous_integrable (mu : PosteriorLaw)
    {f : (Fin 4 → ℝ) → ℝ} (hf : Continuous f) :
    Integrable f (mu : Measure (Fin 4 → ℝ)) := by
  let : IsProbabilityMeasure (mu : Measure (Fin 4 → ℝ)) := mu.property.1
  have hi := hf.continuousOn.integrableOn_compact (μ := (mu : Measure (Fin 4 → ℝ))) (isCompact_stdSimplex ℝ (Fin 4))
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr mu.property.2.1)] at hi

-- @node: posterior_prod_continuous_integrable
/-- If [a real-valued function of a pair of four-state probability vectors is
continuous](hyp:hf), [it is integrable under the product of any two posterior
laws](goal). -/
lemma posterior_prod_continuous_integrable (mu nu : PosteriorLaw)
    {f : (Fin 4 → ℝ) × (Fin 4 → ℝ) → ℝ} (hf : Continuous f) :
    Integrable f ((mu : Measure (Fin 4 → ℝ)).prod (nu : Measure (Fin 4 → ℝ))) := by
  let : IsProbabilityMeasure (mu : Measure (Fin 4 → ℝ)) := mu.property.1
  let : IsProbabilityMeasure (nu : Measure (Fin 4 → ℝ)) := nu.property.1
  have hp := (Measure.quasiMeasurePreserving_fst
    (ν := (nu : Measure (Fin 4 → ℝ)))).ae (ae_iff.mpr mu.property.2.1)
  have hq := (Measure.quasiMeasurePreserving_snd
    (μ := (mu : Measure (Fin 4 → ℝ)))).ae (ae_iff.mpr nu.property.2.1)
  have hs : ∀ᵐ pq ∂((mu : Measure (Fin 4 → ℝ)).prod (nu : Measure (Fin 4 → ℝ))),
      pq ∈ (stdSimplex ℝ (Fin 4)) ×ˢ (stdSimplex ℝ (Fin 4)) := by
    filter_upwards [hp, hq] with pq hp hq
    exact ⟨hp, hq⟩
  have hi := hf.continuousOn.integrableOn_compact
    (μ := (mu : Measure (Fin 4 → ℝ)).prod (nu : Measure (Fin 4 → ℝ)))
    ((isCompact_stdSimplex ℝ (Fin 4)).prod (isCompact_stdSimplex ℝ (Fin 4)))
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hs] at hi

-- @node: momentSymmetryPerm
/-- For [an index k among twelve possibilities](hyp:k), the [moment symmetry
permutation](goal) is the k-th even permutation of the four states in the fixed
enumeration, beginning with the identity. -/
noncomputable def momentSymmetryPerm (k : Fin 12) : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective (![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0], ![0, 2, 3, 1], ![2, 0, 1, 3], ![3, 1, 0, 2], ![1, 3, 2, 0], ![0, 3, 1, 2], ![3, 0, 2, 1], ![1, 2, 0, 3], ![2, 1, 3, 0]] k) (by fin_cases k <;> decide)

-- @node: quadraticIntegrand
/-- For [a three-component coordinate vector x](hyp:x) and [a three-component
coordinate vector y](hyp:y), the [quadratic integrand](goal) is the squared
Euclidean length of the sum of x, y, and their mixed coordinate vector, multiplied by one
minus the inner product of x and y. -/
def quadraticIntegrand (x y : Fin 3 → ℝ) : ℝ :=
  (∑ i : Fin 3, (x i + y i + mixedCoords x y i) ^ 2) *
    (1 - ∑ i : Fin 3, x i * y i)

-- @node: quadratic_symmetry_average
/-- For any two four-component vectors p and q, [summing the quadratic integrand
over the twelve even permutations of q gives twelve times
Q(p) + Q(q) − 4(t(p)Q(q) + Q(p)t(q)) − 6t(p)t(q), where Q is the quadratic
statistic and t is the product of the three posterior coordinates](goal). -/
lemma quadratic_symmetry_average (p q : Fin 4 → ℝ) :
    (∑ k : Fin 12, quadraticIntegrand (postCoords p)
      (postCoords (q ∘ momentSymmetryPerm k))) =
    12 * (quadStat p + quadStat q -
      4 * ((postCoords p 0 * postCoords p 1 * postCoords p 2) * quadStat q +
        quadStat p * (postCoords q 0 * postCoords q 1 * postCoords q 2)) -
      6 * (postCoords p 0 * postCoords p 1 * postCoords p 2) *
        (postCoords q 0 * postCoords q 1 * postCoords q 2)) := by
  have hcoords (k : Fin 12) : postCoords (q ∘ momentSymmetryPerm k) =
      ![![postCoords q 0, postCoords q 1, postCoords q 2], ![postCoords q 0, -postCoords q 1, -postCoords q 2], ![-postCoords q 0, postCoords q 1, -postCoords q 2], ![-postCoords q 0, -postCoords q 1, postCoords q 2], ![postCoords q 1, postCoords q 2, postCoords q 0], ![postCoords q 1, -postCoords q 2, -postCoords q 0], ![-postCoords q 1, postCoords q 2, -postCoords q 0], ![-postCoords q 1, -postCoords q 2, postCoords q 0], ![postCoords q 2, postCoords q 0, postCoords q 1], ![postCoords q 2, -postCoords q 0, -postCoords q 1], ![-postCoords q 2, postCoords q 0, -postCoords q 1], ![-postCoords q 2, -postCoords q 0, postCoords q 1]] k := by
    fin_cases k <;> ext i <;> fin_cases i <;>
      simp [momentSymmetryPerm, postCoords, coordMatrix, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ, Function.comp_def, Equiv.ofBijective_apply] <;> ring
  simp_rw [hcoords]
  simp [quadraticIntegrand, quadStat, mixedCoords, Fin.sum_univ_succ]
  ring

-- @node: quadratic_integral_symmetry
/-- If [a posterior law is invariant under state permutations](hyp:hsym),
[integrating the quadratic integrand against that law is unchanged when its
second vector is transformed by any of the twelve moment symmetry
permutations](goal). -/
lemma quadratic_integral_symmetry (nu : PosteriorLaw) (hsym : IsSymmetricLaw nu)
    (p : Fin 4 → ℝ) (k : Fin 12) :
    (∫ q, quadraticIntegrand (postCoords p) (postCoords (q ∘ momentSymmetryPerm k))
      ∂(nu : Measure (Fin 4 → ℝ))) =
    ∫ q, quadraticIntegrand (postCoords p) (postCoords q)
      ∂(nu : Measure (Fin 4 → ℝ)) := by
  have hm : Measurable (fun q : Fin 4 → ℝ => q ∘ momentSymmetryPerm k) := by fun_prop
  have hf : Measurable (fun q => quadraticIntegrand (postCoords p) (postCoords q)) := by
    unfold quadraticIntegrand mixedCoords postCoords Matrix.mulVec dotProduct
    fun_prop
  simpa only [Function.comp_def] using
    (integral_map hm.aemeasurable hf.aestronglyMeasurable).symm.trans
      (congrArg (fun m : Measure (Fin 4 → ℝ) =>
        ∫ q, quadraticIntegrand (postCoords p) (postCoords q) ∂m)
        (hsym (momentSymmetryPerm k)))

-- @node: posterior_integral_affine_moments
/-- Under any posterior law, [the expectation of a constant a plus b times the
quadratic statistic plus c times the product of the three posterior coordinates
equals a plus b times the quadratic information plus c times the signed third
moment](goal). -/
lemma posterior_integral_affine_moments (mu : PosteriorLaw) (a b c : ℝ) :
    (∫ p, a + b * quadStat p + c *
        (postCoords p 0 * postCoords p 1 * postCoords p 2)
      ∂(mu : Measure (Fin 4 → ℝ))) = a + b * quadInfo mu + c * thirdMoment mu := by
  let : IsProbabilityMeasure (mu : Measure (Fin 4 → ℝ)) := mu.property.1
  have hA : Integrable quadStat (mu : Measure (Fin 4 → ℝ)) :=
    posterior_continuous_integrable mu (by
      unfold quadStat postCoords Matrix.mulVec dotProduct
      fun_prop)
  have ht : Integrable (fun p => postCoords p 0 * postCoords p 1 * postCoords p 2)
      (mu : Measure (Fin 4 → ℝ)) :=
    posterior_continuous_integrable mu (by
      unfold postCoords Matrix.mulVec dotProduct
      fun_prop)
  erw [integral_add ((integrable_const a).add (hA.const_mul b)) (ht.const_mul c),
    integral_add (integrable_const a) (hA.const_mul b),
    integral_const_mul, integral_const_mul]
  simp [quadInfo, thirdMoment]

-- @node: quadratic_integral_average
/-- If [a posterior law ν is invariant under state permutations](hyp:hsym),
[the expected quadratic integrand with first vector p equals
Q(p) + (1 − 4t(p))I(ν) + (−4Q(p) − 6t(p))M₃(ν), where Q is the quadratic
statistic, t is the product of the three posterior coordinates, I is quadratic
information, and M₃ is the signed third moment](goal). -/
lemma quadratic_integral_average (nu : PosteriorLaw) (hsym : IsSymmetricLaw nu)
    (p : Fin 4 → ℝ) :
    (∫ q, quadraticIntegrand (postCoords p) (postCoords q)
      ∂(nu : Measure (Fin 4 → ℝ))) =
    quadStat p + (1 - 4 * (postCoords p 0 * postCoords p 1 * postCoords p 2)) *
      quadInfo nu + (-4 * quadStat p -
        6 * (postCoords p 0 * postCoords p 1 * postCoords p 2)) * thirdMoment nu := by
  have hi (k : Fin 12) : Integrable (fun q => quadraticIntegrand (postCoords p)
      (postCoords (q ∘ momentSymmetryPerm k))) (nu : Measure (Fin 4 → ℝ)) := by
    apply posterior_continuous_integrable
    unfold quadraticIntegrand mixedCoords postCoords Matrix.mulVec dotProduct
    fun_prop
  have havg (q : Fin 4 → ℝ) :
      (∑ k : Fin 12, quadraticIntegrand (postCoords p)
        (postCoords (q ∘ momentSymmetryPerm k))) =
      12 * (quadStat p + (1 - 4 * (postCoords p 0 * postCoords p 1 * postCoords p 2)) *
        quadStat q + (-4 * quadStat p -
          6 * (postCoords p 0 * postCoords p 1 * postCoords p 2)) *
          (postCoords q 0 * postCoords q 1 * postCoords q 2)) := by
    rw [quadratic_symmetry_average]
    ring
  have he : (12 : ℝ) * (∫ q, quadraticIntegrand (postCoords p) (postCoords q)
      ∂(nu : Measure (Fin 4 → ℝ))) =
      12 * (quadStat p + (1 - 4 * (postCoords p 0 * postCoords p 1 * postCoords p 2)) *
        quadInfo nu + (-4 * quadStat p -
          6 * (postCoords p 0 * postCoords p 1 * postCoords p 2)) * thirdMoment nu) := by
    calc
      _ = ∫ q, (∑ k : Fin 12, quadraticIntegrand (postCoords p)
          (postCoords (q ∘ momentSymmetryPerm k))) ∂(nu : Measure (Fin 4 → ℝ)) := by
        rw [integral_finsetSum Finset.univ (fun k _ => hi k)]
        simp [quadratic_integral_symmetry nu hsym]
      _ = _ := by
        simp_rw [havg]
        rw [integral_const_mul, posterior_integral_affine_moments]
  linarith

end OaiCapacityCriterionState
