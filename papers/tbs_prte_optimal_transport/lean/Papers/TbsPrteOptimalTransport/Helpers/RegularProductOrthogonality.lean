module
public import Papers.TbsPrteOptimalTransport.Helpers.Orthogonality
/-! Fractional-interval product weights cancel against their centered component scores. -/
public section
set_option linter.unusedSectionVars false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory

universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- These identities retain the structural-zero convention at invalid indices.
-- In the continuous score, the component index is j-1, not j.
-- @node: continuous_regular_product_weight_path
/-- [Adding t times a direction to the continuous-outcome regular product weights
changes the product score by t times that direction's value times the difference
between the component score and its plug-in value at policy index j minus one](goal). -/
lemma continuous_regular_product_weight_path (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e : NuisanceCont L) (d : RegularIndex L → X → ℝ)
    (k j : ℕ) (o : Obs X Z) (t : ℝ) :
    psiProd M phi dphi L
      {e with gamma := fun a x => e.gamma a x + t * d a x} k j o =
    psiProd M phi dphi L e k j o + t * regularValue d k j o.1 *
      (contScoreComponents M phi dphi L e k (j-1) o - contJ L e k (j-1) o.1) := by
  have hs : contScoreComponents M phi dphi L
      {e with gamma := fun a x => e.gamma a x + t * d a x} k (j-1) o =
      contScoreComponents M phi dphi L e k (j-1) o := rfl
  have hj : contJ L {e with gamma := fun a x => e.gamma a x + t * d a x}
      k (j-1) o.1 = contJ L e k (j-1) o.1 := rfl
  simp only [psiProd, hs, hj, regularValue]
  split_ifs <;> ring

-- @node: binary_regular_product_weight_path
/-- [Adding t times a direction to the binary-outcome regular product weights changes
the product score by t times that direction's value times the difference between the
binary component score and the fitted negative hinge at policy index j](goal). -/
lemma binary_regular_product_weight_path (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e : NuisanceBin L) (d : RegularIndex L → X → ℝ)
    (k j : ℕ) (o : Obs X Z) (t : ℝ) :
    psiProdBin phi dphi L
      {e with gamma := fun a x => e.gamma a x + t * d a x} k j o =
    psiProdBin phi dphi L e k j o + t * regularValue d k j o.1 *
      (binScoreComponents phi dphi L e k j o - hMinus phi L e k j o.1) := by
  have hs : binScoreComponents phi dphi L
      {e with gamma := fun a x => e.gamma a x + t * d a x} k j o =
      binScoreComponents phi dphi L e k j o := rfl
  have hj : hMinus phi L {e with gamma := fun a x => e.gamma a x + t * d a x}
      k j o.1 = hMinus phi L e k j o.1 := rfl
  simp only [psiProdBin, hs, hj, regularValue]
  split_ifs <;> ring

-- The tower identity gives exact cancellation for every t; no exchange of
-- differentiation and integration or regularity of the indicator is needed.
-- @node: continuous_regular_product_weight_orthogonality
/-- Suppose [the conditioning information is contained in the observation sigma-algebra](hyp:hm),
[the weight direction is strongly measurable with respect to that information](hyp:hd),
[the continuous component score](hyp:hs) and [its plug-in value](hyp:hj) are integrable,
[the plug-in value is strongly measurable with respect to the conditioning information](hyp:hjm),
and [the component score's conditional expectation equals its plug-in value almost
surely](hyp:hcond). If [the baseline product score](hyp:hbase) and [the direction times
the centered component score](hyp:hres) are integrable, [the population product-score
mean has derivative zero at zero along the path perturbing only its regular product weights](goal). -/
lemma continuous_regular_product_weight_orthogonality (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e : NuisanceCont L) (d : RegularIndex L → X → ℝ)
    (k j : ℕ) (m : MeasurableSpace (Obs X Z)) (hm : m ≤ Prod.instMeasurableSpace)
    [SigmaFinite ((observationLaw M).trim hm)]
    (hd : StronglyMeasurable[m] (fun o : Obs X Z => regularValue d k j o.1))
    (hs : Integrable (fun o => contScoreComponents M phi dphi L e k (j-1) o)
      (observationLaw M))
    (hj : Integrable (fun o : Obs X Z => contJ L e k (j-1) o.1) (observationLaw M))
    (hjm : StronglyMeasurable[m] (fun o : Obs X Z => contJ L e k (j-1) o.1))
    (hcond : (observationLaw M)[(fun o => contScoreComponents M phi dphi L e
      k (j-1) o) | m] =ᵐ[observationLaw M] (fun o => contJ L e k (j-1) o.1))
    (hbase : Integrable (fun o => psiProd M phi dphi L e k j o) (observationLaw M))
    (hres : Integrable (fun o => regularValue d k j o.1 *
      (contScoreComponents M phi dphi L e k (j-1) o - contJ L e k (j-1) o.1))
      (observationLaw M)) :
    HasDerivAt (fun t : ℝ => ∫ o, psiProd M phi dphi L
      {e with gamma := fun a x => e.gamma a x + t * d a x} k j o
      ∂observationLaw M) 0 0 := by
  let : MeasurableSpace (Obs X Z) := Prod.instMeasurableSpace
  have hz := score_weighted_conditional_residual_zero (observationLaw M) m hm
    (fun o => regularValue d k j o.1)
    (fun o => contScoreComponents M phi dphi L e k (j-1) o)
    (fun o => contJ L e k (j-1) o.1) hd hs hj hres hcond hjm
  have heq : (fun t : ℝ => ∫ o, psiProd M phi dphi L
      {e with gamma := fun a x => e.gamma a x + t * d a x} k j o
      ∂observationLaw M) = (fun _ : ℝ => ∫ o, psiProd M phi dphi L e k j o
      ∂observationLaw M) := by
    funext t
    simp_rw [continuous_regular_product_weight_path]
    simp_rw [mul_assoc]
    rw [integral_add hbase (hres.const_mul t), integral_const_mul, hz,
      mul_zero, add_zero]
  rw [heq]
  exact hasDerivAt_const 0 _

-- @node: binary_regular_product_weight_orthogonality
/-- Suppose [the conditioning information is contained in the observation sigma-algebra](hyp:hm),
[the weight direction is strongly measurable with respect to that information](hyp:hd),
[the binary component score](hyp:hs) and [the fitted negative hinge](hyp:hj) are integrable,
[the hinge is strongly measurable with respect to the conditioning information](hyp:hjm),
and [the component score's conditional expectation equals the hinge almost surely](hyp:hcond).
If [the baseline product score](hyp:hbase) and [the direction times the component score
minus the hinge](hyp:hres) are integrable, [the population binary product-score mean
has derivative zero at zero along the path perturbing only its regular product weights](goal). -/
lemma binary_regular_product_weight_orthogonality (phi dphi : Z → X → ℝ → ℝ)
    (L : LevelData Z X) (e : NuisanceBin L) (d : RegularIndex L → X → ℝ)
    (k j : ℕ) (m : MeasurableSpace (Obs X Z)) (hm : m ≤ Prod.instMeasurableSpace)
    [SigmaFinite ((observationLaw M).trim hm)]
    (hd : StronglyMeasurable[m] (fun o : Obs X Z => regularValue d k j o.1))
    (hs : Integrable (fun o => binScoreComponents phi dphi L e k j o)
      (observationLaw M))
    (hj : Integrable (fun o : Obs X Z => hMinus phi L e k j o.1) (observationLaw M))
    (hjm : StronglyMeasurable[m] (fun o : Obs X Z => hMinus phi L e k j o.1))
    (hcond : (observationLaw M)[(fun o => binScoreComponents phi dphi L e k j o)
      | m] =ᵐ[observationLaw M] (fun o => hMinus phi L e k j o.1))
    (hbase : Integrable (fun o => psiProdBin phi dphi L e k j o) (observationLaw M))
    (hres : Integrable (fun o => regularValue d k j o.1 *
      (binScoreComponents phi dphi L e k j o - hMinus phi L e k j o.1))
      (observationLaw M)) :
    HasDerivAt (fun t : ℝ => ∫ o, psiProdBin phi dphi L
      {e with gamma := fun a x => e.gamma a x + t * d a x} k j o
      ∂observationLaw M) 0 0 := by
  let : MeasurableSpace (Obs X Z) := Prod.instMeasurableSpace
  have hz := score_weighted_conditional_residual_zero (observationLaw M) m hm
    (fun o => regularValue d k j o.1)
    (fun o => binScoreComponents phi dphi L e k j o)
    (fun o => hMinus phi L e k j o.1) hd hs hj hres hcond hjm
  have heq : (fun t : ℝ => ∫ o, psiProdBin phi dphi L
      {e with gamma := fun a x => e.gamma a x + t * d a x} k j o
      ∂observationLaw M) = (fun _ : ℝ => ∫ o, psiProdBin phi dphi L e k j o
      ∂observationLaw M) := by
    funext t
    simp_rw [binary_regular_product_weight_path]
    simp_rw [mul_assoc]
    rw [integral_add hbase (hres.const_mul t), integral_const_mul, hz,
      mul_zero, add_zero]
  rw [heq]
  exact hasDerivAt_const 0 _

end Papers.TbsPrteOptimalTransport
