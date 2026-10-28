module

public import Papers.OaiCapacityCriterionState.Basic
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.Dirac
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Notation

/-! # Posterior laws of uniform four-state experiments

These are laws of posterior vectors under the marginal observation law. Their
barycenter is uniform. Conditional products use the density Z before taking the
image under the normalized product map; this differs from an unweighted product.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace OaiCapacityCriterionState

-- @env: S3
variable {O : Type*} [Fintype O]

/-- For [a measure on four-state belief vectors](hyp:mu), [being a posterior law
under a uniform prior](goal) means that [it is a probability measure](step:1),
[it assigns zero mass outside the probability simplex](step:2), and
[the mean probability of each state is one quarter](step:3). -/
def IsPosteriorLaw (mu : Measure (Fin 4 → ℝ)) : Prop :=
  IsProbabilityMeasure mu ∧ -- @realizes \mu(probability law of the posterior vector)
  mu (stdSimplex ℝ (Fin 4))ᶜ = 0 ∧ -- @realizes p(simplex support) @realizes q(simplex support)
  ∀ i : Fin 4, ∫ p, p i ∂mu = 1 / 4 -- @realizes \mu(uniform barycenter)

-- @node: def:posterior-law
/-- [The space of posterior laws](goal) consists of probability measures on
four-state probability vectors whose mean vector is uniform.
@realizes \mu(law supported on the simplex with uniform barycenter)
@realizes \nu(second law with the same posterior-law domain) -/
def PosteriorLaw : Type := {mu : Measure (Fin 4 → ℝ) // IsPosteriorLaw mu}

/-- [The interpretation of a posterior law as a measure](goal) returns its
underlying probability measure on four-state belief vectors. -/
instance : Coe PosteriorLaw (Measure (Fin 4 → ℝ)) := ⟨Subtype.val⟩

/-- On [an observation space](hyp:O), given [state-dependent observation likelihoods](hyp:lik)
and [an observation](hyp:o),
[its marginal mass under the uniform prior](goal) is one quarter of the sum of
its likelihoods across the four states. -/
noncomputable def experimentMarginal (lik : Fin 4 → O → ℝ) (o : O) : ℝ :=
  (1 / 4) * ∑ i : Fin 4, lik i o

open Classical in
/-- On [an observation space](hyp:O), given [state-dependent observation likelihoods](hyp:lik)
and [an observation](hyp:o),
[the posterior belief vector](goal) assigns each state its likelihood times one
quarter divided by the observation's marginal mass when that mass is positive,
and uses the uniform belief vector otherwise.
@realizes p(posterior vector of a uniform input given a finite observation) -/
noncomputable def experimentPosterior (lik : Fin 4 → O → ℝ) (o : O) : Fin 4 → ℝ :=
  if 0 < experimentMarginal lik o then
    fun i => ((1 / 4) * lik i o) / experimentMarginal lik o
  else unifVec

/-- On [a finite observation space](hyp:O), for [state-dependent observation likelihoods](hyp:lik),
[the law of posterior beliefs](goal) places each observation's marginal mass
on its posterior belief vector. -/
noncomputable def experimentLaw (lik : Fin 4 → O → ℝ) : Measure (Fin 4 → ℝ) :=
  ∑ o : O, ENNReal.ofReal (experimentMarginal lik o) •
    Measure.dirac (experimentPosterior lik o)

omit [Fintype O] in
-- @node: experimentPosterior_mem_simplex
/-- If [all observation likelihoods are nonnegative](hyp:hnonneg),
[the posterior belief vector at any observation belongs to the probability simplex](goal). -/
lemma experimentPosterior_mem_simplex (lik : Fin 4 → O → ℝ)
    (hnonneg : ∀ i o, 0 ≤ lik i o) (o : O) :
    experimentPosterior lik o ∈ stdSimplex ℝ (Fin 4) := by
  classical
  by_cases hpos : 0 < experimentMarginal lik o
  · simp only [experimentPosterior, if_pos hpos]
    constructor
    · intro i
      exact div_nonneg (mul_nonneg (by norm_num) (hnonneg i o)) hpos.le
    · rw [← Finset.sum_div, ← Finset.mul_sum]
      exact div_self (ne_of_gt hpos)
  · simp only [experimentPosterior, if_neg hpos]
    constructor
    · intro i
      norm_num [unifVec]
    · norm_num [unifVec]

omit [Fintype O] in
-- @node: experimentMarginal_mul_posterior
/-- If [all observation likelihoods are nonnegative](hyp:hnonneg),
[an observation's marginal mass times its posterior probability of a state equals
one quarter of that state's likelihood of the observation](goal). -/
lemma experimentMarginal_mul_posterior (lik : Fin 4 → O → ℝ)
    (hnonneg : ∀ i o, 0 ≤ lik i o) (o : O) (i : Fin 4) :
    experimentMarginal lik o * experimentPosterior lik o i = (1 / 4) * lik i o := by
  classical
  by_cases hpos : 0 < experimentMarginal lik o
  · simp only [experimentPosterior, if_pos hpos]
    exact mul_div_cancel₀ _ (ne_of_gt hpos)
  · have hm : experimentMarginal lik o = 0 := le_antisymm (le_of_not_gt hpos)
      (mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ => hnonneg j o))
    have hle := Finset.single_le_sum (s := Finset.univ) (fun j _ => hnonneg j o)
      (Finset.mem_univ i)
    have hzero : lik i o = 0 := by
      dsimp [experimentMarginal] at hm
      linarith [hnonneg i o]
    rw [hm, hzero]
    ring

-- @node: experimentLaw_isPosteriorLaw
/-- If [all observation likelihoods are nonnegative](hyp:hnonneg) and
[the observation likelihoods sum to one for each state](hyp:hnorm),
[the induced posterior law is a probability measure on the simplex with uniform mean](goal). -/
lemma experimentLaw_isPosteriorLaw (lik : Fin 4 → O → ℝ)
    (hnonneg : ∀ i o, 0 ≤ lik i o) (hnorm : ∀ i, ∑ o : O, lik i o = 1) :
    IsPosteriorLaw (experimentLaw lik) := by
  have hm (o : O) : 0 ≤ experimentMarginal lik o :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => hnonneg i o)
  have hsum : ∑ o : O, experimentMarginal lik o = 1 := by
    unfold experimentMarginal
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp [hnorm]
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · simp only [experimentLaw, Measure.finsetSum_apply, Measure.smul_apply,
      measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun o _ => hm o), hsum]
    norm_num
  · classical
    simp only [experimentLaw, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro o _
    rw [Measure.dirac_apply' _ (isClosed_stdSimplex ℝ (Fin 4)).measurableSet.compl]
    simp [experimentPosterior_mem_simplex lik hnonneg o]
  · intro i
    unfold experimentLaw
    rw [integral_finsetSum_measure]
    · simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hm _),
        smul_eq_mul, experimentMarginal_mul_posterior lik hnonneg]
      rw [← Finset.mul_sum, hnorm i, mul_one]
    · intro o _
      exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- For [a measure on four-state belief vectors](hyp:mu),
[symmetry](goal) means invariance under every permutation of the state labels. -/
def IsSymmetricLaw (mu : Measure (Fin 4 → ℝ)) : Prop :=
  ∀ perm : Equiv.Perm (Fin 4), mu.map (fun p => p ∘ perm) = mu

/-- [The matrix of belief contrasts](goal) has rows with signs
$(+,+,-,-)$, $(+,-,+,-)$, and $(+,-,-,+)$, respectively, with every entry of magnitude one.
@realizes L(the three displayed rows of the 3 by 4 coordinate matrix) -/
def coordMatrix : Matrix (Fin 3) (Fin 4) ℝ :=
  !![1, 1, -1, -1; 1, -1, 1, -1; 1, -1, -1, 1]

/-- For [a four-state belief vector](hyp:p), [its three contrast coordinates](goal)
are obtained by multiplying it by the matrix of belief contrasts.
@realizes x(Lp in three real coordinates)
@realizes y(Lq when applied to the second posterior vector) -/
def postCoords (p : Fin 4 → ℝ) : Fin 3 → ℝ := coordMatrix.mulVec p

-- @node: def:posterior-coordinates
/-- For [a four-state belief vector](hyp:p), [the quadratic statistic](goal)
is the sum of the squares of its three contrast coordinates.
@realizes A(the Euclidean squared length of Lp, bounded by three on the simplex) -/
def quadStat (p : Fin 4 → ℝ) : ℝ := ∑ i : Fin 3, postCoords p i ^ 2

-- @node: postCoords_mem_Icc
/-- If [a four-state belief vector lies in the probability simplex](hyp:hp),
[each of its three contrast coordinates lies between minus one and one, inclusive](goal). -/
lemma postCoords_mem_Icc (p : Fin 4 → ℝ) (hp : p ∈ stdSimplex ℝ (Fin 4))
    (i : Fin 3) : postCoords p i ∈ Set.Icc (-1) 1 := by
  have hs := hp.2
  simp [Fin.sum_univ_succ] at hs
  have h0 := hp.1 0
  have h1 := hp.1 1
  have h2 := hp.1 2
  have h3 := hp.1 3
  fin_cases i <;>
    simp [postCoords, coordMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    constructor <;> linarith

-- @node: quadStat_mem_Icc
/-- If [a four-state belief vector lies in the probability simplex](hyp:hp),
[its quadratic statistic lies between zero and three, inclusive](goal). -/
lemma quadStat_mem_Icc (p : Fin 4 → ℝ) (hp : p ∈ stdSimplex ℝ (Fin 4)) :
    quadStat p ∈ Set.Icc 0 3 := by
  constructor
  · exact Finset.sum_nonneg fun i _ => sq_nonneg _
  · calc
      quadStat p ≤ ∑ _i : Fin 3, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have hi := postCoords_mem_Icc p hp i
        nlinarith [sq_nonneg (postCoords p i - 1),
          mul_nonneg (sub_nonneg.mpr hi.2) (sub_nonneg.mpr hi.1)]
      _ = 3 := by norm_num

-- @node: ass:pin-1
/-- [The Euclidean norm identity](goal) asserts that the squared norm of every
three-dimensional real vector equals the sum of the squares of its coordinates. -/
def EuclideanNormPin : Prop :=
  ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ^ 2 = ∑ i : Fin 3, (x i) ^ 2

-- @node: def:statistics
/-- For [a measure on four-state belief vectors](hyp:mu), [quadratic information](goal)
is the integral of the quadratic statistic against that measure.
@realizes m(expectation of A under a posterior law) -/
noncomputable def quadInfo (mu : Measure (Fin 4 → ℝ)) : ℝ := ∫ p, quadStat p ∂mu

-- @node: quadInfo_mem_Icc
/-- [The quadratic information of any posterior law lies between zero and three,
inclusive](goal). -/
lemma quadInfo_mem_Icc (mu : PosteriorLaw) :
    quadInfo mu ∈ Set.Icc 0 3 := by
  have : IsProbabilityMeasure (mu : Measure (Fin 4 → ℝ)) := mu.property.1
  have hs : ∀ᵐ p ∂(mu : Measure (Fin 4 → ℝ)), p ∈ stdSimplex ℝ (Fin 4) :=
    ae_iff.mpr mu.property.2.1
  have hnonneg : ∀ᵐ p ∂(mu : Measure (Fin 4 → ℝ)), 0 ≤ quadStat p :=
    hs.mono fun p hp => (quadStat_mem_Icc p hp).1
  refine ⟨integral_nonneg_of_ae hnonneg, ?_⟩
  have hle := integral_mono_of_nonneg hnonneg (integrable_const (3 : ℝ))
    (hs.mono fun p hp => (quadStat_mem_Icc p hp).2)
  simpa [quadInfo] using hle

/-- For [a measure on four-state belief vectors](hyp:mu), [the signed third moment](goal)
is the integral of the product of the three contrast coordinates.
@realizes \tau(expectation of the product of all three posterior coordinates) -/
noncomputable def thirdMoment (mu : Measure (Fin 4 → ℝ)) : ℝ :=
  ∫ p, postCoords p 0 * postCoords p 1 * postCoords p 2 ∂mu

/-- For [a measure on four-state belief vectors](hyp:mu), [the absolute third moment statistic](goal)
is the absolute value of its signed third moment.
@realizes h(absolute value of the signed third moment) -/
noncomputable def absThird (mu : Measure (Fin 4 → ℝ)) : ℝ := |thirdMoment mu|

/-- Given [a real channel parameter](hyp:t) and [a four-state belief vector](hyp:p),
[the channel-transformed belief vector](goal) is the uniform vector plus the
channel parameter times the deviation of the original vector from uniformity. -/
noncomputable def channelPosterior (t : ℝ) (p : Fin 4 → ℝ) : Fin 4 → ℝ :=
  unifVec + t • (p - unifVec)

/-- For [a real number](hyp:t), [being an admissible channel parameter](goal)
means lying between zero and one, inclusive.
@realizes t(channel parameters lie in the closed interval [0,1]) -/
def IsChannelParameter (t : ℝ) : Prop := t ∈ Set.Icc 0 1

-- @node: def:channel-step
/-- Given [a channel parameter](hyp:t) and [a measure on four-state belief vectors](hyp:mu),
[the channel step](goal) is the distribution obtained by transforming each belief
vector toward uniformity using that parameter. -/
noncomputable def channelStep (t : ℝ) (mu : Measure (Fin 4 → ℝ)) :
    Measure (Fin 4 → ℝ) := mu.map (channelPosterior t)

-- @node: channelStep_isPosteriorLaw
/-- If [the channel parameter lies between zero and one, inclusive](hyp:ht) and
[the initial measure is a posterior law with uniform mean](hyp:hmu),
[the channel step is also a posterior law with uniform mean](goal). -/
lemma channelStep_isPosteriorLaw (t : ℝ) (ht : IsChannelParameter t)
    (mu : Measure (Fin 4 → ℝ)) (hmu : IsPosteriorLaw mu) :
    IsPosteriorLaw (channelStep t mu) := by
  have : IsProbabilityMeasure mu := hmu.1
  have hm : Measurable (channelPosterior t) := by
    unfold channelPosterior
    fun_prop
  have hs : ∀ᵐ p ∂mu, p ∈ stdSimplex ℝ (Fin 4) := ae_iff.mpr hmu.2.1
  have hsimplex : ∀ᵐ p ∂mu, channelPosterior t p ∈ stdSimplex ℝ (Fin 4) := by
    filter_upwards [hs] with p hp
    constructor
    · intro i
      change 0 ≤ 1 / 4 + t * (p i - 1 / 4)
      nlinarith [ht.2, mul_nonneg ht.1 (hp.1 i)]
    · change (∑ i : Fin 4, (1 / 4 + t * (p i - 1 / 4))) = 1
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_sub_distrib, hp.2]
      norm_num
  refine ⟨Measure.isProbabilityMeasure_map hm.aemeasurable, ?_, ?_⟩
  · change mu.map (channelPosterior t) (stdSimplex ℝ (Fin 4))ᶜ = 0
    rw [Measure.map_apply hm ((isClosed_stdSimplex ℝ (Fin 4)).measurableSet.compl)]
    exact ae_iff.mp hsimplex
  · intro i
    have hi : Integrable (fun p : Fin 4 → ℝ => p i) mu := by
      apply (integrable_const (1 : ℝ)).mono' (continuous_apply i).aestronglyMeasurable
      filter_upwards [hs] with p hp
      simpa [Real.norm_eq_abs, abs_of_nonneg (hp.1 i)] using
        (mem_Icc_of_mem_stdSimplex hp i).2
    change (∫ p, p i ∂mu.map (channelPosterior t)) = 1 / 4
    rw [integral_map_of_stronglyMeasurable hm (continuous_apply i).stronglyMeasurable]
    change (∫ p, 1 / 4 + t * (p i - 1 / 4) ∂mu) = 1 / 4
    have hint : Integrable (fun p : Fin 4 → ℝ => t * (p i - 1 / 4)) mu :=
      (hi.sub (integrable_const (1 / 4 : ℝ))).const_mul t
    rw [integral_add (integrable_const (1 / 4 : ℝ)) hint,
      integral_const_mul, integral_sub hi (integrable_const (1 / 4 : ℝ)), hmu.2.2 i]
    simp

/-- Given [a real scaling factor](hyp:t) and [a vector of three contrast coordinates](hyp:x),
[the scaled coordinate vector](goal) multiplies each coordinate by that factor. -/
def scaledCoords (t : ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ := t • x

/-- Given [a real scaling factor](hyp:t) and [a triple of quadratic information,
signed third moment, and absolute third moment statistic](hyp:moments),
[the scaled moment triple](goal) multiplies the first entry by the factor squared
and each of the remaining entries by the factor cubed. -/
def scaledMoments (t : ℝ) (moments : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (t ^ 2 * moments.1, t ^ 3 * moments.2.1, t ^ 3 * moments.2.2)

-- @node: def:channel-scaling
/-- Given [a real scaling factor](hyp:t), [three contrast coordinates](hyp:x), and
[a triple of quadratic information, signed third moment, and absolute third moment statistic](hyp:moments),
[the joint scaling transformation](goal) multiplies the coordinates by the factor
and the three moments by its square, cube, and cube, respectively. -/
def channelScaledMoments (t : ℝ) (x : Fin 3 → ℝ) (moments : ℝ × ℝ × ℝ) :
    (Fin 3 → ℝ) × ℝ × ℝ × ℝ :=
  (scaledCoords t x, scaledMoments t moments)

-- @node: postCoords_channel
/-- [The contrast coordinates of a channel-transformed belief vector equal
the original contrast coordinates multiplied by the channel parameter](goal). -/
lemma postCoords_channel (t : ℝ) (p : Fin 4 → ℝ) :
    postCoords (channelPosterior t p) = scaledCoords t (postCoords p) := by
  ext i
  fin_cases i <;>
    simp [postCoords, channelPosterior, scaledCoords, coordMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, unifVec] <;> ring

-- @node: moments_channelStep
/-- If [the channel parameter lies between zero and one, inclusive](hyp:ht) and
[the initial measure is a posterior law with uniform mean](hyp:hmu),
[a channel step multiplies quadratic information by the parameter squared and
both the signed third moment and its absolute value by the parameter cubed](goal). -/
lemma moments_channelStep (t : ℝ) (ht : IsChannelParameter t)
    (mu : Measure (Fin 4 → ℝ)) (hmu : IsPosteriorLaw mu) :
    (quadInfo (channelStep t mu), thirdMoment (channelStep t mu),
      absThird (channelStep t mu)) =
    scaledMoments t (quadInfo mu, thirdMoment mu, absThird mu) := by
  have hm : Measurable (channelPosterior t) := by
    unfold channelPosterior
    fun_prop
  have hq : StronglyMeasurable quadStat := by
    unfold quadStat postCoords Matrix.mulVec dotProduct
    fun_prop
  have hh : StronglyMeasurable
      (fun p => postCoords p 0 * postCoords p 1 * postCoords p 2) := by
    unfold postCoords Matrix.mulVec dotProduct
    fun_prop
  have hquad : quadInfo (channelStep t mu) = t ^ 2 * quadInfo mu := by
    unfold quadInfo channelStep
    rw [integral_map_of_stronglyMeasurable hm hq]
    calc
      _ = ∫ p, t ^ 2 * quadStat p ∂mu := by
        congr 1
        funext p
        simp only [quadStat, postCoords_channel, scaledCoords, Pi.smul_apply,
          smul_eq_mul, mul_pow, Finset.mul_sum]
      _ = _ := integral_const_mul _ _
  have hthird : thirdMoment (channelStep t mu) = t ^ 3 * thirdMoment mu := by
    unfold thirdMoment channelStep
    rw [integral_map_of_stronglyMeasurable hm hh]
    calc
      _ = ∫ p, t ^ 3 * (postCoords p 0 * postCoords p 1 * postCoords p 2) ∂mu := by
        congr 1
        funext p
        simp only [postCoords_channel, scaledCoords, Pi.smul_apply, smul_eq_mul]
        ring
      _ = _ := integral_const_mul _ _
  have habs : absThird (channelStep t mu) = t ^ 3 * absThird mu := by
    rw [absThird, hthird, abs_mul, abs_of_nonneg (pow_nonneg ht.1 3)]
    rfl
  exact Prod.ext hquad (Prod.ext hthird habs)

/-- [The fully revealing posterior law](goal) assigns mass one quarter to each
of the four belief vectors that put probability one on a single state. -/
noncomputable def revealingLaw : Measure (Fin 4 → ℝ) :=
  ∑ i : Fin 4, (1 / 4 : ℝ≥0∞) • Measure.dirac (Pi.single i 1)

/-- [The uninformative posterior law](goal) assigns all its mass to the uniform
belief vector. -/
noncomputable def uninformativeLaw : Measure (Fin 4 → ℝ) := Measure.dirac unifVec

-- @node: def:extreme-experiments
/-- [The extreme-experiment moment property](goal) asserts that
[the fully revealing law has quadratic information three](step:1),
[the uninformative law has quadratic information zero](step:2), and
[the uninformative law has absolute third moment statistic zero](step:3). -/
def extremeExperiments : Prop :=
  quadInfo revealingLaw = 3 ∧ quadInfo uninformativeLaw = 0 ∧
    absThird uninformativeLaw = 0

-- @node: extreme_moments
/-- [The fully revealing law has quadratic information three, while the
uninformative law has quadratic information zero and absolute third moment
statistic zero](goal). -/
lemma extreme_moments :
    quadInfo revealingLaw = 3 ∧ quadInfo uninformativeLaw = 0 ∧
      absThird uninformativeLaw = 0 := by
  have hvertex : ∀ i : Fin 4, quadStat (Pi.single i 1) = 3 := by
    intro i
    fin_cases i <;>
      norm_num [quadStat, postCoords, coordMatrix, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ, Pi.single_apply]
  have hrevealing : quadInfo revealingLaw = 3 := by
    unfold quadInfo revealingLaw
    rw [integral_finsetSum_measure]
    · simp [integral_smul_measure, integral_dirac, hvertex]
    · intro i _
      exact (integrable_dirac (by simp)).smul_measure (by norm_num)
  have huniform : postCoords unifVec = 0 := by
    ext i
    fin_cases i <;>
      norm_num [postCoords, coordMatrix, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ, unifVec]
  refine ⟨hrevealing, ?_, ?_⟩
  · simp [quadInfo, uninformativeLaw, integral_dirac, quadStat, huniform]
  · simp [absThird, thirdMoment, uninformativeLaw, integral_dirac, huniform]

-- @node: extreme_laws
/-- [Both the fully revealing law and the uninformative law are posterior laws
with uniform mean and are invariant under every permutation of the state labels](goal). -/
lemma extreme_laws :
    IsPosteriorLaw revealingLaw ∧ IsSymmetricLaw revealingLaw ∧
    IsPosteriorLaw uninformativeLaw ∧ IsSymmetricLaw uninformativeLaw := by
  classical
  have hv (i : Fin 4) : Pi.single i (1 : ℝ) ∈ stdSimplex ℝ (Fin 4) := by
    constructor
    · intro j
      simp only [Pi.single_apply]
      split_ifs <;> norm_num
    · simp
  have hu : unifVec ∈ stdSimplex ℝ (Fin 4) := by
    constructor
    · intro i
      norm_num [unifVec]
    · norm_num [unifVec]
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨⟨?_⟩, ?_, ?_⟩
    · norm_num [revealingLaw, Measure.finsetSum_apply, Measure.smul_apply]
      exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
    · simp only [revealingLaw, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
      apply Finset.sum_eq_zero
      intro i _
      rw [Measure.dirac_apply' _ (isClosed_stdSimplex ℝ (Fin 4)).measurableSet.compl]
      simp [hv i]
    · intro i
      unfold revealingLaw
      rw [integral_finsetSum_measure]
      · simp [integral_smul_measure, integral_dirac, Pi.single_apply]
      · intro j _
        exact (integrable_dirac (by simp)).smul_measure (by norm_num)
  · intro perm
    have hm : Measurable (fun p : Fin 4 → ℝ => p ∘ perm) := by fun_prop
    have hp (i : Fin 4) : (Pi.single i (1 : ℝ)) ∘ perm = Pi.single (perm.symm i) 1 := by
      ext j
      simp only [Function.comp_apply, Pi.single_apply]
      have he : perm j = i ↔ j = perm.symm i := by
        constructor
        · intro h
          simpa using congrArg perm.symm h
        · intro h
          simp [h]
      simp [he]
    unfold revealingLaw
    rw [Measure.map_finset_sum' hm.aemeasurable]
    simp only [Measure.map_smul,
      Measure.map_dirac, hp]
    apply Finset.sum_bij (fun i _ => perm.symm i)
    · intro i _
      exact Finset.mem_univ _
    · intro i _ j _ hij
      exact perm.symm.injective hij
    · intro j _
      exact ⟨perm j, Finset.mem_univ _, perm.symm_apply_apply j⟩
    · intro i _
      rfl
  · refine ⟨inferInstanceAs (IsProbabilityMeasure (Measure.dirac unifVec)), ?_, ?_⟩
    · rw [uninformativeLaw, Measure.dirac_apply' _
        (isClosed_stdSimplex ℝ (Fin 4)).measurableSet.compl]
      simp [hu]
    · intro i
      simp [uninformativeLaw, integral_dirac, unifVec]
  · intro perm
    rw [uninformativeLaw, Measure.map_dirac]
    rfl

/-- For [a pair of four-state belief vectors](hyp:pq), [the product density](goal)
is four times the sum of their statewise probability products.
@realizes Z(density 4 times the inner product of the two posterior vectors) -/
def productZ (pq : (Fin 4 → ℝ) × (Fin 4 → ℝ)) : ℝ :=
  4 * ∑ i : Fin 4, pq.1 i * pq.2 i

open Classical in
/-- For [a pair of four-state belief vectors](hyp:pq), [the combined belief vector](goal)
has state probabilities equal to four times the statewise products divided by
the product density when that density is positive, and is uniform otherwise.
@realizes P(normalized product posterior, with uniform extension when Z is zero)
@realizes q(second marginal posterior vector used in the normalized product) -/
noncomputable def productP (pq : (Fin 4 → ℝ) × (Fin 4 → ℝ)) : Fin 4 → ℝ :=
  if 0 < productZ pq then fun i => 4 * pq.1 i * pq.2 i / productZ pq
  else unifVec

-- @node: def:product-rule
/-- Given [a first measure on belief vectors](hyp:mu) and [a second such measure](hyp:nu),
[their conditional-product posterior measure](goal) is obtained by weighting their
independent product by the product density and then taking the distribution of
the combined belief vector.
@realizes \star(law of P under Z times the product of the marginal posterior laws) -/
noncomputable def starLaw (mu nu : Measure (Fin 4 → ℝ)) : Measure (Fin 4 → ℝ) :=
  ((mu.prod nu).withDensity (fun pq => ENNReal.ofReal (productZ pq))).map productP

-- @node: product_rule_bounds
/-- [Under the independent product of any two posterior laws, the product density
lies between zero and four and the combined belief vector lies in the probability
simplex almost surely; moreover, the mean product density is one](goal). -/
lemma product_rule_bounds (mu nu : PosteriorLaw) :
    (∀ᵐ pq ∂((mu : Measure (Fin 4 → ℝ)).prod (nu : Measure (Fin 4 → ℝ))),
      productZ pq ∈ Set.Icc 0 4 ∧ -- @realizes Z(a.e. range [0,4])
      productP pq ∈ stdSimplex ℝ (Fin 4)) ∧ -- @realizes P(a.e. simplex range)
    (∫ pq, productZ pq
      ∂((mu : Measure (Fin 4 → ℝ)).prod (nu : Measure (Fin 4 → ℝ)))) = 1 := by
  have : IsProbabilityMeasure (mu : Measure (Fin 4 → ℝ)) := mu.property.1
  have : IsProbabilityMeasure (nu : Measure (Fin 4 → ℝ)) := nu.property.1
  have hmu : ∀ᵐ p ∂(mu : Measure (Fin 4 → ℝ)), p ∈ stdSimplex ℝ (Fin 4) :=
    ae_iff.mpr mu.property.2.1
  have hnu : ∀ᵐ q ∂(nu : Measure (Fin 4 → ℝ)), q ∈ stdSimplex ℝ (Fin 4) :=
    ae_iff.mpr nu.property.2.1
  constructor
  · have hp := (Measure.quasiMeasurePreserving_fst
        (ν := (nu : Measure (Fin 4 → ℝ)))).ae hmu
    have hq := (Measure.quasiMeasurePreserving_snd
        (μ := (mu : Measure (Fin 4 → ℝ)))).ae hnu
    filter_upwards [hp, hq] with pq hp hq
    have hz : 0 ≤ productZ pq := by
      exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ =>
        mul_nonneg (hp.1 i) (hq.1 i))
    refine ⟨⟨hz, ?_⟩, ?_⟩
    · have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
        mul_le_mul_of_nonneg_left (mem_Icc_of_mem_stdSimplex hq i).2 (hp.1 i))
      simp only [mul_one, hp.2] at hsum
      dsimp [productZ]
      linarith
    · classical
      by_cases hpos : 0 < productZ pq
      · simp only [productP, if_pos hpos]
        constructor
        · intro i
          exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hp.1 i))
            (hq.1 i)) hz
        · rw [← Finset.sum_div]
          simp_rw [mul_assoc]
          rw [← Finset.mul_sum]
          exact div_self (ne_of_gt hpos)
      · simp only [productP, if_neg hpos]
        constructor
        · intro i
          norm_num [unifVec]
        · norm_num [unifVec]
  · have hi : ∀ (rho : PosteriorLaw) (i : Fin 4),
        Integrable (fun p : Fin 4 → ℝ => p i) (rho : Measure (Fin 4 → ℝ)) := by
      intro rho i
      have : IsProbabilityMeasure (rho : Measure (Fin 4 → ℝ)) := rho.property.1
      apply (integrable_const (1 : ℝ)).mono' (continuous_apply i).aestronglyMeasurable
      have hs : ∀ᵐ p ∂(rho : Measure (Fin 4 → ℝ)), p ∈ stdSimplex ℝ (Fin 4) :=
        ae_iff.mpr rho.property.2.1
      filter_upwards [hs] with p hp
      simpa [Real.norm_eq_abs, abs_of_nonneg (hp.1 i)] using
        (mem_Icc_of_mem_stdSimplex hp i).2
    unfold productZ
    rw [integral_const_mul, integral_finsetSum]
    · have hprod (i : Fin 4) :
          (∫ pq, pq.1 i * pq.2 i
            ∂((mu : Measure (Fin 4 → ℝ)).prod (nu : Measure (Fin 4 → ℝ)))) =
          (1 / 4 : ℝ) * (1 / 4) := by
        calc
          _ = (∫ p, p i ∂(mu : Measure (Fin 4 → ℝ))) *
              (∫ q, q i ∂(nu : Measure (Fin 4 → ℝ))) :=
            integral_prod_mul (fun p : Fin 4 → ℝ => p i) (fun q : Fin 4 → ℝ => q i)
          _ = _ := by rw [mu.property.2.2 i, nu.property.2.2 i]
      simp only [hprod]
      norm_num
    · intro i _
      exact (hi mu i).mul_prod (hi nu i)

-- @node: starLaw_isPosteriorLaw
/-- If [the first measure is a posterior law with uniform mean](hyp:hmu) and
[the second measure is a posterior law with uniform mean](hyp:hnu),
[their conditional-product measure is also a posterior law with uniform mean](goal). -/
lemma starLaw_isPosteriorLaw (mu nu : Measure (Fin 4 → ℝ))
    (hmu : IsPosteriorLaw mu) (hnu : IsPosteriorLaw nu) :
    IsPosteriorLaw (starLaw mu nu) := by
  classical
  have : IsProbabilityMeasure mu := hmu.1
  have : IsProbabilityMeasure nu := hnu.1
  let rho := mu.prod nu
  let density := fun pq => ENNReal.ofReal (productZ pq)
  let weighted := rho.withDensity density
  have hzmeas : Measurable productZ := by
    unfold productZ
    fun_prop
  have hdmeas : Measurable density := hzmeas.ennreal_ofReal
  have hpmeas : Measurable productP := by
    unfold productP
    refine Measurable.ite (measurableSet_lt measurable_const hzmeas) ?_ measurable_const
    apply measurable_pi_lambda
    intro i
    exact ((measurable_const.mul ((measurable_pi_apply i).comp measurable_fst)).mul
      ((measurable_pi_apply i).comp measurable_snd)).div hzmeas
  obtain ⟨hbounds, hmass⟩ := product_rule_bounds ⟨mu, hmu⟩ ⟨nu, hnu⟩
  have hzint : Integrable productZ rho := by
    apply (integrable_const (4 : ℝ)).mono' hzmeas.aestronglyMeasurable
    filter_upwards [hbounds] with pq hpq
    simpa [Real.norm_eq_abs, abs_of_nonneg hpq.1.1] using hpq.1.2
  have hweighted : IsProbabilityMeasure weighted := by
    constructor
    change (rho.withDensity density) Set.univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hzint (hbounds.mono fun _ h => h.1.1)]
    rw [hmass]
    norm_num
  have hsupport : ∀ᵐ pq ∂weighted, productP pq ∈ stdSimplex ℝ (Fin 4) :=
    (show weighted ≪ rho from withDensity_absolutelyContinuous rho density).ae_le
      (hbounds.mono fun _ h => h.2)
  refine ⟨?_, ?_, ?_⟩
  · change IsProbabilityMeasure (weighted.map productP)
    exact Measure.isProbabilityMeasure_map hpmeas.aemeasurable
  · change weighted.map productP (stdSimplex ℝ (Fin 4))ᶜ = 0
    rw [Measure.map_apply hpmeas (isClosed_stdSimplex ℝ (Fin 4)).measurableSet.compl]
    exact ae_iff.mp hsupport
  · intro i
    change (∫ p, p i ∂weighted.map productP) = 1 / 4
    rw [integral_map hpmeas.aemeasurable (measurable_pi_apply i).aestronglyMeasurable]
    rw [integral_withDensity_eq_integral_toReal_smul hdmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    have hidentity : ∀ᵐ pq ∂rho,
        (density pq).toReal * productP pq i = 4 * pq.1 i * pq.2 i := by
      have hs_mu : ∀ᵐ p ∂mu, p ∈ stdSimplex ℝ (Fin 4) := ae_iff.mpr hmu.2.1
      have hs_nu : ∀ᵐ q ∂nu, q ∈ stdSimplex ℝ (Fin 4) := ae_iff.mpr hnu.2.1
      have hp := (Measure.quasiMeasurePreserving_fst (ν := nu)).ae hs_mu
      have hq := (Measure.quasiMeasurePreserving_snd (μ := mu)).ae hs_nu
      filter_upwards [hbounds, hp, hq] with pq hb hp hq
      change (ENNReal.ofReal (productZ pq)).toReal * productP pq i = _
      rw [ENNReal.toReal_ofReal hb.1.1]
      by_cases hpos : 0 < productZ pq
      · simp only [productP, if_pos hpos]
        exact mul_div_cancel₀ _ (ne_of_gt hpos)
      · have hz : productZ pq = 0 := le_antisymm (le_of_not_gt hpos) hb.1.1
        have hle := Finset.single_le_sum (s := Finset.univ)
          (fun j _ => mul_nonneg (hp.1 j) (hq.1 j)) (Finset.mem_univ i)
        have hzero : 4 * pq.1 i * pq.2 i = 0 := by
          dsimp [productZ] at hz
          nlinarith [mul_nonneg (hp.1 i) (hq.1 i)]
        rw [hz, hzero, zero_mul]
    calc
      (∫ pq, (density pq).toReal • productP pq i ∂rho) =
          ∫ pq, 4 * pq.1 i * pq.2 i ∂rho := integral_congr_ae hidentity
      _ = 4 * ((∫ p, p i ∂mu) * ∫ q, q i ∂nu) := by
        simp_rw [mul_assoc]
        rw [integral_const_mul]
        exact congrArg (fun x : ℝ => 4 * x)
          (integral_prod_mul (μ := mu) (ν := nu)
            (fun p : Fin 4 → ℝ => p i) (fun q : Fin 4 → ℝ => q i))
      _ = 1 / 4 := by rw [hmu.2.2 i, hnu.2.2 i]; norm_num

-- @node: ass:pin-2
/-- [The product-rule extension property](goal) asserts that, for any two posterior
laws, every measurable rule that maps pairs of probability vectors to probability
vectors and agrees with the normalized product wherever its density is positive
induces the same conditional-product posterior law when applied to the product
measure weighted by that density. -/
def ProductRulePin : Prop :=
  ∀ (mu nu : PosteriorLaw) (extension : (Fin 4 → ℝ) × (Fin 4 → ℝ) → (Fin 4 → ℝ)),
    Measurable extension →
    (∀ pq, pq.1 ∈ stdSimplex ℝ (Fin 4) → pq.2 ∈ stdSimplex ℝ (Fin 4) →
      extension pq ∈ stdSimplex ℝ (Fin 4)) →
    (∀ pq, pq.1 ∈ stdSimplex ℝ (Fin 4) → pq.2 ∈ stdSimplex ℝ (Fin 4) →
      0 < productZ pq → extension pq = productP pq) →
    starLaw mu nu =
      (((mu : Measure (Fin 4 → ℝ)).prod (nu : Measure (Fin 4 → ℝ))).withDensity
        (fun pq => ENNReal.ofReal (productZ pq))).map extension

-- @node: ass:local-moments-lambda
/-- For [a real channel parameter](hyp:lam), [the local-moments parameter condition](goal)
requires that [it be strictly positive](step:1) and [strictly less than one](step:2). -/
def LocalMomentsLambda (lam : ℝ) : Prop := 0 < lam ∧ lam < 1

-- @node: ass:local-moments-symmetry
/-- For [a first posterior law](hyp:mu) and [a second posterior law](hyp:nu),
[the local-moments symmetry condition](goal) requires that
[the first law be invariant under state permutations](step:1) and
[the second law be invariant under state permutations](step:2). -/
def LocalMomentsSymmetry (mu nu : PosteriorLaw) : Prop :=
  IsSymmetricLaw mu ∧ IsSymmetricLaw nu

-- @node: ass:local-moments-channel
/-- For [a real channel parameter](hyp:lam) and [a posterior law](hyp:nu),
[the local-moments channel condition](goal) asserts that there exists another
posterior law such that [applying the channel with this parameter to that law
produces the given law](step:1). -/
def LocalMomentsChannel (lam : ℝ) (nu : PosteriorLaw) : Prop :=
  ∃ nu0 : PosteriorLaw, (nu : Measure (Fin 4 → ℝ)) = channelStep lam nu0

/-- On [an observation space](hyp:O), given [a real channel parameter](hyp:t) and
[state-dependent observation likelihoods](hyp:lik), [the channel-composed likelihood](goal)
of an observation in an initial state is the sum, over intermediate states,
of the channel transition weight times the observation likelihood in that intermediate state. -/
noncomputable def channelLikelihood (t : ℝ) (lik : Fin 4 → O → ℝ) : Fin 4 → O → ℝ :=
  fun i o => ∑ j : Fin 4, channel t i j * lik j o

-- @node: experimentLaw_channel
/-- If [the channel parameter lies between zero and one, inclusive](hyp:ht),
[all observation likelihoods are nonnegative](hyp:hnonneg), and
[the likelihoods sum to one over observations in each state](hyp:hnorm),
[the posterior law of the channel-composed experiment equals the channel
transformation of the original experiment's posterior law](goal). -/
lemma experimentLaw_channel (t : ℝ) (ht : IsChannelParameter t)
    (lik : Fin 4 → O → ℝ) (hnonneg : ∀ i o, 0 ≤ lik i o)
    (hnorm : ∀ i, ∑ o : O, lik i o = 1) :
    experimentLaw (channelLikelihood t lik) = channelStep t (experimentLaw lik) := by
  classical
  have hlik (i : Fin 4) (o : O) :
      channelLikelihood t lik i o = t * lik i o + (1 - t) * experimentMarginal lik o := by
    simp [channelLikelihood, channel, add_mul, mul_ite, ite_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum, experimentMarginal]
    ring
  have hm (o : O) :
      experimentMarginal (channelLikelihood t lik) o = experimentMarginal lik o := by
    simp only [experimentMarginal, hlik, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hp (o : O) : experimentPosterior (channelLikelihood t lik) o =
      channelPosterior t (experimentPosterior lik o) := by
    by_cases hpos : 0 < experimentMarginal lik o
    · ext i
      simp only [experimentPosterior, hm, if_pos hpos]
      change ((1 / 4) * channelLikelihood t lik i o) / experimentMarginal lik o =
        1 / 4 + t * (((1 / 4) * lik i o) / experimentMarginal lik o - 1 / 4)
      rw [hlik]
      field_simp
      ring
    · simp [experimentPosterior, hm, hpos, channelPosterior]
  have hmeas : Measurable (channelPosterior t) := by
    unfold channelPosterior
    fun_prop
  unfold experimentLaw channelStep
  rw [Measure.map_finset_sum hmeas.aemeasurable]
  apply Finset.sum_congr rfl
  intro o _
  rw [Measure.map_smul, Measure.map_dirac' hmeas, hm, hp]

/-- For [a first observation space](hyp:O) and [a second observation space](hyp:O'),
given [the first experiment's state-dependent likelihoods](hyp:lik) and
[the second experiment's state-dependent likelihoods](hyp:lik'),
[the joint likelihood for observations that are conditionally independent given
their common state](goal) is the product of their individual likelihoods in that state. -/
def productLikelihood {O' : Type*} (lik : Fin 4 → O → ℝ) (lik' : Fin 4 → O' → ℝ) :
    Fin 4 → O × O' → ℝ := fun i obs => lik i obs.1 * lik' i obs.2

-- @node: experimentLaw_prod
/-- If [the first experiment's likelihoods are nonnegative](hyp:hnonneg) and
[the second experiment's likelihoods are nonnegative](hyp:hnonneg'), and
[the first experiment's likelihoods sum to one over observations in each state](hyp:hnorm)
and [the second experiment's likelihoods do likewise](hyp:hnorm'),
[the posterior law of their conditionally independent joint experiment equals
the conditional-product combination of their individual posterior laws](goal). -/
lemma experimentLaw_prod {O' : Type*} [Fintype O']
    (lik : Fin 4 → O → ℝ) (lik' : Fin 4 → O' → ℝ)
    (hnonneg : ∀ i o, 0 ≤ lik i o) (hnonneg' : ∀ i o, 0 ≤ lik' i o)
    (hnorm : ∀ i, ∑ o : O, lik i o = 1) (hnorm' : ∀ i, ∑ o : O', lik' i o = 1) :
    experimentLaw (productLikelihood lik lik') =
      starLaw (experimentLaw lik) (experimentLaw lik') := by
  classical
  have hm (o : O) : 0 ≤ experimentMarginal lik o :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => hnonneg i o)
  have hm' (o : O') : 0 ≤ experimentMarginal lik' o :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => hnonneg' i o)
  have hc (o : O) (o' : O') (i : Fin 4) :
      (experimentMarginal lik o * experimentMarginal lik' o') *
        (4 * experimentPosterior lik o i * experimentPosterior lik' o' i) =
      (1 / 4) * productLikelihood lik lik' i (o, o') := by
    dsimp [productLikelihood]
    calc
      _ = 4 * (experimentMarginal lik o * experimentPosterior lik o i) *
          (experimentMarginal lik' o' * experimentPosterior lik' o' i) := by ring
      _ = _ := by
        rw [experimentMarginal_mul_posterior lik hnonneg,
          experimentMarginal_mul_posterior lik' hnonneg']
        ring
  have hw (o : O) (o' : O') :
      (experimentMarginal lik o * experimentMarginal lik' o') *
        productZ (experimentPosterior lik o, experimentPosterior lik' o') =
      experimentMarginal (productLikelihood lik lik') (o, o') := by
    change (experimentMarginal lik o * experimentMarginal lik' o') *
      (4 * ∑ i : Fin 4, experimentPosterior lik o i * experimentPosterior lik' o' i) =
      (1 / 4) * ∑ i : Fin 4, productLikelihood lik lik' i (o, o')
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = (experimentMarginal lik o * experimentMarginal lik' o') *
          (4 * experimentPosterior lik o i * experimentPosterior lik' o' i) := by ring
      _ = _ := hc o o' i
  have hp (o : O) (o' : O')
      (hpos : 0 < experimentMarginal (productLikelihood lik lik') (o, o')) :
      experimentPosterior (productLikelihood lik lik') (o, o') =
        productP (experimentPosterior lik o, experimentPosterior lik' o') := by
    have hw' := hw o o'
    have hmn : 0 < experimentMarginal lik o * experimentMarginal lik' o' := by
      have hne : experimentMarginal lik o * experimentMarginal lik' o' ≠ 0 := by
        intro h
        rw [h, zero_mul] at hw'
        linarith
      exact lt_of_le_of_ne (mul_nonneg (hm o) (hm' o')) (Ne.symm hne)
    have hz : 0 < productZ (experimentPosterior lik o, experimentPosterior lik' o') :=
      (mul_pos_iff_of_pos_left hmn).mp (hw'.symm ▸ hpos)
    ext i
    rw [productP, if_pos hz]
    rw [experimentPosterior, if_pos hpos]
    apply (div_eq_div_iff (ne_of_gt hpos) (ne_of_gt hz)).mpr
    rw [← hw', ← hc o o' i]
    ring
  have hpmeas : Measurable productP := by
    unfold productP
    have hzmeas : Measurable productZ := by unfold productZ; fun_prop
    refine Measurable.ite (measurableSet_lt measurable_const hzmeas) ?_ measurable_const
    apply measurable_pi_lambda
    intro i
    exact ((measurable_const.mul ((measurable_pi_apply i).comp measurable_fst)).mul
      ((measurable_pi_apply i).comp measurable_snd)).div hzmeas
  have hexpand : (experimentLaw lik).prod (experimentLaw lik') =
      ∑ obs : O × O',
        (ENNReal.ofReal (experimentMarginal lik obs.1) *
          ENNReal.ofReal (experimentMarginal lik' obs.2)) •
          Measure.dirac (experimentPosterior lik obs.1, experimentPosterior lik' obs.2) := by
    unfold experimentLaw
    simp_rw [← Measure.sum_fintype]
    rw [Measure.prod_sum]
    simp_rw [Measure.prod_smul_left, Measure.prod_smul_right,
      Measure.dirac_prod_dirac, smul_smul]
  rw [starLaw, hexpand]
  simp_rw [← Measure.sum_fintype, withDensity_sum, withDensity_smul_measure,
    dirac_withDensity, Measure.map_sum hpmeas.aemeasurable,
    Measure.map_smul, Measure.map_dirac' hpmeas, smul_smul]
  rw [Measure.sum_fintype]
  unfold experimentLaw
  apply Finset.sum_congr rfl
  intro obs _
  obtain ⟨o, o'⟩ := obs
  dsimp only [Prod.fst, Prod.snd]
  have he : ENNReal.ofReal (experimentMarginal lik o) *
      ENNReal.ofReal (experimentMarginal lik' o') *
        ENNReal.ofReal (productZ (experimentPosterior lik o, experimentPosterior lik' o')) =
      ENNReal.ofReal (experimentMarginal (productLikelihood lik lik') (o, o')) := by
    rw [← ENNReal.ofReal_mul (hm o),
      ← ENNReal.ofReal_mul (mul_nonneg (hm o) (hm' o')), hw]
  rw [he]
  by_cases hpos : 0 < experimentMarginal (productLikelihood lik lik') (o, o')
  · rw [hp o o' hpos]
  · have hzero : ENNReal.ofReal (experimentMarginal (productLikelihood lik lik') (o, o')) = 0 :=
      ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hpos)
    rw [hzero, zero_smul, zero_smul]

end OaiCapacityCriterionState
