module
public import Papers.OaiUniformInfluenceHypergraph.Helpers.Fourier
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Probability polynomials, Russo–Margulis, and quantiles

The endpoint values, continuity, positive derivative, and quantile recovery
are proved consequences of finite sampling and nontrivial monotonicity.
-/

@[expose] public section

open scoped BigOperators
open Causalean.Experimentation.DesignBased

namespace Papers.OaiUniformInfluenceHypergraph

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- For [a Boolean response function](hyp:f) on [a finite coordinate set](hyp:J),
the [probability polynomial](goal) sums its zero-or-one response over all configurations,
weighting each true coordinate by the polynomial variable and each false coordinate
by one minus that variable. -/
noncomputable def probabilityPolynomial (f : (J → Bool) → Bool) : Polynomial ℝ :=
  ∑ x : J → Bool, Polynomial.C (boolValue f x) *
    ∏ i : J, if x i then Polynomial.X else 1 - Polynomial.X

-- @node: probabilityPolynomial_eval
/-- If [the Bernoulli bias lies between zero and one, inclusive](hyp:hp),
[evaluating the probability polynomial at that bias gives the probability that
the Boolean response is true](goal). -/
lemma probabilityPolynomial_eval (f : (J → Bool) → Bool) (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    (probabilityPolynomial f).eval p = probCurve f p := by
  rw [probCurve, biasedLaw_eq_bernoulliDesign p hp]
  simp only [probabilityPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_prod, apply_ite,
    Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one,
    FiniteDesign.E, bernoulliDesign, prodDesign_p]
  apply Finset.sum_congr rfl
  intro x _
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  cases x i <;> simp [coinDesign]

-- @node: probCurve_continuous
/-- For any Boolean response, [its probability of being true is a continuous
function of the Bernoulli bias on the whole real line](goal). -/
lemma probCurve_continuous (f : (J → Bool) → Bool) : Continuous (probCurve f) := by
  unfold probCurve biasedLaw FiniteDesign.E bernoulliDesign
  simp only [prodDesign_p]
  apply continuous_finsetSum
  intro x _
  apply Continuous.mul _ continuous_const
  apply continuous_finsetProd
  intro i _
  cases x i <;> simp only [coinDesign, cond_false, cond_true] <;>
    fun_prop

-- @node: probCurve_mem_Icc
/-- For any Boolean response and any real bias parameter, [the probability
curve takes a value between zero and one, inclusive](goal). -/
lemma probCurve_mem_Icc (f : (J → Bool) → Bool) (p : ℝ) :
    probCurve f p ∈ Set.Icc 0 1 := by
  constructor
  · apply FiniteDesign.E_nonneg
    intro x
    cases h : f x <;> norm_num [boolValue, h]
  · apply FiniteDesign.E_le_one
    intro x
    cases h : f x <;> norm_num [boolValue, h]

-- @node: boolean_variance_eq_curve
/-- [The variance of a Boolean response under the biased product distribution
equals its probability of being true times one minus that probability](goal). -/
lemma boolean_variance_eq_curve (f : (J → Bool) → Bool) (p : ℝ) :
    (biasedLaw J p).Var (boolValue f) = probCurve f p * (1 - probCurve f p) := by
  have hsq : (fun x => boolValue f x ^ 2) = boolValue f := by
    funext x
    cases h : f x <;> norm_num [boolValue, h]
  rw [FiniteDesign.Var_eq, hsq]
  unfold probCurve
  ring

/-- If [the two Boolean weights sum to one](hyp:hw), [summing the response
over configurations with the selected coordinate weighted by a separate signed
weight equals summing under the full product weights and then summing the response
over both replacements of that coordinate with the signed weights](goal). -/
-- @node: bernoulli_sum_erase_resample
lemma bernoulli_sum_erase_resample (w t : Bool → ℝ) (hw : ∑ b, w b = 1)
    (g : (J → Bool) → ℝ) (i : J) :
    (∑ x, (∏ j ∈ Finset.univ.erase i, w (x j)) * t (x i) * g x) =
      ∑ x, (∏ j : J, w (x j)) * ∑ b, t b * g (Function.update x i b) := by
  classical
  let e : ((J → Bool) × Bool) ≃ ((J → Bool) × Bool) :=
    { toFun := fun z => (Function.update z.1 i z.2, z.1 i)
      invFun := fun z => (Function.update z.1 i z.2, z.1 i)
      left_inv := by intro z; simp
      right_inv := by intro z; simp }
  have hup (x : J → Bool) (b : Bool) :
      (∏ j ∈ Finset.univ.erase i, w (Function.update x i b j)) =
        ∏ j ∈ Finset.univ.erase i, w (x j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  have he := Fintype.sum_equiv e
    (fun z => w z.2 * (∏ j ∈ Finset.univ.erase i, w (z.1 j)) * t (z.1 i) * g z.1)
    (fun z => (∏ j : J, w (z.1 j)) * t z.2 * g (Function.update z.1 i z.2)) (by
      intro z
      dsimp [e]
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self, hup]
      simp)
  simp only [Fintype.sum_prod_type] at he
  simp_rw [← Finset.sum_mul] at he
  rw [hw] at he
  simpa only [one_mul, Finset.mul_sum, mul_assoc] using he

omit [Fintype J] in
/-- If [the Boolean response is increasing in every coordinate](hyp:hf),
[its value with a selected coordinate set to true minus its value with that
coordinate set to false is one when the two responses differ and zero otherwise](goal). -/
-- @node: increasing_section_difference
lemma increasing_section_difference (f : (J → Bool) → Bool) (hf : Monotone f)
    (x : J → Bool) (i : J) :
    boolValue f (replaceCoord x i true) - boolValue f (replaceCoord x i false) =
      if f (replaceCoord x i true) ≠ f (replaceCoord x i false) then 1 else 0 := by
  have hm : f (replaceCoord x i false) ≤ f (replaceCoord x i true) := by
    apply hf
    intro j
    by_cases h : j = i
    · subst j; simp [replaceCoord]
    · simp [replaceCoord, Function.update_of_ne h]
  cases ht : f (replaceCoord x i true) <;>
    cases hb : f (replaceCoord x i false) <;>
      simp_all only [boolValue, ne_eq, Bool.false_eq_true, not_false_eq_true, ↓reduceIte,
        sub_self, sub_zero, Bool.true_eq_false, not_true_eq_false]
  exact Bool.noConfusion (hm rfl)

-- @node: russo_margulis
/-- If [the Boolean response is increasing and nonconstant](hyp:hf) and
[the Bernoulli bias is strictly between zero and one](hyp:hp), [the derivative
of its probability curve at that bias equals its total coordinate influence](goal). -/
lemma russo_margulis (f : (J → Bool) → Bool) (hf : IsIncreasingNontrivial f)
    (p : ℝ) (hp : BiasInterior p) :
    HasDerivAt (probCurve f) (totalCoordInfluence p f) p := by
  let w : Bool → ℝ := fun b => if b then p else 1 - p
  let t : Bool → ℝ := fun b => if b then 1 else -1
  have hw : ∑ b, w b = 1 := by simp [w]
  have hcoin (b : Bool) : HasDerivAt (fun q : ℝ => if b then q else 1 - q) (t b) p := by
    cases b
    · simpa [t] using (hasDerivAt_id p).const_sub 1
    · simpa [t] using hasDerivAt_id' p
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun x _ =>
    (HasDerivAt.fun_finsetProd (u := Finset.univ) (fun j _ => hcoin (x j))).mul_const
      (boolValue f x))
  have hcoeff :
      (∑ x : J → Bool, (∑ i : J,
        (∏ j ∈ Finset.univ.erase i, w (x j)) * t (x i)) * boolValue f x) =
      totalCoordInfluence p f := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    unfold totalCoordInfluence
    apply Finset.sum_congr rfl
    intro i _
    rw [bernoulli_sum_erase_resample w t hw]
    simp only [Fintype.sum_bool, t, Bool.false_eq_true, ↓reduceIte, neg_one_mul,
      one_mul, ← sub_eq_add_neg]
    simp_rw [increasing_section_difference f hf.mono]
    rw [coordInfluence, biasedLaw_eq_bernoulliDesign p ⟨hp.1.le, hp.2.le⟩]
    simp [FiniteDesign.Pr, FiniteDesign.E, FiniteDesign.ind, bernoulliDesign,
      prodDesign_p, coinDesign, w, Bool.cond_eq_ite]
  have hpoly : HasDerivAt (fun q => (probabilityPolynomial f).eval q)
      (totalCoordInfluence p f) p := by
    rw [← hcoeff]
    simpa only [probabilityPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_prod, apply_ite, Polynomial.eval_X,
      Polynomial.eval_sub, Polynomial.eval_one, smul_eq_mul, w, t, mul_comm] using hd
  apply hpoly.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hp] with q hq
  exact (probabilityPolynomial_eval f q ⟨hq.1.le, hq.2.le⟩).symm

-- @node: probCurve_endpoints
/-- If [the Boolean response is increasing and nonconstant](hyp:hf),
[its probability curve is zero at bias zero and one at bias one](goal). -/
lemma probCurve_endpoints (f : (J → Bool) → Bool) (hf : IsIncreasingNontrivial f) :
    probCurve f 0 = 0 ∧ probCurve f 1 = 1 := by
  have hbot : f (fun _ => false) = false := by
    by_contra h
    have ht : f (fun _ => false) = true := by simpa using h
    have hc : ∀ x, f x = true := by
      intro x
      have hx := hf.mono (show (fun _ : J => false) ≤ x from bot_le)
      exact le_antisymm le_top (by simpa [ht] using hx)
    obtain ⟨x, y, hxy⟩ := hf.nonconst
    exact hxy ((hc x).trans (hc y).symm)
  have htop : f (fun _ => true) = true := by
    by_contra h
    have ht : f (fun _ => true) = false := by simpa using h
    have hc : ∀ x, f x = false := by
      intro x
      have hx := hf.mono (show x ≤ (fun _ : J => true) from le_top)
      exact le_antisymm (by simpa [ht] using hx) bot_le
    obtain ⟨x, y, hxy⟩ := hf.nonconst
    exact hxy ((hc x).trans (hc y).symm)
  constructor
  · rw [← probabilityPolynomial_eval f 0 (by simp)]
    simp only [probabilityPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_prod]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : x = fun _ => false
    · simp [hx, boolValue, hbot]
    · have hi : ∃ i, x i = true := by
        by_contra hn
        apply hx
        funext i
        have : x i ≠ true := by intro h; exact hn ⟨i, h⟩
        simpa using this
      obtain ⟨i, hi⟩ := hi
      have hz : (∏ j : J, Polynomial.eval (0 : ℝ)
          (if x j then Polynomial.X else 1 - Polynomial.X)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
      rw [hz, mul_zero]
  · rw [← probabilityPolynomial_eval f 1 (by simp)]
    simp only [probabilityPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_prod]
    rw [Finset.sum_eq_single (fun _ : J => true)]
    · simp [boolValue, htop]
    · intro x _ hx
      have hi : ∃ i, x i = false := by
        by_contra hn
        apply hx
        funext i
        have : x i ≠ false := by intro h; exact hn ⟨i, h⟩
        simpa using this
      obtain ⟨i, hi⟩ := hi
      have hz : (∏ j : J, Polynomial.eval (1 : ℝ)
          (if x j then Polynomial.X else 1 - Polynomial.X)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
      rw [hz, mul_zero]
    · simp

-- @node: biasedLaw_mass_pos
/-- If [the Bernoulli bias is strictly between zero and one](hyp:hp),
[every Boolean configuration has strictly positive probability under the
biased product distribution](goal). -/
lemma biasedLaw_mass_pos (p : ℝ) (hp : BiasInterior p) (x : J → Bool) :
    0 < (biasedLaw J p).p x := by
  rw [biasedLaw_eq_bernoulliDesign p ⟨hp.1.le, hp.2.le⟩]
  simp only [bernoulliDesign, prodDesign_p]
  apply Finset.prod_pos
  intro i _
  cases x i <;> simp only [coinDesign, cond_false, cond_true]
  · exact sub_pos.mpr hp.2
  · exact hp.1

-- @node: boolean_variance_pos_of_nonconstant
/-- If [the Boolean response takes different values on two configurations](hyp:hf)
and [the Bernoulli bias is strictly between zero and one](hyp:hp),
[its variance under the biased product distribution is strictly positive](goal). -/
lemma boolean_variance_pos_of_nonconstant (f : (J → Bool) → Bool)
    (hf : ∃ x y, f x ≠ f y) (p : ℝ) (hp : BiasInterior p) :
    0 < (biasedLaw J p).Var (boolValue f) := by
  obtain ⟨x, y, hxy⟩ := hf
  have hval : boolValue f x ≠ boolValue f y := by
    cases hx : f x <;> cases hy : f y <;> simp_all [boolValue]
  have hw : ∃ z, boolValue f z ≠ (biasedLaw J p).E (boolValue f) := by
    by_cases hx : boolValue f x = (biasedLaw J p).E (boolValue f)
    · exact ⟨y, fun hy => hval (hx.trans hy.symm)⟩
    · exact ⟨x, hx⟩
  obtain ⟨z, hz⟩ := hw
  unfold FiniteDesign.Var FiniteDesign.E
  apply Finset.sum_pos'
  · intro w _
    exact mul_nonneg ((biasedLaw J p).p_nonneg w) (sq_nonneg _)
  · refine ⟨z, Finset.mem_univ _, mul_pos (biasedLaw_mass_pos p hp z) ?_⟩
    exact sq_pos_of_ne_zero (sub_ne_zero.mpr hz)

-- @node: probCurve_derivative_pos
/-- If [the Boolean response is increasing and nonconstant](hyp:hf) and
[the Bernoulli bias is strictly between zero and one](hyp:hp),
[its total coordinate influence at that bias is strictly positive](goal). -/
lemma probCurve_derivative_pos (f : (J → Bool) → Bool) (hf : IsIncreasingNontrivial f)
    (p : ℝ) (hp : BiasInterior p) :
    0 < totalCoordInfluence p f := by
  have hv := boolean_variance_pos_of_nonconstant f hf.nonconst p hp
  have hbound := variance_le_biasScale_sq_mul_influence p hp f
  have hprod : 0 < biasScale p ^ 2 * totalCoordInfluence p f := hv.trans_le hbound
  exact (mul_pos_iff.mp hprod).resolve_right (by
    rintro ⟨hneg, _⟩
    exact (sq_nonneg (biasScale p)).not_gt hneg) |>.2

-- @node: probCurve_strictMonoOn
/-- If [the Boolean response is increasing and nonconstant](hyp:hf),
[its probability curve is strictly increasing on the closed interval from
zero to one](goal). -/
lemma probCurve_strictMonoOn (f : (J → Bool) → Bool) (hf : IsIncreasingNontrivial f) :
    StrictMonoOn (probCurve f) (Set.Icc 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1) (probCurve_continuous f).continuousOn
  intro p hp
  rw [interior_Icc] at hp
  rw [(russo_margulis f hf p hp).deriv]
  exact probCurve_derivative_pos f hf p hp

-- @node: probCurve_interior
/-- If [the Boolean response is increasing and nonconstant](hyp:hf) and
[the Bernoulli bias is strictly between zero and one](hyp:hp),
[the probability of a true response is also strictly between zero and one](goal). -/
lemma probCurve_interior (f : (J → Bool) → Bool) (hf : IsIncreasingNontrivial f)
    (p : ℝ) (hp : BiasInterior p) :
    0 < probCurve f p ∧ probCurve f p < 1 := by
  have hs := probCurve_strictMonoOn f hf
  have he := probCurve_endpoints f hf
  constructor
  · rw [← he.1]
    exact hs (by simp) ⟨hp.1.le, hp.2.le⟩ hp.1
  · rw [← he.2]
    exact hs ⟨hp.1.le, hp.2.le⟩ (by simp) hp.2

-- @node: thresholdQuantile_spec
/-- If [the Boolean response is increasing and nonconstant](hyp:hf) and
[the target probability is strictly between zero and one](hyp:ha),
[its threshold quantile lies strictly between zero and one, attains the target
probability, and is the unique bias in the closed unit interval attaining it](goal). -/
lemma thresholdQuantile_spec (f : (J → Bool) → Bool) (hf : IsIncreasingNontrivial f)
    (a : ℝ) (ha : 0 < a ∧ a < 1) : -- @realizes a(quantile level in (0,1))
    thresholdQuantile f a ∈ Set.Ioo 0 1 ∧
      probCurve f (thresholdQuantile f a) = a ∧
      ∀ p ∈ Set.Icc (0 : ℝ) 1, probCurve f p = a → p = thresholdQuantile f a := by
  have hs := probCurve_strictMonoOn f hf
  have he := probCurve_endpoints f hf
  obtain ⟨p, hp, hpa⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    (probCurve_continuous f).continuousOn
    (show a ∈ Set.Icc (probCurve f 0) (probCurve f 1) by rw [he.1, he.2]; exact ⟨ha.1.le, ha.2.le⟩)
  have hq : thresholdQuantile f a = p := by
    apply IsLeast.csInf_eq
    refine ⟨⟨hp, hpa.ge⟩, ?_⟩
    intro t ht
    exact (hs.le_iff_le hp ht.1).mp (by rw [hpa]; exact ht.2)
  rw [hq]
  refine ⟨⟨?_, ?_⟩, hpa, ?_⟩
  · by_contra hn
    have : p = 0 := le_antisymm (not_lt.mp hn) hp.1
    rw [this, he.1] at hpa
    linarith [ha.1]
  · by_contra hn
    have : p = 1 := le_antisymm hp.2 (not_lt.mp hn)
    rw [this, he.2] at hpa
    linarith [ha.2]
  · intro t ht hta
    exact hs.injOn ht hp (hta.trans hpa.symm)

-- @node: thresholdQuantile_strictMonoOn
/-- If [the Boolean response is increasing and nonconstant](hyp:hf),
[its threshold quantile is strictly increasing as the target probability ranges
strictly between zero and one](goal). -/
lemma thresholdQuantile_strictMonoOn (f : (J → Bool) → Bool) (hf : IsIncreasingNontrivial f) :
    StrictMonoOn (thresholdQuantile f) (Set.Ioo 0 1) := by
  intro a ha b hb hab
  have hqa := thresholdQuantile_spec f hf a ha
  have hqb := thresholdQuantile_spec f hf b hb
  apply (probCurve_strictMonoOn f hf).lt_iff_lt
    ⟨hqa.1.1.le, hqa.1.2.le⟩ ⟨hqb.1.1.le, hqb.1.2.le⟩ |>.mp
  simpa only [hqa.2.1, hqb.2.1] using hab

-- @node: logOdds_hasDerivAt
/-- If [the Boolean response is increasing and nonconstant](hyp:hf) and
[the Bernoulli bias is strictly between zero and one](hyp:hp),
[the derivative of its log odds at that bias equals total coordinate influence
divided by the product of its success and failure probabilities](goal). -/
lemma logOdds_hasDerivAt (f : (J → Bool) → Bool) (hf : IsIncreasingNontrivial f)
    (p : ℝ) (hp : BiasInterior p) :
    HasDerivAt (fun t => Real.log (probCurve f t / (1 - probCurve f t)))
      (totalCoordInfluence p f / (probCurve f p * (1 - probCurve f p))) p := by
  have hq := probCurve_interior f hf p hp
  have h0 : probCurve f p ≠ 0 := ne_of_gt hq.1
  have h1 : 1 - probCurve f p ≠ 0 := ne_of_gt (sub_pos.mpr hq.2)
  have hd := russo_margulis f hf p hp
  have hquot := hd.div (hd.const_sub 1) h1
  have hlog := hquot.log (div_ne_zero h0 h1)
  simp only [Pi.div_apply] at hlog
  convert hlog using 1
  field_simp [h0, h1]
  ring

/-- Suppose [the Boolean response is increasing and nonconstant](hyp:hf),
[the tail probability ε is strictly between zero and one half](hyp:hε),
[A is strictly positive](hyp:hA), and [at every interior bias, total coordinate
influence divided by the product of the success and failure probabilities is
at least A](hyp:hderiv). Then [the threshold width between probabilities ε and
1 − ε is at most (2/A) log((1 − ε)/ε)](goal). -/
-- @node: thresholdWidth_le_of_logOdds_derivative_bound
lemma thresholdWidth_le_of_logOdds_derivative_bound (f : (J → Bool) → Bool)
    (hf : IsIncreasingNontrivial f) (ε : ℝ) (hε : ThresholdEpsilon ε)
    (A : ℝ) (hA : 0 < A)
    (hderiv : ∀ p : ℝ, BiasInterior p →
      A ≤ totalCoordInfluence p f / (probCurve f p * (1 - probCurve f p))) :
    thresholdWidth f ε ≤ 2 / A * Real.log ((1 - ε) / ε) := by
  have he : 0 < ε ∧ ε < 1 := ⟨hε.1, by have := hε.2; linarith⟩
  have he' : 0 < 1 - ε ∧ 1 - ε < 1 := by constructor <;> linarith [he.1, he.2]
  have hqa := thresholdQuantile_spec f hf ε he
  have hqb := thresholdQuantile_spec f hf (1 - ε) he'
  have hab : thresholdQuantile f ε < thresholdQuantile f (1 - ε) :=
    thresholdQuantile_strictMonoOn f hf he he' (by have := hε.2; linarith)
  let D := Set.Icc (thresholdQuantile f ε) (thresholdQuantile f (1 - ε))
  let g := fun t => Real.log (probCurve f t / (1 - probCurve f t))
  have hD : ∀ p ∈ D, BiasInterior p := by
    intro p hp
    exact ⟨lt_of_lt_of_le hqa.1.1 hp.1, lt_of_le_of_lt hp.2 hqb.1.2⟩
  have hg : ∀ p ∈ D, HasDerivAt g
      (totalCoordInfluence p f / (probCurve f p * (1 - probCurve f p))) p := by
    intro p hp
    exact logOdds_hasDerivAt f hf p (hD p hp)
  have hint : interior D ⊆ D := interior_subset
  have hconv : Convex ℝ D := convex_Icc _ _
  have hbound := hconv.mul_sub_le_image_sub_of_le_deriv
    (show ContinuousOn g D from fun p hp => (hg p hp).continuousAt.continuousWithinAt)
    (show DifferentiableOn ℝ g (interior D) from
      fun p hp => (hg p (hint hp)).differentiableAt.differentiableWithinAt)
    (show ∀ p ∈ interior D, A ≤ deriv g p from by
      intro p hp
      rw [(hg p (hint hp)).deriv]
      exact hderiv p (hD p (hint hp)))
    (thresholdQuantile f ε) ⟨le_rfl, hab.le⟩
    (thresholdQuantile f (1 - ε)) ⟨hab.le, le_rfl⟩ hab.le
  have hvalues : g (thresholdQuantile f (1 - ε)) - g (thresholdQuantile f ε) =
      2 * Real.log ((1 - ε) / ε) := by
    dsimp [g]
    rw [hqb.2.1, hqa.2.1]
    have hsub : 1 - (1 - ε) = ε := by ring
    rw [hsub, Real.log_div (ne_of_gt he.1) (ne_of_gt he'.1),
      Real.log_div (ne_of_gt he'.1) (ne_of_gt he.1)]
    ring
  rw [hvalues] at hbound
  unfold thresholdWidth
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hA).mpr (by simpa only [mul_comm A] using hbound)


end Papers.OaiUniformInfluenceHypergraph
