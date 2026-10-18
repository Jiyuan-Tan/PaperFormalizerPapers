module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLConditionalFluctuation
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.Independence.Basic
/-! Conditional moments of a fitted score under training/evaluation independence.
The sample space itself needs no standard Borel structure. The evaluation record
has the standard Borel structure already supplied by the observation space. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory

-- @node: dml_independent_condDistrib
/-- If [the training view is measurable](hyp:hT), [the evaluation record is measurable](hyp:hW),
and [the two are independent](hyp:hind), then [the conditional distribution of the evaluation
record given training equals its marginal distribution for almost every training view](goal). -/
lemma dml_independent_condDistrib {A D B : Type*}
    [MeasurableSpace A] [MeasurableSpace D] [MeasurableSpace B]
    [StandardBorelSpace B] [Nonempty B]
    (μ : Measure A) [IsProbabilityMeasure μ]
    (T : A → D) (W : A → B) (hT : Measurable T) (hW : Measurable W)
    (hind : IndepFun T W μ) :
    condDistrib W T μ =ᵐ[μ.map T] Kernel.const D (μ.map W) := by
  apply condDistrib_ae_eq_of_measure_eq_compProd T hW.aemeasurable
  rw [Measure.compProd_const]
  exact hind.map_prod_eq_prod_map_map hT.aemeasurable hW.aemeasurable

-- @node: dml_independent_fitted_score_condExp
/-- Suppose [training is measurable](hyp:hT), [the evaluation record is measurable](hyp:hW),
[training and evaluation are independent](hyp:hind), and [the evaluation law is P](hyp:hlaw).
If [the fitted score is measurable](hyp:hf) and [its evaluated value is integrable](hyp:hint),
then [its conditional expectation given training equals its population integral with training held fixed,
almost surely](goal). -/
lemma dml_independent_fitted_score_condExp {A D B : Type*}
    [MeasurableSpace A] [MeasurableSpace D] [MeasurableSpace B]
    [StandardBorelSpace B] [Nonempty B]
    (μ : Measure A) [IsProbabilityMeasure μ]
    (P : Measure B) (T : A → D) (W : A → B)
    (hT : Measurable T) (hW : Measurable W) (hind : IndepFun T W μ)
    (hlaw : μ.map W = P) (f : D × B → ℝ) (hf : Measurable f)
    (hint : Integrable (fun a => f (T a, W a)) μ) :
    μ[fun a => f (T a, W a) | MeasurableSpace.comap T inferInstance] =ᵐ[μ]
      (fun a => ∫ b, f (T a, b) ∂P) := by
  have hkernel := ae_of_ae_map hT.aemeasurable
    (dml_independent_condDistrib μ T W hT hW hind)
  have hce := condExp_prod_ae_eq_integral_condDistrib hT hW.aemeasurable
    hf.stronglyMeasurable hint
  filter_upwards [hce, hkernel] with a ha hk
  rw [ha, hk, Kernel.const_apply, hlaw]

-- Centering by the population mean of the training-fixed fitted score makes
-- its conditional mean zero; this is not an assumed conditional identity.
-- @node: dml_independent_centered_score_condExp
/-- Suppose [training is measurable](hyp:hT), [evaluation is measurable](hyp:hW),
[training and evaluation are independent](hyp:hind), and [evaluation has law P](hyp:hlaw).
If [the score is measurable](hyp:hf), [each score with training fixed is integrable under P](hyp:hsection),
and [the population-centered evaluated score is integrable](hyp:hint), then
[that centered score has conditional mean zero given training, almost surely](goal). -/
lemma dml_independent_centered_score_condExp {A D B : Type*}
    [MeasurableSpace A] [MeasurableSpace D] [MeasurableSpace B]
    [StandardBorelSpace B] [Nonempty B]
    (μ : Measure A) [IsProbabilityMeasure μ]
    (P : Measure B) [IsProbabilityMeasure P] (T : A → D) (W : A → B)
    (hT : Measurable T) (hW : Measurable W) (hind : IndepFun T W μ)
    (hlaw : μ.map W = P) (f : D × B → ℝ) (hf : Measurable f)
    (hsection : ∀ t, Integrable (fun b => f (t, b)) P)
    (hint : Integrable (fun a => f (T a, W a) - ∫ b, f (T a, b) ∂P) μ) :
    μ[fun a => f (T a, W a) - ∫ b, f (T a, b) ∂P |
      MeasurableSpace.comap T inferInstance] =ᵐ[μ] 0 := by
  have hm : Measurable (fun t => ∫ b, f (t, b) ∂P) :=
    hf.stronglyMeasurable.integral_prod_right'.measurable
  have hg : Measurable (fun tb : D × B => f tb - ∫ b, f (tb.1, b) ∂P) := by
    exact hf.sub (hm.comp measurable_fst)
  have hce := dml_independent_fitted_score_condExp μ P T W hT hW hind hlaw
    (fun tb => f tb - ∫ b, f (tb.1, b) ∂P) hg hint
  filter_upwards [hce] with a ha
  rw [ha, integral_sub (hsection (T a)) (integrable_const _)]
  simp

-- Two independent evaluation records, jointly independent of the training
-- view, kill the cross moment even though both fitted scores share that view.
-- @node: dml_independent_centered_score_cross_moment
/-- Suppose [training is measurable](hyp:hT), [both evaluation records are measurable](hyp:hW₁,hW₂),
[training is independent of their pair](hyp:htrain), [the records are mutually independent](hyp:heval),
and [each record has law P](hyp:hlaw₁,hlaw₂). If [the score is measurable](hyp:hf),
[its training-fixed sections are integrable](hyp:hsection), and [the product of the two
population-centered scores is integrable](hyp:hint), then [their conditional cross moment
given training is zero almost surely](goal). -/
lemma dml_independent_centered_score_cross_moment {A D B : Type*}
    [MeasurableSpace A] [MeasurableSpace D] [MeasurableSpace B]
    [StandardBorelSpace B] [Nonempty B]
    (μ : Measure A) [IsProbabilityMeasure μ]
    (P : Measure B) [IsProbabilityMeasure P]
    (T : A → D) (W₁ W₂ : A → B)
    (hT : Measurable T) (hW₁ : Measurable W₁) (hW₂ : Measurable W₂)
    (htrain : IndepFun T (fun a => (W₁ a, W₂ a)) μ)
    (heval : IndepFun W₁ W₂ μ)
    (hlaw₁ : μ.map W₁ = P) (hlaw₂ : μ.map W₂ = P)
    (f : D × B → ℝ) (hf : Measurable f)
    (hsection : ∀ t, Integrable (fun b => f (t, b)) P)
    (hint : Integrable (fun a =>
      (f (T a, W₁ a) - ∫ b, f (T a, b) ∂P) *
      (f (T a, W₂ a) - ∫ b, f (T a, b) ∂P)) μ) :
    μ[fun a => (f (T a, W₁ a) - ∫ b, f (T a, b) ∂P) *
      (f (T a, W₂ a) - ∫ b, f (T a, b) ∂P) |
      MeasurableSpace.comap T inferInstance] =ᵐ[μ] 0 := by
  have hm : Measurable (fun t => ∫ b, f (t, b) ∂P) :=
    hf.stronglyMeasurable.integral_prod_right'.measurable
  have hg : Measurable (fun tb : D × (B × B) =>
      (f (tb.1, tb.2.1) - ∫ b, f (tb.1, b) ∂P) *
      (f (tb.1, tb.2.2) - ∫ b, f (tb.1, b) ∂P)) := by
    exact ((hf.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).sub
      (hm.comp measurable_fst)).mul
      ((hf.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))).sub
        (hm.comp measurable_fst))
  have hpair : μ.map (fun a => (W₁ a, W₂ a)) = P.prod P := by
    rw [heval.map_prod_eq_prod_map_map hW₁.aemeasurable hW₂.aemeasurable,
      hlaw₁, hlaw₂]
  have hce := dml_independent_fitted_score_condExp μ (P.prod P) T
    (fun a => (W₁ a, W₂ a)) hT (hW₁.prodMk hW₂) htrain hpair _ hg hint
  filter_upwards [hce] with a ha
  rw [ha, integral_prod_mul
    (fun b => f (T a, b) - ∫ b, f (T a, b) ∂P)
    (fun b => f (T a, b) - ∫ b, f (T a, b) ∂P)]
  rw [integral_sub (hsection (T a)) (integrable_const _)]
  simp

-- This supplies all the conditional moments required by Chebyshev from
-- independence and the fitted score's population L2 energy. Only the score
-- convergence rate remains as input; empirical negligibility is derived.
-- @node: dml_independent_centered_evaluation_sum_tendsto
/-- For [rows of evaluation records containing one more record than the row index](hyp:W), suppose [each training view is measurable](hyp:hT), [each evaluation record is measurable](hyp:hW),
[training is independent of every individual record](hyp:hsingle) and [every distinct pair](hyp:htrain),
[distinct evaluation records are independent](hyp:heval), and [all evaluation records have law P](hyp:hlaw).
If [each score is measurable](hyp:hf), [its training-fixed sections are square integrable](hyp:hsection),
[its evaluated values are square integrable](hyp:hfit), and [its training-fixed population second
moment tends to zero in probability](hyp:hrate), then [the sum of the population-centered evaluation
scores, divided by the square root of the number of records, tends to zero in probability](goal). -/
lemma dml_independent_centered_evaluation_sum_tendsto {A D B : Type*}
    [mA : MeasurableSpace A] [MeasurableSpace D] [MeasurableSpace B]
    [StandardBorelSpace B] [Nonempty B]
    (μ : Measure A) [IsProbabilityMeasure μ]
    (P : Measure B) [IsProbabilityMeasure P]
    (T : ℕ → A → D) (W : ∀ n, Fin (n + 1) → A → B)
    (hT : ∀ n, Measurable (T n)) (hW : ∀ n i, Measurable (W n i))
    (hsingle : ∀ n i, IndepFun (T n) (W n i) μ)
    (htrain : ∀ n i j, i ≠ j →
      IndepFun (T n) (fun a => (W n i a, W n j a)) μ)
    (heval : ∀ n i j, i ≠ j → IndepFun (W n i) (W n j) μ)
    (hlaw : ∀ n i, μ.map (W n i) = P)
    (f : ℕ → D × B → ℝ) (hf : ∀ n, Measurable (f n))
    (hsection : ∀ n t, MemLp (fun b => f n (t, b)) 2 P)
    (hfit : ∀ n i, MemLp (fun a => f n (T n a, W n i a)) 2 μ)
    (hrate : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ b, f n (T n a, b) ^ 2 ∂P) Filter.atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ *
        ∑ i, (f n (T n a, W n i a) - ∫ b, f n (T n a, b) ∂P))
      Filter.atTop (fun _ _ => 0) := by
  let m := fun n => MeasurableSpace.comap (T n) inferInstance
  have hm : ∀ n, m n ≤ mA := fun n => (hT n).comap_le
  let : ∀ n, SigmaFinite (μ.trim (hm n)) := fun n => inferInstance
  have hmean (n : ℕ) (i : Fin (n + 1)) :
      μ[fun a => f n (T n a, W n i a) | m n] =ᵐ[μ]
        (fun a => ∫ b, f n (T n a, b) ∂P) :=
    dml_independent_fitted_score_condExp μ P (T n) (W n i)
      (hT n) (hW n i) (hsingle n i) (hlaw n i) (f n) (hf n)
      ((hfit n i).integrable (by norm_num))
  have hcenter (n : ℕ) (i : Fin (n + 1)) :
      MemLp (fun a => f n (T n a, W n i a) - ∫ b, f n (T n a, b) ∂P) 2 μ := by
    have hb := (MemLp.condExp (m := m n) (by norm_num) (hfit n i)).ae_eq
      (hmean n i)
    exact (hfit n i).sub hb
  apply conditional_centered_score_sum_tendsto_probability_zero μ m hm
    (fun n i a => f n (T n a, W n i a))
    (fun n a => ∫ b, f n (T n a, b) ∂P)
    (fun n a => ∫ b, f n (T n a, b) ^ 2 ∂P) hfit hmean
  · intro n i j hij
    exact dml_independent_centered_score_cross_moment μ P (T n) (W n i) (W n j)
      (hT n) (hW n i) (hW n j) (htrain n i j hij) (heval n i j hij)
      (hlaw n i) (hlaw n j) (f n) (hf n)
      (fun t => (hsection n t).integrable (by norm_num))
      ((hcenter n i).integrable_mul (hcenter n j))
  · intro n i
    have hsq : Measurable (fun tb => f n tb ^ 2) := by fun_prop
    exact (dml_independent_fitted_score_condExp μ P (T n) (W n i)
      (hT n) (hW n i) (hsingle n i) (hlaw n i)
      (fun tb => f n tb ^ 2) hsq (hfit n i).integrable_sq).le
  · intro n
    have hsq : Measurable (fun tb => f n tb ^ 2) := by fun_prop
    have henergy : Measurable (fun t => ∫ b, f n (t, b) ^ 2 ∂P) := by
      first | fun_prop | exact hsq.stronglyMeasurable.integral_prod_right'.measurable
    exact henergy.comp (Measurable.of_comap_le le_rfl)
  · exact hrate

end Papers.TbsPrteOptimalTransport
