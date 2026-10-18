module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLIndependentScoreMoments
/-! Held-out squared score errors from population L² convergence.
Conditional Markov controls the empirical error without requiring its
unconditional expectation to tend to zero or evaluation pair independence. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

-- @node: dml_independent_empirical_score_energy_condExp
/-- If [training is measurable](hyp:hT), [each evaluation record is measurable](hyp:hW),
[each record is independent of training](hyp:hind), [each has law P](hyp:hlaw),
[the score is measurable](hyp:hf), and [each evaluated score is square integrable](hyp:hfit),
then [the conditional expectation of the average squared evaluation score given training
equals its training-fixed population second moment almost surely](goal). -/
lemma dml_independent_empirical_score_energy_condExp {A D B ι : Type*}
    [mA : MeasurableSpace A] [MeasurableSpace D] [MeasurableSpace B]
    [StandardBorelSpace B] [Nonempty B] [Fintype ι] [Nonempty ι]
    (μ : Measure A) [IsProbabilityMeasure μ] (P : Measure B)
    (T : A → D) (W : ι → A → B)
    (hT : Measurable T) (hW : ∀ i, Measurable (W i))
    (hind : ∀ i, IndepFun T (W i) μ) (hlaw : ∀ i, μ.map (W i) = P)
    (f : D × B → ℝ) (hf : Measurable f)
    (hfit : ∀ i, MemLp (fun a => f (T a, W i a)) 2 μ) :
    μ[fun a => (Fintype.card ι : ℝ)⁻¹ * ∑ i, f (T a, W i a) ^ 2 |
      MeasurableSpace.comap T inferInstance] =ᵐ[μ]
      (fun a => ∫ b, f (T a, b) ^ 2 ∂P) := by
  classical
  let m := MeasurableSpace.comap T inferInstance
  let : MeasurableSpace A := mA
  have hsq : Measurable (fun tb => f tb ^ 2) := by fun_prop
  have hsingle (i : ι) := dml_independent_fitted_score_condExp μ P T (W i)
    hT (hW i) (hind i) (hlaw i) (fun tb => f tb ^ 2) hsq (hfit i).integrable_sq
  have hsum := condExp_finsetSum
    (f := fun i a => f (T a, W i a) ^ 2)
    (fun i (_ : i ∈ (Finset.univ : Finset ι)) => (hfit i).integrable_sq) m
  have hscale := condExp_smul (μ := μ) (Fintype.card ι : ℝ)⁻¹
    (∑ i, (fun a => f (T a, W i a) ^ 2)) m
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_pos.ne'
  filter_upwards [hscale, hsum, ae_all_iff.mpr hsingle] with a ha hs hi
  simp only [Finset.sum_fn, Pi.smul_def, smul_eq_mul] at ha hs
  rw [ha, hs]
  simp only [m, hi, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

-- The random training energy need only vanish in probability. Integrating
-- that energy unconditionally would impose an unnecessary stronger rate.
-- @node: dml_independent_empirical_score_energy_tendsto
/-- For [rows of evaluation records containing one more record than the row index](hyp:W), suppose [training views are measurable](hyp:hT), [evaluation records are measurable](hyp:hW),
[each record is independent of its training view](hyp:hind), and [all records have law P](hyp:hlaw).
If [the scores are measurable](hyp:hf), [their evaluated values are square integrable](hyp:hfit),
and [their training-fixed population second moments vanish in probability](hyp:hrate), then
[the average squared evaluation score vanishes in probability](goal). -/
lemma dml_independent_empirical_score_energy_tendsto {A D B : Type*}
    [mA : MeasurableSpace A] [MeasurableSpace D] [MeasurableSpace B]
    [StandardBorelSpace B] [Nonempty B]
    (μ : Measure A) [IsProbabilityMeasure μ] (P : Measure B)
    (T : ℕ → A → D) (W : ∀ n, Fin (n + 1) → A → B)
    (hT : ∀ n, Measurable (T n)) (hW : ∀ n i, Measurable (W n i))
    (hind : ∀ n i, IndepFun (T n) (W n i) μ)
    (hlaw : ∀ n i, μ.map (W n i) = P)
    (f : ℕ → D × B → ℝ) (hf : ∀ n, Measurable (f n))
    (hfit : ∀ n i, MemLp (fun a => f n (T n a, W n i a)) 2 μ)
    (hrate : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ b, f n (T n a, b) ^ 2 ∂P) atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i, f n (T n a, W n i a) ^ 2)
      atTop (fun _ _ => 0) := by
  letI : IsProbabilityMeasure P := by
    rw [← hlaw 0 0]
    exact Measure.isProbabilityMeasure_map (hW 0 0).aemeasurable
  let m := fun n => MeasurableSpace.comap (T n) inferInstance
  have hm : ∀ n, m n ≤ mA := fun n => (hT n).comap_le
  let : ∀ n, SigmaFinite (μ.trim (hm n)) := fun n => inferInstance
  apply conditional_nonneg_tendsto_probability_zero μ m hm _
    (fun n a => ∫ b, f n (T n a, b) ^ 2 ∂P)
  · intro n
    have hsq : Measurable (fun tb => f n tb ^ 2) := by fun_prop
    have henergy : Measurable (fun t => ∫ b, f n (t, b) ^ 2 ∂P) := by
      first | fun_prop | exact hsq.stronglyMeasurable.integral_prod_right'.measurable
    exact henergy.comp (Measurable.of_comap_le le_rfl)
  · intro n
    simpa only [Finset.sum_apply] using (integrable_finsetSum' Finset.univ
      (fun i _ => (hfit n i).integrable_sq)).const_mul ((n + 1 : ℕ) : ℝ)⁻¹
  · intro n
    exact Eventually.of_forall (fun a => mul_nonneg (by positivity)
      (Finset.sum_nonneg (fun i _ => sq_nonneg _)))
  · intro n
    have hce := dml_independent_empirical_score_energy_condExp μ P (T n) (W n)
      (hT n) (hW n) (hind n) (hlaw n) (f n) (hf n) (hfit n)
    simpa only [Fintype.card_fin] using hce.le
  · exact hrate

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} {D : Type*}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z]
  [MeasurableSpace A] [MeasurableSpace D]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- An enumeration of the random evaluation half connects the conditional
-- moment argument to the paper's actual Finset-indexed variance statistic.
-- No empirical score-error convergence is assumed in this assembly.
-- @node: varianceRV_consistent_of_independent_score_energy
/-- For [sample-dependent observation indices for each evaluation row](hyp:J), suppose [the row indices enumerate the evaluation half injectively almost surely](hyp:hrow),
[training views are measurable](hyp:hT), [the indexed observations are measurable](hyp:hW),
[each is independent of training](hyp:hind), and [each has the model's observation law](hyp:hlaw).
Assume [the fitted score factors through training and the observation](hyp:hscore),
[this factor is measurable](hyp:hf), [the true score is measurable](hyp:hg),
[evaluated score errors are square integrable](hyp:hfit), and [their training-fixed population
second moments vanish in probability](hyp:hrate). If [the oracle second moment centered at theta
converges to sigma squared](hyp:hV) and [the fitted mean converges to theta](hyp:hb), then
[the fitted variance estimator converges in probability to sigma squared](goal). -/
lemma varianceRV_consistent_of_independent_score_energy
    (M : LatentIVModel Ω X Z) (μ : Measure A) [IsProbabilityMeasure μ]
    (S : ObservedSample M μ) (I₂ : SampleSplit A) (N : ℕ → ℕ)
    (T : ℕ → A → D) (J : ∀ n, A → Fin (n + 1) → ℕ)
    (hrow : ∀ n, ∀ᵐ a ∂μ, Function.Injective (J n a) ∧
      Finset.univ.image (J n a) = I₂ (N n) a)
    (hT : ∀ n, Measurable (T n))
    (hW : ∀ n i, Measurable (fun a => S.Z (J n a i) a))
    (hind : ∀ n i, IndepFun (T n) (fun a => S.Z (J n a i) a) μ)
    (hlaw : ∀ n i, μ.map (fun a => S.Z (J n a i) a) = observationLaw M)
    (score : ℕ → A → Obs X Z → ℝ) (f : ℕ → D × Obs X Z → ℝ)
    (hscore : ∀ n a o, score (N n) a o = f n (T n a, o))
    (hf : ∀ n, Measurable (f n)) (truth : Obs X Z → ℝ) (hg : Measurable truth)
    (hfit : ∀ n i, MemLp
      (fun a => f n (T n a, S.Z (J n a i) a) - truth (S.Z (J n a i) a)) 2 μ)
    (hrate : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ o, (f n (T n a, o) - truth o) ^ 2 ∂observationLaw M)
      atTop (fun _ _ => 0))
    (theta sigmaSq : ℝ)
    (hV : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ((I₂ (N n) a).card : ℝ)⁻¹ *
        ∑ i ∈ I₂ (N n) a, (truth (S.Z i a) - theta) ^ 2)
      atTop (fun _ _ => sigmaSq))
    (hb : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => dmlRV M S I₂ score (N n) a - theta) atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => varianceRV M S I₂ score (N n) a) atTop
      (fun _ _ => sigmaSq) := by
  classical
  have hd : ∀ n, Measurable (fun tb : D × Obs X Z => f n tb - truth tb.2) := by
    intro n
    fun_prop
  have hE := dml_independent_empirical_score_energy_tendsto μ (observationLaw M) T
    (fun n i a => S.Z (J n a i) a) hT hW hind hlaw
    (fun n tb => f n tb - truth tb.2) hd hfit hrate
  have hI : ∀ n, ∀ᵐ a ∂μ, (I₂ (N n) a).Nonempty := by
    intro n
    filter_upwards [hrow n] with a ha
    rw [← ha.2]
    exact Finset.image_nonempty.mpr Finset.univ_nonempty
  apply varianceRV_consistent_of_empirical_score_error M S I₂ score truth N
    theta sigmaSq hI _ hV hb
  apply TendstoInMeasure.congr _ (Eventually.of_forall (fun _ => rfl)) hE
  intro n
  filter_upwards [hrow n] with a ha
  rw [← ha.2, Finset.card_image_of_injective _ ha.1, Finset.card_univ,
    Fintype.card_fin, Finset.sum_image]
  · simp only [hscore]
  · intro i hi j hj hij
    exact ha.1 hij

end Papers.TbsPrteOptimalTransport
