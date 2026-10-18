module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLCenteredBandConvergence
/-! Changing coefficients in treated-band scores.
The smooth coefficient error and moving-boundary error control the full
weighted discrepancy; conditional centering preserves this convergence. -/
public section

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

universe u v s
variable {Ω : Type u} {X Z : Type v} {A : Type s} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X] [BorelSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Z] [Nonempty X] [Nonempty Z]

-- @node: treatedLaw_bounded_multiplier_integrated_sq_le
/-- If [a covariate weight is measurable](hyp:hw), [a covariate-outcome multiplier is
measurable](hyp:hf) and [bounded in absolute value by one everywhere](hyp:hb), and
[the weight's square is integrable over covariates](hyp:hi), then [the product's
conditional squared energy is integrable, and its covariate average is bounded by
the covariate integral of the squared weight](goal). -/
lemma treatedLaw_bounded_multiplier_integrated_sq_le
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (k : ℕ)
    (w : X → ℝ) (f : X × ℝ → ℝ) (hw : Measurable w) (hf : Measurable f)
    (hb : ∀ x y, |f (x, y)| ≤ 1) (hi : Integrable (fun x => w x ^ 2) (xLaw M)) :
    Integrable (fun x => ∫ y, (w x * f (x, y)) ^ 2 ∂treatedLaw M L k x) (xLaw M) ∧
    (∫ x, ∫ y, (w x * f (x, y)) ^ 2 ∂treatedLaw M L k x ∂xLaw M) ≤
      ∫ x, w x ^ 2 ∂xLaw M := by
  have hbound (x : X) :
      (∫ y, (w x * f (x, y)) ^ 2 ∂treatedLaw M L k x) ≤ w x ^ 2 := by
    let := treatedLaw_isFiniteMeasure M L k x
    calc
      _ ≤ ∫ _ : ℝ, w x ^ 2 ∂treatedLaw M L k x := by
        apply integral_mono_of_nonneg (Eventually.of_forall fun y => sq_nonneg _)
          (integrable_const _)
        apply Eventually.of_forall
        intro y
        have hs : f (x, y) ^ 2 ≤ 1 := by
          simpa only [sq_abs, one_pow] using
            pow_le_pow_left₀ (abs_nonneg (f (x, y))) (hb x y) 2
        simpa only [mul_pow, mul_one] using
          mul_le_mul_of_nonneg_left hs (sq_nonneg (w x))
      _ = (treatedLaw M L k x).real univ * w x ^ 2 := by
        rw [integral_const, smul_eq_mul]
      _ ≤ w x ^ 2 := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (treatedLaw_mass_le_one M L k x) (sq_nonneg (w x))
  have hm : Measurable (fun x => ∫ y, (w x * f (x, y)) ^ 2
      ∂treatedLaw M L k x) := by
    apply measurable_treatedLaw_integral_prod M L k
      (fun p : X × ℝ => (w p.1 * f p) ^ 2)
    fun_prop
  have hi' := hi.mono' hm.aestronglyMeasurable (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y => sq_nonneg _)]
    exact hbound x)
  exact ⟨hi', integral_mono hi' hi hbound⟩

-- @node: treatedLaw_sum_integrated_sq_le
/-- For [a measurable first function](hyp:hf) and [a measurable second function](hyp:hg)
with [square-integrable treated-law sections for the first](hyp:hfm) and
[for the second](hyp:hgm), assume [the first conditional squared energy is integrable
over covariates](hyp:hfi) and [the second is as well](hyp:hgi).
[Their sum has integrable conditional squared energy, and its covariate average is
at most twice the sum of their separate integrated squared energies](goal). -/
lemma treatedLaw_sum_integrated_sq_le
    (M : LatentIVModel Ω X Z) (L : LevelData Z X) (k : ℕ)
    (f g : X × ℝ → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfm : ∀ x, MemLp (fun y => f (x, y)) 2 (treatedLaw M L k x))
    (hgm : ∀ x, MemLp (fun y => g (x, y)) 2 (treatedLaw M L k x))
    (hfi : Integrable (fun x => ∫ y, f (x, y) ^ 2 ∂treatedLaw M L k x) (xLaw M))
    (hgi : Integrable (fun x => ∫ y, g (x, y) ^ 2 ∂treatedLaw M L k x) (xLaw M)) :
    Integrable (fun x => ∫ y, (f (x, y) + g (x, y)) ^ 2
      ∂treatedLaw M L k x) (xLaw M) ∧
    (∫ x, ∫ y, (f (x, y) + g (x, y)) ^ 2 ∂treatedLaw M L k x ∂xLaw M) ≤
      2 * ((∫ x, ∫ y, f (x, y) ^ 2 ∂treatedLaw M L k x ∂xLaw M) +
        ∫ x, ∫ y, g (x, y) ^ 2 ∂treatedLaw M L k x ∂xLaw M) := by
  have hb x : (∫ y, (f (x, y) + g (x, y)) ^ 2 ∂treatedLaw M L k x) ≤
      2 * ((∫ y, f (x, y) ^ 2 ∂treatedLaw M L k x) +
        ∫ y, g (x, y) ^ 2 ∂treatedLaw M L k x) := by
    rw [← integral_add (hfm x).integrable_sq (hgm x).integrable_sq,
      ← integral_const_mul]
    apply integral_mono ((hfm x).add (hgm x)).integrable_sq
      (((hfm x).integrable_sq.add (hgm x).integrable_sq).const_mul 2)
    intro y
    change (f (x, y) + g (x, y)) ^ 2 ≤ 2 * (f (x, y) ^ 2 + g (x, y) ^ 2)
    nlinarith [sq_nonneg (f (x, y) - g (x, y))]
  have hm : Measurable (fun x => ∫ y, (f (x, y) + g (x, y)) ^ 2
      ∂treatedLaw M L k x) := by
    apply measurable_treatedLaw_integral_prod M L k
      (fun p : X × ℝ => (f p + g p) ^ 2)
    fun_prop
  have hi := ((hfi.add hgi).const_mul 2).mono' hm.aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y => sq_nonneg _)]
      exact hb x)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x, 2 * ((∫ y, f (x, y) ^ 2 ∂treatedLaw M L k x) +
        ∫ y, g (x, y) ^ 2 ∂treatedLaw M L k x) ∂xLaw M :=
      integral_mono hi ((hfi.add hgi).const_mul 2) hb
    _ = _ := by rw [integral_const_mul, integral_add hfi hgi]

-- @node: treatedLaw_centered_sum_sq_tendsto_probability_zero
/-- Suppose [the first sequence of functions is measurable](hyp:hf) and [the second
is measurable](hyp:hg), [the first has square-integrable treated-law sections](hyp:hfm)
and [so does the second](hyp:hgm), and [the first conditional squared energies are
integrable over covariates](hyp:hfi), [as are the second](hyp:hgi).
If [the first integrated squared energies vanish in probability](hyp:hrf) and
[the second integrated squared energies vanish in probability](hyp:hrg), then
[the sum, centered by its treated-law integral, has integrated squared energy
converging to zero in probability](goal). -/
lemma treatedLaw_centered_sum_sq_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X) (k : ℕ)
    (f g : ℕ → A → X × ℝ → ℝ)
    (hf : ∀ n a, Measurable (f n a)) (hg : ∀ n a, Measurable (g n a))
    (hfm : ∀ n a x, MemLp (fun y => f n a (x, y)) 2 (treatedLaw M L k x))
    (hgm : ∀ n a x, MemLp (fun y => g n a (x, y)) 2 (treatedLaw M L k x))
    (hfi : ∀ n a, Integrable (fun x => ∫ y, f n a (x, y) ^ 2
      ∂treatedLaw M L k x) (xLaw M))
    (hgi : ∀ n a, Integrable (fun x => ∫ y, g n a (x, y) ^ 2
      ∂treatedLaw M L k x) (xLaw M))
    (hrf : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, ∫ y, f n a (x, y) ^ 2 ∂treatedLaw M L k x ∂xLaw M)
      atTop (fun _ _ => 0))
    (hrg : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, ∫ y, g n a (x, y) ^ 2 ∂treatedLaw M L k x ∂xLaw M)
      atTop (fun _ _ => 0)) :
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n a => ∫ x, ∫ y,
        (f n a (x, y) + g n a (x, y) -
          ∫ z, f n a (x, z) + g n a (x, z) ∂treatedLaw M L k x) ^ 2
        ∂treatedLaw M L k x ∂xLaw M) atTop (fun _ _ => 0) := by
  have hn := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    (show Continuous (fun t : ℝ => -t) by fun_prop).continuousAt hrg
  simp only [neg_zero] at hn
  have hs := hrf.sub hn
  simp only [sub_zero, sub_neg_eq_add] at hs
  have ht := Causalean.Stat.Modes.TendstoInProbability.comp_continuousAt
    (show Continuous (fun t : ℝ => 2 * t) by fun_prop).continuousAt hs
  simp only [mul_zero] at ht
  apply treatedLaw_centered_sq_tendsto_probability_zero M μ L k
    (fun n a p => f n a p + g n a p) (fun n a => (hf n a).add (hg n a))
    (fun n a x => (hfm n a x).add (hgm n a x))
    (fun n a => (treatedLaw_sum_integrated_sq_le M L k _ _ (hf n a) (hg n a)
      (hfm n a) (hgm n a) (hfi n a) (hgi n a)).1)
  apply probability_zero_of_nonneg_le μ _ _ ht
  intro n
  apply Eventually.of_forall
  intro a
  exact ⟨integral_nonneg fun x => integral_nonneg fun y => sq_nonneg _,
    (treatedLaw_sum_integrated_sq_le M L k _ _ (hf n a) (hg n a)
      (hfm n a) (hgm n a) (hfi n a) (hgi n a)).2⟩

-- @node: treatedLaw_changing_weight_centered_band_sq_tendsto_probability_zero
/-- Suppose [the true lower endpoint is measurable](hyp:ha), [the true upper endpoint
is measurable](hyp:hb), [the true weight is measurable](hyp:hw0), [all fitted lower
endpoints are measurable](hyp:hah), [all fitted upper endpoints are measurable](hyp:hbh),
and [all fitted weights are measurable](hyp:hw). If [the fitted weights are uniformly
bounded almost everywhere over covariates](hyp:hwb), [weight errors are square
integrable](hyp:hwm), [lower-threshold indicator errors vanish in integrated square
in probability](hyp:hA), [upper-threshold indicator errors do likewise](hyp:hB), and
[weight errors vanish in covariate mean square in probability](hyp:hW), then
[the difference between fitted and true weighted band indicators, centered by its
treated-law integral, has integrated squared energy converging to zero in probability
along even sample sizes](goal). -/
lemma treatedLaw_changing_weight_centered_band_sq_tendsto_probability_zero
    (M : LatentIVModel Ω X Z) (μ : Measure A) (L : LevelData Z X) (k : ℕ)
    (a b w0 : X → ℝ) (ah bh w : ℕ → A → X → ℝ) (D : ℝ)
    (ha : Measurable a) (hb : Measurable b) (hw0 : Measurable w0)
    (hah : ∀ n s, Measurable (ah n s)) (hbh : ∀ n s, Measurable (bh n s))
    (hw : ∀ n s, Measurable (w n s))
    (hwb : ∀ n s, ∀ᵐ x ∂xLaw M, |w n s x| ≤ D)
    (hwm : ∀ n s, MemLp (fun x => w n s x - w0 x) 2 (xLaw M))
    (hA : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n s => ∫ x, ∫ y, (indicator (y ≤ ah (2*(n+1)) s x) -
        indicator (y ≤ a x)) ^ 2 ∂treatedLaw M L k x ∂xLaw M)
      atTop (fun _ _ => 0))
    (hB : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n s => ∫ x, ∫ y, (indicator (y ≤ bh (2*(n+1)) s x) -
        indicator (y ≤ b x)) ^ 2 ∂treatedLaw M L k x ∂xLaw M)
      atTop (fun _ _ => 0))
    (hW : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n s => ∫ x, (w (2*(n+1)) s x - w0 x) ^ 2 ∂xLaw M)
      atTop (fun _ _ => 0)) :
    let d : ℕ → A → X × ℝ → ℝ := fun n s p =>
      w (2*(n+1)) s p.1 * indicator (ah (2*(n+1)) s p.1 < p.2 ∧
        p.2 ≤ bh (2*(n+1)) s p.1) -
      w0 p.1 * indicator (a p.1 < p.2 ∧ p.2 ≤ b p.1)
    Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n s => ∫ x, ∫ y, (d n s (x, y) -
        ∫ z, d n s (x, z) ∂treatedLaw M L k x) ^ 2
        ∂treatedLaw M L k x ∂xLaw M) atTop (fun _ _ => 0) := by
  dsimp only
  let f : ℕ → A → X × ℝ → ℝ := fun n s p =>
    w (2*(n+1)) s p.1 * (indicator (ah (2*(n+1)) s p.1 < p.2 ∧
      p.2 ≤ bh (2*(n+1)) s p.1) - indicator (a p.1 < p.2 ∧ p.2 ≤ b p.1))
  let g : ℕ → A → X × ℝ → ℝ := fun n s p =>
    (w (2*(n+1)) s p.1 - w0 p.1) * indicator (a p.1 < p.2 ∧ p.2 ≤ b p.1)
  have hBand (c d : X → ℝ) (hc : Measurable c) (hd : Measurable d) :
      Measurable (fun p : X × ℝ => indicator (c p.1 < p.2 ∧ p.2 ≤ d p.1)) := by
    fun_prop
  have hf n s : Measurable (f n s) :=
    ((hw _ s).comp measurable_fst).mul
      ((hBand _ _ (hah _ s) (hbh _ s)).sub (hBand _ _ ha hb))
  have hg n s : Measurable (g n s) :=
    (((hw _ s).sub hw0).comp measurable_fst).mul (hBand _ _ ha hb)
  have hfm n s x : MemLp (fun y => f n s (x, y)) 2 (treatedLaw M L k x) := by
    let := treatedLaw_isFiniteMeasure M L k x
    apply MemLp.of_bound (by
      first | fun_prop | exact ((hf n s).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      |w (2*(n+1)) s x|
    apply Eventually.of_forall
    intro y
    dsimp only [f]
    unfold indicator
    split_ifs <;> simp [Real.norm_eq_abs]
  have hgm n s x : MemLp (fun y => g n s (x, y)) 2 (treatedLaw M L k x) := by
    let := treatedLaw_isFiniteMeasure M L k x
    apply MemLp.of_bound (by
      first | fun_prop | exact ((hg n s).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      |w (2*(n+1)) s x - w0 x|
    apply Eventually.of_forall
    intro y
    dsimp only [g]
    unfold indicator
    split_ifs <;> simp [Real.norm_eq_abs]
  have hgi n s := treatedLaw_bounded_multiplier_integrated_sq_le M L k
    (fun x => w (2*(n+1)) s x - w0 x)
    (fun p => indicator (a p.1 < p.2 ∧ p.2 ≤ b p.1))
    ((hw _ s).sub hw0) (hBand _ _ ha hb)
    (fun x y => by unfold indicator; split_ifs <;> norm_num)
    (hwm _ s).integrable_sq
  have hgr : Causalean.Stat.Modes.TendstoInProbability (fun _ => μ)
      (fun n s => ∫ x, ∫ y, g n s (x, y) ^ 2 ∂treatedLaw M L k x ∂xLaw M)
      atTop (fun _ _ => 0) := by
    apply probability_zero_of_nonneg_le μ _ _ hW
    intro n
    apply Eventually.of_forall
    intro s
    exact ⟨integral_nonneg fun x => integral_nonneg fun y => sq_nonneg _, (hgi n s).2⟩
  have hfr := treatedLaw_weighted_quantile_band_sq_tendsto_probability_zero M μ L k
    a b ah bh w D ha hb hah hbh hw hwb hA hB
  have hs := treatedLaw_centered_sum_sq_tendsto_probability_zero M μ L k f g hf hg hfm hgm
    (fun n s => (treatedLaw_weighted_quantile_band_integrated_sq_bound M L k
      a b (ah (2*(n+1)) s) (bh (2*(n+1)) s) (w (2*(n+1)) s) D
      ha hb (hah _ s) (hbh _ s) (hw _ s) (hwb _ s)).1)
    (fun n s => (hgi n s).1) hfr hgr
  have hid n s p : f n s p + g n s p =
      w (2*(n+1)) s p.1 * indicator (ah (2*(n+1)) s p.1 < p.2 ∧
        p.2 ≤ bh (2*(n+1)) s p.1) -
      w0 p.1 * indicator (a p.1 < p.2 ∧ p.2 ≤ b p.1) := by
    dsimp only [f, g]
    ring
  simpa only [hid] using hs

end Papers.TbsPrteOptimalTransport
