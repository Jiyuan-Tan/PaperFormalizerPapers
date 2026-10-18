module
public import Papers.TbsPrteOptimalTransport.Helpers.ConnectedIV
public import Causalean.Stat.SampleSplit.FiniteSelector
public import Causalean.Stat.EmpiricalProcess.CrossFitRate
public import Mathlib.MeasureTheory.Function.FactorsThrough
/-! Fixed-block moments and finite-label evaluation rates for sample splitting. -/
public section
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedFintypeInType false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

/-! Fixed label configurations reduce to two independent observation blocks.
These helpers implement the finite-configuration proof directive. -/

/-- If [the predictor is jointly measurable using only the training view and
the evaluation argument](hyp:hf), then [it can be represented exactly as a
jointly measurable function of that view and the evaluation argument](goal). -/
lemma measurable_training_predictor_factorization
    {A T B : Type*} [MeasurableSpace T] [MeasurableSpace B]
    (view : A → T) (f : A → B → ℝ)
    (hf : Measurable[(MeasurableSpace.comap view inferInstance).prod inferInstance]
      (Function.uncurry f)) :
    ∃ F : T → B → ℝ, Measurable (Function.uncurry F) ∧
      ∀ a b, f a b = F (view a) b := by
  have hcomap : Measurable[MeasurableSpace.comap (Prod.map view id) inferInstance]
      (Function.uncurry f) := by
    change Measurable[(MeasurableSpace.prod (inferInstance : MeasurableSpace T)
      (inferInstance : MeasurableSpace B)).comap (Prod.map view id)] (Function.uncurry f)
    rw [MeasurableSpace.comap_prodMap, MeasurableSpace.comap_id]
    exact hf
  obtain ⟨F, hF, heq⟩ := hcomap.exists_eq_measurable_comp
  refine ⟨Function.curry F, hF, ?_⟩
  intro a b
  exact congrFun heq (a, b)

/-- If [the predictor is jointly measurable using only the training view and
the evaluation argument](hyp:hf), [C is nonnegative](hyp:hC), and
[the predictor is everywhere bounded in absolute value by C](hyp:hb), then
[it has an exact jointly measurable representation through the training view
that is bounded in absolute value by C even at unrealized views](goal). -/
lemma bounded_training_predictor_factorization
    {A T B : Type*} [MeasurableSpace T] [MeasurableSpace B]
    (view : A → T) (f : A → B → ℝ)
    (hf : Measurable[(MeasurableSpace.comap view inferInstance).prod inferInstance]
      (Function.uncurry f)) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ a b, |f a b| ≤ C) :
    ∃ F : T → B → ℝ, Measurable (Function.uncurry F) ∧
      (∀ t b, |F t b| ≤ C) ∧ ∀ a b, f a b = F (view a) b := by
  obtain ⟨F, hF, heq⟩ := measurable_training_predictor_factorization view f hf
  refine ⟨fun t b => max (-C) (min C (F t b)), ?_, ?_, ?_⟩
  · fun_prop
  · intro t b
    apply abs_le.mpr
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  · intro a b
    dsimp only
    rw [← heq a b]
    have hab := abs_le.mp (hb a b)
    rw [min_eq_right hab.2, max_eq_right hab.1]

/-- Suppose [each observation is measurable](hyp:hW), [the observations are
mutually independent](hyp:hi), [each has distribution P](hyp:hLaw),
[the training and evaluation blocks are disjoint](hyp:hd), and
[the evaluation block is nonempty](hyp:he). If [the score is jointly measurable
in the training block and evaluation observation](hyp:hf), [C is nonnegative](hyp:hC),
and [the score is bounded in absolute value by C](hyp:hb), then
[the second moment of the sum of scores centered by their population means,
divided by the square root of the evaluation size, is at most C squared](goal). -/
lemma fixed_block_centered_second_moment
    {A E ι : Type*} [MeasurableSpace A] [MeasurableSpace E]
    {μ : Measure A} {P : Measure E} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (W : ι → A → E) (hW : ∀ i, Measurable (W i)) (hi : iIndepFun W μ)
    (hLaw : ∀ i, μ.map (W i) = P)
    (train eval : Finset ι) (hd : Disjoint train eval) (he : 0 < eval.card)
    (f : (train → E) → E → ℝ) (hf : Measurable (Function.uncurry f))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ t x, |f t x| ≤ C) :
    ∫⁻ a, ENNReal.ofReal
      (((Real.sqrt (eval.card : ℝ))⁻¹ * ∑ i ∈ eval,
        (f (fun j : train => W j a) (W i a) -
          ∫ x, f (fun j : train => W j a) x ∂P)) ^ 2) ∂μ ≤
      ENNReal.ofReal (C ^ 2) := by
  let T : A → (train → E) := fun a j => W j a
  have hT : Measurable T := by
    fun_prop
  have hTi : @Measurable A (train → E) (MeasurableSpace.comap T inferInstance) _ T := Measurable.of_comap_le le_rfl
  have hg : Measurable[(MeasurableSpace.comap T inferInstance).prod inferInstance]
      (Function.uncurry (fun a x => f (T a) x)) := by
    exact hf.comp (hTi.comp measurable_fst |>.prodMk measurable_snd)
  have hLp (a : A) : MemLp (f (T a)) 2 P := by
    have hm : Measurable (f (T a)) := hf.comp (measurable_const.prodMk measurable_id)
    exact MemLp.of_bound hm.aestronglyMeasurable C
      (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hb (T a) x))
  have hpi : μ.map (fun a (i : eval) => W i a) = Measure.pi (fun _ : eval => P) := by
    rw [(hi.restrict eval).map_fun_eq_pi_map (fun i : eval => (hW i).aemeasurable)]
    simp only [hLaw]
  have hmoment := Causalean.Mathlib.iid_centered_sum_sq_lintegral_le
    eval he W (fun i _ => hW i) (MeasurableSpace.comap T inferInstance) hT.comap_le
    (hi.indepFun_finset train eval hd hW) hpi
    (fun a x => f (T a) x) hg hLp
  refine hmoment.trans ?_
  calc
    ∫⁻ a, ENNReal.ofReal ((eLpNorm (f (T a)) 2 P).toReal ^ 2) ∂μ
        ≤ ∫⁻ _a : A, ENNReal.ofReal (C ^ 2) ∂μ := by
      apply lintegral_mono
      intro a
      dsimp only
      rw [Causalean.Mathlib.eLpNorm_two_sq_toReal_eq_integral_sq (hLp a)]
      apply ENNReal.ofReal_le_ofReal
      calc
        ∫ x, ‖f (T a) x‖ ^ 2 ∂P ≤ ∫ _x : E, C ^ 2 ∂P := by
          apply integral_mono (by simpa only [Real.norm_eq_abs, sq_abs] using (hLp a).integrable_sq)
            (integrable_const _)
          intro x
          exact pow_le_pow_left₀ (norm_nonneg _) (by
            simpa only [Real.norm_eq_abs] using hb (T a) x) 2
        _ = C ^ 2 := by simp
    _ = ENNReal.ofReal (C ^ 2) := by simp

/-- Suppose [the finite split label is measurable](hyp:hl) and
[independent of the first n observations](hyp:hind), [each label's score is
jointly measurable in its training block and evaluation observation](hyp:hf),
[C is nonnegative](hyp:hC), and [all scores are bounded in absolute value by C](hyp:hb).
If [the set of good labels is measurable](hyp:hgood), [training and evaluation
blocks are disjoint on good labels](hyp:hd), and [evaluation blocks are nonempty
on good labels](hyp:he), then [on the good-label event the squared centered score
sum divided by evaluation size is integrable, and its integral over that event
is at most C squared](goal). -/
lemma random_labeled_split_centered_second_moment_integrable
    {A E L : Type*} [MeasurableSpace A] [MeasurableSpace E]
    [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L]
    {μ : Measure A} {P : Measure E} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (S : Causalean.Stat.IIDSample A E μ P) (n : ℕ)
    (label : A → L) (hl : Measurable label)
    (hind : IndepFun label (fun a (i : Fin n) => S.Z i a) μ)
    (train eval : L → Finset (Fin n))
    (f : (l : L) → (train l → E) → E → ℝ)
    (hf : ∀ l, Measurable (Function.uncurry (f l)))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ l t x, |f l t x| ≤ C)
    (good : Set L) (hgood : MeasurableSet good)
    (hd : ∀ l ∈ good, Disjoint (train l) (eval l))
    (he : ∀ l ∈ good, 0 < (eval l).card) :
    IntegrableOn (fun a =>
      (((Real.sqrt ((eval (label a)).card : ℝ))⁻¹ *
        ∑ i ∈ eval (label a),
          (f (label a) (fun j : train (label a) => S.Z j.val a) (S.Z i.val a) -
            ∫ x, f (label a) (fun j : train (label a) => S.Z j.val a) x ∂P)) ^ 2))
      (label ⁻¹' good) μ ∧
    ∫ a in label ⁻¹' good,
      (((Real.sqrt ((eval (label a)).card : ℝ))⁻¹ *
        ∑ i ∈ eval (label a),
          (f (label a) (fun j : train (label a) => S.Z j.val a) (S.Z i.val a) -
            ∫ x, f (label a) (fun j : train (label a) => S.Z j.val a) x ∂P)) ^ 2) ∂μ ≤
      C ^ 2 := by
  let V : A → (Fin n → E) := fun a i => S.Z i a
  let R := Measure.pi (fun _ : Fin n => P)
  let err : L → (Fin n → E) → ℝ := fun l u =>
    (Real.sqrt ((eval l).card : ℝ))⁻¹ * ∑ i ∈ eval l,
      (f l (fun j : train l => u j) (u i) -
        ∫ x, f l (fun j : train l => u j) x ∂P)
  have hV : Measurable V := by
    fun_prop
  have hVL : μ.map V = R := by
    rw [(S.indep.precomp Fin.val_injective).map_fun_eq_pi_map
      (fun i : Fin n => (S.meas i).aemeasurable)]
    simp only [S.map_eq]
    rfl
  have herr (l : L) : Measurable (err l) := by
    have hT : Measurable (fun u : Fin n → E => fun j : train l => u j) := by fun_prop
    have hmean : Measurable (fun t : train l → E => ∫ x, f l t x ∂P) := by
      first | fun_prop | exact (hf l).stronglyMeasurable.integral_prod_right.measurable
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i hi
    exact ((hf l).comp (hT.prodMk (measurable_pi_apply i))).sub (hmean.comp hT)
  have hbranch (l : L) (hg : l ∈ good) :
      ∫⁻ u, ENNReal.ofReal ((err l u) ^ 2) ∂R ≤ ENNReal.ofReal (C ^ 2) := by
    exact fixed_block_centered_second_moment
      (fun i (u : Fin n → E) => u i) (fun i => measurable_pi_apply i)
      (iIndepFun_pi (fun _ => aemeasurable_id))
      (fun i => (measurePreserving_eval (fun _ : Fin n => P) i).map_eq)
      (train l) (eval l) (hd l hg) (he l hg) (f l) (hf l) C hC (hb l)
  have hInt (l : L) (hg : l ∈ good) : Integrable (fun u => (err l u) ^ 2) R := by
    refine ⟨((herr l).pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun u => sq_nonneg (err l u)))]
    exact (hbranch l hg).trans_lt ENNReal.ofReal_lt_top
  have hreal (l : L) (hg : l ∈ good) : ∫ u, (err l u) ^ 2 ∂R ≤ C ^ 2 := by
    apply (ENNReal.ofReal_le_ofReal_iff (sq_nonneg C)).mp
    rw [ofReal_integral_eq_lintegral_ofReal (hInt l hg)
      (ae_of_all _ (fun u => sq_nonneg (err l u)))]
    exact hbranch l hg
  have hselected := Causalean.Stat.IndepFun.integral_finiteSelector_sq_le
    (select := id) (err := err) (Eligible := fun l => l ∈ good)
    hind hl hV measurable_id hgood (sq_nonneg C) (fun l hg => hg)
    (fun l hg => by rw [hVL]; exact hInt l hg)
    (fun l hg => by rw [hVL]; exact hreal l hg)
  have hselectedInt := Causalean.Stat.integrableOn_finiteSelector_sq_of_eligible
    (select := id) (err := err) (Eligible := fun l => l ∈ good)
    hl hV measurable_id hgood (fun l hg => hg)
    (fun l hg => by rw [hVL]; exact hInt l hg)
  exact ⟨hselectedInt, hselected⟩

/-- Suppose [the finite split label is measurable](hyp:hl) and
[independent of the first n observations](hyp:hind), [each label's score is
jointly measurable in training data and the evaluation observation](hyp:hf),
[C is nonnegative](hyp:hC), and [all scores are bounded in absolute value by C](hyp:hb).
If [the good-label set is measurable](hyp:hgood), [training and evaluation blocks
are disjoint on good labels](hyp:hd), [evaluation blocks there are nonempty](hyp:he),
[m is positive](hyp:hm), [every good evaluation block has at least m observations](hyp:hsize),
and [t is positive](hyp:ht), then [the probability of a good label and an absolute
centered evaluation average at least t is at most C squared divided by m times
t squared](goal). -/
lemma random_labeled_split_average_tail
    {A E L : Type*} [MeasurableSpace A] [MeasurableSpace E]
    [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L]
    {μ : Measure A} {P : Measure E} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (S : Causalean.Stat.IIDSample A E μ P) (n : ℕ)
    (label : A → L) (hl : Measurable label)
    (hind : IndepFun label (fun a (i : Fin n) => S.Z i a) μ)
    (train eval : L → Finset (Fin n))
    (f : (l : L) → (train l → E) → E → ℝ)
    (hf : ∀ l, Measurable (Function.uncurry (f l)))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ l t x, |f l t x| ≤ C)
    (good : Set L) (hgood : MeasurableSet good)
    (hd : ∀ l ∈ good, Disjoint (train l) (eval l))
    (he : ∀ l ∈ good, 0 < (eval l).card)
    (m : ℝ) (hm : 0 < m) (hsize : ∀ l ∈ good, m ≤ ((eval l).card : ℝ))
    (t : ℝ) (ht : 0 < t) :
    μ {a | label a ∈ good ∧ t ≤
      |((eval (label a)).card : ℝ)⁻¹ * ∑ i ∈ eval (label a),
        (f (label a) (fun j : train (label a) => S.Z j.val a) (S.Z i.val a) -
          ∫ x, f (label a) (fun j : train (label a) => S.Z j.val a) x ∂P)|} ≤
      ENNReal.ofReal (C ^ 2) / ENNReal.ofReal (m * t ^ 2) := by
  let sumErr : A → ℝ := fun a => ∑ i ∈ eval (label a),
    (f (label a) (fun j : train (label a) => S.Z j.val a) (S.Z i.val a) -
      ∫ x, f (label a) (fun j : train (label a) => S.Z j.val a) x ∂P)
  let N : A → ℝ := fun a => ((eval (label a)).card : ℝ)
  let H : A → ℝ := fun a => ((Real.sqrt (N a))⁻¹ * sumErr a) ^ 2
  let G := label ⁻¹' good
  have hG : MeasurableSet G := hl hgood
  have hmoment := random_labeled_split_centered_second_moment_integrable S n
    label hl hind train eval f hf C hC hb good hgood hd he
  have hInt : Integrable H (μ.restrict G) := hmoment.1
  have hbound : ∫⁻ a, ENNReal.ofReal (H a) ∂(μ.restrict G) ≤
      ENNReal.ofReal (C ^ 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hInt
      (ae_of_all _ (fun a => sq_nonneg _))]
    exact ENNReal.ofReal_le_ofReal hmoment.2
  have hpos : 0 < m * t ^ 2 := mul_pos hm (sq_pos_of_pos ht)
  have hmarkov := meas_ge_le_lintegral_div hInt.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (ENNReal.ofReal_ne_zero_iff.mpr hpos) ENNReal.ofReal_ne_top
  have hsubset :
      {a | label a ∈ good ∧ t ≤ |(N a)⁻¹ * sumErr a|} ⊆
      {a | ENNReal.ofReal (m * t ^ 2) ≤ ENNReal.ofReal (H a)} ∩ G := by
    intro a ha
    have hn : 0 < N a := hm.trans_le (hsize (label a) ha.1)
    have hs : (Real.sqrt (N a)) ^ 2 = N a := Real.sq_sqrt hn.le
    have hs0 : Real.sqrt (N a) ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
    have hidentity : H a = N a * ((N a)⁻¹ * sumErr a) ^ 2 := by
      dsimp only [H]
      rw [mul_pow, inv_pow, hs, mul_pow]
      field_simp
    have ht2 : t ^ 2 ≤ ((N a)⁻¹ * sumErr a) ^ 2 := by
      nlinarith [ha.2, sq_abs ((N a)⁻¹ * sumErr a), abs_nonneg ((N a)⁻¹ * sumErr a)]
    refine ⟨ENNReal.ofReal_le_ofReal ?_, ha.1⟩
    rw [hidentity]
    exact (mul_le_mul_of_nonneg_left ht2 hm.le).trans
      (mul_le_mul_of_nonneg_right (hsize (label a) ha.1) (sq_nonneg _))
  calc
    _ ≤ μ ({a | ENNReal.ofReal (m * t ^ 2) ≤ ENNReal.ofReal (H a)} ∩ G) :=
      measure_mono hsubset
    _ = (μ.restrict G) {a | ENNReal.ofReal (m * t ^ 2) ≤ ENNReal.ofReal (H a)} :=
      (Measure.restrict_apply' hG).symm
    _ ≤ (∫⁻ a, ENNReal.ofReal (H a) ∂(μ.restrict G)) /
        ENNReal.ofReal (m * t ^ 2) := hmarkov
    _ ≤ _ := by gcongr

/-- For [sample-size-dependent split labels](hyp:label) that are
[measurable](hyp:hl) and [independent of the observed sample](hyp:hind),
[label-dependent training and evaluation blocks](hyp:train,eval), and
[scores depending on the label, training observations, and evaluation argument](hyp:f),
suppose [each score is jointly measurable](hyp:hf), [C is nonnegative](hyp:hC),
and [all scores are bounded in absolute value by C](hyp:hb). Given
[sets of good labels](hyp:good) that are [measurable](hyp:hgood), with
[disjoint training and evaluation blocks](hyp:hd) and [nonempty evaluation blocks](hyp:he),
if [c is positive](hyp:hc), [good evaluation blocks have size at least c times
the sample size](hyp:hsize), and [the probability of a bad label tends to zero](hyp:hbad),
then [the evaluation average centered by the training-dependent population mean
is of order the inverse square root of sample size in probability](goal). -/
lemma random_labeled_split_average_isBigOp
    {A E : Type*} [MeasurableSpace A] [MeasurableSpace E]
    {μ : Measure A} {P : Measure E} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (S : Causalean.Stat.IIDSample A E μ P)
    (L : ℕ → Type*) [∀ n, Fintype (L n)] [∀ n, MeasurableSpace (L n)]
    [∀ n, MeasurableSingletonClass (L n)]
    (label : ∀ n, A → L n) (hl : ∀ n, Measurable (label n))
    (hind : ∀ n, IndepFun (label n) (fun a (i : Fin n) => S.Z i a) μ)
    (train eval : ∀ n, L n → Finset (Fin n))
    (f : ∀ n (l : L n), (train n l → E) → E → ℝ)
    (hf : ∀ n l, Measurable (Function.uncurry (f n l)))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n l t x, |f n l t x| ≤ C)
    (good : ∀ n, Set (L n)) (hgood : ∀ n, MeasurableSet (good n))
    (hd : ∀ n l, l ∈ good n → Disjoint (train n l) (eval n l))
    (he : ∀ n l, l ∈ good n → 0 < (eval n l).card)
    (c : ℝ) (hc : 0 < c)
    (hsize : ∀ n l, l ∈ good n → c * n ≤ ((eval n l).card : ℝ))
    (hbad : Tendsto (fun n => μ {a | label n a ∉ good n}) atTop (𝓝 0)) :
    Causalean.Stat.IsBigOp
      (fun n a => ((eval n (label n a)).card : ℝ)⁻¹ *
        ∑ i ∈ eval n (label n a),
          (f n (label n a) (fun j : train n (label n a) => S.Z j.val a) (S.Z i.val a) -
            ∫ x, f n (label n a) (fun j : train n (label n a) => S.Z j.val a) x ∂P))
      (fun n => (n : ℝ)^(-1/2 : ℝ)) μ := by
  intro δ hδ
  by_cases htop : δ = ⊤
  · exact ⟨1, one_pos, Eventually.of_forall (fun n => by simp [htop])⟩
  have hhalf : 0 < δ / 2 := ENNReal.div_pos hδ.ne' (by norm_num)
  have hhalfTop : δ / 2 ≠ ⊤ := ENNReal.div_ne_top htop (by norm_num)
  let ε := (δ / 2).toReal
  have hε : 0 < ε := ENNReal.toReal_pos hhalf.ne' hhalfTop
  let K := Real.sqrt (C ^ 2 / (c * ε) + 1)
  have hK : 0 < K := Real.sqrt_pos.mpr (by positivity)
  have hKs : K ^ 2 = C ^ 2 / (c * ε) + 1 := Real.sq_sqrt (by positivity)
  have hquant : C ^ 2 / (c * K ^ 2) ≤ ε := by
    apply (div_le_iff₀ (mul_pos hc (sq_pos_of_pos hK))).mpr
    have hcancel : C ^ 2 / (c * ε) * (c * ε) = C ^ 2 :=
      div_mul_cancel₀ _ (mul_pos hc hε).ne'
    rw [hKs]
    nlinarith [mul_pos hc hε]
  have hbadSmall : ∀ᶠ n in atTop, μ {a | label n a ∉ good n} ≤ δ / 2 :=
    (hbad.eventually (eventually_lt_nhds hhalf)).mono (fun _ h => h.le)
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbadSmall, eventually_ge_atTop 1] with n hn hn1
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hr : (n : ℝ)^(-1/2 : ℝ) = (Real.sqrt (n : ℝ))⁻¹ := by
    rw [show (-1/2 : ℝ) = -(1/2 : ℝ) by norm_num,
      Real.rpow_neg hnpos.le, ← Real.sqrt_eq_rpow]
  have ht : 0 < K * (n : ℝ)^(-1/2 : ℝ) :=
    mul_pos hK (Real.rpow_pos_of_pos hnpos _)
  have hden : c * (n : ℝ) * (K * (n : ℝ)^(-1/2 : ℝ)) ^ 2 = c * K ^ 2 := by
    rw [hr, mul_pow, inv_pow, Real.sq_sqrt hnpos.le]
    field_simp
  have htail := random_labeled_split_average_tail S n (label n) (hl n) (hind n)
    (train n) (eval n) (f n) (hf n) C hC (hb n) (good n) (hgood n)
    (hd n) (he n) (c * n) (mul_pos hc hnpos) (hsize n)
    (K * (n : ℝ)^(-1/2 : ℝ)) ht
  rw [hden, ← ENNReal.ofReal_div_of_pos (mul_pos hc (sq_pos_of_pos hK))] at htail
  have htailSmall := htail.trans (ENNReal.ofReal_le_ofReal hquant)
  rw [show ENNReal.ofReal ε = δ / 2 from ENNReal.ofReal_toReal hhalfTop] at htailSmall
  let err : A → ℝ := fun a => ((eval n (label n a)).card : ℝ)⁻¹ *
    ∑ i ∈ eval n (label n a),
      (f n (label n a) (fun j : train n (label n a) => S.Z j.val a) (S.Z i.val a) -
        ∫ x, f n (label n a) (fun j : train n (label n a) => S.Z j.val a) x ∂P)
  change μ {a | K * (n : ℝ)^(-1/2 : ℝ) ≤ ‖err a‖} ≤ δ
  calc
    _ ≤ μ ({a | label n a ∈ good n ∧ K * (n : ℝ)^(-1/2 : ℝ) ≤ |err a|} ∪
        {a | label n a ∉ good n}) := by
      apply measure_mono
      intro a ha
      by_cases hg : label n a ∈ good n
      · exact Or.inl ⟨hg, by simpa only [Set.mem_setOf_eq, Real.norm_eq_abs] using ha⟩
      · exact Or.inr hg
    _ ≤ μ {a | label n a ∈ good n ∧ K * (n : ℝ)^(-1/2 : ℝ) ≤ |err a|} +
        μ {a | label n a ∉ good n} := measure_union_le _ _
    _ ≤ δ / 2 + δ / 2 := add_le_add htailSmall hn
    _ = δ := ENNReal.add_halves δ

end Papers.TbsPrteOptimalTransport
