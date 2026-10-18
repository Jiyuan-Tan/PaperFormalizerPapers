module
public import Papers.TbsNeuralCausalPi.Helpers.EmpiricalWassersteinSteps
public import Papers.TbsNeuralCausalPi.Setup.EmpiricalAdmissibility

/-! # Uniform empirical Wasserstein deviation -/
public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
open MeasureTheory
open scoped ENNReal NNReal
noncomputable section

/-- Assuming [the Anthony–Bartlett squared-loss concentration result](hyp:hgate),
let [G be nonempty](hyp:hne), [admit a Borel parametrization](hyp:hadmissible), and
[consist of measurable functions taking values between zero and one](hyp:hG).
If [the sample size is at least one](hyp:hm) and [the tolerance is
positive](hyp:heps) and [less than one](hyp:heps1), then [the probability that
some squared function has absolute population-to-sample error at least the
tolerance is bounded by four times the empirical average-L1 covering number at
radius eps/16 on twice the sample size, times exp(−eps² m/32)](goal). -/
-- @node: anthonyBartlett_squaredLoss_zero
lemma anthonyBartlett_squaredLoss_zero (hgate : AnthonyBartlettSquaredLoss)
    {X : Type} [MeasurableSpace X] [StandardBorelSpace X] (mu : ProbabilityMeasure X)
    (G : Set (X → ℝ)) (hne : G.Nonempty)
    (hadmissible : BorelParametrizedClass G)
    (hG : ∀ g ∈ G, Measurable g ∧ ∀ x, g x ∈ Set.Icc (0:ℝ) 1)
    (m : ℕ) (hm : 1 ≤ m) (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1) :
    (Measure.pi (fun _ : Fin m => (mu : Measure X)))
      {x : Fin m → X | ∃ g ∈ G, eps ≤
        |(∫ y, (g y)^2 ∂(mu : Measure X)) -
          (m : ℝ)⁻¹ * ∑ i, (g (x i))^2|} ≤
      4 * (N1avg (eps/16) G (2*m) (fun g hg => (hG g hg).2)).toENNReal *
        ENNReal.ofReal (Real.exp (-(eps^2*m)/32)) := by
  let embed : X → X × Set.Icc (0:ℝ) 1 := fun x => (x, ⟨0, by norm_num⟩)
  have hembed : Measurable embed := by fun_prop
  let P : ProbabilityMeasure (X × Set.Icc (0:ℝ) 1) := mu.map hembed.aemeasurable
  have hsource := hgate X inferInstance G hne hadmissible hG P m hm eps heps heps1
  change (Measure.pi (fun _ : Fin m => (P : Measure _)))
    {z : Fin m → X × Set.Icc (0:ℝ) 1 | ∃ g ∈ G,
      |(∫ xy : X × Set.Icc (0:ℝ) 1, (g xy.1 - xy.2.val)^2 ∂(P : Measure (X × Set.Icc (0:ℝ) 1))) -
        (m : ℝ)⁻¹ * ∑ i, (g (z i).1 - (z i).2.val)^2| ≥ eps} ≤ _ at hsource
  let sampleEmbed : (Fin m → X) → Fin m → X × Set.Icc (0:ℝ) 1 :=
    fun x i => embed (x i)
  have hsample : Measurable sampleEmbed := by fun_prop
  have hlaw : (Measure.pi (fun _ : Fin m => (mu : Measure X))).map sampleEmbed =
      Measure.pi (fun _ : Fin m => (P : Measure (X × Set.Icc (0:ℝ) 1))) := by
    exact Measure.pi_map_pi (fun _ => hembed.aemeasurable)
  have hloss (g : X → ℝ) (hg : g ∈ G) :
      (∫ xy : X × Set.Icc (0:ℝ) 1, (g xy.1 - xy.2.val)^2 ∂(P : Measure _)) =
        ∫ y, (g y)^2 ∂(mu : Measure X) := by
    change (∫ xy, (g xy.1 - xy.2.val)^2 ∂((mu : Measure X).map embed)) = _
    have hgmeas : Measurable g := (hG g hg).1
    rw [integral_map hembed.aemeasurable (by fun_prop)]
    simp only [embed, sub_zero]
  let E := {z : Fin m → X × Set.Icc (0:ℝ) 1 | ∃ g ∈ G, eps ≤
    |(∫ xy : X × Set.Icc (0:ℝ) 1, (g xy.1 - xy.2.val)^2 ∂(P : Measure _)) -
      (m : ℝ)⁻¹ * ∑ i, (g (z i).1 - (z i).2.val)^2|}
  have hevent : sampleEmbed ⁻¹' E = {x : Fin m → X | ∃ g ∈ G, eps ≤
      |(∫ y, (g y)^2 ∂(mu : Measure X)) - (m : ℝ)⁻¹ * ∑ i, (g (x i))^2|} := by
    ext x
    simp only [E, Set.mem_preimage, Set.mem_ofPred_eq, sampleEmbed, embed, sub_zero]
    exact exists_congr (fun g => and_congr_right (fun hg => by rw [hloss g hg]))
  -- `le_map_apply` applies to arbitrary events, including outer-probability events.
  calc
    _ = (Measure.pi (fun _ : Fin m => (mu : Measure X))) (sampleEmbed ⁻¹' E) :=
      congrArg _ hevent.symm
    _ ≤ ((Measure.pi (fun _ : Fin m => (mu : Measure X))).map sampleEmbed) E :=
      Measure.le_map_apply hsample.aemeasurable E
    _ ≤ _ := by rw [hlaw]; exact hsource

/-- If [the output bound K is positive](hyp:hK) and [the Anthony–Bartlett packing
result](hyp:hAnthonyBartlettPacking_of_gate) and [squared-loss concentration
result](hyp:hAnthonyBartlettSquaredLoss_of_gate) hold, then [there are positive
constants C and c, depending only on the output dimension and K, such that for
any standard Borel input law and Borel-parametrized class of measurable,
K-bounded maps with coordinate pseudo-dimension at most dF, the probability that
the largest empirical pushforward Wasserstein error exceeds delta plus eps is
at most exp(C ((1 + delta⁻ᵈ) log(2 + delta⁻¹) + dF log(2 + eps⁻¹)) − c n eps²),
for every positive sample size and positive delta and eps](goal). -/
-- @node: uniform_empirical_wasserstein_measurable_input
lemma uniform_empirical_wasserstein_measurable_input (d : ℕ) (K : ℝ) (hK : 0 < K)
    (hAnthonyBartlettPacking_of_gate : AnthonyBartlettPacking)
    (hAnthonyBartlettSquaredLoss_of_gate : AnthonyBartlettSquaredLoss) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (X : Type) [MeasurableSpace X] [StandardBorelSpace X] (mu : ProbabilityMeasure X) (F : Set (X → L1Vec d)) (dF : ℝ),
        CoordinatePseudoDimBound F dF → ClassUniformlyBounded F K →
        (∀ f ∈ F, Measurable f) → BorelParametrizedClass F →
        ∀ n : ℕ, 1 ≤ n → ∀ delta eps : ℝ, 0 < delta → 0 < eps →
          (Measure.pi (fun _ : Fin n => (mu : Measure _)))
            {x : Fin n → X | ENNReal.ofReal (delta+eps) <
              ⨆ f : F, wasserstein1 ((mu : Measure _).map f.val)
                ((empiricalMeasure x).map f.val)} ≤
            ENNReal.ofReal (Real.exp
              (C * (((1 + delta ^ (-(d : ℤ))) * Real.log (2 + delta⁻¹) +
                dF * Real.log (2+eps⁻¹))) - c * n * eps^2)) := by
  have hAnthonyBartlett_of_gate : AnthonyBartlettCoveringConcentration :=
    ⟨hAnthonyBartlettPacking_of_gate, hAnthonyBartlettSquaredLoss_of_gate⟩
  by_cases hd : d = 0
  · subst d
    refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
    intro X _ _ mu F dF hdim hbound hF hparam n hn delta eps hdelta heps
    rw [uniform_empirical_wasserstein_large_eps_event_empty mu hbound hF hn
      hdelta.le (by simpa using heps.le), measure_empty]
    exact zero_le
  have hd : 0 < d := Nat.pos_of_ne_zero hd
  have hR : 0 < (d : ℝ) * K := mul_pos (Nat.cast_pos.mpr hd) hK
  obtain ⟨C₀, c, hC₀, hc, hconstants⟩ := empirical_sqrt_cover_tail_constants d hR
  obtain ⟨C, hC, hrate⟩ :=
    uniform_empirical_wasserstein_rate_of_fixed_test_tail d hK.le hC₀.le
  refine ⟨C, c, hC, hc, ?_⟩
  intro X _ _ mu F dF hdim hbound hF hparam n hn delta eps hdelta heps
  by_cases hlarge : 2 * d * K ≤ eps
  · rw [uniform_empirical_wasserstein_large_eps_event_empty mu hbound hF hn hdelta.le hlarge,
      measure_empty]
    exact zero_le
  apply hrate X mu F hbound hF n hn
    (Measure.pi (fun _ : Fin n => (mu : Measure _))) delta eps dF c hdelta heps hdim.1
  intro h hh hzero
  by_cases hne : F.Nonempty
  · obtain ⟨g, hg, hgLip, hgzero, hgBound, heq, hclass⟩ :=
      exists_measurable_anchored_cube_test_representative hbound hh hzero
    let Z := ((fun f : X → L1Vec d => normalizedSqrtTest g (d*K) ∘ f) '' F)
    have hZ : ∀ z ∈ Z, Measurable z ∧ ∀ x, z x ∈ Set.Icc (0 : ℝ) 1 := by
      rintro z ⟨f, hf, rfl⟩
      refine ⟨?_, fun x => normalizedSqrtTest_mem_Icc hR (hgBound (f x))⟩
      have hfmeas := hF f hf
      fun_prop
    have heta : 0 < eps / (2 * (d*K)) := by positivity
    have heta1 : eps / (2 * (d*K)) < 1 := by
      apply (div_lt_one (by positivity : 0 < 2 * (d*K))).mpr
      nlinarith [lt_of_not_ge hlarge]
    have hconcentration :
        (Measure.pi (fun _ : Fin n => (mu : Measure X)))
          {x : Fin n → X | ∃ z ∈ Z, eps / (2*(d*K)) ≤
            |(∫ y, (z y)^2 ∂(mu : Measure _)) -
              (n : ℝ)⁻¹ * ∑ i, (z (x i))^2|} ≤
          4 * (N1avg ((eps / (2*(d*K)))/16) Z (2*n)
            (fun z hz => (hZ z hz).2)).toENNReal *
            ENNReal.ofReal (Real.exp (-((eps/(2*(d*K)))^2 * n)/32)) := by
      exact anthonyBartlett_squaredLoss_zero hAnthonyBartlettSquaredLoss_of_gate
        mu Z (hne.image _) (hparam.postcomp _ (by fun_prop)) hZ n hn _ heta heta1
    have hcover := anchored_cube_sqrt_entropy_le hAnthonyBartlett_of_gate hd hne hdim hbound
      (m := 2*n) (by omega) (div_pos heta (by norm_num : (0 : ℝ) < 16)) hgLip hgzero
    have hscale : 4 * Real.exp 1 / ((eps / (2 * (d*K))) / 16)^2 =
        1024 * Real.exp 1 / (eps / (2 * (d*K)))^2 := by
      field_simp
      ring
    rw [hscale] at hcover
    -- Use the same representative for both the event and its internal cover.
    have hsub : {x : Fin n → X | ∃ f ∈ F,
        ENNReal.ofReal eps < ENNReal.ofReal
          ((∫ y, h y ∂((mu : Measure _).map f)) -
            ∫ y, h y ∂((empiricalMeasure x).map f))} ⊆
        {x : Fin n → X | ∃ z ∈ Z, eps / (2*(d*K)) ≤
          |(∫ y, (z y)^2 ∂(mu : Measure _)) - (n : ℝ)⁻¹ * ∑ i, (z (x i))^2|} := by
      intro x hx
      apply pushforward_failure_subset_squared_loss mu hF hg hR heps.le
        (fun f hf y => hgBound (f y)) hn
      obtain ⟨f, hf, hbad⟩ := hx
      have hid (Q : Measure X) := pushforward_test_integral_congr_on Q (hF f hf)
        (boundedCube_isCompact d K).measurableSet
        (fun x j => (norm_le_pi_norm (f x).ofLp j).trans (hbound.2 f hf x)) heq
      exact ⟨f, hf, by rwa [hid (mu : Measure _), hid (empiricalMeasure x)]⟩
    calc
      _ ≤ _ := measure_mono hsub
      _ ≤ _ := hconcentration
      _ ≤ 4 * ENNReal.ofReal ((Real.exp 1 * (⌊dF⌋₊+1) *
          (2 + 1024 * Real.exp 1 / (eps/(2*(d*K)))^2)^⌊dF⌋₊)^d) *
          ENNReal.ofReal (Real.exp (-((eps/(2*(d*K)))^2 * n)/32)) := by
        gcongr
      _ ≤ _ := hconstants ⌊dF⌋₊ n dF eps (Nat.floor_le hdim.1) heps
  · have hFempty : F = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp only [hFempty, Set.mem_empty_iff_false, false_and, exists_false, Set.ofPred_false,
      measure_empty]
    exact zero_le

-- @node: lem:sup-wasserstein
/-- If [K is positive](hyp:hK) and [the Anthony–Bartlett packing
result](hyp:hAnthonyBartlettPacking_of_gate) and [squared-loss concentration
result](hyp:hAnthonyBartlettSquaredLoss_of_gate) hold, then [there are positive
constants C and c, depending only on the output dimension and K, such that for
every finite-dimensional input law and Borel-parametrized class of measurable,
K-bounded maps with coordinate pseudo-dimension at most dF, the completed IID
sample law assigns probability at most exp(C ((1 + delta⁻ᵈ) log(2 + delta⁻¹) +
dF log(2 + eps⁻¹)) − c n eps²) to the event that the largest empirical
pushforward Wasserstein error exceeds delta plus eps, for positive sample size,
delta, and eps](goal). -/
lemma uniform_empirical_wasserstein (d : ℕ) (K : ℝ) (hK : 0 < K)
    (hAnthonyBartlettPacking_of_gate : AnthonyBartlettPacking)
    (hAnthonyBartlettSquaredLoss_of_gate : AnthonyBartlettSquaredLoss) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (d' : ℕ) (mu : ProbabilityMeasure (L1Vec d')) (F : Set (L1Vec d' → L1Vec d)) (dF : ℝ),
        CoordinatePseudoDimBound F dF → ClassUniformlyBounded F K →
        (∀ f ∈ F, Measurable f) → BorelParametrizedClass F →
        ∀ n : ℕ, 1 ≤ n → ∀ delta eps : ℝ, 0 < delta → 0 < eps →
          (Measure.pi (fun _ : Fin n => (mu : Measure _))).completion
            {x : Fin n → L1Vec d' | ENNReal.ofReal (delta+eps) <
              ⨆ f : F, wasserstein1 ((mu : Measure _).map f.val)
                ((empiricalMeasure x).map f.val)} ≤
            ENNReal.ofReal (Real.exp
              (C * (((1 + delta ^ (-(d : ℤ))) * Real.log (2 + delta⁻¹) +
                dF * Real.log (2+eps⁻¹))) - c * n * eps^2)) := by
  obtain ⟨C, c, hC, hc, h⟩ :=
    uniform_empirical_wasserstein_measurable_input d K hK
      hAnthonyBartlettPacking_of_gate hAnthonyBartlettSquaredLoss_of_gate
  refine ⟨C, c, hC, hc, ?_⟩
  intro d' mu F dF hdim hbound hF hparam n hn delta eps hdelta heps
  change (Measure.pi (fun _ : Fin n => (mu : Measure _)))
    {x : Fin n → L1Vec d' | ENNReal.ofReal (delta+eps) <
      ⨆ f : F, wasserstein1 ((mu : Measure _).map f.val)
        ((empiricalMeasure x).map f.val)} ≤ _
  exact h (L1Vec d') mu F dF hdim hbound hF hparam n hn delta eps hdelta heps
end
end Papers.TbsNeuralCausalPi
