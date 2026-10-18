module
public import Papers.TbsExtremeEffects.Helpers.Hill.SpacingJacobian
public import Toolkit.Foundations.Probability.Distributions.ExponentialSpacings

/-! The factorial ordered density of an independent exponential sample. -/

@[expose] public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

/-- For [the input vector](hyp:x), [the descendingly sorted vector](goal) is the vector obtained by ordering its coordinates from largest to smallest. -/
-- @node: hillSortDescending
noncomputable def hillSortDescending {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  hillDecreasingOrder (fun j x => x j) x

/-- [The sorting map for vectors of length n](goal) is measurable. -/
@[fun_prop]
-- @node: hill_sort_descending_measurable
lemma hill_sort_descending_measurable (n : ℕ) :
    Measurable (hillSortDescending (n := n)) := by
  first | fun_prop | skip
  exact measurable_pi_lambda _
    (hill_decreasing_order_measurable (fun (j : Fin n) (x : Fin n → ℝ) => x j)
      (fun j => measurable_pi_apply j))

/-- [A permutation](hyp:σ) and [a vector whose permuted coordinates are already decreasing](hyp:h) imply [that sorting the vector returns precisely that permuted vector](goal). -/
-- @node: hill_sort_descending_chamber
lemma hill_sort_descending_chamber {n : ℕ} (σ : Equiv.Perm (Fin n))
    (x : Fin n → ℝ) (h : Antitone (x ∘ σ)) : hillSortDescending x = x ∘ σ := by
  have hm : Monotone (x ∘ (Fin.revPerm.trans σ)) := by
    intro i j hij
    exact h (Fin.rev_le_rev.mpr hij)
  have heq := (Tuple.comp_sort_eq_comp_iff_monotone
    (f := x) (σ := Fin.revPerm.trans σ)).mpr hm
  funext i
  have := congrFun heq i.rev
  simpa only [Function.comp_apply, Equiv.trans_apply, Fin.revPerm_apply,
    Fin.rev_rev, hillSortDescending, hillDecreasingOrder] using this.symm

/-- [Two distinct coordinates](hyp:hij) of [the given pair of indices](hyp:i,j) are equal only on [a set of zero Lebesgue volume](goal). -/
-- @node: hill_equal_coordinate_null
lemma hill_equal_coordinate_null {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    volume {x : Fin n → ℝ | x i = x j} = 0 := by
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ) - LinearMap.proj j
  have hL : L ≠ 0 := by
    intro h
    have h' := LinearMap.congr_fun h (fun k => if k = i then 1 else 0)
    simp [L, hij.symm] at h'
  have hker : LinearMap.ker L ≠ ⊤ := by
    intro h
    exact hL (LinearMap.ker_eq_top.mp h)
  have hs : {x : Fin n → ℝ | x i = x j} = (LinearMap.ker L : Set (Fin n → ℝ)) := by
    ext x
    simp [L, LinearMap.mem_ker, sub_eq_zero]
  rw [hs]
  exact Measure.addHaar_submodule volume (LinearMap.ker L) hker

/-- For [a permutation](hyp:σ), [the chamber of vectors whose permuted coordinates decrease](goal) is measurable. -/
-- @node: hill_chamber_measurable
lemma hill_chamber_measurable {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    MeasurableSet {x : Fin n → ℝ | Antitone (x ∘ σ)} := by
  exact (isClosed_antitone.preimage (by fun_prop :
    Continuous (fun x : Fin n → ℝ => x ∘ σ))).measurableSet

/-- For [a permutation](hyp:σ), [sorting Lebesgue measure restricted to its decreasing chamber](goal) gives Lebesgue measure restricted to the standard decreasing chamber. -/
-- @node: hill_chamber_sort_map
lemma hill_chamber_sort_map {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (volume.restrict {x : Fin n → ℝ | Antitone (x ∘ σ)}).map hillSortDescending =
      volume.restrict {y : Fin n → ℝ | Antitone y} := by
  let e : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ.symm
  have he : MeasurePreserving e volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) σ.symm
  have hfun : (e : (Fin n → ℝ) → (Fin n → ℝ)) = (fun x => x ∘ σ) := by
    funext x i
    simp [e, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  rw [Measure.map_congr (ae_restrict_of_forall_mem (hill_chamber_measurable σ)
    (fun x hx => hill_sort_descending_chamber σ x hx))]
  have hpre : e ⁻¹' {y | Antitone y} = {x | Antitone (x ∘ σ)} := by
    rw [hfun]
    rfl
  rw [← hpre, ← hfun, ← e.restrict_map volume {y | Antitone y}, he.map_eq]

/-- [Lebesgue measure on vectors of length n](goal) decomposes into the sum of its restrictions to all permutation-specific decreasing chambers. -/
-- @node: hill_chamber_decomposition
lemma hill_chamber_decomposition (n : ℕ) :
    (volume : Measure (Fin n → ℝ)) = ∑ σ : Equiv.Perm (Fin n),
      volume.restrict {x : Fin n → ℝ | Antitone (x ∘ σ)} := by
  let s (σ : Equiv.Perm (Fin n)) := {x : Fin n → ℝ | Antitone (x ∘ σ)}
  have hu : (⋃ σ, s σ) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨σ, hσ⟩ := (hill_decreasing_order_data (fun j x => x j)).2 x
    have ha := (hill_decreasing_order_data (fun j x => x j)).1 x
    refine mem_iUnion.mpr ⟨σ, ?_⟩
    intro i j hij
    simpa only [Function.comp_apply, ← hσ] using ha hij
  have hd : Pairwise (fun σ τ => AEDisjoint volume (s σ) (s τ)) := by
    intro σ τ hne
    obtain ⟨k, hk⟩ : ∃ k, σ k ≠ τ k := by
      by_contra h
      push_neg at h
      exact hne (Equiv.ext h)
    change volume (s σ ∩ s τ) = 0
    apply measure_mono_null (t := {x : Fin n → ℝ | x (σ k) = x (τ k)})
    · rintro x ⟨hxσ, hxτ⟩
      have hsame : x ∘ σ = x ∘ τ :=
        (hill_sort_descending_chamber σ x hxσ).symm.trans
          (hill_sort_descending_chamber τ x hxτ)
      exact congrFun hsame k
    · exact hill_equal_coordinate_null (σ k) (τ k) hk
  calc
    volume = volume.restrict (⋃ σ, s σ) := by rw [hu, Measure.restrict_univ]
    _ = Measure.sum (fun σ => volume.restrict (s σ)) :=
      Measure.restrict_iUnion_ae hd (fun σ => (hill_chamber_measurable σ).nullMeasurableSet)
    _ = ∑ σ, volume.restrict (s σ) := Measure.sum_fintype _

/-- [The image of Lebesgue measure under descending sorting](goal) is factorial times Lebesgue measure on decreasing vectors. -/
-- @node: hill_sort_descending_volume
lemma hill_sort_descending_volume (n : ℕ) :
    (volume : Measure (Fin n → ℝ)).map hillSortDescending =
      ENNReal.ofReal (n.factorial : ℝ) • volume.restrict {y : Fin n → ℝ | Antitone y} := by
  conv_lhs => rw [hill_chamber_decomposition n]
  rw [Measure.map_finset_sum (hill_sort_descending_measurable n).aemeasurable]
  simp only [hill_chamber_sort_map, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin]
  simp [Nat.cast_smul_eq_nsmul]

/-- For [an input vector](hyp:x), [the product of unit-exponential densities](goal) is unchanged when its coordinates are sorted in descending order. -/
-- @node: hill_sort_exponential_pdf_invariant
lemma hill_sort_exponential_pdf_invariant {n : ℕ} (x : Fin n → ℝ) :
    (∏ j, exponentialPDF 1 (hillSortDescending x j)) =
      ∏ j, exponentialPDF 1 (x j) := by
  obtain ⟨σ, hσ⟩ := (hill_decreasing_order_data (fun j x => x j)).2 x
  change (∏ j, exponentialPDF 1 (hillDecreasingOrder (fun j x => x j) x j)) = _
  simp_rw [hσ]
  exact Equiv.prod_comp σ (fun z => exponentialPDF 1 (x z))

/-- [The law of independent unit-exponential coordinates after descending sorting](goal) has the stated ordered exponential density. -/
-- @node: hill_sorted_exponential_density_law
lemma hill_sorted_exponential_density_law (n : ℕ) :
    (Measure.pi (fun _ : Fin n => expMeasure 1)).map hillSortDescending =
      volume.withDensity (hillOrderedExponentialDensity n) := by
  let f : (Fin n → ℝ) → ℝ≥0∞ := fun z => ∏ j, exponentialPDF 1 (z j)
  have hf : Measurable f := by
    first | fun_prop | skip
    exact Finset.measurable_prod _ (fun j _ =>
      (measurable_exponentialPDFReal 1).ennreal_ofReal.comp (measurable_pi_apply j))
  have hsym : f = fun x => f (hillSortDescending x) :=
    funext (fun x => (hill_sort_exponential_pdf_invariant x).symm)
  rw [← hill_exponential_product_density_law n]
  change (volume.withDensity f).map hillSortDescending = _
  conv_lhs => rw [hsym]
  rw [hill_map_density_comp volume _ f (hill_sort_descending_measurable n) hf,
    hill_sort_descending_volume, withDensity_smul_measure]
  have hset : MeasurableSet {y : Fin n → ℝ | Antitone y} := isClosed_antitone.measurableSet
  rw [← withDensity_smul _ hf, ← withDensity_indicator hset]
  congr 1
  funext y
  classical
  by_cases hy : Antitone y
  · by_cases hz : ∀ j, 0 ≤ y j
    all_goals simp [Set.indicator_apply, hillOrderedExponentialDensity, hy,
      f, hill_exponential_product_pdf, hz]
  · simp [Set.indicator_apply, hillOrderedExponentialDensity, hy]

/-- [Measurable coordinate variables](hyp:hV), [their mutual independence](hyp:hInd), and [their unit-exponential marginal laws](hyp:hLaw) imply [that their decreasing order statistics have the ordered-exponential density](goal). -/
-- @node: hill_independent_exponential_ordered_density
lemma hill_independent_exponential_ordered_density {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {n : ℕ} (V : Fin n → Ω → ℝ)
    (hV : ∀ j, Measurable (V j)) (hInd : iIndepFun V P)
    (hLaw : ∀ j, P.map (V j) = expMeasure 1) :
    P.map (hillDecreasingOrder V) = volume.withDensity (hillOrderedExponentialDensity n) := by
  have hJoint := hInd.map_fun_eq_pi_map (fun j => (hV j).aemeasurable)
  simp only [hLaw] at hJoint
  have hsort : hillDecreasingOrder V = hillSortDescending ∘ (fun w j => V j w) := rfl
  rw [hsort, ← Measure.map_map (hill_sort_descending_measurable n)
    (measurable_pi_lambda _ hV), hJoint]
  exact hill_sorted_exponential_density_law n

/-- [Measurable coordinate variables](hyp:hV), [their mutual independence](hyp:hInd), and [their unit-exponential marginal laws](hyp:hLaw) imply [that their ordered spacings are independent and each has the unit-exponential law](goal). -/
-- @node: hill_independent_exponential_spacing_law
lemma hill_independent_exponential_spacing_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (V : Fin n → Ω → ℝ)
    (hV : ∀ j, Measurable (V j)) (hInd : iIndepFun V P)
    (hLaw : ∀ j, P.map (V j) = expMeasure 1) :
    iIndepFun (hillOrderedSpacing V) P ∧
      ∀ j, P.map (hillOrderedSpacing V j) = expMeasure 1 :=
 by
  have hSpacing : hillOrderedSpacing V =
      Toolkit.Foundations.Probability.Distributions.normalizedSpacing V := by
    funext j w
    simp only [hillOrderedSpacing,
      Toolkit.Foundations.Probability.Distributions.normalizedSpacing,
      Toolkit.Foundations.Probability.Distributions.normalizedSpacingMap_apply,
      Nat.cast_add, Nat.cast_one]
    rfl
  rw [hSpacing]
  exact Toolkit.Foundations.Probability.Distributions.iIndepFun_normalizedSpacing_and_map_eq_expMeasure
    P V (by norm_num) hV hInd hLaw

end Papers.TbsExtremeEffects
