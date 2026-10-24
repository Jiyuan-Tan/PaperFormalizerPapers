module

public import Papers.OaiLinearVarianceRandom.Helpers.OrdinaryHiddenClauses

/-! # Conditional laws for whole hidden test families

The finite-fiber formula applies to arbitrary events of the clause vector,
including killing events which need not be coordinate rectangles.
-/

public section

namespace Papers.OaiLinearVarianceRandom
open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {n : ℕ} {Ω : Type} [MeasurableSpace Ω]

open Classical in
/-- For [a chosen event on each labeled family of finite coordinates](hyp:P),
[the fraction of full coordinate vectors satisfying every family event equals
the product of the corresponding fractions within the separate families](goal). -/
-- @node: finite_partition_event_fraction
lemma finite_partition_event_fraction
    {I R : Type*} [Fintype I] [Fintype R]
    (A : I → Type*) [∀ j, Fintype (A j)] (label : I → R)
    (P : ∀ r, (∀ j : {j // label j = r}, A j.val) → Prop) :
    (Fintype.card {v : ∀ j, A j //
      ∀ r, P r (fun j => v j.val)} : ℝ) / Fintype.card (∀ j, A j) =
      ∏ r, (Fintype.card {v : ∀ j : {j // label j = r}, A j.val // P r v} : ℝ) /
        Fintype.card (∀ j : {j // label j = r}, A j.val) := by
  classical
  let e : (∀ j, A j) ≃ (∀ r, ∀ j : {j // label j = r}, A j.val) :=
    { toFun := fun v r j => v j.val
      invFun := fun v j => v (label j) ⟨j, rfl⟩
      left_inv := fun _ => rfl
      right_inv := by
        intro v
        funext r j
        obtain ⟨j, hj⟩ := j
        subst r
        rfl }
  have hnum := Fintype.card_congr
    ((e.subtypeEquiv (p := fun v => ∀ r, P r (fun j => v j.val))
      (q := fun v => ∀ r, P r (v r)) (fun _ => Iff.rfl)).trans
        (Equiv.subtypePiEquivPi))
  have hden := Fintype.card_congr e
  rw [hnum, hden, Fintype.card_pi, Fintype.card_pi]
  simp only [Nat.cast_prod, Finset.prod_div_distrib]

open Classical in
/-- For [an event of a finite coordinate vector](hyp:P), [the fraction satisfying
the event among vectors whose coordinate observations match a reference vector
equals the fraction satisfying it in the product of the individual coordinate
observation fibers](goal). -/
-- @node: finite_coordinate_fiber_event_fraction
lemma finite_coordinate_fiber_event_fraction
    {I A E : Type*} [Fintype I] [Fintype A]
    (f : I → A → E) (a : I → A) (P : (I → A) → Prop) :
    (Fintype.card {v : I → A // (∀ j, f j (v j) = f j (a j)) ∧ P v} : ℝ) /
      Fintype.card {v : I → A // ∀ j, f j (v j) = f j (a j)} =
    (Fintype.card {v : ∀ j, {x : A // f j x = f j (a j)} //
      P (fun j => (v j).val)} : ℝ) /
      Fintype.card (∀ j, {x : A // f j x = f j (a j)}) := by
  classical
  have hnum := Fintype.card_congr
    (show {v : I → A // (∀ j, f j (v j) = f j (a j)) ∧ P v} ≃
      {v : ∀ j, {x : A // f j x = f j (a j)} // P (fun j => (v j).val)} from
      { toFun := fun v => ⟨fun j => ⟨v.val j, v.property.1 j⟩, v.property.2⟩
        invFun := fun v => ⟨fun j => (v.val j).val,
          ⟨fun j => (v.val j).property, v.property⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl })
  rw [hnum, Fintype.card_congr (Equiv.subtypePiEquivPi
    (p := fun j x => f j x = f j (a j)))]

open Classical in
/-- Given [an event for each labeled coordinate family](hyp:P), suppose
[membership in the joint event, together with matching the reference vector's
coordinate observations, implies every family event](hyp:h). Then [the fraction
of the observation fiber belonging to the joint event is at most the product
of the family event fractions in their respective coordinate fibers](goal). -/
-- @node: finite_coordinate_fiber_event_le_families
lemma finite_coordinate_fiber_event_le_families
    {I A E R : Type*} [Fintype I] [Fintype A] [Fintype R]
    (f : I → A → E) (a : I → A) (s : Set (I → A)) (label : I → R)
    (P : ∀ r, ({j // label j = r} → A) → Prop)
    (h : ∀ v : I → A, (∀ j, f j (v j) = f j (a j)) → v ∈ s →
      ∀ r, P r (fun j => v j.val)) :
    (Fintype.card {v : I → A // (∀ j, f j (v j) = f j (a j)) ∧ v ∈ s} : ℝ) /
      Fintype.card {v : I → A // ∀ j, f j (v j) = f j (a j)} ≤
      ∏ r, (Fintype.card {v : ∀ j : {j // label j = r},
        {x : A // f j.val x = f j.val (a j.val)} //
          P r (fun j => (v j).val)} : ℝ) /
        Fintype.card (∀ j : {j // label j = r},
          {x : A // f j.val x = f j.val (a j.val)}) := by
  classical
  have hcard := Fintype.card_subtype_mono
    (fun v : I → A => (∀ j, f j (v j) = f j (a j)) ∧ v ∈ s)
    (fun v : I → A => (∀ j, f j (v j) = f j (a j)) ∧
      ∀ r, P r (fun j => v j.val))
    (fun v hv => ⟨hv.1, h v hv.1 hv.2⟩)
  have hle := div_le_div_of_nonneg_right
    (show (Fintype.card {v : I → A //
      (∀ j, f j (v j) = f j (a j)) ∧ v ∈ s} : ℝ) ≤
      Fintype.card {v : I → A // (∀ j, f j (v j) = f j (a j)) ∧
        ∀ r, P r (fun j => v j.val)} from by exact_mod_cast hcard)
    (show (0 : ℝ) ≤ Fintype.card {v : I → A //
      ∀ j, f j (v j) = f j (a j)} from Nat.cast_nonneg _)
  have hfrac := finite_coordinate_fiber_event_fraction f a
    (fun v => ∀ r, P r (fun j => v j.val))
  have hprod := finite_partition_event_fraction
    (fun j => {x : A // f j x = f j (a j)}) label
    (fun r v => P r (fun j => (v j).val))
  simp only [← Nat.card_eq_fintype_card] at hle hfrac hprod ⊢
  exact hle.trans_eq (hfrac.trans hprod)

open Classical in
/-- Suppose [the clause sequence is an independent uniform clause
process](hyp:hlaw), [the fixed clause index is positive](hyp:hi), and [every
index in the finite observed set is positive and differs from the fixed
index](hyp:hT). Then [under the law fixing that clause to the reference clause,
the conditional probability of any event of the finite clause vector, given
its coordinate observations, almost surely equals the fraction of vectors
with matching observations that belong to the event](goal). -/
-- @node: fixedClauseMeasure_coarsened_event_mass
lemma fixedClauseMeasure_coarsened_event_mass
    {E : Type*} [Finite E] [MeasurableSpace E] [MeasurableSingletonClass E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Cseq : ℕ → Ω → ProperClause n)
    (hlaw : IsUniformClauseProcess μ Cseq) (i : ℕ) (hi : 1 ≤ i)
    (c0 : ProperClause n) (T : Finset ℕ)
    (hT : ∀ j ∈ T, 1 ≤ j ∧ j ≠ i)
    (f : T → ProperClause n → E) (s : Set (T → ProperClause n)) :
    (fixedClauseMeasure μ Cseq i c0)[
      eventIndicator {ω | (fun j : T => Cseq j ω) ∈ s} |
        MeasurableSpace.comap (fun ω j => f j (Cseq j ω)) inferInstance] =ᵐ[
          fixedClauseMeasure μ Cseq i c0]
      fun ω =>
        (Fintype.card {cs : T → ProperClause n //
          (∀ j, f j (cs j) = f j (Cseq j ω)) ∧ cs ∈ s} : ℝ) /
        Fintype.card {cs : T → ProperClause n //
          ∀ j, f j (cs j) = f j (Cseq j ω)} := by
  classical
  let ν := fixedClauseMeasure μ Cseq i c0
  let X : Ω → (T → ProperClause n) := fun ω j => Cseq j ω
  let F : (T → ProperClause n) → (T → E) := fun cs j => f j (cs j)
  have hX : Measurable X := by
    apply measurable_pi_lambda
    intro j
    exact hlaw.1 _ (hT _ j.property).1
  have hF : Measurable F := measurable_of_finite F
  have : IsProbabilityMeasure ν :=
    fixedClauseMeasure_isProbabilityMeasure μ Cseq hlaw i hi c0
  have hmap : ν.map X = uniformOn (Set.univ : Set (T → ProperClause n)) := by
    rw [fixedClauseMeasure_joint_map μ Cseq hlaw i hi c0 T hT]
    simpa only [uniformClauseMeasure, Set.pi_univ] using
      (uniformOn_pi (f := fun _ : T => (Set.univ : Set (ProperClause n)))).symm
  have hce := condExp_indicator_finite_comap ν (F ∘ X) (hF.comp hX)
    (X ⁻¹' s) (hX (Set.toFinite s).measurableSet)
  filter_upwards [hce] with ω hω
  change ν[eventIndicator (X ⁻¹' s) |
    MeasurableSpace.comap (F ∘ X) inferInstance] ω = _
  rw [show eventIndicator (X ⁻¹' s) =
      (X ⁻¹' s).indicator (fun _ => (1 : ℝ)) by
    ext ω'; simp [eventIndicator, Set.indicator_apply], hω]
  have hden : ν.real ((F ∘ X) ⁻¹' {F (X ω)}) =
      (uniformOn (Set.univ : Set (T → ProperClause n))).real
        {cs | F cs = F (X ω)} := by
    rw [← hmap, map_measureReal_apply hX (Set.toFinite _).measurableSet]
    rfl
  have hnum : ν.real (((F ∘ X) ⁻¹' {F (X ω)}) ∩ X ⁻¹' s) =
      (uniformOn (Set.univ : Set (T → ProperClause n))).real
        ({cs | F cs = F (X ω)} ∩ s) := by
    rw [← hmap, map_measureReal_apply hX (Set.toFinite _).measurableSet]
    rfl
  simp only [Function.comp_apply]
  rw [hden, hnum, uniform_fiber_ratio F (X ω) s]
  simp only [F, X, funext_iff]

open Classical in
/-- Suppose [the clause sequence is an independent uniform clause
process](hyp:hlaw), [the fixed clause index is positive](hyp:hi), and [every
index in the finite observed set is positive and differs from the fixed
index](hyp:hT). For [an event on each labeled family of clause
coordinates](hyp:P), [under the law fixing the designated clause to the
reference clause, the conditional probability that all family events hold,
given the coordinate observations, almost surely equals the product of their
uniform event fractions on the respective observation fibers](goal). -/
-- @node: fixedClauseMeasure_coarsened_family_mass
lemma fixedClauseMeasure_coarsened_family_mass
    {E R : Type*} [Finite E] [MeasurableSpace E] [MeasurableSingletonClass E]
    [Fintype R]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Cseq : ℕ → Ω → ProperClause n)
    (hlaw : IsUniformClauseProcess μ Cseq) (i : ℕ) (hi : 1 ≤ i)
    (c0 : ProperClause n) (T : Finset ℕ)
    (hT : ∀ j ∈ T, 1 ≤ j ∧ j ≠ i)
    (f : T → ProperClause n → E) (label : T → R)
    (P : ∀ r, ({j : T // label j = r} → ProperClause n) → Prop) :
    (fixedClauseMeasure μ Cseq i c0)[
      eventIndicator {ω | ∀ r, P r (fun j => Cseq j.val ω)} |
        MeasurableSpace.comap (fun ω j => f j (Cseq j ω)) inferInstance] =ᵐ[
          fixedClauseMeasure μ Cseq i c0]
      fun ω => ∏ r,
        (Fintype.card {cs : ∀ j : {j : T // label j = r},
          {c : ProperClause n // f j.val c = f j.val (Cseq j.val ω)} //
            P r (fun j => (cs j).val)} : ℝ) /
        Fintype.card (∀ j : {j : T // label j = r},
          {c : ProperClause n // f j.val c = f j.val (Cseq j.val ω)}) := by
  classical
  have h := fixedClauseMeasure_coarsened_event_mass μ Cseq hlaw i hi c0 T hT f
    {cs | ∀ r, P r (fun j => cs j.val)}
  filter_upwards [h] with ω hω
  rw [hω]
  have hfrac := finite_coordinate_fiber_event_fraction f (fun j : T => Cseq j ω)
    (fun cs => ∀ r, P r (fun j => cs j.val))
  have hprod := finite_partition_event_fraction
    (fun j : T => {c : ProperClause n // f j c = f j (Cseq j ω)}) label
    (fun r cs => P r (fun j => (cs j).val))
  simp only [← Nat.card_eq_fintype_card] at hfrac hprod ⊢
  exact hfrac.trans hprod

open Classical in
/-- Suppose [the clause sequence is an independent uniform clause
process](hyp:hlaw), [the fixed clause index is positive](hyp:hi), and [every
index in the finite observed set is positive and differs from the fixed
index](hyp:hT). Then [under the law fixing that clause to the reference clause,
the conditional probability of an event depending on both the observations
and the clause vector, given the observations, almost surely equals the
fraction of vectors in the observation fiber satisfying the event with the
observed information held fixed](goal). -/
-- @node: fixedClauseMeasure_coarsened_dependent_event_mass
lemma fixedClauseMeasure_coarsened_dependent_event_mass
    {E : Type*} [Finite E] [MeasurableSpace E] [MeasurableSingletonClass E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Cseq : ℕ → Ω → ProperClause n)
    (hlaw : IsUniformClauseProcess μ Cseq) (i : ℕ) (hi : 1 ≤ i)
    (c0 : ProperClause n) (T : Finset ℕ)
    (hT : ∀ j ∈ T, 1 ≤ j ∧ j ≠ i)
    (f : T → ProperClause n → E)
    (g : (T → E) → (T → ProperClause n) → Prop) :
    (fixedClauseMeasure μ Cseq i c0)[
      eventIndicator {ω | g (fun j : T => f j (Cseq j ω))
        (fun j : T => Cseq j ω)} |
        MeasurableSpace.comap (fun ω j => f j (Cseq j ω)) inferInstance] =ᵐ[
          fixedClauseMeasure μ Cseq i c0]
      fun ω =>
        (Fintype.card {cs : T → ProperClause n //
          (∀ j, f j (cs j) = f j (Cseq j ω)) ∧
            g (fun j : T => f j (Cseq j ω)) cs} : ℝ) /
        Fintype.card {cs : T → ProperClause n //
          ∀ j, f j (cs j) = f j (Cseq j ω)} := by
  classical
  have h := fixedClauseMeasure_coarsened_event_mass μ Cseq hlaw i hi c0 T hT f
    {cs | g (fun j => f j (cs j)) cs}
  filter_upwards [h] with ω hω
  rw [hω]
  congr 2
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro cs
  constructor
  · rintro ⟨he, hg⟩
    exact ⟨he, (congrArg (fun e => g e cs) (funext he)) ▸ hg⟩
  · rintro ⟨he, hg⟩
    exact ⟨he, (congrArg (fun e => g e cs) (funext he)).symm ▸ hg⟩

open Classical in
/-- Suppose [the clause sequence is an independent uniform clause
process](hyp:hlaw), [the fixed clause index is positive](hyp:hi), and [the
prefix length does not exceed the cap](hyp:hm). Then [under the law fixing the
designated clause to the reference clause, almost every realization
simultaneously has the following property for every event of the capped clause
vector excluding the fixed index: its conditional probability given the
ordinary information equals the fraction of vectors with matching ordinary
prefix observations that belong to the event](goal). -/
-- @node: ordinary_hidden_clause_event_law
lemma ordinary_hidden_clause_event_law
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Cseq : ℕ → Ω → ProperClause n)
    (hlaw : IsUniformClauseProcess μ Cseq) (i : ℕ) (hi : 1 ≤ i)
    (c0 : ProperClause n) (m : ℕ) (hm : m ≤ capL n) :
    ∀ᵐ ω ∂(fixedClauseMeasure μ Cseq i c0),
      ∀ s : Set (((Finset.Icc 1 (capL n)).erase i) → ProperClause n),
      ((fixedClauseMeasure μ Cseq i c0)[
        eventIndicator {ω' | (fun j : ((Finset.Icc 1 (capL n)).erase i) =>
          Cseq j ω') ∈ s} | ordinaryFiltration c0 Cseq i m]) ω =
        (Fintype.card {cs : ((Finset.Icc 1 (capL n)).erase i) → ProperClause n //
          (∀ j : ((Finset.Icc 1 (capL n)).erase i), ordinaryPrefixExposure c0 m j (cs j) =
            ordinaryPrefixExposure c0 m j (Cseq j ω)) ∧ cs ∈ s} : ℝ) /
        Fintype.card {cs : ((Finset.Icc 1 (capL n)).erase i) → ProperClause n //
          ∀ j : ((Finset.Icc 1 (capL n)).erase i), ordinaryPrefixExposure c0 m j (cs j) =
            ordinaryPrefixExposure c0 m j (Cseq j ω)} := by
  classical
  let : MeasurableSpace (Finset (Fin n × Bool) × Option (ProperClause n)) := ⊤
  let : MeasurableSpace (Option (ProperClause n)) := ⊤
  apply ae_all_iff.mpr
  intro s
  rw [ordinaryFiltration_eq_comap_prefix c0 Cseq i m hm]
  exact fixedClauseMeasure_coarsened_event_mass μ Cseq hlaw i hi c0 _
    (fun j hj => ⟨(Finset.mem_Icc.mp (Finset.mem_erase.mp hj).2).1,
      (Finset.mem_erase.mp hj).1⟩)
    (fun j => ordinaryPrefixExposure c0 m j) s

open Classical in
/-- Suppose [the clause sequence is an independent uniform clause
process](hyp:hlaw), [the fixed clause index is positive](hyp:hi), and [the
prefix length does not exceed the cap](hyp:hm). Then [under the law fixing the
designated clause to the reference clause, almost every realization has this
property for every joint event, labeling of the capped coordinates excluding
the fixed index, and choice of family events: if the joint event implies all
family events throughout the current ordinary observation fiber, its
conditional probability given the ordinary information is at most the product
of the uniform family event fractions on their observation fibers](goal). -/
-- @node: ordinary_hidden_clause_event_le_families
lemma ordinary_hidden_clause_event_le_families
    {R : Type*} [Fintype R]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Cseq : ℕ → Ω → ProperClause n)
    (hlaw : IsUniformClauseProcess μ Cseq) (i : ℕ) (hi : 1 ≤ i)
    (c0 : ProperClause n) (m : ℕ) (hm : m ≤ capL n) :
    ∀ᵐ ω ∂(fixedClauseMeasure μ Cseq i c0),
      ∀ (s : Set (((Finset.Icc 1 (capL n)).erase i) → ProperClause n))
        (label : ((Finset.Icc 1 (capL n)).erase i) → R)
        (P : ∀ r, ({j // label j = r} → ProperClause n) → Prop),
      (∀ cs, (∀ j : ((Finset.Icc 1 (capL n)).erase i),
        ordinaryPrefixExposure c0 m j (cs j) =
          ordinaryPrefixExposure c0 m j (Cseq j ω)) → cs ∈ s →
            ∀ r, P r (fun j => cs j.val)) →
      ((fixedClauseMeasure μ Cseq i c0)[
        eventIndicator {ω' | (fun j : ((Finset.Icc 1 (capL n)).erase i) =>
          Cseq j ω') ∈ s} | ordinaryFiltration c0 Cseq i m]) ω ≤
        ∏ r, (Fintype.card {cs : ∀ j : {j // label j = r},
          {c : ProperClause n // ordinaryPrefixExposure c0 m j.val c =
            ordinaryPrefixExposure c0 m j.val (Cseq j.val ω)} //
              P r (fun j => (cs j).val)} : ℝ) /
          Fintype.card (∀ j : {j // label j = r},
            {c : ProperClause n // ordinaryPrefixExposure c0 m j.val c =
              ordinaryPrefixExposure c0 m j.val (Cseq j.val ω)}) := by
  classical
  filter_upwards [ordinary_hidden_clause_event_law μ Cseq hlaw i hi c0 m hm]
    with ω hω
  intro s label P hnecessary
  rw [hω s]
  have hb := finite_coordinate_fiber_event_le_families
    (fun j : ((Finset.Icc 1 (capL n)).erase i) => ordinaryPrefixExposure c0 m j)
    (fun j => Cseq j ω) s label P hnecessary
  simp only [← Nat.card_eq_fintype_card] at hb ⊢
  exact hb

end Papers.OaiLinearVarianceRandom
