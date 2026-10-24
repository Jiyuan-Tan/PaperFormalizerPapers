module

public import Papers.OaiLinearVarianceRandom.Helpers.RootExposure

/-!
# Conditional laws on finite root-exposure fibers

Finite indicator conditional expectations are computed by fiber ratios, following
`Causalean.Stat.FiniteFiberConditioning` (whose corresponding helper is private).
The iid clause law is first conditioned on the omitted clause; finite product
masses then give the independent uniform laws within every exposure fiber.
No standard Borel assumption on the ambient space is needed.
-/

public section

namespace Papers.OaiLinearVarianceRandom
open MeasureTheory ProbabilityTheory
open scoped BigOperators
set_option linter.unusedVariables false

/-- For [a measurable finite-valued observation](hyp:hX) and [a measurable
event](hyp:hA), [the event's conditional probability given the observation equals,
almost surely, the mass of the event within the observed fiber divided by the
mass of that fiber](goal). -/
-- @node: condExp_indicator_finite_comap
lemma condExp_indicator_finite_comap
    {Omega T : Type*} [Finite T] [MeasurableSpace T]
    [MeasurableSingletonClass T] [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (X : Omega → T) (hX : Measurable X)
    (A : Set Omega) (hA : MeasurableSet A) :
    mu[A.indicator (fun _ => (1 : ℝ)) |
      MeasurableSpace.comap X inferInstance] =ᵐ[mu]
      fun omega => (mu.real (X ⁻¹' {X omega}))⁻¹ * mu.real ((X ⁻¹' {X omega}) ∩ A) := by
  let _ := Fintype.ofFinite T
  let q : T → ℝ := fun x => (mu.real (X ⁻¹' {x}))⁻¹ * mu.real ((X ⁻¹' {x}) ∩ A)
  have hq : Measurable q := measurable_of_finite q
  have hqm : StronglyMeasurable[MeasurableSpace.comap X
      (inferInstance : MeasurableSpace T)] (q ∘ X) :=
    (hq.comp (comap_measurable X)).stronglyMeasurable
  have hqOmega : StronglyMeasurable (q ∘ X) :=
    (hq.comp hX).stronglyMeasurable
  have hq_int : Integrable (q ∘ X) mu := by
    apply Integrable.of_bound hqOmega.aestronglyMeasurable 1
    filter_upwards [] with omega
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · exact (by norm_num : (-1 : ℝ) ≤ 0).trans
        (mul_nonneg (inv_nonneg.mpr measureReal_nonneg) measureReal_nonneg)
    · dsimp [q]
      by_cases hz : mu.real (X ⁻¹' {X omega}) = 0
      · simp [hz]
      · rw [inv_mul_le_one₀ (lt_of_le_of_ne measureReal_nonneg (Ne.symm hz))]
        exact measureReal_mono Set.inter_subset_left
  have hind : Integrable (A.indicator fun _ => (1 : ℝ)) mu :=
    (integrable_const 1).indicator hA
  have hversion :
      (q ∘ X) =ᵐ[mu]
        mu[A.indicator (fun _ => (1 : ℝ)) |
          MeasurableSpace.comap X (inferInstance : MeasurableSpace T)] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq hX.comap_le hind
    · intro x _ _
      exact hq_int.integrableOn
    · intro x hx _
      rcases hx with ⟨u, hu, rfl⟩
      classical
      let U : Finset T := Finset.univ.filter (· ∈ u)
      rw [show X ⁻¹' u = ⋃ x ∈ U, X ⁻¹' {x} by
        ext omega
        simp [U]]
      rw [integral_biUnion_finset, integral_biUnion_finset]
      · apply Finset.sum_congr rfl
        intro x hx
        have heq :
            (q ∘ X) =ᵐ[mu.restrict (X ⁻¹' {x})] fun _ => q x := by
          filter_upwards [ae_restrict_mem
            (hX (measurableSet_singleton x))] with omega homega
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at homega
          exact congrArg q homega
        rw [integral_congr_ae heq, integral_const]
        change ((mu.restrict (X ⁻¹' {x})) Set.univ).toReal * q x =
          ∫ y in X ⁻¹' {x}, A.indicator (fun _ => (1 : ℝ)) y ∂mu
        rw [Measure.restrict_apply_univ]
        rw [integral_indicator hA, setIntegral_const, smul_eq_mul, mul_one]
        dsimp [q]
        change mu.real (X ⁻¹' {x}) *
            ((mu.real (X ⁻¹' {x}))⁻¹ *
              mu.real ((X ⁻¹' {x}) ∩ A)) =
          ((mu.restrict (X ⁻¹' {x})) A).toReal
        rw [Measure.restrict_apply hA, Set.inter_comm A]
        change mu.real (X ⁻¹' {x}) *
            ((mu.real (X ⁻¹' {x}))⁻¹ *
              mu.real ((X ⁻¹' {x}) ∩ A)) =
          mu.real ((X ⁻¹' {x}) ∩ A)
        by_cases hzero : mu.real (X ⁻¹' {x}) = 0
        · have hsub : mu.real ((X ⁻¹' {x}) ∩ A) = 0 :=
            le_antisymm (hzero ▸ measureReal_mono Set.inter_subset_left)
              measureReal_nonneg
          simp [hzero, hsub]
        · field_simp
      · intro x _
        exact hX (measurableSet_singleton x)
      · exact Set.pairwiseDisjoint_fiber X U
      · intro x _
        exact hind.integrableOn
      · intro x _
        exact hX (measurableSet_singleton x)
      · exact Set.pairwiseDisjoint_fiber X U
      · intro x _
        exact hq_int.integrableOn
    · exact hqm.aestronglyMeasurable
  exact hversion.symm

open Classical in
/-- [Conditioning a uniform draw from a finite set on having the same image as
a fixed point assigns each point in that fiber the reciprocal of the fiber's
size, and assigns zero to every point outside the fiber](goal). -/
-- @node: uniform_cond_fiber_singleton
lemma uniform_cond_fiber_singleton {A B : Type*} [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (f : A → B) (a b : A) :
    (cond (uniformOn (Set.univ : Set A)) {x | f x = f a}).real {b} =
      if f b = f a then (Fintype.card {x : A // f x = f a} : ℝ)⁻¹ else 0 := by
  classical
  letI : Nonempty A := ⟨a⟩
  have hf : MeasurableSet {x | f x = f a} := Set.toFinite _ |>.measurableSet
  rw [measureReal_def, cond_apply hf]
  by_cases hb : f b = f a
  · have hi : {x | f x = f a} ∩ {b} = {b} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · exact And.right
      · intro h; subst x; exact ⟨hb, rfl⟩
    rw [hi, uniformOn_univ, uniformOn_univ]
    rw [Measure.count_singleton, Measure.count_apply_finite _ (Set.toFinite _),
      Set.toFinite_toFinset, Set.toFinset_card]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div,
      ENNReal.toReal_natCast, ENNReal.toReal_one, hb, if_true]
    have hn : (Fintype.card A : ℝ) ≠ 0 := by positivity
    haveI : Nonempty {x : A // f x = f a} := ⟨⟨a, rfl⟩⟩
    have hfiber : (Fintype.card {x : A // f x = f a} : ℝ) ≠ 0 := by positivity
    field_simp
    exact_mod_cast Fintype.card_congr (Equiv.refl {x : A // f x = f a})
  · have hi : {x | f x = f a} ∩ {b} = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro h hxb
      exact hb (hxb ▸ h)
    simp [hi, hb]

/-- For [an independent uniform clause process](hyp:hlaw), if [the selected
indices are distinct](hyp:hk) and [all are positive](hyp:hkpos), then [the
probability that each selected clause belongs to its designated set equals the
product of those sets' uniform clause probabilities](goal). -/
-- @node: clauseProcess_joint_mass
lemma clauseProcess_joint_mass {n : ℕ} {Ω : Type} {I : Type*} [MeasurableSpace Ω]
    [Fintype I] (μ : Measure Ω) (Cseq : ℕ → Ω → ProperClause n)
    (hlaw : IsUniformClauseProcess μ Cseq) (k : I → ℕ)
    (hk : Function.Injective k) (hkpos : ∀ j, 1 ≤ k j)
    (sets : I → Set (ProperClause n)) :
    μ {ω | ∀ j, Cseq (k j) ω ∈ sets j} =
      ∏ j, uniformClauseMeasure n 3 (sets j) := by
  have hinj : Function.Injective (fun j => k j - 1) := by
    intro a b hab
    dsimp only at hab
    apply hk
    have ha := hkpos a
    have hb := hkpos b
    omega
  have hi : iIndepFun (fun j : I => Cseq (k j)) μ := by
    have h := hlaw.2.1.precomp hinj
    convert h using 1
    funext j ω
    congr 1
    have hpos := hkpos j
    omega
  have hprob (j : I) : μ (Cseq (k j) ⁻¹' sets j) =
      uniformClauseMeasure n 3 (sets j) := by
    rw [← hlaw.2.2 (k j) (hkpos j), Measure.map_apply (hlaw.1 _ (hkpos j))]
    trivial
  have h := hi.meas_iInter (s := fun j => Cseq (k j) ⁻¹' sets j)
    (fun j => ⟨sets j, by trivial, rfl⟩)
  simp only [hprob] at h
  convert h using 1
  congr 1
  ext ω
  simp

open Classical in
/-- For [an independent uniform clause process](hyp:hlaw), [a positive index at
which a clause is fixed](hyp:hi), and [a finite set of positive indices different
from that index](hyp:hJ), [the probability under the fixed-clause law that each
selected clause belongs to its designated set equals the product of the
corresponding uniform clause probabilities](goal). -/
-- @node: fixedClauseMeasure_joint_mass
lemma fixedClauseMeasure_joint_mass {n : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Cseq : ℕ → Ω → ProperClause n)
    (hlaw : IsUniformClauseProcess μ Cseq) (i : ℕ) (hi : 1 ≤ i)
    (c0 : ProperClause n) (J : Finset ℕ)
    (hJ : ∀ j ∈ J, 1 ≤ j ∧ j ≠ i) (sets : J → Set (ProperClause n)) :
    fixedClauseMeasure μ Cseq i c0 {ω | ∀ j : J, Cseq j ω ∈ sets j} =
      ∏ j : J, uniformClauseMeasure n 3 (sets j) := by
  let k : Option J → ℕ := fun o => o.elim i Subtype.val
  have hk : Function.Injective k := by
    intro a b hab
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b => exact False.elim ((hJ b b.property).2 (by simpa [k] using hab.symm))
    | some a =>
      cases b with
      | none => exact False.elim ((hJ a a.property).2 (by simpa [k] using hab))
      | some b => exact congrArg some (Subtype.ext (by simpa [k] using hab))
  have hpos : ∀ j, 1 ≤ k j := by
    intro j
    cases j with
    | none => exact hi
    | some j => exact (hJ j j.property).1
  let t : Option J → Set (ProperClause n) := fun o => o.elim {c0} sets
  have hmass := clauseProcess_joint_mass μ Cseq hlaw k hk hpos t
  have he : {ω | Cseq i ω = c0} ∩ {ω | ∀ j : J, Cseq j ω ∈ sets j} =
      {ω | ∀ o : Option J, Cseq (k o) ω ∈ t o} := by
    ext ω
    simp [k, t, Option.forall]
  have hfix : μ {ω | Cseq i ω = c0} = uniformClauseMeasure n 3 {c0} := by
    rw [← hlaw.2.2 i hi, Measure.map_apply (hlaw.1 i hi) (by trivial)]
    rfl
  have hnonzero : uniformClauseMeasure n 3 {c0} ≠ 0 := by
    haveI : Nonempty (ProperClause n) := ⟨c0⟩
    simp [uniformClauseMeasure, uniformOn_univ, Measure.count_singleton,
      ENNReal.div_ne_zero]
  have hmeas : MeasurableSet {ω | Cseq i ω = c0} :=
    (hlaw.1 i hi) (measurableSet_singleton c0)
  rw [fixedClauseMeasure, cond_apply hmeas, he, hmass, hfix]
  simp only [Fintype.prod_option, t, Option.elim_none, Option.elim_some]
  rw [← mul_assoc, ENNReal.inv_mul_cancel hnonzero (hfix ▸ measure_ne_top μ _), one_mul]

variable {n : ℕ} {Ω : Type} [MeasurableSpace Ω]

set_option maxHeartbeats 1200000 in
open Classical in
/-- With [at least six variables](hyp:hn), [an independent uniform clause
process](hyp:hlaw), and [an omitted index between one and the cap](hyp:hi), [under
the law fixing the omitted clause, almost surely and for every finite selection
of other indices from one through the cap, the conditional probability given
the exposure information of specified clauses equals the product of reciprocal
exposure-fiber sizes when all specified exposures match the observed exposures,
and is zero otherwise](goal). -/
-- @node: hidden_clause_conditional_law
lemma hidden_clause_conditional_law (hn : OmissionN n) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Cseq : ℕ → Ω → ProperClause n)
    (hlaw : IsUniformClauseProcess μ Cseq) (i : ℕ) (hi : DelayIndex i (capL n))
    (c0 : ProperClause n) :
    ∀ᵐ ω ∂(fixedClauseMeasure μ Cseq i c0),
      ∀ J : Finset ℕ, J ⊆ (Finset.Icc 1 (capL n)).erase i →
        ∀ cs : ℕ → ProperClause n,
          ((fixedClauseMeasure μ Cseq i c0)[
        eventIndicator {ω' | ∀ j ∈ J, Cseq j ω' = cs j} |
          exposureSigma c0 Cseq i]) ω =
          ∏ j ∈ J, (if expose c0 (cs j) = expose c0 (Cseq j ω) then
            (Fintype.card {c : ProperClause n // expose c0 c = expose c0 (Cseq j ω)} : ℝ)⁻¹
            else 0) := by
  classical
  let T := (Finset.Icc 1 (capL n)).erase i
  let E := Finset (Fin n × Bool) × Option (ProperClause n)
  letI : MeasurableSpace E := ⊤
  let Y : Ω → (T → E) := fun ω j => expose c0 (Cseq j ω)
  let ν := fixedClauseMeasure μ Cseq i c0
  have hT (j : T) : 1 ≤ (j : ℕ) ∧ (j : ℕ) ≠ i := by
    obtain ⟨hne, hj⟩ := Finset.mem_erase.mp j.property
    exact ⟨(Finset.mem_Icc.mp hj).1, hne⟩
  have hY : Measurable Y := by
    apply measurable_pi_lambda
    intro j
    exact (measurable_of_finite (expose c0)).comp (hlaw.1 _ (hT j).1)
  have hSigma : exposureSigma c0 Cseq i = MeasurableSpace.comap Y inferInstance := by
    simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
      MeasurableSpace.comap_comp, Function.comp_def, Y]
    unfold exposureSigma
    apply le_antisymm
    · apply iSup_le
      intro j
      apply iSup_le
      intro hj
      exact le_iSup_of_le (⟨j, hj⟩ : T) le_rfl
    · apply iSup_le
      intro j
      exact le_iSup_of_le j.val (le_iSup_of_le j.property le_rfl)
  have hν : IsProbabilityMeasure ν := by
    apply cond_isProbabilityMeasure
    change μ (Cseq i ⁻¹' {c0}) ≠ 0
    rw [← Measure.map_apply (hlaw.1 i hi.1) (measurableSet_singleton c0),
        hlaw.2.2 i hi.1]
    haveI : Nonempty (ProperClause n) := ⟨c0⟩
    simp [uniformClauseMeasure, uniformOn_univ, Measure.count_singleton,
      ENNReal.div_ne_zero]
  have hmass (sets : T → Set (ProperClause n)) :
      ν {ω | ∀ j : T, Cseq j ω ∈ sets j} =
        ∏ j : T, uniformClauseMeasure n 3 (sets j) :=
    fixedClauseMeasure_joint_mass μ Cseq hlaw i hi.1 c0 T
      (fun j hj => hT ⟨j, hj⟩) sets
  haveI : Nonempty (ProperClause n) := ⟨c0⟩
  haveI : IsProbabilityMeasure (uniformClauseMeasure n 3) := by
    unfold uniformClauseMeasure
    infer_instance
  have hversion (K : Finset T) (cs : T → ProperClause n) :
      ν[eventIndicator {ω | ∀ j ∈ K, Cseq j ω = cs j} |
          MeasurableSpace.comap Y inferInstance] =ᵐ[ν]
        fun ω => ∏ j ∈ K, (if expose c0 (cs j) = expose c0 (Cseq j ω) then
          (Fintype.card {c : ProperClause n //
            expose c0 c = expose c0 (Cseq j ω)} : ℝ)⁻¹ else 0) := by
    have hA : MeasurableSet {ω | ∀ j ∈ K, Cseq j ω = cs j} := by
      have hm := MeasurableSet.iInter fun j : T =>
        MeasurableSet.iInter fun _ : j ∈ K =>
          (hlaw.1 j (hT j).1) (measurableSet_singleton (cs j))
      convert hm using 1
      ext ω
      simp
    have hce := condExp_indicator_finite_comap ν Y hY
      {ω | ∀ j ∈ K, Cseq j ω = cs j} hA
    filter_upwards [hce] with ω hω
    rw [show eventIndicator {ω | ∀ j ∈ K, Cseq j ω = cs j} =
      {ω | ∀ j ∈ K, Cseq j ω = cs j}.indicator (fun _ => (1 : ℝ)) by
        ext ω'; simp [eventIndicator, Set.indicator_apply]]
    rw [hω]
    let D : T → Set (ProperClause n) := fun j =>
      {c | expose c0 c = expose c0 (Cseq j ω)}
    let N : T → Set (ProperClause n) := fun j =>
      D j ∩ (if j ∈ K then {cs j} else Set.univ)
    have hden : ν (Y ⁻¹' {Y ω}) = ∏ j : T, uniformClauseMeasure n 3 (D j) := by
      convert hmass D using 1
      congr 1
      ext ω'
      simp [Y, D, funext_iff]
    have hnum : ν (Y ⁻¹' {Y ω} ∩ {ω | ∀ j ∈ K, Cseq j ω = cs j}) =
        ∏ j : T, uniformClauseMeasure n 3 (N j) := by
      convert hmass N using 1
      congr 1
      ext ω'
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_ofPred_eq, funext_iff, N, D, Y]
      constructor
      · rintro ⟨he, hc⟩ j
        refine ⟨he j, ?_⟩
        by_cases hj : j ∈ K <;> simp [hj, hc]
      · intro h
        refine ⟨fun j => (h j).1, ?_⟩
        intro j hj
        simpa [hj] using (h j).2
    simp only [measureReal_def, hden, hnum, ENNReal.toReal_prod]
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    have hfactor (j : T) :
        ((uniformClauseMeasure n 3 (D j)).toReal)⁻¹ *
          (uniformClauseMeasure n 3 (N j)).toReal =
        if j ∈ K then (if expose c0 (cs j) = expose c0 (Cseq j ω) then
          (Fintype.card {c : ProperClause n //
            expose c0 c = expose c0 (Cseq j ω)} : ℝ)⁻¹ else 0) else 1 := by
      by_cases hj : j ∈ K
      · simp only [hj, if_true, N]
        have h := uniform_cond_fiber_singleton (expose c0) (Cseq j ω) (cs j)
        simpa only [← Nat.card_eq_fintype_card, uniformClauseMeasure, measureReal_def,
          cond_apply (show MeasurableSet (D j) by trivial), ENNReal.toReal_mul,
          ENNReal.toReal_inv, D] using h
      · simp only [N, hj, if_false, Set.inter_univ]
        apply inv_mul_cancel₀
        have hs : 0 < (uniformClauseMeasure n 3).real {Cseq j ω} := by
          simp [uniformClauseMeasure, measureReal_def, uniformOn_univ,
            Measure.count_singleton]
          exact Fintype.card_pos
        exact ne_of_gt (hs.trans_le (measureReal_mono (by
          intro c hc
          simpa only [Set.mem_singleton_iff] using hc ▸ rfl)))
    simp_rw [hfactor]
    rw [Finset.prod_ite_mem]
    congr 1
    ext j
    simp
  have hall : ∀ᵐ ω ∂ν, ∀ (K : Finset T) (cs : T → ProperClause n),
      ν[eventIndicator {ω | ∀ j ∈ K, Cseq j ω = cs j} |
          MeasurableSpace.comap Y inferInstance] ω =
        ∏ j ∈ K, (if expose c0 (cs j) = expose c0 (Cseq j ω) then
          (Fintype.card {c : ProperClause n //
            expose c0 c = expose c0 (Cseq j ω)} : ℝ)⁻¹ else 0) := by
    exact ae_all_iff.mpr fun K => ae_all_iff.mpr fun cs => hversion K cs
  filter_upwards [hall] with ω hω
  intro J hJ cs
  let K : Finset T := Finset.univ.filter (fun j => j.val ∈ J)
  have hK (j : T) : j ∈ K ↔ j.val ∈ J := by simp [K]
  have hevent : {ω' | ∀ j ∈ J, Cseq j ω' = cs j} =
      {ω' | ∀ j ∈ K, Cseq j ω' = cs j} := by
    ext ω'
    constructor
    · intro h j hj
      exact h j ((hK j).mp hj)
    · intro h j hj
      exact h ⟨j, hJ hj⟩ ((hK _).mpr hj)
  rw [hevent, hSigma]
  change ν[eventIndicator {ω' | ∀ j ∈ K, Cseq j ω' = cs j} |
      MeasurableSpace.comap Y inferInstance] ω = _
  rw [hω K (fun j => cs j)]
  apply Finset.prod_bij (fun j _ => j.val)
  · intro j hj
    exact (hK j).mp hj
  · intro a _ b _ hab
    exact Subtype.ext hab
  · intro j hj
    exact ⟨⟨j, hJ hj⟩, (hK _).mpr hj, rfl⟩
  · intro j hj
    rfl

end Papers.OaiLinearVarianceRandom
