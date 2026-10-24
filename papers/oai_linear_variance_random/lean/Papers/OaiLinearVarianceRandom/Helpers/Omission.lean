module

public import Papers.OaiLinearVarianceRandom.Basic
public import Causalean.Mathlib.Probability.Poisson.Poincare.Tensorization

/-! # Deletion variance bound for the capped satisfiability hitting time -/

public section

namespace Papers.OaiLinearVarianceRandom
open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.PoissonAddOnePoincare
open scoped BigOperators
set_option linter.unusedVariables false

/-- For independent coordinates with a common probability law on a finite
space, if [each coordinate-specific comparison function is unchanged when
that coordinate is replaced](hyp:hG), then [the variance of any real statistic
is at most the sum over coordinates of its expected squared difference from
the corresponding comparison function](goal). -/
-- @node: variance_finite_product_omission
lemma variance_finite_product_omission {A : Type} [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (ν : Measure A) [IsProbabilityMeasure ν] (N : ℕ)
    (F : (Fin N → A) → ℝ) (G : Fin N → (Fin N → A) → ℝ)
    (hG : ∀ i x y, G i (Function.update x i y) = G i x) :
    variance F (Measure.pi (fun _ : Fin N => ν)) ≤
      ∑ i : Fin N, ∫ x, (F x - G i x) ^ 2 ∂Measure.pi (fun _ : Fin N => ν) := by
  classical
  have hF : MemLp F 2 (Measure.pi (fun _ : Fin N => ν)) :=
    ⟨.of_discrete, eLpNorm_lt_top_of_finite⟩
  apply (variance_pi_le_sum_integral_coordinateVariance (fun _ : Fin N => ν) F hF).trans
  apply Finset.sum_le_sum
  intro i _
  rcases N with _ | N
  · exact Fin.elim0 i
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => A) i
  let τ := Measure.pi (fun _ : Fin N => ν)
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (N + 1) => ν) i
  have hins (x : Fin (N + 1) → A) (y : A) :
      e.symm (y, (e x).2) = Function.update x i y := by
    simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv] using
      (Fin.insertNth_removeNth i y x)
  have hup (z : A × (Fin N → A)) (y : A) :
      Function.update (e.symm z) i y = e.symm (y, z.2) := by
    simpa using (hins (e.symm z) y).symm
  have hpoint (z : Fin N → A) (a : A) :
      variance (fun y => F (e.symm (y, z))) ν ≤
        ∫ y, (F (e.symm (y, z)) - G i (e.symm (a, z))) ^ 2 ∂ν := by
    rw [← variance_sub_const (X := fun y => F (e.symm (y, z)))
      (.of_discrete) (G i (e.symm (a, z)))]
    exact variance_le_expectation_sq (.of_discrete)
  calc
    (∫ x, variance (fun y => F
        (coordinateReplace i x y)) ν
        ∂Measure.pi (fun _ : Fin (N + 1) => ν)) =
        ∫ z : A × (Fin N → A), variance (fun y => F (e.symm (y, z.2))) ν
          ∂ν.prod τ := by
      rw [← hmp.symm.integral_comp']
      apply integral_congr_ae
      filter_upwards [] with z
      change variance (fun y => F (Function.update (e.symm z) i y)) ν = _
      simp only [hup]
    _ ≤ ∫ z : A × (Fin N → A),
        ∫ y, (F (e.symm (y, z.2)) - G i (e.symm z)) ^ 2 ∂ν ∂ν.prod τ := by
      exact integral_mono Integrable.of_finite Integrable.of_finite
        (fun z => hpoint z.2 z.1)
    _ = ∫ z : A × (Fin N → A),
        ∫ y, (F (e.symm (y, z.2)) - G i (e.symm (y, z.2))) ^ 2 ∂ν ∂ν.prod τ := by
      apply integral_congr_ae
      filter_upwards [] with z
      apply integral_congr_ae
      filter_upwards [] with y
      rw [← hup, hG]
    _ = ∫ z : A × (Fin N → A),
        (F (e.symm z) - G i (e.symm z)) ^ 2 ∂ν.prod τ := by
      rw [integral_prod_symm _ Integrable.of_finite,
        integral_prod_symm _ Integrable.of_finite]
      simp
    _ = _ := hmp.symm.integral_comp' (fun x => (F x - G i x) ^ 2)

/-- If [two clause sequences agree at every positive index up to the cap
other than the omitted index](hyp:h), then [their capped hitting times after
omitting that index are equal](goal). -/
-- @node: omittedCappedTime_congr
lemma omittedCappedTime_congr {n : ℕ} (c c' : ℕ → ProperClause n) (i : ℕ)
    (h : ∀ j ∈ Finset.Icc 1 (capL n), j ≠ i → c j = c' j) :
    omittedCappedTime c i = omittedCappedTime c' i := by
  classical
  have hsat (m : ℕ) (hm : m ≤ capL n) :
      omittedPrefixSat c i m ↔ omittedPrefixSat c' i m := by
    have heq (j : ℕ) (hj : j ∈ Finset.Icc 1 m) (hji : j ≠ i) : c j = c' j :=
      h j (Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hj).1, (Finset.mem_Icc.mp hj).2.trans hm⟩) hji
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨z, fun j hj hji => heq j hj hji ▸ hz j hj hji⟩
    · rintro ⟨z, hz⟩
      exact ⟨z, fun j hj hji => (heq j hj hji).symm ▸ hz j hj hji⟩
  have hset : (Set.Icc 1 (capL n) ∩ {m | ¬ omittedPrefixSat c i m}) =
      (Set.Icc 1 (capL n) ∩ {m | ¬ omittedPrefixSat c' i m}) := by
    ext m
    exact and_congr_right (fun hm => not_congr (hsat m hm.2))
  have hex : (∃ m ∈ Set.Icc 1 (capL n), ¬ omittedPrefixSat c i m) ↔
      (∃ m ∈ Set.Icc 1 (capL n), ¬ omittedPrefixSat c' i m) := by
    change (Set.Icc 1 (capL n) ∩ {m | ¬ omittedPrefixSat c i m}).Nonempty ↔
      (Set.Icc 1 (capL n) ∩ {m | ¬ omittedPrefixSat c' i m}).Nonempty
    rw [hset]
  simp only [omittedCappedTime, MeasureTheory.hittingBtwn, Set.mem_singleton_iff,
    eq_iff_iff, iff_true]
  rw [hset, hex]

-- @node: lem:omission
/-- If [there are at least six variables](hyp:hn) and [the positive-index
clauses are measurable, independent, and uniformly distributed](hyp:hlaw),
then [the variance of the capped satisfiability hitting time is at most
the sum, over positive indices up to the cap, of the expected squared delay
caused by omitting that clause](goal). -/
lemma variance_cappedTime_le_sum_delay_sq {n : ℕ} (hn : OmissionN n)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Cseq : ℕ → Ω → ProperClause n) (hlaw : IsUniformClauseProcess μ Cseq) :
    variance (fun ω => (cappedTime (fun j => Cseq j ω) : ℝ)) μ ≤
      ∑ i ∈ Finset.Icc 1 (capL n),
        ∫ ω, (delay (fun j => Cseq j ω) i : ℝ) ^ 2 ∂μ := by
  classical
  have hn3 : 3 ≤ n := by unfold OmissionN at hn; omega
  letI : Nonempty (ProperClause n) := properClauseA_nonempty n 3 hn3
  letI : MeasurableSingletonClass (ProperClause n) := ⟨fun _ => trivial⟩
  let ν := uniformClauseMeasure n 3
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν, uniformClauseMeasure]
    infer_instance
  let L := capL n
  let extend : (Fin L → ProperClause n) → ℕ → ProperClause n :=
    fun x j => if h : j - 1 < L then x ⟨j - 1, h⟩ else Classical.choice inferInstance
  let X : Ω → (Fin L → ProperClause n) := fun ω j => Cseq (j.val + 1) ω
  have hXm : Measurable X := by
    apply measurable_pi_lambda
    intro j
    exact hlaw.1 _ (by omega)
  have hXi : iIndepFun (fun j : Fin L => Cseq (j.val + 1)) μ :=
    hlaw.2.1.precomp Fin.val_injective
  have hmap : μ.map X = Measure.pi (fun _ : Fin L => ν) := by
    rw [iIndepFun.map_fun_eq_pi_map (fun j => (hlaw.1 _ (by omega)).aemeasurable) hXi]
    congr 1
    funext j
    exact hlaw.2.2 _ (by omega)
  have hmp : MeasurePreserving X μ (Measure.pi (fun _ : Fin L => ν)) := ⟨hXm, hmap⟩
  have hextX (ω : Ω) (j : ℕ) (hj : j ∈ Finset.Icc 1 L) :
      extend (X ω) j = Cseq j ω := by
    have hj' := Finset.mem_Icc.mp hj
    simp [extend, X, show j - 1 < L by omega, show j - 1 + 1 = j by omega]
  have hT (ω : Ω) : cappedTime (extend (X ω)) =
      cappedTime (fun j => Cseq j ω) := cappedTime_congr _ _ (hextX ω)
  have hO (ω : Ω) (i : ℕ) : omittedCappedTime (extend (X ω)) i =
      omittedCappedTime (fun j => Cseq j ω) i :=
    omittedCappedTime_congr _ _ _ (fun j hj _ => hextX ω j hj)
  let F : (Fin L → ProperClause n) → ℝ := fun x => cappedTime (extend x)
  let G : Fin L → (Fin L → ProperClause n) → ℝ :=
    fun i x => omittedCappedTime (extend x) (i.val + 1)
  have hG (i : Fin L) (x : Fin L → ProperClause n) (y : ProperClause n) :
      G i (Function.update x i y) = G i x := by
    dsimp [G]
    congr 1
    apply omittedCappedTime_congr
    intro j hj hji
    have hj' := Finset.mem_Icc.mp hj
    have hjL : j - 1 < L := by omega
    have hne : (⟨j - 1, hjL⟩ : Fin L) ≠ i := by
      intro h
      have hh : j - 1 = i.val := congrArg Fin.val h
      omega
    simp [extend, hjL, Function.update_of_ne hne]
  have hvar := variance_finite_product_omission ν L F G hG
  have henergy (i : Fin L) :
      (∫ x, (F x - G i x) ^ 2 ∂Measure.pi (fun _ : Fin L => ν)) =
        ∫ ω, (delay (fun j => Cseq j ω) (i.val + 1) : ℝ) ^ 2 ∂μ := by
    rw [← hmp.map_eq, integral_map hmp.aemeasurable (.of_discrete)]
    apply integral_congr_ae
    filter_upwards [] with ω
    dsimp [F, G]
    rw [hT, hO, delay, Nat.cast_sub (cappedTime_le_omittedCappedTime hn _ _)]
    ring
  calc
    variance (fun ω => (cappedTime (fun j => Cseq j ω) : ℝ)) μ =
        variance F (Measure.pi (fun _ : Fin L => ν)) := by
      rw [← hmp.variance_fun_comp (show AEMeasurable F _ from .of_discrete)]
      congr 1
      funext ω
      exact congrArg (fun k : ℕ => (k : ℝ)) (hT ω).symm
    _ ≤ ∑ i : Fin L, ∫ ω,
        (delay (fun j => Cseq j ω) (i.val + 1) : ℝ) ^ 2 ∂μ := by
      simpa only [henergy] using hvar
    _ = _ := by
      apply Finset.sum_bij (fun (i : Fin L) _ => i.val + 1)
      · intro i _
        exact Finset.mem_Icc.mpr ⟨by omega, by have := i.isLt; omega⟩
      · intro i _ j _ hij
        apply Fin.ext
        omega
      · intro j hj
        have hj' := Finset.mem_Icc.mp hj
        refine ⟨⟨j - 1, by omega⟩, Finset.mem_univ _, ?_⟩
        simp only
        omega
      · intro i _
        rfl

end Papers.OaiLinearVarianceRandom
