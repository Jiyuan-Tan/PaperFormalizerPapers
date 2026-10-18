module
public import Papers.TbsPrteOptimalTransport.Helpers.DMLProcedure
/-! Deterministic graph recovery under uniformly small errors in marginal levels.
The population values here are the marginal means of the baseline and policy
propensities. Their equality classes are identified by the gap graph before
ordering the recovered components. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace Papers.TbsPrteOptimalTransport
open Set
open scoped Classical

-- @node: separated_values_close_iff_equal
/-- If [the first estimate is within one quarter of the gap of its population value](hyp:hu),
[the second estimate satisfies the same error bound](hyp:hv), and [the population values
are either equal or at least the gap apart](hyp:hsep), then [the estimates differ by less
than half the gap exactly when the population values are equal](goal). -/
lemma separated_values_close_iff_equal (u v uHat vHat gap : ℝ)
    (hu : |uHat - u| < gap / 4) (hv : |vHat - v| < gap / 4)
    (hsep : u = v ∨ gap ≤ |u - v|) :
    |uHat - vHat| < gap / 2 ↔ u = v := by
  constructor
  · intro hclose
    rcases hsep with heq | hgap
    · exact heq
    · have htri₁ := abs_sub_le u uHat vHat
      have htri₂ := abs_sub_le u vHat v
      rw [abs_sub_comm u uHat] at htri₁
      linarith
  · intro heq
    have htri := abs_sub_le uHat u vHat
    rw [← heq] at hv
    rw [abs_sub_comm u vHat] at htri
    linarith

variable {Z X : Type*} [Fintype Z] [DecidableEq Z]

-- @node: recoveryEdge_iff_population_equal
/-- Suppose [every active vertex's estimated value is within one quarter of the gap of
its population value](hyp:herror) and [population values of active vertices are equal or
at least the gap apart](hyp:hsep). If [the first vertex is active](hyp:ha), [the second
vertex is active](hyp:hb), and [they are distinct](hyp:hne), then [a recovery edge joins
them exactly when their population values are equal](goal). -/
lemma recoveryEdge_iff_population_equal (pb qb : Z → ℝ)
    (rho gap : ℝ) (truth : RecoveryVertex Z → ℝ)
    (herror : ∀ v ∈ recoveryActive pb rho,
      |vertexValue pb qb v - truth v| < gap / 4)
    (hsep : ∀ a ∈ recoveryActive pb rho, ∀ b ∈ recoveryActive pb rho,
      truth a = truth b ∨ gap ≤ |truth a - truth b|)
    {a b : RecoveryVertex Z} (ha : a ∈ recoveryActive pb rho)
    (hb : b ∈ recoveryActive pb rho) (hne : a ≠ b) :
    recoveryEdge pb qb rho gap a b ↔ truth a = truth b := by
  have hc := separated_values_close_iff_equal _ _ _ _ gap
    (herror a ha) (herror b hb) (hsep a ha b hb)
  exact ⟨fun h => hc.mp h.2.2.2, fun h => ⟨ha, hb, hne, hc.mpr h⟩⟩

-- @node: recovery_path_population_equal
/-- If [active vertices have estimation errors smaller than one quarter of the gap](hyp:herror)
and [their population values are equal or at least the gap apart](hyp:hsep), then
[a path of recovery edges, including a path of length zero, between two vertices](hyp:hpath)
implies [equality of their population values](goal). -/
lemma recovery_path_population_equal (pb qb : Z → ℝ)
    (rho gap : ℝ) (truth : RecoveryVertex Z → ℝ)
    (herror : ∀ v ∈ recoveryActive pb rho,
      |vertexValue pb qb v - truth v| < gap / 4)
    (hsep : ∀ a ∈ recoveryActive pb rho, ∀ b ∈ recoveryActive pb rho,
      truth a = truth b ∨ gap ≤ |truth a - truth b|)
    {a b : RecoveryVertex Z}
    (hpath : Relation.ReflTransGen (recoveryEdge pb qb rho gap) a b) :
    truth a = truth b := by
  induction hpath with
  | refl => rfl
  | @tail b c _ hbc ih =>
    exact ih.trans ((recoveryEdge_iff_population_equal pb qb rho gap truth
      herror hsep hbc.1 hbc.2.1 hbc.2.2.1).mp hbc)

-- @node: recoveryComponent_eq_population_class
/-- Suppose [active vertices have estimation errors smaller than one quarter of the gap](hyp:herror)
and [their population values are equal or at least the gap apart](hyp:hsep). For
[an active vertex](hyp:ha), [its recovered component consists exactly of the active
vertices sharing its population value](goal). -/
lemma recoveryComponent_eq_population_class (pb qb : Z → ℝ)
    (rho gap : ℝ) (truth : RecoveryVertex Z → ℝ)
    (herror : ∀ v ∈ recoveryActive pb rho,
      |vertexValue pb qb v - truth v| < gap / 4)
    (hsep : ∀ a ∈ recoveryActive pb rho, ∀ b ∈ recoveryActive pb rho,
      truth a = truth b ∨ gap ≤ |truth a - truth b|)
    {a : RecoveryVertex Z} (ha : a ∈ recoveryActive pb rho) :
    recoveryComponent pb qb rho gap a =
      (recoveryActive pb rho).filter (fun b => truth a = truth b) := by
  ext b
  simp only [recoveryComponent, Finset.mem_filter]
  constructor
  · rintro ⟨hb, hpath⟩
    exact ⟨hb, recovery_path_population_equal pb qb rho gap truth herror hsep hpath⟩
  · rintro ⟨hb, heq⟩
    refine ⟨hb, ?_⟩
    by_cases hab : a = b
    · subst b
      exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single
        ((recoveryEdge_iff_population_equal pb qb rho gap truth herror hsep
          ha hb hab).mpr heq)

-- @node: componentAverage_close_to_common_value
/-- If [a finite collection of recovery vertices is nonempty](hyp:hC) and [every vertex's
estimated value differs from a common target by less than the error tolerance](hyp:herror),
then [the average estimated value over that collection differs from the target by less
than the same tolerance](goal). -/
lemma componentAverage_close_to_common_value (pb qb : Z → ℝ)
    (C : Finset (RecoveryVertex Z)) (hC : C.Nonempty) (t eps : ℝ)
    (herror : ∀ v ∈ C, |vertexValue pb qb v - t| < eps) :
    |componentAverage pb qb C - t| < eps := by
  have hc : (0 : ℝ) < C.card := by exact_mod_cast hC.card_pos
  have hid : componentAverage pb qb C - t =
      (C.card : ℝ)⁻¹ * ∑ v ∈ C, (vertexValue pb qb v - t) := by
    rw [componentAverage, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    field_simp
  rw [hid, abs_mul, abs_of_nonneg (inv_nonneg.mpr hc.le)]
  obtain ⟨v, hv⟩ := hC
  calc
    _ ≤ (C.card : ℝ)⁻¹ * ∑ v ∈ C, |vertexValue pb qb v - t| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ < (C.card : ℝ)⁻¹ * ∑ _v ∈ C, eps :=
      mul_lt_mul_of_pos_left
        (Finset.sum_lt_sum (fun v hv => (herror v hv).le) ⟨v, hv, herror v hv⟩)
        (inv_pos.mpr hc)
    _ = eps := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]

-- @node: recoveryComponent_average_close
/-- If [active vertices have estimation errors smaller than one quarter of the gap](hyp:herror),
[their population values are equal or at least the gap apart](hyp:hsep), and [the chosen
vertex is active](hyp:ha), then [the average estimated value of its recovered component
is within one quarter of the gap of its population value](goal). -/
lemma recoveryComponent_average_close (pb qb : Z → ℝ)
    (rho gap : ℝ) (truth : RecoveryVertex Z → ℝ)
    (herror : ∀ v ∈ recoveryActive pb rho,
      |vertexValue pb qb v - truth v| < gap / 4)
    (hsep : ∀ a ∈ recoveryActive pb rho, ∀ b ∈ recoveryActive pb rho,
      truth a = truth b ∨ gap ≤ |truth a - truth b|)
    {a : RecoveryVertex Z} (ha : a ∈ recoveryActive pb rho) :
    |componentAverage pb qb (recoveryComponent pb qb rho gap a) - truth a| < gap / 4 := by
  have heq := recoveryComponent_eq_population_class pb qb rho gap truth herror hsep ha
  have hmem : a ∈ recoveryComponent pb qb rho gap a := by
    rw [heq]
    exact Finset.mem_filter.mpr ⟨ha, rfl⟩
  apply componentAverage_close_to_common_value pb qb _ ⟨a, hmem⟩
  intro b hb
  rw [heq] at hb
  obtain ⟨hb, hab⟩ := Finset.mem_filter.mp hb
  rw [hab]
  exact herror b hb

-- @node: recoveryComponent_average_order
/-- Suppose [active vertices have estimation errors smaller than one quarter of the gap](hyp:herror)
and [their population values are equal or at least the gap apart](hyp:hsep). If [the first
vertex is active](hyp:ha), [the second vertex is active](hyp:hb), and [the second population
value exceeds the first by at least the gap](hyp:hab), then [the first recovered component's
average estimated value is strictly below the second's](goal). -/
lemma recoveryComponent_average_order (pb qb : Z → ℝ)
    (rho gap : ℝ) (truth : RecoveryVertex Z → ℝ)
    (herror : ∀ v ∈ recoveryActive pb rho,
      |vertexValue pb qb v - truth v| < gap / 4)
    (hsep : ∀ a ∈ recoveryActive pb rho, ∀ b ∈ recoveryActive pb rho,
      truth a = truth b ∨ gap ≤ |truth a - truth b|)
    {a b : RecoveryVertex Z} (ha : a ∈ recoveryActive pb rho)
    (hb : b ∈ recoveryActive pb rho) (hab : truth a + gap ≤ truth b) :
    componentAverage pb qb (recoveryComponent pb qb rho gap a) <
      componentAverage pb qb (recoveryComponent pb qb rho gap b) := by
  have hca := recoveryComponent_average_close pb qb rho gap truth herror hsep ha
  have hcb := recoveryComponent_average_close pb qb rho gap truth herror hsep hb
  have hg : 0 < gap := by
    have hn := abs_nonneg (vertexValue pb qb a - truth a)
    linarith [herror a ha]
  have hca' := (abs_lt.mp hca).2
  have hcb' := (abs_lt.mp hcb).1
  linarith

-- The structural-zero class is removed before the marginal-level gap graph.
-- @node: recoveryComponent_average_order_iff
/-- Suppose [active vertices have estimation errors smaller than one quarter of the gap](hyp:herror)
and [their population values are equal or at least the gap apart](hyp:hsep). For [an active
first vertex](hyp:ha) and [an active second vertex](hyp:hb), [the first recovered component's
average estimated value is strictly below the second's exactly when the first population
value is strictly below the second's](goal). -/
lemma recoveryComponent_average_order_iff (pb qb : Z → ℝ)
    (rho gap : ℝ) (truth : RecoveryVertex Z → ℝ)
    (herror : ∀ v ∈ recoveryActive pb rho,
      |vertexValue pb qb v - truth v| < gap / 4)
    (hsep : ∀ a ∈ recoveryActive pb rho, ∀ b ∈ recoveryActive pb rho,
      truth a = truth b ∨ gap ≤ |truth a - truth b|)
    {a b : RecoveryVertex Z} (ha : a ∈ recoveryActive pb rho)
    (hb : b ∈ recoveryActive pb rho) :
    componentAverage pb qb (recoveryComponent pb qb rho gap a) <
      componentAverage pb qb (recoveryComponent pb qb rho gap b) ↔
        truth a < truth b := by
  have hforward {v w : RecoveryVertex Z}
      (hv : v ∈ recoveryActive pb rho) (hw : w ∈ recoveryActive pb rho)
      (hlt : truth v < truth w) :
      componentAverage pb qb (recoveryComponent pb qb rho gap v) <
        componentAverage pb qb (recoveryComponent pb qb rho gap w) := by
    have hs := hsep v hv w hw
    rcases hs with he | hs
    · exact False.elim (hlt.ne he)
    · rw [abs_of_neg (sub_neg.mpr hlt)] at hs
      exact recoveryComponent_average_order pb qb rho gap truth herror hsep hv hw
        (by linarith)
  constructor
  · intro hlt
    rcases lt_trichotomy (truth a) (truth b) with hab | hab | hab
    · exact hab
    · have hclasses : recoveryComponent pb qb rho gap a =
          recoveryComponent pb qb rho gap b := by
        rw [recoveryComponent_eq_population_class pb qb rho gap truth herror hsep ha,
          recoveryComponent_eq_population_class pb qb rho gap truth herror hsep hb, hab]
      rw [hclasses] at hlt
      exact False.elim (lt_irrefl _ hlt)
    · exact False.elim (lt_asymm hlt (hforward hb ha hab))
  · exact hforward ha hb

-- @node: recoveryActive_eq_population_nonzero
/-- If [every zero population baseline propensity has an estimated value at or below
the threshold](hyp:hzero) and [every nonzero population baseline propensity has an estimate
strictly above the threshold](hyp:hpositive), then [the active recovery set consists of
all policy vertices and exactly those baseline vertices with nonzero population propensity](goal). -/
lemma recoveryActive_eq_population_nonzero (pb : Z → ℝ) (p : Z → ℝ)
    (rho : ℝ)
    (hzero : ∀ z, p z = 0 → pb z ≤ rho)
    (hpositive : ∀ z, p z ≠ 0 → rho < pb z) :
    recoveryActive pb rho = Finset.univ.filter (fun v => v.1 = true ∨ p v.2 ≠ 0) := by
  ext v
  simp only [recoveryActive, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (hv | hv)
    · exact Or.inl hv
    · exact Or.inr (fun hz => (not_lt_of_ge (hzero v.2 hz)) hv)
  · rintro (hv | hv)
    · exact Or.inl hv
    · exact Or.inr (hpositive v.2 hv)

end Papers.TbsPrteOptimalTransport
