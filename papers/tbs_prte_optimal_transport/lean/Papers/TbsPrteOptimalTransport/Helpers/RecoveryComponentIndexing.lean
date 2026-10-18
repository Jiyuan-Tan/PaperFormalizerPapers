module
public import Papers.TbsPrteOptimalTransport.Helpers.LevelGraphRecovery
/-! Population equality classes in the sorted recovery-component list.
These lemmas connect the gap graph to the finite list used to index recovered
baseline and policy levels. Sorting preserves exactly the population classes. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false

namespace Papers.TbsPrteOptimalTransport
open Set
open scoped Classical

universe v
variable {Z : Type v} [Fintype Z] [DecidableEq Z]

-- @node: recoveryComponent_eq_iff_population_value_eq
/-- If [every active vertex has fitted error smaller than one quarter of the gap](hyp:herror) and [any two active vertices have equal population values or values separated by at least the gap](hyp:hsep), then for [two active vertices](hyp:ha,hb), [their recovery components are equal if and only if their population values are equal](goal). -/
lemma recoveryComponent_eq_iff_population_value_eq (pb qb : Z → ℝ)
    (rho gap : ℝ) (truth : RecoveryVertex Z → ℝ)
    (herror : ∀ v ∈ recoveryActive pb rho,
      |vertexValue pb qb v - truth v| < gap / 4)
    (hsep : ∀ a ∈ recoveryActive pb rho, ∀ b ∈ recoveryActive pb rho,
      truth a = truth b ∨ gap ≤ |truth a - truth b|)
    {a b : RecoveryVertex Z} (ha : a ∈ recoveryActive pb rho)
    (hb : b ∈ recoveryActive pb rho) :
    recoveryComponent pb qb rho gap a = recoveryComponent pb qb rho gap b ↔
      truth a = truth b := by
  have hself : a ∈ recoveryComponent pb qb rho gap a := by
    rw [recoveryComponent_eq_population_class pb qb rho gap truth herror hsep ha]
    exact Finset.mem_filter.mpr ⟨ha, rfl⟩
  constructor
  · intro heq
    rw [heq, recoveryComponent_eq_population_class pb qb rho gap truth herror hsep hb]
      at hself
    exact (Finset.mem_filter.mp hself).2.symm
  · intro heq
    rw [recoveryComponent_eq_population_class pb qb rho gap truth herror hsep ha,
      recoveryComponent_eq_population_class pb qb rho gap truth herror hsep hb, heq]

-- @node: recoveryComponent_disjoint_of_population_value_ne
/-- If [every active vertex has fitted error smaller than one quarter of the gap](hyp:herror) and [any two active population values are equal or separated by at least the gap](hyp:hsep), take [two active vertices](hyp:ha,hb) with [different population values](hyp:hab). Then [their recovery components are disjoint](goal). -/
lemma recoveryComponent_disjoint_of_population_value_ne (pb qb : Z → ℝ)
    (rho gap : ℝ) (truth : RecoveryVertex Z → ℝ)
    (herror : ∀ v ∈ recoveryActive pb rho,
      |vertexValue pb qb v - truth v| < gap / 4)
    (hsep : ∀ a ∈ recoveryActive pb rho, ∀ b ∈ recoveryActive pb rho,
      truth a = truth b ∨ gap ≤ |truth a - truth b|)
    {a b : RecoveryVertex Z} (ha : a ∈ recoveryActive pb rho)
    (hb : b ∈ recoveryActive pb rho) (hab : truth a ≠ truth b) :
    Disjoint (recoveryComponent pb qb rho gap a)
      (recoveryComponent pb qb rho gap b) := by
  rw [recoveryComponent_eq_population_class pb qb rho gap truth herror hsep ha,
    recoveryComponent_eq_population_class pb qb rho gap truth herror hsep hb]
  apply Finset.disjoint_left.mpr
  intro v hva hvb
  exact hab ((Finset.mem_filter.mp hva).2.trans (Finset.mem_filter.mp hvb).2.symm)

-- @node: mem_recoveryComponents_iff_population_class
/-- If [every active vertex has fitted error smaller than one quarter of the gap](hyp:herror) and [any two active population values are equal or separated by at least the gap](hyp:hsep), then [a finite vertex set occurs in the recovered-component list if and only if it is exactly the active vertices sharing the population value of some active vertex](goal). -/
lemma mem_recoveryComponents_iff_population_class (pb qb : Z → ℝ)
    (rho gap : ℝ) (truth : RecoveryVertex Z → ℝ)
    (herror : ∀ v ∈ recoveryActive pb rho,
      |vertexValue pb qb v - truth v| < gap / 4)
    (hsep : ∀ a ∈ recoveryActive pb rho, ∀ b ∈ recoveryActive pb rho,
      truth a = truth b ∨ gap ≤ |truth a - truth b|)
    (C : Finset (RecoveryVertex Z)) :
    C ∈ recoveryComponents pb qb rho gap ↔
      ∃ a ∈ recoveryActive pb rho,
        (recoveryActive pb rho).filter (fun b => truth a = truth b) = C := by
  simp only [recoveryComponents, List.mem_mergeSort, Finset.mem_toList, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, heq⟩
    refine ⟨a, ha, ?_⟩
    rw [← recoveryComponent_eq_population_class pb qb rho gap truth herror hsep ha]
    exact heq
  · rintro ⟨a, ha, heq⟩
    refine ⟨a, ha, ?_⟩
    rw [recoveryComponent_eq_population_class pb qb rho gap truth herror hsep ha]
    exact heq

-- @node: recoveryComponents_population_class_nonempty
/-- If [every active vertex has fitted error smaller than one quarter of the gap](hyp:herror), [any two active population values are equal or separated by at least the gap](hyp:hsep), and [a finite set occurs in the recovered-component list](hyp:hC), then [that set is nonempty and contains a vertex whose population value equals that of every member](goal). -/
lemma recoveryComponents_population_class_nonempty (pb qb : Z → ℝ)
    (rho gap : ℝ) (truth : RecoveryVertex Z → ℝ)
    (herror : ∀ v ∈ recoveryActive pb rho,
      |vertexValue pb qb v - truth v| < gap / 4)
    (hsep : ∀ a ∈ recoveryActive pb rho, ∀ b ∈ recoveryActive pb rho,
      truth a = truth b ∨ gap ≤ |truth a - truth b|)
    {C : Finset (RecoveryVertex Z)} (hC : C ∈ recoveryComponents pb qb rho gap) :
    C.Nonempty ∧ ∃ a ∈ C, ∀ b ∈ C, truth a = truth b := by
  obtain ⟨a, ha, rfl⟩ :=
    (mem_recoveryComponents_iff_population_class pb qb rho gap truth herror hsep C).mp hC
  have hmem : a ∈ (recoveryActive pb rho).filter (fun b => truth a = truth b) :=
    Finset.mem_filter.mpr ⟨ha, rfl⟩
  exact ⟨⟨a, hmem⟩, a, hmem, fun b hb => (Finset.mem_filter.mp hb).2⟩

-- @node: recoveryComponent_average_le_iff
/-- If [every active vertex has fitted error smaller than one quarter of the gap](hyp:herror) and [any two active population values are equal or separated by at least the gap](hyp:hsep), then for [two active vertices](hyp:ha,hb), [the fitted average of the first recovery component is no greater than that of the second if and only if the first population value is no greater than the second](goal). -/
lemma recoveryComponent_average_le_iff (pb qb : Z → ℝ)
    (rho gap : ℝ) (truth : RecoveryVertex Z → ℝ)
    (herror : ∀ v ∈ recoveryActive pb rho,
      |vertexValue pb qb v - truth v| < gap / 4)
    (hsep : ∀ a ∈ recoveryActive pb rho, ∀ b ∈ recoveryActive pb rho,
      truth a = truth b ∨ gap ≤ |truth a - truth b|)
    {a b : RecoveryVertex Z} (ha : a ∈ recoveryActive pb rho)
    (hb : b ∈ recoveryActive pb rho) :
    componentAverage pb qb (recoveryComponent pb qb rho gap a) ≤
      componentAverage pb qb (recoveryComponent pb qb rho gap b) ↔
        truth a ≤ truth b := by
  simpa only [not_lt] using
    (not_congr (recoveryComponent_average_order_iff pb qb rho gap truth herror hsep hb ha))

-- @node: recoveryComponents_pairwise_average_le
/-- [The recovered-component list is ordered by nondecreasing fitted component averages: each earlier component has average no greater than each later component](goal). -/
lemma recoveryComponents_pairwise_average_le (pb qb : Z → ℝ) (rho gap : ℝ) :
    (recoveryComponents pb qb rho gap).Pairwise
      (fun C D => componentAverage pb qb C ≤ componentAverage pb qb D) := by
  unfold recoveryComponents
  have hs := List.pairwise_mergeSort
    (le := fun C D : Finset (RecoveryVertex Z) =>
      decide (componentAverage pb qb C ≤ componentAverage pb qb D))
    (by intro a b c hab hbc; simpa using le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
    (by intro a b; simpa using le_total (componentAverage pb qb a) (componentAverage pb qb b))
    ((recoveryActive pb rho).image (recoveryComponent pb qb rho gap)).toList
  simpa only [decide_eq_true_eq] using hs

-- Both fitted marginal vectors yield the same ordered component list.
-- In particular every baseline/policy projection and list index agrees.
-- @node: recoveryComponents_eq_of_common_population_classes
/-- Suppose [two fitted marginal systems select the same active vertices](hyp:hactive), [the first system's fitted errors are smaller than one quarter of the gap on its active vertices](hyp:herror), [the second system satisfies the same error bound relative to the same population values](hyp:herror'), and [any two active population values are equal or separated by at least the gap](hyp:hsep). Then [the two ordered lists of recovered components are equal](goal). -/
lemma recoveryComponents_eq_of_common_population_classes
    (pb qb pb' qb' : Z → ℝ) (rho rho' gap : ℝ)
    (truth : RecoveryVertex Z → ℝ)
    (hactive : recoveryActive pb rho = recoveryActive pb' rho')
    (herror : ∀ v ∈ recoveryActive pb rho,
      |vertexValue pb qb v - truth v| < gap / 4)
    (herror' : ∀ v ∈ recoveryActive pb' rho',
      |vertexValue pb' qb' v - truth v| < gap / 4)
    (hsep : ∀ a ∈ recoveryActive pb rho, ∀ b ∈ recoveryActive pb rho,
      truth a = truth b ∨ gap ≤ |truth a - truth b|) :
    recoveryComponents pb qb rho gap = recoveryComponents pb' qb' rho' gap := by
  have hsep' : ∀ a ∈ recoveryActive pb' rho', ∀ b ∈ recoveryActive pb' rho',
      truth a = truth b ∨ gap ≤ |truth a - truth b| := by
    simpa only [← hactive] using hsep
  have hmem (C : Finset (RecoveryVertex Z)) :
      C ∈ recoveryComponents pb qb rho gap ↔ C ∈ recoveryComponents pb' qb' rho' gap := by
    rw [mem_recoveryComponents_iff_population_class pb qb rho gap truth herror hsep,
      mem_recoveryComponents_iff_population_class pb' qb' rho' gap truth herror' hsep',
      ← hactive]
  have hclass (a : RecoveryVertex Z) (ha : a ∈ recoveryActive pb rho) :
      recoveryComponent pb qb rho gap a = recoveryComponent pb' qb' rho' gap a := by
    rw [recoveryComponent_eq_population_class pb qb rho gap truth herror hsep ha,
      recoveryComponent_eq_population_class pb' qb' rho' gap truth herror' hsep'
        (hactive ▸ ha), ← hactive]
  have hnodup (p q : Z → ℝ) (r : ℝ) :
      (recoveryComponents p q r gap).Nodup := by
    unfold recoveryComponents
    exact (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)
  have hperm := (List.perm_ext_iff_of_nodup
    (hnodup pb qb rho) (hnodup pb' qb' rho')).mpr hmem
  apply List.Perm.eq_of_pairwise (le := fun C D =>
    componentAverage pb qb C ≤ componentAverage pb qb D) _
    (recoveryComponents_pairwise_average_le pb qb rho gap) _ hperm
  · intro C D hC hD hCD hDC
    obtain ⟨a, ha, hCa⟩ :=
      (mem_recoveryComponents_iff_population_class pb qb rho gap truth herror hsep C).mp hC
    obtain ⟨b, hb, hDb⟩ :=
      (mem_recoveryComponents_iff_population_class pb qb rho gap truth herror hsep D).mp
        ((hmem D).mpr hD)
    have hCa' : recoveryComponent pb qb rho gap a = C :=
      (recoveryComponent_eq_population_class pb qb rho gap truth herror hsep ha).trans hCa
    have hDb' : recoveryComponent pb qb rho gap b = D :=
      (recoveryComponent_eq_population_class pb qb rho gap truth herror hsep hb).trans hDb
    rw [← hCa', ← hDb'] at hCD hDC ⊢
    apply (recoveryComponent_eq_iff_population_value_eq pb qb rho gap truth herror hsep ha hb).mpr
    exact le_antisymm
      ((recoveryComponent_average_le_iff pb qb rho gap truth herror hsep ha hb).mp hCD)
      ((recoveryComponent_average_le_iff pb qb rho gap truth herror hsep hb ha).mp hDC)
  · apply List.Pairwise.imp_of_mem _ (recoveryComponents_pairwise_average_le pb' qb' rho' gap)
    intro C D hC hD hCD
    obtain ⟨a, ha, hCa⟩ :=
      (mem_recoveryComponents_iff_population_class pb qb rho gap truth herror hsep C).mp
        ((hmem C).mpr hC)
    obtain ⟨b, hb, hDb⟩ :=
      (mem_recoveryComponents_iff_population_class pb qb rho gap truth herror hsep D).mp
        ((hmem D).mpr hD)
    have hCa' : recoveryComponent pb qb rho gap a = C :=
      (recoveryComponent_eq_population_class pb qb rho gap truth herror hsep ha).trans hCa
    have hDb' : recoveryComponent pb qb rho gap b = D :=
      (recoveryComponent_eq_population_class pb qb rho gap truth herror hsep hb).trans hDb
    rw [← hCa', ← hDb'] at hCD ⊢
    apply (recoveryComponent_average_le_iff pb qb rho gap truth herror hsep ha hb).mpr
    rw [hclass a ha, hclass b hb] at hCD
    exact (recoveryComponent_average_le_iff pb' qb' rho' gap truth herror' hsep'
      (hactive ▸ ha) (hactive ▸ hb)).mp hCD

-- The baseline projection uses only the ordered components and the zero class;
-- fitted numerical component averages need not agree.
-- @node: recoverLevelsAt_baseline_labels_stable
/-- Suppose [two fitted marginal systems select the same active vertices](hyp:hactive), [the first system's fitted errors are smaller than one quarter of the gap on its active vertices](hyp:herror), [the second system satisfies that bound relative to the same population values](hyp:herror'), and [any two active population values are equal or separated by at least the gap](hyp:hsep). Then [the two recovered baseline level counts are equal, and their indexed baseline classes agree at every index](goal). -/
lemma recoverLevelsAt_baseline_labels_stable {X : Type v}
    (pb qb pb' qb' : Z → ℝ) (rho rho' gap : ℝ)
    (truth : RecoveryVertex Z → ℝ)
    (hactive : recoveryActive pb rho = recoveryActive pb' rho')
    (herror : ∀ v ∈ recoveryActive pb rho,
      |vertexValue pb qb v - truth v| < gap / 4)
    (herror' : ∀ v ∈ recoveryActive pb' rho',
      |vertexValue pb' qb' v - truth v| < gap / 4)
    (hsep : ∀ a ∈ recoveryActive pb rho, ∀ b ∈ recoveryActive pb rho,
      truth a = truth b ∨ gap ≤ |truth a - truth b|) :
    (recoverLevelsAt pb qb rho gap : LevelData Z X).K =
      (recoverLevelsAt pb' qb' rho' gap : LevelData Z X).K ∧
    ∀ k, (recoverLevelsAt pb qb rho gap : LevelData Z X).S k =
      (recoverLevelsAt pb' qb' rho' gap : LevelData Z X).S k := by
  have hCs := recoveryComponents_eq_of_common_population_classes pb qb pb' qb'
    rho rho' gap truth hactive herror herror' hsep
  constructor
  · simp only [recoverLevelsAt, hCs]
  · intro k
    by_cases hk : k = 0
    · subst k
      change Finset.univ.filter (fun z => pb z ≤ rho) =
        Finset.univ.filter (fun z => pb' z ≤ rho')
      ext z
      have hz : (false, z) ∈ recoveryActive pb rho ↔
          (false, z) ∈ recoveryActive pb' rho' := by rw [hactive]
      simp only [recoveryActive, Finset.mem_filter, Finset.mem_univ,
        Bool.false_eq_true, false_or, true_and] at hz
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using not_congr hz
    · simp only [recoverLevelsAt, if_neg hk, hCs]

end Papers.TbsPrteOptimalTransport
