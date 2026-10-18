module
public import Papers.TbsPrteOptimalTransport.Helpers.Canonical
/-! Disintegration shared proof obligations. -/
public section
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)

-- @node: canonical_version_unique
/-- If [each measure in the first family is finite](hyp:hF), [each measure in the second
family is finite](hyp:hG), [the first family's mass on every measurable set varies
continuously with the index](hyp:hcF), [the second family has the same continuity
property](hyp:hcG), and [the two families agree almost everywhere under the indexing
probability law](hyp:heq), then [they agree at every index whose every open neighborhood
has positive probability](goal). -/
lemma canonical_version_unique (rho : Measure ℝ) [IsProbabilityMeasure rho]
    (F G : ℝ → Measure ℝ) (hF : ∀ p, IsFiniteMeasure (F p)) (hG : ∀ p, IsFiniteMeasure (G p))
    (hcF : ∀ A : Set ℝ, MeasurableSet A → Continuous (fun p => (F p A).toReal))
    (hcG : ∀ A : Set ℝ, MeasurableSet A → Continuous (fun p => (G p A).toReal))
    (heq : F =ᵐ[rho] G) :
    ∀ p, (∀ O : Set ℝ, IsOpen O → p ∈ O → 0 < rho O) → F p = G p := by
  intro p hp
  apply Measure.ext
  intro A hA
  letI := hF p
  letI := hG p
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  by_contra hne
  let O := {q : ℝ | (F q A).toReal ≠ (G q A).toReal}
  have hO : IsOpen O := isClosed_eq (hcF A hA) (hcG A hA) |>.isOpen_compl
  have hz : rho O = 0 := by
    apply measure_mono_null (t := {q | F q ≠ G q})
    · intro q hq he
      exact hq (congrArg (fun μ : Measure ℝ => (μ A).toReal) he)
    · exact ae_iff.mp heq
  exact (ne_of_gt (hp O hO hne)) hz
-- @node: feasible_components_cartesian
/-- [The feasible values of the treatment-effect objective are exactly all differences
between a feasible treated objective value and a feasible untreated objective value](goal). -/
lemma feasible_components_cartesian (obs : ObservedTransportData X Z) (om : X → ℝ → ℝ) :
    ccotValueSet obs om = {v | ∃ a ∈ treatedValueSet obs om,
      ∃ b ∈ untreatedValueSet obs om, v = a-b} := by
  ext v
  constructor
  · rintro ⟨pi0, pi1, h, rfl⟩
    have h0 := h.support pi0 (by simp)
    have h1 := h.support pi1 (by simp)
    exact ⟨thetaComp om pi1, ⟨pi1, ⟨h1.1, h1.2, h.marginal.2, h.treated⟩, rfl⟩,
      thetaComp om pi0, ⟨pi0, h0.1, h0.2, h.marginal.1, h.untreated, rfl⟩, rfl⟩
  · rintro ⟨a, ⟨pi1, h1, rfl⟩, b, ⟨pi0, h0prob, h0support, h0marg, h0compat, rfl⟩, rfl⟩
    refine ⟨pi0, pi1, ?_, rfl⟩
    exact ⟨(by
      intro pi hpi
      simp only [mem_insert_iff, mem_singleton_iff] at hpi
      rcases hpi with rfl | rfl
      · exact ⟨h0prob, h0support⟩
      · exact ⟨h1.1, h1.2.1⟩), h1.2.2.2, h0compat,
      ⟨h0marg, h1.2.2.1⟩⟩
-- @node: target_interval_endpoints
/-- If [the treated lower endpoint is the least feasible treated value](hyp:hl1),
[the treated upper endpoint is the greatest feasible treated value](hyp:hu1),
[the untreated lower endpoint is the least feasible untreated value](hyp:hl0), and
[the untreated upper endpoint is the greatest feasible untreated value](hyp:hu0), then
[the least feasible treatment-effect value is the treated lower endpoint minus the
untreated upper endpoint, and the greatest is the treated upper endpoint minus the
untreated lower endpoint](goal). -/
lemma target_interval_endpoints (obs : ObservedTransportData X Z) (om : X → ℝ → ℝ)
    (hl1 : IsLeast (treatedValueSet obs om) (thetaLower1 obs om))
    (hu1 : IsGreatest (treatedValueSet obs om) (thetaUpper1 obs om))
    (hl0 : IsLeast (untreatedValueSet obs om) (thetaLower0 obs om))
    (hu0 : IsGreatest (untreatedValueSet obs om) (thetaUpper0 obs om)) :
    IsLeast (ccotValueSet obs om) (thetaLower1 obs om - thetaUpper0 obs om) ∧
    IsGreatest (ccotValueSet obs om) (thetaUpper1 obs om - thetaLower0 obs om) := by
  rw [feasible_components_cartesian]
  constructor
  · refine ⟨⟨thetaLower1 obs om, hl1.1, thetaUpper0 obs om, hu0.1, rfl⟩, ?_⟩
    rintro v ⟨a, ha, b, hb, rfl⟩
    exact sub_le_sub (hl1.2 ha) (hu0.2 hb)
  · refine ⟨⟨thetaUpper1 obs om, hu1.1, thetaLower0 obs om, hl0.1, rfl⟩, ?_⟩
    rintro v ⟨a, ha, b, hb, rfl⟩
    exact sub_le_sub (hu1.2 ha) (hl0.2 hb)

end Papers.TbsPrteOptimalTransport
