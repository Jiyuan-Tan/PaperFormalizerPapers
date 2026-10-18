module
public import Papers.TbsPrteOptimalTransport.Basic
/-! Extension of a feasible joint latent law by the observed instrument kernel. -/
public section
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set
open scoped Classical
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)

/-- If [the two outcome marginals of a candidate joint law are feasible](hyp:hf),
[its resistance–covariate marginal is the product of the uniform resistance law and
the original covariate law](goal). -/
-- @node: feasible_joint_uniform_marginal
lemma feasible_joint_uniform_marginal (piT : Measure ((ℝ × X) × (ℝ × ℝ)))
    (hf : IsFeasiblePair (transportData M) (piT.map (fun a => (a.1, a.2.1)))
      (piT.map (fun a => (a.1, a.2.2)))) :
    piT.map Prod.fst = Causalean.Stat.unifOI.prod (xLaw M) := by
  have hm := hf.marginal.1
  change (piT.map (fun a => (a.1, a.2.1))).map Prod.fst = _ at hm
  rw [Measure.map_map measurable_fst (by fun_prop)] at hm
  exact hm

-- @node: feasible_joint_covariate_marginal
/-- If [the two outcome marginals of a candidate joint law are feasible](hyp:hf),
[its covariate marginal equals the original covariate law](goal). -/
lemma feasible_joint_covariate_marginal (piT : Measure ((ℝ × X) × (ℝ × ℝ)))
    (hf : IsFeasiblePair (transportData M) (piT.map (fun a => (a.1, a.2.1)))
      (piT.map (fun a => (a.1, a.2.2)))) :
    piT.map (fun a => a.1.2) = xLaw M := by
  haveI : IsProbabilityMeasure (xLaw M) :=
    Measure.isProbabilityMeasure_map M.measX.aemeasurable
  have hm := congrArg (fun ν : Measure (ℝ × X) => ν.map Prod.snd)
    (feasible_joint_uniform_marginal M piT hf)
  rw [Measure.map_map measurable_snd measurable_fst] at hm
  change piT.map (fun a => a.1.2) = (Causalean.Stat.unifOI.prod (xLaw M)).snd at hm
  rw [Measure.snd_prod] at hm
  exact hm

/-- If [the model's domains are compact and Borel](hyp:hD) and [both outcome
marginals of the candidate joint law are feasible](hyp:hf), [resistance lies in
the unit interval and both potential outcomes lie in the prescribed outcome
domain almost surely under the candidate law](goal). -/
-- @node: feasible_joint_supported
lemma feasible_joint_supported (hD : DomainsCompactBorel M)
    (piT : Measure ((ℝ × X) × (ℝ × ℝ)))
    (hf : IsFeasiblePair (transportData M) (piT.map (fun a => (a.1, a.2.1)))
      (piT.map (fun a => (a.1, a.2.2)))) :
    ∀ᵐ a ∂piT, a.1.1 ∈ Icc (0 : ℝ) 1 ∧ a.2.1 ∈ M.Yset ∧ a.2.2 ∈ M.Yset := by
  have hs : MeasurableSet {a : (ℝ × X) × ℝ |
      a.1.1 ∈ Icc (0 : ℝ) 1 ∧ a.2 ∈ M.Yset} :=
    (measurable_fst.fst measurableSet_Icc).inter
      (measurable_snd hD.1.measurableSet)
  have h0 := (hf.support (piT.map (fun a => (a.1, a.2.1))) (by simp)).2
  have h1 := (hf.support (piT.map (fun a => (a.1, a.2.2))) (by simp)).2
  have ha0 : ∀ᵐ a ∂piT, a.1.1 ∈ Icc (0 : ℝ) 1 ∧ a.2.1 ∈ M.Yset :=
    (ae_map_iff (by fun_prop) hs).mp (ae_iff.mpr h0)
  have ha1 : ∀ᵐ a ∂piT, a.1.1 ∈ Icc (0 : ℝ) 1 ∧ a.2.2 ∈ M.Yset :=
    (ae_map_iff (by fun_prop) hs).mp (ae_iff.mpr h1)
  filter_upwards [ha0, ha1] with a h0 h1
  exact ⟨h0.1, h0.2, h1.2⟩

/-- For a finite base measure and a finite conditional kernel, if [the map from
the base space to the kernel's conditioning space is measurable](hyp:hf),
[transforming the base coordinate after adjoining a draw from the kernel gives
the same joint measure as transforming the base measure first and then adjoining
that draw](goal). -/
-- @node: sharpness_map_compProd_comap
lemma sharpness_map_compProd_comap {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (ν : Measure A) [IsFiniteMeasure ν] (κ : Kernel B C) [IsFiniteKernel κ]
    (f : A → B) (hf : Measurable f) :
    (ν ⊗ₘ κ.comap f hf).map (fun a => (f a.1, a.2)) = (ν.map f) ⊗ₘ κ := by
  refine Measure.ext_prod fun {s t} hs ht => ?_
  have hmap : Measurable (fun a : A × C => (f a.1, a.2)) := by fun_prop
  rw [Measure.map_apply hmap (hs.prod ht)]
  change (ν ⊗ₘ κ.comap f hf) ((f ⁻¹' s) ×ˢ t) = _
  rw [Measure.compProd_apply_prod (hs.preimage hf) ht,
    Measure.compProd_apply_prod hs ht]
  rw [← lintegral_indicator hs, lintegral_map
    ((κ.measurable_coe ht).indicator hs) hf, ← lintegral_indicator (hs.preimage hf)]
  apply lintegral_congr
  intro a
  by_cases ha : f a ∈ s <;> simp [ha]

/-- If [the model's domains are compact and Borel](hyp:hD) and [both outcome
marginals of a candidate joint probability law are feasible](hyp:hf), [there is
an extension by the instrument that preserves the entire candidate latent law,
matches the observed instrument–covariate law, places resistance in the unit
interval and both outcomes in their prescribed domain almost surely, and is
obtained by adjoining the original instrument kernel conditional on covariates](goal). -/
-- @node: feasible_joint_instrument_extension
lemma feasible_joint_instrument_extension (hD : DomainsCompactBorel M)
    (piT : Measure ((ℝ × X) × (ℝ × ℝ))) [IsProbabilityMeasure piT]
    (hf : IsFeasiblePair (transportData M) (piT.map (fun a => (a.1, a.2.1)))
      (piT.map (fun a => (a.1, a.2.2)))) :
    ∃ P : ProbabilityMeasure (((ℝ × X) × (ℝ × ℝ)) × Z),
      P.toMeasure.map Prod.fst = piT ∧
      P.toMeasure.map (fun a => (a.2, a.1.1.2)) = zxLaw M ∧
      (∀ᵐ a ∂P.toMeasure,
        a.1.1.1 ∈ Icc (0 : ℝ) 1 ∧ a.1.2.1 ∈ M.Yset ∧ a.1.2.2 ∈ M.Yset) ∧
      P.toMeasure = piT ⊗ₘ M.instKernel.comap
        (fun a : (ℝ × X) × (ℝ × ℝ) => a.1.2) (by fun_prop) := by
  haveI := M.instKernel_markov
  let κ := M.instKernel.comap (fun a : (ℝ × X) × (ℝ × ℝ) => a.1.2)
    (by fun_prop)
  haveI : IsMarkovKernel κ := inferInstance
  let P : ProbabilityMeasure (((ℝ × X) × (ℝ × ℝ)) × Z) := ⟨piT ⊗ₘ κ, inferInstance⟩
  have hfst : P.toMeasure.map Prod.fst = piT := Measure.fst_compProd piT κ
  refine ⟨P, hfst, ?_, ?_, rfl⟩
  · have hXZ : P.toMeasure.map (fun a => (a.1.1.2, a.2)) =
        (xLaw M) ⊗ₘ M.instKernel := by
      change (piT ⊗ₘ κ).map (fun a => (a.1.1.2, a.2)) = _
      rw [sharpness_map_compProd_comap piT M.instKernel
        (fun a : (ℝ × X) × (ℝ × ℝ) => a.1.2) (by fun_prop),
        feasible_joint_covariate_marginal M piT hf]
    have hobs : (xLaw M) ⊗ₘ M.instKernel =
        M.law.toMeasure.map (fun s => (M.Xv s, M.Zv s)) := by
      change (M.law.toMeasure.map M.Xv) ⊗ₘ M.instKernel = _
      rw [Measure.compProd_congr M.instKernel_version,
        compProd_map_condDistrib M.measZ.aemeasurable]
    have he := congrArg (fun ν : Measure (X × Z) => ν.map Prod.swap) (hXZ.trans hobs)
    rw [Measure.map_map measurable_swap (by fun_prop),
      Measure.map_map measurable_swap (M.measX.prodMk M.measZ)] at he
    exact he
  · have hs := feasible_joint_supported M hD piT hf
    rw [← hfst] at hs
    exact (ae_map_iff (by fun_prop) (by
      exact (measurable_fst.fst measurableSet_Icc).inter
        ((measurable_snd.fst hD.1.measurableSet).inter
          (measurable_snd.snd hD.1.measurableSet)))).mp hs

end Papers.TbsPrteOptimalTransport
