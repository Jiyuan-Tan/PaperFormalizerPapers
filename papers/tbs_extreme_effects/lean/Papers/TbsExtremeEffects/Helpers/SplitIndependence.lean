module
public import Papers.TbsExtremeEffects.Helpers.RelabelledIID

/-! Joint-law transport and independence for the sample split. -/

public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {q d : ℕ}

/-- If [the fiber transformation is measurable](hyp:hT) and [it preserves the second distribution at every first-coordinate value](hyp:hfiber), then [applying it to the second coordinate of independent draws leaves their product distribution unchanged](goal). -/
-- @node: split_fiber_map
lemma split_fiber_map {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (T : A × B → B) (hT : Measurable T)
    (hfiber : ∀ a, ν.map (fun b => T (a, b)) = ν) :
    (μ.prod ν).map (fun z => (z.1, T z)) = μ.prod ν := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_fst.prodMk hT) hs,
    Measure.prod_apply ((measurable_fst.prodMk hT) hs), Measure.prod_apply hs]
  apply lintegral_congr
  intro a
  have hsection : MeasurableSet (Prod.mk a ⁻¹' s) := measurable_prodMk_left hs
  have hm : Measurable (fun b => T (a, b)) := hT.comp measurable_prodMk_left
  have h := congrArg (fun ρ : Measure B => ρ (Prod.mk a ⁻¹' s)) (hfiber a)
  rw [Measure.map_apply hm hsection] at h
  exact h

/-- If [the sample size is even](hyp:hn) and [sampling is iid](hyp:hiid), then [the relabelled observations have a joint law equal to the product of the split-and-auxiliary law and iid model observation laws](goal). -/
-- @node: split_relabelled_joint_law
lemma split_relabelled_joint_law (M : ExtremeModel q d) (E : NeteExperiment M)
    (n : ℕ) (hn : EvenSampleSize n) (hiid : IIDSampling E n) :
    E.P.map (fun w => ((E.trainSet n w, E.aux w), obs E n w)) =
      (E.P.map (fun w => (E.trainSet n w, E.aux w))).prod
        (Measure.pi (fun _ : Fin n => M.mu.map (observation M))) := by
  let ν := M.mu.map (observation M)
  have hobs : Measurable (observation M) := by
    exact M.measurable_X.prodMk (M.measurable_D.prodMk (M.measurable_Y.prodMk M.measurable_U))
  let : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hobs.aemeasurable
  let S := fun w => (E.trainSet n w, E.aux w)
  let Z := fun w (i : Fin n) => E.Zraw i.val w
  have hS : Measurable S := (E.measurable_train n).prodMk E.measurable_aux
  let : IsProbabilityMeasure (E.P.map S) := Measure.isProbabilityMeasure_map hS.aemeasurable
  have hZ : Measurable Z := by
    exact measurable_pi_lambda _ (fun i => E.measurable_raw i.val)
  have hraw := hiid.1.map_fun_eq_pi_map (fun i : Fin n => (E.measurable_raw i.val).aemeasurable)
  simp_rw [hiid.2] at hraw
  have hpair := (E.split_aux_independent n hn).map_prod_eq_prod_map_map
    hS.aemeasurable hZ.aemeasurable
  rw [hraw] at hpair
  let T : (Finset (Fin n) × E.Aux) × (Fin n → Obs q d) → Fin n → Obs q d :=
    fun z i => z.2 (splitPermutation z.1.1 i)
  have hT : Measurable T :=
    (measurable_randomPermutation (B := Obs q d) (@splitPermutation n)).comp
      ((measurable_fst.fst).prodMk measurable_snd)
  have hfiber (a : Finset (Fin n) × E.Aux) :
      (Measure.pi (fun _ : Fin n => ν)).map (fun b => T (a, b)) =
        Measure.pi (fun _ : Fin n => ν) := by
    have h := (measurePreserving_piCongrLeft (fun _ : Fin n => ν)
      (splitPermutation a.1).symm).map_eq
    convert h using 1
    congr 1
    funext b i
    simp [T, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  have hf := split_fiber_map (E.P.map S) (Measure.pi (fun _ : Fin n => ν)) T hT hfiber
  rw [← hpair, Measure.map_map (measurable_fst.prodMk hT) (hS.prodMk hZ)] at hf
  rw [hpair] at hf
  convert hf using 1
  congr 1
  funext w
  congr 1
  funext i
  exact relabelledObs_eq_permutation E.Zraw E.trainSet n w i

/-- If [both maps are measurable](hyp:hf,hg) and [their joint law is the product of the supplied marginal laws](hyp:hlaw), then [the two maps are independent](goal). -/
-- @node: split_indep_of_product_law
lemma split_indep_of_product_law {W A B : Type*} [MeasurableSpace W]
    [MeasurableSpace A] [MeasurableSpace B] (P : Measure W) [IsProbabilityMeasure P]
    (f : W → A) (g : W → B) (hf : Measurable f) (hg : Measurable g)
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hlaw : P.map (fun w => (f w, g w)) = μ.prod ν) : IndepFun f g P := by
  have hfst := congrArg (fun ρ : Measure (A × B) => ρ.map Prod.fst) hlaw
  have hsnd := congrArg (fun ρ : Measure (A × B) => ρ.map Prod.snd) hlaw
  rw [Measure.map_map measurable_fst (hf.prodMk hg)] at hfst
  rw [Measure.map_map measurable_snd (hf.prodMk hg)] at hsnd
  simp only [Measure.map_fst_prod, Measure.map_snd_prod, measure_univ, one_smul,
    Function.comp_def] at hfst hsnd
  apply (indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable).mpr
  rw [hfst, hsnd]
  exact hlaw

/-- If [the source and observation maps are measurable](hyp:hS,hZ), [the two post-processing maps are measurable](hyp:hT,hV), [the source and observations are independent](hyp:hSZ), and [the post-processed observation components are independent under the observation law](hyp:hTV), then [the source paired with one component is independent of the other component](goal). -/
-- @node: split_pair_indep
lemma split_pair_indep {W A B C D : Type*} [MeasurableSpace W] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (P : Measure W) [IsProbabilityMeasure P] (S : W → A) (Z : W → B)
    (T : B → C) (V : B → D) (hS : Measurable S) (hZ : Measurable Z)
    (hT : Measurable T) (hV : Measurable V) (hSZ : IndepFun S Z P)
    (hTV : IndepFun T V (P.map Z)) :
    IndepFun (fun w => (S w, T (Z w))) (fun w => V (Z w)) P := by
  let : IsProbabilityMeasure (P.map S) := Measure.isProbabilityMeasure_map hS.aemeasurable
  let : IsProbabilityMeasure (P.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  let : IsProbabilityMeasure ((P.map Z).map T) := Measure.isProbabilityMeasure_map hT.aemeasurable
  let : IsProbabilityMeasure ((P.map Z).map V) := Measure.isProbabilityMeasure_map hV.aemeasurable
  have h1 := hSZ.map_prod_eq_prod_map_map hS.aemeasurable hZ.aemeasurable
  have h2 := hTV.map_prod_eq_prod_map_map hT.aemeasurable hV.aemeasurable
  have h3 : P.map (fun w => (S w, (T (Z w), V (Z w)))) =
      (P.map S).prod (((P.map Z).map T).prod ((P.map Z).map V)) := by
    calc
      _ = (P.map (fun w => (S w, Z w))).map
          (fun z => (z.1, (T z.2, V z.2))) :=
        (Measure.map_map (measurable_fst.prodMk ((hT.comp measurable_snd).prodMk
          (hV.comp measurable_snd))) (hS.prodMk hZ)).symm
      _ = _ := by
        rw [h1]
        change ((P.map S).prod (P.map Z)).map (Prod.map id (fun b => (T b, V b))) = _
        rw [← Measure.map_prod_map _ _ measurable_id (hT.prodMk hV), h2, Measure.map_id]
  have hlaw : P.map (fun w => ((S w, T (Z w)), V (Z w))) =
      ((P.map S).prod ((P.map Z).map T)).prod ((P.map Z).map V) := by
    apply MeasurableEquiv.prodAssoc.map_measurableEquiv_injective
    have hm : Measurable (fun w => ((S w, T (Z w)), V (Z w))) := by fun_prop
    rw [Measure.map_map (MeasurableEquiv.measurable _) hm, Measure.prodAssoc_prod]
    exact h3
  exact split_indep_of_product_law P _ _ (hS.prodMk (hT.comp hZ)) (hV.comp hZ)
    _ _ hlaw

/-- If [each coordinate map is measurable](hyp:hf) and [the coordinate family is independent](hyp:hind), then [the family masked to a finite index set is independent of the complementary masked family](goal). -/
-- @node: split_mask_indep
lemma split_mask_indep {W I B : Type*} [MeasurableSpace W] [Fintype I]
    [DecidableEq I] [MeasurableSpace B] (P : Measure W)
    (f : I → W → B) (hf : ∀ i, Measurable (f i)) (hind : iIndepFun f P)
    (S : Finset I) (b₀ : B) :
    IndepFun (fun w i => if i ∈ S then f i w else b₀)
      (fun w i => if i ∈ Sᶜ then f i w else b₀) P := by
  let T : (S → B) → I → B := fun z i => if h : i ∈ S then z ⟨i, h⟩ else b₀
  let V : (↥(Sᶜ) → B) → I → B := fun z i => if h : i ∈ Sᶜ then z ⟨i, h⟩ else b₀
  have hT : Measurable T := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : i ∈ S
    · simpa only [T, dif_pos hi] using (measurable_pi_apply (⟨i, hi⟩ : S))
    · simpa only [T, dif_neg hi] using (measurable_const : Measurable (fun _ : S → B => b₀))
  have hV : Measurable V := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : i ∈ Sᶜ
    · simpa only [V, dif_pos hi] using (measurable_pi_apply (⟨i, hi⟩ : ↥(Sᶜ)))
    · simpa only [V, dif_neg hi] using (measurable_const : Measurable (fun _ : ↥(Sᶜ) → B => b₀))
  have h := (hind.indepFun_finset S Sᶜ disjoint_compl_right hf).comp hT hV
  convert h using 1 <;> funext w i
  · by_cases hi : i ∈ S <;> simp [T, hi, Function.comp_def]
  · by_cases hi : i ∈ S <;> simp [V, hi, Function.comp_def]

end Papers.TbsExtremeEffects
