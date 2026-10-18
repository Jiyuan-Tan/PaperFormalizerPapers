module
public import Papers.TbsExtremeEffects.Basic
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Data.List.GetD

/-! Product-law transport through the independent random split permutation. -/

@[expose] public section
namespace Papers.TbsExtremeEffects
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {q d : ℕ}

-- @node: splitOrder_length
/-- [The concatenated sorted training indices and their complement](goal) contain exactly as many positions as the full sample. -/
lemma splitOrder_length {n : ℕ} (A : Finset (Fin n)) :
    (A.sort (· ≤ ·) ++ Aᶜ.sort (· ≤ ·)).length = n := by
  simp only [List.length_append, Finset.length_sort, Finset.card_compl, Fintype.card_fin]
  exact Nat.add_sub_of_le (by simpa using Finset.card_le_univ A)

-- @node: splitOrder_nodup
/-- [The concatenated sorted training indices and their complement](goal) contain no repeated index. -/
lemma splitOrder_nodup {n : ℕ} (A : Finset (Fin n)) :
    (A.sort (· ≤ ·) ++ Aᶜ.sort (· ≤ ·)).Nodup := by
  classical
  refine List.nodup_append.mpr ⟨Finset.sort_nodup _ _, Finset.sort_nodup _ _, ?_⟩
  simp only [List.disjoint_left, Finset.mem_sort, Finset.mem_compl]
  intro i hi j hj hij
  exact hj (hij ▸ hi)

-- @node: splitOrder_mem
/-- Every sample index [appears in the concatenated sorted training indices and their complement](goal). -/
lemma splitOrder_mem {n : ℕ} (A : Finset (Fin n)) (i : Fin n) :
    i ∈ A.sort (· ≤ ·) ++ Aᶜ.sort (· ≤ ·) := by
  classical
  exact (by simpa using (Classical.em (i ∈ A)))

-- @node: splitPermutation
/-- [The split permutation](goal) sends each sample position to the corresponding position in the ordering that lists the supplied [training-index set](hyp:A) first and its complement second. -/
noncomputable def splitPermutation {n : ℕ} (A : Finset (Fin n)) : Fin n ≃ Fin n :=
  (finCongr (splitOrder_length A).symm).trans
    ((splitOrder_nodup A).getEquivOfForallMemList _ (splitOrder_mem A))

-- @node: relabelledObs_eq_permutation
/-- [The relabelled observation](goal) at a sample position is the raw observation selected by the split permutation generated from the training set. -/
lemma relabelledObs_eq_permutation {W : Type} (raw : ℕ → W → Obs q d)
    (train : (n : ℕ) → W → Finset (Fin n)) (n : ℕ) (w : W) (i : Fin n) :
    relabelledObs raw train n w i = raw (splitPermutation (train n w) i).val w := by
  unfold relabelledObs splitPermutation
  rw [List.getD_eq_getElem _ _ (by simpa [splitOrder_length] using i.isLt)]
  simp only [Equiv.trans_apply, finCongr_apply,
    List.Nodup.getEquivOfForallMemList_apply, List.get_eq_getElem, List.getElem_map]
  rfl

-- @node: randomPermutation
/-- [The randomly permuted coordinate function](goal) uses [the equivalence selected by the first component of the input](hyp:e) to relabel coordinates in [a pair consisting of a selector value and a coordinate vector](hyp:z). -/
def randomPermutation {I A B : Type*} (e : A → I ≃ I)
    (z : A × (I → B)) : I → B := fun i => z.2 (e z.1 i)

-- @node: measurable_randomPermutation
/-- [The coordinate-relabeling map](goal) is measurable when its permutation selector ranges over a countable measurable space. -/
@[fun_prop]
lemma measurable_randomPermutation {I A B : Type*} [Fintype I] [MeasurableSpace A]
    [Countable A] [MeasurableSingletonClass A] [MeasurableSpace B]
    (e : A → I ≃ I) : Measurable (randomPermutation (B := B) e) := by
  apply measurable_from_prod_countable_right
  intro a
  exact measurable_pi_lambda _ (fun i => measurable_pi_apply (e a i))

-- @node: randomPermutation_map
/-- If [the selector is measurable](hyp:hS), [the coordinate vector is measurable](hyp:hZ), [they are independent](hyp:hInd), and [the vector has independent identically distributed coordinates with law `ν`](hyp:hLaw), then [relabeling its coordinates by the selector-dependent permutation preserves that product law](goal). -/
lemma randomPermutation_map {W I A B : Type*} [MeasurableSpace W] [Fintype I]
    [MeasurableSpace A] [Countable A] [MeasurableSingletonClass A] [MeasurableSpace B]
    (P : Measure W) [IsProbabilityMeasure P] (ν : Measure B) [IsProbabilityMeasure ν]
    (S : W → A) (Z : W → I → B) (e : A → I ≃ I)
    (hS : Measurable S) (hZ : Measurable Z) (hInd : IndepFun S Z P)
    (hLaw : P.map Z = Measure.pi (fun _ : I => ν)) :
    P.map (fun w i => Z w (e (S w) i)) = Measure.pi (fun _ : I => ν) := by
  let T : A × (I → B) → (I → B) := randomPermutation e
  have hT : Measurable T := measurable_randomPermutation e
  have hpair := hInd.map_prod_eq_prod_map_map hS.aemeasurable hZ.aemeasurable
  rw [hLaw] at hpair
  have hcomp : (fun w i => Z w (e (S w) i)) = T ∘ (fun w => (S w, Z w)) := rfl
  rw [hcomp, ← Measure.map_map hT (hS.prodMk hZ), hpair]
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hT hs, Measure.prod_apply (hT hs)]
  have hsection (a : A) :
      (Measure.pi (fun _ : I => ν)) (Prod.mk a ⁻¹' (T ⁻¹' s)) =
        (Measure.pi (fun _ : I => ν)) s := by
    have hp := (measurePreserving_piCongrLeft (fun _ : I => ν) (e a).symm).map_eq
    have hm : Measurable (fun z : I → B => fun i => z (e a i)) := by fun_prop
    change (Measure.pi (fun _ : I => ν)) ((fun z : I → B => fun i => z (e a i)) ⁻¹' s) = _
    rw [← Measure.map_apply hm hs]
    have he : ⇑(MeasurableEquiv.piCongrLeft (fun _ : I => B) (e a).symm) =
        (fun z : I → B => fun i => z (e a i)) := by
      funext z i
      simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    rw [he] at hp
    exact congrArg (fun μ => μ s) hp
  simp_rw [hsection]
  rw [lintegral_const, Measure.map_apply hS MeasurableSet.univ]
  simp

-- @node: measurable_obs_tuple
/-- [The full relabelled observation tuple](goal) is measurable for every sample size. -/
@[fun_prop]
lemma measurable_obs_tuple (M : ExtremeModel q d) (E : NeteExperiment M) (n : ℕ) :
    Measurable (fun w => obs E n w) := by
  have hz : Measurable (fun w (i : Fin n) => E.Zraw i.val w) :=
    measurable_pi_lambda _ (fun i => E.measurable_raw i.val)
  have ht := (measurable_randomPermutation (B := Obs q d) (@splitPermutation n)).comp
    ((E.measurable_train n).prodMk hz)
  convert ht using 1
  funext w i
  exact relabelledObs_eq_permutation E.Zraw E.trainSet n w i

-- @node: relabelled_joint_law
/-- If [the sample size is even](hyp:hn) and [the raw sample is independent and identically distributed](hyp:hiid), then [the relabelled observation tuple has the product law of the model's observation distribution](goal). -/
lemma relabelled_joint_law (M : ExtremeModel q d) (E : NeteExperiment M) (n : ℕ)
    (hn : EvenSampleSize n) (hiid : IIDSampling E n) :
    E.P.map (fun w => obs E n w) =
      Measure.pi (fun _ : Fin n => M.mu.map (observation M)) := by
  have hobs : Measurable (observation M) :=
    M.measurable_X.prodMk (M.measurable_D.prodMk (M.measurable_Y.prodMk M.measurable_U))
  letI : IsProbabilityMeasure (M.mu.map (observation M)) :=
    Measure.isProbabilityMeasure_map hobs.aemeasurable
  have hz : Measurable (fun w (i : Fin n) => E.Zraw i.val w) :=
    measurable_pi_lambda _ (fun i => E.measurable_raw i.val)
  have hraw := hiid.1.map_fun_eq_pi_map (fun i : Fin n => (E.measurable_raw i.val).aemeasurable)
  simp_rw [hiid.2] at hraw
  have h := randomPermutation_map E.P (M.mu.map (observation M)) (E.trainSet n)
    (fun w (i : Fin n) => E.Zraw i.val w) (@splitPermutation n)
    (E.measurable_train n) hz (E.randomSplit n hn).2.2 hraw
  convert h using 1
  congr 1
  funext w i
  exact relabelledObs_eq_permutation E.Zraw E.trainSet n w i

end Papers.TbsExtremeEffects
