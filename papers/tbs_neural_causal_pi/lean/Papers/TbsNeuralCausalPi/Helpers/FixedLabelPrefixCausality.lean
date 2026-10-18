module
public import Papers.TbsNeuralCausalPi.Helpers.FixedLabelSelectorTables
/-! # Causality and reconstruction of fixed-label propensity tables

An entry at a node depends only on labels strictly earlier in the topological
order. The simultaneous selector equations therefore identify the factual
stratum uniquely; they do not introduce a circular choice of labels.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

-- @node: evalSteps_eq_of_assignments_before
/-- If [two interventions agree at every node whose topological position
precedes the chosen step](hyp:ht), [their evaluation histories at that step
coincide for the same exogenous realization](goal). -/
lemma evalSteps_eq_of_assignments_before (M : EuclideanSCM kind dims)
    (t t' : Intervention kind) (u : Exogenous kind dims) (r : ℕ)
    (ht : ∀ i, M.dag.topoOrder i < r → t i = t' i) :
    evalSteps M t u r = evalSteps M t' u r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have he := ih (fun i hi => ht i (by omega))
    apply WithLp.ofLp_injective
    funext ⟨i,j⟩
    simp only [evalSteps, WithLp.ofLp_toLp, he]
    by_cases hi : M.dag.topoOrder i = r
    · simp only [hi, if_true]
      rw [ht i (by omega)]
    · simp only [hi, if_false]

-- @node: categoricalStratumAssignment_eq_of_label_eq
/-- If [two categorical strata give a node the same label](hyp:hi),
[their associated fixed-label assignments agree at that node](goal). -/
lemma categoricalStratumAssignment_eq_of_label_eq
    (c c' : CategoricalStratum kind) (i : Fin n) (hi : c i = c' i) :
    categoricalStratumAssignment c i = categoricalStratumAssignment c' i := by
  simp only [categoricalStratumAssignment, hi]

-- @node: fixedLabelStructuralInput_eq_of_prefix
/-- If [two categorical strata agree at every node strictly earlier than
the chosen node in topological order](hyp:hc), [they produce the same
fixed-label structural input at that node for the same latent vector](goal). -/
lemma fixedLabelStructuralInput_eq_of_prefix (M : EuclideanSCM kind dims)
    (c c' : CategoricalStratum kind) (i : Fin n) (z : Latent dims)
    (hc : ∀ j, M.dag.topoOrder j < M.dag.topoOrder i → c j = c' j) :
    fixedLabelStructuralInput M c i z = fixedLabelStructuralInput M c' i z := by
  unfold fixedLabelStructuralInput
  rw [evalSteps_eq_of_assignments_before M _ _ _ _
    (fun j hj => categoricalStratumAssignment_eq_of_label_eq c c' j (hc j hj))]

-- @node: fixedLabelCategoricalPropensity_eq_of_prefix
/-- For [a node with the given number of categories](hyp:hi), if [two strata
agree at every strictly earlier node in topological order](hyp:hc), [their
fixed-label propensity vectors at this node coincide for the same latent
vector](goal). -/
lemma fixedLabelCategoricalPropensity_eq_of_prefix
    (M : CanonicalSCM kind dims dag G C) (c c' : CategoricalStratum kind)
    (i : Fin n) (k : ℕ) (hi : kind i = Sum.inr k) (z : Latent dims)
    (hc : ∀ j, dag.topoOrder j < dag.topoOrder i → c j = c' j) :
    fixedLabelCategoricalPropensity M c i k hi z =
      fixedLabelCategoricalPropensity M c' i k hi z := by
  apply Subtype.ext
  funext j
  change (M.f i (fixedLabelStructuralInput M.toEuclideanSCM c i z)).ofLp _ = _
  rw [fixedLabelStructuralInput_eq_of_prefix M.toEuclideanSCM c c' i z hc]
  rfl

-- @node: rounded_fixedLabelCategoricalPropensity_eq_of_prefix
/-- For [a node with the given number of categories](hyp:hi), if [two strata
agree at all strictly earlier nodes](hyp:hc), [rounding their fixed-label
propensity vectors with the same simplex representative and resolution gives
identical results at any common latent vector](goal). -/
lemma rounded_fixedLabelCategoricalPropensity_eq_of_prefix
    (M : CanonicalSCM kind dims dag G C) (c c' : CategoricalStratum kind)
    (i : Fin n) (k : ℕ) (hi : kind i = Sum.inr k) (z : Latent dims)
    (p0 : probabilitySimplex k) (R : ℕ)
    (hc : ∀ j, dag.topoOrder j < dag.topoOrder i → c j = c' j) :
    simplexRound p0 R (fixedLabelCategoricalPropensity M c i k hi z) =
      simplexRound p0 R (fixedLabelCategoricalPropensity M c' i k hi z) := by
  rw [fixedLabelCategoricalPropensity_eq_of_prefix M c c' i k hi z hc]

-- @node: exists_fixedLabelCategoricalPropensity_causal_tables
/-- Given [a nonnegative Lipschitz bound](hyp:L), assume [the continuous
mechanisms obey it](hyp:hcont), [the categorical propensities obey it on their
domains](hyp:hprop), [the chosen node has the given number of categories](hyp:hi),
[the rounding resolution is positive](hyp:hR), and [the code assigns each cube
point a grid point within the mesh radius](hyp:hgrid). Then [there is a finite
family of simplex-valued tables with log cardinality at most the number of
strata times the category count times the grid size times the logarithm of the
sum of one and the resolution, containing a table whose coordinate error is at most the
mesh radius times the propensity Lipschitz bound plus the reciprocal resolution,
and whose entries agree for strata sharing all labels strictly before the
chosen node](goal).

The propensity Lipschitz bound is the mechanism bound times the structural
input size times the sum of one and the fixed-label propagation budget before
the node. -/
lemma exists_fixedLabelCategoricalPropensity_causal_tables
    (M : CanonicalSCM kind dims dag G C) (L : ℝ≥0)
    (hcont : ContinuousMechanismsLipschitz M.toEuclideanSCM L)
    (hprop : CategoricalPropensityLipschitz M.toEuclideanSCM M.f L)
    (i : Fin n) (k : ℕ) (hi : kind i = Sum.inr k)
    (p0 : probabilitySimplex k) {s R : ℕ} (hR : 0 < R)
    {K rho : ℝ} (grid : Fin s → boundedCube (∑ j, dims j) K)
    (code : boundedCube (∑ j, dims j) K → Fin s)
    (hgrid : ∀ x, dist x.val (grid (code x)).val ≤ rho) :
    ∃ T : Finset (CategoricalStratum kind → Fin s → probabilitySimplex k),
      Real.log (T.card : ℝ) ≤
        (∑ _c : CategoricalStratum kind, ((k * s : ℕ) : ℝ)) *
          Real.log (R + 1 : ℕ) ∧
      ∃ table ∈ T,
        (∀ c x j,
          |(fixedLabelCategoricalPropensity M c i k hi
              ((jointLatentVectorEquiv dims).symm x.val)).val j -
            (table c (code x)).val j| ≤
          (L * ((structuralInputSize M.toEuclideanSCM i : ℝ≥0) *
            (fixedLabelLipschitzBudget M.toEuclideanSCM L (dag.topoOrder i) + 1)) : ℝ≥0) *
              rho + (R : ℝ)⁻¹) ∧
        ∀ c c', (∀ j, dag.topoOrder j < dag.topoOrder i → c j = c' j) →
          table c = table c' := by
  classical
  let alphabet := simplexTableGrid p0 R s
  have hne : alphabet.Nonempty := ⟨_, simplexTableGrid_round_mem p0 R s (fun _ => p0)⟩
  let table := fun c j => simplexRound p0 R (fixedLabelCategoricalPropensity M c i k hi
    ((jointLatentVectorEquiv dims).symm (grid j).val))
  refine ⟨Fintype.piFinset (fun _ : CategoricalStratum kind => alphabet), ?_, table, ?_, ?_, ?_⟩
  · rw [Fintype.card_piFinset, Nat.cast_prod,
      Real.log_prod (fun _ _ => by exact_mod_cast hne.card_pos.ne')]
    calc
      _ ≤ ∑ _c : CategoricalStratum kind, ((k * s : ℕ) : ℝ) *
          Real.log (R + 1 : ℕ) :=
        Finset.sum_le_sum (fun _ _ => simplexTableGrid_log_card_le p0 R s)
      _ = _ := (Finset.sum_mul ..).symm
  · exact Fintype.mem_piFinset.mpr (fun c => simplexTableGrid_round_mem p0 R s _)
  · intro c x j
    let z := (jointLatentVectorEquiv dims).symm x.val
    let z' := (jointLatentVectorEquiv dims).symm (grid (code x)).val
    have hLip := (fixedLabelCategoricalPropensity_coordinate_lipschitz
      M L hcont hprop c i k hi j).dist_le_mul z z'
    rw [Real.dist_eq] at hLip
    have hz : dist z z' ≤ rho := by
      simpa only [z, z', LinearIsometryEquiv.dist_map] using hgrid x
    have hround := (simplexRound_coordinate_error p0 hR
      (fixedLabelCategoricalPropensity M c i k hi z') j).le
    rw [abs_sub_comm] at hround
    exact (abs_sub_le _ ((fixedLabelCategoricalPropensity M c i k hi z').val j) _).trans
      (add_le_add (hLip.trans (mul_le_mul_of_nonneg_left hz (by positivity))) hround)
  · intro c c' hc
    funext j
    exact rounded_fixedLabelCategoricalPropensity_eq_of_prefix M c c' i k hi _ p0 R hc

-- @node: categoricalStratum_eq_factual_of_selector_equations
/-- If [at every categorical node a proposed stratum's label equals the
canonical selector applied to its fixed-label propensity vector and the given
categorical noise](hyp:hc), [the proposed stratum equals the factual categorical
stratum generated by evaluation without intervention](goal). -/
lemma categoricalStratum_eq_factual_of_selector_equations
    (M : CanonicalSCM kind dims dag G C) (u : Exogenous kind dims)
    (c : CategoricalStratum kind)
    (hc : ∀ i k (hi : kind i = Sum.inr k),
      (c i).val =
        (canonicalSelector (.inr k)
          (fun m hm => M.categoricalPositive i m (hi.trans hm))
          (WithLp.toLp 1 (fixedLabelCategoricalPropensity M c i k hi
            (jointNonGumbel u)).val)
          (WithLp.toLp 1 (fun l => (categoricalNoise i u).ofLp
            (Fin.cast (congrArg noiseDim hi).symm l)))).val) :
    c = observedCategoricalStratum
      (intervenedEval M.toEuclideanSCM (fun _ => none) u) := by
  let actual := observedCategoricalStratum
    (intervenedEval M.toEuclideanSCM (fun _ => none) u)
  have hprefix : ∀ r, ∀ i, dag.topoOrder i < r → c i = actual i := by
    intro r
    induction r with
    | zero => intro i hi; omega
    | succ r ih =>
      intro i hi
      by_cases hprev : dag.topoOrder i < r
      · exact ih i hprev
      have htime : dag.topoOrder i = r := by omega
      have hcases : (∃ d, kind i = Sum.inl d) ∨ (∃ k, kind i = Sum.inr k) := by
        cases kind i with
        | inl d => exact Or.inl ⟨d, rfl⟩
        | inr k => exact Or.inr ⟨k, rfl⟩
      rcases hcases with ⟨d, he⟩ | ⟨k, he⟩
      · have hdim : max 1 (noiseDim (kind i)) = 1 := by simp [he, noiseDim]
        apply Fin.ext
        have h1 := (c i).isLt
        have h2 := (actual i).isLt
        omega
      · have hp := fixedLabelCategoricalPropensity_eq_of_prefix M c actual i k he
          (jointNonGumbel u) (fun j hj => ih j (by omega))
        apply Fin.ext
        rw [hc i k he, hp]
        exact (factual_categorical_stratum_eq_selector M u i k he).symm
  funext i
  exact hprefix (n*n+n) i (scm_topoOrder_lt_horizon M.toEuclideanSCM i)

-- @node: existsUnique_categoricalStratum_selector_equations
/-- For any canonical model and exogenous realization, [there is exactly one
categorical stratum whose label at every categorical node equals the canonical
selector applied to that stratum's fixed-label propensity vector and the
realization's categorical noise](goal). -/
lemma existsUnique_categoricalStratum_selector_equations
    (M : CanonicalSCM kind dims dag G C) (u : Exogenous kind dims) :
    ∃! c : CategoricalStratum kind, ∀ i k (hi : kind i = Sum.inr k),
      (c i).val =
        (canonicalSelector (.inr k)
          (fun m hm => M.categoricalPositive i m (hi.trans hm))
          (WithLp.toLp 1 (fixedLabelCategoricalPropensity M c i k hi
            (jointNonGumbel u)).val)
          (WithLp.toLp 1 (fun l => (categoricalNoise i u).ofLp
            (Fin.cast (congrArg noiseDim hi).symm l)))).val := by
  refine ⟨observedCategoricalStratum
    (intervenedEval M.toEuclideanSCM (fun _ => none) u), ?_, ?_⟩
  · exact fun i k hi => factual_categorical_stratum_eq_selector M u i k hi
  · intro c hc
    exact categoricalStratum_eq_factual_of_selector_equations M u c hc

end
end Papers.TbsNeuralCausalPi
