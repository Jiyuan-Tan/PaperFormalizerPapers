module
public import Papers.TbsNeuralCausalPi.Helpers.CounterexampleMechanisms
/-! # The six-atom observational coupling in the backdoor counterexample

The treatment coordinate uses labels one and two. Collapsing the last two
covariate atoms to zero gives the limiting observational law. The synchronous
atom coupling changes only that coordinate and has cost delta / 4.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped ENNReal
noncomputable section

-- @node: counterexampleAtomWeight
/-- The [six observational atom weights](goal), in order, are 1/4, 1/4, 1/8, 1/8,
3/16, and 1/16. -/
def counterexampleAtomWeight : Fin 6 → ℝ≥0∞ :=
  fun i => ENNReal.ofReal ((![(1/4 : ℝ), 1/4, 1/8, 1/8, 3/16, 1/16]) i)

-- @node: counterexampleAtomWeight_sum
/-- [The six observational atom weights sum to one](goal). -/
lemma counterexampleAtomWeight_sum : ∑ i, counterexampleAtomWeight i = 1 := by
  unfold counterexampleAtomWeight
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by fin_cases i <;> norm_num)]
  norm_num [Fin.sum_univ_succ]

-- @node: counterexampleObservationAtom
/-- For [covariate displacement delta](hyp:delta) and [an index among the six
atoms](hyp:i), the [observational atom](goal) is the corresponding row of
(-1,1,0), (-1,2,1), (0,1,0), (0,2,0), (delta,2,1), and (delta,1,1),
with coordinates covariate, treatment label, and outcome. -/
def counterexampleObservationAtom (delta : ℝ) (i : Fin 6) : L1Vec 3 :=
  WithLp.toLp 1 ![(![-1,-1,0,0,delta,delta] : Fin 6 → ℝ) i,
    (![1,2,1,2,2,1] : Fin 6 → ℝ) i, (![0,1,0,0,1,1] : Fin 6 → ℝ) i]

-- @node: counterexampleFiniteObservationLaw
/-- For [covariate displacement delta](hyp:delta), the [finite observational
law](goal) assigns the six specified weights to their corresponding observational atoms. -/
def counterexampleFiniteObservationLaw (delta : ℝ) : Measure (L1Vec 3) :=
  ∑ i, counterexampleAtomWeight i • Measure.dirac (counterexampleObservationAtom delta i)

-- @node: counterexampleFiniteObservationLaw_probability
/-- [The finite observational law is a probability measure for every covariate
displacement](goal). -/
lemma counterexampleFiniteObservationLaw_probability (delta : ℝ) :
    IsProbabilityMeasure (counterexampleFiniteObservationLaw delta) := by
  constructor
  simpa [counterexampleFiniteObservationLaw, Measure.finsetSum_apply,
    Measure.smul_apply] using counterexampleAtomWeight_sum

-- @node: counterexampleObservationCoupling
/-- For [covariate displacement delta](hyp:delta), the [synchronous observational
coupling](goal) pairs each zero-displacement atom with the corresponding
delta-displacement atom, using their common weight. -/
def counterexampleObservationCoupling (delta : ℝ) : Measure (L1Vec 3 × L1Vec 3) :=
  ∑ i, counterexampleAtomWeight i •
    Measure.dirac (counterexampleObservationAtom 0 i, counterexampleObservationAtom delta i)

-- @node: counterexampleObservationCoupling_isCoupling
/-- [The synchronous observational measure is a probability coupling of the
zero-displacement and delta-displacement observational laws](goal). -/
lemma counterexampleObservationCoupling_isCoupling (delta : ℝ) :
    Causalean.Stat.IsCoupling (counterexampleObservationCoupling delta)
      (counterexampleFiniteObservationLaw 0) (counterexampleFiniteObservationLaw delta) := by
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · simpa [counterexampleObservationCoupling, Measure.finsetSum_apply,
      Measure.smul_apply] using counterexampleAtomWeight_sum
  · simp only [counterexampleObservationCoupling, counterexampleFiniteObservationLaw,
      Measure.map_finset_sum measurable_fst.aemeasurable, Measure.map_smul,
      Measure.map_dirac', measurable_fst]
  · simp only [counterexampleObservationCoupling, counterexampleFiniteObservationLaw,
      Measure.map_finset_sum measurable_snd.aemeasurable, Measure.map_smul,
      Measure.map_dirac', measurable_snd]

-- @node: counterexampleObservationAtom_dist
/-- [The distance between corresponding observational atoms at zero and at delta
is zero for the first four atoms and the absolute value of delta for the last two](goal). -/
lemma counterexampleObservationAtom_dist (delta : ℝ) (i : Fin 6) :
    dist (counterexampleObservationAtom 0 i) (counterexampleObservationAtom delta i) =
      if i < 4 then 0 else |delta| := by
  fin_cases i <;>
    simp [counterexampleObservationAtom, PiLp.dist_eq_sum (p := 1) (by norm_num), Real.dist_eq,
      Fin.sum_univ_succ]

-- @node: counterexampleObservationCoupling_cost
/-- [The expected distance under the synchronous observational coupling equals
one quarter of the absolute value of the covariate displacement](goal). -/
lemma counterexampleObservationCoupling_cost (delta : ℝ) :
    (∫⁻ z, edist z.1 z.2 ∂counterexampleObservationCoupling delta) =
      ENNReal.ofReal (|delta| / 4) := by
  simp only [counterexampleObservationCoupling, lintegral_finsetSum_measure,
    lintegral_smul_measure, lintegral_dirac, smul_eq_mul, edist_dist,
    counterexampleObservationAtom_dist]
  norm_num [counterexampleAtomWeight, Fin.sum_univ_succ, Fin.lt_def]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

-- @node: counterexampleFiniteObservationLaw_wasserstein_le
/-- If [delta is nonnegative](hyp:hdelta), [the Wasserstein distance of order one
between the zero-displacement and delta-displacement observational laws is at
most delta divided by two](goal). -/
lemma counterexampleFiniteObservationLaw_wasserstein_le (delta : ℝ) (hdelta : 0 ≤ delta) :
    wasserstein1 (counterexampleFiniteObservationLaw 0)
      (counterexampleFiniteObservationLaw delta) ≤ ENNReal.ofReal (delta / 2) := by
  apply (Toolkit.Foundations.MeasureTheory.wasserstein1_le_cost
    (counterexampleObservationCoupling_isCoupling delta)).trans
  rw [counterexampleObservationCoupling_cost, abs_of_nonneg hdelta]
  exact ENNReal.ofReal_le_ofReal (by linarith)

-- @node: counterexampleTrueLatentWeight
/-- For [a triple of binary indices](hyp:i), the [true latent atom weight](goal)
is the product of a uniform first-coordinate weight and independent Bernoulli
weights with success probabilities 3/5 and 1/3 for the second and third coordinates. -/
def counterexampleTrueLatentWeight (i : Fin 2 × Fin 2 × Fin 2) : ℝ :=
  (1/2) * (if i.2.1 = 1 then 3/5 else 2/5) *
    (if i.2.2 = 1 then 1/3 else 2/3)

-- @node: counterexampleTrueLatentWeight_nonneg
/-- [Every true latent atom weight is nonnegative](goal). -/
lemma counterexampleTrueLatentWeight_nonneg (i : Fin 2 × Fin 2 × Fin 2) :
    0 ≤ counterexampleTrueLatentWeight i := by
  rcases i with ⟨x,a,b⟩
  fin_cases x <;> fin_cases a <;> fin_cases b <;>
    norm_num [counterexampleTrueLatentWeight]

-- @node: counterexampleTrueLatentWeight_sum
/-- [The true latent atom weights sum to one over all eight binary triples](goal). -/
lemma counterexampleTrueLatentWeight_sum : ∑ i, counterexampleTrueLatentWeight i = 1 := by
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, counterexampleTrueLatentWeight]

-- @node: counterexampleTrueLatentAtom
/-- For [a triple of binary indices](hyp:i), the [true latent atom](goal) has
covariate equal to the first index minus one and two noise coordinates equal
to the second and third indices. -/
def counterexampleTrueLatentAtom (i : Fin 2 × Fin 2 × Fin 2) : L1Vec 3 :=
  WithLp.toLp 1 ![-1 + (i.1.val : ℝ), (i.2.1.val : ℝ), (i.2.2.val : ℝ)]

-- @node: counterexampleTrueFiniteLatentLaw
/-- The [true finite latent law](goal) assigns each of the eight true latent
atoms its specified product weight. -/
def counterexampleTrueFiniteLatentLaw : Measure (L1Vec 3) :=
  ∑ i, ENNReal.ofReal (counterexampleTrueLatentWeight i) •
    Measure.dirac (counterexampleTrueLatentAtom i)

-- @node: counterexampleTrueFiniteLatentLaw_probability
/-- [The true finite latent law is a probability measure](goal). -/
lemma counterexampleTrueFiniteLatentLaw_probability :
    IsProbabilityMeasure counterexampleTrueFiniteLatentLaw := by
  constructor
  simp only [counterexampleTrueFiniteLatentLaw, Measure.finsetSum_apply,
    Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => counterexampleTrueLatentWeight_nonneg i),
    counterexampleTrueLatentWeight_sum, ENNReal.ofReal_one]

-- @node: counterexampleTrueInterventionOutcome
/-- Given [a treatment indicator](hyp:t) and [a latent vector containing the
covariate and two noise coordinates](hyp:z), the [true intervention outcome](goal)
evaluates the true outcome mechanism with treatment label two when the indicator
is true and label one otherwise, retaining the covariate and noise coordinates. -/
def counterexampleTrueInterventionOutcome (t : Bool) (z : L1Vec 3) : ℝ :=
  counterexampleTrueOutcome (WithLp.toLp 1
    ![z.ofLp 0, if t then 2 else 1, z.ofLp 1, z.ofLp 2])

-- @node: counterexampleTrueInterventionOutcome_measurable
/-- [For either treatment choice, the true intervention outcome is a measurable
function of the latent vector](goal). -/
@[fun_prop] lemma counterexampleTrueInterventionOutcome_measurable (t : Bool) :
    Measurable (counterexampleTrueInterventionOutcome t) := by
  unfold counterexampleTrueInterventionOutcome
  fun_prop

-- @node: counterexampleTrueInterventionOutcome_integrable
/-- [For either treatment choice, the true intervention outcome is integrable
under the true finite latent law](goal). -/
lemma counterexampleTrueInterventionOutcome_integrable (t : Bool) :
    Integrable (counterexampleTrueInterventionOutcome t) counterexampleTrueFiniteLatentLaw := by
  let := counterexampleTrueFiniteLatentLaw_probability
  apply counterexampleTrueOutcome_integrable
  fun_prop

-- @node: counterexampleTrueInterventionOutcome_at_atom
/-- [At a true latent atom with first binary index zero, the intervention outcome
equals the treatment indicator; with first index one, it equals the second
binary index under treatment and the third binary index under control](goal). -/
lemma counterexampleTrueInterventionOutcome_at_atom
    (t : Bool) (i : Fin 2 × Fin 2 × Fin 2) :
    counterexampleTrueInterventionOutcome t (counterexampleTrueLatentAtom i) =
      if i.1 = 0 then (if t then 1 else 0)
      else (if t then (i.2.1.val : ℝ) else (i.2.2.val : ℝ)) := by
  rcases i with ⟨x,a,b⟩
  fin_cases x <;> fin_cases a <;> fin_cases b <;> cases t <;>
    norm_num [counterexampleTrueInterventionOutcome, counterexampleTrueLatentAtom,
      counterexampleTrueOutcome, counterexampleClamp, counterexampleBlend,
      Matrix.cons_val_two, Matrix.cons_val_three]

-- @node: counterexampleTrueFiniteATE
/-- [The average treatment effect under the true finite latent law equals 19/30](goal). -/
lemma counterexampleTrueFiniteATE :
    (∫ z, counterexampleTrueInterventionOutcome true z -
      counterexampleTrueInterventionOutcome false z ∂counterexampleTrueFiniteLatentLaw) =
      (19/30 : ℝ) := by
  rw [integral_sub (counterexampleTrueInterventionOutcome_integrable true)
    (counterexampleTrueInterventionOutcome_integrable false)]
  have he (t : Bool) :
      (∫ z, counterexampleTrueInterventionOutcome t z ∂counterexampleTrueFiniteLatentLaw) =
        ∑ i, counterexampleTrueLatentWeight i *
          counterexampleTrueInterventionOutcome t (counterexampleTrueLatentAtom i) := by
    rw [counterexampleTrueFiniteLatentLaw, integral_finsetSum_measure]
    · simp only [integral_smul_measure, integral_dirac,
        ENNReal.toReal_ofReal (counterexampleTrueLatentWeight_nonneg _), smul_eq_mul]
    · exact integrable_finsetSum_measure.mp (counterexampleTrueInterventionOutcome_integrable t)
  rw [he, he]
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ,
    counterexampleTrueInterventionOutcome_at_atom, counterexampleTrueLatentWeight]

-- @node: counterexampleTrueFiniteObservationLaw
/-- The [true finite observational law](goal) sums over the true latent atoms:
[take each atom's covariate](step:1), [compute its true probability of treatment
label two](step:2), and [weight the control and treated observation masses by
their treatment probabilities and the atom's latent weight](step:3). -/
def counterexampleTrueFiniteObservationLaw : Measure (L1Vec 3) :=
  ∑ i : Fin 2 × Fin 2 × Fin 2,
    let x := (counterexampleTrueLatentAtom i).ofLp 0
    let p := counterexampleTrueTreatmentProbability x
    ENNReal.ofReal (counterexampleTrueLatentWeight i) •
      (ENNReal.ofReal (1-p) • Measure.dirac (WithLp.toLp 1
        ![x, 1, counterexampleTrueInterventionOutcome false (counterexampleTrueLatentAtom i)]) +
      ENNReal.ofReal p • Measure.dirac (WithLp.toLp 1
        ![x, 2, counterexampleTrueInterventionOutcome true (counterexampleTrueLatentAtom i)]))

-- @node: counterexampleTrueFiniteObservationLaw_eq
/-- [The observational law induced by the true finite mechanisms equals the
six-atom observational law at zero displacement](goal). -/
lemma counterexampleTrueFiniteObservationLaw_eq :
    counterexampleTrueFiniteObservationLaw = counterexampleFiniteObservationLaw 0 := by
  ext s hs
  simp only [counterexampleTrueFiniteObservationLaw, counterexampleFiniteObservationLaw,
    Measure.finsetSum_apply, Measure.smul_apply, Measure.add_apply, smul_eq_mul]
  have hdir (x : L1Vec 3) : (Measure.dirac x) s ≠ ∞ := measure_ne_top _ _
  apply (ENNReal.toReal_eq_toReal_iff' (by
    apply ENNReal.sum_ne_top.mpr
    intro i hi
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    apply ENNReal.add_ne_top.mpr
    exact ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hdir _),
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hdir _)⟩) (by
    apply ENNReal.sum_ne_top.mpr
    intro i hi
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hdir _))).mp
  simp only [Fintype.sum_prod_type, Fin.sum_univ_succ]
  norm_num [counterexampleTrueLatentWeight, counterexampleTrueLatentAtom,
    counterexampleTrueInterventionOutcome, counterexampleTrueOutcome,
    counterexampleBlend, counterexampleAtomWeight,
    counterexampleObservationAtom, counterexampleTrueTreatmentProbability,
    counterexampleClamp, Matrix.cons_val_two, Matrix.cons_val_three]
  have hind (x : L1Vec 3) : s.indicator (1 : L1Vec 3 → ℝ≥0∞) x ≠ ∞ := by
    by_cases hx : x ∈ s <;> simp [Set.indicator, hx]
  simp (disch := solve_by_elim (maxDepth := 50)
    [ENNReal.add_ne_top.mpr, And.intro, ENNReal.mul_ne_top,
      ENNReal.ofReal_ne_top, hind]) only [ENNReal.toReal_add, ENNReal.toReal_mul]
  norm_num
  ring

-- @node: counterexampleApproxFiniteLatentLaw
/-- For [covariate displacement delta](hyp:delta), the [approximate finite latent
law](goal) assigns masses 1/2, 1/4, and 1/4 to covariate values -1, zero, and delta,
respectively. -/
def counterexampleApproxFiniteLatentLaw (delta : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1/2 : ℝ) • Measure.dirac (-1) +
    ENNReal.ofReal (1/4 : ℝ) • Measure.dirac 0 +
    ENNReal.ofReal (1/4 : ℝ) • Measure.dirac delta

-- @node: counterexampleApproxFiniteLatentLaw_probability
/-- [The approximate finite latent law is a probability measure for every
covariate displacement](goal). -/
lemma counterexampleApproxFiniteLatentLaw_probability (delta : ℝ) :
    IsProbabilityMeasure (counterexampleApproxFiniteLatentLaw delta) := by
  constructor
  simp only [counterexampleApproxFiniteLatentLaw, Measure.add_apply,
    Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

-- @node: counterexampleApproxInterventionOutcome
/-- Given [covariate displacement delta](hyp:delta), [a treatment indicator](hyp:t),
and [a covariate value](hyp:x), the [approximate intervention outcome](goal)
evaluates the approximate outcome mechanism at that covariate with treatment
label two when the indicator is true and label one otherwise. -/
def counterexampleApproxInterventionOutcome (delta : ℝ) (t : Bool) (x : ℝ) : ℝ :=
  counterexampleApproxOutcome delta (WithLp.toLp 1 ![x, if t then 2 else 1])

-- @node: counterexampleApproxInterventionOutcome_measurable
/-- [For every displacement and either treatment choice, the approximate
intervention outcome is a measurable function of the covariate](goal). -/
@[fun_prop] lemma counterexampleApproxInterventionOutcome_measurable (delta : ℝ) (t : Bool) :
    Measurable (counterexampleApproxInterventionOutcome delta t) := by
  unfold counterexampleApproxInterventionOutcome
  fun_prop

-- @node: counterexampleApproxInterventionOutcome_integrable
/-- [For every displacement and either treatment choice, the approximate
intervention outcome is integrable under the corresponding approximate finite
latent law](goal). -/
lemma counterexampleApproxInterventionOutcome_integrable (delta : ℝ) (t : Bool) :
    Integrable (counterexampleApproxInterventionOutcome delta t)
      (counterexampleApproxFiniteLatentLaw delta) := by
  let := counterexampleApproxFiniteLatentLaw_probability delta
  apply counterexampleApproxOutcome_integrable
  fun_prop

-- @node: counterexampleApproxInterventionOutcome_at_atoms
/-- If [delta is positive](hyp:hdelta), [the approximate intervention outcome
equals the treatment indicator at covariate -1, zero at covariate zero, and one
at covariate delta](goal). -/
lemma counterexampleApproxInterventionOutcome_at_atoms (delta : ℝ) (hdelta : 0 < delta)
    (t : Bool) :
    counterexampleApproxInterventionOutcome delta t (-1) = (if t then 1 else 0) ∧
    counterexampleApproxInterventionOutcome delta t 0 = 0 ∧
    counterexampleApproxInterventionOutcome delta t delta = 1 := by
  unfold counterexampleApproxInterventionOutcome
  refine ⟨?_, counterexampleApproxOutcome_at_zero _ _ rfl,
    counterexampleApproxOutcome_at_delta _ hdelta _ rfl⟩
  have h := counterexampleApproxOutcome_at_negative delta
    (WithLp.toLp 1 ![(-1 : ℝ), if t then 2 else 1]) rfl
    (by cases t <;> norm_num)
  cases t <;> norm_num at h ⊢ <;> exact h

-- @node: counterexampleApproxFiniteATE
/-- If [delta is positive](hyp:hdelta), [the average treatment effect under the
approximate finite latent law equals one half](goal). -/
lemma counterexampleApproxFiniteATE (delta : ℝ) (hdelta : 0 < delta) :
    (∫ x, counterexampleApproxInterventionOutcome delta true x -
      counterexampleApproxInterventionOutcome delta false x
      ∂counterexampleApproxFiniteLatentLaw delta) = (1/2 : ℝ) := by
  rw [integral_sub (counterexampleApproxInterventionOutcome_integrable delta true)
    (counterexampleApproxInterventionOutcome_integrable delta false)]
  have he (t : Bool) :
      (∫ x, counterexampleApproxInterventionOutcome delta t x
        ∂counterexampleApproxFiniteLatentLaw delta) = (1/2 : ℝ) * (if t then 1 else 0) + 1/4 := by
    have hi := counterexampleApproxInterventionOutcome_integrable delta t
    have hparts := integrable_add_measure.mp hi
    have hleft := integrable_add_measure.mp hparts.1
    rw [counterexampleApproxFiniteLatentLaw,
      integral_add_measure hparts.1 hparts.2, integral_add_measure hleft.1 hleft.2]
    simp only [integral_smul_measure, integral_dirac,
      (counterexampleApproxInterventionOutcome_at_atoms delta hdelta t).1,
      (counterexampleApproxInterventionOutcome_at_atoms delta hdelta t).2.1,
      (counterexampleApproxInterventionOutcome_at_atoms delta hdelta t).2.2]
    norm_num
  rw [he, he]
  norm_num

-- @node: counterexampleApproxFiniteObservationLaw
/-- For [covariate displacement delta](hyp:delta), the [approximate finite
observational law](goal) sums over three covariate atoms: [select the covariate
from -1, zero, and delta](step:1), [compute its approximate probability of
treatment label two](step:2), and [combine the control and treated observation
masses using those probabilities and covariate weights 1/2, 1/4, and 1/4](step:3). -/
def counterexampleApproxFiniteObservationLaw (delta : ℝ) : Measure (L1Vec 3) :=
  ∑ i : Fin 3,
    let x := (![-1,0,delta] : Fin 3 → ℝ) i
    let p := counterexampleApproxTreatmentProbability delta x
    ENNReal.ofReal ((![(1/2 : ℝ),1/4,1/4] : Fin 3 → ℝ) i) •
      (ENNReal.ofReal (1-p) • Measure.dirac (WithLp.toLp 1
        ![x, 1, counterexampleApproxInterventionOutcome delta false x]) +
      ENNReal.ofReal p • Measure.dirac (WithLp.toLp 1
        ![x, 2, counterexampleApproxInterventionOutcome delta true x]))

-- @node: counterexampleApproxFiniteObservationLaw_eq
/-- If [delta is positive](hyp:hdelta), [the observational law induced by the
approximate finite mechanisms equals the six-atom observational law at
displacement delta](goal). -/
lemma counterexampleApproxFiniteObservationLaw_eq (delta : ℝ) (hdelta : 0 < delta) :
    counterexampleApproxFiniteObservationLaw delta = counterexampleFiniteObservationLaw delta := by
  ext s hs
  simp only [counterexampleApproxFiniteObservationLaw, counterexampleFiniteObservationLaw,
    Measure.finsetSum_apply, Measure.smul_apply, Measure.add_apply, smul_eq_mul]
  have hdir (x : L1Vec 3) : (Measure.dirac x) s ≠ ∞ := measure_ne_top _ _
  apply (ENNReal.toReal_eq_toReal_iff' (by
    apply ENNReal.sum_ne_top.mpr
    intro i hi
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    apply ENNReal.add_ne_top.mpr
    exact ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hdir _),
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hdir _)⟩) (by
    apply ENNReal.sum_ne_top.mpr
    intro i hi
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hdir _))).mp
  have hp := counterexampleApproxTreatmentProbability_values delta hdelta
  have hy := counterexampleApproxInterventionOutcome_at_atoms delta hdelta
  norm_num [Fin.sum_univ_succ, Matrix.cons_val_two, counterexampleAtomWeight,
    counterexampleObservationAtom, hp.1, hp.2.1, hp.2.2,
    (hy false).1, (hy false).2.1, (hy false).2.2,
    (hy true).1, (hy true).2.1, (hy true).2.2]
  have hind (x : L1Vec 3) : s.indicator (1 : L1Vec 3 → ℝ≥0∞) x ≠ ∞ := by
    by_cases hx : x ∈ s <;> simp [Set.indicator, hx]
  simp (disch := solve_by_elim (maxDepth := 50)
    [ENNReal.add_ne_top.mpr, And.intro, ENNReal.mul_ne_top,
      ENNReal.ofReal_ne_top, hind]) only [ENNReal.toReal_add, ENNReal.toReal_mul]
  norm_num
  ring

-- @node: counterexampleFiniteMechanisms_wasserstein_le
/-- If [delta is positive](hyp:hdelta), [the Wasserstein distance of order one
between the true and approximate finite observational laws is at most delta
divided by two](goal). -/
lemma counterexampleFiniteMechanisms_wasserstein_le (delta : ℝ) (hdelta : 0 < delta) :
    wasserstein1 counterexampleTrueFiniteObservationLaw
      (counterexampleApproxFiniteObservationLaw delta) ≤ ENNReal.ofReal (delta/2) := by
  rw [counterexampleTrueFiniteObservationLaw_eq,
    counterexampleApproxFiniteObservationLaw_eq delta hdelta]
  exact counterexampleFiniteObservationLaw_wasserstein_le delta hdelta.le

-- @node: counterexampleFiniteATE_gap
/-- If [delta is positive](hyp:hdelta), [the absolute difference between the
true and approximate average treatment effects under their respective finite
latent laws exceeds one tenth](goal). -/
lemma counterexampleFiniteATE_gap (delta : ℝ) (hdelta : 0 < delta) :
    (1/10 : ℝ) < |(∫ z, counterexampleTrueInterventionOutcome true z -
      counterexampleTrueInterventionOutcome false z ∂counterexampleTrueFiniteLatentLaw) -
      (∫ x, counterexampleApproxInterventionOutcome delta true x -
        counterexampleApproxInterventionOutcome delta false x
        ∂counterexampleApproxFiniteLatentLaw delta)| := by
  rw [counterexampleTrueFiniteATE, counterexampleApproxFiniteATE delta hdelta]
  norm_num

-- @node: counterexampleFiniteObservationLaw_tolerance
/-- For [a positive tolerance](hyp:heps), [there exists a positive displacement
whose six-atom observational law is within that tolerance of the
zero-displacement law in Wasserstein distance of order one](goal). -/
lemma counterexampleFiniteObservationLaw_tolerance (eps : ℝ) (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧
      wasserstein1 (counterexampleFiniteObservationLaw 0)
        (counterexampleFiniteObservationLaw delta) ≤ ENNReal.ofReal eps := by
  refine ⟨eps, heps, ?_⟩
  exact (counterexampleFiniteObservationLaw_wasserstein_le eps heps.le).trans
    (ENNReal.ofReal_le_ofReal (by linarith))

-- @node: counterexampleFiniteMechanisms_separation
/-- For [a positive tolerance](hyp:heps), [there exists a positive displacement
such that the true and approximate finite observational laws are within that
tolerance in Wasserstein distance of order one, the approximate treatment-effect
function is integrable under its finite latent law, and the absolute difference
between the true and approximate average treatment effects exceeds one tenth](goal).

Realizing these laws as canonical structural causal model laws remains a separate
construction. -/
lemma counterexampleFiniteMechanisms_separation (eps : ℝ) (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧
      wasserstein1 counterexampleTrueFiniteObservationLaw
        (counterexampleApproxFiniteObservationLaw delta) ≤ ENNReal.ofReal eps ∧
      Integrable (fun x => counterexampleApproxInterventionOutcome delta true x -
        counterexampleApproxInterventionOutcome delta false x)
        (counterexampleApproxFiniteLatentLaw delta) ∧
      (1/10 : ℝ) < |(∫ z, counterexampleTrueInterventionOutcome true z -
        counterexampleTrueInterventionOutcome false z ∂counterexampleTrueFiniteLatentLaw) -
        (∫ x, counterexampleApproxInterventionOutcome delta true x -
          counterexampleApproxInterventionOutcome delta false x
          ∂counterexampleApproxFiniteLatentLaw delta)| := by
  refine ⟨eps, heps, ?_, ?_, counterexampleFiniteATE_gap eps heps⟩
  · exact (counterexampleFiniteMechanisms_wasserstein_le eps heps).trans
      (ENNReal.ofReal_le_ofReal (by linarith))
  · exact (counterexampleApproxInterventionOutcome_integrable eps true).sub
      (counterexampleApproxInterventionOutcome_integrable eps false)

end
end Papers.TbsNeuralCausalPi
