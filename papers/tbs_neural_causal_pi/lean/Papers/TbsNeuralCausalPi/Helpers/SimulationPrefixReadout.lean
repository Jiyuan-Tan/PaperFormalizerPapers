module
public import Papers.TbsNeuralCausalPi.Helpers.SimulationPrefixTables
/-! # Finite complete-output readouts for categorical prefix tables

Continuous readouts and categorical propensities share the same latent code.
The robust prefix event controls the entire selected readout, with a cube
diameter penalty on the exceptional event and no horizon factor.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

/-- Suppose [the output-cube radius B is nonnegative](hyp:hB), [the rounding
tolerance eta is positive](hyp:heta), [L is a nonnegative Lipschitz bound](hyp:L),
and [the coded grid point lies within rho of every latent input](hyp:hgrid).
Then [there is a finite alphabet of prefix readout tables with log cardinality at
most $|I|ek\log(1+2B(e+1)/\eta)$, such that every family of L-Lipschitz readouts
has a table approximating every prefix and latent input within $L\rho+\eta$](goal). -/
-- @node: exists_simulation_prefix_readout_net
lemma exists_simulation_prefix_readout_net
    {I : Type*} [Fintype I] {d e k : ℕ} {K B rho eta : ℝ}
    (hB : 0 ≤ B) (heta : 0 < eta) (L : ℝ≥0)
    (grid : Fin k → boundedCube d K) (code : boundedCube d K → Fin k)
    (hgrid : ∀ x, dist x.val (grid (code x)).val ≤ rho) :
    ∃ T : Finset (I → Fin k → boundedCube e B),
      Real.log (T.card : ℝ) ≤
        (∑ _p : I, ((e * k : ℕ) : ℝ)) * Real.log (1 + 2 * B * (e + 1) / eta) ∧
      ∀ f : I → boundedCube d K → boundedCube e B,
        (∀ p, LipschitzWith L (f p)) →
        ∃ table ∈ T, ∀ p x,
          dist (f p x).val (table p (code x)).val ≤ (L : ℝ) * rho + eta := by
  classical
  obtain ⟨A, happrox, hbudget⟩ := exists_simulation_cube_table_net e k hB heta
  have hnonempty : A.Nonempty := by
    let zero : boundedCube e B := ⟨0, by intro j; simpa using hB⟩
    obtain ⟨t, ht, _⟩ := happrox (fun _ => zero)
    exact ⟨t, ht⟩
  refine ⟨Fintype.piFinset (fun _ : I => A), ?_, ?_⟩
  · rw [Fintype.card_piFinset, Nat.cast_prod,
      Real.log_prod (fun _ _ => by exact_mod_cast hnonempty.card_pos.ne')]
    calc
      _ ≤ ∑ _p : I, ((e * k : ℕ) : ℝ) *
          Real.log (1 + 2 * B * (e + 1) / eta) :=
        Finset.sum_le_sum (fun _ _ => hbudget)
      _ = _ := (Finset.sum_mul ..).symm
  · intro f hf
    choose table hmem herr using fun p => happrox (fun j => f p (grid j))
    refine ⟨table, Fintype.mem_piFinset.mpr hmem, ?_⟩
    intro p x
    have hLip : dist (f p x).val (f p (grid (code x))).val ≤ (L : ℝ) * rho :=
      ((hf p).dist_le_mul x (grid (code x))).trans
        (mul_le_mul_of_nonneg_left (hgrid x) L.coe_nonneg)
    exact (dist_triangle _ (f p (grid (code x))).val _).trans
      (add_le_add hLip (herr p (code x)))

/-- Suppose [every prefix has at least one category](hyp:hk), with
[a successor prefix for each category](hyp:next), [random category probabilities](hyp:r),
and [random category scores](hyp:g), where [the probabilities are measurable](hyp:hr)
and [the scores are measurable](hyp:hg). Then [the prefix reached after any fixed
number of categorical updates from any fixed starting prefix is measurable](goal). -/
-- @node: categoricalPrefixPath_measurable
@[fun_prop] lemma categoricalPrefixPath_measurable
    {Omega I : Type*} [MeasurableSpace Omega] [Countable I]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    (size : I → ℕ)
    (hk : ∀ p m, Sum.inr (size p) = (Sum.inr m : NodeKind) → 0 < m)
    (next : ∀ p, Fin (size p) → I)
    (r : ∀ p, Omega → probabilitySimplex (size p))
    (g : ∀ p, Omega → Fin (size p) → ℝ)
    (hr : ∀ p, Measurable (r p)) (hg : ∀ p, Measurable (g p))
    (t : ℕ) (p : I) :
    Measurable (fun w =>
      (categoricalPrefixStep size hk next (fun p => r p w) (fun p => g p w))^[t] p) := by
  have hstep : ∀ p, Measurable (fun w =>
      categoricalPrefixStep size hk next (fun p => r p w) (fun p => g p w) p) := by
    intro p
    apply (measurable_of_finite (next p)).comp
    apply firstArgmax_getD_measurable
    intro j
    change Measurable (fun w => extendedLog ((r p w).val j) + (g p w j : EReal))
    exact (extendedLog_measurable.comp
      ((measurable_pi_apply j).comp (measurable_subtype_coe.comp (hr p)))).add
      (measurable_coe_real_ereal.comp ((measurable_pi_apply j).comp (hg p)))
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    simp only [Function.iterate_succ_apply']
    have hpair : Measurable (fun z : Omega × I =>
        categoricalPrefixStep size hk next (fun p => r p z.1) (fun p => g p z.1) z.2) :=
      measurable_from_prod_countable_left hstep
    exact hpair.comp (measurable_id.prodMk ih)

/-- Suppose [G supplies random category scores at each prefix](hyp:G),
[the latent input is measurable](hyp:hU), [each score vector is measurable](hyp:hG),
[the latent input is independent of each score vector](hyp:hind), and
[each score vector has the standard Gumbel input law](hyp:hlaw).
Assume [the latent code is measurable](hyp:hcode), [a categorical probability
table is given for each prefix and code](hyp:table), [the probability error
tolerance a is nonnegative](hyp:ha), [every prefix has at least one category](hyp:hk),
and [successor prefixes are specified for each category](hyp:next).
For [random categorical probabilities](hyp:r) [within a of the coded table in
every coordinate](hyp:hr), if [the coded readout approximates each original
readout within c](hyp:herr), then [there is one measurable exceptional event of
probability at most $2a\sum_p\mathrm{size}(p)$ such that, for every realization,
horizon, and starting prefix, the distance between the original and table-based
terminal readouts is at most the nonnegative part of c plus the nonnegative
part of $2eB$ on that event](goal). -/
-- @node: simulation_prefix_readout_error_le
lemma simulation_prefix_readout_error_le
    {Omega I : Type*} [MeasurableSpace Omega] [Fintype I]
    {d e k : ℕ} {K B a c : ℝ}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (size : I → ℕ) (U : Omega → boundedCube d K)
    (G : ∀ p, Omega → Fin (size p) → ℝ)
    (hU : Measurable U) (hG : ∀ p, Measurable (G p))
    (hind : ∀ p, IndepFun U (G p) mu)
    (hlaw : ∀ p, mu.map (G p) = gumbelInputs (size p))
    (code : boundedCube d K → Fin k) (hcode : Measurable code)
    (table : ∀ p, Fin k → probabilitySimplex (size p)) (ha : 0 ≤ a)
    (hk : ∀ p m, Sum.inr (size p) = (Sum.inr m : NodeKind) → 0 < m)
    (next : ∀ p, Fin (size p) → I)
    (r : ∀ p, Omega → probabilitySimplex (size p))
    (hr : ∀ w p i, |(r p w).val i - (table p (code (U w))).val i| ≤ a)
    (f : I → boundedCube d K → boundedCube e B)
    (v : I → Fin k → boundedCube e B)
    (herr : ∀ p x, dist (f p x).val (v p (code x)).val ≤ c) :
    ∃ bad : Set Omega, MeasurableSet bad ∧
      mu bad ≤ ENNReal.ofReal (2 * (∑ p, (size p : ℝ)) * a) ∧
      ∀ w t p,
        edist
          (f ((categoricalPrefixStep size hk next (fun p => r p w)
            (fun p => G p w))^[t] p) (U w)).val
          (v ((categoricalPrefixStep size hk next (fun p => table p (code (U w)))
            (fun p => G p w))^[t] p) (code (U w))).val ≤
          ENNReal.ofReal c + bad.indicator (fun _ => ENNReal.ofReal (2 * e * B)) w := by
  classical
  obtain ⟨bad, hbad, hprob, hagree⟩ := simulation_prefix_table_path_agreement
    mu size U G hU hG hind hlaw code hcode table ha hk next
  refine ⟨bad, hbad, hprob, ?_⟩
  intro w t p
  by_cases hw : w ∈ bad
  · rw [Set.indicator_of_mem hw, edist_dist]
    apply le_trans (ENNReal.ofReal_le_ofReal ?_) (le_add_left le_rfl)
    calc
      dist _ _ ≤ ‖_‖ + ‖_‖ := dist_le_norm_add_norm _ _
      _ ≤ (e : ℝ) * B + (e : ℝ) * B :=
        add_le_add (boundedCube_norm_le (f _ _).property)
          (boundedCube_norm_le (v _ _).property)
      _ = 2 * e * B := by ring
  · rw [Set.indicator_of_notMem hw, add_zero,
      hagree w hw (fun p => r p w) (hr w), edist_dist]
    exact ENNReal.ofReal_le_ofReal (herr _ _)

/-- Suppose [every prefix has at least one category](hyp:hk),
[successor prefixes are specified for each category](hyp:next),
[the latent input is measurable](hyp:hU), [random category scores are given](hyp:g)
with [measurable score vectors](hyp:hg), [the latent code is measurable](hyp:hcode),
and [a categorical probability table is specified for each prefix and code](hyp:table).
Then [the pair consisting of the latent code and the prefix reached using the
coded tables after a fixed horizon from a fixed starting prefix is measurable](goal). -/
-- @node: simulation_prefix_table_type_measurable
@[fun_prop] lemma simulation_prefix_table_type_measurable
    {Omega I : Type*} [MeasurableSpace Omega] [Countable I]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    {d k : ℕ} {K : ℝ}
    (size : I → ℕ)
    (hk : ∀ p m, Sum.inr (size p) = (Sum.inr m : NodeKind) → 0 < m)
    (next : ∀ p, Fin (size p) → I)
    (U : Omega → boundedCube d K) (hU : Measurable U)
    (g : ∀ p, Omega → Fin (size p) → ℝ) (hg : ∀ p, Measurable (g p))
    (code : boundedCube d K → Fin k) (hcode : Measurable code)
    (table : ∀ p, Fin k → probabilitySimplex (size p)) (t : ℕ) (p : I) :
    Measurable (fun w => (code (U w),
      (categoricalPrefixStep size hk next (fun p => table p (code (U w)))
        (fun p => g p w))^[t] p)) := by
  fun_prop

/-- Suppose [a reference probability vector is available at each prefix](hyp:p0),
[G supplies random category scores](hyp:G), [the latent input is measurable](hyp:hU),
[the score vectors are measurable](hyp:hG), [the latent input is independent of
each score vector](hyp:hind), and [each score vector has the standard Gumbel input
law](hyp:hlaw). Assume [B is nonnegative](hyp:hB), [rho is nonnegative](hyp:hrho),
[eta is positive](hyp:heta), [L is a nonnegative Lipschitz bound](hyp:L),
[the latent code is measurable](hyp:hcode), [its grid representative approximates
every input within rho](hyp:hgrid), [every prefix has at least one category](hyp:hk),
and [successor prefixes are specified for each category](hyp:next). Then [there
are finite alphabets of probability and readout tables whose combined log
cardinality is at most
$\sum_p\mathrm{size}(p)k\log(2+\eta^{-1})+|I|ek\log(1+2B(e+1)/\eta)$;
every family of coordinatewise L-Lipschitz probabilities and L-Lipschitz readouts
admits tables and a measurable exceptional event of probability at most
$2\sum_p\mathrm{size}(p)(L\rho+\eta)$, with terminal readout error at most
$L\rho+\eta$ plus $2eB$ on that event, simultaneously for all realizations,
horizons, and starting prefixes](goal). -/
-- @node: exists_simulation_prefix_complete_tables
lemma exists_simulation_prefix_complete_tables
    {Omega I : Type*} [MeasurableSpace Omega] [Fintype I]
    {d e k : ℕ} {K B rho eta : ℝ}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (size : I → ℕ) (p0 : ∀ p, probabilitySimplex (size p))
    (U : Omega → boundedCube d K) (G : ∀ p, Omega → Fin (size p) → ℝ)
    (hU : Measurable U) (hG : ∀ p, Measurable (G p))
    (hind : ∀ p, IndepFun U (G p) mu)
    (hlaw : ∀ p, mu.map (G p) = gumbelInputs (size p))
    (hB : 0 ≤ B) (hrho : 0 ≤ rho) (heta : 0 < eta) (L : ℝ≥0)
    (grid : Fin k → boundedCube d K) (code : boundedCube d K → Fin k)
    (hcode : Measurable code)
    (hgrid : ∀ x, dist x.val (grid (code x)).val ≤ rho)
    (hk : ∀ p m, Sum.inr (size p) = (Sum.inr m : NodeKind) → 0 < m)
    (next : ∀ p, Fin (size p) → I) :
    ∃ P : Finset (∀ p, Fin k → probabilitySimplex (size p)),
    ∃ T : Finset (I → Fin k → boundedCube e B),
      Real.log (P.card : ℝ) + Real.log (T.card : ℝ) ≤
        (∑ p, ((size p * k : ℕ) : ℝ)) * Real.log (2 + eta⁻¹) +
        (∑ _p : I, ((e * k : ℕ) : ℝ)) * Real.log (1 + 2 * B * (e + 1) / eta) ∧
      ∀ r : ∀ p, boundedCube d K → probabilitySimplex (size p),
        (∀ p i, LipschitzWith L (fun x => (r p x).val i)) →
        ∀ f : I → boundedCube d K → boundedCube e B,
          (∀ p, LipschitzWith L (f p)) →
          ∃ table ∈ P, ∃ v ∈ T, ∃ bad : Set Omega, MeasurableSet bad ∧
            mu bad ≤ ENNReal.ofReal
              (2 * (∑ p, (size p : ℝ)) * ((L : ℝ) * rho + eta)) ∧
            ∀ w t p,
              edist
                (f ((categoricalPrefixStep size hk next (fun p => r p (U w))
                  (fun p => G p w))^[t] p) (U w)).val
                (v ((categoricalPrefixStep size hk next (fun p => table p (code (U w)))
                  (fun p => G p w))^[t] p) (code (U w))).val ≤
                ENNReal.ofReal ((L : ℝ) * rho + eta) +
                  bad.indicator (fun _ => ENNReal.ofReal (2 * e * B)) w := by
  obtain ⟨P, hP, happP⟩ := exists_simulation_prefix_table_net size p0 heta L grid code hgrid
  obtain ⟨T, hT, happT⟩ := exists_simulation_prefix_readout_net
    (I := I) hB heta L grid code hgrid
  refine ⟨P, T, add_le_add hP hT, ?_⟩
  intro r hr f hf
  obtain ⟨table, htable, herrP⟩ := happP r hr
  obtain ⟨v, hv, herrT⟩ := happT f hf
  obtain ⟨bad, hbad, hprob, herr⟩ := simulation_prefix_readout_error_le
    mu size U G hU hG hind hlaw code hcode table
    (by positivity : 0 ≤ (L : ℝ) * rho + eta) hk next
    (fun p w => r p (U w)) (fun w p => herrP p (U w)) f v herrT
  exact ⟨table, htable, v, hv, bad, hbad, hprob, herr⟩

end
end Papers.TbsNeuralCausalPi
