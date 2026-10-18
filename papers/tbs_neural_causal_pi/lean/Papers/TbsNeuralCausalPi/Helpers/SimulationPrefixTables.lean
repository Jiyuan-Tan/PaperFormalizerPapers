module
public import Papers.TbsNeuralCausalPi.Helpers.SimulationCubeGrid
/-! # Joint finite tables for every categorical prefix

All prefix propensities use a single joint-latent code. Their finite table
alphabet is chosen before the propensity maps, and its entropy adds over
prefixes. One ambiguity event then controls every prefix simultaneously,
including adaptive choices of nearby propensities and zero simplex weights.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

/-- Given [a category count for each prefix](hyp:size), [a reference probability
vector at each prefix](hyp:p0), [a positive tolerance η](hyp:heta), and
[a nonnegative Lipschitz bound L](hyp:L), use [latent grid points](hyp:grid)
and [a grid encoder](hyp:code) such that [every latent point is within ρ of its
encoded grid point](hyp:hgrid). Then [there is a finite collection of joint
prefix tables whose log cardinality is at most the sum of the category counts
times the grid size times log(2 + 1/η), and every family of coordinatewise
L-Lipschitz probability maps has a table approximating every coordinate
uniformly within Lρ + η](goal). -/
-- @node: exists_simulation_prefix_table_net
lemma exists_simulation_prefix_table_net
    {I : Type*} [Fintype I] {d k : ℕ} {K rho eta : ℝ}
    (size : I → ℕ) (p0 : ∀ p, probabilitySimplex (size p))
    (heta : 0 < eta) (L : ℝ≥0)
    (grid : Fin k → boundedCube d K) (code : boundedCube d K → Fin k)
    (hgrid : ∀ x, dist x.val (grid (code x)).val ≤ rho) :
    ∃ T : Finset (∀ p, Fin k → probabilitySimplex (size p)),
      Real.log (T.card : ℝ) ≤
        (∑ p, ((size p * k : ℕ) : ℝ)) * Real.log (2 + eta⁻¹) ∧
      ∀ f : ∀ p, boundedCube d K → probabilitySimplex (size p),
        (∀ p i, LipschitzWith L (fun x => (f p x).val i)) →
        ∃ table ∈ T, ∀ p x i,
          |(f p x).val i - (table p (code x)).val i| ≤ (L : ℝ) * rho + eta := by
  classical
  have hlocal := fun p => exists_simulation_simplex_tables_on_grid
    heta L (p0 p) grid code hgrid
  choose alph habudget happrox using hlocal
  have hnonempty : ∀ p, (alph p).Nonempty := by
    intro p
    obtain ⟨t, ht, _⟩ := happrox p (fun _ => p0 p)
      (fun _ => (LipschitzWith.const _).weaken (by positivity))
    exact ⟨t, ht⟩
  refine ⟨Fintype.piFinset alph, ?_, ?_⟩
  · rw [Fintype.card_piFinset, Nat.cast_prod,
      Real.log_prod (fun p _ => by exact_mod_cast (hnonempty p).card_pos.ne')]
    calc
      _ ≤ ∑ p, ((size p * k : ℕ) : ℝ) * Real.log (2 + eta⁻¹) :=
        Finset.sum_le_sum (fun p _ => habudget p)
      _ = _ := (Finset.sum_mul ..).symm
  · intro f hf
    choose table hmem herr using fun p => happrox p (f p) (hf p)
    exact ⟨table, Fintype.mem_piFinset.mpr hmem, herr⟩

/-- Under [the probability measure μ](hyp:mu), let [each prefix have its given
category count](hyp:size), [U be the latent vector](hyp:U), and [G provide the
noise block for each prefix](hyp:G). If [U is measurable](hyp:hU), [each noise
block is measurable](hyp:hG), [U is independent of each block](hyp:hind),
[each block has the standard Gumbel input law](hyp:hlaw), [the latent encoder](hyp:code)
[is measurable](hyp:hcode), [the tables contain probability vectors](hyp:table),
[the coordinate tolerance a is nonnegative](hyp:ha), and [each prefix has
positive category count](hyp:hk), then [there is one measurable exceptional
event of probability at most twice a times the sum of the category counts,
outside which every prefix's selector agrees with its table selector for
every probability vector within coordinatewise distance a of the table](goal). -/
-- @node: simulation_prefix_table_robust_agreement
lemma simulation_prefix_table_robust_agreement
    {Omega I : Type*} [MeasurableSpace Omega] [Fintype I]
    {d k : ℕ} {K a : ℝ}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (size : I → ℕ) (U : Omega → boundedCube d K)
    (G : ∀ p, Omega → Fin (size p) → ℝ)
    (hU : Measurable U) (hG : ∀ p, Measurable (G p))
    (hind : ∀ p, IndepFun U (G p) mu)
    (hlaw : ∀ p, mu.map (G p) = gumbelInputs (size p))
    (code : boundedCube d K → Fin k) (hcode : Measurable code)
    (table : ∀ p, Fin k → probabilitySimplex (size p)) (ha : 0 ≤ a)
    (hk : ∀ p m, Sum.inr (size p) = (Sum.inr m : NodeKind) → 0 < m) :
    ∃ bad : Set Omega, MeasurableSet bad ∧
      mu bad ≤ ENNReal.ofReal (2 * (∑ p, (size p : ℝ)) * a) ∧
      ∀ w ∉ bad, ∀ p, ∀ r : probabilitySimplex (size p),
        (∀ i, |r.val i - (table p (code (U w))).val i| ≤ a) →
        canonicalSelector (.inr (size p)) (hk p) (WithLp.toLp 1 r.val)
          (WithLp.toLp 1 (G p w)) =
        canonicalSelector (.inr (size p)) (hk p)
          (WithLp.toLp 1 (table p (code (U w))).val) (WithLp.toLp 1 (G p w)) := by
  let q := fun p x => (table p (code x)).val
  have hq : ∀ p, Measurable (q p) := by intro p; fun_prop
  have hpos : ∀ p x i, 0 ≤ q p x i := fun p x => (table p (code x)).property.1
  have hsum : ∀ p x, ∑ i, q p x i = 1 := fun p x => (table p (code x)).property.2
  refine ⟨{w | CategoricalTableAmbiguity size U G q a w},
    measurableSet_categoricalTableAmbiguity size U G q hU hG hq a,
    categoricalTableAmbiguity_probability_le mu size U G q hU hG hind hlaw
      hq hpos hsum a ha, ?_⟩
  intro w hw p r hr
  exact categoricalTable_noAmbiguity_selector_agreement size U G q hpos hsum a ha hk
    w hw p r.val r.property.1 r.property.2 hr

/-- For [the category counts at each prefix](hyp:size), [positive category
counts](hyp:hk), [a rule giving the next prefix for each selected category](hyp:next),
[prefix probability vectors](hyp:r), [prefix noise vectors](hyp:g), and
[the current prefix](hyp:p), [the categorical prefix transition](goal) applies
the next-prefix rule to the category chosen by the canonical selector using
the current probability and noise vectors. -/
-- @node: categoricalPrefixStep
def categoricalPrefixStep {I : Type*} (size : I → ℕ)
    (hk : ∀ p m, Sum.inr (size p) = (Sum.inr m : NodeKind) → 0 < m)
    (next : ∀ p, Fin (size p) → I)
    (r : ∀ p, probabilitySimplex (size p))
    (g : ∀ p, Fin (size p) → ℝ) (p : I) : I :=
  next p (canonicalSelector (.inr (size p)) (hk p)
    (WithLp.toLp 1 (r p).val) (WithLp.toLp 1 (g p)))

/-- Under [the probability measure μ](hyp:mu), take [prefix category counts](hyp:size),
[a latent vector U](hyp:U), [prefix noise blocks G](hyp:G), and [a latent
encoder](hyp:code) with [probability tables](hyp:table) and [a next-prefix rule](hyp:next).
Assume [U is measurable](hyp:hU), [the noise blocks are measurable](hyp:hG),
[each block is independent of U](hyp:hind), [each has the standard Gumbel
input law](hyp:hlaw), [the encoder is measurable](hyp:hcode), [a is
nonnegative](hyp:ha), and [all category counts are positive](hyp:hk).
Then [one measurable event of probability at most twice a times the sum of
the category counts contains every disagreement between paths driven by
the tables and by any coordinatewise a-close prefix probability vectors,
simultaneously for every horizon and starting prefix](goal). -/
-- @node: simulation_prefix_table_path_agreement
lemma simulation_prefix_table_path_agreement
    {Omega I : Type*} [MeasurableSpace Omega] [Fintype I]
    {d k : ℕ} {K a : ℝ}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (size : I → ℕ) (U : Omega → boundedCube d K)
    (G : ∀ p, Omega → Fin (size p) → ℝ)
    (hU : Measurable U) (hG : ∀ p, Measurable (G p))
    (hind : ∀ p, IndepFun U (G p) mu)
    (hlaw : ∀ p, mu.map (G p) = gumbelInputs (size p))
    (code : boundedCube d K → Fin k) (hcode : Measurable code)
    (table : ∀ p, Fin k → probabilitySimplex (size p)) (ha : 0 ≤ a)
    (hk : ∀ p m, Sum.inr (size p) = (Sum.inr m : NodeKind) → 0 < m)
    (next : ∀ p, Fin (size p) → I) :
    ∃ bad : Set Omega, MeasurableSet bad ∧
      mu bad ≤ ENNReal.ofReal (2 * (∑ p, (size p : ℝ)) * a) ∧
      ∀ w ∉ bad, ∀ r : ∀ p, probabilitySimplex (size p),
        (∀ p i, |(r p).val i - (table p (code (U w))).val i| ≤ a) →
        ∀ t p,
          (categoricalPrefixStep size hk next r (fun p => G p w))^[t] p =
          (categoricalPrefixStep size hk next
            (fun p => table p (code (U w))) (fun p => G p w))^[t] p := by
  obtain ⟨bad, hbad, hprob, hagree⟩ := simulation_prefix_table_robust_agreement
    mu size U G hU hG hind hlaw code hcode table ha hk
  refine ⟨bad, hbad, hprob, ?_⟩
  intro w hw r hr
  have hstep : categoricalPrefixStep size hk next r (fun p => G p w) =
      categoricalPrefixStep size hk next (fun p => table p (code (U w)))
        (fun p => G p w) := by
    funext p
    unfold categoricalPrefixStep
    rw [hagree w hw p (r p) (hr p)]
  intro t p
  rw [hstep]

/-- Under [the probability measure μ](hyp:mu), take [prefix category counts](hyp:size),
[a latent vector U](hyp:U), [prefix noise blocks G](hyp:G), [a latent encoder](hyp:code),
[probability tables](hyp:table), [a next-prefix rule](hyp:next), and
[random prefix probability vectors](hyp:r). Assume [U is measurable](hyp:hU),
[the noise blocks are measurable](hyp:hG), [each block is independent of U](hyp:hind),
[each has the standard Gumbel input law](hyp:hlaw), [the encoder is measurable](hyp:hcode),
[a is nonnegative](hyp:ha), [the category counts are positive](hyp:hk), and
[the random probabilities stay within a of the encoded table in every
coordinate](hyp:hr). Then [the probability of a path disagreement at any
horizon from any starting prefix is at most twice a times the sum of the
category counts](goal). -/
-- @node: simulation_prefix_table_path_failure_le
lemma simulation_prefix_table_path_failure_le
    {Omega I : Type*} [MeasurableSpace Omega] [Fintype I]
    {d k : ℕ} {K a : ℝ}
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
    (hr : ∀ w p i, |(r p w).val i - (table p (code (U w))).val i| ≤ a) :
    mu {w | ∃ t p,
      (categoricalPrefixStep size hk next (fun p => r p w) (fun p => G p w))^[t] p ≠
      (categoricalPrefixStep size hk next
        (fun p => table p (code (U w))) (fun p => G p w))^[t] p} ≤
      ENNReal.ofReal (2 * (∑ p, (size p : ℝ)) * a) := by
  obtain ⟨bad, _, hprob, hagree⟩ := simulation_prefix_table_path_agreement
    mu size U G hU hG hind hlaw code hcode table ha hk next
  apply le_trans (measure_mono ?_) hprob
  rintro w ⟨t, p, hne⟩
  by_contra hw
  exact hne (hagree w hw (fun p => r p w) (hr w) t p)

/-- Under [the probability measure μ](hyp:mu), take [prefix category counts](hyp:size),
[reference probability vectors](hyp:p0), [a latent vector U](hyp:U),
[prefix noise blocks G](hyp:G), [a nonnegative Lipschitz bound L](hyp:L),
[latent grid points](hyp:grid), [a latent encoder](hyp:code), and [a
next-prefix rule](hyp:next). Assume [U is measurable](hyp:hU), [the noise
blocks are measurable](hyp:hG), [each block is independent of U](hyp:hind),
[each has the standard Gumbel input law](hyp:hlaw), [ρ is nonnegative](hyp:hrho),
[η is positive](hyp:heta), [the encoder is measurable](hyp:hcode),
[encoding moves each latent point by at most ρ](hyp:hgrid), and [all category
counts are positive](hyp:hk). Then [there is a finite collection of joint
tables with log cardinality at most the sum of the category counts times
the grid size times log(2 + 1/η); every coordinatewise L-Lipschitz family
admits a table with uniform coordinate error at most Lρ + η and a measurable
exceptional event of probability at most twice (Lρ + η) times the sum of the
category counts, outside which the original and table paths agree at every
horizon from every starting prefix](goal). -/
-- @node: exists_simulation_prefix_path_tables
lemma exists_simulation_prefix_path_tables
    {Omega I : Type*} [MeasurableSpace Omega] [Fintype I]
    {d k : ℕ} {K rho eta : ℝ}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (size : I → ℕ) (p0 : ∀ p, probabilitySimplex (size p))
    (U : Omega → boundedCube d K) (G : ∀ p, Omega → Fin (size p) → ℝ)
    (hU : Measurable U) (hG : ∀ p, Measurable (G p))
    (hind : ∀ p, IndepFun U (G p) mu)
    (hlaw : ∀ p, mu.map (G p) = gumbelInputs (size p))
    (hrho : 0 ≤ rho) (heta : 0 < eta) (L : ℝ≥0)
    (grid : Fin k → boundedCube d K) (code : boundedCube d K → Fin k)
    (hcode : Measurable code)
    (hgrid : ∀ x, dist x.val (grid (code x)).val ≤ rho)
    (hk : ∀ p m, Sum.inr (size p) = (Sum.inr m : NodeKind) → 0 < m)
    (next : ∀ p, Fin (size p) → I) :
    ∃ T : Finset (∀ p, Fin k → probabilitySimplex (size p)),
      Real.log (T.card : ℝ) ≤
        (∑ p, ((size p * k : ℕ) : ℝ)) * Real.log (2 + eta⁻¹) ∧
      ∀ f : ∀ p, boundedCube d K → probabilitySimplex (size p),
        (∀ p i, LipschitzWith L (fun x => (f p x).val i)) →
        ∃ table ∈ T, ∃ bad : Set Omega, MeasurableSet bad ∧
          mu bad ≤ ENNReal.ofReal
            (2 * (∑ p, (size p : ℝ)) * ((L : ℝ) * rho + eta)) ∧
          (∀ p x i, |(f p x).val i - (table p (code x)).val i| ≤
            (L : ℝ) * rho + eta) ∧
          ∀ w ∉ bad, ∀ t p,
            (categoricalPrefixStep size hk next (fun p => f p (U w))
              (fun p => G p w))^[t] p =
            (categoricalPrefixStep size hk next (fun p => table p (code (U w)))
              (fun p => G p w))^[t] p := by
  obtain ⟨T, hT, happrox⟩ := exists_simulation_prefix_table_net
    size p0 heta L grid code hgrid
  refine ⟨T, hT, ?_⟩
  intro f hf
  obtain ⟨table, htable, herr⟩ := happrox f hf
  obtain ⟨bad, hbad, hprob, hagree⟩ := simulation_prefix_table_path_agreement
    mu size U G hU hG hind hlaw code hcode table
      (by positivity : 0 ≤ (L : ℝ) * rho + eta) hk next
  refine ⟨table, htable, bad, hbad, hprob, herr, ?_⟩
  intro w hw
  exact hagree w hw (fun p => f p (U w)) (fun p => herr p (U w))

end
end Papers.TbsNeuralCausalPi
