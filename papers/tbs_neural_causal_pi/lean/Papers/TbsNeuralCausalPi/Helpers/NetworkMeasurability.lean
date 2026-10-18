module
public import Papers.TbsNeuralCausalPi.Helpers.ReLUDepthPadding
public import Papers.TbsNeuralCausalPi.Helpers.NetworkClipping
public import Papers.TbsNeuralCausalPi.Helpers.GumbelSoftmax
/-! # Measurability of structural and generator networks

These facts depend only on the concrete networks and their input laws. Keeping
this layer upstream of model approximation allows the architecture construction
to use it without importing the estimation assumptions.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped ENNReal NNReal

-- @node: ReLUNet.eval_measurable
/-- [The input-to-output function of every ReLU network is measurable](goal). -/
@[fun_prop] lemma ReLUNet.eval_measurable {k o W L : ℕ} (q : ReLUNet k o W L) :
    Measurable q.eval := by
  induction L generalizing k with
  | zero =>
    rcases q with ⟨ls, hd, hw, hf, hc, ow, ob⟩
    have hs : ls = [] := List.length_eq_zero_iff.mp hd
    subst ls
    change Measurable (fun x : L1Vec k => WithLp.toLp 1 (fun j =>
      (∑ i : Fin k, ow j i * (if h : i.val < k then x.ofLp ⟨i.val, h⟩ else 0)) + ob j))
    simp only [dif_pos (Fin.isLt _)]
    fun_prop
  | succ L ih =>
    obtain ⟨l, hl, hw, r, rfl⟩ := exists_relu_head q
    have he : (prependNet l hl hw r).eval = r.eval ∘ layerVector l := by
      funext x
      exact prependNet_eval l hl hw r x
    rw [he]
    apply (ih r).comp
    subst k
    unfold layerVector reluLayer AffineLayer.apply
    simp only [dif_pos (Fin.isLt _)]
    fun_prop

-- @node: coordinateClamp_measurable
/-- [Coordinatewise clamping to any given lower and upper bounds is a measurable
function of the input vector](goal). -/
@[fun_prop] lemma coordinateClamp_measurable {d : ℕ} (a b : ℝ) :
    Measurable (coordinateClamp (d := d) a b) := by
  exact (coordinateClamp_lipschitz a b).continuous.measurable

-- @node: gumbelSoftmaxMix_eq_sum
/-- [The Gumbel mixture of a finite collection of vectors equals their weighted sum,
using hard selection weights at zero temperature and softmax weights otherwise](goal). -/
lemma gumbelSoftmaxMix_eq_sum {n d : ℕ} (V : Fin n → L1Vec d)
    (p : Fin n → ℝ) (tau : ℝ) (G : Fin n → ℝ) :
    gumbelSoftmaxMix V p tau G =
      ∑ i, (if tau = 0 then hardWeights p G else softmaxWeights p tau G).ofLp i • V i := by
  apply WithLp.ofLp_injective 1
  funext j
  simp [gumbelSoftmaxMix, mul_comm]

-- @node: generatorInputLaw_probability
/-- [The joint law of the generator's uniform inputs and Gumbel inputs is a probability
measure for any number of mixture components](goal). -/
lemma generatorInputLaw_probability (n : ℕ) : IsProbabilityMeasure (generatorInputLaw n) := by
  let : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := ⟨by simp⟩
  let := gumbelInputs_probability n
  unfold generatorInputLaw
  infer_instance

-- @node: gumbelSoftmaxMix_measurable
/-- With [at least one mixture component](hyp:hn), if [each component vector depends
measurably on the underlying outcome](hyp:hV) and [the Gumbel input vector is
measurable](hyp:hG), [the Gumbel mixture is measurable for any fixed weights and
temperature](goal). -/
@[fun_prop] lemma gumbelSoftmaxMix_measurable
    {Ω : Type*} [MeasurableSpace Ω] {n d : ℕ} (hn : 0 < n)
    (V : Ω → Fin n → L1Vec d) (hV : ∀ i, Measurable (fun x => V x i))
    (p : Fin n → ℝ) (tau : ℝ) (G : Ω → Fin n → ℝ) (hG : Measurable G) :
    Measurable (fun x => gumbelSoftmaxMix (V x) p tau (G x)) := by
  let : BorelSpace (L1Vec d) := ⟨rfl⟩
  let : BorelSpace (L1Vec n) := ⟨rfl⟩
  have hw : Measurable (fun x =>
      if tau = 0 then hardWeights p (G x) else softmaxWeights p tau (G x)) := by
    split_ifs
    · exact (hardWeights_measurable hn p).comp hG
    · exact (softmaxWeights_measurable p tau).comp hG
  simp_rw [gumbelSoftmaxMix_eq_sum]
  apply Finset.measurable_sum
  intro i _
  exact ((measurable_pi_apply i).comp
    ((PiLp.continuous_ofLp 1 _).measurable.comp hw)).smul (hV i)

-- @node: ThreePartGenerator.eval_measurable
/-- [The output of every three-part generator is a measurable function of its uniform
and Gumbel input vectors](goal). -/
@[fun_prop] lemma ThreePartGenerator.eval_measurable {n d : ℕ} {dC : Fin n → ℕ}
    {W1 L1 W2 L2 : ℕ} {tau : ℝ}
    (Q : ThreePartGenerator n d dC W1 L1 W2 L2 tau) : Measurable Q.eval := by
  let : BorelSpace (L1Vec d) := ⟨rfl⟩
  let : BorelSpace (L1Vec n) := ⟨rfl⟩
  unfold ThreePartGenerator.eval
  simp only [gumbelSoftmaxMix_eq_sum, if_neg (ne_of_gt Q.temperature)]
  have hw : Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      softmaxWeights Q.p tau z.2) := (softmaxWeights_measurable Q.p tau).comp measurable_snd
  apply Finset.measurable_sum
  intro i _
  exact ((measurable_pi_apply i).comp
    ((PiLp.continuous_ofLp 1 _).measurable.comp hw)).smul (by fun_prop)

end Papers.TbsNeuralCausalPi
