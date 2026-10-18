module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Domain of real iterated objective expectations -/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
noncomputable section

variable {I U : Type*} [MeasurableSpace I] [MeasurableSpace U]

/-- For [an outer measure on intervention indices](hyp:muT), [an inner
measure on latent inputs](hyp:muU), and [a real objective depending on both](hyp:f),
[the iterated objective is defined](goal) when [the objective is integrable
over latent inputs for almost every intervention index](step:1) and
[these inner expectations are integrable over intervention indices](step:2). -/
-- @node: iteratedObjectiveDefined
def iteratedObjectiveDefined (muT : Measure I) (muU : Measure U)
    (f : I → U → ℝ) : Prop :=
  (∀ᵐ s ∂muT, Integrable (f s) muU) ∧
    Integrable (fun s => ∫ u, f s u ∂muU) muT

/-- Given [an outer measure on intervention indices](hyp:muT), [an inner
measure on latent inputs](hyp:muU), [a real objective depending on both](hyp:f),
and [integrability of the inner objectives almost everywhere and of their
outer expectation](hyp:_h), the [finite iterated objective](goal) is the
expectation over intervention indices of the latent-input expectation. -/
-- @node: finiteIteratedObjective
def finiteIteratedObjective (muT : Measure I) (muU : Measure U)
    (f : I → U → ℝ) (_h : iteratedObjectiveDefined muT muU f) : ℝ :=
  ∫ s, ∫ u, f s u ∂muU ∂muT

/-- If [two objectives agree for almost every latent input at almost every
intervention index](hyp:hfg) and [the first has integrable inner objectives
almost everywhere and an integrable outer expectation](hyp:hf), then
[the second satisfies the same iterated integrability requirements](goal). -/
-- @node: iteratedObjectiveDefined_congr
lemma iteratedObjectiveDefined_congr {muT : Measure I} {muU : Measure U}
    {f g : I → U → ℝ} (hfg : ∀ᵐ s ∂muT, f s =ᵐ[muU] g s)
    (hf : iteratedObjectiveDefined muT muU f) :
    iteratedObjectiveDefined muT muU g := by
  constructor
  · filter_upwards [hf.1, hfg] with s hs heq
    exact hs.congr heq
  · apply hf.2.congr
    filter_upwards [hfg] with s heq
    exact integral_congr_ae heq

/-- If [the first objective satisfies the iterated integrability requirements](hyp:hf),
[the second satisfies those requirements](hyp:hg), and [the objectives agree
for almost every latent input at almost every intervention index](hyp:hfg),
then [their finite iterated expectations are equal](goal). -/
-- @node: finiteIteratedObjective_congr
lemma finiteIteratedObjective_congr {muT : Measure I} {muU : Measure U}
    {f g : I → U → ℝ} (hf : iteratedObjectiveDefined muT muU f)
    (hg : iteratedObjectiveDefined muT muU g)
    (hfg : ∀ᵐ s ∂muT, f s =ᵐ[muU] g s) :
    finiteIteratedObjective muT muU f hf = finiteIteratedObjective muT muU g hg := by
  apply integral_congr_ae
  filter_upwards [hfg] with s heq
  exact integral_congr_ae heq

end
end Papers.TbsNeuralCausalPi
