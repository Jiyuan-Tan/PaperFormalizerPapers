module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fin.Basic

/-! # Shared four-state notation

The uniform spin takes values in `Fin 4`; posterior vectors have four real coordinates.
-/

@[expose] public section

namespace OaiCapacityCriterionState

/-- The [uniform probability vector on four states](goal) assigns mass one quarter to each state.
@realizes \unif(the uniform probability vector, all four coordinates equal to 1/4)
-/
noncomputable def unifVec : Fin 4 → ℝ := fun _ => 1 / 4

/-- For [a real mixing weight](hyp:lam), [an input state](hyp:i), and
[an output state](hyp:j), the [symmetric channel entry](goal) is the weight times
the indicator that the states coincide, plus one quarter of one minus the weight.
@realizes P_\lambda(the four-state symmetric transition matrix)
-/
noncomputable def channel (lam : ℝ) (i j : Fin 4) : ℝ :=
  lam * (if i = j then 1 else 0) + (1 - lam) / 4

/-- For [a real channel weight](hyp:t), [an input state](hyp:I), and
[an output state](hyp:J), the [joint mass of the uniform input and its channel
output](goal) is one quarter of the corresponding symmetric channel entry. -/
noncomputable def channelStepJoint (t : ℝ)
    (I : Fin 4) -- @realizes I(input spin in Fin 4, with uniform mass 1/4)
    (J : Fin 4) : ℝ := -- @realizes J(output spin in Fin 4, with transition P_t)
  (1 / 4) * channel t I J

end OaiCapacityCriterionState
