module

public import Papers.OaiSmoothNonquadraticAffine.Helpers.ContinuationExistence

/-! # Uniqueness for positive regular radial state curves

Local Lipschitz continuity of the smooth augmented field gives uniqueness near
any common state. Connectedness propagates this agreement along an interval.
-/

public section

open Set Filter
open scoped Topology ContDiff

namespace OaiSmoothNonquadraticAffine

/-- If [the first state curve has nonzero pressure at t](hyp:hP) and [nonzero
profile slope at t](hyp:hy), [the first curve solves the continuation ODE in a
neighborhood of t](hyp:hu), [the second curve also solves it in a neighborhood
of t](hyp:hv), and [the curves have the same state at t](hyp:heq), [they agree
throughout some neighborhood of t](goal). -/
-- @node: continuation_state_eventuallyEq
lemma continuation_state_eventuallyEq {u v : ℝ → Fin 4 → ℝ} {t : ℝ}
    (hP : u t 1 ≠ 0) (hy : u t 2 ≠ 0)
    (hu : ∀ᶠ r in 𝓝 t, HasDerivAt u (continuationField (r, u r)) r)
    (hv : ∀ᶠ r in 𝓝 t, HasDerivAt v (continuationField (r, v r)) r)
    (heq : u t = v t) : u =ᶠ[𝓝 t] v := by
  let f := fun q : ℝ × (Fin 4 → ℝ) => ((1 : ℝ), continuationField q)
  have hs : ContDiffAt ℝ 1 f (t, u t) :=
    (continuation_augmented_contDiffAt hP hy).of_le (by norm_num)
  obtain ⟨K, U, hU, hLip⟩ := hs.exists_lipschitzOnWith
  have huc : ContinuousAt (fun r => (r, u r)) t :=
    continuousAt_id.prodMk (hu.self_of_nhds.continuousAt)
  have hvc : ContinuousAt (fun r => (r, v r)) t :=
    continuousAt_id.prodMk (hv.self_of_nhds.continuousAt)
  have hvU : U ∈ 𝓝 (t, v t) := by simpa only [← heq] using hU
  have haug : (fun r => (r, u r)) =ᶠ[𝓝 t] (fun r => (r, v r)) := by
    apply ODE_solution_unique_of_eventually (v := fun _ => f) (s := fun _ => U)
      (Filter.Eventually.of_forall (fun _ => hLip))
    · filter_upwards [hu, huc.eventually hU] with r hr hrU
      exact ⟨(hasDerivAt_id r).prodMk hr, hrU⟩
    · filter_upwards [hv, hvc.eventually hvU] with r hr hrU
      exact ⟨(hasDerivAt_id r).prodMk hr, hrU⟩
    · exact congrArg (fun w => (t, w)) heq
  exact haug.mono (fun r hr => congrArg Prod.snd hr)

/-- Suppose [a set of radii is open](hyp:hJ) and [connected](hyp:hc), [t belongs
to the set](hyp:ht), and [the first state curve has nonzero pressure and profile
slope everywhere in the set](hyp:hpos). If [the first curve solves the
continuation ODE on the set](hyp:hu), [the second curve solves it there](hyp:hv),
and [their states agree at t](hyp:heq), [the curves agree everywhere in the
set](goal). -/
-- @node: continuation_state_eqOn
lemma continuation_state_eqOn {u v : ℝ → Fin 4 → ℝ} {J : Set ℝ} {t : ℝ}
    (hJ : IsOpen J) (hc : IsPreconnected J) (ht : t ∈ J)
    (hpos : ∀ r ∈ J, u r 1 ≠ 0 ∧ u r 2 ≠ 0)
    (hu : ∀ r ∈ J, HasDerivAt u (continuationField (r, u r)) r)
    (hv : ∀ r ∈ J, HasDerivAt v (continuationField (r, v r)) r)
    (heq : u t = v t) : EqOn u v J := by
  let : PreconnectedSpace J := isPreconnected_iff_preconnectedSpace.mp hc
  have huc : ContinuousOn u J := fun r hr => (hu r hr).continuousAt.continuousWithinAt
  have hvc : ContinuousOn v J := fun r hr => (hv r hr).continuousAt.continuousWithinAt
  have hclosed : IsClosed {r : J | u r = v r} :=
    isClosed_eq huc.domRestrict hvc.domRestrict
  have hopen : IsOpen {r : J | u r = v r} := by
    rw [isOpen_iff_mem_nhds]
    intro r hr
    have hlocal := continuation_state_eventuallyEq (hpos r r.property).1
      (hpos r r.property).2
      (Filter.Eventually.mono (hJ.mem_nhds r.property) (fun s hs => hu s hs))
      (Filter.Eventually.mono (hJ.mem_nhds r.property) (fun s hs => hv s hs)) hr
    exact continuous_subtype_val.continuousAt.eventually hlocal
  have hall := (show IsClopen {r : J | u r = v r} from ⟨hclosed, hopen⟩).eq_univ
    (show ({r : J | u r = v r}).Nonempty from ⟨⟨t, ht⟩, heq⟩)
  intro r hr
  have : (⟨r, hr⟩ : J) ∈ {r : J | u r = v r} := by rw [hall]; trivial
  exact this

/-- Suppose [a set of radii is open](hyp:hJ) and [connected](hyp:hc), [t belongs
to the set](hyp:ht), [the first profile-pressure pair satisfies the radial
system there](hyp:hFP), and [the second pair satisfies the same system
there](hyp:hGQ). If [the first pressure and both profile slopes are nonzero
throughout the set](hyp:hpos), [the profiles agree near t](hyp:hF), and [the
pressures agree near t](hyp:hP), [the two four-coordinate states consisting of
profile, pressure, and their first derivatives agree everywhere in the
set](goal). -/
-- @node: radialSystem_state_eqOn
lemma radialSystem_state_eqOn {F P G Q : ℝ → ℝ} {J : Set ℝ} {t : ℝ}
    (hJ : IsOpen J) (hc : IsPreconnected J) (ht : t ∈ J)
    (hFP : RadialSystem radialDim radialK radialGamma F P J)
    (hGQ : RadialSystem radialDim radialK radialGamma G Q J)
    (hpos : ∀ r ∈ J, P r ≠ 0 ∧ deriv F r ≠ 0 ∧ deriv G r ≠ 0)
    (hF : F =ᶠ[𝓝 t] G) (hP : P =ᶠ[𝓝 t] Q) :
    EqOn (fun r => ![F r, P r, deriv F r, deriv P r])
      (fun r => ![G r, Q r, deriv G r, deriv Q r]) J := by
  apply continuation_state_eqOn hJ hc ht
    (fun r hr => by simpa using ⟨(hpos r hr).1, (hpos r hr).2.1⟩)
    (fun r hr => radialSystem_state_hasDerivAt hFP hr (hpos r hr).2.1)
    (fun r hr => radialSystem_state_hasDerivAt hGQ hr (hpos r hr).2.2)
  rw [hF.eq_of_nhds, hP.eq_of_nhds, hF.deriv_eq, hP.deriv_eq]

/-- Suppose [ε is positive](hyp:hε), [the first outer endpoint is at least
ε](hyp:hR), [the second outer endpoint is at least ε](hyp:hS), [the first
profile-pressure pair is a positive radial solution up to its endpoint](hyp:hFP),
and [the second pair is a positive radial solution up to its endpoint](hyp:hGQ).
If [the first pair agrees with the initial profiles from zero inclusive to ε
exclusive](hyp:heqF) and [the second pair agrees with those same initial profiles
on that interval](hyp:heqG), [both profiles and both pressures agree at every
radius common to their solution intervals](goal). -/
-- @node: positiveRadialSolution_eqOn_overlap
lemma positiveRadialSolution_eqOn_overlap {ε : ℝ} {F₀ P₀ F P G Q : ℝ → ℝ}
    {R S : WithTop ℝ} (hε : 0 < ε) (hR : (ε : WithTop ℝ) ≤ R)
    (hS : (ε : WithTop ℝ) ≤ S)
    (hFP : PositiveRadialSolution F P R) (hGQ : PositiveRadialSolution G Q S)
    (heqF : ∀ r ∈ Ico 0 ε, F r = F₀ r ∧ P r = P₀ r)
    (heqG : ∀ r ∈ Ico 0 ε, G r = F₀ r ∧ Q r = P₀ r) :
    ∀ r ∈ radialInterval R ∩ radialInterval S, F r = G r ∧ P r = Q r := by
  let J := radialInterval (min R S)
  have hJ : J = radialInterval R ∩ radialInterval S := by
    ext r
    simp only [J, radialInterval, mem_ofPred_eq, lt_min_iff, mem_inter_iff]
    tauto
  have hopen : IsOpen J := by
    change IsOpen (radialInterval (min R S))
    cases min R S using WithTop.recTopCoe with
    | top => simpa [radialInterval, Set.Ioi, Set.Ioo] using (isOpen_Ioi : IsOpen (Ioi (0 : ℝ)))
    | coe b => simpa [radialInterval, Set.Ioi, Set.Ioo] using (isOpen_Ioo : IsOpen (Ioo (0 : ℝ) b))
  have hc : IsPreconnected J := by
    change IsPreconnected (radialInterval (min R S))
    cases min R S using WithTop.recTopCoe with
    | top => simpa [radialInterval, Set.Ioi, Set.Ioo] using (convex_Ioi (0 : ℝ)).isPreconnected
    | coe b => simpa [radialInterval, Set.Ioi, Set.Ioo] using (convex_Ioo (0 : ℝ) b).isPreconnected
  have htε : ε / 2 ∈ Ioo 0 ε := ⟨by linarith, by linarith⟩
  have ht : ε / 2 ∈ J := by
    exact ⟨htε.1, lt_min
      ((show ((ε / 2 : ℝ) : WithTop ℝ) < ε by exact_mod_cast htε.2).trans_le hR)
      ((show ((ε / 2 : ℝ) : WithTop ℝ) < ε by exact_mod_cast htε.2).trans_le hS)⟩
  have hlocal : ∀ᶠ r in 𝓝 (ε / 2), F r = G r ∧ P r = Q r := by
    filter_upwards [isOpen_Ioo.mem_nhds htε] with r hr
    have hm : r ∈ Ico 0 ε := ⟨hr.1.le, hr.2⟩
    exact ⟨(heqF r hm).1.trans (heqG r hm).1.symm,
      (heqF r hm).2.trans (heqG r hm).2.symm⟩
  have hstates := radialSystem_state_eqOn hopen hc ht
    (fun r hr => hFP.2.1 r ((hJ ▸ hr).1))
    (fun r hr => hGQ.2.1 r ((hJ ▸ hr).2))
    (fun r hr => ⟨(hFP.2.2 r ((hJ ▸ hr).1)).2.1.ne',
      (hFP.2.2 r ((hJ ▸ hr).1)).2.2.ne',
      (hGQ.2.2 r ((hJ ▸ hr).2)).2.2.ne'⟩)
    (hlocal.mono (fun _ hr => hr.1)) (hlocal.mono (fun _ hr => hr.2))
  intro r hr
  have heq := hstates (hJ.symm ▸ hr)
  exact ⟨by simpa using congrFun heq 0, by simpa using congrFun heq 1⟩

end OaiSmoothNonquadraticAffine
