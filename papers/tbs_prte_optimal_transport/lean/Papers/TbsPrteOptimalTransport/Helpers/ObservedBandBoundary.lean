module
public import Papers.TbsPrteOptimalTransport.Helpers.ObservedBoundaryTransfer
/-! Simultaneous observation-level boundary cancellation for continuous bands. -/
public section
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false

namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z] [Fintype Z] [DecidableEq Z]
variable (M : LatentIVModel Ω X Z)

-- The two endpoint errors provide an L1 envelope for the selected remainder.
-- No outcome moment or density assumption is needed for integrability.
-- @node: population_observed_band_boundary_integrable
/-- Suppose [the original lower](hyp:ha) and [upper](hyp:hb) endpoints, [the perturbed
lower](hyp:ha') and [upper](hyp:hb') endpoints, [the weight](hyp:hw), and [the denominator](hyp:hc)
are measurable; [the original endpoints](hyp:hab) and [the perturbed endpoints](hyp:hab')
are ordered almost everywhere; and [the lower endpoint error](hyp:hia) and [the upper
endpoint error](hyp:hib) are integrable under the covariate law. If [the weight bound is
nonnegative](hyp:hB), [the denominator bound is positive](hyp:hc0), [the weight is almost
everywhere bounded in absolute value by the former](hyp:hwb), and [the denominator is
almost everywhere at least the latter](hyp:hcl), [the population weighted selected treatment
debiased band-boundary remainder is integrable](goal). -/
lemma population_observed_band_boundary_integrable
    (L : LevelData Z X) (i : ℕ) (a b a' b' w c : X → ℝ)
    (ha : Measurable a) (hb : Measurable b)
    (ha' : Measurable a') (hb' : Measurable b')
    (hw : Measurable w) (hc : Measurable c)
    (hab : ∀ᵐ x ∂xLaw M, a x ≤ b x) (hab' : ∀ᵐ x ∂xLaw M, a' x ≤ b' x)
    (hia : Integrable (fun x => a' x - a x) (xLaw M))
    (hib : Integrable (fun x => b' x - b x) (xLaw M))
    (B c0 : ℝ) (hB : 0 ≤ B) (hc0 : 0 < c0)
    (hwb : ∀ᵐ x ∂xLaw M, |w x| ≤ B)
    (hcl : ∀ᵐ x ∂xLaw M, c0 ≤ c x) :
    Integrable (fun o : Obs X Z => w o.1 *
      (indicator (o.2.1 ∈ L.S i) * o.2.2.1 / c o.1 *
        continuousDebiasedBandBoundary (a o.1) (b o.1) (a' o.1) (b' o.1) o.2.2.2))
      (observationLaw M) := by
  apply population_selected_integrand_integrable_of_envelope M L i
    (fun x y => continuousDebiasedBandBoundary (a x) (b x) (a' x) (b' x) y)
    (by unfold continuousDebiasedBandBoundary; fun_prop)
    (fun x => |a' x - a x| + |b' x - b x|) (by fun_prop)
    (hia.abs.fun_add hib.abs) _ w c hw hc B c0 hB hc0 hwb hcl
  filter_upwards [hab, hab'] with x hx hx'
  intro y
  rw [continuous_debiased_band_boundary_difference _ _ _ _ _ hx hx']
  exact (norm_sub_le _ _).trans (add_le_add
    (debiased_quantile_boundary_norm_le (a x) (a' x) y)
    (debiased_quantile_boundary_norm_le (b x) (b' x) y))

-- Ordering is needed only almost everywhere; null-set choices are unrestricted.
-- Both endpoints move, while the product weight and denominator may also vary.
-- The proof subtracts the two previously established single-endpoint derivatives.
-- @node: population_observed_band_boundary_local_path_orthogonality
/-- Suppose [the lower](hyp:ha) and [upper](hyp:hb) endpoints and [their lower](hyp:hda)
and [upper](hyp:hdb) perturbation directions are measurable, with [a square-integrable
lower direction](hyp:hda2) and [a square-integrable upper direction](hyp:hdb2).
If [the baseline endpoints are ordered almost everywhere](hyp:hab), [their linear
perturbations remain ordered locally almost everywhere](hyp:hpath), [the weight bound is
nonnegative](hyp:hB), [the denominator bound is positive](hyp:hc0), [the radius is positive](hyp:hr),
[the density bound is nonnegative](hyp:hC), [locally the weights and denominators are
measurable with those absolute and lower bounds](hyp:hlocal), and [the selected treated
outcome law has interval probabilities bounded by the density bound times length near the
lower endpoint](hyp:hdena) and [near the upper endpoint](hyp:hdenb), [the population weighted
selected treatment debiased band-boundary remainder has derivative zero at zero](goal). -/
lemma population_observed_band_boundary_local_path_orthogonality
    (L : LevelData Z X) (i : ℕ) (a b da db : X → ℝ)
    (ha : Measurable a) (hb : Measurable b)
    (hda : Measurable da) (hdb : Measurable db)
    (hda2 : MemLp da 2 (xLaw M)) (hdb2 : MemLp db 2 (xLaw M))
    (hab : ∀ᵐ x ∂xLaw M, a x ≤ b x)
    (hpath : ∀ᶠ t : ℝ in 𝓝 0, ∀ᵐ x ∂xLaw M, a x + t * da x ≤ b x + t * db x)
    (w c : ℝ → X → ℝ) (B c0 r C : ℝ)
    (hB : 0 ≤ B) (hc0 : 0 < c0) (hr : 0 < r) (hC : 0 ≤ C)
    (hlocal : ∀ᶠ t : ℝ in 𝓝 0, Measurable (w t) ∧ Measurable (c t) ∧
      (∀ᵐ x ∂xLaw M, |w t x| ≤ B) ∧ (∀ᵐ x ∂xLaw M, c0 ≤ c t x))
    (hdena : ∀ᵐ x ∂xLaw M, ∀ u v, a x - r ≤ u → u ≤ v → v ≤ a x + r →
      (treatedLaw M L i x (Ioc u v)).toReal ≤ C * (v - u))
    (hdenb : ∀ᵐ x ∂xLaw M, ∀ u v, b x - r ≤ u → u ≤ v → v ≤ b x + r →
      (treatedLaw M L i x (Ioc u v)).toReal ≤ C * (v - u)) :
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z, w t o.1 *
      (indicator (o.2.1 ∈ L.S i) * o.2.2.1 / c t o.1 *
        continuousDebiasedBandBoundary (a o.1) (b o.1)
          (a o.1 + t * da o.1) (b o.1 + t * db o.1) o.2.2.2)
      ∂observationLaw M) 0 0 := by
  have za := population_observed_quantile_boundary_local_path_orthogonality M L i
    a da ha hda hda2 w c B c0 r C hB hc0 hr hC hlocal hdena
  have zb := population_observed_quantile_boundary_local_path_orthogonality M L i
    b db hb hdb hdb2 w c B c0 r C hB hc0 hr hC hlocal hdenb
  have hz := za.sub zb
  simp only [sub_zero] at hz
  apply hz.congr_of_eventuallyEq
  have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  have hia : Integrable da (xLaw M) := hda2.integrable (by norm_num)
  have hib : Integrable db (xLaw M) := hdb2.integrable (by norm_num)
  filter_upwards [hpath, hlocal] with t ht hl
  let ga : X → ℝ → ℝ := fun x y =>
    (a x + t * da x - y) * indicator (y ≤ a x + t * da x) -
      (a x - y) * indicator (y ≤ a x) - t * da x * indicator (y ≤ a x)
  let gb : X → ℝ → ℝ := fun x y =>
    (b x + t * db x - y) * indicator (y ≤ b x + t * db x) -
      (b x - y) * indicator (y ≤ b x) - t * db x * indicator (y ≤ b x)
  have ia := population_selected_integrand_integrable_of_envelope M L i ga
    (by dsimp only [ga]; fun_prop) (fun x => |t| * |da x|) (by fun_prop)
    (hia.abs.const_mul |t|) (Eventually.of_forall fun x y => by
      simpa only [ga, add_sub_cancel_left, abs_mul] using
        debiased_quantile_boundary_norm_le (a x) (a x + t * da x) y)
    (w t) (c t) hl.1 hl.2.1 B c0 hB hc0 hl.2.2.1 hl.2.2.2
  have ib := population_selected_integrand_integrable_of_envelope M L i gb
    (by dsimp only [gb]; fun_prop) (fun x => |t| * |db x|) (by fun_prop)
    (hib.abs.const_mul |t|) (Eventually.of_forall fun x y => by
      simpa only [gb, add_sub_cancel_left, abs_mul] using
        debiased_quantile_boundary_norm_le (b x) (b x + t * db x) y)
    (w t) (c t) hl.1 hl.2.1 B c0 hB hc0 hl.2.2.1 hl.2.2.2
  have hid : (fun o : Obs X Z => w t o.1 *
      (indicator (o.2.1 ∈ L.S i) * o.2.2.1 / c t o.1 *
        continuousDebiasedBandBoundary (a o.1) (b o.1)
          (a o.1 + t * da o.1) (b o.1 + t * db o.1) o.2.2.2)) =ᵐ[observationLaw M]
      (fun o => w t o.1 *
        (indicator (o.2.1 ∈ L.S i) * o.2.2.1 / c t o.1 * ga o.1 o.2.2.2) -
        w t o.1 *
        (indicator (o.2.1 ∈ L.S i) * o.2.2.1 / c t o.1 * gb o.1 o.2.2.2)) := by
    have ho := observationLaw_covariate_ae M _ (hab.and ht)
    filter_upwards [ho] with o hx
    rw [continuous_debiased_band_boundary_difference _ _ _ _ _ hx.1 hx.2]
    dsimp only [ga, gb]
    simp only [add_sub_cancel_left]
    ring
  rw [integral_congr_ae hid, integral_sub ia ib]
  rfl

-- At the fixed lower endpoint the remainder is exactly the negative upper
-- remainder, so no density assumption at that lower endpoint is introduced.
-- @node: population_observed_band_fixed_lower_path_orthogonality
/-- Suppose [the upper endpoint](hyp:hb) and [its direction](hyp:hdb) are measurable,
[the direction is square-integrable](hyp:hdb2), [the fixed lower endpoint is almost
everywhere below the baseline upper endpoint](hyp:hab), and [this ordering persists locally
along the upper endpoint path](hyp:hpath). If [the weight bound is nonnegative](hyp:hB),
[the denominator bound is positive](hyp:hc0), [the radius is positive](hyp:hr), [the density
bound is nonnegative](hyp:hC), [locally the weights and denominators are measurable with
those absolute and lower bounds](hyp:hlocal), and [the selected treated outcome law has
interval probabilities at most the density bound times length near the upper endpoint](hyp:hdenb),
[the population weighted selected treatment debiased band-boundary remainder with fixed
lower endpoint has derivative zero at zero](goal). -/
lemma population_observed_band_fixed_lower_path_orthogonality
    (L : LevelData Z X) (i : ℕ) (a b db : X → ℝ)
    (hb : Measurable b) (hdb : Measurable db) (hdb2 : MemLp db 2 (xLaw M))
    (hab : ∀ᵐ x ∂xLaw M, a x ≤ b x)
    (hpath : ∀ᶠ t : ℝ in 𝓝 0, ∀ᵐ x ∂xLaw M, a x ≤ b x + t * db x)
    (w c : ℝ → X → ℝ) (B c0 r C : ℝ)
    (hB : 0 ≤ B) (hc0 : 0 < c0) (hr : 0 < r) (hC : 0 ≤ C)
    (hlocal : ∀ᶠ t : ℝ in 𝓝 0, Measurable (w t) ∧ Measurable (c t) ∧
      (∀ᵐ x ∂xLaw M, |w t x| ≤ B) ∧ (∀ᵐ x ∂xLaw M, c0 ≤ c t x))
    (hdenb : ∀ᵐ x ∂xLaw M, ∀ u v, b x - r ≤ u → u ≤ v → v ≤ b x + r →
      (treatedLaw M L i x (Ioc u v)).toReal ≤ C * (v - u)) :
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z, w t o.1 *
      (indicator (o.2.1 ∈ L.S i) * o.2.2.1 / c t o.1 *
        continuousDebiasedBandBoundary (a o.1) (b o.1)
          (a o.1) (b o.1 + t * db o.1) o.2.2.2) ∂observationLaw M) 0 0 := by
  have hz := (population_observed_quantile_boundary_local_path_orthogonality M L i
    b db hb hdb hdb2 w c B c0 r C hB hc0 hr hC hlocal hdenb).neg
  simp only [neg_zero] at hz
  apply hz.congr_of_eventuallyEq
  filter_upwards [hpath] with t ht
  simp only [Pi.neg_apply]
  rw [← integral_neg]
  apply integral_congr_ae
  have ho := observationLaw_covariate_ae M _ (hab.and ht)
  filter_upwards [ho] with o hx
  rw [continuous_debiased_band_boundary_difference _ _ _ _ _ hx.1 hx.2]
  simp only [sub_self, zero_mul, zero_sub, add_sub_cancel_left, mul_neg]

-- Assembly of the actual IFJ/IFM block. The reference retains the fitted
-- denominator; population regressions center the two linear boundary terms.
-- The first band is covered by the fixed-lower alternative in hdena.
-- @node: population_continuous_band_quantile_block_local_orthogonality
/-- Consider [a level below the total number of levels](hyp:hk), [a band index below
that level's band count](hyp:hj), and [the plus side or a nonzero level on the minus side](hyp:hactive).
Suppose [the lower](hyp:hda) and [upper](hyp:hdb) endpoint directions are measurable and
[the lower](hyp:hda2) and [upper](hyp:hdb2) directions are square-integrable, [the baseline
lower](hyp:ha) and [upper](hyp:hb) boundaries are measurable, and [these boundaries are
ordered almost everywhere](hyp:hab). With [a nonnegative weight bound](hyp:hB), [a positive
assignment lower bound](hyp:hc0), [a positive radius](hyp:hr), and [a nonnegative density
bound](hyp:hC), assume [locally the nuisance path uses the designated assignment path,
keeps the outcome and mass blocks at truth, moves both endpoints linearly while preserving
their order, and has measurable assignments and weights satisfying the assignment lower
bound and absolute weight bound](hyp:hlocal). If [the lower direction is zero or the
selected treated law has interval probabilities bounded by the density bound times length
near the lower boundary](hyp:hdena), and [the same interval bound holds near the upper
boundary](hyp:hdenb), [the weighted population difference between the moving quantile score
block and its true-endpoint counterpart with the same moving assignments has derivative
zero at zero](goal). -/
lemma population_continuous_band_quantile_block_local_orthogonality
    (L : LevelData Z X) (e : ℝ → NuisanceCont L)
    (pi : ℝ → PositiveIndex L.K → X → ℝ) (w : ℝ → X → ℝ)
    (plus : Bool) (k j : ℕ) (hk : k < L.K) (hj : j < L.l k)
    (hactive : plus = true ∨ k ≠ 0)
    (da db : X → ℝ) (hda : Measurable da) (hdb : Measurable db)
    (hda2 : MemLp da 2 (xLaw M)) (hdb2 : MemLp db 2 (xLaw M))
    (ha : Measurable (bandBoundary M L k j))
    (hb : Measurable (bandBoundary M L k (j + 1)))
    (hab : ∀ᵐ x ∂xLaw M, bandBoundary M L k j x ≤ bandBoundary M L k (j + 1) x)
    (B c0 r C : ℝ) (hB : 0 ≤ B) (hc0 : 0 < c0) (hr : 0 < r) (hC : 0 ≤ C)
    (hlocal : ∀ᶠ t : ℝ in 𝓝 0,
      (e t).piLev = pi t ∧ (e t).Jplus = (trueNuisance M L).Jplus ∧
      (e t).Jminus = (trueNuisance M L).Jminus ∧
      (e t).Mplus = (trueNuisance M L).Mplus ∧
      (e t).Mminus = (trueNuisance M L).Mminus ∧
      (∀ x, nuValue M (e t) k j x = bandBoundary M L k j x + t * da x) ∧
      (∀ x, nuValue M (e t) k (j + 1) x = bandBoundary M L k (j + 1) x + t * db x) ∧
      (∀ᵐ x ∂xLaw M, bandBoundary M L k j x + t * da x ≤
        bandBoundary M L k (j + 1) x + t * db x) ∧
      (∀ a, Measurable (pi t a)) ∧
      (∀ a, ∀ᵐ x ∂xLaw M, c0 ≤ pi t a x) ∧
      Measurable (w t) ∧ (∀ᵐ x ∂xLaw M, |w t x| ≤ B))
    (hdena : da = 0 ∨ (∀ᵐ x ∂xLaw M, ∀ u v,
      bandBoundary M L k j x - r ≤ u → u ≤ v → v ≤ bandBoundary M L k j x + r →
      (treatedLaw M L (if plus then k + 1 else k) x (Ioc u v)).toReal ≤ C * (v - u)))
    (hdenb : ∀ᵐ x ∂xLaw M, ∀ u v,
      bandBoundary M L k (j + 1) x - r ≤ u → u ≤ v →
      v ≤ bandBoundary M L k (j + 1) x + r →
      (treatedLaw M L (if plus then k + 1 else k) x (Ioc u v)).toReal ≤ C * (v - u)) :
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z, w t o.1 *
      ((IFJ M L (e t) plus k j o + nuValue M (e t) k j o.1 * IFM M L (e t) plus k j o -
        nuValue M (e t) k (j + 1) o.1 * IFM M L (e t) plus k (j + 1) o) -
      (IFJ M L {trueNuisance M L with piLev := pi t} plus k j o +
        bandBoundary M L k j o.1 *
          IFM M L {trueNuisance M L with piLev := pi t} plus k j o -
        bandBoundary M L k (j + 1) o.1 *
          IFM M L {trueNuisance M L with piLev := pi t} plus k (j + 1) o))
      ∂observationLaw M) 0 0 := by
  let i : ℕ := if plus then k + 1 else k
  have hi : 1 ≤ i ∧ i ≤ L.K := by
    cases plus
    · simp only [Bool.false_eq_true, false_or] at hactive
      simp only [i, Bool.false_eq_true, if_false]
      omega
    · simp only [i, if_true]
      omega
  have hskip : (!plus && k == 0) = false := by
    cases plus
    · simp only [Bool.false_eq_true, false_or] at hactive
      simp [hactive]
    · simp
  have hp (t : ℝ) (hm : ∀ a, Measurable (pi t a)) :
      Measurable (positiveValue (pi t) i) := by
    unfold positiveValue
    simpa only [dif_pos hi] using hm ⟨i, hi⟩
  have hbounds : ∀ᶠ t : ℝ in 𝓝 0, Measurable (w t) ∧
      Measurable (positiveValue (pi t) i) ∧
      (∀ᵐ x ∂xLaw M, |w t x| ≤ B) ∧
      (∀ᵐ x ∂xLaw M, c0 ≤ positiveValue (pi t) i x) := by
    filter_upwards [hlocal] with t ht
    rcases ht with ⟨_, _, _, _, _, _, _, _, hpm, hclip, hwm, hwb⟩
    refine ⟨hwm, hp t hpm, hwb, ?_⟩
    simpa only [positiveValue, dif_pos hi] using hclip ⟨i, hi⟩
  have hordered : ∀ᶠ t : ℝ in 𝓝 0, ∀ᵐ x ∂xLaw M,
      bandBoundary M L k j x + t * da x ≤ bandBoundary M L k (j + 1) x + t * db x := by
    filter_upwards [hlocal] with t ht
    exact ht.2.2.2.2.2.2.2.1
  have hz : HasDerivAt (fun t : ℝ => ∫ o : Obs X Z, w t o.1 *
      (indicator (o.2.1 ∈ L.S i) * o.2.2.1 / positiveValue (pi t) i o.1 *
        continuousDebiasedBandBoundary (bandBoundary M L k j o.1)
          (bandBoundary M L k (j + 1) o.1)
          (bandBoundary M L k j o.1 + t * da o.1)
          (bandBoundary M L k (j + 1) o.1 + t * db o.1) o.2.2.2)
      ∂observationLaw M) 0 0 := by
    rcases hdena with hzero | hdena
    · subst da
      simp only [Pi.zero_apply, mul_zero, add_zero] at hordered ⊢
      exact population_observed_band_fixed_lower_path_orthogonality M L i _ _ db
        hb hdb hdb2 hab hordered w (fun t => positiveValue (pi t) i)
        B c0 r C hB hc0 hr hC hbounds hdenb
    · exact population_observed_band_boundary_local_path_orthogonality M L i _ _ da db
        ha hb hda hdb hda2 hdb2 hab hordered w (fun t => positiveValue (pi t) i)
        B c0 r C hB hc0 hr hC hbounds hdena hdenb
  apply hz.congr_of_eventuallyEq
  have : IsFiniteMeasure (xLaw M) := by unfold xLaw; infer_instance
  have hia : Integrable da (xLaw M) := hda2.integrable (by norm_num)
  have hib : Integrable db (xLaw M) := hdb2.integrable (by norm_num)
  filter_upwards [hlocal, hbounds] with t ht htbound
  rcases ht with ⟨hpi, hJp, hJm, hMp, hMm, hna, hnb, horder, hpm, hclip, hwm, hwb⟩
  have iwa : Integrable (fun x => w t x * (t * da x)) (xLaw M) :=
    (hia.const_mul t).bdd_mul hwm.aestronglyMeasurable
      (by simpa only [Real.norm_eq_abs] using hwb)
  have iwb : Integrable (fun x => w t x * (t * db x)) (xLaw M) :=
    (hib.const_mul t).bdd_mul hwm.aestronglyMeasurable
      (by simpa only [Real.norm_eq_abs] using hwb)
  have ia := population_IFM_fitted_denominator_integrable M L (pi t) hpm c0 hc0
    hclip plus k j hk hj.le ha _ (by fun_prop) iwa
  have ib := population_IFM_fitted_denominator_integrable M L (pi t) hpm c0 hc0
    hclip plus k (j + 1) hk (by omega) hb _ (by fun_prop) iwb
  have ir := population_observed_band_boundary_integrable M L i _ _
    (fun x => bandBoundary M L k j x + t * da x)
    (fun x => bandBoundary M L k (j + 1) x + t * db x) (w t) (positiveValue (pi t) i)
    ha hb (by fun_prop) (by fun_prop) hwm htbound.2.1 hab horder
    (by simpa only [add_sub_cancel_left] using hia.const_mul t)
    (by simpa only [add_sub_cancel_left] using hib.const_mul t)
    B c0 hB hc0 hwb htbound.2.2.2
  have hva x : t * da x = nuValue M (e t) k j x - bandBoundary M L k j x := by
    rw [hna]; ring
  have hvb x : t * db x = nuValue M (e t) k (j + 1) x - bandBoundary M L k (j + 1) x := by
    rw [hnb]; ring
  have hir : Integrable (fun o : Obs X Z => w t o.1 *
      ((if !plus && k == 0 then 0 else
        indicator (o.2.1 ∈ L.S (if plus then k + 1 else k)) * o.2.2.1 /
          positiveValue (pi t) (if plus then k + 1 else k) o.1) *
        continuousDebiasedBandBoundary (bandBoundary M L k j o.1)
          (bandBoundary M L k (j + 1) o.1)
          (nuValue M (e t) k j o.1) (nuValue M (e t) k (j + 1) o.1) o.2.2.2))
      (observationLaw M) := by
    simpa only [hskip, Bool.false_eq_true, if_false, hna, hnb, i] using ir
  have hmean := (population_continuous_band_quantile_difference_mean M L (e t)
    (pi t) hpm hpi hJp hJm hMp hMm plus k j hk hj ha hb (w t)
    (fun x => t * da x) (fun x => t * db x) (by fun_prop) (by fun_prop)
    hva hvb ia ib hir).2
  simpa only [hskip, Bool.false_eq_true, if_false, hna, hnb, i] using hmean

-- The fixed lower endpoint is ordered by the admissible quantile range;
-- no separation between estimated quantiles is assumed here.
-- @node: continuous_admissible_nuValue_lower_ae
/-- For [an admissible continuous nuisance specification](hyp:he), [a level below the
total number of levels](hyp:hk), and [an endpoint index no larger than that level's band
count](hyp:hj), [the corresponding endpoint value is almost everywhere at least the model's
minimum outcome](goal). -/
lemma continuous_admissible_nuValue_lower_ae
    (L : LevelData Z X) (eta : NuisanceCont L) (he : ContAdmissible M L eta)
    (k j : ℕ) (hk : k < L.K) (hj : j ≤ L.l k) :
    ∀ᵐ x ∂xLaw M, M.yMin ≤ nuValue M eta k j x := by
  by_cases hj0 : j = 0
  · subst j
    exact Eventually.of_forall fun x => by simp [nuValue]
  · have ha : k < L.K ∧ 1 ≤ j ∧ j ≤ L.l k := ⟨hk, by omega, hj⟩
    rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hnu, _⟩
    filter_upwards [hnu ⟨(k,j), ha⟩] with x hx
    simpa only [nuValue, hj0, if_false, dif_pos ha] using hx.1

-- @node: continuous_admissible_first_band_ordered_path
/-- For [an admissible continuous nuisance direction at the truth](hyp:hd), [a level below
the total number of levels](hyp:hk), and [a level with at least one band](hyp:hj), [locally
along the direction, the perturbed first upper band boundary is almost everywhere at least
the model's minimum outcome](goal). -/
lemma continuous_admissible_first_band_ordered_path
    (L : LevelData Z X) (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (k : ℕ) (hk : k < L.K) (hj : 1 ≤ L.l k) :
    ∀ᶠ t : ℝ in 𝓝 0, ∀ᵐ x ∂xLaw M,
      M.yMin ≤ bandBoundary M L k 1 x + t * del.nu ⟨(k,1), hk, le_rfl, hj⟩ x := by
  obtain ⟨r, hr, hpath⟩ := hd.admissible
  have hn : ∀ᶠ t : ℝ in 𝓝 0, |t| < r :=
    continuousAt_id.abs.eventually_lt_const (by simpa using hr)
  filter_upwards [hn] with t ht
  have hlow := continuous_admissible_nuValue_lower_ae M L
    (trueNuisance M L + t • del) (hpath t ht) k 1 hk hj
  have ha : k < L.K ∧ 1 ≤ 1 ∧ 1 ≤ L.l k := ⟨hk, le_rfl, hj⟩
  have hbase x : (trueNuisance M L).nu ⟨(k,1),ha⟩ x = bandBoundary M L k 1 x := rfl
  simp only [nuValue, Nat.one_ne_zero, if_false, dif_pos ha] at hlow
  change ∀ᵐ x ∂xLaw M, M.yMin ≤
    (trueNuisance M L).nu ⟨(k,1),ha⟩ x + t * del.nu ⟨(k,1),ha⟩ x at hlow
  simpa only [hbase] using hlow

-- First-band cancellation on the paper's admissible path. The fixed lower
-- endpoint needs neither a density bound nor an extra ordering hypothesis.
-- @node: population_observed_first_band_admissible_boundary_orthogonality
/-- Suppose [outcome densities near band boundaries are bounded](hyp:h), [the continuous
nuisance direction is admissible at the truth](hyp:hd), [the level is below the total number
of levels](hyp:hk), [it has at least one band](hyp:hj), [the selected baseline level is
adjacent to it on the plus or valid minus side](hyp:hi), and [its first upper band boundary
is measurable](hyp:hb). If [the weight bound is nonnegative](hyp:hB), [the denominator bound
is positive](hyp:hc0), and [locally the weight and denominator are measurable, the weight
is bounded in absolute value, and the denominator has that lower bound](hyp:hlocal), [the
population weighted selected treatment debiased first-band remainder, with its lower endpoint
fixed at the minimum outcome and upper endpoint moving along the admissible direction,
has derivative zero at zero](goal). -/
lemma population_observed_first_band_admissible_boundary_orthogonality
    (L : LevelData Z X) (h : BoundaryDensitiesBounded M L)
    (del : NuisanceCont L)
    (hd : IsAdmissibleDirection M L (.inl (trueNuisance M L)) (.inl del))
    (k : ℕ) (hk : k < L.K) (hj : 1 ≤ L.l k)
    (i : ℕ) (hi : i = k + 1 ∨ (1 ≤ k ∧ i = k))
    (hb : Measurable (bandBoundary M L k 1))
    (w c : ℝ → X → ℝ) (B c0 : ℝ) (hB : 0 ≤ B) (hc0 : 0 < c0)
    (hlocal : ∀ᶠ t : ℝ in 𝓝 0, Measurable (w t) ∧ Measurable (c t) ∧
      (∀ᵐ x ∂xLaw M, |w t x| ≤ B) ∧ (∀ᵐ x ∂xLaw M, c0 ≤ c t x)) :
    HasDerivAt (fun t : ℝ => ∫ o : Obs X Z, w t o.1 *
      (indicator (o.2.1 ∈ L.S i) * o.2.2.1 / c t o.1 *
        continuousDebiasedBandBoundary M.yMin (bandBoundary M L k 1 o.1)
          M.yMin (bandBoundary M L k 1 o.1 +
            t * del.nu ⟨(k,1), hk, le_rfl, hj⟩ o.1) o.2.2.2)
      ∂observationLaw M) 0 0 := by
  let a : BoundaryIndex L := ⟨(k,1), hk, le_rfl, hj⟩
  obtain ⟨_, _, hdir⟩ := continuous_quantile_direction_regular M L
    (trueNuisance M L) del hd
  have horder := continuous_admissible_first_band_ordered_path M L del hd k hk hj
  have hbase : ∀ᵐ x ∂xLaw M, M.yMin ≤ bandBoundary M L k 1 x := by
    simpa only [zero_mul, add_zero] using horder.self_of_nhds
  obtain ⟨r, C, hr, hden⟩ := h
  apply population_observed_band_fixed_lower_path_orthogonality M L i
    (fun _ => M.yMin) (bandBoundary M L k 1) (del.nu a) hb (hdir a).1
    (continuous_quantile_direction_memLp M L (trueNuisance M L) del hd a)
    hbase horder w c B c0 r |C| hB hc0 hr (abs_nonneg C) hlocal
  filter_upwards [hden k hk 1 le_rfl hj i hi] with x hx
  intro u v hu huv hv
  exact (hx u v hu huv hv).trans
    (mul_le_mul_of_nonneg_right (le_abs_self C) (sub_nonneg.mpr huv))

end Papers.TbsPrteOptimalTransport
