module
public import Papers.TbsPrteOptimalTransport.Helpers.FirstStageTransfer
/-! Strict-exceedance probability rates for the boundary localization and grid errors. -/
public section
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory Filter Set
open scoped Classical Topology ENNReal

variable {A : Type*} [MeasurableSpace A] {μ : Measure A}

-- @node: boundedAtRate_add
/-- If [f is bounded in probability at rate r](hyp:hf) and [g is bounded in probability at rate s](hyp:hg), [their sum is bounded in probability at rate r plus s](goal), including when rates vanish. -/
lemma boundedAtRate_add {f g : ℕ → A → ℝ} {r s : ℕ → ℝ}
    (hf : BoundedAtRate μ f r) (hg : BoundedAtRate μ g s) :
    BoundedAtRate μ (fun n a => f n a + g n a) (fun n => r n + s n) := by
  refine ⟨fun n => add_nonneg (hf.1 n) (hg.1 n), ?_⟩
  intro ε hε
  obtain ⟨C, hC, hc⟩ := hf.2 (ε / 2) (by positivity)
  obtain ⟨D, hD, hd⟩ := hg.2 (ε / 2) (by positivity)
  refine ⟨max C D, lt_max_of_lt_left hC, ?_⟩
  filter_upwards [hc, hd] with n hcn hdn
  have hsub : {a | max C D * (r n + s n) < |f n a + g n a|} ⊆
      {a | C * r n < |f n a|} ∪ {a | D * s n < |g n a|} := by
    intro a ha
    by_contra hn
    have hn' : |f n a| ≤ C * r n ∧ |g n a| ≤ D * s n := by
      simpa only [mem_union, mem_setOf_eq, not_or, not_lt] using hn
    have hcr := mul_le_mul_of_nonneg_right (le_max_left C D) (hf.1 n)
    have hds := mul_le_mul_of_nonneg_right (le_max_right C D) (hg.1 n)
    have hab := abs_add_le (f n a) (g n a)
    change max C D * (r n + s n) < |f n a + g n a| at ha
    nlinarith
  calc
    _ ≤ μ ({a | C * r n < |f n a|} ∪ {a | D * s n < |g n a|}) := measure_mono hsub
    _ ≤ μ {a | C * r n < |f n a|} + μ {a | D * s n < |g n a|} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hcn hdn
    _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

-- @node: boundedAtRate_const_mul
/-- If [f is bounded in probability at rate r](hyp:hf), [multiplying f by any fixed real constant preserves that rate](goal). -/
lemma boundedAtRate_const_mul {f : ℕ → A → ℝ} {r : ℕ → ℝ}
    (hf : BoundedAtRate μ f r) (c : ℝ) :
    BoundedAtRate μ (fun n a => c * f n a) r := by
  apply boundedAtRate_of_uniform_domination μ f _ r (|c| + 1) (by positivity) hf
  intro n a
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)

-- @node: boundedAtRate_deterministic
/-- For [a nonnegative rate sequence r](hyp:hr), [any fixed real multiple of r, viewed as a deterministic random sequence, is bounded in probability at rate r](goal). -/
lemma boundedAtRate_deterministic (r : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n) (c : ℝ) :
    BoundedAtRate μ (fun n _ => c * r n) r := by
  refine ⟨hr, ?_⟩
  intro ε hε
  refine ⟨|c| + 1, by positivity, Eventually.of_forall fun n => ?_⟩
  have he : {a : A | (|c| + 1) * r n < |c * r n|} = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro a ha
    change (|c| + 1) * r n < |c * r n| at ha
    rw [abs_mul, abs_of_nonneg (hr n)] at ha
    nlinarith [hr n]
  rw [he, measure_empty]
  exact bot_le

-- @node: boundedAtRate_of_ae_domination
/-- If [f is bounded in probability at rate r](hyp:hf) and [at every sample size the absolute value of g is almost surely no greater than that of f](hyp:h), [g is also bounded in probability at rate r](goal). -/
lemma boundedAtRate_of_ae_domination {f g : ℕ → A → ℝ} {r : ℕ → ℝ}
    (hf : BoundedAtRate μ f r) (h : ∀ n, ∀ᵐ a ∂μ, |g n a| ≤ |f n a|) :
    BoundedAtRate μ g r := by
  refine ⟨hf.1, ?_⟩
  intro ε hε
  obtain ⟨C, hC, hc⟩ := hf.2 ε hε
  refine ⟨C, hC, hc.mono fun n hn => ?_⟩
  apply le_trans (measure_mono_ae ?_) hn
  filter_upwards [h n] with a ha
  exact fun hg => hg.trans_le ha

-- @node: primitive_boundary_envelope_rate
/-- If [the grid error is bounded in probability at its grid rate](hyp:hGrid), [the first-stage error is bounded in probability at its first-stage rate](hyp:hFirst), [window widths are nonnegative](hyp:hd), [trimming levels are nonnegative](hyp:he), and [mesh sizes are nonnegative](hyp:hm), [the grid error plus B times the sum of window width and twice the first-stage error, plus twice B times trimming and four times B times mesh size, is bounded in probability at the sum of the grid rate, window width, first-stage rate, trimming level, and mesh size](goal). -/
lemma primitive_boundary_envelope_rate (grid first : ℕ → A → ℝ)
    (rQ rp delta eps mesh : ℕ → ℝ) (B : ℝ)
    (hGrid : BoundedAtRate μ grid rQ) (hFirst : BoundedAtRate μ first rp)
    (hd : ∀ n, 0 ≤ delta n) (he : ∀ n, 0 ≤ eps n) (hm : ∀ n, 0 ≤ mesh n) :
    BoundedAtRate μ
      (fun n a => grid n a + B * (delta n + 2 * first n a) +
        2 * B * eps n + 4 * B * mesh n)
      (fun n => rQ n + delta n + rp n + eps n + mesh n) := by
  have h := boundedAtRate_add
    (boundedAtRate_add
      (boundedAtRate_add
        (boundedAtRate_add hGrid (boundedAtRate_deterministic delta hd B))
        (boundedAtRate_const_mul hFirst (2 * B)))
      (boundedAtRate_deterministic eps he (2 * B)))
    (boundedAtRate_deterministic mesh hm (4 * B))
  convert h using 1
  funext n a
  ring

end Papers.TbsPrteOptimalTransport
