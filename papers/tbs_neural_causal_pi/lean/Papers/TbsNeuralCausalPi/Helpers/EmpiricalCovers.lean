module
public import Papers.TbsNeuralCausalPi.Setup.CitedResults
/-! # Empirical covers and scalar range normalization

Strict internal covers, packing-to-cover comparison, and the conversion between
averaged scalar metrics and the paper's unnormalized evaluation metric.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped ENNReal NNReal
noncomputable section

/-- At [a nonnegative radius ε](hyp:eps), [the closed internal covering number
of a set is at most its strict internal covering number at radius ε](goal). -/
-- @node: coveringNumber_le_strictCoveringNumber
lemma coveringNumber_le_strictCoveringNumber {E : Type*} [PseudoEMetricSpace E]
    (eps : ℝ≥0) (S : Set E) :
    Metric.coveringNumber eps S ≤ strictCoveringNumber (eps : ℝ≥0∞) S := by
  unfold strictCoveringNumber
  refine le_iInf fun C => ?_
  apply Metric.IsCover.coveringNumber_le_encard C.property.1
  intro x hx
  obtain ⟨y, hy, hxy⟩ := C.property.2 hx
  refine ⟨y, hy, ?_⟩
  change edist x y < (eps : ℝ≥0∞) at hxy
  exact hxy.le

/-- For [nonnegative radii ε′ and ε](hyp:eps',eps) with [ε′ strictly smaller
than ε](hyp:hslack), [the strict internal covering number at ε is at most
the closed internal covering number at ε′](goal). -/
-- @node: strictCoveringNumber_le_coveringNumber
lemma strictCoveringNumber_le_coveringNumber {E : Type*} [PseudoEMetricSpace E]
    (eps' eps : ℝ≥0) (hslack : eps' < eps) (S : Set E) :
    strictCoveringNumber (eps : ℝ≥0∞) S ≤ Metric.coveringNumber eps' S := by
  unfold Metric.coveringNumber
  refine le_iInf fun C => le_iInf fun hCS => le_iInf fun hC => ?_
  have hstrict : SetRel.IsCover {p : E × E | edist p.1 p.2 < (eps : ℝ≥0∞)} S C := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hC hx
    refine ⟨y, hy, ?_⟩
    change edist x y ≤ (eps' : ℝ≥0∞) at hxy
    change edist x y < (eps : ℝ≥0∞)
    exact lt_of_le_of_lt hxy (by exact_mod_cast hslack)
  exact iInf_le_of_le ⟨C, hCS, hstrict⟩ le_rfl

-- @node: N1avg_le_M1avg
/-- If [every function in the class takes values between zero and one](hyp:hG),
[the sample size is positive](hyp:hm), and [the radius ε is positive](hyp:heps),
[the worst-case empirical covering number in average absolute distance is
at most the corresponding ε-separated packing number](goal). -/
lemma N1avg_le_M1avg {X : Type*} (G : Set (X → ℝ))
    (hG : ∀ g ∈ G, ∀ x, g x ∈ Set.Icc (0 : ℝ) 1) (m : ℕ) (hm : 0 < m)
    (eps : ℝ) (heps : 0 < eps) : N1avg eps G m hG ≤ M1avg eps G m hG := by
  classical
  unfold N1avg M1avg
  refine iSup_le fun x => ?_
  let S := (fun g : X → ℝ => fun i => g (x i)) '' G
  let P := {C : Set (Fin m → ℝ) // C ⊆ S ∧
    ∀ u ∈ C, ∀ w ∈ C, u ≠ w → eps ≤ averagedL1 u w}
  have hP : Nonempty P := ⟨⟨∅, Set.empty_subset _, by simp⟩⟩
  by_cases htop : (⨆ C : P, C.val.encard) = ⊤
  · exact le_trans le_top (le_iSup_of_le x (ge_of_eq htop))
  obtain ⟨C, hC⟩ := ENat.exists_eq_iSup_of_lt_top (f := fun C : P => C.val.encard)
    (lt_top_iff_ne_top.mpr htop)
  have hfinite : C.val.encard ≠ ⊤ := by rw [hC]; exact htop
  have hcover : SetRel.IsCover {p | averagedL1 p.1 p.2 < eps} S C.val := by
    intro u hu
    by_contra! hnot
    have hdist : ∀ w ∈ C.val, eps ≤ averagedL1 u w := by
      intro w hw
      exact le_of_not_gt (hnot w hw)
    have hunot : u ∉ C.val := by
      intro hmem
      have hself := hdist u hmem
      simp [averagedL1] at hself
      linarith
    have hinsert : insert u C.val ⊆ S ∧
        ∀ v ∈ insert u C.val, ∀ w ∈ insert u C.val,
          v ≠ w → eps ≤ averagedL1 v w := by
      refine ⟨Set.insert_subset hu C.property.1, ?_⟩
      intro v hv w hw hvw
      rcases hv with rfl | hv
      · rcases hw with rfl | hw
        · exact (hvw rfl).elim
        · exact hdist w hw
      · rcases hw with rfl | hw
        · have hsym : averagedL1 v w = averagedL1 w v := by
            simp only [averagedL1, abs_sub_comm]
          rw [hsym]
          exact hdist v hv
        · exact C.property.2 v hv w hw hvw
    have hbound : (insert u C.val).encard ≤ C.val.encard :=
      (le_iSup (fun D : P => D.val.encard) ⟨insert u C.val, hinsert⟩).trans_eq hC.symm
    rw [Set.encard_insert_of_notMem hunot] at hbound
    exact (not_le_of_gt ((ENat.lt_add_one_iff hfinite).mpr le_rfl)) hbound
  exact (iInf_le_of_le ⟨C.val, C.property.1, hcover⟩ le_rfl).trans
    (le_iSup_of_le x (hC ▸ le_rfl))
/-- For [a radius ε, possibly infinite](hyp:eps), if [a bijection carries a
covering relation exactly to distance strictly below ε](hyp:hR), [the minimum
cardinality of an internal cover for that relation equals the strict
ε-covering number of the image set](goal). -/
-- @node: strictCoveringNumber_equiv_relation
lemma strictCoveringNumber_equiv_relation {E F : Type*} [PseudoEMetricSpace F]
    (e : E ≃ F) (R : SetRel E E) (eps : ℝ≥0∞) (S : Set E)
    (hR : ∀ u v, (u, v) ∈ R ↔ edist (e u) (e v) < eps) :
    (⨅ C : {C : Set E // C ⊆ S ∧ SetRel.IsCover R S C}, C.val.encard) =
      strictCoveringNumber eps (e '' S) := by
  classical
  apply le_antisymm
  · unfold strictCoveringNumber
    refine le_iInf fun C => ?_
    have hsub : e.symm '' C.val ⊆ S := by
      rintro _ ⟨v, hv, rfl⟩
      obtain ⟨u, hu, rfl⟩ := C.property.1 hv
      simpa using hu
    have hcover : SetRel.IsCover R S (e.symm '' C.val) := by
      intro u hu
      obtain ⟨v, hv, huv⟩ := C.property.2 (Set.mem_image_of_mem e hu)
      refine ⟨e.symm v, Set.mem_image_of_mem e.symm hv, (hR _ _).mpr ?_⟩
      simpa using huv
    exact (iInf_le_of_le ⟨e.symm '' C.val, hsub, hcover⟩ le_rfl).trans
      (Set.encard_image_le _ _)
  · refine le_iInf fun C => ?_
    have hsub : e '' C.val ⊆ e '' S := Set.image_mono C.property.1
    have hcover : SetRel.IsCover {p : F × F | edist p.1 p.2 < eps}
        (e '' S) (e '' C.val) := by
      rintro _ ⟨u, hu, rfl⟩
      obtain ⟨v, hv, huv⟩ := C.property.2 hu
      exact ⟨e v, Set.mem_image_of_mem e hv, (hR _ _).mp huv⟩
    exact (iInf_le_of_le ⟨e '' C.val, hsub, hcover⟩ le_rfl).trans
      (Set.encard_image_le _ _)

/-- If [the scalar functions take values between zero and one](hyp:hG),
[the sample size m is positive](hyp:hm), and [ε is positive](hyp:heps),
[their worst-case empirical covering number at average absolute radius ε
equals their unnormalized one-dimensional covering number at radius mε](goal). -/
-- @node: N1avg_eq_empiricalL1CoveringNumber
lemma N1avg_eq_empiricalL1CoveringNumber {X : Type*} (G : Set (X → ℝ))
    (hG : ∀ g ∈ G, ∀ x, g x ∈ Set.Icc (0 : ℝ) 1)
    (m : ℕ) (hm : 0 < m) (eps : ℝ) (heps : 0 < eps) :
    N1avg eps G m hG = empiricalL1CoveringNumber (ENNReal.ofReal ((m : ℝ) * eps))
      ((fun g : X → ℝ => fun x => WithLp.toLp 1 (fun _ : Fin 1 => g x)) '' G) m := by
  classical
  let e : (Fin m → ℝ) ≃ WithLp 1 (Fin m × Fin 1 → ℝ) :=
    { toFun := fun u => WithLp.toLp 1 (fun ij => u ij.1)
      invFun := fun v i => v.ofLp (i, 0)
      left_inv := fun u => rfl
      right_inv := by
        intro v
        apply WithLp.ofLp_injective 1
        funext ⟨i, j⟩
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        rfl }
  have hrel : ∀ u v : Fin m → ℝ,
      (u, v) ∈ {p | averagedL1 p.1 p.2 < eps} ↔
        edist (e u) (e v) < ENNReal.ofReal ((m : ℝ) * eps) := by
    intro u v
    change averagedL1 u v < eps ↔ _
    rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff (mul_pos (Nat.cast_pos.mpr hm) heps)]
    have hdist : dist (e u) (e v) = ∑ i, |u i - v i| := by
      simp [PiLp.dist_eq_of_L1, e, Fintype.sum_prod_type, Real.dist_eq]
    rw [hdist]
    unfold averagedL1
    rw [inv_mul_lt_iff₀ (Nat.cast_pos.mpr hm)]
  unfold N1avg empiricalL1CoveringNumber
  apply iSup_congr
  intro x
  rw [strictCoveringNumber_equiv_relation e _ _ _ hrel]
  congr 1
  ext v
  constructor
  · rintro ⟨u, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨_, ⟨g, hg, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨_, ⟨g, hg, rfl⟩, rfl⟩


/-- If [K is positive](hyp:hK) and [the scalar function class has
pseudo-dimension at most v](hyp:hv), [the class obtained by adding K and
dividing by 2K also has pseudo-dimension at most v](goal). -/
-- @node: empirical_normalized_pseudodim
lemma empirical_normalized_pseudodim {X : Type*} {G : Set (X → ℝ)}
    {K : ℝ} (hK : 0 < K) {v : ℕ}
    (hv : Causalean.Stat.Concentration.HasPseudoDimAtMost (fun g : G => g.val) v) :
    Causalean.Stat.Concentration.HasPseudoDimAtMost
      (fun g : ((fun f : X → ℝ => fun x => (f x + K) / (2*K)) '' G) => g.val) v := by
  classical
  intro n T
  let T' : Fin n → X × ℝ := fun i => ((T i).1, 2*K*(T i).2-K)
  have hpat (f : X → ℝ) (hf : f ∈ G) :
      Causalean.Stat.Concentration.restrictionPattern
        (Causalean.Stat.Concentration.subgraphClassifier
          (fun g : ((fun f : X → ℝ => fun x => (f x + K) / (2*K)) '' G) => g.val)
          ⟨_, Set.mem_image_of_mem _ hf⟩) T =
      Causalean.Stat.Concentration.restrictionPattern
        (Causalean.Stat.Concentration.subgraphClassifier (fun g : G => g.val) ⟨f, hf⟩) T' := by
    ext i
    simp only [Causalean.Stat.Concentration.restrictionPattern_mem_iff,
      Causalean.Stat.Concentration.subgraphClassifier, decide_eq_true_eq]
    change (T i).2 < (f (T i).1 + K) / (2*K) ↔ 2*K*(T i).2-K < f (T i).1
    rw [lt_div_iff₀ (by positivity : 0 < 2*K)]
    constructor <;> intro h <;> nlinarith
  have heq : Causalean.Stat.Concentration.growthFamily
      (Causalean.Stat.Concentration.subgraphClassifier
        (fun g : ((fun f : X → ℝ => fun x => (f x + K) / (2*K)) '' G) => g.val)) T =
      Causalean.Stat.Concentration.growthFamily
        (Causalean.Stat.Concentration.subgraphClassifier (fun g : G => g.val)) T' := by
    ext A
    simp only [Causalean.Stat.Concentration.mem_growthFamily_iff]
    constructor
    · rintro ⟨⟨g, f, hf, rfl⟩, hg⟩
      exact ⟨⟨f, hf⟩, (hpat f hf).symm.trans hg⟩
    · rintro ⟨⟨f, hf⟩, hfA⟩
      exact ⟨⟨_, Set.mem_image_of_mem _ hf⟩, (hpat f hf).trans hfA⟩
  rw [heq]
  exact hv n T'

/-- If [K is positive](hyp:hK) and [every function in the class is bounded
in absolute value by K](hyp:hG), [adding K and dividing by 2K gives functions
whose values all lie between zero and one](goal). -/
-- @node: empirical_normalized_range
lemma empirical_normalized_range {X : Type*} {G : Set (X → ℝ)}
    {K : ℝ} (hK : 0 < K) (hG : ∀ g ∈ G, ∀ x, |g x| ≤ K) :
    ∀ g ∈ ((fun f : X → ℝ => fun x => (f x + K) / (2*K)) '' G),
      ∀ x, g x ∈ Set.Icc (0 : ℝ) 1 := by
  rintro _ ⟨f, hf, rfl⟩ x
  have hb := abs_le.mp (hG f hf x)
  constructor
  · exact div_nonneg (by linarith) (by positivity)
  · apply (div_le_iff₀ (by positivity : 0 < 2*K)).mpr
    linarith

/-- If [K is positive](hyp:hK), [the radius r is positive](hyp:hr),
[the scalar class is bounded in absolute value by K](hyp:hG), and
[the sample size m is positive](hyp:hm), [the average-distance covering
number at r after adding K and dividing by 2K equals the original class's
unnormalized one-dimensional covering number at radius 2Kmr](goal). -/
-- @node: empirical_normalized_cover_eq
lemma empirical_normalized_cover_eq {X : Type*} {G : Set (X → ℝ)}
    {K r : ℝ} (hK : 0 < K) (hr : 0 < r)
    (hG : ∀ g ∈ G, ∀ x, |g x| ≤ K) {m : ℕ} (hm : 0 < m) :
    N1avg r ((fun f : X → ℝ => fun x => (f x + K) / (2*K)) '' G) m
      (empirical_normalized_range hK hG) =
      empiricalL1CoveringNumber (ENNReal.ofReal (2*K*m*r))
        ((fun f : X → ℝ => fun x => WithLp.toLp 1 (fun _ : Fin 1 => f x)) '' G) m := by
  classical
  have hK0 : (2*K) ≠ 0 := by positivity
  let e : (Fin m → ℝ) ≃ WithLp 1 (Fin m × Fin 1 → ℝ) :=
    { toFun := fun u => WithLp.toLp 1 (fun ij => 2*K*u ij.1-K)
      invFun := fun w i => (w.ofLp (i, 0)+K)/(2*K)
      left_inv := by
        intro u
        funext i
        dsimp
        field_simp
        <;> ring
      right_inv := by
        intro w
        apply WithLp.ofLp_injective 1
        funext ⟨i, j⟩
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        dsimp
        field_simp
        <;> ring }
  have hrel : ∀ u w : Fin m → ℝ,
      (u, w) ∈ {p | averagedL1 p.1 p.2 < r} ↔
        edist (e u) (e w) < ENNReal.ofReal (2*K*m*r) := by
    intro u w
    change averagedL1 u w < r ↔ _
    rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    have he : dist (e u) (e w) = 2*K * ∑ i, |u i-w i| := by
      simp only [PiLp.dist_eq_of_L1, e, Equiv.coe_fn_mk, WithLp.ofLp_toLp,
        Fintype.sum_prod_type, Real.dist_eq, Fin.sum_univ_one]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have hid : 2*K*u i-K-(2*K*w i-K) = (2*K)*(u i-w i) := by ring
      rw [hid, abs_mul, abs_of_pos (by positivity : 0 < 2*K)]
    rw [he]
    unfold averagedL1
    rw [inv_mul_lt_iff₀ (Nat.cast_pos.mpr hm)]
    constructor <;> intro h
    · nlinarith
    · nlinarith
  unfold N1avg empiricalL1CoveringNumber
  apply iSup_congr
  intro x
  rw [strictCoveringNumber_equiv_relation e _ _ _ hrel]
  congr 1
  ext w
  constructor
  · rintro ⟨u, ⟨_, ⟨f, hf, rfl⟩, rfl⟩, rfl⟩
    refine ⟨_, ⟨f, hf, rfl⟩, ?_⟩
    apply WithLp.ofLp_injective 1
    funext ⟨i, j⟩
    change f (x i) = 2*K*((f (x i)+K)/(2*K))-K
    field_simp
    <;> ring
  · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    refine ⟨_, ⟨_, ⟨f, hf, rfl⟩, rfl⟩, ?_⟩
    apply WithLp.ofLp_injective 1
    funext ⟨i, j⟩
    change 2*K*((f (x i)+K)/(2*K))-K = f (x i)
    field_simp
    <;> ring

/-- Assume [the Anthony–Bartlett covering and concentration bounds](hyp:hAnthony),
[a nonempty scalar class](hyp:hne), [a positive range bound K](hyp:hK),
[absolute values bounded by K throughout the class](hyp:hG),
[pseudo-dimension at most v](hyp:hv), [a positive sample size m](hyp:hm),
and [a positive radius r](hyp:hr) [no larger than 2Km](hyp:hsmall).
Then [the unnormalized empirical covering number at r is at most
e(v + 1)(4eKm/r)ᵛ](goal). -/
-- @node: empirical_scalar_cover_le_of_radius_le
lemma empirical_scalar_cover_le_of_radius_le
    (hAnthony : AnthonyBartlettCoveringConcentration)
    {X : Type} {G : Set (X → ℝ)} (hne : G.Nonempty)
    {K : ℝ} (hK : 0 < K) (hG : ∀ g ∈ G, ∀ x, |g x| ≤ K)
    {v : ℕ} (hv : Causalean.Stat.Concentration.HasPseudoDimAtMost (fun g : G => g.val) v)
    {m : ℕ} (hm : 0 < m) {r : ℝ} (hr : 0 < r) (hsmall : r ≤ 2*K*m) :
    (empiricalL1CoveringNumber (ENNReal.ofReal r)
      ((fun f : X → ℝ => fun x => WithLp.toLp 1 (fun _ : Fin 1 => f x)) '' G) m).toENNReal ≤
      ENNReal.ofReal (Real.exp 1 * (v+1) * (4 * Real.exp 1 * K * m / r)^v) := by
  let s := r / (2*K*m)
  have hs : 0 < s := div_pos hr (by positivity)
  have hs1 : s ≤ 1 := (div_le_one (by positivity : 0 < 2*K*(m : ℝ))).mpr hsmall
  have hne' : ((fun f : X → ℝ => fun x => (f x+K)/(2*K)) '' G).Nonempty :=
    hne.image _
  have hpack := hAnthony.1 X _ hne' (empirical_normalized_range hK hG) v
    (empirical_normalized_pseudodim hK hv) m hm s hs hs1
  have hcover := N1avg_le_M1avg _ (empirical_normalized_range hK hG) m hm s hs
  rw [empirical_normalized_cover_eq hK hs hG hm] at hcover
  have hscale : 2*K*(m : ℝ)*s = r := by dsimp [s]; field_simp
  rw [hscale] at hcover
  have hbound := (ENat.toENNReal_mono hcover).trans hpack.le
  have hratio : 2 * Real.exp 1 / s = 4 * Real.exp 1 * K * m / r := by
    dsimp [s]
    field_simp
    <;> ring
  simpa only [hratio] using hbound

/-- If [the scalar class is nonempty](hyp:hne), [K is nonnegative](hyp:hK),
[every class member is bounded in absolute value by K](hyp:hG), and
[r exceeds 2Km](hyp:hr), [its unnormalized empirical covering number on
m observations at radius r is at most one](goal). -/
-- @node: empirical_scalar_cover_le_one
lemma empirical_scalar_cover_le_one {X : Type*} {G : Set (X → ℝ)} (hne : G.Nonempty)
    {K r : ℝ} (hK : 0 ≤ K) (hG : ∀ g ∈ G, ∀ x, |g x| ≤ K)
    (m : ℕ) (hr : 2*K*m < r) :
    empiricalL1CoveringNumber (ENNReal.ofReal r)
      ((fun f : X → ℝ => fun x => WithLp.toLp 1 (fun _ : Fin 1 => f x)) '' G) m ≤ 1 := by
  classical
  obtain ⟨g, hg⟩ := hne
  unfold empiricalL1CoveringNumber
  apply iSup_le
  intro x
  let v : WithLp 1 (Fin m × Fin 1 → ℝ) := WithLp.toLp 1 (fun ij => g (x ij.1))
  have hsub : {v} ⊆
      (fun f : X → L1Vec 1 => WithLp.toLp 1 (fun ij : Fin m × Fin 1 =>
        (f (x ij.1)).ofLp ij.2)) ''
        ((fun f : X → ℝ => fun x => WithLp.toLp 1 (fun _ : Fin 1 => f x)) '' G) := by
    intro w hw
    obtain rfl := Set.mem_singleton_iff.mp hw
    exact ⟨_, ⟨g, hg, rfl⟩, rfl⟩
  have hcover : SetRel.IsCover {p | edist p.1 p.2 < ENNReal.ofReal r}
      ((fun f : X → L1Vec 1 => WithLp.toLp 1 (fun ij : Fin m × Fin 1 =>
        (f (x ij.1)).ofLp ij.2)) ''
        ((fun f : X → ℝ => fun x => WithLp.toLp 1 (fun _ : Fin 1 => f x)) '' G)) {v} := by
    rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    refine ⟨v, Set.mem_singleton _, ?_⟩
    change edist _ v < ENNReal.ofReal r
    rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff
      (lt_of_le_of_lt (by positivity : 0 ≤ 2*K*(m : ℝ)) hr)]
    calc
      _ = ∑ i, |f (x i)-g (x i)| := by
        simp [PiLp.dist_eq_of_L1, v, Fintype.sum_prod_type, Real.dist_eq]
      _ ≤ ∑ _i : Fin m, (2*K) := by
        apply Finset.sum_le_sum
        intro i _
        exact (abs_sub _ _).trans (by linarith [hG f hf (x i), hG g hg (x i)])
      _ = 2*K*m := by simp; ring
      _ < r := hr
  exact (iInf_le_of_le ⟨{v}, hsub, hcover⟩ le_rfl).trans (by simp)

/-- Assume [the Anthony–Bartlett covering and concentration bounds](hyp:hAnthony),
[a nonempty scalar class](hyp:hne), [a positive K](hyp:hK),
[absolute values bounded by K throughout the class](hyp:hG),
[pseudo-dimension at most v](hyp:hv), [a positive sample size m](hyp:hm),
and [a positive radius r](hyp:hr). Then [the unnormalized empirical covering
number at r is at most e(v + 1)(2 + 4eKm/r)ᵛ](goal). -/
-- @node: empirical_scalar_cover_le
lemma empirical_scalar_cover_le
    (hAnthony : AnthonyBartlettCoveringConcentration)
    {X : Type} {G : Set (X → ℝ)} (hne : G.Nonempty)
    {K : ℝ} (hK : 0 < K) (hG : ∀ g ∈ G, ∀ x, |g x| ≤ K)
    {v : ℕ} (hv : Causalean.Stat.Concentration.HasPseudoDimAtMost (fun g : G => g.val) v)
    {m : ℕ} (hm : 0 < m) {r : ℝ} (hr : 0 < r) :
    (empiricalL1CoveringNumber (ENNReal.ofReal r)
      ((fun f : X → ℝ => fun x => WithLp.toLp 1 (fun _ : Fin 1 => f x)) '' G) m).toENNReal ≤
      ENNReal.ofReal (Real.exp 1 * (v+1) * (2 + 4 * Real.exp 1 * K * m / r)^v) := by
  have hbase : 0 ≤ 4 * Real.exp 1 * K * m / r := by positivity
  by_cases hsmall : r ≤ 2*K*m
  · refine (empirical_scalar_cover_le_of_radius_le hAnthony hne hK hG hv hm hr hsmall).trans ?_
    apply ENNReal.ofReal_le_ofReal
    gcongr
    linarith
  · have hcover := empirical_scalar_cover_le_one hne hK.le hG m (lt_of_not_ge hsmall)
    have hcoeff : 1 ≤ Real.exp 1 * ((v : ℝ)+1) :=
      one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by norm_num)) (by have := Nat.cast_nonneg (α := ℝ) v; linarith)
    have hpow : 1 ≤ (2 + 4 * Real.exp 1 * K * m / r)^v :=
      one_le_pow₀ (by linarith)
    have hbound : 1 ≤ Real.exp 1 * ((v : ℝ)+1) *
        (2 + 4 * Real.exp 1 * K * m / r)^v := one_le_mul_of_one_le_of_one_le hcoeff hpow
    exact (ENat.toENNReal_mono hcover).trans (by
      simpa only [ENat.toENNReal_one, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hbound)

end
end Papers.TbsNeuralCausalPi
