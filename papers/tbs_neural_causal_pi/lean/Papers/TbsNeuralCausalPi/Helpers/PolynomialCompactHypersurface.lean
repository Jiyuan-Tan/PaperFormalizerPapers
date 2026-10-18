module
public import Papers.TbsNeuralCausalPi.Helpers.PolynomialCompactArrangement
/-! # Moving strict sign witnesses to a compact hypersurface

Every witness in a positive superlevel of the arrangement barrier can be
moved to its boundary along a line, stopping at the first level crossing.
The path stays away from every original zero set, so all signs are preserved.
The resulting compact hypersurface has controlled degree in the original
variables. Its quantitative component bound remains to be proved.
-/
public section
namespace Papers.TbsNeuralCausalPi

-- @node: polynomialArrangement_first_level_crossing
/-- If [a real-valued function is continuous](hyp:hf), [its value at zero is at
least ε](hyp:h0), and [its value at one is at most ε](hyp:h1), then
[there is a time between zero and one at which its value equals ε, with its
value remaining at least ε at every time from zero to that time](goal). -/
lemma polynomialArrangement_first_level_crossing (f : ℝ → ℝ) (hf : Continuous f)
    (ε : ℝ) (h0 : ε ≤ f 0) (h1 : f 1 ≤ ε) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, f t = ε ∧ ∀ u ∈ Set.Icc (0 : ℝ) t, ε ≤ f u := by
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1)
    hf.continuousOn ⟨h1, h0⟩
  have hc : IsCompact (Set.Icc (0 : ℝ) 1 ∩ {t | f t = ε}) :=
    isCompact_Icc.inter_right (isClosed_eq hf continuous_const)
  obtain ⟨t, ht, hmin⟩ := hc.exists_isMinOn ⟨t, ht, he⟩ continuousOn_id
  refine ⟨t, ht.1, ht.2, ?_⟩
  intro u hu
  by_contra h
  have hlt : f u < ε := lt_of_not_ge h
  obtain ⟨v, hv, he⟩ := intermediate_value_Icc' hu.1 hf.continuousOn ⟨hlt.le, h0⟩
  have htv : t ≤ v := hmin ⟨⟨hv.1, hv.2.trans (hu.2.trans ht.1.2)⟩, he⟩
  have hut : u = t := le_antisymm hu.2 (htv.trans hv.2)
  exact hlt.ne (hut ▸ ht.2)

-- @node: polynomialCompactBarrier_exists_nonpositive
/-- For a finite polynomial family in a nonempty finite set of variables and any
real R, [there is a point where the compact barrier polynomial is nonpositive](goal). -/
lemma polynomialCompactBarrier_exists_nonpositive {I V : Type*}
    [Fintype I] [Fintype V] [Nonempty V]
    (p : I → MvPolynomial V ℝ) (R : ℝ) :
    ∃ b : V → ℝ, MvPolynomial.eval b (polynomialCompactBarrier p R) ≤ 0 := by
  classical
  let b : V → ℝ := fun _ => |R| + 1
  let v : V := Classical.choice inferInstance
  have hsum : (|R| + 1) ^ 2 ≤ ∑ w, b w ^ 2 :=
    Finset.single_le_sum (fun w _ => sq_nonneg (b w)) (Finset.mem_univ v)
  have hball : R - ∑ w, b w ^ 2 ≤ 0 := by
    have habs := abs_nonneg R
    have hR := le_abs_self R
    nlinarith [sq_nonneg |R|]
  refine ⟨b, ?_⟩
  rw [polynomialCompactBarrier_eval]
  exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hball

-- @node: polynomialCompactSuperlevel_sign_on_level
/-- If [ε is positive](hyp:hε) and [a lies in the barrier superlevel set at
height ε](hyp:ha), then [there is a point on the barrier level ε with exactly
the same strict polynomial sign pattern as a](goal). -/
lemma polynomialCompactSuperlevel_sign_on_level {I V : Type*}
    [Fintype I] [Fintype V] [Nonempty V]
    (p : I → MvPolynomial V ℝ) (R : ℝ) {ε : ℝ} (hε : 0 < ε)
    {a : V → ℝ} (ha : a ∈ polynomialCompactSuperlevel p R ε) :
    ∃ b : V → ℝ, MvPolynomial.eval b (polynomialCompactBarrier p R) = ε ∧
      strictPolynomialSignPattern p b = strictPolynomialSignPattern p a := by
  obtain ⟨z, hz⟩ := polynomialCompactBarrier_exists_nonpositive p R
  let line : ℝ → V → ℝ := fun t v => a v + t * (z v - a v)
  have hline : Continuous line := by fun_prop
  let f : ℝ → ℝ := fun t => MvPolynomial.eval (line t) (polynomialCompactBarrier p R)
  have hf : Continuous f := (MvPolynomial.continuous_eval _).comp hline
  have h0 : ε ≤ f 0 := by
    simpa [f, line] using
      (show ε ≤ MvPolynomial.eval a (polynomialCompactBarrier p R) from ha)
  have h1 : f 1 ≤ ε := by
    have he : line 1 = z := by funext v; dsimp [line]; ring
    simpa only [f, he] using hz.trans hε.le
  obtain ⟨t, ht, he, hbefore⟩ := polynomialArrangement_first_level_crossing f hf ε h0 h1
  refine ⟨line t, he, ?_⟩
  have hnonzero : ∀ u ∈ Set.Icc (0 : ℝ) t,
      line u ∈ polynomialNonzeroDomain p := by
    intro u hu
    exact (polynomialCompactSuperlevel_properties p R hε (hbefore u hu)).1
  funext i
  apply Bool.decide_congr
  have hsign := sign_eq_on_preconnected_nonzero isPreconnected_Icc
    (fun u => MvPolynomial.eval (line u) (p i))
    ((MvPolynomial.continuous_eval _).comp hline).continuousOn
    (fun u hu => hnonzero u hu i)
    (show t ∈ Set.Icc (0 : ℝ) t from ⟨ht.1, le_rfl⟩)
    (show 0 ∈ Set.Icc (0 : ℝ) t from ⟨le_rfl, ht.1⟩)
  simpa [line] using hsign

-- @node: polynomialCompactLevel_isCompact
/-- If [ε is positive](hyp:hε), then [the set where the compact barrier
polynomial equals ε is compact](goal). -/
lemma polynomialCompactLevel_isCompact {I V : Type*} [Fintype I] [Fintype V]
    (p : I → MvPolynomial V ℝ) (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    IsCompact {a | MvPolynomial.eval a (polynomialCompactBarrier p R) = ε} := by
  apply (polynomialCompactSuperlevel_isCompact p R hε).of_isClosed_subset
    (isClosed_eq (MvPolynomial.continuous_eval _) continuous_const)
  intro a ha
  exact ha.ge

-- @node: polynomialCompactLevel_carries_signs
/-- For a finite polynomial family in a nonempty finite set of variables,
[there are positive R and ε such that the barrier level ε realizes exactly
the strict sign patterns realized where all the original polynomials are nonzero](goal). -/
lemma polynomialCompactLevel_carries_signs {I V : Type*}
    [Fintype I] [Fintype V] [Nonempty V] (p : I → MvPolynomial V ℝ) :
    ∃ R ε : ℝ, 0 < R ∧ 0 < ε ∧
      strictPolynomialSignPattern p ''
          {a | MvPolynomial.eval a (polynomialCompactBarrier p R) = ε} =
        strictPolynomialSignPattern p '' polynomialNonzeroDomain p := by
  obtain ⟨R, ε, hR, hε, hsigns⟩ := polynomialCompactSuperlevel_carries_signs p
  refine ⟨R, ε, hR, hε, Set.Subset.antisymm ?_ ?_⟩
  · exact Set.image_mono (fun a ha =>
      (polynomialCompactSuperlevel_properties p R hε ha.ge).1)
  · rw [← hsigns]
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hsign⟩ := polynomialCompactSuperlevel_sign_on_level p R hε ha
    exact ⟨b, hb, hsign⟩

-- @node: strictPolynomialSignPattern_compact_hypersurface_reduction
/-- If [each polynomial in the family has total degree at most d](hyp:hd), then
[there is a polynomial in the same variables of total degree at most twice
the number of polynomials times d plus two, whose zero set is compact and has
at least as many connected components as there are strict sign patterns on the
domain where all original polynomials are nonzero](goal). -/
lemma strictPolynomialSignPattern_compact_hypersurface_reduction {I V : Type*}
    [Fintype I] [Finite V] [Nonempty V] (p : I → MvPolynomial V ℝ) (d : ℕ)
    (hd : ∀ i, (p i).totalDegree ≤ d) :
    ∃ Q : MvPolynomial V ℝ,
      Q.totalDegree ≤ 2 * Fintype.card I * d + 2 ∧
      IsCompact {a | MvPolynomial.eval a Q = 0} ∧
      (strictPolynomialSignPattern p '' polynomialNonzeroDomain p).encard ≤
        ((fun a => connectedComponentIn {b | MvPolynomial.eval b Q = 0} a) ''
          {a | MvPolynomial.eval a Q = 0}).encard := by
  classical
  let := Fintype.ofFinite V
  obtain ⟨R, ε, _, hε, hsigns⟩ := polynomialCompactLevel_carries_signs p
  let Q := polynomialCompactBarrier p R - MvPolynomial.C ε
  have hzero : {a | MvPolynomial.eval a Q = 0} =
      {a | MvPolynomial.eval a (polynomialCompactBarrier p R) = ε} := by
    ext a
    simp [Q, sub_eq_zero]
  refine ⟨Q, ?_, ?_, ?_⟩
  · exact (MvPolynomial.totalDegree_sub _ _).trans
      (max_le (polynomialCompactBarrier_degree p R d hd) (by simp))
  · rw [hzero]
    exact polynomialCompactLevel_isCompact p R hε
  · rw [hzero, ← hsigns]
    exact strictPolynomialSignPattern_encard_le_subset_components p
      (fun a ha => (polynomialCompactSuperlevel_properties p R hε ha.ge).1)

-- @node: polynomialComparisonPattern_compact_hypersurface_reduction
/-- If [each polynomial in the family has total degree at most d](hyp:hd), then
[there is a polynomial in one additional variable of total degree at most
four times the number of polynomials times the larger of d and one, plus two,
whose zero set is compact and has at least as many connected components as
there are weak and strict comparison patterns of the original family](goal). -/
lemma polynomialComparisonPattern_compact_hypersurface_reduction {I V : Type*}
    [Fintype I] [Finite V] (p : I → MvPolynomial V ℝ) (d : ℕ)
    (hd : ∀ i, (p i).totalDegree ≤ d) :
    ∃ Q : MvPolynomial (Option V) ℝ,
      Q.totalDegree ≤ 4 * Fintype.card I * max d 1 + 2 ∧
      IsCompact {a | MvPolynomial.eval a Q = 0} ∧
      (Set.range (polynomialComparisonPattern p)).encard ≤
        ((fun a => connectedComponentIn {b | MvPolynomial.eval b Q = 0} a) ''
          {a | MvPolynomial.eval a Q = 0}).encard := by
  classical
  let shifted : I × Bool → MvPolynomial (Option V) ℝ :=
    fun ib => signShiftPolynomial (p ib.1) ib.2
  obtain ⟨Q, hdegree, hcompact, hcount⟩ :=
    strictPolynomialSignPattern_compact_hypersurface_reduction shifted (max d 1)
      (fun ib => (signShiftPolynomial_degree _ _).trans (max_le_max (hd ib.1) le_rfl))
  refine ⟨Q, hdegree.trans_eq ?_, hcompact, ?_⟩
  · simp only [Fintype.card_prod, Fintype.card_bool]
    ring
  · exact (polynomialComparisonPattern_encard_le_nonzero p).trans hcount

end Papers.TbsNeuralCausalPi
