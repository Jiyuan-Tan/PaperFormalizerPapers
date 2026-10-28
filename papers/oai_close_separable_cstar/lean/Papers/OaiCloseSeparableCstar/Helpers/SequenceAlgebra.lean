module

public import Papers.OaiCloseSeparableCstar.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-! # Proposition 2: convergent-sequence algebras -/

@[expose] public section

namespace Papers.OaiCloseSeparableCstar

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable (D P Q : StarSubalgebra ℂ (Op L))

/-- For [a coordinate index](hyp:n) and [an operator on the underlying Hilbert
space](hyp:a), the [single-coordinate operator](goal) applies that operator at
the chosen coordinate and is zero at every other coordinate. -/
-- @node: seqCornerOp
noncomputable def seqCornerOp (n : ℕ) (a : Op L) : Op (SumSpace L) :=
  diagOp (fun k => if k = n then a else 0) ‖a‖ (by
    intro k
    split_ifs <;> simp)

omit [CompleteSpace L] in
/-- [Applying a single-coordinate operator to a vector gives the vector supported
at that coordinate whose value is the given operator applied to the input
vector's coordinate](goal). -/
-- @node: seqCornerOp_apply
lemma seqCornerOp_apply (n : ℕ) (a : Op L) (v : SumSpace L) :
    seqCornerOp n a v = lp.single 2 n (a (v n)) := by
  ext k
  by_cases hk : k = n
  · subst k; simp [seqCornerOp, diagOp]
  · simp [seqCornerOp, diagOp, lp.single_apply, hk]

/-- If [an operator belongs to D](hyp:ha), then [the operator supported at any
single coordinate with that entry belongs to the sequence algebra with entries
in D and limits in P](goal). -/
-- @node: seqCornerOp_mem
lemma seqCornerOp_mem (n : ℕ) {a : Op L} (ha : a ∈ D) :
    seqCornerOp n a ∈ seqAlg D P := by
  refine ⟨fun k => if k = n then a else 0, ?_, ⟨0, P.zero_mem, ?_⟩, ?_⟩
  · intro k
    change (if k = n then a else 0) ∈ D
    split_ifs <;> first | exact ha | exact D.zero_mem
  · apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_gt_atTop n] with k hk
    simp [ne_of_gt hk]
  · intro v k
    rfl

/-- If [an operator commutes with every member of the sequence algebra with
entries in D and limits in P](hyp:hT), then [it also commutes with every member
of the sequence algebra with entries in D and limits in Q](goal). -/
-- @node: seqAlg_commutant_transfer
lemma seqAlg_commutant_transfer {T : Op (SumSpace L)}
    (hT : T ∈ commutant (seqAlg D P : Set (Op (SumSpace L)))) :
    T ∈ commutant (seqAlg D Q : Set (Op (SumSpace L))) := by
  have hc (n : ℕ) (a : Op L) (ha : a ∈ D) (v : SumSpace L) :
      a ((T v) n) = (T (lp.single 2 n (a (v n)))) n := by
    have h := congrArg (fun R : Op (SumSpace L) => (R v) n)
      (hT (seqCornerOp n a) (seqCornerOp_mem D P n ha))
    change (seqCornerOp n a (T v)) n = (T (seqCornerOp n a v)) n at h
    simpa only [seqCornerOp_apply, lp.single_apply_self] using h
  intro S hS
  rcases hS with ⟨x, hx, _, hS⟩
  ext v n
  change (S (T v)) n = (T (S v)) n
  rw [hS]
  calc
    x n ((T v) n) = (T (lp.single 2 n (x n (v n)))) n := hc n (x n) (hx n) v
    _ = (T (S v)) n := by
      have h := hc n 1 D.one_mem (S v)
      simpa only [one_apply_eq_self, hS] using h.symm

/-- [The commutants of the sequence algebras with entries in D and limits in P
or Q are equal](goal). -/
-- @node: seqAlg_commutant_eq
lemma seqAlg_commutant_eq :
    commutant (seqAlg D P : Set (Op (SumSpace L))) =
      commutant (seqAlg D Q : Set (Op (SumSpace L))) := by
  apply Set.Subset.antisymm
  · intro T hT
    exact seqAlg_commutant_transfer D P Q hT
  · intro T hT
    exact seqAlg_commutant_transfer D Q P hT

/-- For [a coordinate index](hyp:n) and [an operator on the Hilbert direct
sum](hyp:T), the [coordinate compression](goal) inserts an input at that
coordinate, applies the operator, and reads the same coordinate of the output. -/
-- @node: seqEntry
noncomputable def seqEntry (n : ℕ) (T : Op (SumSpace L)) : Op L :=
  (lp.evalCLM ℂ (fun _ : ℕ => L) 2 n).comp
    (T.comp (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => L) 2 n))

/-- [The norm of an operator compressed to any single coordinate is at most
the norm of the original operator](goal). -/
-- @node: seqEntry_norm_le
lemma seqEntry_norm_le (n : ℕ) (T : Op (SumSpace L)) :
    ‖seqEntry n T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  let w : SumSpace L := lp.single 2 n v
  change ‖(T w) n‖ ≤ ‖T‖ * ‖v‖
  calc
    _ ≤ ‖T w‖ := lp.norm_apply_le_norm (by norm_num) (T w) n
    _ ≤ ‖T‖ * ‖w‖ := T.le_opNorm w
    _ = ‖T‖ * ‖v‖ := by rw [lp.norm_single (by norm_num)]

/-- [The distance between the compressions of two operators to the same
coordinate is at most the distance between the original operators](goal). -/
-- @node: seqEntry_dist_le
lemma seqEntry_dist_le (n : ℕ) (T S : Op (SumSpace L)) :
    dist (seqEntry n T) (seqEntry n S) ≤ dist T S := by
  have he : seqEntry n (T - S) = seqEntry n T - seqEntry n S := by
    ext v
    rfl
  simpa only [dist_eq_norm_sub, he] using seqEntry_norm_le n (T - S)

/-- [Compression to a fixed coordinate is a continuous function of the
operator](goal). -/
-- @node: seqEntry_continuous
@[fun_prop] lemma seqEntry_continuous (n : ℕ) : Continuous (seqEntry (L := L) n) := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro T S
  simpa using seqEntry_dist_le n T S

/-- If [an operator acts separately at each coordinate according to a given
sequence of operators](hyp:hT), then [its compression to any coordinate equals
the corresponding operator in that sequence](goal). -/
-- @node: seqEntry_eq
lemma seqEntry_eq {T : Op (SumSpace L)} {x : ℕ → Op L}
    (hT : ∀ v n, (T v) n = x n (v n)) (n : ℕ) : seqEntry n T = x n := by
  ext v
  change (T (lp.single 2 n v)) n = x n v
  rw [hT, lp.single_apply_self]

/-- If [the coordinate compressions of one operator converge to p](hyp:hp) and
[those of another operator converge to q](hyp:hq), then [the distance between p
and q is at most the distance between the two original operators](goal). -/
-- @node: seqAlg_limit_dist_le
lemma seqAlg_limit_dist_le {T S : Op (SumSpace L)} {p q : Op L}
    (hp : Filter.Tendsto (fun n => seqEntry n T) Filter.atTop (nhds p))
    (hq : Filter.Tendsto (fun n => seqEntry n S) Filter.atTop (nhds q)) :
    dist p q ≤ dist T S := by
  exact le_of_tendsto (hp.dist hq) (Filter.Eventually.of_forall
    (fun n => seqEntry_dist_le n T S))

/-- If [D is closed in operator norm](hyp:hD) and [P is closed in operator
norm](hyp:hP), then [the sequence algebra with entries in D and limits in P is
closed in operator norm](goal). -/
-- @node: seqAlg_isClosed
lemma seqAlg_isClosed (hD : IsClosed (D : Set (Op L)))
    (hP : IsClosed (P : Set (Op L))) :
    IsClosed (seqAlg D P : Set (Op (SumSpace L))) := by
  classical
  apply IsSeqClosed.isClosed
  intro T S hT hTS
  change ∀ k, ∃ x : ℕ → Op L, (∀ n, x n ∈ D) ∧
    (∃ p ∈ P, Filter.Tendsto x Filter.atTop (nhds p)) ∧
      ∀ v n, (T k v) n = x n (v n) at hT
  choose x hx hpdata hdiag using hT
  choose p hp hxp using hpdata
  have he (k n : ℕ) : seqEntry n (T k) = x k n := seqEntry_eq (hdiag k) n
  have hl (k : ℕ) : Filter.Tendsto (fun n => seqEntry n (T k))
      Filter.atTop (nhds (p k)) := by simpa only [he] using hxp k
  have hpc : CauchySeq p := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hTS.cauchySeq ε hε
    refine ⟨N, fun j hj k hk => ?_⟩
    exact (seqAlg_limit_dist_le (hl j) (hl k)).trans_lt (hN j hj k hk)
  obtain ⟨q, hpq⟩ := cauchySeq_tendsto_of_complete hpc
  have hq : q ∈ P := hP.mem_of_tendsto hpq (Filter.Eventually.of_forall hp)
  have hu : TendstoUniformly (fun k n => seqEntry n (T k)) (fun n => seqEntry n S)
      Filter.atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hTS ε hε
    filter_upwards [Filter.eventually_ge_atTop N] with k hk n
    have hk := hN k hk
    exact (seqEntry_dist_le n S (T k)).trans_lt (by simpa [dist_comm] using hk)
  refine ⟨fun n => seqEntry n S, ?_, ⟨q, hq, ?_⟩, ?_⟩
  · intro n
    apply hD.mem_of_tendsto ((seqEntry_continuous n).tendsto S |>.comp hTS)
    exact Filter.Eventually.of_forall (fun k => by
      change seqEntry n (T k) ∈ D
      rw [he]
      exact hx k n)
  · exact hu.tendsto_of_eventually_tendsto (Filter.Eventually.of_forall hl) hpq
  · intro v n
    have hleft : Filter.Tendsto (fun k => (T k v) n) Filter.atTop (nhds ((S v) n)) := by
      have hc : Continuous (fun R : Op (SumSpace L) => (R v) n) := by
        exact (lp.evalCLM ℂ (fun _ : ℕ => L) 2 n).continuous.comp
          (ContinuousLinearMap.apply ℂ (SumSpace L) v).continuous
      exact (hc.tendsto S).comp hTS
    have hright : Filter.Tendsto (fun k => x k n (v n)) Filter.atTop
        (nhds (seqEntry n S (v n))) := by
      have h := ((seqEntry_continuous n).tendsto S).comp hTS
      have hh : Filter.Tendsto (fun k => seqEntry n (T k) (v n)) Filter.atTop
          (nhds (seqEntry n S (v n))) :=
        ((ContinuousLinearMap.apply ℂ L (v n)).continuous.tendsto (seqEntry n S)).comp h
      simpa only [he] using hh
    exact tendsto_nhds_unique hleft (by simpa only [hdiag] using hright)

omit [CompleteSpace L] in
/-- If [C is nonnegative](hyp:hC), [every entry of a sequence of operators has
norm at most C](hyp:hx), and [an operator acts separately at each coordinate
using those entries](hyp:hT), then [its operator norm is at most C](goal). -/
-- @node: seqDiagonal_norm_le
lemma seqDiagonal_norm_le {T : Op (SumSpace L)} {x : ℕ → Op L} {C : ℝ}
    (hC : 0 ≤ C) (hx : ∀ n, ‖x n‖ ≤ C)
    (hT : ∀ v n, (T v) n = x n (v n)) : ‖T‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro v
  calc
    ‖T v‖ ≤ ‖(C : ℂ) • v‖ := lp.norm_mono (by norm_num) (fun n => by
      rw [hT]
      change ‖x n (v n)‖ ≤ ‖(C : ℂ) • v n‖
      simpa [norm_smul, Complex.norm_real, abs_of_nonneg hC] using
        (x n).le_opNorm (v n) |>.trans
          (mul_le_mul_of_nonneg_right (hx n) (norm_nonneg _)))
    _ = C * ‖v‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]

omit [CompleteSpace L] in
/-- [Inserting an operator at a fixed coordinate and setting all other
coordinates to zero depends continuously on that operator](goal). -/
-- @node: seqCornerOp_continuous
@[fun_prop] lemma seqCornerOp_continuous (n : ℕ) :
    Continuous (seqCornerOp (L := L) n) := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simp only [dist_eq_norm_sub, NNReal.coe_one, one_mul]
  apply seqDiagonal_norm_le (x := fun k => if k = n then a - b else 0)
    (norm_nonneg _)
  · intro k
    split_ifs <;> simp
  · intro v k
    change (seqCornerOp n a v) k - (seqCornerOp n b v) k = _
    simp only [seqCornerOp, diagOp, LinearMap.mkContinuous_apply, LinearMap.coe_mk,
      AddHom.coe_mk]
    split_ifs <;> simp

omit [CompleteSpace L] in
/-- [The map sending an operator to the diagonal operator that applies it at
every coordinate is continuous](goal). -/
-- @node: seqConstantOp_continuous
@[fun_prop] lemma seqConstantOp_continuous :
    Continuous (constantDiagOp (I := ℕ) (V := L)) := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simp only [dist_eq_norm_sub, NNReal.coe_one, one_mul]
  apply seqDiagonal_norm_le (x := fun _ => a - b) (norm_nonneg _)
    (fun _ => le_rfl)
  intro v k
  rfl

omit [CompleteSpace L] in
/-- [Applying the sum of the single-coordinate operators at indices below N
to a vector gives, at coordinate k, the k-th operator applied to the k-th input
coordinate when k is below N, and zero otherwise](goal). -/
-- @node: seqCornerOp_sum_apply
lemma seqCornerOp_sum_apply (N : ℕ) (x : ℕ → Op L) (v : SumSpace L) (k : ℕ) :
    ((∑ n ∈ Finset.range N, seqCornerOp n (x n)) v) k =
      if k < N then x k (v k) else 0 := by
  classical
  simp only [sum_apply, lp.coeFn_sum, Finset.sum_apply,
    seqCornerOp_apply, lp.single_apply]
  simp [Finset.mem_range]

/-- If [D has a countable dense subset](hyp:hD) and [P is contained in D](hyp:hPD),
then [the sequence algebra with entries in D and limits in P has a countable
dense subset](goal). -/
-- @node: seqAlg_isSeparable
lemma seqAlg_isSeparable (hD : TopologicalSpace.IsSeparable (D : Set (Op L)))
    (hPD : P ≤ D) :
    TopologicalSpace.IsSeparable (seqAlg D P : Set (Op (SumSpace L))) := by
  classical
  let F : Set (Op (SumSpace L)) :=
    (constantDiagOp (I := ℕ) '' (P : Set (Op L))) ∪
      ⋃ n : ℕ, seqCornerOp n '' (D : Set (Op L))
  have hF : TopologicalSpace.IsSeparable F :=
    ((hD.mono hPD).image seqConstantOp_continuous).union
      (.iUnion fun n => hD.image (seqCornerOp_continuous n))
  apply (hF.span (R := ℂ)).closure.mono
  intro T hT
  rcases hT with ⟨x, hx, ⟨p, hp, hxp⟩, hdiag⟩
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hxp (ε / 2) (half_pos hε)
  let S : Op (SumSpace L) := constantDiagOp (I := ℕ) p +
    ∑ n ∈ Finset.range N, seqCornerOp n (x n - p)
  refine ⟨S, ?_, ?_⟩
  · apply Submodule.add_mem
    · apply Submodule.subset_span
      exact Or.inl ⟨p, hp, rfl⟩
    · apply Submodule.sum_mem
      intro n hn
      apply Submodule.subset_span
      exact Or.inr (Set.mem_iUnion.mpr ⟨n, x n - p,
        D.sub_mem (hx n) (hPD hp), rfl⟩)
  · rw [dist_eq_norm_sub]
    apply lt_of_le_of_lt _ (half_lt_self hε)
    apply seqDiagonal_norm_le (x := fun n => if n < N then 0 else x n - p)
      (half_pos hε).le
    · intro n
      split_ifs with hn
      · simpa using (half_pos hε).le
      · simpa only [dist_eq_norm_sub] using (hN n (Nat.le_of_not_gt hn)).le
    · intro v n
      change (T v) n - ((constantDiagOp p) v +
        (∑ k ∈ Finset.range N, seqCornerOp k (x k - p)) v) n = _
      rw [lp.coeFn_add, Pi.add_apply, hdiag, seqCornerOp_sum_apply]
      change x n (v n) - (p (v n) + (if n < N then (x n - p) (v n) else 0)) = _
      split_ifs <;> simp

/-- [The unit ball of P is nonempty](goal). -/
-- @node: unitBall_nonempty
lemma unitBall_nonempty : (unitBall P).Nonempty :=
  ⟨0, P.zero_mem, by simp⟩

/-- [The extended Hausdorff distance between the unit balls of P and Q is
finite](goal). -/
-- @node: unitBall_hausdorffEDist_ne_top
lemma unitBall_hausdorffEDist_ne_top :
    Metric.hausdorffEDist (unitBall P) (unitBall Q) ≠ ⊤ := by
  have hb (A : StarSubalgebra ℂ (Op L)) : Bornology.IsBounded (unitBall A) := by
    apply (Metric.isBounded_closedBall (x := (0 : Op L)) (r := 1)).subset
    intro a ha
    simpa only [Metric.mem_closedBall, dist_zero_right] using ha.2
  exact Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
    (unitBall_nonempty P) (unitBall_nonempty Q) (hb P) (hb Q)

/-- If [an operator belongs to the unit ball of the sequence algebra with
entries in D and limits in P](hyp:hT), then [its coordinate compressions
converge to an operator in the unit ball of P](goal). -/
-- @node: seqAlg_unitBall_limit
lemma seqAlg_unitBall_limit {T : Op (SumSpace L)} (hT : T ∈ unitBall (seqAlg D P)) :
    ∃ p ∈ unitBall P,
      Filter.Tendsto (fun n => seqEntry n T) Filter.atTop (nhds p) := by
  rcases hT.1 with ⟨x, hx, ⟨p, hp, hxp⟩, hdiag⟩
  have he (n : ℕ) : seqEntry n T = x n := seqEntry_eq hdiag n
  have hl : Filter.Tendsto (fun n => seqEntry n T) Filter.atTop (nhds p) := by
    simpa only [he] using hxp
  refine ⟨p, ⟨hp, ?_⟩, hl⟩
  exact le_of_tendsto hl.norm (Filter.Eventually.of_forall
    (fun n => (seqEntry_norm_le n T).trans hT.2))

/-- If [P is contained in D](hyp:hPD) and [p belongs to the unit ball of P](hyp:hp),
then [the constant diagonal operator with entry p belongs to the unit ball of
the sequence algebra with entries in D and limits in P](goal). -/
-- @node: seqConstant_unitBall
lemma seqConstant_unitBall (hPD : P ≤ D) {p : Op L} (hp : p ∈ unitBall P) :
    constantDiagOp (I := ℕ) p ∈ unitBall (seqAlg D P) := by
  constructor
  · exact ⟨fun _ => p, fun _ => hPD hp.1, ⟨p, hp.1, tendsto_const_nhds⟩,
      fun _ _ => rfl⟩
  · exact seqDiagonal_norm_le (by norm_num) (fun _ => hp.2) (fun _ _ => rfl)

/-- If [Q is contained in D](hyp:hQD), [T belongs to the unit ball of the sequence
algebra with entries in D and limits in P](hyp:hT), and [the error tolerance is
positive](hyp:hε), then [there is an operator in the unit ball of the sequence
algebra with entries in D and limits in Q whose distance from T is at most the
Kadison–Kastler distance between P and Q plus that tolerance](goal). -/
-- @node: seqAlg_unitBall_approx
lemma seqAlg_unitBall_approx (hQD : Q ≤ D) {T : Op (SumSpace L)}
    (hT : T ∈ unitBall (seqAlg D P)) {ε : ℝ} (hε : 0 < ε) :
    ∃ S ∈ unitBall (seqAlg D Q), dist T S ≤ kkDist P Q + ε := by
  classical
  obtain ⟨p, hp, hl⟩ := seqAlg_unitBall_limit D P hT
  obtain ⟨q, hq, hpq⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt hp
    (lt_add_of_pos_right (kkDist P Q) (half_pos hε))
    (unitBall_hausdorffEDist_ne_top P Q)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hl (ε / 2) (half_pos hε)
  rcases hT.1 with ⟨x, hx, _, hdiag⟩
  have he (n : ℕ) : seqEntry n T = x n := seqEntry_eq hdiag n
  have hxn (n : ℕ) : ‖x n‖ ≤ 1 := by
    rw [← he]
    exact (seqEntry_norm_le n T).trans hT.2
  let y : ℕ → Op L := fun n => if n < N then x n else q
  have hy (n : ℕ) : ‖y n‖ ≤ 1 := by
    dsimp [y]
    split_ifs
    · exact hxn n
    · exact hq.2
  let S : Op (SumSpace L) := diagOp y 1 hy
  have hS (v : SumSpace L) (n : ℕ) : (S v) n = y n (v n) := rfl
  refine ⟨S, ⟨?_, seqDiagonal_norm_le (by norm_num) hy hS⟩, ?_⟩
  · refine ⟨y, ?_, ⟨q, hq.1, ?_⟩, hS⟩
    · intro n
      dsimp [y]
      split_ifs
      · exact hx n
      · exact hQD hq.1
    · apply tendsto_const_nhds.congr'
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      simp [y, not_lt.mpr hn]
  · rw [dist_eq_norm_sub]
    apply seqDiagonal_norm_le (x := fun n => x n - y n)
      (add_nonneg Metric.hausdorffDist_nonneg hε.le)
    · intro n
      by_cases hn : n < N
      · simp only [y, if_pos hn, sub_self, norm_zero]
        exact add_nonneg Metric.hausdorffDist_nonneg hε.le
      · have hnp : dist (x n) p < ε / 2 := by
          simpa only [he, dist_comm] using hN n (Nat.le_of_not_gt hn)
        have hdist := (dist_triangle (x n) p q).trans_lt (add_lt_add hnp hpq)
        simpa only [y, if_neg hn, ← dist_eq_norm_sub, kkDist] using
          hdist.le.trans (by linarith : ε / 2 + (kkDist P Q + ε / 2) ≤ kkDist P Q + ε)
    · intro v n
      change (T v) n - (S v) n = _
      rw [hdiag, hS]
      rfl

/-- [The distance from p to the unit ball of Q is at most the distance from the
constant diagonal operator with entry p to the unit ball of the sequence
algebra with entries in D and limits in Q](goal). -/
-- @node: seqConstant_infDist_le
lemma seqConstant_infDist_le {p : Op L} :
    Metric.infDist p (unitBall Q) ≤
      Metric.infDist (constantDiagOp (I := ℕ) p) (unitBall (seqAlg D Q)) := by
  apply (Metric.le_infDist (unitBall_nonempty (seqAlg D Q))).mpr
  intro S hS
  obtain ⟨q, hq, hl⟩ := seqAlg_unitBall_limit D Q hS
  have hc : Filter.Tendsto
      (fun n => seqEntry n (constantDiagOp (I := ℕ) p)) Filter.atTop (nhds p) := by
    have he (n : ℕ) : seqEntry n (constantDiagOp (I := ℕ) p) = p :=
      seqEntry_eq (x := fun _ => p) (fun _ _ => rfl) n
    simpa only [he] using (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => p) _ _)
  exact (Metric.infDist_le_dist_of_mem hq).trans (seqAlg_limit_dist_le hc hl)

/-- If [P is contained in D](hyp:hPD) and [Q is contained in D](hyp:hQD), then
[the Kadison–Kastler distance between the sequence algebras with entries in D
and limits in P or Q equals the Kadison–Kastler distance between P and Q](goal). -/
-- @node: seqAlg_kkDist_eq
lemma seqAlg_kkDist_eq (hPD : P ≤ D) (hQD : Q ≤ D) :
    kkDist (seqAlg D P) (seqAlg D Q) = kkDist P Q := by
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    apply Metric.hausdorffDist_le_of_mem_dist
      (add_nonneg Metric.hausdorffDist_nonneg hε.le)
    · intro T hT
      exact seqAlg_unitBall_approx D P Q hQD hT hε
    · intro T hT
      obtain ⟨S, hS, hd⟩ := seqAlg_unitBall_approx D Q P hPD hT hε
      exact ⟨S, hS, by simpa only [kkDist, Metric.hausdorffDist_comm] using hd⟩
  · apply Metric.hausdorffDist_le_of_infDist Metric.hausdorffDist_nonneg
    · intro p hp
      exact (seqConstant_infDist_le D Q).trans
        (Metric.infDist_le_hausdorffDist_of_mem (seqConstant_unitBall D P hPD hp)
          (unitBall_hausdorffEDist_ne_top (seqAlg D P) (seqAlg D Q)))
    · intro q hq
      have h := (seqConstant_infDist_le D P (p := q)).trans
        (Metric.infDist_le_hausdorffDist_of_mem (seqConstant_unitBall D Q hQD hq)
          (unitBall_hausdorffEDist_ne_top (seqAlg D Q) (seqAlg D P)))
      simpa only [kkDist, Metric.hausdorffDist_comm] using h

end Papers.OaiCloseSeparableCstar
