module

public import Papers.OaiReconstructionMilnorTheory.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.FieldTheory.Minpoly.Finite
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-! # The intersection of all iterated power subfields is the named base -/

@[expose] public section

namespace Papers.OaiReconstructionMilnorTheory

variable (p : ℕ) (κ F : Type*) [Field κ] [Field F] [Algebra κ F]

-- @node: ass:perfect-core-field
/-- For [a modulus p](hyp:p), [a base field κ](hyp:κ), and [an extension field
F of κ](hyp:F), [the perfect-core field condition](goal) means that κ is
algebraically closed and F is a finitely generated field extension of κ of
characteristic p. -/
def PerfectCoreField : Prop := GeometricField p κ F

-- @node: perfectCore_transcendental_of_not_base
/-- If [κ is algebraically closed and F is a finitely generated extension of κ
of characteristic p](hyp:hF) and [f is outside the image of κ in F](hyp:hf),
then [f is transcendental over κ](goal). -/
lemma perfectCore_transcendental_of_not_base (hF : PerfectCoreField p κ F)
    {f : F} (hf : f ∉ Set.range (algebraMap κ F)) : Transcendental κ f := by
  let : IsAlgClosed κ := hF.1
  intro halg
  let : Algebra.IsAlgebraic κ (IntermediateField.adjoin κ {f}) :=
    IntermediateField.isAlgebraic_adjoin_simple halg.isIntegral
  have hbot := IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic
    (IntermediateField.adjoin κ {f})
  have hmem : f ∈ IntermediateField.adjoin κ {f} :=
    IntermediateField.subset_adjoin κ {f} (Set.mem_singleton f)
  rw [hbot] at hmem
  exact hf hmem

-- @node: perfectCore_base_subset
/-- If [p is prime](hyp:hp) and [κ is algebraically closed and F is a finitely
generated extension of κ of characteristic p](hyp:hF), then [every element of
the image of κ in F is a p-to-the-m-th power in F for every positive integer m](goal). -/
lemma perfectCore_base_subset (hp : PrimeChar p) (hF : PerfectCoreField p κ F) :
    Set.range (algebraMap κ F) ⊆
      (⋂ m : ℕ, ⋂ (_ : 1 ≤ m), Set.range fun x : F => x ^ (p ^ m)) := by
  rintro _ ⟨a, rfl⟩
  apply Set.mem_iInter.mpr
  intro m
  apply Set.mem_iInter.mpr
  intro _
  let : IsAlgClosed κ := hF.1
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq a (pow_pos hp.pos m)
  exact ⟨algebraMap κ F b, by simpa only [map_pow] using congrArg (algebraMap κ F) hb⟩

-- @node: perfectCore_radical_degree_le
/-- For an intermediate field E over which F has finite dimension, if [n is
nonzero](hyp:hn), [the polynomial X to the n-th power minus a is irreducible over
E](hyp:hirr), and [g in F has n-th power equal to a](hyp:hg), then [n is at most
the degree of F over E](goal). -/
lemma perfectCore_radical_degree_le (E : IntermediateField κ F)
    [FiniteDimensional E F] (a : E) {n : ℕ} (hn : n ≠ 0)
    (hirr : Irreducible (Polynomial.X ^ n - Polynomial.C a))
    {g : F} (hg : g ^ n = (a : F)) : n ≤ Module.finrank E F := by
  have hroot : Polynomial.aeval g (Polynomial.X ^ n - Polynomial.C a) = 0 := by
    simp [hg]
  have hmin : minpoly E g = Polynomial.X ^ n - Polynomial.C a :=
    (minpoly.eq_of_irreducible_of_monic hirr hroot (Polynomial.monic_X_pow_sub_C a hn)).symm
  have hdeg := minpoly.natDegree_le (A := E) g
  rw [hmin, Polynomial.natDegree_X_pow_sub_C] at hdeg
  exact hdeg

-- @node: perfectCore_not_mem_of_irreducible_powers
/-- Suppose [p is prime](hyp:hp) and F has finite dimension over an intermediate
field E. If [X to the power p-to-the-m minus a is irreducible over E for every
positive integer m](hyp:hirr), then [a fails to be a p-to-the-m-th power in F
for at least one positive integer m](goal). -/
lemma perfectCore_not_mem_of_irreducible_powers (hp : PrimeChar p)
    (E : IntermediateField κ F) [FiniteDimensional E F] (a : E)
    (hirr : ∀ m : ℕ, 1 ≤ m →
      Irreducible (Polynomial.X ^ (p ^ m) - Polynomial.C a)) :
    (a : F) ∉ (⋂ m : ℕ, ⋂ (_ : 1 ≤ m), Set.range fun x : F => x ^ (p ^ m)) := by
  intro ha
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (Module.finrank E F) hp.one_lt
  have hmpos : 1 ≤ m := by
    by_contra h
    have hm0 : m = 0 := by omega
    have hD := Module.finrank_pos (R := E) (M := F)
    simp only [hm0, pow_zero] at hm
    omega
  obtain ⟨g, hg⟩ := Set.mem_iInter.mp (Set.mem_iInter.mp ha m) hmpos
  have hle := perfectCore_radical_degree_le κ F E a (pow_ne_zero m hp.ne_zero)
    (hirr m hmpos) hg
  exact (not_lt_of_ge hle) hm

-- @node: perfectCore_parameter_eisenstein
/-- Over any field B, if [n is nonzero](hyp:hn), then [the polynomial Y to the
n-th power minus X is irreducible as a polynomial in Y with coefficients in
the polynomial ring B[X]](goal). -/
lemma perfectCore_parameter_eisenstein (B : Type*) [Field B] {n : ℕ} (hn : n ≠ 0) :
    Irreducible (Polynomial.X ^ n - Polynomial.C (Polynomial.X : Polynomial B)) := by
  classical
  let P : Ideal (Polynomial B) := Ideal.span {Polynomial.X}
  have hprime : P.IsPrime := (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr
    Polynomial.prime_X
  have hmonic := Polynomial.monic_X_pow_sub_C (Polynomial.X : Polynomial B) hn
  apply Polynomial.IsEisensteinAt.irreducible (𝓟 := P) _ hprime hmonic.isPrimitive
    (by simpa using Nat.pos_of_ne_zero hn)
  apply hmonic.isEisensteinAt_of_mem_of_notMem hprime.ne_top
  · intro i hi
    have hin : i ≠ n := by simpa only [Polynomial.natDegree_X_pow_sub_C] using ne_of_lt hi
    by_cases hi0 : i = 0
    · subst i
      simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Ne.symm hn, ite_false,
        Polynomial.coeff_C_zero, zero_sub]
      exact P.neg_mem (Ideal.subset_span (Set.mem_singleton _))
    · simp [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C, hin, hi0]
  · simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Ne.symm hn, ite_false,
      Polynomial.coeff_C_zero, zero_sub, Ideal.neg_mem_iff]
    change Polynomial.X ∉ (Ideal.span {Polynomial.X} : Ideal (Polynomial B)) ^ 2
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro hdiv
    have hdeg := Polynomial.natDegree_le_of_dvd hdiv Polynomial.X_ne_zero
    simp at hdeg

-- @node: perfectCore_ratFunc_radical_irreducible
/-- Over any field B, if [n is nonzero](hyp:hn), then [the polynomial Y to the
n-th power minus X is irreducible over the rational function field B(X)](goal). -/
lemma perfectCore_ratFunc_radical_irreducible (B : Type*) [Field B]
    {n : ℕ} (hn : n ≠ 0) :
    Irreducible (Polynomial.X ^ n - Polynomial.C (RatFunc.X : RatFunc B)) := by
  have h := Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map
    (K := RatFunc B) (Polynomial.monic_X_pow_sub_C (Polynomial.X : Polynomial B) hn)
  simpa using h.mp (perfectCore_parameter_eisenstein B hn)

-- @node: perfectCore_adjoin_radical_irreducible
/-- If [f is transcendental over B](hyp:hf) and [n is nonzero](hyp:hn), then
[the polynomial X to the n-th power minus f is irreducible over the field
generated by B and f](goal). -/
lemma perfectCore_adjoin_radical_irreducible (B L : Type*) [Field B] [Field L]
    [Algebra B L] {f : L} (hf : Transcendental B f) {n : ℕ} (hn : n ≠ 0) :
    Irreducible (Polynomial.X ^ n -
      Polynomial.C (IntermediateField.AdjoinSimple.gen B f)) := by
  let e := RatFunc.algEquivOfTranscendental f hf
  have h := (MulEquiv.irreducible_iff (f := Polynomial.mapEquiv e.toRingEquiv)).mpr
    (perfectCore_ratFunc_radical_irreducible B hn)
  have he : e RatFunc.X = IntermediateField.AdjoinSimple.gen B f := by
    apply Subtype.ext
    exact RatFunc.algEquivOfTranscendental_X f hf
  simp only [Polynomial.mapEquiv_apply, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C] at h
  change Irreducible (Polynomial.X ^ n - Polynomial.C (e RatFunc.X)) at h
  rwa [he] at h

-- @node: perfectCore_finite_rational_model
/-- If [F is finitely generated as a field over κ](hyp:hfg) and [f is
transcendental over κ](hyp:hf), then [there is an intermediate field E over
which F has finite dimension, containing an element a whose image in F is f,
such that X to the n-th power minus a is irreducible over E for every nonzero
natural number n](goal). -/
lemma perfectCore_finite_rational_model
    (hfg : (⊤ : IntermediateField κ F).FG) {f : F} (hf : Transcendental κ f) :
    ∃ (E : IntermediateField κ F) (_ : FiniteDimensional E F) (a : E),
      (a : F) = f ∧ ∀ n : ℕ, n ≠ 0 →
        Irreducible (Polynomial.X ^ n - Polynomial.C a) := by
  classical
  have hsingle : AlgebraicIndepOn κ id ({f} : Set F) :=
    (algebraicIndependent_singleton_iff (⟨f, rfl⟩ : ({f} : Set F))).mpr hf
  obtain ⟨s, hfs, hs⟩ := exists_isTranscendenceBasis_superset hsingle
  have hmem : f ∈ s := hfs (Set.mem_singleton f)
  let B := IntermediateField.adjoin κ (s \ {f})
  let E₀ := IntermediateField.adjoin B ({f} : Set F)
  let E := E₀.restrictScalars κ
  have hins : insert f (s \ {f}) = s := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro (rfl | ⟨hx, _⟩)
      · exact hmem
      · exact hx
    · intro hx
      by_cases hxf : x = f
      · exact Or.inl hxf
      · exact Or.inr ⟨hx, hxf⟩
  have hind : AlgebraicIndepOn κ id (insert f (s \ {f})) := hins.symm ▸ hs.1
  have htB : Transcendental B f := by
    apply (IntermediateField.transcendental_adjoin_iff).mpr
    have ht := ((AlgebraicIndepOn.insert_iff (R := κ) (x := id)
      (s := s \ {f}) (i := f) (by simp)).mp hind).2
    rw [Set.image_id] at ht
    exact ht
  have hE : E = IntermediateField.adjoin κ s := by
    dsimp [E, E₀, B]
    rw [IntermediateField.adjoin_adjoin_left]
    congr 1
    rw [Set.union_comm, Set.singleton_union, hins]
  let : Algebra.IsAlgebraic E F := by
    rw [hE]
    have halg := hs.isAlgebraic_field
    rw [Subtype.range_coe] at halg
    exact halg
  let : Algebra.EssFiniteType κ F := IntermediateField.fg_top_iff.mp hfg
  let : Algebra.EssFiniteType E F := Algebra.EssFiniteType.of_comp κ E F
  let : FiniteDimensional E F := Algebra.finite_of_essFiniteType_of_isAlgebraic
  refine ⟨E, inferInstance, IntermediateField.AdjoinSimple.gen B f, rfl, ?_⟩
  intro n hn
  exact perfectCore_adjoin_radical_irreducible B F htB hn

-- @node: lem:perfect-core
/-- If [p is prime](hyp:hp) and [κ is algebraically closed and F is a finitely
generated extension of κ of characteristic p](hyp:hF), then [the elements of F
that are p-to-the-m-th powers for every positive integer m are exactly the
image of κ in F](goal). -/
lemma iInter_pow_eq_base (hp : PrimeChar p) (hF : PerfectCoreField p κ F) :
    (⋂ m : ℕ, ⋂ (_ : 1 ≤ m), Set.range fun x : F => x ^ (p ^ m)) =
      Set.range (algebraMap κ F) := by
  apply Set.Subset.antisymm
  · intro f hf
    by_contra hbase
    have htrans := perfectCore_transcendental_of_not_base p κ F hF hbase
    obtain ⟨E, hfinite, a, ha, hirr⟩ :=
      perfectCore_finite_rational_model κ F hF.2.2 htrans
    let : FiniteDimensional E F := hfinite
    exact perfectCore_not_mem_of_irreducible_powers p κ F hp E a
      (fun m _ => hirr (p ^ m) (pow_ne_zero m hp.ne_zero))
      (ha.symm ▸ hf)
  · exact perfectCore_base_subset p κ F hp hF

end Papers.OaiReconstructionMilnorTheory
