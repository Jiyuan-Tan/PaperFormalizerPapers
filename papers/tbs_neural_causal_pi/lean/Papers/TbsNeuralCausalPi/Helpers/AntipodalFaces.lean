module
public import Mathlib.Analysis.Convex.SimplicialComplex.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic
/-! # Finite signed faces for the local antipodal sphere construction

A cross-polytope face contains no pair of opposite signed coordinate vertices.
This file supplies the abstract finite complex; its geometric realization and
the parity argument are separate proof obligations.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
namespace Antipodal

/-- With [n coordinate directions](hyp:n), a [signed vertex](goal) is a coordinate
index together with a Boolean sign, where true means positive and false means negative. -/
abbrev SignedVertex (n : ℕ) := Fin n × Bool

-- @node: signedAntipode
/-- The [antipode](goal) of [a signed coordinate vertex](hyp:v) keeps its coordinate
index and reverses its sign. -/
def signedAntipode {n : ℕ} (v : SignedVertex n) : SignedVertex n :=
  (v.1, !v.2)

-- @node: signedAntipode_involutive
/-- [Reversing the sign of a signed vertex twice returns the original vertex](goal). -/
@[simp] lemma signedAntipode_involutive {n : ℕ} (v : SignedVertex n) :
    signedAntipode (signedAntipode v) = v := by
  rcases v with ⟨i, b⟩
  cases b <;> rfl

-- @node: signedAntipode_injective
/-- [Distinct signed vertices have distinct antipodes](goal). -/
lemma signedAntipode_injective {n : ℕ} :
    Function.Injective (signedAntipode : SignedVertex n → SignedVertex n) :=
  fun x y h => by simpa using congrArg signedAntipode h

-- @node: signedAntipode_ne
/-- [The antipode of any signed vertex differs from that vertex](goal). -/
lemma signedAntipode_ne {n : ℕ} (v : SignedVertex n) : signedAntipode v ≠ v := by
  rcases v with ⟨i, b⟩
  cases b <;> simp [signedAntipode]

-- @node: NoOpposite
/-- For [a finite set of signed vertices](hyp:s), the [no-opposite condition](goal)
requires that the antipode of every vertex in the set lies outside the set. -/
def NoOpposite {n : ℕ} (s : Finset (SignedVertex n)) : Prop :=
  ∀ v ∈ s, signedAntipode v ∉ s

-- @node: noOpposite_mono
/-- If [a finite set of signed vertices contains no opposite pair](hyp:hs) and
[another set is a subset of it](hyp:hts), then [the subset also contains no opposite pair](goal). -/
lemma noOpposite_mono {n : ℕ} {s t : Finset (SignedVertex n)}
    (hs : NoOpposite s) (hts : t ⊆ s) : NoOpposite t :=
  fun v hv hneg => hs v (hts hv) (hts hneg)

-- @node: noOpposite_singleton
/-- [A set consisting of a single signed vertex contains no opposite pair](goal). -/
lemma noOpposite_singleton {n : ℕ} (v : SignedVertex n) : NoOpposite {v} := by
  intro w hw hneg
  have hwv : w = v := Finset.mem_singleton.mp hw
  subst w
  exact signedAntipode_ne v (Finset.mem_singleton.mp hneg)

-- @node: noOpposite_image_antipode
/-- If [a finite set of signed vertices contains no opposite pair](hyp:hs), then
[the set of their antipodes also contains no opposite pair](goal). -/
lemma noOpposite_image_antipode {n : ℕ} {s : Finset (SignedVertex n)}
    (hs : NoOpposite s) : NoOpposite (s.image signedAntipode) := by
  intro v hv hneg
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨z, hz, hzw⟩ := Finset.mem_image.mp hneg
  have hzw' : z = signedAntipode w := by
    simpa using congrArg signedAntipode hzw
  exact hs w hw (hzw' ▸ hz)

-- @node: signedFaceComplex
/-- In [n coordinate directions](hyp:n), the [abstract signed-face complex](goal)
has as its faces all nonempty finite sets of signed vertices containing no opposite pair. -/
def signedFaceComplex (n : ℕ) : PreAbstractSimplicialComplex (SignedVertex n) where
  faces := {s | s.Nonempty ∧ NoOpposite s}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨hs.1, fun t hts ht => ⟨ht, noOpposite_mono hs.2 hts⟩⟩

-- @node: signedFaceComplex_faces_finite
/-- [The abstract signed-face complex has finitely many faces](goal). -/
lemma signedFaceComplex_faces_finite (n : ℕ) : (signedFaceComplex n).faces.Finite :=
  Set.toFinite _

-- @node: signedFaceComplex_antipode
/-- If [a set of signed vertices is a face of the abstract signed-face complex](hyp:hs),
then [replacing every vertex by its antipode gives another face](goal). -/
lemma signedFaceComplex_antipode {n : ℕ} {s : Finset (SignedVertex n)}
    (hs : s ∈ (signedFaceComplex n).faces) :
    s.image signedAntipode ∈ (signedFaceComplex n).faces :=
  ⟨hs.1.image _, noOpposite_image_antipode hs.2⟩

-- @node: signedFaceComplex_ne_antipode
/-- If [a set of signed vertices is a face of the abstract signed-face complex](hyp:hs),
then [the set of its antipodes differs from the original face](goal). -/
lemma signedFaceComplex_ne_antipode {n : ℕ} {s : Finset (SignedVertex n)}
    (hs : s ∈ (signedFaceComplex n).faces) : s.image signedAntipode ≠ s := by
  intro heq
  obtain ⟨v, hv⟩ := hs.1
  have hneg : signedAntipode v ∈ s.image signedAntipode := Finset.mem_image_of_mem _ hv
  exact hs.2 v hv (heq ▸ hneg)

-- @node: signedVertexVector
/-- The [coordinate vector](goal) representing [a signed vertex](hyp:v) is zero
except at the vertex's coordinate, where it equals one for a positive sign and minus one for a negative sign. -/
def signedVertexVector {n : ℕ} (v : SignedVertex n) : Fin n → ℝ :=
  fun i => if i = v.1 then if v.2 then 1 else -1 else 0

-- @node: signedVertexVector_antipode
/-- [The coordinate vector of a vertex's antipode is the negative of the vertex's coordinate vector](goal). -/
lemma signedVertexVector_antipode {n : ℕ} (v : SignedVertex n) :
    signedVertexVector (signedAntipode v) = -signedVertexVector v := by
  rcases v with ⟨i, b⟩
  funext j
  cases b <;> by_cases h : j = i <;> simp [signedVertexVector, signedAntipode, h]

-- @node: signedVertexVector_injective
/-- [Distinct signed vertices have distinct coordinate vectors](goal). -/
lemma signedVertexVector_injective {n : ℕ} :
    Function.Injective (signedVertexVector : SignedVertex n → (Fin n → ℝ)) := by
  rintro ⟨i, ε⟩ ⟨j, δ⟩ h
  have hij : i = j := by
    by_contra hij
    have he := congrFun h i
    cases ε <;> cases δ <;> simp [signedVertexVector, hij] at he
  subst j
  have he := congrFun h i
  cases ε <;> cases δ <;> simp_all [signedVertexVector] <;> norm_num at he

-- @node: noOpposite_card_le
/-- If [a finite set of signed vertices contains no opposite pair](hyp:hs), then
[its number of vertices is at most the number of coordinate directions](goal). -/
lemma noOpposite_card_le {n : ℕ} {s : Finset (SignedVertex n)}
    (hs : NoOpposite s) : s.card ≤ n := by
  have hinj : Set.InjOn Prod.fst (s : Set (SignedVertex n)) := by
    intro a ha b hb hij
    rcases a with ⟨i, ε⟩
    rcases b with ⟨j, δ⟩
    change i = j at hij
    subst j
    by_cases h : ε = δ
    · exact congrArg (fun c => (i, c)) h
    · have hflip : signedAntipode (i, ε) = (i, δ) := by
        cases ε <;> cases δ <;> simp_all [signedAntipode]
      exact False.elim (hs _ ha (hflip.symm ▸ hb))
  calc
    s.card = (s.image Prod.fst).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ n := by
      simpa using Finset.card_le_card (Finset.subset_univ (s.image Prod.fst))

end Antipodal
end Papers.TbsNeuralCausalPi
