# The corrected paper and its Lean formalization — oai_reconstruction_milnor_theory

For each result of the corrected paper: its statement, the Lean declaration that states it, whether that declaration is proved, and how the two statements correspond phrase by phrase. A result stated differently from the original paper is marked "corrected"; the report says what changed and why.

## Theorem 1.1

**Statement.** \label{thm:main} Let $K/k$ and $L/l$ be finitely generated extensions of algebraically closed fields of characteristic $p$, with \[ \trdeg(K/k)\ge2,\qquad \trdeg(L/l)\ge2. \] The canonical map \[ \Isom(K,k;L,l)\longrightarrow \Isom_{\mathrm M}(V_K,V_L)/\Lambda^\times, \qquad \alpha\longmapsto[\alpha_*], \] is bijective.

**Lean.** `Papers.OaiReconstructionMilnorTheory.milnor_reconstruction_bijective` — `lean/Papers/OaiReconstructionMilnorTheory/TMain.lean:23`

**Status.** proved in Lean, under 3 condition(s) made explicit. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| Let $K/k$ and $L/l$ be finitely generated extensions of algebraically closed fields of characteristic $p$, | `k : Subfield K`<br>`l : Subfield L`<br>`hp : PrimeChar p`<br>`hfields : MainFields p k l` |
| with \[ \trdeg(K/k)\ge2,\qquad | `hdim : MainDimension k l` |
| \trdeg(L/l)\ge2. \] | `hdim : MainDimension k l` |
| The canonical map | — (no Lean counterpart recorded) |
| \[ \Isom(K,k;L,l)\longrightarrow \Isom_{\mathrm M}(V_K,V_L)/\Lambda^\times, \qquad \alpha\longmapsto[\alpha_*], \] | ≈ `∀ α : K ≃+* L`<br>≈ `IsBaseIso k l (⇑α)`<br>≈ then `IsCompatibleIso p (inducedMap p α)`<br>≈ `∀ Θ : MilnorOne K p → MilnorOne L p`<br>≈ `IsCompatibleIso p Θ`<br>≈ then `IsBaseIso k l (⇑α)`<br>≈ `∀ α β : K ≃+* L`<br>≈ `IsBaseIso k l (⇑α)`<br>≈ `IsBaseIso k l (⇑β)`<br>≈ `∀ r : (Coeff p)ˣ`<br>≈ `inducedMap p β = scalarAct p r (inducedMap p α)` |
| is bijective. | then `∃ α : K ≃+* L,`<br>then `∃ r : (Coeff p)ˣ, Θ = scalarAct p r (inducedMap p α)`<br>then `α = β` |

A row marked ≈ was given these phrases with many rows of its result at once, not on its own.

Lean also declares what the paper leaves implicit (the objects and their types): `p : ℕ`, `K L : Type*`, `Field K`, `Field L`.

**Conditions and readings, and the Lean definitions that carry them.**

- reading: In Lemma~\ref{lem:affine-symbol}, $d\in C^\times$ is a locally quantified affine coefficient independent of the previously defined integer $\trdeg(F/\kappa)$. → `AffineCoeffPin` (`lean/Papers/OaiReconstructionMilnorTheory/Helpers/Symbols.lean:69`)
- reading: $\Fp[X]=\Span_{\Fp}\{[X]\}$ and $\Fp[Y]=\Span_{\Fp}\{[Y]\}$ as subspaces of $V_F$. → `FpMultiplesPin` (`lean/Papers/OaiReconstructionMilnorTheory/Helpers/IntersectionSetup.lean:49`)
- reading: $D_s,D_t$ are the coordinate Euler derivations associated with $s,t$ in one fixed, arbitrarily chosen $p$-basis of $F/C$ extending the pair $s,t$. → `IsCoordEulerDerivation` (`lean/Papers/OaiReconstructionMilnorTheory/Helpers/Symbols.lean:24`)
- condition of the paper: Fix a prime $p$ → `PrimeChar` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:32`)
- definition of the paper: write $\Lambda=\Fp$. → `Coeff` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:41`)
- definition of the paper: For a field $F$ of characteristic $p$, set \[ V_F=F^\times/(F^\times)^p=\KM_1(F)/p. \] → `MilnorOne` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:46`)
- definition of the paper: We write $[f]$ for the class of $f\in F^\times$ and use additive notation in $V_F$: thus $[f]+[g]=[fg]$, $r[f]=[f^r]$ for $r\in\Z$, and $[1]=0$. → `cls` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:75`)
- definition of the paper: Define the Steinberg relation subspace \[ R_F=\Span_{\Lambda} \{[f]\otimes[1-f]:f\in F\setminus\{0,1\}\} \subset V_F\otimes_{\Lambda}V_F. \] → `steinbergRel` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:116`)
- definition of the paper: The quotient $W_F=(V_F\otimes_{\Lambda}V_F)/R_F$ is $\KM_2(F)/p$ by the tensor presentation of Milnor $K$-theory \cite[Section~1]{Milnor1970}. → `MilnorTwo` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:125`)
- definition of the paper: We denote the image of $[f]\otimes[g]$ in $W_F$ by $\{f,g\}_F$. → `milnorSymbol` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:144`)
- definition of the paper: Since $(F^\times)^p=C^\times$, the underlying set of $V_F$ is the point set of the projective space $\PP_C(F)$: the class $[f]$ represents the one-dimensional $C$-subspace $Cf$. → `projPoint` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:173`)
- definition of the paper: its projective lines are the sets of one-dimensional subspaces in two-dimensional $C_F$-subspaces of $F$. → `IsProjLine` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:163`)
- definition of the paper: Put $C_F=F^p$. → `powSubfield` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:155`)
- definition of the paper: Let $\Isom_{\mathrm M}(V_K,V_L)$ be the set of $\Lambda$-linear isomorphisms $\Theta:V_K\to V_L$ satisfying \[ (\Theta\otimes\Theta)(R_K)=R_L. \] → `IsCompatibleIso` (`lean/Papers/OaiReconstructionMilnorTheory/Helpers/Isomorphisms.lean:48`)
- definition of the paper: For specified subfields $k\subset K$ and $l\subset L$, write $\Isom(K,k;L,l)$ for the field isomorphisms $\alpha:K\to L$ with $\alpha(k)=l$. → `IsBaseIso` (`lean/Papers/OaiReconstructionMilnorTheory/Helpers/Isomorphisms.lean:73`)
- definition of the paper: Such an isomorphism induces $\alpha_*([f])=[\alpha(f)]$ → `inducedMap` (`lean/Papers/OaiReconstructionMilnorTheory/Helpers/Isomorphisms.lean:82`)
- definition of the paper: Put $H=K^p$ and $C=L^p$. → `linesPowerFields` (`lean/Papers/OaiReconstructionMilnorTheory/Helpers/Isomorphisms.lean:98`)
- condition of the paper: Let $K/k$ and $L/l$ be finitely generated extensions of algebraically closed fields of characteristic $p$ → `MainFields` (`lean/Papers/OaiReconstructionMilnorTheory/Helpers/Isomorphisms.lean:107`)
- condition of the paper: \[ \trdeg(K/k)\ge2,\qquad \trdeg(L/l)\ge2. \] → `MainDimension` (`lean/Papers/OaiReconstructionMilnorTheory/Helpers/Isomorphisms.lean:116`)
- definition of the paper: Scalar multiplication by $\Lambda^\times$ acts on this set. → `scalarCompatibleAction` (`lean/Papers/OaiReconstructionMilnorTheory/Helpers/CompatibleOperations.lean:117`)

## Lemma 2.1

**Statement.** \label{lem:p-degree} With the notation above, $[F:C]=p^d$.

**Lean.** `Papers.OaiReconstructionMilnorTheory.finrank_powSubfield_eq_pow_trdeg` — `lean/Papers/OaiReconstructionMilnorTheory/Helpers/PDegree.lean:117`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| With the notation above, $[F:C]=p^d$. | `p : ℕ`<br>then `FiniteDimensional ↥(powerDegreeSetup p κ F).1 F`<br>then `Module.finrank ↥(powerDegreeSetup p κ F).1 F = p ^ (powerDegreeSetup p κ F).2` |

Lean also declares what the paper leaves implicit (the objects and their types): `κ F : Type*`, `Field κ`, `Field F`, `Algebra κ F`.

Lean assumes conditions that the paper's text does not state: `hp : PrimeChar p`, `hF : GeometricField p κ F`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: Fix a prime $p$ → `PrimeChar` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:32`)
- condition of the paper: Let $F/\kappa$ be a finitely generated extension of an algebraically closed field of characteristic $p$ → `GeometricField` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:183`)
- definition of the paper: and put \[ C=F^p,\qquad d=\trdeg(F/\kappa). \] → `powerDegreeSetup` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:192`)

## Lemma 2.2

**Statement.** \label{lem:p-basis} Let $F$ be any field of characteristic $p$, and put $C=F^p$. If $C\subseteq M\subseteq F$ and $s\in F\setminus M$, then $[M(s):M]=p$. If $[F:C]$ is finite, every $p$-independent list extends to a $p$-basis $s_1,\ldots,s_e$ of $F/C$, with $[F:C]=p^e$ and monomial basis \[ \{s_1^{i_1}\cdots s_e^{i_e}:0\leq i_j<p\}. \] For such a basis there are commuting $C$-linear derivations $D_1,\ldots,D_e$ on $F$ satisfying \[ D_j(s_1^{i_1}\cdots s_e^{i_e}) =i_j s_1^{i_1}\cdots s_e^{i_e}. \] On $C(s_j)$ the kernel of $D_j$ is $C$, and its nonzero eigenvectors with eigenvalue in $C$ are precisely the elements $c s_j^i$, where $c\in C^\times$ and $0\leq i<p$; their eigenvalues are $i\in\Fp$. Moreover, $C(s_j)\cap C(s_k)=C$ when $j\ne k$.

**Lean.** `Papers.OaiReconstructionMilnorTheory.pBasis_structure` — `lean/Papers/OaiReconstructionMilnorTheory/Helpers/PBasis.lean:522`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| Let $F$ be any field of characteristic $p$, | `p : ℕ`<br>`F : Type*`<br>`hF : PBasisFieldChar p F` |
| and put $C=F^p$. | — (no Lean counterpart recorded) |
| If $C\subseteq M\subseteq F$ | `M : IntermediateField ↥(pBasisPowSubfield p F) F` |
| and $s\in F\setminus M$, | `s : F`<br>`PBasisAdjunction p M s` |
| then $[M(s):M]=p$. | then `Module.finrank M ↥(IntermediateField.adjoin M {s}) = p` |
| If $[F:C]$ is finite, every $p$-independent list extends to a $p$-basis $s_1,\ldots,s_e$ of $F/C$, | `PBasisFiniteDegree p F`<br>`r : ℕ`<br>`s : Fin r → F`<br>`IsPIndependent p F s`<br>then `∃ (e : ℕ) (h : r ≤ e) (b : Fin e → F),`<br>then `IsPBasis p F b`<br>`∀ i`<br>then `b (Fin.castLE h i) = s i`<br>`e : ℕ`<br>`b : Fin e → F` |
| with $[F:C]=p^e$ and monomial basis | then `Module.finrank ↥(pBasisPowSubfield p F) F = p ^ e`<br>then `LinearIndependent ↥(pBasisPowSubfield p F) (pMonomial p b)`<br>then `Submodule.span ↥(pBasisPowSubfield p F) (Set.range (pMonomial p b)) = ⊤` |
| \[ \{s_1^{i_1}\cdots s_e^{i_e}:0\leq i_j<p\}. \] | then `LinearIndependent ↥(pBasisPowSubfield p F) (pMonomial p b)`<br>then `Submodule.span ↥(pBasisPowSubfield p F) (Set.range (pMonomial p b)) = ⊤` |
| For such a basis there are commuting $C$-linear derivations $D_1,\ldots,D_e$ on $F$ satisfying | `IsPBasis p F b`<br>then `∃ D : Fin e → Derivation ↥(pBasisPowSubfield p F) F F,`<br>`∀ j k x`<br>then `D j (D k x) = D k (D j x)` |
| \[ D_j(s_1^{i_1}\cdots s_e^{i_e}) =i_j s_1^{i_1}\cdots s_e^{i_e}. \] | `∀ j i`<br>then `D j (pMonomial p b i) = (((i j : ℕ) : ↥(pBasisPowSubfield p F))) • pMonomial p b i` |
| On $C(s_j)$ the kernel of $D_j$ is $C$, | `∀ j`<br>`∀ x ∈ IntermediateField.adjoin ↥(pBasisPowSubfield p F) {b j}`<br>then `D j x = 0 ↔ x ∈ (⊥ : IntermediateField ↥(pBasisPowSubfield p F) F)`<br>`∀ x ∈ IntermediateField.adjoin ↥(pBasisPowSubfield p F) {b j}` |
| and its nonzero eigenvectors with eigenvalue in $C$ are precisely the elements $c s_j^i$, | `∀ j`<br>`x ≠ 0`<br>then `(∃ a : ↥(pBasisPowSubfield p F), D j x = a • x) ↔ ∃ c : ↥(pBasisPowSubfield p F), c ≠ 0 ∧ ∃ i : ℕ, i < p ∧ x = (c : F) * b j ^ i` |
| where $c\in C^\times$ | then `(∃ a : ↥(pBasisPowSubfield p F), D j x = a • x) ↔ ∃ c : ↥(pBasisPowSubfield p F), c ≠ 0 ∧ ∃ i : ℕ, i < p ∧ x = (c : F) * b j ^ i`<br>`∀ j (c : ↥(pBasisPowSubfield p F)) (i : ℕ)` |
| and $0\leq i<p$; | then `(∃ a : ↥(pBasisPowSubfield p F), D j x = a • x) ↔ ∃ c : ↥(pBasisPowSubfield p F), c ≠ 0 ∧ ∃ i : ℕ, i < p ∧ x = (c : F) * b j ^ i`<br>`∀ j (c : ↥(pBasisPowSubfield p F)) (i : ℕ)`<br>`i < p` |
| their eigenvalues are $i\in\Fp$. | then `D j ((c : F) * b j ^ i) = ((i : ↥(pBasisPowSubfield p F))) • ((c : F) * b j ^ i)` |
| Moreover, $C(s_j)\cap C(s_k)=C$ when $j\ne k$. | `∀ j k`<br>`j ≠ k`<br>then `IntermediateField.adjoin ↥(pBasisPowSubfield p F) {b j} ⊓ IntermediateField.adjoin ↥(pBasisPowSubfield p F) {b k} = ⊥` |

Lean also declares what the paper leaves implicit (the objects and their types): `Field F`.

Lean assumes conditions that the paper's text does not state: `hp : PrimeChar p`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: Fix a prime $p$ → `PrimeChar` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:32`)
- definition of the paper: put $C=F^p$. → `pBasisPowSubfield` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:201`)
- definition of the paper: A list $s_1,\ldots,s_r\in F$ is \emph{$p$-independent over $C$} if $[C(s_1,\ldots,s_r):C]=p^r$. → `IsPIndependent` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:224`)
- definition of the paper: A $p$-independent list generating $F$ over $C$ is called a \emph{$p$-basis}. → `IsPBasis` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:231`)
- condition of the paper: Let $F$ be any field of characteristic $p$ → `PBasisFieldChar` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:238`)
- condition of the paper: If $C\subseteq M\subseteq F$ and $s\in F\setminus M$ → `PBasisAdjunction` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:243`)
- condition of the paper: If $[F:C]$ is finite → `PBasisFiniteDegree` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:249`)

## Lemma 2.3

**Statement.** \label{lem:zero-symbol} For $s,t\in F^\times$, one has \[ s\notin C,\qquad \{s,t\}_F=0 \quad\Longrightarrow\quad t\in C(s). \]

**Lean.** `Papers.OaiReconstructionMilnorTheory.mem_adjoin_of_milnorSymbol_eq_zero` — `lean/Papers/OaiReconstructionMilnorTheory/Helpers/Symbols.lean:119`

**Status.** proved in Lean, under 1 condition(s) made explicit. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| For $s,t\in F^\times$, one has | `F : Type*`<br>`s t : F`<br>`hst : ZeroSymbolInputs s t` |
| \[ s\notin C,\qquad | `hzero : ZeroSymbolAntecedent p s t hst` |
| \{s,t\}_F=0 \quad\Longrightarrow\quad | `hzero : ZeroSymbolAntecedent p s t hst` |
| t\in C(s). \] | then `t ∈ IntermediateField.adjoin ↥(powSubfield p F) {s}` |

Lean also declares what the paper leaves implicit (the objects and their types): `p : ℕ`, `Field F`, `κ : Type*`, `Field κ`, `Algebra κ F`.

Lean assumes conditions that the paper's text does not state: `hp : PrimeChar p`, `hF : GeometricField p κ F`.

**Conditions and readings, and the Lean definitions that carry them.**

- reading: $D_s,D_t$ are the coordinate Euler derivations associated with $s,t$ in one fixed, arbitrarily chosen $p$-basis of $F/C$ extending the pair $s,t$. → `IsCoordEulerDerivation` (`lean/Papers/OaiReconstructionMilnorTheory/Helpers/Symbols.lean:24`)
- condition of the paper: Fix a prime $p$ → `PrimeChar` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:32`)
- definition of the paper: write $\Lambda=\Fp$. → `Coeff` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:41`)
- definition of the paper: For a field $F$ of characteristic $p$, set \[ V_F=F^\times/(F^\times)^p=\KM_1(F)/p. \] → `MilnorOne` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:46`)
- definition of the paper: We write $[f]$ for the class of $f\in F^\times$ and use additive notation in $V_F$: thus $[f]+[g]=[fg]$, $r[f]=[f^r]$ for $r\in\Z$, and $[1]=0$. → `cls` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:75`)
- definition of the paper: Define the Steinberg relation subspace \[ R_F=\Span_{\Lambda} \{[f]\otimes[1-f]:f\in F\setminus\{0,1\}\} \subset V_F\otimes_{\Lambda}V_F. \] → `steinbergRel` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:116`)
- definition of the paper: The quotient $W_F=(V_F\otimes_{\Lambda}V_F)/R_F$ is $\KM_2(F)/p$ by the tensor presentation of Milnor $K$-theory \cite[Section~1]{Milnor1970}. → `MilnorTwo` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:125`)
- definition of the paper: We denote the image of $[f]\otimes[g]$ in $W_F$ by $\{f,g\}_F$. → `milnorSymbol` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:144`)
- condition of the paper: Let $F/\kappa$ be a finitely generated extension of an algebraically closed field of characteristic $p$ → `GeometricField` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:183`)
- definition of the paper: and put \[ C=F^p,\qquad d=\trdeg(F/\kappa). \] → `powerDegreeSetup` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:192`)
- definition of the paper: Put $C_F=F^p$. → `powSubfield` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:155`)
- definition of the paper: A list $s_1,\ldots,s_r\in F$ is \emph{$p$-independent over $C$} if $[C(s_1,\ldots,s_r):C]=p^r$. → `IsPIndependent` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:224`)
- definition of the paper: A $p$-independent list generating $F$ over $C$ is called a \emph{$p$-basis}. → `IsPBasis` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:231`)
- definition of the paper: For a $p$-independent pair $s,t$, write $D_s,D_t$ for the corresponding derivations obtained from any extending $p$-basis. → `IsPairDerivations` (`lean/Papers/OaiReconstructionMilnorTheory/Helpers/Symbols.lean:42`)
- condition of the paper: For $s,t\in F^\times$ → `ZeroSymbolInputs` (`lean/Papers/OaiReconstructionMilnorTheory/Helpers/Symbols.lean:52`)
- condition of the paper: If $s\notin C_F$ and $\{s,t\}_F=0$ → `ZeroSymbolAntecedent` (`lean/Papers/OaiReconstructionMilnorTheory/Helpers/Symbols.lean:61`)

## Lemma 2.4

**Statement.** \label{lem:affine-symbol} If $c,d\in C^\times$ and $t,c+dt\in F^\times$, then \[ \{t,c+dt\}_F=0. \]

**Lean.** `Papers.OaiReconstructionMilnorTheory.milnorSymbol_affine_eq_zero` — `lean/Papers/OaiReconstructionMilnorTheory/Helpers/Symbols.lean:136`

**Status.** proved in Lean, under 1 condition(s) made explicit. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| If $c,d\in C^\times$ | `c d t : F`<br>`hinputs : AffineSymbolInputs p c d t` |
| and $t,c+dt\in F^\times$, | `F : Type*`<br>`c d t : F`<br>`hinputs : AffineSymbolInputs p c d t` |
| then \[ \{t,c+dt\}_F=0. \] | then `milnorSymbol p t (c + d * t) hinputs.2.2.1 hinputs.2.2.2 = 0` |

Lean also declares what the paper leaves implicit (the objects and their types): `p : ℕ`, `Field F`, `κ : Type*`, `Field κ`, `Algebra κ F`.

Lean assumes conditions that the paper's text does not state: `hp : PrimeChar p`, `hF : GeometricField p κ F`.

**Conditions and readings, and the Lean definitions that carry them.**

- reading: In Lemma~\ref{lem:affine-symbol}, $d\in C^\times$ is a locally quantified affine coefficient independent of the previously defined integer $\trdeg(F/\kappa)$. → `AffineCoeffPin` (`lean/Papers/OaiReconstructionMilnorTheory/Helpers/Symbols.lean:69`)
- condition of the paper: Fix a prime $p$ → `PrimeChar` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:32`)
- definition of the paper: write $\Lambda=\Fp$. → `Coeff` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:41`)
- definition of the paper: For a field $F$ of characteristic $p$, set \[ V_F=F^\times/(F^\times)^p=\KM_1(F)/p. \] → `MilnorOne` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:46`)
- definition of the paper: We write $[f]$ for the class of $f\in F^\times$ and use additive notation in $V_F$: thus $[f]+[g]=[fg]$, $r[f]=[f^r]$ for $r\in\Z$, and $[1]=0$. → `cls` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:75`)
- definition of the paper: Define the Steinberg relation subspace \[ R_F=\Span_{\Lambda} \{[f]\otimes[1-f]:f\in F\setminus\{0,1\}\} \subset V_F\otimes_{\Lambda}V_F. \] → `steinbergRel` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:116`)
- definition of the paper: The quotient $W_F=(V_F\otimes_{\Lambda}V_F)/R_F$ is $\KM_2(F)/p$ by the tensor presentation of Milnor $K$-theory \cite[Section~1]{Milnor1970}. → `MilnorTwo` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:125`)
- definition of the paper: We denote the image of $[f]\otimes[g]$ in $W_F$ by $\{f,g\}_F$. → `milnorSymbol` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:144`)
- condition of the paper: Let $F/\kappa$ be a finitely generated extension of an algebraically closed field of characteristic $p$ → `GeometricField` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:183`)
- definition of the paper: and put \[ C=F^p,\qquad d=\trdeg(F/\kappa). \] → `powerDegreeSetup` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:192`)
- condition of the paper: If $c,d\in C^\times$ and $t,c+dt\in F^\times$ → `AffineSymbolInputs` (`lean/Papers/OaiReconstructionMilnorTheory/Helpers/Symbols.lean:78`)

## Proposition 3.1

**Statement.** \label{prop:intersection} Let $F$ be a field of characteristic $p$ with $[F:F^p]<\infty$, and put $C=F^p$. Let $X,Y\in F^\times$ be $p$-independent. Suppose \[ U\in C(X)^\times,\qquad V\in C(Y)^\times, \qquad [U]\notin\Fp[X],\qquad [V]\notin\Fp[Y]. \] If \begin{equation} \label{eq:intersection-witness} X\,C(Y/X)^\times\ \cap\ U\,C(V/U)^\times\ne\varnothing, \end{equation} then there is a unique integer $n$, $1\le n<p$, such that \begin{equation} \label{eq:intersection-conclusion} U^n\in C+CX^n,\qquad V^n\in C+CY^n. \end{equation} In fact, either inclusion in \eqref{eq:intersection-conclusion} determines $n$ uniquely. In each inclusion, both coefficients are nonzero.

**Lean.** `Papers.OaiReconstructionMilnorTheory.intersection_unique_power` — `lean/Papers/OaiReconstructionMilnorTheory/Helpers/Intersection.lean:28`

**Status.** proved in Lean, under 1 condition(s) made explicit. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| Let $F$ be a field of characteristic $p$ with $[F:F^p]<\infty$, | `p : ℕ`<br>`F : Type*`<br>`hF : IntersectionFieldChar p F`<br>`hfinite : IntersectionFiniteDegree p F` |
| and put $C=F^p$. | — (no Lean counterpart recorded) |
| Let $X,Y\in F^\times$ be $p$-independent. | `X Y U V : F`<br>`hpair : IntersectionPairInputs p X Y` |
| Suppose \[ U\in C(X)^\times,\qquad | `X Y U V : F`<br>`helements : IntersectionElements p X Y U V` |
| V\in C(Y)^\times, \qquad | `X Y U V : F`<br>`helements : IntersectionElements p X Y U V` |
| [U]\notin\Fp[X],\qquad | `helements : IntersectionElements p X Y U V` |
| [V]\notin\Fp[Y]. \] | `helements : IntersectionElements p X Y U V` |
| If \begin{equation} X\,C(Y/X)^\times\ \cap\ U\,C(V/U)^\times\ne\varnothing, \end{equation} | `hwitness : IntersectionWitness p X Y U V` |
| then there is a unique integer $n$, $1\le n<p$, such that | then `∃ n : ℕ,`<br>then `1 ≤ n`<br>then `n < p`<br>`1 ≤ m`<br>`m < p`<br>`1 ≤ m`<br>`m < p` |
| \begin{equation} U^n\in C+CX^n,\qquad | then `AffPow (intersectionPowSubfield p F) X U m ↔ m = n`<br>then `∃ a ∈ intersectionPowSubfield p F, ∃ b ∈ intersectionPowSubfield p F,`<br>then `U ^ n = a + b * X ^ n` |
| V^n\in C+CY^n. \end{equation} | then `AffPow (intersectionPowSubfield p F) Y V m ↔ m = n`<br>then `∃ a ∈ intersectionPowSubfield p F, ∃ b ∈ intersectionPowSubfield p F,`<br>then `V ^ n = a + b * Y ^ n` |
| In fact, either inclusion in \eqref{eq:intersection-conclusion} determines $n$ uniquely. | `∀ m`<br>then `AffPow (intersectionPowSubfield p F) X U m ↔ m = n`<br>`∀ m`<br>then `AffPow (intersectionPowSubfield p F) Y V m ↔ m = n` |
| In each inclusion, both coefficients are nonzero. | then `a ≠ 0`<br>then `b ≠ 0`<br>then `a ≠ 0`<br>then `b ≠ 0` |

Lean also declares what the paper leaves implicit (the objects and their types): `Field F`.

Lean assumes conditions that the paper's text does not state: `hp : PrimeChar p`.

**Conditions and readings, and the Lean definitions that carry them.**

- reading: $\Fp[X]=\Span_{\Fp}\{[X]\}$ and $\Fp[Y]=\Span_{\Fp}\{[Y]\}$ as subspaces of $V_F$. → `FpMultiplesPin` (`lean/Papers/OaiReconstructionMilnorTheory/Helpers/IntersectionSetup.lean:49`)
- condition of the paper: Fix a prime $p$ → `PrimeChar` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:32`)
- definition of the paper: write $\Lambda=\Fp$. → `Coeff` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:41`)
- definition of the paper: For a field $F$ of characteristic $p$, set \[ V_F=F^\times/(F^\times)^p=\KM_1(F)/p. \] → `MilnorOne` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:46`)
- definition of the paper: We write $[f]$ for the class of $f\in F^\times$ and use additive notation in $V_F$: thus $[f]+[g]=[fg]$, $r[f]=[f^r]$ for $r\in\Z$, and $[1]=0$. → `cls` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:75`)
- definition of the paper: put $C=F^p$. → `intersectionPowSubfield` (`lean/Papers/OaiReconstructionMilnorTheory/Helpers/IntersectionSetup.lean:20`)
- definition of the paper: A list $s_1,\ldots,s_r\in F$ is \emph{$p$-independent over $C$} if $[C(s_1,\ldots,s_r):C]=p^r$. → `IsPIndependent` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:224`)
- definition of the paper: A $p$-independent list generating $F$ over $C$ is called a \emph{$p$-basis}. → `IsPBasis` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:231`)
- condition of the paper: Let $F$ be a field of characteristic $p$ → `IntersectionFieldChar` (`lean/Papers/OaiReconstructionMilnorTheory/Helpers/IntersectionSetup.lean:26`)
- condition of the paper: with $[F:F^p]<\infty$ → `IntersectionFiniteDegree` (`lean/Papers/OaiReconstructionMilnorTheory/Helpers/IntersectionSetup.lean:32`)
- condition of the paper: Let $X,Y\in F^\times$ be $p$-independent. → `IntersectionPairInputs` (`lean/Papers/OaiReconstructionMilnorTheory/Helpers/IntersectionSetup.lean:40`)
- condition of the paper: Suppose \[ U\in C(X)^\times,\qquad V\in C(Y)^\times, \qquad [U]\notin\Fp[X],\qquad [V]\notin\Fp[Y]. \] → `IntersectionElements` (`lean/Papers/OaiReconstructionMilnorTheory/Helpers/IntersectionSetup.lean:59`)
- condition of the paper: If \begin{equation} \label{eq:intersection-witness} X\,C(Y/X)^\times\ \cap\ U\,C(V/U)^\times\ne\varnothing, \end{equation} → `IntersectionWitness` (`lean/Papers/OaiReconstructionMilnorTheory/Helpers/IntersectionSetup.lean:74`)

## Lemma 4.1

**Statement.** \label{lem:scalar-line} Let $F$ have characteristic $p$, with $F\ne F^p$. If multiplication by $r\in\Fp^\times$ on $V_F$ maps every projective line over $F^p$ into a projective line, then $r=1$.

**Lean.** `Papers.OaiReconstructionMilnorTheory.scalar_eq_one_of_preserves_lines` — `lean/Papers/OaiReconstructionMilnorTheory/Helpers/ScalarLine.lean:186`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| Let $F$ have characteristic $p$, | `p : ℕ`<br>`F : Type*`<br>`hF : ScalarLineFieldChar p F` |
| with $F\ne F^p$. | `himperfect : ScalarLineImperfect p F` |
| If multiplication by $r\in\Fp^\times$ on $V_F$ maps every projective line over $F^p$ into a projective line, | `r : (Coeff p)ˣ`<br>`hpreserves : ScalarLinePreservation p F r` |
| then $r=1$. | then `r = 1` |

Lean also declares what the paper leaves implicit (the objects and their types): `Field F`.

Lean assumes conditions that the paper's text does not state: `hp : PrimeChar p`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: Fix a prime $p$ → `PrimeChar` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:32`)
- definition of the paper: write $\Lambda=\Fp$. → `Coeff` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:41`)
- definition of the paper: For a field $F$ of characteristic $p$, set \[ V_F=F^\times/(F^\times)^p=\KM_1(F)/p. \] → `MilnorOne` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:46`)
- definition of the paper: We write $[f]$ for the class of $f\in F^\times$ and use additive notation in $V_F$: thus $[f]+[g]=[fg]$, $r[f]=[f^r]$ for $r\in\Z$, and $[1]=0$. → `cls` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:75`)
- definition of the paper: put $C=F^p$. → `pBasisPowSubfield` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:201`)
- definition of the paper: Since $(F^\times)^p=C^\times$, the underlying set of $V_F$ is the point set of the projective space $\PP_C(F)$: the class $[f]$ represents the one-dimensional $C$-subspace $Cf$. → `projPoint` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:173`)
- definition of the paper: its projective lines are the sets of one-dimensional subspaces in two-dimensional $C_F$-subspaces of $F$. → `IsProjLine` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:163`)
- definition of the paper: Put $C_F=F^p$. → `powSubfield` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:155`)
- condition of the paper: Let $F$ have characteristic $p$ → `ScalarLineFieldChar` (`lean/Papers/OaiReconstructionMilnorTheory/Helpers/ScalarLine.lean:16`)
- condition of the paper: with $F\ne F^p$ → `ScalarLineImperfect` (`lean/Papers/OaiReconstructionMilnorTheory/Helpers/ScalarLine.lean:22`)
- condition of the paper: If multiplication by $r\in\Fp^\times$ on $V_F$ maps every projective line over $F^p$ into a projective line → `ScalarLinePreservation` (`lean/Papers/OaiReconstructionMilnorTheory/Helpers/ScalarLine.lean:29`)

## Proposition 4.2

**Statement.** \label{prop:lines} Let $K/k$ and $L/l$ be finitely generated extensions of algebraically closed fields of characteristic $p$, both of transcendence degree at least two. For every compatible isomorphism $\Theta:V_K\to V_L$, there is a unique $n\in\Fp^\times$ such that $\Psi=n\Theta$ sends every projective line over $K^p$ onto a projective line over $L^p$.

**Lean.** `Papers.OaiReconstructionMilnorTheory.exists_unique_line_correction` — `lean/Papers/OaiReconstructionMilnorTheory/Helpers/Lines.lean:36`

**Status.** proved in Lean, under 3 condition(s) made explicit. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| Let $K/k$ and $L/l$ be finitely generated extensions of algebraically closed fields of characteristic $p$, both of transcendence degree at least two. | `p : ℕ`<br>`K L : Type*`<br>`k : Subfield K`<br>`l : Subfield L`<br>`hp : PrimeChar p`<br>`hfields : LineRecoveryFields p k l` |
| For every compatible isomorphism $\Theta:V_K\to V_L$, there is a unique $n\in\Fp^\times$ such that $\Psi=n\Theta$ sends every projective line over $K^p$ onto a projective line over $L^p$. | `Θ : MilnorOne K p → MilnorOne L p`<br>`hΘ : IsCompatibleIso p Θ`<br>then `∃! n : (Coeff p)ˣ,`<br>`∀ S : Set (MilnorOne K p)`<br>`IsProjLine p K S`<br>then `IsProjLine p L (scalarAct p n Θ '' S)` |

Lean also declares what the paper leaves implicit (the objects and their types): `Field K`, `Field L`.

**Conditions and readings, and the Lean definitions that carry them.**

- reading: In Lemma~\ref{lem:affine-symbol}, $d\in C^\times$ is a locally quantified affine coefficient independent of the previously defined integer $\trdeg(F/\kappa)$. → `AffineCoeffPin` (`lean/Papers/OaiReconstructionMilnorTheory/Helpers/Symbols.lean:69`)
- reading: $\Fp[X]=\Span_{\Fp}\{[X]\}$ and $\Fp[Y]=\Span_{\Fp}\{[Y]\}$ as subspaces of $V_F$. → `FpMultiplesPin` (`lean/Papers/OaiReconstructionMilnorTheory/Helpers/IntersectionSetup.lean:49`)
- reading: $D_s,D_t$ are the coordinate Euler derivations associated with $s,t$ in one fixed, arbitrarily chosen $p$-basis of $F/C$ extending the pair $s,t$. → `IsCoordEulerDerivation` (`lean/Papers/OaiReconstructionMilnorTheory/Helpers/Symbols.lean:24`)
- condition of the paper: Fix a prime $p$ → `PrimeChar` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:32`)
- definition of the paper: write $\Lambda=\Fp$. → `Coeff` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:41`)
- definition of the paper: For a field $F$ of characteristic $p$, set \[ V_F=F^\times/(F^\times)^p=\KM_1(F)/p. \] → `MilnorOne` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:46`)
- definition of the paper: We write $[f]$ for the class of $f\in F^\times$ and use additive notation in $V_F$: thus $[f]+[g]=[fg]$, $r[f]=[f^r]$ for $r\in\Z$, and $[1]=0$. → `cls` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:75`)
- definition of the paper: Define the Steinberg relation subspace \[ R_F=\Span_{\Lambda} \{[f]\otimes[1-f]:f\in F\setminus\{0,1\}\} \subset V_F\otimes_{\Lambda}V_F. \] → `steinbergRel` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:116`)
- definition of the paper: The quotient $W_F=(V_F\otimes_{\Lambda}V_F)/R_F$ is $\KM_2(F)/p$ by the tensor presentation of Milnor $K$-theory \cite[Section~1]{Milnor1970}. → `MilnorTwo` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:125`)
- definition of the paper: We denote the image of $[f]\otimes[g]$ in $W_F$ by $\{f,g\}_F$. → `milnorSymbol` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:144`)
- definition of the paper: Since $(F^\times)^p=C^\times$, the underlying set of $V_F$ is the point set of the projective space $\PP_C(F)$: the class $[f]$ represents the one-dimensional $C$-subspace $Cf$. → `projPoint` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:173`)
- definition of the paper: its projective lines are the sets of one-dimensional subspaces in two-dimensional $C_F$-subspaces of $F$. → `IsProjLine` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:163`)
- definition of the paper: Put $C_F=F^p$. → `powSubfield` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:155`)
- definition of the paper: Let $\Isom_{\mathrm M}(V_K,V_L)$ be the set of $\Lambda$-linear isomorphisms $\Theta:V_K\to V_L$ satisfying \[ (\Theta\otimes\Theta)(R_K)=R_L. \] → `IsCompatibleIso` (`lean/Papers/OaiReconstructionMilnorTheory/Helpers/Isomorphisms.lean:48`)
- definition of the paper: Put $H=K^p$ and $C=L^p$. → `linesPowerFields` (`lean/Papers/OaiReconstructionMilnorTheory/Helpers/Isomorphisms.lean:98`)
- definition of the paper: A list $s_1,\ldots,s_r\in F$ is \emph{$p$-independent over $C$} if $[C(s_1,\ldots,s_r):C]=p^r$. → `IsPIndependent` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:224`)
- condition of the paper: \label{prop:lines} Let $K/k$ and $L/l$ be finitely generated extensions of algebraically closed fields of characteristic $p$, both of transcendence degree at least two. → `LineRecoveryFields` (`lean/Papers/OaiReconstructionMilnorTheory/Helpers/Lines.lean:26`)

## Proposition 5.1

**Statement.** \label{prop:projective-lift} Let $E$ and $E'$ be finite-dimensional vector spaces over fields $H$ and $C$, respectively, with dimensions at least three. Every bijection $\psi:\PP_H(E)\to\PP_C(E')$ that maps lines onto lines is induced by an additive bijection $S:E\to E'$ satisfying \[ S(av)=\sigma(a)S(v)\qquad(a\in H,\ v\in E) \] for a field isomorphism $\sigma:H\to C$. The map $\sigma$ is unique, and $S$ is unique up to multiplication by an element of $C^\times$.

**Lean.** `Papers.OaiReconstructionMilnorTheory.projective_lift` — `lean/Papers/OaiReconstructionMilnorTheory/Helpers/ProjectiveLift.lean:47`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| Let $E$ and $E'$ be finite-dimensional vector spaces over fields $H$ and $C$, respectively, | `hspaces : ProjectiveLiftSpaces H C E E'` |
| with dimensions at least three. | `hspaces : ProjectiveLiftSpaces H C E E'` |
| Every bijection $\psi:\PP_H(E)\to\PP_C(E')$ that maps lines onto lines is induced by an additive bijection $S:E\to E'$ satisfying | `ψ : Projectivization H E → Projectivization C E'`<br>`hψ : ProjectiveLiftBijection ψ`<br>then `∃ σ : H ≃+* C, ∃ S : E ≃+ E',`<br>then `S v ∈ (ψ (Projectivization.mk H v hv)).submodule`<br>`S' v ∈ (ψ (Projectivization.mk H v hv)).submodule` |
| \[ S(av)=\sigma(a)S(v)\qquad | then `S (a • v) = σ a • S v`<br>`S' (a • v) = σ' a • S' v` |
| (a\in H,\ v\in E) \] | `∀ (a : H) v`<br>`∀ (a : H) v` |
| for a field isomorphism $\sigma:H\to C$. | then `∃ σ : H ≃+* C, ∃ S : E ≃+ E',` |
| The map $\sigma$ is unique, | `σ' : H ≃+* C`<br>then `σ' = σ` |
| and $S$ is unique up to multiplication by an element of $C^\times$. | `S' : E ≃+ E'`<br>then `∃ c : Cˣ,`<br>`∀ v`<br>then `S' v = (c : C) • S v` |

Lean also declares what the paper leaves implicit (the objects and their types): `H C E E' : Type*`, `Field H`, `Field C`, `AddCommGroup E`, `Module H E`, `AddCommGroup E'`, `Module C E'`, `∀ v (hv : v ≠ 0)`, `∀ v (hv : v ≠ 0)`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: \label{prop:projective-lift} Let $E$ and $E'$ be finite-dimensional vector spaces over fields $H$ and $C$, respectively, with dimensions at least three. → `ProjectiveLiftSpaces` (`lean/Papers/OaiReconstructionMilnorTheory/Helpers/ProjectiveLiftBasic.lean:28`)
- condition of the paper: Every bijection $\psi:\PP_H(E)\to\PP_C(E')$ that maps lines onto lines → `ProjectiveLiftBijection` (`lean/Papers/OaiReconstructionMilnorTheory/Helpers/ProjectiveLiftBasic.lean:41`)

## Lemma 5.2

**Statement.** \label{lem:perfect-core} If $F/\kappa$ is a finitely generated extension of an algebraically closed field of characteristic $p$, then \[ \bigcap_{m\ge1} F^{p^m}=\kappa. \]

**Lean.** `Papers.OaiReconstructionMilnorTheory.iInter_pow_eq_base` — `lean/Papers/OaiReconstructionMilnorTheory/Helpers/PerfectCore.lean:218`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| If $F/\kappa$ is a finitely generated extension of an algebraically closed field of characteristic $p$, | `p : ℕ`<br>`κ F : Type*`<br>`hp : PrimeChar p`<br>`hF : PerfectCoreField p κ F` |
| then \[ \bigcap_{m\ge1} F^{p^m}=\kappa. \] | then `(⋂ m : ℕ, ⋂ (_ : 1 ≤ m), Set.range fun x : F => x ^ (p ^ m)) = Set.range (algebraMap κ F)` |

Lean also declares what the paper leaves implicit (the objects and their types): `Field κ`, `Field F`, `Algebra κ F`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: Fix a prime $p$ → `PrimeChar` (`lean/Papers/OaiReconstructionMilnorTheory/Basic.lean:32`)
- condition of the paper: If $F/\kappa$ is a finitely generated extension of an algebraically closed field of characteristic $p$ → `PerfectCoreField` (`lean/Papers/OaiReconstructionMilnorTheory/Helpers/PerfectCore.lean:25`)

## Identifiers

| Result | run id | paper label | source | Lean declaration |
| --- | --- | --- | --- | --- |
| Theorem 1.1 | `thm:main` | `thm:main` | `sections/01-introduction.tex:41-54` | `Papers.OaiReconstructionMilnorTheory.milnor_reconstruction_bijective` |
| Lemma 2.1 | `lem:p-degree` | `lem:p-degree` | `sections/02-symbols.tex:17-19` | `Papers.OaiReconstructionMilnorTheory.finrank_powSubfield_eq_pow_trdeg` |
| Lemma 2.2 | `lem:p-basis` | `lem:p-basis` | `sections/02-symbols.tex:46-64` | `Papers.OaiReconstructionMilnorTheory.pBasis_structure` |
| Lemma 2.3 | `lem:zero-symbol` | `lem:zero-symbol` | `sections/02-symbols.tex:93-99` | `Papers.OaiReconstructionMilnorTheory.mem_adjoin_of_milnorSymbol_eq_zero` |
| Lemma 2.4 | `lem:affine-symbol` | `lem:affine-symbol` | `sections/02-symbols.tex:123-128` | `Papers.OaiReconstructionMilnorTheory.milnorSymbol_affine_eq_zero` |
| Proposition 3.1 | `prop:intersection` | `prop:intersection` | `sections/03-intersection.tex:17-37` | `Papers.OaiReconstructionMilnorTheory.intersection_unique_power` |
| Lemma 4.1 | `lem:scalar-line` | `lem:scalar-line` | `sections/04-lines.tex:14-18` | `Papers.OaiReconstructionMilnorTheory.scalar_eq_one_of_preserves_lines` |
| Proposition 4.2 | `prop:lines` | `prop:lines` | `sections/04-lines.tex:32-38` | `Papers.OaiReconstructionMilnorTheory.exists_unique_line_correction` |
| Proposition 5.1 | `prop:projective-lift` | `prop:projective-lift` | `sections/05-fields.tex:13-23` | `Papers.OaiReconstructionMilnorTheory.projective_lift` |
| Lemma 5.2 | `lem:perfect-core` | `lem:perfect-core` | `sections/05-fields.tex:91-97` | `Papers.OaiReconstructionMilnorTheory.iInter_pow_eq_base` |
