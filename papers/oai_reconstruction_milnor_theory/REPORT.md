# Correctness report — oai_reconstruction_milnor_theory

**Verdict: NO ERROR FOUND**

**Paper: MINOR ISSUES — no main result is shown false or weakened**

Minor:

- Theorem 1.1: condition added (bookkeeping or a pinned reading)
- Lemma 2.3: condition added (bookkeeping or a pinned reading)
- Lemma 2.4: condition added (bookkeeping or a pinned reading)
- Proposition 3.1: condition added (bookkeeping or a pinned reading)
- Proposition 4.2: condition added (bookkeeping or a pinned reading)
- `ass:affine-symbol-inputs`: ambiguous; a reading was pinned
- `ass:intersection-elements`: ambiguous; a reading was pinned
- `def:pair-derivations`: ambiguous; a reading was pinned
- `F`: notation ambiguous; a reading was pinned
- `C`: notation ambiguous; a reading was pinned
- `d`: notation ambiguous; a reading was pinned
- `K`: notation ambiguous; a reading was pinned
- `k`: notation ambiguous; a reading was pinned
- `l`: notation ambiguous; a reading was pinned
- `V_F`: notation ambiguous; a reading was pinned
- `g`: notation ambiguous; a reading was pinned
- `[f]`: notation ambiguous; a reading was pinned
- `f`: notation ambiguous; a reading was pinned
- `V_K`: notation ambiguous; a reading was pinned
- `V_L`: notation ambiguous; a reading was pinned
- `\alpha`: notation ambiguous; a reading was pinned
- `r`: notation ambiguous; a reading was pinned
- `s`: notation ambiguous; a reading was pinned
- `t`: notation ambiguous; a reading was pinned
- `s_j`: notation ambiguous; a reading was pinned
- `e`: notation ambiguous; a reading was pinned
- `D_j`: notation ambiguous; a reading was pinned
- `D_s`: notation ambiguous; a reading was pinned
- `D_t`: notation ambiguous; a reading was pinned
- `c`: notation ambiguous; a reading was pinned
- `X`: notation ambiguous; a reading was pinned
- `Y`: notation ambiguous; a reading was pinned
- `U`: notation ambiguous; a reading was pinned
- `V`: notation ambiguous; a reading was pinned
- `n`: notation ambiguous; a reading was pinned
- `\Psi`: notation ambiguous; a reading was pinned
- `H`: notation ambiguous; a reading was pinned
- `E`: notation ambiguous; a reading was pinned
- `E'`: notation ambiguous; a reading was pinned
- `\psi`: notation ambiguous; a reading was pinned
- `S`: notation ambiguous; a reading was pinned

10 result(s) of the paper were examined. None was found wrong as printed. In Lean: 10 proved, 0 taken from the literature as cited, 0 not certified, 0 not formalized.

## What was wrong and what was done

No error was found in the results examined.

## Clarifications (not errors)

Nothing in this section is an error of the paper. Each item is something the paper determines but does not say, made explicit so that the statements can be read, and formalized, in one way.

**How a statement is read.**

- **Theorem 1.1.** In Lemma~\ref{lem:affine-symbol}, $d\in C^\times$ is a locally quantified affine coefficient independent of the previously defined integer $\trdeg(F/\kappa)$.
- **Theorem 1.1.** $\Fp[X]=\Span_{\Fp}\{[X]\}$ and $\Fp[Y]=\Span_{\Fp}\{[Y]\}$ as subspaces of $V_F$.
- **Theorem 1.1.** $D_s,D_t$ are the coordinate Euler derivations associated with $s,t$ in one fixed, arbitrarily chosen $p$-basis of $F/C$ extending the pair $s,t$.

**Notation.**

- $F$: $F$ denotes the characteristic-$p$ field to which the local field-theoretic definitions or arguments are applied. In Lemma~\ref{lem:p-degree}, Lemma~\ref{lem:zero-symbol}, Lemma~\ref{lem:affine-symbol}, Lemma~\ref{lem:perfect-core}: $F/\kappa$ is finitely generated over an algebraically closed field $\kappa$ of characteristic $p$; no positive lower bound on $\trdeg(F/\kappa)$ is imposed. In Lemma~\ref{lem:p-basis}: $F$ is any field of characteristic $p$; finiteness of $[F:F^p]$ is assumed only for the assertions explicitly conditional on finite degree. In Proposition~\ref{prop:intersection}: $[F:F^p]<\infty$. In Lemma~\ref{lem:scalar-line}: $F\ne F^p$; finite power degree and an algebraically closed base are not assumed.
- $C$: $C$ is the scalar field specified in the local field or vector-space setting. In Lemma~\ref{lem:p-degree}, Lemma~\ref{lem:p-basis}, Lemma~\ref{lem:zero-symbol}, Lemma~\ref{lem:affine-symbol}, Proposition~\ref{prop:intersection}, Lemma~\ref{lem:scalar-line}: $C=F^p$. In Theorem~\ref{thm:main}, Proposition~\ref{prop:lines}: $C=L^p$, the power subfield of the target field $L$. In Proposition~\ref{prop:projective-lift}: $C$ is an arbitrary field over which $E'$ is a finite-dimensional vector space of dimension at least three; no power-subfield interpretation is imposed.
- $d$: The letter $d$ is locally bound, denoting either $\trdeg(F/\kappa)$ or a nonzero affine coefficient in the power subfield. In Lemma~\ref{lem:p-degree}: $d=\trdeg(F/\kappa)\in\mathbb Z_{\ge0}$. In Lemma~\ref{lem:affine-symbol}: $d\in C^\times$ is the affine coefficient in $c+dt$, where $C=F^p$. In Proposition~\ref{prop:lines}: In the affine configuration in the proof, $d\in H^\times$ is the coefficient in $y=c+dx$, where $H=K^p$.
- $K$: $K/k$ is a finitely generated extension of an algebraically closed field $k$ of characteristic $p$, with $\trdeg(K/k)\ge2$.
- $k$: $k$ denotes the specified source subfield $k\subset K$ in the base-field notation and a basis index in the notation $s_k$. In Theorem~\ref{thm:main}, Proposition~\ref{prop:lines}: $k$ is algebraically closed of characteristic $p$, and $K/k$ is finitely generated with $\trdeg(K/k)\ge2$. In Lemma~\ref{lem:p-basis}: $k$ in $s_k$ is an integer basis index with $1\le k\le e$; the intersection assertion is for $j\ne k$.
- $l$: $l\subset L$ is the specified target subfield in $\Isom(K,k;L,l)$. In Theorem~\ref{thm:main}, Proposition~\ref{prop:lines}: $l$ is algebraically closed of characteristic $p$, and $L/l$ is finitely generated with $\trdeg(L/l)\ge2$.
- $V_F$: $V_F=F^\times/(F^\times)^p$ has additive operations $[f]+[g]=[fg]$ and $r[f]=[f^r]$, with zero $[1]$, while its underlying set is $\PP_{F^p}(F)$ via $[f]\mapsto F^pf$, whose projective lines come from two-dimensional $F^p$-subspaces of $F$.
- $g$: $g$ is a local nonzero field element; in the class and Milnor-symbol notation it ranges independently over $F^\times$. In Lemma~\ref{lem:perfect-core}: For a given integer $m\ge1$, $g\in F$ is a hypothetical element satisfying $f=g^{p^m}$; it is nonzero because $f\notin\kappa$, and its choice may depend on $m$.
- $[f]$: For $f\in F^\times$, $[f]$ is its class modulo $(F^\times)^p$ and, under the identification of the underlying set of $V_F$ with $\PP_{F^p}(F)$, represents the one-dimensional $F^p$-subspace $F^p f$; $[1]$ is the zero of the additive group $V_F$.
- $f$: $f$ is a local nonzero element of the field whose multiplicative class is being used. In Lemma~\ref{lem:zero-symbol}: In the logarithmic-derivative pairing, $f$ ranges over $F^\times$; when checking a Steinberg pair $([f],[1-f])$, it ranges over $F\setminus\{0,1\}$. In Theorem~\ref{thm:main}: In the induced-map formula and the comparison of semilinear maps $w\mapsto S(fw)$ and $w\mapsto S(f)S(w)$, $f\in K^\times$. In Lemma~\ref{lem:perfect-core}: In the proof, $f\in F\setminus\kappa$ is chosen, hence is nonzero and transcendental over $\kappa$, and is completed to a transcendence basis.
- $V_K$: $V_K=K^\times/(K^\times)^p$ has its additive $\Lambda$-vector-space structure $[f]+[g]=[fg]$, and its underlying set is $\PP_{K^p}(K)$ via $[f]\mapsto K^pf$, so its projective lines are the point sets of two-dimensional $K^p$-subspaces of $K$.
- $V_L$: $V_L=L^\times/(L^\times)^p$ has its additive $\Lambda$-vector-space structure $[f]+[g]=[fg]$, and its underlying set is $\PP_{L^p}(L)$ via $[f]\mapsto L^pf$, so its projective lines are the point sets of two-dimensional $L^p$-subspaces of $L$.
- $\alpha$: $\alpha:K\to L$ is a field isomorphism. In Theorem~\ref{thm:main}: As an argument of the canonical map, $\alpha\in\Isom(K,k;L,l)$, so $\alpha(k)=l$.
- $r$: The letter $r$ is local notation; in the convention $r[f]=[f^r]$ it is an integer, whose action on $V_F$ depends only on its residue in $\Fp$. In Lemma~\ref{lem:p-basis}: In the definition of a $p$-independent list $s_1,\ldots,s_r$, $r$ is the finite length of the list and $[C(s_1,\ldots,s_r):C]=p^r$. In Proposition~\ref{prop:intersection}: In the uniqueness argument, $r$ is a candidate integer exponent with $1\le r<p$, satisfying $U^r=h+jX^r$ with $h,j\in C$; the analogous argument applies to $V$. In Lemma~\ref{lem:scalar-line}: $r\in\Fp^\times$ is the scalar multiplying $V_F$; its powers in the proof use its unique integer representative $1\le r<p$. In Proposition~\ref{prop:lines}: In the inverse-map argument, $r\in\Fp^\times$ is chosen so that $r\Psi^{-1}$ maps projective lines into projective lines. In Theorem~\ref{thm:main}: In the injectivity argument, $r\in\Fp^\times$ is the scalar in $\beta_*=r\alpha_*$.
- $s$: $s$ denotes a local field element, with its field and restrictions specified by the adjunction, pair, or projective point in which it occurs. In Lemma~\ref{lem:p-basis}: $s\in F\setminus M$, where $C\subseteq M\subseteq F$, is the element in the simple adjunction $M(s)/M$. In Lemma~\ref{lem:zero-symbol}: $s\in F^\times$, and the implication has antecedent $s\notin C$. In the contrapositive proof, $t\notin C(s)$, so $s,t$ is a $p$-independent pair used to choose $D_s,D_t$. In Proposition~\ref{prop:lines}: $s\in K^\times$ represents a source projective point; multiplication by $s^{-1}$ takes the line joining $[s],[t]$ to a line through $[1]$.
- $t$: $t$ denotes an element of the field specified by its local pair, affine expression, or coordinate chart. In Lemma~\ref{lem:zero-symbol}: $t\in F^\times$. In the contrapositive proof, $s\notin C$ and $t\notin C(s)$, so the pair $s,t$ is $p$-independent and is extended to the basis defining $D_s,D_t$. In Lemma~\ref{lem:affine-symbol}: $t\in F^\times$ and $c+dt\ne0$, where $c,d\in C^\times$; no $p$-independence premise is imposed. In Proposition~\ref{prop:lines}: In the line joining $[s],[t]$, $t\in K^\times$ is a representative of a source projective point, and multiplication by $s^{-1}$ translates this line to one through $[1]$. In Proposition~\ref{prop:projective-lift}: $t\in H$ is an arbitrary affine coordinate in the lines $(t,t+a)$ and $(t,at)$; it may be zero.
- $s_j$: $s_j$ denotes the $j$th entry of a finite list $s_1,\ldots,s_r\in F$, with $1\leq j\leq r$; the list is $p$-independent over $C$ when $[C(s_1,\ldots,s_r):C]=p^r$, and is a $p$-basis when it is also generating over $C$. In Lemma~\ref{lem:p-basis}: In the finite-degree clause, $s_1,\ldots,s_e$ is an extending $p$-basis of $F/C$, $[F:C]=p^e$, and $1\leq j\leq e$; the monomial exponents satisfy $0\leq i_j<p$.
- $e$: $e$ is a nonnegative integer used as a finite $p$-basis length, except for its explicitly local use as a hypothetical minimal-polynomial degree. In Lemma~\ref{lem:p-basis}: In the statement and the terminating-adjunction argument, $e$ is the length of the extending $p$-basis and satisfies $[F:C]=p^e$. In the preceding minimal-polynomial contradiction only, $e$ is the hypothetical degree $1\leq e<p$, so the polynomial would be $(T-s)^e$; this local $e$ is not the basis length.
- $D_j$: For a chosen finite $p$-basis $s_1,\ldots,s_e$ of $F/C$ and $1\leq j\leq e$, $D_j$ is defined by $D_j(s_1^{i_1}\cdots s_e^{i_e})=i_j s_1^{i_1}\cdots s_e^{i_e}$ for $0\leq i_k<p$, interpreting $i_j$ in $\Fp\subseteq C$, and extending $C$-linearly to $F$.
- $D_s$: For a $p$-independent pair $s,t$, choose any extending $p$-basis; $D_s$ is its $C$-linear Euler derivation with $D_s s=s$ and value zero on every other element of that chosen $p$-basis.
- $D_t$: For a $p$-independent pair $s,t$, choose any extending $p$-basis; $D_t$ is its $C$-linear Euler derivation with $D_t t=t$ and value zero on every other element of that chosen $p$-basis.
- $c$: $c$ is a local scalar coefficient whose field and nonvanishing restrictions are specified by the expression in which it occurs. In Lemma~\ref{lem:p-basis}: $c\in C^\times$ is the coefficient of a nonzero eigenvector $c s_j^i$, where $0\leq i<p$. In Lemma~\ref{lem:affine-symbol}: $c\in C^\times$ is the constant coefficient in $c+dt$, with $t,c+dt\in F^\times$. In Proposition~\ref{prop:lines}: $c\in H$ is the constant coefficient in the hypothetical dependence $y=c+dx$, with $d\in H^\times$; the proof considers $c=0$ and $c\ne0$ separately. In Proposition~\ref{prop:projective-lift}: $c\in C^\times$ is the common value of the coefficients $c_v$ in $T(v)=c_vS(v)$ for nonzero $v\in E$, so that $T=cS$.
- $X$: $X$ is a nonzero element of the locally specified ambient field, used through its projective class $[X]$. In Proposition~\ref{prop:intersection}: $X\in F^\times$ and $[C(X,Y):C]=p^2$. In Proposition~\ref{prop:lines}: $X\in L^\times$ represents $\Theta([x])$ for a nonzero vertex $[x]\in V_K$, with $C=L^p$. For an edge $[x],[y]$, $C(X)\ne C(Y)$ and $X,Y$ are $p$-independent over $C$. The representative is determined only up to $C^\times$.
- $Y$: $Y$ is a nonzero element of the locally specified ambient field, used through its projective class $[Y]$. In Proposition~\ref{prop:intersection}: $Y\in F^\times$ and $[C(X,Y):C]=p^2$. In Proposition~\ref{prop:lines}: $Y\in L^\times$ represents $\Theta([y])$ for a nonzero vertex $[y]\in V_K$, with $C=L^p$. For an edge $[x],[y]$, $C(X)\ne C(Y)$ and $X,Y$ are $p$-independent over $C$. The representative is determined only up to $C^\times$.
- $U$: $U\in C(X)^\times$ satisfies $[U]\notin\Fp[X]$, equivalently $U\notin C^\times X^i$ for every integer $0\le i<p$. In Proposition~\ref{prop:lines}: With $H=K^p$ and $C=L^p$, $U$ is a representative in $L^\times$ of $\Theta([x+a])$, where $a\in H^\times$ and $[x],[y]$ is the chosen edge. It is determined only up to multiplication by $C^\times$.
- $V$: $V\in C(Y)^\times$ satisfies $[V]\notin\Fp[Y]$, equivalently $V\notin C^\times Y^i$ for every integer $0\le i<p$. In Proposition~\ref{prop:lines}: With $H=K^p$ and $C=L^p$, $V$ is a representative in $L^\times$ of $\Theta([y+b])$, where $b\in H^\times$ and $[x],[y]$ is the chosen edge. It is determined only up to multiplication by $C^\times$.
- $n$: $n$ denotes a nonzero power correction modulo $p$, represented by its unique integer in $\{1,\ldots,p-1\}$ when used as an exponent. In Proposition~\ref{prop:intersection}: $n$ is the unique integer $1\le n<p$ such that $U^n\in C+CX^n$ and $V^n\in C+CY^n$; either inclusion determines it uniquely, and both coefficients in each inclusion are nonzero. In Proposition~\ref{prop:lines}, Theorem~\ref{thm:main}: $n\in\Fp^\times$ is the unique scalar such that $\Psi=n\Theta$ sends every projective line over $K^p$ onto a projective line over $L^p$. In the local power calculations its integer representative is used; the scalar is common to all vertices and all affine coefficients.
- $\Psi$: $\Psi=n\Theta$, where $n\in\Fp^\times$ is the unique scalar for which this map sends every projective line over $K^p$ onto a projective line over $L^p$.
- $H$: $H$ denotes the source scalar field in the projective geometry under consideration. In Theorem~\ref{thm:main}, Proposition~\ref{prop:lines}: $H=K^p$. In Proposition~\ref{prop:projective-lift}: $H$ is an arbitrary field over which $E$ is a finite-dimensional vector space of dimension at least three.
- $E$: $E$ is local notation for a vector space or a field, as specified in its statement or proof. In Proposition~\ref{prop:projective-lift}: $E$ is a finite-dimensional vector space over $H$ with $\dim_H E\ge3$. In Lemma~\ref{lem:perfect-core}: For $f\in F\setminus\kappa$, choose a transcendence basis $f,t_2,\ldots,t_d$ over $\kappa$ and put $B=\kappa(t_2,\ldots,t_d)$ and $E=B(f)$; the extension $F/E$ is finite.
- $E'$: $E'$ is a finite-dimensional vector space over $C$ with $\dim_C E'\ge3$.
- $\psi$: $\psi:\PP_H(E)\to\PP_C(E')$ is a bijection that maps projective lines onto projective lines.
- $S$: $S$ is an additive bijection between the source and target vector spaces inducing the specified projective bijection and satisfying $S(av)=\sigma(a)S(v)$ for source scalars $a$ and source vectors $v$. In Proposition~\ref{prop:projective-lift}: $S:E\to E'$ induces $\psi$ and is determined only up to multiplication by an element of $C^\times$. In Theorem~\ref{thm:main}: $S:K\to L$ lifts $\Psi=n\Theta$ over $H=K^p$ and $C=L^p$; it is scaled to satisfy $S(1)=1$ and is then a field isomorphism with $S(k)=l$.

## What was proved in Lean, and what was not

A result is proved in Lean when a Lean declaration reviewed as stating it has a complete proof using no axiom beyond the standard ones. For a corrected result, the corrected statement is the one formalized.

| Result | Formal status | Lean declaration | Axioms |
| --- | --- | --- | --- |
| Theorem 1.1 | proved in Lean, under 3 condition(s) made explicit | `Papers.OaiReconstructionMilnorTheory.milnor_reconstruction_bijective` (`TMain.lean:23`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 2.1 | proved in Lean | `Papers.OaiReconstructionMilnorTheory.finrank_powSubfield_eq_pow_trdeg` (`Helpers/PDegree.lean:117`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 2.2 | proved in Lean | `Papers.OaiReconstructionMilnorTheory.pBasis_structure` (`Helpers/PBasis.lean:522`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 2.3 | proved in Lean, under 1 condition(s) made explicit | `Papers.OaiReconstructionMilnorTheory.mem_adjoin_of_milnorSymbol_eq_zero` (`Helpers/Symbols.lean:119`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 2.4 | proved in Lean, under 1 condition(s) made explicit | `Papers.OaiReconstructionMilnorTheory.milnorSymbol_affine_eq_zero` (`Helpers/Symbols.lean:136`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Proposition 3.1 | proved in Lean, under 1 condition(s) made explicit | `Papers.OaiReconstructionMilnorTheory.intersection_unique_power` (`Helpers/Intersection.lean:28`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 4.1 | proved in Lean | `Papers.OaiReconstructionMilnorTheory.scalar_eq_one_of_preserves_lines` (`Helpers/ScalarLine.lean:186`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Proposition 4.2 | proved in Lean, under 3 condition(s) made explicit | `Papers.OaiReconstructionMilnorTheory.exists_unique_line_correction` (`Helpers/Lines.lean:36`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Proposition 5.1 | proved in Lean | `Papers.OaiReconstructionMilnorTheory.projective_lift` (`Helpers/ProjectiveLift.lean:47`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 5.2 | proved in Lean | `Papers.OaiReconstructionMilnorTheory.iInter_pow_eq_base` (`Helpers/PerfectCore.lean:218`) | the standard ones only (propext, Classical.choice, Quot.sound) |

The Lean development builds; it contains no `sorry`, `admit` or added axiom.

## The corrected paper

`bundle/corrected_paper/` holds the paper as it reads after the corrections, as plain source in the author's own class and layout, compiled to `bundle/corrected_paper/main.pdf` (14 pages). `bundle/MATCH.md` sets each result beside its Lean declaration; `bundle/lean/` holds the Lean code.

The mechanical checks leave nothing open.

# Technical appendix

The records behind the report above, by the run's own identifiers.

- paper: `main.tex` (source sha256 `428b2f20a164b8a9b530414e116609e5d81a932bd6652df17c0ff6f67a891065`)
- stage completed: `5`
- results in scope: 10

| bucket | count |
| --- | --- |
| verified | 5 |
| verified_with_bookkeeping | 5 |
| conditional | 0 |
| repaired | 0 |
| unresolved | 0 |
| not_checked | 0 |
| not_determined | 0 |
| refuted | 0 |

> This is a conditional report. A `verified` result is verified only up to the cited results it assumes, the substrate gates left assumed, and the conditions added during formalization — all listed in full below. `unresolved` means the formalization did not close; it is NOT a claim that the result is wrong. A `refuted` row is a result shown false by a positive witness with no confirmed repair; a `repaired` row was false as printed, and an independent referee confirmed its minimal repair. A `not_determined` row could not be checked as printed: the paper does not say enough to determine the claim, and no reading or repair was adopted; it is NOT a claim that the result is wrong.

## Results

### 1. `thm:main`

| field | value |
| --- | --- |
| bucket | `verified_with_bookkeeping` |
| source | `sections/01-introduction.tex:41-54` (`theorem`, label `thm:main`) |
| statement | \label{thm:main} Let $K/k$ and $L/l$ be finitely generated extensions of algebraically closed fields of characteristic $p$, with \[ \trdeg(K/k)\ge2,\qquad \trdeg(L/l)\ge2. \] The canonical map \[ \Isom(K,k;L,l)\longrightarrow \Isom_{\mathrm M}(V_K,V_L)/\Lambda^\times, \qquad \alpha\longmapsto[\alpha_*], \] is bijective. |
| appended hypothesis list | ass:main-fields, ass:main-dimension |
| Lean | `TMain.lean:23` — `Papers.OaiReconstructionMilnorTheory.milnor_reconstruction_bijective` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | `ass:pin-1`, `ass:pin-2`, `ass:pin-3` |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 2. `lem:p-degree`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `sections/02-symbols.tex:17-19` (`lemma`, label `lem:p-degree`) |
| statement | \label{lem:p-degree} With the notation above, $[F:C]=p^d$. |
| Lean | `Helpers/PDegree.lean:117` — `Papers.OaiReconstructionMilnorTheory.finrank_powSubfield_eq_pow_trdeg` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 3. `lem:p-basis`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `sections/02-symbols.tex:46-64` (`lemma`, label `lem:p-basis`) |
| statement | \label{lem:p-basis} Let $F$ be any field of characteristic $p$, and put $C=F^p$. If $C\subseteq M\subseteq F$ and $s\in F\setminus M$, then $[M(s):M]=p$. If $[F:C]$ is finite, every $p$-independent list extends to a $p$-basis $s_1,\ldots,s_e$ of $F/C$, with $[F:C]=p^e$ and monomial basis \[ \{s_1^{i_1}\cdots s_e^{i_e}:0\leq i_j<p\}. \] For such a basis there are commuting $C$-linear derivations $D_1,\ldots,D_e$ on $F$ satisfying \[ D_j(s_1^{i_1}\cdots s_e^{i_e}) =i_j s_1^{i_1}\cdots s_e^{i_e}. \] On $C(s_j)$ the kernel of $D_j$ is $C$, and its nonzero eigenvectors with eigenvalue in $C$ are precisely the elements $c s_j^i$, where $c\in C^\times$ and $0\leq i<p$; their eigenvalues are $i\in\Fp$. Moreover, $C(s_j)\cap C(s_k)=C$ when $j\ne k$. |
| appended hypothesis list | ass:p-basis-field, ass:p-basis-adjunction, ass:p-basis-finite-degree |
| Lean | `Helpers/PBasis.lean:522` — `Papers.OaiReconstructionMilnorTheory.pBasis_structure` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 4. `lem:zero-symbol`

| field | value |
| --- | --- |
| bucket | `verified_with_bookkeeping` |
| source | `sections/02-symbols.tex:93-99` (`lemma`, label `lem:zero-symbol`) |
| statement | \label{lem:zero-symbol} For $s,t\in F^\times$, one has \[ s\notin C,\qquad \{s,t\}_F=0 \quad\Longrightarrow\quad t\in C(s). \] |
| appended hypothesis list | ass:zero-symbol-inputs, ass:zero-symbol-antecedent |
| Lean | `Helpers/Symbols.lean:119` — `Papers.OaiReconstructionMilnorTheory.mem_adjoin_of_milnorSymbol_eq_zero` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | `ass:pin-3` |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 5. `lem:affine-symbol`

| field | value |
| --- | --- |
| bucket | `verified_with_bookkeeping` |
| source | `sections/02-symbols.tex:123-128` (`lemma`, label `lem:affine-symbol`) |
| statement | \label{lem:affine-symbol} If $c,d\in C^\times$ and $t,c+dt\in F^\times$, then \[ \{t,c+dt\}_F=0. \] |
| appended hypothesis list | ass:affine-symbol-inputs |
| Lean | `Helpers/Symbols.lean:136` — `Papers.OaiReconstructionMilnorTheory.milnorSymbol_affine_eq_zero` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | `ass:pin-1` |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 6. Intersection and exponent `prop:intersection`

| field | value |
| --- | --- |
| bucket | `verified_with_bookkeeping` |
| source | `sections/03-intersection.tex:17-37` (`proposition`, label `prop:intersection`) |
| statement | \label{prop:intersection} Let $F$ be a field of characteristic $p$ with $[F:F^p]<\infty$, and put $C=F^p$. Let $X,Y\in F^\times$ be $p$-independent. Suppose \[ U\in C(X)^\times,\qquad V\in C(Y)^\times, \qquad [U]\notin\Fp[X],\qquad [V]\notin\Fp[Y]. \] If \begin{equation} \label{eq:intersection-witness} X\,C(Y/X)^\times\ \cap\ U\,C(V/U)^\times\ne\varnothing, \end{equation} then there is a unique integer $n$, $1\le n<p$, such that \begin{equation} \label{eq:intersection-conclusion} U^n\in C+CX^n,\qquad V^n\in C+CY^n. \end{equation} In fact, either inclusion in \eqref{eq:intersection-conclusion} determines $n$ uniquely. In each inclusion, both coefficients are nonzero. |
| appended hypothesis list | ass:intersection-field, ass:intersection-finite-degree, ass:intersection-pair-inputs, ass:intersection-elements, ass:intersection-witness |
| Lean | `Helpers/Intersection.lean:28` — `Papers.OaiReconstructionMilnorTheory.intersection_unique_power` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | `ass:pin-2` |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 7. `lem:scalar-line`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `sections/04-lines.tex:14-18` (`lemma`, label `lem:scalar-line`) |
| statement | \label{lem:scalar-line} Let $F$ have characteristic $p$, with $F\ne F^p$. If multiplication by $r\in\Fp^\times$ on $V_F$ maps every projective line over $F^p$ into a projective line, then $r=1$. |
| appended hypothesis list | ass:scalar-line-field, ass:scalar-line-imperfect, ass:scalar-line-preservation |
| Lean | `Helpers/ScalarLine.lean:186` — `Papers.OaiReconstructionMilnorTheory.scalar_eq_one_of_preserves_lines` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 8. `prop:lines`

| field | value |
| --- | --- |
| bucket | `verified_with_bookkeeping` |
| source | `sections/04-lines.tex:32-38` (`proposition`, label `prop:lines`) |
| statement | \label{prop:lines} Let $K/k$ and $L/l$ be finitely generated extensions of algebraically closed fields of characteristic $p$, both of transcendence degree at least two. For every compatible isomorphism $\Theta:V_K\to V_L$, there is a unique $n\in\Fp^\times$ such that $\Psi=n\Theta$ sends every projective line over $K^p$ onto a projective line over $L^p$. |
| appended hypothesis list | ass:line-recovery-fields |
| Lean | `Helpers/Lines.lean:36` — `Papers.OaiReconstructionMilnorTheory.exists_unique_line_correction` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | `ass:pin-1`, `ass:pin-2`, `ass:pin-3` |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 9. Projective lifting `prop:projective-lift`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `sections/05-fields.tex:13-23` (`proposition`, label `prop:projective-lift`) |
| statement | \label{prop:projective-lift} Let $E$ and $E'$ be finite-dimensional vector spaces over fields $H$ and $C$, respectively, with dimensions at least three. Every bijection $\psi:\PP_H(E)\to\PP_C(E')$ that maps lines onto lines is induced by an additive bijection $S:E\to E'$ satisfying \[ S(av)=\sigma(a)S(v)\qquad(a\in H,\ v\in E) \] for a field isomorphism $\sigma:H\to C$. The map $\sigma$ is unique, and $S$ is unique up to multiplication by an element of $C^\times$. |
| appended hypothesis list | ass:projective-lift-spaces, ass:projective-lift-bijection |
| Lean | `Helpers/ProjectiveLift.lean:47` — `Papers.OaiReconstructionMilnorTheory.projective_lift` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 10. `lem:perfect-core`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `sections/05-fields.tex:91-97` (`lemma`, label `lem:perfect-core`) |
| statement | \label{lem:perfect-core} If $F/\kappa$ is a finitely generated extension of an algebraically closed field of characteristic $p$, then \[ \bigcap_{m\ge1} F^{p^m}=\kappa. \] |
| appended hypothesis list | ass:perfect-core-field |
| Lean | `Helpers/PerfectCore.lean:218` — `Papers.OaiReconstructionMilnorTheory.iInter_pow_eq_base` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

## Corrected version

5 of 10 result(s) differ from the version you provided — 0 repaired, 0 with the proof completed (no error), 5 only with a side condition or reading made explicit; the others are as printed. The Lean formalization is of the corrected version.

### `thm:main` (`sections/01-introduction.tex:41-54`)

- as printed: \label{thm:main} Let $K/k$ and $L/l$ be finitely generated extensions of algebraically closed fields of characteristic $p$, with \[ \trdeg(K/k)\ge2,\qquad \trdeg(L/l)\ge2. \] The canonical map \[ \Isom(K,k;L,l)\longrightarrow \Isom_{\mathrm M}(V_K,V_L)/\Lambda^\times, \qquad \alpha\longmapsto[\alpha_*], \] is bijective.
- corrected: statement unchanged
- no error: only a side condition or reading the referee made explicit (see below)
- side condition added by the confirming referee `ass:pin-1`: In Lemma~\ref{lem:affine-symbol}, $d\in C^\times$ is a locally quantified affine coefficient independent of the previously defined integer $\trdeg(F/\kappa)$. — pins reading of ass:affine-symbol-inputs: Lemma~\ref{lem:affine-symbol} quantifies $c,d\in C^\times$, and its proof uses $q=-dt/c$ with $d$ as a coefficient in $C$.
- side condition added by the confirming referee `ass:pin-2`: $\Fp[X]=\Span_{\Fp}\{[X]\}$ and $\Fp[Y]=\Span_{\Fp}\{[Y]\}$ as subspaces of $V_F$. — pins reading of ass:intersection-elements: The introduction defines the additive $\Fp$-vector-space structure on $V_F$ by $r[f]=[f^r]$, and Proposition~\ref{prop:intersection} tests membership of the quotient classes $[U]$ and $[V]$ in these sets.
- side condition added by the confirming referee `ass:pin-3`: $D_s,D_t$ are the coordinate Euler derivations associated with $s,t$ in one fixed, arbitrarily chosen $p$-basis of $F/C$ extending the pair $s,t$. — pins reading of def:pair-derivations: Lemma~\ref{lem:p-basis} defines the coordinate derivations for a chosen basis; the defining sentence then specifies derivations obtained from any extending basis.

### `lem:zero-symbol` (`sections/02-symbols.tex:93-99`)

- as printed: \label{lem:zero-symbol} For $s,t\in F^\times$, one has \[ s\notin C,\qquad \{s,t\}_F=0 \quad\Longrightarrow\quad t\in C(s). \]
- corrected: statement unchanged
- no error: only a side condition or reading the referee made explicit (see below)
- side condition added by the confirming referee `ass:pin-3`: $D_s,D_t$ are the coordinate Euler derivations associated with $s,t$ in one fixed, arbitrarily chosen $p$-basis of $F/C$ extending the pair $s,t$. — pins reading of def:pair-derivations: Lemma~\ref{lem:p-basis} defines the coordinate derivations for a chosen basis; the defining sentence then specifies derivations obtained from any extending basis.

### `lem:affine-symbol` (`sections/02-symbols.tex:123-128`)

- as printed: \label{lem:affine-symbol} If $c,d\in C^\times$ and $t,c+dt\in F^\times$, then \[ \{t,c+dt\}_F=0. \]
- corrected: statement unchanged
- no error: only a side condition or reading the referee made explicit (see below)
- side condition added by the confirming referee `ass:pin-1`: In Lemma~\ref{lem:affine-symbol}, $d\in C^\times$ is a locally quantified affine coefficient independent of the previously defined integer $\trdeg(F/\kappa)$. — pins reading of ass:affine-symbol-inputs: Lemma~\ref{lem:affine-symbol} quantifies $c,d\in C^\times$, and its proof uses $q=-dt/c$ with $d$ as a coefficient in $C$.

### `prop:intersection` (`sections/03-intersection.tex:17-37`)

- as printed: \label{prop:intersection} Let $F$ be a field of characteristic $p$ with $[F:F^p]<\infty$, and put $C=F^p$. Let $X,Y\in F^\times$ be $p$-independent. Suppose \[ U\in C(X)^\times,\qquad V\in C(Y)^\times, \qquad [U]\notin\Fp[X],\qquad [V]\notin\Fp[Y]. \] If \begin{equation} \label{eq:intersection-witness} X\,C(Y/X)^\times\ \cap\ U\,C(V/U)^\times\ne\varnothing, \end{equation} then there is a unique integer $n$, $1\le n<p$, such that \begin{equation} \label{eq:intersection-conclusion} U^n\in C+CX^n,\qquad V^n\in C+CY^n. \end{equation} In fact, either inclusion in \eqref{eq:intersection-conclusion} determines $n$ uniquely. In each inclusion, both coefficients are nonzero.
- corrected: statement unchanged
- no error: only a side condition or reading the referee made explicit (see below)
- side condition added by the confirming referee `ass:pin-2`: $\Fp[X]=\Span_{\Fp}\{[X]\}$ and $\Fp[Y]=\Span_{\Fp}\{[Y]\}$ as subspaces of $V_F$. — pins reading of ass:intersection-elements: The introduction defines the additive $\Fp$-vector-space structure on $V_F$ by $r[f]=[f^r]$, and Proposition~\ref{prop:intersection} tests membership of the quotient classes $[U]$ and $[V]$ in these sets.

### `prop:lines` (`sections/04-lines.tex:32-38`)

- as printed: \label{prop:lines} Let $K/k$ and $L/l$ be finitely generated extensions of algebraically closed fields of characteristic $p$, both of transcendence degree at least two. For every compatible isomorphism $\Theta:V_K\to V_L$, there is a unique $n\in\Fp^\times$ such that $\Psi=n\Theta$ sends every projective line over $K^p$ onto a projective line over $L^p$.
- corrected: statement unchanged
- no error: only a side condition or reading the referee made explicit (see below)
- side condition added by the confirming referee `ass:pin-1`: In Lemma~\ref{lem:affine-symbol}, $d\in C^\times$ is a locally quantified affine coefficient independent of the previously defined integer $\trdeg(F/\kappa)$. — pins reading of ass:affine-symbol-inputs: Lemma~\ref{lem:affine-symbol} quantifies $c,d\in C^\times$, and its proof uses $q=-dt/c$ with $d$ as a coefficient in $C$.
- side condition added by the confirming referee `ass:pin-2`: $\Fp[X]=\Span_{\Fp}\{[X]\}$ and $\Fp[Y]=\Span_{\Fp}\{[Y]\}$ as subspaces of $V_F$. — pins reading of ass:intersection-elements: The introduction defines the additive $\Fp$-vector-space structure on $V_F$ by $r[f]=[f^r]$, and Proposition~\ref{prop:intersection} tests membership of the quotient classes $[U]$ and $[V]$ in these sets.
- side condition added by the confirming referee `ass:pin-3`: $D_s,D_t$ are the coordinate Euler derivations associated with $s,t$ in one fixed, arbitrarily chosen $p$-basis of $F/C$ extending the pair $s,t$. — pins reading of def:pair-derivations: Lemma~\ref{lem:p-basis} defines the coordinate derivations for a chosen basis; the defining sentence then specifies derivations obtained from any extending basis.

## Suggestions to the authors

Not errors: readings the paper determines but does not state, and side conditions the proofs use silently.

- clarification (`ass:pin-1`, used by `thm:main`): In Lemma~\ref{lem:affine-symbol}, $d\in C^\times$ is a locally quantified affine coefficient independent of the previously defined integer $\trdeg(F/\kappa)$. — pins reading of ass:affine-symbol-inputs: Lemma~\ref{lem:affine-symbol} quantifies $c,d\in C^\times$, and its proof uses $q=-dt/c$ with $d$ as a coefficient in $C$.
- clarification (`ass:pin-2`, used by `thm:main`): $\Fp[X]=\Span_{\Fp}\{[X]\}$ and $\Fp[Y]=\Span_{\Fp}\{[Y]\}$ as subspaces of $V_F$. — pins reading of ass:intersection-elements: The introduction defines the additive $\Fp$-vector-space structure on $V_F$ by $r[f]=[f^r]$, and Proposition~\ref{prop:intersection} tests membership of the quotient classes $[U]$ and $[V]$ in these sets.
- clarification (`ass:pin-3`, used by `thm:main`): $D_s,D_t$ are the coordinate Euler derivations associated with $s,t$ in one fixed, arbitrarily chosen $p$-basis of $F/C$ extending the pair $s,t$. — pins reading of def:pair-derivations: Lemma~\ref{lem:p-basis} defines the coordinate derivations for a chosen basis; the defining sentence then specifies derivations obtained from any extending basis.
- `ass:affine-symbol-inputs`: pinned reading: In Lemma~\ref{lem:affine-symbol}, $d\in C^\times$ is a locally quantified affine coefficient independent of the previously defined integer $\trdeg(F/\kappa)$. (Lemma~\ref{lem:affine-symbol} quantifies $c,d\in C^\times$, and its proof uses $q=-dt/c$ with $d$ as a coefficient in $C$.)
- `ass:intersection-elements`: pinned reading: $\Fp[X]=\Span_{\Fp}\{[X]\}$ and $\Fp[Y]=\Span_{\Fp}\{[Y]\}$ as subspaces of $V_F$. (The introduction defines the additive $\Fp$-vector-space structure on $V_F$ by $r[f]=[f^r]$, and Proposition~\ref{prop:intersection} tests membership of the quotient classes $[U]$ and $[V]$ in these sets.)
- `def:pair-derivations`: pinned reading: $D_s,D_t$ are the coordinate Euler derivations associated with $s,t$ in one fixed, arbitrarily chosen $p$-basis of $F/C$ extending the pair $s,t$. (Lemma~\ref{lem:p-basis} defines the coordinate derivations for a chosen basis; the defining sentence then specifies derivations obtained from any extending basis.)
- reading of the symbol `F`: $F$ denotes the characteristic-$p$ field to which the local field-theoretic definitions or arguments are applied. In Lemma~\ref{lem:p-degree}, Lemma~\ref{lem:zero-symbol}, Lemma~\ref{lem:affine-symbol}, Lemma~\ref{lem:perfect-core}: $F/\kappa$ is finitely generated over an algebraically closed field $\kappa$ of characteristic $p$; no positive lower bound on $\trdeg(F/\kappa)$ is imposed. In Lemma~\ref{lem:p-basis}: $F$ is any field of characteristic $p$; finiteness of $[F:F^p]$ is assumed only for the assertions explicitly conditional on finite degree. In Proposition~\ref{prop:intersection}: $[F:F^p]<\infty$. In Lemma~\ref{lem:scalar-line}: $F\ne F^p$; finite power degree and an algebraically closed base are not assumed. — The setup preceding Lemma~\ref{lem:p-degree} specifies $F/\kappa$; Lemma~\ref{lem:p-basis} explicitly allows any characteristic-$p$ field. Proposition~\ref{prop:intersection} assumes finite power degree, and Lemma~\ref{lem:scalar-line} assumes imperfection. Lemma~\ref{lem:perfect-core} uses the geometric field setting.
- reading of the symbol `C`: $C$ is the scalar field specified in the local field or vector-space setting. In Lemma~\ref{lem:p-degree}, Lemma~\ref{lem:p-basis}, Lemma~\ref{lem:zero-symbol}, Lemma~\ref{lem:affine-symbol}, Proposition~\ref{prop:intersection}, Lemma~\ref{lem:scalar-line}: $C=F^p$. In Theorem~\ref{thm:main}, Proposition~\ref{prop:lines}: $C=L^p$, the power subfield of the target field $L$. In Proposition~\ref{prop:projective-lift}: $C$ is an arbitrary field over which $E'$ is a finite-dimensional vector space of dimension at least three; no power-subfield interpretation is imposed. — The section setup and Lemma~\ref{lem:p-basis} put $C=F^p$; Proposition~\ref{prop:intersection} repeats this definition. The proofs of Proposition~\ref{prop:lines} and Theorem~\ref{thm:main} put $C=L^p$. Proposition~\ref{prop:projective-lift} instead introduces $C$ as the scalar field of $E'$.
- reading of the symbol `d`: The letter $d$ is locally bound, denoting either $\trdeg(F/\kappa)$ or a nonzero affine coefficient in the power subfield. In Lemma~\ref{lem:p-degree}: $d=\trdeg(F/\kappa)\in\mathbb Z_{\ge0}$. In Lemma~\ref{lem:affine-symbol}: $d\in C^\times$ is the affine coefficient in $c+dt$, where $C=F^p$. In Proposition~\ref{prop:lines}: In the affine configuration in the proof, $d\in H^\times$ is the coefficient in $y=c+dx$, where $H=K^p$. — The display at lines 201-203 defines the transcendence degree; the hypothesis of Lemma~\ref{lem:affine-symbol} quantifies $c,d\in C^\times$; the proof of Proposition~\ref{prop:lines} writes $y=c+dx$ with $c,d\in H$ and $d\ne0$.
- reading of the symbol `K`: $K/k$ is a finitely generated extension of an algebraically closed field $k$ of characteristic $p$, with $\trdeg(K/k)\ge2$. — The abstract, Theorem~\ref{thm:main}, and Proposition~\ref{prop:lines} explicitly impose these conditions on the source field.
- reading of the symbol `k`: $k$ denotes the specified source subfield $k\subset K$ in the base-field notation and a basis index in the notation $s_k$. In Theorem~\ref{thm:main}, Proposition~\ref{prop:lines}: $k$ is algebraically closed of characteristic $p$, and $K/k$ is finitely generated with $\trdeg(K/k)\ge2$. In Lemma~\ref{lem:p-basis}: $k$ in $s_k$ is an integer basis index with $1\le k\le e$; the intersection assertion is for $j\ne k$. — The introduction defines the specified subfields in $\Isom(K,k;L,l)$. Lemma~\ref{lem:p-basis} introduces $s_1,\ldots,s_e$ and then uses $k$ in $C(s_j)\cap C(s_k)=C$ when $j\ne k$.
- reading of the symbol `l`: $l\subset L$ is the specified target subfield in $\Isom(K,k;L,l)$. In Theorem~\ref{thm:main}, Proposition~\ref{prop:lines}: $l$ is algebraically closed of characteristic $p$, and $L/l$ is finitely generated with $\trdeg(L/l)\ge2$. — The introduction defines the notation for specified subfields without an algebraic-closedness assumption. The hypotheses of Theorem~\ref{thm:main} and Proposition~\ref{prop:lines} then impose the algebraically closed base-field assumptions.
- reading of the symbol `V_F`: $V_F=F^\times/(F^\times)^p$ has additive operations $[f]+[g]=[fg]$ and $r[f]=[f^r]$, with zero $[1]$, while its underlying set is $\PP_{F^p}(F)$ via $[f]\mapsto F^pf$, whose projective lines come from two-dimensional $F^p$-subspaces of $F$. — The introductory definition specifies the additive notation; the passages beginning "Put $C_F=F^p$" and "Since $(F^\times)^p=C^\times$" explicitly distinguish the two structures.
- reading of the symbol `g`: $g$ is a local nonzero field element; in the class and Milnor-symbol notation it ranges independently over $F^\times$. In Lemma~\ref{lem:perfect-core}: For a given integer $m\ge1$, $g\in F$ is a hypothetical element satisfying $f=g^{p^m}$; it is nonzero because $f\notin\kappa$, and its choice may depend on $m$. — The product and Milnor-symbol conventions use $g$ as a second representative, and the logarithmic-derivative pairing explicitly states $f,g\in F^\times$. The perfect-core proof separately supposes $f=g^{p^m}$ with $g\in F$.
- reading of the symbol `[f]`: For $f\in F^\times$, $[f]$ is its class modulo $(F^\times)^p$ and, under the identification of the underlying set of $V_F$ with $\PP_{F^p}(F)$, represents the one-dimensional $F^p$-subspace $F^p f$; $[1]$ is the zero of the additive group $V_F$. — The initial quotient and additive-notation definitions, followed by the paragraph identifying $[f]$ with $Cf$ for $C=F^p$, explicitly give both structures and distinguish their scalar fields.
- reading of the symbol `f`: $f$ is a local nonzero element of the field whose multiplicative class is being used. In Lemma~\ref{lem:zero-symbol}: In the logarithmic-derivative pairing, $f$ ranges over $F^\times$; when checking a Steinberg pair $([f],[1-f])$, it ranges over $F\setminus\{0,1\}$. In Theorem~\ref{thm:main}: In the induced-map formula and the comparison of semilinear maps $w\mapsto S(fw)$ and $w\mapsto S(f)S(w)$, $f\in K^\times$. In Lemma~\ref{lem:perfect-core}: In the proof, $f\in F\setminus\kappa$ is chosen, hence is nonzero and transcendental over $\kappa$, and is completed to a transcendence basis. — The class convention specifies $f\in F^\times$; the Steinberg generators specify $f\in F\setminus\{0,1\}$; the main theorem's proof uses $f\in K^\times$; the perfect-core proof chooses $f\in F\setminus\kappa$.
- reading of the symbol `V_K`: $V_K=K^\times/(K^\times)^p$ has its additive $\Lambda$-vector-space structure $[f]+[g]=[fg]$, and its underlying set is $\PP_{K^p}(K)$ via $[f]\mapsto K^pf$, so its projective lines are the point sets of two-dimensional $K^p$-subspaces of $K$. — The introductory quotient and class notation define the vector-space structure; the projective identification preceding Section~\ref{sec:introduction}'s subsequent sections and the geometric setup identify the underlying point set over the power subfield.
- reading of the symbol `V_L`: $V_L=L^\times/(L^\times)^p$ has its additive $\Lambda$-vector-space structure $[f]+[g]=[fg]$, and its underlying set is $\PP_{L^p}(L)$ via $[f]\mapsto L^pf$, so its projective lines are the point sets of two-dimensional $L^p$-subspaces of $L$. — The introductory quotient and class notation define the vector-space structure; the passages beginning "Put $C_F=F^p$" and "Since $(F^\times)^p=C^\times$" identify the underlying projective point set.
- reading of the symbol `\alpha`: $\alpha:K\to L$ is a field isomorphism. In Theorem~\ref{thm:main}: As an argument of the canonical map, $\alpha\in\Isom(K,k;L,l)$, so $\alpha(k)=l$. — The introduction defines $\Isom(K,k;L,l)$ by the additional condition $\alpha(k)=l$, and the canonical map has that set as its domain.
- reading of the symbol `r`: The letter $r$ is local notation; in the convention $r[f]=[f^r]$ it is an integer, whose action on $V_F$ depends only on its residue in $\Fp$. In Lemma~\ref{lem:p-basis}: In the definition of a $p$-independent list $s_1,\ldots,s_r$, $r$ is the finite length of the list and $[C(s_1,\ldots,s_r):C]=p^r$. In Proposition~\ref{prop:intersection}: In the uniqueness argument, $r$ is a candidate integer exponent with $1\le r<p$, satisfying $U^r=h+jX^r$ with $h,j\in C$; the analogous argument applies to $V$. In Lemma~\ref{lem:scalar-line}: $r\in\Fp^\times$ is the scalar multiplying $V_F$; its powers in the proof use its unique integer representative $1\le r<p$. In Proposition~\ref{prop:lines}: In the inverse-map argument, $r\in\Fp^\times$ is chosen so that $r\Psi^{-1}$ maps projective lines into projective lines. In Theorem~\ref{thm:main}: In the injectivity argument, $r\in\Fp^\times$ is the scalar in $\beta_*=r\alpha_*$. — The class-notation convention specifies $r\in\Z$; the definition of $p$-independence uses a list $s_1,\ldots,s_r$; the intersection uniqueness argument specifies $1\le r<p$; the scalar-line lemma and the line-recovery and injectivity arguments explicitly specify $r\in\Fp^\times$.
- reading of the symbol `s`: $s$ denotes a local field element, with its field and restrictions specified by the adjunction, pair, or projective point in which it occurs. In Lemma~\ref{lem:p-basis}: $s\in F\setminus M$, where $C\subseteq M\subseteq F$, is the element in the simple adjunction $M(s)/M$. In Lemma~\ref{lem:zero-symbol}: $s\in F^\times$, and the implication has antecedent $s\notin C$. In the contrapositive proof, $t\notin C(s)$, so $s,t$ is a $p$-independent pair used to choose $D_s,D_t$. In Proposition~\ref{prop:lines}: $s\in K^\times$ represents a source projective point; multiplication by $s^{-1}$ takes the line joining $[s],[t]$ to a line through $[1]$. — Lemma~\ref{lem:p-basis} assumes $s\in F\setminus M$; Lemma~\ref{lem:zero-symbol} assumes $s,t\in F^\times$; the pair-derivation definition assumes $p$-independence; the line-translation argument uses $[s],[t]$ in the source projective space.
- reading of the symbol `t`: $t$ denotes an element of the field specified by its local pair, affine expression, or coordinate chart. In Lemma~\ref{lem:zero-symbol}: $t\in F^\times$. In the contrapositive proof, $s\notin C$ and $t\notin C(s)$, so the pair $s,t$ is $p$-independent and is extended to the basis defining $D_s,D_t$. In Lemma~\ref{lem:affine-symbol}: $t\in F^\times$ and $c+dt\ne0$, where $c,d\in C^\times$; no $p$-independence premise is imposed. In Proposition~\ref{prop:lines}: In the line joining $[s],[t]$, $t\in K^\times$ is a representative of a source projective point, and multiplication by $s^{-1}$ translates this line to one through $[1]$. In Proposition~\ref{prop:projective-lift}: $t\in H$ is an arbitrary affine coordinate in the lines $(t,t+a)$ and $(t,at)$; it may be zero. — Lemma~\ref{lem:zero-symbol} specifies $s,t\in F^\times$; Lemma~\ref{lem:affine-symbol} specifies $t,c+dt\in F^\times$; the line-translation argument uses representatives $[s],[t]$ in the source projective space; the projective-lifting proof uses affine coordinates over $H$.
- reading of the symbol `s_j`: $s_j$ denotes the $j$th entry of a finite list $s_1,\ldots,s_r\in F$, with $1\leq j\leq r$; the list is $p$-independent over $C$ when $[C(s_1,\ldots,s_r):C]=p^r$, and is a $p$-basis when it is also generating over $C$. In Lemma~\ref{lem:p-basis}: In the finite-degree clause, $s_1,\ldots,s_e$ is an extending $p$-basis of $F/C$, $[F:C]=p^e$, and $1\leq j\leq e$; the monomial exponents satisfy $0\leq i_j<p$. — The paragraph preceding Lemma~\ref{lem:p-basis} defines $p$-independent lists and $p$-bases. Lemma~\ref{lem:p-basis} specifies the extending basis $s_1,\ldots,s_e$ under the finite-degree premise.
- reading of the symbol `e`: $e$ is a nonnegative integer used as a finite $p$-basis length, except for its explicitly local use as a hypothetical minimal-polynomial degree. In Lemma~\ref{lem:p-basis}: In the statement and the terminating-adjunction argument, $e$ is the length of the extending $p$-basis and satisfies $[F:C]=p^e$. In the preceding minimal-polynomial contradiction only, $e$ is the hypothetical degree $1\leq e<p$, so the polynomial would be $(T-s)^e$; this local $e$ is not the basis length. — Lemma~\ref{lem:p-basis} introduces $s_1,\ldots,s_e$ with $[F:C]=p^e$. Its proof temporarily uses $1\leq e<p$ for a hypothetical minimal-polynomial degree, then returns to basis length in the sentence beginning ``If its length is $e$''.
- reading of the symbol `D_j`: For a chosen finite $p$-basis $s_1,\ldots,s_e$ of $F/C$ and $1\leq j\leq e$, $D_j$ is defined by $D_j(s_1^{i_1}\cdots s_e^{i_e})=i_j s_1^{i_1}\cdots s_e^{i_e}$ for $0\leq i_k<p$, interpreting $i_j$ in $\Fp\subseteq C$, and extending $C$-linearly to $F$. — The display in Lemma~\ref{lem:p-basis} specifies the values on the monomial basis; its proof says to define the operators on those monomials and extend $C$-linearly.
- reading of the symbol `D_s`: For a $p$-independent pair $s,t$, choose any extending $p$-basis; $D_s$ is its $C$-linear Euler derivation with $D_s s=s$ and value zero on every other element of that chosen $p$-basis. — The paragraph following Lemma~\ref{lem:p-basis} defines the pair derivations using any extending $p$-basis, and the proof of Lemma~\ref{lem:zero-symbol} explicitly uses $D_s s=s$ and $D_s t=0$.
- reading of the symbol `D_t`: For a $p$-independent pair $s,t$, choose any extending $p$-basis; $D_t$ is its $C$-linear Euler derivation with $D_t t=t$ and value zero on every other element of that chosen $p$-basis. — The paragraph following Lemma~\ref{lem:p-basis} defines the pair derivations using any extending $p$-basis, and the proof of Lemma~\ref{lem:zero-symbol} explicitly uses $D_t t=t$ and $D_t s=0$.
- reading of the symbol `c`: $c$ is a local scalar coefficient whose field and nonvanishing restrictions are specified by the expression in which it occurs. In Lemma~\ref{lem:p-basis}: $c\in C^\times$ is the coefficient of a nonzero eigenvector $c s_j^i$, where $0\leq i<p$. In Lemma~\ref{lem:affine-symbol}: $c\in C^\times$ is the constant coefficient in $c+dt$, with $t,c+dt\in F^\times$. In Proposition~\ref{prop:lines}: $c\in H$ is the constant coefficient in the hypothetical dependence $y=c+dx$, with $d\in H^\times$; the proof considers $c=0$ and $c\ne0$ separately. In Proposition~\ref{prop:projective-lift}: $c\in C^\times$ is the common value of the coefficients $c_v$ in $T(v)=c_vS(v)$ for nonzero $v\in E$, so that $T=cS$. — Lemma~\ref{lem:p-basis} specifies $c\in C^\times$ for eigenvectors; Lemma~\ref{lem:affine-symbol} assumes $c,d\in C^\times$. The proof of Proposition~\ref{prop:lines} allows $c=0$ in a dependence over $H$, and the uniqueness proof of Proposition~\ref{prop:projective-lift} obtains $c$ from the scalars $c_v\in C^\times$.
- reading of the symbol `X`: $X$ is a nonzero element of the locally specified ambient field, used through its projective class $[X]$. In Proposition~\ref{prop:intersection}: $X\in F^\times$ and $[C(X,Y):C]=p^2$. In Proposition~\ref{prop:lines}: $X\in L^\times$ represents $\Theta([x])$ for a nonzero vertex $[x]\in V_K$, with $C=L^p$. For an edge $[x],[y]$, $C(X)\ne C(Y)$ and $X,Y$ are $p$-independent over $C$. The representative is determined only up to $C^\times$. — Proposition~\ref{prop:intersection} takes $X,Y\in F^\times$ to be $p$-independent. The graph in the proof of Proposition~\ref{prop:lines} uses representatives $[X]=\Theta([x])$ in $L$ and imposes independence when an edge is fixed.
- reading of the symbol `Y`: $Y$ is a nonzero element of the locally specified ambient field, used through its projective class $[Y]$. In Proposition~\ref{prop:intersection}: $Y\in F^\times$ and $[C(X,Y):C]=p^2$. In Proposition~\ref{prop:lines}: $Y\in L^\times$ represents $\Theta([y])$ for a nonzero vertex $[y]\in V_K$, with $C=L^p$. For an edge $[x],[y]$, $C(X)\ne C(Y)$ and $X,Y$ are $p$-independent over $C$. The representative is determined only up to $C^\times$. — Proposition~\ref{prop:intersection} takes $X,Y\in F^\times$ to be $p$-independent. The graph in the proof of Proposition~\ref{prop:lines} uses representatives $[Y]=\Theta([y])$ in $L$ and imposes independence when an edge is fixed.
- reading of the symbol `U`: $U\in C(X)^\times$ satisfies $[U]\notin\Fp[X]$, equivalently $U\notin C^\times X^i$ for every integer $0\le i<p$. In Proposition~\ref{prop:lines}: With $H=K^p$ and $C=L^p$, $U$ is a representative in $L^\times$ of $\Theta([x+a])$, where $a\in H^\times$ and $[x],[y]$ is the chosen edge. It is determined only up to multiplication by $C^\times$. — Proposition~\ref{prop:intersection} specifies the subfield and nonmonomiality condition. The proof of Proposition~\ref{prop:lines} sets $u=x+a$, writes $[U]=\Theta([u])$, and establishes the same subfield and nonmonomiality conditions.
- reading of the symbol `V`: $V\in C(Y)^\times$ satisfies $[V]\notin\Fp[Y]$, equivalently $V\notin C^\times Y^i$ for every integer $0\le i<p$. In Proposition~\ref{prop:lines}: With $H=K^p$ and $C=L^p$, $V$ is a representative in $L^\times$ of $\Theta([y+b])$, where $b\in H^\times$ and $[x],[y]$ is the chosen edge. It is determined only up to multiplication by $C^\times$. — Proposition~\ref{prop:intersection} specifies the subfield and nonmonomiality condition. The proof of Proposition~\ref{prop:lines} sets $v=y+b$, writes $[V]=\Theta([v])$, and establishes the same subfield and nonmonomiality conditions.
- reading of the symbol `n`: $n$ denotes a nonzero power correction modulo $p$, represented by its unique integer in $\{1,\ldots,p-1\}$ when used as an exponent. In Proposition~\ref{prop:intersection}: $n$ is the unique integer $1\le n<p$ such that $U^n\in C+CX^n$ and $V^n\in C+CY^n$; either inclusion determines it uniquely, and both coefficients in each inclusion are nonzero. In Proposition~\ref{prop:lines}, Theorem~\ref{thm:main}: $n\in\Fp^\times$ is the unique scalar such that $\Psi=n\Theta$ sends every projective line over $K^p$ onto a projective line over $L^p$. In the local power calculations its integer representative is used; the scalar is common to all vertices and all affine coefficients. — Proposition~\ref{prop:intersection} specifies a unique integer exponent; Proposition~\ref{prop:lines} propagates the local exponents to one scalar and explicitly views it in $\Fp^\times$; Theorem~\ref{thm:main} uses that scalar.
- reading of the symbol `\Psi`: $\Psi=n\Theta$, where $n\in\Fp^\times$ is the unique scalar for which this map sends every projective line over $K^p$ onto a projective line over $L^p$. — Proposition~\ref{prop:lines} specifies the unique scalar and the line property; the proof of Theorem~\ref{thm:main} uses precisely this choice.
- reading of the symbol `H`: $H$ denotes the source scalar field in the projective geometry under consideration. In Theorem~\ref{thm:main}, Proposition~\ref{prop:lines}: $H=K^p$. In Proposition~\ref{prop:projective-lift}: $H$ is an arbitrary field over which $E$ is a finite-dimensional vector space of dimension at least three. — The proof of Proposition~\ref{prop:lines} and the proof of Theorem~\ref{thm:main} put $H=K^p$; Proposition~\ref{prop:projective-lift} instead allows arbitrary scalar fields $H$ and $C$.
- reading of the symbol `E`: $E$ is local notation for a vector space or a field, as specified in its statement or proof. In Proposition~\ref{prop:projective-lift}: $E$ is a finite-dimensional vector space over $H$ with $\dim_H E\ge3$. In Lemma~\ref{lem:perfect-core}: For $f\in F\setminus\kappa$, choose a transcendence basis $f,t_2,\ldots,t_d$ over $\kappa$ and put $B=\kappa(t_2,\ldots,t_d)$ and $E=B(f)$; the extension $F/E$ is finite. — Proposition~\ref{prop:projective-lift} introduces the vector space $E$; the proof of Lemma~\ref{lem:perfect-core} separately puts $E=B(f)$.
- reading of the symbol `E'`: $E'$ is a finite-dimensional vector space over $C$ with $\dim_C E'\ge3$. — The opening sentence of Proposition~\ref{prop:projective-lift} specifies finite dimensionality and the lower dimension bound.
- reading of the symbol `\psi`: $\psi:\PP_H(E)\to\PP_C(E')$ is a bijection that maps projective lines onto projective lines. — Proposition~\ref{prop:projective-lift} explicitly restricts the projective-point bijection to one that maps lines onto lines.
- reading of the symbol `S`: $S$ is an additive bijection between the source and target vector spaces inducing the specified projective bijection and satisfying $S(av)=\sigma(a)S(v)$ for source scalars $a$ and source vectors $v$. In Proposition~\ref{prop:projective-lift}: $S:E\to E'$ induces $\psi$ and is determined only up to multiplication by an element of $C^\times$. In Theorem~\ref{thm:main}: $S:K\to L$ lifts $\Psi=n\Theta$ over $H=K^p$ and $C=L^p$; it is scaled to satisfy $S(1)=1$ and is then a field isomorphism with $S(k)=l$. — Proposition~\ref{prop:projective-lift} specifies the semilinear lift and its uniqueness up to $C^\times$. The proof of Theorem~\ref{thm:main} applies it to $K$ and $L$, scales the lift to satisfy $S(1)=1$, and identifies it as a field isomorphism carrying $k$ onto $l$.

## Added conditions

| id | where | class | condition |
| --- | --- | --- | --- |
| `ass:pin-1` | `thm:main` | V1.5 bookkeeping | In Lemma~\ref{lem:affine-symbol}, $d\in C^\times$ is a locally quantified affine coefficient independent of the previously defined integer $\trdeg(F/\kappa)$. (pins reading of ass:affine-symbol-inputs: Lemma~\ref{lem:affine-symbol} quantifies $c,d\in C^\times$, and its proof uses $q=-dt/c$ with $d$ as a coefficient in $C$.) |
| `ass:pin-2` | `thm:main` | V1.5 bookkeeping | $\Fp[X]=\Span_{\Fp}\{[X]\}$ and $\Fp[Y]=\Span_{\Fp}\{[Y]\}$ as subspaces of $V_F$. (pins reading of ass:intersection-elements: The introduction defines the additive $\Fp$-vector-space structure on $V_F$ by $r[f]=[f^r]$, and Proposition~\ref{prop:intersection} tests membership of the quotient classes $[U]$ and $[V]$ in these sets.) |
| `ass:pin-3` | `thm:main` | V1.5 bookkeeping | $D_s,D_t$ are the coordinate Euler derivations associated with $s,t$ in one fixed, arbitrarily chosen $p$-basis of $F/C$ extending the pair $s,t$. (pins reading of def:pair-derivations: Lemma~\ref{lem:p-basis} defines the coordinate derivations for a chosen basis; the defining sentence then specifies derivations obtained from any extending basis.) |
| `ass:pin-3` | `lem:zero-symbol` | V1.5 bookkeeping | $D_s,D_t$ are the coordinate Euler derivations associated with $s,t$ in one fixed, arbitrarily chosen $p$-basis of $F/C$ extending the pair $s,t$. (pins reading of def:pair-derivations: Lemma~\ref{lem:p-basis} defines the coordinate derivations for a chosen basis; the defining sentence then specifies derivations obtained from any extending basis.) |
| `ass:pin-1` | `lem:affine-symbol` | V1.5 bookkeeping | In Lemma~\ref{lem:affine-symbol}, $d\in C^\times$ is a locally quantified affine coefficient independent of the previously defined integer $\trdeg(F/\kappa)$. (pins reading of ass:affine-symbol-inputs: Lemma~\ref{lem:affine-symbol} quantifies $c,d\in C^\times$, and its proof uses $q=-dt/c$ with $d$ as a coefficient in $C$.) |
| `ass:pin-2` | `prop:intersection` | V1.5 bookkeeping | $\Fp[X]=\Span_{\Fp}\{[X]\}$ and $\Fp[Y]=\Span_{\Fp}\{[Y]\}$ as subspaces of $V_F$. (pins reading of ass:intersection-elements: The introduction defines the additive $\Fp$-vector-space structure on $V_F$ by $r[f]=[f^r]$, and Proposition~\ref{prop:intersection} tests membership of the quotient classes $[U]$ and $[V]$ in these sets.) |
| `ass:pin-1` | `prop:lines` | V1.5 bookkeeping | In Lemma~\ref{lem:affine-symbol}, $d\in C^\times$ is a locally quantified affine coefficient independent of the previously defined integer $\trdeg(F/\kappa)$. (pins reading of ass:affine-symbol-inputs: Lemma~\ref{lem:affine-symbol} quantifies $c,d\in C^\times$, and its proof uses $q=-dt/c$ with $d$ as a coefficient in $C$.) |
| `ass:pin-2` | `prop:lines` | V1.5 bookkeeping | $\Fp[X]=\Span_{\Fp}\{[X]\}$ and $\Fp[Y]=\Span_{\Fp}\{[Y]\}$ as subspaces of $V_F$. (pins reading of ass:intersection-elements: The introduction defines the additive $\Fp$-vector-space structure on $V_F$ by $r[f]=[f^r]$, and Proposition~\ref{prop:intersection} tests membership of the quotient classes $[U]$ and $[V]$ in these sets.) |
| `ass:pin-3` | `prop:lines` | V1.5 bookkeeping | $D_s,D_t$ are the coordinate Euler derivations associated with $s,t$ in one fixed, arbitrarily chosen $p$-basis of $F/C$ extending the pair $s,t$. (pins reading of def:pair-derivations: Lemma~\ref{lem:p-basis} defines the coordinate derivations for a chosen basis; the defining sentence then specifies derivations obtained from any extending basis.) |

## Conditions assumed

### Cited results

None: no result rests on a theorem imported from the literature.

### Deferred substrate gates

None: every substrate this run needed was built and proved.

## Unresolved / notes

- run-level `ass:affine-symbol-inputs`: [note, V1.5] pinned reading: In Lemma~\ref{lem:affine-symbol}, $d\in C^\times$ is a locally quantified affine coefficient independent of the previously defined integer $\trdeg(F/\kappa)$. (Lemma~\ref{lem:affine-symbol} quantifies $c,d\in C^\times$, and its proof uses $q=-dt/c$ with $d$ as a coefficient in $C$.)
- run-level `ass:intersection-elements`: [note, V1.5] pinned reading: $\Fp[X]=\Span_{\Fp}\{[X]\}$ and $\Fp[Y]=\Span_{\Fp}\{[Y]\}$ as subspaces of $V_F$. (The introduction defines the additive $\Fp$-vector-space structure on $V_F$ by $r[f]=[f^r]$, and Proposition~\ref{prop:intersection} tests membership of the quotient classes $[U]$ and $[V]$ in these sets.)
- run-level `def:pair-derivations`: [note, V1.5] pinned reading: $D_s,D_t$ are the coordinate Euler derivations associated with $s,t$ in one fixed, arbitrarily chosen $p$-basis of $F/C$ extending the pair $s,t$. (Lemma~\ref{lem:p-basis} defines the coordinate derivations for a chosen basis; the defining sentence then specifies derivations obtained from any extending basis.)
- run-level `symbol C`: [note, V1.5] symbol table corrected: type "field", space "$\mathrm{Fields}$" (The recorded power-subfield type and subfield space do not cover the arbitrary field $C$ in Proposition~\ref{prop:projective-lift}. Elsewhere the power subfield belongs to the locally specified ambient field, which is $L$ in the reconstruction arguments.)
- run-level `symbol d`: [note, V1.5] symbol table corrected: type "locally bound transcendence degree or affine coefficient", space "$\mathbb Z_{\ge0}$ for the transcendence degree; $C^\times$ or $H^\times$ for the affine coefficient", def "The degree notation is $d=\trdeg(F/\kappa)$. In the local affine expressions $c+dt$ and $c+dx$, $d$ instead denotes the quantified nonzero coefficient in the corresponding power subfield." (The entry assigns only a nonnegative integer meaning. The paper subsequently binds the same letter as a nonzero field coefficient, first over $C$ and later over $H$; these local bindings determine its meaning without ambiguity.)
- run-level `symbol k`: [note, V1.5] symbol table corrected: type "specified source subfield or basis index, according to context", space "$\mathrm{Subfields}(K)$ in the base-field notation; $\{1,\ldots,e\}$ in the basis-index notation", def "The specified subfield $k\subset K$ in the notation $\Isom(K,k;L,l)$; in $s_k$, an index of the basis $s_1,\ldots,s_e$." (The existing base-field qualification remains valid, but its general reading omitted the local use of $k$ as a basis index. That index does not denote a subfield of $K$.)
- run-level `symbol l`: [note, V1.5] symbol table corrected: def "The specified subfield $l\subset L$ in the notation $\Isom(K,k;L,l)$." (The recorded algebraically closed base describes the reconstruction setting but overrestricts the initial definition for arbitrary specified subfields. The later hypotheses specialize the same subfield notation.)
- run-level `symbol \Theta`: [note, V1.5] symbol table corrected: type "compatible linear isomorphism", def "A $\Lambda$-linear isomorphism $\Theta:V_K\to V_L$ satisfying $(\Theta\otimes\Theta)(R_K)=R_L$." (The entry allows an arbitrary linear isomorphism, whereas the paper uses a compatible one, preserving the Steinberg relation subspaces. The later passages do not redefine it.)
- run-level `symbol r`: [note, V1.5] symbol table corrected: type "local integer exponent or list length, or nonzero scalar", space "$\Z$ or $\Fp^\times$, according to context", def "In $r[f]=[f^r]$, $r\in\Z$; in a list $s_1,\ldots,s_r$, $r$ is its length; in scalar multiplication preserving projective lines, $r\in\Fp^\times$." (The recorded integer exponent is correct for the initial convention but does not cover the later nonzero field scalar or the list-length notation. These uses are explicitly distinguished by their local domains.)
- run-level `symbol s`: [note, V1.5] symbol table corrected: space "$F$ or $K$, according to the local use", def "$s$ denotes the element adjoined in $M(s)$, the first member of a pair $s,t$, or a representative of the source projective point $[s]$." (The recorded definition omits the simple-adjunction role and the projective representative in $K$. The restrictions $s\notin M$, $s\notin C$, and independence of the pair belong to their respective local uses.)
- run-level `symbol t`: [note, V1.5] symbol table corrected: space "$F$, $K$, or $H$, according to the local use", def "$t$ is a local field element: a member of the pair $s,t$, the argument in $c+dt$, a representative in a projective line joining $[s],[t]$, or an affine coordinate in $(t,t+a)$ and $(t,at)$." (The recorded pair interpretation is too narrow, and the global space $F$ does not cover the representative in $K$ or the coordinate in the arbitrary field $H$. The pair-derivation use requires independence, whereas the affine-symbol use does not.)
- run-level `symbol e`: [note, V1.5] symbol table corrected: type "basis length or local polynomial degree", def "$e$ is the length of the finite $p$-basis $s_1,\ldots,s_e$, with $[F:C]=p^e$; locally in the minimal-polynomial argument, $e$ instead denotes a hypothetical degree satisfying $1\leq e<p$." (The basis-length interpretation is correct for the statement, but it does not cover the proof's temporary reuse of $e$ as a hypothetical minimal-polynomial degree. The paper explicitly returns to the basis-length meaning afterward.)
- run-level `symbol c`: [note, V1.5] symbol table corrected: type "local scalar coefficient", space "$C$ or $H$, according to the local use", def "$c$ denotes a local scalar coefficient: in an eigenvector $c s_j^i$, in an affine expression $c+dt$ or $c+dx$, or in the comparison $T=cS$ of semilinear lifts." (The recorded entry restricts c to a nonzero eigenvector coefficient. The paper also uses it as an affine coefficient, possibly zero and belonging to H, and as the nonzero scalar relating semilinear lifts.)
- run-level `symbol X`: [note, V1.5] symbol table corrected: space "$F^\times$ in the intersection calculation; $L^\times$ in the line-recovery argument." (The recorded space $F^\times$ covers the intersection proposition but requires local specialization to $L^\times$ in line recovery. Independence is imposed on edge pairs, not on every pair of graph vertices.)
- run-level `symbol Y`: [note, V1.5] symbol table corrected: space "$F^\times$ in the intersection calculation; $L^\times$ in the line-recovery argument." (The recorded space $F^\times$ covers the intersection proposition but requires local specialization to $L^\times$ in line recovery. Independence is imposed on edge pairs, not on every pair of graph vertices.)
- run-level `symbol n`: [note, V1.5] symbol table corrected: type "power-correction exponent or scalar", space "$\{1,\ldots,p-1\}$ when an integer exponent; $\Fp^\times$ when a scalar.", def "The power correction, represented by an integer $1\le n<p$ when used in powers and by its residue in $\Fp^\times$ when used in $\Psi=n\Theta$." (The recorded integer domain and local common-power definition omit the global scalar use. The paper explicitly passes from integer exponents to their nonzero residues when multiplying the linear isomorphism.)
- run-level `symbol H`: [note, V1.5] symbol table corrected: type "field", space "$\mathrm{Fields}$", def "$H$ is the locally specified source scalar field." (The recorded power-subfield type and space exclude the arbitrary field $H$ allowed in projective lifting. The power-subfield identification applies to line recovery and its application in the main theorem.)
- run-level `symbol E`: [note, V1.5] symbol table corrected: type "locally specified vector space or field", def "$E$ denotes a vector space in projective lifting and the field $B(f)$ in the perfect-core proof." (The recorded vector-space type and space cover projective lifting but miss the separate use of $E$ as an intermediate field in the perfect-core proof.)
- note on `ass:affine-symbol-inputs`: pinned reading: In Lemma~\ref{lem:affine-symbol}, $d\in C^\times$ is a locally quantified affine coefficient independent of the previously defined integer $\trdeg(F/\kappa)$. (Lemma~\ref{lem:affine-symbol} quantifies $c,d\in C^\times$, and its proof uses $q=-dt/c$ with $d$ as a coefficient in $C$.)
- note on `ass:intersection-elements`: pinned reading: $\Fp[X]=\Span_{\Fp}\{[X]\}$ and $\Fp[Y]=\Span_{\Fp}\{[Y]\}$ as subspaces of $V_F$. (The introduction defines the additive $\Fp$-vector-space structure on $V_F$ by $r[f]=[f^r]$, and Proposition~\ref{prop:intersection} tests membership of the quotient classes $[U]$ and $[V]$ in these sets.)
- note on `def:pair-derivations`: pinned reading: $D_s,D_t$ are the coordinate Euler derivations associated with $s,t$ in one fixed, arbitrarily chosen $p$-basis of $F/C$ extending the pair $s,t$. (Lemma~\ref{lem:p-basis} defines the coordinate derivations for a chosen basis; the defining sentence then specifies derivations obtained from any extending basis.)
- note on `symbol \Theta`: symbol table corrected: type "compatible linear isomorphism", def "A $\Lambda$-linear isomorphism $\Theta:V_K\to V_L$ satisfying $(\Theta\otimes\Theta)(R_K)=R_L$." (The entry allows an arbitrary linear isomorphism, whereas the paper uses a compatible one, preserving the Steinberg relation subspaces. The later passages do not redefine it.)
- note on `symbol c`: symbol table corrected: type "local scalar coefficient", space "$C$ or $H$, according to the local use", def "$c$ denotes a local scalar coefficient: in an eigenvector $c s_j^i$, in an affine expression $c+dt$ or $c+dx$, or in the comparison $T=cS$ of semilinear lifts." (The recorded entry restricts c to a nonzero eigenvector coefficient. The paper also uses it as an affine coefficient, possibly zero and belonging to H, and as the nonzero scalar relating semilinear lifts.)
- note on `symbol C`: symbol table corrected: type "field", space "$\mathrm{Fields}$" (The recorded power-subfield type and subfield space do not cover the arbitrary field $C$ in Proposition~\ref{prop:projective-lift}. Elsewhere the power subfield belongs to the locally specified ambient field, which is $L$ in the reconstruction arguments.)
- note on `symbol d`: symbol table corrected: type "locally bound transcendence degree or affine coefficient", space "$\mathbb Z_{\ge0}$ for the transcendence degree; $C^\times$ or $H^\times$ for the affine coefficient", def "The degree notation is $d=\trdeg(F/\kappa)$. In the local affine expressions $c+dt$ and $c+dx$, $d$ instead denotes the quantified nonzero coefficient in the corresponding power subfield." (The entry assigns only a nonnegative integer meaning. The paper subsequently binds the same letter as a nonzero field coefficient, first over $C$ and later over $H$; these local bindings determine its meaning without ambiguity.)
- note on `symbol e`: symbol table corrected: type "basis length or local polynomial degree", def "$e$ is the length of the finite $p$-basis $s_1,\ldots,s_e$, with $[F:C]=p^e$; locally in the minimal-polynomial argument, $e$ instead denotes a hypothetical degree satisfying $1\leq e<p$." (The basis-length interpretation is correct for the statement, but it does not cover the proof's temporary reuse of $e$ as a hypothetical minimal-polynomial degree. The paper explicitly returns to the basis-length meaning afterward.)
- note on `symbol E`: symbol table corrected: type "locally specified vector space or field", def "$E$ denotes a vector space in projective lifting and the field $B(f)$ in the perfect-core proof." (The recorded vector-space type and space cover projective lifting but miss the separate use of $E$ as an intermediate field in the perfect-core proof.)
- note on `symbol H`: symbol table corrected: type "field", space "$\mathrm{Fields}$", def "$H$ is the locally specified source scalar field." (The recorded power-subfield type and space exclude the arbitrary field $H$ allowed in projective lifting. The power-subfield identification applies to line recovery and its application in the main theorem.)
- note on `symbol k`: symbol table corrected: type "specified source subfield or basis index, according to context", space "$\mathrm{Subfields}(K)$ in the base-field notation; $\{1,\ldots,e\}$ in the basis-index notation", def "The specified subfield $k\subset K$ in the notation $\Isom(K,k;L,l)$; in $s_k$, an index of the basis $s_1,\ldots,s_e$." (The existing base-field qualification remains valid, but its general reading omitted the local use of $k$ as a basis index. That index does not denote a subfield of $K$.)
- note on `symbol l`: symbol table corrected: def "The specified subfield $l\subset L$ in the notation $\Isom(K,k;L,l)$." (The recorded algebraically closed base describes the reconstruction setting but overrestricts the initial definition for arbitrary specified subfields. The later hypotheses specialize the same subfield notation.)
- note on `symbol n`: symbol table corrected: type "power-correction exponent or scalar", space "$\{1,\ldots,p-1\}$ when an integer exponent; $\Fp^\times$ when a scalar.", def "The power correction, represented by an integer $1\le n<p$ when used in powers and by its residue in $\Fp^\times$ when used in $\Psi=n\Theta$." (The recorded integer domain and local common-power definition omit the global scalar use. The paper explicitly passes from integer exponents to their nonzero residues when multiplying the linear isomorphism.)
- note on `symbol r`: symbol table corrected: type "local integer exponent or list length, or nonzero scalar", space "$\Z$ or $\Fp^\times$, according to context", def "In $r[f]=[f^r]$, $r\in\Z$; in a list $s_1,\ldots,s_r$, $r$ is its length; in scalar multiplication preserving projective lines, $r\in\Fp^\times$." (The recorded integer exponent is correct for the initial convention but does not cover the later nonzero field scalar or the list-length notation. These uses are explicitly distinguished by their local domains.)
- note on `symbol s`: symbol table corrected: space "$F$ or $K$, according to the local use", def "$s$ denotes the element adjoined in $M(s)$, the first member of a pair $s,t$, or a representative of the source projective point $[s]$." (The recorded definition omits the simple-adjunction role and the projective representative in $K$. The restrictions $s\notin M$, $s\notin C$, and independence of the pair belong to their respective local uses.)
- note on `symbol t`: symbol table corrected: space "$F$, $K$, or $H$, according to the local use", def "$t$ is a local field element: a member of the pair $s,t$, the argument in $c+dt$, a representative in a projective line joining $[s],[t]$, or an affine coordinate in $(t,t+a)$ and $(t,at)$." (The recorded pair interpretation is too narrow, and the global space $F$ does not cover the representative in $K$ or the coordinate in the arbitrary field $H$. The pair-derivation use requires independence, whereas the affine-symbol use does not.)
- note on `symbol X`: symbol table corrected: space "$F^\times$ in the intersection calculation; $L^\times$ in the line-recovery argument." (The recorded space $F^\times$ covers the intersection proposition but requires local specialization to $L^\times$ in line recovery. Independence is imposed on edge pairs, not on every pair of graph vertices.)
- note on `symbol Y`: symbol table corrected: space "$F^\times$ in the intersection calculation; $L^\times$ in the line-recovery argument." (The recorded space $F^\times$ covers the intersection proposition but requires local specialization to $L^\times$ in line recovery. Independence is imposed on edge pairs, not on every pair of graph vertices.)

### V1 lint warnings

- thm:main: thm:main references \ref{prop:lines} (prop:lines) but `depends_on` lacks ass:line-recovery-fields; V1.5 must confirm whether the paper assumes it or merely mentions it
- thm:main: thm:main references \ref{prop:projective-lift} (prop:projective-lift) but `depends_on` lacks ass:projective-lift-spaces, ass:projective-lift-bijection; V1.5 must confirm whether the paper assumes it or merely mentions it
- thm:main: thm:main references \ref{lem:perfect-core} (lem:perfect-core) but `depends_on` lacks ass:perfect-core-field; V1.5 must confirm whether the paper assumes it or merely mentions it
- thm:main: thm:main references \ref{lem:scalar-line} (lem:scalar-line) but `depends_on` lacks ass:scalar-line-field, ass:scalar-line-imperfect, ass:scalar-line-preservation; V1.5 must confirm whether the paper assumes it or merely mentions it
- lem:zero-symbol: lem:zero-symbol references \ref{lem:p-basis} (lem:p-basis) but `depends_on` lacks ass:p-basis-field, ass:p-basis-adjunction, ass:p-basis-finite-degree, def:p-basis-power-subfield; V1.5 must confirm whether the paper assumes it or merely mentions it
- prop:intersection: prop:intersection references \ref{lem:p-basis} (lem:p-basis) but `depends_on` lacks ass:p-basis-field, ass:p-basis-adjunction, ass:p-basis-finite-degree, def:p-basis-power-subfield; V1.5 must confirm whether the paper assumes it or merely mentions it
- lem:scalar-line: lem:scalar-line references \ref{lem:p-basis} (lem:p-basis) but `depends_on` lacks ass:p-basis-field, ass:p-basis-adjunction, ass:p-basis-finite-degree; V1.5 must confirm whether the paper assumes it or merely mentions it
- prop:lines: prop:lines references \ref{lem:affine-symbol} (lem:affine-symbol) but `depends_on` lacks ass:affine-symbol-inputs; V1.5 must confirm whether the paper assumes it or merely mentions it
- prop:lines: prop:lines references \ref{lem:zero-symbol} (lem:zero-symbol) but `depends_on` lacks ass:zero-symbol-inputs; V1.5 must confirm whether the paper assumes it or merely mentions it
- prop:lines: prop:lines references \ref{prop:intersection} (prop:intersection) but `depends_on` lacks ass:intersection-field, ass:intersection-finite-degree, ass:intersection-pair-inputs, ass:intersection-elements, ass:intersection-witness, def:intersection-power-subfield; V1.5 must confirm whether the paper assumes it or merely mentions it
- prop:lines: prop:lines references \ref{lem:scalar-line} (lem:scalar-line) but `depends_on` lacks ass:scalar-line-field, ass:scalar-line-imperfect, ass:scalar-line-preservation; V1.5 must confirm whether the paper assumes it or merely mentions it

### Parser warnings

- referee fix applied — lem:zero-symbol: depends_on + lem:p-degree

## Lean evidence

- build of the run barrel: **ok**
- source scan (sorry / admit / axiom): clean

| declaration | axioms |
| --- | --- |
| `Papers.OaiReconstructionMilnorTheory.milnor_reconstruction_bijective` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiReconstructionMilnorTheory.finrank_powSubfield_eq_pow_trdeg` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiReconstructionMilnorTheory.pBasis_structure` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiReconstructionMilnorTheory.mem_adjoin_of_milnorSymbol_eq_zero` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiReconstructionMilnorTheory.milnorSymbol_affine_eq_zero` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiReconstructionMilnorTheory.intersection_unique_power` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiReconstructionMilnorTheory.scalar_eq_one_of_preserves_lines` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiReconstructionMilnorTheory.exists_unique_line_correction` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiReconstructionMilnorTheory.projective_lift` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiReconstructionMilnorTheory.iInter_pow_eq_base` | clean — `propext`, `Classical.choice`, `Quot.sound` |

## Inputs

| artifact | status |
| --- | --- |
| `discovery/v1_scope.json` | present (10 environment(s)) |
| `discovery/v1_5_review.json` | present (verdict PASS) |
| `formalization/crosswalk_full.json` | present (309 object(s)) |
| `graph.json` | present (315 node(s)) |
| Lean evidence | collected (build ok, 0 scan issue(s), 308 declaration(s)) |

## Annotated paper

Annotated paper: `annotated/main.tex` (36 annotation(s), 0 unlocated; index `annotated/ANNOTATIONS.md`); PDF: `annotated/main.pdf`
