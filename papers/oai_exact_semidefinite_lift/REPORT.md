# Correctness report — oai_exact_semidefinite_lift

**Verdict: NO ERROR FOUND**

**Paper: MINOR ISSUES — no main result is shown false or weakened**

Minor:

- Theorem 1.1: condition added (bookkeeping or a pinned reading)
- Lemma 3.1: condition added (bookkeeping or a pinned reading)
- Proposition 4.1: condition added (bookkeeping or a pinned reading)
- `def:moment-matrix`: ambiguous; a reading was pinned
- `def:complex-trigonometric-polynomials`: ambiguous; a reading was pinned
- `S`: notation ambiguous; a reading was pinned
- `Q`: notation ambiguous; a reading was pinned
- `z`: notation ambiguous; a reading was pinned
- `N`: notation ambiguous; a reading was pinned
- `n`: notation ambiguous; a reading was pinned
- `p`: notation ambiguous; a reading was pinned
- `e`: notation ambiguous; a reading was pinned
- `x`: notation ambiguous; a reading was pinned
- `t`: notation ambiguous; a reading was pinned
- `a`: notation ambiguous; a reading was pinned
- `A_\nu`: notation ambiguous; a reading was pinned
- `B_j`: notation ambiguous; a reading was pinned
- `v`: notation ambiguous; a reading was pinned
- `f_1`: notation ambiguous; a reading was pinned
- `f_2`: notation ambiguous; a reading was pinned
- `r_j`: notation ambiguous; a reading was pinned
- `H`: notation ambiguous; a reading was pinned
- `C(\theta)`: notation ambiguous; a reading was pinned
- `q`: notation ambiguous; a reading was pinned
- `M`: notation ambiguous; a reading was pinned
- `b`: notation ambiguous; a reading was pinned
- `H(\Lambda)`: notation ambiguous; a reading was pinned
- `w_0`: notation ambiguous; a reading was pinned
- `m`: notation ambiguous; a reading was pinned
- `b_j`: notation ambiguous; a reading was pinned
- `\widetilde C(\theta)`: notation ambiguous; a reading was pinned

5 result(s) of the paper were examined. None was found wrong as printed. In Lean: 5 proved, 0 taken from the literature as cited, 0 not certified, 0 not formalized.

## What was wrong and what was done

No error was found in the results examined.

## Clarifications (not errors)

Nothing in this section is an error of the paper. Each item is something the paper determines but does not say, made explicit so that the statements can be read, and formalized, in one way.

**How a statement is read.**

- **Theorem 1.1.** In the moment-matrix definition, $(f_1,\ldots,f_5)=(1,\cos\theta,\sin\theta,\cos2\theta,\sin2\theta)$ are real functions and $H(\Lambda)\in\mathbb S^{100}$ is indexed by $(i,a)$ with $1\leq i\leq20$ and $1\leq a\leq5$.
- **Theorem 1.1.** The linear combination is finite, with coefficients in $\mathbb C$ independent of $\theta$ and indices $\ell\in\mathbb Z$ satisfying $-j\leq\ell\leq j$.

**Notation.**

- $S$: $S\in\mathbb S^3$ is the real symmetric weight in $\langle F,H\rangle_S=\operatorname{Re}\operatorname{tr}(F^*SH)$, with no positive semidefiniteness requirement. In Proposition~\ref{prop:lift}: In the matching construction, $S=J_uDJ_u^T$, where $u\in\mathbb R^4$ and $D\in\mathbb S^4$ are arbitrary; neither $D$ nor $S$ must be positive semidefinite.
- $Q$: For $y=(y_1,y_2,y_3)\in\mathbb R^3$, $Q(y)=\begin{pmatrix}y_1^2+y_2^2&-y_1y_2&-y_1y_3\\-y_1y_2&y_2^2+y_3^2&-y_2y_3\\-y_1y_3&-y_2y_3&y_3^2+y_1^2\end{pmatrix}\in\Sym^3$. In Lemma~\ref{lem:matching}, Proposition~\ref{prop:lift}: The two-argument notation denotes the symmetric bilinear polarization $Q(y,z)=\tfrac12\bigl(Q(y+z)-Q(y)-Q(z)\bigr)$ for $y,z\in\mathbb R^3$, so $Q(y,y)=Q(y)$.
- $z$: $z\in\mathbb R^3$ is a real vector argument of $Q$ and its bilinear polarization. In Lemma~\ref{lem:matching}: $(z_1,z_2)\ne(0,0)$, and the proof writes $z=\tau d(\alpha)+\rho k$ with $\tau>0$. In Proposition~\ref{prop:lift}: The matching construction initially uses $(z_1,z_2)\ne(0,0)$. The scalar inequality \eqref{eq:certificate} is then extended to every $z\in\mathbb R^3$ by continuity and subsequently specialized to $z=y$; no extension of $C$ is asserted.
- $N$: The symbol $N$ has distinct local meanings determined by its scope. In Lemma~\ref{lem:matching}: $N=SR_0\in\mathbb C^{3\times2}$ is independent of $\theta$. In Theorem~\ref{thm:main}: $N$ denotes the size of the real symmetric matrix pencil; the construction gives $N=100$.
- $n$: In the matching calculation, $n=N_1\in\mathbb C^{1\times2}$ is the first row of $N=SR_0$, and $n^M=nM$.
- $p$: $p$ is a homogeneous real polynomial on its ambient real vector space, considered with a direction $e$ satisfying $p(e)>0$. In Theorem~\ref{thm:main}, Lemma~\ref{lem:slice}, Proposition~\ref{prop:lift}: $p(X,Z,y)=\det\!\left((\det X)Z-\Phi_y(\adj X)\right)$ on $\mathcal V=\Sym^4\times\Sym^4\times\mathbb R^3$; it has degree twenty and satisfies $p(I_4,I_4,0)=1$.
- $e$: The symbol $e$ denotes the direction with $p(e)>0$ used to define hyperbolicity and the closed cone $K(p,e)$ for the polynomial under consideration. In Theorem~\ref{thm:main}, Lemma~\ref{lem:slice}, Proposition~\ref{prop:lift}: $e=(I_4,I_4,0)\in\mathcal V$ is the specified direction for the polynomial in \eqref{eq:p}, and $p(e)=1$.
- $x$: $x$ is a variable point in the ambient space of $p$. In Theorem~\ref{thm:main}, Lemma~\ref{lem:slice}: $x=(X,Z,y)\in\mathcal V\cong\mathbb R^{23}$, with coordinates given by the upper triangular entries of $X$, then those of $Z$, each in lexicographic order of $(i,j)$, followed by $y_1,y_2,y_3$.
- $t$: $t$ is local real notation, with its scalar or vector role determined by the expression in which it occurs. In Lemma~\ref{lem:slice}: $t\in\mathbb R$ is the scalar indeterminate in $p(te-(\mathcal X,\mathcal Z,Y_\theta(\eta,\xi)))=\det(tI_{20}-L_\theta(\mathcal X,\mathcal Z,\eta,\xi))$. In Proposition~\ref{prop:lift}: In $t^TH(\Lambda)t$, $t=(t_{i,a})\in\mathbb R^{100}$ collects the real coefficients in $q_i=\sum_{a=1}^5t_{i,a}f_a$, $1\leq i\leq20$. In the later test $D=t vv^T$ for $v\in\ker X$, $t$ is instead an arbitrary scalar ranging over all of $\mathbb R$.
- $a$: $a$ is local notation whose scalar or index meaning is determined by the displayed construction in which it occurs. In Theorem~\ref{thm:main}, Lemma~\ref{lem:slice}, Proposition~\ref{prop:lift}: In the definition of $\Phi_y$, $a\in\mathbb R$ is the upper-left entry of its matrix argument. In Lemma~\ref{lem:matching}: In the rotation construction, $a=a(\theta)\in\mathbb C$ is $a=(|g|^2+|h|^2\kappa)/\delta$ when $\delta>0$, and $a=1$ when $\delta=0$, where $\delta=|g|^2+|h|^2$ and $\kappa(\theta)=(w_0/w)^2$. In Theorem~\ref{thm:main}, Proposition~\ref{prop:lift}: In $H(\Lambda)_{(i,a),(j,b)}$, $a$ is an integer basis index with $1\leq a\leq5$.
- $A_\nu$: $A_\nu\in\Sym^{100}$, $1\leq\nu\leq23$, are fixed coefficient matrices, independent of the output point $x$ and the auxiliary vector.
- $B_j$: $B_j$ denotes a real matrix in a locally specified family. In Theorem~\ref{thm:main}: $B_j\in\Sym^{100}$, $1\leq j\leq307$, are fixed auxiliary coefficient matrices of the homogeneous pencil. In Proposition~\ref{prop:lift}: After fixing $y=Y_{\theta_0}(\eta_0,\xi_0)$, $B_j=B(r_j)$ for $1\leq j\leq4$, where $r_j$ are the columns of $\widetilde F_{\theta_0}(\eta_0,\xi_0)$ and $B(r)=\begin{pmatrix}0&r^T\\-r&0_{3\times3}\end{pmatrix}\in\mathbb R^{4\times4}$.
- $v$: The symbol $v$ denotes a locally bound vector, with its space and meaning determined by the enclosing formula. In Theorem~\ref{thm:main}: The vector $v\in\mathbb R^{307}$ is existentially chosen for each output point $x$ in the displayed semidefinite representation. In Lemma~\ref{lem:matching}: In the proof, $v=N_3-iN_2\in\mathbb C^{1\times2}$, and subscripts $+$ and $-$ denote its first and second components. In Proposition~\ref{prop:lift}: In the range-condition argument, $v$ is an arbitrary vector in $\ker X\subseteq\mathbb R^4$.
- $f_1$: The notation $f_1$ is local to its defining tuple: it is the first complex column in $F=(f_1,f_2)$ and the constant real function $f_1(\theta)=1$ in the trigonometric basis $(f_1,\ldots,f_5)$.
- $f_2$: The notation $f_2$ is local to its defining tuple: it is the second complex column in $F=(f_1,f_2)$ and the real function $f_2(\theta)=\cos\theta$ in the trigonometric basis $(f_1,\ldots,f_5)$.
- $r_j$: For $1\leq j\leq4$, $r_j\in\mathbb R^3$ denotes the $j$th column of the realification of $F_\theta(\eta,\xi)$ at the slice parameters currently in use. In Proposition~\ref{prop:lift}: In the calculation leading to \eqref{eq:certificate}, $r_j$ is the $j$th column of $\widetilde F_\theta(\eta,\xi)$ as a function of the slice variables. After choosing $y=Y_{\theta_0}(\eta_0,\xi_0)$, it denotes the $j$th column of $\widetilde F_{\theta_0}(\eta_0,\xi_0)$ for the remainder of the proof, with $B_j=B(r_j)$.
- $H$: When used as an argument of $\langle F,H\rangle_S$, $H$ is an arbitrary matrix in $\mathbb C^{3\times2}$. In Theorem~\ref{thm:main}, Proposition~\ref{prop:lift}: The notation $H(\Lambda)$ denotes the real symmetric moment matrix with entries $H(\Lambda)_{(i,a),(j,b)}=\Lambda\bigl(f_a f_b(L_\theta)_{ij}\bigr)$ for $1\leq i,j\leq20$ and $1\leq a,b\leq5$, using $(f_1,\ldots,f_5)=(1,\cos\theta,\sin\theta,\cos2\theta,\sin2\theta)$.
- $C(\theta)$: $C$ is a chosen function of $\theta\in\mathbb R$ for each fixed pair $(S,z)\in\mathbb S^3\times\mathbb R^3$ satisfying $(z_1,z_2)\ne(0,0)$; its choice may depend on both $S$ and $z$. In Proposition~\ref{prop:lift}: The matching data are $S=J_uDJ_u^T$, with $u\in\mathbb R^4$, $D\in\mathbb S^4$, and $(z_1,z_2)\ne(0,0)$ fixed in the argument.
- $q$: $q$ is a real twenty-component trigonometric polynomial vector in $(\mathcal T_2)^{20}$. In Proposition~\ref{prop:lift}: The constraint \eqref{eq:moment} ranges over every $q\in(\mathcal T_2)^{20}$. To derive \eqref{eq:certificate}, choose $q(\theta)=\bigl((-DJ_u^Tb_1(\theta))^T,\ldots,(-DJ_u^Tb_4(\theta))^T,u^T\bigr)^T$, where $b_j(\theta)$ are the columns of the realification $\widetilde C(\theta)$ supplied by Lemma~\ref{lem:matching} with $S=J_uDJ_u^T$ and $(z_1,z_2)\neq(0,0)$.
- $M$: $M(\theta)=\left(\begin{smallmatrix}a(\theta)&b(\theta)\\-\overline{b(\theta)}&\overline{a(\theta)}\end{smallmatrix}\right)$ uses the prescribed rotation coefficients, is unitary for every real $\theta$, and satisfies $M(\alpha)=I_2$.
- $b$: $b$ denotes either the complex rotation coefficient or the finite basis index, according to its local displayed construction. In Lemma~\ref{lem:matching}: $b=b(\theta)\in\mathbb C$ satisfies $\overline b=gh(1-\kappa)/\delta$ for $\delta>0$, and $b=0$ for $\delta=0$, where $\delta=|g|^2+|h|^2$ and $\kappa(\theta)=(w_0/w)^2$. In Theorem~\ref{thm:main}, Proposition~\ref{prop:lift}: In $H(\Lambda)_{(i,a),(j,b)}$, $b$ is an integer basis index with $1\leq b\leq5$.
- $H(\Lambda)$: $H(\Lambda)$ is indexed by pairs $(i,a)$ with $1\leq i\leq20$ and $1\leq a\leq5$, and its $((i,a),(j,b))$ entry is $\Lambda(f_af_b(L_\theta)_{ij})$.
- $w_0$: $w_0=e^{i\alpha}$ is a unit complex scalar fixed as $\theta$ varies. In Lemma~\ref{lem:matching}: The angle $\alpha$ is chosen from $z=\tau d(\alpha)+\rho k$ with $\tau>0$; equivalently, $w_0=(z_1+iz_2)/\sqrt{z_1^2+z_2^2}$ for $(z_1,z_2)\neq(0,0)$.
- $m$: The symbol $m$ has distinct local meanings determined by its scope. In Lemma~\ref{lem:matching}: $m=N_3+iN_2\in\mathbb C^{1\times2}$ is a row independent of $\theta$. In Theorem~\ref{thm:main}: $m$ denotes the number of auxiliary variables; the construction gives $m=307$.
- $b_j$: $b_j(\theta)$, $1\leq j\leq4$, are the columns of $\widetilde C(\theta)$ and are real trigonometric polynomials of degree at most two with values in $\mathbb R^3$. In Proposition~\ref{prop:lift}: For each fixed $u\in\mathbb R^4$, $D\in\mathbb S^4$, and $z\in\mathbb R^3$ with $(z_1,z_2)\neq(0,0)$, the columns are chosen from a matching matrix for $S=J_uDJ_u^T$ and $z$; this choice may depend on $u,D,z$, and neither $D$ nor $S$ is required to be positive semidefinite.
- $\widetilde C(\theta)$: For each fixed $S\in\mathbb S^3$ and $z\in\mathbb R^3$ with $(z_1,z_2)\ne(0,0)$, $\widetilde C(\theta)$ is the realification of a chosen matching function $C(\theta)$, with $\theta\in\mathbb R$; the choice may depend on $S$ and $z$. In Proposition~\ref{prop:lift}: The chosen matrix is obtained with $S=J_uDJ_u^T$, for fixed $u\in\mathbb R^4$, $D\in\mathbb S^4$, and $z\in\mathbb R^3$ satisfying $(z_1,z_2)\ne(0,0)$.

## What was proved in Lean, and what was not

A result is proved in Lean when a Lean declaration reviewed as stating it has a complete proof using no axiom beyond the standard ones. For a corrected result, the corrected statement is the one formalized.

| Result | Formal status | Lean declaration | Axioms |
| --- | --- | --- | --- |
| Theorem 1.1 | proved in Lean, under 2 condition(s) made explicit | `Papers.OaiExactSemidefiniteLift.exact_semidefinite_lift` (`TMain.lean:30`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 2.1 | proved in Lean | `Papers.OaiExactSemidefiniteLift.gram_identity` (`Helpers/Gram.lean:132`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 2.2 | proved in Lean | `Papers.OaiExactSemidefiniteLift.slice_equivalence` (`Helpers/Slice.lean:432`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 3.1 | proved in Lean, under 1 condition(s) made explicit | `Papers.OaiExactSemidefiniteLift.matching_exists` (`Helpers/Matching.lean:278`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Proposition 4.1 | proved in Lean, under 2 condition(s) made explicit | `Papers.OaiExactSemidefiniteLift.lift_equivalence` (`Helpers/Lift.lean:22`) | the standard ones only (propext, Classical.choice, Quot.sound) |

The Lean development builds; it contains no `sorry`, `admit` or added axiom.

## The corrected paper

`bundle/corrected_paper/` holds the paper as it reads after the corrections, as plain source in the author's own class and layout, compiled to `bundle/corrected_paper/main.pdf` (12 pages). `bundle/MATCH.md` sets each result beside its Lean declaration; `bundle/lean/` holds the Lean code.

The mechanical checks leave nothing open.

# Technical appendix

The records behind the report above, by the run's own identifiers.

- paper: `main.tex` (source sha256 `f2168c225106fb1bcf7d9516942b0ea9b6144538d31ad518a4dcf93941bde4a2`)
- stage completed: `5`
- results in scope: 5

| bucket | count |
| --- | --- |
| verified | 2 |
| verified_with_bookkeeping | 3 |
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
| source | `sections/introduction.tex:68-79` (`theorem`, label `thm:main`) |
| statement | \label{thm:main} There exist fixed matrices $A_1,\ldots,A_{23},B_1,\ldots,B_{307} \in\Sym^{100}$ such that, for every $x=(X,Z,y)\in\mathcal V$, \[ x\in K\quad\Longleftrightarrow\quad \text{there exists }v\in\R^{307}\text{ with } \sum_{\nu=1}^{23}x_\nu A_\nu+ \sum_{j=1}^{307}v_jB_j\succeq0. \] The equivalence holds on the entire closed cone, including points with singular $X$. |
| Lean | `TMain.lean:30` — `Papers.OaiExactSemidefiniteLift.exact_semidefinite_lift` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | `ass:pin-1`, `ass:pin-2` |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 2. Angular Gram factorization `lem:gram`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `sections/angular.tex:32-40` (`lemma`, label `lem:gram`) |
| statement | \label{lem:gram} For every $\theta,\eta,\xi\in\mathbb R$, \begin{equation}\label{eq:gram} \widetilde F_\theta(\eta,\xi) \widetilde F_\theta(\eta,\xi)^T =Q\bigl(Y_\theta(\eta,\xi)\bigr). \end{equation} In particular, $Q(y)\succeq0$ for every $y\in\mathbb R^3$. |
| Lean | `Helpers/Gram.lean:132` — `Papers.OaiExactSemidefiniteLift.gram_identity` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 3. `lem:slice`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `sections/slices.tex:51-63` (`lemma`, label `lem:slice`) |
| statement | \label{lem:slice} For every $\theta,\eta,\xi\in\R$ and $\mathcal X,\mathcal Z\in\Sym^4$, \begin{equation}\label{eq:slice-equivalence} (\mathcal X,\mathcal Z,Y_\theta(\eta,\xi))\in K \quad\Longleftrightarrow\quad L_\theta(\mathcal X,\mathcal Z,\eta,\xi)\succeq0. \end{equation} In particular, $p$ is hyperbolic with respect to $e$. If $\mathcal X\succ0$, the conditions in \eqref{eq:slice-equivalence} are also equivalent to $\mathcal Z\succeq\Phi_{Y_\theta(\eta,\xi)}(\mathcal X^{-1})$. |
| Lean | `Helpers/Slice.lean:432` — `Papers.OaiExactSemidefiniteLift.slice_equivalence` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 4. Degree-two matching `lem:matching`

| field | value |
| --- | --- |
| bucket | `verified_with_bookkeeping` |
| source | `sections/matching.tex:29-42` (`lemma`, label `lem:matching`) |
| statement | \label{lem:matching} Let $S\in\mathbb S^3$ and let $z\in\mathbb R^3$ satisfy $(z_1,z_2)\ne(0,0)$. There is a matrix $C(\theta)\in\mathbb C^{3\times2}$ whose entries are trigonometric polynomials of degree at most two such that, for all $\theta,\eta,\xi\in\mathbb R$, \begin{equation}\label{eq:matching} \begin{aligned} \widetilde C(\theta)\widetilde C(\theta)^T&=Q(z),\\ \langle F_\theta(\eta,\xi),C(\theta)\rangle_S &=\operatorname{tr}\bigl(SQ(Y_\theta(\eta,\xi),z)\bigr). \end{aligned} \end{equation} |
| appended hypothesis list | ass:matching |
| Lean | `Helpers/Matching.lean:278` — `Papers.OaiExactSemidefiniteLift.matching_exists` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | `ass:pin-2` |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 5. `prop:lift`

| field | value |
| --- | --- |
| bucket | `verified_with_bookkeeping` |
| source | `sections/lift.tex:57-65` (`proposition`, label `prop:lift`) |
| statement | \label{prop:lift} For $(X,Z,y)\in\mathbb S^4\times\mathbb S^4\times\mathbb R^3$, the following are equivalent: \begin{enumerate} \item $(X,Z,y)\in K$; \item there is a real linear functional $\Lambda:\mathcal E\to\mathbb R$ satisfying~\eqref{eq:output} and $H(\Lambda)\succeq0$. \end{enumerate} |
| Lean | `Helpers/Lift.lean:22` — `Papers.OaiExactSemidefiniteLift.lift_equivalence` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | `ass:pin-1`, `ass:pin-2` |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

## Corrected version

3 of 5 result(s) differ from the version you provided — 0 repaired, 0 with the proof completed (no error), 3 only with a side condition or reading made explicit; the others are as printed. The Lean formalization is of the corrected version.

### `thm:main` (`sections/introduction.tex:68-79`)

- as printed: \label{thm:main} There exist fixed matrices $A_1,\ldots,A_{23},B_1,\ldots,B_{307} \in\Sym^{100}$ such that, for every $x=(X,Z,y)\in\mathcal V$, \[ x\in K\quad\Longleftrightarrow\quad \text{there exists }v\in\R^{307}\text{ with } \sum_{\nu=1}^{23}x_\nu A_\nu+ \sum_{j=1}^{307}v_jB_j\succeq0. \] The equivalence holds on the entire closed cone, including points with singular $X$.
- corrected: statement unchanged
- no error: only a side condition or reading the referee made explicit (see below)
- side condition added by the confirming referee `ass:pin-1`: In the moment-matrix definition, $(f_1,\ldots,f_5)=(1,\cos\theta,\sin\theta,\cos2\theta,\sin2\theta)$ are real functions and $H(\Lambda)\in\mathbb S^{100}$ is indexed by $(i,a)$ with $1\leq i\leq20$ and $1\leq a\leq5$. — pins reading of def:moment-matrix: The sentence beginning ``Indeed, set'' explicitly assigns the five real functions and the real symmetric matrix space before giving its entries.
- side condition added by the confirming referee `ass:pin-2`: The linear combination is finite, with coefficients in $\mathbb C$ independent of $\theta$ and indices $\ell\in\mathbb Z$ satisfying $-j\leq\ell\leq j$. — pins reading of def:complex-trigonometric-polynomials: This is the standard trigonometric-polynomial convention, also used in Lemma~\ref{lem:matching}, where the frequency-reduction calculation expands in integer powers of $w=e^{i\theta}$.

### `lem:matching` (`sections/matching.tex:29-42`)

- as printed: \label{lem:matching} Let $S\in\mathbb S^3$ and let $z\in\mathbb R^3$ satisfy $(z_1,z_2)\ne(0,0)$. There is a matrix $C(\theta)\in\mathbb C^{3\times2}$ whose entries are trigonometric polynomials of degree at most two such that, for all $\theta,\eta,\xi\in\mathbb R$, \begin{equation}\label{eq:matching} \begin{aligned} \widetilde C(\theta)\widetilde C(\theta)^T&=Q(z),\\ \langle F_\theta(\eta,\xi),C(\theta)\rangle_S &=\operatorname{tr}\bigl(SQ(Y_\theta(\eta,\xi),z)\bigr). \end{aligned} \end{equation}
- corrected: statement unchanged
- no error: only a side condition or reading the referee made explicit (see below)
- side condition added by the confirming referee `ass:pin-2`: The linear combination is finite, with coefficients in $\mathbb C$ independent of $\theta$ and indices $\ell\in\mathbb Z$ satisfying $-j\leq\ell\leq j$. — pins reading of def:complex-trigonometric-polynomials: This is the standard trigonometric-polynomial convention, also used in Lemma~\ref{lem:matching}, where the frequency-reduction calculation expands in integer powers of $w=e^{i\theta}$.

### `prop:lift` (`sections/lift.tex:57-65`)

- as printed: \label{prop:lift} For $(X,Z,y)\in\mathbb S^4\times\mathbb S^4\times\mathbb R^3$, the following are equivalent: \begin{enumerate} \item $(X,Z,y)\in K$; \item there is a real linear functional $\Lambda:\mathcal E\to\mathbb R$ satisfying~\eqref{eq:output} and $H(\Lambda)\succeq0$. \end{enumerate}
- corrected: statement unchanged
- no error: only a side condition or reading the referee made explicit (see below)
- side condition added by the confirming referee `ass:pin-1`: In the moment-matrix definition, $(f_1,\ldots,f_5)=(1,\cos\theta,\sin\theta,\cos2\theta,\sin2\theta)$ are real functions and $H(\Lambda)\in\mathbb S^{100}$ is indexed by $(i,a)$ with $1\leq i\leq20$ and $1\leq a\leq5$. — pins reading of def:moment-matrix: The sentence beginning ``Indeed, set'' explicitly assigns the five real functions and the real symmetric matrix space before giving its entries.
- side condition added by the confirming referee `ass:pin-2`: The linear combination is finite, with coefficients in $\mathbb C$ independent of $\theta$ and indices $\ell\in\mathbb Z$ satisfying $-j\leq\ell\leq j$. — pins reading of def:complex-trigonometric-polynomials: This is the standard trigonometric-polynomial convention, also used in Lemma~\ref{lem:matching}, where the frequency-reduction calculation expands in integer powers of $w=e^{i\theta}$.

## Suggestions to the authors

Not errors: readings the paper determines but does not state, and side conditions the proofs use silently.

- clarification (`ass:pin-1`, used by `thm:main`): In the moment-matrix definition, $(f_1,\ldots,f_5)=(1,\cos\theta,\sin\theta,\cos2\theta,\sin2\theta)$ are real functions and $H(\Lambda)\in\mathbb S^{100}$ is indexed by $(i,a)$ with $1\leq i\leq20$ and $1\leq a\leq5$. — pins reading of def:moment-matrix: The sentence beginning ``Indeed, set'' explicitly assigns the five real functions and the real symmetric matrix space before giving its entries.
- clarification (`ass:pin-2`, used by `thm:main`): The linear combination is finite, with coefficients in $\mathbb C$ independent of $\theta$ and indices $\ell\in\mathbb Z$ satisfying $-j\leq\ell\leq j$. — pins reading of def:complex-trigonometric-polynomials: This is the standard trigonometric-polynomial convention, also used in Lemma~\ref{lem:matching}, where the frequency-reduction calculation expands in integer powers of $w=e^{i\theta}$.
- `def:complex-trigonometric-polynomials`: pinned reading: The linear combination is finite, with coefficients in $\mathbb C$ independent of $\theta$ and indices $\ell\in\mathbb Z$ satisfying $-j\leq\ell\leq j$. (This is the standard trigonometric-polynomial convention, also used in Lemma~\ref{lem:matching}, where the frequency-reduction calculation expands in integer powers of $w=e^{i\theta}$.)
- `def:moment-matrix`: pinned reading: In the moment-matrix definition, $(f_1,\ldots,f_5)=(1,\cos\theta,\sin\theta,\cos2\theta,\sin2\theta)$ are real functions and $H(\Lambda)\in\mathbb S^{100}$ is indexed by $(i,a)$ with $1\leq i\leq20$ and $1\leq a\leq5$. (The sentence beginning ``Indeed, set'' explicitly assigns the five real functions and the real symmetric matrix space before giving its entries.)
- reading of the symbol `S`: $S\in\mathbb S^3$ is the real symmetric weight in $\langle F,H\rangle_S=\operatorname{Re}\operatorname{tr}(F^*SH)$, with no positive semidefiniteness requirement. In Proposition~\ref{prop:lift}: In the matching construction, $S=J_uDJ_u^T$, where $u\in\mathbb R^4$ and $D\in\mathbb S^4$ are arbitrary; neither $D$ nor $S$ must be positive semidefinite. — The weighted-pairing definition permits every real symmetric S; the matching discussion explicitly permits indefinite S. The proof of Proposition~\ref{prop:lift} sets $S=J_uDJ_u^T$.
- reading of the symbol `Q`: For $y=(y_1,y_2,y_3)\in\mathbb R^3$, $Q(y)=\begin{pmatrix}y_1^2+y_2^2&-y_1y_2&-y_1y_3\\-y_1y_2&y_2^2+y_3^2&-y_2y_3\\-y_1y_3&-y_2y_3&y_3^2+y_1^2\end{pmatrix}\in\Sym^3$. In Lemma~\ref{lem:matching}, Proposition~\ref{prop:lift}: The two-argument notation denotes the symmetric bilinear polarization $Q(y,z)=\tfrac12\bigl(Q(y+z)-Q(y)-Q(z)\bigr)$ for $y,z\in\mathbb R^3$, so $Q(y,y)=Q(y)$. — Equation~\eqref{eq:Q} defines the quadratic map. The opening display of Section~\ref{sec:matching} defines its symmetric bilinear polarization, used in Lemma~\ref{lem:matching} and Proposition~\ref{prop:lift}.
- reading of the symbol `z`: $z\in\mathbb R^3$ is a real vector argument of $Q$ and its bilinear polarization. In Lemma~\ref{lem:matching}: $(z_1,z_2)\ne(0,0)$, and the proof writes $z=\tau d(\alpha)+\rho k$ with $\tau>0$. In Proposition~\ref{prop:lift}: The matching construction initially uses $(z_1,z_2)\ne(0,0)$. The scalar inequality \eqref{eq:certificate} is then extended to every $z\in\mathbb R^3$ by continuity and subsequently specialized to $z=y$; no extension of $C$ is asserted. — Lemma~\ref{lem:matching} assumes $(z_1,z_2)\ne(0,0)$. The proof of Proposition~\ref{prop:lift} initially imposes this restriction, then explicitly extends the scalar certificate to every real z by continuity.
- reading of the symbol `N`: The symbol $N$ has distinct local meanings determined by its scope. In Lemma~\ref{lem:matching}: $N=SR_0\in\mathbb C^{3\times2}$ is independent of $\theta$. In Theorem~\ref{thm:main}: $N$ denotes the size of the real symmetric matrix pencil; the construction gives $N=100$. — The matching proof defines $N=SR_0$; the final proof uses $N$ for the pencil size.
- reading of the symbol `n`: In the matching calculation, $n=N_1\in\mathbb C^{1\times2}$ is the first row of $N=SR_0$, and $n^M=nM$. — The proof of Lemma~\ref{lem:matching} explicitly sets $n=N_1$ and $n^M=nM$; the earlier superscript in $\Sym^n$ is only a matrix-size parameter.
- reading of the symbol `p`: $p$ is a homogeneous real polynomial on its ambient real vector space, considered with a direction $e$ satisfying $p(e)>0$. In Theorem~\ref{thm:main}, Lemma~\ref{lem:slice}, Proposition~\ref{prop:lift}: $p(X,Z,y)=\det\!\left((\det X)Z-\Phi_y(\adj X)\right)$ on $\mathcal V=\Sym^4\times\Sym^4\times\mathbb R^3$; it has degree twenty and satisfies $p(I_4,I_4,0)=1$. — The introduction gives the generic convention; equation~\eqref{eq:p} then specifies the polynomial on $\mathcal V$ and states its degree and value at $e$.
- reading of the symbol `e`: The symbol $e$ denotes the direction with $p(e)>0$ used to define hyperbolicity and the closed cone $K(p,e)$ for the polynomial under consideration. In Theorem~\ref{thm:main}, Lemma~\ref{lem:slice}, Proposition~\ref{prop:lift}: $e=(I_4,I_4,0)\in\mathcal V$ is the specified direction for the polynomial in \eqref{eq:p}, and $p(e)=1$. — The introductory definition allows a general direction with $p(e)>0$; \eqref{eq:p} then specifies $e=(I_4,I_4,0)$ and states $p(e)=1$.
- reading of the symbol `x`: $x$ is a variable point in the ambient space of $p$. In Theorem~\ref{thm:main}, Lemma~\ref{lem:slice}: $x=(X,Z,y)\in\mathcal V\cong\mathbb R^{23}$, with coordinates given by the upper triangular entries of $X$, then those of $Z$, each in lexicographic order of $(i,j)$, followed by $y_1,y_2,y_3$. — The introductory root convention quantifies over every $x$; the coordinate identification preceding Theorem~\ref{thm:main} specifies the ordering on $\mathcal V$.
- reading of the symbol `t`: $t$ is local real notation, with its scalar or vector role determined by the expression in which it occurs. In Lemma~\ref{lem:slice}: $t\in\mathbb R$ is the scalar indeterminate in $p(te-(\mathcal X,\mathcal Z,Y_\theta(\eta,\xi)))=\det(tI_{20}-L_\theta(\mathcal X,\mathcal Z,\eta,\xi))$. In Proposition~\ref{prop:lift}: In $t^TH(\Lambda)t$, $t=(t_{i,a})\in\mathbb R^{100}$ collects the real coefficients in $q_i=\sum_{a=1}^5t_{i,a}f_a$, $1\leq i\leq20$. In the later test $D=t vv^T$ for $v\in\ker X$, $t$ is instead an arbitrary scalar ranging over all of $\mathbb R$. — Equation~\eqref{eq:roots} uses the polynomial argument; the calculation following \eqref{eq:moment-matrix} uses the coefficient vector; the proof of Proposition~\ref{prop:lift} explicitly quantifies the scalar in $D=t vv^T$ over all real numbers.
- reading of the symbol `a`: $a$ is local notation whose scalar or index meaning is determined by the displayed construction in which it occurs. In Theorem~\ref{thm:main}, Lemma~\ref{lem:slice}, Proposition~\ref{prop:lift}: In the definition of $\Phi_y$, $a\in\mathbb R$ is the upper-left entry of its matrix argument. In Lemma~\ref{lem:matching}: In the rotation construction, $a=a(\theta)\in\mathbb C$ is $a=(\|g\|^2+\|h\|^2\kappa)/\delta$ when $\delta>0$, and $a=1$ when $\delta=0$, where $\delta=\|g\|^2+\|h\|^2$ and $\kappa(\theta)=(w_0/w)^2$. In Theorem~\ref{thm:main}, Proposition~\ref{prop:lift}: In $H(\Lambda)_{(i,a),(j,b)}$, $a$ is an integer basis index with $1\leq a\leq5$. — Equation~\eqref{eq:Phi} uses $a\in\mathbb R$; equations~\eqref{eq:rotation-system} and~\eqref{eq:rotation-coefficients} define the complex function; equation~\eqref{eq:moment-matrix} uses $1\leq a\leq5$.
- reading of the symbol `A_\nu`: $A_\nu\in\Sym^{100}$, $1\leq\nu\leq23$, are fixed coefficient matrices, independent of the output point $x$ and the auxiliary vector. — Theorem~\ref{thm:main} explicitly says that the matrices are fixed and quantifies over every output point afterward.
- reading of the symbol `B_j`: $B_j$ denotes a real matrix in a locally specified family. In Theorem~\ref{thm:main}: $B_j\in\Sym^{100}$, $1\leq j\leq307$, are fixed auxiliary coefficient matrices of the homogeneous pencil. In Proposition~\ref{prop:lift}: After fixing $y=Y_{\theta_0}(\eta_0,\xi_0)$, $B_j=B(r_j)$ for $1\leq j\leq4$, where $r_j$ are the columns of $\widetilde F_{\theta_0}(\eta_0,\xi_0)$ and $B(r)=\begin{pmatrix}0&r^T\\-r&0_{3\times3}\end{pmatrix}\in\mathbb R^{4\times4}$. — Theorem~\ref{thm:main} specifies fixed coefficient matrices; the proof of Proposition~\ref{prop:lift} introduces a separate family using \eqref{eq:BJ}.
- reading of the symbol `v`: The symbol $v$ denotes a locally bound vector, with its space and meaning determined by the enclosing formula. In Theorem~\ref{thm:main}: The vector $v\in\mathbb R^{307}$ is existentially chosen for each output point $x$ in the displayed semidefinite representation. In Lemma~\ref{lem:matching}: In the proof, $v=N_3-iN_2\in\mathbb C^{1\times2}$, and subscripts $+$ and $-$ denote its first and second components. In Proposition~\ref{prop:lift}: In the range-condition argument, $v$ is an arbitrary vector in $\ker X\subseteq\mathbb R^4$. — The existential quantifier in Theorem~\ref{thm:main}, the definition $v=N_3-iN_2$ in the proof of Lemma~\ref{lem:matching}, and the instruction to take $v\in\ker X$ in the proof of Proposition~\ref{prop:lift} give distinct bindings; the block calculation preceding Lemma~\ref{lem:slice} also uses $v\in\mathbb R^3$.
- reading of the symbol `f_1`: The notation $f_1$ is local to its defining tuple: it is the first complex column in $F=(f_1,f_2)$ and the constant real function $f_1(\theta)=1$ in the trigonometric basis $(f_1,\ldots,f_5)$. — The realification paragraph defines the complex columns; the paragraph preceding \eqref{eq:moment-matrix} explicitly assigns the real basis tuple.
- reading of the symbol `f_2`: The notation $f_2$ is local to its defining tuple: it is the second complex column in $F=(f_1,f_2)$ and the real function $f_2(\theta)=\cos\theta$ in the trigonometric basis $(f_1,\ldots,f_5)$. — The realification paragraph defines the complex columns; the paragraph preceding \eqref{eq:moment-matrix} explicitly assigns the real basis tuple.
- reading of the symbol `r_j`: For $1\leq j\leq4$, $r_j\in\mathbb R^3$ denotes the $j$th column of the realification of $F_\theta(\eta,\xi)$ at the slice parameters currently in use. In Proposition~\ref{prop:lift}: In the calculation leading to \eqref{eq:certificate}, $r_j$ is the $j$th column of $\widetilde F_\theta(\eta,\xi)$ as a function of the slice variables. After choosing $y=Y_{\theta_0}(\eta_0,\xi_0)$, it denotes the $j$th column of $\widetilde F_{\theta_0}(\eta_0,\xi_0)$ for the remainder of the proof, with $B_j=B(r_j)$. — The paragraph following \eqref{eq:BJ} defines the columns of $\widetilde F_\theta(\eta,\xi)$. The proof of Proposition~\ref{prop:lift} first uses these variable columns in the certificate calculation, then explicitly fixes their evaluation for the remainder of the proof.
- reading of the symbol `H`: When used as an argument of $\langle F,H\rangle_S$, $H$ is an arbitrary matrix in $\mathbb C^{3\times2}$. In Theorem~\ref{thm:main}, Proposition~\ref{prop:lift}: The notation $H(\Lambda)$ denotes the real symmetric moment matrix with entries $H(\Lambda)_{(i,a),(j,b)}=\Lambda\bigl(f_a f_b(L_\theta)_{ij}\bigr)$ for $1\leq i,j\leq20$ and $1\leq a,b\leq5$, using $(f_1,\ldots,f_5)=(1,\cos\theta,\sin\theta,\cos2\theta,\sin2\theta)$. — The weighted-pairing definition specifies $F,H\in\mathbb C^{3\times2}$; \eqref{eq:moment-matrix} separately introduces $H(\Lambda)\in\Sym^{100}$.
- reading of the symbol `C(\theta)`: $C$ is a chosen function of $\theta\in\mathbb R$ for each fixed pair $(S,z)\in\mathbb S^3\times\mathbb R^3$ satisfying $(z_1,z_2)\ne(0,0)$; its choice may depend on both $S$ and $z$. In Proposition~\ref{prop:lift}: The matching data are $S=J_uDJ_u^T$, with $u\in\mathbb R^4$, $D\in\mathbb S^4$, and $(z_1,z_2)\ne(0,0)$ fixed in the argument. — The quantifier order and the two identities in Lemma~\ref{lem:matching} fix the parameters and the choice.
- reading of the symbol `q`: $q$ is a real twenty-component trigonometric polynomial vector in $(\mathcal T_2)^{20}$. In Proposition~\ref{prop:lift}: The constraint \eqref{eq:moment} ranges over every $q\in(\mathcal T_2)^{20}$. To derive \eqref{eq:certificate}, choose $q(\theta)=\bigl((-DJ_u^Tb_1(\theta))^T,\ldots,(-DJ_u^Tb_4(\theta))^T,u^T\bigr)^T$, where $b_j(\theta)$ are the columns of the realification $\widetilde C(\theta)$ supplied by Lemma~\ref{lem:matching} with $S=J_uDJ_u^T$ and $(z_1,z_2)\neq(0,0)$. — Equation \eqref{eq:moment} quantifies over every such vector. The proof of Proposition~\ref{prop:lift}, immediately after introducing the columns of $\widetilde C(\theta)$, specifies its five blocks.
- reading of the symbol `M`: $M(\theta)=\left(\begin{smallmatrix}a(\theta)&b(\theta)\\-\overline{b(\theta)}&\overline{a(\theta)}\end{smallmatrix}\right)$ uses the prescribed rotation coefficients, is unitary for every real $\theta$, and satisfies $M(\alpha)=I_2$. — Equations~\eqref{eq:rotation-system} and~\eqref{eq:rotation-coefficients}, together with the prescribed choice for $\delta=0$, fix the coefficients; the following sentence states unitarity and $M(\alpha)=I_2$.
- reading of the symbol `b`: $b$ denotes either the complex rotation coefficient or the finite basis index, according to its local displayed construction. In Lemma~\ref{lem:matching}: $b=b(\theta)\in\mathbb C$ satisfies $\overline b=gh(1-\kappa)/\delta$ for $\delta>0$, and $b=0$ for $\delta=0$, where $\delta=\|g\|^2+\|h\|^2$ and $\kappa(\theta)=(w_0/w)^2$. In Theorem~\ref{thm:main}, Proposition~\ref{prop:lift}: In $H(\Lambda)_{(i,a),(j,b)}$, $b$ is an integer basis index with $1\leq b\leq5$. — Equation~\eqref{eq:rotation-coefficients} and the following zero case define the coefficient; equation~\eqref{eq:moment-matrix} explicitly gives the later index range.
- reading of the symbol `H(\Lambda)`: $H(\Lambda)$ is indexed by pairs $(i,a)$ with $1\leq i\leq20$ and $1\leq a\leq5$, and its $((i,a),(j,b))$ entry is $\Lambda(f_af_b(L_\theta)_{ij})$. — Equation~\eqref{eq:moment-matrix} explicitly gives both index ranges.
- reading of the symbol `w_0`: $w_0=e^{i\alpha}$ is a unit complex scalar fixed as $\theta$ varies. In Lemma~\ref{lem:matching}: The angle $\alpha$ is chosen from $z=\tau d(\alpha)+\rho k$ with $\tau>0$; equivalently, $w_0=(z_1+iz_2)/\sqrt{z_1^2+z_2^2}$ for $(z_1,z_2)\neq(0,0)$. — The proof of Lemma~\ref{lem:matching} writes $z=\tau d(\alpha)+\rho k$ with $\tau>0$ before setting $w_0=e^{i\alpha}$.
- reading of the symbol `m`: The symbol $m$ has distinct local meanings determined by its scope. In Lemma~\ref{lem:matching}: $m=N_3+iN_2\in\mathbb C^{1\times2}$ is a row independent of $\theta$. In Theorem~\ref{thm:main}: $m$ denotes the number of auxiliary variables; the construction gives $m=307$. — The matching proof defines $m=N_3+iN_2$; the final proof uses $m$ for the auxiliary-variable count.
- reading of the symbol `b_j`: $b_j(\theta)$, $1\leq j\leq4$, are the columns of $\widetilde C(\theta)$ and are real trigonometric polynomials of degree at most two with values in $\mathbb R^3$. In Proposition~\ref{prop:lift}: For each fixed $u\in\mathbb R^4$, $D\in\mathbb S^4$, and $z\in\mathbb R^3$ with $(z_1,z_2)\neq(0,0)$, the columns are chosen from a matching matrix for $S=J_uDJ_u^T$ and $z$; this choice may depend on $u,D,z$, and neither $D$ nor $S$ is required to be positive semidefinite. — The proof of Proposition~\ref{prop:lift} fixes $u,D,z$, applies Lemma~\ref{lem:matching} with $S=J_uDJ_u^T$, and defines the columns of the resulting $\widetilde C(\theta)$; it then invokes the degree bound.
- reading of the symbol `\widetilde C(\theta)`: For each fixed $S\in\mathbb S^3$ and $z\in\mathbb R^3$ with $(z_1,z_2)\ne(0,0)$, $\widetilde C(\theta)$ is the realification of a chosen matching function $C(\theta)$, with $\theta\in\mathbb R$; the choice may depend on $S$ and $z$. In Proposition~\ref{prop:lift}: The chosen matrix is obtained with $S=J_uDJ_u^T$, for fixed $u\in\mathbb R^4$, $D\in\mathbb S^4$, and $z\in\mathbb R^3$ satisfying $(z_1,z_2)\ne(0,0)$. — Lemma~\ref{lem:matching} chooses the matrix after fixing $S$ and $z$; the realification definition specifies its four real columns.

## Added conditions

| id | where | class | condition |
| --- | --- | --- | --- |
| `ass:pin-1` | `thm:main` | V1.5 bookkeeping | In the moment-matrix definition, $(f_1,\ldots,f_5)=(1,\cos\theta,\sin\theta,\cos2\theta,\sin2\theta)$ are real functions and $H(\Lambda)\in\mathbb S^{100}$ is indexed by $(i,a)$ with $1\leq i\leq20$ and $1\leq a\leq5$. (pins reading of def:moment-matrix: The sentence beginning ``Indeed, set'' explicitly assigns the five real functions and the real symmetric matrix space before giving its entries.) |
| `ass:pin-2` | `thm:main` | V1.5 bookkeeping | The linear combination is finite, with coefficients in $\mathbb C$ independent of $\theta$ and indices $\ell\in\mathbb Z$ satisfying $-j\leq\ell\leq j$. (pins reading of def:complex-trigonometric-polynomials: This is the standard trigonometric-polynomial convention, also used in Lemma~\ref{lem:matching}, where the frequency-reduction calculation expands in integer powers of $w=e^{i\theta}$.) |
| `ass:pin-2` | `lem:matching` | V1.5 bookkeeping | The linear combination is finite, with coefficients in $\mathbb C$ independent of $\theta$ and indices $\ell\in\mathbb Z$ satisfying $-j\leq\ell\leq j$. (pins reading of def:complex-trigonometric-polynomials: This is the standard trigonometric-polynomial convention, also used in Lemma~\ref{lem:matching}, where the frequency-reduction calculation expands in integer powers of $w=e^{i\theta}$.) |
| `ass:pin-1` | `prop:lift` | V1.5 bookkeeping | In the moment-matrix definition, $(f_1,\ldots,f_5)=(1,\cos\theta,\sin\theta,\cos2\theta,\sin2\theta)$ are real functions and $H(\Lambda)\in\mathbb S^{100}$ is indexed by $(i,a)$ with $1\leq i\leq20$ and $1\leq a\leq5$. (pins reading of def:moment-matrix: The sentence beginning ``Indeed, set'' explicitly assigns the five real functions and the real symmetric matrix space before giving its entries.) |
| `ass:pin-2` | `prop:lift` | V1.5 bookkeeping | The linear combination is finite, with coefficients in $\mathbb C$ independent of $\theta$ and indices $\ell\in\mathbb Z$ satisfying $-j\leq\ell\leq j$. (pins reading of def:complex-trigonometric-polynomials: This is the standard trigonometric-polynomial convention, also used in Lemma~\ref{lem:matching}, where the frequency-reduction calculation expands in integer powers of $w=e^{i\theta}$.) |

## Conditions assumed

### Cited results

None: no result rests on a theorem imported from the literature.

### Deferred substrate gates

None: every substrate this run needed was built and proved.

## Unresolved / notes

- run-level `def:moment-matrix`: [note, V1.5] pinned reading: In the moment-matrix definition, $(f_1,\ldots,f_5)=(1,\cos\theta,\sin\theta,\cos2\theta,\sin2\theta)$ are real functions and $H(\Lambda)\in\mathbb S^{100}$ is indexed by $(i,a)$ with $1\leq i\leq20$ and $1\leq a\leq5$. (The sentence beginning ``Indeed, set'' explicitly assigns the five real functions and the real symmetric matrix space before giving its entries.)
- run-level `def:complex-trigonometric-polynomials`: [note, V1.5] pinned reading: The linear combination is finite, with coefficients in $\mathbb C$ independent of $\theta$ and indices $\ell\in\mathbb Z$ satisfying $-j\leq\ell\leq j$. (This is the standard trigonometric-polynomial convention, also used in Lemma~\ref{lem:matching}, where the frequency-reduction calculation expands in integer powers of $w=e^{i\theta}$.)
- run-level `symbol U(\theta)`: [note, V1.5] symbol table corrected: def "$U(\theta)=\frac1{\sqrt2}\begin{pmatrix}-w^{-1}&-w\\sw^{-2}&sw^2\\cw^{-2}&-cw^2\end{pmatrix}$." (The recorded definition identifies only its role as a coefficient; the paper defines a specific matrix whose entries determine the subsequent calculations.)
- run-level `symbol Q`: [note, V1.5] symbol table corrected: def "$Q(y)=\begin{pmatrix}y_1^2+y_2^2&-y_1y_2&-y_1y_3\\-y_1y_2&y_2^2+y_3^2&-y_2y_3\\-y_1y_3&-y_2y_3&y_3^2+y_1^2\end{pmatrix}$." (The recorded definition only points to an equation instead of recording its defining entries. The later two-argument notation extends the notation to the explicitly defined polarization; it does not replace the original quadratic map.)
- run-level `symbol p`: [note, V1.5] symbol table corrected: def "Initially $p$ is a homogeneous real polynomial with $p(e)>0$; on $\mathcal V=\Sym^4\times\Sym^4\times\mathbb R^3$ the paper defines $p(X,Z,y)=\det\!\left((\det X)Z-\Phi_y(\adj X)\right)$, with $e=(I_4,I_4,0)$." (The recorded definition retains only the generic introductory polynomial and omits the determinant formula that defines the particular cone. The generic convention precedes the explicit specialization.)
- run-level `symbol e`: [note, V1.5] symbol table corrected: def "A direction satisfying $p(e)>0$ in the general closed-cone convention, specialized for the polynomial on $\mathcal V$ in \eqref{eq:p} to $e=(I_4,I_4,0)$." (The recorded entry retains only the generic introductory direction. The paper subsequently fixes the particular direction $(I_4,I_4,0)$, which is the meaning used throughout the cone construction and its results.)
- run-level `symbol t`: [note, V1.5] symbol table corrected: type "real scalar or real coefficient vector, according to the local notation", space "$\mathbb R$ for the polynomial argument and scalar tests; $\mathbb R^{100}$ for the moment-matrix coefficient vector", def "$t$ is the scalar argument in $p(te-x)$; in the moment-matrix calculation it is the vector with entries $t_{i,a}$ defined by $q_i=\sum_a t_{i,a}f_a$; in the range-condition argument it is an arbitrary real scalar in $D=t vv^T$." (The scalar-only entry misses the 100-dimensional coefficient vector used in the moment-matrix calculation and the later independent scalar test. The paper distinguishes these roles locally.)
- run-level `symbol a`: [note, V1.5] symbol table corrected: type "local scalar or moment index", space "$\mathbb R$ for the block scalar, $\mathbb C$ for the rotation coefficient, and $\{1,\ldots,5\}$ for the moment index", def "The notation $a$ denotes the upper-left real entry of the matrix supplied to $\Phi_y$, a complex rotation coefficient, or a basis index in $H(\Lambda)$, according to its local use." (The real block entry is only one use of this notation. The matching proof defines a complex function explicitly, and the moment construction independently reuses the letter as a finite index.)
- run-level `symbol v`: [note, V1.5] symbol table corrected: type "locally bound vector notation", space "$\mathbb R^{307}$, $\mathbb C^{1\times2}$, $\mathbb R^4$, or $\mathbb R^3$, according to the local binding", def "The notation $v$ is locally bound: an auxiliary vector in the lift, the row $N_3-iN_2$, a vector in $\ker X$, or the lower-left block of $W=\left(\begin{smallmatrix}a&v^T\\v&T\end{smallmatrix}\right)$." (The recorded auxiliary-vector meaning is correct for the main theorem but cannot interpret the complex row or kernel vector. These are separate local bindings, not a single vector shared across the arguments.)
- run-level `symbol f_1`: [note, V1.5] symbol table corrected: type "context-dependent column vector or real basis function", space "$\mathbb C^3$ in the realification definition; a real-valued function on $\mathbb R$ in the moment-matrix basis", def "In $F=(f_1,f_2)\in\mathbb C^{3\times2}$, $f_1$ is the first column; in $(f_1,\ldots,f_5)=(1,\cos\theta,\sin\theta,\cos2\theta,\sin2\theta)$, $f_1=1$." (The entry records only the complex column. The later moment-matrix calculation explicitly reuses the name for the constant real basis function; this is local notation, not a change to the realification operation.)
- run-level `symbol f_2`: [note, V1.5] symbol table corrected: type "context-dependent column vector or real basis function", space "$\mathbb C^3$ in the realification definition; a real-valued function on $\mathbb R$ in the moment-matrix basis", def "In $F=(f_1,f_2)\in\mathbb C^{3\times2}$, $f_2$ is the second column; in $(f_1,\ldots,f_5)=(1,\cos\theta,\sin\theta,\cos2\theta,\sin2\theta)$, $f_2=\cos\theta$." (The original entry correctly describes the realification column but omits the explicit later reuse as the real cosine basis function. The listed Gram and matching uses retain the complex-column meaning.)
- run-level `symbol H`: [note, V1.5] symbol table corrected: type "matrix, with notation overloaded between a complex pairing argument and a real symmetric moment matrix", space "$\mathbb C^{3\times2}$ for the pairing argument $H$; $\Sym^{100}$ for $H(\Lambda)$", def "In the weighted pairing, $H\in\mathbb C^{3\times2}$ is the second argument. The moment matrix is defined by $H(\Lambda)_{(i,a),(j,b)}=\Lambda\bigl(f_a f_b(L_\theta)_{ij}\bigr)$, where $(f_1,\ldots,f_5)=(1,\cos\theta,\sin\theta,\cos2\theta,\sin2\theta)$, $1\leq i,j\leq20$, and $1\leq a,b\leq5$." (The entry covers only the complex pairing argument and omits the later real symmetric moment matrix. These meanings are distinguished by the notation $H$ versus $H(\Lambda)$.)
- run-level `symbol C(\theta)`: [note, V1.5] symbol table corrected: def "For $S\in\mathbb S^3$ and $z\in\mathbb R^3$ satisfying $(z_1,z_2)\ne(0,0)$, a chosen matrix whose entries are trigonometric polynomials of degree at most two such that, for all $\theta,\eta,\xi\in\mathbb R$, $\widetilde C(\theta)\widetilde C(\theta)^T=Q(z)$ and $\langle F_\theta(\eta,\xi),C(\theta)\rangle_S=\operatorname{tr}\bigl(SQ(Y_\theta(\eta,\xi),z)\bigr)$." (The recorded degree bound and lemma reference omit the Gram and pairing identities that characterize the chosen matching matrix. The paper permits dependence on both matching parameters and asserts existence rather than uniqueness.)
- run-level `symbol b`: [note, V1.5] symbol table corrected: type "local complex scalar function or moment index", space "$\mathbb C$ for the rotation coefficient and $\{1,\ldots,5\}$ for the moment index", def "For the rotation, $\overline b=gh(1-\kappa)/\delta$ when $\delta>0$, and $b=0$ when $\delta=0$; in the moment matrix, $b$ indexes the five real basis functions." (The entry omits the explicit definition of the complex function and its later reuse as a moment index. These meanings are distinct and locally settled.)
- note on `def:complex-trigonometric-polynomials`: pinned reading: The linear combination is finite, with coefficients in $\mathbb C$ independent of $\theta$ and indices $\ell\in\mathbb Z$ satisfying $-j\leq\ell\leq j$. (This is the standard trigonometric-polynomial convention, also used in Lemma~\ref{lem:matching}, where the frequency-reduction calculation expands in integer powers of $w=e^{i\theta}$.)
- note on `def:moment-matrix`: pinned reading: In the moment-matrix definition, $(f_1,\ldots,f_5)=(1,\cos\theta,\sin\theta,\cos2\theta,\sin2\theta)$ are real functions and $H(\Lambda)\in\mathbb S^{100}$ is indexed by $(i,a)$ with $1\leq i\leq20$ and $1\leq a\leq5$. (The sentence beginning ``Indeed, set'' explicitly assigns the five real functions and the real symmetric matrix space before giving its entries.)
- note on `symbol a`: symbol table corrected: type "local scalar or moment index", space "$\mathbb R$ for the block scalar, $\mathbb C$ for the rotation coefficient, and $\{1,\ldots,5\}$ for the moment index", def "The notation $a$ denotes the upper-left real entry of the matrix supplied to $\Phi_y$, a complex rotation coefficient, or a basis index in $H(\Lambda)$, according to its local use." (The real block entry is only one use of this notation. The matching proof defines a complex function explicitly, and the moment construction independently reuses the letter as a finite index.)
- note on `symbol b`: symbol table corrected: type "local complex scalar function or moment index", space "$\mathbb C$ for the rotation coefficient and $\{1,\ldots,5\}$ for the moment index", def "For the rotation, $\overline b=gh(1-\kappa)/\delta$ when $\delta>0$, and $b=0$ when $\delta=0$; in the moment matrix, $b$ indexes the five real basis functions." (The entry omits the explicit definition of the complex function and its later reuse as a moment index. These meanings are distinct and locally settled.)
- note on `symbol C(\theta)`: symbol table corrected: def "For $S\in\mathbb S^3$ and $z\in\mathbb R^3$ satisfying $(z_1,z_2)\ne(0,0)$, a chosen matrix whose entries are trigonometric polynomials of degree at most two such that, for all $\theta,\eta,\xi\in\mathbb R$, $\widetilde C(\theta)\widetilde C(\theta)^T=Q(z)$ and $\langle F_\theta(\eta,\xi),C(\theta)\rangle_S=\operatorname{tr}\bigl(SQ(Y_\theta(\eta,\xi),z)\bigr)$." (The recorded degree bound and lemma reference omit the Gram and pairing identities that characterize the chosen matching matrix. The paper permits dependence on both matching parameters and asserts existence rather than uniqueness.)
- note on `symbol e`: symbol table corrected: def "A direction satisfying $p(e)>0$ in the general closed-cone convention, specialized for the polynomial on $\mathcal V$ in \eqref{eq:p} to $e=(I_4,I_4,0)$." (The recorded entry retains only the generic introductory direction. The paper subsequently fixes the particular direction $(I_4,I_4,0)$, which is the meaning used throughout the cone construction and its results.)
- note on `symbol f_1`: symbol table corrected: type "context-dependent column vector or real basis function", space "$\mathbb C^3$ in the realification definition; a real-valued function on $\mathbb R$ in the moment-matrix basis", def "In $F=(f_1,f_2)\in\mathbb C^{3\times2}$, $f_1$ is the first column; in $(f_1,\ldots,f_5)=(1,\cos\theta,\sin\theta,\cos2\theta,\sin2\theta)$, $f_1=1$." (The entry records only the complex column. The later moment-matrix calculation explicitly reuses the name for the constant real basis function; this is local notation, not a change to the realification operation.)
- note on `symbol f_2`: symbol table corrected: type "context-dependent column vector or real basis function", space "$\mathbb C^3$ in the realification definition; a real-valued function on $\mathbb R$ in the moment-matrix basis", def "In $F=(f_1,f_2)\in\mathbb C^{3\times2}$, $f_2$ is the second column; in $(f_1,\ldots,f_5)=(1,\cos\theta,\sin\theta,\cos2\theta,\sin2\theta)$, $f_2=\cos\theta$." (The original entry correctly describes the realification column but omits the explicit later reuse as the real cosine basis function. The listed Gram and matching uses retain the complex-column meaning.)
- note on `symbol H`: symbol table corrected: type "matrix, with notation overloaded between a complex pairing argument and a real symmetric moment matrix", space "$\mathbb C^{3\times2}$ for the pairing argument $H$; $\Sym^{100}$ for $H(\Lambda)$", def "In the weighted pairing, $H\in\mathbb C^{3\times2}$ is the second argument. The moment matrix is defined by $H(\Lambda)_{(i,a),(j,b)}=\Lambda\bigl(f_a f_b(L_\theta)_{ij}\bigr)$, where $(f_1,\ldots,f_5)=(1,\cos\theta,\sin\theta,\cos2\theta,\sin2\theta)$, $1\leq i,j\leq20$, and $1\leq a,b\leq5$." (The entry covers only the complex pairing argument and omits the later real symmetric moment matrix. These meanings are distinguished by the notation $H$ versus $H(\Lambda)$.)
- note on `symbol p`: symbol table corrected: def "Initially $p$ is a homogeneous real polynomial with $p(e)>0$; on $\mathcal V=\Sym^4\times\Sym^4\times\mathbb R^3$ the paper defines $p(X,Z,y)=\det\!\left((\det X)Z-\Phi_y(\adj X)\right)$, with $e=(I_4,I_4,0)$." (The recorded definition retains only the generic introductory polynomial and omits the determinant formula that defines the particular cone. The generic convention precedes the explicit specialization.)
- note on `symbol Q`: symbol table corrected: def "$Q(y)=\begin{pmatrix}y_1^2+y_2^2&-y_1y_2&-y_1y_3\\-y_1y_2&y_2^2+y_3^2&-y_2y_3\\-y_1y_3&-y_2y_3&y_3^2+y_1^2\end{pmatrix}$." (The recorded definition only points to an equation instead of recording its defining entries. The later two-argument notation extends the notation to the explicitly defined polarization; it does not replace the original quadratic map.)
- note on `symbol t`: symbol table corrected: type "real scalar or real coefficient vector, according to the local notation", space "$\mathbb R$ for the polynomial argument and scalar tests; $\mathbb R^{100}$ for the moment-matrix coefficient vector", def "$t$ is the scalar argument in $p(te-x)$; in the moment-matrix calculation it is the vector with entries $t_{i,a}$ defined by $q_i=\sum_a t_{i,a}f_a$; in the range-condition argument it is an arbitrary real scalar in $D=t vv^T$." (The scalar-only entry misses the 100-dimensional coefficient vector used in the moment-matrix calculation and the later independent scalar test. The paper distinguishes these roles locally.)
- note on `symbol U(\theta)`: symbol table corrected: def "$U(\theta)=\frac1{\sqrt2}\begin{pmatrix}-w^{-1}&-w\\sw^{-2}&sw^2\\cw^{-2}&-cw^2\end{pmatrix}$." (The recorded definition identifies only its role as a coefficient; the paper defines a specific matrix whose entries determine the subsequent calculations.)
- note on `symbol v`: symbol table corrected: type "locally bound vector notation", space "$\mathbb R^{307}$, $\mathbb C^{1\times2}$, $\mathbb R^4$, or $\mathbb R^3$, according to the local binding", def "The notation $v$ is locally bound: an auxiliary vector in the lift, the row $N_3-iN_2$, a vector in $\ker X$, or the lower-left block of $W=\left(\begin{smallmatrix}a&v^T\\v&T\end{smallmatrix}\right)$." (The recorded auxiliary-vector meaning is correct for the main theorem but cannot interpret the complex row or kernel vector. These are separate local bindings, not a single vector shared across the arguments.)

### V1 lint warnings

- prop:lift: prop:lift references \ref{lem:slice} (lem:slice) but `depends_on` lacks ass:slice-positive-definite; V1.5 must confirm whether the paper assumes it or merely mentions it
- prop:lift: prop:lift references \ref{lem:matching} (lem:matching) but `depends_on` lacks ass:matching; V1.5 must confirm whether the paper assumes it or merely mentions it

### Parser warnings

- sections/lift.tex:68: untitled \begin{proof} bound to prop:lift by proximity (it is the nearest preceding proof-less result, with only a short passage in between); check the binding

## Lean evidence

- build of the run barrel: **ok**
- source scan (sorry / admit / axiom): clean

| declaration | axioms |
| --- | --- |
| `Papers.OaiExactSemidefiniteLift.exact_semidefinite_lift` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiExactSemidefiniteLift.gram_identity` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiExactSemidefiniteLift.slice_equivalence` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiExactSemidefiniteLift.matching_exists` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiExactSemidefiniteLift.lift_equivalence` | clean — `propext`, `Classical.choice`, `Quot.sound` |

## Inputs

| artifact | status |
| --- | --- |
| `discovery/v1_scope.json` | present (5 environment(s)) |
| `discovery/v1_5_review.json` | present (verdict PASS) |
| `formalization/crosswalk_full.json` | present (196 object(s)) |
| `graph.json` | present (197 node(s)) |
| Lean evidence | collected (build ok, 0 scan issue(s), 196 declaration(s)) |

## Annotated paper

Annotated paper: `annotated/main.tex` (28 annotation(s), 0 unlocated; index `annotated/ANNOTATIONS.md`); PDF: `annotated/main.pdf`
