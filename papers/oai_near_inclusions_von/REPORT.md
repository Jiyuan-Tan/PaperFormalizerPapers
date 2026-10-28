# Correctness report — oai_near_inclusions_von

**Verdict: NO ERROR FOUND**

**Paper: MINOR ISSUES — no main result is shown false or weakened**

Minor:

- Theorem 1.1: condition added (bookkeeping or a pinned reading)
- Proposition 3.1: condition added (bookkeeping or a pinned reading)
- `def:matrix-reps`: ambiguous; a reading was pinned
- `H`: notation ambiguous; a reading was pinned
- `M`: notation ambiguous; a reading was pinned
- `N`: notation ambiguous; a reading was pinned
- `\varepsilon_0`: notation ambiguous; a reading was pinned
- `H_n`: notation ambiguous; a reading was pinned
- `M_n`: notation ambiguous; a reading was pinned
- `N_n`: notation ambiguous; a reading was pinned
- `\delta_x`: notation ambiguous; a reading was pinned
- `\pi_z`: notation ambiguous; a reading was pinned
- `A_k(g)`: notation ambiguous; a reading was pinned
- `c_k`: notation ambiguous; a reading was pinned
- `D`: notation ambiguous; a reading was pinned
- `\omega_n`: notation ambiguous; a reading was pinned
- `U_n`: notation ambiguous; a reading was pinned
- `V_n`: notation ambiguous; a reading was pinned
- `\nu_n`: notation ambiguous; a reading was pinned
- `\widehat U_n`: notation ambiguous; a reading was pinned
- `\widehat V_n`: notation ambiguous; a reading was pinned
- `E_{1n}`: notation ambiguous; a reading was pinned
- `E_{2n}`: notation ambiguous; a reading was pinned
- `E_n`: notation ambiguous; a reading was pinned
- `\widetilde R_{1n}`: notation ambiguous; a reading was pinned
- `\widetilde R_{2n}`: notation ambiguous; a reading was pinned
- `\mathcal A_{1n}`: notation ambiguous; a reading was pinned
- `\mathcal A_{2n}`: notation ambiguous; a reading was pinned
- `T_{in}`: notation ambiguous; a reading was pinned
- `\widehat R_{1n}`: notation ambiguous; a reading was pinned
- `\widehat R_{2n}`: notation ambiguous; a reading was pinned
- `L_n`: notation ambiguous; a reading was pinned
- `a_n`: notation ambiguous; a reading was pinned
- `b_n`: notation ambiguous; a reading was pinned
- `f_n`: notation ambiguous; a reading was pinned
- `W_n`: notation ambiguous; a reading was pinned

5 result(s) of the paper were examined. None was found wrong as printed. In Lean: 5 proved, 0 taken from the literature as cited, 0 not certified, 0 not formalized.

## What was wrong and what was done

No error was found in the results examined.

## Clarifications (not errors)

Nothing in this section is an error of the paper. Each item is something the paper determines but does not say, made explicit so that the statements can be read, and formalized, in one way.

**How a statement is read.**

- **Theorem 1.1.** For every $g\in F$, both sums defining $a(g)$ and $b(g)$ run over $k\in\mathbb Z$ and converge absolutely in operator norm.

**Notation.**

- $H$: $H$ is the common complex Hilbert space on which $M$ and $N$ act. In Theorem~\ref{thm:main}, Proposition~\ref{prop:near}: In the algebra construction, $H=S\otimes L$, where $G=F\times F$, $S=\ell^2(G)$ and $L=K\otimes K\otimes D$.
- $M$: $M\subseteq\mathcal B(H)$ is a von Neumann algebra with identity $I_H$, serving as the source argument of $\gamma(M,N)$. In Theorem~\ref{thm:main}, Proposition~\ref{prop:near}: In the algebra construction, $M=W\bigl(\lambda(G)''\otimes I_L\bigr)W^*$; here $\lambda(G)''\otimes I_L$ consists of all $X\otimes I_L$ with $X\in\lambda(G)''$.
- $N$: $N\subseteq\mathcal B(H)$ is a von Neumann algebra with identity $I_H$, serving as the target argument of $\gamma(M,N)$. In Theorem~\ref{thm:main}, Proposition~\ref{prop:near}: In the algebra construction, $N=\bigl(\rho(G)\otimes I_L\bigr)'$, the commutant of the amplified right regular representation.
- $\varepsilon_0$: The constant $\varepsilon_0>0$ is independent of $n$ and of the implementing unitary $u$; its lower-bound property holds for all sufficiently large $n$.
- $H_n$: $(H_n)$ is a sequence of complex Hilbert spaces. In Lemma~\ref{lem:corner}: $H_n$ is arbitrary and need not be separable. In Theorem~\ref{thm:main}: $H_n$ is separable and is realized as $K\otimes K\otimes K\otimes K\otimes\mathbb C^n$ under $S=K\otimes K$.
- $M_n$: The sequence $M_n$ is indexed by integers $n\geq3$.
- $N_n$: The sequence $N_n$ is indexed by integers $n\geq3$.
- $\delta_x$: $\delta_x$ denotes the standard basis vector indexed by $x$ in the ambient group Hilbert space: $K=\ell^2(F)$ when $x\in F$, and $S=\ell^2(G)$ when $x\in G$.
- $\pi_z$: $\pi_z:F\to\mathcal B(K)$ is a unitary representation for each $z\in\mathbb T=\{z\in\mathbb C:|z|=1\}$.
- $A_k(g)$: The operators $A_k(g)\in\mathcal B(K)$ are indexed by $k\in\mathbb Z$ and $g\in F$ and are the Laurent coefficients in $\pi_z(g)=\sum_{k\in\mathbb Z}z^kA_k(g)$ for $z\in\mathbb T$.
- $c_k$: The sequence is indexed by all $k\in\mathbb Z$ and is defined by $c_k=\mathbf1_{\{k=0\}}+2t^{|k|}/(1-t)$, with $t=1/2$.
- $D$: $D$ is the arbitrary nonzero finite-dimensional complex Hilbert space carrying the input unitaries $U,V$. In Theorem~\ref{thm:main}: For each integer $n\geq3$, the construction is applied with $D=\mathbb C^n$.
- $\omega_n$: For each integer $n\geq3$, $\omega_n=e^{2\pi i/n}\in\mathbb T$.
- $U_n$: $U_n$ is defined for every integer $n\geq3$ by $U_ne_j=\omega_n^je_j$ for $0\leq j<n$.
- $V_n$: $V_n$ is defined for every integer $n\geq3$ by $V_ne_j=e_{j+1\bmod n}$ for $0\leq j<n$.
- $\nu_n$: For each integer $n\geq3$, $\nu_n=\|U_nV_n-V_nU_n\|=|\omega_n-1|$ for the clock--shift pair on $\mathbb C^n$.
- $\widehat U_n$: $\widehat U_n$ denotes the first member of a hypothetical pair of commuting unitaries $\widehat U_n,\widehat V_n$ on $\mathbb C^n$, indexed along an infinite subsequence of integers $n\geq3$, satisfying $\|\widehat U_n-U_n\|+\|\widehat V_n-V_n\|\longrightarrow0$ along that subsequence.
- $\widehat V_n$: $\widehat V_n$ denotes a hypothetical unitary on $\mathbb C^n$ indexed by an infinite subsequence of integers $n\geq3$, commuting with $\widehat U_n$, for which $\|\widehat U_n-U_n\|+\|\widehat V_n-V_n\|\longrightarrow0$ along that subsequence.
- $E_{1n}$: $E_{1n}$ is an orthogonal projection on $H_n$ commuting with $E_{2n}$. In Theorem~\ref{thm:main}: $E_{1n}=p_e\otimes I_K\otimes p_e\otimes I_K\otimes I_{\mathbb C^n}$ on $H_n=K\otimes K\otimes K\otimes K\otimes\mathbb C^n$.
- $E_{2n}$: $E_{2n}$ is an orthogonal projection on $H_n$ commuting with $E_{1n}$. In Theorem~\ref{thm:main}: $E_{2n}=I_K\otimes p_e\otimes I_K\otimes p_e\otimes I_{\mathbb C^n}$ on $H_n=K\otimes K\otimes K\otimes K\otimes\mathbb C^n$.
- $E_n$: $E_n=E_{1n}E_{2n}$ is the orthogonal projection onto the intersection of the ranges of the commuting projections $E_{1n}$ and $E_{2n}$. In Theorem~\ref{thm:main}: $E_n=p_e\otimes p_e\otimes p_e\otimes p_e\otimes I_{\mathbb C^n}$ on $H_n=K\otimes K\otimes K\otimes K\otimes\mathbb C^n$, and its range is naturally identified with $\mathbb C^n$.
- $\widetilde R_{1n}$: $\widetilde R_{1n}$ is a unitary on $H_n$ commuting with both $E_{1n}$ and $E_{2n}$, whose restriction to $D_n=E_{1n}E_{2n}H_n$ is $R_{1n}$. In Theorem~\ref{thm:main}: Under $H_n=K\otimes K\otimes K\otimes K\otimes\mathbb C^n$, $\widetilde R_{1n}=I_K\otimes I_K\otimes I_K\otimes I_K\otimes U_n$; under the natural identification $D_n\cong\mathbb C^n$, its restriction is $R_{1n}=U_n$.
- $\widetilde R_{2n}$: $\widetilde R_{2n}$ is a unitary on $H_n$ commuting with both $E_{1n}$ and $E_{2n}$, whose restriction to $D_n=E_{1n}E_{2n}H_n$ is $R_{2n}$. In Theorem~\ref{thm:main}: Under $H_n=K\otimes K\otimes K\otimes K\otimes\mathbb C^n$, $\widetilde R_{2n}=I_K\otimes I_K\otimes I_K\otimes I_K\otimes V_n$; under the natural identification $D_n\cong\mathbb C^n$, its restriction is $R_{2n}=V_n$.
- $\mathcal A_{1n}$: $\mathcal A_{1n}\subset\mathcal B(H_n)$ is a unital von Neumann algebra commuting with $\mathcal A_{2n}$. In Theorem~\ref{thm:main}: On the hypothetical infinite subsequence admitting the implementing unitaries $u_n$ with $\|u_n-I\|\to0$, $\mathcal A_{1n}$ is the von Neumann algebra generated by $\{\Sigma_n(g,e):g\in F\}$.
- $\mathcal A_{2n}$: $\mathcal A_{2n}\subset\mathcal B(H_n)$ is a unital von Neumann algebra commuting with $\mathcal A_{1n}$. In Theorem~\ref{thm:main}: On the hypothetical infinite subsequence admitting the implementing unitaries $u_n$ with $\|u_n-I\|\to0$, $\mathcal A_{2n}$ is the von Neumann algebra generated by $\{\Sigma_n(e,g):g\in F\}$.
- $T_{in}$: For $i\in\{1,2\}$, $T_{in}\in\mathcal A_{in}$ and $\|T_{in}-E_{in}\widetilde R_{in}\|\longrightarrow0$ as $n\to\infty$ along the sequence under consideration. In Theorem~\ref{thm:main}: On the hypothetical infinite subsequence admitting $u_nM_nu_n^*\subset N_n$ with $\|u_n-I\|\to0$, choose a weak operator cluster point $B_{in}$ of $\Sigma_n(g_{ij})$ as $j\to\infty$ and set $T_{in}=t^{-1}B_{in}$, where $g_{1j}=(s_j,e)$ and $g_{2j}=(e,s_j)$.
- $\widehat R_{1n}$: $\widehat R_{1n}$ is chosen for all sufficiently large $n$ as a unitary on $D_n$, commuting with $\widehat R_{2n}$, with $\|\widehat R_{1n}-R_{1n}\|\longrightarrow0$.
- $\widehat R_{2n}$: $\widehat R_{2n}$ is chosen for all sufficiently large $n$ as a unitary on $D_n$, commuting with $\widehat R_{1n}$, with $\|\widehat R_{2n}-R_{2n}\|\longrightarrow0$.
- $L_n$: For each integer $n\geq3$, $L_n=K\otimes K\otimes\mathbb C^n$ is the separable Hilbert space obtained by substituting the clock--shift pair into the construction.
- $a_n$: For each integer $n\geq3$, $a_n(g)=\sum_{k\in\mathbb Z}A_k(g)\otimes I_K\otimes U_n^k$ for $g\in F$, with the series converging absolutely in norm.
- $b_n$: For each integer $n\geq3$, $b_n:F\to\mathcal B(L_n)$ is given by $b_n(g)=\sum_{k\in\mathbb Z}I_K\otimes A_k(g)\otimes V_n^k$, where $L_n=K\otimes K\otimes\mathbb C^n$.
- $f_n$: For each integer $n\geq3$, $f_n(x)=a_n(x_1)b_n(x_2)$ for $x=(x_1,x_2)\in G$, using the construction with $D=\mathbb C^n$ and inputs $U_n,V_n$.
- $W_n$: For each integer $n\geq3$, $W_n$ is the diagonal unitary obtained from $W$ by taking $D=\mathbb C^n$, $U=U_n$, and $V=V_n$.

## What was proved in Lean, and what was not

A result is proved in Lean when a Lean declaration reviewed as stating it has a complete proof using no axiom beyond the standard ones. For a corrected result, the corrected statement is the one formalized.

| Result | Formal status | Lean declaration | Axioms |
| --- | --- | --- | --- |
| Theorem 1.1 | proved in Lean, under 1 condition(s) made explicit | `Papers.OaiNearInclusionsVon.near_inclusion_not_implemented_by_small_unitaries` (`TMain.lean:43`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Proposition 2.1 | proved in Lean | `Papers.OaiNearInclusionsVon.circle_family_exists` (`TCircle.lean:22`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Proposition 3.1 | proved in Lean, under 1 condition(s) made explicit | `Papers.OaiNearInclusionsVon.near_inclusion_bound` (`TNear.lean:28`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 4.1 | proved in Lean | `Papers.OaiNearInclusionsVon.clock_shift_not_near_commuting` (`Helpers/Clock.lean:554`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 4.2 | proved in Lean | `Papers.OaiNearInclusionsVon.corner_commuting_approximants` (`Helpers/CornerFinalization.lean:225`) | the standard ones only (propext, Classical.choice, Quot.sound) |

The Lean development builds; it contains no `sorry`, `admit` or added axiom.

## The corrected paper

`bundle/corrected_paper/` holds the paper as it reads after the corrections, as plain source in the author's own class and layout, compiled to `bundle/corrected_paper/main.pdf` (12 pages). `bundle/MATCH.md` sets each result beside its Lean declaration; `bundle/lean/` holds the Lean code.

The mechanical checks leave nothing open.

# Technical appendix

The records behind the report above, by the run's own identifiers.

- paper: `main.tex` (source sha256 `93ac1e2036d95f8c87223b62f00146728db4908c64504b4e1548f86642216e65`)
- stage completed: `V6`
- results in scope: 5

| bucket | count |
| --- | --- |
| verified | 3 |
| verified_with_bookkeeping | 2 |
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
| source | `sections/introduction.tex:49-61` (`theorem`, label `thm:main`) |
| statement | \label{thm:main} There exist $\varepsilon_0>0$, separable complex Hilbert spaces $H_n$, and von Neumann algebras $M_n,N_n\subseteq\mathcal B(H_n)$ with common identity $I_{H_n}$ such that \[ \gamma(M_n,N_n)\longrightarrow 0, \] but, for all sufficiently large $n$, every unitary $u\in\mathcal B(H_n)$ satisfying $uM_nu^*\subseteq N_n$ obeys \[ \\|u-I_{H_n}\\|\geq\varepsilon_0. \] |
| Lean | `TMain.lean:43` — `Papers.OaiNearInclusionsVon.near_inclusion_not_implemented_by_small_unitaries` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | `ass:pin-1` |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 2. `prop:circle`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `sections/circle.tex:18-36` (`proposition`, label `prop:circle`) |
| statement | \label{prop:circle} There are unitary representations $\pi_z:F\to\B(K)$, indexed by $z\in\mathbb T$, and operators $A_k(g)\in\B(K)$, indexed by $k\in\mathbb Z$ and $g\in F$, such that \begin{align} \pi_z(g)&=\sum_{k\in\mathbb Z}z^kA_k(g), &\sup_{g\in F}\\|A_k(g)\\|&\leq c_k, &c_k&=\mathbf 1_{\{k=0\}}+\frac{2t^{\|k\|}}{1-t}, \label{eq:fourier}\\ \pi_z(s_j)&\xrightarrow[j\to\infty]{\WOT}tzp_e. \label{eq:circle-limit} \end{align} The series in \eqref{eq:fourier} converges absolutely in operator norm, uniformly in $g$ and $z$, and \begin{equation}\label{eq:moments} S_0:=\sum_{k\in\mathbb Z}c_k<\infty, \qquad S_1:=\sum_{k\in\mathbb Z}\|k\|c_k<\infty. \end{equation} |
| Lean | `TCircle.lean:22` — `Papers.OaiNearInclusionsVon.circle_family_exists` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 3. `prop:near`

| field | value |
| --- | --- |
| bucket | `verified_with_bookkeeping` |
| source | `sections/near.tex:67-82` (`proposition`, label `prop:near`) |
| statement | \label{prop:near} For the algebras in \eqref{eq:algebras}, \begin{equation}\label{eq:near-bound} \gamma(M,N)\leq C\\|UV-VU\\|, \qquad C:=\sum_{k,m,p,h\in\mathbb Z} c_kc_mc_pc_h\|m-p\|\,\|h\|<\infty. \end{equation} Moreover, for every $g\in G$, \begin{equation}\label{eq:group-bound} \bigl\\|W(\lambda(g)\otimes I_L)W^* -\lambda(g)\otimes f(g)\bigr\\| \leq C\\|UV-VU\\|. \end{equation} The constant is independent of $D,U,V$. |
| appended hypothesis list | ass:near-unitary-pair |
| Lean | `TNear.lean:28` — `Papers.OaiNearInclusionsVon.near_inclusion_bound` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | `ass:pin-1` |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 4. `lem:clock`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `sections/obstruction.tex:13-26` (`lemma`, label `lem:clock`) |
| statement | \label{lem:clock} For $n\geq3$, let $U_n,V_n$ be the unitaries on $\mathbb C^n$ given by \begin{equation}\label{eq:clock-shift} U_ne_j=\omega_n^je_j,\qquad V_ne_j=e_{j+1\bmod n},\qquad \omega_n=e^{2\pi i/n}\quad(0\leq j<n). \end{equation} Then $\nu_n:=\\|U_nV_n-V_nU_n\\|=\|\omega_n-1\|\to0$. There is no infinite subsequence along which commuting unitaries $\widehat U_n,\widehat V_n$ on $\mathbb C^n$ satisfy \[ \\|\widehat U_n-U_n\\|+\\|\widehat V_n-V_n\\|\longrightarrow0. \] |
| appended hypothesis list | ass:clock-index |
| Lean | `Helpers/Clock.lean:554` — `Papers.OaiNearInclusionsVon.clock_shift_not_near_commuting` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 5. `lem:corner`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `sections/obstruction.tex:76-94` (`lemma`, label `lem:corner`) |
| statement | \label{lem:corner} For each $n$, let $E_{1n},E_{2n}$ be commuting projections on a complex Hilbert space $H_n$, with $D_n=E_nH_n$ nonzero and finite-dimensional, where $E_n=E_{1n}E_{2n}$. Let $\widetilde R_{1n},\widetilde R_{2n}$ be unitaries commuting with both projections, and write $R_{in}=\widetilde R_{in}\|_{D_n}$. Suppose $\mathcal A_{1n},\mathcal A_{2n}\subset\B(H_n)$ are commuting unital von Neumann algebras and there are $T_{in}\in\mathcal A_{in}$ such that \begin{equation}\label{eq:corner-hypothesis} \\|T_{in}-E_{in}\widetilde R_{in}\\|\longrightarrow0 \quad(i=1,2). \end{equation} Then, for all sufficiently large $n$, there are commuting unitaries $\widehat R_{1n},\widehat R_{2n}$ on $D_n$ with \[ \\|\widehat R_{in}-R_{in}\\|\longrightarrow0\quad(i=1,2). \] |
| appended hypothesis list | ass:corner-projections, ass:corner-dimension, ass:corner-unitaries, ass:corner-algebras, ass:corner-approximation |
| Lean | `Helpers/CornerFinalization.lean:225` — `Papers.OaiNearInclusionsVon.corner_commuting_approximants` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

## Corrected version

2 of 5 result(s) differ from the version you provided — 0 repaired, 0 with the proof completed (no error), 2 only with a side condition or reading made explicit; the others are as printed. The Lean formalization is of the corrected version.

### `thm:main` (`sections/introduction.tex:49-61`)

- as printed: \label{thm:main} There exist $\varepsilon_0>0$, separable complex Hilbert spaces $H_n$, and von Neumann algebras $M_n,N_n\subseteq\mathcal B(H_n)$ with common identity $I_{H_n}$ such that \[ \gamma(M_n,N_n)\longrightarrow 0, \] but, for all sufficiently large $n$, every unitary $u\in\mathcal B(H_n)$ satisfying $uM_nu^*\subseteq N_n$ obeys \[ \|u-I_{H_n}\|\geq\varepsilon_0. \]
- corrected: statement unchanged
- no error: only a side condition or reading the referee made explicit (see below)
- side condition added by the confirming referee `ass:pin-1`: For every $g\in F$, both sums defining $a(g)$ and $b(g)$ run over $k\in\mathbb Z$ and converge absolutely in operator norm. — pins reading of def:matrix-reps: Proposition~\ref{prop:circle} indexes $A_k(g)$ by $k\in\mathbb Z$; immediately after \eqref{eq:matrix-reps}, the paper states that the series converge absolutely in norm.

### `prop:near` (`sections/near.tex:67-82`)

- as printed: \label{prop:near} For the algebras in \eqref{eq:algebras}, \begin{equation}\label{eq:near-bound} \gamma(M,N)\leq C\|UV-VU\|, \qquad C:=\sum_{k,m,p,h\in\mathbb Z} c_kc_mc_pc_h|m-p|\,|h|<\infty. \end{equation} Moreover, for every $g\in G$, \begin{equation}\label{eq:group-bound} \bigl\|W(\lambda(g)\otimes I_L)W^* -\lambda(g)\otimes f(g)\bigr\| \leq C\|UV-VU\|. \end{equation} The constant is independent of $D,U,V$.
- corrected: statement unchanged
- no error: only a side condition or reading the referee made explicit (see below)
- side condition added by the confirming referee `ass:pin-1`: For every $g\in F$, both sums defining $a(g)$ and $b(g)$ run over $k\in\mathbb Z$ and converge absolutely in operator norm. — pins reading of def:matrix-reps: Proposition~\ref{prop:circle} indexes $A_k(g)$ by $k\in\mathbb Z$; immediately after \eqref{eq:matrix-reps}, the paper states that the series converge absolutely in norm.

## Suggestions to the authors

Not errors: readings the paper determines but does not state, and side conditions the proofs use silently.

- clarification (`ass:pin-1`, used by `thm:main`): For every $g\in F$, both sums defining $a(g)$ and $b(g)$ run over $k\in\mathbb Z$ and converge absolutely in operator norm. — pins reading of def:matrix-reps: Proposition~\ref{prop:circle} indexes $A_k(g)$ by $k\in\mathbb Z$; immediately after \eqref{eq:matrix-reps}, the paper states that the series converge absolutely in norm.
- `def:matrix-reps`: pinned reading: For every $g\in F$, both sums defining $a(g)$ and $b(g)$ run over $k\in\mathbb Z$ and converge absolutely in operator norm. (Proposition~\ref{prop:circle} indexes $A_k(g)$ by $k\in\mathbb Z$; immediately after \eqref{eq:matrix-reps}, the paper states that the series converge absolutely in norm.)
- reading of the symbol `H`: $H$ is the common complex Hilbert space on which $M$ and $N$ act. In Theorem~\ref{thm:main}, Proposition~\ref{prop:near}: In the algebra construction, $H=S\otimes L$, where $G=F\times F$, $S=\ell^2(G)$ and $L=K\otimes K\otimes D$. — The introduction allows an arbitrary complex Hilbert space. Section~\ref{sec:near} subsequently sets $H=S\otimes L$, with $S=\ell^2(F\times F)$ and $L=K\otimes K\otimes D$; the main sequence applies this construction with $D=\mathbb C^n$.
- reading of the symbol `M`: $M\subseteq\mathcal B(H)$ is a von Neumann algebra with identity $I_H$, serving as the source argument of $\gamma(M,N)$. In Theorem~\ref{thm:main}, Proposition~\ref{prop:near}: In the algebra construction, $M=W\bigl(\lambda(G)''\otimes I_L\bigr)W^*$; here $\lambda(G)''\otimes I_L$ consists of all $X\otimes I_L$ with $X\in\lambda(G)''$. — The introduction defines the gap for general algebras. Equation~\eqref{eq:algebras} specifies the source used in Proposition~\ref{prop:near} and in the construction of the main sequence.
- reading of the symbol `N`: $N\subseteq\mathcal B(H)$ is a von Neumann algebra with identity $I_H$, serving as the target argument of $\gamma(M,N)$. In Theorem~\ref{thm:main}, Proposition~\ref{prop:near}: In the algebra construction, $N=\bigl(\rho(G)\otimes I_L\bigr)'$, the commutant of the amplified right regular representation. — The introduction defines the gap for general algebras. Equation~\eqref{eq:algebras} specifies the target used in Proposition~\ref{prop:near} and in the construction of the main sequence.
- reading of the symbol `\varepsilon_0`: The constant $\varepsilon_0>0$ is independent of $n$ and of the implementing unitary $u$; its lower-bound property holds for all sufficiently large $n$. — The quantifier order and the phrase "for all sufficiently large $n$" in Theorem~\ref{thm:main} specify the uniformity and eventual range of the bound.
- reading of the symbol `H_n`: $(H_n)$ is a sequence of complex Hilbert spaces. In Lemma~\ref{lem:corner}: $H_n$ is arbitrary and need not be separable. In Theorem~\ref{thm:main}: $H_n$ is separable and is realized as $K\otimes K\otimes K\otimes K\otimes\mathbb C^n$ under $S=K\otimes K$. — Lemma~\ref{lem:corner} assumes complex Hilbert spaces without separability; Theorem~\ref{thm:main} requires separability and its proof gives the tensor-product realization.
- reading of the symbol `M_n`: The sequence $M_n$ is indexed by integers $n\geq3$. — The construction preceding \eqref{eq:vanishing-gap} uses the clock--shift pair of Lemma~\ref{lem:clock}, whose index range is $n\geq3$.
- reading of the symbol `N_n`: The sequence $N_n$ is indexed by integers $n\geq3$. — The construction preceding \eqref{eq:vanishing-gap} uses the clock--shift pair of Lemma~\ref{lem:clock}, whose index range is $n\geq3$.
- reading of the symbol `\delta_x`: $\delta_x$ denotes the standard basis vector indexed by $x$ in the ambient group Hilbert space: $K=\ell^2(F)$ when $x\in F$, and $S=\ell^2(G)$ when $x\in G$. — The definition of $K$ explicitly introduces $(\delta_x)_{x\in F}$; after defining $S=\ell^2(G)$, the regular-representation formulas and the definition of $W$ use the same notation for $x\in G$.
- reading of the symbol `\pi_z`: $\pi_z:F\to\mathcal B(K)$ is a unitary representation for each $z\in\mathbb T=\{z\in\mathbb C:\|z\|=1\}$. — Proposition~\ref{prop:circle} specifies the index $z\in\mathbb T$; equation~\eqref{eq:circle-twist} supplies the construction.
- reading of the symbol `A_k(g)`: The operators $A_k(g)\in\mathcal B(K)$ are indexed by $k\in\mathbb Z$ and $g\in F$ and are the Laurent coefficients in $\pi_z(g)=\sum_{k\in\mathbb Z}z^kA_k(g)$ for $z\in\mathbb T$. — Proposition~\ref{prop:circle} explicitly gives both index ranges and the expansion, whose absolute operator-norm convergence identifies its coefficients.
- reading of the symbol `c_k`: The sequence is indexed by all $k\in\mathbb Z$ and is defined by $c_k=\mathbf1_{\{k=0\}}+2t^{\|k\|}/(1-t)$, with $t=1/2$. — Proposition~\ref{prop:circle}, equation~\eqref{eq:fourier}, specifies $k\in\mathbb Z$ and the formula; the preceding construction fixes $t=1/2$.
- reading of the symbol `D`: $D$ is the arbitrary nonzero finite-dimensional complex Hilbert space carrying the input unitaries $U,V$. In Theorem~\ref{thm:main}: For each integer $n\geq3$, the construction is applied with $D=\mathbb C^n$. — The opening of Section~\ref{sec:near} specifies a nonzero finite-dimensional Hilbert space; the proof of Theorem~\ref{thm:main} explicitly takes $D=\mathbb C^n$.
- reading of the symbol `\omega_n`: For each integer $n\geq3$, $\omega_n=e^{2\pi i/n}\in\mathbb T$. — The opening sentence and equation~\eqref{eq:clock-shift} of Lemma~\ref{lem:clock} specify the index range and value.
- reading of the symbol `U_n`: $U_n$ is defined for every integer $n\geq3$ by $U_ne_j=\omega_n^je_j$ for $0\leq j<n$. — Lemma~\ref{lem:clock} specifies both index ranges in its opening sentence and equation~\eqref{eq:clock-shift}.
- reading of the symbol `V_n`: $V_n$ is defined for every integer $n\geq3$ by $V_ne_j=e_{j+1\bmod n}$ for $0\leq j<n$. — Lemma~\ref{lem:clock} specifies both index ranges in its opening sentence and equation~\eqref{eq:clock-shift}.
- reading of the symbol `\nu_n`: For each integer $n\geq3$, $\nu_n=\\|U_nV_n-V_nU_n\\|=\|\omega_n-1\|$ for the clock--shift pair on $\mathbb C^n$. — Lemma~\ref{lem:clock} defines this sequence for $n\geq3$; the construction preceding the proof of Theorem~\ref{thm:main} uses the same clock--shift pair.
- reading of the symbol `\widehat U_n`: $\widehat U_n$ denotes the first member of a hypothetical pair of commuting unitaries $\widehat U_n,\widehat V_n$ on $\mathbb C^n$, indexed along an infinite subsequence of integers $n\geq3$, satisfying $\\|\widehat U_n-U_n\\|+\\|\widehat V_n-V_n\\|\longrightarrow0$ along that subsequence. — Lemma~\ref{lem:clock} specifies the infinite subsequence, commutation, spaces, and approximation condition; its proof assumes such approximants for a contradiction.
- reading of the symbol `\widehat V_n`: $\widehat V_n$ denotes a hypothetical unitary on $\mathbb C^n$ indexed by an infinite subsequence of integers $n\geq3$, commuting with $\widehat U_n$, for which $\\|\widehat U_n-U_n\\|+\\|\widehat V_n-V_n\\|\longrightarrow0$ along that subsequence. — Lemma~\ref{lem:clock} excludes such approximants along any infinite subsequence, and its proof assumes their existence along a subsequence for contradiction.
- reading of the symbol `E_{1n}`: $E_{1n}$ is an orthogonal projection on $H_n$ commuting with $E_{2n}$. In Theorem~\ref{thm:main}: $E_{1n}=p_e\otimes I_K\otimes p_e\otimes I_K\otimes I_{\mathbb C^n}$ on $H_n=K\otimes K\otimes K\otimes K\otimes\mathbb C^n$. — Lemma~\ref{lem:corner} introduces the commuting projections; the proof of Theorem~\ref{thm:main} specifies the tensor slots on which they act.
- reading of the symbol `E_{2n}`: $E_{2n}$ is an orthogonal projection on $H_n$ commuting with $E_{1n}$. In Theorem~\ref{thm:main}: $E_{2n}=I_K\otimes p_e\otimes I_K\otimes p_e\otimes I_{\mathbb C^n}$ on $H_n=K\otimes K\otimes K\otimes K\otimes\mathbb C^n$. — Lemma~\ref{lem:corner} introduces the commuting projections; the proof of Theorem~\ref{thm:main} specifies the tensor slots on which they act.
- reading of the symbol `E_n`: $E_n=E_{1n}E_{2n}$ is the orthogonal projection onto the intersection of the ranges of the commuting projections $E_{1n}$ and $E_{2n}$. In Theorem~\ref{thm:main}: $E_n=p_e\otimes p_e\otimes p_e\otimes p_e\otimes I_{\mathbb C^n}$ on $H_n=K\otimes K\otimes K\otimes K\otimes\mathbb C^n$, and its range is naturally identified with $\mathbb C^n$. — Lemma~\ref{lem:corner} defines the product projection; the proof of Theorem~\ref{thm:main} specifies its concrete range.
- reading of the symbol `\widetilde R_{1n}`: $\widetilde R_{1n}$ is a unitary on $H_n$ commuting with both $E_{1n}$ and $E_{2n}$, whose restriction to $D_n=E_{1n}E_{2n}H_n$ is $R_{1n}$. In Theorem~\ref{thm:main}: Under $H_n=K\otimes K\otimes K\otimes K\otimes\mathbb C^n$, $\widetilde R_{1n}=I_K\otimes I_K\otimes I_K\otimes I_K\otimes U_n$; under the natural identification $D_n\cong\mathbb C^n$, its restriction is $R_{1n}=U_n$. — Lemma~\ref{lem:corner} gives the general unitary and restriction; the proof of Theorem~\ref{thm:main} specifies its action on the five tensor factors.
- reading of the symbol `\widetilde R_{2n}`: $\widetilde R_{2n}$ is a unitary on $H_n$ commuting with both $E_{1n}$ and $E_{2n}$, whose restriction to $D_n=E_{1n}E_{2n}H_n$ is $R_{2n}$. In Theorem~\ref{thm:main}: Under $H_n=K\otimes K\otimes K\otimes K\otimes\mathbb C^n$, $\widetilde R_{2n}=I_K\otimes I_K\otimes I_K\otimes I_K\otimes V_n$; under the natural identification $D_n\cong\mathbb C^n$, its restriction is $R_{2n}=V_n$. — Lemma~\ref{lem:corner} gives the general unitary and restriction; the proof of Theorem~\ref{thm:main} specifies its action on the five tensor factors.
- reading of the symbol `\mathcal A_{1n}`: $\mathcal A_{1n}\subset\mathcal B(H_n)$ is a unital von Neumann algebra commuting with $\mathcal A_{2n}$. In Theorem~\ref{thm:main}: On the hypothetical infinite subsequence admitting the implementing unitaries $u_n$ with $\\|u_n-I\\|\to0$, $\mathcal A_{1n}$ is the von Neumann algebra generated by $\{\Sigma_n(g,e):g\in F\}$. — Lemma~\ref{lem:corner} assumes commuting unital von Neumann algebras; the proof of Theorem~\ref{thm:main} defines them using the two factor restrictions of $\Sigma_n$.
- reading of the symbol `\mathcal A_{2n}`: $\mathcal A_{2n}\subset\mathcal B(H_n)$ is a unital von Neumann algebra commuting with $\mathcal A_{1n}$. In Theorem~\ref{thm:main}: On the hypothetical infinite subsequence admitting the implementing unitaries $u_n$ with $\\|u_n-I\\|\to0$, $\mathcal A_{2n}$ is the von Neumann algebra generated by $\{\Sigma_n(e,g):g\in F\}$. — Lemma~\ref{lem:corner} assumes commuting unital von Neumann algebras; the proof of Theorem~\ref{thm:main} defines them using the two factor restrictions of $\Sigma_n$.
- reading of the symbol `T_{in}`: For $i\in\{1,2\}$, $T_{in}\in\mathcal A_{in}$ and $\\|T_{in}-E_{in}\widetilde R_{in}\\|\longrightarrow0$ as $n\to\infty$ along the sequence under consideration. In Theorem~\ref{thm:main}: On the hypothetical infinite subsequence admitting $u_nM_nu_n^*\subset N_n$ with $\\|u_n-I\\|\to0$, choose a weak operator cluster point $B_{in}$ of $\Sigma_n(g_{ij})$ as $j\to\infty$ and set $T_{in}=t^{-1}B_{in}$, where $g_{1j}=(s_j,e)$ and $g_{2j}=(e,s_j)$. — Lemma~\ref{lem:corner} imposes \eqref{eq:corner-hypothesis}; the proof of Theorem~\ref{thm:main} chooses cluster points and sets $T_{in}=t^{-1}B_{in}$.
- reading of the symbol `\widehat R_{1n}`: $\widehat R_{1n}$ is chosen for all sufficiently large $n$ as a unitary on $D_n$, commuting with $\widehat R_{2n}$, with $\\|\widehat R_{1n}-R_{1n}\\|\longrightarrow0$. — The conclusion of Lemma~\ref{lem:corner} specifies both the eventual index range and the norm approximation.
- reading of the symbol `\widehat R_{2n}`: $\widehat R_{2n}$ is chosen for all sufficiently large $n$ as a unitary on $D_n$, commuting with $\widehat R_{1n}$, with $\\|\widehat R_{2n}-R_{2n}\\|\longrightarrow0$. — The conclusion of Lemma~\ref{lem:corner} specifies both the eventual index range and the norm approximation.
- reading of the symbol `L_n`: For each integer $n\geq3$, $L_n=K\otimes K\otimes\mathbb C^n$ is the separable Hilbert space obtained by substituting the clock--shift pair into the construction. — The paragraph preceding \eqref{eq:vanishing-gap} specifies the substitution, the subscripts, and separability; Lemma~\ref{lem:clock} specifies the index range.
- reading of the symbol `a_n`: For each integer $n\geq3$, $a_n(g)=\sum_{k\in\mathbb Z}A_k(g)\otimes I_K\otimes U_n^k$ for $g\in F$, with the series converging absolutely in norm. — Equation \eqref{eq:matrix-reps} defines $a$, and the substitution preceding \eqref{eq:vanishing-gap} uses the clock--shift pair of Lemma~\ref{lem:clock}.
- reading of the symbol `b_n`: For each integer $n\geq3$, $b_n:F\to\mathcal B(L_n)$ is given by $b_n(g)=\sum_{k\in\mathbb Z}I_K\otimes A_k(g)\otimes V_n^k$, where $L_n=K\otimes K\otimes\mathbb C^n$. — The main-theorem proof applies the construction of Section~\ref{sec:near} to the clock--shift pair of Lemma~\ref{lem:clock}, which is defined for $n\geq3$, and assigns subscripts $n$ to the resulting objects.
- reading of the symbol `f_n`: For each integer $n\geq3$, $f_n(x)=a_n(x_1)b_n(x_2)$ for $x=(x_1,x_2)\in G$, using the construction with $D=\mathbb C^n$ and inputs $U_n,V_n$. — The substitution preceding \eqref{eq:vanishing-gap} uses the clock--shift pair of Lemma~\ref{lem:clock}; \eqref{eq:clock-shift} and the definition of $f$ specify the inputs and map.
- reading of the symbol `W_n`: For each integer $n\geq3$, $W_n$ is the diagonal unitary obtained from $W$ by taking $D=\mathbb C^n$, $U=U_n$, and $V=V_n$. — The construction following Lemma~\ref{lem:clock} specifies the clock-shift pair for $n\geq3$, and the proof of Theorem~\ref{thm:main} applies the construction with $D=\mathbb C^n$ and uses subscripts $n$ for the resulting objects.

## Added conditions

| id | where | class | condition |
| --- | --- | --- | --- |
| `ass:pin-1` | `thm:main` | V1.5 bookkeeping | For every $g\in F$, both sums defining $a(g)$ and $b(g)$ run over $k\in\mathbb Z$ and converge absolutely in operator norm. (pins reading of def:matrix-reps: Proposition~\ref{prop:circle} indexes $A_k(g)$ by $k\in\mathbb Z$; immediately after \eqref{eq:matrix-reps}, the paper states that the series converge absolutely in norm.) |
| `ass:pin-1` | `prop:near` | V1.5 bookkeeping | For every $g\in F$, both sums defining $a(g)$ and $b(g)$ run over $k\in\mathbb Z$ and converge absolutely in operator norm. (pins reading of def:matrix-reps: Proposition~\ref{prop:circle} indexes $A_k(g)$ by $k\in\mathbb Z$; immediately after \eqref{eq:matrix-reps}, the paper states that the series converge absolutely in norm.) |

## Conditions assumed

### Cited results

None: no result rests on a theorem imported from the literature.

### Deferred substrate gates

None: every substrate this run needed was built and proved.

## Unresolved / notes

- run-level `def:matrix-reps`: [note, V1.5] pinned reading: For every $g\in F$, both sums defining $a(g)$ and $b(g)$ run over $k\in\mathbb Z$ and converge absolutely in operator norm. (Proposition~\ref{prop:circle} indexes $A_k(g)$ by $k\in\mathbb Z$; immediately after \eqref{eq:matrix-reps}, the paper states that the series converge absolutely in norm.)
- run-level `symbol H_n`: [note, V1.5] symbol table corrected: space "$\text{complex Hilbert spaces}$", def "For each $n$, $H_n$ is a complex Hilbert space." (The recorded space and definition restrict the symbol to the main theorem's separable representation spaces. The corner lemma instead allows arbitrary complex Hilbert spaces; the main theorem supplies a particular separable realization.)
- run-level `symbol M_n`: [note, V1.5] symbol table corrected: def "$M_n=W_n\bigl(\lambda(G)''\otimes I_{L_n}\bigr)W_n^*$, obtained by applying the construction of Section~\ref{sec:near} to $D=\mathbb C^n$ and the clock--shift pair of Lemma~\ref{lem:clock}." (The recorded definition identifies only the source role. The paper specifies the sequence by its conjugated group von Neumann algebra construction and fixes its index range through the clock--shift pair.)
- run-level `symbol N_n`: [note, V1.5] symbol table corrected: def "$N_n=\bigl(\rho(G)\otimes I_{L_n}\bigr)'$, obtained by applying the construction of Section~\ref{sec:near} to $D=\mathbb C^n$ and the clock--shift pair of Lemma~\ref{lem:clock}." (The recorded definition identifies only the target role. The paper defines the target as the commutant of the amplified right regular representation and fixes its index range through the clock--shift pair.)
- run-level `symbol \delta_x`: [note, V1.5] symbol table corrected: space "$K=\ell^2(F)$ for $x\in F$, or $S=\ell^2(G)$ for $x\in G$, according to the ambient space", def "The standard orthonormal basis vector indexed by $x$ in the indicated group Hilbert space." (The recorded entry restricts the notation to $K$ and $x\in F$, whereas the product-group construction also uses it for the standard basis of $S$ indexed by $G$. The ambient Hilbert space resolves the overload.)
- run-level `symbol \pi_z`: [note, V1.5] symbol table corrected: def "$\pi_z(g)=z^{q(g)}D_z\pi(g)D_z^*=(D_zT_gD_z^*)l(g)$, where $q:F\to\mathbb Z$ is the homomorphism taking every generator $s_j$ to $1$, and $D_z\delta_x=z^{-q(x)}\delta_x$." (The recorded definition merely refers to asserted properties. The paper constructs the family by the displayed twist and explicitly restricts its index to the unit circle.)
- note on `def:matrix-reps`: pinned reading: For every $g\in F$, both sums defining $a(g)$ and $b(g)$ run over $k\in\mathbb Z$ and converge absolutely in operator norm. (Proposition~\ref{prop:circle} indexes $A_k(g)$ by $k\in\mathbb Z$; immediately after \eqref{eq:matrix-reps}, the paper states that the series converge absolutely in norm.)
- note on `symbol \delta_x`: symbol table corrected: space "$K=\ell^2(F)$ for $x\in F$, or $S=\ell^2(G)$ for $x\in G$, according to the ambient space", def "The standard orthonormal basis vector indexed by $x$ in the indicated group Hilbert space." (The recorded entry restricts the notation to $K$ and $x\in F$, whereas the product-group construction also uses it for the standard basis of $S$ indexed by $G$. The ambient Hilbert space resolves the overload.)
- note on `symbol \pi_z`: symbol table corrected: def "$\pi_z(g)=z^{q(g)}D_z\pi(g)D_z^*=(D_zT_gD_z^*)l(g)$, where $q:F\to\mathbb Z$ is the homomorphism taking every generator $s_j$ to $1$, and $D_z\delta_x=z^{-q(x)}\delta_x$." (The recorded definition merely refers to asserted properties. The paper constructs the family by the displayed twist and explicitly restricts its index to the unit circle.)
- note on `symbol H_n`: symbol table corrected: space "$\text{complex Hilbert spaces}$", def "For each $n$, $H_n$ is a complex Hilbert space." (The recorded space and definition restrict the symbol to the main theorem's separable representation spaces. The corner lemma instead allows arbitrary complex Hilbert spaces; the main theorem supplies a particular separable realization.)
- note on `symbol M_n`: symbol table corrected: def "$M_n=W_n\bigl(\lambda(G)''\otimes I_{L_n}\bigr)W_n^*$, obtained by applying the construction of Section~\ref{sec:near} to $D=\mathbb C^n$ and the clock--shift pair of Lemma~\ref{lem:clock}." (The recorded definition identifies only the source role. The paper specifies the sequence by its conjugated group von Neumann algebra construction and fixes its index range through the clock--shift pair.)
- note on `symbol N_n`: symbol table corrected: def "$N_n=\bigl(\rho(G)\otimes I_{L_n}\bigr)'$, obtained by applying the construction of Section~\ref{sec:near} to $D=\mathbb C^n$ and the clock--shift pair of Lemma~\ref{lem:clock}." (The recorded definition identifies only the target role. The paper defines the target as the commutant of the amplified right regular representation and fixes its index range through the clock--shift pair.)

### V1 lint warnings

- thm:main: thm:main references \ref{lem:corner} (lem:corner) but `depends_on` lacks ass:corner-projections, ass:corner-dimension, ass:corner-unitaries, ass:corner-algebras, ass:corner-approximation, def:corner-range, def:corner-restrictions; V1.5 must confirm whether the paper assumes it or merely mentions it
- thm:main: thm:main references \ref{lem:clock} (lem:clock) but `depends_on` lacks ass:clock-index, def:clock-pair; V1.5 must confirm whether the paper assumes it or merely mentions it
- prop:circle: the proof of prop:circle cites [Haa1979, Lemma 1.2] (prop:circle/proof/1/1); the transcription reads the citation as a result this paper proves itself and made no cited node for it (The proof constructs the tree vectors, computes their coefficient as $t^{d(x,y)}$, and proves that left multiplication extends to a unitary representation, establishing the cited positive-definiteness here.). paper: "…$g\mapsto t^{\|g\|}$ of Haagerup \cite[Lemma~1.2]{Haa1979}. We give the tree construction before…"

### Parser warnings

- main.tex:9: \input{glyphtounicode} not found (tried glyphtounicode.tex, glyphtounicode relative to . and the source root); skipped (the bundle does not ship it — check that no result lived there)
- main.tex:10: \input{glyphtounicode-cmex} not found (tried glyphtounicode-cmex.tex, glyphtounicode-cmex relative to . and the source root); skipped (the bundle does not ship it — check that no result lived there)

## Lean evidence

- build of the run barrel: **ok**
- source scan (sorry / admit / axiom): clean

| declaration | axioms |
| --- | --- |
| `Papers.OaiNearInclusionsVon.near_inclusion_not_implemented_by_small_unitaries` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiNearInclusionsVon.circle_family_exists` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiNearInclusionsVon.near_inclusion_bound` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiNearInclusionsVon.clock_shift_not_near_commuting` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiNearInclusionsVon.corner_commuting_approximants` | clean — `propext`, `Classical.choice`, `Quot.sound` |

## Inputs

| artifact | status |
| --- | --- |
| `discovery/v1_scope.json` | present (5 environment(s)) |
| `discovery/v1_5_review.json` | present (verdict PASS) |
| `formalization/crosswalk_full.json` | present (473 object(s)) |
| `graph.json` | present (478 node(s)) |
| Lean evidence | collected (build ok, 0 scan issue(s), 5 declaration(s)) |

## Annotated paper

Annotated paper: `annotated/main.tex` (34 annotation(s), 0 unlocated; index `annotated/ANNOTATIONS.md`); PDF: `annotated/main.pdf`
