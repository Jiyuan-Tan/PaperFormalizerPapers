# Correctness report — oai_close_separable_cstar

**Verdict: NO ERROR FOUND**

**Paper: MINOR ISSUES — no main result is shown false or weakened**

Minor:

- `H`: notation ambiguous; a reading was pinned
- `A`: notation ambiguous; a reading was pinned
- `B`: notation ambiguous; a reading was pinned
- `t`: notation ambiguous; a reading was pinned
- `L`: notation ambiguous; a reading was pinned
- `D`: notation ambiguous; a reading was pinned
- `U_n`: notation ambiguous; a reading was pinned
- `p_b`: notation ambiguous; a reading was pinned
- `W`: notation ambiguous; a reading was pinned
- `\sigma`: notation ambiguous; a reading was pinned

10 result(s) of the paper were examined. None was found wrong as printed. In Lean: 10 proved, 0 taken from the literature as cited, 0 not certified, 0 not formalized.

## What was wrong and what was done

No error was found in the results examined.

## Clarifications (not errors)

Nothing in this section is an error of the paper. Each item is something the paper determines but does not say, made explicit so that the statements can be read, and formalized, in one way.

**Notation.**

- $H$: $H$ denotes the common complex Hilbert space on which the algebras under consideration act. In Proposition~\ref{prop:sequences}, Corollary~\ref{cor:obstruction}: $H=\bigoplus_{n\ge1}L$, where $L$ is the nonzero separable Hilbert space carrying $D$. In Theorem~\ref{thm:main}: The constructed witness is $H=\bigoplus_{n\ge1}L$, with $L$ from Section~\ref{sec:inclusions}; in particular, $H$ is separable.
- $A$: $A$ denotes the first $C^*$-algebra in the pair $A,B\subseteq\B(H)$. In Theorem~\ref{thm:main}: $A$ is a unital, norm-separable $C^*$-algebra with identity $\id_H$; the proof constructs $A=\E_D(P_0)$ using the inclusions from Section~\ref{sec:inclusions}.
- $B$: $B$ denotes the second $C^*$-algebra in the pair $A,B\subseteq\B(H)$. In Theorem~\ref{thm:main}: $B$ is a unital, norm-separable $C^*$-algebra with identity $\id_H$; the proof constructs $B=\E_D(P_t)$ using the inclusions from Section~\ref{sec:inclusions}, with $0<t<1$ chosen so that $2c(t)<\varepsilon$.
- $t$: $t$ is a real parameter with $0<t<1$. In Theorem~\ref{thm:main}: Given $\varepsilon>0$, $t$ is chosen sufficiently small that $2c(t)<\varepsilon$, where $c(t)=2(1-\sqrt{1-t^2})+t/(1-t)+t$.
- $L$: $L$ is the complex Hilbert space on which $D$ acts. In Proposition~\ref{prop:sequences}, Corollary~\ref{cor:obstruction}: $L$ is nonzero and separable. In Theorem~\ref{thm:main}, Lemma~\ref{lem:ambient}, Lemma~\ref{lem:good-inclusion}, Lemma~\ref{lem:bad-inclusion}: $L=K\otimes K$, where $K=\ell^2(G)$.
- $D$: $D\subseteq\B(L)$ is the ambient unital $C^*$-algebra, with identity $\id_L$. In Proposition~\ref{prop:sequences}, Corollary~\ref{cor:obstruction}: $D$ is norm-separable and $Z(D)=\C\id_L$. In Theorem~\ref{thm:main}, Lemma~\ref{lem:ambient}, Lemma~\ref{lem:good-inclusion}, Lemma~\ref{lem:bad-inclusion}: $D=C^*(\{\lambda(g)\otimes\id_K,\id_K\otimes\pi_0(g),\id_K\otimes\pi_t(g):g\in G\}\cup\{\id_K\otimes E_{xy}:x,y\in G\})\subseteq\B(K\otimes K)$, where $E_{xy}\delta_z=\mathbf1_{\{z=y\}}\delta_x$.
- $U_n$: $(U_n)_{n\ge1}$ is one sequence of unitaries on $L$ satisfying $U_nDU_n^*=D$ for every $n$, common to every $b\in Q$: for each such $b$ there is a fixed $p_b\in P$ with $\norm{b-U_np_bU_n^*}\to0$. In Proposition~\ref{prop:sequences}: In the conditional conjugacy argument, for a chosen $S$ satisfying $S\E_D(P)S^*=\E_D(Q)$, $U_n:L\to L$ is the restriction of $S$ from the $n$th coordinate to its image coordinate, with both coordinates identified with $L$.
- $p_b$: For the chosen sequence $(U_n)_{n\ge1}$ and each $b\in Q$, $p_b\in P$ is the fixed element $p_b=\lim_{n\to\infty}U_n^*bU_n$ in operator norm, equivalently $\norm{b-U_np_bU_n^*}\to0$; it may depend on $b$ and on the chosen sequence, but not on $n$.
- $W$: $W$ is a unitary operator on $L$. In Corollary~\ref{cor:obstruction}: $W$ satisfies $WPW^*=Q$ in the conditional distance assertion and is not required to normalize $D$. In Lemma~\ref{lem:ambient}, Theorem~\ref{thm:main}: The supplied choice is $W=W_{\pi_t}W_{\pi_0}^*$, where $W_{\pi_a}(\delta_x\otimes v)=\delta_x\otimes\pi_a(x)v$ for $a=0,t$; it satisfies $WP_0W^*=P_t$ and $\norm{W-\id_L}\le c(t)$.
- $\sigma$: $\sigma$ is a unitary representation of $G$ on a nonzero Hilbert space. In Lemma~\ref{lem:bad-inclusion}: $\sigma=\pi_t\otimes\rho\otimes1$ acts on $K^{\otimes3}$, where $1$ is the trivial representation on the last copy of $K$.

## What was proved in Lean, and what was not

A result is proved in Lean when a Lean declaration reviewed as stating it has a complete proof using no axiom beyond the standard ones. For a corrected result, the corrected statement is the one formalized.

| Result | Formal status | Lean declaration | Axioms |
| --- | --- | --- | --- |
| Theorem 1.1 | proved in Lean | `Papers.OaiCloseSeparableCstar.exists_close_not_conjugate` (`TMain.lean:50`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Proposition 2.1 | proved in Lean | `Papers.OaiCloseSeparableCstar.seqAlg_properties` (`TSequences.lean:24`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 2.3 | proved in Lean | `Papers.OaiCloseSeparableCstar.tensorIdentity_invariant` (`Helpers/Invariant.lean:153`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Corollary 2.4 | proved in Lean | `Papers.OaiCloseSeparableCstar.seqAlg_obstruction` (`TObstruction.lean:68`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 3.1 | proved in Lean | `Papers.OaiCloseSeparableCstar.exists_treeRep` (`Helpers/Tree.lean:29`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 4.1 | proved in Lean | `Papers.OaiCloseSeparableCstar.absorption` (`Helpers/LpOperators.lean:55`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 4.2 | proved in Lean | `Papers.OaiCloseSeparableCstar.ambient_properties` (`Helpers/Ambient.lean:117`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 4.3 | proved in Lean | `Papers.OaiCloseSeparableCstar.goodInclusion` (`Helpers/GoodInclusion.lean:488`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 4.4 | proved in Lean | `Papers.OaiCloseSeparableCstar.norm_sum_leftReg_gen_le` (`Helpers/FreeNorm.lean:182`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 4.5 | proved in Lean | `Papers.OaiCloseSeparableCstar.badInclusion` (`Helpers/BadInclusion.lean:182`) | the standard ones only (propext, Classical.choice, Quot.sound) |

The Lean development builds; it contains no `sorry`, `admit` or added axiom.

## The corrected paper

`bundle/corrected_paper/` holds the paper as it reads after the corrections, as plain source in the author's own class and layout, compiled to `bundle/corrected_paper/main.pdf` (10 pages). `bundle/MATCH.md` sets each result beside its Lean declaration; `bundle/lean/` holds the Lean code.

The mechanical checks leave nothing open.

# Technical appendix

The records behind the report above, by the run's own identifiers.

- paper: `main.tex` (source sha256 `e97075df8760d4987bddeb38e43f55b1314b4a2c75b8fa45ab98553ef009715f`)
- stage completed: `5`
- results in scope: 10

| bucket | count |
| --- | --- |
| verified | 10 |
| verified_with_bookkeeping | 0 |
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
| bucket | `verified` |
| source | `main.tex:67-75` (`theorem`, label `thm:main`) |
| statement | \label{thm:main} For every $\varepsilon>0$ there are a separable complex Hilbert space $H$ and unital, norm-separable $C^*$-algebras $A,B\subseteq\B(H)$ with common identity $\id_H$ such that \[ \KK(A,B)<\varepsilon,\qquad A''=B'', \] but no unitary $u\in\B(H)$ satisfies $uAu^*=B$. |
| Lean | `TMain.lean:50` — `Papers.OaiCloseSeparableCstar.exists_close_not_conjugate` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 2. `prop:sequences`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `main.tex:149-174` (`proposition`, label `prop:sequences`) |
| statement | \label{prop:sequences} Let $L$ be a nonzero separable Hilbert space, let $D\subseteq\B(L)$ be a unital norm-separable $C^*$-algebra with $Z(D)=\C\id_L$, and let $P,Q\subseteq D$ be unital $C^*$-subalgebras containing $\id_L$. On $H=\bigoplus_{n\ge1}L$, define \begin{equation}\label{eq:sequence-definition} \E_D(P)=\{(x_n)_{n\ge1}:x_n\in D,\ x_n\to p\in P\text{ in norm}\}, \end{equation} and define $\E_D(Q)$ similarly. Then: \begin{enumerate} \item These are unital norm-separable $C^*$-algebras with common identity, and \begin{equation}\label{eq:distance-equality} \KK(\E_D(P),\E_D(Q))=\KK(P,Q). \end{equation} \item If a unitary conjugates $\E_D(P)$ onto $\E_D(Q)$, there are unitaries $U_n\in\B(L)$ with $U_nDU_n^*=D$ such that, for every $b\in Q$, some $p_b\in P$ satisfies \begin{equation}\label{eq:pointwise-normalizers} \norm{b-U_np_bU_n^*}\longrightarrow0. \end{equation} The same sequence $(U_n)$ works for every $b$. \item The two algebras have the same commutant, and hence the same von Neumann closure. \end{enumerate} |
| appended hypothesis list | ass:sequences-l, ass:sequences-d, ass:sequences-center, ass:sequences-subalgebras |
| Lean | `TSequences.lean:24` — `Papers.OaiCloseSeparableCstar.seqAlg_properties` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 3. `lem:invariant`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `main.tex:257-264` (`lemma`, label `lem:invariant`) |
| statement | \label{lem:invariant} Let $P,Q\subseteq D\subseteq\B(L)$ be unital $C^*$-algebras. The identity in Definition~\ref{def:tensor} is preserved by conjugating $P$ with any unitary normalizing $D$. If $(U_n)$ is a sequence of unitaries in $\B(L)$ satisfying $U_nDU_n^*=D$ and every $b\in Q$ admits the approximation \eqref{eq:pointwise-normalizers}, then the identity for $P$ implies the identity for $Q$. |
| appended hypothesis list | ass:invariant-unital |
| Lean | `Helpers/Invariant.lean:153` — `Papers.OaiCloseSeparableCstar.tensorIdentity_invariant` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 4. cor:obstruction `thm:obstruction`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `main.tex:285-293` (`corollary`, label `cor:obstruction`) |
| statement | \label{cor:obstruction} Under the hypotheses of Proposition~\ref{prop:sequences}, suppose that $P$ has the spatial tensor-norm identity relative to $D$, whereas $Q$ does not. Then $\E_D(P)$ and $\E_D(Q)$ are not spatially conjugate. If $W\in\B(L)$ is unitary and $WPW^*=Q$, then nevertheless \[ \KK(\E_D(P),\E_D(Q))\le2\norm{W-\id_L}. \] |
| appended hypothesis list | ass:sequences-l, ass:sequences-d, ass:sequences-center, ass:sequences-subalgebras, ass:obstruction-tensor-distinction |
| Lean | `TObstruction.lean:68` — `Papers.OaiCloseSeparableCstar.seqAlg_obstruction` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 5. `lem:tree`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `main.tex:328-337` (`lemma`, label `lem:tree`) |
| statement | \label{lem:tree} For every $0<t<1$, there is a unitary representation $\pi_t:G\to\B(K)$ such that, with $r=\sqrt{1-t^2}$, \begin{align} \inner{\pi_t(s_i)\delta_e}{\delta_e}&=t\quad(i\ge1),\label{eq:coefficient}\\ \sup_{g\in G}\norm{\pi_t(g)-\lambda(g)}&\le c(t),\qquad c(t)=2(1-r)+\frac{t}{1-t}+t.\label{eq:uniform} \end{align} In particular, $c(t)\to0$ as $t\downarrow0$. |
| Lean | `Helpers/Tree.lean:29` — `Papers.OaiCloseSeparableCstar.exists_treeRep` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 6. Absorption `lem:absorption`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `main.tex:448-460` (`lemma`, label `lem:absorption`) |
| statement | \label{lem:absorption} Let $\sigma$ be a unitary representation of $G$ on a nonzero Hilbert space $J$. The operator \[ W_\sigma(\delta_x\otimes v)=\delta_x\otimes\sigma(x)v \quad(x\in G,\ v\in J) \] is unitary on $K\otimes J$ and satisfies \begin{equation}\label{eq:absorption} W_\sigma(\lambda(g)\otimes\id_J)W_\sigma^* =\lambda(g)\otimes\sigma(g)\quad(g\in G). \end{equation} |
| appended hypothesis list | ass:absorption-representation |
| Lean | `Helpers/LpOperators.lean:55` — `Papers.OaiCloseSeparableCstar.absorption` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 7. `lem:ambient`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `main.tex:488-497` (`lemma`, label `lem:ambient`) |
| statement | \label{lem:ambient} The algebra $D$ in \eqref{eq:D} has scalar center, and \begin{equation}\label{eq:commutant} D'=\{Y\otimes\id_K:Y\in\lambda(G)'\}. \end{equation} There is a unitary $W\in\B(L)$ such that \begin{equation}\label{eq:close-W} WP_0W^*=P_t,\qquad \norm{W-\id_L}\le c(t). \end{equation} |
| Lean | `Helpers/Ambient.lean:117` — `Papers.OaiCloseSeparableCstar.ambient_properties` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 8. `lem:good-inclusion`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `main.tex:530-532` (`lemma`, label `lem:good-inclusion`) |
| statement | \label{lem:good-inclusion} The inclusion $P_0\subseteq D$ has the spatial tensor-norm identity. |
| Lean | `Helpers/GoodInclusion.lean:488` — `Papers.OaiCloseSeparableCstar.goodInclusion` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 9. `lem:free-norm`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `main.tex:568-573` (`lemma`, label `lem:free-norm`) |
| statement | \label{lem:free-norm} For every positive integer $m$, \begin{equation}\label{eq:free-norm} \norm{\sum_{i=1}^m\lambda(s_i)}\le2\sqrt m. \end{equation} |
| Lean | `Helpers/FreeNorm.lean:182` — `Papers.OaiCloseSeparableCstar.norm_sum_leftReg_gen_le` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 10. `lem:bad-inclusion`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `main.tex:599-602` (`lemma`, label `lem:bad-inclusion`) |
| statement | \label{lem:bad-inclusion} For every $0<t<1$, the inclusion $P_t\subseteq D$ fails the spatial tensor-norm identity. |
| Lean | `Helpers/BadInclusion.lean:182` — `Papers.OaiCloseSeparableCstar.badInclusion` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

## Suggestions to the authors

Not errors: readings the paper determines but does not state, and side conditions the proofs use silently.

- reading of the symbol `H`: $H$ denotes the common complex Hilbert space on which the algebras under consideration act. In Proposition~\ref{prop:sequences}, Corollary~\ref{cor:obstruction}: $H=\bigoplus_{n\ge1}L$, where $L$ is the nonzero separable Hilbert space carrying $D$. In Theorem~\ref{thm:main}: The constructed witness is $H=\bigoplus_{n\ge1}L$, with $L$ from Section~\ref{sec:inclusions}; in particular, $H$ is separable. — The introductory definition allows $C^*$-algebras in $\B(H)$ without a separability restriction. Proposition~\ref{prop:sequences} sets $H=\bigoplus_{n\ge1}L$; Corollary~\ref{cor:obstruction} inherits that construction. The proof of Theorem~\ref{thm:main} uses the same direct sum with the concrete space $L$ from Section~\ref{sec:inclusions}.
- reading of the symbol `A`: $A$ denotes the first $C^*$-algebra in the pair $A,B\subseteq\B(H)$. In Theorem~\ref{thm:main}: $A$ is a unital, norm-separable $C^*$-algebra with identity $\id_H$; the proof constructs $A=\E_D(P_0)$ using the inclusions from Section~\ref{sec:inclusions}. — The introductory definition imposes no unitality or separability requirement. Theorem~\ref{thm:main} imposes these requirements, and its proof explicitly sets $A=\E_D(P_0)$.
- reading of the symbol `B`: $B$ denotes the second $C^*$-algebra in the pair $A,B\subseteq\B(H)$. In Theorem~\ref{thm:main}: $B$ is a unital, norm-separable $C^*$-algebra with identity $\id_H$; the proof constructs $B=\E_D(P_t)$ using the inclusions from Section~\ref{sec:inclusions}, with $0<t<1$ chosen so that $2c(t)<\varepsilon$. — The introductory definition imposes no unitality or separability requirement. Theorem~\ref{thm:main} imposes these requirements, and its proof explicitly sets $B=\E_D(P_t)$ after choosing $0<t<1$ with $2c(t)<\varepsilon$.
- reading of the symbol `t`: $t$ is a real parameter with $0<t<1$. In Theorem~\ref{thm:main}: Given $\varepsilon>0$, $t$ is chosen sufficiently small that $2c(t)<\varepsilon$, where $c(t)=2(1-\sqrt{1-t^2})+t/(1-t)+t$. — Lemma~\ref{lem:tree} gives the range; the construction fixes such a parameter. The proof of Theorem~\ref{thm:main} chooses it so that $2c(t)<\varepsilon$.
- reading of the symbol `L`: $L$ is the complex Hilbert space on which $D$ acts. In Proposition~\ref{prop:sequences}, Corollary~\ref{cor:obstruction}: $L$ is nonzero and separable. In Theorem~\ref{thm:main}, Lemma~\ref{lem:ambient}, Lemma~\ref{lem:good-inclusion}, Lemma~\ref{lem:bad-inclusion}: $L=K\otimes K$, where $K=\ell^2(G)$. — Proposition~\ref{prop:sequences} assumes a nonzero separable space, inherited by Corollary~\ref{cor:obstruction}; Lemma~\ref{lem:invariant} uses a general ambient Hilbert space. The sentence preceding equation~\eqref{eq:P} sets $L=K\otimes K$ for the concrete construction.
- reading of the symbol `D`: $D\subseteq\B(L)$ is the ambient unital $C^*$-algebra, with identity $\id_L$. In Proposition~\ref{prop:sequences}, Corollary~\ref{cor:obstruction}: $D$ is norm-separable and $Z(D)=\C\id_L$. In Theorem~\ref{thm:main}, Lemma~\ref{lem:ambient}, Lemma~\ref{lem:good-inclusion}, Lemma~\ref{lem:bad-inclusion}: $D=C^*(\{\lambda(g)\otimes\id_K,\id_K\otimes\pi_0(g),\id_K\otimes\pi_t(g):g\in G\}\cup\{\id_K\otimes E_{xy}:x,y\in G\})\subseteq\B(K\otimes K)$, where $E_{xy}\delta_z=\mathbf1_{\{z=y\}}\delta_x$. — Lemma~\ref{lem:invariant} assumes a general unital ambient algebra. Proposition~\ref{prop:sequences} imposes norm separability and scalar center, and Corollary~\ref{cor:obstruction} inherits those hypotheses. Equation~\eqref{eq:D} specifies the concrete algebra used in Lemmas~\ref{lem:ambient}, \ref{lem:good-inclusion}, \ref{lem:bad-inclusion} and the proof of Theorem~\ref{thm:main}.
- reading of the symbol `U_n`: $(U_n)_{n\ge1}$ is one sequence of unitaries on $L$ satisfying $U_nDU_n^*=D$ for every $n$, common to every $b\in Q$: for each such $b$ there is a fixed $p_b\in P$ with $\norm{b-U_np_bU_n^*}\to0$. In Proposition~\ref{prop:sequences}: In the conditional conjugacy argument, for a chosen $S$ satisfying $S\E_D(P)S^*=\E_D(Q)$, $U_n:L\to L$ is the restriction of $S$ from the $n$th coordinate to its image coordinate, with both coordinates identified with $L$. — Proposition~\ref{prop:sequences}(ii) explicitly says that the same sequence works for every $b$; its proof constructs coordinate restrictions of a spatial conjugacy. Lemma~\ref{lem:invariant} assumes a sequence with this same property.
- reading of the symbol `p_b`: For the chosen sequence $(U_n)_{n\ge1}$ and each $b\in Q$, $p_b\in P$ is the fixed element $p_b=\lim_{n\to\infty}U_n^*bU_n$ in operator norm, equivalently $\norm{b-U_np_bU_n^*}\to0$; it may depend on $b$ and on the chosen sequence, but not on $n$. — Proposition~\ref{prop:sequences}(ii) places the choice of $p_b$ after the common sequence and after $b$; its proof identifies $p_b$ as the norm limit of the entries of the pulled-back constant sequence. Lemma~\ref{lem:invariant} assumes precisely the same approximation.
- reading of the symbol `W`: $W$ is a unitary operator on $L$. In Corollary~\ref{cor:obstruction}: $W$ satisfies $WPW^*=Q$ in the conditional distance assertion and is not required to normalize $D$. In Lemma~\ref{lem:ambient}, Theorem~\ref{thm:main}: The supplied choice is $W=W_{\pi_t}W_{\pi_0}^*$, where $W_{\pi_a}(\delta_x\otimes v)=\delta_x\otimes\pi_a(x)v$ for $a=0,t$; it satisfies $WP_0W^*=P_t$ and $\norm{W-\id_L}\le c(t)$. — Corollary~\ref{cor:obstruction} introduces an arbitrary implementing unitary; Lemma~\ref{lem:ambient} and its proof supply the concrete choice, which is used in the proof of Theorem~\ref{thm:main}.
- reading of the symbol `\sigma`: $\sigma$ is a unitary representation of $G$ on a nonzero Hilbert space. In Lemma~\ref{lem:bad-inclusion}: $\sigma=\pi_t\otimes\rho\otimes1$ acts on $K^{\otimes3}$, where $1$ is the trivial representation on the last copy of $K$. — Lemma~\ref{lem:absorption} allows any unitary representation on a nonzero Hilbert space $J$; the proof of Lemma~\ref{lem:bad-inclusion} specifies the tensor product representation and its space.

## Added conditions

None: no condition was added to the paper's own hypotheses.

## Conditions assumed

### Cited results

None: no result rests on a theorem imported from the literature.

### Deferred substrate gates

None: every substrate this run needed was built and proved.

## Unresolved / notes

- run-level `symbol H`: [note, V1.5] symbol table corrected: def "The complex Hilbert space on which the algebras under consideration act." (The recorded definition describes only the main theorem's witness. The introductory notation is general, while the sequence construction specifies a particular direct sum. These are local specializations, not conflicting redefinitions.)
- run-level `symbol A`: [note, V1.5] symbol table corrected: type "$C^*$-algebra", space "$\{C\subseteq\B(H):C\text{ is a }C^*\text{-algebra}\}$", def "One of the $C^*$-algebras $A,B\subseteq\B(H)$ under consideration." (The recorded entry restricts the general notation to the main theorem's algebras. Unitality, norm separability, and the explicit sequence-algebra construction belong to the theorem's scope.)
- run-level `symbol B`: [note, V1.5] symbol table corrected: type "$C^*$-algebra", space "$\{C\subseteq\B(H):C\text{ is a }C^*\text{-algebra}\}$", def "The second of the $C^*$-algebras $A,B\subseteq\B(H)$ under consideration." (The recorded entry restricts the general notation to the main theorem's algebras. The theorem's constructed second algebra depends on the chosen deformation parameter.)
- run-level `symbol D`: [note, V1.5] symbol table corrected: def "$D\subseteq\B(L)$ is the ambient unital $C^*$-algebra." (The recorded definition describes only the sequence setting and omits the defining generators of the concrete algebra. Norm separability and scalar center are scoped hypotheses, rather than additional assumptions of Lemma~\ref{lem:invariant}.)
- run-level `symbol \KK`: [note, V1.5] symbol table corrected: space "$\{f:\mathcal C_H\times\mathcal C_H\to[0,\infty)\}$, where $\mathcal C_H=\{C\subseteq\B(H):C\text{ is a }C^*\text{-algebra}\}$", def "$\KK(A,B)=\max\left\{\sup_{a\in A_1}\inf_{b\in B_1}\norm{a-b},\,\sup_{b\in B_1}\inf_{a\in A_1}\norm{b-a}\right\}$." (The recorded definition mentions two directed distances without specifying how they are combined. The paper defines their maximum. Also, $[0,\infty)$ is the codomain of the distance, rather than the space containing the functional itself.)
- run-level `symbol \E_D(Q)`: [note, V1.5] symbol table corrected: def "$\E_D(Q)=\{(x_n)_{n\ge1}:x_n\in D,\ x_n\to q\in Q\text{ in norm}\}$, acting diagonally on $\bigoplus_{n\ge1}L$." (The recorded 'corresponding diagonal algebra' leaves the coordinate condition implicit. The paper requires every coordinate to belong to $D$ and requires norm convergence to an element of $Q$; coordinates need not belong to $Q$.)
- run-level `symbol W`: [note, V1.5] symbol table corrected: def "A unitary operator on $L$ conjugating the relevant pair of subalgebras." (The recorded definition covers only the conditional unitary in the corollary. The concrete construction also uses W, with the explicit choice supplied by the absorption unitaries. These are scoped choices of the same kind of operator, rather than a change in its type.)
- note on `symbol \E_D(Q)`: symbol table corrected: def "$\E_D(Q)=\{(x_n)_{n\ge1}:x_n\in D,\ x_n\to q\in Q\text{ in norm}\}$, acting diagonally on $\bigoplus_{n\ge1}L$." (The recorded 'corresponding diagonal algebra' leaves the coordinate condition implicit. The paper requires every coordinate to belong to $D$ and requires norm convergence to an element of $Q$; coordinates need not belong to $Q$.)
- note on `symbol \KK`: symbol table corrected: space "$\{f:\mathcal C_H\times\mathcal C_H\to[0,\infty)\}$, where $\mathcal C_H=\{C\subseteq\B(H):C\text{ is a }C^*\text{-algebra}\}$", def "$\KK(A,B)=\max\left\{\sup_{a\in A_1}\inf_{b\in B_1}\norm{a-b},\,\sup_{b\in B_1}\inf_{a\in A_1}\norm{b-a}\right\}$." (The recorded definition mentions two directed distances without specifying how they are combined. The paper defines their maximum. Also, $[0,\infty)$ is the codomain of the distance, rather than the space containing the functional itself.)
- note on `symbol A`: symbol table corrected: type "$C^*$-algebra", space "$\{C\subseteq\B(H):C\text{ is a }C^*\text{-algebra}\}$", def "One of the $C^*$-algebras $A,B\subseteq\B(H)$ under consideration." (The recorded entry restricts the general notation to the main theorem's algebras. Unitality, norm separability, and the explicit sequence-algebra construction belong to the theorem's scope.)
- note on `symbol B`: symbol table corrected: type "$C^*$-algebra", space "$\{C\subseteq\B(H):C\text{ is a }C^*\text{-algebra}\}$", def "The second of the $C^*$-algebras $A,B\subseteq\B(H)$ under consideration." (The recorded entry restricts the general notation to the main theorem's algebras. The theorem's constructed second algebra depends on the chosen deformation parameter.)
- note on `symbol D`: symbol table corrected: def "$D\subseteq\B(L)$ is the ambient unital $C^*$-algebra." (The recorded definition describes only the sequence setting and omits the defining generators of the concrete algebra. Norm separability and scalar center are scoped hypotheses, rather than additional assumptions of Lemma~\ref{lem:invariant}.)
- note on `symbol H`: symbol table corrected: def "The complex Hilbert space on which the algebras under consideration act." (The recorded definition describes only the main theorem's witness. The introductory notation is general, while the sequence construction specifies a particular direct sum. These are local specializations, not conflicting redefinitions.)
- note on `symbol W`: symbol table corrected: def "A unitary operator on $L$ conjugating the relevant pair of subalgebras." (The recorded definition covers only the conditional unitary in the corollary. The concrete construction also uses W, with the explicit choice supplied by the absorption unitaries. These are scoped choices of the same kind of operator, rather than a change in its type.)

### V1 lint warnings

- thm:main: thm:main references \ref{prop:sequences} (prop:sequences) but `depends_on` lacks ass:sequences-l, ass:sequences-d, ass:sequences-center, ass:sequences-subalgebras, ass:sequences-conjugacy; V1.5 must confirm whether the paper assumes it or merely mentions it
- thm:main: thm:main references \ref{cor:obstruction} (cor:obstruction) but `depends_on` lacks ass:obstruction-tensor-distinction, ass:obstruction-unitary; V1.5 must confirm whether the paper assumes it or merely mentions it
- thm:obstruction: cor:obstruction references \ref{prop:sequences} (prop:sequences) but `depends_on` lacks ass:sequences-conjugacy; V1.5 must confirm whether the paper assumes it or merely mentions it
- thm:obstruction: cor:obstruction references \ref{lem:invariant} (lem:invariant) but `depends_on` lacks ass:invariant-unital, ass:invariant-approximation; V1.5 must confirm whether the paper assumes it or merely mentions it
- lem:ambient: lem:ambient references \ref{lem:absorption} (lem:absorption) but `depends_on` lacks ass:absorption-representation; V1.5 must confirm whether the paper assumes it or merely mentions it
- lem:bad-inclusion: lem:bad-inclusion references \ref{lem:absorption} (lem:absorption) but `depends_on` lacks ass:absorption-representation; V1.5 must confirm whether the paper assumes it or merely mentions it

## Lean evidence

- build of the run barrel: **ok**
- source scan (sorry / admit / axiom): clean

| declaration | axioms |
| --- | --- |
| `Papers.OaiCloseSeparableCstar.exists_close_not_conjugate` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiCloseSeparableCstar.seqAlg_properties` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiCloseSeparableCstar.tensorIdentity_invariant` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiCloseSeparableCstar.seqAlg_obstruction` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiCloseSeparableCstar.exists_treeRep` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiCloseSeparableCstar.absorption` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiCloseSeparableCstar.ambient_properties` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiCloseSeparableCstar.goodInclusion` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiCloseSeparableCstar.norm_sum_leftReg_gen_le` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiCloseSeparableCstar.badInclusion` | clean — `propext`, `Classical.choice`, `Quot.sound` |

## Inputs

| artifact | status |
| --- | --- |
| `discovery/v1_scope.json` | present (11 environment(s)) |
| `discovery/v1_5_review.json` | present (verdict PASS) |
| `formalization/crosswalk_full.json` | present (304 object(s)) |
| `graph.json` | present (306 node(s)) |
| Lean evidence | collected (build ok, 0 scan issue(s), 304 declaration(s)) |

## Annotated paper

Annotated paper: `annotated/main.tex` (10 annotation(s), 0 unlocated; index `annotated/ANNOTATIONS.md`); PDF: `annotated/main.pdf`
