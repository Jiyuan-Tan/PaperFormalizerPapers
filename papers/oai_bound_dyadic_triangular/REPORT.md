# Correctness report — oai_bound_dyadic_triangular

**Verdict: NO ERROR FOUND**

**Paper: MINOR ISSUES — no main result is shown false or weakened**

Minor:

- Theorem 1.1: condition added (bookkeeping or a pinned reading)
- Proposition 4.1: condition added (bookkeeping or a pinned reading)
- Lemma 5.2: condition added (bookkeeping or a pinned reading)
- `def:haar-sign`: ambiguous; a reading was pinned
- `k`: notation ambiguous; a reading was pinned
- `m`: notation ambiguous; a reading was pinned
- `\oplus`: notation ambiguous; a reading was pinned
- `F_v`: notation ambiguous; a reading was pinned
- `P`: notation ambiguous; a reading was pinned
- `Q`: notation ambiguous; a reading was pinned
- `a`: notation ambiguous; a reading was pinned
- `U`: notation ambiguous; a reading was pinned
- `H_v`: notation ambiguous; a reading was pinned
- `W_v`: notation ambiguous; a reading was pinned
- `R_v`: notation ambiguous; a reading was pinned
- `T_v`: notation ambiguous; a reading was pinned
- `D_v`: notation ambiguous; a reading was pinned
- `U_v`: notation ambiguous; a reading was pinned
- `w_v(i)`: notation ambiguous; a reading was pinned
- `e_v(\mathbf I)`: notation ambiguous; a reading was pinned
- `e(\mathbf I)`: notation ambiguous; a reading was pinned
- `\tau(\mathbf I)`: notation ambiguous; a reading was pinned
- `b_v`: notation ambiguous; a reading was pinned
- `\delta(\mathbf I)`: notation ambiguous; a reading was pinned
- `J_k`: notation ambiguous; a reading was pinned

8 result(s) of the paper were examined. None was found wrong as printed. In Lean: 8 proved, 0 taken from the literature as cited, 0 not certified, 0 not formalized.

## What was wrong and what was done

No error was found in the results examined.

## Clarifications (not errors)

Nothing in this section is an error of the paper. Each item is something the paper determines but does not say, made explicit so that the statements can be read, and formalized, in one way.

**How a statement is read.**

- **Theorem 1.1.** For $I=[2^kn_I,2^k(n_I+1))$, its halves are $I_{\mathrm{left}}=[2^kn_I,2^kn_I+2^{k-1})$ and $I_{\mathrm{right}}=[2^kn_I+2^{k-1},2^k(n_I+1))$.

**Notation.**

- $k$: $k$ is an integer index whose domain is determined by whether it indexes dyadic scales or a finite eigenbasis. In Proposition~\ref{prop:trace}: In the cubic trace expansion, $k$ ranges over the chosen orthonormal eigenbasis of $M$, just as $i$ and $j$ do. In Proposition~\ref{prop:increase}: The parent scale satisfies $k\ge m+1$. In Lemma~\ref{lem:total}: $J_k$ is defined for $k\ge m$, and the telescoping identity is asserted for $k\ge m+1$. In Theorem~\ref{thm:main}: In the statement, $k$ ranges over $S$; in the step-function proof the telescoping sum ranges over every integer from $k_-=\min S$ through $k_+=\max S$, after choosing $m\le k_--1$.
- $m$: $m\in\Z$ is a chosen common atom scale such that each step input is constant on products of intervals in $\cD_m$; it need not be the coarsest such scale. In Theorem~\ref{thm:main}: In the step-function proof with $S\ne\varnothing$, the common atom scale is refined, if necessary, so that $m\le\min S-1$.
- $\oplus$: $a\oplus b$ is bitwise XOR when its operands are nonnegative integers, whereas $H\oplus K$ is the direct sum when its operands are inner product spaces.
- $F_v$: For $v\in\Z/3\Z$, $F_v:\R_+^2\to\R$ is the input evaluated on the cyclic pair $(x_v,x_{v+1})$. In Proposition~\ref{prop:increase}, Lemma~\ref{lem:total}: The $F_v$ are bounded compactly supported real dyadic step functions at a common fixed scale $m$; $F_v(i,j)$ denotes their constant value on the corresponding pair of atoms. In Lemma~\ref{lem:continuity}: Each $F_v$ belongs to $L^3(\R_+^2)$. In Theorem~\ref{thm:main}: In the statement, the $F_v$ are bounded compactly supported measurable real functions. The proof first treats dyadic step inputs at a common scale $m$ and then passes to general inputs by dyadic step approximation; its completion also applies to arbitrary real $L^3(\R_+^2)$ inputs.
- $P$: $P$ is a symmetric positive semidefinite matrix, with $\supp P=(\ker P)^\perp$; zero eigenvalues are omitted when the supported Hessian form is evaluated. In Lemma~\ref{lem:hessian}: For the smoothness and derivative assertions, $P$ varies among matrices positive definite on a fixed support, and the directions act on that support. In Lemma~\ref{lem:order}: $P$ and $Q$ act on the same space and satisfy $P\le aQ$.
- $Q$: $Q$ has a local matrix meaning and a separate local nonnegative scalar meaning. In Lemma~\ref{lem:order}: $Q$ is a positive semidefinite matrix on the same space as $P$, satisfying $P\le aQ$. In Proposition~\ref{prop:trace}: $Q=\sum_{i,j:\,q_i+q_j>0}\frac{q_i^2q_j^2}{q_i+q_j}\abs{D_{ij}}^2$ is a nonnegative scalar, where $m_i$ are the eigenvalues of $M$, $q_i=\abs{m_i}$ are ordered nonincreasingly, and $D_{ij}$ are entries in that orthonormal eigenbasis.
- $a$: $a$ is a real scalar whose meaning is local to its occurrence. In Lemma~\ref{lem:order}: $a\ge1$ is the comparison factor satisfying $P\le aQ$. In Lemma~\ref{lem:total}: In the energy estimate, $a,b\ge0$ are the Hilbert--Schmidt norms of the two edges incident to $v$; thus $a$ need not be at least one. In Theorem~\ref{thm:main}: In the inequality $\abs{\abs a-\abs b}\le\abs{a-b}$ used to pass to the absolute sum, $a,b$ are real scalar arguments.
- $U$: $U$ is a symmetric matrix on the same space as $T$. In Corollary~\ref{cor:gap}: $-T\le U\le T$; consequently $U$ annihilates $\ker T$.
- $H_v$: $H_v$, $v\in\Z/3\Z$, is a finite-dimensional real inner product space. In Proposition~\ref{prop:increase}, Lemma~\ref{lem:total}: For $\mathbf I\in\cA_k$, $k\ge m$, $H_v$ has an orthonormal basis indexed by the intervals of $\cD_m$ contained in $I_v$, so $\dim H_v=2^{k-m}$. In Proposition~\ref{prop:increase}: In the proof, child atom spaces are identified with the corresponding coordinate subspaces of the fixed parent spaces, and child matrices are extended by zero.
- $W_v$: $W_v:H_{v+1}\to H_v$ is a real linear map, with vertex indices interpreted in $\Z/3\Z$. In Proposition~\ref{prop:increase}, Lemma~\ref{lem:total}: For $\mathbf I\in\cA_k$, $k\ge m$, the atom-basis entries are $W_v(i,j)=\sqrt{w_v(i)w_{v+1}(j)}\,F_v(i,j)$, where $F_v(i,j)$ is the input's constant value on the corresponding atom pair. In Proposition~\ref{prop:increase}: In the proof, child maps are extended by zero to the parent atom spaces; the extended child edge is $C_vW_vC_{v+1}$, where $C_v=(\Id+s_vD_v)^{1/2}$.
- $R_v$: $R_v=[\,W_v\quad W_{v-1}^*\,]:H_{v+1}\oplus H_{v-1}\to H_v$, with $v\in\Z/3\Z$. In Proposition~\ref{prop:increase}, Lemma~\ref{lem:total}: $R_v$ is constructed separately for each admissible triple $\mathbf I\in\cA_k$, $k\ge m$, from its atom spaces and the weighted edge matrices in equation~\ref{eq:weighted-edge}.
- $T_v$: $T_v=R_v^*R_v$ is the Gram operator on $H_{v+1}\oplus H_{v-1}$ of the row star $R_v=[\,W_v\quad W_{v-1}^*\,]$. In Proposition~\ref{prop:increase}, Lemma~\ref{lem:total}: $T_v$ depends on the interval triple through its atom spaces and weighted edges: in $e_v(\mathbf I)=\Phi(T_v)$ it is $T_v(\mathbf I)=R_v(\mathbf I)^*R_v(\mathbf I)$, and a child energy uses the corresponding child's operator.
- $D_v$: $D_v:H_v\to H_v$, $v\in\Z/3\Z$, is symmetric and satisfies $\norm{D_v}_{\op}\le1$. In Proposition~\ref{prop:increase}: For the parent $\mathbf I\in\cA_k$, $k\ge m+1$, $D_v$ is diagonal in the atom basis, with diagonal entry equal to the constant value of $h_{I_v}$ on that atom.
- $U_v$: $U_v=R_v^*D_vR_v$ acts on $H_{v+1}\oplus H_{v-1}$, with $v\in\Z/3\Z$. In Proposition~\ref{prop:increase}: For each $\mathbf I\in\cA_k$ with $k\ge m+1$, $U_v$ uses the row star of that triple and the diagonal matrix $D_v$ of the $h_{I_v}$-values on its atoms.
- $w_v(i)$: For $\mathbf I\in\cA_k$ with $k\ge m$ and $v\in\Z/3\Z$, $i$ indexes an interval of $\cD_m$ contained in $I_v$, and $w_v(i)=2^{m-k}$ is its mass under $\abs{I_v}^{-1}\dd x_v$; the $2^{k-m}$ atom weights sum to one.
- $e_v(\mathbf I)$: $e_v(\mathbf I)$ is defined for $v\in\Z/3\Z$ and $\mathbf I\in\cA_k$ with $k\ge m$, using the atom spaces and weighted edge matrices at the common atom scale $m$.
- $e(\mathbf I)$: $e(\mathbf I)=\sum_{v=0}^2e_v(\mathbf I)$ is the local matrix energy for $\mathbf I\in\cA_k$, $k\ge m$, constructed from inputs constant on products of intervals in $\cD_m$ using the atom weights $w_v(i)=2^{m-k}$.
- $\tau(\mathbf I)$: $\tau(\mathbf I)$ is defined for $\mathbf I\in\cA_k$ with $k\ge m+1$, using the weighted atom matrices $W_v$ and the diagonal matrices $D_v$ of the $h_{I_v}$-values on atoms; equivalently, $\tau(\mathbf I)=2^{-3k}\int_{I_0\times I_1\times I_2}F_0(x_0,x_1)F_1(x_1,x_2)F_2(x_2,x_0)\prod_{v=0}^2h_{I_v}(x_v)\dd x_0\dd x_1\dd x_2$.
- $b_v$: For a child of $\mathbf I$, $b_v=0$ selects the left half of $I_v$ and $b_v=1$ selects the right half, whose index is $2n_{I_v}+b_v$; admissible child triples satisfy $b_0\oplus b_1\oplus b_2=0$.
- $\delta(\mathbf I)$: For $\mathbf I\in\cA_k$ with $k\ge m+1$, $\delta(\mathbf I)=\frac14\sum_{\mathbf I'\in\operatorname{ch}(\mathbf I)}e(\mathbf I')-e(\mathbf I)$, where $m$ is the common dyadic step scale of the inputs.
- $J_k$: $J_k=\sum_{\mathbf I\in\cA_k}2^{2k}e(\mathbf I)$ is defined for integer $k\ge m$, using inputs constant on products of intervals in $\cD_m$. In Theorem~\ref{thm:main}: In the step-function proof with nonempty $S$, the common atom level is refined so that $m\le k_--1$, where $k_-=\min S$; hence $J_{k_--1}$ and all subsequent energies in the telescoping sum are defined.

## What was proved in Lean, and what was not

A result is proved in Lean when a Lean declaration reviewed as stating it has a complete proof using no axiom beyond the standard ones. For a corrected result, the corrected statement is the one formalized.

| Result | Formal status | Lean declaration | Axioms |
| --- | --- | --- | --- |
| Theorem 1.1 | proved in Lean, under 1 condition(s) made explicit | `Papers.OaiBoundDyadicTriangular.dyadic_triangular_bound` (`TMain.lean:65`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 2.1 | proved in Lean | `Papers.OaiBoundDyadicTriangular.matrixEnergy_hessian` (`Helpers/MatrixHessian.lean:104`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 2.2 | proved in Lean | `Papers.OaiBoundDyadicTriangular.hessForm_order` (`Helpers/MatrixHessian.lean:135`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Corollary 2.3 | proved in Lean | `Papers.OaiBoundDyadicTriangular.matrixEnergy_midpoint_gap` (`TGap.lean:22`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Proposition 3.1 | proved in Lean | `Papers.OaiBoundDyadicTriangular.abs_trace_le_hessForm_sum` (`TTrace.lean:212`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Proposition 4.1 | proved in Lean, under 1 condition(s) made explicit | `Papers.OaiBoundDyadicTriangular.energyIncrement_controls_trace` (`TIncrease.lean:24`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 5.1 | proved in Lean | `Papers.OaiBoundDyadicTriangular.totalEnergy_bound_and_telescope` (`Helpers/Summation.lean:262`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 5.2 | proved in Lean, under 1 condition(s) made explicit | `Papers.OaiBoundDyadicTriangular.localForm_one_scale_bound` (`Helpers/Continuity.lean:29`) | the standard ones only (propext, Classical.choice, Quot.sound) |

The Lean development builds; it contains no `sorry`, `admit` or added axiom.

## The corrected paper

`bundle/corrected_paper/` holds the paper as it reads after the corrections, as plain source in the author's own class and layout, compiled to `bundle/corrected_paper/main.pdf` (12 pages). `bundle/MATCH.md` sets each result beside its Lean declaration; `bundle/lean/` holds the Lean code.

The mechanical checks leave nothing open.

# Technical appendix

The records behind the report above, by the run's own identifiers.

- paper: `main.tex` (source sha256 `5c9302a7870a5779b689dc5b5031fd57d652d421fee7ed6656b7cf040a227568`)
- stage completed: `5`
- results in scope: 8

| bucket | count |
| --- | --- |
| verified | 5 |
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
| source | `sections/01-introduction.tex:39-47` (`theorem`, label `thm:main`) |
| statement | \label{thm:main} For every finite \(S\subset\Z\) and all real bounded compactly supported measurable functions \(F_0,F_1,F_2\) on \(\R_+^2\), \begin{equation}\label{eq:main} \sum_{k\in S}\sum_{\mathbf I\in\cA_k} \abs{L_{\mathbf I}(F_0,F_1,F_2)} \le 40\prod_{v=0}^2\norm{F_v}_{L^3(\R_+^2)}. \end{equation} |
| appended hypothesis list | ass:main-scales, ass:main-inputs |
| Lean | `TMain.lean:65` — `Papers.OaiBoundDyadicTriangular.dyadic_triangular_bound` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | `ass:pin-1` |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 2. Hessian of the energy `lem:hessian`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `sections/02-matrix.tex:28-36` (`lemma`, label `lem:hessian`) |
| statement | \label{lem:hessian} On matrices positive definite on a fixed support, \(\Phi\) is smooth and, for a symmetric direction \(K\) on that support, \[ d\Phi_P(K)=\frac32\tr(\sqrt P\,K), \qquad d^2\Phi_P(K,K)=b_P(K). \] In particular, \(\Phi\) is convex on the positive semidefinite cone. |
| appended hypothesis list | ass:hessian-positive-support, ass:hessian-direction |
| Lean | `Helpers/MatrixHessian.lean:104` — `Papers.OaiBoundDyadicTriangular.matrixEnergy_hessian` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 3. Order comparison `lem:order`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `sections/02-matrix.tex:65-72` (`lemma`, label `lem:order`) |
| statement | \label{lem:order} Suppose \(P,Q\) are positive semidefinite matrices on the same space, \(a\ge1\), and \(P\le aQ\). Every symmetric \(K\) supported on \(P\) is supported on \(Q\), and \begin{equation}\label{eq:order} b_P(K)\ge a^{-1/2}b_Q(K). \end{equation} |
| appended hypothesis list | ass:order-matrices, ass:order-factor, ass:order-comparison, ass:order-direction |
| Lean | `Helpers/MatrixHessian.lean:135` — `Papers.OaiBoundDyadicTriangular.hessForm_order` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 4. A midpoint gap `thm:gap`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `sections/02-matrix.tex:113-120` (`corollary`, label `cor:gap`) |
| statement | \label{cor:gap} If \(T\ge0\) and \(U=U^*\) satisfy \(-T\le U\le T\), then \(U\) is supported on \(T\) and \begin{equation}\label{eq:gap} \frac{\Phi(T+U)+\Phi(T-U)}2-\Phi(T) \ge\frac{1}{2\sqrt2}b_T(U). \end{equation} |
| appended hypothesis list | ass:gap-positive, ass:gap-symmetry, ass:gap-order |
| Lean | `TGap.lean:22` — `Papers.OaiBoundDyadicTriangular.matrixEnergy_midpoint_gap` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 5. Mixed trace estimate `prop:trace`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `sections/03-trace.tex:22-31` (`proposition`, label `prop:trace`) |
| statement | \label{prop:trace} For the maps in \eqref{eq:row-star}, let \(D_v:H_v\to H_v\) be symmetric with \(\norm{D_v}_{\op}\le1\), and put \(U_v=R_v^*D_vR_v\). Then \(U_v\) is supported on \(T_v\), and \begin{equation}\label{eq:trace} \abs{\tr(D_0W_0D_1W_1D_2W_2)} \le\frac53\sum_{v=0}^2 b_{T_v}(U_v). \end{equation} The constant is independent of all three dimensions. |
| appended hypothesis list | ass:trace-symmetry, ass:trace-contraction |
| Lean | `TTrace.lean:212` — `Papers.OaiBoundDyadicTriangular.abs_trace_le_hessForm_sum` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 6. Local energy increase `prop:increase`

| field | value |
| --- | --- |
| bucket | `verified_with_bookkeeping` |
| source | `sections/04-dyadic.tex:52-64` (`proposition`, label `prop:increase`) |
| statement | \label{prop:increase} For \(\mathbf I\in\cA_k\), \(k\ge m+1\), define \[ \delta(\mathbf I) =\frac14\sum_{\mathbf I'\in\operatorname{ch}(\mathbf I)} e(\mathbf I')-e(\mathbf I). \] Then \(\delta(\mathbf I)\ge0\), and \begin{equation}\label{eq:local-control} \abs{\tau(\mathbf I)} \le\frac{10\sqrt2}{3}\,\delta(\mathbf I). \end{equation} |
| appended hypothesis list | ass:increase-triple, ass:increase-scale |
| Lean | `TIncrease.lean:24` — `Papers.OaiBoundDyadicTriangular.energyIncrement_controls_trace` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | `ass:pin-1` |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 7. Total energy `lem:total`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `sections/05-summation.tex:9-24` (`lemma`, label `lem:total`) |
| statement | \label{lem:total} For the step functions of Section~\ref{sec:dyadic} and every \(k\ge m\), set \[ J_k=\sum_{\mathbf I\in\cA_k}2^{2k}e(\mathbf I). \] Then \begin{equation}\label{eq:total} 0\le J_k\le2\sqrt2\sum_{v=0}^2\norm{F_v}_3^3. \end{equation} For \(k\ge m+1\), \begin{equation}\label{eq:telescope} \sum_{\mathbf I\in\cA_k}2^{2k}\delta(\mathbf I) =J_{k-1}-J_k. \end{equation} |
| appended hypothesis list | ass:step-bounded, ass:step-compact, ass:step-atoms, ass:total-scale |
| Lean | `Helpers/Summation.lean:262` — `Papers.OaiBoundDyadicTriangular.totalEnergy_bound_and_telescope` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 8. Continuity at one scale `lem:continuity`

| field | value |
| --- | --- |
| bucket | `verified_with_bookkeeping` |
| source | `sections/05-summation.tex:80-90` (`lemma`, label `lem:continuity`) |
| statement | \label{lem:continuity} For every \(k\in\Z\) and real \(F_v\in L^3(\R_+^2)\), \begin{equation}\label{eq:one-scale} \sum_{\mathbf I\in\cA_k}\abs{L_{\mathbf I}(F_0,F_1,F_2)} \le\prod_{v=0}^2\norm{F_v}_3. \end{equation} Consequently the sequence \((L_{\mathbf I}(F_0,F_1,F_2))_{\mathbf I\in\cA_k}\) depends continuously on the inputs as a map from \(L^3\times L^3\times L^3\) to \(\ell^1(\cA_k)\). |
| appended hypothesis list | ass:continuity-scale, ass:continuity-inputs |
| Lean | `Helpers/Continuity.lean:29` — `Papers.OaiBoundDyadicTriangular.localForm_one_scale_bound` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | `ass:pin-1` |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

## Corrected version

3 of 8 result(s) differ from the version you provided — 0 repaired, 0 with the proof completed (no error), 3 only with a side condition or reading made explicit; the others are as printed. The Lean formalization is of the corrected version.

### `thm:main` (`sections/01-introduction.tex:39-47`)

- as printed: \label{thm:main} For every finite \(S\subset\Z\) and all real bounded compactly supported measurable functions \(F_0,F_1,F_2\) on \(\R_+^2\), \begin{equation}\label{eq:main} \sum_{k\in S}\sum_{\mathbf I\in\cA_k} \abs{L_{\mathbf I}(F_0,F_1,F_2)} \le 40\prod_{v=0}^2\norm{F_v}_{L^3(\R_+^2)}. \end{equation}
- corrected: statement unchanged
- no error: only a side condition or reading the referee made explicit (see below)
- side condition added by the confirming referee `ass:pin-1`: For $I=[2^kn_I,2^k(n_I+1))$, its halves are $I_{\mathrm{left}}=[2^kn_I,2^kn_I+2^{k-1})$ and $I_{\mathrm{right}}=[2^kn_I+2^{k-1},2^k(n_I+1))$. — pins reading of def:haar-sign: The introduction defines dyadic intervals as half-open, and the subsection ``The four children'' identifies the left and right children by indices $2n_I$ and $2n_I+1$ at scale $k-1$.

### `prop:increase` (`sections/04-dyadic.tex:52-64`)

- as printed: \label{prop:increase} For \(\mathbf I\in\cA_k\), \(k\ge m+1\), define \[ \delta(\mathbf I) =\frac14\sum_{\mathbf I'\in\operatorname{ch}(\mathbf I)} e(\mathbf I')-e(\mathbf I). \] Then \(\delta(\mathbf I)\ge0\), and \begin{equation}\label{eq:local-control} \abs{\tau(\mathbf I)} \le\frac{10\sqrt2}{3}\,\delta(\mathbf I). \end{equation}
- corrected: statement unchanged
- no error: only a side condition or reading the referee made explicit (see below)
- side condition added by the confirming referee `ass:pin-1`: For $I=[2^kn_I,2^k(n_I+1))$, its halves are $I_{\mathrm{left}}=[2^kn_I,2^kn_I+2^{k-1})$ and $I_{\mathrm{right}}=[2^kn_I+2^{k-1},2^k(n_I+1))$. — pins reading of def:haar-sign: The introduction defines dyadic intervals as half-open, and the subsection ``The four children'' identifies the left and right children by indices $2n_I$ and $2n_I+1$ at scale $k-1$.

### `lem:continuity` (`sections/05-summation.tex:80-90`)

- as printed: \label{lem:continuity} For every \(k\in\Z\) and real \(F_v\in L^3(\R_+^2)\), \begin{equation}\label{eq:one-scale} \sum_{\mathbf I\in\cA_k}\abs{L_{\mathbf I}(F_0,F_1,F_2)} \le\prod_{v=0}^2\norm{F_v}_3. \end{equation} Consequently the sequence \((L_{\mathbf I}(F_0,F_1,F_2))_{\mathbf I\in\cA_k}\) depends continuously on the inputs as a map from \(L^3\times L^3\times L^3\) to \(\ell^1(\cA_k)\).
- corrected: statement unchanged
- no error: only a side condition or reading the referee made explicit (see below)
- side condition added by the confirming referee `ass:pin-1`: For $I=[2^kn_I,2^k(n_I+1))$, its halves are $I_{\mathrm{left}}=[2^kn_I,2^kn_I+2^{k-1})$ and $I_{\mathrm{right}}=[2^kn_I+2^{k-1},2^k(n_I+1))$. — pins reading of def:haar-sign: The introduction defines dyadic intervals as half-open, and the subsection ``The four children'' identifies the left and right children by indices $2n_I$ and $2n_I+1$ at scale $k-1$.

## Suggestions to the authors

Not errors: readings the paper determines but does not state, and side conditions the proofs use silently.

- clarification (`ass:pin-1`, used by `thm:main`): For $I=[2^kn_I,2^k(n_I+1))$, its halves are $I_{\mathrm{left}}=[2^kn_I,2^kn_I+2^{k-1})$ and $I_{\mathrm{right}}=[2^kn_I+2^{k-1},2^k(n_I+1))$. — pins reading of def:haar-sign: The introduction defines dyadic intervals as half-open, and the subsection ``The four children'' identifies the left and right children by indices $2n_I$ and $2n_I+1$ at scale $k-1$.
- `def:haar-sign`: pinned reading: For $I=[2^kn_I,2^k(n_I+1))$, its halves are $I_{\mathrm{left}}=[2^kn_I,2^kn_I+2^{k-1})$ and $I_{\mathrm{right}}=[2^kn_I+2^{k-1},2^k(n_I+1))$. (The introduction defines dyadic intervals as half-open, and the subsection ``The four children'' identifies the left and right children by indices $2n_I$ and $2n_I+1$ at scale $k-1$.)
- reading of the symbol `k`: $k$ is an integer index whose domain is determined by whether it indexes dyadic scales or a finite eigenbasis. In Proposition~\ref{prop:trace}: In the cubic trace expansion, $k$ ranges over the chosen orthonormal eigenbasis of $M$, just as $i$ and $j$ do. In Proposition~\ref{prop:increase}: The parent scale satisfies $k\ge m+1$. In Lemma~\ref{lem:total}: $J_k$ is defined for $k\ge m$, and the telescoping identity is asserted for $k\ge m+1$. In Theorem~\ref{thm:main}: In the statement, $k$ ranges over $S$; in the step-function proof the telescoping sum ranges over every integer from $k_-=\min S$ through $k_+=\max S$, after choosing $m\le k_--1$. — The introduction defines dyadic scales for $k\in\Z$; Proposition~\ref{prop:trace} expands the cubic trace in a finite eigenbasis; the energy statements explicitly restrict scales relative to $m$.
- reading of the symbol `m`: $m\in\Z$ is a chosen common atom scale such that each step input is constant on products of intervals in $\cD_m$; it need not be the coarsest such scale. In Theorem~\ref{thm:main}: In the step-function proof with $S\ne\varnothing$, the common atom scale is refined, if necessary, so that $m\le\min S-1$. — The opening of Section~\ref{sec:dyadic} chooses a common atom scale. The step-function proof of Theorem~\ref{thm:main} explicitly refines that scale when necessary.
- reading of the symbol `\oplus`: $a\oplus b$ is bitwise XOR when its operands are nonnegative integers, whereas $H\oplus K$ is the direct sum when its operands are inner product spaces. — The introduction explicitly defines integer XOR; \eqref{eq:row-star} uses the same glyph for the row operator's domain, and the proof of Proposition~\ref{prop:trace} sets $H=H_0\oplus H_1\oplus H_2$.
- reading of the symbol `F_v`: For $v\in\Z/3\Z$, $F_v:\R_+^2\to\R$ is the input evaluated on the cyclic pair $(x_v,x_{v+1})$. In Proposition~\ref{prop:increase}, Lemma~\ref{lem:total}: The $F_v$ are bounded compactly supported real dyadic step functions at a common fixed scale $m$; $F_v(i,j)$ denotes their constant value on the corresponding pair of atoms. In Lemma~\ref{lem:continuity}: Each $F_v$ belongs to $L^3(\R_+^2)$. In Theorem~\ref{thm:main}: In the statement, the $F_v$ are bounded compactly supported measurable real functions. The proof first treats dyadic step inputs at a common scale $m$ and then passes to general inputs by dyadic step approximation; its completion also applies to arbitrary real $L^3(\R_+^2)$ inputs. — The local-form definition fixes the cyclic arguments. The dyadic construction preceding the weighted-edge definition fixes the common atom scale and step inputs; Lemma~\ref{lem:continuity} specifies $L^3$ inputs, and Theorem~\ref{thm:main} specifies bounded compactly supported measurable inputs and uses dyadic step approximation in its proof.
- reading of the symbol `P`: $P$ is a symmetric positive semidefinite matrix, with $\supp P=(\ker P)^\perp$; zero eigenvalues are omitted when the supported Hessian form is evaluated. In Lemma~\ref{lem:hessian}: For the smoothness and derivative assertions, $P$ varies among matrices positive definite on a fixed support, and the directions act on that support. In Lemma~\ref{lem:order}: $P$ and $Q$ act on the same space and satisfy $P\le aQ$. — The definitions preceding equation~\ref{eq:hessian} specify support and the zero convention; Lemma~\ref{lem:hessian} specifies a fixed support for smoothness; Lemma~\ref{lem:order} specifies the comparison space.
- reading of the symbol `Q`: $Q$ has a local matrix meaning and a separate local nonnegative scalar meaning. In Lemma~\ref{lem:order}: $Q$ is a positive semidefinite matrix on the same space as $P$, satisfying $P\le aQ$. In Proposition~\ref{prop:trace}: $Q=\sum_{i,j:\,q_i+q_j>0}\frac{q_i^2q_j^2}{q_i+q_j}\abs{D_{ij}}^2$ is a nonnegative scalar, where $m_i$ are the eigenvalues of $M$, $q_i=\abs{m_i}$ are ordered nonincreasingly, and $D_{ij}$ are entries in that orthonormal eigenbasis. — Lemma~\ref{lem:order} defines the comparison matrix; equation~\ref{eq:Q} introduces the scalar after choosing an orthonormal eigenbasis of $M$.
- reading of the symbol `a`: $a$ is a real scalar whose meaning is local to its occurrence. In Lemma~\ref{lem:order}: $a\ge1$ is the comparison factor satisfying $P\le aQ$. In Lemma~\ref{lem:total}: In the energy estimate, $a,b\ge0$ are the Hilbert--Schmidt norms of the two edges incident to $v$; thus $a$ need not be at least one. In Theorem~\ref{thm:main}: In the inequality $\abs{\abs a-\abs b}\le\abs{a-b}$ used to pass to the absolute sum, $a,b$ are real scalar arguments. — Lemma~\ref{lem:order} introduces the comparison factor; the proof of Lemma~\ref{lem:total} introduces the edge norms; the completion of Theorem~\ref{thm:main} uses the scalar absolute-value inequality.
- reading of the symbol `U`: $U$ is a symmetric matrix on the same space as $T$. In Corollary~\ref{cor:gap}: $-T\le U\le T$; consequently $U$ annihilates $\ker T$. — Corollary~\ref{cor:gap} specifies symmetry and the order bounds on the midpoint perturbation.
- reading of the symbol `H_v`: $H_v$, $v\in\Z/3\Z$, is a finite-dimensional real inner product space. In Proposition~\ref{prop:increase}, Lemma~\ref{lem:total}: For $\mathbf I\in\cA_k$, $k\ge m$, $H_v$ has an orthonormal basis indexed by the intervals of $\cD_m$ contained in $I_v$, so $\dim H_v=2^{k-m}$. In Proposition~\ref{prop:increase}: In the proof, child atom spaces are identified with the corresponding coordinate subspaces of the fixed parent spaces, and child matrices are extended by zero. — The paragraph introducing \eqref{eq:row-star} specifies the abstract spaces. Section~\ref{sec:dyadic} specifies their atom bases, and the proof of Proposition~\ref{prop:increase} keeps parent spaces fixed.
- reading of the symbol `W_v`: $W_v:H_{v+1}\to H_v$ is a real linear map, with vertex indices interpreted in $\Z/3\Z$. In Proposition~\ref{prop:increase}, Lemma~\ref{lem:total}: For $\mathbf I\in\cA_k$, $k\ge m$, the atom-basis entries are $W_v(i,j)=\sqrt{w_v(i)w_{v+1}(j)}\,F_v(i,j)$, where $F_v(i,j)$ is the input's constant value on the corresponding atom pair. In Proposition~\ref{prop:increase}: In the proof, child maps are extended by zero to the parent atom spaces; the extended child edge is $C_vW_vC_{v+1}$, where $C_v=(\Id+s_vD_v)^{1/2}$. — The paragraph introducing \eqref{eq:row-star} gives the abstract maps; \eqref{eq:weighted-edge} gives their dyadic specialization. The proof of Proposition~\ref{prop:increase} specifies how child maps are represented on parent spaces.
- reading of the symbol `R_v`: $R_v=[\,W_v\quad W_{v-1}^*\,]:H_{v+1}\oplus H_{v-1}\to H_v$, with $v\in\Z/3\Z$. In Proposition~\ref{prop:increase}, Lemma~\ref{lem:total}: $R_v$ is constructed separately for each admissible triple $\mathbf I\in\cA_k$, $k\ge m$, from its atom spaces and the weighted edge matrices in equation~\ref{eq:weighted-edge}. — Equation~\ref{eq:row-star} defines the general map; the construction preceding equation~\ref{eq:weighted-edge} specifies the atom spaces and weighted matrices for $\mathbf I\in\cA_k$, $k\ge m$.
- reading of the symbol `T_v`: $T_v=R_v^*R_v$ is the Gram operator on $H_{v+1}\oplus H_{v-1}$ of the row star $R_v=[\,W_v\quad W_{v-1}^*\,]$. In Proposition~\ref{prop:increase}, Lemma~\ref{lem:total}: $T_v$ depends on the interval triple through its atom spaces and weighted edges: in $e_v(\mathbf I)=\Phi(T_v)$ it is $T_v(\mathbf I)=R_v(\mathbf I)^*R_v(\mathbf I)$, and a child energy uses the corresponding child's operator. — Equation~\ref{eq:row-star} defines the operator. The instruction preceding equation~\ref{eq:local-energy} applies that construction to the atom spaces and weighted edges of each interval triple.
- reading of the symbol `D_v`: $D_v:H_v\to H_v$, $v\in\Z/3\Z$, is symmetric and satisfies $\norm{D_v}_{\op}\le1$. In Proposition~\ref{prop:increase}: For the parent $\mathbf I\in\cA_k$, $k\ge m+1$, $D_v$ is diagonal in the atom basis, with diagonal entry equal to the constant value of $h_{I_v}$ on that atom. — Proposition~\ref{prop:trace} specifies arbitrary symmetric contractions; the local-trace paragraph specializes them to Haar sign matrices.
- reading of the symbol `U_v`: $U_v=R_v^*D_vR_v$ acts on $H_{v+1}\oplus H_{v-1}$, with $v\in\Z/3\Z$. In Proposition~\ref{prop:increase}: For each $\mathbf I\in\cA_k$ with $k\ge m+1$, $U_v$ uses the row star of that triple and the diagonal matrix $D_v$ of the $h_{I_v}$-values on its atoms. — The definition in Proposition~\ref{prop:trace} is reused in equation~\ref{eq:conditional}; the dyadic construction defines the Haar sign matrices for $k\ge m+1$.
- reading of the symbol `w_v(i)`: For $\mathbf I\in\cA_k$ with $k\ge m$ and $v\in\Z/3\Z$, $i$ indexes an interval of $\cD_m$ contained in $I_v$, and $w_v(i)=2^{m-k}$ is its mass under $\abs{I_v}^{-1}\dd x_v$; the $2^{k-m}$ atom weights sum to one. — The atom-space paragraph explicitly gives the atom index set, normalized measure, and weight $2^{m-k}$.
- reading of the symbol `e_v(\mathbf I)`: $e_v(\mathbf I)$ is defined for $v\in\Z/3\Z$ and $\mathbf I\in\cA_k$ with $k\ge m$, using the atom spaces and weighted edge matrices at the common atom scale $m$. — The paragraph preceding \eqref{eq:weighted-edge} specifies the atom construction and $k\ge m$; \eqref{eq:local-energy} defines the energy.
- reading of the symbol `e(\mathbf I)`: $e(\mathbf I)=\sum_{v=0}^2e_v(\mathbf I)$ is the local matrix energy for $\mathbf I\in\cA_k$, $k\ge m$, constructed from inputs constant on products of intervals in $\cD_m$ using the atom weights $w_v(i)=2^{m-k}$. — Section~\ref{sec:dyadic} specifies the step inputs, and the paragraph containing \eqref{eq:weighted-edge} and \eqref{eq:local-energy} specifies $k\ge m$ and the normalized atom weights.
- reading of the symbol `\tau(\mathbf I)`: $\tau(\mathbf I)$ is defined for $\mathbf I\in\cA_k$ with $k\ge m+1$, using the weighted atom matrices $W_v$ and the diagonal matrices $D_v$ of the $h_{I_v}$-values on atoms; equivalently, $\tau(\mathbf I)=2^{-3k}\int_{I_0\times I_1\times I_2}F_0(x_0,x_1)F_1(x_1,x_2)F_2(x_2,x_0)\prod_{v=0}^2h_{I_v}(x_v)\dd x_0\dd x_1\dd x_2$. — The paragraph defining the local trace assumes $k\ge m+1$, specifies $D_v$, and identifies the trace with the normalized integral; \eqref{eq:trace-integral} gives its normalization.
- reading of the symbol `b_v`: For a child of $\mathbf I$, $b_v=0$ selects the left half of $I_v$ and $b_v=1$ selects the right half, whose index is $2n_{I_v}+b_v$; admissible child triples satisfy $b_0\oplus b_1\oplus b_2=0$. — The child construction specifies the child index $2n_{I_v}+b_v$ and the admissibility condition, fixing which bit selects each half.
- reading of the symbol `\delta(\mathbf I)`: For $\mathbf I\in\cA_k$ with $k\ge m+1$, $\delta(\mathbf I)=\frac14\sum_{\mathbf I'\in\operatorname{ch}(\mathbf I)}e(\mathbf I')-e(\mathbf I)$, where $m$ is the common dyadic step scale of the inputs. — Proposition~\ref{prop:increase} introduces the quantity for $\mathbf I\in\cA_k$, $k\ge m+1$; Lemma~\ref{lem:total} uses it over the same scale range.
- reading of the symbol `J_k`: $J_k=\sum_{\mathbf I\in\cA_k}2^{2k}e(\mathbf I)$ is defined for integer $k\ge m$, using inputs constant on products of intervals in $\cD_m$. In Theorem~\ref{thm:main}: In the step-function proof with nonempty $S$, the common atom level is refined so that $m\le k_--1$, where $k_-=\min S$; hence $J_{k_--1}$ and all subsequent energies in the telescoping sum are defined. — The opening sentence and defining display of Lemma~\ref{lem:total} specify the step inputs and $k\ge m$.

## Added conditions

| id | where | class | condition |
| --- | --- | --- | --- |
| `ass:pin-1` | `thm:main` | V1.5 bookkeeping | For $I=[2^kn_I,2^k(n_I+1))$, its halves are $I_{\mathrm{left}}=[2^kn_I,2^kn_I+2^{k-1})$ and $I_{\mathrm{right}}=[2^kn_I+2^{k-1},2^k(n_I+1))$. (pins reading of def:haar-sign: The introduction defines dyadic intervals as half-open, and the subsection ``The four children'' identifies the left and right children by indices $2n_I$ and $2n_I+1$ at scale $k-1$.) |
| `ass:pin-1` | `prop:increase` | V1.5 bookkeeping | For $I=[2^kn_I,2^k(n_I+1))$, its halves are $I_{\mathrm{left}}=[2^kn_I,2^kn_I+2^{k-1})$ and $I_{\mathrm{right}}=[2^kn_I+2^{k-1},2^k(n_I+1))$. (pins reading of def:haar-sign: The introduction defines dyadic intervals as half-open, and the subsection ``The four children'' identifies the left and right children by indices $2n_I$ and $2n_I+1$ at scale $k-1$.) |
| `ass:pin-1` | `lem:continuity` | V1.5 bookkeeping | For $I=[2^kn_I,2^k(n_I+1))$, its halves are $I_{\mathrm{left}}=[2^kn_I,2^kn_I+2^{k-1})$ and $I_{\mathrm{right}}=[2^kn_I+2^{k-1},2^k(n_I+1))$. (pins reading of def:haar-sign: The introduction defines dyadic intervals as half-open, and the subsection ``The four children'' identifies the left and right children by indices $2n_I$ and $2n_I+1$ at scale $k-1$.) |

## Conditions assumed

### Cited results

None: no result rests on a theorem imported from the literature.

### Deferred substrate gates

None: every substrate this run needed was built and proved.

## Unresolved / notes

- run-level `def:haar-sign`: [note, V1.5] pinned reading: For $I=[2^kn_I,2^k(n_I+1))$, its halves are $I_{\mathrm{left}}=[2^kn_I,2^kn_I+2^{k-1})$ and $I_{\mathrm{right}}=[2^kn_I+2^{k-1},2^k(n_I+1))$. (The introduction defines dyadic intervals as half-open, and the subsection ``The four children'' identifies the left and right children by indices $2n_I$ and $2n_I+1$ at scale $k-1$.)
- run-level `symbol k`: [note, V1.5] symbol table corrected: type "integer index for dyadic scales; also a dummy eigenbasis index", space "$\Z$ for dyadic scales; the finite eigenbasis index set in the cubic trace expansion", def "$k$ indexes dyadic scales in $\cD_k$, $\cA_k$, and the local forms and energies; in $\tr((DM)^3)=\sum_{i,j,k}m_im_jm_kD_{ij}D_{jk}D_{ki}$, it indexes the chosen orthonormal eigenbasis of $M$." (The entry describes the dyadic use correctly but misses the locally bound eigenbasis index in the cubic trace expansion. This is contextual reuse, rather than a replacement of the dyadic convention.)
- run-level `symbol \oplus`: [note, V1.5] symbol table corrected: type "bitwise XOR for nonnegative integers; direct sum for inner product spaces", space "$\Z_{\ge0}^2\to\Z_{\ge0}$ for integer operands; direct sums of finite-dimensional real inner product spaces for space operands", def "$\oplus$ denotes bitwise XOR of nonnegative integers in admissibility and child-index constraints, and direct sum in expressions such as $H_{v+1}\oplus H_{v-1}$ and $H_0\oplus H_1\oplus H_2$." (The integer operation is correctly recorded, but the entry omits the conventional direct-sum use. Operand types distinguish these simultaneous meanings.)
- run-level `symbol K`: [note, V1.5] symbol table corrected: def "A symmetric matrix $K$ is supported on $P$ if it annihilates $\ker P$. Symmetry then also puts its range in $\supp P$." (The recorded entry invokes support without defining it. The paper explicitly requires annihilation of the kernel, which determines the admissible directions in the Hessian form.)
- run-level `symbol b_P(K)`: [note, V1.5] symbol table corrected: def "For a symmetric matrix $K$ supported on $P$, $b_P(K)=\frac32\sum_{i,j}\frac{\abs{K_{ij}}^2}{\sqrt{p_i}+\sqrt{p_j}}$, where $p_i>0$ are the eigenvalues of $P$ on its support, and the entries are taken in an orthonormal eigenbasis of that support. If $P=0$, the only supported $K$ is zero and $b_0(0)=0$." (The formula is correct, but the recorded definition omits the required orthonormal eigenbasis convention for its matrix entries.)
- run-level `symbol Q`: [note, V1.5] symbol table corrected: type "positive semidefinite comparison matrix or local nonnegative scalar", space "$\{A\in\R^{d\times d}:A=A^*,\ A\ge0\}\cup[0,\infty)$", def "In Lemma~\ref{lem:order}, $Q$ is a positive semidefinite matrix on the same space as $P$, with $P\le aQ$; in the proof of Proposition~\ref{prop:trace}, $Q=\sum_{i,j:\,q_i+q_j>0}\frac{q_i^2q_j^2}{q_i+q_j}\abs{D_{ij}}^2$." (The recorded entry covers only the comparison matrix. The trace proof independently defines a scalar quadratic quantity with the same letter; the two meanings are local and unambiguous.)
- run-level `symbol a`: [note, V1.5] symbol table corrected: type "real scalar with separate local meanings", space "$\R$", def "In Lemma~\ref{lem:order}, $a\ge1$ and $P\le aQ$. In the proof of Lemma~\ref{lem:total}, $a,b$ are the Hilbert--Schmidt norms of the two edges incident to $v$. In the completion of Theorem~\ref{thm:main}, $a,b$ are scalar arguments of $\abs{\abs a-\abs b}\le\abs{a-b}$." (The comparison-factor entry misses two later local uses. The edge norm may be zero, and the absolute-value inequality uses real scalar arguments, so the global range $[1,\infty)$ is incorrect.)
- note on `def:haar-sign`: pinned reading: For $I=[2^kn_I,2^k(n_I+1))$, its halves are $I_{\mathrm{left}}=[2^kn_I,2^kn_I+2^{k-1})$ and $I_{\mathrm{right}}=[2^kn_I+2^{k-1},2^k(n_I+1))$. (The introduction defines dyadic intervals as half-open, and the subsection ``The four children'' identifies the left and right children by indices $2n_I$ and $2n_I+1$ at scale $k-1$.)
- note on `symbol \oplus`: symbol table corrected: type "bitwise XOR for nonnegative integers; direct sum for inner product spaces", space "$\Z_{\ge0}^2\to\Z_{\ge0}$ for integer operands; direct sums of finite-dimensional real inner product spaces for space operands", def "$\oplus$ denotes bitwise XOR of nonnegative integers in admissibility and child-index constraints, and direct sum in expressions such as $H_{v+1}\oplus H_{v-1}$ and $H_0\oplus H_1\oplus H_2$." (The integer operation is correctly recorded, but the entry omits the conventional direct-sum use. Operand types distinguish these simultaneous meanings.)
- note on `symbol a`: symbol table corrected: type "real scalar with separate local meanings", space "$\R$", def "In Lemma~\ref{lem:order}, $a\ge1$ and $P\le aQ$. In the proof of Lemma~\ref{lem:total}, $a,b$ are the Hilbert--Schmidt norms of the two edges incident to $v$. In the completion of Theorem~\ref{thm:main}, $a,b$ are scalar arguments of $\abs{\abs a-\abs b}\le\abs{a-b}$." (The comparison-factor entry misses two later local uses. The edge norm may be zero, and the absolute-value inequality uses real scalar arguments, so the global range $[1,\infty)$ is incorrect.)
- note on `symbol b_P(K)`: symbol table corrected: def "For a symmetric matrix $K$ supported on $P$, $b_P(K)=\frac32\sum_{i,j}\frac{\abs{K_{ij}}^2}{\sqrt{p_i}+\sqrt{p_j}}$, where $p_i>0$ are the eigenvalues of $P$ on its support, and the entries are taken in an orthonormal eigenbasis of that support. If $P=0$, the only supported $K$ is zero and $b_0(0)=0$." (The formula is correct, but the recorded definition omits the required orthonormal eigenbasis convention for its matrix entries.)
- note on `symbol k`: symbol table corrected: type "integer index for dyadic scales; also a dummy eigenbasis index", space "$\Z$ for dyadic scales; the finite eigenbasis index set in the cubic trace expansion", def "$k$ indexes dyadic scales in $\cD_k$, $\cA_k$, and the local forms and energies; in $\tr((DM)^3)=\sum_{i,j,k}m_im_jm_kD_{ij}D_{jk}D_{ki}$, it indexes the chosen orthonormal eigenbasis of $M$." (The entry describes the dyadic use correctly but misses the locally bound eigenbasis index in the cubic trace expansion. This is contextual reuse, rather than a replacement of the dyadic convention.)
- note on `symbol K`: symbol table corrected: def "A symmetric matrix $K$ is supported on $P$ if it annihilates $\ker P$. Symmetry then also puts its range in $\supp P$." (The recorded entry invokes support without defining it. The paper explicitly requires annihilation of the kernel, which determines the admissible directions in the Hessian form.)
- note on `symbol Q`: symbol table corrected: type "positive semidefinite comparison matrix or local nonnegative scalar", space "$\{A\in\R^{d\times d}:A=A^*,\ A\ge0\}\cup[0,\infty)$", def "In Lemma~\ref{lem:order}, $Q$ is a positive semidefinite matrix on the same space as $P$, with $P\le aQ$; in the proof of Proposition~\ref{prop:trace}, $Q=\sum_{i,j:\,q_i+q_j>0}\frac{q_i^2q_j^2}{q_i+q_j}\abs{D_{ij}}^2$." (The recorded entry covers only the comparison matrix. The trace proof independently defines a scalar quadratic quantity with the same letter; the two meanings are local and unambiguous.)

### V1 lint warnings

- lem:order: lem:order references \ref{lem:hessian} (lem:hessian) but `depends_on` lacks ass:hessian-positive-support, ass:hessian-direction; V1.5 must confirm whether the paper assumes it or merely mentions it
- thm:gap: cor:gap references \ref{lem:hessian} (lem:hessian) but `depends_on` lacks ass:hessian-positive-support, ass:hessian-direction; V1.5 must confirm whether the paper assumes it or merely mentions it
- thm:gap: cor:gap references \ref{lem:order} (lem:order) but `depends_on` lacks ass:order-matrices, ass:order-factor, ass:order-comparison, ass:order-direction; V1.5 must confirm whether the paper assumes it or merely mentions it
- prop:trace: prop:trace references \ref{lem:order} (lem:order) but `depends_on` lacks ass:order-matrices, ass:order-factor, ass:order-comparison, ass:order-direction; V1.5 must confirm whether the paper assumes it or merely mentions it
- prop:increase: prop:increase references \ref{lem:hessian} (lem:hessian) but `depends_on` lacks ass:hessian-positive-support, ass:hessian-direction; V1.5 must confirm whether the paper assumes it or merely mentions it
- prop:increase: prop:increase references \ref{cor:gap} (cor:gap) but `depends_on` lacks ass:gap-positive, ass:gap-symmetry, ass:gap-order; V1.5 must confirm whether the paper assumes it or merely mentions it
- prop:increase: prop:increase references \ref{prop:trace} (prop:trace) but `depends_on` lacks ass:trace-symmetry, ass:trace-contraction, def:trace-perturbation; V1.5 must confirm whether the paper assumes it or merely mentions it
- thm:main: thm:main references \ref{prop:increase} (prop:increase) but `depends_on` lacks ass:increase-triple, ass:increase-scale, def:energy-increment; V1.5 must confirm whether the paper assumes it or merely mentions it
- thm:main: thm:main references \ref{lem:total} (lem:total) but `depends_on` lacks ass:total-scale, ass:total-telescope-scale, def:total-energy; V1.5 must confirm whether the paper assumes it or merely mentions it
- thm:main: thm:main references \ref{lem:continuity} (lem:continuity) but `depends_on` lacks ass:continuity-scale, ass:continuity-inputs; V1.5 must confirm whether the paper assumes it or merely mentions it

### Parser warnings

- sections/05-summation.tex:125: a second \begin{proof} for thm:main; appended to that result's proof (the locator names the first proof only)

## Lean evidence

- build of the run barrel: **ok**
- source scan (sorry / admit / axiom): clean

| declaration | axioms |
| --- | --- |
| `Papers.OaiBoundDyadicTriangular.dyadic_triangular_bound` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiBoundDyadicTriangular.matrixEnergy_hessian` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiBoundDyadicTriangular.hessForm_order` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiBoundDyadicTriangular.matrixEnergy_midpoint_gap` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiBoundDyadicTriangular.abs_trace_le_hessForm_sum` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiBoundDyadicTriangular.energyIncrement_controls_trace` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiBoundDyadicTriangular.totalEnergy_bound_and_telescope` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiBoundDyadicTriangular.localForm_one_scale_bound` | clean — `propext`, `Classical.choice`, `Quot.sound` |

## Inputs

| artifact | status |
| --- | --- |
| `discovery/v1_scope.json` | present (8 environment(s)) |
| `discovery/v1_5_review.json` | present (verdict PASS) |
| `formalization/crosswalk_full.json` | present (408 object(s)) |
| `graph.json` | present (410 node(s)) |
| Lean evidence | collected (build ok, 0 scan issue(s), 406 declaration(s)) |

## Annotated paper

Annotated paper: `annotated/main.tex` (22 annotation(s), 0 unlocated; index `annotated/ANNOTATIONS.md`); PDF: `annotated/main.pdf`
