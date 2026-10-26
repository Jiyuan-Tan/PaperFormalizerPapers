# Correctness report — oai_sharp_threshold_monotone

**Verdict: NO ERROR FOUND**

**Paper: MINOR ISSUES — no main result is shown false or weakened**

Minor:

- `\mathcal P`: notation ambiguous; a reading was pinned
- `a`: notation ambiguous; a reading was pinned
- `p_a(\mathcal P)`: notation ambiguous; a reading was pinned
- `f`: notation ambiguous; a reading was pinned
- `x`: notation ambiguous; a reading was pinned
- `b`: notation ambiguous; a reading was pinned
- `S`: notation ambiguous; a reading was pinned
- `m`: notation ambiguous; a reading was pinned
- `k`: notation ambiguous; a reading was pinned
- `y`: notation ambiguous; a reading was pinned
- `f_y`: notation ambiguous; a reading was pinned
- `A`: notation ambiguous; a reading was pinned
- `\widehat{f_y}(A)`: notation ambiguous; a reading was pinned
- `I(f_y)`: notation ambiguous; a reading was pinned
- `B`: notation ambiguous; a reading was pinned
- `u`: notation ambiguous; a reading was pinned
- `v`: notation ambiguous; a reading was pinned
- `I_e(f_y)`: notation ambiguous; a reading was pinned
- `s`: notation ambiguous; a reading was pinned
- `d_S(u)`: notation ambiguous; a reading was pinned

6 result(s) of the paper were examined. None was found wrong as printed. In Lean: 6 proved, 0 taken from the literature as cited, 0 not certified, 0 not formalized.

## What was wrong and what was done

No error was found in the results examined.

## Clarifications (not errors)

Nothing in this section is an error of the paper. Each item is something the paper determines but does not say, made explicit so that the statements can be read, and formalized, in one way.

**Notation.**

- $\mathcal P$: $\mathcal P\subseteq\{0,1\}^{E_n}$ is a graph family invariant under every permutation of $[n]$. In Theorem~\ref{thm:threshold}: $\mathcal P$ is increasing under addition of edges and satisfies $\varnothing\ne\mathcal P\ne\{0,1\}^{E_n}$.
- $a$: In $p_a(\mathcal P)$, $a\in(0,1)$ is the probability level in the defining inequality $\mu_p(\mathcal P)\ge a$. In Lemma~\ref{lem:low-degree}: In the scalar two-point inequality, $a$ is an arbitrary real scalar. In tensorization, the same letter locally denotes the real-valued coefficient function on $\{0,1\}^{J\setminus\{i\}}$ in $g=a+b\chi_i$; this is a function of the remaining coordinates.
- $p_a(\mathcal P)$: For $0<a<1$, $p_a(\mathcal P)=\inf\{p\in[0,1]:\mu_p(\mathcal P)\ge a\}$ whenever this defining set is nonempty. In Theorem~\ref{thm:threshold}: $p_a(\mathcal P)\in(0,1)$ is the unique solution of $\mu_{p_a(\mathcal P)}(\mathcal P)=a$ for every $0<a<1$.
- $f$: $f$ is a Boolean function $f:\{0,1\}^{E_n}\to\{0,1\}$. In Theorem~\ref{thm:threshold}: $f=\1_{\mathcal P}$, where $\mathcal P$ is the nontrivial increasing graph property under consideration. In Proposition~\ref{prop:block}, Lemma~\ref{lem:block-capture}, Theorem~\ref{thm:variance}: $f$ is invariant under every permutation of $[n]$; monotonicity is not assumed. In Lemma~\ref{lem:restriction}: $f$ is an arbitrary Boolean function on $\{0,1\}^{E_n}$; neither symmetry nor monotonicity is assumed.
- $x$: $x$ denotes an argument configuration on the coordinate set of the function being evaluated; in $x_{e\leftarrow b}$ it is a graph configuration in $\{0,1\}^{E_n}$. In Lemma~\ref{lem:low-degree}: In the Fourier characters, $x\in\{0,1\}^{J}$; as an argument of $\Delta_i g$, $x$ ranges over the remaining coordinates $J\setminus\{i\}$. In Lemma~\ref{lem:restriction}: In $f_y(x)=f(x,y)$, $x\in\{0,1\}^{F}$ is the free-coordinate configuration, while $y\in\{0,1\}^{H}$ specifies the exterior coordinates.
- $b$: In the notation $x_{e\leftarrow b}$, $b\in\{0,1\}$ is the value assigned to coordinate $e$. In Lemma~\ref{lem:low-degree}: In the scalar two-point inequality, $b$ is an arbitrary real scalar. In tensorization, the same letter locally denotes the real-valued coefficient function on $\{0,1\}^{J\setminus\{i\}}$ in $g=a+b\chi_i$; this is a function of the remaining coordinates.
- $S$: $S$ is a subset of the coordinate set indexing a product Fourier character or coefficient. In Lemma~\ref{lem:low-degree}: $S\subseteq J$; the low-degree sum ranges over $1\le |S|\le k$, interpreted literally for integer $|S|$. In Lemma~\ref{lem:restriction}, Proposition~\ref{prop:block}, Lemma~\ref{lem:block-capture}, Theorem~\ref{thm:variance}: The original graph Fourier indices satisfy $S\subseteq E_n$, so $S$ can also be viewed as the edge set of a simple graph on $[n]$. In Lemma~\ref{lem:block-capture}: The support-selection argument fixes each nonempty $S$ with $|S|\le k^2/2$ separately; no single block is required to capture all such supports.
- $m$: $m\ge2$ is a numerical parameter whose admissible values and choice depend on its local use. In Lemma~\ref{lem:low-degree}: $m$ is any real number at least $2$ satisfying the stipulated comparison $I_i(h)\le I(h)/m$ for every $i\in J$. In Proposition~\ref{prop:block}: $m$ is an integer with $3\le m\le n$ and is the cardinality of the vertex block. In Lemma~\ref{lem:block-capture}: $m=\lfloor\sqrt n\rfloor$, under the assumption $\log n\ge16$. In Theorem~\ref{thm:variance}: In the proof branch $\log n\ge16$, $m=\lfloor\sqrt n\rfloor$; the branch $2\le n<e^{16}$ does not use $m$.
- $k$: $k$ denotes a positive real degree cutoff, with comparisons to integer cardinalities interpreted literally rather than requiring $k$ to be an integer. In Lemma~\ref{lem:low-degree}: $k=\sigma\log m/64$, where $m\ge2$ is the real influence comparison parameter. In Lemma~\ref{lem:restriction}: $k$ is any positive real number, with no required relation to an influence comparison parameter. In Proposition~\ref{prop:block}: $k=\sigma\log m/64$, where $m$ is the integer block size satisfying $3\le m\le n$. In Lemma~\ref{lem:block-capture}, Theorem~\ref{thm:variance}: When $t=\log n\ge16$, $m=\lfloor\sqrt n\rfloor$ and $k=\sigma\log m/64$; the original Fourier levels are split at $k^2/2$.
- $y$: $y\in\{0,1\}^{H}$ denotes the exterior assignment, held fixed when defining or evaluating the restricted function $f_y$ and integrated out when an exterior expectation $\E_y$ is taken. In Proposition~\ref{prop:block}: The exterior coordinate set is $H_B=E_n\setminus F_B$, consisting of the edges with both endpoints outside $B$.
- $f_y$: For each fixed exterior assignment $y\in\{0,1\}^{H}$, $f_y:\{0,1\}^{F}\to\{0,1\}$ is the function $x\mapsto f(x,y)$, where $(x,y)$ is the configuration on $E_n=F\cup H$. In Proposition~\ref{prop:block}: Here $F=F_B=\{e\in E_n:e\cap B\ne\varnothing\}$ and $H=H_B=E_n\setminus F_B$; for every exterior assignment $y$, $f_y$ is invariant under permutations supported on $B$.
- $A$: $A$ is locally bound notation denoting either a Fourier index set on the indicated coordinates or the transformed function $T_\rho a$, according to its surrounding definition. In Lemma~\ref{lem:low-degree}: In the derivative coefficient identities and sums, $A\subseteq J\setminus\{i\}$. Within the tensorization argument, $A=T_\rho a$ is instead a real function on the coordinates $J\setminus\{i\}$. In Lemma~\ref{lem:restriction}: $A\subseteq F$ indexes the Fourier coefficients of $f_y$ on the free coordinates; the displayed mass sum restricts it to $1\le |A|\le k$, while the coefficient expansion holds for every $A\subseteq F$.
- $\widehat{f_y}(A)$: For $A\subseteq F$ and $y\in\{0,1\}^{H}$, where $H=E_n\setminus F$, $\widehat{f_y}(A)=\E_{x\sim\mathrm{Bernoulli}(p)^{\otimes F}}[f(x,y)\chi_A(x)]$; this integrates only the free coordinates and retains its dependence on $y$.
- $I(f_y)$: $I(f_y)=\sum_{e\in F}\Pr_p\bigl(f_y(x_{e\leftarrow1})\ne f_y(x_{e\leftarrow0})\bigr)$, with $y$ held fixed and each pivotal probability integrating only the coordinates in $F\setminus\{e\}$. In Proposition~\ref{prop:block}: The free coordinate set is $F_B=\{e\in E_n:e\cap B\ne\varnothing\}$, and $I(f_y)$ is evaluated with both $B$ and its exterior assignment $y$ fixed before averaging.
- $B$: The notation $B$ is local to its context, denoting either the auxiliary function $T_\rho b$ or an $m$-element vertex block. In Lemma~\ref{lem:low-degree}: In the tensorization proof, $B=T_\rho b$ is a real function on the coordinates other than $i$, where $g=a+b\chi_i$. In Proposition~\ref{prop:block}: $B\in\binom{[n]}m$, with integer $3\le m\le n$. In Lemma~\ref{lem:block-capture}: The proof uses $B\in\binom{[n]}m$ with $m=\lfloor\sqrt n\rfloor$.
- $u$: The notation $u$ is local to its context, denoting a real function in the projection argument or a vertex in the graph arguments. In Lemma~\ref{lem:low-degree}: $u$ is a real function on $\{0,1\}^J$ satisfying $u=P_{\le d}u$; in the supremum defining the projection norm it also satisfies $\|u\|_2=1$. In Proposition~\ref{prop:block}: In $\{\{u,w\}:u\in B\}$, $u$ ranges over all vertices of $B$. In Lemma~\ref{lem:block-capture}: For each fixed nonempty $S\subseteq E_n$ with $|S|\le k^2/2$, choose $u\in V(S)$ with $d_S(u)\le 2|S|/|V(S)|$. This choice may depend on $S$ and is made before choosing the block; $B\cap V(S)=\{u\}$ is an event, rather than a condition defining $u$.
- $v$: $v$ is local notation for either a real function or a number of nonisolated vertices, according to its scope. In Lemma~\ref{lem:low-degree}: $v$ is an arbitrary real function on $\{0,1\}^J$ to which $P_{\le d}$ is applied. In Lemma~\ref{lem:block-capture}: For the fixed nonempty edge set $S\subseteq E_n$, $v=|V(S)|$ is the number of its nonisolated vertices.
- $I_e(f_y)$: For $e\in F$ and each fixed exterior assignment $y\in\{0,1\}^{H}$, $I_e(f_y)$ is the probability, over the remaining free coordinates with Bernoulli-$p$ product law, that changing coordinate $e$ changes $f_y$.
- $s$: $s$ is a positive scalar whose meaning is local to the argument. In Lemma~\ref{lem:low-degree}: $s$ is a real argument in $(0,1/2]$ for the function $s\mapsto s\log(4/s)$. In Lemma~\ref{lem:block-capture}: $s=|S|$ is the positive integer number of edges of the fixed support graph, with $1\le s\le k^2/2$.
- $d_S(u)$: $d_S(u)$ is the degree of $u$ in the simple graph with edge set $S$. In Lemma~\ref{lem:block-capture}: For each fixed nonempty support $S$ under consideration, $u\in V(S)$ is chosen with $d_S(u)\le 2|S|/|V(S)|$, so $1\le d_S(u)\le\sqrt{2|S|}\le k$.

## What was proved in Lean, and what was not

A result is proved in Lean when a Lean declaration reviewed as stating it has a complete proof using no axiom beyond the standard ones. For a corrected result, the corrected statement is the one formalized.

| Result | Formal status | Lean declaration | Axioms |
| --- | --- | --- | --- |
| Theorem 1.1 | proved in Lean | `Papers.OaiSharpThresholdMonotone.propertyQuantile_width_le` (`TThreshold.lean:48`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Theorem 1.2 | proved in Lean | `Papers.OaiSharpThresholdMonotone.variance_le_log_sq_inv_mul_totalInfluence` (`TVariance.lean:18`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 2.1 | proved in Lean | `Papers.OaiSharpThresholdMonotone.sum_lowDegree_fourierCoeff_sq_le` (`Helpers/LowDegree.lean:215`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 3.1 | proved in Lean | `Papers.OaiSharpThresholdMonotone.restriction_mass_and_influence` (`Helpers/Restriction.lean:233`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Proposition 3.2 | proved in Lean | `Papers.OaiSharpThresholdMonotone.block_average_lowDegree_mass_le` (`Helpers/BlockAverage.lean:150`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 3.3 | proved in Lean | `Papers.OaiSharpThresholdMonotone.captured_lowDegree_mass_le` (`Helpers/BlockCapture.lean:19`) | the standard ones only (propext, Classical.choice, Quot.sound) |

The Lean development builds; it contains no `sorry`, `admit` or added axiom.

## The corrected paper

`bundle/corrected_paper/` holds the paper as it reads after the corrections, as plain source in the author's own class and layout, compiled to `bundle/corrected_paper/main.pdf` (12 pages). `bundle/MATCH.md` sets each result beside its Lean declaration; `bundle/lean/` holds the Lean code.

The mechanical checks leave nothing open.

# Technical appendix

The records behind the report above, by the run's own identifiers.

- paper: `main.tex` (source sha256 `f221dd0a595568d1b088637af795c26f3565ad2ed197f8301906386dcabc0312`)
- stage completed: `5`
- results in scope: 6

| bucket | count |
| --- | --- |
| verified | 6 |
| verified_with_bookkeeping | 0 |
| conditional | 0 |
| repaired | 0 |
| unresolved | 0 |
| not_checked | 0 |
| not_determined | 0 |
| refuted | 0 |

> This is a conditional report. A `verified` result is verified only up to the cited results it assumes, the substrate gates left assumed, and the conditions added during formalization — all listed in full below. `unresolved` means the formalization did not close; it is NOT a claim that the result is wrong. A `refuted` row is a result shown false by a positive witness with no confirmed repair; a `repaired` row was false as printed, and an independent referee confirmed its minimal repair. A `not_determined` row could not be checked as printed: the paper does not say enough to determine the claim, and no reading or repair was adopted; it is NOT a claim that the result is wrong.

## Results

### 1. Friedgut--Kalai sharp-threshold conjecture `thm:threshold`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `sections/introduction.tex:12-20` (`theorem`, label `thm:threshold`) |
| statement | \label{thm:threshold} For every integer $n\ge2$, every nontrivial increasing family $\mathcal P$ of graphs on $n$ vertices invariant under all vertex permutations, and every $0<\varepsilon<1/2$, \begin{equation} \label{eq:threshold} p_{1-\varepsilon}(\mathcal P)-p_\varepsilon(\mathcal P) \le \frac{2^{19}}{(\log n)^2}\log\frac1{2\varepsilon}. \end{equation} |
| appended hypothesis list | ass:threshold-n, ass:threshold-property, ass:threshold-epsilon |
| Lean | `TThreshold.lean:48` — `Papers.OaiSharpThresholdMonotone.propertyQuantile_width_le` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 2. Variance and influence `thm:variance`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `sections/introduction.tex:70-78` (`theorem`, label `thm:variance`) |
| statement | \label{thm:variance} For every integer $n\ge2$, every Boolean function $f$ on $E_n$ invariant under vertex permutations, and every $0<p<1$, \begin{equation} \label{eq:variance} \Var_p(f)\le\frac{2^{17}}{(\log n)^2}I_p(f). \end{equation} No monotonicity assumption is needed. |
| appended hypothesis list | ass:variance-n, ass:variance-symmetry, ass:variance-bias |
| Lean | `TVariance.lean:18` — `Papers.OaiSharpThresholdMonotone.variance_le_log_sq_inv_mul_totalInfluence` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 3. `lem:low-degree`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `sections/fourier.tex:58-70` (`lemma`, label `lem:low-degree`) |
| statement | \label{lem:low-degree} Let $m\ge2$ be real and let $h:\{0,1\}^J\to\{0,1\}$ satisfy $I_i(h)\le I(h)/m$ for every $i\in J$. If \[ k=\frac{\sigma\log m}{64}, \] then \begin{equation}\label{eq:low-degree} \sum_{1\le \|S\|\le k}\widehat h(S)^2\le m^{-1/4}I(h). \end{equation} Every degree cutoff is interpreted literally for integer degrees $\|S\|$; in particular, the sum is empty when $k<1$. |
| appended hypothesis list | ass:finite-coordinate-set, ass:interior-bias, ass:low-degree-m, ass:low-degree-small-influences, ass:low-degree-cutoff |
| Lean | `Helpers/LowDegree.lean:215` — `Papers.OaiSharpThresholdMonotone.sum_lowDegree_fourierCoeff_sq_le` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 4. Exact averaging over a restriction `lem:restriction`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `sections/graph.tex:25-40` (`lemma`, label `lem:restriction`) |
| statement | \label{lem:restriction} Let $F\subseteq E_n$, put $H=E_n\setminus F$, and, for $y\in\{0,1\}^{H}$, let $f_y(x)=f(x,y)$ for $x\in\{0,1\}^{F}$. If $y$ has the Bernoulli-$p$ product law, then, for every real $k>0$, \begin{align} \E_y\sum_{\substack{A\subseteq F\\1\le \|A\|\le k}} \widehat{f_y}(A)^2 &=\sum_{\substack{S\subseteq E_n\\1\le\|S\cap F\|\le k}} \widehat f(S)^2, \label{eq:restriction-mass}\\ \E_y I(f_y)&=\sum_{e\in F}I_e(f). \label{eq:restriction-influence} \end{align} |
| appended hypothesis list | ass:interior-bias, ass:restriction-boolean-function, ass:restriction-free-edges, ass:restriction-law, ass:restriction-cutoff |
| Lean | `Helpers/Restriction.lean:233` — `Papers.OaiSharpThresholdMonotone.restriction_mass_and_influence` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 5. The block estimate `prop:block`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `sections/graph.tex:62-77` (`proposition`, label `prop:block`) |
| statement | \label{prop:block} Let $3\le m\le n$ be an integer, let $B$ be uniform among the $m$-element subsets of $[n]$, and set \[ F_B=\{e\in E_n:e\cap B\ne\varnothing\}, \qquad k=\frac{\sigma\log m}{64}. \] Then \begin{equation} \sum_{S\subseteq E_n} \Pr_B\{1\le \|S\cap F_B\|\le k\}\widehat f(S)^2 \le \frac{2m}{n}\,m^{-1/4}I(f). \label{eq:block-average} \end{equation} |
| appended hypothesis list | ass:interior-bias, ass:graph-symmetry, ass:block-m, ass:block-law |
| Lean | `Helpers/BlockAverage.lean:150` — `Papers.OaiSharpThresholdMonotone.block_average_lowDegree_mass_le` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 6. Capturing low Fourier levels `lem:block-capture`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `sections/graph.tex:111-125` (`lemma`, label `lem:block-capture`) |
| statement | \label{lem:block-capture} Suppose $t=\log n\ge16$, and put \[ m=\lfloor\sqrt n\rfloor, \qquad k=\frac{\sigma\log m}{64}. \] Then \begin{equation} \sum_{\substack{S\subseteq E_n\\1\le \|S\|\le k^2/2}} \widehat f(S)^2 \le 4m^{-1/4}I(f). \label{eq:captured-mass} \end{equation} |
| appended hypothesis list | ass:interior-bias, ass:graph-symmetry, ass:block-capture-size |
| Lean | `Helpers/BlockCapture.lean:19` — `Papers.OaiSharpThresholdMonotone.captured_lowDegree_mass_le` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

## Suggestions to the authors

Not errors: readings the paper determines but does not state, and side conditions the proofs use silently.

- reading of the symbol `\mathcal P`: $\mathcal P\subseteq\{0,1\}^{E_n}$ is a graph family invariant under every permutation of $[n]$. In Theorem~\ref{thm:threshold}: $\mathcal P$ is increasing under addition of edges and satisfies $\varnothing\ne\mathcal P\ne\{0,1\}^{E_n}$. — The introduction defines graph properties by permutation invariance and separately defines increasing and nontrivial. Theorem~\ref{thm:threshold} explicitly imposes both additional conditions.
- reading of the symbol `a`: In $p_a(\mathcal P)$, $a\in(0,1)$ is the probability level in the defining inequality $\mu_p(\mathcal P)\ge a$. In Lemma~\ref{lem:low-degree}: In the scalar two-point inequality, $a$ is an arbitrary real scalar. In tensorization, the same letter locally denotes the real-valued coefficient function on $\{0,1\}^{J\setminus\{i\}}$ in $g=a+b\chi_i$; this is a function of the remaining coordinates. — The introduction specifies "For $0<a<1$, define" before the quantile display. The proof of Lemma~\ref{lem:low-degree} introduces real scalars $a,b$ and subsequently functions $a,b$ in the tensorization argument.
- reading of the symbol `p_a(\mathcal P)`: For $0<a<1$, $p_a(\mathcal P)=\inf\{p\in[0,1]:\mu_p(\mathcal P)\ge a\}$ whenever this defining set is nonempty. In Theorem~\ref{thm:threshold}: $p_a(\mathcal P)\in(0,1)$ is the unique solution of $\mu_{p_a(\mathcal P)}(\mathcal P)=a$ for every $0<a<1$. — The introduction defines the infimum for $0<a<1$. The proof of Theorem~\ref{thm:threshold} establishes endpoint probabilities zero and one and strict increase on $(0,1)$, concluding that every quantile is the unique interior point with probability $a$.
- reading of the symbol `f`: $f$ is a Boolean function $f:\{0,1\}^{E_n}\to\{0,1\}$. In Theorem~\ref{thm:threshold}: $f=\1_{\mathcal P}$, where $\mathcal P$ is the nontrivial increasing graph property under consideration. In Proposition~\ref{prop:block}, Lemma~\ref{lem:block-capture}, Theorem~\ref{thm:variance}: $f$ is invariant under every permutation of $[n]$; monotonicity is not assumed. In Lemma~\ref{lem:restriction}: $f$ is an arbitrary Boolean function on $\{0,1\}^{E_n}$; neither symmetry nor monotonicity is assumed. — Immediately before Lemma~\ref{lem:restriction}, the paper states: "The next identities hold for every Boolean $f$, without a symmetry assumption." The symmetry assumption remains in force for Proposition~\ref{prop:block}, Lemma~\ref{lem:block-capture}, and Theorem~\ref{thm:variance}.
- reading of the symbol `x`: $x$ denotes an argument configuration on the coordinate set of the function being evaluated; in $x_{e\leftarrow b}$ it is a graph configuration in $\{0,1\}^{E_n}$. In Lemma~\ref{lem:low-degree}: In the Fourier characters, $x\in\{0,1\}^{J}$; as an argument of $\Delta_i g$, $x$ ranges over the remaining coordinates $J\setminus\{i\}$. In Lemma~\ref{lem:restriction}: In $f_y(x)=f(x,y)$, $x\in\{0,1\}^{F}$ is the free-coordinate configuration, while $y\in\{0,1\}^{H}$ specifies the exterior coordinates. — The coordinate-replacement definition uses the graph cube. The product Fourier basis uses $\{0,1\}^{J}$, and the coordinate-difference definition explicitly makes $\Delta_i g$ a function on the remaining coordinates. Lemma~\ref{lem:restriction} explicitly specifies $x\in\{0,1\}^{F}$.
- reading of the symbol `b`: In the notation $x_{e\leftarrow b}$, $b\in\{0,1\}$ is the value assigned to coordinate $e$. In Lemma~\ref{lem:low-degree}: In the scalar two-point inequality, $b$ is an arbitrary real scalar. In tensorization, the same letter locally denotes the real-valued coefficient function on $\{0,1\}^{J\setminus\{i\}}$ in $g=a+b\chi_i$; this is a function of the remaining coordinates. — The coordinate-replacement definition specifies $b\in\{0,1\}$. The proof of Lemma~\ref{lem:low-degree} subsequently says "For real $a,b$" and then introduces coefficient functions in $g=a+b\chi_i$.
- reading of the symbol `S`: $S$ is a subset of the coordinate set indexing a product Fourier character or coefficient. In Lemma~\ref{lem:low-degree}: $S\subseteq J$; the low-degree sum ranges over $1\le \|S\|\le k$, interpreted literally for integer $\|S\|$. In Lemma~\ref{lem:restriction}, Proposition~\ref{prop:block}, Lemma~\ref{lem:block-capture}, Theorem~\ref{thm:variance}: The original graph Fourier indices satisfy $S\subseteq E_n$, so $S$ can also be viewed as the edge set of a simple graph on $[n]$. In Lemma~\ref{lem:block-capture}: The support-selection argument fixes each nonempty $S$ with $\|S\|\le k^2/2$ separately; no single block is required to capture all such supports. — The Fourier setup defines characters for $S\subseteq J$. The graph sums explicitly use $S\subseteq E_n$, and the proof of Lemma~\ref{lem:block-capture} fixes a nonempty support with $\|S\|\le k^2/2$.
- reading of the symbol `m`: $m\ge2$ is a numerical parameter whose admissible values and choice depend on its local use. In Lemma~\ref{lem:low-degree}: $m$ is any real number at least $2$ satisfying the stipulated comparison $I_i(h)\le I(h)/m$ for every $i\in J$. In Proposition~\ref{prop:block}: $m$ is an integer with $3\le m\le n$ and is the cardinality of the vertex block. In Lemma~\ref{lem:block-capture}: $m=\lfloor\sqrt n\rfloor$, under the assumption $\log n\ge16$. In Theorem~\ref{thm:variance}: In the proof branch $\log n\ge16$, $m=\lfloor\sqrt n\rfloor$; the branch $2\le n<e^{16}$ does not use $m$. — Lemma~\ref{lem:low-degree} allows real $m\ge2$; Proposition~\ref{prop:block} specifies integer $3\le m\le n$; Lemma~\ref{lem:block-capture} sets $m=\lfloor\sqrt n\rfloor$; the large-$n$ branch of the proof of Theorem~\ref{thm:variance} adopts that choice.
- reading of the symbol `k`: $k$ denotes a positive real degree cutoff, with comparisons to integer cardinalities interpreted literally rather than requiring $k$ to be an integer. In Lemma~\ref{lem:low-degree}: $k=\sigma\log m/64$, where $m\ge2$ is the real influence comparison parameter. In Lemma~\ref{lem:restriction}: $k$ is any positive real number, with no required relation to an influence comparison parameter. In Proposition~\ref{prop:block}: $k=\sigma\log m/64$, where $m$ is the integer block size satisfying $3\le m\le n$. In Lemma~\ref{lem:block-capture}, Theorem~\ref{thm:variance}: When $t=\log n\ge16$, $m=\lfloor\sqrt n\rfloor$ and $k=\sigma\log m/64$; the original Fourier levels are split at $k^2/2$. — Lemma~\ref{lem:low-degree} explicitly states the integer-degree convention; Lemma~\ref{lem:restriction} permits every positive real cutoff; Proposition~\ref{prop:block}, Lemma~\ref{lem:block-capture}, and the proof of Theorem~\ref{thm:variance} specify their local choices.
- reading of the symbol `y`: $y\in\{0,1\}^{H}$ denotes the exterior assignment, held fixed when defining or evaluating the restricted function $f_y$ and integrated out when an exterior expectation $\E_y$ is taken. In Proposition~\ref{prop:block}: The exterior coordinate set is $H_B=E_n\setminus F_B$, consisting of the edges with both endpoints outside $B$. — The proof of Proposition~\ref{prop:block} specifies $H_B$ as the edges with both endpoints outside $B$. Lemma~\ref{lem:block-capture} is no longer listed as using $y$.
- reading of the symbol `f_y`: For each fixed exterior assignment $y\in\{0,1\}^{H}$, $f_y:\{0,1\}^{F}\to\{0,1\}$ is the function $x\mapsto f(x,y)$, where $(x,y)$ is the configuration on $E_n=F\cup H$. In Proposition~\ref{prop:block}: Here $F=F_B=\{e\in E_n:e\cap B\ne\varnothing\}$ and $H=H_B=E_n\setminus F_B$; for every exterior assignment $y$, $f_y$ is invariant under permutations supported on $B$. — Lemma~\ref{lem:restriction} defines the function for each exterior assignment; the proof of Proposition~\ref{prop:block} fixes a block and an arbitrary assignment on $H_B$ before applying the restriction.
- reading of the symbol `A`: $A$ is locally bound notation denoting either a Fourier index set on the indicated coordinates or the transformed function $T_\rho a$, according to its surrounding definition. In Lemma~\ref{lem:low-degree}: In the derivative coefficient identities and sums, $A\subseteq J\setminus\{i\}$. Within the tensorization argument, $A=T_\rho a$ is instead a real function on the coordinates $J\setminus\{i\}$. In Lemma~\ref{lem:restriction}: $A\subseteq F$ indexes the Fourier coefficients of $f_y$ on the free coordinates; the displayed mass sum restricts it to $1\le \|A\|\le k$, while the coefficient expansion holds for every $A\subseteq F$. — The derivative coefficient identity specifies $A\subseteq J\setminus\{i\}$; the tensorization proof subsequently sets $A=T_\rho a$; Lemma~\ref{lem:restriction} sums over $A\subseteq F$.
- reading of the symbol `\widehat{f_y}(A)`: For $A\subseteq F$ and $y\in\{0,1\}^{H}$, where $H=E_n\setminus F$, $\widehat{f_y}(A)=\E_{x\sim\mathrm{Bernoulli}(p)^{\otimes F}}[f(x,y)\chi_A(x)]$; this integrates only the free coordinates and retains its dependence on $y$. — Lemma~\ref{lem:restriction} defines $f_y(x)=f(x,y)$, and its proof integrates over $x$ to obtain $\widehat{f_y}(A)=\sum_{D\subseteq H}\widehat f(A\cup D)\chi_D(y)$.
- reading of the symbol `I(f_y)`: $I(f_y)=\sum_{e\in F}\Pr_p\bigl(f_y(x_{e\leftarrow1})\ne f_y(x_{e\leftarrow0})\bigr)$, with $y$ held fixed and each pivotal probability integrating only the coordinates in $F\setminus\{e\}$. In Proposition~\ref{prop:block}: The free coordinate set is $F_B=\{e\in E_n:e\cap B\ne\varnothing\}$, and $I(f_y)$ is evaluated with both $B$ and its exterior assignment $y$ fixed before averaging. — The definition of pivotal influence and the proof of Lemma~\ref{lem:restriction} identify the restricted pivotal event with the original event with exterior coordinates fixed; the proof of Proposition~\ref{prop:block} applies this with the free set $F_B$.
- reading of the symbol `B`: The notation $B$ is local to its context, denoting either the auxiliary function $T_\rho b$ or an $m$-element vertex block. In Lemma~\ref{lem:low-degree}: In the tensorization proof, $B=T_\rho b$ is a real function on the coordinates other than $i$, where $g=a+b\chi_i$. In Proposition~\ref{prop:block}: $B\in\binom{[n]}m$, with integer $3\le m\le n$. In Lemma~\ref{lem:block-capture}: The proof uses $B\in\binom{[n]}m$ with $m=\lfloor\sqrt n\rfloor$. — The tensorization proof writes $g=a+b\chi_i$ and sets $B=T_\rho b$ at lines 243--246. The vertex-block definition at lines 381--382 and the choice in the block-capture proof specify the other use.
- reading of the symbol `u`: The notation $u$ is local to its context, denoting a real function in the projection argument or a vertex in the graph arguments. In Lemma~\ref{lem:low-degree}: $u$ is a real function on $\{0,1\}^J$ satisfying $u=P_{\le d}u$; in the supremum defining the projection norm it also satisfies $\\|u\\|_2=1$. In Proposition~\ref{prop:block}: In $\{\{u,w\}:u\in B\}$, $u$ ranges over all vertices of $B$. In Lemma~\ref{lem:block-capture}: For each fixed nonempty $S\subseteq E_n$ with $\|S\|\le k^2/2$, choose $u\in V(S)$ with $d_S(u)\le 2\|S\|/\|V(S)\|$. This choice may depend on $S$ and is made before choosing the block; $B\cap V(S)=\{u\}$ is an event, rather than a condition defining $u$. — The projection argument specifies $u=P_{\le d}u$ and the unit-norm supremum in \eqref{eq:projection-norm}; the orbit description uses $u\in B$; the support argument explicitly chooses $u\in V(S)$ and later states that its choice may depend on $S$.
- reading of the symbol `v`: $v$ is local notation for either a real function or a number of nonisolated vertices, according to its scope. In Lemma~\ref{lem:low-degree}: $v$ is an arbitrary real function on $\{0,1\}^J$ to which $P_{\le d}$ is applied. In Lemma~\ref{lem:block-capture}: For the fixed nonempty edge set $S\subseteq E_n$, $v=\|V(S)\|$ is the number of its nonisolated vertices. — The proof of Lemma~\ref{lem:low-degree} introduces the projection estimate for every real function $v$; the proof of Lemma~\ref{lem:block-capture} explicitly writes $v=\|V(S)\|$.
- reading of the symbol `I_e(f_y)`: For $e\in F$ and each fixed exterior assignment $y\in\{0,1\}^{H}$, $I_e(f_y)$ is the probability, over the remaining free coordinates with Bernoulli-$p$ product law, that changing coordinate $e$ changes $f_y$. — The proof of Lemma~\ref{lem:restriction} identifies this pivotal event with that for $f$ with exterior coordinates fixed to $y$, and then averages over $y$ separately.
- reading of the symbol `s`: $s$ is a positive scalar whose meaning is local to the argument. In Lemma~\ref{lem:low-degree}: $s$ is a real argument in $(0,1/2]$ for the function $s\mapsto s\log(4/s)$. In Lemma~\ref{lem:block-capture}: $s=\|S\|$ is the positive integer number of edges of the fixed support graph, with $1\le s\le k^2/2$. — The proof of Lemma~\ref{lem:low-degree} considers $s\mapsto s\log(4/s)$ on $(0,1/2]$. The proof of Lemma~\ref{lem:block-capture} fixes a nonempty $S$ and writes $s=\|S\|\le k^2/2$.
- reading of the symbol `d_S(u)`: $d_S(u)$ is the degree of $u$ in the simple graph with edge set $S$. In Lemma~\ref{lem:block-capture}: For each fixed nonempty support $S$ under consideration, $u\in V(S)$ is chosen with $d_S(u)\le 2\|S\|/\|V(S)\|$, so $1\le d_S(u)\le\sqrt{2\|S\|}\le k$. — The proof of Lemma~\ref{lem:block-capture} chooses a nonisolated vertex whose degree is at most the average degree and records the resulting bounds in \eqref{eq:support-degree}.

## Added conditions

None: no condition was added to the paper's own hypotheses.

## Conditions assumed

### Cited results

None: no result rests on a theorem imported from the literature.

### Deferred substrate gates

None: every substrate this run needed was built and proved.

## Unresolved / notes

- run-level `symbol a`: [note, V1.5] symbol table corrected: type "Context-dependent quantile level, real scalar, or real-valued coefficient function.", space "$(0,1)$ in the quantile definition; $\mathbb R$ in the scalar inequality; $\mathbb R^{\{0,1\}^{J\setminus\{i\}}}$ in tensorization.", def "In $p_a(\mathcal P)$, $a$ is the probability level with $0<a<1$; the local uses of $a$ in the product norm argument are specified separately." (The recorded quantile level is correct in the introduction but its type and domain do not cover the locally reused scalar and function in the low-degree proof. The figure's panel label (a) introduces no mathematical quantity.)
- run-level `symbol x`: [note, V1.5] symbol table corrected: space "$\{0,1\}^{E_n}$ in graph coordinate replacement; $\{0,1\}^{J}$ in the product Fourier basis; $\{0,1\}^{J\setminus\{i\}}$ as the argument of $\Delta_i g$; $\{0,1\}^{F}$ in $f_y(x)=f(x,y)$.", def "$x$ denotes a configuration on the indicated coordinate set; in a restriction, $f_y(x)=f(x,y)$ for $x\in\{0,1\}^{F}$." (The recorded entry confines $x$ to the full graph cube. The paper also uses it on a general finite product, on the coordinates remaining after a coordinate difference, and on the free coordinates of a restriction.)
- run-level `symbol b`: [note, V1.5] symbol table corrected: type "Context-dependent coordinate value, real scalar, or real-valued coefficient function.", space "$\{0,1\}$ in coordinate replacement; $\mathbb R$ in the scalar inequality; $\mathbb R^{\{0,1\}^{J\setminus\{i\}}}$ in tensorization.", def "In $x_{e\leftarrow b}$, $b\in\{0,1\}$ is the assigned coordinate value; the local uses of $b$ in the product norm argument are specified separately." (The recorded Boolean domain is correct for coordinate replacement but does not cover the real scalars and coefficient functions denoted by the locally reused letter in the low-degree proof. The figure's panel label (b) introduces no mathematical quantity.)
- run-level `symbol m`: [note, V1.5] symbol table corrected: type "influence comparison parameter or vertex-block size", def "$m$ is the real influence comparison parameter $m\ge2$ in the product estimate and the integer vertex-block size in the graph block arguments." (The entry covers only the real comparison parameter. The graph arguments also use an integer block size, subsequently fixed as a function of $n$.)
- run-level `symbol k`: [note, V1.5] symbol table corrected: def "$k>0$ is a real Fourier degree cutoff; degree conditions such as $\|S\|\le k$ are interpreted literally for integer degrees, with the sum empty when $k<1$." (The recorded formula is correct locally but incorrectly defines k globally: the restriction identity permits any positive real cutoff. Other uses choose the same formula with different local meanings of m, and the variance proof introduces that choice only in its large-n case.)
- run-level `symbol A`: [note, V1.5] symbol table corrected: type "Locally bound Fourier index or transformed real function", space "Locally $2^{J\setminus\{i\}}$, $2^F$, or $\mathbb R^{\{0,1\}^{J\setminus\{i\}}}$.", def "In the derivative coefficient identity, $A\subseteq J\setminus\{i\}$. In the tensorization argument, $A=T_\rho a$, using the operator on the other coordinates. In restriction coefficients, $A\subseteq F$." (The recorded entry covers only the derivative Fourier index. The paper also uses $A$ for the transformed function $T_\rho a$ and for a Fourier index on $F$. The apparent occurrence in the introduction is the ordinary word A, not a mathematical symbol.)
- run-level `symbol B`: [note, V1.5] symbol table corrected: type "locally defined auxiliary function or vertex block", space "$\mathbb R^{\{0,1\}^{J\setminus\{i\}}}$ or $\binom{[n]}m$, according to context", def "In the tensorization argument, $B=T_\rho b$, using the operator on the coordinates other than $i$; in the vertex-block arguments, $B$ is an $m$-element subset of $[n]$." (The recorded vertex-block type does not cover the earlier auxiliary function $B=T_\rho b$. These are separate local uses of the same notation, with no unresolved ambiguity.)
- run-level `symbol u`: [note, V1.5] symbol table corrected: type "local real function or graph vertex", space "$\mathbb R^{\{0,1\}^J}$ or $[n]$, according to context", def "In the projection argument, $u$ is a real function satisfying $u=P_{\le d}u$; in the graph arguments, $u$ denotes a vertex." (The recorded vertex-only entry misses the real function in the projection proof and conflates the chosen support vertex with the subsequent one-vertex event.)
- run-level `symbol v`: [note, V1.5] symbol table corrected: type "locally scoped real function or vertex count", space "$\mathbb R^{\{0,1\}^J}\cup\mathbb N$", def "$v$ denotes an arbitrary real function on $\{0,1\}^J$ in the projection estimate, and $v=\|V(S)\|$, where $V(S)$ is the set of nonisolated vertices of $S$, in the block-capture argument." (The recorded function type covers the projection argument but excludes the later integer vertex count. These are separate local uses of the same notation.)
- run-level `symbol s`: [note, V1.5] symbol table corrected: type "local scalar variable or support edge count", space "$(0,\infty)$", def "In the scalar monotonicity calculation, $s$ is the argument of $s\mapsto s\log(4/s)$ on $(0,1/2]$; in the support graph argument, $s=\|S\|$ for a nonempty edge set $S$." (The integer edge-count entry misses the earlier real scalar argument in the monotonicity calculation.)
- note on `symbol a`: symbol table corrected: type "Context-dependent quantile level, real scalar, or real-valued coefficient function.", space "$(0,1)$ in the quantile definition; $\mathbb R$ in the scalar inequality; $\mathbb R^{\{0,1\}^{J\setminus\{i\}}}$ in tensorization.", def "In $p_a(\mathcal P)$, $a$ is the probability level with $0<a<1$; the local uses of $a$ in the product norm argument are specified separately." (The recorded quantile level is correct in the introduction but its type and domain do not cover the locally reused scalar and function in the low-degree proof. The figure's panel label (a) introduces no mathematical quantity.)
- note on `symbol A`: symbol table corrected: type "Locally bound Fourier index or transformed real function", space "Locally $2^{J\setminus\{i\}}$, $2^F$, or $\mathbb R^{\{0,1\}^{J\setminus\{i\}}}$.", def "In the derivative coefficient identity, $A\subseteq J\setminus\{i\}$. In the tensorization argument, $A=T_\rho a$, using the operator on the other coordinates. In restriction coefficients, $A\subseteq F$." (The recorded entry covers only the derivative Fourier index. The paper also uses $A$ for the transformed function $T_\rho a$ and for a Fourier index on $F$. The apparent occurrence in the introduction is the ordinary word A, not a mathematical symbol.)
- note on `symbol b`: symbol table corrected: type "Context-dependent coordinate value, real scalar, or real-valued coefficient function.", space "$\{0,1\}$ in coordinate replacement; $\mathbb R$ in the scalar inequality; $\mathbb R^{\{0,1\}^{J\setminus\{i\}}}$ in tensorization.", def "In $x_{e\leftarrow b}$, $b\in\{0,1\}$ is the assigned coordinate value; the local uses of $b$ in the product norm argument are specified separately." (The recorded Boolean domain is correct for coordinate replacement but does not cover the real scalars and coefficient functions denoted by the locally reused letter in the low-degree proof. The figure's panel label (b) introduces no mathematical quantity.)
- note on `symbol B`: symbol table corrected: type "locally defined auxiliary function or vertex block", space "$\mathbb R^{\{0,1\}^{J\setminus\{i\}}}$ or $\binom{[n]}m$, according to context", def "In the tensorization argument, $B=T_\rho b$, using the operator on the coordinates other than $i$; in the vertex-block arguments, $B$ is an $m$-element subset of $[n]$." (The recorded vertex-block type does not cover the earlier auxiliary function $B=T_\rho b$. These are separate local uses of the same notation, with no unresolved ambiguity.)
- note on `symbol k`: symbol table corrected: def "$k>0$ is a real Fourier degree cutoff; degree conditions such as $\|S\|\le k$ are interpreted literally for integer degrees, with the sum empty when $k<1$." (The recorded formula is correct locally but incorrectly defines k globally: the restriction identity permits any positive real cutoff. Other uses choose the same formula with different local meanings of m, and the variance proof introduces that choice only in its large-n case.)
- note on `symbol m`: symbol table corrected: type "influence comparison parameter or vertex-block size", def "$m$ is the real influence comparison parameter $m\ge2$ in the product estimate and the integer vertex-block size in the graph block arguments." (The entry covers only the real comparison parameter. The graph arguments also use an integer block size, subsequently fixed as a function of $n$.)
- note on `symbol s`: symbol table corrected: type "local scalar variable or support edge count", space "$(0,\infty)$", def "In the scalar monotonicity calculation, $s$ is the argument of $s\mapsto s\log(4/s)$ on $(0,1/2]$; in the support graph argument, $s=\|S\|$ for a nonempty edge set $S$." (The integer edge-count entry misses the earlier real scalar argument in the monotonicity calculation.)
- note on `symbol u`: symbol table corrected: type "local real function or graph vertex", space "$\mathbb R^{\{0,1\}^J}$ or $[n]$, according to context", def "In the projection argument, $u$ is a real function satisfying $u=P_{\le d}u$; in the graph arguments, $u$ denotes a vertex." (The recorded vertex-only entry misses the real function in the projection proof and conflates the chosen support vertex with the subsequent one-vertex event.)
- note on `symbol v`: symbol table corrected: type "locally scoped real function or vertex count", space "$\mathbb R^{\{0,1\}^J}\cup\mathbb N$", def "$v$ denotes an arbitrary real function on $\{0,1\}^J$ in the projection estimate, and $v=\|V(S)\|$, where $V(S)$ is the set of nonisolated vertices of $S$, in the block-capture argument." (The recorded function type covers the projection argument but excludes the later integer vertex count. These are separate local uses of the same notation.)
- note on `symbol x`: symbol table corrected: space "$\{0,1\}^{E_n}$ in graph coordinate replacement; $\{0,1\}^{J}$ in the product Fourier basis; $\{0,1\}^{J\setminus\{i\}}$ as the argument of $\Delta_i g$; $\{0,1\}^{F}$ in $f_y(x)=f(x,y)$.", def "$x$ denotes a configuration on the indicated coordinate set; in a restriction, $f_y(x)=f(x,y)$ for $x\in\{0,1\}^{F}$." (The recorded entry confines $x$ to the full graph cube. The paper also uses it on a general finite product, on the coordinates remaining after a coordinate difference, and on the free coordinates of a restriction.)

### V1 lint warnings

- prop:block: prop:block references \ref{lem:low-degree} (lem:low-degree) but `depends_on` lacks ass:low-degree-m, ass:low-degree-small-influences, ass:low-degree-cutoff; V1.5 must confirm whether the paper assumes it or merely mentions it
- prop:block: prop:block references \ref{lem:restriction} (lem:restriction) but `depends_on` lacks ass:restriction-free-edges, ass:restriction-law, ass:restriction-cutoff, def:restriction-exterior, def:restricted-function; V1.5 must confirm whether the paper assumes it or merely mentions it
- thm:variance: thm:variance references \ref{lem:block-capture} (lem:block-capture) but `depends_on` lacks ass:block-capture-size; V1.5 must confirm whether the paper assumes it or merely mentions it
- thm:threshold: thm:threshold references \ref{thm:variance} (thm:variance) but `depends_on` lacks ass:variance-n, ass:variance-symmetry, ass:variance-bias; V1.5 must confirm whether the paper assumes it or merely mentions it

## Lean evidence

- build of the run barrel: **ok**
- source scan (sorry / admit / axiom): clean

| declaration | axioms |
| --- | --- |
| `Papers.OaiSharpThresholdMonotone.propertyQuantile_width_le` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiSharpThresholdMonotone.variance_le_log_sq_inv_mul_totalInfluence` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiSharpThresholdMonotone.sum_lowDegree_fourierCoeff_sq_le` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiSharpThresholdMonotone.restriction_mass_and_influence` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiSharpThresholdMonotone.block_average_lowDegree_mass_le` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiSharpThresholdMonotone.captured_lowDegree_mass_le` | clean — `propext`, `Classical.choice`, `Quot.sound` |

## Inputs

| artifact | status |
| --- | --- |
| `discovery/v1_scope.json` | present (6 environment(s)) |
| `discovery/v1_5_review.json` | present (verdict PASS) |
| `formalization/crosswalk_full.json` | present (177 object(s)) |
| `graph.json` | present (181 node(s)) |
| Lean evidence | collected (build ok, 0 scan issue(s), 177 declaration(s)) |

## Annotated paper

Annotated paper: `annotated/main.tex` (20 annotation(s), 0 unlocated; index `annotated/ANNOTATIONS.md`); PDF: `annotated/main.pdf`
