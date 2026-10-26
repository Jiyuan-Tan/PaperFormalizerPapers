# Correctness report — oai_uniform_influence_hypergraph

**Verdict: NO ERROR FOUND**

**Paper: MINOR ISSUES — no main result is shown false or weakened**

Minor:

- `p`: notation ambiguous; a reading was pinned
- `f`: notation ambiguous; a reading was pinned
- `x`: notation ambiguous; a reading was pinned
- `b`: notation ambiguous; a reading was pinned
- `J`: notation ambiguous; a reading was pinned
- `A`: notation ambiguous; a reading was pinned
- `S`: notation ambiguous; a reading was pinned
- `m`: notation ambiguous; a reading was pinned
- `k`: notation ambiguous; a reading was pinned
- `L`: notation ambiguous; a reading was pinned
- `a`: notation ambiguous; a reading was pinned
- `T`: notation ambiguous; a reading was pinned
- `f_y`: notation ambiguous; a reading was pinned
- `s`: notation ambiguous; a reading was pinned
- `u`: notation ambiguous; a reading was pinned
- `d_S(u)`: notation ambiguous; a reading was pinned
- `N_r`: notation ambiguous; a reading was pinned

5 result(s) of the paper were examined. None was found wrong as printed. In Lean: 5 proved, 0 taken from the literature as cited, 0 not certified, 0 not formalized.

## What was wrong and what was done

No error was found in the results examined.

## Clarifications (not errors)

Nothing in this section is an error of the paper. Each item is something the paper determines but does not say, made explicit so that the statements can be read, and formalized, in one way.

**Notation.**

- $p$: $p$ denotes the common Bernoulli bias, with $p\in[0,1]$. In Theorem~\ref{thm:main}, Lemma~\ref{lem:low}, Lemma~\ref{lem:block}: $0<p<1$. In Corollary~\ref{cor:threshold}: In $q(p)=\E_p f$ and the definition of $p_a$, $p$ ranges over $[0,1]$, including the endpoint product laws.
- $f$: $f:\{0,1\}^{E_{n,r}}\to\{0,1\}$ is invariant under every permutation of $[n]$. In Corollary~\ref{cor:threshold}: $f$ is increasing and nontrivial.
- $x$: $x$ denotes a configuration in $\{0,1\}^{J}$ for the coordinate set on which the function being evaluated is defined. In Theorem~\ref{thm:main}, Corollary~\ref{cor:threshold}: For evaluations of $f$, the coordinate set is $E_{n,r}$. In Lemma~\ref{lem:block}: The coordinate set is $E=E_{n,r}$ for $f$, and $F_B$ for the restricted function $f_y$.
- $b$: $b$ is locally bound, with its domain determined by the expression in which it occurs. In Theorem~\ref{thm:main}, Lemma~\ref{lem:block}, Corollary~\ref{cor:threshold}: In the coordinate replacement notation $x_{e\leftarrow b}$, $b\in\{0,1\}$ is the replacement value. In Lemma~\ref{lem:low}: In the one-coordinate norm calculation, $b\in\mathbb R$ is an arbitrary scalar. In the product induction, $g=a+b\chi_i$ uses a real-valued coefficient function $b$ on $\{0,1\}^{J\setminus\{i\}}$.
- $J$: $J$ denotes the finite coordinate set of the product space currently under consideration. In Theorem~\ref{thm:main}, Lemma~\ref{lem:block}: For the Fourier expansion of $f$, $J=E=E_{n,r}$; when the finite-coordinate estimate is applied to a restricted function $f_y$, its coordinate set is $J=F_B$.
- $A$: $A$ is a subset of the current coordinate set indexing a Fourier basis function or coefficient. In Lemma~\ref{lem:low}: In the difference identity $\widehat h(A\cup\{i\})=\sigma\widehat{\Delta_i h}(A)$, $A\subseteq J\setminus\{i\}$. In Lemma~\ref{lem:block}: In the expansion of $\widehat{f_y}(A)$, $A\subseteq F_B$.
- $S$: $S$ denotes a subset of the current coordinate set, used as a Fourier index or, for hypergraph coordinates, as an edge support. In Lemma~\ref{lem:low}: $S\subseteq J$, and the low-degree sum ranges over $1\le|S|\le k$. In Theorem~\ref{thm:main}, Lemma~\ref{lem:block}: $S\subseteq E_{n,r}$ indexes the Fourier expansion of $f$. In Lemma~\ref{lem:capture}: $S\subseteq E_{n,r}$ is a fixed support with $1\le|S|\le L$, considered before $B$ is sampled.
- $m$: $m$ is a fixed real parameter with $m\ge1$. In Lemma~\ref{lem:low}: $m\ge2$ is real and is the parameter in the individual-influence bound $I_i(h)\le I(h)/m$ and the cutoff $k=\sigma\log m/64$. In Lemma~\ref{lem:block}: $m$ is an integer with $r+1\le m\le n$, and $|B|=m$. In Lemma~\ref{lem:capture}: $m$ is an integer with $1\le m\le n$, and $|B|=m$. In Theorem~\ref{thm:main}: In the proof for $n\ge N_r$, $m=\lfloor\sqrt n\rfloor$ is the block size.
- $k$: $k$ is a real degree cutoff; comparisons of integer cardinalities with $k$ require no rounding. In Lemma~\ref{lem:low}: $k=\sigma\log m/64$ with real $m\ge2$; the low-degree sum is empty if $k<1$. The auxiliary projection inequalities are established for every real cutoff $k\ge0$. In Lemma~\ref{lem:block}: $k=\sigma\log m/64$ with integer $r+1\le m\le n$. In Lemma~\ref{lem:capture}: $k>0$ is arbitrary, and $L=(k/r)^{r/(r-1)}$. In Theorem~\ref{thm:main}: In the branch $n\ge N_r$, $m=\lfloor\sqrt n\rfloor$ and $k=\sigma\log m/64>0$.
- $L$: $L=(k/r)^\alpha$ is a positive real support-size cutoff. In Lemma~\ref{lem:capture}: $k>0$ is an arbitrary cutoff, so $L$ is not tied to $\sigma\log m/64$. In Theorem~\ref{thm:main}: In the branch $n\ge N_r$, $m=\lfloor\sqrt n\rfloor$, $k=\sigma\log m/64$, and hence $L=(\sigma\log m/(64r))^\alpha$.
- $a$: The letter $a$ is locally bound, with its domain and meaning determined by the calculation in which it occurs. In Corollary~\ref{cor:threshold}: $a\in(0,1)$ is the probability level indexing $p_a$. In Lemma~\ref{lem:low}: In the one-coordinate calculation, $a\in\mathbb R$ is a coefficient; in the product induction $g=a+b\chi_i$, it is a real-valued function on $\{0,1\}^{J\setminus\{i\}}$.
- $T$: On any current coordinate set $K\subseteq J$, $T$ denotes the linear operator on real-valued functions on $\{0,1\}^K$ determined by $T\chi_A=\rho^{|A|}\chi_A$ for every $A\subseteq K$, with the same $p$ and $\rho$.
- $f_y$: For each fixed $B$ and outside assignment $y$, $f_y$ is the restriction of $f$ to $\{0,1\}^{F_B}$; its Fourier coefficients and influences are computed on the free coordinates with bias $p$, and it is invariant under every permutation supported on $B$.
- $s$: $s=|S|$ is the number of edges in the support under consideration. In Lemma~\ref{lem:capture}: $1\le s\le L$.
- $u$: $u$ is a locally bound auxiliary object whose domain is specified in the argument using it. In Lemma~\ref{lem:low}: $u\in\operatorname{span}\{\chi_A:A\subseteq J,\ |A|\le k\}$ is a real-valued function; in the dual characterization of the projection norm, the supremum is over such functions with $\|u\|_2=1$. In Lemma~\ref{lem:capture}: $u\in V=\bigcup_{e\in S}e$ is a vertex chosen with $1\le d_S(u)\le k$; this choice depends only on $S$ and is made before $B$ is sampled.
- $d_S(u)$: $d_S(u)=|\{e\in S:u\in e\}|$ is the degree of the chosen vertex $u\in\bigcup_{e\in S}e$, with $1\le d_S(u)\le\min\{s,k\}$; the choice of $u$ depends only on $S$ and is made before $B$ is sampled.
- $N_r$: $N_r>r$ is a fixed integer depending only on $r$, chosen so that all four inequalities in \eqref{eq:large-n} hold for every $n\ge N_r$ with $m=\lfloor\sqrt n\rfloor$.

## What was proved in Lean, and what was not

A result is proved in Lean when a Lean declaration reviewed as stating it has a complete proof using no axiom beyond the standard ones. For a corrected result, the corrected statement is the one formalized.

| Result | Formal status | Lean declaration | Axioms |
| --- | --- | --- | --- |
| Theorem 1.1 | proved in Lean | `Papers.OaiUniformInfluenceHypergraph.variance_le_div_log_pow_mul_totalInfluence` (`TMain.lean:201`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 2.1 | proved in Lean | `Papers.OaiUniformInfluenceHypergraph.sum_lowDegree_fourierCoeff_sq_le` (`Helpers/LowDegree.lean:196`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 3.1 | proved in Lean | `Papers.OaiUniformInfluenceHypergraph.sum_blockProb_mul_fourierCoeff_sq_le` (`Helpers/Block.lean:164`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 3.2 | proved in Lean | `Papers.OaiUniformInfluenceHypergraph.blockProb_capture_ge` (`Helpers/Capture.lean:127`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Corollary 4.1 | proved in Lean | `Papers.OaiUniformInfluenceHypergraph.thresholdWidth_le` (`TCorThreshold.lean:18`) | the standard ones only (propext, Classical.choice, Quot.sound) |

The Lean development builds; it contains no `sorry`, `admit` or added axiom.

## The corrected paper

`bundle/corrected_paper/` holds the paper as it reads after the corrections, as plain source in the author's own class and layout, compiled to `bundle/corrected_paper/main.pdf` (9 pages). `bundle/MATCH.md` sets each result beside its Lean declaration; `bundle/lean/` holds the Lean code.

The mechanical checks leave nothing open.

# Technical appendix

The records behind the report above, by the run's own identifiers.

- paper: `main.tex` (source sha256 `2dd494bc1aea45b04ad243638464191504b0363d136bfdabc97a21cded1a6012`)
- stage completed: `5`
- results in scope: 5

| bucket | count |
| --- | --- |
| verified | 5 |
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
| source | `introduction.tex:24-32` (`theorem`, label `thm:main`) |
| statement | \label{thm:main} For every integer $r\ge3$ there is a finite constant $C_r$ such that, for every integer $n\ge r$, every $0<p<1$, and every hypergraph property $f:\{0,1\}^{E_{n,r}}\to\{0,1\}$, \begin{equation}\label{eq:main} \Var_p(f)\le \frac{C_r}{(\log n)^{r/(r-1)}}I_p(f). \end{equation} No monotonicity assumption is required. |
| appended hypothesis list | ass:main-r, ass:main-n, ass:main-p |
| Lean | `TMain.lean:201` — `Papers.OaiUniformInfluenceHypergraph.variance_le_div_log_pow_mul_totalInfluence` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 2. Low-degree mass `lem:low`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `fourier.tex:39-47` (`lemma`, label `lem:low`) |
| statement | \label{lem:low} Let $m\ge2$ be real and let $h:\{0,1\}^J\to\{0,1\}$ satisfy $I_i(h)\le I(h)/m$ for every $i\in J$. With $k=\sigma\log m/64$, one has \begin{equation}\label{eq:low} \sum_{1\le \|S\|\le k}\widehat h(S)^2\le m^{-1/4}I(h). \end{equation} The sum is empty when $k<1$. |
| appended hypothesis list | ass:low-m, ass:low-individual-influences |
| Lean | `Helpers/LowDegree.lean:196` — `Papers.OaiUniformInfluenceHypergraph.sum_lowDegree_fourierCoeff_sq_le` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 3. Averaged restriction estimate `lem:block`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `restriction.tex:18-26` (`lemma`, label `lem:block`) |
| statement | \label{lem:block} Let $r+1\le m\le n$ be integers and set $k=\sigma\log m/64$. For $B$ chosen uniformly among the $m$-subsets of $[n]$, \begin{equation}\label{eq:block} \sum_{S\subseteq E} \Pr_B(1\le\|S\cap F_B\|\le k)\widehat f(S)^2 \le m^{-1/4}\frac{rm}{n}I_p(f). \end{equation} |
| appended hypothesis list | ass:block-domain |
| Lean | `Helpers/Block.lean:164` — `Papers.OaiUniformInfluenceHypergraph.sum_blockProb_mul_fourierCoeff_sq_le` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 4. Capturing a support at one vertex `lem:capture`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `restriction.tex:72-86` (`lemma`, label `lem:capture`) |
| statement | \label{lem:capture} Let $n\ge r\ge3$ and $1\le m\le n$ be integers, let $k>0$, and put \[ \alpha=\frac r{r-1},\qquad L=(k/r)^\alpha. \] Suppose \begin{equation}\label{eq:capture-condition} rL\frac{m-1}{n-1}\le\frac12. \end{equation} For a uniform $m$-subset $B$ of $[n]$ and every $S\subseteq E_{n,r}$ with $1\le\|S\|\le L$, \begin{equation}\label{eq:capture} \Pr_B(1\le\|S\cap F_B\|\le k)\ge\frac{m}{2n}. \end{equation} |
| appended hypothesis list | ass:capture-integer-domain, ass:capture-k, ass:capture-condition, ass:capture-support |
| Lean | `Helpers/Capture.lean:127` — `Papers.OaiUniformInfluenceHypergraph.blockProb_capture_ge` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 5. cor:threshold `thm:cor-threshold`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `completion.tex:71-79` (`corollary`, label `cor:threshold`) |
| statement | \label{cor:threshold} For a nontrivial increasing property of $r$-uniform hypergraphs on $n\ge r$ vertices, where $r\ge3$, and every $0<\varepsilon<1/2$, \[ p_{1-\varepsilon}-p_\varepsilon \le\frac{2C_r}{(\log n)^{r/(r-1)}} \log\frac{1-\varepsilon}{\varepsilon}. \] |
| appended hypothesis list | ass:threshold-epsilon |
| Lean | `TCorThreshold.lean:18` — `Papers.OaiUniformInfluenceHypergraph.thresholdWidth_le` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

## Suggestions to the authors

Not errors: readings the paper determines but does not state, and side conditions the proofs use silently.

- reading of the symbol `p`: $p$ denotes the common Bernoulli bias, with $p\in[0,1]$. In Theorem~\ref{thm:main}, Lemma~\ref{lem:low}, Lemma~\ref{lem:block}: $0<p<1$. In Corollary~\ref{cor:threshold}: In $q(p)=\E_p f$ and the definition of $p_a$, $p$ ranges over $[0,1]$, including the endpoint product laws. — The product and Fourier setup fixes an interior bias, whereas the threshold-quantile definition explicitly uses $\inf\{p\in[0,1]:q(p)\ge a\}$.
- reading of the symbol `f`: $f:\{0,1\}^{E_{n,r}}\to\{0,1\}$ is invariant under every permutation of $[n]$. In Corollary~\ref{cor:threshold}: $f$ is increasing and nontrivial. — The introduction defines a hypergraph property by permutation invariance; the threshold-quantile paragraph and Corollary~\ref{cor:threshold} additionally require an increasing, nontrivial property.
- reading of the symbol `x`: $x$ denotes a configuration in $\{0,1\}^{J}$ for the coordinate set on which the function being evaluated is defined. In Theorem~\ref{thm:main}, Corollary~\ref{cor:threshold}: For evaluations of $f$, the coordinate set is $E_{n,r}$. In Lemma~\ref{lem:block}: The coordinate set is $E=E_{n,r}$ for $f$, and $F_B$ for the restricted function $f_y$. — The introduction uses hypergraph configurations on $E_{n,r}$. Section~\ref{sec:fourier} works on an arbitrary finite set $J$ and defines $\chi_i(x)=(x_i-p)/\sigma$ there; Section~\ref{sec:restriction} specializes the basis to $J=E$ and applies the finite-product estimate to functions on $F_B$.
- reading of the symbol `b`: $b$ is locally bound, with its domain determined by the expression in which it occurs. In Theorem~\ref{thm:main}, Lemma~\ref{lem:block}, Corollary~\ref{cor:threshold}: In the coordinate replacement notation $x_{e\leftarrow b}$, $b\in\{0,1\}$ is the replacement value. In Lemma~\ref{lem:low}: In the one-coordinate norm calculation, $b\in\mathbb R$ is an arbitrary scalar. In the product induction, $g=a+b\chi_i$ uses a real-valued coefficient function $b$ on $\{0,1\}^{J\setminus\{i\}}$. — Lines 47-48 define coordinate replacement; lines 221-222 specify real $a,b$; lines 235-237 specify that the coefficients in $g=a+b\chi_i$ depend on the remaining coordinates.
- reading of the symbol `J`: $J$ denotes the finite coordinate set of the product space currently under consideration. In Theorem~\ref{thm:main}, Lemma~\ref{lem:block}: For the Fourier expansion of $f$, $J=E=E_{n,r}$; when the finite-coordinate estimate is applied to a restricted function $f_y$, its coordinate set is $J=F_B$. — Section~\ref{sec:fourier} starts with arbitrary finite $J$. Section~\ref{sec:restriction} specifies $J=E$ for $f$, and the proof of Lemma~\ref{lem:block} applies the finite-coordinate estimate to $f_y$ on $F_B$.
- reading of the symbol `A`: $A$ is a subset of the current coordinate set indexing a Fourier basis function or coefficient. In Lemma~\ref{lem:low}: In the difference identity $\widehat h(A\cup\{i\})=\sigma\widehat{\Delta_i h}(A)$, $A\subseteq J\setminus\{i\}$. In Lemma~\ref{lem:block}: In the expansion of $\widehat{f_y}(A)$, $A\subseteq F_B$. — The basis definition specifies $A\subseteq J$. The difference identity specifies $A\subseteq J\setminus\{i\}$, and the restriction proof explicitly specifies $A\subseteq F_B$.
- reading of the symbol `S`: $S$ denotes a subset of the current coordinate set, used as a Fourier index or, for hypergraph coordinates, as an edge support. In Lemma~\ref{lem:low}: $S\subseteq J$, and the low-degree sum ranges over $1\le\|S\|\le k$. In Theorem~\ref{thm:main}, Lemma~\ref{lem:block}: $S\subseteq E_{n,r}$ indexes the Fourier expansion of $f$. In Lemma~\ref{lem:capture}: $S\subseteq E_{n,r}$ is a fixed support with $1\le\|S\|\le L$, considered before $B$ is sampled. — The Fourier identities sum over $S\subseteq J$; the restriction estimate sums over $S\subseteq E$; Lemma~\ref{lem:capture} specifies $S\subseteq E_{n,r}$ with $1\le\|S\|\le L$.
- reading of the symbol `m`: $m$ is a fixed real parameter with $m\ge1$. In Lemma~\ref{lem:low}: $m\ge2$ is real and is the parameter in the individual-influence bound $I_i(h)\le I(h)/m$ and the cutoff $k=\sigma\log m/64$. In Lemma~\ref{lem:block}: $m$ is an integer with $r+1\le m\le n$, and $\|B\|=m$. In Lemma~\ref{lem:capture}: $m$ is an integer with $1\le m\le n$, and $\|B\|=m$. In Theorem~\ref{thm:main}: In the proof for $n\ge N_r$, $m=\lfloor\sqrt n\rfloor$ is the block size. — Lemma~\ref{lem:low} allows real $m\ge2$; Lemmas~\ref{lem:block} and~\ref{lem:capture} specify integer block sizes with different ranges; the proof of Theorem~\ref{thm:main} chooses $m=\lfloor\sqrt n\rfloor$ when $n\ge N_r$.
- reading of the symbol `k`: $k$ is a real degree cutoff; comparisons of integer cardinalities with $k$ require no rounding. In Lemma~\ref{lem:low}: $k=\sigma\log m/64$ with real $m\ge2$; the low-degree sum is empty if $k<1$. The auxiliary projection inequalities are established for every real cutoff $k\ge0$. In Lemma~\ref{lem:block}: $k=\sigma\log m/64$ with integer $r+1\le m\le n$. In Lemma~\ref{lem:capture}: $k>0$ is arbitrary, and $L=(k/r)^{r/(r-1)}$. In Theorem~\ref{thm:main}: In the branch $n\ge N_r$, $m=\lfloor\sqrt n\rfloor$ and $k=\sigma\log m/64>0$. — Lemmas~\ref{lem:low} and~\ref{lem:block} set $k=\sigma\log m/64$. The projection argument permits any real $k\ge0$. Lemma~\ref{lem:capture} assumes only $k>0$, and the large-$n$ proof of Theorem~\ref{thm:main} sets $m=\lfloor\sqrt n\rfloor$ and $k=\sigma\log m/64$.
- reading of the symbol `L`: $L=(k/r)^\alpha$ is a positive real support-size cutoff. In Lemma~\ref{lem:capture}: $k>0$ is an arbitrary cutoff, so $L$ is not tied to $\sigma\log m/64$. In Theorem~\ref{thm:main}: In the branch $n\ge N_r$, $m=\lfloor\sqrt n\rfloor$, $k=\sigma\log m/64$, and hence $L=(\sigma\log m/(64r))^\alpha$. — The capture lemma allows arbitrary positive k; the main theorem's proof instead chooses k from the bias and block size before defining L.
- reading of the symbol `a`: The letter $a$ is locally bound, with its domain and meaning determined by the calculation in which it occurs. In Corollary~\ref{cor:threshold}: $a\in(0,1)$ is the probability level indexing $p_a$. In Lemma~\ref{lem:low}: In the one-coordinate calculation, $a\in\mathbb R$ is a coefficient; in the product induction $g=a+b\chi_i$, it is a real-valued function on $\{0,1\}^{J\setminus\{i\}}$. — The quantile definition specifies $0<a<1$; the one-coordinate calculation says "For real $a,b$"; the product induction writes $g=a+b\chi_i$ and specifies dependence on the remaining coordinates.
- reading of the symbol `T`: On any current coordinate set $K\subseteq J$, $T$ denotes the linear operator on real-valued functions on $\{0,1\}^K$ determined by $T\chi_A=\rho^{\|A\|}\chi_A$ for every $A\subseteq K$, with the same $p$ and $\rho$. — The proof first defines the spectral action on J, then explicitly uses T on the remaining coordinates in the induction.
- reading of the symbol `f_y`: For each fixed $B$ and outside assignment $y$, $f_y$ is the restriction of $f$ to $\{0,1\}^{F_B}$; its Fourier coefficients and influences are computed on the free coordinates with bias $p$, and it is invariant under every permutation supported on $B$. — The proof of Lemma~\ref{lem:block} fixes $B$ and $y$, establishes invariance under permutations supported on $B$, and applies Lemma~\ref{lem:low} using the free product measure before averaging over $y$.
- reading of the symbol `s`: $s=\|S\|$ is the number of edges in the support under consideration. In Lemma~\ref{lem:capture}: $1\le s\le L$. — The proof of Lemma~\ref{lem:capture} begins by fixing a support satisfying $1\le\|S\|\le L$ and writing $s=\|S\|$.
- reading of the symbol `u`: $u$ is a locally bound auxiliary object whose domain is specified in the argument using it. In Lemma~\ref{lem:low}: $u\in\operatorname{span}\{\chi_A:A\subseteq J,\ \|A\|\le k\}$ is a real-valued function; in the dual characterization of the projection norm, the supremum is over such functions with $\\|u\\|_2=1$. In Lemma~\ref{lem:capture}: $u\in V=\bigcup_{e\in S}e$ is a vertex chosen with $1\le d_S(u)\le k$; this choice depends only on $S$ and is made before $B$ is sampled. — The proof of Lemma~\ref{lem:low} quantifies over functions in the low-degree span. The proof of Lemma~\ref{lem:capture} explicitly chooses a vertex before sampling $B$.
- reading of the symbol `d_S(u)`: $d_S(u)=\|\{e\in S:u\in e\}\|$ is the degree of the chosen vertex $u\in\bigcup_{e\in S}e$, with $1\le d_S(u)\le\min\{s,k\}$; the choice of $u$ depends only on $S$ and is made before $B$ is sampled. — The proof of Lemma~\ref{lem:capture} chooses a vertex of degree between $1$ and $k$ and explicitly states that this choice depends only on $S$, before sampling $B$.
- reading of the symbol `N_r`: $N_r>r$ is a fixed integer depending only on $r$, chosen so that all four inequalities in \eqref{eq:large-n} hold for every $n\ge N_r$ with $m=\lfloor\sqrt n\rfloor$. — The proof of Theorem~\ref{thm:main} specifies this choice and explicitly states that it is independent of $p$ and $f$.

## Added conditions

None: no condition was added to the paper's own hypotheses.

## Conditions assumed

### Cited results

None: no result rests on a theorem imported from the literature.

### Deferred substrate gates

None: every substrate this run needed was built and proved.

## Unresolved / notes

- run-level `symbol p`: [note, V1.5] symbol table corrected: space "$[0,1]$" (The recorded open interval is correct for the analytic estimates but omits the endpoint biases explicitly included in the threshold-quantile definition. The role of p remains the same.)
- run-level `symbol x`: [note, V1.5] symbol table corrected: space "$\{0,1\}^{J}$ on the current coordinate set $J$.", def "$x$ is a configuration on the current coordinate set; for $J=E_{n,r}$ it represents a simple $r$-uniform hypergraph." (The recorded space covers only hypergraph configurations. The Fourier definitions also use $x$ on an arbitrary finite product, and their restriction applications use the free coordinate set.)
- run-level `symbol b`: [note, V1.5] symbol table corrected: type "locally bound coordinate value, real scalar, or real-valued coefficient function", space "$\{0,1\}$ in coordinate replacement; $\mathbb R$ in the one-coordinate calculation; $\mathbb R^{\{0,1\}^{J\setminus\{i\}}}$ in the product decomposition", def "In $x_{e\leftarrow b}$, $b$ is the value assigned to coordinate $e$. In the one-coordinate calculation, $a,b$ are real. In $g=a+b\chi_i$, $a,b$ depend on the remaining coordinates." (The recorded binary domain covers coordinate replacement but excludes the scalar and coefficient-function uses in the proof of Lemma~\ref{lem:low}. These are explicit local reuses of the letter, with no unresolved ambiguity.)
- run-level `symbol S`: [note, V1.5] symbol table corrected: type "coordinate subset", space "$2^J$ for the current coordinate set $J$", def "$S$ is a subset of the current coordinate set indexing a Fourier coefficient; in the hypergraph setting it is also regarded as a set of distinct $r$-edges." (The recorded domain restricts all uses to hypergraph coordinates and the expansion of $f$. The finite-coordinate estimate instead uses subsets of arbitrary $J$ indexing the expansion of $h$.)
- run-level `symbol m`: [note, V1.5] symbol table corrected: type "real parameter", space "$[1,\infty)$", def "$m$ is a real parameter whose domain and role are specified locally." (The recorded integer type and block-size definition exclude the real parameter used in Lemma~\ref{lem:low}. The block lemmas impose distinct integer ranges, and the main proof makes an exact choice rather than merely choosing about $\sqrt n$.)
- run-level `symbol k`: [note, V1.5] symbol table corrected: def "$k$ is a real degree cutoff specified locally." (The recorded formula is valid for the analytic and block estimates but is not the general definition: the capture lemma allows an arbitrary positive cutoff, and the auxiliary projection estimate allows any nonnegative real cutoff.)
- run-level `symbol a`: [note, V1.5] symbol table corrected: type "locally bound quantile level or coefficient", space "Context dependent: $(0,1)$, $\mathbb R$, or $\mathbb R^{\{0,1\}^{J\setminus\{i\}}}$.", def "The letter $a$ denotes the level in $p_a=\inf\{p\in[0,1]:q(p)\ge a\}$ for $0<a<1$, a real coefficient in the one-coordinate calculation, or the coefficient function in $g=a+b\chi_i$, where $a,b$ depend on the remaining coordinates." (The entry records only the quantile level. The proof also uses $a$ for an unrestricted real coefficient and then a coefficient function on the remaining coordinates; these are distinct local bindings.)
- run-level `symbol u`: [note, V1.5] symbol table corrected: type "real-valued function or vertex", space "$\mathbb R^{\{0,1\}^J}\cup[n]$", def "The symbol $u$ is locally bound, denoting a function in the low-degree projection argument or a vertex in the support-capture argument." (The entry records only the function meaning, but the capture proof uses the same letter for a support vertex. These are separate local bindings.)
- note on `symbol a`: symbol table corrected: type "locally bound quantile level or coefficient", space "Context dependent: $(0,1)$, $\mathbb R$, or $\mathbb R^{\{0,1\}^{J\setminus\{i\}}}$.", def "The letter $a$ denotes the level in $p_a=\inf\{p\in[0,1]:q(p)\ge a\}$ for $0<a<1$, a real coefficient in the one-coordinate calculation, or the coefficient function in $g=a+b\chi_i$, where $a,b$ depend on the remaining coordinates." (The entry records only the quantile level. The proof also uses $a$ for an unrestricted real coefficient and then a coefficient function on the remaining coordinates; these are distinct local bindings.)
- note on `symbol b`: symbol table corrected: type "locally bound coordinate value, real scalar, or real-valued coefficient function", space "$\{0,1\}$ in coordinate replacement; $\mathbb R$ in the one-coordinate calculation; $\mathbb R^{\{0,1\}^{J\setminus\{i\}}}$ in the product decomposition", def "In $x_{e\leftarrow b}$, $b$ is the value assigned to coordinate $e$. In the one-coordinate calculation, $a,b$ are real. In $g=a+b\chi_i$, $a,b$ depend on the remaining coordinates." (The recorded binary domain covers coordinate replacement but excludes the scalar and coefficient-function uses in the proof of Lemma~\ref{lem:low}. These are explicit local reuses of the letter, with no unresolved ambiguity.)
- note on `symbol k`: symbol table corrected: def "$k$ is a real degree cutoff specified locally." (The recorded formula is valid for the analytic and block estimates but is not the general definition: the capture lemma allows an arbitrary positive cutoff, and the auxiliary projection estimate allows any nonnegative real cutoff.)
- note on `symbol m`: symbol table corrected: type "real parameter", space "$[1,\infty)$", def "$m$ is a real parameter whose domain and role are specified locally." (The recorded integer type and block-size definition exclude the real parameter used in Lemma~\ref{lem:low}. The block lemmas impose distinct integer ranges, and the main proof makes an exact choice rather than merely choosing about $\sqrt n$.)
- note on `symbol p`: symbol table corrected: space "$[0,1]$" (The recorded open interval is correct for the analytic estimates but omits the endpoint biases explicitly included in the threshold-quantile definition. The role of p remains the same.)
- note on `symbol S`: symbol table corrected: type "coordinate subset", space "$2^J$ for the current coordinate set $J$", def "$S$ is a subset of the current coordinate set indexing a Fourier coefficient; in the hypergraph setting it is also regarded as a set of distinct $r$-edges." (The recorded domain restricts all uses to hypergraph coordinates and the expansion of $f$. The finite-coordinate estimate instead uses subsets of arbitrary $J$ indexing the expansion of $h$.)
- note on `symbol u`: symbol table corrected: type "real-valued function or vertex", space "$\mathbb R^{\{0,1\}^J}\cup[n]$", def "The symbol $u$ is locally bound, denoting a function in the low-degree projection argument or a vertex in the support-capture argument." (The entry records only the function meaning, but the capture proof uses the same letter for a support vertex. These are separate local bindings.)
- note on `symbol x`: symbol table corrected: space "$\{0,1\}^{J}$ on the current coordinate set $J$.", def "$x$ is a configuration on the current coordinate set; for $J=E_{n,r}$ it represents a simple $r$-uniform hypergraph." (The recorded space covers only hypergraph configurations. The Fourier definitions also use $x$ on an arbitrary finite product, and their restriction applications use the free coordinate set.)

### V1 lint warnings

- lem:block: lem:block references \ref{lem:low} (lem:low) but `depends_on` lacks ass:low-m, ass:low-individual-influences, def:low-cutoff; V1.5 must confirm whether the paper assumes it or merely mentions it
- thm:cor-threshold: cor:threshold references \ref{thm:main} (thm:main) but `depends_on` lacks ass:main-r, ass:main-n, ass:main-p; V1.5 must confirm whether the paper assumes it or merely mentions it
- thm:cor-threshold: the proof of cor:threshold cites [Russo81, Lemma 3] (cor:threshold/proof/1/1); the transcription reads the citation as a result this paper proves itself and made no cited node for it (The proof derives the Margulis--Russo identity directly by separate coordinate biases and monotonicity.). paper: "…derivative; see~\cite{Margulis74}, \cite[Lemma~3]{Russo81}, and \cite[Lemma~2.2]{FK96}. Here it…"
- thm:cor-threshold: the proof of cor:threshold cites [FK96, Lemma 2.2] (cor:threshold/proof/1/1); the transcription reads the citation as a result this paper proves itself and made no cited node for it (The proof derives the Margulis--Russo identity directly by separate coordinate biases and monotonicity.). paper: "…\cite[Lemma~3]{Russo81}, and \cite[Lemma~2.2]{FK96}. Here it follows directly by giving…"

## Lean evidence

- build of the run barrel: **ok**
- source scan (sorry / admit / axiom): clean

| declaration | axioms |
| --- | --- |
| `Papers.OaiUniformInfluenceHypergraph.variance_le_div_log_pow_mul_totalInfluence` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiUniformInfluenceHypergraph.sum_lowDegree_fourierCoeff_sq_le` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiUniformInfluenceHypergraph.sum_blockProb_mul_fourierCoeff_sq_le` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiUniformInfluenceHypergraph.blockProb_capture_ge` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiUniformInfluenceHypergraph.thresholdWidth_le` | clean — `propext`, `Classical.choice`, `Quot.sound` |

## Inputs

| artifact | status |
| --- | --- |
| `discovery/v1_scope.json` | present (5 environment(s)) |
| `discovery/v1_5_review.json` | present (verdict PASS) |
| `formalization/crosswalk_full.json` | present (160 object(s)) |
| `graph.json` | present (164 node(s)) |
| Lean evidence | collected (build ok, 0 scan issue(s), 160 declaration(s)) |

## Annotated paper

Annotated paper: `annotated/main.tex` (17 annotation(s), 0 unlocated; index `annotated/ANNOTATIONS.md`); PDF: `annotated/main.pdf`
