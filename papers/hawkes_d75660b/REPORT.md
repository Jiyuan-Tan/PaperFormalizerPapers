# Correctness report — hawkes_d75660b

**Verdict: NO ERROR FOUND**

**Paper: MINOR ISSUES — no main result is shown false or weakened**

Minor:

- Theorem 1: condition added (bookkeeping or a pinned reading)
- Corollary 1: condition added (bookkeeping or a pinned reading); ambiguous; a reading was pinned
- Lemma 1: condition added (bookkeeping or a pinned reading)
- Lemma 2: condition added (bookkeeping or a pinned reading)
- Corollary 2: condition added (bookkeeping or a pinned reading)
- `ass:prefs-total`: ambiguous; a reading was pinned
- `ass:meanrecursolve1-index`: ambiguous; a reading was pinned
- `def:intensitydefeq`: ambiguous; a reading was pinned
- `def:prefs`: ambiguous; a reading was pinned
- `def:combx-duration`: ambiguous; a reading was pinned
- `g`: notation ambiguous; a reading was pinned
- `\rho`: notation ambiguous; a reading was pinned
- `\tau_i`: notation ambiguous; a reading was pinned
- `\tau`: notation ambiguous; a reading was pinned
- `i`: notation ambiguous; a reading was pinned
- `n`: notation ambiguous; a reading was pinned
- `m`: notation ambiguous; a reading was pinned
- `\pi`: notation ambiguous; a reading was pinned
- `\kappa^+`: notation ambiguous; a reading was pinned
- `k_i`: notation ambiguous; a reading was pinned
- `k_i^+`: notation ambiguous; a reading was pinned
- `Z_i`: notation ambiguous; a reading was pinned
- `Y_m`: notation ambiguous; a reading was pinned
- `X_m`: notation ambiguous; a reading was pinned
- `k`: notation ambiguous; a reading was pinned
- `\ell`: notation ambiguous; a reading was pinned

5 result(s) of the paper were examined. None was found wrong as printed. In Lean: 5 proved, 0 taken from the literature as cited, 0 not certified, 0 not formalized.

## What was wrong and what was done

No error was found in the results examined.

## Clarifications (not errors)

Nothing in this section is an error of the paper. Each item is something the paper determines but does not say, made explicit so that the statements can be read, and formalized, in one way. None of them needs action.

**How a statement is read.**

- **Theorem 1.** $\mathbb{N}=\{0,1,2,\dots\}$ in the domain $\kappa\in\mathbb{N}^n$ of Definition~\ref{def:prefs}.
- **Theorem 1.** $n\in\mathbb{Z}_+$ and $m\in\{0,\dots,n-1\}$.
- **Theorem 1.** $N_t=\sum_{i=0}^{N-1}\mathbf{1}\{\tau_i\leq t\}$, and the integral in \eqref{intensityDefEq} is against the cluster point measure on $[0,t]$; for $g(t)=\rho e^{-t}$, the displayed $\lambda_t$ is the right-continuous post-jump version, whose predictable intensity is $\lambda_{t-}$ for $t>0$.
- **Theorem 1.** $\mathbb{N}=\{0,1,2,\dots\}$ in the definition of preference counts.
- **Theorem 1.** The $\tau$ constructed in Definition~\ref{def:combx-duration} has the same distribution as the cluster duration $\tau:=\tau_{N-1}$ defined from \eqref{intensityDefEq}.
- **Corollary 1.** The integrand $\frac{e^{-u}-e^{-\rho}}{\rho e^{-\rho}-u e^{-u}}$ is interpreted by its continuous extension at $u=\rho$, with value $1/(1-\rho)$.

**Notation.**

- $g$: The excitation kernel is a function $g:\mathbb{R}_+\to\mathbb{R}_+$. In Theorem~\ref{meanIdThm1}, Corollary~\ref{corIdThm1}: The kernel is $g(t)=\rho e^{-t}$ for $t\in\mathbb{R}_+$.
- $\rho$: The kernel parameter satisfies $\rho\in\mathbb{R}_+$ and $\rho<1$ throughout the analysis.
- $\tau_i$: The actual cluster points are indexed by $i\in\{0,\dots,N-1\}$, with $0=\tau_0<\cdots<\tau_{N-1}$; no further actual cluster points are required.
- $\tau$: The cluster duration is $\tau:=\tau_{N-1}$, with $\tau=0$ when $N=1$. In Theorem~\ref{meanIdThm1}, Corollary~\ref{corIdThm1}: For evaluating the duration law, $\tau$ also denotes the combinatorially constructed duration of Definition~\ref{def:combx-duration}: sample $N\sim\mathsf{Borel}(\rho)$; set $\tau=0$ if $N=1$; given $N=n+1$, sample the length-$n$ preference count $\kappa$ with the displayed law, then sample conditionally independent $Z_i\sim\mathrm{Exp}(\kappa_i^+-i+1)$ for $1\leq i\leq n$, and set $\tau=\sum_{i=1}^{N-1}Z_i$. This is a representation in distribution of the cluster duration.
- $i$: $i$ is a locally bound nonnegative-integer coordinate or summation index; preference-count coordinates have $1\leq i\leq n$, generalized parking-function order indices have $1\leq i\leq m$, and in $\mathsf{H}_j=\sum_{i=1}^j1/i$ it has $1\leq i\leq j$. In Lemma~\ref{kappaCPMF1}: In the prefix-count product $\prod_{i=1}^m {n-k_{i-1}^+\choose k_i}$, $i\in\{1,\dots,m\}$. In Corollary~\ref{meanRecurSolve1}: In the displayed finite correction sum, $i\in\{0,\dots,m\}$. In Theorem~\ref{meanIdThm1}: In the proof's triple sum, $0\leq i\leq m\leq n-1$; after summing over $m$, $0\leq i\leq n-1$; after exchanging the sums over $i$ and $n$, $i\geq0$ and $n\geq i+1$.
- $n$: $n\in\mathbb{Z}_+$ is the number of available preferences in a generalized parking function and the common length of a classic parking function and its preference-count vectors. In Lemma~\ref{kappaCPMF1}, Lemma~\ref{meanRecur1}, Corollary~\ref{meanRecurSolve1}: $n$ is a fixed positive integer specifying the length of the preference-count vector. In Theorem~\ref{meanIdThm1}: In the proof, $n$ is a dummy index for conditioning on $N=n+1$: the initial sum ranges over $n\geq0$, its $n=0$ term is dropped, and subsequent length-$n$ preference-count terms have $n\geq1$. After exchanging summations, the inner sum has $n\geq i+1$.
- $m$: $m$ is an integer parameter whose role and admissible range depend on whether it denotes a parking-function length or a preference-count index; as a parking-function length it satisfies $1\leq m\leq n$. In Lemma~\ref{kappaCPMF1}: $m$ indexes the observed prefix $(\kappa_1,\dots,\kappa_m)$ for $1\leq m<n$; the distribution of $\kappa_1$ is supplied separately. In Lemma~\ref{meanRecur1}, Corollary~\ref{meanRecurSolve1}: $m\in\{0,1,\dots,n-1\}$ is the preference-count index, including the initial index zero. In Theorem~\ref{meanIdThm1}: $m$ is a summation index ranging from $0$ to $n-1$ for each $n\geq1$.
- $\pi$: $\pi$ denotes a preference vector in $\mathbb{Z}_+^m$; it is a generalized parking function over $n$ preferences precisely when its sorted coordinates satisfy $\pi_{(i)}\leq n-m+i$ for $1\leq i\leq m$. In Lemma~\ref{kappaCPMF1}, Lemma~\ref{meanRecur1}: $\pi$ is a classic length-$n$ parking function, so its length is $n$ and its associated counts satisfy $\kappa_i(\pi)=|\{\ell:\pi_\ell=i\}|$.
- $\kappa^+$: $\kappa^+$ is the cumulative vector associated with $\kappa$, with $\kappa_i^+=\sum_{j=1}^i\kappa_j$ for $1\leq i\leq n$. In Lemma~\ref{meanRecur1}: The cumulative coordinates are extended to index zero by $\kappa_0^+=0$ almost surely.
- $k_i$: $k_i$, for $i\in\{1,\dots,n\}$, is a fixed nonnegative-integer value of $\kappa_i$; admissible full vectors satisfy $\sum_{i=1}^n k_i=n$ and $\sum_{j=1}^i k_j\geq i$ for every $1\leq i\leq n$. In Lemma~\ref{kappaCPMF1}: In the conditional PMF, $k_1,\dots,k_m$ specify the conditioning prefix on its positive-probability support, and $k_{m+1}$ is the candidate next count, with $0\leq k_{m+1}\leq n-k_m^+$ and $k_m^++k_{m+1}\geq m+1$.
- $k_i^+$: $k_i^+=\sum_{j=1}^i k_j$ is the fixed cumulative value associated with the realized preference counts, with $k_0^+=0$, $i\leq k_i^+\leq n$ for $1\leq i\leq n$, and $k_n^+=n$.
- $Z_i$: For $N=n+1\geq2$, the variables $(Z_i)_{i=1}^n$ are independent conditional on $\kappa$ and $N$, with conditional exponential rates $\kappa_i^+-i+1$; no $Z_i$ is required when $N=1$.
- $Y_m$: $Y_m$ has its stated Bernoulli law conditional on $\kappa_m^+$ and is the component on which the conditional binomial law of $X_m$ depends.
- $X_m$: $X_m$ is an auxiliary count whose binomial law is conditional on both $\kappa_m^+$ and $Y_m$, with support $\{0,\dots,n-\kappa_m^+-Y_m\}$.
- $k$: $k$ is the dummy integer summation index ranging over $\{0,\dots,n-\kappa_m^+\}$ when evaluating the conditional expectation given $\kappa_1,\dots,\kappa_m$.
- $\ell$: $\ell$ is a positive-integer dummy index, local to the preference-count map or summation in which it occurs. In Lemma~\ref{kappaCPMF1}, Lemma~\ref{meanRecur1}, Theorem~\ref{meanIdThm1}: In $\kappa_i(\pi)=|\{\ell:\pi_\ell=i\}|$, the index ranges over $\ell\in\{1,\dots,n\}$, the coordinates of $\pi$. In Theorem~\ref{meanIdThm1}: In the reindexed inner summation in the proof, $\ell=n-i$ ranges over $\{1,2,\dots\}$ because the preceding summation has $n\geq i+1$.

## What was proved in Lean, and what was not

A result is proved in Lean when a Lean declaration reviewed as stating it has a complete proof using no axiom beyond the standard ones. For a corrected result, the corrected statement is the one formalized.

| Result | Formal status | Lean declaration | Axioms |
| --- | --- | --- | --- |
| Theorem 1 | proved in Lean, under 5 condition(s) made explicit | `Papers.HawkesD75660b.meanDurationIdentity` (`T2.lean:27`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Corollary 1 | proved in Lean, under 6 condition(s) made explicit | `Papers.HawkesD75660b.meanDurationIntegral` (`T3.lean:28`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 1 | proved in Lean, under 2 condition(s) made explicit | `Papers.HawkesD75660b.conditionalPreferenceCountLaw` (`Helpers/ConditionalCounts.lean:32`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 2 | proved in Lean, under 2 condition(s) made explicit | `Papers.HawkesD75660b.meanRecurrence` (`Helpers/MeanRecurrence.lean:445`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Corollary 2 | proved in Lean, under 3 condition(s) made explicit | `Papers.HawkesD75660b.meanRecurrenceSolution` (`T1.lean:56`) | the standard ones only (propext, Classical.choice, Quot.sound) |

The Lean development builds; it contains no `sorry`, `admit` or added axiom.

## The corrected paper

`bundle/corrected_paper/` holds the paper as it reads after the corrections, as plain source in the author's own class and layout, compiled to `bundle/corrected_paper/main.pdf` (13 pages). `bundle/MATCH.md` sets each result beside its Lean declaration; `bundle/lean/` holds the Lean code.

The mechanical checks leave nothing open.

# Technical appendix

The records behind the report above, by the run's own identifiers.

- paper: `main.tex` (source sha256 `d79ad65830357663245beb36a5fb54316a8d83ea04ec78d7b389faf9d7595f70`)
- stage completed: `V6`
- results in scope: 5

| bucket | count |
| --- | --- |
| verified | 0 |
| verified_with_bookkeeping | 5 |
| conditional | 0 |
| repaired | 0 |
| unresolved | 0 |
| not_checked | 0 |
| not_determined | 0 |
| refuted | 0 |

> This is a conditional report. A `verified` result is verified only up to the cited results it assumes, the substrate gates left assumed, and the conditions added during formalization — all listed in full below. `unresolved` means the formalization did not close; it is NOT a claim that the result is wrong. A `refuted` row is a result shown false by a positive witness with no confirmed repair; a `repaired` row was false as printed, and an independent referee confirmed its minimal repair. A `not_determined` row could not be checked as printed: the paper does not say enough to determine the claim, and no reading or repair was adopted; it is NOT a claim that the result is wrong.

## Results

### 1. meanIdThm1 `thm:meanidthm1`

| field | value |
| --- | --- |
| bucket | `verified_with_bookkeeping` |
| source | `main.tex:243-255` (`theorem`, label `meanIdThm1`) |
| statement | \label{meanIdThm1} Let $B \sim \mathsf{Borel}(\rho)$. Then, the mean duration of the Markovian Hawkes cluster is such that \begin{align} \E{\tau} &= \left(1-\rho\right) \E{B \cdot \mathsf{H}_B} - 1 , \end{align} where $\mathsf{H}_j = \sum_{i=1}^j 1/i$ is the $j$th Harmonic number for each $j \in \mathbb{Z}_+$. |
| appended hypothesis list | ass:subcritical, ass:meanidthm1-borel |
| Lean | `T2.lean:27` — `Papers.HawkesD75660b.meanDurationIdentity` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | `ass:pin-2`, `ass:pin-3`, `ass:pin-4`, `ass:pin-5`, `ass:pin-6` |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 2. corIdThm1 `thm:coridthm1`

| field | value |
| --- | --- |
| bucket | `verified_with_bookkeeping` |
| source | `main.tex:257-266` (`corollary`, label `corIdThm1`) |
| statement | \label{corIdThm1} The mean duration of the Markovian Hawkes cluster is given by \begin{align} \E{\tau} &= \int_0^\rho \frac{e^{-u} - e^{-\rho}}{\rho e^{-\rho} - u e^{-u}}\mathrm{d}u . \end{align} |
| appended hypothesis list | ass:subcritical |
| Lean | `T3.lean:28` — `Papers.HawkesD75660b.meanDurationIntegral` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity pinned · correctness ok |
| added conditions | `ass:pin-1`, `ass:pin-2`, `ass:pin-3`, `ass:pin-4`, `ass:pin-5`, `ass:pin-6` |
| cited results | — |
| assumed substrate gates | — |
| findings | [note, V1.5] pinned reading: The integrand $\frac{e^{-u}-e^{-\rho}}{\rho e^{-\rho}-u e^{-u}}$ is interpreted by its continuous extension at $u=\rho$, with value $1/(1-\rho)$. (The change of variables in the proof of Corollary~\ref{corIdThm1} preserves the integral through a removable endpoint singularity; the displayed quotient has precisely this limit.) |

### 3. kappaCPMF1 `lem:kappacpmf1`

| field | value |
| --- | --- |
| bucket | `verified_with_bookkeeping` |
| source | `main.tex:383-410` (`lemma`, label `kappaCPMF1`) |
| statement | \label{kappaCPMF1} For $n \in \mathbb{Z}_+$, let $\kappa$ be a length-$n$ preference count with distribution given by~\eqref{kappaDist}. Then, the conditional distribution of $\kappa_{m+1}$ given $\kappa_1$ through $\kappa_m$ has probability mass function (PMF) given by \begin{align} \PP{\kappa_{m+1} = k_{m+1} \mid \kappa_1 = k_1, \dots, \kappa_m = k_m} &= \frac{k_{m+1}^+ - m}{k_m^+ - m + 1} {n - k_m^+ \choose k_{m+1}} \frac{\left(n-m\right)^{n-k_{m+1}^+-1}}{(n-m+1)^{n-k_m^+-1}} , \end{align} for each $m < n$, meaning that $\kappa_{m+1} \| (\kappa_1, \dots, \kappa_m) \stackrel{\mathsf{D}}{=} X_m + Y_m$, where, given $\kappa_m^+$, \begin{align} X_m \| Y_m \sim \mathsf{Bin}\left( n - \kappa_m^+ - Y_m , \frac{1}{n-m+1} \right) \qquad \text{ and } \qquad Y_m \sim \mathsf{Bern}\left(\frac{n-\kappa_m^+}{(n-m)(\kappa_m^+ - m + 1)} \right) , \end{align} with $(\kappa_1 - 1) \sim \mathsf{Bin}\left(n-1, 1/(n+1)\right)$. |
| appended hypothesis list | ass:kappacpmf1-index, ass:kappacpmf1-law |
| Lean | `Helpers/ConditionalCounts.lean:32` — `Papers.HawkesD75660b.conditionalPreferenceCountLaw` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | `ass:pin-2`, `ass:pin-5` |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 4. meanRecur1 `lem:meanrecur1`

| field | value |
| --- | --- |
| bucket | `verified_with_bookkeeping` |
| source | `main.tex:496-507` (`lemma`, label `meanRecur1`) |
| statement | \label{meanRecur1} For $n \in \mathbb{Z}_+$, let $\kappa$ be a length-$n$ preference count with distribution given by~\eqref{kappaDist}. Then, for each $m \in \{0, 1, \dots, n - 1\}$, \begin{align} \E{\frac{1}{\kappa_{m+1}^+ - m} } &= \left(1 + \frac{1}{n-m}\right)\E{\frac{1}{\kappa_m^+ - m + 1}} - {n \choose m}\frac{(m+1)^{m-1}}{(n+1)^{n-1}}(n-m)^{n-m-1} , \end{align} where $\PP{\kappa_0^+ = 0} = 1$. |
| appended hypothesis list | ass:meanrecur1-index, ass:meanrecur1-law |
| Lean | `Helpers/MeanRecurrence.lean:445` — `Papers.HawkesD75660b.meanRecurrence` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | `ass:pin-2`, `ass:pin-5` |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 5. meanRecurSolve1 `thm:meanrecursolve1`

| field | value |
| --- | --- |
| bucket | `verified_with_bookkeeping` |
| source | `main.tex:572-586` (`corollary`, label `meanRecurSolve1`) |
| statement | \label{meanRecurSolve1} For $m < n$, let $\kappa$ be a length-$n$ preference count with distribution given by~\eqref{kappaDist}. Then, \begin{align} \E{\frac{1}{\kappa_{m+1}^+ - m} } &= \frac{n+1}{n-m} - \frac{1}{n-m} \sum_{i=0}^m {n \choose i} \left(\frac{i+1}{n+1}\right)^{i-1} \left(\frac{n-i}{n+1}\right)^{n-i} . \end{align} |
| appended hypothesis list | ass:meanrecursolve1-index, ass:meanrecursolve1-law |
| Lean | `T1.lean:56` — `Papers.HawkesD75660b.meanRecurrenceSolution` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | `ass:pin-2`, `ass:pin-3`, `ass:pin-5` |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

## Corrected version

5 of 5 result(s) differ from the version you provided — 0 repaired, 0 with the proof completed (no error), 5 only with a side condition or reading made explicit; the others are as printed. The Lean formalization is of the corrected version.

### `thm:meanidthm1` (`main.tex:243-255`)

- as printed: \label{meanIdThm1} Let $B \sim \mathsf{Borel}(\rho)$. Then, the mean duration of the Markovian Hawkes cluster is such that \begin{align} \E{\tau} &= \left(1-\rho\right) \E{B \cdot \mathsf{H}_B} - 1 , \end{align} where $\mathsf{H}_j = \sum_{i=1}^j 1/i$ is the $j$th Harmonic number for each $j \in \mathbb{Z}_+$.
- corrected: statement unchanged
- no error: only a side condition or reading the referee made explicit (see below)
- side condition added by the confirming referee `ass:pin-2`: $\mathbb{N}=\{0,1,2,\dots\}$ in the domain $\kappa\in\mathbb{N}^n$ of Definition~\ref{def:prefs}. — pins reading of def:prefs: Definition~\ref{def:prefs} asserts a bijection with cumulative preference counts, and the following paragraph identifies counts with numbers of drivers choosing each preference. The classic parking function $\pi=(1,1)$ gives $\kappa=(2,0)$ and cumulative vector $(2,2)$, requiring zero to be allowed.
- side condition added by the confirming referee `ass:pin-3`: $n\in\mathbb{Z}_+$ and $m\in\{0,\dots,n-1\}$. — pins reading of ass:meanrecursolve1-index: Corollary~\ref{meanRecurSolve1} uses the coordinate $\kappa_{m+1}^+$ and a sum beginning at zero; the proof of Theorem~\ref{meanIdThm1} applies it for exactly $0\leq m\leq n-1$.
- side condition added by the confirming referee `ass:pin-4`: $N_t=\sum_{i=0}^{N-1}\mathbf{1}\{\tau_i\leq t\}$, and the integral in \eqref{intensityDefEq} is against the cluster point measure on $[0,t]$; for $g(t)=\rho e^{-t}$, the displayed $\lambda_t$ is the right-continuous post-jump version, whose predictable intensity is $\lambda_{t-}$ for $t>0$. — pins reading of def:intensitydefeq: Equation~\eqref{intensityDefEq} includes all points counted by $N_t$, starting at $\tau_0=0$. The stated exponential kernel then fixes the corresponding right-continuous path version.
- side condition added by the confirming referee `ass:pin-5`: $\mathbb{N}=\{0,1,2,\dots\}$ in the definition of preference counts. — pins reading of def:prefs: The preference-count map immediately following Definition~\ref{def:prefs} sends the classic parking function $\pi=(1,1)$ to $\kappa=(2,0)$. The claimed bijection with weakly increasing cumulative counts likewise permits zero increments.
- side condition added by the confirming referee `ass:pin-6`: The $\tau$ constructed in Definition~\ref{def:combx-duration} has the same distribution as the cluster duration $\tau:=\tau_{N-1}$ defined from \eqref{intensityDefEq}. — pins reading of def:combx-duration: The paragraph immediately following Definition~\ref{def:combx-duration} identifies the two constructions as equivalent and uses the combinatorial construction for the main proofs; the introduction explicitly describes the conditional representation as equivalence in distribution.

### `thm:coridthm1` (`main.tex:257-266`)

- as printed: \label{corIdThm1} The mean duration of the Markovian Hawkes cluster is given by \begin{align} \E{\tau} &= \int_0^\rho \frac{e^{-u} - e^{-\rho}}{\rho e^{-\rho} - u e^{-u}}\mathrm{d}u . \end{align}
- corrected: statement unchanged
- no error: only a side condition or reading the referee made explicit (see below)
- side condition added by the confirming referee `ass:pin-1`: The integrand $\frac{e^{-u}-e^{-\rho}}{\rho e^{-\rho}-u e^{-u}}$ is interpreted by its continuous extension at $u=\rho$, with value $1/(1-\rho)$. — pins reading of thm:coridthm1: The change of variables in the proof of Corollary~\ref{corIdThm1} preserves the integral through a removable endpoint singularity; the displayed quotient has precisely this limit.
- side condition added by the confirming referee `ass:pin-2`: $\mathbb{N}=\{0,1,2,\dots\}$ in the domain $\kappa\in\mathbb{N}^n$ of Definition~\ref{def:prefs}. — pins reading of def:prefs: Definition~\ref{def:prefs} asserts a bijection with cumulative preference counts, and the following paragraph identifies counts with numbers of drivers choosing each preference. The classic parking function $\pi=(1,1)$ gives $\kappa=(2,0)$ and cumulative vector $(2,2)$, requiring zero to be allowed.
- side condition added by the confirming referee `ass:pin-3`: $n\in\mathbb{Z}_+$ and $m\in\{0,\dots,n-1\}$. — pins reading of ass:meanrecursolve1-index: Corollary~\ref{meanRecurSolve1} uses the coordinate $\kappa_{m+1}^+$ and a sum beginning at zero; the proof of Theorem~\ref{meanIdThm1} applies it for exactly $0\leq m\leq n-1$.
- side condition added by the confirming referee `ass:pin-4`: $N_t=\sum_{i=0}^{N-1}\mathbf{1}\{\tau_i\leq t\}$, and the integral in \eqref{intensityDefEq} is against the cluster point measure on $[0,t]$; for $g(t)=\rho e^{-t}$, the displayed $\lambda_t$ is the right-continuous post-jump version, whose predictable intensity is $\lambda_{t-}$ for $t>0$. — pins reading of def:intensitydefeq: Equation~\eqref{intensityDefEq} includes all points counted by $N_t$, starting at $\tau_0=0$. The stated exponential kernel then fixes the corresponding right-continuous path version.
- side condition added by the confirming referee `ass:pin-5`: $\mathbb{N}=\{0,1,2,\dots\}$ in the definition of preference counts. — pins reading of def:prefs: The preference-count map immediately following Definition~\ref{def:prefs} sends the classic parking function $\pi=(1,1)$ to $\kappa=(2,0)$. The claimed bijection with weakly increasing cumulative counts likewise permits zero increments.
- side condition added by the confirming referee `ass:pin-6`: The $\tau$ constructed in Definition~\ref{def:combx-duration} has the same distribution as the cluster duration $\tau:=\tau_{N-1}$ defined from \eqref{intensityDefEq}. — pins reading of def:combx-duration: The paragraph immediately following Definition~\ref{def:combx-duration} identifies the two constructions as equivalent and uses the combinatorial construction for the main proofs; the introduction explicitly describes the conditional representation as equivalence in distribution.

### `lem:kappacpmf1` (`main.tex:383-410`)

- as printed: \label{kappaCPMF1} For $n \in \mathbb{Z}_+$, let $\kappa$ be a length-$n$ preference count with distribution given by~\eqref{kappaDist}. Then, the conditional distribution of $\kappa_{m+1}$ given $\kappa_1$ through $\kappa_m$ has probability mass function (PMF) given by \begin{align} \PP{\kappa_{m+1} = k_{m+1} \mid \kappa_1 = k_1, \dots, \kappa_m = k_m} &= \frac{k_{m+1}^+ - m}{k_m^+ - m + 1} {n - k_m^+ \choose k_{m+1}} \frac{\left(n-m\right)^{n-k_{m+1}^+-1}}{(n-m+1)^{n-k_m^+-1}} , \end{align} for each $m < n$, meaning that $\kappa_{m+1} | (\kappa_1, \dots, \kappa_m) \stackrel{\mathsf{D}}{=} X_m + Y_m$, where, given $\kappa_m^+$, \begin{align} X_m | Y_m \sim \mathsf{Bin}\left( n - \kappa_m^+ - Y_m , \frac{1}{n-m+1} \right) \qquad \text{ and } \qquad Y_m \sim \mathsf{Bern}\left(\frac{n-\kappa_m^+}{(n-m)(\kappa_m^+ - m + 1)} \right) , \end{align} with $(\kappa_1 - 1) \sim \mathsf{Bin}\left(n-1, 1/(n+1)\right)$.
- corrected: statement unchanged
- no error: only a side condition or reading the referee made explicit (see below)
- side condition added by the confirming referee `ass:pin-2`: $\mathbb{N}=\{0,1,2,\dots\}$ in the domain $\kappa\in\mathbb{N}^n$ of Definition~\ref{def:prefs}. — pins reading of def:prefs: Definition~\ref{def:prefs} asserts a bijection with cumulative preference counts, and the following paragraph identifies counts with numbers of drivers choosing each preference. The classic parking function $\pi=(1,1)$ gives $\kappa=(2,0)$ and cumulative vector $(2,2)$, requiring zero to be allowed.
- side condition added by the confirming referee `ass:pin-5`: $\mathbb{N}=\{0,1,2,\dots\}$ in the definition of preference counts. — pins reading of def:prefs: The preference-count map immediately following Definition~\ref{def:prefs} sends the classic parking function $\pi=(1,1)$ to $\kappa=(2,0)$. The claimed bijection with weakly increasing cumulative counts likewise permits zero increments.

### `lem:meanrecur1` (`main.tex:496-507`)

- as printed: \label{meanRecur1} For $n \in \mathbb{Z}_+$, let $\kappa$ be a length-$n$ preference count with distribution given by~\eqref{kappaDist}. Then, for each $m \in \{0, 1, \dots, n - 1\}$, \begin{align} \E{\frac{1}{\kappa_{m+1}^+ - m} } &= \left(1 + \frac{1}{n-m}\right)\E{\frac{1}{\kappa_m^+ - m + 1}} - {n \choose m}\frac{(m+1)^{m-1}}{(n+1)^{n-1}}(n-m)^{n-m-1} , \end{align} where $\PP{\kappa_0^+ = 0} = 1$.
- corrected: statement unchanged
- no error: only a side condition or reading the referee made explicit (see below)
- side condition added by the confirming referee `ass:pin-2`: $\mathbb{N}=\{0,1,2,\dots\}$ in the domain $\kappa\in\mathbb{N}^n$ of Definition~\ref{def:prefs}. — pins reading of def:prefs: Definition~\ref{def:prefs} asserts a bijection with cumulative preference counts, and the following paragraph identifies counts with numbers of drivers choosing each preference. The classic parking function $\pi=(1,1)$ gives $\kappa=(2,0)$ and cumulative vector $(2,2)$, requiring zero to be allowed.
- side condition added by the confirming referee `ass:pin-5`: $\mathbb{N}=\{0,1,2,\dots\}$ in the definition of preference counts. — pins reading of def:prefs: The preference-count map immediately following Definition~\ref{def:prefs} sends the classic parking function $\pi=(1,1)$ to $\kappa=(2,0)$. The claimed bijection with weakly increasing cumulative counts likewise permits zero increments.

### `thm:meanrecursolve1` (`main.tex:572-586`)

- as printed: \label{meanRecurSolve1} For $m < n$, let $\kappa$ be a length-$n$ preference count with distribution given by~\eqref{kappaDist}. Then, \begin{align} \E{\frac{1}{\kappa_{m+1}^+ - m} } &= \frac{n+1}{n-m} - \frac{1}{n-m} \sum_{i=0}^m {n \choose i} \left(\frac{i+1}{n+1}\right)^{i-1} \left(\frac{n-i}{n+1}\right)^{n-i} . \end{align}
- corrected: statement unchanged
- no error: only a side condition or reading the referee made explicit (see below)
- side condition added by the confirming referee `ass:pin-2`: $\mathbb{N}=\{0,1,2,\dots\}$ in the domain $\kappa\in\mathbb{N}^n$ of Definition~\ref{def:prefs}. — pins reading of def:prefs: Definition~\ref{def:prefs} asserts a bijection with cumulative preference counts, and the following paragraph identifies counts with numbers of drivers choosing each preference. The classic parking function $\pi=(1,1)$ gives $\kappa=(2,0)$ and cumulative vector $(2,2)$, requiring zero to be allowed.
- side condition added by the confirming referee `ass:pin-3`: $n\in\mathbb{Z}_+$ and $m\in\{0,\dots,n-1\}$. — pins reading of ass:meanrecursolve1-index: Corollary~\ref{meanRecurSolve1} uses the coordinate $\kappa_{m+1}^+$ and a sum beginning at zero; the proof of Theorem~\ref{meanIdThm1} applies it for exactly $0\leq m\leq n-1$.
- side condition added by the confirming referee `ass:pin-5`: $\mathbb{N}=\{0,1,2,\dots\}$ in the definition of preference counts. — pins reading of def:prefs: The preference-count map immediately following Definition~\ref{def:prefs} sends the classic parking function $\pi=(1,1)$ to $\kappa=(2,0)$. The claimed bijection with weakly increasing cumulative counts likewise permits zero increments.

## Suggestions to the authors

Not errors: readings the paper determines but does not state, and side conditions the proofs use silently.

- clarification (`ass:pin-2`, used by `thm:meanidthm1`): $\mathbb{N}=\{0,1,2,\dots\}$ in the domain $\kappa\in\mathbb{N}^n$ of Definition~\ref{def:prefs}. — pins reading of def:prefs: Definition~\ref{def:prefs} asserts a bijection with cumulative preference counts, and the following paragraph identifies counts with numbers of drivers choosing each preference. The classic parking function $\pi=(1,1)$ gives $\kappa=(2,0)$ and cumulative vector $(2,2)$, requiring zero to be allowed.
- clarification (`ass:pin-3`, used by `thm:meanidthm1`): $n\in\mathbb{Z}_+$ and $m\in\{0,\dots,n-1\}$. — pins reading of ass:meanrecursolve1-index: Corollary~\ref{meanRecurSolve1} uses the coordinate $\kappa_{m+1}^+$ and a sum beginning at zero; the proof of Theorem~\ref{meanIdThm1} applies it for exactly $0\leq m\leq n-1$.
- clarification (`ass:pin-4`, used by `thm:meanidthm1`): $N_t=\sum_{i=0}^{N-1}\mathbf{1}\{\tau_i\leq t\}$, and the integral in \eqref{intensityDefEq} is against the cluster point measure on $[0,t]$; for $g(t)=\rho e^{-t}$, the displayed $\lambda_t$ is the right-continuous post-jump version, whose predictable intensity is $\lambda_{t-}$ for $t>0$. — pins reading of def:intensitydefeq: Equation~\eqref{intensityDefEq} includes all points counted by $N_t$, starting at $\tau_0=0$. The stated exponential kernel then fixes the corresponding right-continuous path version.
- clarification (`ass:pin-5`, used by `thm:meanidthm1`): $\mathbb{N}=\{0,1,2,\dots\}$ in the definition of preference counts. — pins reading of def:prefs: The preference-count map immediately following Definition~\ref{def:prefs} sends the classic parking function $\pi=(1,1)$ to $\kappa=(2,0)$. The claimed bijection with weakly increasing cumulative counts likewise permits zero increments.
- clarification (`ass:pin-6`, used by `thm:meanidthm1`): The $\tau$ constructed in Definition~\ref{def:combx-duration} has the same distribution as the cluster duration $\tau:=\tau_{N-1}$ defined from \eqref{intensityDefEq}. — pins reading of def:combx-duration: The paragraph immediately following Definition~\ref{def:combx-duration} identifies the two constructions as equivalent and uses the combinatorial construction for the main proofs; the introduction explicitly describes the conditional representation as equivalence in distribution.
- clarification (`ass:pin-1`, used by `thm:coridthm1`): The integrand $\frac{e^{-u}-e^{-\rho}}{\rho e^{-\rho}-u e^{-u}}$ is interpreted by its continuous extension at $u=\rho$, with value $1/(1-\rho)$. — pins reading of thm:coridthm1: The change of variables in the proof of Corollary~\ref{corIdThm1} preserves the integral through a removable endpoint singularity; the displayed quotient has precisely this limit.
- `ass:meanrecursolve1-index`: pinned reading: $n\in\mathbb{Z}_+$ and $m\in\{0,\dots,n-1\}$. (Corollary~\ref{meanRecurSolve1} uses the coordinate $\kappa_{m+1}^+$ and a sum beginning at zero; the proof of Theorem~\ref{meanIdThm1} applies it for exactly $0\leq m\leq n-1$.)
- `ass:prefs-total`: pinned reading: $\mathbb{N}=\{0,1,2,\dots\}$ in the domain $\kappa\in\mathbb{N}^n$ of Definition~\ref{def:prefs}. (Definition~\ref{def:prefs} asserts a bijection with cumulative preference counts, and the following paragraph identifies counts with numbers of drivers choosing each preference. The classic parking function $\pi=(1,1)$ gives $\kappa=(2,0)$ and cumulative vector $(2,2)$, requiring zero to be allowed.)
- `def:combx-duration`: pinned reading: The $\tau$ constructed in Definition~\ref{def:combx-duration} has the same distribution as the cluster duration $\tau:=\tau_{N-1}$ defined from \eqref{intensityDefEq}. (The paragraph immediately following Definition~\ref{def:combx-duration} identifies the two constructions as equivalent and uses the combinatorial construction for the main proofs; the introduction explicitly describes the conditional representation as equivalence in distribution.)
- `def:intensitydefeq`: pinned reading: $N_t=\sum_{i=0}^{N-1}\mathbf{1}\{\tau_i\leq t\}$, and the integral in \eqref{intensityDefEq} is against the cluster point measure on $[0,t]$; for $g(t)=\rho e^{-t}$, the displayed $\lambda_t$ is the right-continuous post-jump version, whose predictable intensity is $\lambda_{t-}$ for $t>0$. (Equation~\eqref{intensityDefEq} includes all points counted by $N_t$, starting at $\tau_0=0$. The stated exponential kernel then fixes the corresponding right-continuous path version.)
- `def:prefs`: pinned reading: $\mathbb{N}=\{0,1,2,\dots\}$ in the definition of preference counts. (The preference-count map immediately following Definition~\ref{def:prefs} sends the classic parking function $\pi=(1,1)$ to $\kappa=(2,0)$. The claimed bijection with weakly increasing cumulative counts likewise permits zero increments.)
- `thm:coridthm1`: pinned reading: The integrand $\frac{e^{-u}-e^{-\rho}}{\rho e^{-\rho}-u e^{-u}}$ is interpreted by its continuous extension at $u=\rho$, with value $1/(1-\rho)$. (The change of variables in the proof of Corollary~\ref{corIdThm1} preserves the integral through a removable endpoint singularity; the displayed quotient has precisely this limit.)
- reading of the symbol `g`: The excitation kernel is a function $g:\mathbb{R}_+\to\mathbb{R}_+$. In Theorem~\ref{meanIdThm1}, Corollary~\ref{corIdThm1}: The kernel is $g(t)=\rho e^{-t}$ for $t\in\mathbb{R}_+$. — The paragraph containing equation \eqref{intensityDefEq} introduces the general kernel and then specifies $g(t)=\rho e^{-t}$ for the Markovian Hawkes cluster.
- reading of the symbol `\rho`: The kernel parameter satisfies $\rho\in\mathbb{R}_+$ and $\rho<1$ throughout the analysis. — Immediately after introducing the Borel cluster size, the paper states: "Accordingly, we will assume $\rho < 1$ throughout our analysis."
- reading of the symbol `\tau_i`: The actual cluster points are indexed by $i\in\{0,\dots,N-1\}$, with $0=\tau_0<\cdots<\tau_{N-1}$; no further actual cluster points are required. — Equation \eqref{intensityDefEq} indexes points starting at zero; the following paragraph states that the total number $N$ is finite almost surely, and the duration is defined as $\tau_{N-1}$.
- reading of the symbol `\tau`: The cluster duration is $\tau:=\tau_{N-1}$, with $\tau=0$ when $N=1$. In Theorem~\ref{meanIdThm1}, Corollary~\ref{corIdThm1}: For evaluating the duration law, $\tau$ also denotes the combinatorially constructed duration of Definition~\ref{def:combx-duration}: sample $N\sim\mathsf{Borel}(\rho)$; set $\tau=0$ if $N=1$; given $N=n+1$, sample the length-$n$ preference count $\kappa$ with the displayed law, then sample conditionally independent $Z_i\sim\mathrm{Exp}(\kappa_i^+-i+1)$ for $1\leq i\leq n$, and set $\tau=\sum_{i=1}^{N-1}Z_i$. This is a representation in distribution of the cluster duration. — The introduction defines the duration by the last cluster point. Definition~\ref{def:combx-duration} subsequently uses the same notation for the combinatorial construction, and the proof of Theorem~\ref{meanIdThm1} evaluates its mean through that construction.
- reading of the symbol `i`: $i$ is a locally bound nonnegative-integer coordinate or summation index; preference-count coordinates have $1\leq i\leq n$, generalized parking-function order indices have $1\leq i\leq m$, and in $\mathsf{H}_j=\sum_{i=1}^j1/i$ it has $1\leq i\leq j$. In Lemma~\ref{kappaCPMF1}: In the prefix-count product $\prod_{i=1}^m {n-k_{i-1}^+\choose k_i}$, $i\in\{1,\dots,m\}$. In Corollary~\ref{meanRecurSolve1}: In the displayed finite correction sum, $i\in\{0,\dots,m\}$. In Theorem~\ref{meanIdThm1}: In the proof's triple sum, $0\leq i\leq m\leq n-1$; after summing over $m$, $0\leq i\leq n-1$; after exchanging the sums over $i$ and $n$, $i\geq0$ and $n\geq i+1$. — Definitions~\ref{gpfDef1}, \ref{def:prefs}, and \ref{def:combx-duration} give the coordinate ranges; Theorem~\ref{meanIdThm1} defines the harmonic-number index. Corollary~\ref{meanRecurSolve1} and the proof of Theorem~\ref{meanIdThm1} display the zero-based summation ranges.
- reading of the symbol `n`: $n\in\mathbb{Z}_+$ is the number of available preferences in a generalized parking function and the common length of a classic parking function and its preference-count vectors. In Lemma~\ref{kappaCPMF1}, Lemma~\ref{meanRecur1}, Corollary~\ref{meanRecurSolve1}: $n$ is a fixed positive integer specifying the length of the preference-count vector. In Theorem~\ref{meanIdThm1}: In the proof, $n$ is a dummy index for conditioning on $N=n+1$: the initial sum ranges over $n\geq0$, its $n=0$ term is dropped, and subsequent length-$n$ preference-count terms have $n\geq1$. After exchanging summations, the inner sum has $n\geq i+1$. — Definition~\ref{gpfDef1} specifies $m$ preferences over $n$ available values; Definition~\ref{def:prefs} specifies length-$n$ counts. Definition~\ref{def:combx-duration} uses these counts given $N=n+1$, and the proof of Theorem~\ref{meanIdThm1} displays the corresponding summation ranges.
- reading of the symbol `m`: $m$ is an integer parameter whose role and admissible range depend on whether it denotes a parking-function length or a preference-count index; as a parking-function length it satisfies $1\leq m\leq n$. In Lemma~\ref{kappaCPMF1}: $m$ indexes the observed prefix $(\kappa_1,\dots,\kappa_m)$ for $1\leq m<n$; the distribution of $\kappa_1$ is supplied separately. In Lemma~\ref{meanRecur1}, Corollary~\ref{meanRecurSolve1}: $m\in\{0,1,\dots,n-1\}$ is the preference-count index, including the initial index zero. In Theorem~\ref{meanIdThm1}: $m$ is a summation index ranging from $0$ to $n-1$ for each $n\geq1$. — Definition~\ref{gpfDef1} requires positive lengths; Lemma~\ref{meanRecur1} explicitly includes zero, and the proof of Theorem~\ref{meanIdThm1} applies Corollary~\ref{meanRecurSolve1} starting at zero.
- reading of the symbol `\pi`: $\pi$ denotes a preference vector in $\mathbb{Z}_+^m$; it is a generalized parking function over $n$ preferences precisely when its sorted coordinates satisfy $\pi_{(i)}\leq n-m+i$ for $1\leq i\leq m$. In Lemma~\ref{kappaCPMF1}, Lemma~\ref{meanRecur1}: $\pi$ is a classic length-$n$ parking function, so its length is $n$ and its associated counts satisfy $\kappa_i(\pi)=\|\{\ell:\pi_\ell=i\}\|$. — Definition~\ref{gpfDef1} gives the general vector and criterion; the paragraph following Definition~\ref{def:prefs} and the proof of Lemma~\ref{kappaCPMF1} identify the classic length-$n$ vector underlying the counts.
- reading of the symbol `\kappa^+`: $\kappa^+$ is the cumulative vector associated with $\kappa$, with $\kappa_i^+=\sum_{j=1}^i\kappa_j$ for $1\leq i\leq n$. In Lemma~\ref{meanRecur1}: The cumulative coordinates are extended to index zero by $\kappa_0^+=0$ almost surely. — Definition~\ref{def:prefs} gives the cumulative map; Lemma~\ref{meanRecur1} additionally states $\PP{\kappa_0^+=0}=1$.
- reading of the symbol `k_i`: $k_i$, for $i\in\{1,\dots,n\}$, is a fixed nonnegative-integer value of $\kappa_i$; admissible full vectors satisfy $\sum_{i=1}^n k_i=n$ and $\sum_{j=1}^i k_j\geq i$ for every $1\leq i\leq n$. In Lemma~\ref{kappaCPMF1}: In the conditional PMF, $k_1,\dots,k_m$ specify the conditioning prefix on its positive-probability support, and $k_{m+1}$ is the candidate next count, with $0\leq k_{m+1}\leq n-k_m^+$ and $k_m^++k_{m+1}\geq m+1$. — Definition~\ref{def:prefs} supplies the preference-count support, equation~\eqref{kappaDist} evaluates the joint law at $(k_1,\dots,k_n)$, and Lemma~\ref{kappaCPMF1} evaluates conditional probabilities at fixed prefix values.
- reading of the symbol `k_i^+`: $k_i^+=\sum_{j=1}^i k_j$ is the fixed cumulative value associated with the realized preference counts, with $k_0^+=0$, $i\leq k_i^+\leq n$ for $1\leq i\leq n$, and $k_n^+=n$. — Definition~\ref{def:prefs} defines cumulative counts by partial sums. The proof of Lemma~\ref{kappaCPMF1} uses $k_m^+$ as the number of assigned coordinates and explicitly states that $k_0^+=0$.
- reading of the symbol `Z_i`: For $N=n+1\geq2$, the variables $(Z_i)_{i=1}^n$ are independent conditional on $\kappa$ and $N$, with conditional exponential rates $\kappa_i^+-i+1$; no $Z_i$ is required when $N=1$. — Steps (i)--(iii) of Definition~\ref{def:combx-duration} specify the size, conditioning, index range, and independent exponential sampling.
- reading of the symbol `Y_m`: $Y_m$ has its stated Bernoulli law conditional on $\kappa_m^+$ and is the component on which the conditional binomial law of $X_m$ depends. — The phrase "where, given $\kappa_m^+$" and the following joint specification in Lemma~\ref{kappaCPMF1}.
- reading of the symbol `X_m`: $X_m$ is an auxiliary count whose binomial law is conditional on both $\kappa_m^+$ and $Y_m$, with support $\{0,\dots,n-\kappa_m^+-Y_m\}$. — The defining display in Lemma~\ref{kappaCPMF1} specifies the laws given $\kappa_m^+$ and explicitly conditions $X_m$ on $Y_m$.
- reading of the symbol `k`: $k$ is the dummy integer summation index ranging over $\{0,\dots,n-\kappa_m^+\}$ when evaluating the conditional expectation given $\kappa_1,\dots,\kappa_m$. — The proof of Lemma~\ref{meanRecur1} explicitly writes both sums with bounds $k=0$ and $n-\kappa_m^+$ after stating $\kappa_{m+1}\leq n-\kappa_m^+$.
- reading of the symbol `\ell`: $\ell$ is a positive-integer dummy index, local to the preference-count map or summation in which it occurs. In Lemma~\ref{kappaCPMF1}, Lemma~\ref{meanRecur1}, Theorem~\ref{meanIdThm1}: In $\kappa_i(\pi)=\|\{\ell:\pi_\ell=i\}\|$, the index ranges over $\ell\in\{1,\dots,n\}$, the coordinates of $\pi$. In Theorem~\ref{meanIdThm1}: In the reindexed inner summation in the proof, $\ell=n-i$ ranges over $\{1,2,\dots\}$ because the preceding summation has $n\geq i+1$. — The paragraph following Definition~\ref{def:prefs} defines $\kappa_i(\pi)=\|\{\ell:\pi_\ell=i\}\|$ for a length-$n$ parking function; the proof of Theorem~\ref{meanIdThm1} explicitly reindexes its inner sum by $\ell=n-i$.

## Added conditions

| id | where | class | condition |
| --- | --- | --- | --- |
| `ass:pin-2` | `thm:meanidthm1` | V1.5 bookkeeping | $\mathbb{N}=\{0,1,2,\dots\}$ in the domain $\kappa\in\mathbb{N}^n$ of Definition~\ref{def:prefs}. (pins reading of def:prefs: Definition~\ref{def:prefs} asserts a bijection with cumulative preference counts, and the following paragraph identifies counts with numbers of drivers choosing each preference. The classic parking function $\pi=(1,1)$ gives $\kappa=(2,0)$ and cumulative vector $(2,2)$, requiring zero to be allowed.) |
| `ass:pin-3` | `thm:meanidthm1` | V1.5 bookkeeping | $n\in\mathbb{Z}_+$ and $m\in\{0,\dots,n-1\}$. (pins reading of ass:meanrecursolve1-index: Corollary~\ref{meanRecurSolve1} uses the coordinate $\kappa_{m+1}^+$ and a sum beginning at zero; the proof of Theorem~\ref{meanIdThm1} applies it for exactly $0\leq m\leq n-1$.) |
| `ass:pin-4` | `thm:meanidthm1` | V1.5 bookkeeping | $N_t=\sum_{i=0}^{N-1}\mathbf{1}\{\tau_i\leq t\}$, and the integral in \eqref{intensityDefEq} is against the cluster point measure on $[0,t]$; for $g(t)=\rho e^{-t}$, the displayed $\lambda_t$ is the right-continuous post-jump version, whose predictable intensity is $\lambda_{t-}$ for $t>0$. (pins reading of def:intensitydefeq: Equation~\eqref{intensityDefEq} includes all points counted by $N_t$, starting at $\tau_0=0$. The stated exponential kernel then fixes the corresponding right-continuous path version.) |
| `ass:pin-5` | `thm:meanidthm1` | V1.5 bookkeeping | $\mathbb{N}=\{0,1,2,\dots\}$ in the definition of preference counts. (pins reading of def:prefs: The preference-count map immediately following Definition~\ref{def:prefs} sends the classic parking function $\pi=(1,1)$ to $\kappa=(2,0)$. The claimed bijection with weakly increasing cumulative counts likewise permits zero increments.) |
| `ass:pin-6` | `thm:meanidthm1` | V1.5 bookkeeping | The $\tau$ constructed in Definition~\ref{def:combx-duration} has the same distribution as the cluster duration $\tau:=\tau_{N-1}$ defined from \eqref{intensityDefEq}. (pins reading of def:combx-duration: The paragraph immediately following Definition~\ref{def:combx-duration} identifies the two constructions as equivalent and uses the combinatorial construction for the main proofs; the introduction explicitly describes the conditional representation as equivalence in distribution.) |
| `ass:pin-1` | `thm:coridthm1` | V1.5 bookkeeping | The integrand $\frac{e^{-u}-e^{-\rho}}{\rho e^{-\rho}-u e^{-u}}$ is interpreted by its continuous extension at $u=\rho$, with value $1/(1-\rho)$. (pins reading of thm:coridthm1: The change of variables in the proof of Corollary~\ref{corIdThm1} preserves the integral through a removable endpoint singularity; the displayed quotient has precisely this limit.) |
| `ass:pin-2` | `thm:coridthm1` | V1.5 bookkeeping | $\mathbb{N}=\{0,1,2,\dots\}$ in the domain $\kappa\in\mathbb{N}^n$ of Definition~\ref{def:prefs}. (pins reading of def:prefs: Definition~\ref{def:prefs} asserts a bijection with cumulative preference counts, and the following paragraph identifies counts with numbers of drivers choosing each preference. The classic parking function $\pi=(1,1)$ gives $\kappa=(2,0)$ and cumulative vector $(2,2)$, requiring zero to be allowed.) |
| `ass:pin-3` | `thm:coridthm1` | V1.5 bookkeeping | $n\in\mathbb{Z}_+$ and $m\in\{0,\dots,n-1\}$. (pins reading of ass:meanrecursolve1-index: Corollary~\ref{meanRecurSolve1} uses the coordinate $\kappa_{m+1}^+$ and a sum beginning at zero; the proof of Theorem~\ref{meanIdThm1} applies it for exactly $0\leq m\leq n-1$.) |
| `ass:pin-4` | `thm:coridthm1` | V1.5 bookkeeping | $N_t=\sum_{i=0}^{N-1}\mathbf{1}\{\tau_i\leq t\}$, and the integral in \eqref{intensityDefEq} is against the cluster point measure on $[0,t]$; for $g(t)=\rho e^{-t}$, the displayed $\lambda_t$ is the right-continuous post-jump version, whose predictable intensity is $\lambda_{t-}$ for $t>0$. (pins reading of def:intensitydefeq: Equation~\eqref{intensityDefEq} includes all points counted by $N_t$, starting at $\tau_0=0$. The stated exponential kernel then fixes the corresponding right-continuous path version.) |
| `ass:pin-5` | `thm:coridthm1` | V1.5 bookkeeping | $\mathbb{N}=\{0,1,2,\dots\}$ in the definition of preference counts. (pins reading of def:prefs: The preference-count map immediately following Definition~\ref{def:prefs} sends the classic parking function $\pi=(1,1)$ to $\kappa=(2,0)$. The claimed bijection with weakly increasing cumulative counts likewise permits zero increments.) |
| `ass:pin-6` | `thm:coridthm1` | V1.5 bookkeeping | The $\tau$ constructed in Definition~\ref{def:combx-duration} has the same distribution as the cluster duration $\tau:=\tau_{N-1}$ defined from \eqref{intensityDefEq}. (pins reading of def:combx-duration: The paragraph immediately following Definition~\ref{def:combx-duration} identifies the two constructions as equivalent and uses the combinatorial construction for the main proofs; the introduction explicitly describes the conditional representation as equivalence in distribution.) |
| `ass:pin-2` | `lem:kappacpmf1` | V1.5 bookkeeping | $\mathbb{N}=\{0,1,2,\dots\}$ in the domain $\kappa\in\mathbb{N}^n$ of Definition~\ref{def:prefs}. (pins reading of def:prefs: Definition~\ref{def:prefs} asserts a bijection with cumulative preference counts, and the following paragraph identifies counts with numbers of drivers choosing each preference. The classic parking function $\pi=(1,1)$ gives $\kappa=(2,0)$ and cumulative vector $(2,2)$, requiring zero to be allowed.) |
| `ass:pin-5` | `lem:kappacpmf1` | V1.5 bookkeeping | $\mathbb{N}=\{0,1,2,\dots\}$ in the definition of preference counts. (pins reading of def:prefs: The preference-count map immediately following Definition~\ref{def:prefs} sends the classic parking function $\pi=(1,1)$ to $\kappa=(2,0)$. The claimed bijection with weakly increasing cumulative counts likewise permits zero increments.) |
| `ass:pin-2` | `lem:meanrecur1` | V1.5 bookkeeping | $\mathbb{N}=\{0,1,2,\dots\}$ in the domain $\kappa\in\mathbb{N}^n$ of Definition~\ref{def:prefs}. (pins reading of def:prefs: Definition~\ref{def:prefs} asserts a bijection with cumulative preference counts, and the following paragraph identifies counts with numbers of drivers choosing each preference. The classic parking function $\pi=(1,1)$ gives $\kappa=(2,0)$ and cumulative vector $(2,2)$, requiring zero to be allowed.) |
| `ass:pin-5` | `lem:meanrecur1` | V1.5 bookkeeping | $\mathbb{N}=\{0,1,2,\dots\}$ in the definition of preference counts. (pins reading of def:prefs: The preference-count map immediately following Definition~\ref{def:prefs} sends the classic parking function $\pi=(1,1)$ to $\kappa=(2,0)$. The claimed bijection with weakly increasing cumulative counts likewise permits zero increments.) |
| `ass:pin-2` | `thm:meanrecursolve1` | V1.5 bookkeeping | $\mathbb{N}=\{0,1,2,\dots\}$ in the domain $\kappa\in\mathbb{N}^n$ of Definition~\ref{def:prefs}. (pins reading of def:prefs: Definition~\ref{def:prefs} asserts a bijection with cumulative preference counts, and the following paragraph identifies counts with numbers of drivers choosing each preference. The classic parking function $\pi=(1,1)$ gives $\kappa=(2,0)$ and cumulative vector $(2,2)$, requiring zero to be allowed.) |
| `ass:pin-3` | `thm:meanrecursolve1` | V1.5 bookkeeping | $n\in\mathbb{Z}_+$ and $m\in\{0,\dots,n-1\}$. (pins reading of ass:meanrecursolve1-index: Corollary~\ref{meanRecurSolve1} uses the coordinate $\kappa_{m+1}^+$ and a sum beginning at zero; the proof of Theorem~\ref{meanIdThm1} applies it for exactly $0\leq m\leq n-1$.) |
| `ass:pin-5` | `thm:meanrecursolve1` | V1.5 bookkeeping | $\mathbb{N}=\{0,1,2,\dots\}$ in the definition of preference counts. (pins reading of def:prefs: The preference-count map immediately following Definition~\ref{def:prefs} sends the classic parking function $\pi=(1,1)$ to $\kappa=(2,0)$. The claimed bijection with weakly increasing cumulative counts likewise permits zero increments.) |

## Conditions assumed

### Cited results

None: no result rests on a theorem imported from the literature.

### Deferred substrate gates

None: every substrate this run needed was built and proved.

## Unresolved / notes

- run-level `ass:prefs-total`: [note, V1.5] pinned reading: $\mathbb{N}=\{0,1,2,\dots\}$ in the domain $\kappa\in\mathbb{N}^n$ of Definition~\ref{def:prefs}. (Definition~\ref{def:prefs} asserts a bijection with cumulative preference counts, and the following paragraph identifies counts with numbers of drivers choosing each preference. The classic parking function $\pi=(1,1)$ gives $\kappa=(2,0)$ and cumulative vector $(2,2)$, requiring zero to be allowed.)
- run-level `ass:meanrecursolve1-index`: [note, V1.5] pinned reading: $n\in\mathbb{Z}_+$ and $m\in\{0,\dots,n-1\}$. (Corollary~\ref{meanRecurSolve1} uses the coordinate $\kappa_{m+1}^+$ and a sum beginning at zero; the proof of Theorem~\ref{meanIdThm1} applies it for exactly $0\leq m\leq n-1$.)
- run-level `def:intensitydefeq`: [note, V1.5] pinned reading: $N_t=\sum_{i=0}^{N-1}\mathbf{1}\{\tau_i\leq t\}$, and the integral in \eqref{intensityDefEq} is against the cluster point measure on $[0,t]$; for $g(t)=\rho e^{-t}$, the displayed $\lambda_t$ is the right-continuous post-jump version, whose predictable intensity is $\lambda_{t-}$ for $t>0$. (Equation~\eqref{intensityDefEq} includes all points counted by $N_t$, starting at $\tau_0=0$. The stated exponential kernel then fixes the corresponding right-continuous path version.)
- run-level `def:prefs`: [note, V1.5] pinned reading: $\mathbb{N}=\{0,1,2,\dots\}$ in the definition of preference counts. (The preference-count map immediately following Definition~\ref{def:prefs} sends the classic parking function $\pi=(1,1)$ to $\kappa=(2,0)$. The claimed bijection with weakly increasing cumulative counts likewise permits zero increments.)
- run-level `def:combx-duration`: [note, V1.5] pinned reading: The $\tau$ constructed in Definition~\ref{def:combx-duration} has the same distribution as the cluster duration $\tau:=\tau_{N-1}$ defined from \eqref{intensityDefEq}. (The paragraph immediately following Definition~\ref{def:combx-duration} identifies the two constructions as equivalent and uses the combinatorial construction for the main proofs; the introduction explicitly describes the conditional representation as equivalence in distribution.)
- run-level `symbol \lambda_t`: [note, V1.5] symbol table corrected: def "The cluster intensity is $\lambda_t=\int_0^t g(t-u)\mathrm{d}N_u=\sum_{i=0}^{N_t-1}g(t-\tau_i)$." (The recorded entry supplies only an equation reference. The defining convolution and point sum are needed to specify the intensity.)
- run-level `symbol N_t`: [note, V1.5] symbol table corrected: def "The cluster counting process counts the initial point $\tau_0=0$ and subsequent cluster points: $N_t=\sum_{i=0}^{N-1}\mathbf{1}\{\tau_i\leq t\}$ for $t\geq0$, so $N_0=1$." (Merely calling this a paired counting process omits its initial point convention. The sum from $i=0$ to $N_t-1$ in equation \eqref{intensityDefEq} and the definition of total cluster size determine that convention.)
- run-level `symbol m`: [note, V1.5] symbol table corrected: space "$\{0,1,2,\dots\}$" (The positive-integer space excludes the explicitly used value zero. Its reuse as a prefix or summation index is distinct from its positive parking-function length role.)
- run-level `symbol Z_i`: [note, V1.5] symbol table corrected: type "conditionally exponential random variable", def "Given $N=n+1$ and $\kappa$ with cumulative form $\kappa^+$, sample $Z_i\sim\mathrm{Exp}(\kappa_i^+-i+1)$ independently for each $i\in\{1,\dots,n\}$; the duration is $\tau=\sum_{i=1}^{N-1}Z_i$." (The recorded rate is correct, but the vague term omits the exponential law and conditional independence. Independence is conditional on the sampled preference count.)
- run-level `symbol Y_m`: [note, V1.5] symbol table corrected: def "Given $\kappa_m^+$, $Y_m\sim\mathsf{Bern}\left((n-\kappa_m^+)/((n-m)(\kappa_m^+-m+1))\right)$ in the representation $\kappa_{m+1}\mid(\kappa_1,\dots,\kappa_m)\stackrel{\mathsf D}{=}X_m+Y_m$." (The entry omits the success probability and conditioning. The paper specifies a hierarchical conditional construction, without asserting independence of $X_m$ and $Y_m$.)
- run-level `symbol X_m`: [note, V1.5] symbol table corrected: def "Given $\kappa_m^+$, $X_m\mid Y_m\sim\mathsf{Bin}\left(n-\kappa_m^+-Y_m,1/(n-m+1)\right)$, with $\kappa_{m+1}\mid(\kappa_1,\dots,\kappa_m)\stackrel{\mathsf D}{=}X_m+Y_m$." (The recorded label omits the binomial parameters and its dependence on the Bernoulli component. The representation specifies equality in conditional distribution, rather than a pathwise identity.)
- note on `ass:meanrecursolve1-index`: pinned reading: $n\in\mathbb{Z}_+$ and $m\in\{0,\dots,n-1\}$. (Corollary~\ref{meanRecurSolve1} uses the coordinate $\kappa_{m+1}^+$ and a sum beginning at zero; the proof of Theorem~\ref{meanIdThm1} applies it for exactly $0\leq m\leq n-1$.)
- note on `ass:prefs-total`: pinned reading: $\mathbb{N}=\{0,1,2,\dots\}$ in the domain $\kappa\in\mathbb{N}^n$ of Definition~\ref{def:prefs}. (Definition~\ref{def:prefs} asserts a bijection with cumulative preference counts, and the following paragraph identifies counts with numbers of drivers choosing each preference. The classic parking function $\pi=(1,1)$ gives $\kappa=(2,0)$ and cumulative vector $(2,2)$, requiring zero to be allowed.)
- note on `def:combx-duration`: pinned reading: The $\tau$ constructed in Definition~\ref{def:combx-duration} has the same distribution as the cluster duration $\tau:=\tau_{N-1}$ defined from \eqref{intensityDefEq}. (The paragraph immediately following Definition~\ref{def:combx-duration} identifies the two constructions as equivalent and uses the combinatorial construction for the main proofs; the introduction explicitly describes the conditional representation as equivalence in distribution.)
- note on `def:intensitydefeq`: pinned reading: $N_t=\sum_{i=0}^{N-1}\mathbf{1}\{\tau_i\leq t\}$, and the integral in \eqref{intensityDefEq} is against the cluster point measure on $[0,t]$; for $g(t)=\rho e^{-t}$, the displayed $\lambda_t$ is the right-continuous post-jump version, whose predictable intensity is $\lambda_{t-}$ for $t>0$. (Equation~\eqref{intensityDefEq} includes all points counted by $N_t$, starting at $\tau_0=0$. The stated exponential kernel then fixes the corresponding right-continuous path version.)
- note on `def:prefs`: pinned reading: $\mathbb{N}=\{0,1,2,\dots\}$ in the definition of preference counts. (The preference-count map immediately following Definition~\ref{def:prefs} sends the classic parking function $\pi=(1,1)$ to $\kappa=(2,0)$. The claimed bijection with weakly increasing cumulative counts likewise permits zero increments.)
- note on `symbol \lambda_t`: symbol table corrected: def "The cluster intensity is $\lambda_t=\int_0^t g(t-u)\mathrm{d}N_u=\sum_{i=0}^{N_t-1}g(t-\tau_i)$." (The recorded entry supplies only an equation reference. The defining convolution and point sum are needed to specify the intensity.)
- note on `symbol m`: symbol table corrected: space "$\{0,1,2,\dots\}$" (The positive-integer space excludes the explicitly used value zero. Its reuse as a prefix or summation index is distinct from its positive parking-function length role.)
- note on `symbol N_t`: symbol table corrected: def "The cluster counting process counts the initial point $\tau_0=0$ and subsequent cluster points: $N_t=\sum_{i=0}^{N-1}\mathbf{1}\{\tau_i\leq t\}$ for $t\geq0$, so $N_0=1$." (Merely calling this a paired counting process omits its initial point convention. The sum from $i=0$ to $N_t-1$ in equation \eqref{intensityDefEq} and the definition of total cluster size determine that convention.)
- note on `symbol X_m`: symbol table corrected: def "Given $\kappa_m^+$, $X_m\mid Y_m\sim\mathsf{Bin}\left(n-\kappa_m^+-Y_m,1/(n-m+1)\right)$, with $\kappa_{m+1}\mid(\kappa_1,\dots,\kappa_m)\stackrel{\mathsf D}{=}X_m+Y_m$." (The recorded label omits the binomial parameters and its dependence on the Bernoulli component. The representation specifies equality in conditional distribution, rather than a pathwise identity.)
- note on `symbol Y_m`: symbol table corrected: def "Given $\kappa_m^+$, $Y_m\sim\mathsf{Bern}\left((n-\kappa_m^+)/((n-m)(\kappa_m^+-m+1))\right)$ in the representation $\kappa_{m+1}\mid(\kappa_1,\dots,\kappa_m)\stackrel{\mathsf D}{=}X_m+Y_m$." (The entry omits the success probability and conditioning. The paper specifies a hierarchical conditional construction, without asserting independence of $X_m$ and $Y_m$.)
- note on `symbol Z_i`: symbol table corrected: type "conditionally exponential random variable", def "Given $N=n+1$ and $\kappa$ with cumulative form $\kappa^+$, sample $Z_i\sim\mathrm{Exp}(\kappa_i^+-i+1)$ independently for each $i\in\{1,\dots,n\}$; the duration is $\tau=\sum_{i=1}^{N-1}Z_i$." (The recorded rate is correct, but the vague term omits the exponential law and conditional independence. Independence is conditional on the sampled preference count.)
- note on `thm:coridthm1`: pinned reading: The integrand $\frac{e^{-u}-e^{-\rho}}{\rho e^{-\rho}-u e^{-u}}$ is interpreted by its continuous extension at $u=\rho$, with value $1/(1-\rho)$. (The change of variables in the proof of Corollary~\ref{corIdThm1} preserves the integral through a removable endpoint singularity; the displayed quotient has precisely this limit.)

### V1 lint warnings

- thm:meanidthm1: meanIdThm1 references \ref{meanRecurSolve1} (meanRecurSolve1) but `depends_on` lacks ass:meanrecursolve1-index, ass:meanrecursolve1-law; V1.5 must confirm whether the paper assumes it or merely mentions it

## Lean evidence

- build of the run barrel: **ok**
- source scan (sorry / admit / axiom): clean

| declaration | axioms |
| --- | --- |
| `Papers.HawkesD75660b.meanDurationIdentity` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.HawkesD75660b.meanDurationIntegral` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.HawkesD75660b.conditionalPreferenceCountLaw` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.HawkesD75660b.meanRecurrence` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.HawkesD75660b.meanRecurrenceSolution` | clean — `propext`, `Classical.choice`, `Quot.sound` |

## Inputs

| artifact | status |
| --- | --- |
| `discovery/v1_scope.json` | present (8 environment(s)) |
| `discovery/v1_5_review.json` | present (verdict PASS) |
| `formalization/crosswalk_full.json` | present (304 object(s)) |
| `graph.json` | present (308 node(s)) |
| Lean evidence | collected (build ok, 0 scan issue(s), 5 declaration(s)) |

## Annotated paper

Annotated paper: `annotated/main.tex` (21 annotation(s), 1 unlocated; index `annotated/ANNOTATIONS.md`); PDF: `annotated/main.pdf`
