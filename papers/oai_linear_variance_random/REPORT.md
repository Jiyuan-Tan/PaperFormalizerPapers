# Correctness report — oai_linear_variance_random

**Verdict: NO ERROR FOUND**

**Paper: MINOR ISSUES — no main result is shown false or weakened**

Minor:

- `n`: notation ambiguous; a reading was pinned
- `j`: notation ambiguous; a reading was pinned
- `m`: notation ambiguous; a reading was pinned
- `C`: notation ambiguous; a reading was pinned
- `n_0`: notation ambiguous; a reading was pinned
- `i`: notation ambiguous; a reading was pinned
- `s`: notation ambiguous; a reading was pinned
- `u`: notation ambiguous; a reading was pinned
- `S`: notation ambiguous; a reading was pinned
- `a`: notation ambiguous; a reading was pinned
- `q_j`: notation ambiguous; a reading was pinned
- `d`: notation ambiguous; a reading was pinned
- `p`: notation ambiguous; a reading was pinned
- `T`: notation ambiguous; a reading was pinned
- `T^{(i)}`: notation ambiguous; a reading was pinned
- `D_i`: notation ambiguous; a reading was pinned
- `A_m`: notation ambiguous; a reading was pinned
- `S_m`: notation ambiguous; a reading was pinned
- `Z`: notation ambiguous; a reading was pinned
- `V`: notation ambiguous; a reading was pinned
- `\cG_m`: notation ambiguous; a reading was pinned
- `\cH_m`: notation ambiguous; a reading was pinned
- `p_m`: notation ambiguous; a reading was pinned
- `W_m`: notation ambiguous; a reading was pinned
- `r_n`: notation ambiguous; a reading was pinned
- `p_1`: notation ambiguous; a reading was pinned
- `p_2`: notation ambiguous; a reading was pinned
- `m_1`: notation ambiguous; a reading was pinned
- `m_2`: notation ambiguous; a reading was pinned
- `a(p_1,p_2)`: notation ambiguous; a reading was pinned
- `\eta`: notation ambiguous; a reading was pinned
- `t`: notation ambiguous; a reading was pinned
- `Y`: notation ambiguous; a reading was pinned
- `\mathcal F_i`: notation ambiguous; a reading was pinned
- `J_j`: notation ambiguous; a reading was pinned
- `p_{\rm coll}`: notation ambiguous; a reading was pinned
- `c_0`: notation ambiguous; a reading was pinned
- `H_n'`: notation ambiguous; a reading was pinned

11 result(s) of the paper were examined. None was found wrong as printed. In Lean: 10 proved, 1 taken from the literature as cited, 0 not certified, 0 not formalized.

## What was wrong and what was done

No error was found in the results examined.

## Clarifications (not errors)

Nothing in this section is an error of the paper. Each item is something the paper determines but does not say, made explicit so that the statements can be read, and formalized, in one way.

**Notation.**

- $n$: $n\ge3$ is the integer number of variables in the proper 3-clause process. In Lemma~\ref{lem:omission}, Lemma~\ref{lem:tests}, Lemma~\ref{lem:occupation}, Corollary~\ref{cor:duration}, Proposition~\ref{prop:delay}, Lemma~\ref{lem:moments}: The variable count satisfies $n\ge6$.
- $j$: $j$ is an integer index: clause indices in $C_j$ start at $1$, whereas the number of auxiliary proper 2-clauses in $q_j(S)$ starts at $0$; other summation ranges are those displayed locally.
- $m$: $m$ is a nonnegative integer indexing prefixes of the clause process. In Lemma~\ref{lem:tests}, Lemma~\ref{lem:occupation}: The time index satisfies $i\le m<L$. In Proposition~\ref{prop:delay}: In the proof's sums over prefix times, $m$ ranges from $i$ to $L-1$.
- $C$: $C$ has a local meaning: an absolute finite constant in the variance bounds or a clause in the survivor-set construction. In Theorem~\ref{thm:main}, Corollary~\ref{cor:window}: $C$ is an absolute finite constant satisfying $\Var(H_n)\le Cn$ for every integer $n\ge3$. In Lemma~\ref{lem:potential}: $C$ in the potential increment denotes an independent uniform proper 3-clause on the $u$ variables.
- $n_0$: $n_0$ is an absolute deterministic threshold, independent of $n$, such that $\Var(H_n)\ge cn$ for every admissible integer $n\ge n_0$.
- $i$: $i$ is an integer index with $1\le i\le L$ specifying the omitted clause $C_i$; omission retains the original indices of all other clauses.
- $s$: $s$ is an integer prefix index summed over $m\le s<L$, where $i\le m<L$.
- $u$: $u\ge3$ is the integer number of coordinates of the assignment space on which the clause-survival and killing functionals are evaluated. In Lemma~\ref{lem:tests}, Lemma~\ref{lem:occupation}, Corollary~\ref{cor:duration}, Proposition~\ref{prop:delay}: $u=n-3$ is the number of nonroot variables, with $n\ge6$.
- $S$: $S$ denotes a subset of $\{0,1\}^u$ to which the clause-survival and killing functionals are applied. In Lemma~\ref{lem:one}: $S$ is nonempty. In Lemma~\ref{lem:tests}, Lemma~\ref{lem:occupation}, Corollary~\ref{cor:duration}, Proposition~\ref{prop:delay}: The assignment sets used here are $S_m$, for $i\le m\le L$: the nonroot assignments that, together with the root assignment $w$ falsifying $C_i$, satisfy $B_m^{(i)}$; these sets are $\cG_m$-measurable and decrease with $m$.
- $a$: $a$ is a positive deterministic parameter whose meaning is local to its occurrence. In Lemma~\ref{lem:one}, Lemma~\ref{lem:potential}, Lemma~\ref{lem:tests}, Lemma~\ref{lem:occupation}, Corollary~\ref{cor:duration}, Proposition~\ref{prop:delay}: In the short-clause notation, $a\in\{2,3\}$ is the number of distinct variables in a proper clause. In Theorem~\ref{thm:wilson}: $a(p_1,p_2)>0$ is a constant depending on the fixed levels $1>p_1>p_2>0$ and independent of $n,m_1,m_2$.
- $q_j$: For every integer $j\ge0$ and $S\subseteq\{0,1\}^u$, $q_j(S)$ is the probability that $j$ independent random proper 2-clauses kill $S$, with $q_j(\varnothing)=1$ and $q_0(S)=0$ for $S\ne\varnothing$.
- $d$: $d$ is a positive integer used as the clause count in $q_d(S)$ and the length of the sum $P_d(S)=\sum_{j=0}^{d-1}q_j(S)$. In Lemma~\ref{lem:potential}: $d\ge1$ is an arbitrary fixed integer. In Lemma~\ref{lem:tests}, Lemma~\ref{lem:occupation}, Corollary~\ref{cor:duration}, Proposition~\ref{prop:delay}, Lemma~\ref{lem:moments}: $d=\max\{1,Z\}$, where $Z$ counts indices $j\le L$, excluding $i$, whose clauses meet at least one root; in particular, $d$ is $\cE$-measurable.
- $p$: In the introductory killing-probability shorthand $p=q_d(S)$, whereas in $r_n(p)$ the symbol $p$ denotes a deterministic probability level satisfying $0<p<1$.
- $T$: $T=\min(H_n,L)$ is defined for $n\ge6$, with $L=10n$, and is a function of the first $L$ clauses.
- $T^{(i)}$: For $n\ge6$ and $1\le i\le L=10n$, $T^{(i)}$ is the first unsatisfiable original index of $B_m^{(i)}$, capped at $L$; it is a function of $(C_j)_{1\le j\le L,\,j\ne i}$ and does not depend on $C_i$.
- $D_i$: For $n\ge6$, $L=10n$ and $1\le i\le L$, $D_i=T^{(i)}-T\ge0$ is the delay obtained by omitting $C_i$ while retaining all original clause indices; it is a function of the first $L$ clauses. In Lemma~\ref{lem:tests}, Lemma~\ref{lem:occupation}, Corollary~\ref{cor:duration}, Proposition~\ref{prop:delay}: $D_i=\sum_{m=i}^{L-1}\ind_{A_m}$, where $A_m=\{T\le m<T^{(i)}\}$.
- $A_m$: $A_m$ is defined for integer indices $i\le m<L$ and is $\cH_m$-measurable.
- $S_m$: For $i\le m\le L$, $S_m\subseteq\{0,1\}^u$, with $u=n-3$, is the $\cG_m$-measurable set of nonroot assignments that together with $w$ satisfy $B_m$, and these sets decrease with $m$.
- $Z$: $Z$ is the $\cE$-measurable count $\bigl|\{j:1\le j\le L,\ j\ne i,\ C_j\text{ meets }R\}\bigr|$, counting indices throughout the capped exposure, including future indices.
- $V$: $V=\sum_{1\le j\le L,\,j\ne i}\ind_{\{|\operatorname{vars}(C_j)\cap R|\ge2\}}$ counts collision indices throughout the entire capped exposure and is $\cE$-measurable.
- $\cG_m$: $\cG_m=\cE\vee\sigma(\text{ordinary contents through index }m)$ is defined for integer indices $i\le m\le L$; the hidden nonroot parts of test clauses are not revealed in this filtration.
- $\cH_m$: $\cH_m=\cG_m\vee\sigma(\text{test parts through index }m)$ is defined for integer indices $i\le m\le L$ and includes the complete future clause-type information already contained in $\cE$.
- $p_m$: For $i\le m\le L$, $p_m=q_d(S_m)$ is $\cG_m$-measurable and nondecreasing in $m$.
- $W_m$: For $i\le m<L$, $W_m$ is the $\cG_m$-measurable quantity $\min\{L,Kd^\beta p_m^{-\beta}\}$ when $p_m>0$, and $L$ when $p_m=0$.
- $r_n$: For each $n\ge3$ and $0<p<1$, $r_n(p)=\min\{m\ge0:s_n(m)\le p\}$ is a finite positive integer determined by the unconditional distribution of $H_n$.
- $p_1$: $p_1$ is a fixed deterministic probability level, independent of $n$, with $0<p_2<p_1<1$.
- $p_2$: $p_2$ is a fixed deterministic probability level, independent of $n$, with $0<p_2<p_1<1$.
- $m_1$: $m_1$ is a deterministic nonnegative integer endpoint satisfying $s_n(m_1)\ge p_1$; it may depend on $n$ and need not be the integer level location $r_n(p_1)$.
- $m_2$: $m_2$ is a deterministic nonnegative integer endpoint satisfying $s_n(m_2)\le p_2$; it may depend on $n$ and need not be the integer level location $r_n(p_2)$.
- $a(p_1,p_2)$: $a(p_1,p_2)>0$ is a deterministic constant depending only on the fixed levels $p_1,p_2$, independent of $n$ and of the admissible endpoints $m_1,m_2$.
- $\eta$: $\eta\in(0,1/2)$ is a fixed deterministic probability level, independent of $n$; constants in $\Theta_\eta(\sqrt n)$ may depend on $\eta$.
- $t$: $t$ is a deterministic real parameter with a meaning local to its occurrence. In Lemma~\ref{lem:one}: $t$ is the argument of $(t)_a=t(t-1)\cdots(t-a+1)$; the evaluations used are $t=b$ and $t=u$. In Corollary~\ref{cor:window}: $t=(2Cn/\eta)^{1/2}$, with $C$ the upper-bound constant from Theorem~\ref{thm:main}; this deviation radius varies with $n$.
- $Y$: $Y\subseteq S$ is the survivor set obtained by imposing the auxiliary proper 2-clauses. In Lemma~\ref{lem:potential}: In the proof, $j$ is a fixed nonnegative integer and $Y$ consists of exactly those $z\in S$ satisfying all $j$ auxiliary clauses; thus $Y=S$ when $j=0$, and $Y$ may be empty.
- $\mathcal F_i$: For $0\le i\le L$, $\mathcal F_i=\sigma(C_1,\ldots,C_i)$, with $\mathcal F_0$ the trivial sigma-field.
- $J_j$: For $1\le j\le L$ with $j\ne i$, $J_j$ is the event that $C_j$ meets at least two variables of $R$.
- $p_{\rm coll}$: $p_{\rm coll}$ is the common probability $\Prb(J_j)$ for any $1\le j\le L$ with $j\ne i$; it depends only on $n$.
- $c_0$: $c_0>0$ is an absolute constant, independent of $n$, such that $b_n-a_n\ge c_0\sqrt n$ for all sufficiently large $n$.
- $H_n'$: $H_n'$ has the same distribution as $H_n$ and is independent of $H_n$.

## What was proved in Lean, and what was not

A result is proved in Lean when a Lean declaration reviewed as stating it has a complete proof using no axiom beyond the standard ones. For a corrected result, the corrected statement is the one formalized.

| Result | Formal status | Lean declaration | Axioms |
| --- | --- | --- | --- |
| Theorem 1.1 | proved in Lean, given 1 cited result(s) | `Papers.OaiLinearVarianceRandom.var_hittingTime_theta_n` (`TMain.lean:124`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 2.1 | proved in Lean | `Papers.OaiLinearVarianceRandom.oneKillProb_two_rpow_le` (`Helpers/AssignmentSets.lean:347`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 2.2 | proved in Lean | `Papers.OaiLinearVarianceRandom.potential_drift` (`Helpers/Potential.lean:244`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 3.1 | proved in Lean | `Papers.OaiLinearVarianceRandom.variance_cappedTime_le_sum_delay_sq` (`Helpers/Omission.lean:119`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 3.2 | proved in Lean | `Papers.OaiLinearVarianceRandom.condProb_pivotal_le` (`Helpers/Pivotality.lean:36`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 4.1 | proved in Lean | `Papers.OaiLinearVarianceRandom.condExp_occupation_le` (`Helpers/Pivotality.lean:85`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Corollary 4.2 | proved in Lean | `Papers.OaiLinearVarianceRandom.condExp_pivotal_duration_le` (`TDuration.lean:82`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Proposition 4.3 | proved in Lean | `Papers.OaiLinearVarianceRandom.condExp_delay_sq_le` (`TDelay.lean:25`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 4.4 | proved in Lean | `Papers.OaiLinearVarianceRandom.incidence_moments_bound` (`Helpers/Moments.lean:292`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Theorem 5.1 | taken from the literature as cited; not proved here | — | — |
| Corollary 5.2 | proved in Lean, given 1 cited result(s) | `Papers.OaiLinearVarianceRandom.levelLocation_window_theta_sqrt` (`TWindow.lean:30`) | the standard ones only (propext, Classical.choice, Quot.sound) |

**Taken from the literature, not proved here.**

- Wilson2002, Corollary 4 — checked against arXiv:math/0005136 e-print (fetched by the runner; the arXiv version may differ from the published one)

  What Lean assumes for it: `Papers.OaiLinearVarianceRandom.WilsonSeparation` (`Basic.lean:556`)

  ```lean
  def WilsonSeparation : Sort 0 :=
    ∀ p1 p2 : ℝ, WilsonLevels p1 p2 →
      ∃ a : ℝ, 0 < a ∧ -- @realizes a(p_1,p_2)(positive constant depending only on fixed levels)
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → MainN n →
        ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (Cseq : ℕ → Ω → ProperClause n), IsUniformClauseProcess μ Cseq →
          ∀ m1 m2 : ℤ,
            WilsonEndpoints (survivalFnInt μ (fun ω => hittingTime (fun j => Cseq j ω)))
              p1 p2 m1 m2 → a * Real.sqrt n ≤ (m2 : ℝ) - (m1 : ℝ)
  ```

The Lean development builds; it contains no `sorry`, `admit` or added axiom.

## The corrected paper

`bundle/corrected_paper/` holds the paper as it reads after the corrections, as plain source in the author's own class and layout, compiled to `bundle/corrected_paper/main.pdf` (11 pages). `bundle/MATCH.md` sets each result beside its Lean declaration; `bundle/lean/` holds the Lean code.

The mechanical checks leave nothing open.

# Technical appendix

The records behind the report above, by the run's own identifiers.

- paper: `main.tex` (source sha256 `9f961bc4e490c1d668014b02866b32020126ad7c8b0f94732a227554ab6d4404`)
- stage completed: `5`
- results in scope: 11

| bucket | count |
| --- | --- |
| verified | 8 |
| verified_with_bookkeeping | 0 |
| conditional | 3 |
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
| bucket | `conditional` |
| source | `main.tex:61-70` (`theorem`, label `thm:main`) |
| statement | \label{thm:main} There is an absolute constant $C<\infty$ such that \[ \Var(H_n)\le Cn\qquad(n\ge3). \] There are also absolute constants $c>0$ and $n_0$ such that $\Var(H_n)\ge cn$ for $n\ge n_0$. In particular, $\Var(H_n)=\Theta(n)$ as $n\to\infty$. |
| appended hypothesis list | ass:main-n |
| Lean | `TMain.lean:124` — `Papers.OaiLinearVarianceRandom.var_hittingTime_theta_n` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | `thm:wilson` (Wilson2002, Corollary 4) |
| assumed substrate gates | — |
| findings | — |

### 2. One-clause comparison `lem:one`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `main.tex:179-187` (`lemma`, label `lem:one`) |
| statement | \label{lem:one} For a nonempty assignment set $S$, let $h_a(S)$ be the probability that one random proper $a$-clause kills $S$, for $a=2,3$. Then \begin{equation} h_2(S)^\beta\le3h_3(S)+u^{-3}. \label{eq:one} \end{equation} |
| appended hypothesis list | ass:one-u, ass:one-nonempty |
| Lean | `Helpers/AssignmentSets.lean:347` — `Papers.OaiLinearVarianceRandom.oneKillProb_two_rpow_le` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 3. Potential drift `lem:potential`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `main.tex:216-231` (`lemma`, label `lem:potential`) |
| statement | \label{lem:potential} For every integer $d\ge1$, put \[ P_d(S)=\sum_{j=0}^{d-1}q_j(S). \] Then $0\le P_d(S)\le d$, and $P_d$ is nondecreasing when $S$ shrinks. If $C$ is an independent random proper 3-clause on the $u$ variables, then \begin{equation} \ind_{\{S\ne\varnothing\}}q_d(S)^\beta \le d^{\beta-1} \left(3\E_C[P_d(S[C])-P_d(S)]+du^{-3}\right). \label{eq:drift} \end{equation} |
| appended hypothesis list | ass:one-u, ass:potential-d |
| Lean | `Helpers/Potential.lean:244` — `Papers.OaiLinearVarianceRandom.potential_drift` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 4. Coordinate omission `lem:omission`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `main.tex:284-291` (`lemma`, label `lem:omission`) |
| statement | \label{lem:omission} The capped hitting time satisfies \begin{equation} \Var(T)\le\sum_{i=1}^L\E D_i^2. \label{eq:variance-deletion} \end{equation} |
| appended hypothesis list | ass:omission-n |
| Lean | `Helpers/Omission.lean:119` — `Papers.OaiLinearVarianceRandom.variance_cappedTime_le_sum_delay_sq` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 5. Root-test bound `lem:tests`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `main.tex:382-392` (`lemma`, label `lem:tests`) |
| statement | \label{lem:tests} For $i\le m<L$, conditional on $\cG_m$, \begin{align} \Prb(A_m\mid\cG_m)&\le\ind_{\{S_m\ne\varnothing\}}p_m^3 &&\text{on }\{V=0\},\label{eq:test3}\\ \Prb(A_m\mid\cG_m)&\le\ind_{\{S_m\ne\varnothing\}}p_m^2 &&\text{on }\{V=1\}. \label{eq:test2} \end{align} |
| appended hypothesis list | ass:omission-n, ass:tests-time, ass:delay-index |
| Lean | `Helpers/Pivotality.lean:36` — `Papers.OaiLinearVarianceRandom.condProb_pivotal_le` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 6. Conditional occupation estimate `lem:occupation`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `main.tex:428-437` (`lemma`, label `lem:occupation`) |
| statement | \label{lem:occupation} With $K=7$, for every $i\le m<L$, \begin{equation} \E\left[\sum_{s=m}^{L-1}\ind_{\{S_s\ne\varnothing\}}p_s^\beta \,\middle\|\,\cH_m\right] \le Kd^\beta. \label{eq:occupation} \end{equation} |
| appended hypothesis list | ass:omission-n, ass:occupation-time, ass:delay-index |
| Lean | `Helpers/Pivotality.lean:85` — `Papers.OaiLinearVarianceRandom.condExp_occupation_le` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 7. Remaining duration `thm:duration`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `main.tex:467-481` (`corollary`, label `cor:duration`) |
| statement | \label{cor:duration} For $i\le m<L$, \begin{equation} \E\left[\sum_{s=m}^{L-1}\ind_{A_s}\,\middle\|\,\cH_m\right]\le W_m, \qquad W_m=\begin{cases} \min\{L,Kd^\beta p_m^{-\beta}\},&p_m>0,\\ L,&p_m=0. \end{cases} \label{eq:duration} \end{equation} In particular, $W_m$ is measurable with respect to the smaller sigma-field $\cG_m$. |
| appended hypothesis list | ass:omission-n, ass:duration-time, ass:delay-index |
| Lean | `TDuration.lean:82` — `Papers.OaiLinearVarianceRandom.condExp_pivotal_duration_le` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 8. Squared delay conditional on the exposure `prop:delay`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `main.tex:496-506` (`proposition`, label `prop:delay`) |
| statement | \label{prop:delay} For every $1\le i\le L$, \begin{equation} \E[D_i^2\mid\cE] \le 2K^2d^3\ind_{\{V=0\}} +2KLd^{3/2}\ind_{\{V=1\}} +L^2\ind_{\{V\ge2\}}. \label{eq:delay-bound} \end{equation} |
| appended hypothesis list | ass:omission-n, ass:delay-index |
| Lean | `TDelay.lean:25` — `Papers.OaiLinearVarianceRandom.condExp_delay_sq_le` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 9. Root-incidence moments `lem:moments`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `main.tex:545-554` (`lemma`, label `lem:moments`) |
| statement | \label{lem:moments} Uniformly in $n\ge6$, $i$, and the fixed value of $C_i$, \begin{equation} \E d^3=O(1),\qquad \E[d^{3/2}\ind_{\{V\ge1\}}]=O(n^{-1}),\qquad \Prb(V\ge2)=O(n^{-2}). \label{eq:moments} \end{equation} |
| appended hypothesis list | ass:omission-n, ass:moments-range |
| Lean | `Helpers/Moments.lean:292` — `Papers.OaiLinearVarianceRandom.incidence_moments_bound` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 10. Wilson~\cite{Wilson2002}, Corollary~4 `thm:wilson`

| field | value |
| --- | --- |
| bucket | `conditional` |
| source | `main.tex:647-655` (`theorem`, label `thm:wilson`) |
| statement | \label{thm:wilson} Fix $1>p_1>p_2>0$. There is a constant $a(p_1,p_2)>0$ such that, for all sufficiently large $n$, if integers $m_1,m_2$ satisfy $s_n(m_1)\ge p_1$ and $s_n(m_2)\le p_2$, then \[ m_2-m_1\ge a(p_1,p_2)\sqrt n. \] |
| appended hypothesis list | ass:main-n, ass:wilson-levels, ass:wilson-endpoints |
| Lean | no declaration anchored |
| crosswalk verdict | — |
| axioms | — |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | `thm:wilson` (Wilson2002, Corollary 4) |
| assumed substrate gates | — |
| findings | [note, V1.5] cited source checked: arXiv:math/0005136 e-print (fetched by the runner; the arXiv version may differ from the published one) |

### 11. Fixed central windows `thm:window`

| field | value |
| --- | --- |
| bucket | `conditional` |
| source | `main.tex:682-688` (`corollary`, label `cor:window`) |
| statement | \label{cor:window} For every fixed $0<\eta<1/2$, \[ r_n(\eta)-r_n(1-\eta)=\Theta_\eta(\sqrt n). \] |
| appended hypothesis list | ass:main-n, ass:window-eta |
| Lean | `TWindow.lean:30` — `Papers.OaiLinearVarianceRandom.levelLocation_window_theta_sqrt` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | `thm:wilson` (Wilson2002, Corollary 4) |
| assumed substrate gates | — |
| findings | — |

## Suggestions to the authors

Not errors: readings the paper determines but does not state, and side conditions the proofs use silently.

- reading of the symbol `n`: $n\ge3$ is the integer number of variables in the proper 3-clause process. In Lemma~\ref{lem:omission}, Lemma~\ref{lem:tests}, Lemma~\ref{lem:occupation}, Corollary~\ref{cor:duration}, Proposition~\ref{prop:delay}, Lemma~\ref{lem:moments}: The variable count satisfies $n\ge6$. — The introduction fixes an integer $n\ge3$. The omitted-clause construction begins "Assume $n\ge6$", and Lemma~\ref{lem:moments} explicitly states uniformity in $n\ge6$.
- reading of the symbol `j`: $j$ is an integer index: clause indices in $C_j$ start at $1$, whereas the number of auxiliary proper 2-clauses in $q_j(S)$ starts at $0$; other summation ranges are those displayed locally. — The process is introduced as $C_1,C_2,\ldots$; $q_j(S)$ is explicitly defined for $j\ge0$, and $P_d(S)$ sums over $0\le j\le d-1$. The exposure considers clause indices $j\le L$ other than $i$.
- reading of the symbol `m`: $m$ is a nonnegative integer indexing prefixes of the clause process. In Lemma~\ref{lem:tests}, Lemma~\ref{lem:occupation}: The time index satisfies $i\le m<L$. In Proposition~\ref{prop:delay}: In the proof's sums over prefix times, $m$ ranges from $i$ to $L-1$. — The prefix definition includes $F_0$; the tail bound is stated for every integer $m\ge0$. Lemmas~\ref{lem:tests} and~\ref{lem:occupation} explicitly restrict their time index to $i\le m<L$.
- reading of the symbol `C`: $C$ has a local meaning: an absolute finite constant in the variance bounds or a clause in the survivor-set construction. In Theorem~\ref{thm:main}, Corollary~\ref{cor:window}: $C$ is an absolute finite constant satisfying $\Var(H_n)\le Cn$ for every integer $n\ge3$. In Lemma~\ref{lem:potential}: $C$ in the potential increment denotes an independent uniform proper 3-clause on the $u$ variables. — The survivor-set definition uses $C$ for a clause, and Lemma~\ref{lem:potential} specifies an independent random proper 3-clause. Lemma~\ref{lem:occupation} is no longer listed as using this symbol.
- reading of the symbol `n_0`: $n_0$ is an absolute deterministic threshold, independent of $n$, such that $\Var(H_n)\ge cn$ for every admissible integer $n\ge n_0$. — Theorem~\ref{thm:main} explicitly calls $c$ and $n_0$ absolute constants and states the lower bound for $n\ge n_0$.
- reading of the symbol `i`: $i$ is an integer index with $1\le i\le L$ specifying the omitted clause $C_i$; omission retains the original indices of all other clauses. — The deletion setup says: "For $1\le i\le L$, omit $C_i$ while retaining the original indices"; the exposure subsequently fixes $i$.
- reading of the symbol `s`: $s$ is an integer prefix index summed over $m\le s<L$, where $i\le m<L$. — The occupation proof displays the range $m\le s<L$; the duration argument uses the same future-prefix range, and the delay proof explicitly sums from $s=m$ to $L-1$.
- reading of the symbol `u`: $u\ge3$ is the integer number of coordinates of the assignment space on which the clause-survival and killing functionals are evaluated. In Lemma~\ref{lem:tests}, Lemma~\ref{lem:occupation}, Corollary~\ref{cor:duration}, Proposition~\ref{prop:delay}: $u=n-3$ is the number of nonroot variables, with $n\ge6$. — The potential section begins with $u\ge3$ variables; the exposure construction states that there are $u=n-3\ge3$ nonroot variables.
- reading of the symbol `S`: $S$ denotes a subset of $\{0,1\}^u$ to which the clause-survival and killing functionals are applied. In Lemma~\ref{lem:one}: $S$ is nonempty. In Lemma~\ref{lem:tests}, Lemma~\ref{lem:occupation}, Corollary~\ref{cor:duration}, Proposition~\ref{prop:delay}: The assignment sets used here are $S_m$, for $i\le m\le L$: the nonroot assignments that, together with the root assignment $w$ falsifying $C_i$, satisfy $B_m^{(i)}$; these sets are $\cG_m$-measurable and decrease with $m$. — The potential section defines the functionals for $S\subseteq\{0,1\}^u$; Lemma~\ref{lem:one} assumes nonemptiness; the exposure construction defines the sets $S_m$ and their measurability.
- reading of the symbol `a`: $a$ is a positive deterministic parameter whose meaning is local to its occurrence. In Lemma~\ref{lem:one}, Lemma~\ref{lem:potential}, Lemma~\ref{lem:tests}, Lemma~\ref{lem:occupation}, Corollary~\ref{cor:duration}, Proposition~\ref{prop:delay}: In the short-clause notation, $a\in\{2,3\}$ is the number of distinct variables in a proper clause. In Theorem~\ref{thm:wilson}: $a(p_1,p_2)>0$ is a constant depending on the fixed levels $1>p_1>p_2>0$ and independent of $n,m_1,m_2$. — Lemma~\ref{lem:one} specifies $a=2,3$ for short clauses; Theorem~\ref{thm:wilson} separately introduces a positive constant $a(p_1,p_2)$ for fixed probability levels.
- reading of the symbol `q_j`: For every integer $j\ge0$ and $S\subseteq\{0,1\}^u$, $q_j(S)$ is the probability that $j$ independent random proper 2-clauses kill $S$, with $q_j(\varnothing)=1$ and $q_0(S)=0$ for $S\ne\varnothing$. — The definition in Section~\ref{sec:potential} specifies $j\ge0$ and explicitly gives both empty-set and zero-clause conventions.
- reading of the symbol `d`: $d$ is a positive integer used as the clause count in $q_d(S)$ and the length of the sum $P_d(S)=\sum_{j=0}^{d-1}q_j(S)$. In Lemma~\ref{lem:potential}: $d\ge1$ is an arbitrary fixed integer. In Lemma~\ref{lem:tests}, Lemma~\ref{lem:occupation}, Corollary~\ref{cor:duration}, Proposition~\ref{prop:delay}, Lemma~\ref{lem:moments}: $d=\max\{1,Z\}$, where $Z$ counts indices $j\le L$, excluding $i$, whose clauses meet at least one root; in particular, $d$ is $\cE$-measurable. — Lemma~\ref{lem:potential} allows every integer $d\ge1$; the exposure construction sets $d=\max\{1,Z\}$ and states its $\cE$-measurability.
- reading of the symbol `p`: In the introductory killing-probability shorthand $p=q_d(S)$, whereas in $r_n(p)$ the symbol $p$ denotes a deterministic probability level satisfying $0<p<1$. — The introduction writes $p=q_d(S)$; the later display defining $r_n(p)$ explicitly uses $p$ as its argument and restricts it to $(0,1)$.
- reading of the symbol `T`: $T=\min(H_n,L)$ is defined for $n\ge6$, with $L=10n$, and is a function of the first $L$ clauses. — The omission setup begins with $n\ge6$ and $L=10n$, defines $T$, and states that both capped variables are functions of the first $L$ clauses.
- reading of the symbol `T^{(i)}`: For $n\ge6$ and $1\le i\le L=10n$, $T^{(i)}$ is the first unsatisfiable original index of $B_m^{(i)}$, capped at $L$; it is a function of $(C_j)_{1\le j\le L,\,j\ne i}$ and does not depend on $C_i$. — The omission setup specifies the index range, retention of original indices, the cap, and the absence of dependence on $C_i$.
- reading of the symbol `D_i`: For $n\ge6$, $L=10n$ and $1\le i\le L$, $D_i=T^{(i)}-T\ge0$ is the delay obtained by omitting $C_i$ while retaining all original clause indices; it is a function of the first $L$ clauses. In Lemma~\ref{lem:tests}, Lemma~\ref{lem:occupation}, Corollary~\ref{cor:duration}, Proposition~\ref{prop:delay}: $D_i=\sum_{m=i}^{L-1}\ind_{A_m}$, where $A_m=\{T\le m<T^{(i)}\}$. — The definitions preceding Lemma~\ref{lem:omission} specify the cap, index range and omission convention; equation~\eqref{eq:delay} gives its occupation representation.
- reading of the symbol `A_m`: $A_m$ is defined for integer indices $i\le m<L$ and is $\cH_m$-measurable. — The definition preceding equation~\eqref{eq:A} specifies $i\le m<L$; the paragraph defining the filtrations explicitly states that $A_m$ is $\cH_m$-measurable.
- reading of the symbol `S_m`: For $i\le m\le L$, $S_m\subseteq\{0,1\}^u$, with $u=n-3$, is the $\cG_m$-measurable set of nonroot assignments that together with $w$ satisfy $B_m$, and these sets decrease with $m$. — The defining paragraph following equation~\eqref{eq:delay} specifies the index range and decreasing sets; the root definitions give $u=n-3$, and the paragraph defining the filtrations explicitly states $\cG_m$-measurability.
- reading of the symbol `Z`: $Z$ is the $\cE$-measurable count $\bigl\|\{j:1\le j\le L,\ j\ne i,\ C_j\text{ meets }R\}\bigr\|$, counting indices throughout the capped exposure, including future indices. — The exposure paragraph specifies every index $j\le L$ other than $i$, includes future information in $\cE$, defines $Z$ by root incidence, and explicitly states its $\cE$-measurability.
- reading of the symbol `V`: $V=\sum_{1\le j\le L,\,j\ne i}\ind_{\{\|\operatorname{vars}(C_j)\cap R\|\ge2\}}$ counts collision indices throughout the entire capped exposure and is $\cE$-measurable. — The exposure paragraph ranges over all indices through $L$ other than $i$, defines collisions by meeting at least two roots, and explicitly states that $V$ is $\cE$-measurable.
- reading of the symbol `\cG_m`: $\cG_m=\cE\vee\sigma(\text{ordinary contents through index }m)$ is defined for integer indices $i\le m\le L$; the hidden nonroot parts of test clauses are not revealed in this filtration. — The defining display specifies $i\le m\le L$, and the following paragraph explicitly says that the tests are kept out of $\cG_m$.
- reading of the symbol `\cH_m`: $\cH_m=\cG_m\vee\sigma(\text{test parts through index }m)$ is defined for integer indices $i\le m\le L$ and includes the complete future clause-type information already contained in $\cE$. — The defining display is preceded by $i\le m\le L$, and the exposure definition includes information at future indices.
- reading of the symbol `p_m`: For $i\le m\le L$, $p_m=q_d(S_m)$ is $\cG_m$-measurable and nondecreasing in $m$. — The filtration definitions preceding equation~\eqref{eq:p} specify $i\le m\le L$, and the sentence following that equation explicitly states measurability and monotonicity.
- reading of the symbol `W_m`: For $i\le m<L$, $W_m$ is the $\cG_m$-measurable quantity $\min\{L,Kd^\beta p_m^{-\beta}\}$ when $p_m>0$, and $L$ when $p_m=0$. — Corollary~\ref{cor:duration} defines the piecewise quantity for $i\le m<L$ and explicitly states its $\cG_m$-measurability.
- reading of the symbol `r_n`: For each $n\ge3$ and $0<p<1$, $r_n(p)=\min\{m\ge0:s_n(m)\le p\}$ is a finite positive integer determined by the unconditional distribution of $H_n$. — The definition of the level locations explicitly restricts $0<p<1$ and states that the locations are finite by \eqref{eq:tail} and positive because $s_n(0)=1$.
- reading of the symbol `p_1`: $p_1$ is a fixed deterministic probability level, independent of $n$, with $0<p_2<p_1<1$. — Theorem~\ref{thm:wilson} fixes $1>p_1>p_2>0$. The current result-use list contains no application specifying $p_1=1-\eta$.
- reading of the symbol `p_2`: $p_2$ is a fixed deterministic probability level, independent of $n$, with $0<p_2<p_1<1$. — Theorem~\ref{thm:wilson} fixes $1>p_1>p_2>0$. The current result-use list contains no application specifying $p_2=\eta$.
- reading of the symbol `m_1`: $m_1$ is a deterministic nonnegative integer endpoint satisfying $s_n(m_1)\ge p_1$; it may depend on $n$ and need not be the integer level location $r_n(p_1)$. — Theorem~\ref{thm:wilson} permits integer endpoints satisfying $s_n(m_1)\ge p_1$. No current result using the symbol specifies the former level-location choice.
- reading of the symbol `m_2`: $m_2$ is a deterministic nonnegative integer endpoint satisfying $s_n(m_2)\le p_2$; it may depend on $n$ and need not be the integer level location $r_n(p_2)$. — Theorem~\ref{thm:wilson} permits integer endpoints satisfying $s_n(m_2)\le p_2$. No current result using the symbol specifies the former level-location choice.
- reading of the symbol `a(p_1,p_2)`: $a(p_1,p_2)>0$ is a deterministic constant depending only on the fixed levels $p_1,p_2$, independent of $n$ and of the admissible endpoints $m_1,m_2$. — Theorem~\ref{thm:wilson} fixes the levels before asserting the existence of the constant, uniformly for all sufficiently large $n$ and all endpoints satisfying its inequalities.
- reading of the symbol `\eta`: $\eta\in(0,1/2)$ is a fixed deterministic probability level, independent of $n$; constants in $\Theta_\eta(\sqrt n)$ may depend on $\eta$. — Corollary~\ref{cor:window} states the conclusion for every fixed $0<\eta<1/2$ and writes the dependence explicitly as $\Theta_\eta$.
- reading of the symbol `t`: $t$ is a deterministic real parameter with a meaning local to its occurrence. In Lemma~\ref{lem:one}: $t$ is the argument of $(t)_a=t(t-1)\cdots(t-a+1)$; the evaluations used are $t=b$ and $t=u$. In Corollary~\ref{cor:window}: $t=(2Cn/\eta)^{1/2}$, with $C$ the upper-bound constant from Theorem~\ref{thm:main}; this deviation radius varies with $n$. — The proof of Lemma~\ref{lem:one} introduces the falling-factorial argument; the proof of Corollary~\ref{cor:window} explicitly chooses a deviation radius.
- reading of the symbol `Y`: $Y\subseteq S$ is the survivor set obtained by imposing the auxiliary proper 2-clauses. In Lemma~\ref{lem:potential}: In the proof, $j$ is a fixed nonnegative integer and $Y$ consists of exactly those $z\in S$ satisfying all $j$ auxiliary clauses; thus $Y=S$ when $j=0$, and $Y$ may be empty. — The proof of Lemma~\ref{lem:potential} fixes $j\ge0$ and defines $Y$ as the subset surviving $j$ independent random proper 2-clauses.
- reading of the symbol `\mathcal F_i`: For $0\le i\le L$, $\mathcal F_i=\sigma(C_1,\ldots,C_i)$, with $\mathcal F_0$ the trivial sigma-field. — The proof of Lemma~\ref{lem:omission} defines the filtration and uses $\mathcal F_{i-1}$ when summing the differences over $1\le i\le L$.
- reading of the symbol `J_j`: For $1\le j\le L$ with $j\ne i$, $J_j$ is the event that $C_j$ meets at least two variables of $R$. — The proof of Lemma~\ref{lem:moments} introduces $J_j$ explicitly for each $j\ne i$ with $j\le L$; the exposure defines collisions as clauses meeting at least two roots.
- reading of the symbol `p_{\rm coll}`: $p_{\rm coll}$ is the common probability $\Prb(J_j)$ for any $1\le j\le L$ with $j\ne i$; it depends only on $n$. — The proof of Lemma~\ref{lem:moments} defines the collision probability for each other clause and uses the same probability at all $L-1$ indices.
- reading of the symbol `c_0`: $c_0>0$ is an absolute constant, independent of $n$, such that $b_n-a_n\ge c_0\sqrt n$ for all sufficiently large $n$. — The sentence following \eqref{eq:separation} specifies an absolute positive constant and the sufficiently large $n$ qualification.
- reading of the symbol `H_n'`: $H_n'$ has the same distribution as $H_n$ and is independent of $H_n$. — The defining sentence is: "Let $H_n'$ be an independent copy of $H_n$."

## Added conditions

None: no condition was added to the paper's own hypotheses.

## Conditions assumed

### Cited results

| id | used by | citation | locator | checked against |
| --- | --- | --- | --- | --- |
| `thm:wilson` | `thm:main` | Wilson2002 | Corollary 4 | arXiv:math/0005136 e-print (fetched by the runner; the arXiv version may differ from the published one) |
| `thm:wilson` | `thm:wilson` | Wilson2002 | Corollary 4 | arXiv:math/0005136 e-print (fetched by the runner; the arXiv version may differ from the published one) |
| `thm:wilson` | `thm:window` | Wilson2002 | Corollary 4 | arXiv:math/0005136 e-print (fetched by the runner; the arXiv version may differ from the published one) |

`thm:wilson` (Wilson2002, Corollary 4):

What Lean assumes for it: `Papers.OaiLinearVarianceRandom.WilsonSeparation` (`Basic.lean:556`)

```lean
def WilsonSeparation : Sort 0 :=
  ∀ p1 p2 : ℝ, WilsonLevels p1 p2 →
    ∃ a : ℝ, 0 < a ∧ -- @realizes a(p_1,p_2)(positive constant depending only on fixed levels)
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → MainN n →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (Cseq : ℕ → Ω → ProperClause n), IsUniformClauseProcess μ Cseq →
        ∀ m1 m2 : ℤ,
          WilsonEndpoints (survivalFnInt μ (fun ω => hittingTime (fun j => Cseq j ω)))
            p1 p2 m1 m2 → a * Real.sqrt n ≤ (m2 : ℝ) - (m1 : ℝ)
```

### Deferred substrate gates

None: every substrate this run needed was built and proved.

## Unresolved / notes

- run-level `symbol x_j`: [note, V1.5] symbol table corrected: space "$\{x_1,\ldots,x_n\}$", def "$x_j$ is the $j$th Boolean variable symbol among $x_1,\ldots,x_n$, for $1\le j\le n$." (The paper uses $x_j$ as a variable symbol, including as an element of the root set. The recorded space $\{0,1\}$ describes an assigned truth value rather than the variable itself.)
- run-level `symbol C`: [note, V1.5] symbol table corrected: type "locally reused absolute constant or clause", space "$\mathbb R\,\cup\,\{\text{clauses on the }u\text{ variables}\}$", def "$C$ denotes the absolute finite constant in $\Var(H_n)\le Cn$ in the variance and window bounds, and denotes a clause in $S[C]=\{z\in S:z\models C\}$ and the potential argument." (The constant-only entry omits the local clause meaning. The existing repair remains applicable; its clause scope is restricted to Lemma~\ref{lem:potential}.)
- run-level `symbol a`: [note, V1.5] symbol table corrected: type "locally defined positive deterministic parameter", space "$\mathbb R_{>0}$", def "$a$ denotes the clause arity $a=2,3$ in the short-clause notation; $a(p_1,p_2)>0$ denotes the separation constant in Wilson's theorem." (The clause-arity entry is correct for the potential arguments but does not cover the positive separation constant introduced later.)
- run-level `symbol d`: [note, V1.5] symbol table corrected: def "The positive integer parameter in $P_d(S)=\sum_{j=0}^{d-1}q_j(S)$; in the root exposure, $d=\max\{1,Z\}$, where $Z$ counts indices $j\le L$, $j\ne i$, whose clauses meet at least one root." (The recorded description omits the defining incidence-count formula, which determines the quantities in the delay and moment bounds. The arbitrary potential parameter is specialized to this exposure-measurable count.)
- run-level `symbol p`: [note, V1.5] symbol table corrected: type "killing-probability shorthand or probability-level argument", def "The introductory shorthand is $p=q_d(S)$; in $r_n(p)=\min\{m\ge0:s_n(m)\le p\}$, $p$ is a probability level with $0<p<1$." (The recorded entry covers only the introductory shorthand and misses the later probability-level argument. The indexed process $p_m=q_d(S_m)$ is consistent with the introductory use.)
- run-level `symbol \cE`: [note, V1.5] symbol table corrected: def "For every $1\le j\le L$ with $j\ne i$, reveal the subset of $R$ met by $C_j$ and all signs on that subset. If the clause meets no root, leave all its contents hidden. If it meets exactly one root whose literal is true under $w$, leave its two nonroot literals hidden. For every other clause, reveal all its remaining contents. The sigma-field $\cE$ is generated by this exposure, including the information at future indices." (The recorded phrase 'root exposure' omits which nonroot contents are revealed. The paper reveals all remaining contents except those of ordinary clauses and the nonroot parts of test clauses; this distinction determines the conditioning sigma-field.)
- run-level `symbol t`: [note, V1.5] symbol table corrected: type "locally defined deterministic real parameter", def "$t$ denotes the argument in $(t)_a$ where falling factorials are used, and the deviation radius $(2Cn/\eta)^{1/2}$ in the central-window proof." (The entry covers only the falling-factorial argument and misses the later deterministic deviation radius.)
- note on `symbol \cE`: symbol table corrected: def "For every $1\le j\le L$ with $j\ne i$, reveal the subset of $R$ met by $C_j$ and all signs on that subset. If the clause meets no root, leave all its contents hidden. If it meets exactly one root whose literal is true under $w$, leave its two nonroot literals hidden. For every other clause, reveal all its remaining contents. The sigma-field $\cE$ is generated by this exposure, including the information at future indices." (The recorded phrase 'root exposure' omits which nonroot contents are revealed. The paper reveals all remaining contents except those of ordinary clauses and the nonroot parts of test clauses; this distinction determines the conditioning sigma-field.)
- note on `symbol a`: symbol table corrected: type "locally defined positive deterministic parameter", space "$\mathbb R_{>0}$", def "$a$ denotes the clause arity $a=2,3$ in the short-clause notation; $a(p_1,p_2)>0$ denotes the separation constant in Wilson's theorem." (The clause-arity entry is correct for the potential arguments but does not cover the positive separation constant introduced later.)
- note on `symbol C`: symbol table corrected: type "locally reused absolute constant or clause", space "$\mathbb R\,\cup\,\{\text{clauses on the }u\text{ variables}\}$", def "$C$ denotes the absolute finite constant in $\Var(H_n)\le Cn$ in the variance and window bounds, and denotes a clause in $S[C]=\{z\in S:z\models C\}$ and the potential argument." (The constant-only entry omits the local clause meaning. The existing repair remains applicable; its clause scope is restricted to Lemma~\ref{lem:potential}.)
- note on `symbol d`: symbol table corrected: def "The positive integer parameter in $P_d(S)=\sum_{j=0}^{d-1}q_j(S)$; in the root exposure, $d=\max\{1,Z\}$, where $Z$ counts indices $j\le L$, $j\ne i$, whose clauses meet at least one root." (The recorded description omits the defining incidence-count formula, which determines the quantities in the delay and moment bounds. The arbitrary potential parameter is specialized to this exposure-measurable count.)
- note on `symbol p`: symbol table corrected: type "killing-probability shorthand or probability-level argument", def "The introductory shorthand is $p=q_d(S)$; in $r_n(p)=\min\{m\ge0:s_n(m)\le p\}$, $p$ is a probability level with $0<p<1$." (The recorded entry covers only the introductory shorthand and misses the later probability-level argument. The indexed process $p_m=q_d(S_m)$ is consistent with the introductory use.)
- note on `symbol t`: symbol table corrected: type "locally defined deterministic real parameter", def "$t$ denotes the argument in $(t)_a$ where falling factorials are used, and the deviation radius $(2Cn/\eta)^{1/2}$ in the central-window proof." (The entry covers only the falling-factorial argument and misses the later deterministic deviation radius.)
- note on `symbol x_j`: symbol table corrected: space "$\{x_1,\ldots,x_n\}$", def "$x_j$ is the $j$th Boolean variable symbol among $x_1,\ldots,x_n$, for $1\le j\le n$." (The paper uses $x_j$ as a variable symbol, including as an element of the root set. The recorded space $\{0,1\}$ describes an assigned truth value rather than the variable itself.)
- note on `thm:wilson`: cited source checked: arXiv:math/0005136 e-print (fetched by the runner; the arXiv version may differ from the published one)

### V1 lint warnings

- lem:potential: lem:potential references \ref{lem:one} (lem:one) but `depends_on` lacks ass:one-nonempty; V1.5 must confirm whether the paper assumes it or merely mentions it
- lem:occupation: lem:occupation references \ref{lem:potential} (lem:potential) but `depends_on` lacks ass:potential-d, ass:potential-clause; V1.5 must confirm whether the paper assumes it or merely mentions it
- prop:delay: prop:delay references \ref{cor:duration} (cor:duration) but `depends_on` lacks ass:duration-time; V1.5 must confirm whether the paper assumes it or merely mentions it
- prop:delay: prop:delay references \ref{lem:tests} (lem:tests) but `depends_on` lacks ass:tests-time; V1.5 must confirm whether the paper assumes it or merely mentions it
- prop:delay: prop:delay references \ref{lem:occupation} (lem:occupation) but `depends_on` lacks ass:occupation-time; V1.5 must confirm whether the paper assumes it or merely mentions it
- thm:window: cor:window references \ref{thm:wilson} (thm:wilson) but `depends_on` lacks ass:wilson-levels, ass:wilson-endpoints; V1.5 must confirm whether the paper assumes it or merely mentions it

### Parser warnings

- main.tex:10: \input{glyphtounicode} not found (tried glyphtounicode.tex, glyphtounicode relative to . and the source root); skipped (the bundle does not ship it — check that no result lived there)
- main.tex:11: \input{glyphtounicode-cmex} not found (tried glyphtounicode-cmex.tex, glyphtounicode-cmex relative to . and the source root); skipped (the bundle does not ship it — check that no result lived there)

## Lean evidence

- build of the run barrel: **ok**
- source scan (sorry / admit / axiom): clean

| declaration | axioms |
| --- | --- |
| `Papers.OaiLinearVarianceRandom.var_hittingTime_theta_n` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiLinearVarianceRandom.oneKillProb_two_rpow_le` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiLinearVarianceRandom.potential_drift` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiLinearVarianceRandom.variance_cappedTime_le_sum_delay_sq` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiLinearVarianceRandom.condProb_pivotal_le` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiLinearVarianceRandom.condExp_occupation_le` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiLinearVarianceRandom.condExp_pivotal_duration_le` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiLinearVarianceRandom.condExp_delay_sq_le` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiLinearVarianceRandom.incidence_moments_bound` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiLinearVarianceRandom.levelLocation_window_theta_sqrt` | clean — `propext`, `Classical.choice`, `Quot.sound` |

## Inputs

| artifact | status |
| --- | --- |
| `discovery/v1_scope.json` | present (11 environment(s)) |
| `discovery/v1_5_review.json` | present (verdict PASS) |
| `formalization/crosswalk_full.json` | present (302 object(s)) |
| `graph.json` | present (306 node(s)) |
| Lean evidence | collected (build ok, 0 scan issue(s), 302 declaration(s)) |

## Annotated paper

Annotated paper: `annotated/main.tex` (38 annotation(s), 0 unlocated; index `annotated/ANNOTATIONS.md`); PDF: `annotated/main.pdf`
