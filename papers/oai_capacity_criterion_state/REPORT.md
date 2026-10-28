# Correctness report — oai_capacity_criterion_state

**Verdict: NO ERROR FOUND**

**Paper: MINOR ISSUES — no main result is shown false or weakened**

Minor:

- Theorem 1.1: condition added (bookkeeping or a pinned reading)
- Proposition 2.1: condition added (bookkeeping or a pinned reading)
- Lemma 4.1: condition added (bookkeeping or a pinned reading)
- `def:posterior-coordinates`: ambiguous; a reading was pinned
- `def:product-rule`: ambiguous; a reading was pinned
- `L_n`: notation ambiguous; a reading was pinned
- `\mu`: notation ambiguous; a reading was pinned
- `\nu`: notation ambiguous; a reading was pinned
- `t`: notation ambiguous; a reading was pinned
- `\star`: notation ambiguous; a reading was pinned
- `q`: notation ambiguous; a reading was pinned
- `Z`: notation ambiguous; a reading was pinned
- `P`: notation ambiguous; a reading was pinned
- `s`: notation ambiguous; a reading was pinned

4 result(s) of the paper were examined. None was found wrong as printed. In Lean: 3 proved, 1 taken from the literature as cited, 0 not certified, 0 not formalized.

## What was wrong and what was done

No error was found in the results examined.

## Clarifications (not errors)

Nothing in this section is an error of the paper. Each item is something the paper determines but does not say, made explicit so that the statements can be read, and formalized, in one way.

**How a statement is read.**

- **Theorem 1.1.** For $x\in\mathbb R^3$, $|x|^2=x_1^2+x_2^2+x_3^2$.
- **Theorem 1.1.** The combined posterior law is the law of $P$ under $Z\,d(\mu\otimes\nu)$, with $P_i=4p_iq_i/Z$ on $\{Z>0\}$ and any measurable simplex-valued extension on $\{Z=0\}$.

**Notation.**

- $L_n$: $L_n=\{v\in V(T):|v|=n\}$ for $n\in\mathbb N_0$.
- $\mu$: $\mu$ denotes the distribution of the posterior vector $p$ for an experiment about a uniform input spin in $[4]$, taken under the marginal law of the observation. In Theorem~\ref{thm:main}: The posterior laws of finite-depth subtree experiments, including descendant-level observations, independently channel-degraded terminal observations, and partial products at a vertex, belong to $\calC$. In Proposition~\ref{prop:companion}: $\mu\in\calC$, where $\calC$ is the class of symmetric posterior laws specified in the statement. In Lemma~\ref{lem:local-moments}: $\mu$ is symmetric, meaning invariant under all permutations of its four posterior entries; membership in $\calC$ is not required.
- $\nu$: $\nu$ is the second marginal posterior law for an experiment about a uniform input spin in $[4]$. In Proposition~\ref{prop:companion}: $\nu\in\calC$, where $\calC$ is the class of symmetric posterior laws specified in the statement. In Lemma~\ref{lem:local-moments}: $\nu$ is a symmetric posterior law obtained by a channel step of parameter $\lambda$, with $0<\lambda<1$.
- $t$: In a channel step, $t\in[0,1]$ denotes the parameter of the channel $P_t$. In Theorem~\ref{thm:main}: In the tangent inequality $(1+2t)^{-1/2}\geq1-t$ for $t\geq0$, the letter $t$ is a local dummy variable ranging over $[0,\infty)$, independent of its use as a channel parameter.
- $\star$: $\mu\star\nu$ is the law of $P$ under $Z\,d(\mu\otimes\nu)$, where $Z=4\sum_i p_iq_i$ and $P_i=4p_iq_i/Z$ on $\{Z>0\}$, with arbitrary simplex-valued extension on $\{Z=0\}$.
- $q$: $q$ is the second marginal posterior vector, with law $\nu$, for an experiment about a uniform input spin in $[4]$. In Lemma~\ref{lem:local-moments}: $q_i\geq(1-\lambda)/4$ for every $i\in\{1,2,3,4\}$, since its law is obtained by a channel step of parameter $\lambda$.
- $Z$: $Z=4\sum_{i=1}^4p_iq_i$ is the density of the joint marginal observation law relative to the product of its marginal laws, with $\int Z\,d(\mu\otimes\nu)=1$. In Lemma~\ref{lem:local-moments}: $Z=1+s\geq1-\lambda>0$.
- $P$: $P_i=4p_iq_i/Z$ on $\{Z>0\}$; its combined posterior law is the image under $P$ of the measure $Z\,d(\mu\otimes\nu)$, and its value on $\{Z=0\}$ may be any probability vector. In Lemma~\ref{lem:local-moments}: $Z=1+s\geq1-\lambda>0$, so the displayed coordinate formula defines $P$ throughout the product sampling law.
- $s$: $s=x\cdot y$ satisfies $-\lambda\leq s\leq3$ and $1+s\geq1-\lambda>0$.

## What was proved in Lean, and what was not

A result is proved in Lean when a Lean declaration reviewed as stating it has a complete proof using no axiom beyond the standard ones. For a corrected result, the corrected statement is the one formalized.

| Result | Formal status | Lean declaration | Axioms |
| --- | --- | --- | --- |
| Theorem 1.1 | proved in Lean, given 1 cited result(s), under 2 condition(s) made explicit | `OaiCapacityCriterionState.reconstructs_iff_capacity_pos` (`TMain.lean:26`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Proposition 2.1 | taken from the literature as cited; not proved here | — | — |
| Lemma 3.1 | proved in Lean | `OaiCapacityCriterionState.exists_flow_of_labels` (`Helpers/Flow.lean:199`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 4.1 | proved in Lean, under 2 condition(s) made explicit | `OaiCapacityCriterionState.local_moment_bounds` (`Helpers/LocalMoments.lean:607`) | the standard ones only (propext, Classical.choice, Quot.sound) |

**Taken from the literature, not proved here.**

- OpenAI26Potts, Proposition 3.2 and Equations (3.8)--(3.9) — checked against source supplied by the user at discovery/cited_sources/OpenAI26Potts.txt

  What Lean assumes for it: `OaiCapacityCriterionState.CompanionMomentSaving` (`Helpers/CitedGates.lean:32`)

  ```lean
  def CompanionMomentSaving : Sort 0 :=
    ∃ C : Set (Measure (Fin 4 → ℝ)), -- @realizes \calC(class of symmetric posterior laws)
      (∀ mu ∈ C, IsPosteriorLaw mu ∧ IsSymmetricLaw mu) ∧
      revealingLaw ∈ C ∧ uninformativeLaw ∈ C ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ mu ∈ C, channelStep t mu ∈ C) ∧
      (∀ mu ∈ C, ∀ nu ∈ C, starLaw mu nu ∈ C) ∧
      ∀ mu ∈ C, ∀ nu ∈ C,
        quadInfo (starLaw mu nu) ≤ quadInfo mu + quadInfo nu -
          (1 / 1000 : ℝ) * -- @realizes c(the fixed positive constant 1/1000)
            ((∫ p, quadStat p ^ 2 ∂mu) * quadInfo nu +
              quadInfo mu * ∫ p, quadStat p ^ 2 ∂nu)
  ```

The Lean development builds; it contains no `sorry`, `admit` or added axiom.

## The corrected paper

`bundle/corrected_paper/` holds the paper as it reads after the corrections, as plain source in the author's own class and layout, compiled to `bundle/corrected_paper/main.pdf` (12 pages). `bundle/MATCH.md` sets each result beside its Lean declaration; `bundle/lean/` holds the Lean code.

The mechanical checks leave nothing open.

# Technical appendix

The records behind the report above, by the run's own identifiers.

- paper: `main.tex` (source sha256 `35f70e08ed507fead58dc16d02fe36ebc9fa5b0d79a345cd04c1b7291a7532e0`)
- stage completed: `5`
- results in scope: 4

| bucket | count |
| --- | --- |
| verified | 1 |
| verified_with_bookkeeping | 1 |
| conditional | 2 |
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
| source | `main.tex:95-104` (`theorem`, label `thm:main`) |
| statement | \label{thm:main} Let $T$ be an infinite rooted tree with at most $B<\infty$ children per vertex, and let $0<\lambda<1$. For the broadcast model \eqref{eq:channel}, \[ a_\infty(T,\lambda)>0 \quad\Longleftrightarrow\quad \Capacity_{3,\lambda}(T)>0. \] |
| appended hypothesis list | ass:main-tree, ass:main-lambda |
| Lean | `TMain.lean:26` — `OaiCapacityCriterionState.reconstructs_iff_capacity_pos` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | `ass:pin-1`, `ass:pin-2` |
| cited results | `prop:companion` (OpenAI26Potts, Proposition 3.2 and Equations (3.8)--(3.9)) |
| assumed substrate gates | — |
| findings | — |

### 2. Companion input, {\cite[Proposition~3.2 and Equations~(3.8)--(3.9)]{OpenAI26Potts}} `prop:companion`

| field | value |
| --- | --- |
| bucket | `conditional` |
| source | `main.tex:290-301` (`proposition`, label `prop:companion`) |
| statement | \label{prop:companion} There is a class $\calC$ of symmetric posterior laws containing the revealing and uninformative laws and preserved by channel steps with any parameter in $[0,1]$ and by conditionally independent products. For $\mu,\nu\in\calC$, \begin{equation}\label{eq:moment-saving} m(\mu\star\nu)\leq m(\mu)+m(\nu) -c\left(\E_\mu[A^2]m(\nu)+m(\mu)\E_\nu[A^2]\right), \qquad c=\frac1{1000}. \end{equation} |
| Lean | no declaration anchored |
| crosswalk verdict | — |
| axioms | — |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | `ass:pin-1`, `ass:pin-2` |
| cited results | `prop:companion` (OpenAI26Potts, Proposition 3.2 and Equations (3.8)--(3.9)) |
| assumed substrate gates | — |
| findings | [note, V1.5] cited source checked: source supplied by the user at discovery/cited_sources/OpenAI26Potts.txt |

### 3. A flow from recursive labels `lem:flow`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `main.tex:323-332` (`lemma`, label `lem:flow`) |
| statement | \label{lem:flow} Suppose nonnegative finite labels $(z_v)_{v\in T}$ satisfy \begin{equation}\label{eq:label-recursion} z_v\leq\sum_{w\in\children(v)} \frac{r z_w}{\sqrt{1+z_w^2}}. \end{equation} Then there is a flow of mass $z_\rho$ whose potential \eqref{eq:potential} is at most one on every ray. In particular, $\Capacity_{3,\lambda}(T)\geq z_\rho$. |
| appended hypothesis list | ass:flow-label-recursion, ass:main-tree, ass:main-lambda |
| Lean | `Helpers/Flow.lean:199` — `OaiCapacityCriterionState.exists_flow_of_labels` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 4. `lem:local-moments`

| field | value |
| --- | --- |
| bucket | `verified_with_bookkeeping` |
| source | `main.tex:435-449` (`lemma`, label `lem:local-moments`) |
| statement | \label{lem:local-moments} Fix $0<\lambda<1$. Let $\mu,\nu$ be symmetric posterior laws, with $\nu$ obtained by a channel step of parameter $\lambda$. There is a finite constant $C=C(\lambda)$ such that \begin{align} m(\mu\star\nu) &\geq m(\mu)+m(\nu) -C\bigl(h(\mu)m(\nu)+m(\mu)h(\nu)\bigr), \label{eq:local-m-lower}\\ h(\mu\star\nu) &\leq h(\mu)+h(\nu)+C m(\mu)m(\nu). \label{eq:local-h-upper} \end{align} The first inequality holds with $C=7$. |
| appended hypothesis list | ass:local-moments-lambda, ass:local-moments-symmetry, ass:local-moments-channel |
| Lean | `Helpers/LocalMoments.lean:607` — `OaiCapacityCriterionState.local_moment_bounds` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | `ass:pin-1`, `ass:pin-2` |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

## Corrected version

3 of 4 result(s) differ from the version you provided — 0 repaired, 0 with the proof completed (no error), 3 only with a side condition or reading made explicit; the others are as printed. The Lean formalization is of the corrected version.

### `thm:main` (`main.tex:95-104`)

- as printed: \label{thm:main} Let $T$ be an infinite rooted tree with at most $B<\infty$ children per vertex, and let $0<\lambda<1$. For the broadcast model \eqref{eq:channel}, \[ a_\infty(T,\lambda)>0 \quad\Longleftrightarrow\quad \Capacity_{3,\lambda}(T)>0. \]
- corrected: statement unchanged
- no error: only a side condition or reading the referee made explicit (see below)
- side condition added by the confirming referee `ass:pin-1`: For $x\in\mathbb R^3$, $|x|^2=x_1^2+x_2^2+x_3^2$. — pins reading of def:posterior-coordinates: The sentence immediately following the statistics display states that vector norms are Euclidean.
- side condition added by the confirming referee `ass:pin-2`: The combined posterior law is the law of $P$ under $Z\,d(\mu\otimes\nu)$, with $P_i=4p_iq_i/Z$ on $\{Z>0\}$ and any measurable simplex-valued extension on $\{Z=0\}$. — pins reading of def:product-rule: Immediately after the product-rule display, the paper states that the value of $P$ at $Z=0$ is irrelevant and derives the weighting from the conditional observation likelihoods.

### `prop:companion` (`main.tex:290-301`)

- as printed: \label{prop:companion} There is a class $\calC$ of symmetric posterior laws containing the revealing and uninformative laws and preserved by channel steps with any parameter in $[0,1]$ and by conditionally independent products. For $\mu,\nu\in\calC$, \begin{equation}\label{eq:moment-saving} m(\mu\star\nu)\leq m(\mu)+m(\nu) -c\left(\E_\mu[A^2]m(\nu)+m(\mu)\E_\nu[A^2]\right), \qquad c=\frac1{1000}. \end{equation}
- corrected: statement unchanged
- no error: only a side condition or reading the referee made explicit (see below)
- side condition added by the confirming referee `ass:pin-1`: For $x\in\mathbb R^3$, $|x|^2=x_1^2+x_2^2+x_3^2$. — pins reading of def:posterior-coordinates: The sentence immediately following the statistics display states that vector norms are Euclidean.
- side condition added by the confirming referee `ass:pin-2`: The combined posterior law is the law of $P$ under $Z\,d(\mu\otimes\nu)$, with $P_i=4p_iq_i/Z$ on $\{Z>0\}$ and any measurable simplex-valued extension on $\{Z=0\}$. — pins reading of def:product-rule: Immediately after the product-rule display, the paper states that the value of $P$ at $Z=0$ is irrelevant and derives the weighting from the conditional observation likelihoods.

### `lem:local-moments` (`main.tex:435-449`)

- as printed: \label{lem:local-moments} Fix $0<\lambda<1$. Let $\mu,\nu$ be symmetric posterior laws, with $\nu$ obtained by a channel step of parameter $\lambda$. There is a finite constant $C=C(\lambda)$ such that \begin{align} m(\mu\star\nu) &\geq m(\mu)+m(\nu) -C\bigl(h(\mu)m(\nu)+m(\mu)h(\nu)\bigr), \label{eq:local-m-lower}\\ h(\mu\star\nu) &\leq h(\mu)+h(\nu)+C m(\mu)m(\nu). \label{eq:local-h-upper} \end{align} The first inequality holds with $C=7$.
- corrected: statement unchanged
- no error: only a side condition or reading the referee made explicit (see below)
- side condition added by the confirming referee `ass:pin-1`: For $x\in\mathbb R^3$, $|x|^2=x_1^2+x_2^2+x_3^2$. — pins reading of def:posterior-coordinates: The sentence immediately following the statistics display states that vector norms are Euclidean.
- side condition added by the confirming referee `ass:pin-2`: The combined posterior law is the law of $P$ under $Z\,d(\mu\otimes\nu)$, with $P_i=4p_iq_i/Z$ on $\{Z>0\}$ and any measurable simplex-valued extension on $\{Z=0\}$. — pins reading of def:product-rule: Immediately after the product-rule display, the paper states that the value of $P$ at $Z=0$ is irrelevant and derives the weighting from the conditional observation likelihoods.

## Suggestions to the authors

Not errors: readings the paper determines but does not state, and side conditions the proofs use silently.

- clarification (`ass:pin-1`, used by `thm:main`): For $x\in\mathbb R^3$, $\|x\|^2=x_1^2+x_2^2+x_3^2$. — pins reading of def:posterior-coordinates: The sentence immediately following the statistics display states that vector norms are Euclidean.
- clarification (`ass:pin-2`, used by `thm:main`): The combined posterior law is the law of $P$ under $Z\,d(\mu\otimes\nu)$, with $P_i=4p_iq_i/Z$ on $\{Z>0\}$ and any measurable simplex-valued extension on $\{Z=0\}$. — pins reading of def:product-rule: Immediately after the product-rule display, the paper states that the value of $P$ at $Z=0$ is irrelevant and derives the weighting from the conditional observation likelihoods.
- `def:posterior-coordinates`: pinned reading: For $x\in\mathbb R^3$, $\|x\|^2=x_1^2+x_2^2+x_3^2$. (The sentence immediately following the statistics display states that vector norms are Euclidean.)
- `def:product-rule`: pinned reading: The combined posterior law is the law of $P$ under $Z\,d(\mu\otimes\nu)$, with $P_i=4p_iq_i/Z$ on $\{Z>0\}$ and any measurable simplex-valued extension on $\{Z=0\}$. (Immediately after the product-rule display, the paper states that the value of $P$ at $Z=0$ is irrelevant and derives the weighting from the conditional observation likelihoods.)
- reading of the symbol `L_n`: $L_n=\{v\in V(T):\|v\|=n\}$ for $n\in\mathbb N_0$. — The introductory tree notation defines levels by vertex depth; in particular $L_0$ consists of the root.
- reading of the symbol `\mu`: $\mu$ denotes the distribution of the posterior vector $p$ for an experiment about a uniform input spin in $[4]$, taken under the marginal law of the observation. In Theorem~\ref{thm:main}: The posterior laws of finite-depth subtree experiments, including descendant-level observations, independently channel-degraded terminal observations, and partial products at a vertex, belong to $\calC$. In Proposition~\ref{prop:companion}: $\mu\in\calC$, where $\calC$ is the class of symmetric posterior laws specified in the statement. In Lemma~\ref{lem:local-moments}: $\mu$ is symmetric, meaning invariant under all permutations of its four posterior entries; membership in $\calC$ is not required. — The definition preceding \eqref{eq:statistics} specifies the marginal posterior law. Proposition~\ref{prop:companion} restricts it to $\calC$; the following paragraph establishes membership for all finite-depth subtree experiments and partial products used in the paper. Lemma~\ref{lem:local-moments} assumes symmetry without requiring membership in $\calC$.
- reading of the symbol `\nu`: $\nu$ is the second marginal posterior law for an experiment about a uniform input spin in $[4]$. In Proposition~\ref{prop:companion}: $\nu\in\calC$, where $\calC$ is the class of symmetric posterior laws specified in the statement. In Lemma~\ref{lem:local-moments}: $\nu$ is a symmetric posterior law obtained by a channel step of parameter $\lambda$, with $0<\lambda<1$. — The normalized-product construction introduces $\mu\star\nu$ from the two marginal posterior laws. Proposition~\ref{prop:companion} restricts both laws to $\calC$; Lemma~\ref{lem:local-moments} assumes symmetry and a channel step of parameter $\lambda$ for $\nu$.
- reading of the symbol `t`: In a channel step, $t\in[0,1]$ denotes the parameter of the channel $P_t$. In Theorem~\ref{thm:main}: In the tangent inequality $(1+2t)^{-1/2}\geq1-t$ for $t\geq0$, the letter $t$ is a local dummy variable ranging over $[0,\infty)$, independent of its use as a channel parameter. — The channel-step paragraph explicitly specifies $t\in[0,1]$. The later tangent-bound sentence explicitly binds a separate local variable $t\geq0$.
- reading of the symbol `\star`: $\mu\star\nu$ is the law of $P$ under $Z\,d(\mu\otimes\nu)$, where $Z=4\sum_i p_iq_i$ and $P_i=4p_iq_i/Z$ on $\{Z>0\}$, with arbitrary simplex-valued extension on $\{Z=0\}$. — The definition preceding \eqref{eq:product-rule} combines experiments about the same uniform input, and the following paragraph explicitly specifies the weighted product construction.
- reading of the symbol `q`: $q$ is the second marginal posterior vector, with law $\nu$, for an experiment about a uniform input spin in $[4]$. In Lemma~\ref{lem:local-moments}: $q_i\geq(1-\lambda)/4$ for every $i\in\{1,2,3,4\}$, since its law is obtained by a channel step of parameter $\lambda$. — The normalized-product construction defines the second posterior vector and its law. The local moment lemma assumes that $\nu$ is obtained by a channel step of parameter $\lambda$, and its proof explicitly states that each coordinate of $q$ is at least $(1-\lambda)/4$.
- reading of the symbol `Z`: $Z=4\sum_{i=1}^4p_iq_i$ is the density of the joint marginal observation law relative to the product of its marginal laws, with $\int Z\,d(\mu\otimes\nu)=1$. In Lemma~\ref{lem:local-moments}: $Z=1+s\geq1-\lambda>0$. — The paragraph defining \eqref{eq:product-rule} identifies the weighting density and states $\E Z=1$; \eqref{eq:product-coordinates} and \eqref{eq:denominator} give its local coordinate expression and lower bound.
- reading of the symbol `P`: $P_i=4p_iq_i/Z$ on $\{Z>0\}$; its combined posterior law is the image under $P$ of the measure $Z\,d(\mu\otimes\nu)$, and its value on $\{Z=0\}$ may be any probability vector. In Lemma~\ref{lem:local-moments}: $Z=1+s\geq1-\lambda>0$, so the displayed coordinate formula defines $P$ throughout the product sampling law. — The paragraph surrounding \eqref{eq:product-rule} specifies the marginal weight $Z$, states $\E Z=1$, and says that the value of $P$ at $Z=0$ is irrelevant.
- reading of the symbol `s`: $s=x\cdot y$ satisfies $-\lambda\leq s\leq3$ and $1+s\geq1-\lambda>0$. — The proof defines $s$ in its opening display and gives these bounds in \eqref{eq:denominator}, using the channel-step lower bound on every coordinate of $q$.

## Added conditions

| id | where | class | condition |
| --- | --- | --- | --- |
| `ass:pin-1` | `thm:main` | V1.5 bookkeeping | For $x\in\mathbb R^3$, $\|x\|^2=x_1^2+x_2^2+x_3^2$. (pins reading of def:posterior-coordinates: The sentence immediately following the statistics display states that vector norms are Euclidean.) |
| `ass:pin-2` | `thm:main` | V1.5 bookkeeping | The combined posterior law is the law of $P$ under $Z\,d(\mu\otimes\nu)$, with $P_i=4p_iq_i/Z$ on $\{Z>0\}$ and any measurable simplex-valued extension on $\{Z=0\}$. (pins reading of def:product-rule: Immediately after the product-rule display, the paper states that the value of $P$ at $Z=0$ is irrelevant and derives the weighting from the conditional observation likelihoods.) |
| `ass:pin-1` | `prop:companion` | V1.5 bookkeeping | For $x\in\mathbb R^3$, $\|x\|^2=x_1^2+x_2^2+x_3^2$. (pins reading of def:posterior-coordinates: The sentence immediately following the statistics display states that vector norms are Euclidean.) |
| `ass:pin-2` | `prop:companion` | V1.5 bookkeeping | The combined posterior law is the law of $P$ under $Z\,d(\mu\otimes\nu)$, with $P_i=4p_iq_i/Z$ on $\{Z>0\}$ and any measurable simplex-valued extension on $\{Z=0\}$. (pins reading of def:product-rule: Immediately after the product-rule display, the paper states that the value of $P$ at $Z=0$ is irrelevant and derives the weighting from the conditional observation likelihoods.) |
| `ass:pin-1` | `lem:local-moments` | V1.5 bookkeeping | For $x\in\mathbb R^3$, $\|x\|^2=x_1^2+x_2^2+x_3^2$. (pins reading of def:posterior-coordinates: The sentence immediately following the statistics display states that vector norms are Euclidean.) |
| `ass:pin-2` | `lem:local-moments` | V1.5 bookkeeping | The combined posterior law is the law of $P$ under $Z\,d(\mu\otimes\nu)$, with $P_i=4p_iq_i/Z$ on $\{Z>0\}$ and any measurable simplex-valued extension on $\{Z=0\}$. (pins reading of def:product-rule: Immediately after the product-rule display, the paper states that the value of $P$ at $Z=0$ is irrelevant and derives the weighting from the conditional observation likelihoods.) |

## Conditions assumed

### Cited results

| id | used by | citation | locator | checked against |
| --- | --- | --- | --- | --- |
| `prop:companion` | `thm:main` | OpenAI26Potts | Proposition 3.2 and Equations (3.8)--(3.9) | source supplied by the user at discovery/cited_sources/OpenAI26Potts.txt |
| `prop:companion` | `prop:companion` | OpenAI26Potts | Proposition 3.2 and Equations (3.8)--(3.9) | source supplied by the user at discovery/cited_sources/OpenAI26Potts.txt |

`prop:companion` (OpenAI26Potts, Proposition 3.2 and Equations (3.8)--(3.9)):

What Lean assumes for it: `OaiCapacityCriterionState.CompanionMomentSaving` (`Helpers/CitedGates.lean:32`)

```lean
def CompanionMomentSaving : Sort 0 :=
  ∃ C : Set (Measure (Fin 4 → ℝ)), -- @realizes \calC(class of symmetric posterior laws)
    (∀ mu ∈ C, IsPosteriorLaw mu ∧ IsSymmetricLaw mu) ∧
    revealingLaw ∈ C ∧ uninformativeLaw ∈ C ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ mu ∈ C, channelStep t mu ∈ C) ∧
    (∀ mu ∈ C, ∀ nu ∈ C, starLaw mu nu ∈ C) ∧
    ∀ mu ∈ C, ∀ nu ∈ C,
      quadInfo (starLaw mu nu) ≤ quadInfo mu + quadInfo nu -
        (1 / 1000 : ℝ) * -- @realizes c(the fixed positive constant 1/1000)
          ((∫ p, quadStat p ^ 2 ∂mu) * quadInfo nu +
            quadInfo mu * ∫ p, quadStat p ^ 2 ∂nu)
```

### Deferred substrate gates

None: every substrate this run needed was built and proved.

## Unresolved / notes

- run-level `def:posterior-coordinates`: [note, V1.5] pinned reading: For $x\in\mathbb R^3$, $\|x\|^2=x_1^2+x_2^2+x_3^2$. (The sentence immediately following the statistics display states that vector norms are Euclidean.)
- run-level `def:product-rule`: [note, V1.5] pinned reading: The combined posterior law is the law of $P$ under $Z\,d(\mu\otimes\nu)$, with $P_i=4p_iq_i/Z$ on $\{Z>0\}$ and any measurable simplex-valued extension on $\{Z=0\}$. (Immediately after the product-rule display, the paper states that the value of $P$ at $Z=0$ is irrelevant and derives the weighting from the conditional observation likelihoods.)
- run-level `symbol T`: [note, V1.5] symbol table corrected: space "$\{\text{infinite rooted trees with uniformly bounded numbers of children}\}$", def "Let $T$ be an infinite locally finite rooted tree with root $\rho$. Assume that every vertex has at most $B$ children, where $B$ is a fixed positive integer; vertices with zero or one child are allowed. The tree is deterministic and known to the observer." (The recorded space permits locally finite trees without a uniform degree bound, whereas the paper assumes a fixed finite bound $B$ on the number of children throughout. The later capacity definition and theorem use the same tree.)
- run-level `symbol \star`: [note, V1.5] symbol table corrected: space "$\mathcal D\times\mathcal D\to\mathcal D$, where $\mathcal D=\{\eta\in\mathcal P(\Delta_4):\int p_i\,d\eta(p)=1/4\text{ for }i=1,2,3,4\}$ and $\Delta_4=\{p\in[0,1]^4:\sum_i p_i=1\}$" (The recorded function space includes arbitrary simplex laws, whereas the operation is defined for posterior laws of a uniform input, which have uniform barycenter. The weighted pushforward specifies the operation independently of a realization of the experiments.)
- run-level `symbol \calC`: [note, V1.5] symbol table corrected: def "A class $\calC$ of symmetric posterior laws containing the revealing and uninformative laws and preserved by channel steps with any parameter in $[0,1]$ and by conditionally independent products." (The recorded description omits the specified members and closure operations. These properties determine why the finite subtree experiments and partial products belong to the asserted class.)
- note on `def:posterior-coordinates`: pinned reading: For $x\in\mathbb R^3$, $\|x\|^2=x_1^2+x_2^2+x_3^2$. (The sentence immediately following the statistics display states that vector norms are Euclidean.)
- note on `def:product-rule`: pinned reading: The combined posterior law is the law of $P$ under $Z\,d(\mu\otimes\nu)$, with $P_i=4p_iq_i/Z$ on $\{Z>0\}$ and any measurable simplex-valued extension on $\{Z=0\}$. (Immediately after the product-rule display, the paper states that the value of $P$ at $Z=0$ is irrelevant and derives the weighting from the conditional observation likelihoods.)
- note on `prop:companion`: cited source checked: source supplied by the user at discovery/cited_sources/OpenAI26Potts.txt
- note on `symbol \calC`: symbol table corrected: def "A class $\calC$ of symmetric posterior laws containing the revealing and uninformative laws and preserved by channel steps with any parameter in $[0,1]$ and by conditionally independent products." (The recorded description omits the specified members and closure operations. These properties determine why the finite subtree experiments and partial products belong to the asserted class.)
- note on `symbol \star`: symbol table corrected: space "$\mathcal D\times\mathcal D\to\mathcal D$, where $\mathcal D=\{\eta\in\mathcal P(\Delta_4):\int p_i\,d\eta(p)=1/4\text{ for }i=1,2,3,4\}$ and $\Delta_4=\{p\in[0,1]^4:\sum_i p_i=1\}$" (The recorded function space includes arbitrary simplex laws, whereas the operation is defined for posterior laws of a uniform input, which have uniform barycenter. The weighted pushforward specifies the operation independently of a realization of the experiments.)
- note on `symbol T`: symbol table corrected: space "$\{\text{infinite rooted trees with uniformly bounded numbers of children}\}$", def "Let $T$ be an infinite locally finite rooted tree with root $\rho$. Assume that every vertex has at most $B$ children, where $B$ is a fixed positive integer; vertices with zero or one child are allowed. The tree is deterministic and known to the observer." (The recorded space permits locally finite trees without a uniform degree bound, whereas the paper assumes a fixed finite bound $B$ on the number of children throughout. The later capacity definition and theorem use the same tree.)

### V1 lint warnings

- lem:flow: depends on ass:main-tree which the environment never references; V1.5 must confirm the paper actually assumes it
- lem:flow: depends on ass:main-lambda which the environment never references; V1.5 must confirm the paper actually assumes it

### Parser warnings

- main.tex:10: \input{glyphtounicode} not found (tried glyphtounicode.tex, glyphtounicode relative to . and the source root); skipped (the bundle does not ship it — check that no result lived there)
- main.tex:11: \input{glyphtounicode-cmex} not found (tried glyphtounicode-cmex.tex, glyphtounicode-cmex relative to . and the source root); skipped (the bundle does not ship it — check that no result lived there)
- referee fix applied — lem:flow: depends_on + ass:main-tree, ass:main-lambda

## Lean evidence

- build of the run barrel: **ok**
- source scan (sorry / admit / axiom): clean

| declaration | axioms |
| --- | --- |
| `OaiCapacityCriterionState.reconstructs_iff_capacity_pos` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `OaiCapacityCriterionState.exists_flow_of_labels` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `OaiCapacityCriterionState.local_moment_bounds` | clean — `propext`, `Classical.choice`, `Quot.sound` |

## Inputs

| artifact | status |
| --- | --- |
| `discovery/v1_scope.json` | present (4 environment(s)) |
| `discovery/v1_5_review.json` | present (verdict PASS) |
| `formalization/crosswalk_full.json` | present (432 object(s)) |
| `graph.json` | present (436 node(s)) |
| Lean evidence | collected (build ok, 0 scan issue(s), 359 declaration(s)) |

## Annotated paper

Annotated paper: `annotated/main.tex` (11 annotation(s), 0 unlocated; index `annotated/ANNOTATIONS.md`); PDF: `annotated/main.pdf`
