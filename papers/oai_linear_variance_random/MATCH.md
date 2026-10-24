# The corrected paper and its Lean formalization — oai_linear_variance_random

For each result of the corrected paper: its statement, the Lean declaration that states it, whether that declaration is proved, and how the two statements correspond phrase by phrase. A result stated differently from the original paper is marked "corrected"; the report says what changed and why.

## Theorem 1.1

**Statement.** \label{thm:main} There is an absolute constant $C<\infty$ such that \[ \Var(H_n)\le Cn\qquad(n\ge3). \] There are also absolute constants $c>0$ and $n_0$ such that $\Var(H_n)\ge cn$ for $n\ge n_0$. In particular, $\Var(H_n)=\Theta(n)$ as $n\to\infty$.

**Lean.** `Papers.OaiLinearVarianceRandom.var_hittingTime_theta_n` — `lean/Papers/OaiLinearVarianceRandom/TMain.lean:124`

**Status.** proved in Lean, given 1 cited result(s). **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| There is an absolute constant $C<\infty$ such that | then `∃ C : ℝ,` |
| \[ \Var(H_n)\le Cn\qquad | then `variance (fun ω => (hittingTime (fun j => Cseq j ω) : ℝ)) μ ≤ C * n` |
| (n\ge3). \] | `∀ n : ℕ`<br>`MainN n` |
| There are also absolute constants $c>0$ and $n_0$ such that $\Var(H_n)\ge cn$ for $n\ge n_0$. | then `∃ c : ℝ,`<br>then `0 < c`<br>then `∃ n0 : ℝ,`<br>`∀ n : ℕ`<br>`n0 ≤ n`<br>then `c * n ≤ variance (fun ω => (hittingTime (fun j => Cseq j ω) : ℝ)) μ` |
| In particular, $\Var(H_n)=\Theta(n)$ as $n\to\infty$. | — (no Lean counterpart recorded) |

Lean also declares what the paper leaves implicit (the objects and their types): `Ω : Type`, `MeasurableSpace Ω`, `μ : Measure Ω`, `IsProbabilityMeasure μ`, `Cseq : ℕ → Ω → ProperClause n`, `Ω : Type`, `MeasurableSpace Ω`, `μ : Measure Ω`, `IsProbabilityMeasure μ`, `Cseq : ℕ → Ω → ProperClause n`.

Lean assumes conditions that the paper's text does not state: `hWilson_of_gate : WilsonSeparation`, `IsUniformClauseProcess μ Cseq`, `MainN n`, `IsUniformClauseProcess μ Cseq`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: Fix an integer $n\ge3$. → `MainN` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:158`)
- condition of the paper: Let $C_1,C_2,\ldots$ be independent clauses, each uniform among the $8\binom n3$ proper 3-clauses. → `IsUniformClauseProcess` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:172`)
- definition of the paper: Write \[ F_m=\bigwedge_{j=1}^m C_j,\qquad H_n=\min\{m\ge1:F_m\text{ is unsatisfiable}\}, \] where $F_0$ is the empty, satisfiable formula. → `hittingTime` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:199`)
- definition of the paper: set $L=10n$, and let $T=\min(H_n,L)$. → `cappedTime` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:210`)
- definition of the paper: Define the survival function and its integer level locations by \[ s_n(m)=\Prb(H_n>m),\qquad r_n(p)=\min\{m\ge0:s_n(m)\le p\}\quad(0<p<1). \] → `survivalLevels` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:512`)

**Taken from the literature: Wilson2002, Corollary 4.**

What Lean assumes for it: `Papers.OaiLinearVarianceRandom.WilsonSeparation` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:556`)

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

## Lemma 2.1

**Statement.** \label{lem:one} For a nonempty assignment set $S$, let $h_a(S)$ be the probability that one random proper $a$-clause kills $S$, for $a=2,3$. Then \begin{equation} h_2(S)^\beta\le3h_3(S)+u^{-3}. \label{eq:one} \end{equation}

**Lean.** `Papers.OaiLinearVarianceRandom.oneKillProb_two_rpow_le` — `lean/Papers/OaiLinearVarianceRandom/Helpers/AssignmentSets.lean:347`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| For a nonempty assignment set $S$, let $h_a(S)$ be the probability that one random proper $a$-clause kills $S$, for $a=2,3$. | `hclause : ∀ a, a = 2 ∨ a = 3 →`<br>`OneClauseLaw a (ν a)`<br>`S : Finset (Fin u → Bool)`<br>`hS : OneNonempty S` |
| Then \begin{equation} h_2(S)^\beta\le3h_3(S)+u^{-3}. \end{equation} | then `(oneKillProb 2 S) ^ beta ≤ 3 * oneKillProb 3 S + (u : ℝ) ^ (-3 : ℝ)` |

Lean also declares what the paper leaves implicit (the objects and their types): `u : ℕ`, `ν : (a : ℕ) → Measure (ProperClauseA u a)`, `νj : (j : ℕ) → Measure (Fin j → ProperClauseA u 2)`.

Lean assumes conditions that the paper's text does not state: `hu : OneU u`, `hreplacement : SampledWithReplacement (ν 2) νj`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: We first work on $u\ge3$ variables, independently of the clause process. → `OneU` (`lean/Papers/OaiLinearVarianceRandom/Helpers/AssignmentSets.lean:30`)
- condition of the paper: Throughout, a random proper $a$-clause on a specified variable set is uniform over the clauses using $a$ distinct variables and independent fair signs. → `OneClauseLaw` (`lean/Papers/OaiLinearVarianceRandom/Helpers/AssignmentSets.lean:48`)
- condition of the paper: For a nonempty assignment set $S$ → `OneNonempty` (`lean/Papers/OaiLinearVarianceRandom/Helpers/AssignmentSets.lean:36`)
- definition of the paper: \label{lem:one} For a nonempty assignment set $S$, let $h_a(S)$ be the probability that one random proper $a$-clause kills $S$, for $a=2,3$. → `oneKillProb` (`lean/Papers/OaiLinearVarianceRandom/Helpers/AssignmentSets.lean:169`)
- definition of the paper: Set $\beta=3/2$ for the rest of the paper. → `beta` (`lean/Papers/OaiLinearVarianceRandom/Helpers/AssignmentSets.lean:163`)
- condition of the paper: Independent collections are sampled with replacement. → `SampledWithReplacement` (`lean/Papers/OaiLinearVarianceRandom/Helpers/AssignmentSets.lean:67`)

## Lemma 2.2

**Statement.** \label{lem:potential} For every integer $d\ge1$, put \[ P_d(S)=\sum_{j=0}^{d-1}q_j(S). \] Then $0\le P_d(S)\le d$, and $P_d$ is nondecreasing when $S$ shrinks. If $C$ is an independent random proper 3-clause on the $u$ variables, then \begin{equation} \ind_{\{S\ne\varnothing\}}q_d(S)^\beta \le d^{\beta-1} \left(3\E_C[P_d(S[C])-P_d(S)]+du^{-3}\right). \label{eq:drift} \end{equation}

**Lean.** `Papers.OaiLinearVarianceRandom.potential_drift` — `lean/Papers/OaiLinearVarianceRandom/Helpers/Potential.lean:244`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| For every integer $d\ge1$, put | `d : ℕ`<br>`hd : PotentialD d` |
| \[ P_d(S)=\sum_{j=0}^{d-1}q_j(S). \] | — (no Lean counterpart recorded) |
| Then $0\le P_d(S)\le d$, | then `0 ≤ potential d S`<br>then `potential d S ≤ d` |
| and $P_d$ is nondecreasing when $S$ shrinks. | `∀ S' : Finset (Fin u → Bool)`<br>`S' ⊆ S`<br>then `potential d S ≤ potential d S'` |
| If $C$ is an independent random proper 3-clause on the $u$ variables, | `u : ℕ`<br>`hC : PotentialClauseLaw (ν 3) νj joint` |
| then \begin{equation} \ind_{\{S\ne\varnothing\}}q_d(S)^\beta \le d^{\beta-1} \left(3\E_C[P_d(S[C])-P_d(S)]+du^{-3}\right). \end{equation} | then `(if S.Nonempty then (1 : ℝ) else 0) * (killProb d S) ^ beta ≤ (d : ℝ) ^ (beta - 1) * (3 * (∫ C, potential d (survivors S C) - potential d S ∂(ν 3)) + d * (u : ℝ) ^ (-3 : ℝ))` |

Lean also declares what the paper leaves implicit (the objects and their types): `ν : (a : ℕ) → Measure (ProperClauseA u a)`, `S : Finset (Fin u → Bool)`, `νj : (j : ℕ) → Measure (Fin j → ProperClauseA u 2)`, `joint : (j : ℕ) → Measure ((Fin j → ProperClauseA u 2) × ProperClauseA u 3)`.

Lean assumes conditions that the paper's text does not state: `hu : OneU u`, `hclause : ∀ a, a = 2 ∨ a = 3 →`, `OneClauseLaw a (ν a)`, `hreplacement : SampledWithReplacement (ν 2) νj`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: We first work on $u\ge3$ variables, independently of the clause process. → `OneU` (`lean/Papers/OaiLinearVarianceRandom/Helpers/AssignmentSets.lean:30`)
- condition of the paper: Throughout, a random proper $a$-clause on a specified variable set is uniform over the clauses using $a$ distinct variables and independent fair signs. → `OneClauseLaw` (`lean/Papers/OaiLinearVarianceRandom/Helpers/AssignmentSets.lean:48`)
- condition of the paper: For every integer $d\ge1$ → `PotentialD` (`lean/Papers/OaiLinearVarianceRandom/Helpers/AssignmentSets.lean:42`)
- condition of the paper: If $C$ is an independent random proper 3-clause on the $u$ variables, → `PotentialClauseLaw` (`lean/Papers/OaiLinearVarianceRandom/Helpers/AssignmentSets.lean:57`)
- definition of the paper: For $S\subseteq\{0,1\}^u$ and a clause $C$, let \[ S[C]=\{z\in S:z\models C\}. \] → `survivors` (`lean/Papers/OaiLinearVarianceRandom/Helpers/AssignmentSets.lean:75`)
- definition of the paper: For $j\ge0$, define $q_j(S)$ as the probability that $j$ independent random proper 2-clauses \emph{kill} $S$, meaning that no member of $S$ satisfies them all. → `killProb` (`lean/Papers/OaiLinearVarianceRandom/Helpers/AssignmentSets.lean:91`)
- definition of the paper: In particular, \[ q_j(\varnothing)=1\quad(j\ge0),\qquad q_0(S)=0\quad(S\ne\varnothing). \] → `killProb_conventions` (`lean/Papers/OaiLinearVarianceRandom/Helpers/AssignmentSets.lean:101`)
- definition of the paper: Set $\beta=3/2$ for the rest of the paper. → `beta` (`lean/Papers/OaiLinearVarianceRandom/Helpers/AssignmentSets.lean:163`)
- definition of the paper: \label{lem:potential} For every integer $d\ge1$, put \[ P_d(S)=\sum_{j=0}^{d-1}q_j(S). \] → `potential` (`lean/Papers/OaiLinearVarianceRandom/Helpers/AssignmentSets.lean:178`)
- definition of the paper: \label{lem:one} For a nonempty assignment set $S$, let $h_a(S)$ be the probability that one random proper $a$-clause kills $S$, for $a=2,3$. → `oneKillProb` (`lean/Papers/OaiLinearVarianceRandom/Helpers/AssignmentSets.lean:169`)
- condition of the paper: Independent collections are sampled with replacement. → `SampledWithReplacement` (`lean/Papers/OaiLinearVarianceRandom/Helpers/AssignmentSets.lean:67`)

## Lemma 3.1

**Statement.** \label{lem:omission} The capped hitting time satisfies \begin{equation} \Var(T)\le\sum_{i=1}^L\E D_i^2. \label{eq:variance-deletion} \end{equation}

**Lean.** `Papers.OaiLinearVarianceRandom.variance_cappedTime_le_sum_delay_sq` — `lean/Papers/OaiLinearVarianceRandom/Helpers/Omission.lean:119`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| The capped hitting time satisfies | — (no Lean counterpart recorded) |
| \begin{equation} \Var(T)\le\sum_{i=1}^L\E D_i^2. \end{equation} | then `variance (fun ω => (cappedTime (fun j => Cseq j ω) : ℝ)) μ ≤ ∑ i ∈ Finset.Icc 1 (capL n), ∫ ω, (delay (fun j => Cseq j ω) i : ℝ) ^ 2 ∂μ` |

Lean also declares what the paper leaves implicit (the objects and their types): `n : ℕ`, `Ω : Type`, `MeasurableSpace Ω`, `μ : Measure Ω`, `IsProbabilityMeasure μ`, `Cseq : ℕ → Ω → ProperClause n`.

Lean assumes conditions that the paper's text does not state: `hn : OmissionN n`, `hlaw : IsUniformClauseProcess μ Cseq`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: Assume $n\ge6$ → `OmissionN` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:162`)
- condition of the paper: Let $C_1,C_2,\ldots$ be independent clauses, each uniform among the $8\binom n3$ proper 3-clauses. → `IsUniformClauseProcess` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:172`)
- definition of the paper: Write \[ F_m=\bigwedge_{j=1}^m C_j,\qquad H_n=\min\{m\ge1:F_m\text{ is unsatisfiable}\}, \] where $F_0$ is the empty, satisfiable formula. → `hittingTime` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:199`)
- definition of the paper: set $L=10n$, and let $T=\min(H_n,L)$. → `cappedTime` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:210`)
- definition of the paper: For $1\le i\le L$, omit $C_i$ while retaining the original indices: \[ B_m^{(i)}=\bigwedge_{\substack{1\le j\le m\\j\ne i}} C_j. \] → `omittedPrefixSat` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:287`)
- definition of the paper: Let $T^{(i)}$ be the first index at which this omitted-clause process is unsatisfiable, capped at $L$, and set $D_i=T^{(i)}-T\ge0$. → `omittedCappedTime` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:295`)

## Lemma 3.2

**Statement.** \label{lem:tests} For $i\le m<L$, conditional on $\cG_m$, \begin{align} \Prb(A_m\mid\cG_m)&\le\ind_{\{S_m\ne\varnothing\}}p_m^3 &&\text{on }\{V=0\},\label{eq:test3}\\ \Prb(A_m\mid\cG_m)&\le\ind_{\{S_m\ne\varnothing\}}p_m^2 &&\text{on }\{V=1\}. \label{eq:test2} \end{align}

**Lean.** `Papers.OaiLinearVarianceRandom.condProb_pivotal_le` — `lean/Papers/OaiLinearVarianceRandom/Helpers/Pivotality.lean:36`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| For $i\le m<L$, conditional on $\cG_m$, | `i : ℕ`<br>`m : ℕ`<br>`hm : TestsTime i m (capL n)` |
| \begin{align} \Prb(A_m\mid\cG_m)&\le\ind_{\{S_m\ne\varnothing\}}p_m^3 &&\text{on }\{V=0\},\\ | then `∀ᵐ ω ∂(fixedClauseMeasure μ Cseq i c0),`<br>`collisionCount c0 Cseq i ω = 0`<br>then `((fixedClauseMeasure μ Cseq i c0)[ eventIndicator (pivotalEvent Cseq i m) | ordinaryFiltration c0 Cseq i m]) ω ≤ (if (nonrootSolutions c0 Cseq i m ω).Nonempty then 1 else 0) * (killProcess c0 Cseq i m ω) ^ 3` |
| \Prb(A_m\mid\cG_m)&\le\ind_{\{S_m\ne\varnothing\}}p_m^2 &&\text{on }\{V=1\}. \end{align} | then `∀ᵐ ω ∂(fixedClauseMeasure μ Cseq i c0),`<br>`collisionCount c0 Cseq i ω = 1`<br>then `((fixedClauseMeasure μ Cseq i c0)[ eventIndicator (pivotalEvent Cseq i m) | ordinaryFiltration c0 Cseq i m]) ω ≤ (if (nonrootSolutions c0 Cseq i m ω).Nonempty then 1 else 0) * (killProcess c0 Cseq i m ω) ^ 2` |

Lean also declares what the paper leaves implicit (the objects and their types): `n : ℕ`, `Ω : Type`, `MeasurableSpace Ω`, `μ : Measure Ω`, `IsProbabilityMeasure μ`, `Cseq : ℕ → Ω → ProperClause n`, `c0 : ProperClause n`.

Lean assumes conditions that the paper's text does not state: `hn : OmissionN n`, `hlaw : IsUniformClauseProcess μ Cseq`, `hi : DelayIndex i (capL n)`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: Assume $n\ge6$ → `OmissionN` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:162`)
- condition of the paper: Let $C_1,C_2,\ldots$ be independent clauses, each uniform among the $8\binom n3$ proper 3-clauses. → `IsUniformClauseProcess` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:172`)
- condition of the paper: Throughout, a random proper $a$-clause on a specified variable set is uniform over the clauses using $a$ distinct variables and independent fair signs. → `OneClauseLaw` (`lean/Papers/OaiLinearVarianceRandom/Helpers/AssignmentSets.lean:48`)
- definition of the paper: Write \[ F_m=\bigwedge_{j=1}^m C_j,\qquad H_n=\min\{m\ge1:F_m\text{ is unsatisfiable}\}, \] where $F_0$ is the empty, satisfiable formula. → `hittingTime` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:199`)
- definition of the paper: set $L=10n$, and let $T=\min(H_n,L)$. → `cappedTime` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:210`)
- definition of the paper: For $1\le i\le L$, omit $C_i$ while retaining the original indices: \[ B_m^{(i)}=\bigwedge_{\substack{1\le j\le m\\j\ne i}} C_j. \] → `omittedPrefixSat` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:287`)
- definition of the paper: Let $T^{(i)}$ be the first index at which this omitted-clause process is unsatisfiable, capped at $L$, and set $D_i=T^{(i)}-T\ge0$. → `omittedCappedTime` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:295`)
- definition of the paper: Write $B_m=B_m^{(i)}$. → `omittedPrefixSatAt` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:76`)
- definition of the paper: Call the three variables of $C_i$ the \emph{roots}, denote their set by $R$, and let $w\in\{0,1\}^R$ be the unique root assignment falsifying $C_i$. → `roots` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:83`)
- definition of the paper: There are $u=n-3\ge3$ nonroot variables. → `nonrootCount` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:142`)
- definition of the paper: For $i\le m<L$, define \begin{equation} A_m=\{B_m\text{ is satisfiable and }B_m\wedge C_i \text{ is unsatisfiable}\} =\{T\le m<T^{(i)}\}. \label{eq:A} \end{equation} → `pivotalEvent` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:187`)
- definition of the paper: For $i\le m\le L$, let $S_m\subseteq\{0,1\}^u$ consist of the nonroot assignments that, together with $w$, satisfy $B_m$. → `nonrootSolutions` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:292`)
- definition of the paper: For every index $j\le L$ other than $i$, first reveal the subset of $R$ met by $C_j$ and all signs on that subset. Classify the index as follows: \begin{itemize} \item An \emph{ordinary} clause meets no root; leave all its contents hidden. \item A \emph{test} clause meets exactly one root, whose literal is true under $w$; leave its two nonroot literals hidden. \item For every other clause, reveal all its remaining contents. \end{itemize} Let $\cE$ be the sigma-field of this exposure, including the information at future indices. → `exposureSigma` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:335`)
- definition of the paper: Let $Z$ count the exposed indices meeting at least one root, and let $V$ count those meeting at least two roots. → `exposureCounts` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:372`)
- definition of the paper: Set $d=\max\{1,Z\}$. → `incidenceParam` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:382`)
- definition of the paper: For $i\le m\le L$, define \begin{align*} \cG_m&=\cE\vee\sigma(\text{ordinary contents through index }m),\\ \cH_m&=\cG_m\vee\sigma(\text{test parts through index }m). \end{align*} → `ordinaryFiltration` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:408`)
- definition of the paper: Finally, put \begin{equation} p_m=q_d(S_m). \label{eq:p} \end{equation} → `killProcess` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:436`)
- definition of the paper: For $j\ge0$, define $q_j(S)$ as the probability that $j$ independent random proper 2-clauses \emph{kill} $S$, meaning that no member of $S$ satisfies them all. → `killProb` (`lean/Papers/OaiLinearVarianceRandom/Helpers/AssignmentSets.lean:91`)
- condition of the paper: For $i\le m<L$ → `TestsTime` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:33`)
- condition of the paper: Independent collections are sampled with replacement. → `SampledWithReplacement` (`lean/Papers/OaiLinearVarianceRandom/Helpers/AssignmentSets.lean:67`)
- condition of the paper: For $1\le i\le L$ → `DelayIndex` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:55`)

## Lemma 4.1

**Statement.** \label{lem:occupation} With $K=7$, for every $i\le m<L$, \begin{equation} \E\left[\sum_{s=m}^{L-1}\ind_{\{S_s\ne\varnothing\}}p_s^\beta \,\middle|\,\cH_m\right] \le Kd^\beta. \label{eq:occupation} \end{equation}

**Lean.** `Papers.OaiLinearVarianceRandom.condExp_occupation_le` — `lean/Papers/OaiLinearVarianceRandom/Helpers/Pivotality.lean:85`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| With $K=7$, for every $i\le m<L$, | `i : ℕ`<br>`m : ℕ`<br>`hm : OccupationTime i m (capL n)` |
| \begin{equation} \E\left[\sum_{s=m}^{L-1}\ind_{\{S_s\ne\varnothing\}}p_s^\beta \,\middle\|\,\cH_m\right] \le Kd^\beta. \end{equation} | then `((fixedClauseMeasure μ Cseq i c0)[ (fun ω => ∑ s ∈ Finset.Ico m (capL n), occupationTerm c0 Cseq i s ω) | testFiltration c0 Cseq i m]) ≤ᵐ[fixedClauseMeasure μ Cseq i c0] (fun ω => occupationK * (incidenceParam c0 Cseq i ω : ℝ) ^ beta)` |

Lean also declares what the paper leaves implicit (the objects and their types): `n : ℕ`, `Ω : Type`, `MeasurableSpace Ω`, `μ : Measure Ω`, `IsProbabilityMeasure μ`, `Cseq : ℕ → Ω → ProperClause n`, `c0 : ProperClause n`.

Lean assumes conditions that the paper's text does not state: `hn : OmissionN n`, `hlaw : IsUniformClauseProcess μ Cseq`, `hi : DelayIndex i (capL n)`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: Assume $n\ge6$ → `OmissionN` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:162`)
- condition of the paper: Let $C_1,C_2,\ldots$ be independent clauses, each uniform among the $8\binom n3$ proper 3-clauses. → `IsUniformClauseProcess` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:172`)
- condition of the paper: Throughout, a random proper $a$-clause on a specified variable set is uniform over the clauses using $a$ distinct variables and independent fair signs. → `OneClauseLaw` (`lean/Papers/OaiLinearVarianceRandom/Helpers/AssignmentSets.lean:48`)
- definition of the paper: Write \[ F_m=\bigwedge_{j=1}^m C_j,\qquad H_n=\min\{m\ge1:F_m\text{ is unsatisfiable}\}, \] where $F_0$ is the empty, satisfiable formula. → `hittingTime` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:199`)
- definition of the paper: set $L=10n$, and let $T=\min(H_n,L)$. → `cappedTime` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:210`)
- definition of the paper: For $1\le i\le L$, omit $C_i$ while retaining the original indices: \[ B_m^{(i)}=\bigwedge_{\substack{1\le j\le m\\j\ne i}} C_j. \] → `omittedPrefixSat` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:287`)
- definition of the paper: Let $T^{(i)}$ be the first index at which this omitted-clause process is unsatisfiable, capped at $L$, and set $D_i=T^{(i)}-T\ge0$. → `omittedCappedTime` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:295`)
- definition of the paper: Write $B_m=B_m^{(i)}$. → `omittedPrefixSatAt` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:76`)
- definition of the paper: Call the three variables of $C_i$ the \emph{roots}, denote their set by $R$, and let $w\in\{0,1\}^R$ be the unique root assignment falsifying $C_i$. → `roots` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:83`)
- definition of the paper: There are $u=n-3\ge3$ nonroot variables. → `nonrootCount` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:142`)
- definition of the paper: For $i\le m<L$, define \begin{equation} A_m=\{B_m\text{ is satisfiable and }B_m\wedge C_i \text{ is unsatisfiable}\} =\{T\le m<T^{(i)}\}. \label{eq:A} \end{equation} → `pivotalEvent` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:187`)
- definition of the paper: For $i\le m\le L$, let $S_m\subseteq\{0,1\}^u$ consist of the nonroot assignments that, together with $w$, satisfy $B_m$. → `nonrootSolutions` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:292`)
- definition of the paper: For every index $j\le L$ other than $i$, first reveal the subset of $R$ met by $C_j$ and all signs on that subset. Classify the index as follows: \begin{itemize} \item An \emph{ordinary} clause meets no root; leave all its contents hidden. \item A \emph{test} clause meets exactly one root, whose literal is true under $w$; leave its two nonroot literals hidden. \item For every other clause, reveal all its remaining contents. \end{itemize} Let $\cE$ be the sigma-field of this exposure, including the information at future indices. → `exposureSigma` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:335`)
- definition of the paper: Let $Z$ count the exposed indices meeting at least one root, and let $V$ count those meeting at least two roots. → `exposureCounts` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:372`)
- definition of the paper: Set $d=\max\{1,Z\}$. → `incidenceParam` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:382`)
- definition of the paper: For $i\le m\le L$, define \begin{align*} \cG_m&=\cE\vee\sigma(\text{ordinary contents through index }m),\\ \cH_m&=\cG_m\vee\sigma(\text{test parts through index }m). \end{align*} → `ordinaryFiltration` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:408`)
- definition of the paper: Finally, put \begin{equation} p_m=q_d(S_m). \label{eq:p} \end{equation} → `killProcess` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:436`)
- definition of the paper: For $j\ge0$, define $q_j(S)$ as the probability that $j$ independent random proper 2-clauses \emph{kill} $S$, meaning that no member of $S$ satisfies them all. → `killProb` (`lean/Papers/OaiLinearVarianceRandom/Helpers/AssignmentSets.lean:91`)
- condition of the paper: for every $i\le m<L$ → `OccupationTime` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:41`)
- definition of the paper: With $K=7$ → `occupationK` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:444`)
- definition of the paper: \label{lem:potential} For every integer $d\ge1$, put \[ P_d(S)=\sum_{j=0}^{d-1}q_j(S). \] → `potential` (`lean/Papers/OaiLinearVarianceRandom/Helpers/AssignmentSets.lean:178`)
- definition of the paper: Set $\beta=3/2$ for the rest of the paper. → `beta` (`lean/Papers/OaiLinearVarianceRandom/Helpers/AssignmentSets.lean:163`)
- condition of the paper: Independent collections are sampled with replacement. → `SampledWithReplacement` (`lean/Papers/OaiLinearVarianceRandom/Helpers/AssignmentSets.lean:67`)
- condition of the paper: For $1\le i\le L$ → `DelayIndex` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:55`)

## Corollary 4.2

**Statement.** \label{cor:duration} For $i\le m<L$, \begin{equation} \E\left[\sum_{s=m}^{L-1}\ind_{A_s}\,\middle|\,\cH_m\right]\le W_m, \qquad W_m=\begin{cases} \min\{L,Kd^\beta p_m^{-\beta}\},&p_m>0,\\ L,&p_m=0. \end{cases} \label{eq:duration} \end{equation} In particular, $W_m$ is measurable with respect to the smaller sigma-field $\cG_m$.

**Lean.** `Papers.OaiLinearVarianceRandom.condExp_pivotal_duration_le` — `lean/Papers/OaiLinearVarianceRandom/TDuration.lean:82`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| For $i\le m<L$, | `i : ℕ`<br>`m : ℕ`<br>`hm : DurationTime i m (capL n)` |
| \begin{equation} \E\left[\sum_{s=m}^{L-1}\ind_{A_s}\,\middle\|\,\cH_m\right]\le W_m, \qquad | then `((fixedClauseMeasure μ Cseq i c0)[ (fun ω => ∑ s ∈ Finset.Ico m (capL n), eventIndicator (pivotalEvent Cseq i s) ω) | testFiltration c0 Cseq i m]) ≤ᵐ[fixedClauseMeasure μ Cseq i c0] durationBound c0 Cseq i m` |
| W_m=\begin{cases} \min\{L,Kd^\beta p_m^{-\beta}\},&p_m>0,\\ L,&p_m=0. \end{cases} \end{equation} | — (no Lean counterpart recorded) |
| In particular, $W_m$ is measurable with respect to the smaller sigma-field $\cG_m$. | then `StronglyMeasurable[ordinaryFiltration c0 Cseq i m] (durationBound c0 Cseq i m)` |

Lean also declares what the paper leaves implicit (the objects and their types): `n : ℕ`, `Ω : Type`, `MeasurableSpace Ω`, `μ : Measure Ω`, `IsProbabilityMeasure μ`, `Cseq : ℕ → Ω → ProperClause n`, `c0 : ProperClause n`.

Lean assumes conditions that the paper's text does not state: `hn : OmissionN n`, `hlaw : IsUniformClauseProcess μ Cseq`, `hi : DelayIndex i (capL n)`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: Assume $n\ge6$ → `OmissionN` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:162`)
- condition of the paper: Let $C_1,C_2,\ldots$ be independent clauses, each uniform among the $8\binom n3$ proper 3-clauses. → `IsUniformClauseProcess` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:172`)
- condition of the paper: Throughout, a random proper $a$-clause on a specified variable set is uniform over the clauses using $a$ distinct variables and independent fair signs. → `OneClauseLaw` (`lean/Papers/OaiLinearVarianceRandom/Helpers/AssignmentSets.lean:48`)
- definition of the paper: Write \[ F_m=\bigwedge_{j=1}^m C_j,\qquad H_n=\min\{m\ge1:F_m\text{ is unsatisfiable}\}, \] where $F_0$ is the empty, satisfiable formula. → `hittingTime` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:199`)
- definition of the paper: set $L=10n$, and let $T=\min(H_n,L)$. → `cappedTime` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:210`)
- definition of the paper: For $1\le i\le L$, omit $C_i$ while retaining the original indices: \[ B_m^{(i)}=\bigwedge_{\substack{1\le j\le m\\j\ne i}} C_j. \] → `omittedPrefixSat` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:287`)
- definition of the paper: Let $T^{(i)}$ be the first index at which this omitted-clause process is unsatisfiable, capped at $L$, and set $D_i=T^{(i)}-T\ge0$. → `omittedCappedTime` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:295`)
- definition of the paper: Write $B_m=B_m^{(i)}$. → `omittedPrefixSatAt` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:76`)
- definition of the paper: Call the three variables of $C_i$ the \emph{roots}, denote their set by $R$, and let $w\in\{0,1\}^R$ be the unique root assignment falsifying $C_i$. → `roots` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:83`)
- definition of the paper: There are $u=n-3\ge3$ nonroot variables. → `nonrootCount` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:142`)
- definition of the paper: For $i\le m<L$, define \begin{equation} A_m=\{B_m\text{ is satisfiable and }B_m\wedge C_i \text{ is unsatisfiable}\} =\{T\le m<T^{(i)}\}. \label{eq:A} \end{equation} → `pivotalEvent` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:187`)
- definition of the paper: For $i\le m\le L$, let $S_m\subseteq\{0,1\}^u$ consist of the nonroot assignments that, together with $w$, satisfy $B_m$. → `nonrootSolutions` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:292`)
- definition of the paper: For every index $j\le L$ other than $i$, first reveal the subset of $R$ met by $C_j$ and all signs on that subset. Classify the index as follows: \begin{itemize} \item An \emph{ordinary} clause meets no root; leave all its contents hidden. \item A \emph{test} clause meets exactly one root, whose literal is true under $w$; leave its two nonroot literals hidden. \item For every other clause, reveal all its remaining contents. \end{itemize} Let $\cE$ be the sigma-field of this exposure, including the information at future indices. → `exposureSigma` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:335`)
- definition of the paper: Let $Z$ count the exposed indices meeting at least one root, and let $V$ count those meeting at least two roots. → `exposureCounts` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:372`)
- definition of the paper: Set $d=\max\{1,Z\}$. → `incidenceParam` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:382`)
- definition of the paper: For $i\le m\le L$, define \begin{align*} \cG_m&=\cE\vee\sigma(\text{ordinary contents through index }m),\\ \cH_m&=\cG_m\vee\sigma(\text{test parts through index }m). \end{align*} → `ordinaryFiltration` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:408`)
- definition of the paper: Finally, put \begin{equation} p_m=q_d(S_m). \label{eq:p} \end{equation} → `killProcess` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:436`)
- definition of the paper: For $j\ge0$, define $q_j(S)$ as the probability that $j$ independent random proper 2-clauses \emph{kill} $S$, meaning that no member of $S$ satisfies them all. → `killProb` (`lean/Papers/OaiLinearVarianceRandom/Helpers/AssignmentSets.lean:91`)
- condition of the paper: For $i\le m<L$ → `DurationTime` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:48`)
- definition of the paper: With $K=7$ → `occupationK` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:444`)
- definition of the paper: Set $\beta=3/2$ for the rest of the paper. → `beta` (`lean/Papers/OaiLinearVarianceRandom/Helpers/AssignmentSets.lean:163`)
- condition of the paper: Independent collections are sampled with replacement. → `SampledWithReplacement` (`lean/Papers/OaiLinearVarianceRandom/Helpers/AssignmentSets.lean:67`)
- condition of the paper: For $1\le i\le L$ → `DelayIndex` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:55`)

## Proposition 4.3

**Statement.** \label{prop:delay} For every $1\le i\le L$, \begin{equation} \E[D_i^2\mid\cE] \le 2K^2d^3\ind_{\{V=0\}} +2KLd^{3/2}\ind_{\{V=1\}} +L^2\ind_{\{V\ge2\}}. \label{eq:delay-bound} \end{equation}

**Lean.** `Papers.OaiLinearVarianceRandom.condExp_delay_sq_le` — `lean/Papers/OaiLinearVarianceRandom/TDelay.lean:25`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| For every $1\le i\le L$, | `i : ℕ`<br>`hi : DelayIndex i (capL n)` |
| \begin{equation} \E[D_i^2\mid\cE] \le 2K^2d^3\ind_{\{V=0\}} +2KLd^{3/2}\ind_{\{V=1\}} +L^2\ind_{\{V\ge2\}}. \end{equation} | then `((fixedClauseMeasure μ Cseq i c0)[ (fun ω => (delay (fun j => Cseq j ω) i : ℝ) ^ 2) | exposureSigma c0 Cseq i]) ≤ᵐ[fixedClauseMeasure μ Cseq i c0] (fun ω => 2 * occupationK ^ 2 * (incidenceParam c0 Cseq i ω : ℝ) ^ 3 * (if collisionCount c0 Cseq i ω = 0 then 1 else 0) + 2 * occupationK * capL n * (incidenceParam c0 Cseq i ω : ℝ) ^ beta * (if collisionCount c0 Cseq i ω = 1 then 1 else 0) + (capL n : ℝ) ^ 2 * (if 2 ≤ collisionCount c0 Cseq i ω then 1 else 0))` |

Lean also declares what the paper leaves implicit (the objects and their types): `n : ℕ`, `Ω : Type`, `MeasurableSpace Ω`, `μ : Measure Ω`, `IsProbabilityMeasure μ`, `Cseq : ℕ → Ω → ProperClause n`, `c0 : ProperClause n`.

Lean assumes conditions that the paper's text does not state: `hn : OmissionN n`, `hlaw : IsUniformClauseProcess μ Cseq`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: Assume $n\ge6$ → `OmissionN` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:162`)
- condition of the paper: Let $C_1,C_2,\ldots$ be independent clauses, each uniform among the $8\binom n3$ proper 3-clauses. → `IsUniformClauseProcess` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:172`)
- condition of the paper: Throughout, a random proper $a$-clause on a specified variable set is uniform over the clauses using $a$ distinct variables and independent fair signs. → `OneClauseLaw` (`lean/Papers/OaiLinearVarianceRandom/Helpers/AssignmentSets.lean:48`)
- definition of the paper: Write \[ F_m=\bigwedge_{j=1}^m C_j,\qquad H_n=\min\{m\ge1:F_m\text{ is unsatisfiable}\}, \] where $F_0$ is the empty, satisfiable formula. → `hittingTime` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:199`)
- definition of the paper: set $L=10n$, and let $T=\min(H_n,L)$. → `cappedTime` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:210`)
- definition of the paper: For $1\le i\le L$, omit $C_i$ while retaining the original indices: \[ B_m^{(i)}=\bigwedge_{\substack{1\le j\le m\\j\ne i}} C_j. \] → `omittedPrefixSat` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:287`)
- definition of the paper: Let $T^{(i)}$ be the first index at which this omitted-clause process is unsatisfiable, capped at $L$, and set $D_i=T^{(i)}-T\ge0$. → `omittedCappedTime` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:295`)
- definition of the paper: Write $B_m=B_m^{(i)}$. → `omittedPrefixSatAt` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:76`)
- definition of the paper: Call the three variables of $C_i$ the \emph{roots}, denote their set by $R$, and let $w\in\{0,1\}^R$ be the unique root assignment falsifying $C_i$. → `roots` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:83`)
- definition of the paper: There are $u=n-3\ge3$ nonroot variables. → `nonrootCount` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:142`)
- definition of the paper: For $i\le m<L$, define \begin{equation} A_m=\{B_m\text{ is satisfiable and }B_m\wedge C_i \text{ is unsatisfiable}\} =\{T\le m<T^{(i)}\}. \label{eq:A} \end{equation} → `pivotalEvent` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:187`)
- definition of the paper: For $i\le m\le L$, let $S_m\subseteq\{0,1\}^u$ consist of the nonroot assignments that, together with $w$, satisfy $B_m$. → `nonrootSolutions` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:292`)
- definition of the paper: For every index $j\le L$ other than $i$, first reveal the subset of $R$ met by $C_j$ and all signs on that subset. Classify the index as follows: \begin{itemize} \item An \emph{ordinary} clause meets no root; leave all its contents hidden. \item A \emph{test} clause meets exactly one root, whose literal is true under $w$; leave its two nonroot literals hidden. \item For every other clause, reveal all its remaining contents. \end{itemize} Let $\cE$ be the sigma-field of this exposure, including the information at future indices. → `exposureSigma` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:335`)
- definition of the paper: Let $Z$ count the exposed indices meeting at least one root, and let $V$ count those meeting at least two roots. → `exposureCounts` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:372`)
- definition of the paper: Set $d=\max\{1,Z\}$. → `incidenceParam` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:382`)
- definition of the paper: For $i\le m\le L$, define \begin{align*} \cG_m&=\cE\vee\sigma(\text{ordinary contents through index }m),\\ \cH_m&=\cG_m\vee\sigma(\text{test parts through index }m). \end{align*} → `ordinaryFiltration` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:408`)
- definition of the paper: Finally, put \begin{equation} p_m=q_d(S_m). \label{eq:p} \end{equation} → `killProcess` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:436`)
- definition of the paper: For $j\ge0$, define $q_j(S)$ as the probability that $j$ independent random proper 2-clauses \emph{kill} $S$, meaning that no member of $S$ satisfies them all. → `killProb` (`lean/Papers/OaiLinearVarianceRandom/Helpers/AssignmentSets.lean:91`)
- condition of the paper: For $1\le i\le L$ → `DelayIndex` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:55`)
- definition of the paper: \begin{equation} D_i=\sum_{m=i}^{L-1}\ind_{A_m}. \label{eq:delay} \end{equation} → `delayIndicatorSum` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:231`)
- definition of the paper: With $K=7$ → `occupationK` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:444`)
- definition of the paper: Set $\beta=3/2$ for the rest of the paper. → `beta` (`lean/Papers/OaiLinearVarianceRandom/Helpers/AssignmentSets.lean:163`)
- condition of the paper: Independent collections are sampled with replacement. → `SampledWithReplacement` (`lean/Papers/OaiLinearVarianceRandom/Helpers/AssignmentSets.lean:67`)

## Lemma 4.4

**Statement.** \label{lem:moments} Uniformly in $n\ge6$, $i$, and the fixed value of $C_i$, \begin{equation} \E d^3=O(1),\qquad \E[d^{3/2}\ind_{\{V\ge1\}}]=O(n^{-1}),\qquad \Prb(V\ge2)=O(n^{-2}). \label{eq:moments} \end{equation}

**Lean.** `Papers.OaiLinearVarianceRandom.incidence_moments_bound` — `lean/Papers/OaiLinearVarianceRandom/Helpers/Moments.lean:292`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| Uniformly in $n\ge6$, $i$, | `∀ n : ℕ`<br>`OmissionN n`<br>`∀ i : ℕ` |
| and the fixed value of $C_i$, | `∀ c0 : ProperClause n` |
| \begin{equation} \E d^3=O(1),\qquad | then `∃ A : ℝ,`<br>then `0 < A`<br>then `(∫ ω, (incidenceParam c0 Cseq i ω : ℝ) ^ 3 ∂(fixedClauseMeasure μ Cseq i c0)) ≤ A` |
| \E[d^{3/2}\ind_{\{V\ge1\}}]=O(n^{-1}),\qquad | then `∃ A : ℝ,`<br>then `0 < A`<br>then `(∫ ω, (incidenceParam c0 Cseq i ω : ℝ) ^ beta * (if 1 ≤ collisionCount c0 Cseq i ω then 1 else 0) ∂(fixedClauseMeasure μ Cseq i c0)) ≤ A / n` |
| \Prb(V\ge2)=O(n^{-2}). \end{equation} | then `∃ A : ℝ,`<br>then `0 < A`<br>then `(fixedClauseMeasure μ Cseq i c0).real {ω | 2 ≤ collisionCount c0 Cseq i ω} ≤ A / (n : ℝ) ^ 2` |

Lean also declares what the paper leaves implicit (the objects and their types): `Ω : Type`, `MeasurableSpace Ω`, `μ : Measure Ω`, `IsProbabilityMeasure μ`, `Cseq : ℕ → Ω → ProperClause n`.

Lean assumes conditions that the paper's text does not state: `MomentsRange n i`, `IsUniformClauseProcess μ Cseq`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: Assume $n\ge6$ → `OmissionN` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:162`)
- condition of the paper: Uniformly in $n\ge6$, $i$, and the fixed value of $C_i$, → `MomentsRange` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:65`)
- condition of the paper: Let $C_1,C_2,\ldots$ be independent clauses, each uniform among the $8\binom n3$ proper 3-clauses. → `IsUniformClauseProcess` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:172`)
- definition of the paper: Write \[ F_m=\bigwedge_{j=1}^m C_j,\qquad H_n=\min\{m\ge1:F_m\text{ is unsatisfiable}\}, \] where $F_0$ is the empty, satisfiable formula. → `hittingTime` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:199`)
- definition of the paper: set $L=10n$, and let $T=\min(H_n,L)$. → `cappedTime` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:210`)
- definition of the paper: Call the three variables of $C_i$ the \emph{roots}, denote their set by $R$, and let $w\in\{0,1\}^R$ be the unique root assignment falsifying $C_i$. → `roots` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:83`)
- definition of the paper: For every index $j\le L$ other than $i$, first reveal the subset of $R$ met by $C_j$ and all signs on that subset. Classify the index as follows: \begin{itemize} \item An \emph{ordinary} clause meets no root; leave all its contents hidden. \item A \emph{test} clause meets exactly one root, whose literal is true under $w$; leave its two nonroot literals hidden. \item For every other clause, reveal all its remaining contents. \end{itemize} Let $\cE$ be the sigma-field of this exposure, including the information at future indices. → `exposureSigma` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:335`)
- definition of the paper: Let $Z$ count the exposed indices meeting at least one root, and let $V$ count those meeting at least two roots. → `exposureCounts` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:372`)
- definition of the paper: Set $d=\max\{1,Z\}$. → `incidenceParam` (`lean/Papers/OaiLinearVarianceRandom/Helpers/RootExposure.lean:382`)

## Theorem 5.1

**Statement.** \label{thm:wilson} Fix $1>p_1>p_2>0$. There is a constant $a(p_1,p_2)>0$ such that, for all sufficiently large $n$, if integers $m_1,m_2$ satisfy $s_n(m_1)\ge p_1$ and $s_n(m_2)\le p_2$, then \[ m_2-m_1\ge a(p_1,p_2)\sqrt n. \]

**Lean.** no declaration

**Status.** taken from the literature as cited; not proved here.

**Taken from the literature: Wilson2002, Corollary 4.**

What Lean assumes for it: `Papers.OaiLinearVarianceRandom.WilsonSeparation` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:556`)

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

## Corollary 5.2

**Statement.** \label{cor:window} For every fixed $0<\eta<1/2$, \[ r_n(\eta)-r_n(1-\eta)=\Theta_\eta(\sqrt n). \]

**Lean.** `Papers.OaiLinearVarianceRandom.levelLocation_window_theta_sqrt` — `lean/Papers/OaiLinearVarianceRandom/TWindow.lean:30`

**Status.** proved in Lean, given 1 cited result(s). **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| For every fixed $0<\eta<1/2$, | `∀ η : ℝ`<br>`WindowEta η` |
| \[ r_n(\eta)-r_n(1-\eta)=\Theta_\eta(\sqrt n). \] | then `∃ c1 : ℝ,`<br>then `0 < c1`<br>then `∃ c2 : ℝ,`<br>then `0 < c2`<br>then `∃ N : ℕ,`<br>`∀ n : ℕ`<br>`N ≤ n`<br>then `c1 * Real.sqrt n ≤ (levelLocation μ H η : ℝ) - (levelLocation μ H (1 - η) : ℝ)`<br>then `(levelLocation μ H η : ℝ) - (levelLocation μ H (1 - η) : ℝ) ≤ c2 * Real.sqrt n` |

Lean also declares what the paper leaves implicit (the objects and their types): `Ω : Type`, `MeasurableSpace Ω`, `μ : Measure Ω`, `IsProbabilityMeasure μ`, `Cseq : ℕ → Ω → ProperClause n`, `let H := fun ω => hittingTime (fun j => Cseq j ω)`.

Lean assumes conditions that the paper's text does not state: `hWilson_of_gate : WilsonSeparation`, `MainN n`, `IsUniformClauseProcess μ Cseq`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: Fix an integer $n\ge3$. → `MainN` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:158`)
- condition of the paper: Let $C_1,C_2,\ldots$ be independent clauses, each uniform among the $8\binom n3$ proper 3-clauses. → `IsUniformClauseProcess` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:172`)
- condition of the paper: For every fixed $0<\eta<1/2$ → `WindowEta` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:539`)
- definition of the paper: Write \[ F_m=\bigwedge_{j=1}^m C_j,\qquad H_n=\min\{m\ge1:F_m\text{ is unsatisfiable}\}, \] where $F_0$ is the empty, satisfiable formula. → `hittingTime` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:199`)
- definition of the paper: Define the survival function and its integer level locations by \[ s_n(m)=\Prb(H_n>m),\qquad r_n(p)=\min\{m\ge0:s_n(m)\le p\}\quad(0<p<1). \] → `survivalLevels` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:512`)

**Taken from the literature: Wilson2002, Corollary 4.**

What Lean assumes for it: `Papers.OaiLinearVarianceRandom.WilsonSeparation` (`lean/Papers/OaiLinearVarianceRandom/Basic.lean:556`)

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

## Identifiers

| Result | run id | paper label | source | Lean declaration |
| --- | --- | --- | --- | --- |
| Theorem 1.1 | `thm:main` | `thm:main` | `main.tex:61-70` | `Papers.OaiLinearVarianceRandom.var_hittingTime_theta_n` |
| Lemma 2.1 | `lem:one` | `lem:one` | `main.tex:179-187` | `Papers.OaiLinearVarianceRandom.oneKillProb_two_rpow_le` |
| Lemma 2.2 | `lem:potential` | `lem:potential` | `main.tex:216-231` | `Papers.OaiLinearVarianceRandom.potential_drift` |
| Lemma 3.1 | `lem:omission` | `lem:omission` | `main.tex:284-291` | `Papers.OaiLinearVarianceRandom.variance_cappedTime_le_sum_delay_sq` |
| Lemma 3.2 | `lem:tests` | `lem:tests` | `main.tex:382-392` | `Papers.OaiLinearVarianceRandom.condProb_pivotal_le` |
| Lemma 4.1 | `lem:occupation` | `lem:occupation` | `main.tex:428-437` | `Papers.OaiLinearVarianceRandom.condExp_occupation_le` |
| Corollary 4.2 | `thm:duration` | `cor:duration` | `main.tex:467-481` | `Papers.OaiLinearVarianceRandom.condExp_pivotal_duration_le` |
| Proposition 4.3 | `prop:delay` | `prop:delay` | `main.tex:496-506` | `Papers.OaiLinearVarianceRandom.condExp_delay_sq_le` |
| Lemma 4.4 | `lem:moments` | `lem:moments` | `main.tex:545-554` | `Papers.OaiLinearVarianceRandom.incidence_moments_bound` |
| Theorem 5.1 | `thm:wilson` | `thm:wilson` | `main.tex:647-655` | — |
| Corollary 5.2 | `thm:window` | `cor:window` | `main.tex:682-688` | `Papers.OaiLinearVarianceRandom.levelLocation_window_theta_sqrt` |
