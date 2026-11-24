# The corrected paper and its Lean formalization — hawkes_d75660b

For each result of the corrected paper: its statement, the Lean declaration that states it, whether that declaration is proved, and how the two statements correspond phrase by phrase. A result stated differently from the original paper is marked "corrected"; the report says what changed and why.

## Theorem 1

**Statement.** \label{meanIdThm1} Let $B \sim \mathsf{Borel}(\rho)$. Then, the mean duration of the Markovian Hawkes cluster is such that \begin{align} \E{\tau} &= \left(1-\rho\right) \E{B \cdot \mathsf{H}_B} - 1 , \end{align} where $\mathsf{H}_j = \sum_{i=1}^j 1/i$ is the $j$th Harmonic number for each $j \in \mathbb{Z}_+$.

**Lean.** `Papers.HawkesD75660b.meanDurationIdentity` — `lean/Papers/HawkesD75660b/T2.lean:27`

**Status.** proved in Lean, under 5 condition(s) made explicit. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| Let $B \sim \mathsf{Borel}(\rho)$. | `ρ : ℝ≥0`<br>`B : ΩB → ℕ`<br>`hB : auxiliaryBorelLaw ρ Q B` |
| Then, the mean duration of the Markovian Hawkes cluster is such that | `C : Ω → EpochConfiguration`<br>then `(∫ ω, (clusterDuration C ω : ℝ) ∂P) = (1 - (ρ : ℝ)) * (∫ ω, (B ω : ℝ) * harmonicNumber (B ω) ∂Q) - 1` |
| \begin{align} \E{\tau} &= \left(1-\rho\right) \E{B \cdot \mathsf{H}_B} - 1 , \end{align} | then `(∫ ω, (clusterDuration C ω : ℝ) ∂P) = (1 - (ρ : ℝ)) * (∫ ω, (B ω : ℝ) * harmonicNumber (B ω) ∂Q) - 1` |
| where $\mathsf{H}_j = \sum_{i=1}^j 1/i$ is the $j$th Harmonic number for each $j \in \mathbb{Z}_+$. | — (no Lean counterpart recorded) |

Lean also declares what the paper leaves implicit (the objects and their types): `Ω ΩB : Type*`, `MeasurableSpace Ω`, `MeasurableSpace ΩB`, `P : Measure Ω`, `IsProbabilityMeasure P`, `Q : Measure ΩB`, `IsProbabilityMeasure Q`.

Lean assumes conditions that the paper's text does not state: `hworld : hawkesClusterWorld P C ρ`, `hsubcritical : subcritical ρ`, `hcounting : clusterCountingConvention P C ρ`, `hrepresentation : durationRepresentation P C ρ`.

**Conditions and readings, and the Lean definitions that carry them.**

- reading: $\mathbb{N}=\{0,1,2,\dots\}$ in the domain $\kappa\in\mathbb{N}^n$ of Definition~\ref{def:prefs}. → `naturalCountDomainConvention` (`lean/Papers/HawkesD75660b/Basic.lean:202`)
- reading: $n\in\mathbb{Z}_+$ and $m\in\{0,\dots,n-1\}$. → `solutionIndexConvention` (`lean/Papers/HawkesD75660b/Basic.lean:210`)
- reading: $N_t=\sum_{i=0}^{N-1}\mathbf{1}\{\tau_i\leq t\}$, and the integral in \eqref{intensityDefEq} is against the cluster point measure on $[0,t]$; for $g(t)=\rho e^{-t}$, the displayed $\lambda_t$ is the right-continuous post-jump version, whose predictable intensity is $\lambda_{t-}$ for $t>0$. → `clusterCountingConvention` (`lean/Papers/HawkesD75660b/Helpers/Cluster.lean:233`)
- reading: $\mathbb{N}=\{0,1,2,\dots\}$ in the definition of preference counts. → `zeroCountConvention` (`lean/Papers/HawkesD75660b/Basic.lean:206`)
- reading: The $\tau$ constructed in Definition~\ref{def:combx-duration} has the same distribution as the cluster duration $\tau:=\tau_{N-1}$ defined from \eqref{intensityDefEq}. → `durationRepresentation` (`lean/Papers/HawkesD75660b/Helpers/Duration.lean:294`)
- condition of the paper: Accordingly, we will assume $\rho < 1$ throughout our analysis. → `subcritical` (`lean/Papers/HawkesD75660b/Basic.lean:30`)
- condition of the paper: \label{meanIdThm1} Let $B \sim \mathsf{Borel}(\rho)$. → `auxiliaryBorelLaw` (`lean/Papers/HawkesD75660b/Basic.lean:51`)
- definition of the paper: Hence, we can isolate the self-excitement to a purely history-driven \emph{Hawkes cluster model} which has the stochastic intensity and counting process pair $(\lambda_t, N_t)$ governed by \begin{align} \lambda_t &= \int_0^t g(t-u)\mathrm{d}N_u = \sum_{i=0}^{N_t-1} g(t-\tau_i) , \label{intensityDefEq} \end{align} where $g : \mathbb{R}_+ \to \mathbb{R}_+$ is the \emph{excitation kernel} and $0 = \tau_0 < \tau_1 < \tau_2 < \dots$ are the \emph{cluster points}. → `clusterIntensity` (`lean/Papers/HawkesD75660b/Helpers/Cluster.lean:59`)
- definition of the paper: If we specify $g(\cdot)$ to be $g(t) = \rho e^{-t}$ for some $\rho \in \mathbb{R}_+$, then we receive the cluster model for the \textit{Markovian Hawkes process}, which is likely the most widely used and well-studied form of self-excitement \citep{oakes1975markovian}. → `markovianKernel` (`lean/Papers/HawkesD75660b/Basic.lean:37`)
- definition of the paper: $N := \lim_{t \to \infty} N_t$ → `clusterSize` (`lean/Papers/HawkesD75660b/Helpers/Cluster.lean:73`)
- definition of the paper: the \emph{duration} of the cluster $\tau := \tau_{N-1}$ → `clusterDuration` (`lean/Papers/HawkesD75660b/Helpers/Cluster.lean:79`)
- definition of the paper: where $\mathsf{H}_j = \sum_{i=1}^j 1/i$ is the $j$th Harmonic number for each $j \in \mathbb{Z}_+$. → `harmonicNumber` (`lean/Papers/HawkesD75660b/Basic.lean:223`)
- definition of the paper: \label{def:combx-duration} Let $\tau \geq 0$ be constructed as follows: \begin{enumerate}[i)] \item Sample $N \sim \mathrm{Borel}(\rho)$ as the \emph{size} of the cluster. If $N=1$, then $\tau = 0$. \item Given $N = n + 1$ for $n \in \mathbb{Z}_+$, sample a length-$n$ preference count $\kappa$ according to the distribution \begin{align} \PP{\kappa_1 = k_1, \dots, \kappa_n = k_n} &= \frac{1}{(n+1)^{n-1}}{n \choose k_1, \dots, k_n} = \frac{n!}{(n+1)^{n-1}\prod_{i=1}^n k_i !} . \label{kappaDist} \end{align} \item Given $\kappa$ with cumulative form $\kappa^+$, sample $Z_i \sim \mathrm{Exp}(\kappa^+_i -i + 1)$ independently for each $i \in \{1, \dots, n\}$. \end{enumerate} Then, let $\tau := \sum_{i=1}^{N-1} Z_i$ be the \emph{combinatorially constructed cluster duration}. \hfill \Halmos → `combinatorialDuration` (`lean/Papers/HawkesD75660b/Helpers/Duration.lean:61`)

## Corollary 1

**Statement.** \label{corIdThm1} The mean duration of the Markovian Hawkes cluster is given by \begin{align} \E{\tau} &= \int_0^\rho \frac{e^{-u} - e^{-\rho}}{\rho e^{-\rho} - u e^{-u}}\mathrm{d}u . \end{align}

**Lean.** `Papers.HawkesD75660b.meanDurationIntegral` — `lean/Papers/HawkesD75660b/T3.lean:28`

**Status.** proved in Lean, under 6 condition(s) made explicit. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| The mean duration of the Markovian Hawkes cluster is given by | `C : Ω → EpochConfiguration`<br>then `(∫ ω, (clusterDuration C ω : ℝ) ∂P) = ∫ u in (0 : ℝ)..(ρ : ℝ), durationIntegrand ρ u` |
| \begin{align} \E{\tau} &= \int_0^\rho \frac{e^{-u} - e^{-\rho}}{\rho e^{-\rho} - u e^{-u}}\mathrm{d}u . \end{align} | `ρ : ℝ≥0`<br>then `(∫ ω, (clusterDuration C ω : ℝ) ∂P) = ∫ u in (0 : ℝ)..(ρ : ℝ), durationIntegrand ρ u` |

Lean also declares what the paper leaves implicit (the objects and their types): `Ω ΩB : Type*`, `MeasurableSpace Ω`, `MeasurableSpace ΩB`, `P : Measure Ω`, `IsProbabilityMeasure P`, `Q : Measure ΩB`, `IsProbabilityMeasure Q`, `B : ΩB → ℕ`.

Lean assumes conditions that the paper's text does not state: `hworld : hawkesClusterWorld P C ρ`, `hsubcritical : subcritical ρ`, `hB : auxiliaryBorelLaw ρ Q B`, `hendpoint : continuousEndpointConvention ρ`, `hcounting : clusterCountingConvention P C ρ`, `hrepresentation : durationRepresentation P C ρ`.

**Conditions and readings, and the Lean definitions that carry them.**

- reading: The integrand $\frac{e^{-u}-e^{-\rho}}{\rho e^{-\rho}-u e^{-u}}$ is interpreted by its continuous extension at $u=\rho$, with value $1/(1-\rho)$. → `continuousEndpointConvention` (`lean/Papers/HawkesD75660b/Helpers/Integral.lean:34`)
- reading: $\mathbb{N}=\{0,1,2,\dots\}$ in the domain $\kappa\in\mathbb{N}^n$ of Definition~\ref{def:prefs}. → `naturalCountDomainConvention` (`lean/Papers/HawkesD75660b/Basic.lean:202`)
- reading: $n\in\mathbb{Z}_+$ and $m\in\{0,\dots,n-1\}$. → `solutionIndexConvention` (`lean/Papers/HawkesD75660b/Basic.lean:210`)
- reading: $N_t=\sum_{i=0}^{N-1}\mathbf{1}\{\tau_i\leq t\}$, and the integral in \eqref{intensityDefEq} is against the cluster point measure on $[0,t]$; for $g(t)=\rho e^{-t}$, the displayed $\lambda_t$ is the right-continuous post-jump version, whose predictable intensity is $\lambda_{t-}$ for $t>0$. → `clusterCountingConvention` (`lean/Papers/HawkesD75660b/Helpers/Cluster.lean:233`)
- reading: $\mathbb{N}=\{0,1,2,\dots\}$ in the definition of preference counts. → `zeroCountConvention` (`lean/Papers/HawkesD75660b/Basic.lean:206`)
- reading: The $\tau$ constructed in Definition~\ref{def:combx-duration} has the same distribution as the cluster duration $\tau:=\tau_{N-1}$ defined from \eqref{intensityDefEq}. → `durationRepresentation` (`lean/Papers/HawkesD75660b/Helpers/Duration.lean:294`)
- condition of the paper: Accordingly, we will assume $\rho < 1$ throughout our analysis. → `subcritical` (`lean/Papers/HawkesD75660b/Basic.lean:30`)
- condition of the paper: \label{meanIdThm1} Let $B \sim \mathsf{Borel}(\rho)$. → `auxiliaryBorelLaw` (`lean/Papers/HawkesD75660b/Basic.lean:51`)
- definition of the paper: Hence, we can isolate the self-excitement to a purely history-driven \emph{Hawkes cluster model} which has the stochastic intensity and counting process pair $(\lambda_t, N_t)$ governed by \begin{align} \lambda_t &= \int_0^t g(t-u)\mathrm{d}N_u = \sum_{i=0}^{N_t-1} g(t-\tau_i) , \label{intensityDefEq} \end{align} where $g : \mathbb{R}_+ \to \mathbb{R}_+$ is the \emph{excitation kernel} and $0 = \tau_0 < \tau_1 < \tau_2 < \dots$ are the \emph{cluster points}. → `clusterIntensity` (`lean/Papers/HawkesD75660b/Helpers/Cluster.lean:59`)
- definition of the paper: If we specify $g(\cdot)$ to be $g(t) = \rho e^{-t}$ for some $\rho \in \mathbb{R}_+$, then we receive the cluster model for the \textit{Markovian Hawkes process}, which is likely the most widely used and well-studied form of self-excitement \citep{oakes1975markovian}. → `markovianKernel` (`lean/Papers/HawkesD75660b/Basic.lean:37`)
- definition of the paper: the \emph{duration} of the cluster $\tau := \tau_{N-1}$ → `clusterDuration` (`lean/Papers/HawkesD75660b/Helpers/Cluster.lean:79`)
- definition of the paper: where $\mathsf{H}_j = \sum_{i=1}^j 1/i$ is the $j$th Harmonic number for each $j \in \mathbb{Z}_+$. → `harmonicNumber` (`lean/Papers/HawkesD75660b/Basic.lean:223`)

## Lemma 1

**Statement.** \label{kappaCPMF1} For $n \in \mathbb{Z}_+$, let $\kappa$ be a length-$n$ preference count with distribution given by~\eqref{kappaDist}. Then, the conditional distribution of $\kappa_{m+1}$ given $\kappa_1$ through $\kappa_m$ has probability mass function (PMF) given by \begin{align} \PP{\kappa_{m+1} = k_{m+1} \mid \kappa_1 = k_1, \dots, \kappa_m = k_m} &= \frac{k_{m+1}^+ - m}{k_m^+ - m + 1} {n - k_m^+ \choose k_{m+1}} \frac{\left(n-m\right)^{n-k_{m+1}^+-1}}{(n-m+1)^{n-k_m^+-1}} , \end{align} for each $m < n$, meaning that $\kappa_{m+1} | (\kappa_1, \dots, \kappa_m) \stackrel{\mathsf{D}}{=} X_m + Y_m$, where, given $\kappa_m^+$, \begin{align} X_m | Y_m \sim \mathsf{Bin}\left( n - \kappa_m^+ - Y_m , \frac{1}{n-m+1} \right) \qquad \text{ and } \qquad Y_m \sim \mathsf{Bern}\left(\frac{n-\kappa_m^+}{(n-m)(\kappa_m^+ - m + 1)} \right) , \end{align} with $(\kappa_1 - 1) \sim \mathsf{Bin}\left(n-1, 1/(n+1)\right)$.

**Lean.** `Papers.HawkesD75660b.conditionalPreferenceCountLaw` — `lean/Papers/HawkesD75660b/Helpers/ConditionalCounts.lean:32`

**Status.** proved in Lean, under 2 condition(s) made explicit. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| For $n \in \mathbb{Z}_+$, let $\kappa$ be a length-$n$ preference count with distribution given by~\eqref{kappaDist}. | `n : ℕ`<br>`κ : Ω → CountVector n`<br>`hindex : kappaCPMFIndex n`<br>`hlaw : kappaCPMFLaw P κ` |
| Then, the conditional distribution of $\kappa_{m+1}$ given $\kappa_1$ through $\kappa_m$ has probability mass function (PMF) given by | then `(ProbabilityTheory.cond P (countPrefixEvent κ m k)).real {ω | κ ω ⟨m, hm⟩ = v} = conditionalCountMass n m s v` |
| \begin{align} \PP{\kappa_{m+1} = k_{m+1} \mid \kappa_1 = k_1, \dots, \kappa_m = k_m} &= \frac{k_{m+1}^+ - m}{k_m^+ - m + 1} {n - k_m^+ \choose k_{m+1}} \frac{\left(n-m\right)^{n-k_{m+1}^+-1}}{(n-m+1)^{n-k_m^+-1}} , \end{align} | `∀ k : CountVector n`<br>`∀ v : ℕ`<br>then `(ProbabilityTheory.cond P (countPrefixEvent κ m k)).real {ω | κ ω ⟨m, hm⟩ = v} = conditionalCountMass n m s v` |
| for each $m < n$, meaning that $\kappa_{m+1} \| (\kappa_1, \dots, \kappa_m) \stackrel{\mathsf{D}}{=} X_m + Y_m$, | `∀ m : ℕ`<br>`∀ hm : m < n`<br>then `IdentDistrib (fun ω => κ ω ⟨m, hm⟩) (fun q : ℕ × ℕ => q.1 + q.2) (ProbabilityTheory.cond P (countPrefixEvent κ m k)) (auxiliaryCountLaw n m s)` |
| where, given $\kappa_m^+$, | then `HasLaw Prod.snd (bernoulliNat (bernoulliParameter n m s)) (auxiliaryCountLaw n m s)`<br>then `HasLaw Prod.fst (ProbabilityTheory.binomial (n - s - y) (reciprocalProbability (n - m))) (ProbabilityTheory.cond (auxiliaryCountLaw n m s) {q | q.2 = y})` |
| \begin{align} X_m \| Y_m \sim \mathsf{Bin}\left( n - \kappa_m^+ - Y_m , \frac{1}{n-m+1} \right) \qquad \text{ and } \qquad | `∀ y : ℕ`<br>then `HasLaw Prod.fst (ProbabilityTheory.binomial (n - s - y) (reciprocalProbability (n - m))) (ProbabilityTheory.cond (auxiliaryCountLaw n m s) {q | q.2 = y})` |
| Y_m \sim \mathsf{Bern}\left(\frac{n-\kappa_m^+}{(n-m)(\kappa_m^+ - m + 1)} \right) , \end{align} | then `HasLaw Prod.snd (bernoulliNat (bernoulliParameter n m s)) (auxiliaryCountLaw n m s)` |
| with $(\kappa_1 - 1) \sim \mathsf{Bin}\left(n-1, 1/(n+1)\right)$. | then `HasLaw (fun ω => κ ω ⟨0, hindex⟩ - 1) (ProbabilityTheory.binomial (n - 1) (reciprocalProbability n)) P` |

Lean also declares what the paper leaves implicit (the objects and their types): `Ω : Type*`, `MeasurableSpace Ω`, `P : Measure Ω`, `IsProbabilityMeasure P`, `let s := prefixCount k m`.

Lean assumes conditions that the paper's text does not state: `hdomain : naturalCountDomainConvention`, `hzero : zeroCountConvention`, `1 ≤ m`, `0 < P (countPrefixEvent κ m k)`, `v ≤ n - s`, `m + 1 ≤ s + v`, `0 < auxiliaryCountLaw n m s {q | q.2 = y}`.

**Conditions and readings, and the Lean definitions that carry them.**

- reading: $\mathbb{N}=\{0,1,2,\dots\}$ in the domain $\kappa\in\mathbb{N}^n$ of Definition~\ref{def:prefs}. → `naturalCountDomainConvention` (`lean/Papers/HawkesD75660b/Basic.lean:202`)
- reading: $\mathbb{N}=\{0,1,2,\dots\}$ in the definition of preference counts. → `zeroCountConvention` (`lean/Papers/HawkesD75660b/Basic.lean:206`)
- definition of the paper: \label{def:prefs} For $n \in \mathbb{Z}_+$, $\kappa \in \mathbb{N}^n$ is a vector of \emph{preference counts} if and only if $\sum_{i=1}^n \kappa_i = n$ and $\sum_{j=1}^i \kappa_j \ge i$ for $i \in \{1, \dots, n\}$. → `PreferenceCounts` (`lean/Papers/HawkesD75660b/Basic.lean:124`)
- definition of the paper: Likewise, $\kappa^+ \in \mathbb{Z}^n$ is a vector of \emph{cumulative preference counts} if and only if $1 \leq \kappa_1^+ \leq \dots \leq \kappa_n^+ \leq n$ and $\kappa^+_i \geq i$ for $i \in \{1, \dots, n\}$, where the bijection $\kappa_i^+ = \sum_{j=1}^i \kappa_j$ for $i \in \{1,\dots,n\}$ connects the two concepts. → `CumulativePreferenceCounts` (`lean/Papers/HawkesD75660b/Basic.lean:141`)
- definition of the paper: where the bijection $\kappa_i^+ = \sum_{j=1}^i \kappa_j$ for $i \in \{1,\dots,n\}$ connects the two concepts. → `cumulativePreferenceCounts` (`lean/Papers/HawkesD75660b/Basic.lean:148`)
- definition of the paper: \begin{align} \PP{\kappa_1 = k_1, \dots, \kappa_n = k_n} &= \frac{1}{(n+1)^{n-1}}{n \choose k_1, \dots, k_n} = \frac{n!}{(n+1)^{n-1}\prod_{i=1}^n k_i !} . \label{kappaDist} \end{align} → `preferenceCountMass` (`lean/Papers/HawkesD75660b/Basic.lean:161`)
- condition of the paper: For $n \in \mathbb{Z}_+$, → `kappaCPMFIndex` (`lean/Papers/HawkesD75660b/Basic.lean:174`)
- condition of the paper: with distribution given by~\eqref{kappaDist}. → `kappaCPMFLaw` (`lean/Papers/HawkesD75660b/Basic.lean:187`)
- definition of the paper: \label{gpfDef1} For $m, n \in \mathbb{Z}_+$ with $m \leq n$, $\pi \in \mathbb{Z}_+^m$ is a \emph{generalized parking function} of length $m$ over $n$ preferences if and only if it is such that, when sorted such that $\pi_{(1)} \leq \dots \leq \pi_{(m)}$, each $\pi_{(i)} \leq n - m + i$ for $i \in \{1, \dots, m\}$.\hfill \Halmos → `GeneralizedParkingFunction` (`lean/Papers/HawkesD75660b/Basic.lean:88`)
- definition of the paper: A ``classic'' parking function is obtained when $m = n$. → `ClassicParkingFunction` (`lean/Papers/HawkesD75660b/Basic.lean:98`)
- definition of the paper: the vector defined component-wise by $\kappa_i(\pi) = |\{\ell : \pi_\ell = i \}|$ → `preferenceCountsOfParking` (`lean/Papers/HawkesD75660b/Basic.lean:155`)

## Lemma 2

**Statement.** \label{meanRecur1} For $n \in \mathbb{Z}_+$, let $\kappa$ be a length-$n$ preference count with distribution given by~\eqref{kappaDist}. Then, for each $m \in \{0, 1, \dots, n - 1\}$, \begin{align} \E{\frac{1}{\kappa_{m+1}^+ - m} } &= \left(1 + \frac{1}{n-m}\right)\E{\frac{1}{\kappa_m^+ - m + 1}} - {n \choose m}\frac{(m+1)^{m-1}}{(n+1)^{n-1}}(n-m)^{n-m-1} , \end{align} where $\PP{\kappa_0^+ = 0} = 1$.

**Lean.** `Papers.HawkesD75660b.meanRecurrence` — `lean/Papers/HawkesD75660b/Helpers/MeanRecurrence.lean:445`

**Status.** proved in Lean, under 2 condition(s) made explicit. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| For $n \in \mathbb{Z}_+$, let $\kappa$ be a length-$n$ preference count with distribution given by~\eqref{kappaDist}. | `n : ℕ`<br>`κ : Ω → CountVector n`<br>`hindex : meanRecurrenceIndex n`<br>`hlaw : meanRecurrenceLaw P κ` |
| Then, for each $m \in \{0, 1, \dots, n - 1\}$, | `∀ m : ℕ`<br>`m < n` |
| \begin{align} \E{\frac{1}{\kappa_{m+1}^+ - m} } &= \left(1 + \frac{1}{n-m}\right)\E{\frac{1}{\kappa_m^+ - m + 1}} - {n \choose m}\frac{(m+1)^{m-1}}{(n+1)^{n-1}}(n-m)^{n-m-1} , \end{align} | then `(∫ ω, 1 / ((prefixCount (κ ω) (m + 1) : ℝ) - m) ∂P) = (1 + 1 / ((n : ℝ) - m)) * (∫ ω, 1 / ((prefixCount (κ ω) m : ℝ) - m + 1) ∂P) - (Nat.choose n m : ℝ) * ((m + 1 : ℝ) ^ ((m : ℤ) - 1) / (n + 1 : ℝ) ^ ((n : ℤ) - 1)) * ((n : ℝ) - m) ^ ((n : ℤ) - m - 1)` |
| where $\PP{\kappa_0^+ = 0} = 1$. | — (no Lean counterpart recorded) |

Lean also declares what the paper leaves implicit (the objects and their types): `Ω : Type*`, `MeasurableSpace Ω`, `P : Measure Ω`, `IsProbabilityMeasure P`.

Lean assumes conditions that the paper's text does not state: `hdomain : naturalCountDomainConvention`, `hzero : zeroCountConvention`.

**Conditions and readings, and the Lean definitions that carry them.**

- reading: $\mathbb{N}=\{0,1,2,\dots\}$ in the domain $\kappa\in\mathbb{N}^n$ of Definition~\ref{def:prefs}. → `naturalCountDomainConvention` (`lean/Papers/HawkesD75660b/Basic.lean:202`)
- reading: $\mathbb{N}=\{0,1,2,\dots\}$ in the definition of preference counts. → `zeroCountConvention` (`lean/Papers/HawkesD75660b/Basic.lean:206`)
- definition of the paper: \label{def:prefs} For $n \in \mathbb{Z}_+$, $\kappa \in \mathbb{N}^n$ is a vector of \emph{preference counts} if and only if $\sum_{i=1}^n \kappa_i = n$ and $\sum_{j=1}^i \kappa_j \ge i$ for $i \in \{1, \dots, n\}$. → `PreferenceCounts` (`lean/Papers/HawkesD75660b/Basic.lean:124`)
- definition of the paper: Likewise, $\kappa^+ \in \mathbb{Z}^n$ is a vector of \emph{cumulative preference counts} if and only if $1 \leq \kappa_1^+ \leq \dots \leq \kappa_n^+ \leq n$ and $\kappa^+_i \geq i$ for $i \in \{1, \dots, n\}$, where the bijection $\kappa_i^+ = \sum_{j=1}^i \kappa_j$ for $i \in \{1,\dots,n\}$ connects the two concepts. → `CumulativePreferenceCounts` (`lean/Papers/HawkesD75660b/Basic.lean:141`)
- definition of the paper: where the bijection $\kappa_i^+ = \sum_{j=1}^i \kappa_j$ for $i \in \{1,\dots,n\}$ connects the two concepts. → `cumulativePreferenceCounts` (`lean/Papers/HawkesD75660b/Basic.lean:148`)
- definition of the paper: \begin{align} \PP{\kappa_1 = k_1, \dots, \kappa_n = k_n} &= \frac{1}{(n+1)^{n-1}}{n \choose k_1, \dots, k_n} = \frac{n!}{(n+1)^{n-1}\prod_{i=1}^n k_i !} . \label{kappaDist} \end{align} → `preferenceCountMass` (`lean/Papers/HawkesD75660b/Basic.lean:161`)
- condition of the paper: For $n \in \mathbb{Z}_+$, → `meanRecurrenceIndex` (`lean/Papers/HawkesD75660b/Basic.lean:178`)
- condition of the paper: with distribution given by~\eqref{kappaDist}. → `meanRecurrenceLaw` (`lean/Papers/HawkesD75660b/Basic.lean:192`)
- definition of the paper: where $\PP{\kappa_0^+ = 0} = 1$. → `zeroCumulativeCount` (`lean/Papers/HawkesD75660b/Basic.lean:214`)
- definition of the paper: A ``classic'' parking function is obtained when $m = n$. → `ClassicParkingFunction` (`lean/Papers/HawkesD75660b/Basic.lean:98`)
- definition of the paper: the vector defined component-wise by $\kappa_i(\pi) = |\{\ell : \pi_\ell = i \}|$ → `preferenceCountsOfParking` (`lean/Papers/HawkesD75660b/Basic.lean:155`)

## Corollary 2

**Statement.** \label{meanRecurSolve1} For $m < n$, let $\kappa$ be a length-$n$ preference count with distribution given by~\eqref{kappaDist}. Then, \begin{align} \E{\frac{1}{\kappa_{m+1}^+ - m} } &= \frac{n+1}{n-m} - \frac{1}{n-m} \sum_{i=0}^m {n \choose i} \left(\frac{i+1}{n+1}\right)^{i-1} \left(\frac{n-i}{n+1}\right)^{n-i} . \end{align}

**Lean.** `Papers.HawkesD75660b.meanRecurrenceSolution` — `lean/Papers/HawkesD75660b/T1.lean:56`

**Status.** proved in Lean, under 3 condition(s) made explicit. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| For $m < n$, let $\kappa$ be a length-$n$ preference count with distribution given by~\eqref{kappaDist}. | `n : ℕ`<br>`κ : Ω → CountVector n`<br>`m : ℕ`<br>`hindex : meanRecurrenceSolutionIndex n m`<br>`hlaw : meanRecurrenceSolutionLaw P κ`<br>`hrange : solutionIndexConvention n m` |
| Then, \begin{align} \E{\frac{1}{\kappa_{m+1}^+ - m} } &= \frac{n+1}{n-m} - \frac{1}{n-m} \sum_{i=0}^m {n \choose i} \left(\frac{i+1}{n+1}\right)^{i-1} \left(\frac{n-i}{n+1}\right)^{n-i} . \end{align} | then `(∫ ω, 1 / ((prefixCount (κ ω) (m + 1) : ℝ) - m) ∂P) = (n + 1 : ℝ) / ((n : ℝ) - m) - (1 / ((n : ℝ) - m)) * ∑ i ∈ Finset.range (m + 1), (Nat.choose n i : ℝ) * (((i + 1 : ℝ) / (n + 1 : ℝ)) ^ ((i : ℤ) - 1)) * (((n : ℝ) - i) / (n + 1 : ℝ)) ^ (n - i)` |

Lean also declares what the paper leaves implicit (the objects and their types): `Ω : Type*`, `MeasurableSpace Ω`, `P : Measure Ω`, `IsProbabilityMeasure P`.

Lean assumes conditions that the paper's text does not state: `hdomain : naturalCountDomainConvention`, `hzero : zeroCountConvention`.

**Conditions and readings, and the Lean definitions that carry them.**

- reading: $\mathbb{N}=\{0,1,2,\dots\}$ in the domain $\kappa\in\mathbb{N}^n$ of Definition~\ref{def:prefs}. → `naturalCountDomainConvention` (`lean/Papers/HawkesD75660b/Basic.lean:202`)
- reading: $n\in\mathbb{Z}_+$ and $m\in\{0,\dots,n-1\}$. → `solutionIndexConvention` (`lean/Papers/HawkesD75660b/Basic.lean:210`)
- reading: $\mathbb{N}=\{0,1,2,\dots\}$ in the definition of preference counts. → `zeroCountConvention` (`lean/Papers/HawkesD75660b/Basic.lean:206`)
- definition of the paper: \label{def:prefs} For $n \in \mathbb{Z}_+$, $\kappa \in \mathbb{N}^n$ is a vector of \emph{preference counts} if and only if $\sum_{i=1}^n \kappa_i = n$ and $\sum_{j=1}^i \kappa_j \ge i$ for $i \in \{1, \dots, n\}$. → `PreferenceCounts` (`lean/Papers/HawkesD75660b/Basic.lean:124`)
- definition of the paper: Likewise, $\kappa^+ \in \mathbb{Z}^n$ is a vector of \emph{cumulative preference counts} if and only if $1 \leq \kappa_1^+ \leq \dots \leq \kappa_n^+ \leq n$ and $\kappa^+_i \geq i$ for $i \in \{1, \dots, n\}$, where the bijection $\kappa_i^+ = \sum_{j=1}^i \kappa_j$ for $i \in \{1,\dots,n\}$ connects the two concepts. → `CumulativePreferenceCounts` (`lean/Papers/HawkesD75660b/Basic.lean:141`)
- definition of the paper: where the bijection $\kappa_i^+ = \sum_{j=1}^i \kappa_j$ for $i \in \{1,\dots,n\}$ connects the two concepts. → `cumulativePreferenceCounts` (`lean/Papers/HawkesD75660b/Basic.lean:148`)
- definition of the paper: \begin{align} \PP{\kappa_1 = k_1, \dots, \kappa_n = k_n} &= \frac{1}{(n+1)^{n-1}}{n \choose k_1, \dots, k_n} = \frac{n!}{(n+1)^{n-1}\prod_{i=1}^n k_i !} . \label{kappaDist} \end{align} → `preferenceCountMass` (`lean/Papers/HawkesD75660b/Basic.lean:161`)
- condition of the paper: For $m < n$, → `meanRecurrenceSolutionIndex` (`lean/Papers/HawkesD75660b/Basic.lean:182`)
- condition of the paper: with distribution given by~\eqref{kappaDist}. → `meanRecurrenceSolutionLaw` (`lean/Papers/HawkesD75660b/Basic.lean:197`)

## Identifiers

| Result | run id | paper label | source | Lean declaration |
| --- | --- | --- | --- | --- |
| Theorem 1 | `thm:meanidthm1` | `meanIdThm1` | `main.tex:243-255` | `Papers.HawkesD75660b.meanDurationIdentity` |
| Corollary 1 | `thm:coridthm1` | `corIdThm1` | `main.tex:257-266` | `Papers.HawkesD75660b.meanDurationIntegral` |
| Lemma 1 | `lem:kappacpmf1` | `kappaCPMF1` | `main.tex:383-410` | `Papers.HawkesD75660b.conditionalPreferenceCountLaw` |
| Lemma 2 | `lem:meanrecur1` | `meanRecur1` | `main.tex:496-507` | `Papers.HawkesD75660b.meanRecurrence` |
| Corollary 2 | `thm:meanrecursolve1` | `meanRecurSolve1` | `main.tex:572-586` | `Papers.HawkesD75660b.meanRecurrenceSolution` |
