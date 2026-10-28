# The corrected paper and its Lean formalization — oai_near_inclusions_von

For each result of the corrected paper: its statement, the Lean declaration that states it, whether that declaration is proved, and how the two statements correspond phrase by phrase. A result stated differently from the original paper is marked "corrected"; the report says what changed and why.

## Theorem 1.1

**Statement.** \label{thm:main} There exist $\varepsilon_0>0$, separable complex Hilbert spaces $H_n$, and von Neumann algebras $M_n,N_n\subseteq\mathcal B(H_n)$ with common identity $I_{H_n}$ such that \[ \gamma(M_n,N_n)\longrightarrow 0, \] but, for all sufficiently large $n$, every unitary $u\in\mathcal B(H_n)$ satisfying $uM_nu^*\subseteq N_n$ obeys \[ \|u-I_{H_n}\|\geq\varepsilon_0. \]

**Lean.** `Papers.OaiNearInclusionsVon.near_inclusion_not_implemented_by_small_unitaries` — `lean/Papers/OaiNearInclusionsVon/TMain.lean:43`

**Status.** proved in Lean, under 1 condition(s) made explicit. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| There exist $\varepsilon_0>0$, separable complex Hilbert spaces $H_n$, | then `∃ ε₀ : ℝ,`<br>then `0 < ε₀`<br>`∀ n`<br>then `TopologicalSpace.SeparableSpace (mainH n)` |
| and von Neumann algebras $M_n,N_n\subseteq\mathcal B(H_n)$ with common identity $I_{H_n}$ such that | — (no Lean counterpart recorded) |
| \[ \gamma(M_n,N_n)\longrightarrow 0, \] | then `Tendsto (mainGap π A hπ) atTop (𝓝 0)` |
| but, for all sufficiently large $n$, every unitary $u\in\mathcal B(H_n)$ satisfying $uM_nu^*\subseteq N_n$ obeys | then `∀ᶠ n in atTop,`<br>`∀ u ∈ unitary (mainH n →L[ℂ] mainH n)`<br>`∀ x ∈ mainSource π A hπ n`<br>`u * x * star u ∈ mainTarget n` |
| \[ \\|u-I_{H_n}\\|\geq\varepsilon_0. \] | then `ε₀ ≤ ‖u - 1‖` |

Lean concludes what the paper's text does not state: `∃ (π : CircleRep) (A : LaurentData) (hπ : IsCircleFamily π A),`.

**Conditions and readings, and the Lean definitions that carry them.**

- reading: For every $g\in F$, both sums defining $a(g)$ and $b(g)$ run over $k\in\mathbb Z$ and converge absolutely in operator norm. → `MatrixRepsAbsConv` (`lean/Papers/OaiNearInclusionsVon/Helpers/NearConstruction.lean:85`)
- definition of the paper: Apply the construction of Section~\ref{sec:near} to $D=\mathbb C^n$ and the clock--shift pair of Lemma~\ref{lem:clock}. Use subscripts $n$ for the resulting objects $L_n,H_n,a_n,b_n,f_n,W_n, M_n,N_n$. → `mainSource` (`lean/Papers/OaiNearInclusionsVon/Helpers/MainSequence.lean:65`)
- definition of the paper: The weak limits from Proposition~\ref{prop:circle} become \begin{equation}\label{eq:matrix-limits} a(s_j)\xrightarrow{\WOT}t p_e\otimes I_K\otimes U, \qquad b(s_j)\xrightarrow{\WOT}t I_K\otimes p_e\otimes V. \end{equation} → `matrixLimitsWot` (`lean/Papers/OaiNearInclusionsVon/Helpers/MatrixLimits.lean:246`)
- definition of the paper: Let $M$ and $N$ be von Neumann algebras acting on a complex Hilbert space $H$, both with identity $I_H$. Their one-sided near-inclusion gap is \begin{equation}\label{eq:gamma-definition} \gamma(M,N)=\sup_{\substack{x\in M\\\|x\|\leq 1}} \inf_{y\in N}\|x-y\|. \end{equation} → `nearInclusionGap` (`lean/Papers/OaiNearInclusionsVon/Helpers/Gap.lean:22`)
- definition of the paper: and let $p_e$ be the projection onto $\mathbb C\delta_e$. → `projE` (`lean/Papers/OaiNearInclusionsVon/Helpers/FreeGroupSpace.lean:50`)
- definition of the paper: Throughout the construction, \[ t=\frac12,\qquad r=(1-t^2)^{1/2},\qquad \mathbb T=\{z\in\mathbb C:|z|=1\}. \] → `circleParameters` (`lean/Papers/OaiNearInclusionsVon/Helpers/FreeGroupSpace.lean:74`)
- definition of the paper: \begin{equation}\label{eq:vanishing-gap} \gamma(M_n,N_n)\leq C\nu_n\longrightarrow0. \end{equation} → `vanishingGap` (`lean/Papers/OaiNearInclusionsVon/Helpers/MainSequence.lean:123`)

## Proposition 2.1

**Statement.** \label{prop:circle} There are unitary representations $\pi_z:F\to\B(K)$, indexed by $z\in\mathbb T$, and operators $A_k(g)\in\B(K)$, indexed by $k\in\mathbb Z$ and $g\in F$, such that \begin{align} \pi_z(g)&=\sum_{k\in\mathbb Z}z^kA_k(g), &\sup_{g\in F}\|A_k(g)\|&\leq c_k, &c_k&=\mathbf 1_{\{k=0\}}+\frac{2t^{|k|}}{1-t}, \label{eq:fourier}\\ \pi_z(s_j)&\xrightarrow[j\to\infty]{\WOT}tzp_e. \label{eq:circle-limit} \end{align} The series in \eqref{eq:fourier} converges absolutely in operator norm, uniformly in $g$ and $z$, and \begin{equation}\label{eq:moments} S_0:=\sum_{k\in\mathbb Z}c_k<\infty, \qquad S_1:=\sum_{k\in\mathbb Z}|k|c_k<\infty. \end{equation}

**Lean.** `Papers.OaiNearInclusionsVon.circle_family_exists` — `lean/Papers/OaiNearInclusionsVon/TCircle.lean:22`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| There are unitary representations $\pi_z:F\to\B(K)$, indexed by $z\in\mathbb T$, | then `∃ (π : CircleRep) (A : LaurentData), IsCircleFamily π A` |
| and operators $A_k(g)\in\B(K)$, indexed by $k\in\mathbb Z$ | then `∃ (π : CircleRep) (A : LaurentData), IsCircleFamily π A` |
| and $g\in F$, such that | then `∃ (π : CircleRep) (A : LaurentData), IsCircleFamily π A` |
| \begin{align} \pi_z(g)&=\sum_{k\in\mathbb Z}z^kA_k(g), | then `∃ (π : CircleRep) (A : LaurentData), IsCircleFamily π A` |
| &\sup_{g\in F}\\|A_k(g)\\|&\leq c_k, | then `∃ (π : CircleRep) (A : LaurentData), IsCircleFamily π A` |
| &c_k&=\mathbf 1_{\{k=0\}}+\frac{2t^{\|k\|}}{1-t}, \\ | then `∃ (π : CircleRep) (A : LaurentData), IsCircleFamily π A` |
| \pi_z(s_j)&\xrightarrow[j\to\infty]{\WOT}tzp_e. \end{align} | then `∃ (π : CircleRep) (A : LaurentData), IsCircleFamily π A` |
| The series in \eqref{eq:fourier} converges absolutely in operator norm, uniformly in $g$ and $z$, | then `∃ (π : CircleRep) (A : LaurentData), IsCircleFamily π A` |
| and \begin{equation} S_0:=\sum_{k\in\mathbb Z}c_k<\infty, \qquad | then `∃ (π : CircleRep) (A : LaurentData), IsCircleFamily π A` |
| S_1:=\sum_{k\in\mathbb Z}\|k\|c_k<\infty. \end{equation} | then `∃ (π : CircleRep) (A : LaurentData), IsCircleFamily π A` |

**Conditions and readings, and the Lean definitions that carry them.**

- definition of the paper: Let $F$ be the free group on generators $s_j$, $j\geq 1$, with identity $e$. → `FreeGrp` (`lean/Papers/OaiNearInclusionsVon/Helpers/FreeGroupSpace.lean:27`)
- definition of the paper: Put $K=\ell^2(F)$ → `TreeSpace` (`lean/Papers/OaiNearInclusionsVon/Helpers/FreeGroupSpace.lean:39`)
- definition of the paper: write $(\delta_x)_{x\in F}$ for its standard orthonormal basis → `treeBasis` (`lean/Papers/OaiNearInclusionsVon/Helpers/FreeGroupSpace.lean:44`)
- definition of the paper: and let $p_e$ be the projection onto $\mathbb C\delta_e$. → `projE` (`lean/Papers/OaiNearInclusionsVon/Helpers/FreeGroupSpace.lean:50`)
- definition of the paper: We use the left regular representation $l(g)\delta_x=\delta_{gx}$. → `leftReg` (`lean/Papers/OaiNearInclusionsVon/Helpers/FreeGroupSpace.lean:57`)
- definition of the paper: Throughout the construction, \[ t=\frac12,\qquad r=(1-t^2)^{1/2},\qquad \mathbb T=\{z\in\mathbb C:|z|=1\}. \] → `circleParameters` (`lean/Papers/OaiNearInclusionsVon/Helpers/FreeGroupSpace.lean:74`)

## Proposition 3.1

**Statement.** \label{prop:near} For the algebras in \eqref{eq:algebras}, \begin{equation}\label{eq:near-bound} \gamma(M,N)\leq C\|UV-VU\|, \qquad C:=\sum_{k,m,p,h\in\mathbb Z} c_kc_mc_pc_h|m-p|\,|h|<\infty. \end{equation} Moreover, for every $g\in G$, \begin{equation}\label{eq:group-bound} \bigl\|W(\lambda(g)\otimes I_L)W^* -\lambda(g)\otimes f(g)\bigr\| \leq C\|UV-VU\|. \end{equation} The constant is independent of $D,U,V$.

**Lean.** `Papers.OaiNearInclusionsVon.near_inclusion_bound` — `lean/Papers/OaiNearInclusionsVon/TNear.lean:28`

**Status.** proved in Lean, under 1 condition(s) made explicit. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| For the algebras in \eqref{eq:algebras}, | — (no Lean counterpart recorded) |
| \begin{equation} \gamma(M,N)\leq C\\|UV-VU\\|, \qquad | then `nearInclusionGap (sourceAlg A U V hb : Set (Hsp D →L[ℂ] Hsp D)) (targetAlg (D := D) : Set (Hsp D →L[ℂ] Hsp D)) ≤ nearC * ‖U * V - V * U‖` |
| C:=\sum_{k,m,p,h\in\mathbb Z} c_kc_mc_pc_h\|m-p\|\,\|h\|<\infty. \end{equation} | then `Summable nearWeight` |
| Moreover, for every $g\in G$, | `∀ g : ProdGrp` |
| \begin{equation} \bigl\\|W(\lambda(g)\otimes I_L)W^* -\lambda(g)\otimes f(g)\bigr\\| \leq C\\|UV-VU\\|. \end{equation} | then `‖diagUnitary A U V hb * lamAmp g * star (diagUnitary A U V hb) - lamAmp g * lp.mapCLM 2 (fun _ : ProdGrp => prodMap A U V g) (norm_nonneg _) (fun _ => le_rfl)‖ ≤ nearC * ‖U * V - V * U‖` |
| The constant is independent of $D,U,V$. | `D : Type*`<br>`U V : D →L[ℂ] D` |

Lean also declares what the paper leaves implicit (the objects and their types): `NormedAddCommGroup D`, `InnerProductSpace ℂ D`, `CompleteSpace D`, `π : CircleRep`, `A : LaurentData`, `let hb := prodMap_norm_bound π A hπ U V ⟨hUV.2.2.1, hUV.2.2.2⟩`.

Lean assumes conditions that the paper's text does not state: `hπ : IsCircleFamily π A`, `hUV : NearUnitaryPair U V`, `habs : MatrixRepsAbsConv A U V`.

**Conditions and readings, and the Lean definitions that carry them.**

- reading: For every $g\in F$, both sums defining $a(g)$ and $b(g)$ run over $k\in\mathbb Z$ and converge absolutely in operator norm. → `MatrixRepsAbsConv` (`lean/Papers/OaiNearInclusionsVon/Helpers/NearConstruction.lean:85`)
- definition of the paper: Let $M$ and $N$ be von Neumann algebras acting on a complex Hilbert space $H$, both with identity $I_H$. Their one-sided near-inclusion gap is \begin{equation}\label{eq:gamma-definition} \gamma(M,N)=\sup_{\substack{x\in M\\\|x\|\leq 1}} \inf_{y\in N}\|x-y\|. \end{equation} → `nearInclusionGap` (`lean/Papers/OaiNearInclusionsVon/Helpers/Gap.lean:22`)
- condition of the paper: two unitaries $U,V$ on a nonzero finite-dimensional Hilbert space $D$. → `NearUnitaryPair` (`lean/Papers/OaiNearInclusionsVon/Helpers/NearConstruction.lean:28`)
- definition of the paper: On $L=K\otimes K\otimes D$, define \begin{equation}\label{eq:matrix-reps} a(g)=\sum_k A_k(g)\otimes I_K\otimes U^k, \qquad b(g)=\sum_k I_K\otimes A_k(g)\otimes V^k \quad(g\in F). \end{equation} → `matrixRepA` (`lean/Papers/OaiNearInclusionsVon/Helpers/NearConstruction.lean:94`)
- definition of the paper: Put $G=F\times F$, $S=\ell^2(G)$, and $H=S\otimes L$. → `ProdGrp` (`lean/Papers/OaiNearInclusionsVon/Helpers/NearConstruction.lean:116`)
- definition of the paper: Our conventions for the commuting left and right regular representations on $S$ are \[ \lambda(g)\delta_x=\delta_{gx},\qquad \rho(g)\delta_x=\delta_{xg^{-1}}. \] → `lamReg` (`lean/Papers/OaiNearInclusionsVon/Helpers/NearConstruction.lean:136`)
- definition of the paper: For $x=(x_1,x_2)\in G$, put $f(x)=a(x_1)b(x_2)$ → `prodMap` (`lean/Papers/OaiNearInclusionsVon/Helpers/NearConstruction.lean:158`)
- definition of the paper: and define the diagonal unitary $W$ by \[ W(\delta_x\otimes v)=\delta_x\otimes f(x)v. \] → `diagUnitary` (`lean/Papers/OaiNearInclusionsVon/Helpers/NearConstruction.lean:340`)
- definition of the paper: Define \begin{equation}\label{eq:algebras} M=W\bigl(\lambda(G)''\otimes I_L\bigr)W^*, \qquad N=\bigl(\rho(G)\otimes I_L\bigr)'. \end{equation} → `sourceAlg` (`lean/Papers/OaiNearInclusionsVon/Helpers/NearConstruction.lean:427`)
- definition of the paper: Primes denote commutants. → `commutant` (`lean/Papers/OaiNearInclusionsVon/Helpers/Gap.lean:33`)

## Lemma 4.1

**Statement.** \label{lem:clock} For $n\geq3$, let $U_n,V_n$ be the unitaries on $\mathbb C^n$ given by \begin{equation}\label{eq:clock-shift} U_ne_j=\omega_n^je_j,\qquad V_ne_j=e_{j+1\bmod n},\qquad \omega_n=e^{2\pi i/n}\quad(0\leq j<n). \end{equation} Then $\nu_n:=\|U_nV_n-V_nU_n\|=|\omega_n-1|\to0$. There is no infinite subsequence along which commuting unitaries $\widehat U_n,\widehat V_n$ on $\mathbb C^n$ satisfy \[ \|\widehat U_n-U_n\|+\|\widehat V_n-V_n\|\longrightarrow0. \]

**Lean.** `Papers.OaiNearInclusionsVon.clock_shift_not_near_commuting` — `lean/Papers/OaiNearInclusionsVon/Helpers/Clock.lean:554`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| For $n\geq3$, let $U_n,V_n$ be the unitaries on $\mathbb C^n$ given by | `n : ℕ`<br>`hn : ClockIndex n` |
| \begin{equation} U_ne_j=\omega_n^je_j,\qquad | — (no Lean counterpart recorded) |
| V_ne_j=e_{j+1\bmod n},\qquad | — (no Lean counterpart recorded) |
| \omega_n=e^{2\pi i/n}\quad | — (no Lean counterpart recorded) |
| (0\leq j<n). \end{equation} | — (no Lean counterpart recorded) |
| Then $\nu_n:=\\|U_nV_n-V_nU_n\\|=\|\omega_n-1\|\to0$. | then `nuN ⟨n, hn⟩ = ‖omegaN ⟨n, hn⟩ - 1‖`<br>then `Tendsto nuN atTop (𝓝 0)` |
| There is no infinite subsequence along which commuting unitaries $\widehat U_n,\widehat V_n$ on $\mathbb C^n$ satisfy | then `¬ ∃ (φ : ℕ → ClockNat) (Uhat Vhat : ∀ k, ClockSpace (φ k) →L[ℂ] ClockSpace (φ k)), StrictMono φ ∧ (∀ k, Uhat k ∈ unitary _ ∧ Vhat k ∈ unitary _ ∧ Commute (Uhat k) (Vhat k)) ∧ Tendsto (fun k => ‖Uhat k - clockU (φ k)‖ + ‖Vhat k - shiftV (φ k)‖) atTop (𝓝 0)` |
| \[ \\|\widehat U_n-U_n\\|+\\|\widehat V_n-V_n\\|\longrightarrow0. \] | then `¬ ∃ (φ : ℕ → ClockNat) (Uhat Vhat : ∀ k, ClockSpace (φ k) →L[ℂ] ClockSpace (φ k)), StrictMono φ ∧ (∀ k, Uhat k ∈ unitary _ ∧ Vhat k ∈ unitary _ ∧ Commute (Uhat k) (Vhat k)) ∧ Tendsto (fun k => ‖Uhat k - clockU (φ k)‖ + ‖Vhat k - shiftV (φ k)‖) atTop (𝓝 0)` |

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: For $n\geq3$ → `ClockIndex` (`lean/Papers/OaiNearInclusionsVon/Helpers/Clock.lean:37`)
- definition of the paper: \label{lem:clock} For $n\geq3$, let $U_n,V_n$ be the unitaries on $\mathbb C^n$ given by \begin{equation}\label{eq:clock-shift} U_ne_j=\omega_n^je_j,\qquad V_ne_j=e_{j+1\bmod n},\qquad \omega_n=e^{2\pi i/n}\quad(0\leq j<n). \end{equation} → `clockU` (`lean/Papers/OaiNearInclusionsVon/Helpers/Clock.lean:55`)

## Lemma 4.2

**Statement.** \label{lem:corner} For each $n$, let $E_{1n},E_{2n}$ be commuting projections on a complex Hilbert space $H_n$, with $D_n=E_nH_n$ nonzero and finite-dimensional, where $E_n=E_{1n}E_{2n}$. Let $\widetilde R_{1n},\widetilde R_{2n}$ be unitaries commuting with both projections, and write $R_{in}=\widetilde R_{in}|_{D_n}$. Suppose $\mathcal A_{1n},\mathcal A_{2n}\subset\B(H_n)$ are commuting unital von Neumann algebras and there are $T_{in}\in\mathcal A_{in}$ such that \begin{equation}\label{eq:corner-hypothesis} \|T_{in}-E_{in}\widetilde R_{in}\|\longrightarrow0 \quad(i=1,2). \end{equation} Then, for all sufficiently large $n$, there are commuting unitaries $\widehat R_{1n},\widehat R_{2n}$ on $D_n$ with \[ \|\widehat R_{in}-R_{in}\|\longrightarrow0\quad(i=1,2). \]

**Lean.** `Papers.OaiNearInclusionsVon.corner_commuting_approximants` — `lean/Papers/OaiNearInclusionsVon/Helpers/CornerFinalization.lean:225`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| For each $n$, let $E_{1n},E_{2n}$ be commuting projections on a complex Hilbert space $H_n$, | `H : ℕ → Type*`<br>`E₁ E₂ R₁ R₂ T₁ T₂ : ∀ n, H n →`<br>`L[ℂ] H n`<br>`hE : CornerProjections E₁ E₂` |
| with $D_n=E_nH_n$ nonzero and finite-dimensional, | `hD : CornerDimension E₁ E₂`<br>`let : ∀ n, FiniteDimensional ℂ (cornerRange E₁ E₂ n) := fun n => (hD n).2` |
| where $E_n=E_{1n}E_{2n}$. | — (no Lean counterpart recorded) |
| Let $\widetilde R_{1n},\widetilde R_{2n}$ be unitaries commuting with both projections, | `E₁ E₂ R₁ R₂ T₁ T₂ : ∀ n, H n →`<br>`L[ℂ] H n`<br>`hR : CornerUnitaries E₁ E₂ R₁ R₂` |
| and write $R_{in}=\widetilde R_{in}\|_{D_n}$. | — (no Lean counterpart recorded) |
| Suppose $\mathcal A_{1n},\mathcal A_{2n}\subset\B(H_n)$ are commuting unital von Neumann algebras and there are $T_{in}\in\mathcal A_{in}$ such that | `E₁ E₂ R₁ R₂ T₁ T₂ : ∀ n, H n →`<br>`L[ℂ] H n`<br>`A₁ A₂ : ∀ n, VonNeumannAlgebra (H n)`<br>`hA : CornerAlgebras A₁ A₂`<br>`hT : CornerApproximation A₁ A₂ T₁ T₂ E₁ E₂ R₁ R₂` |
| \begin{equation} \\|T_{in}-E_{in}\widetilde R_{in}\\|\longrightarrow0 \quad | `hT : CornerApproximation A₁ A₂ T₁ T₂ E₁ E₂ R₁ R₂` |
| (i=1,2). \end{equation} | `hT : CornerApproximation A₁ A₂ T₁ T₂ E₁ E₂ R₁ R₂` |
| Then, for all sufficiently large $n$, there are commuting unitaries $\widehat R_{1n},\widehat R_{2n}$ on $D_n$ with | then `∃ Rhat₁ Rhat₂ : ∀ n, cornerRange E₁ E₂ n →L[ℂ] cornerRange E₁ E₂ n, (∀ᶠ n in atTop, Rhat₁ n ∈ unitary _ ∧ Rhat₂ n ∈ unitary _ ∧ Commute (Rhat₁ n) (Rhat₂ n)) ∧ Tendsto (fun n => ‖Rhat₁ n - cornerRestrict E₁ E₂ R₁ n‖) atTop (𝓝 0) ∧ Tendsto (fun n => ‖Rhat₂ n - cornerRestrict E₁ E₂ R₂ n‖) atTop (𝓝 0)` |
| \[ \\|\widehat R_{in}-R_{in}\\|\longrightarrow0\quad | then `∃ Rhat₁ Rhat₂ : ∀ n, cornerRange E₁ E₂ n →L[ℂ] cornerRange E₁ E₂ n, (∀ᶠ n in atTop, Rhat₁ n ∈ unitary _ ∧ Rhat₂ n ∈ unitary _ ∧ Commute (Rhat₁ n) (Rhat₂ n)) ∧ Tendsto (fun n => ‖Rhat₁ n - cornerRestrict E₁ E₂ R₁ n‖) atTop (𝓝 0) ∧ Tendsto (fun n => ‖Rhat₂ n - cornerRestrict E₁ E₂ R₂ n‖) atTop (𝓝 0)` |
| (i=1,2). \] | then `∃ Rhat₁ Rhat₂ : ∀ n, cornerRange E₁ E₂ n →L[ℂ] cornerRange E₁ E₂ n, (∀ᶠ n in atTop, Rhat₁ n ∈ unitary _ ∧ Rhat₂ n ∈ unitary _ ∧ Commute (Rhat₁ n) (Rhat₂ n)) ∧ Tendsto (fun n => ‖Rhat₁ n - cornerRestrict E₁ E₂ R₁ n‖) atTop (𝓝 0) ∧ Tendsto (fun n => ‖Rhat₂ n - cornerRestrict E₁ E₂ R₂ n‖) atTop (𝓝 0)` |

Lean also declares what the paper leaves implicit (the objects and their types): `∀ n, NormedAddCommGroup (H n)`, `∀ n, InnerProductSpace ℂ (H n)`, `∀ n, CompleteSpace (H n)`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: For each $n$, let $E_{1n},E_{2n}$ be commuting projections on a complex Hilbert space $H_n$ → `CornerProjections` (`lean/Papers/OaiNearInclusionsVon/Helpers/Corner.lean:24`)
- condition of the paper: with $D_n=E_nH_n$ nonzero and finite-dimensional → `CornerDimension` (`lean/Papers/OaiNearInclusionsVon/Helpers/Corner.lean:39`)
- condition of the paper: Let $\widetilde R_{1n},\widetilde R_{2n}$ be unitaries commuting with both projections → `CornerUnitaries` (`lean/Papers/OaiNearInclusionsVon/Helpers/Corner.lean:44`)
- condition of the paper: Suppose $\mathcal A_{1n},\mathcal A_{2n}\subset\B(H_n)$ are commuting unital von Neumann algebras → `CornerAlgebras` (`lean/Papers/OaiNearInclusionsVon/Helpers/Corner.lean:52`)
- condition of the paper: and there are $T_{in}\in\mathcal A_{in}$ such that \begin{equation}\label{eq:corner-hypothesis} \|T_{in}-E_{in}\widetilde R_{in}\|\longrightarrow0 \quad(i=1,2). \end{equation} → `CornerApproximation` (`lean/Papers/OaiNearInclusionsVon/Helpers/Corner.lean:57`)
- definition of the paper: with $D_n=E_nH_n$ nonzero and finite-dimensional, where $E_n=E_{1n}E_{2n}$. → `cornerRange` (`lean/Papers/OaiNearInclusionsVon/Helpers/Corner.lean:34`)
- definition of the paper: and write $R_{in}=\widetilde R_{in}|_{D_n}$. → `cornerRestrict` (`lean/Papers/OaiNearInclusionsVon/Helpers/Corner.lean:71`)

## Identifiers

| Result | run id | paper label | source | Lean declaration |
| --- | --- | --- | --- | --- |
| Theorem 1.1 | `thm:main` | `thm:main` | `sections/introduction.tex:49-61` | `Papers.OaiNearInclusionsVon.near_inclusion_not_implemented_by_small_unitaries` |
| Proposition 2.1 | `prop:circle` | `prop:circle` | `sections/circle.tex:18-36` | `Papers.OaiNearInclusionsVon.circle_family_exists` |
| Proposition 3.1 | `prop:near` | `prop:near` | `sections/near.tex:67-82` | `Papers.OaiNearInclusionsVon.near_inclusion_bound` |
| Lemma 4.1 | `lem:clock` | `lem:clock` | `sections/obstruction.tex:13-26` | `Papers.OaiNearInclusionsVon.clock_shift_not_near_commuting` |
| Lemma 4.2 | `lem:corner` | `lem:corner` | `sections/obstruction.tex:76-94` | `Papers.OaiNearInclusionsVon.corner_commuting_approximants` |
