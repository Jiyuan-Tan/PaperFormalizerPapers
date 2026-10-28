# The corrected paper and its Lean formalization — oai_bound_dyadic_triangular

For each result of the corrected paper: its statement, the Lean declaration that states it, whether that declaration is proved, and how the two statements correspond phrase by phrase. A result stated differently from the original paper is marked "corrected"; the report says what changed and why.

## Theorem 1.1

**Statement.** \label{thm:main} For every finite \(S\subset\Z\) and all real bounded compactly supported measurable functions \(F_0,F_1,F_2\) on \(\R_+^2\), \begin{equation}\label{eq:main} \sum_{k\in S}\sum_{\mathbf I\in\cA_k} \abs{L_{\mathbf I}(F_0,F_1,F_2)} \le 40\prod_{v=0}^2\norm{F_v}_{L^3(\R_+^2)}. \end{equation}

**Lean.** `Papers.OaiBoundDyadicTriangular.dyadic_triangular_bound` — `lean/Papers/OaiBoundDyadicTriangular/TMain.lean:65`

**Status.** proved in Lean, under 1 condition(s) made explicit. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| For every finite \(S\subset\Z\) and all real bounded compactly supported measurable functions \(F_0,F_1,F_2\) on \(\R_+^2\), | `S : Set ℤ`<br>`F : Fin 3 → ℝ × ℝ → ℝ`<br>`hS : MainScales S`<br>`hInputs : MainInputs F` |
| \begin{equation} \sum_{k\in S}\sum_{\mathbf I\in\cA_k} \abs{L_{\mathbf I}(F_0,F_1,F_2)} \le 40\prod_{v=0}^2\norm{F_v}_{L^3(\R_+^2)}. \end{equation} | then `∑ k ∈ hS.toFinset, ∑ n ∈ T k, |localForm k n.val F| ≤ 40 * ∏ v : Fin 3, (eLpNorm (F v) 3 quadrantMeasure).toReal` |

Lean also declares what the paper leaves implicit (the objects and their types): `∀ T : ℤ → Finset admissibleSet`.

Lean assumes conditions that the paper's text does not state: `hHalves : HaarHalvesConvention`.

**Conditions and readings, and the Lean definitions that carry them.**

- reading: For $I=[2^kn_I,2^k(n_I+1))$, its halves are $I_{\mathrm{left}}=[2^kn_I,2^kn_I+2^{k-1})$ and $I_{\mathrm{right}}=[2^kn_I+2^{k-1},2^k(n_I+1))$. → `HaarHalvesConvention` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:295`)
- definition of the paper: Write \(\R_+=[0,\infty)\). → `Rplus` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:230`)
- definition of the paper: For \(k\in\Z\), let \[ \cD_k=\{[2^kn,2^k(n+1)):n\in\Z_{\ge0}\}. \] → `dyadicInterval` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:244`)
- definition of the paper: For \(I\in\cD_k\), denote its index by \(n_I\) and set \[ h_I=\mathbf1_{I_{\mathrm{left}}}-\mathbf1_{I_{\mathrm{right}}}. \] → `haarSign` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:260`)
- definition of the paper: Let \(\oplus\) denote bitwise XOR of nonnegative integers → `xor3` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:270`)
- definition of the paper: define the set of admissible triples \[ \cA_k=\{(I_0,I_1,I_2)\in\cD_k^3: n_{I_0}\oplus n_{I_1}\oplus n_{I_2}=0\}. \] → `IsAdmissible` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:275`)
- definition of the paper: For \(\mathbf I\in\cA_k\) and three real functions \(F_v\) on \(\R_+^2\), put \begin{equation}\label{eq:local-form} L_{\mathbf I}(F_0,F_1,F_2) =2^{-k}\int_{I_0\times I_1\times I_2} F_0(x_0,x_1)F_1(x_1,x_2)F_2(x_2,x_0) \prod_{v=0}^2 h_{I_v}(x_v)\dd x_0\dd x_1\dd x_2. \end{equation} → `localForm` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:309`)
- definition of the paper: \begin{equation}\label{eq:trace-integral} L_{\mathbf I}(F_0,F_1,F_2)=2^{2k}\tau(\mathbf I). \end{equation} → `traceNormalizedForm` (`lean/Papers/OaiBoundDyadicTriangular/Helpers/AtomEnergy.lean:225`)
- condition of the paper: For every finite \(S\subset\Z\) → `MainScales` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:348`)
- condition of the paper: all real bounded compactly supported measurable functions \(F_0,F_1,F_2\) on \(\R_+^2\) → `MainInputs` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:356`)

## Lemma 2.1

**Statement.** \label{lem:hessian} On matrices positive definite on a fixed support, \(\Phi\) is smooth and, for a symmetric direction \(K\) on that support, \[ d\Phi_P(K)=\frac32\tr(\sqrt P\,K), \qquad d^2\Phi_P(K,K)=b_P(K). \] In particular, \(\Phi\) is convex on the positive semidefinite cone.

**Lean.** `Papers.OaiBoundDyadicTriangular.matrixEnergy_hessian` — `lean/Papers/OaiBoundDyadicTriangular/Helpers/MatrixHessian.lean:104`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| On matrices positive definite on a fixed support, \(\Phi\) is smooth and, for a symmetric direction \(K\) on that support, | `P K : Matrix ι ι ℝ`<br>`hP : HessianPositiveSupport P`<br>`hK : HessianDirection P K`<br>then `p ∈ positiveSupportLocus P`<br>then `ContDiffOn ℝ ⊤ Φ (positiveSupportLocus P)`<br>`∀ Q ∈ positiveSupportLocus P`<br>`∀ L : E` |
| \[ d\Phi_P(K)=\frac32\tr(\sqrt P\,K), \qquad | then `fderiv ℝ Φ Q L = (3 / 2 : ℝ) * (CFC.sqrt Q.val * L.val).trace`<br>then `fderiv ℝ Φ p d = (3 / 2 : ℝ) * (CFC.sqrt P * K).trace` |
| d^2\Phi_P(K,K)=b_P(K). \] | then `fderiv ℝ (fderiv ℝ Φ) Q L L = hessForm Q.val (supportedTangent_isHermitian P Q) L.val`<br>then `fderiv ℝ (fderiv ℝ Φ) p d d = hessForm P hP.isHermitian K` |
| In particular, \(\Phi\) is convex on the positive semidefinite cone. | then `ConvexOn ℝ {A : Matrix ι ι ℝ | A.PosSemidef} matrixEnergy` |

Lean also declares what the paper leaves implicit (the objects and their types): `ι : Type*`, `Fintype ι`, `DecidableEq ι`, `let E := supportedTangent P`, `let Φ : E → ℝ := fun Q => matrixEnergy Q.val`, `let p : E := ⟨P, base_mem_supportedTangent P hP⟩`, `let d : E := ⟨K, (mem_supportedTangent P K).mpr hK⟩`.

Lean concludes what the paper's text does not state: `IsOpen (positiveSupportLocus P)`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: All spaces and matrices in the proof are real → `RealMatrixSetting` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:35`)
- definition of the paper: \(R^*\) denotes the transpose of \(R\). → `realAdjoint` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:42`)
- definition of the paper: For a symmetric positive semidefinite matrix \(P\), define \[ \Phi(P)=\tr(P^{3/2}),\qquad \supp P=(\ker P)^\perp. \] → `matrixEnergy` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:63`)
- definition of the paper: A symmetric matrix \(K\) is \emph{supported on \(P\)} if it annihilates \(\ker P\). → `SupportedOn` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:55`)
- definition of the paper: For such \(K\), define \begin{equation}\label{eq:hessian} b_P(K)=\frac32\sum_{i,j} \frac{\abs{K_{ij}}^2}{\sqrt{p_i}+\sqrt{p_j}}, \end{equation} where \(p_i>0\) are the eigenvalues of \(P\) on its support, and the entries are taken in an orthonormal eigenbasis of that support. If \(P=0\), the only supported \(K\) is zero and \(b_0(0)=0\). → `hessForm` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:84`)
- condition of the paper: On matrices positive definite on a fixed support → `HessianPositiveSupport` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:98`)
- condition of the paper: for a symmetric direction \(K\) on that support → `HessianDirection` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:106`)

## Lemma 2.2

**Statement.** \label{lem:order} Suppose \(P,Q\) are positive semidefinite matrices on the same space, \(a\ge1\), and \(P\le aQ\). Every symmetric \(K\) supported on \(P\) is supported on \(Q\), and \begin{equation}\label{eq:order} b_P(K)\ge a^{-1/2}b_Q(K). \end{equation}

**Lean.** `Papers.OaiBoundDyadicTriangular.hessForm_order` — `lean/Papers/OaiBoundDyadicTriangular/Helpers/MatrixHessian.lean:135`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| Suppose \(P,Q\) are positive semidefinite matrices on the same space, \(a\ge1\), | `P Q K : Matrix ι ι ℝ`<br>`a : ℝ`<br>`hMatrices : OrderMatrices P Q`<br>`hFactor : OrderFactor a` |
| and \(P\le aQ\). | `hComparison : OrderComparison P Q a` |
| Every symmetric \(K\) supported on \(P\) is supported on \(Q\), | `P Q K : Matrix ι ι ℝ`<br>`hDirection : OrderDirection P K`<br>then `SupportedOn Q K` |
| and \begin{equation} b_P(K)\ge a^{-1/2}b_Q(K). \end{equation} | then `a ^ (-1 / 2 : ℝ) * hessForm Q hMatrices.2.isHermitian K ≤ hessForm P hMatrices.1.isHermitian K` |

Lean also declares what the paper leaves implicit (the objects and their types): `ι : Type*`, `Fintype ι`, `DecidableEq ι`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: All spaces and matrices in the proof are real → `RealMatrixSetting` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:35`)
- definition of the paper: \(R^*\) denotes the transpose of \(R\). → `realAdjoint` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:42`)
- definition of the paper: For a symmetric positive semidefinite matrix \(P\), define \[ \Phi(P)=\tr(P^{3/2}),\qquad \supp P=(\ker P)^\perp. \] → `matrixEnergy` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:63`)
- definition of the paper: A symmetric matrix \(K\) is \emph{supported on \(P\)} if it annihilates \(\ker P\). → `SupportedOn` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:55`)
- definition of the paper: For such \(K\), define \begin{equation}\label{eq:hessian} b_P(K)=\frac32\sum_{i,j} \frac{\abs{K_{ij}}^2}{\sqrt{p_i}+\sqrt{p_j}}, \end{equation} where \(p_i>0\) are the eigenvalues of \(P\) on its support, and the entries are taken in an orthonormal eigenbasis of that support. If \(P=0\), the only supported \(K\) is zero and \(b_0(0)=0\). → `hessForm` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:84`)
- condition of the paper: Suppose \(P,Q\) are positive semidefinite matrices on the same space → `OrderMatrices` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:114`)
- condition of the paper: \(a\ge1\) → `OrderFactor` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:124`)
- condition of the paper: \(P\le aQ\) → `OrderComparison` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:131`)
- condition of the paper: Every symmetric \(K\) supported on \(P\) → `OrderDirection` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:137`)

## Corollary 2.3

**Statement.** \label{cor:gap} If \(T\ge0\) and \(U=U^*\) satisfy \(-T\le U\le T\), then \(U\) is supported on \(T\) and \begin{equation}\label{eq:gap} \frac{\Phi(T+U)+\Phi(T-U)}2-\Phi(T) \ge\frac{1}{2\sqrt2}b_T(U). \end{equation}

**Lean.** `Papers.OaiBoundDyadicTriangular.matrixEnergy_midpoint_gap` — `lean/Papers/OaiBoundDyadicTriangular/TGap.lean:22`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| If \(T\ge0\) | `T U : Matrix ι ι ℝ`<br>`hPositive : GapPositive T` |
| and \(U=U^*\) satisfy \(-T\le U\le T\), | `T U : Matrix ι ι ℝ`<br>`hSymmetry : GapSymmetry U`<br>`hOrder : GapOrder T U` |
| then \(U\) is supported on \(T\) and | then `SupportedOn T U` |
| \begin{equation} \frac{\Phi(T+U)+\Phi(T-U)}2-\Phi(T) \ge\frac{1}{2\sqrt2}b_T(U). \end{equation} | then `1 / (2 * Real.sqrt 2) * hessForm T hPositive.isHermitian U ≤ (matrixEnergy (T + U) + matrixEnergy (T - U)) / 2 - matrixEnergy T` |

Lean also declares what the paper leaves implicit (the objects and their types): `ι : Type*`, `Fintype ι`, `DecidableEq ι`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: All spaces and matrices in the proof are real → `RealMatrixSetting` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:35`)
- definition of the paper: \(R^*\) denotes the transpose of \(R\). → `realAdjoint` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:42`)
- definition of the paper: For a symmetric positive semidefinite matrix \(P\), define \[ \Phi(P)=\tr(P^{3/2}),\qquad \supp P=(\ker P)^\perp. \] → `matrixEnergy` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:63`)
- definition of the paper: A symmetric matrix \(K\) is \emph{supported on \(P\)} if it annihilates \(\ker P\). → `SupportedOn` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:55`)
- definition of the paper: For such \(K\), define \begin{equation}\label{eq:hessian} b_P(K)=\frac32\sum_{i,j} \frac{\abs{K_{ij}}^2}{\sqrt{p_i}+\sqrt{p_j}}, \end{equation} where \(p_i>0\) are the eigenvalues of \(P\) on its support, and the entries are taken in an orthonormal eigenbasis of that support. If \(P=0\), the only supported \(K\) is zero and \(b_0(0)=0\). → `hessForm` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:84`)
- condition of the paper: If \(T\ge0\) → `GapPositive` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:144`)
- condition of the paper: \(U=U^*\) → `GapSymmetry` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:152`)
- condition of the paper: \(-T\le U\le T\) → `GapOrder` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:160`)

## Proposition 3.1

**Statement.** \label{prop:trace} For the maps in \eqref{eq:row-star}, let \(D_v:H_v\to H_v\) be symmetric with \(\norm{D_v}_{\op}\le1\), and put \(U_v=R_v^*D_vR_v\). Then \(U_v\) is supported on \(T_v\), and \begin{equation}\label{eq:trace} \abs{\tr(D_0W_0D_1W_1D_2W_2)} \le\frac53\sum_{v=0}^2 b_{T_v}(U_v). \end{equation} The constant is independent of all three dimensions.

**Lean.** `Papers.OaiBoundDyadicTriangular.abs_trace_le_hessForm_sum` — `lean/Papers/OaiBoundDyadicTriangular/TTrace.lean:212`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| For the maps in \eqref{eq:row-star}, let \(D_v:H_v\to H_v\) be symmetric with \(\norm{D_v}_{\op}\le1\), | `D₀ : Matrix H₀ H₀ ℝ`<br>`D₁ : Matrix H₁ H₁ ℝ`<br>`D₂ : Matrix H₂ H₂ ℝ`<br>`hSymmetry : TraceSymmetry D₀ D₁ D₂`<br>`hContraction : TraceContraction D₀ D₁ D₂` |
| and put \(U_v=R_v^*D_vR_v\). | — (no Lean counterpart recorded) |
| Then \(U_v\) is supported on \(T_v\), | then `SupportedOn (rowGram R₀) (rowPerturbation R₀ D₀)`<br>then `SupportedOn (rowGram R₁) (rowPerturbation R₁ D₁)`<br>then `SupportedOn (rowGram R₂) (rowPerturbation R₂ D₂)` |
| and \begin{equation} \abs{\tr(D_0W_0D_1W_1D_2W_2)} \le\frac53\sum_{v=0}^2 b_{T_v}(U_v). \end{equation} | then `|(D₀ * W₀ * D₁ * W₁ * D₂ * W₂).trace| ≤ (5 / 3 : ℝ) * (hessForm (rowGram R₀) (rowGram_isHermitian R₀) (rowPerturbation R₀ D₀) + hessForm (rowGram R₁) (rowGram_isHermitian R₁) (rowPerturbation R₁ D₁) + hessForm (rowGram R₂) (rowGram_isHermitian R₂) (rowPerturbation R₂ D₂))` |
| The constant is independent of all three dimensions. | — (no Lean counterpart recorded) |

Lean also declares what the paper leaves implicit (the objects and their types): `H₀ H₁ H₂ : Type*`, `Fintype H₀`, `DecidableEq H₀`, `Fintype H₁`, `DecidableEq H₁`, `Fintype H₂`, `DecidableEq H₂`, `W₀ : Matrix H₀ H₁ ℝ`, `W₁ : Matrix H₁ H₂ ℝ`, `W₂ : Matrix H₂ H₀ ℝ`, `let R₀ := rowStar W₀ W₂`, `let R₁ := rowStar W₁ W₀`, `let R₂ := rowStar W₂ W₁`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: All spaces and matrices in the proof are real → `RealMatrixSetting` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:35`)
- definition of the paper: \(R^*\) denotes the transpose of \(R\). → `realAdjoint` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:42`)
- definition of the paper: For a symmetric positive semidefinite matrix \(P\), define \[ \Phi(P)=\tr(P^{3/2}),\qquad \supp P=(\ker P)^\perp. \] → `matrixEnergy` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:63`)
- definition of the paper: A symmetric matrix \(K\) is \emph{supported on \(P\)} if it annihilates \(\ker P\). → `SupportedOn` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:55`)
- definition of the paper: For such \(K\), define \begin{equation}\label{eq:hessian} b_P(K)=\frac32\sum_{i,j} \frac{\abs{K_{ij}}^2}{\sqrt{p_i}+\sqrt{p_j}}, \end{equation} where \(p_i>0\) are the eigenvalues of \(P\) on its support, and the entries are taken in an orthonormal eigenbasis of that support. If \(P=0\), the only supported \(K\) is zero and \(b_0(0)=0\). → `hessForm` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:84`)
- definition of the paper: Let \(H_v\), \(v\in\Z/3\Z\), be finite-dimensional real inner product spaces, and let \(W_v:H_{v+1}\to H_v\). The two edges incident to vertex \(v\) form the \emph{row star} \begin{equation}\label{eq:row-star} R_v=[\,W_v\quad W_{v-1}^*\,]: H_{v+1}\oplus H_{v-1}\longrightarrow H_v, \qquad T_v=R_v^*R_v. \end{equation} → `rowStar` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:171`)
- definition of the paper: put \(U_v=R_v^*D_vR_v\). → `rowPerturbation` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:186`)
- condition of the paper: let \(D_v:H_v\to H_v\) be symmetric → `TraceSymmetry` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:202`)
- condition of the paper: \(\norm{D_v}_{\op}\le1\) → `TraceContraction` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:216`)

## Proposition 4.1

**Statement.** \label{prop:increase} For \(\mathbf I\in\cA_k\), \(k\ge m+1\), define \[ \delta(\mathbf I) =\frac14\sum_{\mathbf I'\in\operatorname{ch}(\mathbf I)} e(\mathbf I')-e(\mathbf I). \] Then \(\delta(\mathbf I)\ge0\), and \begin{equation}\label{eq:local-control} \abs{\tau(\mathbf I)} \le\frac{10\sqrt2}{3}\,\delta(\mathbf I). \end{equation}

**Lean.** `Papers.OaiBoundDyadicTriangular.energyIncrement_controls_trace` — `lean/Papers/OaiBoundDyadicTriangular/TIncrease.lean:24`

**Status.** proved in Lean, under 1 condition(s) made explicit. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| For \(\mathbf I\in\cA_k\), \(k\ge m+1\), define | `k m : ℤ`<br>`n : Fin 3 → ℕ`<br>`hTriple : IncreaseTriple n`<br>`hScale : IncreaseScale k m` |
| \[ \delta(\mathbf I) =\frac14\sum_{\mathbf I'\in\operatorname{ch}(\mathbf I)} e(\mathbf I')-e(\mathbf I). \] | — (no Lean counterpart recorded) |
| Then \(\delta(\mathbf I)\ge0\), | then `0 ≤ energyIncrement F k m n` |
| and \begin{equation} \abs{\tau(\mathbf I)} \le\frac{10\sqrt2}{3}\,\delta(\mathbf I). \end{equation} | then `|localTrace F k m n| ≤ 10 * Real.sqrt 2 / 3 * energyIncrement F k m n` |

Lean also declares what the paper leaves implicit (the objects and their types): `F : Fin 3 → ℝ × ℝ → ℝ`.

Lean assumes conditions that the paper's text does not state: `hBounded : StepBounded F`, `hCompact : StepCompact F`, `hAtoms : StepAtoms F m`, `hHalves : HaarHalvesConvention`.

**Conditions and readings, and the Lean definitions that carry them.**

- reading: For $I=[2^kn_I,2^k(n_I+1))$, its halves are $I_{\mathrm{left}}=[2^kn_I,2^kn_I+2^{k-1})$ and $I_{\mathrm{right}}=[2^kn_I+2^{k-1},2^k(n_I+1))$. → `HaarHalvesConvention` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:295`)
- definition of the paper: Write \(\R_+=[0,\infty)\). → `Rplus` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:230`)
- definition of the paper: For \(k\in\Z\), let \[ \cD_k=\{[2^kn,2^k(n+1)):n\in\Z_{\ge0}\}. \] → `dyadicInterval` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:244`)
- definition of the paper: For \(I\in\cD_k\), denote its index by \(n_I\) and set \[ h_I=\mathbf1_{I_{\mathrm{left}}}-\mathbf1_{I_{\mathrm{right}}}. \] → `haarSign` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:260`)
- definition of the paper: Let \(\oplus\) denote bitwise XOR of nonnegative integers → `xor3` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:270`)
- definition of the paper: define the set of admissible triples \[ \cA_k=\{(I_0,I_1,I_2)\in\cD_k^3: n_{I_0}\oplus n_{I_1}\oplus n_{I_2}=0\}. \] → `IsAdmissible` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:275`)
- condition of the paper: All spaces and matrices in the proof are real → `RealMatrixSetting` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:35`)
- definition of the paper: \(R^*\) denotes the transpose of \(R\). → `realAdjoint` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:42`)
- definition of the paper: For a symmetric positive semidefinite matrix \(P\), define \[ \Phi(P)=\tr(P^{3/2}),\qquad \supp P=(\ker P)^\perp. \] → `matrixEnergy` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:63`)
- definition of the paper: A symmetric matrix \(K\) is \emph{supported on \(P\)} if it annihilates \(\ker P\). → `SupportedOn` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:55`)
- definition of the paper: For such \(K\), define \begin{equation}\label{eq:hessian} b_P(K)=\frac32\sum_{i,j} \frac{\abs{K_{ij}}^2}{\sqrt{p_i}+\sqrt{p_j}}, \end{equation} where \(p_i>0\) are the eigenvalues of \(P\) on its support, and the entries are taken in an orthonormal eigenbasis of that support. If \(P=0\), the only supported \(K\) is zero and \(b_0(0)=0\). → `hessForm` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:84`)
- condition of the paper: For this section, the inputs are bounded → `StepBounded` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:321`)
- condition of the paper: compactly supported, → `StepCompact` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:328`)
- condition of the paper: constant on products of intervals in \(\cD_m\), for some \(m\in\Z\). → `StepAtoms` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:337`)
- definition of the paper: Let \(H_v\), \(v\in\Z/3\Z\), be finite-dimensional real inner product spaces, and let \(W_v:H_{v+1}\to H_v\). The two edges incident to vertex \(v\) form the \emph{row star} \begin{equation}\label{eq:row-star} R_v=[\,W_v\quad W_{v-1}^*\,]: H_{v+1}\oplus H_{v-1}\longrightarrow H_v, \qquad T_v=R_v^*R_v. \end{equation} → `rowStar` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:171`)
- definition of the paper: For \(\mathbf I=(I_0,I_1,I_2)\in\cA_k\), \(k\ge m\), let \(H_v\) have an orthonormal basis indexed by the intervals of \(\cD_m\) inside \(I_v\). Call these intervals atoms. → `atomIndex` (`lean/Papers/OaiBoundDyadicTriangular/Helpers/AtomEnergy.lean:123`)
- definition of the paper: In the probability measure \(\abs{I_v}^{-1}\dd x_v\), each atom has weight \(w_v(i)=2^{m-k}\). → `atomWeight` (`lean/Papers/OaiBoundDyadicTriangular/Helpers/AtomEnergy.lean:132`)
- definition of the paper: Define \(W_v:H_{v+1}\to H_v\) by \begin{equation}\label{eq:weighted-edge} W_v(i,j)=\sqrt{w_v(i)w_{v+1}(j)}\,F_v(i,j), \end{equation} where \(F_v(i,j)\) is the constant value on the corresponding atom pair. → `weightedEdge` (`lean/Papers/OaiBoundDyadicTriangular/Helpers/AtomEnergy.lean:156`)
- definition of the paper: Use these maps in \eqref{eq:row-star}, and define \begin{equation}\label{eq:local-energy} e_v(\mathbf I)=\Phi(T_v)=\Phi(R_vR_v^*), \qquad e(\mathbf I)=\sum_{v=0}^2 e_v(\mathbf I). \end{equation} → `localEnergy` (`lean/Papers/OaiBoundDyadicTriangular/Helpers/AtomEnergy.lean:184`)
- definition of the paper: If \(b_v\in\{0,1\}\) chooses the left or right half of \(I_v\), the child index is \(2n_{I_v}+b_v\). The child triple is admissible precisely when \(b_0\oplus b_1\oplus b_2=0\). Equivalently, with \(s_v=(-1)^{b_v}\), its signs satisfy \(s_0s_1s_2=1\). Write \(\operatorname{ch}(\mathbf I)\) for these four children. → `children` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:422`)
- definition of the paper: If \(k\ge m+1\), let \(D_v\) be the diagonal matrix of the \(h_{I_v}\)-values on the atoms, and put \[ \tau(\mathbf I)=\tr(D_0W_0D_1W_1D_2W_2). \] → `localTrace` (`lean/Papers/OaiBoundDyadicTriangular/Helpers/AtomEnergy.lean:215`)
- definition of the paper: define \[ \delta(\mathbf I) =\frac14\sum_{\mathbf I'\in\operatorname{ch}(\mathbf I)} e(\mathbf I')-e(\mathbf I). \] → `energyIncrement` (`lean/Papers/OaiBoundDyadicTriangular/Helpers/AtomEnergy.lean:236`)
- condition of the paper: For \(\mathbf I\in\cA_k\) → `IncreaseTriple` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:366`)
- condition of the paper: \(k\ge m+1\) → `IncreaseScale` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:372`)

## Lemma 5.1

**Statement.** \label{lem:total} For the step functions of Section~\ref{sec:dyadic} and every \(k\ge m\), set \[ J_k=\sum_{\mathbf I\in\cA_k}2^{2k}e(\mathbf I). \] Then \begin{equation}\label{eq:total} 0\le J_k\le2\sqrt2\sum_{v=0}^2\norm{F_v}_3^3. \end{equation} For \(k\ge m+1\), \begin{equation}\label{eq:telescope} \sum_{\mathbf I\in\cA_k}2^{2k}\delta(\mathbf I) =J_{k-1}-J_k. \end{equation}

**Lean.** `Papers.OaiBoundDyadicTriangular.totalEnergy_bound_and_telescope` — `lean/Papers/OaiBoundDyadicTriangular/Helpers/Summation.lean:262`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| For the step functions of Section~\ref{sec:dyadic} and every \(k\ge m\), set | ≈ `F : Fin 3 → ℝ × ℝ → ℝ`<br>≈ `hBounded : StepBounded F`<br>≈ `hCompact : StepCompact F`<br>≈ `hAtoms : StepAtoms F m`<br>≈ `TotalScale k m` |
| \[ J_k=\sum_{\mathbf I\in\cA_k}2^{2k}e(\mathbf I). \] | — (no Lean counterpart recorded) |
| Then \begin{equation} 0\le J_k\le2\sqrt2\sum_{v=0}^2\norm{F_v}_3^3. \end{equation} | then `0 ≤ totalEnergy F k m`<br>then `totalEnergy F k m ≤ 2 * Real.sqrt 2 * ∑ v : Fin 3, (eLpNorm (F v) 3 quadrantMeasure).toReal ^ 3` |
| For \(k\ge m+1\), | `TotalTelescopeScale k m` |
| \begin{equation} \sum_{\mathbf I\in\cA_k}2^{2k}\delta(\mathbf I) =J_{k-1}-J_k. \end{equation} | then `(∑' n : admissibleSet, (2 : ℝ)^(2*k) * energyIncrement F k m n.val) = totalEnergy F (k - 1) m - totalEnergy F k m` |

A row marked ≈ was given these phrases with many rows of its result at once, not on its own.

Lean also declares what the paper leaves implicit (the objects and their types): `k m : ℤ`.

**Conditions and readings, and the Lean definitions that carry them.**

- definition of the paper: Write \(\R_+=[0,\infty)\). → `Rplus` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:230`)
- definition of the paper: For \(k\in\Z\), let \[ \cD_k=\{[2^kn,2^k(n+1)):n\in\Z_{\ge0}\}. \] → `dyadicInterval` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:244`)
- definition of the paper: Let \(\oplus\) denote bitwise XOR of nonnegative integers → `xor3` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:270`)
- definition of the paper: define the set of admissible triples \[ \cA_k=\{(I_0,I_1,I_2)\in\cD_k^3: n_{I_0}\oplus n_{I_1}\oplus n_{I_2}=0\}. \] → `IsAdmissible` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:275`)
- condition of the paper: All spaces and matrices in the proof are real → `RealMatrixSetting` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:35`)
- definition of the paper: \(R^*\) denotes the transpose of \(R\). → `realAdjoint` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:42`)
- definition of the paper: For a symmetric positive semidefinite matrix \(P\), define \[ \Phi(P)=\tr(P^{3/2}),\qquad \supp P=(\ker P)^\perp. \] → `matrixEnergy` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:63`)
- condition of the paper: For this section, the inputs are bounded → `StepBounded` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:321`)
- condition of the paper: compactly supported, → `StepCompact` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:328`)
- condition of the paper: constant on products of intervals in \(\cD_m\), for some \(m\in\Z\). → `StepAtoms` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:337`)
- definition of the paper: Let \(H_v\), \(v\in\Z/3\Z\), be finite-dimensional real inner product spaces, and let \(W_v:H_{v+1}\to H_v\). The two edges incident to vertex \(v\) form the \emph{row star} \begin{equation}\label{eq:row-star} R_v=[\,W_v\quad W_{v-1}^*\,]: H_{v+1}\oplus H_{v-1}\longrightarrow H_v, \qquad T_v=R_v^*R_v. \end{equation} → `rowStar` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:171`)
- definition of the paper: For \(\mathbf I=(I_0,I_1,I_2)\in\cA_k\), \(k\ge m\), let \(H_v\) have an orthonormal basis indexed by the intervals of \(\cD_m\) inside \(I_v\). Call these intervals atoms. → `atomIndex` (`lean/Papers/OaiBoundDyadicTriangular/Helpers/AtomEnergy.lean:123`)
- definition of the paper: In the probability measure \(\abs{I_v}^{-1}\dd x_v\), each atom has weight \(w_v(i)=2^{m-k}\). → `atomWeight` (`lean/Papers/OaiBoundDyadicTriangular/Helpers/AtomEnergy.lean:132`)
- definition of the paper: Define \(W_v:H_{v+1}\to H_v\) by \begin{equation}\label{eq:weighted-edge} W_v(i,j)=\sqrt{w_v(i)w_{v+1}(j)}\,F_v(i,j), \end{equation} where \(F_v(i,j)\) is the constant value on the corresponding atom pair. → `weightedEdge` (`lean/Papers/OaiBoundDyadicTriangular/Helpers/AtomEnergy.lean:156`)
- definition of the paper: Use these maps in \eqref{eq:row-star}, and define \begin{equation}\label{eq:local-energy} e_v(\mathbf I)=\Phi(T_v)=\Phi(R_vR_v^*), \qquad e(\mathbf I)=\sum_{v=0}^2 e_v(\mathbf I). \end{equation} → `localEnergy` (`lean/Papers/OaiBoundDyadicTriangular/Helpers/AtomEnergy.lean:184`)
- definition of the paper: If \(b_v\in\{0,1\}\) chooses the left or right half of \(I_v\), the child index is \(2n_{I_v}+b_v\). The child triple is admissible precisely when \(b_0\oplus b_1\oplus b_2=0\). Equivalently, with \(s_v=(-1)^{b_v}\), its signs satisfy \(s_0s_1s_2=1\). Write \(\operatorname{ch}(\mathbf I)\) for these four children. → `children` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:422`)
- definition of the paper: define \[ \delta(\mathbf I) =\frac14\sum_{\mathbf I'\in\operatorname{ch}(\mathbf I)} e(\mathbf I')-e(\mathbf I). \] → `energyIncrement` (`lean/Papers/OaiBoundDyadicTriangular/Helpers/AtomEnergy.lean:236`)
- definition of the paper: set \[ J_k=\sum_{\mathbf I\in\cA_k}2^{2k}e(\mathbf I). \] → `totalEnergy` (`lean/Papers/OaiBoundDyadicTriangular/Helpers/AtomEnergy.lean:248`)
- condition of the paper: For \(k\ge m+1\) → `TotalTelescopeScale` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:384`)
- condition of the paper: every \(k\ge m\) → `TotalScale` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:378`)

## Lemma 5.2

**Statement.** \label{lem:continuity} For every \(k\in\Z\) and real \(F_v\in L^3(\R_+^2)\), \begin{equation}\label{eq:one-scale} \sum_{\mathbf I\in\cA_k}\abs{L_{\mathbf I}(F_0,F_1,F_2)} \le\prod_{v=0}^2\norm{F_v}_3. \end{equation} Consequently the sequence \((L_{\mathbf I}(F_0,F_1,F_2))_{\mathbf I\in\cA_k}\) depends continuously on the inputs as a map from \(L^3\times L^3\times L^3\) to \(\ell^1(\cA_k)\).

**Lean.** `Papers.OaiBoundDyadicTriangular.localForm_one_scale_bound` — `lean/Papers/OaiBoundDyadicTriangular/Helpers/Continuity.lean:29`

**Status.** proved in Lean, under 1 condition(s) made explicit. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| For every \(k\in\Z\) and real \(F_v\in L^3(\R_+^2)\), | `k : ℤ`<br>`F : Fin 3 → ℝ × ℝ → ℝ`<br>`hScale : ContinuityScale k`<br>`hInputs : ContinuityInputs F` |
| \begin{equation} \sum_{\mathbf I\in\cA_k}\abs{L_{\mathbf I}(F_0,F_1,F_2)} \le\prod_{v=0}^2\norm{F_v}_3. \end{equation} | then `∑ n ∈ T, |localForm k n.val F| ≤ ∏ v : Fin 3, (eLpNorm (F v) 3 quadrantMeasure).toReal` |
| Consequently the sequence \((L_{\mathbf I}(F_0,F_1,F_2))_{\mathbf I\in\cA_k}\) depends continuously on the inputs as a map from \(L^3\times L^3\times L^3\) to \(\ell^1(\cA_k)\). | — (no Lean counterpart recorded) |

Lean also declares what the paper leaves implicit (the objects and their types): `∀ T : Finset admissibleSet`, `G : Fin 3 → ℝ × ℝ → ℝ`, `∀ T : Finset admissibleSet`.

Lean assumes conditions that the paper's text does not state: `hHalves : HaarHalvesConvention`, `ContinuityInputs G`.

Lean concludes what the paper's text does not state: `∑ n ∈ T, |localForm k n.val F - localForm k n.val G| ≤ (eLpNorm (fun x => F 0 x - G 0 x) 3 quadrantMeasure).toReal * (eLpNorm (F 1) 3 quadrantMeasure).toReal * (eLpNorm (F 2) 3 quadrantMeasure).toReal + (eLpNorm (G 0) 3 quadrantMeasure).toReal * (eLpNorm (fun x => F 1 x - G 1 x) 3 quadrantMeasure).toReal * (eLpNorm (F 2) 3 quadrantMeasure).toReal + (eLpNorm (G 0) 3 quadrantMeasure).toReal * (eLpNorm (G 1) 3 quadrantMeasure).toReal * (eLpNorm (fun x => F 2 x - G 2 x) 3 quadrantMeasure).toReal`.

**Conditions and readings, and the Lean definitions that carry them.**

- reading: For $I=[2^kn_I,2^k(n_I+1))$, its halves are $I_{\mathrm{left}}=[2^kn_I,2^kn_I+2^{k-1})$ and $I_{\mathrm{right}}=[2^kn_I+2^{k-1},2^k(n_I+1))$. → `HaarHalvesConvention` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:295`)
- definition of the paper: Write \(\R_+=[0,\infty)\). → `Rplus` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:230`)
- definition of the paper: For \(k\in\Z\), let \[ \cD_k=\{[2^kn,2^k(n+1)):n\in\Z_{\ge0}\}. \] → `dyadicInterval` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:244`)
- definition of the paper: For \(I\in\cD_k\), denote its index by \(n_I\) and set \[ h_I=\mathbf1_{I_{\mathrm{left}}}-\mathbf1_{I_{\mathrm{right}}}. \] → `haarSign` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:260`)
- definition of the paper: Let \(\oplus\) denote bitwise XOR of nonnegative integers → `xor3` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:270`)
- definition of the paper: define the set of admissible triples \[ \cA_k=\{(I_0,I_1,I_2)\in\cD_k^3: n_{I_0}\oplus n_{I_1}\oplus n_{I_2}=0\}. \] → `IsAdmissible` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:275`)
- definition of the paper: For \(\mathbf I\in\cA_k\) and three real functions \(F_v\) on \(\R_+^2\), put \begin{equation}\label{eq:local-form} L_{\mathbf I}(F_0,F_1,F_2) =2^{-k}\int_{I_0\times I_1\times I_2} F_0(x_0,x_1)F_1(x_1,x_2)F_2(x_2,x_0) \prod_{v=0}^2 h_{I_v}(x_v)\dd x_0\dd x_1\dd x_2. \end{equation} → `localForm` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:309`)
- condition of the paper: For every \(k\in\Z\) → `ContinuityScale` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:389`)
- condition of the paper: real \(F_v\in L^3(\R_+^2)\) → `ContinuityInputs` (`lean/Papers/OaiBoundDyadicTriangular/Basic.lean:398`)

## Identifiers

| Result | run id | paper label | source | Lean declaration |
| --- | --- | --- | --- | --- |
| Theorem 1.1 | `thm:main` | `thm:main` | `sections/01-introduction.tex:39-47` | `Papers.OaiBoundDyadicTriangular.dyadic_triangular_bound` |
| Lemma 2.1 | `lem:hessian` | `lem:hessian` | `sections/02-matrix.tex:28-36` | `Papers.OaiBoundDyadicTriangular.matrixEnergy_hessian` |
| Lemma 2.2 | `lem:order` | `lem:order` | `sections/02-matrix.tex:65-72` | `Papers.OaiBoundDyadicTriangular.hessForm_order` |
| Corollary 2.3 | `thm:gap` | `cor:gap` | `sections/02-matrix.tex:113-120` | `Papers.OaiBoundDyadicTriangular.matrixEnergy_midpoint_gap` |
| Proposition 3.1 | `prop:trace` | `prop:trace` | `sections/03-trace.tex:22-31` | `Papers.OaiBoundDyadicTriangular.abs_trace_le_hessForm_sum` |
| Proposition 4.1 | `prop:increase` | `prop:increase` | `sections/04-dyadic.tex:52-64` | `Papers.OaiBoundDyadicTriangular.energyIncrement_controls_trace` |
| Lemma 5.1 | `lem:total` | `lem:total` | `sections/05-summation.tex:9-24` | `Papers.OaiBoundDyadicTriangular.totalEnergy_bound_and_telescope` |
| Lemma 5.2 | `lem:continuity` | `lem:continuity` | `sections/05-summation.tex:80-90` | `Papers.OaiBoundDyadicTriangular.localForm_one_scale_bound` |
