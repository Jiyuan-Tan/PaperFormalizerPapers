# Correctness report — cns_simple_dml

**Verdict: ERRORS FOUND — REPAIRED BY MINIMAL PATCHES**

28 result(s) of the paper were examined, and 5 corollaries and 8 propositions a correction split off them. 22 were found wrong as printed: 22 corrected (17 by a weaker statement), 0 not repaired. In Lean: 40 proved, 1 taken from the literature as cited, 0 not certified, 0 not formalized.

> FIXTURE (TheoremCheckerPapers test data): trimmed from a real bundle; not a complete bundle.

## What was wrong and what was done

### Theorem 5.1 — corrected; the corrected statement is weaker

- **As printed.** \label{thm:dml}Suppose Assumption~\ref{assumption:cont} holds, $ E[\{Y-\gamma_0(W)\}^2 \mid W]\leq \bar{\sigma}^2,$ and $\|\alpha^{\min}_0\|_{\infty}\leq\bar{\alpha}. $ Then with probability $1-\epsilon$, $$ \sup_{z\in\mathbb{R}} \left| \text{\normalfont pr} \left\{\frac{n^{1/2}}{\ […fixture: truncated]
