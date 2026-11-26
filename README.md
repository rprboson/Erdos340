# Improving the Cubic Constant for Greedy Sidon and Mian–Chowla Sequences

This repository contains the manuscript and a complete, sorry-free **Lean 4** formalization proving that every greedy Sidon sequence generated from a finite initial Sidon set — including the classical **Mian–Chowla sequence** ([OEIS A005282](https://oeis.org/A005282): $1, 2, 4, 8, 13, 21, 31, 45, 66, 81, \dots$) — breaks the classical $\frac{1}{6}n^3$ asymptotic barrier:

$$\limsup_{n \to \infty} \frac{a_n}{n^3} \le \frac{1}{6} - \frac{1}{12{,}000{,}000} < \frac{1}{6}.$$

The problem of determining the asymptotic growth of the Mian–Chowla sequence is **Erdős Problem #340** (Erdős & Graham, 1980), where the standard cubic counting bound $a_n \le \frac{1}{6}n^3 + O(n^2)$ has long stood as the baseline upper bound.

---

## Overview of the Proof

The repository brings together two complementary proofs of the strict improvement below $1/6$:

1. **Qualitative weak-limit proof (Manuscript, Sections 2–4):** Assumes $\limsup_{n\to\infty} a_n/n^3 = 1/6$, passes to a limiting probability measure $\nu$ on $[0, 1]$ via Prokhorov's theorem, proves $\operatorname{supp}(\nu) \subseteq [0, 1/2]$ and $F(u) \ge u^{1/3}$, derives an upper-tail lower bound on disjoint subintervals, and reaches a contradiction in $\mathbb{E}[W]$ via a seven-step rational staircase on $[0.12, 0.26]$.
2. **Quantitative finitary proof (Manuscript, Section 5 & Lean 4):** Replaces weak limits and integrals with an elementary, completely finitary 4-bin counting argument over finite sets (`Finset`), yielding the explicit constant $\frac{1}{6} - \frac{1}{12{,}000{,}000}$ for all sufficiently large $n$.

The manuscript also discusses the natural coverage-only barrier ($\kappa \approx 0.133161$), explaining why breaking further — and in particular establishing $a_n = o(n^3)$ — requires controlling internal collisions among forward obstructions $a_i + a_j - a_k$.

---

## Formal Verification in Lean 4

The file [`Erdos340/MianChowlaBound.lean`](Erdos340/MianChowlaBound.lean) formalizes the entire quantitative proof from first principles in **Lean 4 (`v4.37.0-rc1`)** with **Mathlib**, with **zero `sorry`s** and **zero warnings**.

To eliminate any specification gap, the formalization defines Sidon ($B_2$) sets, proves that every greedy Sidon sequence from an arbitrary finite initial prefix satisfies the causal coverage property, and explicitly constructs the classical Mian–Chowla sequence inductively.

### Key Declarations

| Declaration | Description |
| :--- | :--- |
| `MianChowla.IsSidonSet` | Standard definition of a Sidon ($B_2$) set of natural numbers. |
| `MianChowla.IsGreedySidonFrom` | Greedy Sidon sequence starting from any finite initial Sidon prefix. |
| `MianChowla.IsCausallyCoveredFrom` | Causal coverage property above a threshold $C$ (`a i + a j = y + a k` with $k < i \le j < n$). |
| `MianChowla.IsGreedySidonFrom.isCausallyCoveredFrom` | Bridge lemma: every greedy Sidon sequence is causally covered above $a_{n_0}$. |
| `MianChowla.greedySidon_eventually_le_below_one_sixth` | Main theorem for all greedy Sidon sequences: `∀ᶠ n in atTop, (a n : ℝ) / n ^ 3 ≤ 1 / 6 - 1 / 12000000`. |
| `MianChowla.mianChowla` | Explicit inductive construction of the classical Mian–Chowla sequence (`mianChowla 0 = 1`, `mianChowla 1 = 2`). |
| `MianChowla.mianChowla_isSidon` | Proof that `Set.range mianChowla` is a Sidon set. |
| `MianChowla.mianChowla_eventually_le_below_one_sixth` | Main corollary for the classical Mian–Chowla sequence. |

### Axiom Check

Both main theorems are verified by the Lean 4 kernel using only the three standard axioms:

```text
'MianChowla.greedySidon_eventually_le_below_one_sixth' depends on axioms: [propext, Classical.choice, Quot.sound]
'MianChowla.mianChowla_eventually_le_below_one_sixth' depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## Repository Structure

```text
.
├── Erdos340/
│   └── MianChowlaBound.lean     # Complete Lean 4 formalization (zero sorry)
├── greedy_sidon_cubic_bound.pdf # Manuscript (weak-limit proof, 4-bin proof, and remarks)
└── README.md
```

---

## How to Verify

### Option 1: Directly in the browser (no installation)
Open the Lean 4 Web Editor at [live.lean-lang.org](https://live.lean-lang.org/) (or paste the contents of `Erdos340/MianChowlaBound.lean` there) and inspect the `#print axioms` output at the end of the file.

*(Optional direct link: replace this line with your saved `live.lean-lang.org` URL.)*

### Option 2: Locally with Lake
With Lean 4 (`v4.37.0-rc1`) and Mathlib configured in your Lake project:

```bash
lake build Erdos340.MianChowlaBound
```

---

## Disclosure of AI Assistance and Attribution

In accordance with scholarly transparency, the proof strategies, Lean 4 formalization drafts, interval-arithmetic scripts, and manuscript exposition were developed during an interactive research session with **Google Gemini**, directed, inspected, and verified by **Rodrigo Pereira Resende**. All mathematical claims in the quantitative theorem have been independently machine-checked by the Lean 4 kernel.

---

## References

1. Y. C. Cheng, *Greedy Sidon sets for linear forms*, J. Number Theory **266** (2025), 225–248.
2. P. Erdős and R. L. Graham, *Old and New Problems and Results in Combinatorial Number Theory*, Monographies de L'Enseignement Mathématique, vol. 28, Université de Genève, 1980.
3. X. D. Jia, *On the distribution of a $B_2$-sequence*, Qufu Shifan Daxue Xuebao Ziran Kexue Ban **14** (1988), 12–18.
4. A. M. Mian and S. Chowla, *On the $B_2$ sequences of Sidon*, Proc. Nat. Acad. Sci. India Sect. A **14** (1944), 3–4.
5. K. O'Bryant, *A complete annotated bibliography of work related to Sidon sequences*, Electron. J. Combin., Dynamic Survey DS11 (2004), 39 pp.
