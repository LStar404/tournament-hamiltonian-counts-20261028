#!/usr/bin/env python3
"""Build unified bilingual submission appendices from audited source proofs.

The historical companions are immutable inputs. Complete proof ranges retain
all equations and numbering. The explicit, counted EDITS below harmonize local
literature comparisons and references; scoped substitutions unify maximum-score
and analytic-majorant notation. No other proof rewriting is permitted.
SOURCE_HASHES and COPY_HASHES pin every raw and transformed block: changes to
either require deliberate review, not merely regeneration. Extraction comments
record both digests and each transformation count. The only whitespace change
preserves a trailing TeX control space by appending an empty group.
The LaTeX conversion follows render_compact_main.py and uses the corresponding
detailed companion's approved preamble.

Run from any directory:
    python3 tools/build_technical_appendix.py
    python3 tools/build_technical_appendix.py --check

PDFs are compiled separately with tools/compile_tex.py or the source-preserving
portable-font builder.  This tool never changes the detailed companions.
"""
from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
MANUSCRIPTS = ROOT / "manuscripts"

FRONT = {
    "en": r"""# Technical appendix for Hamiltonian path counts in tournaments

Xingchen Liu and Xiangyu Ye

11 November 2026

## Scope and dependency map

This appendix contains the longer analytic proofs used by the main paper, *Quantitative Hamiltonian path counts and degree stability*. It presents the complete proofs with section, theorem, equation and reference numbers retained for compatibility with the main paper. It is intended to be read with the main paper; the remaining expanded companion is optional further reading, not an additional prerequisite for these proofs.

The permanent approximation is an analytic tool with an independent quantitative proof for fixed entry-bound and spectral-gap parameters. Its determinant main term is not asserted to be new, and this appendix makes no broader novelty claim about its range of admissible matrices. The local comparisons in Section 3 follow the contribution statement in Section 3 of the main paper.

- [Section 3](#technical-permanent) proves Theorem 3.1 in full: Gaussian pairing, compressed non-Gaussian cores, the linear coefficient window, factorial restoration, the coefficient tail and the final uniform error bound.
- [Section 4](#technical-scaling) proves local diagonal scaling and its cost, Gaussian deletion and centering, paired score preprocessing, the exact nonprincipal restoration identity and the small-score estimate. Lemma 4.4 uses Theorem 3.1 and Lemmas 4.1--4.3. Lemma 4.5 uses the same scaling and deletion estimates without paired prescaling.
- [Lemma 6.1](#technical-spectral-cap) is included with its complete proof because A.1 refers to its transitive determinant polynomial. Its eigenvalue calculation also verifies the frequency used in the carousel example in Section 4.3.
- [Sections A.1--A.3](#technical-algebra) supply the transitive determinant identity, alternating-switching isomorphism, equality of power diagonals and the fourth-moment equality algebra used in the main paper's spectral argument. The carousel example in Section 4.3 uses A.2 and Lemma 6.1 directly.

Unqualified section and lemma references refer to this appendix; references to the main paper are explicitly identified. The needed notation is restated below. Standard external tools retain their original citations. The full original reference list is included to preserve citation numbers. The original author statement and personal acknowledgments are not reproduced.

## Notation

We use the main paper's maximum-score notation $\Delta_s=\|S\mathbf1\|_\infty$. In A.2--A.3, $d$ denotes the matrix or tournament order; local block sizes and degree indices in Section 3 also retain $d$. The scalar analytic majorant is

$$
\mathcal G_{C,q}(r)=\exp\!\left(\frac{C^2r^2}{2(1-q^2r^2)}\right),\qquad rq<1.
$$

It is distinct both from the score product $\Gamma=\prod_i(1-a_i^2)$ in Section 4 and from the Gaussian matrix functional $\mathcal G(M)=\det(I-MM^{\mathsf T})^{-1/2}$. The generating series $G(t)=\det(I-t^2BB^{\mathsf T})^{-1/2}$ in Section 3 is also a local notation. The symbols $C$ and $q$ there are fixed analytic parameters; in Section 4, $C=2A/(n-1)$ is a matrix, while in A.2, $q=(d-1)/2$ is an integer.

For a tournament adjacency matrix $A$, put

$$
S=A-A^{\mathsf T},\qquad 2A=J-I+S,\qquad s=S\mathbf1,
\qquad s_i=2d_i^+-(n-1),\qquad \sum_i s_i=0,
$$
$$
\mathcal E=\|s\|_2^2,\qquad
\Delta_s=\|s\|_\infty,\qquad
a=\frac{s}{n-1},\qquad \tau=\|a\|_2^2\quad(n\ge2).
$$

Here $I_p$ is the identity, $J_p=\mathbf1_p\mathbf1_p^{\mathsf T}$, $P_p=J_p/p$, and $\Pi_p=I_p-P_p$. Submatrix rows and columns are listed in increasing original-label order; they need not be the same sets. In Section 4, $n$ or $N$ is the full order, $m=n-t$ is the retained order, and $p$ is a general matrix order. Empty sums are zero, empty products are one, and the empty determinant and permanent are one. The symbol $\|\cdot\|_{\rm op}$ denotes the Euclidean operator norm, and $\|\cdot\|_F$ or $\|\cdot\|_{\mathrm F}$ denotes the Frobenius norm.

For the nonzero frequency pairs $\pm i\lambda_j$ of $S$, set

$$
x_j=\lambda_j^2/n^2,\qquad
D_n(S)=\det(I-S^{\mathsf T}S/n^2)^{-1/2}
=\prod_j(1-x_j)^{-1},
$$
$$
\rho_n(S)=D_n(S)\det(I+S/n)
=\prod_j\frac{1+x_j}{1-x_j}.
$$

The paired singular values give $\sum_jx_j=(n-1)/(2n)<1/2$, so these determinant factors are positive; all square roots mean the positive roots. The symbols $T_n^0$, $T_n$ and $T_d$ denote the transitive sign matrix in their respective orders, with entries $+1$ strictly above the diagonal. An odd carousel on $d=2q+1$ vertices has arcs $i\to j$ exactly when $j-i\pmod d\in\{1,\ldots,q\}$. Every logarithm is natural. Uniform error constants may depend on the fixed analytic or deletion-window parameters explicitly stated, but not on the particular admissible matrix, tournament or deletion sets.
""",
    "zh": r"""# 竞赛图 Hamilton 路径计数的技术附录

刘星辰、叶祥宇

2026年11月11日

## 范围与依赖导航

本附录集中收录主文《竞赛图 Hamilton 路径的定量计数与度稳定性》实际使用的较长分析证明。附录完整呈现所需证明，保留章节号、定理号、式号和引文号，以便与主文互相引用。本附录与主文共同构成所需证明；详细稿的其余部分作为可选展开阅读，不是这些证明的额外前提。

永久式近似在这里作为分析工具使用，附录给出固定元素界和谱隙参数下的独立定量证明。本文不把行列式主项称为新结果，也不在此提出关于适用矩阵范围的更广新颖性主张。第 3 节的局部文献比较与主文第 3 节的贡献定位一致。

- [第 3 节](#technical-permanent)完整证明定理 3.1，包括高斯配对、压缩后的非高斯核心、线性系数窗口、阶乘恢复、系数尾部及最终一致误差界。
- [第 4 节](#technical-scaling)完整证明局部对角缩放及其代价、高斯删除与中心化、配对度差预处理、非主子阵的精确恢复恒等式及小度差近似。引理 4.4 使用定理 3.1 和引理 4.1--4.3；引理 4.5 使用相同的缩放与删除估计，但不作配对预缩放。
- [引理 6.1](#technical-spectral-cap)保留完整陈述与证明，以补齐 A.1 对传递矩阵行列式多项式的依赖。其中的特征值计算也给出第 4.3 节圆环例子所用的频率。
- [A.1--A.3](#technical-algebra)给出主文谱论证所需的传递矩阵行列式恒等式、交替切换同构、矩阵幂的对角元相等及四次矩等号代数。第 4.3 节的圆环例子直接使用 A.2 和引理 6.1。

未特别注明的章节和引理引用均指本附录；对主文的引用明确标出。所需记号约定在下文重述。标准外部工具保留原引文。附录完整保留原参考文献表以维持引文编号，不收录原作者说明和个人致谢。

## 记号

最大度差与主文统一记为 $\Delta_s=\|S\mathbf1\|_\infty$。A.2--A.3 中的 $d$ 表示矩阵或竞赛图阶数；第 3 节的局部块大小和度数指标也保留 $d$。标量分析控制函数记为

$$
\mathcal G_{C,q}(r)=\exp\!\left(\frac{C^2r^2}{2(1-q^2r^2)}\right),\qquad rq<1.
$$

它既不同于第 4 节的度差乘积 $\Gamma=\prod_i(1-a_i^2)$，也不同于高斯矩阵泛函 $\mathcal G(M)=\det(I-MM^{\mathsf T})^{-1/2}$。第 3 节的生成函数 $G(t)=\det(I-t^2BB^{\mathsf T})^{-1/2}$ 也是局部记号。该节的 $C,q$ 是固定分析参数；第 4 节中 $C=2A/(n-1)$ 是矩阵，A.2 中 $q=(d-1)/2$ 是整数。

对竞赛图邻接矩阵 $A$，记

$$
S=A-A^{\mathsf T},\qquad 2A=J-I+S,\qquad s=S\mathbf1,
\qquad s_i=2d_i^+-(n-1),\qquad \sum_i s_i=0,
$$
$$
\mathcal E=\|s\|_2^2,\qquad
\Delta_s=\|s\|_\infty,\qquad
a=\frac{s}{n-1},\qquad \tau=\|a\|_2^2\quad(n\ge2).
$$

这里 $I_p$ 是单位矩阵，$J_p=\mathbf1_p\mathbf1_p^{\mathsf T}$，$P_p=J_p/p$，$\Pi_p=I_p-P_p$。子矩阵行列均按原顶点标号递增排列，行集与列集可以不同。第 4 节中 $n$ 或 $N$ 是完整阶数，$m=n-t$ 是保留阶数，$p$ 是一般矩阵阶数。空和为零，空积为一，空矩阵的行列式与永久式均为一。$\|\cdot\|_{\rm op}$ 表示 Euclidean 算子范数，$\|\cdot\|_F$ 或 $\|\cdot\|_{\mathrm F}$ 表示 Frobenius 范数。

若 $S$ 的非零频率对为 $\pm i\lambda_j$，记

$$
x_j=\lambda_j^2/n^2,\qquad
D_n(S)=\det(I-S^{\mathsf T}S/n^2)^{-1/2}
=\prod_j(1-x_j)^{-1},
$$
$$
\rho_n(S)=D_n(S)\det(I+S/n)
=\prod_j\frac{1+x_j}{1-x_j}.
$$

奇异值成对给出 $\sum_jx_j=(n-1)/(2n)<1/2$，所以这些行列式因子为正；平方根均取正根。$T_n^0$、$T_n$、$T_d$ 表示对应阶数的传递符号矩阵，即严格上三角元素全为 $+1$ 的反对称矩阵。奇阶圆环图的阶数为 $d=2q+1$，其边 $i\to j$ 当且仅当 $j-i\pmod d\in\{1,\ldots,q\}$。对数均为自然对数。一致误差常数可以依赖明确固定的分析参数或删除窗口参数，但不依赖具体的容许矩阵、竞赛图或删除集合。
""",
}

CONFIG = {
    "en": {
        "source": "08_detailed_proof.en",
        "target": "09_technical_appendix.en",
        "reference_heading": "## References",
        "lemma_start": "**Lemma 6.1 (Spectral cap).**",
        "lemma_end": "**Historical remark.**",
        "lemma_heading": "## 6.1 The spectral radius and an elementary uniform bound",
        "author": "Xingchen Liu and Xiangyu Ye",
        "date": "11 November 2026",
        "running_head": "HAMILTONIAN PATH COUNTS: TECHNICAL APPENDIX",
    },
    "zh": {
        "source": "07_detailed_proof.zh",
        "target": "10_technical_appendix.zh",
        "reference_heading": "## 参考文献",
        "lemma_start": "**引理 6.1（谱上限）。**",
        "lemma_end": "**历史说明。**",
        "lemma_heading": "## 6.1 谱半径与统一粗界",
        "author": "刘星辰、叶祥宇",
        "date": "2026年11月11日",
        "running_head": "竞赛图 Hamilton 路径计数技术附录",
    },
}


def extract(source: str, start: str, end: str | None = None) -> str:
    """Copy a unique source range, trimming only boundary whitespace."""
    starts = list(re.finditer(r"^" + re.escape(start), source, flags=re.M))
    if len(starts) != 1:
        raise ValueError(f"Expected exactly one extraction boundary: {start!r}")
    first = starts[0].start()
    if end is None:
        return source[first:].strip()
    ends = list(re.finditer(r"^" + re.escape(end), source, flags=re.M))
    if len(ends) != 1:
        raise ValueError(f"Expected exactly one extraction boundary: {end!r}")
    last = ends[0].start()
    if last <= first:
        raise ValueError(f"Out-of-order extraction boundaries: {start!r}, {end!r}")
    return source[first:last].strip()


def source_chunks(source: str, config: dict[str, str]) -> list[tuple[str, str]]:
    """Select complete raw proof ranges before documented submission transformations."""
    return [
        ("technical-permanent", extract(source, "## 3.", "## 4.")),
        ("technical-scaling", extract(source, "## 4.", "## 5.")),
        ("technical-spectral-cap", extract(source, config["lemma_start"], config["lemma_end"])),
        ("technical-algebra", extract(source, "## A.", "### A.4")),
        ("technical-references", extract(source, config["reference_heading"])),
    ]


CONTROL_SPACE_EOL = re.compile(r"(?<!\\)\\ (?=\n)")
NORMALIZATION = "trailing-tex-control-space-empty-group-v1"


def normalize_extracted_copy(raw: str) -> tuple[str, int]:
    """Append an empty group to a single-backslash control space before newline.

    The original control space remains effective in math and text modes.
    Interior control spaces and double-backslash line breaks are unchanged.
    """
    return CONTROL_SPACE_EOL.subn(lambda _: r"\ {}", raw)


# Reviewed submission edits: (block, exact old text, exact new text, count).
# These are organizational/notation changes, not replacements of proof steps.
EDITS = {'en': [('technical-permanent',
         'McCullagh [5] obtained the determinant main term under moderate-deviation conditions. Here we give '
         'a self-contained version for a fixed entry bound $C$ and singular-value spectral gap $q$, with an '
         'error uniform over the matrix class determined by these parameters. The proof controls the '
         'coefficients and the tail separately, so that the conclusion applies uniformly to the deletions '
         'and scalings in Section 4. A recent related approximation of Li [8, Theorem 2.1] assumes that the '
         'maximum absolute row or column sum of the centered perturbation is $o(n)$; this condition does not '
         'cover dense kernels whose corresponding sums have order $n$.',
         'McCullagh [5, §3] already gives the determinant approximation with an $O(n^{-1})$ error under '
         'moderate-deviation hypotheses. For nonnegative inputs, the fixed entry and spectral-gap '
         'assumptions here imply weak boundedness and the required gap, and his determinant factor is '
         'exactly $\\det(I-BB^{\\mathsf T})^{-1/2}$; the identification is detailed in Section 3 of the main '
         'paper. Uniformity over a fixed class is not by itself a novelty distinction from a theorem valid '
         'for every admissible sequence. We retain the independent proof to track constants through '
         'compressed cores, the coefficient window and the tail, making them available after deletion and '
         'scaling. We do not claim to repair an identified gap in [5]. Li [8, Theorem 2.1] assumes that the '
         'maximum absolute row or column sum of the centered perturbation is $o(n)$; this narrower '
         'hypothesis does not cover the dense kernels used here, but this comparison is not a novelty claim '
         'relative to [5] or [12].',
         1),
        ('technical-permanent',
         "The compressed-core proof below was developed independently in the authors' earlier path-counting "
         'project [14]. We retain the signed-matrix theorem as a separate analytic result, while the '
         'tournament applications in Sections 4--8 use nonnegative matrices.',
         'The compressed-core proof was developed independently in the earlier path-counting project [14]. '
         'Signed inputs are not a priority distinction: McCullagh [5, §4.1] already discusses complex '
         'perturbations. We retain the real signed formulation and its proof; the tournament applications '
         'use nonnegative inputs.',
         1),
        ('technical-permanent',
         'Divoux and Wang [12, Proposition 3.1] prove a uniform permanent approximation with relative error '
         '$o(1)$ for nonnegative doubly stochastic matrices. In the nonnegative setting used in our counting '
         'argument, their proof can be refined to give an $O(N^{-1})$ error. This rate is a refinement of '
         'their estimates, rather than the statement of their proposition. Theorem 3.1 here allows an '
         'arbitrary real doubly centered matrix $E$, without requiring $J+E$ to be nonnegative. We retain '
         'that formulation and its detailed proof; the two theorem statements do not have identical '
         'hypotheses.',
         'Divoux and Wang [12, Proposition 3.1] prove a uniform permanent approximation with relative error '
         '$o(1)$ for nonnegative doubly stochastic matrices. In the nonnegative setting used in our counting '
         'argument, their proof can be refined to give an $O(N^{-1})$ error. This rate is a refinement of '
         'their estimates, rather than the statement of their proposition. Theorem 3.1 here allows an '
         'arbitrary real doubly centered matrix $E$, without requiring $J+E$ to be nonnegative. We retain '
         'that formulation and its detailed proof; the two theorem statements do not have identical '
         'hypotheses. The difference in stated hypotheses is not a claim of priority or of a new range '
         'beyond McCullagh [5, §4.1]; see also Section 3 of the main paper.',
         1),
        ('technical-permanent',
         'The proof uses the Gaussian series $G(t)$, which is a different object from the numerical bound '
         '$G=100/19$ in Section 7.4. Put',
         'The proof uses the Gaussian generating series $G(t)$. Put',
         1),
        ('technical-permanent',
         'In this section we define a separate control function $\\Gamma(r)$, which is distinct from the '
         'score product $\\Gamma$ in Section 7:',
         'Use the scalar analytic majorant $\\mathcal G_{C,q}$ defined above:',
         1),
        ('technical-permanent',
         'and the corresponding norms are computed as in Definition 2.3.',
         'and the corresponding norms follow the conventions above.',
         1),
        ('technical-permanent',
         'This polynomial is a different object from the scalar weight $h_k=((k+1)/2)^{k/2}$ in Section 2.',
         'This notation is local to the present lemma.',
         1),
        ('technical-scaling',
         'The carousel transformation in Section 8.2 preserves all frequencies of the sign matrix, and the '
         'largest positive frequency is $\\cot(\\pi/(2n))$.',
         'The alternating switching and permutation in A.2 preserve all frequencies of the sign matrix; '
         'Lemma 6.1 gives the largest positive frequency $\\cot(\\pi/(2n))$.',
         1),
        ('technical-scaling', 'Theorem 8.1', 'Theorem 8.1 of the main paper', 2),
        ('technical-algebra',
         'Sections 6 and 11 also use',
         'The spectral arguments in the main paper also use',
         1)],
 'zh': [('technical-permanent',
         'McCullagh [5] 在适度偏离条件下得到了行列式主项。这里给出固定元素界 $C$、奇异值谱隙 $q$ '
         '下的自包含版本，其误差对这些参数所确定的矩阵类一致成立。证明分别控制系数与尾项，以便将结论一致地用于第 4 节中的删除和缩放。Li [8, Theorem 2.1] '
         '的近期相关近似假设中心扰动的最大绝对行和或列和为 $o(n)$；这一条件不覆盖相应行列和为 $n$ 量级的稠密核。',
         'McCullagh [5, §3] 已在适度偏离假设下给出具有 $O(n^{-1})$ 误差的行列式近似。对非负输入，本文的固定元素界和谱隙假设蕴含弱有界性及所需谱隙，其行列式因子恰为 '
         '$\\det(I-BB^{\\mathsf T})^{-1/2}$；主文第 3 '
         '节详细核对这一对应。固定矩阵类上的一致性本身也不能构成相对于逐个容许序列定理的新颖性区别。这里保留独立证明，以逐步跟踪压缩核心、系数窗口和尾部中的常数，供删除与缩放之后使用，并不声称修复 [5] '
         '中已确认的缺口。Li [8, Theorem 2.1] 假设中心扰动的最大绝对行和或列和为 $o(n)$；这一较窄条件不覆盖这里使用的稠密核，但这一比较不构成相对于 [5] 或 [12] '
         '的新颖性主张。',
         1),
        ('technical-permanent',
         '这套证明的主要结构已见于 10 月 8 日的独立路径存档 '
         '[14]。这里保留有符号实矩阵版本，并明确其与后续应用的区别：图论部分实际使用非负的缩放矩阵，有符号一般性是定理本身的额外范围，而非这些应用的必要条件。例如',
         '压缩核心证明独立形成于此前的路径计数项目 [14]。有符号输入不构成优先性区别：McCullagh [5, §4.1] 已讨论复扰动。这里保留实有符号版本及其证明；竞赛图应用实际使用非负输入。例如',
         1),
        ('technical-permanent',
         'Divoux–Wang [12, 命题 3.1] 对非负双随机矩阵给出了统一的 $1+o(1)$ 永久式近似。对于本文计数中出现的这一类矩阵，其证明可以细化为 '
         '$1+O(N^{-1})$。这里的误差阶不是原命题的陈述，而是保留其估计中的参数依赖后得到的改进。本文定理 3.1 允许任意实双中心化矩阵 $E$，不要求 $J+E$ '
         '非负；我们保留这一形式及其详细证明，不将两篇论文的定理假设视为完全相同。',
         'Divoux–Wang [12, 命题 3.1] 对非负双随机矩阵给出了统一的 $1+o(1)$ 永久式近似。对于本文计数中出现的这一类矩阵，其证明可以细化为 '
         '$1+O(N^{-1})$。这里的误差阶不是原命题的陈述，而是保留其估计中的参数依赖后得到的改进。本文定理 3.1 允许任意实双中心化矩阵 $E$，不要求 $J+E$ '
         '非负；我们保留这一形式及其详细证明，不将两篇论文的定理假设视为完全相同。 定理假设的表述差别并不构成优先性主张，也不声称超越 McCullagh [5, §4.1] 的适用范围；另见主文第 3 '
         '节。',
         1),
        ('technical-permanent',
         '证明中使用高斯级数 $G(t)$；它与第 7.4 节的数值上限 $G=100/19$ 是不同对象。令',
         '证明中使用高斯生成级数 $G(t)$。令',
         1),
        ('technical-permanent',
         '本节另定义控制函数 $\\Gamma(r)$，不与第 7 节的度差乘积 $\\Gamma$ 混用：',
         '使用前面定义的标量分析控制函数 $\\mathcal G_{C,q}$：',
         1),
        ('technical-permanent', '这个多项式与第 2 节标量权重 $h_k=((k+1)/2)^{k/2}$ 是不同对象。', '这里的记号只用于本引理。', 1),
        ('technical-scaling',
         '第 8.2 节的圆环变换保留符号矩阵的全部频率，最大正频率为 $\\cot(\\pi/(2n))$。',
         'A.2 中的交替切换与置换保留符号矩阵的全部频率；引理 6.1 给出最大正频率 $\\cot(\\pi/(2n))$。',
         1),
        ('technical-scaling', '定理 8.1', '主文定理 8.1', 2),
        ('technical-algebra', '第 6、11 节还用到', '主文的谱论证还用到', 1),
        ('technical-algebra', '该公式同时覆盖奇阶和偶阶；命题 6.6 与第 8.2 节均使用这一版本。', '该公式同时覆盖奇阶和偶阶，供主文的谱比较使用。', 1)]}

EDITS['zh'].append(('technical-permanent', '相应范数仍按定义 2.3 计算。', '相应范数遵循前面的约定。', 1))

# Display-only wrapping of Proposition 3.5 after the majorant notation grows.
# Three aligned lines retain the four terms verbatim; no font-size changes.
PROPOSITION_35_DISPLAY = (
    '|f(1)-G(1)|\n\\le \\frac{\\Gamma(R)T_1+K_G}{n}\n+\\frac{8\\Gamma(R)D^2}{n^2}\n+\\frac{R}{R-1}\\exp\\!\\left(\\beta\\sqrt n-\\alpha n\\log R\\right)\n+\\sigma\\Gamma(\\sigma)\\exp\\!\\left(-\\alpha n\\log\\sigma\\right).',
    '\\begin{aligned}\n|f(1)-G(1)|\n&\\le \\frac{\\Gamma(R)T_1+K_G}{n}\n+\\frac{8\\Gamma(R)D^2}{n^2}\\\\\n&\\quad+\\frac{R}{R-1}\\exp\\!\\left(\\beta\\sqrt n-\\alpha n\\log R\\right)\\\\\n&\\quad+\\sigma\\Gamma(\\sigma)\\exp\\!\\left(-\\alpha n\\log\\sigma\\right).\n\\end{aligned}',
)
for _language in CONFIG:
    EDITS[_language].append(("technical-permanent", *PROPOSITION_35_DISPLAY, 1))

SOURCE_HASHES = {'en': {'technical-permanent': '1c5a8952c61e6f7ee166f2a96dd233692eadd6e3e53f404a4d3c36f02f852f9d',
        'technical-scaling': '352940c54d4dcceb929cbd342fe1f4b11da1e120b860e4b90f83a384237ae7b9',
        'technical-spectral-cap': '1566fa652f4782e1a53216f2626610b61615e140ea7ab628ddc485574e2ffdda',
        'technical-algebra': '367e0e11472f6d4f97181333616ed6f392c822a92e963729139a72c100edd8ec',
        'technical-references': '1f98b0b8731d3894c571e1a3720298bf214d1eb37d1bcd346c3a008755e1326a'},
 'zh': {'technical-permanent': '3d4508f07065d636405f7e0479a0bea82fc2fbb8404fc336a140c322ae99d699',
        'technical-scaling': '64fc01bf570af1dca2f5c2c5694251bbce7b0625b568f43986375134af770315',
        'technical-spectral-cap': 'ec6a6e0153c6f6a061769d6e0dae8093260c6b80cf4c7a5d2a12400db52a19b0',
        'technical-algebra': '575e14157fdc0b628a3162bb172c934c23d024be87c80e88d1c592ec3b85de94',
        'technical-references': '594f3291d056aab8d9fc862676f0970cce8900d6977f49ca0d1aad1f231fabf0'}}


COPY_HASHES = {'en': {'technical-permanent': 'bec6fe50425f87eba4bd0783d021d5cc15a49bcc14622a4b7daac2f113b7c9b5',
        'technical-scaling': '4dfe201c1d1b4c72350025bd924dc61a0a80f7e0e3723ec5776e376ab2cde3f7',
        'technical-spectral-cap': '1566fa652f4782e1a53216f2626610b61615e140ea7ab628ddc485574e2ffdda',
        'technical-algebra': '4c9b467095a2778603529123f3bf4ef0caac964f0cc04475f53559ee223764f1',
        'technical-references': '1f98b0b8731d3894c571e1a3720298bf214d1eb37d1bcd346c3a008755e1326a'},
 'zh': {'technical-permanent': '00f346938bf36bc0c99816bdc9638ffb306acbbfd0c2c2e4cae378e6bcb47d63',
        'technical-scaling': 'c47eaac61d416d09ff957f0bf5ecddbc721106818d4efa0980e92c0a486e6486',
        'technical-spectral-cap': 'ec6a6e0153c6f6a061769d6e0dae8093260c6b80cf4c7a5d2a12400db52a19b0',
        'technical-algebra': '977076bfa4422b457070c3eea79c8e45d0585d7269e2137d132c051580b09207',
        'technical-references': '594f3291d056aab8d9fc862676f0970cce8900d6977f49ca0d1aad1f231fabf0'}}


def transform_copy(language: str, anchor: str, raw: str) -> tuple[str, list[str]]:
    """Apply only reviewed exact-text edits and narrowly scoped notation changes."""
    if hashlib.sha256(raw.encode()).hexdigest() != SOURCE_HASHES[language][anchor]:
        raise ValueError(f"Unreviewed source change: {language}/{anchor}")
    chunk, count = normalize_extracted_copy(raw)
    audit = [f"control-space:{count}"]
    for index, (block, old, new, expected) in enumerate(EDITS[language]):
        if block != anchor:
            continue
        if chunk.count(old) != expected:
            raise ValueError(f"Submission edit {language}/{index} no longer matches")
        chunk = chunk.replace(old, new)
        audit.append(f"edit-{index}:{expected}")
    if anchor == "technical-permanent":
        # Never rename the Gamma(N+1,1) probability distribution.
        chunk, count = re.subn(r"\\Gamma(?=\((?:r|R|1|\\sigma)\))",
                               lambda _: r"\mathcal G_{C,q}", chunk)
        audit.append(f"analytic-majorant:{count}")
    if anchor == "technical-scaling":
        before, marker, scores = chunk.partition("### 4.5 ")
        if not marker:
            raise ValueError("Missing small-score section boundary")
        # All standalone d in this subsection denote maximum score; products
        # nd^2 and 2td require explicit handling. No other section is touched.
        scores, count = re.subn(r"(?<![A-Za-z\\])d(?![A-Za-z])",
                                lambda _: r"\Delta_s", scores)
        for old, new in (("nd^2", r"n\Delta_s^2"), ("2td", r"2t\Delta_s")):
            count += scores.count(old)
            scores = scores.replace(old, new)
        chunk = before + marker + scores
        audit.append(f"maximum-score:{count}")
    if hashlib.sha256(chunk.encode()).hexdigest() != COPY_HASHES[language][anchor]:
        raise ValueError(f"Unreviewed transformed proof change: {language}/{anchor}")
    return chunk, audit


def make_markdown(language: str) -> str:
    config = CONFIG[language]
    path = MANUSCRIPTS / (config["source"] + ".md")
    source = path.read_text(encoding="utf-8")
    chunks = source_chunks(source, config)
    parts = [FRONT[language].strip()]
    for anchor, raw_chunk in chunks:
        chunk, audit = transform_copy(language, anchor, raw_chunk)
        raw_digest = hashlib.sha256(raw_chunk.encode("utf-8")).hexdigest()
        copy_digest = hashlib.sha256(chunk.encode("utf-8")).hexdigest()
        annotation = (
            f'<!-- Extraction from {path.name}; block={anchor}; '
            f'raw_block_sha256={raw_digest}; copy_block_sha256={copy_digest}; '
            f'normalization={NORMALIZATION}; transformations={",".join(audit)}. -->'
        )
        parts.extend([annotation, f'<a id="{anchor}"></a>'])
        if anchor == "technical-spectral-cap":
            parts.append(config["lemma_heading"])
        parts.append(chunk)
    markdown = "\n\n".join(parts) + "\n"
    # Pinned raw/copy hashes reject unreviewed changes even on regeneration.
    # --check additionally compares each generated artifact byte for byte.
    for anchor, raw_chunk in chunks:
        expected, _ = transform_copy(language, anchor, raw_chunk)
        if expected not in markdown:
            raise AssertionError("A source proof range changed beyond the documented submission transformations")
    original_tags = re.findall(r"\\tag\{([^}]+)\}", "\n".join(c for _, c in chunks))
    actual_tags = re.findall(r"\\tag\{([^}]+)\}", markdown)
    if original_tags != actual_tags:
        raise AssertionError("Equation numbers were altered during extraction")
    if len(actual_tags) != len(set(actual_tags)):
        raise ValueError("Duplicate equation tags in the selected proof ranges")
    ids = re.findall(r'<a id="([^"]+)"></a>', markdown)
    if len(ids) != len(set(ids)):
        raise ValueError("Duplicate explicit Markdown anchors")
    internal_links = re.findall(r"\]\(#([^)]*)\)", markdown)
    missing = set(internal_links) - set(ids)
    if missing:
        raise ValueError(f"Unresolved internal links: {sorted(missing)}")
    return markdown


def convert(markdown: str) -> str:
    """Use the same Pandoc route as the compact main-paper renderer."""
    markdown = re.sub(r"<!--.*?-->\s*", "", markdown, flags=re.S)
    markdown = re.sub(
        r'<a id="([^"]+)"></a>\s*\$\$(.*?)\$\$',
        lambda m: "\\begin{equation}\n" + m[2].strip()
        + "\n\\label{" + m[1] + "}\n\\end{equation}",
        markdown,
        flags=re.S,
    )
    markdown = re.sub(
        r'<a id="([^"]+)"></a>',
        lambda m: "\\phantomsection\\label{" + m[1] + "}",
        markdown,
    )
    result = subprocess.run(
        ["pandoc", "-f", "markdown+raw_tex", "-t", "latex",
         "--shift-heading-level-by=-1", "--wrap=none"],
        input=markdown, text=True, capture_output=True, check=True,
    )
    if result.stderr.strip():
        raise RuntimeError("Pandoc reported a warning: " + result.stderr.strip())
    latex = result.stdout.replace(".png}", ".pdf}")
    latex = re.sub(r"\\texttt\{([0-9a-f]{32,})\}", lambda m: r"\nolinkurl{" + m[1] + "}", latex)
    latex = re.sub(r",height=[^,\]]+", "", latex)
    latex = re.sub(
        r"(?m)^(\\(?:sub)*section\*?\{)",
        lambda m: "\\Needspace{12\\baselineskip}\n" + m[1],
        latex,
    )
    return latex


def make_latex(language: str, markdown: str) -> str:
    config = CONFIG[language]
    source = (MANUSCRIPTS / (config["source"] + ".tex")).read_text(encoding="utf-8")
    prefix, delimiter, _ = source.partition(r"\begin{document}")
    if not delimiter:
        raise ValueError("Detailed companion has no LaTeX document boundary")
    title = markdown.splitlines()[0].removeprefix("# ")
    prefix = re.sub(
        r"\\fancyhead\[C\]\{.*?\}\n",
        lambda _: r"\fancyhead[C]{\small " + config["running_head"] + "}\n",
        prefix,
    )
    prefix = re.sub(
        r"\\hypersetup\{pdftitle=.*?\}\n",
        lambda _: r"\hypersetup{pdftitle={" + title + "},pdfauthor={"
        + config["author"] + "}}\n",
        prefix,
    )
    body = markdown[markdown.index("## "):]
    title_block = (
        "\\begin{document}\n\\thispagestyle{plain}\n\\begin{center}\n"
        "{\\Large\\bfseries " + title + "\\par}\n\\vspace{9pt}\n"
        "{\\normalsize " + config["author"] + "\\par}\n\\vspace{5pt}\n"
        "{\\small " + config["date"] + "\\par}\n\\end{center}\n"
    )
    return (
        "% Generated by tools/build_technical_appendix.py; edit the generator or source proofs.\n"
        + prefix + title_block + convert(body) + "\n\\end{document}\n"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Verify generated sources without changing files")
    parser.add_argument("--language", choices=("en", "zh"), action="append", help="Build selected language(s); default both")
    args = parser.parse_args()
    stale = []
    for language in args.language or CONFIG:
        markdown = make_markdown(language)
        latex = make_latex(language, markdown)
        for extension, contents in (("md", markdown), ("tex", latex)):
            destination = MANUSCRIPTS / (CONFIG[language]["target"] + "." + extension)
            if args.check:
                if not destination.exists() or destination.read_text(encoding="utf-8") != contents:
                    stale.append(destination.relative_to(ROOT).as_posix())
            else:
                destination.write_text(contents, encoding="utf-8")
                print(f"Wrote {destination.relative_to(ROOT)}")
    if stale:
        print("Stale or missing generated sources:\n" + "\n".join(stale), file=sys.stderr)
        return 1
    if args.check:
        print("Both proof extraction integrity and generated-source checks passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
