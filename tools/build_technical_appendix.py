#!/usr/bin/env python3
"""Extract the bilingual technical appendices without rewriting source proofs.

The detailed companions remain independent expanded reading.  This generator
copies their complete Sections 3 and 4, Lemma 6.1 (needed by A.1), A.1--A.3,
and reference lists.  The new front matter records the dependency map and the
main paper's notation changes.  Source section, theorem, equation and reference
numbers are preserved.  The sole non-mathematical normalization appends an empty
group after a single TeX control space immediately before a newline, producing
\\ {} and retaining the original control space even in math mode.  Extraction
annotations retain both the raw block SHA-256 and the normalized copy SHA-256,
together with the exact replacement count.
Raw block hashes cover the selected ranges after boundary whitespace trimming;
no interior source whitespace or proof content is otherwise rewritten.
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

This appendix contains the longer analytic proofs used by the main paper, *Quantitative Hamiltonian path counts and degree stability*. It reproduces complete passages from the expanded English proof companion, with their original section, theorem, equation and reference numbers. It is intended to be read with the main paper; the remaining expanded companion is optional further reading, not an additional prerequisite for these proofs.

The permanent approximation is an analytic tool with an independent quantitative proof for fixed entry-bound and spectral-gap parameters. Its determinant main term is not asserted to be new, and this appendix makes no broader novelty claim about its range of admissible matrices. The contribution statement in the revised main introduction governs the paper; historical comparisons in the extracted text are retained as source context.

- [Section 3](#technical-permanent) proves Theorem 3.1 in full: Gaussian pairing, compressed non-Gaussian cores, the linear coefficient window, factorial restoration, the coefficient tail and the final uniform error bound.
- [Section 4](#technical-scaling) proves local diagonal scaling and its cost, Gaussian deletion and centering, paired score preprocessing, the exact nonprincipal restoration identity and the small-score estimate. Lemma 4.4 uses Theorem 3.1 and Lemmas 4.1--4.3. Lemma 4.5 uses the same scaling and deletion estimates without paired prescaling.
- [Lemma 6.1](#technical-spectral-cap) is included with its complete proof because A.1 refers to its transitive determinant polynomial. Its eigenvalue calculation also verifies the frequency used in the carousel example in Section 4.3.
- [Sections A.1--A.3](#technical-algebra) supply the transitive determinant identity, alternating-switching isomorphism, equality of power diagonals and the fourth-moment equality algebra used in the main paper's spectral argument. The mention of Section 8.2 in the example of Section 4.3 is closed here by A.2 and Lemma 6.1.

References to Sections 7, 8 and 11 in the extracted passages indicate subsequent applications, not additional proof inputs. The references to Section 2 distinguish reused notation; the needed conventions are restated below. Standard external tools retain their original citations. The full original reference list is included to preserve citation numbers. The original author statement and personal acknowledgments are not reproduced.

## Notation correspondence

The extracted proofs retain their historical notation. In particular, the main paper now writes $\Delta_s=\|S\mathbf1\|_\infty$ for the maximum score, where Sections 3--4 of this appendix use $d$ when denoting that quantity. In A.2--A.3, $d$ instead denotes the matrix or tournament order. The scalar control function $\Gamma(r)$ of Section 3 is written $\mathcal G_{C,q}(r)$ in the main paper:

$$
\mathcal G_{C,q}(r)=\exp\!\left(\frac{C^2r^2}{2(1-q^2r^2)}\right)
=\Gamma(r)\quad\text{in historical Section 3},\qquad rq<1.
$$

It is distinct both from the score product $\Gamma=\prod_i(1-a_i^2)$ in Section 4 and from the Gaussian matrix functional $\mathcal G(M)=\det(I-MM^{\mathsf T})^{-1/2}$. The generating series $G(t)=\det(I-t^2BB^{\mathsf T})^{-1/2}$ in Section 3 is also a local notation. The symbols $C$ and $q$ there are fixed analytic parameters; in Section 4, $C=2A/(n-1)$ is a matrix, while in A.2, $q=(d-1)/2$ is an integer.

For a tournament adjacency matrix $A$, put

$$
S=A-A^{\mathsf T},\qquad 2A=J-I+S,\qquad s=S\mathbf1,
\qquad s_i=2d_i^+-(n-1),\qquad \sum_i s_i=0,
$$
$$
\mathcal E=\|s\|_2^2,\qquad
\Delta_s=d=\|s\|_\infty,\qquad
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

本附录集中收录主文《竞赛图 Hamilton 路径的定量计数与度稳定性》实际使用的较长分析证明。内容按完整段落从中文详细证明稿抽取，保留原章节号、定理号、式号和引文号。本附录与主文共同构成所需证明；详细稿的其余部分作为可选展开阅读，不是这些证明的额外前提。

永久式近似在这里作为分析工具使用，附录给出固定元素界和谱隙参数下的独立定量证明。本文不把行列式主项称为新结果，也不在此提出关于适用矩阵范围的更广新颖性主张。论文贡献以修订后主文引言的定位为准；抽取段落中的历史比较保留为原文语境。

- [第 3 节](#technical-permanent)完整证明定理 3.1，包括高斯配对、压缩后的非高斯核心、线性系数窗口、阶乘恢复、系数尾部及最终一致误差界。
- [第 4 节](#technical-scaling)完整证明局部对角缩放及其代价、高斯删除与中心化、配对度差预处理、非主子阵的精确恢复恒等式及小度差近似。引理 4.4 使用定理 3.1 和引理 4.1--4.3；引理 4.5 使用相同的缩放与删除估计，但不作配对预缩放。
- [引理 6.1](#technical-spectral-cap)保留完整陈述与证明，以补齐 A.1 对传递矩阵行列式多项式的依赖。其中的特征值计算也给出第 4.3 节圆环例子所用的频率。
- [A.1--A.3](#technical-algebra)给出主文谱论证所需的传递矩阵行列式恒等式、交替切换同构、矩阵幂的对角元相等及四次矩等号代数。第 4.3 节例子中对第 8.2 节的引用，可由本附录的 A.2 和引理 6.1 直接补齐。

抽取段落中对第 7、8、11 节的引用指向后续应用，并非额外的证明输入；对第 2 节的引用用于区分复用记号，所需约定在下文重述。标准外部工具保留原引文。附录完整保留原参考文献表以维持引文编号，不收录原作者说明和个人致谢。

## 记号对照

抽取的证明保留历史记号。主文已将最大度差改记为 $\Delta_s=\|S\mathbf1\|_\infty$；本附录第 3--4 节在表示该量时仍用 $d$。A.2--A.3 中的 $d$ 则表示矩阵或竞赛图阶数。第 3 节的标量控制函数 $\Gamma(r)$ 在主文中改记为 $\mathcal G_{C,q}(r)$：

$$
\mathcal G_{C,q}(r)=\exp\!\left(\frac{C^2r^2}{2(1-q^2r^2)}\right)
=\Gamma(r)\quad\text{（历史第 3 节记号）},\qquad rq<1.
$$

它既不同于第 4 节的度差乘积 $\Gamma=\prod_i(1-a_i^2)$，也不同于高斯矩阵泛函 $\mathcal G(M)=\det(I-MM^{\mathsf T})^{-1/2}$。第 3 节的生成函数 $G(t)=\det(I-t^2BB^{\mathsf T})^{-1/2}$ 也是局部记号。该节的 $C,q$ 是固定分析参数；第 4 节中 $C=2A/(n-1)$ 是矩阵，A.2 中 $q=(d-1)/2$ 是整数。

对竞赛图邻接矩阵 $A$，记

$$
S=A-A^{\mathsf T},\qquad 2A=J-I+S,\qquad s=S\mathbf1,
\qquad s_i=2d_i^+-(n-1),\qquad \sum_i s_i=0,
$$
$$
\mathcal E=\|s\|_2^2,\qquad
\Delta_s=d=\|s\|_\infty,\qquad
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
    """These copied proof ranges are not normalized or edited."""
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


def make_markdown(language: str) -> str:
    config = CONFIG[language]
    path = MANUSCRIPTS / (config["source"] + ".md")
    source = path.read_text(encoding="utf-8")
    chunks = source_chunks(source, config)
    parts = [FRONT[language].strip()]
    for anchor, raw_chunk in chunks:
        chunk, count = normalize_extracted_copy(raw_chunk)
        raw_digest = hashlib.sha256(raw_chunk.encode("utf-8")).hexdigest()
        copy_digest = hashlib.sha256(chunk.encode("utf-8")).hexdigest()
        annotation = (
            f'<!-- Extraction from {path.name}; block={anchor}; '
            f'raw_block_sha256={raw_digest}; copy_block_sha256={copy_digest}; '
            f'normalization={NORMALIZATION}; replacements={count}. -->'
        )
        parts.extend([annotation, f'<a id="{anchor}"></a>'])
        if anchor == "technical-spectral-cap":
            parts.append(config["lemma_heading"])
        parts.append(chunk)
    markdown = "\n\n".join(parts) + "\n"
    # Compare against narrowly normalized copies, never broad whitespace folding.
    # The dual hashes also make source-only and substantive copy changes visible
    # to --check, which compares every complete generated artifact byte for byte.
    for _, raw_chunk in chunks:
        expected, _ = normalize_extracted_copy(raw_chunk)
        if expected not in markdown:
            raise AssertionError("A source proof range changed beyond the documented normalization")
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
